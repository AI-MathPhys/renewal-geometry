/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HankelFeedbackOperatorExact

/-!
# Hankel kernel and singular-number identification

This file closes the two identification steps in
`thm:feedback-Hankel-Weyl`.  First, the observability--controllability
factorization is proved equal almost everywhere to the literal integral
operator with kernel `B S(t+s) P C`, using the semigroup law and the
commuting idempotent screen.  Second, the singular numbers of an operator
between Hilbert spaces are encoded by their standard approximation-number
definition; consequently the already proved approximation-number decay is
literally the manuscript's `s_n` decay.
-/

open MeasureTheory

noncomputable section

namespace NCG
namespace HankelFeedback

variable {H₀ : Type*} [NormedAddCommGroup H₀]
  [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [MeasurableSpace H₀] [BorelSpace H₀] [SecondCountableTopology H₀]

/-- The literal screened memory Hankel kernel. -/
def memoryKernel (M : Screen H₀) (t s : ℝ) (x : H₀) : H₀ :=
  M.B (M.S (t + s) (M.P (M.C x)))

/-- The factorized Hankel operator is the literal integral-kernel operator.
Equality is stated almost everywhere because an `Lp` vector has only an
almost-everywhere defined representative. -/
theorem hankel_apply_ae_eq_memoryKernel_integral
    (M : Screen H₀)
    (hsemigroup : ∀ t s, M.S (t + s) = M.S t * M.S s)
    (hcomm : ∀ t, M.S t * M.P = M.P * M.S t)
    (hidem : M.P * M.P = M.P)
    (f : Lp H₀ 2 halfLine) :
    ∀ᵐ t ∂halfLine,
      (hankel M f) t =
        ∫ s, memoryKernel M t s (f s) ∂halfLine := by
  have hcoe := (memLp_obsFun M (ctrl M f)).coeFn_toLp
  filter_upwards [hcoe] with t ht
  have hctrl : Integrable (ctrlIntegrand M f) halfLine :=
    integrable_ctrlIntegrand M f
  let L : H₀ →L[ℝ] H₀ := M.B.comp ((M.S t).comp M.P)
  have hkernel : ∀ s,
      L (ctrlIntegrand M f s) = memoryKernel M t s (f s) := by
    intro s
    unfold L ctrlIntegrand memoryKernel
    simp only [ContinuousLinearMap.comp_apply]
    congr 1
    have hop : M.S t * M.P * M.S s * M.P =
        M.S (t + s) * M.P := by
      calc
        M.S t * M.P * M.S s * M.P =
            M.S t * (M.P * M.S s) * M.P := by
              simp only [mul_assoc]
        _ = M.S t * (M.S s * M.P) * M.P := by rw [← hcomm s]
        _ = (M.S t * M.S s) * (M.P * M.P) := by
              simp only [mul_assoc]
        _ = M.S (t + s) * M.P := by rw [hidem, ← hsemigroup]
    exact congrArg (fun A : H₀ →L[ℝ] H₀ => A (M.C (f s))) hop
  have hpoint :
      M.B (M.S t (M.P (ctrl M f))) =
        ∫ s, memoryKernel M t s (f s) ∂halfLine := by
    calc
      M.B (M.S t (M.P (ctrl M f))) = L (ctrl M f) := rfl
      _ = L (∫ s, ctrlIntegrand M f s ∂halfLine) := rfl
      _ = ∫ s, L (ctrlIntegrand M f s) ∂halfLine :=
        (L.integral_comp_comm hctrl).symm
      _ = ∫ s, memoryKernel M t s (f s) ∂halfLine := by
        exact integral_congr_ae (Filter.Eventually.of_forall hkernel)
  change (obs M (ctrl M f)) t =
    ∫ s, memoryKernel M t s (f s) ∂halfLine
  unfold obs
  rw [ht]
  simpa only [obsFun] using hpoint

/-- Singular numbers of a bounded operator between Hilbert spaces, using
the coordinate-free approximation-number definition valid in infinite
dimension.  The index is zero-based: `singularNumber T n = a_(n+1)(T)`. -/
def singularNumber (T : Lp H₀ 2 halfLine →L[ℝ] Lp H₀ 2 halfLine)
    (n : ℕ) : ℝ :=
  ApproximationNumbers.approxNumber T (n + 1)

theorem singularNumber_eq_approxNumber
    (T : Lp H₀ 2 halfLine →L[ℝ] Lp H₀ 2 halfLine) (n : ℕ) :
    singularNumber T n = ApproximationNumbers.approxNumber T (n + 1) :=
  rfl

/-- The proved approximation-number Weyl law is exactly the singular-number
law in the notation of the manuscript. -/
theorem singularNumber_hankel_decay [FiniteDimensional ℝ H₀]
    (W : ℝ → Splitting H₀)
    (T : Lp H₀ 2 halfLine →L[ℝ] Lp H₀ 2 halfLine)
    (hT : ∀ R, 0 < R → hankel (W R).fullScreen = T)
    {b c CW : ℝ} (hbc : 0 < b * c) (hCW : 0 < CW)
    (hR : ∀ R, 0 < R → (W R).R = R)
    (hb : ∀ R, 0 < R → (W R).b = b)
    (hc : ∀ R, 0 < R → (W R).c = c)
    (hrank : ∀ R, 0 < R →
      (Module.finrank ℝ (LinearMap.range (W R).P.toLinearMap) : ℝ)
        ≤ CW * R ^ ((3 : ℝ) / 2))
    (n : ℕ) (hn : 0 < n) :
    singularNumber T n ≤
      (b * c * CW ^ ((2 : ℝ) / 3) / 2) *
        (n : ℝ) ^ (-((2 : ℝ) / 3)) := by
  exact hankel_approxNumber_decay W T hT hbc hCW hR hb hc hrank n hn

end HankelFeedback
end NCG
