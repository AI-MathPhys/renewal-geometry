/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTCompiledChannelGeneratorExact

/-!
# Finite-dimensional channel norm comparison

This module closes the norm-equivalence step in
`thm:SMST-compiled-channel-generator`.  A linear Hamiltonian projection out
of any finite-dimensional normed channel space is automatically bounded.  We
combine that operator-norm bound with explicit Frobenius/sup-norm comparison
and the proved inner-derivation identity, thereby constructing the
manuscript's dimension-dependent constant instead of assuming it.
-/

open Matrix NormedSpace Filter Set

namespace NCG
namespace SMSTChannel

variable {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The Frobenius square of a square matrix is bounded by the number of
entries times the square of its product-space sup norm. -/
theorem hsFrobSq_le_card_sq_mul_norm_sq (A : Matrix d d ℂ) :
    hsFrobSq A ≤ (Fintype.card d : ℝ) ^ 2 * ‖A‖ ^ 2 := by
  rw [hsFrobSq]
  calc
    (∑ i, ∑ j, Complex.normSq (A i j))
        ≤ ∑ _i : d, ∑ _j : d, ‖A‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [Complex.normSq_eq_norm_sq]
          gcongr
          exact (norm_apply_le_norm (A i) j).trans (norm_apply_le_norm A i)
    _ = (Fintype.card d : ℝ) ^ 2 * ‖A‖ ^ 2 := by
          simp [pow_two]

/-- Hilbert--Schmidt norm versus the product-space sup norm. -/
theorem matrixHSNorm_le_card_mul_norm (A : Matrix d d ℂ) :
    matrixHSNorm A ≤ (Fintype.card d : ℝ) * ‖A‖ := by
  rw [matrixHSNorm]
  have h := hsFrobSq_le_card_sq_mul_norm_sq A
  have hsqrt := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs] at hsqrt
  have hn : 0 ≤ (Fintype.card d : ℝ) := by positivity
  have hnorm : 0 ≤ ‖A‖ := norm_nonneg _
  simpa [abs_of_nonneg (mul_nonneg hn hnorm), pow_two] using hsqrt

/-- A Hermitian inner derivation has superoperator HS norm at most
`sqrt(2d)` times the matrix HS norm.  The traceless case is equality. -/
theorem adSuperHSNorm_le_sqrt_card_mul_matrixHSNorm
    (H : Matrix d d ℂ) (hH : Hᴴ = H) :
    adSuperHSNorm H ≤
      Real.sqrt (2 * Fintype.card d) * matrixHSNorm H := by
  rw [adSuperHSNorm, matrixHSNorm]
  have hsq : adSuperHSSq H ≤
      2 * Fintype.card d * hsFrobSq H := by
    rw [adSuperHSSq_expansion H hH]
    exact sub_le_self _ (mul_nonneg (by positivity) (Complex.normSq_nonneg _))
  calc
    Real.sqrt (adSuperHSSq H)
        ≤ Real.sqrt (2 * Fintype.card d * hsFrobSq H) :=
          Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (2 * Fintype.card d) * Real.sqrt (hsFrobSq H) := by
          rw [Real.sqrt_mul (by positivity)]

section Projection

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every linear Hamiltonian projection out of a finite-dimensional channel
space has a channel-norm to superoperator-HS comparison constant. -/
theorem finiteDimensional_channel_to_adHS_bound
    (P : E →ₗ[ℝ] Matrix d d ℂ) :
    ∃ cd : ℝ, 0 ≤ cd ∧ ∀ x : E, (P x)ᴴ = P x →
      adSuperHSNorm (P x) ≤ cd * ‖x‖ := by
  let Pc : E →L[ℝ] Matrix d d ℂ :=
    ⟨P, P.continuous_of_finiteDimensional⟩
  refine ⟨Real.sqrt (2 * Fintype.card d) * Fintype.card d * ‖Pc‖,
    by positivity, ?_⟩
  intro x hx
  calc
    adSuperHSNorm (P x)
        ≤ Real.sqrt (2 * Fintype.card d) * matrixHSNorm (P x) :=
          adSuperHSNorm_le_sqrt_card_mul_matrixHSNorm (P x) hx
    _ ≤ Real.sqrt (2 * Fintype.card d) *
        ((Fintype.card d : ℝ) * ‖P x‖) := by
          gcongr
          exact matrixHSNorm_le_card_mul_norm (P x)
    _ ≤ Real.sqrt (2 * Fintype.card d) *
        ((Fintype.card d : ℝ) * (‖Pc‖ * ‖x‖)) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm Pc x
    _ = (Real.sqrt (2 * Fintype.card d) * Fintype.card d * ‖Pc‖) * ‖x‖ := by
          ring

/-- The manuscript's `c_d` exists automatically once Hamiltonian extraction
is a linear projection on a finite-dimensional channel space. -/
theorem compiled_generator_hs_bound_of_finiteDimensional_projection
    (P : E →ₗ[ℝ] Matrix d d ℂ) :
    ∃ cd : ℝ, 0 ≤ cd ∧ ∀ x : E,
      (P x)ᴴ = P x → (P x).trace = 0 →
      matrixHSNorm (P x) ≤
        cd / Real.sqrt (2 * Fintype.card d) * ‖x‖ := by
  obtain ⟨cd, hcd, hbound⟩ := finiteDimensional_channel_to_adHS_bound P
  refine ⟨cd, hcd, ?_⟩
  intro x hx htr
  exact compiled_generator_hs_bound (P x) 0 cd ‖x‖
    (by simpa using hx) (by simpa using htr) (by simpa using hbound x hx)

/-- Vanishing channel error implies vanishing Hamiltonian-projection error,
with no norm-comparison hypothesis: finite dimensionality supplies it. -/
theorem compiled_generator_hs_tendsto_of_finiteDimensional_projection
    (P : E →ₗ[ℝ] Matrix d d ℂ) (x : ℝ → E)
    (hx : Tendsto (fun h => ‖x h‖) (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hHerm : ∀ h, (P (x h))ᴴ = P (x h))
    (htr : ∀ h, (P (x h)).trace = 0) :
    Tendsto (fun h => matrixHSNorm (P (x h)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  obtain ⟨cd, _hcd, hbound⟩ :=
    compiled_generator_hs_bound_of_finiteDimensional_projection P
  have hlim : Tendsto
      (fun h => cd / Real.sqrt (2 * Fintype.card d) * ‖x h‖)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using hx.const_mul (cd / Real.sqrt (2 * Fintype.card d))
  exact squeeze_zero'
    (Eventually.of_forall fun h => Real.sqrt_nonneg _)
    (Eventually.of_forall fun h => hbound (x h) (hHerm h) (htr h)) hlim

end Projection

section Combined

variable {A : Type} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

/-- Combined generator and projected-Hamiltonian convergence.  This is the
exact finite-dimensional norm-equivalence closure of
`thm:SMST-compiled-channel-generator`: the only analytic input is the stated
`o(h)` compiled-channel error. -/
theorem compiled_channel_generator_and_hamiltonian_convergence
    (W : ℝ → A) (adD : A) (ε : ℝ → ℝ) (h₀ : ℝ) (hh₀ : 0 < h₀)
    (P : A →ₗ[ℝ] Matrix d d ℂ)
    (hPHerm : ∀ x, (P x)ᴴ = P x)
    (hPtr : ∀ x, (P x).trace = 0)
    (hε : Tendsto ε (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hW : ∀ h ∈ Ioc (0 : ℝ) h₀,
      ‖W h - exp (h • adD)‖ ≤ ε h * h) :
    let err := fun h : ℝ => h⁻¹ • (W h - 1) - adD
    Tendsto (fun h => ‖err h‖) (nhdsWithin 0 (Ioi 0)) (nhds 0)
      ∧ Tendsto (fun h => matrixHSNorm (P (err h)))
          (nhdsWithin 0 (Ioi 0)) (nhds 0)
      ∧ ∃ cd : ℝ, 0 ≤ cd ∧ ∀ h,
          matrixHSNorm (P (err h)) ≤
            cd / Real.sqrt (2 * Fintype.card d) * ‖err h‖ := by
  dsimp only
  have hgen := compiled_generator_convergence W adD ε h₀ hh₀ hε hW
  refine ⟨hgen,
    compiled_generator_hs_tendsto_of_finiteDimensional_projection P _ hgen
      (fun h => hPHerm _) (fun h => hPtr _), ?_⟩
  obtain ⟨cd, hcd, hbound⟩ :=
    compiled_generator_hs_bound_of_finiteDimensional_projection P
  exact ⟨cd, hcd, fun h => hbound _ (hPHerm _) (hPtr _)⟩

end Combined

end SMSTChannel
end NCG
