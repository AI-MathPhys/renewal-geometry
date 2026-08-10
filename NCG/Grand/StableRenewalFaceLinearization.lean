/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FaceLinearization

/-!
# Stable renewal face linearization

This file completes the stable branch of `thm:renewal-face-linearization` from the
Gran-Tensor manuscript.  A summable one-step transport error makes the dyadically
renormalized functionals converge, with the expected explicit tail estimate.  A
vanishing quadratic additivity defect makes the limit additive, while continuity
of one approximant makes that additive limit a continuous real-linear functional.

The first theorem also packages the regularity step omitted from the exact branch:
an additive real-valued functional which is bounded on a neighborhood of zero is
automatically a continuous real-linear functional.
-/

open Filter Finset
open scoped Topology

namespace NCG

/-- An additive real-valued functional which is bounded on a neighborhood of zero
has a unique realization as a continuous real-linear functional.  This is the
regularity step in the exact branch of `thm:renewal-face-linearization`. -/
theorem additive_locallyBounded_toContinuousLinearMap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → ℝ) (hadd : ∀ x y, A (x + y) = A x + A y)
    {s : Set E} (hs : s ∈ 𝓝 (0 : E))
    (hbounded : Bornology.IsBounded (A '' s)) :
    ∃! ell : E →L[ℝ] ℝ, ∀ x, ell x = A x := by
  have hzero : A 0 = 0 := by
    have h := hadd 0 0
    simp only [zero_add] at h
    linarith
  let f : E →+ ℝ :=
    { toFun := A
      map_zero' := hzero
      map_add' := hadd }
  have hf : Continuous f :=
    f.continuous_of_isBounded_nhds_zero hs hbounded
  refine ⟨f.toRealLinearMap hf, ?_, ?_⟩
  · intro x
    rfl
  · intro g hg
    ext x
    exact (hg x).trans rfl

/-- The canonical series limit of a sequence of approximately compatible face
functionals. -/
noncomputable def stableRenewalFaceLimit {E : Type*}
    (L : ℕ → E → ℝ) (z : E) : ℝ :=
  L 0 z + ∑' n : ℕ, (L (n + 1) z - L n z)

/-- Stable derivative-free renewal face linearization.

The conclusion records pointwise convergence, the sharp summable-tail estimate,
uniform control on every norm-bounded set, convergence of the scalar tail to zero,
and uniqueness of the resulting continuous real-linear functional. -/
theorem stable_renewal_face_linearization {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℕ → E → ℝ) (ε η : ℕ → ℝ)
    (hε_nonneg : ∀ m, 0 ≤ ε m) (hε_sum : Summable ε)
    (htransport : ∀ m z, |L (m + 1) z - L m z| ≤ ε m * ‖z‖)
    (hη_zero : Tendsto η atTop (𝓝 0))
    (hquasi : ∀ m x y,
      |L m (x + y) - L m x - L m y| ≤ η m * ‖x‖ * ‖y‖)
    (m₀ : ℕ) (hcontinuous : ContinuousAt (L m₀) 0) :
    ∃! ell : E →L[ℝ] ℝ,
      (∀ z, Tendsto (fun m => L m z) atTop (𝓝 (ell z))) ∧
      (∀ m z,
        |ell z - L m z| ≤ (∑' n : ℕ, ε (n + m)) * ‖z‖) ∧
      (∀ R m z, ‖z‖ ≤ R →
        |ell z - L m z| ≤ (∑' n : ℕ, ε (n + m)) * R) ∧
      Tendsto (fun m => ∑' n : ℕ, ε (n + m)) atTop (𝓝 0) := by
  let inc : ℕ → E → ℝ := fun m z => L (m + 1) z - L m z
  let A : E → ℝ := stableRenewalFaceLimit L
  have hinc_sum (z : E) : Summable (fun m => inc m z) := by
    apply (hε_sum.mul_right ‖z‖).of_norm_bounded
    intro m
    simpa [inc, Real.norm_eq_abs] using htransport m z
  have hpartial (m : ℕ) (z : E) :
      L m z = L 0 z + ∑ n ∈ range m, inc n z := by
    induction m with
    | zero => simp
    | succ m ihm =>
        rw [sum_range_succ, ← add_assoc, ← ihm]
        simp [inc]
  have hpointwise (z : E) :
      Tendsto (fun m => L m z) atTop (𝓝 (A z)) := by
    have hsum := (hinc_sum z).hasSum.tendsto_sum_nat
    have hconst : Tendsto (fun _ : ℕ => L 0 z) atTop (𝓝 (L 0 z)) :=
      tendsto_const_nhds
    have hadd := hconst.add hsum
    have hfun : (fun m => L m z) =
        (fun m => L 0 z + ∑ n ∈ range m, inc n z) :=
      funext fun m => hpartial m z
    rw [hfun]
    simpa only [A, stableRenewalFaceLimit] using hadd
  have htail_identity (m : ℕ) (z : E) :
      A z - L m z = ∑' n : ℕ, inc (n + m) z := by
    have hsplit := (hinc_sum z).sum_add_tsum_nat_add m
    rw [hpartial]
    simp only [A, stableRenewalFaceLimit]
    linarith
  have htail (m : ℕ) (z : E) :
      |A z - L m z| ≤ (∑' n : ℕ, ε (n + m)) * ‖z‖ := by
    rw [htail_identity, ← tsum_mul_right]
    change ‖∑' n : ℕ, inc (n + m) z‖ ≤ ∑' n : ℕ, ε (n + m) * ‖z‖
    apply tsum_of_norm_bounded
      (((summable_nat_add_iff m).2 hε_sum).mul_right ‖z‖).hasSum
    intro n
    simpa [inc, Real.norm_eq_abs] using htransport (n + m) z
  have htail_zero :
      Tendsto (fun m => ∑' n : ℕ, ε (n + m)) atTop (𝓝 0) :=
    tendsto_sum_nat_add ε
  have hadd : ∀ x y : E, A (x + y) = A x + A y := by
    intro x y
    have hconv : Tendsto
        (fun m => L m (x + y) - L m x - L m y)
        atTop (𝓝 (A (x + y) - A x - A y)) :=
      ((hpointwise (x + y)).sub (hpointwise x)).sub (hpointwise y)
    have hbound : Tendsto (fun m => η m * ‖x‖ * ‖y‖) atTop (𝓝 0) := by
      simpa using (hη_zero.mul_const ‖x‖).mul_const ‖y‖
    have hle : |A (x + y) - A x - A y| ≤ 0 :=
      le_of_tendsto_of_tendsto
        (hconv.abs) hbound (Eventually.of_forall fun m => hquasi m x y)
    have hz : A (x + y) - A x - A y = 0 :=
      abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    linarith
  have hA_zero : A 0 = 0 := by
    have h := hadd 0 0
    simp only [zero_add] at h
    linarith
  have hresidual : Tendsto (fun z => A z - L m₀ z) (𝓝 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun z => norm_nonneg (A z - L m₀ z))
      (fun z => by simpa [Real.norm_eq_abs] using htail m₀ z)
    simpa using
      (tendsto_const_nhds.mul
        (tendsto_norm_zero : Tendsto (fun z : E => ‖z‖) (𝓝 0) (𝓝 0)))
  have hA_continuousAt : ContinuousAt A 0 := by
    have hsum := hresidual.add hcontinuous
    have hLm_zero : L m₀ 0 = A 0 := by
      have h := htail m₀ 0
      have h' : |A 0 - L m₀ 0| ≤ 0 := by simpa using h
      have habs : |A 0 - L m₀ 0| = 0 :=
        le_antisymm h' (abs_nonneg _)
      exact (sub_eq_zero.mp (abs_eq_zero.mp habs)).symm
    change Tendsto A (𝓝 0) (𝓝 (A 0))
    simpa only [sub_add_cancel, hLm_zero, zero_add] using hsum
  let f : E →+ ℝ :=
    { toFun := A
      map_zero' := hA_zero
      map_add' := hadd }
  have hf : Continuous f := continuous_of_continuousAt_zero f hA_continuousAt
  let ell : E →L[ℝ] ℝ := f.toRealLinearMap hf
  have hell_apply (z : E) : ell z = A z := rfl
  refine ⟨ell, ?_, ?_⟩
  · refine ⟨fun z => by simpa [hell_apply] using hpointwise z, ?_, ?_, htail_zero⟩
    · intro m z
      simpa [hell_apply] using htail m z
    · intro R m z hz
      calc
        |ell z - L m z|
            ≤ (∑' n : ℕ, ε (n + m)) * ‖z‖ := by
                simpa [hell_apply] using htail m z
        _ ≤ (∑' n : ℕ, ε (n + m)) * R := by
          gcongr
          exact tsum_nonneg fun n => hε_nonneg (n + m)
  · intro g hg
    ext z
    exact tendsto_nhds_unique (hg.1 z) (hpointwise z)

end NCG
