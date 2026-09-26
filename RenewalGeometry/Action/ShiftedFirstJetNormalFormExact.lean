/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Action.ShiftedJetActionHessianExact

/-!
# Discrete summation by parts and the shifted-first-jet coefficient identity
  (`lem:native-firstjet-normal-form`, Einstein–Standard-Model action-closure manuscript)

The two exact identities used in the proof of `lem:native-firstjet-normal-form`:

* `eq:native-SBP`, the discrete product rule
  `⟨C, δ⁺_μ W⟩ = -⟨δ⁻_μ C, W⟩ + δ⁻_μ ⟨C, T_μ W⟩`
  (`inner_fwdDiff_eq`), whose lattice-divergence term sums to zero on the
  periodic grid (`sum_bwdDiff`) and, on a sub-box `S`, to the exact collar
  functional `h⁻¹(Σ_{x ∈ S} g(x) - Σ_{x ∈ S - e_μ} g(x))` (`sum_bwdDiff_eq_collar`),
  giving the exact summation-by-parts identities `sum_inner_fwdDiff` and
  `sum_inner_fwdDiff_box`;
* `eq:native-C-firstjet`, the coefficient identity
  `δ⁻_μ C(e) = ∫₀¹ DC(e₋ + t h p₋)[p₋] dt`
  with `e₋ = T_{-μ} e`, `p₋ = T_{-μ} δ⁺_μ e` (`bwdDiff_eq_integral`,
  from the pointwise form `smul_sub_eq_integral`), a shifted-first-jet
  expression with no inverse power of `h`.

Not covered here (disclosed): the exact decomposition of the Cartan
plaquette logarithm `R^h` into a discrete curl of the coframe connection plus
a regular function of shifted connections, and hence the full normal form
`eq:native-firstjet-normal-form` of the local action `eq:native-local-action`,
which requires the complete definition of the local densities.
-/

open Finset

namespace RenewalGeometry
namespace ShiftedFirstJet

open ShiftedJetAction (Grid unitVec sum_translate)

variable {n : ℕ} [NeZero n]

/-- The backward difference `δ⁻_μ f (x) = (f(x) - f(x - e_μ))/h`. -/
noncomputable def bwdDiff {V : Type*} [AddCommGroup V] [Module ℝ V] (h : ℝ) (μ : Fin 4)
    (f : Grid n → V) (x : Grid n) : V :=
  h⁻¹ • (f x - f (x - unitVec n μ))

/-- The shift `T_μ W (x) = W (x + e_μ)`. -/
def shift (μ : Fin 4) {V : Type*} (W : Grid n → V) (x : Grid n) : V := W (x + unitVec n μ)

section SBP

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `eq:native-SBP`: the discrete product rule
`⟨C, δ⁺_μ W⟩ = -⟨δ⁻_μ C, W⟩ + δ⁻_μ ⟨C, T_μ W⟩`, pointwise. -/
theorem inner_fwdDiff_eq (h : ℝ) (μ : Fin 4) (C W : Grid n → V) (x : Grid n) :
    inner ℝ (C x) (ShiftedJetAction.fwdDiff h μ W x) =
      -inner ℝ (bwdDiff h μ C x) (W x) +
        bwdDiff h μ (fun z => inner ℝ (C z) (shift μ W z)) x := by
  unfold ShiftedJetAction.fwdDiff bwdDiff shift
  simp only [inner_smul_right, inner_smul_left, inner_sub_right, inner_sub_left, smul_eq_mul,
    sub_add_cancel, RCLike.conj_to_real]
  ring

/-- The periodic lattice divergence sums to zero. -/
theorem sum_bwdDiff (h : ℝ) (μ : Fin 4) (g : Grid n → ℝ) :
    ∑ x, bwdDiff h μ g x = 0 := by
  unfold bwdDiff
  have := sum_translate g (-unitVec n μ)
  simp only [← sub_eq_add_neg] at this
  rw [← smul_sum, sum_sub_distrib, this, sub_self, smul_zero]

/-- On a sub-box `S`, the lattice divergence sums to the exact collar functional
`h⁻¹(Σ_{x ∈ S} g(x) - Σ_{x ∈ S - e_μ} g(x))`, which depends on `g` only near the
boundary of `S`. -/
theorem sum_bwdDiff_eq_collar (h : ℝ) (μ : Fin 4) (g : Grid n → ℝ) (S : Finset (Grid n)) :
    ∑ x ∈ S, bwdDiff h μ g x =
      h⁻¹ * (∑ x ∈ S, g x - ∑ x ∈ S.map (Equiv.subRight (unitVec n μ)).toEmbedding, g x) := by
  unfold bwdDiff
  rw [← smul_sum, sum_sub_distrib, sum_map, smul_eq_mul]
  rfl

/-- Exact periodic summation by parts: `Σ_x ⟨C, δ⁺_μ W⟩ = -Σ_x ⟨δ⁻_μ C, W⟩`. -/
theorem sum_inner_fwdDiff (h : ℝ) (μ : Fin 4) (C W : Grid n → V) :
    ∑ x, inner ℝ (C x) (ShiftedJetAction.fwdDiff h μ W x) = -∑ x, inner ℝ (bwdDiff h μ C x) (W x) := by
  simp_rw [inner_fwdDiff_eq]
  rw [sum_add_distrib, sum_bwdDiff, sum_neg_distrib, add_zero]

/-- Exact summation by parts on a sub-box with the collar functional. -/
theorem sum_inner_fwdDiff_box (h : ℝ) (μ : Fin 4) (C W : Grid n → V) (S : Finset (Grid n)) :
    ∑ x ∈ S, inner ℝ (C x) (ShiftedJetAction.fwdDiff h μ W x) =
      -∑ x ∈ S, inner ℝ (bwdDiff h μ C x) (W x) +
        h⁻¹ * (∑ x ∈ S, inner ℝ (C x) (shift μ W x) -
          ∑ x ∈ S.map (Equiv.subRight (unitVec n μ)).toEmbedding, inner ℝ (C x) (shift μ W x)) := by
  simp_rw [inner_fwdDiff_eq]
  rw [sum_add_distrib, sum_neg_distrib, sum_bwdDiff_eq_collar]

end SBP

section FirstJet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-- Pointwise form of `eq:native-C-firstjet`: for a `C¹` coefficient `C`,
`(C(a + h p) - C(a))/h = ∫₀¹ DC(a + t h p)[p] dt`. -/
theorem smul_sub_eq_integral {C : E → F} (hC : ContDiff ℝ 1 C) {h : ℝ} (hh : h ≠ 0)
    (a p : E) :
    h⁻¹ • (C (a + h • p) - C a) = ∫ t in (0 : ℝ)..1, fderiv ℝ C (a + t • (h • p)) p := by
  have hdiff : ∀ t : ℝ, HasDerivAt (fun t : ℝ => C (a + t • (h • p)))
      (fderiv ℝ C (a + t • (h • p)) (h • p)) t := by
    intro t
    have hg : HasDerivAt (fun t : ℝ => a + t • (h • p)) (h • p) t := by
      simpa using ((hasDerivAt_id t).smul_const (h • p)).const_add a
    have hf : HasFDerivAt C (fderiv ℝ C (a + t • (h • p))) (a + t • (h • p)) :=
      (hC.differentiable one_ne_zero _).hasFDerivAt
    exact hf.comp_hasDerivAt t hg
  have hcont : Continuous fun t : ℝ => fderiv ℝ C (a + t • (h • p)) (h • p) := by
    have h1 : Continuous fun t : ℝ => a + t • (h • p) := by fun_prop
    exact ((hC.continuous_fderiv one_ne_zero).comp h1).clm_apply continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun t _ => hdiff t) (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero] at hFTC
  have hlin : ∀ t : ℝ, fderiv ℝ C (a + t • (h • p)) (h • p) =
      h • fderiv ℝ C (a + t • (h • p)) p := fun t => by rw [map_smul]
  simp_rw [hlin] at hFTC
  rw [intervalIntegral.integral_smul] at hFTC
  rw [← hFTC, smul_smul, inv_mul_cancel₀ hh, one_smul]

/-- `eq:native-C-firstjet`: with `e₋ = T_{-μ} e` and `p₋ = T_{-μ} δ⁺_μ e`,
`δ⁻_μ C(e)(x) = ∫₀¹ DC(e₋ + t h p₋)[p₋] dt`. -/
theorem bwdDiff_eq_integral {C : E → F} (hC : ContDiff ℝ 1 C) {h : ℝ} (hh : h ≠ 0)
    (μ : Fin 4) (e : Grid n → E) (x : Grid n) :
    bwdDiff h μ (fun z => C (e z)) x =
      ∫ t in (0 : ℝ)..1, fderiv ℝ C (e (x - unitVec n μ) +
        t • (h • ShiftedJetAction.fwdDiff h μ e (x - unitVec n μ))) (ShiftedJetAction.fwdDiff h μ e (x - unitVec n μ)) := by
  have hrec : e x = e (x - unitVec n μ) + h • ShiftedJetAction.fwdDiff h μ e (x - unitVec n μ) := by
    unfold ShiftedJetAction.fwdDiff
    rw [smul_smul, mul_inv_cancel₀ hh, one_smul, sub_add_cancel, add_sub_cancel]
  rw [← smul_sub_eq_integral hC hh, ← hrec]
  rfl

end FirstJet

end ShiftedFirstJet
end RenewalGeometry
