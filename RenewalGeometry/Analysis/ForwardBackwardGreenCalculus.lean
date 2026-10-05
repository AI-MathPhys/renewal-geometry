/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.ForwardBackwardVariationOfConstants

/-!
# Calculus of the forward–backward Green operator

Complement to `Analysis/ForwardBackwardVariationOfConstants.lean` (emergent-spacetime manuscript,
`eq:supp-exact-green`, `thm:supp-exact-boundary`).  There, the variation-of-constants formula shows
that every solution of `e' = D e + F` is given by its boundary data and the Green operator
`(𝒢_S F)(s) = ∫₀ˢ e^{(s-r)D} Π₋ F(r) dr - ∫ₛˢ e^{(s-r)D} Π₊ F(r) dr`.  Here we prove the converse
direction ("the integral equation is equivalent to the specified differential and boundary
conditions"):

* `FBGreen.green_eq_factor`: `𝒢_S F (s) = e^{sD}∫₀ˢ e^{-rD}Π₋F - e^{sD}∫ₛˢ e^{-rD}Π₊F`;
* `FBGreen.hasDerivAt_green`: for continuous `F`, `(𝒢_S F)' = D 𝒢_S F + F` everywhere;
* `FBGreen.green_boundary_zero` / `FBGreen.green_boundary_end`: `Π₋ (𝒢_S F)(0) = 0` and
  `Π₊ (𝒢_S F)(S) = 0` (complementary idempotents);
* `FBGreen.green_sub_of_continuous`: linearity.
-/

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

namespace RenewalGeometry
namespace FBGreen

open FBVariation

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem prop_add (D : E →L[ℝ] E) (s t : ℝ) : prop D (s + t) = prop D s * prop D t := by
  unfold prop
  rw [add_smul]
  have hr := NormedSpace.expSeries_radius_eq_top ℝ (E →L[ℝ] E)
  exact NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl D).smul_left s).smul_right t) (hr.symm ▸ edist_lt_top _ _)
    (hr.symm ▸ edist_lt_top _ _)

theorem prop_zero (D : E →L[ℝ] E) : prop D 0 = 1 := by simp [prop]

theorem prop_sub (D : E →L[ℝ] E) (s r : ℝ) : prop D (s - r) = prop D s * prop D (-r) := by
  rw [sub_eq_add_neg, prop_add]

theorem prop_mul_neg (D : E →L[ℝ] E) (s : ℝ) : prop D s * prop D (-s) = 1 := by
  rw [← prop_add, add_neg_cancel, prop_zero]

theorem prop_apply_comm (D P : E →L[ℝ] E) (hP : Commute D P) (t : ℝ) (x : E) :
    prop D t (P x) = P (prop D t x) := by
  rw [← ContinuousLinearMap.mul_apply, prop_commute D P hP t, ContinuousLinearMap.mul_apply]

theorem prop_apply_D (D : E →L[ℝ] E) (t : ℝ) (x : E) : prop D t (D x) = D (prop D t x) :=
  prop_apply_comm D D (Commute.refl D) t x

theorem continuous_prop_apply (D P : E →L[ℝ] E) (c : ℝ) {g : ℝ → E} (hg : Continuous g) :
    Continuous fun r => prop D (c - r) (P (g r)) :=
  ((continuous_prop D).comp (continuous_const.sub continuous_id)).clm_apply
    (P.continuous.comp hg)

theorem continuous_prop_neg_apply (D P : E →L[ℝ] E) {g : ℝ → E} (hg : Continuous g) :
    Continuous fun r => prop D (-r) (P (g r)) :=
  ((continuous_prop D).comp continuous_neg).clm_apply (P.continuous.comp hg)

/-- **Factorisation of the Green operator** through `e^{(s-r)D} = e^{sD} e^{-rD}`. -/
theorem green_eq_factor (D Pp Pm : E →L[ℝ] E) (S : ℝ) {g : ℝ → E} (hg : Continuous g) (s : ℝ) :
    green D Pp Pm S g s =
      prop D s (∫ r in (0 : ℝ)..s, prop D (-r) (Pm (g r)))
        - prop D s (∫ r in s..S, prop D (-r) (Pp (g r))) := by
  have hm := (continuous_prop_neg_apply D Pm hg).intervalIntegrable (μ := volume) 0 s
  have hp := (continuous_prop_neg_apply D Pp hg).intervalIntegrable (μ := volume) s S
  rw [← (prop D s).intervalIntegral_comp_comm hm, ← (prop D s).intervalIntegral_comp_comm hp]
  unfold green
  congr 1 <;> refine intervalIntegral.integral_congr fun r _ => ?_ <;>
    simp only [prop_sub, ContinuousLinearMap.mul_apply]

/-- **The Green operator solves the inhomogeneous equation**: for continuous `g`,
`(𝒢_S g)' = D (𝒢_S g) + g` at every `s`. -/
theorem hasDerivAt_green (D Pp Pm : E →L[ℝ] E) (hsum : Pp + Pm = 1) (S : ℝ) {g : ℝ → E}
    (hg : Continuous g) (s : ℝ) :
    HasDerivAt (green D Pp Pm S g) (D (green D Pp Pm S g s) + g s) s := by
  have hcm := continuous_prop_neg_apply D Pm hg
  have hcp := continuous_prop_neg_apply D Pp hg
  have hIm : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, prop D (-r) (Pm (g r)))
      (prop D (-s) (Pm (g s))) s :=
    intervalIntegral.integral_hasDerivAt_right (hcm.intervalIntegrable _ _)
      (hcm.stronglyMeasurableAtFilter _ _) hcm.continuousAt
  have hIp : HasDerivAt (fun u => ∫ r in u..S, prop D (-r) (Pp (g r)))
      (-prop D (-s) (Pp (g s))) s :=
    intervalIntegral.integral_hasDerivAt_left (hcp.intervalIntegrable _ _)
      (hcp.stronglyMeasurableAtFilter _ _) hcp.continuousAt
  have h1 := (hasDerivAt_prop D s).clm_apply hIm
  have h2 := (hasDerivAt_prop D s).clm_apply hIp
  have hfun : green D Pp Pm S g = fun u =>
      prop D u (∫ r in (0 : ℝ)..u, prop D (-r) (Pm (g r)))
        - prop D u (∫ r in u..S, prop D (-r) (Pp (g r))) :=
    funext fun u => green_eq_factor D Pp Pm S hg u
  have hc : ∀ x : E, prop D s (prop D (-s) x) = x := fun x => by
    rw [← ContinuousLinearMap.mul_apply, prop_mul_neg, ContinuousLinearMap.one_apply]
  have hsplit : g s = Pp (g s) + Pm (g s) := by
    rw [← ContinuousLinearMap.add_apply, hsum, ContinuousLinearMap.one_apply]
  rw [hfun]
  refine (h1.sub h2).congr_deriv ?_
  simp only [ContinuousLinearMap.mul_apply, map_neg, hc, prop_apply_D, map_sub]
  conv_rhs => rw [hsplit]
  abel

theorem continuous_green (D Pp Pm : E →L[ℝ] E) (hsum : Pp + Pm = 1) (S : ℝ) {g : ℝ → E}
    (hg : Continuous g) : Continuous (green D Pp Pm S g) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_green D Pp Pm hsum S hg s).continuousAt

theorem mul_eq_zero_of_compl (Pp Pm : E →L[ℝ] E) (hsum : Pp + Pm = 1) (hPm : Pm * Pm = Pm) :
    Pm * Pp = 0 := by
  have : Pp = 1 - Pm := eq_sub_of_add_eq hsum
  rw [this, mul_sub, mul_one, hPm, sub_self]

theorem mul_eq_zero_of_compl' (Pp Pm : E →L[ℝ] E) (hsum : Pp + Pm = 1) (hPp : Pp * Pp = Pp) :
    Pp * Pm = 0 := by
  have : Pm = 1 - Pp := eq_sub_of_add_eq' hsum
  rw [this, mul_sub, mul_one, hPp, sub_self]

/-- **Initial boundary condition**: `Π₋ (𝒢_S g)(0) = 0`. -/
theorem green_boundary_zero (D Pp Pm : E →L[ℝ] E) (hsum : Pp + Pm = 1) (hm : Commute D Pm)
    (hPm : Pm * Pm = Pm) (S : ℝ) {g : ℝ → E} (hg : Continuous g) :
    Pm (green D Pp Pm S g 0) = 0 := by
  have h0 := mul_eq_zero_of_compl Pp Pm hsum hPm
  have hint := (continuous_prop_neg_apply D Pp hg).intervalIntegrable (μ := volume) 0 S
  simp only [green, intervalIntegral.integral_same, zero_sub, map_neg]
  rw [← Pm.intervalIntegral_comp_comm hint, neg_eq_zero]
  have hz : ∀ r, Pm (prop D (-r) (Pp (g r))) = 0 := fun r => by
    rw [← prop_apply_comm D Pm hm, ← ContinuousLinearMap.mul_apply Pm Pp, h0]
    simp
  simp [hz]

/-- **Terminal boundary condition**: `Π₊ (𝒢_S g)(S) = 0`. -/
theorem green_boundary_end (D Pp Pm : E →L[ℝ] E) (hsum : Pp + Pm = 1) (hp : Commute D Pp)
    (hPp : Pp * Pp = Pp) (S : ℝ) {g : ℝ → E} (hg : Continuous g) :
    Pp (green D Pp Pm S g S) = 0 := by
  have h0 := mul_eq_zero_of_compl' Pp Pm hsum hPp
  have hint := (continuous_prop_apply D Pm S hg).intervalIntegrable (μ := volume) 0 S
  simp only [green, intervalIntegral.integral_same, sub_zero]
  rw [← Pp.intervalIntegral_comp_comm hint]
  have hz : ∀ r, Pp (prop D (S - r) (Pm (g r))) = 0 := fun r => by
    rw [← prop_apply_comm D Pp hp, ← ContinuousLinearMap.mul_apply Pp Pm, h0]
    simp
  simp [hz]

/-- Linearity of the Green operator on continuous functions. -/
theorem green_sub_of_continuous (D Pp Pm : E →L[ℝ] E) (S : ℝ) {f g : ℝ → E}
    (hf : Continuous f) (hg : Continuous g) (s : ℝ) :
    green D Pp Pm S f s - green D Pp Pm S g s = green D Pp Pm S (fun r => f r - g r) s := by
  have h1 := intervalIntegral.integral_sub
    ((continuous_prop_apply D Pm s hf).intervalIntegrable (μ := volume) 0 s)
    ((continuous_prop_apply D Pm s hg).intervalIntegrable (μ := volume) 0 s)
  have h2 := intervalIntegral.integral_sub
    ((continuous_prop_apply D Pp s hf).intervalIntegrable (μ := volume) s S)
    ((continuous_prop_apply D Pp s hg).intervalIntegrable (μ := volume) s S)
  simp only [green, map_sub]
  rw [h1, h2]
  abel

/-- The Green operator only sees the values of its argument on `[0, S]`. -/
theorem green_congr (D Pp Pm : E →L[ℝ] E) {S : ℝ} {f g : ℝ → E}
    (hfg : ∀ r ∈ Icc 0 S, f r = g r) {s : ℝ} (hs : s ∈ Icc 0 S) :
    green D Pp Pm S f s = green D Pp Pm S g s := by
  unfold green
  congr 1
  · refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.1] at hr
    simp only [hfg r ⟨hr.1, hr.2.trans hs.2⟩]
  · refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.2] at hr
    simp only [hfg r ⟨hs.1.trans hr.1, hr.2⟩]

end FBGreen
end RenewalGeometry
