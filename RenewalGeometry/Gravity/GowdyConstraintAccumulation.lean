/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdyConstraintIncrementExact
import RenewalGeometry.Analysis.PeriodicGridResidualInverseEstimate

/-!
# Accumulated staggered-constraint error of a residual-perturbed Gowdy history
  (`prop:supp-gowdy-residual-control`, last clause; emergent-spacetime supplement)

Along a history `X_{k+1} = Φ_h(X_k) + r_k` of the Gowdy symmetric splitting (frames of the
deterministic predictions `B_k = Φ_h(X_k)` and of the actual states `X_{k+1}` in the envelope
`‖U‖_∞ ≤ R'`), the exact constraint increment `eq:supp-gowdy-constraint-increment`
(`staggeredMomentum_residual_increment`) is bounded at every site by
`|D₊ r^λ| + 8R' ‖r^U‖_∞ ≤ (1 + 8R') ‖r_k‖_{1,∞,ℓ}` (`abs_staggeredMomentum_step_le`), with
`|𝒥(a) - 𝒥(b)| ≤ 2(‖a‖ + ‖b‖) ‖a - b‖` (`abs_J_sub_le`).  Telescoping and the residual budget
`sum_crNorm_le_sqrt_residualFlux` (`r = 1`) give (`staggeredMomentum_accumulated`)

`|𝒦_ℓ(X_n)(j)| ≤ |𝒦_ℓ(X_0)(j)| + 2(1 + 8R') √(2nh) √𝓕_h`,  `𝓕_h = ℓ^{-3} 𝓔_h`,

the bound "initial value plus `C √𝓕_h`" of `prop:supp-gowdy-residual-control`.  Since
`𝓕_h^{(1)} ≤ 𝓕_h^{(r)}` for `ℓ ≤ 1` and `r ≥ 1` (`residualFlux_one_le`), the same bound holds with
the flux of every order `r ≥ 1` (`staggeredMomentum_accumulated_of_le`).
-/

open Finset

namespace RenewalGeometry.GowdyStaggered

namespace ConstraintAccumulation

noncomputable section

open PeriodicGridResidual

variable {N : ℕ} [NeZero N]

/-- `|𝒥(a) - 𝒥(b)| ≤ 2(‖a‖ + ‖b‖)‖a - b‖` (sup norms on `ℝ⁴`). -/
theorem abs_J_sub_le (a b : Fin 4 → ℝ) : |J a - J b| ≤ 2 * (‖a‖ + ‖b‖) * ‖a - b‖ := by
  have ha : ∀ i, |a i| ≤ ‖a‖ := fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm a i
  have hb : ∀ i, |b i| ≤ ‖b‖ := fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b i
  have hd : ∀ i, |a i - b i| ≤ ‖a - b‖ := fun i => by
    rw [← Real.norm_eq_abs, ← Pi.sub_apply]; exact norm_le_pi_norm (a - b) i
  have e : J a - J b = (a 0 - b 0) * a 1 + b 0 * (a 1 - b 1) + ((a 2 - b 2) * a 3 +
      b 2 * (a 3 - b 3)) := by simp only [J]; ring
  rw [e]
  have h1 : |(a 0 - b 0) * a 1| ≤ ‖a - b‖ * ‖a‖ := by
    rw [abs_mul]; exact mul_le_mul (hd 0) (ha 1) (abs_nonneg _) (norm_nonneg _)
  have h2 : |b 0 * (a 1 - b 1)| ≤ ‖b‖ * ‖a - b‖ := by
    rw [abs_mul]; exact mul_le_mul (hb 0) (hd 1) (abs_nonneg _) (norm_nonneg _)
  have h3 : |(a 2 - b 2) * a 3| ≤ ‖a - b‖ * ‖a‖ := by
    rw [abs_mul]; exact mul_le_mul (hd 2) (ha 3) (abs_nonneg _) (norm_nonneg _)
  have h4 : |b 2 * (a 3 - b 3)| ≤ ‖b‖ * ‖a - b‖ := by
    rw [abs_mul]; exact mul_le_mul (hb 2) (hd 3) (abs_nonneg _) (norm_nonneg _)
  have t1 := abs_add_le ((a 0 - b 0) * a 1 + b 0 * (a 1 - b 1))
    ((a 2 - b 2) * a 3 + b 2 * (a 3 - b 3))
  have t2 := abs_add_le ((a 0 - b 0) * a 1) (b 0 * (a 1 - b 1))
  have t3 := abs_add_le ((a 2 - b 2) * a 3) (b 2 * (a 3 - b 3))
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b)]

/-- The residual array `j ↦ (r^U_j, r^λ_j)` of one step. -/
def resArr (rU : ZMod N → Fin 4 → ℝ) (rlam : ZMod N → ℝ) : ZMod N → (Fin 4 → ℝ) × ℝ :=
  fun j => (rU j, rlam j)

theorem norm_le_crNorm_one (ℓ : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ZMod N → E) : ‖v‖ ≤ crNorm 1 ℓ v :=
  Finset.le_sup' (fun k => ‖(PeriodicGridResidual.fwdDiff ℓ)^[k] v‖)
    (show (0 : ℕ) ∈ range (1 + 1) from mem_range.2 (by norm_num))

theorem norm_fwdDiff_le_crNorm_one (ℓ : ℝ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : ZMod N → E) : ‖PeriodicGridResidual.fwdDiff ℓ v‖ ≤ crNorm 1 ℓ v :=
  Finset.le_sup' (fun k => ‖(PeriodicGridResidual.fwdDiff ℓ)^[k] v‖)
    (show (1 : ℕ) ∈ range (1 + 1) from mem_range.2 (by norm_num))

theorem norm_rU_le_crNorm (ℓ : ℝ) (rU : ZMod N → Fin 4 → ℝ) (rlam : ZMod N → ℝ) (j : ZMod N) :
    ‖rU j‖ ≤ crNorm 1 ℓ (resArr rU rlam) :=
  (norm_fst_le (resArr rU rlam j)).trans ((norm_le_pi_norm (resArr rU rlam) j).trans
    (norm_le_crNorm_one ℓ _))

theorem abs_fwdDiff_rlam_le_crNorm (ℓ : ℝ) (rU : ZMod N → Fin 4 → ℝ) (rlam : ZMod N → ℝ)
    (j : ZMod N) : |(rlam (j + 1) - rlam j) / ℓ| ≤ crNorm 1 ℓ (resArr rU rlam) := by
  have e : (PeriodicGridResidual.fwdDiff ℓ (resArr rU rlam) j).2 = (rlam (j + 1) - rlam j) / ℓ := by
    simp [PeriodicGridResidual.fwdDiff, resArr, div_eq_inv_mul]
  rw [← e, ← Real.norm_eq_abs]
  exact (norm_snd_le _).trans ((norm_le_pi_norm _ j).trans (norm_fwdDiff_le_crNorm_one ℓ _))

/-- **One-step constraint bound**: under the envelope `‖Û‖, ‖U⁺‖ ≤ R'` at the sites `j, j+1`,
`|𝒦_ℓ(X⁺)(j) - 𝒦_ℓ(X₀)(j)| ≤ (1 + 8R') ‖r‖_{1,∞,ℓ}`. -/
theorem abs_staggeredMomentum_step_le (ℓ σ : ℝ) (hℓ : ℓ ≠ 0) {R' : ℝ}
    {X₀ X₁ X₃ X' : GridState N} (h₁ : IsSourceStep σ X₀ X₁)
    (h₃ : IsSourceStep σ (transport ℓ X₁) X₃) (rlam : ZMod N → ℝ) (rU : ZMod N → Fin 4 → ℝ)
    (hlam : ∀ j, X'.lam j = X₃.lam j + rlam j) (hU : ∀ j, (X'.site j).u = (X₃.site j).u + rU j)
    (hB : ∀ j, ‖(X₃.site j).u‖ ≤ R') (hX : ∀ j, ‖(X'.site j).u‖ ≤ R') (j : ZMod N) :
    |staggeredMomentum ℓ X' j - staggeredMomentum ℓ X₀ j| ≤
      (1 + 8 * R') * crNorm 1 ℓ (resArr rU rlam) := by
  rw [staggeredMomentum_residual_increment ℓ σ hℓ h₁ h₃ rlam rU hlam hU j]
  have eJ : ∀ k, gradJ (X₃.site k).u ⬝ᵥ rU k + J (rU k) = J (X'.site k).u - J (X₃.site k).u := by
    intro k; rw [hU k, J_add_sub]
  rw [eJ j, eJ (j + 1)]
  set c := crNorm 1 ℓ (resArr rU rlam)
  have hJ : ∀ k, |J (X'.site k).u - J (X₃.site k).u| ≤ 4 * R' * c := by
    intro k
    refine (abs_J_sub_le _ _).trans ?_
    have hd : ‖(X'.site k).u - (X₃.site k).u‖ ≤ c := by
      rw [hU k, add_sub_cancel_left]; exact norm_rU_le_crNorm ℓ rU rlam k
    have hR : 0 ≤ R' := (norm_nonneg _).trans (hB k)
    have := add_le_add (hX k) (hB k)
    have hc : 0 ≤ c := crNorm_nonneg _ _ _
    calc 2 * (‖(X'.site k).u‖ + ‖(X₃.site k).u‖) * ‖(X'.site k).u - (X₃.site k).u‖
        ≤ 2 * (R' + R') * c := by gcongr
      _ = 4 * R' * c := by ring
  have hD := abs_fwdDiff_rlam_le_crNorm ℓ rU rlam j
  have hj := hJ j
  have hj1 := hJ (j + 1)
  have t1 := abs_sub ((rlam (j + 1) - rlam j) / ℓ)
    (2 * (((J (X'.site j).u - J (X₃.site j).u) +
      (J (X'.site (j + 1)).u - J (X₃.site (j + 1)).u)) / 2))
  have t2 : |2 * (((J (X'.site j).u - J (X₃.site j).u) +
      (J (X'.site (j + 1)).u - J (X₃.site (j + 1)).u)) / 2)| ≤ 8 * R' * c := by
    rw [show 2 * (((J (X'.site j).u - J (X₃.site j).u) +
      (J (X'.site (j + 1)).u - J (X₃.site (j + 1)).u)) / 2) =
      (J (X'.site j).u - J (X₃.site j).u) + (J (X'.site (j + 1)).u - J (X₃.site (j + 1)).u) by
        ring]
    exact (abs_add_le _ _).trans (by linarith)
  linarith

/-- **Accumulated staggered-constraint error** (`prop:supp-gowdy-residual-control`, last clause):
along a residual-perturbed history of symmetric splitting steps with frames in the envelope
`‖U‖_∞ ≤ R'`, for `h = ℓ ∈ (0, 2]`,
`|𝒦_ℓ(X_n)(j)| ≤ |𝒦_ℓ(X_0)(j)| + 2 (1 + 8R') √(2nh) √𝓕_h`, `𝓕_h = ℓ^{-3} Σ_{k<n} ‖r_k‖²_{2,ℓ}/(2h)`. -/
theorem staggeredMomentum_accumulated {ℓ σ R' : ℝ} (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ 2)
    (X X₁ X₃ : ℕ → GridState N) (h₁ : ∀ k, IsSourceStep σ (X k) (X₁ k))
    (h₃ : ∀ k, IsSourceStep σ (transport ℓ (X₁ k)) (X₃ k)) (rlam : ℕ → ZMod N → ℝ)
    (rU : ℕ → ZMod N → Fin 4 → ℝ)
    (hlam : ∀ k j, (X (k + 1)).lam j = (X₃ k).lam j + rlam k j)
    (hU : ∀ k j, ((X (k + 1)).site j).u = ((X₃ k).site j).u + rU k j)
    (hB : ∀ k j, ‖((X₃ k).site j).u‖ ≤ R') (hX : ∀ k j, ‖((X (k + 1)).site j).u‖ ≤ R')
    (n : ℕ) (j : ZMod N) :
    |staggeredMomentum ℓ (X n) j| ≤ |staggeredMomentum ℓ (X 0) j| +
      2 * (1 + 8 * R') * Real.sqrt (2 * n * ℓ) *
        Real.sqrt (residualFlux 1 ℓ ℓ (fun k => resArr (rU k) (rlam k)) n) := by
  have hR : 0 ≤ R' := (norm_nonneg _).trans (hB 0 0)
  have hstep : ∀ k, |staggeredMomentum ℓ (X (k + 1)) j - staggeredMomentum ℓ (X k) j| ≤
      (1 + 8 * R') * crNorm 1 ℓ (resArr (rU k) (rlam k)) := fun k =>
    abs_staggeredMomentum_step_le ℓ σ hℓ.ne' (h₁ k) (h₃ k) (rlam k) (rU k) (hlam k) (hU k)
      (hB k) (hX k) j
  have htel : staggeredMomentum ℓ (X n) j - staggeredMomentum ℓ (X 0) j =
      ∑ k ∈ range n, (staggeredMomentum ℓ (X (k + 1)) j - staggeredMomentum ℓ (X k) j) := by
    rw [Finset.sum_range_sub (fun k => staggeredMomentum ℓ (X k) j)]
  have hsum : |staggeredMomentum ℓ (X n) j - staggeredMomentum ℓ (X 0) j| ≤
      (1 + 8 * R') * ∑ k ∈ range n, crNorm 1 ℓ (resArr (rU k) (rlam k)) := by
    rw [htel, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hstep k)
  have hbud := sum_crNorm_le_sqrt_residualFlux hℓ hℓ2 1 (fun k => resArr (rU k) (rlam k)) n
  have h2 : (1 + 8 * R') * ∑ k ∈ range n, crNorm 1 ℓ (resArr (rU k) (rlam k)) ≤
      (1 + 8 * R') * (2 ^ 1 * Real.sqrt (2 * n * ℓ) *
        Real.sqrt (residualFlux 1 ℓ ℓ (fun k => resArr (rU k) (rlam k)) n)) :=
    mul_le_mul_of_nonneg_left hbud (by positivity)
  have t := abs_sub_abs_le_abs_sub (staggeredMomentum ℓ (X n) j) (staggeredMomentum ℓ (X 0) j)
  have e : (1 + 8 * R') * (2 ^ 1 * Real.sqrt (2 * n * ℓ) *
        Real.sqrt (residualFlux 1 ℓ ℓ (fun k => resArr (rU k) (rlam k)) n)) =
      2 * (1 + 8 * R') * Real.sqrt (2 * n * ℓ) *
        Real.sqrt (residualFlux 1 ℓ ℓ (fun k => resArr (rU k) (rlam k)) n) := by ring
  linarith

/-- For `0 < ℓ ≤ 1` and `r ≥ 1` the flux of order one is dominated by the flux of order `r`:
`𝓕_h^{(1)} = ℓ^{-3} 𝓔_h ≤ ℓ^{-(2r+1)} 𝓔_h = 𝓕_h^{(r)}`. -/
theorem residualFlux_one_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ℓ h : ℝ}
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hh : 0 < h) {r : ℕ} (hr : 1 ≤ r) (res : ℕ → ZMod N → E)
    (n : ℕ) : residualFlux 1 ℓ h res n ≤ residualFlux r ℓ h res n := by
  unfold residualFlux
  have hE : 0 ≤ residualEnergy ℓ h res n :=
    Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (by positivity)
  apply div_le_div_of_nonneg_left hE (by positivity)
  exact pow_le_pow_of_le_one hℓ.le hℓ1 (by omega)

/-- The accumulated constraint bound with the flux `𝓕_h = ℓ^{-(2r+1)} 𝓔_h` of any order `r ≥ 1`
(`0 < ℓ ≤ 1`). -/
theorem staggeredMomentum_accumulated_of_le {ℓ σ R' : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {r : ℕ}
    (hr : 1 ≤ r) (X X₁ X₃ : ℕ → GridState N) (h₁ : ∀ k, IsSourceStep σ (X k) (X₁ k))
    (h₃ : ∀ k, IsSourceStep σ (transport ℓ (X₁ k)) (X₃ k)) (rlam : ℕ → ZMod N → ℝ)
    (rU : ℕ → ZMod N → Fin 4 → ℝ)
    (hlam : ∀ k j, (X (k + 1)).lam j = (X₃ k).lam j + rlam k j)
    (hU : ∀ k j, ((X (k + 1)).site j).u = ((X₃ k).site j).u + rU k j)
    (hB : ∀ k j, ‖((X₃ k).site j).u‖ ≤ R') (hX : ∀ k j, ‖((X (k + 1)).site j).u‖ ≤ R')
    (n : ℕ) (j : ZMod N) :
    |staggeredMomentum ℓ (X n) j| ≤ |staggeredMomentum ℓ (X 0) j| +
      2 * (1 + 8 * R') * Real.sqrt (2 * n * ℓ) *
        Real.sqrt (residualFlux r ℓ ℓ (fun k => resArr (rU k) (rlam k)) n) := by
  have hR : 0 ≤ R' := (norm_nonneg _).trans (hB 0 0)
  have h := staggeredMomentum_accumulated hℓ (by linarith) X X₁ X₃ h₁ h₃ rlam rU hlam hU hB hX n j
  have hF := residualFlux_one_le hℓ hℓ1 hℓ hr (fun k => resArr (rU k) (rlam k)) n
  have : Real.sqrt (residualFlux 1 ℓ ℓ (fun k => resArr (rU k) (rlam k)) n) ≤
      Real.sqrt (residualFlux r ℓ ℓ (fun k => resArr (rU k) (rlam k)) n) := Real.sqrt_le_sqrt hF
  have h2 : 0 ≤ 2 * (1 + 8 * R') * Real.sqrt (2 * n * ℓ) := by positivity
  nlinarith

end

end ConstraintAccumulation

end RenewalGeometry.GowdyStaggered
