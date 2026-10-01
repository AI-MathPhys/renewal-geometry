/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.CharacteristicStrangSplittingConsistency
import RenewalGeometry.Gravity.GowdySourceFieldLipschitz

/-!
# Second-order consistency of the Gowdy symmetric splitting
  (`thm:supp-gowdy-momentum`, consistency clause; emergent-spacetime supplement)

The library encodes the Gowdy scheme of the manuscript exactly
(`GowdyStaggeredMomentumExact`): the rescaled frame `U = √t (a, b, c, d)`, the local source
flow `eq:supp-gowdy-source-flow` with its implicit-midpoint half-steps, and the
characteristic transport `eq:supp-gowdy-transport` on the periodic grid `ZMod N`.

This file proves the remaining clause of `thm:supp-gowdy-momentum`: **the
source-half / transport / source-half step with synchronized `h = ℓ` is second-order
consistent on bounded smooth reference charts with `t ≥ t₀ > 0`.**  Precisely
(`gowdy_symmetric_splitting_second_order`): for every `C³` solution of the first-order frame
system `eq:supp-gowdy-frame-system` on the slab `[t₀, t₁] × 𝕋¹` (`t₀ > 0`; functions on
`ℝ × ℝ`, `2π`-periodic in `θ`), there are `C, h₀, δ > 0` such that for every grid size `N`
with `ℓ = 2π/N ≤ h₀` and every `τ` with `[τ, τ + ℓ] ⊆ [t₀, t₁]`, the step from the grid
sampling of the solution at time `τ` exists on the near-identity branch (stage increments at
most `δ`; `step_exists`, by the Banach fixed-point theorem), and every such realisation
differs from the grid sampling at time `τ + ℓ` by at most `C ℓ³` at every site, both in the
local state `(U, P, Q, t)` and in the background `λ` (`local_error_grid`).

The proof instantiates the abstract characteristic Strang-splitting theorem
`CharacteristicSplitting.StrangSetup.local_error`:

* the projections `projPlus`, `projMinus`, `projZero` onto the right-moving
  (`w⁺`), left-moving (`w⁻`) and non-moving (`P, Q, t`) parts, and the identity
  `transport_site_toVec` showing that `transport` is the exact characteristic shift;
* the densities `g± = |w±|²` with their chart estimates;
* the bounded convex compact chart `chartK t₀ R` with the bound, the explicit Lipschitz
  constant (`localFieldVec_lipschitz_on_chart`) and a second-difference bound of the source
  field (via a smooth regularisation `regField` of `t ↦ 1/t, 1/√t` and compactness);
* the reference state `GowdyFrameSolution.Z = (√t (a,b,c,d), P, Q, t)` and the
  characteristic form of the frame system (`char_plus`, `char_minus`, `char_zero`,
  `char_lam`), derived from `eq:supp-gowdy-frame-system` by the chain rule;
* uniform derivative bounds on the slab from periodicity and compactness.
-/

open Set
open scoped BigOperators

namespace RenewalGeometry.GowdyStaggered

noncomputable section

/-! ### Coordinates of the state vector -/

theorem abs_u_le (v : StateVec) (i : Fin 4) : |v.1 i| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm v.1 i).trans (norm_fst_le v)

theorem abs_P_le (v : StateVec) : |v.2.1| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]; exact (norm_fst_le v.2).trans (norm_snd_le v)

theorem abs_Q_le (v : StateVec) : |v.2.2.1| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact (norm_fst_le v.2.2).trans ((norm_snd_le v.2).trans (norm_snd_le v))

theorem abs_t_le (v : StateVec) : |v.2.2.2| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact (norm_snd_le v.2.2).trans ((norm_snd_le v.2).trans (norm_snd_le v))

theorem norm_stateVec_le {v : StateVec} {r : ℝ} (hr : 0 ≤ r) (hu : ∀ i, |v.1 i| ≤ r)
    (hP : |v.2.1| ≤ r) (hQ : |v.2.2.1| ≤ r) (ht : |v.2.2.2| ≤ r) : ‖v‖ ≤ r := by
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩⟩
  · exact (pi_norm_le_iff_of_nonneg hr).2 fun i => by rw [Real.norm_eq_abs]; exact hu i
  · rwa [Real.norm_eq_abs]
  · rwa [Real.norm_eq_abs]
  · rwa [Real.norm_eq_abs]

/-! ### Characteristic projections -/

/-- Projection onto the right-moving characteristic part `w⁺` (as a frame). -/
def projPlus : StateVec →ₗ[ℝ] StateVec where
  toFun v := (![(v.1 0 + v.1 1) / 2, (v.1 0 + v.1 1) / 2, (v.1 2 + v.1 3) / 2,
    (v.1 2 + v.1 3) / 2], 0, 0, 0)
  map_add' x y := by
    refine Prod.ext ?_ (by simp)
    funext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by
    refine Prod.ext ?_ (by simp)
    funext i; fin_cases i <;> simp <;> ring

/-- Projection onto the left-moving characteristic part `w⁻` (as a frame). -/
def projMinus : StateVec →ₗ[ℝ] StateVec where
  toFun v := (![(v.1 0 - v.1 1) / 2, -((v.1 0 - v.1 1) / 2), (v.1 2 - v.1 3) / 2,
    -((v.1 2 - v.1 3) / 2)], 0, 0, 0)
  map_add' x y := by
    refine Prod.ext ?_ (by simp)
    funext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by
    refine Prod.ext ?_ (by simp)
    funext i; fin_cases i <;> simp <;> ring

/-- Projection onto the non-moving part `(P, Q, t)`. -/
def projZero : StateVec →ₗ[ℝ] StateVec where
  toFun v := (0, v.2.1, v.2.2.1, v.2.2.2)
  map_add' x y := Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext (by simp) (by simp)))
  map_smul' c x := Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext (by simp) (by simp)))

theorem projPlus_apply (v : StateVec) : projPlus v = (![(v.1 0 + v.1 1) / 2,
    (v.1 0 + v.1 1) / 2, (v.1 2 + v.1 3) / 2, (v.1 2 + v.1 3) / 2], 0, 0, 0) := rfl

theorem projMinus_apply (v : StateVec) : projMinus v = (![(v.1 0 - v.1 1) / 2,
    -((v.1 0 - v.1 1) / 2), (v.1 2 - v.1 3) / 2, -((v.1 2 - v.1 3) / 2)], 0, 0, 0) := rfl

theorem projZero_apply (v : StateVec) : projZero v = (0, v.2.1, v.2.2.1, v.2.2.2) := rfl

theorem proj_sum (v : StateVec) : projPlus v + projMinus v + projZero v = v := by
  rw [projPlus_apply, projMinus_apply, projZero_apply]
  refine Prod.ext ?_ (by simp)
  funext i; fin_cases i <;> simp <;> ring

theorem abs_half_add_le (v : StateVec) (i j : Fin 4) : |(v.1 i + v.1 j) / 2| ≤ ‖v‖ := by
  rw [abs_div, abs_two]
  have := abs_add_le (v.1 i) (v.1 j)
  linarith [abs_u_le v i, abs_u_le v j]

theorem abs_half_sub_le (v : StateVec) (i j : Fin 4) : |(v.1 i - v.1 j) / 2| ≤ ‖v‖ := by
  rw [abs_div, abs_two]
  have := abs_sub (v.1 i) (v.1 j)
  linarith [abs_u_le v i, abs_u_le v j]

theorem norm_projPlus_le (v : StateVec) : ‖projPlus v‖ ≤ ‖v‖ := by
  rw [projPlus_apply]
  refine norm_stateVec_le (norm_nonneg _) (fun i => ?_) (by simp) (by simp) (by simp)
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
    Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    first | exact abs_half_add_le v 0 1 | exact abs_half_add_le v 2 3

theorem norm_projMinus_le (v : StateVec) : ‖projMinus v‖ ≤ ‖v‖ := by
  rw [projMinus_apply]
  refine norm_stateVec_le (norm_nonneg _) (fun i => ?_) (by simp) (by simp) (by simp)
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
    Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, abs_neg] <;>
    first | exact abs_half_sub_le v 0 1 | exact abs_half_sub_le v 2 3

theorem norm_projZero_le (v : StateVec) : ‖projZero v‖ ≤ ‖v‖ := by
  rw [projZero_apply]
  exact norm_stateVec_le (norm_nonneg _) (fun i => by simp) (abs_P_le v) (abs_Q_le v)
    (abs_t_le v)

/-- **The transport map is the exact characteristic shift**: the transported local state at
site `j` is `Π₊ X_{j+1} + Π₋ X_{j-1} + Π₀ X_j`. -/
theorem transport_site_toVec {N : ℕ} (ℓ : ℝ) (X : GridState N) (j : ZMod N) :
    ((transport ℓ X).site j).toVec = projPlus (X.site (j + 1)).toVec +
      projMinus (X.site (j - 1)).toVec + projZero (X.site j).toVec := by
  have h2 : invSqrt2 ^ 2 = 1 / 2 := by rw [sq]; exact invSqrt2_sq
  rw [projPlus_apply, projMinus_apply, projZero_apply]
  simp only [transport, LocalState.toVec]
  refine Prod.ext ?_ (by simp)
  funext i
  fin_cases i <;> simp [recombine, wPlus, wMinus] <;> ring_nf <;> (try simp only [h2]) <;> ring

/-! ### The characteristic densities `g± = |w±|²` -/

theorem gPlus_eq (u : Fin 4 → ℝ) : gPlus u = ((u 0 + u 1) ^ 2 + (u 2 + u 3) ^ 2) / 2 := by
  have h2 := invSqrt2_sq
  simp only [gPlus, wPlus, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination ((u 0 + u 1) ^ 2 + (u 2 + u 3) ^ 2) * h2

theorem gMinus_eq (u : Fin 4 → ℝ) : gMinus u = ((u 0 - u 1) ^ 2 + (u 2 - u 3) ^ 2) / 2 := by
  have h2 := invSqrt2_sq
  simp only [gMinus, wMinus, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination ((u 0 - u 1) ^ 2 + (u 2 - u 3) ^ 2) * h2

/-- The right-moving density as a function of the local state. -/
def densPlus (v : StateVec) : ℝ := gPlus v.1

/-- The left-moving density as a function of the local state. -/
def densMinus (v : StateVec) : ℝ := gMinus v.1

theorem abs_projPlus_ge (v : StateVec) :
    |v.1 0 + v.1 1| / 2 ≤ ‖projPlus v‖ ∧ |v.1 2 + v.1 3| / 2 ≤ ‖projPlus v‖ := by
  have e0 : (projPlus v).1 0 = (v.1 0 + v.1 1) / 2 := by simp [projPlus_apply]
  have e2 : (projPlus v).1 2 = (v.1 2 + v.1 3) / 2 := by simp [projPlus_apply]
  have h0 := abs_u_le (projPlus v) 0
  have h2 := abs_u_le (projPlus v) 2
  rw [e0, abs_div, abs_two] at h0
  rw [e2, abs_div, abs_two] at h2
  exact ⟨h0, h2⟩

theorem abs_projMinus_ge (v : StateVec) :
    |v.1 0 - v.1 1| / 2 ≤ ‖projMinus v‖ ∧ |v.1 2 - v.1 3| / 2 ≤ ‖projMinus v‖ := by
  have e0 : (projMinus v).1 0 = (v.1 0 - v.1 1) / 2 := by simp [projMinus_apply]
  have e2 : (projMinus v).1 2 = (v.1 2 - v.1 3) / 2 := by simp [projMinus_apply]
  have h0 := abs_u_le (projMinus v) 0
  have h2 := abs_u_le (projMinus v) 2
  rw [e0, abs_div, abs_two] at h0
  rw [e2, abs_div, abs_two] at h2
  exact ⟨h0, h2⟩

/-- Lipschitz bound of a two-term quadratic density. -/
theorem abs_quad_sub_le {α β α' β' R N : ℝ} (hα : |α - α'| ≤ 2 * N) (hβ : |β - β'| ≤ 2 * N)
    (hA : |α + α'| ≤ 4 * R) (hB : |β + β'| ≤ 4 * R) :
    |(α ^ 2 + β ^ 2) / 2 - (α' ^ 2 + β' ^ 2) / 2| ≤ 8 * R * N := by
  have e : (α ^ 2 + β ^ 2) / 2 - (α' ^ 2 + β' ^ 2) / 2 =
      ((α - α') * (α + α') + (β - β') * (β + β')) / 2 := by ring
  rw [e, abs_div, abs_two]
  have h1 : |(α - α') * (α + α')| ≤ 2 * N * (4 * R) := by
    rw [abs_mul]; exact mul_le_mul hα hA (abs_nonneg _) (by linarith [abs_nonneg (α - α')])
  have h2 : |(β - β') * (β + β')| ≤ 2 * N * (4 * R) := by
    rw [abs_mul]; exact mul_le_mul hβ hB (abs_nonneg _) (by linarith [abs_nonneg (β - β')])
  have := abs_add_le ((α - α') * (α + α')) ((β - β') * (β + β'))
  linarith

theorem abs_sum_four_le {x y : StateVec} {R : ℝ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (i j : Fin 4)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    |x.1 i + s * x.1 j + (y.1 i + s * y.1 j)| ≤ 4 * R := by
  have hs' : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have a1 := abs_u_le x i; have a2 := abs_u_le x j
  have a3 := abs_u_le y i; have a4 := abs_u_le y j
  have b1 : |s * x.1 j| ≤ R := by rw [abs_mul, hs']; linarith
  have b2 : |s * y.1 j| ≤ R := by rw [abs_mul, hs']; linarith
  have c1 := abs_add_le (x.1 i) (s * x.1 j)
  have c2 := abs_add_le (y.1 i) (s * y.1 j)
  have c3 := abs_add_le (x.1 i + s * x.1 j) (y.1 i + s * y.1 j)
  linarith

theorem densPlus_lip {x y : StateVec} {R : ℝ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |densPlus x - densPlus y| ≤ 8 * R * ‖projPlus (x - y)‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  obtain ⟨h1, h2⟩ := abs_projPlus_ge (x - y)
  simp only [Prod.fst_sub, Pi.sub_apply] at h1 h2
  unfold densPlus
  rw [gPlus_eq, gPlus_eq]
  apply abs_quad_sub_le
  · rw [show x.1 0 + x.1 1 - (y.1 0 + y.1 1) = x.1 0 - y.1 0 + (x.1 1 - y.1 1) by ring]
    linarith
  · rw [show x.1 2 + x.1 3 - (y.1 2 + y.1 3) = x.1 2 - y.1 2 + (x.1 3 - y.1 3) by ring]
    linarith
  · simpa using abs_sum_four_le hx hy 0 1 1 (Or.inl rfl)
  · simpa using abs_sum_four_le hx hy 2 3 1 (Or.inl rfl)

theorem densMinus_lip {x y : StateVec} {R : ℝ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |densMinus x - densMinus y| ≤ 8 * R * ‖projMinus (x - y)‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  obtain ⟨h1, h2⟩ := abs_projMinus_ge (x - y)
  simp only [Prod.fst_sub, Pi.sub_apply] at h1 h2
  unfold densMinus
  rw [gMinus_eq, gMinus_eq]
  apply abs_quad_sub_le
  · rw [show x.1 0 - x.1 1 - (y.1 0 - y.1 1) = x.1 0 - y.1 0 - (x.1 1 - y.1 1) by ring]
    linarith
  · rw [show x.1 2 - x.1 3 - (y.1 2 - y.1 3) = x.1 2 - y.1 2 - (x.1 3 - y.1 3) by ring]
    linarith
  · have := abs_sum_four_le hx hy 0 1 (-1) (Or.inr rfl)
    rw [show x.1 0 - x.1 1 + (y.1 0 - y.1 1) = x.1 0 + -1 * x.1 1 + (y.1 0 + -1 * y.1 1) by
      ring]
    exact this
  · have := abs_sum_four_le hx hy 2 3 (-1) (Or.inr rfl)
    rw [show x.1 2 - x.1 3 + (y.1 2 - y.1 3) = x.1 2 + -1 * x.1 3 + (y.1 2 + -1 * y.1 3) by
      ring]
    exact this

theorem densPlus_symm (x y : StateVec) :
    |densPlus x + densPlus y - 2 * densPlus ((1 / 2 : ℝ) • (x + y))| ≤ 2 * ‖x - y‖ ^ 2 := by
  have e : densPlus x + densPlus y - 2 * densPlus ((1 / 2 : ℝ) • (x + y)) =
      ((x.1 0 - y.1 0 + (x.1 1 - y.1 1)) ^ 2 + (x.1 2 - y.1 2 + (x.1 3 - y.1 3)) ^ 2) / 4 := by
    unfold densPlus; rw [gPlus_eq, gPlus_eq, gPlus_eq]; simp; ring
  rw [e, abs_of_nonneg (by positivity)]
  have a0 := abs_u_le (x - y) 0; have a1 := abs_u_le (x - y) 1
  have a2 := abs_u_le (x - y) 2; have a3 := abs_u_le (x - y) 3
  simp only [Prod.fst_sub, Pi.sub_apply] at a0 a1 a2 a3
  have b1 : (x.1 0 - y.1 0 + (x.1 1 - y.1 1)) ^ 2 ≤ (2 * ‖x - y‖) ^ 2 := by
    apply sq_le_sq'
    · linarith [neg_abs_le (x.1 0 - y.1 0), neg_abs_le (x.1 1 - y.1 1)]
    · linarith [le_abs_self (x.1 0 - y.1 0), le_abs_self (x.1 1 - y.1 1)]
  have b2 : (x.1 2 - y.1 2 + (x.1 3 - y.1 3)) ^ 2 ≤ (2 * ‖x - y‖) ^ 2 := by
    apply sq_le_sq'
    · linarith [neg_abs_le (x.1 2 - y.1 2), neg_abs_le (x.1 3 - y.1 3)]
    · linarith [le_abs_self (x.1 2 - y.1 2), le_abs_self (x.1 3 - y.1 3)]
  nlinarith

theorem densMinus_symm (x y : StateVec) :
    |densMinus x + densMinus y - 2 * densMinus ((1 / 2 : ℝ) • (x + y))| ≤ 2 * ‖x - y‖ ^ 2 := by
  have e : densMinus x + densMinus y - 2 * densMinus ((1 / 2 : ℝ) • (x + y)) =
      ((x.1 0 - y.1 0 - (x.1 1 - y.1 1)) ^ 2 + (x.1 2 - y.1 2 - (x.1 3 - y.1 3)) ^ 2) / 4 := by
    unfold densMinus; rw [gMinus_eq, gMinus_eq, gMinus_eq]; simp; ring
  rw [e, abs_of_nonneg (by positivity)]
  have a0 := abs_u_le (x - y) 0; have a1 := abs_u_le (x - y) 1
  have a2 := abs_u_le (x - y) 2; have a3 := abs_u_le (x - y) 3
  simp only [Prod.fst_sub, Pi.sub_apply] at a0 a1 a2 a3
  have b1 : (x.1 0 - y.1 0 - (x.1 1 - y.1 1)) ^ 2 ≤ (2 * ‖x - y‖) ^ 2 := by
    apply sq_le_sq'
    · linarith [neg_abs_le (x.1 0 - y.1 0), le_abs_self (x.1 1 - y.1 1)]
    · linarith [le_abs_self (x.1 0 - y.1 0), neg_abs_le (x.1 1 - y.1 1)]
  have b2 : (x.1 2 - y.1 2 - (x.1 3 - y.1 3)) ^ 2 ≤ (2 * ‖x - y‖) ^ 2 := by
    apply sq_le_sq'
    · linarith [neg_abs_le (x.1 2 - y.1 2), le_abs_self (x.1 3 - y.1 3)]
    · linarith [le_abs_self (x.1 2 - y.1 2), neg_abs_le (x.1 3 - y.1 3)]
  nlinarith

/-! ### A smooth regularisation of the source field away from `t = 0` -/

/-- A smooth clock equal to `t` for `t ≥ t₀/2` and bounded below by `t₀/4`. -/
def regClock (t₀ t : ℝ) : ℝ :=
  t₀ / 4 + (t - t₀ / 4) * Real.smoothTransition ((t - t₀ / 4) / (t₀ / 4))

theorem regClock_eq {t₀ t : ℝ} (h0 : 0 < t₀) (ht : t₀ / 2 ≤ t) : regClock t₀ t = t := by
  unfold regClock
  rw [Real.smoothTransition.one_of_one_le, mul_one]
  · ring
  · rw [le_div_iff₀ (by linarith)]; linarith

theorem regClock_ge {t₀ : ℝ} (h0 : 0 < t₀) (t : ℝ) : t₀ / 4 ≤ regClock t₀ t := by
  unfold regClock
  rcases le_or_gt t (t₀ / 4) with h | h
  · rw [Real.smoothTransition.zero_of_nonpos]
    · simp
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  · have := Real.smoothTransition.nonneg ((t - t₀ / 4) / (t₀ / 4))
    nlinarith

theorem regClock_pos {t₀ : ℝ} (h0 : 0 < t₀) (t : ℝ) : 0 < regClock t₀ t :=
  lt_of_lt_of_le (by linarith) (regClock_ge h0 t)

theorem contDiff_regClock (t₀ : ℝ) : ContDiff ℝ 3 (regClock t₀) := by
  unfold regClock
  have hs : ContDiff ℝ 3 Real.smoothTransition := Real.smoothTransition.contDiff
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (hs.comp ((contDiff_id.sub contDiff_const).div_const _)))

/-- The source field with `t` replaced by the regularised clock in the coefficients. -/
def regField (t₀ : ℝ) (v : StateVec) : StateVec :=
  (sourceField (regClock t₀ v.2.2.2) v.1, v.1 0 / Real.sqrt (regClock t₀ v.2.2.2),
    Real.exp (-v.2.1) * v.1 2 / Real.sqrt (regClock t₀ v.2.2.2), 1)

theorem regField_eq {t₀ : ℝ} (h0 : 0 < t₀) {v : StateVec} (hv : t₀ / 2 ≤ v.2.2.2) :
    regField t₀ v = localFieldVec v := by
  rw [localFieldVec_eq, regField, regClock_eq h0 hv]

theorem contDiff_regField {t₀ : ℝ} (h0 : 0 < t₀) : ContDiff ℝ 2 (regField t₀) := by
  have hT : ContDiff ℝ 2 (fun v : StateVec => regClock t₀ v.2.2.2) :=
    ((contDiff_regClock t₀).of_le (by norm_num)).comp
      (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
  have hTne : ∀ v : StateVec, regClock t₀ v.2.2.2 ≠ 0 := fun v => (regClock_pos h0 _).ne'
  have hS : ContDiff ℝ 2 (fun v : StateVec => Real.sqrt (regClock t₀ v.2.2.2)) :=
    hT.sqrt hTne
  have hSne : ∀ v : StateVec, Real.sqrt (regClock t₀ v.2.2.2) ≠ 0 :=
    fun v => (Real.sqrt_pos.mpr (regClock_pos h0 _)).ne'
  have h2T : ContDiff ℝ 2 (fun v : StateVec => 2 * regClock t₀ v.2.2.2) := contDiff_const.mul hT
  have h2Tne : ∀ v : StateVec, 2 * regClock t₀ v.2.2.2 ≠ 0 :=
    fun v => mul_ne_zero two_ne_zero (hTne v)
  have hu : ∀ i : Fin 4, ContDiff ℝ 2 (fun v : StateVec => v.1 i) :=
    fun i => (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hP : ContDiff ℝ 2 (fun v : StateVec => v.2.1) := contDiff_fst.comp contDiff_snd
  unfold regField
  refine ContDiff.prodMk ?_ (ContDiff.prodMk ?_ (ContDiff.prodMk ?_ contDiff_const))
  · refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · simp only [sourceField, Fin.zero_eta, Matrix.cons_val_zero]
      exact (((hu 0).neg).div h2T h2Tne).add
        ((((hu 2).pow 2).sub ((hu 3).pow 2)).div hS hSne)
    · simp only [sourceField, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact (hu 1).div h2T h2Tne
    · simp only [sourceField]
      simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      exact (((hu 2).neg).div h2T h2Tne).add
        (((((hu 0).neg).mul (hu 2)).add ((hu 1).mul (hu 3))).div hS hSne)
    · simp only [sourceField]
      simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      exact ((hu 3).div h2T h2Tne).add
        ((((hu 0).mul (hu 3)).sub ((hu 1).mul (hu 2))).div hS hSne)
  · exact (hu 0).div hS hSne
  · exact ((Real.contDiff_exp.comp hP.neg).mul (hu 2)).div hS hSne

/-! ### The compact convex chart -/

/-- The bounded chart `{‖v‖ ≤ R, t ≥ t₀/2}` of the local state space. -/
def chartK (t₀ R : ℝ) : Set StateVec := {v | ‖v‖ ≤ R ∧ t₀ / 2 ≤ v.2.2.2}

theorem chartK_eq (t₀ R : ℝ) :
    chartK t₀ R = Metric.closedBall 0 R ∩ {v : StateVec | t₀ / 2 ≤ v.2.2.2} := by
  ext v; simp [chartK]

theorem isCompact_chartK (t₀ R : ℝ) : IsCompact (chartK t₀ R) := by
  rw [chartK_eq]
  exact (isCompact_closedBall 0 R).inter_right
    (isClosed_le continuous_const (continuous_snd.comp (continuous_snd.comp continuous_snd)))

theorem convex_chartK (t₀ R : ℝ) : Convex ℝ (chartK t₀ R) := by
  rw [chartK_eq]
  refine (convex_closedBall 0 R).inter ?_
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hx hy ⊢
  have e : t₀ / 2 = a * (t₀ / 2) + b * (t₀ / 2) := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_nonneg ha (sub_nonneg.2 hx), mul_nonneg hb (sub_nonneg.2 hy)]

theorem chartK_subset_gowdyChart {t₀ R : ℝ} {v : StateVec} (hv : v ∈ chartK t₀ R) :
    v ∈ gowdyChart (t₀ / 2) R :=
  ⟨hv.2, fun i => (abs_u_le v i).trans hv.1, (abs_P_le v).trans hv.1⟩

theorem exists_field_bound {t₀ : ℝ} (h0 : 0 < t₀) (R : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ v ∈ chartK t₀ R, ‖localFieldVec v‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_chartK t₀ R).exists_bound_of_continuousOn
    (contDiff_regField h0).continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun v hv => ?_⟩
  rw [← regField_eq h0 hv.2]
  exact (hC v hv).trans (le_max_left _ _)

theorem exists_field_symm {t₀ : ℝ} (h0 : 0 < t₀) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ chartK t₀ R, ∀ y ∈ chartK t₀ R,
      ‖localFieldVec x + localFieldVec y - (2 : ℝ) • localFieldVec ((1 / 2 : ℝ) • (x + y))‖ ≤
        M * ‖x - y‖ ^ 2 := by
  have hG := contDiff_regField h0
  obtain ⟨C, hC⟩ := (isCompact_chartK t₀ R).exists_bound_of_continuousOn
    (hG.continuous_iteratedFDeriv (m := 2) le_rfl).continuousOn
  refine ⟨max C 0 / 4, by positivity, fun x hx y hy => ?_⟩
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • (y - x) ∈ chartK t₀ R := by
    intro s hs
    have := convex_chartK t₀ R hx hy (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s) hs.1
      (by ring)
    convert this using 1
    module
  have hψ : ContDiff ℝ 2 (fun s : ℝ => regField t₀ (x + s • (y - x))) :=
    VectorLineTaylor.contDiff_lineMap hG x (y - x)
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv 2 (fun s : ℝ => regField t₀ (x + s • (y - x))) s‖ ≤
        max C 0 * ‖y - x‖ ^ 2 := by
    intro s hs
    have := VectorLineTaylor.norm_iteratedDeriv_lineMap_le (n := 2) hG x (y - x)
      (k := 2) le_rfl s
    refine this.trans ?_
    gcongr
    exact (hC _ (hseg s hs)).trans (le_max_left _ _)
  have := CharacteristicSplitting.norm_symm_le _ hψ zero_le_one hbound
  have e1 : x + (1 / 2 : ℝ) • (y - x) = (1 / 2 : ℝ) • (x + y) := by module
  simp only [zero_smul, add_zero, one_smul, add_sub_cancel, e1] at this
  have hmid : (1 / 2 : ℝ) • (x + y) ∈ chartK t₀ R := by
    have := hseg (1 / 2) ⟨by norm_num, by norm_num⟩
    rwa [e1] at this
  rw [regField_eq h0 hx.2, regField_eq h0 hy.2, regField_eq h0 hmid.2] at this
  calc _ ≤ max C 0 * ‖y - x‖ ^ 2 * 1 ^ 2 / 4 := this
    _ = max C 0 / 4 * ‖x - y‖ ^ 2 := by rw [norm_sub_rev]; ring

/-! ### The frame system and its reference solution -/

/-- `∂_t f` at `p = (t, θ)`. -/
def dT (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ f p (1, 0)

/-- `∂_θ f` at `p = (t, θ)`. -/
def dΘ (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ f p (0, 1)

/-- A `C³` solution of the first-order Gowdy frame system `eq:supp-gowdy-frame-system` on
the slab `[t₀, t₁] × 𝕋¹`: the fields `a = P_t, b = P_θ, c = e^P Q_t, d = e^P Q_θ, P, Q, λ`
are functions of `(t, θ) ∈ ℝ × ℝ`, `2π`-periodic in `θ`, and satisfy

`a_t = b_θ - a/t + c² - d²`, `b_t = a_θ`, `c_t = d_θ - c/t - ac + bd`, `d_t = c_θ + ad - bc`,
`P_t = a`, `Q_t = e^{-P} c`, `λ_t = 2 t e` with `e = (a² + b² + c² + d²)/2`

for `t ∈ [t₀, t₁]`.  (The coordinate constraints `eq:supp-gowdy-coordinate-constraints`
are not needed for the evolution and are not assumed.) -/
structure GowdyFrameSolution (t₀ t₁ : ℝ) where
  a : ℝ × ℝ → ℝ
  b : ℝ × ℝ → ℝ
  c : ℝ × ℝ → ℝ
  d : ℝ × ℝ → ℝ
  P : ℝ × ℝ → ℝ
  Q : ℝ × ℝ → ℝ
  lam : ℝ × ℝ → ℝ
  smooth_a : ContDiff ℝ 3 a
  smooth_b : ContDiff ℝ 3 b
  smooth_c : ContDiff ℝ 3 c
  smooth_d : ContDiff ℝ 3 d
  smooth_P : ContDiff ℝ 3 P
  smooth_Q : ContDiff ℝ 3 Q
  smooth_lam : ContDiff ℝ 3 lam
  periodic_a : ∀ p : ℝ × ℝ, a (p.1, p.2 + 2 * Real.pi) = a p
  periodic_b : ∀ p : ℝ × ℝ, b (p.1, p.2 + 2 * Real.pi) = b p
  periodic_c : ∀ p : ℝ × ℝ, c (p.1, p.2 + 2 * Real.pi) = c p
  periodic_d : ∀ p : ℝ × ℝ, d (p.1, p.2 + 2 * Real.pi) = d p
  periodic_P : ∀ p : ℝ × ℝ, P (p.1, p.2 + 2 * Real.pi) = P p
  periodic_Q : ∀ p : ℝ × ℝ, Q (p.1, p.2 + 2 * Real.pi) = Q p
  periodic_lam : ∀ p : ℝ × ℝ, lam (p.1, p.2 + 2 * Real.pi) = lam p
  eq_a : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ →
    dT a p = dΘ b p - a p / p.1 + c p ^ 2 - d p ^ 2
  eq_b : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → dT b p = dΘ a p
  eq_c : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ →
    dT c p = dΘ d p - c p / p.1 - a p * c p + b p * d p
  eq_d : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → dT d p = dΘ c p + a p * d p - b p * c p
  eq_P : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → dT P p = a p
  eq_Q : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → dT Q p = Real.exp (-P p) * c p
  eq_lam : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ →
    dT lam p = 2 * p.1 * ((a p ^ 2 + b p ^ 2 + c p ^ 2 + d p ^ 2) / 2)

namespace GowdyFrameSolution

variable {t₀ t₁ : ℝ} (sol : GowdyFrameSolution t₀ t₁)

/-- The frame fields `(a, b, c, d)`. -/
def fr : Fin 4 → ℝ × ℝ → ℝ := ![sol.a, sol.b, sol.c, sol.d]

theorem smooth_fr (i : Fin 4) : ContDiff ℝ 3 (sol.fr i) := by
  fin_cases i
  · exact sol.smooth_a
  · exact sol.smooth_b
  · exact sol.smooth_c
  · exact sol.smooth_d

theorem periodic_fr (i : Fin 4) (p : ℝ × ℝ) :
    sol.fr i (p.1, p.2 + 2 * Real.pi) = sol.fr i p := by
  fin_cases i
  · exact sol.periodic_a p
  · exact sol.periodic_b p
  · exact sol.periodic_c p
  · exact sol.periodic_d p

/-- The reference local state `(U, P, Q, t)` with `U = √t (a, b, c, d)`
(`eq:supp-gowdy-rescaled-frame`); the clock is regularised below `t₀/2` so that the state is
globally `C³`, and agrees with `√t` on the slab. -/
def Z (p : ℝ × ℝ) : StateVec :=
  (fun i => Real.sqrt (regClock t₀ p.1) * sol.fr i p, sol.P p, sol.Q p, p.1)

theorem Z_eq (h0 : 0 < t₀) {p : ℝ × ℝ} (hp : t₀ / 2 ≤ p.1) :
    sol.Z p = (fun i => Real.sqrt p.1 * sol.fr i p, sol.P p, sol.Q p, p.1) := by
  simp [Z, regClock_eq h0 hp]

theorem contDiff_Z (h0 : 0 < t₀) : ContDiff ℝ 3 sol.Z := by
  have hs : ContDiff ℝ 3 (fun p : ℝ × ℝ => Real.sqrt (regClock t₀ p.1)) :=
    ((contDiff_regClock t₀).comp contDiff_fst).sqrt fun p => (regClock_pos h0 _).ne'
  refine ContDiff.prodMk ?_ (sol.smooth_P.prodMk (sol.smooth_Q.prodMk contDiff_fst))
  exact contDiff_pi.2 fun i => hs.mul (sol.smooth_fr i)

theorem periodic_Z (p : ℝ × ℝ) : sol.Z (p.1, p.2 + 2 * Real.pi) = sol.Z p := by
  simp only [Z, sol.periodic_fr, sol.periodic_P, sol.periodic_Q]

/-- The derivative of the reference state at a point with `t > t₀/2`. -/
def ZDeriv (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] StateVec :=
  (ContinuousLinearMap.pi fun i => Real.sqrt p.1 • fderiv ℝ (sol.fr i) p +
      (sol.fr i p * (1 / (2 * Real.sqrt p.1))) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((fderiv ℝ sol.P p).prod ((fderiv ℝ sol.Q p).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)))

theorem hasFDerivAt_Z (h0 : 0 < t₀) {p : ℝ × ℝ} (hp : t₀ / 2 < p.1) :
    HasFDerivAt sol.Z (sol.ZDeriv p) p := by
  have hp0 : 0 < p.1 := by linarith
  -- the regularised square root
  have hsq1 : HasDerivAt (fun t => Real.sqrt (regClock t₀ t)) (1 / (2 * Real.sqrt p.1)) p.1 := by
    refine (Real.hasDerivAt_sqrt hp0.ne').congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hp] with t ht
    rw [regClock_eq h0 (le_of_lt ht)]
  have hsq : HasFDerivAt (fun q : ℝ × ℝ => Real.sqrt (regClock t₀ q.1))
      ((1 / (2 * Real.sqrt p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hsq1.comp_hasFDerivAt p (hasFDerivAt_fst)
  have hsqp : Real.sqrt (regClock t₀ p.1) = Real.sqrt p.1 := by
    rw [regClock_eq h0 hp.le]
  have hcomp : ∀ i, HasFDerivAt (fun q : ℝ × ℝ => Real.sqrt (regClock t₀ q.1) * sol.fr i q)
      (Real.sqrt p.1 • fderiv ℝ (sol.fr i) p +
        (sol.fr i p * (1 / (2 * Real.sqrt p.1))) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    intro i
    have hf : HasFDerivAt (sol.fr i) (fderiv ℝ (sol.fr i) p) p :=
      ((sol.smooth_fr i).differentiable (by norm_num) p).hasFDerivAt
    refine (hsq.mul hf).congr_fderiv ?_
    rw [hsqp, smul_smul]
  refine HasFDerivAt.prodMk ?_ (HasFDerivAt.prodMk ?_ (HasFDerivAt.prodMk ?_ hasFDerivAt_fst))
  · exact hasFDerivAt_pi.2 hcomp
  · exact (sol.smooth_P.differentiable (by norm_num) p).hasFDerivAt
  · exact (sol.smooth_Q.differentiable (by norm_num) p).hasFDerivAt

theorem fderiv_Z_apply (h0 : 0 < t₀) {p : ℝ × ℝ} (hp : t₀ / 2 < p.1) (w : ℝ × ℝ) :
    fderiv ℝ sol.Z p w =
      (fun i => Real.sqrt p.1 * fderiv ℝ (sol.fr i) p w +
          sol.fr i p * (1 / (2 * Real.sqrt p.1)) * w.1,
        fderiv ℝ sol.P p w, fderiv ℝ sol.Q p w, w.1) := by
  rw [(sol.hasFDerivAt_Z h0 hp).fderiv]
  simp [ZDeriv, mul_assoc]

theorem fderiv_apply_plus (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    fderiv ℝ f p (1, -1) = dT f p - dΘ f p := by
  rw [show ((1 : ℝ), (-1 : ℝ)) = ((1 : ℝ), (0 : ℝ)) - ((0 : ℝ), (1 : ℝ)) by simp, map_sub]
  rfl

theorem fderiv_apply_minus (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    fderiv ℝ f p (1, 1) = dT f p + dΘ f p := by
  rw [show ((1 : ℝ), (1 : ℝ)) = ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) by simp, map_add]
  rfl

/-- Characteristic form of the frame system, right-moving part:
`Π₊ (∂_t - ∂_θ) Z = Π₊ F(Z)`. -/
theorem char_plus (h0 : 0 < t₀) {p : ℝ × ℝ} (hp : p.1 ∈ Icc t₀ t₁) :
    projPlus (fderiv ℝ sol.Z p (1, -1)) = projPlus (localFieldVec (sol.Z p)) := by
  have hp2 : t₀ / 2 < p.1 := by linarith [hp.1]
  have hpos : 0 < p.1 := by linarith [hp.1]
  rw [sol.fderiv_Z_apply h0 hp2, sol.Z_eq h0 hp2.le, localFieldVec_eq, projPlus_apply,
    projPlus_apply]
  have ha := sol.eq_a p hp
  have hb := sol.eq_b p hp
  have hc := sol.eq_c p hp
  have hd := sol.eq_d p hp
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.mpr hpos
  have hss : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hpos.le
  refine Prod.ext ?_ (by simp)
  funext i
  fin_cases i <;>
  · simp [fr, sourceField, fderiv_apply_plus]
    try simp only [ha, hb, hc, hd]
    generalize p.1 = t at hpos ⊢
    obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
      ⟨Real.sqrt t, Real.sqrt_pos.2 hpos, (Real.sq_sqrt hpos.le).symm⟩
    rw [Real.sqrt_sq hs.le]
    field_simp
    ring

/-- Characteristic form of the frame system, left-moving part:
`Π₋ (∂_t + ∂_θ) Z = Π₋ F(Z)`. -/
theorem char_minus (h0 : 0 < t₀) {p : ℝ × ℝ} (hp : p.1 ∈ Icc t₀ t₁) :
    projMinus (fderiv ℝ sol.Z p (1, 1)) = projMinus (localFieldVec (sol.Z p)) := by
  have hp2 : t₀ / 2 < p.1 := by linarith [hp.1]
  have hpos : 0 < p.1 := by linarith [hp.1]
  rw [sol.fderiv_Z_apply h0 hp2, sol.Z_eq h0 hp2.le, localFieldVec_eq, projMinus_apply,
    projMinus_apply]
  have ha := sol.eq_a p hp
  have hb := sol.eq_b p hp
  have hc := sol.eq_c p hp
  have hd := sol.eq_d p hp
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.mpr hpos
  have hss : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hpos.le
  refine Prod.ext ?_ (by simp)
  funext i
  fin_cases i <;>
  · simp [fr, sourceField, fderiv_apply_minus]
    try simp only [ha, hb, hc, hd]
    generalize p.1 = t at hpos ⊢
    obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
      ⟨Real.sqrt t, Real.sqrt_pos.2 hpos, (Real.sq_sqrt hpos.le).symm⟩
    rw [Real.sqrt_sq hs.le]
    field_simp
    ring

/-- Characteristic form of the frame system, non-moving part:
`Π₀ ∂_t Z = Π₀ F(Z)` (`P_t = a`, `Q_t = e^{-P} c`, `t_t = 1`). -/
theorem char_zero (h0 : 0 < t₀) {p : ℝ × ℝ} (hp : p.1 ∈ Icc t₀ t₁) :
    projZero (fderiv ℝ sol.Z p (1, 0)) = projZero (localFieldVec (sol.Z p)) := by
  have hp2 : t₀ / 2 < p.1 := by linarith [hp.1]
  have hpos : 0 < p.1 := by linarith [hp.1]
  rw [sol.fderiv_Z_apply h0 hp2, sol.Z_eq h0 hp2.le, localFieldVec_eq, projZero_apply,
    projZero_apply]
  have hP : fderiv ℝ sol.P p (1, 0) = sol.a p := sol.eq_P p hp
  have hQ : fderiv ℝ sol.Q p (1, 0) = Real.exp (-sol.P p) * sol.c p := sol.eq_Q p hp
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.mpr hpos
  simp only [hP, hQ, fr]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp; field_simp
  · simp; field_simp

/-- The background equation in characteristic form: `λ_t = g₊(Z) + g₋(Z)`. -/
theorem char_lam (h0 : 0 < t₀) {p : ℝ × ℝ} (hp : p.1 ∈ Icc t₀ t₁) :
    fderiv ℝ sol.lam p (1, 0) = densPlus (sol.Z p) + densMinus (sol.Z p) := by
  have hp2 : t₀ / 2 < p.1 := by linarith [hp.1]
  have hpos : 0 < p.1 := by linarith [hp.1]
  have hl : fderiv ℝ sol.lam p (1, 0) = _ := sol.eq_lam p hp
  rw [hl, sol.Z_eq h0 hp2.le, densPlus, densMinus, gPlus_eq, gMinus_eq]
  have hss : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hpos.le
  simp only [fr, Matrix.cons_val_zero, Matrix.cons_val_one]
  try simp only [Matrix.cons_val, Fin.reduceFinMk, Fin.isValue]
  linear_combination (-(sol.a p ^ 2 + sol.b p ^ 2 + sol.c p ^ 2 + sol.d p ^ 2)) * hss

end GowdyFrameSolution

/-! ### Uniform bounds on the slab from periodicity -/

/-- A continuous function on `ℝ × ℝ`, `2π`-periodic in the second variable, is bounded on
every slab `[t₀, t₁] × ℝ`. -/
theorem exists_bound_of_periodic {E : Type*} [NormedAddCommGroup E] (f : ℝ × ℝ → E)
    (hf : Continuous f) (hper : ∀ p : ℝ × ℝ, f (p.1, p.2 + 2 * Real.pi) = f p) (t₀ t₁ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ‖f p‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := t₀) (b := t₁)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun p hp => ?_⟩
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  have hθ : toIcoMod hT 0 p.2 + toIcoDiv hT 0 p.2 • (2 * Real.pi) = p.2 :=
    toIcoMod_add_toIcoDiv_zsmul hT 0 p.2
  have hmem : toIcoMod hT 0 p.2 ∈ Ico 0 (0 + 2 * Real.pi) := toIcoMod_mem_Ico hT 0 p.2
  have hperf : Function.Periodic (fun θ => f (p.1, θ)) (2 * Real.pi) := fun θ => hper (p.1, θ)
  have heq : f p = f (p.1, toIcoMod hT 0 p.2) := by
    have := (hperf.zsmul (toIcoDiv hT 0 p.2)) (toIcoMod hT 0 p.2)
    try dsimp only at this
    rw [hθ] at this
    exact this
  rw [heq]
  have hm2 : toIcoMod hT 0 p.2 ≤ 2 * Real.pi := by linarith [hmem.2]
  exact (hC (p.1, toIcoMod hT 0 p.2) ⟨hp, ⟨hmem.1, hm2⟩⟩).trans (le_max_left _ _)

theorem iteratedFDeriv_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (hper : ∀ p : ℝ × ℝ, f (p.1, p.2 + 2 * Real.pi) = f p) (k : ℕ)
    (p : ℝ × ℝ) :
    iteratedFDeriv ℝ k f (p.1, p.2 + 2 * Real.pi) = iteratedFDeriv ℝ k f p := by
  have hfun : (fun q : ℝ × ℝ => f (q + ((0 : ℝ), 2 * Real.pi))) = f := by
    funext q
    rw [← hper q]
    congr 1
    ext <;> simp
  have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) k ((0 : ℝ), 2 * Real.pi) p
  rw [hfun] at this
  rw [show ((p.1, p.2 + 2 * Real.pi) : ℝ × ℝ) = p + ((0 : ℝ), 2 * Real.pi) by
    ext <;> simp]
  exact this.symm

theorem exists_iteratedFDeriv_bound_of_periodic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ × ℝ → E) (hf : ContDiff ℝ 3 f)
    (hper : ∀ p : ℝ × ℝ, f (p.1, p.2 + 2 * Real.pi) = f p) {k : ℕ} (hk : k ≤ 3)
    (t₀ t₁ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ‖iteratedFDeriv ℝ k f p‖ ≤ C :=
  exists_bound_of_periodic _ (hf.continuous_iteratedFDeriv (by exact_mod_cast hk))
    (iteratedFDeriv_periodic f hper k) t₀ t₁

/-! ### The Gowdy instance of the characteristic splitting setup -/

namespace GowdyFrameSolution

variable {t₀ t₁ : ℝ} (sol : GowdyFrameSolution t₀ t₁)

/-- The radius of the chart: one more than a bound of the reference state on the slab. -/
def chartRadius (h0 : 0 < t₀) : ℝ :=
  Classical.choose (exists_bound_of_periodic sol.Z (sol.contDiff_Z h0).continuous
    sol.periodic_Z t₀ t₁) + 1

theorem chartRadius_spec (h0 : 0 < t₀) :
    0 ≤ sol.chartRadius h0 - 1 ∧ ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ →
      ‖sol.Z p‖ ≤ sol.chartRadius h0 - 1 := by
  have := Classical.choose_spec (exists_bound_of_periodic sol.Z (sol.contDiff_Z h0).continuous
    sol.periodic_Z t₀ t₁)
  simpa [chartRadius] using this

/-- The derivative bound of the reference solution on the slab (orders 1–3 of `Z`, order 3
of `λ`). -/
def derivBound (h0 : 0 < t₀) : ℝ :=
  Classical.choose (exists_iteratedFDeriv_bound_of_periodic sol.Z (sol.contDiff_Z h0)
      sol.periodic_Z (k := 1) (by norm_num) t₀ t₁) +
    Classical.choose (exists_iteratedFDeriv_bound_of_periodic sol.Z (sol.contDiff_Z h0)
      sol.periodic_Z (k := 2) (by norm_num) t₀ t₁) +
    Classical.choose (exists_iteratedFDeriv_bound_of_periodic sol.Z (sol.contDiff_Z h0)
      sol.periodic_Z (k := 3) (by norm_num) t₀ t₁) +
    Classical.choose (exists_iteratedFDeriv_bound_of_periodic sol.lam sol.smooth_lam
      sol.periodic_lam (k := 3) (by norm_num) t₀ t₁)

theorem derivBound_spec (h0 : 0 < t₀) :
    0 ≤ sol.derivBound h0 ∧ ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ →
      ‖iteratedFDeriv ℝ 1 sol.Z p‖ ≤ sol.derivBound h0 ∧
      ‖iteratedFDeriv ℝ 2 sol.Z p‖ ≤ sol.derivBound h0 ∧
      ‖iteratedFDeriv ℝ 3 sol.Z p‖ ≤ sol.derivBound h0 ∧
      ‖iteratedFDeriv ℝ 3 sol.lam p‖ ≤ sol.derivBound h0 := by
  have h1 := Classical.choose_spec (exists_iteratedFDeriv_bound_of_periodic sol.Z
    (sol.contDiff_Z h0) sol.periodic_Z (k := 1) (by norm_num) t₀ t₁)
  have h2 := Classical.choose_spec (exists_iteratedFDeriv_bound_of_periodic sol.Z
    (sol.contDiff_Z h0) sol.periodic_Z (k := 2) (by norm_num) t₀ t₁)
  have h3 := Classical.choose_spec (exists_iteratedFDeriv_bound_of_periodic sol.Z
    (sol.contDiff_Z h0) sol.periodic_Z (k := 3) (by norm_num) t₀ t₁)
  have h4 := Classical.choose_spec (exists_iteratedFDeriv_bound_of_periodic sol.lam
    sol.smooth_lam sol.periodic_lam (k := 3) (by norm_num) t₀ t₁)
  unfold derivBound
  refine ⟨by linarith [h1.1, h2.1, h3.1, h4.1], fun p hp => ⟨?_, ?_, ?_, ?_⟩⟩
  · linarith [h1.2 p hp, h2.1, h3.1, h4.1]
  · linarith [h2.2 p hp, h1.1, h3.1, h4.1]
  · linarith [h3.2 p hp, h1.1, h2.1, h4.1]
  · linarith [h4.2 p hp, h1.1, h2.1, h3.1]

/-- The bound of the source field on the chart. -/
def fieldBound (h0 : 0 < t₀) : ℝ := Classical.choose (exists_field_bound h0 (sol.chartRadius h0))

/-- The second-difference constant of the source field on the chart. -/
def fieldSymm (h0 : 0 < t₀) : ℝ := Classical.choose (exists_field_symm h0 (sol.chartRadius h0))

/-- **The Gowdy splitting as a characteristic Strang-splitting setup**: reference state
`Z = (√t (a,b,c,d), P, Q, t)`, background `λ`, source field `eq:supp-gowdy-source-flow`,
densities `g± = |w±|²`, projections onto `w⁺`, `w⁻`, `(P, Q, t)`, chart
`{‖v‖ ≤ R, t ≥ t₀/2}`, tube radius `min 1 (t₀/2)`, explicit Lipschitz constant
`gowdyLipschitz (t₀/2) R`, density constants `8R` and `2`. -/
def strangSetup (h0 : 0 < t₀) : CharacteristicSplitting.StrangSetup StateVec where
  Z := sol.Z
  lam := sol.lam
  F := localFieldVec
  gp := densPlus
  gm := densMinus
  Pp := projPlus
  Pm := projMinus
  P0 := projZero
  K := chartK t₀ (sol.chartRadius h0)
  t₀ := t₀
  t₁ := t₁
  δ := min 1 (t₀ / 2)
  B := sol.fieldBound h0
  L := gowdyLipschitz (t₀ / 2) (sol.chartRadius h0)
  M := sol.fieldSymm h0
  Lg := 8 * sol.chartRadius h0
  Mg := 2
  D := sol.derivBound h0
  proj_sum := proj_sum
  norm_Pp := norm_projPlus_le
  norm_Pm := norm_projMinus_le
  norm_P0 := norm_projZero_le
  Z_smooth := sol.contDiff_Z h0
  lam_smooth := sol.smooth_lam
  Z_bound1 p hp := ((sol.derivBound_spec h0).2 p hp).1
  Z_bound2 p hp := ((sol.derivBound_spec h0).2 p hp).2.1
  Z_bound3 p hp := ((sol.derivBound_spec h0).2 p hp).2.2.1
  lam_bound3 p hp := ((sol.derivBound_spec h0).2 p hp).2.2.2
  char_plus p hp := sol.char_plus h0 hp
  char_minus p hp := sol.char_minus h0 hp
  char_zero p hp := sol.char_zero h0 hp
  char_lam p hp := sol.char_lam h0 hp
  δ_pos := lt_min one_pos (by linarith)
  tube p hp v hv := by
    have hR := (sol.chartRadius_spec h0).2 p hp
    have hδ1 : ‖v - sol.Z p‖ ≤ 1 := hv.trans (min_le_left _ _)
    have hδ2 : ‖v - sol.Z p‖ ≤ t₀ / 2 := hv.trans (min_le_right _ _)
    refine ⟨?_, ?_⟩
    · calc ‖v‖ = ‖(v - sol.Z p) + sol.Z p‖ := by rw [sub_add_cancel]
        _ ≤ ‖v - sol.Z p‖ + ‖sol.Z p‖ := norm_add_le _ _
        _ ≤ sol.chartRadius h0 := by linarith
    · have ht := abs_t_le (v - sol.Z p)
      have hZt : (sol.Z p).2.2.2 = p.1 := rfl
      simp only [Prod.snd_sub, hZt] at ht
      have := (abs_le.1 (ht.trans hδ2)).1
      linarith [hp.1]
  convex := convex_chartK t₀ _
  F_bound := (Classical.choose_spec (exists_field_bound h0 (sol.chartRadius h0))).2
  F_lip x hx y hy := localFieldVec_lipschitz_on_chart (by linarith)
    (by linarith [(sol.chartRadius_spec h0).1]) x (chartK_subset_gowdyChart hx) y
    (chartK_subset_gowdyChart hy)
  F_symm := (Classical.choose_spec (exists_field_symm h0 (sol.chartRadius h0))).2
  gp_lip x hx y hy := densPlus_lip hx.1 hy.1
  gm_lip x hx y hy := densMinus_lip hx.1 hy.1
  gp_symm x _ y _ := densPlus_symm x y
  gm_symm x _ y _ := densMinus_symm x y
  B_nonneg := (Classical.choose_spec (exists_field_bound h0 (sol.chartRadius h0))).1
  L_nonneg := gowdyLipschitz_nonneg (by linarith) (by linarith [(sol.chartRadius_spec h0).1])
  M_nonneg := (Classical.choose_spec (exists_field_symm h0 (sol.chartRadius h0))).1
  Lg_nonneg := by linarith [(sol.chartRadius_spec h0).1]
  Mg_nonneg := by norm_num
  D_nonneg := (sol.derivBound_spec h0).1

end GowdyFrameSolution

/-! ### Grid sampling and the consistency theorem -/

/-- The angle `θ_j = j · 2π/N` of the site `j ∈ ZMod N`. -/
def sampleAngle (N : ℕ) (j : ZMod N) : ℝ := (j.val : ℝ) * (2 * Real.pi / N)

theorem sampleAngle_add_one (N : ℕ) [NeZero N] (j : ZMod N) :
    ∃ k : ℤ, sampleAngle N (j + 1) = sampleAngle N j + 2 * Real.pi / N + k * (2 * Real.pi) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hv : (j + 1).val = (j.val + 1) % N := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  refine ⟨-(((j.val + 1) / N : ℕ) : ℤ), ?_⟩
  have hdm : (((j.val + 1) % N : ℕ) : ℝ) + N * (((j.val + 1) / N : ℕ) : ℝ) = j.val + 1 := by
    exact_mod_cast Nat.mod_add_div (j.val + 1) N
  have h' : (((j.val + 1) % N : ℕ) : ℝ) = j.val + 1 - N * (((j.val + 1) / N : ℕ) : ℝ) := by
    linarith
  unfold sampleAngle
  rw [hv, h', Int.cast_neg, Int.cast_natCast]
  field_simp
  ring

theorem periodic_int {E : Type*} (f : ℝ × ℝ → E)
    (hper : ∀ p : ℝ × ℝ, f (p.1, p.2 + 2 * Real.pi) = f p) (τ θ : ℝ) (k : ℤ) :
    f (τ, θ + k * (2 * Real.pi)) = f (τ, θ) := by
  have hperf : Function.Periodic (fun θ => f (τ, θ)) (2 * Real.pi) := fun θ => hper (τ, θ)
  exact (hperf.int_mul k) θ

theorem sample_succ {E : Type*} (f : ℝ × ℝ → E)
    (hper : ∀ p : ℝ × ℝ, f (p.1, p.2 + 2 * Real.pi) = f p) (N : ℕ) [NeZero N] (τ : ℝ)
    (j : ZMod N) : f (τ, sampleAngle N (j + 1)) = f (τ, sampleAngle N j + 2 * Real.pi / N) := by
  obtain ⟨k, hk⟩ := sampleAngle_add_one N j
  rw [hk, periodic_int f hper]

theorem sample_pred {E : Type*} (f : ℝ × ℝ → E)
    (hper : ∀ p : ℝ × ℝ, f (p.1, p.2 + 2 * Real.pi) = f p) (N : ℕ) [NeZero N] (τ : ℝ)
    (j : ZMod N) : f (τ, sampleAngle N (j - 1)) = f (τ, sampleAngle N j - 2 * Real.pi / N) := by
  obtain ⟨k, hk⟩ := sampleAngle_add_one N (j - 1)
  rw [sub_add_cancel] at hk
  have : sampleAngle N j - 2 * Real.pi / N =
      sampleAngle N (j - 1) + k * (2 * Real.pi) := by rw [hk]; ring
  rw [this, periodic_int f hper]

namespace GowdyFrameSolution

variable {t₀ t₁ : ℝ} (sol : GowdyFrameSolution t₀ t₁)

/-- The grid sampling `𝖲_ℓ X_*(τ)` of the reference solution on `ZMod N`, `ℓ = 2π/N`:
local state `Z(τ, θ_j)` and background `λ(τ, θ_j)` at site `j`. -/
def sample (N : ℕ) (τ : ℝ) : GridState N where
  site j := LocalState.ofVec (sol.Z (τ, sampleAngle N j))
  lam j := sol.lam (τ, sampleAngle N j)

/-- The local error of one split step on the grid, with the explicit constants of
`strangSetup` (see `symmetric_splitting_second_order`). -/
theorem local_error_grid (h0 : 0 < t₀) (N : ℕ) [NeZero N]
    (hN : 2 * Real.pi / N ≤ (sol.strangSetup h0).stepBound) (τ : ℝ) (hτ : t₀ ≤ τ)
    (hτh : τ + 2 * Real.pi / N ≤ t₁) (X₁ X₃ : GridState N)
    (h₁ : IsSourceStep (2 * Real.pi / N / 2) (sol.sample N τ) X₁)
    (h₃ : IsSourceStep (2 * Real.pi / N / 2) (transport (2 * Real.pi / N) X₁) X₃)
    (hd₁ : ∀ j, ‖(X₁.site j).toVec - ((sol.sample N τ).site j).toVec‖ ≤ (sol.strangSetup h0).δ)
    (hd₃ : ∀ j, ‖(X₃.site j).toVec - ((transport (2 * Real.pi / N) X₁).site j).toVec‖ ≤
      (sol.strangSetup h0).δ) (j : ZMod N) :
    ‖(X₃.site j).toVec - ((sol.sample N (τ + 2 * Real.pi / N)).site j).toVec‖ ≤
        max (sol.strangSetup h0).stateConst (sol.strangSetup h0).lamConst *
          (2 * Real.pi / N) ^ 3 ∧
      |X₃.lam j - (sol.sample N (τ + 2 * Real.pi / N)).lam j| ≤
        max (sol.strangSetup h0).stateConst (sol.strangSetup h0).lamConst *
          (2 * Real.pi / N) ^ 3 := by
  set S := sol.strangSetup h0 with hS
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  set θ := sampleAngle N j with hθ
  -- the sampled states in vector form
  have hsamp : ∀ k, ((sol.sample N τ).site k).toVec = sol.Z (τ, sampleAngle N k) := by
    intro k; simp [sample]
  have hZp : sol.Z (τ, sampleAngle N (j + 1)) = S.Z (τ, θ + ℓ) :=
    sample_succ sol.Z sol.periodic_Z N τ j
  have hZm : sol.Z (τ, sampleAngle N (j - 1)) = S.Z (τ, θ - ℓ) :=
    sample_pred sol.Z sol.periodic_Z N τ j
  -- stage one at the three sites
  have hstage1 : ∀ k, (X₁.site k).toVec = sol.Z (τ, sampleAngle N k) + (ℓ / 2) •
      localFieldVec ((1 / 2 : ℝ) • (sol.Z (τ, sampleAngle N k) + (X₁.site k).toVec)) := by
    intro k
    have := (isMidpointStep_iff_toVec _ _ _).1 (h₁.1 k)
    rwa [hsamp k] at this
  have hd1 : ∀ k, ‖(X₁.site k).toVec - sol.Z (τ, sampleAngle N k)‖ ≤ S.δ := by
    intro k; have := hd₁ k; rwa [hsamp k] at this
  have h1p := hstage1 (j + 1)
  have h1m := hstage1 (j - 1)
  have h10 := hstage1 j
  have hd1p := hd1 (j + 1)
  have hd1m := hd1 (j - 1)
  have hd10 := hd1 j
  rw [hZp] at h1p hd1p
  rw [hZm] at h1m hd1m
  -- the transported state and the last stage
  have htr : ((transport ℓ X₁).site j).toVec =
      S.transportCombine (X₁.site (j - 1)).toVec (X₁.site j).toVec (X₁.site (j + 1)).toVec := by
    rw [transport_site_toVec]
    rfl
  have h3 : (X₃.site j).toVec = S.transportCombine (X₁.site (j - 1)).toVec (X₁.site j).toVec
      (X₁.site (j + 1)).toVec + (ℓ / 2) • S.F ((1 / 2 : ℝ) • (S.transportCombine
        (X₁.site (j - 1)).toVec (X₁.site j).toVec (X₁.site (j + 1)).toVec + (X₃.site j).toVec)) := by
    have := (isMidpointStep_iff_toVec _ _ _).1 (h₃.1 j)
    rw [htr] at this
    exact this
  have hd3 := hd₃ j
  rw [htr] at hd3
  have hmain := S.local_error (h := ℓ) (τ := τ) (θ := θ) hℓpos hN hτ hτh h1m hd1m h10 hd10
    h1p hd1p h3 hd3
  obtain ⟨hst, hlam⟩ := hmain
  have hC1 : S.stateConst ≤ max S.stateConst S.lamConst := le_max_left _ _
  have hC2 : S.lamConst ≤ max S.stateConst S.lamConst := le_max_right _ _
  have hℓ3 : 0 ≤ ℓ ^ 3 := by positivity
  refine ⟨?_, ?_⟩
  · have e : ((sol.sample N (τ + ℓ)).site j).toVec = S.Z (τ + ℓ, θ) := by simp [sample]; rfl
    rw [e]
    exact hst.trans (mul_le_mul_of_nonneg_right hC1 hℓ3)
  · have elam : X₃.lam j = sol.lam (τ, θ) + ℓ / 2 *
        ((densPlus (X₁.site j).toVec + densPlus (X₁.site (j + 1)).toVec) +
          (densMinus (X₁.site j).toVec + densMinus (X₁.site (j - 1)).toVec)) := by
      rw [h₃.2]
      simp only [transport, h₁.2, sample]
      rfl
    rw [elam]
    exact hlam.trans (mul_le_mul_of_nonneg_right hC2 hℓ3)

/-- **The split step is well defined on the near-identity branch**: for `ℓ = 2π/N` below the
step threshold and `[τ, τ + ℓ] ⊆ [t₀, t₁]`, source half-steps from the sampled state and from
its transport exist with stage increments at most `δ` (Banach fixed point). -/
theorem step_exists (h0 : 0 < t₀) (N : ℕ) [NeZero N]
    (hN : 2 * Real.pi / N ≤ (sol.strangSetup h0).stepBound) (τ : ℝ) (hτ : t₀ ≤ τ)
    (hτh : τ + 2 * Real.pi / N ≤ t₁) :
    ∃ X₁ X₃ : GridState N,
      IsSourceStep (2 * Real.pi / N / 2) (sol.sample N τ) X₁ ∧
      IsSourceStep (2 * Real.pi / N / 2) (transport (2 * Real.pi / N) X₁) X₃ ∧
      (∀ j, ‖(X₁.site j).toVec - ((sol.sample N τ).site j).toVec‖ ≤ (sol.strangSetup h0).δ) ∧
      (∀ j, ‖(X₃.site j).toVec - ((transport (2 * Real.pi / N) X₁).site j).toVec‖ ≤
        (sol.strangSetup h0).δ) := by
  set S := sol.strangSetup h0 with hS
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hslab : ∀ k : ZMod N, ((τ, sampleAngle N k) : ℝ × ℝ).1 ∈ Icc S.t₀ S.t₁ :=
    fun k => ⟨hτ, by show τ ≤ t₁; linarith⟩
  have h1 := fun k : ZMod N => S.stage_one_exists hℓpos hN (hslab k)
  choose Y hYd hY using h1
  let X₁ : GridState N :=
    { site := fun k => LocalState.ofVec (Y k), lam := (sol.sample N τ).lam }
  have hsamp : ∀ k, ((sol.sample N τ).site k).toVec = sol.Z (τ, sampleAngle N k) := by
    intro k; simp [sample]
  have hX₁ : IsSourceStep (ℓ / 2) (sol.sample N τ) X₁ := by
    refine ⟨fun k => ?_, rfl⟩
    rw [isMidpointStep_iff_toVec, hsamp k]
    exact hY k
  have hnear : ∀ j, ‖((transport ℓ X₁).site j).toVec - S.Z (τ + ℓ, sampleAngle N j)‖ ≤
      S.δ / 2 := by
    intro j
    have hZp : S.Z (τ, sampleAngle N (j + 1)) = S.Z (τ, sampleAngle N j + ℓ) :=
      sample_succ sol.Z sol.periodic_Z N τ j
    have hZm : S.Z (τ, sampleAngle N (j - 1)) = S.Z (τ, sampleAngle N j - ℓ) :=
      sample_pred sol.Z sol.periodic_Z N τ j
    have h1p := hY (j + 1)
    have h1m := hY (j - 1)
    have hd1p := hYd (j + 1)
    have hd1m := hYd (j - 1)
    rw [hZp] at h1p hd1p
    rw [hZm] at h1m hd1m
    rw [transport_site_toVec]
    exact S.transportCombine_near hℓpos hN hτ hτh h1m hd1m (hY j) (hYd j) h1p hd1p
  have h3 := fun j : ZMod N => S.stage_three_exists hℓpos hN hτ hτh (hnear j)
  choose Y3 hY3d hY3 using h3
  let X₃ : GridState N :=
    { site := fun k => LocalState.ofVec (Y3 k), lam := (transport ℓ X₁).lam }
  refine ⟨X₁, X₃, hX₁, ⟨fun k => ?_, rfl⟩, fun k => ?_, fun k => ?_⟩
  · rw [isMidpointStep_iff_toVec]
    exact hY3 k
  · rw [hsamp k]; exact hYd k
  · exact (hY3d k).trans (by linarith [S.δ_pos])

/-- **Second-order consistency of the Gowdy symmetric splitting**
(`thm:supp-gowdy-momentum`, consistency clause).  For a `C³` solution of the frame system
`eq:supp-gowdy-frame-system` on the slab `[t₀, t₁] × 𝕋¹` with `t₀ > 0` there are `C`, `h₀ > 0`
and a near-identity radius `δ > 0` such that, for every grid `ZMod N` with synchronized step
`h = ℓ = 2π/N ≤ h₀` and every `τ` with `[τ, τ + ℓ] ⊆ [t₀, t₁]`:

* the source-half / transport / source-half step from the sampled state `𝖲_ℓ X_*(τ)` exists
  on the near-identity branch (implicit-midpoint half-steps of duration `ℓ/2` with stage
  increments `≤ δ`), and
* every such realisation `(X₁, X₃)` reproduces the sampled solution at `τ + ℓ` up to `C ℓ³`
  at every site `j`: `‖X₃(j) - X_*(τ+ℓ, θ_j)‖ ≤ C ℓ³` (local state `(U, P, Q, t)`, sup norm)
  and `|λ₃(j) - λ_*(τ+ℓ, θ_j)| ≤ C ℓ³`. -/
theorem symmetric_splitting_second_order (h0 : 0 < t₀) :
    ∃ C h₀ δ : ℝ, 0 < h₀ ∧ 0 < δ ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ h₀ →
      ∀ τ : ℝ, t₀ ≤ τ → τ + 2 * Real.pi / N ≤ t₁ →
      (∃ X₁ X₃ : GridState N,
        IsSourceStep (2 * Real.pi / N / 2) (sol.sample N τ) X₁ ∧
        IsSourceStep (2 * Real.pi / N / 2) (transport (2 * Real.pi / N) X₁) X₃ ∧
        (∀ j, ‖(X₁.site j).toVec - ((sol.sample N τ).site j).toVec‖ ≤ δ) ∧
        (∀ j, ‖(X₃.site j).toVec - ((transport (2 * Real.pi / N) X₁).site j).toVec‖ ≤ δ)) ∧
      ∀ X₁ X₃ : GridState N,
        IsSourceStep (2 * Real.pi / N / 2) (sol.sample N τ) X₁ →
        IsSourceStep (2 * Real.pi / N / 2) (transport (2 * Real.pi / N) X₁) X₃ →
        (∀ j, ‖(X₁.site j).toVec - ((sol.sample N τ).site j).toVec‖ ≤ δ) →
        (∀ j, ‖(X₃.site j).toVec - ((transport (2 * Real.pi / N) X₁).site j).toVec‖ ≤ δ) →
        ∀ j, ‖(X₃.site j).toVec - ((sol.sample N (τ + 2 * Real.pi / N)).site j).toVec‖ ≤
            C * (2 * Real.pi / N) ^ 3 ∧
          |X₃.lam j - (sol.sample N (τ + 2 * Real.pi / N)).lam j| ≤
            C * (2 * Real.pi / N) ^ 3 := by
  refine ⟨max (sol.strangSetup h0).stateConst (sol.strangSetup h0).lamConst,
    (sol.strangSetup h0).stepBound, (sol.strangSetup h0).δ, (sol.strangSetup h0).stepBound_pos,
    (sol.strangSetup h0).δ_pos, fun N _ hN τ hτ hτh => ⟨sol.step_exists h0 N hN τ hτ hτh, ?_⟩⟩
  intro X₁ X₃ h₁ h₃ hd₁ hd₃ j
  exact sol.local_error_grid h0 N hN τ hτ hτh X₁ X₃ h₁ h₃ hd₁ hd₃ j

end GowdyFrameSolution

/-- **Non-vacuity**: the trivial frame data `a = b = c = d = P = Q = λ = 0` solve the frame
system on every slab, so `GowdyFrameSolution` is inhabited. -/
example (t₀ t₁ : ℝ) : GowdyFrameSolution t₀ t₁ where
  a := 0
  b := 0
  c := 0
  d := 0
  P := 0
  Q := 0
  lam := 0
  smooth_a := contDiff_const
  smooth_b := contDiff_const
  smooth_c := contDiff_const
  smooth_d := contDiff_const
  smooth_P := contDiff_const
  smooth_Q := contDiff_const
  smooth_lam := contDiff_const
  periodic_a _ := rfl
  periodic_b _ := rfl
  periodic_c _ := rfl
  periodic_d _ := rfl
  periodic_P _ := rfl
  periodic_Q _ := rfl
  periodic_lam _ := rfl
  eq_a _ _ := by simp [dT, dΘ]
  eq_b _ _ := by simp [dT, dΘ]
  eq_c _ _ := by simp [dT, dΘ]
  eq_d _ _ := by simp [dT, dΘ]
  eq_P _ _ := by simp [dT]
  eq_Q _ _ := by simp [dT]
  eq_lam _ _ := by simp [dT]

end

end RenewalGeometry.GowdyStaggered
