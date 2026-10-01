/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cutoff continuation and first exit for autonomous ODEs

The finite open writer of the emergent-spacetime manuscript (`cor:supp-open-lifespan`) is, for each
cutoff, an autonomous ODE `y' = F(y)` on a finite-dimensional space whose vector field is smooth
only on a chart.  Its common lifespan is obtained from an a priori bound by a first-exit
(continuation) argument.  This file provides that argument in general form:

* `firstExit_le`: continuous induction.  If `φ` is continuous on `[0, T]`, `φ 0 ≤ a < b`, and
  `φ ≤ b` on `[0, t]` forces `φ t ≤ a`, then `φ ≤ a` on `[0, T]`;
* `cutoff`, `cutoffField`: the piecewise-linear cutoff `χ_ρ` (`1` on `(-∞, ρ]`, `0` on
  `[2ρ, ∞)`) and the cut-off field `χ_ρ(Φ x) F(x)`; `lipschitzWith_cutoffField`: if `Φ` is
  Lipschitz and `F` is Lipschitz and bounded on `{Φ ≤ 2ρ}`, the cut-off field is globally
  Lipschitz (and bounded, `norm_cutoffField_le`);
* `exists_hasDerivWithinAt_of_lipschitzWith`: a globally Lipschitz bounded autonomous field has a
  solution on every compact time interval (Picard–Lindelöf, `IsPicardLindelof`);
* `exists_solution_of_apriori`: **existence through a prescribed time from an a priori bound**:
  if every solution that stays in `{Ψ ≤ b}` on `[0, t]` actually satisfies `Ψ ≤ a < b` at `t`,
  and `{Ψ ≤ b} ⊆ {Φ ≤ ρ}`, then a solution exists on all of `[0, T]` and stays in `{Ψ ≤ a}`;
* `eqOn_of_apriori`: **uniqueness** under the same a priori bound (every solution stays in the
  Lipschitz region, so `ODE_solution_unique_of_mem_Icc_right` applies).
-/

open Set Metric Filter Topology
open scoped NNReal

namespace RenewalGeometry.ODECutoff

noncomputable section

/-! ### Continuous induction -/

/-- **First exit (continuous induction).**  Let `φ` be continuous on `[0, T]` with `φ 0 ≤ a < b`.
If, for every `t ∈ [0, T]`, the bound `φ ≤ b` on `[0, t]` implies `φ t ≤ a`, then `φ ≤ a` on the
whole interval. -/
theorem firstExit_le {φ : ℝ → ℝ} {T a b : ℝ} (hφ : ContinuousOn φ (Icc 0 T)) (hab : a < b)
    (h0 : φ 0 ≤ a) (hstep : ∀ t ∈ Icc 0 T, (∀ τ ∈ Icc 0 t, φ τ ≤ b) → φ t ≤ a) :
    ∀ t ∈ Icc 0 T, φ t ≤ a := by
  have hb : ∀ t ∈ Icc 0 T, φ t < b := by
    by_contra hcon
    push Not at hcon
    set S : Set ℝ := Icc 0 T ∩ φ ⁻¹' Ici b with hSdef
    have hSne : S.Nonempty := by
      obtain ⟨t, ht, h⟩ := hcon
      exact ⟨t, ht, h⟩
    have hScl : IsClosed S := hφ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
    set t0 := sInf S
    have ht0 : t0 ∈ S := hScl.csInf_mem hSne hSbdd
    have hlt : ∀ τ ∈ Ico 0 t0, φ τ < b := by
      intro τ hτ
      by_contra h
      push Not at h
      have hmem : τ ∈ S := ⟨⟨hτ.1, hτ.2.le.trans ht0.1.2⟩, h⟩
      exact absurd (csInf_le hSbdd hmem) (not_le.mpr hτ.2)
    have ht0pos : 0 < t0 := by
      rcases ht0.1.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have h2 : b ≤ φ t0 := ht0.2
        rw [← h] at h2
        linarith
    have hle : φ t0 ≤ b := by
      have hcl : t0 ∈ closure (Ico 0 t0) := by
        rw [closure_Ico ht0pos.ne]
        exact ⟨ht0pos.le, le_rfl⟩
      have hc : ContinuousWithinAt φ (Ico 0 t0) t0 :=
        (hφ t0 ht0.1).mono fun τ hτ => ⟨hτ.1, hτ.2.le.trans ht0.1.2⟩
      exact ContinuousWithinAt.closure_le hcl hc continuousWithinAt_const fun τ hτ =>
        (hlt τ hτ).le
    have hfin := hstep t0 ht0.1 fun τ hτ => by
      rcases hτ.2.lt_or_eq with h | h
      · exact (hlt τ ⟨hτ.1, h⟩).le
      · rw [h]; exact hle
    have h2 : b ≤ φ t0 := ht0.2
    linarith
  intro t ht
  exact hstep t ht fun τ hτ => (hb τ ⟨hτ.1, hτ.2.trans ht.2⟩).le

/-! ### The cutoff -/

/-- The piecewise-linear cutoff `χ_ρ(r) = max 0 (min 1 ((2ρ - r)/ρ))`. -/
def cutoff (ρ r : ℝ) : ℝ := max 0 (min 1 ((2 * ρ - r) / ρ))

theorem cutoff_nonneg (ρ r : ℝ) : 0 ≤ cutoff ρ r := le_max_left _ _

theorem cutoff_le_one (ρ r : ℝ) : cutoff ρ r ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem cutoff_of_le {ρ r : ℝ} (hρ : 0 < ρ) (h : r ≤ ρ) : cutoff ρ r = 1 := by
  unfold cutoff
  have h1 : 1 ≤ (2 * ρ - r) / ρ := by rw [le_div_iff₀ hρ]; linarith
  rw [min_eq_left h1, max_eq_right zero_le_one]

theorem cutoff_of_ge {ρ r : ℝ} (hρ : 0 < ρ) (h : 2 * ρ ≤ r) : cutoff ρ r = 0 := by
  unfold cutoff
  have h1 : (2 * ρ - r) / ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hρ.le
  rw [min_eq_right (h1.trans zero_le_one), max_eq_left h1]

theorem abs_cutoff_sub_le {ρ : ℝ} (hρ : 0 < ρ) (r r' : ℝ) :
    |cutoff ρ r - cutoff ρ r'| ≤ |r - r'| / ρ := by
  unfold cutoff
  calc |max 0 (min 1 ((2 * ρ - r) / ρ)) - max 0 (min 1 ((2 * ρ - r') / ρ))|
      ≤ |min 1 ((2 * ρ - r) / ρ) - min 1 ((2 * ρ - r') / ρ)| := by
        rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ ≤ max |1 - 1| |(2 * ρ - r) / ρ - (2 * ρ - r') / ρ| := abs_min_sub_min_le_max _ _ _ _
    _ = |r - r'| / ρ := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _), div_sub_div_same,
          show 2 * ρ - r - (2 * ρ - r') = r' - r by ring, abs_div, abs_of_pos hρ, abs_sub_comm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cut-off vector field `x ↦ χ_ρ(Φ x) F(x)`. -/
def cutoffField (F : E → E) (Φ : E → ℝ) (ρ : ℝ) (x : E) : E := cutoff ρ (Φ x) • F x

theorem cutoffField_eq {F : E → E} {Φ : E → ℝ} {ρ : ℝ} (hρ : 0 < ρ) {x : E} (hx : Φ x ≤ ρ) :
    cutoffField F Φ ρ x = F x := by
  simp [cutoffField, cutoff_of_le hρ hx]

theorem norm_cutoffField_le {F : E → E} {Φ : E → ℝ} {ρ M : ℝ} (hρ : 0 < ρ) (hM0 : 0 ≤ M)
    (hM : ∀ x, Φ x ≤ 2 * ρ → ‖F x‖ ≤ M) (x : E) : ‖cutoffField F Φ ρ x‖ ≤ M := by
  unfold cutoffField
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
  by_cases hx : Φ x ≤ 2 * ρ
  · calc cutoff ρ (Φ x) * ‖F x‖ ≤ 1 * M :=
          mul_le_mul (cutoff_le_one _ _) (hM x hx) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  · rw [cutoff_of_ge hρ (le_of_lt (not_le.mp hx)), zero_mul]; exact hM0

/-- **The cut-off field is globally Lipschitz**: if `Φ` is `K_Φ`-Lipschitz and `F` is
`L`-Lipschitz with `‖F‖ ≤ M` on `{Φ ≤ 2ρ}`, then `χ_ρ(Φ) F` is `(L + M K_Φ/ρ)`-Lipschitz. -/
theorem lipschitzWith_cutoffField {F : E → E} {Φ : E → ℝ} {ρ : ℝ} {KΦ L M : ℝ≥0} (hρ : 0 < ρ)
    (hΦ : LipschitzWith KΦ Φ) (hF : LipschitzOnWith L F {x | Φ x ≤ 2 * ρ})
    (hM : ∀ x, Φ x ≤ 2 * ρ → ‖F x‖ ≤ M) :
    LipschitzWith (L + Real.toNNReal ((M : ℝ) * KΦ / ρ)) (cutoffField F Φ ρ) := by
  set c : ℝ := (M : ℝ) * KΦ / ρ with hc
  have hc0 : 0 ≤ c := by positivity
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_add, Real.coe_toNNReal _ hc0, dist_eq_norm, dist_eq_norm]
  set d := ‖x - y‖
  have hd : 0 ≤ d := norm_nonneg _
  have hχ : |cutoff ρ (Φ x) - cutoff ρ (Φ y)| ≤ KΦ * d / ρ := by
    refine (abs_cutoff_sub_le hρ _ _).trans ?_
    have h1 := hΦ.dist_le_mul x y
    rw [Real.dist_eq, dist_eq_norm] at h1
    exact div_le_div_of_nonneg_right h1 hρ.le
  -- the cutoff-difference term at a point of the Lipschitz region
  have hdiff : ∀ z, Φ z ≤ 2 * ρ → ‖(cutoff ρ (Φ x) - cutoff ρ (Φ y)) • F z‖ ≤ c * d := by
    intro z hz
    rw [norm_smul, Real.norm_eq_abs]
    calc |cutoff ρ (Φ x) - cutoff ρ (Φ y)| * ‖F z‖ ≤ KΦ * d / ρ * M :=
          mul_le_mul hχ (hM z hz) (norm_nonneg _) (by positivity)
      _ = c * d := by rw [hc]; ring
  have hLd : 0 ≤ (L : ℝ) * d := by positivity
  unfold cutoffField
  by_cases hx : Φ x ≤ 2 * ρ <;> by_cases hy : Φ y ≤ 2 * ρ
  · have e : cutoff ρ (Φ x) • F x - cutoff ρ (Φ y) • F y =
        cutoff ρ (Φ x) • (F x - F y) + (cutoff ρ (Φ x) - cutoff ρ (Φ y)) • F y := by
      rw [smul_sub, sub_smul]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖cutoff ρ (Φ x) • (F x - F y)‖ ≤ L * d := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
      have h2 := hF.dist_le_mul x hx y hy
      rw [dist_eq_norm, dist_eq_norm] at h2
      calc cutoff ρ (Φ x) * ‖F x - F y‖ ≤ 1 * (L * d) :=
            mul_le_mul (cutoff_le_one _ _) h2 (norm_nonneg _) zero_le_one
        _ = L * d := one_mul _
    have h3 := hdiff y hy
    nlinarith
  · have hy0 : cutoff ρ (Φ y) = 0 := cutoff_of_ge hρ (le_of_lt (not_le.mp hy))
    have e : cutoff ρ (Φ x) • F x - cutoff ρ (Φ y) • F y =
        (cutoff ρ (Φ x) - cutoff ρ (Φ y)) • F x := by
      rw [hy0, zero_smul, sub_zero, sub_zero]
    rw [e]
    have := hdiff x hx
    nlinarith
  · have hx0 : cutoff ρ (Φ x) = 0 := cutoff_of_ge hρ (le_of_lt (not_le.mp hx))
    have e : cutoff ρ (Φ x) • F x - cutoff ρ (Φ y) • F y =
        (cutoff ρ (Φ x) - cutoff ρ (Φ y)) • F y := by
      rw [hx0, zero_smul, zero_sub, zero_sub, neg_smul]
    rw [e]
    have := hdiff y hy
    nlinarith
  · have hx0 : cutoff ρ (Φ x) = 0 := cutoff_of_ge hρ (le_of_lt (not_le.mp hx))
    have hy0 : cutoff ρ (Φ y) = 0 := cutoff_of_ge hρ (le_of_lt (not_le.mp hy))
    rw [hx0, hy0, zero_smul, zero_smul, sub_zero, norm_zero]
    positivity

/-! ### Global solutions of globally Lipschitz bounded fields -/

/-- **Picard–Lindelöf for a globally Lipschitz bounded autonomous field**: a solution exists on
every compact time interval, through any initial point. -/
theorem exists_hasDerivWithinAt_of_lipschitzWith [CompleteSpace E] {G : E → E} {K M : ℝ≥0}
    (hG : LipschitzWith K G) (hM : ∀ x, ‖G x‖ ≤ M) (x0 : E) {tmin tmax t0 : ℝ}
    (ht0 : t0 ∈ Icc tmin tmax) :
    ∃ y : ℝ → E, y t0 = x0 ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt y (G (y t)) (Icc tmin tmax) t := by
  set a : ℝ≥0 := M * Real.toNNReal (tmax - tmin)
  have hPL : IsPicardLindelof (fun _ => G) (⟨t0, ht0⟩ : Icc tmin tmax) x0 a 0 M K := by
    refine IsPicardLindelof.of_time_independent (fun x _ => hM x) hG.lipschitzOnWith ?_
    simp only [a, NNReal.coe_mul, Real.coe_toNNReal', NNReal.coe_zero, sub_zero]
    have h1 : max (tmax - t0) (t0 - tmin) ≤ max (tmax - tmin) 0 := by
      refine max_le ?_ ?_
      · exact (by linarith [ht0.1] : tmax - t0 ≤ tmax - tmin).trans (le_max_left _ _)
      · exact (by linarith [ht0.2] : t0 - tmin ≤ tmax - tmin).trans (le_max_left _ _)
    exact mul_le_mul_of_nonneg_left h1 M.2
  exact IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hPL

/-! ### Existence and uniqueness from an a priori bound -/

/-- **Existence through a prescribed time from an a priori bound** (first-exit argument).

Let `F` be `L`-Lipschitz with `‖F‖ ≤ M` on `{Φ ≤ 2ρ}`, `Φ` Lipschitz, `Ψ` continuous with
`{Ψ ≤ b} ⊆ {Φ ≤ ρ}`, and `a < b`.  Suppose every solution `y` of `y' = F(y)` with `y 0 = x0`
which stays in `{Ψ ≤ b}` on `[0, t]` (`t ≤ T`) satisfies `Ψ (y t) ≤ a`.  If `Ψ x0 ≤ a`, then
there is a solution on `[0, T]` (two-sided derivatives at every `t ∈ [0, T]`) staying in
`{Ψ ≤ a}`. -/
theorem exists_solution_of_apriori [CompleteSpace E] (F : E → E) (Φ Ψ : E → ℝ) {KΦ L M : ℝ≥0}
    {ρ a b T : ℝ} (hρ : 0 < ρ) (hΦ : LipschitzWith KΦ Φ)
    (hF : LipschitzOnWith L F {x | Φ x ≤ 2 * ρ}) (hM : ∀ x, Φ x ≤ 2 * ρ → ‖F x‖ ≤ M)
    (hΨ : Continuous Ψ) (hab : a < b) (hΨΦ : ∀ x, Ψ x ≤ b → Φ x ≤ ρ) (hT : 0 ≤ T) (x0 : E)
    (hx0 : Ψ x0 ≤ a)
    (hapriori : ∀ y : ℝ → E, y 0 = x0 → ∀ t ∈ Icc 0 T,
      (∀ τ ∈ Icc 0 t, HasDerivAt y (F (y τ)) τ ∧ Ψ (y τ) ≤ b) → Ψ (y t) ≤ a) :
    ∃ y : ℝ → E, y 0 = x0 ∧ ∀ t ∈ Icc 0 T, HasDerivAt y (F (y t)) t ∧ Ψ (y t) ≤ a := by
  set G := cutoffField F Φ ρ
  have hG := lipschitzWith_cutoffField hρ hΦ hF hM
  have hGM : ∀ x, ‖G x‖ ≤ M := norm_cutoffField_le hρ M.2 hM
  obtain ⟨y, hy0, hy⟩ := exists_hasDerivWithinAt_of_lipschitzWith hG hGM x0
    (tmin := -1) (tmax := T + 1) (t0 := 0) ⟨by norm_num, by linarith⟩
  have hyd : ∀ t ∈ Icc 0 T, HasDerivAt y (G (y t)) t := by
    intro t ht
    have hmem : t ∈ Icc (-1) (T + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine (hy t hmem).hasDerivAt (Icc_mem_nhds ?_ ?_)
    · linarith [ht.1]
    · linarith [ht.2]
  have hcont : ContinuousOn (fun t => Ψ (y t)) (Icc 0 T) := fun t ht =>
    (hΨ.continuousAt.comp (hyd t ht).continuousAt).continuousWithinAt
  have hstay : ∀ t ∈ Icc 0 T, Ψ (y t) ≤ a := by
    refine firstExit_le hcont hab (by rw [hy0]; exact hx0) fun t ht hbt => ?_
    refine hapriori y hy0 t ht fun τ hτ => ⟨?_, hbt τ hτ⟩
    have hτT : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.trans ht.2⟩
    have := hyd τ hτT
    rwa [show G (y τ) = F (y τ) from cutoffField_eq hρ (hΨΦ _ (hbt τ hτ))] at this
  refine ⟨y, hy0, fun t ht => ⟨?_, hstay t ht⟩⟩
  have := hyd t ht
  rwa [show G (y t) = F (y t) from cutoffField_eq hρ (hΨΦ _ ((hstay t ht).trans hab.le))] at this

/-- **Uniqueness under an a priori bound**: two solutions on `[0, T]` with the same initial point
`x0`, `Ψ x0 ≤ a`, coincide on `[0, T]` (both stay in `{Ψ ≤ a} ⊆ {Φ ≤ ρ}` by the first-exit
argument, where `F` is Lipschitz). -/
theorem eqOn_of_apriori (F : E → E) (Φ Ψ : E → ℝ) {L : ℝ≥0} {ρ a b T : ℝ}
    (hF : LipschitzOnWith L F {x | Φ x ≤ 2 * ρ}) (hρ : 0 ≤ ρ)
    (hΨ : Continuous Ψ) (hab : a < b) (hΨΦ : ∀ x, Ψ x ≤ b → Φ x ≤ ρ) (x0 : E)
    (hx0 : Ψ x0 ≤ a)
    (hapriori : ∀ y : ℝ → E, y 0 = x0 → ∀ t ∈ Icc 0 T,
      (∀ τ ∈ Icc 0 t, HasDerivAt y (F (y τ)) τ ∧ Ψ (y τ) ≤ b) → Ψ (y t) ≤ a)
    (y z : ℝ → E) (hy0 : y 0 = x0) (hz0 : z 0 = x0)
    (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (F (y t)) t) (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (F (z t)) t) :
    EqOn y z (Icc 0 T) := by
  have hstay : ∀ w : ℝ → E, w 0 = x0 → (∀ t ∈ Icc 0 T, HasDerivAt w (F (w t)) t) →
      ∀ t ∈ Icc 0 T, Ψ (w t) ≤ a := by
    intro w hw0 hw
    have hcont : ContinuousOn (fun t => Ψ (w t)) (Icc 0 T) := fun t ht =>
      (hΨ.continuousAt.comp (hw t ht).continuousAt).continuousWithinAt
    exact firstExit_le hcont hab (by rw [hw0]; exact hx0) fun t ht hbt =>
      hapriori w hw0 t ht fun τ hτ => ⟨hw τ ⟨hτ.1, hτ.2.trans ht.2⟩, hbt τ hτ⟩
  have hys := hstay y hy0 hy
  have hzs := hstay z hz0 hz
  have hmem : ∀ w : ℝ → E, (∀ t ∈ Icc 0 T, Ψ (w t) ≤ a) →
      ∀ t ∈ Ico 0 T, w t ∈ {x | Φ x ≤ 2 * ρ} := by
    intro w hw t ht
    have := hΨΦ _ ((hw t (Ico_subset_Icc_self ht)).trans hab.le)
    show Φ (w t) ≤ 2 * ρ
    linarith
  refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => {x | Φ x ≤ 2 * ρ})
    (K := L) (fun _ _ => hF)
    (fun t ht => (hy t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hy t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (hmem y hys)
    (fun t ht => (hz t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hz t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (hmem z hzs)
    (by rw [hy0, hz0])

/-! ### Forced square-root Gronwall inequality -/

/-- **Forced Gronwall inequality for `√E`.**  If `E ≥ 0` is differentiable on `[0, T]` with
`E' ≤ K E + K √E g` for a continuous `g ≥ 0` and `K ≥ 0`, then
`√E(t) ≤ e^{K t} (√E(0) + K ∫_0^t g)` on `[0, T]`.  (This is the scalar form of
`(𝓔^{1/2})' ≤ C 𝓔^{1/2} + C g`, without dividing by `√E` where `E` vanishes.) -/
theorem sqrt_le_of_forced_deriv {E g : ℝ → ℝ} {K T : ℝ} (hK : 0 ≤ K)
    (hE : ∀ t ∈ Icc 0 T, ∃ e', HasDerivAt E e' t ∧ e' ≤ K * E t + K * Real.sqrt (E t) * g t)
    (hE0 : ∀ t ∈ Icc 0 T, 0 ≤ E t) (hg : ContinuousOn g (Icc 0 T))
    (hg0 : ∀ t ∈ Icc 0 T, 0 ≤ g t) :
    ∀ t ∈ Icc 0 T, Real.sqrt (E t) ≤
      Real.exp (K * t) * (Real.sqrt (E 0) + K * ∫ τ in (0)..t, g τ) := by
  choose! e' he' using hE
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hgi : ∀ u ∈ Icc 0 T, IntervalIntegrable g MeasureTheory.volume 0 u := fun u hu =>
    (hg.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc hu.1
  set h : ℝ → ℝ := fun σ => Real.exp (-K * σ) * g σ
  have hhc : ContinuousOn h (Icc 0 T) := (Real.continuous_exp.comp
    (continuous_const.mul continuous_id)).continuousOn.mul hg
  have hhi : ∀ u ∈ Icc 0 T, IntervalIntegrable h MeasureTheory.volume 0 u := fun u hu =>
    (hhc.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc hu.1
  -- the key estimate for every regularization `η > 0`
  have key : ∀ η > 0, Real.sqrt (E t) ≤
      Real.exp (K * t) * (Real.sqrt (E 0) + K * ∫ τ in (0)..t, g τ) +
        Real.exp (K * t) * Real.sqrt η := by
    intro η hη
    set φ : ℝ → ℝ := fun τ => Real.sqrt (E τ + η)
    have hpos : ∀ τ ∈ Icc 0 T, 0 < E τ + η := fun τ hτ => by linarith [hE0 τ hτ]
    have hφd : ∀ τ ∈ Icc 0 T, HasDerivAt φ (e' τ / (2 * φ τ)) τ := by
      intro τ hτ
      have h1 := (Real.hasDerivAt_sqrt (hpos τ hτ).ne').comp τ ((he' τ hτ).1.add_const η)
      refine h1.congr_deriv ?_
      simp only [φ]; ring
    have hφbd : ∀ τ ∈ Icc 0 T, e' τ / (2 * φ τ) ≤ K * φ τ + K * g τ := by
      intro τ hτ
      have hφp : 0 < φ τ := Real.sqrt_pos.mpr (hpos τ hτ)
      have hsq : φ τ ^ 2 = E τ + η := Real.sq_sqrt (hpos τ hτ).le
      have hsE : Real.sqrt (E τ) ≤ φ τ := Real.sqrt_le_sqrt (by linarith)
      have hsE0 := Real.sqrt_nonneg (E τ)
      rw [div_le_iff₀ (by positivity)]
      have h1 := (he' τ hτ).2
      have hg' := hg0 τ hτ
      have h2 : K * E τ ≤ K * φ τ ^ 2 := mul_le_mul_of_nonneg_left (by linarith) hK
      have h3 : K * Real.sqrt (E τ) * g τ ≤ K * φ τ * g τ := by
        have := mul_le_mul_of_nonneg_left hsE hK
        exact mul_le_mul_of_nonneg_right this hg'
      nlinarith [mul_nonneg hK hφp.le, mul_nonneg (mul_nonneg hK hφp.le) hg']
    -- `ψ = e^{-Kτ} φ - K ∫_0^τ e^{-Kσ} g` is antitone
    set ψ : ℝ → ℝ := fun τ => Real.exp (-K * τ) * φ τ - K * ∫ σ in (0)..τ, h σ
    have hψc : ContinuousOn ψ (Icc 0 T) := by
      refine ContinuousOn.sub ?_ (continuousOn_const.mul ?_)
      · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
          fun τ hτ => (hφd τ hτ).continuousAt.continuousWithinAt
      · have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
          (f := h) (a := 0) (b := T) (by
            rw [uIcc_of_le hT]
            exact hhc.integrableOn_Icc)
        rwa [uIcc_of_le hT] at this
    have hψd : ∀ τ ∈ Ioo 0 T, HasDerivAt ψ (Real.exp (-K * τ) * (-K) * φ τ +
        Real.exp (-K * τ) * (e' τ / (2 * φ τ)) - K * h τ) τ := by
      intro τ hτ
      have hτ' : τ ∈ Icc 0 T := Ioo_subset_Icc_self hτ
      have h1 : HasDerivAt (fun σ => Real.exp (-K * σ)) (Real.exp (-K * τ) * (-K)) τ := by
        have := ((hasDerivAt_id τ).const_mul (-K)).exp
        simpa using this
      have h2 : HasDerivAt (fun u => ∫ σ in (0)..u, h σ) (h τ) τ :=
        intervalIntegral.integral_hasDerivAt_right (hhi τ hτ')
          (hhc.mono Ioo_subset_Icc_self |>.stronglyMeasurableAtFilter isOpen_Ioo τ hτ)
          (hhc.continuousAt (Icc_mem_nhds hτ.1 hτ.2))
      exact (h1.mul (hφd τ hτ')).sub (h2.const_mul K)
    have hanti : AntitoneOn ψ (Icc 0 T) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hψc ?_ ?_
      · intro τ hτ
        rw [interior_Icc] at hτ
        exact (hψd τ hτ).differentiableAt.differentiableWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        rw [(hψd τ hτ).deriv]
        have hb := hφbd τ (Ioo_subset_Icc_self hτ)
        have hex := Real.exp_pos (-K * τ)
        have : Real.exp (-K * τ) * (e' τ / (2 * φ τ)) ≤
            Real.exp (-K * τ) * (K * φ τ + K * g τ) := mul_le_mul_of_nonneg_left hb hex.le
        simp only [h]
        nlinarith
    have hψt := hanti ⟨le_rfl, hT⟩ ht ht.1
    simp only [ψ, mul_zero, Real.exp_zero, one_mul, intervalIntegral.integral_same, sub_zero]
      at hψt
    -- `∫ e^{-Kσ} g ≤ ∫ g`
    have hint : ∫ σ in (0)..t, h σ ≤ ∫ σ in (0)..t, g σ := by
      refine intervalIntegral.integral_mono_on ht.1 (hhi t ht) (hgi t ht) fun σ hσ => ?_
      have hσT : σ ∈ Icc 0 T := ⟨hσ.1, hσ.2.trans ht.2⟩
      have h1 : Real.exp (-K * σ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hσ.1])
      have := hg0 σ hσT
      simp only [h]
      nlinarith
    have hφt : φ t ≤ Real.exp (K * t) * (φ 0 + K * ∫ σ in (0)..t, g σ) := by
      have e1 : φ t = Real.exp (K * t) * (Real.exp (-K * t) * φ t) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
      rw [e1]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have := mul_le_mul_of_nonneg_left hint hK
      linarith
    have hs1 : Real.sqrt (E t) ≤ φ t := Real.sqrt_le_sqrt (by linarith)
    have hs0 : φ 0 ≤ Real.sqrt (E 0) + Real.sqrt η := by
      simp only [φ]
      have ha := Real.sq_sqrt (hE0 0 ⟨le_rfl, hT⟩)
      have hb := Real.sq_sqrt hη.le
      have ha0 := Real.sqrt_nonneg (E 0)
      have hb0 := Real.sqrt_nonneg η
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith [mul_nonneg ha0 hb0]⟩
    have hex := Real.exp_pos (K * t)
    calc Real.sqrt (E t) ≤ φ t := hs1
      _ ≤ Real.exp (K * t) * (φ 0 + K * ∫ σ in (0)..t, g σ) := hφt
      _ ≤ Real.exp (K * t) * (Real.sqrt (E 0) + Real.sqrt η + K * ∫ σ in (0)..t, g σ) := by
          gcongr
      _ = _ := by ring
  -- let `η → 0`
  by_contra hcon
  push Not at hcon
  set B := Real.exp (K * t) * (Real.sqrt (E 0) + K * ∫ τ in (0)..t, g τ)
  set d := Real.sqrt (E t) - B
  have hd : 0 < d := by simp only [d]; linarith
  have hex := Real.exp_pos (K * t)
  set η := (d / (2 * Real.exp (K * t))) ^ 2
  have hη : 0 < η := by positivity
  have h1 := key η hη
  have h2 : Real.sqrt η = d / (2 * Real.exp (K * t)) := Real.sqrt_sq (by positivity)
  rw [h2] at h1
  have h3 : Real.exp (K * t) * (d / (2 * Real.exp (K * t))) = d / 2 := by
    field_simp
  rw [h3] at h1
  simp only [d] at h1
  linarith

end

end RenewalGeometry.ODECutoff
