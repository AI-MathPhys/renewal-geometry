/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Scaled source control of physical stationarity
  (`prop:source-bound`, Einstein–SM action closure)

The positive source space with Gram `G_h` is rendered as a real
inner-product space `W` (its inner product is the `G_h` metric, so
`‖w‖ = ‖w‖_{G_h}`); a finite action covector `a_h` is a continuous
linear functional `a : W →L[ℝ] ℝ`, whose operator norm is the dual
norm `‖a_h‖_{G_h^{-1}}` (equivalently the `G_h`-norm of its Riesz
representative, `source_bound_riesz`).  The test space `V` carries
the `C^{r_0}` norm, `vh : V → W` is the source lift `v_h`, and
`Φ v = D𝒮_h(z_h^d)[𝓘_h v]` is the finite first variation.

* `stationarityDefect Φ` — `ε_h(K) = sup_{‖v‖ ≤ 1} |D𝒮_h[𝓘_h v]|`
  (`eq:stationarity`);
* `source_bound_pointwise` — `|Φ v| ≤ (L_h √R_h + e_h) ‖v‖`;
* `source_bound` — `ε_h(K) ≤ L_h √R_h + e_h` under
  `‖a_h‖²_{G_h^{-1}} ≤ R_h`, `‖v_h(v)‖_{G_h} ≤ L_h ‖v‖` and the
  identification error `|D𝒮_h[𝓘_h v] - a_h[v_h(v)]| ≤ e_h ‖v‖`;
* `source_bound_riesz` — the same with the covector given by its
  Riesz representative `α` and `‖α‖_{G_h}² ≤ R_h`;
* `source_bound_tendsto` — the "in particular" clause: the sufficient
  vanishing condition `L_h √R_h + e_h → 0` forces `ε_h(K) → 0`.

Scoped hypotheses disclosed: the constants `L_h, e_h` are taken
nonnegative (as bound constants they are).
-/

open scoped InnerProductSpace

namespace RenewalGeometry

/-- `eq:stationarity`: the physical common-action stationarity defect
`ε_h(K) = sup_{‖v‖ ≤ 1} |Φ v|` with `Φ v = D𝒮_h(z_h^d)[𝓘_h v]`. -/
noncomputable def stationarityDefect {V : Type*} [NormedAddCommGroup V]
    (Φ : V → ℝ) : ℝ :=
  ⨆ v : {v : V // ‖v‖ ≤ 1}, |Φ v.1|

/-- The defect is nonnegative as soon as the unit-ball values are
bounded (the value at `v = 0` is `|Φ 0| ≥ 0`). -/
theorem stationarityDefect_nonneg_of_bound {V : Type*} [NormedAddCommGroup V]
    (Φ : V → ℝ) (C : ℝ) (hC : ∀ v : V, ‖v‖ ≤ 1 → |Φ v| ≤ C) :
    0 ≤ stationarityDefect Φ := by
  unfold stationarityDefect
  have hbdd : BddAbove (Set.range fun v : {v : V // ‖v‖ ≤ 1} => |Φ v.1|) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact hC v.1 v.2
  exact le_ciSup_of_le hbdd ⟨0, by simp⟩ (abs_nonneg _)

/-- `prop:source-bound` (pointwise form): Cauchy–Schwarz in the `G_h`
metric, the lift bound and the identification error give
`|D𝒮_h[𝓘_h v]| ≤ (L_h √R_h + e_h) ‖v‖`. -/
theorem source_bound_pointwise {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (a : W →L[ℝ] ℝ) (vh : V → W) (Φ : V → ℝ) (R L e : ℝ)
    (hR : ‖a‖ ^ 2 ≤ R)
    (hlift : ∀ v, ‖vh v‖ ≤ L * ‖v‖)
    (hident : ∀ v, |Φ v - a (vh v)| ≤ e * ‖v‖) (v : V) :
    |Φ v| ≤ (L * Real.sqrt R + e) * ‖v‖ := by
  have hRnn : 0 ≤ R := le_trans (sq_nonneg _) hR
  have hnorm : ‖a‖ ≤ Real.sqrt R := (Real.le_sqrt (norm_nonneg _) hRnn).2 hR
  have hcs : |a (vh v)| ≤ ‖a‖ * ‖vh v‖ := by
    rw [← Real.norm_eq_abs]
    exact a.le_opNorm _
  calc |Φ v| = |(Φ v - a (vh v)) + a (vh v)| := by rw [sub_add_cancel]
    _ ≤ |Φ v - a (vh v)| + |a (vh v)| := by
        simpa only [Real.norm_eq_abs] using
          norm_add_le (Φ v - a (vh v)) (a (vh v))
    _ ≤ e * ‖v‖ + ‖a‖ * ‖vh v‖ := add_le_add (hident v) hcs
    _ ≤ e * ‖v‖ + Real.sqrt R * (L * ‖v‖) :=
        add_le_add le_rfl
          (mul_le_mul hnorm (hlift v) (norm_nonneg _) (Real.sqrt_nonneg _))
    _ = (L * Real.sqrt R + e) * ‖v‖ := by ring

/-- `prop:source-bound`: if `‖a_h‖²_{G_h^{-1}} ≤ R_h`,
`‖v_h(v)‖_{G_h} ≤ L_h ‖v‖_{C^{r_0}}` and
`|D𝒮_h[𝓘_h v] - a_h[v_h(v)]| ≤ e_h ‖v‖_{C^{r_0}}`, then
`ε_h(K) ≤ L_h √R_h + e_h`. -/
theorem source_bound {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (a : W →L[ℝ] ℝ) (vh : V → W) (Φ : V → ℝ) (R L e : ℝ)
    (hR : ‖a‖ ^ 2 ≤ R) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hlift : ∀ v, ‖vh v‖ ≤ L * ‖v‖)
    (hident : ∀ v, |Φ v - a (vh v)| ≤ e * ‖v‖) :
    stationarityDefect Φ ≤ L * Real.sqrt R + e := by
  unfold stationarityDefect
  have : Nonempty {v : V // ‖v‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  apply ciSup_le
  intro v
  have hC : 0 ≤ L * Real.sqrt R + e :=
    add_nonneg (mul_nonneg hL (Real.sqrt_nonneg _)) he
  calc |Φ v.1| ≤ (L * Real.sqrt R + e) * ‖v.1‖ :=
        source_bound_pointwise a vh Φ R L e hR hlift hident v.1
    _ ≤ (L * Real.sqrt R + e) * 1 := mul_le_mul_of_nonneg_left v.2 hC
    _ = L * Real.sqrt R + e := mul_one _

/-- `prop:source-bound` with the covector written through its Riesz
representative `α ∈ W`: `a_h[w] = ⟪α, w⟫_{G_h}` and
`‖a_h‖²_{G_h^{-1}} = ‖α‖²_{G_h} ≤ R_h`. -/
theorem source_bound_riesz {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (α : W) (vh : V → W) (Φ : V → ℝ) (R L e : ℝ)
    (hR : ‖α‖ ^ 2 ≤ R) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hlift : ∀ v, ‖vh v‖ ≤ L * ‖v‖)
    (hident : ∀ v, |Φ v - ⟪α, vh v⟫_ℝ| ≤ e * ‖v‖) :
    stationarityDefect Φ ≤ L * Real.sqrt R + e := by
  refine source_bound (innerSL ℝ α) vh Φ R L e ?_ hL he hlift ?_
  · rw [innerSL_apply_norm]
    exact hR
  · intro v
    simpa [innerSL_apply_apply] using hident v

/-- `prop:source-bound` ("in particular"): along a regulator sequence,
the sufficient vanishing condition `L_h √R_h + e_h → 0` forces
physical common-action stationarity `ε_h(K) → 0`. -/
theorem source_bound_tendsto {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (a : ℕ → W →L[ℝ] ℝ) (vh : ℕ → V → W) (Φ : ℕ → V → ℝ)
    (R L e : ℕ → ℝ)
    (hR : ∀ n, ‖a n‖ ^ 2 ≤ R n) (hL : ∀ n, 0 ≤ L n) (he : ∀ n, 0 ≤ e n)
    (hlift : ∀ n v, ‖vh n v‖ ≤ L n * ‖v‖)
    (hident : ∀ n v, |Φ n v - a n (vh n v)| ≤ e n * ‖v‖)
    (hvan : Filter.Tendsto (fun n => L n * Real.sqrt (R n) + e n)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => stationarityDefect (Φ n)) Filter.atTop (nhds 0) := by
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hvan
  · refine stationarityDefect_nonneg_of_bound (Φ n)
      (L n * Real.sqrt (R n) + e n) (fun v hv => ?_)
    have hC : 0 ≤ L n * Real.sqrt (R n) + e n :=
      add_nonneg (mul_nonneg (hL n) (Real.sqrt_nonneg _)) (he n)
    calc |Φ n v| ≤ (L n * Real.sqrt (R n) + e n) * ‖v‖ :=
          source_bound_pointwise (a n) (vh n) (Φ n) (R n) (L n) (e n)
            (hR n) (hlift n) (hident n) v
      _ ≤ (L n * Real.sqrt (R n) + e n) * 1 := mul_le_mul_of_nonneg_left hv hC
      _ = _ := mul_one _
  · exact source_bound (a n) (vh n) (Φ n) (R n) (L n) (e n)
      (hR n) (hL n) (he n) (hlift n) (hident n)

end RenewalGeometry
