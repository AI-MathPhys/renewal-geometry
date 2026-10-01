/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterForcedEnergy

/-!
# The lower-order difference estimate of the open writer (`eq:supp-open-difference`)

`cor:supp-open-lifespan`, third clause.  Two top-bounded forced records `X = (q, v)`,
`Y = (p, w)` (`q_t = v`, `v_t = V_{0,h}(q, v) + f`, `p_t = w`, `w_t = V_{0,h}(p, w) + f̃`, both in
the top chart `‖·‖_{X^s_h} ≤ δ` on `[0, T]`) satisfy, for `3 ≤ r ≤ s - 1`,
`‖X(t) - Y(t)‖_{X^r_h} ≤ C e^{K T} (‖X(0) - Y(0)‖_{X^r_h} + ∫_0^t ‖f - f̃‖_{r,h})`
with `C, K` independent of the mesh.

* `accel_bound`: the writer acceleration is bounded in `H^{s-1}_h` by `K ‖X‖_{X^s_h}` on the
  chart (the bound used inside `static_bounds`, exported);
* `pointwise_chart`: the pointwise chart facts (`½ ≤ a ≤ 3/2`, `|c - δ| ≤ 1/18`,
  `|ȧ|, |ċ| ≤ K₁ ‖X‖`);
* `genEnergy`, `genEnergy_bounds`: the quadratic energy `eq:supp-open-energy` of arbitrary data
  `(Q, V)` with the shifted coefficients of a fixed record, uniformly equivalent to
  `‖(Q, V)‖²_{X^r_h}` (`¼` and `8`);
* `diffSource_eq`: the exact difference row (`eq:supp-open-difference-source`): with the
  coefficients of `q`, the source is
  `𝖦(q,v) - 𝖦(p,w) - (a(q) - a(p)) V_{0,h}(p,w) + Σ D_i⁻((c(q) - c(p)) D_j⁺ p) - 𝖪_{b(q)-b(p)} w
   + a(q)(f - f̃)`;
* `diff_static_bound`: the rate of the difference energy is `≤ K (‖δX‖² + ‖δX‖ ‖f - f̃‖_{r,h})`;
* `sqrt_gronwall`: the scalar comparison `E' ≤ K E + K √E g ⇒
  √E(t) ≤ e^{Kt/2}(√E(0) + (K/2) ∫_0^t g)`;
* `open_writer_difference` (**`eq:supp-open-difference`**).
-/

open Set Metric Filter Topology Finset MeasureTheory
open scoped NNReal BigOperators

namespace RenewalGeometry.OpenWriterLifespan

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterEnergyEstimate

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

attribute [local irreducible] harmA harmB harmC compensatorMap

/-! ### Pointwise chart and the acceleration bound -/

/-- The pointwise chart: on a small ball of the top norm, `½ ≤ a ≤ 3/2`, `|c^{ij} - δ^{ij}| ≤ 1/18`,
the coefficients are differentiable and `|ȧ|, |ċ^{ij}| ≤ K₁ ‖X‖_{X^s_h}`. -/
theorem pointwise_chart (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ > 0, ∃ K₁ ≥ 0, ∀ (N : ℕ) [NeZero N] (q v : Grid N → MetricRec), IsSymRec q → IsSymRec v →
      Xnorm s q v ≤ δ →
      (∀ x, 1 / 2 ≤ aArr q x ∧ aArr q x ≤ 3 / 2) ∧
      (∀ x i j, |cArr q i j x - (if i = j then 1 else 0)| ≤ 1 / 18) ∧
      (∀ x, |adot q v x| ≤ K₁ * Xnorm s q v) ∧
      (∀ x i j, |cdot q v i j x| ≤ K₁ * Xnorm s q v) ∧
      (∀ x, DifferentiableAt ℝ harmA (minkowski + q x)) ∧
      (∀ x i j, DifferentiableAt ℝ (harmC i j) (minkowski + q x)) := by
  obtain ⟨ε, hε, M, hM, hchart⟩ := exists_chart
  have hL := supConst_nonneg
  refine ⟨ε / (2 * (supConst + 1)), by positivity, M * supConst, by positivity,
    fun N _ q v hq hv hX => ?_⟩
  have hqy : ∀ y, ‖q y‖ < ε := by
    intro y
    have h1 := norm_q_le s (by omega) hq v y
    have h2 : supConst * Xnorm s q v ≤ supConst * (ε / (2 * (supConst + 1))) :=
      mul_le_mul_of_nonneg_left hX hL
    have h3 : supConst * (ε / (2 * (supConst + 1))) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hch : ∀ y, _ := fun y => hchart (minkowski + q y) (by rw [add_sub_cancel_left]; exact hqy y)
  have hvy : ∀ y, ‖v y‖ ≤ supConst * Xnorm s q v := fun y => norm_v_le s (by omega) q hv y
  refine ⟨fun x => ?_, fun x i j => ((hch x).2 i j).2.2, fun x => ?_, fun x i j => ?_,
    fun x => (hch x).1.1, fun x i j => ((hch x).2 i j).1⟩
  · have := (hch x).1.2.2; simp only [aArr]; rw [abs_le] at this; constructor <;> linarith
  · have h1 := (fderiv ℝ harmA (minkowski + q x)).le_opNorm (v x)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    calc ‖fderiv ℝ harmA (minkowski + q x)‖ * ‖v x‖ ≤ M * (supConst * Xnorm s q v) :=
          mul_le_mul (hch x).1.2.1 (hvy x) (norm_nonneg _) hM
      _ = M * supConst * Xnorm s q v := by ring
  · have h1 := (fderiv ℝ (harmC i j) (minkowski + q x)).le_opNorm (v x)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    calc ‖fderiv ℝ (harmC i j) (minkowski + q x)‖ * ‖v x‖ ≤ M * (supConst * Xnorm s q v) :=
          mul_le_mul ((hch x).2 i j).2.1 (hvy x) (norm_nonneg _) hM
      _ = M * supConst * Xnorm s q v := by ring

/-- **The acceleration bound** (`‖q_tt‖_{s-1,h} ≤ K ‖X‖_{X^s_h}` on the chart), exported from
the proof of `static_bounds`. -/
theorem accel_bound (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (q v : Grid N → MetricRec), IsSymRec q → IsSymRec v →
      Xnorm s q v ≤ δ → ∀ μ ν, PeriodicGridSobolev.sobNorm (s - 1)
        (cx (comp (harmonicWriterAcceleration q v) μ ν)) ≤ K * Xnorm s q v := by
  open PeriodicGridSobolev.Moser in
  obtain ⟨δ0, hδ0, K₁, hK₁, hpc⟩ := pointwise_chart s hs
  obtain ⟨δ1, hδ1, C1, hC1, hm1⟩ := moser_coefficients (s - 1) (by omega)
  obtain ⟨δ3, hδ3, C3, hC3, hm3⟩ := moser_coefficients (s + 1) (by omega)
  obtain ⟨δG, hδG, CG, hCG, hmG⟩ := moser_compensator s (by omega)
  set As := algConst s
  set As1 := algConst (s - 1)
  set KG : ℝ := CG * 6400
  set K2 : ℝ := (As1 + 1) * (9 * (As + 1) + 3 * As1 + 3 * As + KG)
  set Cs : ℝ := C1 + C3 + 1
  have hCs : 0 < Cs := by positivity
  set δ : ℝ := min (min δ0 1) (min (min (δ1 / 16) (δ3 / 16)) (min (δG / 80) (1 / (16 * Cs))))
  have hδpos : 0 < δ := by positivity
  have hAs := algConst_pos s
  have hAs1 := algConst_pos (s - 1)
  have hKG : 0 ≤ KG := by positivity
  refine ⟨δ, hδpos, K2, by positivity, fun N _ q v hq hv hX μ ν => ?_⟩
  set X := Xnorm s q v
  have hX0 : 0 ≤ X := Xnorm_nonneg s q v
  have hδ0' : δ ≤ δ0 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1' : δ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδd1 : δ ≤ δ1 / 16 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδd3 : δ ≤ δ3 / 16 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδdG : δ ≤ δG / 80 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδCs : δ ≤ 1 / (16 * Cs) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hX1 : X ≤ 1 := hX.trans hδ1'
  have hXs : 16 * Cs * X ≤ 1 := by
    have := hX.trans hδCs
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hC1X : C1 * (16 * X) ≤ 1 := by nlinarith
  have hC3X : C3 * (16 * X) ≤ 1 := by nlinarith
  obtain ⟨ha, -, -, -, -, -⟩ := hpc N q v hq hv (hX.trans hδ0')
  have ha_ne : ∀ x, aArr q x ≠ 0 := fun x => by have := (ha x).1; positivity
  have hcs1 : PeriodicGridSobolev.Moser.coordSum (s - 1) bM q ≤ 16 * X :=
    coordSum_bM_q_le s hq v (by omega)
  have hcs3 : PeriodicGridSobolev.Moser.coordSum (s + 1) bM q ≤ 16 * X :=
    coordSum_bM_q_le s hq v le_rfl
  have hM1 := hm1 N q (hcs1.trans (by linarith [hX.trans hδd1]))
  have hM3 := hm3 N q (hcs3.trans (by linarith [hX.trans hδd3]))
  have hcJ := coordSum_bJ_le s hq hv
  have hMG := hmG N (jetArr q v) (hcJ.trans (by linarith [hX.trans hδdG]))
  have hainv : PeriodicGridSobolev.sobNorm (s - 1)
      (cx (fun x => (harmA (minkowski + q x))⁻¹) - fun _ => (1 : ℂ)) ≤ C1 * (16 * X) :=
    hM1.2.1.trans (by gcongr)
  have hc_s1 : ∀ i j, PeriodicGridSobolev.sobNorm (s + 1) (cx (cArr q i j) -
      fun _ => ((if i = j then 1 else 0 : ℝ) : ℂ)) ≤ C3 * (16 * X) := fun i j =>
    (hM3.2.2.1 i j).trans (by gcongr)
  have hb_s1 : ∀ i, PeriodicGridSobolev.sobNorm (s + 1) (cx (bArr q i) - fun _ => (0 : ℂ)) ≤
      C3 * (16 * X) := fun i => (hM3.2.2.2 i).trans (by gcongr)
  have hG : PeriodicGridSobolev.sobNorm s (cx (comp (Garr q v) μ ν)) ≤ KG * X ^ 2 := by
    refine (hMG μ ν).trans ?_
    have := PeriodicGridSobolev.Moser.coordSum_nonneg s bJ (jetArr q v)
    calc CG * PeriodicGridSobolev.Moser.coordSum s bJ (jetArr q v) ^ 2 ≤ CG * (80 * X) ^ 2 := by
          gcongr
      _ = KG * X ^ 2 := by simp only [KG]; ring
  have hrw := writer_row_cx q v μ ν ha_ne
  have e : cx (comp (harmonicWriterAcceleration q v) μ ν) =
      cx (fun x => (harmA (minkowski + q x))⁻¹) *
        (cx (aArr q) * cx (comp (harmonicWriterAcceleration q v) μ ν)) := by
    funext x
    simp only [Pi.mul_apply, cx_apply]
    rw [← mul_assoc, ← Complex.ofReal_mul, show (harmA (minkowski + q x))⁻¹ * aArr q x = 1 from
      inv_mul_cancel₀ (ha_ne x), Complex.ofReal_one, one_mul]
  rw [e, hrw]
  refine (sobNorm_coef_mul_le (s - 1) (by omega) _ _ 1 (by simp)
    (hainv.trans (by nlinarith))).trans ?_
  have hR := rhs_bound s hs (cx (comp q μ ν)) (cx (comp v μ ν)) (cx (comp (Garr q v) μ ν))
    (fun i j => cx (cArr q i j)) (fun i => cx (bArr q i))
    (fun i j => ((if i = j then 1 else 0 : ℝ) : ℂ)) (fun i j => by split_ifs <;> simp) X KG
    (fun i j => (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
      ((hc_s1 i j).trans (by nlinarith)))
    (fun i => (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
      ((hb_s1 i).trans (by nlinarith)))
    (fun j => (PeriodicGridSobolev.CommutedRow.sobNorm_Dp_le s j _).trans
      (sobNorm_q_le s hq v μ ν le_rfl))
    (sobNorm_v_le s q hv μ ν le_rfl)
    (hG.trans (by
      have hXX : X ^ 2 ≤ X := by nlinarith
      exact mul_le_mul_of_nonneg_left hXX hKG))
  calc (As1 + 1) * PeriodicGridSobolev.sobNorm (s - 1) _ ≤ (As1 + 1) *
        ((9 * (As + 1) + 3 * As1 + 3 * As + KG) * X) := by gcongr
    _ = K2 * X := by simp only [K2]; ring

/-! ### The quadratic energy of arbitrary data -/

/-- The quadratic energy `eq:supp-open-energy` of data `(Q, V)` with shifted coefficient arrays
`S^α a`, `S^α c` (the coefficients of a fixed record). -/
def genEnergy (r : ℕ) (a : Grid N → ℝ) (c : Fin 3 → Fin 3 → Grid N → ℝ)
    (Q V : Grid N → MetricRec) : ℝ :=
  ∑ α ∈ PeriodicGridSobolev.multiIndices r,
    energy (SαR α a) (fun i j => SαR α (c i j))
      (fun κ : Upper => DαR α (comp Q κ.1.1 κ.1.2)) (fun κ : Upper => DαR α (comp V κ.1.1 κ.1.2))

theorem shiftedEnergy_eq_genEnergy (s : ℕ) (q v : Grid N → MetricRec) :
    shiftedEnergy s q v = genEnergy s (aArr q) (cArr q) q v := rfl

/-- **Uniform equivalence of the quadratic energy**: if `½ ≤ a ≤ 3/2` and `|c - δ| ≤ 1/18`
pointwise, then `¼ ‖(Q, V)‖²_{X^r_h} ≤ 𝓔 ≤ 8 ‖(Q, V)‖²_{X^r_h}` for all data. -/
theorem genEnergy_bounds (r : ℕ) (a : Grid N → ℝ) (c : Fin 3 → Fin 3 → Grid N → ℝ)
    (ha : ∀ x, 1 / 2 ≤ a x ∧ a x ≤ 3 / 2)
    (hc : ∀ x i j, |c i j x - (if i = j then 1 else 0)| ≤ 1 / 18) (Q V : Grid N → MetricRec) :
    Xsq r Q V / 4 ≤ genEnergy r a c Q V ∧ genEnergy r a c Q V ≤ 8 * Xsq r Q V := by
  have hN : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
  have hc' : ∀ x i j, |c i j x| ≤ 19 / 18 := fun x i j => by
    have h := hc x i j
    have : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    calc |c i j x| = |(c i j x - (if i = j then 1 else 0)) + (if i = j then 1 else 0)| := by ring_nf
      _ ≤ 1 / 18 + 1 := (abs_add_le _ _).trans (add_le_add h this)
      _ = 19 / 18 := by norm_num
  -- the per-level quantities
  set G : (Fin 3 → ℕ) → Upper → ℝ := fun α κ =>
    PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp V κ.1.1 κ.1.2))) +
      ∑ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
        (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))) +
      PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))
  have hG : ∀ α (κ : Upper), ((N : ℝ) ^ 3)⁻¹ * ∑ x, (DαR α (comp V κ.1.1 κ.1.2) x ^ 2 +
      ∑ i, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2 +
      DαR α (comp Q κ.1.1 κ.1.2) x ^ 2) = G α κ := by
    intro α κ
    have hv' : PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp V κ.1.1 κ.1.2))) =
        ((N : ℝ) ^ 3)⁻¹ * ∑ x, DαR α (comp V κ.1.1 κ.1.2) x ^ 2 := by
      rw [← cx_DαR, gridNormSq_cx]
    have hq' : PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2))) =
        ((N : ℝ) ^ 3)⁻¹ * ∑ x, DαR α (comp Q κ.1.1 κ.1.2) x ^ 2 := by
      rw [← cx_DαR, gridNormSq_cx]
    have hd' : ∀ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
        (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))) =
        ((N : ℝ) ^ 3)⁻¹ * ∑ x, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2 := by
      intro i; rw [← cx_DαR, ← cx_Dp, gridNormSq_cx]
    simp only [G, hv', hq', hd']
    rw [sum_add_distrib, sum_add_distrib, sum_comm (s := univ) (t := univ) (f := fun x i =>
      OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2), mul_add, mul_add,
      Finset.mul_sum (s := univ) (f := fun i => ∑ x,
        OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2)]
  have hlevel : ∀ α, (1 / 4) * ∑ κ : Upper, G α κ ≤
      energy (SαR α a) (fun i j => SαR α (c i j)) (fun κ : Upper => DαR α (comp Q κ.1.1 κ.1.2))
        (fun κ : Upper => DαR α (comp V κ.1.1 κ.1.2)) ∧
      energy (SαR α a) (fun i j => SαR α (c i j)) (fun κ : Upper => DαR α (comp Q κ.1.1 κ.1.2))
        (fun κ : Upper => DαR α (comp V κ.1.1 κ.1.2)) ≤ 2 * ∑ κ : Upper, G α κ := by
    intro α
    unfold energy
    have hpt : ∀ (κ : Upper) x,
        (1 / 2) * (DαR α (comp V κ.1.1 κ.1.2) x ^ 2 +
          ∑ i, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2 +
          DαR α (comp Q κ.1.1 κ.1.2) x ^ 2) ≤
        DαR α (comp V κ.1.1 κ.1.2) x * (SαR α a x * DαR α (comp V κ.1.1 κ.1.2) x) +
          ∑ i, ∑ j, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x *
            (SαR α (c i j) x * OpenWriterEnergy.Dp j (DαR α (comp Q κ.1.1 κ.1.2)) x) +
          DαR α (comp Q κ.1.1 κ.1.2) x ^ 2 ∧
        DαR α (comp V κ.1.1 κ.1.2) x * (SαR α a x * DαR α (comp V κ.1.1 κ.1.2) x) +
          ∑ i, ∑ j, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x *
            (SαR α (c i j) x * OpenWriterEnergy.Dp j (DαR α (comp Q κ.1.1 κ.1.2)) x) +
          DαR α (comp Q κ.1.1 κ.1.2) x ^ 2 ≤
        4 * (DαR α (comp V κ.1.1 κ.1.2) x ^ 2 +
          ∑ i, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2 +
          DαR α (comp Q κ.1.1 κ.1.2) x ^ 2) := by
      intro κ x
      have e : SαR α a x = a (x + svec α) := rfl
      have ha1 := (ha (x + svec α)).1
      have ha2 := (ha (x + svec α)).2
      have hv2 := sq_nonneg (DαR α (comp V κ.1.1 κ.1.2) x)
      have hq2 := sq_nonneg (DαR α (comp Q κ.1.1 κ.1.2) x)
      have hd2 : 0 ≤ ∑ i, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2 :=
        sum_nonneg fun _ _ => sq_nonneg _
      have hlo := quad_lower (fun i => OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x)
        (fun i j => SαR α (c i j) x) (fun i j => hc (x + svec α) i j)
      have hup := quad_upper (fun i => OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x)
        (fun i j => SαR α (c i j) x) (19 / 18) (fun i j => hc' (x + svec α) i j)
      rw [e]
      constructor
      · nlinarith
      · nlinarith
    constructor
    · calc (1 / 4) * ∑ κ : Upper, G α κ = ((N : ℝ) ^ 3)⁻¹ * (1 / 2) * ∑ κ : Upper, ∑ x,
            (1 / 2) * (DαR α (comp V κ.1.1 κ.1.2) x ^ 2 +
              ∑ i, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2 +
              DαR α (comp Q κ.1.1 κ.1.2) x ^ 2) := by
            rw [← sum_congr rfl fun κ _ => hG α κ, mul_sum, mul_sum]
            refine sum_congr rfl fun κ _ => ?_
            rw [← mul_sum]; ring
        _ ≤ _ := by
            gcongr with κ _ x _
            exact (hpt κ x).1
    · calc ((N : ℝ) ^ 3)⁻¹ * (1 / 2) * ∑ κ : Upper, ∑ x, _
          ≤ ((N : ℝ) ^ 3)⁻¹ * (1 / 2) * ∑ κ : Upper, ∑ x,
            4 * (DαR α (comp V κ.1.1 κ.1.2) x ^ 2 +
              ∑ i, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2 +
              DαR α (comp Q κ.1.1 κ.1.2) x ^ 2) := by
            gcongr with κ _ x _
            exact (hpt κ x).2
        _ = 2 * ∑ κ : Upper, G α κ := by
            rw [← sum_congr rfl fun κ _ => hG α κ, mul_sum, mul_sum]
            refine sum_congr rfl fun κ _ => ?_
            rw [← mul_sum]; ring
  -- summation over the multi-indices
  have hsum : ∑ α ∈ PeriodicGridSobolev.multiIndices r, ∑ κ : Upper, G α κ =
      ∑ κ : Upper, (PeriodicGridSobolev.sobSq r (cx (comp V κ.1.1 κ.1.2)) +
        ∑ α ∈ PeriodicGridSobolev.multiIndices r, ∑ i, PeriodicGridSobolev.gridNormSq
          (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))) +
        PeriodicGridSobolev.sobSq r (cx (comp Q κ.1.1 κ.1.2))) := by
    rw [sum_comm]
    refine sum_congr rfl fun κ _ => ?_
    simp only [G, sum_add_distrib, PeriodicGridSobolev.sobSq]
  constructor
  · calc Xsq r Q V / 4 ≤ (1 / 4) * ∑ α ∈ PeriodicGridSobolev.multiIndices r,
          ∑ κ : Upper, G α κ := by
          rw [hsum, Xsq, div_eq_mul_inv, mul_comm, show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun κ _ => ?_) (by norm_num)
          have hcnt := PeriodicGridSobolev.CommutedRow.sobSq_succ_le_shifted r
            (cx (comp Q κ.1.1 κ.1.2))
          have e2 : ∑ α ∈ PeriodicGridSobolev.multiIndices r,
              (PeriodicGridSobolev.gridNormSq
                (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2))) +
              ∑ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
                (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2))))) =
              ∑ α ∈ PeriodicGridSobolev.multiIndices r, ∑ i, PeriodicGridSobolev.gridNormSq
                (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))) +
              PeriodicGridSobolev.sobSq r (cx (comp Q κ.1.1 κ.1.2)) := by
            rw [sum_add_distrib, add_comm]; rfl
          linarith
      _ = ∑ α ∈ PeriodicGridSobolev.multiIndices r, (1 / 4) * ∑ κ : Upper, G α κ := by
          rw [mul_sum]
      _ ≤ genEnergy r a c Q V := sum_le_sum fun α _ => (hlevel α).1
  · calc genEnergy r a c Q V ≤ ∑ α ∈ PeriodicGridSobolev.multiIndices r,
          2 * ∑ κ : Upper, G α κ := sum_le_sum fun α _ => (hlevel α).2
      _ = 2 * ∑ κ : Upper, (PeriodicGridSobolev.sobSq r (cx (comp V κ.1.1 κ.1.2)) +
          ∑ α ∈ PeriodicGridSobolev.multiIndices r, ∑ i, PeriodicGridSobolev.gridNormSq
            (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))) +
          PeriodicGridSobolev.sobSq r (cx (comp Q κ.1.1 κ.1.2))) := by
          rw [← mul_sum, hsum]
      _ ≤ 2 * ∑ κ : Upper, (PeriodicGridSobolev.sobSq r (cx (comp V κ.1.1 κ.1.2)) +
          3 * PeriodicGridSobolev.sobSq (r + 1) (cx (comp Q κ.1.1 κ.1.2)) +
          PeriodicGridSobolev.sobSq (r + 1) (cx (comp Q κ.1.1 κ.1.2))) := by
          gcongr with κ _
          · exact sum_Dp_Dα_sq_le r _
          · exact PeriodicGridSobolev.sobSq_mono (by omega) _
      _ ≤ 8 * Xsq r Q V := by
          unfold Xsq
          rw [mul_sum, mul_sum]
          refine sum_le_sum fun κ _ => ?_
          have := PeriodicGridSobolev.sobSq_nonneg r (cx (comp V κ.1.1 κ.1.2))
          have := PeriodicGridSobolev.sobSq_nonneg (r + 1) (cx (comp Q κ.1.1 κ.1.2))
          linarith


/-! ### The difference row -/

/-- The acceleration difference `δv_t = (V_{0,h}(q, v) + f) - (V_{0,h}(p, w) + f̃)`. -/
def dAcc (q p v w f g : Grid N → MetricRec) : Grid N → MetricRec :=
  harmonicWriterAcceleration q v + f - (harmonicWriterAcceleration p w + g)

/-- The remainder of the commuted difference row with the shifted coefficients of `q`. -/
def Rdiff (α : Fin 3 → ℕ) (q p v w f g : Grid N → MetricRec) (μ ν : Fin 4) : Grid N → ℝ :=
  fun x => SαR α (aArr q) x * DαR α (comp (dAcc q p v w f g) μ ν) x
    - divArr (fun i j => SαR α (cArr q i j)) (DαR α (comp (q - p) μ ν)) x
    + skewArr (fun i => SαR α (bArr q i)) (DαR α (comp (v - w) μ ν)) x

/-- The exact rate of the difference energy. -/
def diffRate (r : ℕ) (q p v w f g : Grid N → MetricRec) : ℝ :=
  ∑ α ∈ PeriodicGridSobolev.multiIndices r, ((N : ℝ) ^ 3)⁻¹ * ∑ κ : Upper, ∑ x,
    ((1 / 2) * (DαR α (comp (v - w) κ.1.1 κ.1.2) x *
        (SαR α (adot q v) x * DαR α (comp (v - w) κ.1.1 κ.1.2) x)) +
      (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i (DαR α (comp (q - p) κ.1.1 κ.1.2)) x *
        (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j (DαR α (comp (q - p) κ.1.1 κ.1.2)) x) +
      DαR α (comp (q - p) κ.1.1 κ.1.2) x * DαR α (comp (v - w) κ.1.1 κ.1.2) x +
      DαR α (comp (v - w) κ.1.1 κ.1.2) x * Rdiff α q p v w f g κ.1.1 κ.1.2 x)

/-- **Exact identity for the difference energy** (`eq:supp-open-energy` for `(δq, δv)` with the
shifted coefficients of `q`). -/
theorem hasDerivAt_diffEnergy (r : ℕ) (q p v w f g : ℝ → Grid N → MetricRec) (t : ℝ)
    (hsym : IsSymRec (q t))
    (hq : ∀ x, HasDerivAt (fun τ => q τ x) (v t x) t)
    (hp : ∀ x, HasDerivAt (fun τ => p τ x) (w t x) t)
    (hv : ∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
      (harmonicWriterAcceleration (q t) (v t) x κ.1.1 κ.1.2 + f t x κ.1.1 κ.1.2) t)
    (hw : ∀ x (κ : Upper), HasDerivAt (fun τ => w τ x κ.1.1 κ.1.2)
      (harmonicWriterAcceleration (p t) (w t) x κ.1.1 κ.1.2 + g t x κ.1.1 κ.1.2) t)
    (hdA : ∀ x, DifferentiableAt ℝ harmA (minkowski + q t x))
    (hdC : ∀ x i j, DifferentiableAt ℝ (harmC i j) (minkowski + q t x)) :
    HasDerivAt (fun τ => genEnergy r (aArr (q τ)) (cArr (q τ)) (q τ - p τ) (v τ - w τ))
      (diffRate r (q t) (p t) (v t) (w t) (f t) (g t)) t := by
  unfold genEnergy diffRate
  refine HasDerivAt.fun_sum fun α _ => ?_
  have hg : ∀ y, HasDerivAt (fun τ => minkowski + q τ y) (v t y) t := fun y =>
    (hq y).const_add minkowski
  have hcomp : ∀ (μ ν : Fin 4) x, HasDerivAt (fun τ => comp (q τ - p τ) μ ν x)
      (comp (v t - w t) μ ν x) t := by
    intro μ ν x
    have h1 := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hq x) μ) ν
    have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hp x) μ) ν
    exact h1.sub h2
  refine hasDerivAt_energy (fun τ (κ : Upper) => DαR α (comp (q τ - p τ) κ.1.1 κ.1.2))
    (fun τ (κ : Upper) => DαR α (comp (v τ - w τ) κ.1.1 κ.1.2)) (fun τ => SαR α (aArr (q τ)))
    (fun τ i j => SαR α (cArr (q τ) i j)) (fun i => SαR α (bArr (q t) i))
    (fun κ => DαR α (comp (dAcc (q t) (p t) (v t) (w t) (f t) (g t)) κ.1.1 κ.1.2))
    (SαR α (adot (q t) (v t))) (fun i j => SαR α (cdot (q t) (v t) i j))
    (fun κ => Rdiff α (q t) (p t) (v t) (w t) (f t) (g t) κ.1.1 κ.1.2) t ?_ ?_ ?_ ?_ ?_ ?_
  · intro κ x
    exact hasDerivAt_DαR (fun y => hcomp κ.1.1 κ.1.2 y) α x
  · intro κ x
    refine hasDerivAt_DαR (u := fun τ => comp (v τ - w τ) κ.1.1 κ.1.2) (fun y => ?_) α x
    exact (hv y κ).sub (hw y κ)
  · intro x
    exact (hdA (x + svec α)).hasFDerivAt.comp_hasDerivAt t (hg (x + svec α))
  · intro i j x
    exact (hdC (x + svec α) i j).hasFDerivAt.comp_hasDerivAt t (hg (x + svec α))
  · intro i j x
    simp only [SαR, cArr]
    refine harmC_symm _ (fun μ ν => ?_) i j
    simp only [Pi.add_apply]
    rw [minkowski_symm, hsym]
  · intro κ x
    simp only [Rdiff]
    ring

/-- The complex coefficient-weighted divergence `Σ_{ij} D_i⁻(c^{ij} D_j⁺ Q)`. -/
def cDiv (c : Fin 3 → Fin 3 → PeriodicGridSobolev.Grid N → ℂ) (Q : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.Grid N → ℂ :=
  ∑ i, ∑ j, PeriodicGridSobolev.Dm i (c i j * PeriodicGridSobolev.Dp j Q)

/-- The complex skew transport `Σ_i (b^i D_i⁰ V + D_i⁰(b^i V))`. -/
def cSkew (b : Fin 3 → PeriodicGridSobolev.Grid N → ℂ) (V : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.Grid N → ℂ :=
  ∑ i, (b i * PeriodicGridSobolev.D0 i V + PeriodicGridSobolev.D0 i (b i * V))

theorem cDiv_sub_right (c : Fin 3 → Fin 3 → PeriodicGridSobolev.Grid N → ℂ) (Q P) :
    cDiv c (Q - P) = cDiv c Q - cDiv c P := by
  simp only [cDiv, map_sub, mul_sub, sum_sub_distrib]

theorem cDiv_sub_left (c c' : Fin 3 → Fin 3 → PeriodicGridSobolev.Grid N → ℂ) (P) :
    cDiv (fun i j => c i j - c' i j) P = cDiv c P - cDiv c' P := by
  simp only [cDiv, sub_mul, map_sub, sum_sub_distrib]

theorem cSkew_sub_right (b : Fin 3 → PeriodicGridSobolev.Grid N → ℂ) (V W) :
    cSkew b (V - W) = cSkew b V - cSkew b W := by
  simp only [cSkew, map_sub, mul_sub, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  abel

theorem cSkew_sub_left (b b' : Fin 3 → PeriodicGridSobolev.Grid N → ℂ) (W) :
    cSkew (fun i => b i - b' i) W = cSkew b W - cSkew b' W := by
  simp only [cSkew, sub_mul, map_sub, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  abel

/-- The complex source of the difference row, defined so that
`a(q) δv_t = Σ D_i⁻(c(q) D_j⁺ δq) - 𝖪_{b(q)} δv + 𝖦^δ`. -/
def diffSource (q p v w f g : Grid N → MetricRec) (μ ν : Fin 4) : PeriodicGridSobolev.Grid N → ℂ :=
  cx (aArr q) * cx (comp (dAcc q p v w f g) μ ν) -
    (cDiv (fun i j => cx (cArr q i j)) (cx (comp (q - p) μ ν)) -
      cSkew (fun i => cx (bArr q i)) (cx (comp (v - w) μ ν)))

theorem cx_comp_sub (u u' : Grid N → MetricRec) (μ ν : Fin 4) :
    cx (comp (u - u') μ ν) = cx (comp u μ ν) - cx (comp u' μ ν) := by
  funext x; simp [comp, cx]

theorem cx_comp_add (u u' : Grid N → MetricRec) (μ ν : Fin 4) :
    cx (comp (u + u') μ ν) = cx (comp u μ ν) + cx (comp u' μ ν) := by
  funext x; simp [comp, cx]

/-- **The difference source** (`eq:supp-open-difference-source` plus the force difference):
`𝖦^δ = 𝖦(q,v) - 𝖦(p,w) - (a(q) - a(p)) V_{0,h}(p,w) + Σ D_i⁻((c(q) - c(p)) D_j⁺ p)
 - 𝖪_{b(q) - b(p)} w + a(q)(f - f̃)`. -/
theorem diffSource_eq (q p v w f g : Grid N → MetricRec) (μ ν : Fin 4)
    (haq : ∀ x, aArr q x ≠ 0) (hap : ∀ x, aArr p x ≠ 0) :
    diffSource q p v w f g μ ν =
      (cx (comp (Garr q v) μ ν) - cx (comp (Garr p w) μ ν)) -
        (cx (aArr q) - cx (aArr p)) * cx (comp (harmonicWriterAcceleration p w) μ ν) +
        cDiv (fun i j => cx (cArr q i j) - cx (cArr p i j)) (cx (comp p μ ν)) -
        cSkew (fun i => cx (bArr q i) - cx (bArr p i)) (cx (comp w μ ν)) +
        cx (aArr q) * (cx (comp f μ ν) - cx (comp g μ ν)) := by
  have rq := writer_row_cx q v μ ν haq
  have rp := writer_row_cx p w μ ν hap
  have e1 : cx (comp (dAcc q p v w f g) μ ν) = cx (comp (harmonicWriterAcceleration q v) μ ν) +
      cx (comp f μ ν) - (cx (comp (harmonicWriterAcceleration p w) μ ν) + cx (comp g μ ν)) := by
    funext x; simp [dAcc, comp, cx]
  unfold diffSource
  rw [e1, cx_comp_sub, cx_comp_sub, cDiv_sub_right, cSkew_sub_right, cDiv_sub_left,
    cSkew_sub_left]
  simp only [cDiv, cSkew] at *
  linear_combination rq - rp

/-- The remainder of the commuted difference row is the explicit commutator remainder. -/
theorem cx_Rdiff (α : Fin 3 → ℕ) (q p v w f g : Grid N → MetricRec) (μ ν : Fin 4) :
    cx (Rdiff α q p v w f g μ ν) = PeriodicGridSobolev.CommutedRow.rowRem α (cx (aArr q))
      (cx (comp (dAcc q p v w f g) μ ν)) (cx (comp (v - w) μ ν)) (cx (comp (q - p) μ ν))
      (diffSource q p v w f g μ ν) (fun i j => cx (cArr q i j)) (fun i => cx (bArr q i)) := by
  have hrow0 : cx (aArr q) * cx (comp (dAcc q p v w f g) μ ν) =
      ∑ i, ∑ j, PeriodicGridSobolev.Dm i (cx (cArr q i j) *
        PeriodicGridSobolev.Dp j (cx (comp (q - p) μ ν))) -
      ∑ i, (cx (bArr q i) * PeriodicGridSobolev.D0 i (cx (comp (v - w) μ ν)) +
        PeriodicGridSobolev.D0 i (cx (bArr q i) * cx (comp (v - w) μ ν))) +
      diffSource q p v w f g μ ν := by
    unfold diffSource cDiv cSkew; abel
  have hrow := PeriodicGridSobolev.CommutedRow.commuted_row α _ _ _ _ _
    (fun i j => cx (cArr q i j)) (fun i => cx (bArr q i)) hrow0
  have e : Rdiff α q p v w f g μ ν = (fun x => SαR α (aArr q) x *
      DαR α (comp (dAcc q p v w f g) μ ν) x)
      - divArr (fun i j => SαR α (cArr q i j)) (DαR α (comp (q - p) μ ν))
      + skewArr (fun i => SαR α (bArr q i)) (DαR α (comp (v - w) μ ν)) := by
    funext x; simp [Rdiff]
  rw [e, cx_add, cx_sub, cx_fun_mul, cx_divArr, cx_skewArr, cx_SαR, cx_DαR]
  simp only [cx_SαR, cx_DαR]
  rw [hrow]
  abel

/-! ### Lipschitz Moser estimates for the chart coefficients -/

/-- Uniform Lipschitz Moser bounds for `a`, `c^{ij}`, `b^i` at order `r`. -/
theorem moser_lipschitz_coefficients (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (q p : Grid N → MetricRec),
      PeriodicGridSobolev.Moser.coordSum r bM q ≤ δ →
      PeriodicGridSobolev.Moser.coordSum r bM p ≤ δ →
      PeriodicGridSobolev.sobNorm r (cx (aArr q) - cx (aArr p)) ≤
          C * PeriodicGridSobolev.Moser.coordSum r bM (q - p) ∧
      (∀ i j, PeriodicGridSobolev.sobNorm r (cx (cArr q i j) - cx (cArr p i j)) ≤
          C * PeriodicGridSobolev.Moser.coordSum r bM (q - p)) ∧
      ∀ i, PeriodicGridSobolev.sobNorm r (cx (bArr q i) - cx (bArr p i)) ≤
          C * PeriodicGridSobolev.Moser.coordSum r bM (q - p) := by
  let F : Fin 1 ⊕ (Fin 3 × Fin 3 ⊕ Fin 3) → MetricRec → ℝ
    | Sum.inl _ => harmA
    | Sum.inr (Sum.inl ij) => harmC ij.1 ij.2
    | Sum.inr (Sum.inr i) => harmB i
  have hF : ∀ k, AnalyticAt ℝ (F k) minkowski := by
    rintro (k | ij | i)
    · exact analyticAt_harmA
    · exact analyticAt_harmC ij.1 ij.2
    · exact analyticAt_harmB i
  obtain ⟨δ, hδ, C, hC, h⟩ := uniformize (fun k δ C => ∀ (N : ℕ) [NeZero N]
      (q p : Grid N → MetricRec), PeriodicGridSobolev.Moser.coordSum r bM q ≤ δ →
      PeriodicGridSobolev.Moser.coordSum r bM p ≤ δ →
      PeriodicGridSobolev.sobNorm r
        (fun x => ((F k (minkowski + q x) - F k (minkowski + p x) : ℝ) : ℂ))
        ≤ C * PeriodicGridSobolev.Moser.coordSum r bM (q - p))
    (fun k δ δ' C C' _ hδ' hC' hP N _ q p hq hp => (hP N q p (hq.trans hδ') (hp.trans hδ')).trans
      (by gcongr; exact PeriodicGridSobolev.Moser.coordSum_nonneg _ _ _))
    (fun k => by
      obtain ⟨pp, R, hp⟩ := hF k
      exact PeriodicGridSobolev.Moser.moser_lipschitz r hr bM hp)
  refine ⟨δ, hδ, C, hC, fun N _ q p hq hp => ⟨?_, fun i j => ?_, fun i => ?_⟩⟩
  · have := h (Sum.inl 0) N q p hq hp
    convert this using 2
    funext x; simp [cx, aArr, F]
  · have := h (Sum.inr (Sum.inl (i, j))) N q p hq hp
    convert this using 2
    funext x; simp [cx, cArr, F]
  · have := h (Sum.inr (Sum.inr i)) N q p hq hp
    convert this using 2
    funext x; simp [cx, bArr, F]

/-- Uniform Lipschitz Moser bound for the compensator at order `r`. -/
theorem moser_lipschitz_compensator (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (u u' : Grid N → JetSpace),
      PeriodicGridSobolev.Moser.coordSum r bJ u ≤ δ →
      PeriodicGridSobolev.Moser.coordSum r bJ u' ≤ δ → ∀ μ ν : Fin 4,
      PeriodicGridSobolev.sobNorm r (cx (fun x => compensatorMap (u x) μ ν) -
        cx (fun x => compensatorMap (u' x) μ ν)) ≤
        C * PeriodicGridSobolev.Moser.coordSum r bJ (u - u') := by
  obtain ⟨δ, hδ, C, hC, h⟩ := uniformize (ι := Fin 4 × Fin 4) (fun k δ C => ∀ (N : ℕ) [NeZero N]
      (u u' : Grid N → JetSpace), PeriodicGridSobolev.Moser.coordSum r bJ u ≤ δ →
      PeriodicGridSobolev.Moser.coordSum r bJ u' ≤ δ →
      PeriodicGridSobolev.sobNorm r (fun x =>
        ((compensatorMap (0 + u x) k.1 k.2 - compensatorMap (0 + u' x) k.1 k.2 : ℝ) : ℂ))
        ≤ C * PeriodicGridSobolev.Moser.coordSum r bJ (u - u'))
    (fun k δ δ' C C' _ hδ' hC' hP N _ u u' hu hu' =>
      (hP N u u' (hu.trans hδ') (hu'.trans hδ')).trans
      (by gcongr; exact PeriodicGridSobolev.Moser.coordSum_nonneg _ _ _))
    (fun k => by
      obtain ⟨pp, R, hp⟩ := analyticAt_compensatorMap k.1 k.2 0
      exact PeriodicGridSobolev.Moser.moser_lipschitz r hr bJ (A := fun w : JetSpace =>
        compensatorMap w k.1 k.2) (c := ((0, 0) : JetSpace)) hp)
  refine ⟨δ, hδ, C, hC, fun N _ u u' hu hu' μ ν => ?_⟩
  have := h (μ, ν) N u u' hu hu'
  convert this using 2
  funext x; simp [cx]

theorem jetArr_sub (q p v w : Grid N → MetricRec) :
    jetArr q v - jetArr p w = jetArr (q - p) (v - w) := by
  funext x
  simp only [jetArr, Pi.sub_apply, Prod.mk_sub_mk, fwd]
  congr 2
  funext i
  simp only [Pi.sub_apply, smul_sub]
  abel

/-- Continuity of the force norm. -/
theorem continuous_Fnorm (r : ℕ) : Continuous (Fnorm (N := N) r) := by
  have hc : ∀ μ ν : Fin 4,
      Continuous fun f : Grid N → MetricRec => PeriodicGridSobolev.sobSq r (cx (comp f μ ν)) := by
    intro μ ν
    have h1 : Continuous fun f : Grid N → MetricRec => cx (comp f μ ν) :=
      continuous_pi fun x => Complex.continuous_ofReal.comp
        ((continuous_apply ν).comp ((continuous_apply μ).comp (continuous_apply x)))
    simp_rw [← PeriodicGridSobolev.sobNorm_sq]
    exact ((PeriodicGridSobolev.Moser.continuous_sobNorm r).comp h1).pow 2
  unfold Fnorm
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun κ _ => hc _ _)

/-! ### The static difference bound -/

theorem isSymRec_sub {u u' : Grid N → MetricRec} (hu : IsSymRec u) (hu' : IsSymRec u') :
    IsSymRec (u - u') := fun x μ ν => by simp only [Pi.sub_apply, hu x μ ν, hu' x μ ν]

set_option maxHeartbeats 4000000 in
/-- **Static bound of the difference rate**: for `3 ≤ r` and `r + 1 ≤ s` there are `δ > 0`,
`K ≥ 0`, independent of the mesh, such that for two symmetric records in the top chart
`‖(q, v)‖_{X^s_h}, ‖(p, w)‖_{X^s_h} ≤ δ` and arbitrary forces `f, f̃`,
`diffRate ≤ K ‖δX‖²_{X^r_h} + K ‖δX‖_{X^r_h} ‖f - f̃‖_{r,h}`. -/
theorem diff_static_bound (s r : ℕ) (hr : 3 ≤ r) (hrs : r + 1 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (q p v w f g : Grid N → MetricRec),
      IsSymRec q → IsSymRec p → IsSymRec v → IsSymRec w → Xnorm s q v ≤ δ → Xnorm s p w ≤ δ →
      diffRate r q p v w f g ≤
        K * Xsq r (q - p) (v - w) + K * Xnorm r (q - p) (v - w) * Fnorm r (f - g) := by
  open PeriodicGridSobolev PeriodicGridSobolev.Moser PeriodicGridSobolev.CommutedRow in
  have hs : 3 ≤ s := by omega
  obtain ⟨δ0, hδ0, K₁, hK₁, hpc⟩ := pointwise_chart s hs
  obtain ⟨δA, hδA, KA, hKA, hacc⟩ := accel_bound s hs
  obtain ⟨δa, hδa, Ca, hCa, hma⟩ := moser_coefficients r (by omega)
  obtain ⟨δa1, hδa1, Ca1, hCa1, hma1⟩ := moser_coefficients (r - 1) (by omega)
  obtain ⟨δc, hδc, Cc, hCc, hmc⟩ := moser_coefficients (r + 1) (by omega)
  obtain ⟨δl, hδl, Cl, hCl, hml⟩ := moser_lipschitz_coefficients r (by omega)
  obtain ⟨δl1, hδl1, Cl1, hCl1, hml1⟩ := moser_lipschitz_coefficients (r + 1) (by omega)
  obtain ⟨δG, hδG, CG, hCG, hmG⟩ := moser_lipschitz_compensator r (by omega)
  obtain ⟨Cr, hCr, hrow⟩ := rowRem_norm_le r hr
  set Cs : ℝ := Ca + Ca1 + Cc + 1
  have hCs : 0 < Cs := by positivity
  set δ : ℝ := min (min (min δ0 δA) (min 1 (1 / (16 * Cs))))
    (min (min (δa / 16) (δa1 / 16)) (min (min (δc / 16) (δl / 16)) (min (δl1 / 16) (δG / 80))))
  have hδ : 0 < δ := by positivity
  set Ar := algConst r
  set Ar1 := algConst (r - 1)
  set Ar2 := algConst (r + 1)
  have hAr := algConst_pos r
  have hAr1 := algConst_pos (r - 1)
  have hAr2 := algConst_pos (r + 1)
  set CGt : ℝ := CG * 80 + Ar * (Cl * 16) * KA + 9 * (Ar2 * (Cl1 * 16)) +
    3 * ((Ar + Ar2) * (Cl1 * 16)) + (Ar + 1)
  have hCGt : 0 ≤ CGt := by positivity
  set CV : ℝ := (Ar1 + 1) * (9 * (Ar + 1) + 3 * Ar1 + 3 * Ar + CGt)
  have hCV : 0 ≤ CV := by positivity
  set CR : ℝ := Cr * (CV + 12) + CGt
  have hCR : 0 ≤ CR := by positivity
  set cM : ℝ := ((multiIndices r).card : ℝ)
  set cU : ℝ := (Fintype.card Upper : ℝ)
  set K : ℝ := cM * cU * (5 * K₁ + 1 + CR) + cM * cU * CR
  refine ⟨δ, hδ, K, by positivity, fun N _ q p v w f g hq hp hv hw hXq hXp => ?_⟩
  -- bookkeeping of the radii
  set Xq := Xnorm s q v
  set Xp := Xnorm s p w
  have hXq0 : 0 ≤ Xq := Xnorm_nonneg _ _ _
  have hXp0 : 0 ≤ Xp := Xnorm_nonneg _ _ _
  have hδ0' : δ ≤ δ0 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδA' : δ ≤ δA := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδCs : δ ≤ 1 / (16 * Cs) :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδa' : δ ≤ δa / 16 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδa1' : δ ≤ δa1 / 16 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδc' : δ ≤ δc / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_left _ _).trans (min_le_left _ _)))
  have hδl' : δ ≤ δl / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_left _ _).trans (min_le_right _ _)))
  have hδl1' : δ ≤ δl1 / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδG' : δ ≤ δG / 80 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hXq1 : Xq ≤ 1 := hXq.trans hδ1
  have hXp1 : Xp ≤ 1 := hXp.trans hδ1
  have hsmall : 16 * Cs * Xq ≤ 1 := by
    have := hXq.trans hδCs
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hCsX : ∀ C', 0 ≤ C' → C' ≤ Cs → C' * (16 * Xq) ≤ 1 := fun C' _ hC' =>
    calc C' * (16 * Xq) ≤ Cs * (16 * Xq) := mul_le_mul_of_nonneg_right hC' (by positivity)
      _ = 16 * Cs * Xq := by ring
      _ ≤ 1 := hsmall
  have hCaX : Ca * (16 * Xq) ≤ 1 := hCsX Ca hCa (by simp only [Cs]; linarith)
  have hCa1X : Ca1 * (16 * Xq) ≤ 1 := hCsX Ca1 hCa1 (by simp only [Cs]; linarith)
  have hCcX : Cc * (16 * Xq) ≤ 1 := hCsX Cc hCc (by simp only [Cs]; linarith)
  -- the pointwise chart of `q` and `p`
  obtain ⟨ha, hc, hadot, hcdot, -, -⟩ := hpc N q v hq hv (hXq.trans hδ0')
  obtain ⟨hap, -, -, -, -, -⟩ := hpc N p w hp hw (hXp.trans hδ0')
  have haq_ne : ∀ x, aArr q x ≠ 0 := fun x => by have := (ha x).1; positivity
  have hap_ne : ∀ x, aArr p x ≠ 0 := fun x => by have := (hap x).1; positivity
  -- coefficient bounds for `q`
  have hcsq_r : coordSum r bM q ≤ 16 * Xq := coordSum_bM_q_le s hq v (by omega)
  have hcsq_r1 : coordSum (r - 1) bM q ≤ 16 * Xq := coordSum_bM_q_le s hq v (by omega)
  have hcsq_r2 : coordSum (r + 1) bM q ≤ 16 * Xq := coordSum_bM_q_le s hq v (by omega)
  have hMa := hma N q (hcsq_r.trans (by linarith [hXq.trans hδa']))
  have hMa1 := hma1 N q (hcsq_r1.trans (by linarith [hXq.trans hδa1']))
  have hMc := hmc N q (hcsq_r2.trans (by linarith [hXq.trans hδc']))
  have ha_r : sobNorm r (cx (aArr q) - fun _ => (1 : ℂ)) ≤ 1 :=
    hMa.1.trans ((mul_le_mul_of_nonneg_left hcsq_r hCa).trans hCaX)
  have hainv : sobNorm (r - 1) (cx (fun x => (harmA (minkowski + q x))⁻¹) -
      fun _ => (1 : ℂ)) ≤ 1 :=
    hMa1.2.1.trans ((mul_le_mul_of_nonneg_left hcsq_r1 hCa1).trans hCa1X)
  have hc_r2 : ∀ i j, sobNorm (r + 1) (cx (cArr q i j) -
      fun _ => ((if i = j then 1 else 0 : ℝ) : ℂ)) ≤ 1 := fun i j =>
    (hMc.2.2.1 i j).trans ((mul_le_mul_of_nonneg_left hcsq_r2 hCc).trans hCcX)
  have hb_r2 : ∀ i, sobNorm (r + 1) (cx (bArr q i) - fun _ => (0 : ℂ)) ≤ 1 := fun i =>
    (hMc.2.2.2 i).trans ((mul_le_mul_of_nonneg_left hcsq_r2 hCc).trans hCcX)
  -- the difference norms
  set D := Xnorm r (q - p) (v - w)
  set F := Fnorm r (f - g)
  have hD0 : 0 ≤ D := Xnorm_nonneg _ _ _
  have hF0 : 0 ≤ F := Fnorm_nonneg _ _
  have hqd := isSymRec_sub hq hp
  have hvd := isSymRec_sub hv hw
  have hDcs : coordSum r bM (q - p) ≤ 16 * D := coordSum_bM_q_le r hqd (v - w) (by omega)
  have hDcs1 : coordSum (r + 1) bM (q - p) ≤ 16 * D := coordSum_bM_q_le r hqd (v - w) le_rfl
  have hDcJ : coordSum r bJ (jetArr (q - p) (v - w)) ≤ 80 * D := coordSum_bJ_le r hqd hvd
  -- Lipschitz bounds
  have hL := hml N q p (hcsq_r.trans (by linarith [hXq.trans hδl']))
    ((coordSum_bM_q_le s hp w (by omega)).trans (by linarith [hXp.trans hδl']))
  have hL1 := hml1 N q p (hcsq_r2.trans (by linarith [hXq.trans hδl1']))
    ((coordSum_bM_q_le s hp w (by omega)).trans (by linarith [hXp.trans hδl1']))
  have hLG := hmG N (jetArr q v) (jetArr p w)
    (((coordSum_mono (by omega) bJ _).trans (coordSum_bJ_le s hq hv)).trans
      (by linarith [hXq.trans hδG']))
    (((coordSum_mono (by omega) bJ _).trans (coordSum_bJ_le s hp hw)).trans
      (by linarith [hXp.trans hδG']))
  rw [jetArr_sub] at hLG
  have hΔa : sobNorm r (cx (aArr q) - cx (aArr p)) ≤ Cl * 16 * D := by
    refine hL.1.trans ?_
    calc Cl * coordSum r bM (q - p) ≤ Cl * (16 * D) := mul_le_mul_of_nonneg_left hDcs hCl
      _ = Cl * 16 * D := by ring
  have hΔc : ∀ i j, sobNorm (r + 1) (cx (cArr q i j) - cx (cArr p i j)) ≤ Cl1 * 16 * D := by
    intro i j
    refine (hL1.2.1 i j).trans ?_
    calc Cl1 * coordSum (r + 1) bM (q - p) ≤ Cl1 * (16 * D) :=
          mul_le_mul_of_nonneg_left hDcs1 hCl1
      _ = Cl1 * 16 * D := by ring
  have hΔb : ∀ i, sobNorm (r + 1) (cx (bArr q i) - cx (bArr p i)) ≤ Cl1 * 16 * D := by
    intro i
    refine (hL1.2.2 i).trans ?_
    calc Cl1 * coordSum (r + 1) bM (q - p) ≤ Cl1 * (16 * D) :=
          mul_le_mul_of_nonneg_left hDcs1 hCl1
      _ = Cl1 * 16 * D := by ring
  -- the source bound
  have hGsrc : ∀ κ : Upper, sobNorm r (diffSource q p v w f g κ.1.1 κ.1.2) ≤ CGt * (D + F) := by
    intro κ
    rw [diffSource_eq q p v w f g κ.1.1 κ.1.2 haq_ne hap_ne]
    have t1 : sobNorm r (cx (comp (Garr q v) κ.1.1 κ.1.2) - cx (comp (Garr p w) κ.1.1 κ.1.2)) ≤
        CG * 80 * D := by
      have := hLG κ.1.1 κ.1.2
      calc _ = sobNorm r (cx (fun x => compensatorMap (jetArr q v x) κ.1.1 κ.1.2) -
              cx (fun x => compensatorMap (jetArr p w x) κ.1.1 κ.1.2)) := rfl
        _ ≤ CG * coordSum r bJ (jetArr (q - p) (v - w)) := this
        _ ≤ CG * (80 * D) := mul_le_mul_of_nonneg_left hDcJ hCG
        _ = CG * 80 * D := by ring
    have t2 : sobNorm r ((cx (aArr q) - cx (aArr p)) *
        cx (comp (harmonicWriterAcceleration p w) κ.1.1 κ.1.2)) ≤ Ar * (Cl * 16) * KA * D := by
      refine (sobNorm_mul_le r (by omega) _ _).trans ?_
      have hAp : sobNorm r (cx (comp (harmonicWriterAcceleration p w) κ.1.1 κ.1.2)) ≤ KA :=
        (sobNorm_mono (by omega) _).trans ((hacc N p w hp hw (hXp.trans hδA') _ _).trans
          (mul_le_of_le_one_right hKA hXp1))
      calc Ar * sobNorm r (cx (aArr q) - cx (aArr p)) *
            sobNorm r (cx (comp (harmonicWriterAcceleration p w) κ.1.1 κ.1.2))
          ≤ Ar * (Cl * 16 * D) * KA := by
            gcongr
            exact sobNorm_nonneg _ _
        _ = Ar * (Cl * 16) * KA * D := by ring
    have t3 : sobNorm r (cDiv (fun i j => cx (cArr q i j) - cx (cArr p i j))
        (cx (comp p κ.1.1 κ.1.2))) ≤ 9 * (Ar2 * (Cl1 * 16)) * D := by
      unfold cDiv
      have hij : ∀ i j, sobNorm r (Dm i ((cx (cArr q i j) - cx (cArr p i j)) *
          Dp j (cx (comp p κ.1.1 κ.1.2)))) ≤ Ar2 * (Cl1 * 16) * D := by
        intro i j
        refine (sobNorm_Dm_le r i _).trans ((sobNorm_mul_le (r + 1) (by omega) _ _).trans ?_)
        have hp2 : sobNorm (r + 1) (Dp j (cx (comp p κ.1.1 κ.1.2))) ≤ 1 :=
          (sobNorm_Dp_le (r + 1) j _).trans ((sobNorm_q_le s hp w _ _ (by omega)).trans hXp1)
        calc Ar2 * sobNorm (r + 1) (cx (cArr q i j) - cx (cArr p i j)) *
              sobNorm (r + 1) (Dp j (cx (comp p κ.1.1 κ.1.2))) ≤ Ar2 * (Cl1 * 16 * D) * 1 := by
              gcongr
              · exact sobNorm_nonneg _ _
              · exact hΔc i j
          _ = Ar2 * (Cl1 * 16) * D := by ring
      calc _ ≤ ∑ i, sobNorm r (∑ j, Dm i ((cx (cArr q i j) - cx (cArr p i j)) *
            Dp j (cx (comp p κ.1.1 κ.1.2)))) := sobNorm_sum_le _ _ _
        _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, Ar2 * (Cl1 * 16) * D :=
            sum_le_sum fun i _ => (sobNorm_sum_le _ _ _).trans (sum_le_sum fun j _ => hij i j)
        _ = 9 * (Ar2 * (Cl1 * 16)) * D := by simp; ring
    have t4 : sobNorm r (cSkew (fun i => cx (bArr q i) - cx (bArr p i))
        (cx (comp w κ.1.1 κ.1.2))) ≤ 3 * ((Ar + Ar2) * (Cl1 * 16)) * D := by
      unfold cSkew
      have hw1 : sobNorm (r + 1) (cx (comp w κ.1.1 κ.1.2)) ≤ 1 :=
        (sobNorm_v_le s p hw _ _ (by omega)).trans hXp1
      have hi : ∀ i, sobNorm r ((cx (bArr q i) - cx (bArr p i)) * D0 i (cx (comp w κ.1.1 κ.1.2)) +
          D0 i ((cx (bArr q i) - cx (bArr p i)) * cx (comp w κ.1.1 κ.1.2))) ≤
          (Ar + Ar2) * (Cl1 * 16) * D := by
        intro i
        refine (sobNorm_add_le _ _ _).trans ?_
        have h1 : sobNorm r ((cx (bArr q i) - cx (bArr p i)) * D0 i (cx (comp w κ.1.1 κ.1.2))) ≤
            Ar * (Cl1 * 16 * D) * 1 := by
          refine (sobNorm_mul_le r (by omega) _ _).trans ?_
          gcongr
          · exact sobNorm_nonneg _ _
          · exact (sobNorm_mono (by omega) _).trans (hΔb i)
          · exact (sobNorm_D0_le r i _).trans hw1
        have h2 : sobNorm r (D0 i ((cx (bArr q i) - cx (bArr p i)) * cx (comp w κ.1.1 κ.1.2))) ≤
            Ar2 * (Cl1 * 16 * D) * 1 := by
          refine (sobNorm_D0_le r i _).trans ((sobNorm_mul_le (r + 1) (by omega) _ _).trans ?_)
          gcongr
          · exact sobNorm_nonneg _ _
          · exact hΔb i
        calc _ ≤ Ar * (Cl1 * 16 * D) * 1 + Ar2 * (Cl1 * 16 * D) * 1 := add_le_add h1 h2
          _ = (Ar + Ar2) * (Cl1 * 16) * D := by ring
      calc _ ≤ ∑ i, sobNorm r ((cx (bArr q i) - cx (bArr p i)) * D0 i (cx (comp w κ.1.1 κ.1.2)) +
            D0 i ((cx (bArr q i) - cx (bArr p i)) * cx (comp w κ.1.1 κ.1.2))) :=
            sobNorm_sum_le _ _ _
        _ ≤ ∑ _i : Fin 3, (Ar + Ar2) * (Cl1 * 16) * D := sum_le_sum fun i _ => hi i
        _ = 3 * ((Ar + Ar2) * (Cl1 * 16)) * D := by simp; ring
    have t5 : sobNorm r (cx (aArr q) * (cx (comp f κ.1.1 κ.1.2) - cx (comp g κ.1.1 κ.1.2))) ≤
        (Ar + 1) * F := by
      refine (sobNorm_coef_mul_le r (by omega) _ _ 1 (by simp) ha_r).trans ?_
      rw [← cx_comp_sub]
      exact mul_le_mul_of_nonneg_left (sobNorm_le_Fnorm r (f - g) κ) (by positivity)
    calc _ ≤ CG * 80 * D + Ar * (Cl * 16) * KA * D + 9 * (Ar2 * (Cl1 * 16)) * D +
          3 * ((Ar + Ar2) * (Cl1 * 16)) * D + (Ar + 1) * F := by
          refine (sobNorm_add_le _ _ _).trans (add_le_add ?_ t5)
          refine (sobNorm_sub_le _ _ _).trans (add_le_add ?_ t4)
          refine (sobNorm_add_le _ _ _).trans (add_le_add ?_ t3)
          exact (sobNorm_sub_le _ _ _).trans (add_le_add t1 t2)
      _ ≤ CGt * (D + F) := by
          have h1 : 0 ≤ (CG * 80 + Ar * (Cl * 16) * KA + 9 * (Ar2 * (Cl1 * 16)) +
              3 * ((Ar + Ar2) * (Cl1 * 16))) * F := by positivity
          have h2 : 0 ≤ (Ar + 1) * D := by positivity
          have e : CGt * (D + F) = CG * 80 * D + Ar * (Cl * 16) * KA * D +
              9 * (Ar2 * (Cl1 * 16)) * D + 3 * ((Ar + Ar2) * (Cl1 * 16)) * D + (Ar + 1) * F +
              ((CG * 80 + Ar * (Cl * 16) * KA + 9 * (Ar2 * (Cl1 * 16)) +
                3 * ((Ar + Ar2) * (Cl1 * 16))) * F + (Ar + 1) * D) := by
            simp only [CGt]; ring
          linarith
  -- the acceleration difference in `H^{r-1}_h`
  have hδvt : ∀ κ : Upper, sobNorm (r - 1) (cx (comp (dAcc q p v w f g) κ.1.1 κ.1.2)) ≤
      CV * (D + F) := by
    intro κ
    have e : cx (comp (dAcc q p v w f g) κ.1.1 κ.1.2) =
        cx (fun x => (harmA (minkowski + q x))⁻¹) *
          (cx (aArr q) * cx (comp (dAcc q p v w f g) κ.1.1 κ.1.2)) := by
      funext x
      simp only [Pi.mul_apply, cx_apply]
      rw [← mul_assoc, ← Complex.ofReal_mul, show (harmA (minkowski + q x))⁻¹ * aArr q x = 1 from
        inv_mul_cancel₀ (haq_ne x), Complex.ofReal_one, one_mul]
    have hrw : cx (aArr q) * cx (comp (dAcc q p v w f g) κ.1.1 κ.1.2) =
        ∑ i, ∑ j, Dm i (cx (cArr q i j) * Dp j (cx (comp (q - p) κ.1.1 κ.1.2))) -
        ∑ i, (cx (bArr q i) * D0 i (cx (comp (v - w) κ.1.1 κ.1.2)) +
          D0 i (cx (bArr q i) * cx (comp (v - w) κ.1.1 κ.1.2))) +
        diffSource q p v w f g κ.1.1 κ.1.2 := by
      unfold diffSource cDiv cSkew; abel
    rw [e, hrw]
    refine (sobNorm_coef_mul_le (r - 1) (by omega) _ _ 1 (by simp) hainv).trans ?_
    have hR := rhs_bound r hr (cx (comp (q - p) κ.1.1 κ.1.2)) (cx (comp (v - w) κ.1.1 κ.1.2))
      (diffSource q p v w f g κ.1.1 κ.1.2) (fun i j => cx (cArr q i j)) (fun i => cx (bArr q i))
      (fun i j => ((if i = j then 1 else 0 : ℝ) : ℂ)) (fun i j => by split_ifs <;> simp)
      (D + F) CGt
      (fun i j => (sobNorm_mono (by omega) _).trans (hc_r2 i j))
      (fun i => (sobNorm_mono (by omega) _).trans (hb_r2 i))
      (fun j => (sobNorm_Dp_le r j _).trans ((sobNorm_q_le r hqd (v - w) _ _ le_rfl).trans
        (by linarith)))
      ((sobNorm_v_le r (q - p) hvd _ _ le_rfl).trans (by linarith)) (hGsrc κ)
    calc (Ar1 + 1) * sobNorm (r - 1) _ ≤ (Ar1 + 1) *
          ((9 * (Ar + 1) + 3 * Ar1 + 3 * Ar + CGt) * (D + F)) := by gcongr
      _ = CV * (D + F) := by simp only [CV]; ring
  -- the remainder of the commuted difference row
  have hRd : ∀ α ∈ multiIndices r, ∀ κ : Upper,
      gridNorm (cx (Rdiff α q p v w f g κ.1.1 κ.1.2)) ≤ CR * (D + F) := by
    intro α hα κ
    rw [mem_multiIndices] at hα
    rw [cx_Rdiff]
    refine (hrow N α hα _ _ _ _ _ _ _ 1 (fun i j => ((if i = j then 1 else 0 : ℝ) : ℂ))
      (fun _ => 0)).trans ?_
    have hq1 : sobNorm (r + 1) (cx (comp (q - p) κ.1.1 κ.1.2)) ≤ D :=
      sobNorm_q_le r hqd (v - w) _ _ le_rfl
    have hv1 : sobNorm r (cx (comp (v - w) κ.1.1 κ.1.2)) ≤ D :=
      sobNorm_v_le r (q - p) hvd _ _ le_rfl
    have u1 : sobNorm r (cx (aArr q) - fun _ => (1 : ℂ)) *
        sobNorm (r - 1) (cx (comp (dAcc q p v w f g) κ.1.1 κ.1.2)) ≤ 1 * (CV * (D + F)) :=
      mul_le_mul ha_r (hδvt κ) (sobNorm_nonneg _ _) zero_le_one
    have u2 : ∑ i, ∑ j, sobNorm (r + 1) (cx (cArr q i j) -
        fun _ => ((if i = j then 1 else 0 : ℝ) : ℂ)) *
        sobNorm (r + 1) (cx (comp (q - p) κ.1.1 κ.1.2)) ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 1 * D :=
      sum_le_sum fun i _ => sum_le_sum fun j _ =>
        mul_le_mul (hc_r2 i j) hq1 (sobNorm_nonneg _ _) zero_le_one
    have u3 : ∑ i, sobNorm (r + 1) (cx (bArr q i) - fun _ => (0 : ℂ)) *
        sobNorm r (cx (comp (v - w) κ.1.1 κ.1.2)) ≤ ∑ _i : Fin 3, 1 * D :=
      sum_le_sum fun i _ => mul_le_mul (hb_r2 i) hv1 (sobNorm_nonneg _ _) zero_le_one
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at u2 u3
    have hsum := add_le_add (add_le_add u1 u2) u3
    have := mul_le_mul_of_nonneg_left hsum hCr
    have h4 := hGsrc κ
    calc _ ≤ Cr * (1 * (CV * (D + F)) + (3 : ℕ) * ((3 : ℕ) * (1 * D)) + (3 : ℕ) * (1 * D)) +
          CGt * (D + F) := by linarith
      _ ≤ CR * (D + F) := by
          have h1 : 0 ≤ Cr * 12 * F := by positivity
          have e : CR * (D + F) = Cr * (1 * (CV * (D + F)) + (3 : ℕ) * ((3 : ℕ) * (1 * D)) +
              (3 : ℕ) * (1 * D)) + CGt * (D + F) + Cr * 12 * F := by
            simp only [CR]; push_cast; ring
          linarith
  -- the rate
  have hper : ∀ α ∈ multiIndices r, ∀ κ : Upper,
      ((N : ℝ) ^ 3)⁻¹ * ∑ x,
        ((1 / 2) * (DαR α (comp (v - w) κ.1.1 κ.1.2) x *
            (SαR α (adot q v) x * DαR α (comp (v - w) κ.1.1 κ.1.2) x)) +
          (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i (DαR α (comp (q - p) κ.1.1 κ.1.2)) x *
            (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j (DαR α (comp (q - p) κ.1.1 κ.1.2)) x) +
          DαR α (comp (q - p) κ.1.1 κ.1.2) x * DαR α (comp (v - w) κ.1.1 κ.1.2) x +
          DαR α (comp (v - w) κ.1.1 κ.1.2) x * Rdiff α q p v w f g κ.1.1 κ.1.2 x) ≤
      (5 * K₁ + 1 + CR) * D ^ 2 + CR * D * F := by
    intro α hα κ
    have hdeg := mem_multiIndices.mp hα
    set vα := DαR α (comp (v - w) κ.1.1 κ.1.2)
    set qα := DαR α (comp (q - p) κ.1.1 κ.1.2)
    set R := Rdiff α q p v w f g κ.1.1 κ.1.2
    have hvα : gridNorm (cx vα) ≤ D :=
      (gridNorm_cx_DαR_le hdeg _).trans (sobNorm_v_le r (q - p) hvd _ _ le_rfl)
    have hqα : gridNorm (cx qα) ≤ D :=
      (gridNorm_cx_DαR_le hdeg _).trans (sobNorm_q_le r hqd (v - w) _ _ (by omega))
    have hdα : ∀ i, gridNorm (cx (OpenWriterEnergy.Dp i qα)) ≤ D := fun i =>
      (gridNorm_cx_Dp_DαR_le (by omega) i _).trans (sobNorm_q_le r hqd (v - w) _ _ le_rfl)
    have hK1X : K₁ * Xq ≤ K₁ := mul_le_of_le_one_right hK₁ hXq1
    have hpt : ∀ x, (1 / 2) * (vα x * (SαR α (adot q v) x * vα x)) +
        (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i qα x *
          (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j qα x) ≤
        (1 / 2) * K₁ * vα x ^ 2 + (3 / 2) * K₁ * ∑ i, OpenWriterEnergy.Dp i qα x ^ 2 := by
      intro x
      have h1 : vα x * (SαR α (adot q v) x * vα x) ≤ K₁ * vα x ^ 2 := by
        have := (hadot (x + svec α)).trans hK1X
        have e : SαR α (adot q v) x = adot q v (x + svec α) := rfl
        rw [e]
        have h := (le_abs_self _).trans (abs_mul_mul_le (vα x) (adot q v (x + svec α)) (vα x)
          _ this)
        linarith
      have h2 := quad_upper (fun i => OpenWriterEnergy.Dp i qα x)
        (fun i j => SαR α (cdot q v i j) x) K₁
        (fun i j => (hcdot (x + svec α) i j).trans hK1X)
      linarith
    have hN : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
    have e4 : ((N : ℝ) ^ 3)⁻¹ * ∑ x,
        ((1 / 2) * (vα x * (SαR α (adot q v) x * vα x)) +
        (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i qα x *
          (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j qα x) +
        qα x * vα x + vα x * R x) =
        ((N : ℝ) ^ 3)⁻¹ * ∑ x, ((1 / 2) * (vα x * (SαR α (adot q v) x * vα x)) +
          (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i qα x *
            (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j qα x)) +
        ((N : ℝ) ^ 3)⁻¹ * ∑ x, qα x * vα x + ((N : ℝ) ^ 3)⁻¹ * ∑ x, vα x * R x := by
      simp only [← mul_add, ← sum_add_distrib]
    rw [e4]
    have b1 : ((N : ℝ) ^ 3)⁻¹ * ∑ x, ((1 / 2) * (vα x * (SαR α (adot q v) x * vα x)) +
          (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i qα x *
            (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j qα x)) ≤
        (1 / 2) * K₁ * D ^ 2 + (3 / 2) * K₁ * (3 * D ^ 2) := by
      refine (avg_le hpt).trans ?_
      have e : ((N : ℝ) ^ 3)⁻¹ * ∑ x, ((1 / 2) * K₁ * vα x ^ 2 +
          (3 / 2) * K₁ * ∑ i, OpenWriterEnergy.Dp i qα x ^ 2) =
          (1 / 2) * K₁ * gridNorm (cx vα) ^ 2 +
          (3 / 2) * K₁ * ∑ i, gridNorm (cx (OpenWriterEnergy.Dp i qα)) ^ 2 := by
        simp only [← avg_sq, sum_add_distrib, mul_add, ← mul_sum]
        rw [sum_comm (s := univ) (t := univ) (f := fun x i => OpenWriterEnergy.Dp i qα x ^ 2)]
        simp only [mul_sum]
        ring
      rw [e]
      have hv2 : gridNorm (cx vα) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (gridNorm_nonneg _) hvα 2
      have hd2 : ∑ i, gridNorm (cx (OpenWriterEnergy.Dp i qα)) ^ 2 ≤ 3 * D ^ 2 := by
        calc ∑ i, gridNorm (cx (OpenWriterEnergy.Dp i qα)) ^ 2 ≤ ∑ _i : Fin 3, D ^ 2 :=
              sum_le_sum fun i _ => pow_le_pow_left₀ (gridNorm_nonneg _) (hdα i) 2
          _ = 3 * D ^ 2 := by simp
      gcongr
    have b2 : ((N : ℝ) ^ 3)⁻¹ * ∑ x, qα x * vα x ≤ D * D :=
      (le_abs_self _).trans ((abs_inner_le qα vα).trans
        (mul_le_mul hqα hvα (gridNorm_nonneg _) hD0))
    have b3 : ((N : ℝ) ^ 3)⁻¹ * ∑ x, vα x * R x ≤ D * (CR * (D + F)) :=
      (le_abs_self _).trans ((abs_inner_le vα R).trans
        (mul_le_mul hvα (hRd α hα κ) (gridNorm_nonneg _) hD0))
    have e : (1 / 2) * K₁ * D ^ 2 + (3 / 2) * K₁ * (3 * D ^ 2) + D * D + D * (CR * (D + F)) =
        (5 * K₁ + 1 + CR) * D ^ 2 + CR * D * F := by ring
    linarith
  have hD2 : Xsq r (q - p) (v - w) = D ^ 2 := (Xnorm_sq _ _ _).symm
  calc diffRate r q p v w f g ≤ ∑ _α ∈ multiIndices r, ∑ _κ : Upper,
        ((5 * K₁ + 1 + CR) * D ^ 2 + CR * D * F) := by
        unfold diffRate
        refine sum_le_sum fun α hα => ?_
        rw [mul_sum]
        exact sum_le_sum fun κ _ => hper α hα κ
    _ = cM * cU * ((5 * K₁ + 1 + CR) * D ^ 2 + CR * D * F) := by
        simp only [sum_const, card_univ, nsmul_eq_mul, cM, cU]; ring
    _ ≤ K * Xsq r (q - p) (v - w) + K * D * F := by
        rw [hD2]
        have hcMU : 0 ≤ cM * cU := by positivity
        have h1 : 0 ≤ cM * cU * CR * D ^ 2 := by positivity
        have h2 : 0 ≤ cM * cU * (5 * K₁ + 1 + CR) * D * F := by positivity
        have e : K * D ^ 2 + K * D * F = cM * cU * ((5 * K₁ + 1 + CR) * D ^ 2 + CR * D * F) +
            (cM * cU * CR * D ^ 2 + cM * cU * (5 * K₁ + 1 + CR) * D * F) := by
          simp only [K]; ring
        linarith

/-! ### The difference estimate -/

/-- A pair of forced record histories `X = (q, v)`, `Y = (p, w)` with forces `f, f̃` on `[0, T]`,
both in the top chart `‖·‖_{X^s_h} ≤ δ` (two-sided derivatives, ten-component equations). -/
def IsForcedPair (s : ℕ) (δ T : ℝ) (q p v w f g : ℝ → Grid N → MetricRec) : Prop :=
  ∀ t ∈ Icc 0 T, IsSymRec (q t) ∧ IsSymRec (v t) ∧ IsSymRec (p t) ∧ IsSymRec (w t) ∧
    (∀ x, HasDerivAt (fun τ => q τ x) (v t x) t) ∧
    (∀ x, HasDerivAt (fun τ => p τ x) (w t x) t) ∧
    (∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
      (harmonicWriterAcceleration (q t) (v t) x κ.1.1 κ.1.2 + f t x κ.1.1 κ.1.2) t) ∧
    (∀ x (κ : Upper), HasDerivAt (fun τ => w τ x κ.1.1 κ.1.2)
      (harmonicWriterAcceleration (p t) (w t) x κ.1.1 κ.1.2 + g t x κ.1.1 κ.1.2) t) ∧
    Xnorm s (q t) (v t) ≤ δ ∧ Xnorm s (p t) (w t) ≤ δ

/-- **`eq:supp-open-difference`** (`cor:supp-open-lifespan`, third clause): the lower-order
difference estimate.  For `3 ≤ r ≤ s - 1` there are a top-chart radius `δ > 0` and `K ≥ 0`,
independent of the mesh, such that for every `N`, every `T ≥ 0` and every two top-bounded forced
records `X = (q, v)`, `Y = (p, w)` on `[0, T]` with forces `f, f̃` continuous on `[0, T]`,
`‖X(t) - Y(t)‖_{X^r_h} ≤ 2 e^{K t} (3 ‖X(0) - Y(0)‖_{X^r_h} + K ∫_0^t ‖f - f̃‖_{r,h})`
for every `t ∈ [0, T]`; in particular
`sup_{t ≤ T} ‖X - Y‖_{X^r_h} ≤ C_T (‖X(0) - Y(0)‖_{X^r_h} + ∫_0^T ‖f - f̃‖_{r,h})` with
`C_T = 6 e^{K T} (1 + K)`, no inverse-mesh exponential. -/
theorem open_writer_difference (s r : ℕ) (hr : 3 ≤ r) (hrs : r + 1 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (T : ℝ) (q p v w f g : ℝ → Grid N → MetricRec),
      IsForcedPair s δ T q p v w f g → ContinuousOn f (Icc 0 T) → ContinuousOn g (Icc 0 T) →
      ∀ t ∈ Icc 0 T, Xnorm r (q t - p t) (v t - w t) ≤
        2 * Real.exp (K * t) * (3 * Xnorm r (q 0 - p 0) (v 0 - w 0) +
          K * ∫ τ in (0)..t, Fnorm r (f τ - g τ)) := by
  have hs : 3 ≤ s := by omega
  obtain ⟨δ1, hδ1, Kd, hKd, hstat⟩ := diff_static_bound s r hr hrs
  obtain ⟨δ0, hδ0, K₁, hK₁, hpc⟩ := pointwise_chart s hs
  set δ := min δ1 δ0
  have hδ : 0 < δ := lt_min hδ1 hδ0
  refine ⟨δ, hδ, 4 * Kd, by positivity, fun N _ T q p v w f g hpair hf hg => ?_⟩
  set E : ℝ → ℝ := fun τ => genEnergy r (aArr (q τ)) (cArr (q τ)) (q τ - p τ) (v τ - w τ)
  set Fn : ℝ → ℝ := fun τ => Fnorm r (f τ - g τ)
  set Dn : ℝ → ℝ := fun τ => Xnorm r (q τ - p τ) (v τ - w τ)
  -- the energy bounds at each time
  have hbd : ∀ τ ∈ Icc 0 T, Xsq r (q τ - p τ) (v τ - w τ) / 4 ≤ E τ ∧
      E τ ≤ 8 * Xsq r (q τ - p τ) (v τ - w τ) := by
    intro τ hτ
    obtain ⟨hqs, hvs, -, -, -, -, -, -, hXq, -⟩ := hpair τ hτ
    obtain ⟨ha, hc, -⟩ := hpc N (q τ) (v τ) hqs hvs (hXq.trans (min_le_right _ _))
    exact genEnergy_bounds r _ _ ha hc _ _
  have hE0 : ∀ τ ∈ Icc 0 T, 0 ≤ E τ := fun τ hτ =>
    le_trans (by have := Xsq_nonneg r (q τ - p τ) (v τ - w τ); linarith) (hbd τ hτ).1
  have hDs : ∀ τ ∈ Icc 0 T, Dn τ ≤ 2 * Real.sqrt (E τ) := by
    intro τ hτ
    have h1 : Dn τ ^ 2 ≤ 4 * E τ := by
      have := (hbd τ hτ).1
      rw [show Dn τ ^ 2 = Xsq r (q τ - p τ) (v τ - w τ) from Xnorm_sq _ _ _]
      linarith
    have hD0 : 0 ≤ Dn τ := Xnorm_nonneg _ _ _
    have : Dn τ = Real.sqrt (Dn τ ^ 2) := (Real.sqrt_sq hD0).symm
    rw [this, show 2 * Real.sqrt (E τ) = Real.sqrt (4 * E τ) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt h1
  -- the differential inequality
  have hderiv : ∀ τ ∈ Icc 0 T, ∃ e', HasDerivAt E e' τ ∧
      e' ≤ 4 * Kd * E τ + 4 * Kd * Real.sqrt (E τ) * Fn τ := by
    intro τ hτ
    obtain ⟨hqs, hvs, hps, hws, hq, hp, hv, hw, hXq, hXp⟩ := hpair τ hτ
    obtain ⟨-, -, -, -, hdA, hdC⟩ := hpc N (q τ) (v τ) hqs hvs (hXq.trans (min_le_right _ _))
    refine ⟨_, hasDerivAt_diffEnergy r q p v w f g τ hqs hq hp hv hw hdA hdC, ?_⟩
    have h1 := hstat N (q τ) (p τ) (v τ) (w τ) (f τ) (g τ) hqs hps hvs hws
      (hXq.trans (min_le_left _ _)) (hXp.trans (min_le_left _ _))
    have h2 : Xsq r (q τ - p τ) (v τ - w τ) ≤ 4 * E τ := by linarith [(hbd τ hτ).1]
    have h3 : Dn τ * Fn τ ≤ 2 * Real.sqrt (E τ) * Fn τ :=
      mul_le_mul_of_nonneg_right (hDs τ hτ) (Fnorm_nonneg _ _)
    have h4 : Kd * Xsq r (q τ - p τ) (v τ - w τ) ≤ Kd * (4 * E τ) :=
      mul_le_mul_of_nonneg_left h2 hKd
    have h5 : Kd * (Dn τ * Fn τ) ≤ Kd * (2 * Real.sqrt (E τ) * Fn τ) :=
      mul_le_mul_of_nonneg_left h3 hKd
    have h6 : 0 ≤ Kd * (2 * Real.sqrt (E τ) * Fn τ) := by
      have := Fnorm_nonneg r (f τ - g τ)
      positivity
    have e1 : Kd * Xnorm r (q τ - p τ) (v τ - w τ) * Fnorm r (f τ - g τ) = Kd * (Dn τ * Fn τ) := by
      simp only [Dn, Fn]; ring
    rw [e1] at h1
    nlinarith
  -- the forced Gronwall inequality
  have hFc : ContinuousOn Fn (Icc 0 T) := (continuous_Fnorm r).comp_continuousOn (hf.sub hg)
  intro t ht
  have hgr := ODECutoff.sqrt_le_of_forced_deriv (by positivity) hderiv hE0 hFc
    (fun τ _ => Fnorm_nonneg _ _) t ht
  have hT : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hsE0 : Real.sqrt (E 0) ≤ 3 * Dn 0 := by
    have h1 := (hbd 0 hT).2
    have hD0 : 0 ≤ Dn 0 := Xnorm_nonneg _ _ _
    rw [show Xsq r (q 0 - p 0) (v 0 - w 0) = Dn 0 ^ 2 from (Xnorm_sq _ _ _).symm] at h1
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hint : 0 ≤ ∫ τ in (0)..t, Fn τ :=
    intervalIntegral.integral_nonneg ht.1 fun τ _ => Fnorm_nonneg _ _
  have hex := Real.exp_pos (4 * Kd * t)
  calc Dn t ≤ 2 * Real.sqrt (E t) := hDs t ht
    _ ≤ 2 * (Real.exp (4 * Kd * t) * (Real.sqrt (E 0) + 4 * Kd * ∫ τ in (0)..t, Fn τ)) := by
        gcongr
    _ ≤ 2 * Real.exp (4 * Kd * t) * (3 * Dn 0 + 4 * Kd * ∫ τ in (0)..t, Fn τ) := by
        rw [← mul_assoc]
        gcongr

/-- Non-vacuity: the flat pair `X = Y = 0` with zero forces is a top-bounded forced pair. -/
example (s r : ℕ) (hr : 3 ≤ r) (hrs : r + 1 ≤ s) : True := by
  obtain ⟨δ, hδ, K, hK, h⟩ := open_writer_difference s r hr hrs
  have hX : Xnorm s (0 : Grid 5 → MetricRec) 0 ≤ δ := by
    have : Xsq s (0 : Grid 5 → MetricRec) 0 = 0 := by
      unfold Xsq
      refine sum_eq_zero fun κ _ => ?_
      have e : cx (comp (0 : Grid 5 → MetricRec) κ.1.1 κ.1.2) = 0 := by funext x; simp [comp, cx]
      rw [e]
      simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
    rw [Xnorm, this, Real.sqrt_zero]; exact hδ.le
  have hpair : IsForcedPair s δ 1 (fun _ => (0 : Grid 5 → MetricRec)) (fun _ => 0) (fun _ => 0)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
    intro t _
    refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun x => hasDerivAt_const _ _, fun x => hasDerivAt_const _ _, fun x κ => ?_,
      fun x κ => ?_, hX, hX⟩
    · rw [harmonicWriterAcceleration_zero]; simpa using hasDerivAt_const t (0 : ℝ)
    · rw [harmonicWriterAcceleration_zero]; simpa using hasDerivAt_const t (0 : ℝ)
  have := h 5 1 _ _ _ _ _ _ hpair continuousOn_const continuousOn_const 1 ⟨zero_le_one, le_rfl⟩
  trivial
end

end RenewalGeometry.OpenWriterLifespan
