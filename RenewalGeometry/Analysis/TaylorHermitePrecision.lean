/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TaylorHermiteResidual

/-!
# Sobolev-scaled finite precision for the Taylor–Hermite polynomial
  (`lem:supp-open-hermite-precision`, `eq:supp-open-hermite-precision`; emergent-spacetime
  manuscript)

In the setting of `TaylorHermiteResidual` (a second-order writer with inverse-mesh bounds),
let `Q_X` be the endpoint-corrected Taylor–Hermite polynomial and `Q̃_X = Q_X + δQ` a degree-seven
perturbation, with `b ≥ max_{e ∈ {0,1}, j ≤ 3} τʲ ‖δQ⁽ʲ⁾(eτ)‖` (velocity-space norm).

* `Writer.phase_pert_le`, `Writer.phaseVel_pert_le`, `Writer.Bounds.defect_pert_le`,
  `Writer.Bounds.defectDeriv_pert_le`: the change of the phase, of its velocity, of the defect
  and of its time derivative under a polynomial perturbation.
* `hermite_precision` (**`lem:supp-open-hermite-precision`**): (1) `‖δQ⁽ʲ⁾(t)‖ ≤ C_j τ^{-j} b`
  on `[0, τ]`; if moreover `b ≤ c ε τ² h⁵` then, on sufficiently fine meshes, (2) the perturbed
  polynomial stays in the chart, (3) the defect changes by at most `C τ^{-2} b` and its time
  derivative by at most `C τ^{-3} b`, and (4) the bounds `‖f‖ ≤ C ε h⁵`, `‖∂_t f‖ ≤ C ε h³` of
  `eq:supp-open-hermite-local-defect` are preserved.
-/

open Set Metric Filter Topology Function
open scoped ContDiff BigOperators NNReal

namespace RenewalGeometry.TaylorHermiteResidual

open IteratedDerivBounds TwoPointHermite

noncomputable section

namespace Writer

variable {Eq Ev : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] [CompleteSpace Eq]
  [NormedAddCommGroup Ev] [NormedSpace ℝ Ev] [CompleteSpace Ev] {W : Writer Eq Ev}
  {h A δ : ℝ}

omit [CompleteSpace Eq] [CompleteSpace Ev] in
theorem phase_pert_le (W : Writer Eq Ev) (P d : Fin 8 → Eq) (t : ℝ) :
    ‖W.phase (P + d) t - W.phase P t‖ ≤
      ‖W.u‖ * ‖W.ι (polyCurveDeriv 0 d t)‖ + ‖W.ι (polyCurveDeriv 1 d t)‖ := by
  have e : W.phase (P + d) t - W.phase P t = (polyCurve d t, W.ι (polyCurveDeriv 1 d t)) := by
    have hQ0 : polyCurve (P + d) t = polyCurve P t + polyCurve d t := by
      rw [← polyCurveDeriv_zero, polyCurveDeriv_add, polyCurveDeriv_zero, polyCurveDeriv_zero]
    show (polyCurve (P + d) t, W.ι (polyCurveDeriv 1 (P + d) t)) -
      (polyCurve P t, W.ι (polyCurveDeriv 1 P t)) = _
    rw [hQ0, polyCurveDeriv_add, map_add]
    refine Prod.ext ?_ ?_ <;> simp
  rw [e]
  refine (norm_prod_le_iff.mpr ⟨?_, ?_⟩)
  · have hx : ‖polyCurve d t‖ ≤ ‖W.u‖ * ‖W.ι (polyCurveDeriv 0 d t)‖ := by
      have := W.u.le_opNorm (W.ι (polyCurve d t))
      rw [W.u_ι] at this
      rwa [polyCurveDeriv_zero]
    have := norm_nonneg (W.ι (polyCurveDeriv 1 d t))
    linarith
  · have := mul_nonneg (norm_nonneg W.u) (norm_nonneg (W.ι (polyCurveDeriv 0 d t)))
    linarith

omit [CompleteSpace Eq] [CompleteSpace Ev] in
theorem phaseVel_pert_le (W : Writer Eq Ev) (P d : Fin 8 → Eq) (t : ℝ) :
    ‖W.phaseVel (P + d) t - W.phaseVel P t‖ ≤
      ‖W.u‖ * ‖W.ι (polyCurveDeriv 1 d t)‖ + ‖W.ι (polyCurveDeriv 2 d t)‖ := by
  have e : W.phaseVel (P + d) t - W.phaseVel P t =
      (polyCurveDeriv 1 d t, W.ι (polyCurveDeriv 2 d t)) := by
    show (polyCurveDeriv 1 (P + d) t, W.ι (polyCurveDeriv 2 (P + d) t)) -
      (polyCurveDeriv 1 P t, W.ι (polyCurveDeriv 2 P t)) = _
    rw [polyCurveDeriv_add, polyCurveDeriv_add, map_add]
    refine Prod.ext ?_ ?_ <;> simp
  rw [e]
  refine (norm_prod_le_iff.mpr ⟨?_, ?_⟩)
  · have hx : ‖polyCurveDeriv 1 d t‖ ≤ ‖W.u‖ * ‖W.ι (polyCurveDeriv 1 d t)‖ := by
      have := W.u.le_opNorm (W.ι (polyCurveDeriv 1 d t))
      rwa [W.u_ι] at this
    have := norm_nonneg (W.ι (polyCurveDeriv 2 d t))
    linarith
  · have := mul_nonneg (norm_nonneg W.u) (norm_nonneg (W.ι (polyCurveDeriv 1 d t)))
    linarith

theorem Bounds.defect_pert_le (hB : W.Bounds h A δ) {P d : Fin 8 → Eq} {t : ℝ}
    (hPU : W.phase P t ∈ ball 0 δ) (hQU : W.phase (P + d) t ∈ ball 0 δ) :
    ‖W.defect (P + d) t - W.defect P t‖ ≤
      ‖W.ι (polyCurveDeriv 2 d t)‖ + A * h⁻¹ * ‖W.phase (P + d) t - W.phase P t‖ := by
  have e : W.defect (P + d) t - W.defect P t = W.ι (polyCurveDeriv 2 d t) +
      (W.field (W.phase P t) - W.field (W.phase (P + d) t)).2 := by
    simp only [defect, V_eq, Prod.snd_sub]; rw [polyCurveDeriv_add, map_add]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_snd_le _).trans ((hB.lip_field hPU hQU).trans ?_)
  rw [norm_sub_rev]

theorem Bounds.defectDeriv_pert_le (hB : W.Bounds h A δ) {P d : Fin 8 → Eq} {t : ℝ}
    (hPU : W.phase P t ∈ ball 0 δ) (hQU : W.phase (P + d) t ∈ ball 0 δ) :
    ‖W.defectDeriv (P + d) t - W.defectDeriv P t‖ ≤
      ‖W.ι (polyCurveDeriv 3 d t)‖ +
        A * h⁻¹ * ‖W.phase (P + d) t - W.phase P t‖ * ‖W.phaseVel P t‖ +
        A * h⁻¹ * ‖W.phaseVel (P + d) t - W.phaseVel P t‖ := by
  set F := W.field
  have e : W.defectDeriv (P + d) t - W.defectDeriv P t = W.ι (polyCurveDeriv 3 d t) +
      ((fderiv ℝ F (W.phase P t) - fderiv ℝ F (W.phase (P + d) t)) (W.phaseVel P t)).2 -
      (fderiv ℝ F (W.phase (P + d) t) (W.phaseVel (P + d) t - W.phaseVel P t)).2 := by
    simp only [defectDeriv, ContinuousLinearMap.sub_apply, map_sub, Prod.snd_sub]
    rw [polyCurveDeriv_add, map_add]; abel
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
  · refine (norm_snd_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (hB.lip_fderiv hPU hQU).trans ?_
    rw [norm_sub_rev]
  · refine (norm_snd_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    exact mul_le_mul_of_nonneg_right (hB.norm_fderiv hQU) (norm_nonneg _)

omit [CompleteSpace Eq] [CompleteSpace Ev] in
/-- **First clause of `lem:supp-open-hermite-precision`** in the velocity norm:
`‖ι δQ⁽ʲ⁾(t)‖ ≤ C_j τ^{-j} b` on `[0, τ]` when `τⁱ ‖ι δQ⁽ⁱ⁾(eτ)‖ ≤ b` at both endpoints. -/
theorem norm_ι_pert_le (W : Writer Eq Ev) (d : Fin 8 → Eq) {τ b : ℝ} (hτ : 0 < τ)
    (hb : ∀ e : Fin 2, ∀ i : Fin 4,
      τ ^ (i : ℕ) * ‖W.ι (polyCurveDeriv i d (((e : ℕ) : ℝ) * τ))‖ ≤ b)
    (j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖W.ι (polyCurveDeriv j d t)‖ ≤ hermiteConst 3 j * b / τ ^ j := by
  rw [W.ι_polyCurveDeriv]
  refine norm_polyCurveDeriv_le_scaled (k := 3) _ hτ (fun e i => ?_) j ht
  rw [← W.ι_polyCurveDeriv]
  exact hb e i

end Writer

universe uq uv

set_option maxHeartbeats 4000000 in
/-- **`lem:supp-open-hermite-precision`** (Sobolev-scaled finite precision), abstract form.
Fix `A ≥ 1`, `0 < c₋, c₊` and `c_b ≥ 0`.  There are `h₀ > 0` and `C`, depending only on
`(A, c₋, c₊, c_b)`, such that for every writer with the inverse-mesh bounds
`W.Bounds h A δ` (`h ≤ h₀`), every source `‖X‖ ≤ ε ≤ δ/4`, every step `c₋h² ≤ τ ≤ c₊h²`, every
degree-seven perturbation `δQ` of `Q_X` and every
`b ≥ max_{e ∈ {0,1}, j ≤ 3} τʲ ‖δQ⁽ʲ⁾(eτ)‖` (`eq:supp-open-hermite-precision`), for all
`t ∈ [0, τ]`:
1. `‖δQ⁽ʲ⁾(t)‖ ≤ C_j τ^{-j} b` for every `j` (with `C_j = hermiteConst 3 j`);
and if `b ≤ c_b ε τ² h⁵`:
2. the perturbed polynomial `Q̃_X = Q_X + δQ` stays in the chart;
3. `‖f_{Q̃}(t) − f_Q(t)‖ ≤ C τ^{-2} b` and `‖∂_t f_{Q̃}(t) − ∂_t f_Q(t)‖ ≤ C τ^{-3} b`;
4. `‖f_{Q̃}(t)‖ ≤ C ε h⁵`, `f_{Q̃}` is differentiable and `‖∂_t f_{Q̃}(t)‖ ≤ C ε h³`. -/
theorem hermite_precision (A cm cp cb : ℝ) (hA : 1 ≤ A) (hcm : 0 < cm) (hcp : 0 < cp)
    (hcb : 0 ≤ cb) :
    ∃ h₀ > 0, ∃ C ≥ 0, ∀ {Eq : Type uq} {Ev : Type uv} [NormedAddCommGroup Eq]
      [NormedSpace ℝ Eq] [CompleteSpace Eq] [NormedAddCommGroup Ev] [NormedSpace ℝ Ev]
      [CompleteSpace Ev] (W : Writer Eq Ev) (h δ : ℝ), W.Bounds h A δ → h ≤ h₀ →
      ∀ (X : Eq × Ev) (ε τ : ℝ), ‖X‖ ≤ ε → 4 * ε ≤ δ → cm * h ^ 2 ≤ τ → τ ≤ cp * h ^ 2 →
      ∀ (d : Fin 8 → Eq) (b : ℝ),
      (∀ e : Fin 2, ∀ i : Fin 4,
        τ ^ (i : ℕ) * ‖W.ι (polyCurveDeriv i d (((e : ℕ) : ℝ) * τ))‖ ≤ b) →
      ∀ t ∈ Icc 0 τ,
        (∀ j, ‖W.ι (polyCurveDeriv j d t)‖ ≤ hermiteConst 3 j * b / τ ^ j) ∧
        (b ≤ cb * ε * τ ^ 2 * h ^ 5 →
          W.phase (W.hermiteC X τ + d) t ∈ ball 0 δ ∧
          ‖W.defect (W.hermiteC X τ + d) t - W.defect (W.hermiteC X τ) t‖ ≤ C * b / τ ^ 2 ∧
          ‖W.defectDeriv (W.hermiteC X τ + d) t - W.defectDeriv (W.hermiteC X τ) t‖ ≤
            C * b / τ ^ 3 ∧
          ‖W.defect (W.hermiteC X τ + d) t‖ ≤ C * ε * h ^ 5 ∧
          HasDerivAt (W.defect (W.hermiteC X τ + d)) (W.defectDeriv (W.hermiteC X τ + d) t) t ∧
          ‖W.defectDeriv (W.hermiteC X τ + d) t‖ ≤ C * ε * h ^ 3) := by
  obtain ⟨h₁, hh₁, C0, hC0, hres⟩ := hermite_residual_full.{uq, uv} A cm cp hA hcm hcp
  set c := max cp 1 with hcdef
  have hc1 : 1 ≤ c := le_max_right _ _
  have hcp' : cp ≤ c := le_max_left _ _
  set KH := ∑ j ∈ Finset.range 4, hermiteConst 3 j with hKH
  have hKH0 : 0 ≤ KH := Finset.sum_nonneg fun j _ => hermiteConst_nonneg 3 j
  have hKHj : ∀ j < 4, hermiteConst 3 j ≤ KH := fun j hj =>
    Finset.single_le_sum (f := fun j => hermiteConst 3 j) (fun j _ => hermiteConst_nonneg 3 j)
      (Finset.mem_range.mpr hj)
  set K1 := A * c * KH + KH with hK1
  have hK10 : 0 ≤ K1 := by positivity
  set D2 := KH + A * c * K1 with hD2
  set D3 := KH + A * c ^ 2 * K1 * C0 + A * c * K1 with hD3
  have hD20 : 0 ≤ D2 := by positivity
  have hD30 : 0 ≤ D3 := by positivity
  set C := C0 + D2 + D3 + (D2 * cb + D3 * cb / cm) with hCdef
  have hC : 0 ≤ C := by positivity
  refine ⟨min h₁ (1 / (2 * (K1 * cb * c) + 1)), lt_min hh₁ (by positivity), C, hC, ?_⟩
  intro Eq Ev _ _ _ _ _ _ W h δ hB hh0 X ε τ hX hεδ hτm hτp d b hb t ht
  have hh := hB.h_pos
  have hh1 := hB.h_le_one
  have hM := hB.M_pos
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hX
  have hε1 : ε ≤ 1 := by linarith [hB.δ_le_one]
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτm
  have hτc : τ ≤ c * h ^ 2 := hτp.trans (mul_le_mul_of_nonneg_right hcp' (by positivity))
  have hb0 : 0 ≤ b := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hb 0 0)
  -- clause 1
  have hd : ∀ j, ‖W.ι (polyCurveDeriv j d t)‖ ≤ hermiteConst 3 j * b / τ ^ j :=
    fun j => Writer.norm_ι_pert_le W d hτ0 hb j ht
  refine ⟨hd, fun hbs => ?_⟩
  -- the residual of `Q_X`
  obtain ⟨hQU, hDQ, -, hDDQ, hQn, hQv⟩ :=
    hres W h δ hB (hh0.trans (min_le_left _ _)) X ε τ hX hεδ hτm hτp t ht
  -- `h⁻¹ ≤ c / τ`
  have hhτ : h⁻¹ * τ ≤ c := by
    calc h⁻¹ * τ ≤ h⁻¹ * (c * h ^ 2) := mul_le_mul_of_nonneg_left hτc (by positivity)
      _ = c * h * (h⁻¹ * h) := by ring
      _ = c * h := by rw [inv_mul_cancel₀ hh.ne', mul_one]
      _ ≤ c := by nlinarith
  have hhinv : h⁻¹ ≤ c / τ := by rw [le_div_iff₀ hτ0]; exact hhτ
  have hdj : ∀ j < 4, ‖W.ι (polyCurveDeriv j d t)‖ ≤ KH * b / τ ^ j := fun j hj =>
    (hd j).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hKHj j hj) hb0)
      (by positivity))
  have hu : ‖W.u‖ ≤ c / τ * A := by
    calc ‖W.u‖ ≤ A * h⁻¹ := hB.norm_u
      _ ≤ A * (c / τ) := mul_le_mul_of_nonneg_left hhinv (by linarith)
      _ = c / τ * A := by ring
  -- phase and velocity changes
  have hph : ‖W.phase (W.hermiteC X τ + d) t - W.phase (W.hermiteC X τ) t‖ ≤ K1 * b / τ := by
    refine (Writer.phase_pert_le W _ d t).trans ?_
    have h0 := hdj 0 (by norm_num)
    have h1 := hdj 1 (by norm_num)
    simp only [pow_zero, div_one, pow_one] at h0 h1
    calc ‖W.u‖ * ‖W.ι (polyCurveDeriv 0 d t)‖ + ‖W.ι (polyCurveDeriv 1 d t)‖
        ≤ c / τ * A * (KH * b) + KH * b / τ :=
          add_le_add (mul_le_mul hu h0 (norm_nonneg _) (by positivity)) h1
      _ = K1 * b / τ := by rw [hK1]; field_simp
  have hvel : ‖W.phaseVel (W.hermiteC X τ + d) t - W.phaseVel (W.hermiteC X τ) t‖ ≤
      K1 * b / τ ^ 2 := by
    refine (Writer.phaseVel_pert_le W _ d t).trans ?_
    have h1 := hdj 1 (by norm_num)
    have h2 := hdj 2 (by norm_num)
    simp only [pow_one] at h1
    calc ‖W.u‖ * ‖W.ι (polyCurveDeriv 1 d t)‖ + ‖W.ι (polyCurveDeriv 2 d t)‖
        ≤ c / τ * A * (KH * b / τ) + KH * b / τ ^ 2 :=
          add_le_add (mul_le_mul hu h1 (norm_nonneg _) (by positivity)) h2
      _ = K1 * b / τ ^ 2 := by rw [hK1]; field_simp
  -- chart
  have hbτ : b / τ ≤ cb * c * ε * h ^ 7 := by
    rw [div_le_iff₀ hτ0]
    calc b ≤ cb * ε * τ ^ 2 * h ^ 5 := hbs
      _ = cb * ε * τ * h ^ 5 * τ := by ring
      _ ≤ cb * ε * (c * h ^ 2) * h ^ 5 * τ := by gcongr
      _ = cb * c * ε * h ^ 7 * τ := by ring
  have hsm : K1 * cb * c * h ^ 7 ≤ 1 / 2 := by
    have hh0b : h ≤ 1 / (2 * (K1 * cb * c) + 1) := hh0.trans (min_le_right _ _)
    have h0 : h * (2 * (K1 * cb * c) + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp hh0b
    have h7 : h ^ 7 ≤ h := by
      calc h ^ 7 = h * h ^ 6 := by ring
        _ ≤ h * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hh.le hh1) hh.le
        _ = h := mul_one h
    have : 0 ≤ K1 * cb * c := by positivity
    nlinarith
  have hQ'U : W.phase (W.hermiteC X τ + d) t ∈ ball 0 δ := by
    rw [mem_ball_zero_iff]
    calc ‖W.phase (W.hermiteC X τ + d) t‖
        = ‖W.phase (W.hermiteC X τ) t + (W.phase (W.hermiteC X τ + d) t -
            W.phase (W.hermiteC X τ) t)‖ := by congr 1; abel
      _ ≤ ‖W.phase (W.hermiteC X τ) t‖ + ‖W.phase (W.hermiteC X τ + d) t -
            W.phase (W.hermiteC X τ) t‖ := norm_add_le _ _
      _ ≤ 3 * ε + K1 * (b / τ) := by
          exact add_le_add hQn (hph.trans (le_of_eq (by ring)))
      _ ≤ 3 * ε + ε / 2 := by
          have := mul_le_mul_of_nonneg_left hbτ hK10
          have := mul_le_mul_of_nonneg_right hsm hε0
          nlinarith
      _ < δ := by linarith [hB.δ_pos]
  -- defect changes
  have hΔ2 : ‖W.defect (W.hermiteC X τ + d) t - W.defect (W.hermiteC X τ) t‖ ≤ D2 * b / τ ^ 2 := by
    refine (hB.defect_pert_le hQU hQ'U).trans ?_
    have h2 := hdj 2 (by norm_num)
    calc ‖W.ι (polyCurveDeriv 2 d t)‖ + A * h⁻¹ * ‖W.phase (W.hermiteC X τ + d) t -
          W.phase (W.hermiteC X τ) t‖ ≤ KH * b / τ ^ 2 + A * (c / τ) * (K1 * b / τ) :=
          add_le_add h2 (mul_le_mul (mul_le_mul_of_nonneg_left hhinv (by linarith)) hph
            (norm_nonneg _) (by positivity))
      _ = D2 * b / τ ^ 2 := by rw [hD2]; field_simp
  have hΔ3 : ‖W.defectDeriv (W.hermiteC X τ + d) t - W.defectDeriv (W.hermiteC X τ) t‖ ≤
      D3 * b / τ ^ 3 := by
    refine (hB.defectDeriv_pert_le hQU hQ'U).trans ?_
    have h3 := hdj 3 (by norm_num)
    have hv : ‖W.phaseVel (W.hermiteC X τ) t‖ ≤ C0 * (c / τ) := by
      calc ‖W.phaseVel (W.hermiteC X τ) t‖ ≤ C0 * h⁻¹ * ε := hQv
        _ ≤ C0 * h⁻¹ * 1 := mul_le_mul_of_nonneg_left hε1 (by positivity)
        _ ≤ C0 * (c / τ) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hhinv hC0
    have hAh : A * h⁻¹ ≤ A * (c / τ) := mul_le_mul_of_nonneg_left hhinv (by linarith)
    calc ‖W.ι (polyCurveDeriv 3 d t)‖ +
          A * h⁻¹ * ‖W.phase (W.hermiteC X τ + d) t - W.phase (W.hermiteC X τ) t‖ *
            ‖W.phaseVel (W.hermiteC X τ) t‖ +
          A * h⁻¹ * ‖W.phaseVel (W.hermiteC X τ + d) t - W.phaseVel (W.hermiteC X τ) t‖
        ≤ KH * b / τ ^ 3 + A * (c / τ) * (K1 * b / τ) * (C0 * (c / τ)) +
            A * (c / τ) * (K1 * b / τ ^ 2) := by
          refine add_le_add (add_le_add h3 ?_) ?_
          · exact mul_le_mul (mul_le_mul hAh hph (norm_nonneg _) (by positivity)) hv
              (norm_nonneg _) (by positivity)
          · exact mul_le_mul hAh hvel (norm_nonneg _) (by positivity)
      _ = D3 * b / τ ^ 3 := by rw [hD3]; field_simp; try ring
  -- final bounds
  have hb2 : b / τ ^ 2 ≤ cb * ε * h ^ 5 := by
    rw [div_le_iff₀ (by positivity)]
    calc b ≤ cb * ε * τ ^ 2 * h ^ 5 := hbs
      _ = cb * ε * h ^ 5 * τ ^ 2 := by ring
  have hb3 : b / τ ^ 3 ≤ cb / cm * ε * h ^ 3 := by
    rw [div_le_iff₀ (by positivity)]
    have : cm * h ^ 2 * h ^ 3 * τ ^ 2 ≤ τ * h ^ 3 * τ ^ 2 := by
      gcongr
    calc b ≤ cb * ε * τ ^ 2 * h ^ 5 := hbs
      _ = cb / cm * ε * (cm * h ^ 2 * h ^ 3 * τ ^ 2) := by field_simp
      _ ≤ cb / cm * ε * (τ * h ^ 3 * τ ^ 2) := by gcongr
      _ = cb / cm * ε * h ^ 3 * τ ^ 3 := by ring
  have hext1 : 0 ≤ D2 * cb := by positivity
  have hext2 : 0 ≤ D3 * cb / cm := by positivity
  have hCD2 : D2 ≤ C := by rw [hCdef]; linarith
  have hCD3 : D3 ≤ C := by rw [hCdef]; linarith
  refine ⟨hQ'U, hΔ2.trans ?_, hΔ3.trans ?_, ?_, W.hasDerivAt_defect hB.deriv.contDiffOn hQ'U, ?_⟩
  · rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hCD2 (by positivity)
  · rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hCD3 (by positivity)
  · calc ‖W.defect (W.hermiteC X τ + d) t‖
        ≤ ‖W.defect (W.hermiteC X τ) t‖ +
            ‖W.defect (W.hermiteC X τ + d) t - W.defect (W.hermiteC X τ) t‖ := by
          calc ‖W.defect (W.hermiteC X τ + d) t‖ = ‖W.defect (W.hermiteC X τ) t +
                (W.defect (W.hermiteC X τ + d) t - W.defect (W.hermiteC X τ) t)‖ := by
                congr 1; abel
            _ ≤ _ := norm_add_le _ _
      _ ≤ C0 * ε * h ^ 5 + D2 * (cb * ε * h ^ 5) := by
          refine add_le_add hDQ (hΔ2.trans ?_)
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hb2 hD20
      _ ≤ C * ε * h ^ 5 := by
          rw [hCdef]
          have : 0 ≤ ε * h ^ 5 := by positivity
          have : 0 ≤ D3 * ε * h ^ 5 := by positivity
          have : 0 ≤ D3 * cb / cm * (ε * h ^ 5) := by positivity
          have : 0 ≤ D2 * (ε * h ^ 5) := by positivity
          nlinarith
  · calc ‖W.defectDeriv (W.hermiteC X τ + d) t‖
        ≤ ‖W.defectDeriv (W.hermiteC X τ) t‖ +
            ‖W.defectDeriv (W.hermiteC X τ + d) t - W.defectDeriv (W.hermiteC X τ) t‖ := by
          calc ‖W.defectDeriv (W.hermiteC X τ + d) t‖ = ‖W.defectDeriv (W.hermiteC X τ) t +
                (W.defectDeriv (W.hermiteC X τ + d) t - W.defectDeriv (W.hermiteC X τ) t)‖ := by
                congr 1; abel
            _ ≤ _ := norm_add_le _ _
      _ ≤ C0 * ε * h ^ 3 + D3 * (cb / cm * ε * h ^ 3) := by
          refine add_le_add hDDQ (hΔ3.trans ?_)
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hb3 hD30
      _ ≤ C * ε * h ^ 3 := by
          rw [hCdef]
          have k0 : 0 ≤ (D2 + D3 + D2 * cb) * (ε * h ^ 3) := by positivity
          have k1 : D3 * (cb / cm * ε * h ^ 3) = D3 * cb / cm * (ε * h ^ 3) := by ring
          have k2 : (C0 + D2 + D3 + (D2 * cb + D3 * cb / cm)) * ε * h ^ 3 =
              C0 * ε * h ^ 3 + (D2 + D3 + D2 * cb) * (ε * h ^ 3) + D3 * cb / cm * (ε * h ^ 3) := by
            ring
          rw [k1, k2]
          linarith

end

end RenewalGeometry.TaylorHermiteResidual
