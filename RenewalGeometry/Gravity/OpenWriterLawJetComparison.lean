/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterLawDifference

/-!
# The `h`-gaining multiplier bound and the low jets of the law comparison
  (infrastructure for `thm:supp-law-einstein`, `eq:supp-law-jet-comparison`)

Let `X_B = (q_B, v_B)` solve the law-family writer `eq:supp-law-family` with mark `B`
(`‖B‖_op ≤ b ≤ 1/48`) and `X_0 = (q_0, v_0)` the central writer, with the same small initial
record.  Regarding the stencil on the `B`-trajectory as the external force
`f_B = -a(q_B)⁻¹ h² B Λ_h² q_B` of the central writer, the lower Sobolev orders gain one power of the
mesh (`lem:supp-law-multiplier`): `h² ‖Λ_h² q‖_{r,h} ≤ 18 h ‖q‖_{r+3,h}`.

* `sobNorm_lap2_mesh`: `h² ‖Λ_h² w‖_{r,h} ≤ 18 h ‖w‖_{r+3,h}` (one difference paid by the mesh,
  three by the order);
* `sobNorm_bTerm_mesh`, `Fnorm_lawForce_mesh`: `‖f_B‖_{s-2,h} ≤ C h ‖B‖ ‖X_B‖_{X^s_h}`;
* `law_jet_comparison_low`: the slots `j = 0, 1, 2` of `eq:supp-law-jet-comparison`,
  `‖q_B - q_0‖_{s-1,h} + ‖q_B' - q_0'‖_{s-2,h}` (jointly, `‖·‖_{X^{s-2}_h}`) and
  `‖q_B'' - q_0''‖_{s-3,h}`, bounded by `C h ‖B‖_op ‖X(0)‖_{X^s_h}` uniformly on the common
  lifespan.  The slot `j = 3` (a Lipschitz version of `jetDeriv_bound`) and the convergence clause
  (`thm:supp-open-einstein`) are not included.
-/

open Set Metric Filter Topology Finset MeasureTheory
open scoped NNReal BigOperators

namespace RenewalGeometry.OpenWriterLifespan

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterEnergyEstimate

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-- **The `h`-gaining multiplier bound** (`eq:supp-law-orders`, second estimate):
`h² ‖Λ_h² w‖_{r,h} ≤ 18 h ‖w‖_{r+3,h}`; one of the four differences is paid by the mesh, three by
the Sobolev order. -/
theorem sobNorm_lap2_mesh (r : ℕ) (w : PeriodicGridSobolev.Grid N → ℂ) :
    ((N : ℝ) ^ 2)⁻¹ * PeriodicGridSobolev.sobNorm r (lapC (lapC w)) ≤
      18 * (N : ℝ)⁻¹ * PeriodicGridSobolev.sobNorm (r + 3) w := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hij : ∀ i j, PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Dm i
      (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dm j (PeriodicGridSobolev.Dp j w)))) ≤
      2 * (N : ℝ) * PeriodicGridSobolev.sobNorm (r + 3) w := by
    intro i j
    have h1 := sobNorm_Dm_mesh r i (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dm j
      (PeriodicGridSobolev.Dp j w)))
    have h2 := PeriodicGridSobolev.CommutedRow.sobNorm_Dp_le r i
      (PeriodicGridSobolev.Dm j (PeriodicGridSobolev.Dp j w))
    have h3 := PeriodicGridSobolev.CommutedRow.sobNorm_Dm_le (r + 1) j (PeriodicGridSobolev.Dp j w)
    have h4 := PeriodicGridSobolev.CommutedRow.sobNorm_Dp_le (r + 2) j w
    have h0 : (0 : ℝ) ≤ 2 * N := by positivity
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans (h3.trans h4)) h0)
  rw [lapC_lapC]
  have hsum : PeriodicGridSobolev.sobNorm r (∑ i, ∑ j, PeriodicGridSobolev.Dm i
      (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dm j (PeriodicGridSobolev.Dp j w)))) ≤
      9 * (2 * (N : ℝ) * PeriodicGridSobolev.sobNorm (r + 3) w) := by
    refine (PeriodicGridSobolev.Moser.sobNorm_sum_le _ _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 2 * (N : ℝ) * PeriodicGridSobolev.sobNorm (r + 3) w :=
          sum_le_sum fun i _ => (PeriodicGridSobolev.Moser.sobNorm_sum_le _ _ _).trans
            (sum_le_sum fun j _ => hij i j)
      _ = _ := by simp; ring
  calc ((N : ℝ) ^ 2)⁻¹ * _ ≤ ((N : ℝ) ^ 2)⁻¹ *
        (9 * (2 * (N : ℝ) * PeriodicGridSobolev.sobNorm (r + 3) w)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 18 * (N : ℝ)⁻¹ * PeriodicGridSobolev.sobNorm (r + 3) w := by field_simp; ring

/-- The stencil of a mark gains one mesh power at two orders below the top:
`‖h² B Λ_h² q‖_{r,h} ≤ 288 b h ‖(q, v)‖_{X^{r+2}_h}`. -/
theorem sobNorm_bTerm_mesh (r : ℕ) {b : ℝ} {B : Upper → Upper → ℝ} (hB : IsMark b B)
    {q : Grid N → MetricRec} (hq : IsSymRec q) (v : Grid N → MetricRec) (k : Upper) :
    PeriodicGridSobolev.sobNorm r (cx (comp (bTerm B q) k.1.1 k.1.2)) ≤
      288 * b * (N : ℝ)⁻¹ * Xnorm (r + 2) q v := by
  have hb := hB.nonneg
  rw [cx_comp_bTerm]
  refine (PeriodicGridSobolev.Moser.sobNorm_sum_le _ _ _).trans ?_
  have hl : ∀ l : Upper, PeriodicGridSobolev.sobNorm r
      (((((N : ℝ) ^ 2)⁻¹ * B k l : ℝ) : ℂ) • lapC (lapC (cx (comp q l.1.1 l.1.2)))) ≤
      18 * b * (N : ℝ)⁻¹ * Xnorm (r + 2) q v := by
    intro l
    rw [PeriodicGridSobolev.Moser.sobNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((N : ℝ) ^ 2)⁻¹)]
    have h1 := sobNorm_lap2_mesh r (cx (comp q l.1.1 l.1.2))
    have h2 := sobNorm_q_le (r + 2) hq v l.1.1 l.1.2 (le_refl (r + 3))
    have h3 := hB.entry_le k l
    have hX := Xnorm_nonneg (r + 2) q v
    have hNi : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    calc ((N : ℝ) ^ 2)⁻¹ * |B k l| * PeriodicGridSobolev.sobNorm r
          (lapC (lapC (cx (comp q l.1.1 l.1.2)))) =
          |B k l| * (((N : ℝ) ^ 2)⁻¹ * PeriodicGridSobolev.sobNorm r
            (lapC (lapC (cx (comp q l.1.1 l.1.2))))) := by ring
      _ ≤ b * (18 * (N : ℝ)⁻¹ * Xnorm (r + 2) q v) := by
          refine mul_le_mul h3 (h1.trans ?_)
            (mul_nonneg (by positivity) (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _)) hb
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 18 * b * (N : ℝ)⁻¹ * Xnorm (r + 2) q v := by ring
  calc _ ≤ ∑ _l : Upper, 18 * b * (N : ℝ)⁻¹ * Xnorm (r + 2) q v := sum_le_sum fun l _ => hl l
    _ = (Fintype.card Upper : ℝ) * (18 * b * (N : ℝ)⁻¹ * Xnorm (r + 2) q v) := by simp
    _ ≤ 288 * b * (N : ℝ)⁻¹ * Xnorm (r + 2) q v := by
        have hc : (Fintype.card Upper : ℝ) ≤ 16 := by
          have h1 : Fintype.card Upper ≤ Fintype.card (Fin 4 × Fin 4) := Fintype.card_subtype_le _
          have h2 : Fintype.card (Fin 4 × Fin 4) = 16 := by simp
          exact_mod_cast h1.trans h2.le
        have := Xnorm_nonneg (r + 2) q v
        have h3 : 0 ≤ 18 * b * (N : ℝ)⁻¹ * Xnorm (r + 2) q v := by positivity
        calc (Fintype.card Upper : ℝ) * (18 * b * (N : ℝ)⁻¹ * Xnorm (r + 2) q v) ≤
              16 * (18 * b * (N : ℝ)⁻¹ * Xnorm (r + 2) q v) := mul_le_mul_of_nonneg_right hc h3
          _ = 288 * b * (N : ℝ)⁻¹ * Xnorm (r + 2) q v := by ring

/-- **The comparison force gains one mesh power**: for `r ≥ 2` there are `δ > 0`, `C ≥ 0`,
independent of the mesh and of the mark, such that on the chart `‖(q, v)‖_{X^{r+2}_h} ≤ δ`,
`‖-a(q)⁻¹ h² B Λ_h² q‖_{r,h} ≤ C h b ‖(q, v)‖_{X^{r+2}_h}` for every mark with `‖B‖_op ≤ b`. -/
theorem Fnorm_lawForce_mesh (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (b : ℝ) (B : Upper → Upper → ℝ)
      (q v : Grid N → MetricRec), IsMark b B → IsSymRec q → Xnorm (r + 2) q v ≤ δ →
      Fnorm r (lawForce B q) ≤ C * (N : ℝ)⁻¹ * b * Xnorm (r + 2) q v := by
  obtain ⟨δa, hδa, Ca, hCa, hma⟩ := moser_coefficients r hr
  set Ar := PeriodicGridSobolev.Moser.algConst r
  have hAr := PeriodicGridSobolev.Moser.algConst_pos r
  refine ⟨min (δa / 16) (1 / (16 * (Ca + 1))), by positivity, 16 * ((Ar + 1) * 288),
    by positivity, fun N _ b B q v hB hq hX => ?_⟩
  have hb := hB.nonneg
  set X := Xnorm (r + 2) q v
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  have hcsq : PeriodicGridSobolev.Moser.coordSum r bM q ≤ 16 * X :=
    coordSum_bM_q_le (r + 2) hq v (by omega)
  have hainv : PeriodicGridSobolev.sobNorm r
      (cx (fun x => (aArr q x)⁻¹) - fun _ => (1 : ℂ)) ≤ 1 := by
    have hM := hma N q (hcsq.trans (by linarith [hX.trans (min_le_left _ _)]))
    refine hM.2.1.trans ?_
    have h1 : X ≤ 1 / (16 * (Ca + 1)) := hX.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    calc Ca * PeriodicGridSobolev.Moser.coordSum r bM q ≤ Ca * (16 * X) :=
          mul_le_mul_of_nonneg_left hcsq hCa
      _ ≤ 1 := by nlinarith
  have hM : 0 ≤ (Ar + 1) * (288 * b * (N : ℝ)⁻¹ * X) := by positivity
  refine (lawDiff_Fnorm_le_of_comp_le r _ hM fun κ => ?_).trans (le_of_eq (by ring))
  have e : cx (comp (lawForce B q) κ.1.1 κ.1.2) =
      -(cx (fun x => (aArr q x)⁻¹) * cx (comp (bTerm B q) κ.1.1 κ.1.2)) := by
    funext x; simp [comp, cx, lawForce]
  rw [e, PeriodicGridSobolev.Moser.sobNorm_neg]
  refine (sobNorm_coef_mul_le r hr _ _ 1 (by simp) hainv).trans ?_
  exact mul_le_mul_of_nonneg_left (sobNorm_bTerm_mesh r hB hq v κ) (by positivity)

theorem isMark_zero_jet : IsMark (1 / 48) (fun _ _ : Upper => (0 : ℝ)) := by
  refine ⟨fun _ _ => rfl, fun ξ η => ?_⟩
  simp only [mul_zero, zero_mul, sum_const_zero, abs_zero]
  positivity

theorem lawAccel_zero_mark (q v : Grid N → MetricRec) :
    lawAccel (fun _ _ => 0) q v = harmonicWriterAcceleration q v := by
  funext x μ ν
  simp [lawAccel, lawForce, bTerm]

/-- Continuity of the comparison force along a history in the analytic chart. -/
theorem continuousOn_lawForce_of_chart (s : ℕ) (hs : 1 ≤ s) :
    ∃ ρ > 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ) (T : ℝ)
      (q v : ℝ → Grid N → MetricRec), (∀ t ∈ Icc 0 T, ContinuousAt q t) →
      (∀ t ∈ Icc 0 T, IsSymRec (q t)) → (∀ t ∈ Icc 0 T, Xnorm s (q t) (v t) ≤ ρ) →
      ContinuousOn (fun t => lawForce B (q t)) (Icc 0 T) := by
  obtain ⟨r₀, hr₀, hchart⟩ := exists_det_chart
  have hS := supConst_nonneg
  have hS1 : 0 < supConst + 1 := by linarith
  refine ⟨r₀ / (2 * (supConst + 1)), div_pos hr₀ (by linarith),
    fun N _ B T q v hqc hqs hX => ?_⟩
  intro t ht
  have hz : ∀ z, ‖(minkowski + q t z) - minkowski‖ < r₀ := by
    intro z
    rw [add_sub_cancel_left]
    have h1 := norm_q_le s hs (hqs t ht) (v t) z
    have h2 : supConst * Xnorm s (q t) (v t) ≤ supConst * (r₀ / (2 * (supConst + 1))) :=
      mul_le_mul_of_nonneg_left (hX t ht) hS
    have h3 : supConst * (r₀ / (2 * (supConst + 1))) < r₀ := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    exact lt_of_le_of_lt h1 (h2.trans_lt h3)
  have hcomp : ∀ x μ ν, ContinuousAt (fun τ => lawForce B (q τ) x μ ν) t := by
    intro x μ ν
    have hA : AnalyticAt ℝ (fun y : State N => lawAccel B y.1 y.2 x μ ν -
        harmonicWriterAcceleration y.1 y.2 x μ ν) (q t, 0) :=
      (analyticAt_lawAccel B (q t, 0) (fun z => (hchart _ (hz z)).1)
        (fun z => (hchart _ (hz z)).2) x μ ν).sub
        (analyticAt_accel (q t, 0) (fun z => (hchart _ (hz z)).1)
          (fun z => (hchart _ (hz z)).2) x μ ν)
    have hpath : ContinuousAt (fun τ => ((q τ, (0 : Grid N → MetricRec)) : State N)) t :=
      (hqc t ht).prodMk continuousAt_const
    have h := hA.continuousAt.comp_of_eq hpath rfl
    refine h.congr (Eventually.of_forall fun τ => ?_)
    simp [lawAccel]
  exact (continuousAt_pi.2 fun x => continuousAt_pi.2 fun μ => continuousAt_pi.2 fun ν =>
    hcomp x μ ν).continuousWithinAt

/-- **The low slots of the law jet comparison** (`eq:supp-law-jet-comparison`, `j = 0, 1, 2`).
For `s ≥ 5` there are `ε₀, T₀ > 0` and `C ≥ 0`, independent of the mesh and of the mark, such
that for every mark `B = Bᵀ`, `‖B‖_op ≤ b ≤ 1/48`, and all solutions `X_B` of the law writer and
`X_0` of the central writer on `[0, T₀]` with the same symmetric initial record of size
`ε = ‖X(0)‖_{X^s_h} ≤ ε₀`,
`‖(q_B - q_0, q_B' - q_0')(t)‖_{X^{s-2}_h} + ‖q_B''(t) - q_0''(t)‖_{s-3,h} ≤ C h b ε`
for `t ∈ [0, T₀]` (`q_B'' = V_{B,h}(q_B, q_B')`, `q_0'' = V_{0,h}(q_0, q_0')`; the first norm controls
`‖q_B - q_0‖_{s-1,h}` and `‖q_B' - q_0'‖_{s-2,h}`). -/
theorem law_jet_comparison_low (s : ℕ) (hs : 5 ≤ s) :
    ∃ ε₀ > 0, ∃ T₀ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (b : ℝ) (B : Upper → Upper → ℝ),
      IsMark b B → b ≤ 1 / 48 → ∀ qB vB q0 v0 : ℝ → Grid N → MetricRec,
      qB 0 = q0 0 → vB 0 = v0 0 → Xnorm s (q0 0) (v0 0) ≤ ε₀ →
      IsAccSolution (lawAccel B) T₀ qB vB → IsWriterSolution T₀ q0 v0 →
      ∀ t ∈ Icc 0 T₀, Xnorm (s - 2) (qB t - q0 t) (vB t - v0 t) +
        Fnorm (s - 3) (lawAccel B (qB t) (vB t) - harmonicWriterAcceleration (q0 t) (v0 t)) ≤
        C * (N : ℝ)⁻¹ * b * Xnorm s (q0 0) (v0 0) := by
  obtain ⟨εL, hεL, TL, hTL, CL, hCL, hL⟩ := law_lifespan s (by omega)
  obtain ⟨δW, hδW, KW, hKW, hW⟩ := open_writer_difference s (s - 2) (by omega) (by omega)
  obtain ⟨δK, hδK, KK, hKK, hK⟩ := dAcc_bound s (s - 2) (by omega) (by omega)
  obtain ⟨δF, hδF, CF, hCF, hF⟩ := Fnorm_lawForce_mesh (s - 2) (by omega)
  obtain ⟨ρc, hρc, hcont⟩ := continuousOn_lawForce_of_chart s (by omega)
  set ρ : ℝ := min (min δW δK) (min δF ρc)
  have hρ : 0 < ρ := by positivity
  set C₁ : ℝ := 2 * Real.exp (KW * TL) * KW * TL * (CF * CL)
  have hC₁ : 0 ≤ C₁ := by positivity
  refine ⟨min εL (ρ / (CL + 1)), by positivity, TL, hTL, C₁ + 16 * (KK * (C₁ + CF * CL)),
    by positivity, fun N _ b B hB hb qB vB q0 v0 hq0 hv0 hε hsolB hsol0 => ?_⟩
  have hb0 := hB.nonneg
  have hB' : IsMark (1 / 48) B := hB.mono hb
  set ε := Xnorm s (q0 0) (v0 0)
  have hε0 : 0 ≤ ε := Xnorm_nonneg _ _ _
  have hNi : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hsol0' : IsAccSolution (lawAccel (fun _ _ => 0)) TL q0 v0 := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hsol0 t ht
    exact ⟨h1, h2, h3, fun x κ => by rw [lawAccel_zero_mark]; exact h4 x κ⟩
  have h0mem : (0 : ℝ) ∈ Icc 0 TL := ⟨le_rfl, hTL.le⟩
  obtain ⟨hs0q, hs0v, -, -⟩ := hsol0 0 h0mem
  -- the chart bounds of both histories (uniqueness of the lifespan solutions)
  have hCLε : CL * ε ≤ ρ := by
    have h1 : ε ≤ ρ / (CL + 1) := hε.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hchartB : ∀ t ∈ Icc 0 TL, Xnorm s (qB t) (vB t) ≤ CL * ε := by
    obtain ⟨⟨q, v, hq, hv, hsol, hbd⟩, huniq⟩ := hL N B hB' (q0 0) (v0 0) hs0q hs0v
      (hε.trans (min_le_left _ _))
    intro t ht
    obtain ⟨e1, e2⟩ := huniq qB vB q v hq0 hv0 hq hv hsolB hsol t ht
    rw [e1, e2]; exact hbd t ht
  have hchart0 : ∀ t ∈ Icc 0 TL, Xnorm s (q0 t) (v0 t) ≤ CL * ε := by
    obtain ⟨⟨q, v, hq, hv, hsol, hbd⟩, huniq⟩ := hL N (fun _ _ => 0) isMark_zero_jet
      (q0 0) (v0 0) hs0q hs0v (hε.trans (min_le_left _ _))
    intro t ht
    obtain ⟨e1, e2⟩ := huniq q0 v0 q v rfl rfl hq hv hsol0' hsol t ht
    rw [e1, e2]; exact hbd t ht
  -- the comparison force
  have hforce : ∀ t ∈ Icc 0 TL, Fnorm (s - 2) (lawForce B (qB t)) ≤ CF * CL * (N : ℝ)⁻¹ * b * ε := by
    intro t ht
    obtain ⟨hqs, -, -, -⟩ := hsolB t ht
    have hX : Xnorm (s - 2 + 2) (qB t) (vB t) ≤ CL * ε := by
      rw [show s - 2 + 2 = s by omega]; exact hchartB t ht
    have h := hF N b B (qB t) (vB t) hB hqs (hX.trans (hCLε.trans
      ((min_le_right _ _).trans (min_le_left _ _))))
    rw [show s - 2 + 2 = s by omega] at h
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_left (hchartB t ht) (by positivity :
      (0 : ℝ) ≤ CF * (N : ℝ)⁻¹ * b)
    nlinarith
  -- the forced pair
  have hpair : IsForcedPair s δW TL qB q0 vB v0 (fun t => lawForce B (qB t)) (fun _ => 0) := by
    intro t ht
    obtain ⟨hqs, hvs, hq, hv⟩ := hsolB t ht
    obtain ⟨hq0s, hv0s, hq0d, hv0d⟩ := hsol0 t ht
    refine ⟨hqs, hvs, hq0s, hv0s, hq, hq0d, fun x κ => hv x κ, fun x κ => ?_,
      (hchartB t ht).trans (hCLε.trans ((min_le_left _ _).trans (min_le_left _ _))),
      (hchart0 t ht).trans (hCLε.trans ((min_le_left _ _).trans (min_le_left _ _)))⟩
    refine (hv0d x κ).congr_deriv ?_
    simp
  have hfc : ContinuousOn (fun t => lawForce B (qB t)) (Icc 0 TL) :=
    hcont N B TL qB vB (fun t ht => continuousAt_pi.2 fun x => ((hsolB t ht).2.2.1 x).continuousAt)
      (fun t ht => (hsolB t ht).1)
      (fun t ht => (hchartB t ht).trans (hCLε.trans ((min_le_right _ _).trans (min_le_right _ _))))
  intro t ht
  have hd := hW N TL qB q0 vB v0 (fun t => lawForce B (qB t)) (fun _ => 0) hpair hfc
    continuousOn_const t ht
  have hinit : Xnorm (s - 2) (qB 0 - q0 0) (vB 0 - v0 0) = 0 := by
    rw [hq0, hv0, sub_self, sub_self]
    have : Xsq (s - 2) (0 : Grid N → MetricRec) 0 = 0 := by
      unfold Xsq
      refine sum_eq_zero fun κ _ => ?_
      have e : cx (comp (0 : Grid N → MetricRec) κ.1.1 κ.1.2) = 0 := by
        funext x; simp [comp, cx]
      rw [e]
      simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
    rw [Xnorm, this, Real.sqrt_zero]
  rw [hinit, mul_zero, zero_add] at hd
  have hint : (∫ τ in (0)..t, Fnorm (s - 2) (lawForce B (qB τ) - (fun _ => 0) τ)) ≤
      TL * (CF * CL * (N : ℝ)⁻¹ * b * ε) := by
    have hcI : ContinuousOn (fun τ => Fnorm (s - 2) (lawForce B (qB τ) - (fun _ => 0) τ))
        (Icc 0 t) := by
      have : (fun τ => Fnorm (s - 2) (lawForce B (qB τ) - (fun _ => (0 : Grid N → MetricRec)) τ)) =
          fun τ => Fnorm (s - 2) (lawForce B (qB τ)) := by funext τ; simp
      rw [this]
      exact (continuous_Fnorm (s - 2)).comp_continuousOn
        (hfc.mono (Icc_subset_Icc le_rfl ht.2))
    have h1 := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht.1
      (hcI.intervalIntegrable_of_Icc ht.1)
      (intervalIntegrable_const (μ := MeasureTheory.volume)) (fun τ hτ => by
        have := hforce τ ⟨hτ.1, hτ.2.trans ht.2⟩
        simpa using this)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    have h2 : 0 ≤ CF * CL * (N : ℝ)⁻¹ * b * ε := by positivity
    calc _ ≤ t * (CF * CL * (N : ℝ)⁻¹ * b * ε) := h1
      _ ≤ TL * (CF * CL * (N : ℝ)⁻¹ * b * ε) := mul_le_mul_of_nonneg_right ht.2 h2
  have hX2 : Xnorm (s - 2) (qB t - q0 t) (vB t - v0 t) ≤ C₁ * (N : ℝ)⁻¹ * b * ε := by
    refine hd.trans ?_
    have hexp : Real.exp (KW * t) ≤ Real.exp (KW * TL) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hKW)
    have hI0 : 0 ≤ ∫ τ in (0)..t, Fnorm (s - 2) (lawForce B (qB τ) - (fun _ => 0) τ) :=
      intervalIntegral.integral_nonneg ht.1 fun τ _ => Fnorm_nonneg _ _
    calc 2 * Real.exp (KW * t) * (KW * ∫ τ in (0)..t,
          Fnorm (s - 2) (lawForce B (qB τ) - (fun _ => 0) τ)) ≤
          2 * Real.exp (KW * TL) * (KW * (TL * (CF * CL * (N : ℝ)⁻¹ * b * ε))) := by
          have := mul_nonneg hKW hI0
          gcongr
      _ = C₁ * (N : ℝ)⁻¹ * b * ε := by simp only [C₁]; ring
  -- the second slot
  have hacc : Fnorm (s - 3) (lawAccel B (qB t) (vB t) - harmonicWriterAcceleration (q0 t) (v0 t)) ≤
      16 * (KK * ((C₁ + CF * CL) * (N : ℝ)⁻¹ * b * ε)) := by
    have hM : 0 ≤ KK * ((C₁ + CF * CL) * (N : ℝ)⁻¹ * b * ε) := by positivity
    refine lawDiff_Fnorm_le_of_comp_le (s - 3) _ hM fun κ => ?_
    obtain ⟨hqs, hvs, -, -⟩ := hsolB t ht
    obtain ⟨hq0s, hv0s, -, -⟩ := hsol0 t ht
    have e : lawAccel B (qB t) (vB t) - harmonicWriterAcceleration (q0 t) (v0 t) =
        dAcc (qB t) (q0 t) (vB t) (v0 t) (lawForce B (qB t)) 0 := by
      funext x μ ν
      simp [dAcc, lawAccel]
    rw [e]
    have h := hK N (qB t) (q0 t) (vB t) (v0 t) (lawForce B (qB t)) 0 hqs hq0s hvs hv0s
      ((hchartB t ht).trans (hCLε.trans ((min_le_left _ _).trans (min_le_right _ _))))
      ((hchart0 t ht).trans (hCLε.trans ((min_le_left _ _).trans (min_le_right _ _)))) κ
    rw [show s - 2 - 1 = s - 3 by omega, sub_zero] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hKK)
    have := hforce t ht
    nlinarith
  calc _ ≤ C₁ * (N : ℝ)⁻¹ * b * ε + 16 * (KK * ((C₁ + CF * CL) * (N : ℝ)⁻¹ * b * ε)) :=
        add_le_add hX2 hacc
    _ = (C₁ + 16 * (KK * (C₁ + CF * CL))) * (N : ℝ)⁻¹ * b * ε := by ring

/-- Non-vacuity of `law_jet_comparison_low`: the flat histories of both writers with the zero
record satisfy its hypotheses for every mesh. -/
example (s : ℕ) (hs : 5 ≤ s) : True := by
  obtain ⟨ε₀, hε₀, T₀, hT₀, C, hC, h⟩ := law_jet_comparison_low s hs
  have hsolB : IsAccSolution (lawAccel (fun _ _ => 0)) T₀ (fun _ => (0 : Grid 5 → MetricRec))
      (fun _ => 0) := by
    intro t _
    refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun x => hasDerivAt_const _ _, fun x κ => ?_⟩
    show HasDerivAt _ (lawAccel (fun _ _ => 0) (0 : Grid 5 → MetricRec) 0 x κ.1.1 κ.1.2) t
    rw [lawAccel_zero_mark, harmonicWriterAcceleration_zero]
    exact hasDerivAt_const _ _
  have hsol0 : IsWriterSolution T₀ (fun _ => (0 : Grid 5 → MetricRec)) (fun _ => 0) := by
    intro t _
    refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun x => hasDerivAt_const _ _, fun x κ => ?_⟩
    show HasDerivAt _ (harmonicWriterAcceleration (0 : Grid 5 → MetricRec) 0 x κ.1.1 κ.1.2) t
    rw [harmonicWriterAcceleration_zero]
    exact hasDerivAt_const _ _
  have hX : Xnorm s (0 : Grid 5 → MetricRec) 0 ≤ ε₀ := by
    have : Xsq s (0 : Grid 5 → MetricRec) 0 = 0 := by
      unfold Xsq
      refine sum_eq_zero fun κ _ => ?_
      have e : cx (comp (0 : Grid 5 → MetricRec) κ.1.1 κ.1.2) = 0 := by funext x; simp [comp, cx]
      rw [e]
      simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
    rw [Xnorm, this, Real.sqrt_zero]; exact hε₀.le
  have := h 5 (1 / 48) (fun _ _ => 0) isMark_zero_jet le_rfl (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) rfl rfl hX hsolB hsol0 0 ⟨le_rfl, hT₀.le⟩
  trivial

end

end RenewalGeometry.OpenWriterLifespan
