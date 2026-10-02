/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterLawJetComparison
import RenewalGeometry.Gravity.OpenWriterTimeJets

/-!
# The full law jet comparison (`thm:supp-law-einstein`, `eq:supp-law-jet-comparison`)

Let `X_B = (q_B, v_B)` solve the law-family writer `eq:supp-law-family` with a mark `B`
(`B = Bᵀ`, `‖B‖_op ≤ b ≤ 1/48`) and `X_0 = (q_0, v_0)` the central writer, from the same small
record.  This file adds the slot `j = 3` of `eq:supp-law-jet-comparison` to the slots
`j = 0, 1, 2` of `law_jet_comparison_low`.

* `lawJet_moser_lipschitz_rates`, `lawJet_moser_lipschitz_compensator_rate`: Lipschitz Moser
  bounds for the coefficient rates `ȧ, ċ, ḃ` and for the compensator differential `D𝖦(w)[w']`;
* `lawJet_divArr_sub_le`, `lawJet_skew_sub_le`: difference bounds for the flux and the skew
  transport with a near-constant coefficient;
* `jetDeriv_lipschitz`: the Lipschitz version of `jetDeriv_bound` one order lower,
  `‖q_ttt - p_ttt‖_{s-4,h} ≤ K (‖(q - p, v - w)‖_{X^{s-2}_h} + ‖W - W'‖_{s-3,h})`;
* `law_jet_comparison`: all four slots `j = 0, 1, 2, 3` of `eq:supp-law-jet-comparison`, on any
  horizon, for histories in a common top chart.

The Einstein-limit clause is in `OpenWriterLawEinsteinLimit.lean`.
-/

open Set Metric Filter Topology Finset MeasureTheory
open scoped NNReal BigOperators

namespace RenewalGeometry.OpenWriterLifespan

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterEnergyEstimate

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

theorem lawJet_cx_sub_eq (a b : Grid N → ℝ) : cx a - cx b = fun x => ((a x - b x : ℝ) : ℂ) := by
  funext x; simp [cx]

theorem lawJet_coordSum_bP_sub (r : ℕ) (q v p w : Grid N → MetricRec) :
    PeriodicGridSobolev.Moser.coordSum r bP ((fun x => (q x, v x)) - fun x => (p x, w x)) =
      PeriodicGridSobolev.Moser.coordSum r bM (q - p) +
        PeriodicGridSobolev.Moser.coordSum r bM (v - w) := by
  rw [← coordSum_bP]
  rfl

theorem lawJet_coordSum_bJP_sub (r : ℕ) (u u' p p' : Grid N → JetSpace) :
    PeriodicGridSobolev.Moser.coordSum r bJP ((fun x => (u x, u' x)) - fun x => (p x, p' x)) =
      PeriodicGridSobolev.Moser.coordSum r bJ (u - p) +
        PeriodicGridSobolev.Moser.coordSum r bJ (u' - p') := by
  rw [← coordSum_bJP]
  rfl

/-- **Lipschitz Moser bounds for the coefficient rates** `ȧ = Da(g)[v]`, `ċ`, `ḃ`:
`‖ȧ(q, v) - ȧ(p, w)‖_{r,h} ≤ C (S_r(q - p) + S_r(v - w))` on a mesh-independent ball. -/
theorem lawJet_moser_lipschitz_rates (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (q v p w : Grid N → MetricRec),
      PeriodicGridSobolev.Moser.coordSum r bM q + PeriodicGridSobolev.Moser.coordSum r bM v ≤ δ →
      PeriodicGridSobolev.Moser.coordSum r bM p + PeriodicGridSobolev.Moser.coordSum r bM w ≤ δ →
      PeriodicGridSobolev.sobNorm r (cx (adot q v) - cx (adot p w)) ≤
          C * (PeriodicGridSobolev.Moser.coordSum r bM (q - p) +
            PeriodicGridSobolev.Moser.coordSum r bM (v - w)) ∧
      (∀ i j, PeriodicGridSobolev.sobNorm r (cx (cdot q v i j) - cx (cdot p w i j)) ≤
          C * (PeriodicGridSobolev.Moser.coordSum r bM (q - p) +
            PeriodicGridSobolev.Moser.coordSum r bM (v - w))) ∧
      ∀ i, PeriodicGridSobolev.sobNorm r (cx (bdot q v i) - cx (bdot p w i)) ≤
          C * (PeriodicGridSobolev.Moser.coordSum r bM (q - p) +
            PeriodicGridSobolev.Moser.coordSum r bM (v - w)) := by
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
      (u u' : Grid N → MetricRec × MetricRec), PeriodicGridSobolev.Moser.coordSum r bP u ≤ δ →
      PeriodicGridSobolev.Moser.coordSum r bP u' ≤ δ →
      PeriodicGridSobolev.sobNorm r (fun x =>
        ((fderiv ℝ (F k) (minkowski + ((0 : MetricRec × MetricRec) + u x).1)
            ((0 : MetricRec × MetricRec) + u x).2 -
          fderiv ℝ (F k) (minkowski + ((0 : MetricRec × MetricRec) + u' x).1)
            ((0 : MetricRec × MetricRec) + u' x).2 : ℝ) : ℂ))
        ≤ C * PeriodicGridSobolev.Moser.coordSum r bP (u - u'))
    (fun k δ δ' C C' _ hδ' hC' hP N _ u u' hu hu' =>
      (hP N u u' (hu.trans hδ') (hu'.trans hδ')).trans
      (by gcongr; exact PeriodicGridSobolev.Moser.coordSum_nonneg _ _ _))
    (fun k => by
      obtain ⟨pp, R, hp⟩ := analyticAt_rate (hF k)
      exact PeriodicGridSobolev.Moser.moser_lipschitz r hr bP
        (A := fun z : MetricRec × MetricRec => fderiv ℝ (F k) (minkowski + z.1) z.2) hp)
  refine ⟨δ, hδ, C, hC, fun N _ q v p w hqv hpw => ?_⟩
  have hu := (coordSum_bP r q v).symm ▸ hqv
  have hu' := (coordSum_bP r p w).symm ▸ hpw
  have key : ∀ k, PeriodicGridSobolev.sobNorm r
      (fun x => ((fderiv ℝ (F k) (minkowski + q x) (v x) -
        fderiv ℝ (F k) (minkowski + p x) (w x) : ℝ) : ℂ)) ≤
      C * (PeriodicGridSobolev.Moser.coordSum r bM (q - p) +
        PeriodicGridSobolev.Moser.coordSum r bM (v - w)) := by
    intro k
    have := h k N (fun x => (q x, v x)) (fun x => (p x, w x)) hu hu'
    rw [lawJet_coordSum_bP_sub] at this
    convert this using 2
    funext x
    simp
  refine ⟨?_, fun i j => ?_, fun i => ?_⟩
  · rw [lawJet_cx_sub_eq]; exact key (Sum.inl 0)
  · rw [lawJet_cx_sub_eq]; exact key (Sum.inr (Sum.inl (i, j)))
  · rw [lawJet_cx_sub_eq]; exact key (Sum.inr (Sum.inr i))

/-- **Lipschitz Moser bound for the compensator differential**:
`‖D𝖦(u)[u'] - D𝖦(p)[p']‖_{r,h} ≤ C (S_r(u - p) + S_r(u' - p'))`. -/
theorem lawJet_moser_lipschitz_compensator_rate (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (u u' p p' : Grid N → JetSpace),
      PeriodicGridSobolev.Moser.coordSum r bJ u + PeriodicGridSobolev.Moser.coordSum r bJ u' ≤ δ →
      PeriodicGridSobolev.Moser.coordSum r bJ p + PeriodicGridSobolev.Moser.coordSum r bJ p' ≤ δ →
      ∀ μ ν : Fin 4, PeriodicGridSobolev.sobNorm r
        ((fun x => ((fderiv ℝ (fun z : JetSpace => compensatorMap z μ ν) (u x) (u' x) : ℝ) : ℂ)) -
          fun x => ((fderiv ℝ (fun z : JetSpace => compensatorMap z μ ν) (p x) (p' x) : ℝ) : ℂ)) ≤
        C * (PeriodicGridSobolev.Moser.coordSum r bJ (u - p) +
          PeriodicGridSobolev.Moser.coordSum r bJ (u' - p')) := by
  obtain ⟨δ, hδ, C, hC, h⟩ := uniformize (ι := Fin 4 × Fin 4) (fun k δ C => ∀ (N : ℕ) [NeZero N]
      (y y' : Grid N → JetSpace × JetSpace), PeriodicGridSobolev.Moser.coordSum r bJP y ≤ δ →
      PeriodicGridSobolev.Moser.coordSum r bJP y' ≤ δ →
      PeriodicGridSobolev.sobNorm r (fun x =>
        ((fderiv ℝ (fun z : JetSpace => compensatorMap z k.1 k.2)
            ((0 : JetSpace × JetSpace) + y x).1 ((0 : JetSpace × JetSpace) + y x).2 -
          fderiv ℝ (fun z : JetSpace => compensatorMap z k.1 k.2)
            ((0 : JetSpace × JetSpace) + y' x).1 ((0 : JetSpace × JetSpace) + y' x).2 : ℝ) : ℂ))
        ≤ C * PeriodicGridSobolev.Moser.coordSum r bJP (y - y'))
    (fun k δ δ' C C' _ hδ' hC' hP N _ y y' hy hy' =>
      (hP N y y' (hy.trans hδ') (hy'.trans hδ')).trans
      (by gcongr; exact PeriodicGridSobolev.Moser.coordSum_nonneg _ _ _))
    (fun k => by
      obtain ⟨pp, R, hp⟩ := analyticAt_compensator_rate k.1 k.2
      exact PeriodicGridSobolev.Moser.moser_lipschitz r hr bJP
        (A := fun z : JetSpace × JetSpace =>
          fderiv ℝ (fun w : JetSpace => compensatorMap w k.1 k.2) z.1 z.2) hp)
  refine ⟨δ, hδ, C, hC, fun N _ u u' p p' hu hp μ ν => ?_⟩
  have hy := (coordSum_bJP r u u').symm ▸ hu
  have hy' := (coordSum_bJP r p p').symm ▸ hp
  have := h (μ, ν) N (fun x => (u x, u' x)) (fun x => (p x, p' x)) hy hy'
  rw [lawJet_coordSum_bJP_sub] at this
  convert this using 2
  funext x
  simp

/-- Product difference: `‖f g - f' g'‖_{r,h} ≤ A_r (‖f - f'‖ ‖g‖ + ‖f'‖ ‖g - g'‖)`. -/
theorem lawJet_sobNorm_mul_sub_le (r : ℕ) (hr : 2 ≤ r) (f g f' g' : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.sobNorm r (f * g - f' * g') ≤
      PeriodicGridSobolev.Moser.algConst r * (PeriodicGridSobolev.sobNorm r (f - f') *
        PeriodicGridSobolev.sobNorm r g + PeriodicGridSobolev.sobNorm r f' *
          PeriodicGridSobolev.sobNorm r (g - g')) := by
  have e : f * g - f' * g' = (f - f') * g + f' * (g - g') := by ring
  rw [e]
  refine (PeriodicGridSobolev.Moser.sobNorm_add_le _ _ _).trans ?_
  have h1 := PeriodicGridSobolev.Moser.sobNorm_mul_le r hr (f - f') g
  have h2 := PeriodicGridSobolev.Moser.sobNorm_mul_le r hr f' (g - g')
  nlinarith

/-- Difference of a near-constant coefficient product:
`‖c w - c' w'‖_{r,h} ≤ (A_r + 1) ‖w - w'‖ + A_r ‖c - c'‖ ‖w'‖` when `‖c - d‖_{r,h} ≤ 1`, `|d| ≤ 1`. -/
theorem lawJet_coef_mul_sub_le (r : ℕ) (hr : 2 ≤ r) (c c' w w' : PeriodicGridSobolev.Grid N → ℂ)
    (d : ℂ) (hd : ‖d‖ ≤ 1) (hc : PeriodicGridSobolev.sobNorm r (c - fun _ => d) ≤ 1) :
    PeriodicGridSobolev.sobNorm r (c * w - c' * w') ≤
      (PeriodicGridSobolev.Moser.algConst r + 1) * PeriodicGridSobolev.sobNorm r (w - w') +
        PeriodicGridSobolev.Moser.algConst r * PeriodicGridSobolev.sobNorm r (c - c') *
          PeriodicGridSobolev.sobNorm r w' := by
  have e : c * w - c' * w' = c * (w - w') + (c - c') * w' := by ring
  rw [e]
  refine (PeriodicGridSobolev.Moser.sobNorm_add_le _ _ _).trans ?_
  have h1 := sobNorm_coef_mul_le r hr c (w - w') d hd hc
  have h2 := PeriodicGridSobolev.Moser.sobNorm_mul_le r hr (c - c') w'
  linarith

/-- **Difference of the divergence flux** with a near-constant coefficient. -/
theorem lawJet_divArr_sub_le (r : ℕ) (hr : 2 ≤ r)
    (c c' : Fin 3 → Fin 3 → PeriodicGridSobolev.Grid N → ℂ) (Q Q' : PeriodicGridSobolev.Grid N → ℂ)
    (d : Fin 3 → Fin 3 → ℂ) (hd : ∀ i j, ‖d i j‖ ≤ 1)
    (hc : ∀ i j, PeriodicGridSobolev.sobNorm (r + 1) (c i j - fun _ => d i j) ≤ 1)
    {Dc MQ DQ : ℝ} (hDc : ∀ i j, PeriodicGridSobolev.sobNorm (r + 1) (c i j - c' i j) ≤ Dc)
    (hMQ : PeriodicGridSobolev.sobNorm (r + 2) Q' ≤ MQ)
    (hDQ : PeriodicGridSobolev.sobNorm (r + 2) (Q - Q') ≤ DQ) :
    PeriodicGridSobolev.sobNorm r
      ((∑ i, ∑ j, PeriodicGridSobolev.Dm i (c i j * PeriodicGridSobolev.Dp j Q)) -
        ∑ i, ∑ j, PeriodicGridSobolev.Dm i (c' i j * PeriodicGridSobolev.Dp j Q')) ≤
      9 * ((PeriodicGridSobolev.Moser.algConst (r + 1) + 1) * DQ +
        PeriodicGridSobolev.Moser.algConst (r + 1) * Dc * MQ) := by
  open PeriodicGridSobolev PeriodicGridSobolev.Moser PeriodicGridSobolev.CommutedRow in
  have hA := algConst_pos (r + 1)
  have hij : ∀ i j, sobNorm r (Dm i (c i j * Dp j Q) - Dm i (c' i j * Dp j Q')) ≤
      (algConst (r + 1) + 1) * DQ + algConst (r + 1) * Dc * MQ := by
    intro i j
    have e : Dm i (c i j * Dp j Q) - Dm i (c' i j * Dp j Q') =
        Dm i (c i j * Dp j Q - c' i j * Dp j Q') := by
      rw [map_sub]
    rw [e]
    refine (sobNorm_Dm_le r i _).trans ?_
    refine (lawJet_coef_mul_sub_le (r + 1) (by omega) _ _ _ _ (d i j) (hd i j) (hc i j)).trans ?_
    have h1 : sobNorm (r + 1) (Dp j Q - Dp j Q') ≤ DQ := by
      rw [← map_sub]; exact (sobNorm_Dp_le (r + 1) j _).trans hDQ
    have h2 : sobNorm (r + 1) (Dp j Q') ≤ MQ := (sobNorm_Dp_le (r + 1) j _).trans hMQ
    have h3 := hDc i j
    have h0 := sobNorm_nonneg (r + 1) (c i j - c' i j)
    have h4 := sobNorm_nonneg (r + 1) (Dp j Q')
    have : algConst (r + 1) * sobNorm (r + 1) (c i j - c' i j) * sobNorm (r + 1) (Dp j Q') ≤
        algConst (r + 1) * Dc * MQ := by
      have hDc0 : 0 ≤ Dc := h0.trans h3
      gcongr
    nlinarith
  rw [← Finset.sum_sub_distrib]
  refine (sobNorm_sum_le _ _ _).trans ?_
  calc ∑ i, sobNorm r (∑ j, Dm i (c i j * Dp j Q) - ∑ j, Dm i (c' i j * Dp j Q'))
      ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ((algConst (r + 1) + 1) * DQ + algConst (r + 1) * Dc * MQ) := by
        refine sum_le_sum fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact (sobNorm_sum_le _ _ _).trans (sum_le_sum fun j _ => hij i j)
    _ = _ := by simp; ring

/-- **Difference of the skew transport** with a near-constant coefficient. -/
theorem lawJet_skew_sub_le (r : ℕ) (hr : 2 ≤ r)
    (b b' : Fin 3 → PeriodicGridSobolev.Grid N → ℂ) (V V' : PeriodicGridSobolev.Grid N → ℂ)
    (d : Fin 3 → ℂ) (hd : ∀ i, ‖d i‖ ≤ 1)
    (hb : ∀ i, PeriodicGridSobolev.sobNorm (r + 1) (b i - fun _ => d i) ≤ 1)
    {Db MV DV : ℝ} (hDb : ∀ i, PeriodicGridSobolev.sobNorm (r + 1) (b i - b' i) ≤ Db)
    (hMV : PeriodicGridSobolev.sobNorm (r + 1) V' ≤ MV)
    (hDV : PeriodicGridSobolev.sobNorm (r + 1) (V - V') ≤ DV) :
    PeriodicGridSobolev.sobNorm r
      ((∑ i, (b i * PeriodicGridSobolev.D0 i V + PeriodicGridSobolev.D0 i (b i * V))) -
        ∑ i, (b' i * PeriodicGridSobolev.D0 i V' + PeriodicGridSobolev.D0 i (b' i * V'))) ≤
      3 * ((PeriodicGridSobolev.Moser.algConst r + 1 +
          (PeriodicGridSobolev.Moser.algConst (r + 1) + 1)) * DV +
        (PeriodicGridSobolev.Moser.algConst r + PeriodicGridSobolev.Moser.algConst (r + 1)) *
          Db * MV) := by
  open PeriodicGridSobolev PeriodicGridSobolev.Moser PeriodicGridSobolev.CommutedRow in
  have hA := algConst_pos r
  have hA1 := algConst_pos (r + 1)
  have hi : ∀ i, sobNorm r ((b i * D0 i V + D0 i (b i * V)) - (b' i * D0 i V' + D0 i (b' i * V'))) ≤
      (algConst r + 1 + (algConst (r + 1) + 1)) * DV + (algConst r + algConst (r + 1)) * Db * MV := by
    intro i
    have e : (b i * D0 i V + D0 i (b i * V)) - (b' i * D0 i V' + D0 i (b' i * V')) =
        (b i * D0 i V - b' i * D0 i V') + D0 i (b i * V - b' i * V') := by
      rw [map_sub]; ring
    rw [e]
    refine (sobNorm_add_le _ _ _).trans ?_
    have hbr : sobNorm r (b i - fun _ => d i) ≤ 1 := (sobNorm_mono (by omega) _).trans (hb i)
    have h1 := lawJet_coef_mul_sub_le r hr (b i) (b' i) (D0 i V) (D0 i V') (d i) (hd i) hbr
    have h2 := lawJet_coef_mul_sub_le (r + 1) (by omega) (b i) (b' i) V V' (d i) (hd i) (hb i)
    have h3 : sobNorm r (D0 i V - D0 i V') ≤ DV := by
      rw [← map_sub]; exact (sobNorm_D0_le r i _).trans hDV
    have h4 : sobNorm r (D0 i V') ≤ MV := (sobNorm_D0_le r i _).trans hMV
    have h5 : sobNorm r (b i - b' i) ≤ Db := (sobNorm_mono (by omega) _).trans (hDb i)
    have h6 := sobNorm_D0_le r i (b i * V - b' i * V')
    have n1 := sobNorm_nonneg r (b i - b' i)
    have n2 := sobNorm_nonneg r (D0 i V')
    have n3 := sobNorm_nonneg (r + 1) (b i - b' i)
    have n4 := sobNorm_nonneg (r + 1) V'
    have hDb0 : 0 ≤ Db := n3.trans (hDb i)
    have m1 : algConst r * sobNorm r (b i - b' i) * sobNorm r (D0 i V') ≤ algConst r * Db * MV := by
      gcongr
    have m2 : algConst (r + 1) * sobNorm (r + 1) (b i - b' i) * sobNorm (r + 1) V' ≤
        algConst (r + 1) * Db * MV := by
      gcongr; exact hDb i
    have m3 : (algConst r + 1) * sobNorm r (D0 i V - D0 i V') ≤ (algConst r + 1) * DV := by gcongr
    have m4 : (algConst (r + 1) + 1) * sobNorm (r + 1) (V - V') ≤ (algConst (r + 1) + 1) * DV := by
      gcongr
    nlinarith
  rw [← Finset.sum_sub_distrib]
  refine (sobNorm_sum_le _ _ _).trans ?_
  calc _ ≤ ∑ _i : Fin 3, ((algConst r + 1 + (algConst (r + 1) + 1)) * DV +
        (algConst r + algConst (r + 1)) * Db * MV) := sum_le_sum fun i _ => hi i
    _ = _ := by simp; ring

/-- Seven-term triangle inequality. -/
theorem lawJet_sobNorm_seven_le (r : ℕ) (d1 d2 d3 d4 d5 d6 d7 : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.sobNorm r (d1 + d2 - (d3 + d4) + d5 - d6 - d7) ≤
      PeriodicGridSobolev.sobNorm r d1 + PeriodicGridSobolev.sobNorm r d2 +
        PeriodicGridSobolev.sobNorm r d3 + PeriodicGridSobolev.sobNorm r d4 +
        PeriodicGridSobolev.sobNorm r d5 + PeriodicGridSobolev.sobNorm r d6 +
        PeriodicGridSobolev.sobNorm r d7 := by
  open PeriodicGridSobolev.Moser in
  have h1 := sobNorm_sub_le r (d1 + d2 - (d3 + d4) + d5 - d6) d7
  have h2 := sobNorm_sub_le r (d1 + d2 - (d3 + d4) + d5) d6
  have h3 := sobNorm_add_le r (d1 + d2 - (d3 + d4)) d5
  have h4 := sobNorm_sub_le r (d1 + d2) (d3 + d4)
  have h5 := sobNorm_add_le r d1 d2
  have h6 := sobNorm_add_le r d3 d4
  linarith

/-- The bracket of the once-differentiated mass row, `jetDeriv = a⁻¹ · jetRow`. -/
def jetRow (B : Upper → Upper → ℝ) (q v W : Grid N → MetricRec) (μ ν : Fin 4) : Grid N → ℝ :=
  divArr (cdot q v) (comp q μ ν) + divArr (cArr q) (comp v μ ν) -
    (skewArr (bdot q v) (comp v μ ν) + skewArr (bArr q) (comp W μ ν)) +
    (fun x => fderiv ℝ (fun u : JetSpace => compensatorMap u μ ν) (jetArr q v x) (jetArr v W x)) -
    comp (bTerm B v) μ ν - fun x => adot q v x * comp (lawAccel B q v) μ ν x

theorem jetDeriv_eq_jetRow (B : Upper → Upper → ℝ) (q v W : Grid N → MetricRec) (x : Grid N)
    (μ ν : Fin 4) : jetDeriv B q v W x μ ν = (aArr q x)⁻¹ * jetRow B q v W μ ν x := by
  simp only [jetDeriv, jetRow, comp, Pi.add_apply, Pi.sub_apply]

theorem bTerm_zero_mark (u : Grid N → MetricRec) : bTerm (fun _ _ => 0) u = 0 := by
  funext x μ ν; simp [bTerm]

theorem comp_symRec_sub (u u' : Grid N → MetricRec) (κ : Upper) :
    comp (symRec u - symRec u') κ.1.1 κ.1.2 = comp (u - u') κ.1.1 κ.1.2 := by
  funext x; simp [comp, symRec_upper]

set_option maxHeartbeats 8000000 in
/-- **The Lipschitz version of `jetDeriv_bound`** one order lower (`s ≥ 6`): there are `δ > 0`,
`K ≥ 0`, independent of the mesh and of the mark, such that for symmetric records `(q, v)`,
`(p, w)` in the top chart `‖·‖_{X^s_h} ≤ δ`, the third time derivatives of the mass row
(`jetDeriv` with the zero mark, the first one evaluated at an arbitrary mark acceleration
`W = V_{B,h}(q, v)`) satisfy, componentwise,
`‖q_ttt - p_ttt‖_{s-4,h} ≤ K (‖(q - p, v - w)‖_{X^{s-2}_h} + ‖V_{B,h}(q,v) - V_{0,h}(p,w)‖_{s-3,h})`. -/
theorem jetDeriv_lipschitz (s : ℕ) (hs : 6 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ) (q v p w : Grid N → MetricRec),
      IsMark (1 / 48) B → IsSymRec q → IsSymRec v → IsSymRec p → IsSymRec w →
      Xnorm s q v ≤ δ → Xnorm s p w ≤ δ → ∀ κ : Upper,
      PeriodicGridSobolev.sobNorm (s - 4)
        (cx (fun x => jetDeriv (fun _ _ => 0) q v (symRec (lawAccel B q v)) x κ.1.1 κ.1.2) -
          cx (fun x => jetDeriv (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) x
            κ.1.1 κ.1.2)) ≤
        K * (Xnorm (s - 2) (q - p) (v - w) +
          Fnorm (s - 3) (lawAccel B q v - lawAccel (fun _ _ => 0) p w)) := by
  open PeriodicGridSobolev PeriodicGridSobolev.Moser PeriodicGridSobolev.CommutedRow in
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 4 := ⟨s - 4, by omega⟩
  have hr : 2 ≤ r := by omega
  simp only [show r + 4 - 4 = r by omega, show r + 4 - 3 = r + 1 by omega,
    show r + 4 - 2 = r + 2 by omega]
  obtain ⟨δL, hδL, KL, hKL, hLa⟩ := lawAccel_bound (r + 4) (by omega)
  obtain ⟨δJ, hδJ, KJ, hKJ, hJ⟩ := jetDeriv_bound (r + 4) (by omega)
  obtain ⟨δK, hδK, KK, hKK, hK⟩ := dAcc_bound (r + 4) (r + 2) (by omega) (by omega)
  obtain ⟨δR1, hδR1, CR1, hCR1, hR1⟩ := lawJet_moser_lipschitz_rates (r + 1) (by omega)
  obtain ⟨δR0, hδR0, CR0, hCR0, hR0⟩ := lawJet_moser_lipschitz_rates r hr
  obtain ⟨δr1, hδr1, Cr1, hCr1, hmr1⟩ := moser_rate_coefficients (r + 1) (by omega)
  obtain ⟨δr0, hδr0, Cr0, hCr0, hmr0⟩ := moser_rate_coefficients r hr
  obtain ⟨δ0, hδ0, C0, hC0, hm0⟩ := moser_coefficients r hr
  obtain ⟨δ1, hδ1, C1, hC1, hm1⟩ := moser_coefficients (r + 1) (by omega)
  obtain ⟨δl0, hδl0, Cl0, hCl0, hml0⟩ := moser_lipschitz_coefficients r hr
  obtain ⟨δl1, hδl1, Cl1, hCl1, hml1⟩ := moser_lipschitz_coefficients (r + 1) (by omega)
  obtain ⟨δG, hδG, CG, hCG, hG⟩ := lawJet_moser_lipschitz_compensator_rate r hr
  obtain ⟨r₀, hr₀, hchart⟩ := exists_det_chart
  have hS := supConst_nonneg
  set A0 := algConst r
  set A1 := algConst (r + 1)
  have hA0 := algConst_pos r
  have hA1 := algConst_pos (r + 1)
  set Dj : ℝ := 80 + 1280 * (1 + KL)
  obtain ⟨K1, hK1def⟩ : ∃ K1 : ℝ, K1 = 9 * ((A1 + 1) + A1 * (CR1 * 32)) +
      9 * ((A1 + 1) + A1 * (Cl1 * 16)) +
      3 * ((A0 + 1 + (A1 + 1)) + (A0 + A1) * (CR1 * 32)) + 3 * ((A0 + A1) * (Cl1 * 16) * KL) +
      CG * (80 + 80 * 16) + A0 * (CR0 * 32 * KL + Cr0 * 32 * KK) := ⟨_, rfl⟩
  obtain ⟨K2, hK2def⟩ : ∃ K2 : ℝ, K2 = 3 * (A0 + 1 + (A1 + 1)) + CG * (80 * 16) := ⟨_, rfl⟩
  obtain ⟨K3, hK3def⟩ : ∃ K3 : ℝ, K3 = A0 * (Cl0 * 16) * KJ := ⟨_, rfl⟩
  have hK1 : 0 ≤ K1 := by rw [hK1def]; positivity
  have hK2 : 0 ≤ K2 := by rw [hK2def]; positivity
  have hK3 : 0 ≤ K3 := by rw [hK3def]; positivity
  refine ⟨min (min (min δL δJ) (min δK (δR1 / 32))) (min (min (δR0 / 32) (δr1 / 32))
      (min (δr0 / 32) (δ0 / 16))) ⊓ (min (min (δ1 / 16) (δl0 / 16)) (min (δl1 / 16) (δG / Dj)) ⊓
      (min (min 1 (r₀ / (2 * (supConst + 1)))) (min (1 / (32 * Cr1 + 1))
        (min (1 / (16 * C0 + 1)) (1 / (16 * C1 + 1)))))),
    by positivity, (A0 + 1) * (K1 + K2 + K3), mul_nonneg (by positivity) (by linarith),
    fun N _ B q v p w hB hq hv hp hw hX hY κ => ?_⟩
  set X := Xnorm (r + 4) q v
  set Y := Xnorm (r + 4) p w
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  have hY0 : 0 ≤ Y := Xnorm_nonneg _ _ _
  have m : ∀ a, (min (min (min δL δJ) (min δK (δR1 / 32))) (min (min (δR0 / 32) (δr1 / 32))
      (min (δr0 / 32) (δ0 / 16))) ⊓ (min (min (δ1 / 16) (δl0 / 16)) (min (δl1 / 16) (δG / Dj)) ⊓
      (min (min 1 (r₀ / (2 * (supConst + 1)))) (min (1 / (32 * Cr1 + 1))
        (min (1 / (16 * C0 + 1)) (1 / (16 * C1 + 1))))))) ≤ a → X ≤ a ∧ Y ≤ a :=
    fun a ha => ⟨hX.trans ha, hY.trans ha⟩
  obtain ⟨hXL, hYL⟩ := m δL (by simp)
  obtain ⟨hXJ, hYJ⟩ := m δJ (by simp)
  obtain ⟨hXK, hYK⟩ := m δK (by simp)
  obtain ⟨hXR1, hYR1⟩ := m (δR1 / 32) (by simp)
  obtain ⟨hXR0, hYR0⟩ := m (δR0 / 32) (by simp)
  obtain ⟨hXr1, hYr1⟩ := m (δr1 / 32) (by simp)
  obtain ⟨hXr0, hYr0⟩ := m (δr0 / 32) (by simp)
  obtain ⟨hX0', hY0'⟩ := m (δ0 / 16) (by simp)
  obtain ⟨hX1', hY1'⟩ := m (δ1 / 16) (by simp)
  obtain ⟨hXl0, hYl0⟩ := m (δl0 / 16) (by simp)
  obtain ⟨hXl1, hYl1⟩ := m (δl1 / 16) (by simp)
  obtain ⟨hXG, hYG⟩ := m (δG / Dj) (by simp)
  obtain ⟨hX1, hY1⟩ := m 1 (by simp)
  obtain ⟨hXc, hYc⟩ := m (r₀ / (2 * (supConst + 1))) (by simp)
  obtain ⟨hXr1s, -⟩ := m (1 / (32 * Cr1 + 1)) (by simp)
  obtain ⟨hXC0, -⟩ := m (1 / (16 * C0 + 1)) (by simp)
  obtain ⟨hXC1, -⟩ := m (1 / (16 * C1 + 1)) (by simp)
  clear m
  -- the differences
  have hqp := isSymRec_sub hq hp
  have hvw := isSymRec_sub hv hw
  set Xd := Xnorm (r + 2) (q - p) (v - w)
  set Fd := Fnorm (r + 1) (lawAccel B q v - lawAccel (fun _ _ => 0) p w)
  have hXd0 : 0 ≤ Xd := Xnorm_nonneg _ _ _
  have hFd0 : 0 ≤ Fd := Fnorm_nonneg _ _
  have hZ : IsMark (1 / 48) (fun _ _ : Upper => (0 : ℝ)) := isMark_zero
  -- coordinate sizes
  have cq : ∀ k, k ≤ r + 5 → coordSum k bM q ≤ 16 * X := fun k hk => coordSum_bM_q_le _ hq v hk
  have cv : ∀ k, k ≤ r + 4 → coordSum k bM v ≤ 16 * X := fun k hk => coordSum_bM_v_le _ q hv hk
  have cp : ∀ k, k ≤ r + 5 → coordSum k bM p ≤ 16 * Y := fun k hk => coordSum_bM_q_le _ hp w hk
  have cw : ∀ k, k ≤ r + 4 → coordSum k bM w ≤ 16 * Y := fun k hk => coordSum_bM_v_le _ p hw hk
  have cqp : ∀ k, k ≤ r + 3 → coordSum k bM (q - p) ≤ 16 * Xd :=
    fun k hk => coordSum_bM_q_le _ hqp (v - w) hk
  have cvw : ∀ k, k ≤ r + 2 → coordSum k bM (v - w) ≤ 16 * Xd :=
    fun k hk => coordSum_bM_v_le _ (q - p) hvw hk
  have cpq : coordSum r bM (p - q) ≤ 16 * Xd := by
    have := coordSum_bM_q_le (r + 2) (isSymRec_sub hp hq) (w - v) (r := r) (by omega)
    rwa [lawDiff_Xnorm_sub_comm] at this
  -- the chart at `p` and `q`
  have hchartq : ∀ y, harmA (minkowski + q y) ≠ 0 := by
    intro y
    refine (hchart _ ?_).2
    rw [add_sub_cancel_left]
    have h1 := norm_q_le (r + 4) (by omega) hq v y
    have h2 : supConst * X ≤ supConst * (r₀ / (2 * (supConst + 1))) :=
      mul_le_mul_of_nonneg_left hXc hS
    have h3 : supConst * (r₀ / (2 * (supConst + 1))) < r₀ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hchartp : ∀ y, harmA (minkowski + p y) ≠ 0 := by
    intro y
    refine (hchart _ ?_).2
    rw [add_sub_cancel_left]
    have h1 := norm_q_le (r + 4) (by omega) hp w y
    have h2 : supConst * Y ≤ supConst * (r₀ / (2 * (supConst + 1))) :=
      mul_le_mul_of_nonneg_left hYc hS
    have h3 : supConst * (r₀ / (2 * (supConst + 1))) < r₀ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have sum16 : ∀ (f : Upper → ℝ) (c : ℝ), (∀ κ', f κ' ≤ c) → 0 ≤ c → ∑ κ', f κ' ≤ 16 * c := by
    intro f c hf hc
    calc ∑ κ', f κ' ≤ ∑ _κ' : Upper, c := sum_le_sum fun κ' _ => hf κ'
      _ = (Fintype.card Upper : ℝ) * c := by rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ 16 * c := by
          have hc' : (Fintype.card Upper : ℝ) ≤ 16 := by
            have h1 : Fintype.card Upper ≤ Fintype.card (Fin 4 × Fin 4) := Fintype.card_subtype_le _
            have h2 : Fintype.card (Fin 4 × Fin 4) = 16 := by simp
            exact_mod_cast h1.trans h2.le
          exact mul_le_mul_of_nonneg_right hc' hc
  -- static bounds
  have hWq : ∀ κ' : Upper, sobNorm (r + 3) (cx (comp (lawAccel B q v) κ'.1.1 κ'.1.2)) ≤ KL * X :=
    fun κ' => by
      have := hLa N B q v hB hq hv hXL κ'
      rwa [show r + 4 - 1 = r + 3 by omega] at this
  have hWq0 : ∀ κ' : Upper,
      sobNorm (r + 3) (cx (comp (lawAccel (fun _ _ => 0) q v) κ'.1.1 κ'.1.2)) ≤ KL * X :=
    fun κ' => by
      have := hLa N _ q v hZ hq hv hXL κ'
      rwa [show r + 4 - 1 = r + 3 by omega] at this
  have hWp : ∀ κ' : Upper,
      sobNorm (r + 3) (cx (comp (lawAccel (fun _ _ => 0) p w) κ'.1.1 κ'.1.2)) ≤ KL * Y :=
    fun κ' => by
      have := hLa N _ p w hZ hp hw hYL κ'
      rwa [show r + 4 - 1 = r + 3 by omega] at this
  have hJp : sobNorm r (cx (fun x => jetDeriv (fun _ _ => 0) p w
      (symRec (lawAccel (fun _ _ => 0) p w)) x κ.1.1 κ.1.2)) ≤ KJ := by
    have := hJ N _ p w hZ hp hw hYJ κ
    rw [show r + 4 - 2 = r + 2 by omega] at this
    exact (sobNorm_mono (by omega) _).trans (this.trans (by nlinarith))
  -- coefficients of `q` near constants
  have hM0 := hm0 N q ((cq r (by omega)).trans (by linarith))
  have hC0X : C0 * (16 * X) ≤ 1 := by
    have h := hXC0; rw [le_div_iff₀ (by positivity)] at h; nlinarith
  have hainv : sobNorm r (cx (fun x => (aArr q x)⁻¹) - fun _ => (1 : ℂ)) ≤ 1 :=
    hM0.2.1.trans ((mul_le_mul_of_nonneg_left (cq r (by omega)) hC0).trans hC0X)
  have hM1 := hm1 N q ((cq (r + 1) (by omega)).trans (by linarith))
  have hC1X : C1 * (16 * X) ≤ 1 := by
    have h := hXC1; rw [le_div_iff₀ (by positivity)] at h; nlinarith
  have hc1 : ∀ i j, sobNorm (r + 1) (cx (cArr q i j) -
      fun _ => ((if i = j then 1 else 0 : ℝ) : ℂ)) ≤ 1 := fun i j =>
    (hM1.2.2.1 i j).trans ((mul_le_mul_of_nonneg_left (cq (r + 1) (by omega)) hC1).trans hC1X)
  have hb1 : ∀ i, sobNorm (r + 1) (cx (bArr q i) - fun _ => (0 : ℂ)) ≤ 1 := fun i =>
    (hM1.2.2.2 i).trans ((mul_le_mul_of_nonneg_left (cq (r + 1) (by omega)) hC1).trans hC1X)
  -- rates
  have hRq := hmr1 N q v (by linarith [cq (r + 1) (by omega), cv (r + 1) (by omega)])
  have hR0p := hmr0 N p w (by linarith [cp r (by omega), cw r (by omega)])
  have hCr1X : Cr1 * (32 * X) ≤ 1 := by
    have h := hXr1s; rw [le_div_iff₀ (by positivity)] at h; nlinarith
  have hqv32 : coordSum (r + 1) bM q + coordSum (r + 1) bM v ≤ 32 * X := by
    linarith [cq (r + 1) (by omega), cv (r + 1) (by omega)]
  have hcdot : ∀ i j, sobNorm (r + 1) (cx (cdot q v i j) - fun _ => (0 : ℂ)) ≤ 1 := fun i j => by
    rw [show (cx (cdot q v i j) - fun _ => (0 : ℂ)) = cx (cdot q v i j) by funext x; simp]
    exact (hRq.2.1 i j).trans ((mul_le_mul_of_nonneg_left hqv32 hCr1).trans hCr1X)
  have hbdot : ∀ i, sobNorm (r + 1) (cx (bdot q v i) - fun _ => (0 : ℂ)) ≤ 1 := fun i => by
    rw [show (cx (bdot q v i) - fun _ => (0 : ℂ)) = cx (bdot q v i) by funext x; simp]
    exact (hRq.2.2 i).trans ((mul_le_mul_of_nonneg_left hqv32 hCr1).trans hCr1X)
  -- Lipschitz bounds
  have hsum1 : coordSum (r + 1) bM (q - p) + coordSum (r + 1) bM (v - w) ≤ 32 * Xd := by
    linarith [cqp (r + 1) (by omega), cvw (r + 1) (by omega)]
  have hsum0 : coordSum r bM (q - p) + coordSum r bM (v - w) ≤ 32 * Xd := by
    linarith [cqp r (by omega), cvw r (by omega)]
  have hLq := hR1 N q v p w (by linarith [cq (r + 1) (by omega), cv (r + 1) (by omega)])
    (by linarith [cp (r + 1) (by omega), cw (r + 1) (by omega)])
  have hLq0 := hR0 N q v p w (by linarith [cq r (by omega), cv r (by omega)])
    (by linarith [cp r (by omega), cw r (by omega)])
  have hLc := hml1 N q p (by linarith [cq (r + 1) (by omega)]) (by linarith [cp (r + 1) (by omega)])
  have hLa0 := hml0 N p q (by linarith [cp r (by omega)]) (by linarith [cq r (by omega)])
  -- the seven pieces
  have T1 : sobNorm r ((∑ i, ∑ j, Dm i (cx (cdot q v i j) * Dp j (cx (comp q κ.1.1 κ.1.2)))) -
      ∑ i, ∑ j, Dm i (cx (cdot p w i j) * Dp j (cx (comp p κ.1.1 κ.1.2)))) ≤
      9 * ((A1 + 1) * Xd + A1 * (CR1 * (32 * Xd)) * 1) := by
    refine lawJet_divArr_sub_le r hr (fun i j => cx (cdot q v i j)) (fun i j => cx (cdot p w i j))
      _ _ (fun _ _ => 0) (fun _ _ => by simp) hcdot (fun i j => (hLq.2.1 i j).trans ?_) ?_ ?_
    · exact mul_le_mul_of_nonneg_left hsum1 hCR1
    · exact (sobNorm_q_le (r + 4) hp w _ _ (by omega)).trans hY1
    · rw [← cx_comp_sub]; exact sobNorm_q_le (r + 2) hqp (v - w) _ _ (by omega)
  have T2 : sobNorm r ((∑ i, ∑ j, Dm i (cx (cArr q i j) * Dp j (cx (comp v κ.1.1 κ.1.2)))) -
      ∑ i, ∑ j, Dm i (cx (cArr p i j) * Dp j (cx (comp w κ.1.1 κ.1.2)))) ≤
      9 * ((A1 + 1) * Xd + A1 * (Cl1 * (16 * Xd)) * 1) := by
    refine lawJet_divArr_sub_le r hr (fun i j => cx (cArr q i j)) (fun i j => cx (cArr p i j))
      _ _ (fun i j => ((if i = j then 1 else 0 : ℝ) : ℂ)) (fun i j => by split_ifs <;> simp) hc1
      (fun i j => (hLc.2.1 i j).trans ?_) ?_ ?_
    · exact mul_le_mul_of_nonneg_left (cqp (r + 1) (by omega)) hCl1
    · exact (sobNorm_v_le (r + 4) p hw _ _ (by omega)).trans hY1
    · rw [← cx_comp_sub]; exact sobNorm_v_le (r + 2) (q - p) hvw _ _ (by omega)
  have T3 : sobNorm r ((∑ i, (cx (bdot q v i) * D0 i (cx (comp v κ.1.1 κ.1.2)) +
        D0 i (cx (bdot q v i) * cx (comp v κ.1.1 κ.1.2)))) -
      ∑ i, (cx (bdot p w i) * D0 i (cx (comp w κ.1.1 κ.1.2)) +
        D0 i (cx (bdot p w i) * cx (comp w κ.1.1 κ.1.2)))) ≤
      3 * ((A0 + 1 + (A1 + 1)) * Xd + (A0 + A1) * (CR1 * (32 * Xd)) * 1) := by
    refine lawJet_skew_sub_le r hr (fun i => cx (bdot q v i)) (fun i => cx (bdot p w i)) _ _
      (fun _ => 0) (fun _ => by simp) hbdot (fun i => (hLq.2.2 i).trans ?_) ?_ ?_
    · exact mul_le_mul_of_nonneg_left hsum1 hCR1
    · exact (sobNorm_v_le (r + 4) p hw _ _ (by omega)).trans hY1
    · rw [← cx_comp_sub]; exact sobNorm_v_le (r + 2) (q - p) hvw _ _ (by omega)
  have T4 : sobNorm r ((∑ i, (cx (bArr q i) * D0 i (cx (comp (symRec (lawAccel B q v)) κ.1.1 κ.1.2)) +
        D0 i (cx (bArr q i) * cx (comp (symRec (lawAccel B q v)) κ.1.1 κ.1.2)))) -
      ∑ i, (cx (bArr p i) * D0 i (cx (comp (symRec (lawAccel (fun _ _ => 0) p w)) κ.1.1 κ.1.2)) +
        D0 i (cx (bArr p i) * cx (comp (symRec (lawAccel (fun _ _ => 0) p w)) κ.1.1 κ.1.2)))) ≤
      3 * ((A0 + 1 + (A1 + 1)) * Fd + (A0 + A1) * (Cl1 * (16 * Xd)) * KL) := by
    rw [comp_symRec, comp_symRec]
    refine lawJet_skew_sub_le r hr (fun i => cx (bArr q i)) (fun i => cx (bArr p i)) _ _
      (fun _ => 0) (fun _ => by simp) hb1 (fun i => (hLc.2.2 i).trans ?_) ?_ ?_
    · exact mul_le_mul_of_nonneg_left (cqp (r + 1) (by omega)) hCl1
    · exact (sobNorm_mono (by omega) _).trans ((hWp κ).trans (by nlinarith))
    · rw [← cx_comp_sub]; exact sobNorm_le_Fnorm (r + 1) _ κ
  have T5 : sobNorm r (cx (fun x => fderiv ℝ (fun u : JetSpace => compensatorMap u κ.1.1 κ.1.2)
        (jetArr q v x) (jetArr v (symRec (lawAccel B q v)) x)) -
      cx (fun x => fderiv ℝ (fun u : JetSpace => compensatorMap u κ.1.1 κ.1.2)
        (jetArr p w x) (jetArr w (symRec (lawAccel (fun _ _ => 0) p w)) x))) ≤
      CG * (80 * Xd + 80 * (16 * (Xd + Fd))) := by
    have hjv : ∀ (a b : RootParityConnector.Grid N → MetricRec) (B' : Upper → Upper → ℝ) (Z : ℝ), IsSymRec a →
        IsSymRec b → Xnorm (r + 4) a b ≤ Z → (∀ κ' : Upper,
          sobNorm (r + 3) (cx (comp (lawAccel B' a b) κ'.1.1 κ'.1.2)) ≤ KL * Z) →
        coordSum r bJ (jetArr a b) + coordSum r bJ (jetArr b (symRec (lawAccel B' a b))) ≤
          Dj * Z := by
      intro a b B' Z ha hb hab hacc
      have hZ0 : 0 ≤ Z := (Xnorm_nonneg _ _ _).trans hab
      have j1 : coordSum r bJ (jetArr a b) ≤ 80 * Z :=
        (coordSum_mono (by omega) bJ _).trans ((coordSum_bJ_le (r + 4) ha hb).trans (by linarith))
      have j2 : coordSum r bJ (jetArr b (symRec (lawAccel B' a b))) ≤ 80 * (16 * (Z + KL * Z)) := by
        refine (coordSum_bJ_le r hb (isSymRec_symRec _)).trans
          (mul_le_mul_of_nonneg_left ((Xnorm_le_sum r _ _).trans ?_) (by norm_num))
        refine sum16 _ _ (fun κ' => add_le_add ?_ ?_) (by positivity)
        · exact sobNorm_v_le (r + 4) a hb _ _ (by omega) |>.trans hab
        · rw [comp_symRec]; exact (sobNorm_mono (by omega) _).trans (hacc κ')
      simp only [Dj]; nlinarith
    have hjq := hjv q v B X hq hv le_rfl hWq
    have hjp := hjv p w _ Y hp hw le_rfl hWp
    have hDjX : Dj * X ≤ δG := by
      have h := hXG; rw [le_div_iff₀ (by positivity)] at h; linarith
    have hDjY : Dj * Y ≤ δG := by
      have h := hYG; rw [le_div_iff₀ (by positivity)] at h; linarith
    have h := hG N (jetArr q v) (jetArr v (symRec (lawAccel B q v))) (jetArr p w)
      (jetArr w (symRec (lawAccel (fun _ _ => 0) p w))) (hjq.trans hDjX) (hjp.trans hDjY)
      κ.1.1 κ.1.2
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCG)
    rw [jetArr_sub, jetArr_sub]
    have e1 : coordSum r bJ (jetArr (q - p) (v - w)) ≤ 80 * Xd :=
      (coordSum_mono (by omega) bJ _).trans (coordSum_bJ_le (r + 2) hqp hvw)
    have e2 : coordSum r bJ (jetArr (v - w) (symRec (lawAccel B q v) -
        symRec (lawAccel (fun _ _ => 0) p w))) ≤ 80 * (16 * (Xd + Fd)) := by
      refine (coordSum_bJ_le r hvw (isSymRec_sub (isSymRec_symRec _) (isSymRec_symRec _))).trans
        (mul_le_mul_of_nonneg_left ((Xnorm_le_sum r _ _).trans ?_) (by norm_num))
      refine sum16 _ _ (fun κ' => add_le_add ?_ ?_) (by positivity)
      · exact sobNorm_v_le (r + 2) (q - p) hvw _ _ (by omega)
      · rw [comp_symRec_sub]
        exact (sobNorm_mono (by omega) _).trans (sobNorm_le_Fnorm (r + 1) _ κ')
    linarith
  have T6 : sobNorm r (cx (comp (bTerm (fun _ _ => 0) v) κ.1.1 κ.1.2) -
      cx (comp (bTerm (fun _ _ => 0) w) κ.1.1 κ.1.2)) ≤ 0 := by
    rw [bTerm_zero_mark, bTerm_zero_mark, sub_self]
    have e : (0 : PeriodicGridSobolev.Grid N → ℂ) = (0 : ℂ) • (0 : PeriodicGridSobolev.Grid N → ℂ) := by
      simp
    rw [e, sobNorm_smul]; simp
  have T7 : sobNorm r (cx (adot q v) * cx (comp (lawAccel (fun _ _ => 0) q v) κ.1.1 κ.1.2) -
      cx (adot p w) * cx (comp (lawAccel (fun _ _ => 0) p w) κ.1.1 κ.1.2)) ≤
      A0 * ((CR0 * (32 * Xd)) * KL + (Cr0 * 32) * (KK * Xd)) := by
    refine (lawJet_sobNorm_mul_sub_le r hr _ _ _ _).trans ?_
    have a1 : sobNorm r (cx (adot q v) - cx (adot p w)) ≤ CR0 * (32 * Xd) :=
      hLq0.1.trans (mul_le_mul_of_nonneg_left hsum0 hCR0)
    have a2 : sobNorm r (cx (comp (lawAccel (fun _ _ => 0) q v) κ.1.1 κ.1.2)) ≤ KL :=
      (sobNorm_mono (by omega) _).trans ((hWq0 κ).trans (by nlinarith))
    have a3 : sobNorm r (cx (adot p w)) ≤ Cr0 * 32 :=
      hR0p.1.trans (by nlinarith [cp r (by omega), cw r (by omega)])
    have a4 : sobNorm r (cx (comp (lawAccel (fun _ _ => 0) q v) κ.1.1 κ.1.2) -
        cx (comp (lawAccel (fun _ _ => 0) p w) κ.1.1 κ.1.2)) ≤ KK * Xd := by
      have h := hK N q p v w 0 0 hq hp hv hw hXK hYK κ
      rw [show r + 2 - 1 = r + 1 by omega, sub_self, lawDiff_Fnorm_zero, add_zero] at h
      rw [← cx_comp_sub, lawAccel_zero, lawAccel_zero]
      have e : harmonicWriterAcceleration q v - harmonicWriterAcceleration p w =
          dAcc q p v w 0 0 := by
        simp [dAcc]
      rw [e]; exact (sobNorm_mono (by omega) _).trans h
    have := add_le_add (mul_le_mul a1 a2 (sobNorm_nonneg _ _) (by positivity))
      (mul_le_mul a3 a4 (sobNorm_nonneg _ _) (by positivity))
    exact mul_le_mul_of_nonneg_left this hA0.le
  -- the bracket difference
  have hEd : sobNorm r (cx (jetRow (fun _ _ => 0) q v (symRec (lawAccel B q v)) κ.1.1 κ.1.2) -
      cx (jetRow (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) κ.1.1 κ.1.2)) ≤
      K1 * Xd + K2 * Fd := by
    have e : cx (jetRow (fun _ _ => 0) q v (symRec (lawAccel B q v)) κ.1.1 κ.1.2) -
        cx (jetRow (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) κ.1.1 κ.1.2) =
        (((∑ i, ∑ j, Dm i (cx (cdot q v i j) * Dp j (cx (comp q κ.1.1 κ.1.2)))) -
          ∑ i, ∑ j, Dm i (cx (cdot p w i j) * Dp j (cx (comp p κ.1.1 κ.1.2)))) +
        ((∑ i, ∑ j, Dm i (cx (cArr q i j) * Dp j (cx (comp v κ.1.1 κ.1.2)))) -
          ∑ i, ∑ j, Dm i (cx (cArr p i j) * Dp j (cx (comp w κ.1.1 κ.1.2)))) -
        (((∑ i, (cx (bdot q v i) * D0 i (cx (comp v κ.1.1 κ.1.2)) +
            D0 i (cx (bdot q v i) * cx (comp v κ.1.1 κ.1.2)))) -
          ∑ i, (cx (bdot p w i) * D0 i (cx (comp w κ.1.1 κ.1.2)) +
            D0 i (cx (bdot p w i) * cx (comp w κ.1.1 κ.1.2)))) +
         ((∑ i, (cx (bArr q i) * D0 i (cx (comp (symRec (lawAccel B q v)) κ.1.1 κ.1.2)) +
            D0 i (cx (bArr q i) * cx (comp (symRec (lawAccel B q v)) κ.1.1 κ.1.2)))) -
          ∑ i, (cx (bArr p i) * D0 i (cx (comp (symRec (lawAccel (fun _ _ => 0) p w)) κ.1.1 κ.1.2)) +
            D0 i (cx (bArr p i) * cx (comp (symRec (lawAccel (fun _ _ => 0) p w)) κ.1.1 κ.1.2))))) +
        (cx (fun x => fderiv ℝ (fun u : JetSpace => compensatorMap u κ.1.1 κ.1.2)
            (jetArr q v x) (jetArr v (symRec (lawAccel B q v)) x)) -
          cx (fun x => fderiv ℝ (fun u : JetSpace => compensatorMap u κ.1.1 κ.1.2)
            (jetArr p w x) (jetArr w (symRec (lawAccel (fun _ _ => 0) p w)) x))) -
        (cx (comp (bTerm (fun _ _ => 0) v) κ.1.1 κ.1.2) -
          cx (comp (bTerm (fun _ _ => 0) w) κ.1.1 κ.1.2)) -
        (cx (adot q v) * cx (comp (lawAccel (fun _ _ => 0) q v) κ.1.1 κ.1.2) -
          cx (adot p w) * cx (comp (lawAccel (fun _ _ => 0) p w) κ.1.1 κ.1.2))) := by
      simp only [jetRow, cx_add, cx_sub, cx_divArr, cx_skewArr, cx_fun_mul]
      abel
    rw [e]
    refine (lawJet_sobNorm_seven_le r _ _ _ _ _ _ _).trans ?_
    have hT : 9 * ((A1 + 1) * Xd + A1 * (CR1 * (32 * Xd)) * 1) +
        9 * ((A1 + 1) * Xd + A1 * (Cl1 * (16 * Xd)) * 1) +
        3 * ((A0 + 1 + (A1 + 1)) * Xd + (A0 + A1) * (CR1 * (32 * Xd)) * 1) +
        3 * ((A0 + 1 + (A1 + 1)) * Fd + (A0 + A1) * (Cl1 * (16 * Xd)) * KL) +
        CG * (80 * Xd + 80 * (16 * (Xd + Fd))) + 0 +
        A0 * ((CR0 * (32 * Xd)) * KL + (Cr0 * 32) * (KK * Xd)) = K1 * Xd + K2 * Fd := by
      rw [hK1def, hK2def]; ring
    linarith [T1, T2, T3, T4, T5, T6, T7]
  -- the inverse mass factor
  have hsplit : cx (fun x => jetDeriv (fun _ _ => 0) q v (symRec (lawAccel B q v)) x κ.1.1 κ.1.2) -
      cx (fun x => jetDeriv (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) x
        κ.1.1 κ.1.2) =
      cx (fun x => (aArr q x)⁻¹) *
        (cx (jetRow (fun _ _ => 0) q v (symRec (lawAccel B q v)) κ.1.1 κ.1.2) -
          cx (jetRow (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) κ.1.1 κ.1.2)) +
      cx (fun x => (aArr q x)⁻¹) * ((cx (aArr p) - cx (aArr q)) *
        cx (fun x => jetDeriv (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) x
          κ.1.1 κ.1.2)) := by
    funext x
    have hqx : ((aArr q x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hchartq x
    have hpx : ((aArr p x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hchartp x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, cx_apply, jetDeriv_eq_jetRow]
    push_cast
    field_simp
    ring
  rw [hsplit]
  refine (sobNorm_add_le _ _ _).trans ?_
  have f1 : sobNorm r (cx (fun x => (aArr q x)⁻¹) *
      (cx (jetRow (fun _ _ => 0) q v (symRec (lawAccel B q v)) κ.1.1 κ.1.2) -
        cx (jetRow (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) κ.1.1 κ.1.2))) ≤
      (A0 + 1) * sobNorm r
      (cx (jetRow (fun _ _ => 0) q v (symRec (lawAccel B q v)) κ.1.1 κ.1.2) -
        cx (jetRow (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) κ.1.1 κ.1.2)) :=
    sobNorm_coef_mul_le r hr (cx (fun x => (aArr q x)⁻¹))
    (cx (jetRow (fun _ _ => 0) q v (symRec (lawAccel B q v)) κ.1.1 κ.1.2) -
      cx (jetRow (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) κ.1.1 κ.1.2)) 1
    (by simp) hainv
  have f2 : sobNorm r (cx (fun x => (aArr q x)⁻¹) * ((cx (aArr p) - cx (aArr q)) *
      cx (fun x => jetDeriv (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) x
        κ.1.1 κ.1.2))) ≤ (A0 + 1) * sobNorm r ((cx (aArr p) - cx (aArr q)) *
      cx (fun x => jetDeriv (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) x
        κ.1.1 κ.1.2)) :=
    sobNorm_coef_mul_le r hr (cx (fun x => (aArr q x)⁻¹)) ((cx (aArr p) - cx (aArr q)) *
    cx (fun x => jetDeriv (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) x
      κ.1.1 κ.1.2)) 1 (by simp) hainv
  have f3 : sobNorm r ((cx (aArr p) - cx (aArr q)) *
      cx (fun x => jetDeriv (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) x
        κ.1.1 κ.1.2)) ≤ A0 * sobNorm r (cx (aArr p) - cx (aArr q)) *
      sobNorm r (cx (fun x => jetDeriv (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) x
        κ.1.1 κ.1.2)) := sobNorm_mul_le r hr _ _
  have f4 : sobNorm r (cx (aArr p) - cx (aArr q)) ≤ Cl0 * (16 * Xd) :=
    hLa0.1.trans (mul_le_mul_of_nonneg_left cpq hCl0)
  have f5 : sobNorm r (cx (aArr p) - cx (aArr q)) *
      sobNorm r (cx (fun x => jetDeriv (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) x
        κ.1.1 κ.1.2)) ≤ Cl0 * (16 * Xd) * KJ :=
    mul_le_mul f4 hJp (sobNorm_nonneg _ _) (by positivity)
  have g2 : sobNorm r ((cx (aArr p) - cx (aArr q)) *
      cx (fun x => jetDeriv (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) x
        κ.1.1 κ.1.2)) ≤ K3 * Xd := by
    refine f3.trans ?_
    rw [hK3def, mul_assoc]
    calc A0 * (sobNorm r (cx (aArr p) - cx (aArr q)) * sobNorm r (cx (fun x =>
          jetDeriv (fun _ _ => 0) p w (symRec (lawAccel (fun _ _ => 0) p w)) x κ.1.1 κ.1.2))) ≤
          A0 * (Cl0 * (16 * Xd) * KJ) := mul_le_mul_of_nonneg_left f5 hA0.le
      _ = A0 * (Cl0 * 16) * KJ * Xd := by ring
  have h1 := mul_le_mul_of_nonneg_left hEd (by positivity : (0 : ℝ) ≤ A0 + 1)
  have h2 := mul_le_mul_of_nonneg_left g2 (by positivity : (0 : ℝ) ≤ A0 + 1)
  have hfin : 0 ≤ (A0 + 1) * (K1 + K2 + K3) * (Xd + Fd) -
      ((A0 + 1) * (K1 * Xd + K2 * Fd) + (A0 + 1) * (K3 * Xd)) := by
    have e : (A0 + 1) * (K1 + K2 + K3) * (Xd + Fd) -
        ((A0 + 1) * (K1 * Xd + K2 * Fd) + (A0 + 1) * (K3 * Xd)) =
        (A0 + 1) * (K1 * Fd + K2 * Xd + K3 * Fd) := by ring
    rw [e]; positivity
  linarith

/-- Restriction of a law-family solution to a shorter interval. -/
theorem isAccSolution_mono_T {Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec}
    {T T' : ℝ} {q v : ℝ → Grid N → MetricRec} (h : IsAccSolution Acc T q v) (hT : T' ≤ T) :
    IsAccSolution Acc T' q v :=
  fun t ht => h t ⟨ht.1, ht.2.trans hT⟩

theorem isWriterSolution_mono_T {T T' : ℝ} {q v : ℝ → Grid N → MetricRec}
    (h : IsWriterSolution T q v) (hT : T' ≤ T) : IsWriterSolution T' q v :=
  fun t ht => h t ⟨ht.1, ht.2.trans hT⟩

theorem isAccSolution_zero_of_writer {T : ℝ} {q v : ℝ → Grid N → MetricRec}
    (h : IsWriterSolution T q v) : IsAccSolution (lawAccel (fun _ _ => 0)) T q v := by
  intro t ht
  obtain ⟨h1, h2, h3, h4⟩ := h t ht
  exact ⟨h1, h2, h3, fun x κ => by rw [lawAccel_zero]; exact h4 x κ⟩

/-- The mark part of the third time derivative:
`jetDeriv_B - jetDeriv_0 = a⁻¹ (-h² B Λ_h² v - ȧ f_B)` at the same record. -/
theorem jetDeriv_sub_zero_mark (B : Upper → Upper → ℝ) (q v W : Grid N → MetricRec) (x : Grid N)
    (μ ν : Fin 4) : jetDeriv B q v W x μ ν - jetDeriv (fun _ _ => 0) q v W x μ ν =
      (aArr q x)⁻¹ * (-bTerm B v x μ ν - adot q v x * lawForce B q x μ ν) := by
  have h0 : bTerm (fun _ _ => 0) v x μ ν = 0 := by rw [bTerm_zero_mark]; rfl
  have h1 : lawAccel B q v x μ ν - lawAccel (fun _ _ => 0) q v x μ ν = lawForce B q x μ ν := by
    have e1 : lawAccel (fun _ _ => 0) q v = harmonicWriterAcceleration q v := lawAccel_zero q v
    rw [e1]; simp [lawAccel]
  simp only [jetDeriv, h0]
  rw [← h1]; ring

set_option maxHeartbeats 4000000 in
/-- **The full law jet comparison** (`eq:supp-law-jet-comparison`, `j = 0, 1, 2, 3`), with an
explicit common top chart.  For `s ≥ 6` there is a chart radius `ρ > 0` and, for every horizon
`T ≥ 0`, a constant `C ≥ 0`, independent of the mesh `h = 1/N` and of the mark, such that for
every mark `B = Bᵀ`, `‖B‖_op ≤ b ≤ 1/48`, every solution `X_B` of the law writer and every
solution `X_0` of the central writer on `[0, T]` with the same initial record, both in the top
ball `‖·‖_{X^s_h} ≤ E ≤ ρ`, and every `t ∈ [0, T]` and upper component `κ`:
* `q_B''' = jetDeriv B …` and `q_0''' = jetDeriv 0 …` are the time derivatives (within
  `[0, T]`) of `q_B'' = V_{B,h}(q_B, q_B')` and `q_0'' = V_{0,h}(q_0, q_0')`;
* `‖(q_B - q_0, q_B' - q_0')‖_{X^{s-2}_h} + ‖q_B'' - q_0''‖_{s-3,h} + ‖q_B''' - q_0'''‖_{s-4,h}
  ≤ C h b E` (the first norm controls `‖q_B - q_0‖_{s-1,h}` and `‖q_B' - q_0'‖_{s-2,h}`). -/
theorem law_jet_comparison (s : ℕ) (hs : 6 ≤ s) :
    ∃ ρ > 0, ∀ T, 0 ≤ T → ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (b : ℝ) (B : Upper → Upper → ℝ),
      IsMark b B → b ≤ 1 / 48 → ∀ (E : ℝ) (qB vB q0 v0 : ℝ → Grid N → MetricRec),
      qB 0 = q0 0 → vB 0 = v0 0 →
      IsAccSolution (lawAccel B) T qB vB → IsWriterSolution T q0 v0 →
      (∀ t ∈ Icc 0 T, Xnorm s (qB t) (vB t) ≤ E) → (∀ t ∈ Icc 0 T, Xnorm s (q0 t) (v0 t) ≤ E) →
      E ≤ ρ → ∀ t ∈ Icc 0 T, ∀ κ : Upper,
        (∀ x, HasDerivWithinAt (fun τ => lawAccel B (qB τ) (vB τ) x κ.1.1 κ.1.2)
          (jetDeriv B (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x κ.1.1 κ.1.2)
          (Icc 0 T) t) ∧
        (∀ x, HasDerivWithinAt (fun τ => harmonicWriterAcceleration (q0 τ) (v0 τ) x κ.1.1 κ.1.2)
          (jetDeriv (fun _ _ => 0) (q0 t) (v0 t)
            (symRec (harmonicWriterAcceleration (q0 t) (v0 t))) x κ.1.1 κ.1.2) (Icc 0 T) t) ∧
        Xnorm (s - 2) (qB t - q0 t) (vB t - v0 t) +
          Fnorm (s - 3) (lawAccel B (qB t) (vB t) - harmonicWriterAcceleration (q0 t) (v0 t)) +
          PeriodicGridSobolev.sobNorm (s - 4)
            (cx (fun x => jetDeriv B (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x
              κ.1.1 κ.1.2) -
            cx (fun x => jetDeriv (fun _ _ => 0) (q0 t) (v0 t)
              (symRec (harmonicWriterAcceleration (q0 t) (v0 t))) x κ.1.1 κ.1.2)) ≤
          C * (N : ℝ)⁻¹ * b * E := by
  open PeriodicGridSobolev PeriodicGridSobolev.Moser in
  obtain ⟨δW, hδW, KW, hKW, hW⟩ := open_writer_difference s (s - 2) (by omega) (by omega)
  obtain ⟨δK, hδK, KK, hKK, hK⟩ := dAcc_bound s (s - 2) (by omega) (by omega)
  obtain ⟨δF, hδF, CF, hCF, hF⟩ := Fnorm_lawForce_mesh (s - 2) (by omega)
  obtain ⟨δF4, hδF4, CF4, hCF4, hF4⟩ := Fnorm_lawForce_mesh (s - 4) (by omega)
  obtain ⟨ρc, hρc, hcont⟩ := continuousOn_lawForce_of_chart s (by omega)
  obtain ⟨δJ, hδJ, CJ, hCJ, hJ⟩ := law_time_jets s (by omega)
  obtain ⟨δL, hδL, KL, hKL, hLip⟩ := jetDeriv_lipschitz s hs
  obtain ⟨δa, hδa, Ca, hCa, hma⟩ := moser_coefficients (s - 4) (by omega)
  obtain ⟨δr, hδr, Cr, hCr, hmr⟩ := moser_rate_coefficients (s - 4) (by omega)
  set A4 := algConst (s - 4)
  have hA4 := algConst_pos (s - 4)
  refine ⟨min (min (min δW δK) (min δF δF4)) (min (min ρc δJ) (min δL (min (δa / 16)
      (min (δr / 32) (min (1 / (16 * (Ca + 1))) 1))))), by positivity, fun T hT => ?_⟩
  set C₁ : ℝ := 2 * Real.exp (KW * T) * KW * T * CF
  have hC₁ : 0 ≤ C₁ := by positivity
  set C₂ : ℝ := 16 * (KK * (C₁ + CF))
  set C₃ : ℝ := (A4 + 1) * (288 + A4 * (Cr * 32) * CF4)
  refine ⟨C₁ + C₂ + (C₃ + KL * (C₁ + C₂)), by positivity,
    fun N _ b B hB hb E qB vB q0 v0 hq0 hv0 hsolB hsol0 hXB hX0 hEρ t ht κ => ?_⟩
  have hb0 := hB.nonneg
  have hB' : IsMark (1 / 48) B := hB.mono hb
  have hNi : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hE0 : 0 ≤ E := (Xnorm_nonneg _ _ _).trans (hX0 0 ⟨le_rfl, hT⟩)
  have mρ : ∀ a, min (min (min δW δK) (min δF δF4)) (min (min ρc δJ) (min δL (min (δa / 16)
      (min (δr / 32) (min (1 / (16 * (Ca + 1))) 1))))) ≤ a → E ≤ a := fun a ha => hEρ.trans ha
  have hEW := mρ δW (by simp)
  have hEK := mρ δK (by simp)
  have hEF := mρ δF (by simp)
  have hEF4 := mρ δF4 (by simp)
  have hEc := mρ ρc (by simp)
  have hEJ := mρ δJ (by simp)
  have hEL := mρ δL (by simp)
  have hEa := mρ (δa / 16) (by simp)
  have hEr := mρ (δr / 32) (by simp)
  have hECa := mρ (1 / (16 * (Ca + 1))) (by simp)
  have hE1 := mρ 1 (by simp)
  clear mρ
  have hsol0' := isAccSolution_zero_of_writer hsol0
  -- the comparison force
  have hforce : ∀ τ ∈ Icc 0 T, Fnorm (s - 2) (lawForce B (qB τ)) ≤ CF * (N : ℝ)⁻¹ * b * E := by
    intro τ hτ
    obtain ⟨hqs, -, -, -⟩ := hsolB τ hτ
    have hX : Xnorm (s - 2 + 2) (qB τ) (vB τ) ≤ E := by
      rw [show s - 2 + 2 = s by omega]; exact hXB τ hτ
    have h := hF N b B (qB τ) (vB τ) hB hqs (hX.trans hEF)
    rw [show s - 2 + 2 = s by omega] at h
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_left (hXB τ hτ) (by positivity : (0 : ℝ) ≤ CF * (N : ℝ)⁻¹ * b)
    linarith
  have hpair : IsForcedPair s δW T qB q0 vB v0 (fun τ => lawForce B (qB τ)) (fun _ => 0) := by
    intro τ hτ
    obtain ⟨hqs, hvs, hq, hv⟩ := hsolB τ hτ
    obtain ⟨hq0s, hv0s, hq0d, hv0d⟩ := hsol0 τ hτ
    refine ⟨hqs, hvs, hq0s, hv0s, hq, hq0d, fun x κ => hv x κ, fun x κ => ?_,
      (hXB τ hτ).trans hEW, (hX0 τ hτ).trans hEW⟩
    refine (hv0d x κ).congr_deriv ?_
    simp
  have hfc : ContinuousOn (fun τ => lawForce B (qB τ)) (Icc 0 T) :=
    hcont N B T qB vB (fun τ hτ => continuousAt_pi.2 fun x => ((hsolB τ hτ).2.2.1 x).continuousAt)
      (fun τ hτ => (hsolB τ hτ).1) (fun τ hτ => (hXB τ hτ).trans hEc)
  have hd := hW N T qB q0 vB v0 (fun τ => lawForce B (qB τ)) (fun _ => 0) hpair hfc
    continuousOn_const t ht
  have hinit : Xnorm (s - 2) (qB 0 - q0 0) (vB 0 - v0 0) = 0 := by
    rw [hq0, hv0, sub_self, sub_self]
    have : Xsq (s - 2) (0 : RootParityConnector.Grid N → MetricRec) 0 = 0 := by
      unfold Xsq
      refine sum_eq_zero fun κ _ => ?_
      have e : cx (comp (0 : RootParityConnector.Grid N → MetricRec) κ.1.1 κ.1.2) = 0 := by
        funext x; simp [comp, cx]
      rw [e]
      simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
    rw [Xnorm, this, Real.sqrt_zero]
  rw [hinit, mul_zero, zero_add] at hd
  have hint : (∫ τ in (0)..t, Fnorm (s - 2) (lawForce B (qB τ) - (fun _ => 0) τ)) ≤
      T * (CF * (N : ℝ)⁻¹ * b * E) := by
    have hcI : ContinuousOn (fun τ => Fnorm (s - 2) (lawForce B (qB τ) - (fun _ => 0) τ))
        (Icc 0 t) := by
      have : (fun τ => Fnorm (s - 2) (lawForce B (qB τ) - (fun _ => (0 : RootParityConnector.Grid N → MetricRec)) τ)) =
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
    have h2 : 0 ≤ CF * (N : ℝ)⁻¹ * b * E := by positivity
    calc _ ≤ t * (CF * (N : ℝ)⁻¹ * b * E) := h1
      _ ≤ T * (CF * (N : ℝ)⁻¹ * b * E) := mul_le_mul_of_nonneg_right ht.2 h2
  have hX2 : Xnorm (s - 2) (qB t - q0 t) (vB t - v0 t) ≤ C₁ * (N : ℝ)⁻¹ * b * E := by
    refine hd.trans ?_
    have hexp : Real.exp (KW * t) ≤ Real.exp (KW * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hKW)
    have hI0 : 0 ≤ ∫ τ in (0)..t, Fnorm (s - 2) (lawForce B (qB τ) - (fun _ => 0) τ) :=
      intervalIntegral.integral_nonneg ht.1 fun τ _ => Fnorm_nonneg _ _
    calc 2 * Real.exp (KW * t) * (KW * ∫ τ in (0)..t,
          Fnorm (s - 2) (lawForce B (qB τ) - (fun _ => 0) τ)) ≤
          2 * Real.exp (KW * T) * (KW * (T * (CF * (N : ℝ)⁻¹ * b * E))) := by
          have := mul_nonneg hKW hI0
          gcongr
      _ = C₁ * (N : ℝ)⁻¹ * b * E := by simp only [C₁]; ring
  -- the second slot
  have hacc : Fnorm (s - 3) (lawAccel B (qB t) (vB t) - harmonicWriterAcceleration (q0 t) (v0 t)) ≤
      C₂ * (N : ℝ)⁻¹ * b * E := by
    have hM : 0 ≤ KK * ((C₁ + CF) * (N : ℝ)⁻¹ * b * E) := by positivity
    refine (lawDiff_Fnorm_le_of_comp_le (s - 3) _ hM fun κ => ?_).trans (le_of_eq (by ring))
    obtain ⟨hqs, hvs, -, -⟩ := hsolB t ht
    obtain ⟨hq0s, hv0s, -, -⟩ := hsol0 t ht
    have e : lawAccel B (qB t) (vB t) - harmonicWriterAcceleration (q0 t) (v0 t) =
        dAcc (qB t) (q0 t) (vB t) (v0 t) (lawForce B (qB t)) 0 := by
      funext x μ ν
      simp [dAcc, lawAccel]
    rw [e]
    have h := hK N (qB t) (q0 t) (vB t) (v0 t) (lawForce B (qB t)) 0 hqs hq0s hvs hv0s
      ((hXB t ht).trans hEK) ((hX0 t ht).trans hEK) κ
    rw [show s - 2 - 1 = s - 3 by omega, sub_zero] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hKK)
    have := hforce t ht
    nlinarith
  -- the time derivatives
  have hjB := hJ N B T E qB vB hB' hEJ hsolB hXB t ht κ
  have hj0 := hJ N (fun _ _ => 0) T E q0 v0 isMark_zero hEJ hsol0' hX0 t ht κ
  simp only [lawAccel_zero] at hj0
  refine ⟨hjB.1, hj0.1, ?_⟩
  -- the third slot
  obtain ⟨hqs, hvs, -, -⟩ := hsolB t ht
  obtain ⟨hq0s, hv0s, -, -⟩ := hsol0 t ht
  have hL := hLip N B (qB t) (vB t) (q0 t) (v0 t) hB' hqs hvs hq0s hv0s ((hXB t ht).trans hEL)
    ((hX0 t ht).trans hEL) κ
  simp only [lawAccel_zero] at hL
  have hmark : sobNorm (s - 4)
      (cx (fun x => jetDeriv B (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x κ.1.1 κ.1.2) -
        cx (fun x => jetDeriv (fun _ _ => 0) (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x
          κ.1.1 κ.1.2)) ≤ C₃ * (N : ℝ)⁻¹ * b * E := by
    set X := Xnorm s (qB t) (vB t)
    have hXE : X ≤ E := hXB t ht
    have hX0' : 0 ≤ X := Xnorm_nonneg _ _ _
    have e : cx (fun x => jetDeriv B (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x κ.1.1 κ.1.2) -
        cx (fun x => jetDeriv (fun _ _ => 0) (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x
          κ.1.1 κ.1.2) = cx (fun x => (aArr (qB t) x)⁻¹) *
        (-cx (comp (bTerm B (vB t)) κ.1.1 κ.1.2) -
          cx (adot (qB t) (vB t)) * cx (comp (lawForce B (qB t)) κ.1.1 κ.1.2)) := by
      funext x
      have := jetDeriv_sub_zero_mark B (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x
        κ.1.1 κ.1.2
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, cx_apply, comp]
      rw [← Complex.ofReal_sub, this]
      push_cast; ring
    rw [e]
    have hcs : coordSum (s - 4) bM (qB t) ≤ 16 * X := coordSum_bM_q_le s hqs (vB t) (by omega)
    have hcv : coordSum (s - 4) bM (vB t) ≤ 16 * X := coordSum_bM_v_le s (qB t) hvs (by omega)
    have hM := hma N (qB t) (hcs.trans (by linarith))
    have hCaX : Ca * (16 * X) ≤ 1 := by
      have h := hECa; rw [le_div_iff₀ (by positivity)] at h; nlinarith
    have hainv : sobNorm (s - 4) (cx (fun x => (aArr (qB t) x)⁻¹) - fun _ => (1 : ℂ)) ≤ 1 :=
      hM.2.1.trans ((mul_le_mul_of_nonneg_left hcs hCa).trans hCaX)
    refine (sobNorm_coef_mul_le (s - 4) (by omega) _ _ 1 (by simp) hainv).trans ?_
    have h1 : sobNorm (s - 4) (cx (comp (bTerm B (vB t)) κ.1.1 κ.1.2)) ≤
        288 * b * (N : ℝ)⁻¹ * E := by
      refine (sobNorm_bTerm_mesh (s - 4) hB hvs 0 κ).trans ?_
      rw [show s - 4 + 2 = s - 2 by omega]
      have hv1 : Xnorm (s - 2) (vB t) 0 ≤ X := by
        refine (lawDiff_Xnorm_mono (by omega : s - 2 ≤ s - 1) _ _).trans ?_
        rcases Xnorm_vel_le s (qB t) (vB t) with h | h
        · exact h
        · omega
      have := mul_le_mul_of_nonneg_left (hv1.trans hXE) (by positivity : (0 : ℝ) ≤ 288 * b * (N : ℝ)⁻¹)
      linarith
    have h2 : sobNorm (s - 4) (cx (adot (qB t) (vB t))) ≤ Cr * 32 := by
      have hR := (hmr N (qB t) (vB t) (by linarith)).1
      refine hR.trans ?_
      have : coordSum (s - 4) bM (qB t) + coordSum (s - 4) bM (vB t) ≤ 32 := by linarith
      nlinarith
    have h3 : sobNorm (s - 4) (cx (comp (lawForce B (qB t)) κ.1.1 κ.1.2)) ≤
        CF4 * (N : ℝ)⁻¹ * b * E := by
      refine (sobNorm_le_Fnorm (s - 4) _ κ).trans ?_
      have hX' : Xnorm (s - 4 + 2) (qB t) (vB t) ≤ E := by
        refine (lawDiff_Xnorm_mono (by omega) _ _).trans hXE
      have h := hF4 N b B (qB t) (vB t) hB hqs (hX'.trans hEF4)
      refine h.trans ?_
      have := mul_le_mul_of_nonneg_left hX' (by positivity : (0 : ℝ) ≤ CF4 * (N : ℝ)⁻¹ * b)
      linarith
    have h4 : sobNorm (s - 4) (-cx (comp (bTerm B (vB t)) κ.1.1 κ.1.2) -
        cx (adot (qB t) (vB t)) * cx (comp (lawForce B (qB t)) κ.1.1 κ.1.2)) ≤
        288 * b * (N : ℝ)⁻¹ * E + A4 * (Cr * 32) * (CF4 * (N : ℝ)⁻¹ * b * E) := by
      refine (sobNorm_sub_le _ _ _).trans ?_
      rw [sobNorm_neg]
      have h5 := sobNorm_mul_le (s - 4) (by omega) (cx (adot (qB t) (vB t)))
        (cx (comp (lawForce B (qB t)) κ.1.1 κ.1.2))
      have h6 : A4 * sobNorm (s - 4) (cx (adot (qB t) (vB t))) *
          sobNorm (s - 4) (cx (comp (lawForce B (qB t)) κ.1.1 κ.1.2)) ≤
          A4 * (Cr * 32) * (CF4 * (N : ℝ)⁻¹ * b * E) := by
        have := mul_le_mul h2 h3 (sobNorm_nonneg _ _) (by positivity)
        calc A4 * sobNorm (s - 4) (cx (adot (qB t) (vB t))) *
              sobNorm (s - 4) (cx (comp (lawForce B (qB t)) κ.1.1 κ.1.2)) =
              A4 * (sobNorm (s - 4) (cx (adot (qB t) (vB t))) *
                sobNorm (s - 4) (cx (comp (lawForce B (qB t)) κ.1.1 κ.1.2))) := by ring
          _ ≤ A4 * ((Cr * 32) * (CF4 * (N : ℝ)⁻¹ * b * E)) :=
            mul_le_mul_of_nonneg_left this hA4.le
          _ = _ := by ring
      linarith
    calc (A4 + 1) * sobNorm (s - 4) (-cx (comp (bTerm B (vB t)) κ.1.1 κ.1.2) -
          cx (adot (qB t) (vB t)) * cx (comp (lawForce B (qB t)) κ.1.1 κ.1.2)) ≤
          (A4 + 1) * (288 * b * (N : ℝ)⁻¹ * E + A4 * (Cr * 32) * (CF4 * (N : ℝ)⁻¹ * b * E)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = C₃ * (N : ℝ)⁻¹ * b * E := by simp only [C₃]; ring
  have h3rd : sobNorm (s - 4)
      (cx (fun x => jetDeriv B (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x κ.1.1 κ.1.2) -
        cx (fun x => jetDeriv (fun _ _ => 0) (q0 t) (v0 t)
          (symRec (harmonicWriterAcceleration (q0 t) (v0 t))) x κ.1.1 κ.1.2)) ≤
      C₃ * (N : ℝ)⁻¹ * b * E + KL * ((C₁ + C₂) * (N : ℝ)⁻¹ * b * E) := by
    have e : cx (fun x => jetDeriv B (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x κ.1.1 κ.1.2) -
        cx (fun x => jetDeriv (fun _ _ => 0) (q0 t) (v0 t)
          (symRec (harmonicWriterAcceleration (q0 t) (v0 t))) x κ.1.1 κ.1.2) =
        (cx (fun x => jetDeriv B (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x κ.1.1 κ.1.2) -
          cx (fun x => jetDeriv (fun _ _ => 0) (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x
            κ.1.1 κ.1.2)) +
        (cx (fun x => jetDeriv (fun _ _ => 0) (qB t) (vB t) (symRec (lawAccel B (qB t) (vB t))) x
            κ.1.1 κ.1.2) -
          cx (fun x => jetDeriv (fun _ _ => 0) (q0 t) (v0 t)
            (symRec (harmonicWriterAcceleration (q0 t) (v0 t))) x κ.1.1 κ.1.2)) := by abel
    rw [e]
    refine (sobNorm_add_le _ _ _).trans (add_le_add hmark (hL.trans ?_))
    refine mul_le_mul_of_nonneg_left ?_ hKL
    have := add_le_add hX2 hacc
    linarith
  calc _ ≤ C₁ * (N : ℝ)⁻¹ * b * E + C₂ * (N : ℝ)⁻¹ * b * E +
        (C₃ * (N : ℝ)⁻¹ * b * E + KL * ((C₁ + C₂) * (N : ℝ)⁻¹ * b * E)) :=
        add_le_add (add_le_add hX2 hacc) h3rd
    _ = (C₁ + C₂ + (C₃ + KL * (C₁ + C₂))) * (N : ℝ)⁻¹ * b * E := by ring

/-- Non-vacuity of `law_jet_comparison`: the flat histories of both writers satisfy its
hypotheses on `[0, 1]` for every mesh, with `E = 0`. -/
example (s : ℕ) (hs : 6 ≤ s) : True := by
  obtain ⟨ρ, hρ, h⟩ := law_jet_comparison s hs
  obtain ⟨C, hC, h1⟩ := h 1 zero_le_one
  have hsolB : IsAccSolution (lawAccel (fun _ _ => 0)) 1 (fun _ => (0 : Grid 5 → MetricRec))
      (fun _ => 0) := by
    intro t _
    refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun x => hasDerivAt_const _ _, fun x κ => ?_⟩
    rw [lawAccel_zero_state]
    exact hasDerivAt_const _ _
  have hsol0 : IsWriterSolution 1 (fun _ => (0 : Grid 5 → MetricRec)) (fun _ => 0) := by
    intro t _
    refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun x => hasDerivAt_const _ _, fun x κ => ?_⟩
    show HasDerivAt _ (harmonicWriterAcceleration (0 : Grid 5 → MetricRec) 0 x κ.1.1 κ.1.2) t
    rw [harmonicWriterAcceleration_zero]
    exact hasDerivAt_const _ _
  have hX : ∀ t ∈ Icc (0 : ℝ) 1, Xnorm s ((fun _ => (0 : Grid 5 → MetricRec)) t)
      ((fun _ => (0 : Grid 5 → MetricRec)) t) ≤ 0 := by
    intro t _
    have : Xsq s (0 : Grid 5 → MetricRec) 0 = 0 := by
      unfold Xsq
      refine sum_eq_zero fun κ _ => ?_
      have e : cx (comp (0 : Grid 5 → MetricRec) κ.1.1 κ.1.2) = 0 := by funext x; simp [comp, cx]
      rw [e]
      simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
    simp only [Xnorm, this, Real.sqrt_zero, le_refl]
  have := h1 5 (1 / 48) (fun _ _ => 0) isMark_zero_jet le_rfl 0 _ _ _ _ rfl rfl hsolB hsol0 hX hX
    hρ.le 0 ⟨le_rfl, zero_le_one⟩
  trivial

end

end RenewalGeometry.OpenWriterLifespan
