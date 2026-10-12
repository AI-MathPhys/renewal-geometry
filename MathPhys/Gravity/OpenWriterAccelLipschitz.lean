/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Gravity.OpenWriterDifferenceEstimate

/-!
# Record-norm comparisons and the one-order-down Lipschitz bound of the open writer

Infrastructure for the periodic-grid harmonic-gauge writer `V_{0,h}` on ten-component records:

* `Xnorm_le_sum`: the phase-space norm `‖(Q, V)‖_{X^r_h}` is bounded by the sum of the
  component Sobolev norms;
* `lawDiff_Fnorm_le_of_comp_le`: `‖F‖_{r,h} ≤ 16 M` when every upper component is bounded by
  `M` in `H^r_h`;
* `dAcc_bound`: the writer acceleration with forcing is Lipschitz one order down,
  `‖(V_{0,h}(q,v) + f) - (V_{0,h}(p,w) + f̃)‖_{r-1,h} ≤ K (‖δX‖_{X^r_h} + ‖f - f̃‖_{r,h})`,
  uniformly in the mesh.

Split out of `OpenWriterTimeJets` and `OpenWriterLawDifference` (declaration names unchanged);
those files treat the law family `B` built on top of the writer.
-/

open Set Metric Filter Topology Finset MeasureTheory
open scoped NNReal BigOperators

namespace MathPhys.OpenWriterLifespan

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterEnergyEstimate

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]


theorem Xnorm_le_sum (r : ℕ) (Q V : Grid N → MetricRec) :
    Xnorm r Q V ≤ ∑ κ : Upper, (PeriodicGridSobolev.sobNorm (r + 1) (cx (comp Q κ.1.1 κ.1.2)) +
      PeriodicGridSobolev.sobNorm r (cx (comp V κ.1.1 κ.1.2))) := by
  have h0 : 0 ≤ ∑ κ : Upper, (PeriodicGridSobolev.sobNorm (r + 1) (cx (comp Q κ.1.1 κ.1.2)) +
      PeriodicGridSobolev.sobNorm r (cx (comp V κ.1.1 κ.1.2))) :=
    sum_nonneg fun _ _ => add_nonneg (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _)
      (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _)
  unfold Xnorm
  rw [Real.sqrt_le_left h0]
  unfold Xsq
  calc ∑ κ : Upper, (PeriodicGridSobolev.sobSq (r + 1) (cx (comp Q κ.1.1 κ.1.2)) +
        PeriodicGridSobolev.sobSq r (cx (comp V κ.1.1 κ.1.2))) ≤
        ∑ κ : Upper, (PeriodicGridSobolev.sobNorm (r + 1) (cx (comp Q κ.1.1 κ.1.2)) +
          PeriodicGridSobolev.sobNorm r (cx (comp V κ.1.1 κ.1.2))) ^ 2 := by
        refine sum_le_sum fun κ _ => ?_
        rw [← PeriodicGridSobolev.sobNorm_sq, ← PeriodicGridSobolev.sobNorm_sq]
        have := PeriodicGridSobolev.Moser.sobNorm_nonneg (r + 1) (cx (comp Q κ.1.1 κ.1.2))
        have := PeriodicGridSobolev.Moser.sobNorm_nonneg r (cx (comp V κ.1.1 κ.1.2))
        nlinarith
    _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg fun κ _ =>
        add_nonneg (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _)
          (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _)

/-- `‖F‖_{r,h} ≤ 16 M` when every upper component is bounded by `M` in `H^r_h`. -/
theorem lawDiff_Fnorm_le_of_comp_le (r : ℕ) (F : Grid N → MetricRec) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ κ : Upper, PeriodicGridSobolev.sobNorm r (cx (comp F κ.1.1 κ.1.2)) ≤ M) :
    Fnorm r F ≤ 16 * M := by
  have hc : (Fintype.card Upper : ℝ) ≤ 16 := by
    have h1 : Fintype.card Upper ≤ Fintype.card (Fin 4 × Fin 4) := Fintype.card_subtype_le _
    have h2 : Fintype.card (Fin 4 × Fin 4) = 16 := by simp
    exact_mod_cast h1.trans h2.le
  unfold Fnorm
  rw [Real.sqrt_le_left (by positivity)]
  calc ∑ κ : Upper, PeriodicGridSobolev.sobSq r (cx (comp F κ.1.1 κ.1.2)) ≤ ∑ _κ : Upper, M ^ 2 :=
        sum_le_sum fun κ _ => by
          rw [← PeriodicGridSobolev.sobNorm_sq]
          exact pow_le_pow_left₀ (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _) (h κ) 2
    _ = (Fintype.card Upper : ℝ) * M ^ 2 := by simp
    _ ≤ 16 * M ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ ≤ (16 * M) ^ 2 := by nlinarith [sq_nonneg M]

set_option maxHeartbeats 4000000 in
/-- **Lipschitz bound of the writer acceleration one order down** (the bound `hδvt` inside
`diff_static_bound`, exported): for `3 ≤ r`, `r + 1 ≤ s` there are `δ > 0`, `K ≥ 0`,
independent of the mesh, such that for two symmetric records in the top chart and forces
`f, f̃`, `‖(V_{0,h}(q,v) + f) - (V_{0,h}(p,w) + f̃)‖_{r-1,h} ≤ K (‖δX‖_{X^r_h} + ‖f - f̃‖_{r,h})`
componentwise. -/
theorem dAcc_bound (s r : ℕ) (hr : 3 ≤ r) (hrs : r + 1 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (q p v w f g : Grid N → MetricRec),
      IsSymRec q → IsSymRec p → IsSymRec v → IsSymRec w → Xnorm s q v ≤ δ → Xnorm s p w ≤ δ →
      ∀ κ : Upper, PeriodicGridSobolev.sobNorm (r - 1) (cx (comp (dAcc q p v w f g) κ.1.1 κ.1.2)) ≤
        K * (Xnorm r (q - p) (v - w) + Fnorm r (f - g)) := by
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
  refine ⟨δ, hδ, CV, hCV, fun N _ q p v w f g hq hp hv hw hXq hXp => ?_⟩
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
  exact hδvt

end

end MathPhys.OpenWriterLifespan
