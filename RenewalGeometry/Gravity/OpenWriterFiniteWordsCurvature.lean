/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterFiniteWordsUniform

/-!
# Curvature convergence along the law family and along the finite successor words
  (`thm:main-open-law-basin` (L2), `thm:main-open-3plus1` (O3)/(O4); emergent-spacetime manuscript)

* `law_family_curvature` (**(L2), curvature convergence uniformly on the coefficient ball**): for
  every sequence of marks `B_n` of the closed ball, the law-family histories from the harmonic
  preparation have interpolated metrics converging to the harmonic vacuum development `g` of
  `supp_open_einstein`, and `‖Riem(g_{B,h}) - Riem(g)‖_{H^{s-3}} ≤ C h ε` with `C` independent of
  the cutoff and of the marks.
* `finite_words_curvature` (**(O4): the certified finite histories inherit the curvature
  convergence of (O3)**): the same for the bank words of the compatible finite initialization.

Proof: the Lipschitz Moser estimate for `riemOf` (`pjet_moser_fin`) applied along the jet chain
word → exact law history (`finite_words_compare`, `accJet_diff`) → central writer (the four-slot
comparison of `supp_law_einstein`, `accJet_diff`) → continuum (the Riemann rate of
`supp_open_einstein`); the central histories of the two theorems are identified by uniqueness
next to a small writer solution (`writer_eq_of_small`).
-/

open Set Metric Filter Topology Finset MeasureTheory UnitAddTorus
open scoped NNReal BigOperators Real

namespace RenewalGeometry.OpenWriterFiniteWords

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterContinuum PeriodicGridSobolev.Composition OpenWriterGridBridge
  RootParityConnector HarmonicWriter OpenWriterLimitRegularity OpenWriterSubsidiary
  HarmonicGaugePropagation ContractedBianchiJet HarmonicDefect OpenWriterRateLift
  OpenWriterLocalJets
open PeriodicGridSobolev (GridH)

noncomputable section

set_option linter.unusedSectionVars false

/-- The Lipschitz Moser estimate for the Riemann tensor of small jet fields. -/
theorem finiteWords_riem_lipschitz (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (P P' : C(T3, PJet)), (∀ j, MemH r ⇑(ccoord bPJ P j)) →
      (∀ j, MemH r ⇑(ccoord bPJ P' j)) → ccoordSum r bPJ P ≤ δ → ccoordSum r bPJ P' ≤ δ →
      ∀ a b c d : Fin 4, ∃ F : CT,
        (∀ y, F y = ((riemOf (P y) a b c d - riemOf (P' y) a b c d : ℝ) : ℂ)) ∧ MemH r ⇑F ∧
          sn r ⇑F ≤ C * ccoordSum r bPJ (P - P') := by
  obtain ⟨δ, hδ, C, hC, hm⟩ := pjet_moser_fin r hr
    (fun p : Fin 4 × Fin 4 × Fin 4 × Fin 4 => fun z => riemOf z p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun p => analyticAt_riemOf _ _ _ _ 0 det_minkowski_add_zero)
  exact ⟨δ, hδ, C, hC, fun P P' hP hP' hPδ hP'δ a b c d => hm (a, b, c, d) P P' hP hP' hPδ hP'δ⟩


set_option maxHeartbeats 4000000 in
-- the identification of the central histories and the three-link jet chain in one statement
/-- **(L2): curvature convergence, uniformly on the coefficient ball** (`thm:main-open-law-basin`,
"the metric, subsidiary, noncollapse and curvature conclusions of `thm:main-open-3plus1` are uniform
on the entire coefficient ball", curvature-convergence part).  For `s ≥ 6` there are `εs, T > 0` and
`C ≥ 0`, independent of the cutoff, such that for every `(γ, K) ∈ D_s(ε)`, `ε ≤ εs`, with harmonic
preparation `V₀` and harmonic vacuum development `g = η + Q` (`supp_open_einstein`; `G(g) = 0`), and
for every sequence of marks `B_n` of the closed ball (no convergence), the law-family histories from
the samples of `(Q₀, V₀)` have interpolated metrics converging to `Q` on `[0, T]` and
`‖Riem(g_{B_n,h}) - Riem(g)‖_{H^{s-3}} ≤ C h ε` componentwise, with one constant `C` for all marks. -/
theorem law_family_curvature (s : ℕ) (hs : 6 ≤ s) :
    ∃ εs > 0, ∃ T > 0, ∃ C ≥ 0, ∀ (Q₀ Kr : C(T3, MetricRec)) (Qd Kd : Fin 3 → C(T3, MetricRec))
      (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      DsData s Q₀ Kr Qd Kd Qdd → dataSize s Q₀ Kr ≤ ε → ε ≤ εs →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
      ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd' Vd' : ℝ → Fin 3 → C(T3, MetricRec))
        (Qdd' : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
        (∀ t ∈ Set.Icc 0 T, IsContJet (Q t) (V t) (Qd' t) (Vd' t) (Qdd' t) ∧
          ∀ y μ ν, einstein (minkowski + Q t y) (recInv (minkowski + Q t y))
            (metricJet (V t y, fun i => Qd' t i y))
            (ddArr (A t y) (fun i => Vd' t i y) (fun i j => Qdd' t i j y)) μ ν = 0) ∧
        ∀ (b : ℕ → ℝ) (B : ℕ → Upper → Upper → ℝ), (∀ n, IsMark (b n) (B n)) →
          (∀ n, b n ≤ 1 / 48) →
          ∃ qB vB : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec,
            (∀ n, IsAccSolution (lawAccel (B n)) T (qB n) (vB n) ∧
              qB n 0 = sampleRec (n + 1) ⇑Q₀ ∧ vB n 0 = sampleRec (n + 1) ⇑V₀) ∧
            ∀ t ∈ Set.Icc 0 T,
              Tendsto (fun n => interpRec (qB n t)) atTop (𝓝 (Q t)) ∧
              ∀ n (a b' c d : Fin 4), ∃ F : CT,
                (∀ y, F y = ((riemOf (accJet (qB n t) (vB n t)
                    (lawAccel (B n) (qB n t) (vB n t)) y) a b' c d -
                  riemOf (pjetField (Q t) (V t) (A t) (Qd' t) (Vd' t) (Qdd' t) y) a b' c d :
                    ℝ) : ℂ)) ∧
                MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * ε * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨εO, hεO, TO, hTO, KO, hKO, CO, hCO, CεO, hCεO, hO⟩ := supp_open_einstein s hs
  obtain ⟨εL, hεL, TL, hTL, TBL, hTBL, KL0, _, CL0, _, Cε0, _, CB, hCB, hLE⟩ :=
    supp_law_einstein s hs
  obtain ⟨bU, hbU, hUniq⟩ := writer_eq_of_small s (by omega)
  obtain ⟨δA, hδA, KA, hKA, hacc⟩ := accel_bound s (by omega)
  obtain ⟨δL, hδL, KL, hKL, hlacc⟩ := lawAccel_bound s (by omega)
  obtain ⟨δM, hδM, CM, hCM, hRm⟩ := finiteWords_riem_lipschitz (s - 3) (by omega)
  set T : ℝ := min TO TL
  have hT : 0 < T := lt_min hTO hTL
  have hTO' : T ≤ TO := min_le_left _ _
  have hTL' : T ≤ TL := min_le_right _ _
  set Kx : ℝ := KA + KL
  have hKx : 0 ≤ Kx := by positivity
  set S3 : ℝ := sizeConst s Kx
  have hS3 : 0 ≤ S3 := by simp only [S3, sizeConst]; positivity
  set P : ℝ := diffConst s
  have hP : 0 ≤ P := diffConst_nonneg s
  set δ : ℝ := min (min bU δA) (min δL δM)
  have hδ : 0 < δ := by positivity
  set εs : ℝ := min (min εO εL) (δ / ((S3 + 1) * (CB + 1)))
  have hεs : 0 < εs := by positivity
  set C : ℝ := CM * (288 * P * CB) + CO * Real.exp (KO * T) * (1 + T) * CεO
  refine ⟨εs, hεs, T, hT, C, by positivity, fun Q₀ Kr Qd Kd Qdd ε hD hsz hεε => ?_⟩
  have hε0 : 0 ≤ ε := (add_nonneg (ccoordSum_nonneg _ _ _) (ccoordSum_nonneg _ _ _)).trans hsz
  have hεO : ε ≤ εO := hεε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεL : ε ≤ εL := hεε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hXδ : (S3 + 1) * (CB * ε) ≤ δ := by
    have h1 : ε ≤ δ / ((S3 + 1) * (CB + 1)) := hεε.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    have : (S3 + 1) * (CB * ε) ≤ ε * ((S3 + 1) * (CB + 1)) := by nlinarith
    linarith
  have hCBδ : CB * ε ≤ δ := by nlinarith
  have hS3δ : S3 * (CB * ε) ≤ δ := by nlinarith
  obtain ⟨V₀, hV₀, qO, vO, hsolO, -, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, hcont⟩ :=
    hO Q₀ Kr Qd Kd Qdd ε hD hsz hεO
  obtain ⟨V₀', hV₀', qL, vL, hsolL, QL, VL, AL, QdL, VdL, QddL, -, -, -, hfamL⟩ :=
    hLE Q₀ Kr Qd Kd Qdd ε hD hsz hεL
  have hVV : V₀' = V₀ := DFunLike.coe_injective (hV₀'.trans hV₀.symm)
  subst hVV
  refine ⟨V₀', hV₀', Q, V, A, Qd', Vd', Qdd', hQ0, hV0, fun t ht => ?_, fun b B hB hb => ?_⟩
  · obtain ⟨⟨-, -, -, -, -, -, -, cJ, -, -, -, -⟩, cE⟩ := hcont t ⟨ht.1, ht.2.trans hTO'⟩
    exact ⟨cJ, cE⟩
  obtain ⟨qB, vB, hsolB, -, hbndB, hcmpB, -⟩ := hfamL b B hB hb
  refine ⟨qB, vB, fun n => ⟨restrict_acc (hsolB n).1 (hTL'.trans hTBL), (hsolB n).2.1,
    (hsolB n).2.2⟩, fun t ht => ?_⟩
  have htO : t ∈ Set.Icc 0 TO := ⟨ht.1, ht.2.trans hTO'⟩
  have htL : t ∈ Set.Icc 0 TL := ⟨ht.1, ht.2.trans hTL'⟩
  have htB : t ∈ Set.Icc 0 TBL := ⟨ht.1, (ht.2.trans hTL').trans hTBL⟩
  -- the central histories of the two theorems coincide on `[0, T]`
  have hid : ∀ n, qO n t = qL n t ∧ vO n t = vL n t := by
    intro n
    refine hUniq (n + 1) T (qL n) (vL n) (qO n) (vO n) (restrict_writer (hsolL n).1 hTL')
      (restrict_writer (hsolO n).1 hTO') ((hsolO n).2.1.trans (hsolL n).2.1.symm)
      ((hsolO n).2.2.trans (hsolL n).2.2.symm) (fun τ hτ => ?_) t ht
    exact (hbndB n τ ⟨hτ.1, hτ.2.trans hTL'⟩).2.trans
      (hCBδ.trans ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨⟨c1, -, -, -, -, -, -, -, -, -, -, cRiem⟩, -⟩ := hcont t htO
  have hsB : ∀ n, IsSymRec (qB n t) ∧ IsSymRec (vB n t) := fun n =>
    ⟨((hsolB n).1 t htB).1, ((hsolB n).1 t htB).2.1⟩
  have hsL : ∀ n, IsSymRec (qL n t) ∧ IsSymRec (vL n t) := fun n =>
    ⟨((hsolL n).1 t htL).1, ((hsolL n).1 t htL).2.1⟩
  -- the four-slot comparison of the law history with the central writer
  have hDiff : ∀ n, Xnorm (s - 2) (qB n t - qL n t) (vB n t - vL n t) +
      Fnorm (s - 3) (lawAccel (B n) (qB n t) (vB n t) - harmonicWriterAcceleration (qL n t) (vL n t))
        ≤ CB * ε * ((n : ℝ) + 1)⁻¹ := by
    intro n
    have h := ((hcmpB n t htL) (upperOf 0 0)).2.2
    have h0 := PeriodicGridSobolev.Moser.sobNorm_nonneg (s - 4)
      (cx (fun x => jetDeriv (B n) (qB n t) (vB n t)
        (symRec (lawAccel (B n) (qB n t) (vB n t))) x (upperOf 0 0).1.1 (upperOf 0 0).1.2) -
      cx (fun x => jetDeriv (fun _ _ => 0) (qL n t) (vL n t)
        (symRec (harmonicWriterAcceleration (qL n t) (vL n t))) x (upperOf 0 0).1.1
          (upperOf 0 0).1.2))
    have hb1 : b n ≤ 1 := (hb n).trans (by norm_num)
    have hbn : 0 ≤ b n := (hB n).nonneg
    have : CB * ((n : ℝ) + 1)⁻¹ * b n * ε ≤ CB * ε * ((n : ℝ) + 1)⁻¹ := by
      have hw : 0 ≤ CB * ε * ((n : ℝ) + 1)⁻¹ := by positivity
      have e : CB * ((n : ℝ) + 1)⁻¹ * b n * ε = (CB * ε * ((n : ℝ) + 1)⁻¹) * b n := by ring
      rw [e]; nlinarith
    linarith
  refine ⟨?_, fun n a b' c d => ?_⟩
  · -- metric convergence
    have hr : Tendsto (fun n : ℕ => Real.sqrt (pc 2) * (CB * ε) * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (Real.sqrt (pc 2) * (CB * ε))
      simpa using this
    refine lawLimit_tendsto_of_upper_rate c1 (fun n y μ ν => interpRec_symm (hsB n).1 y μ ν)
      (fun n y μ ν => interpRec_symm ((hid n).1 ▸ (hsL n).1) y μ ν) _ hr 0 fun n _ κ => ?_
    have h := lawLimit_interp_diff 2 (qB n t) (qO n t) κ.1.1 κ.1.2
    refine ⟨h.1, h.2.trans ?_⟩
    rw [(hid n).1]
    have h1 := sobNorm_q_le (s - 2) (isSymRec_sub (hsB n).1 (hsL n).1) (vB n t - vL n t)
      κ.1.1 κ.1.2 (r := 2) (by omega)
    have h2 := hDiff n
    have h3 := Fnorm_nonneg (s - 3)
      (lawAccel (B n) (qB n t) (vB n t) - harmonicWriterAcceleration (qL n t) (vL n t))
    have h4 : PeriodicGridSobolev.sobNorm 2 (cx (comp (qB n t - qL n t) κ.1.1 κ.1.2)) ≤
        CB * ε * ((n : ℝ) + 1)⁻¹ := by linarith
    calc Real.sqrt (pc 2) * PeriodicGridSobolev.sobNorm 2 (cx (comp (qB n t - qL n t) κ.1.1 κ.1.2))
        ≤ Real.sqrt (pc 2) * (CB * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
      _ = _ := by ring
  -- the curvature: law → central → continuum
  have hXB : Xnorm s (qB n t) (vB n t) ≤ CB * ε := (hbndB n t htL).1
  have hXL : Xnorm s (qL n t) (vL n t) ≤ CB * ε := (hbndB n t htL).2
  have hmark : IsMark (1 / 48) (B n) := (hB n).mono (hb n)
  have hδA' : CB * ε ≤ δA := hCBδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδL' : CB * ε ≤ δL := hCBδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδM' : S3 * (CB * ε) ≤ δM := hS3δ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hJB : ccoordSum (s - 3) bPJ (accJet (qB n t) (vB n t) (lawAccel (B n) (qB n t) (vB n t)))
      ≤ S3 * (CB * ε) := by
    refine accJet_size s (by omega) (hsB n).1 (hsB n).2 _ hKx hXB fun κ => ?_
    refine (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
      ((hlacc (n + 1) (B n) (qB n t) (vB n t) hmark (hsB n).1 (hsB n).2 (hXB.trans hδL') κ).trans ?_)
    exact mul_le_mul (by simp only [Kx]; linarith) hXB (Xnorm_nonneg _ _ _) hKx
  have hJL : ccoordSum (s - 3) bPJ (accJet (qL n t) (vL n t)
      (harmonicWriterAcceleration (qL n t) (vL n t))) ≤ S3 * (CB * ε) := by
    refine accJet_size s (by omega) (hsL n).1 (hsL n).2 _ hKx hXL fun κ => ?_
    refine (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
      ((hacc (n + 1) (qL n t) (vL n t) (hsL n).1 (hsL n).2 (hXL.trans hδA') κ.1.1 κ.1.2).trans ?_)
    exact mul_le_mul (by simp only [Kx]; linarith) hXL (Xnorm_nonneg _ _ _) hKx
  obtain ⟨F1, hF1, hF1m, hF1s⟩ := hRm _ _ (accJet_memH _ _ _ _) (accJet_memH _ _ _ _)
    (hJB.trans hδM') (hJL.trans hδM') a b' c d
  obtain ⟨-, hdS⟩ := accJet_diff s (by omega) (hsB n).1 (hsB n).2 (hsL n).1 (hsL n).2
    (lawAccel (B n) (qB n t) (vB n t)) (harmonicWriterAcceleration (qL n t) (vL n t)) (hDiff n)
  obtain ⟨F2, hF2, hF2m, hF2s⟩ := cRiem n a b' c d
  refine ⟨F1 + F2, fun y => ?_, memH_add hF1m hF2m, (lawLimit_sn_add_le F1 F2 hF2m).trans ?_⟩
  · rw [ContinuousMap.add_apply, hF1 y, hF2 y, (hid n).1, (hid n).2]
    simp only [accJet]
    push_cast; ring
  · have hw : 0 ≤ ε * ((n : ℝ) + 1)⁻¹ := by positivity
    have k1 : sn (s - 3) ⇑F1 ≤ CM * (288 * P * CB) * (ε * ((n : ℝ) + 1)⁻¹) := by
      refine hF1s.trans ?_
      calc CM * ccoordSum (s - 3) bPJ _ ≤ CM * (288 * P * (CB * ε * ((n : ℝ) + 1)⁻¹)) :=
            mul_le_mul_of_nonneg_left hdS hCM
        _ = _ := by ring
    have k2 : sn (s - 3) ⇑F2 ≤ CO * Real.exp (KO * T) * (1 + T) * CεO * (ε * ((n : ℝ) + 1)⁻¹) := by
      refine hF2s.trans ?_
      have he : Real.exp (KO * t) ≤ Real.exp (KO * T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hKO)
      have h1t : 1 + t ≤ 1 + T := by linarith [ht.2]
      calc CO * Real.exp (KO * t) * (1 + t) * (CεO * ε) * ((n : ℝ) + 1)⁻¹ =
            (CO * Real.exp (KO * t) * (1 + t) * CεO) * (ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ (CO * Real.exp (KO * T) * (1 + T) * CεO) * (ε * ((n : ℝ) + 1)⁻¹) := by
            gcongr
            linarith [ht.1]
    calc sn (s - 3) ⇑F1 + sn (s - 3) ⇑F2 ≤ C * (ε * ((n : ℝ) + 1)⁻¹) := by
          simp only [C]; nlinarith
      _ = C * ε * ((n : ℝ) + 1)⁻¹ := by ring


set_option maxHeartbeats 8000000 in
-- the identification of the central histories and the four-link jet chain in one statement
/-- **(O4): the certified finite histories inherit the curvature convergence of (O3)**
(`thm:main-open-3plus1`).  Fix `s ≥ 6` and `c, c₀ ≥ 0`.  There is a slab `T > 0` such that for
every horizon `T₁ ∈ (0, T]` there are `εs > 0`, `C ≥ 0` and `n₀`, independent of the cutoff, with:
for every `(γ, K) ∈ D_s(ε)`, `ε ≤ εs`, with harmonic preparation `V₀` and harmonic vacuum
development `g = η + Q` (`supp_open_einstein`; `G(g) = 0`), arbitrary marks `B_n` of the closed ball
(the open writer is `B_n = 0`) and every sequence of bank words on `[0, T₁]` obeying the precision
convention `η = c ε h^{s+10}` and starting within `c₀ ε h⁴` of the samples of `(Q₀, V₀)`, the
interpolated word metrics converge to `Q` and `‖Riem(g_h^{word}) - Riem(g)‖_{H^{s-3}} ≤ C h ε`
componentwise for `n ≥ n₀`. -/
theorem finite_words_curvature (s : ℕ) (hs : 6 ≤ s) (cη c₀ : ℝ) (hcη : 0 ≤ cη) (hc₀ : 0 ≤ c₀) :
    ∃ T > 0, ∀ T₁, 0 < T₁ → T₁ ≤ T → ∃ εs > 0, ∃ C ≥ 0, ∃ n₀ : ℕ,
    ∀ (Q₀ Kr : C(T3, MetricRec)) (Qd Kd : Fin 3 → C(T3, MetricRec))
      (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      DsData s Q₀ Kr Qd Kd Qdd → dataSize s Q₀ Kr ≤ ε → ε ≤ εs →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
      ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd' Vd' : ℝ → Fin 3 → C(T3, MetricRec))
        (Qdd' : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
        (∀ t ∈ Set.Icc 0 T₁, IsContJet (Q t) (V t) (Qd' t) (Vd' t) (Qdd' t) ∧
          ∀ y μ ν, einstein (minkowski + Q t y) (recInv (minkowski + Q t y))
            (metricJet (V t y, fun i => Qd' t i y))
            (ddArr (A t y) (fun i => Vd' t i y) (fun i j => Qdd' t i j y)) μ ν = 0) ∧
        ∀ (b : ℕ → ℝ) (B : ℕ → Upper → Upper → ℝ), (∀ n, IsMark (b n) (B n)) →
          (∀ n, b n ≤ 1 / 48) →
          ∀ β : ∀ n : ℕ, ℕ → Fin 4 → Upper → GridH (n + 1) (s + 1),
          (∀ n, BankPrecise s (B n) (stepOf (n + 1) T₁)
            (cη * ε * (1 / (((n + 1 : ℕ) : ℝ))) ^ (s + 10)) (β n) (numCells (n + 1) T₁)) →
          (∀ n, Xnorm s (recOf (β n 0 0) - sampleRec (n + 1) ⇑Q₀)
            (recOf (β n 0 1) - sampleRec (n + 1) ⇑V₀) ≤ c₀ * ε * (1 / (((n + 1 : ℕ) : ℝ))) ^ 4) →
          ∀ t ∈ Set.Icc 0 T₁,
            Tendsto (fun n => interpRec ((bankWord s T₁ (β n)).path 0 t)) atTop (𝓝 (Q t)) ∧
            Tendsto (fun n => interpRec ((bankWord s T₁ (β n)).path 1 t)) atTop (𝓝 (V t)) ∧
            Tendsto (fun n => interpRec ((bankWord s T₁ (β n)).path 2 t)) atTop (𝓝 (A t)) ∧
            ∀ n, n₀ ≤ n → (bankWord s T₁ (β n)).recNorm s t ≤ C * ε ∧ ∀ (a b' c d : Fin 4), ∃ F : CT,
              (∀ y, F y = ((riemOf (accJet ((bankWord s T₁ (β n)).path 0 t)
                  ((bankWord s T₁ (β n)).path 1 t) ((bankWord s T₁ (β n)).path 2 t) y) a b' c d -
                riemOf (pjetField (Q t) (V t) (A t) (Qd' t) (Vd' t) (Qdd' t) y) a b' c d :
                  ℝ) : ℂ)) ∧
              MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * ε * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨εO, hεO, TO, hTO, KO, hKO, CO, hCO, CεO, hCεO, hO⟩ := supp_open_einstein s hs
  obtain ⟨εL, hεL, TL, hTL, TBL, hTBL, KL0, _, CL0, _, Cε0, _, CB, hCB, hLE⟩ :=
    supp_law_einstein s hs
  obtain ⟨bU, hbU, hUniq⟩ := writer_eq_of_small s (by omega)
  obtain ⟨δA, hδA, KA, hKA, hacc⟩ := accel_bound s (by omega)
  obtain ⟨δL, hδL, KL, hKL, hlacc⟩ := lawAccel_bound s (by omega)
  obtain ⟨δM, hδM, CM, hCM, hRm⟩ := finiteWords_riem_lipschitz (s - 3) (by omega)
  refine ⟨min TO TL, lt_min hTO hTL, fun T₁ hT₁ hT₁T => ?_⟩
  have hTO' : T₁ ≤ TO := hT₁T.trans (min_le_left _ _)
  have hTL' : T₁ ≤ TL := hT₁T.trans (min_le_right _ _)
  obtain ⟨εc, hεc, N₀, Dc, hDc, Xc, hXc, hcmp⟩ :=
    finite_words_compare s hs T₁ hT₁ cη c₀ CB hcη hc₀ hCB
  set S10 : ℝ := Real.sqrt (Fintype.card Upper)
  have hS10 : 0 ≤ S10 := Real.sqrt_nonneg _
  set Xc' : ℝ := Xc + CB + 1
  have hXc' : 1 ≤ Xc' := by simp only [Xc']; linarith
  set Kx : ℝ := KA + KL + Dc
  have hKx : 0 ≤ Kx := by positivity
  set S3 : ℝ := sizeConst s Kx
  have hS3 : 0 ≤ S3 := by simp only [S3, sizeConst]; positivity
  set P : ℝ := diffConst s
  have hP : 0 ≤ P := diffConst_nonneg s
  set Dc' : ℝ := Dc + S10 * Dc
  have hDc' : 0 ≤ Dc' := by positivity
  set δ : ℝ := min (min bU δA) (min δL δM)
  have hδ : 0 < δ := by positivity
  set εs : ℝ := min (min εO εL) (min εc (δ / ((S3 + 1) * (Xc' + 1))))
  have hεs : 0 < εs := by positivity
  set T : ℝ := min TO TL
  set C : ℝ := CM * (288 * P * Dc') + CM * (288 * P * CB) +
    CO * Real.exp (KO * T) * (1 + T) * CεO + Xc
  refine ⟨εs, hεs, C, by positivity, N₀, fun Q₀ Kr Qd Kd Qdd ε hD hsz hεε => ?_⟩
  have hε0 : 0 ≤ ε := (add_nonneg (ccoordSum_nonneg _ _ _) (ccoordSum_nonneg _ _ _)).trans hsz
  have hεO : ε ≤ εO := hεε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεL : ε ≤ εL := hεε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεc' : ε ≤ εc := hεε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hXδ : (S3 + 1) * (Xc' * ε) ≤ δ := by
    have h1 : ε ≤ δ / ((S3 + 1) * (Xc' + 1)) :=
      hεε.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    have : (S3 + 1) * (Xc' * ε) ≤ ε * ((S3 + 1) * (Xc' + 1)) := by nlinarith
    linarith
  have hXcδ : Xc' * ε ≤ δ := by nlinarith
  have hS3δ : S3 * (Xc' * ε) ≤ δ := by nlinarith
  have hCBX : CB * ε ≤ Xc' * ε := mul_le_mul_of_nonneg_right (by simp only [Xc']; linarith) hε0
  have hCBδ : CB * ε ≤ δ := hCBX.trans hXcδ
  obtain ⟨V₀, hV₀, qO, vO, hsolO, -, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, hcont⟩ :=
    hO Q₀ Kr Qd Kd Qdd ε hD hsz hεO
  obtain ⟨V₀', hV₀', qL, vL, hsolL, QL, VL, AL, QdL, VdL, QddL, -, -, -, hfamL⟩ :=
    hLE Q₀ Kr Qd Kd Qdd ε hD hsz hεL
  have hVV : V₀' = V₀ := DFunLike.coe_injective (hV₀'.trans hV₀.symm)
  subst hVV
  refine ⟨V₀', hV₀', Q, V, A, Qd', Vd', Qdd', hQ0, hV0, fun t ht => ?_,
    fun b B hB hb β hprec hstart t ht => ?_⟩
  · obtain ⟨⟨-, -, -, -, -, -, -, cJ, -, -, -, -⟩, cE⟩ := hcont t ⟨ht.1, ht.2.trans hTO'⟩
    exact ⟨cJ, cE⟩
  obtain ⟨qB, vB, hsolB, -, hbndB, hcmpB, -⟩ := hfamL b B hB hb
  have htO : t ∈ Set.Icc 0 TO := ⟨ht.1, ht.2.trans hTO'⟩
  have htL : t ∈ Set.Icc 0 TL := ⟨ht.1, ht.2.trans hTL'⟩
  have htB : t ∈ Set.Icc 0 TBL := ⟨ht.1, (ht.2.trans hTL').trans hTBL⟩
  have hid : ∀ n, qO n t = qL n t ∧ vO n t = vL n t := by
    intro n
    refine hUniq (n + 1) T₁ (qL n) (vL n) (qO n) (vO n) (restrict_writer (hsolL n).1 hTL')
      (restrict_writer (hsolO n).1 hTO') ((hsolO n).2.1.trans (hsolL n).2.1.symm)
      ((hsolO n).2.2.trans (hsolL n).2.2.symm) (fun τ hτ => ?_) t ht
    exact (hbndB n τ ⟨hτ.1, hτ.2.trans hTL'⟩).2.trans
      (hCBδ.trans ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨⟨c1, c2, c3, -, -, -, -, -, -, -, -, cRiem⟩, -⟩ := hcont t htO
  have hsB : ∀ n, IsSymRec (qB n t) ∧ IsSymRec (vB n t) := fun n =>
    ⟨((hsolB n).1 t htB).1, ((hsolB n).1 t htB).2.1⟩
  have hsL : ∀ n, IsSymRec (qL n t) ∧ IsSymRec (vL n t) := fun n =>
    ⟨((hsolL n).1 t htL).1, ((hsolL n).1 t htL).2.1⟩
  have hDiff : ∀ n, Xnorm (s - 2) (qB n t - qL n t) (vB n t - vL n t) +
      Fnorm (s - 3) (lawAccel (B n) (qB n t) (vB n t) - harmonicWriterAcceleration (qL n t) (vL n t))
        ≤ CB * ε * ((n : ℝ) + 1)⁻¹ := by
    intro n
    have h := ((hcmpB n t htL) (upperOf 0 0)).2.2
    have h0 := PeriodicGridSobolev.Moser.sobNorm_nonneg (s - 4)
      (cx (fun x => jetDeriv (B n) (qB n t) (vB n t)
        (symRec (lawAccel (B n) (qB n t) (vB n t))) x (upperOf 0 0).1.1 (upperOf 0 0).1.2) -
      cx (fun x => jetDeriv (fun _ _ => 0) (qL n t) (vL n t)
        (symRec (harmonicWriterAcceleration (qL n t) (vL n t))) x (upperOf 0 0).1.1
          (upperOf 0 0).1.2))
    have hb1 : b n ≤ 1 := (hb n).trans (by norm_num)
    have hbn : 0 ≤ b n := (hB n).nonneg
    have : CB * ((n : ℝ) + 1)⁻¹ * b n * ε ≤ CB * ε * ((n : ℝ) + 1)⁻¹ := by
      have hw : 0 ≤ CB * ε * ((n : ℝ) + 1)⁻¹ := by positivity
      have e : CB * ((n : ℝ) + 1)⁻¹ * b n * ε = (CB * ε * ((n : ℝ) + 1)⁻¹) * b n := by ring
      rw [e]; nlinarith
    linarith
  -- the comparison of the words with the exact law histories
  have hW : ∀ n, N₀ ≤ n →
      (bankWord s T₁ (β n)).recNorm s t ≤ Xc * ε ∧
      Xnorm (s - 1) ((bankWord s T₁ (β n)).path 0 t - qB n t)
        ((bankWord s T₁ (β n)).path 1 t - vB n t) ≤ Dc * ε * ((n : ℝ) + 1)⁻¹ ∧
      ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3) (cx (comp ((bankWord s T₁ (β n)).path 2 t -
        lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2)) ≤ Dc * ε * ((n : ℝ) + 1)⁻¹ := by
    intro n hn
    have hh : 1 / (((n + 1 : ℕ) : ℝ)) = ((n : ℝ) + 1)⁻¹ := by rw [Nat.cast_succ, one_div]
    have hstart' : Xnorm s (recOf (β n 0 0) - qB n 0) (recOf (β n 0 1) - vB n 0) ≤
        c₀ * ε * (1 / (((n + 1 : ℕ) : ℝ))) ^ 4 := by
      rw [(hsolB n).2.1, (hsolB n).2.2]; exact hstart n
    have h := hcmp (n + 1) (by omega) (B n) ((hB n).mono (hb n)) (β n) ε hε0 hεc' (qB n) (vB n)
      TBL (hTL'.trans hTBL) (hsolB n).1 (fun τ hτ => (hbndB n τ ⟨hτ.1, hτ.2.trans hTL'⟩).1)
      (hprec n) hstart' t ht
    rw [hh] at h
    exact h
  have hsW : ∀ n k, IsSymRec ((bankWord s T₁ (β n)).path k t) := fun n k =>
    LawWord.isSymRec_path (bankWord s T₁ (β n))
      (fun j i => isSymRec_recOf (bankLetter (stepOf (n + 1) T₁) (β n) j i)) k t
  -- the law histories converge to `Q`
  have hcB : Tendsto (fun n => interpRec (qB n t)) atTop (𝓝 (Q t)) := by
    have hr : Tendsto (fun n : ℕ => Real.sqrt (pc 2) * (CB * ε) * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (Real.sqrt (pc 2) * (CB * ε))
      simpa using this
    refine lawLimit_tendsto_of_upper_rate c1 (fun n y μ ν => interpRec_symm (hsB n).1 y μ ν)
      (fun n y μ ν => interpRec_symm ((hid n).1 ▸ (hsL n).1) y μ ν) _ hr 0 fun n _ κ => ?_
    have h := lawLimit_interp_diff 2 (qB n t) (qO n t) κ.1.1 κ.1.2
    refine ⟨h.1, h.2.trans ?_⟩
    rw [(hid n).1]
    have h1 := sobNorm_q_le (s - 2) (isSymRec_sub (hsB n).1 (hsL n).1) (vB n t - vL n t)
      κ.1.1 κ.1.2 (r := 2) (by omega)
    have h2 := hDiff n
    have h3 := Fnorm_nonneg (s - 3)
      (lawAccel (B n) (qB n t) (vB n t) - harmonicWriterAcceleration (qL n t) (vL n t))
    have h4 : PeriodicGridSobolev.sobNorm 2 (cx (comp (qB n t - qL n t) κ.1.1 κ.1.2)) ≤
        CB * ε * ((n : ℝ) + 1)⁻¹ := by linarith
    calc Real.sqrt (pc 2) * PeriodicGridSobolev.sobNorm 2 (cx (comp (qB n t - qL n t) κ.1.1 κ.1.2))
        ≤ Real.sqrt (pc 2) * (CB * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hrB : Tendsto (fun n : ℕ => Real.sqrt (pc 2) * (CB * ε) * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (Real.sqrt (pc 2) * (CB * ε))
    simpa using this
  have hrW : Tendsto (fun n : ℕ => Real.sqrt (pc 2) * (Dc * ε) * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (Real.sqrt (pc 2) * (Dc * ε))
    simpa using this
  have hcBv : Tendsto (fun n => interpRec (vB n t)) atTop (𝓝 (V t)) := by
    refine lawLimit_tendsto_of_upper_rate c2 (fun n y μ ν => interpRec_symm (hsB n).2 y μ ν)
      (fun n y μ ν => interpRec_symm ((hid n).2 ▸ (hsL n).2) y μ ν) _ hrB 0 fun n _ κ => ?_
    have h := lawLimit_interp_diff 2 (vB n t) (vO n t) κ.1.1 κ.1.2
    refine ⟨h.1, h.2.trans ?_⟩
    rw [(hid n).2]
    have h1 := sobNorm_v_le (s - 2) (qB n t - qL n t) (isSymRec_sub (hsB n).2 (hsL n).2)
      κ.1.1 κ.1.2 (r := 2) (by omega)
    have h2 := hDiff n
    have h3 := Fnorm_nonneg (s - 3)
      (lawAccel (B n) (qB n t) (vB n t) - harmonicWriterAcceleration (qL n t) (vL n t))
    have h4 : PeriodicGridSobolev.sobNorm 2 (cx (comp (vB n t - vL n t) κ.1.1 κ.1.2)) ≤
        CB * ε * ((n : ℝ) + 1)⁻¹ := by linarith
    calc Real.sqrt (pc 2) * PeriodicGridSobolev.sobNorm 2 (cx (comp (vB n t - vL n t) κ.1.1 κ.1.2))
        ≤ Real.sqrt (pc 2) * (CB * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hcBa : Tendsto (fun n => interpRec (symRec (lawAccel (B n) (qB n t) (vB n t)))) atTop
      (𝓝 (A t)) := by
    refine lawLimit_tendsto_of_upper_rate c3 (fun n y μ ν => interpRec_symRec_symm _ y μ ν)
      (fun n y μ ν => interpRec_symRec_symm _ y μ ν) _ hrB 0 fun n _ κ => ?_
    rw [cmp_interpRec_symRec, cmp_interpRec_symRec]
    have h := lawLimit_interp_diff 2 (lawAccel (B n) (qB n t) (vB n t))
      (harmonicWriterAcceleration (qO n t) (vO n t)) κ.1.1 κ.1.2
    refine ⟨h.1, h.2.trans ?_⟩
    rw [(hid n).1, (hid n).2]
    have h1 := (PeriodicGridSobolev.Moser.sobNorm_mono (show 2 ≤ s - 3 by omega) _).trans
      (sobNorm_le_Fnorm (s - 3)
        (lawAccel (B n) (qB n t) (vB n t) - harmonicWriterAcceleration (qL n t) (vL n t)) κ)
    have h2 := hDiff n
    have h3 := Xnorm_nonneg (s - 2) (qB n t - qL n t) (vB n t - vL n t)
    have h4 : PeriodicGridSobolev.sobNorm 2 (cx (comp (lawAccel (B n) (qB n t) (vB n t) -
        harmonicWriterAcceleration (qL n t) (vL n t)) κ.1.1 κ.1.2)) ≤
        CB * ε * ((n : ℝ) + 1)⁻¹ := by linarith
    calc _ ≤ Real.sqrt (pc 2) * (CB * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
      _ = _ := by ring
  refine ⟨?_, ?_, ?_, fun n hn => ⟨?_, fun a b' c d => ?_⟩⟩
  · -- the word metrics converge to `Q`
    have hr : Tendsto (fun n : ℕ => Real.sqrt (pc 2) * (Dc * ε) * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (Real.sqrt (pc 2) * (Dc * ε))
      simpa using this
    refine lawLimit_tendsto_of_upper_rate hcB (fun n y μ ν => interpRec_symm (hsW n 0) y μ ν)
      (fun n y μ ν => interpRec_symm (hsB n).1 y μ ν) _ hr N₀ fun n hn κ => ?_
    have h := lawLimit_interp_diff 2 ((bankWord s T₁ (β n)).path 0 t) (qB n t) κ.1.1 κ.1.2
    refine ⟨h.1, h.2.trans ?_⟩
    have h1 := sobNorm_q_le (s - 1) (isSymRec_sub (hsW n 0) (hsB n).1)
      ((bankWord s T₁ (β n)).path 1 t - vB n t) κ.1.1 κ.1.2 (r := 2) (by omega)
    have h4 := h1.trans (hW n hn).2.1
    calc Real.sqrt (pc 2) * PeriodicGridSobolev.sobNorm 2
          (cx (comp ((bankWord s T₁ (β n)).path 0 t - qB n t) κ.1.1 κ.1.2))
        ≤ Real.sqrt (pc 2) * (Dc * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
      _ = _ := by ring
  · -- the word velocities converge to `V`
    refine lawLimit_tendsto_of_upper_rate hcBv (fun n y μ ν => interpRec_symm (hsW n 1) y μ ν)
      (fun n y μ ν => interpRec_symm (hsB n).2 y μ ν) _ hrW N₀ fun n hn κ => ?_
    have h := lawLimit_interp_diff 2 ((bankWord s T₁ (β n)).path 1 t) (vB n t) κ.1.1 κ.1.2
    refine ⟨h.1, h.2.trans ?_⟩
    have h1 := sobNorm_v_le (s - 1) ((bankWord s T₁ (β n)).path 0 t - qB n t)
      (isSymRec_sub (hsW n 1) (hsB n).2) κ.1.1 κ.1.2 (r := 2) (by omega)
    have h4 := h1.trans (hW n hn).2.1
    calc Real.sqrt (pc 2) * PeriodicGridSobolev.sobNorm 2
          (cx (comp ((bankWord s T₁ (β n)).path 1 t - vB n t) κ.1.1 κ.1.2))
        ≤ Real.sqrt (pc 2) * (Dc * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
      _ = _ := by ring
  · -- the word accelerations converge to `A`
    refine lawLimit_tendsto_of_upper_rate hcBa (fun n y μ ν => interpRec_symm (hsW n 2) y μ ν)
      (fun n y μ ν => interpRec_symRec_symm _ y μ ν) _ hrW N₀ fun n hn κ => ?_
    rw [cmp_interpRec_symRec]
    have h := lawLimit_interp_diff 2 ((bankWord s T₁ (β n)).path 2 t)
      (lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2
    refine ⟨h.1, h.2.trans ?_⟩
    have h4 := (PeriodicGridSobolev.Moser.sobNorm_mono (show 2 ≤ s - 3 by omega) _).trans
      ((hW n hn).2.2 κ)
    calc _ ≤ Real.sqrt (pc 2) * (Dc * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
      _ = _ := by ring
  · -- the record bound
    refine (hW n hn).1.trans (mul_le_mul_of_nonneg_right ?_ hε0)
    have : 0 ≤ CM * (288 * P * Dc') + CM * (288 * P * CB) +
        CO * Real.exp (KO * T) * (1 + T) * CεO := by positivity
    simp only [C]; linarith
  -- the curvature: word → law → central → continuum
  obtain ⟨w1, w2, w3⟩ := hW n hn
  set W := bankWord s T₁ (β n)
  have hXB : Xnorm s (qB n t) (vB n t) ≤ Xc' * ε := (hbndB n t htL).1.trans hCBX
  have hXL : Xnorm s (qL n t) (vL n t) ≤ Xc' * ε := (hbndB n t htL).2.trans hCBX
  have hXW : Xnorm s (W.path 0 t) (W.path 1 t) ≤ Xc' * ε :=
    w1.trans (mul_le_mul_of_nonneg_right (by simp only [Xc']; linarith) hε0)
  have hmark : IsMark (1 / 48) (B n) := (hB n).mono (hb n)
  have hδA' : Xc' * ε ≤ δA := hXcδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδL' : Xc' * ε ≤ δL := hXcδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδM' : S3 * (Xc' * ε) ≤ δM := hS3δ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hfB : ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3)
      (cx (comp (lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2)) ≤ KL * (Xc' * ε) := fun κ =>
    (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
      ((hlacc (n + 1) (B n) (qB n t) (vB n t) hmark (hsB n).1 (hsB n).2 (hXB.trans hδL') κ).trans
        (mul_le_mul_of_nonneg_left hXB hKL))
  have hJB : ccoordSum (s - 3) bPJ (accJet (qB n t) (vB n t) (lawAccel (B n) (qB n t) (vB n t)))
      ≤ S3 * (Xc' * ε) := by
    refine accJet_size s (by omega) (hsB n).1 (hsB n).2 _ hKx hXB fun κ => (hfB κ).trans ?_
    exact mul_le_mul_of_nonneg_right (by simp only [Kx]; linarith) (by positivity)
  have hJL : ccoordSum (s - 3) bPJ (accJet (qL n t) (vL n t)
      (harmonicWriterAcceleration (qL n t) (vL n t))) ≤ S3 * (Xc' * ε) := by
    refine accJet_size s (by omega) (hsL n).1 (hsL n).2 _ hKx hXL fun κ => ?_
    refine (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
      ((hacc (n + 1) (qL n t) (vL n t) (hsL n).1 (hsL n).2 (hXL.trans hδA') κ.1.1 κ.1.2).trans ?_)
    exact mul_le_mul (by simp only [Kx]; linarith) hXL (Xnorm_nonneg _ _ _) hKx
  have hJW : ccoordSum (s - 3) bPJ (accJet (W.path 0 t) (W.path 1 t) (W.path 2 t))
      ≤ S3 * (Xc' * ε) := by
    refine accJet_size s (by omega) (hsW n 0) (hsW n 1) _ hKx hXW fun κ => ?_
    have e : comp (W.path 2 t) κ.1.1 κ.1.2 =
        comp (W.path 2 t - lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2 +
          comp (lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2 := by
      funext x; simp only [comp, Pi.sub_apply, Pi.add_apply]; ring
    rw [e, cx_add]
    refine (PeriodicGridSobolev.Moser.sobNorm_add_le _ _ _).trans ?_
    have a1 := w3 κ
    have a2 := hfB κ
    have k1 : Dc * ε * ((n : ℝ) + 1)⁻¹ ≤ Dc * (Xc' * ε) := by
      have hn1 : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by have := (n.cast_nonneg : (0 : ℝ) ≤ n); linarith)
      have : ε * ((n : ℝ) + 1)⁻¹ ≤ Xc' * ε := by nlinarith
      calc Dc * ε * ((n : ℝ) + 1)⁻¹ = Dc * (ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ Dc * (Xc' * ε) := mul_le_mul_of_nonneg_left this hDc
    have e2 : Kx * (Xc' * ε) = KA * (Xc' * ε) + KL * (Xc' * ε) + Dc * (Xc' * ε) := by
      simp only [Kx]; ring
    have : 0 ≤ KA * (Xc' * ε) := by positivity
    linarith
  have hdiffW : Xnorm (s - 2) (W.path 0 t - qB n t) (W.path 1 t - vB n t) +
      Fnorm (s - 3) (W.path 2 t - lawAccel (B n) (qB n t) (vB n t)) ≤
        Dc' * ε * ((n : ℝ) + 1)⁻¹ := by
    have a1 := (lawDiff_Xnorm_mono (r := s - 2) (r' := s - 1) (by omega) _ _).trans w2
    have a2 := finiteWords_Fnorm_le_of_sobNorm_le _ (by positivity) w3
    have e : Dc' * ε * ((n : ℝ) + 1)⁻¹ =
        Dc * ε * ((n : ℝ) + 1)⁻¹ + S10 * (Dc * ε * ((n : ℝ) + 1)⁻¹) := by simp only [Dc']; ring
    linarith
  obtain ⟨F0, hF0, hF0m, hF0s⟩ := hRm _ _ (accJet_memH _ _ _ _) (accJet_memH _ _ _ _)
    (hJW.trans hδM') (hJB.trans hδM') a b' c d
  obtain ⟨-, hdS0⟩ := accJet_diff s (by omega) (hsW n 0) (hsW n 1) (hsB n).1 (hsB n).2
    (W.path 2 t) (lawAccel (B n) (qB n t) (vB n t)) hdiffW
  obtain ⟨F1, hF1, hF1m, hF1s⟩ := hRm _ _ (accJet_memH _ _ _ _) (accJet_memH _ _ _ _)
    (hJB.trans hδM') (hJL.trans hδM') a b' c d
  obtain ⟨-, hdS⟩ := accJet_diff s (by omega) (hsB n).1 (hsB n).2 (hsL n).1 (hsL n).2
    (lawAccel (B n) (qB n t) (vB n t)) (harmonicWriterAcceleration (qL n t) (vL n t)) (hDiff n)
  obtain ⟨F2, hF2, hF2m, hF2s⟩ := cRiem n a b' c d
  refine ⟨F0 + (F1 + F2), fun y => ?_, memH_add hF0m (memH_add hF1m hF2m),
    (lawLimit_sn_add_le F0 (F1 + F2) (memH_add hF1m hF2m)).trans
      (add_le_add le_rfl (lawLimit_sn_add_le F1 F2 hF2m)) |>.trans ?_⟩
  · rw [ContinuousMap.add_apply, ContinuousMap.add_apply, hF0 y, hF1 y, hF2 y, (hid n).1,
      (hid n).2]
    simp only [accJet]
    push_cast; ring
  · have hw : 0 ≤ ε * ((n : ℝ) + 1)⁻¹ := by positivity
    have k0 : sn (s - 3) ⇑F0 ≤ CM * (288 * P * Dc') * (ε * ((n : ℝ) + 1)⁻¹) := by
      refine hF0s.trans ?_
      calc CM * ccoordSum (s - 3) bPJ _ ≤ CM * (288 * P * (Dc' * ε * ((n : ℝ) + 1)⁻¹)) :=
            mul_le_mul_of_nonneg_left hdS0 hCM
        _ = _ := by ring
    have k1 : sn (s - 3) ⇑F1 ≤ CM * (288 * P * CB) * (ε * ((n : ℝ) + 1)⁻¹) := by
      refine hF1s.trans ?_
      calc CM * ccoordSum (s - 3) bPJ _ ≤ CM * (288 * P * (CB * ε * ((n : ℝ) + 1)⁻¹)) :=
            mul_le_mul_of_nonneg_left hdS hCM
        _ = _ := by ring
    have k2 : sn (s - 3) ⇑F2 ≤ CO * Real.exp (KO * T) * (1 + T) * CεO * (ε * ((n : ℝ) + 1)⁻¹) := by
      refine hF2s.trans ?_
      have htT : t ≤ T := ht.2.trans hT₁T
      have he : Real.exp (KO * t) ≤ Real.exp (KO * T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hKO)
      have h1t : 1 + t ≤ 1 + T := by linarith
      calc CO * Real.exp (KO * t) * (1 + t) * (CεO * ε) * ((n : ℝ) + 1)⁻¹ =
            (CO * Real.exp (KO * t) * (1 + t) * CεO) * (ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ (CO * Real.exp (KO * T) * (1 + T) * CεO) * (ε * ((n : ℝ) + 1)⁻¹) := by
            gcongr
            linarith [ht.1]
    calc sn (s - 3) ⇑F0 + (sn (s - 3) ⇑F1 + sn (s - 3) ⇑F2) ≤ C * (ε * ((n : ℝ) + 1)⁻¹) := by
          have : 0 ≤ Xc * (ε * ((n : ℝ) + 1)⁻¹) := by positivity
          simp only [C]; nlinarith
      _ = C * ε * ((n : ℝ) + 1)⁻¹ := by ring


/-- `UniformO3` is monotone in its constant. -/
theorem finiteWords_uniformO3_mono {s : ℕ} {C C' ε : ℝ} {n : ℕ} {q v f : Grid (n + 1) → MetricRec}
    (h : UniformO3 s C ε n q v f) (hC : C ≤ C') (hε : 0 ≤ ε) : UniformO3 s C' ε n q v f := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have k : C * ε * ((n : ℝ) + 1)⁻¹ ≤ C' * ε * ((n : ℝ) + 1)⁻¹ := by gcongr
  have k' : C * ε ≤ C' * ε := mul_le_mul_of_nonneg_right hC hε
  refine ⟨fun b => ?_, fun b => ?_, fun μ ν => ?_, fun a b c d => ?_, h5, h6⟩
  · obtain ⟨F, hF, hm, hs⟩ := h1 b; exact ⟨F, hF, hm, hs.trans k⟩
  · obtain ⟨F, hF, hm, hs⟩ := h2 b; exact ⟨F, hF, hm, hs.trans k⟩
  · obtain ⟨F, hF, hm, hs⟩ := h3 μ ν; exact ⟨F, hF, hm, hs.trans k⟩
  · obtain ⟨F, hF, hm, hs⟩ := h4 a b c d; exact ⟨F, hF, hm, hs.trans k'⟩

set_option maxHeartbeats 4000000 in
-- the assembly of the three word theorems on one vacuum development
/-- **`thm:main-open-3plus1` (O4), assembled on ONE vacuum development `g`.**  Fix `s ≥ 6` and
`c, c₀ ≥ 0`.  There is a slab `T > 0` such that for every horizon `T₁ ∈ (0, T]` there are
`εs > 0`, `C ≥ 0` and `n₀`, independent of the cutoff, with: for every `(γ, K) ∈ D_s(ε)`,
`ε ≤ εs`, with harmonic preparation `V₀`, there is one continuum jet `(Q, V, A, ∂Q, ∂V, ∂²Q)` of a
vacuum development `g = η + Q` with the prescribed data (`G(g) = 0` on `[0, T₁]`) such that for
arbitrary marks `B_n` of the closed ball (the open writer is `B_n = 0`) and every sequence of bank
words on `[0, T₁]` obeying the precision convention `c ε h^{s+10}` and starting within `c₀ ε h⁴` of
the samples of `(Q₀, V₀)`:
* the interpolated word records `(Q_h, Q_h', Q_h'')` converge to `(Q, V, A)` (O2), and for
  `n ≥ n₀`:
* `‖(Q_h, Q_h')(t)‖_{X^s_h} ≤ C ε` (O1);
* `‖g_h - g‖_{H^{s-1}} + ‖∂ₜg_h - ∂ₜg‖_{H^{s-2}} + ‖∂ₜ²g_h - ∂ₜ²g‖_{H^{s-3}} ≤ C h ε` componentwise (O2);
* the whole `(O3)` package `UniformO3` (subsidiary, its actual time derivative, Einstein residual
  `≤ C h ε`, curvature `≤ C ε`, rate lift, cut margin, noncollapse), and
  `‖Riem(g_h) - Riem(g)‖_{H^{s-3}} ≤ C h ε` (O3). -/
theorem main_open_finite_realization (s : ℕ) (hs : 6 ≤ s) (cη c₀ : ℝ) (hcη : 0 ≤ cη)
    (hc₀ : 0 ≤ c₀) :
    ∃ T > 0, ∀ T₁, 0 < T₁ → T₁ ≤ T → ∃ εs > 0, ∃ C ≥ 0, ∃ n₀ : ℕ,
    ∀ (Q₀ Kr : C(T3, MetricRec)) (Qd Kd : Fin 3 → C(T3, MetricRec))
      (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      DsData s Q₀ Kr Qd Kd Qdd → dataSize s Q₀ Kr ≤ ε → ε ≤ εs →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
      ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd' Vd' : ℝ → Fin 3 → C(T3, MetricRec))
        (Qdd' : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
        (∀ t ∈ Set.Icc 0 T₁, IsContJet (Q t) (V t) (Qd' t) (Vd' t) (Qdd' t) ∧
          ∀ y μ ν, einstein (minkowski + Q t y) (recInv (minkowski + Q t y))
            (metricJet (V t y, fun i => Qd' t i y))
            (ddArr (A t y) (fun i => Vd' t i y) (fun i j => Qdd' t i j y)) μ ν = 0) ∧
        ∀ (b : ℕ → ℝ) (B : ℕ → Upper → Upper → ℝ), (∀ n, IsMark (b n) (B n)) →
          (∀ n, b n ≤ 1 / 48) →
          ∀ β : ∀ n : ℕ, ℕ → Fin 4 → Upper → GridH (n + 1) (s + 1),
          (∀ n, BankPrecise s (B n) (stepOf (n + 1) T₁)
            (cη * ε * (1 / (((n + 1 : ℕ) : ℝ))) ^ (s + 10)) (β n) (numCells (n + 1) T₁)) →
          (∀ n, Xnorm s (recOf (β n 0 0) - sampleRec (n + 1) ⇑Q₀)
            (recOf (β n 0 1) - sampleRec (n + 1) ⇑V₀) ≤ c₀ * ε * (1 / (((n + 1 : ℕ) : ℝ))) ^ 4) →
          ∀ t ∈ Set.Icc 0 T₁,
            Tendsto (fun n => interpRec ((bankWord s T₁ (β n)).path 0 t)) atTop (𝓝 (Q t)) ∧
            Tendsto (fun n => interpRec ((bankWord s T₁ (β n)).path 1 t)) atTop (𝓝 (V t)) ∧
            Tendsto (fun n => interpRec ((bankWord s T₁ (β n)).path 2 t)) atTop (𝓝 (A t)) ∧
            ∀ n, n₀ ≤ n →
              (bankWord s T₁ (β n)).recNorm s t ≤ C * ε ∧
              (∀ κ : Upper,
                sn (s - 1) ⇑(cmp (interpRec ((bankWord s T₁ (β n)).path 0 t)) κ.1.1 κ.1.2 -
                  cmp (Q t) κ.1.1 κ.1.2) ≤ C * ε * ((n : ℝ) + 1)⁻¹ ∧
                sn (s - 2) ⇑(cmp (interpRec ((bankWord s T₁ (β n)).path 1 t)) κ.1.1 κ.1.2 -
                  cmp (V t) κ.1.1 κ.1.2) ≤ C * ε * ((n : ℝ) + 1)⁻¹ ∧
                sn (s - 3) ⇑(cmp (interpRec ((bankWord s T₁ (β n)).path 2 t)) κ.1.1 κ.1.2 -
                  cmp (A t) κ.1.1 κ.1.2) ≤ C * ε * ((n : ℝ) + 1)⁻¹) ∧
              UniformO3 s C ε n ((bankWord s T₁ (β n)).path 0 t)
                ((bankWord s T₁ (β n)).path 1 t) ((bankWord s T₁ (β n)).path 2 t) ∧
              (∀ (y : T3) (b' : Fin 4), HasDerivWithinAt (fun τ => gaugeOf (accJet
                ((bankWord s T₁ (β n)).path 0 τ) ((bankWord s T₁ (β n)).path 1 τ)
                ((bankWord s T₁ (β n)).path 2 τ) y) b')
                (dtGaugeOf (accJet ((bankWord s T₁ (β n)).path 0 t)
                  ((bankWord s T₁ (β n)).path 1 t) ((bankWord s T₁ (β n)).path 2 t) y) b')
                (Set.Icc 0 T₁) t) ∧
              ∀ (a b' c d : Fin 4), ∃ F : CT,
                (∀ y, F y = ((riemOf (accJet ((bankWord s T₁ (β n)).path 0 t)
                    ((bankWord s T₁ (β n)).path 1 t) ((bankWord s T₁ (β n)).path 2 t) y) a b' c d -
                  riemOf (pjetField (Q t) (V t) (A t) (Qd' t) (Vd' t) (Qdd' t) y) a b' c d :
                    ℝ) : ℂ)) ∧
                MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * ε * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨TE, hTE, hE⟩ := finite_words_einstein s hs cη c₀ hcη hc₀
  obtain ⟨TU, hTU, hU⟩ := finite_words_uniform s hs cη c₀ hcη hc₀
  obtain ⟨TC, hTC, hCv⟩ := finite_words_curvature s hs cη c₀ hcη hc₀
  refine ⟨min TE (min TU TC), lt_min hTE (lt_min hTU hTC), fun T₁ hT₁ hT₁T => ?_⟩
  obtain ⟨εE, hεE, KE, hKE, CE, hCE, CεE, hCεE, CBE, hCBE, CWE, hCWE, nE, hE'⟩ :=
    hE T₁ hT₁ (hT₁T.trans (min_le_left _ _))
  obtain ⟨εU, hεU, CU, hCU, nU, hU'⟩ :=
    hU T₁ hT₁ (hT₁T.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨εC, hεC, CC, hCC, nC, hC'⟩ :=
    hCv T₁ hT₁ (hT₁T.trans ((min_le_right _ _).trans (min_le_right _ _)))
  set Cr : ℝ := CE * Real.exp (KE * T₁) * (1 + T₁) * CεE + CBE + CWE
  have hCr : 0 ≤ Cr := by positivity
  refine ⟨min εE (min εU εC), lt_min hεE (lt_min hεU hεC), Cr + CU + CC, by positivity,
    max nE (max nU nC), fun Q₀ Kr Qd Kd Qdd ε hD hsz hεε => ?_⟩
  have hε0 : 0 ≤ ε := (add_nonneg (ccoordSum_nonneg _ _ _) (ccoordSum_nonneg _ _ _)).trans hsz
  obtain ⟨V₀E, hV₀E, QE, VE, AE, -, -, -, -, -, -, hfamE⟩ :=
    hE' Q₀ Kr Qd Kd Qdd ε hD hsz (hεε.trans (min_le_left _ _))
  obtain ⟨V₀U, hV₀U, hfamU⟩ :=
    hU' Q₀ Kr Qd Kd Qdd ε hD hsz (hεε.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨V₀, hV₀, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, hcj, hfamC⟩ :=
    hC' Q₀ Kr Qd Kd Qdd ε hD hsz (hεε.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have e1 : V₀E = V₀ := DFunLike.coe_injective (hV₀E.trans hV₀.symm)
  have e2 : V₀U = V₀ := DFunLike.coe_injective (hV₀U.trans hV₀.symm)
  subst e1 e2
  refine ⟨_, hV₀, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, hcj,
    fun b B hB hb β hprec hstart t ht => ?_⟩
  obtain ⟨d1, d2, d3, drate⟩ := hfamE b B hB hb β hprec hstart t ht
  obtain ⟨c1, c2, c3, hcn⟩ := hfamC b B hB hb β hprec hstart t ht
  -- the two theorems describe the same limit `g`: uniqueness of limits
  have hQ : QE t = Q t := tendsto_nhds_unique d1 c1
  have hV : VE t = V t := tendsto_nhds_unique d2 c2
  have hA : AE t = A t := tendsto_nhds_unique d3 c3
  refine ⟨c1, c2, c3, fun n hn => ?_⟩
  have hnE : nE ≤ n := (le_max_left _ _).trans hn
  have hnU : nU ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnC : nC ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  obtain ⟨hrec, hriem⟩ := hcn n hnC
  obtain ⟨hU3, hgd⟩ := hfamU b B hB hb β hprec hstart n hnU t ht
  have hw : 0 ≤ ε * ((n : ℝ) + 1)⁻¹ := by positivity
  have hCrC : Cr ≤ Cr + CU + CC := by linarith
  have hCUC : CU ≤ Cr + CU + CC := by linarith
  have hCCC : CC ≤ Cr + CU + CC := by linarith
  -- the Einstein rates with the time-uniform constant
  have hrate : ∀ x : ℝ, x ≤ ((CE * Real.exp (KE * t) * (1 + t) * CεE + CBE) * ε + CWE * ε) *
      ((n : ℝ) + 1)⁻¹ → x ≤ (Cr + CU + CC) * ε * ((n : ℝ) + 1)⁻¹ := by
    intro x hx
    refine hx.trans ?_
    have he : Real.exp (KE * t) ≤ Real.exp (KE * T₁) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hKE)
    have h1t : 1 + t ≤ 1 + T₁ := by linarith [ht.2]
    have k : CE * Real.exp (KE * t) * (1 + t) * CεE ≤ CE * Real.exp (KE * T₁) * (1 + T₁) * CεE := by
      gcongr; linarith [ht.1]
    calc ((CE * Real.exp (KE * t) * (1 + t) * CεE + CBE) * ε + CWE * ε) * ((n : ℝ) + 1)⁻¹ =
          (CE * Real.exp (KE * t) * (1 + t) * CεE + CBE + CWE) * (ε * ((n : ℝ) + 1)⁻¹) := by ring
      _ ≤ Cr * (ε * ((n : ℝ) + 1)⁻¹) := by gcongr; simp only [Cr]; linarith
      _ ≤ (Cr + CU + CC) * (ε * ((n : ℝ) + 1)⁻¹) := mul_le_mul_of_nonneg_right hCrC hw
      _ = _ := by ring
  refine ⟨hrec.trans (mul_le_mul_of_nonneg_right hCCC hε0), fun κ => ?_,
    finiteWords_uniformO3_mono hU3 hCUC hε0, hgd, fun a b' c d => ?_⟩
  · obtain ⟨r1, r2, r3⟩ := drate n hnE κ
    rw [hQ] at r1
    rw [hV] at r2
    rw [hA] at r3
    exact ⟨hrate _ r1, hrate _ r2, hrate _ r3⟩
  · obtain ⟨F, hF, hFm, hFs⟩ := hriem a b' c d
    refine ⟨F, hF, hFm, hFs.trans ?_⟩
    have : CC * ε * ((n : ℝ) + 1)⁻¹ ≤ (Cr + CU + CC) * ε * ((n : ℝ) + 1)⁻¹ := by gcongr
    exact this

end

end RenewalGeometry.OpenWriterFiniteWords
