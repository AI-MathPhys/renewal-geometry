/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterFiniteWordsEinstein
import RenewalGeometry.Gravity.OpenWriterRateLiftUniform

/-!
# The `(O3)` package along finite successor words (`thm:main-open-3plus1`, item (O4);
  emergent-spacetime manuscript)

* `uniformO3_of_close`: the `(O3)` package `UniformO3` (subsidiary field and its time derivative,
  Einstein residual of the reconstructed metric at rate `C h ε`, curvature bound `C ε`, interior-cone
  rate lift with cut margin, noncollapse of the interpolated metric) is stable under perturbations
  of the record triple `(q, v, f)` of size `O(ε h)` in `X^{s-2}_h × H^{s-3}_h` inside the common
  small ball (Lipschitz Moser estimates `pjet_moser_fin`, jet differences `accJet_diff`).
* `finiteWords_gauge_hasDerivWithinAt`: `∂ₜ c(g_h)` along any `C²` record path is
  `dtGaugeOf (accJet q v ∂ₜv)` (pointwise form of `gauge_hasDerivWithinAt_acc`).
* `finite_words_compare`: a bank word obeying the precision convention and starting within
  `c₀ ε h⁴` of an exact law history stays within `O(ε h)` of it in `X^{s-1}_h` (position, velocity)
  and in `H^{s-3}_h` (acceleration), on any horizon.
* `finite_words_uniform` (**(O3) inherited by the certified finite histories**, `thm:main-open-3plus1`
  (O4)): on every slab `[0, T₁]`, `T₁ ≤ T`, the bank words of the compatible finite initialization
  satisfy the whole `(O3)` package `UniformO3` (subsidiary field, its actual time derivative and
  Einstein residual of the reconstructed metric `≤ C h ε`, curvature `≤ C ε`, interior-cone rate
  lift with cut margin, noncollapse), uniformly in the cutoff and in the marks `B_n`.
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

theorem finiteWords_gaugeOf_acc {N : ℕ} [NeZero N] (q v f : Grid N → MetricRec) (y : T3)
    (b : Fin 4) : gaugeOf (accJet q v f y) b = gaugeOf (interpJet1 q v y) b := by
  rw [← gaugeOf_trunc (accJet q v f y)]
  rfl


/-- **`∂ₜ c(g_h)` along any `C²` record path** (pointwise form of `gauge_hasDerivWithinAt_acc`):
if at time `t` the record has velocity `v t` and the velocity has (componentwise) derivative `f`,
the velocities are symmetric on `[0, T]` and `g_h = η + 𝓘_h q(t)` is nondegenerate, then
`τ ↦ c_b(g_h)(τ, y)` has derivative `dtGaugeOf (accJet q(t) v(t) f)` within `[0, T]` (the
acceleration slot of the jet along the path is irrelevant for `c_b`). -/
theorem finiteWords_gauge_hasDerivWithinAt {N : ℕ} [NeZero N] {T : ℝ}
    {q v F : ℝ → Grid N → MetricRec} {t : ℝ} (ht : t ∈ Set.Icc 0 T) (f : Grid N → MetricRec)
    (hsym : ∀ τ ∈ Set.Icc 0 T, IsSymRec (v τ))
    (hq : ∀ x, HasDerivAt (fun τ => q τ x) (v t x) t)
    (hv : ∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2) (f x κ.1.1 κ.1.2) t) (y : T3)
    (hdet : (Matrix.of (minkowski + interpRec (q t) y)).det ≠ 0) (b : Fin 4) :
    HasDerivWithinAt (fun τ => gaugeOf (accJet (q τ) (v τ) (F τ) y) b)
      (dtGaugeOf (accJet (q t) (v t) f y) b) (Set.Icc 0 T) t := by
  set Z : ℝ → PJet := fun τ => (interpRec (q τ) y, interpRec (symRec (v τ)) y,
    interpRec (symRec f) y, fun i => interpD (q τ) i y,
    fun i => interpD (v t) i y, fun i j => interpDD (q t) i j y) with hZ
  have hsv : symRec (v t) = v t := symRec_of_isSymRec (hsym t ht)
  have hZt : Z t = accJet (q t) (v t) f y := by
    simp only [Z, hsv]; rfl
  have hq' : HasDerivAt (fun τ => interpRec (q τ) y) (interpRec (symRec (v t)) y) t := by
    rw [hsv]; exact hasDerivAt_interpRec hq y
  have hg : MHasDeriv (fun τ => (pjJet (Z τ)).g) ((pjJet (Z t)).dg 0) t :=
    C3Field.mhasDeriv_of_rec_add minkowski hq'
  have hP : Jet3.PathDeriv (fun τ => pjJet (Z τ)) 0 t := by
    refine ⟨hg, ?_, fun a => ?_, fun a b' i j => ?_⟩
    · exact mhasDeriv_inv (A := fun τ => Matrix.of (minkowski + interpRec (q τ) y)) hg hdet
    · refine Fin.cases ?_ (fun i => ?_) a
      · exact C3Field.mhasDeriv_of_rec (hasDerivAt_interpRec_symRec (u := v) (t := t) hv y)
      · exact C3Field.mhasDeriv_of_rec (hasDerivAt_interpD hq i y)
    · exact (hasDerivAt_const t ((pjJet (Z t)).ddg a b' i j)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun τ => rfl)
  have h1 := hP.gc b
  have h2 : (pjJet (Z t)).dgc 0 b = dtGaugeOf (accJet (q t) (v t) f y) b := by
    rw [← hZt]; rfl
  rw [h2] at h1
  refine h1.hasDerivWithinAt.congr (fun τ hτ => ?_) ?_
  · show gaugeOf (accJet (q τ) (v τ) (F τ) y) b = gaugeOf (Z τ) b
    rw [← gaugeOf_trunc (accJet (q τ) (v τ) (F τ) y), ← gaugeOf_trunc (Z τ)]
    simp only [Z, trunc, symRec_of_isSymRec (hsym τ hτ)]
    rfl
  · show gaugeOf (accJet (q t) (v t) (F t) y) b = gaugeOf (Z t) b
    rw [← gaugeOf_trunc (accJet (q t) (v t) (F t) y), ← gaugeOf_trunc (Z t)]
    simp only [Z, trunc, hsv]
    rfl

set_option maxHeartbeats 1600000 in
-- the four Moser transfers share all constants
/-- **Stability of the `(O3)` package.**  For `s ≥ 6` there are a radius `Δ > 0` and `K ≥ 0`,
independent of the cutoff, such that: if a record triple `(q, v, f)` (position, velocity,
acceleration) satisfies `UniformO3 s C ε n`, and a second symmetric triple `(q', v', f')` lies with
it in the ball `‖(q, v)‖_{X^s_h}, ‖(q', v')‖_{X^s_h} ≤ X_c ε` with accelerations
`‖f‖, ‖f'‖ ≤ K_f X_c ε` in `H^{s-3}_h` (`(S_3(K_f) + S_2 + 1) X_c ε ≤ Δ`) and differs from it by
`‖(q' - q, v' - v)‖_{X^{s-2}_h} + ‖f' - f‖_{s-3,h} ≤ D_c ε h`, then `(q', v', f')` satisfies
`UniformO3 s (C + K (D_c + S_3(K_f) X_c)) ε n`. -/
theorem uniformO3_of_close (s : ℕ) (hs : 6 ≤ s) :
    ∃ Δ > 0, ∃ K ≥ 0, ∀ (n : ℕ) (q v f q' v' f' : Grid (n + 1) → MetricRec)
      (C ε Kf Xc Dc : ℝ), 0 ≤ C → 0 ≤ ε → 0 ≤ Kf → 0 ≤ Xc → 0 ≤ Dc →
      IsSymRec q → IsSymRec v → IsSymRec q' → IsSymRec v' →
      Xnorm s q v ≤ Xc * ε → Xnorm s q' v' ≤ Xc * ε →
      (∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3) (cx (comp f κ.1.1 κ.1.2)) ≤
        Kf * (Xc * ε)) →
      (∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3) (cx (comp f' κ.1.1 κ.1.2)) ≤
        Kf * (Xc * ε)) →
      (sizeConst s Kf + sizeConst1 s + 1) * (Xc * ε) ≤ Δ →
      Xnorm (s - 2) (q' - q) (v' - v) + Fnorm (s - 3) (f' - f) ≤ Dc * ε * ((n : ℝ) + 1)⁻¹ →
      UniformO3 s C ε n q v f →
      UniformO3 s (C + K * (Dc + sizeConst s Kf * Xc)) ε n q' v' f' := by
  obtain ⟨δR, hδR, hRate⟩ := rateLift_of_Xnorm s (by omega)
  obtain ⟨δI, hδI, hInterp⟩ := rateLift_interp s (by omega)
  obtain ⟨δG, hδG, CG, hCG, hGm⟩ := pjet_moser_fin (s - 2) (by omega)
    (fun b : Fin 4 => fun z => gaugeOf z b) analyticAt_gaugeOf
  obtain ⟨δD, hδD, CD, hCD, hDm⟩ := pjet_moser_fin (s - 3) (by omega)
    (fun b : Fin 4 => fun z => dtGaugeOf z b) analyticAt_dtGaugeOf
  obtain ⟨δE, hδE, CE, hCE, hEm⟩ := pjet_moser_fin (s - 3) (by omega)
    (fun p : Fin 4 × Fin 4 => fun z => einOf z p.1 p.2) (fun p => analyticAt_einOf p.1 p.2)
  obtain ⟨δM, hδM, CR, hCR, hRm⟩ := riem_moser (s - 3) (by omega)
  set P : ℝ := diffConst s
  have hP : 0 ≤ P := diffConst_nonneg s
  set P' : ℝ := Real.sqrt (pc (s - 2)) + Real.sqrt (pc (s - 2 + 1))
  have hP' : 0 ≤ P' := by positivity
  set Δ : ℝ := min (min δR δI) (min (min δG δD) (min δE δM))
  have hΔ : 0 < Δ := by positivity
  set K : ℝ := (CG + CD + CE + 1) * (288 * (P + P')) + CR
  have hK : 0 ≤ K := by positivity
  refine ⟨Δ, hΔ, K, hK, fun n q v f q' v' f' C ε Kf Xc Dc hC hε hKf hXc hDc hq hv hq' hv' hX hX'
    hf hf' hΔX hD hU => ?_⟩
  obtain ⟨b1, b2, b3, -, -, -⟩ := hU
  have hΔR : Δ ≤ δR := (min_le_left _ _).trans (min_le_left _ _)
  have hΔI : Δ ≤ δI := (min_le_left _ _).trans (min_le_right _ _)
  have hΔG : Δ ≤ δG := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hΔD : Δ ≤ δD := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hΔE : Δ ≤ δE := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hΔM : Δ ≤ δM := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set X : ℝ := Xc * ε
  have hX0 : 0 ≤ X := by positivity
  set S3 : ℝ := sizeConst s Kf
  have hS3 : 0 ≤ S3 := by simp only [S3, sizeConst]; positivity
  set S2 : ℝ := sizeConst1 s
  have hS2 : 0 ≤ S2 := by simp only [S2, sizeConst1]; positivity
  have hS3X : S3 * X ≤ Δ := by nlinarith
  have hS2X : S2 * X ≤ Δ := by nlinarith
  have hXΔ : X ≤ Δ := by nlinarith
  -- sizes
  have hJ := accJet_size s (by omega) hq hv f hKf hX hf
  have hJ' := accJet_size s (by omega) hq' hv' f' hKf hX' hf'
  have hJ1 := accJet1_size s (by omega) hq hv hX
  have hJ1' := accJet1_size s (by omega) hq' hv' hX'
  -- differences
  set w : ℝ := ε * ((n : ℝ) + 1)⁻¹
  have hw : 0 ≤ w := by positivity
  set D : ℝ := Dc * ε * ((n : ℝ) + 1)⁻¹
  have hDw : D = Dc * w := by simp only [D, w]; ring
  obtain ⟨-, hdS⟩ := accJet_diff s (by omega) hq' hv' hq hv f' f hD
  obtain ⟨-, hdS1⟩ := accJet1_diff s (by omega) hq' hv' hq hv
    (le_trans (le_add_of_nonneg_right (Fnorm_nonneg _ _)) hD)
  have hfin : ∀ (Cm Pq X1 X2 : ℝ), 0 ≤ Cm → Cm ≤ CG + CD + CE + 1 → 0 ≤ Pq → Pq ≤ P + P' →
      X1 ≤ Cm * (288 * Pq * D) → X2 ≤ C * ε * ((n : ℝ) + 1)⁻¹ →
      X1 + X2 ≤ (C + K * (Dc + S3 * Xc)) * ε * ((n : ℝ) + 1)⁻¹ := by
    intro Cm Pq X1 X2 hCm hCm' hPq hPq' h1 h2
    have k1 : Cm * (288 * Pq * D) ≤ (CG + CD + CE + 1) * (288 * (P + P')) * (Dc * w) := by
      rw [hDw]
      have : Cm * (288 * Pq) ≤ (CG + CD + CE + 1) * (288 * (P + P')) :=
        mul_le_mul hCm' (by linarith) (by positivity) (by positivity)
      calc Cm * (288 * Pq * (Dc * w)) = Cm * (288 * Pq) * (Dc * w) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right this (by positivity)
    have k2 : (CG + CD + CE + 1) * (288 * (P + P')) * (Dc * w) ≤ K * (Dc * w) :=
      mul_le_mul_of_nonneg_right (by simp only [K]; linarith) (by positivity)
    have k3 : 0 ≤ K * (S3 * Xc) * w := by positivity
    have e : (C + K * (Dc + S3 * Xc)) * ε * ((n : ℝ) + 1)⁻¹ =
        C * ε * ((n : ℝ) + 1)⁻¹ + K * (Dc * w) + K * (S3 * Xc) * w := by simp only [w]; ring
    linarith
  refine ⟨fun b => ?_, fun b => ?_, fun μ ν => ?_, fun a b c d => ?_,
    hRate (n + 1) q' v' hq' (hX'.trans (hXΔ.trans hΔR)),
    hInterp (n + 1) q' v' f' hq' (hJ'.trans (hS3X.trans hΔI))⟩
  · -- gauge covector
    obtain ⟨F1, hF1, hF1m, hF1s⟩ := hGm b (interpJet1 q' v') (interpJet1 q v)
      (accJet1_memH _ _ _) (accJet1_memH _ _ _) (hJ1'.trans (hS2X.trans hΔG))
      (hJ1.trans (hS2X.trans hΔG))
    obtain ⟨F0, hF0, hF0m, hF0s⟩ := b1 b
    refine ⟨F1 + F0, fun y => ?_, memH_add hF1m hF0m,
      (lawLimit_sn_add_le F1 F0 hF0m).trans (hfin CG P' _ _ hCG (by linarith) hP' (by linarith)
        (hF1s.trans (mul_le_mul_of_nonneg_left hdS1 hCG)) hF0s)⟩
    rw [ContinuousMap.add_apply, hF1 y, hF0 y, finiteWords_gaugeOf_acc q v f y b,
      finiteWords_gaugeOf_acc q' v' f' y b]
    push_cast; ring
  · -- its time derivative
    obtain ⟨F1, hF1, hF1m, hF1s⟩ := hDm b (accJet q' v' f') (accJet q v f)
      (accJet_memH _ _ _ _) (accJet_memH _ _ _ _) (hJ'.trans (hS3X.trans hΔD))
      (hJ.trans (hS3X.trans hΔD))
    obtain ⟨F0, hF0, hF0m, hF0s⟩ := b2 b
    refine ⟨F1 + F0, fun y => ?_, memH_add hF1m hF0m,
      (lawLimit_sn_add_le F1 F0 hF0m).trans (hfin CD P _ _ hCD (by linarith) hP (by linarith)
        (hF1s.trans (mul_le_mul_of_nonneg_left hdS hCD)) hF0s)⟩
    rw [ContinuousMap.add_apply, hF1 y, hF0 y]
    push_cast; ring
  · -- the Einstein tensor
    obtain ⟨F1, hF1, hF1m, hF1s⟩ := hEm (μ, ν) (accJet q' v' f') (accJet q v f)
      (accJet_memH _ _ _ _) (accJet_memH _ _ _ _) (hJ'.trans (hS3X.trans hΔE))
      (hJ.trans (hS3X.trans hΔE))
    obtain ⟨F0, hF0, hF0m, hF0s⟩ := b3 μ ν
    refine ⟨F1 + F0, fun y => ?_, memH_add hF1m hF0m,
      (lawLimit_sn_add_le F1 F0 hF0m).trans (hfin CE P _ _ hCE (by linarith) hP (by linarith)
        (hF1s.trans (mul_le_mul_of_nonneg_left hdS hCE)) hF0s)⟩
    rw [ContinuousMap.add_apply, hF1 y, hF0 y]
    push_cast; ring
  · -- the curvature bound
    obtain ⟨F, hF, hFm, hFs⟩ := hRm (accJet q' v' f') (accJet_memH _ q' v' f')
      (hJ'.trans (hS3X.trans hΔM)) a b c d
    refine ⟨F, hF, hFm, hFs.trans ?_⟩
    have hCRK : CR ≤ K := by
      have : 0 ≤ (CG + CD + CE + 1) * (288 * (P + P')) := by positivity
      simp only [K]; linarith
    calc CR * ccoordSum (s - 3) bPJ (accJet q' v' f') ≤ CR * (S3 * X) :=
          mul_le_mul_of_nonneg_left hJ' hCR
      _ ≤ K * (S3 * X) := mul_le_mul_of_nonneg_right hCRK (by positivity)
      _ = K * (S3 * Xc) * ε := by simp only [X]; ring
      _ ≤ (C + K * (Dc + S3 * Xc)) * ε := by
          apply mul_le_mul_of_nonneg_right _ hε
          have : 0 ≤ K * Dc := by positivity
          nlinarith


set_option maxHeartbeats 4000000 in
-- the comparison of a word with an exact history in one statement
/-- **Comparison of a bank word with the exact law history** (the step of
`finite_words_einstein`, for a general exact history).  Fix `s ≥ 6`, a horizon `T > 0` and
constants `c, c₀, C_B ≥ 0`.  There are `ε_c > 0`, `N₀` and `D_c, X_c ≥ 0` such that for `N ≥ N₀`,
every mark of the closed ball, every exact law history `(q_B, v_B)` on `[0, T_B] ⊇ [0, T]` with
`‖(q_B, v_B)‖_{X^s_h} ≤ C_B ε` on `[0, T]`, and every bank word obeying the precision convention
`η = c ε h^{s+10}` and starting within `c₀ ε h⁴` of `(q_B, v_B)(0)` in `X^s_h` (`ε ≤ ε_c`): on
`[0, T]`, `‖(Q, Q')‖_{X^s_h} ≤ X_c ε`, `‖(Q - q_B, Q' - v_B)‖_{X^{s-1}_h} ≤ D_c ε h` and
`‖Q'' - V_B(q_B, v_B)‖_{s-3,h} ≤ D_c ε h` componentwise. -/
theorem finite_words_compare (s : ℕ) (hs : 6 ≤ s) (T : ℝ) (hT : 0 < T) (cη c₀ CB : ℝ)
    (hcη : 0 ≤ cη) (hc₀ : 0 ≤ c₀) (hCB : 0 ≤ CB) :
    ∃ εc > 0, ∃ N₀ : ℕ, ∃ Dc ≥ 0, ∃ Xc ≥ 0, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ (B : Upper → Upper → ℝ), IsMark (1 / 48) B →
      ∀ (β : ℕ → Fin 4 → Upper → GridH N (s + 1)) (ε : ℝ), 0 ≤ ε → ε ≤ εc →
      ∀ (qB vB : ℝ → Grid N → MetricRec) (TB : ℝ), T ≤ TB → IsAccSolution (lawAccel B) TB qB vB →
      (∀ t ∈ Set.Icc 0 T, Xnorm s (qB t) (vB t) ≤ CB * ε) →
      BankPrecise s B (stepOf N T) (cη * ε * (1 / (N : ℝ)) ^ (s + 10)) β (numCells N T) →
      Xnorm s (recOf (β 0 0) - qB 0) (recOf (β 0 1) - vB 0) ≤ c₀ * ε * (1 / (N : ℝ)) ^ 4 →
      ∀ τ ∈ Set.Icc 0 T, (bankWord s T β).recNorm s τ ≤ Xc * ε ∧
        Xnorm (s - 1) ((bankWord s T β).path 0 τ - qB τ) ((bankWord s T β).path 1 τ - vB τ) ≤
          Dc * ε * (1 / (N : ℝ)) ∧
        ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3) (cx (comp ((bankWord s T β).path 2 τ -
          lawAccel B (qB τ) (vB τ)) κ.1.1 κ.1.2)) ≤ Dc * ε * (1 / (N : ℝ)) := by
  obtain ⟨ε₀, hε₀, N₀, CF, hCF, hFW⟩ := finite_words_bounds s (by omega) T hT cη hcη
  obtain ⟨δD, hδD, KD, hKD, hDiff⟩ := law_difference s (s - 1) (by omega) (by omega)
  obtain ⟨δA, hδA, KA, hKA, hAcc⟩ := lawAccel_diff_bound s (s - 2) (by omega) (by omega)
  set S20 : ℝ := Real.sqrt (2 * Fintype.card Upper)
  have hS20 : 0 ≤ S20 := Real.sqrt_nonneg _
  set cw : ℝ := S20 * (CB + c₀) + 1
  have hcw : 1 ≤ cw := by have : 0 ≤ S20 * (CB + c₀) := by positivity
                          simp only [cw]; linarith
  set δ : ℝ := min δD δA
  have hδ : 0 < δ := lt_min hδD hδA
  set εc : ℝ := min (ε₀ / cw) (δ / (CF * cw + CB + 1))
  have hεc : 0 < εc := by
    have : 0 < cw := by linarith
    positivity
  set D1 : ℝ := 3 * Real.exp (KD * T) * (3 * c₀ + KD * (T * (CF * cw)))
  have hD1 : 0 ≤ D1 := by positivity
  set Dc : ℝ := D1 + (CF * cw + KA * D1)
  refine ⟨εc, hεc, N₀, Dc, by positivity, CF * cw, by positivity,
    fun N _ hN B hmark β ε hε0 hεε qB vB TB hTTB hsolA hbnd hprec hstartn τ hτ => ?_⟩
  have hεcw : cw * ε ≤ ε₀ := by
    have h1 : ε ≤ ε₀ / cw := hεε.trans (min_le_left _ _)
    rw [le_div_iff₀ (by linarith)] at h1
    linarith
  have hεδ : (CF * cw + CB) * ε ≤ δ := by
    have h1 : ε ≤ δ / (CF * cw + CB + 1) := hεε.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    have : (CF * cw + CB) * ε ≤ ε * (CF * cw + CB + 1) := by nlinarith
    linarith
  have hCFδ : CF * (cw * ε) ≤ δ := by
    have : 0 ≤ CB * ε := by positivity
    nlinarith
  have hCBδ : CB * ε ≤ δ := by
    have : 0 ≤ CF * cw * ε := by positivity
    nlinarith
  set W := bankWord s T β
  set h : ℝ := 1 / (N : ℝ) with hhdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hh0 : 0 < h := by rw [hhdef]; positivity
  have hh1 : h ≤ 1 := by rw [hhdef, div_le_one (by linarith)]; exact hN1
  -- the initial record
  have hτ0 : (0 : ℝ) ∈ Set.Icc 0 TB := ⟨le_rfl, hT.le.trans hTTB⟩
  have hsq0 : IsSymRec (qB 0) := (hsolA 0 hτ0).1
  have hsv0 : IsSymRec (vB 0) := (hsolA 0 hτ0).2.1
  have hW0 : W.path 0 0 = recOf (β 0 0) := by
    have := bankWord_path_node s hT β (j := 0) (Nat.zero_le _) 0
    simpa using this
  have hW1 : W.path 1 0 = recOf (β 0 1) := by
    have := bankWord_path_node s hT β (j := 0) (Nat.zero_le _) 1
    simpa using this
  have hdsym0 : IsSymRec (recOf (β 0 0) - qB 0) := isSymRec_sub (isSymRec_recOf _) hsq0
  have hdsym1 : IsSymRec (recOf (β 0 1) - vB 0) := isSymRec_sub (isSymRec_recOf _) hsv0
  have hsamp : Xnorm s (qB 0) (vB 0) ≤ CB * ε := hbnd 0 ⟨le_rfl, hT.le⟩
  have hh4 : h ^ 4 ≤ 1 := pow_le_one₀ hh0.le hh1
  have hstart1 : Xnorm s (recOf (β 0 0)) (recOf (β 0 1)) ≤ cw * ε := by
    have e0 : recOf (β 0 0) = qB 0 + (recOf (β 0 0) - qB 0) := (add_sub_cancel _ _).symm
    have e1 : recOf (β 0 1) = vB 0 + (recOf (β 0 1) - vB 0) := (add_sub_cancel _ _).symm
    rw [e0, e1]
    refine (finiteWords_Xnorm_add_le s hsq0 hdsym0 hsv0 hdsym1).trans ?_
    have hd : c₀ * ε * h ^ 4 ≤ c₀ * ε := by
      have : 0 ≤ c₀ * ε := by positivity
      nlinarith
    calc S20 * (Xnorm s (qB 0) (vB 0) + Xnorm s (recOf (β 0 0) - qB 0) (recOf (β 0 1) - vB 0))
        ≤ S20 * (CB * ε + c₀ * ε) := by
          gcongr
          exact hstartn.trans hd
      _ = S20 * (CB + c₀) * ε := by ring
      _ ≤ cw * ε := by gcongr; simp only [cw]; linarith
  have hprecn : BankPrecise s B (stepOf N T) (cη * (cw * ε) * (1 / (N : ℝ)) ^ (s + 10)) β
      (numCells N T) := by
    refine hprec.mono ?_
    have : ε ≤ cw * ε := by nlinarith
    gcongr
  obtain ⟨-, hglob, -, -⟩ := hFW N hN B hmark β (cw * ε) (by positivity) hεcw hstart1 hprecn
  -- the forced pair
  have hsW0 : ∀ τ', IsSymRec (W.path 0 τ') :=
    LawWord.isSymRec_path W (fun j i => isSymRec_recOf (bankLetter (stepOf N T) β j i)) 0
  have hsW1 : ∀ τ', IsSymRec (W.path 1 τ') :=
    LawWord.isSymRec_path W (fun j i => isSymRec_recOf (bankLetter (stepOf N T) β j i)) 1
  have hWmono := bankWord_node_strictMono s hT β
  have hWjm := bankWord_jetsMatch s hT β
  have hpair : IsLawForcedPair B s δD T (W.path 0) qB (W.path 1) vB (W.residual B)
      (fun _ => 0) := by
    intro τ' hτ'
    have hτB : τ' ∈ Set.Icc 0 TB := ⟨hτ'.1, hτ'.2.trans hTTB⟩
    obtain ⟨s1, s2, d1, d2⟩ := hsolA τ' hτB
    refine ⟨hsW0 τ', hsW1 τ', s1, s2, fun x => ?_, d1, fun x κ => ?_, fun x κ => ?_, ?_, ?_⟩
    · exact hasDerivAt_pi.1 (LawWord.hasDerivAt_path hWmono hWjm (k := 0) (by norm_num) τ') x
    · have h := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1
        (LawWord.hasDerivAt_path hWmono hWjm (k := 1) (by norm_num) τ') x) κ.1.1) κ.1.2
      refine h.congr_deriv ?_
      simp only [LawWord.residual, Pi.sub_apply]
      ring
    · refine (d2 x κ).congr_deriv ?_
      simp
    · exact (hglob τ' hτ').1.trans (hCFδ.trans (min_le_left _ _))
    · exact (hbnd τ' hτ').trans (hCBδ.trans (min_le_left _ _))
  have hfc : ContinuousOn (W.residual B) (Set.Icc 0 T) := fun τ' hτ' =>
    (hglob τ' hτ').2.2.1.continuousAt.continuousWithinAt
  have hd := hDiff N B T (W.path 0) qB (W.path 1) vB (W.residual B)
    (fun _ => 0) hmark hpair hfc continuousOn_const τ hτ
  -- the starting difference
  have hX0 : Xnorm (s - 1) (W.path 0 0 - qB 0) (W.path 1 0 - vB 0) ≤ c₀ * ε * h := by
    rw [hW0, hW1]
    refine (lawDiff_Xnorm_mono (by omega) _ _).trans (hstartn.trans ?_)
    have : h ^ 4 ≤ h := by
      calc h ^ 4 ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by norm_num)
        _ = h := pow_one h
    have : 0 ≤ c₀ * ε := by positivity
    nlinarith
  -- the integrated defect
  have hI : (∫ σ in (0)..τ, Fnorm (s - 1) (W.residual B σ - (fun _ => 0) σ)) ≤
      T * (CF * (cw * ε) * h) := by
    have hn' := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := τ)
      (f := fun σ => Fnorm (s - 1) (W.residual B σ - (fun _ => 0) σ))
      (C := CF * (cw * ε) * h) fun x hx => by
        rw [uIoc_of_le hτ.1] at hx
        have hxT : x ∈ Set.Icc 0 T := ⟨hx.1.le, hx.2.trans hτ.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (Fnorm_nonneg _ _), sub_zero]
        refine (lawDiff_Fnorm_mono (by omega) _).trans ((hglob x hxT).2.1.trans ?_)
        have : h ^ 5 ≤ h := by
          calc h ^ 5 ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by norm_num)
            _ = h := pow_one h
        have : 0 ≤ CF * (cw * ε) := by positivity
        nlinarith
    rw [sub_zero, abs_of_nonneg hτ.1] at hn'
    have h1 := (Real.le_norm_self _).trans hn'
    have h2 : CF * (cw * ε) * h * τ ≤ T * (CF * (cw * ε) * h) := by
      have : 0 ≤ CF * (cw * ε) * h := by positivity
      nlinarith [hτ.2]
    exact h1.trans h2
  have hdiff : Xnorm (s - 1) (W.path 0 τ - qB τ) (W.path 1 τ - vB τ) ≤ D1 * ε * h := by
    refine hd.trans ?_
    have hexp : Real.exp (KD * τ) ≤ Real.exp (KD * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 hKD)
    have hin : 0 ≤ ∫ σ in (0)..τ, Fnorm (s - 1) (W.residual B σ - (fun _ => 0) σ) :=
      intervalIntegral.integral_nonneg hτ.1 fun _ _ => Fnorm_nonneg _ _
    calc 3 * Real.exp (KD * τ) * (3 * Xnorm (s - 1) (W.path 0 0 - qB 0) (W.path 1 0 - vB 0) +
          KD * ∫ σ in (0)..τ, Fnorm (s - 1) (W.residual B σ - (fun _ => 0) σ)) ≤
          3 * Real.exp (KD * T) * (3 * (c₀ * ε * h) + KD * (T * (CF * (cw * ε) * h))) := by
          have hX0n := Xnorm_nonneg (s - 1) (W.path 0 0 - qB 0) (W.path 1 0 - vB 0)
          refine mul_le_mul (mul_le_mul_of_nonneg_left hexp (by norm_num))
            (add_le_add (by linarith [hX0]) (mul_le_mul_of_nonneg_left hI hKD))
            (add_nonneg (by positivity) (mul_nonneg hKD hin)) (by positivity)
      _ = D1 * ε * h := by simp only [D1]; ring
  have hD1Dc : D1 * ε * h ≤ Dc * ε * h := by
    have : D1 ≤ Dc := by have : 0 ≤ CF * cw + KA * D1 := by positivity
                         simp only [Dc]; linarith
    gcongr
  refine ⟨(hglob τ hτ).1.trans (le_of_eq (by ring)), hdiff.trans hD1Dc, fun κ => ?_⟩
  -- the acceleration
  have e : comp (W.path 2 τ - lawAccel B (qB τ) (vB τ)) κ.1.1 κ.1.2 =
      comp (W.residual B τ) κ.1.1 κ.1.2 +
        comp (lawAccel B (W.path 0 τ) (W.path 1 τ) - lawAccel B (qB τ) (vB τ)) κ.1.1 κ.1.2 := by
    funext x
    simp only [comp, LawWord.residual, Pi.sub_apply, Pi.add_apply]
    ring
  rw [e, cx_add]
  refine (PeriodicGridSobolev.Moser.sobNorm_add_le _ _ _).trans ?_
  have a1 : PeriodicGridSobolev.sobNorm (s - 3) (cx (comp (W.residual B τ) κ.1.1 κ.1.2)) ≤
      CF * cw * ε * h := by
    refine (sobNorm_le_Fnorm _ _ κ).trans ((lawDiff_Fnorm_mono (by omega) _).trans
      ((hglob τ hτ).2.1.trans ?_))
    have : h ^ 5 ≤ h := by
      calc h ^ 5 ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by norm_num)
        _ = h := pow_one h
    have : 0 ≤ CF * (cw * ε) := by positivity
    nlinarith
  have hWs : Xnorm s (W.path 0 τ) (W.path 1 τ) ≤ δA :=
    (hglob τ hτ).1.trans (hCFδ.trans (min_le_right _ _))
  have hBs : Xnorm s (qB τ) (vB τ) ≤ δA := (hbnd τ hτ).trans (hCBδ.trans (min_le_right _ _))
  have hτB : τ ∈ Set.Icc 0 TB := ⟨hτ.1, hτ.2.trans hTTB⟩
  have a2 := hAcc N B (W.path 0 τ) (qB τ) (W.path 1 τ) (vB τ) hmark (hsW0 τ)
    (hsolA τ hτB).1 (hsW1 τ) (hsolA τ hτB).2.1 hWs hBs κ
  rw [show s - 2 - 1 = s - 3 by omega] at a2
  have a3 : Xnorm (s - 2) (W.path 0 τ - qB τ) (W.path 1 τ - vB τ) ≤ D1 * ε * h :=
    (lawDiff_Xnorm_mono (by omega) _ _).trans hdiff
  calc _ ≤ CF * cw * ε * h + KA * (D1 * ε * h) := add_le_add a1 (a2.trans (by gcongr))
    _ = (CF * cw + KA * D1) * ε * h := by ring
    _ ≤ Dc * ε * h := by
        have : CF * cw + KA * D1 ≤ Dc := by simp only [Dc]; linarith
        gcongr


theorem finiteWords_Fnorm_le_of_sobNorm_le {N : ℕ} [NeZero N] {r : ℕ} (f : Grid N → MetricRec)
    {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ κ : Upper, PeriodicGridSobolev.sobNorm r (cx (comp f κ.1.1 κ.1.2)) ≤ M) :
    Fnorm r f ≤ Real.sqrt (Fintype.card Upper) * M := by
  rw [Fnorm, ← Real.sqrt_sq hM, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ κ : Upper, PeriodicGridSobolev.sobSq r (cx (comp f κ.1.1 κ.1.2)) ≤ ∑ _κ : Upper, M ^ 2 := by
        refine Finset.sum_le_sum fun κ _ => ?_
        rw [← PeriodicGridSobolev.sobNorm_sq]
        exact pow_le_pow_left₀ (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _) (h κ) 2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

set_option maxHeartbeats 4000000 in
-- the identification of the exact histories and the transfer in one statement
/-- **The `(O3)` package along the finite successor words** (inheritance clause of
`thm:main-open-3plus1` (O4)).  Fix `s ≥ 6` and `c, c₀ ≥ 0`.  There is a slab `T > 0` such that for
every horizon `T₁ ∈ (0, T]` there are `εs > 0`, `C ≥ 0` and `n₀`, independent of the cutoff, with:
for every `(γ, K) ∈ D_s(ε)`, `ε ≤ εs`, with compatible preparation `V₀`, every sequence of marks
`B_n` of the closed ball and every sequence of bank words on `[0, T₁]` obeying the precision
convention `η = c ε h^{s+10}` and starting within `c₀ ε h⁴` of the samples of `(Q₀, V₀)` in
`X^s_h`, the word records `(Q_h, Q_h', Q_h'')` satisfy the full `(O3)` package `UniformO3` at every
`t ∈ [0, T₁]` for `n ≥ n₀`: subsidiary field, its time derivative and Einstein residual of the
reconstructed metric `≤ C h ε`, curvature `≤ C ε`, interior-cone rate lift with cut margin and
noncollapse of the interpolated metric. -/
theorem finite_words_uniform (s : ℕ) (hs : 6 ≤ s) (cη c₀ : ℝ) (hcη : 0 ≤ cη) (hc₀ : 0 ≤ c₀) :
    ∃ T > 0, ∀ T₁, 0 < T₁ → T₁ ≤ T → ∃ εs > 0, ∃ C ≥ 0, ∃ n₀ : ℕ,
    ∀ (Q₀ Kr : C(T3, MetricRec)) (Qd Kd : Fin 3 → C(T3, MetricRec))
      (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      DsData s Q₀ Kr Qd Kd Qdd → dataSize s Q₀ Kr ≤ ε → ε ≤ εs →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
        ∀ (b : ℕ → ℝ) (B : ℕ → Upper → Upper → ℝ), (∀ n, IsMark (b n) (B n)) →
          (∀ n, b n ≤ 1 / 48) →
          ∀ β : ∀ n : ℕ, ℕ → Fin 4 → Upper → GridH (n + 1) (s + 1),
          (∀ n, BankPrecise s (B n) (stepOf (n + 1) T₁)
            (cη * ε * (1 / (((n + 1 : ℕ) : ℝ))) ^ (s + 10)) (β n) (numCells (n + 1) T₁)) →
          (∀ n, Xnorm s (recOf (β n 0 0) - sampleRec (n + 1) ⇑Q₀)
            (recOf (β n 0 1) - sampleRec (n + 1) ⇑V₀) ≤ c₀ * ε * (1 / (((n + 1 : ℕ) : ℝ))) ^ 4) →
          ∀ n, n₀ ≤ n → ∀ t ∈ Set.Icc 0 T₁,
            UniformO3 s C ε n ((bankWord s T₁ (β n)).path 0 t) ((bankWord s T₁ (β n)).path 1 t)
              ((bankWord s T₁ (β n)).path 2 t) ∧
            ∀ (y : T3) (b : Fin 4), HasDerivWithinAt (fun τ => gaugeOf (accJet
              ((bankWord s T₁ (β n)).path 0 τ) ((bankWord s T₁ (β n)).path 1 τ)
              ((bankWord s T₁ (β n)).path 2 τ) y) b)
              (dtGaugeOf (accJet ((bankWord s T₁ (β n)).path 0 t) ((bankWord s T₁ (β n)).path 1 t)
                ((bankWord s T₁ (β n)).path 2 t) y) b) (Set.Icc 0 T₁) t := by
  obtain ⟨εU, hεU, TU, hTU, TBU, hTBU, CU, hCU, hU⟩ := supp_law_einstein_uniform s hs
  obtain ⟨εL, hεL, TL, hTL, TBL, hTBL, K0, _, C0, _, Cε0, _, CB, hCB, hLE⟩ := supp_law_einstein s hs
  obtain ⟨Δ, hΔ, KU, hKU, hclose⟩ := uniformO3_of_close s hs
  obtain ⟨δL, hδL, KL, hKL, hlacc⟩ := lawAccel_bound s (by omega)
  obtain ⟨r₁, hr₁, hinv⟩ := exists_inv_chart
  obtain ⟨δP, hδP, hPS⟩ := accJet_pointwise_small s (by omega) hr₁
  refine ⟨min TU TL, lt_min hTU hTL, fun T₁ hT₁ hT₁T => ?_⟩
  have hT₁U : T₁ ≤ TU := hT₁T.trans (min_le_left _ _)
  have hT₁L : T₁ ≤ TL := hT₁T.trans (min_le_right _ _)
  obtain ⟨εc, hεc, N₀, Dc, hDc, Xc, hXc, hcmp⟩ :=
    finite_words_compare s hs T₁ hT₁ cη c₀ CB hcη hc₀ hCB
  set S10 : ℝ := Real.sqrt (Fintype.card Upper)
  have hS10 : 0 ≤ S10 := Real.sqrt_nonneg _
  set Xc' : ℝ := Xc + CB + 1
  have hXc' : 1 ≤ Xc' := by simp only [Xc']; linarith
  set Kf : ℝ := KL + Dc
  have hKf : 0 ≤ Kf := by positivity
  set Dc' : ℝ := Dc + S10 * Dc
  have hDc' : 0 ≤ Dc' := by positivity
  set Sz : ℝ := (sizeConst s Kf + sizeConst1 s + 1) * Xc'
  have hSz : 0 < Sz := by
    have h1 : 0 ≤ sizeConst s Kf := by simp only [sizeConst]; positivity
    have h2 : 0 ≤ sizeConst1 s := by simp only [sizeConst1]; positivity
    simp only [Sz]; nlinarith
  set εs : ℝ := min (min (min εU εL) (δP / Sz)) (min εc (min (Δ / Sz) (δL / (CB + 1))))
  have hεs : 0 < εs := by positivity
  refine ⟨εs, hεs, CU + KU * (Dc' + sizeConst s Kf * Xc'), by
    have : 0 ≤ sizeConst s Kf := by simp only [sizeConst]; positivity
    positivity, N₀, fun Q₀ Kr Qd Kd Qdd ε hD hsz hεε => ?_⟩
  have hε0 : 0 ≤ ε := (add_nonneg (ccoordSum_nonneg _ _ _) (ccoordSum_nonneg _ _ _)).trans hsz
  have hεU : ε ≤ εU := hεε.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hεL : ε ≤ εL := hεε.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hεP : Sz * ε ≤ δP := by
    have h1 : ε ≤ δP / Sz := hεε.trans ((min_le_left _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ hSz] at h1; linarith
  have hεc' : ε ≤ εc := hεε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεΔ : Sz * ε ≤ Δ := by
    have h1 : ε ≤ Δ / Sz := hεε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
    rw [le_div_iff₀ hSz] at h1; linarith
  have hεδ : CB * ε ≤ δL := by
    have h1 : ε ≤ δL / (CB + 1) := hεε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
    rw [le_div_iff₀ (by positivity)] at h1; nlinarith
  obtain ⟨V₀, hV₀, q, v, -, -, -, hfamU⟩ := hU Q₀ Kr Qd Kd Qdd ε hD hsz hεU
  obtain ⟨V₀', hV₀', q', v', -, Q, V, A, Qd', Vd', Qdd', -, -, -, hfamL⟩ :=
    hLE Q₀ Kr Qd Kd Qdd ε hD hsz hεL
  have hVV : V₀' = V₀ := DFunLike.coe_injective (hV₀'.trans hV₀.symm)
  subst hVV
  refine ⟨V₀', hV₀', fun b B hB hb β hprec hstart n hn t ht => ?_⟩
  obtain ⟨qB, vB, hsolB, huB, hUB⟩ := hfamU b B hB hb
  obtain ⟨qL, vL, hsolL, huL, hbndL, -, -⟩ := hfamL b B hB hb
  have hmark : IsMark (1 / 48) (B n) := (hB n).mono (hb n)
  -- identification of the two exact law histories on `[0, T₁]`
  have hid : ∀ τ ∈ Set.Icc 0 T₁, qB n τ = qL n τ ∧ vB n τ = vL n τ := by
    intro τ hτ
    rcases le_total TBL TBU with h | h
    · exact huL n (qB n) (vB n) (hsolB n).2.1 (hsolB n).2.2 (restrict_acc (hsolB n).1 h) τ
        ⟨hτ.1, (hτ.2.trans hT₁L).trans hTBL⟩
    · have := huB n (qL n) (vL n) (hsolL n).2.1 (hsolL n).2.2 (restrict_acc (hsolL n).1 h) τ
        ⟨hτ.1, (hτ.2.trans hT₁U).trans hTBU⟩
      exact ⟨this.1.symm, this.2.symm⟩
  have hbnd : ∀ τ ∈ Set.Icc 0 T₁, Xnorm s (qB n τ) (vB n τ) ≤ CB * ε := fun τ hτ => by
    rw [(hid τ hτ).1, (hid τ hτ).2]
    exact (hbndL n τ ⟨hτ.1, hτ.2.trans hT₁L⟩).1
  have hstart' : Xnorm s (recOf (β n 0 0) - qB n 0) (recOf (β n 0 1) - vB n 0) ≤
      c₀ * ε * (1 / (((n + 1 : ℕ) : ℝ))) ^ 4 := by
    rw [(hsolB n).2.1, (hsolB n).2.2]; exact hstart n
  obtain ⟨c1, c2, c3⟩ := hcmp (n + 1) (by omega) (B n) hmark (β n) ε hε0 hεc' (qB n) (vB n) TBU
    (hT₁U.trans hTBU) (hsolB n).1 hbnd (hprec n) hstart' t ht
  have hU0 := (hUB n t ⟨ht.1, ht.2.trans hT₁U⟩).1
  set h : ℝ := 1 / (((n + 1 : ℕ) : ℝ)) with hhdef
  have hh : h = ((n : ℝ) + 1)⁻¹ := by rw [hhdef, Nat.cast_succ, one_div]
  have hh0 : 0 < h := by rw [hh]; positivity
  have hh1 : h ≤ 1 := by
    rw [hh]; exact inv_le_one_of_one_le₀ (by have := (n.cast_nonneg : (0 : ℝ) ≤ n); linarith)
  have htB : t ∈ Set.Icc 0 TBU := ⟨ht.1, (ht.2.trans hT₁U).trans hTBU⟩
  obtain ⟨sq, sv, -, -⟩ := (hsolB n).1 t htB
  set W := bankWord s T₁ (β n)
  have swq : IsSymRec (W.path 0 t) :=
    LawWord.isSymRec_path W (fun j i => isSymRec_recOf (bankLetter (stepOf (n + 1) T₁) (β n) j i)) 0 t
  have swv : IsSymRec (W.path 1 t) :=
    LawWord.isSymRec_path W (fun j i => isSymRec_recOf (bankLetter (stepOf (n + 1) T₁) (β n) j i)) 1 t
  have hCBX : CB * ε ≤ Xc' * ε := mul_le_mul_of_nonneg_right (by simp only [Xc']; linarith) hε0
  have hXq : Xnorm s (qB n t) (vB n t) ≤ Xc' * ε := (hbnd t ht).trans hCBX
  have hXw : Xnorm s (W.path 0 t) (W.path 1 t) ≤ Xc' * ε :=
    c1.trans (mul_le_mul_of_nonneg_right (by simp only [Xc']; linarith) hε0)
  have hfB : ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3)
      (cx (comp (lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2)) ≤ KL * (CB * ε) := fun κ =>
    (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
      ((hlacc (n + 1) (B n) (qB n t) (vB n t) hmark sq sv ((hbnd t ht).trans hεδ) κ).trans
        (mul_le_mul_of_nonneg_left (hbnd t ht) hKL))
  have hf : ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3)
      (cx (comp (lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2)) ≤ Kf * (Xc' * ε) := fun κ => by
    refine (hfB κ).trans ?_
    have : KL * (CB * ε) ≤ KL * (Xc' * ε) := mul_le_mul_of_nonneg_left hCBX hKL
    have : KL * (Xc' * ε) ≤ Kf * (Xc' * ε) :=
      mul_le_mul_of_nonneg_right (by simp only [Kf]; linarith) (by positivity)
    linarith
  have hf' : ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3) (cx (comp (W.path 2 t) κ.1.1 κ.1.2)) ≤
      Kf * (Xc' * ε) := fun κ => by
    have e : comp (W.path 2 t) κ.1.1 κ.1.2 =
        comp (W.path 2 t - lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2 +
          comp (lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2 := by
      funext x; simp only [comp, Pi.sub_apply, Pi.add_apply]; ring
    rw [e, cx_add]
    refine (PeriodicGridSobolev.Moser.sobNorm_add_le _ _ _).trans ?_
    have a1 := c3 κ
    have a2 := hfB κ
    have k1 : Dc * ε * h ≤ Dc * (Xc' * ε) := by
      have : ε * h ≤ Xc' * ε := by nlinarith
      calc Dc * ε * h = Dc * (ε * h) := by ring
        _ ≤ Dc * (Xc' * ε) := mul_le_mul_of_nonneg_left this hDc
    have k2 : KL * (CB * ε) ≤ KL * (Xc' * ε) := mul_le_mul_of_nonneg_left hCBX hKL
    have e2 : Kf * (Xc' * ε) = KL * (Xc' * ε) + Dc * (Xc' * ε) := by simp only [Kf]; ring
    linarith
  have hdiff : Xnorm (s - 2) (W.path 0 t - qB n t) (W.path 1 t - vB n t) +
      Fnorm (s - 3) (W.path 2 t - lawAccel (B n) (qB n t) (vB n t)) ≤ Dc' * ε * ((n : ℝ) + 1)⁻¹ := by
    have a1 := (lawDiff_Xnorm_mono (r := s - 2) (r' := s - 1) (by omega) _ _).trans c2
    have a2 := finiteWords_Fnorm_le_of_sobNorm_le _ (by positivity) c3
    rw [← hh]
    have e : Dc' * ε * h = Dc * ε * h + S10 * (Dc * ε * h) := by simp only [Dc']; ring
    linarith
  have hsz' : (sizeConst s Kf + sizeConst1 s + 1) * (Xc' * ε) ≤ Δ := by
    have e : (sizeConst s Kf + sizeConst1 s + 1) * (Xc' * ε) = Sz * ε := by simp only [Sz]; ring
    rw [e]; exact hεΔ
  refine ⟨hclose n (qB n t) (vB n t) (lawAccel (B n) (qB n t) (vB n t)) (W.path 0 t) (W.path 1 t)
    (W.path 2 t) CU ε Kf Xc' Dc' hCU hε0 hKf (by linarith) hDc' sq sv swq swv hXq hXw hf hf' hsz'
    hdiff hU0, fun y b => ?_⟩
  -- the actual time derivative of the subsidiary field along the word
  have hJw := accJet_size s (by omega) swq swv (W.path 2 t) hKf hXw hf'
  have hS3Sz : sizeConst s Kf * (Xc' * ε) ≤ Sz * ε := by
    have h2 : 0 ≤ sizeConst1 s := by simp only [sizeConst1]; positivity
    have : sizeConst s Kf * Xc' ≤ Sz := by simp only [Sz]; nlinarith
    nlinarith
  have hsm := hPS (n + 1) _ _ _ (hJw.trans (hS3Sz.trans hεP)) y
  have hdet : (Matrix.of (minkowski + interpRec (W.path 0 t) y)).det ≠ 0 :=
    (hinv _ (by rw [add_sub_cancel_left]; exact hsm)).1
  have hWmono := bankWord_node_strictMono s hT₁ (β n)
  have hWjm := bankWord_jetsMatch s hT₁ (β n)
  refine finiteWords_gauge_hasDerivWithinAt ht (W.path 2 t) (fun τ _ =>
    LawWord.isSymRec_path W (fun j i => isSymRec_recOf (bankLetter (stepOf (n + 1) T₁) (β n) j i))
      1 τ) (fun x => ?_) (fun x κ => ?_) y hdet b
  · exact hasDerivAt_pi.1 (LawWord.hasDerivAt_path hWmono hWjm (k := 0) (by norm_num) t) x
  · exact hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1
      (LawWord.hasDerivAt_path hWmono hWjm (k := 1) (by norm_num) t) x) κ.1.1) κ.1.2

end

end RenewalGeometry.OpenWriterFiniteWords
