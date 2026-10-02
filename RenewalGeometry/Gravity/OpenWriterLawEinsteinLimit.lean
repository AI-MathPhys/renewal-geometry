/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterLawJetLipschitz
import RenewalGeometry.Gravity.OpenWriterHarmonicPreparation
import RenewalGeometry.Gravity.OpenWriterLawCostControl
import RenewalGeometry.StatMech.SupplementLawRowNeighbourhoodExact

/-!
# The uniform Einstein limit of the law family (`thm:supp-law-einstein`) and of chronological
  law neighbourhoods (`thm:supp-law-row-neighbourhood`, Einstein clause)

* `supp_law_einstein` (**`thm:supp-law-einstein`**): for every sequence of marks `B_n` of the
  closed ball (no convergence required), the law-family solutions started from the samples of
  the harmonic preparation of `(γ, K) ∈ D_s(ε)` satisfy the four-slot jet comparison
  `eq:supp-law-jet-comparison` against the central writer (`law_jet_comparison`), stay in a common
  top ball, and their interpolants converge uniformly to the same harmonic vacuum development as
  the central writer (`supp_open_einstein`), with the metric rate `O(h ε)` in `H^{s-1}`, `H^{s-2}`,
  `H^{s-3}`.
* `supp_law_row_einstein` (Einstein clause of **`thm:supp-law-row-neighbourhood`**): a
  chronological word history whose stopped physical cost is at most `h²` along any sequence of
  cutoffs obeys `lem:supp-law-cost-control` with `d_h = h` (`law_cost_control`) and its
  interpolated records converge to the same vacuum development, at rate `O(h (ε + ε_w))`.
* Helpers: `lawLimit_interp_diff`, `lawLimit_interpD_diff`, `lawLimit_interpDD_diff`,
  `lawLimit_tendsto_of_upper`, `lawLimit_tendsto_of_upper_rate`, `lawLimit_sn_add_le`.
-/

open Finset Filter Topology UnitAddTorus
open scoped NNReal BigOperators Real

namespace RenewalGeometry.OpenWriterLimitRegularity

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterGridBridge RootParityConnector PeriodicGridSobolev.Composition
  HarmonicWriter OpenWriterContinuum HarmonicGaugePropagation ContractedBianchiJet HarmonicDefect

noncomputable section

set_option linter.unusedSectionVars false

/-- The interpolant difference of two grid records is controlled by the grid norm of the
difference: `‖𝓘_h u - 𝓘_h u'‖_{H^r} ≤ √(pc r) ‖u - u'‖_{r,h}` componentwise. -/
theorem lawLimit_interp_diff {N : ℕ} [NeZero N] (r : ℕ) (u u' : Grid N → MetricRec) (μ ν : Fin 4) :
    MemH r ⇑(cmp (interpRec u) μ ν - cmp (interpRec u') μ ν) ∧
      sn r ⇑(cmp (interpRec u) μ ν - cmp (interpRec u') μ ν) ≤
        Real.sqrt (pc r) * PeriodicGridSobolev.sobNorm r (cx (comp (u - u') μ ν)) := by
  rw [← cmp_sub, ← interpRec_sub]
  exact memH_cmp_reField r _ μ ν

theorem lawLimit_interpD_diff {N : ℕ} [NeZero N] (r : ℕ) (u u' : Grid N → MetricRec) (i : Fin 3)
    (κ : Upper) :
    MemH r ⇑(cmp (interpD u i) κ.1.1 κ.1.2 - cmp (interpD u' i) κ.1.1 κ.1.2) ∧
      sn r ⇑(cmp (interpD u i) κ.1.1 κ.1.2 - cmp (interpD u' i) κ.1.1 κ.1.2) ≤
        Real.sqrt (pc (r + 1)) * PeriodicGridSobolev.sobNorm (r + 1) (cx (comp (u - u') κ.1.1 κ.1.2)) := by
  have h0 := lawLimit_interp_diff (r + 1) u u' κ.1.1 κ.1.2
  have h := derivRec_cauchy u u' κ [i] r h0.1
  exact ⟨h.1, h.2.trans h0.2⟩

theorem lawLimit_interpDD_diff {N : ℕ} [NeZero N] (r : ℕ) (u u' : Grid N → MetricRec) (i j : Fin 3)
    (κ : Upper) :
    MemH r ⇑(cmp (interpDD u i j) κ.1.1 κ.1.2 - cmp (interpDD u' i j) κ.1.1 κ.1.2) ∧
      sn r ⇑(cmp (interpDD u i j) κ.1.1 κ.1.2 - cmp (interpDD u' i j) κ.1.1 κ.1.2) ≤
        Real.sqrt (pc (r + 2)) * PeriodicGridSobolev.sobNorm (r + 2) (cx (comp (u - u') κ.1.1 κ.1.2)) := by
  have h0 := lawLimit_interp_diff (r + 2) u u' κ.1.1 κ.1.2
  have h := derivRec_cauchy u u' κ [i, j] r h0.1
  exact ⟨h.1, h.2.trans h0.2⟩

/-- Sequences of symmetric record fields whose upper components are `H²`-close at rate
`D h` have the same uniform limit. -/
theorem lawLimit_tendsto_of_upper {F G : ℕ → C(T3, MetricRec)} {L : C(T3, MetricRec)}
    (hG : Tendsto G atTop (𝓝 L)) (hFs : ∀ n y μ ν, F n y μ ν = F n y ν μ)
    (hGs : ∀ n y μ ν, G n y μ ν = G n y ν μ) (D : ℝ)
    (h : ∀ n (κ : Upper), MemH 2 ⇑(cmp (F n) κ.1.1 κ.1.2 - cmp (G n) κ.1.1 κ.1.2) ∧
      sn 2 ⇑(cmp (F n) κ.1.1 κ.1.2 - cmp (G n) κ.1.1 κ.1.2) ≤ D * ((n : ℝ) + 1)⁻¹) :
    Tendsto F atTop (𝓝 L) := by
  have hn : ∀ n, ‖F n - G n‖ ≤ Real.sqrt cEmb * (D * ((n : ℝ) + 1)⁻¹) := fun n =>
    norm_sub_le_of_upper (F n) (G n) (hFs n) (hGs n) (h n)
  have hb : Tendsto (fun n : ℕ => Real.sqrt cEmb * (D * ((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simp only [one_div] at this
    simpa using (this.const_mul D).const_mul (Real.sqrt cEmb)
  have h0 : Tendsto (fun n => F n - G n) atTop (𝓝 0) :=
    squeeze_zero_norm hn hb
  have := hG.add h0
  simpa using this

/-- Triangle inequality for `sn` when only the second summand is known to be in `H^r`. -/
theorem lawLimit_sn_add_le {r : ℕ} (F G : CT) (hG : MemH r ⇑G) :
    sn r ⇑(F + G) ≤ sn r ⇑F + sn r ⇑G := by
  by_cases hF : MemH r ⇑F
  · exact sn_add_le' hF hG
  · have hFG : ¬ MemH r ⇑(F + G) := fun h => hF (by
      have := memH_sub h hG
      simpa using this)
    have e : sn r ⇑(F + G) = 0 := by
      unfold sn PeriodicGridSobolev.trigSobSq
      rw [tsum_eq_zero_of_not_summable hFG, Real.sqrt_zero]
    rw [e]
    exact add_nonneg (sn_nonneg _ _) (sn_nonneg _ _)

theorem lawLimit_three_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c ≤ d) : a ≤ d ∧ b ≤ d := ⟨by linarith, by linarith⟩

theorem lawLimit_isWriterSolution_of_zero {N : ℕ} [NeZero N] {T : ℝ} {q v : ℝ → Grid N → MetricRec}
    (h : IsAccSolution (lawAccel (fun _ _ => 0)) T q v) : IsWriterSolution T q v := by
  intro t ht
  obtain ⟨h1, h2, h3, h4⟩ := h t ht
  exact ⟨h1, h2, h3, fun x κ => by rw [← lawAccel_zero]; exact h4 x κ⟩

set_option maxHeartbeats 8000000 in
/-- **`thm:supp-law-einstein`** (uniform Einstein limit for the whole coefficient family), for
`s ≥ 6`.  There are `ε_s, T > 0` (`T ≤ T_B`, the common lifespan of the law family) and constants
`K, C, C_ε, C_B` such that for every `(γ, K) ∈ D_s(ε)` (`DsData`, `dataSize ≤ ε ≤ ε_s`), with the
harmonic preparation `V₀ = prepFun` and the central-writer solutions `q_n` of
`thm:supp-open-einstein` converging to the harmonic vacuum development `(Q, V, A)` (classical
solution of the reduced equation with data `(Q₀, V₀)` and vanishing Einstein tensor), and for
**every** sequence of marks `B_n` (`B_n = B_nᵀ`, `‖B_n‖_op ≤ b_n ≤ 1/48`; no convergence of `B_n`
required):
* the law-family writer with mark `B_n` has a unique solution `(q_{B_n}, v_{B_n})` on `[0, T_B]`
  from the same initial samples, and both histories stay in the common top ball `C_B ε`;
* the jet comparison `eq:supp-law-jet-comparison` holds for `j = 0, 1, 2, 3` (`q''' = jetDeriv`),
  `≤ C_B h ‖B_n‖ ε` with `h = 1/(n+1)`;
* the whole interpolated sequence (`𝓘_h q_B`, `𝓘_h ∂ₜq_B`, `𝓘_h ∂ₜ²q_B` and the spatial derivatives
  of the interpolants) converges uniformly on `𝕋³` to the **same** vacuum development, with the
  metric rate of `eq:supp-open-metric-rate`:
  `‖𝓘_h q_B - Q‖_{H^{s-1}} + ‖𝓘_h ∂ₜq_B - V‖_{H^{s-2}} + ‖𝓘_h ∂ₜ²q_B - A‖_{H^{s-3}} = O(h ε)`
  (each upper component, constants uniform in the marks). -/
theorem supp_law_einstein (s : ℕ) (hs : 6 ≤ s) :
    ∃ εs > 0, ∃ T > 0, ∃ TB ≥ T, ∃ K ≥ 0, ∃ C ≥ 0, ∃ Cε ≥ 0, ∃ CB ≥ 0,
    ∀ (Q₀ Kr : C(T3, MetricRec)) (Qd Kd : Fin 3 → C(T3, MetricRec))
      (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      DsData s Q₀ Kr Qd Kd Qdd → dataSize s Q₀ Kr ≤ ε → ε ≤ εs →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
      ∃ q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec,
        (∀ n, IsWriterSolution T (q n) (v n) ∧ q n 0 = sampleRec (n + 1) ⇑Q₀ ∧
          v n 0 = sampleRec (n + 1) ⇑V₀) ∧
        ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd' Vd' : ℝ → Fin 3 → C(T3, MetricRec))
          (Qdd' : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
          (∀ t ∈ Set.Icc 0 T,
            Tendsto (fun n => interpRec (q n t)) atTop (𝓝 (Q t)) ∧
            Tendsto (fun n => interpRec (v n t)) atTop (𝓝 (V t)) ∧
            Tendsto (fun n => interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t))))
              atTop (𝓝 (A t)) ∧
            IsContJet (Q t) (V t) (Qd' t) (Vd' t) (Qdd' t) ∧
            (∀ y (κ : Upper), normalRow (Q t y) (V t y) (A t y) (fun i => Qd' t i y)
              (fun i => Vd' t i y) (fun i j => Qdd' t i j y) κ.1.1 κ.1.2 = 0) ∧
            (t ∈ Set.Ioo 0 T → ∀ y, HasDerivAt (fun τ => Q τ y) (V t y) t ∧
              HasDerivAt (fun τ => V τ y) (A t y) t) ∧
            ∀ y μ ν, einstein (minkowski + Q t y) (recInv (minkowski + Q t y))
              (metricJet (V t y, fun i => Qd' t i y))
              (ddArr (A t y) (fun i => Vd' t i y) (fun i j => Qdd' t i j y)) μ ν = 0) ∧
          ∀ (b : ℕ → ℝ) (B : ℕ → Upper → Upper → ℝ), (∀ n, IsMark (b n) (B n)) →
            (∀ n, b n ≤ 1 / 48) →
          ∃ qB vB : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec,
            (∀ n, IsAccSolution (lawAccel (B n)) TB (qB n) (vB n) ∧
              qB n 0 = sampleRec (n + 1) ⇑Q₀ ∧ vB n 0 = sampleRec (n + 1) ⇑V₀) ∧
            (∀ n (q' v' : ℝ → Grid (n + 1) → MetricRec), q' 0 = sampleRec (n + 1) ⇑Q₀ →
              v' 0 = sampleRec (n + 1) ⇑V₀ → IsAccSolution (lawAccel (B n)) TB q' v' →
              ∀ t ∈ Set.Icc 0 TB, q' t = qB n t ∧ v' t = vB n t) ∧
            (∀ n, ∀ t ∈ Set.Icc 0 T, Xnorm s (qB n t) (vB n t) ≤ CB * ε ∧
              Xnorm s (q n t) (v n t) ≤ CB * ε) ∧
            (∀ n, ∀ t ∈ Set.Icc 0 T, ∀ κ : Upper,
              (∀ x, HasDerivWithinAt (fun τ => lawAccel (B n) (qB n τ) (vB n τ) x κ.1.1 κ.1.2)
                (jetDeriv (B n) (qB n t) (vB n t) (symRec (lawAccel (B n) (qB n t) (vB n t))) x
                  κ.1.1 κ.1.2) (Set.Icc 0 T) t) ∧
              (∀ x, HasDerivWithinAt (fun τ => harmonicWriterAcceleration (q n τ) (v n τ) x κ.1.1 κ.1.2)
                (jetDeriv (fun _ _ => 0) (q n t) (v n t)
                  (symRec (harmonicWriterAcceleration (q n t) (v n t))) x κ.1.1 κ.1.2)
                (Set.Icc 0 T) t) ∧
              Xnorm (s - 2) (qB n t - q n t) (vB n t - v n t) +
                Fnorm (s - 3) (lawAccel (B n) (qB n t) (vB n t) -
                  harmonicWriterAcceleration (q n t) (v n t)) +
                PeriodicGridSobolev.sobNorm (s - 4)
                  (cx (fun x => jetDeriv (B n) (qB n t) (vB n t)
                    (symRec (lawAccel (B n) (qB n t) (vB n t))) x κ.1.1 κ.1.2) -
                  cx (fun x => jetDeriv (fun _ _ => 0) (q n t) (v n t)
                    (symRec (harmonicWriterAcceleration (q n t) (v n t))) x κ.1.1 κ.1.2)) ≤
                CB * ((n : ℝ) + 1)⁻¹ * b n * ε) ∧
            ∀ t ∈ Set.Icc 0 T,
              Tendsto (fun n => interpRec (qB n t)) atTop (𝓝 (Q t)) ∧
              Tendsto (fun n => interpRec (vB n t)) atTop (𝓝 (V t)) ∧
              Tendsto (fun n => interpRec (symRec (lawAccel (B n) (qB n t) (vB n t)))) atTop
                (𝓝 (A t)) ∧
              (∀ i, Tendsto (fun n => interpD (qB n t) i) atTop (𝓝 (Qd' t i))) ∧
              (∀ i, Tendsto (fun n => interpD (vB n t) i) atTop (𝓝 (Vd' t i))) ∧
              (∀ i j, Tendsto (fun n => interpDD (qB n t) i j) atTop (𝓝 (Qdd' t i j))) ∧
              ∀ n (κ : Upper),
                sn (s - 1) ⇑(cmp (interpRec (qB n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ≤
                  (C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε * ((n : ℝ) + 1)⁻¹ ∧
                sn (s - 2) ⇑(cmp (interpRec (vB n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ≤
                  (C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε * ((n : ℝ) + 1)⁻¹ ∧
                sn (s - 3) ⇑(cmp (interpRec (lawAccel (B n) (qB n t) (vB n t))) κ.1.1 κ.1.2 -
                  cmp (A t) κ.1.1 κ.1.2) ≤
                  (C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨εs, hεs, TC, hTC, K, hK, C, hC, Cε, hCε, hE⟩ := supp_open_einstein s hs
  obtain ⟨εL, hεL, TL, hTL, CL, hCL, hL⟩ := law_lifespan s (by omega)
  obtain ⟨ρ, hρ, hcmp⟩ := law_jet_comparison s hs
  obtain ⟨δM, hδM, CM, hCM, hprep⟩ := prep_moser s (by omega)
  obtain ⟨CS, hCS, hsamp⟩ := Xnorm_sample_le s (by omega)
  set T := min TC TL with hTdef
  have hT : 0 < T := lt_min hTC hTL
  have hTC' : T ≤ TC := min_le_left _ _
  have hTL' : T ≤ TL := min_le_right _ _
  obtain ⟨CJ, hCJ, hJ⟩ := hcmp T hT.le
  set Cp : ℝ := 1 + CM
  have hCp : 0 ≤ Cp := by positivity
  set c0 : ℝ := CS * Cp
  have hc0 : 0 ≤ c0 := by positivity
  set E0 : ℝ := CL * c0
  have hE0 : 0 ≤ E0 := by positivity
  set S : ℝ := Real.sqrt (pc (s - 1)) + Real.sqrt (pc (s - 2)) + Real.sqrt (pc (s - 3)) +
    Real.sqrt (pc 2) + Real.sqrt (pc 3) + Real.sqrt (pc 4) + 1
  have hS1 : 1 ≤ S := by
    have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
    have := Real.sqrt_nonneg (pc (s - 3)); have := Real.sqrt_nonneg (pc 2)
    have := Real.sqrt_nonneg (pc 3); have := Real.sqrt_nonneg (pc 4)
    simp only [S]; linarith
  set CB : ℝ := (CJ + 1) * (E0 + 1) * S
  have hCB : 0 ≤ CB := by positivity
  have hJE : CJ * E0 ≤ (CJ + 1) * (E0 + 1) := by nlinarith
  have hkey : ∀ x, 0 ≤ x → x ≤ S → x * (CJ * E0) ≤ CB := by
    intro x hx hxS
    calc x * (CJ * E0) ≤ S * ((CJ + 1) * (E0 + 1)) :=
          mul_le_mul hxS hJE (by positivity) (by linarith)
      _ = CB := by simp only [CB]; ring
  have hE0CB : E0 ≤ CB := by
    have h1 : E0 ≤ (CJ + 1) * (E0 + 1) := by nlinarith
    calc E0 ≤ (CJ + 1) * (E0 + 1) * 1 := by linarith
      _ ≤ CB := mul_le_mul_of_nonneg_left hS1 (by positivity)
  have hCJCB : CJ * E0 ≤ CB := by simpa using hkey 1 zero_le_one hS1
  refine ⟨min εs (min δM (min (εL / (c0 + 1)) (ρ / (E0 + 1)))), by positivity, T, hT, TL, hTL',
    K, hK, C, hC, Cε, hCε, CB, hCB, fun Q₀ Kr Qd Kd Qdd ε hD hsz hεs' => ?_⟩
  have hA0 : 0 ≤ ccoordSum (s + 1) bM Q₀ := ccoordSum_nonneg _ _ _
  have hB0 : 0 ≤ ccoordSum s bM Kr := ccoordSum_nonneg _ _ _
  have hε0 : 0 ≤ ε := (add_nonneg hA0 hB0).trans hsz
  have hεM : ε ≤ δM := hεs'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεL' : ε ≤ εL / (c0 + 1) :=
    hεs'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hερ : ε ≤ ρ / (E0 + 1) :=
    hεs'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hA : ccoordSum (s + 1) bM Q₀ ≤ ε := by unfold dataSize at hsz; linarith
  obtain ⟨V₀, hV₀, q, v, hqv, huniq, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, hcr⟩ :=
    hE Q₀ Kr Qd Kd Qdd ε hD hsz (hεs'.trans (min_le_left _ _))
  obtain ⟨V₀', hV₀', hVreg, hVb⟩ := hprep Q₀ Kr Qd hD.dQ hD.regQ hD.regK (hA.trans hεM)
  have eV : V₀' = V₀ := ContinuousMap.ext fun y => congrFun (hV₀'.trans hV₀.symm) y
  rw [eV] at hVreg hVb
  have hVsym : ∀ y μ ν, V₀ y μ ν = V₀ y ν μ := by
    intro y μ ν
    rw [hV₀]
    refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
      simp only [prepFun, sliceMat_zero_zero, sliceMat_zero_succ, sliceMat_succ_zero,
        sliceMat_succ_succ, Matrix.of_apply]
    rw [hD.symK y i.succ j.succ]
  have hcT : contTop s Q₀ V₀ ≤ Cp * ε := by
    unfold contTop
    have := mul_le_mul_of_nonneg_left hsz hCM
    unfold dataSize at this
    simp only [Cp]; nlinarith
  have hX0 : ∀ (N : ℕ) [NeZero N], Xnorm s (sampleRec N ⇑Q₀) (sampleRec N ⇑V₀) ≤ c0 * ε :=
    fun N _ => (hsamp N Q₀ V₀ hD.regQ hVreg).trans (by
      calc CS * contTop s Q₀ V₀ ≤ CS * (Cp * ε) := mul_le_mul_of_nonneg_left hcT hCS
        _ = c0 * ε := by simp only [c0]; ring)
  have hc0L : c0 * ε ≤ εL := by
    have h := hεL'; rw [le_div_iff₀ (by positivity)] at h; nlinarith
  have hE0ρ : E0 * ε ≤ ρ := by
    have h := hερ; rw [le_div_iff₀ (by positivity)] at h; nlinarith
  have hbound : ∀ n, ∀ q' v' : ℝ → Grid (n + 1) → MetricRec,
      (∀ t ∈ Set.Icc 0 TL, Xnorm s (q' t) (v' t) ≤
        CL * Xnorm s (sampleRec (n + 1) ⇑Q₀) (sampleRec (n + 1) ⇑V₀)) →
      ∀ t ∈ Set.Icc 0 TL, Xnorm s (q' t) (v' t) ≤ E0 * ε := by
    intro n q' v' h t ht
    refine (h t ht).trans ?_
    have := mul_le_mul_of_nonneg_left (hX0 (n + 1)) hCL
    calc _ ≤ CL * (c0 * ε) := this
      _ = E0 * ε := by simp only [E0]; ring
  -- the central chart
  have hcentral : ∀ n, ∀ t ∈ Set.Icc 0 T, Xnorm s (q n t) (v n t) ≤ E0 * ε := by
    intro n t ht
    obtain ⟨⟨qc, vc, hqc0, hvc0, hsolc, hbdc⟩, huc⟩ := hL (n + 1) (fun _ _ => 0) isMark_zero
      (sampleRec (n + 1) ⇑Q₀) (sampleRec (n + 1) ⇑V₀) (isSymRec_sampleRec hD.symQ)
      (isSymRec_sampleRec hVsym) ((hX0 (n + 1)).trans hc0L)
    obtain ⟨hsol, hq0, hv0⟩ := hqv n
    have heq : q n t = qc t ∧ v n t = vc t := by
      rcases le_total TL TC with h | h
      · exact huc (q n) (v n) qc vc hq0 hv0 hqc0 hvc0
          (isAccSolution_zero_of_writer (isWriterSolution_mono_T hsol h)) hsolc t
          ⟨ht.1, ht.2.trans hTL'⟩
      · have := huniq n qc vc hqc0 hvc0
          (lawLimit_isWriterSolution_of_zero (isAccSolution_mono_T hsolc h)) t
          ⟨ht.1, ht.2.trans hTC'⟩
        exact ⟨this.1.symm, this.2.symm⟩
    rw [heq.1, heq.2]
    exact hbound n qc vc hbdc t ⟨ht.1, ht.2.trans hTL'⟩
  refine ⟨V₀, hV₀, q, v, fun n => ⟨isWriterSolution_mono_T (hqv n).1 hTC', (hqv n).2.1,
    (hqv n).2.2⟩, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, fun t ht => ?_, fun b B hB hb => ?_⟩
  · obtain ⟨⟨h1, h2, h3, -, -, -, -, h8, h9, h10, -, -⟩, h13⟩ := hcr t ⟨ht.1, ht.2.trans hTC'⟩
    exact ⟨h1, h2, h3, h8, h9, fun htt => h10 ⟨htt.1, htt.2.trans_le hTC'⟩, h13⟩
  -- the law family
  have hex : ∀ n, ∃ qB vB : ℝ → Grid (n + 1) → MetricRec, qB 0 = sampleRec (n + 1) ⇑Q₀ ∧
      vB 0 = sampleRec (n + 1) ⇑V₀ ∧ IsAccSolution (lawAccel (B n)) TL qB vB ∧
      ∀ t ∈ Set.Icc 0 TL, Xnorm s (qB t) (vB t) ≤
        CL * Xnorm s (sampleRec (n + 1) ⇑Q₀) (sampleRec (n + 1) ⇑V₀) := fun n =>
    (hL (n + 1) (B n) ((hB n).mono (hb n)) (sampleRec (n + 1) ⇑Q₀) (sampleRec (n + 1) ⇑V₀)
      (isSymRec_sampleRec hD.symQ) (isSymRec_sampleRec hVsym) ((hX0 (n + 1)).trans hc0L)).1
  choose qB vB hqB0 hvB0 hsolB hbdB using hex
  have hBbd : ∀ n, ∀ t ∈ Set.Icc 0 T, Xnorm s (qB n t) (vB n t) ≤ E0 * ε := fun n t ht =>
    hbound n (qB n) (vB n) (hbdB n) t ⟨ht.1, ht.2.trans hTL'⟩
  have hjet : ∀ n, ∀ t ∈ Set.Icc 0 T, ∀ κ : Upper,
      (∀ x, HasDerivWithinAt (fun τ => lawAccel (B n) (qB n τ) (vB n τ) x κ.1.1 κ.1.2)
        (jetDeriv (B n) (qB n t) (vB n t) (symRec (lawAccel (B n) (qB n t) (vB n t))) x
          κ.1.1 κ.1.2) (Set.Icc 0 T) t) ∧
      (∀ x, HasDerivWithinAt (fun τ => harmonicWriterAcceleration (q n τ) (v n τ) x κ.1.1 κ.1.2)
        (jetDeriv (fun _ _ => 0) (q n t) (v n t)
          (symRec (harmonicWriterAcceleration (q n t) (v n t))) x κ.1.1 κ.1.2)
        (Set.Icc 0 T) t) ∧
      Xnorm (s - 2) (qB n t - q n t) (vB n t - v n t) +
        Fnorm (s - 3) (lawAccel (B n) (qB n t) (vB n t) -
          harmonicWriterAcceleration (q n t) (v n t)) +
        PeriodicGridSobolev.sobNorm (s - 4)
          (cx (fun x => jetDeriv (B n) (qB n t) (vB n t)
            (symRec (lawAccel (B n) (qB n t) (vB n t))) x κ.1.1 κ.1.2) -
          cx (fun x => jetDeriv (fun _ _ => 0) (q n t) (v n t)
            (symRec (harmonicWriterAcceleration (q n t) (v n t))) x κ.1.1 κ.1.2)) ≤
        CJ * ((n : ℝ) + 1)⁻¹ * b n * (E0 * ε) := by
    intro n t ht κ
    have h := hJ (n + 1) (b n) (B n) (hB n) (hb n) (E0 * ε) (qB n) (vB n) (q n) (v n)
      ((hqB0 n).trans (hqv n).2.1.symm) ((hvB0 n).trans (hqv n).2.2.symm)
      (isAccSolution_mono_T (hsolB n) hTL') (isWriterSolution_mono_T (hqv n).1 hTC')
      (hBbd n) (hcentral n) hE0ρ t ht κ
    have e : (((n + 1 : ℕ) : ℝ))⁻¹ = ((n : ℝ) + 1)⁻¹ := by rw [Nat.cast_succ]
    rw [e] at h
    exact h
  have hbn : ∀ n, 0 ≤ b n := fun n => (hB n).nonneg
  -- grid differences at rate `h`
  set D0 : ℝ := CJ * (E0 * ε)
  have hD0 : 0 ≤ D0 := by positivity
  have hdiff : ∀ n, ∀ t ∈ Set.Icc 0 T, Xnorm (s - 2) (qB n t - q n t) (vB n t - v n t) ≤
      D0 * ((n : ℝ) + 1)⁻¹ ∧ Fnorm (s - 3) (lawAccel (B n) (qB n t) (vB n t) -
        harmonicWriterAcceleration (q n t) (v n t)) ≤ D0 * ((n : ℝ) + 1)⁻¹ := by
    intro n t ht
    have h := (hjet n t ht ⟨(0, 0), le_rfl⟩).2.2
    have hb1 : CJ * ((n : ℝ) + 1)⁻¹ * b n * (E0 * ε) ≤ D0 * ((n : ℝ) + 1)⁻¹ := by
      have hn : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
      have h1 : b n ≤ 1 := (hb n).trans (by norm_num)
      calc CJ * ((n : ℝ) + 1)⁻¹ * b n * (E0 * ε) = (CJ * ((n : ℝ) + 1)⁻¹ * (E0 * ε)) * b n := by
            ring
        _ ≤ (CJ * ((n : ℝ) + 1)⁻¹ * (E0 * ε)) * 1 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = D0 * ((n : ℝ) + 1)⁻¹ := by simp only [D0]; ring
    have := lawLimit_three_le (Xnorm_nonneg _ _ _) (Fnorm_nonneg _ _)
      (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _) h
    exact ⟨this.1.trans hb1, this.2.trans hb1⟩
  refine ⟨qB, vB, fun n => ⟨hsolB n, hqB0 n, hvB0 n⟩, fun n q' v' h1 h2 h3 t ht => ?_,
    fun n t ht => ⟨(hBbd n t ht).trans (mul_le_mul_of_nonneg_right hE0CB hε0),
      (hcentral n t ht).trans (mul_le_mul_of_nonneg_right hE0CB hε0)⟩,
    fun n t ht κ => ?_, fun t ht => ?_⟩
  · exact (hL (n + 1) (B n) ((hB n).mono (hb n)) (sampleRec (n + 1) ⇑Q₀) (sampleRec (n + 1) ⇑V₀)
      (isSymRec_sampleRec hD.symQ) (isSymRec_sampleRec hVsym) ((hX0 (n + 1)).trans hc0L)).2
      q' v' (qB n) (vB n) h1 h2 (hqB0 n) (hvB0 n) h3 (hsolB n) t ht
  · obtain ⟨h1, h2, h3⟩ := hjet n t ht κ
    refine ⟨h1, h2, h3.trans ?_⟩
    have hn : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    have h4 : CJ * E0 * ε ≤ CB * ε := mul_le_mul_of_nonneg_right hCJCB hε0
    calc CJ * ((n : ℝ) + 1)⁻¹ * b n * (E0 * ε) = (((n : ℝ) + 1)⁻¹ * b n) * (CJ * E0 * ε) := by
          ring
      _ ≤ (((n : ℝ) + 1)⁻¹ * b n) * (CB * ε) :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg hn (hbn n))
      _ = CB * ((n : ℝ) + 1)⁻¹ * b n * ε := by ring
  -- convergence
  have htC : t ∈ Set.Icc 0 TC := ⟨ht.1, ht.2.trans hTC'⟩
  have htL : t ∈ Set.Icc 0 TL := ⟨ht.1, ht.2.trans hTL'⟩
  obtain ⟨⟨c1, c2, c3, -, c5, c6, c7, -, -, -, c11, -⟩, -⟩ := hcr t htC
  have hsq : ∀ n, IsSymRec (q n t) := fun n => ((hqv n).1 t htC).1
  have hsv : ∀ n, IsSymRec (v n t) := fun n => ((hqv n).1 t htC).2.1
  have hsqB : ∀ n, IsSymRec (qB n t) := fun n => (hsolB n t htL).1
  have hsvB : ∀ n, IsSymRec (vB n t) := fun n => (hsolB n t htL).2.1
  have hsdq : ∀ n, IsSymRec (qB n t - q n t) := fun n => isSymRec_sub (hsqB n) (hsq n)
  have hsdv : ∀ n, IsSymRec (vB n t - v n t) := fun n => isSymRec_sub (hsvB n) (hsv n)
  have gq : ∀ n (κ : Upper) (r : ℕ), r ≤ s - 1 →
      PeriodicGridSobolev.sobNorm r (cx (comp (qB n t - q n t) κ.1.1 κ.1.2)) ≤ D0 * ((n : ℝ) + 1)⁻¹ :=
    fun n κ r hr => (sobNorm_q_le (s - 2) (hsdq n) _ _ _ (by omega)).trans (hdiff n t ht).1
  have gv : ∀ n (κ : Upper) (r : ℕ), r ≤ s - 2 →
      PeriodicGridSobolev.sobNorm r (cx (comp (vB n t - v n t) κ.1.1 κ.1.2)) ≤ D0 * ((n : ℝ) + 1)⁻¹ :=
    fun n κ r hr => (sobNorm_v_le (s - 2) _ (hsdv n) _ _ hr).trans (hdiff n t ht).1
  have ga : ∀ n (κ : Upper) (r : ℕ), r ≤ s - 3 →
      PeriodicGridSobolev.sobNorm r (cx (comp (lawAccel (B n) (qB n t) (vB n t) -
        harmonicWriterAcceleration (q n t) (v n t)) κ.1.1 κ.1.2)) ≤ D0 * ((n : ℝ) + 1)⁻¹ :=
    fun n κ r hr => ((PeriodicGridSobolev.Moser.sobNorm_mono hr _).trans
      (sobNorm_le_Fnorm (s - 3) _ κ)).trans (hdiff n t ht).2
  have mulD : ∀ (r : ℕ) (n : ℕ) (x : ℝ), x ≤ D0 * ((n : ℝ) + 1)⁻¹ →
      Real.sqrt (pc r) * x ≤ Real.sqrt (pc r) * D0 * ((n : ℝ) + 1)⁻¹ := fun r n x hx => by
    calc Real.sqrt (pc r) * x ≤ Real.sqrt (pc r) * (D0 * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg (pc r))
      _ = _ := by ring
  refine ⟨?_, ?_, ?_, fun i => ?_, fun i => ?_, fun i j => ?_, fun n κ => ⟨?_, ?_, ?_⟩⟩
  · refine lawLimit_tendsto_of_upper c1 (fun n y μ ν => interpRec_symm (hsqB n) y μ ν)
      (fun n y μ ν => interpRec_symm (hsq n) y μ ν) (Real.sqrt (pc 2) * D0) fun n κ => ?_
    have h := lawLimit_interp_diff 2 (qB n t) (q n t) κ.1.1 κ.1.2
    exact ⟨h.1, h.2.trans (mulD 2 n _ (gq n κ 2 (by omega)))⟩
  · refine lawLimit_tendsto_of_upper c2 (fun n y μ ν => interpRec_symm (hsvB n) y μ ν)
      (fun n y μ ν => interpRec_symm (hsv n) y μ ν) (Real.sqrt (pc 2) * D0) fun n κ => ?_
    have h := lawLimit_interp_diff 2 (vB n t) (v n t) κ.1.1 κ.1.2
    exact ⟨h.1, h.2.trans (mulD 2 n _ (gv n κ 2 (by omega)))⟩
  · refine lawLimit_tendsto_of_upper c3 (fun n y μ ν => interpRec_symRec_symm _ y μ ν)
      (fun n y μ ν => interpRec_symRec_symm _ y μ ν) (Real.sqrt (pc 2) * D0) fun n κ => ?_
    rw [cmp_interpRec_symRec, cmp_interpRec_symRec]
    have h := lawLimit_interp_diff 2 (lawAccel (B n) (qB n t) (vB n t))
      (harmonicWriterAcceleration (q n t) (v n t)) κ.1.1 κ.1.2
    exact ⟨h.1, h.2.trans (mulD 2 n _ (ga n κ 2 (by omega)))⟩
  · refine lawLimit_tendsto_of_upper (c5 i) (fun n y μ ν => interpD_symm (hsqB n) i y μ ν)
      (fun n y μ ν => interpD_symm (hsq n) i y μ ν) (Real.sqrt (pc 3) * D0) fun n κ => ?_
    have h := lawLimit_interpD_diff 2 (qB n t) (q n t) i κ
    exact ⟨h.1, h.2.trans (mulD 3 n _ (gq n κ 3 (by omega)))⟩
  · refine lawLimit_tendsto_of_upper (c6 i) (fun n y μ ν => interpD_symm (hsvB n) i y μ ν)
      (fun n y μ ν => interpD_symm (hsv n) i y μ ν) (Real.sqrt (pc 3) * D0) fun n κ => ?_
    have h := lawLimit_interpD_diff 2 (vB n t) (v n t) i κ
    exact ⟨h.1, h.2.trans (mulD 3 n _ (gv n κ 3 (by omega)))⟩
  · refine lawLimit_tendsto_of_upper (c7 i j) (fun n y μ ν => interpDD_symm (hsqB n) i j y μ ν)
      (fun n y μ ν => interpDD_symm (hsq n) i j y μ ν) (Real.sqrt (pc 4) * D0) fun n κ => ?_
    have h := lawLimit_interpDD_diff 2 (qB n t) (q n t) i j κ
    exact ⟨h.1, h.2.trans (mulD 4 n _ (gq n κ 4 (by omega)))⟩
  all_goals
    have hn : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    have hfac : 0 ≤ C * Real.exp (K * t) * (1 + t) := by
      have : 0 ≤ 1 + t := by linarith [ht.1]
      positivity
  · have e : cmp (interpRec (qB n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2 =
        (cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) +
        (cmp (interpRec (qB n t)) κ.1.1 κ.1.2 - cmp (interpRec (q n t)) κ.1.1 κ.1.2) := by abel
    rw [e]
    have h := lawLimit_interp_diff (s - 1) (qB n t) (q n t) κ.1.1 κ.1.2
    refine (lawLimit_sn_add_le _ _ h.1).trans ?_
    have r1 := (c11 n κ).1
    have r2 := h.2.trans (mulD (s - 1) n _ (gq n κ (s - 1) le_rfl))
    have hk := hkey (Real.sqrt (pc (s - 1))) (Real.sqrt_nonneg _) (by
      have := Real.sqrt_nonneg (pc (s - 2)); have := Real.sqrt_nonneg (pc (s - 3))
      have := Real.sqrt_nonneg (pc 2); have := Real.sqrt_nonneg (pc 3)
      have := Real.sqrt_nonneg (pc 4); simp only [S]; linarith)
    have h5 : Real.sqrt (pc (s - 1)) * D0 * ((n : ℝ) + 1)⁻¹ ≤ CB * ε * ((n : ℝ) + 1)⁻¹ := by
      calc Real.sqrt (pc (s - 1)) * D0 * ((n : ℝ) + 1)⁻¹ =
            Real.sqrt (pc (s - 1)) * (CJ * E0) * ε * ((n : ℝ) + 1)⁻¹ := by simp only [D0]; ring
        _ ≤ CB * ε * ((n : ℝ) + 1)⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hε0) hn
    have e2 : (C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε * ((n : ℝ) + 1)⁻¹ =
        C * Real.exp (K * t) * (1 + t) * (Cε * ε) * ((n : ℝ) + 1)⁻¹ + CB * ε * ((n : ℝ) + 1)⁻¹ := by
      ring
    rw [e2]
    linarith
  · have e : cmp (interpRec (vB n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2 =
        (cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) +
        (cmp (interpRec (vB n t)) κ.1.1 κ.1.2 - cmp (interpRec (v n t)) κ.1.1 κ.1.2) := by abel
    rw [e]
    have h := lawLimit_interp_diff (s - 2) (vB n t) (v n t) κ.1.1 κ.1.2
    refine (lawLimit_sn_add_le _ _ h.1).trans ?_
    have r1 := (c11 n κ).2.1
    have r2 := h.2.trans (mulD (s - 2) n _ (gv n κ (s - 2) le_rfl))
    have hk := hkey (Real.sqrt (pc (s - 2))) (Real.sqrt_nonneg _) (by
      have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 3))
      have := Real.sqrt_nonneg (pc 2); have := Real.sqrt_nonneg (pc 3)
      have := Real.sqrt_nonneg (pc 4); simp only [S]; linarith)
    have h5 : Real.sqrt (pc (s - 2)) * D0 * ((n : ℝ) + 1)⁻¹ ≤ CB * ε * ((n : ℝ) + 1)⁻¹ := by
      calc Real.sqrt (pc (s - 2)) * D0 * ((n : ℝ) + 1)⁻¹ =
            Real.sqrt (pc (s - 2)) * (CJ * E0) * ε * ((n : ℝ) + 1)⁻¹ := by simp only [D0]; ring
        _ ≤ CB * ε * ((n : ℝ) + 1)⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hε0) hn
    have e2 : (C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε * ((n : ℝ) + 1)⁻¹ =
        C * Real.exp (K * t) * (1 + t) * (Cε * ε) * ((n : ℝ) + 1)⁻¹ + CB * ε * ((n : ℝ) + 1)⁻¹ := by
      ring
    rw [e2]
    linarith
  · have e : cmp (interpRec (lawAccel (B n) (qB n t) (vB n t))) κ.1.1 κ.1.2 - cmp (A t) κ.1.1 κ.1.2 =
        (cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
          cmp (A t) κ.1.1 κ.1.2) +
        (cmp (interpRec (lawAccel (B n) (qB n t) (vB n t))) κ.1.1 κ.1.2 -
          cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2) := by abel
    rw [e]
    have h := lawLimit_interp_diff (s - 3) (lawAccel (B n) (qB n t) (vB n t))
      (harmonicWriterAcceleration (q n t) (v n t)) κ.1.1 κ.1.2
    refine (lawLimit_sn_add_le _ _ h.1).trans ?_
    have r1 := (c11 n κ).2.2
    have r2 := h.2.trans (mulD (s - 3) n _ (ga n κ (s - 3) le_rfl))
    have hk := hkey (Real.sqrt (pc (s - 3))) (Real.sqrt_nonneg _) (by
      have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
      have := Real.sqrt_nonneg (pc 2); have := Real.sqrt_nonneg (pc 3)
      have := Real.sqrt_nonneg (pc 4); simp only [S]; linarith)
    have h5 : Real.sqrt (pc (s - 3)) * D0 * ((n : ℝ) + 1)⁻¹ ≤ CB * ε * ((n : ℝ) + 1)⁻¹ := by
      calc Real.sqrt (pc (s - 3)) * D0 * ((n : ℝ) + 1)⁻¹ =
            Real.sqrt (pc (s - 3)) * (CJ * E0) * ε * ((n : ℝ) + 1)⁻¹ := by simp only [D0]; ring
        _ ≤ CB * ε * ((n : ℝ) + 1)⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hε0) hn
    have e2 : (C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε * ((n : ℝ) + 1)⁻¹ =
        C * Real.exp (K * t) * (1 + t) * (Cε * ε) * ((n : ℝ) + 1)⁻¹ + CB * ε * ((n : ℝ) + 1)⁻¹ := by
      ring
    rw [e2]
    linarith

/-- Eventual version of `lawLimit_tendsto_of_upper` with an arbitrary rate `r_m → 0`. -/
theorem lawLimit_tendsto_of_upper_rate {F G : ℕ → C(T3, MetricRec)} {L : C(T3, MetricRec)}
    (hG : Tendsto G atTop (𝓝 L)) (hFs : ∀ n y μ ν, F n y μ ν = F n y ν μ)
    (hGs : ∀ n y μ ν, G n y μ ν = G n y ν μ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) (n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → ∀ κ : Upper, MemH 2 ⇑(cmp (F n) κ.1.1 κ.1.2 - cmp (G n) κ.1.1 κ.1.2) ∧
      sn 2 ⇑(cmp (F n) κ.1.1 κ.1.2 - cmp (G n) κ.1.1 κ.1.2) ≤ r n) :
    Tendsto F atTop (𝓝 L) := by
  have hn : ∀ᶠ n in atTop, ‖F n - G n‖ ≤ Real.sqrt cEmb * r n :=
    eventually_atTop.2 ⟨n₀, fun n hn => norm_sub_le_of_upper (F n) (G n) (hFs n) (hGs n) (h n hn)⟩
  have hb : Tendsto (fun n : ℕ => Real.sqrt cEmb * r n) atTop (𝓝 0) := by
    simpa using hr.const_mul (Real.sqrt cEmb)
  have h0 : Tendsto (fun n => F n - G n) atTop (𝓝 0) := squeeze_zero_norm' hn hb
  have := hG.add h0
  simpa using this

set_option maxHeartbeats 8000000 in
/-- **The Einstein clause of `thm:supp-law-row-neighbourhood`**: a chronological history whose
stopped physical cost is at most `h²` obeys `lem:supp-law-cost-control` with `d_h = h` and has the
same Einstein limit as `thm:supp-law-einstein`.  For `s ≥ 6` there are `ε_s, T, ε_w, ρ > 0` and
constants such that for every `(γ, K) ∈ D_s(ε)` there is the harmonic vacuum development
`(Q, V, A)` of `supp_law_einstein` (data `(Q₀, V₀)`, `V₀ = prepFun`, vanishing Einstein tensor) with
the following property.  Let `B_n` be any marks of the closed ball, `φ` any sequence of cutoff
indices with `φ m → ∞` (e.g. the odd cutoffs `N = 2m + 1`), and `W_m` chronological words on the
grid `N = φ m + 1` (`h = 1/(φ m + 1)`, cells `c₋h² ≤ τ ≤ c₊h²`, shared jets through order three)
with mark `B_{φ m}`, starting at the samples of `(Q₀, V₀)`, with initial record of size
`≤ ε_w ≤ ε_w⁰` (the cost normalization).  If the stopped cost satisfies `C_h ≤ h²` for every
`m ≥ m₀`, then for those `m` the word has no failure and stays in the guard chart, and the
interpolated word records `𝓘_h Q`, `𝓘_h Q'`, `𝓘_h Q''` converge uniformly on `𝕋³` to `Q, V, A` on
`[0, T]`, at the rate `O(h (ε + ε_w))` in `H^{s-1}`, `H^{s-2}`, `H^{s-3}`. -/
theorem supp_law_row_einstein (s : ℕ) (hs : 6 ≤ s) :
    ∃ εs > 0, ∃ T > 0, ∃ εw₀ > 0, ∃ ρ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∃ Cε ≥ 0, ∃ CB ≥ 0, ∃ CW ≥ 0,
    ∀ (Q₀ Kr : C(T3, MetricRec)) (Qd Kd : Fin 3 → C(T3, MetricRec))
      (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      DsData s Q₀ Kr Qd Kd Qdd → dataSize s Q₀ Kr ≤ ε → ε ≤ εs →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
      ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd' Vd' : ℝ → Fin 3 → C(T3, MetricRec))
        (Qdd' : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
        (∀ t ∈ Set.Icc 0 T, IsContJet (Q t) (V t) (Qd' t) (Vd' t) (Qdd' t) ∧
          (∀ y (κ : Upper), normalRow (Q t y) (V t y) (A t y) (fun i => Qd' t i y)
            (fun i => Vd' t i y) (fun i j => Qdd' t i j y) κ.1.1 κ.1.2 = 0) ∧
          ∀ y μ ν, einstein (minkowski + Q t y) (recInv (minkowski + Q t y))
            (metricJet (V t y, fun i => Qd' t i y))
            (ddArr (A t y) (fun i => Vd' t i y) (fun i j => Qdd' t i j y)) μ ν = 0) ∧
        ∀ (b : ℕ → ℝ) (B : ℕ → Upper → Upper → ℝ), (∀ n, IsMark (b n) (B n)) →
          (∀ n, b n ≤ 1 / 48) → ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
          ∀ (W : ∀ m : ℕ, LawWord (φ m + 1)) (cm cp εw : ℝ) (m₀ : ℕ),
          (∀ m, m₀ ≤ m → 1 ≤ φ m) →
          (∀ m, (W m).IsChronological ((φ m : ℝ) + 1)⁻¹ cm cp T) →
          (∀ m, (W m).path 0 0 = sampleRec (φ m + 1) ⇑Q₀ ∧
            (W m).path 1 0 = sampleRec (φ m + 1) ⇑V₀) →
          0 < εw → εw ≤ εw₀ → (∀ m, (W m).recNorm s 0 ≤ εw) →
          (∀ m, m₀ ≤ m → (W m).cost (B (φ m)) s ρ εw T ≤ ((φ m : ℝ) + 1)⁻¹ ^ 2) →
          (∀ m, m₀ ≤ m → (W m).fail = none ∧ ∀ t ∈ Set.Icc 0 T, (W m).recNorm s t < ρ) ∧
          ∀ t ∈ Set.Icc 0 T,
            Tendsto (fun m => interpRec ((W m).path 0 t)) atTop (𝓝 (Q t)) ∧
            Tendsto (fun m => interpRec ((W m).path 1 t)) atTop (𝓝 (V t)) ∧
            Tendsto (fun m => interpRec ((W m).path 2 t)) atTop (𝓝 (A t)) ∧
            ∀ m, m₀ ≤ m → ∀ κ : Upper,
              sn (s - 1) ⇑(cmp (interpRec ((W m).path 0 t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ≤
                ((C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε + CW * εw) * ((φ m : ℝ) + 1)⁻¹ ∧
              sn (s - 2) ⇑(cmp (interpRec ((W m).path 1 t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ≤
                ((C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε + CW * εw) * ((φ m : ℝ) + 1)⁻¹ ∧
              sn (s - 3) ⇑(cmp (interpRec ((W m).path 2 t)) κ.1.1 κ.1.2 - cmp (A t) κ.1.1 κ.1.2) ≤
                ((C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε + CW * εw) * ((φ m : ℝ) + 1)⁻¹ := by
  obtain ⟨εs, hεs, Te, hTe, TB, hTB, K, hK, C, hC, Cε, hCε, CB, hCB, hLE⟩ := supp_law_einstein s hs
  obtain ⟨εc, hεc, Tc, hTc, ρ, hρ, hcc⟩ := law_cost_control s (by omega)
  set T := min Te Tc
  have hT : 0 < T := lt_min hTe hTc
  have hTe' : T ≤ Te := min_le_left _ _
  have hTc' : T ≤ Tc := min_le_right _ _
  obtain ⟨CW0, hCW0, hcc'⟩ := hcc T hT hTc'
  set Sq : ℝ := Real.sqrt (pc (s - 1)) + Real.sqrt (pc (s - 2)) + Real.sqrt (pc (s - 3)) +
    Real.sqrt (pc 2) + 1
  have hSq : ∀ r ∈ ({s - 1, s - 2, s - 3, 2} : Finset ℕ), Real.sqrt (pc r) ≤ Sq := by
    intro r hr
    have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
    have := Real.sqrt_nonneg (pc (s - 3)); have := Real.sqrt_nonneg (pc 2)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [Sq] <;> linarith
  refine ⟨εs, hεs, T, hT, εc, hεc, ρ, hρ, K, hK, C, hC, Cε, hCε, CB, hCB, CW0 * Sq,
    by positivity, fun Q₀ Kr Qd Kd Qdd ε hD hsz hεs' => ?_⟩
  obtain ⟨V₀, hV₀, q, v, -, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, hcen, hfam⟩ :=
    hLE Q₀ Kr Qd Kd Qdd ε hD hsz hεs'
  have hε0 : 0 ≤ ε := (add_nonneg (ccoordSum_nonneg _ _ _) (ccoordSum_nonneg _ _ _)).trans hsz
  refine ⟨V₀, hV₀, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, fun t ht => ?_,
    fun b B hB hb φ hφ W cm cp εw m₀ hφ1 hW hW0 hεw hεw₀ hrec hcost => ?_⟩
  · obtain ⟨-, -, -, h8, h9, -, h13⟩ := hcen t ⟨ht.1, ht.2.trans hTe'⟩
    exact ⟨h8, h9, h13⟩
  obtain ⟨qB, vB, hsolB, huB, -, -, hconv⟩ := hfam b B hB hb
  -- the cost lemma at `d = h`
  have hcm : ∀ m, m₀ ≤ m → (W m).fail = none ∧ (∀ t ∈ Set.Icc 0 T, (W m).recNorm s t < ρ) ∧
      ∀ t ∈ Set.Icc 0 T, Xnorm (s - 1) ((W m).path 0 t - qB (φ m) t) ((W m).path 1 t - vB (φ m) t) +
        Fnorm (s - 3) ((W m).path 2 t - lawAccel (B (φ m)) (qB (φ m) t) (vB (φ m) t)) ≤
        CW0 * εw * ((φ m : ℝ) + 1)⁻¹ := by
    intro m hm
    have e : (((φ m + 1 : ℕ) : ℝ))⁻¹ = ((φ m : ℝ) + 1)⁻¹ := by rw [Nat.cast_succ]
    have hchr : (W m).IsChronological (((φ m + 1 : ℕ) : ℝ))⁻¹ cm cp T := by rw [e]; exact hW m
    have hh : ((φ m : ℝ) + 1)⁻¹ ≤ 1 / 2 := by
      have : (2 : ℝ) ≤ (φ m : ℝ) + 1 := by
        have := hφ1 m hm
        have : (1 : ℝ) ≤ (φ m : ℝ) := by exact_mod_cast this
        linarith
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) this
    obtain ⟨hfail, hguard, -, qc, vc, hqc0, hvc0, hsolc, huc, hsh⟩ := hcc' (φ m + 1) (B (φ m))
      ((hB (φ m)).mono (hb (φ m))) (W m) cm cp hchr εw hεw hεw₀ (hrec m) ((φ m : ℝ) + 1)⁻¹
      (by positivity) hh (hcost m hm)
    refine ⟨hfail, hguard, fun t ht => ?_⟩
    have heq : qc t = qB (φ m) t ∧ vc t = vB (φ m) t := by
      rcases le_total TB Tc with h | h
      · exact huB (φ m) qc vc (hqc0.trans (hW0 m).1) (hvc0.trans (hW0 m).2)
          (isAccSolution_mono_T hsolc h) t ⟨ht.1, (ht.2.trans hTe').trans hTB⟩
      · have := huc (qB (φ m)) (vB (φ m)) ((hsolB (φ m)).2.1.trans (hW0 m).1.symm)
          ((hsolB (φ m)).2.2.trans (hW0 m).2.symm) (isAccSolution_mono_T (hsolB (φ m)).1 h) t
          ⟨ht.1, ht.2.trans hTc'⟩
        exact ⟨this.1.symm, this.2.symm⟩
    rw [← heq.1, ← heq.2]
    exact hsh t ht
  refine ⟨fun m hm => ⟨(hcm m hm).1, (hcm m hm).2.1⟩, fun t ht => ?_⟩
  have htB : t ∈ Set.Icc 0 TB := ⟨ht.1, (ht.2.trans hTe').trans hTB⟩
  obtain ⟨c1, c2, c3, -, -, -, crates⟩ := hconv t ⟨ht.1, ht.2.trans hTe'⟩
  have hsP : ∀ m k, IsSymRec ((W m).path k t) := fun m k =>
    LawWord.isSymRec_path (W m) (hW m).2.2.2.2.2.2.1 k t
  have hsqB : ∀ n, IsSymRec (qB n t) := fun n => ((hsolB n).1 t htB).1
  have hsvB : ∀ n, IsSymRec (vB n t) := fun n => ((hsolB n).1 t htB).2.1
  set D : ℝ := CW0 * εw
  have hD0 : 0 ≤ D := by positivity
  have gq : ∀ m, m₀ ≤ m → ∀ (κ : Upper) (r : ℕ), r ≤ s →
      PeriodicGridSobolev.sobNorm r (cx (comp ((W m).path 0 t - qB (φ m) t) κ.1.1 κ.1.2)) ≤
        D * ((φ m : ℝ) + 1)⁻¹ := fun m hm κ r hr => by
    have h1 := sobNorm_q_le (s - 1) (isSymRec_sub (hsP m 0) (hsqB (φ m)))
      ((W m).path 1 t - vB (φ m) t) κ.1.1 κ.1.2 (r := r) (by omega)
    have h2 := (hcm m hm).2.2 t ht
    have h3 := Fnorm_nonneg (s - 3) ((W m).path 2 t - lawAccel (B (φ m)) (qB (φ m) t) (vB (φ m) t))
    linarith
  have gv : ∀ m, m₀ ≤ m → ∀ (κ : Upper) (r : ℕ), r ≤ s - 1 →
      PeriodicGridSobolev.sobNorm r (cx (comp ((W m).path 1 t - vB (φ m) t) κ.1.1 κ.1.2)) ≤
        D * ((φ m : ℝ) + 1)⁻¹ := fun m hm κ r hr => by
    have h1 := sobNorm_v_le (s - 1) ((W m).path 0 t - qB (φ m) t)
      (isSymRec_sub (hsP m 1) (hsvB (φ m))) κ.1.1 κ.1.2 hr
    have h2 := (hcm m hm).2.2 t ht
    have h3 := Fnorm_nonneg (s - 3) ((W m).path 2 t - lawAccel (B (φ m)) (qB (φ m) t) (vB (φ m) t))
    linarith
  have ga : ∀ m, m₀ ≤ m → ∀ (κ : Upper) (r : ℕ), r ≤ s - 3 →
      PeriodicGridSobolev.sobNorm r (cx (comp ((W m).path 2 t -
        lawAccel (B (φ m)) (qB (φ m) t) (vB (φ m) t)) κ.1.1 κ.1.2)) ≤
        D * ((φ m : ℝ) + 1)⁻¹ := fun m hm κ r hr => by
    have h1 := (PeriodicGridSobolev.Moser.sobNorm_mono hr _).trans
      (sobNorm_le_Fnorm (s - 3) ((W m).path 2 t - lawAccel (B (φ m)) (qB (φ m) t) (vB (φ m) t)) κ)
    have h2 := (hcm m hm).2.2 t ht
    have h3 := Xnorm_nonneg (s - 1) ((W m).path 0 t - qB (φ m) t) ((W m).path 1 t - vB (φ m) t)
    linarith
  have mulD : ∀ (r : ℕ) (m : ℕ) (x : ℝ), x ≤ D * ((φ m : ℝ) + 1)⁻¹ →
      Real.sqrt (pc r) * x ≤ Real.sqrt (pc r) * D * ((φ m : ℝ) + 1)⁻¹ := fun r m x hx => by
    calc Real.sqrt (pc r) * x ≤ Real.sqrt (pc r) * (D * ((φ m : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg (pc r))
      _ = _ := by ring
  have hrate : ∀ c : ℝ, Tendsto (fun m => c * ((φ m : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    intro c
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ
    simp only [one_div, Function.comp_def] at this
    simpa using this.const_mul c
  refine ⟨?_, ?_, ?_, fun m hm κ => ⟨?_, ?_, ?_⟩⟩
  · refine lawLimit_tendsto_of_upper_rate (c1.comp hφ)
      (fun m y μ ν => interpRec_symm (hsP m 0) y μ ν)
      (fun m y μ ν => interpRec_symm (hsqB (φ m)) y μ ν) _ (hrate (Real.sqrt (pc 2) * D)) m₀
      fun m hm κ => ?_
    have h := lawLimit_interp_diff 2 ((W m).path 0 t) (qB (φ m) t) κ.1.1 κ.1.2
    exact ⟨h.1, h.2.trans (mulD 2 m _ (gq m hm κ 2 (by omega)))⟩
  · refine lawLimit_tendsto_of_upper_rate (c2.comp hφ)
      (fun m y μ ν => interpRec_symm (hsP m 1) y μ ν)
      (fun m y μ ν => interpRec_symm (hsvB (φ m)) y μ ν) _ (hrate (Real.sqrt (pc 2) * D)) m₀
      fun m hm κ => ?_
    have h := lawLimit_interp_diff 2 ((W m).path 1 t) (vB (φ m) t) κ.1.1 κ.1.2
    exact ⟨h.1, h.2.trans (mulD 2 m _ (gv m hm κ 2 (by omega)))⟩
  · refine lawLimit_tendsto_of_upper_rate (c3.comp hφ)
      (fun m y μ ν => interpRec_symm (hsP m 2) y μ ν)
      (fun m y μ ν => interpRec_symRec_symm _ y μ ν) _ (hrate (Real.sqrt (pc 2) * D)) m₀
      fun m hm κ => ?_
    show MemH 2 ⇑(cmp (interpRec ((W m).path 2 t)) κ.1.1 κ.1.2 -
        cmp (interpRec (symRec (lawAccel (B (φ m)) (qB (φ m) t) (vB (φ m) t)))) κ.1.1 κ.1.2) ∧
      sn 2 ⇑(cmp (interpRec ((W m).path 2 t)) κ.1.1 κ.1.2 -
        cmp (interpRec (symRec (lawAccel (B (φ m)) (qB (φ m) t) (vB (φ m) t)))) κ.1.1 κ.1.2) ≤
        Real.sqrt (pc 2) * D * ((φ m : ℝ) + 1)⁻¹
    rw [cmp_interpRec_symRec]
    have h := lawLimit_interp_diff 2 ((W m).path 2 t)
      (lawAccel (B (φ m)) (qB (φ m) t) (vB (φ m) t)) κ.1.1 κ.1.2
    exact ⟨h.1, h.2.trans (mulD 2 m _ (ga m hm κ 2 (by omega)))⟩
  all_goals
    have hn : (0 : ℝ) ≤ ((φ m : ℝ) + 1)⁻¹ := by positivity
    have e2 : ((C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε + CW0 * Sq * εw) *
        ((φ m : ℝ) + 1)⁻¹ = (C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε * ((φ m : ℝ) + 1)⁻¹ +
          Sq * D * ((φ m : ℝ) + 1)⁻¹ := by simp only [D]; ring
    rw [e2]
  · have e : cmp (interpRec ((W m).path 0 t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2 =
        (cmp (interpRec (qB (φ m) t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) +
        (cmp (interpRec ((W m).path 0 t)) κ.1.1 κ.1.2 - cmp (interpRec (qB (φ m) t)) κ.1.1 κ.1.2) := by
      abel
    rw [e]
    have h := lawLimit_interp_diff (s - 1) ((W m).path 0 t) (qB (φ m) t) κ.1.1 κ.1.2
    refine (lawLimit_sn_add_le _ _ h.1).trans ?_
    have r1 := (crates (φ m) κ).1
    have r2 := h.2.trans (mulD (s - 1) m _ (gq m hm κ (s - 1) (by omega)))
    have r3 : Real.sqrt (pc (s - 1)) * D * ((φ m : ℝ) + 1)⁻¹ ≤ Sq * D * ((φ m : ℝ) + 1)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hSq _ (by simp)) hD0) hn
    linarith
  · have e : cmp (interpRec ((W m).path 1 t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2 =
        (cmp (interpRec (vB (φ m) t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) +
        (cmp (interpRec ((W m).path 1 t)) κ.1.1 κ.1.2 - cmp (interpRec (vB (φ m) t)) κ.1.1 κ.1.2) := by
      abel
    rw [e]
    have h := lawLimit_interp_diff (s - 2) ((W m).path 1 t) (vB (φ m) t) κ.1.1 κ.1.2
    refine (lawLimit_sn_add_le _ _ h.1).trans ?_
    have r1 := (crates (φ m) κ).2.1
    have r2 := h.2.trans (mulD (s - 2) m _ (gv m hm κ (s - 2) (by omega)))
    have r3 : Real.sqrt (pc (s - 2)) * D * ((φ m : ℝ) + 1)⁻¹ ≤ Sq * D * ((φ m : ℝ) + 1)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hSq _ (by simp)) hD0) hn
    linarith
  · have e : cmp (interpRec ((W m).path 2 t)) κ.1.1 κ.1.2 - cmp (A t) κ.1.1 κ.1.2 =
        (cmp (interpRec (lawAccel (B (φ m)) (qB (φ m) t) (vB (φ m) t))) κ.1.1 κ.1.2 -
          cmp (A t) κ.1.1 κ.1.2) +
        (cmp (interpRec ((W m).path 2 t)) κ.1.1 κ.1.2 -
          cmp (interpRec (lawAccel (B (φ m)) (qB (φ m) t) (vB (φ m) t))) κ.1.1 κ.1.2) := by
      abel
    rw [e]
    have h := lawLimit_interp_diff (s - 3) ((W m).path 2 t)
      (lawAccel (B (φ m)) (qB (φ m) t) (vB (φ m) t)) κ.1.1 κ.1.2
    refine (lawLimit_sn_add_le _ _ h.1).trans ?_
    have r1 := (crates (φ m) κ).2.2
    have r2 := h.2.trans (mulD (s - 3) m _ (ga m hm κ (s - 3) le_rfl))
    have r3 : Real.sqrt (pc (s - 3)) * D * ((φ m : ℝ) + 1)⁻¹ ≤ Sq * D * ((φ m : ℝ) + 1)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hSq _ (by simp)) hD0) hn
    linarith

/-- **Almost-sure form of the Einstein clause of `thm:supp-law-row-neighbourhood`** along the odd
cutoffs `N = 2m + 1`: if random chronological words (under any common coupling `μ`, no
independence between cutoffs) have exceptional probabilities
`μ{C_h > h²} ≤ K h²` (`eq:supp-law-row-probability`, proved from the row moment condition by
`ChronologicalRow.WordProcess.prob_cost_gt_le`), then almost surely the interpolated word records
converge on `[0, T]` to the vacuum development of `supp_law_einstein` (first Borel–Cantelli lemma,
`ChronologicalRow.odd_cutoff_eventually_not_exceptional`, plus `supp_law_row_einstein`). -/
theorem supp_law_row_einstein_ae (s : ℕ) (hs : 6 ≤ s) :
    ∃ εs > 0, ∃ T > 0, ∃ εw₀ > 0, ∃ ρ > 0,
    ∀ (Q₀ Kr : C(T3, MetricRec)) (Qd Kd : Fin 3 → C(T3, MetricRec))
      (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      DsData s Q₀ Kr Qd Kd Qdd → dataSize s Q₀ Kr ≤ ε → ε ≤ εs →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
      ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd' Vd' : ℝ → Fin 3 → C(T3, MetricRec))
        (Qdd' : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
        (∀ t ∈ Set.Icc 0 T, ∀ y μ ν, einstein (minkowski + Q t y) (recInv (minkowski + Q t y))
            (metricJet (V t y, fun i => Qd' t i y))
            (ddArr (A t y) (fun i => Vd' t i y) (fun i j => Qdd' t i j y)) μ ν = 0) ∧
        ∀ (b : ℕ → ℝ) (B : ℕ → Upper → Upper → ℝ), (∀ n, IsMark (b n) (B n)) →
          (∀ n, b n ≤ 1 / 48) →
          ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
            (W : Ω → ∀ m : ℕ, LawWord (2 * m + 1)) (cm cp εw Kc : ℝ), 0 ≤ Kc →
          (∀ ω m, (W ω m).IsChronological (((2 * m : ℕ) : ℝ) + 1)⁻¹ cm cp T) →
          (∀ ω m, (W ω m).path 0 0 = sampleRec (2 * m + 1) ⇑Q₀ ∧
            (W ω m).path 1 0 = sampleRec (2 * m + 1) ⇑V₀) →
          0 < εw → εw ≤ εw₀ → (∀ ω m, (W ω m).recNorm s 0 ≤ εw) →
          (∀ m : ℕ, P {ω | (((2 * m : ℕ) : ℝ) + 1)⁻¹ ^ 2 < (W ω m).cost (B (2 * m)) s ρ εw T} ≤
            ENNReal.ofReal (Kc / (2 * (m : ℝ) + 1) ^ 2)) →
          ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T,
            Tendsto (fun m => interpRec ((W ω m).path 0 t)) atTop (𝓝 (Q t)) ∧
            Tendsto (fun m => interpRec ((W ω m).path 1 t)) atTop (𝓝 (V t)) ∧
            Tendsto (fun m => interpRec ((W ω m).path 2 t)) atTop (𝓝 (A t)) := by
  obtain ⟨εs, hεs, T, hT, εw₀, hεw₀, ρ, hρ, K, -, C, -, Cε, -, CB, -, CW, -, hR⟩ :=
    supp_law_row_einstein s hs
  refine ⟨εs, hεs, T, hT, εw₀, hεw₀, ρ, hρ, fun Q₀ Kr Qd Kd Qdd ε hD hsz hε => ?_⟩
  obtain ⟨V₀, hV₀, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, hvac, hfam⟩ := hR Q₀ Kr Qd Kd Qdd ε hD hsz hε
  refine ⟨V₀, hV₀, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, fun t ht => (hvac t ht).2.2,
    fun b B hB hb Ω _ P W cm cp εw Kc hKc hW hW0 hεw hεw' hrec hP => ?_⟩
  have hae := ChronologicalRow.odd_cutoff_eventually_not_exceptional P
    (fun m => {ω | (((2 * m : ℕ) : ℝ) + 1)⁻¹ ^ 2 < (W ω m).cost (B (2 * m)) s ρ εw T}) Kc hKc hP
  filter_upwards [hae] with ω hω
  obtain ⟨m₁, hm₁⟩ := eventually_atTop.1 hω
  have hφ : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_atTop.2 fun c => ⟨c, fun a ha => by omega⟩
  have h := hfam b B hB hb (fun m => 2 * m) hφ (W ω) cm cp εw (max m₁ 1)
    (fun m hm => by have := le_of_max_le_right hm; omega) (hW ω) (hW0 ω) hεw hεw' (hrec ω)
    (fun m hm => not_lt.1 (hm₁ m (le_of_max_le_left hm)))
  exact fun t ht => ⟨(h.2 t ht).1, (h.2 t ht).2.1, (h.2 t ht).2.2.1⟩

/-- Non-vacuity of `supp_law_einstein`: the flat data `(γ, K) = (I, 0)` (`dsData_zero`) lie in
the data class and produce, for the constant mark sequence `B_n = 0`, law-family histories. -/
example (s : ℕ) (hs : 6 ≤ s) : True := by
  obtain ⟨εs, hεs, T, hT, TB, hTB, K, hK, C, hC, Cε, hCε, CB, hCB, h⟩ := supp_law_einstein s hs
  have hsz : dataSize s (0 : C(T3, MetricRec)) 0 ≤ εs := by
    have e : dataSize s (0 : C(T3, MetricRec)) 0 = 0 := contTop_zero s
    rw [e]; exact hεs.le
  obtain ⟨V₀, _, q, v, _, Q, V, A, Qd1, Vd1, Qdd1, _, _, _, hfam⟩ :=
    h 0 0 (fun _ => 0) (fun _ => 0) (fun _ _ => 0) εs (dsData_zero s) hsz le_rfl
  obtain ⟨qB, vB, -⟩ := hfam (fun _ => 1 / 48) (fun _ _ _ => 0) (fun _ => isMark_zero)
    (fun _ => le_rfl)
  trivial

end

end RenewalGeometry.OpenWriterLimitRegularity
