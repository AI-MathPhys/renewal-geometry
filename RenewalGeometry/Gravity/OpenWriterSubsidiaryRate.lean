/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterHarmonicPreparation

/-!
# Subsidiary bounds for the interpolated open writer
  (`lem:supp-open-subsidiary`, `lem:supp-open-initial-gauge`; emergent-spacetime manuscript)

Pointwise metric-jet functionals on the space-time 2-jet space `PJet`:

* `pjJet z` — the metric 2-jet of `g = η + z.1` (inverse at type `Matrix`);
* `gaugeOf z b` — the lower-index gauge covector `c_b(g) = g_{bμ} g^{αβ} Γ^μ_{αβ}`
  (`eq:supp-open-reduced-residual`), depending on the 1-jet only (`gaugeOf_trunc`);
* `dtGaugeOf z b` — its time derivative `∂ₜc_b` (chain rule through the 2-jet);
* `einOf z μ ν` — the Einstein tensor `G_{μν}(g)`.

All three are analytic at the flat jet (`analyticAt_gaugeOf`, `analyticAt_dtGaugeOf`,
`analyticAt_einOf`), so the Lipschitz continuum Moser estimate applies to them
(`pjet_moser_fin`).
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.OpenWriterSubsidiary

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterContinuum HarmonicGaugePropagation ContractedBianchiJet
  PeriodicGridSobolev.Composition OpenWriterGridBridge RootParityConnector HarmonicWriter
  HarmonicDefect OpenWriterLimitRegularity

noncomputable section

set_option linter.unusedSectionVars false

/-! ### The jet functionals -/

/-- The array space `(g, g⁻¹, ∂g, ∂²g)`. -/
abbrev ArrJet := (Fin 4 → Fin 4 → ℝ) × (Fin 4 → Fin 4 → ℝ) × (Fin 4 → Fin 4 → Fin 4 → ℝ) ×
  (Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)

/-- The metric arrays of a pointwise 2-jet: `g = η + z.1`, `g⁻¹` (matrix inverse), `∂g`, `∂²g`. -/
def arrOf (z : PJet) : ArrJet := (minkowski + z.1, recInv (minkowski + z.1), dgOf z, ddgOf z)

/-- The metric 2-jet (`Jet3` with vanishing third jet) of an array. -/
def arrJet (X : ArrJet) : Jet3 (Fin 4) := ofArrays X.1 X.2.1 X.2.2.1 X.2.2.2

/-- The metric 2-jet of `g = η + z.1` with the jet `z`. -/
def pjJet (z : PJet) : Jet3 (Fin 4) := arrJet (arrOf z)

/-- **The gauge covector** `c_b(g) = g_{bμ} g^{αβ} Γ^μ_{αβ}` of the jet `z`. -/
def gaugeOf (z : PJet) (b : Fin 4) : ℝ := (pjJet z).gc b

/-- **Its time derivative** `∂ₜ c_b(g)` (chain rule; uses the 2-jet). -/
def dtGaugeOf (z : PJet) (b : Fin 4) : ℝ := (pjJet z).dgc 0 b

/-- **The Einstein tensor** `G_{μν}(g) = R_{μν} - ½ g_{μν} R` of the jet `z`. -/
def einOf (z : PJet) (μ ν : Fin 4) : ℝ := (pjJet z).einM μ ν

theorem analyticAt_arrOf (z₀ : PJet) (hdet : (Matrix.of (minkowski + z₀.1)).det ≠ 0) :
    AnalyticAt ℝ arrOf z₀ := by
  have hg : AnalyticAt ℝ (fun z : PJet => minkowski + z.1) z₀ := by fun_prop
  have hinv : AnalyticAt ℝ (fun z : PJet => recInv (minkowski + z.1)) z₀ := by
    refine AnalyticAt.pi fun i => AnalyticAt.pi fun j => ?_
    exact (analyticAt_inv_entry _ hdet i j).comp_of_eq hg rfl
  have hdg : AnalyticAt ℝ (fun z : PJet => dgOf z) z₀ := by
    refine AnalyticAt.pi fun α => ?_
    refine Fin.cases ?_ (fun i => ?_) α
    · simp only [dgOf, Fin.cons_zero]; fun_prop
    · simp only [dgOf, Fin.cons_succ]; fun_prop
  have hddg : AnalyticAt ℝ (fun z : PJet => ddgOf z) z₀ := by
    refine AnalyticAt.pi fun α => ?_
    refine Fin.cases ?_ (fun i => ?_) α
    · refine AnalyticAt.pi fun β => ?_
      refine Fin.cases ?_ (fun j => ?_) β
      · simp only [ddgOf, Fin.cons_zero]; fun_prop
      · simp only [ddgOf, Fin.cons_zero, Fin.cons_succ]; fun_prop
    · refine AnalyticAt.pi fun β => ?_
      refine Fin.cases ?_ (fun j => ?_) β
      · simp only [ddgOf, Fin.cons_succ, Fin.cons_zero]; fun_prop
      · simp only [ddgOf, Fin.cons_succ]; fun_prop
  exact hg.prod (hinv.prod (hdg.prod hddg))

theorem analyticAt_arr_gc (b : Fin 4) (X : ArrJet) :
    AnalyticAt ℝ (fun X : ArrJet => (arrJet X).gc b) X := by
  simp only [arrJet, ofArrays, Jet3.gc, Jet3.gcUp, Jet3.chr, Jet3.low, Matrix.mul_apply,
    Matrix.of_apply]
  fun_prop

theorem analyticAt_arr_dgc (b : Fin 4) (X : ArrJet) :
    AnalyticAt ℝ (fun X : ArrJet => (arrJet X).dgc 0 b) X := by
  simp only [arrJet, ofArrays, Jet3.dgc, Jet3.gcUp, Jet3.dgcUp, Jet3.dG, Jet3.chr, Jet3.dchr,
    Jet3.low, Jet3.dlow, Matrix.mul_apply, Matrix.of_apply, Matrix.neg_apply, Matrix.sub_apply]
  fun_prop

theorem analyticAt_arr_einM (μ ν : Fin 4) (X : ArrJet) :
    AnalyticAt ℝ (fun X : ArrJet => (arrJet X).einM μ ν) X := by
  simp only [arrJet, ofArrays, Jet3.einM, Jet3.scal, Jet3.ricM, Jet3.riem, Jet3.chr, Jet3.dchr,
    Jet3.low, Jet3.dlow, Matrix.mul_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.trace, Matrix.diag, Matrix.transpose_apply, smul_eq_mul]
  fun_prop

theorem det_minkowski_add_zero : (Matrix.of (minkowski + (0 : PJet).1)).det ≠ 0 := by
  simpa using det_minkowski_ne

theorem analyticAt_gaugeOf (b : Fin 4) : AnalyticAt ℝ (fun z => gaugeOf z b) 0 :=
  (analyticAt_arr_gc b _).comp (analyticAt_arrOf 0 det_minkowski_add_zero)

theorem analyticAt_dtGaugeOf (b : Fin 4) : AnalyticAt ℝ (fun z => dtGaugeOf z b) 0 :=
  (analyticAt_arr_dgc b _).comp (analyticAt_arrOf 0 det_minkowski_add_zero)

theorem analyticAt_einOf (μ ν : Fin 4) : AnalyticAt ℝ (fun z => einOf z μ ν) 0 :=
  (analyticAt_arr_einM μ ν _).comp (analyticAt_arrOf 0 det_minkowski_add_zero)

/-- The truncation of a jet to its 1-jet `(q, v, ∂q)`. -/
def trunc (z : PJet) : PJet := (z.1, z.2.1, 0, z.2.2.2.1, 0, 0)

/-- **The gauge covector depends on the 1-jet only.** -/
theorem gaugeOf_trunc (z : PJet) (b : Fin 4) : gaugeOf (trunc z) b = gaugeOf z b := by
  simp only [gaugeOf, pjJet, arrJet, arrOf, ofArrays, trunc, Jet3.gc, Jet3.gcUp, Jet3.chr,
    Jet3.low]
  rfl

/-! ### The Lipschitz Moser estimate for jet functionals -/

/-- **Lipschitz continuum Moser estimate for a finite family of jet functionals** analytic at the
flat jet: on a small `H^r` ball of jet fields (`r ≥ 2`),
`‖Φᵢ(P) - Φᵢ(P')‖_{H^r} ≤ C Σ_j ‖P_j - P'_j‖_{H^r}`, uniformly in `i`. -/
theorem pjet_moser_fin {ι : Type*} [Fintype ι] [Nonempty ι] (r : ℕ) (hr : 2 ≤ r)
    (Φ : ι → PJet → ℝ) (hΦ : ∀ i, AnalyticAt ℝ (Φ i) 0) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (i : ι) (P P' : C(T3, PJet)), (∀ j, MemH r ⇑(ccoord bPJ P j)) →
      (∀ j, MemH r ⇑(ccoord bPJ P' j)) → ccoordSum r bPJ P ≤ δ → ccoordSum r bPJ P' ≤ δ →
      ∃ F : CT, (∀ y, F y = ((Φ i (P y) - Φ i (P' y) : ℝ) : ℂ)) ∧ MemH r ⇑F ∧
        sn r ⇑F ≤ C * ccoordSum r bPJ (P - P') := by
  have h : ∀ i, ∃ δ > 0, ∃ C ≥ 0, ∀ P P' : C(T3, PJet), (∀ j, MemH r ⇑(ccoord bPJ P j)) →
      (∀ j, MemH r ⇑(ccoord bPJ P' j)) → ccoordSum r bPJ P ≤ δ → ccoordSum r bPJ P' ≤ δ →
      ∃ F : CT, (∀ y, F y = ((Φ i (P y) - Φ i (P' y) : ℝ) : ℂ)) ∧ MemH r ⇑F ∧
        sn r ⇑F ≤ C * ccoordSum r bPJ (P - P') := by
    intro i
    obtain ⟨p, R, hp⟩ := hΦ i
    obtain ⟨δ, hδ, C, hC, hm⟩ := cont_moser_lipschitz r hr bPJ hp
    refine ⟨δ, hδ, C, hC, fun P P' hP hP' h1 h2 => ?_⟩
    obtain ⟨F, hF, hFm, hFs⟩ := hm P P' hP hP' h1 h2
    exact ⟨F, fun y => by rw [hF y]; simp, hFm, hFs⟩
  choose δf hδf Cf hCf hm using h
  set δ0 : ℝ := (univ : Finset ι).inf' univ_nonempty δf
  have hδ0 : 0 < δ0 := by rw [Finset.lt_inf'_iff]; intro i _; exact hδf i
  have hδ0le : ∀ i, δ0 ≤ δf i := fun i => Finset.inf'_le _ (mem_univ i)
  set C0 : ℝ := ∑ i, Cf i
  have hC0 : ∀ i, Cf i ≤ C0 := fun i => single_le_sum (f := Cf) (fun i _ => hCf i) (mem_univ i)
  have hC0n : 0 ≤ C0 := sum_nonneg fun i _ => hCf i
  refine ⟨δ0, hδ0, C0, hC0n, fun i P P' hP hP' h1 h2 => ?_⟩
  obtain ⟨F, hF, hFm, hFs⟩ := hm i P P' hP hP' (h1.trans (hδ0le i)) (h2.trans (hδ0le i))
  exact ⟨F, hF, hFm, hFs.trans (mul_le_mul_of_nonneg_right (hC0 i) (ccoordSum_nonneg _ _ _))⟩

/-! ### Jet fields of the interpolated writer and of the limit -/

section Jets

variable {N : ℕ} [NeZero N]

/-- The space-time 2-jet field of the interpolant `g_h = η + 𝓘_h q`:
`(𝓘_h q, 𝓘_h v, 𝓘_h ∂ₜv, ∂ᵢ𝓘_h q, ∂ᵢ𝓘_h v, ∂ᵢ∂ⱼ𝓘_h q)` (`∂ₜv` the actual finite acceleration). -/
def interpJet (q v : Grid N → MetricRec) : C(T3, PJet) :=
  pjetField (interpRec q) (interpRec v) (interpRec (symRec (harmonicWriterAcceleration q v)))
    (interpD q) (interpD v) (interpDD q)

/-- The 1-jet field `(𝓘_h q, 𝓘_h v, 0, ∂ᵢ𝓘_h q, 0, 0)` of the interpolant. -/
def interpJet1 (q v : Grid N → MetricRec) : C(T3, PJet) :=
  pjetField (interpRec q) (interpRec v) 0 (interpD q) 0 0

theorem interpJet1_apply (q v : Grid N → MetricRec) (y : T3) :
    interpJet1 q v y = trunc (interpJet q v y) := rfl

end Jets

theorem sn_zero_CT (r : ℕ) : sn r ⇑(0 : CT) = 0 := by
  simp [sn, PeriodicGridSobolev.trigSobSq, mFourierCoeff]

theorem ccoordSum_zero_rec (r : ℕ) : ccoordSum r bM (0 : C(T3, MetricRec)) = 0 := by
  unfold ccoordSum
  simp only [ccoord_zero, sn_zero_CT, Finset.sum_const_zero]

theorem memH_ccoord_zero_rec (r : ℕ) (k : Σ _ : Fin 4, Fin 4) :
    MemH r ⇑(ccoord bM (0 : C(T3, MetricRec)) k) := by
  rw [ccoord_zero]; exact memH_zero r

set_option maxHeartbeats 4000000 in
/-- **Rates of the interpolant jet fields** (from `writer_limit_solves`): along writer histories in
the top ball of size `ε ≤ δ`, the interpolant 2-jet fields have `H^{s-3}` size `≤ S ε`, the limit
2-jet field likewise, and their difference is `O(h ε)` in `H^{s-3}`; the 1-jet fields have the same
properties at the order `s - 2`. -/
theorem writer_jet_rates (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∃ S ≥ 0, ∀ (T : ℝ) (q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec)
      (Q₀ V₀ : C(T3, MetricRec)) (ε : ℝ),
      (∀ n, IsWriterSolution T (q n) (v n)) →
      (∀ n, q n 0 = sampleRec (n + 1) ⇑Q₀) → (∀ n, v n 0 = sampleRec (n + 1) ⇑V₀) →
      (∀ y μ ν, Q₀ y μ ν = Q₀ y ν μ) → (∀ y μ ν, V₀ y μ ν = V₀ y ν μ) →
      (∀ k, MemH (s + 1) ⇑(ccoord bM Q₀ k)) → (∀ k, MemH s ⇑(ccoord bM V₀ k)) →
      contTop s Q₀ V₀ ≤ ε → (∀ n, ∀ t ∈ Set.Icc 0 T, Xnorm s (q n t) (v n t) ≤ ε) → ε ≤ δ →
      ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd Vd : ℝ → Fin 3 → C(T3, MetricRec))
        (Qdd : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
        ∀ t ∈ Set.Icc 0 T,
          Tendsto (fun n => interpRec (q n t)) atTop (𝓝 (Q t)) ∧
          Tendsto (fun n => interpRec (v n t)) atTop (𝓝 (V t)) ∧
          Tendsto (fun n => interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t)))) atTop
            (𝓝 (A t)) ∧
          IsContJet (Q t) (V t) (Qd t) (Vd t) (Qdd t) ∧
          (∀ j, MemH (s - 3) ⇑(ccoord bPJ (pjetField (Q t) (V t) (A t) (Qd t) (Vd t) (Qdd t)) j)) ∧
          ccoordSum (s - 3) bPJ (pjetField (Q t) (V t) (A t) (Qd t) (Vd t) (Qdd t)) ≤ S * ε ∧
          (∀ j, MemH (s - 2) ⇑(ccoord bPJ (pjetField (Q t) (V t) 0 (Qd t) 0 0) j)) ∧
          ccoordSum (s - 2) bPJ (pjetField (Q t) (V t) 0 (Qd t) 0 0) ≤ S * ε ∧
          ∀ n,
            (∀ j, MemH (s - 3) ⇑(ccoord bPJ (interpJet (q n t) (v n t)) j)) ∧
            ccoordSum (s - 3) bPJ (interpJet (q n t) (v n t)) ≤ S * ε ∧
            ccoordSum (s - 3) bPJ (interpJet (q n t) (v n t) -
              pjetField (Q t) (V t) (A t) (Qd t) (Vd t) (Qdd t)) ≤
                C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ ∧
            (∀ j, MemH (s - 2) ⇑(ccoord bPJ (interpJet1 (q n t) (v n t)) j)) ∧
            ccoordSum (s - 2) bPJ (interpJet1 (q n t) (v n t)) ≤ S * ε ∧
            ccoordSum (s - 2) bPJ (interpJet1 (q n t) (v n t) -
              pjetField (Q t) (V t) 0 (Qd t) 0 0) ≤
                C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨δW, hδW, K₁, hK₁, C₁, hC₁, K₂, hK₂, C₂, hC₂, hW⟩ := writer_limit_solves s hs
  obtain ⟨δA, hδA, KA, hKA, hacc⟩ := accel_bound s (by omega)
  set r := s - 3 with hrdef
  set r2 := s - 2 with hr2def
  set S3 : ℝ := 16 * (Real.sqrt (pc r) * (2 + KA) + 6 * Real.sqrt (pc (r + 1)) +
    9 * Real.sqrt (pc (r + 2)))
  set S2 : ℝ := 16 * (2 * Real.sqrt (pc r2) + 3 * Real.sqrt (pc (r2 + 1)))
  set S : ℝ := S3 + S2
  have hS3 : 0 ≤ S3 := by
    simp only [S3]
    exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (by linarith)) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
  have hS2 : 0 ≤ S2 := by simp only [S2]; positivity
  set K : ℝ := K₁ + K₂
  set C : ℝ := 16 * (3 * C₁ + 15 * C₂)
  have hKnn : 0 ≤ K := add_nonneg hK₁ hK₂
  have hCnn : 0 ≤ C := by simp only [C]; positivity
  refine ⟨min δW δA, lt_min hδW hδA, K, hKnn, C, hCnn, S, add_nonneg hS3 hS2,
    fun T q v Q₀ V₀ ε hsol hq0 hv0 hQs hVs hQ hV hX0 hXq hεδ => ?_⟩
  have hε0 : 0 ≤ ε := (contTop_nonneg _ _ _).trans hX0
  obtain ⟨Q, V, A, Qd, Vd, Qdd, hQ0, hV0, hP⟩ := hW T q v Q₀ V₀ ε hsol hq0 hv0 hQs hVs hQ hV hX0 hXq
    (hεδ.trans (min_le_left _ _))
  refine ⟨Q, V, A, Qd, Vd, Qdd, hQ0, hV0, fun t ht => ?_⟩
  obtain ⟨hQt, hVt, hjet, hrow, hder, hAt, hQdt, hVdt, hQddt, hr1, hrQd, hrVd, hrQdd⟩ := hP t ht
  have hexp1 : Real.exp (K₁ * t) ≤ Real.exp (K * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by simp [K]; linarith) ht.1)
  have hexp2 : Real.exp (K₂ * t) ≤ Real.exp (K * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by simp [K]; linarith) ht.1)
  have hfac0 : ∀ n : ℕ, 0 ≤ (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := fun n =>
    mul_nonneg (mul_nonneg (by linarith [ht.1]) hε0)
      (inv_nonneg.mpr (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  -- symmetries
  have hsq : ∀ n, IsSymRec (q n t) := fun n => (hsol n t ht).1
  have hsv : ∀ n, IsSymRec (v n t) := fun n => (hsol n t ht).2.1
  have hQsym := symm_of_tendsto (fun n y μ ν => interpRec_symm (hsq n) y μ ν) hQt
  have hVsym := symm_of_tendsto (fun n y μ ν => interpRec_symm (hsv n) y μ ν) hVt
  have hAsym := symm_of_tendsto (fun n y μ ν => interpRec_symRec_symm _ y μ ν) hAt
  have hQdsym := fun i => symm_of_tendsto (fun n y μ ν => interpD_symm (hsq n) i y μ ν) (hQdt i)
  have hVdsym := fun i => symm_of_tendsto (fun n y μ ν => interpD_symm (hsv n) i y μ ν) (hVdt i)
  have hQddsym := fun i j => symm_of_tendsto (fun n y μ ν => interpDD_symm (hsq n) i j y μ ν)
    (hQddt i j)
  set Jn : ℕ → C(T3, PJet) := fun n => interpJet (q n t) (v n t)
  set J : C(T3, PJet) := pjetField (Q t) (V t) (A t) (Qd t) (Vd t) (Qdd t)
  set J1n : ℕ → C(T3, PJet) := fun n => interpJet1 (q n t) (v n t)
  set J1 : C(T3, PJet) := pjetField (Q t) (V t) 0 (Qd t) 0 0
  -- derivative-slot bounds for interpolants
  have hderQ : ∀ n i (k : Σ _ : Fin 4, Fin 4) (r' : ℕ), MemH r' ⇑(ccoord bM (interpD (q n t) i) k) ∧
      sn r' ⇑(ccoord bM (interpD (q n t) i) k) ≤ sn (r' + 1) ⇑(ccoord bM (interpRec (q n t)) k) := by
    intro n i k r'
    rw [ccoord_bM, ccoord_bM]
    exact memH_of_isLineDeriv (isLineDeriv_cmp (isLineDeriv_reField i _) k.1 k.2)
      (memH_cmp_reField _ _ _ _).1
  have hderV : ∀ n i (k : Σ _ : Fin 4, Fin 4) (r' : ℕ), MemH r' ⇑(ccoord bM (interpD (v n t) i) k) ∧
      sn r' ⇑(ccoord bM (interpD (v n t) i) k) ≤ sn (r' + 1) ⇑(ccoord bM (interpRec (v n t)) k) := by
    intro n i k r'
    rw [ccoord_bM, ccoord_bM]
    exact memH_of_isLineDeriv (isLineDeriv_cmp (isLineDeriv_reField i _) k.1 k.2)
      (memH_cmp_reField _ _ _ _).1
  have hderQQ : ∀ n i j (k : Σ _ : Fin 4, Fin 4) (r' : ℕ),
      MemH r' ⇑(ccoord bM (interpDD (q n t) i j) k) ∧
      sn r' ⇑(ccoord bM (interpDD (q n t) i j) k) ≤ sn (r' + 1) ⇑(ccoord bM (interpD (q n t) j) k) := by
    intro n i j k r'
    rw [ccoord_bM, ccoord_bM]
    exact memH_of_isLineDeriv (isLineDeriv_cmp (isLineDeriv_reField i _) k.1 k.2)
      (memH_cmp_reField _ _ _ _).1
  have hsum16 : ∀ (f : (Σ _ : Fin 4, Fin 4) → ℝ) (B : ℝ), (∀ k, f k ≤ B) → ∑ k, f k ≤ 16 * B :=
    fun f B h => (sum_le_sum fun k _ => h k).trans (by simp)
  -- sizes of the interpolant jets
  have hJnS : ∀ n, ccoordSum r bPJ (Jn n) ≤ S3 * ε := by
    intro n
    have X := hXq n t ht
    simp only [Jn, interpJet]
    rw [ccoordSum_pjetField]
    have b1 := ccoordSum_interpRec_le r s (hsq n) (v n t) (by omega)
    have b2 := ccoordSum_interpRec_v_le r s (q n t) (hsv n) (by omega)
    have b3 : ccoordSum r bM (interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t)))) ≤
        16 * (Real.sqrt (pc r) * (KA * Xnorm s (q n t) (v n t))) := by
      unfold ccoordSum
      refine hsum16 _ _ fun k => (memH_interpRec r _ k).2.trans
        (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
      rw [comp_symRec_eq]
      exact (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
        (hacc (n + 1) (q n t) (v n t) (hsq n) (hsv n)
          ((hXq n t ht).trans (hεδ.trans (min_le_right _ _))) _ _)
    have b4 : ∀ i, ccoordSum r bM (interpD (q n t) i) ≤
        16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t) := fun i =>
      (sum_le_sum fun k _ => (hderQ n i k r).2).trans
        (ccoordSum_interpRec_le (r + 1) s (hsq n) (v n t) (by omega))
    have b5 : ∀ i, ccoordSum r bM (interpD (v n t) i) ≤
        16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t) := fun i =>
      (sum_le_sum fun k _ => (hderV n i k r).2).trans
        (ccoordSum_interpRec_v_le (r + 1) s (q n t) (hsv n) (by omega))
    have b6 : ∀ i j, ccoordSum r bM (interpDD (q n t) i j) ≤
        16 * Real.sqrt (pc (r + 2)) * Xnorm s (q n t) (v n t) := fun i j =>
      (sum_le_sum fun k _ => (hderQQ n i j k r).2).trans
        ((sum_le_sum fun k _ => (hderQ n j k (r + 1)).2).trans
          (ccoordSum_interpRec_le (r + 2) s (hsq n) (v n t) (by omega)))
    have s4 : ∑ i, ccoordSum r bM (interpD (q n t) i) ≤
        3 * (16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t)) :=
      (sum_le_sum fun i _ => b4 i).trans (by simp)
    have s5 : ∑ i, ccoordSum r bM (interpD (v n t) i) ≤
        3 * (16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t)) :=
      (sum_le_sum fun i _ => b5 i).trans (by simp)
    have s6 : ∑ i, ∑ j, ccoordSum r bM (interpDD (q n t) i j) ≤
        9 * (16 * Real.sqrt (pc (r + 2)) * Xnorm s (q n t) (v n t)) :=
      (sum_le_sum fun i _ => sum_le_sum fun j _ => b6 i j).trans (by simp; ring_nf; rfl)
    have hSX : (16 * Real.sqrt (pc r) * Xnorm s (q n t) (v n t)) +
        (16 * Real.sqrt (pc r) * Xnorm s (q n t) (v n t)) +
        16 * (Real.sqrt (pc r) * (KA * Xnorm s (q n t) (v n t))) +
        3 * (16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t)) +
        3 * (16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t)) +
        9 * (16 * Real.sqrt (pc (r + 2)) * Xnorm s (q n t) (v n t)) =
          S3 * Xnorm s (q n t) (v n t) := by
      simp only [S3]; ring
    have := mul_le_mul_of_nonneg_left X hS3
    linarith
  have hJ1nS : ∀ n, ccoordSum r2 bPJ (J1n n) ≤ S2 * ε := by
    intro n
    have X := hXq n t ht
    simp only [J1n, interpJet1]
    rw [ccoordSum_pjetField]
    have b1 := ccoordSum_interpRec_le r2 s (hsq n) (v n t) (by omega)
    have b2 := ccoordSum_interpRec_v_le r2 s (q n t) (hsv n) (by omega)
    have b4 : ∀ i, ccoordSum r2 bM (interpD (q n t) i) ≤
        16 * Real.sqrt (pc (r2 + 1)) * Xnorm s (q n t) (v n t) := fun i =>
      (sum_le_sum fun k _ => (hderQ n i k r2).2).trans
        (ccoordSum_interpRec_le (r2 + 1) s (hsq n) (v n t) (by omega))
    have s4 : ∑ i, ccoordSum r2 bM (interpD (q n t) i) ≤
        3 * (16 * Real.sqrt (pc (r2 + 1)) * Xnorm s (q n t) (v n t)) :=
      (sum_le_sum fun i _ => b4 i).trans (by simp)
    have z2 : ∑ _i : Fin 3, ∑ _j : Fin 3,
        ccoordSum r2 bM ((0 : Fin 3 → Fin 3 → C(T3, MetricRec)) _i _j) = 0 := by
      simp [ccoordSum_zero_rec]
    have z1' : ∑ i : Fin 3, ccoordSum r2 bM ((0 : Fin 3 → C(T3, MetricRec)) i) = 0 := by
      simp [ccoordSum_zero_rec]
    have hSX : (16 * Real.sqrt (pc r2) * Xnorm s (q n t) (v n t)) +
        (16 * Real.sqrt (pc r2) * Xnorm s (q n t) (v n t)) +
        3 * (16 * Real.sqrt (pc (r2 + 1)) * Xnorm s (q n t) (v n t)) =
          S2 * Xnorm s (q n t) (v n t) := by
      simp only [S2]; ring
    have := mul_le_mul_of_nonneg_left X hS2
    rw [ccoordSum_zero_rec, z1', z2]
    linarith
  -- the rates of each slot (upper components)
  set ρ₁ : ℕ → ℝ := fun n => C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
  set ρ₂ : ℕ → ℝ := fun n => C₂ * Real.exp (K₂ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
  have hdiff : ∀ n, (∀ j, MemH r ⇑(ccoord bPJ (Jn n - J) j)) ∧
      ccoordSum r bPJ (Jn n - J) ≤ 16 * (3 * ρ₁ n + 15 * ρ₂ n) := by
    intro n
    have eJ : Jn n - J = pjetField (interpRec (q n t) - Q t) (interpRec (v n t) - V t)
        (interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t))) - A t)
        (interpD (q n t) - Qd t) (interpD (v n t) - Vd t) (interpDD (q n t) - Qdd t) :=
      pjetField_sub _ _ _ _ _ _ _ _ _ _ _ _
    obtain ⟨m1, c1⟩ := ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpRec_symm (hsq n) y μ ν)
      hQsym (B := ρ₁ n) fun κ => ⟨memH_mono (by omega) (hr1 n κ).1.1,
        (sn_mono' (by omega) (hr1 n κ).1.1).trans (hr1 n κ).1.2⟩
    obtain ⟨m2, c2⟩ := ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpRec_symm (hsv n) y μ ν)
      hVsym (B := ρ₁ n) fun κ => ⟨memH_mono (by omega) (hr1 n κ).2.1.1,
        (sn_mono' (by omega) (hr1 n κ).2.1.1).trans (hr1 n κ).2.1.2⟩
    obtain ⟨m3, c3⟩ := ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpRec_symRec_symm _ y μ ν)
      hAsym (B := ρ₁ n) fun κ => by
        rw [cmp_interpRec_symRec (N := n + 1)]; exact (hr1 n κ).2.2
    have m4 := fun i => ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpD_symm (hsq n) i y μ ν)
      (hQdsym i) (B := ρ₂ n) fun κ => ⟨memH_mono (by omega) (hrQd n κ i).1,
        (sn_mono' (by omega) (hrQd n κ i).1).trans (hrQd n κ i).2⟩
    have m5 := fun i => ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpD_symm (hsv n) i y μ ν)
      (hVdsym i) (B := ρ₂ n) fun κ => hrVd n κ i
    have m6 := fun i j => ccoordSum_sub_le_of_upper r _ _
      (fun y μ ν => interpDD_symm (hsq n) i j y μ ν) (hQddsym i j) (B := ρ₂ n) fun κ => hrQdd n κ i j
    rw [eJ]
    refine ⟨memH_pjetField m1 m2 m3 (fun i => (m4 i).1) (fun i => (m5 i).1)
      (fun i j => (m6 i j).1), ?_⟩
    rw [ccoordSum_pjetField]
    have s4 : ∑ i, ccoordSum r bM ((interpD (q n t) - Qd t) i) ≤ 3 * (16 * ρ₂ n) :=
      (sum_le_sum fun i _ => (m4 i).2).trans (by simp)
    have s5 : ∑ i, ccoordSum r bM ((interpD (v n t) - Vd t) i) ≤ 3 * (16 * ρ₂ n) :=
      (sum_le_sum fun i _ => (m5 i).2).trans (by simp)
    have s6 : ∑ i, ∑ j, ccoordSum r bM ((interpDD (q n t) - Qdd t) i j) ≤ 9 * (16 * ρ₂ n) :=
      (sum_le_sum fun i _ => sum_le_sum fun j _ => (m6 i j).2).trans (by simp; ring_nf; rfl)
    linarith
  have hdiff1 : ∀ n, (∀ j, MemH r2 ⇑(ccoord bPJ (J1n n - J1) j)) ∧
      ccoordSum r2 bPJ (J1n n - J1) ≤ 16 * (3 * ρ₁ n + 15 * ρ₂ n) := by
    intro n
    have eJ : J1n n - J1 = pjetField (interpRec (q n t) - Q t) (interpRec (v n t) - V t)
        (0 - 0) (interpD (q n t) - Qd t) (0 - 0) (0 - 0) :=
      pjetField_sub _ _ _ _ _ _ _ _ _ _ _ _
    obtain ⟨m1, c1⟩ := ccoordSum_sub_le_of_upper r2 _ _ (fun y μ ν => interpRec_symm (hsq n) y μ ν)
      hQsym (B := ρ₁ n) fun κ => ⟨memH_mono (by omega) (hr1 n κ).1.1,
        (sn_mono' (by omega) (hr1 n κ).1.1).trans (hr1 n κ).1.2⟩
    obtain ⟨m2, c2⟩ := ccoordSum_sub_le_of_upper r2 _ _ (fun y μ ν => interpRec_symm (hsv n) y μ ν)
      hVsym (B := ρ₁ n) fun κ => (hr1 n κ).2.1
    have m4 := fun i => ccoordSum_sub_le_of_upper r2 _ _
      (fun y μ ν => interpD_symm (hsq n) i y μ ν) (hQdsym i) (B := ρ₂ n) fun κ => hrQd n κ i
    rw [eJ]
    simp only [sub_zero]
    refine ⟨memH_pjetField m1 m2 (memH_ccoord_zero_rec r2) (fun i => (m4 i).1)
      (fun i => memH_ccoord_zero_rec r2) (fun i j => memH_ccoord_zero_rec r2), ?_⟩
    rw [ccoordSum_pjetField]
    have s4 : ∑ i, ccoordSum r2 bM ((interpD (q n t) - Qd t) i) ≤ 3 * (16 * ρ₂ n) :=
      (sum_le_sum fun i _ => (m4 i).2).trans (by simp)
    have z1 : ∑ i : Fin 3, ccoordSum r2 bM ((0 : Fin 3 → C(T3, MetricRec)) i) = 0 := by
      simp [ccoordSum_zero_rec]
    have z2 : ∑ i : Fin 3, ∑ j : Fin 3,
        ccoordSum r2 bM ((0 : Fin 3 → Fin 3 → C(T3, MetricRec)) i j) = 0 := by
      simp [ccoordSum_zero_rec]
    have hρ2 : 0 ≤ ρ₂ n := by
      have e : ρ₂ n = (C₂ * Real.exp (K₂ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
        simp only [ρ₂]; ring
      rw [e]; exact mul_nonneg (mul_nonneg hC₂ (Real.exp_pos _).le) (hfac0 n)
    have hρ1 : 0 ≤ ρ₁ n := by
      have e : ρ₁ n = (C₁ * Real.exp (K₁ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
        simp only [ρ₁]; ring
      rw [e]; exact mul_nonneg (mul_nonneg hC₁ (Real.exp_pos _).le) (hfac0 n)
    rw [ccoordSum_zero_rec, z1, z2]
    linarith
  -- membership of the interpolant jets
  have hJnm : ∀ n j, MemH r ⇑(ccoord bPJ (Jn n) j) := by
    intro n
    exact memH_pjetField (fun k => (memH_interpRec r _ k).1) (fun k => (memH_interpRec r _ k).1)
      (fun k => (memH_interpRec r _ k).1) (fun i k => (hderQ n i k r).1)
      (fun i k => (hderV n i k r).1) (fun i j k => (hderQQ n i j k r).1)
  have hJ1nm : ∀ n j, MemH r2 ⇑(ccoord bPJ (J1n n) j) := by
    intro n
    exact memH_pjetField (fun k => (memH_interpRec r2 _ k).1) (fun k => (memH_interpRec r2 _ k).1)
      (memH_ccoord_zero_rec r2) (fun i k => (hderQ n i k r2).1)
      (fun i => memH_ccoord_zero_rec r2) (fun i j => memH_ccoord_zero_rec r2)
  -- the rate in the final form
  have hρ : ∀ n, 16 * (3 * ρ₁ n + 15 * ρ₂ n) ≤
      C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by
    intro n
    have h2 : ρ₁ n ≤ C₁ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
      simp only [ρ₁]
      calc C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
          = C₁ * Real.exp (K₁ * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ C₁ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp1 hC₁) (hfac0 n)
    have h3 : ρ₂ n ≤ C₂ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
      simp only [ρ₂]
      calc C₂ * Real.exp (K₂ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
          = C₂ * Real.exp (K₂ * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ C₂ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp2 hC₂) (hfac0 n)
    have e : C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ =
        16 * (3 * (C₁ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹)) +
          15 * (C₂ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹))) := by
      simp only [C]; ring
    rw [e]; linarith
  -- limits of the rates
  have hρlim : Tendsto (fun n : ℕ => 16 * (3 * ρ₁ n + 15 * ρ₂ n)) atTop (𝓝 0) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simp only [one_div] at h0
    have h1 : Tendsto ρ₁ atTop (𝓝 0) := by
      simpa using h0.const_mul (C₁ * Real.exp (K₁ * t) * (1 + t) * ε)
    have h2 : Tendsto ρ₂ atTop (𝓝 0) := by
      simpa using h0.const_mul (C₂ * Real.exp (K₂ * t) * (1 + t) * ε)
    simpa using (((h1.const_mul 3).add (h2.const_mul 15)).const_mul 16)
  -- membership and size of the limit jets
  have hlimit : ∀ (r' : ℕ) (Pn : ℕ → C(T3, PJet)) (P : C(T3, PJet)) (B : ℝ),
      (∀ n j, MemH r' ⇑(ccoord bPJ (Pn n) j)) → (∀ n, ccoordSum r' bPJ (Pn n) ≤ B) →
      (∀ n, (∀ j, MemH r' ⇑(ccoord bPJ (Pn n - P) j)) ∧
        ccoordSum r' bPJ (Pn n - P) ≤ 16 * (3 * ρ₁ n + 15 * ρ₂ n)) →
      (∀ j, MemH r' ⇑(ccoord bPJ P j)) ∧ ccoordSum r' bPJ P ≤ B := by
    intro r' Pn P B hm hS hd
    have hPm : ∀ j, MemH r' ⇑(ccoord bPJ P j) := by
      intro j
      have h1 := hm 0 j
      have h2 := (hd 0).1 j
      rw [ccoord_sub] at h2
      exact memH_of_sub h1 h2
    refine ⟨hPm, ?_⟩
    have hle : ∀ n, ccoordSum r' bPJ P ≤ B + 16 * (3 * ρ₁ n + 15 * ρ₂ n) := by
      intro n
      unfold ccoordSum
      have hk : ∀ j, sn r' ⇑(ccoord bPJ P j) ≤ sn r' ⇑(ccoord bPJ (Pn n) j) +
          sn r' ⇑(ccoord bPJ (Pn n - P) j) := by
        intro j
        have e : ccoord bPJ P j = ccoord bPJ (Pn n) j - ccoord bPJ (Pn n - P) j := by
          rw [ccoord_sub]; abel
        rw [e]
        exact sn_sub_le' (hm n j) ((hd n).1 j)
      calc ∑ j, sn r' ⇑(ccoord bPJ P j)
          ≤ ∑ j, (sn r' ⇑(ccoord bPJ (Pn n) j) + sn r' ⇑(ccoord bPJ (Pn n - P) j)) :=
            sum_le_sum fun j _ => hk j
        _ = ccoordSum r' bPJ (Pn n) + ccoordSum r' bPJ (Pn n - P) := by
            rw [sum_add_distrib]; rfl
        _ ≤ B + 16 * (3 * ρ₁ n + 15 * ρ₂ n) := add_le_add (hS n) (hd n).2
    have hlim : Tendsto (fun n : ℕ => B + 16 * (3 * ρ₁ n + 15 * ρ₂ n)) atTop (𝓝 B) := by
      simpa using tendsto_const_nhds.add hρlim
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hle
  obtain ⟨hJm, hJS⟩ := hlimit r Jn J (S3 * ε) hJnm hJnS hdiff
  obtain ⟨hJ1m, hJ1S⟩ := hlimit r2 J1n J1 (S2 * ε) hJ1nm hJ1nS hdiff1
  have hS3S : S3 * ε ≤ S * ε := mul_le_mul_of_nonneg_right (by simp only [S]; linarith) hε0
  have hS2S : S2 * ε ≤ S * ε := mul_le_mul_of_nonneg_right (by simp only [S]; linarith) hε0
  refine ⟨hQt, hVt, hAt, hjet, hJm, hJS.trans hS3S, hJ1m, hJ1S.trans hS2S, fun n => ⟨hJnm n,
    (hJnS n).trans hS3S, (hdiff n).2.trans (hρ n), hJ1nm n, (hJ1nS n).trans hS2S,
    (hdiff1 n).2.trans (hρ n)⟩⟩

/-! ### The jet functionals of a classical solution -/

/-- The pointwise 2-jet of a `C³` field. -/
def pjAt (F : C3Field) (t : ℝ) (x : T3) : PJet :=
  (F.Q t x, F.V t x, F.A t x, fun i => F.Qd t i x, fun i => F.Vd t i x, fun i j => F.Qdd t i j x)

theorem gc_jetAt (F : C3Field) (t : ℝ) (x : T3) (b : Fin 4) :
    (F.jetAt t x).gc b = gaugeOf (pjAt F t x) b := rfl

theorem dgc_jetAt (F : C3Field) (t : ℝ) (x : T3) (b : Fin 4) :
    (F.jetAt t x).dgc 0 b = dtGaugeOf (pjAt F t x) b := rfl

theorem ddArr_eq_ddgOf (z : PJet) : ddArr z.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2 = ddgOf z := by
  funext α β
  refine Fin.cases ?_ (fun i => ?_) α <;> refine Fin.cases ?_ (fun j => ?_) β <;> rfl

theorem einM_congr {J J' : Jet3 (Fin 4)} (hg : J.g = J'.g) (hG : J.G = J'.G) (hdg : J.dg = J'.dg)
    (hddg : J.ddg = J'.ddg) : J.einM = J'.einM := by
  cases J; cases J'
  simp only at hg hG hdg hddg
  subst hg hG hdg hddg
  rfl

theorem einM_jetAt (F : C3Field) (t : ℝ) (x : T3) (μ ν : Fin 4) :
    (F.jetAt t x).einM μ ν = einOf (pjAt F t x) μ ν := by
  unfold einOf
  have hddg : (F.jetAt t x).ddg = (pjJet (pjAt F t x)).ddg := by
    funext a b
    have h := congrFun (congrFun (ddArr_eq_ddgOf (pjAt F t x)) a) b
    simp only [C3Field.jetAt, pjJet, arrJet, arrOf, ofArrays]
    rw [← h]
    rfl
  exact congrFun (congrFun (einM_congr (J := F.jetAt t x) (J' := pjJet (pjAt F t x)) rfl rfl rfl hddg) μ) ν

/-- **The time derivative of the gauge covector of a solution vanishes on the closed slab**
(interior points by differentiating `c = 0`, endpoints by continuity of the jet). -/
theorem hyp_dgc_time_eq_zero {F : C3Field} {T : ℝ} (h : F.Hyp T) (hT : 0 < T)
    (hI : F.InitData) : ∀ t ∈ Set.Icc 0 T, ∀ x b, (F.jetAt t x).dgc 0 b = 0 := by
  have hc := h.gc_eq_zero hT.le hI
  have hint : ∀ t ∈ Set.Ioo 0 T, ∀ x b, (F.jetAt t x).dgc 0 b = 0 := by
    intro t ht x b
    have h1 := (h.pathDeriv_time ht x).gc b
    have h2 : HasDerivAt (fun τ => (F.jetAt τ x).gc b) 0 t := by
      refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
      exact hc τ (Set.Ioo_subset_Icc_self hτ) x b
    exact h1.unique h2
  intro t ht x b
  have hJ := h.jetCont hT.le
  have hcont : Continuous fun τ : ℝ => (F.jc T (τ, x)).dgc 0 b :=
    ((continuous_apply b).comp ((continuous_apply 0).comp hJ.dgc)).comp
      (continuous_id.prodMk continuous_const)
  have heq : Set.EqOn (fun τ : ℝ => (F.jc T (τ, x)).dgc 0 b) (fun _ => 0) (Set.Ioo 0 T) :=
    fun τ hτ => by
      simp only
      rw [C3Field.jc_eq (Set.Ioo_subset_Icc_self hτ)]
      exact hint τ hτ x b
  have hcl := heq.closure hcont continuous_const
  rw [closure_Ioo hT.ne] at hcl
  have := hcl ht
  simp only at this
  rwa [C3Field.jc_eq ht] at this

/-! ### Time derivatives of interpolated histories -/

section TimeDeriv

variable {N : ℕ} [NeZero N]

theorem hasDerivAt_interpD {u : ℝ → Grid N → MetricRec} {u' : Grid N → MetricRec} {t : ℝ}
    (hu : ∀ x, HasDerivAt (fun τ => u τ x) (u' x) t) (i : Fin 3) (y : T3) :
    HasDerivAt (fun τ => interpD (u τ) i y) (interpD u' i y) t := by
  refine hasDerivAt_reField_time
    (w := fun τ μ ν => PeriodicGridSobolev.Sampling.specD i (cx (comp (u τ) μ ν)))
    (fun μ ν x => ?_) y
  refine hasDerivAt_specD (w := fun τ => cx (comp (u τ) μ ν)) (fun z => ?_) i x
  have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hu z) μ) ν
  exact h.ofReal_comp

/-- **The jet slots of the interpolant are its actual derivatives**: along a writer solution on
`[0, T]`, `∂ₜ(𝓘_h q) = 𝓘_h v` on `[0, T]`, `∂ₜ(∂ᵢ𝓘_h q) = ∂ᵢ𝓘_h v` on `[0, T]` and
`∂ₜ(𝓘_h v) = 𝓘_h(∂ₜv)` (the finite acceleration) on `(0, T)`; the spatial slots are classical
spatial derivatives (`isContJet_interp`). -/
theorem interpJet_time_derivs {T : ℝ} {q v : ℝ → Grid N → MetricRec} (hsol : IsWriterSolution T q v)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (y : T3) :
    HasDerivAt (fun τ => interpRec (q τ) y) (interpRec (v t) y) t ∧
    (∀ i, HasDerivAt (fun τ => interpD (q τ) i y) (interpD (v t) i y) t) ∧
    (t ∈ Set.Ioo 0 T → HasDerivAt (fun τ => interpRec (v τ) y)
      (interpRec (symRec (harmonicWriterAcceleration (q t) (v t))) y) t) := by
  refine ⟨hasDerivAt_interpRec (hsol t ht).2.2.1 y,
    fun i => hasDerivAt_interpD (hsol t ht).2.2.1 i y, fun ht' => ?_⟩
  have h := hasDerivAt_interpRec_symRec (u := v) (t := t) (hsol t ht).2.2.2 y
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ht'] with σ hσ
  rw [symRec_of_isSymRec (hsol σ (Set.Ioo_subset_Icc_self hσ)).2.1]

/-- **`∂ₜ c(g_h)` is the time derivative of the gauge covector of the interpolant** (one-sided at
the ends of `[0, T]`): along a writer solution, where `g_h = η + 𝓘_h q` is nondegenerate,
`τ ↦ c_b(g_h)(τ, y)` has derivative `dtGaugeOf (interpJet …)` within `[0, T]`. -/
theorem gauge_hasDerivWithinAt {T : ℝ} {q v : ℝ → Grid N → MetricRec}
    (hsol : IsWriterSolution T q v) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (y : T3)
    (hdet : (Matrix.of (minkowski + interpRec (q t) y)).det ≠ 0) (b : Fin 4) :
    HasDerivWithinAt (fun τ => gaugeOf (interpJet (q τ) (v τ) y) b)
      (dtGaugeOf (interpJet (q t) (v t) y) b) (Set.Icc 0 T) t := by
  set Z : ℝ → PJet := fun τ => (interpRec (q τ) y, interpRec (symRec (v τ)) y,
    interpRec (symRec (harmonicWriterAcceleration (q t) (v t))) y, fun i => interpD (q τ) i y,
    fun i => interpD (v t) i y, fun i j => interpDD (q t) i j y) with hZ
  have hsv : symRec (v t) = v t := symRec_of_isSymRec (hsol t ht).2.1
  have hZt : Z t = interpJet (q t) (v t) y := by
    simp only [Z, hsv]; rfl
  have hq : HasDerivAt (fun τ => interpRec (q τ) y) (interpRec (symRec (v t)) y) t := by
    rw [hsv]; exact hasDerivAt_interpRec (hsol t ht).2.2.1 y
  have hg : MHasDeriv (fun τ => (pjJet (Z τ)).g) ((pjJet (Z t)).dg 0) t :=
    C3Field.mhasDeriv_of_rec_add minkowski hq
  have hP : Jet3.PathDeriv (fun τ => pjJet (Z τ)) 0 t := by
    refine ⟨hg, ?_, fun a => ?_, fun a b' i j => ?_⟩
    · exact mhasDeriv_inv (A := fun τ => Matrix.of (minkowski + interpRec (q τ) y)) hg hdet
    · refine Fin.cases ?_ (fun i => ?_) a
      · exact C3Field.mhasDeriv_of_rec
          (hasDerivAt_interpRec_symRec (u := v) (t := t) (hsol t ht).2.2.2 y)
      · exact C3Field.mhasDeriv_of_rec (hasDerivAt_interpD (hsol t ht).2.2.1 i y)
    · exact (hasDerivAt_const t ((pjJet (Z t)).ddg a b' i j)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun τ => rfl)
  have h1 := hP.gc b
  have h2 : (pjJet (Z t)).dgc 0 b = dtGaugeOf (interpJet (q t) (v t) y) b := by
    rw [← hZt]; rfl
  rw [h2] at h1
  refine h1.hasDerivWithinAt.congr (fun τ hτ => ?_) ?_
  · show gaugeOf (interpJet (q τ) (v τ) y) b = gaugeOf (Z τ) b
    rw [← gaugeOf_trunc (interpJet (q τ) (v τ) y), ← gaugeOf_trunc (Z τ)]
    simp only [Z, trunc, symRec_of_isSymRec (hsol τ hτ).2.1]
    rfl
  · show gaugeOf (interpJet (q t) (v t) y) b = gaugeOf (Z t) b
    rw [hZt]

end TimeDeriv

/-! ### The subsidiary bounds -/

set_option maxHeartbeats 8000000 in
/-- **`lem:supp-open-subsidiary`** (forced subsidiary energy on the common interval), for `s ≥ 6`:
there are `ε_s, T_s > 0` and `C ≥ 0` such that for every `(γ, K) ∈ D_s(ε)` (`DsData`,
`dataSize ≤ ε ≤ ε_s`) with the harmonic initialization `V₀ = prepFun`
(`eq:supp-open-harmonic-initial`), the open writer has, for every mesh `h = 1/(n + 1)`, a unique
solution on `[0, T_s]` from the samples of `(Q₀, V₀)`, and the interpolated metric
`g_h = η + 𝓘_h q_h` (with its jet `interpJet`, whose slots are its actual derivatives:
`interpJet_time_derivs`, `isContJet_interp`) satisfies, for every `t ∈ [0, T_s]`,
`‖c(g_h)‖_{H^{s-2}} + ‖∂ₜ c(g_h)‖_{H^{s-3}} + ‖G(g_h)‖_{H^{s-3}} ≤ C h ε` componentwise
(`eq:supp-open-subsidiary`), where `∂ₜ c(g_h)` is the time derivative of `τ ↦ c(g_h)(τ, y)` within
`[0, T_s]`. -/
theorem supp_open_subsidiary (s : ℕ) (hs : 6 ≤ s) :
    ∃ εs > 0, ∃ TL > 0, ∃ C ≥ 0, ∀ (Q₀ Kr : C(T3, MetricRec))
      (Qd Kd : Fin 3 → C(T3, MetricRec)) (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      DsData s Q₀ Kr Qd Kd Qdd → dataSize s Q₀ Kr ≤ ε → ε ≤ εs →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
      ∃ q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec,
        (∀ n, IsWriterSolution TL (q n) (v n) ∧ q n 0 = sampleRec (n + 1) ⇑Q₀ ∧
          v n 0 = sampleRec (n + 1) ⇑V₀) ∧
        (∀ n (q' v' : ℝ → Grid (n + 1) → MetricRec), q' 0 = sampleRec (n + 1) ⇑Q₀ →
          v' 0 = sampleRec (n + 1) ⇑V₀ → IsWriterSolution TL q' v' →
          ∀ t ∈ Set.Icc 0 TL, q' t = q n t ∧ v' t = v n t) ∧
        ∀ n, ∀ t ∈ Set.Icc 0 TL,
          (∀ b, ∃ F : CT, (∀ y, F y = ((gaugeOf (interpJet (q n t) (v n t) y) b : ℝ) : ℂ)) ∧
            MemH (s - 2) ⇑F ∧ sn (s - 2) ⇑F ≤ C * ε * ((n : ℝ) + 1)⁻¹) ∧
          (∀ b, ∃ F : CT, (∀ y, F y = ((dtGaugeOf (interpJet (q n t) (v n t) y) b : ℝ) : ℂ)) ∧
            MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * ε * ((n : ℝ) + 1)⁻¹) ∧
          (∀ μ ν, ∃ F : CT, (∀ y, F y = ((einOf (interpJet (q n t) (v n t) y) μ ν : ℝ) : ℂ)) ∧
            MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * ε * ((n : ℝ) + 1)⁻¹) ∧
          ∀ y b, HasDerivWithinAt (fun τ => gaugeOf (interpJet (q n τ) (v n τ) y) b)
            (dtGaugeOf (interpJet (q n t) (v n t) y) b) (Set.Icc 0 TL) t := by
  obtain ⟨δ1, hδ1, h1⟩ := writer_limit_hyp s hs
  obtain ⟨δ2, hδ2, K, hK, C, hC, S, hS, h2⟩ := writer_jet_rates s (by omega)
  obtain ⟨δM, hδM, CM, hCM, hprep⟩ := prep_moser s (by omega)
  obtain ⟨εL, hεL, TL, hTL, CL, hCL, hlife⟩ := open_writer_lifespan s (by omega)
  obtain ⟨CS, hCS, hsamp⟩ := Xnorm_sample_le s (by omega)
  obtain ⟨δG, hδG, CG, hCG, hGm⟩ := pjet_moser_fin (s - 2) (by omega)
    (fun b : Fin 4 => fun z => gaugeOf z b) analyticAt_gaugeOf
  obtain ⟨δD, hδD, CD, hCD, hDm⟩ := pjet_moser_fin (s - 3) (by omega)
    (fun b : Fin 4 => fun z => dtGaugeOf z b) analyticAt_dtGaugeOf
  obtain ⟨δE, hδE, CE, hCE, hEm⟩ := pjet_moser_fin (s - 3) (by omega)
    (fun p : Fin 4 × Fin 4 => fun z => einOf z p.1 p.2) (fun p => analyticAt_einOf p.1 p.2)
  obtain ⟨r₁, hr₁, hinv⟩ := exists_inv_chart
  set B : ℝ := 1 + ∑ j, ‖bPJ j‖
  have hB : ∀ j, ‖bPJ j‖ ≤ B := fun j => by
    have := single_le_sum (f := fun j => ‖bPJ j‖) (fun _ _ => norm_nonneg _) (mem_univ j)
    linarith
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∑ j, ‖bPJ j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  set Cp : ℝ := 1 + CM
  have hCp : 0 ≤ Cp := by positivity
  set Cε : ℝ := (1 + CL * CS) * Cp
  have hCε : 0 ≤ Cε := by positivity
  have hCpε : Cp ≤ Cε := by
    have : 0 ≤ CL * CS * Cp := by positivity
    simp only [Cε]; nlinarith
  set δJ : ℝ := min (min δG δD) (min δE (r₁ / (2 * (B * Real.sqrt cEmb + 1))))
  have hδJ : 0 < δJ := by positivity
  set Z0 : ℝ := Real.exp (K * TL) * (1 + TL) * Cε
  have hZ0 : 0 ≤ Z0 := by positivity
  set Cout : ℝ := (CG + CD + CE) * C * Z0
  have hCout : 0 ≤ Cout := by positivity
  refine ⟨min (min (min δM (εL / (CS * Cp + 1))) (min (δ1 / (Cε + 1)) (δ2 / (Cε + 1))))
      (δJ / ((S + 1) * (Cε + 1))), by positivity, TL, hTL, Cout, hCout,
    fun Q₀ Kr Qd Kd Qdd ε hD hsz hεs => ?_⟩
  have hεs' := hεs.trans (min_le_left _ _)
  have hεJ : ε ≤ δJ / ((S + 1) * (Cε + 1)) := hεs.trans (min_le_right _ _)
  have hεM : ε ≤ δM := hεs'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεL' : ε ≤ εL / (CS * Cp + 1) := hεs'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ δ1 / (Cε + 1) := hεs'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε2 : ε ≤ δ2 / (Cε + 1) := hεs'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hA0 : 0 ≤ ccoordSum (s + 1) bM Q₀ := ccoordSum_nonneg _ _ _
  have hB0' : 0 ≤ ccoordSum s bM Kr := ccoordSum_nonneg _ _ _
  have hε0 : 0 ≤ ε := (add_nonneg hA0 hB0').trans hsz
  have hA : ccoordSum (s + 1) bM Q₀ ≤ ε := by unfold dataSize at hsz; linarith
  obtain ⟨V₀, hV₀, hVreg, hVb⟩ := hprep Q₀ Kr Qd hD.dQ hD.regQ hD.regK (hA.trans hεM)
  -- the prepared data
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
  have hX0 : ∀ N [NeZero N], Xnorm s (sampleRec N ⇑Q₀) (sampleRec N ⇑V₀) ≤ CS * (Cp * ε) :=
    fun N _ => (hsamp N Q₀ V₀ hD.regQ hVreg).trans (mul_le_mul_of_nonneg_left hcT hCS)
  have hXL : CS * (Cp * ε) ≤ εL := by
    have h := hεL'
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hex : ∀ n : ℕ, ∃ qv : (ℝ → Grid (n + 1) → MetricRec) × (ℝ → Grid (n + 1) → MetricRec),
      qv.1 0 = sampleRec (n + 1) ⇑Q₀ ∧ qv.2 0 = sampleRec (n + 1) ⇑V₀ ∧
      IsWriterSolution TL qv.1 qv.2 ∧ ∀ t ∈ Set.Icc 0 TL, Xnorm s (qv.1 t) (qv.2 t) ≤
        CL * Xnorm s (sampleRec (n + 1) ⇑Q₀) (sampleRec (n + 1) ⇑V₀) := by
    intro n
    obtain ⟨q, v, h1, h2, h3, h4⟩ := (hlife (n + 1) (sampleRec (n + 1) ⇑Q₀)
      (sampleRec (n + 1) ⇑V₀) (isSymRec_sampleRec hD.symQ) (isSymRec_sampleRec hVsym)
      ((hX0 (n + 1)).trans hXL)).1
    exact ⟨(q, v), h1, h2, h3, h4⟩
  choose qv hq0 hv0 hsol hXqv using hex
  set q : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec := fun n => (qv n).1
  set v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec := fun n => (qv n).2
  have hW : WriterData s TL q v Q₀ V₀ (Cε * ε) := by
    refine ⟨hsol, hq0, hv0, hD.symQ, hVsym, hD.regQ, hVreg, hcT.trans
      (mul_le_mul_of_nonneg_right hCpε hε0), fun n t ht => (hXqv n t ht).trans ?_⟩
    have := mul_le_mul_of_nonneg_left (hX0 (n + 1)) hCL
    have h' : CL * (CS * (Cp * ε)) ≤ Cε * ε := by
      simp only [Cε]
      have : 0 ≤ Cp * ε := by positivity
      nlinarith
    linarith
  have hεδ1 : Cε * ε ≤ δ1 := by
    rw [le_div_iff₀ (by positivity)] at hε1; nlinarith
  have hεδ2 : Cε * ε ≤ δ2 := by
    rw [le_div_iff₀ (by positivity)] at hε2; nlinarith
  have hSJ : S * (Cε * ε) ≤ δJ := by
    rw [le_div_iff₀ (by positivity)] at hεJ
    have h3 : S * (Cε * ε) ≤ ε * ((S + 1) * (Cε + 1)) := by
      have : S * Cε ≤ (S + 1) * (Cε + 1) := by nlinarith
      nlinarith
    linarith
  refine ⟨V₀, hV₀, q, v, fun n => ⟨hsol n, hq0 n, hv0 n⟩, fun n q' v' h1 h2 h3 t ht =>
    (hlife (n + 1) (sampleRec (n + 1) ⇑Q₀) (sampleRec (n + 1) ⇑V₀)
      (isSymRec_sampleRec hD.symQ) (isSymRec_sampleRec hVsym) ((hX0 (n + 1)).trans hXL)).2
      q' v' (q n) (v n) h1 h2 (hq0 n) (hv0 n) h3 (hsol n) t ht, ?_⟩
  -- the limit
  have hW' := hW
  obtain ⟨-, -, -, hQs, -, hQ, hV, hX0', hXq⟩ := hW'
  obtain ⟨Q, V, A, Qd', Vd', Qdd', hQ0, hV0, hcr⟩ := h2 TL q v Q₀ V₀ (Cε * ε) hsol hq0 hv0 hQs
    hVsym hQ hV hX0' hXq hεδ2
  obtain ⟨hF, hlim⟩ := h1 TL q v Q₀ V₀ (Cε * ε) hW hεδ1 hTL.le
  have eQ : ∀ τ ∈ Set.Icc 0 TL, (limField q v TL).Q τ = ⇑(Q τ) := fun τ hτ => by
    have e := tendsto_nhds_unique (hlim τ hτ).1 (hcr τ hτ).1
    show ⇑(limF (famQ q []) (clampT TL τ)) = _
    rw [clampT_of_mem hτ, e]
  have eV : ∀ τ ∈ Set.Icc 0 TL, (limField q v TL).V τ = ⇑(V τ) := fun τ hτ => by
    have e := tendsto_nhds_unique (hlim τ hτ).2.1 (hcr τ hτ).2.1
    show ⇑(limF (famV v []) (clampT TL τ)) = _
    rw [clampT_of_mem hτ, e]
  have eA : ∀ τ ∈ Set.Icc 0 TL, (limField q v TL).A τ = ⇑(A τ) := fun τ hτ => by
    have e := tendsto_nhds_unique (hlim τ hτ).2.2 (hcr τ hτ).2.2.1
    show ⇑(limF (famA q v []) (clampT TL τ)) = _
    rw [clampT_of_mem hτ, e]
  have eQd : ∀ τ ∈ Set.Icc 0 TL, ∀ i, (limField q v TL).Qd τ i = ⇑(Qd' τ i) := fun τ hτ i => by
    have h' := hF.xQ τ hτ i
    rw [eQ τ hτ] at h'
    exact isLineDeriv_unique h' ((hcr τ hτ).2.2.2.1.dQ i)
  have eQdd : ∀ τ ∈ Set.Icc 0 TL, ∀ i j, (limField q v TL).Qdd τ i j = ⇑(Qdd' τ i j) :=
    fun τ hτ i j => by
      have h' := hF.xQd τ hτ i j
      rw [eQd τ hτ j] at h'
      exact isLineDeriv_unique h' ((hcr τ hτ).2.2.2.1.dQd i j)
  have eVd : ∀ τ ∈ Set.Icc 0 TL, ∀ i, (limField q v TL).Vd τ i = ⇑(Vd' τ i) := fun τ hτ i => by
    have h' := hF.xV τ hτ i
    rw [eV τ hτ] at h'
    exact isLineDeriv_unique h' ((hcr τ hτ).2.2.2.1.dV i)
  -- the initial slice from the data
  have h0 : (0 : ℝ) ∈ Set.Icc 0 TL := ⟨le_rfl, hTL.le⟩
  set F := limField q v TL
  have fQ : F.Q 0 = ⇑Q₀ := by rw [eQ 0 h0, hQ0]
  have fV : F.V 0 = ⇑V₀ := by rw [eV 0 h0, hV0]
  have fQd : ∀ k, F.Qd 0 k = ⇑(Qd k) := fun k => by
    have h' := hF.xQ 0 h0 k
    rw [fQ] at h'
    exact isLineDeriv_unique h' (hD.dQ k)
  have fQdd : ∀ k l, F.Qdd 0 k l = ⇑(Qdd k l) := fun k l => by
    have h' := hF.xQd 0 h0 k l
    rw [fQd l] at h'
    exact isLineDeriv_unique h' (hD.dQd k l)
  have qt : ∀ y μ, Q₀ y μ 0 = 0 := fun y μ => by rw [hD.symQ]; exact hD.timeQ y μ
  have qdt : ∀ k y μ, Qd k y 0 μ = 0 ∧ Qd k y μ 0 = 0 := fun k y μ =>
    ⟨isLineDeriv_comp_unique (hD.dQ k) (isLineDeriv_zero k) (fun x => hD.timeQ x μ) y,
     isLineDeriv_comp_unique (hD.dQ k) (isLineDeriv_zero k) (fun x => qt x μ) y⟩
  have qddt : ∀ k l y μ, Qdd k l y 0 μ = 0 ∧ Qdd k l y μ 0 = 0 := fun k l y μ =>
    ⟨isLineDeriv_comp_unique (hD.dQd k l) (isLineDeriv_zero k) (fun x => (qdt l x μ).1) y,
     isLineDeriv_comp_unique (hD.dQd k l) (isLineDeriv_zero k) (fun x => (qdt l x μ).2) y⟩
  have hI : F.InitData := by
    intro x
    have hdet : (Matrix.of (minkowski + Q₀ x)).det ≠ 0 := by
      have := hF.det_ne h0 x; rwa [fQ] at this
    obtain ⟨hblk, hγγ⟩ := inv_block (g := minkowski + Q₀ x)
      (by simp [minkowski, hD.timeQ]) (fun i => by simp [minkowski, hD.timeQ, fin_zero_ne_succ])
      (fun i => by simp [minkowski, qt, Fin.succ_ne_zero]) hdet
    set S0 := dataSlice ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) (fun i => ⇑(Kd i)) (fun i j => ⇑(Qdd i j)) x
    set S : SliceData := { S0 with
      dv00 := (fun k => F.Vd 0 k x 0 0)
      dv0 := (fun k i => F.Vd 0 k x 0 i.succ)
      w := Matrix.of (F.A 0 x) }
    have hSv : S.Valid := by
      refine ⟨hγγ, ?_, ?_, fun k => ?_, fun k l => ?_, fun k l => ?_, ?_, fun k => ?_, ?_⟩
      · ext i j; simp [S, S0, dataSlice, hD.symQ x, minkowski_symm]
      · ext i j
        exact recInv_symm (fun μ ν => by simp only [Pi.add_apply, hD.symQ x μ ν, minkowski_symm μ ν])
          j.succ i.succ
      · ext i j
        have := hF.sQd 0 k x j.succ i.succ
        rw [fQd] at this
        exact this
      · ext i j
        have := hF.sQdd 0 k l x j.succ i.succ
        rw [fQdd] at this
        exact this
      · ext i j
        have := congrFun (congrFun (hF.iQdd 0 k l) x) i.succ
        rw [fQdd, fQdd] at this
        exact congrFun this j.succ
      · ext i j; simp [S, S0, dataSlice, hD.symK x]
      · ext i j
        have h := isLineDeriv_comp_unique (hD.dK k) (isLineDeriv_entry (hD.dK k) j.succ i.succ)
          (fun y => hD.symK y i.succ j.succ) x
        first | exact h | exact h.symm
      · ext μ ν; exact hF.sA 0 x ν μ
    refine ⟨S, hSv, ⟨rfl, fun l => rfl⟩, hD.ham x, hD.mom x, ?_, ?_, ?_, ?_⟩
    · show Matrix.of (minkowski + F.Q 0 x) = sliceMat (-1) 0 S0.γ
      rw [fQ]
      ext μ ν
      refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
        simp [S0, dataSlice, minkowski, hD.timeQ, qt, Fin.succ_ne_zero, fin_zero_ne_succ]
    · show (Matrix.of (minkowski + F.Q 0 x))⁻¹ = sliceMat (-1) 0 S0.γi
      rw [fQ]; exact hblk
    · funext a
      refine Fin.cases ?_ (fun k => ?_) a
      · show Matrix.of (F.V 0 x) = sliceMat S0.v00 S0.v0 ((-2 : ℝ) • S0.K)
        rw [fV, hV₀]
        ext μ ν
        refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
          simp [S0, dataSlice, prepFun]
      · show Matrix.of (F.Qd 0 k x) = sliceMat 0 0 (S0.dγ k)
        rw [fQd]
        ext μ ν
        refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
          simp [S0, dataSlice, (qdt k x _).1, (qdt k x _).2]
    · have hVdsp : ∀ (l i j : Fin 3), F.Vd 0 l x i.succ j.succ = -2 * Kd l x i.succ j.succ := by
        intro l i j
        refine isLineDeriv_comp_unique (hF.xV 0 h0 l) (f := fun y => -2 * Kr y i.succ j.succ)
          (f' := fun y => -2 * Kd l y i.succ j.succ)
          (fun y => ((isLineDeriv_entry (hD.dK l) i.succ j.succ) y).const_mul (-2)) (fun y => ?_) x
        rw [fV, hV₀]; simp [prepFun]
      have hdtk : ∀ l, Matrix.of (F.Vd 0 l x) = S.dtk l := by
        intro l
        ext μ ν
        refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν
        · rfl
        · rfl
        · show F.Vd 0 l x i.succ 0 = F.Vd 0 l x 0 i.succ
          exact hF.sVd 0 l x _ _
        · show F.Vd 0 l x i.succ j.succ = ((-2 : ℝ) • S0.dK l) i j
          rw [hVdsp]; simp [S0, dataSlice]
      funext a b
      refine Fin.cases ?_ (fun k => ?_) a <;> refine Fin.cases ?_ (fun l => ?_) b
      · rfl
      · exact hdtk l
      · exact hdtk k
      · show Matrix.of (F.Qdd 0 k l x) = sliceMat 0 0 (S0.ddγ k l)
        rw [fQdd]
        ext μ ν
        refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
          simp [S0, dataSlice, (qddt k l x _).1, (qddt k l x _).2]
  -- the limit functionals vanish
  have hgc0 := hF.gc_eq_zero hTL.le hI
  have hdgc0 := hyp_dgc_time_eq_zero hF hTL hI
  have hein0 := hF.einM_eq_zero hTL hI
  intro n t ht
  obtain ⟨-, -, -, -, hJm, hJS, hJ1m, hJ1S, hn⟩ := hcr t ht
  obtain ⟨hJnm, hJnS, hd, hJ1nm, hJ1nS, hd1⟩ := hn n
  set J := pjetField (Q t) (V t) (A t) (Qd' t) (Vd' t) (Qdd' t) with hJdef
  have hpj : ∀ y, pjAt F t y = J y := by
    intro y
    simp only [pjAt, J, pjetField, ContinuousMap.coe_mk, eQ t ht, eV t ht, eA t ht, eQd t ht,
      eVd t ht, eQdd t ht]
  have hJ1 : ∀ y, pjetField (Q t) (V t) 0 (Qd' t) 0 0 y = trunc (J y) := fun y => rfl
  -- the rate in the final form
  have hrate : C * Real.exp (K * t) * (1 + t) * (Cε * ε) * ((n : ℝ) + 1)⁻¹ ≤
      C * Z0 * (ε * ((n : ℝ) + 1)⁻¹) := by
    have hexp : Real.exp (K * t) ≤ Real.exp (K * TL) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK)
    have h1t : 1 + t ≤ 1 + TL := by linarith [ht.2]
    have hn0 : 0 ≤ ε * ((n : ℝ) + 1)⁻¹ := mul_nonneg hε0 (by positivity)
    have e1 : C * Real.exp (K * t) * (1 + t) * (Cε * ε) * ((n : ℝ) + 1)⁻¹ =
        C * (Real.exp (K * t) * (1 + t) * Cε) * (ε * ((n : ℝ) + 1)⁻¹) := by ring
    rw [e1]
    have h2' : Real.exp (K * t) * (1 + t) * Cε ≤ Z0 := by
      simp only [Z0]
      have := mul_le_mul hexp h1t (by linarith [ht.1]) (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right this hCε
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2' hC) hn0
  have hfin : ∀ Cx : ℝ, 0 ≤ Cx → Cx ≤ CG + CD + CE → ∀ X : ℝ,
      X ≤ C * Real.exp (K * t) * (1 + t) * (Cε * ε) * ((n : ℝ) + 1)⁻¹ →
      Cx * X ≤ Cout * ε * ((n : ℝ) + 1)⁻¹ := by
    intro Cx hCx0 hCx X hX
    have hX' := hX.trans hrate
    have hn0 : 0 ≤ ε * ((n : ℝ) + 1)⁻¹ := mul_nonneg hε0 (by positivity)
    calc Cx * X ≤ Cx * (C * Z0 * (ε * ((n : ℝ) + 1)⁻¹)) := mul_le_mul_of_nonneg_left hX' hCx0
      _ ≤ (CG + CD + CE) * (C * Z0 * (ε * ((n : ℝ) + 1)⁻¹)) :=
          mul_le_mul_of_nonneg_right hCx (by positivity)
      _ = Cout * ε * ((n : ℝ) + 1)⁻¹ := by simp only [Cout]; ring
  have hSδ : S * (Cε * ε) ≤ δJ := hSJ
  have hδJG : δJ ≤ δG := (min_le_left _ _).trans (min_le_left _ _)
  have hδJD : δJ ≤ δD := (min_le_left _ _).trans (min_le_right _ _)
  have hδJE : δJ ≤ δE := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨fun b => ?_, fun b => ?_, fun μ ν => ?_, fun y b => ?_⟩
  · -- the gauge covector in `H^{s-2}`
    obtain ⟨G, hG, hGm, hGs⟩ := hGm b (interpJet1 (q n t) (v n t))
      (pjetField (Q t) (V t) 0 (Qd' t) 0 0) hJ1nm hJ1m ((hJ1nS.trans hSδ).trans hδJG)
      ((hJ1S.trans hSδ).trans hδJG)
    refine ⟨G, fun y => ?_, hGm, hfin CG hCG (by linarith) _ hd1
      |> fun h => hGs.trans h⟩
    rw [hG y]
    rw [interpJet1_apply, gaugeOf_trunc, hJ1, gaugeOf_trunc, ← hpj, ← gc_jetAt,
      hgc0 t ht y b, sub_zero]
  · -- its time derivative in `H^{s-3}`
    obtain ⟨G, hG, hGm, hGs⟩ := hDm b (interpJet (q n t) (v n t)) J hJnm hJm
      ((hJnS.trans hSδ).trans hδJD) ((hJS.trans hSδ).trans hδJD)
    refine ⟨G, fun y => ?_, hGm, hfin CD hCD (by linarith) _ hd
      |> fun h => hGs.trans h⟩
    rw [hG y]
    rw [← hpj, ← dgc_jetAt, hdgc0 t ht y b, sub_zero]
  · -- the Einstein tensor in `H^{s-3}`
    obtain ⟨G, hG, hGm, hGs⟩ := hEm (μ, ν) (interpJet (q n t) (v n t)) J hJnm hJm
      ((hJnS.trans hSδ).trans hδJE) ((hJS.trans hSδ).trans hδJE)
    refine ⟨G, fun y => ?_, hGm, hfin CE hCE (by linarith) _ hd
      |> fun h => hGs.trans h⟩
    rw [hG y]
    rw [← hpj, ← einM_jetAt]
    have := congrFun (congrFun (hein0 t ht y) μ) ν
    rw [this, Matrix.zero_apply, sub_zero]
  · -- the time derivative is the actual derivative
    have hsmall : ‖interpRec (q n t) y‖ < r₁ := by
      have h1' : ‖interpRec (q n t) y‖ ≤ ‖interpJet (q n t) (v n t) y‖ := by
        convert norm_fst_le (interpJet (q n t) (v n t) y) using 1
      have h2' := norm_le_ccoordSum (s - 3) (by omega) bPJ hB (interpJet (q n t) (v n t)) hJnm y
      have h3 : B * (Real.sqrt cEmb * ccoordSum (s - 3) bPJ (interpJet (q n t) (v n t))) ≤
          B * (Real.sqrt cEmb * δJ) := by
        gcongr
        exact hJnS.trans hSδ
      have h4 : B * (Real.sqrt cEmb * δJ) < r₁ := by
        have hδ4 : δJ ≤ r₁ / (2 * (B * Real.sqrt cEmb + 1)) :=
          (min_le_right _ _).trans (min_le_right _ _)
        have hpos : 0 < 2 * (B * Real.sqrt cEmb + 1) := by positivity
        rw [le_div_iff₀ hpos] at hδ4
        nlinarith [Real.sqrt_nonneg cEmb]
      linarith
    have hdet : (Matrix.of (minkowski + interpRec (q n t) y)).det ≠ 0 :=
      (hinv (minkowski + interpRec (q n t) y) (by rwa [add_sub_cancel_left])).1
    exact gauge_hasDerivWithinAt (hsol n) ht y hdet b

end

end RenewalGeometry.OpenWriterSubsidiary
