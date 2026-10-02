/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterFiniteWords
import RenewalGeometry.Gravity.OpenWriterLawEinsteinLimit

/-!
# The Einstein limit of the finite local successor words (`thm:supp-open-finite-words`,
  last clause; emergent-spacetime manuscript)

* `ofRec`, `recOf_ofRec`, `finiteWords_Xnorm_add_le`: symmetric record arrays as ten-component
  writer records, and the triangle inequality of the `X^s_h` norm up to the factor `√20`.
* `finite_words_einstein` (**"every resulting history has the same Einstein limit"**): for
  harmonic vacuum data `(γ, K) ∈ D_s(ε)` and arbitrary marks `B_n` of the closed ball, every
  sequence of bank words (`OpenWriterFiniteWords.bankWord`) obeying the precision convention
  `η = c ε h^{s+10}` and whose starting finite record differs from the compatible preparation
  (the samples of `(γ, prep)`) by at most `c₀ ε h⁴` in `X^s_h` has interpolated records converging
  on the common slab to the same harmonic vacuum development as the central writer
  (`supp_law_einstein`), with the metric rate `O(h ε)` in `H^{s-1}`, `H^{s-2}`, `H^{s-3}`.

The word is compared with the exact law-family history from the samples through the forced
lower-order difference estimate `law_difference` (the word is a forced history with the actual
acceleration defect as force, `‖f‖_{H^s_h} = O(ε h⁵)` by `finite_words_bounds`); its starting
perturbation `O(ε h⁴)` and integrated defect `O(ε h⁵)` are both `O(ε h)`.
-/

open Set Metric Filter Topology Finset MeasureTheory UnitAddTorus
open scoped NNReal BigOperators Real

namespace RenewalGeometry.OpenWriterFiniteWords

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterGridBridge RootParityConnector PeriodicGridSobolev.Composition
  HarmonicWriter OpenWriterContinuum HarmonicGaugePropagation ContractedBianchiJet HarmonicDefect
  OpenWriterLimitRegularity OpenWriterLocalJets
open PeriodicGridSobolev (GridH)

noncomputable section

set_option linter.unusedSectionVars false

section Records

variable {N : ℕ} [NeZero N]

/-- The ten upper components of a record array as a writer record. -/
def ofRec (r : ℕ) (u : Grid N → MetricRec) : Upper → GridH N r :=
  fun κ => PeriodicGridSobolev.GridH.mk (comp u κ.1.1 κ.1.2)

theorem recOf_ofRec {r : ℕ} {u : Grid N → MetricRec} (hu : IsSymRec u) : recOf (ofRec r u) = u := by
  funext x μ ν
  show comp u (upperOf μ ν).1.1 (upperOf μ ν).1.2 x = u x μ ν
  rw [comp_upperOf hu μ ν]
  rfl

theorem ofRec_add (r : ℕ) (u w : Grid N → MetricRec) : ofRec r (u + w) = ofRec r u + ofRec r w :=
  rfl

theorem finiteWords_isSymRec_add {u w : Grid N → MetricRec} (hu : IsSymRec u) (hw : IsSymRec w) :
    IsSymRec (u + w) := fun x μ ν => by simp only [Pi.add_apply, hu x μ ν, hw x μ ν]

/-- The triangle inequality of the `X^s_h` norm of symmetric records, up to the factor `√20`
(through the equivalent writer norm). -/
theorem finiteWords_Xnorm_add_le (s : ℕ) {q p v w : Grid N → MetricRec} (hq : IsSymRec q)
    (hp : IsSymRec p) (hv : IsSymRec v) (hw : IsSymRec w) :
    Xnorm s (q + p) (v + w) ≤ Real.sqrt (2 * Fintype.card Upper) * (Xnorm s q v + Xnorm s p w) := by
  set X1 : XS N s := (ofRec (s + 1) q, ofRec s v)
  set X2 : XS N s := (ofRec (s + 1) p, ofRec s w)
  have h1 := Xnorm_le_norm s (X1 + X2)
  have e1 : recOf (X1 + X2).1 = q + p := by
    show recOf (ofRec (s + 1) q + ofRec (s + 1) p) = q + p
    rw [← ofRec_add, recOf_ofRec (finiteWords_isSymRec_add hq hp)]
  have e2 : recOf (X1 + X2).2 = v + w := by
    show recOf (ofRec s v + ofRec s w) = v + w
    rw [← ofRec_add, recOf_ofRec (finiteWords_isSymRec_add hv hw)]
  rw [e1, e2] at h1
  have n1 := norm_le_Xnorm s X1
  have n2 := norm_le_Xnorm s X2
  have f1 : recOf X1.1 = q := recOf_ofRec hq
  have f2 : recOf X1.2 = v := recOf_ofRec hv
  have f3 : recOf X2.1 = p := recOf_ofRec hp
  have f4 : recOf X2.2 = w := recOf_ofRec hw
  rw [f1, f2] at n1
  rw [f3, f4] at n2
  calc Xnorm s (q + p) (v + w) ≤ Real.sqrt (2 * Fintype.card Upper) * ‖X1 + X2‖ := h1
    _ ≤ Real.sqrt (2 * Fintype.card Upper) * (‖X1‖ + ‖X2‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2 * Fintype.card Upper) * (Xnorm s q v + Xnorm s p w) :=
        mul_le_mul_of_nonneg_left (add_le_add n1 n2) (Real.sqrt_nonneg _)


end Records

set_option maxHeartbeats 4000000 in
-- the comparison of a word with the exact history and the convergence assembly in one statement
/-- **The Einstein clause of `thm:supp-open-finite-words`: every resulting history has the same
Einstein limit.**  Fix `s ≥ 6` and constants `c, c₀ ≥ 0`.  There is a slab `T > 0` such that for
every horizon `T₁ ∈ (0, T]` there are `εs > 0`, rate constants and `n₀`, independent of the cutoff,
such that (on `[0, T₁]`, for bank words of horizon `T₁`) for every harmonic vacuum datum
`(γ, K) ∈ D_s(ε)`, `ε ≤ εs`, with compatible preparation `V₀` and harmonic vacuum development
`(Q, V, A)` (the same as for the central writer, `supp_law_einstein`; it satisfies the
normal-row equations and `G(g) = 0` on `[0, T]`), for arbitrary marks `B_n` of the closed ball and
every sequence of bank words on the cutoffs `N = n + 1` whose scaled endpoint jets obey the
precision convention `η = c ε h^{s+10}` and whose starting finite record differs from the
compatible preparation (the samples of `Q₀`, `V₀`) by at most `c₀ ε h⁴` in `X^s_h`, the
interpolated word records converge on `[0, T]` to `(Q, V, A)`, at the metric rate `O(h ε)` in
`H^{s-1}`, `H^{s-2}`, `H^{s-3}` for `n ≥ n₀`. -/
theorem finite_words_einstein (s : ℕ) (hs : 6 ≤ s) (cη c₀ : ℝ) (hcη : 0 ≤ cη) (hc₀ : 0 ≤ c₀) :
    ∃ T > 0, ∀ T₁, 0 < T₁ → T₁ ≤ T → ∃ εs > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∃ Cε ≥ 0, ∃ CB ≥ 0,
    ∃ CW ≥ 0, ∃ n₀ : ℕ,
    ∀ (Q₀ Kr : C(T3, MetricRec)) (Qd Kd : Fin 3 → C(T3, MetricRec))
      (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      DsData s Q₀ Kr Qd Kd Qdd → dataSize s Q₀ Kr ≤ ε → ε ≤ εs →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
      ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd' Vd' : ℝ → Fin 3 → C(T3, MetricRec))
        (Qdd' : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
        (∀ t ∈ Set.Icc 0 T₁, IsContJet (Q t) (V t) (Qd' t) (Vd' t) (Qdd' t) ∧
          (∀ y (κ : Upper), normalRow (Q t y) (V t y) (A t y) (fun i => Qd' t i y)
            (fun i => Vd' t i y) (fun i j => Qdd' t i j y) κ.1.1 κ.1.2 = 0) ∧
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
            ∀ n, n₀ ≤ n → ∀ κ : Upper,
              sn (s - 1) ⇑(cmp (interpRec ((bankWord s T₁ (β n)).path 0 t)) κ.1.1 κ.1.2 -
                cmp (Q t) κ.1.1 κ.1.2) ≤
                ((C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε + CW * ε) * ((n : ℝ) + 1)⁻¹ ∧
              sn (s - 2) ⇑(cmp (interpRec ((bankWord s T₁ (β n)).path 1 t)) κ.1.1 κ.1.2 -
                cmp (V t) κ.1.1 κ.1.2) ≤
                ((C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε + CW * ε) * ((n : ℝ) + 1)⁻¹ ∧
              sn (s - 3) ⇑(cmp (interpRec ((bankWord s T₁ (β n)).path 2 t)) κ.1.1 κ.1.2 -
                cmp (A t) κ.1.1 κ.1.2) ≤
                ((C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε + CW * ε) * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨εs1, hεs1, T, hT, TB, hTB, K, hK, C, hC, Cε, hCε, CB, hCB, hLE⟩ := supp_law_einstein s hs
  refine ⟨T, hT, fun T₁ hT₁ hT₁T => ?_⟩
  obtain ⟨ε₀, hε₀, N₀, CF, hCF, hFW⟩ := finite_words_bounds s (by omega) T₁ hT₁ cη hcη
  obtain ⟨δD, hδD, KD, hKD, hDiff⟩ := law_difference s (s - 1) (by omega) (by omega)
  obtain ⟨δA, hδA, KA, hKA, hAcc⟩ := lawAccel_diff_bound s (s - 2) (by omega) (by omega)
  set S20 : ℝ := Real.sqrt (2 * Fintype.card Upper)
  have hS20 : 0 ≤ S20 := Real.sqrt_nonneg _
  set cw : ℝ := S20 * (CB + c₀) + 1
  have hcw : 1 ≤ cw := by have : 0 ≤ S20 * (CB + c₀) := by positivity
                          simp only [cw]; linarith
  set δ : ℝ := min δD δA
  have hδ : 0 < δ := lt_min hδD hδA
  set εs : ℝ := min εs1 (min (ε₀ / cw) (δ / (CF * cw + CB + 1)))
  have hεs : 0 < εs := by
    have : 0 < cw := by linarith
    positivity
  set D1 : ℝ := 3 * Real.exp (KD * T₁) * (3 * c₀ + KD * (T₁ * (CF * cw)))
  have hD1 : 0 ≤ D1 := by positivity
  set Dt : ℝ := D1 + (CF * cw + KA * D1)
  have hDt : 0 ≤ Dt := by positivity
  set Sq : ℝ := Real.sqrt (pc (s - 1)) + Real.sqrt (pc (s - 2)) + Real.sqrt (pc (s - 3)) +
    Real.sqrt (pc 2) + 1
  have hSq : ∀ r ∈ ({s - 1, s - 2, s - 3, 2} : Finset ℕ), Real.sqrt (pc r) ≤ Sq := by
    intro r hr
    have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
    have := Real.sqrt_nonneg (pc (s - 3)); have := Real.sqrt_nonneg (pc 2)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [Sq] <;> linarith
  have hSq0 : 0 ≤ Sq := by
    have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
    have := Real.sqrt_nonneg (pc (s - 3)); have := Real.sqrt_nonneg (pc 2)
    simp only [Sq]; linarith
  refine ⟨εs, hεs, K, hK, C, hC, Cε, hCε, CB, hCB, Sq * Dt, by positivity, N₀,
    fun Q₀ Kr Qd Kd Qdd ε hD hsz hεε => ?_⟩
  have hε0 : 0 ≤ ε := (add_nonneg (ccoordSum_nonneg _ _ _) (ccoordSum_nonneg _ _ _)).trans hsz
  have hεs1' : ε ≤ εs1 := hεε.trans (min_le_left _ _)
  have hεcw : cw * ε ≤ ε₀ := by
    have h1 : ε ≤ ε₀ / cw := hεε.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by linarith)] at h1
    linarith
  have hεδ : (CF * cw + CB) * ε ≤ δ := by
    have h1 : ε ≤ δ / (CF * cw + CB + 1) := hεε.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    have : (CF * cw + CB) * ε ≤ ε * (CF * cw + CB + 1) := by nlinarith
    linarith
  have hCFδ : CF * (cw * ε) ≤ δ := by
    have : 0 ≤ CB * ε := by positivity
    nlinarith
  have hCBδ : CB * ε ≤ δ := by
    have : 0 ≤ CF * cw * ε := by positivity
    nlinarith
  obtain ⟨V₀, hV₀, q, v, -, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, hcen, hfam⟩ :=
    hLE Q₀ Kr Qd Kd Qdd ε hD hsz hεs1'
  refine ⟨V₀, hV₀, Q, V, A, Qd', Vd', Qdd', hQ0, hV0, fun t ht => ?_,
    fun b B hB hb β hprec hstart t ht => ?_⟩
  · obtain ⟨-, -, -, h8, h9, -, h13⟩ := hcen t ⟨ht.1, ht.2.trans hT₁T⟩
    exact ⟨h8, h9, h13⟩
  obtain ⟨qB, vB, hsolB, -, hbndB, -, hconv⟩ := hfam b B hB hb
  have hTTB : T₁ ≤ TB := hT₁T.trans hTB
  -- the comparison of each word with the exact history from the samples
  have hcmp : ∀ n, N₀ ≤ n → ∀ τ ∈ Set.Icc 0 T₁,
      Xnorm (s - 1) ((bankWord s T₁ (β n)).path 0 τ - qB n τ)
        ((bankWord s T₁ (β n)).path 1 τ - vB n τ) ≤ D1 * ε * ((n : ℝ) + 1)⁻¹ ∧
      ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3) (cx (comp ((bankWord s T₁ (β n)).path 2 τ -
        lawAccel (B n) (qB n τ) (vB n τ)) κ.1.1 κ.1.2)) ≤
        (CF * cw + KA * D1) * ε * ((n : ℝ) + 1)⁻¹ := by
    intro n hn τ hτ
    set W := bankWord s T₁ (β n)
    set h : ℝ := 1 / (((n + 1 : ℕ) : ℝ)) with hhdef
    have hh : h = ((n : ℝ) + 1)⁻¹ := by rw [hhdef, Nat.cast_succ, one_div]
    have hh0 : 0 < h := by rw [hh]; positivity
    have hh1 : h ≤ 1 := by
      rw [hh]; exact inv_le_one_of_one_le₀ (by have := (n.cast_nonneg : (0 : ℝ) ≤ n); linarith)
    have hmark : IsMark (1 / 48) (B n) := (hB n).mono (hb n)
    -- the initial record
    have hτ0 : (0 : ℝ) ∈ Set.Icc 0 TB := ⟨le_rfl, hT₁.le.trans hTTB⟩
    obtain ⟨hsolA, hq0, hv0⟩ := hsolB n
    have hsq0 : IsSymRec (sampleRec (n + 1) ⇑Q₀) := hq0 ▸ (hsolA 0 hτ0).1
    have hsv0 : IsSymRec (sampleRec (n + 1) ⇑V₀) := hv0 ▸ (hsolA 0 hτ0).2.1
    have hW0 : W.path 0 0 = recOf (β n 0 0) := by
      have := bankWord_path_node s hT₁ (β n) (j := 0) (Nat.zero_le _) 0
      simpa using this
    have hW1 : W.path 1 0 = recOf (β n 0 1) := by
      have := bankWord_path_node s hT₁ (β n) (j := 0) (Nat.zero_le _) 1
      simpa using this
    have hstartn := hstart n
    have hdsym0 : IsSymRec (recOf (β n 0 0) - sampleRec (n + 1) ⇑Q₀) :=
      isSymRec_sub (isSymRec_recOf _) hsq0
    have hdsym1 : IsSymRec (recOf (β n 0 1) - sampleRec (n + 1) ⇑V₀) :=
      isSymRec_sub (isSymRec_recOf _) hsv0
    have hsamp : Xnorm s (sampleRec (n + 1) ⇑Q₀) (sampleRec (n + 1) ⇑V₀) ≤ CB * ε := by
      have := (hbndB n 0 ⟨le_rfl, hT.le⟩).1
      rwa [hq0, hv0] at this
    have hh4 : h ^ 4 ≤ 1 := pow_le_one₀ hh0.le hh1
    have hstart1 : Xnorm s (recOf (β n 0 0)) (recOf (β n 0 1)) ≤ cw * ε := by
      have e0 : recOf (β n 0 0) = sampleRec (n + 1) ⇑Q₀ + (recOf (β n 0 0) - sampleRec (n + 1) ⇑Q₀) :=
        (add_sub_cancel _ _).symm
      have e1 : recOf (β n 0 1) = sampleRec (n + 1) ⇑V₀ + (recOf (β n 0 1) - sampleRec (n + 1) ⇑V₀) :=
        (add_sub_cancel _ _).symm
      rw [e0, e1]
      refine (finiteWords_Xnorm_add_le s hsq0 hdsym0 hsv0 hdsym1).trans ?_
      have hd : c₀ * ε * h ^ 4 ≤ c₀ * ε := by
        have : 0 ≤ c₀ * ε := by positivity
        nlinarith
      calc S20 * (Xnorm s (sampleRec (n + 1) ⇑Q₀) (sampleRec (n + 1) ⇑V₀) +
            Xnorm s (recOf (β n 0 0) - sampleRec (n + 1) ⇑Q₀)
              (recOf (β n 0 1) - sampleRec (n + 1) ⇑V₀)) ≤ S20 * (CB * ε + c₀ * ε) := by
            gcongr
            exact hstartn.trans hd
        _ = S20 * (CB + c₀) * ε := by ring
        _ ≤ cw * ε := by gcongr; simp only [cw]; linarith
    have hprecn : BankPrecise s (B n) (stepOf (n + 1) T₁)
        (cη * (cw * ε) * (1 / (((n + 1 : ℕ) : ℝ))) ^ (s + 10)) (β n) (numCells (n + 1) T₁) := by
      refine (hprec n).mono ?_
      have : ε ≤ cw * ε := by nlinarith
      gcongr
    obtain ⟨-, hglob, -, -⟩ := hFW (n + 1) (by omega) (B n) hmark (β n) (cw * ε)
      (by positivity) hεcw hstart1 hprecn
    -- the forced pair
    have hsW0 : ∀ τ', IsSymRec (W.path 0 τ') :=
      LawWord.isSymRec_path W (fun j i => isSymRec_recOf (bankLetter (stepOf (n + 1) T₁) (β n) j i)) 0
    have hsW1 : ∀ τ', IsSymRec (W.path 1 τ') :=
      LawWord.isSymRec_path W (fun j i => isSymRec_recOf (bankLetter (stepOf (n + 1) T₁) (β n) j i)) 1
    have hWmono := bankWord_node_strictMono s hT₁ (β n)
    have hWjm := bankWord_jetsMatch s hT₁ (β n)
    have hpair : IsLawForcedPair (B n) s δD T₁ (W.path 0) (qB n) (W.path 1) (vB n) (W.residual (B n))
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
      · exact (hbndB n τ' ⟨hτ'.1, hτ'.2.trans hT₁T⟩).1.trans (hCBδ.trans (min_le_left _ _))
    have hfc : ContinuousOn (W.residual (B n)) (Set.Icc 0 T₁) := fun τ' hτ' =>
      (hglob τ' hτ').2.2.1.continuousAt.continuousWithinAt
    have hd := hDiff (n + 1) (B n) T₁ (W.path 0) (qB n) (W.path 1) (vB n) (W.residual (B n))
      (fun _ => 0) hmark hpair hfc continuousOn_const τ hτ
    -- the starting difference
    have hX0 : Xnorm (s - 1) (W.path 0 0 - qB n 0) (W.path 1 0 - vB n 0) ≤ c₀ * ε * h := by
      rw [hW0, hW1, hq0, hv0]
      refine (lawDiff_Xnorm_mono (by omega) _ _).trans (hstartn.trans ?_)
      have : h ^ 4 ≤ h := by
        calc h ^ 4 ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by norm_num)
          _ = h := pow_one h
      have : 0 ≤ c₀ * ε := by positivity
      nlinarith
    -- the integrated defect
    have hI : (∫ σ in (0)..τ, Fnorm (s - 1) (W.residual (B n) σ - (fun _ => 0) σ)) ≤
        T₁ * (CF * (cw * ε) * h) := by
      have hn' := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := τ)
        (f := fun σ => Fnorm (s - 1) (W.residual (B n) σ - (fun _ => 0) σ))
        (C := CF * (cw * ε) * h) fun x hx => by
          rw [uIoc_of_le hτ.1] at hx
          have hxT : x ∈ Set.Icc 0 T₁ := ⟨hx.1.le, hx.2.trans hτ.2⟩
          rw [Real.norm_eq_abs, abs_of_nonneg (Fnorm_nonneg _ _), sub_zero]
          refine (lawDiff_Fnorm_mono (by omega) _).trans ((hglob x hxT).2.1.trans ?_)
          have : h ^ 5 ≤ h := by
            calc h ^ 5 ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by norm_num)
              _ = h := pow_one h
          have : 0 ≤ CF * (cw * ε) := by positivity
          nlinarith
      rw [sub_zero, abs_of_nonneg hτ.1] at hn'
      have h1 := (Real.le_norm_self _).trans hn'
      have h2 : CF * (cw * ε) * h * τ ≤ T₁ * (CF * (cw * ε) * h) := by
        have : 0 ≤ CF * (cw * ε) * h := by positivity
        nlinarith [hτ.2]
      exact h1.trans h2
    have hdiff : Xnorm (s - 1) (W.path 0 τ - qB n τ) (W.path 1 τ - vB n τ) ≤ D1 * ε * h := by
      refine hd.trans ?_
      have hexp : Real.exp (KD * τ) ≤ Real.exp (KD * T₁) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 hKD)
      have hin : 0 ≤ ∫ σ in (0)..τ, Fnorm (s - 1) (W.residual (B n) σ - (fun _ => 0) σ) :=
        intervalIntegral.integral_nonneg hτ.1 fun _ _ => Fnorm_nonneg _ _
      calc 3 * Real.exp (KD * τ) * (3 * Xnorm (s - 1) (W.path 0 0 - qB n 0) (W.path 1 0 - vB n 0) +
            KD * ∫ σ in (0)..τ, Fnorm (s - 1) (W.residual (B n) σ - (fun _ => 0) σ)) ≤
            3 * Real.exp (KD * T₁) * (3 * (c₀ * ε * h) + KD * (T₁ * (CF * (cw * ε) * h))) := by
            have hX0n := Xnorm_nonneg (s - 1) (W.path 0 0 - qB n 0) (W.path 1 0 - vB n 0)
            refine mul_le_mul (mul_le_mul_of_nonneg_left hexp (by norm_num))
              (add_le_add (by linarith [hX0]) (mul_le_mul_of_nonneg_left hI hKD))
              (add_nonneg (by positivity) (mul_nonneg hKD hin)) (by positivity)
        _ = D1 * ε * h := by simp only [D1]; ring
    refine ⟨by rw [← hh]; exact hdiff, fun κ => ?_⟩
    -- the acceleration
    have e : comp (W.path 2 τ - lawAccel (B n) (qB n τ) (vB n τ)) κ.1.1 κ.1.2 =
        comp (W.residual (B n) τ) κ.1.1 κ.1.2 +
          comp (lawAccel (B n) (W.path 0 τ) (W.path 1 τ) - lawAccel (B n) (qB n τ) (vB n τ))
            κ.1.1 κ.1.2 := by
      funext x
      simp only [comp, LawWord.residual, Pi.sub_apply, Pi.add_apply]
      ring
    rw [e, cx_add]
    refine (PeriodicGridSobolev.Moser.sobNorm_add_le _ _ _).trans ?_
    have a1 : PeriodicGridSobolev.sobNorm (s - 3) (cx (comp (W.residual (B n) τ) κ.1.1 κ.1.2)) ≤
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
    have hBs : Xnorm s (qB n τ) (vB n τ) ≤ δA :=
      (hbndB n τ ⟨hτ.1, hτ.2.trans hT₁T⟩).1.trans (hCBδ.trans (min_le_right _ _))
    have hτB : τ ∈ Set.Icc 0 TB := ⟨hτ.1, hτ.2.trans hTTB⟩
    have a2 := hAcc (n + 1) (B n) (W.path 0 τ) (qB n τ) (W.path 1 τ) (vB n τ) hmark (hsW0 τ)
      (hsolA τ hτB).1 (hsW1 τ) (hsolA τ hτB).2.1 hWs hBs κ
    rw [show s - 2 - 1 = s - 3 by omega] at a2
    have a3 : Xnorm (s - 2) (W.path 0 τ - qB n τ) (W.path 1 τ - vB n τ) ≤ D1 * ε * h :=
      (lawDiff_Xnorm_mono (by omega) _ _).trans hdiff
    have hD1h : 0 ≤ KA := hKA
    calc _ ≤ CF * cw * ε * h + KA * (D1 * ε * h) := add_le_add a1 (a2.trans (by gcongr))
      _ = (CF * cw + KA * D1) * ε * ((n : ℝ) + 1)⁻¹ := by rw [← hh]; ring
  -- the convergence
  obtain ⟨c1, c2, c3, -, -, -, crates⟩ := hconv t ⟨ht.1, ht.2.trans hT₁T⟩
  have hτB : t ∈ Set.Icc 0 TB := ⟨ht.1, ht.2.trans hTTB⟩
  have hsP : ∀ n k, IsSymRec ((bankWord s T₁ (β n)).path k t) := fun n k =>
    LawWord.isSymRec_path (bankWord s T₁ (β n))
      (fun j i => isSymRec_recOf (bankLetter (stepOf (n + 1) T₁) (β n) j i)) k t
  have hsqB : ∀ n, IsSymRec (qB n t) := fun n => ((hsolB n).1 t hτB).1
  have hsvB : ∀ n, IsSymRec (vB n t) := fun n => ((hsolB n).1 t hτB).2.1
  set D : ℝ := Dt * ε
  have hD0 : 0 ≤ D := by positivity
  have hn0 : ∀ n : ℕ, (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := fun n => by positivity
  have hD1D : ∀ n : ℕ, D1 * ε * ((n : ℝ) + 1)⁻¹ ≤ D * ((n : ℝ) + 1)⁻¹ := fun n => by
    have : D1 ≤ Dt := by have : 0 ≤ CF * cw + KA * D1 := by positivity
                         simp only [Dt]; linarith
    have := mul_le_mul_of_nonneg_right this hε0
    exact mul_le_mul_of_nonneg_right (by simp only [D]; linarith) (hn0 n)
  have hDaD : ∀ n : ℕ, (CF * cw + KA * D1) * ε * ((n : ℝ) + 1)⁻¹ ≤ D * ((n : ℝ) + 1)⁻¹ :=
    fun n => by
      have : CF * cw + KA * D1 ≤ Dt := by simp only [Dt]; linarith
      have := mul_le_mul_of_nonneg_right this hε0
      exact mul_le_mul_of_nonneg_right (by simp only [D]; linarith) (hn0 n)
  have gq : ∀ n, N₀ ≤ n → ∀ (κ : Upper) (r : ℕ), r ≤ s →
      PeriodicGridSobolev.sobNorm r (cx (comp ((bankWord s T₁ (β n)).path 0 t - qB n t)
        κ.1.1 κ.1.2)) ≤ D * ((n : ℝ) + 1)⁻¹ := fun n hn κ r hr => by
    have h1 := sobNorm_q_le (s - 1) (isSymRec_sub (hsP n 0) (hsqB n))
      ((bankWord s T₁ (β n)).path 1 t - vB n t) κ.1.1 κ.1.2 (r := r) (by omega)
    exact h1.trans (((hcmp n hn t ht).1).trans (hD1D n))
  have gv : ∀ n, N₀ ≤ n → ∀ (κ : Upper) (r : ℕ), r ≤ s - 1 →
      PeriodicGridSobolev.sobNorm r (cx (comp ((bankWord s T₁ (β n)).path 1 t - vB n t)
        κ.1.1 κ.1.2)) ≤ D * ((n : ℝ) + 1)⁻¹ := fun n hn κ r hr => by
    have h1 := sobNorm_v_le (s - 1) ((bankWord s T₁ (β n)).path 0 t - qB n t)
      (isSymRec_sub (hsP n 1) (hsvB n)) κ.1.1 κ.1.2 hr
    exact h1.trans (((hcmp n hn t ht).1).trans (hD1D n))
  have ga : ∀ n, N₀ ≤ n → ∀ (κ : Upper) (r : ℕ), r ≤ s - 3 →
      PeriodicGridSobolev.sobNorm r (cx (comp ((bankWord s T₁ (β n)).path 2 t -
        lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2)) ≤ D * ((n : ℝ) + 1)⁻¹ :=
    fun n hn κ r hr =>
      ((PeriodicGridSobolev.Moser.sobNorm_mono hr _).trans ((hcmp n hn t ht).2 κ)).trans (hDaD n)
  have mulD : ∀ (r : ℕ) (n : ℕ) (x : ℝ), x ≤ D * ((n : ℝ) + 1)⁻¹ →
      Real.sqrt (pc r) * x ≤ Real.sqrt (pc r) * D * ((n : ℝ) + 1)⁻¹ := fun r n x hx => by
    calc Real.sqrt (pc r) * x ≤ Real.sqrt (pc r) * (D * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg (pc r))
      _ = _ := by ring
  have hrate : ∀ c : ℝ, Tendsto (fun n : ℕ => c * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    intro c
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simp only [one_div] at this
    simpa using this.const_mul c
  refine ⟨?_, ?_, ?_, fun n hn κ => ⟨?_, ?_, ?_⟩⟩
  · refine lawLimit_tendsto_of_upper_rate c1
      (fun n y μ ν => interpRec_symm (hsP n 0) y μ ν)
      (fun n y μ ν => interpRec_symm (hsqB n) y μ ν) _ (hrate (Real.sqrt (pc 2) * D)) N₀
      fun n hn κ => ?_
    have h := lawLimit_interp_diff 2 ((bankWord s T₁ (β n)).path 0 t) (qB n t) κ.1.1 κ.1.2
    exact ⟨h.1, h.2.trans (mulD 2 n _ (gq n hn κ 2 (by omega)))⟩
  · refine lawLimit_tendsto_of_upper_rate c2
      (fun n y μ ν => interpRec_symm (hsP n 1) y μ ν)
      (fun n y μ ν => interpRec_symm (hsvB n) y μ ν) _ (hrate (Real.sqrt (pc 2) * D)) N₀
      fun n hn κ => ?_
    have h := lawLimit_interp_diff 2 ((bankWord s T₁ (β n)).path 1 t) (vB n t) κ.1.1 κ.1.2
    exact ⟨h.1, h.2.trans (mulD 2 n _ (gv n hn κ 2 (by omega)))⟩
  · refine lawLimit_tendsto_of_upper_rate c3
      (fun n y μ ν => interpRec_symm (hsP n 2) y μ ν)
      (fun n y μ ν => interpRec_symRec_symm _ y μ ν) _ (hrate (Real.sqrt (pc 2) * D)) N₀
      fun n hn κ => ?_
    show MemH 2 ⇑(cmp (interpRec ((bankWord s T₁ (β n)).path 2 t)) κ.1.1 κ.1.2 -
        cmp (interpRec (symRec (lawAccel (B n) (qB n t) (vB n t)))) κ.1.1 κ.1.2) ∧
      sn 2 ⇑(cmp (interpRec ((bankWord s T₁ (β n)).path 2 t)) κ.1.1 κ.1.2 -
        cmp (interpRec (symRec (lawAccel (B n) (qB n t) (vB n t)))) κ.1.1 κ.1.2) ≤
        Real.sqrt (pc 2) * D * ((n : ℝ) + 1)⁻¹
    rw [cmp_interpRec_symRec]
    have h := lawLimit_interp_diff 2 ((bankWord s T₁ (β n)).path 2 t)
      (lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2
    exact ⟨h.1, h.2.trans (mulD 2 n _ (ga n hn κ 2 (by omega)))⟩
  all_goals
    have hn' : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    have e2 : ((C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε + Sq * Dt * ε) *
        ((n : ℝ) + 1)⁻¹ = (C * Real.exp (K * t) * (1 + t) * Cε + CB) * ε * ((n : ℝ) + 1)⁻¹ +
          Sq * D * ((n : ℝ) + 1)⁻¹ := by simp only [D]; ring
    rw [e2]
  · have e : cmp (interpRec ((bankWord s T₁ (β n)).path 0 t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2 =
        (cmp (interpRec (qB n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) +
        (cmp (interpRec ((bankWord s T₁ (β n)).path 0 t)) κ.1.1 κ.1.2 -
          cmp (interpRec (qB n t)) κ.1.1 κ.1.2) := by
      abel
    rw [e]
    have h := lawLimit_interp_diff (s - 1) ((bankWord s T₁ (β n)).path 0 t) (qB n t) κ.1.1 κ.1.2
    refine (lawLimit_sn_add_le _ _ h.1).trans ?_
    have r1 := (crates n κ).1
    have r2 := h.2.trans (mulD (s - 1) n _ (gq n hn κ (s - 1) (by omega)))
    have r3 : Real.sqrt (pc (s - 1)) * D * ((n : ℝ) + 1)⁻¹ ≤ Sq * D * ((n : ℝ) + 1)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hSq _ (by simp)) hD0) hn'
    linarith
  · have e : cmp (interpRec ((bankWord s T₁ (β n)).path 1 t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2 =
        (cmp (interpRec (vB n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) +
        (cmp (interpRec ((bankWord s T₁ (β n)).path 1 t)) κ.1.1 κ.1.2 -
          cmp (interpRec (vB n t)) κ.1.1 κ.1.2) := by
      abel
    rw [e]
    have h := lawLimit_interp_diff (s - 2) ((bankWord s T₁ (β n)).path 1 t) (vB n t) κ.1.1 κ.1.2
    refine (lawLimit_sn_add_le _ _ h.1).trans ?_
    have r1 := (crates n κ).2.1
    have r2 := h.2.trans (mulD (s - 2) n _ (gv n hn κ (s - 2) (by omega)))
    have r3 : Real.sqrt (pc (s - 2)) * D * ((n : ℝ) + 1)⁻¹ ≤ Sq * D * ((n : ℝ) + 1)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hSq _ (by simp)) hD0) hn'
    linarith
  · have e : cmp (interpRec ((bankWord s T₁ (β n)).path 2 t)) κ.1.1 κ.1.2 - cmp (A t) κ.1.1 κ.1.2 =
        (cmp (interpRec (lawAccel (B n) (qB n t) (vB n t))) κ.1.1 κ.1.2 -
          cmp (A t) κ.1.1 κ.1.2) +
        (cmp (interpRec ((bankWord s T₁ (β n)).path 2 t)) κ.1.1 κ.1.2 -
          cmp (interpRec (lawAccel (B n) (qB n t) (vB n t))) κ.1.1 κ.1.2) := by
      abel
    rw [e]
    have h := lawLimit_interp_diff (s - 3) ((bankWord s T₁ (β n)).path 2 t)
      (lawAccel (B n) (qB n t) (vB n t)) κ.1.1 κ.1.2
    refine (lawLimit_sn_add_le _ _ h.1).trans ?_
    have r1 := (crates n κ).2.2
    have r2 := h.2.trans (mulD (s - 3) n _ (ga n hn κ (s - 3) le_rfl))
    have r3 : Real.sqrt (pc (s - 3)) * D * ((n : ℝ) + 1)⁻¹ ≤ Sq * D * ((n : ℝ) + 1)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hSq _ (by simp)) hD0) hn'
    linarith


/-! ### Non-vacuity -/

section NonVacuity

variable {N : ℕ} [NeZero N]

/-- The exact bank of a source `X₀` starts at `X₀`. -/
theorem exactBank_start (s : ℕ) (B : Upper → Upper → ℝ) (τ : ℝ) (X₀ : XS N s) :
    recOf (exactBank s B τ X₀ 0 0) = recOf X₀.1 ∧ recOf (exactBank s B τ X₀ 0 1) = recOf X₀.2 := by
  refine ⟨rfl, ?_⟩
  show recOf ((gridWriter s B).qj 1 X₀) = recOf X₀.2
  rw [TaylorHermiteResidual.Writer.qj_one]
  rfl

/-- Non-vacuity of the hypotheses of `finite_words_einstein`: for symmetric records `u, v` (the
samples of the compatible preparation), the exact bank started at `(u, v)` has zero starting
perturbation and satisfies the precision convention with every tolerance `η ≥ 0`. -/
theorem exactBank_einstein_hyps (s : ℕ) (B : Upper → Upper → ℝ) (τ η : ℝ) (hη : 0 ≤ η) (J : ℕ)
    {u v : Grid N → MetricRec} (hu : IsSymRec u) (hv : IsSymRec v) :
    Xnorm s (recOf (exactBank s B τ (ofRec (s + 1) u, ofRec s v) 0 0) - u)
      (recOf (exactBank s B τ (ofRec (s + 1) u, ofRec s v) 0 1) - v) = 0 ∧
    BankPrecise s B τ η (exactBank s B τ (ofRec (s + 1) u, ofRec s v)) J := by
  obtain ⟨e0, e1⟩ := exactBank_start s B τ (ofRec (s + 1) u, ofRec s v)
  refine ⟨?_, (exactBank_precise s B τ _ J).mono hη⟩
  rw [e0, e1]
  show Xnorm s (recOf (ofRec (s + 1) u) - u) (recOf (ofRec s v) - v) = 0
  rw [recOf_ofRec hu, recOf_ofRec hv, sub_self, sub_self]
  exact lawCost_Xnorm_zero s

/-- Non-vacuity of `finite_words_bounds`: for every horizon, on every fine grid and for every
small initial record `X₀`, the exact bank started at `X₀` satisfies all its hypotheses (with the
open writer `B = 0` and precision `η = 0`), so its conclusions apply. -/
example (s : ℕ) (hs : 5 ≤ s) (T : ℝ) (hT : 0 < T) :
    ∃ ε₀ > 0, ∃ N₀ : ℕ, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N], N₀ ≤ N → ∀ X₀ : XS N s,
      Xnorm s (recOf X₀.1) (recOf X₀.2) ≤ ε₀ →
      ∀ t ∈ Icc 0 T, (bankWord s T (exactBank s (fun _ _ => 0) (stepOf N T) X₀)).recNorm s t ≤
        C * Xnorm s (recOf X₀.1) (recOf X₀.2) := by
  obtain ⟨ε₀, hε₀, N₀, C, hC, h⟩ := finite_words_bounds s hs T hT 0 le_rfl
  refine ⟨ε₀, hε₀, N₀, C, hC, fun N _ hN X₀ hX t ht => ?_⟩
  obtain ⟨e0, e1⟩ := exactBank_start s (fun _ _ => 0) (stepOf N T) X₀
  have hstart : Xnorm s (recOf (exactBank s (fun _ _ => 0) (stepOf N T) X₀ 0 0))
      (recOf (exactBank s (fun _ _ => 0) (stepOf N T) X₀ 0 1)) ≤
      Xnorm s (recOf X₀.1) (recOf X₀.2) := by rw [e0, e1]
  exact ((h N hN (fun _ _ => 0) isMark_zero_lawWord _ _ (Xnorm_nonneg _ _ _) hX hstart
    ((exactBank_precise s _ _ X₀ _).mono (by simp))).2.1 t ht).1

end NonVacuity

end

end RenewalGeometry.OpenWriterFiniteWords
