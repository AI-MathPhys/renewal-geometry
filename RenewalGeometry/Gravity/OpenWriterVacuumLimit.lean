/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterLimitRegularity

/-!
# The vacuum Einstein limit of the open writer (`thm:supp-open-einstein`)

* `HarmonicPrep Q₀ V₀` — `(Q₀, V₀)` is the harmonic preparation `eq:supp-open-harmonic-initial` of
  slice data `(γ, K)` satisfying the vacuum constraints of `eq:main-open-data-class` (pointwise,
  with classical spatial derivative fields).
* `writer_limit_vacuum` — **`thm:supp-open-einstein`**: for `s ≥ 6`, the whole sequence of
  interpolated writer solutions started from the samples of a small harmonic preparation converges
  (with the metric rate `eq:supp-open-metric-rate` and the curvature rate
  `eq:supp-open-curvature-rate`) to a classical solution of the reduced equation, and its Einstein
  tensor vanishes on `[0, T] × 𝕋³` (`eq:supp-open-vacuum`).
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.OpenWriterLimitRegularity

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterGridBridge RootParityConnector PeriodicGridSobolev.Composition
  HarmonicWriter OpenWriterContinuum HarmonicGaugePropagation ContractedBianchiJet HarmonicDefect

noncomputable section

set_option linter.unusedSectionVars false

/-- **Harmonic preparation of constrained slice data**: `Q₀, V₀` have classical spatial derivative
fields `Qd₀, Qdd₀, Vd₀`, and at every point the space-time 2-jet `(η + Q₀, V₀, ∂Q₀, ∂V₀, ∂∂Q₀)`
is the unit-lapse zero-shift slice jet of slice data `(γ, K)` (with an arbitrary acceleration)
satisfying the harmonic initialization `eq:supp-open-harmonic-initial` and the vacuum constraints
`R(γ) + (tr_γ K)² - |K|²_γ = 0`, `∇_γ^j K_{ji} - ∂ᵢ tr_γ K = 0` of `eq:main-open-data-class`. -/
def HarmonicPrep (Q₀ V₀ : T3 → MetricRec) : Prop :=
  ∃ (Qd₀ Vd₀ : Fin 3 → T3 → MetricRec) (Qdd₀ : Fin 3 → Fin 3 → T3 → MetricRec),
    (∀ i, IsLineDeriv i Q₀ (Qd₀ i)) ∧ (∀ i j, IsLineDeriv i (Qd₀ j) (Qdd₀ i j)) ∧
    (∀ i, IsLineDeriv i V₀ (Vd₀ i)) ∧
    ∀ x, ∃ S : SliceData, S.Valid ∧ S.HarmonicInit ∧ S.hamC = 0 ∧ (∀ i, S.momC i = 0) ∧
      Matrix.of (minkowski + Q₀ x) = S.jet.g ∧ (Matrix.of (minkowski + Q₀ x))⁻¹ = S.jet.G ∧
      Matrix.of (V₀ x) = S.jet.dg 0 ∧ (∀ k, Matrix.of (Qd₀ k x) = S.jet.dg k.succ) ∧
      (∀ k, Matrix.of (Vd₀ k x) = S.jet.ddg 0 k.succ) ∧
      (∀ k l, Matrix.of (Qdd₀ k l x) = S.jet.ddg k.succ l.succ)

theorem isLineDeriv_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {i : Fin 3}
    {F G G' : T3 → E} (hG : IsLineDeriv i F G) (hG' : IsLineDeriv i F G') : G = G' :=
  funext fun x => (hG x).unique (hG' x)

end

/-! ### The curvature rate with the symmetric limit acceleration (copy of
`writer_limit_curvature_rate` that also exports the limits of the acceleration and of the
spatial derivatives) -/

end RenewalGeometry.OpenWriterLimitRegularity

open Finset Filter Topology UnitAddTorus ComplexConjugate
open scoped BigOperators Real

namespace RenewalGeometry.OpenWriterContinuum

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterGridBridge RootParityConnector PeriodicGridSobolev.Composition
  HarmonicWriter

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

attribute [local irreducible] harmA harmB harmC compensatorMap

/-- **`writer_limit_curvature_rate` with the symmetric limit acceleration**: the same statement,
exporting in addition the uniform limits `𝓘_h ∂ₜv → A`, `∂ᵢ𝓘_h q → Qd`, `∂ᵢ𝓘_h v → Vd`,
`∂ᵢ∂ⱼ𝓘_h q → Qdd` and the symmetry of `A`. -/
theorem writer_limit_curvature_rate_sym (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∀ (T : ℝ) (q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec)
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
            (𝓝 (A t)) ∧ (∀ y μ ν, A t y μ ν = A t y ν μ) ∧
          (∀ i, Tendsto (fun n => interpD (q n t) i) atTop (𝓝 (Qd t i))) ∧
          (∀ i, Tendsto (fun n => interpD (v n t) i) atTop (𝓝 (Vd t i))) ∧
          (∀ i j, Tendsto (fun n => interpDD (q n t) i j) atTop (𝓝 (Qdd t i j))) ∧
          IsContJet (Q t) (V t) (Qd t) (Vd t) (Qdd t) ∧
          (∀ y (κ : Upper), normalRow (Q t y) (V t y) (A t y) (fun i => Qd t i y)
            (fun i => Vd t i y) (fun i j => Qdd t i j y) κ.1.1 κ.1.2 = 0) ∧
          (t ∈ Set.Ioo 0 T → ∀ y, HasDerivAt (fun τ => Q τ y) (V t y) t ∧
            HasDerivAt (fun τ => V τ y) (A t y) t) ∧
          (∀ n (κ : Upper),
            sn (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ≤
              C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ ∧
            sn (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ≤
              C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ ∧
            sn (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
              cmp (A t) κ.1.1 κ.1.2) ≤ C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) ∧
          ∀ n (a b c d : Fin 4), ∃ F : CT,
            (∀ y, F y = ((riemOf (pjetField (interpRec (q n t)) (interpRec (v n t))
                (interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t))))
                (interpD (q n t)) (interpD (v n t)) (interpDD (q n t)) y) a b c d -
              riemOf (pjetField (Q t) (V t) (A t) (Qd t) (Vd t) (Qdd t) y) a b c d : ℝ) : ℂ)) ∧
            MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨δW, hδW, K₁, hK₁, C₁, hC₁, K₂, hK₂, C₂, hC₂, hW⟩ := writer_limit_solves s hs
  obtain ⟨δA, hδA, KA, hKA, hacc⟩ := accel_bound s (by omega)
  -- the Lipschitz Moser estimate for the Riemann map, uniform over the indices
  have hR : ∀ e : Fin 4 × Fin 4 × Fin 4 × Fin 4, ∃ δ > 0, ∃ C ≥ 0, ∀ P P' : C(T3, PJet),
      (∀ j, MemH (s - 3) ⇑(ccoord bPJ P j)) → (∀ j, MemH (s - 3) ⇑(ccoord bPJ P' j)) →
      ccoordSum (s - 3) bPJ P ≤ δ → ccoordSum (s - 3) bPJ P' ≤ δ →
      ∃ F : CT, (∀ y, F y = ((riemOf (P y) e.1 e.2.1 e.2.2.1 e.2.2.2 -
        riemOf (P' y) e.1 e.2.1 e.2.2.1 e.2.2.2 : ℝ) : ℂ)) ∧ MemH (s - 3) ⇑F ∧
        sn (s - 3) ⇑F ≤ C * ccoordSum (s - 3) bPJ (P - P') := by
    intro e
    have hdet0 : (Matrix.of (minkowski + (0 : PJet).1)).det ≠ 0 := by
      simpa using det_minkowski_ne
    obtain ⟨p, R, hp⟩ := analyticAt_riemOf e.1 e.2.1 e.2.2.1 e.2.2.2 0 hdet0
    obtain ⟨δ, hδ, C, hC, hm⟩ := cont_moser_lipschitz (s - 3) (by omega) bPJ hp
    refine ⟨δ, hδ, C, hC, fun P P' hP hP' h1 h2 => ?_⟩
    obtain ⟨F, hF, hFm, hFs⟩ := hm P P' hP hP' h1 h2
    exact ⟨F, fun y => by rw [hF y]; simp, hFm, hFs⟩
  choose δR hδR CR hCR hRm using hR
  set δR0 : ℝ := (univ : Finset (Fin 4 × Fin 4 × Fin 4 × Fin 4)).inf' univ_nonempty δR
  have hδR0 : 0 < δR0 := by rw [Finset.lt_inf'_iff]; intro e _; exact hδR e
  have hδR0le : ∀ e, δR0 ≤ δR e := fun e => Finset.inf'_le _ (mem_univ e)
  set CR0 : ℝ := ∑ e, CR e
  have hCR0 : ∀ e, CR e ≤ CR0 := fun e =>
    single_le_sum (f := CR) (fun e _ => hCR e) (mem_univ e)
  have hCR0n : 0 ≤ CR0 := sum_nonneg fun e _ => hCR e
  clear_value δR0 CR0
  -- sizes
  set r := s - 3 with hrdef
  set S : ℝ := 16 * (Real.sqrt (pc r) * (2 + KA) + 6 * Real.sqrt (pc (r + 1)) + 9 * Real.sqrt (pc (r + 2)))
  have hS : 0 ≤ S := by
    simp only [S]
    exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (by linarith)) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
  set δ : ℝ := min (min δW δA) (δR0 / (S + 1))
  have hδ : 0 < δ := lt_min (lt_min hδW hδA) (div_pos hδR0 (by linarith))
  set K : ℝ := K₁ + K₂
  set C : ℝ := C₁ + C₂ + CR0 * 16 * (3 * C₁ + 15 * C₂)
  have hKnn : 0 ≤ K := add_nonneg hK₁ hK₂
  have hCnn : 0 ≤ C := add_nonneg (add_nonneg hC₁ hC₂)
    (mul_nonneg (mul_nonneg hCR0n (by norm_num)) (by linarith))
  refine ⟨δ, hδ, K, hKnn, C, hCnn,
    fun T q v Q₀ V₀ ε hsol hq0 hv0 hQs hVs hQ hV hX0 hXq hεδ => ?_⟩
  have hε0 : 0 ≤ ε := (contTop_nonneg _ _ _).trans hX0
  obtain ⟨Q, V, A, Qd, Vd, Qdd, hQ0, hV0, hP⟩ := hW T q v Q₀ V₀ ε hsol hq0 hv0 hQs hVs hQ hV hX0 hXq
    (hεδ.trans ((min_le_left _ _).trans (min_le_left _ _)))
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
  -- the jet fields
  set Jn : ℕ → C(T3, PJet) := fun n => pjetField (interpRec (q n t)) (interpRec (v n t))
    (interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t))))
    (interpD (q n t)) (interpD (v n t)) (interpDD (q n t))
  set J : C(T3, PJet) := pjetField (Q t) (V t) (A t) (Qd t) (Vd t) (Qdd t)
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
  have hJnS : ∀ n, ccoordSum r bPJ (Jn n) ≤ S * ε := by
    intro n
    have X := hXq n t ht
    have hX0' := Xnorm_nonneg s (q n t) (v n t)
    simp only [Jn]
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
          ((hXq n t ht).trans (hεδ.trans ((min_le_left _ _).trans (min_le_right _ _)))) _ _)
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
        9 * (16 * Real.sqrt (pc (r + 2)) * Xnorm s (q n t) (v n t)) = S * Xnorm s (q n t) (v n t) := by
      simp only [S]; ring
    have := mul_le_mul_of_nonneg_left X hS
    linarith
  -- the rates of each slot (upper components)
  set ρ₁ : ℕ → ℝ := fun n => C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
  set ρ₂ : ℕ → ℝ := fun n => C₂ * Real.exp (K₂ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
  have hρ₁ : ∀ n, 0 ≤ ρ₁ n := fun n => by
    have e : ρ₁ n = (C₁ * Real.exp (K₁ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
      simp only [ρ₁]; ring
    rw [e]; exact mul_nonneg (mul_nonneg hC₁ (Real.exp_pos _).le) (hfac0 n)
  have hρ₂ : ∀ n, 0 ≤ ρ₂ n := fun n => by
    have e : ρ₂ n = (C₂ * Real.exp (K₂ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
      simp only [ρ₂]; ring
    rw [e]; exact mul_nonneg (mul_nonneg hC₂ (Real.exp_pos _).le) (hfac0 n)
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
  -- membership and size of the limit jet
  have hJnm : ∀ n j, MemH r ⇑(ccoord bPJ (Jn n) j) := by
    intro n
    refine memH_pjetField (fun k => (memH_interpRec r _ k).1) (fun k => (memH_interpRec r _ k).1)
      (fun k => (memH_interpRec r _ k).1) (fun i k => (hderQ n i k r).1) (fun i k => (hderV n i k r).1)
      (fun i j k => (hderQQ n i j k r).1)
  have hJm : ∀ j, MemH r ⇑(ccoord bPJ J j) := by
    intro j
    have h1 := hJnm 0 j
    have h2 := (hdiff 0).1 j
    have e : ccoord bPJ (Jn 0 - J) j = ccoord bPJ (Jn 0) j - ccoord bPJ J j := ccoord_sub _ _ _ _
    rw [e] at h2
    exact memH_of_sub h1 h2
  have hJS : ccoordSum r bPJ J ≤ S * ε := by
    have hle : ∀ n, ccoordSum r bPJ J ≤ S * ε + 16 * (3 * ρ₁ n + 15 * ρ₂ n) := by
      intro n
      unfold ccoordSum
      have hk : ∀ j, sn r ⇑(ccoord bPJ J j) ≤ sn r ⇑(ccoord bPJ (Jn n) j) +
          sn r ⇑(ccoord bPJ (Jn n - J) j) := by
        intro j
        have e : ccoord bPJ J j = ccoord bPJ (Jn n) j - ccoord bPJ (Jn n - J) j := by
          rw [ccoord_sub]; abel
        rw [e]
        exact sn_sub_le' (hJnm n j) ((hdiff n).1 j)
      calc ∑ j, sn r ⇑(ccoord bPJ J j)
          ≤ ∑ j, (sn r ⇑(ccoord bPJ (Jn n) j) + sn r ⇑(ccoord bPJ (Jn n - J) j)) :=
            sum_le_sum fun j _ => hk j
        _ = ccoordSum r bPJ (Jn n) + ccoordSum r bPJ (Jn n - J) := by
            rw [sum_add_distrib]; rfl
        _ ≤ S * ε + 16 * (3 * ρ₁ n + 15 * ρ₂ n) := add_le_add (hJnS n) (hdiff n).2
    have hlim : Tendsto (fun n : ℕ => S * ε + 16 * (3 * ρ₁ n + 15 * ρ₂ n)) atTop (𝓝 (S * ε)) := by
      have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simp only [one_div] at h0
      have h1 : Tendsto ρ₁ atTop (𝓝 0) := by
        simpa using h0.const_mul (C₁ * Real.exp (K₁ * t) * (1 + t) * ε)
      have h2 : Tendsto ρ₂ atTop (𝓝 0) := by
        simpa using h0.const_mul (C₂ * Real.exp (K₂ * t) * (1 + t) * ε)
      simpa using tendsto_const_nhds.add (((h1.const_mul 3).add (h2.const_mul 15)).const_mul 16)
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hle
  have hSδ : S * ε ≤ δR0 := by
    have h1 : ε ≤ δR0 / (S + 1) := hεδ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by linarith)] at h1
    nlinarith
  refine ⟨hQt, hVt, hAt, hAsym, hQdt, hVdt, hQddt, hjet, hrow, hder, fun n κ => ⟨?_, ?_, ?_⟩,
    fun n a b c d => ?_⟩
  · exact (hr1 n κ).1.2.trans (by
      have e1 : C₁ * Real.exp (K₁ * t) ≤ C * Real.exp (K * t) := by
        have : C₁ ≤ C := by
          simp only [C]
          have := mul_nonneg (mul_nonneg hCR0n (by norm_num : (0:ℝ) ≤ 16))
            (by linarith : (0:ℝ) ≤ 3 * C₁ + 15 * C₂)
          linarith
        exact mul_le_mul this hexp1 (Real.exp_pos _).le hCnn
      calc C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
          = (C₁ * Real.exp (K₁ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ (C * Real.exp (K * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_right e1 (hfac0 n)
        _ = _ := by ring)
  · exact (hr1 n κ).2.1.2.trans (by
      have e1 : C₁ * Real.exp (K₁ * t) ≤ C * Real.exp (K * t) := by
        have : C₁ ≤ C := by
          simp only [C]
          have := mul_nonneg (mul_nonneg hCR0n (by norm_num : (0:ℝ) ≤ 16))
            (by linarith : (0:ℝ) ≤ 3 * C₁ + 15 * C₂)
          linarith
        exact mul_le_mul this hexp1 (Real.exp_pos _).le hCnn
      calc C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
          = (C₁ * Real.exp (K₁ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ (C * Real.exp (K * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_right e1 (hfac0 n)
        _ = _ := by ring)
  · exact (hr1 n κ).2.2.2.trans (by
      have e1 : C₁ * Real.exp (K₁ * t) ≤ C * Real.exp (K * t) := by
        have : C₁ ≤ C := by
          simp only [C]
          have := mul_nonneg (mul_nonneg hCR0n (by norm_num : (0:ℝ) ≤ 16))
            (by linarith : (0:ℝ) ≤ 3 * C₁ + 15 * C₂)
          linarith
        exact mul_le_mul this hexp1 (Real.exp_pos _).le hCnn
      calc C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
          = (C₁ * Real.exp (K₁ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ (C * Real.exp (K * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_right e1 (hfac0 n)
        _ = _ := by ring)
  · -- the curvature rate
    set e : Fin 4 × Fin 4 × Fin 4 × Fin 4 := (a, b, c, d)
    obtain ⟨F, hF, hFm, hFs⟩ := hRm e (Jn n) J (hJnm n) hJm ((hJnS n).trans (hSδ.trans (hδR0le e)))
      (hJS.trans (hSδ.trans (hδR0le e)))
    refine ⟨F, fun y => hF y, hFm, hFs.trans ?_⟩
    have h1 : CR e * ccoordSum r bPJ (Jn n - J) ≤ CR0 * (16 * (3 * ρ₁ n + 15 * ρ₂ n)) :=
      mul_le_mul (hCR0 e) (hdiff n).2 (ccoordSum_nonneg _ _ _) hCR0n
    refine h1.trans ?_
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
    have hE := hfac0 n
    have hex := (Real.exp_pos (K * t)).le
    set Z := Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹)
    have hZ : 0 ≤ Z := mul_nonneg hex hE
    have h4 : CR0 * (16 * (3 * ρ₁ n + 15 * ρ₂ n)) ≤ CR0 * 16 * (3 * C₁ + 15 * C₂) * Z := by
      have h5 : 3 * ρ₁ n + 15 * ρ₂ n ≤ (3 * C₁ + 15 * C₂) * Z := by
        have e1 : C₁ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) = C₁ * Z := by
          simp only [Z]; ring
        have e2 : C₂ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) = C₂ * Z := by
          simp only [Z]; ring
        rw [e1] at h2; rw [e2] at h3
        nlinarith
      have := mul_le_mul_of_nonneg_left h5 (mul_nonneg hCR0n (by norm_num) : (0 : ℝ) ≤ CR0 * 16)
      linarith
    refine h4.trans ?_
    have h6 : CR0 * 16 * (3 * C₁ + 15 * C₂) ≤ C := by
      simp only [C]; linarith
    calc CR0 * 16 * (3 * C₁ + 15 * C₂) * Z ≤ C * Z := mul_le_mul_of_nonneg_right h6 hZ
      _ = C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by simp only [Z]; ring


end

end RenewalGeometry.OpenWriterContinuum

namespace RenewalGeometry.OpenWriterLimitRegularity

noncomputable section


open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterGridBridge RootParityConnector PeriodicGridSobolev.Composition
  HarmonicWriter OpenWriterContinuum HarmonicGaugePropagation ContractedBianchiJet HarmonicDefect

/-- The acceleration is determined by the normal row (`a = -g^{00} ≠ 0`). -/
theorem row_acc_unique {q v w w' : MetricRec} {qd vd : Fin 3 → MetricRec}
    {qdd : Fin 3 → Fin 3 → MetricRec} (ha : harmA (minkowski + q) ≠ 0) (μ ν : Fin 4)
    (h : normalRow q v w qd vd qdd μ ν = 0) (h' : normalRow q v w' qd vd qdd μ ν = 0) :
    w μ ν = w' μ ν := by
  simp only [normalRow, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h h'
  have : harmA (minkowski + q) * (w μ ν - w' μ ν) = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 ha
  · linarith

set_option maxHeartbeats 2000000 in
/-- **`thm:supp-open-einstein`** (whole-sequence nonsymmetric vacuum limit), for `s ≥ 6`: there
are mesh-independent `δ, K, C` such that, if for every mesh `h = 1/(n + 1)` the open writer solution
on `[0, T]` starts from the samples of a harmonic preparation `(Q₀, V₀)` of constrained slice data
(`HarmonicPrep`, `eq:supp-open-harmonic-initial`, `eq:main-open-data-class`) in the top ball of size
`ε ≤ δ` and stays there, then the whole sequence of real interpolants of `q`, `v`, `∂ₜv` and of
their spatial derivatives converges uniformly on `[0, T] × 𝕋³` to the fields of a classical solution
of the harmonic reduced equation with the given data, with the metric rate
`eq:supp-open-metric-rate` and the curvature rate `eq:supp-open-curvature-rate`, and the
**Einstein tensor of the limit metric vanishes** on `[0, T] × 𝕋³` (`eq:supp-open-vacuum`). -/
theorem writer_limit_vacuum (s : ℕ) (hs : 6 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∀ (T : ℝ) (q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec)
      (Q₀ V₀ : C(T3, MetricRec)) (ε : ℝ), WriterData s T q v Q₀ V₀ ε → ε ≤ δ → 0 < T →
      HarmonicPrep ⇑Q₀ ⇑V₀ →
      ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd Vd : ℝ → Fin 3 → C(T3, MetricRec))
        (Qdd : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
        ∀ t ∈ Set.Icc 0 T,
          (Tendsto (fun n => interpRec (q n t)) atTop (𝓝 (Q t)) ∧
          Tendsto (fun n => interpRec (v n t)) atTop (𝓝 (V t)) ∧
          Tendsto (fun n => interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t)))) atTop
            (𝓝 (A t)) ∧ (∀ y μ ν, A t y μ ν = A t y ν μ) ∧
          (∀ i, Tendsto (fun n => interpD (q n t) i) atTop (𝓝 (Qd t i))) ∧
          (∀ i, Tendsto (fun n => interpD (v n t) i) atTop (𝓝 (Vd t i))) ∧
          (∀ i j, Tendsto (fun n => interpDD (q n t) i j) atTop (𝓝 (Qdd t i j))) ∧
          IsContJet (Q t) (V t) (Qd t) (Vd t) (Qdd t) ∧
          (∀ y (κ : Upper), normalRow (Q t y) (V t y) (A t y) (fun i => Qd t i y)
            (fun i => Vd t i y) (fun i j => Qdd t i j y) κ.1.1 κ.1.2 = 0) ∧
          (t ∈ Set.Ioo 0 T → ∀ y, HasDerivAt (fun τ => Q τ y) (V t y) t ∧
            HasDerivAt (fun τ => V τ y) (A t y) t) ∧
          (∀ n (κ : Upper),
            sn (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ≤
              C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ ∧
            sn (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ≤
              C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ ∧
            sn (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
              cmp (A t) κ.1.1 κ.1.2) ≤ C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) ∧
          ∀ n (a b c d : Fin 4), ∃ F : CT,
            (∀ y, F y = ((riemOf (pjetField (interpRec (q n t)) (interpRec (v n t))
                (interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t))))
                (interpD (q n t)) (interpD (v n t)) (interpDD (q n t)) y) a b c d -
              riemOf (pjetField (Q t) (V t) (A t) (Qd t) (Vd t) (Qdd t) y) a b c d : ℝ) : ℂ)) ∧
            MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) ∧
          ∀ y μ ν, einstein (minkowski + Q t y) (recInv (minkowski + Q t y))
            (metricJet (V t y, fun i => Qd t i y))
            (ddArr (A t y) (fun i => Vd t i y) (fun i j => Qdd t i j y)) μ ν = 0 := by
  obtain ⟨δ1, hδ1, h1⟩ := writer_limit_hyp s hs
  obtain ⟨δ2, hδ2, K, hK, C, hC, h2⟩ := writer_limit_curvature_rate_sym s (by omega)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, K, hK, C, hC, fun T q v Q₀ V₀ ε hW hεδ hT hP => ?_⟩
  have hW' := hW
  obtain ⟨hsol, hq0, hv0, hQs, hVs, hQ, hV, hX0, hXq⟩ := hW'
  obtain ⟨Q, V, A, Qd, Vd, Qdd, hQ0, hV0, hcr⟩ := h2 T q v Q₀ V₀ ε hsol hq0 hv0 hQs hVs hQ hV
    hX0 hXq (hεδ.trans (min_le_right _ _))
  obtain ⟨hF, hlim⟩ := h1 T q v Q₀ V₀ ε hW (hεδ.trans (min_le_left _ _)) hT.le
  refine ⟨Q, V, A, Qd, Vd, Qdd, hQ0, hV0, fun t ht => ⟨hcr t ht, ?_⟩⟩
  -- the fields of `limField` coincide with the limit fields on `[0, T]`
  have eQ : ∀ τ ∈ Set.Icc 0 T, (limField q v T).Q τ = ⇑(Q τ) := fun τ hτ => by
    have e := tendsto_nhds_unique (hlim τ hτ).1 (hcr τ hτ).1
    show ⇑(limF (famQ q []) (clampT T τ)) = _
    rw [clampT_of_mem hτ, e]
  have eV : ∀ τ ∈ Set.Icc 0 T, (limField q v T).V τ = ⇑(V τ) := fun τ hτ => by
    have e := tendsto_nhds_unique (hlim τ hτ).2.1 (hcr τ hτ).2.1
    show ⇑(limF (famV v []) (clampT T τ)) = _
    rw [clampT_of_mem hτ, e]
  have eA : ∀ τ ∈ Set.Icc 0 T, (limField q v T).A τ = ⇑(A τ) := fun τ hτ => by
    have e := tendsto_nhds_unique (hlim τ hτ).2.2 (hcr τ hτ).2.2.1
    show ⇑(limF (famA q v []) (clampT T τ)) = _
    rw [clampT_of_mem hτ, e]
  have eQd : ∀ τ ∈ Set.Icc 0 T, ∀ i, (limField q v T).Qd τ i = ⇑(Qd τ i) := fun τ hτ i => by
    have h' := hF.xQ τ hτ i
    rw [eQ τ hτ] at h'
    exact isLineDeriv_unique h' ((hcr τ hτ).2.2.2.2.2.2.2.1.dQ i)
  have eQdd : ∀ τ ∈ Set.Icc 0 T, ∀ i j, (limField q v T).Qdd τ i j = ⇑(Qdd τ i j) :=
    fun τ hτ i j => by
      have h' := hF.xQd τ hτ i j
      rw [eQd τ hτ j] at h'
      exact isLineDeriv_unique h' ((hcr τ hτ).2.2.2.2.2.2.2.1.dQd i j)
  have eVd : ∀ τ ∈ Set.Icc 0 T, ∀ i, (limField q v T).Vd τ i = ⇑(Vd τ i) := fun τ hτ i => by
    have h' := hF.xV τ hτ i
    rw [eV τ hτ] at h'
    exact isLineDeriv_unique h' ((hcr τ hτ).2.2.2.2.2.2.2.1.dV i)
  -- the initial slice
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hI : (limField q v T).InitData := by
    intro x
    obtain ⟨Qd₀, Vd₀, Qdd₀, hdQ, hdQd, hdV, hS⟩ := hP
    obtain ⟨S, hSv, hSH, hham, hmom, hg, hG, hdg0, hdgk, hddg0k, hddgkl⟩ := hS x
    have fQ : (limField q v T).Q 0 = ⇑Q₀ := by rw [eQ 0 h0, hQ0]
    have fV : (limField q v T).V 0 = ⇑V₀ := by rw [eV 0 h0, hV0]
    have fQd : ∀ k, (limField q v T).Qd 0 k = Qd₀ k := fun k => by
      have h' := hF.xQ 0 h0 k
      rw [fQ] at h'
      exact isLineDeriv_unique h' (hdQ k)
    have fQdd : ∀ k l, (limField q v T).Qdd 0 k l = Qdd₀ k l := fun k l => by
      have h' := hF.xQd 0 h0 k l
      rw [fQd l] at h'
      exact isLineDeriv_unique h' (hdQd k l)
    have fVd : ∀ k, (limField q v T).Vd 0 k = Vd₀ k := fun k => by
      have h' := hF.xV 0 h0 k
      rw [fV] at h'
      exact isLineDeriv_unique h' (hdV k)
    set S' : SliceData := { S with w := Matrix.of ((limField q v T).A 0 x) }
    have hS'v : S'.Valid := ⟨hSv.γγi, hSv.γ_symm, hSv.γi_symm, hSv.dγ_symm, hSv.ddγ_symm,
      hSv.ddγ_comm, hSv.K_symm, hSv.dK_symm, by
        ext μ ν; exact (hF.sA 0 x ν μ)⟩
    refine ⟨S', hS'v, hSH, hham, hmom, ?_, ?_, ?_, ?_⟩
    · show Matrix.of (minkowski + (limField q v T).Q 0 x) = S.jet.g
      rw [fQ]; exact hg
    · show (Matrix.of (minkowski + (limField q v T).Q 0 x))⁻¹ = S.jet.G
      rw [fQ]; exact hG
    · funext a
      refine Fin.cases ?_ (fun k => ?_) a
      · show Matrix.of ((limField q v T).V 0 x) = S.jet.dg 0
        rw [fV]; exact hdg0
      · show Matrix.of ((limField q v T).Qd 0 k x) = S.jet.dg k.succ
        rw [fQd]; exact hdgk k
    · funext a b
      refine Fin.cases ?_ (fun k => ?_) a <;> refine Fin.cases ?_ (fun l => ?_) b
      · rfl
      · show Matrix.of ((limField q v T).Vd 0 l x) = S.jet.ddg 0 l.succ
        rw [fVd]; exact hddg0k l
      · show Matrix.of ((limField q v T).Vd 0 k x) = S.jet.ddg k.succ 0
        rw [fVd]; exact hddg0k k
      · show Matrix.of ((limField q v T).Qdd 0 k l x) = S.jet.ddg k.succ l.succ
        rw [fQdd]; exact hddgkl k l
  intro y μ ν
  have hE := hF.einstein_eq_zero hT hI t ht y μ ν
  have r1 := congrFun (eQ t ht) y
  have r2 := congrFun (eV t ht) y
  have r3 := congrFun (eA t ht) y
  have r4 : (fun i => (limField q v T).Qd t i y) = fun i => Qd t i y :=
    funext fun i => congrFun (eQd t ht i) y
  have r5 : (fun i => (limField q v T).Vd t i y) = fun i => Vd t i y :=
    funext fun i => congrFun (eVd t ht i) y
  have r6 : (fun i j => (limField q v T).Qdd t i j y) = fun i j => Qdd t i j y :=
    funext fun i => funext fun j => congrFun (eQdd t ht i j) y
  rw [r1, r2, r3, r4, r5, r6] at hE
  exact hE


/-! ### Non-vacuity: the flat preparation -/

theorem minkowski_eq_sliceMat : Matrix.of minkowski = sliceMat (-1) 0 1 := by
  ext μ ν
  refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
    simp [minkowski, Matrix.one_apply, Fin.succ_ne_zero, Fin.succ_inj]
  all_goals (try (intro h; exact absurd h.symm (Fin.succ_ne_zero _)))

/-- The flat data `γ = 1`, `K = 0` give the harmonic preparation `(Q₀, V₀) = (0, 0)`. -/
theorem harmonicPrep_zero : HarmonicPrep (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun i => isLineDeriv_zero i,
    fun i j => isLineDeriv_zero i, fun i => isLineDeriv_zero i, fun x => ?_⟩
  refine ⟨SliceData.flatSlice, SliceData.flatSlice_valid, SliceData.flatSlice_harmonicInit,
    ?_, fun i => ?_, ?_, ?_, ?_, fun k => ?_, fun k => ?_, fun k l => ?_⟩
  · simp [SliceData.hamC, SliceData.trK, SliceData.normK2, SliceData.flatSlice, Jet3.scal,
      Jet3.ricM, Jet3.riem, Jet3.dchr, Jet3.chr, Jet3.low, Jet3.dlow, SliceData.spatial,
      Matrix.trace, Matrix.diag]
  · simp [SliceData.momC, SliceData.divK, SliceData.dtrK, SliceData.flatSlice, Jet3.chr,
      Jet3.low, Jet3.dG, SliceData.spatial]
  · simp only [add_zero, SliceData.jet_g, minkowski_eq_sliceMat]; rfl
  · show (Matrix.of (minkowski + 0))⁻¹ = _
    rw [add_zero, minkowski_inv, minkowski_eq_sliceMat]; rfl
  · ext μ ν
    refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
      simp [SliceData.flatSlice]
  · ext μ ν
    refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
      simp [SliceData.flatSlice]
  · ext μ ν
    refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
      simp [SliceData.flatSlice, SliceData.dtk]
  · ext μ ν
    refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
      simp [SliceData.flatSlice]

end

end RenewalGeometry.OpenWriterLimitRegularity
