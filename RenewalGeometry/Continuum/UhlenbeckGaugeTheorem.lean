/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientDefect
import RenewalGeometry.Analysis.UhlenbeckContinuity
import RenewalGeometry.Analysis.UhlenbeckCoulombIFT

/-!
# Uhlenbeck's small-energy gauge theorem: structure-group form, the dilation path, and the
  reduction of `prop:critical-uhlenbeck` (Einstein–Standard-Model action closure)

This file collects, for `prop:critical-uhlenbeck` and `thm:critical-quotient-defect`, the parts of
K. Uhlenbeck's small-energy Coulomb gauge theorem (Comm. Math. Phys. 83 (1982), Thm 1.3, `p = 2`,
dimension 4) that live on Euclidean balls, on top of the periodic analytic core proved in
`Analysis/UhlenbeckHodgeEstimate.lean`, `Analysis/UhlenbeckCoulombIFT.lean`,
`Analysis/UhlenbeckCoulombApriori.lean`, `Analysis/UhlenbeckContinuity.lean`.

* `UhlenbeckSmallEnergyGaugeIn m G 𝔤` — **the structure-group form** of the named theorem
  `CriticalGauge.UhlenbeckSmallEnergyGauge`: connections with values in a set `𝔤` of matrices
  (the Lie algebra of a closed subgroup `G ⊆ U(m)`, e.g. `𝔤_SM = 𝔰(𝔲(3) ⊕ 𝔲(2)) ⊂ 𝔲(5)`) have
  `G`-valued Coulomb gauges.  `uhlenbeckIn_unitary_iff`: for `G = U(m)`, `𝔤 = M_m(ℂ)` it is
  exactly `UhlenbeckSmallEnergyGauge m`; `UhlenbeckSmallEnergyGaugeIn.mono`: monotone in `(G, 𝔤)`.
* `uhlenbeck_ball_cover_in`, `critical_uhlenbeck_of_gauge_in` — the ball cover of
  `CriticalQuotient.uhlenbeck_ball_cover` and `prop:critical-uhlenbeck`
  (`CriticalGauge.critical_uhlenbeck_of_gauge`) re-derived for `𝔤`-valued connections with
  `G`-valued gauges (so that the `G_SM`-equivariant budgets can be pulled back); the `U(m)`
  statements are the case `G = U(m)`.
* `dilateConn`, `curvVec_dilateConn`, `curvEnergy_dilateConn`, `curvEnergy_dilateConn_le` —
  **the continuity path** `A_t(x) = t A(c + t(x - c))` of Uhlenbeck's proof:
  `F_{A_t}(x) = t² F_A(c + t(x - c))`, hence `∫_{B_r(c)} |F_{A_t}|² = ∫_{B_{tr}(c)} |F_A|²`
  (scale invariance of the four-dimensional Yang–Mills energy), which is `≤ ∫_{B_r(c)} |F_A|²`
  for `0 < t ≤ 1`, and `A_0 = 0`.  So the small-energy hypothesis holds along the whole path.

What is proved about Uhlenbeck's theorem itself (periodic rendering, `𝕋⁴`), see the docstrings
of the analysis files: the Hodge/Gaffney estimate, the critical Sobolev–Poincaré inequality, the
critical Coulomb a-priori estimate with absorption (`coulomb_apriori_torus`, also in the
Neumann/reflection rendering, `coulomb_apriori_torus_neumann`), the first-exit gap and its
propagation along continuous paths, uniqueness of the Coulomb gauge up to constants
(`coulomb_gauge_unique_torus`), the linear part of the implicit-function step (the Laplacian is an
isomorphism of mean-zero `H²` onto mean-zero `L²`, `laplace_solve`/`laplace_unique`; the kernel of
the linearised operator `d^*d_a` at a small Coulomb `a` is the constants,
`linearized_coulomb_kernel_const`), and the abelian case of the theorem
(`abelian_coulomb_gauge`).  **Not proved** (the remaining steps of the named theorem): the
nonlinear implicit-function (openness) step (a Banach algebra of matrix functions on which the
exponential is `C¹`, surjectivity of the linearisation at `a ≠ 0` by Fredholm theory), the
compactness/regularity of the gauges in the closedness step (elliptic regularity of the
Coulomb–Neumann problem up to `C^∞`, needed for the smooth gauges of the named Prop), and the
transfer from the torus/cube-with-reflection rendering to Euclidean balls.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.UhlenbeckGauge

open SobolevOpen CriticalGauge CriticalQuotient

set_option linter.unusedSectionVars false

/-! ### The structure-group form of the named theorem -/

/-- **Uhlenbeck's small-energy Coulomb gauge theorem for a structure group** (Uhlenbeck, CMP 83
(1982), Thm 1.3, stated there for every compact Lie group `G`): with `G ⊆ U(m)` a set of unitary
matrices (the structure group) and `𝔤` a set of skew-Hermitian matrices (its Lie algebra), there
are `ε_U > 0` and `C_U` such that for every ball `B_r(c) ⊂ ℝ⁴` there is `C_r` with: every smooth
unitary connection with values in `𝔤` and `∫_{B_r(c)} |F_A|² ≤ ε_U` has a gauge `R`, `G`-valued
and smooth on the ball, with `R·A` Coulomb on the ball, `‖R·A‖_{W^{1,2}(B_r(c))} ≤ C_r ‖F_A‖_2`
and `‖R·A‖_{L⁴(B_r(c))} ≤ C_U ‖F_A‖_2`.  Same clauses as `UhlenbeckSmallEnergyGauge`. -/
def UhlenbeckSmallEnergyGaugeIn (m : ℕ) (G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  ∃ εU : ℝ≥0, 0 < εU ∧ ∃ CU : ℝ≥0, ∀ (c : Fin 4 → ℝ) (r : ℝ), 0 < r → ∃ Cr : ℝ≥0,
    ∀ A : MConn m, IsSmoothUnitaryConn A → (∀ μ y, A μ y ∈ 𝔤) → curvEnergy A (eBall c r) ≤ εU →
      ∃ R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ y ∈ eBall c r, R y ∈ G) ∧
        (∀ c' e', ContDiffOn ℝ ∞ (fun y => R y c' e') (eBall c r)) ∧
        (∀ x ∈ eBall c r, ∀ c' e', ∑ μ, entryGrad (gaugeConn R A) μ c' e' μ x = 0) ∧
        (∀ ν c' e', MemW12 (eBall c r) (entries (gaugeConn R A) ν c' e')
          (entryGrad (gaugeConn R A) ν c' e')) ∧
        (∀ ν c' e', w12Norm (eBall c r) (entries (gaugeConn R A) ν c' e')
          (entryGrad (gaugeConn R A) ν c' e') ≤ Cr * curvEnergy A (eBall c r) ^ (1 / 2 : ℝ)) ∧
        (∀ ν c' e', eLpNorm (entries (gaugeConn R A) ν c' e') 4 (volume.restrict (eBall c r)) ≤
          CU * curvEnergy A (eBall c r) ^ (1 / 2 : ℝ))

/-- Monotonicity in the structure data: a larger group `G'` and a smaller algebra `𝔤'`. -/
theorem UhlenbeckSmallEnergyGaugeIn.mono {m : ℕ} {G G' 𝔤 𝔤' : Set (Matrix (Fin m) (Fin m) ℂ)}
    (h : UhlenbeckSmallEnergyGaugeIn m G 𝔤) (hG : G ⊆ G') (h𝔤 : 𝔤' ⊆ 𝔤) :
    UhlenbeckSmallEnergyGaugeIn m G' 𝔤' := by
  obtain ⟨εU, hεU, CU, hU⟩ := h
  refine ⟨εU, hεU, CU, fun c r hr => ?_⟩
  obtain ⟨Cr, hCr⟩ := hU c r hr
  refine ⟨Cr, fun A hA h𝔤A hE => ?_⟩
  obtain ⟨R, hRG, hR⟩ := hCr A hA (fun μ y => h𝔤 (h𝔤A μ y)) hE
  exact ⟨R, fun y hy => hG (hRG y hy), hR⟩

/-- For the full unitary group (and no constraint on the Lie-algebra values), the structure-group
form is exactly the named theorem `UhlenbeckSmallEnergyGauge m`. -/
theorem uhlenbeckIn_unitary_iff (m : ℕ) :
    UhlenbeckSmallEnergyGaugeIn m (unitaryGroup (Fin m) ℂ) univ ↔
      UhlenbeckSmallEnergyGauge m := by
  constructor
  · rintro ⟨εU, hεU, CU, hU⟩
    refine ⟨εU, hεU, CU, fun c r hr => ?_⟩
    obtain ⟨Cr, hCr⟩ := hU c r hr
    exact ⟨Cr, fun A hA hE => hCr A hA (fun _ _ => mem_univ _) hE⟩
  · rintro ⟨εU, hεU, CU, hU⟩
    refine ⟨εU, hεU, CU, fun c r hr => ?_⟩
    obtain ⟨Cr, hCr⟩ := hU c r hr
    exact ⟨Cr, fun A hA _ hE => hCr A hA hE⟩

/-! ### The ball cover and `prop:critical-uhlenbeck` with `G`-valued gauges -/

/-- **The small-energy ball cover with `G`-valued Uhlenbeck gauges** (structure-group form of
`CriticalQuotient.uhlenbeck_ball_cover`): for `𝔤`-valued smooth unitary connections `A_h` on
`K = box a b` with uniformly integrable critical curvature energy, every compact `K' ⊂ K` and
`η > 0`, there are finitely many balls `B_r(c_j) ⊂ K` whose inner cubes cover `K'` and gauges
`R_{h,j}`, `G`-valued and smooth on the balls, with `R_{h,j}·A_h` Coulomb, uniformly bounded in
`W^{1,2}(B_r(c_j))` and with `L⁴` norms `≤ η`. -/
theorem uhlenbeck_ball_cover_in {m : ℕ} {G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hU : UhlenbeckSmallEnergyGaugeIn m G 𝔤)
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (h𝔤 : ∀ h μ y, A h μ y ∈ 𝔤)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧ (∀ j, eBall (ctr j) r ⊆ box a b) ∧
      K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ eBall (ctr j) r, R h j y ∈ G) ∧
        (∀ h j c e, ContDiffOn ℝ ∞ (fun y => R h j y c e) (eBall (ctr j) r)) ∧
        (∀ h j, ∀ x ∈ eBall (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h j ν c e,
          MemW12 (eBall (ctr j) r) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ∧
          w12Norm (eBall (ctr j) r) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ B) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (eBall (ctr j) r)) ≤ η) := by
  obtain ⟨εU, hεU, CU, hU'⟩ := hU
  set εs : ℝ≥0 := min εU ((η / (CU + 1)) ^ 2)
  have hεs : 0 < εs := lt_min hεU (by positivity)
  obtain ⟨δ, hδ, hUIδ⟩ := (criticalCurvatureUI_iff _ _ _).mp hUI εs (by exact_mod_cast hεs)
  obtain ⟨r0, hr0, hthick⟩ := hK'.exists_thickening_subset_open (isOpen_box a b) hK'Q
  set r : ℝ := min (r0 / 2) (min 1 δ / 2)
  have hr : 0 < r := lt_min (by positivity) (by have := lt_min one_pos hδ; positivity)
  have hrr0 : r < r0 := (min_le_left _ _).trans_lt (by linarith)
  have hvol : (2 * r) ^ Fintype.card (Fin 4) ≤ δ := by
    have h2r : 2 * r ≤ min 1 δ := by
      have := min_le_right (r0 / 2) (min 1 δ / 2); linarith
    have h0 : 0 ≤ 2 * r := by linarith
    have h1 : 2 * r ≤ 1 := h2r.trans (min_le_left _ _)
    simp only [Fintype.card_fin]
    calc (2 * r) ^ 4 ≤ (2 * r) ^ 1 := pow_le_pow_of_le_one h0 h1 (by norm_num)
      _ = 2 * r := pow_one _
      _ ≤ δ := h2r.trans (min_le_right _ _)
  have hball : ∀ c ∈ K', eBall c r ⊆ box a b := by
    intro c hc x hx
    refine hthick (Metric.mem_thickening_iff.mpr ⟨c, hc, ?_⟩)
    exact (Metric.mem_ball.mp (eBall_subset_ball c hr hx)).trans hrr0
  have hballvol : ∀ c, volume (eBall c r) ≤ ENNReal.ofReal δ := fun c =>
    (measure_mono (eBall_subset_ball c hr)).trans (by
      rw [Real.volume_pi_ball c hr]; exact ENNReal.ofReal_le_ofReal hvol)
  have henergy : ∀ h, ∀ c ∈ K', curvEnergy (A h) (eBall c r) ≤ εs := fun h c hc =>
    hUIδ h (eBall c r) (isOpen_eBall c r).measurableSet (hball c hc) (hballvol c)
  obtain ⟨t, ht⟩ := hK'.elim_finite_subcover (fun c : K' => innerCube c.1 r)
    (fun c => isOpen_box _ _) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, by
      rw [innerCube, mem_box]; intro i; constructor <;> simp <;> linarith⟩)
  set N := t.card
  set ctr : Fin N → Fin 4 → ℝ := fun j => (t.equivFin.symm j : K').1
  have hctr : ∀ j, ctr j ∈ K' := fun j => (t.equivFin.symm j : K').2
  refine ⟨N, ctr, r, hr, fun j => hball _ (hctr j), ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp (ht hx)
    refine mem_iUnion.mpr ⟨t.equivFin ⟨c, hct⟩, ?_⟩
    simpa [ctr] using hxc
  choose Cr hCr using fun j => hU' (ctr j) r hr
  have hsmall : ∀ h j, curvEnergy (A h) (eBall (ctr j) r) ≤ εU := fun h j =>
    (henergy h _ (hctr j)).trans (by exact_mod_cast min_le_left _ _)
  choose R hRu hRs hRdiv hRW hRw12 hR4 using fun h j => hCr j (A h) (hA h) (h𝔤 h) (hsmall h j)
  refine ⟨R, hRu, hRs, hRdiv, ⟨∑ j, (Cr j : ℝ≥0∞) * (εU : ℝ≥0∞) ^ (1 / 2 : ℝ), ?_,
    fun h j ν c e => ⟨hRW h j ν c e, ?_⟩⟩, fun h j ν c e => ?_⟩
  · exact ENNReal.sum_ne_top.mpr fun j _ => ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top)
  · refine (hRw12 h j ν c e).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => (Cr j : ℝ≥0∞) *
      (εU : ℝ≥0∞) ^ (1 / 2 : ℝ)) (fun _ _ => zero_le) (Finset.mem_univ j))
    exact mul_le_mul_right (ENNReal.rpow_le_rpow (hsmall h j) (by norm_num)) _
  · exact (hR4 h j ν c e).trans (mul_rpow_half_le (min_le_right _ _) (henergy h _ (hctr j)))

/-- **`prop:critical-uhlenbeck` with `G`-valued gauges, conditional on the structure-group form
of the named theorem** (box rendering of the chart `K = box a b`, as in
`CriticalGauge.critical_uhlenbeck_of_gauge`, which is the case `G = U(m)`, `𝔤 = M_m(ℂ)`):
for `𝔤`-valued smooth unitary connections `A_h` with bounded, uniformly integrable critical
curvature energy, every compact `K' ⊂ K` and `η > 0`: a finite cover of `K'` by cubes
`Q_j ⊂ K`, local `G`-valued gauges `R_{h,j}` with `d^*(R·A_h) = 0` on `Q_j`, uniform
`W^{1,2}(Q_j)` bounds, `L⁴(Q_j)` norms `≤ η`, and one subsequence along which every chart
converges (`CoulombLimit`: weakly in `W^{1,2}`, strongly in `L^q`, `q < 4`, curvature against
bounded weights). -/
theorem critical_uhlenbeck_of_gauge_in {m : ℕ} {G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hU : UhlenbeckSmallEnergyGaugeIn m G 𝔤)
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (h𝔤 : ∀ h μ y, A h μ y ∈ 𝔤)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (lo hi : Fin N → Fin 4 → ℝ), (∀ j i, lo j i < hi j i) ∧
      (∀ j, box (lo j) (hi j) ⊆ box a b) ∧ K' ⊆ ⋃ j, box (lo j) (hi j) ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ box (lo j) (hi j), R h j y ∈ G) ∧
        (∀ h j, ∀ x ∈ box (lo j) (hi j), ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h j ν c e,
          MemW12 (box (lo j) (hi j)) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ∧
          w12Norm (box (lo j) (hi j)) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ B) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (box (lo j) (hi j))) ≤ η) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ j, CoulombLimit (box (lo j) (hi j)) (fun h => gaugeConn (R h j) (A h)) φ := by
  obtain ⟨N, ctr, r, hr, hball, hcov, R, hRG, _hRs, hRdiv, ⟨B, hBt, hB⟩, hR4⟩ :=
    uhlenbeck_ball_cover_in hU A hA h𝔤 hUI hK' hK'Q hη
  set lo : Fin N → Fin 4 → ℝ := fun j i => ctr j i - r / 4
  set hi : Fin N → Fin 4 → ℝ := fun j i => ctr j i + r / 4
  have hcube : ∀ j, box (lo j) (hi j) ⊆ eBall (ctr j) r := by
    intro j
    refine Subset.trans ?_ (box_subset_eBall (ctr j) hr)
    intro x hx
    rw [mem_box] at hx ⊢
    intro i
    have := hx i
    simp only [lo, hi] at this
    constructor <;> linarith [this.1, this.2]
  refine ⟨N, lo, hi, fun j i => by simp only [lo, hi]; linarith,
    fun j => (hcube j).trans (hball j), ?_, R, fun h j y hy => hRG h j y (hcube j hy),
    fun h j x hx => hRdiv h j x (hcube j hx), ⟨B, hBt, fun h j ν c e =>
      ⟨(hB h j ν c e).1.mono (hcube j), (w12Norm_mono (hcube j) _ _).trans (hB h j ν c e).2⟩⟩,
    fun h j ν c e => (eLpNorm_mono_measure _ (Measure.restrict_mono (hcube j) le_rfl)).trans
      (hR4 h j ν c e), ?_⟩
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨j, by simpa [innerCube, lo, hi] using hj⟩
  · refine exists_common_subseq (fun j φ => CoulombLimit (box (lo j) (hi j))
      (fun h => gaugeConn (R h j) (A h)) φ) (fun j φ _ => ?_)
      (fun j φ ψ hψ hP => hP.comp hψ)
    exact exists_coulombLimit (fun i => by simp only [lo, hi]; linarith)
      (fun h ν c e => (hB h j ν c e).1.mono (hcube j)) hBt
      (fun h ν c e => (w12Norm_mono (hcube j) _ _).trans (hB h j ν c e).2) φ

/-! ### The continuity path: dilations and scale invariance of the energy -/

/-- The dilation `A_t(x) = t A(c + t(x - c))` of a connection about the centre `c`. -/
def dilateConn {m : ℕ} (t : ℝ) (c : Fin 4 → ℝ) (A : MConn m) : MConn m :=
  fun μ y => (t : ℂ) • A μ (c + t • (y - c))

theorem hasFDerivAt_dilate (t : ℝ) (c y : Fin 4 → ℝ) :
    HasFDerivAt (fun y : Fin 4 → ℝ => c + t • (y - c))
      (t • ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) y := by
  have h1 : HasFDerivAt (fun y : Fin 4 → ℝ => y - c) (ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) y :=
    (hasFDerivAt_id y).sub_const c
  have h2 := h1.const_smul (t : ℝ)
  have h3 := h2.const_add c
  simpa using h3

/-- The chain rule for the dilation: `∂_μ (t f(c + t(y - c))) = t² (∂_μ f)(c + t(y - c))`. -/
theorem pd_dilate {f : (Fin 4 → ℝ) → ℂ} (hf : Differentiable ℝ f) (t : ℝ) (c : Fin 4 → ℝ)
    (μ : Fin 4) (y : Fin 4 → ℝ) :
    pd (fun y => (t : ℂ) * f (c + t • (y - c))) μ y = (t : ℂ) ^ 2 * pd f μ (c + t • (y - c)) := by
  have hcomp := (hf (c + t • (y - c))).hasFDerivAt.comp y (hasFDerivAt_dilate t c y)
  have h2 := hcomp.const_mul (t : ℂ)
  unfold pd
  show fderiv ℝ (fun y => (t : ℂ) * (f ∘ fun y => c + t • (y - c)) y) y (Pi.single μ 1) = _
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
    ContinuousLinearMap.map_smul, smul_eq_mul, Complex.real_smul]
  ring

theorem entries_dilateConn {m : ℕ} (t : ℝ) (c : Fin 4 → ℝ) (A : MConn m) (ν : Fin 4)
    (c' e' : Fin m) (y : Fin 4 → ℝ) :
    entries (dilateConn t c A) ν c' e' y = (t : ℂ) * entries A ν c' e' (c + t • (y - c)) := by
  simp [entries, dilateConn, Matrix.smul_apply]

theorem entryGrad_dilateConn {m : ℕ} {A : MConn m} (hA : IsSmoothUnitaryConn A) (t : ℝ)
    (c : Fin 4 → ℝ) (ν : Fin 4) (c' e' : Fin m) (μ : Fin 4) (y : Fin 4 → ℝ) :
    entryGrad (dilateConn t c A) ν c' e' μ y =
      (t : ℂ) ^ 2 * entryGrad A ν c' e' μ (c + t • (y - c)) := by
  have e : (fun y => dilateConn t c A ν y c' e') =
      fun y => (t : ℂ) * (fun z => A ν z c' e') (c + t • (y - c)) := by
    funext y; exact entries_dilateConn t c A ν c' e' y
  simp only [entryGrad]
  rw [e, pd_dilate ((hA.smooth ν c' e').differentiable (by simp)) t c μ y]

/-- **Curvature of the dilation**: `F_{A_t}(y) = t² F_A(c + t(y - c))`. -/
theorem curvVec_dilateConn {m : ℕ} {A : MConn m} (hA : IsSmoothUnitaryConn A) (t : ℝ)
    (c y : Fin 4 → ℝ) :
    curvVec (dilateConn t c A) y = ((t : ℂ) ^ 2) • curvVec A (c + t • (y - c)) := by
  ext p
  simp only [curvVec, curvatureW, PiLp.smul_apply, smul_eq_mul, entryGrad_dilateConn hA,
    entries_dilateConn]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem mem_eBall_dilate {c y : Fin 4 → ℝ} {t r : ℝ} (ht : 0 < t) :
    c + t • (y - c) ∈ eBall c (t * r) ↔ y ∈ eBall c r := by
  simp only [eBall, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    add_sub_cancel_left, mul_pow]
  rw [← Finset.mul_sum]
  exact mul_lt_mul_iff_of_pos_left (by positivity)

theorem measurable_curvVec_enorm {m : ℕ} {A : MConn m} (hA : IsSmoothUnitaryConn A) :
    Measurable fun x => ‖curvVec A x‖ₑ ^ 2 := by
  have hc : Continuous (curvVec A) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
    simp only [curvatureW, entries, entryGrad]
    refine Continuous.add (Continuous.sub ?_ ?_) (continuous_finset_sum _ fun k _ => ?_)
    · exact continuous_pd ((hA.smooth _ _ _).of_le (by simp)) _
    · exact continuous_pd ((hA.smooth _ _ _).of_le (by simp)) _
    · exact (((hA.smooth _ _ _).continuous).mul (hA.smooth _ _ _).continuous).sub
        (((hA.smooth _ _ _).continuous).mul (hA.smooth _ _ _).continuous)
  exact hc.measurable.enorm.pow_const 2

/-- `∫ g(c + t(y - c)) dy = t^{-4} ∫ g` for `t > 0` (Lebesgue measure on `ℝ⁴`). -/
theorem lintegral_comp_dilate {g : (Fin 4 → ℝ) → ℝ≥0∞} (hg : Measurable g) {t : ℝ}
    (ht : 0 < t) (c : Fin 4 → ℝ) :
    ∫⁻ y, g (c + t • (y - c)) = ENNReal.ofReal (t ^ 4)⁻¹ * ∫⁻ y, g y := by
  rw [lintegral_sub_right_eq_self (fun u => g (c + t • u)) c]
  have hmap := Measure.map_addHaar_smul (volume : Measure (Fin 4 → ℝ)) ht.ne'
  have h1 : ∫⁻ u, g (c + t • u) = ∫⁻ v, g (c + v) ∂(Measure.map (t • ·) volume) :=
    (lintegral_map (f := fun v => g (c + v)) (hg.comp (measurable_const_add c))
      (measurable_const_smul t)).symm
  rw [h1, hmap, lintegral_smul_measure, lintegral_add_left_eq_self (fun v => g v) c]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, smul_eq_mul]
  congr 2
  rw [abs_of_nonneg (inv_nonneg.2 (by positivity))]

/-- **Scale invariance of the Yang–Mills energy along the dilation path**:
`∫_{B_r(c)} |F_{A_t}|² = ∫_{B_{tr}(c)} |F_A|²` for `t > 0`. -/
theorem curvEnergy_dilateConn {m : ℕ} {A : MConn m} (hA : IsSmoothUnitaryConn A) {t : ℝ}
    (ht : 0 < t) (c : Fin 4 → ℝ) (r : ℝ) :
    curvEnergy (dilateConn t c A) (eBall c r) = curvEnergy A (eBall c (t * r)) := by
  set F : (Fin 4 → ℝ) → ℝ≥0∞ := fun x => ‖curvVec A x‖ₑ ^ 2
  have hF : Measurable F := measurable_curvVec_enorm hA
  have hball : MeasurableSet (eBall c (t * r)) := (isOpen_eBall c _).measurableSet
  have hpt : ∀ y, (eBall c r).indicator (fun y => ‖curvVec (dilateConn t c A) y‖ₑ ^ 2) y =
      ENNReal.ofReal (t ^ 4) * (eBall c (t * r)).indicator F (c + t • (y - c)) := by
    intro y
    by_cases hy : y ∈ eBall c r
    · rw [indicator_of_mem hy, indicator_of_mem ((mem_eBall_dilate ht).2 hy),
        curvVec_dilateConn hA, enorm_smul]
      simp only [F]
      have hn : ‖((t : ℂ) ^ 2)‖ₑ ^ 2 = ENNReal.ofReal (t ^ 4) := by
        rw [← ofReal_norm_eq_enorm, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos ht, ← ENNReal.ofReal_pow (by positivity)]
        ring_nf
      rw [mul_pow, hn]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy ((mem_eBall_dilate ht).1 h)),
        mul_zero]
  unfold curvEnergy
  rw [← lintegral_indicator (isOpen_eBall c r).measurableSet, ← lintegral_indicator hball]
  simp only [hpt]
  rw [lintegral_const_mul (f := fun a => (eBall c (t * r)).indicator F (c + t • (a - c))) _
    ((hF.indicator hball).comp (by fun_prop : Measurable fun a : Fin 4 → ℝ => c + t • (a - c))),
    lintegral_comp_dilate (hF.indicator hball) ht c, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
    one_mul]

/-- **Along the continuity path the energy stays small**: for `0 < t ≤ 1`,
`∫_{B_r(c)} |F_{A_t}|² ≤ ∫_{B_r(c)} |F_A|²`. -/
theorem curvEnergy_dilateConn_le {m : ℕ} {A : MConn m} (hA : IsSmoothUnitaryConn A) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (c : Fin 4 → ℝ) (r : ℝ) :
    curvEnergy (dilateConn t c A) (eBall c r) ≤ curvEnergy A (eBall c r) := by
  rw [curvEnergy_dilateConn hA ht]
  refine lintegral_mono_set fun x hx => ?_
  simp only [eBall, mem_setOf_eq] at hx ⊢
  have : (t * r) ^ 2 ≤ r ^ 2 := by
    rw [mul_pow]; exact mul_le_of_le_one_left (sq_nonneg r) (by nlinarith)
  linarith

/-- The dilation path starts at the trivial connection: `A_0 = 0`. -/
theorem dilateConn_zero {m : ℕ} (c : Fin 4 → ℝ) (A : MConn m) :
    dilateConn 0 c A = fun _ _ => 0 := by
  funext μ y; simp [dilateConn]

/-- The dilations of a smooth unitary connection are smooth unitary connections. -/
theorem isSmoothUnitaryConn_dilateConn {m : ℕ} {A : MConn m} (hA : IsSmoothUnitaryConn A)
    (t : ℝ) (c : Fin 4 → ℝ) : IsSmoothUnitaryConn (dilateConn t c A) := by
  refine ⟨fun μ c' e' => ?_, fun μ y => ?_⟩
  · have e : (fun y => dilateConn t c A μ y c' e') =
        fun y => (t : ℂ) * (fun z => A μ z c' e') (c + t • (y - c)) := by
      funext y; exact entries_dilateConn t c A μ c' e' y
    rw [e]
    exact contDiff_const.mul ((hA.smooth μ c' e').comp (by fun_prop))
  · simp only [dilateConn, star_smul, hA.skew, Complex.star_def, Complex.conj_ofReal, smul_neg]

/-- The dilations stay `𝔤`-valued for every set `𝔤` closed under real scalar multiplication
(e.g. a Lie algebra `𝔤 ⊂ 𝔲(m)`). -/
theorem dilateConn_mem {m : ℕ} {𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)}
    (h𝔤 : ∀ (s : ℝ), ∀ X ∈ 𝔤, (s : ℂ) • X ∈ 𝔤) {A : MConn m} (hA : ∀ μ y, A μ y ∈ 𝔤)
    (t : ℝ) (c : Fin 4 → ℝ) : ∀ μ y, dilateConn t c A μ y ∈ 𝔤 :=
  fun μ y => h𝔤 t _ (hA μ _)

/-! ### Non-vacuity -/

/-- The clauses of the named theorem are satisfiable: for the trivial connection the constant
gauge `R = 1` is Coulomb with `R·A = 0`.  (The full statement `UhlenbeckSmallEnergyGaugeIn` for
`G ⊇ {1}` restricted to the zero connection.) -/
example (c : Fin 4 → ℝ) (r : ℝ) :
    let R : (Fin 4 → ℝ) → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
    let A : MConn 1 := fun _ _ => 0
    (∀ y ∈ eBall c r, R y ∈ unitaryGroup (Fin 1) ℂ) ∧
      (∀ x ∈ eBall c r, ∀ c' e', ∑ μ, entryGrad (gaugeConn R A) μ c' e' μ x = 0) ∧
      (∀ ν c' e', eLpNorm (entries (gaugeConn R A) ν c' e') 4 (volume.restrict (eBall c r)) ≤
        0 * curvEnergy A (eBall c r) ^ (1 / 2 : ℝ)) := by
  intro R A
  have hg : gaugeConn R A = fun _ _ => 0 := by
    funext μ x
    ext c' e'
    simp [gaugeConn, R, A, pdM, pd]
  refine ⟨fun _ _ => one_mem _, fun x _ c' e' => ?_, fun ν c' e' => ?_⟩
  · simp [hg, entryGrad, pd]
  · have h0 : entries (gaugeConn R A) ν c' e' = fun _ => 0 := by
      funext y; simp [hg, entries]
    simp [h0]

end RenewalGeometry.UhlenbeckGauge
