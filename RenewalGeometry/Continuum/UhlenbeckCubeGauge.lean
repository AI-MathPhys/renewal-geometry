/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.UhlenbeckGaugeTheorem

/-!
# Uhlenbeck's small-energy gauge theorem on cubes: the cube rendering of the named Prop and the
  reduction of `prop:critical-uhlenbeck` to it (stage D assembly, cube route)

Generic infrastructure for `prop:critical-uhlenbeck` of the Einstein–Standard-Model
action-closure manuscript.  The manuscript uses Uhlenbeck's gauges only "on the corresponding
smaller balls" of a finite cover of `K' ⋐ K` (proof of `prop:critical-uhlenbeck`), and the library
reduction (`UhlenbeckGauge.uhlenbeck_ball_cover_in`, `critical_uhlenbeck_of_gauge_in`) only uses the
gauge on the inner cubes `box(c ∓ r/4)`.  Balls are a convenience; cubes serve equally:

* `cubeC c r = box (c - r) (c + r)` (`= Metric.ball c r` in the sup metric of `ℝ⁴`,
  `cubeC_eq_ball`);
* `UhlenbeckSmallEnergyGaugeCubeIn m G 𝔤` — **the cube rendering** of
  `UhlenbeckGauge.UhlenbeckSmallEnergyGaugeIn m G 𝔤`: the same clauses with the Euclidean ball
  `eBall c r` replaced by the cube `cubeC c r` (small curvature energy on the cube; `G`-valued
  gauge smooth on the open cube; pointwise Coulomb condition on the cube; `W^{1,2}` and `L⁴`
  bounds on the cube);
* `uhlenbeck_cube_cover_in`, `critical_uhlenbeck_of_gauge_cube_in` — the cover and
  `prop:critical-uhlenbeck` (same conclusion as `critical_uhlenbeck_of_gauge_in`: finite cover
  of `K'` by Coulomb cubes, uniform `W^{1,2}` bounds, `L⁴ ≤ η`, one subsequence with
  `CoulombLimit` on every cube) from the cube Prop.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.UhlenbeckCube

open SobolevOpen CriticalGauge CriticalQuotient UhlenbeckGauge

set_option linter.unusedSectionVars false

/-- The open cube of half-side `r` centred at `c`. -/
def cubeC (c : Fin 4 → ℝ) (r : ℝ) : Set (Fin 4 → ℝ) := box (fun i => c i - r) (fun i => c i + r)

theorem cubeC_eq_ball (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) : cubeC c r = Metric.ball c r := by
  ext x
  rw [Metric.mem_ball, dist_pi_lt_iff hr, cubeC, mem_box]
  refine forall_congr' fun i => ?_
  rw [Real.dist_eq, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem isOpen_cubeC (c : Fin 4 → ℝ) (r : ℝ) : IsOpen (cubeC c r) := isOpen_box _ _

theorem innerCube_subset_cubeC (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) :
    innerCube c r ⊆ cubeC c r := by
  intro x hx
  rw [innerCube, mem_box] at hx
  rw [cubeC, mem_box]
  intro i
  have := hx i
  constructor <;> linarith [this.1, this.2]

/-- **Uhlenbeck's small-energy gauge theorem on cubes** (structure-group form; the cube rendering
of `UhlenbeckGauge.UhlenbeckSmallEnergyGaugeIn`): the clauses of the ball version with the ball
`eBall c r` replaced by the cube `cubeC c r`. -/
def UhlenbeckSmallEnergyGaugeCubeIn (m : ℕ) (G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  ∃ εU : ℝ≥0, 0 < εU ∧ ∃ CU : ℝ≥0, ∀ (c : Fin 4 → ℝ) (r : ℝ), 0 < r → ∃ Cr : ℝ≥0,
    ∀ A : MConn m, IsSmoothUnitaryConn A → (∀ μ y, A μ y ∈ 𝔤) → curvEnergy A (cubeC c r) ≤ εU →
      ∃ R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ y ∈ cubeC c r, R y ∈ G) ∧
        (∀ c' e', ContDiffOn ℝ ∞ (fun y => R y c' e') (cubeC c r)) ∧
        (∀ x ∈ cubeC c r, ∀ c' e', ∑ μ, entryGrad (gaugeConn R A) μ c' e' μ x = 0) ∧
        (∀ ν c' e', MemW12 (cubeC c r) (entries (gaugeConn R A) ν c' e')
          (entryGrad (gaugeConn R A) ν c' e')) ∧
        (∀ ν c' e', w12Norm (cubeC c r) (entries (gaugeConn R A) ν c' e')
          (entryGrad (gaugeConn R A) ν c' e') ≤ Cr * curvEnergy A (cubeC c r) ^ (1 / 2 : ℝ)) ∧
        (∀ ν c' e', eLpNorm (entries (gaugeConn R A) ν c' e') 4 (volume.restrict (cubeC c r)) ≤
          CU * curvEnergy A (cubeC c r) ^ (1 / 2 : ℝ))

/-- Monotonicity in the structure data. -/
theorem UhlenbeckSmallEnergyGaugeCubeIn.mono {m : ℕ} {G G' 𝔤 𝔤' : Set (Matrix (Fin m) (Fin m) ℂ)}
    (h : UhlenbeckSmallEnergyGaugeCubeIn m G 𝔤) (hG : G ⊆ G') (h𝔤 : 𝔤' ⊆ 𝔤) :
    UhlenbeckSmallEnergyGaugeCubeIn m G' 𝔤' := by
  obtain ⟨εU, hεU, CU, hU⟩ := h
  refine ⟨εU, hεU, CU, fun c r hr => ?_⟩
  obtain ⟨Cr, hCr⟩ := hU c r hr
  refine ⟨Cr, fun A hA h𝔤A hE => ?_⟩
  obtain ⟨R, hRG, hR⟩ := hCr A hA (fun μ y => h𝔤 (h𝔤A μ y)) hE
  exact ⟨R, fun y hy => hG (hRG y hy), hR⟩

/-- **The small-energy cube cover with `G`-valued Uhlenbeck gauges** (cube rendering of
`UhlenbeckGauge.uhlenbeck_ball_cover_in`). -/
theorem uhlenbeck_cube_cover_in {m : ℕ} {G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hU : UhlenbeckSmallEnergyGaugeCubeIn m G 𝔤)
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (h𝔤 : ∀ h μ y, A h μ y ∈ 𝔤)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧ (∀ j, cubeC (ctr j) r ⊆ box a b) ∧
      K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ cubeC (ctr j) r, R h j y ∈ G) ∧
        (∀ h j c e, ContDiffOn ℝ ∞ (fun y => R h j y c e) (cubeC (ctr j) r)) ∧
        (∀ h j, ∀ x ∈ cubeC (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h j ν c e,
          MemW12 (cubeC (ctr j) r) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ∧
          w12Norm (cubeC (ctr j) r) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ B) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (cubeC (ctr j) r)) ≤ η) := by
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
  have hball : ∀ c ∈ K', cubeC c r ⊆ box a b := by
    intro c hc x hx
    refine hthick (Metric.mem_thickening_iff.mpr ⟨c, hc, ?_⟩)
    rw [cubeC_eq_ball c hr] at hx
    exact (Metric.mem_ball.mp hx).trans hrr0
  have hballvol : ∀ c, volume (cubeC c r) ≤ ENNReal.ofReal δ := fun c => by
    rw [cubeC_eq_ball c hr, Real.volume_pi_ball c hr]; exact ENNReal.ofReal_le_ofReal hvol
  have henergy : ∀ h, ∀ c ∈ K', curvEnergy (A h) (cubeC c r) ≤ εs := fun h c hc =>
    hUIδ h (cubeC c r) (isOpen_cubeC c r).measurableSet (hball c hc) (hballvol c)
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
  have hsmall : ∀ h j, curvEnergy (A h) (cubeC (ctr j) r) ≤ εU := fun h j =>
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

/-- **`prop:critical-uhlenbeck` with `G`-valued gauges from the cube rendering of Uhlenbeck's
theorem** (same conclusion as `UhlenbeckGauge.critical_uhlenbeck_of_gauge_in`). -/
theorem critical_uhlenbeck_of_gauge_cube_in {m : ℕ} {G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hU : UhlenbeckSmallEnergyGaugeCubeIn m G 𝔤)
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
    uhlenbeck_cube_cover_in hU A hA h𝔤 hUI hK' hK'Q hη
  set lo : Fin N → Fin 4 → ℝ := fun j i => ctr j i - r / 4
  set hi : Fin N → Fin 4 → ℝ := fun j i => ctr j i + r / 4
  have hcube : ∀ j, box (lo j) (hi j) ⊆ cubeC (ctr j) r := fun j =>
    innerCube_subset_cubeC (ctr j) hr
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

/-- Non-vacuity of the clauses of the cube Prop: for the trivial connection, `R = 1`. -/
example (c : Fin 4 → ℝ) (r : ℝ) :
    let R : (Fin 4 → ℝ) → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
    let A : MConn 1 := fun _ _ => 0
    (∀ y ∈ cubeC c r, R y ∈ unitaryGroup (Fin 1) ℂ) ∧
      (∀ x ∈ cubeC c r, ∀ c' e', ∑ μ, entryGrad (gaugeConn R A) μ c' e' μ x = 0) := by
  intro R A
  have hg : gaugeConn R A = fun _ _ => 0 := by
    funext μ x
    ext c' e'
    simp [gaugeConn, R, A, pdM, pd]
  exact ⟨fun _ _ => one_mem _, fun x _ c' e' => by simp [hg, entryGrad, pd]⟩

end RenewalGeometry.UhlenbeckCube
