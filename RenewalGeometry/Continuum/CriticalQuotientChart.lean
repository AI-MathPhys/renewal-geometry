/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientConversions

/-!
# The `G_SM` Coulomb charts with all their bounds
  (`thm:critical-quotient-defect`, `prop:critical-uhlenbeck`; Einstein–Standard-Model
  action-closure manuscript)

A re-run of `UhlenbeckGaugeClosed.critical_quotient_closure_of_gauge_in` for the Standard-Model
structure group (`G_SM = S(U(3) × U(2))`, Uhlenbeck's theorem `uhlenbeckSmallEnergyGaugeIn_SM`)
that also exports the data needed to pass the first-variation rows: the gauges `R_{h,j}` are
smooth and `G_SM`-valued on the whole Uhlenbeck balls `B_j ⊃ Q̄_j`, the Coulomb connections are
`𝔰(𝔲(3) ⊕ 𝔲(2))`-valued and uniformly bounded in `W^{1,2}(Q_j)`, the transported matter sections
are uniformly bounded in `W^{1,2}(Q_j)`, and one subsequence carries the coframe limit and the
quotient limits on every cube (`critical_quotient_chart_SM`).
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.CriticalQuotientRows

open SobolevOpen CriticalGauge CriticalQuotient CriticalQuotientClosure UhlenbeckGauge
  BallAnalysis.SMGaugeStructure BallAnalysis.UhlenbeckStandardModel SMGaugeLie EinsteinSM

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- **(Q1) in `L^∞ ∩ H¹`**: along `φ` the coframes converge uniformly and in `L²` to a bounded
limit `e₀`, and their classical partials converge in `L²` to an `L²` field `de₀` (the weak
gradient of `e₀`): `CoframeLimit` with the limit in `L^∞ ∩ H¹`. -/
def CoframeLimitH1 (K : Set (Fin 4 → ℝ)) (e : ℕ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (φ : ℕ → ℕ) : Prop :=
  ∃ (e₀ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (de₀ : Fin 4 → Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℝ),
    (∀ i ν, MemLp (fun y => e₀ y i ν) ⊤ (volume.restrict K)) ∧
    (∀ i ν μ, MemLp (de₀ i ν μ) 2 (volume.restrict K)) ∧
    ∀ i ν, Tendsto (fun k => eLpNorm (fun y => e (φ k) y i ν - e₀ y i ν) ⊤ (volume.restrict K))
        atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (fun y => e (φ k) y i ν - e₀ y i ν) 2 (volume.restrict K))
        atTop (𝓝 0) ∧
      ∀ μ, Tendsto (fun k => eLpNorm (fun y => pd (fun y => e (φ k) y i ν) μ y - de₀ i ν μ y) 2
        (volume.restrict K)) atTop (𝓝 0)

theorem CoframeLimitH1.comp {K : Set (Fin 4 → ℝ)} {e : ℕ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ}
    {φ ψ : ℕ → ℕ} (h : CoframeLimitH1 K e φ) (hψ : StrictMono ψ) : CoframeLimitH1 K e (φ ∘ ψ) := by
  obtain ⟨e₀, de₀, h1, h2, h⟩ := h
  exact ⟨e₀, de₀, h1, h2, fun i ν => ⟨(h i ν).1.comp hψ.tendsto_atTop,
    (h i ν).2.1.comp hψ.tendsto_atTop, fun μ => ((h i ν).2.2 μ).comp hψ.tendsto_atTop⟩⟩

theorem CoframeLimitH1.coframeLimit {K : Set (Fin 4 → ℝ)}
    {e : ℕ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ} {φ : ℕ → ℕ} (h : CoframeLimitH1 K e φ) :
    CoframeLimit K e φ := by
  obtain ⟨e₀, de₀, -, -, h⟩ := h
  exact ⟨e₀, de₀, h⟩

/-- **The Standard-Model Coulomb charts with all bounds** (re-run of the closure extraction with
`G_SM`-valued gauges; box rendering `K = box a b`). -/
theorem critical_quotient_chart_SM
    {a b : Fin 4 → ℝ} (A : ℕ → MConn 5) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (hsm : ∀ h μ y, Matrix.of.symm (A h μ y) ∈ smLie)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {S : Type} [Fintype S] (u : ℕ → S → (Fin 4 → ℝ) → Fin 5 → ℂ)
    (hu : ∀ h s, ContDiff ℝ ∞ (u h s))
    (hQ3 : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h s,
      ∑ e, eLpNorm (fun y => u h s y e) 2 (volume.restrict (box a b)) +
        ∑ e, ∑ μ, eLpNorm (fun y => covDerV (A h) (u h s) μ y e) 2 (volume.restrict (box a b))
          ≤ B)
    (e : ℕ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hQ1 : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      CoframeLimitH1 (box a b) e (φ ∘ ψ))
    (SH : Set S)
    (hUI4 : ∀ s ∈ SH, UnifIntegrable (fun p : ℕ × Fin 5 => fun y => u p.1 s y p.2) 4
      (volume.restrict (box a b)))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧
      (∀ j, eBall (ctr j) r ⊆ box a b) ∧ (∀ j, innerCube (ctr j) r ⊆ eBall (ctr j) r) ∧
      K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin 5) (Fin 5) ℂ,
        (∀ h j, ∀ y ∈ eBall (ctr j) r, R h j y ∈ GSM) ∧
        (∀ h j c e, ContDiffOn ℝ ∞ (fun y => R h j y c e) (eBall (ctr j) r)) ∧
        (∀ h j, ∀ y ∈ eBall (ctr j) r, ∀ μ,
          Matrix.of.symm (gaugeConn (R h j) (A h) μ y) ∈ smLie) ∧
        (∀ h j, ∀ x ∈ innerCube (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (innerCube (ctr j) r)) ≤ η) ∧
        (∃ BA : ℝ≥0∞, BA ≠ ⊤ ∧ ∀ h j ν c e,
          MemW12 (innerCube (ctr j) r) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ∧
          w12Norm (innerCube (ctr j) r) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ BA) ∧
        (∃ Bu : ℝ≥0∞, Bu ≠ ⊤ ∧ ∀ h j s c,
          MemW12 (innerCube (ctr j) r) (transp (R h j) (u h s) c) (tgrad (R h j) (u h s) c) ∧
          w12Norm (innerCube (ctr j) r) (transp (R h j) (u h s) c) (tgrad (R h j) (u h s) c)
            ≤ Bu) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ CoframeLimitH1 (box a b) e φ ∧ ∀ j,
          QuotientLimitL4 (innerCube (ctr j) r) (fun h => gaugeConn (R h j) (A h))
            (fun h s => transp (R h j) (u h s)) (fun h s => tgrad (R h j) (u h s)) φ SH := by
  obtain ⟨N, ctr, r, hr, hball, hcover, R, hRG, hRs, hdiv, ⟨BA, hBAt, hAW⟩, hA4⟩ :=
    uhlenbeck_ball_cover_in uhlenbeckSmallEnergyGaugeIn_SM A hA
      (fun h μ y => mem_gSM_of_smLie (hsm h μ y)) hUI hK' hK'Q hη
  have hRu : ∀ h j, ∀ y ∈ eBall (ctr j) r, R h j y ∈ unitaryGroup (Fin 5) ℂ :=
    fun h j y hy => (hRG h j y hy).1
  obtain ⟨B, hBt, hB⟩ := hQ3
  choose C hC using fun j => transported_bound (ctr j) hr 5
  have hT := fun h j s => hC j (R h j) (hRu h j) (hRs h j) (A h) (hA h) (u h s) (hu h s) η
    (hA4 h j)
  have hQK : ∀ j, innerCube (ctr j) r ⊆ box a b := fun j =>
    (innerCube_subset_eBall (ctr j) hr).trans (hball j)
  have hRQ : ∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ unitaryGroup (Fin 5) ℂ :=
    fun h j y hy => hRu h j y (innerCube_subset_eBall _ hr hy)
  -- uniform `W^{1,2}` bounds on every cube
  set Bj : ℝ≥0∞ := BA + (∑ j, (C j : ℝ≥0∞)) * (1 + (η : ℝ≥0∞)) * (5 * B + 5 * B)
  have hBjt : Bj ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hBAt, ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.coe_ne_top) (by simp))
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) hBt,
      ENNReal.mul_ne_top (by simp) hBt⟩)⟩
  have hsum1 : ∀ j h s, ∑ e, eLpNorm (fun y => u h s y e) 2
      (volume.restrict (innerCube (ctr j) r)) ≤ B := fun j h s =>
    (Finset.sum_le_sum fun e _ => eLpNorm_mono_measure _
      (Measure.restrict_mono (hQK j) le_rfl)).trans (le_add_right le_rfl |>.trans (hB h s))
  have hsum2 : ∀ j h s, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (A h) (u h s) μ y e) 2
      (volume.restrict (innerCube (ctr j) r)) ≤ B := fun j h s =>
    (Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun μ _ =>
      eLpNorm_mono_measure _ (Measure.restrict_mono (hQK j) le_rfl)).trans
      (le_add_left le_rfl |>.trans (hB h s))
  have hBu : ∀ j h s c, w12Norm (innerCube (ctr j) r) (transp (R h j) (u h s) c)
      (tgrad (R h j) (u h s) c) ≤ Bj := by
    intro j h s c
    refine ((hT h j s).2 c).trans (le_add_left ?_)
    have hCj : (C j : ℝ≥0∞) ≤ ∑ j, (C j : ℝ≥0∞) :=
      Finset.single_le_sum (f := fun j => (C j : ℝ≥0∞)) (fun _ _ => zero_le) (Finset.mem_univ j)
    have hm : ((5 : ℕ) : ℝ≥0∞) = 5 := by norm_num
    rw [hm]
    gcongr
    · exact hsum1 j h s
    · exact hsum2 j h s
  have hBA : ∀ j h ν c e, w12Norm (innerCube (ctr j) r)
      (entries (gaugeConn (R h j) (A h)) ν c e)
      (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ Bj := fun j h ν c e =>
    (w12Norm_mono (innerCube_subset_eBall _ hr) _ _).trans ((hAW h j ν c e).2.trans le_self_add)
  -- the common extraction for the quotient limits
  obtain ⟨φ₀, hφ₀, hQL⟩ := exists_common_subseq (fun j φ => QuotientLimit (innerCube (ctr j) r)
    (fun h => gaugeConn (R h j) (A h)) (fun h s => transp (R h j) (u h s))
    (fun h s => tgrad (R h j) (u h s)) φ) (fun j φ _ => exists_quotientLimit
      (fun i => by linarith)
      (fun h ν c e => (hAW h j ν c e).1.mono (innerCube_subset_eBall _ hr))
      (fun h s c => (hT h j s).1 c) hBjt (fun h ν c e => hBA j h ν c e)
      (fun h s c => hBu j h s c) φ) (fun j φ ψ hψ hP => hP.comp hψ)
  obtain ⟨ψ₁, hψ₁, hcf⟩ := hQ1 φ₀ hφ₀
  refine ⟨N, ctr, r, hr, hball, fun j => innerCube_subset_eBall _ hr, hcover, R, hRG, hRs,
    fun h j y hy μ => gaugeConn_mem_smLie (isOpen_eBall _ _) (hRG h j) hy
      (mDiffAt_of_contDiffOn (isOpen_eBall _ _) (hRs h j) hy) (fun ν => hsm h ν y) μ,
    fun h j x hx => hdiv h j x (innerCube_subset_eBall _ hr hx), fun h j ν c e =>
      (eLpNorm_mono_measure _ (Measure.restrict_mono (innerCube_subset_eBall _ hr) le_rfl)).trans
        (hA4 h j ν c e),
    ⟨Bj, hBjt, fun h j ν c e => ⟨(hAW h j ν c e).1.mono (innerCube_subset_eBall _ hr),
      hBA j h ν c e⟩⟩, ⟨Bj, hBjt, fun h j s c => ⟨(hT h j s).1 c, hBu j h s c⟩⟩,
    φ₀ ∘ ψ₁, hφ₀.comp hψ₁, hcf, fun j => ?_⟩
  -- the Vitali clause on every cube
  have hQL' := (hQL j).comp hψ₁
  have hcube : innerCube (ctr j) r =
      box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4) := innerCube_eq_box _ _
  have hQm : MeasurableSet (innerCube (ctr j) r) := by
    rw [hcube]; exact (isOpen_box _ _).measurableSet
  rw [hcube] at hQL' ⊢
  refine quotientLimitL4_of (fun i => by linarith) hQL' (fun k s c => ?_) (fun s hs c => ?_)
  · have := ((hT k j s).1 c).memLp.1
    rwa [hcube] at this
  · have hUIQ := unifIntegrable_restrict_subset hQm (hQK j) (hUI4 s hs)
    rw [hcube] at hUIQ hQm
    have hmeasu : ∀ h e', AEStronglyMeasurable (fun y => u h s y e')
        (volume.restrict (box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4))) :=
      fun h e' => ((continuous_apply e').comp (hu h s).continuous).aestronglyMeasurable
    have hRQ' : ∀ h, ∀ y ∈ box (fun i => ctr j i - r / 4) (fun i => ctr j i + r / 4),
        R h j y ∈ unitaryGroup (Fin 5) ℂ := fun h y hy => hRQ h j y (by rwa [hcube])
    exact unifIntegrable_transp (R := fun h => R h j) (u := fun h => u h s) hQm hRQ' hmeasu
      hUIQ c

end RenewalGeometry.CriticalQuotientRows
