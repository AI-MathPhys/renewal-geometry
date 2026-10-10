/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.UhlenbeckGaugeClosed
import RenewalGeometry.Continuum.UhlenbeckCubeGauge

/-!
# Critical gauge-quotient closure from the cube rendering of Uhlenbeck's theorem
  (`thm:critical-quotient-defect`, Einstein–Standard-Model action-closure manuscript)

* `ball_cover_of_cube_cover`: the cube cover `UhlenbeckCube.uhlenbeck_cube_cover_in` restricted to
  the inscribed Euclidean balls `eBall c r ⊆ cubeC c r` has all the clauses of the ball cover
  `UhlenbeckGauge.uhlenbeck_ball_cover_in` (the inner cubes `box(c ∓ r/4)` lie in the balls);
* `critical_quotient_closure_of_gauge_cube_in`: the composed compactness / coframe / Vitali
  statement `UhlenbeckGaugeClosed.critical_quotient_closure_of_gauge_in`, conditional on the cube
  rendering `UhlenbeckSmallEnergyGaugeCubeIn m G 𝔤` instead of the ball Prop (same conclusion).
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.UhlenbeckCubeClosed

open SobolevOpen CriticalGauge CriticalQuotient CriticalQuotientClosure UhlenbeckGauge
  UhlenbeckCube

set_option linter.unusedSectionVars false

theorem eBall_subset_cubeC (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) : eBall c r ⊆ cubeC c r := by
  rw [cubeC_eq_ball c hr]; exact eBall_subset_ball c hr

/-- **The ball cover from the cube cover**: restricting the Coulomb gauges of the cube cover to
the inscribed Euclidean balls gives all the clauses of `uhlenbeck_ball_cover_in`. -/
theorem ball_cover_of_cube_cover {m : ℕ} {G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hU : UhlenbeckSmallEnergyGaugeCubeIn m G 𝔤)
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
  obtain ⟨N, ctr, r, hr, hcube, hcov, R, hRG, hRs, hdiv, ⟨B, hBt, hB⟩, h4⟩ :=
    uhlenbeck_cube_cover_in hU A hA h𝔤 hUI hK' hK'Q hη
  have hsub : ∀ j, eBall (ctr j) r ⊆ cubeC (ctr j) r := fun j => eBall_subset_cubeC _ hr
  exact ⟨N, ctr, r, hr, fun j => (hsub j).trans (hcube j), hcov, R,
    fun h j y hy => hRG h j y (hsub j hy), fun h j c e => (hRs h j c e).mono (hsub j),
    fun h j x hx => hdiv h j x (hsub j hx), ⟨B, hBt, fun h j ν c e =>
      ⟨(hB h j ν c e).1.mono (hsub j), (w12Norm_mono (hsub j) _ _).trans (hB h j ν c e).2⟩⟩,
    fun h j ν c e => (eLpNorm_mono_measure _ (Measure.restrict_mono (hsub j) le_rfl)).trans
      (h4 h j ν c e)⟩

/-- **`thm:critical-quotient-defect`, composed compactness and Vitali clauses, conditional on
the cube rendering of Uhlenbeck's theorem** (`UhlenbeckSmallEnergyGaugeCubeIn m G 𝔤`); same
hypotheses and conclusion as `UhlenbeckGaugeClosed.critical_quotient_closure_of_gauge_in`. -/
theorem critical_quotient_closure_of_gauge_cube_in {m : ℕ} {G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hU : UhlenbeckSmallEnergyGaugeCubeIn m G 𝔤) (hG : G ⊆ unitaryGroup (Fin m) ℂ)
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (h𝔤 : ∀ h μ y, A h μ y ∈ 𝔤)
    (_hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (A h) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {S : Type} [Fintype S] (u : ℕ → S → (Fin 4 → ℝ) → Fin m → ℂ)
    (hu : ∀ h s, ContDiff ℝ ∞ (u h s))
    (hQ3 : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h s,
      ∑ e, eLpNorm (fun y => u h s y e) 2 (volume.restrict (box a b)) +
        ∑ e, ∑ μ, eLpNorm (fun y => covDerV (A h) (u h s) μ y e) 2 (volume.restrict (box a b))
          ≤ B)
    (e : ℕ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hQ1 : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      CoframeLimit (box a b) e (φ ∘ ψ))
    {P : Type*} [MetricSpace P] {Pset : Set P} (hPset : IsCompact Pset) (θ : ℕ → P)
    (hθ : ∀ h, θ h ∈ Pset)
    (SH : Set S)
    (hUI4 : ∀ s ∈ SH, UnifIntegrable (fun p : ℕ × Fin m => fun y => u p.1 s y p.2) 4
      (volume.restrict (box a b)))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧
      (∀ j, innerCube (ctr j) r ⊆ box a b) ∧ K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ G) ∧
        (∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ unitaryGroup (Fin m) ℂ) ∧
        (∀ h j, ∀ x ∈ innerCube (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (innerCube (ctr j) r)) ≤ η) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ CoframeLimit (box a b) e φ ∧
          (∃ θ₀ ∈ Pset, Tendsto (θ ∘ φ) atTop (𝓝 θ₀)) ∧ ∀ j,
          QuotientLimitL4 (innerCube (ctr j) r) (fun h => gaugeConn (R h j) (A h))
            (fun h s => transp (R h j) (u h s)) (fun h s => tgrad (R h j) (u h s)) φ SH := by
  obtain ⟨N, ctr, r, hr, hball, hcover, R, hRG, hRs, hdiv, ⟨BA, hBAt, hAW⟩, hA4⟩ :=
    ball_cover_of_cube_cover hU A hA h𝔤 hUI hK' hK'Q hη
  have hRu : ∀ h j, ∀ y ∈ eBall (ctr j) r, R h j y ∈ unitaryGroup (Fin m) ℂ :=
    fun h j y hy => hG (hRG h j y hy)
  obtain ⟨B, hBt, hB⟩ := hQ3
  choose C hC using fun j => transported_bound (ctr j) hr m
  have hT := fun h j s => hC j (R h j) (hRu h j) (hRs h j) (A h) (hA h) (u h s) (hu h s) η
    (hA4 h j)
  have hQK : ∀ j, innerCube (ctr j) r ⊆ box a b := fun j =>
    (innerCube_subset_eBall (ctr j) hr).trans (hball j)
  have hRQ : ∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ unitaryGroup (Fin m) ℂ :=
    fun h j y hy => hRu h j y (innerCube_subset_eBall _ hr hy)
  refine ⟨N, ctr, r, hr, hQK, hcover, R,
    fun h j y hy => hRG h j y (innerCube_subset_eBall _ hr hy), hRQ,
    fun h j x hx => hdiv h j x (innerCube_subset_eBall _ hr hx), fun h j ν c e =>
      (eLpNorm_mono_measure _ (Measure.restrict_mono (innerCube_subset_eBall _ hr) le_rfl)).trans
        (hA4 h j ν c e), ?_⟩
  -- uniform `W^{1,2}` bounds on every cube
  set Bj : Fin N → ℝ≥0∞ := fun j => BA + (C j : ℝ≥0∞) * (1 + (η : ℝ≥0∞)) * (m * B + m * B)
  have hBjt : ∀ j, Bj j ≠ ⊤ := fun j => ENNReal.add_ne_top.mpr ⟨hBAt, ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp)) (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by simp) hBt, ENNReal.mul_ne_top (by simp) hBt⟩)⟩
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
      (tgrad (R h j) (u h s) c) ≤ Bj j := by
    intro j h s c
    refine ((hT h j s).2 c).trans (le_add_left ?_)
    gcongr
    · exact hsum1 j h s
    · exact hsum2 j h s
  have hBA : ∀ j h ν c e, w12Norm (innerCube (ctr j) r)
      (entries (gaugeConn (R h j) (A h)) ν c e)
      (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ Bj j := fun j h ν c e =>
    (w12Norm_mono (innerCube_subset_eBall _ hr) _ _).trans ((hAW h j ν c e).2.trans le_self_add)
  -- the common extraction for the quotient limits
  obtain ⟨φ₀, hφ₀, hQL⟩ := exists_common_subseq (fun j φ => QuotientLimit (innerCube (ctr j) r)
    (fun h => gaugeConn (R h j) (A h)) (fun h s => transp (R h j) (u h s))
    (fun h s => tgrad (R h j) (u h s)) φ) (fun j φ _ => exists_quotientLimit
      (fun i => by linarith)
      (fun h ν c e => (hAW h j ν c e).1.mono (innerCube_subset_eBall _ hr))
      (fun h s c => (hT h j s).1 c) (hBjt j) (fun h ν c e => hBA j h ν c e)
      (fun h s c => hBu j h s c) φ) (fun j φ ψ hψ hP => hP.comp hψ)
  -- (Q1): coframes, then the compact banks
  obtain ⟨ψ₁, hψ₁, hcf⟩ := hQ1 φ₀ hφ₀
  obtain ⟨θ₀, hθ₀, ψ₂, hψ₂, hθlim⟩ := hPset.tendsto_subseq (fun k => hθ ((φ₀ ∘ ψ₁) k))
  refine ⟨φ₀ ∘ ψ₁ ∘ ψ₂, hφ₀.comp (hψ₁.comp hψ₂), ?_, ⟨θ₀, hθ₀, hθlim⟩, fun j => ?_⟩
  · exact hcf.comp hψ₂
  -- the Vitali clause on every cube
  have hQL' := (hQL j).comp (hψ₁.comp hψ₂)
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
        R h j y ∈ unitaryGroup (Fin m) ℂ := fun h y hy => hRQ h j y (by rwa [hcube])
    exact unifIntegrable_transp (R := fun h => R h j) (u := fun h => u h s) hQm hRQ' hmeasu
      hUIQ c

end RenewalGeometry.UhlenbeckCubeClosed
