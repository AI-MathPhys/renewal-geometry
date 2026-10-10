/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallUhlenbeckPath

/-!
# Classical versus weak derivatives on open sets, and continuity versus a.e. statements
  (stage D4 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `exists_smooth_cutoff` — **smooth Urysohn**: for `K` compact inside an open `Ω ⊆ ℝⁿ` there is a
  smooth `χ` with `tsupport χ ⊆ Ω`, compact support, `χ = 1` near every point of `K`
  (finitely many `ContDiffBump`s and `smoothTransition`);
* `hasWeakPartial_of_contDiffOn` — a `C¹` function on an open `Ω` has its classical partial
  derivatives as weak partial derivatives on `Ω` (cut-off to a global `C¹` function);
* `eqOn_of_ae_eq_of_continuousOn`, `mem_of_ae_mem_of_continuousOn` — continuous functions on an
  open set agreeing a.e. agree everywhere there, and a.e. values in a closed set are everywhere
  values in it (Lebesgue measure charges open sets);
* `HasWeakPartial.add`, `HasWeakPartial.const_mul`, `hasWeakPartial_re_im` — linearity of complex
  weak derivatives.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.FinalTools

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ### Smooth Urysohn -/

/-- **Smooth cut-off** equal to `1` near a compact set inside an open set. -/
theorem exists_smooth_cutoff {K Ω : Set (Fin n → ℝ)} (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) :
    ∃ χ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      ∀ x ∈ K, χ =ᶠ[𝓝 x] fun _ => 1 := by
  classical
  -- radii
  have hδ : ∀ x ∈ K, ∃ δ > 0, closedBall x (2 * δ) ⊆ Ω := by
    intro x hx
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩ x (hKΩ hx)
    exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hεΩ⟩
  choose δ hδpos hδΩ using hδ
  -- a finite subcover of `K` by the inner balls
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun x : K => ball (x : Fin n → ℝ) (δ x x.2))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hδpos x hx)⟩)
  -- the bumps
  let b : K → ContDiffBump (0 : Fin n → ℝ) := fun x =>
    ⟨δ x x.2, 2 * δ x x.2, hδpos x x.2, by linarith [hδpos x x.2]⟩
  set S : (Fin n → ℝ) → ℝ := fun y => ∑ x ∈ T, b x (y - x)
  have hS : ContDiff ℝ ∞ S :=
    ContDiff.sum fun x _ => (b x).contDiff.comp (contDiff_id.sub contDiff_const)
  set χ : (Fin n → ℝ) → ℝ := fun y => Real.smoothTransition (S y)
  have hS0 : ∀ y, y ∉ ⋃ x ∈ T, ball (x : Fin n → ℝ) (2 * δ x x.2) → S y = 0 := by
    intro y hy
    refine Finset.sum_eq_zero fun x hx => ?_
    apply (b x).zero_of_le_dist
    simp only [mem_iUnion, not_exists] at hy
    have := hy x hx
    rw [mem_ball, not_lt] at this
    simpa [dist_eq_norm] using this
  have hsupp : tsupport χ ⊆ ⋃ x ∈ T, closedBall (x : Fin n → ℝ) (2 * δ x x.2) := by
    apply closure_minimal
    · intro y hy
      by_contra h
      apply hy
      have : y ∉ ⋃ x ∈ T, ball (x : Fin n → ℝ) (2 * δ x x.2) := fun h' => h (by
        simp only [mem_iUnion] at h' ⊢
        obtain ⟨x, hx, hb⟩ := h'
        exact ⟨x, hx, ball_subset_closedBall hb⟩)
      simp [χ, hS0 y this, Real.smoothTransition.zero]
    · exact (T.finite_toSet.isClosed_biUnion fun x _ => isClosed_closedBall)
  refine ⟨χ, Real.smoothTransition.contDiff.comp hS, ?_, ?_, fun x hx => ?_⟩
  · refine HasCompactSupport.intro' (K := ⋃ x ∈ T, closedBall (x : Fin n → ℝ) (2 * δ x x.2))
      ((T.finite_toSet).isCompact_biUnion fun x _ => isCompact_closedBall _ _)
      (T.finite_toSet.isClosed_biUnion fun x _ => isClosed_closedBall) fun y hy => ?_
    have : y ∉ ⋃ x ∈ T, ball (x : Fin n → ℝ) (2 * δ x x.2) := fun h' => hy (by
      simp only [mem_iUnion] at h' ⊢
      obtain ⟨x, hx, hb⟩ := h'
      exact ⟨x, hx, ball_subset_closedBall hb⟩)
    simp [χ, hS0 y this, Real.smoothTransition.zero]
  · refine hsupp.trans ?_
    simp only [iUnion_subset_iff]
    exact fun x _ => hδΩ x x.2
  · -- `χ = 1` on the inner balls
    obtain ⟨x0, hx0T, hx0⟩ : ∃ x0 ∈ T, x ∈ ball (x0 : Fin n → ℝ) (δ x0 x0.2) := by
      have := hT hx
      simp only [mem_iUnion] at this
      obtain ⟨x0, hx0, h⟩ := this
      exact ⟨x0, hx0, h⟩
    filter_upwards [isOpen_ball.mem_nhds hx0] with y hy
    show Real.smoothTransition (S y) = 1
    apply Real.smoothTransition.one_of_one_le
    have h1 : b x0 (y - x0) = 1 := (b x0).one_of_mem_closedBall (by
      rw [mem_closedBall, dist_zero_right, ← dist_eq_norm]
      exact (mem_ball.mp hy).le)
    calc (1 : ℝ) = b x0 (y - x0) := h1.symm
      _ ≤ S y := Finset.single_le_sum (f := fun x => b x (y - x)) (fun x _ => (b x).nonneg)
          hx0T

/-! ### Classical derivatives are weak derivatives on open sets -/

/-- **A `C¹` function on an open set has its classical partials as weak partials there.** -/
theorem hasWeakPartial_of_contDiffOn {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {F : (Fin n → ℝ) → ℂ}
    (hF : ContDiffOn ℝ 1 F Ω) (i : Fin n) : HasWeakPartial Ω i F (pd F i) := by
  intro φ hφ
  obtain ⟨χ, hχ, hχc, hχΩ, hχ1⟩ := exists_smooth_cutoff hφ.compact hΩ hφ.subset
  set G : (Fin n → ℝ) → ℂ := fun y => ((χ y : ℝ) : ℂ) * F y
  have hG : ContDiff ℝ 1 G := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Ω
    · exact ((Complex.ofRealCLM.contDiff.comp (hχ.of_le (by simp))).contDiffAt).mul
        ((hF y hy).contDiffAt (hΩ.mem_nhds hy))
    · have hy' : y ∉ tsupport χ := fun h => hy (hχΩ h)
      have : G =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy'] with z hz
        simp [G, image_eq_zero_of_notMem_tsupport hz]
      exact contDiffAt_const.congr_of_eventuallyEq this
  have h := hasWeakPartial_of_contDiff Ω hG i φ hφ
  have e1 : ∀ x, ((pd φ i x : ℝ) : ℂ) * G x = ((pd φ i x : ℝ) : ℂ) * F x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have := (hχ1 x hx).self_of_nhds
      simp [G, this]
    · have : pd φ i x = 0 := by
        have hpd := hasCompactSupport_pd hφ.compact i
        exact image_eq_zero_of_notMem_tsupport (fun h' => hx (tsupport_pd_subset φ i h'))
      simp [this]
  have e2 : ∀ x, ((φ x : ℝ) : ℂ) * pd G i x = ((φ x : ℝ) : ℂ) * pd F i x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hev : G =ᶠ[𝓝 x] F := by
        filter_upwards [hχ1 x hx] with z hz
        simp [G, hz]
      unfold pd
      rw [hev.fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  simp_rw [e1, e2] at h
  exact h

/-! ### Continuity versus almost everywhere -/

theorem eqOn_of_ae_eq_of_continuousOn {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {E : Type*}
    [TopologicalSpace E] [T2Space E] {f g : (Fin n → ℝ) → E} (hf : ContinuousOn f Ω)
    (hg : ContinuousOn g Ω) (h : f =ᵐ[volume.restrict Ω] g) : EqOn f g Ω := by
  intro x hx
  by_contra hne
  -- the set where they differ is open in `Ω`
  obtain ⟨U, hU, hxU, hUne⟩ : ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U ∩ Ω, f y ≠ g y := by
    obtain ⟨V, W, hV, hW, hfV, hgW, hVW⟩ := t2_separation hne
    have h1 := (hf x hx).preimage_mem_nhdsWithin (hV.mem_nhds hfV)
    have h2 := (hg x hx).preimage_mem_nhdsWithin (hW.mem_nhds hgW)
    rw [mem_nhdsWithin] at h1 h2
    obtain ⟨U1, hU1, hxU1, hU1s⟩ := h1
    obtain ⟨U2, hU2, hxU2, hU2s⟩ := h2
    refine ⟨U1 ∩ U2, hU1.inter hU2, ⟨hxU1, hxU2⟩, fun y hy heq => ?_⟩
    have hfy : f y ∈ V := hU1s ⟨hy.1.1, hy.2⟩
    have hgy : g y ∈ W := hU2s ⟨hy.1.2, hy.2⟩
    exact Set.disjoint_left.mp hVW hfy (heq ▸ hgy)
  have hpos : 0 < volume (U ∩ Ω) := (hU.inter hΩ).measure_pos volume ⟨x, hxU, hx⟩
  have hnull : volume (U ∩ Ω) = 0 := by
    rw [EventuallyEq, ae_restrict_iff' hΩ.measurableSet] at h
    rw [ae_iff] at h
    refine measure_mono_null (fun y hy => ?_) h
    exact fun h' => hUne y hy (h' hy.2)
  exact hpos.ne' hnull

theorem mem_of_ae_mem_of_continuousOn {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {E : Type*}
    [TopologicalSpace E] {f : (Fin n → ℝ) → E} (hf : ContinuousOn f Ω) {G : Set E}
    (hG : IsClosed G) (h : ∀ᵐ x ∂(volume.restrict Ω), f x ∈ G) : ∀ x ∈ Ω, f x ∈ G := by
  intro x hx
  by_contra hne
  have h1 := (hf x hx).preimage_mem_nhdsWithin (hG.isOpen_compl.mem_nhds hne)
  rw [mem_nhdsWithin] at h1
  obtain ⟨U, hU, hxU, hUs⟩ := h1
  have hpos : 0 < volume (U ∩ Ω) := (hU.inter hΩ).measure_pos volume ⟨x, hxU, hx⟩
  have hnull : volume (U ∩ Ω) = 0 := by
    rw [ae_restrict_iff' hΩ.measurableSet, ae_iff] at h
    refine measure_mono_null (fun y hy => ?_) h
    exact fun h' => hUs ⟨hy.1, hy.2⟩ (h' hy.2)
  exact hpos.ne' hnull

end RenewalGeometry.BallAnalysis.FinalTools
