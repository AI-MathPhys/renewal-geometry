/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevAlgebra

/-!
# `H³(B) ⊂ C⁰_b(B)` up to the boundary, weak Sobolev functions on balls of `ℝ⁴`
  (stages D1c/D4 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `uniformCauchySeqOn_of_convHk3` — smooth `H³(B)`-convergent sequences converge uniformly on the
  ball (`abs_le_n3` applied to differences);
* `exists_continuous_rep_of_memHk3` — **every weak `H³(B)` function has a representative which is
  the uniform limit on `B` of smooth functions**: continuous on `B`, bounded, a.e. equal;
* `ae_abs_le_of_memHk3`, `memLp_top_of_memHk3` — `H³(B) ⊂ L^∞(B)`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff Uniformity

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

section C0

variable (c : Fin 4 → ℝ) (r : ℝ)

/-- `n3` is controlled by the classical `H³` norm `nW`. -/
theorem n3_le_nW {s : ℕ} (hs : 3 ≤ s) (u : (Fin 4 → ℝ) → ℝ) : n3 c r u ≤ 4 * nW c r s u := by
  have := n3_pdw_le c r u (a := []) (by simpa using hs)
  simpa using this

/-- **Smooth `H³(B)`-Cauchy sequences converge uniformly on the ball.** -/
theorem uniformCauchySeqOn_of_convHk3 (hr : 0 < r) {φ : ℕ → (Fin 4 → ℝ) → ℝ}
    (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) {u : (Fin 4 → ℝ) → ℝ}
    (hc : ConvHk (euclBall c r) 3 φ u) : UniformCauchySeqOn φ atTop (euclBall c r) := by
  obtain ⟨C, hC, hb⟩ := abs_le_n3 c r hr
  obtain ⟨D, G, hG, hD, hd, -⟩ := exists_word_data c r hr hφ hc
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  -- `C * 4 * (D m + D p) → 0`
  have hlim : Tendsto (fun q : ℕ × ℕ => C * (4 * (D q.1 + D q.2))) atTop (𝓝 0) := by
    have hA : Tendsto (fun q : ℕ × ℕ => D q.1 + D q.2) atTop (𝓝 0) := by
      simpa using (hD.comp tendsto_fst_nat).add (hD.comp tendsto_snd_nat)
    have := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul hA (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)))
      (Or.inr hC)
    simpa using this
  have hev := (ENNReal.tendsto_nhds_zero.mp hlim) (ENNReal.ofReal (ε / 2)) (by simpa using hε)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨⟨N1, N2⟩, hN⟩ := hev
  refine ⟨max N1 N2, fun m hm p hp x hx => ?_⟩
  have h1 := hb (fun y => φ m y - φ p y) ((hφ m).sub (hφ p)) x hx
  have h2 : n3 c r (fun y => φ m y - φ p y) ≤ 4 * (D m + D p) :=
    (n3_le_nW c r (le_refl 3) _).trans (by gcongr; exact hd m p)
  have h3 := hN (m, p) ⟨le_trans (le_max_left _ _) hm, le_trans (le_max_right _ _) hp⟩
  have h4 : ENNReal.ofReal |φ m x - φ p x| ≤ ENNReal.ofReal (ε / 2) :=
    h1.trans ((by gcongr : C * n3 c r (fun y => φ m y - φ p y) ≤ C * (4 * (D m + D p))).trans h3)
  rw [dist_eq_norm, Real.norm_eq_abs]
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4
  linarith

/-- **`H³(B) ⊂ C⁰_b(B)` (up to the boundary)**: every weak `H³(B)` function has a representative
`v` which is the uniform limit on `B` of smooth functions (hence continuous and bounded on `B`). -/
theorem exists_continuous_rep_of_memHk3 (hr : 0 < r) {u : (Fin 4 → ℝ) → ℝ}
    (hu : MemHk (euclBall c r) 3 u) :
    ∃ (φ : ℕ → (Fin 4 → ℝ) → ℝ) (v : (Fin 4 → ℝ) → ℝ), (∀ m, ContDiff ℝ ∞ (φ m)) ∧
      ConvHk (euclBall c r) 3 φ u ∧ TendstoUniformlyOn φ v atTop (euclBall c r) ∧
      v =ᵐ[volume.restrict (euclBall c r)] u := by
  have : Fact (0 < r) := ⟨hr⟩
  obtain ⟨φ, hφ, hc⟩ := (memHk_iff_exists_convHk c r 3).mp hu
  have hU := uniformCauchySeqOn_of_convHk3 c r hr hφ hc
  -- pointwise limits
  have hcs : ∀ x ∈ euclBall c r, CauchySeq fun m => φ m x := fun x hx => hU.cauchySeq hx
  set v : (Fin 4 → ℝ) → ℝ := fun x => limUnder atTop fun m => φ m x
  have hv : ∀ x ∈ euclBall c r, Tendsto (fun m => φ m x) atTop (𝓝 (v x)) := fun x hx =>
    (hcs x hx).tendsto_limUnder
  have hTU : TendstoUniformlyOn φ v atTop (euclBall c r) :=
    hU.tendstoUniformlyOn_of_tendsto hv
  refine ⟨φ, v, hφ, hc, hTU, ?_⟩
  -- `φ m → v` and `φ m → u` in `L²(B)`
  have hfin := isFiniteMeasure_restrict_euclBall c hr.le
  have hvm : AEStronglyMeasurable v (volume.restrict (euclBall c r)) := by
    have hcont : ContinuousOn v (euclBall c r) :=
      hTU.continuousOn (Frequently.of_forall fun m => (hφ m).continuous.continuousOn)
    exact hcont.aestronglyMeasurable (measurableSet_euclBall c r)
  have h1 : Tendsto (fun m => eLpNorm (φ m - v) 2 (volume.restrict (euclBall c r))) atTop
      (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hμ : (volume.restrict (euclBall c r)) Set.univ ≠ ⊤ := measure_ne_top _ _
    -- choose `δ` with `δ * μ(B)^{1/2} ≤ ε`
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧
        ENNReal.ofReal δ * (volume.restrict (euclBall c r)) Set.univ ^ (1 / (2 : ℝ)) ≤ ε := by
      by_cases hεt : ε = ⊤
      · exact ⟨1, one_pos, by rw [hεt]; exact le_top⟩
      set M := (volume.restrict (euclBall c r)) Set.univ ^ (1 / (2 : ℝ))
      have hMt : M ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hμ
      refine ⟨ε.toReal / (M.toReal + 1), div_pos (ENNReal.toReal_pos hε.ne' hεt) (by positivity),
        ?_⟩
      calc ENNReal.ofReal (ε.toReal / (M.toReal + 1)) * M
          = ENNReal.ofReal (ε.toReal / (M.toReal + 1)) * ENNReal.ofReal M.toReal := by
            rw [ENNReal.ofReal_toReal hMt]
        _ = ENNReal.ofReal (ε.toReal / (M.toReal + 1) * M.toReal) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal ε.toReal := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [ENNReal.toReal_nonneg (a := ε), ENNReal.toReal_nonneg (a := M)]
        _ = ε := ENNReal.ofReal_toReal hεt
    have hev := (Metric.tendstoUniformlyOn_iff.mp hTU) δ hδ0
    filter_upwards [hev] with m hm
    have hpt : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ‖(φ m - v) x‖ ≤ δ := by
      filter_upwards [ae_restrict_mem (measurableSet_euclBall c r)] with x hx
      have := hm x hx
      rw [dist_comm, dist_eq_norm] at this
      simpa [Pi.sub_apply] using this.le
    refine (eLpNorm_le_of_ae_bound hpt).trans ?_
    rw [mul_comm, show ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) by norm_num]
    exact hδ
  have h2 := hc.base.2
  -- uniqueness of `L²` limits through `L²(B)`
  have hvL : MemLp v 2 (volume.restrict (euclBall c r)) := by
    have hφL : MemLp (φ 0) 2 (volume.restrict (euclBall c r)) :=
      memLp_euclBall_of_continuous c hr.le (hφ 0).continuous 2
    have hd : MemLp (φ 0 - v) 2 (volume.restrict (euclBall c r)) := by
      obtain ⟨M, hM⟩ : ∃ M, ∀ᶠ m in atTop, eLpNorm (φ m - v) 2 (volume.restrict (euclBall c r)) < M
          ∧ M < ⊤ := ⟨1, by
        filter_upwards [(ENNReal.tendsto_nhds_zero.mp h1) (1 / 2) (by norm_num)] with m hm
        exact ⟨hm.trans_lt (by norm_num), by norm_num⟩⟩
      obtain ⟨m, hm⟩ := hM.exists
      have hdm : MemLp (φ m - v) 2 (volume.restrict (euclBall c r)) :=
        ⟨((hφ m).continuous.aestronglyMeasurable).sub hvm, hm.1.trans hm.2⟩
      have e : φ 0 - v = (φ 0 - φ m) + (φ m - v) := by funext x; simp
      rw [e]
      exact ((memLp_euclBall_of_continuous c hr.le ((hφ 0).sub (hφ m)).continuous 2)).add hdm
    have e : v = φ 0 - (φ 0 - v) := by funext x; simp
    rw [e]; exact hφL.sub hd
  have hA : Tendsto (fun m => (memLp_euclBall_of_continuous c hr.le (hφ m).continuous 2).toLp
      (φ m)) atTop (𝓝 (hvL.toLp v)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']; exact h1
  have hB : Tendsto (fun m => (memLp_euclBall_of_continuous c hr.le (hφ m).continuous 2).toLp
      (φ m)) atTop (𝓝 (hc.base.1.toLp u)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']; exact h2
  have := tendsto_nhds_unique hA hB
  have hae := (MemLp.toLp_eq_toLp_iff hvL hc.base.1).mp this
  exact hae

/-- **`H³(B) ⊂ L^∞(B)`**: weak `H³(B)` functions are essentially bounded on the ball. -/
theorem ae_abs_le_of_memHk3 (hr : 0 < r) {u : (Fin 4 → ℝ) → ℝ}
    (hu : MemHk (euclBall c r) 3 u) :
    ∃ M : ℝ, ∀ᵐ x ∂(volume.restrict (euclBall c r)), |u x| ≤ M := by
  obtain ⟨φ, v, hφ, -, hTU, hvu⟩ := exists_continuous_rep_of_memHk3 c r hr hu
  -- `φ N` is within `1` of `v` on the ball and bounded on the closed ball
  obtain ⟨N, hN⟩ := ((Metric.tendstoUniformlyOn_iff.mp hTU) 1 one_pos).exists
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall c |r|).exists_bound_of_continuousOn
    (hφ N).continuous.continuousOn
  refine ⟨M0 + 1, ?_⟩
  filter_upwards [hvu, ae_restrict_mem (measurableSet_euclBall c r)] with x hx hxB
  rw [← hx]
  have h1 := hN x hxB
  have hxc : x ∈ closedBall c |r| :=
    mem_closedBall_of_sqDist_le (abs_nonneg r) (by rw [sq_abs]; exact le_of_lt hxB)
  have h2 := hM0 x hxc
  rw [Real.norm_eq_abs] at h2
  rw [Real.dist_eq] at h1
  have := abs_sub_abs_le_abs_sub (v x) (φ N x)
  linarith

end C0

end RenewalGeometry.BallAnalysis.BallReg
