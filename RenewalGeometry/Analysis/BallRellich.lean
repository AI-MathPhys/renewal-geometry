/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevDeriv
import RenewalGeometry.Analysis.SobolevBoxCompactness

/-!
# Rellich–Kondrachov on Euclidean balls of `ℝ⁴`, and for `H^s(B)` jets
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `eLpNorm_ballExt_le` — the `L²(ℝⁿ)` norm of the reflection extension `ballExt` is controlled by
  the `L²(B)` norm;
* `rellich_euclBall_C1` — **Rellich on balls for `C¹` functions**: bounded in `W^{1,2}(B_r(c))`
  ⟹ a subsequence converges in `L²(B_r(c))` (reflection extension + `rellich_ball`);
* `rellich_euclBall` — the same for weak `H¹(B)` functions (smooth approximation);
* `rellich_HsB` — **compactness of `H^{s+1}(B) ⊂ H^s(B)`** for jets (component-wise Rellich and a
  finite diagonal extraction).
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg

set_option linter.unusedSectionVars false

section Extension

variable {n : ℕ} [NeZero n]

/-- The extension is bounded in `L²` by the function. -/
theorem eLpNorm_ballExt_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : (Fin n → ℝ) → ℂ}
    (hu : ContDiff ℝ 1 u) :
    eLpNorm (ballExt c r u) 2 volume ≤
      (1 + ENNReal.ofReal (3 ^ (n - 1)) ^ (1 / 2 : ℝ)) *
        eLpNorm u 2 (volume.restrict (euclBall c r)) := by
  have hB := measurableSet_euclBall c r
  have hA := measurableSet_annulus c r
  rw [ballExt_eq_add]
  have hext : Continuous (extOut c r u) := (contDiff_extOut c hr hu).continuous
  refine (eLpNorm_add_le (hu.continuous.aestronglyMeasurable.indicator hB)
    (hext.aestronglyMeasurable.indicator hB.compl) (by norm_num)).trans ?_
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hB, eLpNorm_indicator_eq_eLpNorm_restrict hB.compl,
    add_mul, one_mul]
  refine add_le_add le_rfl ?_
  have h1 : eLpNorm (extOut c r u) 2 (volume.restrict (euclBall c r)ᶜ) ≤
      eLpNorm ((annulus c r).indicator fun x => ‖u (reflBall c r x)‖) 2
        (volume.restrict (euclBall c r)ᶜ) := by
    refine eLpNorm_mono_ae (ae_restrict_of_forall_mem hB.compl fun x hx => ?_)
    have hx1 : r ^ 2 ≤ sqDist c x := not_lt.mp hx
    by_cases hxa : x ∈ annulus c r
    · rw [indicator_of_mem hxa, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      unfold extOut
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (extCut_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (extCut_le_one _)
    · have hfar : 9 / 4 * r ^ 2 ≤ sqDist c x := by
        by_contra h; exact hxa ⟨hx1, (not_le.mp h).le⟩
      rw [extOut_eq_zero hr u hfar, norm_zero]; exact norm_nonneg _
  have h2 : eLpNorm ((annulus c r).indicator fun x => ‖u (reflBall c r x)‖) 2
      (volume.restrict (euclBall c r)ᶜ) ≤
        eLpNorm (fun x => ‖u (reflBall c r x)‖) 2 (volume.restrict (annulus c r)) := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hA]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have h3 := eLpNorm_annulus_comp_le c hr hu.continuous
  rw [eLpNorm_norm] at h2
  exact h1.trans (h2.trans h3)

theorem sqDist_gt_of_norm_gt (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {x : Fin n → ℝ}
    (hx : ‖c‖ + 2 * r < ‖x‖) : 9 / 4 * r ^ 2 < sqDist c x := by
  have h1 : 2 * r < ‖x - c‖ := by
    have := norm_sub_norm_le x c
    linarith
  obtain ⟨i, hi⟩ : ∃ i, 2 * r < |x i - c i| := by
    by_contra h
    push_neg at h
    have : ‖x - c‖ ≤ 2 * r := (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      rw [Pi.sub_apply, Real.norm_eq_abs]; exact h i
    linarith
  have h2 : (x i - c i) ^ 2 ≤ sqDist c x :=
    Finset.single_le_sum (f := fun i => (x i - c i) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h3 : (2 * r) ^ 2 < (x i - c i) ^ 2 := by
    rw [← sq_abs (x i - c i)]
    exact pow_lt_pow_left₀ hi (by positivity) (by norm_num)
  nlinarith

/-- **Rellich–Kondrachov on Euclidean balls, `C¹` functions**: a sequence bounded in
`W^{1,2}(B_r(c))` has a subsequence converging in `L²(B_r(c))`. -/
theorem rellich_euclBall_C1 (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (u : ℕ → (Fin n → ℝ) → ℂ)
    (hu : ∀ k, ContDiff ℝ 1 (u k)) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hb : ∀ k, eLpNorm (u k) 2 (volume.restrict (euclBall c r)) +
      ∑ i, eLpNorm (pd (u k) i) 2 (volume.restrict (euclBall c r)) ≤ M) :
    ∃ (φ : ℕ → ℕ) (v : (Fin n → ℝ) → ℂ), StrictMono φ ∧ MemLp v 2 volume ∧
      Tendsto (fun k => eLpNorm (u (φ k) - v) 2 (volume.restrict (euclBall c r))) atTop (𝓝 0) := by
  obtain ⟨Md, hMd0, hMd⟩ := exists_bound_deriv_extCut
  set K := ENNReal.ofReal (3 ^ (n - 1)) ^ (1 / 2 : ℝ)
  have hK : K ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  set R := ‖c‖ + 2 * r
  have hR : 0 ≤ R := by positivity
  set U : ℕ → (Fin n → ℝ) → ℂ := fun k => ballExt c r (u k)
  set G : ℕ → Fin n → (Fin n → ℝ) → ℂ := fun k => ballExtGrad c r (u k)
  have hW : ∀ k, MemW12 univ (U k) (G k) := fun k => memW12_ballExt c hr (hu k)
  have hU0 : ∀ k x, R < ‖x‖ → U k x = 0 := fun k x hx => ballExt_eq_zero c hr (u k) hx
  have hG0 : ∀ k i x, R < ‖x‖ → G k i x = 0 := by
    intro k i x hx
    have hfar := sqDist_gt_of_norm_gt c hr hx
    have hnot : x ∉ euclBall c r := by
      simp only [euclBall, mem_setOf_eq, not_lt]; nlinarith [sq_nonneg r]
    simp only [G, ballExtGrad_eq_add, Pi.add_apply, indicator_of_notMem hnot, zero_add,
      indicator_of_mem (show x ∈ (euclBall c r)ᶜ from hnot)]
    exact pd_extOut_eq_zero c hr (u k) hfar i
  set T : ℝ≥0∞ := (1 + K) + n * (1 + K * (ENNReal.ofReal (3 * Md / r) + 4))
  have hT : T ≠ ⊤ := by finiteness
  have hWb : ∀ k, w12Norm univ (U k) (G k) ≤ T * M := by
    intro k
    unfold w12Norm
    rw [Measure.restrict_univ]
    have h1 := eLpNorm_ballExt_le c hr (hu k)
    have h2 : ∀ i, eLpNorm (G k i) 2 volume ≤
        eLpNorm (pd (u k) i) 2 (volume.restrict (euclBall c r)) +
          K * (ENNReal.ofReal (3 * Md / r) * eLpNorm (u k) 2 (volume.restrict (euclBall c r)) +
            4 * ∑ j, eLpNorm (pd (u k) j) 2 (volume.restrict (euclBall c r))) := fun i =>
      (eLpNorm_ballExtGrad_le c hr (hu k) i).trans
        (add_le_add le_rfl (eLpNorm_pd_extOut_le c hr (hu k) hMd0 hMd i))
    have hu1 : eLpNorm (u k) 2 (volume.restrict (euclBall c r)) ≤ M :=
      le_trans le_self_add (hb k)
    have hu2 : ∑ j, eLpNorm (pd (u k) j) 2 (volume.restrict (euclBall c r)) ≤ M :=
      le_trans le_add_self (hb k)
    have hu3 : ∀ i, eLpNorm (pd (u k) i) 2 (volume.restrict (euclBall c r)) ≤ M := fun i =>
      (Finset.single_le_sum (f := fun j => eLpNorm (pd (u k) j) 2
        (volume.restrict (euclBall c r))) (fun _ _ => zero_le) (Finset.mem_univ i)).trans hu2
    calc eLpNorm (U k) 2 volume + ∑ i, eLpNorm (G k i) 2 volume
        ≤ (1 + K) * M + ∑ _i : Fin n, (M + K * (ENNReal.ofReal (3 * Md / r) * M + 4 * M)) := by
          gcongr with i
          · exact h1.trans (by gcongr)
          · exact (h2 i).trans (by gcongr; exact hu3 i)
      _ = T * M := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, T]
          ring
  obtain ⟨φ, v, hφ, hv, hlim⟩ := rellich_ball hR U G hW hU0 hG0
    (ENNReal.mul_ne_top hT hM) hWb
  refine ⟨φ, v, hφ, hv, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => bot_le)
    (fun k => ?_)
  have e : eLpNorm (u (φ k) - v) 2 (volume.restrict (euclBall c r)) =
      eLpNorm (U (φ k) - v) 2 (volume.restrict (euclBall c r)) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' (measurableSet_euclBall c r)).mpr
      (Eventually.of_forall fun x hx => ?_))
    simp [U, ballExt, hx]
  rw [e]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

end Extension

section Weak

variable (c : Fin 4 → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- **Rellich–Kondrachov on balls for weak `H¹(B)` functions** (real-valued). -/
theorem rellich_euclBall (u : ℕ → (Fin 4 → ℝ) → ℝ) (g : ℕ → Fin 4 → (Fin 4 → ℝ) → ℝ)
    (hu : ∀ k, MemLp (u k) 2 (volume.restrict (euclBall c r)))
    (hg : ∀ k i, MemLp (g k i) 2 (volume.restrict (euclBall c r)))
    (hw : ∀ k i, HasWeakPartialR (euclBall c r) i (u k) (g k i)) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hb : ∀ k, eLpNorm (u k) 2 (volume.restrict (euclBall c r)) +
      ∑ i, eLpNorm (g k i) 2 (volume.restrict (euclBall c r)) ≤ M) :
    ∃ (φ : ℕ → ℕ) (v : (Fin 4 → ℝ) → ℝ), StrictMono φ ∧
      MemLp v 2 (volume.restrict (euclBall c r)) ∧
      Tendsto (fun k => eLpNorm (u (φ k) - v) 2 (volume.restrict (euclBall c r))) atTop (𝓝 0) := by
  set μB := volume.restrict (euclBall c r)
  have hfin := isFiniteMeasure_restrict_euclBall c hr.out.le
  -- smooth approximants with small errors
  have hex : ∀ k, ∃ ψ : (Fin 4 → ℝ) → ℝ, ContDiff ℝ ∞ ψ ∧
      eLpNorm (ψ - u k) 2 μB ≤ ENNReal.ofReal (1 / (k + 1)) ∧
      ∑ i, eLpNorm (pd ψ i - g k i) 2 μB ≤ ENNReal.ofReal (1 / (k + 1)) := by
    intro k
    have hk1 : MemHk (euclBall c r) 1 (u k) := ⟨hu k, fun i => ⟨g k i, hw k i, hg k i⟩⟩
    obtain ⟨φ, hφ, hcv⟩ := (memHk_iff_exists_convHk c r 1).mp hk1
    have hd : ∀ i, Tendsto (fun m => eLpNorm (pd (φ m) i - g k i) 2 μB) atTop (𝓝 0) := by
      intro i
      obtain ⟨g', hg'⟩ := hcv.2 i
      have hw' := hasWeakPartialR_of_conv (isBounded_euclBall' c r) (measurableSet_euclBall c r)
        hφ hcv.1.1 hg'.1 hcv.1.2 hg'.2
      have e : g' =ᵐ[μB] g k i := by
        have := weakR_ae_eq (isOpen_euclBall c r) hw' (hw k i) hg'.1 (hg k i)
        rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]; exact this
      exact hg'.2.congr fun m => eLpNorm_congr_ae (EventuallyEq.rfl.sub e)
    have hsum : Tendsto (fun m => ∑ i, eLpNorm (pd (φ m) i - g k i) 2 μB) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun i _ => hd i
    have hε : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / (k + 1)) := by
      rw [ENNReal.ofReal_pos]; positivity
    obtain ⟨m, hm1, hm2⟩ := ((ENNReal.tendsto_nhds_zero.mp hcv.1.2 _ hε).and
      (ENNReal.tendsto_nhds_zero.mp hsum _ hε)).exists
    exact ⟨φ m, hφ m, hm1, hm2⟩
  choose ψ hψ hψ1 hψ2 using hex
  -- the smooth approximants are bounded in `H¹(B)`
  have hψb : ∀ k, eLpNorm (fun x => ((ψ k x : ℝ) : ℂ)) 2 μB +
      ∑ i, eLpNorm (pd (fun x => ((ψ k x : ℝ) : ℂ)) i) 2 μB ≤ M + 1 + 4 := by
    intro k
    have hpd : ∀ i, pd (fun x => ((ψ k x : ℝ) : ℂ)) i = fun x => ((pd (ψ k) i x : ℝ) : ℂ) :=
      fun i => funext fun x => pd_ofReal_fun ((hψ k).of_le (by simp)) i x
    simp only [hpd]
    have e1 : eLpNorm (fun x => ((ψ k x : ℝ) : ℂ)) 2 μB = eLpNorm (ψ k) 2 μB := by
      exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp)
    have e2 : ∀ i, eLpNorm (fun x => ((pd (ψ k) i x : ℝ) : ℂ)) 2 μB = eLpNorm (pd (ψ k) i) 2 μB :=
      fun i => eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp)
    simp only [e1, e2]
    have hk1 : ENNReal.ofReal (1 / (k + 1)) ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h1 : eLpNorm (ψ k) 2 μB ≤ eLpNorm (u k) 2 μB + 1 := by
      have := eLpNorm_le_via (hψ k).continuous.aestronglyMeasurable (hu k).aestronglyMeasurable
        (μ := μB)
      refine this.trans ?_
      rw [add_comm]
      gcongr
      exact (hψ1 k).trans hk1
    have h2 : ∀ i, eLpNorm (pd (ψ k) i) 2 μB ≤ eLpNorm (g k i) 2 μB + 1 := by
      intro i
      have := eLpNorm_le_via (continuous_pd ((hψ k).of_le (by simp)) i).aestronglyMeasurable
        (hg k i).aestronglyMeasurable (μ := μB)
      refine this.trans ?_
      rw [add_comm]
      gcongr
      refine le_trans ?_ ((hψ2 k).trans hk1)
      exact Finset.single_le_sum (f := fun i => eLpNorm (pd (ψ k) i - g k i) 2 μB)
        (fun _ _ => zero_le) (Finset.mem_univ i)
    calc eLpNorm (ψ k) 2 μB + ∑ i, eLpNorm (pd (ψ k) i) 2 μB
        ≤ (eLpNorm (u k) 2 μB + 1) + ∑ i : Fin 4, (eLpNorm (g k i) 2 μB + 1) := by
          exact add_le_add h1 (Finset.sum_le_sum fun i _ => h2 i)
      _ = (eLpNorm (u k) 2 μB + ∑ i, eLpNorm (g k i) 2 μB) + 1 + 4 := by
          rw [Finset.sum_add_distrib]; simp; ring
      _ ≤ M + 1 + 4 := by gcongr; exact hb k
  obtain ⟨φ, v, hφ, hv, hlim⟩ := rellich_euclBall_C1 c hr.out (fun k x => ((ψ k x : ℝ) : ℂ))
    (fun k => Complex.ofRealCLM.contDiff.comp ((hψ k).of_le (by simp)))
    (M := M + 1 + 4) (by finiteness) hψb
  -- the real limit
  set w : (Fin 4 → ℝ) → ℝ := fun x => (v x).re
  have hwm : MemLp w 2 μB := (hv.restrict _).re
  refine ⟨φ, w, hφ, hwm, ?_⟩
  have hb1 : ∀ k, eLpNorm (ψ (φ k) - w) 2 μB ≤
      eLpNorm ((fun x => ((ψ (φ k) x : ℝ) : ℂ)) - v) 2 μB := by
    intro k
    refine eLpNorm_mono fun x => ?_
    simp only [Pi.sub_apply, Real.norm_eq_abs, w]
    calc |ψ (φ k) x - (v x).re| = |(((ψ (φ k) x : ℝ) : ℂ) - v x).re| := by simp
      _ ≤ ‖((ψ (φ k) x : ℝ) : ℂ) - v x‖ := Complex.abs_re_le_norm _
  have hlim2 : Tendsto (fun k => eLpNorm (ψ (φ k) - u (φ k)) 2 μB) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ENNReal.ofReal (1 / ((φ k : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      simpa [Function.comp_def] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le)
      fun k => hψ1 (φ k)
  have hsum := (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hb1).add hlim2
  rw [zero_add] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
    fun k => ?_
  have e : u (φ k) - w = (ψ (φ k) - w) - (ψ (φ k) - u (φ k)) := by funext x; simp
  rw [e]
  exact (eLpNorm_sub_le ((hψ _).continuous.aestronglyMeasurable.sub hwm.aestronglyMeasurable)
    ((hψ _).continuous.aestronglyMeasurable.sub (hu _).aestronglyMeasurable) (by norm_num))


/-- Common subsequence for finitely many subsequence-stable properties (finite diagonal
extraction). -/
theorem exists_common_subseq' {N : ℕ} (P : Fin N → (ℕ → ℕ) → Prop)
    (hP : ∀ j (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P j (φ ∘ ψ))
    (hmono : ∀ j (φ ψ : ℕ → ℕ), StrictMono ψ → P j φ → P j (φ ∘ ψ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, P j φ := by
  have key : ∀ n : ℕ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j : Fin N, (j : ℕ) < n → P j φ := by
    intro n
    induction n with
    | zero => exact ⟨id, strictMono_id, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨φ, hφ, hP'⟩ := ih
      by_cases hn : n < N
      · obtain ⟨ψ, hψ, hj⟩ := hP ⟨n, hn⟩ φ hφ
        refine ⟨φ ∘ ψ, hφ.comp hψ, fun j hjn => ?_⟩
        by_cases hjn' : (j : ℕ) = n
        · have : j = ⟨n, hn⟩ := Fin.ext hjn'
          subst this; exact hj
        · exact hmono j φ ψ hψ (hP' j (by omega))
      · exact ⟨φ, hφ, fun j hj => hP' j (by have := j.isLt; omega)⟩
  obtain ⟨φ, hφ, h⟩ := key N
  exact ⟨φ, hφ, fun j => h j j.isLt⟩

/-- A bounded sequence of `H¹(B)` data in `L²(B)`-elements has an `L²`-convergent subsequence:
the component-wise step of `rellich_HsB`. -/
theorem exists_tendsto_L2B_of_H1 (u : ℕ → L2B c r) (g : ℕ → Fin 4 → L2B c r)
    (hw : ∀ k i, HasWeakPartialR (euclBall c r) i (u k : (Fin 4 → ℝ) → ℝ)
      (g k i : (Fin 4 → ℝ) → ℝ)) {M : ℝ} (hb : ∀ k, ‖u k‖ ≤ M ∧ ∀ i, ‖g k i‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (v : L2B c r), StrictMono φ ∧ Tendsto (fun k => u (φ k)) atTop (𝓝 v) := by
  have hE : ∀ f : L2B c r, eLpNorm (f : (Fin 4 → ℝ) → ℝ) 2 (volume.restrict (euclBall c r)) =
      ENNReal.ofReal ‖f‖ := fun f => by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  obtain ⟨φ, v, hφ, hv, hlim⟩ := rellich_euclBall c r (fun k => (u k : (Fin 4 → ℝ) → ℝ))
    (fun k i => (g k i : (Fin 4 → ℝ) → ℝ)) (fun k => Lp.memLp _) (fun k i => Lp.memLp _) hw
    (M := ENNReal.ofReal M + 4 * ENNReal.ofReal M) (by finiteness) (fun k => by
      simp only [hE]
      gcongr
      · exact (hb k).1
      · calc ∑ i : Fin 4, ENNReal.ofReal ‖g k i‖ ≤ ∑ _i : Fin 4, ENNReal.ofReal M :=
              Finset.sum_le_sum fun i _ => ENNReal.ofReal_le_ofReal ((hb k).2 i)
          _ = 4 * ENNReal.ofReal M := by simp)
  refine ⟨φ, hv.toLp v, hφ, ?_⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm]
  exact hlim

/-- **Rellich for jets: `H^{s+1}(B) ⊂⊂ H^s(B)`.** A bounded sequence in `HsB c r (s+1)` has a
subsequence whose restriction to `HsB c r s` converges. -/
theorem rellich_HsB {s : ℕ} (F : ℕ → HsB c r (s + 1)) {M : ℝ} (hM : ∀ k, ‖F k‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (G : HsB c r s), StrictMono φ ∧
      Tendsto (fun k => restrL c r (Nat.le_succ s) (F (φ k))) atTop (𝓝 G) := by
  classical
  set W := ↥(wordsUpTo 4 s)
  let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  have hmem : ∀ w : W, w.1 ∈ wordsUpTo 4 (s + 1) := fun w => mem_wordsUpTo_mono (Nat.le_succ s) w.2
  have hmemi : ∀ (w : W) (i : Fin 4), i :: w.1 ∈ wordsUpTo 4 (s + 1) := fun w i =>
    mem_wordsUpTo.mpr (by have := mem_wordsUpTo.mp w.2; simp; omega)
  let comp : ℕ → W → L2B c r := fun k w => (F k : JetAmb c r (s + 1)) ⟨w.1, hmem w⟩
  let P : Fin (Fintype.card W) → (ℕ → ℕ) → Prop := fun j φ =>
    ∃ v : L2B c r, Tendsto (fun k => comp (φ k) (e j)) atTop (𝓝 v)
  have hnorm : ∀ k (w' : ↥(wordsUpTo 4 (s + 1))), ‖(F k : JetAmb c r (s + 1)) w'‖ ≤ M :=
    fun k w' => (PiLp.norm_apply_le _ w').trans (hM k)
  obtain ⟨φ, hφ, hP⟩ := exists_common_subseq' P (fun j φ hφ => by
      obtain ⟨ψ, v, hψ, hv⟩ := exists_tendsto_L2B_of_H1 c r (fun k => comp (φ k) (e j))
        (fun k i => (F (φ k) : JetAmb c r (s + 1)) ⟨i :: (e j).1, hmemi (e j) i⟩)
        (fun k i => (F (φ k)).2 ⟨(e j).1, hmem (e j)⟩ i (hmemi (e j) i))
        (fun k => ⟨hnorm _ _, fun i => hnorm _ _⟩)
      exact ⟨ψ, hψ, v, hv⟩)
    (fun j φ ψ hψ ⟨v, hv⟩ => ⟨v, hv.comp hψ.tendsto_atTop⟩)
  choose v hv using hP
  let Gj : JetAmb c r s := WithLp.toLp 2 fun w => v (e.symm w)
  have hconv : Tendsto (fun k => restrJet c r (Nat.le_succ s) (F (φ k) : JetAmb c r (s + 1)))
      atTop (𝓝 Gj) := by
    refine ((PiLp.continuous_toLp 2 _).tendsto _).comp ?_
    rw [tendsto_pi_nhds]
    intro w
    have := hv (e.symm w)
    simp only [Equiv.apply_symm_apply] at this
    exact this
  have hG : Gj ∈ HsB c r s :=
    (isClosed_HsB c r s).mem_of_tendsto hconv (Eventually.of_forall fun k =>
      restrJet_mem c r (Nat.le_succ s) (F (φ k)).2)
  refine ⟨φ, ⟨Gj, hG⟩, hφ, ?_⟩
  rw [tendsto_subtype_rng]
  exact hconv

end Weak

end RenewalGeometry.BallAnalysis.BallAlg
