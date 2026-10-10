/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallJetSeminorm

/-!
# Functions in every `H^k(B)` are smooth on the open ball
  (stage D4 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `exists_convHk_pdw` — if smooth `φ_m → u` in `H^{k+|w|}(B)` then `∂^w φ_m` converges in `H^k(B)`;
* `exists_smooth_rep` (**main result**): if `u ∈ H^k(B_r(c))` for every `k`, there is `f`,
  `C^∞` on the open ball, with `f = u` a.e. on the ball and with classical partial derivatives
  that are the weak partial derivatives of `u` (`HasWeakPartialR`).  Proof: the explicit smooth
  approximants `smoothApprox` converge in every `H^k(B)`; all their derivatives converge uniformly
  on the ball (`H³(B) ⊂ C⁰_b(B)`, `uniformCauchySeqOn_of_convHk3`); uniform limits with uniformly
  convergent derivatives are differentiable (`hasFDerivAt_of_tendstoUniformlyOn`), and induction
  on the order.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.SmoothRep

open SobolevOpen BallReg

set_option linter.unusedSectionVars false

variable (c : Fin 4 → ℝ) (r : ℝ)

/-- Derivatives of `H^{k+|w|}`-convergent sequences converge in `H^k`. -/
theorem exists_convHk_pdw {φ : ℕ → (Fin 4 → ℝ) → ℝ} :
    ∀ (w : List (Fin 4)) (k : ℕ) {u : (Fin 4 → ℝ) → ℝ},
      ConvHk (euclBall c r) (k + w.length) φ u →
      ∃ g, ConvHk (euclBall c r) k (fun m => pdw (φ m) w) g
  | [], k, u, h => ⟨u, by simpa using h⟩
  | i :: w, k, u, h => by
    obtain ⟨g, hg⟩ := exists_convHk_pdw w (k + 1) (u := u) (by
      simpa [Nat.add_assoc, Nat.add_comm 1] using h)
    obtain ⟨g', hg'⟩ := hg.2 i
    exact ⟨g', by simpa using hg'⟩

theorem fderiv_eq_sum_pd {f : (Fin 4 → ℝ) → ℝ} (x : Fin 4 → ℝ) :
    fderiv ℝ f x = ∑ i, pd f i x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i := by
  ext v
  rw [fderiv_apply_eq_sum_pd]
  simp [mul_comm]

/-- **Functions in every `H^k(B)` are smooth on the open ball.** -/
theorem exists_smooth_rep (hr : 0 < r) {u : (Fin 4 → ℝ) → ℝ}
    (hu : ∀ k, MemHk (euclBall c r) k u) :
    ∃ f : (Fin 4 → ℝ) → ℝ, ContDiffOn ℝ ∞ f (euclBall c r) ∧
      f =ᵐ[volume.restrict (euclBall c r)] u ∧
      ∀ i, HasWeakPartialR (euclBall c r) i u (pd f i) := by
  haveI : Fact (0 < r) := ⟨hr⟩
  set B := euclBall c r
  have hBo : IsOpen B := isOpen_euclBall c r
  set φ : ℕ → (Fin 4 → ℝ) → ℝ := fun m => smoothApprox c r m u
  have hφ : ∀ m, ContDiff ℝ ∞ (φ m) := fun m => contDiff_smoothApprox c r (hu 0) m
  have hconv : ∀ k, ConvHk B k φ u := fun k => convHk_smoothApprox c r k (hu k)
  -- every derivative converges uniformly on the ball
  have hunif : ∀ w : List (Fin 4), UniformCauchySeqOn (fun m => pdw (φ m) w) atTop B := by
    intro w
    obtain ⟨g, hg⟩ := exists_convHk_pdw c r w 3 (hconv (3 + w.length))
    exact uniformCauchySeqOn_of_convHk3 c r hr (fun m => contDiff_pdw (hφ m) w) hg
  have hlim : ∀ w : List (Fin 4), ∀ x ∈ B, ∃ y, Tendsto (fun m => pdw (φ m) w x) atTop (𝓝 y) :=
    fun w x hx => cauchySeq_tendsto_of_complete ((hunif w).cauchySeq hx)
  choose H hH using hlim
  set G : List (Fin 4) → (Fin 4 → ℝ) → ℝ := fun w x => if hx : x ∈ B then H w x hx else 0
  have hGt : ∀ w, ∀ x ∈ B, Tendsto (fun m => pdw (φ m) w x) atTop (𝓝 (G w x)) := by
    intro w x hx; simp only [G, dif_pos hx]; exact hH w x hx
  have hGu : ∀ w, TendstoUniformlyOn (fun m => pdw (φ m) w) (G w) atTop B :=
    fun w => (hunif w).tendstoUniformlyOn_of_tendsto (hGt w)
  -- derivatives of the limits
  have hderiv : ∀ w, ∀ x ∈ B, HasFDerivAt (G w) (∑ i, G (i :: w) x •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) x := by
    intro w x hx
    refine hasFDerivAt_of_tendstoUniformlyOn (f := fun m => pdw (φ m) w)
      (f' := fun m y => ∑ i, pdw (φ m) (i :: w) y •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i)
      (g' := fun y => ∑ i, G (i :: w) y •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) hBo ?_ ?_ (hGt w) hx
    · -- uniform convergence of the derivatives
      have hsum : TendstoUniformlyOn (fun m y => ∑ i, pdw (φ m) (i :: w) y •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i)
          (fun y => ∑ i, G (i :: w) y • ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin 4 => ℝ) i) atTop B := by
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        have hεi : ∀ i : Fin 4, ∀ᶠ m in atTop, ∀ y ∈ B,
            dist (G (i :: w) y) (pdw (φ m) (i :: w) y) < ε / 5 := fun i =>
          Metric.tendstoUniformlyOn_iff.mp (hGu (i :: w)) (ε / 5) (by positivity)
        filter_upwards [hεi 0, hεi 1, hεi 2, hεi 3] with m h0 h1 h2 h3 y hy
        rw [dist_eq_norm, ← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans_lt ?_
        have hb : ∀ i : Fin 4, ‖G (i :: w) y • ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin 4 => ℝ) i - pdw (φ m) (i :: w) y • ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin 4 => ℝ) i‖ < ε / 5 := by
          intro i
          rw [← sub_smul (G (i :: w) y) (pdw (φ m) (i :: w) y)
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i), norm_smul]
          have hp : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i‖ ≤ 1 :=
            ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
              simp only [ContinuousLinearMap.proj_apply, one_mul]
              exact norm_le_pi_norm v i
          have hd : ‖G (i :: w) y - pdw (φ m) (i :: w) y‖ < ε / 5 := by
            rw [← dist_eq_norm]
            fin_cases i
            · exact h0 y hy
            · exact h1 y hy
            · exact h2 y hy
            · exact h3 y hy
          calc ‖G (i :: w) y - pdw (φ m) (i :: w) y‖ *
                ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i‖
              ≤ ‖G (i :: w) y - pdw (φ m) (i :: w) y‖ * 1 := by gcongr
            _ < ε / 5 := by rw [mul_one]; exact hd
        calc ∑ i, _ < ∑ _i : Fin 4, ε / 5 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
              fun i _ => hb i
          _ < ε := by simp; linarith
      exact hsum
    · intro m y _
      have := ((contDiff_pdw (hφ m) w).differentiable (by simp) y).hasFDerivAt
      convert this using 1
      rw [fderiv_eq_sum_pd]
      rfl
  have hpdG : ∀ w i, ∀ x ∈ B, pd (G w) i x = G (i :: w) x := by
    intro w i x hx
    unfold pd
    rw [(hderiv w x hx).fderiv]
    simp [Finset.sum_apply, Pi.single_apply]
  -- smoothness by induction on the order
  have hsmooth : ∀ n : ℕ, ∀ w, ContDiffOn ℝ n (G w) B := by
    intro n
    induction n with
    | zero => intro w; exact contDiffOn_zero.mpr fun x hx => (hderiv w x hx).continuousAt.continuousWithinAt
    | succ n ih =>
      intro w
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by norm_cast,
        contDiffOn_succ_iff_fderiv_of_isOpen hBo]
      refine ⟨fun x hx => (hderiv w x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      have hcongr : ∀ x ∈ B, fderiv ℝ (G w) x = ∑ i, G (i :: w) x •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i :=
        fun x hx => (hderiv w x hx).fderiv
      refine ContDiffOn.congr ?_ hcongr
      exact ContDiffOn.sum fun i _ => (ih (i :: w)).smul contDiffOn_const
  refine ⟨G [], contDiffOn_infty.mpr fun n => hsmooth n [], ?_, fun i => ?_⟩
  · -- the limit is `u`
    have h2 : Tendsto (fun m => eLpNorm (φ m - u) 2 (volume.restrict B)) atTop (𝓝 0) :=
      (hconv 0).2
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun m => (hφ m).continuous.aestronglyMeasurable) (hconv 0).1.aestronglyMeasurable
      h2).exists_seq_tendsto_ae
    rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]
    filter_upwards [(ae_restrict_iff' (measurableSet_euclBall c r)).mp hae] with x hx hxB
    exact tendsto_nhds_unique ((hGt [] x hxB).comp hns.tendsto_atTop) (hx hxB)
  · -- the weak derivative
    obtain ⟨g, hg⟩ := (hconv 1).2 i
    have hb := hg
    have hw := hasWeakPartialR_of_conv (isBounded_euclBall' c r) (measurableSet_euclBall c r)
      hφ (hconv 1).1.1 hb.1 (hconv 1).1.2 hb.2
    -- `g = pd (G []) i` a.e. on the ball
    have he : g =ᵐ[volume.restrict B] pd (G []) i := by
      obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
        (fun m => (continuous_pd ((hφ m).of_le (by simp)) i).aestronglyMeasurable)
        hb.1.aestronglyMeasurable hb.2).exists_seq_tendsto_ae
      rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]
      filter_upwards [(ae_restrict_iff' (measurableSet_euclBall c r)).mp hae] with x hx hxB
      rw [hpdG [] i x hxB]
      exact tendsto_nhds_unique (hx hxB) ((hGt [i] x hxB).comp hns.tendsto_atTop)
    exact hw.congr_ae' EventuallyEq.rfl he

end RenewalGeometry.BallAnalysis.SmoothRep
