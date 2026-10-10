/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallPathContinuity
import RenewalGeometry.Analysis.BallCoulombAprioriWeak
import RenewalGeometry.Analysis.BallTangentialApprox

/-!
# Coulomb gauge states on a ball: the weak a-priori estimate for Sobolev Coulomb connections
  (stage D2/D3 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `gaugeAct_zero`, `coulF_zero` — at `ξ = 0` the Coulomb functional is the divergence of the
  coefficients: `coulF L (a, 0) = (Σ_μ ∂_μ a_μ^b)_b`;
* `star_embX_of_skew`, `exp_embX_mul_star` — for a basis of skew-Hermitian matrices the gauges
  `e^X`, `X = Σ ξ^b e_b`, are unitary: `e^X (e^X)^* = 1`;
* `isWeakBallCoulomb_embX` (**main result**) — a tangential, Coulomb `𝔤`-valued connection with
  `H⁴(B)` coefficients has `IsWeakBallCoulomb` matrix entries (smooth tangential approximation
  `exists_tangential_approx`), so the critical a-priori estimate `coulomb_apriori_weak` applies
  to it.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg WeakCoulomb TanApprox

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m d : ℕ}

/-! ### The Coulomb functional at the identity gauge -/

theorem embX_zero' {s : ℕ} [Fact (3 ≤ s)] (L : LieBasis m d) :
    embX (c := c) (r := r) (s := s) L 0 = 0 := by
  have := map_zero (embXL (c := c) (r := r) (s := s) (m := m) L)
  simpa [embXL_apply] using this

theorem gaugeAct_zero (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) (μ : Fin 4) :
    gaugeAct L a 0 μ = embX L (a μ) := by
  simp only [gaugeAct, embX_zero', neg_zero, exp_zero, rhoML_eq, map_one, derM_one, one_mul,
    mul_one, zero_mul, sub_zero]

/-- **At the identity gauge, the Coulomb functional is the divergence of the coefficients.** -/
theorem coulF_zero (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) :
    coulF L (a, 0) = fun b => ∑ μ, derS μ (a μ b) := by
  unfold coulF
  simp only [gaugeAct_zero, derM_embX]
  rw [embX_sum', coordL_embX]
  funext b
  simp [Finset.sum_apply]

/-! ### Unitarity of the exponential gauges -/

theorem star_embX_of_skew {s : ℕ} [Fact (3 ≤ s)] (L : LieBasis m d)
    (hskew : ∀ b, star (L.e b) = -L.e b) (u : Fin d → SobAlg c r s) :
    star (embX L u) = -embX L u := by
  have hre : ∀ b i j, (L.e b j i).re = -(L.e b i j).re := fun b i j => by
    have := congrFun (congrFun (hskew b) i) j
    simp only [Matrix.star_apply, Matrix.neg_apply] at this
    have h2 := congrArg Complex.re this
    simpa using h2
  have him : ∀ b i j, (L.e b j i).im = (L.e b i j).im := fun b i j => by
    have := congrFun (congrFun (hskew b) i) j
    simp only [Matrix.star_apply, Matrix.neg_apply] at this
    have h2 := congrArg Complex.im this
    simp at h2
    linarith
  refine Matrix.ext fun i j => ?_
  rw [Matrix.star_apply, Matrix.neg_apply, embX_apply, embX_apply]
  ext
  · simp only [Cx.star_re', Cx.neg_re]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [hre, neg_smul]
  · simp only [Cx.star_im', Cx.neg_im]
    congr 1
    exact Finset.sum_congr rfl fun b _ => by rw [him]

set_option backward.isDefEq.respectTransparency false in
/-- **Exponential gauges are unitary**: `e^X (e^X)^* = 1` for `X = Σ ξ^b e_b` with a
skew-Hermitian basis. -/
theorem exp_embX_mul_star {s : ℕ} [Fact (3 ≤ s)] (L : LieBasis m d)
    (hskew : ∀ b, star (L.e b) = -L.e b) (u : Fin d → SobAlg c r s) :
    exp (embX L u) * star (exp (embX L u)) = 1 := by
  have hrad : ∀ z : MatSob c r s m,
      z ∈ EMetric.ball (0 : MatSob c r s m) (expSeries ℝ (MatSob c r s m)).radius := fun z => by
    rw [expSeries_radius_eq_top]; exact edist_lt_top _ _
  rw [star_exp, star_embX_of_skew L hskew, ← exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (Commute.neg_right (Commute.refl _)) (hrad _) (hrad _), add_neg_cancel, exp_zero]

set_option backward.isDefEq.respectTransparency false in
theorem star_exp_embX {s : ℕ} [Fact (3 ≤ s)] (L : LieBasis m d)
    (hskew : ∀ b, star (L.e b) = -L.e b) (u : Fin d → SobAlg c r s) :
    star (exp (embX L u)) = exp (-embX L u) := by
  rw [star_exp, star_embX_of_skew L hskew]


/-! ### The weak Coulomb glue -/

theorem memLp_evC {s : ℕ} [Fact (3 ≤ s)] (z : Cx (SobAlg c r s)) :
    MemLp (evC z) 2 (volume.restrict (euclBall c r)) := by
  have h1 : MemLp (fun x => ((fn z.re x : ℝ) : ℂ)) 2 (volume.restrict (euclBall c r)) :=
    (memLp_fn z.re).ofReal
  have h2 : MemLp (fun x => ((fn z.im x : ℝ) : ℂ) * Complex.I) 2
      (volume.restrict (euclBall c r)) := (memLp_fn z.im).ofReal.mul_const _
  exact h1.add h2

theorem eLpNorm_sum_ofReal_mul_le {μ : Measure (Fin 4 → ℝ)} {ι : Type*} (t : Finset ι)
    (f : ι → (Fin 4 → ℝ) → ℝ) (C : ι → ℂ) (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    eLpNorm (fun x => ∑ i ∈ t, ((f i x : ℝ) : ℂ) * C i) 2 μ ≤
      ∑ i ∈ t, ‖C i‖ₑ * eLpNorm (f i) 2 μ := by
  have e : (fun x => ∑ i ∈ t, ((f i x : ℝ) : ℂ) * C i) =
      ∑ i ∈ t, fun x => C i • ((f i x : ℝ) : ℂ) := by
    funext x; simp [Finset.sum_apply, mul_comm]
  rw [e]
  refine (eLpNorm_sum_le (fun i _ => (Complex.continuous_ofReal.comp_aestronglyMeasurable
    (hf i)).const_smul (C i)) (by norm_num)).trans (Finset.sum_le_sum fun i _ => ?_)
  show eLpNorm (C i • fun x => ((f i x : ℝ) : ℂ)) 2 μ ≤ _
  rw [eLpNorm_const_smul]
  gcongr
  exact le_of_eq (eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp))

theorem pd_sum_ofReal_mul {ι : Type*} (t : Finset ι) {W : ι → (Fin 4 → ℝ) → ℝ}
    (hW : ∀ i, ContDiff ℝ 1 (W i)) (C : ι → ℂ) (μ : Fin 4) (x : Fin 4 → ℝ) :
    pd (fun y => ∑ i ∈ t, ((W i y : ℝ) : ℂ) * C i) μ x = ∑ i ∈ t, ((pd (W i) μ x : ℝ) : ℂ) * C i := by
  have hd : ∀ i, DifferentiableAt ℝ (fun y => ((W i y : ℝ) : ℂ)) x := fun i =>
    (Complex.ofRealCLM.contDiff.comp (hW i)).differentiable one_ne_zero x
  rw [pd_sum_complex (F := fun i y => ((W i y : ℝ) : ℂ) * C i)
    fun i _ => (hd i).mul (differentiableAt_const (C i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_mul_complex (hd i) (differentiableAt_const (C i)), pd_const_complex, pd_ofReal_fun (hW i)]
  ring

/-- The entries of a `𝔤`-valued field, a.e. -/
theorem evM_embX_entry {s : ℕ} [Fact (3 ≤ s)] (L : LieBasis m d) (u : Fin d → SobAlg c r s)
    (i j : Fin m) :
    (fun x => evM (embX L u) x i j) =ᵐ[volume.restrict (euclBall c r)]
      fun x => ∑ b, ((fn (u b) x : ℝ) : ℂ) * L.e b i j := by
  filter_upwards [evM_embX L u] with x hx
  rw [hx]
  simp [Matrix.sum_apply, Matrix.smul_apply]

/-- **Tangential Coulomb `𝔤`-valued connections with `H⁴(B)` coefficients are weak Coulomb
forms**, with the gradients `∂_μ A_ν` given by the derivatives `derM μ`. -/
theorem isWeakBallCoulomb_embX (L : LieBasis m d) {a : Fin 4 → Fin d → SobAlg c r 4}
    (ha : a ∈ TSp (c := c) (r := r) d) (hcoul : coulF L (a, 0) = 0) :
    IsWeakBallCoulomb c r (fun ν i j x => evM (embX L (a ν)) x i j)
      (fun ν i j μ x => evM (derM μ (embX L (a ν))) x i j) := by
  set ρ := volume.restrict (euclBall c r)
  have hcb : ∀ b, ∑ μ, derS μ (a μ b) = 0 := fun b => by
    have := congrFun hcoul b
    rwa [coulF_zero] at this
  -- the smooth tangential approximants of each coefficient field
  have hex : ∀ b, ∃ Wt : ℕ → Fin 4 → (Fin 4 → ℝ) → ℝ, (∀ k ν, ContDiff ℝ ∞ (Wt k ν)) ∧
      (∀ k y, sqDist c y = r ^ 2 → ∑ ν, (y ν - c ν) * Wt k ν y = 0) ∧
      (∀ ν, Tendsto (fun k => eLpNorm (Wt k ν - fn (a ν b)) 2 ρ) atTop (𝓝 0)) ∧
      (∀ ν μ, Tendsto (fun k => eLpNorm (pd (Wt k ν) μ - fn (derS μ (a ν b))) 2 ρ)
        atTop (𝓝 0)) := by
    intro b
    have htan : IsTangentialS (fun μ => a μ b) := mem_tanSub.mp (ha b)
    have htan' : IsWeakTangential c r (fun ν => fn (a ν b))
        (fun x => ∑ ν, fn (derS ν (a ν b)) x) :=
      IsWeakTangential.congr_ae htan (fun ν => EventuallyEq.rfl) (fn_divS _)
    exact exists_tangential_approx c hr.out (fun ν => memHk_fn (a ν b))
      (fun ν μ => weak_derS μ (a ν b)) (fun ν μ => memLp_fn _) htan'
  choose Wt hWs hWt hWL hWD using hex
  have hW1 : ∀ b k ν, ContDiff ℝ 1 (Wt b k ν) := fun b k ν => (hWs b k ν).of_le (by simp)
  refine ⟨fun ν i j => memLp_evC _, fun ν i j μ => memLp_evC _,
    ⟨fun k ν i j x => ∑ b, ((Wt b k ν x : ℝ) : ℂ) * L.e b i j, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k ν i j
    exact ContDiff.sum fun b _ =>
      ((Complex.ofRealCLM.contDiff.comp ((hWs b k ν).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))).mul contDiff_const)
  · intro k y hy i j
    have e : ∀ μ, ((y μ - c μ : ℝ) : ℂ) * ∑ b, ((Wt b k μ y : ℝ) : ℂ) * L.e b i j =
        ∑ b, (((y μ - c μ) * Wt b k μ y : ℝ) : ℂ) * L.e b i j := fun μ => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      push_cast; ring
    simp_rw [e]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hWt b k y hy]
    simp
  · intro ν i j
    have hle : ∀ k, eLpNorm ((fun x => ∑ b, ((Wt b k ν x : ℝ) : ℂ) * L.e b i j) -
        fun x => evM (embX L (a ν)) x i j) 2 ρ ≤
        ∑ b, ‖L.e b i j‖ₑ * eLpNorm (Wt b k ν - fn (a ν b)) 2 ρ := by
      intro k
      have e : ((fun x => ∑ b, ((Wt b k ν x : ℝ) : ℂ) * L.e b i j) -
          fun x => evM (embX L (a ν)) x i j) =ᵐ[ρ]
          fun x => ∑ b, (((Wt b k ν - fn (a ν b)) x : ℝ) : ℂ) * L.e b i j := by
        filter_upwards [evM_embX_entry L (a ν) i j] with x hx
        simp only [Pi.sub_apply, hx, ← Finset.sum_sub_distrib, Complex.ofReal_sub, sub_mul]
      rw [eLpNorm_congr_ae e]
      exact eLpNorm_sum_ofReal_mul_le _ _ _ fun b =>
        (hWs b k ν).continuous.aestronglyMeasurable.sub (memLp_fn _).aestronglyMeasurable
    have hlim : Tendsto (fun k => ∑ b, ‖L.e b i j‖ₑ * eLpNorm (Wt b k ν - fn (a ν b)) 2 ρ)
        atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun b _ =>
        ENNReal.Tendsto.const_mul (hWL b ν) (Or.inr enorm_ne_top) (a := ‖L.e b i j‖ₑ)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hle
  · intro ν i j μ
    have hle : ∀ k, eLpNorm (pd (fun x => ∑ b, ((Wt b k ν x : ℝ) : ℂ) * L.e b i j) μ -
        fun x => evM (derM μ (embX L (a ν))) x i j) 2 ρ ≤
        ∑ b, ‖L.e b i j‖ₑ * eLpNorm (pd (Wt b k ν) μ - fn (derS μ (a ν b))) 2 ρ := by
      intro k
      have e : (pd (fun x => ∑ b, ((Wt b k ν x : ℝ) : ℂ) * L.e b i j) μ -
          fun x => evM (derM μ (embX L (a ν))) x i j) =ᵐ[ρ]
          fun x => ∑ b, (((pd (Wt b k ν) μ - fn (derS μ (a ν b))) x : ℝ) : ℂ) * L.e b i j := by
        rw [derM_embX]
        filter_upwards [evM_embX_entry L (fun b => derS μ (a ν b)) i j] with x hx
        simp only [Pi.sub_apply, hx, pd_sum_ofReal_mul _ (fun b => hW1 b k ν),
          ← Finset.sum_sub_distrib, Complex.ofReal_sub, sub_mul]
      rw [eLpNorm_congr_ae e]
      exact eLpNorm_sum_ofReal_mul_le _ _ _ fun b =>
        (continuous_pd (hW1 b k ν) μ).aestronglyMeasurable.sub (memLp_fn _).aestronglyMeasurable
    have hlim : Tendsto (fun k => ∑ b, ‖L.e b i j‖ₑ *
        eLpNorm (pd (Wt b k ν) μ - fn (derS μ (a ν b))) 2 ρ) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun b _ =>
        ENNReal.Tendsto.const_mul (hWD b ν μ) (Or.inr enorm_ne_top) (a := ‖L.e b i j‖ₑ)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hle
  · intro i j
    have h1 : ∀ μ, (fun x => evM (derM μ (embX L (a μ))) x i j) =ᵐ[ρ]
        fun x => ∑ b, ((fn (derS μ (a μ b)) x : ℝ) : ℂ) * L.e b i j := fun μ => by
      rw [derM_embX]; exact evM_embX_entry L _ i j
    have h2 : ∀ b, (fun x => ∑ μ, fn (derS μ (a μ b)) x) =ᵐ[ρ] fun _ => (0 : ℝ) := fun b => by
      filter_upwards [fn_sum Finset.univ (fun μ => derS μ (a μ b)), fn_zero (c := c) (r := r) (s := 3)]
        with x hx h0
      rw [← hx, hcb b, h0]
    filter_upwards [ae_all_iff.mpr h1, ae_all_iff.mpr h2] with x hx hx2
    simp only [hx]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← Complex.ofReal_sum, hx2, Complex.ofReal_zero, zero_mul,
      Finset.sum_const_zero]

end RenewalGeometry.BallAnalysis.BallAlg
