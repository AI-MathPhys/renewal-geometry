/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevDensity
import RenewalGeometry.Analysis.BallLinearizedCoulomb

/-!
# `H^{s+2}` regularity of the linearised Coulomb operator with smooth tangential coefficients
  (stage C4b/C5b of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

The weak linearised Coulomb problem of `BallLinearizedCoulomb.linearized_neumann_ball`,
`Σ_{k,ν} ⟨∂_νξ_k + Σ_l a_ν^{kl} ξ_l, ∂_νη_k⟩ = ℓ(η)`, is the weak form of
`d^*(dξ + [a, ξ]) = f` with the natural boundary condition `(dξ + [a, ξ])·ν = 0`.  When the
coefficients are smooth and **tangential** (`Σ_ν (x_ν - c_ν) a_ν^{kl}(x) = 0` on the sphere, as for
a connection in the tangential gauge `x·a = 0`), the coupling integrates by parts without boundary
term (`tangential_ibp_H1B`), so each component solves a Neumann problem
`Δξ_k = f_k - Σ_l ∂_ν(a_ν^{kl} ξ_l)` (`linearized_component_eq_sol`), and the `H^{k+2}` regularity
of the Neumann problem bootstraps:

* `linearized_neumann_Hk`: for `f_k ∈ H^s(B)` every component of the weak solution lies in
  `H^{s+2}(B)`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

section IBP

variable (c : Fin 4 → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- A field `a` is tangential on the sphere `|x - c| = r`. -/
def IsTangentialOn (a : Fin 4 → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ x, sqDist c x = r ^ 2 → ∑ ν, (x ν - c ν) * a ν x = 0

/-- **Integration by parts against a tangential field** (`C¹` functions, no boundary term):
`Σ_ν ∫_B a_ν u ∂_νv = -∫_B (Σ_ν ∂_ν(a_ν u)) v`. -/
theorem integral_tangential_ibp_C1 {a : Fin 4 → (Fin 4 → ℝ) → ℝ}
    (ha : ∀ ν, ContDiff ℝ ∞ (a ν)) (htan : IsTangentialOn c r a) {u v : (Fin 4 → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    ∑ ν, ∫ x in euclBall c r, a ν x * u x * pd v ν x =
      -∫ x in euclBall c r, (∑ ν, (pd (a ν) ν x * u x + a ν x * pd u ν x)) * v x := by
  have hr0 := hr.out
  have ha1 : ∀ ν, ContDiff ℝ 1 (a ν) := fun ν => (ha ν).of_le (by simp)
  have hau : ∀ ν, ContDiff ℝ 1 (fun x => a ν x * u x) := fun ν => (ha1 ν).mul hu
  have h := fun ν => integral_mul_pd_ball c hr0 (hau ν) hv ν
  have hpd : ∀ ν x, pd (fun x => a ν x * u x) ν x = pd (a ν) ν x * u x + a ν x * pd u ν x :=
    fun ν x => pd_mul (ha1 ν) hu ν x
  simp only [hpd] at h
  -- the boundary terms vanish
  have hbd : ∑ ν, r ^ (4 - 1) * ∫ w, a ν (c + r • w) * u (c + r • w) * v (c + r • w) * w ν
      ∂(sphereMeasure 4) = 0 := by
    rw [← Finset.mul_sum]
    have hint : ∀ ν, Integrable (fun w => a ν (c + r • w) * u (c + r • w) * v (c + r • w) * w ν)
        (sphereMeasure 4) := fun ν =>
      integrable_sphereMeasure (by
        have h1 := (ha1 ν).continuous; have h2 := hu.continuous; have h3 := hv.continuous
        fun_prop)
    rw [← integral_finset_sum _ fun ν _ => hint ν]
    have h0 : ∫ w, ∑ ν, a ν (c + r • w) * u (c + r • w) * v (c + r • w) * w ν
        ∂(sphereMeasure 4) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_sphereMeasure 4] with w hw
      have hs : sqDist c (c + r • w) = r ^ 2 := by
        simp only [sqDist, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
        simp only [mul_pow, ← Finset.mul_sum, hw, mul_one]
      have ht := htan (c + r • w) hs
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left] at ht
      have : ∑ ν, a ν (c + r • w) * u (c + r • w) * v (c + r • w) * w ν =
          (u (c + r • w) * v (c + r • w) / r) * ∑ ν, r * w ν * a ν (c + r • w) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        field_simp
      rw [this, ht, mul_zero]
      rfl
    rw [h0, mul_zero]
  have hint2 : ∀ ν, IntegrableOn (fun x => (pd (a ν) ν x * u x + a ν x * pd u ν x) * v x)
      (euclBall c r) := fun ν =>
    integrableOn_euclBall hr0.le ((((continuous_pd (ha1 ν) ν).mul hu.continuous).add
      ((ha1 ν).continuous.mul (continuous_pd hu ν))).mul hv.continuous)
  calc ∑ ν, ∫ x in euclBall c r, a ν x * u x * pd v ν x
      = ∑ ν, (r ^ (4 - 1) * ∫ w, a ν (c + r • w) * u (c + r • w) * v (c + r • w) * w ν
          ∂(sphereMeasure 4) - ∫ x in euclBall c r,
            (pd (a ν) ν x * u x + a ν x * pd u ν x) * v x) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [← h ν]
    _ = -∫ x in euclBall c r, (∑ ν, (pd (a ν) ν x * u x + a ν x * pd u ν x)) * v x := by
        rw [Finset.sum_sub_distrib, hbd, zero_sub]
        simp only [Finset.sum_mul]
        rw [integral_finset_sum _ fun ν _ => hint2 ν]

/-- A uniform bound of a continuous function on the ball. -/
def supB (g : (Fin 4 → ℝ) → ℝ) (hg : Continuous g) : ℝ :=
  (exists_abs_le_on_bounded (Ω := euclBall c r) hg (isBounded_euclBall' c r)).choose

theorem supB_spec (g : (Fin 4 → ℝ) → ℝ) (hg : Continuous g) :
    ∀ x ∈ euclBall c r, |g x| ≤ supB c r g hg :=
  (exists_abs_le_on_bounded (Ω := euclBall c r) hg (isBounded_euclBall' c r)).choose_spec.2

/-- Multiplication by a smooth function on `L²(B)`. -/
def mulS (g : (Fin 4 → ℝ) → ℝ) (hg : ContDiff ℝ ∞ g) : L2B c r →L[ℝ] L2B c r :=
  mulOp c r hg.continuous (supB_spec c r g hg.continuous)

theorem coeFn_mulS (g : (Fin 4 → ℝ) → ℝ) (hg : ContDiff ℝ ∞ g) (f : L2B c r) :
    (mulS c r g hg f : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)] fun x => g x * f x :=
  coeFn_mulOp c r _ _ f

/-- The divergence `Σ_ν ∂_ν(a_ν w)` of `a w` for `w ∈ H¹(B)`, as a continuous linear map. -/
def divTan {a : Fin 4 → (Fin 4 → ℝ) → ℝ} (ha : ∀ ν, ContDiff ℝ ∞ (a ν)) :
    H1Amb c r →L[ℝ] L2B c r :=
  ∑ ν, ((mulS c r (pd (a ν) ν) (contDiff_pd (ha ν) ν)).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin 4) => L2B c r) none) +
    (mulS c r (a ν) (ha ν)).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin 4) => L2B c r) (some ν)))

theorem divTan_apply {a : Fin 4 → (Fin 4 → ℝ) → ℝ} (ha : ∀ ν, ContDiff ℝ ∞ (a ν))
    (w : H1Amb c r) :
    divTan c r ha w = ∑ ν, (mulS c r (pd (a ν) ν) (contDiff_pd (ha ν) ν) (w none) +
      mulS c r (a ν) (ha ν) (w (some ν))) := by
  simp [divTan, ContinuousLinearMap.sum_apply]

/-- **Integration by parts against a tangential smooth field on `H¹(B)`**:
`Σ_ν ⟨a_ν x₀, y_ν⟩ = -⟨Σ_ν ∂_ν(a_ν x₀), y₀⟩` for `x, y ∈ H¹(B)`. -/
theorem tangential_ibp_H1B {a : Fin 4 → (Fin 4 → ℝ) → ℝ} (ha : ∀ ν, ContDiff ℝ ∞ (a ν))
    (htan : IsTangentialOn c r a) :
    ∀ x ∈ H1B c r, ∀ y ∈ H1B c r,
      ∑ ν, ⟪mulS c r (a ν) (ha ν) (x none), y (some ν)⟫ = -⟪divTan c r ha x, y none⟫ := by
  have hr0 := hr.out
  have hp := fun k => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin 4) => L2B c r) k).continuous
  -- for graphs
  have hgraph : ∀ u v : C1fun (n := 4), ∑ ν, ⟪mulS c r (a ν) (ha ν) (graphC1 c r u none),
      graphC1 c r v (some ν)⟫ = -⟪divTan c r ha (graphC1 c r u), graphC1 c r v none⟫ := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    replace hu : ContDiff ℝ 1 u := hu
    replace hv : ContDiff ℝ 1 v := hv
    rw [divTan_apply]
    simp only [graphC1_some, graphC1_none]
    have e1 : ∀ ν, ⟪mulS c r (a ν) (ha ν) ((memLp_ball_of_C1 c r hu).toLp u),
        (memLp_ball_pd_of_C1 c r hv ν).toLp (pd v ν)⟫ =
          ∫ x in euclBall c r, a ν x * u x * pd v ν x := by
      intro ν
      rw [real_inner_comm, inner_toLp_left]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_mulS c r (a ν) (ha ν) ((memLp_ball_of_C1 c r hu).toLp u),
        (memLp_ball_of_C1 c r hu).coeFn_toLp] with x h1 h2
      rw [h1, h2]; ring
    simp only [e1, sum_inner]
    rw [integral_tangential_ibp_C1 c r ha htan hu hv, neg_inj]
    have e2 : ∀ ν, ⟪mulS c r (pd (a ν) ν) (contDiff_pd (ha ν) ν) ((memLp_ball_of_C1 c r hu).toLp u) +
        mulS c r (a ν) (ha ν) ((memLp_ball_pd_of_C1 c r hu ν).toLp (pd u ν)),
        (memLp_ball_of_C1 c r hv).toLp v⟫ =
          ∫ x in euclBall c r, (pd (a ν) ν x * u x + a ν x * pd u ν x) * v x := by
      intro ν
      rw [real_inner_comm, inner_toLp_left]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add (mulS c r (pd (a ν) ν) (contDiff_pd (ha ν) ν)
          ((memLp_ball_of_C1 c r hu).toLp u))
          (mulS c r (a ν) (ha ν) ((memLp_ball_pd_of_C1 c r hu ν).toLp (pd u ν))),
        coeFn_mulS c r (pd (a ν) ν) (contDiff_pd (ha ν) ν) ((memLp_ball_of_C1 c r hu).toLp u),
        coeFn_mulS c r (a ν) (ha ν) ((memLp_ball_pd_of_C1 c r hu ν).toLp (pd u ν)),
        (memLp_ball_of_C1 c r hu).coeFn_toLp, (memLp_ball_pd_of_C1 c r hu ν).coeFn_toLp]
        with x h1 h2 h3 h4 h5
      rw [h1, Pi.add_apply, h2, h3, h4, h5]; ring
    rw [Finset.sum_congr rfl fun ν _ => e2 ν]
    have hint : ∀ ν, IntegrableOn (fun x => (pd (a ν) ν x * u x + a ν x * pd u ν x) * v x)
        (euclBall c r) := fun ν => by
      have ha1 : ContDiff ℝ 1 (a ν) := (ha ν).of_le (by simp)
      exact integrableOn_euclBall hr0.le
        ((((continuous_pd ha1 ν).mul hu.continuous).add
          (ha1.continuous.mul (continuous_pd hu ν))).mul hv.continuous)
    rw [← integral_finset_sum (f := fun ν x => (pd (a ν) ν x * u x + a ν x * pd u ν x) * v x) _
      fun ν _ => hint ν]
    congr 1; funext x; rw [Finset.sum_mul]
  intro x hx
  -- first extend in `x` for graph `y`
  have hx' : ∀ v : C1fun (n := 4), ∑ ν, ⟪mulS c r (a ν) (ha ν) (x none), graphC1 c r v (some ν)⟫ =
      -⟪divTan c r ha x, graphC1 c r v none⟫ := by
    intro v
    refine H1B_induction c r (P := fun x => ∑ ν, ⟪mulS c r (a ν) (ha ν) (x none),
      graphC1 c r v (some ν)⟫ = -⟪divTan c r ha x, graphC1 c r v none⟫) ?_ (fun u => hgraph u v) x hx
    exact isClosed_eq (continuous_finset_sum _ fun ν _ =>
      ((mulS c r (a ν) (ha ν)).continuous.comp (hp none)).inner continuous_const)
      ((divTan c r ha).continuous.inner continuous_const).neg
  intro y hy
  refine H1B_induction c r (P := fun y => ∑ ν, ⟪mulS c r (a ν) (ha ν) (x none), y (some ν)⟫ =
    -⟪divTan c r ha x, y none⟫) ?_ hx' y hy
  exact isClosed_eq (continuous_finset_sum _ fun ν _ => continuous_const.inner (hp (some ν)))
    (continuous_const.inner (hp none)).neg

end IBP

/-! ### The linearised problem as Neumann problems and the bootstrap -/

section LinReg

variable (c : Fin 4 → ℝ) (r : ℝ) [hr : Fact (0 < r)] (N : ℕ)

theorem mulCLM_sob_eq {g : (Fin 4 → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg4 : MemLp g 4 (volume.restrict (euclBall c r))) (x : H1B0 c r) :
    mulCLM c r hg4 (sobCLM c r x) = mulS c r g hg ((x : H1Amb c r) none) := by
  refine Lp.ext ?_
  have h1 : (mulCLM c r hg4 (sobCLM c r x) : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      fun y => g y * (sobCLM c r x : (Fin 4 → ℝ) → ℝ) y :=
    ((Lp.memLp (sobCLM c r x)).mul' hg4).coeFn_toLp
  have h2 : (sobCLM c r x : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      (((x : H1Amb c r) none : L2B c r) : (Fin 4 → ℝ) → ℝ) := (memLp_four_H1B c r x).coeFn_toLp
  filter_upwards [h1, h2, coeFn_mulS c r g hg ((x : H1Amb c r) none)] with y e1 e2 e3
  rw [e1, e2, e3]

/-- The test field with a single non-zero component. -/
def singleXi (k : Fin N) (y : H1B0 c r) : XiB c r N := WithLp.toLp 2 (Pi.single k y)

theorem singleXi_apply (k k' : Fin N) (y : H1B0 c r) :
    singleXi c r N k y k' = if k' = k then y else 0 := by
  simp [singleXi, Pi.single_apply]

/-- **Each component of a weak solution of the linearised problem is a Neumann solution** with data
`f_k - Σ_l Σ_ν ∂_ν(a_ν^{kl} ξ_l)` (smooth tangential coefficients). -/
theorem linearized_component_eq_sol {a : Fin 4 → Fin N → Fin N → (Fin 4 → ℝ) → ℝ}
    (has : ∀ ν k l, ContDiff ℝ ∞ (a ν k l))
    (ha4 : ∀ ν k l, MemLp (a ν k l) 4 (volume.restrict (euclBall c r)))
    (htan : ∀ k l, IsTangentialOn c r (fun ν => a ν k l)) {f : Fin N → L2B c r}
    {ξ : XiB c r N}
    (hξ : ∀ η : XiB c r N, dirFormN c r N ξ η + couplingN c r N ha4 ξ η =
      -∑ k, ⟪f k, ((η k : H1B0 c r) : H1Amb c r) none⟫) (k : Fin N) :
    ξ k = solCLM c r (f k - ∑ l, divTan c r (fun ν => has ν k l) ((ξ l : H1B0 c r) : H1Amb c r)) := by
  refine neumann_H1B0_unique c r (F := f k - ∑ l, divTan c r (fun ν => has ν k l)
    ((ξ l : H1B0 c r) : H1Amb c r)) (fun y => ?_) (solCLM_spec c r _)
  have h := hξ (singleXi c r N k y)
  rw [dirFormN_apply, couplingN_apply] at h
  have hs : ∀ k', singleXi c r N k y k' = if k' = k then y else 0 := fun k' =>
    singleXi_apply c r N k k' y
  simp only [hs] at h
  -- simplify the sums over the test components
  have e1 : ∑ k', dirForm c r (ξ k') (if k' = k then y else 0) = dirForm c r (ξ k) y := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have e2 : ∀ ν l, ∑ k', ⟪mulCLM c r (ha4 ν k' l) (sobCLM c r (ξ l)),
      derivL c r ν (if k' = k then y else 0)⟫ =
        ⟪mulCLM c r (ha4 ν k l) (sobCLM c r (ξ l)), derivL c r ν y⟫ := by
    intro ν l
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have e3 : ∑ k', ⟪f k', (((if k' = k then y else 0 : H1B0 c r)) : H1Amb c r) none⟫ =
      ⟪f k, ((y : H1B0 c r) : H1Amb c r) none⟫ := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [e1] at h
  rw [e3] at h
  have e4 : ∑ ν, ∑ k', ∑ l, ⟪mulCLM c r (ha4 ν k' l) (sobCLM c r (ξ l)),
      derivL c r ν (if k' = k then y else 0)⟫ =
        ∑ l, ∑ ν, ⟪mulS c r (a ν k l) (has ν k l) (((ξ l : H1B0 c r) : H1Amb c r) none),
          ((y : H1B0 c r) : H1Amb c r) (some ν)⟫ := by
    have hν : ∀ ν, ∑ k', ∑ l, ⟪mulCLM c r (ha4 ν k' l) (sobCLM c r (ξ l)),
        derivL c r ν (if k' = k then y else 0)⟫ =
          ∑ l, ⟪mulS c r (a ν k l) (has ν k l) (((ξ l : H1B0 c r) : H1Amb c r) none),
            ((y : H1B0 c r) : H1Amb c r) (some ν)⟫ := by
      intro ν
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_eq_single k]
      · simp only [if_true]
        rw [mulCLM_sob_eq c r (has ν k l) (ha4 ν k l)]
        rfl
      · intro b _ hb; simp [hb]
      · simp
    rw [Finset.sum_congr rfl fun ν _ => hν ν, Finset.sum_comm]
  rw [e4] at h
  have e5 : ∀ l, ∑ ν, ⟪mulS c r (a ν k l) (has ν k l) (((ξ l : H1B0 c r) : H1Amb c r) none),
      ((y : H1B0 c r) : H1Amb c r) (some ν)⟫ = -⟪divTan c r (fun ν => has ν k l)
        ((ξ l : H1B0 c r) : H1Amb c r), ((y : H1B0 c r) : H1Amb c r) none⟫ := fun l =>
    tangential_ibp_H1B c r (fun ν => has ν k l) (htan k l) _ (ξ l).2.1 _ y.2.1
  simp only [e5] at h
  rw [loadCLM_apply, inner_sub_left, sum_inner]
  simp only [Finset.sum_neg_distrib] at h
  linarith

/-- **`H^{s+2}` regularity of the linearised Coulomb problem with smooth tangential coefficients**:
if `f_k ∈ H^s(B)` and `ξ` is a weak solution of
`Σ_{k,ν} ⟨∂_νξ_k + Σ_l a_ν^{kl} ξ_l, ∂_νη_k⟩ = -Σ_k ⟨f_k, η_k⟩` for all mean-zero test fields, with
smooth coefficients tangential on the sphere, then every `ξ_k ∈ H^{s+2}(B)`. -/
theorem linearized_neumann_Hk (s : ℕ) {a : Fin 4 → Fin N → Fin N → (Fin 4 → ℝ) → ℝ}
    (has : ∀ ν k l, ContDiff ℝ ∞ (a ν k l))
    (ha4 : ∀ ν k l, MemLp (a ν k l) 4 (volume.restrict (euclBall c r)))
    (htan : ∀ k l, IsTangentialOn c r (fun ν => a ν k l)) {f : Fin N → L2B c r}
    (hf : ∀ k, MemHk (euclBall c r) s (f k : (Fin 4 → ℝ) → ℝ)) {ξ : XiB c r N}
    (hξ : ∀ η : XiB c r N, dirFormN c r N ξ η + couplingN c r N ha4 ξ η =
      -∑ k, ⟪f k, ((η k : H1B0 c r) : H1Amb c r) none⟫) :
    ∀ k, MemHk (euclBall c r) (s + 2)
      ((((ξ k : H1B0 c r) : H1Amb c r) none : L2B c r) : (Fin 4 → ℝ) → ℝ) := by
  have hB := isBounded_euclBall' c r
  have hBm := measurableSet_euclBall c r
  have hBo := isOpen_euclBall c r
  set u : Fin N → (Fin 4 → ℝ) → ℝ := fun k =>
    ((((ξ k : H1B0 c r) : H1Amb c r) none : L2B c r) : (Fin 4 → ℝ) → ℝ)
  have hweak : ∀ k ν, HasWeakPartialR (euclBall c r) ν (u k)
      ((((ξ k : H1B0 c r) : H1Amb c r) (some ν) : L2B c r) : (Fin 4 → ℝ) → ℝ) := fun k ν =>
    hasWeakPartialR_of_H1B c r (ξ k).2.1 ν
  -- the data of the component equations
  have hdiv : ∀ m, (∀ l, MemHk (euclBall c r) (m + 1) (u l)) → ∀ k l,
      MemHk (euclBall c r) m (divTan c r (fun ν => has ν k l)
        ((ξ l : H1B0 c r) : H1Amb c r) : (Fin 4 → ℝ) → ℝ) := by
    intro m hu k l
    rw [divTan_apply]
    have hterm : ∀ ν, MemHk (euclBall c r) m
        ((mulS c r (pd (a ν k l) ν) (contDiff_pd (has ν k l) ν) (((ξ l : H1B0 c r) : H1Amb c r) none) +
          mulS c r (a ν k l) (has ν k l) (((ξ l : H1B0 c r) : H1Amb c r) (some ν)) : L2B c r) :
            (Fin 4 → ℝ) → ℝ) := by
      intro ν
      have h1 := ((hu l).mono (Nat.le_succ m)).mul_smooth hB hBm (contDiff_pd (has ν k l) ν)
      have h2 := ((hu l).deriv hBo (hweak l ν) (Lp.memLp _)).mul_smooth hB hBm (has ν k l)
      refine (h1.add h2).congr_ae ?_
      filter_upwards [Lp.coeFn_add (mulS c r (pd (a ν k l) ν) (contDiff_pd (has ν k l) ν)
          (((ξ l : H1B0 c r) : H1Amb c r) none))
          (mulS c r (a ν k l) (has ν k l) (((ξ l : H1B0 c r) : H1Amb c r) (some ν))),
        coeFn_mulS c r (pd (a ν k l) ν) (contDiff_pd (has ν k l) ν)
          (((ξ l : H1B0 c r) : H1Amb c r) none),
        coeFn_mulS c r (a ν k l) (has ν k l) (((ξ l : H1B0 c r) : H1Amb c r) (some ν))]
        with x e1 e2 e3
      rw [e1, Pi.add_apply, e2, e3]
    refine (MemHk.sum' Finset.univ fun ν _ => hterm ν).congr_ae ?_
    filter_upwards [coeFn_finset_sum c r Finset.univ fun ν =>
      (mulS c r (pd (a ν k l) ν) (contDiff_pd (has ν k l) ν) (((ξ l : H1B0 c r) : H1Amb c r) none) +
        mulS c r (a ν k l) (has ν k l) (((ξ l : H1B0 c r) : H1Amb c r) (some ν)))] with x hx
    rw [hx]
  have hstep : ∀ m, m ≤ s → (∀ l, MemHk (euclBall c r) (m + 1) (u l)) →
      ∀ k, MemHk (euclBall c r) (m + 2) (u k) := by
    intro m hm hu k
    set F := f k - ∑ l, divTan c r (fun ν => has ν k l) ((ξ l : H1B0 c r) : H1Amb c r)
    have hF : MemHk (euclBall c r) m (F : (Fin 4 → ℝ) → ℝ) := by
      have h1 := (hf k).mono hm
      have h2 := MemHk.sum' Finset.univ fun l _ => hdiv m hu k l
      refine (h1.sub h2).congr_ae ?_
      filter_upwards [Lp.coeFn_sub (f k) (∑ l, divTan c r (fun ν => has ν k l)
          ((ξ l : H1B0 c r) : H1Amb c r)),
        coeFn_finset_sum c r Finset.univ fun l => divTan c r (fun ν => has ν k l)
          ((ξ l : H1B0 c r) : H1Amb c r)] with x e1 e2
      rw [e1, Pi.sub_apply, e2]
    have hsol := neumann_Hk_weak c r m hF
    have heq := linearized_component_eq_sol c r N has ha4 htan hξ k
    have : u k = solFn c r F := by
      simp only [u, solFn]; rw [heq]
    rw [this]; exact hsol
  -- the bootstrap
  have hall : ∀ m, m ≤ s → ∀ k, MemHk (euclBall c r) (m + 2) (u k) := by
    intro m
    induction m with
    | zero =>
      intro _ k
      refine hstep 0 (Nat.zero_le s) (fun l => ⟨Lp.memLp _, fun ν => ⟨_, hweak l ν, Lp.memLp _⟩⟩) k
    | succ m ih =>
      intro hm k
      exact hstep (m + 1) hm (fun l => ih (by omega) l) k
  exact hall s le_rfl

end LinReg

end RenewalGeometry.BallAnalysis.BallReg
