/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactLegendreHamiltonian

/-!
# The symmetric-square-root triad of the canonical ADM coframe
  (`subsec:supp-exact-action-provenance`, "the canonical ADM coframe"; emergent-spacetime
  manuscript)

The manuscript writes `e = e(γ, N, β)` for "the canonical ADM coframe" but never specifies the
spatial triad `E(γ)` with `EᵀE = γ`.  We fix the **symmetric square root** (a disclosed
rendering): near the flat metric `γ = I`, `E(γ)` is the unique matrix near `I` with `E² = γ`;
for symmetric `γ` it is symmetric, so `EᵀE = E² = γ`.

It is constructed with the analytic implicit function theorem
(`AnalyticImplicit.analytic_implicit_function`) applied to `F(γ, E) = E E - γ` on
`M3 = Fin 3 → Fin 3 → ℝ`, whose partial derivative `∂_E F(I, I) = 2 id` is invertible.

* `sqrtTriad`, `sqrtTriad_one` (`E(I) = I`), `analyticAt_sqrtTriad` (analytic at `I`),
  `sqrtTriad_sq` (`E(γ)² = γ` near `I`), `sqrtTriad_unique` (local uniqueness),
  `sqrtTriad_symm` and `sqrtTriad_transpose_mul` (`E(γ)ᵀE(γ) = γ` for symmetric `γ` near `I`),
  `hasFDerivAt_sqrtTriad` (`DE(I) = ½ id`).
* `hasFDerivAt_of_sq_remainder`: a generic derivative criterion from an exact quadratic
  remainder bound (used again in the jet files).
-/

open Filter Finset
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.QuadJet

open AnalyticImplicit

set_option linter.unusedSectionVars false

/-! ### A derivative criterion -/

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- If `f(x₀ + d) - f(x₀) - L d = Q d` with `‖Q d‖ ≤ K ‖d‖²`, then `L` is the derivative of `f` at
`x₀`. -/
theorem hasFDerivAt_of_sq_remainder {f : E → F} {L : E →L[ℝ] F} {x₀ : E} (K : ℝ)
    (h : ∀ d, ‖f (x₀ + d) - f x₀ - L d‖ ≤ K * ‖d‖ ^ 2) : HasFDerivAt f L x₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun d : E => f (x₀ + d) - f x₀ - L d) =O[𝓝 0] (fun d : E => ‖d‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound K (Eventually.of_forall fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h d
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

end Generic

/-! ### `3 × 3` matrices as plain arrays -/

/-- Real `3 × 3` arrays (sup norm), the type of the triad parameter of
`ExactLegendreHamiltonian`. -/
abbrev M3 := Fin 3 → Fin 3 → ℝ

/-- The identity array. -/
def one3 : M3 := (1 : Matrix (Fin 3) (Fin 3) ℝ)

/-- The matrix product of arrays. -/
def mul3 (E F : M3) : M3 := fun i j => ∑ k, E i k * F k j

/-- The transpose of an array. -/
def tr3 (E : M3) : M3 := fun i j => E j i

theorem one3_apply (i j : Fin 3) : one3 i j = if i = j then 1 else 0 := by
  simp [one3, Matrix.one_apply]

theorem mul3_one3 (E : M3) : mul3 E one3 = E := by
  funext i j; simp [mul3, one3_apply]

theorem one3_mul3 (E : M3) : mul3 one3 E = E := by
  funext i j; simp [mul3, one3_apply]

theorem mul3_add_left (E E' F : M3) : mul3 (E + E') F = mul3 E F + mul3 E' F := by
  funext i j; simp [mul3, add_mul, Finset.sum_add_distrib]

theorem mul3_add_right (E F F' : M3) : mul3 E (F + F') = mul3 E F + mul3 E F' := by
  funext i j; simp [mul3, mul_add, Finset.sum_add_distrib]

theorem mul3_smul_left (c : ℝ) (E F : M3) : mul3 (c • E) F = c • mul3 E F := by
  funext i j; simp [mul3, Finset.mul_sum, mul_assoc]

theorem mul3_smul_right (c : ℝ) (E F : M3) : mul3 E (c • F) = c • mul3 E F := by
  funext i j; simp only [mul3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem tr3_mul3 (E F : M3) : tr3 (mul3 E F) = mul3 (tr3 F) (tr3 E) := by
  funext i j; simp only [tr3, mul3]; exact Finset.sum_congr rfl fun _ _ => by ring

theorem tr3_one3 : tr3 one3 = one3 := by
  funext i j; simp [tr3, one3_apply, eq_comm]

theorem norm_mul3_le (E F : M3) : ‖mul3 E F‖ ≤ 3 * (‖E‖ * ‖F‖) := by
  have hnn : 0 ≤ 3 * (‖E‖ * ‖F‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => (pi_norm_le_iff_of_nonneg hnn).2 fun j => ?_
  have hE : ∀ a b, ‖E a b‖ ≤ ‖E‖ := fun a b => (norm_le_pi_norm (E a) b).trans (norm_le_pi_norm E a)
  have hF : ∀ a b, ‖F a b‖ ≤ ‖F‖ := fun a b => (norm_le_pi_norm (F a) b).trans (norm_le_pi_norm F a)
  calc ‖mul3 E F i j‖ = ‖∑ k, E i k * F k j‖ := rfl
    _ ≤ ∑ k, ‖E i k * F k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 3, ‖E‖ * ‖F‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]; exact mul_le_mul (hE i k) (hF k j) (norm_nonneg _) (norm_nonneg _)
    _ = 3 * (‖E‖ * ‖F‖) := by simp

theorem continuous_tr3 : Continuous tr3 :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply j)

/-! ### The square map -/

/-- `F(γ, E) = E E - γ`. -/
def sqF (p : M3 × M3) : M3 := mul3 p.2 p.2 - p.1

theorem analyticAt_sqF (p : M3 × M3) : AnalyticAt ℝ sqF p := by
  have h2 : ∀ a b, AnalyticAt ℝ (fun q : M3 × M3 => q.2 a b) p := fun a b =>
    analyticAt_pi_apply (analyticAt_pi_apply analyticAt_snd a) b
  have h1 : ∀ a b, AnalyticAt ℝ (fun q : M3 × M3 => q.1 a b) p := fun a b =>
    analyticAt_pi_apply (analyticAt_pi_apply analyticAt_fst a) b
  refine AnalyticAt.pi fun i => AnalyticAt.pi fun j => ?_
  exact (Finset.analyticAt_fun_sum _ fun k _ => (h2 i k).mul (h2 k j)).sub (h1 i j)

/-- The linear map `(dγ, dE) ↦ dE + dE - dγ`, the derivative of `F` at `(I, I)`. -/
def sqFLin : (M3 × M3) →ₗ[ℝ] M3 where
  toFun d := d.2 + d.2 - d.1
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add]; abel
  map_smul' c a := by simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_sub,
    smul_add]

/-- The derivative of `F` at `(I, I)`. -/
def sqFDer : (M3 × M3) →L[ℝ] M3 := LinearMap.toContinuousLinearMap sqFLin

@[simp] theorem sqFDer_apply (d : M3 × M3) : sqFDer d = d.2 + d.2 - d.1 := rfl

theorem hasFDerivAt_sqF : HasFDerivAt sqF sqFDer (one3, one3) := by
  refine hasFDerivAt_of_sq_remainder 3 fun d => ?_
  have hid : sqF ((one3, one3) + d) - sqF (one3, one3) - sqFDer d = mul3 d.2 d.2 := by
    simp only [sqF, Prod.fst_add, Prod.snd_add, sqFDer_apply, mul3_add_left, mul3_add_right,
      mul3_one3, one3_mul3]
    abel
  rw [hid]
  calc ‖mul3 d.2 d.2‖ ≤ 3 * (‖d.2‖ * ‖d.2‖) := norm_mul3_le _ _
    _ ≤ 3 * (‖d‖ * ‖d‖) := by
        gcongr <;> exact norm_snd_le d
    _ = 3 * ‖d‖ ^ 2 := by ring

theorem sqF_one : sqF (one3, one3) = 0 := by simp [sqF, mul3_one3]

theorem sqFDer_inr_isInvertible : (fderiv ℝ sqF (one3, one3) ∘L
    ContinuousLinearMap.inr ℝ M3 M3).IsInvertible := by
  rw [hasFDerivAt_sqF.fderiv]
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ M3) ?_ ?_
  · ext d i j; simp; ring
  · ext d i j; simp; ring

/-- The implicit-function package for `E² = γ` at `(I, I)`. -/
theorem exists_sqrt_germ :
    ∃ ψ : M3 → M3, ψ one3 = one3 ∧ AnalyticAt ℝ ψ one3 ∧
      (∀ᶠ γ in 𝓝 one3, sqF (γ, ψ γ) = sqF (one3, one3)) ∧
      (∀ᶠ v in 𝓝 (one3, one3), sqF v = sqF (one3, one3) ↔ ψ v.1 = v.2) := by
  obtain ⟨ψ, h0, ha, hsol, huniq, -⟩ :=
    analytic_implicit_function (u := (one3, one3)) (analyticAt_sqF _) sqFDer_inr_isInvertible
  exact ⟨ψ, h0, ha, hsol, huniq⟩

/-- **The symmetric-square-root triad**: the analytic germ at `I` of the solution `E(γ)` of
`E² = γ` with `E(I) = I` (extended arbitrarily away from `I`). -/
def sqrtTriad : M3 → M3 := Classical.choose exists_sqrt_germ

theorem sqrtTriad_spec :
    sqrtTriad one3 = one3 ∧ AnalyticAt ℝ sqrtTriad one3 ∧
      (∀ᶠ γ in 𝓝 one3, sqF (γ, sqrtTriad γ) = sqF (one3, one3)) ∧
      (∀ᶠ v in 𝓝 (one3, one3), sqF v = sqF (one3, one3) ↔ sqrtTriad v.1 = v.2) :=
  Classical.choose_spec exists_sqrt_germ

/-- `E(I) = I`. -/
theorem sqrtTriad_one : sqrtTriad one3 = one3 := sqrtTriad_spec.1

/-- `E` is analytic at `I`. -/
theorem analyticAt_sqrtTriad : AnalyticAt ℝ sqrtTriad one3 := sqrtTriad_spec.2.1

/-- `E(γ)² = γ` near `I`. -/
theorem sqrtTriad_sq : ∀ᶠ γ in 𝓝 one3, mul3 (sqrtTriad γ) (sqrtTriad γ) = γ := by
  filter_upwards [sqrtTriad_spec.2.2.1] with γ hγ
  rw [sqF_one, sqF, sub_eq_zero] at hγ
  exact hγ

/-- **Local uniqueness**: near `(I, I)`, `E² = γ` holds iff `E = E(γ)`. -/
theorem sqrtTriad_unique : ∀ᶠ v in 𝓝 (one3, one3), mul3 v.2 v.2 = v.1 ↔ sqrtTriad v.1 = v.2 := by
  filter_upwards [sqrtTriad_spec.2.2.2] with v hv
  rw [sqF_one, sqF, sub_eq_zero] at hv
  exact hv

/-- For symmetric `γ` near `I`, the square root is symmetric. -/
theorem sqrtTriad_symm : ∀ᶠ γ in 𝓝 one3, tr3 γ = γ → tr3 (sqrtTriad γ) = sqrtTriad γ := by
  have hc : ContinuousAt (fun γ : M3 => (γ, tr3 (sqrtTriad γ))) one3 :=
    continuousAt_id.prodMk (continuous_tr3.continuousAt.comp analyticAt_sqrtTriad.continuousAt)
  have h0 : (fun γ : M3 => (γ, tr3 (sqrtTriad γ))) one3 = (one3, one3) := by
    simp [sqrtTriad_one, tr3_one3]
  have hu := sqrtTriad_unique
  rw [← h0] at hu
  filter_upwards [hc.eventually hu, sqrtTriad_sq] with γ hγ hsq hsym
  have : mul3 (tr3 (sqrtTriad γ)) (tr3 (sqrtTriad γ)) = γ := by
    rw [← tr3_mul3, hsq, hsym]
  exact (hγ.1 this).symm

/-- **The triad induces the metric**: `E(γ)ᵀ E(γ) = γ` for symmetric `γ` near `I`. -/
theorem sqrtTriad_transpose_mul : ∀ᶠ γ in 𝓝 one3, tr3 γ = γ →
    mul3 (tr3 (sqrtTriad γ)) (sqrtTriad γ) = γ := by
  filter_upwards [sqrtTriad_symm, sqrtTriad_sq] with γ hs hsq hγ
  rw [hs hγ, hsq]

/-- **`DE(I) = ½ id`**. -/
theorem hasFDerivAt_sqrtTriad :
    HasFDerivAt sqrtTriad ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ M3) one3 := by
  have hd := analyticAt_sqrtTriad.differentiableAt.hasFDerivAt
  set D := fderiv ℝ sqrtTriad one3
  -- the composite `γ ↦ F(γ, E(γ))` is eventually constant
  have hpair : HasFDerivAt (fun γ : M3 => (γ, sqrtTriad γ))
      ((ContinuousLinearMap.id ℝ M3).prod D) one3 := (hasFDerivAt_id one3).prodMk hd
  have hcomp : HasFDerivAt (fun γ : M3 => sqF (γ, sqrtTriad γ))
      (sqFDer ∘L (ContinuousLinearMap.id ℝ M3).prod D) one3 := by
    have h1 : HasFDerivAt sqF sqFDer ((fun γ : M3 => (γ, sqrtTriad γ)) one3) := by
      rw [show (fun γ : M3 => (γ, sqrtTriad γ)) one3 = (one3, one3) by simp [sqrtTriad_one]]
      exact hasFDerivAt_sqF
    exact h1.comp one3 hpair
  have hconst : HasFDerivAt (fun γ : M3 => sqF (γ, sqrtTriad γ)) (0 : M3 →L[ℝ] M3) one3 :=
    (hasFDerivAt_const (sqF (one3, one3)) one3).congr_of_eventuallyEq
      (sqrtTriad_spec.2.2.1.mono fun γ hγ => hγ)
  have hzero := hcomp.unique hconst
  have hD : D = (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ M3 := by
    ext v i j
    have := congrArg (fun T : M3 →L[ℝ] M3 => T v i j) hzero
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, sqFDer_apply, zero_apply,
      Pi.zero_apply, Pi.sub_apply, Pi.add_apply] at this
    simp only [smul_apply, ContinuousLinearMap.id_apply, Pi.smul_apply,
      smul_eq_mul]
    linarith
  rw [← hD]; exact hd

/-- Non-vacuity: the flat metric has the flat triad, and `I` is symmetric. -/
example : sqrtTriad one3 = one3 ∧ tr3 one3 = one3 := ⟨sqrtTriad_one, tr3_one3⟩

end RenewalGeometry.ExactPhaseAction.QuadJet
