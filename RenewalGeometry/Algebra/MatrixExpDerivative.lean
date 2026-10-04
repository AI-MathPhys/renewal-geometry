/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.OperatorHalfCoth

/-!
# The derivative of the exponential in a Banach algebra and of its local logarithms

Mathlib differentiates `NormedSpace.exp` only along commuting directions.  This file proves the
general (non-commutative) **dexp formula** in any complete normed `ℝ`-algebra `𝔸` and the
derivative of every local logarithm chart, as used in `lem:native-log-gauge-differential` of the
Einstein–SM action-closure manuscript (left-trivialized differential
`U̇ U⁻¹ = h 𝒥(Z) Ȧ`, `Z = h ad_A`, `𝒥(Z) = ∫₀¹ e^{tZ} dt`).

Main results (`ad_X Y = XY - YX`, `adOp`):
* `exp_sub_exp_eq_integral` (Duhamel): `e^A - e^B = ∫₀¹ e^{sA} (A - B) e^{(1-s)B} ds`;
* `fderiv_exp_apply`: `D exp(X)[Y] = ∫₀¹ e^{sX} Y e^{(1-s)X} ds`;
* `exp_smul_adOp_apply`: `e^{s ad_X} Y = e^{sX} Y e^{-sX}`;
* `integral_exp_smul`: `∫₀¹ e^{sZ} ds = 𝒥(Z) = Σ_k Z^k/(k+1)!` (`OperatorHalfCoth.dexpJ`);
* `fderiv_exp_eq`: **`D exp(X)[Y] = (𝒥(ad_X) Y) e^X`**;
* `hasStrictFDerivAt_exp`: if `𝒥(ad_X)` is invertible (e.g. `‖ad_X‖ ≤ 1/4`,
  `isUnit_dexpJ_adOp_of_norm_le`), `exp` is strictly differentiable at `X` with the invertible
  derivative `dexpCLE X`;
* `hasStrictFDerivAt_log_of_eventually`: **every local left inverse `Log` of `exp` near `X`
  (`Log (e^Y) = Y` for `Y` near `X`) is strictly differentiable at `e^X` with derivative
  `W ↦ 𝒥(ad_X)⁻¹ (W e^{-X})`**;
* `hasDerivAt_log_comp`: along any curve `γ` with `γ(s) = e^X`,
  `d/dt Log(γ(t))|_s = 𝒥(ad_X)⁻¹ (γ'(s) e^{-X})`;
* `hasDerivAt_log_gauge_curve`: the derivative of `t ↦ Log(e^{tξ} e^X e^{-tη})` at `t = 0` is
  `𝒥(ad_X)⁻¹ (ξ - e^{ad_X} η)`;
* `exists_log_chart`: such a local logarithm exists at every `X` with `𝒥(ad_X)` invertible
  (non-vacuity of the chart hypothesis).
-/

open NormedSpace Filter Topology Set MeasureTheory
open scoped Nat

namespace RenewalGeometry.MatrixExpDerivative

open OperatorHalfCoth

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `exp` is continuous (via analyticity, without a `ℚ`-normed structure). -/
theorem continuous_exp' : Continuous (exp : 𝔸 → 𝔸) :=
  continuous_iff_continuousAt.2 fun x => (exp_analytic (𝕂 := ℝ) x).continuousAt

/-- `e^{x+y} = e^x e^y` for commuting `x, y` in a complete normed `ℝ`-algebra. -/
theorem exp_add_of_commute' {x y : 𝔸} (h : Commute x y) : exp (x + y) = exp x * exp y := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact exp_add_of_commute h

theorem exp_mul_exp_neg (x : 𝔸) : exp x * exp (-x) = 1 := by
  rw [← exp_add_of_commute' (Commute.refl x).neg_right, add_neg_cancel, exp_zero]

theorem exp_neg_mul_exp (x : 𝔸) : exp (-x) * exp x = 1 := by
  rw [← exp_add_of_commute' (Commute.refl x).neg_left, neg_add_cancel, exp_zero]

/-- The adjoint operator `ad_X Y = XY - YX`. -/
def adOp (X : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  ContinuousLinearMap.mul ℝ 𝔸 X - (ContinuousLinearMap.mul ℝ 𝔸).flip X

@[simp] theorem adOp_apply (X Y : 𝔸) : adOp X Y = X * Y - Y * X := by
  simp [adOp]

theorem adOp_smul (c : ℝ) (X : 𝔸) : adOp (c • X) = c • adOp X := by
  ext Y
  simp [smul_sub, smul_mul_assoc, mul_smul_comm]

theorem norm_adOp_le (X : 𝔸) : ‖adOp X‖ ≤ 2 * ‖X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Y => ?_
  rw [adOp_apply]
  calc ‖X * Y - Y * X‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖X‖ * ‖Y‖ := by ring

/-! ### Duhamel's formula -/

theorem hasDerivAt_exp_duhamel (A B : 𝔸) (s : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A) * exp ((1 - s) • B))
      (exp (s • A) * (A - B) * exp ((1 - s) • B)) s := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) A s
  have h2 : HasDerivAt (fun s : ℝ => exp ((1 - s) • B)) ((-1 : ℝ) • (B * exp ((1 - s) • B))) s :=
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B (1 - s)).scomp s ((hasDerivAt_id s).const_sub 1)
  refine (h1.mul h2).congr_deriv ?_
  rw [neg_one_smul]
  simp only [mul_neg, mul_sub, sub_mul, mul_assoc]
  abel

/-- **Duhamel's formula** `e^A - e^B = ∫₀¹ e^{sA} (A - B) e^{(1-s)B} ds`. -/
theorem exp_sub_exp_eq_integral (A B : 𝔸) :
    exp A - exp B = ∫ s in (0 : ℝ)..1, exp (s • A) * (A - B) * exp ((1 - s) • B) := by
  have hc : Continuous fun s : ℝ => exp (s • A) * (A - B) * exp ((1 - s) • B) :=
    ((continuous_exp'.comp (continuous_id.smul continuous_const)).mul continuous_const).mul
      (continuous_exp'.comp ((continuous_const.sub continuous_id).smul continuous_const))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_exp_duhamel A B s)
    (hc.intervalIntegrable _ _)]
  simp

/-! ### The derivative of the exponential -/

/-- **`D exp(X)[Y] = ∫₀¹ e^{sX} Y e^{(1-s)X} ds`.** -/
theorem fderiv_exp_apply (X Y : 𝔸) :
    fderiv ℝ exp X Y = ∫ s in (0 : ℝ)..1, exp (s • X) * Y * exp ((1 - s) • X) := by
  set G : ℝ → 𝔸 := fun t => ∫ s in (0 : ℝ)..1, exp (s • (X + t • Y)) * Y * exp ((1 - s) • X)
    with hGdef
  have hG : Continuous G := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 1
    exact ((continuous_exp'.comp (continuous_snd.smul (continuous_const.add
      (continuous_fst.smul continuous_const)))).mul continuous_const).mul
      (continuous_exp'.comp ((continuous_const.sub continuous_snd).smul continuous_const))
  have hrep : ∀ t : ℝ, exp (X + t • Y) - exp X = t • G t := by
    intro t
    rw [exp_sub_exp_eq_integral, hGdef, ← intervalIntegral.integral_smul]
    congr 1
    funext s
    rw [add_sub_cancel_left, mul_smul_comm, smul_mul_assoc]
  have h1 : HasDerivAt (fun t : ℝ => exp (X + t • Y)) (fderiv ℝ exp X Y) 0 := by
    have hf := (exp_analytic (𝕂 := ℝ) X).differentiableAt.hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => X + t • Y) Y 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const Y).const_add X
    exact hf.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun t : ℝ => exp (X + t • Y)) (G 0) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hT : Tendsto G (𝓝[≠] 0) (𝓝 (G 0)) := hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [slope_def_module]
    simp only [zero_smul, add_zero, sub_zero]
    rw [hrep t, smul_smul, inv_mul_cancel₀ ht, one_smul]
  rw [h1.unique h2, hGdef]
  simp

/-! ### Conjugation by exponentials is the exponential of `ad` -/

/-- **`e^{s ad_X} Y = e^{sX} Y e^{-sX}`.** -/
theorem exp_smul_adOp_apply (X Y : 𝔸) (s : ℝ) :
    exp (s • adOp X) Y = exp (s • X) * Y * exp (-(s • X)) := by
  set phi : ℝ → 𝔸 := fun s => exp (s • -X) * exp (s • adOp X) Y * exp (s • X) with hphi
  have hd : ∀ s, HasDerivAt phi 0 s := by
    intro s
    have ha := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-X) s
    have hW : HasDerivAt (fun s : ℝ => exp (s • adOp X) Y) (adOp X (exp (s • adOp X) Y)) s := by
      have := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (adOp X) s).clm_apply (hasDerivAt_const s Y)
      simpa using this
    have hc := hasDerivAt_exp_smul_const (𝕂 := ℝ) X s
    have c1 : Commute X (exp (s • -X)) := ((Commute.refl X).neg_right.smul_right s).exp_right
    have c2 : Commute X (exp (s • X)) := ((Commute.refl X).smul_right s).exp_right
    refine ((ha.mul hW).mul hc).congr_deriv ?_
    rw [adOp_apply]
    have key : ∀ a W c : 𝔸, a * X = X * a → c * X = X * c →
        (-X * a * W + a * (X * W - W * X)) * c + a * W * (c * X) = 0 := by
      intro a W c h1 h2
      have : (-X * a * W + a * (X * W - W * X)) * c + a * W * (c * X) =
          (a * X - X * a) * W * c + a * W * (c * X - X * c) := by noncomm_ring
      rw [this, h1, h2]; simp
    exact key _ _ _ c1.eq.symm c2.eq.symm
  have hconst : ∀ s, phi s = phi 0 := by
    intro s
    exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) s 0
  have h0 : phi 0 = Y := by
    have h00 : (0 : ℝ) • adOp X = 0 := by ext; simp
    have h01 : exp ((0 : ℝ) • adOp X) = 1 := by rw [h00]; exact exp_zero
    simp only [hphi, h01, zero_smul, exp_zero, one_mul, mul_one, ContinuousLinearMap.one_apply]
  have hs := hconst s
  rw [h0] at hs
  have key : exp (s • X) * phi s * exp (-(s • X)) = exp (s • adOp X) Y := by
    simp only [hphi, smul_neg]
    rw [← mul_assoc, ← mul_assoc, exp_mul_exp_neg, one_mul, mul_assoc, exp_mul_exp_neg, mul_one]
  rw [← key, hs]

/-! ### `∫₀¹ e^{sZ} ds = 𝒥(Z)` -/

/-- **`∫₀¹ e^{sZ} ds = 𝒥(Z) = Σ_k Z^k/(k+1)!`** in any complete normed algebra with `‖1‖ = 1`. -/
theorem integral_exp_smul {𝔹 : Type*} [NormedRing 𝔹] [NormedAlgebra ℝ 𝔹] [CompleteSpace 𝔹]
    [NormOneClass 𝔹] (Z : 𝔹) : ∫ s in (0 : ℝ)..1, exp (s • Z) = dexpJ Z := by
  have hF : ∀ s : ℝ, HasSum (fun k => ((k ! : ℝ)⁻¹ * s ^ k) • Z ^ k) (exp (s • Z)) := by
    intro s
    have := exp_series_hasSum_exp' (𝕂 := ℝ) (s • Z)
    simpa [smul_pow, smul_smul] using this
  have hcont : ∀ k : ℕ, Continuous fun s : ℝ => ((k ! : ℝ)⁻¹ * s ^ k) • Z ^ k := fun k =>
    (continuous_const.mul (continuous_pow k)).smul continuous_const
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := 1) (F := fun k s => ((k ! : ℝ)⁻¹ * s ^ k) • Z ^ k) (f := fun s => exp (s • Z))
    (fun k _ => ‖Z‖ ^ k / k !) (fun k => (hcont k).aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast, abs_pow,
        abs_of_pos ht.1, div_eq_inv_mul]
      have h1 : t ^ k ≤ 1 := pow_le_one₀ ht.1.le ht.2
      have h2 : ‖Z ^ k‖ ≤ ‖Z‖ ^ k := norm_pow_le Z k
      calc (k ! : ℝ)⁻¹ * t ^ k * ‖Z ^ k‖ ≤ (k ! : ℝ)⁻¹ * 1 * ‖Z‖ ^ k := by gcongr
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun t _ => Real.summable_pow_div_factorial ‖Z‖)
    intervalIntegrable_const (Filter.Eventually.of_forall fun t _ => hF t)
  have hval : ∀ k : ℕ, ∫ s in (0 : ℝ)..1, ((k ! : ℝ)⁻¹ * s ^ k) • Z ^ k = jCoeff k • Z ^ k := by
    intro k
    rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul, integral_pow]
    congr 1
    simp only [jCoeff, one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_succ]
    field_simp
  simp only [hval] at hsum
  exact hsum.unique (hasSum_dexpJ Z)

/-! ### The dexp formula -/

section Dexp

variable [Nontrivial 𝔸]

/-- **The dexp formula** `D exp(X)[Y] = (𝒥(ad_X) Y) e^X`, `𝒥(Z) = ∫₀¹ e^{tZ} dt`. -/
theorem fderiv_exp_eq (X Y : 𝔸) : fderiv ℝ exp X Y = dexpJ (adOp X) Y * exp X := by
  rw [fderiv_exp_apply]
  have hint : ∀ s : ℝ, exp (s • X) * Y * exp ((1 - s) • X) =
      ((ContinuousLinearMap.mul ℝ 𝔸).flip (exp X)) (exp (s • adOp X) Y) := by
    intro s
    have hsplit : exp ((1 - s) • X) = exp (-(s • X)) * exp X := by
      rw [← exp_add_of_commute' ((Commute.refl X).smul_left s).neg_left, sub_smul, one_smul]
      congr 1; abel
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', exp_smul_adOp_apply,
      hsplit, mul_assoc (exp (s • X) * Y)]
  simp_rw [hint]
  have hcI : Continuous fun s : ℝ => exp (s • adOp X) :=
    continuous_exp'.comp (continuous_id.smul continuous_const)
  rw [ContinuousLinearMap.intervalIntegral_comp_comm _ ((hcI.clm_apply continuous_const).intervalIntegrable _ _),
    ← ContinuousLinearMap.intervalIntegral_apply (hcI.intervalIntegrable _ _), ]
  erw [integral_exp_smul]
  rfl

/-- `𝒥(Z) Z = e^Z - 1` (`Z` commutes with `𝒥(Z)`). -/
theorem dexpJ_mul {𝔹 : Type*} [NormedRing 𝔹] [NormedAlgebra ℝ 𝔹] [CompleteSpace 𝔹]
    [NormOneClass 𝔹] (Z : 𝔹) : dexpJ Z * Z = exp Z - 1 := by
  have h1 : HasSum (fun k => (jCoeff k • Z ^ k) * Z) (dexpJ Z * Z) := (hasSum_dexpJ Z).mul_right Z
  have h2 : HasSum (fun k => Z * (jCoeff k • Z ^ k)) (Z * dexpJ Z) := (hasSum_dexpJ Z).mul_left Z
  rw [← mul_dexpJ]
  refine h1.unique (h2.congr_fun fun k => ?_)
  rw [smul_mul_assoc, mul_smul_comm, ← pow_succ, ← pow_succ']

/-- On the chart `‖ad_X‖ ≤ 1/4` (e.g. `‖X‖ ≤ 1/8`), `𝒥(ad_X)` is invertible. -/
theorem isUnit_dexpJ_of_norm_le {𝔹 : Type*} [NormedRing 𝔹] [NormedAlgebra ℝ 𝔹] [CompleteSpace 𝔹]
    [NormOneClass 𝔹] (Z : 𝔹) (hZ : ‖Z‖ ≤ 1 / 4) : IsUnit (dexpJ Z) :=
  (dexpJ_isUnit_and_norm_inverse_le Z hZ).1

theorem isUnit_dexpJ_adOp_of_norm_le (X : 𝔸) (hX : ‖X‖ ≤ 1 / 8) : IsUnit (dexpJ (adOp X)) :=
  isUnit_dexpJ_of_norm_le _ ((norm_adOp_le X).trans (by linarith))

/-- The derivative `Y ↦ (𝒥(ad_X) Y) e^X` of `exp` at `X`, as a continuous linear map. -/
def dexpCLM (X : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  ((ContinuousLinearMap.mul ℝ 𝔸).flip (exp X)).comp (dexpJ (adOp X))

/-- The candidate inverse `W ↦ 𝒥(ad_X)⁻¹ (W e^{-X})`. -/
def dexpInvCLM (X : 𝔸) : 𝔸 →L[ℝ] 𝔸 :=
  (Ring.inverse (dexpJ (adOp X))).comp ((ContinuousLinearMap.mul ℝ 𝔸).flip (exp (-X)))

@[simp] theorem dexpCLM_apply (X Y : 𝔸) : dexpCLM X Y = dexpJ (adOp X) Y * exp X := rfl

@[simp] theorem dexpInvCLM_apply (X W : 𝔸) :
    dexpInvCLM X W = Ring.inverse (dexpJ (adOp X)) (W * exp (-X)) := rfl

theorem fderiv_exp_eq_dexpCLM (X : 𝔸) : fderiv ℝ exp X = dexpCLM X := by
  ext Y; rw [fderiv_exp_eq, dexpCLM_apply]

/-- When `𝒥(ad_X)` is invertible, the derivative of `exp` at `X` is a linear isomorphism. -/
def dexpCLE (X : 𝔸) (hJ : IsUnit (dexpJ (adOp X))) : 𝔸 ≃L[ℝ] 𝔸 :=
  ContinuousLinearEquiv.equivOfInverse (dexpCLM X) (dexpInvCLM X)
    (fun Y => by
      rw [dexpInvCLM_apply, dexpCLM_apply, mul_assoc, exp_mul_exp_neg, mul_one,
        ← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hJ]
      rfl)
    (fun W => by
      rw [dexpCLM_apply, dexpInvCLM_apply, ← ContinuousLinearMap.mul_apply,
        Ring.mul_inverse_cancel _ hJ, ContinuousLinearMap.one_apply, mul_assoc,
        exp_neg_mul_exp, mul_one])

@[simp] theorem dexpCLE_apply (X : 𝔸) (hJ : IsUnit (dexpJ (adOp X))) (Y : 𝔸) :
    dexpCLE X hJ Y = dexpJ (adOp X) Y * exp X := rfl

@[simp] theorem dexpCLE_symm_apply (X : 𝔸) (hJ : IsUnit (dexpJ (adOp X))) (W : 𝔸) :
    (dexpCLE X hJ).symm W = Ring.inverse (dexpJ (adOp X)) (W * exp (-X)) := rfl

/-- **`exp` is strictly differentiable at `X` with derivative `Y ↦ (𝒥(ad_X) Y) e^X`**, a linear
isomorphism when `𝒥(ad_X)` is invertible. -/
theorem hasStrictFDerivAt_exp (X : 𝔸) (hJ : IsUnit (dexpJ (adOp X))) :
    HasStrictFDerivAt exp ((dexpCLE X hJ : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) X := by
  have h := (exp_analytic (𝕂 := ℝ) X).hasStrictFDerivAt
  rw [fderiv_exp_eq_dexpCLM] at h
  exact h

/-- **Derivative of a local logarithm.**  If `Log (e^Y) = Y` for all `Y` near `X` and `𝒥(ad_X)`
is invertible, then `Log` is strictly differentiable at `e^X` with derivative
`W ↦ 𝒥(ad_X)⁻¹ (W e^{-X})`, the inverse of the dexp map. -/
theorem hasStrictFDerivAt_log_of_eventually (X : 𝔸) (hJ : IsUnit (dexpJ (adOp X)))
    {Log : 𝔸 → 𝔸} (hLog : ∀ᶠ Y in 𝓝 X, Log (exp Y) = Y) :
    HasStrictFDerivAt Log (((dexpCLE X hJ).symm : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) (exp X) :=
  (hasStrictFDerivAt_exp X hJ).to_local_left_inverse hLog

/-- Non-vacuity of the chart hypothesis: at every `X` with `𝒥(ad_X)` invertible there is a
local logarithm `Log` with `Log (e^Y) = Y` near `X` (the local inverse of `exp`). -/
theorem exists_log_chart (X : 𝔸) (hJ : IsUnit (dexpJ (adOp X))) :
    ∃ Log : 𝔸 → 𝔸, ∀ᶠ Y in 𝓝 X, Log (exp Y) = Y :=
  ⟨_, (hasStrictFDerivAt_exp X hJ).eventually_left_inverse⟩

/-- **Logarithmic derivative along a gauge curve.**  If `Log` is a local logarithm near `X` and
`𝒥(ad_X)` is invertible, then
`d/dt Log(e^{tξ} e^X e^{-tη})|_{t=0} = 𝒥(ad_X)⁻¹ (ξ - e^{ad_X} η)`. -/
theorem hasDerivAt_log_gauge_curve (X ξ η : 𝔸) (hJ : IsUnit (dexpJ (adOp X)))
    {Log : 𝔸 → 𝔸} (hLog : ∀ᶠ Y in 𝓝 X, Log (exp Y) = Y) :
    HasDerivAt (fun t : ℝ => Log (exp (t • ξ) * exp X * exp (-(t • η))))
      (Ring.inverse (dexpJ (adOp X)) (ξ - exp (adOp X) η)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => exp (t • ξ) * exp X * exp (t • -η))
      (ξ * exp X - exp X * η) 0 := by
    have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) ξ 0
    have h3 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-η) 0
    refine ((h1.mul (hasDerivAt_const (0 : ℝ) (exp X))).mul h3).congr_deriv ?_
    simp [sub_eq_add_neg]
  have hL := (hasStrictFDerivAt_log_of_eventually X hJ hLog).hasFDerivAt
  have := hL.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  simp only [smul_neg] at this
  refine this.congr_deriv ?_
  simp only [ContinuousLinearEquiv.coe_coe, dexpCLE_symm_apply]
  congr 1
  have hc := exp_smul_adOp_apply X η 1
  rw [one_smul, one_smul] at hc
  rw [hc, sub_mul, mul_assoc ξ, exp_mul_exp_neg, mul_one]


/-- **Chain rule for a local logarithm along an arbitrary curve**: if `Log (e^Y) = Y` near `X`,
`𝒥(ad_X)` is invertible and `γ(s) = e^X`, then
`d/dt Log(γ(t))|_{t=s} = 𝒥(ad_X)⁻¹ (γ'(s) e^{-X})` (left-trivialized `γ' γ⁻¹`). -/
theorem hasDerivAt_log_comp (X : 𝔸) (hJ : IsUnit (dexpJ (adOp X))) {Log : 𝔸 → 𝔸}
    (hLog : ∀ᶠ Y in 𝓝 X, Log (exp Y) = Y) {γ : ℝ → 𝔸} {γ' : 𝔸} {s : ℝ}
    (hγ : HasDerivAt γ γ' s) (hs : γ s = exp X) :
    HasDerivAt (fun t => Log (γ t)) (Ring.inverse (dexpJ (adOp X)) (γ' * exp (-X))) s := by
  have := (hasStrictFDerivAt_log_of_eventually X hJ hLog).hasFDerivAt.comp_hasDerivAt_of_eq s hγ
    hs.symm
  simp only [ContinuousLinearEquiv.coe_coe, dexpCLE_symm_apply] at this
  exact this

end Dexp

end

end RenewalGeometry.MatrixExpDerivative
