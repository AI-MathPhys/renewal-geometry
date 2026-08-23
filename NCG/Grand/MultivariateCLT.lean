/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Multivariate central limit theorem (Cramér–Wold)

Machinery for the stochastic continuum records (`cor:primitive-score-continuum`,
`thm:concrete-renewal-score-profile`, the Ornstein–Uhlenbeck records): the vector
central limit theorem for i.i.d. centred square-integrable random vectors in
`EuclideanSpace ℝ ι`, derived from Mathlib's one-dimensional CLT through the
Cramér–Wold device (Lévy's continuity theorem on the finite-dimensional carrier).

* `covMatrix X P` is the covariance matrix `E[X_i X_j]` of a centred vector variable;
  `covMatrix_posSemidef`, `dotProduct_covMatrix` (`tᵀ S t = E[⟪t, X⟫²]`),
  `variance_inner` (`Var ⟪t, X⟫ = tᵀ S t`);
* `hasLaw_inner_multivariateGaussian`: the projection `⟪t, Y⟫` of a centred Gaussian vector
  with covariance `S` is `N(0, tᵀ S t)`;
* `tendstoInDistribution_inv_sqrt_smul_sum` (**multivariate CLT**): for i.i.d. centred
  square-integrable `X k : Ω → EuclideanSpace ℝ ι`, `n^{-1/2} ∑_{k<n} X k` converges in
  distribution to the centred multivariate Gaussian with covariance `covMatrix X P`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex Finset Matrix
open scoped InnerProductSpace

namespace NCG
namespace MultivariateCLT

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι]
variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- The inner product on `EuclideanSpace ℝ ι` as a coordinate sum. -/
theorem inner_eq_sum (t x : EuclideanSpace ℝ ι) : ⟪t, x⟫_ℝ = ∑ i, t i * x i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The covariance matrix `E[X_i X_j]` of a (centred) vector variable. -/
noncomputable def covMatrix (X : Ω → EuclideanSpace ℝ ι) (P : Measure Ω) : Matrix ι ι ℝ :=
  Matrix.of fun i j => P[fun ω => X ω i * X ω j]

/-- Coordinates of a square-integrable vector variable are square-integrable. -/
theorem memLp_coord {X : Ω → EuclideanSpace ℝ ι} (hX : MemLp X 2 P) (i : ι) :
    MemLp (fun ω => X ω i) 2 P := by
  classical
  have h : MemLp (fun ω => ⟪EuclideanSpace.single i (1 : ℝ), X ω⟫_ℝ) 2 P :=
    hX.const_inner (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))
  refine MemLp.ae_eq (Filter.Eventually.of_forall fun ω => ?_) h
  simp [EuclideanSpace.inner_single_left]

theorem integrable_coord_mul {X : Ω → EuclideanSpace ℝ ι} (hX : MemLp X 2 P) (i j : ι) :
    Integrable (fun ω => X ω i * X ω j) P :=
  (memLp_coord hX i).integrable_mul (memLp_coord hX j)

omit [Fintype ι] in
theorem covMatrix_apply (X : Ω → EuclideanSpace ℝ ι) (i j : ι) :
    covMatrix X P i j = P[fun ω => X ω i * X ω j] := rfl

omit [Fintype ι] in
theorem covMatrix_isHermitian {X : Ω → EuclideanSpace ℝ ι} :
    (covMatrix X P).IsHermitian := by
  ext i j
  simp [covMatrix_apply, mul_comm]

/-- `tᵀ S t = E[⟪t, X⟫²]`. -/
theorem dotProduct_covMatrix {X : Ω → EuclideanSpace ℝ ι} (hX : MemLp X 2 P)
    (t : EuclideanSpace ℝ ι) :
    t ⬝ᵥ covMatrix X P *ᵥ t = P[fun ω => ⟪t, X ω⟫_ℝ ^ 2] := by
  have hint : ∀ i j, Integrable (fun ω => t i * t j * (X ω i * X ω j)) P := fun i j =>
    (integrable_coord_mul hX i j).const_mul _
  calc t ⬝ᵥ covMatrix X P *ᵥ t
      = ∑ i, ∑ j, t i * t j * P[fun ω => X ω i * X ω j] := by
        simp only [dotProduct, Matrix.mulVec, covMatrix_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, ∑ j, P[fun ω => t i * t j * (X ω i * X ω j)] := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
    _ = P[fun ω => ∑ i, ∑ j, t i * t j * (X ω i * X ω j)] := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => hint i j]
    _ = P[fun ω => ⟪t, X ω⟫_ℝ ^ 2] := by
        congr 1
        funext ω
        beta_reduce
        rw [inner_eq_sum, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring

theorem covMatrix_posSemidef {X : Ω → EuclideanSpace ℝ ι} (hX : MemLp X 2 P) :
    (covMatrix X P).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨covMatrix_isHermitian, fun t => ?_⟩
  have := dotProduct_covMatrix hX (WithLp.toLp 2 t)
  simp only [star_trivial]
  have ht : (WithLp.toLp 2 t : EuclideanSpace ℝ ι) ⬝ᵥ covMatrix X P *ᵥ (WithLp.toLp 2 t) =
      t ⬝ᵥ covMatrix X P *ᵥ t := rfl
  rw [← ht, this]
  exact integral_nonneg fun ω => sq_nonneg _

/-- The mean of a projection of a centred vector variable vanishes. -/
theorem integral_inner_eq_zero {X : Ω → EuclideanSpace ℝ ι} (hX : Integrable X P)
    (h0 : P[X] = 0) (t : EuclideanSpace ℝ ι) : P[fun ω => ⟪t, X ω⟫_ℝ] = 0 := by
  rw [integral_inner hX, h0, inner_zero_right]

/-- `Var ⟪t, X⟫ = tᵀ S t` for a centred square-integrable vector variable. -/
theorem variance_inner {X : Ω → EuclideanSpace ℝ ι} (hX : MemLp X 2 P) (h0 : P[X] = 0)
    (t : EuclideanSpace ℝ ι) :
    Var[fun ω => ⟪t, X ω⟫_ℝ; P] = t ⬝ᵥ covMatrix X P *ᵥ t := by
  rw [variance_of_integral_eq_zero (hX.const_inner (𝕜 := ℝ) t).aemeasurable
    (integral_inner_eq_zero (hX.integrable (by norm_num)) h0 t), dotProduct_covMatrix hX]

/-! ### Gaussian projections -/

variable [DecidableEq ι]

/-- The projection of a centred Gaussian vector with covariance `S` is `N(0, tᵀ S t)`. -/
theorem hasLaw_inner_multivariateGaussian {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    {Y : Ω' → EuclideanSpace ℝ ι} (hY : HasLaw Y (multivariateGaussian 0 S) P')
    (t : EuclideanSpace ℝ ι) :
    HasLaw (fun ω => ⟪t, Y ω⟫_ℝ) (gaussianReal 0 (t ⬝ᵥ S *ᵥ t).toNNReal) P' := by
  have hG : HasGaussianLaw Y P' := hY.hasGaussianLaw
  have hG' : HasGaussianLaw (fun ω => ⟪t, Y ω⟫_ℝ) P' := by
    have := hG.map_fun (innerSL ℝ t)
    simpa using this
  have hmeas : AEMeasurable (fun ω => ⟪t, Y ω⟫_ℝ) P' := hG'.aemeasurable
  refine ⟨hmeas, ?_⟩
  rw [hG'.map_eq_gaussianReal]
  -- mean and variance of the projection
  have hYmeas : AEMeasurable Y P' := hY.aemeasurable
  have hmean : P'[fun ω => ⟪t, Y ω⟫_ℝ] = 0 := by
    rw [← integral_map (f := fun y => ⟪t, y⟫_ℝ) hYmeas (by fun_prop), hY.map_eq,
      show (∫ y, ⟪t, y⟫_ℝ ∂multivariateGaussian 0 S) = ⟪t, ∫ y, y ∂multivariateGaussian 0 S⟫_ℝ from
        integral_inner IsGaussian.integrable_id t,
      integral_id_multivariateGaussian, inner_zero_right]
  have hvar : Var[fun ω => ⟪t, Y ω⟫_ℝ; P'] = t ⬝ᵥ S *ᵥ t := by
    rw [variance_of_integral_eq_zero hmeas hmean,
      ← integral_map (f := fun y => ⟪t, y⟫_ℝ ^ 2) hYmeas (by fun_prop), hY.map_eq,
      ← covarianceBilin_multivariateGaussian hS t t,
      covarianceBilin_apply (μ := multivariateGaussian 0 S) IsGaussian.memLp_two_id t t,
      integral_id_multivariateGaussian' (μ := 0) (S := S)]
    simp [sq]
  rw [hmean, hvar]

/-! ### The multivariate CLT -/

omit [DecidableEq ι] in
/-- The characteristic function of a vector variable at `t` is the characteristic function
of its projection `⟪t, ·⟫` at `1`. -/
theorem charFun_map_eq_charFun_inner {X : Ω → EuclideanSpace ℝ ι} (hX : AEMeasurable X P)
    (t : EuclideanSpace ℝ ι) :
    charFun (P.map X) t = charFun (P.map fun ω => ⟪t, X ω⟫_ℝ) 1 := by
  have hXt : AEMeasurable (fun ω => ⟪t, X ω⟫_ℝ) P := hX.const_inner
  rw [charFun_apply, charFun_apply_real, integral_map (f := fun x => exp (⟪x, t⟫_ℝ * I)) hX
    (by fun_prop), integral_map (f := fun x : ℝ => exp (((1 : ℝ) : ℂ) * (x : ℂ) * I)) hXt
    (by fun_prop)]
  simp [real_inner_comm]

/-- **Multivariate central limit theorem (Cramér–Wold).** For i.i.d. centred
square-integrable random vectors `X k` in `EuclideanSpace ℝ ι` and a random vector `Y` with the
centred Gaussian law of covariance `covMatrix X P`, the normalised sums `n^{-1/2} ∑_{k<n} X k`
converge in distribution to `Y`. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum {X : ℕ → Ω → EuclideanSpace ℝ ι}
    {Y : Ω' → EuclideanSpace ℝ ι}
    (hY : HasLaw Y (multivariateGaussian 0 (covMatrix (X 0) P)) P')
    (hX : MemLp (X 0) 2 P) (h0 : P[X 0] = 0) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω => (√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω) atTop Y
      (fun _ => P) P' := by
  have hmeas : ∀ k, AEMeasurable (X k) P := fun k => (hident k).aemeasurable_fst
  have hSn : ∀ n : ℕ, AEMeasurable (fun ω => (√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω) P :=
    fun n => by fun_prop
  refine ⟨hSn, hY.aemeasurable, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
  -- the scalar projections
  set ξ : ℕ → Ω → ℝ := fun k ω => ⟪t, X k ω⟫_ℝ with hξ
  have hξmeas : ∀ k, AEMeasurable (ξ k) P := fun k => (hmeas k).const_inner
  have hξL2 : MemLp (ξ 0) 2 P := hX.const_inner (𝕜 := ℝ) t
  have hξindep : iIndepFun ξ P := hindep.comp (fun _ x => ⟪t, x⟫_ℝ) (by fun_prop)
  have hξident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P :=
    fun i => (hident i).comp (u := fun x => ⟪t, x⟫_ℝ) (by fun_prop)
  have hξ0 : P[ξ 0] = 0 := integral_inner_eq_zero (hX.integrable (by norm_num)) h0 t
  have hξvar : Var[ξ 0; P] = t ⬝ᵥ covMatrix (X 0) P *ᵥ t := variance_inner hX h0 t
  have hYt : HasLaw (fun ω => ⟪t, Y ω⟫_ℝ) (gaussianReal 0 Var[ξ 0; P].toNNReal) P' := by
    rw [hξvar]
    exact hasLaw_inner_multivariateGaussian (covMatrix_posSemidef hX) hY t
  have hreal := tendstoInDistribution_inv_sqrt_mul_sum_sub hYt hξL2 hξindep hξident
  have hchar := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hreal.tendsto 1
  -- identify both sides with the projected characteristic functions
  have hL : ∀ n : ℕ, charFun (P.map fun ω => (√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω) t =
      charFun (P.map fun ω => (√n)⁻¹ * (∑ k ∈ Finset.range n, ξ k ω - n * P[ξ 0])) 1 := by
    intro n
    rw [charFun_map_eq_charFun_inner (hSn n) t, hξ0]
    congr 2
    funext ω
    simp [ξ, inner_smul_right, inner_sum]
  have hR : charFun (P'.map Y) t = charFun (P'.map fun ω => ⟪t, Y ω⟫_ℝ) 1 :=
    charFun_map_eq_charFun_inner hY.aemeasurable t
  convert hchar using 2
  · exact hL _
  · exact hR

end MultivariateCLT
end NCG
