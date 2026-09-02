/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianHeatSemigroup
import NCG.Grand.FiniteHermitianEulerRootResolventScaling
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The zero-time endpoint for finite Hermitian heat semigroups

Positive semidefinite finite generators produce contraction semigroups. On
vectors in the generator domain (all vectors in finite dimension), the heat
orbit moves by at most time times the norm of the generator applied to the
vector. The second estimate is the uniform small-time input needed to attach
the endpoint zero to varying-Hilbert Mosco semigroup convergence.
-/

open Matrix Set
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.ImplicitEuler

universe u v

private theorem hasDerivAt_exp_real_smul_apply
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (x : E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => NormedSpace.exp ((s : ℂ) • K) x)
      (K (NormedSpace.exp ((t : ℂ) • K) x)) t := by
  have h1 : HasDerivAt
      (fun z : ℂ => NormedSpace.exp (z • K))
      (K * NormedSpace.exp ((t : ℂ) • K)) (t : ℂ) :=
    hasDerivAt_exp_smul_const' K (t : ℂ)
  have h2 := h1.scomp t Complex.ofRealCLM.hasDerivAt
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul,
    Function.comp_def] at h2
  have happ :=
    ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h2
  convert happ using 1
  · funext s
    rfl
  · change K (NormedSpace.exp ((t : ℂ) • K) x) =
      (K * NormedSpace.exp ((t : ℂ) • K)) x
    rfl

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Every finite Hermitian exponential orbit is continuous in real time. -/
theorem continuous_finiteHermitian_exp_neg_apply
    (G : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    Continuous (fun t : ℝ ↦
      NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G) x) := by
  let B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G
  apply continuous_iff_continuousAt.mpr
  intro t
  have h :=
    hasDerivAt_exp_real_smul_apply (-B) x t
  simpa [B] using h.continuousAt

/-- The heat exponential of a positive-semidefinite finite Hermitian generator
is a contraction at every nonnegative time. -/
theorem norm_finiteHermitian_exp_neg_le_one
    (G : Matrix ι ι ℂ) (hG : G.PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G)‖ ≤ 1 := by
  rw [← finiteHermitianHeatOperator_eq_exp_smul hG.1 t]
  unfold finiteHermitianHeatOperator finiteHermitianHeat
    finiteUnitarySpectralHeat
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  change ‖(hG.1.eigenvectorUnitary : Matrix ι ι ℂ) *
      finiteSpectralHeat hG.1.eigenvalues t *
      (star hG.1.eigenvectorUnitary : Matrix ι ι ℂ)‖ ≤ 1
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul]
  unfold finiteSpectralHeat
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg ht (hG.eigenvalues_nonneg i)))

/-- Applied-vector small-time estimate for a positive-semidefinite finite
Hermitian heat semigroup. Unlike an operator-norm continuity estimate, its
constant depends only on the chosen vector through its generator image. -/
theorem norm_finiteHermitian_exp_neg_apply_sub_self_le
    (G : Matrix ι ι ℂ) (hG : G.PosSemidef) (t : ℝ) (ht : 0 ≤ t)
    (x : EuclideanSpace ℂ ι) :
    ‖NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G) x - x‖
      ≤ t * ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G x‖ := by
  let B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G
  let K : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι := -B
  let orbit : ℝ → EuclideanSpace ℂ ι :=
    fun s => NormedSpace.exp ((s : ℂ) • K) x
  have horbitDeriv : ∀ s : ℝ,
      HasDerivAt orbit (K (orbit s)) s := by
    intro s
    simpa [orbit] using hasDerivAt_exp_real_smul_apply K x s
  have hderivBound : ∀ s ∈ Icc (0 : ℝ) t,
      ‖K (orbit s)‖ ≤ ‖B x‖ := by
    intro s hs
    have hscale : (s : ℂ) • K = (-(s : ℂ)) • B := by
      simp [K]
    have hcomm :
        NormedSpace.exp ((-(s : ℂ)) • B) * B =
          B * NormedSpace.exp ((-(s : ℂ)) • B) :=
      ((Commute.refl B).smul_left (-(s : ℂ))).exp_left
    have heq :
        K (orbit s) =
          -(NormedSpace.exp ((-(s : ℂ)) • B) (B x)) := by
      have horbit :
          orbit s = NormedSpace.exp ((-(s : ℂ)) • B) x := by
        change NormedSpace.exp ((s : ℂ) • K) x =
          NormedSpace.exp ((-(s : ℂ)) • B) x
        rw [hscale]
      rw [horbit]
      change ((-B) * NormedSpace.exp ((-(s : ℂ)) • B)) x =
        (-(NormedSpace.exp ((-(s : ℂ)) • B) * B)) x
      rw [neg_mul, ← hcomm]
    rw [heq, norm_neg]
    calc
      ‖NormedSpace.exp ((-(s : ℂ)) • B) (B x)‖
          ≤ ‖NormedSpace.exp ((-(s : ℂ)) • B)‖ * ‖B x‖ :=
        (NormedSpace.exp ((-(s : ℂ)) • B)).le_opNorm (B x)
      _ ≤ 1 * ‖B x‖ := by
        gcongr
        simpa [B] using
          norm_finiteHermitian_exp_neg_le_one G hG s hs.1
      _ = ‖B x‖ := one_mul _
  have hmv :=
    (convex_Icc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (horbitDeriv s).hasDerivWithinAt)
      hderivBound (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
  simpa [orbit, K, B, abs_of_nonneg ht, mul_comm] using hmv

/-- A positive shifted resolvent vector belongs to a uniformly controlled
generator core: if d = (G+b)⁻¹ f, then Gd = f-bd. -/
theorem generator_apply_finiteHermitianShiftedResolventOperator
    (G : Matrix ι ι ℂ) (hG : G.PosSemidef) (b : ℝ) (hb : 0 < b)
    (f : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G
        (finiteHermitianShiftedResolventOperator G b f) =
      f - (b : ℂ) • finiteHermitianShiftedResolventOperator G b f := by
  let M : Matrix ι ι ℂ := (b : ℂ) • (1 : Matrix ι ι ℂ) + G
  have hMpos : M.PosDef := by
    have hscalar :
        ((b : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := by
      simpa [RCLike.real_smul_eq_coe_smul] using
        (Matrix.PosDef.one.smul hb)
    exact hscalar.add_posSemidef hG
  have hmul : M * M⁻¹ = 1 :=
    Matrix.mul_nonsing_inv M
      (M.isUnit_iff_isUnit_det.mp hMpos.isUnit)
  have hGinv :
      G * M⁻¹ = 1 - (b : ℂ) • M⁻¹ := by
    calc
      G * M⁻¹ =
          (M - (b : ℂ) • (1 : Matrix ι ι ℂ)) * M⁻¹ := by
            congr 1
            simp [M]
      _ = M * M⁻¹ -
          ((b : ℂ) • (1 : Matrix ι ι ℂ)) * M⁻¹ := sub_mul _ _ _
      _ = 1 - (b : ℂ) • M⁻¹ := by
        rw [hmul, Matrix.smul_mul, Matrix.one_mul]
  have hop := congrArg
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) hGinv
  simp only [map_mul, map_sub, map_one, map_smul] at hop
  have happ := congrArg
    (fun T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι => T f) hop
  simpa [M, finiteHermitianShiftedResolventOperator,
    ContinuousLinearMap.mul_apply] using happ

end NCG.ImplicitEuler
