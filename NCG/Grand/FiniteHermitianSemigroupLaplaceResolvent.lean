/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianSemigroupLaplace
import NCG.Grand.FiniteHermitianEulerRootResolventScaling

/-!
# Laplace transforms of finite Hermitian heat orbits

The operator-valued shifted Laplace identity is converted into the exact
applied-vector formula needed by varying-Hilbert dominated convergence:

∫₀∞ exp(-λt) exp(-tG)x dt = (λI + G)⁻¹x.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.ImplicitEuler

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A scalar shift factors from a matrix exponential as the ordinary real
Laplace weight. -/
theorem exp_neg_scalarShift_add_matrix_eq_weighted
    (G : Matrix ι ι ℂ) (lam t : ℝ) :
    NormedSpace.exp
        ((-(t : ℂ)) • ((lam : ℂ) • (1 : Matrix ι ι ℂ) + G)) =
      ((Real.exp (-lam * t) : ℝ) : ℂ) •
        NormedSpace.exp ((-(t : ℂ)) • G) := by
  have hsplit :
      ((-(t : ℂ)) • ((lam : ℂ) • (1 : Matrix ι ι ℂ) + G)) =
        (((-(t : ℂ)) * (lam : ℂ)) • (1 : Matrix ι ι ℂ)) +
          (-(t : ℂ)) • G := by
    ext i j
    simp [Matrix.smul_apply]
    ring
  rw [hsplit]
  have hcomm : Commute
      (((-(t : ℂ)) * (lam : ℂ)) • (1 : Matrix ι ι ℂ))
      ((-(t : ℂ)) • G) := by
    rw [Algebra.smul_def, Matrix.mul_one]
    exact Algebra.commutes _ _
  rw [Matrix.exp_add_of_commute _ _ hcomm]
  have hscalar :
      NormedSpace.exp
          (((-(t : ℂ)) * (lam : ℂ)) • (1 : Matrix ι ι ℂ)) =
        Complex.exp ((-(t : ℂ)) * (lam : ℂ)) •
          (1 : Matrix ι ι ℂ) := by
    rw [Algebra.smul_def, Matrix.mul_one,
      ← NormedSpace.algebraMap_exp_comm,
      ← Complex.exp_eq_exp_ℂ]
    simp [Algebra.smul_def]
  rw [hscalar, Matrix.smul_mul, Matrix.one_mul]
  congr 1
  calc
    Complex.exp ((-(t : ℂ)) * (lam : ℂ)) =
        Complex.exp (((-lam * t : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = ((Real.exp (-lam * t) : ℝ) : ℂ) :=
      (Complex.ofReal_exp (-lam * t)).symm

/-- The weighted positive-semidefinite heat matrix is integrable on the
positive half-line. -/
theorem integrableOn_weighted_exp_neg_posSemidef
    (G : Matrix ι ι ℂ) (hG : G.PosSemidef)
    (lam : ℝ) (hlam : 0 < lam) :
    IntegrableOn
      (fun t : ℝ ↦ ((Real.exp (-lam * t) : ℝ) : ℂ) •
        NormedSpace.exp ((-(t : ℂ)) • G))
      (Ioi 0) := by
  have hint := integrableOn_exp_neg_shift_posSemidef hG lam hlam
  exact hint.congr (ae_of_all _ fun t ↦
    exp_neg_scalarShift_add_matrix_eq_weighted G lam t)

/-- Operator-valued unshifted form of the finite Hermitian
Laplace--resolvent identity. -/
theorem integral_weighted_exp_neg_posSemidef_eq_inv
    (G : Matrix ι ι ℂ) (hG : G.PosSemidef)
    (lam : ℝ) (hlam : 0 < lam) :
    (∫ t : ℝ in Ioi 0,
        ((Real.exp (-lam * t) : ℝ) : ℂ) •
          NormedSpace.exp ((-(t : ℂ)) • G)) =
      (((lam : ℂ) • (1 : Matrix ι ι ℂ) + G)⁻¹) := by
  rw [← integral_exp_neg_shift_posSemidef_eq_inv hG lam hlam]
  apply integral_congr_ae
  filter_upwards with t
  exact (exp_neg_scalarShift_add_matrix_eq_weighted G lam t).symm

/-- Matrix action on one Euclidean vector, bundled as a real continuous
linear map so it commutes with Bochner integration. -/
noncomputable def matrixActionCLM (x : EuclideanSpace ℂ ι) :
    Matrix ι ι ℂ →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M ↦ Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x
      map_add' := by
        intro M N
        simp
      map_smul' := by
        intro c M
        simpa only [RingHom.id_apply, _root_.smul_apply] using congrArg
          (fun T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι ↦ T x)
          (map_smul (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))
            c M) }

@[simp] theorem matrixActionCLM_apply
    (x : EuclideanSpace ℂ ι) (M : Matrix ι ι ℂ) :
    matrixActionCLM x M =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x := rfl

/-- Matrix and Euclidean-operator exponentials agree under the canonical
star-algebra equivalence. -/
theorem toEuclideanCLM_exp_neg_smul
    (G : Matrix ι ι ℂ) (hG : G.IsHermitian) (t : ℝ) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        (NormedSpace.exp ((-(t : ℂ)) • G)) =
      NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G) := by
  calc
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        (NormedSpace.exp ((-(t : ℂ)) • G)) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        (finiteHermitianHeat hG t) := by
          rw [finiteHermitianHeat_eq_exp_smul hG t]
    _ = finiteHermitianHeatOperator hG t := rfl
    _ = _ := finiteHermitianHeatOperator_eq_exp_smul hG t

/-- Weighted finite Hermitian heat orbits are Bochner integrable on the
positive half-line. -/
theorem integrableOn_weighted_finiteHermitianHeat_apply
    (G : Matrix ι ι ℂ) (hG : G.PosSemidef)
    (lam : ℝ) (hlam : 0 < lam) (x : EuclideanSpace ℂ ι) :
    IntegrableOn
      (fun t : ℝ ↦ ((Real.exp (-lam * t) : ℝ) : ℂ) •
        (NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G)) x)
      (Ioi 0) := by
  have hint := integrableOn_weighted_exp_neg_posSemidef G hG lam hlam
  have happ := (matrixActionCLM x).integrable_comp hint
  apply happ.congr
  filter_upwards with t
  simp only [matrixActionCLM_apply, map_smul, _root_.smul_apply]
  rw [toEuclideanCLM_exp_neg_smul G hG.1 t]

/-- Applied-vector form of the finite Hermitian Laplace--resolvent identity. -/
theorem integral_weighted_finiteHermitianHeat_apply_eq_shiftedResolvent
    (G : Matrix ι ι ℂ) (hG : G.PosSemidef)
    (lam : ℝ) (hlam : 0 < lam) (x : EuclideanSpace ℂ ι) :
    (∫ t : ℝ in Ioi 0,
        ((Real.exp (-lam * t) : ℝ) : ℂ) •
          (NormedSpace.exp ((-(t : ℂ)) •
            Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G)) x) =
      finiteHermitianShiftedResolventOperator G lam x := by
  have hint := integrableOn_weighted_exp_neg_posSemidef G hG lam hlam
  have hcomm := (matrixActionCLM x).integral_comp_comm hint
  rw [integral_weighted_exp_neg_posSemidef_eq_inv G hG lam hlam] at hcomm
  simp_rw [matrixActionCLM_apply, map_smul,
    toEuclideanCLM_exp_neg_smul G hG.1] at hcomm
  simpa [finiteHermitianShiftedResolventOperator] using hcomm

end NCG.ImplicitEuler
