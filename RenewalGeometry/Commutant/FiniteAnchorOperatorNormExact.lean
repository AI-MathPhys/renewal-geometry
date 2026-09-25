/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.FiniteAnchorHoweActualExact

/-!
# Finite-anchor stability from operator-norm data (`thm:finite-anchor`)

`thm:finite-anchor` of the spacetime–gauge duality manuscript.  Transport a cutoff family
to one common finite screened carrier `ℂ^n`, write `c_X = (c_{1,X}, …, c_{s,X})`, and put

* `C_X = (∑_j ‖c_{j,X}‖_op²)^{1/2}` (`opNormBudget`),
* `ε_{X,Y} = (∑_j ‖c_{j,X} - c_{j,Y}‖_op²)^{1/2}` (`opNormDisplacement`),

with `‖·‖_op` the `ℓ²` operator norm of a matrix (`Matrix.Norms.L2Operator`).  If a fixed
protected algebra `M` commutes with both tuples, the anchor Howe Gram satisfies
`𝔾_Howe(c_{X₀} | M) ⪰ γ₀ I` on `M^⊥`, and `4 (C_X + C_{X₀}) ε_{X,X₀} < γ₀`, then
`C*(c_X)' = M` and `λ⁺_min(ℒ_{C*(c_X)}) ≥ γ₀ - 4 (C_X + C_{X₀}) ε_{X,X₀}`
(`finiteAnchorHowe_operatorNormData`).

The earlier file `FiniteAnchorHoweActualExact.lean` assumed the quadratic-form
perturbation bound `|‖J_c x‖² - ‖J_{c₀} x‖²| ≤ 4 (C + C₀) ε ‖x‖²` as a hypothesis; here it is
*derived* from the operator-norm data through the cross-cutting Hilbert–Schmidt estimates

* `matrixL2_mul_le`, `matrixL2_mul_right_le`: `‖A X‖_HS ≤ ‖A‖_op ‖X‖_HS`,
  `‖X A‖_HS ≤ ‖A‖_op ‖X‖_HS`;
* `matrixL2_commutator_le`: `‖[A, X]‖_HS ≤ 2 ‖A‖_op ‖X‖_HS`;
* `jointCommutatorL2_norm_le`: `‖∂_c‖_{2→2} ≤ 2 C`;
* `jointCommutatorL2_sub_norm_le`: `‖∂_c - ∂_{c₀}‖_{2→2} ≤ 2 ε`;
* `jointCommutatorL2_sq_perturbation`: the manuscript's
  `A*A - B*B = A*(A-B) + (A*-B*)B` quadratic-form bound `4 (C + C₀) ε ‖x‖²`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RenewalGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Hilbert–Schmidt versus operator norm -/

/-- The Hilbert–Schmidt realization inverts the entry extraction. -/
theorem matrixL2_l2Matrix {m k : Type*} [Fintype m] [Fintype k]
    (x : EuclideanSpace ℂ (m × k)) : matrixL2 (l2Matrix x) = x := by
  ext ⟨i, j⟩
  simp [matrixL2, l2Matrix]

/-- The Hilbert–Schmidt norm is invariant under conjugate transposition. -/
theorem matrixL2_conjTranspose_norm {m k : Type*} [Fintype m] [Fintype k]
    (M : Matrix m k ℂ) : ‖matrixL2 Mᴴ‖ = ‖matrixL2 M‖ := by
  have h : ‖matrixL2 Mᴴ‖ ^ 2 = ‖matrixL2 M‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [matrixL2, WithLp.ofLp_toLp, Fintype.sum_prod_type, conjTranspose_apply,
      norm_star]
    rw [Finset.sum_comm]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The Hilbert–Schmidt norm of `M` is the sum of the squared Euclidean norms of its columns. -/
theorem matrixL2_norm_sq_eq_sum_cols {m k : Type*} [Fintype m] [Fintype k]
    (M : Matrix m k ℂ) :
    ‖matrixL2 M‖ ^ 2 = ∑ j, ‖(WithLp.toLp 2 (M.col j) : EuclideanSpace ℂ m)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [matrixL2, WithLp.ofLp_toLp, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  simp [Matrix.col]

/-- **Cross-cutting estimate**: `‖A X‖_HS ≤ ‖A‖_op ‖X‖_HS` for the `ℓ²` operator norm. -/
theorem matrixL2_mul_le {k : Type*} [Fintype k] (A : Matrix n n ℂ) (X : Matrix n k ℂ) :
    ‖matrixL2 (A * X)‖ ≤ ‖A‖ * ‖matrixL2 X‖ := by
  have hsq : ‖matrixL2 (A * X)‖ ^ 2 ≤ (‖A‖ * ‖matrixL2 X‖) ^ 2 := by
    rw [matrixL2_norm_sq_eq_sum_cols, mul_pow, matrixL2_norm_sq_eq_sum_cols, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hcol : (A * X).col j = A *ᵥ X.col j := by
      ext i
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]
    rw [hcol, ← mul_pow]
    have hle : ‖(WithLp.toLp 2 (A *ᵥ X.col j) : EuclideanSpace ℂ n)‖
        ≤ ‖A‖ * ‖(WithLp.toLp 2 (X.col j) : EuclideanSpace ℂ n)‖ := by
      rw [← Matrix.toEuclideanCLM_toLp, ← Matrix.l2_opNorm_toEuclideanCLM]
      exact ContinuousLinearMap.le_opNorm _ _
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- **Cross-cutting estimate**: `‖X A‖_HS ≤ ‖A‖_op ‖X‖_HS` for the `ℓ²` operator norm. -/
theorem matrixL2_mul_right_le (A X : Matrix n n ℂ) :
    ‖matrixL2 (X * A)‖ ≤ ‖A‖ * ‖matrixL2 X‖ := by
  calc ‖matrixL2 (X * A)‖ = ‖matrixL2 (X * A)ᴴ‖ := (matrixL2_conjTranspose_norm _).symm
    _ = ‖matrixL2 (Aᴴ * Xᴴ)‖ := by rw [Matrix.conjTranspose_mul]
    _ ≤ ‖Aᴴ‖ * ‖matrixL2 Xᴴ‖ := matrixL2_mul_le _ _
    _ = ‖A‖ * ‖matrixL2 X‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, matrixL2_conjTranspose_norm]

/-- **Cross-cutting estimate**: `‖[A, X]‖_HS ≤ 2 ‖A‖_op ‖X‖_HS`. -/
theorem matrixL2_commutator_le (A X : Matrix n n ℂ) :
    ‖matrixL2 (A * X - X * A)‖ ≤ 2 * ‖A‖ * ‖matrixL2 X‖ := by
  rw [matrixL2_sub]
  calc ‖matrixL2 (A * X) - matrixL2 (X * A)‖
      ≤ ‖matrixL2 (A * X)‖ + ‖matrixL2 (X * A)‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖matrixL2 X‖ + ‖A‖ * ‖matrixL2 X‖ :=
        add_le_add (matrixL2_mul_le _ _) (matrixL2_mul_right_le _ _)
    _ = 2 * ‖A‖ * ‖matrixL2 X‖ := by ring

/-! ### The joint commutator derivation -/

omit [DecidableEq n] in
/-- The squared norm of the joint commutator is the sum over the letters of the squared
Hilbert–Schmidt commutator norms. -/
theorem jointCommutatorL2_norm_sq_eq_sum {s : ℕ} (c : Fin s → Matrix n n ℂ)
    (x : EuclideanSpace ℂ (n × n)) :
    ‖jointCommutatorL2 c x‖ ^ 2
      = ∑ j, ‖matrixL2 (c j * l2Matrix x - l2Matrix x * c j)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [jointCommutatorL2, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  simp [matrixL2, Fintype.sum_prod_type]

omit [DecidableEq n] in
/-- The joint commutator is linear in the letter tuple. -/
theorem jointCommutatorL2_sub_apply {s : ℕ} (c c₀ : Fin s → Matrix n n ℂ)
    (x : EuclideanSpace ℂ (n × n)) :
    jointCommutatorL2 c x - jointCommutatorL2 c₀ x = jointCommutatorL2 (c - c₀) x := by
  ext ⟨j, i, k⟩
  simp [jointCommutatorL2, Matrix.sub_mul, Matrix.mul_sub]
  ring

/-- The operator-norm budget `C_X = (∑_j ‖c_{j,X}‖_op²)^{1/2}` of `thm:finite-anchor`. -/
noncomputable def opNormBudget {s : ℕ} (c : Fin s → Matrix n n ℂ) : ℝ :=
  Real.sqrt (∑ j, ‖c j‖ ^ 2)

/-- The operator-norm displacement `ε_{X,Y} = (∑_j ‖c_{j,X} - c_{j,Y}‖_op²)^{1/2}` of
`thm:finite-anchor`. -/
noncomputable def opNormDisplacement {s : ℕ} (c c₀ : Fin s → Matrix n n ℂ) : ℝ :=
  opNormBudget (c - c₀)

theorem opNormBudget_nonneg {s : ℕ} (c : Fin s → Matrix n n ℂ) : 0 ≤ opNormBudget c :=
  Real.sqrt_nonneg _

theorem opNormDisplacement_nonneg {s : ℕ} (c c₀ : Fin s → Matrix n n ℂ) :
    0 ≤ opNormDisplacement c c₀ :=
  Real.sqrt_nonneg _

theorem opNormBudget_sq {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    opNormBudget c ^ 2 = ∑ j, ‖c j‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `‖∂_{c} x‖ ≤ 2 C_X ‖x‖`: the derivation bound of `thm:finite-anchor`. -/
theorem jointCommutatorL2_norm_le {s : ℕ} (c : Fin s → Matrix n n ℂ)
    (x : EuclideanSpace ℂ (n × n)) :
    ‖jointCommutatorL2 c x‖ ≤ 2 * opNormBudget c * ‖x‖ := by
  have hsq : ‖jointCommutatorL2 c x‖ ^ 2 ≤ (2 * opNormBudget c * ‖x‖) ^ 2 := by
    rw [jointCommutatorL2_norm_sq_eq_sum]
    calc ∑ j, ‖matrixL2 (c j * l2Matrix x - l2Matrix x * c j)‖ ^ 2
        ≤ ∑ j, (2 * ‖c j‖ * ‖x‖) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          have h := matrixL2_commutator_le (c j) (l2Matrix x)
          rwa [matrixL2_l2Matrix] at h
      _ = (2 * opNormBudget c * ‖x‖) ^ 2 := by
          rw [mul_pow, mul_pow, opNormBudget_sq, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (by have := opNormBudget_nonneg c; positivity)).mp hsq

/-- `‖(∂_c - ∂_{c₀}) x‖ ≤ 2 ε_{X,X₀} ‖x‖`: the displacement bound of `thm:finite-anchor`. -/
theorem jointCommutatorL2_sub_norm_le {s : ℕ} (c c₀ : Fin s → Matrix n n ℂ)
    (x : EuclideanSpace ℂ (n × n)) :
    ‖jointCommutatorL2 c x - jointCommutatorL2 c₀ x‖
      ≤ 2 * opNormDisplacement c c₀ * ‖x‖ := by
  rw [jointCommutatorL2_sub_apply]
  exact jointCommutatorL2_norm_le (c - c₀) x

/-- The manuscript's quadratic-form perturbation bound
`|‖∂_c x‖² - ‖∂_{c₀} x‖²| ≤ 4 (C_X + C_{X₀}) ε_{X,X₀} ‖x‖²`, derived from the operator-norm
data via `A*A - B*B = A*(A-B) + (A*-B*)B`. -/
theorem jointCommutatorL2_sq_perturbation {s : ℕ} (c c₀ : Fin s → Matrix n n ℂ)
    (x : EuclideanSpace ℂ (n × n)) :
    |‖jointCommutatorL2 c x‖ ^ 2 - ‖jointCommutatorL2 c₀ x‖ ^ 2|
      ≤ 4 * (opNormBudget c + opNormBudget c₀) * opNormDisplacement c c₀ * ‖x‖ ^ 2 := by
  set a := ‖jointCommutatorL2 c x‖ with ha
  set b := ‖jointCommutatorL2 c₀ x‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hab : |a - b| ≤ 2 * opNormDisplacement c c₀ * ‖x‖ :=
    (abs_norm_sub_norm_le _ _).trans (jointCommutatorL2_sub_norm_le c c₀ x)
  have hsum : a + b ≤ 2 * opNormBudget c * ‖x‖ + 2 * opNormBudget c₀ * ‖x‖ :=
    add_le_add (jointCommutatorL2_norm_le c x) (jointCommutatorL2_norm_le c₀ x)
  have hfactor : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a + b)]
  have hε := opNormDisplacement_nonneg c c₀
  have hx := norm_nonneg x
  calc |a - b| * (a + b)
      ≤ (2 * opNormDisplacement c c₀ * ‖x‖)
          * (2 * opNormBudget c * ‖x‖ + 2 * opNormBudget c₀ * ‖x‖) :=
        mul_le_mul hab hsum (by positivity) (by positivity)
    _ = 4 * (opNormBudget c + opNormBudget c₀) * opNormDisplacement c c₀ * ‖x‖ ^ 2 := by
        ring

/-! ### The finite-anchor theorem -/

/-- **`thm:finite-anchor` (Finite-anchor stability).**  On a common finite screened carrier,
if the protected algebra `M` commutes with the anchor tuple `c₀ = c_{X₀}` and the later tuple
`c = c_X`, the anchor Howe Gram has the floor `γ₀ > 0` on `M^⊥`, and the operator-norm data
satisfy `4 (C_X + C_{X₀}) ε_{X,X₀} < γ₀`, then the later commutant is exactly `M`
(`C*(c_X)' = M`, in both the Hilbert–Schmidt-kernel and the matrix-commutant form) and the
first positive eigenvalue of the later commutant Laplacian is at least
`γ₀ - 4 (C_X + C_{X₀}) ε_{X,X₀} > 0`. -/
theorem finiteAnchorHowe_operatorNormData {s : ℕ}
    (c₀ c : Fin s → Matrix n n ℂ)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (γ₀ : ℝ) (hγ : 0 < γ₀)
    (hM₀ : M ≤ LinearMap.ker (jointCommutatorL2 c₀))
    (hM : M ≤ LinearMap.ker (jointCommutatorL2 c))
    (hanchor : ∀ x ∈ Mᗮ, γ₀ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 c₀ x‖ ^ 2)
    (hsmall : 4 * (opNormBudget c + opNormBudget c₀) * opNormDisplacement c c₀ < γ₀) :
    LinearMap.ker (jointCommutatorL2 c) = M
    ∧ 0 < γ₀ - 4 * (opNormBudget c + opNormBudget c₀) * opNormDisplacement c c₀
    ∧ (∀ x ∈ Mᗮ,
        (γ₀ - 4 * (opNormBudget c + opNormBudget c₀) * opNormDisplacement c c₀) * ‖x‖ ^ 2
          ≤ ‖jointCommutatorL2 c x‖ ^ 2)
    ∧ (∀ X : Matrix n n ℂ,
        matrixL2 X ∈ LinearMap.ker (jointCommutatorL2 c) ↔ ∀ j, c j * X = X * c j)
    ∧ RelativeHoweSpectralMargin c :=
  finiteAnchorHowe_actualJointCommutator c₀ c M γ₀ (opNormBudget c) (opNormBudget c₀)
    (opNormDisplacement c c₀) hγ (opNormBudget_nonneg c) (opNormBudget_nonneg c₀)
    (opNormDisplacement_nonneg c c₀) hM₀ hM hanchor
    (jointCommutatorL2_sq_perturbation c c₀) hsmall

end RenewalGeometry
