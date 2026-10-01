/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Analysis.ApproximationSingularValues

/-!
# One-sided operator–Schmidt rank certificate
  (`cor:incidence-one-sided-rank`, spacetime–gauge duality manuscript)

For an incidence `Y ∈ B(K_s,K_t) ⊗ B(M_s,M_t)`, rendered as a matrix
`Y : Matrix (Kt × Mt) (Ks × Ms) ℂ`, the slice map `𝒮_Y` of `prop:incidence-slice-Gram` is
the realigned matrix `sliceMatrix Y : Matrix (Mt × Ms) (Kt × Ks) ℂ`, and the
operator–Schmidt coefficients of `Y` are the singular values of `𝒮_Y`, taken here in
their approximation-number rendering
`σ_{k+1}(Y) = dist_op(𝒮_Y, rank ≤ k)` (`approximationSingularValue`).

If an observed incidence `Ŷ` obeys `‖Ŷ − Y‖_HS ≤ ε`, then

`σ_k(Y) ≥ (σ̂_k − ε)₊`,   `rank Y ≥ #{k : σ̂_k > ε}`   (`eq:incidence-one-sided-rank`).

* `opNorm_euclideanOperatorOfMatrix_le_hsNorm`: the operator norm of a matrix is at most its
  Hilbert–Schmidt norm (row-wise Cauchy–Schwarz);
* `norm_sliceOperator_sub_le`: `‖𝒮_Ŷ − 𝒮_Y‖_op ≤ ‖Ŷ − Y‖_HS` (linearity of the slice
  map and invariance of the Hilbert–Schmidt norm under realignment);
* `schmidtCoefficient_lower`: the positive-part bound;
* `schmidtRank_lower`: the rank count;
* `incidence_one_sided_rank`: both assembled.

Rendering disclosed: `σ_k` is the approximation number (Eckart–Young rendering of the
singular value), `rank Y` is the rank of the slice operator (the operator–Schmidt rank),
and the count `#{k : σ̂_k > ε}` is taken over any initial segment `k < N` (all such
`k` lie below the ambient dimension anyway, since `σ̂_k = 0` for `k ≥ rank Ŷ`).  The
final caveat of the corollary (a coefficient below the error floor cannot certify
absence) is a remark, not a claim.
-/

open Matrix

namespace RenewalGeometry
namespace OneSidedRank

/-! ## Hilbert–Schmidt norm and the operator-norm bound -/

section HS

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The squared Hilbert–Schmidt norm `‖A‖²_HS = ∑ |A i j|²`. -/
noncomputable def hsNormSq (A : Matrix m n ℂ) : ℝ :=
  ∑ ij : m × n, Complex.normSq (A ij.1 ij.2)

/-- The Hilbert–Schmidt norm `‖A‖_HS`. -/
noncomputable def hsNorm (A : Matrix m n ℂ) : ℝ := Real.sqrt (hsNormSq A)

omit [DecidableEq n] in
theorem hsNormSq_nonneg (A : Matrix m n ℂ) : 0 ≤ hsNormSq A :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

omit [DecidableEq n] in
theorem hsNormSq_eq_sum_sum (A : Matrix m n ℂ) :
    hsNormSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [hsNormSq, Fintype.sum_prod_type, Complex.normSq_eq_norm_sq]

omit [DecidableEq n] in
/-- Row-wise Cauchy–Schwarz: `‖A v‖² ≤ ‖A‖²_HS ‖v‖²`. -/
theorem sum_normSq_mulVec_le (A : Matrix m n ℂ) (v : n → ℂ) :
    ∑ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ hsNormSq A * ∑ j, ‖v j‖ ^ 2 := by
  rw [hsNormSq_eq_sum_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
    simp only [mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  have h2 : (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- A matrix as a Euclidean operator. -/
noncomputable def euclideanOperatorOfMatrix (A : Matrix m n ℂ) : EuclideanOperator m n :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

theorem euclideanOperatorOfMatrix_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    euclideanOperatorOfMatrix A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

theorem norm_sq_euclideanOperatorOfMatrix_apply_le (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖euclideanOperatorOfMatrix A x‖ ^ 2 ≤ hsNormSq A * ‖x‖ ^ 2 := by
  rw [euclideanOperatorOfMatrix_apply, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  exact sum_normSq_mulVec_le A _

/-- The operator norm of a matrix (as a Euclidean operator) is at most its
Hilbert–Schmidt norm. -/
theorem opNorm_euclideanOperatorOfMatrix_le_hsNorm (A : Matrix m n ℂ) :
    ‖euclideanOperatorOfMatrix A‖ ≤ hsNorm A := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  calc ‖euclideanOperatorOfMatrix A x‖
      = Real.sqrt (‖euclideanOperatorOfMatrix A x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (hsNormSq A * ‖x‖ ^ 2) :=
        Real.sqrt_le_sqrt (norm_sq_euclideanOperatorOfMatrix_apply_le A x)
    _ = hsNorm A * ‖x‖ := by
        rw [Real.sqrt_mul (hsNormSq_nonneg A), Real.sqrt_sq (norm_nonneg _), hsNorm]

end HS

/-! ## Slice map, Schmidt coefficients and the certificate -/

variable {Kt Ks Mt Ms : Type*} [Fintype Kt] [Fintype Ks] [Fintype Mt] [Fintype Ms]
  [DecidableEq Kt] [DecidableEq Ks]

/-- The realigned slice matrix of an incidence `Y`: the matrix of the slice map
`𝒮_Y : B(K_s,K_t)* → B(M_s,M_t)` of `prop:incidence-slice-Gram`. -/
def sliceMatrix (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) : Matrix (Mt × Ms) (Kt × Ks) ℂ :=
  Matrix.of fun mm kk => Y (kk.1, mm.1) (kk.2, mm.2)

omit [Fintype Kt] [Fintype Ks] [Fintype Mt] [Fintype Ms] [DecidableEq Kt] [DecidableEq Ks] in
theorem sliceMatrix_sub (A B : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    sliceMatrix (A - B) = sliceMatrix A - sliceMatrix B := by
  ext mm kk
  simp [sliceMatrix]

omit [DecidableEq Kt] [DecidableEq Ks] in
/-- Realignment is a reindexing, so it preserves the Hilbert–Schmidt norm. -/
theorem hsNormSq_sliceMatrix (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    hsNormSq (sliceMatrix Y) = hsNormSq Y := by
  let e : (Mt × Ms) × (Kt × Ks) ≃ (Kt × Mt) × (Ks × Ms) :=
    { toFun := fun x => ((x.2.1, x.1.1), (x.2.2, x.1.2))
      invFun := fun y => ((y.1.2, y.2.2), (y.1.1, y.2.1))
      left_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
      right_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl }
  exact Fintype.sum_equiv e _ _ fun x => rfl

omit [DecidableEq Kt] [DecidableEq Ks] in
theorem hsNorm_sliceMatrix (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    hsNorm (sliceMatrix Y) = hsNorm Y := by
  rw [hsNorm, hsNorm, hsNormSq_sliceMatrix]

/-- The slice operator `𝒮_Y` as a Euclidean operator. -/
noncomputable def sliceOperator (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    EuclideanOperator (Mt × Ms) (Kt × Ks) :=
  euclideanOperatorOfMatrix (sliceMatrix Y)

theorem sliceOperator_sub (A B : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    sliceOperator A - sliceOperator B = sliceOperator (A - B) := by
  rw [sliceOperator, sliceOperator, sliceOperator, sliceMatrix_sub, euclideanOperatorOfMatrix,
    euclideanOperatorOfMatrix, euclideanOperatorOfMatrix, map_sub, map_sub]

/-- `‖𝒮_Ŷ − 𝒮_Y‖_op ≤ ‖Ŷ − Y‖_HS`. -/
theorem norm_sliceOperator_sub_le (A B : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    ‖sliceOperator A - sliceOperator B‖ ≤ hsNorm (A - B) := by
  rw [sliceOperator_sub, ← hsNorm_sliceMatrix]
  exact opNorm_euclideanOperatorOfMatrix_le_hsNorm _

/-- The `(k+1)`st operator–Schmidt coefficient `σ_{k+1}(Y)` of an incidence, in its
approximation-number rendering. -/
noncomputable def schmidtCoefficient (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) (k : ℕ) : ℝ :=
  approximationSingularValue (sliceOperator Y) k

/-- The operator–Schmidt rank of an incidence: the rank of its slice operator. -/
noncomputable def schmidtRank (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) : ℕ :=
  euclideanOperatorRank (sliceOperator Y)

theorem schmidtCoefficient_nonneg (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) (k : ℕ) :
    0 ≤ schmidtCoefficient Y k :=
  approximationSingularValue_nonneg _ _

/-- **`eq:incidence-one-sided-rank`, first bound**: `σ_k(Y) ≥ (σ̂_k − ε)₊`. -/
theorem schmidtCoefficient_lower {Y Yhat : Matrix (Kt × Mt) (Ks × Ms) ℂ} {ε : ℝ}
    (h : hsNorm (Yhat - Y) ≤ ε) (k : ℕ) :
    max (schmidtCoefficient Yhat k - ε) 0 ≤ schmidtCoefficient Y k := by
  refine max_le ?_ (schmidtCoefficient_nonneg Y k)
  have hpert := approximationSingularValue_lower_perturbation (sliceOperator Y)
    (sliceOperator Yhat) k
  have hn : ‖sliceOperator Y - sliceOperator Yhat‖ ≤ ε := by
    rw [norm_sub_rev]
    exact (norm_sliceOperator_sub_le _ _).trans h
  unfold schmidtCoefficient
  linarith

/-- **`eq:incidence-one-sided-rank`, second bound**: `rank Y ≥ #{k < N : σ̂_k > ε}`. -/
theorem schmidtRank_lower {Y Yhat : Matrix (Kt × Mt) (Ks × Ms) ℂ} {ε : ℝ}
    (h : hsNorm (Yhat - Y) ≤ ε) (N : ℕ) :
    ((Finset.range N).filter fun k => ε < schmidtCoefficient Yhat k).card ≤ schmidtRank Y := by
  set K := ((Finset.range N).filter fun k => ε < schmidtCoefficient Yhat k).card with hK
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · rw [hK0]
    exact Nat.zero_le _
  · have hlast : ε < schmidtCoefficient Yhat (K - 1) := by
      by_contra hcon
      push Not at hcon
      have hsub : ((Finset.range N).filter fun k => ε < schmidtCoefficient Yhat k)
          ⊆ Finset.range (K - 1) := by
        intro k hk
        rw [Finset.mem_filter] at hk
        rw [Finset.mem_range]
        by_contra hge
        push Not at hge
        have hmono := approximationSingularValue_antitone (sliceOperator Yhat) hge
        change schmidtCoefficient Yhat k ≤ schmidtCoefficient Yhat (K - 1) at hmono
        linarith [hk.2]
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_range] at hcard
      omega
    have hpos : 0 < schmidtCoefficient Y (K - 1) := by
      have hlow := schmidtCoefficient_lower h (K - 1)
      have h2 : 0 < schmidtCoefficient Yhat (K - 1) - ε := by linarith
      exact lt_of_lt_of_le (lt_of_lt_of_le h2 (le_max_left _ _)) hlow
    by_contra hlt
    push Not at hlt
    have hzero := approximationSingularValue_eq_zero_of_rank_le (sliceOperator Y) (K - 1)
      (by change schmidtRank Y ≤ K - 1; omega)
    change schmidtCoefficient Y (K - 1) = 0 at hzero
    linarith

/-- **`cor:incidence-one-sided-rank`** (`eq:incidence-one-sided-rank`): if the observed
incidence obeys `‖Ŷ − Y‖_HS ≤ ε`, then every operator–Schmidt coefficient of `Y` is
bounded below by `(σ̂_k − ε)₊` and the operator–Schmidt rank of `Y` is at least the
number of observed coefficients above the error floor. -/
theorem incidence_one_sided_rank {Y Yhat : Matrix (Kt × Mt) (Ks × Ms) ℂ} {ε : ℝ}
    (h : hsNorm (Yhat - Y) ≤ ε) :
    (∀ k, max (schmidtCoefficient Yhat k - ε) 0 ≤ schmidtCoefficient Y k)
    ∧ ∀ N, ((Finset.range N).filter fun k => ε < schmidtCoefficient Yhat k).card
        ≤ schmidtRank Y :=
  ⟨schmidtCoefficient_lower h, schmidtRank_lower h⟩

end OneSidedRank
end RenewalGeometry

