/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact finite Store-frequency pencil
  (`thm:store-frequency-pencil-master`, flagship manuscript)

For the moment sequence `m_n = Σ_j w_j λ_jⁿ` of the loaded Store
spectrum (`w_j > 0`, `λ_j > 0` pairwise distinct) and the Hankel
matrices `H₀ = [m_{a+b}]`, `H₁ = [m_{a+b+1}]` of size `s`:

* `H₀ ≻ 0` and `H₁ ⪰ 0` (`storeH0_posDef`, `storeH1_posSemidef`),
  via the Vandermonde factorizations (`storeH0_factor`,
  `storeH1_factor`);
* generalized eigenpairs: for each `j` the vector `x_j = V⁻¹e_j`
  satisfies the boxed pencil equation `H₁x_j = λ_jH₀x_j`, is
  nonzero, and the family is linearly independent — a basis of
  generalized eigenvectors carrying each loaded value once
  (`store_pencil_eigen`, `store_pencil_independent`);
* with the monic annihilator `q(t) = Π_j(t-λ_j)`, the boxed
  system `H₀(q_0,…,q_{s-1})ᵀ = -(m_s,…,m_{2s-1})ᵀ` and its
  uniqueness (`store_annihilator_system`,
  `store_annihilator_unique`);
* the boxed exact recurrence `m_{n+s} + Σ_k q_k m_{n+k} = 0` for
  every `n` (`store_recurrence`);
* the boxed weight recovery `w = V⁻¹(m_0,…,m_{s-1})ᵀ` in the
  manuscript's convention `V_{aj} = λ_jᵃ`
  (`store_weight_recovery`).

The first `2s` moments therefore determine the loaded spectrum,
its weights, and its exact finite recurrence.  The strict ordering
`0 < λ_1 < ⋯ < λ_s` of the manuscript enters as positivity plus
pairwise distinctness (disclosed).
-/

open Matrix Polynomial Finset

namespace NCG

variable {s : ℕ} (w lam : Fin s → ℝ)

/-- The Store moment sequence `m_n = Σ_j w_j λ_jⁿ`. -/
noncomputable def storeMoment (n : ℕ) : ℝ := ∑ j, w j * lam j ^ n

/-- The Hankel matrix `H₀ = [m_{a+b}]`. -/
noncomputable def storeH0 : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.of fun a b => storeMoment w lam ((a : ℕ) + b)

/-- The shifted Hankel matrix `H₁ = [m_{a+b+1}]`. -/
noncomputable def storeH1 : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.of fun a b => storeMoment w lam ((a : ℕ) + b + 1)

/-- Vandermonde factorization of `H₀`. -/
lemma storeH0_factor :
    storeH0 w lam
      = (Matrix.vandermonde lam)ᵀ * Matrix.diagonal w
        * Matrix.vandermonde lam := by
  rw [Matrix.mul_assoc]
  ext a b
  rw [Matrix.mul_apply, storeH0, Matrix.of_apply, storeMoment]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.transpose_apply, Matrix.diagonal_mul,
    Matrix.vandermonde_apply, Matrix.vandermonde_apply, pow_add]
  ring

/-- Vandermonde factorization of `H₁`. -/
lemma storeH1_factor :
    storeH1 w lam
      = (Matrix.vandermonde lam)ᵀ
        * Matrix.diagonal (fun j => w j * lam j)
        * Matrix.vandermonde lam := by
  rw [Matrix.mul_assoc]
  ext a b
  rw [Matrix.mul_apply, storeH1, Matrix.of_apply, storeMoment]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.transpose_apply, Matrix.diagonal_mul,
    Matrix.vandermonde_apply, Matrix.vandermonde_apply, pow_succ,
    pow_add]
  ring

/-- The Vandermonde determinant is nonzero for distinct nodes. -/
lemma vandermonde_det_ne_zero (hinj : Function.Injective lam) :
    (Matrix.vandermonde lam).det ≠ 0 := by
  rw [Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i < j := Finset.mem_Ioi.mp hj
  exact sub_ne_zero.mpr fun h => hij.ne' (hinj h)

/-- Distinct nodes make the Vandermonde action injective. -/
lemma vandermonde_mulVec_eq_zero (hinj : Function.Injective lam)
    {x : Fin s → ℝ} (hx : Matrix.vandermonde lam *ᵥ x = 0) :
    x = 0 := by
  have hunit : IsUnit (Matrix.vandermonde lam).det :=
    (vandermonde_det_ne_zero lam hinj).isUnit
  calc x = 1 *ᵥ x := (Matrix.one_mulVec x).symm
    _ = ((Matrix.vandermonde lam)⁻¹ * Matrix.vandermonde lam) *ᵥ x := by
        rw [Matrix.nonsing_inv_mul _ hunit]
    _ = (Matrix.vandermonde lam)⁻¹ *ᵥ (Matrix.vandermonde lam *ᵥ x) := by
        rw [← Matrix.mulVec_mulVec]
    _ = 0 := by rw [hx, Matrix.mulVec_zero]

/-- The Hankel quadratic form is a weighted sum of squares. -/
lemma hankel_quadratic (d x : Fin s → ℝ) :
    x ⬝ᵥ (((Matrix.vandermonde lam)ᵀ * Matrix.diagonal d
        * Matrix.vandermonde lam) *ᵥ x)
      = ∑ j, d j * (Matrix.vandermonde lam *ᵥ x) j ^ 2 := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    ← Matrix.mulVec_mulVec]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_diagonal]
  ring

/-- `H₀ ≻ 0`: the boxed positivity of the pencil base. -/
theorem storeH0_posDef (hw : ∀ j, 0 < w j)
    (hinj : Function.Injective lam) :
    (storeH0 w lam).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rw [Matrix.IsHermitian]
    ext a b
    simp only [Matrix.conjTranspose_apply, storeH0, Matrix.of_apply,
      star_trivial]
    rw [Nat.add_comm]
  · intro x hx
    rw [star_trivial, storeH0_factor, hankel_quadratic]
    have hp : Matrix.vandermonde lam *ᵥ x ≠ 0 := fun h =>
      hx (vandermonde_mulVec_eq_zero lam hinj h)
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hp
    refine Finset.sum_pos'
      (fun j _ => mul_nonneg (hw j).le (sq_nonneg _))
      ⟨j0, mem_univ j0, ?_⟩
    exact mul_pos (hw j0)
      ((sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hj0)))

/-- `H₁ ⪰ 0`: the boxed semidefiniteness of the shifted pencil. -/
theorem storeH1_posSemidef (hw : ∀ j, 0 ≤ w j)
    (hlam : ∀ j, 0 ≤ lam j) :
    (storeH1 w lam).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian]
    ext a b
    simp only [Matrix.conjTranspose_apply, storeH1, Matrix.of_apply,
      star_trivial]
    rw [Nat.add_comm (a : ℕ) b]
  · intro x
    rw [star_trivial, storeH1_factor, hankel_quadratic]
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hw j) (hlam j)) (sq_nonneg _)

/-! ### Generalized eigenpairs -/

/-- The generalized eigenvector `x_j = V⁻¹e_j`. -/
noncomputable def pencilVec (j : Fin s) : Fin s → ℝ :=
  (Matrix.vandermonde lam)⁻¹ *ᵥ Pi.single j 1

lemma vandermonde_pencilVec (hinj : Function.Injective lam)
    (j : Fin s) :
    Matrix.vandermonde lam *ᵥ pencilVec lam j = Pi.single j 1 := by
  rw [pencilVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (vandermonde_det_ne_zero lam hinj).isUnit,
    Matrix.one_mulVec]

lemma diagonal_mulVec_single (d : Fin s → ℝ) (j : Fin s) :
    Matrix.diagonal d *ᵥ Pi.single j 1 = d j • Pi.single j 1 := by
  funext i
  rw [Matrix.mulVec_diagonal, Pi.smul_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- `thm:store-frequency-pencil-master`, boxed pencil equation:
`H₁x_j = λ_jH₀x_j` with `x_j ≠ 0`. -/
theorem store_pencil_eigen (hinj : Function.Injective lam)
    (j : Fin s) :
    storeH1 w lam *ᵥ pencilVec lam j
      = lam j • (storeH0 w lam *ᵥ pencilVec lam j)
    ∧ pencilVec lam j ≠ 0 := by
  constructor
  · rw [storeH0_factor, storeH1_factor, Matrix.mul_assoc,
      Matrix.mul_assoc]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [vandermonde_pencilVec lam hinj j, diagonal_mulVec_single,
      diagonal_mulVec_single, Matrix.mulVec_smul,
      Matrix.mulVec_smul, smul_smul]
    congr 1
    ring
  · intro h
    have h1 := vandermonde_pencilVec lam hinj j
    rw [h, Matrix.mulVec_zero] at h1
    have h2 := congrFun h1 j
    simp at h2

/-- The generalized eigenvectors form a basis: linear
independence. -/
theorem store_pencil_independent (hinj : Function.Injective lam)
    (c : Fin s → ℝ) (hc : ∑ j, c j • pencilVec lam j = 0) :
    c = 0 := by
  have h := congrArg (fun v => Matrix.vandermonde lam *ᵥ v) hc
  simp only [Matrix.mulVec_zero] at h
  rw [Matrix.mulVec_sum] at h
  have hterm : ∀ j, Matrix.vandermonde lam *ᵥ (c j • pencilVec lam j)
      = Pi.single j (c j) := by
    intro j
    rw [Matrix.mulVec_smul, vandermonde_pencilVec lam hinj j]
    funext i
    rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply]
    by_cases hij : i = j <;> simp [hij]
  rw [Finset.sum_congr rfl fun j _ => hterm j] at h
  funext j
  have hj := congrFun h j
  rw [Finset.sum_apply] at hj
  rw [Finset.sum_eq_single j (fun i _ hij => by
      simp [Ne.symm hij])
    (fun hmem => absurd (mem_univ j) hmem)] at hj
  simpa using hj

/-! ### The monic annihilator and the moment recurrence -/

/-- The monic annihilator `q(t) = Π_j (t - λ_j)`. -/
noncomputable def storeAnnihilator : Polynomial ℝ :=
  ∏ j, (X - C (lam j))

lemma storeAnnihilator_monic : (storeAnnihilator lam).Monic :=
  monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (lam j)

lemma storeAnnihilator_natDegree :
    (storeAnnihilator lam).natDegree = s := by
  rw [storeAnnihilator,
    natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
  simp

lemma storeAnnihilator_eval_root (j : Fin s) :
    (storeAnnihilator lam).eval (lam j) = 0 := by
  rw [storeAnnihilator, eval_prod]
  exact Finset.prod_eq_zero (mem_univ j) (by simp)

/-- Monic expansion of the annihilator. -/
lemma storeAnnihilator_eval_expand (x : ℝ) :
    (storeAnnihilator lam).eval x
      = x ^ s + ∑ k : Fin s,
          (storeAnnihilator lam).coeff k * x ^ (k : ℕ) := by
  rw [eval_eq_sum_range, storeAnnihilator_natDegree,
    Finset.sum_range_succ]
  have hlead : (storeAnnihilator lam).coeff s = 1 := by
    have h := (storeAnnihilator_monic lam).coeff_natDegree
    rwa [storeAnnihilator_natDegree] at h
  rw [hlead, one_mul, ← Fin.sum_univ_eq_sum_range
    (fun i => (storeAnnihilator lam).coeff i * x ^ i)]
  ring

/-- `thm:store-frequency-pencil-master`, boxed recurrence:
`m_{n+s} + Σ_k q_k m_{n+k} = 0`. -/
theorem store_recurrence (n : ℕ) :
    storeMoment w lam (n + s)
      + ∑ k : Fin s, (storeAnnihilator lam).coeff k
          * storeMoment w lam (n + k) = 0 := by
  have hswap : ∑ k : Fin s, (storeAnnihilator lam).coeff k
      * storeMoment w lam (n + k)
      = ∑ j, ∑ k : Fin s, (storeAnnihilator lam).coeff k
          * (w j * lam j ^ (n + (k : ℕ))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [storeMoment, Finset.mul_sum]
  rw [storeMoment, hswap, ← Finset.sum_add_distrib]
  have hterm : ∀ j, w j * lam j ^ (n + s)
      + ∑ k : Fin s, (storeAnnihilator lam).coeff k
          * (w j * lam j ^ (n + (k : ℕ)))
      = w j * lam j ^ n * (storeAnnihilator lam).eval (lam j) := by
    intro j
    rw [storeAnnihilator_eval_expand, mul_add, Finset.mul_sum]
    congr 1
    · rw [pow_add]
      ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add]
      ring
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  rw [Finset.sum_congr rfl fun j _ => by
    rw [storeAnnihilator_eval_root lam j, mul_zero]]
  exact Finset.sum_const_zero

/-- `thm:store-frequency-pencil-master`, boxed annihilator system:
`H₀(q_0,…,q_{s-1})ᵀ = -(m_s,…,m_{2s-1})ᵀ`. -/
theorem store_annihilator_system :
    storeH0 w lam *ᵥ (fun k : Fin s => (storeAnnihilator lam).coeff k)
      = fun a : Fin s => -(storeMoment w lam ((a : ℕ) + s)) := by
  funext a
  have h := store_recurrence w lam (a : ℕ)
  simp only [Matrix.mulVec, dotProduct, storeH0, Matrix.of_apply]
  have h' : ∑ b : Fin s, storeMoment w lam ((a : ℕ) + b)
      * (storeAnnihilator lam).coeff b
      = ∑ k : Fin s, (storeAnnihilator lam).coeff k
        * storeMoment w lam ((a : ℕ) + k) :=
    Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [h']
  linarith

/-- The annihilator vector is the unique solution of the boxed
linear system. -/
theorem store_annihilator_unique (hw : ∀ j, 0 < w j)
    (hinj : Function.Injective lam) (q' : Fin s → ℝ)
    (hq' : storeH0 w lam *ᵥ q'
      = fun a : Fin s => -(storeMoment w lam ((a : ℕ) + s))) :
    q' = fun k : Fin s => (storeAnnihilator lam).coeff k := by
  have hdet : IsUnit (storeH0 w lam).det :=
    (storeH0_posDef w lam hw hinj).det_pos.ne'.isUnit
  have hsub : storeH0 w lam *ᵥ
      (q' - fun k : Fin s => (storeAnnihilator lam).coeff k) = 0 := by
    rw [Matrix.mulVec_sub, hq', store_annihilator_system]
    exact sub_self _
  have hzero : q' - (fun k : Fin s => (storeAnnihilator lam).coeff k) = 0 := by
    calc q' - (fun k : Fin s => (storeAnnihilator lam).coeff k)
        = 1 *ᵥ (q' - fun k : Fin s => (storeAnnihilator lam).coeff k) :=
          (Matrix.one_mulVec _).symm
      _ = ((storeH0 w lam)⁻¹ * storeH0 w lam) *ᵥ
          (q' - fun k : Fin s => (storeAnnihilator lam).coeff k) := by
          rw [Matrix.nonsing_inv_mul _ hdet]
      _ = (storeH0 w lam)⁻¹ *ᵥ (storeH0 w lam *ᵥ
          (q' - fun k : Fin s => (storeAnnihilator lam).coeff k)) := by
          rw [← Matrix.mulVec_mulVec]
      _ = 0 := by rw [hsub, Matrix.mulVec_zero]
  exact sub_eq_zero.mp hzero

/-- `thm:store-frequency-pencil-master`, boxed weight recovery:
`Vw = (m_0,…,m_{s-1})ᵀ` and `w = V⁻¹(m_0,…,m_{s-1})ᵀ` in the
convention `V_{aj} = λ_jᵃ`. -/
theorem store_weight_recovery (hinj : Function.Injective lam) :
    ((Matrix.vandermonde lam)ᵀ *ᵥ w
      = fun a : Fin s => storeMoment w lam (a : ℕ))
    ∧ (((Matrix.vandermonde lam)ᵀ)⁻¹ *ᵥ
        (fun a : Fin s => storeMoment w lam (a : ℕ)) = w) := by
  have h1 : (Matrix.vandermonde lam)ᵀ *ᵥ w
      = fun a : Fin s => storeMoment w lam (a : ℕ) := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.vandermonde, storeMoment, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨h1, ?_⟩
  rw [← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul,
    Matrix.one_mulVec]
  rw [Matrix.det_transpose]
  exact (vandermonde_det_ne_zero lam hinj).isUnit

end NCG
