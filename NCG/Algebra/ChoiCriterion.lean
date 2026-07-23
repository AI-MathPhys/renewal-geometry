/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.PrimitiveWeight

/-!
# The Choi criterion (`lem:choi`)

For a linear map `Φ : M_n(ℂ) → M_m(ℂ)`, define its Choi matrix on
product indices by `C_Φ (i,k) (j,l) = Φ(E_ij) k l`.  Then `Φ` is
completely positive — every identity-ampliation `id_{M_k} ⊗ Φ`
preserves positive semidefiniteness — **iff** `C_Φ ⪰ 0`
(`choi_criterion`).

* forward: `C_Φ` is the `n`-ampliation of `Φ` applied to the
  maximally entangled rank-one projector `Ω = v vᴴ`, `v(a,b) = δ_ab`;
* backward: a positive square root of `C_Φ` (from the functional
  calculus toolkit of `NCG/Upstream/PrimitiveWeight.lean`, after
  reindexing the product index to `Fin (n·m)`) yields an explicit
  Kraus decomposition `Φ(X) = Σ_α W_α X W_αᴴ`, whose ampliations
  `Σ_α (1 ⊗ W_α) X (1 ⊗ W_α)ᴴ` are manifestly positive.
-/

namespace NCG

open Matrix
open scoped ComplexOrder

variable {n m : ℕ}

/-- The **Choi matrix** of a linear map on matrix algebras:
`C_Φ (i,k) (j,l) = Φ(E_ij) k l`. -/
noncomputable def choiMatrix
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- The identity ampliation `id_{M_k} ⊗ Φ` on product indices. -/
noncomputable def ampliate (k : ℕ)
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin k × Fin m) (Fin k × Fin m) ℂ where
  toFun X := Matrix.of fun p q =>
    Φ (Matrix.of fun i j => X (p.1, i) (q.1, j)) p.2 q.2
  map_add' X Y := by
    ext ⟨p1, p2⟩ ⟨q1, q2⟩
    show Φ (Matrix.of fun i j => (X + Y) (p1, i) (q1, j)) p2 q2
      = Φ (Matrix.of fun i j => X (p1, i) (q1, j)) p2 q2
        + Φ (Matrix.of fun i j => Y (p1, i) (q1, j)) p2 q2
    have h1 : (Matrix.of fun i j => (X + Y) (p1, i) (q1, j))
        = (Matrix.of fun i j => X (p1, i) (q1, j))
          + Matrix.of fun i j => Y (p1, i) (q1, j) := by
      ext i j
      simp [Matrix.add_apply]
    rw [h1, map_add, Matrix.add_apply]
  map_smul' c X := by
    ext ⟨p1, p2⟩ ⟨q1, q2⟩
    show Φ (Matrix.of fun i j => (c • X) (p1, i) (q1, j)) p2 q2
      = (c • Φ (Matrix.of fun i j => X (p1, i) (q1, j))) p2 q2
    have h1 : (Matrix.of fun i j => (c • X) (p1, i) (q1, j))
        = c • Matrix.of fun i j => X (p1, i) (q1, j) := by
      ext i j
      simp [Matrix.smul_apply]
    rw [h1, map_smul]

/-- **Complete positivity** for maps of matrix algebras: every
identity ampliation preserves positive semidefiniteness. -/
def IsMatrixCompletelyPositive
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    Prop :=
  ∀ (k : ℕ) (X : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ),
    X.PosSemidef → (ampliate k Φ X).PosSemidef

/-- The maximally entangled projector
`Ω (a,b) (c,d) = δ_ab δ_cd`. -/
noncomputable def entangledProj (n : ℕ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  vecMulVec (fun p => if p.1 = p.2 then 1 else 0)
    (star fun p : Fin n × Fin n => if p.1 = p.2 then (1 : ℂ) else 0)

theorem entangledProj_posSemidef (n : ℕ) :
    (entangledProj n).PosSemidef :=
  posSemidef_vecMulVec_self_star _

/-- The Choi matrix is the `n`-ampliation at the entangled
projector. -/
theorem choiMatrix_eq_ampliate
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    choiMatrix Φ = ampliate n Φ (entangledProj n) := by
  ext ⟨a, k⟩ ⟨c, l⟩
  show Φ (Matrix.single a c 1) k l
    = Φ (Matrix.of fun i j => entangledProj n (a, i) (c, j)) k l
  have harg : (Matrix.single a c (1 : ℂ))
      = Matrix.of fun i j => entangledProj n (a, i) (c, j) := by
    ext i j
    simp only [Matrix.of_apply, entangledProj, vecMulVec_apply,
      Pi.star_apply, Matrix.single_apply]
    rcases eq_or_ne a i with rfl | hai
    · rcases eq_or_ne c j with rfl | hcj
      · simp
      · simp [hcj]
    · simp [hai]
  rw [harg]

/-- Forward direction: complete positivity forces `C_Φ ⪰ 0`. -/
theorem choiMatrix_posSemidef_of_cp
    {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ}
    (h : IsMatrixCompletelyPositive Φ) : (choiMatrix Φ).PosSemidef := by
  rw [choiMatrix_eq_ampliate]
  exact h n (entangledProj n) (entangledProj_posSemidef n)

/-- Collapsing a product-indexed sum whose off-block terms vanish. -/
theorem sum_prod_collapse {β : Type*} [AddCommMonoid β] {k₀ : ℕ}
    {J : Type*} [Fintype J] (p : Fin k₀) (g : Fin k₀ → J → β)
    (h : ∀ c, c ≠ p → ∀ j, g c j = 0) :
    (∑ c : Fin k₀, ∑ j : J, g c j) = ∑ j : J, g p j := by
  rw [Finset.sum_eq_single p]
  · intro c _ hcp
    exact Finset.sum_eq_zero fun j _ => h c hcp j
  · intro habs
    exact absurd (Finset.mem_univ p) habs

/-- Backward direction: a positive Choi matrix yields an explicit
Kraus decomposition, hence complete positivity. -/
theorem cp_of_choiMatrix_posSemidef
    {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ}
    (hC : (choiMatrix Φ).PosSemidef) : IsMatrixCompletelyPositive Φ := by
  classical
  set e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv with he
  set C' : Matrix (Fin (n * m)) (Fin (n * m)) ℂ :=
    (choiMatrix Φ).submatrix e.symm e.symm with hC'def
  have hC' : C'.PosSemidef :=
    (Matrix.posSemidef_submatrix_equiv e.symm).mpr hC
  set S : Matrix (Fin (n * m)) (Fin (n * m)) ℂ :=
    hC'.1.cfc Real.sqrt with hSdef
  have hSS : S * S = C' := by
    rw [hSdef, Upstream.PrimitiveWeight.cfc_mul]
    have h1 : hC'.1.cfc (fun x => Real.sqrt x * Real.sqrt x)
        = hC'.1.cfc id :=
      Upstream.PrimitiveWeight.cfc_congr hC'.1 fun i =>
        Real.mul_self_sqrt (hC'.eigenvalues_nonneg i)
    rw [h1, Upstream.PrimitiveWeight.cfc_id']
  have hSherm : S.IsHermitian :=
    Upstream.PrimitiveWeight.cfc_isHermitian hC'.1 _
  -- the Kraus operators
  set W : Fin (n * m) → Matrix (Fin m) (Fin n) ℂ :=
    fun α => Matrix.of fun k i => star (S α (e (i, k))) with hW
  -- Choi entries through the square root
  have hCdecomp : ∀ (i j : Fin n) (k l : Fin m),
      Φ (Matrix.single i j 1) k l
        = ∑ α, W α k i * star (W α l j) := by
    intro i j k l
    have h3 : Φ (Matrix.single i j 1) k l
        = C' (e (i, k)) (e (j, l)) := by
      rw [hC'def]
      simp [Matrix.submatrix_apply, choiMatrix]
    have h4 : C' (e (i, k)) (e (j, l))
        = ∑ α, S (e (i, k)) α * S α (e (j, l)) := by
      rw [← hSS, Matrix.mul_apply]
    rw [h3, h4]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h5 : S (e (i, k)) α = star (S α (e (i, k))) := by
      have h6 := congrFun (congrFun hSherm.eq (e (i, k))) α
      rw [Matrix.conjTranspose_apply] at h6
      exact h6.symm
    rw [h5]
    simp only [hW, Matrix.of_apply, star_star]
  -- the map in Kraus form
  have hKraus : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      Φ X = ∑ α, W α * X * (W α)ᴴ := by
    intro X
    ext k l
    have hL : Φ X k l
        = ∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) k l := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      rw [map_sum, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show Matrix.single i j (X i j)
          = X i j • Matrix.single i j (1 : ℂ) from by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]]
      rw [map_smul, Matrix.smul_apply, smul_eq_mul]
    have hL2 : (∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) k l)
        = ∑ i, ∑ j, ∑ α, W α k i * X i j * star (W α l j) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hCdecomp i j k l, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      ring
    have hswap : (∑ i, ∑ j, ∑ α, W α k i * X i j * star (W α l j))
        = ∑ α, ∑ i, ∑ j, W α k i * X i j * star (W α l j) := by
      rw [show (∑ i, ∑ j, ∑ α : Fin (n * m),
          W α k i * X i j * star (W α l j))
          = ∑ i, ∑ α : Fin (n * m), ∑ j,
            W α k i * X i j * star (W α l j) from
        Finset.sum_congr rfl fun i _ => Finset.sum_comm]
      exact Finset.sum_comm
    have hR : (∑ α, W α * X * (W α)ᴴ) k l
        = ∑ α, ∑ i, ∑ j, W α k i * X i j * star (W α l j) := by
      rw [Matrix.sum_apply]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Matrix.mul_apply]
      have h9 : ∀ b, (W α * X) k b * (W α)ᴴ b l
          = ∑ i, W α k i * X i b * star (W α l b) := by
        intro b
        rw [Matrix.mul_apply, Matrix.conjTranspose_apply,
          Finset.sum_mul]
      rw [Finset.sum_congr rfl fun b _ => h9 b]
      exact Finset.sum_comm
    rw [hL, hL2, hswap, hR]
  -- Kraus form of the ampliation
  intro k₀ X hX
  set Wk : Fin (n * m) →
      Matrix (Fin k₀ × Fin m) (Fin k₀ × Fin n) ℂ :=
    fun α => Matrix.of fun p q =>
      if p.1 = q.1 then W α p.2 q.2 else 0 with hWk
  have hper : ∀ (p q : Fin k₀) (k : Fin m) (l : Fin m)
      (α : Fin (n * m)),
      (W α * (Matrix.of fun i j => X (p, i) (q, j)) * (W α)ᴴ) k l
        = (Wk α * X * (Wk α)ᴴ) (p, k) (q, l) := by
    intro p q k l α
    have hLHS : (W α * (Matrix.of fun i j => X (p, i) (q, j))
        * (W α)ᴴ) k l
        = ∑ b, ∑ i, W α k i * X (p, i) (q, b) * star (W α l b) := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_apply, Matrix.conjTranspose_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.of_apply]
    have hRHS : (Wk α * X * (Wk α)ᴴ) (p, k) (q, l)
        = ∑ b, ∑ i, W α k i * X (p, i) (q, b) * star (W α l b) := by
      have hz1 : ∀ c, c ≠ q → ∀ b : Fin n,
          (Wk α * X) (p, k) (c, b) * (Wk α)ᴴ (c, b) (q, l) = 0 := by
        intro c hcq b
        have h1 : (Wk α)ᴴ (c, b) (q, l) = 0 := by
          rw [Matrix.conjTranspose_apply]
          have h2 : Wk α (q, l) (c, b) = 0 := by
            simp only [hWk, Matrix.of_apply]
            rw [if_neg (fun h => hcq h.symm)]
          rw [h2, star_zero]
        rw [h1, mul_zero]
      rw [Matrix.mul_apply, Fintype.sum_prod_type,
        sum_prod_collapse q _ hz1]
      refine Finset.sum_congr rfl fun b _ => ?_
      have h1 : (Wk α)ᴴ (q, b) (q, l) = star (W α l b) := by
        rw [Matrix.conjTranspose_apply]
        simp [hWk]
      have h2 : (Wk α * X) (p, k) (q, b)
          = ∑ i, W α k i * X (p, i) (q, b) := by
        have hz2 : ∀ c, c ≠ p → ∀ i : Fin n,
            Wk α (p, k) (c, i) * X (c, i) (q, b) = 0 := by
          intro c hcp i
          have h3 : Wk α (p, k) (c, i) = 0 := by
            simp only [hWk, Matrix.of_apply]
            rw [if_neg (fun h => hcp h.symm)]
          rw [h3, zero_mul]
        rw [Matrix.mul_apply, Fintype.sum_prod_type,
          sum_prod_collapse p _ hz2]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [hWk]
      rw [h1, h2, Finset.sum_mul]
    rw [hLHS, hRHS]
  have hampl : ampliate k₀ Φ X = ∑ α, Wk α * X * (Wk α)ᴴ := by
    ext ⟨p, k⟩ ⟨q, l⟩
    show Φ (Matrix.of fun i j => X (p, i) (q, j)) k l = _
    rw [hKraus, Matrix.sum_apply, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun α _ => hper p q k l α
  rw [hampl]
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb)
    PosSemidef.zero ?_
  intro α _
  exact hX.mul_mul_conjTranspose_same (Wk α)

/-- **Lemma `lem:choi` (the Choi criterion)**: a linear map of matrix
algebras is completely positive iff its Choi matrix is positive
semidefinite. -/
theorem choi_criterion
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    IsMatrixCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef :=
  ⟨choiMatrix_posSemidef_of_cp, cp_of_choiMatrix_posSemidef⟩

end NCG
