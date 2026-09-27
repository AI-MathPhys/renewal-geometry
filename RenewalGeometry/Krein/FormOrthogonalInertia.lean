/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.PontryaginRationalRealization
import RenewalGeometry.Krein.SignedHaynsworthInertia

/-!
# Inertia of a Pontryagin form on orthogonal decompositions

Infrastructure for `thm:supp-pole-Hankel` (P2)–(P4) of `papers/predictive_spectral_geometry`.
For a finite Pontryagin realization `P` (indefinite form `[x, y] = ⟪x, J y⟫` on `N`) and a
subspace `W ≤ N`, `P.subNegIndex W` / `P.subPosIndex W` are the negative / positive indices of the
form restricted to `W`.

* `subNegIndex_eq_negInertia_gram`: the negative index of the restricted form is the negative
  inertia of the Gram matrix `[x_i, x_j]` of any finite spanning family of `W` (this is (P2): the
  local inertia at a pole is the inertia of the principal-part Hankel Gram, once the local Krylov
  family is known to span the root subspace).
* `subNegIndex_add_subPosIndex_eq_finrank`: **Sylvester's count** `neg + pos = dim W` when the
  form is nondegenerate on `W`.
* `neutral_pair`: if `W = V ⊔ V'` with `V`, `V'` neutral and the form nondegenerate on `W`, then
  `dim V = dim V'` and `neg = pos = dim V` (this is (P3): a nonreal conjugate pole pair contributes
  its local McMillan degree equally to the positive and negative index).
* `subNegIndex_sup_of_orthogonal`, `subNegIndex_finset_sup_of_orthogonal`: **additivity** of the
  negative index over form-orthogonal decompositions (this is (P4)).
-/

open scoped InnerProductSpace InnerProduct
open Module Matrix

noncomputable section

namespace RenewalGeometry

/-! ## The positive index -/

section PosIndex

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

/-- The positive index of a form: the negative index of `-B`. -/
def posIndex (B : N → N → ℂ) : ℕ := negIndex fun x y => -B x y

/-- The negative index of a form pulled back along a linear map, for the negated form. -/
theorem pullbackForm_neg {W : Type*} [AddCommGroup W] [Module ℂ W] (B : N → N → ℂ)
    (f : W →ₗ[ℂ] N) :
    pullbackForm (fun x y => -B x y) f = fun x y => -pullbackForm B f x y := rfl

end PosIndex

/-! ## Inertia of a matrix: Sylvester's count for invertible Hermitian matrices -/

section Sylvester

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `posInertia G = #{positive eigenvalues}` for a Hermitian `G`. -/
theorem posInertia_eq_card_pos_eigenvalues (G : Matrix ι ι ℂ) (hG : G.IsHermitian) :
    posInertia G = (Finset.univ.filter fun j => 0 < hG.eigenvalues j).card := by
  have horth : ∀ i j, star ⇑(hG.eigenvectorBasis i) ⬝ᵥ ⇑(hG.eigenvectorBasis j) =
      if i = j then 1 else 0 := by
    intro i j
    have hU := Unitary.coe_star_mul_self hG.eigenvectorUnitary
    have := congrFun (congrFun hU i) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at this
    rw [← this]
    simp only [dotProduct, Pi.star_apply, Matrix.IsHermitian.eigenvectorUnitary_apply]
  have heig : ∀ j, G *ᵥ ⇑(hG.eigenvectorBasis j) =
      ((hG.eigenvalues j : ℂ)) • ⇑(hG.eigenvectorBasis j) := by
    intro j
    rw [hG.mulVec_eigenvectorBasis]
    funext k
    simp [Complex.real_smul]
  exact posInertia_eq_card_of_eigenbasis G hG.eigenvalues (fun i => ⇑(hG.eigenvectorBasis i))
    horth heig

/-- `negInertia G = #{negative eigenvalues}` for a Hermitian `G`. -/
theorem negInertia_eq_card_neg_eigenvalues (G : Matrix ι ι ℂ) (hG : G.IsHermitian) :
    negInertia G = (Finset.univ.filter fun j => hG.eigenvalues j < 0).card := by
  have horth : ∀ i j, star ⇑(hG.eigenvectorBasis i) ⬝ᵥ ⇑(hG.eigenvectorBasis j) =
      if i = j then 1 else 0 := by
    intro i j
    have hU := Unitary.coe_star_mul_self hG.eigenvectorUnitary
    have := congrFun (congrFun hU i) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at this
    rw [← this]
    simp only [dotProduct, Pi.star_apply, Matrix.IsHermitian.eigenvectorUnitary_apply]
  have heig : ∀ j, (-G) *ᵥ ⇑(hG.eigenvectorBasis j) =
      ((-hG.eigenvalues j : ℝ) : ℂ) • ⇑(hG.eigenvectorBasis j) := by
    intro j
    rw [Matrix.neg_mulVec, hG.mulVec_eigenvectorBasis]
    funext k
    simp [Complex.real_smul]
  rw [negInertia, posInertia_eq_card_of_eigenbasis (-G) (fun j => -hG.eigenvalues j)
    (fun i => ⇑(hG.eigenvectorBasis i)) horth heig]
  congr 1
  ext j
  simp

/-- **Sylvester's count**: an invertible Hermitian matrix has `pos + neg = n`. -/
theorem posInertia_add_negInertia_eq_card (G : Matrix ι ι ℂ) (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) : posInertia G + negInertia G = Fintype.card ι := by
  rw [posInertia_eq_card_pos_eigenvalues G hG, negInertia_eq_card_neg_eigenvalues G hG]
  have hne : ∀ j, hG.eigenvalues j ≠ 0 := by
    intro j hj
    apply hdet
    rw [hG.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  have hcongr : (Finset.univ.filter fun j => hG.eigenvalues j < 0) =
      Finset.univ.filter fun j => ¬ 0 < hG.eigenvalues j := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (hne j)⟩
  rw [hcongr, Finset.card_filter_add_card_filter_not, Finset.card_univ]

/-- `negInertia` is additive on Hermitian block-diagonal matrices. -/
theorem negInertia_fromBlocks_diag {p q : Type} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] (A : Matrix p p ℂ) (D : Matrix q q ℂ) (hA : A.IsHermitian)
    (hD : D.IsHermitian) : negInertia (fromBlocks A 0 0 D) = negInertia A + negInertia D := by
  unfold negInertia
  simp only [Matrix.fromBlocks_neg, neg_zero]
  exact posInertia_fromBlocks_diag (-A) (-D) hA.neg hD.neg

end Sylvester

namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (P : PontryaginRealization H N)

/-! ## Indices of the form restricted to a subspace -/

/-- The negative index of the Pontryagin form restricted to `W`. -/
def subNegIndex (W : Submodule ℂ N) : ℕ := negIndex (pullbackForm P.form W.subtype)

/-- The positive index of the Pontryagin form restricted to `W`. -/
def subPosIndex (W : Submodule ℂ N) : ℕ := posIndex (pullbackForm P.form W.subtype)

/-- The Gram matrix `[x_i, x_j]` of a finite family. -/
def gram {ι : Type} [Fintype ι] (x : ι → N) : Matrix ι ι ℂ := Matrix.of fun i j => P.form (x i) (x j)

theorem gram_isHermitian {ι : Type} [Fintype ι] (x : ι → N) : (P.gram x).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [gram, Matrix.of_apply, Complex.star_def]
  rw [P.form_conj_symm (x i) (x j)]
  exact Complex.conj_conj _

theorem range_combinationMap {ι : Type} [Fintype ι] (x : ι → N) :
    LinearMap.range (combinationMap x) = Submodule.span ℂ (Set.range x) :=
  Fintype.range_linearCombination ℂ x

variable [FiniteDimensional ℂ N]

/-- The negative index of the restricted form is the negative index of the pullback along any
linear map onto `W`. -/
theorem subNegIndex_eq_negIndex_pullback {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (W : Submodule ℂ N) (f : V →ₗ[ℂ] N) (hf : LinearMap.range f = W) :
    P.subNegIndex W = negIndex (pullbackForm P.form f) := by
  have hmem : ∀ v, f v ∈ W := fun v => hf ▸ LinearMap.mem_range_self f v
  set g : V →ₗ[ℂ] W := f.codRestrict W hmem with hg
  have hgsurj : LinearMap.range g = ⊤ := by
    rw [LinearMap.range_codRestrict, hf]
    exact Submodule.comap_subtype_self W
  have hcomp : f = W.subtype ∘ₗ g := by
    ext v
    rfl
  have h0 : pullbackForm P.form W.subtype 0 0 = 0 := by
    simp [pullbackForm]
  rw [subNegIndex, ← negIndex_pullback_eq_of_surjective _ h0 g hgsurj, hcomp]
  rfl

/-- **The negative index of the restricted form is the negative inertia of the Gram matrix of any
finite spanning family** (`thm:supp-pole-Hankel`, (P2) mechanism). -/
theorem subNegIndex_eq_negInertia_gram {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → N)
    (W : Submodule ℂ N) (hx : Submodule.span ℂ (Set.range x) = W) :
    P.subNegIndex W = negInertia (P.gram x) := by
  rw [P.subNegIndex_eq_negIndex_pullback W (combinationMap x) (by rw [range_combinationMap, hx])]
  exact (P.negInertia_gram_eq_negIndex_pullback x).symm

/-- The positive counterpart: `posIndex` of the restricted form is `posInertia` of the Gram. -/
theorem subPosIndex_eq_posInertia_gram {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → N)
    (W : Submodule ℂ N) (hx : Submodule.span ℂ (Set.range x) = W) :
    P.subPosIndex W = posInertia (P.gram x) := by
  have hmem : ∀ v, combinationMap x v ∈ W := fun v =>
    hx ▸ (range_combinationMap x) ▸ LinearMap.mem_range_self _ v
  set g : (ι → ℂ) →ₗ[ℂ] W := (combinationMap x).codRestrict W hmem with hg
  have hgsurj : LinearMap.range g = ⊤ := by
    rw [LinearMap.range_codRestrict, range_combinationMap, hx]
    exact Submodule.comap_subtype_self W
  have hcomp : combinationMap x = W.subtype ∘ₗ g := by
    ext v
    rfl
  have h0 : (fun a b => -pullbackForm P.form W.subtype a b) 0 0 = 0 := by
    simp [pullbackForm]
  have key : posIndex (pullbackForm P.form W.subtype) =
      negIndex (pullbackForm (fun a b => -P.form a b) (combinationMap x)) := by
    rw [posIndex, ← negIndex_pullback_eq_of_surjective _ h0 g hgsurj, hcomp]
    rfl
  rw [subPosIndex, key, ← neg_neg (P.gram x), ← negInertia, negInertia_eq_negIndex]
  congr 1
  funext c d
  rw [pullbackForm, form_combination]
  change -(star c ⬝ᵥ (P.gram x *ᵥ d)) = star c ⬝ᵥ ((-P.gram x) *ᵥ d)
  rw [Matrix.neg_mulVec, dotProduct_neg]

/-! ## Sylvester's count for a nondegenerate restriction -/

/-- The form is nondegenerate on `W`: every vector of `W` orthogonal to all of `W` is zero. -/
def IsNondegenerateOn (W : Submodule ℂ N) : Prop :=
  ∀ y ∈ W, (∀ x ∈ W, P.form x y = 0) → y = 0

/-- The vectors orthogonal to a set on the left form a submodule. -/
def leftOrthogonal (S : Set N) : Submodule ℂ N where
  carrier := {y | ∀ x ∈ S, P.form x y = 0}
  add_mem' := fun {a b} ha hb x hx => by rw [form_add_right, ha x hx, hb x hx, add_zero]
  zero_mem' := fun x _ => form_zero_right P x
  smul_mem' := fun c {y} hy x hx => by rw [form_smul_right, hy x hx, mul_zero]

theorem mem_leftOrthogonal (S : Set N) (y : N) : y ∈ P.leftOrthogonal S ↔ ∀ x ∈ S, P.form x y = 0 :=
  Iff.rfl

/-- The vectors orthogonal to a set on the right form a submodule. -/
def rightOrthogonal (S : Set N) : Submodule ℂ N where
  carrier := {x | ∀ y ∈ S, P.form x y = 0}
  add_mem' := fun {a b} ha hb y hy => by rw [form_add_left, ha y hy, hb y hy, add_zero]
  zero_mem' := fun y _ => form_zero_left P y
  smul_mem' := fun c {x} hx y hy => by rw [form_smul_left, hx y hy, mul_zero]

theorem mem_rightOrthogonal (S : Set N) (x : N) :
    x ∈ P.rightOrthogonal S ↔ ∀ y ∈ S, P.form x y = 0 :=
  Iff.rfl

/-- The Gram matrix of a basis of `W` is invertible when the form is nondegenerate on `W`. -/
theorem det_gram_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (W : Submodule ℂ N)
    (hW : P.IsNondegenerateOn W) (e : Basis ι ℂ W) :
    (P.gram fun i => (e i : N)).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set y : N := ∑ j, c j • (e j : N) with hy
  have hyW : y ∈ W := Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (e j).2
  have horth : ∀ x ∈ W, P.form x y = 0 := by
    intro x hx
    have hspan : x ∈ Submodule.span ℂ (Set.range fun i => (e i : N)) := by
      have : Submodule.span ℂ (Set.range fun i => (e i : N)) = W := by
        rw [show (Set.range fun i => (e i : N)) = W.subtype '' Set.range e by
          rw [← Set.range_comp]; rfl]
        rw [← Submodule.map_span, e.span_eq, Submodule.map_subtype_top]
      rw [this]; exact hx
    have hK : Submodule.span ℂ (Set.range fun i => (e i : N)) ≤ P.rightOrthogonal {y} := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩ y' hy'
      rw [Set.mem_singleton_iff] at hy'
      subst hy'
      rw [hy, form_sum_right]
      have := congrFun hc i
      simp only [Matrix.mulVec, dotProduct, gram, Matrix.of_apply, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [form_smul_right, mul_comm]
    exact hK hspan y (Set.mem_singleton y)
  have hy0 : y = 0 := hW y hyW horth
  apply hc0
  have hli := e.linearIndependent
  have : ∑ j, c j • e j = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
    exact hy0
  exact (Fintype.linearIndependent_iff.mp hli c this) |> funext

/-- **Sylvester's count** for a nondegenerate restriction: `neg + pos = dim W`. -/
theorem subNegIndex_add_subPosIndex_eq_finrank (W : Submodule ℂ N) (hW : P.IsNondegenerateOn W) :
    P.subNegIndex W + P.subPosIndex W = finrank ℂ W := by
  classical
  let e := Module.finBasis ℂ W
  set x : Fin (finrank ℂ W) → N := fun i => (e i : N) with hx
  have hspan : Submodule.span ℂ (Set.range x) = W := by
    rw [show Set.range x = W.subtype '' Set.range e by rw [← Set.range_comp]; rfl]
    rw [← Submodule.map_span, e.span_eq, Submodule.map_subtype_top]
  rw [P.subNegIndex_eq_negInertia_gram x W hspan, P.subPosIndex_eq_posInertia_gram x W hspan,
    add_comm, posInertia_add_negInertia_eq_card _ (P.gram_isHermitian x)
    (P.det_gram_ne_zero W hW e), Fintype.card_fin]

/-! ## Neutral subspaces and negative subspaces meet trivially -/

/-- A subspace of `W` on which the form is definite (in the sense of a fixed sign predicate)
meets a neutral subspace trivially: the dimension count. -/
theorem finrank_add_finrank_le_of_neutral (B : N → N → ℂ) (W V : Submodule ℂ N) (hVW : V ≤ W)
    (hV : ∀ x ∈ V, B x x = 0) (U : Submodule ℂ W)
    (hU : ∀ u ∈ U, u ≠ 0 → (pullbackForm B W.subtype u u).re < 0) :
    finrank ℂ U + finrank ℂ V ≤ finrank ℂ W := by
  set U' : Submodule ℂ N := U.map W.subtype with hU'
  have hfin : finrank ℂ U' = finrank ℂ U := Submodule.finrank_map_subtype_eq W U
  have hU'W : U' ≤ W := Submodule.map_subtype_le W U
  have hinf : U' ⊓ V = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hzU', hzV⟩ := Submodule.mem_inf.mp hz
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hzU'
    by_contra hne
    have hu0 : u ≠ 0 := fun h => hne (by rw [h, map_zero])
    have h1 := hU u hu hu0
    have h2 := hV _ hzV
    simp only [pullbackForm] at h1
    rw [h2] at h1
    simp at h1
  have := Submodule.finrank_sup_add_finrank_inf_eq U' V
  rw [hinf, finrank_bot, add_zero, hfin] at this
  rw [← this]
  exact Submodule.finrank_mono (sup_le hU'W hVW)

/-- `neg(W) + dim V ≤ dim W` for a neutral `V ≤ W`. -/
theorem subNegIndex_add_finrank_le_of_neutral (W V : Submodule ℂ N) (hVW : V ≤ W)
    (hV : ∀ x ∈ V, P.form x x = 0) : P.subNegIndex W + finrank ℂ V ≤ finrank ℂ W := by
  have : P.subNegIndex W ≤ finrank ℂ W - finrank ℂ V := by
    refine negIndex_le fun U hU => ?_
    have := finrank_add_finrank_le_of_neutral P.form W V hVW hV U hU
    omega
  have h2 : finrank ℂ V ≤ finrank ℂ W := Submodule.finrank_mono hVW
  omega

/-- `pos(W) + dim V ≤ dim W` for a neutral `V ≤ W`. -/
theorem subPosIndex_add_finrank_le_of_neutral (W V : Submodule ℂ N) (hVW : V ≤ W)
    (hV : ∀ x ∈ V, P.form x x = 0) : P.subPosIndex W + finrank ℂ V ≤ finrank ℂ W := by
  have : P.subPosIndex W ≤ finrank ℂ W - finrank ℂ V := by
    refine negIndex_le fun U hU => ?_
    have := finrank_add_finrank_le_of_neutral (fun a b => -P.form a b) W V hVW
      (fun x hx => by rw [hV x hx, neg_zero]) U hU
    omega
  have h2 : finrank ℂ V ≤ finrank ℂ W := Submodule.finrank_mono hVW
  omega

/-- **Neutral pairs** (`thm:supp-pole-Hankel`, (P3)): if `W = V ⊔ V'` with `V`, `V'` neutral and the
form nondegenerate on `W`, then `dim V = dim V'` and `neg(W) = pos(W) = dim V`. -/
theorem neutral_pair (V V' : Submodule ℂ N) (hdisj : V ⊓ V' = ⊥)
    (hV : ∀ x ∈ V, P.form x x = 0) (hV' : ∀ x ∈ V', P.form x x = 0)
    (hnd : P.IsNondegenerateOn (V ⊔ V')) :
    finrank ℂ V = finrank ℂ V' ∧ P.subNegIndex (V ⊔ V') = finrank ℂ V ∧
      P.subPosIndex (V ⊔ V') = finrank ℂ V := by
  have hdim : finrank ℂ (V ⊔ V' : Submodule ℂ N) = finrank ℂ V + finrank ℂ V' := by
    have := Submodule.finrank_sup_add_finrank_inf_eq V V'
    rw [hdisj, finrank_bot, add_zero] at this
    exact this
  have h1 := P.subNegIndex_add_finrank_le_of_neutral (V ⊔ V') V le_sup_left hV
  have h2 := P.subNegIndex_add_finrank_le_of_neutral (V ⊔ V') V' le_sup_right hV'
  have h3 := P.subPosIndex_add_finrank_le_of_neutral (V ⊔ V') V le_sup_left hV
  have h4 := P.subPosIndex_add_finrank_le_of_neutral (V ⊔ V') V' le_sup_right hV'
  have h5 := P.subNegIndex_add_subPosIndex_eq_finrank (V ⊔ V') hnd
  omega

/-! ## Additivity over orthogonal decompositions -/

omit [FiniteDimensional ℂ N] in
/-- The Gram matrix of a concatenated family of mutually orthogonal families is block diagonal. -/
theorem gram_sum_elim {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (x₁ : ι₁ → N) (x₂ : ι₂ → N)
    (horth : ∀ i j, P.form (x₁ i) (x₂ j) = 0) :
    P.gram (Sum.elim x₁ x₂) = fromBlocks (P.gram x₁) 0 0 (P.gram x₂) := by
  ext (i | i) (j | j)
  · rfl
  · simp [gram, horth]
  · simp only [gram, Matrix.of_apply, Sum.elim_inr, Sum.elim_inl, fromBlocks_apply₂₁,
      Matrix.zero_apply]
    rw [form_conj_symm, horth, map_zero]
  · rfl

/-- **Two-summand additivity** (`thm:supp-pole-Hankel`, (P4) mechanism): the negative index of the
form on `W₁ ⊔ W₂` is the sum of the negative indices when `W₁ ⊥ W₂`. -/
theorem subNegIndex_sup_of_orthogonal (W₁ W₂ : Submodule ℂ N)
    (horth : ∀ x ∈ W₁, ∀ y ∈ W₂, P.form x y = 0) :
    P.subNegIndex (W₁ ⊔ W₂) = P.subNegIndex W₁ + P.subNegIndex W₂ := by
  classical
  let e₁ := Module.finBasis ℂ W₁
  let e₂ := Module.finBasis ℂ W₂
  set x₁ : Fin (finrank ℂ W₁) → N := fun i => (e₁ i : N) with hx₁
  set x₂ : Fin (finrank ℂ W₂) → N := fun i => (e₂ i : N) with hx₂
  have hspan₁ : Submodule.span ℂ (Set.range x₁) = W₁ := by
    rw [show Set.range x₁ = W₁.subtype '' Set.range e₁ by rw [← Set.range_comp]; rfl]
    rw [← Submodule.map_span, e₁.span_eq, Submodule.map_subtype_top]
  have hspan₂ : Submodule.span ℂ (Set.range x₂) = W₂ := by
    rw [show Set.range x₂ = W₂.subtype '' Set.range e₂ by rw [← Set.range_comp]; rfl]
    rw [← Submodule.map_span, e₂.span_eq, Submodule.map_subtype_top]
  have hspan : Submodule.span ℂ (Set.range (Sum.elim x₁ x₂)) = W₁ ⊔ W₂ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hspan₁, hspan₂]
  have horth' : ∀ i j, P.form (x₁ i) (x₂ j) = 0 := fun i j => horth _ (e₁ i).2 _ (e₂ j).2
  rw [P.subNegIndex_eq_negInertia_gram (Sum.elim x₁ x₂) _ hspan,
    P.subNegIndex_eq_negInertia_gram x₁ W₁ hspan₁, P.subNegIndex_eq_negInertia_gram x₂ W₂ hspan₂,
    P.gram_sum_elim x₁ x₂ horth',
    negInertia_fromBlocks_diag _ _ (P.gram_isHermitian x₁) (P.gram_isHermitian x₂)]

omit [FiniteDimensional ℂ N] in
theorem subNegIndex_bot : P.subNegIndex ⊥ = 0 := by
  have := negIndex_le_finrank (pullbackForm P.form (⊥ : Submodule ℂ N).subtype)
  rw [finrank_bot] at this
  exact Nat.le_zero.mp this

/-- **Finite additivity** (`thm:supp-pole-Hankel`, (P4)): the negative index on the sup of a finite
family of pairwise form-orthogonal subspaces is the sum of the negative indices. -/
theorem subNegIndex_finset_sup_of_orthogonal {ι : Type*} (W : ι → Submodule ℂ N)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j, P.form x y = 0) (s : Finset ι) :
    P.subNegIndex (s.sup W) = ∑ i ∈ s, P.subNegIndex (W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [subNegIndex_bot]
  | insert a s ha ih =>
      rw [Finset.sup_insert, Finset.sum_insert ha, ← ih]
      refine P.subNegIndex_sup_of_orthogonal (W a) (s.sup W) fun x hx y hy => ?_
      have hK : s.sup W ≤ P.leftOrthogonal (W a) := by
        refine Finset.sup_le fun i hi => ?_
        intro z hz x' hx'
        exact horth a i (fun h => ha (h ▸ hi)) x' hx' z hz
      exact hK hy x hx

end PontryaginRealization

end RenewalGeometry

end
