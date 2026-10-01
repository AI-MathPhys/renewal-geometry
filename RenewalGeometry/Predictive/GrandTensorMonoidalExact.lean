/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.DerivedPredictiveCarrierUniversalExact

/-!
# Tensorial covariance and independent composition of the Grand Tensor
(`prop:supp-grand-monoidal`, emergent-spacetime manuscript)

* `GrandTensorMonoidal.gram_coordinate_change` — under `c = C c̃` the word-Gram quadratic
  form transforms by `K̃ = Cᴴ K C`.
* `GrandTensorMonoidal.regTrace` — the normalized regular trace
  `τ̂_reg(a) = Tr(L_a)/dim A` (`eq:supp-regular-trace`) of a finite-dimensional algebra;
  `regTrace_algEquiv`: invariant under algebra isomorphisms;
  `regTrace_tmul`: multiplicative on tensor products, `τ̂(a ⊗ b) = τ̂(a) τ̂(b)`.
* `GrandTensorMonoidal.wordGram` — the word-Gram matrix `K(v,w) = τ̂([v]^*[w])`
  (`eq:supp-word-gram`) of a represented word family;
  `wordGram_starAlgEquiv`: a `*`-isomorphism carrying represented words to represented words
  preserves all word moments; `wordGram_tensor`: on a rectangular bank of independent word
  pairs, `K₁₂((v₁,v₂),(w₁,w₂)) = K₁(v₁,w₁) K₂(v₂,w₂)` (`eq:supp-grand-gram-product`), i.e.
  `K₁₂ = K₁ ⊗ₖ K₂`; `wordGram_tensor_comm`, `wordGram_tensor_assoc`: compatibility with
  interchange and reassociation of the independent factors.
* `GrandTensorMonoidal.indepProduct` — the independent composite of two predictive systems
  (product preparations = product histories, joint local operations `(a,b)` including the
  identity operations, factorized future probabilities);
  `indepProduct_futureEquivalent_iff` and `indepProductMinimalEquiv`:
  `Z₁₂^min ≃ Z₁^min × Z₂^min` (`eq:supp-grand-product`, first identification).
* `GrandTensorMonoidal.contextualIdeal`, `HistoryAlgebra` — a raw represented algebra with a
  context family closed under inserting elements on either side; its contextual null set is a
  two-sided ideal, the largest one invisible in all contexts (`lem:supp-contextual-ideal`), and
  `𝒜^hist = 𝒜^raw/𝒥^ctx` (`eq:supp-history-algebra`); `historyMoment` is `τ̂_reg([v]^*[w])`.
  `historyAlgebra_starAlgEquiv`: a `*`-isomorphism of raw algebras carrying contexts to contexts
  (e.g. a record-preserving unitary conjugation) induces an isomorphism of history algebras
  compatible with the involution and preserving all word moments.
  `productContexts_null_iff`, `compositeHistoryAlgebraEquiv`, `compositeHistoryMoment`: with
  the product contextual family on `R₁ ⊗ R₂`, there is no further contextual ideal, the
  composite history algebra is `𝒜₁^hist ⊗ 𝒜₂^hist` (`[r₁ ⊗ r₂] ↦ [r₁] ⊗ [r₂]`), and word
  moments of independent word pairs factor.
-/

open scoped TensorProduct Kronecker

namespace RenewalGeometry

namespace GrandTensorMonoidal

/-! ## Covariance of the Gram form under word-coordinate changes -/

open Matrix in
/-- **`prop:supp-grand-monoidal`, coordinate rule.**  Substituting `c = C c̃` in the word-Gram
quadratic form gives the Gram matrix `K̃ = Cᴴ K C`. -/
theorem gram_coordinate_change {K : Type*} [Field K] [StarRing K] {m n : Type*} [Fintype m]
    [Fintype n] (Kmat : Matrix m m K) (C : Matrix m n K) (ct : n → K) :
    star (C *ᵥ ct) ⬝ᵥ (Kmat *ᵥ (C *ᵥ ct)) = star ct ⬝ᵥ ((C.conjTranspose * Kmat * C) *ᵥ ct) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-! ## The normalized regular trace -/

section RegTrace

variable {K : Type*} [Field K]

/-- `eq:supp-regular-trace`: the normalized regular trace `τ̂_reg(a) = Tr(L_a)/dim A`. -/
noncomputable def regTrace (A : Type*) [Ring A] [Algebra K A] (a : A) : K :=
  LinearMap.trace K A (LinearMap.mulLeft K a) / (Module.finrank K A : K)

variable {A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]

/-- Left multiplication is conjugated by an algebra isomorphism. -/
theorem mulLeft_algEquiv (φ : A ≃ₐ[K] B) (a : A) :
    LinearMap.mulLeft K (φ a) = φ.toLinearEquiv.conj (LinearMap.mulLeft K a) := by
  ext b
  simp [LinearEquiv.conj_apply]

/-- The normalized regular trace is invariant under algebra isomorphisms. -/
theorem regTrace_algEquiv (φ : A ≃ₐ[K] B) (a : A) : regTrace (K := K) B (φ a) = regTrace (K := K) A a := by
  unfold regTrace
  rw [mulLeft_algEquiv, LinearMap.trace_conj', φ.toLinearEquiv.finrank_eq]

/-- Left multiplication by an elementary tensor is the tensor product of the left
multiplications (`L_{a ⊗ b} = L_a ⊗ L_b`). -/
theorem mulLeft_tmul (a : A) (b : B) :
    LinearMap.mulLeft K (a ⊗ₜ[K] b) = TensorProduct.map (LinearMap.mulLeft K a)
      (LinearMap.mulLeft K b) := by
  apply TensorProduct.ext'
  intro x y
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- **The normalized regular trace is multiplicative**:
`τ̂_reg(a ⊗ b) = τ̂_reg(a) τ̂_reg(b)` on `A ⊗ B`, since `Tr(L_a ⊗ L_b) = Tr(L_a) Tr(L_b)` and
`dim(A ⊗ B) = dim A dim B`. -/
theorem regTrace_tmul [FiniteDimensional K A] [FiniteDimensional K B] (a : A) (b : B) :
    regTrace (K := K) (A ⊗[K] B) (a ⊗ₜ[K] b) = regTrace (K := K) A a * regTrace (K := K) B b := by
  unfold regTrace
  rw [mulLeft_tmul, LinearMap.trace_tensorProduct', Module.finrank_tensorProduct,
    Nat.cast_mul, div_mul_div_comm]

end RegTrace

/-! ## Word-Gram matrices -/

section WordGram

variable {K : Type*} [Field K] [StarRing K]

/-- `eq:supp-word-gram`: the word-Gram matrix `K(v,w) = τ̂_reg([v]^* [w])` of a represented
word family `[·] : W → A`. -/
noncomputable def wordGram {W : Type*} (A : Type*) [Ring A] [Algebra K A] [Star A]
    (rep : W → A) : Matrix W W K :=
  fun v w => regTrace A (star (rep v) * rep w)

omit [StarRing K] in
/-- **Covariance of word moments.**  A `*`-isomorphism of history algebras carrying the
represented words of one realization to those of the other preserves every word moment. -/
theorem wordGram_starAlgEquiv {W A B : Type*} [Ring A] [Algebra K A] [StarRing A]
    [Ring B] [Algebra K B] [StarRing B]
    (φ : A ≃⋆ₐ[K] B) (repA : W → A) (repB : W → B) (hrep : ∀ w, φ (repA w) = repB w) :
    wordGram (K := K) B repB = wordGram (K := K) A repA := by
  ext v w
  simp only [wordGram]
  rw [← hrep v, ← hrep w, ← map_star, ← map_mul]
  exact regTrace_algEquiv (AlgEquivClass.toAlgEquiv φ : A ≃ₐ[K] B) _

variable {A B : Type*} [Ring A] [Algebra K A] [StarAddMonoid A] [StarModule K A]
  [Ring B] [Algebra K B] [StarAddMonoid B] [StarModule K B]
  [FiniteDimensional K A] [FiniteDimensional K B]

/-- **`eq:supp-grand-gram-product`.**  On a rectangular bank of independent word pairs,
represented by `[v₁] ⊗ [v₂]`, the joint word-Gram matrix is the Kronecker product:
`K₁₂((v₁,v₂),(w₁,w₂)) = K₁(v₁,w₁) K₂(v₂,w₂)`. -/
theorem wordGram_tensor {W₁ W₂ : Type*} (rep₁ : W₁ → A) (rep₂ : W₂ → B) :
    wordGram (K := K) (A ⊗[K] B) (fun p : W₁ × W₂ => rep₁ p.1 ⊗ₜ[K] rep₂ p.2)
      = wordGram (K := K) A rep₁ ⊗ₖ wordGram (K := K) B rep₂ := by
  ext ⟨v₁, v₂⟩ ⟨w₁, w₂⟩
  simp only [wordGram, Matrix.kroneckerMap_apply, TensorProduct.star_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]
  exact regTrace_tmul _ _

/-- Compatibility with interchange of the independent factors: the joint Gram matrix is
symmetric under swapping the two factors. -/
theorem wordGram_tensor_comm {W₁ W₂ : Type*} (rep₁ : W₁ → A) (rep₂ : W₂ → B)
    (v₁ w₁ : W₁) (v₂ w₂ : W₂) :
    wordGram (K := K) (A ⊗[K] B) (fun p : W₁ × W₂ => rep₁ p.1 ⊗ₜ[K] rep₂ p.2) (v₁, v₂) (w₁, w₂)
      = wordGram (K := K) (B ⊗[K] A) (fun p : W₂ × W₁ => rep₂ p.1 ⊗ₜ[K] rep₁ p.2)
          (v₂, v₁) (w₂, w₁) := by
  rw [wordGram_tensor, wordGram_tensor, Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply,
    mul_comm]

/-- Compatibility with reassociation of three independent factors. -/
theorem wordGram_tensor_assoc {C : Type*} [Ring C] [Algebra K C] [StarAddMonoid C]
    [StarModule K C] [FiniteDimensional K C] {W₁ W₂ W₃ : Type*}
    (rep₁ : W₁ → A) (rep₂ : W₂ → B) (rep₃ : W₃ → C) (v₁ w₁ : W₁) (v₂ w₂ : W₂) (v₃ w₃ : W₃) :
    wordGram (K := K) ((A ⊗[K] B) ⊗[K] C)
        (fun p : (W₁ × W₂) × W₃ => (rep₁ p.1.1 ⊗ₜ[K] rep₂ p.1.2) ⊗ₜ[K] rep₃ p.2)
        ((v₁, v₂), v₃) ((w₁, w₂), w₃)
      = wordGram (K := K) (A ⊗[K] (B ⊗[K] C))
        (fun p : W₁ × (W₂ × W₃) => rep₁ p.1 ⊗ₜ[K] (rep₂ p.2.1 ⊗ₜ[K] rep₃ p.2.2))
        (v₁, (v₂, v₃)) (w₁, (w₂, w₃)) := by
  have h1 := wordGram_tensor (K := K) (A := A ⊗[K] B) (B := C)
    (fun p : W₁ × W₂ => rep₁ p.1 ⊗ₜ[K] rep₂ p.2) rep₃
  have h2 := wordGram_tensor (K := K) (A := A) (B := B ⊗[K] C) rep₁
    (fun p : W₂ × W₃ => rep₂ p.1 ⊗ₜ[K] rep₃ p.2)
  have h1' := congrFun (congrFun h1 ((v₁, v₂), v₃)) ((w₁, w₂), w₃)
  have h2' := congrFun (congrFun h2 (v₁, (v₂, v₃))) (w₁, (w₂, w₃))
  rw [h1', h2', Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply, wordGram_tensor,
    wordGram_tensor, Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply, mul_assoc]

end WordGram

/-! ## Independent composition of predictive systems -/

section Product

open DerivedPredictiveCarrierUniversal

variable {H₁ L₁ H₂ L₂ : Type*}

/-- The independent composite of two predictive systems: product preparations (joint
histories are pairs, joint reachability is the product), joint local operations `(a,b)`
acting independently on the two factors, and factorized future probabilities. -/
def indepProduct (P₁ : PredictiveSystem H₁ L₁) (P₂ : PredictiveSystem H₂ L₂) :
    PredictiveSystem (H₁ × H₂) (L₁ × L₂) where
  probability h w := P₁.probability h.1 (w.map Prod.fst) * P₂.probability h.2 (w.map Prod.snd)
  step h a := (P₁.step h.1 a.1, P₂.step h.2 a.2)
  branch h a := P₁.branch h.1 a.1 * P₂.branch h.2 a.2
  probability_nil h := by simp [P₁.probability_nil, P₂.probability_nil]
  probability_cons h a w := by
    simp only [List.map_cons, P₁.probability_cons, P₂.probability_cons]
    ring

/-- An identity operation of a predictive system: probability one, history unchanged. -/
structure IdentityOperation {H L : Type*} (P : PredictiveSystem H L) where
  /-- the identity letter -/
  id : L
  branch_id : ∀ h, P.branch h id = 1
  step_id : ∀ h, P.step h id = h

theorem IdentityOperation.probability_replicate {H L : Type*} {P : PredictiveSystem H L}
    (I : IdentityOperation P) (h : H) (n : ℕ) : P.probability h (List.replicate n I.id) = 1 := by
  induction n with
  | zero => exact P.probability_nil h
  | succ n ih => rw [List.replicate_succ, P.probability_cons, I.branch_id, I.step_id, ih, one_mul]

/-- **Joint future signatures of independent processes.**  With identity operations on both
factors, two joint histories are future equivalent exactly when both marginal histories are
(a test on one factor with the identity on the other detects any unequal marginal). -/
theorem indepProduct_futureEquivalent_iff (P₁ : PredictiveSystem H₁ L₁)
    (P₂ : PredictiveSystem H₂ L₂) (I₁ : IdentityOperation P₁) (I₂ : IdentityOperation P₂)
    (h h' : H₁ × H₂) :
    (indepProduct P₁ P₂).FutureEquivalent h h' ↔
      P₁.FutureEquivalent h.1 h'.1 ∧ P₂.FutureEquivalent h.2 h'.2 := by
  constructor
  · intro hh
    refine ⟨fun w₁ => ?_, fun w₂ => ?_⟩
    · have := hh (w₁.map fun a => (a, I₂.id))
      simp only [indepProduct, List.map_map] at this
      have hs : ((Prod.snd ∘ fun a => (a, I₂.id)) : L₁ → L₂) = fun _ => I₂.id := rfl
      have hf : ((Prod.fst ∘ fun a => (a, I₂.id)) : L₁ → L₁) = id := rfl
      rw [hs, hf, List.map_id, List.map_const', I₂.probability_replicate,
        I₂.probability_replicate, mul_one, mul_one] at this
      exact this
    · have := hh (w₂.map fun b => (I₁.id, b))
      simp only [indepProduct, List.map_map] at this
      have hs : ((Prod.snd ∘ fun b => (I₁.id, b)) : L₂ → L₂) = id := rfl
      have hf : ((Prod.fst ∘ fun b => (I₁.id, b)) : L₂ → L₁) = fun _ => I₁.id := rfl
      rw [hs, hf, List.map_id, List.map_const', I₁.probability_replicate,
        I₁.probability_replicate, one_mul, one_mul] at this
      exact this
  · rintro ⟨h₁, h₂⟩ w
    simp only [indepProduct]
    rw [h₁, h₂]

/-- **`eq:supp-grand-product`, predictive factor.**  For independent processes with identity
operations and product reachability, `Z₁₂^min ≃ Z₁^min × Z₂^min`, `[(h₁,h₂)] ↦ ([h₁],[h₂])`. -/
noncomputable def indepProductMinimalEquiv (P₁ : PredictiveSystem H₁ L₁)
    (P₂ : PredictiveSystem H₂ L₂) (I₁ : IdentityOperation P₁) (I₂ : IdentityOperation P₂) :
    (indepProduct P₁ P₂).MinimalCarrier ≃ P₁.MinimalCarrier × P₂.MinimalCarrier :=
  (Quotient.congr (Equiv.refl _) (fun h h' =>
      indepProduct_futureEquivalent_iff P₁ P₂ I₁ I₂ h h')).trans
    (Setoid.prodQuotientEquiv P₁.futureSetoid P₂.futureSetoid).symm

@[simp] theorem indepProductMinimalEquiv_mk (P₁ : PredictiveSystem H₁ L₁)
    (P₂ : PredictiveSystem H₂ L₂) (I₁ : IdentityOperation P₁) (I₂ : IdentityOperation P₂)
    (h : H₁ × H₂) :
    indepProductMinimalEquiv P₁ P₂ I₁ I₂ (Quotient.mk _ h)
      = (Quotient.mk _ h.1, Quotient.mk _ h.2) := rfl

/-- The identification `Z₁₂^min ≃ Z₁^min × Z₂^min` carries the joint branch law to the
product of the marginal branch laws. -/
theorem indepProductMinimalEquiv_branch (P₁ : PredictiveSystem H₁ L₁)
    (P₂ : PredictiveSystem H₂ L₂) (I₁ : IdentityOperation P₁) (I₂ : IdentityOperation P₂)
    (z : (indepProduct P₁ P₂).MinimalCarrier) (a : L₁ × L₂) :
    (indepProduct P₁ P₂).minimalBranch a z
      = P₁.minimalBranch a.1 (indepProductMinimalEquiv P₁ P₂ I₁ I₂ z).1
        * P₂.minimalBranch a.2 (indepProductMinimalEquiv P₁ P₂ I₁ I₂ z).2 := by
  induction z using Quotient.inductionOn with
  | h h => rfl

end Product

/-! ## Contextual history algebras: transport and independent composition -/

section Contextual

open Module

variable {K : Type*} [Field K]

/-- The contextually null elements of a raw represented algebra: those on which every admitted
context functional vanishes. -/
def contextualNull {R : Type*} [Ring R] [Algebra K R] (C : Set (Dual K R)) : Set R :=
  {a | ∀ φ ∈ C, φ a = 0}

/-- An admitted context family is closed under inserting represented elements on either side
of the tested element. -/
def ContextClosed {R : Type*} [Ring R] [Algebra K R] (C : Set (Dual K R)) : Prop :=
  ∀ φ ∈ C, ∀ x y : R, φ ∘ₗ (LinearMap.mulLeft K x ∘ₗ LinearMap.mulRight K y) ∈ C

/-- `lem:supp-contextual-ideal`: for a closed context family, the contextually null elements
form an ideal (two-sided by `contextualIdeal_isTwoSided`). -/
def contextualIdeal {R : Type*} [Ring R] [Algebra K R] (C : Set (Dual K R))
    (hC : ContextClosed C) : Ideal R where
  carrier := contextualNull C
  add_mem' {a b} ha hb φ hφ := by
    rw [map_add, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' φ _ := map_zero φ
  smul_mem' c a ha φ hφ := by
    have h := ha _ (hC φ hφ c 1)
    simpa using h

instance contextualIdeal_isTwoSided {R : Type*} [Ring R] [Algebra K R] (C : Set (Dual K R))
    (hC : ContextClosed C) : (contextualIdeal C hC).IsTwoSided := by
  constructor
  intro a b ha φ hφ
  have h := ha _ (hC φ hφ 1 b)
  simpa using h

/-- `lem:supp-contextual-ideal`, universal property: the contextual null ideal contains every
ideal invisible in all admitted contexts. -/
theorem le_contextualIdeal {R : Type*} [Ring R] [Algebra K R] (C : Set (Dual K R))
    (hC : ContextClosed C) (I : Ideal R) (hI : ∀ a ∈ I, ∀ φ ∈ C, φ a = 0) :
    I ≤ contextualIdeal C hC :=
  fun a ha => hI a ha

/-- `eq:supp-history-algebra`: the history algebra `𝒜^hist = 𝒜^raw / 𝒥^ctx`. -/
abbrev HistoryAlgebra {R : Type*} [Ring R] [Algebra K R] (C : Set (Dual K R))
    (hC : ContextClosed C) : Type _ :=
  R ⧸ contextualIdeal C hC

/-- The history word moment `τ̂_reg([v]^* [w])` of two raw represented elements, computed in the
history algebra (the involution of `𝒜^hist` is induced from the raw involution). -/
noncomputable def historyMoment {R : Type*} [Ring R] [Algebra K R] [Star R]
    (C : Set (Dual K R)) (hC : ContextClosed C) (v w : R) : K :=
  regTrace (K := K) (HistoryAlgebra C hC)
    (Ideal.Quotient.mk (contextualIdeal C hC) (star v * w))

/-- **`prop:supp-grand-monoidal`, unitary covariance.**  A `*`-isomorphism `Φ` of raw represented
algebras (for instance conjugation by a record-preserving unitary) that carries the admitted
contexts to the admitted contexts (`ψ ∈ C' ↔ ψ ∘ Φ ∈ C`) maps the contextual null ideal onto the
contextual null ideal, hence induces an isomorphism of history algebras `[r] ↦ [Φ r]`, and
preserves every word moment. -/
theorem historyAlgebra_starAlgEquiv {R R' : Type*} [Ring R] [Algebra K R] [StarRing R]
    [Ring R'] [Algebra K R'] [StarRing R']
    (C : Set (Dual K R)) (hC : ContextClosed C) (C' : Set (Dual K R')) (hC' : ContextClosed C')
    (Φ : R ≃⋆ₐ[K] R')
    (hctx : ∀ ψ : Dual K R',
      ψ ∈ C' ↔ ψ ∘ₗ (AlgEquivClass.toAlgEquiv Φ : R ≃ₐ[K] R').toLinearMap ∈ C) :
    ∃ e : HistoryAlgebra C hC ≃ₐ[K] HistoryAlgebra C' hC',
      (∀ r : R, e (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (Φ r)) ∧
      (∀ r : R, e (Ideal.Quotient.mk _ (star r)) = Ideal.Quotient.mk _ (star (Φ r))) ∧
      (∀ v w : R, historyMoment C' hC' (Φ v) (Φ w) = historyMoment C hC v w) := by
  let Ψ : R ≃ₐ[K] R' := AlgEquivClass.toAlgEquiv Φ
  have hmem : ∀ r : R, r ∈ contextualIdeal C hC ↔ Ψ r ∈ contextualIdeal C' hC' := by
    intro r
    constructor
    · intro hr ψ hψ
      exact hr _ ((hctx ψ).mp hψ)
    · intro hr φ hφ
      have hφ' : φ ∘ₗ (Ψ.symm : R' ≃ₐ[K] R).toLinearMap ∈ C' := by
        rw [hctx]
        convert hφ using 1
        ext x
        simp [Ψ]
      have := hr _ hφ'
      simpa [Ψ] using this
  have hIJ : contextualIdeal C' hC' = (contextualIdeal C hC).map (Ψ : R →+* R') := by
    apply le_antisymm
    · intro y hy
      have hy' : Ψ.symm y ∈ contextualIdeal C hC := (hmem _).mpr (by simpa using hy)
      have := Ideal.mem_map_of_mem (Ψ : R →+* R') hy'
      simpa using this
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (hmem x).mp hx
  let e := Ideal.quotientEquivAlg (contextualIdeal C hC) (contextualIdeal C' hC') Ψ hIJ
  refine ⟨e, fun r => rfl, fun r => ?_, fun v w => ?_⟩
  · change Ideal.Quotient.mk _ (Ψ (star r)) = _
    congr 1
    exact map_star Φ r
  unfold historyMoment
  have h1 : Ideal.Quotient.mk (contextualIdeal C' hC') (star (Φ v) * Φ w)
      = e (Ideal.Quotient.mk (contextualIdeal C hC) (star v * w)) := by
    change _ = Ideal.Quotient.mk _ (Ψ (star v * w))
    congr 1
    change star (Φ v) * Φ w = Φ (star v * w)
    rw [map_mul, map_star]
  rw [h1]
  exact regTrace_algEquiv e _

/-- The product context functionals `φ₁ ⊗ φ₂` of two independent processes. -/
def productContexts {R₁ R₂ : Type*} [Ring R₁] [Algebra K R₁] [Ring R₂] [Algebra K R₂]
    (C₁ : Set (Dual K R₁)) (C₂ : Set (Dual K R₂)) : Set (Dual K (R₁ ⊗[K] R₂)) :=
  {ψ | ∃ φ₁ ∈ C₁, ∃ φ₂ ∈ C₂, ψ = TensorProduct.dualDistrib K R₁ R₂ (φ₁ ⊗ₜ φ₂)}

/-- The quotient map of a raw algebra onto its history algebra. -/
abbrev historyQuotient {R : Type*} [Ring R] [Algebra K R] (C : Set (Dual K R))
    (hC : ContextClosed C) : R →ₐ[K] HistoryAlgebra C hC :=
  Ideal.Quotient.mkₐ K (contextualIdeal C hC)

/-- A context functional descends to the history algebra. -/
noncomputable def descendContext {R : Type*} [Ring R] [Algebra K R] (C : Set (Dual K R))
    (hC : ContextClosed C) (φ : Dual K R) (hφ : φ ∈ C) : Dual K (HistoryAlgebra C hC) :=
  ((contextualIdeal C hC).restrictScalars K).liftQ φ (fun _ ha => ha φ hφ) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv K (contextualIdeal C hC)).symm.toLinearMap

theorem descendContext_mk {R : Type*} [Ring R] [Algebra K R] (C : Set (Dual K R))
    (hC : ContextClosed C) (φ : Dual K R) (hφ : φ ∈ C) (r : R) :
    descendContext C hC φ hφ (Ideal.Quotient.mk _ r) = φ r := by
  rfl

/-- The descended context functionals span the whole dual of a finite-dimensional history
algebra (contextual separation). -/
theorem span_descendContext_eq_top {R : Type*} [Ring R] [Algebra K R] [FiniteDimensional K R]
    (C : Set (Dual K R)) (hC : ContextClosed C) :
    Submodule.span K {ψ | ∃ φ, ∃ hφ : φ ∈ C, ψ = descendContext C hC φ hφ} = ⊤ := by
  set W := Submodule.span K {ψ | ∃ φ, ∃ hφ : φ ∈ C, ψ = descendContext C hC φ hφ}
  have hbot : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Submodule.mem_dualCoannihilator] at ha
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    intro φ hφ
    have := ha _ (Submodule.subset_span ⟨φ, hφ, rfl⟩)
    rwa [descendContext_mk] at this
  have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
  rw [hbot, Submodule.dualAnnihilator_bot] at this
  exact this.symm

variable {R₁ R₂ : Type*} [Ring R₁] [Algebra K R₁] [Ring R₂] [Algebra K R₂]
  [FiniteDimensional K R₁] [FiniteDimensional K R₂]

/-- **Product contexts separate the tensor product of history algebras.**  An element of the
composite raw algebra `R₁ ⊗ R₂` is null in every product context exactly when it lies in the
kernel of `R₁ ⊗ R₂ → 𝒜₁^hist ⊗ 𝒜₂^hist`: there is no further contextual ideal. -/
theorem productContexts_null_iff (C₁ : Set (Dual K R₁)) (hC₁ : ContextClosed C₁)
    (C₂ : Set (Dual K R₂)) (hC₂ : ContextClosed C₂) (x : R₁ ⊗[K] R₂) :
    x ∈ contextualNull (productContexts C₁ C₂) ↔
      Algebra.TensorProduct.map (historyQuotient C₁ hC₁) (historyQuotient C₂ hC₂) x = 0 := by
  set f := Algebra.TensorProduct.map (historyQuotient C₁ hC₁) (historyQuotient C₂ hC₂)
  have hfac : ∀ φ₁ (h₁ : φ₁ ∈ C₁) φ₂ (h₂ : φ₂ ∈ C₂) (y : R₁ ⊗[K] R₂),
      TensorProduct.dualDistrib K R₁ R₂ (φ₁ ⊗ₜ φ₂) y
        = TensorProduct.dualDistrib K _ _
            (descendContext C₁ hC₁ φ₁ h₁ ⊗ₜ descendContext C₂ hC₂ φ₂ h₂) (f y) := by
    intro φ₁ h₁ φ₂ h₂ y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [f, Algebra.TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mkₐ_eq_mk, descendContext_mk,
        descendContext_mk]
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
  constructor
  · intro hx
    set y := f x
    let ev : (Dual K (HistoryAlgebra C₁ hC₁) ⊗[K] Dual K (HistoryAlgebra C₂ hC₂)) →ₗ[K] K :=
      LinearMap.applyₗ (R := K) y ∘ₗ TensorProduct.dualDistrib K _ _
    have hgen : ∀ ψ₁ ∈ {ψ | ∃ φ, ∃ hφ : φ ∈ C₁, ψ = descendContext C₁ hC₁ φ hφ},
        ∀ ψ₂ ∈ {ψ | ∃ φ, ∃ hφ : φ ∈ C₂, ψ = descendContext C₂ hC₂ φ hφ},
          ev (ψ₁ ⊗ₜ ψ₂) = 0 := by
      rintro _ ⟨φ₁, h₁, rfl⟩ _ ⟨φ₂, h₂, rfl⟩
      have := hx _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
      rw [hfac φ₁ h₁ φ₂ h₂] at this
      exact this
    have hall : ∀ t, ev t = 0 := by
      intro t
      have hle : Submodule.span K {t : Dual K (HistoryAlgebra C₁ hC₁) ⊗[K]
          Dual K (HistoryAlgebra C₂ hC₂) | ∃ ψ₁ ψ₂, ψ₁ ⊗ₜ ψ₂ = t} ≤ LinearMap.ker ev := by
        rw [Submodule.span_le]
        rintro _ ⟨ψ₁, ψ₂, rfl⟩
        have h1 : ψ₁ ∈ Submodule.span K
            {ψ | ∃ φ, ∃ hφ : φ ∈ C₁, ψ = descendContext C₁ hC₁ φ hφ} := by
          rw [span_descendContext_eq_top]; trivial
        have h2 : ψ₂ ∈ Submodule.span K
            {ψ | ∃ φ, ∃ hφ : φ ∈ C₂, ψ = descendContext C₂ hC₂ φ hφ} := by
          rw [span_descendContext_eq_top]; trivial
        change ev (ψ₁ ⊗ₜ ψ₂) = 0
        induction h1 using Submodule.span_induction with
        | mem a ha =>
          induction h2 using Submodule.span_induction with
          | mem b hb => exact hgen a ha b hb
          | zero => simp
          | add b c _ _ hb hc => rw [TensorProduct.tmul_add, map_add, hb, hc, add_zero]
          | smul k b _ hb => rw [TensorProduct.tmul_smul, map_smul, hb, smul_zero]
        | zero => simp
        | add _ c _ _ ha hc => rw [TensorProduct.add_tmul, map_add, ha, hc, add_zero]
        | smul k a _ ha => rw [← TensorProduct.smul_tmul', map_smul, ha, smul_zero]
      have hmem : t ∈ Submodule.span K {t : Dual K (HistoryAlgebra C₁ hC₁) ⊗[K]
          Dual K (HistoryAlgebra C₂ hC₂) | ∃ ψ₁ ψ₂, ψ₁ ⊗ₜ ψ₂ = t} := by
        rw [TensorProduct.span_tmul_eq_top]; trivial
      exact hle hmem
    have hdual : ∀ θ : Dual K (HistoryAlgebra C₁ hC₁ ⊗[K] HistoryAlgebra C₂ hC₂), θ y = 0 := by
      intro θ
      have := hall ((TensorProduct.dualDistribEquiv K _ _).symm θ)
      have he : TensorProduct.dualDistrib K _ _ ((TensorProduct.dualDistribEquiv K _ _).symm θ)
          = θ := (TensorProduct.dualDistribEquiv K _ _).apply_symm_apply θ
      simp only [ev, LinearMap.coe_comp, Function.comp_apply, LinearMap.applyₗ_apply_apply,
        he] at this
      exact this
    exact (Module.forall_dual_apply_eq_zero_iff K y).mp hdual
  · intro hx ψ hψ
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hψ
    rw [hfac φ₁ h₁ φ₂ h₂, hx, map_zero]

/-- The quotient of a ring by a two-sided ideal (a notational helper). -/
abbrev RawQuotient {A : Type*} [Ring A] (I : Ideal A) : Type _ := A ⧸ I

/-- The null ideal of the product contexts on the composite raw algebra `R₁ ⊗ R₂`; by
`mem_compositeNullIdeal` it is exactly the set of product-contextually null elements. -/
abbrev compositeNullIdeal (C₁ : Set (Dual K R₁)) (hC₁ : ContextClosed C₁)
    (C₂ : Set (Dual K R₂)) (hC₂ : ContextClosed C₂) : Ideal (R₁ ⊗[K] R₂) :=
  RingHom.ker (Algebra.TensorProduct.map (historyQuotient C₁ hC₁) (historyQuotient C₂ hC₂))

/-- The composite null ideal consists exactly of the elements null in every product context;
in particular it is the largest ideal invisible in all product contexts. -/
theorem mem_compositeNullIdeal (C₁ : Set (Dual K R₁)) (hC₁ : ContextClosed C₁)
    (C₂ : Set (Dual K R₂)) (hC₂ : ContextClosed C₂) (x : R₁ ⊗[K] R₂) :
    x ∈ compositeNullIdeal C₁ hC₁ C₂ hC₂ ↔ x ∈ contextualNull (productContexts C₁ C₂) := by
  rw [RingHom.mem_ker, productContexts_null_iff]

omit [FiniteDimensional K R₁] [FiniteDimensional K R₂] in
theorem compositeHistoryQuotient_surjective (C₁ : Set (Dual K R₁)) (hC₁ : ContextClosed C₁)
    (C₂ : Set (Dual K R₂)) (hC₂ : ContextClosed C₂) :
    Function.Surjective
      (Algebra.TensorProduct.map (historyQuotient C₁ hC₁) (historyQuotient C₂ hC₂)) :=
  TensorProduct.map_surjective (Ideal.Quotient.mkₐ_surjective K _)
    (Ideal.Quotient.mkₐ_surjective K _)

/-- **`eq:supp-grand-product`, history-algebra factor.**  The composite history algebra of two
independent processes — the raw tensor product (generated by `a ⊗ I` and `I ⊗ b`) modulo the
null ideal of the product contexts — is isomorphic to `𝒜₁^hist ⊗ 𝒜₂^hist`. -/
noncomputable def compositeHistoryAlgebraEquiv (C₁ : Set (Dual K R₁)) (hC₁ : ContextClosed C₁)
    (C₂ : Set (Dual K R₂)) (hC₂ : ContextClosed C₂) :
    RawQuotient (compositeNullIdeal C₁ hC₁ C₂ hC₂)
      ≃ₐ[K] HistoryAlgebra C₁ hC₁ ⊗[K] HistoryAlgebra C₂ hC₂ :=
  Ideal.quotientKerAlgEquivOfSurjective (compositeHistoryQuotient_surjective C₁ hC₁ C₂ hC₂)

omit [FiniteDimensional K R₁] [FiniteDimensional K R₂] in
/-- The identification is specified on elementary histories: `[r₁ ⊗ r₂] ↦ [r₁] ⊗ [r₂]`. -/
theorem compositeHistoryAlgebraEquiv_mk_tmul (C₁ : Set (Dual K R₁)) (hC₁ : ContextClosed C₁)
    (C₂ : Set (Dual K R₂)) (hC₂ : ContextClosed C₂) (r₁ : R₁) (r₂ : R₂) :
    compositeHistoryAlgebraEquiv C₁ hC₁ C₂ hC₂ (Ideal.Quotient.mk _ (r₁ ⊗ₜ r₂))
      = Ideal.Quotient.mk _ r₁ ⊗ₜ Ideal.Quotient.mk _ r₂ := rfl

/-- **`eq:supp-grand-gram-product` in the composite history algebra.**  The word moment of two
independent word pairs, computed with the normalized regular trace of the composite history
algebra, is the product of the marginal word moments. -/
theorem compositeHistoryMoment [StarRing K] [StarAddMonoid R₁] [StarModule K R₁]
    [StarAddMonoid R₂] [StarModule K R₂]
    (C₁ : Set (Dual K R₁)) (hC₁ : ContextClosed C₁)
    (C₂ : Set (Dual K R₂)) (hC₂ : ContextClosed C₂) (v₁ w₁ : R₁) (v₂ w₂ : R₂) :
    regTrace (K := K) (RawQuotient (compositeNullIdeal C₁ hC₁ C₂ hC₂))
        (Ideal.Quotient.mk _ (star (v₁ ⊗ₜ[K] v₂) * (w₁ ⊗ₜ[K] w₂)))
      = historyMoment C₁ hC₁ v₁ w₁ * historyMoment C₂ hC₂ v₂ w₂ := by
  rw [← regTrace_algEquiv (compositeHistoryAlgebraEquiv C₁ hC₁ C₂ hC₂), TensorProduct.star_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, compositeHistoryAlgebraEquiv_mk_tmul]
  exact regTrace_tmul _ _

end Contextual

end GrandTensorMonoidal

end RenewalGeometry
