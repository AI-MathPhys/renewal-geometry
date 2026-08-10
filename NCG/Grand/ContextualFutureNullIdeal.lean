/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteMatrixBlockIdealDecomposition
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# The complete contextual future-null ideal

This file gives the exact algebraic and finite-dimensional quotient content of
`lem:contextual-null-ideal`.  The null test includes both `q` and `star q` in
every two-sided context.  It therefore forms a two-sided star ideal.  In a
finite matrix-block process algebra, its canonical central support realizes
the quotient as the complementary block summand; that representative respects
addition, multiplication, and star, and it is nonzero exactly when a
contextual future test detects the class.
-/

namespace NCG

open scoped ComplexOrder

/-- Complete contextual future nullity, including the manuscript's second
family of tests on the adjoint history. -/
def contextualFutureNull {A : Type*} [Ring A] [StarRing A] {κ : Type*}
    (R : κ → A →+ ℂ) : Set A :=
  {q | (∀ (k : κ) (u v : A), R k (u * q * v) = 0) ∧
    ∀ (k : κ) (u v : A), R k (u * star q * v) = 0}

/-- The complete contextual future-null set as a left ideal. -/
def contextualFutureNullIdeal {A : Type*} [Ring A] [StarRing A] {κ : Type*}
    (R : κ → A →+ ℂ) : Ideal A where
  carrier := contextualFutureNull R
  zero_mem' := by
    constructor <;> intro k u v <;> simp
  add_mem' := by
    intro p q hp hq
    constructor
    · intro k u v
      rw [mul_add, add_mul, map_add, hp.1 k u v, hq.1 k u v, add_zero]
    · intro k u v
      rw [star_add, mul_add, add_mul, map_add, hp.2 k u v, hq.2 k u v, add_zero]
  smul_mem' := by
    intro a q hq
    change contextualFutureNull R (a * q)
    constructor
    · intro k u v
      rw [show u * (a * q) * v = (u * a) * q * v by simp only [mul_assoc]]
      exact hq.1 k (u * a) v
    · intro k u v
      rw [star_mul]
      rw [show u * (star q * star a) * v = u * star q * (star a * v) by
        simp only [mul_assoc]]
      exact hq.2 k u (star a * v)

/-- Contextual future nullity is also closed under multiplication on the
right, hence is a genuine two-sided ideal. -/
instance contextualFutureNullIdeal_isTwoSided
    {A : Type*} [Ring A] [StarRing A] {κ : Type*} (R : κ → A →+ ℂ) :
    (contextualFutureNullIdeal R).IsTwoSided where
  mul_mem_of_left {q} a hq := by
    change contextualFutureNull R _ at hq ⊢
    constructor
    · intro k u v
      rw [show u * (q * a) * v = u * q * (a * v) by simp only [mul_assoc]]
      exact hq.1 k u (a * v)
    · intro k u v
      rw [star_mul]
      rw [show u * (star a * star q) * v = (u * star a) * star q * v by
        simp only [mul_assoc]]
      exact hq.2 k (u * star a) v

/-- The second family of defining tests makes the ideal star-stable. -/
theorem contextualFutureNullIdeal_star_mem
    {A : Type*} [Ring A] [StarRing A] {κ : Type*} (R : κ → A →+ ℂ)
    {q : A} (hq : q ∈ contextualFutureNullIdeal R) :
    star q ∈ contextualFutureNullIdeal R := by
  change contextualFutureNull R q at hq
  change contextualFutureNull R (star q)
  constructor
  · exact hq.2
  · intro k u v
    rw [star_star]
    exact hq.1 k u v

/-- Failure of contextual nullity is exactly visibility in at least one of
the two defining future-test families. -/
theorem not_contextualFutureNull_iff_visible
    {A : Type*} [Ring A] [StarRing A] {κ : Type*} (R : κ → A →+ ℂ) (q : A) :
    q ∉ contextualFutureNull R ↔
      ∃ (k : κ) (u v : A),
        R k (u * q * v) ≠ 0 ∨ R k (u * star q * v) ≠ 0 := by
  classical
  simp only [contextualFutureNull, Set.mem_setOf_eq, not_and_or, not_forall]
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · rcases hk with ⟨u, v, huv⟩
      exact ⟨k, u, v, Or.inl huv⟩
    · rcases hk with ⟨u, v, huv⟩
      exact ⟨k, u, v, Or.inr huv⟩
  · rintro ⟨k, u, v, huv | huv⟩
    · exact Or.inl ⟨k, u, v, huv⟩
    · exact Or.inr ⟨k, u, v, huv⟩

section MatrixBlockQuotient

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (d : ι → Type*) [∀ b, Fintype (d b)] [∀ b, DecidableEq (d b)]
variable {κ : Type*}

/-- The canonical representative of a quotient class: discard precisely the
central matrix blocks belonging to the contextual null ideal. -/
noncomputable def contextualHistoryRepresentative
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ)
    (q : FiniteMatrixBlockAlgebra d) : FiniteMatrixBlockAlgebra d :=
  let N := contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom)
  (1 - matrixBlockCentralSupport d N) * q

/-- The canonical representative realizes the finite-dimensional quotient:
it is additive, multiplicative, star-preserving, and its kernel is exactly the
complete contextual future-null ideal. -/
theorem contextualHistoryRepresentative_structure
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ) :
    let N := contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom)
    let z := matrixBlockCentralSupport d N
    let e := 1 - z
    e * e = e ∧ star e = e ∧ (∀ a, e * a = a * e)
      ∧ (∀ p q, contextualHistoryRepresentative d R (p + q) =
          contextualHistoryRepresentative d R p + contextualHistoryRepresentative d R q)
      ∧ (∀ p q, contextualHistoryRepresentative d R (p * q) =
          contextualHistoryRepresentative d R p * contextualHistoryRepresentative d R q)
      ∧ (∀ q, contextualHistoryRepresentative d R (star q) =
          star (contextualHistoryRepresentative d R q))
      ∧ (∀ q, contextualHistoryRepresentative d R q = 0 ↔ q ∈ N) := by
  classical
  dsimp only
  let N := contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom)
  let z := matrixBlockCentralSupport d N
  let e := 1 - z
  rcases matrixBlockCentralSupport_isCentralProjection d N with ⟨hz, hstarz, hcenz⟩
  change z * z = z at hz
  change star z = z at hstarz
  change ∀ a, z * a = a * z at hcenz
  have he : e * e = e := by
    calc
      e * e = 1 - z - z + z * z := by
        dsimp [e]
        noncomm_ring
      _ = e := by rw [hz]; dsimp [e]; abel
  have hstare : star e = e := by
    dsimp [e]
    rw [star_sub, star_one, hstarz]
  have hcene : ∀ a, e * a = a * e := by
    intro a
    dsimp [e]
    rw [sub_mul, mul_sub, one_mul, mul_one, hcenz]
  refine ⟨he, hstare, hcene, ?_, ?_, ?_, ?_⟩
  · intro p q
    simp only [contextualHistoryRepresentative, mul_add]
  · intro p q
    simp only [contextualHistoryRepresentative]
    calc
      e * (p * q) = (e * e) * (p * q) := by rw [he]
      _ = e * (e * p) * q := by simp only [mul_assoc]
      _ = e * (p * e) * q := by rw [hcene p]
      _ = (e * p) * (e * q) := by simp only [mul_assoc]
      _ = _ := rfl
  · intro q
    simp only [contextualHistoryRepresentative]
    rw [star_mul, hstare, hcene]
  · intro q
    simp only [contextualHistoryRepresentative]
    constructor
    · intro hq
      change e * q = 0 at hq
      have hsplit := (central_source_decomposition z hz hcenz).1 q
      have hsplit' : q = z * q + e * q := by simpa [e] using hsplit
      have hqz : q = z * q := by rw [hq, add_zero] at hsplit'; exact hsplit'
      exact (matrixBlockIdeal_eq_centralSupport_range d N q).2 ⟨q, hqz⟩
    · intro hq
      rcases (matrixBlockIdeal_eq_centralSupport_range d N q).1 hq with ⟨a, rfl⟩
      rw [show e * (z * a) = (e * z) * a by simp only [mul_assoc]]
      have : e * z = 0 := by
        calc
          e * z = z - z * z := by dsimp [e]; noncomm_ring
          _ = 0 := by rw [hz, sub_self]
      rw [this, zero_mul]

/-- A quotient representative is nonzero exactly when some admitted
contextual future test sees its class.  This is future separation. -/
theorem contextualHistoryRepresentative_nonzero_iff_visible
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ)
    (q : FiniteMatrixBlockAlgebra d) :
    contextualHistoryRepresentative d R q ≠ 0 ↔
      ∃ (k : κ) (u v : FiniteMatrixBlockAlgebra d),
        R k (u * q * v) ≠ 0 ∨ R k (u * star q * v) ≠ 0 := by
  classical
  let N := contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom)
  have hker := (contextualHistoryRepresentative_structure d R).2.2.2.2.2.2 q
  calc
    contextualHistoryRepresentative d R q ≠ 0 ↔ q ∉ N := not_congr hker
    _ ↔ _ := not_contextualFutureNull_iff_visible (fun k => (R k).toAddMonoidHom) q

/-- Complete finite-dimensional quotient package: the null ideal is the
range of a unique central projection, and the complementary matrix-block
representative supplies its finite-dimensional future-separated star-algebra
quotient. -/
theorem contextualFutureNull_finiteMatrixBlock_quotient
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ) :
    let N := contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom)
    ∃! z : FiniteMatrixBlockAlgebra d,
      z * z = z ∧ star z = z ∧ (∀ a, z * a = a * z)
      ∧ (∀ x, x ∈ N ↔ ∃ a, x = z * a)
      ∧ (∀ a, a = z * a + (1 - z) * a) := by
  dsimp only
  exact finiteMatrixBlock_centralIdeal_decomposition d
    (contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom))

/-- Indices of the simple matrix blocks which survive contextual quotienting. -/
abbrev ContextualSurvivingBlock
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ) :=
  {b : ι // b ∉ matrixBlockIdealSupport d
    (contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom))}

instance contextualSurvivingBlockFinite
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ) :
    Finite (ContextualSurvivingBlock d R) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance contextualSurvivingBlockFintype
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ) :
    Fintype (ContextualSurvivingBlock d R) := Fintype.ofFinite _

noncomputable instance contextualSurvivingBlockDecidableEq
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ) :
    DecidableEq (ContextualSurvivingBlock d R) := Classical.decEq _

/-- The history quotient as the literal finite product of its surviving full
matrix blocks. -/
abbrev ContextualHistoryBlockAlgebra
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ) :=
  ∀ b : ContextualSurvivingBlock d R, CStarMatrix (d b.1) (d b.1) ℂ

/-- Restriction to the surviving blocks is the canonical quotient
star-algebra homomorphism. -/
noncomputable def contextualHistoryBlockRepresentation
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ) :
    FiniteMatrixBlockAlgebra d →⋆ₐ[ℂ] ContextualHistoryBlockAlgebra d R where
  toFun q b := CStarMatrix.ofMatrix (q b.1)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- Every tuple on the surviving blocks has an extension by zero to the full
process algebra. -/
theorem contextualHistoryBlockRepresentation_surjective
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ) :
    Function.Surjective (contextualHistoryBlockRepresentation d R) := by
  classical
  intro y
  let q : FiniteMatrixBlockAlgebra d := fun b =>
    if hb : b ∉ matrixBlockIdealSupport d
        (contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom))
      then CStarMatrix.ofMatrix.symm (y ⟨b, hb⟩) else 0
  refine ⟨q, ?_⟩
  funext b
  rcases b with ⟨b, hb⟩
  change CStarMatrix.ofMatrix (q b) = y ⟨b, hb⟩
  dsimp [q]
  rw [dif_pos hb]
  exact Equiv.apply_symm_apply CStarMatrix.ofMatrix _

/-- The kernel of restriction to surviving blocks is exactly the complete
contextual future-null ideal. -/
theorem contextualHistoryBlockRepresentation_ker
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ)
    (q : FiniteMatrixBlockAlgebra d) :
    contextualHistoryBlockRepresentation d R q = 0 ↔
      q ∈ contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom) := by
  classical
  let N := contextualFutureNullIdeal (fun k => (R k).toAddMonoidHom)
  let z := matrixBlockCentralSupport d N
  constructor
  · intro hq
    apply (matrixBlockIdeal_eq_centralSupport_range d N q).2
    refine ⟨q, ?_⟩
    funext b
    change q b = z b * q b
    by_cases hb : b ∈ matrixBlockIdealSupport d N
    · rw [show z b = 1 from matrixBlockCentralSupport_apply_of_mem d N hb]
      simp
    · have hqb : q b = 0 := by
        have hentry := congrFun hq
          (⟨b, hb⟩ : ContextualSurvivingBlock d R)
        exact hentry
      rw [show z b = 0 from matrixBlockCentralSupport_apply_of_not_mem d N hb]
      simp [hqb]
  · intro hq
    rcases (matrixBlockIdeal_eq_centralSupport_range d N q).1 hq with ⟨a, rfl⟩
    funext b
    change z b.1 * a b.1 = 0
    rw [show z b.1 = 0 from
      matrixBlockCentralSupport_apply_of_not_mem d N b.property]
    exact zero_mul _

/-- The concrete quotient codomain is finite-dimensional over `ℂ`. -/
theorem contextualHistoryBlockAlgebra_finiteDimensional
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ) :
    FiniteDimensional ℂ (ContextualHistoryBlockAlgebra d R) := by
  exact FiniteDimensional.of_surjective
    (contextualHistoryBlockRepresentation d R).toAlgHom.toLinearMap
    (contextualHistoryBlockRepresentation_surjective d R)

/-- The surviving finite product carries its canonical matrix-product
`CStarAlgebra` structure. -/
noncomputable instance contextualHistoryBlockAlgebraCStarAlgebra
    (R : κ → FiniteMatrixBlockAlgebra d →ₗ[ℂ] ℂ) :
    CStarAlgebra (ContextualHistoryBlockAlgebra d R) := by
  letI : ∀ b : ContextualSurvivingBlock d R,
      CStarAlgebra (CStarMatrix (d b.1) (d b.1) ℂ) := fun _ => inferInstance
  infer_instance

end MatrixBlockQuotient

end NCG
