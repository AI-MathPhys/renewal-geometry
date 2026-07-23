/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.Operational
import NCG.Algebra.ChoiCriterion

/-!
# Process systems, parallel completeness, ancillary stability, roles

Encodes four definitional statements of `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:process-system` — `ProcessSystem`: a rooted operational system
  on a monoidal process category with multiplicative discard effects
  and admissible continuations closed under discarding and
  whiskering;
* `def:parallel-completeness` — `ParallelComplete`: `≡₁ = ≡∥` on
  every process set, together with the **proved equivalence** with
  bijectivity of every canonical comparison `κ_{A,B}` from parallel
  classes onto sequential classes
  (`parallelComplete_iff_bijective`);
* `def:ancillary-stability` — `IsCompletelyAncillaryStable`:
  positivity of every extension `id_{M_k} ⊗ Φ` by a `k`-level complex
  ancilla, definitionally the matrix complete positivity of the Choi
  development and hence equivalent to positivity of the Choi matrix
  (`isCompletelyAncillaryStable_iff_choi`);
* `def:logical-roles` — `LogicalRole`: the four exhaustive logical
  roles of hypotheses (foundational axiom, microscopic model
  specification, phase criterion, physical selection).
-/

namespace NCG.Upstream

open CategoryTheory MonoidalCategory

universe u v w t

variable {P : Type u} [Category.{v} P] {W : Type w} {T : P → Type t}

/-- **Definition `def:process-system`**: a rooted operational process
system on a symmetric-monoidal-style process category: an
`OperationalSystem` together with discard effects `u_A : A ⟶ I` that
are multiplicative over tensor (via whiskering and the left unitor)
and admissible, with the admissible continuations closed under
whiskering by ancillas.  (The convex mixing clause is abstracted into
the structureless weight set `W` of the underlying system.) -/
structure ProcessSystem (P : Type u) [Category.{v} P]
    [MonoidalCategory P] (W : Type w) (T : P → Type t)
    extends OperationalSystem P W T where
  /-- The discard effect at each interface. -/
  discard : ∀ A : P, A ⟶ 𝟙_ P
  /-- Discarding the trivial interface is trivial. -/
  discard_unit : discard (𝟙_ P) = 𝟙 (𝟙_ P)
  /-- Discards are multiplicative over the tensor product. -/
  discard_tensor : ∀ A B : P,
    discard (A ⊗ B) = (discard A ▷ B) ≫ (λ_ B).hom ≫ discard B
  /-- Discards are admissible continuations. -/
  cont_discard : ∀ A : P, Cont (discard A)
  /-- Admissible continuations are closed under whiskering. -/
  cont_whisker : ∀ {A B : P} (f : A ⟶ B) (R : P),
    Cont f → Cont (f ▷ R)

/-- Two-sided contextual equivalence is an equivalence relation. -/
theorem ctxEquiv_equivalence (O : OperationalSystem P W T)
    (A B : P) : Equivalence (CtxEquiv O (A := A) (B := B)) :=
  ⟨fun _ _ _ _ _ _ => rfl,
    fun h a C c hc t => (h a C c hc t).symm,
    fun h1 h2 a C c hc t => (h1 a C c hc t).trans (h2 a C c hc t)⟩

/-- Complete contextual equivalence is an equivalence relation. -/
theorem cctxEquiv_equivalence [MonoidalCategory P]
    (O : OperationalSystem P W T) (A B : P) :
    Equivalence (CCtxEquiv O (A := A) (B := B)) :=
  ⟨fun _ _ _ _ _ _ _ => rfl,
    fun h R a C c hc t => (h R a C c hc t).symm,
    fun h1 h2 R a C c hc t =>
      (h1 R a C c hc t).trans (h2 R a C c hc t)⟩

/-- The setoid of sequential (two-sided contextual) equivalence. -/
def ctxSetoid (O : OperationalSystem P W T) (A B : P) :
    Setoid (A ⟶ B) :=
  ⟨CtxEquiv O, ctxEquiv_equivalence O A B⟩

/-- The setoid of parallel (complete contextual) equivalence. -/
def cctxSetoid [MonoidalCategory P] (O : OperationalSystem P W T)
    (A B : P) : Setoid (A ⟶ B) :=
  ⟨CCtxEquiv O, cctxEquiv_equivalence O A B⟩

/-- The canonical comparison `κ_{A,B}` from parallel classes onto
sequential classes (well defined since `≡∥ ⊆ ≡₁` once the right
unitor is absorbed by the admissible continuations). -/
def parallelComparison [MonoidalCategory P]
    (O : OperationalSystem P W T)
    (hu : ∀ (B C : P) (c : B ⟶ C), O.Cont c →
      O.Cont ((ρ_ B).hom ≫ c))
    (A B : P) :
    Quotient (cctxSetoid O A B) → Quotient (ctxSetoid O A B) :=
  Quotient.map' id fun _ _ h =>
    cctxEquiv_implies_ctxEquiv h (hu B)

theorem parallelComparison_surjective [MonoidalCategory P]
    (O : OperationalSystem P W T)
    (hu : ∀ (B C : P) (c : B ⟶ C), O.Cont c →
      O.Cont ((ρ_ B).hom ≫ c))
    (A B : P) :
    Function.Surjective (parallelComparison O hu A B) := by
  intro x
  obtain ⟨p, rfl⟩ := Quotient.exists_rep x
  exact ⟨Quotient.mk _ p, rfl⟩

/-- **Definition `def:parallel-completeness`**: the operational
theory is parallel complete when `≡₁ = ≡∥` on every process set —
the precise no-holism condition. -/
def ParallelComplete [MonoidalCategory P]
    (O : OperationalSystem P W T) : Prop :=
  ∀ {A B : P} (p q : A ⟶ B), CtxEquiv O p q ↔ CCtxEquiv O p q

/-- **Definition `def:parallel-completeness` (equivalent form)**:
parallel completeness holds iff every canonical comparison
`κ_{A,B}` is bijective. -/
theorem parallelComplete_iff_bijective [MonoidalCategory P]
    (O : OperationalSystem P W T)
    (hu : ∀ (B C : P) (c : B ⟶ C), O.Cont c →
      O.Cont ((ρ_ B).hom ≫ c)) :
    ParallelComplete O
      ↔ ∀ A B : P, Function.Bijective (parallelComparison O hu A B)
    := by
  constructor
  · intro hpc A B
    refine ⟨?_, parallelComparison_surjective O hu A B⟩
    intro x y hxy
    obtain ⟨p, rfl⟩ := Quotient.exists_rep x
    obtain ⟨q, rfl⟩ := Quotient.exists_rep y
    have hctx : CtxEquiv O p q := Quotient.exact' hxy
    exact Quotient.sound' ((hpc p q).mp hctx)
  · intro hbij A B p q
    constructor
    · intro hctx
      have h1 : parallelComparison O hu A B (Quotient.mk _ p)
          = parallelComparison O hu A B (Quotient.mk _ q) :=
        Quotient.sound' hctx
      exact Quotient.exact' ((hbij A B).1 h1)
    · intro hcc
      exact cctxEquiv_implies_ctxEquiv hcc (hu B)

open scoped ComplexOrder in
/-- **Definition `def:ancillary-stability`**: a deterministic
predictive transformation is completely ancillary stable when for
every `k ≥ 1` its extension by the identity on a `k`-level complex
ancilla `id_{M_k} ⊗ Φ` preserves positivity. -/
def IsCompletelyAncillaryStable {n m : ℕ}
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    Prop :=
  ∀ (k : ℕ) (X : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ),
    X.PosSemidef → (ampliate k Φ X).PosSemidef

/-- Complete ancillary stability is definitionally matrix complete
positivity. -/
theorem isCompletelyAncillaryStable_iff_matrixCP {n m : ℕ}
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    IsCompletelyAncillaryStable Φ ↔ IsMatrixCompletelyPositive Φ :=
  Iff.rfl

open scoped ComplexOrder in
/-- Complete ancillary stability is equivalent to positivity of the
Choi matrix (`thm:choi` applied to `def:ancillary-stability`). -/
theorem isCompletelyAncillaryStable_iff_choi {n m : ℕ}
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    IsCompletelyAncillaryStable Φ ↔ (choiMatrix Φ).PosSemidef :=
  (isCompletelyAncillaryStable_iff_matrixCP Φ).trans
    (choi_criterion Φ)

/-- **Definition `def:logical-roles`**: the four logical roles of
hypotheses in the reconstruction — foundational axiom, microscopic
model specification, phase criterion, and physical selection. -/
inductive LogicalRole : Type
  | foundationalAxiom
  | modelSpecification
  | phaseCriterion
  | physicalSelection
  deriving DecidableEq, Repr

/-- A role assignment tags every hypothesis of a development with
exactly one logical role. -/
structure RoleAssignment (H : Type*) where
  /-- The role of each hypothesis. -/
  role : H → LogicalRole

/-- The four roles are exhaustive. -/
theorem LogicalRole.role_cases (r : LogicalRole) :
    r = foundationalAxiom ∨ r = modelSpecification
      ∨ r = phaseCriterion ∨ r = physicalSelection := by
  cases r
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

end NCG.Upstream
