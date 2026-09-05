/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GeneratedMinimalRecord

/-!
# Algebraic decomposition of unread record fibres

The record-refinement theorem already constructs the canonical set
decomposition into fibres.  Here it is lifted to the literal complex function
algebras, and a chosen constant-fibre trivialization is shown to give the
base-preserving product decomposition claimed in the manuscript.
-/

namespace NCG

/-- Pullback along an equivalence gives the corresponding equivalence of
complex function algebras. -/
def functionAlgebraEquiv {X Y : Type*} (e : X ≃ Y) :
    (X → ℂ) ≃ₐ[ℂ] (Y → ℂ) where
  toFun f := f ∘ e.symm
  invFun g := g ∘ e
  left_inv f := by funext x; simp
  right_inv g := by funext y; simp
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' c := rfl

/-- The boxed fibrewise algebra decomposition
`C(R) ≅ ∏_ρ C(q⁻¹(ρ))`.  For a finite discrete record this dependent
product is the manuscript's finite direct sum. -/
def recordFibreFunctionAlgebraEquiv {R Q : Type*} (q : R → Q) :
    (R → ℂ) ≃ₐ[ℂ]
      ((ρ : Q) → {r : R // q r = ρ} → ℂ) where
  toFun f ρ r := f r.1
  invFun g r := g (q r) ⟨r, rfl⟩
  left_inv f := rfl
  right_inv g := by
    funext ρ r
    rcases r with ⟨r, rfl⟩
    rfl
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' c := rfl

/-- Chosen fibre trivializations assemble to a base-preserving equivalence
`R ≃ Q × D`. -/
def recordBaseProductEquiv {R Q D : Type*} (q : R → Q)
    (e : ∀ ρ : Q, {r : R // q r = ρ} ≃ D) : R ≃ Q × D :=
  (Equiv.sigmaFiberEquiv q).symm |>.trans
    (Equiv.sigmaCongrRight e) |>.trans
      (Equiv.sigmaEquivProd Q D)
/-- The induced base-preserving algebra product decomposition. -/
def recordBaseProductFunctionAlgebraEquiv {R Q D : Type*} (q : R → Q)
    (e : ∀ ρ : Q, {r : R // q r = ρ} ≃ D) :
    (R → ℂ) ≃ₐ[ℂ] (Q × D → ℂ) :=
  functionAlgebraEquiv (recordBaseProductEquiv q e)

/-- Under the product decomposition, a pullback from the minimal base is
exactly constant in the unread fibre coordinate. -/
theorem recordBaseProductFunctionAlgebraEquiv_pullback
    {R Q D : Type*} (q : R → Q)
    (e : ∀ ρ : Q, {r : R // q r = ρ} ≃ D) (g : Q → ℂ) :
    recordBaseProductFunctionAlgebraEquiv q e (g ∘ q) =
      fun p : Q × D => g p.1 := by
  funext p
  rcases p with ⟨ρ, d⟩
  change g (q ((e ρ).symm d).1) = g ρ
  rw [((e ρ).symm d).2]

/-- Exact algebra-level completion of the unread-refinement bundle: canonical
minimal-record equivalence, the literal fibre function-algebra decomposition,
and a base-preserving product algebra whenever all fibres are trivialized by
one type `E`. -/
theorem record_refinement_algebra_bundle_exact
    {A R' R D V : Type*}
    (M' : WordRecordMachine A R' D V)
    (M : WordRecordMachine A R D V) (π : R' → R)
    (hπ : Function.Surjective π)
    (hstep : ∀ a r, π (M'.step a r) = M.step a (π r))
    (hread : ∀ d r, M'.read d r = M.read d (π r)) :
    Nonempty (MinRec M'.futureSig ≃ MinRec M.futureSig)
      ∧ Nonempty ((R → ℂ) ≃ₐ[ℂ]
        ((ρ : MinRec M.futureSig) →
          {r : R // Quotient.mk (minRecSetoid M.futureSig) r = ρ} → ℂ))
      ∧ ∀ (E : Type*)
          (e : ∀ ρ : MinRec M.futureSig,
            {r : R // Quotient.mk (minRecSetoid M.futureSig) r = ρ} ≃ E),
        Nonempty ((R → ℂ) ≃ₐ[ℂ] (MinRec M.futureSig × E → ℂ)) := by
  refine ⟨(WordRecordMachine.record_refinement_bundle_exact
    M' M π hπ hstep hread).1,
    ⟨recordFibreFunctionAlgebraEquiv
      (fun r => Quotient.mk (minRecSetoid M.futureSig) r)⟩, ?_⟩
  intro E e
  exact ⟨recordBaseProductFunctionAlgebraEquiv
    (fun r => Quotient.mk (minRecSetoid M.futureSig) r) e⟩

end NCG
