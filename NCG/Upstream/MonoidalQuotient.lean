/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The symmetric monoidal quotient category

Covers `thm:universal-quotient` from `manuscripts/renewal_emergence/renewal_emergence.tex`: for a
**monoidal congruence** — a hom relation stable under both
whiskerings (`MonoidalHomRel`) — the quotient category
`CategoryTheory.Quotient r` carries a symmetric monoidal structure
descending the one on `P`:

* `instMonoidalCategoryQuotient` — `Q_pred = C_G/≡∥` **is** a
  monoidal category: tensor descends to classes because the
  congruence is monoidal, and all coherence laws descend along the
  full quotient functor;
* `instSymmetricCategoryQuotient` — the braiding descends, so the
  quotient is symmetric monoidal;
* the **universal property** is Mathlib's `Quotient.lift` /
  `lift_spec` / `lift_unique`: every functor constant on complete
  contextual classes factors uniquely through the quotient functor;
* `quotient_iso_of_rel_iff` — if two congruences coincide (the
  parallel-completeness hypothesis `≡₁ = ≡∥`), the two quotient
  categories are **isomorphic**: the induced comparison functors
  compose to the identity in both directions.

Instantiation: `P = C_G` with `r = CCtxEquiv` (the parallel setoid
`cctxSetoid` of `NCG/Upstream/ProcessCompleteness.lean`); the
`MonoidalHomRel` instance for `CCtxEquiv` is the tensor-stability
clause of `thm:parallel-completion`.
-/

namespace NCG.Upstream

open CategoryTheory MonoidalCategory

variable {P : Type*} [Category P] [MonoidalCategory P]

/-- A **monoidal congruence**: a hom relation stable under both
whiskerings.  For the parallel equivalence `≡∥` this is the
tensor-stability clause of `thm:parallel-completion`. -/
class MonoidalHomRel (r : HomRel P) : Prop where
  /-- Stability under left whiskering. -/
  whiskerLeft_rel : ∀ (X : P) {Y Z : P} {f g : Y ⟶ Z},
    r f g → r (X ◁ f) (X ◁ g)
  /-- Stability under right whiskering. -/
  whiskerRight_rel : ∀ {Y Z : P} {f g : Y ⟶ Z} (X : P),
    r f g → r (f ▷ X) (g ▷ X)

variable (r : HomRel P) [MonoidalHomRel r]

theorem compClosure_whiskerLeft (X : P) {Y Z : P} {f g : Y ⟶ Z}
    (h : HomRel.CompClosure r f g) :
    HomRel.CompClosure r (X ◁ f) (X ◁ g) := by
  obtain ⟨a, b, p, m₁, m₂, q, hm⟩ := h
  rw [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp]
  exact HomRel.CompClosure.intro _ _ _ _ _ _
    (MonoidalHomRel.whiskerLeft_rel _ hm)

theorem compClosure_whiskerRight {Y Z : P} {f g : Y ⟶ Z} (X : P)
    (h : HomRel.CompClosure r f g) :
    HomRel.CompClosure r (f ▷ X) (g ▷ X) := by
  obtain ⟨a, b, p, m₁, m₂, q, hm⟩ := h
  rw [MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight]
  exact HomRel.CompClosure.intro _ _ _ _ _ _
    (MonoidalHomRel.whiskerRight_rel _ hm)

/-- Left whiskering on the quotient. -/
def qWhiskerLeft (X : CategoryTheory.Quotient r)
    {Y Z : CategoryTheory.Quotient r} (f : Y ⟶ Z) :
    (CategoryTheory.Quotient.mk (r := r) (X.as ⊗ Y.as) : _) ⟶
      CategoryTheory.Quotient.mk (r := r) (X.as ⊗ Z.as) :=
  Quot.liftOn f (fun f' => Quot.mk _ (X.as ◁ f'))
    (fun _ _ h => Quot.sound (compClosure_whiskerLeft r X.as h))

/-- Right whiskering on the quotient. -/
def qWhiskerRight {Y Z : CategoryTheory.Quotient r} (f : Y ⟶ Z)
    (X : CategoryTheory.Quotient r) :
    (CategoryTheory.Quotient.mk (r := r) (Y.as ⊗ X.as) : _) ⟶
      CategoryTheory.Quotient.mk (r := r) (Z.as ⊗ X.as) :=
  Quot.liftOn f (fun f' => Quot.mk _ (f' ▷ X.as))
    (fun _ _ h => Quot.sound (compClosure_whiskerRight r X.as h))

instance monoidalQuotientStruct :
    MonoidalCategoryStruct (CategoryTheory.Quotient r) where
  tensorObj X Y := ⟨X.as ⊗ Y.as⟩
  whiskerLeft X _ _ f := qWhiskerLeft r X f
  whiskerRight f X := qWhiskerRight r f X
  tensorHom f g :=
    CategoryTheory.Quotient.comp r (qWhiskerRight r f _)
      (qWhiskerLeft r _ g)
  tensorUnit := ⟨𝟙_ P⟩
  associator X Y Z :=
    (CategoryTheory.Quotient.functor r).mapIso (α_ X.as Y.as Z.as)
  leftUnitor X :=
    (CategoryTheory.Quotient.functor r).mapIso (λ_ X.as)
  rightUnitor X :=
    (CategoryTheory.Quotient.functor r).mapIso (ρ_ X.as)

/-- **Theorem `thm:universal-quotient` (first assertion)**: the
quotient of a monoidal category by a monoidal congruence is a
monoidal category — the parallel congruence descends the tensor to
complete contextual classes, and every coherence law descends along
the full quotient functor. -/
instance monoidalQuotient :
    MonoidalCategory (CategoryTheory.Quotient r) where
  tensorHom_def := by
    rintro ⟨X₁⟩ ⟨Y₁⟩ ⟨X₂⟩ ⟨Y₂⟩ ⟨f⟩ ⟨g⟩
    rfl
  id_tensorHom_id := by
    rintro ⟨X₁⟩ ⟨X₂⟩
    show Quot.mk _ _ = Quot.mk _ _
    exact congrArg (Quot.mk _) (by cat_disch)
  tensorHom_comp_tensorHom := by
    rintro ⟨X₁⟩ ⟨Y₁⟩ ⟨Z₁⟩ ⟨X₂⟩ ⟨Y₂⟩ ⟨Z₂⟩ ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    show Quot.mk _ _ = Quot.mk _ _
    refine congrArg (Quot.mk _) ?_
    dsimp only
    rw [← MonoidalCategory.tensorHom_def,
      ← MonoidalCategory.tensorHom_def,
      ← MonoidalCategory.tensorHom_def]
    exact MonoidalCategory.tensorHom_comp_tensorHom f₁ f₂ g₁ g₂
  whiskerLeft_id := by
    rintro ⟨X⟩ ⟨Y⟩
    exact congrArg (Quot.mk _) (MonoidalCategory.whiskerLeft_id X Y)
  id_whiskerRight := by
    rintro ⟨X⟩ ⟨Y⟩
    exact congrArg (Quot.mk _) (MonoidalCategory.id_whiskerRight X Y)
  associator_naturality := by
    rintro ⟨X₁⟩ ⟨X₂⟩ ⟨X₃⟩ ⟨Y₁⟩ ⟨Y₂⟩ ⟨Y₃⟩ ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    show Quot.mk _ _ = Quot.mk _ _
    refine congrArg (Quot.mk _) ?_
    dsimp only
    rw [← MonoidalCategory.tensorHom_def,
      ← MonoidalCategory.tensorHom_def,
      ← MonoidalCategory.tensorHom_def,
      ← MonoidalCategory.tensorHom_def]
    exact MonoidalCategory.associator_naturality f₁ f₂ f₃
  leftUnitor_naturality := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩
    show CategoryTheory.Quotient.comp r _ _
      = CategoryTheory.Quotient.comp r _ _
    show Quot.mk _ _ = Quot.mk _ _
    exact congrArg (Quot.mk _)
      (MonoidalCategory.leftUnitor_naturality f)
  rightUnitor_naturality := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩
    show CategoryTheory.Quotient.comp r _ _
      = CategoryTheory.Quotient.comp r _ _
    show Quot.mk _ _ = Quot.mk _ _
    exact congrArg (Quot.mk _)
      (MonoidalCategory.rightUnitor_naturality f)
  pentagon := by
    rintro ⟨W⟩ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    show CategoryTheory.Quotient.comp r _ _
      = CategoryTheory.Quotient.comp r _ _
    show Quot.mk _ _ = Quot.mk _ _
    exact congrArg (Quot.mk _) (MonoidalCategory.pentagon W X Y Z)
  triangle := by
    rintro ⟨X⟩ ⟨Y⟩
    show CategoryTheory.Quotient.comp r _ _ = _
    show Quot.mk _ _ = Quot.mk _ _
    exact congrArg (Quot.mk _) (MonoidalCategory.triangle X Y)

section Symmetric

variable [SymmetricCategory P]

/-- **`thm:universal-quotient` (symmetric structure)**: the braiding
descends to the quotient. -/
instance braidedQuotient :
    BraidedCategory (CategoryTheory.Quotient r) where
  braiding X Y :=
    (CategoryTheory.Quotient.functor r).mapIso (β_ X.as Y.as)
  braiding_naturality_right := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩
    show CategoryTheory.Quotient.comp r _ _
      = CategoryTheory.Quotient.comp r _ _
    show Quot.mk _ _ = Quot.mk _ _
    exact congrArg (Quot.mk _)
      (BraidedCategory.braiding_naturality_right X f)
  braiding_naturality_left := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩ ⟨Z⟩
    show CategoryTheory.Quotient.comp r _ _
      = CategoryTheory.Quotient.comp r _ _
    show Quot.mk _ _ = Quot.mk _ _
    exact congrArg (Quot.mk _)
      (BraidedCategory.braiding_naturality_left f Z)
  hexagon_forward := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    show CategoryTheory.Quotient.comp r _ _
      = CategoryTheory.Quotient.comp r _ _
    show Quot.mk _ _ = Quot.mk _ _
    exact congrArg (Quot.mk _) (BraidedCategory.hexagon_forward X Y Z)
  hexagon_reverse := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    show CategoryTheory.Quotient.comp r _ _
      = CategoryTheory.Quotient.comp r _ _
    show Quot.mk _ _ = Quot.mk _ _
    exact congrArg (Quot.mk _) (BraidedCategory.hexagon_reverse X Y Z)

/-- **`thm:universal-quotient` (symmetry)**: the quotient of a
symmetric monoidal category by a monoidal congruence is symmetric
monoidal. -/
instance symmetricQuotient :
    SymmetricCategory (CategoryTheory.Quotient r) where
  symmetry := by
    rintro ⟨X⟩ ⟨Y⟩
    show CategoryTheory.Quotient.comp r _ _ = _
    show Quot.mk _ _ = Quot.mk _ _
    exact congrArg (Quot.mk _) (SymmetricCategory.symmetry X Y)

end Symmetric

/-! ## The parallel-completeness isomorphism -/

/-- The comparison functor between quotients by two congruences that
imply one another. -/
def quotientComparison {r r' : HomRel P}
    (h : ∀ ⦃X Y : P⦄ (f g : X ⟶ Y), r f g → r' f g) :
    CategoryTheory.Quotient r ⥤ CategoryTheory.Quotient r' :=
  CategoryTheory.Quotient.lift r (CategoryTheory.Quotient.functor r')
    (fun _ _ f g hr => CategoryTheory.Quotient.sound r' (h f g hr))

/-- **`thm:universal-quotient` (parallel-completeness
isomorphism)**: if the two kernel relations coincide — the
parallel-completeness hypothesis `≡₁ = ≡∥` — the comparison functors
compose to the identity in both directions: the quotients are
canonically **isomorphic** categories. -/
theorem quotient_iso_of_rel_iff {r r' : HomRel P}
    (h : ∀ ⦃X Y : P⦄ (f g : X ⟶ Y), r f g ↔ r' f g) :
    quotientComparison (fun _ _ f g hr => (h f g).mp hr) ⋙
        quotientComparison (fun _ _ f g hr => (h f g).mpr hr)
      = 𝟭 (CategoryTheory.Quotient r)
    ∧ quotientComparison (fun _ _ f g hr => (h f g).mpr hr) ⋙
        quotientComparison (fun _ _ f g hr => (h f g).mp hr)
      = 𝟭 (CategoryTheory.Quotient r') := by
  constructor
  · have h1 : CategoryTheory.Quotient.functor r ⋙
        (quotientComparison (fun _ _ f g hr => (h f g).mp hr) ⋙
          quotientComparison (fun _ _ f g hr => (h f g).mpr hr))
        = CategoryTheory.Quotient.functor r := rfl
    have h2 : CategoryTheory.Quotient.functor r ⋙
        𝟭 (CategoryTheory.Quotient r)
        = CategoryTheory.Quotient.functor r := rfl
    rw [CategoryTheory.Quotient.lift_unique r
        (CategoryTheory.Quotient.functor r)
        (fun _ _ f g hr => CategoryTheory.Quotient.sound r hr) _ h1,
      CategoryTheory.Quotient.lift_unique r
        (CategoryTheory.Quotient.functor r)
        (fun _ _ f g hr => CategoryTheory.Quotient.sound r hr) _ h2]
  · have h1 : CategoryTheory.Quotient.functor r' ⋙
        (quotientComparison (fun _ _ f g hr => (h f g).mpr hr) ⋙
          quotientComparison (fun _ _ f g hr => (h f g).mp hr))
        = CategoryTheory.Quotient.functor r' := rfl
    have h2 : CategoryTheory.Quotient.functor r' ⋙
        𝟭 (CategoryTheory.Quotient r')
        = CategoryTheory.Quotient.functor r' := rfl
    rw [CategoryTheory.Quotient.lift_unique r'
        (CategoryTheory.Quotient.functor r')
        (fun _ _ f g hr => CategoryTheory.Quotient.sound r' hr) _ h1,
      CategoryTheory.Quotient.lift_unique r'
        (CategoryTheory.Quotient.functor r')
        (fun _ _ f g hr => CategoryTheory.Quotient.sound r' hr) _ h2]

end NCG.Upstream
