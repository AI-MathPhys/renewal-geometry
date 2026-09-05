/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DimensionPairwise

/-!
# Exact future-minimal serial relation cells

This supplies the first two clauses of the dimension pairwise-completion
theorem: literal two-endpoint incidence and the future-minimal alternative for
parallel relation letters.  The existing orbit theorem supplies clause (iii).
-/

namespace NCG

/-- A finite serial relation alphabet with executable reversal and a complete
future signature. -/
structure FutureMinimalSerialCell (X A F : Type*) where
  source : A → X
  target : A → X
  source_ne_target : ∀ a, source a ≠ target a
  reverse : A → A
  reverse_source : ∀ a, source (reverse a) = target a
  reverse_target : ∀ a, target (reverse a) = source a
  reverse_involutive : Function.Involutive reverse
  future : A → F

namespace FutureMinimalSerialCell

variable {X A F : Type*} [DecidableEq X]

/-- The oriented incidence vector of one primitive serial relation. -/
def boundary (C : FutureMinimalSerialCell X A F) (a : A) : X → ℤ :=
  Pi.single (C.target a) 1 - Pi.single (C.source a) 1

/-- Future equivalence is equality of the complete future signature. -/
def futureSetoid (C : FutureMinimalSerialCell X A F) : Setoid A where
  r a b := C.future a = C.future b
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h g => h.trans g⟩

/-- The actual future-minimal relation record. -/
abbrev MinimalRecord (C : FutureMinimalSerialCell X A F) :=
  Quotient C.futureSetoid

/-- Each primitive boundary has exactly one target coefficient `+1`, one
source coefficient `-1`, and no other support. -/
theorem boundary_is_oriented_edge (C : FutureMinimalSerialCell X A F) (a : A) :
    C.boundary a (C.target a) = 1
    ∧ C.boundary a (C.source a) = -1
    ∧ ∀ x, x ≠ C.source a → x ≠ C.target a →
      C.boundary a x = 0 := by
  have hts : C.target a ≠ C.source a := (C.source_ne_target a).symm
  refine ⟨?_, ?_, ?_⟩
  · simp [boundary, Pi.single_apply, hts]
  · simp [boundary, Pi.single_apply, C.source_ne_target a]
  · intro x hxs hxt
    simp [boundary, Pi.single_apply, hxs, hxt]

/-- Executable reversal negates the oriented incidence vector. -/
theorem boundary_reverse (C : FutureMinimalSerialCell X A F) (a : A) :
    C.boundary (C.reverse a) = -C.boundary a := by
  funext x
  simp only [boundary, C.reverse_source, C.reverse_target, Pi.neg_apply, Pi.sub_apply]
  ring

/-- Two parallel letters are either the same future-minimal record, or the
complete future Read itself distinguishes them. -/
theorem parallel_identified_or_relation_colour
    (C : FutureMinimalSerialCell X A F) (a b : A)
    (_hsource : C.source a = C.source b)
    (_htarget : C.target a = C.target b) :
    Quotient.mk C.futureSetoid a = Quotient.mk C.futureSetoid b
      ∨ ∃ read : A → F, read = C.future ∧ read a ≠ read b := by
  by_cases h : C.future a = C.future b
  · exact Or.inl (Quotient.sound h)
  · exact Or.inr ⟨C.future, rfl, h⟩

/-- Exact three-clause package for `thm:dimension-pairwise-completion`. -/
theorem dimension_pairwise_completion_exact
    (C : FutureMinimalSerialCell X A F)
    {Gamma : Subgroup (Equiv.Perm X)} {R : Set (Sym2 X)}
    (htrans : ∀ p q : Sym2 X, ¬p.IsDiag → ¬q.IsDiag →
      ∃ g ∈ Gamma, Sym2.map (⇑g) p = q)
    (hRinv : ∀ g ∈ Gamma, ∀ p ∈ R, Sym2.map (⇑g) p ∈ R)
    (hne : ∃ p ∈ R, ¬p.IsDiag) :
    (∀ a, C.boundary a (C.target a) = 1
      ∧ C.boundary a (C.source a) = -1
      ∧ ∀ x, x ≠ C.source a → x ≠ C.target a →
        C.boundary a x = 0)
    ∧ (∀ a b, C.source a = C.source b →
        C.target a = C.target b →
        Quotient.mk C.futureSetoid a = Quotient.mk C.futureSetoid b
          ∨ ∃ read : A → F, read = C.future ∧ read a ≠ read b)
    ∧ ∀ q : Sym2 X, ¬q.IsDiag → q ∈ R := by
  exact ⟨C.boundary_is_oriented_edge,
    fun a b hs ht => C.parallel_identified_or_relation_colour a b hs ht,
    dimension_pairwise_completion Gamma R htrans hRinv hne⟩

end FutureMinimalSerialCell
end NCG
