/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# One-shell exactness does not imply projected nesting

A typed retained/tail model for `cth:GT-one-shell-no-nesting`.
-/

namespace NCG
namespace OneShellNestingCounterexample

/-- Data of two one-shell maps with an intermediate tail channel. -/
structure TwoShellModel (Command Retained Tail : Type*) where
  firstRetained : Command → Retained
  firstTail : Command → Tail
  secondRetained : Retained → Tail → Retained
  zeroTail : Tail

def directTwoShell {C R T : Type*} (M : TwoShellModel C R T) (c : C) : R :=
  M.secondRetained (M.firstRetained c) (M.firstTail c)

def tailDeletedTwoShell {C R T : Type*} (M : TwoShellModel C R T) (c : C) : R :=
  M.secondRetained (M.firstRetained c) M.zeroTail

/-- The one-dimensional manuscript witness. -/
def additiveTwoShell : TwoShellModel ℝ ℝ ℝ where
  firstRetained := id
  firstTail := id
  secondRetained := fun x r ↦ x + r
  zeroTail := 0

/-- `cth:GT-one-shell-no-nesting`: both retained one-shell maps are represented
exactly, but direct composition and deletion of the intermediate tail give
`2c` and `c`, respectively. -/
theorem exact_one_shells_do_not_force_projected_nesting :
    (∀ c, additiveTwoShell.firstRetained c = c)
      ∧ (∀ x r, additiveTwoShell.secondRetained x r = x + r)
      ∧ (∀ c, directTwoShell additiveTwoShell c = 2 * c)
      ∧ (∀ c, tailDeletedTwoShell additiveTwoShell c = c)
      ∧ (∀ {c}, c ≠ 0 →
          directTwoShell additiveTwoShell c ≠ tailDeletedTwoShell additiveTwoShell c) := by
  refine ⟨fun _ ↦ rfl, fun _ _ ↦ rfl, ?_, ?_, ?_⟩
  · intro c
    simp [directTwoShell, additiveTwoShell]
    ring
  · intro c
    simp [tailDeletedTwoShell, additiveTwoShell]
  · intro c hc heq
    simp [directTwoShell, tailDeletedTwoShell, additiveTwoShell] at heq
    apply hc
    linarith

end OneShellNestingCounterexample
end NCG
