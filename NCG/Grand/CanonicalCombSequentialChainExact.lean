/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CanonicalPrefixPurificationUniqueness
import NCG.Grand.CombDilation

/-!
# All-depth sequential chain for the canonical comb dilation

The prefix-purification module constructs each support-minimal link and proves uniqueness of
its memory gauge.  `CombDilation` verifies the two-link matrix identity.  This file supplies
the missing induction for an arbitrary finite, dependently typed chain of memory carriers.

The result is categorical and therefore applies directly to the varying spaces
`H_{2k-2} ⊗ A_{k-1}` and `H_{2k-1} ⊗ A_k`: linkwise isometries compose to an isometry, and
dressing each link by adjacent memory gauges telescopes to the two endpoint gauges only.
-/

namespace NCG
namespace CanonicalCombSequentialChain

universe u

variable {X : ℕ → Type u}

/-- Ordered composition of the first `n` links of a dependently typed sequential dilation. -/
def sequentialChain (V : ∀ k, X k → X (k + 1)) :
    ∀ n, X 0 → X n
  | 0 => id
  | n + 1 => V n ∘ sequentialChain V n

@[simp] theorem sequentialChain_zero (V : ∀ k, X k → X (k + 1)) :
    sequentialChain V 0 = id := rfl

@[simp] theorem sequentialChain_succ (V : ∀ k, X k → X (k + 1)) (n : ℕ) :
    sequentialChain V (n + 1) = V n ∘ sequentialChain V n := rfl

/-- Adjacent gauge dressing of one sequential link. -/
def dressedLink (V : ∀ k, X k → X (k + 1)) (U : ∀ k, X k ≃ X k)
    (k : ℕ) : X k → X (k + 1) :=
  U (k + 1) ∘ V k ∘ (U k).symm

/-- **All-depth gauge telescoping.** Dressing every link by adjacent memory gauges leaves
only the terminal gauge and the inverse initial gauge on the complete sequential chain. -/
theorem sequentialChain_dressed
    (V : ∀ k, X k → X (k + 1)) (U : ∀ k, X k ≃ X k) (n : ℕ) :
    sequentialChain (dressedLink V U) n =
      U n ∘ sequentialChain V n ∘ (U 0).symm := by
  funext x
  induction n with
  | zero => simp [sequentialChain]
  | succ n ih =>
      simp only [sequentialChain_succ, Function.comp_apply, dressedLink]
      rw [ih]
      simp

/-- Pointwise form of all-depth gauge telescoping. -/
theorem sequentialChain_dressed_apply
    (V : ∀ k, X k → X (k + 1)) (U : ∀ k, X k ≃ X k)
    (n : ℕ) (x : X 0) :
    sequentialChain (dressedLink V U) n x =
      U n (sequentialChain V n ((U 0).symm x)) := by
  rw [sequentialChain_dressed V U n]
  rfl

/-! ## Isometric links -/

variable [∀ k, MetricSpace (X k)]

/-- A chain of isometric prefix links is isometric at every finite depth. -/
theorem sequentialChain_isometry
    (V : ∀ k, X k → X (k + 1)) (hV : ∀ k, Isometry (V k)) (n : ℕ) :
    Isometry (sequentialChain V n) := by
  induction n with
  | zero => exact isometry_id
  | succ n ih => exact (hV n).comp ih

/-- Hence the all-depth chain is injective, the finite-memory version of lossless sequential
linking before the final memory trace. -/
theorem sequentialChain_injective
    (V : ∀ k, X k → X (k + 1)) (hV : ∀ k, Isometry (V k)) (n : ℕ) :
    Function.Injective (sequentialChain V n) :=
  (sequentialChain_isometry V hV n).injective

/-! ## Transport of terminal data -/

variable {Y : Type*}

/-- Every terminal quantity invariant under the unique terminal memory gauge has the same
value on the two support-minimal sequential realizations (up to the initial gauge). -/
theorem terminal_invariant_of_dressed_chain
    (V : ∀ k, X k → X (k + 1)) (U : ∀ k, X k ≃ X k)
    (terminal : X n → Y) (hinv : ∀ z, terminal (U n z) = terminal z)
    (x : X 0) :
    terminal (sequentialChain (dressedLink V U) n x) =
      terminal (sequentialChain V n ((U 0).symm x)) := by
  rw [sequentialChain_dressed_apply]
  exact hinv _

/-- If the scalar initial memory is fixed, every gauge-invariant terminal quantity is exactly
unchanged by the unique linkwise memory gauges. -/
theorem terminal_invariant_of_fixed_initial_memory
    (V : ∀ k, X k → X (k + 1)) (U : ∀ k, X k ≃ X k)
    (hU0 : U 0 = Equiv.refl (X 0))
    (terminal : X n → Y) (hinv : ∀ z, terminal (U n z) = terminal z)
    (x : X 0) :
    terminal (sequentialChain (dressedLink V U) n x) =
      terminal (sequentialChain V n x) := by
  rw [terminal_invariant_of_dressed_chain V U terminal hinv x, hU0]
  rfl

/-! ## Simultaneous selection of the canonical prefix links -/

/-- Per-prefix existence of a support-minimal link selects one coherent indexed family of
links.  Combined with `sequentialChain`, this is the finite sequential realization rather
than a collection of unrelated one-step witnesses. -/
theorem choose_all_prefix_links
    (Good : ∀ k, (X k → X (k + 1)) → Prop)
    (hexists : ∀ k, ∃ V, Good k V) :
    ∃ V : ∀ k, X k → X (k + 1), ∀ k, Good k (V k) := by
  choose V hV using hexists
  exact ⟨V, hV⟩

/-- Complete all-depth comb packet: a family selected from the prefix dilation witnesses
forms an isometric sequential chain at every depth and satisfies endpoint-only gauge
telescoping for every alternative support-minimal gauge family. -/
theorem canonical_comb_all_depth_chain
    (Good : ∀ k, (X k → X (k + 1)) → Prop)
    (hexists : ∀ k, ∃ V, Good k V ∧ Isometry V) :
    ∃ V : ∀ k, X k → X (k + 1),
      (∀ k, Good k (V k)) ∧
      (∀ n, Isometry (sequentialChain V n)) ∧
      (∀ (U : ∀ k, X k ≃ X k) n,
        sequentialChain (dressedLink V U) n =
          U n ∘ sequentialChain V n ∘ (U 0).symm) := by
  choose V hGood hIso using hexists
  exact ⟨V, hGood, sequentialChain_isometry V hIso,
    fun U n => sequentialChain_dressed V U n⟩

end CanonicalCombSequentialChain
end NCG
