/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.WordLocalizerScoreAndInfluence

/-!
# Adaptive word-localizer stop: invariance, generated carrier, termination

Exact abstract encoding of `thm:GT-adaptive-word-localizer-stop`.

Letters act by linear maps `L a : E →ₗ[ℂ] E` on a finite-dimensional
coefficient space; the source is a submodule `V`; the generated word carrier
is `generatedCarrier L V = ⨆_w (word w) V`.

* `generatedCarrier_le_of_invariant`: every letter-invariant submodule
  containing the source contains the generated carrier;
* `represented_eq_generated_of_stop` (NL.4j): if the represented span
  contains the source, is contained in the generated carrier, and every
  one-letter extension of it lies in it (zero word innovation), then it **is**
  the complete generated word carrier;
* `innovation_pos_of_missing_direction` (converse): a generated direction
  missing from the represented span forces some one-letter extension to leave
  the span;
* termination: `strict_rounds_le` — each strict round raises the finite
  dimension by at least one, so at most `finrank E - finrank (initial)`
  strict rounds occur (the rank bookkeeping of
  `WordLocalizerScoreAndInfluence.adaptive_word_strict_increment_bound`).
The held-out test and the action-compatibility clause are
`cor:GT-flat-word-action-compatibility` (proved separately).
-/

open Submodule

namespace NCG
namespace AdaptiveWordLocalizerStop

variable {ι E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The linear map of a word (list of letters), applied right to left. -/
def wordMap (L : ι → E →ₗ[ℂ] E) : List ι → E →ₗ[ℂ] E
  | [] => LinearMap.id
  | a :: w => L a ∘ₗ wordMap L w

/-- The generated word carrier `⨆_w (word w)(V)`. -/
def generatedCarrier (L : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) : Submodule ℂ E :=
  ⨆ w : List ι, V.map (wordMap L w)

theorem source_le_generatedCarrier (L : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) :
    V ≤ generatedCarrier L V := by
  have : V.map (wordMap L []) ≤ generatedCarrier L V := le_iSup (fun w => V.map (wordMap L w)) []
  simpa [wordMap] using this

/-- The generated carrier is invariant under every letter. -/
theorem generatedCarrier_invariant (L : ι → E →ₗ[ℂ] E) (V : Submodule ℂ E) (a : ι) :
    (generatedCarrier L V).map (L a) ≤ generatedCarrier L V := by
  unfold generatedCarrier
  rw [Submodule.map_iSup]
  refine iSup_le fun w => ?_
  rw [← Submodule.map_comp]
  exact le_iSup (fun w => V.map (wordMap L w)) (a :: w)

/-- **Minimality**: a letter-invariant submodule containing the source contains
the generated carrier. -/
theorem generatedCarrier_le_of_invariant (L : ι → E →ₗ[ℂ] E) (V M : Submodule ℂ E)
    (hV : V ≤ M) (hinv : ∀ a, M.map (L a) ≤ M) : generatedCarrier L V ≤ M := by
  refine iSup_le fun w => ?_
  induction w with
  | nil => simpa [wordMap] using hV
  | cons a w ih =>
    calc V.map (wordMap L (a :: w)) = (V.map (wordMap L w)).map (L a) := by
          simp [wordMap, Submodule.map_comp]
      _ ≤ M.map (L a) := Submodule.map_mono ih
      _ ≤ M := hinv a

/-- **(NL.4j) zero innovation is a genuine stop**: if the represented span
`M` contains the source, lies inside the generated carrier, and every
one-letter extension of `M` lies in `M`, then `M` is the complete generated
word carrier. -/
theorem represented_eq_generated_of_stop (L : ι → E →ₗ[ℂ] E) (V M : Submodule ℂ E)
    (hV : V ≤ M) (hM : M ≤ generatedCarrier L V) (hstop : ∀ a, M.map (L a) ≤ M) :
    M = generatedCarrier L V :=
  le_antisymm hM (generatedCarrier_le_of_invariant L V M hV hstop)

/-- **Converse**: a missing generated direction forces a positive one-letter
innovation (some extension of the represented span leaves it). -/
theorem innovation_pos_of_missing_direction (L : ι → E →ₗ[ℂ] E) (V M : Submodule ℂ E)
    (hV : V ≤ M) (hmiss : ¬ generatedCarrier L V ≤ M) :
    ∃ a, ¬ M.map (L a) ≤ M := by
  by_contra hcon
  push Not at hcon
  exact hmiss (generatedCarrier_le_of_invariant L V M hV hcon)

/-- **Termination**: a chain of represented spans in which every round is a
strict inclusion has length at most `finrank E - finrank M₀`. -/
theorem strict_rounds_le [FiniteDimensional ℂ E] (M : ℕ → Submodule ℂ E)
    (hstrict : ∀ n, M n < M (n + 1)) (n : ℕ) :
    n ≤ Module.finrank ℂ E - Module.finrank ℂ (M 0) := by
  have hgrow : ∀ k, Module.finrank ℂ (M 0) + k ≤ Module.finrank ℂ (M k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := Submodule.finrank_lt_finrank_of_lt (hstrict k)
      omega
  have hle := Submodule.finrank_le (M n)
  have := hgrow n
  omega

/-- The rank bookkeeping of one round: a nonzero innovation of rank `r` raises
the represented dimension by exactly `r`, and the remaining budget drops by
`r` (`WordLocalizerScoreAndInfluence.adaptive_word_rank_accounting`). -/
theorem round_budget (ambient represented innovation : ℕ)
    (hfit : represented + innovation ≤ ambient) :
    ambient - (represented + innovation) = (ambient - represented) - innovation :=
  WordLocalizerScoreAndInfluence.adaptive_word_rank_accounting ambient represented innovation hfit

end AdaptiveWordLocalizerStop
end NCG
