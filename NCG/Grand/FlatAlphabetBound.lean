/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Flat depth requires alphabet control
  (`thm:flat-alphabet-bound`, Gran-Tensor manuscript)

* `flat_alphabet_bound`: a history algebra spanned by words of
  length ≤ r in m primitive letters has dimension at most
  `1 + m + ⋯ + m^r`; bounded nondecreasing dimensions of an
  injective cutoff system stabilize; and the coordinate algebra
  `ℂ^X` is flat at depth one with diverging dimension, so
  uniform flat depth alone is insufficient.

Rendering disclosed: flatness by depth `r` is rendered as the
word-span hypothesis; "injective maps between equal finite
dimensions are isomorphisms" is the standard finite-dimensional
fact packaged in the stabilization clause.
-/

namespace NCG

/-- `thm:flat-alphabet-bound`. -/
theorem flat_alphabet_bound :
    -- (1) word-span dimension bound
    (∀ {A : Type*} [AddCommGroup A] [Module ℂ A] (m r : ℕ)
      (v : (Σ k : Fin (r + 1), (Fin k → Fin m)) → A),
      Submodule.span ℂ (Set.range v) = ⊤ →
      Module.finrank ℂ A
        ≤ ∑ k ∈ Finset.range (r + 1), m ^ k)
    -- (2) bounded monotone dimensions stabilize
    ∧ (∀ (dim : ℕ → ℕ) (K : ℕ), Monotone dim →
        (∀ n, dim n ≤ K) →
        ∃ N, ∀ n, N ≤ n → dim n = dim N)
    -- (3) the coordinate counterexample: flat at depth one,
    --     diverging dimension
    ∧ (∀ X : ℕ,
        (∀ i j : Fin X,
          (Pi.single i 1 : Fin X → ℂ) * Pi.single j 1
            = if i = j then Pi.single i 1 else 0)
        ∧ Submodule.span ℂ
            (Set.range fun i : Fin X =>
              (Pi.single i 1 : Fin X → ℂ)) = ⊤
        ∧ Module.finrank ℂ (Fin X → ℂ) = X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A _ _ m r v hspan
    classical
    have h1 : Module.finrank ℂ A
        = Module.finrank ℂ (⊤ : Submodule ℂ A) :=
      (finrank_top ℂ A).symm
    rw [h1, ← hspan]
    calc Module.finrank ℂ (Submodule.span ℂ (Set.range v))
        ≤ (Set.range v).toFinset.card :=
          finrank_span_le_card (Set.range v)
      _ ≤ Fintype.card (Σ k : Fin (r + 1), (Fin k → Fin m)) := by
          rw [Set.toFinset_range]
          exact Finset.card_image_le.trans
            (by rw [Finset.card_univ])
      _ = ∑ k ∈ Finset.range (r + 1), m ^ k := by
          rw [Fintype.card_sigma]
          rw [Fin.sum_univ_eq_sum_range
            (fun k => Fintype.card (Fin k → Fin m))]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp
  · intro dim K hmono hbound
    by_contra h
    push Not at h
    have key : ∀ k, ∃ n, k ≤ dim n := by
      intro k
      induction k with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ k ihk =>
          obtain ⟨n, hn⟩ := ihk
          obtain ⟨m, hm, hne⟩ := h n
          have hmn := hmono hm
          exact ⟨m, by omega⟩
    obtain ⟨n, hn⟩ := key (K + 1)
    exact absurd (hbound n) (by omega)
  · intro X
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        funext x
        by_cases hx : x = i
        · subst hx
          simp
        · simp [hx]
      · rw [if_neg hij]
        funext x
        by_cases hx : x = i
        · subst hx
          simp [Ne.symm hij]
        · simp [hx]
    · have hfun : (fun i : Fin X =>
          (Pi.single i 1 : Fin X → ℂ))
          = ⇑(Pi.basisFun ℂ (Fin X)) := by
        funext i
        rw [Pi.basisFun_apply]
      rw [hfun]
      exact (Pi.basisFun ℂ (Fin X)).span_eq
    · simp

end NCG
