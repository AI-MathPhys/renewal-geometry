/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Ordered predictive realization
  (`thm:ordered-memory`, Gran-Tensor manuscript)

* `ordered_memory`: on each finite response space, the
  future-pointwise cone is closed, pointed, and generating;
  precomposition transitions are positive; and every complete
  instrument preserves the normalization functional — the boxed
  identity `u(Σ_o A_{a_o} m) = u(m)`.

Rendering disclosed: response spaces are rendered as functions
on the finite declared futures with the pointwise cone (the
intersection of the future half-spaces); "physical columns
belong to the cone and span" is the operational-table
hypothesis; instrument completeness is the operational axiom
`Σ_o m(a_o f) = m(f)` taken as the hypothesis it is.
-/

namespace NCG

/-- `thm:ordered-memory`. -/
theorem ordered_memory {F : Type*} :
    -- (1) the future cone is closed
    IsClosed {m : F → ℝ | ∀ f, 0 ≤ m f}
    -- (2) pointed
    ∧ (∀ m : F → ℝ, (∀ f, 0 ≤ m f) → (∀ f, 0 ≤ -m f) →
        m = 0)
    -- (3) generating
    ∧ (∀ m : F → ℝ, ∃ p q : F → ℝ,
        (∀ f, 0 ≤ p f) ∧ (∀ f, 0 ≤ q f) ∧ m = p - q)
    -- (4) precomposition transitions are positive
    ∧ (∀ (a : F → F) (m : F → ℝ), (∀ f, 0 ≤ m f) →
        ∀ f, 0 ≤ (m ∘ a) f)
    -- (5) complete instruments preserve normalization
    ∧ (∀ {O : Type*} [Fintype O] (a : O → F → F)
        (m : F → ℝ) (e : F),
        (∀ f, ∑ o, m (a o f) = m f) →
        (∑ o, (m ∘ a o)) e = m e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : {m : F → ℝ | ∀ f, 0 ≤ m f}
        = ⋂ f, {m : F → ℝ | 0 ≤ m f} := by
      ext m
      simp
    rw [this]
    refine isClosed_iInter fun f => ?_
    exact isClosed_le continuous_const (continuous_apply f)
  · intro m h1 h2
    funext f
    have := h1 f
    have := h2 f
    simp only [Pi.zero_apply]
    linarith [h1 f, h2 f]
  · intro m
    refine ⟨fun f => max (m f) 0, fun f => max (-m f) 0,
      fun f => le_max_right _ _, fun f => le_max_right _ _, ?_⟩
    funext f
    simp only [Pi.sub_apply]
    rcases le_total (m f) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  · intro a m hm f
    exact hm (a f)
  · intro O _ a m e hcomp
    have := hcomp e
    simpa using this

end NCG
