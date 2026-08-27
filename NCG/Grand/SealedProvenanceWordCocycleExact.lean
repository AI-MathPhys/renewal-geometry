/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SealedProvenanceQuotient

/-!
# All-word sealed-provenance cocycle

This exposes the manuscript theorem at its actual free-monoid quantification,
including the centered passive response for every pair of words.
-/

open Matrix

namespace NCG

variable {sigma iota l e y : Type*} [Fintype l] [Fintype e]
  [DecidableEq l] [DecidableEq e]

/-- `thm:sealed-provenance-cocycle` with its full all-word quantifiers. -/
theorem sealed_provenance_word_cocycle_exact
    (T : sigma → Matrix l l ℂ) (C : sigma → Matrix e l ℂ)
    (Dm : sigma → Matrix e e ℂ) (R : iota → Matrix y e ℂ) :
    (∀ v w : List sigma,
      wordH T C Dm (v ++ w) =
          wordH T C Dm v * wordT T w +
            wordD Dm v * wordH T C Dm w
      ∧ wordD Dm (v ++ w) = wordD Dm v * wordD Dm w)
    ∧ (∀ (lam : iota) (v w : List sigma),
      R lam * wordH T C Dm (v ++ w) -
          R lam * wordH T C Dm v * wordT T w =
        R lam * wordD Dm v * wordH T C Dm w) := by
  have hq := sealed_provenance_quotient T C Dm R
  have hD := hq.2.1
  have hH := hq.2.2.1
  constructor
  · intro v w
    exact ⟨hH v w, hD v w⟩
  · intro lam v w
    rw [hH, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    abel

end NCG
