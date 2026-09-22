/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.StandardModel.ConservativeResolvedGradingExtensions

/-!
# Word moments cannot manufacture an external shadow

`thm:external-shadow-no-go` of the spacetime--gauge duality manuscript: there
are conservative extensions of one historical process with identical
historical word algebra, multiplication table, complete word-Gram hierarchy
and resolved classical cylinder probabilities, but different values of a
proposed grading-changing cross block.  Hence no function of the old word
moments alone can recover such an external shadow.

The countermodel is the pair of conservative extensions of
`ConservativeResolvedGradingExtensions`: an arbitrary finite old letter
process `K` is tensored with an unread two-level spectator, and the new
letter is either the grading read `Z` (even extension) or the grading flip
`X` (odd extension).  Since the old letters are embedded by the same map in
both extensions, every historical word coincides *literally*
(`extendedOldWord_even_eq_odd`), so every word moment, the Gram hierarchy,
the multiplication table and all resolved cylinder entries agree; both Gram
hierarchies are twice the old Gram (`wordGram_even`, `wordGram_odd`).  The
proposed left-to-right cross block is zero in the even extension and nonzero
in the odd one.  The final clause states the no-go: no function of the old
word data (or of the word Gram hierarchy) returns the cross block of both
extensions (`external_shadow_no_go`).
-/

open Matrix Kronecker

namespace RenewalGeometry

variable {h ι : Type*} [Fintype h] [DecidableEq h]

/-- The represented historical word of an extended process: the product of
the images of the old letters only. -/
def extendedOldWord (P : ι ⊕ Unit → Matrix (h × Fin 2) (h × Fin 2) ℂ)
    (w : List ι) : Matrix (h × Fin 2) (h × Fin 2) ℂ :=
  (w.map (fun a => P (Sum.inl a))).prod

/-- The complete word-Gram hierarchy of an extended process, restricted to
historical words: `Tr(w₁ᴴ w₂)`. -/
noncomputable def wordGram (P : ι ⊕ Unit → Matrix (h × Fin 2) (h × Fin 2) ℂ)
    (w₁ w₂ : List ι) : ℂ :=
  Matrix.trace ((extendedOldWord P w₁)ᴴ * extendedOldWord P w₂)

/-- The proposed grading-changing cross block of the new letter: its
left-to-right compression. -/
def gradingCrossBlock (P : ι ⊕ Unit → Matrix (h × Fin 2) (h × Fin 2) ℂ) :
    Matrix (h × Fin 2) (h × Fin 2) ℂ :=
  ((1 : Matrix h h ℂ) ⊗ₖ resolvedLeftProjection) * P (Sum.inr ()) *
    ((1 : Matrix h h ℂ) ⊗ₖ resolvedRightProjection)

/-- In the even extension every historical word is the conservative
embedding of the old word. -/
theorem extendedOldWord_even (K : ι → Matrix h h ℂ) (w : List ι) :
    extendedOldWord (gradingEvenProcessExtension K) w =
      resolvedGradingEmbed (representedWord K w) := by
  unfold extendedOldWord
  simp only [gradingEvenProcessExtension]
  exact resolvedGradingEmbed_word K w

/-- In the odd extension every historical word is the conservative
embedding of the old word. -/
theorem extendedOldWord_odd (K : ι → Matrix h h ℂ) (w : List ι) :
    extendedOldWord (gradingOddProcessExtension K) w =
      resolvedGradingEmbed (representedWord K w) := by
  unfold extendedOldWord
  simp only [gradingOddProcessExtension]
  exact resolvedGradingEmbed_word K w

/-- The historical word algebras of the two extensions coincide literally. -/
theorem extendedOldWord_even_eq_odd (K : ι → Matrix h h ℂ) (w : List ι) :
    extendedOldWord (gradingEvenProcessExtension K) w =
      extendedOldWord (gradingOddProcessExtension K) w := by
  rw [extendedOldWord_even, extendedOldWord_odd]

/-- The Gram entry of two embedded words is twice the old Gram entry. -/
theorem trace_embed_gram (A B : Matrix h h ℂ) :
    Matrix.trace ((resolvedGradingEmbed A)ᴴ * resolvedGradingEmbed B) =
      2 * Matrix.trace (Aᴴ * B) := by
  unfold resolvedGradingEmbed
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker,
    Matrix.trace_one, Fintype.card_fin, mul_comm]
  norm_num

/-- The even word-Gram hierarchy is twice the old word-Gram hierarchy. -/
theorem wordGram_even (K : ι → Matrix h h ℂ) (w₁ w₂ : List ι) :
    wordGram (gradingEvenProcessExtension K) w₁ w₂ =
      2 * Matrix.trace ((representedWord K w₁)ᴴ * representedWord K w₂) := by
  unfold wordGram
  rw [extendedOldWord_even, extendedOldWord_even, trace_embed_gram]

/-- The odd word-Gram hierarchy is twice the old word-Gram hierarchy. -/
theorem wordGram_odd (K : ι → Matrix h h ℂ) (w₁ w₂ : List ι) :
    wordGram (gradingOddProcessExtension K) w₁ w₂ =
      2 * Matrix.trace ((representedWord K w₁)ᴴ * representedWord K w₂) := by
  unfold wordGram
  rw [extendedOldWord_odd, extendedOldWord_odd, trace_embed_gram]

/-- The even extension has vanishing grading-changing cross block. -/
theorem gradingCrossBlock_even (K : ι → Matrix h h ℂ) :
    gradingCrossBlock (gradingEvenProcessExtension K) = 0 := by
  unfold gradingCrossBlock
  simp only [gradingEvenProcessExtension]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.one_mul]
  have hz : resolvedLeftProjection * clockZ * resolvedRightProjection = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [resolvedLeftProjection, resolvedRightProjection, clockZ, Matrix.mul_apply,
        Matrix.single_apply]
  rw [hz, Matrix.kronecker_zero]

/-- The odd extension has nonvanishing grading-changing cross block. -/
theorem gradingCrossBlock_odd [Nonempty h] (K : ι → Matrix h h ℂ) :
    gradingCrossBlock (gradingOddProcessExtension K) ≠ 0 :=
  gradingOddProcessExtension_crossBlock_ne_zero K

/-- **`thm:external-shadow-no-go`.**  For an arbitrary finite historical
process `K`, the even and odd conservative extensions (i) both recover every
old word after normalized grading discard; (ii) have literally identical
historical word algebras (hence identical multiplication tables); (iii) have
identical complete word-Gram hierarchies, both equal to twice the old Gram;
(iv) have identical resolved cylinder entries on the resolved carrier;
(v) have cross blocks `0` and `≠ 0` respectively; and therefore (vi) no
function of the historical word data, and (vii) no function of the word-Gram
hierarchy, returns the cross block of both extensions. -/
theorem external_shadow_no_go [Nonempty h] (K : ι → Matrix h h ℂ) :
    (∀ w : List ι,
      discardResolvedGrading (extendedOldWord (gradingEvenProcessExtension K) w) =
        representedWord K w ∧
      discardResolvedGrading (extendedOldWord (gradingOddProcessExtension K) w) =
        representedWord K w) ∧
    (∀ w : List ι,
      extendedOldWord (gradingEvenProcessExtension K) w =
        extendedOldWord (gradingOddProcessExtension K) w) ∧
    (∀ w₁ w₂ : List ι,
      wordGram (gradingEvenProcessExtension K) w₁ w₂ =
        wordGram (gradingOddProcessExtension K) w₁ w₂ ∧
      wordGram (gradingEvenProcessExtension K) w₁ w₂ =
        2 * Matrix.trace ((representedWord K w₁)ᴴ * representedWord K w₂)) ∧
    (∀ (w : List ι) (x y : h × Fin 2),
      extendedOldWord (gradingEvenProcessExtension K) w x y =
        extendedOldWord (gradingOddProcessExtension K) w x y) ∧
    gradingCrossBlock (gradingEvenProcessExtension K) = 0 ∧
    gradingCrossBlock (gradingOddProcessExtension K) ≠ 0 ∧
    (¬ ∃ Φ : (List ι → Matrix (h × Fin 2) (h × Fin 2) ℂ) →
        Matrix (h × Fin 2) (h × Fin 2) ℂ,
      Φ (extendedOldWord (gradingEvenProcessExtension K)) =
          gradingCrossBlock (gradingEvenProcessExtension K) ∧
      Φ (extendedOldWord (gradingOddProcessExtension K)) =
          gradingCrossBlock (gradingOddProcessExtension K)) ∧
    (¬ ∃ Φ : (List ι → List ι → ℂ) → Matrix (h × Fin 2) (h × Fin 2) ℂ,
      Φ (wordGram (gradingEvenProcessExtension K)) =
          gradingCrossBlock (gradingEvenProcessExtension K) ∧
      Φ (wordGram (gradingOddProcessExtension K)) =
          gradingCrossBlock (gradingOddProcessExtension K)) := by
  have hwords : extendedOldWord (gradingEvenProcessExtension K) =
      extendedOldWord (gradingOddProcessExtension K) :=
    funext (extendedOldWord_even_eq_odd K)
  have hgram : wordGram (gradingEvenProcessExtension K) =
      wordGram (gradingOddProcessExtension K) := by
    funext w₁ w₂
    rw [wordGram_even, wordGram_odd]
  refine ⟨?_, extendedOldWord_even_eq_odd K, ?_, ?_, gradingCrossBlock_even K,
    gradingCrossBlock_odd K, ?_, ?_⟩
  · intro w
    constructor
    · rw [extendedOldWord_even, discardResolvedGrading_embed]
    · rw [extendedOldWord_odd, discardResolvedGrading_embed]
  · intro w₁ w₂
    exact ⟨by rw [wordGram_even, wordGram_odd], wordGram_even K w₁ w₂⟩
  · intro w x y
    rw [extendedOldWord_even_eq_odd]
  · rintro ⟨Φ, hΦe, hΦo⟩
    rw [hwords] at hΦe
    rw [hΦe] at hΦo
    exact gradingCrossBlock_odd K (hΦo.symm.trans (gradingCrossBlock_even K))
  · rintro ⟨Φ, hΦe, hΦo⟩
    rw [hgram] at hΦe
    rw [hΦe] at hΦo
    exact gradingCrossBlock_odd K (hΦo.symm.trans (gradingCrossBlock_even K))

end RenewalGeometry
