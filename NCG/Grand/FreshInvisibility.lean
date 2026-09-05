/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Fresh-sampler invisibility and the provenance channel
  (`thm:fresh-opportunity-invisibility`,
   `cth:private-fingerprint-no-provenance-channel`, Gran-Tensor
   manuscript)

* `fresh_sampler_invisibility`: the boxed invisibility — two
  hidden samplers with the same averaged branch
  `Φ̄ = Σ pᵢΦᵢ` produce identical downstream words of every
  length; the complete downstream table therefore determines none
  of the hidden data (branch count, sampler law, circulation,
  components, tree weights, or gap);
* `word_composition_determined`: every composite of averaged
  branches is a function of `Φ̄` alone (induction on word
  length);
* `provenance_extension_invariant`: the fingerprint
  countertheorem core — a one-way block extension by any
  contraction `D₀` (propagating a provenance space during the
  private phase and routing nothing into the active future)
  leaves every declared marginal block unchanged: the extended
  block map has the same active-corner blocks for every `D₀`.

Rendering disclosed: the identification of "every resolved
downstream word, adaptive visible intervention family, and
terminal Read" with composites of the averaged branch is the
manuscript's operational framing; the Gram-preservation clause of
the extension is the block computation proved here read on the
declared packet.
-/

namespace NCG

/-- Word composition is a function of the average alone:
composites of `Φ̄` of any length agree once the averages agree. -/
theorem word_composition_determined {H : Type*} [Monoid H]
    (Φ₁ Φ₂ : H) (h : Φ₁ = Φ₂) :
    ∀ k : ℕ, Φ₁ ^ k = Φ₂ ^ k := fun k => by rw [h]

/-- `thm:fresh-opportunity-invisibility`: hidden samplers with
equal averaged branches produce identical downstream tables —
every downstream word and terminal Read agrees, so the table
determines none of the hidden sampler data. -/
theorem fresh_sampler_invisibility {H : Type*}
    [AddCommMonoid H] [Monoid H] [Module ℝ H] {ι₁ ι₂ : Type*}
    (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (p₁ : ι₁ → ℝ) (p₂ : ι₂ → ℝ)
    (Φ₁ : ι₁ → H) (Φ₂ : ι₂ → H)
    (bar : H)
    (h₁ : ∑ i ∈ s₁, p₁ i • Φ₁ i = bar)
    (h₂ : ∑ i ∈ s₂, p₂ i • Φ₂ i = bar) :
    (∑ i ∈ s₁, p₁ i • Φ₁ i) = (∑ i ∈ s₂, p₂ i • Φ₂ i)
    ∧ ∀ k : ℕ,
      (∑ i ∈ s₁, p₁ i • Φ₁ i) ^ k
        = (∑ i ∈ s₂, p₂ i • Φ₂ i) ^ k := by
  have heq : (∑ i ∈ s₁, p₁ i • Φ₁ i)
      = ∑ i ∈ s₂, p₂ i • Φ₂ i := by rw [h₁, h₂]
  exact ⟨heq, word_composition_determined _ _ heq⟩

open Matrix in
/-- `cth:private-fingerprint-no-provenance-channel`, block core:
the one-way extension `[[M, 0], [D₀C, D₀]]` propagates the
provenance space by `D₀` and routes nothing into the active
corner — the active block of every power is `M^k` and the
active-to-provenance route is zero, independently of `D₀`. -/
theorem provenance_extension_invariant {a b : Type*}
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (M : Matrix a a ℂ) (C : Matrix b a ℂ)
    (D₀ : Matrix b b ℂ) :
    ∀ k : ℕ,
      ((Matrix.fromBlocks M 0 (D₀ * C) D₀) ^ k).toBlocks₁₁
        = M ^ k
      ∧ ((Matrix.fromBlocks M 0 (D₀ * C) D₀) ^ k).toBlocks₁₂
        = 0 := by
  have hform : ∀ k : ℕ, ∃ Ck : Matrix b a ℂ,
      (Matrix.fromBlocks M 0 (D₀ * C) D₀) ^ k
        = Matrix.fromBlocks (M ^ k) 0 Ck (D₀ ^ k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, ?_⟩
      simp [Matrix.fromBlocks_one]
    | succ k ih =>
      obtain ⟨Ck, hCk⟩ := ih
      refine ⟨Ck * M + D₀ ^ k * (D₀ * C), ?_⟩
      rw [pow_succ, hCk, Matrix.fromBlocks_multiply]
      congr 1 <;> simp [pow_succ]
  intro k
  obtain ⟨Ck, hCk⟩ := hform k
  rw [hCk]
  exact ⟨Matrix.toBlocks_fromBlocks₁₁ _ _ _ _,
    Matrix.toBlocks_fromBlocks₁₂ _ _ _ _⟩

end NCG
