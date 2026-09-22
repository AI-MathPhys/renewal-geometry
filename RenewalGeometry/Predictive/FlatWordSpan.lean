/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.CharacterLeakage
/-!
# Flat extension of a finite word span

`lem:flat-word-span` (spacetime--gauge duality manuscript, appendix on
multiplicity birth).  For a finite represented letter alphabet `𝓛` acting on a
source-minimal quotient, the word spans
`V_r = span {ℓ_k ⋯ ℓ_1 ξ : k ≤ r, ℓ_j ∈ 𝓛, ξ ∈ V_0}` are nested.  If the Gram
ranks (equivalently the dimensions) of `V_r` and `V_{r+1}` agree then
`V_{r+1} = V_r`, every letter preserves `V_r`, and `V_s = V_r` for all `s ≥ r`;
consequently every external isotypic multiplicity is constant from depth `r`
on.

The word span is defined recursively (`wordSpan`) and identified with the span
of the images of words of length at most `r` (`wordSpan_eq_span_wordImage`).
The Gram-rank form of the hypothesis is bridged through
`saturation_rank` (`Predictive/CharacterLeakage.lean`) in
`flat_word_span_of_gram_rank`.
-/

open Matrix

namespace RenewalGeometry

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*}

/-- The nested word spans `V_r`: `V_0` is the seed space and
`V_{r+1} = V_r + Σ_ℓ ℓ V_r` over the letters of the alphabet. -/
def wordSpan (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) : ℕ → Submodule ℂ E
  | 0 => V0
  | r + 1 => wordSpan L V0 r ⊔ ⨆ ℓ, Submodule.map (L ℓ) (wordSpan L V0 r)

/-- Action of a word `ℓ_k ⋯ ℓ_1` (listed left to right) on a vector. -/
def wordAct (L : ι → E →ₗ[ℂ] E) : List ι → E → E
  | [], ξ => ξ
  | ℓ :: w, ξ => L ℓ (wordAct L w ξ)

/-- Images of seed vectors under words of length at most `r`. -/
def wordImage (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (r : ℕ) : Set E :=
  {v | ∃ w : List ι, w.length ≤ r ∧ ∃ ξ ∈ V0, wordAct L w ξ = v}

@[simp] theorem wordSpan_zero (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) :
    wordSpan L V0 0 = V0 := rfl

theorem wordSpan_succ (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (r : ℕ) :
    wordSpan L V0 (r + 1) =
      wordSpan L V0 r ⊔ ⨆ ℓ, Submodule.map (L ℓ) (wordSpan L V0 r) := rfl

/-- The word spans are nested. -/
theorem wordSpan_le_succ (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (r : ℕ) :
    wordSpan L V0 r ≤ wordSpan L V0 (r + 1) :=
  le_sup_left

theorem wordSpan_mono (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) :
    Monotone (wordSpan L V0) :=
  monotone_nat_of_le_succ (wordSpan_le_succ L V0)

/-- One letter applied to the depth-`r` span lands in the depth-`(r+1)` span. -/
theorem map_wordSpan_le_succ (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E)
    (r : ℕ) (ℓ : ι) :
    Submodule.map (L ℓ) (wordSpan L V0 r) ≤ wordSpan L V0 (r + 1) :=
  le_trans (le_iSup (fun ℓ => Submodule.map (L ℓ) (wordSpan L V0 r)) ℓ) le_sup_right

/-- Every word of length at most `r` maps the seed space into `V_r`. -/
theorem wordAct_mem_wordSpan (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) :
    ∀ (w : List ι) (r : ℕ), w.length ≤ r →
      ∀ ξ ∈ V0, wordAct L w ξ ∈ wordSpan L V0 r
  | [], r, _, ξ, hξ => wordSpan_mono L V0 (Nat.zero_le r) hξ
  | ℓ :: w, 0, hw, _, _ => by simp at hw
  | ℓ :: w, r + 1, hw, ξ, hξ => by
    have hw' : w.length ≤ r := by simpa using hw
    exact map_wordSpan_le_succ L V0 r ℓ
      ⟨wordAct L w ξ, wordAct_mem_wordSpan L V0 w r hw' ξ hξ, rfl⟩

theorem wordImage_mono (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E)
    {r s : ℕ} (hrs : r ≤ s) : wordImage L V0 r ⊆ wordImage L V0 s := by
  rintro v ⟨w, hw, ξ, hξ, rfl⟩
  exact ⟨w, hw.trans hrs, ξ, hξ, rfl⟩

/-- The recursive word span is exactly the manuscript's span of all words of
length at most `r` applied to the seed space. -/
theorem wordSpan_eq_span_wordImage (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E)
    (r : ℕ) :
    wordSpan L V0 r = Submodule.span ℂ (wordImage L V0 r) := by
  apply le_antisymm
  · induction r with
    | zero =>
      intro ξ hξ
      exact Submodule.subset_span ⟨[], le_rfl, ξ, hξ, rfl⟩
    | succ r ih =>
      rw [wordSpan_succ]
      refine sup_le ?_ (iSup_le fun ℓ => ?_)
      · exact ih.trans (Submodule.span_mono (wordImage_mono L V0 (Nat.le_succ r)))
      · calc Submodule.map (L ℓ) (wordSpan L V0 r)
            ≤ Submodule.map (L ℓ) (Submodule.span ℂ (wordImage L V0 r)) :=
              Submodule.map_mono ih
          _ = Submodule.span ℂ (L ℓ '' wordImage L V0 r) := Submodule.map_span _ _
          _ ≤ Submodule.span ℂ (wordImage L V0 (r + 1)) := by
              apply Submodule.span_mono
              rintro v ⟨u, ⟨w, hw, ξ, hξ, rfl⟩, rfl⟩
              exact ⟨ℓ :: w, by simpa using hw, ξ, hξ, rfl⟩
  · rw [Submodule.span_le]
    rintro v ⟨w, hw, ξ, hξ, rfl⟩
    exact wordAct_mem_wordSpan L V0 w r hw ξ hξ

/-- **`lem:flat-word-span`** (spacetime--gauge duality manuscript).  If the
depth-`(r+1)` word span is no larger than the depth-`r` span (equal Gram ranks),
then `V_{r+1} = V_r`, every letter of the alphabet preserves `V_r`, and
`V_s = V_r` for every `s ≥ r`. -/
theorem flat_word_span [FiniteDimensional ℂ E]
    (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (r : ℕ)
    (hflat : Module.finrank ℂ (wordSpan L V0 (r + 1))
      ≤ Module.finrank ℂ (wordSpan L V0 r)) :
    wordSpan L V0 (r + 1) = wordSpan L V0 r
    ∧ (∀ ℓ, Submodule.map (L ℓ) (wordSpan L V0 r) ≤ wordSpan L V0 r)
    ∧ ∀ s, r ≤ s → wordSpan L V0 s = wordSpan L V0 r := by
  have heq : wordSpan L V0 (r + 1) = wordSpan L V0 r :=
    (Submodule.eq_of_le_of_finrank_le (wordSpan_le_succ L V0 r) hflat).symm
  have hletter : ∀ ℓ, Submodule.map (L ℓ) (wordSpan L V0 r) ≤ wordSpan L V0 r :=
    fun ℓ => heq ▸ map_wordSpan_le_succ L V0 r ℓ
  refine ⟨heq, hletter, ?_⟩
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => rfl
  | succ s hs ih =>
    refine le_antisymm ?_ (ih ▸ wordSpan_le_succ L V0 s)
    rw [wordSpan_succ, ih]
    exact sup_le le_rfl (iSup_le hletter)

/-- The "consequently" clause of `lem:flat-word-span`: any invariant of the word
span — in particular every external isotypic multiplicity, read off the
subspace `V_s` — is constant for `s ≥ r` at a flat depth. -/
theorem flat_word_span_multiplicity_constant [FiniteDimensional ℂ E]
    (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (r : ℕ)
    (hflat : Module.finrank ℂ (wordSpan L V0 (r + 1))
      ≤ Module.finrank ℂ (wordSpan L V0 r))
    (mult : Submodule ℂ E → ℕ) :
    ∀ s, r ≤ s → mult (wordSpan L V0 s) = mult (wordSpan L V0 r) :=
  fun s hs => congrArg mult ((flat_word_span L V0 r hflat).2.2 s hs)

/-- The Gram rank of a labelled spanning family (the columns of `C`) is the
dimension of its span (`saturation_rank` composed with Mathlib's column-span
description of the rank). -/
theorem gram_rank_eq_finrank_span_cols {N q : Type*} [Fintype N] [Fintype q]
    (C : Matrix N q ℂ) :
    (Cᴴ * C).rank
      = Module.finrank ℂ (Submodule.span ℂ (Set.range C.col)) := by
  rw [saturation_rank, Matrix.rank_eq_finrank_span_cols]

/-- `lem:flat-word-span` in its literal Gram-rank form: if `C_r`, `C_{r+1}` are
labelled spanning families (columns) of `V_r`, `V_{r+1}` inside a coordinate
carrier and `rank K_r = rank K_{r+1}` for the Grams `K = Cᴴ C`, then the word
span is flat from depth `r` on. -/
theorem flat_word_span_of_gram_rank {N : Type*} [Fintype N]
    (L : ι → (N → ℂ) →ₗ[ℂ] (N → ℂ)) (V0 : Submodule ℂ (N → ℂ)) (r : ℕ)
    {q q' : Type*} [Fintype q] [Fintype q']
    (Cr : Matrix N q ℂ) (Cr' : Matrix N q' ℂ)
    (hCr : Submodule.span ℂ (Set.range Cr.col) = wordSpan L V0 r)
    (hCr' : Submodule.span ℂ (Set.range Cr'.col) = wordSpan L V0 (r + 1))
    (hrank : (Crᴴ * Cr).rank = (Cr'ᴴ * Cr').rank) :
    wordSpan L V0 (r + 1) = wordSpan L V0 r
    ∧ (∀ ℓ, Submodule.map (L ℓ) (wordSpan L V0 r) ≤ wordSpan L V0 r)
    ∧ ∀ s, r ≤ s → wordSpan L V0 s = wordSpan L V0 r := by
  apply flat_word_span L V0 r
  rw [gram_rank_eq_finrank_span_cols, gram_rank_eq_finrank_span_cols,
    hCr, hCr'] at hrank
  exact hrank.symm.le

end RenewalGeometry
