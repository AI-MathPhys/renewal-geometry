/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.FlatWordSpan
import RenewalGeometry.Predictive.FiniteGrandTensorExact

/-!
# Finite flat word reconstruction: least flat depth and exhaustion
  (`thm:supp-word-flatness`, `eq:supp-flat-stop`, `eq:supp-word-gram`;
  emergent-spacetime manuscript — partial)

For a represented generator family `gen : Γ → Matrix M M ℂ` on the finite
support-minimal carrier `M` (the represented projections, primitive branch
maps and their Hilbert–Schmidt adjoints, so the family is closed under `star`),
the represented word spans

`𝒲_{X,≤r} = historyWordSpan gen r = span {[w] : |w| ≤ r}`

are the nested word spans `wordSpan` of `Predictive/FlatWordSpan` for the
left-multiplication letters `L γ = gen γ · ` and the seed `span {1}`
(`wordOp_mem_historyWordSpan`).  This file proves the two structural clauses
of `thm:supp-word-flatness` in the dimension form of `eq:supp-flat-stop`
(`rank 𝕂_{X,r} = dim 𝒲_{X,≤r}` for the faithful positive regular trace):

* `exists_least_flat_depth`: there is a least `r_X` with
  `dim 𝒲_{≤ r_X} = dim 𝒲_{≤ r_X + 1}`, because the nested word spans of a
  finite-dimensional algebra cannot grow forever;
* `historyWordSpan_eq_historyAlgebra_of_flat`: at any flat depth the word
  span is the whole history algebra `A^hist = StarAlgebra.adjoin ℂ (range gen)`
  (the stabilized span contains the unit and is invariant under left
  multiplication by every generator, hence by the generated algebra), and
  `𝒲_{≤ s} = 𝒲_{≤ r}` for all `s ≥ r` (`flat_word_span`);
* `flat_word_reconstruction_partial`: the two clauses bundled at the least
  flat depth.

Not covered here (still open for the record): positivity of the word-Gram
panels `𝕂_{X,r}(v,w) = τ̂_reg([v]^*[w])` as Gram matrices of the regular
trace (which needs positivity of the intrinsic regular trace on a matrix
star-subalgebra — `Krein/PositiveKreinDistinct.lean:wordGram_positive`
proves it for an abstractly positive functional), the identification
`rank 𝕂_{X,r} = dim 𝒲_{X,≤r}` (faithfulness), and the reconstruction of
units, multiplication, involution and predictive core algebras from the
panel through depth `r_X + 1`.
-/

open Matrix Module

namespace RenewalGeometry
namespace FiniteGrandTensor

variable {M : Type*} [Fintype M] [DecidableEq M] {Γ : Type*}

/-- The left-multiplication letters `L γ = gen γ ·` on `B(M)`. -/
def genLetter (gen : Γ → Matrix M M ℂ) (γ : Γ) : Matrix M M ℂ →ₗ[ℂ] Matrix M M ℂ :=
  LinearMap.mulLeft ℂ (gen γ)

/-- The represented word span `𝒲_{X,≤r} = span {[w] : |w| ≤ r}` as the nested
word span of `FlatWordSpan` with seed `span {1}`. -/
def historyWordSpan (gen : Γ → Matrix M M ℂ) (r : ℕ) : Submodule ℂ (Matrix M M ℂ) :=
  wordSpan (genLetter gen) (Submodule.span ℂ {(1 : Matrix M M ℂ)}) r

theorem wordAct_genLetter (gen : Γ → Matrix M M ℂ) (w : List Γ) :
    wordAct (genLetter gen) w 1 = wordOp gen w := by
  induction w with
  | nil => rfl
  | cons γ w ih =>
    simp only [wordAct, wordOp_cons, ih, genLetter, LinearMap.mulLeft_apply]

/-- Every represented word of length at most `r` lies in `𝒲_{X,≤r}`. -/
theorem wordOp_mem_historyWordSpan (gen : Γ → Matrix M M ℂ) (w : List Γ) (r : ℕ)
    (hw : w.length ≤ r) : wordOp gen w ∈ historyWordSpan gen r := by
  rw [← wordAct_genLetter]
  exact wordAct_mem_wordSpan _ _ w r hw 1 (Submodule.mem_span_singleton_self _)

theorem one_mem_historyWordSpan (gen : Γ → Matrix M M ℂ) (r : ℕ) :
    (1 : Matrix M M ℂ) ∈ historyWordSpan gen r :=
  wordOp_mem_historyWordSpan gen [] r (Nat.zero_le r)

/-- The word spans lie in the history algebra. -/
theorem historyWordSpan_le_historyAlgebra (gen : Γ → Matrix M M ℂ) (r : ℕ) :
    historyWordSpan gen r ≤ Subalgebra.toSubmodule (historyAlgebra gen).toSubalgebra := by
  induction r with
  | zero =>
    unfold historyWordSpan
    rw [wordSpan, Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    show (1 : Matrix M M ℂ) ∈ Subalgebra.toSubmodule (historyAlgebra gen).toSubalgebra
    rw [Subalgebra.mem_toSubmodule]
    exact one_mem _
  | succ r ih =>
    unfold historyWordSpan at ih ⊢
    rw [wordSpan_succ]
    refine sup_le ih (iSup_le fun γ => ?_)
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    have hx' := ih hx
    simp only [Submodule.mem_comap, Subalgebra.mem_toSubmodule, genLetter,
      LinearMap.mulLeft_apply] at hx' ⊢
    exact mul_mem (gen_mem_historyAlgebra gen γ) hx'

/-- The ranks of the nested word spans stabilize: there is a least depth `r_X`
with `dim 𝒲_{≤ r_X} = dim 𝒲_{≤ r_X + 1}` (`eq:supp-flat-stop` in dimension
form). -/
theorem exists_least_flat_depth (gen : Γ → Matrix M M ℂ) :
    ∃ r : ℕ, finrank ℂ (historyWordSpan gen r) = finrank ℂ (historyWordSpan gen (r + 1)) ∧
      ∀ r' < r, finrank ℂ (historyWordSpan gen r') ≠ finrank ℂ (historyWordSpan gen (r' + 1)) := by
  classical
  have hmono : ∀ r, finrank ℂ (historyWordSpan gen r) ≤ finrank ℂ (historyWordSpan gen (r + 1)) :=
    fun r => Submodule.finrank_mono (wordSpan_le_succ _ _ r)
  have hex : ∃ r, finrank ℂ (historyWordSpan gen r) = finrank ℂ (historyWordSpan gen (r + 1)) := by
    by_contra hcon
    push Not at hcon
    have hgrow : ∀ r, r ≤ finrank ℂ (historyWordSpan gen r) := by
      intro r
      induction r with
      | zero => exact Nat.zero_le _
      | succ r ih =>
        have hlt := lt_of_le_of_ne (hmono r) (hcon r)
        omega
    have hbound := Submodule.finrank_le (historyWordSpan gen (finrank ℂ (Matrix M M ℂ) + 1))
    have := hgrow (finrank ℂ (Matrix M M ℂ) + 1)
    omega
  refine ⟨Nat.find hex, Nat.find_spec hex, fun r' hr' => ?_⟩
  exact Nat.find_min hex hr'

/-- At a flat depth the word span is invariant under every generator and
contains the unit, hence contains the whole history algebra: left
multiplication by any element of `Algebra.adjoin ℂ (range gen ∪ star (range gen))`
preserves the span when the family is star-closed. -/
theorem mul_mem_historyWordSpan_of_flat (gen : Γ → Matrix M M ℂ)
    (hstar : ∀ γ, ∃ γ', star (gen γ) = gen γ') (r : ℕ)
    (hinv : ∀ γ, Submodule.map (genLetter gen γ) (historyWordSpan gen r) ≤ historyWordSpan gen r)
    {a : Matrix M M ℂ} (ha : a ∈ Algebra.adjoin ℂ (Set.range gen ∪ star (Set.range gen))) :
    ∀ y ∈ historyWordSpan gen r, a * y ∈ historyWordSpan gen r := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    intro y hy
    have hgen : ∃ γ, gen γ = x := by
      rcases hx with ⟨γ, rfl⟩ | hx
      · exact ⟨γ, rfl⟩
      · obtain ⟨γ, hγ⟩ := Set.mem_star.mp hx
        obtain ⟨γ', hγ'⟩ := hstar γ
        exact ⟨γ', by rw [← hγ', hγ, star_star]⟩
    obtain ⟨γ, rfl⟩ := hgen
    exact hinv γ ⟨y, hy, rfl⟩
  | algebraMap c =>
    intro y hy
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ c hy
  | add x z _ _ hx hz =>
    intro y hy
    rw [add_mul]
    exact Submodule.add_mem _ (hx y hy) (hz y hy)
  | mul x z _ _ hx hz =>
    intro y hy
    rw [mul_assoc]
    exact hx _ (hz y hy)

/-- **Exhaustion clause of `thm:supp-word-flatness`.**  For a star-closed
represented generator family, at a flat depth `r` (`dim 𝒲_{≤r+1} ≤ dim 𝒲_{≤r}`,
i.e. `rank 𝕂_{X,r} = rank 𝕂_{X,r+1}`) the represented word span is the whole
history algebra, and the word spans are constant from depth `r` on. -/
theorem historyWordSpan_eq_historyAlgebra_of_flat (gen : Γ → Matrix M M ℂ)
    (hstar : ∀ γ, ∃ γ', star (gen γ) = gen γ') (r : ℕ)
    (hflat : finrank ℂ (historyWordSpan gen (r + 1)) ≤ finrank ℂ (historyWordSpan gen r)) :
    historyWordSpan gen r = Subalgebra.toSubmodule (historyAlgebra gen).toSubalgebra ∧
      ∀ s, r ≤ s → historyWordSpan gen s = historyWordSpan gen r := by
  obtain ⟨_, hinv, hconst⟩ := flat_word_span (genLetter gen)
    (Submodule.span ℂ {(1 : Matrix M M ℂ)}) r hflat
  refine ⟨le_antisymm (historyWordSpan_le_historyAlgebra gen r) ?_, hconst⟩
  intro a ha
  rw [Subalgebra.mem_toSubmodule] at ha
  change a ∈ (StarAlgebra.adjoin ℂ (Set.range gen)).toSubalgebra at ha
  rw [StarAlgebra.adjoin_toSubalgebra] at ha
  have h := mul_mem_historyWordSpan_of_flat gen hstar r hinv ha 1 (one_mem_historyWordSpan gen r)
  rwa [mul_one] at h

/-- `thm:supp-word-flatness`, structural clauses at the least flat depth
`r_X`: `eq:supp-flat-stop` holds at `r_X` and fails below it, the represented
word span at `r_X` is the whole history algebra, and the spans are constant
from `r_X` on. -/
theorem flat_word_reconstruction_partial (gen : Γ → Matrix M M ℂ)
    (hstar : ∀ γ, ∃ γ', star (gen γ) = gen γ') :
    ∃ r : ℕ,
      (finrank ℂ (historyWordSpan gen r) = finrank ℂ (historyWordSpan gen (r + 1)) ∧
        ∀ r' < r, finrank ℂ (historyWordSpan gen r') ≠
          finrank ℂ (historyWordSpan gen (r' + 1))) ∧
      historyWordSpan gen r = Subalgebra.toSubmodule (historyAlgebra gen).toSubalgebra ∧
      ∀ s, r ≤ s → historyWordSpan gen s = historyWordSpan gen r := by
  obtain ⟨r, hr, hmin⟩ := exists_least_flat_depth gen
  exact ⟨r, ⟨hr, hmin⟩, historyWordSpan_eq_historyAlgebra_of_flat gen hstar r hr.symm.le⟩

end FiniteGrandTensor
end RenewalGeometry
