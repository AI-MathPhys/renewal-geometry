/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.FlatWordSpan
/-!
# Flat-depth multiplicity-birth obstruction

`thm:flat-depth-colour` (spacetime--gauge duality manuscript, external
multiplicity census and the first internal-factor obstruction).

Setting.  A finite-dimensional physical carrier `E`, represented source letters
`L ℓ : E →ₗ[ℂ] E`, a seed space `V0`, and the external symmetry action
`ρ g : E →ₗ[ℂ] E` (the tetrahedral `S₄` action in the manuscript; here any
family of operators).  The depth-`r` source-word carrier is
`𝒱_r = wordSpan L V0 r` (`Predictive/FlatWordSpan.lean`), the *external-trivial
multiplicity* is
`m_{0,r} = dim (𝒱_r ⊓ E^ρ)` (`trivialMultiplicity`, eq. `trivial-multiplicity`:
for a `ρ`-stable `𝒱_r` this is `dim Hom_G(𝟏, 𝒱_r)`, the dimension of the fixed
vectors of `𝒱_r`), and the colour-birth depth is
`r_col^birth = min {s : m_{0,s} ≥ 3}` in `ℕ∞` (`colourBirthDepth`,
eq. `colour-birth-depth`, value `⊤` when no such depth exists).

The relative commutant of the external action restricted to the trivial
isotypic component of `𝒱_s` is `End_ℂ(𝒱_s ⊓ E^ρ) ≅ M_{m_{0,s}}(ℂ)`
(`thm:active-isotypic`, eq. `external-isotypic-commutant`); an "external-trivial
internal `M₃(ℂ)` factor" is an injective linear image of `M₃(ℂ)` inside that
block (`trivialBlock`).

Results.

* `no_M3_of_trivialMultiplicity_le_two`: the `thm:active-isotypic` clause for the
  trivial isotypic block — with `m₀ ≤ 2` the block has dimension `≤ 4 < 9`, so
  `M₃(ℂ)` does not embed;
* `flat_depth_colour_obstruction`: **`thm:flat-depth-colour`** in the dimension
  form of the flatness hypothesis — `dim 𝒱_{r+1} ≤ dim 𝒱_r` and `m_{0,r} ≤ 2`
  give `𝒱_s = 𝒱_r` for all `s ≥ r`, `m_{0,s} ≤ 2` for **every** depth `s`, no
  external-trivial `M₃(ℂ)` factor at any depth, and `r_col^birth = ⊤`;
* `flat_depth_colour_obstruction_of_gram_rank`: the same with the literal
  hypothesis `rank K_r = rank K_{r+1}` for Grams `K = Cᴴ C` of labelled spanning
  families of `𝒱_r`, `𝒱_{r+1}`;
* `sourceWordMatrix`, `sourceWordGram`, `span_cols_sourceWordMatrix`: the
  labelled source-word family of the manuscript — columns indexed by (word of
  length `≤ r`, source label) with entries `(ℓ_k ⋯ ℓ_1 s_j)` — whose column span
  is exactly `𝒱_r` when `V0` is spanned by the sources;
* `flat_depth_colour_obstruction_of_word_gram`: **`thm:flat-depth-colour`** with
  the hypothesis stated on the source-word Grams `K_r = W_rᴴ W_r` themselves.
-/

open Matrix

namespace RenewalGeometry
namespace FlatDepthColour

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι G : Type*}

/-! ### External-trivial multiplicity and the colour-birth depth -/

/-- Fixed vectors of the external symmetry family `ρ`: the trivial isotypic
component `E^ρ` of the carrier. -/
def invariants (ρ : G → E →ₗ[ℂ] E) : Submodule ℂ E :=
  ⨅ g, LinearMap.ker (ρ g - LinearMap.id)

theorem mem_invariants {ρ : G → E →ₗ[ℂ] E} {v : E} :
    v ∈ invariants ρ ↔ ∀ g, ρ g v = v := by
  simp [invariants, sub_eq_zero]

/-- The external-trivial multiplicity `m₀(V) = dim (V ⊓ E^ρ)`
(eq. `trivial-multiplicity`): the number of copies of the trivial external
irreducible inside a (`ρ`-stable) carrier `V`. -/
noncomputable def trivialMultiplicity (ρ : G → E →ₗ[ℂ] E) (V : Submodule ℂ E) : ℕ :=
  Module.finrank ℂ ↥(V ⊓ invariants ρ)

/-- The external-trivial multiplicity is monotone in the carrier. -/
theorem trivialMultiplicity_mono [FiniteDimensional ℂ E] (ρ : G → E →ₗ[ℂ] E)
    {V W : Submodule ℂ E} (h : V ≤ W) :
    trivialMultiplicity ρ V ≤ trivialMultiplicity ρ W :=
  Submodule.finrank_mono (inf_le_inf_right _ h)

/-- The depth-`r` external-trivial multiplicity `m_{0,r} = m₀(𝒱_r)`. -/
noncomputable def m0 (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (ρ : G → E →ₗ[ℂ] E)
    (r : ℕ) : ℕ :=
  trivialMultiplicity ρ (wordSpan L V0 r)

/-- The colour-birth depth `r_col^birth = min {s : m_{0,s} ≥ 3}` in `ℕ∞`
(eq. `colour-birth-depth`); it is `⊤` when no depth has `m_{0,s} ≥ 3`. -/
noncomputable def colourBirthDepth (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E)
    (ρ : G → E →ₗ[ℂ] E) : ℕ∞ :=
  ⨅ (s : ℕ) (_ : 3 ≤ m0 L V0 ρ s), (s : ℕ∞)

/-- The external-trivial block of the depth-`s` relative commutant:
`End_ℂ(𝒱_s ⊓ E^ρ) ≅ M_{m_{0,s}}(ℂ)` (eq. `external-isotypic-commutant`,
trivial isotypic summand). -/
abbrev trivialBlock (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (ρ : G → E →ₗ[ℂ] E)
    (s : ℕ) :=
  ↥(wordSpan L V0 s ⊓ invariants ρ) →ₗ[ℂ] ↥(wordSpan L V0 s ⊓ invariants ρ)

/-- The `thm:active-isotypic` clause on the trivial isotypic block: if the
external-trivial multiplicity of `V` is at most two, `M₃(ℂ)` admits no injective
linear map into `End_ℂ(V ⊓ E^ρ)` (dimension `m₀² ≤ 4 < 9`). -/
theorem no_M3_of_trivialMultiplicity_le_two [FiniteDimensional ℂ E]
    (ρ : G → E →ₗ[ℂ] E) (V : Submodule ℂ E) (h : trivialMultiplicity ρ V ≤ 2)
    (f : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ]
      (↥(V ⊓ invariants ρ) →ₗ[ℂ] ↥(V ⊓ invariants ρ))) :
    ¬Function.Injective f := by
  intro hinj
  have h9 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_linearMap] at h9
  have hM3 : Module.finrank ℂ (Matrix (Fin 3) (Fin 3) ℂ) = 9 := by
    rw [Module.finrank_matrix, Module.finrank_self]
    simp
  unfold trivialMultiplicity at h
  nlinarith

/-! ### The obstruction theorem -/

/-- **`thm:flat-depth-colour`** (dimension form of the flatness hypothesis).
If `dim 𝒱_{r+1} ≤ dim 𝒱_r` (equality of the Gram ranks) and `m_{0,r} ≤ 2`, then
`𝒱_s = 𝒱_r` for every `s ≥ r`, the external-trivial multiplicity is `≤ 2` at
every depth, no depth carries an external-trivial `M₃(ℂ)` factor, and
`r_col^birth = ∞`. -/
theorem flat_depth_colour_obstruction [FiniteDimensional ℂ E]
    (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (ρ : G → E →ₗ[ℂ] E) (r : ℕ)
    (hflat : Module.finrank ℂ (wordSpan L V0 (r + 1))
      ≤ Module.finrank ℂ (wordSpan L V0 r))
    (hm : m0 L V0 ρ r ≤ 2) :
    (∀ s, r ≤ s → wordSpan L V0 s = wordSpan L V0 r)
    ∧ (∀ s, m0 L V0 ρ s ≤ 2)
    ∧ (∀ s, ∀ f : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] trivialBlock L V0 ρ s,
        ¬Function.Injective f)
    ∧ colourBirthDepth L V0 ρ = ⊤ := by
  have hfreeze := (flat_word_span L V0 r hflat).2.2
  have hm2 : ∀ s, m0 L V0 ρ s ≤ 2 := by
    intro s
    rcases le_or_gt r s with hrs | hsr
    · unfold m0
      rw [hfreeze s hrs]
      exact hm
    · exact (trivialMultiplicity_mono ρ (wordSpan_mono L V0 hsr.le)).trans hm
  refine ⟨hfreeze, hm2, fun s f => no_M3_of_trivialMultiplicity_le_two ρ _ (hm2 s) f, ?_⟩
  refine le_antisymm le_top (le_iInf fun s => le_iInf fun h3 => ?_)
  exact absurd h3 (by have := hm2 s; omega)

/-- **`thm:flat-depth-colour`** in its literal Gram-rank form: `C_r`, `C_{r+1}`
are labelled spanning families (columns) of `𝒱_r`, `𝒱_{r+1}` and
`rank K_r = rank K_{r+1}` for the Grams `K = Cᴴ C`. -/
theorem flat_depth_colour_obstruction_of_gram_rank {N : Type*} [Fintype N]
    (L : ι → (N → ℂ) →ₗ[ℂ] (N → ℂ)) (V0 : Submodule ℂ (N → ℂ))
    (ρ : G → (N → ℂ) →ₗ[ℂ] (N → ℂ)) (r : ℕ)
    {q q' : Type*} [Fintype q] [Fintype q']
    (Cr : Matrix N q ℂ) (Cr' : Matrix N q' ℂ)
    (hCr : Submodule.span ℂ (Set.range Cr.col) = wordSpan L V0 r)
    (hCr' : Submodule.span ℂ (Set.range Cr'.col) = wordSpan L V0 (r + 1))
    (hrank : (Crᴴ * Cr).rank = (Cr'ᴴ * Cr').rank)
    (hm : m0 L V0 ρ r ≤ 2) :
    (∀ s, r ≤ s → wordSpan L V0 s = wordSpan L V0 r)
    ∧ (∀ s, m0 L V0 ρ s ≤ 2)
    ∧ (∀ s, ∀ f : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] trivialBlock L V0 ρ s,
        ¬Function.Injective f)
    ∧ colourBirthDepth L V0 ρ = ⊤ := by
  apply flat_depth_colour_obstruction L V0 ρ r _ hm
  rw [gram_rank_eq_finrank_span_cols, gram_rank_eq_finrank_span_cols,
    hCr, hCr'] at hrank
  exact hrank.symm.le

/-! ### The labelled source-word Gram -/

/-- Words of length at most `r` over the letter alphabet. -/
abbrev WordsLe (ι : Type*) (r : ℕ) := {w : List ι // w.length ≤ r}

instance instFiniteWordsLe [Finite ι] (r : ℕ) : Finite (WordsLe ι r) :=
  (List.finite_length_le ι r).to_subtype

noncomputable instance instFintypeWordsLe [Finite ι] (r : ℕ) : Fintype (WordsLe ι r) :=
  Fintype.ofFinite _

/-- The represented word `ℓ_k ⋯ ℓ_1` as a linear map. -/
def wordMap (L : ι → E →ₗ[ℂ] E) : List ι → E →ₗ[ℂ] E
  | [] => LinearMap.id
  | ℓ :: w => L ℓ ∘ₗ wordMap L w

theorem wordAct_eq_wordMap (L : ι → E →ₗ[ℂ] E) : ∀ (w : List ι) (ξ : E),
    wordAct L w ξ = wordMap L w ξ
  | [], _ => rfl
  | ℓ :: w, ξ => by
    simp [wordAct, wordMap, wordAct_eq_wordMap L w]

/-- The labelled source-word family `W_r`: columns indexed by a word of length
`≤ r` and a source label, with column `(w, j) = ℓ_k ⋯ ℓ_1 s_j`. -/
noncomputable def sourceWordMatrix {N σ : Type*} [Finite ι]
    (L : ι → (N → ℂ) →ₗ[ℂ] (N → ℂ)) (s : σ → N → ℂ) (r : ℕ) :
    Matrix N (WordsLe ι r × σ) ℂ :=
  fun n p => wordAct L p.1.1 (s p.2) n

/-- Column `(w, j)` of `W_r` is the represented word applied to the source `s_j`. -/
theorem col_sourceWordMatrix {N σ : Type*} [Finite ι]
    (L : ι → (N → ℂ) →ₗ[ℂ] (N → ℂ)) (s : σ → N → ℂ) (r : ℕ) (p : WordsLe ι r × σ) :
    (sourceWordMatrix L s r).col p = wordAct L p.1.1 (s p.2) := rfl

/-- The labelled source-word Gram `K_r = W_rᴴ W_r`. -/
noncomputable def sourceWordGram {N σ : Type*} [Fintype N] [Finite ι]
    (L : ι → (N → ℂ) →ₗ[ℂ] (N → ℂ)) (s : σ → N → ℂ) (r : ℕ) :
    Matrix (WordsLe ι r × σ) (WordsLe ι r × σ) ℂ :=
  (sourceWordMatrix L s r)ᴴ * sourceWordMatrix L s r

/-- The column span of `W_r` is exactly the depth-`r` source-word carrier `𝒱_r`
seeded by the sources. -/
theorem span_cols_sourceWordMatrix {N σ : Type*} [Finite ι]
    (L : ι → (N → ℂ) →ₗ[ℂ] (N → ℂ)) (s : σ → N → ℂ) (r : ℕ) :
    Submodule.span ℂ (Set.range (sourceWordMatrix L s r).col)
      = wordSpan L (Submodule.span ℂ (Set.range s)) r := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨⟨w, j⟩, rfl⟩
    rw [col_sourceWordMatrix]
    exact wordAct_mem_wordSpan L _ w.1 r w.2 (s j) (Submodule.subset_span ⟨j, rfl⟩)
  · rw [wordSpan_eq_span_wordImage, Submodule.span_le]
    rintro v ⟨w, hw, ξ, hξ, rfl⟩
    rw [wordAct_eq_wordMap]
    have hmem : wordMap L w ξ ∈ Submodule.map (wordMap L w)
        (Submodule.span ℂ (Set.range s)) := ⟨ξ, hξ, rfl⟩
    rw [Submodule.map_span] at hmem
    refine Submodule.span_mono ?_ hmem
    rintro u ⟨_, ⟨j, rfl⟩, rfl⟩
    refine ⟨(⟨w, hw⟩, j), ?_⟩
    rw [col_sourceWordMatrix, wordAct_eq_wordMap]

/-- **`thm:flat-depth-colour`** with the hypothesis on the source-word Grams
themselves: if `rank K_r = rank K_{r+1}` for `K_r = W_rᴴ W_r` and `m_{0,r} ≤ 2`,
then `𝒱_s = 𝒱_r` for all `s ≥ r`, no depth carries an external-trivial `M₃(ℂ)`
factor, and `r_col^birth = ∞`. -/
theorem flat_depth_colour_obstruction_of_word_gram {N σ : Type*} [Fintype N]
    [Finite ι] [Fintype σ]
    (L : ι → (N → ℂ) →ₗ[ℂ] (N → ℂ)) (s : σ → N → ℂ)
    (ρ : G → (N → ℂ) →ₗ[ℂ] (N → ℂ)) (r : ℕ)
    (hrank : (sourceWordGram L s r).rank = (sourceWordGram L s (r + 1)).rank)
    (hm : m0 L (Submodule.span ℂ (Set.range s)) ρ r ≤ 2) :
    (∀ s', r ≤ s' → wordSpan L (Submodule.span ℂ (Set.range s)) s'
        = wordSpan L (Submodule.span ℂ (Set.range s)) r)
    ∧ (∀ s', m0 L (Submodule.span ℂ (Set.range s)) ρ s' ≤ 2)
    ∧ (∀ s', ∀ f : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ]
        trivialBlock L (Submodule.span ℂ (Set.range s)) ρ s', ¬Function.Injective f)
    ∧ colourBirthDepth L (Submodule.span ℂ (Set.range s)) ρ = ⊤ :=
  flat_depth_colour_obstruction_of_gram_rank L _ ρ r
    (sourceWordMatrix L s r) (sourceWordMatrix L s (r + 1))
    (span_cols_sourceWordMatrix L s r) (span_cols_sourceWordMatrix L s (r + 1))
    hrank hm

end FlatDepthColour
end RenewalGeometry
