/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OtherLoadingEmergence
import NCG.Grand.GrandOrder

/-!
# Exact assembly of an admissibly loaded subhierarchy

This module completes `thm:loaded-subhierarchy`.  The earlier
`LoadedSubhierarchy` module proves the three algebraic engines (Gram
positivity, contextual-null absorption, and finite stabilization).  Here an
admissible loading is packaged by the data that the manuscript declares:
finite panel expansion, source admission of selected records, a represented
word algebra, and a compatible cutoff synthesis.  The theorem below derives
the complete six-clause certificate, including the canonical kernel quotient,
flat source-minimal reconstruction, and the exact cutoff Gram congruence.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Operational data supplied by an admissible finite loading.  In particular,
`gramExpansion` says that every loaded Gram is assembled from finitely many
universal Gram/panel matrices, while `selectedInSource` says that selected
records already belong to the represented universal history algebra. -/
structure AdmissibleLoadedSubhierarchyData
    (h e panel selected A B eY : Type)
    [Fintype h] [Fintype e] [Fintype panel] [Fintype eY]
    [Ring A] [StarRing A] [Ring B] [StarRing B] where
  /-- Loaded word synthesis at depth `r`. -/
  wordSynthesis : ℕ → Matrix h e ℂ
  /-- Loaded word spans are nested. -/
  nested : ∀ r,
    LinearMap.range (wordSynthesis r).mulVecLin ≤
      LinearMap.range (wordSynthesis (r + 1)).mulVecLin
  /-- Universal Gram entries and declared inserted panels. -/
  universalPanel : panel → Matrix e e ℂ
  /-- The finite coefficients used at each depth. -/
  panelCoefficient : ℕ → panel → ℂ
  /-- Every loaded Gram is a finite linear combination of declared panels. -/
  gramExpansion : ∀ r,
    (wordSynthesis r)ᴴ * wordSynthesis r =
      ∑ p, panelCoefficient r p • universalPanel p
  /-- Representation of the loaded word algebra on the source algebra. -/
  evaluate : A →+* B
  /-- Evaluation respects the involution. -/
  evaluate_star : ∀ a, evaluate (star a) = star (evaluate a)
  /-- Values of records selected from the universal operational algebra. -/
  selectedValue : selected → B
  /-- Selected records need no new source-admission theorem. -/
  selectedInSource : ∀ s, selectedValue s ∈ evaluate.range
  /-- Higher-cutoff synthesis on the compatible selected history space. -/
  higherSynthesis : ℕ → Matrix h eY ℂ
  /-- Inclusion of the lower-cutoff loaded words into the higher cutoff. -/
  cutoffEmbedding : ℕ → Matrix eY e ℂ
  /-- Compatibility of physical letters, panels, and their word syntheses. -/
  cutoffSynthesis : ∀ r,
    wordSynthesis r = higherSynthesis r * cutoffEmbedding r

/-- The six exact conclusions of the loaded-subhierarchy theorem. -/
structure CanonicalLoadedSubhierarchyCertificate
    {h e panel selected A B eY : Type}
    [Fintype h] [Fintype e] [Fintype panel] [Fintype eY]
    [Ring A] [StarRing A] [Ring B] [StarRing B]
    (L : AdmissibleLoadedSubhierarchyData h e panel selected A B eY) : Prop where
  /-- (i) Every loaded word Gram is positive. -/
  gramPositive : ∀ r,
    ((L.wordSynthesis r)ᴴ * L.wordSynthesis r).PosSemidef
  /-- (i) Every loaded Gram has the declared finite universal-panel expansion. -/
  finiteUniversalPanelExpansion : ∀ r,
    (L.wordSynthesis r)ᴴ * L.wordSynthesis r =
      ∑ p, L.panelCoefficient r p • L.universalPanel p
  /-- (ii) Selected operational records already lie in the source range. -/
  selectedRecordsAlreadyAdmitted : ∀ s, L.selectedValue s ∈ L.evaluate.range
  /-- (iii) Future-null words are closed under left multiplication. -/
  futureNull_mul_left : ∀ q, q ∈ RingHom.ker L.evaluate →
    ∀ w, w * q ∈ RingHom.ker L.evaluate
  /-- (iii) Future-null words are closed under right multiplication. -/
  futureNull_mul_right : ∀ q, q ∈ RingHom.ker L.evaluate →
    ∀ w, q * w ∈ RingHom.ker L.evaluate
  /-- (iii) Future-null words are closed under involution. -/
  futureNull_star : ∀ q, q ∈ RingHom.ker L.evaluate →
    star q ∈ RingHom.ker L.evaluate
  /-- (iii) The represented quotient is canonically the source-generated range. -/
  quotientEquivSourceGenerated :
    Nonempty (A ⧸ RingHom.ker L.evaluate ≃+* L.evaluate.range)
  /-- (iv) Finite flatness, source minimality, and the unique Gram-fixing
  isometry are bundled by the canonical hierarchy certificate. -/
  flatSourceMinimalReconstruction : IsCanonicalLoadedHierarchy L.wordSynthesis
  /-- (v) Exact cutoff compatibility of every loaded Gram. -/
  cutoffGramCompatibility : ∀ r,
    (L.wordSynthesis r)ᴴ * L.wordSynthesis r =
      (L.cutoffEmbedding r)ᴴ *
        ((L.higherSynthesis r)ᴴ * L.higherSynthesis r) *
          L.cutoffEmbedding r
  /-- (vi) Products of already represented histories use the existing writer. -/
  representedWordProduct : ∀ a b,
    L.evaluate (a * b) = L.evaluate a * L.evaluate b
  /-- (vi) Adjoints of already represented histories use the existing writer. -/
  representedWordStar : ∀ a,
    L.evaluate (star a) = star (L.evaluate a)

/-- `thm:loaded-subhierarchy`, exact six-clause assembly. -/
theorem canonicalLoadedSubhierarchyAssembly
    {h e panel selected A B eY : Type}
    [Fintype h] [Fintype e] [Fintype panel] [Fintype eY]
    [Ring A] [StarRing A] [Ring B] [StarRing B]
    (L : AdmissibleLoadedSubhierarchyData h e panel selected A B eY) :
    CanonicalLoadedSubhierarchyCertificate L := by
  refine {
    gramPositive := ?_
    finiteUniversalPanelExpansion := L.gramExpansion
    selectedRecordsAlreadyAdmitted := L.selectedInSource
    futureNull_mul_left := ?_
    futureNull_mul_right := ?_
    futureNull_star := ?_
    quotientEquivSourceGenerated :=
      ⟨RingHom.quotientKerEquivRange L.evaluate⟩
    flatSourceMinimalReconstruction :=
      canonical_loaded_hierarchy L.wordSynthesis L.nested
    cutoffGramCompatibility := ?_
    representedWordProduct := fun a b => map_mul L.evaluate a b
    representedWordStar := L.evaluate_star }
  · intro r
    exact Matrix.posSemidef_conjTranspose_mul_self (L.wordSynthesis r)
  · intro q hq w
    change L.evaluate (w * q) = 0
    rw [map_mul, hq, mul_zero]
  · intro q hq w
    change L.evaluate (q * w) = 0
    rw [map_mul, hq, zero_mul]
  · intro q hq
    change L.evaluate (star q) = 0
    rw [L.evaluate_star, hq, star_zero]
  · intro r
    rw [L.cutoffSynthesis]
    exact cutoff_compatibility (L.higherSynthesis r) (L.cutoffEmbedding r)

end NCG
