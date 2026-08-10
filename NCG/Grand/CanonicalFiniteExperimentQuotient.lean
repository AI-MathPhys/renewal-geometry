/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CanonicalLikelihoodRatioQuotient

/-!
# Canonical finite-experiment quotient and common decoder

Support-exact projective-column quotient for a finite family of nonnegative
rows.  A faithful positive mixture supplies a normalization gauge, while the
proved positive-proportionality characterization shows that the resulting
equivalence relation is independent of the chosen mixture weights.
-/

open Finset

namespace NCG
open AcceptedActionInformationPythagoras
open ComparisonSignatureQuotient
namespace CanonicalFiniteExperimentQuotient

/-- Column normalized by a faithful mixture. -/
noncomputable def normalizedColumn
    {I U : Type*} (rows : I → U → ℝ) (mixture : U → ℝ) (u : U) :
    I → ℝ := fun i ↦ rows i u / mixture u

/-- Projective experiment quotient as the range of normalized columns. -/
abbrev Quotient {I U : Type*} (rows : I → U → ℝ)
    (mixture : U → ℝ) :=
  Set.range (normalizedColumn rows mixture)

noncomputable instance quotientFintype
    {I U : Type*} [Fintype U]
    (rows : I → U → ℝ) (mixture : U → ℝ) :
    Fintype (Quotient rows mixture) := by
  classical
  exact Set.fintypeRange (normalizedColumn rows mixture)

noncomputable instance quotientDecidableEq
    {I U : Type*} (rows : I → U → ℝ) (mixture : U → ℝ) :
    DecidableEq (Quotient rows mixture) :=
  Classical.decEq _

noncomputable def quotientMap {I U : Type*}
    (rows : I → U → ℝ) (mixture : U → ℝ) :
    U → Quotient rows mixture := fun u ↦
  ⟨normalizedColumn rows mixture u, u, rfl⟩

theorem quotientMap_surjective {I U : Type*}
    (rows : I → U → ℝ) (mixture : U → ℝ) :
    Function.Surjective (quotientMap rows mixture) := by
  rintro ⟨column, u, hu⟩
  subst column
  exact ⟨u, rfl⟩

/-- Equality in the quotient is exactly equality of normalized columns. -/
theorem quotientMap_eq_iff {I U : Type*}
    (rows : I → U → ℝ) (mixture : U → ℝ) (u v : U) :
    quotientMap rows mixture u = quotientMap rows mixture v ↔
      ∀ i, rows i u / mixture u = rows i v / mixture v := by
  constructor
  · intro h i
    exact congrFun (Subtype.ext_iff.mp h) i
  · intro h
    apply Subtype.ext
    funext i
    exact h i

/-- Normalized-column equality is equivalent to positive proportionality of
the original probability columns. -/
theorem quotientMap_eq_iff_positive_proportional
    {I U : Type*} [Fintype I]
    (rows : I → U → ℝ) (weights : I → ℝ) (mixture : U → ℝ)
    (hmix : ∀ u, mixture u = ∑ i, weights i * rows i u)
    (hmixture : ∀ u, 0 < mixture u) (u v : U) :
    quotientMap rows mixture u = quotientMap rows mixture v ↔
      ∃ a : ℝ, 0 < a ∧ ∀ i, rows i u = a * rows i v := by
  constructor
  · intro h
    refine ⟨mixture u / mixture v, div_pos (hmixture u) (hmixture v), ?_⟩
    intro i
    have hi := (quotientMap_eq_iff rows mixture u v).mp h i
    field_simp [ne_of_gt (hmixture u), ne_of_gt (hmixture v)] at hi ⊢
    linarith
  · rintro ⟨a, ha, hrows⟩
    apply (quotientMap_eq_iff rows mixture u v).2
    have hmixuv : mixture u = a * mixture v := by
      rw [hmix u, hmix v, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hrows i]
      ring
    intro i
    rw [hrows i, hmixuv]
    field_simp [ne_of_gt ha, ne_of_gt (hmixture v)]

/-- Every `2×2` column minor vanishes exactly when two nonzero columns are
positively proportional (using positivity of their mixture masses). -/
theorem quotientMap_eq_iff_vanishing_minors
    {I U : Type*} [Fintype I]
    (rows : I → U → ℝ) (weights : I → ℝ) (mixture : U → ℝ)
    (hweights : ∀ i, 0 < weights i) (hrows : ∀ i u, 0 ≤ rows i u)
    (hmix : ∀ u, mixture u = ∑ i, weights i * rows i u)
    (hmixture : ∀ u, 0 < mixture u) (u v : U) :
    quotientMap rows mixture u = quotientMap rows mixture v ↔
      ∀ i j, rows i u * rows j v = rows i v * rows j u := by
  constructor
  · intro h i j
    obtain ⟨a, _, ha⟩ :=
      (quotientMap_eq_iff_positive_proportional rows weights mixture
        hmix hmixture u v).mp h
    rw [ha i, ha j]
    ring
  · intro hminor
    apply (quotientMap_eq_iff rows mixture u v).2
    intro i
    have hweighted : rows i u * mixture v = rows i v * mixture u := by
      rw [hmix u, hmix v, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      calc
        rows i u * (weights j * rows j v) =
            weights j * (rows i u * rows j v) := by ring
        _ = weights j * (rows i v * rows j u) :=
          congrArg (weights j * ·) (hminor i j)
        _ = rows i v * (weights j * rows j u) := by ring
    apply (div_eq_div_iff (ne_of_gt (hmixture u)) (ne_of_gt (hmixture v))).2
    exact hweighted

/-- The mixture-native decoder on a quotient cell. -/
noncomputable def decoder
    {I U : Type*} [Fintype U]
    (rows : I → U → ℝ) (mixture : U → ℝ)
    (z : Quotient rows mixture) (u : U) : ℝ :=
  if quotientMap rows mixture u = z then
      mixture u / pushforwardRow (quotientMap rows mixture) mixture z
    else 0

theorem decoder_nonneg_and_sum_one
    {I U : Type*} [Fintype U]
    (rows : I → U → ℝ) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u) (z : Quotient rows mixture) :
    (∀ u, 0 ≤ decoder rows mixture z u) ∧ ∑ u, decoder rows mixture z u = 1 := by
  classical
  have hC := quotientMap_surjective rows mixture
  have hpush : 0 < pushforwardRow (quotientMap rows mixture) mixture z :=
    pushforwardRow_pos _ _ hC hmixture z
  constructor
  · intro u
    by_cases h : quotientMap rows mixture u = z
    · simp only [decoder, h, if_true]
      exact le_of_lt (div_pos (hmixture u) hpush)
    · simp [decoder, h]
  · unfold decoder
    rw [← Finset.sum_filter]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpush)

/-- Every experiment row is reconstructed by its quotient pushforward and
the single mixture-native decoder. -/
theorem common_decoder_reconstructs
    {I U : Type*} [Fintype U]
    (rows : I → U → ℝ) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u) :
    ∀ i u, rows i u =
      pushforwardRow (quotientMap rows mixture) (rows i)
        (quotientMap rows mixture u) *
      decoder rows mixture (quotientMap rows mixture u) u := by
  classical
  intro i u
  let C := quotientMap rows mixture
  let z := C u
  have hpush : 0 < pushforwardRow C mixture z :=
    pushforwardRow_pos C mixture (quotientMap_surjective rows mixture) hmixture z
  have hcross (v : U) (hv : C v = z) :
      rows i u * mixture v = rows i v * mixture u := by
    have hratio := (quotientMap_eq_iff rows mixture u v).mp hv.symm i
    field_simp [ne_of_gt (hmixture u), ne_of_gt (hmixture v)] at hratio
    linarith
  unfold decoder
  rw [if_pos rfl]
  change rows i u = pushforwardRow C (rows i) z *
    (mixture u / pushforwardRow C mixture z)
  field_simp [ne_of_gt hpush]
  unfold pushforwardRow
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  exact hcross v (Finset.mem_filter.mp hv).2

/-- Finite `f`-divergence with a faithful reference row. -/
noncomputable def finiteFDivergence
    {U : Type*} [Fintype U] (phi : ℝ → ℝ) (p q : U → ℝ) : ℝ :=
  ∑ u, q u * phi (p u / q u)

/-- The common decoder preserves every finite `f`-divergence whose reference
row is faithful. -/
theorem finiteFDivergence_preserved
    {I U : Type*} [Fintype U]
    (rows : I → U → ℝ) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u)
    (i j : I) (hj : ∀ u, 0 < rows j u) (phi : ℝ → ℝ) :
    finiteFDivergence phi (rows i) (rows j) =
      finiteFDivergence phi
        (pushforwardRow (quotientMap rows mixture) (rows i))
        (pushforwardRow (quotientMap rows mixture) (rows j)) := by
  classical
  let C := quotientMap rows mixture
  let D := decoder rows mixture
  have hrecon : ∀ i u, rows i u =
      pushforwardRow C (rows i) (C u) * D (C u) u := by
    simpa [C, D] using common_decoder_reconstructs rows mixture hmixture
  have hDpos (u : U) : 0 < D (C u) u := by
    unfold D decoder
    rw [if_pos rfl]
    exact div_pos (hmixture u)
      (pushforwardRow_pos C mixture (quotientMap_surjective rows mixture)
        hmixture (C u))
  unfold finiteFDivergence
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := C)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun u ↦ rows j u * phi (rows i u / rows j u))]
  apply Finset.sum_congr rfl
  intro z _
  obtain ⟨u₀, rfl⟩ := quotientMap_surjective rows mixture z
  have hjcoarse : 0 < pushforwardRow C (rows j) (C u₀) :=
    pushforwardRow_pos C (rows j) (quotientMap_surjective rows mixture) hj _
  calc
    ∑ u ∈ (Finset.univ.filter fun u ↦ C u = C u₀),
        rows j u * phi (rows i u / rows j u) =
      ∑ u ∈ (Finset.univ.filter fun u ↦ C u = C u₀),
        (pushforwardRow C (rows j) (C u₀) * D (C u₀) u) *
          phi (pushforwardRow C (rows i) (C u₀) /
            pushforwardRow C (rows j) (C u₀)) := by
              apply Finset.sum_congr rfl
              intro u hu
              have hCu : C u = C u₀ := (Finset.mem_filter.mp hu).2
              have hDu : 0 < D (C u₀) u := by
                simpa only [hCu] using hDpos u
              rw [hrecon j u, hrecon i u, hCu]
              congr 2
              field_simp [ne_of_gt hjcoarse, ne_of_gt hDu]
    _ = pushforwardRow C (rows j) (C u₀) *
        phi (pushforwardRow C (rows i) (C u₀) /
          pushforwardRow C (rows j) (C u₀)) := by
      have hsumfiber :
          ∑ u ∈ (Finset.univ.filter fun u ↦ C u = C u₀), D (C u₀) u = 1 := by
        unfold D decoder
        calc
          ∑ u ∈ (Finset.univ.filter fun u ↦ C u = C u₀),
              (if quotientMap rows mixture u = C u₀ then
                mixture u / pushforwardRow (quotientMap rows mixture) mixture (C u₀)
              else 0) =
              ∑ u ∈ (Finset.univ.filter fun u ↦ C u = C u₀),
                mixture u / pushforwardRow C mixture (C u₀) := by
                  apply Finset.sum_congr rfl
                  intro u hu
                  rw [if_pos (Finset.mem_filter.mp hu).2]
          _ = pushforwardRow C mixture (C u₀) /
              pushforwardRow C mixture (C u₀) := by
                rw [← Finset.sum_div]
                rfl
          _ = 1 := div_self (ne_of_gt
            (pushforwardRow_pos C mixture (quotientMap_surjective rows mixture)
              hmixture (C u₀)))
      calc
        ∑ u ∈ (Finset.univ.filter fun u ↦ C u = C u₀),
            (pushforwardRow C (rows j) (C u₀) * D (C u₀) u) *
              phi (pushforwardRow C (rows i) (C u₀) /
                pushforwardRow C (rows j) (C u₀)) =
            (pushforwardRow C (rows j) (C u₀) *
              phi (pushforwardRow C (rows i) (C u₀) /
                pushforwardRow C (rows j) (C u₀))) *
              ∑ u ∈ (Finset.univ.filter fun u ↦ C u = C u₀), D (C u₀) u := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro u _
                ring
        _ = _ := by rw [hsumfiber, mul_one]

/-- Support membership is reflected exactly by the quotient pushforward. -/
theorem support_reflected_by_pushforward
    {I U : Type*} [Fintype U]
    (rows : I → U → ℝ) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u) (i : I) (u : U) :
    rows i u = 0 ↔
      pushforwardRow (quotientMap rows mixture) (rows i)
        (quotientMap rows mixture u) = 0 := by
  classical
  have hrecon := common_decoder_reconstructs rows mixture hmixture i u
  have hdecoder : 0 < decoder rows mixture (quotientMap rows mixture u) u := by
    unfold decoder
    rw [if_pos rfl]
    exact div_pos (hmixture u)
      (pushforwardRow_pos _ _ (quotientMap_surjective rows mixture)
        hmixture _)
  constructor
  · intro hzero
    rw [hzero] at hrecon
    exact (mul_eq_zero.mp hrecon.symm).resolve_right (ne_of_gt hdecoder)
  · intro hzero
    rw [hrecon, hzero, zero_mul]

/-- Hence every directed support singularity is preserved and reflected. -/
theorem support_singularity_preserved
    {I U : Type*} [Fintype U]
    (rows : I → U → ℝ) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u) (i j : I) (u : U) :
    (rows i u = 0 ∧ 0 < rows j u) ↔
      (pushforwardRow (quotientMap rows mixture) (rows i)
          (quotientMap rows mixture u) = 0 ∧
       0 < pushforwardRow (quotientMap rows mixture) (rows j)
          (quotientMap rows mixture u)) := by
  have hi := support_reflected_by_pushforward rows mixture hmixture i u
  have hj := support_reflected_by_pushforward rows mixture hmixture j u
  constructor
  · rintro ⟨hizero, hjpos⟩
    refine ⟨hi.mp hizero, ?_⟩
    have hrecon := common_decoder_reconstructs rows mixture hmixture j u
    have hdecoder : 0 < decoder rows mixture (quotientMap rows mixture u) u := by
      unfold decoder
      rw [if_pos rfl]
      exact div_pos (hmixture u)
        (pushforwardRow_pos _ _ (quotientMap_surjective rows mixture) hmixture _)
    have hproduct : 0 <
        pushforwardRow (quotientMap rows mixture) (rows j)
          (quotientMap rows mixture u) *
        decoder rows mixture (quotientMap rows mixture u) u := by
      rwa [← hrecon]
    exact pos_of_mul_pos_left hproduct (le_of_lt hdecoder)
  · rintro ⟨hizero, hjpos⟩
    refine ⟨hi.mpr hizero, ?_⟩
    have hrecon := common_decoder_reconstructs rows mixture hmixture j u
    rw [hrecon]
    exact mul_pos hjpos (by
      unfold decoder
      rw [if_pos rfl]
      exact div_pos (hmixture u)
        (pushforwardRow_pos _ _ (quotientMap_surjective rows mixture)
          hmixture _))

/-- Composition of a row with a later finite channel. -/
noncomputable def applyChannel
    {U V : Type*} [Fintype U] (row : U → ℝ) (L : U → V → ℝ)
    (v : V) : ℝ :=
  ∑ u, row u * L u v

/-- Channel induced on the experiment quotient by the common decoder. -/
noncomputable def quotientChannel
    {I U V : Type*} [Fintype U]
    (rows : I → U → ℝ) (mixture : U → ℝ)
    (L : U → V → ℝ) (z : Quotient rows mixture) (v : V) : ℝ :=
  ∑ u, decoder rows mixture z u * L u v

/-- Every later stochastic (indeed, arbitrary linear) channel factors through
the experiment quotient. -/
theorem later_channel_factors
    {I U V : Type*} [Fintype U]
    (rows : I → U → ℝ) (mixture : U → ℝ)
    (hmixture : ∀ u, 0 < mixture u) (L : U → V → ℝ) :
    ∀ i v, applyChannel (rows i) L v =
      applyChannel (pushforwardRow (quotientMap rows mixture) (rows i))
        (quotientChannel rows mixture L) v := by
  classical
  intro i v
  unfold applyChannel quotientChannel
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ)
    (g := quotientMap rows mixture) (fun _ _ ↦ Finset.mem_univ _)
    (fun u ↦ rows i u * L u v)]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  calc
    ∑ u ∈ (Finset.univ.filter fun u ↦ quotientMap rows mixture u = z),
        rows i u * L u v =
        ∑ u ∈ (Finset.univ.filter fun u ↦ quotientMap rows mixture u = z),
          pushforwardRow (quotientMap rows mixture) (rows i) z *
            (decoder rows mixture z u * L u v) := by
              apply Finset.sum_congr rfl
              intro u hu
              have hCu := (Finset.mem_filter.mp hu).2
              rw [common_decoder_reconstructs rows mixture hmixture i u, hCu]
              ring
    _ = ∑ u, pushforwardRow (quotientMap rows mixture) (rows i) z *
          (decoder rows mixture z u * L u v) := by
      calc
        ∑ u ∈ (Finset.univ.filter fun u ↦ quotientMap rows mixture u = z),
            pushforwardRow (quotientMap rows mixture) (rows i) z *
              (decoder rows mixture z u * L u v) =
            ∑ u ∈ (Finset.univ.filter fun u ↦ quotientMap rows mixture u = z),
              pushforwardRow (quotientMap rows mixture) (rows i) z *
                ((mixture u / pushforwardRow (quotientMap rows mixture) mixture z) *
                  L u v) := by
                    apply Finset.sum_congr rfl
                    intro u hu
                    unfold decoder
                    rw [if_pos (Finset.mem_filter.mp hu).2]
        _ = ∑ u, if quotientMap rows mixture u = z then
              pushforwardRow (quotientMap rows mixture) (rows i) z *
                ((mixture u / pushforwardRow (quotientMap rows mixture) mixture z) *
                  L u v) else 0 := by
          exact Finset.sum_filter
            (s := Finset.univ)
            (fun u ↦ quotientMap rows mixture u = z)
            (fun u ↦ pushforwardRow (quotientMap rows mixture) (rows i) z *
              ((mixture u / pushforwardRow (quotientMap rows mixture) mixture z) *
                L u v))
        _ = ∑ u, pushforwardRow (quotientMap rows mixture) (rows i) z *
              (decoder rows mixture z u * L u v) := by
                apply Finset.sum_congr rfl
                intro u _
                by_cases hu : quotientMap rows mixture u = z
                · simp [decoder, hu]
                · simp [decoder, hu]

/-- A mixture of rows inherits any common decoder possessed by all rows. -/
theorem mixture_reconstructs_from_common_decoder
    {I U Z : Type*} [Fintype I] [Fintype U] [Fintype Z] [DecidableEq Z]
    (rows : I → U → ℝ) (weights : I → ℝ) (mixture : U → ℝ)
    (hmix : ∀ u, mixture u = ∑ i, weights i * rows i u)
    (record : U → Z) (commonDecoder : Z → U → ℝ)
    (hreconstruct : ∀ i u, rows i u =
      pushforwardRow record (rows i) (record u) * commonDecoder (record u) u) :
    ∀ u, mixture u =
      pushforwardRow record mixture (record u) * commonDecoder (record u) u := by
  intro u
  have hcoarse (z : Z) : pushforwardRow record mixture z =
      ∑ i, weights i * pushforwardRow record (rows i) z := by
    unfold pushforwardRow
    calc
      ∑ x ∈ (Finset.univ.filter fun x ↦ record x = z), mixture x =
          ∑ x ∈ (Finset.univ.filter fun x ↦ record x = z),
            ∑ i, weights i * rows i x := by
              apply Finset.sum_congr rfl
              intro x _
              rw [hmix x]
      _ = ∑ i, weights i *
          ∑ x ∈ (Finset.univ.filter fun x ↦ record x = z), rows i x := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
  rw [hmix u, hcoarse (record u), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hreconstruct i u]
  ring

/-- The projective quotient is the unique coarsest deterministic record
admitting one decoder for the complete experiment. -/
theorem quotient_is_unique_coarsest_common_decoder_record
    {I U Z : Type*} [Fintype I] [Fintype U] [Fintype Z] [DecidableEq Z]
    (rows : I → U → ℝ) (weights : I → ℝ) (mixture : U → ℝ)
    (hmix : ∀ u, mixture u = ∑ i, weights i * rows i u)
    (hmixture : ∀ u, 0 < mixture u)
    (record : U → Z) (hrecord : Function.Surjective record)
    (commonDecoder : Z → U → ℝ)
    (hreconstruct : ∀ i u, rows i u =
      pushforwardRow record (rows i) (record u) * commonDecoder (record u) u) :
    ∃! g : Z → Quotient rows mixture,
      Function.Surjective g ∧ g ∘ record = quotientMap rows mixture := by
  have hmixrecon := mixture_reconstructs_from_common_decoder
    rows weights mixture hmix record commonDecoder hreconstruct
  have hratio (i : I) (u : U) : rows i u / mixture u =
      pushforwardRow record (rows i) (record u) /
        pushforwardRow record mixture (record u) := by
    rw [hreconstruct i u, hmixrecon u]
    have hD : commonDecoder (record u) u ≠ 0 := by
      intro hzero
      have hpos := hmixture u
      rw [hmixrecon u, hzero, mul_zero] at hpos
      exact (ne_of_gt hpos) rfl
    field_simp [hD]
  have hfibre : ∀ {u v}, record u = record v →
      quotientMap rows mixture u = quotientMap rows mixture v := by
    intro u v huv
    apply (quotientMap_eq_iff rows mixture u v).2
    intro i
    rw [hratio i u, hratio i v, huv]
  let g := descendThroughSurjection record hrecord (quotientMap rows mixture) hfibre
  have hgcomp : g ∘ record = quotientMap rows mixture :=
    descendThroughSurjection_comp record hrecord _ hfibre
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨u, rfl⟩ := quotientMap_surjective rows mixture z
    exact ⟨record u, congrFun hgcomp u⟩
  refine ⟨g, ⟨hgsurj, hgcomp⟩, ?_⟩
  intro g' hg'
  exact descendThroughSurjection_unique record hrecord
    (quotientMap rows mixture) g' hg'.2

/-- The complete experiment containing every actual and comparator row. -/
def comparisonRows {Theta U : Type*}
    (actual comparator : Theta → U → ℝ) : Sum Theta Theta → U → ℝ
  | Sum.inl theta => actual theta
  | Sum.inr theta => comparator theta

/-- The experiment quotient always refines the likelihood-ratio quotient. -/
theorem experiment_quotient_refines_likelihood_ratio_quotient
    {Theta U : Type*} [Fintype Theta] [Fintype U]
    (actual comparator : Theta → U → ℝ)
    (weights : Sum Theta Theta → ℝ) (mixture : U → ℝ)
    (hmix : ∀ u, mixture u = ∑ i, weights i * comparisonRows actual comparator i u)
    (hmixture : ∀ u, 0 < mixture u)
    (hcomparator : ∀ theta u, 0 < comparator theta u) :
    ∃! g : Quotient (comparisonRows actual comparator) mixture →
        CanonicalLikelihoodRatioQuotient.Quotient actual comparator,
      Function.Surjective g ∧
        g ∘ quotientMap (comparisonRows actual comparator) mixture =
          CanonicalLikelihoodRatioQuotient.quotientMap actual comparator := by
  let expMap := quotientMap (comparisonRows actual comparator) mixture
  let lrMap := CanonicalLikelihoodRatioQuotient.quotientMap actual comparator
  have hfibre : ∀ {u v}, expMap u = expMap v → lrMap u = lrMap v := by
    intro u v huv
    obtain ⟨a, ha, hprop⟩ :=
      (quotientMap_eq_iff_positive_proportional
        (comparisonRows actual comparator) weights mixture hmix hmixture u v).mp huv
    apply Subtype.ext
    funext theta
    have hA := hprop (Sum.inl theta)
    have hQ := hprop (Sum.inr theta)
    change actual theta u = a * actual theta v at hA
    change comparator theta u = a * comparator theta v at hQ
    change actual theta u / comparator theta u =
      actual theta v / comparator theta v
    rw [hA, hQ]
    field_simp [ne_of_gt ha, ne_of_gt (hcomparator theta v)]
  let g := descendThroughSurjection expMap
    (quotientMap_surjective _ _) lrMap hfibre
  have hgcomp : g ∘ expMap = lrMap :=
    descendThroughSurjection_comp expMap (quotientMap_surjective _ _) _ hfibre
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨u, rfl⟩ :=
      CanonicalLikelihoodRatioQuotient.quotientMap_surjective actual comparator z
    exact ⟨expMap u, congrFun hgcomp u⟩
  refine ⟨g, ⟨hgsurj, hgcomp⟩, ?_⟩
  intro g' hg'
  exact descendThroughSurjection_unique expMap (quotientMap_surjective _ _)
    lrMap g' hg'.2

/-- Two quotient maps have exactly the same cells. -/
def SameFibres {U A B : Type*} (left : U → A) (right : U → B) : Prop :=
  ∀ u v, left u = left v ↔ right u = right v

/-- Denominator-free form of class-independence of comparator conditionals
inside each likelihood-ratio cell. -/
def ComparatorConditionalsClassIndependent
    {Theta U : Type*} (actual comparator : Theta → U → ℝ) : Prop :=
  ∀ theta phi u v,
    CanonicalLikelihoodRatioQuotient.quotientMap actual comparator u =
      CanonicalLikelihoodRatioQuotient.quotientMap actual comparator v →
    comparator theta u * comparator phi v =
      comparator theta v * comparator phi u

/-- The experiment and LR quotients coincide exactly when comparator
conditionals inside every LR cell are independent of comparison class. -/
theorem experiment_eq_likelihood_ratio_iff_comparator_conditionals_independent
    {Theta U : Type*} [Fintype Theta] [Nonempty Theta] [Fintype U]
    (actual comparator : Theta → U → ℝ)
    (weights : Sum Theta Theta → ℝ) (mixture : U → ℝ)
    (hmix : ∀ u, mixture u = ∑ i, weights i * comparisonRows actual comparator i u)
    (hmixture : ∀ u, 0 < mixture u)
    (hactual : ∀ theta u, 0 < actual theta u)
    (hcomparator : ∀ theta u, 0 < comparator theta u) :
    SameFibres
      (quotientMap (comparisonRows actual comparator) mixture)
      (CanonicalLikelihoodRatioQuotient.quotientMap actual comparator) ↔
      ComparatorConditionalsClassIndependent actual comparator := by
  let expMap := quotientMap (comparisonRows actual comparator) mixture
  let lrMap := CanonicalLikelihoodRatioQuotient.quotientMap actual comparator
  have hexp_to_lr : ∀ {u v}, expMap u = expMap v → lrMap u = lrMap v := by
    intro u v huv
    obtain ⟨a, ha, hprop⟩ :=
      (quotientMap_eq_iff_positive_proportional
        (comparisonRows actual comparator) weights mixture hmix hmixture u v).mp huv
    apply Subtype.ext
    funext theta
    have hA := hprop (Sum.inl theta)
    have hQ := hprop (Sum.inr theta)
    change actual theta u = a * actual theta v at hA
    change comparator theta u = a * comparator theta v at hQ
    change actual theta u / comparator theta u =
      actual theta v / comparator theta v
    rw [hA, hQ]
    field_simp [ne_of_gt ha, ne_of_gt (hcomparator theta v)]
  constructor
  · intro hsame theta phi u v hlr
    have hexp := (hsame u v).mpr hlr
    obtain ⟨a, _, hprop⟩ :=
      (quotientMap_eq_iff_positive_proportional
        (comparisonRows actual comparator) weights mixture hmix hmixture u v).mp hexp
    have htheta := hprop (Sum.inr theta)
    have hphi := hprop (Sum.inr phi)
    change comparator theta u = a * comparator theta v at htheta
    change comparator phi u = a * comparator phi v at hphi
    rw [htheta, hphi]
    ring
  · intro hind u v
    constructor
    · exact hexp_to_lr
    · intro hlr
      let theta₀ : Theta := Classical.choice inferInstance
      let a := comparator theta₀ u / comparator theta₀ v
      have ha : 0 < a := div_pos (hcomparator theta₀ u) (hcomparator theta₀ v)
      have hQ (theta : Theta) : comparator theta u = a * comparator theta v := by
        have hcross := hind theta₀ theta u v hlr
        unfold a
        field_simp [ne_of_gt (hcomparator theta₀ v)]
        nlinarith
      have hA (theta : Theta) : actual theta u = a * actual theta v := by
        have hratio := congrFun (Subtype.ext_iff.mp hlr) theta
        change actual theta u / comparator theta u =
          actual theta v / comparator theta v at hratio
        rw [hQ theta] at hratio
        field_simp [ne_of_gt ha, ne_of_gt (hcomparator theta v)] at hratio
        nlinarith
      apply (quotientMap_eq_iff_positive_proportional
        (comparisonRows actual comparator) weights mixture hmix hmixture u v).2
      refine ⟨a, ha, ?_⟩
      intro index
      cases index with
      | inl theta => exact hA theta
      | inr theta => exact hQ theta

end CanonicalFiniteExperimentQuotient
end NCG
