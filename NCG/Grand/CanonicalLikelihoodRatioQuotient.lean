/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AcceptedActionInformationPythagoras
import NCG.Grand.ComparisonSignatureQuotient

/-!
# Canonical likelihood-ratio quotient

This file proves `thm:accepted-LR-quotient` for finite strictly positive rows:
the likelihood-ratio range quotient is KL-lossless and initial among all
lossless deterministic reads; actual and comparator conditional laws agree in
every cell; the resulting common decoder reconstructs both rows; and total
variation and bounded-observable expectation differences are preserved.
-/

open Finset

namespace NCG
open AcceptedActionInformationPythagoras
open ComparisonSignatureQuotient
namespace CanonicalLikelihoodRatioQuotient

/-- The complete likelihood-ratio signature of a fine output. -/
noncomputable def likelihoodRatioSignature
    {Theta U : Type*} (actual comparator : Theta → U → ℝ) (u : U) :
    Theta → ℝ := fun theta ↦ actual theta u / comparator theta u

/-- The canonical likelihood-ratio quotient, represented by the range of its
complete signature. -/
abbrev Quotient {Theta U : Type*}
    (actual comparator : Theta → U → ℝ) :=
  Set.range (likelihoodRatioSignature actual comparator)

/-- Canonical quotient map. -/
noncomputable def quotientMap {Theta U : Type*}
    (actual comparator : Theta → U → ℝ) :
    U → Quotient actual comparator := fun u ↦
  ⟨likelihoodRatioSignature actual comparator u, u, rfl⟩

theorem quotientMap_surjective {Theta U : Type*}
    (actual comparator : Theta → U → ℝ) :
    Function.Surjective (quotientMap actual comparator) := by
  rintro ⟨signature, u, hu⟩
  subst signature
  exact ⟨u, rfl⟩

/-- A factorization of the fine likelihood ratio through a read forces the
two conditional rows inside every fibre to coincide. -/
theorem conditional_eq_of_likelihood_ratio_factorization
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (hC : Function.Surjective C)
    (r s : U → ℝ) (hr : ∀ u, 0 < r u) (hs : ∀ u, 0 < s u)
    (ratio : Z → ℝ) (hratio : ∀ u, r u / s u = ratio (C u)) :
    let R := canonicalPartitionedRow C r hC hr
    let S := canonicalPartitionedRow C s hC hs
    ∀ z u, C u = z → R.conditional z u = S.conditional z u := by
  dsimp only
  let R := canonicalPartitionedRow C r hC hr
  let S := canonicalPartitionedRow C s hC hs
  have hratio_pos (z : Z) : 0 < ratio z := by
    obtain ⟨u, rfl⟩ := hC z
    rw [← hratio u]
    exact div_pos (hr u) (hs u)
  have hpoint (u : U) : r u = ratio (C u) * s u := by
    apply (div_eq_iff (ne_of_gt (hs u))).mp
    rw [hratio u]
  have hcoarse (z : Z) : R.coarse z = ratio z * S.coarse z := by
    rw [R.coarse_eq_pushforward C r z, S.coarse_eq_pushforward C s z]
    unfold pushforwardRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hCu : C u = z := (Finset.mem_filter.mp hu).2
    rw [hpoint u, hCu]
  intro z u hCu
  change R.conditional z u = S.conditional z u
  have hpoint_u := hpoint u
  rw [R.factor u, S.factor u, hCu, hcoarse z] at hpoint_u
  apply mul_left_cancel₀
    (mul_ne_zero (ne_of_gt (hratio_pos z)) (ne_of_gt (S.coarse_pos z)))
  simpa [mul_assoc] using hpoint_u

/-- The KL divergence is preserved whenever the likelihood ratio factors
through the read. -/
theorem finiteKL_eq_pushforward_of_ratio_factorization
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (hC : Function.Surjective C)
    (r s : U → ℝ) (hr : ∀ u, 0 < r u) (hs : ∀ u, 0 < s u)
    (ratio : Z → ℝ) (hratio : ∀ u, r u / s u = ratio (C u)) :
    let R := canonicalPartitionedRow C r hC hr
    let S := canonicalPartitionedRow C s hC hs
    finiteKL r s = finiteKL R.coarse S.coarse := by
  dsimp only
  let R := canonicalPartitionedRow C r hC hr
  let S := canonicalPartitionedRow C s hC hs
  have hconditional : ∀ z u, C u = z →
      R.conditional z u = S.conditional z u :=
    conditional_eq_of_likelihood_ratio_factorization C hC r s hr hs ratio hratio
  rw [finiteKL_partition_chain C r s R S]
  have hfibre (z : Z) : fibreKL C z (R.conditional z) (S.conditional z) = 0 := by
    apply (fibreKL_eq_zero_iff C r s R S z).2
    funext u
    exact hconditional z u u.property
  simp [hfibre, R, S]

/-- Equality in deterministic KL data processing forces the fine likelihood
ratio to be constant on every read fibre. -/
theorem likelihood_ratio_constant_of_KL_preserved
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (hC : Function.Surjective C)
    (r s : U → ℝ) (hr : ∀ u, 0 < r u) (hs : ∀ u, 0 < s u)
    (hKL : finiteKL r s =
      finiteKL (pushforwardRow C r) (pushforwardRow C s)) :
    ∀ {u v}, C u = C v → r u / s u = r v / s v := by
  let R := canonicalPartitionedRow C r hC hr
  let S := canonicalPartitionedRow C s hC hs
  have hchain := finiteKL_partition_chain C r s R S
  have hcoarseR : R.coarse = pushforwardRow C r := by
    funext z
    exact R.coarse_eq_pushforward C r z
  have hcoarseS : S.coarse = pushforwardRow C s := by
    funext z
    exact S.coarse_eq_pushforward C s z
  have hsum : ∑ z, R.coarse z *
      fibreKL C z (R.conditional z) (S.conditional z) = 0 := by
    rw [hcoarseR, hcoarseS] at hchain
    rw [hcoarseR]
    rw [hKL] at hchain
    linarith
  have hterm : ∀ z ∈ (Finset.univ : Finset Z),
      0 ≤ R.coarse z * fibreKL C z (R.conditional z) (S.conditional z) := by
    intro z _
    exact mul_nonneg (le_of_lt (R.coarse_pos z))
      (fibreKL_nonneg C r s R S z)
  have hconditional (z : Z) :
      (fun u : {u // C u = z} ↦ R.conditional z u) =
        (fun u : {u // C u = z} ↦ S.conditional z u) := by
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum
    have hproduct := hall z (Finset.mem_univ z)
    have hfibre : fibreKL C z (R.conditional z) (S.conditional z) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt (R.coarse_pos z))
    exact (fibreKL_eq_zero_iff C r s R S z).mp hfibre
  intro u v huv
  have hucond0 := congrFun (hconditional (C u)) ⟨u, rfl⟩
  have hucond : R.conditional (C v) u = S.conditional (C v) u := by
    simpa only [huv] using hucond0
  have hvcond := congrFun (hconditional (C v)) ⟨v, rfl⟩
  rw [R.factor u, S.factor u, R.factor v, S.factor v, huv]
  rw [hucond, hvcond]
  field_simp [ne_of_gt (S.coarse_pos (C v)),
    ne_of_gt (S.conditional_pos (C v) u huv),
    ne_of_gt (S.conditional_pos (C v) v rfl)]

/-- Every comparison row is KL-lossless on the canonical likelihood-ratio
quotient, and actual/comparator conditionals coincide cellwise. -/
theorem canonical_quotient_lossless_and_conditional_agreement
    {Theta U : Type*} [Fintype Theta] [Fintype U]
    (actual comparator : Theta → U → ℝ)
    (hactual : ∀ theta u, 0 < actual theta u)
    (hcomparator : ∀ theta u, 0 < comparator theta u) :
    ∀ theta,
      finiteKL (actual theta) (comparator theta) =
        finiteKL
          (pushforwardRow (quotientMap actual comparator) (actual theta))
          (pushforwardRow (quotientMap actual comparator) (comparator theta)) ∧
      (∀ z u, quotientMap actual comparator u = z →
        conditionalRow (quotientMap actual comparator) (actual theta) z u =
          conditionalRow (quotientMap actual comparator) (comparator theta) z u) := by
  classical
  intro theta
  let C := quotientMap actual comparator
  have hC : Function.Surjective C := quotientMap_surjective actual comparator
  let ratio : Quotient actual comparator → ℝ := fun z ↦ z.1 theta
  have hratio : ∀ u, actual theta u / comparator theta u = ratio (C u) := by
    intro u
    rfl
  constructor
  · simpa [canonicalPartitionedRow] using
      (finiteKL_eq_pushforward_of_ratio_factorization C hC
        (actual theta) (comparator theta) (hactual theta) (hcomparator theta)
        ratio hratio)
  · simpa [canonicalPartitionedRow] using
      (conditional_eq_of_likelihood_ratio_factorization C hC
        (actual theta) (comparator theta) (hactual theta) (hcomparator theta)
        ratio hratio)

/-- Any deterministic read preserving all classwise KL divergences maps
uniquely and surjectively onto the likelihood-ratio quotient. -/
theorem canonical_quotient_is_unique_coarsest_lossless_record
    {Theta U Z : Type*} [Fintype Theta] [Fintype U] [Fintype Z]
    [DecidableEq Z]
    (actual comparator : Theta → U → ℝ)
    (hactual : ∀ theta u, 0 < actual theta u)
    (hcomparator : ∀ theta u, 0 < comparator theta u)
    (record : U → Z) (hrecord : Function.Surjective record)
    (hlossless : ∀ theta,
      finiteKL (actual theta) (comparator theta) =
        finiteKL (pushforwardRow record (actual theta))
          (pushforwardRow record (comparator theta))) :
    ∃! g : Z → Quotient actual comparator,
      Function.Surjective g ∧ g ∘ record = quotientMap actual comparator := by
  have hratio (theta : Theta) {u v : U} (huv : record u = record v) :
      actual theta u / comparator theta u =
        actual theta v / comparator theta v :=
    likelihood_ratio_constant_of_KL_preserved record hrecord
      (actual theta) (comparator theta) (hactual theta) (hcomparator theta)
      (hlossless theta) huv
  have hfibre : ∀ {u v}, record u = record v →
      quotientMap actual comparator u = quotientMap actual comparator v := by
    intro u v huv
    apply Subtype.ext
    funext theta
    exact hratio theta huv
  let g := descendThroughSurjection record hrecord
    (quotientMap actual comparator) hfibre
  have hgcomp : g ∘ record = quotientMap actual comparator :=
    descendThroughSurjection_comp record hrecord _ hfibre
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨u, rfl⟩ := quotientMap_surjective actual comparator z
    exact ⟨record u, congrFun hgcomp u⟩
  refine ⟨g, ⟨hgsurj, hgcomp⟩, ?_⟩
  intro g' hg'
  exact descendThroughSurjection_unique record hrecord
    (quotientMap actual comparator) g' hg'.2

/-- Total variation of two finite rows. -/
noncomputable def finiteTotalVariation {U : Type*} [Fintype U]
    (r s : U → ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ u, |r u - s u|

/-- Expectation of a fine observable against a finite row. -/
noncomputable def finiteExpectation {U : Type*} [Fintype U]
    (r f : U → ℝ) : ℝ :=
  ∑ u, r u * f u

/-- Common conditional mean of an observable in a read cell. -/
noncomputable def conditionalMean
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (C : U → Z) (conditional : Z → U → ℝ)
    (f : U → ℝ) (z : Z) : ℝ :=
  ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z), conditional z u * f u

/-- A common conditional decoder preserves total variation exactly. -/
theorem totalVariation_eq_pushforward_of_common_conditionals
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (r s : U → ℝ)
    (R : PartitionedRow C r) (S : PartitionedRow C s)
    (hconditional : ∀ z u, C u = z →
      R.conditional z u = S.conditional z u) :
    finiteTotalVariation r s = finiteTotalVariation R.coarse S.coarse := by
  unfold finiteTotalVariation
  congr 1
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := C)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun u ↦ |r u - s u|)]
  apply Finset.sum_congr rfl
  intro z _
  calc
    ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z), |r u - s u| =
        ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
          |(R.coarse z - S.coarse z) * R.conditional z u| := by
            apply Finset.sum_congr rfl
            intro u hu
            have hCu : C u = z := (Finset.mem_filter.mp hu).2
            rw [R.factor u, S.factor u, hCu, hconditional z u hCu]
            ring_nf
    _ = |R.coarse z - S.coarse z| *
        ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
          R.conditional z u := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u hu
            rw [abs_mul, abs_of_pos (R.conditional_pos z u
              (Finset.mem_filter.mp hu).2)]
    _ = |R.coarse z - S.coarse z| := by
      rw [R.conditional_sum z, mul_one]

/-- A common conditional decoder reconstructs every fine observable
expectation difference from the coarse rows. -/
theorem expectationDifference_eq_coarse_common_mean
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (r s : U → ℝ)
    (R : PartitionedRow C r) (S : PartitionedRow C s)
    (hconditional : ∀ z u, C u = z →
      R.conditional z u = S.conditional z u)
    (f : U → ℝ) :
    finiteExpectation r f - finiteExpectation s f =
      ∑ z, (R.coarse z - S.coarse z) *
        conditionalMean C R.conditional f z := by
  unfold finiteExpectation conditionalMean
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := C)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun u ↦ r u * f u - s u * f u)]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hCu : C u = z := (Finset.mem_filter.mp hu).2
  rw [R.factor u, S.factor u, hCu, hconditional z u hCu]
  ring

/-- The canonical quotient's common conditional kernel reconstructs both
rows, preserves total variation, and reconstructs every observable difference. -/
theorem canonical_common_decoder_variation_and_observables
    {Theta U : Type*} [Fintype Theta] [Fintype U]
    (actual comparator : Theta → U → ℝ)
    (hactual : ∀ theta u, 0 < actual theta u)
    (hcomparator : ∀ theta u, 0 < comparator theta u) :
    ∀ theta,
      let C := quotientMap actual comparator
      let actualCoarse := pushforwardRow C (actual theta)
      let comparatorCoarse := pushforwardRow C (comparator theta)
      let decoder := conditionalRow C (comparator theta)
      (∀ u, actual theta u = actualCoarse (C u) * decoder (C u) u) ∧
      (∀ u, comparator theta u = comparatorCoarse (C u) * decoder (C u) u) ∧
      finiteTotalVariation (actual theta) (comparator theta) =
        finiteTotalVariation actualCoarse comparatorCoarse ∧
      (∀ f : U → ℝ,
        finiteExpectation (actual theta) f - finiteExpectation (comparator theta) f =
          ∑ z, (actualCoarse z - comparatorCoarse z) *
            conditionalMean C decoder f z) := by
  classical
  intro theta
  dsimp only
  let C := quotientMap actual comparator
  have hC : Function.Surjective C := quotientMap_surjective actual comparator
  let A := canonicalPartitionedRow C (actual theta) hC (hactual theta)
  let Q := canonicalPartitionedRow C (comparator theta) hC (hcomparator theta)
  have hcond : ∀ z u, C u = z → A.conditional z u = Q.conditional z u := by
    simpa [C, A, Q, canonicalPartitionedRow] using
      (canonical_quotient_lossless_and_conditional_agreement
        actual comparator hactual hcomparator theta).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    rw [A.factor u, hcond (C u) u rfl]
    rfl
  · intro u
    exact Q.factor u
  · simpa [A, Q, canonicalPartitionedRow] using
      (totalVariation_eq_pushforward_of_common_conditionals C
        (actual theta) (comparator theta) A Q hcond)
  · intro f
    have hE := expectationDifference_eq_coarse_common_mean C
      (actual theta) (comparator theta) A Q hcond f
    calc
      finiteExpectation (actual theta) f - finiteExpectation (comparator theta) f =
          ∑ z, (A.coarse z - Q.coarse z) *
            conditionalMean C A.conditional f z := hE
      _ = ∑ z, (A.coarse z - Q.coarse z) *
            conditionalMean C Q.conditional f z := by
        apply Finset.sum_congr rfl
        intro z _
        congr 1
        unfold conditionalMean
        apply Finset.sum_congr rfl
        intro u hu
        rw [hcond z u (Finset.mem_filter.mp hu).2]
      _ = ∑ z,
          (pushforwardRow (quotientMap actual comparator) (actual theta) z -
            pushforwardRow (quotientMap actual comparator) (comparator theta) z) *
          conditionalMean (quotientMap actual comparator)
            (conditionalRow (quotientMap actual comparator) (comparator theta)) f z := by
        rfl

end CanonicalLikelihoodRatioQuotient
end NCG
