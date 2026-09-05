/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CanonicalFiniteExperimentQuotient

/-!
# Decoder innovation and conditional information

Finite support-aware KL chain rule for a proposed deterministic compression,
including experiment rows with zero entries and zero-mass coarse cells.
-/

open Finset

namespace NCG
open AcceptedActionInformationPythagoras
open CanonicalFiniteExperimentQuotient
namespace DecoderInnovationConditionalInformation

/-- Conditional KL divergence in one fibre.  It is only used with a prefactor
equal to the coarse mass, so zero-mass cells contribute zero. -/
noncomputable def conditionalFibreKL
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (C : U → Z) (p m : U → ℝ) (z : Z) : ℝ :=
  finiteKL
    (fun u : {u // C u = z} ↦ p u / pushforwardRow C p z)
    (fun u : {u // C u = z} ↦ m u / pushforwardRow C m z)

theorem pushforwardRow_nonneg
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (C : U → Z) (p : U → ℝ) (hp : ∀ u, 0 ≤ p u) (z : Z) :
    0 ≤ pushforwardRow C p z := by
  unfold pushforwardRow
  exact Finset.sum_nonneg fun u _ ↦ hp u

theorem pushforwardRow_sum
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (p : U → ℝ) :
    ∑ z, pushforwardRow C p z = ∑ u, p u := by
  unfold pushforwardRow
  exact Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := C)
    (fun _ _ ↦ Finset.mem_univ _) p

/-- Support-aware deterministic KL chain rule. -/
theorem finiteKL_compression_chain
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (hC : Function.Surjective C)
    (p m : U → ℝ) (hp : ∀ u, 0 ≤ p u) (hm : ∀ u, 0 < m u) :
    finiteKL p m =
      finiteKL (pushforwardRow C p) (pushforwardRow C m) +
        ∑ z, pushforwardRow C p z * conditionalFibreKL C p m z := by
  have hmC (z : Z) : 0 < pushforwardRow C m z :=
    pushforwardRow_pos C m hC hm z
  have hlocal (z : Z) :
      ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
          p u * Real.log (p u / m u) =
        pushforwardRow C p z *
            Real.log (pushforwardRow C p z / pushforwardRow C m z) +
          pushforwardRow C p z * conditionalFibreKL C p m z := by
    by_cases hpCzero : pushforwardRow C p z = 0
    · have hzero : ∀ u ∈ (Finset.univ.filter fun u ↦ C u = z), p u = 0 := by
        intro u hu
        have hsum : ∑ v ∈ (Finset.univ.filter fun v ↦ C v = z), p v = 0 := by
          simpa [pushforwardRow] using hpCzero
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun v _ ↦ hp v)).mp hsum u hu
      simp only [hpCzero, zero_mul, zero_add]
      apply Finset.sum_eq_zero
      intro u hu
      rw [hzero u hu, zero_mul]
    · have hpC : 0 < pushforwardRow C p z :=
        lt_of_le_of_ne (pushforwardRow_nonneg C p hp z) (Ne.symm hpCzero)
      have hlog (u : U) (hu : C u = z) :
          p u * Real.log (p u / m u) =
            p u * Real.log (pushforwardRow C p z / pushforwardRow C m z) +
              p u * Real.log
                ((p u / pushforwardRow C p z) /
                  (m u / pushforwardRow C m z)) := by
        by_cases hpu : p u = 0
        · simp [hpu]
        · have hpupos : 0 < p u := lt_of_le_of_ne (hp u) (Ne.symm hpu)
          rw [← mul_add]
          congr 1
          rw [← Real.log_mul
            (div_ne_zero (ne_of_gt hpC) (ne_of_gt (hmC z)))
            (div_ne_zero
              (div_ne_zero hpu (ne_of_gt hpC))
              (div_ne_zero (ne_of_gt (hm u)) (ne_of_gt (hmC z))))]
          congr 1
          field_simp [ne_of_gt hpC, ne_of_gt (hmC z), hpu, ne_of_gt (hm u)]
      unfold conditionalFibreKL finiteKL
      rw [← Finset.sum_subtype
        (p := fun u ↦ C u = z)
        (Finset.univ.filter fun u ↦ C u = z) (by simp)
        (fun u ↦ (p u / pushforwardRow C p z) *
          Real.log ((p u / pushforwardRow C p z) /
            (m u / pushforwardRow C m z)))]
      calc
        ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
            p u * Real.log (p u / m u) =
          ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
            (p u * Real.log (pushforwardRow C p z / pushforwardRow C m z) +
              p u * Real.log ((p u / pushforwardRow C p z) /
                (m u / pushforwardRow C m z))) := by
                  apply Finset.sum_congr rfl
                  intro u hu
                  exact hlog u (Finset.mem_filter.mp hu).2
        _ = pushforwardRow C p z *
              Real.log (pushforwardRow C p z / pushforwardRow C m z) +
            ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
              p u * Real.log ((p u / pushforwardRow C p z) /
                (m u / pushforwardRow C m z)) := by
                  rw [Finset.sum_add_distrib]
                  congr 1
                  unfold pushforwardRow
                  rw [Finset.sum_mul]
        _ = pushforwardRow C p z *
              Real.log (pushforwardRow C p z / pushforwardRow C m z) +
            pushforwardRow C p z *
              ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
                (p u / pushforwardRow C p z) *
                  Real.log ((p u / pushforwardRow C p z) /
                    (m u / pushforwardRow C m z)) := by
                      congr 1
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro u _
                      field_simp [ne_of_gt hpC]
  unfold finiteKL
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := C)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun u ↦ p u * Real.log (p u / m u))]
  simp_rw [hlocal]
  rw [Finset.sum_add_distrib]

/-- Decoder innovation of a proposed deterministic record. -/
noncomputable def decoderInnovation
    {I U Z : Type*} [Fintype I] [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (weights : I → ℝ) (rows : I → U → ℝ)
    (mixture : U → ℝ) : ℝ :=
  ∑ i, weights i * ∑ z,
    pushforwardRow C (rows i) z * conditionalFibreKL C (rows i) mixture z

/-- Finite conditional mutual information in its conditional-KL form. -/
noncomputable def conditionalMutualInformation
    {I U Z : Type*} [Fintype I] [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (weights : I → ℝ) (rows : I → U → ℝ)
    (mixture : U → ℝ) : ℝ :=
  ∑ i, weights i * ∑ z,
    pushforwardRow C (rows i) z * conditionalFibreKL C (rows i) mixture z

theorem decoderInnovation_eq_conditionalMutualInformation
    {I U Z : Type*} [Fintype I] [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (weights : I → ℝ) (rows : I → U → ℝ)
    (mixture : U → ℝ) :
    decoderInnovation C weights rows mixture =
      conditionalMutualInformation C weights rows mixture := rfl

/-- The displayed averaged KL Pythagoras identity. -/
theorem decoder_innovation_identity
    {I U Z : Type*} [Fintype I] [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (hC : Function.Surjective C)
    (weights : I → ℝ) (rows : I → U → ℝ) (mixture : U → ℝ)
    (hrows : ∀ i u, 0 ≤ rows i u) (hmixture : ∀ u, 0 < mixture u) :
    ∑ i, weights i * finiteKL (rows i) mixture =
      ∑ i, weights i *
        finiteKL (pushforwardRow C (rows i)) (pushforwardRow C mixture) +
      decoderInnovation C weights rows mixture := by
  unfold decoderInnovation
  simp_rw [finiteKL_compression_chain C hC (rows _) mixture (hrows _) hmixture,
    mul_add]
  rw [Finset.sum_add_distrib]

/-- A coarse-mass-weighted conditional KL term is nonnegative, including a
zero-mass cell. -/
theorem weighted_conditionalFibreKL_nonneg
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (hC : Function.Surjective C)
    (p m : U → ℝ) (hp : ∀ u, 0 ≤ p u) (hm : ∀ u, 0 < m u)
    (hpsum : ∑ u, p u = 1) (hmsum : ∑ u, m u = 1) (z : Z) :
    0 ≤ pushforwardRow C p z * conditionalFibreKL C p m z := by
  by_cases hpCzero : pushforwardRow C p z = 0
  · simp [hpCzero]
  · have hpC : 0 < pushforwardRow C p z :=
      lt_of_le_of_ne (pushforwardRow_nonneg C p hp z) (Ne.symm hpCzero)
    have hmC : 0 < pushforwardRow C m z := pushforwardRow_pos C m hC hm z
    let pc : {u // C u = z} → ℝ := fun u ↦ p u / pushforwardRow C p z
    let mc : {u // C u = z} → ℝ := fun u ↦ m u / pushforwardRow C m z
    have hpc_nonneg : ∀ u, 0 ≤ pc u := fun u ↦
      div_nonneg (hp u) (le_of_lt hpC)
    have hmc_pos : ∀ u, 0 < mc u := fun u ↦
      div_pos (hm u) hmC
    have hpc_sum : ∑ u, pc u = 1 := by
      rw [← Finset.sum_subtype
        (p := fun u ↦ C u = z)
        (Finset.univ.filter fun u ↦ C u = z) (by simp)
        (fun u ↦ p u / pushforwardRow C p z)]
      unfold pushforwardRow
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hpC)
    have hmc_sum : ∑ u, mc u = 1 := by
      rw [← Finset.sum_subtype
        (p := fun u ↦ C u = z)
        (Finset.univ.filter fun u ↦ C u = z) (by simp)
        (fun u ↦ m u / pushforwardRow C m z)]
      unfold pushforwardRow
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hmC)
    have hKL := (finiteKL_nonneg_eq_iff_of_nonnegative
      pc mc hpc_nonneg hmc_pos hpc_sum hmc_sum).1
    exact mul_nonneg (le_of_lt hpC) (by
      simpa [conditionalFibreKL, pc, mc] using hKL)

/-- On a positive coarse cell, conditional KL vanishes exactly when the
conditional experiment row equals the mixture-native conditional row. -/
theorem conditionalFibreKL_eq_zero_iff_of_pos
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (hC : Function.Surjective C)
    (p m : U → ℝ) (hp : ∀ u, 0 ≤ p u) (hm : ∀ u, 0 < m u)
    (z : Z) (hpC : 0 < pushforwardRow C p z) :
    conditionalFibreKL C p m z = 0 ↔
      (fun u : {u // C u = z} ↦ p u / pushforwardRow C p z) =
        (fun u : {u // C u = z} ↦ m u / pushforwardRow C m z) := by
  have hmC : 0 < pushforwardRow C m z := pushforwardRow_pos C m hC hm z
  let pc : {u // C u = z} → ℝ := fun u ↦ p u / pushforwardRow C p z
  let mc : {u // C u = z} → ℝ := fun u ↦ m u / pushforwardRow C m z
  have hpc_nonneg : ∀ u, 0 ≤ pc u := fun u ↦
    div_nonneg (hp u) (le_of_lt hpC)
  have hmc_pos : ∀ u, 0 < mc u := fun u ↦ div_pos (hm u) hmC
  have hpc_sum : ∑ u, pc u = 1 := by
    rw [← Finset.sum_subtype
      (p := fun u ↦ C u = z)
      (Finset.univ.filter fun u ↦ C u = z) (by simp)
      (fun u ↦ p u / pushforwardRow C p z)]
    unfold pushforwardRow
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpC)
  have hmc_sum : ∑ u, mc u = 1 := by
    rw [← Finset.sum_subtype
      (p := fun u ↦ C u = z)
      (Finset.univ.filter fun u ↦ C u = z) (by simp)
      (fun u ↦ m u / pushforwardRow C m z)]
    unfold pushforwardRow
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hmC)
  simpa [conditionalFibreKL, pc, mc] using
    (finiteKL_nonneg_eq_iff_of_nonnegative
      pc mc hpc_nonneg hmc_pos hpc_sum hmc_sum).2

/-- The mixture-native decoder associated with an arbitrary surjective
deterministic record. -/
noncomputable def proposedDecoder
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (C : U → Z) (mixture : U → ℝ) (z : Z) (u : U) : ℝ :=
  if C u = z then mixture u / pushforwardRow C mixture z else 0

/-- A record refines the canonical experiment quotient when its fibres are
contained in quotient fibres. -/
def RefinesExperimentQuotient
    {I U Z : Type*} (C : U → Z) (rows : I → U → ℝ)
    (mixture : U → ℝ) : Prop :=
  ∃ g : Z → CanonicalFiniteExperimentQuotient.Quotient rows mixture,
    g ∘ C = CanonicalFiniteExperimentQuotient.quotientMap rows mixture

/-- Refinement of the experiment quotient is equivalent to exact recovery of
every experiment row by the proposed mixture-native decoder. -/
theorem refinesExperimentQuotient_iff_proposedDecoder_reconstructs
    {I U Z : Type*} [Fintype I] [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (hC : Function.Surjective C)
    (weights : I → ℝ) (rows : I → U → ℝ) (mixture : U → ℝ)
    (hmix : ∀ u, mixture u = ∑ i, weights i * rows i u)
    (hmixture : ∀ u, 0 < mixture u) :
    RefinesExperimentQuotient C rows mixture ↔
      ∀ i u, rows i u =
        pushforwardRow C (rows i) (C u) * proposedDecoder C mixture (C u) u := by
  constructor
  · rintro ⟨g, hg⟩
    intro i u
    have hpush : 0 < pushforwardRow C mixture (C u) :=
      pushforwardRow_pos C mixture hC hmixture (C u)
    have hcross (v : U) (hv : C v = C u) :
        rows i u * mixture v = rows i v * mixture u := by
      have hquot : quotientMap rows mixture u = quotientMap rows mixture v := by
        rw [← congrFun hg u, ← congrFun hg v]
        change g (C u) = g (C v)
        rw [hv]
      have hratio := (quotientMap_eq_iff rows mixture u v).mp hquot i
      field_simp [ne_of_gt (hmixture u), ne_of_gt (hmixture v)] at hratio
      linarith
    unfold proposedDecoder
    rw [if_pos rfl]
    field_simp [ne_of_gt hpush]
    unfold pushforwardRow
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v hv
    exact hcross v (Finset.mem_filter.mp hv).2
  · intro hreconstruct
    obtain ⟨g, hg, _⟩ :=
      quotient_is_unique_coarsest_common_decoder_record
        rows weights mixture hmix hmixture C hC
        (proposedDecoder C mixture) hreconstruct
    exact ⟨g, hg.2⟩

theorem decoderInnovation_nonneg
    {I U Z : Type*} [Fintype I] [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (hC : Function.Surjective C)
    (weights : I → ℝ) (rows : I → U → ℝ) (mixture : U → ℝ)
    (hweights : ∀ i, 0 ≤ weights i) (hrows : ∀ i u, 0 ≤ rows i u)
    (hmixture : ∀ u, 0 < mixture u)
    (hrowSum : ∀ i, ∑ u, rows i u = 1) (hmixtureSum : ∑ u, mixture u = 1) :
    0 ≤ decoderInnovation C weights rows mixture := by
  unfold decoderInnovation
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hweights i)
  exact Finset.sum_nonneg fun z _ ↦
    weighted_conditionalFibreKL_nonneg C hC (rows i) mixture
      (hrows i) hmixture (hrowSum i) hmixtureSum z

/-- Decoder innovation vanishes exactly when the proposed mixture-native
decoder reconstructs every experiment row.  Positive prior weights make the
averaged equality sharp row by row. -/
theorem decoderInnovation_eq_zero_iff_proposedDecoder_reconstructs
    {I U Z : Type*} [Fintype I] [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (hC : Function.Surjective C)
    (weights : I → ℝ) (rows : I → U → ℝ) (mixture : U → ℝ)
    (hweights : ∀ i, 0 < weights i) (hrows : ∀ i u, 0 ≤ rows i u)
    (hmixture : ∀ u, 0 < mixture u)
    (hrowSum : ∀ i, ∑ u, rows i u = 1) (hmixtureSum : ∑ u, mixture u = 1)
    (hmix : ∀ u, mixture u = ∑ i, weights i * rows i u) :
    decoderInnovation C weights rows mixture = 0 ↔
      ∀ i u, rows i u =
        pushforwardRow C (rows i) (C u) * proposedDecoder C mixture (C u) u := by
  have hcell_nonneg (i : I) (z : Z) :
      0 ≤ pushforwardRow C (rows i) z *
        conditionalFibreKL C (rows i) mixture z :=
    weighted_conditionalFibreKL_nonneg C hC (rows i) mixture
      (hrows i) hmixture (hrowSum i) hmixtureSum z
  constructor
  · intro hzero
    have hrow_zero (i : I) :
        ∑ z, pushforwardRow C (rows i) z *
          conditionalFibreKL C (rows i) mixture z = 0 := by
      have houter : ∀ j ∈ Finset.univ,
          weights j * (∑ z, pushforwardRow C (rows j) z *
            conditionalFibreKL C (rows j) mixture z) = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦
          mul_nonneg (le_of_lt (hweights j))
            (Finset.sum_nonneg fun z _ ↦ hcell_nonneg j z))).mp
        simpa [decoderInnovation] using hzero
      exact (mul_eq_zero.mp (houter i (Finset.mem_univ i))).resolve_left
        (ne_of_gt (hweights i))
    have hcell_zero (i : I) (z : Z) :
        pushforwardRow C (rows i) z *
          conditionalFibreKL C (rows i) mixture z = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ ↦ hcell_nonneg i z)).mp (hrow_zero i) z (Finset.mem_univ z)
    intro i u
    by_cases hpCzero : pushforwardRow C (rows i) (C u) = 0
    · have hpoint : rows i u = 0 := by
        have hall : ∀ v ∈ (Finset.univ.filter fun v ↦ C v = C u),
            rows i v = 0 := by
          apply (Finset.sum_eq_zero_iff_of_nonneg
            (fun v _ ↦ hrows i v)).mp
          simpa [pushforwardRow] using hpCzero
        exact hall u (by simp)
      rw [hpoint, hpCzero, zero_mul]
    · have hpC : 0 < pushforwardRow C (rows i) (C u) :=
        lt_of_le_of_ne (pushforwardRow_nonneg C (rows i) (hrows i) (C u))
          (Ne.symm hpCzero)
      have hKL : conditionalFibreKL C (rows i) mixture (C u) = 0 :=
        (mul_eq_zero.mp (hcell_zero i (C u))).resolve_left (ne_of_gt hpC)
      have heq := congrFun
        ((conditionalFibreKL_eq_zero_iff_of_pos C hC (rows i) mixture
          (hrows i) hmixture (C u) hpC).mp hKL) ⟨u, rfl⟩
      have hmC : 0 < pushforwardRow C mixture (C u) :=
        pushforwardRow_pos C mixture hC hmixture (C u)
      unfold proposedDecoder
      rw [if_pos rfl]
      field_simp [ne_of_gt hpC, ne_of_gt hmC] at heq ⊢
      linarith
  · intro hreconstruct
    have hmixreconstruct := mixture_reconstructs_from_common_decoder
      rows weights mixture hmix C (proposedDecoder C mixture) hreconstruct
    unfold decoderInnovation
    apply Finset.sum_eq_zero
    intro i _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro z _
    by_cases hpCzero : pushforwardRow C (rows i) z = 0
    · simp [hpCzero]
    · have hpC : 0 < pushforwardRow C (rows i) z :=
        lt_of_le_of_ne (pushforwardRow_nonneg C (rows i) (hrows i) z)
          (Ne.symm hpCzero)
      have hmC : 0 < pushforwardRow C mixture z :=
        pushforwardRow_pos C mixture hC hmixture z
      have hconditional : conditionalFibreKL C (rows i) mixture z = 0 := by
        apply (conditionalFibreKL_eq_zero_iff_of_pos C hC (rows i) mixture
          (hrows i) hmixture z hpC).2
        funext u
        have hr := hreconstruct i u
        have hm := hmixreconstruct u
        rw [u.property] at hr hm
        rw [hr, hm]
        field_simp [ne_of_gt hpC, ne_of_gt hmC]
      rw [hconditional, mul_zero]

/-- Sharp equality statement for decoder innovation: no conditional
information is lost exactly for records refining the experiment quotient. -/
theorem decoderInnovation_eq_zero_iff_refinesExperimentQuotient
    {I U Z : Type*} [Fintype I] [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (hC : Function.Surjective C)
    (weights : I → ℝ) (rows : I → U → ℝ) (mixture : U → ℝ)
    (hweights : ∀ i, 0 < weights i) (hrows : ∀ i u, 0 ≤ rows i u)
    (hmixture : ∀ u, 0 < mixture u)
    (hrowSum : ∀ i, ∑ u, rows i u = 1) (hmixtureSum : ∑ u, mixture u = 1)
    (hmix : ∀ u, mixture u = ∑ i, weights i * rows i u) :
    decoderInnovation C weights rows mixture = 0 ↔
      RefinesExperimentQuotient C rows mixture := by
  rw [decoderInnovation_eq_zero_iff_proposedDecoder_reconstructs
    C hC weights rows mixture hweights hrows hmixture hrowSum hmixtureSum hmix]
  exact (refinesExperimentQuotient_iff_proposedDecoder_reconstructs
    C hC weights rows mixture hmix hmixture).symm

end DecoderInnovationConditionalInformation
end NCG
