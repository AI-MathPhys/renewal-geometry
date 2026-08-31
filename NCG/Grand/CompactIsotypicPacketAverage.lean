/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactHaarRankOneAverage
import NCG.Grand.IsotypicPartialTraceFormula

/-!
# Partial trace of a compact isotypic packet average

The normalized Haar average of a packet conjugated on an irreducible tensor
factor has exactly the same multiplicity partial trace as the source packet.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder Kronecker Matrix.Norms.Elementwise

namespace NCG
namespace CompactIsotypicPacketAverage

variable {G : Type*} {I M : Type}
variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
variable [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]

noncomputable local instance matrixContinuousENorm :
    ContinuousENorm (Matrix (I × M) (I × M) ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _
    Matrix.seminormedAddCommGroup.toSeminormedAddGroup

/-- Conjugation orbit acting only on the irreducible tensor factor. -/
def isotypicPacketOrbit (ρ : G → Matrix I I ℂ)
    (J : Matrix (I × M) (I × M) ℂ) (g : G) :
    Matrix (I × M) (I × M) ℂ :=
  (ρ g ⊗ₖ (1 : Matrix M M ℂ)) * J *
    (ρ g ⊗ₖ (1 : Matrix M M ℂ))ᴴ

/-- Normalized compact-Haar average of an isotypic packet. -/
noncomputable def isotypicPacketAverage (ρ : G → Matrix I I ℂ)
    (J : Matrix (I × M) (I × M) ℂ) :
    Matrix (I × M) (I × M) ℂ :=
  ∫ g : G, isotypicPacketOrbit ρ J g
    ∂NCG.CompactHaarRankOneAverage.normalizedHaar G

/-- The multiplicity partial trace as a continuous linear map. -/
noncomputable def multiplicityPartialTraceCLM :
    Matrix (I × M) (I × M) ℂ →L[ℂ] Matrix M M ℂ :=
  ({ toFun := NCG.IsotypicPartialTrace.multiplicityPartialTrace
     map_add' := by
       intro A B
       ext a b
       simp [NCG.IsotypicPartialTrace.multiplicityPartialTrace,
         Finset.sum_add_distrib]
     map_smul' := by
       intro c A
       ext a b
       simp [NCG.IsotypicPartialTrace.multiplicityPartialTrace,
         Finset.mul_sum] } :
    Matrix (I × M) (I × M) ℂ →ₗ[ℂ] Matrix M M ℂ).toContinuousLinearMap

theorem continuous_isotypicPacketOrbit
    (ρ : G → Matrix I I ℂ)
    (hρtensor : Continuous (fun g =>
      ρ g ⊗ₖ (1 : Matrix M M ℂ)))
    (J : Matrix (I × M) (I × M) ℂ) :
    Continuous (isotypicPacketOrbit ρ J) := by
  unfold isotypicPacketOrbit
  fun_prop

theorem integrable_isotypicPacketOrbit
    (ρ : G → Matrix I I ℂ)
    (hρtensor : Continuous (fun g =>
      ρ g ⊗ₖ (1 : Matrix M M ℂ)))
    (J : Matrix (I × M) (I × M) ℂ) :
    Integrable (isotypicPacketOrbit ρ J)
      (NCG.CompactHaarRankOneAverage.normalizedHaar G) := by
  have hc := continuous_isotypicPacketOrbit ρ hρtensor J
  exact integrableOn_univ.mp
    (hc.continuousOn.integrableOn_of_subset_isCompact isCompact_univ
      MeasurableSet.univ Subset.rfl
      (measure_ne_top
        (NCG.CompactHaarRankOneAverage.normalizedHaar G) Set.univ))

/-- The Haar average preserves the source packet's multiplicity partial
trace exactly. -/
theorem isotypicPacketAverage_partialTrace_eq
    (ρ : G → Matrix I I ℂ)
    (hρtensor : Continuous (fun g =>
      ρ g ⊗ₖ (1 : Matrix M M ℂ)))
    (hunit : ∀ g, (ρ g)ᴴ * ρ g = 1)
    (J : Matrix (I × M) (I × M) ℂ) :
    NCG.IsotypicPartialTrace.multiplicityPartialTrace
        (isotypicPacketAverage ρ J) =
      NCG.IsotypicPartialTrace.multiplicityPartialTrace J := by
  have hint := integrable_isotypicPacketOrbit ρ hρtensor J
  change multiplicityPartialTraceCLM
      (∫ g : G, isotypicPacketOrbit ρ J g
        ∂NCG.CompactHaarRankOneAverage.normalizedHaar G) = _
  calc
    _ = ∫ g : G, multiplicityPartialTraceCLM
          (isotypicPacketOrbit ρ J g)
        ∂NCG.CompactHaarRankOneAverage.normalizedHaar G :=
      (ContinuousLinearMap.integral_comp_comm
        multiplicityPartialTraceCLM hint).symm
    _ = ∫ _g : G, NCG.IsotypicPartialTrace.multiplicityPartialTrace J
        ∂NCG.CompactHaarRankOneAverage.normalizedHaar G := by
      apply integral_congr_ae
      filter_upwards [] with g
      change NCG.IsotypicPartialTrace.multiplicityPartialTrace
          (isotypicPacketOrbit ρ J g) = _
      exact
        NCG.IsotypicPartialTrace.multiplicityPartialTrace_kronecker_unitary_conjugation
          (ρ g) (hunit g) J
    _ = _ := by simp

/-- The compact-Haar isotypic packet average is invariant under conjugation
by the tensor representation. -/
theorem isotypicPacketAverage_covariant
    (ρ : G →* Matrix I I ℂ)
    (hρtensor : Continuous (fun g =>
      ρ g ⊗ₖ (1 : Matrix M M ℂ)))
    (J : Matrix (I × M) (I × M) ℂ) (h : G) :
    (ρ h ⊗ₖ (1 : Matrix M M ℂ)) *
        isotypicPacketAverage ρ J *
        (ρ h ⊗ₖ (1 : Matrix M M ℂ))ᴴ =
      isotypicPacketAverage ρ J := by
  let R : G → Matrix (I × M) (I × M) ℂ := fun g =>
    ρ g ⊗ₖ (1 : Matrix M M ℂ)
  have hRmul : ∀ g k, R (g * k) = R g * R k := by
    intro g k
    dsimp [R]
    rw [map_mul, ← Matrix.mul_kronecker_mul]
    simp
  let conjugate : Matrix (I × M) (I × M) ℂ →ₗ[ℂ]
      Matrix (I × M) (I × M) ℂ :=
    { toFun := fun A => R h * A * (R h)ᴴ
      map_add' := by
        intro A B
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c A
        rw [Matrix.mul_smul, Matrix.smul_mul]
        simp }
  let conjugateC := conjugate.toContinuousLinearMap
  have hint := integrable_isotypicPacketOrbit ρ hρtensor J
  change conjugateC (isotypicPacketAverage ρ J) =
    isotypicPacketAverage ρ J
  rw [isotypicPacketAverage]
  calc
    conjugateC (∫ g : G, isotypicPacketOrbit ρ J g
        ∂NCG.CompactHaarRankOneAverage.normalizedHaar G) =
        ∫ g : G, conjugateC (isotypicPacketOrbit ρ J g)
          ∂NCG.CompactHaarRankOneAverage.normalizedHaar G :=
      (ContinuousLinearMap.integral_comp_comm conjugateC hint).symm
    _ = ∫ g : G, isotypicPacketOrbit ρ J (h * g)
          ∂NCG.CompactHaarRankOneAverage.normalizedHaar G := by
      apply integral_congr_ae
      filter_upwards [] with g
      dsimp [conjugateC, conjugate, R]
      unfold isotypicPacketOrbit
      change R h * (R g * J * (R g)ᴴ) * (R h)ᴴ =
        R (h * g) * J * (R (h * g))ᴴ
      rw [hRmul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = ∫ g : G, isotypicPacketOrbit ρ J g
          ∂NCG.CompactHaarRankOneAverage.normalizedHaar G :=
      integral_mul_left_eq_self
        (μ := NCG.CompactHaarRankOneAverage.normalizedHaar G)
        (isotypicPacketOrbit ρ J) h

/-- Exact compact-Haar Schur formula with the manuscript's source-defined
multiplicity packet `Tr_I J`. -/
theorem isotypicPacketAverage_eq_normalized_identity_kronecker_sourcePartialTrace
    [Nonempty I]
    (ρ : G →* Matrix I I ℂ)
    [CategoryTheory.Simple
      (FDRep.of (NCG.CompactIsotypicSchur.matrixRepresentation ρ))]
    (hρtensor : Continuous (fun g =>
      ρ g ⊗ₖ (1 : Matrix M M ℂ)))
    (hunit : ∀ g, (ρ g)ᴴ * ρ g = 1)
    (J : Matrix (I × M) (I × M) ℂ) :
    isotypicPacketAverage ρ J =
      ((Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) ⊗ₖ
        NCG.IsotypicPartialTrace.multiplicityPartialTrace J := by
  let F := isotypicPacketAverage ρ J
  have hRunit : ∀ g,
      (ρ g ⊗ₖ (1 : Matrix M M ℂ))ᴴ *
          (ρ g ⊗ₖ (1 : Matrix M M ℂ)) = 1 := by
    intro g
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hunit g]
    simp
  have hcomm : ∀ g,
      F * (ρ g ⊗ₖ (1 : Matrix M M ℂ)) =
        (ρ g ⊗ₖ (1 : Matrix M M ℂ)) * F := by
    intro g
    have hcov := isotypicPacketAverage_covariant ρ hρtensor J g
    change (ρ g ⊗ₖ (1 : Matrix M M ℂ)) * F *
      (ρ g ⊗ₖ (1 : Matrix M M ℂ))ᴴ = F at hcov
    calc
      F * (ρ g ⊗ₖ (1 : Matrix M M ℂ)) =
          ((ρ g ⊗ₖ (1 : Matrix M M ℂ)) * F *
            (ρ g ⊗ₖ (1 : Matrix M M ℂ))ᴴ) *
              (ρ g ⊗ₖ (1 : Matrix M M ℂ)) := by rw [hcov]
      _ = (ρ g ⊗ₖ (1 : Matrix M M ℂ)) * F *
          ((ρ g ⊗ₖ (1 : Matrix M M ℂ))ᴴ *
            (ρ g ⊗ₖ (1 : Matrix M M ℂ))) := by
            simp only [Matrix.mul_assoc]
      _ = (ρ g ⊗ₖ (1 : Matrix M M ℂ)) * F := by
            rw [hRunit g, Matrix.mul_one]
  have hformula :=
    NCG.IsotypicPartialTrace.isotypic_partialTrace_formula_of_global_covariance
      ρ F hcomm
  change F = _
  rw [hformula]
  have htrace : NCG.IsotypicPartialTrace.multiplicityPartialTrace F =
      NCG.IsotypicPartialTrace.multiplicityPartialTrace J := by
    simpa [F] using
      (isotypicPacketAverage_partialTrace_eq ρ hρtensor hunit J)
  rw [htrace]

/-- The manuscript multiplicity packet is positive semidefinite whenever the
source packet is positive semidefinite. -/
theorem source_multiplicity_packet_posSemidef
    (J : Matrix (I × M) (I × M) ℂ) (hJ : J.PosSemidef) :
    (NCG.IsotypicPartialTrace.multiplicityPartialTrace J).PosSemidef :=
  NCG.IsotypicPartialTrace.multiplicityPartialTrace_posSemidef J hJ

end CompactIsotypicPacketAverage
end NCG
