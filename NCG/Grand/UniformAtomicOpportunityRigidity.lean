/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.K4Opportunity
import NCG.Grand.K4CutCycleIsotypicSchur
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Uniform atomic opportunity rigidity

This file gives the exact encoding of
`thm:atomic-opportunity-rigidity` from the Gran--Tensor manuscript.  It adds
the forcing and probabilistic clauses that are deliberately absent from the
older arithmetic/Gram lemma `NCG.atomic_opportunity_rigidity`.

The completed-cycle selector is the literal reset kernel on four labels.  Its
finite path law is a product, and its joint law with the endpoint bit factors.
The contrast Gram is derived from the uniform expectation.  Finally, the
relative permutation action is written in the basis
`e₀-e₃, e₁-e₃, e₂-e₃`; its determinant is computed on that three-dimensional
carrier, while the scalar joint commutant supplies the usual irreducibility
certificate.
-/

open scoped BigOperators
open Matrix

namespace NCG

/-! ## Sourcewise-uniform atom counting -/

/-- Four equal source-`H` opportunity atoms are forced by their total mass
`4/5` and individual mass `1/5`. -/
theorem sourceH_uniform_atoms_force_four
    {Ω : Type*} [Fintype Ω]
    (atomWeight : ℚ) (hWeight : atomWeight = 1 / 5)
    (hTotal : (Fintype.card Ω : ℚ) * atomWeight = 4 / 5) :
    Fintype.card Ω = 4 := by
  rw [hWeight] at hTotal
  have hCard : (Fintype.card Ω : ℚ) = 4 := by
    norm_num at hTotal ⊢
    linarith
  exact_mod_cast hCard

/-- Two equal completed source-`P` endpoint atoms are forced by their total
mass `2/3` and individual mass `1/3`. -/
theorem sourceP_uniform_atoms_force_two
    {E : Type*} [Fintype E]
    (atomWeight : ℚ) (hWeight : atomWeight = 1 / 3)
    (hTotal : (Fintype.card E : ℚ) * atomWeight = 2 / 3) :
    Fintype.card E = 2 := by
  rw [hWeight] at hTotal
  have hCard : (Fintype.card E : ℚ) = 2 := by
    norm_num at hTotal ⊢
    linarith
  exact_mod_cast hCard

/-! ## Reset selector and independent fair endpoint -/

/-- The completed-cycle opportunity selector: every row is the same uniform
law, hence older provenance cannot feed back into the next label. -/
def atomicOpportunityResetKernel (_previous _next : Fin 4) : ℚ := 1 / 4

/-- Every row of the reset selector is a probability distribution. -/
theorem atomicOpportunityResetKernel_row_sum (previous : Fin 4) :
    ∑ next, atomicOpportunityResetKernel previous next = 1 := by
  simp [atomicOpportunityResetKernel]

/-- Reset means literal independence from the previous opportunity label. -/
theorem atomicOpportunityResetKernel_no_feedback
    (previous previous' next : Fin 4) :
    atomicOpportunityResetKernel previous next =
      atomicOpportunityResetKernel previous' next := rfl

/-- Every finite completed-cycle label history has the iid uniform product
probability `(1/4)^n`. -/
theorem atomicOpportunityResetKernel_iid_path
    {n : ℕ} (previous next : Fin n → Fin 4) :
    ∏ k, atomicOpportunityResetKernel (previous k) (next k) =
      (1 / 4 : ℚ) ^ n := by
  simp [atomicOpportunityResetKernel]

/-- Uniform opportunity law. -/
def atomicOpportunityLaw (_ : Fin 4) : ℚ := 1 / 4

/-- Independent fair endpoint-bit law. -/
def atomicEndpointLaw (_ : Bool) : ℚ := 1 / 2

/-- The joint completed-cycle law. -/
def atomicOpportunityEndpointLaw (o : Fin 4) (endpoint : Bool) : ℚ :=
  atomicOpportunityLaw o * atomicEndpointLaw endpoint

/-- The joint law factors, which is the exact independence statement. -/
theorem atomicOpportunity_endpoint_independent (o : Fin 4) (endpoint : Bool) :
    atomicOpportunityEndpointLaw o endpoint =
      atomicOpportunityLaw o * atomicEndpointLaw endpoint := rfl

/-- The opportunity marginal of the joint law is uniform. -/
theorem atomicOpportunityEndpointLaw_opportunity_marginal (o : Fin 4) :
    ∑ endpoint : Bool, atomicOpportunityEndpointLaw o endpoint = 1 / 4 := by
  fin_cases o <;>
    simp [atomicOpportunityEndpointLaw, atomicOpportunityLaw,
      atomicEndpointLaw] <;> norm_num

/-- The endpoint marginal of the joint law is a fair bit. -/
theorem atomicOpportunityEndpointLaw_endpoint_marginal (endpoint : Bool) :
    ∑ o : Fin 4, atomicOpportunityEndpointLaw o endpoint = 1 / 2 := by
  simp [atomicOpportunityEndpointLaw, atomicOpportunityLaw, atomicEndpointLaw]

/-! ## The derived centered-contrast Gram -/

/-- Centered point contrast `Xᵢ = 1_{O=i} - 1/4`. -/
noncomputable def atomicOpportunityContrast (i o : Fin 4) : ℂ :=
  (if o = i then 1 else 0) - 1 / 4

/-- The contrast Gram, defined as the expectation under the uniform law. -/
noncomputable def atomicOpportunityContrastGram : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => ∑ o : Fin 4,
    (1 / 4 : ℂ) * atomicOpportunityContrast i o * atomicOpportunityContrast j o

/-- Direct covariance calculation `E(XᵢXⱼ)=δᵢⱼ/4-1/16`. -/
theorem atomicOpportunityContrastGram_entry (i j : Fin 4) :
    atomicOpportunityContrastGram i j =
      (1 / 4 : ℂ) * ((if i = j then 1 else 0) - 1 / 4) := by
  fin_cases i <;> fin_cases j <;>
    simp [atomicOpportunityContrastGram, atomicOpportunityContrast,
      Fin.sum_univ_four] <;> norm_num

/-- The relative projector `I - (1/4)11*`. -/
noncomputable def atomicOpportunityRelativeProjector : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => (if i = j then 1 else 0) - 1 / 4

/-- The manuscript identity `GΩ = (1/4) P_rel`, now derived from the
expectation defining `GΩ`. -/
theorem atomicOpportunityContrastGram_eq_quarter_relativeProjector :
    atomicOpportunityContrastGram =
      (1 / 4 : ℂ) • atomicOpportunityRelativeProjector := by
  ext i j
  rw [atomicOpportunityContrastGram_entry]
  simp [atomicOpportunityRelativeProjector]

/-- The relative projector kills the constant direction. -/
theorem atomicOpportunityRelativeProjector_kills_constants :
    atomicOpportunityRelativeProjector *ᵥ (fun _ => (1 : ℂ)) = 0 := by
  funext i
  fin_cases i <;>
    simp [atomicOpportunityRelativeProjector, Matrix.mulVec, dotProduct]

/-- On the sum-zero carrier the relative projector is the identity. -/
theorem atomicOpportunityRelativeProjector_on_meanZero
    (v : Fin 4 → ℂ) (hv : v ∈ meanZero) :
    atomicOpportunityRelativeProjector *ᵥ v = v := by
  have hsum : ∑ i, v i = 0 := hv
  funext i
  have hsum' : v 0 + v 1 + v 2 + v 3 = 0 := by
    simpa [Fin.sum_univ_four] using hsum
  fin_cases i <;>
    simp [atomicOpportunityRelativeProjector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] <;> linear_combination (-1 / 4 : ℂ) * hsum'

/-- The range of the derived Gram is exactly the three-dimensional relative
carrier. -/
theorem atomicOpportunityContrastGram_range :
    LinearMap.range atomicOpportunityContrastGram.mulVecLin = meanZero := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change ∑ i, (atomicOpportunityContrastGram *ᵥ x) i = 0
    simp only [atomicOpportunityContrastGram_eq_quarter_relativeProjector,
      smul_mulVec, Pi.smul_apply]
    have hzero : ∑ i, (atomicOpportunityRelativeProjector *ᵥ x) i = 0 := by
      simp [atomicOpportunityRelativeProjector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four]
      ring
    change ∑ i, (1 / 4 : ℂ) *
      (atomicOpportunityRelativeProjector *ᵥ x) i = 0
    rw [← Finset.mul_sum, hzero, mul_zero]
  · intro y hy
    refine ⟨(4 : ℂ) • y, ?_⟩
    rw [Matrix.mulVecLin_apply,
      atomicOpportunityContrastGram_eq_quarter_relativeProjector,
      smul_mulVec, Matrix.mulVec_smul]
    rw [atomicOpportunityRelativeProjector_on_meanZero y hy]
    ext i
    simp

/-- The derived contrast Gram has rank exactly three. -/
theorem atomicOpportunityContrastGram_rank :
    Matrix.rank atomicOpportunityContrastGram = 3 := by
  rw [Matrix.rank, atomicOpportunityContrastGram_range]
  exact smst_record_native_generations.2.2.2.1

/-- Every nonzero vector in the relative carrier has the unique positive
Gram eigenvalue `1/4`; together with rank three this is
`λmin⁺(GΩ)=1/4`. -/
theorem atomicOpportunityContrastGram_positive_eigenvalue
    (v : Fin 4 → ℂ) (hv : v ∈ meanZero) (_hne : v ≠ 0) :
    atomicOpportunityContrastGram *ᵥ v = (1 / 4 : ℂ) • v ∧
      (0 : ℝ) < 1 / 4 := by
  constructor
  · rw [atomicOpportunityContrastGram_eq_quarter_relativeProjector,
      smul_mulVec,
      atomicOpportunityRelativeProjector_on_meanZero v hv]
  · norm_num

/-! ## The standard relative `S₄` action -/

/-- Basis vector `eⱼ-e₃` of the integral relative carrier. -/
def atomicRelativeBasisVector (j : Fin 3) : Fin 4 → ℤ :=
  fun i => (if i = j.castSucc then 1 else 0) - (if i = 3 then 1 else 0)

/-- Matrix of a relabelling on the relative basis
`e₀-e₃, e₁-e₃, e₂-e₃`.  Taking the first three coordinates is legitimate
because every permuted basis vector still has coordinate sum zero. -/
def atomicRelativePermutationMatrix (σ : Equiv.Perm (Fin 4)) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j =>
    (σ.permMatrix ℤ) i.castSucc j.castSucc - (σ.permMatrix ℤ) i.castSucc 3

/-- The displayed matrix really gives the restriction of the full
permutation action to the relative carrier in the displayed basis. -/
theorem atomicRelativePermutationMatrix_represents_restriction :
    ∀ (σ : Equiv.Perm (Fin 4)) (j : Fin 3) (i : Fin 4),
      (σ.permMatrix ℤ *ᵥ atomicRelativeBasisVector j) i =
        ∑ k : Fin 3,
          atomicRelativePermutationMatrix σ k j * atomicRelativeBasisVector k i := by
  decide +kernel

/-- The determinant of the restricted three-dimensional action is the sign
of the relabelling.  This is not merely the determinant of the full
four-dimensional permutation matrix. -/
theorem atomicRelativePermutationMatrix_det_sign
    (σ : Equiv.Perm (Fin 4)) :
    (atomicRelativePermutationMatrix σ).det = Equiv.Perm.sign σ := by
  revert σ
  decide +kernel

/-- Concrete irreducibility certificate for the standard triplet: an
equivariant idempotent is either zero or identity.  Over a finite group in
characteristic zero this is equivalent to absence of a proper invariant
summand. -/
theorem k4StandardTriplet_equivariantIdempotent_trivial
    (P : Matrix (Fin 3) (Fin 3) ℂ)
    (hs : P * k4StandardTransposition = k4StandardTransposition * P)
    (ht : P * k4StandardFourCycle = k4StandardFourCycle * P)
    (hP : P * P = P) :
    P = 0 ∨ P = 1 := by
  obtain ⟨α, rfl⟩ := k4StandardTriplet_jointCommutant_scalar P hs ht
  have hα := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) hP
  simp [Matrix.mul_apply, Fin.sum_univ_three] at hα
  have hα' : α ^ 2 = α := by simpa [pow_two] using hα
  rcases eq_zero_or_one_of_sq_eq_self hα' with hzero | hone
  · left
    simp [hzero]
  · right
    simp [hone]

/-- Exact packet collecting every mathematical clause of
`thm:atomic-opportunity-rigidity`.  The final implication records the
manuscript's physicality qualifier: covariance of the complete future table
is a prerequisite, not a consequence of the abstract `S₄` action. -/
theorem uniform_atomic_opportunity_rigidity
    {Ω E : Type*} [Fintype Ω] [Fintype E]
    (hWeight pWeight : ℚ)
    (hhWeight : hWeight = 1 / 5)
    (hpWeight : pWeight = 1 / 3)
    (hHTotal : (Fintype.card Ω : ℚ) * hWeight = 4 / 5)
    (hPTotal : (Fintype.card E : ℚ) * pWeight = 2 / 3)
    (futureTableCovariant abstractRelabellingPhysical : Prop)
    (hPhysical : abstractRelabellingPhysical → futureTableCovariant) :
    Fintype.card Ω = 4 ∧ Fintype.card E = 2
      ∧ (∀ previous previous' next : Fin 4,
          atomicOpportunityResetKernel previous next =
            atomicOpportunityResetKernel previous' next)
      ∧ (∀ o endpoint, atomicOpportunityEndpointLaw o endpoint =
          atomicOpportunityLaw o * atomicEndpointLaw endpoint)
      ∧ atomicOpportunityContrastGram =
          (1 / 4 : ℂ) • atomicOpportunityRelativeProjector
      ∧ Matrix.rank atomicOpportunityContrastGram = 3
      ∧ (∀ σ : Equiv.Perm (Fin 4),
          (atomicRelativePermutationMatrix σ).det = Equiv.Perm.sign σ)
      ∧ (abstractRelabellingPhysical → futureTableCovariant) := by
  exact ⟨sourceH_uniform_atoms_force_four hWeight hhWeight hHTotal,
    sourceP_uniform_atoms_force_two pWeight hpWeight hPTotal,
    atomicOpportunityResetKernel_no_feedback,
    atomicOpportunity_endpoint_independent,
    atomicOpportunityContrastGram_eq_quarter_relativeProjector,
    atomicOpportunityContrastGram_rank,
    atomicRelativePermutationMatrix_det_sign,
    hPhysical⟩

end NCG
