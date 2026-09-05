/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMGaugeQuotientExact

/-!
# The Higgs-vacuum stabilizer inside the Standard-Model gauge group

This proves the group-theoretic clause of `thm:SM-active-SM-II`: the
stabilizer of a nonzero reference weak doublet in `S(U(3) × U(2))` is
canonically `U(3)`.  The weak block is forced to be
`diag(conj(det A), 1)` by unitarity, the fixed-vector equation, and the product
determinant constraint.
-/

open Matrix

namespace NCG

/-- Reference unit weak doublet. -/
def smHiggsVacuum : Fin 2 → ℂ := fun i => if i = 1 then 1 else 0

/-- The subgroup of `S(U(3) × U(2))` fixing the reference Higgs doublet. -/
noncomputable def smHiggsVacuumStabilizer : Subgroup SMGaugeGroup where
  carrier := {g | g.1.2.1.mulVec smHiggsVacuum = smHiggsVacuum}
  one_mem' := by
    change (1 : Matrix (Fin 2) (Fin 2) ℂ).mulVec smHiggsVacuum = smHiggsVacuum
    exact Matrix.one_mulVec smHiggsVacuum
  mul_mem' := by
    intro a b ha hb
    change ((a * b).1.2.1).mulVec smHiggsVacuum = smHiggsVacuum
    rw [show (a * b).1.2.1 = a.1.2.1 * b.1.2.1 from rfl,
      ← Matrix.mulVec_mulVec, hb, ha]
  inv_mem' := by
    intro a ha
    change ((a⁻¹).1.2.1).mulVec smHiggsVacuum = smHiggsVacuum
    calc
      ((a⁻¹).1.2.1).mulVec smHiggsVacuum =
          ((a⁻¹).1.2.1).mulVec (a.1.2.1.mulVec smHiggsVacuum) := by rw [ha]
      _ = (((a⁻¹).1.2.1) * a.1.2.1).mulVec smHiggsVacuum := by
        rw [Matrix.mulVec_mulVec]
      _ = smHiggsVacuum := by
        have hmul : ((a⁻¹).1.2 : SMGaugeU2) * a.1.2 = 1 := inv_mul_cancel _
        have hmat : ((a⁻¹).1.2.1) * a.1.2.1 = 1 := congrArg Subtype.val hmul
        rw [hmat, Matrix.one_mulVec]

/-- Weak compensator associated with a colour-unitary matrix. -/
noncomputable def smWeakCompensatorMatrix (A : SMGaugeU3) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then star A.1.det else 1)

theorem smWeakCompensatorMatrix_unitary (A : SMGaugeU3) :
    smWeakCompensatorMatrix A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hd := Matrix.det_of_mem_unitary A.2
  have hdcomm : A.1.det * (starRingEnd ℂ) A.1.det = 1 := hd.2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [smWeakCompensatorMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      hd.1, hd.2, hdcomm]

/-- The determinant of the compensating weak block. -/
theorem smWeakCompensatorMatrix_det (A : SMGaugeU3) :
    (smWeakCompensatorMatrix A).det = star A.1.det := by
  simp [smWeakCompensatorMatrix, Matrix.det_fin_two]

/-- The weak compensator as a unitary matrix. -/
noncomputable def smWeakCompensator (A : SMGaugeU3) : SMGaugeU2 :=
  ⟨smWeakCompensatorMatrix A, smWeakCompensatorMatrix_unitary A⟩

@[simp] theorem smWeakCompensator_val (A : SMGaugeU3) :
    (smWeakCompensator A).1 = smWeakCompensatorMatrix A := rfl

theorem smWeakCompensator_fixes_vacuum (A : SMGaugeU3) :
    (smWeakCompensator A).1.mulVec smHiggsVacuum = smHiggsVacuum := by
  funext i
  fin_cases i <;>
    simp [smWeakCompensator, smWeakCompensatorMatrix, smHiggsVacuum,
      Matrix.mulVec, Fin.sum_univ_two]

@[simp] theorem smWeakCompensator_one :
    smWeakCompensator (1 : SMGaugeU3) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [smWeakCompensator, smWeakCompensatorMatrix]

theorem smWeakCompensator_mul (A B : SMGaugeU3) :
    smWeakCompensator (A * B) = smWeakCompensator A * smWeakCompensator B := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [smWeakCompensator, smWeakCompensatorMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.det_mul, star_mul'] <;> ring

/-- The element of `S(U(3) × U(2))` determined by a colour-unitary block. -/
noncomputable def smHiggsStabilizerElement (A : SMGaugeU3) : SMGaugeGroup := by
  refine ⟨(A, smWeakCompensator A), ?_⟩
  change unitaryDetHom (Fin 3) A *
    unitaryDetHom (Fin 2) (smWeakCompensator A) = 1
  apply Subtype.ext
  change A.1.det * (smWeakCompensator A).1.det = 1
  rw [smWeakCompensator_val, smWeakCompensatorMatrix_det]
  exact (Matrix.det_of_mem_unitary A.2).2

/-- The canonical embedding of `U(3)` lands in the Higgs stabilizer. -/
noncomputable def smHiggsStabilizerEmbedding :
    SMGaugeU3 →* smHiggsVacuumStabilizer where
  toFun A := ⟨smHiggsStabilizerElement A,
    smWeakCompensator_fixes_vacuum A⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact smWeakCompensator_one
  map_mul' A B := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact smWeakCompensator_mul A B

/-- A weak unitary block fixing the reference doublet and satisfying the
`S(U(3) × U(2))` determinant constraint is the unique compensator of its
colour block. -/
theorem higgsStabilizer_weakBlock_eq_compensator
    (g : smHiggsVacuumStabilizer) :
    g.1.1.2 = smWeakCompensator g.1.1.1 := by
  let A : SMGaugeU3 := g.1.1.1
  let B : SMGaugeU2 := g.1.1.2
  have h01 : B.1 0 1 = 0 := by
    have h := congrFun g.2 0
    simpa [B, smHiggsVacuum, Matrix.mulVec, Fin.sum_univ_two] using h
  have h11 : B.1 1 1 = 1 := by
    have h := congrFun g.2 1
    simpa [B, smHiggsVacuum, Matrix.mulVec, Fin.sum_univ_two] using h
  have h10 : B.1 1 0 = 0 := by
    have h := congrFun (congrFun B.2.1 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h01, h11] using h
  have hdetProduct : A.1.det * B.1.det = 1 := by
    have h := congrArg Subtype.val g.1.2
    simpa [A, B, determinantProductHom, unitaryDetHom] using h
  have hdetB : B.1.det = B.1 0 0 := by
    rw [Matrix.det_fin_two, h01, h10, h11]
    ring
  have hproduct : A.1.det * B.1 0 0 = 1 := by
    rw [← hdetB]
    exact hdetProduct
  have h00 : B.1 0 0 = star A.1.det := by
    have hd := (Matrix.det_of_mem_unitary A.2).1
    calc
      B.1 0 0 = 1 * B.1 0 0 := by rw [one_mul]
      _ = (star A.1.det * A.1.det) * B.1 0 0 := by rw [hd]
      _ = star A.1.det * (A.1.det * B.1 0 0) := by rw [mul_assoc]
      _ = star A.1.det := by rw [hproduct, mul_one]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, B, smWeakCompensator, smWeakCompensatorMatrix,
      h00, h01, h10, h11]

/-- **Higgs stabilizer theorem (CA.16).**  The stabilizer of the nonzero
reference weak doublet in `S(U(3) × U(2))` is canonically `U(3)`. -/
noncomputable def smHiggsVacuumStabilizerEquivU3 :
    smHiggsVacuumStabilizer ≃* SMGaugeU3 := by
  let projection : smHiggsVacuumStabilizer →* SMGaugeU3 :=
    { toFun := fun g => g.1.1.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact
    { toFun := projection
      invFun := smHiggsStabilizerEmbedding
      left_inv := by
        intro g
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact (higgsStabilizer_weakBlock_eq_compensator g).symm
      right_inv := by intro A; rfl
      map_mul' := projection.map_mul }

end NCG
