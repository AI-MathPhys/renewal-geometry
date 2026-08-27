/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMGroup

/-!
# Exact global Standard Model gauge quotient

This file closes the group-isomorphism packaging in `thm:SM-group`.  It constructs the explicit
homomorphism

`(SU(3) × SU(2)) × U(1) → S(U(3) × U(2))`,

proves it surjective, identifies its kernel with the displayed central sixth roots of unity, and
applies the first isomorphism theorem.
-/

open Matrix

namespace NCG

noncomputable def phaseUnitary (n : Type) [Fintype n] [DecidableEq n]
    (z : Circle) : Matrix.unitaryGroup n ℂ :=
  ⟨(z : ℂ) • (1 : Matrix n n ℂ), by
    rw [Matrix.mem_unitaryGroup_iff']
    have hz : star (z : ℂ) * (z : ℂ) = 1 := by
      change (starRingEnd ℂ) (z : ℂ) * (z : ℂ) = 1
      rw [← Circle.coe_inv_eq_conj]
      exact inv_mul_cancel₀ (Circle.coe_ne_zero z)
    simpa using sm_group.2.1 (z : ℂ) (1 : Matrix n n ℂ) hz⟩

@[simp] theorem phaseUnitary_val (n : Type) [Fintype n] [DecidableEq n]
    (z : Circle) : (phaseUnitary n z : Matrix n n ℂ) = (z : ℂ) • 1 := rfl

abbrev SMGaugeSU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ
abbrev SMGaugeSU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ
abbrev SMGaugeU3 := Matrix.unitaryGroup (Fin 3) ℂ
abbrev SMGaugeU2 := Matrix.unitaryGroup (Fin 2) ℂ
abbrev SMGaugeCover := (SMGaugeSU3 × SMGaugeSU2) × Circle

noncomputable def specialToUnitary (n : Type) [Fintype n] [DecidableEq n] :
    Matrix.specialUnitaryGroup n ℂ →* Matrix.unitaryGroup n ℂ :=
  Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup

noncomputable def phaseUnitaryHom (n : Type) [Fintype n] [DecidableEq n] :
    Circle →* Matrix.unitaryGroup n ℂ where
  toFun := phaseUnitary n
  map_one' := by
    apply Subtype.ext
    simp [phaseUnitary]
  map_mul' z w := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    simp [phaseUnitary, Circle.coe_mul]
    ring

/-- The explicit central-charge map `(g₃,g₂,z) ↦ (z⁻²g₃,z³g₂)`. -/
noncomputable def smGaugeAmbientHom : SMGaugeCover →* (SMGaugeU3 × SMGaugeU2) where
  toFun x :=
    (phaseUnitaryHom (Fin 3) ((x.2⁻¹) ^ 2) * specialToUnitary (Fin 3) x.1.1,
     phaseUnitaryHom (Fin 2) (x.2 ^ 3) * specialToUnitary (Fin 2) x.1.2)
  map_one' := by
    ext <;> simp
  map_mul' x y := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Submonoid.coe_mul]
      simp [phaseUnitaryHom, phaseUnitary, specialToUnitary, Matrix.mul_smul,
        Matrix.smul_mul, mul_assoc, mul_left_comm]
      rw [smul_smul]
      congr 1
      ring
    · apply Subtype.ext
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Submonoid.coe_mul]
      simp [phaseUnitaryHom, phaseUnitary, specialToUnitary, Matrix.mul_smul,
        Matrix.smul_mul, mul_assoc, mul_left_comm]
      rw [smul_smul]
      congr 1
      ring

noncomputable def unitaryDetHom (n : Type) [Fintype n] [DecidableEq n] :
    Matrix.unitaryGroup n ℂ →* unitary ℂ where
  toFun A := ⟨A.1.det, Matrix.det_of_mem_unitary A.2⟩
  map_one' := by ext; simp
  map_mul' A B := by ext; simp

noncomputable def determinantProductHom : (SMGaugeU3 × SMGaugeU2) →* unitary ℂ where
  toFun x := unitaryDetHom (Fin 3) x.1 * unitaryDetHom (Fin 2) x.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    ac_rfl

/-- `S(U(3) × U(2))`, represented as the kernel of the product determinant. -/
noncomputable abbrev SMGaugeGroup := determinantProductHom.ker

theorem smGaugeAmbientHom_mem (x : SMGaugeCover) :
    smGaugeAmbientHom x ∈ determinantProductHom.ker := by
  apply Subtype.ext
  change ((smGaugeAmbientHom x).1.1.det * (smGaugeAmbientHom x).2.1.det : ℂ) = 1
  have hg3 : x.1.1.1.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp x.1.1.2).2
  have hg2 : x.1.2.1.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp x.1.2.2).2
  have h := sm_group.1 x.1.1.1 x.1.2.1 (x.2 : ℂ) (Circle.coe_ne_zero x.2)
  rw [hg3, hg2, mul_one] at h
  simpa [smGaugeAmbientHom, phaseUnitaryHom, phaseUnitary, specialToUnitary] using h

noncomputable def smGaugeHom : SMGaugeCover →* SMGaugeGroup :=
  smGaugeAmbientHom.codRestrict determinantProductHom.ker smGaugeAmbientHom_mem

noncomputable def unitaryToCircle (u : unitary ℂ) : Circle :=
  ⟨u.1, by
    change u.1 ∈ Metric.sphere (0 : ℂ) 1
    apply mem_sphere_zero_iff_norm.mpr
    exact CStarRing.norm_of_mem_unitary u.2⟩

@[simp] theorem unitaryToCircle_coe (u : unitary ℂ) :
    (unitaryToCircle u : ℂ) = u.1 := rfl

theorem smGaugeHom_surjective : Function.Surjective smGaugeHom := by
  intro y
  let bdet : Circle := unitaryToCircle (unitaryDetHom (Fin 2) y.1.2)
  obtain ⟨z, hz⟩ :=
    (Circle.isQuotientCoveringMap_npow 6).toIsQuotientMap.surjective bdet
  have hz6 : (z : ℂ) ^ 6 = y.1.2.1.det := congrArg Subtype.val hz
  have hAB : y.1.1.1.det * y.1.2.1.det = 1 := by
    have h := congrArg Subtype.val y.2
    simpa [determinantProductHom, unitaryDetHom] using h
  let g3u : SMGaugeU3 := phaseUnitary (Fin 3) (z ^ 2) * y.1.1
  have hg3det : g3u.1.det = 1 := by
    change (((z : ℂ) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℂ) * y.1.1.1).det = 1
    rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]
    calc
      ((z : ℂ) ^ 2) ^ 3 * y.1.1.1.det = y.1.2.1.det * y.1.1.1.det := by
        rw [show ((z : ℂ)^2)^3 = (z : ℂ)^6 by ring, hz6]
      _ = 1 := by simpa [mul_comm] using hAB
  let g3 : SMGaugeSU3 := ⟨g3u.1, g3u.2, hg3det⟩
  let g2u : SMGaugeU2 := phaseUnitary (Fin 2) ((z⁻¹) ^ 3) * y.1.2
  have hg2det : g2u.1.det = 1 := by
    change ((((z : Circle)⁻¹ : ℂ) ^ 3) • (1 : Matrix (Fin 2) (Fin 2) ℂ) * y.1.2.1).det = 1
    rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]
    rw [show ((((z : Circle)⁻¹ : ℂ) ^ 3) ^ 2) = ((z : ℂ) ^ 6)⁻¹ by simp; ring]
    rw [hz6]
    exact inv_mul_cancel₀ (Matrix.UnitaryGroup.det_isUnit y.1.2).ne_zero
  let g2 : SMGaugeSU2 := ⟨g2u.1, g2u.2, hg2det⟩
  refine ⟨((g3, g2), z), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    simp [smGaugeHom, smGaugeAmbientHom, g3, g3u, phaseUnitaryHom,
      phaseUnitary, specialToUnitary, Matrix.mul_smul, Matrix.smul_mul]
  · apply Subtype.ext
    simp [smGaugeHom, smGaugeAmbientHom, g2, g2u, phaseUnitaryHom,
      phaseUnitary, specialToUnitary, Matrix.mul_smul, Matrix.smul_mul]

/-- The kernel is precisely the displayed central sixth-root subgroup. -/
theorem mem_smGaugeHom_ker_iff_centralZ6 (x : SMGaugeCover) :
    x ∈ smGaugeHom.ker ↔
      x.1.1.1 = (x.2 : ℂ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
      x.1.2.1 = ((x.2 : ℂ)⁻¹) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      (x.2 : ℂ) ^ 6 = 1 := by
  constructor
  · intro hx
    have heq : smGaugeHom x = 1 := hx
    have h3 : ((x.2 : ℂ)⁻¹) ^ 2 • x.1.1.1 = 1 := by
      have h := congrArg (fun q => q.1.1.1) heq
      simpa [smGaugeHom, smGaugeAmbientHom, phaseUnitaryHom, phaseUnitary,
        specialToUnitary] using h
    have h2 : (x.2 : ℂ) ^ 3 • x.1.2.1 = 1 := by
      have h := congrArg (fun q => q.1.2.1) heq
      simpa [smGaugeHom, smGaugeAmbientHom, phaseUnitaryHom, phaseUnitary,
        specialToUnitary] using h
    exact sm_group.2.2.2 x.1.1.1 x.1.2.1 (x.2 : ℂ)
      (Circle.coe_ne_zero x.2)
      (Matrix.mem_specialUnitaryGroup_iff.mp x.1.1.2).2 h3 h2
  · rintro ⟨h3, h2, _⟩
    change smGaugeHom x = 1
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      simp [smGaugeHom, smGaugeAmbientHom, phaseUnitaryHom, phaseUnitary,
        specialToUnitary, h3]
    · apply Subtype.ext
      simp [smGaugeHom, smGaugeAmbientHom, phaseUnitaryHom, phaseUnitary,
        specialToUnitary, h2]

/-- `S(U(3)×U(2)) ≃ (SU(3)×SU(2)×U(1))/ℤ₆`. -/
noncomputable def smGaugeQuotientEquiv :
    SMGaugeCover ⧸ smGaugeHom.ker ≃* SMGaugeGroup :=
  QuotientGroup.quotientKerEquivOfSurjective smGaugeHom smGaugeHom_surjective

end NCG
