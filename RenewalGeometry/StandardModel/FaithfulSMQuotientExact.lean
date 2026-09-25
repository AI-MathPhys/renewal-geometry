/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.SMGaugeQuotientExact

/-!
# Faithful matter realization of the determinant quotient (`prop:faithful-SM-quotient`)

`prop:faithful-SM-quotient` of the spacetime–gauge duality manuscript.  With the abelian charge
normalized by `y = 6Y`, the one-generation left-handed Weyl packet

`Q : (3,2)_1, u^c : (3̄,1)_{-4}, d^c : (3̄,1)_2, L : (1,2)_{-3}, e^c : (1,1)_6, H : (1,2)_3,
[ν^c : (1,1)_0]`

is realized as seven matrix representations (`repQ`, `repUc`, `repDc`, `repL`, `repEc`, `repH`,
`repNuc`) of the cover `G̃ = SU(3) × SU(2) × U(1)_y = SMGaugeCover`.

* `commonKernel_eq_smGaugeHom_ker`: the common kernel of the seven representations is exactly
  the kernel of the determinant quotient map `G̃ → S(U(3) × U(2))`
  (`{(z² I₃, z⁻³ I₂, z) : z⁶ = 1}`, `mem_smGaugeHom_ker_iff_centralZ6`).
* `commonKernel_eq_zpowers`: **the boxed identity** `K = ⟨(e^{2πi/3} I₃, -I₂, e^{iπ/3})⟩`
  (`z6`), and `orderOf_z6` gives `K ≅ ℤ₆`.
* `faithful_quotient`: the joint packet representation has kernel `K`, so the represented
  matter packet is faithful precisely on `G̃ / K` (`QuotientGroup.kerLift` is injective) — the
  same global group `S(U(3) × U(2))` selected by the determinant seed (`smGaugeQuotientEquiv`).
-/

open Matrix Kronecker

namespace RenewalGeometry
namespace FaithfulSMQuotient

/-! ### The seven matter representations -/

/-- The colour factor `g₃` of a cover element, as a matrix. -/
noncomputable def colour : SMGaugeCover →* Matrix (Fin 3) (Fin 3) ℂ :=
  (Matrix.specialUnitaryGroup (Fin 3) ℂ).subtype.comp
    ((MonoidHom.fst SMGaugeSU3 SMGaugeSU2).comp (MonoidHom.fst (SMGaugeSU3 × SMGaugeSU2) Circle))

/-- The weak factor `g₂` of a cover element, as a matrix. -/
noncomputable def weak : SMGaugeCover →* Matrix (Fin 2) (Fin 2) ℂ :=
  (Matrix.specialUnitaryGroup (Fin 2) ℂ).subtype.comp
    ((MonoidHom.snd SMGaugeSU3 SMGaugeSU2).comp (MonoidHom.fst (SMGaugeSU3 × SMGaugeSU2) Circle))

@[simp] theorem colour_apply (x : SMGaugeCover) : colour x = x.1.1.1 := rfl
@[simp] theorem weak_apply (x : SMGaugeCover) : weak x = x.1.2.1 := rfl

/-- The conjugate colour representation `3̄`: entrywise complex conjugation of `g₃`. -/
noncomputable def colourConj : SMGaugeCover →* Matrix (Fin 3) (Fin 3) ℂ :=
  (starRingEnd ℂ).mapMatrix.toMonoidHom.comp colour

@[simp] theorem colourConj_apply (x : SMGaugeCover) :
    colourConj x = x.1.1.1.map (starRingEnd ℂ) := rfl

/-- The bifundamental `(3,2)`: `g₃ ⊗ g₂` on `ℂ³ ⊗ ℂ²`. -/
noncomputable def bifund : SMGaugeCover →* Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ where
  toFun x := colour x ⊗ₖ weak x
  map_one' := by simp
  map_mul' x y := by simp [Matrix.mul_kronecker_mul]

@[simp] theorem bifund_apply (x : SMGaugeCover) : bifund x = x.1.1.1 ⊗ₖ x.1.2.1 := rfl

/-- Twist a representation by the abelian charge `y` (normalized `y = 6Y`): `x ↦ z^y • ρ x`. -/
noncomputable def charged {d : Type} [Fintype d] [DecidableEq d] (y : ℤ)
    (ρ : SMGaugeCover →* Matrix d d ℂ) : SMGaugeCover →* Matrix d d ℂ where
  toFun x := ((x.2 : ℂ) ^ y) • ρ x
  map_one' := by simp
  map_mul' x w := by
    simp only [Prod.snd_mul, Circle.coe_mul, mul_zpow, map_mul]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

@[simp] theorem charged_apply {d : Type} [Fintype d] [DecidableEq d] (y : ℤ)
    (ρ : SMGaugeCover →* Matrix d d ℂ) (x : SMGaugeCover) :
    charged y ρ x = ((x.2 : ℂ) ^ y) • ρ x := rfl

/-- `Q : (3,2)_1`. -/
noncomputable def repQ : SMGaugeCover →* Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  charged 1 bifund
/-- `u^c : (3̄,1)_{-4}`. -/
noncomputable def repUc : SMGaugeCover →* Matrix (Fin 3) (Fin 3) ℂ := charged (-4) colourConj
/-- `d^c : (3̄,1)_2`. -/
noncomputable def repDc : SMGaugeCover →* Matrix (Fin 3) (Fin 3) ℂ := charged 2 colourConj
/-- `L : (1,2)_{-3}`. -/
noncomputable def repL : SMGaugeCover →* Matrix (Fin 2) (Fin 2) ℂ := charged (-3) weak
/-- `e^c : (1,1)_6`. -/
noncomputable def repEc : SMGaugeCover →* Matrix Unit Unit ℂ := charged 6 1
/-- `H : (1,2)_3`. -/
noncomputable def repH : SMGaugeCover →* Matrix (Fin 2) (Fin 2) ℂ := charged 3 weak
/-- The optional neutral singlet `ν^c : (1,1)_0`. -/
noncomputable def repNuc : SMGaugeCover →* Matrix Unit Unit ℂ := charged 0 1

/-- The common kernel `K` of the seven matter representations. -/
noncomputable def commonKernel : Subgroup SMGaugeCover :=
  repQ.ker ⊓ repUc.ker ⊓ repDc.ker ⊓ repL.ker ⊓ repEc.ker ⊓ repH.ker ⊓ repNuc.ker

theorem mem_commonKernel {x : SMGaugeCover} :
    x ∈ commonKernel ↔
      repQ x = 1 ∧ repUc x = 1 ∧ repDc x = 1 ∧ repL x = 1 ∧ repEc x = 1 ∧ repH x = 1 ∧
        repNuc x = 1 := by
  simp only [commonKernel, Subgroup.mem_inf, MonoidHom.mem_ker]
  tauto

/-! ### Scalar bookkeeping -/

theorem star_circle_coe (z : Circle) : star (z : ℂ) = (z : ℂ)⁻¹ := by
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
  rfl

theorem map_star_smul_one {d : Type} [Fintype d] [DecidableEq d] (c : ℂ) :
    ((c • (1 : Matrix d d ℂ)).map (starRingEnd ℂ)) = (star c) • (1 : Matrix d d ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [h]

theorem smul_one_eq_one_iff {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (c : ℂ) :
    c • (1 : Matrix d d ℂ) = 1 ↔ c = 1 := by
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty d›
    have := congrFun (congrFun h i) i
    simpa using this
  · rintro rfl
    simp

/-! ### The common kernel is the determinant-quotient kernel -/

/-- **`prop:faithful-SM-quotient`, kernel identification.**  The common kernel of the seven
matter representations is exactly the kernel `{(z² I₃, z⁻³ I₂, z) : z⁶ = 1}` of the determinant
quotient map `G̃ → S(U(3) × U(2))`. -/
theorem commonKernel_eq_smGaugeHom_ker : commonKernel = smGaugeHom.ker := by
  ext x
  rw [mem_commonKernel, mem_smGaugeHom_ker_iff_centralZ6]
  obtain ⟨⟨g3, g2⟩, z⟩ := x
  simp only [repQ, repUc, repDc, repL, repEc, repH, repNuc, charged_apply, bifund_apply,
    colourConj_apply, weak_apply, MonoidHom.one_apply]
  have hz : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  constructor
  · rintro ⟨-, -, hDc, hL, hEc, -, -⟩
    have hz6 : (z : ℂ) ^ 6 = 1 := by
      have := (smul_one_eq_one_iff (d := Unit) _).mp hEc
      simpa using this
    have hg2 : g2.1 = ((z : ℂ)⁻¹) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      have h1 : g2.1 = ((z : ℂ) ^ (-3 : ℤ))⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [← hL, smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hz), one_smul]
      rw [h1]
      congr 1
      rw [_root_.zpow_neg, inv_inv, inv_pow, zpow_ofNat]
      have h33 : (z : ℂ) ^ 3 * (z : ℂ) ^ 3 = 1 := by
        rw [← pow_add]
        norm_num [hz6]
      exact eq_inv_of_mul_eq_one_left h33
    have hg3 : g3.1 = (z : ℂ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
      have h1 : g3.1.map (starRingEnd ℂ) = ((z : ℂ) ^ (2 : ℤ))⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
        rw [← hDc, smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hz), one_smul]
      have h3 : (g3.1.map (starRingEnd ℂ)).map (starRingEnd ℂ) = g3.1 := by
        ext i j
        simp
      rw [h1, map_star_smul_one] at h3
      rw [← h3]
      congr 1
      rw [zpow_ofNat, star_inv₀, star_pow, star_circle_coe, inv_pow, inv_inv]
    exact ⟨hg3, hg2, hz6⟩
  · rintro ⟨hg3, hg2, hz6⟩
    have hstar : star (z : ℂ) = (z : ℂ)⁻¹ := star_circle_coe z
    rw [hg3, hg2]
    simp only [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one,
      map_star_smul_one, smul_smul, star_pow, hstar, _root_.zpow_neg, zpow_ofNat, pow_zero, pow_one, inv_pow]
    have hz3 : (z : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ hz
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [smul_one_eq_one_iff, show (z : ℂ) * (((z : ℂ) ^ 3)⁻¹ * (z : ℂ) ^ 2)
        = (z : ℂ) ^ 3 * ((z : ℂ) ^ 3)⁻¹ by ring]
      exact mul_inv_cancel₀ hz3
    · rw [smul_one_eq_one_iff, ← mul_inv, ← pow_add]
      norm_num [hz6]
    · rw [smul_one_eq_one_iff]
      exact mul_inv_cancel₀ (pow_ne_zero _ hz)
    · rw [smul_one_eq_one_iff, ← mul_inv, ← pow_add]
      norm_num [hz6]
    · rw [smul_one_eq_one_iff]
      exact hz6
    · rw [smul_one_eq_one_iff]
      exact mul_inv_cancel₀ hz3
    · simp

/-! ### The explicit ℤ₆ generator -/

/-- The primitive sixth root `e^{iπ/3}` on the circle. -/
noncomputable def zeta6 : Circle := Circle.exp (Real.pi / 3)

theorem zeta6_coe : (zeta6 : ℂ) = Complex.exp (2 * Real.pi * Complex.I / 6) := by
  rw [zeta6, Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem isPrimitiveRoot_zeta6 : IsPrimitiveRoot (zeta6 : ℂ) 6 := by
  rw [zeta6_coe]
  exact_mod_cast Complex.isPrimitiveRoot_exp 6 (by norm_num)

theorem zeta6_pow_six : (zeta6 : ℂ) ^ 6 = 1 := isPrimitiveRoot_zeta6.pow_eq_one

/-- `e^{2πi/3} I₃ ∈ SU(3)`. -/
theorem colourGen_mem :
    (zeta6 : ℂ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    have hz : star (zeta6 : ℂ) * (zeta6 : ℂ) = 1 := by
      rw [star_circle_coe]
      exact inv_mul_cancel₀ (Circle.coe_ne_zero _)
    have hz2 : star ((zeta6 : ℂ) ^ 2) * (zeta6 : ℂ) ^ 2 = 1 := by
      rw [star_pow, ← mul_pow, hz, one_pow]
    simpa using sm_group.2.1 ((zeta6 : ℂ) ^ 2) (1 : Matrix (Fin 3) (Fin 3) ℂ) hz2
  · rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, ← pow_mul]
    exact zeta6_pow_six

/-- `-I₂ = e^{-iπ} I₂ ∈ SU(2)`. -/
theorem weakGen_mem :
    ((zeta6 : ℂ)⁻¹) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    have hz : star ((zeta6 : ℂ)⁻¹) * (zeta6 : ℂ)⁻¹ = 1 := by
      rw [star_inv₀, star_circle_coe, inv_inv]
      exact mul_inv_cancel₀ (Circle.coe_ne_zero _)
    have hz3 : star (((zeta6 : ℂ)⁻¹) ^ 3) * ((zeta6 : ℂ)⁻¹) ^ 3 = 1 := by
      rw [star_pow, ← mul_pow, hz, one_pow]
    simpa using sm_group.2.1 (((zeta6 : ℂ)⁻¹) ^ 3) (1 : Matrix (Fin 2) (Fin 2) ℂ) hz3
  · rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, ← pow_mul, inv_pow]
    rw [show 3 * 2 = 6 by norm_num, zeta6_pow_six, inv_one]

/-- The generator `z₆ = (e^{2πi/3} I₃, -I₂, e^{iπ/3})` of `eq:faithful-SM-kernel`. -/
noncomputable def z6 : SMGaugeCover :=
  ((⟨(zeta6 : ℂ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ), colourGen_mem⟩,
    ⟨((zeta6 : ℂ)⁻¹) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ), weakGen_mem⟩), zeta6)

/-- The displayed entries of the generator: `e^{2πi/3} I₃`, `-I₂`, `e^{iπ/3}`. -/
theorem z6_entries :
    (z6.1.1 : Matrix (Fin 3) (Fin 3) ℂ) = Complex.exp (2 * Real.pi * Complex.I / 3) • 1 ∧
    (z6.1.2 : Matrix (Fin 2) (Fin 2) ℂ) = -1 ∧
    (z6.2 : ℂ) = Complex.exp (Real.pi / 3 * Complex.I) := by
  refine ⟨?_, ?_, ?_⟩
  · change (zeta6 : ℂ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) = _
    congr 1
    rw [zeta6_coe, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · change ((zeta6 : ℂ)⁻¹) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ) = -1
    have h : ((zeta6 : ℂ)⁻¹) ^ 3 = -1 := by
      rw [inv_pow, zeta6_coe, ← Complex.exp_nat_mul]
      rw [show ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 6) = Real.pi * Complex.I by
        push_cast; ring, Complex.exp_pi_mul_I]
      norm_num
    rw [h]
    simp
  · change (Circle.exp (Real.pi / 3) : ℂ) = _
    rw [Circle.coe_exp]
    push_cast
    ring_nf

theorem z6_mem_smGaugeHom_ker : z6 ∈ smGaugeHom.ker := by
  rw [mem_smGaugeHom_ker_iff_centralZ6]
  exact ⟨rfl, rfl, zeta6_pow_six⟩

/-- **`prop:faithful-SM-quotient`, boxed identity `eq:faithful-SM-kernel`.**
`K = ⟨(e^{2πi/3} I₃, -I₂, e^{iπ/3})⟩`. -/
theorem commonKernel_eq_zpowers : commonKernel = Subgroup.zpowers z6 := by
  rw [commonKernel_eq_smGaugeHom_ker]
  apply le_antisymm
  · intro x hx
    rw [mem_smGaugeHom_ker_iff_centralZ6] at hx
    obtain ⟨hg3, hg2, hz6⟩ := hx
    obtain ⟨i, -, hi⟩ := isPrimitiveRoot_zeta6.eq_pow_of_pow_eq_one hz6
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(i : ℤ), ?_⟩
    rw [zpow_natCast]
    obtain ⟨⟨g3, g2⟩, z⟩ := x
    simp only at hg3 hg2 hi
    have hz : z = zeta6 ^ i := by
      ext
      rw [Circle.coe_pow, hi]
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · apply Subtype.ext
      rw [Prod.pow_fst, Prod.pow_fst, SubmonoidClass.coe_pow]
      change ((zeta6 : ℂ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ)) ^ i = g3.1
      rw [smul_pow, one_pow, hg3, ← hi]
      congr 1
      ring
    · apply Subtype.ext
      rw [Prod.pow_fst, Prod.pow_snd, SubmonoidClass.coe_pow]
      change (((zeta6 : ℂ)⁻¹) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ^ i = g2.1
      rw [smul_pow, one_pow, hg2, ← hi]
      congr 1
      ring
    · rw [Prod.pow_snd]
      exact hz.symm
  · exact Subgroup.zpowers_le.mpr z6_mem_smGaugeHom_ker

theorem z6_pow_six : z6 ^ 6 = 1 := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · apply Subtype.ext
    rw [Prod.pow_fst, Prod.pow_fst, SubmonoidClass.coe_pow]
    change ((zeta6 : ℂ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ)) ^ 6 = 1
    rw [smul_pow, one_pow, ← pow_mul, show 2 * 6 = 6 * 2 by norm_num, pow_mul, zeta6_pow_six]
    simp
  · apply Subtype.ext
    rw [Prod.pow_fst, Prod.pow_snd, SubmonoidClass.coe_pow]
    change (((zeta6 : ℂ)⁻¹) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ^ 6 = 1
    rw [smul_pow, one_pow, ← pow_mul, inv_pow, show 3 * 6 = 6 * 3 by norm_num, pow_mul,
      zeta6_pow_six]
    simp
  · rw [Prod.pow_snd]
    ext
    rw [Circle.coe_pow]
    exact zeta6_pow_six

/-- `K ≅ ℤ₆`: the generator has order exactly six. -/
theorem orderOf_z6 : orderOf z6 = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨z6_pow_six, fun m hm hm0 hpow => ?_⟩
  have hsnd := congrArg (fun x : SMGaugeCover => (x.2 : ℂ)) hpow
  simp only [Prod.pow_snd, Circle.coe_pow] at hsnd
  exact isPrimitiveRoot_zeta6.pow_ne_one_of_pos_of_lt hm0.ne' hm hsnd

/-! ### Faithfulness precisely on the quotient -/

/-- The joint packet representation `Q ⊕ u^c ⊕ d^c ⊕ L ⊕ e^c ⊕ H ⊕ ν^c`. -/
noncomputable def jointRep :=
  repQ.prod (repUc.prod (repDc.prod (repL.prod (repEc.prod (repH.prod repNuc)))))

theorem jointRep_ker : jointRep.ker = commonKernel := by
  simp only [jointRep, MonoidHom.ker_prod, commonKernel]
  ac_rfl

/-- **`prop:faithful-SM-quotient`, faithfulness.**  The represented matter packet has kernel
exactly `K = ⟨z₆⟩ = ker (G̃ → S(U(3) × U(2)))`, hence it is faithful precisely on `G̃ / K`: the
descended representation of the quotient is injective. -/
theorem faithful_quotient :
    jointRep.ker = Subgroup.zpowers z6 ∧
    jointRep.ker = smGaugeHom.ker ∧
    jointRep.toHomUnits.ker = jointRep.ker ∧
    Function.Injective (QuotientGroup.kerLift jointRep.toHomUnits) :=
  ⟨jointRep_ker.trans commonKernel_eq_zpowers, jointRep_ker.trans commonKernel_eq_smGaugeHom_ker,
    MonoidHom.ker_toHomUnits jointRep, QuotientGroup.kerLift_injective jointRep.toHomUnits⟩

end FaithfulSMQuotient
end RenewalGeometry
