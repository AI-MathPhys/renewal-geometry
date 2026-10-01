/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.FaithfulSMQuotientExact

/-!
# Descent and covariant Yukawa blocks (`lem:SM-descent`)

Einstein–SM action closure, `lem:SM-descent` (with `tab:SM-representations`,
`eq:explicit-Yukawa-blocks`, `eq:yukawa-bound`).  Namespace `RenewalGeometry.SMDescentYukawa`.

* **Descent** (`sm_descent`).  The rows `Q_L : (3,2)_{1/6}`, `u_R : (3,1)_{2/3}`,
  `d_R : (3,1)_{-1/3}`, `L_L : (1,2)_{-1/2}`, `e_R : (1,1)_{-1}`, `ν_R : (1,1)_0`,
  `H : (1,2)_{1/2}` are given on `G_SM = S(U(3) × U(2))` explicitly (`U₃ ⊗ U₂`,
  `det U₂ · U₃`, `U₃`, `(det U₂)⁻¹ U₂`, `(det U₂)⁻¹`, `1`, `U₂`), and each one composed with the
  covering map `(g₃, g₂, z) ↦ (z⁻² g₃, z³ g₂)` is the cover representation with colour/weak
  factor and `U(1)` weight `6Y` (`FaithfulSMQuotient.charged`).  Hence the central `ℤ₆`
  generator `(e^{2πi/3} I₃, -I₂, e^{iπ/3})` acts trivially on every row.
* **Conjugate doublet** (`higgsConj_mulVec`): `iσ₂ \overline{U H} = \overline{det U}\, U\, iσ₂ H̄`
  for `U ∈ U(2)`.
* **Yukawa blocks** (`leftBlock`, `yukawaMin`, `neutralBlock`, `majoranaBlock`, `yukawaExt`) on
  the carrier `(Q_L ⊕ L_L) ⊕ (u_R ⊕ d_R ⊕ e_R) [⊕ (ν_R ⊕ ν_R^c)]` with generation factor `ℂ³`;
  covariance `yukawaMin_covariant`, `yukawaExt_covariant`, invariance of `Ψ†𝓜Ψ`
  (`bilinear_invariant`).
* **Affinity and bounds** (`yukawaExt_affine`, `yukawa_bound`).
* `sm_descent_yukawa` assembles the lemma.

Rendering: the bound `eq:yukawa-bound` is stated entrywise (all finite-dimensional norms are
equivalent, so this is the statement up to a dimension constant); `|H|` is the sup norm on
`ℂ²`; the Higgs derivative of the affine map is its linear part `L_𝐘`.  The Majorana block is
the Hermitian assembly of the constant symmetric `M_R` between `ν_R` and its charge
conjugate on the doubled carrier.
-/

open Matrix Kronecker

namespace RenewalGeometry

namespace SMDescentYukawa

noncomputable section

/-! ### The colour and weak factors of `G_SM = S(U(3) × U(2))` -/

/-- `(U₃, U₂) ↦ U₃`. -/
def smU3 : SMGaugeGroup →* Matrix (Fin 3) (Fin 3) ℂ :=
  (Matrix.unitaryGroup (Fin 3) ℂ).subtype.comp
    ((MonoidHom.fst SMGaugeU3 SMGaugeU2).comp determinantProductHom.ker.subtype)

/-- `(U₃, U₂) ↦ U₂`. -/
def smU2 : SMGaugeGroup →* Matrix (Fin 2) (Fin 2) ℂ :=
  (Matrix.unitaryGroup (Fin 2) ℂ).subtype.comp
    ((MonoidHom.snd SMGaugeU3 SMGaugeU2).comp determinantProductHom.ker.subtype)

@[simp] theorem smU3_apply (y : SMGaugeGroup) :
    smU3 y = ((y : SMGaugeU3 × SMGaugeU2).1 : Matrix (Fin 3) (Fin 3) ℂ) := rfl
@[simp] theorem smU2_apply (y : SMGaugeGroup) :
    smU2 y = ((y : SMGaugeU3 × SMGaugeU2).2 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- The determinant character `χ(U₃, U₂) = det U₂`. -/
def smChi : SMGaugeGroup →* ℂ := Matrix.detMonoidHom.comp smU2

@[simp] theorem smChi_apply (y : SMGaugeGroup) : smChi y = (smU2 y).det := rfl

/-- Twist a representation of `G_SM` by an integer power of the determinant character. -/
def detTwist {d : Type} [Fintype d] [DecidableEq d] (k : ℤ)
    (ρ : SMGaugeGroup →* Matrix d d ℂ) : SMGaugeGroup →* Matrix d d ℂ where
  toFun y := (smChi y ^ k) • ρ y
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_zpow]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

@[simp] theorem detTwist_apply {d : Type} [Fintype d] [DecidableEq d] (k : ℤ)
    (ρ : SMGaugeGroup →* Matrix d d ℂ) (y : SMGaugeGroup) :
    detTwist k ρ y = (smChi y ^ k) • ρ y := rfl

/-- `(3, 2)` on `G_SM`: `U₃ ⊗ U₂`. -/
def smBifund : SMGaugeGroup →* Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ where
  toFun y := smU3 y ⊗ₖ smU2 y
  map_one' := by simp
  map_mul' x y := by simp [Matrix.mul_kronecker_mul]

@[simp] theorem smBifund_apply (y : SMGaugeGroup) : smBifund y = smU3 y ⊗ₖ smU2 y := rfl

/-! ### The representation packet of `tab:SM-representations` on `G_SM` -/

/-- `Q_L : (3, 2)_{1/6}`. -/
def repQL := smBifund
/-- `u_R : (3, 1)_{2/3}`: `det U₂ · U₃`. -/
def repUR := detTwist 1 smU3
/-- `d_R : (3, 1)_{-1/3}`: `U₃`. -/
def repDR := smU3
/-- `L_L : (1, 2)_{-1/2}`: `(det U₂)⁻¹ · U₂`. -/
def repLL := detTwist (-1) smU2
/-- `e_R : (1, 1)_{-1}`: `(det U₂)⁻¹`. -/
def repER := detTwist (-1) (1 : SMGaugeGroup →* Matrix Unit Unit ℂ)
/-- `ν_R : (1, 1)_0` (optional). -/
def repNR : SMGaugeGroup →* Matrix Unit Unit ℂ := 1
/-- `H : (1, 2)_{1/2}`: `U₂`. -/
def repH := smU2

open FaithfulSMQuotient in
/-- The cover image `(g₃, g₂, z) ↦ (z⁻² g₃, z³ g₂)` evaluated on the two factors. -/
theorem smGaugeHom_factors (x : SMGaugeCover) :
    smU3 (smGaugeHom x) = ((x.2 : ℂ)⁻¹ ^ 2) • x.1.1.1 ∧
      smU2 (smGaugeHom x) = ((x.2 : ℂ) ^ 3) • x.1.2.1 := by
  constructor
  · simp [smGaugeHom, smGaugeAmbientHom, phaseUnitaryHom, phaseUnitary, specialToUnitary]
  · simp [smGaugeHom, smGaugeAmbientHom, phaseUnitaryHom, phaseUnitary, specialToUnitary]

theorem smChi_smGaugeHom (x : SMGaugeCover) : smChi (smGaugeHom x) = (x.2 : ℂ) ^ 6 := by
  rw [smChi_apply, (smGaugeHom_factors x).2, Matrix.det_smul, Fintype.card_fin,
    (Matrix.mem_specialUnitaryGroup_iff.mp x.1.2.2).2]
  ring

/-! ### Descent: each row of `tab:SM-representations` is pulled back from `G_SM` -/

section Descent

open FaithfulSMQuotient

/-- The cover representation of a row with colour/weak factor `ρ` and integer weight
`6Y = y` of the covering `U(1)` factor. -/
abbrev coverRow {d : Type} [Fintype d] [DecidableEq d] (y : ℤ)
    (ρ : SMGaugeCover →* Matrix d d ℂ) : SMGaugeCover →* Matrix d d ℂ :=
  charged y ρ

theorem descent_QL : repQL.comp smGaugeHom = coverRow 1 bifund := by
  ext1 x
  obtain ⟨h3, h2⟩ := smGaugeHom_factors x
  have hz : (x.2 : ℂ) ≠ 0 := Circle.coe_ne_zero x.2
  simp only [MonoidHom.comp_apply, repQL, smBifund_apply, h3, h2, charged_apply, bifund_apply,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, zpow_one]
  congr 1
  field_simp

theorem descent_UR : repUR.comp smGaugeHom = coverRow 4 colour := by
  ext1 x
  have h3 := (smGaugeHom_factors x).1
  have hz : (x.2 : ℂ) ≠ 0 := Circle.coe_ne_zero x.2
  simp only [MonoidHom.comp_apply, repUR, detTwist_apply, smChi_smGaugeHom, h3, charged_apply,
    colour_apply, smul_smul, zpow_one]
  congr 1
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]
  field_simp

theorem descent_DR : repDR.comp smGaugeHom = coverRow (-2) colour := by
  ext1 x
  have h3 := (smGaugeHom_factors x).1
  simp only [MonoidHom.comp_apply, repDR, h3, charged_apply, colour_apply]
  congr 1
  rw [_root_.zpow_neg, inv_pow, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]

theorem descent_LL : repLL.comp smGaugeHom = coverRow (-3) weak := by
  ext1 x
  have h2 := (smGaugeHom_factors x).2
  have hz : (x.2 : ℂ) ≠ 0 := Circle.coe_ne_zero x.2
  simp only [MonoidHom.comp_apply, repLL, detTwist_apply, smChi_smGaugeHom, h2, charged_apply,
    weak_apply, smul_smul]
  congr 1
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_one, show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl,
    zpow_natCast]
  field_simp

theorem descent_ER :
    repER.comp smGaugeHom = coverRow (-6) (1 : SMGaugeCover →* Matrix Unit Unit ℂ) := by
  ext1 x
  simp only [MonoidHom.comp_apply, repER, detTwist_apply, smChi_smGaugeHom, charged_apply,
    MonoidHom.one_apply]
  congr 1
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_one, show (6 : ℤ) = ((6 : ℕ) : ℤ) by rfl,
    zpow_natCast]

theorem descent_NR :
    repNR.comp smGaugeHom = coverRow 0 (1 : SMGaugeCover →* Matrix Unit Unit ℂ) := by
  ext1 x
  simp [repNR]

theorem descent_H : repH.comp smGaugeHom = coverRow 3 weak := by
  ext1 x
  have h2 := (smGaugeHom_factors x).2
  simp only [MonoidHom.comp_apply, repH, h2, charged_apply, weak_apply]
  congr 1

/-- **`lem:SM-descent`, descent clause.**  Every row of `tab:SM-representations`
(`Q_L, u_R, d_R, L_L, e_R`, the optional `ν_R`, and `H`), realised on the cover
`SU(3) × SU(2) × U(1)` with colour/weak factor and `U(1)` weight `6Y`, factors through the
covering homomorphism `(g₃, g₂, z) ↦ (z⁻² g₃, z³ g₂)` onto `G_SM = S(U(3) × U(2))`: it is the
pull-back of an explicit representation of `G_SM`.  In particular the central `ℤ₆` kernel,
generated by `(e^{2πi/3} I₃, -I₂, e^{iπ/3})`, acts trivially on every row. -/
theorem sm_descent :
    repQL.comp smGaugeHom = coverRow 1 bifund ∧
    repUR.comp smGaugeHom = coverRow 4 colour ∧
    repDR.comp smGaugeHom = coverRow (-2) colour ∧
    repLL.comp smGaugeHom = coverRow (-3) weak ∧
    repER.comp smGaugeHom = coverRow (-6) (1 : SMGaugeCover →* Matrix Unit Unit ℂ) ∧
    repNR.comp smGaugeHom = coverRow 0 (1 : SMGaugeCover →* Matrix Unit Unit ℂ) ∧
    repH.comp smGaugeHom = coverRow 3 weak ∧
    (coverRow 1 bifund z6 = 1 ∧ coverRow 4 colour z6 = 1 ∧ coverRow (-2) colour z6 = 1 ∧
      coverRow (-3) weak z6 = 1 ∧ coverRow (-6) (1 : SMGaugeCover →* Matrix Unit Unit ℂ) z6 = 1 ∧
      coverRow 0 (1 : SMGaugeCover →* Matrix Unit Unit ℂ) z6 = 1 ∧ coverRow 3 weak z6 = 1) := by
  have hk : smGaugeHom z6 = 1 := z6_mem_smGaugeHom_ker
  refine ⟨descent_QL, descent_UR, descent_DR, descent_LL, descent_ER, descent_NR, descent_H,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← descent_QL, MonoidHom.comp_apply, hk, map_one]
  · rw [← descent_UR, MonoidHom.comp_apply, hk, map_one]
  · rw [← descent_DR, MonoidHom.comp_apply, hk, map_one]
  · rw [← descent_LL, MonoidHom.comp_apply, hk, map_one]
  · rw [← descent_ER, MonoidHom.comp_apply, hk, map_one]
  · rw [← descent_NR, MonoidHom.comp_apply, hk, map_one]
  · rw [← descent_H, MonoidHom.comp_apply, hk, map_one]

end Descent

/-! ### The conjugate doublet `H̃ = iσ₂ H̄` -/

/-- `H̃ = iσ₂ H̄`, with `iσ₂ = [[0, 1], [-1, 0]]`. -/
def higgsConj (H : Fin 2 → ℂ) : Fin 2 → ℂ := ![star (H 1), -star (H 0)]

theorem star_det_of_unitary {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : star U.det * U.det = 1 := by
  have := Matrix.det_of_mem_unitary hU
  exact (Unitary.mem_iff.mp this).1

/-- For `U ∈ U(2)`, `iσ₂ \overline{U H} = \overline{det U} · U (iσ₂ H̄)`: the conjugate doublet
transforms in the doublet with the opposite determinant charge. -/
theorem higgsConj_mulVec {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (H : Fin 2 → ℂ) :
    higgsConj (U *ᵥ H) = star U.det • (U *ᵥ higgsConj H) := by
  have h1 : star U * U = 1 := (Unitary.mem_iff.mp hU).1
  have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv h1
  have hdet := star_det_of_unitary hU
  have hd0 : U.det ≠ 0 := by
    intro h; rw [h, mul_zero] at hdet; exact zero_ne_one hdet
  have hsd : star U.det = U.det⁻¹ := eq_inv_of_mul_eq_one_left hdet
  have hstar : star U = U.det⁻¹ • adjugate U := by
    rw [← hinv, Matrix.inv_def, Ring.inverse_eq_inv']
  have e : ∀ i j, star (U j i) = U.det⁻¹ * adjugate U i j := by
    intro i j
    have := congrFun (congrFun hstar i) j
    simpa using this
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
  rw [hsd]
  ext k
  fin_cases k <;>
    simp [higgsConj, Matrix.mulVec, dotProduct, Fin.sum_univ_two, star_add, star_mul,
      e00, e01, e10, e11] <;> ring

/-! ### Colour–weak contraction blocks -/

/-- `Q̄_L H̃ u_R` contraction: `δ_{ab} H̃_i`. -/
def tQu (H : Fin 2 → ℂ) : Matrix (Fin 3 × Fin 2) (Fin 3) ℂ :=
  fun p b => if p.1 = b then higgsConj H p.2 else 0

/-- `Q̄_L H d_R` contraction: `δ_{ab} H_i`. -/
def tQd (H : Fin 2 → ℂ) : Matrix (Fin 3 × Fin 2) (Fin 3) ℂ :=
  fun p b => if p.1 = b then H p.2 else 0

/-- `L̄_L H e_R` contraction: `H_i`. -/
def tLe (H : Fin 2 → ℂ) : Matrix (Fin 2) Unit ℂ := fun i _ => H i

/-- `L̄_L H̃ ν_R` contraction: `H̃_i`. -/
def tLn (H : Fin 2 → ℂ) : Matrix (Fin 2) Unit ℂ := fun i _ => higgsConj H i

section Intertwining

variable {U3 : Matrix (Fin 3) (Fin 3) ℂ} {U2 : Matrix (Fin 2) (Fin 2) ℂ}

theorem tQu_intertwine (hU2 : U2 ∈ Matrix.unitaryGroup (Fin 2) ℂ) (H : Fin 2 → ℂ) :
    (U3 ⊗ₖ U2) * tQu H = tQu (U2 *ᵥ H) * (U2.det • U3) := by
  have hdet := star_det_of_unitary hU2
  ext ⟨a, i⟩ b
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, tQu,
    higgsConj_mulVec hU2, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.smul_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination (-(U3 a b * U2 i k * higgsConj H k)) * hdet

theorem tQd_intertwine (H : Fin 2 → ℂ) :
    (U3 ⊗ₖ U2) * tQd H = tQd (U2 *ᵥ H) * U3 := by
  ext ⟨a, i⟩ b
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, tQd,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem tLe_intertwine (H : Fin 2 → ℂ) :
    ((U2.det ^ (-1 : ℤ)) • U2) * tLe H =
      tLe (U2 *ᵥ H) * ((U2.det ^ (-1 : ℤ)) • (1 : Matrix Unit Unit ℂ)) := by
  ext i j
  fin_cases i <;> simp [Matrix.mul_apply, tLe, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

theorem tLn_intertwine (hU2 : U2 ∈ Matrix.unitaryGroup (Fin 2) ℂ) (H : Fin 2 → ℂ) :
    ((U2.det ^ (-1 : ℤ)) • U2) * tLn H = tLn (U2 *ᵥ H) := by
  have hdet := star_det_of_unitary hU2
  have hd0 : U2.det ≠ 0 := by
    intro h; rw [h, mul_zero] at hdet; exact zero_ne_one hdet
  have hsd : star U2.det = U2.det⁻¹ := eq_inv_of_mul_eq_one_left hdet
  ext i j
  have hT : tLn (U2 *ᵥ H) i j = (star U2.det • (U2 *ᵥ higgsConj H)) i := by
    simp only [tLn, higgsConj_mulVec hU2]
  rw [hT, hsd]
  fin_cases i <;> simp [Matrix.mul_apply, tLn, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

end Intertwining

/-! ### Unitarity helpers -/

section Unitarity

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem fromBlocks_diag_mem_unitary {A : Matrix m m ℂ} {D : Matrix n n ℂ}
    (hA : A ∈ unitary (Matrix m m ℂ)) (hD : D ∈ unitary (Matrix n n ℂ)) :
    fromBlocks A 0 0 D ∈ unitary (Matrix (m ⊕ n) (m ⊕ n) ℂ) := by
  rw [Unitary.mem_iff] at hA hD ⊢
  simp only [Matrix.star_eq_conjTranspose] at hA hD ⊢
  rw [fromBlocks_conjTranspose]
  simp only [conjTranspose_zero]
  constructor
  · rw [fromBlocks_multiply]; simp [hA.1, hD.1]
  · rw [fromBlocks_multiply]; simp [hA.2, hD.2]

theorem smul_mem_unitary {d : ℂ} (hd : star d * d = 1) (k : ℤ) {U : Matrix m m ℂ}
    (hU : U ∈ unitary (Matrix m m ℂ)) : (d ^ k) • U ∈ unitary (Matrix m m ℂ) := by
  have hk : star (d ^ k) * d ^ k = 1 := by
    rw [star_zpow₀, ← mul_zpow, hd, _root_.one_zpow]
  rw [Unitary.mem_iff] at hU ⊢
  refine ⟨?_, ?_⟩
  · rw [star_smul, smul_mul_smul_comm, hk, one_smul, hU.1]
  · rw [star_smul, smul_mul_smul_comm, mul_comm, hk, one_smul, hU.2]

/-- The block-Hermitian assembly `[[0, A], [Aᴴ, 0]]` (the block plus its Hermitian
conjugate). -/
def hermBlock (A : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 A Aᴴ 0

/-- An intertwining `ρ_L A = A' ρ_R` of unitaries lifts to the Hermitian assembly. -/
theorem hermBlock_intertwine {ρL : Matrix m m ℂ} {ρR : Matrix n n ℂ}
    (hL : ρL ∈ unitary (Matrix m m ℂ)) (hR : ρR ∈ unitary (Matrix n n ℂ))
    {A A' : Matrix m n ℂ} (h : ρL * A = A' * ρR) :
    fromBlocks ρL 0 0 ρR * hermBlock A = hermBlock A' * fromBlocks ρL 0 0 ρR := by
  rw [Unitary.mem_iff] at hL hR
  simp only [Matrix.star_eq_conjTranspose] at hL hR
  have hc : Aᴴ * ρLᴴ = ρRᴴ * A'ᴴ := by
    rw [← conjTranspose_mul, h, conjTranspose_mul]
  have h2 : ρR * Aᴴ = A'ᴴ * ρL := by
    calc ρR * Aᴴ = ρR * (Aᴴ * (ρLᴴ * ρL)) := by rw [hL.1, Matrix.mul_one]
      _ = ρR * (ρRᴴ * A'ᴴ * ρL) := by rw [← Matrix.mul_assoc Aᴴ, hc]
      _ = (ρR * ρRᴴ) * A'ᴴ * ρL := by simp only [Matrix.mul_assoc]
      _ = A'ᴴ * ρL := by rw [hR.2, Matrix.one_mul]
  unfold hermBlock
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp [h, h2]

/-- Generation spectator: an intertwining lifts through `⊗ₖ` with a generation matrix. -/
theorem kron_intertwine {r : Type*} [DecidableEq r] [Fintype r]
    {A : Matrix m m ℂ} {T T' : Matrix m n ℂ} {B : Matrix n n ℂ} (h : A * T = T' * B)
    (Y : Matrix r r ℂ) :
    (A ⊗ₖ (1 : Matrix r r ℂ)) * (T ⊗ₖ Y) = (T' ⊗ₖ Y) * (B ⊗ₖ (1 : Matrix r r ℂ)) := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, h, Matrix.one_mul, Matrix.mul_one]

end Unitarity

/-! ### The one-generation-times-three carrier and the Yukawa map -/

/-- The generation factor `ℂ³`. -/
abbrev Gen := Fin 3
abbrev QIdx := (Fin 3 × Fin 2) × Gen
abbrev LIdx := Fin 2 × Gen
abbrev UIdx := Fin 3 × Gen
abbrev DIdx := Fin 3 × Gen
abbrev EIdx := Unit × Gen
abbrev NIdx := Unit × Gen
/-- Left-handed carrier `Q_L ⊕ L_L`. -/
abbrev LeftIdx := QIdx ⊕ LIdx
/-- Right-handed carrier of the minimal packet `(u_R ⊕ d_R) ⊕ e_R`. -/
abbrev RightIdx := (UIdx ⊕ DIdx) ⊕ EIdx
/-- The minimal fermion carrier. -/
abbrev MinIdx := LeftIdx ⊕ RightIdx
/-- The neutral extension `ν_R ⊕ ν_R^c` (charge-conjugate doubled carrier). -/
abbrev NeutralIdx := NIdx ⊕ NIdx
/-- The extended fermion carrier. -/
abbrev ExtIdx := MinIdx ⊕ NeutralIdx

instance : DecidableEq LeftIdx := inferInstanceAs (DecidableEq (QIdx ⊕ LIdx))
instance : DecidableEq RightIdx := inferInstanceAs (DecidableEq ((UIdx ⊕ DIdx) ⊕ EIdx))
instance : DecidableEq MinIdx := inferInstanceAs (DecidableEq (LeftIdx ⊕ RightIdx))
instance : DecidableEq NeutralIdx := inferInstanceAs (DecidableEq (NIdx ⊕ NIdx))
instance : DecidableEq ExtIdx := inferInstanceAs (DecidableEq (MinIdx ⊕ NeutralIdx))
instance : Fintype ExtIdx := inferInstanceAs (Fintype (MinIdx ⊕ NeutralIdx))

/-- A Yukawa coefficient bank: generation matrices `Y_u, Y_d, Y_e, Y_ν ∈ M₃(ℂ)` and a
constant symmetric Majorana matrix `M_R`. -/
structure YukawaBank where
  Yu : Matrix Gen Gen ℂ
  Yd : Matrix Gen Gen ℂ
  Ye : Matrix Gen Gen ℂ
  Yn : Matrix Gen Gen ℂ
  MR : Matrix Gen Gen ℂ
  MR_symm : MRᵀ = MR

/-- The left–right block of `eq:explicit-Yukawa-blocks`:
`Q̄_L H̃ Y_u u_R + Q̄_L H Y_d d_R + L̄_L H Y_e e_R`. -/
def leftBlock (Y : YukawaBank) (H : Fin 2 → ℂ) : Matrix LeftIdx RightIdx ℂ :=
  fromBlocks (fromCols (tQu H ⊗ₖ Y.Yu) (tQd H ⊗ₖ Y.Yd)) 0 0 (tLe H ⊗ₖ Y.Ye)

/-- The minimal-packet mass map `𝓜_𝐘(H)`: the blocks plus Hermitian conjugates. -/
def yukawaMin (Y : YukawaBank) (H : Fin 2 → ℂ) : Matrix MinIdx MinIdx ℂ :=
  hermBlock (leftBlock Y H)

/-- The neutral coupling `L̄_L H̃ Y_ν ν_R`. -/
def neutralBlock (Y : YukawaBank) (H : Fin 2 → ℂ) : Matrix MinIdx NeutralIdx ℂ :=
  fromBlocks (fromRows (0 : Matrix QIdx NIdx ℂ) (tLn H ⊗ₖ Y.Yn)) 0 0 0

/-- The constant Majorana block on `ν_R ⊕ ν_R^c`. -/
def majoranaBlock (Y : YukawaBank) : Matrix NeutralIdx NeutralIdx ℂ :=
  hermBlock ((1 : Matrix Unit Unit ℂ) ⊗ₖ Y.MR)

/-- The neutral-extension mass map `𝓜_𝐘(H)` on the extended carrier. -/
def yukawaExt (Y : YukawaBank) (H : Fin 2 → ℂ) : Matrix ExtIdx ExtIdx ℂ :=
  fromBlocks (yukawaMin Y H) (neutralBlock Y H) (neutralBlock Y H)ᴴ (majoranaBlock Y)

/-! ### The fermion representation and covariance -/

/-- `G_SM` on the left-handed carrier: `(Q_L ⊕ L_L) ⊗ ℂ³_gen`. -/
def rhoLeft (y : SMGaugeGroup) : Matrix LeftIdx LeftIdx ℂ :=
  fromBlocks (repQL y ⊗ₖ (1 : Matrix Gen Gen ℂ)) 0 0 (repLL y ⊗ₖ (1 : Matrix Gen Gen ℂ))

/-- `G_SM` on the right-handed minimal carrier `(u_R ⊕ d_R ⊕ e_R) ⊗ ℂ³_gen`. -/
def rhoRight (y : SMGaugeGroup) : Matrix RightIdx RightIdx ℂ :=
  fromBlocks (fromBlocks (repUR y ⊗ₖ (1 : Matrix Gen Gen ℂ)) 0 0
    (repDR y ⊗ₖ (1 : Matrix Gen Gen ℂ))) 0 0 (repER y ⊗ₖ (1 : Matrix Gen Gen ℂ))

/-- `G_SM` on the minimal carrier. -/
def rhoMin (y : SMGaugeGroup) : Matrix MinIdx MinIdx ℂ := fromBlocks (rhoLeft y) 0 0 (rhoRight y)

/-- `G_SM` on the extended carrier (`ν_R`, `ν_R^c` are gauge neutral, `repNR = 1`). -/
def rhoExt (y : SMGaugeGroup) : Matrix ExtIdx ExtIdx ℂ :=
  fromBlocks (rhoMin y) 0 0 (1 : Matrix NeutralIdx NeutralIdx ℂ)

theorem smU2_mem (y : SMGaugeGroup) : smU2 y ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (y : SMGaugeU3 × SMGaugeU2).2.2

theorem smU3_mem (y : SMGaugeGroup) : smU3 y ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
  (y : SMGaugeU3 × SMGaugeU2).1.2

theorem smChi_star (y : SMGaugeGroup) : star (smChi y) * smChi y = 1 :=
  star_det_of_unitary (smU2_mem y)

theorem one_mem_unitary' {r : Type*} [Fintype r] [DecidableEq r] :
    (1 : Matrix r r ℂ) ∈ unitary (Matrix r r ℂ) := one_mem _

theorem rhoLeft_mem (y : SMGaugeGroup) : rhoLeft y ∈ unitary (Matrix LeftIdx LeftIdx ℂ) := by
  refine fromBlocks_diag_mem_unitary (kronecker_mem_unitary ?_ one_mem_unitary')
    (kronecker_mem_unitary ?_ one_mem_unitary')
  · exact kronecker_mem_unitary (smU3_mem y) (smU2_mem y)
  · exact smul_mem_unitary (smChi_star y) (-1) (smU2_mem y)

theorem rhoRight_mem (y : SMGaugeGroup) :
    rhoRight y ∈ unitary (Matrix RightIdx RightIdx ℂ) := by
  refine fromBlocks_diag_mem_unitary (fromBlocks_diag_mem_unitary
    (kronecker_mem_unitary ?_ one_mem_unitary') (kronecker_mem_unitary ?_ one_mem_unitary'))
    (kronecker_mem_unitary ?_ one_mem_unitary')
  · exact smul_mem_unitary (smChi_star y) 1 (smU3_mem y)
  · exact smU3_mem y
  · exact smul_mem_unitary (smChi_star y) (-1) one_mem_unitary'

theorem rhoMin_mem (y : SMGaugeGroup) : rhoMin y ∈ unitary (Matrix MinIdx MinIdx ℂ) :=
  fromBlocks_diag_mem_unitary (rhoLeft_mem y) (rhoRight_mem y)

/-- Covariance of the left–right block: `ρ_L(g) A(H) = A(ρ_H(g) H) ρ_R(g)`. -/
theorem leftBlock_covariant (Y : YukawaBank) (y : SMGaugeGroup) (H : Fin 2 → ℂ) :
    rhoLeft y * leftBlock Y H = leftBlock Y (repH y *ᵥ H) * rhoRight y := by
  have hU2 := smU2_mem y
  have hQu : (repQL y) * tQu H = tQu (repH y *ᵥ H) * repUR y := by
    simp only [repQL, smBifund_apply, repUR, detTwist_apply, zpow_one, smChi_apply, repH]
    exact tQu_intertwine hU2 H
  have hQd : (repQL y) * tQd H = tQd (repH y *ᵥ H) * repDR y := by
    simp only [repQL, smBifund_apply, repDR, repH]
    exact tQd_intertwine H
  have hLe : (repLL y) * tLe H = tLe (repH y *ᵥ H) * repER y := by
    simp only [repLL, detTwist_apply, smChi_apply, repER, MonoidHom.one_apply, repH]
    exact tLe_intertwine H
  unfold rhoLeft leftBlock rhoRight
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [Matrix.mul_fromCols, fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, add_zero, zero_add]
  rw [kron_intertwine hQu, kron_intertwine hQd, kron_intertwine hLe]

/-- **Covariance of the minimal mass map**: `ρ(g) 𝓜_𝐘(H) = 𝓜_𝐘(ρ_H(g) H) ρ(g)`, i.e.
`𝓜_𝐘(ρ_H(g)H) = ρ(g) 𝓜_𝐘(H) ρ(g)⁻¹`. -/
theorem yukawaMin_covariant (Y : YukawaBank) (y : SMGaugeGroup) (H : Fin 2 → ℂ) :
    rhoMin y * yukawaMin Y H = yukawaMin Y (repH y *ᵥ H) * rhoMin y :=
  hermBlock_intertwine (rhoLeft_mem y) (rhoRight_mem y) (leftBlock_covariant Y y H)

theorem neutralBlock_covariant (Y : YukawaBank) (y : SMGaugeGroup) (H : Fin 2 → ℂ) :
    rhoMin y * neutralBlock Y H = neutralBlock Y (repH y *ᵥ H) := by
  have hLn : (repLL y) * tLn H = tLn (repH y *ᵥ H) * (1 : Matrix Unit Unit ℂ) := by
    simp only [repLL, detTwist_apply, smChi_apply, repH, Matrix.mul_one]
    exact tLn_intertwine (smU2_mem y) H
  unfold rhoMin neutralBlock rhoLeft
  rw [fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [fromBlocks_mul_fromRows]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [kron_intertwine hLn]
  simp only [one_kronecker_one, Matrix.mul_one]

/-- **Covariance of the neutral-extension mass map** (Dirac neutrino coupling and constant
symmetric Majorana block on the doubled carrier). -/
theorem yukawaExt_covariant (Y : YukawaBank) (y : SMGaugeGroup) (H : Fin 2 → ℂ) :
    rhoExt y * yukawaExt Y H = yukawaExt Y (repH y *ᵥ H) * rhoExt y := by
  have hN := neutralBlock_covariant Y y H
  have hu := rhoMin_mem y
  rw [Unitary.mem_iff] at hu
  simp only [Matrix.star_eq_conjTranspose] at hu
  have hNh : (neutralBlock Y H)ᴴ = (neutralBlock Y (repH y *ᵥ H))ᴴ * rhoMin y := by
    rw [← hN, conjTranspose_mul, Matrix.mul_assoc, hu.1, Matrix.mul_one]
  unfold rhoExt yukawaExt
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul,
    Matrix.mul_one]
  rw [yukawaMin_covariant, hN, ← hNh]

theorem rhoExt_mem (y : SMGaugeGroup) : rhoExt y ∈ unitary (Matrix ExtIdx ExtIdx ℂ) :=
  fromBlocks_diag_mem_unitary (rhoMin_mem y) one_mem_unitary'

/-- Invariance of the Hermitian mass bilinear `Ψ† 𝓜 Ψ` under a unitary intertwiner. -/
theorem bilinear_invariant {m : Type*} [Fintype m] [DecidableEq m] {ρ M M' : Matrix m m ℂ}
    (hu : ρ ∈ unitary (Matrix m m ℂ)) (h : ρ * M = M' * ρ) (ψ : m → ℂ) :
    star (ρ *ᵥ ψ) ⬝ᵥ (M' *ᵥ (ρ *ᵥ ψ)) = star ψ ⬝ᵥ (M *ᵥ ψ) := by
  rw [Unitary.mem_iff] at hu
  simp only [Matrix.star_eq_conjTranspose] at hu
  rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hu.1, Matrix.one_mulVec]

/-! ### Affinity in real Higgs coordinates -/

section Affine

theorem higgsConj_add (H H' : Fin 2 → ℂ) :
    higgsConj (H + H') = higgsConj H + higgsConj H' := by
  ext k; fin_cases k <;> simp [higgsConj] ; ring

theorem higgsConj_smul (t : ℝ) (H : Fin 2 → ℂ) : higgsConj (t • H) = t • higgsConj H := by
  ext k; fin_cases k <;> simp [higgsConj, Complex.real_smul]

theorem tQu_add (H H' : Fin 2 → ℂ) : tQu (H + H') = tQu H + tQu H' := by
  ext p b; simp only [tQu, higgsConj_add, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp

theorem tQu_smul (t : ℝ) (H : Fin 2 → ℂ) : tQu (t • H) = t • tQu H := by
  ext p b; simp only [tQu, higgsConj_smul, Matrix.smul_apply, Pi.smul_apply]; split_ifs <;> simp

theorem tQd_add (H H' : Fin 2 → ℂ) : tQd (H + H') = tQd H + tQd H' := by
  ext p b; simp only [tQd, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp

theorem tQd_smul (t : ℝ) (H : Fin 2 → ℂ) : tQd (t • H) = t • tQd H := by
  ext p b; simp only [tQd, Matrix.smul_apply, Pi.smul_apply]; split_ifs <;> simp

theorem tLe_add (H H' : Fin 2 → ℂ) : tLe (H + H') = tLe H + tLe H' := by
  ext i j; simp [tLe]

theorem tLe_smul (t : ℝ) (H : Fin 2 → ℂ) : tLe (t • H) = t • tLe H := by
  ext i j; simp [tLe]

theorem tLn_add (H H' : Fin 2 → ℂ) : tLn (H + H') = tLn H + tLn H' := by
  ext i j; simp [tLn, higgsConj_add]

theorem tLn_smul (t : ℝ) (H : Fin 2 → ℂ) : tLn (t • H) = t • tLn H := by
  ext i j; simp [tLn, higgsConj_smul]

variable {m n₁ n₂ : Type*}

theorem fromCols_add' (A A' : Matrix m n₁ ℂ) (B B' : Matrix m n₂ ℂ) :
    fromCols (A + A') (B + B') = fromCols A B + fromCols A' B' := by
  ext i j; cases j <;> simp

theorem fromCols_smul' (t : ℝ) (A : Matrix m n₁ ℂ) (B : Matrix m n₂ ℂ) :
    fromCols (t • A) (t • B) = t • fromCols A B := by
  ext i j; cases j <;> simp

theorem fromRows_add' (A A' : Matrix n₁ m ℂ) (B B' : Matrix n₂ m ℂ) :
    fromRows (A + A') (B + B') = fromRows A B + fromRows A' B' := by
  ext i j; cases i <;> simp

theorem fromRows_smul' (t : ℝ) (A : Matrix n₁ m ℂ) (B : Matrix n₂ m ℂ) :
    fromRows (t • A) (t • B) = t • fromRows A B := by
  ext i j; cases i <;> simp

theorem hermBlock_add [Fintype m] [Fintype n₁] (A A' : Matrix m n₁ ℂ) :
    hermBlock (A + A') = hermBlock A + hermBlock A' := by
  unfold hermBlock
  rw [conjTranspose_add, fromBlocks_add]
  simp

theorem hermBlock_smul [Fintype m] [Fintype n₁] (t : ℝ) (A : Matrix m n₁ ℂ) :
    hermBlock (t • A) = t • hermBlock A := by
  unfold hermBlock
  rw [conjTranspose_smul, fromBlocks_smul]
  simp

theorem leftBlock_add (Y : YukawaBank) (H H' : Fin 2 → ℂ) :
    leftBlock Y (H + H') = leftBlock Y H + leftBlock Y H' := by
  unfold leftBlock
  rw [tQu_add, tQd_add, tLe_add, add_kronecker, add_kronecker, add_kronecker, fromCols_add',
    fromBlocks_add]
  simp

theorem leftBlock_smul (Y : YukawaBank) (t : ℝ) (H : Fin 2 → ℂ) :
    leftBlock Y (t • H) = t • leftBlock Y H := by
  unfold leftBlock
  rw [tQu_smul, tQd_smul, tLe_smul, smul_kronecker, smul_kronecker, smul_kronecker,
    fromCols_smul', fromBlocks_smul]
  simp

theorem neutralBlock_add (Y : YukawaBank) (H H' : Fin 2 → ℂ) :
    neutralBlock Y (H + H') = neutralBlock Y H + neutralBlock Y H' := by
  unfold neutralBlock
  rw [tLn_add, add_kronecker, fromBlocks_add]
  simp only [add_zero]
  congr 1
  rw [← fromRows_add', add_zero]

theorem neutralBlock_smul (Y : YukawaBank) (t : ℝ) (H : Fin 2 → ℂ) :
    neutralBlock Y (t • H) = t • neutralBlock Y H := by
  unfold neutralBlock
  rw [tLn_smul, smul_kronecker, fromBlocks_smul]
  simp only [smul_zero]
  congr 1
  rw [← fromRows_smul', smul_zero]

/-- The linear part of the extended mass map (everything except the Majorana block). -/
def yukawaExtLin (Y : YukawaBank) (H : Fin 2 → ℂ) : Matrix ExtIdx ExtIdx ℂ :=
  fromBlocks (yukawaMin Y H) (neutralBlock Y H) (neutralBlock Y H)ᴴ 0

/-- The minimal mass map is real-linear in the Higgs field. -/
def yukawaMinLinear (Y : YukawaBank) : (Fin 2 → ℂ) →ₗ[ℝ] Matrix MinIdx MinIdx ℂ where
  toFun := yukawaMin Y
  map_add' H H' := by
    simp only [yukawaMin]; rw [leftBlock_add, hermBlock_add]
  map_smul' t H := by
    simp only [yukawaMin, RingHom.id_apply]; rw [leftBlock_smul, hermBlock_smul]

/-- The linear part of the extended mass map, as a real-linear map. -/
def yukawaExtLinear (Y : YukawaBank) : (Fin 2 → ℂ) →ₗ[ℝ] Matrix ExtIdx ExtIdx ℂ where
  toFun := yukawaExtLin Y
  map_add' H H' := by
    simp only [yukawaExtLin, yukawaMin]
    rw [leftBlock_add, hermBlock_add, neutralBlock_add, conjTranspose_add, fromBlocks_add]
    simp
  map_smul' t H := by
    simp only [yukawaExtLin, yukawaMin, RingHom.id_apply]
    rw [leftBlock_smul, hermBlock_smul, neutralBlock_smul, conjTranspose_smul, fromBlocks_smul]
    simp

theorem yukawaMin_zero (Y : YukawaBank) : yukawaMin Y 0 = 0 :=
  (yukawaMinLinear Y).map_zero

theorem neutralBlock_zero (Y : YukawaBank) : neutralBlock Y 0 = 0 := by
  have := neutralBlock_smul Y 0 0
  simpa using this

/-- **Affinity in real Higgs coordinates**: `𝓜_𝐘(H) = 𝓜_𝐘(0) + L_𝐘(H)` with `L_𝐘` real-linear
and `𝓜_𝐘(0)` the constant Majorana block. -/
theorem yukawaExt_affine (Y : YukawaBank) (H : Fin 2 → ℂ) :
    yukawaExt Y H = yukawaExt Y 0 + yukawaExtLinear Y H ∧
      yukawaExt Y 0 = fromBlocks 0 0 0 (majoranaBlock Y) := by
  have h0 : yukawaExt Y 0 = fromBlocks 0 0 0 (majoranaBlock Y) := by
    unfold yukawaExt
    rw [yukawaMin_zero, neutralBlock_zero, conjTranspose_zero]
  refine ⟨?_, h0⟩
  rw [h0]
  change _ = _ + yukawaExtLin Y H
  unfold yukawaExt yukawaExtLin
  rw [fromBlocks_add]
  simp

end Affine

/-! ### Entrywise bounds (`eq:yukawa-bound`) -/

section Bounds

/-- All entries of `M` are bounded by `c`. -/
def EntryLe {m n : Type*} (M : Matrix m n ℂ) (c : ℝ) : Prop := ∀ i j, ‖M i j‖ ≤ c

variable {m n o p : Type*}

theorem entryLe_zero {c : ℝ} (hc : 0 ≤ c) : EntryLe (0 : Matrix m n ℂ) c := by
  intro i j; simpa using hc

theorem EntryLe.mono {M : Matrix m n ℂ} {c c' : ℝ} (h : EntryLe M c) (hc : c ≤ c') :
    EntryLe M c' := fun i j => (h i j).trans hc

theorem entryLe_fromBlocks {A : Matrix m o ℂ} {B : Matrix m p ℂ} {C : Matrix n o ℂ}
    {D : Matrix n p ℂ} {c : ℝ} (hA : EntryLe A c) (hB : EntryLe B c) (hC : EntryLe C c)
    (hD : EntryLe D c) : EntryLe (fromBlocks A B C D) c := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j

theorem entryLe_fromCols {A : Matrix m o ℂ} {B : Matrix m p ℂ} {c : ℝ} (hA : EntryLe A c)
    (hB : EntryLe B c) : EntryLe (fromCols A B) c := by
  intro i j
  rcases j with j | j
  · exact hA i j
  · exact hB i j

theorem entryLe_fromRows {A : Matrix m o ℂ} {B : Matrix n o ℂ} {c : ℝ} (hA : EntryLe A c)
    (hB : EntryLe B c) : EntryLe (fromRows A B) c := by
  intro i j
  rcases i with i | i
  · exact hA i j
  · exact hB i j

theorem entryLe_conjTranspose {A : Matrix m n ℂ} {c : ℝ} (hA : EntryLe A c) :
    EntryLe Aᴴ c := by
  intro i j
  simpa [Matrix.conjTranspose_apply] using hA j i

theorem entryLe_kronecker {A : Matrix m n ℂ} {B : Matrix o p ℂ} {a b : ℝ} (hA : EntryLe A a)
    (hB : EntryLe B b) (ha : 0 ≤ a) : EntryLe (A ⊗ₖ B) (a * b) := by
  rintro ⟨i, k⟩ ⟨j, l⟩
  simp only [kroneckerMap_apply, norm_mul]
  exact mul_le_mul (hA i j) (hB k l) (norm_nonneg _) ha

theorem norm_higgsConj_le (H : Fin 2 → ℂ) (k : Fin 2) : ‖higgsConj H k‖ ≤ ‖H‖ := by
  fin_cases k
  · simpa [higgsConj] using norm_le_pi_norm H 1
  · simpa [higgsConj] using norm_le_pi_norm H 0

theorem entryLe_tQu (H : Fin 2 → ℂ) : EntryLe (tQu H) ‖H‖ := by
  intro p b; unfold tQu; split_ifs
  · exact norm_higgsConj_le H _
  · simp

theorem entryLe_tQd (H : Fin 2 → ℂ) : EntryLe (tQd H) ‖H‖ := by
  intro p b; unfold tQd; split_ifs
  · exact norm_le_pi_norm H _
  · simp

theorem entryLe_tLe (H : Fin 2 → ℂ) : EntryLe (tLe H) ‖H‖ := fun i _ => norm_le_pi_norm H i

theorem entryLe_tLn (H : Fin 2 → ℂ) : EntryLe (tLn H) ‖H‖ := fun i _ => norm_higgsConj_le H i

theorem entryLe_one_unit : EntryLe (1 : Matrix Unit Unit ℂ) 1 := by
  intro i j; simp

/-- A coefficient bank bounded by `R`: every Yukawa and Majorana entry has modulus `≤ R`. -/
def YukawaBank.BoundedBy (Y : YukawaBank) (R : ℝ) : Prop :=
  EntryLe Y.Yu R ∧ EntryLe Y.Yd R ∧ EntryLe Y.Ye R ∧ EntryLe Y.Yn R ∧ EntryLe Y.MR R

theorem entryLe_yukawaExtLin (Y : YukawaBank) {R : ℝ} (hR : 0 ≤ R) (hY : Y.BoundedBy R)
    (H : Fin 2 → ℂ) : EntryLe (yukawaExtLinear Y H) (‖H‖ * R) := by
  obtain ⟨hu, hd, he, hn, -⟩ := hY
  have hH := norm_nonneg H
  have hc : 0 ≤ ‖H‖ * R := mul_nonneg hH hR
  have hL : EntryLe (leftBlock Y H) (‖H‖ * R) :=
    entryLe_fromBlocks (entryLe_fromCols (entryLe_kronecker (entryLe_tQu H) hu hH)
      (entryLe_kronecker (entryLe_tQd H) hd hH)) (entryLe_zero hc) (entryLe_zero hc)
      (entryLe_kronecker (entryLe_tLe H) he hH)
  have hN : EntryLe (neutralBlock Y H) (‖H‖ * R) :=
    entryLe_fromBlocks (entryLe_fromRows (entryLe_zero hc)
      (entryLe_kronecker (entryLe_tLn H) hn hH)) (entryLe_zero hc) (entryLe_zero hc)
      (entryLe_zero hc)
  change EntryLe (yukawaExtLin Y H) _
  exact entryLe_fromBlocks (entryLe_fromBlocks (entryLe_zero hc) hL
    (entryLe_conjTranspose hL) (entryLe_zero hc)) hN (entryLe_conjTranspose hN) (entryLe_zero hc)

/-- **`eq:yukawa-bound`** on a bounded coefficient bank (entrywise form): if all Yukawa and
Majorana entries have modulus `≤ R`, then every entry of `𝓜_𝐘(H)` is bounded by
`R (1 + |H|)`, and every entry of the Higgs derivative `D_H 𝓜_𝐘(H)[η] = L_𝐘(η)` by `R |η|`.
The constant depends only on `R`. -/
theorem yukawa_bound (Y : YukawaBank) {R : ℝ} (hR : 0 ≤ R) (hY : Y.BoundedBy R)
    (H η : Fin 2 → ℂ) :
    EntryLe (yukawaExt Y H) (R * (1 + ‖H‖)) ∧
      yukawaExt Y (H + η) - yukawaExt Y H = yukawaExtLinear Y η ∧
      EntryLe (yukawaExtLinear Y η) (R * ‖η‖) := by
  have hH := norm_nonneg H
  obtain ⟨hA, h0⟩ := yukawaExt_affine Y H
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, h0]
    have hMaj : EntryLe (majoranaBlock Y) (1 * R) := by
      have h1 := entryLe_kronecker entryLe_one_unit hY.2.2.2.2 zero_le_one
      exact entryLe_fromBlocks (entryLe_zero (by positivity)) h1 (entryLe_conjTranspose h1)
        (entryLe_zero (by positivity))
    have hlin := entryLe_yukawaExtLin Y hR hY H
    intro i j
    rw [Matrix.add_apply]
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖(fromBlocks 0 0 0 (majoranaBlock Y) : Matrix ExtIdx ExtIdx ℂ) i j‖ ≤ 1 * R :=
      entryLe_fromBlocks (entryLe_zero (by positivity)) (entryLe_zero (by positivity))
        (entryLe_zero (by positivity)) hMaj i j
    have e2 := hlin i j
    nlinarith
  · obtain ⟨hA', -⟩ := yukawaExt_affine Y (H + η)
    rw [hA', hA, map_add]
    abel
  · have := entryLe_yukawaExtLin Y hR hY η
    exact this.mono (by rw [mul_comm])

end Bounds

/-- **`lem:SM-descent`** (assembly).
1. *Descent*: every row of `tab:SM-representations` (with `ν_R` on the neutral extension and
   the Higgs doublet) on the cover `SU(3) × SU(2) × U(1)` with weight `6Y` is the pull-back of
   an explicit representation of `G_SM = S(U(3) × U(2))` (`sm_descent`).
2. *Covariant Yukawa blocks*: the mass map `𝓜_𝐘(H)` assembled from
   `Q̄_L H̃ Y_u u_R + Q̄_L H Y_d d_R + L̄_L H Y_e e_R` + h.c. (minimal packet), and on the
   neutral extension also `L̄_L H̃ Y_ν ν_R` + h.c. and the constant symmetric Majorana block on
   `ν_R ⊕ ν_R^c`, satisfies `ρ(g) 𝓜_𝐘(H) = 𝓜_𝐘(ρ_H(g)H) ρ(g)` for the unitary fermion
   representation, so the Hermitian mass bilinear `Ψ†𝓜_𝐘(H)Ψ` is gauge invariant.
3. *Affinity*: `𝓜_𝐘(H) = 𝓜_𝐘(0) + L_𝐘(H)` with `L_𝐘` real-linear and `𝓜_𝐘(0)` the Majorana
   block.
4. *`eq:yukawa-bound`* on every bank bounded by `R`, with constants depending only on `R`. -/
theorem sm_descent_yukawa (Y : YukawaBank) (y : SMGaugeGroup) :
    (repQL.comp smGaugeHom = coverRow 1 FaithfulSMQuotient.bifund ∧
      repUR.comp smGaugeHom = coverRow 4 FaithfulSMQuotient.colour ∧
      repDR.comp smGaugeHom = coverRow (-2) FaithfulSMQuotient.colour ∧
      repLL.comp smGaugeHom = coverRow (-3) FaithfulSMQuotient.weak ∧
      repER.comp smGaugeHom = coverRow (-6) (1 : SMGaugeCover →* Matrix Unit Unit ℂ) ∧
      repNR.comp smGaugeHom = coverRow 0 (1 : SMGaugeCover →* Matrix Unit Unit ℂ) ∧
      repH.comp smGaugeHom = coverRow 3 FaithfulSMQuotient.weak) ∧
    (∀ H, rhoMin y * yukawaMin Y H = yukawaMin Y (repH y *ᵥ H) * rhoMin y) ∧
    (∀ H, rhoExt y * yukawaExt Y H = yukawaExt Y (repH y *ᵥ H) * rhoExt y) ∧
    (∀ H ψ, star (rhoExt y *ᵥ ψ) ⬝ᵥ (yukawaExt Y (repH y *ᵥ H) *ᵥ (rhoExt y *ᵥ ψ)) =
      star ψ ⬝ᵥ (yukawaExt Y H *ᵥ ψ)) ∧
    (∀ H, yukawaExt Y H = yukawaExt Y 0 + yukawaExtLinear Y H) ∧
    (∀ R, 0 ≤ R → Y.BoundedBy R → ∀ H η,
      EntryLe (yukawaExt Y H) (R * (1 + ‖H‖)) ∧
      yukawaExt Y (H + η) - yukawaExt Y H = yukawaExtLinear Y η ∧
      EntryLe (yukawaExtLinear Y η) (R * ‖η‖)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := sm_descent
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, fun H => yukawaMin_covariant Y y H,
    fun H => yukawaExt_covariant Y y H,
    fun H ψ => bilinear_invariant (rhoExt_mem y) (yukawaExt_covariant Y y H) ψ,
    fun H => (yukawaExt_affine Y H).1, fun R hR hY H η => yukawa_bound Y hR hY H η⟩

end

end SMDescentYukawa

end RenewalGeometry
