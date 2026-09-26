/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.DegreeOneColourNoGoExact

/-!
# The degree-one relative commutant is `ℂ ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ`

`eq:degree-one-commutant` of `thm:active-isotypic` (spacetime–gauge duality paper): the
relative commutant of the tetrahedral relabeling action on the ordered-root carrier
`E` (`DegreeOneColourNoGo.degreeOneCommutant`, dimension `7`) is isomorphic as a
unital `ℂ`-algebra to `ℂ ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ`, the blocks being the multiplicity algebras
of `ℂ_type` (`Qtype`), `W ⊗ ℂ²` (the two standard blocks `QC = W₊`, `QG = W₋` and the
intertwiners `E12 = QC X QG`, `E21 ∝ QG X QC` built from the same-tail-minus-same-head
pattern `X`), `V₂` (`QW2`) and `W ⊗ sgn` (`QP`).

* `E12_mul_E21`, `E21_mul_E12`: `E12 E21 = QC`, `E21 E12 = QG` — the two standard
  blocks are linked by a `2 × 2` system of matrix units (kernel-checked over `ℤ`);
* `toMatHom`: the unital algebra homomorphism `ℂ × M₂(ℂ) × ℂ × ℂ → M_E(ℂ)` with image
  in the commutant, with an explicit trace left inverse (`coords_toMat`);
* `degreeOneCommutantEquiv : ℂ × M₂(ℂ) × ℂ × ℂ ≃ₐ[ℂ] degreeOneCommutant` and
  `finrank_degreeOneCommutant : finrank = 7`.
-/

open Matrix Module RenewalGeometry.ActiveResidual RenewalGeometry.EdgeCommutant
  RenewalGeometry.DegreeOneColourNoGo

namespace RenewalGeometry
namespace DegreeOneWedderburn

/-! ### The odd intertwiner pattern -/

/-- Same-tail pattern (distinct roots with the same tail). -/
def NtZ : Matrix E E ℤ := fun e f => if e.val.1 = f.val.1 ∧ e ≠ f then 1 else 0

/-- Same-head pattern (distinct roots with the same head). -/
def NhZ : Matrix E E ℤ := fun e f => if e.val.2 = f.val.2 ∧ e ≠ f then 1 else 0

/-- The reversal-odd, `S₄`-invariant pattern `X = N_tail − N_head`. -/
def XZ : Matrix E E ℤ := NtZ - NhZ

set_option maxHeartbeats 400000 in
theorem NtZ_sub_NhZ_eq_rel : ∀ e f : E,
    NtZ e f - NhZ e f =
      ((if rel e f = 2 then 1 else 0) - (if rel e f = 3 then 1 else 0) : ℤ) := by
  decide

theorem XZ_eq_rel (e f : E) :
    XZ e f = ((if rel e f = 2 then 1 else 0) - (if rel e f = 3 then 1 else 0) : ℤ) := by
  rw [XZ, Matrix.sub_apply, NtZ_sub_NhZ_eq_rel]

/-- `X` over `ℂ`. -/
noncomputable def X : Matrix E E ℂ := cz XZ

theorem X_eq : X = EdgeCommutantBasis.relMatrix 2 - EdgeCommutantBasis.relMatrix 3 := by
  ext e f
  simp only [X, cz, Matrix.map_apply, XZ_eq_rel, Matrix.sub_apply, EdgeCommutantBasis.relMatrix]
  push_cast
  rfl

/-- `X` lies in the degree-one commutant. -/
theorem X_comm (σ : Equiv.Perm V) : X * Pm σ = Pm σ * X := by
  rw [X_eq, Matrix.sub_mul, Matrix.mul_sub, EdgeCommutantBasis.relMatrix_mem 2 σ,
    EdgeCommutantBasis.relMatrix_mem 3 σ]

set_option maxHeartbeats 4000000 in
theorem hZ3X4X3 : Z3 * XZ * Z4 * XZ * Z3 = 4608 • Z3 := by decide

set_option maxHeartbeats 4000000 in
theorem hZ4X3X4 : Z4 * XZ * Z3 * XZ * Z4 = 4608 • Z4 := by decide

theorem QC_X_QG_X_QC : QC * X * QG * X * QC = (8 : ℂ) • QC := by
  have h : cz (Z3 * XZ * Z4 * XZ * Z3) = (4608 : ℂ) • cz Z3 := by
    rw [hZ3X4X3, cz_nsmul]; norm_num
  simp only [QC, QG, X, Matrix.smul_mul, Matrix.mul_smul, ← cz_mul, h, smul_smul]
  norm_num

theorem QG_X_QC_X_QG : QG * X * QC * X * QG = (8 : ℂ) • QG := by
  have h : cz (Z4 * XZ * Z3 * XZ * Z4) = (4608 : ℂ) • cz Z4 := by
    rw [hZ4X3X4, cz_nsmul]; norm_num
  simp only [QC, QG, X, Matrix.smul_mul, Matrix.mul_smul, ← cz_mul, h, smul_smul]
  norm_num

theorem QG_QC : QG * QC = 0 := orth_symm QC_herm QG_herm QC_QG

/-! ### Matrix units between the two standard blocks -/

/-- `E12 = QC X QG : W₋ → W₊`. -/
noncomputable def E12 : Matrix E E ℂ := QC * X * QG

/-- `E21 = (1/8) QG X QC : W₊ → W₋`. -/
noncomputable def E21 : Matrix E E ℂ := (8 : ℂ)⁻¹ • (QG * X * QC)

theorem E12_mul_E21 : E12 * E21 = QC := by
  rw [E12, E21, Matrix.mul_smul]
  have : QC * X * QG * (QG * X * QC) = QC * X * QG * X * QC := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (QC * X) QG QG, QG_idem]
  rw [this, QC_X_QG_X_QC, smul_smul]
  norm_num

theorem E21_mul_E12 : E21 * E12 = QG := by
  rw [E12, E21, Matrix.smul_mul]
  have : QG * X * QC * (QC * X * QG) = QG * X * QC * X * QG := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (QG * X) QC QC, QC_idem]
  rw [this, QG_X_QC_X_QG, smul_smul]
  norm_num

theorem E12_mul_E12 : E12 * E12 = 0 := by
  rw [E12]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (QC * X) QG QC, QG_QC]
  simp

theorem E21_mul_E21 : E21 * E21 = 0 := by
  rw [E21, Matrix.smul_mul, Matrix.mul_smul]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (QG * X) QC QG, QC_QG]
  simp

theorem Q_mul_E12 {Q : Matrix E E ℂ} (h : Q * QC = 0) : Q * E12 = 0 := by
  rw [E12, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.zero_mul, Matrix.zero_mul]

theorem E12_mul_Q {Q : Matrix E E ℂ} (h : QG * Q = 0) : E12 * Q = 0 := by
  rw [E12, Matrix.mul_assoc, h, Matrix.mul_zero]

theorem Q_mul_E21 {Q : Matrix E E ℂ} (h : Q * QG = 0) : Q * E21 = 0 := by
  rw [E21, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.zero_mul,
    Matrix.zero_mul, smul_zero]

theorem E21_mul_Q {Q : Matrix E E ℂ} (h : QC * Q = 0) : E21 * Q = 0 := by
  rw [E21, Matrix.smul_mul, Matrix.mul_assoc, h, Matrix.mul_zero, smul_zero]

theorem QC_mul_E12 : QC * E12 = E12 := by
  rw [E12, ← Matrix.mul_assoc, ← Matrix.mul_assoc, QC_idem]

theorem E12_mul_QG : E12 * QG = E12 := by
  rw [E12, Matrix.mul_assoc, QG_idem]

theorem QG_mul_E21 : QG * E21 = E21 := by
  rw [E21, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, QG_idem]

theorem E21_mul_QC : E21 * QC = E21 := by
  rw [E21, Matrix.smul_mul, Matrix.mul_assoc, QC_idem]

theorem E12_trace : E12.trace = 0 := by
  rw [E12, Matrix.trace_mul_comm, ← Matrix.mul_assoc, QG_QC, Matrix.zero_mul,
    Matrix.trace_zero]

theorem E21_trace : E21.trace = 0 := by
  rw [E21, Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, QC_QG, Matrix.zero_mul,
    Matrix.trace_zero, smul_zero]

/-! ### The reversed orthogonality relations -/

theorem QW2_Qtype : QW2 * Qtype = 0 := orth_symm Qtype_herm QW2_herm Qtype_QW2
theorem QC_Qtype : QC * Qtype = 0 := orth_symm Qtype_herm QC_herm Qtype_QC
theorem QG_Qtype : QG * Qtype = 0 := orth_symm Qtype_herm QG_herm Qtype_QG
theorem QP_Qtype : QP * Qtype = 0 := orth_symm Qtype_herm QP_herm Qtype_QP
theorem QC_QW2 : QC * QW2 = 0 := orth_symm QW2_herm QC_herm QW2_QC
theorem QG_QW2 : QG * QW2 = 0 := orth_symm QW2_herm QG_herm QW2_QG
theorem QP_QW2 : QP * QW2 = 0 := orth_symm QW2_herm QP_herm QW2_QP
theorem QP_QC : QP * QC = 0 := orth_symm QC_herm QP_herm QC_QP
theorem QP_QG : QP * QG = 0 := orth_symm QG_herm QP_herm QG_QP

/-! ### The algebra homomorphism -/

/-- The coordinate algebra `ℂ ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ`. -/
abbrev Coord := ℂ × Matrix (Fin 2) (Fin 2) ℂ × ℂ × ℂ

/-- `(a, M, b, c) ↦ a Qtype + M₀₀ QC + M₀₁ E12 + M₁₀ E21 + M₁₁ QG + b QW2 + c QP`. -/
noncomputable def toMat (x : Coord) : Matrix E E ℂ :=
  x.1 • Qtype + (x.2.1 0 0 • QC + x.2.1 0 1 • E12 + x.2.1 1 0 • E21 + x.2.1 1 1 • QG) +
    x.2.2.1 • QW2 + x.2.2.2 • QP

theorem toMat_mul (x y : Coord) : toMat (x * y) = toMat x * toMat y := by
  simp only [toMat, Prod.fst_mul, Prod.snd_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Qtype_idem, QW2_idem, QC_idem, QG_idem, QP_idem,
    Qtype_QW2, Qtype_QC, Qtype_QG, Qtype_QP, QW2_QC, QW2_QG, QW2_QP, QC_QG, QC_QP, QG_QP,
    QW2_Qtype, QC_Qtype, QG_Qtype, QP_Qtype, QC_QW2, QG_QW2, QP_QW2, QP_QC, QP_QG, QG_QC,
    Q_mul_E12 Qtype_QC, Q_mul_E12 QW2_QC, Q_mul_E12 QG_QC, Q_mul_E12 QP_QC,
    E12_mul_Q QG_Qtype, E12_mul_Q QG_QW2, E12_mul_Q QG_QC, E12_mul_Q QG_QP,
    Q_mul_E21 Qtype_QG, Q_mul_E21 QW2_QG, Q_mul_E21 QC_QG, Q_mul_E21 QP_QG,
    E21_mul_Q QC_Qtype, E21_mul_Q QC_QW2, E21_mul_Q QC_QG, E21_mul_Q QC_QP,
    QC_mul_E12, E12_mul_QG, QG_mul_E21, E21_mul_QC, E12_mul_E21, E21_mul_E12, E12_mul_E12,
    E21_mul_E21, smul_zero, add_zero, zero_add, smul_smul]
  module

theorem toMat_one : toMat 1 = 1 := by
  simp only [toMat, Prod.fst_one, Prod.snd_one, Matrix.one_apply, Fin.isValue, ↓reduceIte,
    Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat,
    one_smul, zero_smul, add_zero, zero_add]
  rw [← Qsum]
  abel

/-- The unital algebra homomorphism `ℂ × M₂(ℂ) × ℂ × ℂ →ₐ[ℂ] M_E(ℂ)`. -/
noncomputable def toMatHom : Coord →ₐ[ℂ] Matrix E E ℂ where
  toFun := toMat
  map_one' := toMat_one
  map_mul' := toMat_mul
  map_zero' := by simp [toMat]
  map_add' x y := by
    simp only [toMat, Prod.fst_add, Prod.snd_add, Matrix.add_apply, add_smul]
    abel
  commutes' c := by
    simp only [toMat, Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_one, Prod.snd_one, Matrix.smul_apply, Matrix.one_apply, Fin.isValue,
      ↓reduceIte, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
      OfNat.one_ne_ofNat, smul_eq_mul, mul_one, mul_zero, zero_smul, add_zero, zero_add]
    rw [← Qsum]
    simp only [smul_add]
    abel

theorem toMatHom_apply (x : Coord) : toMatHom x = toMat x := rfl

/-! ### The trace left inverse -/

/-- Trace coordinates on `M_E(ℂ)`, a left inverse of `toMat`. -/
noncomputable def coords (Y : Matrix E E ℂ) : Coord :=
  ((Qtype * Y).trace,
    !![(QC * Y).trace / 3, (E21 * Y).trace / 3; (E12 * Y).trace / 3, (QG * Y).trace / 3],
    (QW2 * Y).trace / 2, (QP * Y).trace / 3)

theorem coords_toMat (x : Coord) : coords (toMat x) = x := by
  obtain ⟨a, M, b, c⟩ := x
  simp only [coords, toMat, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Qtype_idem, QW2_idem, QC_idem, QG_idem, QP_idem,
    Qtype_QW2, Qtype_QC, Qtype_QG, Qtype_QP, QW2_QC, QW2_QG, QW2_QP, QC_QG, QC_QP, QG_QP,
    QW2_Qtype, QC_Qtype, QG_Qtype, QP_Qtype, QC_QW2, QG_QW2, QP_QW2, QP_QC, QP_QG, QG_QC,
    Q_mul_E12 Qtype_QC, Q_mul_E12 QW2_QC, Q_mul_E12 QG_QC, Q_mul_E12 QP_QC,
    Q_mul_E21 Qtype_QG, Q_mul_E21 QW2_QG, Q_mul_E21 QC_QG, Q_mul_E21 QP_QG,
    E21_mul_Q QC_Qtype, E21_mul_Q QC_QW2, E21_mul_Q QC_QG, E21_mul_Q QC_QP,
    E12_mul_Q QG_Qtype, E12_mul_Q QG_QW2, E12_mul_Q QG_QC, E12_mul_Q QG_QP,
    QC_mul_E12, QG_mul_E21, E12_mul_QG, E21_mul_QC, E12_mul_E21, E21_mul_E12, E12_mul_E12,
    E21_mul_E21, E12_trace, E21_trace, Qtype_trace, QW2_trace, QC_trace, QG_trace, QP_trace,
    Matrix.trace_zero, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, mul_one]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp <;> try ring
  · simp <;> try ring
  · simp <;> try ring

theorem toMat_injective : Function.Injective toMat :=
  Function.LeftInverse.injective coords_toMat

/-! ### Landing in the commutant -/

theorem toMat_comm (x : Coord) (σ : Equiv.Perm V) : toMat x * Pm σ = Pm σ * toMat x := by
  have hQ : ∀ Q : Matrix E E ℂ,
      Q ∈ Submodule.span ℂ ({1, Rm, Nm, Mm, Dis} : Set (Matrix E E ℂ)) →
      Q * Pm σ = Pm σ * Q := fun Q hQ => Q_central hQ (Pm σ) (Pm_mem σ)
  have hE12 : E12 * Pm σ = Pm σ * E12 := by
    rw [E12, Matrix.mul_assoc, hQ QG QG_mem_span, ← Matrix.mul_assoc, Matrix.mul_assoc QC,
      X_comm, ← Matrix.mul_assoc, hQ QC QC_mem_span]
    simp only [Matrix.mul_assoc]
  have hE21 : E21 * Pm σ = Pm σ * E21 := by
    rw [E21, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hQ QC QC_mem_span,
      ← Matrix.mul_assoc, Matrix.mul_assoc QG, X_comm, ← Matrix.mul_assoc, hQ QG QG_mem_span]
    simp only [Matrix.mul_assoc]
  simp only [toMat, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    hQ Qtype Qtype_mem_span, hQ QW2 QW2_mem_span, hQ QC QC_mem_span, hQ QG QG_mem_span,
    hQ QP QP_mem_span, hE12, hE21]

theorem toMat_mem (x : Coord) : toMat x ∈ degreeOneCommutant :=
  mem_degreeOneCommutant.mpr (toMat_comm x)

/-- The homomorphism into the degree-one commutant. -/
noncomputable def toCommutantHom : Coord →ₐ[ℂ] degreeOneCommutant :=
  toMatHom.codRestrict degreeOneCommutant toMat_mem

theorem toCommutantHom_injective : Function.Injective toCommutantHom := by
  intro x y h
  apply toMat_injective
  exact congrArg Subtype.val h

theorem finrank_Coord : finrank ℂ Coord = 7 := by
  simp [Module.finrank_prod, Module.finrank_matrix]

/-- The degree-one commutant has dimension exactly seven. -/
theorem finrank_degreeOneCommutant : finrank ℂ degreeOneCommutant = 7 := by
  refine le_antisymm finrank_degreeOneCommutant_le ?_
  have h := LinearMap.finrank_le_finrank_of_injective (f := toCommutantHom.toLinearMap)
    toCommutantHom_injective
  rw [finrank_Coord] at h
  exact h

theorem toCommutantHom_surjective : Function.Surjective toCommutantHom := by
  have h := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := toCommutantHom.toLinearMap)
    (by rw [finrank_Coord, finrank_degreeOneCommutant])).mp toCommutantHom_injective
  exact h

/-- **`eq:degree-one-commutant`**: the relative commutant of the external tetrahedral
action on the degree-one categorical carrier is `ℂ ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ` — the multiplicity
algebras of `ℂ_type`, `W ⊗ ℂ²`, `V₂`, `W ⊗ sgn` (multiplicities `1, 2, 1, 1`). -/
noncomputable def degreeOneCommutantEquiv : Coord ≃ₐ[ℂ] degreeOneCommutant :=
  AlgEquiv.ofBijective toCommutantHom ⟨toCommutantHom_injective, toCommutantHom_surjective⟩

/-- The isomorphism sends `(a, M, b, c)` to
`a Qtype + M₀₀ QC + M₀₁ E12 + M₁₀ E21 + M₁₁ QG + b QW2 + c QP`. -/
theorem degreeOneCommutantEquiv_apply (x : Coord) :
    (degreeOneCommutantEquiv x : Matrix E E ℂ) = toMat x := rfl

end DegreeOneWedderburn
end RenewalGeometry
