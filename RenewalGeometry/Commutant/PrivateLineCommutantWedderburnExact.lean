/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.DegreeOneCommutantWedderburnExact

/-!
# The private-line relative commutant is `M₂(ℂ) ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ`

`eq:degree-one-private-commutant` of `thm:active-isotypic` (spacetime–gauge duality
paper): after adjoining one external-trivial private contrast line to the ordered-root
carrier `E`, the relative commutant of the extended tetrahedral action on
`E ⊕ ℂ` (`DegreeOneColourNoGo.privateLineCommutant`) is isomorphic as a unital
`ℂ`-algebra to `M₂(ℂ) ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ` (dimension `10`): the multiplicity vector
`(1, 2, 1, 1)` of `E` becomes `(2, 2, 1, 1)`, the trivial sector now carrying the type
line `ℂ_type ⊂ E` together with the private line.

* `Z1_apply`, `Qtype_apply`: the trivial-isotypic projection `Qtype` is `(1/12) J`
  (`J` the all-ones matrix), so the constant column `u0` and the normalised constant
  row `v0 = (1/12) u0ᴴ` satisfy `Qtype u0 = u0`, `v0 Qtype = v0`, `v0 u0 = 1`,
  `u0 v0 = Qtype`, and all other blocks annihilate them;
* `toMatHom'`: the unital algebra homomorphism
  `M₂(ℂ) × M₂(ℂ) × ℂ × ℂ →ₐ[ℂ] M_{E ⊕ ℂ}(ℂ)`, sending `(N, M, b, c)` to the block
  matrix `[[N₀₀ Qtype + (M-block) + b QW2 + c QP, N₀₁ u0], [N₁₀ v0, N₁₁]]`, with an
  explicit left inverse `coords'`;
* `column_invariant`, `row_invariant`: `S₄`-invariant columns and rows on `E` are
  constant (transitivity of the relabeling action on ordered roots, `act_transitive`);
* `privateLineCommutantEquiv : M₂(ℂ) × M₂(ℂ) × ℂ × ℂ ≃ₐ[ℂ] privateLineCommutant` and
  `finrank_privateLineCommutant : finrank = 10`.
-/

open Matrix Module RenewalGeometry.ActiveResidual RenewalGeometry.EdgeCommutant
  RenewalGeometry.DegreeOneColourNoGo RenewalGeometry.DegreeOneWedderburn

namespace RenewalGeometry
namespace PrivateLineWedderburn

/-! ### The trivial-isotypic projection is `(1/12) J` -/

theorem Z1_eq : Z1 = Matrix.of fun _ _ => (2 : ℤ) := by decide

theorem Z1_apply (e f : E) : Z1 e f = 2 := by
  rw [Z1_eq, Matrix.of_apply]

theorem Qtype_apply (e f : E) : Qtype e f = (12 : ℂ)⁻¹ := by
  rw [Qtype, Matrix.smul_apply, cz, Matrix.map_apply, Z1_apply]
  push_cast
  norm_num

/-- The constant column on `E`. -/
def u0 : Matrix E Unit ℂ := fun _ _ => 1

/-- The normalised constant row `(1/12) u0ᴴ` on `E`. -/
noncomputable def v0 : Matrix Unit E ℂ := fun _ _ => (12 : ℂ)⁻¹

theorem Qtype_mul_u0 : Qtype * u0 = u0 := by
  ext e i
  simp only [Matrix.mul_apply, Qtype_apply, u0, mul_one, Finset.sum_const, Finset.card_univ,
    card_E, nsmul_eq_mul]
  norm_num

theorem v0_mul_Qtype : v0 * Qtype = v0 := by
  ext i f
  simp only [Matrix.mul_apply, Qtype_apply, v0, Finset.sum_const, Finset.card_univ,
    card_E, nsmul_eq_mul]
  norm_num

theorem v0_mul_u0 : v0 * u0 = 1 := by
  ext i j
  simp only [Matrix.mul_apply, v0, u0, mul_one, Finset.sum_const, Finset.card_univ,
    card_E, nsmul_eq_mul, Matrix.one_apply, ite_true]
  norm_num

theorem u0_mul_v0 : u0 * v0 = Qtype := by
  ext e f
  simp only [Matrix.mul_apply, v0, u0, one_mul, Qtype_apply, Finset.univ_unique,
    Finset.sum_singleton]

theorem Q_mul_u0 {Q : Matrix E E ℂ} (h : Q * Qtype = 0) : Q * u0 = 0 := by
  rw [← Qtype_mul_u0, ← Matrix.mul_assoc, h, Matrix.zero_mul]

theorem v0_mul_Q {Q : Matrix E E ℂ} (h : Qtype * Q = 0) : v0 * Q = 0 := by
  rw [← v0_mul_Qtype, Matrix.mul_assoc, h, Matrix.mul_zero]

/-! ### Invariance of the constant column and row -/

theorem Pm_mul_apply (σ : Equiv.Perm V) (B : Matrix E Unit ℂ) (e : E) (i : Unit) :
    (Pm σ * B) e i = B (act σ⁻¹ e) i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (act σ⁻¹ e)]
  · rw [Pm_apply, if_pos, one_mul]
    rw [← act_mul, mul_inv_cancel, act_one]
  · intro f _ hf
    rw [Pm_apply, if_neg, zero_mul]
    intro h
    apply hf
    rw [h, ← act_mul, inv_mul_cancel, act_one]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_Pm_apply (σ : Equiv.Perm V) (C : Matrix Unit E ℂ) (i : Unit) (f : E) :
    (C * Pm σ) i f = C i (act σ f) := by
  simp only [Matrix.mul_apply, Pm_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem Pm_mul_u0 (σ : Equiv.Perm V) : Pm σ * u0 = u0 := by
  ext e i
  rw [Pm_mul_apply]
  rfl

theorem v0_mul_Pm (σ : Equiv.Perm V) : v0 * Pm σ = v0 := by
  ext i f
  rw [mul_Pm_apply]
  rfl

/-- The relabeling action of `S₄` is transitive on ordered roots. -/
theorem act_transitive : ∀ e : E, ∃ τ : Equiv.Perm V, act τ e01 = e := by decide

/-- An `S₄`-invariant column on `E` is constant. -/
theorem column_invariant {B : Matrix E Unit ℂ} (h : ∀ σ, Pm σ * B = B) :
    B = B e01 () • u0 := by
  ext e i
  obtain ⟨τ, hτ⟩ := act_transitive e
  have := congrFun (congrFun (h τ⁻¹) e01) i
  rw [Pm_mul_apply, inv_inv, hτ] at this
  cases i
  simp only [Matrix.smul_apply, u0, smul_eq_mul, mul_one]
  exact this

/-- An `S₄`-invariant row on `E` is constant. -/
theorem row_invariant {C : Matrix Unit E ℂ} (h : ∀ σ, C * Pm σ = C) :
    C = (12 * C () e01) • v0 := by
  ext i e
  obtain ⟨τ, hτ⟩ := act_transitive e
  have := congrFun (congrFun (h τ) i) e01
  rw [mul_Pm_apply, hτ] at this
  cases i
  simp only [Matrix.smul_apply, v0, smul_eq_mul]
  rw [← this]
  field_simp

/-! ### The algebra homomorphism -/

/-- The coordinate algebra `M₂(ℂ) ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ`. -/
abbrev Coord' := Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ × ℂ × ℂ

/-- `(N, M, b, c) ↦ [[N₀₀ Qtype + M₀₀ QC + M₀₁ E12 + M₁₀ E21 + M₁₁ QG + b QW2 + c QP, N₀₁ u0],
[N₁₀ v0, N₁₁]]`. -/
noncomputable def toMat' (x : Coord') : Matrix Eplus Eplus ℂ :=
  Matrix.fromBlocks (toMat (x.1 0 0, x.2.1, x.2.2.1, x.2.2.2)) (x.1 0 1 • u0) (x.1 1 0 • v0)
    (x.1 1 1 • 1)

theorem toMat_add (x y : Coord) : toMat (x + y) = toMat x + toMat y := toMatHom.map_add x y

theorem toMat_smul (r : ℂ) (x : Coord) : toMat (r • x) = r • toMat x := map_smul toMatHom r x

theorem toMat_zero : toMat 0 = 0 := toMatHom.map_zero

theorem toMat'_mul (x y : Coord') : toMat' (x * y) = toMat' x * toMat' y := by
  simp only [toMat', toMat, Matrix.fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul,
    Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Qtype_idem, QW2_idem, QC_idem, QG_idem, QP_idem,
      Qtype_QW2, Qtype_QC, Qtype_QG, Qtype_QP, QW2_QC, QW2_QG, QW2_QP, QC_QG, QC_QP, QG_QP,
      QW2_Qtype, QC_Qtype, QG_Qtype, QP_Qtype, QC_QW2, QG_QW2, QP_QW2, QP_QC, QP_QG, QG_QC,
      Q_mul_E12 Qtype_QC, Q_mul_E12 QW2_QC, Q_mul_E12 QG_QC, Q_mul_E12 QP_QC,
      E12_mul_Q QG_Qtype, E12_mul_Q QG_QW2, E12_mul_Q QG_QC, E12_mul_Q QG_QP,
      Q_mul_E21 Qtype_QG, Q_mul_E21 QW2_QG, Q_mul_E21 QC_QG, Q_mul_E21 QP_QG,
      E21_mul_Q QC_Qtype, E21_mul_Q QC_QW2, E21_mul_Q QC_QG, E21_mul_Q QC_QP,
      QC_mul_E12, E12_mul_QG, QG_mul_E21, E21_mul_QC, E12_mul_E21, E21_mul_E12, E12_mul_E12,
      E21_mul_E21, u0_mul_v0, smul_zero, add_zero, zero_add, smul_smul]
    module
  · simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      Qtype_mul_u0, Q_mul_u0 QW2_Qtype, Q_mul_u0 QC_Qtype, Q_mul_u0 QG_Qtype, Q_mul_u0 QP_Qtype,
      Q_mul_u0 (E12_mul_Q QG_Qtype), Q_mul_u0 (E21_mul_Q QC_Qtype),
      smul_zero, add_zero, smul_smul]
    module
  · simp only [Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      v0_mul_Qtype, v0_mul_Q Qtype_QW2, v0_mul_Q Qtype_QC, v0_mul_Q Qtype_QG, v0_mul_Q Qtype_QP,
      v0_mul_Q (Q_mul_E12 Qtype_QC), v0_mul_Q (Q_mul_E21 Qtype_QG),
      smul_zero, add_zero, smul_smul]
    module
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, v0_mul_u0, smul_smul]
    module

theorem toMat'_one : toMat' 1 = 1 := by
  rw [← Matrix.fromBlocks_one]
  simp only [toMat', Prod.fst_one, Prod.snd_one, Matrix.one_apply, Fin.isValue, ↓reduceIte,
    Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, one_smul, zero_smul]
  rw [Matrix.fromBlocks_inj]
  exact ⟨toMat_one, rfl, rfl, rfl⟩

/-- The unital algebra homomorphism `M₂(ℂ) × M₂(ℂ) × ℂ × ℂ →ₐ[ℂ] M_{E ⊕ ℂ}(ℂ)`. -/
noncomputable def toMatHom' : Coord' →ₐ[ℂ] Matrix Eplus Eplus ℂ where
  toFun := toMat'
  map_one' := toMat'_one
  map_mul' := toMat'_mul
  map_zero' := by
    rw [← Matrix.fromBlocks_zero]
    simp only [toMat', Prod.fst_zero, Prod.snd_zero, Matrix.zero_apply, zero_smul]
    rw [Matrix.fromBlocks_inj]
    exact ⟨toMat_zero, rfl, rfl, rfl⟩
  map_add' x y := by
    simp only [toMat', Prod.fst_add, Prod.snd_add, Matrix.add_apply]
    rw [Matrix.fromBlocks_add, Matrix.fromBlocks_inj]
    exact ⟨toMat_add (x.1 0 0, x.2.1, x.2.2.1, x.2.2.2) (y.1 0 0, y.2.1, y.2.2.1, y.2.2.2),
      add_smul _ _ _, add_smul _ _ _, add_smul _ _ _⟩
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Matrix.fromBlocks_one,
      Matrix.fromBlocks_smul, smul_zero, smul_zero]
    simp only [toMat', Prod.smul_fst, Prod.smul_snd, Prod.fst_one, Prod.snd_one,
      Matrix.smul_apply, Matrix.one_apply, Fin.isValue, ↓reduceIte, Fin.zero_eq_one_iff,
      Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, smul_zero, zero_smul]
    rw [Matrix.fromBlocks_inj]
    refine ⟨?_, rfl, rfl, by rw [smul_eq_mul, mul_one]⟩
    have h := toMat_smul c 1
    rw [toMat_one] at h
    exact h

theorem toMatHom'_apply (x : Coord') : toMatHom' x = toMat' x := rfl

/-! ### The left inverse -/

/-- Block coordinates on `M_{E ⊕ ℂ}(ℂ)`, a left inverse of `toMat'`. -/
noncomputable def coords' (Y : Matrix Eplus Eplus ℂ) : Coord' :=
  (!![(coords Y.toBlocks₁₁).1, Y.toBlocks₁₂ e01 (); 12 * Y.toBlocks₂₁ () e01, Y.toBlocks₂₂ () ()],
    (coords Y.toBlocks₁₁).2.1, (coords Y.toBlocks₁₁).2.2.1, (coords Y.toBlocks₁₁).2.2.2)

theorem coords'_toMat' (x : Coord') : coords' (toMat' x) = x := by
  obtain ⟨N, M, b, c⟩ := x
  simp only [coords', toMat', Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, coords_toMat, Matrix.smul_apply,
    u0, v0, smul_eq_mul, mul_one, Matrix.one_apply_eq]
  refine Prod.ext ?_ rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem toMat'_injective : Function.Injective toMat' :=
  Function.LeftInverse.injective coords'_toMat'

/-! ### Landing in the private-line commutant -/

theorem mem_privateLineCommutant {X : Matrix Eplus Eplus ℂ} :
    X ∈ privateLineCommutant ↔ ∀ σ : Equiv.Perm V, X * PmPlus σ = PmPlus σ * X := by
  rw [privateLineCommutant, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h σ
    exact (h (PmPlus σ) ⟨σ, rfl⟩).symm
  · rintro h _ ⟨σ, rfl⟩
    exact (h σ).symm

theorem toMat'_comm (x : Coord') (σ : Equiv.Perm V) :
    toMat' x * PmPlus σ = PmPlus σ * toMat' x := by
  simp only [toMat', PmPlus, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_zero, add_zero,
    zero_add, Pm_mul_u0, v0_mul_Pm, toMat_comm]

theorem toMat'_mem (x : Coord') : toMat' x ∈ privateLineCommutant :=
  mem_privateLineCommutant.mpr (toMat'_comm x)

/-- The homomorphism into the private-line commutant. -/
noncomputable def toCommutantHom' : Coord' →ₐ[ℂ] privateLineCommutant :=
  toMatHom'.codRestrict privateLineCommutant toMat'_mem

theorem toCommutantHom'_injective : Function.Injective toCommutantHom' := by
  intro x y h
  apply toMat'_injective
  exact congrArg Subtype.val h

/-! ### Surjectivity -/

theorem exists_toMat'_eq {X : Matrix Eplus Eplus ℂ} (hX : X ∈ privateLineCommutant) :
    ∃ x : Coord', toMat' x = X := by
  rw [mem_privateLineCommutant] at hX
  have hXe : X = Matrix.fromBlocks X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks X).symm
  set A := X.toBlocks₁₁
  set B := X.toBlocks₁₂
  set C := X.toBlocks₂₁
  set D := X.toBlocks₂₂
  have hblocks : ∀ σ : Equiv.Perm V,
      A * Pm σ = Pm σ * A ∧ B = Pm σ * B ∧ C * Pm σ = C := by
    intro σ
    have h := hX σ
    rw [hXe, PmPlus, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj] at h
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero,
      zero_add] at h
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hA : A ∈ degreeOneCommutant :=
    mem_degreeOneCommutant.mpr fun σ => (hblocks σ).1
  obtain ⟨x, hx⟩ := degreeOneCommutantEquiv.surjective ⟨A, hA⟩
  have hxA : toMat x = A := by
    rw [← degreeOneCommutantEquiv_apply, hx]
  have hB : B = B e01 () • u0 := column_invariant fun σ => ((hblocks σ).2.1).symm
  have hC : C = (12 * C () e01) • v0 := row_invariant fun σ => (hblocks σ).2.2
  have hD : D = D () () • (1 : Matrix Unit Unit ℂ) := by
    ext ⟨⟩ ⟨⟩
    simp
  refine ⟨(!![x.1, B e01 (); 12 * C () e01, D () ()], x.2.1, x.2.2.1, x.2.2.2), ?_⟩
  rw [hXe, toMat']
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]
  rw [Matrix.fromBlocks_inj]
  exact ⟨hxA, hB.symm, hC.symm, hD.symm⟩

theorem toCommutantHom'_surjective : Function.Surjective toCommutantHom' := by
  intro Y
  obtain ⟨x, hx⟩ := exists_toMat'_eq Y.2
  exact ⟨x, Subtype.ext hx⟩

/-- **`eq:degree-one-private-commutant`**: the relative commutant of the external
tetrahedral action on the degree-one carrier enlarged by one external-trivial private
contrast line is `M₂(ℂ) ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ` — the multiplicity algebras of the trivial
sector (type line and private line), `W ⊗ ℂ²`, `V₂`, `W ⊗ sgn` (multiplicities
`2, 2, 1, 1`). -/
noncomputable def privateLineCommutantEquiv : Coord' ≃ₐ[ℂ] privateLineCommutant :=
  AlgEquiv.ofBijective toCommutantHom' ⟨toCommutantHom'_injective, toCommutantHom'_surjective⟩

/-- The isomorphism sends `(N, M, b, c)` to the block matrix
`[[N₀₀ Qtype + M₀₀ QC + M₀₁ E12 + M₁₀ E21 + M₁₁ QG + b QW2 + c QP, N₀₁ u0], [N₁₀ v0, N₁₁]]`. -/
theorem privateLineCommutantEquiv_apply (x : Coord') :
    (privateLineCommutantEquiv x : Matrix Eplus Eplus ℂ) = toMat' x := rfl

theorem finrank_Coord' : finrank ℂ Coord' = 10 := by
  simp [Module.finrank_prod, Module.finrank_matrix]

/-- The private-line commutant has dimension exactly ten. -/
theorem finrank_privateLineCommutant : finrank ℂ privateLineCommutant = 10 := by
  rw [← privateLineCommutantEquiv.toLinearEquiv.finrank_eq, finrank_Coord']

end PrivateLineWedderburn
end RenewalGeometry
