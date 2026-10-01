/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.ReciprocalWedderburnKronecker
import RenewalGeometry.Commutant.JointTypedActionAlgebra
import RenewalGeometry.StandardModel.InternalSeedSaturationExact

/-!
# Clifford–tetrahedral compatibility and internal lift
  (`thm:clifford-tetrahedral-compatibility`)

Let `(e_ij)_{i,j ∈ Fin 4}` be matrix units for a unital represented Clifford factor
`𝒜_Cl ≅ M_4(ℂ)` (index `0` plays the role of the paper's `1`).

* `restrict_matrixUnits`: if `P_r` is a reducing carrier projection (`[P_r, e_ij] = 0`) and
  `E_r` an isometry onto `P_r ℋ`, the restrictions `E_r^* e_ij E_r` are matrix units on
  `P_r ℋ`; we then work on `P_r ℋ` with matrix units `e`.
* `reductionUnitary`: with `𝒱_r = e_00 P_r ℋ = Ran E` (`E^* E = 1`, `E E^* = e_00`), the map
  `𝒰_r(e_i ⊗ ξ) = e_{i0} ξ` (`eq:clifford-reduction-unitary`) is unitary
  (`reductionUnitary_conjTranspose_mul`, `reductionUnitary_mul_conjTranspose`) and
  `𝒰_r^* e_ij 𝒰_r = E_ij ⊗ I` (`reductionUnitary_conj_matrixUnit`), so
  `𝒜_Cl|_{P_r ℋ} = M_4(ℂ) ⊗ I` (`clifford_conj_eq`).
* `conj_eq_one_kron_of_commute`: an operator commuting with all `e_ij` is `I_4 ⊗ x̃` with
  `x̃ = E^* x E` its restriction to `𝒱_r`.
* `reducedRep`: the reduced representation `ρ_r(g) = E^* v_r(g) E`, a genuine unitary
  representation, with `v_r(g) = I_4 ⊗ ρ_r(g)` and `b_j = I_4 ⊗ b̃_j`, `[b̃_j, ρ_r(g)] = 0` and
  `C^*(b̃_j) ⊆ 𝒜_tet,r'` (`clifford_tetrahedral_reduction`, `eq:clifford-tetrahedral-lift`).
* `liftHom_image_extCommutant`: the lift `x̃ ↦ 𝒰_r (I ⊗ x̃) 𝒰_r^*` is a faithful unital algebra
  map carrying `𝒜_tet,r' = ρ_r(S_4)'` onto `𝒜_Cl' ∩ v_r(S_4)'`;
  `clifford_tetrahedral_internal_lift`: under the hypotheses of
  `thm:internal-seed-saturation` (`internal_seed_saturation_of_unitary`) the lift is a
  represented copy of `M_3(ℂ) ⊕ M_2(ℂ) ⊕ ℂ ⊕ ℂ` equal to `𝒜_Cl' ∩ v_r(S_4)'`.
* `clifford_tetrahedral_converse`: every tensor-factor realization satisfies
  `eq:clifford-tetrahedral-compatibility`.

The group `S_4` is any finite group `G` here (`Equiv.Perm (Fin 4)` is the case of the paper).
-/

open Matrix
open scoped Kronecker

namespace RenewalGeometry
namespace CliffordTetrahedral

set_option linter.unusedSectionVars false

/-- Matrix-unit relations for a family `e : Fin 4 → Fin 4 → M_n(ℂ)`. -/
structure IsMatrixUnits {n : Type*} [Fintype n] [DecidableEq n]
    (e : Fin 4 → Fin 4 → Matrix n n ℂ) : Prop where
  mul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0
  sum : ∑ i, e i i = 1
  adj : ∀ i j, (e i j)ᴴ = e j i

/-- **Restriction to a reducing projection.**  If `P` commutes with the matrix units `e` and
`E_r` is an isometry with `E_r E_r^* = P`, the compressions `E_r^* e_ij E_r` are matrix units on
`P ℋ`. -/
theorem restrict_matrixUnits {h n : Type*} [Fintype h] [DecidableEq h] [Fintype n]
    [DecidableEq n] (e : Fin 4 → Fin 4 → Matrix h h ℂ) (he : IsMatrixUnits e)
    (P : Matrix h h ℂ) (hP : ∀ i j, P * e i j = e i j * P) (Er : Matrix h n ℂ)
    (hEr1 : Erᴴ * Er = 1) (hEr2 : Er * Erᴴ = P) :
    IsMatrixUnits fun i j => Erᴴ * e i j * Er := by
  have hPE : P * Er = Er := by rw [← hEr2, Matrix.mul_assoc, hEr1, Matrix.mul_one]
  refine ⟨fun i j k l => ?_, ?_, fun i j => ?_⟩
  · calc Erᴴ * e i j * Er * (Erᴴ * e k l * Er) = Erᴴ * e i j * (Er * Erᴴ) * e k l * Er := by
          simp only [Matrix.mul_assoc]
      _ = Erᴴ * (e i j * e k l) * (P * Er) := by
          rw [hEr2, Matrix.mul_assoc (Erᴴ * e i j), hP k l]; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hPE, he.mul]
          split_ifs <;> simp
  · rw [← Matrix.sum_mul, ← Matrix.mul_sum, he.sum, Matrix.mul_one, hEr1]
  · rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, he.adj,
      Matrix.mul_assoc]

/-- Sums pass through the left Kronecker factor. -/
theorem sum_kronecker_left {κ a b c d : Type*} (s : Finset κ) (A : κ → Matrix a b ℂ)
    (B : Matrix c d ℂ) : (∑ k ∈ s, A k) ⊗ₖ B = ∑ k ∈ s, A k ⊗ₖ B := by
  ext p q
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

section Reduction

variable {n : Type} [Fintype n] [DecidableEq n] {J : Type} [Fintype J] [DecidableEq J]
variable (e : Fin 4 → Fin 4 → Matrix n n ℂ) (E : Matrix n J ℂ)

/-- **`eq:clifford-reduction-unitary`**: `𝒰_r(e_i ⊗ ξ) = e_{i0} ξ`, with `𝒱_r = Ran E`. -/
def reductionUnitary : Matrix n (Fin 4 × J) ℂ :=
  Matrix.of fun x p => (e p.1 0 * E) x p.2

variable {e E}

/-- Entries of `𝒰_r^* X 𝒰_r`. -/
theorem reductionUnitary_conj_apply (X : Matrix n n ℂ) (i : Fin 4) (a : J) (j : Fin 4) (b : J) :
    ((reductionUnitary e E)ᴴ * X * reductionUnitary e E) (i, a) (j, b) =
      ((e i 0 * E)ᴴ * X * (e j 0 * E)) a b := by
  simp only [Matrix.mul_apply, reductionUnitary, conjTranspose_apply, Matrix.of_apply,
    Finset.sum_mul]

/-- Cancellation of `I_4 ⊗ ·`. -/
theorem one_kron_cancel {x y : Matrix J J ℂ}
    (h : (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x = (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ y) : x = y := by
  ext a b
  have := congrFun (congrFun h (0, a)) (0, b)
  simpa [kroneckerMap_apply] using this

variable (he : IsMatrixUnits e) (hE1 : Eᴴ * E = 1) (hE2 : E * Eᴴ = e 0 0)
include he hE1 hE2

theorem e00_mul_E : e 0 0 * E = E := by
  rw [← hE2, Matrix.mul_assoc, hE1, Matrix.mul_one]

/-- Columns of `𝒰_r`: `(e_{i0} E)^* (e_{j0} E) = δ_ij`. -/
theorem col_inner (i j : Fin 4) : (e i 0 * E)ᴴ * (e j 0 * E) = if i = j then 1 else 0 := by
  rw [conjTranspose_mul, he.adj]
  calc Eᴴ * e 0 i * (e j 0 * E) = Eᴴ * (e 0 i * e j 0) * E := by simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [he.mul]
        split_ifs with h
        · rw [Matrix.mul_assoc, e00_mul_E he hE1 hE2, hE1]
        · simp

/-- `𝒰_r` is an isometry. -/
theorem reductionUnitary_conjTranspose_mul :
    (reductionUnitary e E)ᴴ * reductionUnitary e E = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have h := congrFun (congrFun (col_inner he hE1 hE2 i j) a) b
  rw [Matrix.mul_apply] at h ⊢
  simp only [reductionUnitary, conjTranspose_apply, Matrix.of_apply] at h ⊢
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply]
  · simp [hij]

/-- `𝒰_r` is onto: `𝒰_r 𝒰_r^* = ∑_i e_{i0} e_00 e_{0i} = ∑_i e_ii = I`. -/
theorem reductionUnitary_mul_conjTranspose :
    reductionUnitary e E * (reductionUnitary e E)ᴴ = 1 := by
  have hsum : reductionUnitary e E * (reductionUnitary e E)ᴴ =
      ∑ i, (e i 0 * E) * (e i 0 * E)ᴴ := by
    ext x y
    simp only [Matrix.mul_apply, reductionUnitary, conjTranspose_apply, Matrix.of_apply,
      Matrix.sum_apply, Fintype.sum_prod_type]
  rw [hsum, ← he.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_mul, he.adj]
  calc e i 0 * E * (Eᴴ * e 0 i) = e i 0 * (E * Eᴴ) * e 0 i := by simp only [Matrix.mul_assoc]
    _ = e i i := by rw [hE2, he.mul, if_pos rfl, he.mul, if_pos rfl]

/-- **`𝒜_Cl|_{P_r ℋ} = M_4(ℂ) ⊗ I`**: `𝒰_r^* e_kl 𝒰_r = E_kl ⊗ I`. -/
theorem reductionUnitary_conj_matrixUnit (k l : Fin 4) :
    (reductionUnitary e E)ᴴ * e k l * reductionUnitary e E =
      Matrix.single k l (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have hblock : (e i 0 * E)ᴴ * e k l * (e j 0 * E) =
      if i = k ∧ l = j then (1 : Matrix J J ℂ) else 0 := by
    rw [conjTranspose_mul, he.adj]
    calc Eᴴ * e 0 i * e k l * (e j 0 * E) = Eᴴ * (e 0 i * e k l * e j 0) * E := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [he.mul]
          by_cases hik : i = k
          · subst hik
            rw [if_pos rfl, he.mul]
            by_cases hlj : l = j
            · subst hlj
              rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, Matrix.mul_assoc, e00_mul_E he hE1 hE2, hE1]
            · rw [if_neg hlj, if_neg (fun h => hlj h.2)]
              simp
          · rw [if_neg hik, if_neg (fun h => hik h.1)]
            simp
  have h := congrFun (congrFun hblock a) b
  have hlhs := reductionUnitary_conj_apply (e := e) (E := E) (e k l) i a j b
  rw [hlhs, h, kroneckerMap_apply, Matrix.single_apply]
  by_cases hik : i = k
  · by_cases hlj : l = j
    · subst hik
      subst hlj
      simp
    · rw [if_neg (fun h => hlj h.2), if_neg (fun h => hlj h.2)]
      simp
  · rw [if_neg (fun h => hik h.1), if_neg (fun h => hik h.1.symm)]
    simp

/-- `U^* x U` for the reduction unitary, as a convenient rewriting form. -/
theorem conj_back (X : Matrix n n ℂ) :
    reductionUnitary e E * ((reductionUnitary e E)ᴴ * X * reductionUnitary e E) *
      (reductionUnitary e E)ᴴ = X := by
  calc reductionUnitary e E * ((reductionUnitary e E)ᴴ * X * reductionUnitary e E) *
        (reductionUnitary e E)ᴴ
      = (reductionUnitary e E * (reductionUnitary e E)ᴴ) * X *
          (reductionUnitary e E * (reductionUnitary e E)ᴴ) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [reductionUnitary_mul_conjTranspose he hE1 hE2, Matrix.one_mul, Matrix.mul_one]

/-- **`𝒜_Cl|_{P_r ℋ} = M_4(ℂ) ⊗ I`** in the reduction coordinates: for every
`a ∈ M_4(ℂ)`, `𝒰_r (a ⊗ I) 𝒰_r^* = ∑_{kl} a_kl e_kl`. -/
theorem clifford_conj_eq (a : Matrix (Fin 4) (Fin 4) ℂ) :
    reductionUnitary e E * (a ⊗ₖ (1 : Matrix J J ℂ)) * (reductionUnitary e E)ᴴ =
      ∑ k, ∑ l, a k l • e k l := by
  have ha : a ⊗ₖ (1 : Matrix J J ℂ) =
      ∑ k, ∑ l, a k l • (Matrix.single k l (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single a]
    simp only [sum_kronecker_left, ← Matrix.smul_kronecker, Matrix.smul_single, smul_eq_mul,
      mul_one]
  rw [ha, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, ← reductionUnitary_conj_matrixUnit he hE1 hE2 k l,
    conj_back he hE1 hE2]

/-- An operator commuting with all `e_ij` commutes, in the reduction coordinates, with the whole
factor `M_4(ℂ) ⊗ I`. -/
theorem conj_commute_kron_of_commute (X : Matrix n n ℂ)
    (hX : ∀ i j, X * e i j = e i j * X) (g : Matrix (Fin 4) (Fin 4) ℂ) :
    (g ⊗ₖ (1 : Matrix J J ℂ)) * ((reductionUnitary e E)ᴴ * X * reductionUnitary e E) =
      ((reductionUnitary e E)ᴴ * X * reductionUnitary e E) * (g ⊗ₖ (1 : Matrix J J ℂ)) := by
  set U := reductionUnitary e E with hU
  have hUU : Uᴴ * U = 1 := reductionUnitary_conjTranspose_mul he hE1 hE2
  have hunit : ∀ k l, (Matrix.single k l (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * (Uᴴ * X * U) =
      (Uᴴ * X * U) * (Matrix.single k l (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) := by
    intro k l
    rw [← reductionUnitary_conj_matrixUnit he hE1 hE2 k l]
    calc Uᴴ * e k l * U * (Uᴴ * X * U) = Uᴴ * (e k l * (U * Uᴴ) * X) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * (X * (U * Uᴴ) * e k l) * U := by
          rw [reductionUnitary_mul_conjTranspose he hE1 hE2, Matrix.mul_one, Matrix.mul_one,
            hX k l]
      _ = Uᴴ * X * U * (Uᴴ * e k l * U) := by simp only [Matrix.mul_assoc]
  rw [Matrix.matrix_eq_sum_single g]
  simp only [sum_kronecker_left, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hs : Matrix.single k l (g k l) = g k l • Matrix.single k l (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs, Matrix.smul_kronecker, Matrix.smul_mul, Matrix.mul_smul, hunit]

/-- **Factorization of the Clifford commutant.**  An operator commuting with every `e_ij` is
`I_4 ⊗ x̃` in the reduction coordinates, with `x̃ = E^* X E` its restriction to `𝒱_r`. -/
theorem conj_eq_one_kron_of_commute (X : Matrix n n ℂ) (hX : ∀ i j, X * e i j = e i j * X) :
    (reductionUnitary e E)ᴴ * X * reductionUnitary e E =
      (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ (Eᴴ * X * E) := by
  obtain ⟨B, hB⟩ := NCG.CommonOrigin.left_factor_commutant _
    (conj_commute_kron_of_commute he hE1 hE2 X hX)
  have hBid : B = Eᴴ * X * E := by
    ext a b
    have h := congrFun (congrFun hB (0, a)) (0, b)
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul] at h
    rw [← h, reductionUnitary_conj_apply, e00_mul_E he hE1 hE2]
  rw [hB, hBid]

/-- The operator reconstructed from its restriction: `X = 𝒰_r (I ⊗ E^* X E) 𝒰_r^*`. -/
theorem eq_conj_one_kron_of_commute (X : Matrix n n ℂ) (hX : ∀ i j, X * e i j = e i j * X) :
    X = reductionUnitary e E * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ (Eᴴ * X * E)) *
      (reductionUnitary e E)ᴴ := by
  rw [← conj_eq_one_kron_of_commute he hE1 hE2 X hX, conj_back he hE1 hE2]

end Reduction

/-! ### The lift and the reduced representation -/

section Lift

variable {J : Type} [Fintype J] [DecidableEq J]

/-- `x ↦ I_4 ⊗ x` as a unital algebra map. -/
def oneKronHom : Matrix J J ℂ →ₐ[ℂ] Matrix (Fin 4 × J) (Fin 4 × J) ℂ where
  toFun x := (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x
  map_one' := Matrix.one_kronecker_one
  map_mul' x y := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.kronecker_zero _
  map_add' x y := Matrix.kronecker_add _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul, Matrix.one_kronecker_one]

theorem oneKronHom_injective : Function.Injective (oneKronHom (J := J)) := by
  intro x y hxy
  exact one_kron_cancel hxy

end Lift

section Representation

variable {n : Type} [Fintype n] [DecidableEq n] {J : Type} [Fintype J] [DecidableEq J]
variable {e : Fin 4 → Fin 4 → Matrix n n ℂ} {E : Matrix n J ℂ}
variable (he : IsMatrixUnits e) (hE1 : Eᴴ * E = 1) (hE2 : E * Eᴴ = e 0 0)
variable {G : Type} [Group G]

/-- The lift `x̃ ↦ 𝒰_r (I_4 ⊗ x̃) 𝒰_r^*`, a unital algebra map `B(𝒱_r) → B(P_r ℋ)`. -/
def liftHom : Matrix J J ℂ →ₐ[ℂ] Matrix n n ℂ :=
  (InternalSeedSaturation.conjHom (reductionUnitary e E)
      (reductionUnitary_conjTranspose_mul he hE1 hE2)
      (reductionUnitary_mul_conjTranspose he hE1 hE2)).comp oneKronHom

theorem liftHom_apply (x : Matrix J J ℂ) :
    liftHom he hE1 hE2 x = reductionUnitary e E * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x) *
      (reductionUnitary e E)ᴴ := by
  simp only [liftHom, AlgHom.comp_apply, InternalSeedSaturation.conjHom_apply]
  rfl

theorem liftHom_injective : Function.Injective (liftHom he hE1 hE2) :=
  (InternalSeedSaturation.conjHom_injective _ (reductionUnitary_conjTranspose_mul he hE1 hE2)
    (reductionUnitary_mul_conjTranspose he hE1 hE2)).comp oneKronHom_injective

include he hE1 hE2 in
/-- Restriction of a lifted operator. -/
theorem restrict_liftHom (x : Matrix J J ℂ) : Eᴴ * liftHom he hE1 hE2 x * E = x := by
  have hX : ∀ i j, liftHom he hE1 hE2 x * e i j = e i j * liftHom he hE1 hE2 x := by
    intro i j
    have hc := NCG.CommonOrigin.kron_right_commutes (Matrix.single i j (1 : ℂ)) x
    rw [liftHom_apply, ← conj_back he hE1 hE2 (e i j),
      reductionUnitary_conj_matrixUnit he hE1 hE2 i j]
    set U := reductionUnitary e E
    have hUU : Uᴴ * U = 1 := reductionUnitary_conjTranspose_mul he hE1 hE2
    calc U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x) * Uᴴ *
          (U * (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * Uᴴ)
        = U * (((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x) * (Uᴴ * U) *
            (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * ((Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * (Uᴴ * U) *
            ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x)) * Uᴴ := by
          rw [hUU, Matrix.mul_one, Matrix.mul_one, hc]
      _ = U * (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * Uᴴ *
            (U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x) * Uᴴ) := by
          simp only [Matrix.mul_assoc]
  have h := conj_eq_one_kron_of_commute he hE1 hE2 _ hX
  rw [liftHom_apply] at h
  set U := reductionUnitary e E
  have hUU : Uᴴ * U = 1 := reductionUnitary_conjTranspose_mul he hE1 hE2
  have h' : (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x =
      (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ
        (Eᴴ * (U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x) * Uᴴ) * E) := by
    rw [← h]
    calc (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x
        = (Uᴴ * U) * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x) * (Uᴴ * U) := by
          rw [hUU, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [liftHom_apply]
  exact (one_kron_cancel h').symm

include he hE1 hE2 in
/-- Every operator commuting with all `e_ij` is a lift: `X = lift(E^* X E)`. -/
theorem eq_liftHom_of_commute (X : Matrix n n ℂ) (hX : ∀ i j, X * e i j = e i j * X) :
    X = liftHom he hE1 hE2 (Eᴴ * X * E) := by
  rw [liftHom_apply]
  exact eq_conj_one_kron_of_commute he hE1 hE2 X hX

include he hE1 hE2 in
/-- Lifts commute with the Clifford matrix units. -/
theorem liftHom_commute_matrixUnit (x : Matrix J J ℂ) (i j : Fin 4) :
    liftHom he hE1 hE2 x * e i j = e i j * liftHom he hE1 hE2 x := by
  have hc := NCG.CommonOrigin.kron_right_commutes (Matrix.single i j (1 : ℂ)) x
  rw [← conj_back he hE1 hE2 (e i j), reductionUnitary_conj_matrixUnit he hE1 hE2 i j,
    liftHom_apply]
  set U := reductionUnitary e E
  have hUU : Uᴴ * U = 1 := reductionUnitary_conjTranspose_mul he hE1 hE2
  calc U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x) * Uᴴ *
        (U * (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * Uᴴ)
      = U * (((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x) * (Uᴴ * U) *
          (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ))) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * ((Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * (Uᴴ * U) *
          ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x)) * Uᴴ := by
        rw [hUU, Matrix.mul_one, Matrix.mul_one, hc]
    _ = U * (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * Uᴴ *
          (U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ x) * Uᴴ) := by
        simp only [Matrix.mul_assoc]

/-- The reduced representation `ρ_r(g) = E^* v_r(g) E` on `𝒱_r`. -/
def reducedRep (v : G →* Matrix n n ℂ) (hv : ∀ g i j, v g * e i j = e i j * v g) :
    G →* Matrix J J ℂ where
  toFun g := Eᴴ * v g * E
  map_one' := by rw [map_one, Matrix.mul_one, hE1]
  map_mul' g h := by
    apply liftHom_injective he hE1 hE2
    show liftHom he hE1 hE2 (Eᴴ * v (g * h) * E) =
      liftHom he hE1 hE2 ((Eᴴ * v g * E) * (Eᴴ * v h * E))
    rw [map_mul (liftHom he hE1 hE2), ← eq_liftHom_of_commute he hE1 hE2 _ (hv g),
      ← eq_liftHom_of_commute he hE1 hE2 _ (hv h),
      ← eq_liftHom_of_commute he hE1 hE2 _ (hv (g * h)), map_mul]

theorem reducedRep_apply (v : G →* Matrix n n ℂ) (hv : ∀ g i j, v g * e i j = e i j * v g)
    (g : G) : reducedRep he hE1 hE2 v hv g = Eᴴ * v g * E := rfl

/-- The reduced representation is unitary. -/
theorem reducedRep_unitary (v : G →* Matrix n n ℂ) (hv : ∀ g i j, v g * e i j = e i j * v g)
    (hvu : ∀ g, (v g)ᴴ = v g⁻¹) (g : G) :
    (reducedRep he hE1 hE2 v hv g)ᴴ = reducedRep he hE1 hE2 v hv g⁻¹ := by
  rw [reducedRep_apply, reducedRep_apply, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, hvu, Matrix.mul_assoc]

/-- An element commuting with every `ρ_r(g)` lies in `𝒜_tet,r' = C^*(ρ_r(G))'`. -/
theorem mem_extCommutant_of_commute (ρ : G →* Matrix J J ℂ) (x : Matrix J J ℂ)
    (hx : ∀ g, x * ρ g = ρ g * x) : x ∈ InternalSeedSaturation.extCommutant ρ := by
  rw [InternalSeedSaturation.extCommutant, Subalgebra.mem_centralizer_iff]
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact (hx g).symm
  | algebraMap r => exact Algebra.commutes r x
  | add y z _ _ hy hz => rw [add_mul, mul_add, hy, hz]
  | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]

/-- **`eq:clifford-tetrahedral-lift`.**  Under `eq:clifford-tetrahedral-compatibility`:
`v_r(g) = 𝒰_r (I_4 ⊗ ρ_r(g)) 𝒰_r^*` with `ρ_r` a genuine unitary representation,
`b_j = 𝒰_r (I_4 ⊗ b̃_j) 𝒰_r^*`, `[b̃_j, ρ_r(g)] = 0`, and `C^*(b̃_j) ⊆ 𝒜_tet,r'`. -/
theorem clifford_tetrahedral_reduction {β : Type*} (v : G →* Matrix n n ℂ)
    (hvu : ∀ g, (v g)ᴴ = v g⁻¹) (hv : ∀ g i j, v g * e i j = e i j * v g)
    (b : β → Matrix n n ℂ) (hbe : ∀ k i j, b k * e i j = e i j * b k)
    (hbv : ∀ k g, b k * v g = v g * b k) :
    (∀ g, v g = liftHom he hE1 hE2 (reducedRep he hE1 hE2 v hv g)) ∧
    (∀ g, (reducedRep he hE1 hE2 v hv g)ᴴ = reducedRep he hE1 hE2 v hv g⁻¹) ∧
    (∀ k, b k = liftHom he hE1 hE2 (Eᴴ * b k * E)) ∧
    (∀ k g, (Eᴴ * b k * E) * reducedRep he hE1 hE2 v hv g =
      reducedRep he hE1 hE2 v hv g * (Eᴴ * b k * E)) ∧
    starAdjoin (Set.range fun k => Eᴴ * b k * E) ≤
      InternalSeedSaturation.extCommutant (reducedRep he hE1 hE2 v hv) := by
  have hcomm : ∀ k g, (Eᴴ * b k * E) * reducedRep he hE1 hE2 v hv g =
      reducedRep he hE1 hE2 v hv g * (Eᴴ * b k * E) := by
    intro k g
    apply liftHom_injective he hE1 hE2
    rw [map_mul, map_mul, reducedRep_apply, ← eq_liftHom_of_commute he hE1 hE2 _ (hbe k),
      ← eq_liftHom_of_commute he hE1 hE2 _ (hv g), hbv]
  refine ⟨fun g => eq_liftHom_of_commute he hE1 hE2 _ (hv g),
    reducedRep_unitary he hE1 hE2 v hv hvu, fun k => eq_liftHom_of_commute he hE1 hE2 _ (hbe k),
    hcomm, ?_⟩
  -- the centralizer of `ρ_r(G)` is a star-closed subalgebra containing the reduced bank
  set ρ := reducedRep he hE1 hE2 v hv
  let C : Subalgebra ℂ (Matrix J J ℂ) := Subalgebra.centralizer ℂ (Set.range ρ)
  have hC : ∀ x ∈ C, xᴴ ∈ C := by
    intro x hx
    rw [Subalgebra.mem_centralizer_iff] at hx ⊢
    rintro _ ⟨g, rfl⟩
    have h := hx _ ⟨g⁻¹, rfl⟩
    have h' := congrArg conjTranspose h
    rw [conjTranspose_mul, conjTranspose_mul, ← reducedRep_unitary he hE1 hE2 v hv hvu,
      conjTranspose_conjTranspose] at h'
    exact h'.symm
  have hle : starAdjoin (Set.range fun k => Eᴴ * b k * E) ≤ C := by
    refine starAdjoin_le hC ?_
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    exact (hcomm k g).symm
  intro x hx
  apply mem_extCommutant_of_commute
  intro g
  have := (Subalgebra.mem_centralizer_iff ℂ).mp (hle hx) _ ⟨g, rfl⟩
  exact this.symm

/-- **The lift identifies `𝒜_tet,r'` with `𝒜_Cl' ∩ v_r(G)'`**: the lift maps the relative
commutant `C^*(ρ_r(G))'` on `𝒱_r` exactly onto the operators on `P_r ℋ` commuting with all
`e_ij` and all `v_r(g)`. -/
theorem liftHom_image_extCommutant (v : G →* Matrix n n ℂ)
    (hv : ∀ g i j, v g * e i j = e i j * v g) :
    liftHom he hE1 hE2 '' (InternalSeedSaturation.extCommutant (reducedRep he hE1 hE2 v hv) :
        Set (Matrix J J ℂ)) =
      {X | (∀ i j, X * e i j = e i j * X) ∧ ∀ g, X * v g = v g * X} := by
  ext X
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨liftHom_commute_matrixUnit he hE1 hE2 x, fun g => ?_⟩
    rw [eq_liftHom_of_commute he hE1 hE2 _ (hv g), ← map_mul, ← map_mul]
    congr 1
    rw [SetLike.mem_coe, InternalSeedSaturation.extCommutant,
      Subalgebra.mem_centralizer_iff] at hx
    exact (hx _ (Algebra.subset_adjoin ⟨g, rfl⟩)).symm
  · rintro ⟨hXe, hXv⟩
    refine ⟨Eᴴ * X * E, ?_, (eq_liftHom_of_commute he hE1 hE2 X hXe).symm⟩
    apply mem_extCommutant_of_commute
    intro g
    apply liftHom_injective he hE1 hE2
    rw [map_mul, map_mul, ← eq_liftHom_of_commute he hE1 hE2 X hXe, reducedRep_apply,
      ← eq_liftHom_of_commute he hE1 hE2 _ (hv g), hXv]

include he hE1 hE2 in
open InternalAssembly InternalDeficit in
/-- **Internal lift (`thm:clifford-tetrahedral-compatibility`, saturation clause).**  If the
reduced bank on `𝒱_r` satisfies the hypotheses of `thm:internal-seed-saturation` (census
`(3, 2, 1, 1)` and (I1)–(I4), as in `internal_seed_saturation_of_unitary`), its lift is a
represented copy of `M_3(ℂ) ⊕ M_2(ℂ) ⊕ ℂ ⊕ ℂ` inside `P_r ℋ`, generated by the lifted words
and equal to `𝒜_Cl' ∩ v_r(G)'`. -/
theorem clifford_tetrahedral_internal_lift [Fintype G] (v : G →* Matrix n n ℂ)
    (hvu : ∀ g, (v g)ᴴ = v g⁻¹) (hv : ∀ g i j, v g * e i j = e i j * v g) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (I K : ι → Type)
      (_ : ∀ b, Fintype (I b)) (_ : ∀ b, DecidableEq (I b))
      (_ : ∀ b, Fintype (K b)) (_ : ∀ b, DecidableEq (K b))
      (W : Matrix J (Σ b, I b × K b) ℂ),
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      ∀ (κ : ι ≃ Fin 4), (∀ k, Fintype.card (K (κ.symm k)) = ![3, 2, 1, 1] k) →
        ∀ {u : Matrix (Fin 7) (Fin 7) ℂ},
          (ColourSupported u ∧ 0 < omega7 u) ∨ InternalSeedSaturation.ReciprocalBridge u →
          ∀ {h : Fin 7 → ℂ}, Router h →
          ∃ Ψ : blockAlgebra →ₐ[ℂ] Matrix n n ℂ,
            Function.Injective Ψ ∧
            Set.range Ψ = {X | (∀ i j, X * e i j = e i j * X) ∧ ∀ g, X * v g = v g * X} ∧
            Algebra.adjoin ℂ (Ψ '' (Subtype.val ⁻¹' (baseGens ∪ bridgeGens u ∪ routerGen h))) =
              Algebra.adjoin ℂ (Set.range Ψ) := by
  set ρ := reducedRep he hE1 hE2 v hv
  obtain ⟨ι, _, _, I, K, _, _, _, _, W, hW1, hW2, -, -, -, hsat⟩ :=
    InternalSeedSaturation.internal_seed_saturation_of_unitary ρ
      (reducedRep_unitary he hE1 hE2 v hv hvu)
  refine ⟨ι, inferInstance, inferInstance, I, K, inferInstance, inferInstance, inferInstance,
    inferInstance, W, hW1, hW2, ?_⟩
  intro κ hcard u hI1 h hr
  obtain ⟨Φ, hgen, -⟩ := hsat κ hcard hI1 hr
  let Ψ : blockAlgebra →ₐ[ℂ] Matrix n n ℂ :=
    (liftHom he hE1 hE2).comp ((InternalSeedSaturation.extCommutant ρ).val.comp Φ.toAlgHom)
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    have h1 := liftHom_injective he hE1 hE2 hxy
    exact Φ.injective (Subtype.ext h1)
  have hrange : Set.range Ψ =
      liftHom he hE1 hE2 '' (InternalSeedSaturation.extCommutant ρ : Set (Matrix J J ℂ)) := by
    ext X
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(Φ x : Matrix J J ℂ), (Φ x).2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Φ.symm ⟨y, hy⟩, ?_⟩
      simp [Ψ]
  refine ⟨Ψ, hΨinj, by rw [hrange, liftHom_image_extCommutant], ?_⟩
  -- the lifted words generate the lifted algebra
  have himage : Ψ '' (Subtype.val ⁻¹' (baseGens ∪ bridgeGens u ∪ routerGen h)) =
      liftHom he hE1 hE2 '' (((InternalSeedSaturation.extCommutant ρ).val.comp Φ.toAlgHom) ''
        (Subtype.val ⁻¹' (baseGens ∪ bridgeGens u ∪ routerGen h))) := by
    rw [Set.image_image]
    rfl
  rw [himage, ← AlgHom.map_adjoin, hgen]
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subalgebra.mem_map.mp hx
    exact Algebra.subset_adjoin ⟨Φ.symm ⟨y, hy⟩, by simp [Ψ]⟩
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact Subalgebra.mem_map.mpr ⟨Φ x, (Φ x).2, rfl⟩

end Representation

/-! ### The converse -/

/-- **Converse (`thm:clifford-tetrahedral-compatibility`).**  Any tensor-factor realization
`e_ij = 𝒰 (E_ij ⊗ I) 𝒰^*`, `v(g) = 𝒰 (I ⊗ ρ(g)) 𝒰^*`, `b_k = 𝒰 (I ⊗ b̃_k) 𝒰^*` with
`[b̃_k, ρ(g)] = 0` and `𝒰` unitary satisfies `eq:clifford-tetrahedral-compatibility`. -/
theorem clifford_tetrahedral_converse {n J G β : Type*} [Fintype n] [DecidableEq n] [Fintype J]
    [DecidableEq J] (U : Matrix n (Fin 4 × J) ℂ) (hU : Uᴴ * U = 1)
    (ρ : G → Matrix J J ℂ) (bt : β → Matrix J J ℂ) (hbt : ∀ k g, bt k * ρ g = ρ g * bt k) :
    (∀ (g : G) (i j : Fin 4), U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ ρ g) * Uᴴ *
        (U * (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * Uᴴ) =
      U * (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * Uᴴ *
        (U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ ρ g) * Uᴴ)) ∧
    (∀ (k : β) (i j : Fin 4), U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ bt k) * Uᴴ *
        (U * (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * Uᴴ) =
      U * (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * Uᴴ *
        (U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ bt k) * Uᴴ)) ∧
    (∀ (k : β) (g : G), U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ bt k) * Uᴴ *
        (U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ ρ g) * Uᴴ) =
      U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ ρ g) * Uᴴ *
        (U * ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ bt k) * Uᴴ)) := by
  have key : ∀ A B : Matrix (Fin 4 × J) (Fin 4 × J) ℂ, A * B = B * A →
      U * A * Uᴴ * (U * B * Uᴴ) = U * B * Uᴴ * (U * A * Uᴴ) := by
    intro A B hAB
    calc U * A * Uᴴ * (U * B * Uᴴ) = U * (A * (Uᴴ * U) * B) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * (B * (Uᴴ * U) * A) * Uᴴ := by rw [hU, Matrix.mul_one, Matrix.mul_one, hAB]
      _ = U * B * Uᴴ * (U * A * Uᴴ) := by simp only [Matrix.mul_assoc]
  refine ⟨fun g i j => key _ _ (NCG.CommonOrigin.kron_right_commutes _ _).symm,
    fun k i j => key _ _ (NCG.CommonOrigin.kron_right_commutes _ _).symm,
    fun k g => key _ _ ?_⟩
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hbt]

/-! ### Assembly -/

section Assembly

variable {n : Type} [Fintype n] [DecidableEq n] {e : Fin 4 → Fin 4 → Matrix n n ℂ}

/-- `𝒰_r(e_i ⊗ ξ_a) = e_{i0} ξ_a` for the orthonormal basis `ξ_a = E e_a` of `𝒱_r`
(`eq:clifford-reduction-unitary`). -/
theorem reductionUnitary_mulVec_basis {J : Type} [Fintype J] [DecidableEq J] (E : Matrix n J ℂ)
    (i : Fin 4) (a : J) :
    reductionUnitary e E *ᵥ Pi.single (i, a) 1 = e i 0 *ᵥ (E.col a) := by
  rw [Matrix.mulVec_single_one]
  ext x
  simp [reductionUnitary, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]

/-- `𝒱_r = e_00 P_r ℋ` has an orthonormal basis: an isometry `E` with `E E^* = e_00`. -/
theorem exists_reduction_isometry (he : IsMatrixUnits e) :
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (E : Matrix n J ℂ),
      Eᴴ * E = 1 ∧ E * Eᴴ = e 0 0 :=
  projection_factor (e 0 0) (he.adj 0 0) (by rw [he.mul, if_pos rfl])

/-- **Clifford–tetrahedral compatibility (`thm:clifford-tetrahedral-compatibility`).**  Let
`(e_ij)` be matrix units of the represented Clifford factor on the reduced carrier `P_r ℋ`
(`restrict_matrixUnits` produces them from a reducing projection), `v_r` a genuine unitary
representation and `(b_k)` a bank satisfying `eq:clifford-tetrahedral-compatibility`.  Then
there are an orthonormal basis `E` of `𝒱_r = e_00 P_r ℋ` and the unitary
`𝒰_r(e_i ⊗ ξ) = e_{i0} ξ` such that `𝒜_Cl|_{P_r ℋ} = M_4(ℂ) ⊗ I`, `v_r(g) = I_4 ⊗ ρ_r(g)` with
`ρ_r` a genuine unitary representation, `b_k = I_4 ⊗ b̃_k`, `[b̃_k, ρ_r(g)] = 0`,
`C^*(b̃_k) ⊆ 𝒜_tet,r'`, and the lift identifies `𝒜_tet,r'` with `𝒜_Cl' ∩ v_r(G)'`
(`eq:clifford-tetrahedral-lift`). -/
theorem clifford_tetrahedral_compatibility (he : IsMatrixUnits e) {G : Type} [Group G]
    {β : Type*} (v : G →* Matrix n n ℂ) (hvu : ∀ g, (v g)ᴴ = v g⁻¹)
    (hv : ∀ g i j, v g * e i j = e i j * v g)
    (b : β → Matrix n n ℂ) (hbe : ∀ k i j, b k * e i j = e i j * b k)
    (hbv : ∀ k g, b k * v g = v g * b k) :
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (E : Matrix n J ℂ)
      (hE1 : Eᴴ * E = 1) (hE2 : E * Eᴴ = e 0 0),
      (reductionUnitary e E)ᴴ * reductionUnitary e E = 1 ∧
      reductionUnitary e E * (reductionUnitary e E)ᴴ = 1 ∧
      (∀ i a, reductionUnitary e E *ᵥ Pi.single (i, a) 1 = e i 0 *ᵥ (E.col a)) ∧
      (∀ k l, (reductionUnitary e E)ᴴ * e k l * reductionUnitary e E =
        Matrix.single k l (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) ∧
      (∀ a : Matrix (Fin 4) (Fin 4) ℂ,
        reductionUnitary e E * (a ⊗ₖ (1 : Matrix J J ℂ)) * (reductionUnitary e E)ᴴ =
          ∑ k, ∑ l, a k l • e k l) ∧
      (∀ g, v g = liftHom he hE1 hE2 (reducedRep he hE1 hE2 v hv g)) ∧
      (∀ g, (reducedRep he hE1 hE2 v hv g)ᴴ = reducedRep he hE1 hE2 v hv g⁻¹) ∧
      (∀ k, b k = liftHom he hE1 hE2 (Eᴴ * b k * E)) ∧
      (∀ k g, (Eᴴ * b k * E) * reducedRep he hE1 hE2 v hv g =
        reducedRep he hE1 hE2 v hv g * (Eᴴ * b k * E)) ∧
      starAdjoin (Set.range fun k => Eᴴ * b k * E) ≤
        InternalSeedSaturation.extCommutant (reducedRep he hE1 hE2 v hv) ∧
      liftHom he hE1 hE2 '' (InternalSeedSaturation.extCommutant (reducedRep he hE1 hE2 v hv) :
          Set (Matrix J J ℂ)) =
        {X | (∀ i j, X * e i j = e i j * X) ∧ ∀ g, X * v g = v g * X} := by
  obtain ⟨J, _, _, E, hE1, hE2⟩ := exists_reduction_isometry he
  obtain ⟨h1, h2, h3, h4, h5⟩ := clifford_tetrahedral_reduction he hE1 hE2 v hvu hv b hbe hbv
  exact ⟨J, inferInstance, inferInstance, E, hE1, hE2,
    reductionUnitary_conjTranspose_mul he hE1 hE2, reductionUnitary_mul_conjTranspose he hE1 hE2,
    reductionUnitary_mulVec_basis E, reductionUnitary_conj_matrixUnit he hE1 hE2,
    clifford_conj_eq he hE1 hE2, h1, h2, h3, h4, h5, liftHom_image_extCommutant he hE1 hE2 v hv⟩

end Assembly

end CliffordTetrahedral
end RenewalGeometry
