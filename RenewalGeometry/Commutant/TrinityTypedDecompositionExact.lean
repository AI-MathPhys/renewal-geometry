/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.ReciprocalWedderburnKronecker
import RenewalGeometry.Commutant.JointTypedActionAlgebra
import RenewalGeometry.Commutant.ArbitraryIncidenceDualityExact

/-!
# Factor obstruction and typed decomposition for a general `M_n(ℂ)` (`thm:trinity`)

Let a unital `*`-copy `φ : M_n(ℂ) → B(ℋ)` of `M_n(ℂ)` act on a finite Hilbert space `ℋ`
(`n ≥ 1`), and let `𝒜_type` be a commuting unital finite-dimensional `C^*`-algebra.

* `factor_commutant` (`eq:factor-commutant`): there is a unitary `U : ℂⁿ ⊗ 𝒦 → ℋ` with
  `φ(X) = U (X ⊗ I) U^*`, and `M_n(ℂ)' = U (I_n ⊗ B(𝒦)) U^*`;
* `trinity_typed_decomposition` (`eq:trinity-H`, `eq:trinity-Aint`, `eq:trinity-C`,
  `eq:trinity-Cprime`): there are a finite sector set `Λ`, spaces `V_λ = ℂ^{I λ}`,
  `M_λ = ℂ^{J λ}` and a unitary `T : ℂⁿ ⊗ (⊕_λ V_λ ⊗ M_λ) → ℋ` with
  `φ(X) = T (X ⊗ I) T^*`, `𝒜_type = T (I_n ⊗ ⊕_λ B(V_λ) ⊗ I_{M_λ}) T^*`,
  `𝒞 = C^*(φ(M_n), 𝒜_type) = T (M_n(ℂ) ⊗ ⊕_λ B(V_λ) ⊗ I_{M_λ}) T^*`, and
  `𝒞' = T (I_n ⊗ ⊕_λ I_{V_λ} ⊗ B(M_λ)) T^*`.

The carrier `ℂⁿ ⊗ (⊕_λ V_λ ⊗ M_λ)` is canonically `⊕_λ ℂⁿ ⊗ V_λ ⊗ M_λ` (distributivity of
`⊗` over `⊕`), under which `I_n ⊗ ⊕_λ B(V_λ) ⊗ I = ⊕_λ I_n ⊗ B(V_λ) ⊗ I`,
`M_n ⊗ ⊕_λ B(V_λ) ⊗ I = ⊕_λ B(ℂⁿ ⊗ V_λ) ⊗ I` and `I_n ⊗ ⊕_λ I ⊗ B(M_λ) = ⊕_λ I ⊗ B(M_λ)`;
these canonical identifications are not spelled out as a reindexing.  The obstruction
clause is `factor_obstruction`: `I_m ⊗ B(𝒦)` has trivial centre, so an internal algebra with
a non-scalar central element is not the full commutant.

Method: the matrix units `e_ij = φ(E_ij)` give the reduction unitary `𝒰(e_i ⊗ ξ) = e_{i0} ξ`
(general-`n` version of the Clifford reduction); the commuting algebra is `I ⊗ 𝒜'` for a
star-closed `𝒜' ⊆ B(𝒦)`; the Wedderburn–Kronecker theorem (`reciprocal_wedderburn`) applied
to `𝒜'` gives `V_λ, M_λ`; the commutant is computed directly and `𝒞` by the finite double
commutant theorem.
-/

open Matrix
open scoped Kronecker

namespace RenewalGeometry
namespace TrinityDecomposition

set_option linter.unusedSectionVars false

/-! ### Matrix units of a `*`-copy of `M_m(ℂ)` -/

/-- Matrix-unit relations for a family `e : Fin m → Fin m → M_h(ℂ)`. -/
structure IsMatUnits {m : ℕ} {h : Type*} [Fintype h] [DecidableEq h]
    (e : Fin m → Fin m → Matrix h h ℂ) : Prop where
  mul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0
  sum : ∑ i, e i i = 1
  adj : ∀ i j, (e i j)ᴴ = e j i

/-- The matrix units `φ(E_ij)` of a unital `*`-copy of `M_m(ℂ)`. -/
theorem isMatUnits_of_starHom {m : ℕ} {h : Type*} [Fintype h] [DecidableEq h]
    (φ : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix h h ℂ) (hφ : ∀ X, φ Xᴴ = (φ X)ᴴ) :
    IsMatUnits fun i j => φ (Matrix.single i j 1) := by
  refine ⟨fun i j k l => ?_, ?_, fun i j => ?_⟩
  · rw [← map_mul]
    split_ifs with h
    · rw [h, Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
  · rw [← map_sum, Matrix.sum_single_one, map_one]
  · rw [← hφ, Matrix.conjTranspose_single, star_one]

/-! ### The reduction unitary for general `m` -/

section Reduction

variable {m : ℕ} [NeZero m]
variable {h : Type} [Fintype h] [DecidableEq h] {J : Type} [Fintype J] [DecidableEq J]
variable (e : Fin m → Fin m → Matrix h h ℂ) (E : Matrix h J ℂ)

/-- `𝒰(e_i ⊗ ξ) = e_{i0} ξ`, with `Ran E = e₀₀ ℋ`. -/
def reductionU : Matrix h (Fin m × J) ℂ :=
  Matrix.of fun x p => (e p.1 0 * E) x p.2

variable {e E}

theorem reductionU_conj_apply (X : Matrix h h ℂ) (i : Fin m) (a : J) (j : Fin m) (b : J) :
    ((reductionU e E)ᴴ * X * reductionU e E) (i, a) (j, b) =
      ((e i 0 * E)ᴴ * X * (e j 0 * E)) a b := by
  simp only [Matrix.mul_apply, reductionU, conjTranspose_apply, Matrix.of_apply,
    Finset.sum_mul]

theorem sum_kronecker_left' {κ a b c d : Type*} (s : Finset κ) (A : κ → Matrix a b ℂ)
    (B : Matrix c d ℂ) : (∑ k ∈ s, A k) ⊗ₖ B = ∑ k ∈ s, A k ⊗ₖ B := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons x s hx ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.add_kronecker, ih]

theorem one_kron_cancel' {x y : Matrix J J ℂ}
    (hxy : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ x = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ y) :
    x = y := by
  ext a b
  have := congrFun (congrFun hxy (0, a)) (0, b)
  simpa [kroneckerMap_apply] using this

variable (he : IsMatUnits e) (hE1 : Eᴴ * E = 1) (hE2 : E * Eᴴ = e 0 0)
include he hE1 hE2

theorem e00_mul_E' : e 0 0 * E = E := by
  rw [← hE2, Matrix.mul_assoc, hE1, Matrix.mul_one]

theorem col_inner' (i j : Fin m) : (e i 0 * E)ᴴ * (e j 0 * E) = if i = j then 1 else 0 := by
  rw [conjTranspose_mul, he.adj]
  calc Eᴴ * e 0 i * (e j 0 * E) = Eᴴ * (e 0 i * e j 0) * E := by simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [he.mul]
        split_ifs with h
        · rw [Matrix.mul_assoc, e00_mul_E' he hE1 hE2, hE1]
        · simp

theorem reductionU_conjTranspose_mul : (reductionU e E)ᴴ * reductionU e E = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have h := congrFun (congrFun (col_inner' he hE1 hE2 i j) a) b
  rw [Matrix.mul_apply] at h ⊢
  simp only [reductionU, conjTranspose_apply, Matrix.of_apply] at h ⊢
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply]
  · simp [hij]

theorem reductionU_mul_conjTranspose : reductionU e E * (reductionU e E)ᴴ = 1 := by
  have hsum : reductionU e E * (reductionU e E)ᴴ = ∑ i, (e i 0 * E) * (e i 0 * E)ᴴ := by
    ext x y
    simp only [Matrix.mul_apply, reductionU, conjTranspose_apply, Matrix.of_apply,
      Matrix.sum_apply, Fintype.sum_prod_type]
  rw [hsum, ← he.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_mul, he.adj]
  calc e i 0 * E * (Eᴴ * e 0 i) = e i 0 * (E * Eᴴ) * e 0 i := by simp only [Matrix.mul_assoc]
    _ = e i i := by rw [hE2, he.mul, if_pos rfl, he.mul, if_pos rfl]

theorem reductionU_conj_matrixUnit (k l : Fin m) :
    (reductionU e E)ᴴ * e k l * reductionU e E =
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
              rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, Matrix.mul_assoc, e00_mul_E' he hE1 hE2, hE1]
            · rw [if_neg hlj, if_neg (fun h => hlj h.2)]
              simp
          · rw [if_neg hik, if_neg (fun h => hik h.1)]
            simp
  have h := congrFun (congrFun hblock a) b
  have hlhs := reductionU_conj_apply (e := e) (E := E) (e k l) i a j b
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

theorem conj_back' (X : Matrix h h ℂ) :
    reductionU e E * ((reductionU e E)ᴴ * X * reductionU e E) * (reductionU e E)ᴴ = X := by
  calc reductionU e E * ((reductionU e E)ᴴ * X * reductionU e E) * (reductionU e E)ᴴ
      = (reductionU e E * (reductionU e E)ᴴ) * X *
          (reductionU e E * (reductionU e E)ᴴ) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [reductionU_mul_conjTranspose he hE1 hE2, Matrix.one_mul, Matrix.mul_one]

/-- `𝒰 (a ⊗ I) 𝒰^* = ∑_{kl} a_kl e_kl`. -/
theorem reductionU_conj_kron (a : Matrix (Fin m) (Fin m) ℂ) :
    reductionU e E * (a ⊗ₖ (1 : Matrix J J ℂ)) * (reductionU e E)ᴴ =
      ∑ k, ∑ l, a k l • e k l := by
  have ha : a ⊗ₖ (1 : Matrix J J ℂ) =
      ∑ k, ∑ l, a k l • (Matrix.single k l (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single a]
    simp only [sum_kronecker_left', ← Matrix.smul_kronecker, Matrix.smul_single, smul_eq_mul,
      mul_one]
  rw [ha, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, ← reductionU_conj_matrixUnit he hE1 hE2 k l,
    conj_back' he hE1 hE2]

theorem conj_commute_kron_of_commute' (X : Matrix h h ℂ)
    (hX : ∀ i j, X * e i j = e i j * X) (g : Matrix (Fin m) (Fin m) ℂ) :
    (g ⊗ₖ (1 : Matrix J J ℂ)) * ((reductionU e E)ᴴ * X * reductionU e E) =
      ((reductionU e E)ᴴ * X * reductionU e E) * (g ⊗ₖ (1 : Matrix J J ℂ)) := by
  set U := reductionU e E with hU
  have hunit : ∀ k l, (Matrix.single k l (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) * (Uᴴ * X * U) =
      (Uᴴ * X * U) * (Matrix.single k l (1 : ℂ) ⊗ₖ (1 : Matrix J J ℂ)) := by
    intro k l
    rw [← reductionU_conj_matrixUnit he hE1 hE2 k l]
    calc Uᴴ * e k l * U * (Uᴴ * X * U) = Uᴴ * (e k l * (U * Uᴴ) * X) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * (X * (U * Uᴴ) * e k l) * U := by
          rw [reductionU_mul_conjTranspose he hE1 hE2, Matrix.mul_one, Matrix.mul_one, hX k l]
      _ = Uᴴ * X * U * (Uᴴ * e k l * U) := by simp only [Matrix.mul_assoc]
  rw [Matrix.matrix_eq_sum_single g]
  simp only [sum_kronecker_left', Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hs : Matrix.single k l (g k l) = g k l • Matrix.single k l (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs, Matrix.smul_kronecker, Matrix.smul_mul, Matrix.mul_smul, hunit]

/-- An operator commuting with every `e_ij` is `I_m ⊗ x̃` in the reduction coordinates. -/
theorem conj_eq_one_kron_of_commute' (X : Matrix h h ℂ) (hX : ∀ i j, X * e i j = e i j * X) :
    (reductionU e E)ᴴ * X * reductionU e E =
      (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (Eᴴ * X * E) := by
  obtain ⟨B, hB⟩ := NCG.CommonOrigin.left_factor_commutant _
    (conj_commute_kron_of_commute' he hE1 hE2 X hX)
  have hBid : B = Eᴴ * X * E := by
    ext a b
    have h := congrFun (congrFun hB (0, a)) (0, b)
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul] at h
    rw [← h, reductionU_conj_apply, e00_mul_E' he hE1 hE2]
  rw [hB, hBid]

end Reduction

/-! ### The factor and the typed decomposition -/

section Main

variable {m : ℕ} [NeZero m] {h : Type} [Fintype h] [DecidableEq h]

/-- `x ↦ I_m ⊗ x` as a unital algebra map. -/
def oneKron (m : ℕ) (K : Type) [Fintype K] [DecidableEq K] :
    Matrix K K ℂ →ₐ[ℂ] Matrix (Fin m × K) (Fin m × K) ℂ where
  toFun x := (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ x
  map_one' := Matrix.one_kronecker_one
  map_mul' x y := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.kronecker_zero _
  map_add' x y := Matrix.kronecker_add _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul, Matrix.one_kronecker_one]

theorem unitary_conj_mul {N K : Type} [Fintype N] [Fintype K] [DecidableEq K]
    (U : Matrix N K ℂ) (hU : Uᴴ * U = 1) (x y : Matrix K K ℂ) :
    U * x * Uᴴ * (U * y * Uᴴ) = U * (x * y) * Uᴴ := by
  calc U * x * Uᴴ * (U * y * Uᴴ) = U * x * (Uᴴ * U) * y * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * (x * y) * Uᴴ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem unitary_conj_injective {N K : Type} [Fintype N] [Fintype K] [DecidableEq K]
    (U : Matrix N K ℂ) (hU : Uᴴ * U = 1) {x y : Matrix K K ℂ}
    (hxy : U * x * Uᴴ = U * y * Uᴴ) : x = y := by
  have h := congrArg (fun z => Uᴴ * z * U) hxy
  simp only [Matrix.mul_assoc] at h
  rw [hU, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul, ← Matrix.mul_assoc, hU,
    Matrix.one_mul] at h
  simpa using h

/-- `φ(X) = ∑_{kl} X_kl φ(E_kl)`. -/
theorem algHom_eq_sum_units (φ : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix h h ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    φ X = ∑ k, ∑ l, X k l • φ (Matrix.single k l 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

/-- **`eq:factor-commutant`.**  A unital `*`-copy `φ` of `M_m(ℂ)` on a finite Hilbert space
`ℋ` is unitarily `M_m(ℂ) ⊗ I` on `ℂ^m ⊗ 𝒦`, and its commutant is `I_m ⊗ B(𝒦)`. -/
theorem factor_commutant (φ : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix h h ℂ)
    (hφ : ∀ X, φ Xᴴ = (φ X)ᴴ) :
    ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (U : Matrix h (Fin m × K) ℂ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (∀ X, φ X = U * (X ⊗ₖ (1 : Matrix K K ℂ)) * Uᴴ) ∧
      matCommutant (Set.range φ) =
        {Y | ∃ y : Matrix K K ℂ, Y = U * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ y) * Uᴴ} := by
  set e : Fin m → Fin m → Matrix h h ℂ := fun i j => φ (Matrix.single i j 1) with hedef
  have he : IsMatUnits e := isMatUnits_of_starHom φ hφ
  obtain ⟨K, _, _, E, hE1, hE2⟩ := projection_factor (e 0 0) (he.adj 0 0)
    (by rw [he.mul, if_pos rfl])
  set U := reductionU e E
  have hU1 := reductionU_conjTranspose_mul he hE1 hE2
  have hU2 := reductionU_mul_conjTranspose he hE1 hE2
  have hφU : ∀ X, φ X = U * (X ⊗ₖ (1 : Matrix K K ℂ)) * Uᴴ := by
    intro X
    rw [reductionU_conj_kron he hE1 hE2, algHom_eq_sum_units φ X]
  refine ⟨K, inferInstance, inferInstance, U, hU1, hU2, hφU, ?_⟩
  ext Y
  constructor
  · intro hY
    have hYe : ∀ i j, Y * e i j = e i j * Y := fun i j => hY _ ⟨_, rfl⟩
    refine ⟨Eᴴ * Y * E, ?_⟩
    rw [← conj_eq_one_kron_of_commute' he hE1 hE2 Y hYe, conj_back' he hE1 hE2]
  · rintro ⟨y, rfl⟩ _ ⟨X, rfl⟩
    rw [hφU, unitary_conj_mul U hU1, unitary_conj_mul U hU1, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
      Matrix.one_mul]

/-- **The factor obstruction** (`thm:trinity`): the full commutant `M_m(ℂ)' = I_m ⊗ B(𝒦)` has
trivial centre, so an internal algebra with a non-scalar central element is not the full
commutant of the external factor. -/
theorem factor_obstruction (φ : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix h h ℂ)
    (hφ : ∀ X, φ Xᴴ = (φ X)ᴴ) (A : Subalgebra ℂ (Matrix h h ℂ))
    (hz : ∃ z ∈ A, (∀ a ∈ A, z * a = a * z) ∧ ∀ c : ℂ, z ≠ c • 1) :
    (A : Set (Matrix h h ℂ)) ≠ matCommutant (Set.range φ) := by
  intro hA
  obtain ⟨z, hzA, hzc, hzs⟩ := hz
  obtain ⟨K, _, _, U, hU1, hU2, -, hcomm⟩ := factor_commutant φ hφ
  have hmem : ∀ y : Matrix K K ℂ,
      U * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ y) * Uᴴ ∈ (A : Set (Matrix h h ℂ)) := by
    intro y; rw [hA, hcomm]; exact ⟨y, rfl⟩
  have hz' : z ∈ matCommutant (Set.range φ) := by rw [← hA]; exact hzA
  rw [hcomm] at hz'
  obtain ⟨y, rfl⟩ := hz'
  have hy : ∀ y' : Matrix K K ℂ, y * y' = y' * y := by
    intro y'
    have h := hzc _ (hmem y')
    rw [unitary_conj_mul U hU1, unitary_conj_mul U hU1, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul] at h
    exact one_kron_cancel' (by simpa using unitary_conj_injective U hU1 h)
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
    fun i j => (hy (Matrix.single i j 1)).symm
  apply hzs c
  rw [← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.kronecker_smul,
    Matrix.one_kronecker_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU2]

/-- The `C^*`-algebra generated by a star-closed set has the same commutant as the set. -/
theorem matCommutant_starAdjoin_of_starClosed {N : Type} [Fintype N] [DecidableEq N]
    (S : Set (Matrix N N ℂ)) (hS : ∀ a ∈ S, aᴴ ∈ S) :
    matCommutant (starAdjoin S : Set (Matrix N N ℂ)) = matCommutant S := by
  ext T
  have h := ArbitraryIncidenceDuality.mem_matCommutant_starAdjoin_iff S T
  change T ∈ matCommutant ((StarAlgebra.adjoin ℂ S : StarSubalgebra ℂ (Matrix N N ℂ)) :
    Set (Matrix N N ℂ)) ↔ _
  rw [h]
  constructor
  · intro hT a ha; exact (hT a ha).1
  · intro hT a ha; exact ⟨hT a ha, hT _ (hS a ha)⟩

/-- The conjugation `x ↦ U x U^*` by a unitary, as a unital algebra map. -/
def conjAlgHom {N K : Type} [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K]
    (U : Matrix N K ℂ) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) :
    Matrix K K ℂ →ₐ[ℂ] Matrix N N ℂ where
  toFun x := U * x * Uᴴ
  map_one' := by rw [Matrix.mul_one, hU2]
  map_mul' x y := (unitary_conj_mul U hU1 x y).symm
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hU2]

theorem conjAlgHom_apply {N K : Type} [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K]
    (U : Matrix N K ℂ) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (x : Matrix K K ℂ) :
    conjAlgHom U hU1 hU2 x = U * x * Uᴴ := rfl

/-- Commutant of `I_m ⊗ 𝒮`: the operators all of whose `(i, j)` coefficient blocks commute
with `𝒮`. -/
theorem matCommutant_one_kron {N : Type} [Fintype N] [DecidableEq N]
    (S : Set (Matrix N N ℂ)) :
    matCommutant {Y | ∃ Z ∈ S, Y = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Z} =
      {Q | ∀ i j, SMSTQuiverCommutantAssembly.blockSlice Q i j ∈ matCommutant S} := by
  ext Q
  constructor
  · intro hQ i j Z hZ
    have h := hQ _ ⟨Z, hZ, rfl⟩
    have h' := (ArbitraryIncidenceDuality.one_kron_commute_iff_blockSlice Z Z Q).mp h.symm i j
    exact h'.symm
  · rintro hQ _ ⟨Z, hZ, rfl⟩
    refine ((ArbitraryIncidenceDuality.one_kron_commute_iff_blockSlice Z Z Q).mpr
      fun i j => (hQ i j Z hZ).symm).symm

/-- Commutants transported along a unitary `T`. -/
theorem matCommutant_conj {N K : Type} [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K]
    (T : Matrix N K ℂ) (hT1 : Tᴴ * T = 1) (hT2 : T * Tᴴ = 1) (S : Set (Matrix K K ℂ)) :
    matCommutant {Y | ∃ Q ∈ S, Y = T * Q * Tᴴ} = {Y | ∃ Q ∈ matCommutant S, Y = T * Q * Tᴴ} := by
  ext Y
  constructor
  · intro hY
    refine ⟨Tᴴ * Y * T, fun Q hQ => ?_, ?_⟩
    · have h := hY _ ⟨Q, hQ, rfl⟩
      apply unitary_conj_injective T hT1
      rw [← unitary_conj_mul T hT1, ← unitary_conj_mul T hT1]
      have hb : T * (Tᴴ * Y * T) * Tᴴ = Y := by
        calc T * (Tᴴ * Y * T) * Tᴴ = (T * Tᴴ) * Y * (T * Tᴴ) := by simp only [Matrix.mul_assoc]
          _ = Y := by rw [hT2, Matrix.one_mul, Matrix.mul_one]
      rw [hb, h]
    · calc Y = (T * Tᴴ) * Y * (T * Tᴴ) := by rw [hT2, Matrix.one_mul, Matrix.mul_one]
        _ = T * (Tᴴ * Y * T) * Tᴴ := by simp only [Matrix.mul_assoc]
  · rintro ⟨Q, hQ, rfl⟩ _ ⟨P, hP, rfl⟩
    rw [unitary_conj_mul T hT1, unitary_conj_mul T hT1, hQ P hP]

/-- **Finite double commutant, as a set identity**, for a unital `*`-closed subalgebra. -/
theorem eq_matCommutant_matCommutant {N : Type} [Fintype N] [DecidableEq N]
    (C : Subalgebra ℂ (Matrix N N ℂ)) (hC : ∀ a ∈ C, aᴴ ∈ C) :
    (C : Set (Matrix N N ℂ)) = matCommutant (matCommutant (C : Set (Matrix N N ℂ))) := by
  ext X
  constructor
  · intro hX T hT
    exact (hT X hX).symm
  · intro hX
    exact double_commutant C hC X hX

/-- **`thm:trinity`, typed decomposition** (`eq:trinity-H`, `eq:trinity-Aint`,
`eq:trinity-C`, `eq:trinity-Cprime`).  Let `φ` be a unital `*`-copy of `M_m(ℂ)` (`m ≥ 1`) on a
finite Hilbert space `ℋ` and `𝒜_type` a commuting unital `*`-closed subalgebra.  There are a
finite sector set `Λ`, nonempty `V_λ = ℂ^{I λ}`, `M_λ = ℂ^{J λ}` and a unitary
`T : ℂ^m ⊗ (⊕_λ V_λ ⊗ M_λ) → ℋ` with
* `φ(X) = T (X ⊗ I) T^*`;
* `𝒜_type = T (I_m ⊗ ⊕_λ B(V_λ) ⊗ I_{M_λ}) T^*`;
* `𝒞 = C^*(φ(M_m), 𝒜_type) = T (M_m(ℂ) ⊗ ⊕_λ B(V_λ) ⊗ I_{M_λ}) T^*` (every `(i, j)` block
  in `⊕_λ B(V_λ) ⊗ I`), i.e. `⊕_λ B(ℂ^m ⊗ V_λ) ⊗ I_{M_λ}`;
* `𝒞' = T (I_m ⊗ ⊕_λ I_{V_λ} ⊗ B(M_λ)) T^*`. -/
theorem trinity_typed_decomposition (φ : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix h h ℂ)
    (hφ : ∀ X, φ Xᴴ = (φ X)ᴴ) (A : Subalgebra ℂ (Matrix h h ℂ)) (hAstar : ∀ a ∈ A, aᴴ ∈ A)
    (hAcomm : ∀ a ∈ A, ∀ X, a * φ X = φ X * a) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (I J : ι → Type)
      (_ : ∀ b, Fintype (I b)) (_ : ∀ b, DecidableEq (I b))
      (_ : ∀ b, Fintype (J b)) (_ : ∀ b, DecidableEq (J b))
      (T : Matrix h (Fin m × Σ b, I b × J b) ℂ),
      Tᴴ * T = 1 ∧ T * Tᴴ = 1 ∧ (∀ b, Nonempty (I b)) ∧ (∀ b, Nonempty (J b)) ∧
      (∀ X, φ X = T * (X ⊗ₖ (1 : Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ)) * Tᴴ) ∧
      (A : Set (Matrix h h ℂ)) =
        {Y | ∃ Z ∈ actionBlockSet I J,
          Y = T * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Z) * Tᴴ} ∧
      (starAdjoin (Set.range φ ∪ (A : Set (Matrix h h ℂ))) : Set (Matrix h h ℂ)) =
        {Y | ∃ Q : Matrix (Fin m × Σ b, I b × J b) (Fin m × Σ b, I b × J b) ℂ,
          (∀ i j, SMSTQuiverCommutantAssembly.blockSlice Q i j ∈ actionBlockSet I J) ∧ Y = T * Q * Tᴴ} ∧
      matCommutant (starAdjoin (Set.range φ ∪ (A : Set (Matrix h h ℂ))) :
          Set (Matrix h h ℂ)) =
        {Y | ∃ Z ∈ multBlockSet I J,
          Y = T * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Z) * Tᴴ} := by
  obtain ⟨K, _, _, U, hU1, hU2, hφU, hcomm⟩ := factor_commutant φ hφ
  set L : Matrix K K ℂ →ₐ[ℂ] Matrix h h ℂ := (conjAlgHom U hU1 hU2).comp (oneKron m K) with hL
  have hLapply : ∀ y, L y = U * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ y) * Uᴴ := fun y => rfl
  have hLinj : Function.Injective L := fun x y hxy =>
    one_kron_cancel' (unitary_conj_injective U hU1 hxy)
  have hLstar : ∀ y, L yᴴ = (L y)ᴴ := by
    intro y
    rw [hLapply, hLapply, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_kronecker, conjTranspose_one, Matrix.mul_assoc]
  have hAL : ∀ a ∈ A, ∃ y, a = L y := by
    intro a ha
    have hmem : a ∈ matCommutant (Set.range φ) := by
      rintro _ ⟨X, rfl⟩; exact hAcomm a ha X
    rw [hcomm] at hmem
    exact hmem
  set A' : Subalgebra ℂ (Matrix K K ℂ) := A.comap L with hA'
  have hA'mem : ∀ y, y ∈ A' ↔ L y ∈ A := fun y => Iff.rfl
  have hA'star : ∀ y ∈ A', yᴴ ∈ A' := by
    intro y hy
    rw [hA'mem, hLstar]
    exact hAstar _ hy
  obtain ⟨ι, _, _, I, J, _, _, _, _, W, hW1, hW2, hNI, hNJ, hAW, hMW⟩ :=
    reciprocal_wedderburn A' hA'star
  set T : Matrix h (Fin m × Σ b, I b × J b) ℂ :=
    U * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ W) with hTdef
  have hT1 : Tᴴ * T = 1 := by
    rw [hTdef, conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, hW1, Matrix.one_kronecker_one]
  have hT2 : T * Tᴴ = 1 := by
    rw [hTdef, conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (_ ⊗ₖ W), ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, hW2, Matrix.one_kronecker_one, Matrix.one_mul, hU2]
  have hTconj : ∀ Q : Matrix (Fin m × Σ b, I b × J b) (Fin m × Σ b, I b × J b) ℂ, T * Q * Tᴴ =
      U * (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ W) * Q * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Wᴴ)) *
        Uᴴ := by
    intro Q
    rw [hTdef, conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one]
    simp only [Matrix.mul_assoc]
  have hTone : ∀ Z : Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ,
      T * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Z) * Tᴴ = L (W * Z * Wᴴ) := by
    intro Z
    rw [hTconj, hLapply, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.one_mul]
  have hWback : ∀ y : Matrix K K ℂ, W * (Wᴴ * y * W) * Wᴴ = y := by
    intro y
    calc W * (Wᴴ * y * W) * Wᴴ = (W * Wᴴ) * y * (W * Wᴴ) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [hW2, Matrix.one_mul, Matrix.mul_one]
  -- the commutant of the generators
  have hstarS : ∀ a ∈ Set.range φ ∪ (A : Set (Matrix h h ℂ)),
      aᴴ ∈ Set.range φ ∪ (A : Set (Matrix h h ℂ)) := by
    rintro a (⟨X, rfl⟩ | ha)
    · exact Or.inl ⟨Xᴴ, hφ X⟩
    · exact Or.inr (hAstar a ha)
  have hCprime : matCommutant (starAdjoin (Set.range φ ∪ (A : Set (Matrix h h ℂ))) :
      Set (Matrix h h ℂ)) = {Y | ∃ Z ∈ multBlockSet I J,
        Y = T * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Z) * Tᴴ} := by
    rw [matCommutant_starAdjoin_of_starClosed _ hstarS]
    ext Y
    constructor
    · intro hY
      have hYφ : Y ∈ matCommutant (Set.range φ) := fun a ha => hY a (Or.inl ha)
      rw [hcomm] at hYφ
      obtain ⟨y, rfl⟩ := hYφ
      have hyA' : y ∈ matCommutant (A' : Set (Matrix K K ℂ)) := by
        intro y' hy'
        apply hLinj
        rw [map_mul, map_mul]
        exact hY _ (Or.inr hy')
      have hZ : Wᴴ * y * W ∈ multBlockSet I J := by
        rw [← hMW]; exact ⟨y, hyA', rfl⟩
      refine ⟨_, hZ, ?_⟩
      rw [hTone, hWback]
      exact (hLapply y).symm
    · rintro ⟨Z, hZ, rfl⟩ a ha
      rw [← hMW] at hZ
      obtain ⟨y, hy, rfl⟩ := hZ
      rw [hTone, hWback]
      rcases ha with ⟨X, rfl⟩ | ha
      · have hmem : L y ∈ matCommutant (Set.range φ) := by rw [hcomm]; exact ⟨y, rfl⟩
        exact hmem _ ⟨X, rfl⟩
      · obtain ⟨y', rfl⟩ := hAL a ha
        rw [← map_mul, ← map_mul, hy y' ha]
  refine ⟨ι, inferInstance, inferInstance, I, J, inferInstance, inferInstance, inferInstance,
    inferInstance, T, hT1, hT2, hNI, hNJ, ?_, ?_, ?_, hCprime⟩
  · -- `φ(X) = T (X ⊗ I) T^*`
    intro X
    rw [hφU X, hTconj, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      Matrix.mul_one, Matrix.one_mul, hW2]
  · -- `𝒜_type = T (I_m ⊗ ⊕ B(V) ⊗ I) T^*`
    ext Y
    constructor
    · intro hY
      obtain ⟨y, rfl⟩ := hAL Y hY
      have hZ : Wᴴ * y * W ∈ actionBlockSet I J := by
        rw [← hAW]; exact ⟨y, hY, rfl⟩
      refine ⟨_, hZ, ?_⟩
      rw [hTone, hWback]
    · rintro ⟨Z, hZ, rfl⟩
      rw [← hAW] at hZ
      obtain ⟨y, hy, rfl⟩ := hZ
      rw [hTone, hWback]
      exact hy
  · -- `𝒞 = T (M_m ⊗ ⊕ B(V) ⊗ I) T^*` by the double commutant theorem
    rw [eq_matCommutant_matCommutant _ (starAdjoin_starClosed _), hCprime]
    have hset : {Y | ∃ Z ∈ multBlockSet I J,
        Y = T * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Z) * Tᴴ} =
        {Y | ∃ Q ∈ {Y | ∃ Z ∈ multBlockSet I J, Y = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Z},
          Y = T * Q * Tᴴ} := by
      ext Y
      constructor
      · rintro ⟨Z, hZ, rfl⟩; exact ⟨_, ⟨Z, hZ, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨Z, hZ, rfl⟩, rfl⟩; exact ⟨Z, hZ, rfl⟩
    rw [hset, matCommutant_conj T hT1 hT2, matCommutant_one_kron, matCommutant_multBlockSet]
    ext Y
    constructor
    · rintro ⟨Q, hQ, rfl⟩; exact ⟨Q, hQ, rfl⟩
    · rintro ⟨Q, hQ, rfl⟩; exact ⟨Q, hQ, rfl⟩

/-! ### Non-vacuity -/

/-- `X ↦ X ⊗ I_K` as a unital algebra map. -/
def kronOne (m : ℕ) (K : Type) [Fintype K] [DecidableEq K] :
    Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix (Fin m × K) (Fin m × K) ℂ where
  toFun x := x ⊗ₖ (1 : Matrix K K ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' x y := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.zero_kronecker _
  map_add' x y := Matrix.add_kronecker _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker, Matrix.one_kronecker_one]

/-- **Non-vacuity**: `M₂(ℂ) ⊗ I` on `ℂ² ⊗ ℂ²` with the commuting non-scalar algebra
`I ⊗ M₂(ℂ)` satisfies the hypotheses of `trinity_typed_decomposition`. -/
example : ∃ (φ : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (A : Subalgebra ℂ (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)),
    (∀ X, φ Xᴴ = (φ X)ᴴ) ∧ (∀ a ∈ A, aᴴ ∈ A) ∧ (∀ a ∈ A, ∀ X, a * φ X = φ X * a) ∧
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Matrix.single 0 0 1 ∈ A := by
  refine ⟨kronOne 2 (Fin 2), (oneKron 2 (Fin 2)).range, fun X => ?_, ?_, ?_,
    ⟨Matrix.single 0 0 1, rfl⟩⟩
  · show Xᴴ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) = (X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
    rw [conjTranspose_kronecker, conjTranspose_one]
  · rintro _ ⟨y, rfl⟩
    refine ⟨yᴴ, ?_⟩
    show (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ yᴴ = ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ y)ᴴ
    rw [conjTranspose_kronecker, conjTranspose_one]
  · rintro _ ⟨y, rfl⟩ X
    show (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ y * (X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ y)
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_one]


end Main

end TrinityDecomposition
end RenewalGeometry
