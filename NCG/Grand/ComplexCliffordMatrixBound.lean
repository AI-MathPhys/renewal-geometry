/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.JordanWigner
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# The matrix-size bound for an even complex Clifford family

The Jordan--Wigner representation identifies the complex Clifford algebra on
`2m` generators with `M_(2^m)(ℂ)`.  Simplicity of that matrix algebra makes
every unital representation faithful.  Consequently a Clifford family in
`M_n(ℂ)` forces `(2^m)^2 ≤ n^2`.
-/

open scoped BigOperators

namespace NCG.ComplexCliffordBound

abbrev CliffordIndex (m : ℕ) := Fin m × Bool

/-- The standard complex sum-of-squares quadratic form. -/
def cliffordQuadratic (m : ℕ) : QuadraticForm ℂ (CliffordIndex m → ℂ) :=
  QuadraticMap.weightedSumSquares ℂ (fun _ => (1 : ℂ))

/-- Linear extension of a finite matrix family. -/
def familyLinear {ι n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype n] [DecidableEq n]
    (G : ι → Matrix n n ℂ) : (ι → ℂ) →ₗ[ℂ] Matrix n n ℂ where
  toFun a := ∑ i, a i • G i
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, smul_smul,
      Finset.smul_sum]

@[simp] theorem familyLinear_single {ι n : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype n] [DecidableEq n]
    (G : ι → Matrix n n ℂ) (i : ι) :
    familyLinear G (Pi.single i 1) = G i := by
  classical
  simp [familyLinear]

/-- Squaring a linear combination of Clifford generators gives its standard
quadratic norm times the identity. -/
theorem familyLinear_sq {ι n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype n] [DecidableEq n]
    (G : ι → Matrix n n ℂ)
    (hcliff : ∀ i j,
      G i * G j + G j * G i =
        (if i = j then (2 : ℂ) else 0) • 1)
    (a : ι → ℂ) :
    familyLinear G a * familyLinear G a =
      (∑ i, a i * a i) • (1 : Matrix n n ℂ) := by
  classical
  have hdouble :
      (2 : ℂ) • (familyLinear G a * familyLinear G a) =
        ∑ i, ∑ j, (a i * a j) • (G i * G j + G j * G i) := by
    have hfirst :
        familyLinear G a * familyLinear G a =
          ∑ i, ∑ j, (a i * a j) • (G j * G i) := by
      change (∑ i, a i • G i) * (∑ i, a i • G i) =
        ∑ i, ∑ j, (a i * a j) • (G j * G i)
      simp only [familyLinear, Finset.sum_mul, Finset.mul_sum,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hswap :
        (∑ i, ∑ j, (a i * a j) • (G j * G i)) =
          ∑ i, ∑ j, (a i * a j) • (G i * G j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_comm (a j) (a i)]
    rw [hfirst]
    rw [hswap]
    simp only [smul_add, Finset.sum_add_distrib, hswap]
    module
  apply smul_right_injective (Matrix n n ℂ) (by norm_num : (2 : ℂ) ≠ 0)
  change (2 : ℂ) • (familyLinear G a * familyLinear G a) =
    (2 : ℂ) • ((∑ i, a i * a i) • (1 : Matrix n n ℂ))
  rw [hdouble]
  simp [hcliff, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

/-- The universal Clifford-algebra representation attached to a matrix
Clifford family. -/
noncomputable def cliffordRepresentation {n : Type*} [Fintype n]
    [DecidableEq n] (m : ℕ)
    (G : CliffordIndex m → Matrix n n ℂ)
    (hcliff : ∀ i j,
      G i * G j + G j * G i =
        (if i = j then (2 : ℂ) else 0) • 1) :
    CliffordAlgebra (cliffordQuadratic m) →ₐ[ℂ] Matrix n n ℂ :=
  CliffordAlgebra.lift (cliffordQuadratic m) ⟨familyLinear G, by
    intro a
    rw [familyLinear_sq G hcliff]
    simp [cliffordQuadratic, Algebra.smul_def, map_sum]⟩

@[simp] theorem cliffordRepresentation_ι_single {n : Type*} [Fintype n]
    [DecidableEq n] (m : ℕ)
    (G : CliffordIndex m → Matrix n n ℂ)
    (hcliff : ∀ i j,
      G i * G j + G j * G i =
        (if i = j then (2 : ℂ) else 0) • 1)
    (i : CliffordIndex m) :
    cliffordRepresentation m G hcliff
        (CliffordAlgebra.ι (cliffordQuadratic m) (Pi.single i 1)) = G i := by
  simp [cliffordRepresentation]

/-- The Jordan--Wigner Clifford representation is onto the full matrix
algebra. -/
theorem jordanWigner_surjective (m : ℕ) :
    Function.Surjective
      (cliffordRepresentation m (NCG.CommonOrigin.jwGamma (m := m))
        NCG.CommonOrigin.jwGamma_clifford) := by
  let ρ := cliffordRepresentation m (NCG.CommonOrigin.jwGamma (m := m))
    NCG.CommonOrigin.jwGamma_clifford
  rw [← AlgHom.range_eq_top]
  apply le_antisymm le_top
  rw [← NCG.CommonOrigin.jwGamma_generates (m := m)]
  rw [Algebra.adjoin_le_iff]
  rintro A ⟨i, rfl⟩
  exact ⟨CliffordAlgebra.ι (cliffordQuadratic m) (Pi.single i 1), by
    simp [ρ]⟩

/-- The Clifford algebra on `2m` complex generators and the Jordan--Wigner
matrix algebra have the same finite dimension. -/
theorem jordanWigner_finrank_eq (m : ℕ) :
    Module.finrank ℂ (CliffordAlgebra (cliffordQuadratic m)) =
      Module.finrank ℂ
        (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) := by
  letI : LinearOrder (CliffordIndex m) :=
    LinearOrder.lift' (Fintype.equivFin (CliffordIndex m))
      (Fintype.equivFin (CliffordIndex m)).injective
  let b : Module.Basis (CliffordIndex m) ℂ (CliffordIndex m → ℂ) :=
    Pi.basisFun ℂ (CliffordIndex m)
  calc
    Module.finrank ℂ (CliffordAlgebra (cliffordQuadratic m)) =
        Module.finrank ℂ (ExteriorAlgebra ℂ (CliffordIndex m → ℂ)) :=
      LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior (cliffordQuadratic m))
    _ = Fintype.card (Finset (CliffordIndex m)) :=
      Module.finrank_eq_card_basis b.ExteriorAlgebra
    _ = Module.finrank ℂ
        (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) := by
      rw [Module.finrank_matrix, Module.finrank_self, mul_one,
        Fintype.card_finset, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool, Fintype.card_fun, Fintype.card_fin]
      simpa [pow_two] using (pow_mul 2 m 2)

/-- Algebra equivalence supplied by the Jordan--Wigner model. -/
noncomputable def jordanWignerEquiv (m : ℕ) :
    CliffordAlgebra (cliffordQuadratic m) ≃ₐ[ℂ]
      Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ := by
  letI : LinearOrder (CliffordIndex m) :=
    LinearOrder.lift' (Fintype.equivFin (CliffordIndex m))
      (Fintype.equivFin (CliffordIndex m)).injective
  let b : Module.Basis (CliffordIndex m) ℂ (CliffordIndex m → ℂ) :=
    Pi.basisFun ℂ (CliffordIndex m)
  letI : FiniteDimensional ℂ (ExteriorAlgebra ℂ (CliffordIndex m → ℂ)) :=
    Module.Finite.of_basis b.ExteriorAlgebra
  letI : FiniteDimensional ℂ (CliffordAlgebra (cliffordQuadratic m)) :=
    (CliffordAlgebra.equivExterior (cliffordQuadratic m)).symm.finiteDimensional
  let ρ := cliffordRepresentation m (NCG.CommonOrigin.jwGamma (m := m))
    NCG.CommonOrigin.jwGamma_clifford
  exact AlgEquiv.ofBijective ρ ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := ρ.toLinearMap)
      (jordanWigner_finrank_eq m)).mpr (jordanWigner_surjective m),
    jordanWigner_surjective m⟩

/- Any complex `2m`-generator Clifford family in `n × n` matrices obeys
the exponential matrix-size bound. -/
/-- Cardinal form of the matrix-size bound, for an arbitrary finite nonempty
matrix index type. -/
theorem matrix_card_bound (m : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    (G : CliffordIndex m → Matrix ι ι ℂ)
    (hcliff : ∀ i j,
      G i * G j + G j * G i =
        (if i = j then (2 : ℂ) else 0) • 1) :
    (2 ^ m) ^ 2 ≤ (Fintype.card ι) ^ 2 := by
  let ρ : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ →ₐ[ℂ]
      Matrix ι ι ℂ :=
    (cliffordRepresentation m G hcliff).comp
      (jordanWignerEquiv m).symm.toAlgHom
  have hinj : Function.Injective ρ := ρ.toRingHom.injective
  have hdim := LinearMap.finrank_le_finrank_of_injective
    (f := ρ.toLinearMap) hinj
  simpa [Module.finrank_matrix, Fintype.card_fun, pow_two] using hdim

theorem matrix_size_bound (m n : ℕ) (hn : 0 < n)
    (G : CliffordIndex m → Matrix (Fin n) (Fin n) ℂ)
    (hcliff : ∀ i j,
      G i * G j + G j * G i =
        (if i = j then (2 : ℂ) else 0) • 1) :
    (2 ^ m) ^ 2 ≤ n ^ 2 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  simpa using matrix_card_bound m G hcliff

end NCG.ComplexCliffordBound
