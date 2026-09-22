/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.JointCommutatorContinuousOperator
import RenewalGeometry.Commutant.RelativeHoweGramSpectralCertificateExact
/-!
# The commutant Laplacian as a sum of `ad* ad`, and the relative Howe Gram

Covers `def:commutant-laplacian` and `def:howe-gram` of the spacetime--gauge
duality manuscript on the finite Hilbert--Schmidt carrier
`EuclideanSpace ℂ (n × n)`.

* `adCLM c j`: the continuous derivation `X ↦ [c_j, X]` on the Hilbert--Schmidt
  carrier (the `j`-th coordinate of the stacked joint commutator source).
* `commutantLaplacianCLM_eq_sum_adjoint_comp`: the boxed display
  `𝓛_𝒞 = Σ_j ad_{c_j}^* ad_{c_j}`.
* `commutantLaplacianCLM_inner_self`: `⟪X, 𝓛_𝒞 X⟫ = Σ_j ‖[c_j, X]‖²_HS`.
* `relativeHoweGram c E`: the matrix `𝔾_Howe(c | M)_{ab} = Σ_j ⟪[c_j, E_a], [c_j, E_b]⟫_HS`
  for a Hilbert--Schmidt orthonormal basis `E` of `M^⊥`
  (`IsHSOrthonormalBasisOf M E`), identified with the Gram of the stacked
  joint commutator source, hence Hermitian and positive semidefinite.
-/

open scoped InnerProductSpace

noncomputable section

namespace RenewalGeometry
open Matrix

/-- Coordinate projection of the stacked Hilbert--Schmidt carrier onto its
`j`-th block. -/
def stackCoordCLM {n : Type*} [Fintype n] {s : ℕ} (j : Fin s) :
    EuclideanSpace ℂ (Fin s × (n × n)) →L[ℂ] EuclideanSpace ℂ (n × n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun ij => x (j, ij))
      map_add' := fun x y => by
        ext ij
        simp
      map_smul' := fun a x => by
        ext ij
        simp }

@[simp] theorem stackCoordCLM_apply {n : Type*} [Fintype n] {s : ℕ} (j : Fin s)
    (x : EuclideanSpace ℂ (Fin s × (n × n))) (ij : n × n) :
    stackCoordCLM j x ij = x (j, ij) := rfl

/-- The inner product on the stacked carrier is the sum of the block inner
products. -/
theorem inner_eq_sum_stackCoord {n : Type*} [Fintype n] {s : ℕ}
    (x y : EuclideanSpace ℂ (Fin s × (n × n))) :
    ⟪x, y⟫_ℂ = ∑ j, ⟪stackCoordCLM j x, stackCoordCLM j y⟫_ℂ := by
  simp only [PiLp.inner_apply, stackCoordCLM_apply, Fintype.sum_prod_type]

/-- The derivation `ad_{c_j} : X ↦ [c_j, X]` on the Hilbert--Schmidt carrier, as
the `j`-th block of the stacked joint commutator source. -/
def adCLM {n : Type*} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ) (j : Fin s) :
    EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n) :=
  stackCoordCLM j ∘L jointCommutatorCLM c

/-- `ad_{c_j}` is literally the commutator with `c_j`. -/
theorem adCLM_matrixL2 {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (j : Fin s) (X : Matrix n n ℂ) :
    adCLM c j (matrixL2 X) = matrixL2 (c j * X - X * c j) := by
  ext ij
  simp [adCLM, jointCommutatorL2, matrixL2]

/-- The stacked joint commutator source has the derivations as its blocks. -/
theorem stackCoordCLM_jointCommutatorCLM {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (j : Fin s) (x : EuclideanSpace ℂ (n × n)) :
    stackCoordCLM j (jointCommutatorCLM c x) = adCLM c j x := rfl

/-- Polarised Gram identity of the stacked source: `⟪J x, J y⟫ = Σ_j ⟪ad_j x, ad_j y⟫`. -/
theorem inner_jointCommutatorCLM {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (x y : EuclideanSpace ℂ (n × n)) :
    ⟪jointCommutatorCLM c x, jointCommutatorCLM c y⟫_ℂ =
      ∑ j, ⟪adCLM c j x, adCLM c j y⟫_ℂ := by
  rw [inner_eq_sum_stackCoord]
  rfl

/-- **`def:commutant-laplacian`**, boxed display: the commutant Laplacian is
`Σ_j ad_{c_j}^* ad_{c_j}`. -/
theorem commutantLaplacianCLM_eq_sum_adjoint_comp {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) :
    commutantLaplacianCLM c =
      ∑ j, ContinuousLinearMap.adjoint (adCLM c j) ∘L adCLM c j := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [commutantLaplacianCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, inner_jointCommutatorCLM,
    ContinuousLinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

/-- The quadratic form of the commutant Laplacian is the summed squared
Hilbert--Schmidt norm of the derivations. -/
theorem commutantLaplacianCLM_inner_self {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (x : EuclideanSpace ℂ (n × n)) :
    ⟪x, commutantLaplacianCLM c x⟫_ℂ = ∑ j, ((‖adCLM c j x‖ : ℂ)) ^ 2 := by
  rw [commutantLaplacianCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, inner_jointCommutatorCLM]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact inner_self_eq_norm_sq_to_K _

/-- On matrices, `⟪X, 𝓛_𝒞 X⟫ = Σ_j ‖[c_j, X]‖²_HS` in the trace convention. -/
theorem commutantLaplacianCLM_inner_self_matrixL2 {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (X : Matrix n n ℂ) :
    ⟪matrixL2 X, commutantLaplacianCLM c (matrixL2 X)⟫_ℂ =
      ∑ j, ((((c j * X - X * c j)ᴴ * (c j * X - X * c j)).trace).re : ℂ) := by
  rw [commutantLaplacianCLM_inner_self]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [adCLM_matrixL2, ← matrixL2_norm_sq]
  push_cast
  ring

/-- **`def:howe-gram`** (spacetime--gauge duality manuscript): the relative Howe
Gram `𝔾_Howe(c | M)_{ab} = Σ_j ⟪[c_j, E_a], [c_j, E_b]⟫_HS` of a labelled family
`E` (intended: a Hilbert--Schmidt orthonormal basis of `M^⊥`). -/
def relativeHoweGram {n : Type*} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ)
    {r : ℕ} (E : Fin r → Matrix n n ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b =>
    ∑ j, ⟪matrixL2 (c j * E a - E a * c j), matrixL2 (c j * E b - E b * c j)⟫_ℂ

/-- `E` is a Hilbert--Schmidt orthonormal basis of `M^⊥`, the hypothesis of
`def:howe-gram`. -/
def IsHSOrthonormalBasisOf {n : Type*} [Fintype n]
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n))) {r : ℕ}
    (E : Fin r → Matrix n n ℂ) : Prop :=
  Orthonormal ℂ (fun a => matrixL2 (E a)) ∧
    Submodule.span ℂ (Set.range fun a => matrixL2 (E a)) = Mᗮ

theorem relativeHoweGram_apply {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) {r : ℕ} (E : Fin r → Matrix n n ℂ) (a b : Fin r) :
    relativeHoweGram c E a b =
      ∑ j, ⟪matrixL2 (c j * E a - E a * c j), matrixL2 (c j * E b - E b * c j)⟫_ℂ :=
  rfl

/-- The relative Howe Gram is the polarised Gram of the stacked joint commutator
source on the family `E`. -/
theorem relativeHoweGram_eq_inner_jointCommutatorCLM {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) {r : ℕ} (E : Fin r → Matrix n n ℂ) (a b : Fin r) :
    relativeHoweGram c E a b =
      ⟪jointCommutatorCLM c (matrixL2 (E a)), jointCommutatorCLM c (matrixL2 (E b))⟫_ℂ := by
  rw [relativeHoweGram_apply, inner_jointCommutatorCLM]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [adCLM_matrixL2, adCLM_matrixL2]

/-- The stacked commutator coefficients of the family `E`, as a matrix whose
columns are indexed by the family. -/
def relativeHoweSynthesis {n : Type*} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ)
    {r : ℕ} (E : Fin r → Matrix n n ℂ) : Matrix (Fin s × (n × n)) (Fin r) ℂ :=
  Matrix.of fun q a => (c q.1 * E a - E a * c q.1) q.2.1 q.2.2

/-- The relative Howe Gram is a Gram matrix `Aᴴ A`. -/
theorem relativeHoweGram_eq_conjTranspose_mul_self {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) {r : ℕ} (E : Fin r → Matrix n n ℂ) :
    relativeHoweGram c E =
      (relativeHoweSynthesis c E)ᴴ * relativeHoweSynthesis c E := by
  ext a b
  simp only [relativeHoweGram_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    relativeHoweSynthesis, Matrix.of_apply, PiLp.inner_apply, matrixL2,
    WithLp.ofLp_toLp, RCLike.inner_apply, Fintype.sum_prod_type]

/-- The relative Howe Gram is Hermitian. -/
theorem relativeHoweGram_isHermitian {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) {r : ℕ} (E : Fin r → Matrix n n ℂ) :
    (relativeHoweGram c E).IsHermitian := by
  rw [relativeHoweGram_eq_conjTranspose_mul_self]
  exact Matrix.isHermitian_conjTranspose_mul_self _

/-- The relative Howe Gram is positive semidefinite. -/
theorem relativeHoweGram_posSemidef {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) {r : ℕ} (E : Fin r → Matrix n n ℂ) :
    (relativeHoweGram c E).PosSemidef := by
  rw [relativeHoweGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end RenewalGeometry
