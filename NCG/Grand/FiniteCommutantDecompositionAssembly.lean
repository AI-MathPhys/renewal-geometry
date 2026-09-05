/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StarMatrixUnits
import NCG.Grand.FiniteOrthogonalSectorDecomposition

/-!
# Finite commutant decomposition: represented-sector assembly

This file assembles the previously separate Artin--Wedderburn, star-unit,
orthogonal-sector, and bicommutant layers of
`thm:commutant-decomposition`.

The coordinate-free multiplicity form used here is equivalent to
`⊕λ ℂ^{nλ} ⊗ ℂ^{mλ}`: the indices in one `block` are the defining matrix
factor, while the range of `p (base j)` is its common multiplicity space.
The partial isometries `v j` identify every diagonal range in a block with
that common range, and `carrierUnitary` assembles all diagonal ranges into
the original finite Hilbert carrier.
-/

noncomputable section

open Matrix
open scoped BigOperators

namespace NCG
namespace FiniteCommutantDecompositionAssembly

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A complete represented finite commutant decomposition certificate.

The matrices `v j * (v k)ᴴ` are star-compatible matrix units.  Equal values
of `block` are the manuscript's `λ`-sectors; `base` selects the common
multiplicity corner in each such sector. -/
structure Certificate
    (S : Subalgebra ℂ (Matrix n n ℂ)) where
  /-- Total number of diagonal matrix-unit slots. -/
  slotCount : ℕ
  /-- Simple-block label of a slot. -/
  block : Fin slotCount → ℕ
  /-- Orthogonal diagonal projections. -/
  p : Fin slotCount → Matrix n n ℂ
  /-- Partial isometries from the common multiplicity corner. -/
  v : Fin slotCount → Matrix n n ℂ
  /-- Chosen base slot, constant on each block. -/
  base : Fin slotCount → Fin slotCount
  base_block : ∀ j, block (base j) = block j
  base_eq : ∀ j k, block j = block k → base j = base k
  p_mem : ∀ j, p j ∈ S
  p_star : ∀ j, (p j)ᴴ = p j
  p_idem : ∀ j, p j * p j = p j
  p_orthogonal : ∀ j k, j ≠ k → p j * p k = 0
  p_sum : ∑ j, p j = 1
  v_mem : ∀ j, v j ∈ S
  v_initial : ∀ j k, (v j)ᴴ * v k =
    if j = k then p (base j) else 0
  v_final : ∀ j, v j * (v j)ᴴ = p j
  /-- Central support projection of every simple block. -/
  centralBlock : ∀ b : ℕ, ∀ x ∈ S,
    (∑ j ∈ Finset.univ.filter (fun j => block j = b), p j) * x =
      x * ∑ j ∈ Finset.univ.filter (fun j => block j = b), p j
  /-- Unitary decomposition of the carrier into the diagonal ranges.  The
  `v`-laws above regroup equal-block summands into defining-factor tensor
  multiplicity-factor form. -/
  carrierUnitary :
    PiLp 2 (fun j => LinearMap.range (Matrix.toEuclideanLin (p j))) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ n
  /-- Exact star law for the represented matrix units. -/
  matrixUnit_star : ∀ j k, (v j * (v k)ᴴ)ᴴ = v k * (v j)ᴴ
  /-- Exact multiplication law for the represented matrix units. -/
  matrixUnit_mul : ∀ j k l m,
    (v j * (v k)ᴴ) * (v l * (v m)ᴴ) =
      if k = l ∧ base m = base k then v j * (v m)ᴴ else 0
  /-- The represented algebra and its matrix commutant are mutual
  commutants. -/
  mutualCommutant :
    matCommutant (matCommutant (S : Set (Matrix n n ℂ))) =
      (S : Set (Matrix n n ℂ))

/-- Matrix multiplication by a self-adjoint matrix is self-adjoint for the
standard finite Hilbert inner product. -/
theorem toEuclideanLin_inner_selfAdjoint
    (A : Matrix n n ℂ) (hA : Aᴴ = A)
    (x y : EuclideanSpace ℂ n) :
    inner ℂ (Matrix.toEuclideanLin A x) y =
      inner ℂ x (Matrix.toEuclideanLin A y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toEuclideanLin_apply]
  calc
    WithLp.ofLp y ⬝ᵥ star (A *ᵥ WithLp.ofLp x) =
        star (A *ᵥ WithLp.ofLp x) ⬝ᵥ WithLp.ofLp y :=
      dotProduct_comm _ _
    _ = star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp y) := by
      rw [Matrix.star_mulVec, hA, Matrix.dotProduct_mulVec]
    _ = (A *ᵥ WithLp.ofLp y) ⬝ᵥ star (WithLp.ofLp x) :=
      dotProduct_comm _ _

/-- A star-unit system's diagonal projections give the promised unitary
carrier decomposition. -/
def carrierUnitaryOfStarUnits
    {M : ℕ} (p : Fin M → Matrix n n ℂ)
    (hpstar : ∀ j, (p j)ᴴ = p j)
    (hporth : ∀ j k, j ≠ k → p j * p k = 0)
    (hpsum : ∑ j, p j = 1) :
    PiLp 2 (fun j => LinearMap.range (Matrix.toEuclideanLin (p j))) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ n := by
  let P : Fin M → EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n :=
    fun j => Matrix.toEuclideanLin (p j)
  apply FiniteOrthogonalSectorDecomposition.orthogonalSectorUnitaryEquiv
    P
  · intro j x y
    exact toEuclideanLin_inner_selfAdjoint (p j) (hpstar j) x y
  · intro j k hjk
    apply LinearMap.ext
    intro x
    apply WithLp.ofLp_injective
    change p j *ᵥ (p k *ᵥ WithLp.ofLp x) = 0
    rw [Matrix.mulVec_mulVec, hporth j k hjk, Matrix.zero_mulVec]
  · intro x
    apply WithLp.ofLp_injective
    simp only [WithLp.ofLp_sum, P, Matrix.ofLp_toEuclideanLin_apply]
    rw [← Matrix.sum_mulVec, hpsum, Matrix.one_mulVec]

/-- **Finite commutant decomposition.**  Every unital star-closed finite
complex matrix algebra has one assembled represented-sector certificate:
orthogonal central blocks, star-compatible full matrix units, the unitary
carrier direct sum with common multiplicity corners, and the exact mutual
commutant identity. -/
theorem finite_commutant_decomposition
    (S : Subalgebra ℂ (Matrix n n ℂ))
    (hstar : ∀ a ∈ S, aᴴ ∈ S) :
    Nonempty (Certificate S) := by
  obtain ⟨M, block, p, v, base,
    hbaseBlock, hbaseEq, hpMem, hpStar, hpIdem, hpOrth, hpSum,
    hvMem, hvInitial, hvFinal, hcentral⟩ :=
      StarUnits.star_unit_system S hstar
  refine ⟨{
    slotCount := M
    block := block
    p := p
    v := v
    base := base
    base_block := hbaseBlock
    base_eq := hbaseEq
    p_mem := hpMem
    p_star := hpStar
    p_idem := hpIdem
    p_orthogonal := hpOrth
    p_sum := hpSum
    v_mem := hvMem
    v_initial := hvInitial
    v_final := hvFinal
    centralBlock := hcentral
    carrierUnitary := carrierUnitaryOfStarUnits p hpStar hpOrth hpSum
    matrixUnit_star := fun j k => StarUnits.unit_star
    matrixUnit_mul := fun j k l m =>
      StarUnits.unit_mul p v base hpStar hpIdem hpOrth hvInitial j k l m
    mutualCommutant :=
      FiniteStarSubalgebraMutualCommutant.mutualCommutants S hstar }⟩

end FiniteCommutantDecompositionAssembly
end NCG
