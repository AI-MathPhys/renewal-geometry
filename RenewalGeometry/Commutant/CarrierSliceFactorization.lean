/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.EquivariantMultiplicityFactorization
import RenewalGeometry.Commutant.GraphLoadedEdgeCommutantAssembly

/-!
# Multiplicity-one incidence factorization from a prescribed carrier line

Covers `lem:multiplicity-factorization` of the spacetime–gauge duality paper.

An incidence operator `Y : K_λ ⊗ M_λ → K_μ ⊗ M_μ` is encoded as a matrix on the
product index types `Matrix (n × g') (m × g) ℂ` (carrier indices `n, m`, multiplicity
indices `g', g`).  Its *carrier coefficient space* is the span of the carrier slices
`(i, j) ↦ Y (i, a) (j, b)` (the `multiplicityCarrierBlock`s), i.e. the image of `Y`
under all multiplicity-side linear functionals `(id ⊗ ψ)(Y)`.

* `multiplicityOne_incidenceFactorization_exact`: if this space lies in a line
  `ℂ D` with `D ≠ 0`, there is a unique `F` with `Y = D ⊗ F`
  (`eq:incidence-factorization`).
* `carrierCoefficientSpace_le_of_equivariance`: the "in particular" clause — a declared
  equivariance `(L_q ⊗ 1) Y = Y (R_q ⊗ 1)` whose carrier intertwiner space is the line
  `ℂ D` forces the carrier coefficient space into `ℂ D`.
* `multiplicitySliceSpan_kronecker`: on this branch the multiplicity coefficient
  space `𝔅_e` (span of the multiplicity slices `(a, b) ↦ Y (i, a) (j, b)`) is exactly the
  line `ℂ F`.
* `typedMultiplicity_line_reduction`, `typedMultiplicity_carrier_reduction`: the typed
  multiplicity equations `eq:typed-multiplicity` over `𝔅_e = ℂ F` (resp. the carrier-level
  commutation with `Y = D ⊗ F` and its adjoint) reduce to the two equations
  `R_μ F = F R_λ` and `R_λ F^* = F^* R_μ`.
-/

open Matrix
open scoped Kronecker

namespace RenewalGeometry

section CarrierCoefficientSpace

variable {n m g g' : Type*}

/-- The carrier coefficient space of an incidence operator: the span of its carrier
slices `(i, j) ↦ Y (i, a) (j, b)`, i.e. of all `(id ⊗ ψ)(Y)` over multiplicity-side
functionals `ψ` (`lem:multiplicity-factorization`, "prescribed carrier coefficient
space"). -/
def carrierCoefficientSpace (Y : Matrix (n × g') (m × g) ℂ) :
    Submodule ℂ (Matrix n m ℂ) :=
  Submodule.span ℂ (Set.range fun ab : g' × g => multiplicityCarrierBlock Y ab.1 ab.2)

theorem multiplicityCarrierBlock_mem_carrierCoefficientSpace
    (Y : Matrix (n × g') (m × g) ℂ) (a : g') (b : g) :
    multiplicityCarrierBlock Y a b ∈ carrierCoefficientSpace Y :=
  Submodule.subset_span ⟨(a, b), rfl⟩

/-- A multiplicity slice of an incidence operator: the matrix
`(a, b) ↦ Y (i, a) (j, b)`, i.e. `(φ ⊗ id)(Y)` for the carrier matrix-entry functional
`φ = E_{ij}^*` (`def:incidence-coefficients`). -/
def multiplicitySlice (Y : Matrix (n × g') (m × g) ℂ) (i : n) (j : m) :
    Matrix g' g ℂ :=
  fun a b => Y (i, a) (j, b)

/-- The span of the multiplicity slices: the intrinsic coefficient space `𝔅_e` of
`def:incidence-coefficients` in matrix coordinates. -/
def multiplicitySliceSpan (Y : Matrix (n × g') (m × g) ℂ) :
    Submodule ℂ (Matrix g' g ℂ) :=
  Submodule.span ℂ (Set.range fun ij : n × m => multiplicitySlice Y ij.1 ij.2)

theorem multiplicityCarrierBlock_kronecker (D : Matrix n m ℂ) (F : Matrix g' g ℂ)
    (a : g') (b : g) :
    multiplicityCarrierBlock (D ⊗ₖ F) a b = F a b • D := by
  ext i j
  simp [multiplicityCarrierBlock, Matrix.kroneckerMap_apply, mul_comm]

theorem multiplicitySlice_kronecker (D : Matrix n m ℂ) (F : Matrix g' g ℂ)
    (i : n) (j : m) :
    multiplicitySlice (D ⊗ₖ F) i j = D i j • F := by
  ext a b
  simp [multiplicitySlice, Matrix.kroneckerMap_apply]

/-- A Kronecker product `D ⊗ F` has carrier coefficient space inside the line `ℂ D`. -/
theorem carrierCoefficientSpace_kronecker_le (D : Matrix n m ℂ) (F : Matrix g' g ℂ) :
    carrierCoefficientSpace (D ⊗ₖ F) ≤ ℂ ∙ D := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  show multiplicityCarrierBlock (D ⊗ₖ F) a b ∈ ℂ ∙ D
  rw [multiplicityCarrierBlock_kronecker]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self D)

/-- On the multiplicity-one branch `Y = D ⊗ F` with `D ≠ 0`, the intrinsic coefficient
space `𝔅_e` is exactly the line `ℂ F`. -/
theorem multiplicitySliceSpan_kronecker (D : Matrix n m ℂ) (hD : D ≠ 0)
    (F : Matrix g' g ℂ) :
    multiplicitySliceSpan (D ⊗ₖ F) = ℂ ∙ F := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨i, j⟩, rfl⟩
    show multiplicitySlice (D ⊗ₖ F) i j ∈ ℂ ∙ F
    rw [multiplicitySlice_kronecker]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self F)
  · obtain ⟨i, j, hij⟩ : ∃ i j, D i j ≠ 0 := by
      by_contra hall
      apply hD
      ext i j
      rw [Matrix.zero_apply]
      by_contra hz
      exact hall ⟨i, j, hz⟩
    refine Submodule.span_le.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, hx]
    have hmem : multiplicitySlice (D ⊗ₖ F) i j ∈ multiplicitySliceSpan (D ⊗ₖ F) :=
      Submodule.subset_span ⟨(i, j), rfl⟩
    rw [multiplicitySlice_kronecker] at hmem
    have := Submodule.smul_mem (multiplicitySliceSpan (D ⊗ₖ F)) (D i j)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hij, one_smul] at this

end CarrierCoefficientSpace

section Factorization

variable {n m g g' : Type*} [Fintype n] [Fintype m] [Fintype g] [Fintype g']

/-- **Multiplicity-one incidence factorization (`lem:multiplicity-factorization`,
primary clause).**  If the carrier coefficient space of an edge lies in the line
`ℂ D` with `D ≠ 0`, the edge factorizes uniquely, relative to `D`, as
`Y = D ⊗ F` (`eq:incidence-factorization`). -/
theorem multiplicityOne_incidenceFactorization_exact
    (D : Matrix n m ℂ) (hD : D ≠ 0)
    (Y : Matrix (n × g') (m × g) ℂ)
    (hY : carrierCoefficientSpace Y ≤ ℂ ∙ D) :
    ∃! F : Matrix g' g ℂ, Y = D ⊗ₖ F := by
  classical
  have hblock : ∀ a b, ∃ c : ℂ, multiplicityCarrierBlock Y a b = c • D := by
    intro a b
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (hY (multiplicityCarrierBlock_mem_carrierCoefficientSpace Y a b))
    exact ⟨c, hc.symm⟩
  choose coeff hcoeff using hblock
  have hfactor : Y = D ⊗ₖ (fun a b => coeff a b) := by
    ext ia jb
    rcases ia with ⟨i, a⟩
    rcases jb with ⟨j, b⟩
    have hab := congrFun (congrFun (hcoeff a b) i) j
    simp only [multiplicityCarrierBlock, Matrix.smul_apply, smul_eq_mul] at hab
    change Y (i, a) (j, b) = D i j * coeff a b
    rw [hab, mul_comm]
  refine ⟨fun a b => coeff a b, hfactor, ?_⟩
  intro F' hF'
  exact GraphLoadedEdgeCommutant.kronecker_left_cancel hD (hF'.symm.trans hfactor)

omit [Fintype n] [Fintype m] in
/-- The carrier coefficient space is the line `ℂ D` (not just contained in it) as soon
as `Y ≠ 0`; with `Y = 0` the factorization is `0 = D ⊗ 0`. -/
theorem carrierCoefficientSpace_eq_of_kronecker
    (D : Matrix n m ℂ) (F : Matrix g' g ℂ) (hF : F ≠ 0) :
    carrierCoefficientSpace (D ⊗ₖ F) = ℂ ∙ D := by
  classical
  apply le_antisymm (carrierCoefficientSpace_kronecker_le D F)
  obtain ⟨a, b, hab⟩ : ∃ a b, F a b ≠ 0 := by
    by_contra hall
    apply hF
    ext a b
    rw [Matrix.zero_apply]
    by_contra hz
    exact hall ⟨a, b, hz⟩
  refine Submodule.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [SetLike.mem_coe, hx]
  have hmem := multiplicityCarrierBlock_mem_carrierCoefficientSpace (D ⊗ₖ F) a b
  rw [multiplicityCarrierBlock_kronecker] at hmem
  have := Submodule.smul_mem (carrierCoefficientSpace (D ⊗ₖ F)) (F a b)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hab, one_smul] at this

/-- **"In particular" clause of `lem:multiplicity-factorization`.**  A declared
equivariance `(L_q ⊗ 1) Y = Y (R_q ⊗ 1)` (acting trivially on the multiplicity factors)
whose carrier intertwiner space is the line `ℂ D` forces the carrier coefficient space
of `Y` into `ℂ D`. -/
theorem carrierCoefficientSpace_le_of_equivariance
    {κ : Type*} [DecidableEq g] [DecidableEq g']
    (L : κ → Matrix n n ℂ) (R : κ → Matrix m m ℂ)
    (D : Matrix n m ℂ)
    (hSchur : ∀ Z : Matrix n m ℂ, (∀ q, L q * Z = Z * R q) → ∃ c : ℂ, Z = c • D)
    (Y : Matrix (n × g') (m × g) ℂ)
    (hY : ∀ q, (L q ⊗ₖ (1 : Matrix g' g' ℂ)) * Y = Y * (R q ⊗ₖ (1 : Matrix g g ℂ))) :
    carrierCoefficientSpace Y ≤ ℂ ∙ D := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  obtain ⟨c, hc⟩ := hSchur _ (fun q => tensorEquivariance_multiplicityCarrierBlock L R Y hY q a b)
  show multiplicityCarrierBlock Y a b ∈ ℂ ∙ D
  rw [hc]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self D)

/-- Equivariant multiplicity-one factorization, derived from the intrinsic clause. -/
theorem multiplicityOne_incidenceFactorization_of_equivariance
    {κ : Type*} [DecidableEq g] [DecidableEq g']
    (L : κ → Matrix n n ℂ) (R : κ → Matrix m m ℂ)
    (D : Matrix n m ℂ) (hD : D ≠ 0)
    (hSchur : ∀ Z : Matrix n m ℂ, (∀ q, L q * Z = Z * R q) → ∃ c : ℂ, Z = c • D)
    (Y : Matrix (n × g') (m × g) ℂ)
    (hY : ∀ q, (L q ⊗ₖ (1 : Matrix g' g' ℂ)) * Y = Y * (R q ⊗ₖ (1 : Matrix g g ℂ))) :
    ∃! F : Matrix g' g ℂ, Y = D ⊗ₖ F :=
  multiplicityOne_incidenceFactorization_exact D hD Y
    (carrierCoefficientSpace_le_of_equivariance L R D hSchur Y hY)

end Factorization

section Reduction

variable {n m g g' : Type*} [Fintype n] [Fintype m] [Fintype g] [Fintype g']
  [DecidableEq n] [DecidableEq m] [DecidableEq g] [DecidableEq g']

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  [DecidableEq g] [DecidableEq g'] in
/-- **Reduction clause of `lem:multiplicity-factorization` (coefficient-space form).**
On the branch `𝔅_e = ℂ F`, the typed multiplicity equations `eq:typed-multiplicity`
(`R_μ B = B R_λ`, `R_λ B^* = B^* R_μ` for every `B ∈ 𝔅_e`) reduce to
`R_μ F = F R_λ` and `R_λ F^* = F^* R_μ`. -/
theorem typedMultiplicity_line_reduction
    (F : Matrix g' g ℂ) (Rtgt : Matrix g' g' ℂ) (Rsrc : Matrix g g ℂ) :
    (∀ B ∈ (ℂ ∙ F), Rtgt * B = B * Rsrc ∧ Rsrc * Bᴴ = Bᴴ * Rtgt) ↔
      (Rtgt * F = F * Rsrc ∧ Rsrc * Fᴴ = Fᴴ * Rtgt) := by
  constructor
  · intro h
    exact h F (Submodule.mem_span_singleton_self F)
  · rintro ⟨h1, h2⟩ B hB
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hB
    constructor
    · rw [Matrix.mul_smul, Matrix.smul_mul, h1]
    · rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, h2]

/-- **Reduction clause of `lem:multiplicity-factorization` (carrier form).**  For the
factorized edge `Y = D ⊗ F` with `D ≠ 0`, commutation of the block-diagonal multiplicity
operator `(1 ⊗ R_μ, 1 ⊗ R_λ)` with `Y` and `Y^*` is equivalent to the two multiplicity
equations. -/
theorem typedMultiplicity_carrier_reduction
    (D : Matrix n m ℂ) (hD : D ≠ 0) (F : Matrix g' g ℂ)
    (Rtgt : Matrix g' g' ℂ) (Rsrc : Matrix g g ℂ) :
    (((1 : Matrix n n ℂ) ⊗ₖ Rtgt) * (D ⊗ₖ F) = (D ⊗ₖ F) * ((1 : Matrix m m ℂ) ⊗ₖ Rsrc) ∧
      ((1 : Matrix m m ℂ) ⊗ₖ Rsrc) * (D ⊗ₖ F)ᴴ = (D ⊗ₖ F)ᴴ * ((1 : Matrix n n ℂ) ⊗ₖ Rtgt)) ↔
      (Rtgt * F = F * Rsrc ∧ Rsrc * Fᴴ = Fᴴ * Rtgt) := by
  have hDH : Dᴴ ≠ 0 := by
    intro hzero
    apply hD
    have := congrArg Matrix.conjTranspose hzero
    simpa using this
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
        Matrix.mul_one] at h1
      exact GraphLoadedEdgeCommutant.kronecker_left_cancel hD h1
    · rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one] at h2
      exact GraphLoadedEdgeCommutant.kronecker_left_cancel hDH h2
  · rintro ⟨h1, h2⟩
    constructor
    · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
        Matrix.mul_one, h1]
    · rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, h2]

end Reduction

end RenewalGeometry
