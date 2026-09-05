/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Unitary assembly of finitely many orthogonal sectors

This module proves the carrier-assembly step used in finite commutant
decompositions. A finite family of self-adjoint linear projections with
pairwise-zero products and sum equal to the identity decomposes the Hilbert
carrier unitarily as the finite L2-direct sum of their ranges.
-/

noncomputable section

open scoped BigOperators

namespace NCG
namespace FiniteOrthogonalSectorDecomposition

variable {Λ H : Type*} [Fintype Λ] [DecidableEq Λ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The sector cut out by one member of a projection family. -/
def sectorRange (P : Λ → H →ₗ[ℂ] H) (i : Λ) : Submodule ℂ H :=
  LinearMap.range (P i)

/-- Assembly of a finite family of sector vectors. -/
def assembleSectors (P : Λ → H →ₗ[ℂ] H) :
    PiLp 2 (fun i => sectorRange P i) →ₗ[ℂ] H where
  toFun v := ∑ i, (v i).1
  map_add' v w := by
    simp only [PiLp.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [PiLp.smul_apply, RingHom.id_apply, Submodule.coe_smul]
    exact Finset.smul_sum.symm

omit [Fintype Λ] [DecidableEq Λ] in
theorem sector_inner_eq_zero
    (P : Λ → H →ₗ[ℂ] H)
    (hself : ∀ i x y, inner ℂ (P i x) y = inner ℂ x (P i y))
    (horth : ∀ i j, i ≠ j → (P i).comp (P j) = 0)
    {i j : Λ} (hij : i ≠ j)
    (x : sectorRange P i) (y : sectorRange P j) :
    inner ℂ x.1 y.1 = 0 := by
  obtain ⟨u, hu⟩ := x.2
  obtain ⟨v, hv⟩ := y.2
  rw [← hu, ← hv, hself]
  have hzero := LinearMap.congr_fun (horth i j hij) v
  change P i (P j v) = 0 at hzero
  rw [hzero]
  simp

omit [DecidableEq Λ] in
/-- Pairwise orthogonality turns the inner product of two assembled vectors
into the sum of the sector inner products. -/
theorem inner_assembleSectors
    (P : Λ → H →ₗ[ℂ] H)
    (hself : ∀ i x y, inner ℂ (P i x) y = inner ℂ x (P i y))
    (horth : ∀ i j, i ≠ j → (P i).comp (P j) = 0)
    (v w : PiLp 2 (fun i => sectorRange P i)) :
    inner ℂ (assembleSectors P v) (assembleSectors P w) =
      ∑ i, inner ℂ (v i) (w i) := by
  simp only [assembleSectors, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single i]
  · rfl
  · intro j hj hji
    exact sector_inner_eq_zero P hself horth hji.symm (v i) (w j)
  · simp

/-- Assembly is an isometry for an orthogonal projection family. -/
def sectorAssemblyIsometry
    (P : Λ → H →ₗ[ℂ] H)
    (hself : ∀ i x y, inner ℂ (P i x) y = inner ℂ x (P i y))
    (horth : ∀ i j, i ≠ j → (P i).comp (P j) = 0) :
    PiLp 2 (fun i => sectorRange P i) →ₗᵢ[ℂ] H where
  toLinearMap := assembleSectors P
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    calc
      ‖assembleSectors P v‖ ^ 2 =
          RCLike.re (inner ℂ (assembleSectors P v)
            (assembleSectors P v)) := norm_sq_eq_re_inner _
      _ = RCLike.re (inner ℂ v v) := by
        rw [PiLp.inner_apply, inner_assembleSectors P hself horth]
      _ = ‖v‖ ^ 2 := (norm_sq_eq_re_inner _).symm

omit [DecidableEq Λ] in
theorem sectorAssemblyIsometry_surjective
    (P : Λ → H →ₗ[ℂ] H)
    (hself : ∀ i x y, inner ℂ (P i x) y = inner ℂ x (P i y))
    (horth : ∀ i j, i ≠ j → (P i).comp (P j) = 0)
    (hsum : ∀ x, ∑ i, P i x = x) :
    Function.Surjective (sectorAssemblyIsometry P hself horth) := by
  intro x
  let v : PiLp 2 (fun i => sectorRange P i) :=
    WithLp.toLp 2 (fun i => ⟨P i x, ⟨x, rfl⟩⟩)
  refine ⟨v, ?_⟩
  change ∑ i, P i x = x
  exact hsum x

/-- A finite self-adjoint orthogonal resolution of the identity gives a
unitary direct-sum decomposition of the carrier. -/
def orthogonalSectorUnitaryEquiv
    (P : Λ → H →ₗ[ℂ] H)
    (hself : ∀ i x y, inner ℂ (P i x) y = inner ℂ x (P i y))
    (horth : ∀ i j, i ≠ j → (P i).comp (P j) = 0)
    (hsum : ∀ x, ∑ i, P i x = x) :
    PiLp 2 (fun i => sectorRange P i) ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (sectorAssemblyIsometry P hself horth)
    (sectorAssemblyIsometry_surjective P hself horth hsum)

end FiniteOrthogonalSectorDecomposition
end NCG
