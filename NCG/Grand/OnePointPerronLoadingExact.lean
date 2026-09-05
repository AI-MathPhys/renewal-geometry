/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniversalCoupledActionCarrier

/-!
# Exact Perron transport under one-point vacuum loading

This file completes CA.9 beyond rank preservation.  A one-point internal
factor gives an explicit linear equivalence of vector spaces, intertwines the
loaded matrix with the original matrix, and therefore preserves every
eigenvalue, normalized Perron vector, and pressure computed from the positive
Perron eigenvalue.
-/

open Matrix Kronecker

namespace NCG
namespace OnePointPerronLoading

variable {p u : Type*} [Fintype p] [Fintype u]
variable [DecidableEq p] [DecidableEq u] [Unique u]

/-- Lift a gravitational vector to the unique internal vacuum point. -/
def liftVector : (p → ℂ) →ₗ[ℂ] (p × u → ℂ) where
  toFun r := fun x => r x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restrict a total vector to the unique internal vacuum point. -/
def restrictVector : (p × u → ℂ) →ₗ[ℂ] (p → ℂ) where
  toFun r := fun i => r (i, default)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictVector_liftVector (r : p → ℂ) :
    restrictVector (liftVector (u := u) r) = r := by
  rfl

@[simp] theorem liftVector_restrictVector (r : p × u → ℂ) :
    liftVector (restrictVector r) = r := by
  funext x
  cases x with
  | mk i a =>
      have ha : a = default := Subsingleton.elim _ _
      subst a
      rfl

/-- The one-point lift is a literal linear equivalence. -/
def vectorEquiv : (p → ℂ) ≃ₗ[ℂ] (p × u → ℂ) where
  toFun := liftVector
  invFun := restrictVector
  left_inv := restrictVector_liftVector
  right_inv := liftVector_restrictVector
  map_add' := LinearMap.map_add liftVector
  map_smul' := LinearMap.map_smul liftVector

/-- The Kronecker-loaded matrix intertwines the lifted vector with the
original matrix action. -/
theorem kroneckerOne_mulVec_lift (Q : Matrix p p ℂ) (r : p → ℂ) :
    (Q ⊗ₖ (1 : Matrix u u ℂ)).mulVec (liftVector r) =
      liftVector (Q.mulVec r) := by
  ext x
  rcases x with ⟨i, a⟩
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp [liftVector, Matrix.kroneckerMap_apply]

/-- Every eigenpair is preserved and reflected by one-point loading. -/
theorem loaded_eigenpair_iff (Q : Matrix p p ℂ) (r : p → ℂ) (ψ : ℂ) :
    (Q ⊗ₖ (1 : Matrix u u ℂ)).mulVec (liftVector r) =
        ψ • liftVector r ↔
      Q.mulVec r = ψ • r := by
  rw [kroneckerOne_mulVec_lift]
  constructor
  · intro h
    exact (liftVector_injective h)
  · intro h
    rw [h]
    exact LinearMap.map_smul _ _ _
  where
    liftVector_injective : Function.Injective
        (liftVector (p := p) (u := u)) :=
      Function.LeftInverse.injective restrictVector_liftVector

/-- Normalization by any linear functional is transported without change. -/
theorem loaded_normalization_iff
    (Q : Matrix p p ℂ) (normalize : (p → ℂ) →ₗ[ℂ] ℂ)
    (r : p → ℂ) (ψ : ℂ) :
    ((Q ⊗ₖ (1 : Matrix u u ℂ)).mulVec (liftVector (u := u) r) =
          ψ • liftVector (u := u) r ∧
        normalize (restrictVector (u := u) (liftVector (u := u) r)) = 1) ↔
      (Q.mulVec r = ψ • r ∧ normalize r = 1) := by
  simp [loaded_eigenpair_iff (u := u)]

/-- Uniqueness of a normalized Perron vector is preserved on the total
one-point-loaded carrier. -/
theorem unique_normalized_eigenvector_transport
    (Q : Matrix p p ℂ) (normalize : (p → ℂ) →ₗ[ℂ] ℂ)
    (r : p → ℂ) (ψ : ℂ)
    (huniq : ∀ z, Q.mulVec z = ψ • z → normalize z = 1 → z = r) :
    ∀ z : p × u → ℂ,
      (Q ⊗ₖ (1 : Matrix u u ℂ)).mulVec z = ψ • z →
      normalize (restrictVector (u := u) z) = 1 →
      z = liftVector (u := u) r := by
  intro z hz hn
  rw [← liftVector_restrictVector z] at hz ⊢
  apply congrArg (liftVector (u := u))
  exact huniq (restrictVector (u := u) z)
    ((loaded_eigenpair_iff (u := u) Q (restrictVector (u := u) z) ψ).1 hz) hn

/-- Pressure assigned to a positive Perron eigenvalue. -/
noncomputable def perronPressure (ρ : ℝ) : ℝ := Real.log ρ

/-- The loaded Perron eigenpair has exactly the original eigenvalue, so the
pressure computed from that eigenvalue is unchanged. -/
theorem perronPressure_onePointLoading
    (Q : Matrix p p ℂ) (r : p → ℂ) (ρ : ℝ)
    (heig : Q.mulVec r = (ρ : ℂ) • r) :
    (Q ⊗ₖ (1 : Matrix u u ℂ)).mulVec (liftVector r) =
        (ρ : ℂ) • liftVector r
      ∧ perronPressure ρ = Real.log ρ := by
  exact ⟨(loaded_eigenpair_iff Q r (ρ : ℂ)).2 heig, rfl⟩

/-- Squared entrywise discrepancy between two finite rows. -/
noncomputable def rowSquaredGap (A B : Matrix (p × u) (p × u) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j - B i j)

/-- Once provenance, accepted, and action reconstructions are all the unique
one-point-loaded row, both manuscript gaps vanish literally. -/
theorem commonProvenance_and_acceptedAction_gaps_zero
    (Qprov Qacc Qact : Matrix (p × u) (p × u) ℂ)
    (Q : Matrix p p ℂ)
    (hprov : Qprov = Q ⊗ₖ (1 : Matrix u u ℂ))
    (hacc : Qacc = Q ⊗ₖ (1 : Matrix u u ℂ))
    (hact : Qact = Q ⊗ₖ (1 : Matrix u u ℂ)) :
    rowSquaredGap Qprov Qact = 0 ∧ rowSquaredGap Qacc Qact = 0 := by
  subst Qprov
  subst Qacc
  subst Qact
  simp [rowSquaredGap]

/-- Complete CA.9 packet: the displayed driven row, unchanged rank,
intertwined eigenvector, and unchanged pressure. -/
theorem onePointPerronLoading_exact (Q : Matrix p p ℂ) (r : p → ℂ) (ψ : ℂ) :
    (∀ i j, (Q ⊗ₖ (1 : Matrix u u ℂ)) (i, default) (j, default) = Q i j) ∧
    Matrix.rank (Q ⊗ₖ (1 : Matrix u u ℂ)) = Matrix.rank Q ∧
    ((Q ⊗ₖ (1 : Matrix u u ℂ)).mulVec (liftVector r) =
        ψ • liftVector r ↔ Q.mulVec r = ψ • r) := by
  exact ⟨(onePointVacuumLoading Q).1, (onePointVacuumLoading Q).2,
    loaded_eigenpair_iff Q r ψ⟩

end OnePointPerronLoading
end NCG
