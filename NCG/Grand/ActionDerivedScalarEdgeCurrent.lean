/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Action-derived scalar edge current

This file develops the finite-dimensional canonical Poisson-bracket
calculation behind the scalar-current corollary.  A transported kinetic metric
appears in the edge gradient energy and its inverse appears in the momentum
energy.  Metric compatibility makes them cancel, leaving the symmetrized
transported momentum current.  A local potential cancels separately under
lapse antisymmetrization, and summing the edge identity gives the smeared
finite-lattice bracket.
-/

open Matrix

namespace NCG

/-- Cancellation of the target kinetic metric against its Hamiltonian inverse. -/
theorem targetKineticMetric_inverse_cancellation
    {d : Type*} [Fintype d] [DecidableEq d]
    (K Kinv : Matrix d d ℝ) (hKsym : Kᵀ = K) (hKinv : K * Kinv = 1)
    (a p : d → ℝ) :
    (K.mulVec a) ⬝ᵥ (Kinv.mulVec p) = a ⬝ᵥ p := by
  calc
    (K.mulVec a) ⬝ᵥ (Kinv.mulVec p)
        = (Kinv.mulVec p) ⬝ᵥ (K.mulVec a) := dotProduct_comm _ _
    _ = a ⬝ᵥ Kᵀ.mulVec (Kinv.mulVec p) := by
          rw [Matrix.dotProduct_transpose_mulVec]
    _ = a ⬝ᵥ (K * Kinv).mulVec p := by
          rw [hKsym, Matrix.mulVec_mulVec]
    _ = a ⬝ᵥ p := by rw [hKinv, Matrix.one_mulVec]

/-- Cancellation at the source endpoint.  Compatibility transports the
source momentum before pairing with the edge difference. -/
theorem transportedKineticMetric_inverse_cancellation
    {d : Type*} [Fintype d] [DecidableEq d]
    (Kx Ky KxInv U : Matrix d d ℝ)
    (hKysym : Kyᵀ = Ky) (hKxInv : Kx * KxInv = 1)
    (hcompat : Ky * U = U * Kx) (a p : d → ℝ) :
    ((Uᵀ * Ky).mulVec a) ⬝ᵥ (KxInv.mulVec p) =
      a ⬝ᵥ U.mulVec p := by
  calc
    ((Uᵀ * Ky).mulVec a) ⬝ᵥ (KxInv.mulVec p)
        = (KxInv.mulVec p) ⬝ᵥ (Uᵀ * Ky).mulVec a := dotProduct_comm _ _
    _ = (KxInv.mulVec p) ⬝ᵥ Uᵀ.mulVec (Ky.mulVec a) := by
          rw [← Matrix.mulVec_mulVec]
    _ = (Ky.mulVec a) ⬝ᵥ U.mulVec (KxInv.mulVec p) := by
          rw [Matrix.dotProduct_transpose_mulVec]
    _ = a ⬝ᵥ Kyᵀ.mulVec (U.mulVec (KxInv.mulVec p)) := by
          rw [dotProduct_comm (Ky.mulVec a),
            ← Matrix.dotProduct_transpose_mulVec]
    _ = a ⬝ᵥ (Ky * U * KxInv).mulVec p := by
          rw [hKysym, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = a ⬝ᵥ U.mulVec p := by
          rw [hcompat, Matrix.mul_assoc, hKxInv, Matrix.mul_one]

/-- The scalar current carried by one oriented edge `x → y`. -/
noncomputable def scalarEdgeCurrent
    {d : Type*} [Fintype d]
    (w : ℝ) (U : Matrix d d ℝ) (δ px py : d → ℝ) : ℝ :=
  (w / 2) * (δ ⬝ᵥ (U.mulVec px + py))

/-- The edge contribution obtained directly by pairing the canonical field
and momentum gradients of the two smeared Hamiltonians. -/
noncomputable def scalarEdgeCanonicalBracket
    {d : Type*} [Fintype d]
    (_Kx Ky KxInv KyInv U : Matrix d d ℝ)
    (w Nx Ny Mx My : ℝ) (δ px py : d → ℝ) : ℝ :=
  let aN := (Nx + Ny) * w / 2
  let aM := (Mx + My) * w / 2
  ((-aN) • ((Uᵀ * Ky).mulVec δ)) ⬝ᵥ (Mx • KxInv.mulVec px)
    - (Nx • KxInv.mulVec px) ⬝ᵥ ((-aM) • ((Uᵀ * Ky).mulVec δ))
    + (aN • Ky.mulVec δ) ⬝ᵥ (My • KyInv.mulVec py)
    - (Ny • KyInv.mulVec py) ⬝ᵥ (aM • Ky.mulVec δ)

/-- Exact one-edge Poisson-bracket identity. -/
theorem scalarEdgeCanonicalBracket_eq_lapseWedge_current
    {d : Type*} [Fintype d] [DecidableEq d]
    (Kx Ky KxInv KyInv U : Matrix d d ℝ)
    (hKysym : Kyᵀ = Ky)
    (hKxInv : Kx * KxInv = 1) (hKyInv : Ky * KyInv = 1)
    (hcompat : Ky * U = U * Kx)
    (w Nx Ny Mx My : ℝ) (δ px py : d → ℝ) :
    scalarEdgeCanonicalBracket Kx Ky KxInv KyInv U
        w Nx Ny Mx My δ px py =
      (Nx * My - Mx * Ny) * scalarEdgeCurrent w U δ px py := by
  have hx := transportedKineticMetric_inverse_cancellation
    Kx Ky KxInv U hKysym hKxInv hcompat δ px
  have hy := targetKineticMetric_inverse_cancellation
    Ky KyInv hKysym hKyInv δ py
  simp only [scalarEdgeCanonicalBracket, scalarEdgeCurrent,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hx, hy]
  rw [dotProduct_comm (KxInv.mulVec px) ((Uᵀ * Ky).mulVec δ), hx]
  rw [dotProduct_comm (KyInv.mulVec py) (Ky.mulVec δ), hy]
  rw [dotProduct_add]
  ring

/-- A point-local scalar potential makes no contribution to the
lapse-antisymmetrized canonical bracket. -/
theorem localScalarPotential_lapseAntisymmetrization_zero
    {d : Type*} [Fintype d]
    (Kinv : Matrix d d ℝ) (force p : d → ℝ) (Nx Mx : ℝ) :
    (Nx • force) ⬝ᵥ (Mx • Kinv.mulVec p)
      - (Nx • Kinv.mulVec p) ⬝ᵥ (Mx • force) = 0 := by
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm (Kinv.mulVec p) force]
  ring

/-- Summing the action-derived edge identities gives the exact smeared scalar
current bracket `D_sc(ω(N,M))`. -/
theorem finiteScalarAction_poissonBracket_eq_edgeCurrentSum
    {E : Type*} [Fintype E]
    (edgeBracket edgeCurrent : E → ℝ)
    (omega : E → ℝ)
    (hedge : ∀ e, edgeBracket e = omega e * edgeCurrent e) :
    (∑ e, edgeBracket e) = ∑ e, omega e * edgeCurrent e := by
  apply Finset.sum_congr rfl
  intro e _
  exact hedge e

/-- Transported field difference on an oriented edge. -/
def transportedScalarEdgeDifference
    {V E d : Type*} [Fintype d]
    (src dst : E → V) (U : E → Matrix d d ℝ)
    (φ : V → d → ℝ) (e : E) : d → ℝ :=
  φ (dst e) - (U e).mulVec (φ (src e))

/-- Complete finite-lattice form of the action-derived current identity.  The
left side is the sum of canonical endpoint-gradient pairings; the right side
is `D_sc(ω(N,M))` with
`ω_e = N_src M_dst - M_src N_dst` and the displayed symmetrized current. -/
theorem finiteTransportedScalarAction_poissonBracket
    {V E d : Type*} [Fintype E] [Fintype d] [DecidableEq d]
    (src dst : E → V) (K Kinv : V → Matrix d d ℝ)
    (U : E → Matrix d d ℝ) (w : E → ℝ)
    (hKsym : ∀ x, (K x)ᵀ = K x)
    (hKinv : ∀ x, K x * Kinv x = 1)
    (hcompat : ∀ e, K (dst e) * U e = U e * K (src e))
    (φ p : V → d → ℝ) (N M : V → ℝ) :
    (∑ e, scalarEdgeCanonicalBracket
      (K (src e)) (K (dst e)) (Kinv (src e)) (Kinv (dst e)) (U e)
      (w e) (N (src e)) (N (dst e)) (M (src e)) (M (dst e))
      (transportedScalarEdgeDifference src dst U φ e)
      (p (src e)) (p (dst e))) =
    ∑ e, (N (src e) * M (dst e) - M (src e) * N (dst e)) *
      scalarEdgeCurrent (w e) (U e)
        (transportedScalarEdgeDifference src dst U φ e)
        (p (src e)) (p (dst e)) := by
  apply finiteScalarAction_poissonBracket_eq_edgeCurrentSum
  intro e
  exact scalarEdgeCanonicalBracket_eq_lapseWedge_current
    (K (src e)) (K (dst e)) (Kinv (src e)) (Kinv (dst e)) (U e)
    (hKsym (dst e)) (hKinv (src e)) (hKinv (dst e)) (hcompat e)
    (w e) (N (src e)) (N (dst e)) (M (src e)) (M (dst e))
    (transportedScalarEdgeDifference src dst U φ e)
    (p (src e)) (p (dst e))

end NCG
