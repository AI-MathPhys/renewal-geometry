/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCARSecondQuantizationLieExact
import NCG.Flagship.V036MatterLegendre

/-!
# Nonlinear finite matter Legendre envelope

This module supplies the nonlinear envelope identities and pointwise Hessian
reciprocity used in `thm:SMST-matter-Legendre`.  They are stated along
arbitrary finite-dimensional directions, which is exactly the directional
form of `D_p H = v` and `D_z H = -D_z L`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace MatterLegendreEnvelope

variable {Z P : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- The Hamiltonian obtained by evaluating the Legendre envelope at its
stationary velocity selector. -/
def legendreHamiltonian (L : Z → P → ℝ) (velocity : Z → P → P)
    (z : Z) (p : P) : ℝ :=
  inner ℝ p (velocity z p) - L z (velocity z p)

/-- Momentum envelope identity.  If the selected velocity is differentiable
along a momentum direction and the Lagrangian derivative in that induced
velocity direction is the stationary pairing with `p`, then
`D_p H[ṗ] = ⟪ṗ,v⟫`. -/
theorem momentum_envelope_direction
    (L : Z → P → ℝ) (velocity : Z → P → P)
    (z : Z) (p pdot vdot : P)
    (hv : HasDerivAt (fun t : ℝ => velocity z (p + t • pdot)) vdot 0)
    (hL : HasDerivAt
      (fun t : ℝ => L z (velocity z (p + t • pdot)))
      (inner ℝ p vdot) 0) :
    HasDerivAt
      (fun t : ℝ => legendreHamiltonian L velocity z (p + t • pdot))
      (inner ℝ pdot (velocity z p)) 0 := by
  have hp : HasDerivAt (fun t : ℝ => p + t • pdot) pdot 0 := by
    have ht : HasDerivAt (fun t : ℝ => t • pdot) pdot 0 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) 0).smul_const pdot
    exact ht.const_add p
  have hpair := hp.inner ℝ hv
  have h := hpair.sub hL
  change HasDerivAt
    ((fun t : ℝ => inner ℝ (p + t • pdot)
        (velocity z (p + t • pdot))) -
      (fun t : ℝ => L z (velocity z (p + t • pdot))))
    (inner ℝ pdot (velocity z p)) 0
  simpa using h

/-- Configuration envelope identity.  Along any configuration direction,
the velocity-response terms cancel at stationarity and
`D_z H[ż] = -D_z L[ż]`. -/
theorem configuration_envelope_direction
    (L : Z → P → ℝ) (velocity : Z → P → P)
    (z zdot : Z) (p vdot : P) (DzL : ℝ)
    (hv : HasDerivAt
      (fun t : ℝ => velocity (z + t • zdot) p) vdot 0)
    (hL : HasDerivAt
      (fun t : ℝ => L (z + t • zdot) (velocity (z + t • zdot) p))
      (DzL + inner ℝ p vdot) 0) :
    HasDerivAt
      (fun t : ℝ => legendreHamiltonian L velocity (z + t • zdot) p)
      (-DzL) 0 := by
  have hp : HasDerivAt (fun _ : ℝ => p) 0 0 := hasDerivAt_const 0 p
  have hpair := hp.inner ℝ hv
  have h := hpair.sub hL
  change HasDerivAt
    ((fun t : ℝ => inner ℝ p (velocity (z + t • zdot) p)) -
      (fun t : ℝ => L (z + t • zdot) (velocity (z + t • zdot) p)))
    (-DzL) 0
  simpa using h

/-- Differentiating the stationary equation `p=D_vL` gives
`D²_{vv}L · D²_{pp}H=I`; positive definiteness then identifies the
Hamiltonian Hessian with the inverse Lagrangian Hessian. -/
theorem hessian_reciprocity
    {v : Type*} [Fintype v] [DecidableEq v]
    (K J : Matrix v v ℂ) (hK : K.PosDef)
    (hstationary : K * J = 1) :
    J = K⁻¹ := by
  haveI := hK.isUnit.invertible
  calc
    J = 1 * J := (Matrix.one_mul J).symm
    _ = (K⁻¹ * K) * J := by rw [Matrix.inv_mul_of_invertible]
    _ = K⁻¹ * (K * J) := Matrix.mul_assoc _ _ _
    _ = K⁻¹ := by rw [hstationary, Matrix.mul_one]

/-- Consolidated nonlinear envelope and Hessian certificate. -/
theorem nonlinear_legendre_envelope
    (L : Z → P → ℝ) (velocity : Z → P → P)
    (z zdot : Z) (p pdot vp vz : P) (DzL : ℝ)
    (hvp : HasDerivAt (fun t : ℝ => velocity z (p + t • pdot)) vp 0)
    (hLp : HasDerivAt
      (fun t : ℝ => L z (velocity z (p + t • pdot)))
      (inner ℝ p vp) 0)
    (hvz : HasDerivAt
      (fun t : ℝ => velocity (z + t • zdot) p) vz 0)
    (hLz : HasDerivAt
      (fun t : ℝ => L (z + t • zdot) (velocity (z + t • zdot) p))
      (DzL + inner ℝ p vz) 0) :
    HasDerivAt
      (fun t : ℝ => legendreHamiltonian L velocity z (p + t • pdot))
      (inner ℝ pdot (velocity z p)) 0 ∧
    HasDerivAt
      (fun t : ℝ => legendreHamiltonian L velocity (z + t • zdot) p)
      (-DzL) 0 :=
  ⟨momentum_envelope_direction L velocity z p pdot vp hvp hLp,
    configuration_envelope_direction L velocity z zdot p vz DzL hvz hLz⟩

end MatterLegendreEnvelope
end NCG
