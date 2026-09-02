/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CartanInjectivityExact

/-!
# Exact connection variation for the Palatini--Holst action

This closes the variational gap left by `PotentialPalatini`.  On a real
Hilbert space of connection coefficients, the covariant curvature variation
is represented by a bounded linear map.  The boundary-free integration by
parts identity gives the exact Euler vector `-D(PB) - Sigma`; stationarity
against every connection perturbation forces that vector to vanish.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace NCG.PalatiniConnectionVariation

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The connection-dependent affine Palatini--Holst action. -/
def connectionAction (curvatureVariation : W →L[ℝ] W)
    (PB spin connection : W) : ℝ :=
  inner ℝ (curvatureVariation connection) PB - inner ℝ connection spin

/-- Exact first-variation identity after covariant integration by parts.  The
vector `covariantPB` represents `D(P_{alpha,beta} B)`. -/
theorem connectionAction_increment
    (curvatureVariation : W →L[ℝ] W) (PB spin covariantPB connection δω : W)
    (hibp : ∀ v : W,
      inner ℝ (curvatureVariation v) PB = -inner ℝ v covariantPB)
    (t : ℝ) :
    connectionAction curvatureVariation PB spin (connection + t • δω) -
        connectionAction curvatureVariation PB spin connection =
      t * inner ℝ δω (-covariantPB - spin) := by
  simp only [connectionAction, map_add, map_smul, inner_add_left,
    inner_smul_left, inner_sub_right, inner_neg_right, hibp,
    starRingEnd_apply, star_trivial]
  ring

/-- Connection stationarity against every perturbation is exactly the Euler
equation `-D(PB) - Sigma = 0`. -/
theorem connection_stationarity_euler
    (curvatureVariation : W →L[ℝ] W) (PB spin covariantPB connection : W)
    (hibp : ∀ v : W,
      inner ℝ (curvatureVariation v) PB = -inner ℝ v covariantPB)
    (hstationary : ∀ δω : W,
      connectionAction curvatureVariation PB spin (connection + δω) =
        connectionAction curvatureVariation PB spin connection) :
    -covariantPB - spin = 0 := by
  let euler : W := -covariantPB - spin
  have hinc := connectionAction_increment curvatureVariation PB spin
    covariantPB connection euler hibp 1
  have hzero : connectionAction curvatureVariation PB spin
      (connection + (1 : ℝ) • euler) -
      connectionAction curvatureVariation PB spin connection = 0 := by
    rw [one_smul, hstationary euler, sub_self]
  rw [hzero] at hinc
  have hinner : inner ℝ euler euler = 0 := by
    simpa [euler] using hinc.symm
  exact (inner_self_eq_zero.mp hinner : euler = 0)

/-- The full connection-stationarity/torsion packet: exact Euler equation,
spinless Cartan torsion vanishing, and the finite-cutoff singular-value bound. -/
theorem palatini_connection_torsion_packet
    (curvatureVariation : W →L[ℝ] W) (PB covariantPB connection : W)
    (hibp : ∀ v : W,
      inner ℝ (curvatureVariation v) PB = -inner ℝ v covariantPB)
    (hstationary : ∀ δω : W,
      connectionAction curvatureVariation PB 0 (connection + δω) =
        connectionAction curvatureVariation PB 0 connection)
    {A : Type*} [Ring A] [Algebra ℝ A]
    (J : A) (hJ : J * J = -1) (α β : ℝ)
    (hab : α ^ 2 + β ^ 2 ≠ 0)
    {V U : Type} [NormedAddCommGroup V] [NormedAddCommGroup U]
    (K : V → U) (Pmap : U → U) (z T : V)
    (hPinj : Function.Injective Pmap)
    (hKinj : ∀ v, K v = K z → v = z)
    (hCartanStationary : Pmap (K T) = Pmap (K z))
    (w : U) (κ : ℝ) (hκ : 0 < κ)
    (hfloor : ∀ v, κ * ‖v‖ ≤ ‖K v‖) (hKT : K T = w) :
    (-covariantPB = 0) ∧
    T = z ∧
    ‖T‖ ≤ κ⁻¹ * ‖w‖ ∧
    ((α • J + β • (1 : A)) *
      ((α ^ 2 + β ^ 2)⁻¹ • (β • (1 : A) - α • J)) = 1) ∧
    (((α ^ 2 + β ^ 2)⁻¹ • (β • (1 : A) - α • J)) *
      (α • J + β • (1 : A)) = 1) := by
  have heuler := connection_stationarity_euler curvatureVariation PB 0
    covariantPB connection hibp hstationary
  have hcov : -covariantPB = 0 := by simpa using heuler
  have htorsion : T = z :=
    NCG.CartanInjectivity.spinless_torsion_zero K Pmap z hPinj hKinj T
      hCartanStationary
  obtain ⟨hinvLeft, hinvRight, hbound⟩ :=
    NCG.palatini_torsion_core J hJ α β hab
  exact ⟨hcov, htorsion, hbound (V := V) (W := U) K T w κ hκ hfloor hKT,
    hinvLeft, hinvRight⟩

end NCG.PalatiniConnectionVariation
