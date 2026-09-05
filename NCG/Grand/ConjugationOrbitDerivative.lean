/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.OrbitHodgeTransfer
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# equivariant differentiation of the conjugation orbit

This file closes the only clause missing from the finite orbit--Hodge transfer:
the derivative at the identity of `exp(-tX) G exp(tX)` is `[G,X]`, and the
chain rule for an equivariant finite export sends the full-cell commutator
source to the exported commutator source.  Derivative uniqueness supplies the
advertised unique orbit derivative.
-/

namespace NCG

variable {A : Type*} [CStarAlgebra A]

/-- The conjugation orbit `exp(-tX) G exp(tX)`, componentwise. -/
noncomputable def conjugationOrbit {I : Type*}
    (X : A) (G : I → A) (t : ℂ) (i : I) : A :=
  NormedSpace.exp (t • (-X)) * G i * NormedSpace.exp (t • X)

/-- The tangent source of the conjugation orbit. -/
def orbitCommutator {I : Type*} (X : A) (G : I → A) (i : I) : A :=
  G i * X - X * G i

/-- Componentwise differentiation of the exponential conjugation path. -/
theorem hasDerivAt_conjugationOrbit_component {I : Type*}
    (X : A) (G : I → A) (i : I) :
    HasDerivAt (fun t : ℂ => conjugationOrbit X G t i)
      (orbitCommutator X G i) 0 := by
  have hneg : HasDerivAt (fun t : ℂ => NormedSpace.exp (t • (-X))) (-X) 0 := by
    simpa using hasDerivAt_exp_smul_const (-X) (0 : ℂ)
  have hpos : HasDerivAt (fun t : ℂ => NormedSpace.exp (t • X)) X 0 := by
    simpa using hasDerivAt_exp_smul_const X (0 : ℂ)
  have h := (hneg.mul_const (G i)).mul hpos
  convert h using 1
  · funext t
    rfl
  · simp [orbitCommutator, sub_eq_add_neg, add_comm]

/-- The whole finite tuple has derivative equal to its stacked commutator
source. -/
theorem hasDerivAt_conjugationOrbit {I : Type*} [Fintype I]
    (X : A) (G : I → A) :
    HasDerivAt (fun t : ℂ => conjugationOrbit X G t)
      (orbitCommutator X G) 0 := by
  rw [hasDerivAt_pi]
  exact fun i => hasDerivAt_conjugationOrbit_component X G i

@[simp] theorem conjugationOrbit_zero {I : Type*}
    (X : A) (G : I → A) : conjugationOrbit X G 0 = G := by
  funext i
  simp [conjugationOrbit]

/-- Differentiating an equivariant finite export gives exactly the commutator
source chain rule `J_c = D_orb Φ_G J_G`. -/
theorem equivariant_orbit_derivative
    {I K : Type*} [Fintype I] [Fintype K]
    (X : A) (G : I → A) (c : K → A)
    (Φ : (I → A) → (K → A))
    (D : (I → A) →L[ℂ] (K → A))
    (hΦ : HasFDerivAt Φ D G)
    (hequiv : ∀ t : ℂ,
      Φ (conjugationOrbit X G t) = conjugationOrbit X c t) :
    D (orbitCommutator X G) = orbitCommutator X c := by
  have hpath := hasDerivAt_conjugationOrbit X G
  have hΦ0 : HasFDerivAt Φ D (conjugationOrbit X G 0) := by
    simpa using hΦ
  have hchain := hΦ0.comp_hasDerivAt (x := (0 : ℂ)) hpath
  have hchain' : HasDerivAt (fun t : ℂ => conjugationOrbit X c t)
      (D (orbitCommutator X G)) 0 :=
    hchain.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => (hequiv t).symm)
  exact hchain'.unique (hasDerivAt_conjugationOrbit X c)

/-- The equivariant orbit derivative is unique, and its unique value is the
exported commutator source. -/
theorem equivariant_orbit_derivative_unique
    {I K : Type*} [Fintype I] [Fintype K]
    (X : A) (G : I → A) (c : K → A)
    (Φ : (I → A) → (K → A))
    (D : (I → A) →L[ℂ] (K → A))
    (hΦ : HasFDerivAt Φ D G)
    (hequiv : ∀ t : ℂ,
      Φ (conjugationOrbit X G t) = conjugationOrbit X c t) :
    ∃! v : K → A,
      HasDerivAt (fun t : ℂ => Φ (conjugationOrbit X G t)) v 0 := by
  refine ⟨orbitCommutator X c, ?_, ?_⟩
  · have hpath := hasDerivAt_conjugationOrbit X G
    have hΦ0 : HasFDerivAt Φ D (conjugationOrbit X G 0) := by
      simpa using hΦ
    exact (hΦ0.comp_hasDerivAt (x := (0 : ℂ)) hpath).congr_deriv
      (equivariant_orbit_derivative X G c Φ D hΦ hequiv)
  · intro v hv
    exact hv.unique
      ((hasDerivAt_conjugationOrbit X c).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => hequiv t))

end NCG
