/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpinNetwork
import NCG.Grand.FinitePeterWeylDecomposition
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthonormal basis of finite gauge-invariant holonomy functions

For a finite graph and finite gauge group, the gauge-fixed functions form a
concrete finite-dimensional Hilbert subspace of all functions on `G^E`.
This file constructs its orthonormal basis, proves invariance and completeness,
and records the unitary coefficient transform.  It also expands every basis
vector uniquely in the complete edgewise Peter--Weyl basis; these expansion
coefficients are the finite contraction tensor.  Vertex-local factorization of
that tensor is developed separately.
-/

open scoped ComplexConjugate PiTensorProduct

namespace NCG.FiniteSpinNetwork

variable {G V E : Type*} [Group G] [Fintype G] [Fintype V]
  [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The linear subspace of functions fixed by every vertex gauge
transformation. -/
def GaugeInvariantSubspace (t s : E → V) :
    Submodule ℂ (EuclideanSpace ℂ (E → G)) where
  carrier := {f | ∀ (h : V → G) (g : E → G),
    f.ofLp (NCG.gaugeAct t s h g) = f.ofLp g}
  zero_mem' := by simp
  add_mem' := by
    intro f f' hf hf' h g
    change f.ofLp (NCG.gaugeAct t s h g) +
      f'.ofLp (NCG.gaugeAct t s h g) = f.ofLp g + f'.ofLp g
    rw [hf h g, hf' h g]
  smul_mem' := by
    intro c f hf h g
    change c * f.ofLp (NCG.gaugeAct t s h g) = c * f.ofLp g
    rw [hf h g]

/-- The canonical finite index set for an orthonormal basis of the invariant
subspace. -/
abbrev SpinIndex (t s : E → V) :=
  Fin (Module.finrank ℂ (GaugeInvariantSubspace (G := G) t s))

/-- A choice-independent-in-dimension orthonormal basis of all gauge-invariant
holonomy functions. -/
noncomputable def invariantOrthonormalBasis (t s : E → V) :
    OrthonormalBasis (SpinIndex (G := G) t s) ℂ
      (GaugeInvariantSubspace (G := G) t s) :=
  stdOrthonormalBasis ℂ (GaugeInvariantSubspace (G := G) t s)

/-- The basis vector rendered as a scalar function on the full configuration
space. -/
noncomputable def spinFunction (t s : E → V)
    (a : SpinIndex (G := G) t s) : (E → G) → ℂ :=
  (invariantOrthonormalBasis (G := G) t s a).1.ofLp

theorem spinFunction_gaugeInvariant (t s : E → V)
    (a : SpinIndex (G := G) t s) (h : V → G) (g : E → G) :
    spinFunction (G := G) t s a (NCG.gaugeAct t s h g) =
      spinFunction (G := G) t s a g :=
  (invariantOrthonormalBasis (G := G) t s a).property h g

/-- The spin functions are orthonormal in the inherited finite `L²` inner
product. -/
theorem spinFunction_orthonormal (t s : E → V) :
    Orthonormal ℂ
      (fun a : SpinIndex (G := G) t s =>
        invariantOrthonormalBasis (G := G) t s a) :=
  (invariantOrthonormalBasis (G := G) t s).orthonormal

/-- Every gauge-invariant function has the exact finite spin expansion. -/
theorem spinFunction_expansion (t s : E → V)
    (f : GaugeInvariantSubspace (G := G) t s) :
    f = ∑ a : SpinIndex (G := G) t s,
      (((invariantOrthonormalBasis (G := G) t s).repr f).ofLp a) •
        invariantOrthonormalBasis (G := G) t s a := by
  exact ((invariantOrthonormalBasis (G := G) t s).sum_repr f).symm

/-- Holonomy histories and invariant spin coefficients are related by a
unitary (linear-isometric) transform. -/
noncomputable def spinCoefficientTransform (t s : E → V) :
    GaugeInvariantSubspace (G := G) t s ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (SpinIndex (G := G) t s) :=
  (invariantOrthonormalBasis (G := G) t s).repr

theorem spinCoefficientTransform_inner (t s : E → V)
    (f f' : GaugeInvariantSubspace (G := G) t s) :
    inner ℂ (spinCoefficientTransform (G := G) t s f)
        (spinCoefficientTransform (G := G) t s f') = inner ℂ f f' :=
  (spinCoefficientTransform (G := G) t s).inner_map_map f f'

/-- Coefficient of an invariant spin vector in the complete edgewise
Peter--Weyl basis.  This is the finite contraction tensor before its
vertex-local factorization. -/
noncomputable def contractionCoefficient
    (D : NCG.FinitePeterWeyl.MatrixBlockDecomposition G)
    (t s : E → V) (a : SpinIndex (G := G) t s)
    (label : E → NCG.FinitePeterWeyl.CoefficientIndex D) : ℂ :=
  (NCG.FinitePeterWeyl.edgePeterWeylBasis D E).repr
    (spinFunction (G := G) t s a) label

/-- Every invariant spin basis vector is exactly the contraction of the full
edge matrix-coefficient basis against its contraction tensor. -/
theorem spinFunction_edge_contraction
    (D : NCG.FinitePeterWeyl.MatrixBlockDecomposition G)
    (t s : E → V) (a : SpinIndex (G := G) t s) :
    spinFunction (G := G) t s a =
      ∑ label : E → NCG.FinitePeterWeyl.CoefficientIndex D,
        contractionCoefficient D t s a label •
          NCG.FinitePeterWeyl.edgePeterWeylBasis D E label := by
  simpa [contractionCoefficient] using
    (NCG.FinitePeterWeyl.edgePeterWeylBasis D E).sum_repr
      (spinFunction (G := G) t s a) |>.symm

end NCG.FiniteSpinNetwork
