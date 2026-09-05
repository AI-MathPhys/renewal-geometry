import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Stacking finitely many bounded operators

A finite family `D j : E → F` defines one bounded operator from `E` into the
Hilbert direct sum of the `F`-fibres.  Its squared norm is the sum of the
directional squared norms, and its normal operator is exactly
`Σ j, (D j)† D j`.
-/

noncomputable section

namespace NCG

variable {d E F : Type*} [Fintype d]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Stack a finite family of bounded operators into the Hilbert `L²` direct
sum of their codomains. -/
def finiteDirectionalOperatorStack (D : d → E →L[ℂ] F) :
    E →L[ℂ] PiLp 2 (fun _ : d ↦ F) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : d ↦ F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi D)

@[simp]
theorem finiteDirectionalOperatorStack_apply
    (D : d → E →L[ℂ] F) (x : E) (j : d) :
    finiteDirectionalOperatorStack D x j = D j x := rfl

/-- Exact energy identity for the stacked operator. -/
theorem finiteDirectionalOperatorStack_norm_sq
    (D : d → E →L[ℂ] F) (x : E) :
    ‖finiteDirectionalOperatorStack D x‖ ^ 2 =
      ∑ j, ‖D j x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

/-- The normal operator of the stack is the sum of the directional normal
operators. -/
theorem finiteDirectionalOperatorStack_adjoint_comp
    (D : d → E →L[ℂ] F) :
    (finiteDirectionalOperatorStack D).adjoint ∘L
        finiteDirectionalOperatorStack D =
      ∑ j, (D j).adjoint ∘L D j := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply]
  simp only [sum_apply, sum_inner,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    finiteDirectionalOperatorStack_apply]

end NCG
