/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MoorePenroseSchurExact
import NCG.Grand.PositiveSqrtExact

/-!
# Hilbert–Schmidt norms on finite-dimensional spaces

`hsSq A = Tr(A† A)` is the squared Hilbert–Schmidt norm of `A : V →L[ℝ] H`.  It equals
`∑ᵢ ‖A bᵢ‖²` for any orthonormal basis (`hsSq_eq_sum`), is additive on operators with
orthogonal ranges (`hsSq_add_of_adjoint_comp_eq_zero`), splits along a family of mutually
orthogonal projections, and satisfies the Hilbert–Schmidt Thomson principle
(`hsSq_minNorm`): the minimum of `‖H‖²_HS` over `L H = Q` is `Tr(Q† C† Q)` with `C = L L†`.
-/

open ContinuousLinearMap Submodule NCG.MoorePenrose
open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace HilbertSchmidt

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The squared Hilbert–Schmidt norm `Tr(A† A)`. -/
noncomputable def hsSq (A : V →L[ℝ] H) : ℝ :=
  LinearMap.trace ℝ V ((A† ∘L A : V →L[ℝ] V) : V →ₗ[ℝ] V)

omit [FiniteDimensional ℝ V] in
theorem hsSq_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (A : V →L[ℝ] H) :
    hsSq A = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [hsSq, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ⟪b i, (A†) (A (b i))⟫ = _
  rw [adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem hsSq_nonneg (A : V →L[ℝ] H) : 0 ≤ hsSq A := by
  rw [hsSq_eq_sum (stdOrthonormalBasis ℝ V)]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem hsSq_eq_zero_of_eq_zero : hsSq (0 : V →L[ℝ] H) = 0 := by
  rw [hsSq_eq_sum (stdOrthonormalBasis ℝ V)]
  simp

/-- Additivity on operators with orthogonal ranges. -/
theorem hsSq_add_of_adjoint_comp_eq_zero {A B : V →L[ℝ] H} (h : A† ∘L B = 0) :
    hsSq (A + B) = hsSq A + hsSq B := by
  rw [hsSq_eq_sum (stdOrthonormalBasis ℝ V), hsSq_eq_sum (stdOrthonormalBasis ℝ V),
    hsSq_eq_sum (stdOrthonormalBasis ℝ V), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_apply, pow_two, pow_two, pow_two]
  refine norm_add_sq_eq_norm_sq_add_norm_sq_real ?_
  have h' : (A†) (B (stdOrthonormalBasis ℝ V i)) = 0 :=
    congrArg (fun T : V →L[ℝ] V => T (stdOrthonormalBasis ℝ V i)) h
  rw [← adjoint_inner_right, h', inner_zero_right]

omit [FiniteDimensional ℝ V] in
/-- The Hilbert–Schmidt norm of a composite as a trace. -/
theorem hsSq_comp_eq_trace {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [CompleteSpace W] (R : H →L[ℝ] W) (A : V →L[ℝ] H) :
    hsSq (R ∘L A) = LinearMap.trace ℝ V ((A† ∘L (R† ∘L R) ∘L A : V →L[ℝ] V) : V →ₗ[ℝ] V) := by
  rw [hsSq, adjoint_comp]
  rfl

/-- Splitting the Hilbert–Schmidt norm along a positive square root:
`hsSq A = hsSq (Q A) + hsSq (sqrt (I - Q† Q) A)` when `Q` is contractive. -/
theorem hsSq_eq_hsSq_comp_add_sqrt {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [CompleteSpace W] [FiniteDimensional ℝ H]
    (Q : H →L[ℝ] W) (hQ : (1 - Q† ∘L Q).IsPositive) (A : V →L[ℝ] H) :
    hsSq A = hsSq (Q ∘L A) + hsSq (PositiveSqrt.sqrt (1 - Q† ∘L Q) hQ ∘L A) := by
  rw [hsSq_eq_sum (stdOrthonormalBasis ℝ V), hsSq_eq_sum (stdOrthonormalBasis ℝ V),
    hsSq_eq_sum (stdOrthonormalBasis ℝ V), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [comp_apply, comp_apply, PositiveSqrt.norm_sqrt_apply_sq, sub_apply, one_apply_eq_self,
    inner_sub_left, comp_apply, adjoint_inner_left, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  ring

/-! ### The Hilbert–Schmidt Thomson principle -/

section Thomson

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [CompleteSpace W] [FiniteDimensional ℝ H] (L : H →L[ℝ] W) (Q : V →L[ℝ] W)

/-- The minimum-norm lift `H₀ = L† C† Q` of `Q` through `L`, where `C = L L†`. -/
noncomputable def minNormLift : V →L[ℝ] H := L† ∘L gramPinv (L†) ∘L Q

omit [FiniteDimensional ℝ V] [CompleteSpace V] [FiniteDimensional ℝ H] in
theorem minNormLift_apply (x : V) : minNormLift L Q x = minNormSolution L (Q x) := rfl

omit [FiniteDimensional ℝ V] [CompleteSpace V] in
theorem comp_minNormLift (hQ : ∀ x, Q x ∈ LinearMap.range L.toLinearMap) :
    L ∘L minNormLift L Q = Q :=
  ContinuousLinearMap.ext fun x => minNormSolution_apply L (hQ x)

/-- `‖H₀‖²_HS = Tr[Q† C† Q]`. -/
theorem hsSq_minNormLift (hQ : ∀ x, Q x ∈ LinearMap.range L.toLinearMap) :
    hsSq (minNormLift L Q)
      = LinearMap.trace ℝ V ((Q† ∘L gramPinv (L†) ∘L Q : V →L[ℝ] V) : V →ₗ[ℝ] V) := by
  rw [hsSq_eq_sum (stdOrthonormalBasis ℝ V),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ V)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [minNormLift_apply, norm_sq_minNormSolution L (hQ _)]
  change _ = ⟪stdOrthonormalBasis ℝ V i, (Q†) (gramPinv (L†) (Q (stdOrthonormalBasis ℝ V i)))⟫
  rw [adjoint_inner_right]

/-- **The Hilbert–Schmidt Thomson principle**: `H₀` has minimal Hilbert–Schmidt norm among all
lifts `K` with `L K = Q`. -/
theorem hsSq_minNormLift_le {K : V →L[ℝ] H} (hK : L ∘L K = Q) :
    hsSq (minNormLift L Q) ≤ hsSq K := by
  rw [hsSq_eq_sum (stdOrthonormalBasis ℝ V), hsSq_eq_sum (stdOrthonormalBasis ℝ V)]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : L (K (stdOrthonormalBasis ℝ V i)) = Q (stdOrthonormalBasis ℝ V i) :=
    congrArg (fun T : V →L[ℝ] W => T (stdOrthonormalBasis ℝ V i)) hK
  rw [minNormLift_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_minNormSolution_le L h) 2

end Thomson

end HilbertSchmidt
end NCG
