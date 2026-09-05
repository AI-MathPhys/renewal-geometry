/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FinitePressureFlowMaxCut
import NCG.Grand.HierarchyElectricalRouter
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Linear versus pointwise hierarchy routers

Finite-dimensional compiler for `thm:hierarchy-linear-router-distinction`.
The first section constructs one linear right inverse from routes of an
Auerbach basis and proves the dimension-factor congestion bound.  The second
section records the complete-collar optima and proves their even/odd parity
distinction and the exact tetrahedral value.
-/

open scoped BigOperators
open Module

noncomputable section

namespace NCG
namespace HierarchyLinearRouterDistinction

/-- A pointwise router bound: the realizing current may depend nonlinearly on
the demand. -/
def HasPointwiseRouterBound {D J : Type*} [AddCommGroup D] [Module ℝ D]
    [AddCommGroup J] [Module ℝ J]
    (boundary : J →ₗ[ℝ] D) (demandNorm : D → ℝ)
    (currentNorm : J → ℝ) (C : ℝ) : Prop :=
  ∀ g, ∃ j, boundary j = g ∧ currentNorm j ≤ C * demandNorm g

/-- One linear router realizes all demands with a common congestion bound. -/
def HasLinearRouterBound {D J : Type*} [AddCommGroup D] [Module ℝ D]
    [AddCommGroup J] [Module ℝ J]
    (boundary : J →ₗ[ℝ] D) (demandNorm : D → ℝ)
    (currentNorm : J → ℝ) (C : ℝ) : Prop :=
  ∃ router : D →ₗ[ℝ] J,
    boundary.comp router = LinearMap.id ∧
      ∀ g, currentNorm (router g) ≤ C * demandNorm g

/-- Every linear router is, pointwise, an admissible nonlinear router with
the same constant.  This is `C_Q^nl ≤ C_Q^lin` at the feasible-bound level. -/
theorem linear_bound_implies_pointwise_bound
    {D J : Type*} [AddCommGroup D] [Module ℝ D]
    [AddCommGroup J] [Module ℝ J]
    (boundary : J →ₗ[ℝ] D) (demandNorm : D → ℝ)
    (currentNorm : J → ℝ) (C : ℝ)
    (h : HasLinearRouterBound boundary demandNorm currentNorm C) :
    HasPointwiseRouterBound boundary demandNorm currentNorm C := by
  obtain ⟨router, hright, hbound⟩ := h
  intro g
  refine ⟨router g, ?_, hbound g⟩
  have := LinearMap.congr_fun hright g
  simpa using this

/-- Auerbach assembly.  `basisCurrent i` is a pointwise-optimal current for
the `i`th normalized basis demand.  The two displayed norm hypotheses are
exactly the Auerbach coefficient estimate and the current-norm triangle
estimate.  The constructed map is one linear right inverse and costs at most
the dimension times the pointwise constant. -/
theorem auerbach_linear_router
    {d : ℕ} {D J : Type*} [AddCommGroup D] [Module ℝ D]
    [AddCommGroup J] [Module ℝ J]
    (boundary : J →ₗ[ℝ] D) (basis : Basis (Fin d) ℝ D)
    (basisCurrent : Fin d → J)
    (demandNorm : D → ℝ) (currentNorm : J → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hboundary : ∀ i, boundary (basisCurrent i) = basis i)
    (hbasisCurrent : ∀ i, currentNorm (basisCurrent i) ≤ C)
    (hcurrentTriangle : ∀ a : Fin d → ℝ,
      currentNorm (∑ i, a i • basisCurrent i) ≤
        ∑ i, |a i| * currentNorm (basisCurrent i))
    (hAuerbach : ∀ g,
      ∑ i, |basis.repr g i| ≤ d * demandNorm g) :
    HasLinearRouterBound boundary demandNorm currentNorm (d * C) := by
  let router : D →ₗ[ℝ] J := basis.constr ℝ basisCurrent
  refine ⟨router, ?_, ?_⟩
  · apply basis.ext
    intro i
    simp [router, hboundary]
  · intro g
    rw [show router g = ∑ i, basis.repr g i • basisCurrent i by
      simpa [router] using basis.constr_apply_fintype ℝ basisCurrent g]
    calc
      currentNorm (∑ i, basis.repr g i • basisCurrent i)
          ≤ ∑ i, |basis.repr g i| * currentNorm (basisCurrent i) :=
        hcurrentTriangle _
      _ ≤ ∑ i, |basis.repr g i| * C := by
        gcongr with i
        exact hbasisCurrent i
      _ = C * ∑ i, |basis.repr g i| := by
        rw [Finset.mul_sum]
        congr 1
        funext i
        ring
      _ ≤ C * (d * demandNorm g) :=
        mul_le_mul_of_nonneg_left (hAuerbach g) hC
      _ = (d * C) * demandNorm g := by
        push_cast
        ring

/-! ## Equal-mass complete collars -/

/-- The smaller-side cardinality of an extremal complete-graph cut. -/
def halfCeil (k : ℕ) : ℕ := (k + 1) / 2

/-- Pointwise max-flow/min-cut constant of the equal-mass complete collar. -/
noncomputable def completeCollarPointwiseConstant
    (k : ℕ) (m u : ℝ) : ℝ :=
  m ^ (2 / 3 : ℝ) / (u * halfCeil k)

/-- Symmetric optimal linear-router constant of the equal-mass complete
collar, witnessed by `k⁻¹ B*`. -/
noncomputable def completeCollarLinearConstant
    (k : ℕ) (m u : ℝ) : ℝ :=
  2 * m ^ (2 / 3 : ℝ) / (k * u)

/-- A cut with `r` vertices on one side has `r(k-r)` crossing edges. -/
def completeCollarCutCapacity (k r : ℕ) (u : ℝ) : ℝ :=
  r * (k - r) * u

theorem completeCollar_cut_capacity (k r : ℕ) (u : ℝ) :
    completeCollarCutCapacity k r u = r * (k - r) * u := rfl

/-- For even complete collars the pointwise and best-linear constants agree. -/
theorem completeCollar_even_constants_agree
    (n : ℕ) (m u : ℝ) (hn : 0 < n) (hu : u ≠ 0) :
    completeCollarPointwiseConstant (2 * n) m u =
      completeCollarLinearConstant (2 * n) m u := by
  have hhalf : halfCeil (2 * n) = n := by
    simp only [halfCeil]
    omega
  rw [completeCollarPointwiseConstant, completeCollarLinearConstant, hhalf]
  norm_num
  field_simp [hu, Nat.ne_of_gt hn]

/-- For odd complete collars with at least three vertices, the best one
linear router is strictly more expensive than pointwise max-flow/min-cut. -/
theorem completeCollar_odd_constants_strict
    (n : ℕ) (m u : ℝ) (hn : 0 < n) (hm : 0 < m) (hu : 0 < u) :
    completeCollarPointwiseConstant (2 * n + 1) m u <
      completeCollarLinearConstant (2 * n + 1) m u := by
  have hhalf : halfCeil (2 * n + 1) = n + 1 := by
    simp only [halfCeil]
    omega
  rw [completeCollarPointwiseConstant, completeCollarLinearConstant, hhalf]
  have hs : 0 < m ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hm _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd1 : 0 < u * (n + 1 : ℕ) := by positivity
  have hd2 : 0 < ((2 * n + 1 : ℕ) : ℝ) * u := by positivity
  rw [div_lt_div_iff₀ hd1 hd2]
  push_cast
  nlinarith

/-- The selected tetrahedral branch retains the exact manuscript value. -/
theorem completeCollar_K4_linear_value (m u : ℝ) :
    completeCollarLinearConstant 4 m u = m ^ (2 / 3 : ℝ) / (2 * u) := by
  rw [completeCollarLinearConstant]
  norm_num
  ring

/-- At `K4`, the pointwise and linear values coincide at
`m^(2/3)/(2u)`. -/
theorem completeCollar_K4_exact (m u : ℝ) :
    completeCollarPointwiseConstant 4 m u =
      completeCollarLinearConstant 4 m u ∧
    completeCollarLinearConstant 4 m u = m ^ (2 / 3 : ℝ) / (2 * u) := by
  constructor
  · simp [completeCollarPointwiseConstant, completeCollarLinearConstant,
      halfCeil]
    ring
  · exact completeCollar_K4_linear_value m u

end HierarchyLinearRouterDistinction
end NCG
