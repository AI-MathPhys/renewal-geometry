/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteWeightedGraphHodgeDiracExact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Attainment of the finite weighted graph Connes distance

Connectedness removes the kernel after fixing one vertex value. The resulting
finite-dimensional unit ball is compact. Consequently the actual commutator
distance has an optimizer; no variational attainment premise is required.
-/

open Matrix Set
open scoped Matrix.Norms.L2Operator

namespace NCG.FiniteConnesDistanceAttainment

open FiniteWeightedGraphHodgeDirac

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph gradient, as a linear map into the actual lower commutator block. -/
def gradientLinear (mass : V → ℝ) (conductance : V → V → ℝ) :
    (V → ℝ) →ₗ[ℝ] Matrix (V × V) V ℝ where
  toFun := lipschitzBlock mass conductance
  map_add' f g := by
    ext xy z
    by_cases hz : z = xy.1 <;> simp [lipschitzBlock, hz] <;> ring
  map_smul' a f := by
    ext xy z
    by_cases hz : z = xy.1 <;> simp [lipschitzBlock, hz] <;> ring

theorem graphLipschitz_eq_norm_gradient
    (mass : V → ℝ) (conductance : V → V → ℝ) (f : V → ℝ) :
    graphLipschitz mass conductance f = ‖gradientLinear mass conductance f‖ := by
  have h₁ := norm_sq_dirac_commutator mass conductance f
  have h₂ := norm_sq_lipschitzBlock mass conductance f
  have h₃ : 0 ≤ graphLipschitz mass conductance f := norm_nonneg _
  have h₄ : 0 ≤ ‖gradientLinear mass conductance f‖ := norm_nonneg _
  change graphLipschitz mass conductance f ^ 2 = _ at h₁
  change ‖gradientLinear mass conductance f‖ ^ 2 = _ at h₂
  nlinarith

theorem continuous_graphLipschitz
    (mass : V → ℝ) (conductance : V → V → ℝ) :
    Continuous (graphLipschitz mass conductance) := by
  have h := (gradientLinear mass conductance).continuous_of_finiteDimensional.norm
  simpa only [← graphLipschitz_eq_norm_gradient] using h

/-- Fix the constant mode by recording one vertex value alongside the gradient. -/
def anchoredGradient (mass : V → ℝ) (conductance : V → V → ℝ) (x₀ : V) :
    (V → ℝ) →ₗ[ℝ] ℝ × Matrix (V × V) V ℝ :=
  (LinearMap.proj x₀).prod (gradientLinear mass conductance)

theorem anchoredGradient_injective
    (mass : V → ℝ) (conductance : V → V → ℝ) (x₀ : V)
    (hmass : ∀ x, 0 < mass x) (hconnected : ConductanceConnected conductance) :
    Function.Injective (anchoredGradient mass conductance x₀) := by
  letI : Nonempty V := ⟨x₀⟩
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  have hzero : f x₀ = 0 := congrArg Prod.fst hf
  have hgrad : lipschitzBlock mass conductance f = 0 := congrArg Prod.snd hf
  obtain ⟨a, ha⟩ := (lipschitzBlock_eq_zero_iff_constant mass conductance f
    hmass hconnected).mp hgrad
  ext x
  simpa [ha x₀] using (ha x).trans (by simpa [ha x₀] using hzero)

/-- Normalized feasible functions for the Connes variational problem. -/
def anchoredUnitBall (mass : V → ℝ) (conductance : V → V → ℝ) (x₀ : V) :
    Set (V → ℝ) := {f | f x₀ = 0 ∧ graphLipschitz mass conductance f ≤ 1}

theorem isCompact_anchoredUnitBall
    (mass : V → ℝ) (conductance : V → V → ℝ) (x₀ : V)
    (hmass : ∀ x, 0 < mass x) (hconnected : ConductanceConnected conductance) :
    IsCompact (anchoredUnitBall mass conductance x₀) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_eq (continuous_apply x₀) continuous_const).inter
      (isClosed_le (continuous_graphLipschitz mass conductance) continuous_const)
  · obtain ⟨K, hKpos, hK⟩ :=
      (anchoredGradient mass conductance x₀).injective_iff_antilipschitz.mp
        (anchoredGradient_injective mass conductance x₀ hmass hconnected)
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨K, ?_⟩
    intro f hf
    have hbound := ZeroHomClass.bound_of_antilipschitz
      (anchoredGradient mass conductance x₀) hK f
    have hnorm : ‖anchoredGradient mass conductance x₀ f‖ ≤ 1 := by
      change max ‖f x₀‖ ‖gradientLinear mass conductance f‖ ≤ 1
      rw [hf.1, norm_zero, ← graphLipschitz_eq_norm_gradient]
      exact max_le zero_le_one hf.2
    exact hbound.trans ((mul_le_mul_of_nonneg_left hnorm K.coe_nonneg).trans_eq (mul_one _))

theorem graphLipschitz_sub_constant
    (mass : V → ℝ) (conductance : V → V → ℝ) (f : V → ℝ) (a : ℝ) :
    graphLipschitz mass conductance (fun x => f x - a) =
      graphLipschitz mass conductance f := by
  simp only [graphLipschitz_eq_norm_gradient]
  congr 1
  ext xy z
  by_cases hz : z = xy.1 <;> simp [gradientLinear, lipschitzBlock, hz] <;> ring

theorem distanceValues_eq_anchored_image
    (mass : V → ℝ) (conductance : V → V → ℝ) (x₀ x y : V) :
    distanceValues mass conductance x y =
      (fun f : V → ℝ => |f x - f y|) '' anchoredUnitBall mass conductance x₀ := by
  ext r
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun z => f z - f x₀, ⟨sub_self _, ?_⟩, ?_⟩
    · simpa only [graphLipschitz_sub_constant] using hf
    · change |(f x - f x₀) - (f y - f x₀)| = |f x - f y|
      congr 1
      ring
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf.2, rfl⟩

theorem isCompact_distanceValues
    (mass : V → ℝ) (conductance : V → V → ℝ) (x y : V)
    (hmass : ∀ x, 0 < mass x) (hconnected : ConductanceConnected conductance) :
    IsCompact (distanceValues mass conductance x y) := by
  rw [distanceValues_eq_anchored_image mass conductance x x y]
  exact (isCompact_anchoredUnitBall mass conductance x hmass hconnected).image
    (((continuous_apply x).sub (continuous_apply y)).abs)

theorem zero_mem_distanceValues
    (mass : V → ℝ) (conductance : V → V → ℝ) (x y : V) :
    0 ∈ distanceValues mass conductance x y := by
  refine ⟨0, ?_, by simp⟩
  simp [graphLipschitz_eq_norm_gradient]

/-- The actual finite Connes distance, as the supremum of commutator-feasible differences. -/
def connesDistance (mass : V → ℝ) (conductance : V → V → ℝ) (x y : V) : ℝ :=
  sSup (distanceValues mass conductance x y)

theorem connesDistance_isGreatest
    (mass : V → ℝ) (conductance : V → V → ℝ) (x y : V)
    (hmass : ∀ x, 0 < mass x) (hconnected : ConductanceConnected conductance) :
    IsGreatest (distanceValues mass conductance x y) (connesDistance mass conductance x y) :=
  (isCompact_distanceValues mass conductance x y hmass hconnected).isGreatest_sSup
    ⟨0, zero_mem_distanceValues mass conductance x y⟩

theorem exists_connesDistance_optimizer
    (mass : V → ℝ) (conductance : V → V → ℝ) (x y : V)
    (hmass : ∀ x, 0 < mass x) (hconnected : ConductanceConnected conductance) :
    ∃ f : V → ℝ, graphLipschitz mass conductance f ≤ 1 ∧
      connesDistance mass conductance x y = |f x - f y| :=
  (connesDistance_isGreatest mass conductance x y hmass hconnected).1

end

end NCG.FiniteConnesDistanceAttainment
