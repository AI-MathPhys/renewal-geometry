/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Projective compactness of finite-stage states
  (`thm:projective-state-compactness`, Gran-Tensor manuscript)

* `finite_stage_state_compactness`: the single-stage
  Bolzano–Weierstrass step — a norm-bounded sequence of
  functionals on a finite-dimensional stage algebra has a
  subsequence converging to a functional in the same ball
  (the dual ball of a finite-dimensional space is compact);
* `limit_state_evaluation`: convergence in the dual passes to
  every evaluation `φ_{σ j}(a) → ψ(a)`;
* `limit_state_normalization`: normalization persists —
  `φ_j(1) = 1` along the subsequence forces `ψ(1) = 1`;
* `limit_state_positive`: positivity persists — real-part
  positivity on a fixed element passes to the limit functional;
* `compatible_limit_constant`: the exactly-compatible branch —
  if the pulled-back values stabilize (`f n = f m` for `n ≥ m`),
  the limit exists along the full sequence with value `f m`, so
  no subsequence is required and the limit state is unique.

Rendering disclosed: the diagonal extraction across all stages
simultaneously (Cantor's scheme through the injective sequence
`𝒜₁ → 𝒜₂ → ⋯`) and the assembly of the compatible family into a
state on the AF inductive limit are the manuscript's
bookkeeping; the per-stage compactness, the persistence of the
state conditions under weak limits, and the exact-compatibility
branch are proved here.
-/

open Filter Topology

namespace NCG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Single-stage Bolzano–Weierstrass: a sequence of functionals
in the unit ball of the dual of a finite-dimensional stage has a
subsequence converging to a functional in the same ball. -/
theorem finite_stage_state_compactness [FiniteDimensional ℂ E]
    (φ : ℕ → (E →L[ℂ] ℂ)) (hbd : ∀ j, ‖φ j‖ ≤ 1) :
    ∃ ψ : E →L[ℂ] ℂ, ‖ψ‖ ≤ 1 ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun j => φ (σ j)) atTop (𝓝 ψ) := by
  have hmem : ∀ j,
      φ j ∈ Metric.closedBall (0 : E →L[ℂ] ℂ) 1 := by
    intro j
    simpa [Metric.mem_closedBall, dist_zero_right] using hbd j
  have hcomp :
      IsCompact (Metric.closedBall (0 : E →L[ℂ] ℂ) 1) :=
    isCompact_closedBall _ _
  obtain ⟨ψ, hψ, σ, hσ, hconv⟩ := hcomp.tendsto_subseq hmem
  refine ⟨ψ, ?_, σ, hσ, hconv⟩
  simpa [Metric.mem_closedBall, dist_zero_right] using hψ

/-- Dual convergence passes to every evaluation:
`φ_{σ j}(a) → ψ(a)` for each fixed stage element `a`. -/
theorem limit_state_evaluation (φ : ℕ → (E →L[ℂ] ℂ))
    (ψ : E →L[ℂ] ℂ) (σ : ℕ → ℕ)
    (hconv : Tendsto (fun j => φ (σ j)) atTop (𝓝 ψ)) (a : E) :
    Tendsto (fun j => φ (σ j) a) atTop (𝓝 (ψ a)) := by
  have hc : Continuous fun T : E →L[ℂ] ℂ => T a :=
    (ContinuousLinearMap.apply ℂ ℂ a).continuous
  exact (hc.tendsto ψ).comp hconv

/-- Normalization persists: unit values along the subsequence
force the limit functional to be unital. -/
theorem limit_state_normalization (φ : ℕ → (E →L[ℂ] ℂ))
    (ψ : E →L[ℂ] ℂ) (σ : ℕ → ℕ)
    (hconv : Tendsto (fun j => φ (σ j)) atTop (𝓝 ψ)) (u : E)
    (hone : ∀ j, φ (σ j) u = 1) : ψ u = 1 := by
  have h := limit_state_evaluation φ ψ σ hconv u
  have h' : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 (ψ u)) := by
    simpa [hone] using h
  exact tendsto_nhds_unique h' tendsto_const_nhds

/-- Positivity persists: real-part positivity on a fixed element
passes to the weak limit. -/
theorem limit_state_positive (φ : ℕ → (E →L[ℂ] ℂ))
    (ψ : E →L[ℂ] ℂ) (σ : ℕ → ℕ)
    (hconv : Tendsto (fun j => φ (σ j)) atTop (𝓝 ψ)) (a : E)
    (hpos : ∀ j, 0 ≤ (φ (σ j) a).re) : 0 ≤ (ψ a).re := by
  have h := limit_state_evaluation φ ψ σ hconv a
  have hre : Tendsto (fun j => (φ (σ j) a).re) atTop
      (𝓝 (ψ a).re) := (Complex.continuous_re.tendsto _).comp h
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hre
    (Eventually.of_forall hpos)

/-- Exactly-compatible branch: if the pulled-back values
stabilize at stage `m`, the full sequence converges to the stage
value — no subsequence is required and the limit is unique. -/
theorem compatible_limit_constant (f : ℕ → ℂ) (m : ℕ)
    (hstab : ∀ n, m ≤ n → f n = f m) :
    Tendsto f atTop (𝓝 (f m)) := by
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  exact hstab n hn

end NCG
