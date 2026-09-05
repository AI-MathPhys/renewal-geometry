/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Graph-core approximation of soft modes

Graph-norm approximation transfers a normalized transient soft-mode sequence to vectors in an
operator core.  The approximants remain asymptotically normalized, their protected components
vanish, and their operator residuals vanish.  When the core is the span of primitive source
words, this is the analytic step that turns abstract soft modes into finite operational panels.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace K F]

/-- Normalize a nonzero core vector using the ambient real norm, viewed in the scalar field. -/
def graphNormalize (K : Type u) [RCLike K]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H] (x : H) : H :=
  ((‖x‖⁻¹ : ℝ) : K) • x

@[simp] theorem norm_graphNormalize_of_norm_ne_zero
    (x : H) (hx : ‖x‖ ≠ 0) :
    ‖graphNormalize K x‖ = 1 := by
  simp [graphNormalize, norm_smul, inv_mul_cancel₀ hx]
/-- Graph-norm approximants of normalized transient soft modes retain all three asymptotic
properties needed by the primitive-word witness: unit norm, zero protected component, and zero
operator residual. -/
theorem graphCoreApproximation_preserves_softMode
    (A : ℕ → H →ₗ[K] F) (E : ℕ → H →L[K] H) (v core : ℕ → H)
    (hEnorm : ∀ n, ‖E n‖ ≤ 1)
    (hvnorm : ∀ n, ‖v n‖ = 1)
    (hvprotected : ∀ n, E n (v n) = 0)
    (hvresidual : Tendsto (fun n ↦ ‖A n (v n)‖) atTop (nhds 0))
    (hcarrier : Tendsto (fun n ↦ ‖core n - v n‖) atTop (nhds 0))
    (hgraph : Tendsto (fun n ↦ ‖A n (core n - v n)‖) atTop (nhds 0)) :
    Tendsto (fun n ↦ ‖core n‖) atTop (nhds 1) ∧
      Tendsto (fun n ↦ ‖E n (core n)‖) atTop (nhds 0) ∧
      Tendsto (fun n ↦ ‖A n (core n)‖) atTop (nhds 0) := by
  have hnorm : Tendsto (fun n ↦ ‖core n‖) atTop (nhds 1) := by
    have hdiff : Tendsto (fun n ↦ ‖core n‖ - 1) atTop (nhds 0) :=
      squeeze_zero_norm (fun n ↦ by
        rw [Real.norm_eq_abs, ← hvnorm n]
        exact abs_norm_sub_norm_le (core n) (v n)) hcarrier
    have := hdiff.add (tendsto_const_nhds (x := (1 : ℝ)))
    simpa using this
  have hprotected : Tendsto (fun n ↦ ‖E n (core n)‖) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n ↦ norm_nonneg _
    · exact Filter.Eventually.of_forall fun n ↦ by
        calc
          ‖E n (core n)‖ = ‖E n (core n - v n)‖ := by
            rw [map_sub, hvprotected n, sub_zero]
          _ ≤ ‖E n‖ * ‖core n - v n‖ := (E n).le_opNorm _
          _ ≤ ‖core n - v n‖ := by
            simpa using mul_le_mul_of_nonneg_right (hEnorm n) (norm_nonneg (core n - v n))
    · exact hcarrier
  have hresidual : Tendsto (fun n ↦ ‖A n (core n)‖) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n ↦ norm_nonneg _
    · exact Filter.Eventually.of_forall fun n ↦ by
        calc
          ‖A n (core n)‖ = ‖A n (core n - v n) + A n (v n)‖ := by
            congr 1
            rw [← map_add]
            congr 1
            abel
          _ ≤ ‖A n (core n - v n)‖ + ‖A n (v n)‖ := norm_add_le _ _
    · simpa using hgraph.add hvresidual
  exact ⟨hnorm, hprotected, hresidual⟩

/-- Normalizing the core approximants makes the unit-norm clause exact eventually while
preserving vanishing protected components and operator residuals. -/
theorem graphCoreNormalization_preserves_softMode
    (A : ℕ → H →ₗ[K] F) (E : ℕ → H →L[K] H) (v core : ℕ → H)
    (hEnorm : ∀ n, ‖E n‖ ≤ 1)
    (hvnorm : ∀ n, ‖v n‖ = 1)
    (hvprotected : ∀ n, E n (v n) = 0)
    (hvresidual : Tendsto (fun n ↦ ‖A n (v n)‖) atTop (nhds 0))
    (hcarrier : Tendsto (fun n ↦ ‖core n - v n‖) atTop (nhds 0))
    (hgraph : Tendsto (fun n ↦ ‖A n (core n - v n)‖) atTop (nhds 0)) :
    (∀ᶠ n in atTop, ‖graphNormalize K (core n)‖ = 1) ∧
      Tendsto (fun n ↦ ‖E n (graphNormalize K (core n))‖) atTop (nhds 0) ∧
      Tendsto (fun n ↦ ‖A n (graphNormalize K (core n))‖) atTop (nhds 0) := by
  obtain ⟨hnorm, hprotected, hresidual⟩ :=
    graphCoreApproximation_preserves_softMode
      A E v core hEnorm hvnorm hvprotected hvresidual hcarrier hgraph
  have hpos : ∀ᶠ n in atTop, 0 < ‖core n‖ :=
    hnorm.eventually (Ioi_mem_nhds zero_lt_one)
  have hexact : ∀ᶠ n in atTop, ‖graphNormalize K (core n)‖ = 1 :=
    hpos.mono fun n hn ↦ norm_graphNormalize_of_norm_ne_zero (core n) (ne_of_gt hn)
  have hinv : Tendsto (fun n ↦ ‖core n‖⁻¹) atTop (nhds 1) := by
    simpa using hnorm.inv₀ one_ne_zero
  have hcoefficient :
      Tendsto (fun n ↦ ‖((‖core n‖⁻¹ : ℝ) : K)‖) atTop (nhds 1) := by
    simpa [RCLike.norm_ofReal, abs_of_nonneg] using hinv
  have hprotectedNormalized :
      Tendsto (fun n ↦ ‖E n (graphNormalize K (core n))‖) atTop (nhds 0) := by
    convert hcoefficient.mul hprotected using 1 <;>
      simp [graphNormalize, norm_smul]
  have hresidualNormalized :
      Tendsto (fun n ↦ ‖A n (graphNormalize K (core n))‖) atTop (nhds 0) := by
    convert hcoefficient.mul hresidual using 1 <;>
      simp [graphNormalize, norm_smul]
  exact ⟨hexact, hprotectedNormalized, hresidualNormalized⟩
/-- The squared residual panels of graph-core soft-mode approximants also vanish. -/
theorem graphCoreApproximation_residualSq_tendsto_zero
    (A : ℕ → H →ₗ[K] F) (core : ℕ → H)
    (hresidual : Tendsto (fun n ↦ ‖A n (core n)‖) atTop (nhds 0)) :
    Tendsto (fun n ↦ ‖A n (core n)‖ ^ 2) atTop (nhds 0) := by
  simpa using hresidual.pow 2

end NCG
