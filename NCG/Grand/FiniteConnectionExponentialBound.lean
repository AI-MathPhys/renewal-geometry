/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTorusCovariantSymbolCutoffLimit
import Mathlib.Order.Filter.Finite

/-!
# Eventual exponential bounds for finite connection families

For a fixed finite family of bounded connection operators, the factors
`‖B_j‖ exp(h_N ‖B_j‖)` admit one eventual uniform bound because the cutoff
mesh tends to zero.  This discharges the only quantitative bookkeeping
hypothesis in the Fourier phase-chord tail estimate.
-/

open Filter Topology

noncomputable section

namespace NCG

variable {d E : Type*} [Fintype d]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A simple strictly positive envelope for a finite family of operator
norms. -/
def finiteConnectionNormEnvelope (B : d → E →L[ℂ] E) : ℝ :=
  (∑ j, ‖B j‖) + 1

theorem norm_le_finiteConnectionNormEnvelope
    (B : d → E →L[ℂ] E) (j : d) :
    ‖B j‖ ≤ finiteConnectionNormEnvelope B := by
  have hj : ‖B j‖ ≤ ∑ i, ‖B i‖ :=
    Finset.single_le_sum (fun i _ ↦ norm_nonneg (B i)) (Finset.mem_univ j)
  unfold finiteConnectionNormEnvelope
  linarith

/-- The finite-mesh exponential connection factors are eventually bounded
by one common envelope, simultaneously in every direction. -/
theorem eventually_connectionExp_le_finiteConnectionNormEnvelope
    (B : d → E →L[ℂ] E) :
    ∀ᶠ N : ℕ in atTop, ∀ j,
      ‖B j‖ * Real.exp (finiteTorusCutoffMesh N * ‖B j‖) ≤
        finiteConnectionNormEnvelope B := by
  have hmesh : Tendsto finiteTorusCutoffMesh atTop (𝓝 0) :=
    finiteTorusCutoffMesh_tendsto_right.mono_right inf_le_left
  have hcoord (j : d) :
      ∀ᶠ N : ℕ in atTop,
        ‖B j‖ * Real.exp (finiteTorusCutoffMesh N * ‖B j‖) ≤
          finiteConnectionNormEnvelope B := by
    have harg : Tendsto
        (fun N : ℕ ↦ finiteTorusCutoffMesh N * ‖B j‖)
        atTop (𝓝 0) := by
      simpa using hmesh.mul_const ‖B j‖
    have hexp : Tendsto
        (fun N : ℕ ↦ Real.exp (finiteTorusCutoffMesh N * ‖B j‖))
        atTop (𝓝 1) := by
      have hcomp := Real.continuous_exp.continuousAt.tendsto.comp harg
      rw [Real.exp_zero] at hcomp
      exact hcomp.congr'
        (Eventually.of_forall fun _ ↦ rfl)
    have hproduct : Tendsto
        (fun N : ℕ ↦ ‖B j‖ *
          Real.exp (finiteTorusCutoffMesh N * ‖B j‖))
        atTop (𝓝 ‖B j‖) := by
      simpa using tendsto_const_nhds.mul hexp
    have hstrict : ‖B j‖ < finiteConnectionNormEnvelope B := by
      have hj : ‖B j‖ ≤ ∑ i, ‖B i‖ :=
        Finset.single_le_sum (fun i _ ↦ norm_nonneg (B i))
          (Finset.mem_univ j)
      unfold finiteConnectionNormEnvelope
      linarith
    exact (hproduct.eventually (Iio_mem_nhds hstrict)).mono
      (fun _ h ↦ h.le)
  exact (eventually_all).2 hcoord

end NCG
