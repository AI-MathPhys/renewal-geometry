/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.SourceCoercivityInfluenceExact

/-!
# The continuum Howe coercivity: the per-cutoff spectral floor

Final machinery layer for `thm:SMST-continuum-Howe`: the compiled
varying-Hilbert library already proves the kernel locking, protected-projection
convergence, first-positive-eigenvalue convergence, eventual uniform
coercivity, and the no-escape clause
(`continuumHowe_kernel_and_coercivity_of_injective_limit_endpoints`,
`jointCommutator_protectedKernelRigidity_of_denseSources_of_graphScreens`,
`jointCommutator_firstPositiveEigenvalue_tendsto_of_denseSources_of_graphScreens`).
Their remaining per-cutoff input — the finite spectral coercivity of each
commutant Laplacian at its own least positive eigenvalue — is proved here by
spectral calculus:

* `psd_sub_gap_supportProj_posSemidef`: a positive-semidefinite matrix
  dominates `μ` times its support projection whenever every eigenvalue is
  zero or at least `μ`;
* `rayleigh_ge_gap_complement` (**the per-cutoff Howe floor**):
  `μ·⟨v, Q v⟩ ≤ ⟨v, M v⟩` with `Q` the support (complement-of-kernel)
  projection — the quadratic form of each cutoff commutant Laplacian
  dominates its least positive eigenvalue on the unprotected complement.
-/

open Matrix Finset
open scoped ComplexOrder

namespace NCG
namespace ContinuumHowe

open NCG.GeometricThresholdBank NCG.SourceCoercivityInfluence

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive-semidefinite matrix dominates `μ` times its support projection
whenever every eigenvalue is zero or at least `μ`. -/
theorem psd_sub_gap_supportProj_posSemidef {M : Matrix n n ℂ}
    (hM : M.PosSemidef) (μ : ℝ)
    (hdich : ∀ i, hM.1.eigenvalues i = 0 ∨ μ ≤ hM.1.eigenvalues i) :
    (M - (μ : ℂ) • supportProj hM.1).PosSemidef := by
  have hform : M - (μ : ℂ) • supportProj hM.1
      = spectralFunction hM.1
          (fun l => l - μ * if 0 < l then 1 else 0) := by
    have hid : spectralFunction hM.1 (fun l => l) = M := spectralFunction_id hM.1
    unfold supportProj
    rw [spectralFunction_sub, spectralFunction_smul, hid]
  rw [hform]
  refine spectralFunction_posSemidef hM.1 _ fun i => ?_
  rcases hdich i with h0 | hge
  · rw [h0]
    norm_num
  · by_cases hl : 0 < hM.1.eigenvalues i
    · rw [if_pos hl]
      linarith
    · have hzero : hM.1.eigenvalues i = 0 :=
        le_antisymm (not_lt.mp hl) (hM.eigenvalues_nonneg i)
      rw [if_neg hl, hzero]
      norm_num

/-- **The per-cutoff Howe floor**: the quadratic form of a positive
semidefinite commutant Laplacian dominates its least positive eigenvalue on
the unprotected complement — `μ·⟨v, Q v⟩ ≤ ⟨v, M v⟩` with `Q` the support
projection. -/
theorem rayleigh_ge_gap_complement {M : Matrix n n ℂ}
    (hM : M.PosSemidef) (μ : ℝ)
    (hdich : ∀ i, hM.1.eigenvalues i = 0 ∨ μ ≤ hM.1.eigenvalues i)
    (v : n → ℂ) :
    μ * rayleigh (supportProj hM.1) v ≤ rayleigh M v := by
  have hpsd := psd_sub_gap_supportProj_posSemidef hM μ hdich
  have h0 := rayleigh_nonneg hpsd v
  rw [rayleigh_sub, rayleigh_smul] at h0
  linarith

/-- The unprotected residual is nonnegative: the support projection is
positive semidefinite. -/
theorem rayleigh_supportProj_nonneg {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (v : n → ℂ) : 0 ≤ rayleigh (supportProj hM) v :=
  rayleigh_nonneg (supportProj_posSemidef hM) v

end ContinuumHowe
end NCG
