/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedOperatorNormalResolventConvergence
import NCG.Grand.CovariantFourierOperatorStack
import NCG.Grand.FiniteTorusCovariantSymbolCutoffLimit

/-!
# Convergence of covariant Fourier stack resolvents

The normal operators of the directional stacks are the full covariant
Laplacian symbols.  Symbol convergence therefore implies operator-norm
convergence of the positive-shift stack resolvents, first at one integer mode
and then uniformly on every fixed finite Fourier box.
-/

open Filter Topology
open scoped InnerProduct

noncomputable section

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Nontrivial E]

theorem shifted_meshCovariantFourierOperatorStack_tendsto_cutoff
    (k : d → ℤ) (B : d → E →L[ℂ] E) (lam : ℝ) :
    Tendsto
      (fun N : ℕ ↦ VaryingHilbert.shiftedBoundedNormalCLM
        (meshCovariantFourierOperatorStack (finiteTorusCutoffMesh N) k B) lam)
      atTop
      (𝓝 (VaryingHilbert.shiftedBoundedNormalCLM
        (continuumCovariantFourierOperatorStack k B) lam)) := by
  have hL := meshCovariantLaplacianSymbol_tendsto_cutoff k B
  simpa only [VaryingHilbert.shiftedBoundedNormalCLM,
    meshCovariantFourierOperatorStack_adjoint_comp,
    continuumCovariantFourierOperatorStack_adjoint_comp] using
    hL.add tendsto_const_nhds

/-- Fixed-mode operator-norm convergence of the canonical stack
resolvents. -/
theorem meshCovariantFourierOperatorStack_resolvent_tendsto_cutoff
    (k : d → ℤ) (B : d → E →L[ℂ] E)
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto
      (fun N : ℕ ↦ VaryingHilbert.boundedOperatorNormalResolvent
        (meshCovariantFourierOperatorStack (finiteTorusCutoffMesh N) k B)
        lam hlam)
      atTop
      (𝓝 (VaryingHilbert.boundedOperatorNormalResolvent
        (continuumCovariantFourierOperatorStack k B) lam hlam)) :=
  VaryingHilbert.boundedOperatorNormalResolvent_tendsto_of_shifted
    (fun N : ℕ ↦
      meshCovariantFourierOperatorStack (finiteTorusCutoffMesh N) k B)
    (continuumCovariantFourierOperatorStack k B) lam hlam
    (shifted_meshCovariantFourierOperatorStack_tendsto_cutoff k B lam)

/-- On a fixed finite Fourier box, all stack resolvent blocks are eventually
uniformly close. -/
theorem eventually_forall_mem_finset_meshStack_resolvents_close
    (s : Finset (d → ℤ)) (B : d → E →L[ℂ] E)
    (lam : ℝ) (hlam : 0 < lam) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ s,
      ‖VaryingHilbert.boundedOperatorNormalResolvent
          (meshCovariantFourierOperatorStack
            (finiteTorusCutoffMesh N) k B) lam hlam -
        VaryingHilbert.boundedOperatorNormalResolvent
          (continuumCovariantFourierOperatorStack k B) lam hlam‖ < ε := by
  filter_upwards
      [eventually_forall_mem_finset_dist_lt_of_tendsto s
        (fun k _ ↦
          meshCovariantFourierOperatorStack_resolvent_tendsto_cutoff
            k B lam hlam) hε]
      with N hN k hk
  simpa only [dist_eq_norm] using hN k hk

end NCG
