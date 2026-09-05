/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DenseSourceStrongConvergence

/-!
# Pointwise operator convergence from a dense core

Uniformly bounded continuous linear operators on one Hilbert space converge strongly everywhere
once they converge on a dense subset.  This fixed-space wrapper specializes the varying-Hilbert
dense-source theorem to the constant comparison system.
-/

open Filter Set Topology

noncomputable section

namespace NCG

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- A uniformly operator-norm-bounded sequence is strongly convergent everywhere if it converges
pointwise on a dense subset. -/
theorem tendsto_apply_of_dense_of_uniform_opNorm
    (Tn : ℕ → E →L[K] E) (T : E →L[K] E)
    (D : Set E) (hD : Dense D)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖Tn n‖ ≤ C)
    (hcore : ∀ d ∈ D, Tendsto (fun n ↦ Tn n d) atTop (𝓝 (T d))) :
    ∀ x : E, Tendsto (fun n ↦ Tn n x) atTop (𝓝 (T x)) := by
  let J := NCG.VaryingHilbert.constantSystem K E
  have hsource : ∀ d ∈ D,
      J.StronglyConverges (fun _ : ℕ ↦ d) d := by
    intro d hd
    simp [J, NCG.VaryingHilbert.constantSystem, NCG.VaryingHilbert.System.StronglyConverges]
  have hcore' : ∀ d ∈ D,
      J.StronglyConverges (fun n ↦ Tn n d) (T d) := by
    intro d hd
    simpa [J, NCG.VaryingHilbert.constantSystem,
      NCG.VaryingHilbert.System.StronglyConverges] using hcore d hd
  have hall := J.strongOperatorConverges_of_dense_sources_of_uniform_opNorm
    J Tn T D hD (fun d _ ↦ d) hsource C hC hbound hcore'
  intro x
  have hx : J.StronglyConverges (fun _ : ℕ ↦ x) x := by
    simp [J, NCG.VaryingHilbert.constantSystem, NCG.VaryingHilbert.System.StronglyConverges]
  simpa [J, NCG.VaryingHilbert.constantSystem, NCG.VaryingHilbert.System.StronglyConverges] using
    hall (fun _ : ℕ ↦ x) x hx

end NCG
