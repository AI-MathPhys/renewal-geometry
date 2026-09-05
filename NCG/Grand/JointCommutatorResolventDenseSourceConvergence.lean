/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DenseSourceStrongConvergence
import NCG.Grand.JointCommutatorResolventFamily
import NCG.Grand.OperatorGraphResolventBound

/-!
# Joint-commutator resolvent convergence from dense sources

Canonical positive-shift joint-commutator resolvents have the sharp uniform
operator bound `1 / λ`.  Convergence on compatible lifts of a dense source
set therefore implies strong operator convergence.  Reindexing those same
dense lifts gives the cofinal strong convergence needed by Mosco compilers.
-/

open Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Dense-source convergence of one canonical joint-commutator resolvent
implies varying-Hilbert strong operator convergence at that shift. -/
theorem jointCommutatorResolvent_strongOperatorConverges_of_denseSources
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (T : H →L[ℂ] H) (lam : ℝ) (hlam : 0 < lam)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ x ∈ D, J.StronglyConverges (source x) x)
    (hconv : ∀ x ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam cutoff
        (source x cutoff))
      (T x)) :
    J.StrongOperatorConverges J
      (NCG.jointCommutatorResolventFamily c lam) T := by
  apply J.strongOperatorConverges_of_dense_sources_of_uniform_opNorm
    J (NCG.jointCommutatorResolventFamily c lam) T
    D hD source hsource (1 / lam) (by positivity)
  · intro cutoff
    exact operatorGraphResolvent_opNorm_le_inv
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
      (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
      (NCG.jointCommutatorResolventFamily c lam cutoff) lam hlam
      (NCG.jointCommutatorResolventFamily_resolventEquation
        c lam hlam cutoff)
  · exact hconv

/-- The same dense-source test automatically gives strong operator convergence
after every cofinal reindexing.  Thus applications need only prove convergence
of the canonical resolvent on one fixed dense source family. -/
theorem jointCommutatorResolvent_cofinalStrongOperatorConverges_of_denseSources
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (T : H →L[ℂ] H) (lam : ℝ) (hlam : 0 < lam)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ x ∈ D, J.StronglyConverges (source x) x)
    (hconv : ∀ x ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam cutoff
        (source x cutoff))
      (T x)) :
    ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
      (J.reindex φ).StrongOperatorConverges (J.reindex φ)
        (fun cutoff ↦
          NCG.jointCommutatorResolventFamily c lam (φ cutoff)) T := by
  intro φ hφ
  apply (J.reindex φ).strongOperatorConverges_of_dense_sources_of_uniform_opNorm
    (J.reindex φ)
    (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam (φ cutoff))
    T D hD (fun x cutoff ↦ source x (φ cutoff))
    (fun x hx ↦ (hsource x hx).reindex J hφ)
    (1 / lam) (by positivity)
  · intro cutoff
    exact operatorGraphResolvent_opNorm_le_inv
      (⊤ : Submodule ℂ
        (EuclideanSpace ℂ (d (φ cutoff) × d (φ cutoff))))
      (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c (φ cutoff))))
      (NCG.jointCommutatorResolventFamily c lam (φ cutoff)) lam hlam
      (NCG.jointCommutatorResolventFamily_resolventEquation
        c lam hlam (φ cutoff))
  · intro x hx
    exact (hconv x hx).reindex J hφ

end NCG.VaryingHilbert.System
