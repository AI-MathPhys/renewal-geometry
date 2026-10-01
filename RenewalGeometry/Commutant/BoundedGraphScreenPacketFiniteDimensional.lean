/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.CofinalSpectralUpgradeExact
import RenewalGeometry.Commutant.JointCommutatorBoundedKernelSpectralConsequencesFromDenseSourcesAndGraphScreens

/-!
# The bounded-limit graph-screen packet forces a finite-dimensional carrier

Audit lemma for the graph-screen rendering used by `cofinalSpectralUpgrade_exact` and
`coerciveContinuumHoweDuality_exact` (`cor:cofinal-spectral-upgrade`, `thm:cofinal-duality`
former version, `prop:protected-kernel-locking`).

In that packet the continuum resolvent is the canonical bounded normal resolvent
`R_b = (A† A + b)⁻¹` of a **bounded** operator `A : H →L F`, and the compact graph-screen tail
makes `R_b` compact (`jointCommutator_boundedKernelSpectralConsequences_of_denseSources_of_graphScreens`).
Since `(A† A + b) R_b = I`, the identity is then compact and `H` is finite dimensional
(`boundedGraphScreenPacket_finiteDimensional`).  Hence the packet together with the hypothesis
`¬ FiniteDimensional ℂ H` is contradictory (`cofinalSpectralUpgrade_packet_false`): the theorems
stated under it hold vacuously.  A faithful rendering of the compact spectral upgrade must use
an unbounded limiting form (as `operatorGraphMosco_lowSpectrumConvergence_of_graphScreens` does).
-/

open Complex Filter Set Topology

noncomputable section

namespace RenewalGeometry.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- **Audit: the bounded-limit graph-screen packet forces `dim H < ∞`.** -/
theorem boundedGraphScreenPacket_finiteDimensional
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : RenewalGeometry.VaryingHilbert.System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : RenewalGeometry.VaryingHilbert.System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hcore : ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ RenewalGeometry.jointCommutatorResolventFamily c lam0 cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam0 y))
    (a : ℝ) (ha : 0 < a)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ screenIndex, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM (c cutoff)))
        (RenewalGeometry.jointCommutatorResolventFamily c a cutoff) a ha
        (RenewalGeometry.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      ‖y - screen screenIndex y‖ < ε)
    (hfst : ∀ cutoff y, J.embedding cutoff y.fst = (L.embedding cutoff y).fst)
    (b : ℝ) (hb : 0 < b) :
    FiniteDimensional ℂ H := by
  obtain ⟨_, _, _, _, hRcompact, _⟩ :=
    J.jointCommutator_boundedKernelSpectralConsequences_of_denseSources_of_graphScreens
      (iota := PEmpty.{1}) c L A lam0 hlam0 D hD source hsource hcore a ha screen hcompact
      htail hfst b hb (fun _ e => e.elim) (fun e => e.elim) (fun e => e.elim)
  let T : H →L[ℂ] H := ContinuousLinearMap.adjoint A ∘L A + (b : ℂ) • ContinuousLinearMap.id ℂ H
  have hid : (T ∘ boundedOperatorNormalResolventFamily A b) = (_root_.id : H → H) := by
    funext f
    change (ContinuousLinearMap.adjoint A ∘L A) (boundedOperatorNormalResolventFamily A b f) +
      ((b : ℂ) • ContinuousLinearMap.id ℂ H) (boundedOperatorNormalResolventFamily A b f) = f
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    exact boundedOperatorNormalResolventFamily_normalEquation A b hb f
  have hcomp : IsCompactOperator (T ∘ boundedOperatorNormalResolventFamily A b) :=
    hRcompact.clm_comp T
  rw [hid] at hcomp
  exact FiniteDimensional.of_isCompactOperator_id hcomp

/-- **Audit: the hypotheses of `cofinalSpectralUpgrade_exact` (and of
`coerciveContinuumHoweDuality_exact`) are contradictory**, because the graph-screen packet with
a bounded limit forces `FiniteDimensional ℂ H` while the packet also assumes the opposite. -/
theorem cofinalSpectralUpgrade_packet_false
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : RenewalGeometry.VaryingHilbert.System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : RenewalGeometry.VaryingHilbert.System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hcore : ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ RenewalGeometry.jointCommutatorResolventFamily c lam0 cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam0 y))
    (a : ℝ) (ha : 0 < a)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ screenIndex, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM (c cutoff)))
        (RenewalGeometry.jointCommutatorResolventFamily c a cutoff) a ha
        (RenewalGeometry.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      ‖y - screen screenIndex y‖ < ε)
    (hfst : ∀ cutoff y, J.embedding cutoff y.fst = (L.embedding cutoff y).fst)
    (b : ℝ) (hb : 0 < b)
    (hinfinite : ¬FiniteDimensional ℂ H) : False :=
  hinfinite (boundedGraphScreenPacket_finiteDimensional c J L A lam0 hlam0 D hD source hsource
    hcore a ha screen hcompact htail hfst b hb)

end RenewalGeometry.VaryingHilbert.System
