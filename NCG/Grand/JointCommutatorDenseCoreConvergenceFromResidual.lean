/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorResolventResidual
import NCG.Grand.BoundedOperatorNormalResolventFamily
import NCG.Grand.VaryingHilbertAsymptoticDensityFromDenseSources
import NCG.Grand.VaryingHilbertNormalOperatorConvergence
import NCG.Grand.VaryingHilbertCompressedOperators

/-!
# Dense-core joint-commutator resolvent convergence from consistency residuals

To prove convergence of the canonical finite resolvents on a dense core, it is
enough to construct stage candidates converging to the desired continuum
resolvent output and prove that their finite shifted-normal-equation residuals
tend to zero.  The sharp residual estimate makes the actual finite resolver
outputs converge automatically.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Candidate convergence plus a vanishing discrete normal-equation residual
implies convergence of the canonical finite joint-commutator resolvers. -/
theorem jointCommutator_denseCoreConvergence_of_normalResidual
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (lam : ℝ) (hlam : 0 < lam)
    (R : H →L[ℂ] H) (D : Set H)
    (source candidate : H → ∀ cutoff,
      EuclideanSpace ℂ (d cutoff × d cutoff))
    (hcandidate : ∀ y ∈ D, J.StronglyConverges (candidate y) (R y))
    (hresidual : ∀ y ∈ D, Tendsto
      (fun cutoff ↦
        ‖source y cutoff -
          NCG.shiftedCommutantLaplacianCLM (c cutoff) lam
            (candidate y cutoff)‖)
      atTop (nhds 0)) :
    ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam cutoff
        (source y cutoff))
      (R y) := by
  intro y hy
  let err : ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff) :=
    fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam cutoff
      (source y cutoff) - candidate y cutoff
  have herr : J.StronglyConverges err 0 := by
    rw [StronglyConverges, tendsto_zero_iff_norm_tendsto_zero]
    have hupper : ∀ cutoff,
        ‖J.embedding cutoff (err cutoff)‖ ≤
          ‖source y cutoff -
            NCG.shiftedCommutantLaplacianCLM (c cutoff) lam
              (candidate y cutoff)‖ / lam := by
      intro cutoff
      rw [LinearIsometry.norm_map]
      exact NCG.norm_jointCommutatorResolventFamily_sub_le_residual_div
        c lam hlam cutoff (source y cutoff) (candidate y cutoff)
    have hright : Tendsto
        (fun cutoff ↦
          ‖source y cutoff -
            NCG.shiftedCommutantLaplacianCLM (c cutoff) lam
              (candidate y cutoff)‖ / lam)
        atTop (nhds 0) := by
      simpa using (hresidual y hy).div_const lam
    exact squeeze_zero (fun cutoff ↦ norm_nonneg _) hupper hright
  have hsum := NCG.VaryingHilbert.System.StronglyConverges.add
    J (hcandidate y hy) herr
  have hseq :
      (fun cutoff ↦ candidate y cutoff + err cutoff) =
        (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam cutoff
          (source y cutoff)) := by
    funext cutoff
    dsimp only [err]
    abel
  rw [← hseq]
  simpa using hsum

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace H] [CompleteSpace F]

/-- Canonical-continuum specialization: only convergence of consistent
candidates and their finite normal residuals remains to prove. -/
theorem jointCommutator_denseCoreConvergence_to_boundedNormalResolvent_of_normalResidual
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) (D : Set H)
    (source candidate : H → ∀ cutoff,
      EuclideanSpace ℂ (d cutoff × d cutoff))
    (hcandidate : ∀ y ∈ D, J.StronglyConverges (candidate y)
      (boundedOperatorNormalResolventFamily A lam y))
    (hresidual : ∀ y ∈ D, Tendsto
      (fun cutoff ↦
        ‖source y cutoff -
          NCG.shiftedCommutantLaplacianCLM (c cutoff) lam
            (candidate y cutoff)‖)
      atTop (nhds 0)) :
    ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam y) := by
  exact J.jointCommutator_denseCoreConvergence_of_normalResidual
    c lam hlam (boundedOperatorNormalResolventFamily A lam)
      D source candidate hcandidate hresidual

/-- Dense compatible source lifts make the adjoint lifts of the canonical
continuum resolver into convergent candidates.  Thus a single explicit
shifted-normal consistency residual proves dense-core resolver convergence. -/
theorem jointCommutator_denseCoreConvergence_to_boundedNormalResolvent_of_adjointLiftResidual
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff,
      EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hresidual : ∀ y ∈ D, Tendsto
      (fun cutoff ↦
        ‖source y cutoff -
          NCG.shiftedCommutantLaplacianCLM (c cutoff) lam
            (J.adjointLift cutoff
              (boundedOperatorNormalResolventFamily A lam y))‖)
      atTop (nhds 0)) :
    ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam y) := by
  have hdense : J.IsAsymptoticallyDense :=
    J.isAsymptoticallyDense_of_denseSources D hD source hsource
  apply J.jointCommutator_denseCoreConvergence_to_boundedNormalResolvent_of_normalResidual
    c A lam hlam D source
      (fun y cutoff ↦ J.adjointLift cutoff
        (boundedOperatorNormalResolventFamily A lam y))
  · intro y hy
    exact J.stronglyConverges_adjointLift hdense
      (boundedOperatorNormalResolventFamily A lam y)
  · exact hresidual

/-- Compatible source lifts need not themselves satisfy a shifted-normal
residual estimate.  It is enough to prove consistency on the canonical
adjoint lifts: asymptotic density makes the source and canonical lifts
automatically close in the native stage norm. -/
theorem jointCommutator_denseCoreConvergence_to_boundedNormalResolvent_of_adjointLiftConsistency
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff,
      EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hconsistency : ∀ y ∈ D, Tendsto
      (fun cutoff ↦
        ‖J.adjointLift cutoff y -
          NCG.shiftedCommutantLaplacianCLM (c cutoff) lam
            (J.adjointLift cutoff
              (boundedOperatorNormalResolventFamily A lam y))‖)
      atTop (nhds 0)) :
    ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam y) := by
  have hdense : J.IsAsymptoticallyDense :=
    J.isAsymptoticallyDense_of_denseSources D hD source hsource
  apply J.jointCommutator_denseCoreConvergence_to_boundedNormalResolvent_of_adjointLiftResidual
    c A lam hlam D hD source hsource
  intro y hy
  have hsourceDiff := StronglyConverges.norm_sub_adjointLift_tendsto_zero
    J hdense (hsource y hy)
  apply squeeze_zero' (g := fun cutoff ↦
    ‖source y cutoff - J.adjointLift cutoff y‖ +
      ‖J.adjointLift cutoff y -
        NCG.shiftedCommutantLaplacianCLM (c cutoff) lam
          (J.adjointLift cutoff
            (boundedOperatorNormalResolventFamily A lam y))‖)
  · exact Eventually.of_forall fun _ ↦ norm_nonneg _
  · exact Eventually.of_forall fun cutoff ↦ by
      rw [show source y cutoff -
          NCG.shiftedCommutantLaplacianCLM (c cutoff) lam
              (J.adjointLift cutoff
                (boundedOperatorNormalResolventFamily A lam y)) =
            (source y cutoff - J.adjointLift cutoff y) +
              (J.adjointLift cutoff y -
                NCG.shiftedCommutantLaplacianCLM (c cutoff) lam
                  (J.adjointLift cutoff
                    (boundedOperatorNormalResolventFamily A lam y))) by abel]
      exact norm_add_le _ _
  · simpa only [add_zero] using hsourceDiff.add (hconsistency y hy)

/-- Strong operator convergence of the shifted finite commutant Laplacians
to the shifted bounded normal operator automatically supplies the canonical
adjoint-lift consistency defect, hence dense-core resolvent convergence. -/
theorem jointCommutator_denseCoreConvergence_of_shiftedNormalStrongConvergence
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff,
      EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hoperator : J.StrongOperatorConverges J
      (fun cutoff ↦ NCG.shiftedCommutantLaplacianCLM (c cutoff) lam)
      (shiftedBoundedNormalCLM A lam)) :
    ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam y) := by
  have hdense : J.IsAsymptoticallyDense :=
    J.isAsymptoticallyDense_of_denseSources D hD source hsource
  apply J.jointCommutator_denseCoreConvergence_to_boundedNormalResolvent_of_adjointLiftConsistency
    c A lam hlam D hD source hsource
  intro y hy
  let u := boundedOperatorNormalResolventFamily A lam y
  have hadj : J.StronglyConverges (fun cutoff ↦ J.adjointLift cutoff u) u :=
    J.stronglyConverges_adjointLift hdense u
  have hout : J.StronglyConverges
      (fun cutoff ↦ NCG.shiftedCommutantLaplacianCLM (c cutoff) lam
        (J.adjointLift cutoff u))
      (shiftedBoundedNormalCLM A lam u) :=
    hoperator _ _ hadj
  have heq : shiftedBoundedNormalCLM A lam u = y := by
    rw [shiftedBoundedNormalCLM_apply]
    exact boundedOperatorNormalResolventFamily_normalEquation A lam hlam y
  have hout' : J.StronglyConverges
      (fun cutoff ↦ NCG.shiftedCommutantLaplacianCLM (c cutoff) lam
        (J.adjointLift cutoff u)) y := by
    simpa only [heq] using hout
  have hdiff := StronglyConverges.norm_sub_adjointLift_tendsto_zero
    J hdense hout'
  simpa only [u, norm_sub_rev] using hdiff

/-- It suffices to prove strong operator convergence of the raw commutant
Laplacians.  Adding the positive scalar shift is automatic because identity
operators converge strongly on every varying-Hilbert system. -/
theorem jointCommutator_denseCoreConvergence_of_commutantLaplacianStrongConvergence
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff,
      EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hnormal : J.StrongOperatorConverges J
      (fun cutoff ↦ NCG.commutantLaplacianCLM (c cutoff))
      ((ContinuousLinearMap.adjoint A).comp A)) :
    ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam y) := by
  have hscalar : J.StrongOperatorConverges J
      (fun _ ↦ (lam : ℂ) • ContinuousLinearMap.id ℂ _)
      ((lam : ℂ) • ContinuousLinearMap.id ℂ H) :=
    StrongOperatorConverges.smul J (lam : ℂ)
      J.strongOperatorConverges_id
  have hshift : J.StrongOperatorConverges J
      (fun cutoff ↦ NCG.shiftedCommutantLaplacianCLM (c cutoff) lam)
      (shiftedBoundedNormalCLM A lam) := by
    simpa only [NCG.shiftedCommutantLaplacianCLM,
      shiftedBoundedNormalCLM, ContinuousLinearMap.one_def] using
        StrongOperatorConverges.add J hnormal hscalar
  exact J.jointCommutator_denseCoreConvergence_of_shiftedNormalStrongConvergence
    c A lam hlam D hD source hsource hshift

/-- First-order convergence of the finite joint commutator maps and their
adjoints implies convergence of their commutant Laplacians, and therefore
dense-core convergence of the canonical finite resolvents. -/
theorem jointCommutator_denseCoreConvergence_of_commutatorAndAdjointConvergence
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := F)
      (Hn := fun cutoff ↦
        EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff))))
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff,
      EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hcommutator : J.StrongOperatorConverges L
      (fun cutoff ↦ NCG.jointCommutatorCLM (c cutoff)) A)
    (hadjoint : L.StrongOperatorConverges J
      (fun cutoff ↦ ContinuousLinearMap.adjoint
        (NCG.jointCommutatorCLM (c cutoff)))
      (ContinuousLinearMap.adjoint A)) :
    ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam y) := by
  have hnormal : J.StrongOperatorConverges J
      (fun cutoff ↦ NCG.commutantLaplacianCLM (c cutoff))
      ((ContinuousLinearMap.adjoint A).comp A) := by
    simpa only [NCG.commutantLaplacianCLM] using
      StrongOperatorConverges.adjoint_comp_self J L hcommutator hadjoint
  exact J.jointCommutator_denseCoreConvergence_of_commutantLaplacianStrongConvergence
    c A lam hlam D hD source hsource hnormal

end NCG.VaryingHilbert.System
