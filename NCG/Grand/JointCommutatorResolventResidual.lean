/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorResolventFamily
import NCG.Grand.OperatorGraphResolventBound

/-!
# Residual estimates for finite joint-commutator resolvents

The canonical finite resolver is the inverse of the shifted commutant
Laplacian.  Its sharp `1 / λ` norm bound converts an approximate shifted normal
equation into a quantitative resolver error estimate.
-/

noncomputable section

namespace NCG

universe u

/-- The canonical finite resolver is a left inverse of the shifted commutant
Laplacian. -/
theorem jointCommutatorResolventFamily_shifted_apply
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (lam : ℝ) (hlam : 0 < lam) (cutoff : ℕ)
    (u : EuclideanSpace ℂ (d cutoff × d cutoff)) :
    jointCommutatorResolventFamily c lam cutoff
        (shiftedCommutantLaplacianCLM (c cutoff) lam u) = u := by
  rw [jointCommutatorResolventFamily, jointCommutatorResolventAllShifts,
    dif_pos hlam]
  change (shiftedCommutantLaplacianEquiv (c cutoff) lam hlam).symm
      (shiftedCommutantLaplacianEquiv (c cutoff) lam hlam u) = u
  exact (shiftedCommutantLaplacianEquiv (c cutoff) lam hlam).symm_apply_apply u

/-- Resolver error is the resolver applied to the shifted-equation residual. -/
theorem jointCommutatorResolventFamily_sub_eq_resolvent_residual
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (lam : ℝ) (hlam : 0 < lam) (cutoff : ℕ)
    (f u : EuclideanSpace ℂ (d cutoff × d cutoff)) :
    jointCommutatorResolventFamily c lam cutoff f - u =
      jointCommutatorResolventFamily c lam cutoff
        (f - shiftedCommutantLaplacianCLM (c cutoff) lam u) := by
  rw [map_sub, jointCommutatorResolventFamily_shifted_apply c lam hlam cutoff u]

/-- Sharp approximate-solution estimate for the canonical finite resolver. -/
theorem norm_jointCommutatorResolventFamily_sub_le_residual_div
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (lam : ℝ) (hlam : 0 < lam) (cutoff : ℕ)
    (f u : EuclideanSpace ℂ (d cutoff × d cutoff)) :
    ‖jointCommutatorResolventFamily c lam cutoff f - u‖ ≤
      ‖f - shiftedCommutantLaplacianCLM (c cutoff) lam u‖ / lam := by
  rw [jointCommutatorResolventFamily_sub_eq_resolvent_residual
    c lam hlam cutoff f u]
  have hnorm : ‖jointCommutatorResolventFamily c lam cutoff‖ ≤ 1 / lam :=
    NCG.VaryingHilbert.operatorGraphResolvent_opNorm_le_inv
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
      (NCG.VaryingHilbert.boundedOperatorGraphMap
        (jointCommutatorCLM (c cutoff)))
      (jointCommutatorResolventFamily c lam cutoff) lam hlam
      (jointCommutatorResolventFamily_resolventEquation c lam hlam cutoff)
  calc
    ‖jointCommutatorResolventFamily c lam cutoff
        (f - shiftedCommutantLaplacianCLM (c cutoff) lam u)‖ ≤
        ‖jointCommutatorResolventFamily c lam cutoff‖ *
          ‖f - shiftedCommutantLaplacianCLM (c cutoff) lam u‖ :=
      (jointCommutatorResolventFamily c lam cutoff).le_opNorm _
    _ ≤ (1 / lam) *
        ‖f - shiftedCommutantLaplacianCLM (c cutoff) lam u‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖f - shiftedCommutantLaplacianCLM (c cutoff) lam u‖ / lam := by
      ring

end NCG
