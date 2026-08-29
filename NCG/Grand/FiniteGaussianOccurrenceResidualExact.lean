/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteGrassmannWickExteriorExact
import NCG.Grand.NaimarkPhaseSharpness

/-!
# Exact finite Gaussian-occurrence residual

This file proves `thm:SMQG-Gaussian-occurrence` on a complete finite represented
word bank.  The directly acquired kernel and the Wick--exterior prediction are
compared on every represented grade.  The occurrence residual is the sum of
the squared Hilbert--Schmidt discrepancies.  Its vanishing is proved equivalent
to equality of every represented mixed coefficient, not merely stipulated.

The held-out grade-two prediction is exposed separately, together with the
strict positivity criterion for a failed held-out test.
-/

open Matrix Finset

namespace NCG
namespace FiniteGaussianOccurrenceResidual

open FiniteCompoundMatrixExteriorPower

variable {f : Type*} [Fintype f] [DecidableEq f]

/-- The grade-`r` quasi-free kernel predicted from scalar line weight `q`,
one-particle covariance `P`, and one-sided synthesis `W`. -/
noncomputable def quasiFreeGradeKernel {d : ℕ} (q : ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (r : ℕ)
    (W : Matrix (GradeIdx r d) f ℂ) : Matrix f f ℂ :=
  q • (Wᴴ * cmpd r P * W)

/-- Complete represented Gaussian occurrence residual through the top
fermionic grade. -/
noncomputable def gaussianOccurrenceResidual {d : ℕ}
    (Kdir : (r : ℕ) → Matrix f f ℂ) (q : ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (W : (r : ℕ) → Matrix (GradeIdx r d) f ℂ) : ℝ :=
  ∑ r ∈ Finset.range (d + 1),
    hsFrobSq (Kdir r - quasiFreeGradeKernel q P r (W r))

theorem gaussianOccurrenceResidual_nonneg {d : ℕ}
    (Kdir : (r : ℕ) → Matrix f f ℂ) (q : ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (W : (r : ℕ) → Matrix (GradeIdx r d) f ℂ) :
    0 ≤ gaussianOccurrenceResidual Kdir q P W :=
  Finset.sum_nonneg fun r _ => hsFrobSq_nonneg _

/-- Vanishing of the complete residual is equivalent to equality of every
represented grade with its Wick--exterior kernel. -/
theorem gaussianOccurrenceResidual_eq_zero_iff {d : ℕ}
    (Kdir : (r : ℕ) → Matrix f f ℂ) (q : ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (W : (r : ℕ) → Matrix (GradeIdx r d) f ℂ) :
    gaussianOccurrenceResidual Kdir q P W = 0 ↔
      ∀ r ∈ Finset.range (d + 1),
        Kdir r = quasiFreeGradeKernel q P r (W r) := by
  rw [gaussianOccurrenceResidual, Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h r hr
      exact sub_eq_zero.mp ((hsFrobSq_eq_zero_iff _).mp (h r hr))
    · intro h r hr
      exact (hsFrobSq_eq_zero_iff _).mpr (sub_eq_zero.mpr (h r hr))
  · intro r hr
    exact hsFrobSq_nonneg _

/-- The held-out grade-two coefficient is exactly the exterior Wick
prediction `q W₂ᴴ (⋀²P) W₂`. -/
theorem heldOutGradeTwo_prediction {d : ℕ} (q : ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (W₂ : Matrix (GradeIdx 2 d) f ℂ) :
    quasiFreeGradeKernel q P 2 W₂ = q • (W₂ᴴ * cmpd 2 P * W₂) := rfl

/-- A held-out grade-two discrepancy has strictly positive squared
Hilbert--Schmidt residual exactly when the direct coefficient differs from the
Gaussian prediction. -/
theorem heldOutGradeTwo_residual_pos_iff_ne {d : ℕ} (q : ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (W₂ : Matrix (GradeIdx 2 d) f ℂ) (K₂ : Matrix f f ℂ) :
    0 < hsFrobSq (K₂ - quasiFreeGradeKernel q P 2 W₂) ↔
      K₂ ≠ quasiFreeGradeKernel q P 2 W₂ := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨_, hne⟩ heq
    apply hne
    exact ((hsFrobSq_eq_zero_iff _).mpr (sub_eq_zero.mpr heq)).symm
  · intro hne
    refine ⟨hsFrobSq_nonneg _, ?_⟩
    intro hz
    exact hne (sub_eq_zero.mp ((hsFrobSq_eq_zero_iff _).mp hz.symm))

/-- **`thm:SMQG-Gaussian-occurrence`.**  On a complete finite represented
word bank, zero occurrence residual is equivalent to the directly occurring
functional being the `q`-weighted gauge-invariant Gaussian functional on every
represented grade; grade two supplies an independent held-out falsification
test. -/
theorem smqg_exact_Gaussian_occurrence {d : ℕ}
    (Kdir : (r : ℕ) → Matrix f f ℂ) (q : ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (W : (r : ℕ) → Matrix (GradeIdx r d) f ℂ) :
    (gaussianOccurrenceResidual Kdir q P W = 0 ↔
      ∀ r ∈ Finset.range (d + 1),
        Kdir r = quasiFreeGradeKernel q P r (W r)) ∧
      quasiFreeGradeKernel q P 2 (W 2) =
        q • ((W 2)ᴴ * cmpd 2 P * W 2) :=
  ⟨gaussianOccurrenceResidual_eq_zero_iff Kdir q P W,
    heldOutGradeTwo_prediction q P (W 2)⟩

end FiniteGaussianOccurrenceResidual
end NCG
