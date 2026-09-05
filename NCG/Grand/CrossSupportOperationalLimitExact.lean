/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CrossSupportGenerator

/-!
# Operational small-time extraction of cross support

This file adds the analytic clause of `thm:SM-cross-support-generator`: the derivative at zero of
the compressed semigroup is reconstructed by its right-hand difference quotient.  It then bundles
that limit with the already proved GKSL compression identities and Kraus positivity.
-/

open Matrix Filter Set
open scoped Topology ComplexOrder

namespace NCG

/-- A differentiable matrix path through zero is recovered from its right difference quotient. -/
theorem tendsto_inv_smul_of_hasDerivAt_zero {n : Type*} [Fintype n] [DecidableEq n]
    (F : ℝ → Matrix n n ℂ) (A : Matrix n n ℂ)
    (hF0 : F 0 = 0)
    (hF : ∀ i j, HasDerivAt (fun t ↦ F t i j) (A i j) 0) :
    Tendsto (fun t : ℝ ↦ t⁻¹ • F t) (nhdsWithin 0 (Ioi 0)) (nhds A) := by
  change Tendsto (fun t i j ↦ t⁻¹ • F t i j) (nhdsWithin 0 (Ioi 0)) (nhds (fun i j ↦ A i j))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  simpa [hF0] using (hF i j).tendsto_slope_zero_right

/-- The operational `L ← R` compression is the right derivative of the physical semigroup. -/
theorem crossSupport_operational_smallTime_limit {n : Type*} [Fintype n] [DecidableEq n]
    (PL PR : Matrix n n ℂ) (T : ℝ → Matrix n n ℂ) (L X : Matrix n n ℂ)
    (hzero : PL * T 0 * PL = 0)
    (hdiff : ∀ i j, HasDerivAt (fun t ↦ (PL * T t * PL) i j) ((PL * L * PL) i j) 0) :
    Tendsto (fun t : ℝ ↦ t⁻¹ • (PL * T t * PL))
      (nhdsWithin 0 (Ioi 0)) (nhds (PL * L * PL)) :=
  tendsto_inv_smul_of_hasDerivAt_zero (fun t ↦ PL * T t * PL) (PL * L * PL) hzero hdiff

/-- Full exact package for `thm:SM-cross-support-generator`, including the operational limit. -/
theorem cross_support_generator_exact {n : Type*} [Fintype n] [DecidableEq n]
    (PL PR : Matrix n n ℂ) (hLR : PL * PR = 0) (hRL : PR * PL = 0)
    (H V X : Matrix n n ℂ) (T : ℝ → Matrix n n ℂ)
    (hzero : PL * T 0 * PL = 0)
    (hdiff : ∀ i j, HasDerivAt (fun t ↦ (PL * T t * PL) i j)
      ((PL * (H * (PR * X * PR) - (PR * X * PR) * H
        + V * (PR * X * PR) * Vᴴ
        - (2 : ℂ)⁻¹ • ((Vᴴ * V) * (PR * X * PR)
          + (PR * X * PR) * (Vᴴ * V))) * PL) i j) 0) :
    (PL * (H * (PR * X * PR) - (PR * X * PR) * H) * PL = 0)
    ∧ (PL * ((Vᴴ * V) * (PR * X * PR)
        + (PR * X * PR) * (Vᴴ * V)) * PL = 0)
    ∧ (PL * (V * (PR * X * PR) * Vᴴ) * PL
        = (PL * V * PR) * X * (PR * Vᴴ * PL))
    ∧ (∀ Y : Matrix n n ℂ, Y.PosSemidef →
        ((PL * V * PR) * Y * (PL * V * PR)ᴴ).PosSemidef)
    ∧ Tendsto (fun t : ℝ ↦ t⁻¹ • (PL * T t * PL))
        (nhdsWithin 0 (Ioi 0))
        (nhds ((PL * V * PR) * X * (PR * Vᴴ * PL))) := by
  obtain ⟨hHam, hAnti, hJump, hPos⟩ := cross_support_generator PL PR hLR hRL H V X
  refine ⟨hHam, hAnti, hJump, hPos, ?_⟩
  have hlim := tendsto_inv_smul_of_hasDerivAt_zero
    (fun t ↦ PL * T t * PL)
    (PL * (H * (PR * X * PR) - (PR * X * PR) * H
      + V * (PR * X * PR) * Vᴴ
      - (2 : ℂ)⁻¹ • ((Vᴴ * V) * (PR * X * PR)
        + (PR * X * PR) * (Vᴴ * V))) * PL) hzero hdiff
  have hgen :
      PL * (H * (PR * X * PR) - (PR * X * PR) * H
        + V * (PR * X * PR) * Vᴴ
        - (2 : ℂ)⁻¹ • ((Vᴴ * V) * (PR * X * PR)
          + (PR * X * PR) * (Vᴴ * V))) * PL
        = (PL * V * PR) * X * (PR * Vᴴ * PL) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, hHam, hJump, hAnti]
    simp
  rw [hgen] at hlim
  exact hlim

end NCG
