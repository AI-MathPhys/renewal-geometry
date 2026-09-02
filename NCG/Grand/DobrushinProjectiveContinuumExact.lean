/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Dobrushin projective continuum estimate

This file proves the comparison and convergence core of
`thm:SMFS-projective-continuum`.  A nonnegative Dobrushin resolvent with
column mass at most `(1-α)⁻¹` transports a direct local/collar mismatch into
the exact adjacent-writer bound.  Vanishing defects give the U4 adjacent
compatibility row, while summable defects make every fixed writer Cauchy and
hence give the U3 full-tail limit in a complete target.
-/

open Finset Filter
open scoped BigOperators Topology

noncomputable section

namespace NCG.DobrushinProjectiveContinuum

variable {I E : Type*}

/-- Total response after interpolation through the nonnegative influence
resolvent.  The index `j` locates the changed block and `i` the observed
block. -/
def influenceResponse [Fintype I] (R : I → I → ℝ) (direct : I → ℝ) : ℝ :=
  ∑ i, ∑ j, R i j * direct j

theorem influenceResponse_nonnegative [Fintype I]
    (R : I → I → ℝ) (direct : I → ℝ)
    (hR : ∀ i j, 0 ≤ R i j) (hdirect : ∀ j, 0 ≤ direct j) :
    0 ≤ influenceResponse R direct := by
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hR i j) (hdirect j)

/-- The Dobrushin comparison estimate: column mass of the resolvent times
the total direct mismatch. -/
theorem influenceResponse_le
    [Fintype I] (R : I → I → ℝ) (direct : I → ℝ)
    (alpha defect : ℝ)
    (hR : ∀ i j, 0 ≤ R i j)
    (hdirect : ∀ j, 0 ≤ direct j)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hcolumn : ∀ j, ∑ i, R i j ≤ (1 - alpha)⁻¹)
    (hdirectMass : ∑ j, direct j ≤ defect) :
    influenceResponse R direct ≤ (1 - alpha)⁻¹ * defect := by
  have hinv0 : 0 ≤ (1 - alpha)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr halpha1.le)
  rw [influenceResponse, Finset.sum_comm]
  calc
    ∑ j, ∑ i, R i j * direct j =
        ∑ j, (∑ i, R i j) * direct j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ ≤ ∑ j, (1 - alpha)⁻¹ * direct j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hcolumn j) (hdirect j)
    _ = (1 - alpha)⁻¹ * ∑ j, direct j := by rw [Finset.mul_sum]
    _ ≤ (1 - alpha)⁻¹ * defect :=
      mul_le_mul_of_nonneg_left hdirectMass hinv0

/-- A resolved one-step projective comparison packet.  It contains only the
local interpolation identity/inequality supplied by the Gibbs specification;
the global Dobrushin factor and every continuum consequence are derived. -/
structure AdjacentComparison [Fintype I] (E : Type*) [PseudoMetricSpace E]
    (alpha : ℝ) where
  expected : ℕ → E
  resolvent : ℕ → I → I → ℝ
  directMismatch : ℕ → I → ℝ
  defect : ℕ → ℝ
  writerConstant : ℝ
  writerConstant_nonnegative : 0 ≤ writerConstant
  resolvent_nonnegative : ∀ n i j, 0 ≤ resolvent n i j
  direct_nonnegative : ∀ n j, 0 ≤ directMismatch n j
  resolvent_column : ∀ n j,
    ∑ i, resolvent n i j ≤ (1 - alpha)⁻¹
  direct_mass : ∀ n, ∑ j, directMismatch n j ≤ defect n
  interpolation : ∀ n,
    dist (expected (n + 1)) (expected n) ≤
      writerConstant * influenceResponse (resolvent n) (directMismatch n)

theorem adjacent_projective_bound [Fintype I]
    [PseudoMetricSpace E] (alpha : ℝ)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (P : AdjacentComparison (I := I) E alpha) :
    ∀ n, dist (P.expected (n + 1)) (P.expected n) ≤
      P.writerConstant / (1 - alpha) * P.defect n := by
  intro n
  have hresp := influenceResponse_le
    (P.resolvent n) (P.directMismatch n) alpha (P.defect n)
    (P.resolvent_nonnegative n) (P.direct_nonnegative n)
    halpha0 halpha1 (P.resolvent_column n) (P.direct_mass n)
  calc
    dist (P.expected (n + 1)) (P.expected n) ≤
        P.writerConstant * influenceResponse (P.resolvent n)
          (P.directMismatch n) := P.interpolation n
    _ ≤ P.writerConstant * ((1 - alpha)⁻¹ * P.defect n) :=
      mul_le_mul_of_nonneg_left hresp P.writerConstant_nonnegative
    _ = P.writerConstant / (1 - alpha) * P.defect n := by
      rw [div_eq_mul_inv]
      ring

/-- U4: a vanishing local/collar defect makes every adjacent fixed writer
compatible in the limit. -/
theorem adjacent_distance_tendsto_zero [Fintype I]
    [PseudoMetricSpace E] (alpha : ℝ)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (P : AdjacentComparison (I := I) E alpha)
    (hdefect : Tendsto P.defect atTop (𝓝 0)) :
    Tendsto (fun n => dist (P.expected (n + 1)) (P.expected n))
      atTop (𝓝 0) := by
  let c : ℝ := P.writerConstant / (1 - alpha)
  have hupper : ∀ n, dist (P.expected (n + 1)) (P.expected n) ≤
      c * P.defect n := adjacent_projective_bound alpha halpha0 halpha1 P
  have hbound : Tendsto (fun n => c * P.defect n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hdefect)
  exact squeeze_zero (fun _ => dist_nonneg) hupper hbound

/-- U3: summable adjacent locality/collar defects give a unique full-tail
limit for the fixed writer. -/
theorem expected_tendsto_of_summable_defect [Fintype I]
    [PseudoMetricSpace E] [CompleteSpace E]
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (P : AdjacentComparison (I := I) E alpha)
    (hsum : Summable P.defect) :
    ∃ limit : E, Tendsto P.expected atTop (𝓝 limit) := by
  let c : ℝ := P.writerConstant / (1 - alpha)
  have hscaled : Summable (fun n => c * P.defect n) := by
    simpa using hsum.mul_left c
  have hstep : ∀ n, dist (P.expected n) (P.expected (n + 1)) ≤
      c * P.defect n := by
    intro n
    rw [dist_comm]
    exact adjacent_projective_bound alpha halpha0 halpha1 P n
  exact cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable (fun n => c * P.defect n) hstep hscaled)

/-- **`thm:SMFS-projective-continuum`, exact comparison form.**  The boxed
adjacent estimate, U4 vanishing-defect compatibility, and U3 summable-tail
continuum limit hold simultaneously for every static, transfer, Green,
connected, score, action, or determinant-line writer represented by an
`AdjacentComparison` packet. -/
theorem dobrushin_projective_continuum [Fintype I]
    [PseudoMetricSpace E] [CompleteSpace E]
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (P : AdjacentComparison (I := I) E alpha) :
    (∀ n, dist (P.expected (n + 1)) (P.expected n) ≤
      P.writerConstant / (1 - alpha) * P.defect n) ∧
    (Tendsto P.defect atTop (𝓝 0) →
      Tendsto (fun n => dist (P.expected (n + 1)) (P.expected n))
        atTop (𝓝 0)) ∧
    (Summable P.defect →
      ∃ limit : E, Tendsto P.expected atTop (𝓝 limit)) := by
  exact ⟨adjacent_projective_bound alpha halpha0 halpha1 P,
    adjacent_distance_tendsto_zero alpha halpha0 halpha1 P,
    expected_tendsto_of_summable_defect alpha halpha0 halpha1 P⟩

end NCG.DobrushinProjectiveContinuum
