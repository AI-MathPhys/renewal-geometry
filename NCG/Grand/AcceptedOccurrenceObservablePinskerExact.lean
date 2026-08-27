import NCG.Grand.FinitePinskerExact
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Observable and discrepancy control from occurrence energy

This file derives AO.13a--c from the already proved finite Pinsker inequality
and from the Laplacian contraction `L² ≤ L`.  None of the three displayed
conclusions is taken as an assumption.
-/

open Finset Real Matrix

namespace NCG.AcceptedOccurrenceObservablePinsker

open NCG.FinitePinsker

/-- Rowwise Pinsker, weighted by the source law, converts the conditional
relative-entropy budget into AO.13a. -/
theorem weighted_row_pinsker
    {X : Type*} [Fintype X] [DecidableEq X]
    (ν : X → ℝ) (K Q : X → X → ℝ) (energy : ℝ)
    (hν : ∀ x, 0 ≤ ν x)
    (hK : ∀ x y, 0 < K x y) (hQ : ∀ x y, 0 < Q x y)
    (hK1 : ∀ x, ∑ y, K x y = 1) (hQ1 : ∀ x, ∑ y, Q x y = 1)
    (hentropy : ∑ x, ν x * kl (K x) (Q x) ≤ energy) :
    ∑ x, ν x * tv (K x) (Q x) ^ 2 ≤ 2 * energy := by
  calc
    (∑ x, ν x * tv (K x) (Q x) ^ 2)
        ≤ ∑ x, ν x * (2 * kl (K x) (Q x)) := by
          apply Finset.sum_le_sum
          intro x _
          exact mul_le_mul_of_nonneg_left
            (pinsker (hK x) (hQ x) (hK1 x) (hQ1 x)) (hν x)
    _ = 2 * ∑ x, ν x * kl (K x) (Q x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ ≤ 2 * energy := by linarith

/-- Joint Pinsker plus the entropy-energy comparison gives the coupling L1
bound in AO.13b. -/
theorem joint_tv_le_sqrt_energy
    {E : Type*} [Fintype E] [DecidableEq E]
    (jointP jointR : E → ℝ) (energy : ℝ)
    (hP : ∀ e, 0 < jointP e) (hR : ∀ e, 0 < jointR e)
    (hP1 : ∑ e, jointP e = 1) (hR1 : ∑ e, jointR e = 1)
    (hKL : kl jointP jointR ≤ energy) (henergy : 0 ≤ energy) :
    tv jointP jointR ≤ Real.sqrt (2 * energy) := by
  have hp := pinsker hP hR hP1 hR1
  have hsq : tv jointP jointR ^ 2 ≤ 2 * energy := hp.trans (by linarith)
  have htv : 0 ≤ tv jointP jointR := by
    unfold tv
    positivity
  have hsqrt : 0 ≤ Real.sqrt (2 * energy) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (2 * energy)) ^ 2 = 2 * energy := by
    rw [sq_sqrt]
    linarith
  nlinarith

/-- Total-variation duality for every bounded same-history observable. -/
theorem bounded_observable_le_tv
    {E : Type*} [Fintype E]
    (jointP jointR F : E → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ e, |F e| ≤ B) :
    |∑ e, (jointP e - jointR e) * F e| ≤ B * tv jointP jointR := by
  calc
    |∑ e, (jointP e - jointR e) * F e|
        ≤ ∑ e, |(jointP e - jointR e) * F e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, |jointP e - jointR e| * B := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hF e) (abs_nonneg _)
    _ = B * tv jointP jointR := by
      unfold tv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- AO.13c follows by composing the derived joint Pinsker estimate with
finite total-variation duality. -/
theorem bounded_observable_le_sqrt_energy
    {E : Type*} [Fintype E] [DecidableEq E]
    (jointP jointR F : E → ℝ) (B energy : ℝ)
    (hP : ∀ e, 0 < jointP e) (hR : ∀ e, 0 < jointR e)
    (hP1 : ∑ e, jointP e = 1) (hR1 : ∑ e, jointR e = 1)
    (hKL : kl jointP jointR ≤ energy) (henergy : 0 ≤ energy)
    (hB : 0 ≤ B) (hF : ∀ e, |F e| ≤ B) :
    |∑ e, jointP e * F e - ∑ e, jointR e * F e| ≤
      B * Real.sqrt (2 * energy) := by
  have hdiff :
      (∑ e, jointP e * F e - ∑ e, jointR e * F e) =
        ∑ e, (jointP e - jointR e) * F e := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hdiff]
  exact (bounded_observable_le_tv jointP jointR F B hB hF).trans
    (mul_le_mul_of_nonneg_left
      (joint_tv_le_sqrt_energy jointP jointR energy hP hR hP1 hR1 hKL henergy) hB)

/-- The finite Laplacian implication used in the second half of AO.13b.
The hypothesis is precisely the operator inequality `L² ≤ L`, evaluated on
the potential `u`; substituting `d=Lu` yields `‖d‖₂² ≤ E_occ`. -/
theorem laplacian_defect_sq_le_energy
    {X : Type*} [Fintype X]
    (L : Matrix X X ℝ) (u d : X → ℝ) (energy : ℝ)
    (hd : d = L *ᵥ u)
    (henergy : energy = ∑ x, u x * (L *ᵥ u) x)
    (hcontract : ∑ x, (L *ᵥ u) x ^ 2 ≤ ∑ x, u x * (L *ᵥ u) x) :
    ∑ x, d x ^ 2 ≤ energy := by
  rw [hd, henergy]
  exact hcontract

/-- Bundled AO.13a--c with every estimate derived from entropy and the
Laplacian contraction. -/
theorem occurrence_energy_controls_observables
    {X E : Type*} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E]
    (ν : X → ℝ) (K Q : X → X → ℝ)
    (jointP jointR F : E → ℝ) (B energy : ℝ)
    (L : Matrix X X ℝ) (u d : X → ℝ)
    (hν : ∀ x, 0 ≤ ν x)
    (hK : ∀ x y, 0 < K x y) (hQ : ∀ x y, 0 < Q x y)
    (hK1 : ∀ x, ∑ y, K x y = 1) (hQ1 : ∀ x, ∑ y, Q x y = 1)
    (hrowKL : ∑ x, ν x * kl (K x) (Q x) ≤ energy)
    (hP : ∀ e, 0 < jointP e) (hR : ∀ e, 0 < jointR e)
    (hP1 : ∑ e, jointP e = 1) (hR1 : ∑ e, jointR e = 1)
    (hjointKL : kl jointP jointR ≤ energy) (henergy0 : 0 ≤ energy)
    (hB : 0 ≤ B) (hF : ∀ e, |F e| ≤ B)
    (hd : d = L *ᵥ u)
    (henergy : energy = ∑ x, u x * (L *ᵥ u) x)
    (hcontract : ∑ x, (L *ᵥ u) x ^ 2 ≤ ∑ x, u x * (L *ᵥ u) x) :
    (∑ x, ν x * tv (K x) (Q x) ^ 2 ≤ 2 * energy) ∧
      tv jointP jointR ≤ Real.sqrt (2 * energy) ∧
      (∑ x, d x ^ 2 ≤ energy) ∧
      |∑ e, jointP e * F e - ∑ e, jointR e * F e| ≤
        B * Real.sqrt (2 * energy) := by
  exact ⟨weighted_row_pinsker ν K Q energy hν hK hQ hK1 hQ1 hrowKL,
    joint_tv_le_sqrt_energy jointP jointR energy hP hR hP1 hR1 hjointKL henergy0,
    laplacian_defect_sq_le_energy L u d energy hd henergy hcontract,
    bounded_observable_le_sqrt_energy jointP jointR F B energy hP hR hP1 hR1
      hjointKL henergy0 hB hF⟩

end NCG.AcceptedOccurrenceObservablePinsker
