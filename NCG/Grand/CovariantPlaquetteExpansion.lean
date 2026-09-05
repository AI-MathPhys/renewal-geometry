/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GroupCommutatorBound

/-!
# Quantitative covariant plaquette expansion

This file proves the non-Abelian plaquette clause of
`thm:periodic-covariant-information-limit`.  For contractive exponential
curves, the four-link holonomy differs from
`1 + h²[A,B]` by an explicit cubic group-commutator error plus the quadratic
tail of `exp (h²[A,B])`.
-/

open NormedSpace Set Asymptotics

namespace NCG
namespace CovariantPlaquette

variable {𝔄 : Type} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]
  [CompleteSpace 𝔄] [NormedAlgebra ℚ 𝔄] [NormOneClass 𝔄]

/-- The constant-coefficient plaquette built from the two link generators. -/
noncomputable def plaquette (h : ℝ) (A B : 𝔄) : 𝔄 :=
  exp ((-h) • A) * exp ((-h) • B) * exp (h • A) * exp (h • B)

/-- Quantitative second-order plaquette expansion.  The first summand is the
cubic group-commutator error; the second is the exact exponential Taylor tail
at `h²[A,B]`. -/
theorem norm_plaquette_sub_secondOrder_le
    (A B : 𝔄) (h M : ℝ) (hh : 0 ≤ h) (hM : 0 ≤ M)
    (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M)
    (hcA : ∀ u : ℝ, ‖exp (u • A)‖ ≤ 1)
    (hcB : ∀ u : ℝ, ‖exp (u • B)‖ ≤ 1)
    (hcComm : ∀ u : ℝ, ‖exp (u • (A * B - B * A))‖ ≤ 1) :
    ‖plaquette h A B - (1 + h ^ 2 • (A * B - B * A))‖ ≤
      28 * (h * M) ^ 3 +
        ‖h ^ 2 • (A * B - B * A)‖ ^ 2 *
          Real.exp ‖h ^ 2 • (A * B - B * A)‖ := by
  let X : 𝔄 := (-h) • A
  let Y : 𝔄 := (-h) • B
  let C : 𝔄 := A * B - B * A
  have hβ : 0 ≤ h * M := mul_nonneg hh hM
  have hX : ‖X‖ ≤ h * M := by
    dsimp [X]
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hA hh
  have hY : ‖Y‖ ≤ h * M := by
    dsimp [Y]
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hB hh
  have hXY : X * Y - Y * X = h ^ 2 • C := by
    simp only [X, Y, C, smul_mul_smul]
    rw [show -h * -h = h ^ 2 by ring, smul_sub]
  have hcX : ∀ u : ℝ, ‖exp (u • X)‖ ≤ 1 := by
    intro u
    have huv : u • X = (-u * h) • A := by
      simp only [X, smul_smul]
      congr 1
      ring
    rw [huv]
    exact hcA (-u * h)
  have hcY : ∀ u : ℝ, ‖exp (u • Y)‖ ≤ 1 := by
    intro u
    have huv : u • Y = (-u * h) • B := by
      simp only [Y, smul_smul]
      congr 1
      ring
    rw [huv]
    exact hcB (-u * h)
  have hcXY : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖exp (u • (X * Y - Y * X))‖ ≤ 1 := by
    intro u _
    rw [hXY, smul_smul]
    exact hcComm (u * h ^ 2)
  have hGroup := SharpTrotter.group_comm_exp_bound (A := 𝔄)
    X Y (h * M) hβ hX hY hcX hcY hcXY
  have hTail := ChannelEstimates.exp_sub_linear_bound (h ^ 2 • C)
  have hTriangle :
      ‖exp X * exp Y * exp (-X) * exp (-Y) - (1 + h ^ 2 • C)‖ ≤
        ‖exp X * exp Y * exp (-X) * exp (-Y) - exp (h ^ 2 • C)‖ +
          ‖exp (h ^ 2 • C) - 1 - h ^ 2 • C‖ := by
    have hsplit :
        exp X * exp Y * exp (-X) * exp (-Y) - (1 + h ^ 2 • C) =
          (exp X * exp Y * exp (-X) * exp (-Y) - exp (h ^ 2 • C)) +
            (exp (h ^ 2 • C) - 1 - h ^ 2 • C) := by
      abel
    rw [hsplit]
    exact norm_add_le _ _
  calc
    ‖plaquette h A B - (1 + h ^ 2 • (A * B - B * A))‖ =
        ‖exp X * exp Y * exp (-X) * exp (-Y) - (1 + h ^ 2 • C)‖ := by
      simp only [plaquette, X, Y, C, neg_smul, neg_neg]
    _ ≤ ‖exp X * exp Y * exp (-X) * exp (-Y) - exp (h ^ 2 • C)‖ +
          ‖exp (h ^ 2 • C) - 1 - h ^ 2 • C‖ := hTriangle
    _ ≤ 28 * (h * M) ^ 3 +
          ‖h ^ 2 • C‖ ^ 2 * Real.exp ‖h ^ 2 • C‖ := by
      rw [hXY] at hGroup
      exact add_le_add hGroup hTail
/-- A pure cubic bound on the regulator range `0 ≤ h ≤ 1`.  In particular,
the plaquette is `1 + h²[A,B] + O(h³)` with an explicit constant depending
only on a common generator norm bound. -/
theorem norm_plaquette_sub_secondOrder_le_cubic
    (A B : 𝔄) (h M : ℝ) (hh : 0 ≤ h) (hhOne : h ≤ 1) (hM : 0 ≤ M)
    (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M)
    (hcA : ∀ u : ℝ, ‖exp (u • A)‖ ≤ 1)
    (hcB : ∀ u : ℝ, ‖exp (u • B)‖ ≤ 1)
    (hcComm : ∀ u : ℝ, ‖exp (u • (A * B - B * A))‖ ≤ 1) :
    ‖plaquette h A B - (1 + h ^ 2 • (A * B - B * A))‖ ≤
      (28 * M ^ 3 + 4 * M ^ 4 * Real.exp (2 * M ^ 2)) * h ^ 3 := by
  have hMain := norm_plaquette_sub_secondOrder_le
    A B h M hh hM hA hB hcA hcB hcComm
  have hComm : ‖A * B - B * A‖ ≤ 2 * M ^ 2 := by
    calc
      ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le _ _
      _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ M * M + M * M := by
        exact add_le_add
          (mul_le_mul hA hB (norm_nonneg B) hM)
          (mul_le_mul hB hA (norm_nonneg A) hM)
      _ = 2 * M ^ 2 := by ring
  have hZ : ‖h ^ 2 • (A * B - B * A)‖ ≤ 2 * h ^ 2 * M ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
    calc
      h ^ 2 * ‖A * B - B * A‖ ≤ h ^ 2 * (2 * M ^ 2) :=
        mul_le_mul_of_nonneg_left hComm (sq_nonneg h)
      _ = 2 * h ^ 2 * M ^ 2 := by ring
  have hZCoarse : ‖h ^ 2 • (A * B - B * A)‖ ≤ 2 * M ^ 2 := by
    calc
      ‖h ^ 2 • (A * B - B * A)‖ ≤ 2 * h ^ 2 * M ^ 2 := hZ
      _ ≤ 2 * M ^ 2 := by
        have hhSq : h ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg M]
  have hExp : Real.exp ‖h ^ 2 • (A * B - B * A)‖ ≤
      Real.exp (2 * M ^ 2) := Real.exp_le_exp.mpr hZCoarse
  have hZSq : ‖h ^ 2 • (A * B - B * A)‖ ^ 2 ≤
      (2 * h ^ 2 * M ^ 2) ^ 2 := by
    nlinarith [norm_nonneg (h ^ 2 • (A * B - B * A)),
      mul_nonneg (mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) (sq_nonneg h)) (sq_nonneg M)]
  have hTail :
      ‖h ^ 2 • (A * B - B * A)‖ ^ 2 *
          Real.exp ‖h ^ 2 • (A * B - B * A)‖ ≤
        4 * h ^ 4 * M ^ 4 * Real.exp (2 * M ^ 2) := by
    calc
      ‖h ^ 2 • (A * B - B * A)‖ ^ 2 *
          Real.exp ‖h ^ 2 • (A * B - B * A)‖ ≤
        (2 * h ^ 2 * M ^ 2) ^ 2 * Real.exp (2 * M ^ 2) :=
          mul_le_mul hZSq hExp (Real.exp_pos _).le (sq_nonneg _)
      _ = 4 * h ^ 4 * M ^ 4 * Real.exp (2 * M ^ 2) := by ring
  have hhPow : h ^ 4 ≤ h ^ 3 := by
    nlinarith [sq_nonneg (h ^ 2), mul_nonneg (sq_nonneg h) hh]
  calc
    ‖plaquette h A B - (1 + h ^ 2 • (A * B - B * A))‖ ≤
        28 * (h * M) ^ 3 +
          ‖h ^ 2 • (A * B - B * A)‖ ^ 2 *
            Real.exp ‖h ^ 2 • (A * B - B * A)‖ := hMain
    _ ≤ 28 * (h * M) ^ 3 +
        4 * h ^ 4 * M ^ 4 * Real.exp (2 * M ^ 2) :=
      add_le_add_right hTail _
    _ ≤ (28 * M ^ 3 + 4 * M ^ 4 * Real.exp (2 * M ^ 2)) * h ^ 3 := by
      have hcoef : 0 ≤ 4 * M ^ 4 * Real.exp (2 * M ^ 2) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hhPow hcoef]

/-- One-sided asymptotic form of the quantitative plaquette estimate. -/
theorem plaquette_sub_secondOrder_isBigO_right
    (A B : 𝔄) (M : ℝ) (hM : 0 ≤ M)
    (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M)
    (hcA : ∀ u : ℝ, ‖exp (u • A)‖ ≤ 1)
    (hcB : ∀ u : ℝ, ‖exp (u • B)‖ ≤ 1)
    (hcComm : ∀ u : ℝ, ‖exp (u • (A * B - B * A))‖ ≤ 1) :
    (fun h : ℝ => plaquette h A B -
      (1 + h ^ 2 • (A * B - B * A)))
      =O[nhdsWithin 0 (Set.Ici 0)] fun h : ℝ => h ^ 3 := by
  let C : ℝ := 28 * M ^ 3 + 4 * M ^ 4 * Real.exp (2 * M ^ 2)
  refine IsBigO.of_bound C ?_
  have hhOne : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ici 0), h ≤ 1 :=
    (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hhOne] with h hh hh1
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hh 3)]
  exact norm_plaquette_sub_secondOrder_le_cubic
    A B h M hh hh1 hM hA hB hcA hcB hcComm


end CovariantPlaquette
end NCG
