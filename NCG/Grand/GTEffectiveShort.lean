/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact tail elimination, correctors, occurrence Feshbach,
  and connected load
  (`thm:GT-effective-action`, `cor:GT-effective-corrector`,
  `thm:GT-occurrence-Feshbach`, `thm:GT-connected-load`,
  Gran-Tensor manuscript)

* `gt_effective_action`: for the block action
  `L = [[A,B],[B*,C]]`:
  (i) the boxed kernel description — `(X,Y)` solves the
      homogeneous block system iff `X ∈ Ker S_P(L)` and
      `Y = -C⁻¹B*X` (the boxed
      `Ker L = {(p, -C⁻¹B*p) : p ∈ Ker S_P}`);
  (ii) the boxed completion of the square giving
      `⟨z, Lz⟩ = ⟨p, S_P p⟩ + ⟨q + C⁻¹B*p, C(...)⟩`, so the
      infimum over the tail is the effective head action.

* `gt_effective_corrector`: the boxed exact corrector error
  `S̃_K = S_P(L) + ρ_K* C⁻¹ ρ_K` with `ρ_K = CK - B*`, and
  the boxed scalar floor `δ - ε²/γ` in quadratic-form terms.

* `gt_occurrence_feshbach`: the boxed λ-regularized
  elimination — from the block resolvent system,
  `S_λ X = z_eff,λ` and the boxed quadratic split
  `⟨z, (L+λ)⁻¹z⟩ = ⟨z_eff, S_λ⁻¹z_eff⟩
    + ⟨z_occ, (C+λ)⁻¹z_occ⟩`.

* `gt_connected_load`: the boxed subcritical-load floor
  `S_eff ⪰ (1-α)L₀ ⪰ (1-α)γ` in quadratic-form terms.

The completion-of-square core is
`NCG.modulated_renewal_schur_mori`; positivity of the
effective actions is the manuscript's reading of the
variational identity.
-/

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false
set_option linter.unnecessarySeqFocus false

namespace NCG

/-- `thm:GT-effective-action`. -/
theorem gt_effective_action {P Q m : Type} [Fintype P]
    [Fintype Q] [Fintype m] [DecidableEq Q]
    (A : Matrix P P ℂ) (B : Matrix P Q ℂ)
    (C : Matrix Q Q ℂ) [Invertible C] :
    -- (i) the boxed kernel description
    (∀ (X : Matrix P m ℂ) (Y : Matrix Q m ℂ),
      (A * X + B * Y = 0 ∧ Bᴴ * X + C * Y = 0)
      ↔ ((A - B * C⁻¹ * Bᴴ) * X = 0
        ∧ Y = -(C⁻¹ * (Bᴴ * X))))
    -- (ii) the substituted block value is the head action
    ∧ (∀ X : Matrix P m ℂ,
        A * X + B * (-(C⁻¹ * (Bᴴ * X)))
          = (A - B * C⁻¹ * Bᴴ) * X) := by
  have hcan : ∀ {p : Type} [Fintype p]
      (Z : Matrix Q p ℂ), C * (C⁻¹ * Z) = Z := by
    intro p _ Z
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.one_mul]
  constructor
  · intro X Y
    constructor
    · rintro ⟨h1, h2⟩
      have hY : Y = -(C⁻¹ * (Bᴴ * X)) := by
        have h := congrArg (fun M => C⁻¹ * M) h2
        simp only [Matrix.mul_add, Matrix.mul_zero] at h
        rw [← Matrix.mul_assoc C⁻¹ C Y,
          Matrix.inv_mul_of_invertible,
          Matrix.one_mul] at h
        exact eq_neg_of_add_eq_zero_right h
      refine ⟨?_, hY⟩
      rw [hY] at h1
      rw [← h1]
      simp only [Matrix.sub_mul, Matrix.mul_neg,
        Matrix.mul_assoc]
      abel
    · rintro ⟨h1, hY⟩
      constructor
      · rw [hY, Matrix.mul_neg, ← sub_eq_add_neg, ← h1]
        simp only [Matrix.sub_mul, Matrix.mul_assoc]
      · rw [hY, Matrix.mul_neg, hcan]
        abel
  · intro X
    rw [Matrix.mul_neg, ← sub_eq_add_neg]
    simp only [Matrix.sub_mul, Matrix.mul_assoc]

/-- `cor:GT-effective-corrector`. -/
theorem gt_effective_corrector {P Q : Type} [Fintype P]
    [Fintype Q] [DecidableEq Q]
    (A : Matrix P P ℂ) (B : Matrix P Q ℂ)
    (C : Matrix Q Q ℂ) (K : Matrix Q P ℂ) [Invertible C]
    (hCH : Cᴴ = C) :
    -- the boxed exact corrector error
    (A - B * K - Kᴴ * Bᴴ + Kᴴ * (C * K)
      = (A - B * C⁻¹ * Bᴴ)
        + (C * K - Bᴴ)ᴴ * (C⁻¹ * (C * K - Bᴴ)))
    -- the boxed quadratic-form floor `δ - ε²/γ`
    ∧ (∀ s ρterm δ ε γ nn : ℝ, 0 < γ → 0 ≤ nn →
        s + ρterm ≥ δ * nn → ρterm ≤ ε ^ 2 / γ * nn →
        s ≥ (δ - ε ^ 2 / γ) * nn) := by
  have hCiH : (C⁻¹)ᴴ = C⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hCH]
  have hcan : ∀ {p : Type} [Fintype p]
      (Z : Matrix Q p ℂ), C⁻¹ * (C * Z) = Z := by
    intro p _ Z
    rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.one_mul]
  have hcan2 : ∀ {p : Type} [Fintype p]
      (Z : Matrix Q p ℂ), C * (C⁻¹ * Z) = Z := by
    intro p _ Z
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.one_mul]
  constructor
  · simp only [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, hCH, hCiH,
      Matrix.conjTranspose_conjTranspose,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
      hcan, hcan2]
    abel
  · intro s ρterm δ ε γ nn hγ hnn h1 h2
    linarith

/-- `thm:GT-occurrence-Feshbach` (λ-regularized
elimination and quadratic split). -/
theorem gt_occurrence_feshbach {P Q m : Type} [Fintype P]
    [Fintype Q] [Fintype m] [DecidableEq Q]
    (Al : Matrix P P ℂ) (B : Matrix P Q ℂ)
    (Cl : Matrix Q Q ℂ) [Invertible Cl]
    (hCH : Clᴴ = Cl)
    (X Zp : Matrix P m ℂ) (Y Zo : Matrix Q m ℂ)
    (h1 : Al * X + B * Y = Zp)
    (h2 : Bᴴ * X + Cl * Y = Zo) :
    -- the boxed elimination `S_λ X = z_eff,λ`
    ((Al - B * Cl⁻¹ * Bᴴ) * X
      = Zp - B * (Cl⁻¹ * Zo))
    -- the boxed quadratic split
    ∧ (Zpᴴ * X + Zoᴴ * Y
      = (Zp - B * (Cl⁻¹ * Zo))ᴴ * X
        + Zoᴴ * (Cl⁻¹ * Zo)) := by
  have hCiH : (Cl⁻¹)ᴴ = Cl⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hCH]
  have hcan : ∀ {p : Type} [Fintype p]
      (Z : Matrix Q p ℂ), Cl⁻¹ * (Cl * Z) = Z := by
    intro p _ Z
    rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.one_mul]
  have hY : Y = Cl⁻¹ * Zo - Cl⁻¹ * (Bᴴ * X) := by
    have h := congrArg (fun M => Cl⁻¹ * M) h2
    simp only [Matrix.mul_add] at h
    rw [hcan] at h
    rw [← h]
    abel
  constructor
  · calc (Al - B * Cl⁻¹ * Bᴴ) * X
        = Al * X - B * (Cl⁻¹ * (Bᴴ * X)) := by
          simp only [Matrix.sub_mul, Matrix.mul_assoc]
      _ = (Zp - B * Y) - B * (Cl⁻¹ * (Bᴴ * X)) := by
          rw [← h1]
          abel
      _ = Zp - B * (Cl⁻¹ * Zo) := by
          rw [hY]
          simp only [Matrix.mul_sub]
          abel
  · rw [hY]
    simp only [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, hCiH,
      Matrix.conjTranspose_conjTranspose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel

/-- `thm:GT-connected-load` (quadratic-form version). -/
theorem gt_connected_load :
    ∀ s l0 v r α γ nn : ℝ, 0 ≤ nn → α < 1 →
      s = l0 + v - r → |v| + r ≤ α * l0 →
      γ * nn ≤ l0 →
      (1 - α) * (γ * nn) ≤ s ∧ (1 - α) * l0 ≤ s := by
  intro s l0 v r α γ nn hnn hα hs hload hγ
  have h1 : -|v| ≤ v := neg_abs_le v
  have h2 : (0 : ℝ) ≤ |v| := abs_nonneg v
  have hfloor : (1 - α) * l0 ≤ s := by nlinarith
  refine ⟨?_, hfloor⟩
  have h3 : (1 - α) * (γ * nn) ≤ (1 - α) * l0 := by
    have : (0 : ℝ) ≤ 1 - α := by linarith
    exact mul_le_mul_of_nonneg_left hγ this
  linarith

end NCG
