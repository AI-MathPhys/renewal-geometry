/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Protected-observable Riesz theorem
  (`thm:GT-protected-Riesz`, Gran-Tensor manuscript)

* `gt_protected_riesz`: for a positive self-adjoint action
  `L` and a range source `e = Lu` (the hypothesis
  `Ran E ⊆ Ran L` per column),
  (i) the boxed Riesz bound
      `|⟨e, v⟩|² ≤ ⟨u, Lu⟩ ⟨v, Lv⟩` — the Gram constant
      `⟨u, Lu⟩ = ⟨e, L†e⟩` is the boxed Riesz observable
      `𝓡_E(L)`, and the bound is the Cauchy–Schwarz
      inequality of the `L`-semi-inner product;
  (ii) the boxed optimality witness — if the Riesz value
      `λ = ⟨u, Lu⟩` is positive, then `z = λ⁻¹u` is a unit
      protected output (`⟨e, z⟩ = 1`) whose action is
      exactly `⟨z, Lz⟩ = λ⁻¹`: an unbounded influence
      sequence is the same thing as unit protected outputs
      of vanishing action.

* `gt_protected_riesz_eigen`: the matrix eigenvector form —
  if `c` is an eigenvector of `𝓡_E(L) = EᴴL⁻¹E` with
  eigenvalue `λ ≠ 0`, then `z = λ⁻¹L⁻¹Ec` satisfies the
  boxed pair `Eᴴz = c` and `zᴴLz = λ⁻¹(cᴴc)`.

The pseudoinverse formulation on `Ker L`-complements is the
manuscript's regularized reading; here the range hypothesis
is rendered by an explicit preimage (clause set 1) and by
invertibility (clause set 2).
-/

open scoped InnerProductSpace
open Matrix

namespace NCG

/-- `thm:GT-protected-Riesz` (Riesz bound + optimality
witness). -/
theorem gt_protected_riesz {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : V →ₗ[ℝ] V)
    (hsa : ∀ x y : V, ⟪L x, y⟫_ℝ = ⟪x, L y⟫_ℝ)
    (hpsd : ∀ x : V, 0 ≤ ⟪x, L x⟫_ℝ) :
    -- (i) the boxed Riesz bound with the boxed Gram
    -- constant, for a range source e = Lu
    (∀ u v : V,
      ⟪L u, v⟫_ℝ ^ 2 ≤ ⟪u, L u⟫_ℝ * ⟪v, L v⟫_ℝ)
    -- (ii) the boxed optimality witness
    ∧ (∀ u : V, 0 < ⟪u, L u⟫_ℝ →
        ⟪L u, (⟪u, L u⟫_ℝ)⁻¹ • u⟫_ℝ = 1
        ∧ ⟪(⟪u, L u⟫_ℝ)⁻¹ • u,
            L ((⟪u, L u⟫_ℝ)⁻¹ • u)⟫_ℝ
          = (⟪u, L u⟫_ℝ)⁻¹) := by
  have hexp : ∀ u v : V, ∀ t : ℝ,
      ⟪u + t • v, L (u + t • v)⟫_ℝ
        = ⟪u, L u⟫_ℝ + 2 * t * ⟪L u, v⟫_ℝ
          + t ^ 2 * ⟪v, L v⟫_ℝ := by
    intro u v t
    have h1 : ⟪u, L v⟫_ℝ = ⟪L u, v⟫_ℝ := (hsa u v).symm
    have h2 : ⟪v, L u⟫_ℝ = ⟪L u, v⟫_ℝ :=
      (real_inner_comm v (L u)).symm
    simp only [map_add, map_smul, inner_add_left,
      inner_add_right, real_inner_smul_left,
      real_inner_smul_right, h1, h2]
    ring
  constructor
  · intro u v
    rcases eq_or_lt_of_le (hpsd v) with hc | hc
    · -- degenerate direction: ⟪v, Lv⟫ = 0 forces the
      -- cross term to vanish
      have hb : ⟪L u, v⟫_ℝ = 0 := by
        by_contra hb
        have h := hpsd
          (u + (-(⟪u, L u⟫_ℝ + 1)
            / (2 * ⟪L u, v⟫_ℝ)) • v)
        rw [hexp, ← hc] at h
        have hsimp : 2 * (-(⟪u, L u⟫_ℝ + 1)
            / (2 * ⟪L u, v⟫_ℝ)) * ⟪L u, v⟫_ℝ
            = -(⟪u, L u⟫_ℝ + 1) := by
          field_simp
        rw [hsimp] at h
        simp only [mul_zero] at h
        linarith
      rw [hb, ← hc]
      norm_num
    · have h := hpsd
        (u + (-(⟪L u, v⟫_ℝ / ⟪v, L v⟫_ℝ)) • v)
      rw [hexp] at h
      have hcne : ⟪v, L v⟫_ℝ ≠ 0 := ne_of_gt hc
      field_simp at h
      nlinarith [h, hc, sq_nonneg ⟪L u, v⟫_ℝ]
  · intro u hlam
    have hne : ⟪u, L u⟫_ℝ ≠ 0 := ne_of_gt hlam
    have hcomm : ⟪L u, u⟫_ℝ = ⟪u, L u⟫_ℝ :=
      (real_inner_comm (L u) u).symm
    constructor
    · rw [real_inner_smul_right, hcomm]
      field_simp
    · rw [map_smul, real_inner_smul_left,
        real_inner_smul_right]
      field_simp

/-- `thm:GT-protected-Riesz` (matrix eigenvector
witness). -/
theorem gt_protected_riesz_eigen {n k : Type} [Fintype n]
    [Fintype k] [DecidableEq n]
    (L : Matrix n n ℂ) [Invertible L] (hL : Lᴴ = L)
    (E : Matrix n k ℂ) (c : Matrix k Unit ℂ) (lam : ℝ)
    (hlam : lam ≠ 0)
    (heig : Eᴴ * L⁻¹ * E * c = (lam : ℂ) • c) :
    -- the boxed pair: unit protected output, action λ⁻¹
    Eᴴ * ((lam : ℂ)⁻¹ • (L⁻¹ * (E * c))) = c
    ∧ ((lam : ℂ)⁻¹ • (L⁻¹ * (E * c)))ᴴ
        * (L * ((lam : ℂ)⁻¹ • (L⁻¹ * (E * c))))
      = (lam : ℂ)⁻¹ • (cᴴ * c) := by
  have hlamC : (lam : ℂ) ≠ 0 := by
    exact_mod_cast hlam
  have hchain : Eᴴ * (L⁻¹ * (E * c)) = (lam : ℂ) • c := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact heig
  constructor
  · rw [Matrix.mul_smul, hchain, smul_smul,
      inv_mul_cancel₀ hlamC, one_smul]
  · have hLinvH : L⁻¹ᴴ = L⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, hL]
    have hstar : star ((lam : ℂ)⁻¹) = (lam : ℂ)⁻¹ := by
      rw [star_inv₀, Complex.star_def,
        Complex.conj_ofReal]
    have hfold : (L⁻¹ * (E * c))ᴴ * (E * c)
        = (lam : ℂ) • (cᴴ * c) := by
      calc (L⁻¹ * (E * c))ᴴ * (E * c)
          = ((E * c)ᴴ * L⁻¹ᴴ) * (E * c) := by
            rw [Matrix.conjTranspose_mul]
        _ = cᴴ * (Eᴴ * (L⁻¹ * (E * c))) := by
            rw [hLinvH, Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
        _ = cᴴ * ((lam : ℂ) • c) := by rw [hchain]
        _ = (lam : ℂ) • (cᴴ * c) := by
            rw [Matrix.mul_smul]
    calc ((lam : ℂ)⁻¹ • (L⁻¹ * (E * c)))ᴴ
          * (L * ((lam : ℂ)⁻¹ • (L⁻¹ * (E * c))))
        = ((lam : ℂ)⁻¹ • (L⁻¹ * (E * c))ᴴ)
          * ((lam : ℂ)⁻¹ • (E * c)) := by
          rw [Matrix.conjTranspose_smul, hstar,
            Matrix.mul_smul,
            Matrix.mul_inv_cancel_left_of_invertible]
      _ = ((lam : ℂ)⁻¹ * (lam : ℂ)⁻¹)
          • ((L⁻¹ * (E * c))ᴴ * (E * c)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul,
            smul_smul]
      _ = ((lam : ℂ)⁻¹ * (lam : ℂ)⁻¹)
          • ((lam : ℂ) • (cᴴ * c)) := by rw [hfold]
      _ = (lam : ℂ)⁻¹ • (cᴴ * c) := by
          rw [smul_smul]
          congr 1
          field_simp

end NCG
