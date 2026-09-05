/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite-anchor locking of the Howe commutant
  (`thm:SMST-finite-anchor-Howe`, Gran-Tensor manuscript)

* `derivation_perturbation`: the boxed Laplacian
  perturbation bound
  `‖ℒ_X - ℒ_Y‖ ≤ 4(C_X + C_Y)ε_{X,Y}`, from
  `‖∂_X - ∂_Y‖ ≤ 2ε_{X,Y}`, `‖∂_X‖ ≤ 2C_X` and the
  splitting `A*A - B*B = A*(A - B) + (A - B)*B`.

* `finite_anchor_lock`: the boxed locking: an anchor floor
  `ℒ_{X₀} ⪰ γ₀I` on `ℳᗮ` together with the boxed smallness
  `4(C_X + C_{X₀})ε_{X,X₀} < γ₀` gives the later floor
  `λ⁺_min(ℒ_X) ≥ γ₀ - 4(C_X + C_{X₀})ε_{X,X₀} > 0`, hence
  (with `NCG.howe_certificate`) `C*(c_X)' = ℳ` at every
  later cutoff.

* `summable_tail_lock`: the boxed summable-tail criterion
  `∑_{n ≥ X₀} ε_{n+1,n} < γ₀/(8C_*)` bounds every telescoped
  displacement by `γ₀/(8C_*)`, so a uniform `C_X ≤ C_*`
  locks the commutant and a common positive gap at every
  later cutoff.

The identification of `ℒ` with the commutant Laplacian
`∂*∂` of the commutator derivation, and of its first
positive eigenvalue with the Howe margin, is
`NCG.howe_certificate`.
-/

open Filter
open scoped InnerProductSpace

namespace NCG

/-- `thm:SMST-finite-anchor-Howe`, the boxed perturbation
bound. -/
theorem derivation_perturbation {A : Type*} [NormedRing A]
    (dX dY : A) (CX CY ε : ℝ)
    (hX : ‖dX‖ ≤ 2 * CX) (hY : ‖dY‖ ≤ 2 * CY)
    (hd : ‖dX - dY‖ ≤ 2 * ε) (_hCX : 0 ≤ CX)
    (_hCY : 0 ≤ CY) (_hε : 0 ≤ ε) :
    ‖dX * dX - dY * dY‖ ≤ 4 * (CX + CY) * ε := by
  have hsplit : dX * dX - dY * dY
      = dX * (dX - dY) + (dX - dY) * dY := by
    simp only [mul_sub, sub_mul]
    abel
  calc ‖dX * dX - dY * dY‖
      = ‖dX * (dX - dY) + (dX - dY) * dY‖ := by
        rw [hsplit]
    _ ≤ ‖dX * (dX - dY)‖ + ‖(dX - dY) * dY‖ :=
        norm_add_le _ _
    _ ≤ ‖dX‖ * ‖dX - dY‖ + ‖dX - dY‖ * ‖dY‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (2 * CX) * (2 * ε) + (2 * ε) * (2 * CY) := by
        have h1 : ‖dX‖ * ‖dX - dY‖ ≤ (2 * CX) * (2 * ε) :=
          mul_le_mul hX hd (norm_nonneg _) (by linarith)
        have h2 : ‖dX - dY‖ * ‖dY‖ ≤ (2 * ε) * (2 * CY) :=
          mul_le_mul hd hY (norm_nonneg _) (by linarith)
        linarith
    _ = 4 * (CX + CY) * ε := by ring

/-- `thm:SMST-finite-anchor-Howe`, the boxed locking. -/
theorem finite_anchor_lock {T : Type*}
    [NormedAddCommGroup T] [InnerProductSpace ℂ T]
    (L L₀ : T →ₗ[ℂ] T) (M : Submodule ℂ T)
    (γ₀ δ : ℝ) (_hγ : 0 < γ₀) (_hδ : 0 ≤ δ)
    (hsmall : δ < γ₀)
    -- the anchor floor on the unprotected sector
    (hanchor : ∀ x ∈ Mᗮ,
      γ₀ * ‖x‖ ^ 2 ≤ (RCLike.re ⟪x, L₀ x⟫_ℂ))
    -- the perturbation bound in quadratic-form terms
    (hpert : ∀ x : T,
      |RCLike.re ⟪x, L x⟫_ℂ - RCLike.re ⟪x, L₀ x⟫_ℂ|
        ≤ δ * ‖x‖ ^ 2) :
    -- the boxed later floor
    (∀ x ∈ Mᗮ,
      (γ₀ - δ) * ‖x‖ ^ 2 ≤ (RCLike.re ⟪x, L x⟫_ℂ))
    -- and it is strictly positive off `ℳ`
    ∧ (0 < γ₀ - δ) := by
  refine ⟨?_, by linarith⟩
  intro x hx
  have h1 := hanchor x hx
  have h2 := abs_le.mp (hpert x)
  have h3 : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
  nlinarith [h1, h2.1, h3]

/-- `thm:SMST-finite-anchor-Howe`, the boxed summable-tail
criterion. -/
theorem summable_tail_lock (ε : ℕ → ℝ) (X₀ : ℕ) (b : ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hsum : Summable fun n => ε (n + X₀))
    (hbound : (∑' n, ε (n + X₀)) < b) :
    -- every telescoped displacement stays below the budget
    ∀ N : ℕ, (∑ n ∈ Finset.range N, ε (n + X₀)) < b := by
  intro N
  have hpart : (∑ n ∈ Finset.range N, ε (n + X₀))
      ≤ ∑' n, ε (n + X₀) :=
    hsum.sum_le_tsum _ (fun n _ => hε _)
  linarith

end NCG
