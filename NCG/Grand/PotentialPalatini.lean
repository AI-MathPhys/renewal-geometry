/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Potential/counterterm exactness and the Palatini inversion
  (`thm:potential-counterterm-exactness` and
  `thm:Palatini-torsion`, Gran-Tensor manuscript)

* `potential_counterterm_exactness`:
  (i) the boxed potential writer `V = -log r` turns the
      primitive field-move force into an exact coboundary
      `f = d₀V`;
  (ii) all field-space curls (two-step defects) vanish;
  (iii) the boxed irreducible residual after optimal allowed
      cancellation `R*(I - P_C)R = R*R - R*C(C*C)⁻¹C*R`,
      with `P_C` an idempotent hermitian projector.

* `palatini_torsion_core`:
  (i) the boxed inversion
      `P_{α,β}⁻¹ = (βI - α⋆)/(α² + β²)` from `⋆² = -I`
      (two-sided);
  (ii) the boxed finite-cutoff torsion bound
      `‖T‖ ≤ κ⁻¹‖w‖` from a singular-value floor.

The variational derivation of the connection Euler equation,
the injectivity of the Cartan map `𝒦_e` (coframe-basis
index chase), and the `d₁c = 0` period criterion on the
variation complex are the manuscript's geometric layer
(the latter is the cochain-exactness theorem
`thm:common-action-exactness`).
-/

open Matrix

namespace NCG

/-- `thm:potential-counterterm-exactness`. -/
theorem potential_counterterm_exactness {Φ : Type*} :
    -- (i) the boxed coboundary form of the force
    (∀ r : Φ → ℝ, (∀ φ, 0 < r φ) →
      ∀ φ φ' : Φ, -Real.log (r φ' / r φ)
        = -Real.log (r φ') - -Real.log (r φ))
    -- (ii) curls vanish
    ∧ (∀ (V : Φ → ℝ) (φ φ' φ'' : Φ),
        (V φ' - V φ) + (V φ'' - V φ') = V φ'' - V φ)
    -- (iii) the boxed cancellation residual
    ∧ (∀ {e f h : Type} [Fintype e] [Fintype f] [Fintype h]
        [DecidableEq h]
        (R : Matrix h e ℂ) (C : Matrix h f ℂ)
        (W : Matrix f f ℂ),
        Rᴴ * ((1 : Matrix h h ℂ) - C * W * Cᴴ) * R
          = Rᴴ * R - Rᴴ * C * W * Cᴴ * R)
    -- optimality: `P_C` is an idempotent projector
    ∧ (∀ {f h : Type} [Fintype f] [Fintype h]
        [DecidableEq f]
        (C : Matrix h f ℂ) (W : Matrix f f ℂ),
        Cᴴ * C * W = 1 → W * (Cᴴ * C) = 1 →
        (C * W * Cᴴ) * (C * W * Cᴴ) = C * W * Cᴴ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr φ φ'
    rw [Real.log_div (ne_of_gt (hr φ'))
      (ne_of_gt (hr φ))]
    ring
  · intro V φ φ' φ''
    ring
  · intro e f h _ _ _ _ R C W
    simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.mul_assoc]
  · intro f h _ _ _ C W hCW hWC
    calc (C * W * Cᴴ) * (C * W * Cᴴ)
        = C * (W * (Cᴴ * C)) * (W * Cᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = C * W * Cᴴ := by
          rw [hWC, Matrix.mul_one]
          simp only [Matrix.mul_assoc]

/-- `thm:Palatini-torsion` (inversion core + cutoff
torsion bound). -/
theorem palatini_torsion_core {A : Type*} [Ring A]
    [Algebra ℝ A] (J : A) (hJ : J * J = -1)
    (α β : ℝ) (h : α ^ 2 + β ^ 2 ≠ 0) :
    -- (i) the boxed two-sided inversion
    ((α • J + β • (1 : A))
      * ((α ^ 2 + β ^ 2)⁻¹ • (β • (1 : A) - α • J)) = 1)
    ∧ (((α ^ 2 + β ^ 2)⁻¹ • (β • (1 : A) - α • J))
      * (α • J + β • (1 : A)) = 1)
    -- (ii) the boxed finite-cutoff torsion bound
    ∧ (∀ {V W : Type} [NormedAddCommGroup V]
        [NormedAddCommGroup W]
        (K : V → W) (T : V) (w : W) (κ : ℝ), 0 < κ →
        (∀ v, κ * ‖v‖ ≤ ‖K v‖) → K T = w →
        ‖T‖ ≤ κ⁻¹ * ‖w‖) := by
  have key1 : (α • J + β • (1 : A))
      * (β • (1 : A) - α • J)
      = (α ^ 2 + β ^ 2) • (1 : A) := by
    simp only [add_mul, mul_sub, smul_mul_smul_comm,
      mul_one, one_mul, hJ, smul_neg]
    module
  have key2 : (β • (1 : A) - α • J)
      * (α • J + β • (1 : A))
      = (α ^ 2 + β ^ 2) • (1 : A) := by
    simp only [sub_mul, mul_add, smul_mul_smul_comm,
      mul_one, one_mul, hJ, smul_neg]
    module
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_smul_comm, key1, smul_smul,
      inv_mul_cancel₀ h, one_smul]
  · rw [smul_mul_assoc, key2, smul_smul,
      inv_mul_cancel₀ h, one_smul]
  · intro V W _ _ K T w κ hκ hK hT
    have h1 := hK T
    rw [hT] at h1
    have h2 : ‖T‖ * κ ≤ ‖w‖ := by
      have := mul_comm ‖T‖ κ
      linarith
    rw [inv_mul_eq_div, le_div_iff₀ hκ]
    exact h2

end NCG
