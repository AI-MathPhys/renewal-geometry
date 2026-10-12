/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Inversion of the Palatini–Holst operator and the finite-cutoff torsion bound

* `palatini_torsion_core`:
  (i) for `J` with `J² = -1` in an `ℝ`-algebra, `α J + β` is two-sided invertible with inverse
      `(β - α J)/(α² + β²)` (the inversion of `α ⋆ + β` from `⋆² = -I`);
  (ii) a linear map with a singular-value floor `κ ‖v‖ ≤ ‖K v‖` inverts with
      `‖T‖ ≤ κ⁻¹ ‖K T‖`.

Split out of `PotentialPalatini` (declaration name unchanged).
-/

namespace MathPhys

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

end MathPhys
