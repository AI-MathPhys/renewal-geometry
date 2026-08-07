/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Anomaly-forced central weights
  (`thm:SM-anomaly-forced-weights`, Gran-Tensor manuscript)

* `anomaly_forced_weights`: the displayed anomaly traces of the
  chiral packet vanish simultaneously exactly when `3a+2b = 0`;
  the coprime integral solutions are `(a,b) = ±(-2,3)`; and the
  substituted weight table is the boxed
  `y = (Q,u,d,L,e,H) = (1,4,-2,-3,-6,3)`.

Rendering disclosed: the tensor-type weight table
`(a+b,-2a,a,-b,-2b,b)` is definitional for the additive central
action on `Q = C⊗W, u = Λ²C*, d = C, L = W*, e = Λ²W*, H = W`;
the anomaly trace evaluations over the chiral packet are the
manuscript's displayed forms and are taken at face value here
(their vanishing structure and the arithmetic consequences are
what is proved).
-/

namespace NCG

/-- The tensor-type weight table of the central action. -/
def smCentralWeights (a b : ℤ) : Fin 6 → ℤ :=
  ![a + b, -2 * a, a, -b, -2 * b, b]

/-- `thm:SM-anomaly-forced-weights`: anomaly vanishing iff
`3a+2b = 0`, primitive integral solutions, and the boxed
hypercharge table. -/
theorem anomaly_forced_weights :
    (∀ a b : ℚ,
      ((3 * a + 2 * b) / 2 = 0
        ∧ 3 * (3 * a + 2 * b) = 0
        ∧ 3 * (3 * a + 2 * b) * (3 * a ^ 2 + 2 * b ^ 2) = 0)
      ↔ 3 * a + 2 * b = 0)
    ∧ (∀ a b : ℤ, 3 * a + 2 * b = 0 ↔
        ∃ t : ℤ, a = -2 * t ∧ b = 3 * t)
    ∧ (∀ a b : ℤ, 3 * a + 2 * b = 0 → IsCoprime a b →
        (a = -2 ∧ b = 3) ∨ (a = 2 ∧ b = -3))
    ∧ (smCentralWeights (-2) 3 = ![1, 4, -2, -3, -6, 3]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    constructor
    · rintro ⟨h1, -, -⟩
      linarith
    · intro h
      refine ⟨by linarith, by linarith, by
        rw [h, mul_zero, zero_mul]⟩
  · intro a b
    constructor
    · intro h
      have h2 : (2 : ℤ) ∣ a := by omega
      obtain ⟨s, hs⟩ := h2
      refine ⟨-s, by omega, by omega⟩
    · rintro ⟨t, rfl, rfl⟩
      ring
  · intro a b h hcop
    have hex : ∃ t : ℤ, a = -2 * t ∧ b = 3 * t := by
      have h2 : (2 : ℤ) ∣ a := by omega
      obtain ⟨s, hs⟩ := h2
      exact ⟨-s, by omega, by omega⟩
    obtain ⟨t, rfl, rfl⟩ := hex
    obtain ⟨u, v, huv⟩ := hcop
    have ht : t ∣ 1 :=
      ⟨-2 * u + 3 * v, by linear_combination -huv⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one ht) with rfl | rfl
    · left
      norm_num
    · right
      norm_num
  · funext i
    fin_cases i <;> simp [smCentralWeights]

end NCG
