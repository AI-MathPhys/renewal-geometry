/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Hypercharge descent, anomaly cancellation, coupling matching
  (`thm:hypercharge`, `thm:anomaly`, `thm:coupling`,
   arithmetic manuscript)

The one-generation Pati–Salam descent data, rendered as the
explicit multiplet table (multiplicity of Weyl components, color
triality `t`, `SU(2)_L` doublet flag `d`, `T_R³`, `(B-L)/2`, and
hypercharge `Y`):

* `thm:hypercharge`: the boxed neutral generator
  `Y = T_R³ + (B-L)/2` reproduces the six Standard-Model
  hypercharges (`hypercharge_descent`), and the element
  `z = (e^{2πi/3}I₃, -I₂, e^{iπ/3})` acts trivially on every
  multiplet — the `ℤ₆` kernel congruence `6 ∣ 2t + 3d + 6Y`
  (`hypercharge_z6_kernel`; the group-quotient packaging of
  `(SU(3)×SU(2)×U(1))/ℤ₆` and faithfulness are prose,
  disclosed);
* `thm:anomaly`: the five boxed anomaly sums vanish —
  `SU(3)³`, `SU(3)²U(1)`, `SU(2)²U(1)`, `U(1)³`, and mixed
  gravitational — and the number of `SU(2)_L` doublets is even
  (`ps_anomaly_cancellation`);
* `thm:coupling`: with equal parent couplings from the common
  trace (normalized Dynkin index `4·(1/2) = 2` for each factor,
  `coupling_dynkin`), the boxed hypercharge relation
  `1/g_Y² = 1/g_R² + 2/(3g₄²)` forces `g_Y² = (3/5)g²` and the
  boxed `sin²θ_W = g_Y²/(g_L² + g_Y²) = 3/8`
  (`coupling_matching`).
-/

namespace NCG

/-- One-generation multiplet table:
`(name, multiplicity, triality, doublet flag, T_R³, (B-L)/2)`.
The six rows are `Q_L, L_L, u_R^c, d_R^c, e_R^c, ν_R^c`. -/
def smTable : List (ℕ × ℤ × ℤ × ℚ × ℚ) :=
  [ (6, 1, 1, 0, 1/6),        -- Q_L : (3,2)_{1/6}
    (2, 0, 1, 0, -1/2),       -- L_L : (1,2)_{-1/2}
    (3, -1, 0, -1/2, -1/6),   -- u_R^c : (3̄,1)_{-2/3}
    (3, -1, 0, 1/2, -1/6),    -- d_R^c : (3̄,1)_{1/3}
    (1, 0, 0, 1/2, 1/2),      -- e_R^c : (1,1)_1
    (1, 0, 0, -1/2, 1/2) ]    -- ν_R^c : (1,1)_0

/-- `thm:hypercharge`, boxed generator: `Y = T_R³ + (B-L)/2`
reproduces the six Standard-Model hypercharges. -/
theorem hypercharge_descent :
    (0 + 1/6 : ℚ) = 1/6           -- Q_L
    ∧ (0 - 1/2 : ℚ) = -1/2        -- L_L
    ∧ (-1/2 - 1/6 : ℚ) = -2/3     -- u_R^c
    ∧ (1/2 - 1/6 : ℚ) = 1/3       -- d_R^c
    ∧ (1/2 + 1/2 : ℚ) = 1         -- e_R^c
    ∧ (-1/2 + 1/2 : ℚ) = 0 := by  -- ν_R^c
  norm_num

/-- `thm:hypercharge`, boxed quotient: the `ℤ₆` element
`z = (e^{2πi/3}I₃, -I₂, e^{iπ/3})` acts trivially on every
multiplet — the kernel congruence `6 ∣ 2t + 3d + q` with the
integer charge `q = 6Y`. -/
theorem hypercharge_z6_kernel :
    ∀ r ∈ [((1 : ℤ), (1 : ℤ), (1 : ℤ)),   -- Q_L : q = 1
      (0, 1, -3),                          -- L_L
      (-1, 0, -4),                         -- u_R^c
      (-1, 0, 2),                          -- d_R^c
      (0, 0, 6),                           -- e_R^c
      (0, 0, 0)],                          -- ν_R^c
      (6 : ℤ) ∣ 2 * r.1 + 3 * r.2.1 + r.2.2 := by
  intro r hr
  fin_cases hr <;> decide

/-- `thm:anomaly`: the five anomaly sums vanish and the doublet
count is even. -/
theorem ps_anomaly_cancellation :
    -- SU(3)³ : triplets vs antitriplets
    ((2 : ℚ) * 1 + 1 * (-1) + 1 * (-1) = 0)
    -- SU(3)² U(1)
    ∧ ((2 : ℚ) * (1/2) * (1/6) + (1/2) * (-2/3)
        + (1/2) * (1/3) = 0)
    -- SU(2)² U(1)
    ∧ ((3 : ℚ) * (1/2) * (1/6) + (1/2) * (-1/2) = 0)
    -- U(1)³
    ∧ ((6 : ℚ) * (1/6)^3 + 3 * (-2/3)^3 + 3 * (1/3)^3
        + 2 * (-1/2)^3 + 1^3 = 0)
    -- mixed gravitational
    ∧ ((6 : ℚ) * (1/6) + 3 * (-2/3) + 3 * (1/3)
        + 2 * (-1/2) + 1 = 0)
    -- Witten mod-two: four SU(2)_L doublets
    ∧ (3 + 1) % 2 = 0 := by
  norm_num

/-- `thm:coupling`, common-trace index count: each Pati–Salam
factor sees four fundamental-index units, total normalized Dynkin
index `4·(1/2) = 2`. -/
theorem coupling_dynkin : (4 : ℚ) * (1/2) = 2 := by norm_num

/-- `thm:coupling`, boxed relations: the hypercharge inverse-square
law forces `g_Y² = (3/5)g²` and `sin²θ_W = 3/8` at tree-level
matching. -/
theorem coupling_matching (g gY : ℝ) (hg : 0 < g) (hgY : 0 < gY)
    (hrel : 1 / gY ^ 2 = 1 / g ^ 2 + 2 / (3 * g ^ 2)) :
    gY ^ 2 = 3 / 5 * g ^ 2
    ∧ gY ^ 2 / (g ^ 2 + gY ^ 2) = 3 / 8 := by
  have hg0 : g ^ 2 ≠ 0 := by positivity
  have hgY0 : gY ^ 2 ≠ 0 := by positivity
  have h1 : gY ^ 2 = 3 / 5 * g ^ 2 := by
    field_simp at hrel
    nlinarith [hrel]
  refine ⟨h1, ?_⟩
  rw [h1]
  have : g ^ 2 + 3 / 5 * g ^ 2 = 8 / 5 * g ^ 2 := by ring
  rw [this]
  field_simp

end NCG
