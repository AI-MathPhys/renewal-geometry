/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Sibuya-subordinated eigenmode generating function
  (`thm:sibuya-subordinated-eigenmode-main`, SM_emergence)

* `sibuyaGF` — the Sibuya(α) waiting-law generating function
  `ψ(z) = 1 - (1-z)^α`;
* `renewal_count_summation` — summing the completed-renewal count
  over `k` renewals, `Σ_k (sψ)^k·(1-ψ)/(1-z)`, gives the standard
  renewal identity `U_s(z) = (1-ψ)/((1-z)(1-sψ))`;
* `sibuya_substitution` — substituting the Sibuya generating
  function yields the boxed exact eigenmode formula
  `U_s(z) = (1-z)^{α-1}/(1-s+s(1-z)^α)`;
* `sibuya_eigenmode_gf` — the combined statement.

The per-count generating identity `Σ_n P(N_n = k) zⁿ =
ψ(z)^k(1-ψ(z))/(1-z)` is the declared renewal-model input, and the
singularity-analysis asymptotics `u_n ~ n^{-α}/((1-s)Γ(1-α))` are
not formalized.
-/

namespace NCG

/-- The Sibuya(α) waiting-law generating function
`ψ(z) = 1 - (1-z)^α`. -/
noncomputable def sibuyaGF (alpha z : ℝ) : ℝ := 1 - (1 - z) ^ alpha

/-- The renewal-count summation: summing `(sψ)^k` against the
survivor factor `(1-ψ)/(1-z)` over the completed-renewal count `k`
gives the standard renewal identity. -/
theorem renewal_count_summation {s psi z : ℝ}
    (h : |s * psi| < 1) (hz : z ≠ 1) :
    ∑' k : ℕ, (s * psi) ^ k * ((1 - psi) / (1 - z))
      = (1 - psi) / ((1 - z) * (1 - s * psi)) := by
  have hz' : (1 : ℝ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hne : s * psi ≠ 1 := by
    intro he
    rw [he] at h
    simp at h
  have h1 : (1 : ℝ) - s * psi ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rw [tsum_mul_right, tsum_geometric_of_abs_lt_one h]
  field_simp

/-- `thm:sibuya-subordinated-eigenmode-main` (substitution):
plugging the Sibuya generating function into the renewal identity
gives the boxed eigenmode formula. -/
theorem sibuya_substitution {alpha s z : ℝ} (hz : z < 1) :
    (1 - sibuyaGF alpha z)
        / ((1 - z) * (1 - s * sibuyaGF alpha z))
      = (1 - z) ^ (alpha - 1)
        / (1 - s + s * (1 - z) ^ alpha) := by
  have hpos : (0 : ℝ) < 1 - z := by linarith
  simp only [sibuyaGF]
  rw [show (1 : ℝ) - (1 - (1 - z) ^ alpha) = (1 - z) ^ alpha from
      by ring,
    show (1 : ℝ) - s * (1 - (1 - z) ^ alpha)
      = 1 - s + s * (1 - z) ^ alpha from by ring]
  rw [Real.rpow_sub hpos, Real.rpow_one, div_div]

/-- The combined exact generating function: the renewal-count sum
of the Sibuya-subordinated eigenmode equals
`(1-z)^{α-1}/(1-s+s(1-z)^α)`. -/
theorem sibuya_eigenmode_gf {alpha s z : ℝ} (hz : z < 1)
    (habs : |s * sibuyaGF alpha z| < 1) :
    ∑' k : ℕ, (s * sibuyaGF alpha z) ^ k
        * ((1 - sibuyaGF alpha z) / (1 - z))
      = (1 - z) ^ (alpha - 1)
        / (1 - s + s * (1 - z) ^ alpha) := by
  rw [renewal_count_summation habs (by linarith),
    sibuya_substitution hz]

end NCG
