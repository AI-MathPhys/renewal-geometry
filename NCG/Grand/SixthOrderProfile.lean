/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Universal continuum cell profile through sixth order
  (`thm:renewal-sixth-order-cell-profile`, Gran-Tensor
  manuscript)

* `geometric_remainder_bound`: the boxed seventh-order error —
  a Stieltjes jet whose coefficients beyond sixth order are
  dominated by `D·q^{j-2}` has remainder at most
  `E⁽⁷⁾ = D·q⁵|θ|⁷/(1-q|θ|)` (geometric tail comparison);
* `sixth_jet_identity`: the boxed effective-diffusivity bracket
  — the sixth-order polynomial jet `P⁽⁶⁾ = Σ θʲD⁽ʲ⁾` with the
  displayed `D⁽²⁾…D⁽⁶⁾` satisfies exactly
  `κ_eff⁽⁶⁾·(2πk₁)² = κ·(2πk₁)² - P⁽⁶⁾` — the Markovian bracket
  is the jet, term by term;
* `stieltjes_mass_bound`: the boxed memory-mass window — with
  `m(0) = d + ν_total`, `|m(0) - P| ≤ E`, and `|d - P| ≤ E`,
  the memory mass satisfies `0 ≤ ν_total ≤ 2E` — every
  finite-frequency memory mass is `O(|θ|⁷)`.

Rendering disclosed: the derivation of the coefficient
domination `|c_j| ≤ D·q^{j-2}` from the first-chaos cell
expansion (the `q_φ` contraction), the subsequential-limit
existence of the continuum Stieltjes profile, and the
identification of the displayed `D⁽ʲ⁾` with the renewal moments
are the manuscript's continuum layer; the remainder bound, the
jet identity, and the mass window are proved here.
-/

namespace NCG

/-- Boxed seventh-order remainder: coefficients dominated by
`D·qʲ⁺⁵` (for `θʲ⁺⁷`) leave a geometric tail at most
`D·q⁵|θ|⁷/(1-q|θ|)`. -/
theorem geometric_remainder_bound (c : ℕ → ℝ) (D q θ : ℝ)
    (_hD : 0 ≤ D) (hq : 0 ≤ q) (hθq : q * |θ| < 1)
    (hc : ∀ j, |c j| ≤ D * q ^ (j + 5)) :
    |∑' j : ℕ, c j * θ ^ (j + 7)|
      ≤ D * q ^ 5 * |θ| ^ 7 / (1 - q * |θ|) := by
  have hdom : ∀ j : ℕ, |c j * θ ^ (j + 7)|
      ≤ D * q ^ 5 * |θ| ^ 7 * (q * |θ|) ^ j := by
    intro j
    rw [abs_mul, abs_pow]
    calc |c j| * |θ| ^ (j + 7)
        ≤ D * q ^ (j + 5) * |θ| ^ (j + 7) := by
          exact mul_le_mul_of_nonneg_right (hc j)
            (by positivity)
      _ = D * q ^ 5 * |θ| ^ 7 * (q * |θ|) ^ j := by
          rw [mul_pow]
          ring
  have hgeo : Summable fun j : ℕ =>
      D * q ^ 5 * |θ| ^ 7 * (q * |θ|) ^ j := by
    refine Summable.mul_left _ ?_
    exact summable_geometric_of_lt_one (by positivity) hθq
  have hsum : Summable fun j : ℕ => |c j * θ ^ (j + 7)| :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) hdom hgeo
  calc |∑' j : ℕ, c j * θ ^ (j + 7)|
      ≤ ∑' j : ℕ, |c j * θ ^ (j + 7)| := by
        have hsum' : Summable
            fun j : ℕ => ‖c j * θ ^ (j + 7)‖ := by
          simpa [Real.norm_eq_abs] using hsum
        have h := norm_tsum_le_tsum_norm hsum'
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' j : ℕ, D * q ^ 5 * |θ| ^ 7 * (q * |θ|) ^ j :=
        hsum.tsum_le_tsum hdom hgeo
    _ = D * q ^ 5 * |θ| ^ 7 * (1 - q * |θ|)⁻¹ := by
        rw [tsum_mul_left,
          tsum_geometric_of_lt_one (by positivity) hθq]
    _ = D * q ^ 5 * |θ| ^ 7 / (1 - q * |θ|) := by
        rw [div_eq_mul_inv]

/-- Boxed sixth-order effective diffusivity: the bracket is
exactly the jet — `κ_eff⁽⁶⁾·w = κ·w - P⁽⁶⁾(θ)` with
`w = (2πk₁)²` and the displayed `D⁽²⁾…D⁽⁶⁾`. -/
theorem sixth_jet_identity
    (κ r r3 j3 k3 r23 r4 μ3 θ w : ℝ) :
    κ * (1 - r * θ ^ 2 + μ3 * r ^ 2 * θ ^ 3
        - (μ3 ^ 2 * r ^ 3 + r3) * θ ^ 4
        + μ3 * (μ3 ^ 2 * r ^ 4 + 2 * r * r3 + j3) * θ ^ 5
        - (μ3 ^ 4 * r ^ 5 + 3 * μ3 ^ 2 * r ^ 2 * r3
            + 2 * μ3 ^ 2 * r * j3 + μ3 ^ 2 * k3
            + r23 + r4) * θ ^ 6) * w
      = κ * w
        - (θ ^ 2 * (κ * r * w)
          + θ ^ 3 * (-(κ * μ3 * r ^ 2) * w)
          + θ ^ 4 * (κ * (μ3 ^ 2 * r ^ 3 + r3) * w)
          + θ ^ 5 * (-(κ * μ3
              * (μ3 ^ 2 * r ^ 4 + 2 * r * r3 + j3)) * w)
          + θ ^ 6 * (κ * (μ3 ^ 4 * r ^ 5
              + 3 * μ3 ^ 2 * r ^ 2 * r3
              + 2 * μ3 ^ 2 * r * j3 + μ3 ^ 2 * k3
              + r23 + r4) * w)) := by
  ring

/-- Boxed memory-mass window: `m(0) = d + ν_total` with both
jet approximations within `E` give `0 ≤ ν_total ≤ 2E`. -/
theorem stieltjes_mass_bound {ι : Type*} [Fintype ι]
    (ν : ι → ℝ) (hν : ∀ i, 0 ≤ ν i) (m0 d P E : ℝ)
    (hstieltjes : m0 = d + ∑ i, ν i)
    (hm : |m0 - P| ≤ E) (hd : |d - P| ≤ E) :
    0 ≤ ∑ i, ν i ∧ ∑ i, ν i ≤ 2 * E := by
  have hnn : 0 ≤ ∑ i, ν i :=
    Finset.sum_nonneg fun i _ => hν i
  refine ⟨hnn, ?_⟩
  have h1 := abs_le.mp hm
  have h2 := abs_le.mp hd
  have : ∑ i, ν i = (m0 - P) - (d - P) := by
    rw [hstieltjes]
    ring
  linarith [h1.1, h1.2, h2.1, h2.2]

end NCG
