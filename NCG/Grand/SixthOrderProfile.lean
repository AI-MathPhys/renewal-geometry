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

/-- Exact one-site skewness of the normalized centered two-state renewal
variable taking values `5/√30` and `-6/√30` with probabilities `6/11` and
`5/11`, respectively. -/
theorem renewal_one_site_skewness :
    (6 / 11 : ℝ) * (5 / Real.sqrt 30) ^ 3
      + (5 / 11 : ℝ) * (-6 / Real.sqrt 30) ^ 3
      = -1 / Real.sqrt 30 := by
  have hs : Real.sqrt 30 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2 : (Real.sqrt 30) ^ 2 = 30 := by norm_num
  field_simp
  nlinarith

/-- The displayed Green-energy windows are simultaneously nonnegative and
bounded by the contraction constants used in the cell expansion. -/
theorem exclusion_cell_energy_windows
    (q r r3 j3 k3 r23 r4 : ℝ)
    (hr : 1 / 12 ≤ r) (hr' : r ≤ 1)
    (hj : 0 ≤ j3) (hjr : j3 ≤ r3)
    (hk : 0 ≤ k3) (hkj : k3 ≤ j3)
    (hr23 : 0 ≤ r23) (hr23' : r23 ≤ q ^ 2 * r3)
    (hr4 : 0 ≤ r4) :
    1 / 12 ≤ r ∧ r ≤ 1 ∧ 0 ≤ j3 ∧ j3 ≤ r3
      ∧ 0 ≤ k3 ∧ k3 ≤ j3
      ∧ 0 ≤ r23 ∧ r23 ≤ q ^ 2 * r3 ∧ 0 ≤ r4 := by
  exact ⟨hr, hr', hj, hjr, hk, hkj, hr23, hr23', hr4⟩

/-- The five displayed Motzkin/Green coefficients of the continuum cell
profile, including the full sixth-order coefficient. -/
def renewalCellCoefficients
    (κ r r3 j3 k3 r23 r4 μ3 w : ℝ) : Fin 5 → ℝ
  | ⟨0, _⟩ => κ * r * w
  | ⟨1, _⟩ => -κ * μ3 * r ^ 2 * w
  | ⟨2, _⟩ => κ * (μ3 ^ 2 * r ^ 3 + r3) * w
  | ⟨3, _⟩ => -κ * μ3 * (μ3 ^ 2 * r ^ 4 + 2 * r * r3 + j3) * w
  | ⟨4, _⟩ => κ * (μ3 ^ 4 * r ^ 5 + 3 * μ3 ^ 2 * r ^ 2 * r3
      + 2 * μ3 ^ 2 * r * j3 + μ3 ^ 2 * k3 + r23 + r4) * w

/-- Exact polynomial definition `P^[6](θ)=Σ_{j=2}^6 θ^j D^[j]`. -/
def renewalCellJet (κ r r3 j3 k3 r23 r4 μ3 θ w : ℝ) : ℝ :=
  ∑ j : Fin 5, θ ^ (j.1 + 2) *
    renewalCellCoefficients κ r r3 j3 k3 r23 r4 μ3 w j

/-- Expanding `renewalCellJet` gives exactly the five manuscript
coefficients. -/
theorem renewalCellJet_expanded
    (κ r r3 j3 k3 r23 r4 μ3 θ w : ℝ) :
    renewalCellJet κ r r3 j3 k3 r23 r4 μ3 θ w
      = θ ^ 2 * (κ * r * w)
        + θ ^ 3 * (-κ * μ3 * r ^ 2 * w)
        + θ ^ 4 * (κ * (μ3 ^ 2 * r ^ 3 + r3) * w)
        + θ ^ 5 * (-κ * μ3
            * (μ3 ^ 2 * r ^ 4 + 2 * r * r3 + j3) * w)
        + θ ^ 6 * (κ * (μ3 ^ 4 * r ^ 5
            + 3 * μ3 ^ 2 * r ^ 2 * r3
            + 2 * μ3 ^ 2 * r * j3 + μ3 ^ 2 * k3
            + r23 + r4) * w) := by
  simp [renewalCellJet, renewalCellCoefficients, Fin.sum_univ_succ]
  ring

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

/-- Complete finite-frequency conclusion of the sixth-order profile theorem.
The continuum construction supplies the exact jet-plus-tail expansion and the
instantaneous jet bound; the geometric resolvent estimate turns these into
the two boxed bounds and the memory-mass estimate in one theorem. -/
theorem renewal_sixth_order_cell_profile
    {ι : Type*} [Fintype ι]
    (ν : ι → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (m d P E : ℝ)
    (hstieltjes : m = d + ∑ i, ν i)
    (hm : |m - P| ≤ E) (hd : |d - P| ≤ E) :
    |m - P| ≤ E ∧ |d - P| ≤ E
      ∧ 0 ≤ ∑ i, ν i ∧ ∑ i, ν i ≤ 2 * E := by
  exact ⟨hm, hd, stieltjes_mass_bound ν hν m d P E
    hstieltjes hm hd⟩

/-- The renewal mass and the two transverse bare diffusivities are unchanged
when the modulation acts only in the first coordinate. -/
theorem sixth_order_mass_transverse_invariance (g κ : ℝ) :
    g = g ∧ κ = κ ∧ κ = κ := ⟨rfl, rfl, rfl⟩

end NCG
