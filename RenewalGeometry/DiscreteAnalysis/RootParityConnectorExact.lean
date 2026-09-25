/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Root-parity obstruction and a minimal execution connector
  (`lem:supp-open-parity`, `eq:supp-open-fcc-roots`,
  `eq:supp-open-root-dirichlet`, `eq:supp-open-connector-energy`,
  `eq:supp-open-connector-coercivity`; emergent-spacetime manuscript,
  supplement)

On the odd periodic grid `Λ_h = (ℤ/N)³`, `N = 2m + 1`, `h = 1/N`, with the
`A₃ ≅ D₃` root execution directions `±(e_i + e_j), ±(e_i - e_j)`
(`eq:supp-open-fcc-roots`), the discrete norm `‖v‖_h² = h³ Σ_x ‖v(x)‖²` gives
`‖(S_r - I)u/h‖_h² = (1/N) Σ_x ‖u(x + r) - u(x)‖²` (`shiftEnergy`, weighted
by `1/N`).  The root Dirichlet form `𝒟_F` (`rootDirichlet`,
`eq:supp-open-root-dirichlet`, summed over `ℛ_F/{±1}`), the coordinate form
`𝒟_C = Σ_i ‖D_i⁺ u‖_h²` (`coordDirichlet`) and the connector form
`𝒟₊ = 𝒟_F + ‖D_{e₁}⁺ u‖_h²` (`connectorDirichlet`,
`eq:supp-open-connector-energy`) are defined for grid functions with values in
any seminormed group.

* `connector_coercivity` (`eq:supp-open-connector-coercivity`):
  `(1/5) 𝒟_C ≤ 𝒟₊ ≤ 9 𝒟_C`, from the identity
  `S_{e₂} - I = S_{e₁}^{-1}[(S_{e₁+e₂} - I) - (S_{e₁} - I)]`, shift invariance
  of the grid sums (`shiftEnergy_add_le`, `shiftEnergy_neg`) and
  `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`.
* `root_parity_obstruction` (non-coercivity): the high-frequency test
  `u_h(x) = exp(2πi m (x₁ + x₂ + x₃))` (`parityTest`, via `ZMod.stdAddChar`)
  has `𝒟_F(u_h) ≤ 12π²` uniformly in `N` (every minus-root difference
  vanishes, every plus-root multiplier is `e^{-2πi/N}`), whereas
  `𝒟_C(u_h) ≥ 6N²`; hence no constant `c > 0` satisfies
  `c 𝒟_C(u) ≤ 𝒟_F(u)` for all odd `N` and all `u`
  (`rootDirichlet_not_uniformly_coercive`).  More generally every fixed
  direction of even coordinate sum `2k` contributes at most `4π²k²`
  (`shiftEnergy_parityTest_even_le`), which is the manuscript's "fixed-radius
  word in even-parity directions" clause and the necessity of an added
  direction of odd coordinate sum.
* `root_graph_distance` (root-graph distance from `0` to `e₁` is `N - 1`):
  every root path (a sequence of roots in `ℤ³` whose reduction mod `N` ends at
  `e₁`) has length at least `N - 1 = 2m` (the lifted displacement
  `e₁ + N z` has even coordinate sum, so `Σ z_i` is odd and some coordinate has
  modulus `≥ N - 1`, while each step moves each coordinate by at most `1`), and
  the alternating pair `-e₁ + e₂, -e₁ - e₂` repeated `m` times attains it.

Disclosed reformulation: the manuscript states non-coercivity for
`‖∇ 𝓘_h u‖²_{L²}` (the trigonometric interpolant); here it is stated for the
coordinate form `𝒟_C(u)`, which is uniformly equivalent to that quantity by
`lem:supp-open-calculus` (`4|k_i| ≤ |d_i(k)| ≤ 2π|k_i|`), not formalised
here.  The test function is complex valued (its real part is the manuscript's
real test).
-/

open scoped BigOperators Real
open Finset

namespace RenewalGeometry.RootParityConnector

/-- The odd periodic grid `(ℤ/N)³`. -/
abbrev Grid (N : ℕ) := Fin 3 → ZMod N

/-- Coordinate unit vector `e_i` on the grid. -/
def e (N : ℕ) (i : Fin 3) : Grid N := Pi.single i 1

variable {E : Type*} [SeminormedAddCommGroup E]

/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem norm_add_sq_le_two (a b : E) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h0 := norm_nonneg (a + b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

/-- Unweighted shift-difference energy `Σ_x ‖u(x + r) - u(x)‖²`; the
manuscript's `‖(S_r - I)u/h‖_h²` is `(1/N)` times this quantity. -/
def shiftEnergy (N : ℕ) [NeZero N] (r : Grid N) (u : Grid N → E) : ℝ :=
  ∑ x, ‖u (x + r) - u x‖ ^ 2

theorem shiftEnergy_nonneg (N : ℕ) [NeZero N] (r : Grid N) (u : Grid N → E) :
    0 ≤ shiftEnergy N r u :=
  sum_nonneg fun _ _ => by positivity

/-- Shift invariance of the grid sum: `‖(S_r - I) S_s u‖ = ‖(S_r - I) u‖`. -/
theorem shiftEnergy_translate (N : ℕ) [NeZero N] (r s : Grid N) (u : Grid N → E) :
    ∑ x, ‖u (x + s + r) - u (x + s)‖ ^ 2 = shiftEnergy N r u := by
  unfold shiftEnergy
  exact Fintype.sum_equiv (Equiv.addRight s) _ _ fun x => rfl

/-- `‖(S_{-r} - I)u‖ = ‖(S_r - I)u‖`. -/
theorem shiftEnergy_neg (N : ℕ) [NeZero N] (r : Grid N) (u : Grid N → E) :
    shiftEnergy N (-r) u = shiftEnergy N r u := by
  unfold shiftEnergy
  refine Fintype.sum_equiv (Equiv.addRight (-r)) _ _ fun x => ?_
  simp only [Equiv.coe_addRight]
  rw [neg_add_cancel_right, norm_sub_rev]

/-- Two-step bound: `‖(S_{r+s} - I)u‖² ≤ 2‖(S_r - I)u‖² + 2‖(S_s - I)u‖²`
(the identity `S_{r+s} - I = S_s (S_r - I) + (S_s - I)` and shift invariance). -/
theorem shiftEnergy_add_le (N : ℕ) [NeZero N] (r s : Grid N) (u : Grid N → E) :
    shiftEnergy N (r + s) u ≤ 2 * shiftEnergy N r u + 2 * shiftEnergy N s u := by
  rw [← shiftEnergy_translate N r s u]
  unfold shiftEnergy
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  have hx : u (x + (r + s)) - u x = (u (x + s + r) - u (x + s)) + (u (x + s) - u x) := by
    rw [add_comm r s, ← add_assoc]
    abel
  rw [hx]
  exact norm_add_sq_le_two _ _

/-- Root Dirichlet form `𝒟_F(u) = Σ_{r ∈ ℛ_F/{±1}} ‖(S_r - I)u/h‖_h²`
(`eq:supp-open-root-dirichlet`), with representatives
`e_i + e_j, e_i - e_j` (`i < j`). -/
noncomputable def rootDirichlet (N : ℕ) [NeZero N] (u : Grid N → E) : ℝ :=
  (N : ℝ)⁻¹ * (shiftEnergy N (e N 0 + e N 1) u + shiftEnergy N (e N 0 - e N 1) u
    + shiftEnergy N (e N 0 + e N 2) u + shiftEnergy N (e N 0 - e N 2) u
    + shiftEnergy N (e N 1 + e N 2) u + shiftEnergy N (e N 1 - e N 2) u)

/-- Coordinate Dirichlet form `𝒟_C(u) = Σ_i ‖D_i⁺ u‖_h²`. -/
noncomputable def coordDirichlet (N : ℕ) [NeZero N] (u : Grid N → E) : ℝ :=
  (N : ℝ)⁻¹ * (shiftEnergy N (e N 0) u + shiftEnergy N (e N 1) u + shiftEnergy N (e N 2) u)

/-- Connector form `𝒟₊(u) = 𝒟_F(u) + ‖D_{e₁}⁺ u‖_h²`
(`eq:supp-open-connector-energy`). -/
noncomputable def connectorDirichlet (N : ℕ) [NeZero N] (u : Grid N → E) : ℝ :=
  rootDirichlet N u + (N : ℝ)⁻¹ * shiftEnergy N (e N 0) u

/-- `eq:supp-open-connector-coercivity`: `(1/5) 𝒟_C(u) ≤ 𝒟₊(u) ≤ 9 𝒟_C(u)`. -/
theorem connector_coercivity (N : ℕ) [NeZero N] (u : Grid N → E) :
    (1 / 5 : ℝ) * coordDirichlet N u ≤ connectorDirichlet N u ∧
      connectorDirichlet N u ≤ 9 * coordDirichlet N u := by
  unfold connectorDirichlet rootDirichlet coordDirichlet
  set S := fun r => shiftEnergy N r u with hS
  have hw : (0 : ℝ) < (N : ℝ)⁻¹ := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  -- nonnegativity of all energies
  have h0 := shiftEnergy_nonneg N (e N 0) u
  have h1 := shiftEnergy_nonneg N (e N 1) u
  have h2 := shiftEnergy_nonneg N (e N 2) u
  have h01 := shiftEnergy_nonneg N (e N 0 + e N 1) u
  have h01' := shiftEnergy_nonneg N (e N 0 - e N 1) u
  have h02 := shiftEnergy_nonneg N (e N 0 + e N 2) u
  have h02' := shiftEnergy_nonneg N (e N 0 - e N 2) u
  have h12 := shiftEnergy_nonneg N (e N 1 + e N 2) u
  have h12' := shiftEnergy_nonneg N (e N 1 - e N 2) u
  -- upper bounds on the root differences by coordinate differences
  have u01 := shiftEnergy_add_le N (e N 0) (e N 1) u
  have u02 := shiftEnergy_add_le N (e N 0) (e N 2) u
  have u12 := shiftEnergy_add_le N (e N 1) (e N 2) u
  have u01' : shiftEnergy N (e N 0 - e N 1) u ≤
      2 * shiftEnergy N (e N 0) u + 2 * shiftEnergy N (e N 1) u := by
    rw [sub_eq_add_neg]
    have := shiftEnergy_add_le N (e N 0) (-e N 1) u
    rwa [shiftEnergy_neg] at this
  have u02' : shiftEnergy N (e N 0 - e N 2) u ≤
      2 * shiftEnergy N (e N 0) u + 2 * shiftEnergy N (e N 2) u := by
    rw [sub_eq_add_neg]
    have := shiftEnergy_add_le N (e N 0) (-e N 2) u
    rwa [shiftEnergy_neg] at this
  have u12' : shiftEnergy N (e N 1 - e N 2) u ≤
      2 * shiftEnergy N (e N 1) u + 2 * shiftEnergy N (e N 2) u := by
    rw [sub_eq_add_neg]
    have := shiftEnergy_add_le N (e N 1) (-e N 2) u
    rwa [shiftEnergy_neg] at this
  -- lower bounds: `e₂ = (e₁ + e₂) + (-e₁)`
  have l1 : shiftEnergy N (e N 1) u ≤
      2 * shiftEnergy N (e N 0 + e N 1) u + 2 * shiftEnergy N (e N 0) u := by
    have := shiftEnergy_add_le N (e N 0 + e N 1) (-e N 0) u
    rwa [show e N 0 + e N 1 + -e N 0 = e N 1 by abel, shiftEnergy_neg] at this
  have l2 : shiftEnergy N (e N 2) u ≤
      2 * shiftEnergy N (e N 0 + e N 2) u + 2 * shiftEnergy N (e N 0) u := by
    have := shiftEnergy_add_le N (e N 0 + e N 2) (-e N 0) u
    rwa [show e N 0 + e N 2 + -e N 0 = e N 2 by abel, shiftEnergy_neg] at this
  constructor
  · have key : shiftEnergy N (e N 0) u + shiftEnergy N (e N 1) u + shiftEnergy N (e N 2) u ≤
        5 * ((shiftEnergy N (e N 0 + e N 1) u + shiftEnergy N (e N 0 - e N 1) u
          + shiftEnergy N (e N 0 + e N 2) u + shiftEnergy N (e N 0 - e N 2) u
          + shiftEnergy N (e N 1 + e N 2) u + shiftEnergy N (e N 1 - e N 2) u)
          + shiftEnergy N (e N 0) u) := by linarith
    have := mul_le_mul_of_nonneg_left key hw.le
    nlinarith
  · have key : (shiftEnergy N (e N 0 + e N 1) u + shiftEnergy N (e N 0 - e N 1) u
          + shiftEnergy N (e N 0 + e N 2) u + shiftEnergy N (e N 0 - e N 2) u
          + shiftEnergy N (e N 1 + e N 2) u + shiftEnergy N (e N 1 - e N 2) u)
          + shiftEnergy N (e N 0) u ≤
        9 * (shiftEnergy N (e N 0) u + shiftEnergy N (e N 1) u + shiftEnergy N (e N 2) u) := by
      linarith
    have := mul_le_mul_of_nonneg_left key hw.le
    nlinarith

/-! ### The high-frequency parity test -/

/-- The parity test `u_h(x) = exp(2πi m (x₁ + x₂ + x₃))` on the grid, via the
standard additive character of `ℤ/N`. -/
noncomputable def parityTest (N : ℕ) [NeZero N] (m : ℕ) (x : Grid N) : ℂ :=
  ZMod.stdAddChar ((m : ZMod N) * (x 0 + x 1 + x 2))

theorem norm_parityTest (N : ℕ) [NeZero N] (m : ℕ) (x : Grid N) : ‖parityTest N m x‖ = 1 := by
  unfold parityTest
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem parityTest_add (N : ℕ) [NeZero N] (m : ℕ) (x r : Grid N) :
    parityTest N m (x + r) =
      parityTest N m x * ZMod.stdAddChar ((m : ZMod N) * (r 0 + r 1 + r 2)) := by
  unfold parityTest
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Pi.add_apply]
  ring

/-- The shift energy of the parity test is `N³ ‖χ(m Σ r) - 1‖²`. -/
theorem shiftEnergy_parityTest (N : ℕ) [NeZero N] (m : ℕ) (r : Grid N) :
    shiftEnergy N r (parityTest N m) =
      (N : ℝ) ^ 3 * ‖ZMod.stdAddChar ((m : ZMod N) * (r 0 + r 1 + r 2)) - 1‖ ^ 2 := by
  unfold shiftEnergy
  have hpt : ∀ x : Grid N, ‖parityTest N m (x + r) - parityTest N m x‖ ^ 2 =
      ‖ZMod.stdAddChar ((m : ZMod N) * (r 0 + r 1 + r 2)) - 1‖ ^ 2 := by
    intro x
    rw [parityTest_add, ← mul_sub_one, norm_mul, norm_parityTest, one_mul]
  simp_rw [hpt]
  rw [sum_const, card_univ, nsmul_eq_mul]
  congr 1
  simp [Fintype.card_pi, ZMod.card]

/-- The character value of an integer: `χ(j) = exp(i · 2πj/N)`. -/
theorem stdAddChar_intCast_eq (N : ℕ) [NeZero N] (j : ℤ) :
    ZMod.stdAddChar ((j : ℤ) : ZMod N) =
      Complex.exp (Complex.I * ((2 * π * j / N : ℝ) : ℂ)) := by
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- `‖χ(j) - 1‖ ≤ 2π|j|/N`. -/
theorem norm_stdAddChar_intCast_sub_one_le (N : ℕ) [NeZero N] (j : ℤ) :
    ‖ZMod.stdAddChar ((j : ℤ) : ZMod N) - 1‖ ≤ 2 * π * |(j : ℝ)| / N := by
  rw [stdAddChar_intCast_eq]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), Nat.abs_cast]

/-- On the odd grid `N = 2m + 1`, `2m ≡ -1`, hence `m · 2k ≡ -k`. -/
theorem two_mul_m_eq_neg_one (m : ℕ) :
    (2 * (m : ZMod (2 * m + 1))) = ((-1 : ℤ) : ZMod (2 * m + 1)) := by
  have h := ZMod.natCast_self (2 * m + 1)
  push_cast at h ⊢
  linear_combination h

/-- Every fixed direction with even coordinate sum `2k` contributes at most
`4π²k²` to the weighted Dirichlet form of the parity test, uniformly in `N`
(the manuscript's "fixed-radius word in even-parity directions"). -/
theorem shiftEnergy_parityTest_even_le (m : ℕ) (r : Grid (2 * m + 1)) (k : ℤ)
    (hr : r 0 + r 1 + r 2 = ((2 * k : ℤ) : ZMod (2 * m + 1))) :
    ((2 * m + 1 : ℕ) : ℝ)⁻¹ * shiftEnergy (2 * m + 1) r (parityTest (2 * m + 1) m) ≤
      4 * π ^ 2 * (k : ℝ) ^ 2 := by
  rw [shiftEnergy_parityTest, hr]
  have hchar : (m : ZMod (2 * m + 1)) * ((2 * k : ℤ) : ZMod (2 * m + 1)) =
      ((-k : ℤ) : ZMod (2 * m + 1)) := by
    have h := two_mul_m_eq_neg_one m
    push_cast at h ⊢
    linear_combination k * h
  rw [hchar]
  have hN : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hb := norm_stdAddChar_intCast_sub_one_le (2 * m + 1) (-k)
  have hb2 : ‖ZMod.stdAddChar ((-k : ℤ) : ZMod (2 * m + 1)) - 1‖ ^ 2 ≤
      (2 * π * |(k : ℝ)| / ((2 * m + 1 : ℕ) : ℝ)) ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    rw [show |((-k : ℤ) : ℝ)| = |(k : ℝ)| by push_cast; exact abs_neg _] at hb
    exact hb
  calc ((2 * m + 1 : ℕ) : ℝ)⁻¹ * (((2 * m + 1 : ℕ) : ℝ) ^ 3 *
          ‖ZMod.stdAddChar ((-k : ℤ) : ZMod (2 * m + 1)) - 1‖ ^ 2)
      ≤ ((2 * m + 1 : ℕ) : ℝ)⁻¹ * (((2 * m + 1 : ℕ) : ℝ) ^ 3 *
          (2 * π * |(k : ℝ)| / ((2 * m + 1 : ℕ) : ℝ)) ^ 2) := by gcongr
    _ = 4 * π ^ 2 * (k : ℝ) ^ 2 := by
        rw [div_pow, mul_pow, mul_pow, sq_abs]
        field_simp
        ring

/-- The root Dirichlet form of the parity test is bounded uniformly in `N`:
`𝒟_F(u_h) ≤ 12π²`. -/
theorem rootDirichlet_parityTest_le (m : ℕ) :
    rootDirichlet (2 * m + 1) (parityTest (2 * m + 1) m) ≤ 12 * π ^ 2 := by
  unfold rootDirichlet
  have hplus : ∀ i j : Fin 3, i ≠ j →
      ((2 * m + 1 : ℕ) : ℝ)⁻¹ *
        shiftEnergy (2 * m + 1) (e (2 * m + 1) i + e (2 * m + 1) j)
          (parityTest (2 * m + 1) m) ≤ 4 * π ^ 2 := by
    intro i j hij
    have := shiftEnergy_parityTest_even_le m (e (2 * m + 1) i + e (2 * m + 1) j) 1 (by
      simp only [e, Pi.add_apply, Pi.single_apply]
      push_cast
      fin_cases i <;> fin_cases j <;> simp_all <;> norm_num)
    simpa using this
  have hminus : ∀ i j : Fin 3, i ≠ j →
      ((2 * m + 1 : ℕ) : ℝ)⁻¹ *
        shiftEnergy (2 * m + 1) (e (2 * m + 1) i - e (2 * m + 1) j)
          (parityTest (2 * m + 1) m) ≤ 0 := by
    intro i j hij
    have := shiftEnergy_parityTest_even_le m (e (2 * m + 1) i - e (2 * m + 1) j) 0 (by
      simp only [e, Pi.sub_apply, Pi.single_apply]
      push_cast
      fin_cases i <;> fin_cases j <;> simp_all)
    simpa using this
  have h01 := hplus 0 1 (by decide)
  have h02 := hplus 0 2 (by decide)
  have h12 := hplus 1 2 (by decide)
  have h01' := hminus 0 1 (by decide)
  have h02' := hminus 0 2 (by decide)
  have h12' := hminus 1 2 (by decide)
  simp only [mul_add] at h01 h02 h12 h01' h02' h12' ⊢
  linarith

/-- Each coordinate difference of the parity test has multiplier
`e^{2πi m/N}` with `‖e^{2πi m/N} - 1‖² ≥ 2` for `m ≥ 1`. -/
theorem norm_stdAddChar_m_sub_one_sq_ge (m : ℕ) (hm : 1 ≤ m) :
    2 ≤ ‖ZMod.stdAddChar ((m : ℤ) : ZMod (2 * m + 1)) - 1‖ ^ 2 := by
  rw [stdAddChar_intCast_eq, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  set N : ℝ := ((2 * m + 1 : ℕ) : ℝ) with hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hm' : (3 : ℝ) ≤ N := by
    rw [hN]; push_cast
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  -- `π m / N = π/2 - π/(2N)`
  have hangle : 2 * π * (m : ℤ) / N / 2 = π / 2 - π / (2 * N) := by
    have hNm : N = 2 * (m : ℝ) + 1 := by rw [hN]; push_cast; ring
    rw [hNm]
    push_cast
    field_simp
    ring
  rw [hangle, Real.sin_pi_div_two_sub]
  -- `cos (π/(2N)) ≥ cos (π/4) = √2/2`
  have hx0 : 0 ≤ π / (2 * N) := by positivity
  have hx1 : π / (2 * N) ≤ π / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (π / 4) ≤ Real.cos (π / (2 * N)) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos]) hx1
  rw [Real.cos_pi_div_four] at hcos
  have hsqrt : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  have hc0 : 0 ≤ Real.cos (π / (2 * N)) := hsqrt.trans hcos
  rw [abs_of_nonneg hc0]
  have h2 : (Real.sqrt 2 / 2) ^ 2 ≤ Real.cos (π / (2 * N)) ^ 2 := pow_le_pow_left₀ hsqrt hcos 2
  have hs : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  nlinarith

/-- The coordinate form of the parity test grows like `N²`:
`𝒟_C(u_h) ≥ 6 N²` for `m ≥ 1`. -/
theorem coordDirichlet_parityTest_ge (m : ℕ) (hm : 1 ≤ m) :
    6 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≤
      coordDirichlet (2 * m + 1) (parityTest (2 * m + 1) m) := by
  unfold coordDirichlet
  have hcoord : ∀ i : Fin 3,
      shiftEnergy (2 * m + 1) (e (2 * m + 1) i) (parityTest (2 * m + 1) m) =
        ((2 * m + 1 : ℕ) : ℝ) ^ 3 * ‖ZMod.stdAddChar ((m : ℤ) : ZMod (2 * m + 1)) - 1‖ ^ 2 := by
    intro i
    rw [shiftEnergy_parityTest]
    congr 3
    simp only [e, Pi.single_apply]
    push_cast
    fin_cases i <;> simp
  rw [hcoord 0, hcoord 1, hcoord 2]
  have hN : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hb := norm_stdAddChar_m_sub_one_sq_ge m hm
  have hN3 : ((2 * m + 1 : ℕ) : ℝ)⁻¹ * ((2 * m + 1 : ℕ) : ℝ) ^ 3 = ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by
    field_simp
  calc 6 * ((2 * m + 1 : ℕ) : ℝ) ^ 2
      = 3 * (((2 * m + 1 : ℕ) : ℝ)⁻¹ * ((2 * m + 1 : ℕ) : ℝ) ^ 3) * 2 := by rw [hN3]; ring
    _ ≤ 3 * (((2 * m + 1 : ℕ) : ℝ)⁻¹ * ((2 * m + 1 : ℕ) : ℝ) ^ 3) *
          ‖ZMod.stdAddChar ((m : ℤ) : ZMod (2 * m + 1)) - 1‖ ^ 2 := by
        gcongr
    _ = _ := by ring

/-- `lem:supp-open-parity`, non-coercivity clause (reformulated with the
coordinate form): there is no constant `c > 0` with `c 𝒟_C(u) ≤ 𝒟_F(u)` for
all odd `N` and all grid functions `u`; the parity test witnesses the failure
at every sufficiently large cutoff. -/
theorem rootDirichlet_not_uniformly_coercive :
    ∀ c : ℝ, 0 < c → ∃ m : ℕ, ∃ u : Grid (2 * m + 1) → ℂ,
      rootDirichlet (2 * m + 1) u < c * coordDirichlet (2 * m + 1) u := by
  intro c hc
  set m : ℕ := ⌈2 * π ^ 2 / c⌉₊ + 1 with hm
  refine ⟨m, parityTest (2 * m + 1) m, ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hF := rootDirichlet_parityTest_le m
  have hC := coordDirichlet_parityTest_ge m hm1
  have hN : (2 * π ^ 2 / c) < ((2 * m + 1 : ℕ) : ℝ) := by
    have h1 : (2 * π ^ 2 / c) ≤ (⌈2 * π ^ 2 / c⌉₊ : ℝ) := Nat.le_ceil _
    rw [hm]
    push_cast
    linarith
  have hN1 : (1 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ 2 * m + 1 := by omega
    exact_mod_cast this
  have hN2 : (2 * π ^ 2 / c) < ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hkey : 12 * π ^ 2 < c * (6 * ((2 * m + 1 : ℕ) : ℝ) ^ 2) := by
    rw [div_lt_iff₀ hc] at hN2
    nlinarith
  calc rootDirichlet (2 * m + 1) (parityTest (2 * m + 1) m) ≤ 12 * π ^ 2 := hF
    _ < c * (6 * ((2 * m + 1 : ℕ) : ℝ) ^ 2) := hkey
    _ ≤ c * coordDirichlet (2 * m + 1) (parityTest (2 * m + 1) m) := by gcongr

/-- `root_parity_obstruction`: the full non-coercivity witness, with the
uniform root-form bound and the growing coordinate form. -/
theorem root_parity_obstruction (m : ℕ) (hm : 1 ≤ m) :
    rootDirichlet (2 * m + 1) (parityTest (2 * m + 1) m) ≤ 12 * π ^ 2 ∧
      6 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≤ coordDirichlet (2 * m + 1) (parityTest (2 * m + 1) m) :=
  ⟨rootDirichlet_parityTest_le m, coordDirichlet_parityTest_ge m hm⟩

/-! ### Root-graph distance from `0` to `e₁` -/

/-- Integer coordinate unit vector. -/
def ε (i : Fin 3) : Fin 3 → ℤ := Pi.single i 1

/-- The twelve `A₃` roots `±(e_i + e_j), ±(e_i - e_j)` (`i ≠ j`) in `ℤ³`
(`eq:supp-open-fcc-roots`). -/
def IsRoot (r : Fin 3 → ℤ) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ (r = ε i + ε j ∨ r = -(ε i + ε j) ∨ r = ε i - ε j)

/-- Every root has even coordinate sum. -/
theorem IsRoot.coordSum_even {r : Fin 3 → ℤ} (h : IsRoot r) : Even (∑ k, r k) := by
  obtain ⟨i, j, hij, h⟩ := h
  rcases h with h | h | h <;> subst h <;> fin_cases i <;> fin_cases j <;>
    first | exact absurd rfl hij | decide

/-- Every root moves each coordinate by at most one. -/
theorem IsRoot.abs_apply_le {r : Fin 3 → ℤ} (h : IsRoot r) (k : Fin 3) : |r k| ≤ 1 := by
  obtain ⟨i, j, hij, h⟩ := h
  rcases h with h | h | h <;> subst h <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | exact absurd rfl hij | decide

/-- Reduction of an integer displacement to the periodic grid. -/
def toGrid (N : ℕ) (v : Fin 3 → ℤ) : Grid N := fun i => (v i : ZMod N)

theorem toGrid_sum (N : ℕ) {ι : Type*} (s : Finset ι) (p : ι → Fin 3 → ℤ) :
    toGrid N (∑ n ∈ s, p n) = ∑ n ∈ s, toGrid N (p n) := by
  funext i
  simp [toGrid, Finset.sum_apply]

/-- Lower bound: a root path of length `ℓ` from `0` whose reduction ends at
`e₁` on the odd grid `N = 2m + 1` has `ℓ ≥ N - 1 = 2m`. -/
theorem root_path_length_ge (m ℓ : ℕ) (p : ℕ → Fin 3 → ℤ) (hp : ∀ n < ℓ, IsRoot (p n))
    (hend : toGrid (2 * m + 1) (∑ n ∈ range ℓ, p n) = e (2 * m + 1) 0) : 2 * m ≤ ℓ := by
  set s : Fin 3 → ℤ := ∑ n ∈ range ℓ, p n with hs
  -- even coordinate sum of the displacement
  have heven : Even (∑ k, s k) := by
    have : ∑ k, s k = ∑ n ∈ range ℓ, ∑ k, p n k := by
      simp only [hs, Finset.sum_apply]
      exact Finset.sum_comm
    rw [this]
    exact Finset.sum_induction _ Even (fun a b ha hb => ha.add hb) ⟨0, by simp⟩
      fun n hn => (hp n (mem_range.mp hn)).coordSum_even
  -- each coordinate is `δ_{k0}` modulo `N`
  have hcoord : ∀ k, ((2 * m + 1 : ℕ) : ℤ) ∣ ε 0 k - s k := by
    intro k
    have h := congrFun hend k
    simp only [toGrid, e] at h
    have h' : ((s k : ℤ) : ZMod (2 * m + 1)) = ((ε 0 k : ℤ) : ZMod (2 * m + 1)) := by
      rw [h]
      simp only [ε, Pi.single_apply]
      split_ifs <;> simp
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h'
  choose z hz using hcoord
  -- parity forces a nonzero `z_k`
  have hsum : ∑ k, s k = 1 - ((2 * m + 1 : ℕ) : ℤ) * ∑ k, z k := by
    have : ∀ k, s k = ε 0 k - ((2 * m + 1 : ℕ) : ℤ) * z k := fun k => by linarith [hz k]
    simp_rw [this]
    rw [sum_sub_distrib, ← mul_sum]
    have h1 : ∑ k : Fin 3, ε 0 k = 1 := by decide
    rw [h1]
  have hodd : Odd (∑ k, z k) := by
    rw [hsum] at heven
    have hN : Odd ((2 * m + 1 : ℕ) : ℤ) := by push_cast; exact odd_two_mul_add_one _
    by_contra hcon
    rw [Int.not_odd_iff_even] at hcon
    have := hcon.mul_left ((2 * m + 1 : ℕ) : ℤ)
    have h1 : Even (1 : ℤ) := by
      have := heven.add this
      simpa using this
    exact Int.not_even_one h1
  obtain ⟨k, hk⟩ : ∃ k, z k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ∑ k, z k = 0 := sum_eq_zero fun k _ => hcon k
    rw [this] at hodd
    exact Int.not_odd_zero hodd
  -- that coordinate has modulus at least `N - 1`
  have hbig : ((2 * m : ℕ) : ℤ) ≤ |s k| := by
    have hz' : s k = ε 0 k - ((2 * m + 1 : ℕ) : ℤ) * z k := by linarith [hz k]
    have hε : |ε 0 k| ≤ 1 := by
      simp only [ε, Pi.single_apply]; split_ifs <;> simp
    have hzk : 1 ≤ |z k| := Int.one_le_abs hk
    have h1 : ((2 * m + 1 : ℕ) : ℤ) * |z k| ≤ |((2 * m + 1 : ℕ) : ℤ) * z k| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((2 * m + 1 : ℕ) : ℤ))]
    have h2 : |((2 * m + 1 : ℕ) : ℤ) * z k| - |ε 0 k| ≤ |s k| := by
      rw [hz']
      have := abs_sub_abs_le_abs_sub (((2 * m + 1 : ℕ) : ℤ) * z k) (ε 0 k)
      rw [abs_sub_comm] at this
      exact this
    push_cast at h1 h2 ⊢
    nlinarith
  -- but each step moves the coordinate by at most one
  have hsmall : |s k| ≤ ℓ := by
    calc |s k| = |∑ n ∈ range ℓ, p n k| := by rw [hs, Finset.sum_apply]
      _ ≤ ∑ n ∈ range ℓ, |p n k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ range ℓ, (1 : ℤ) :=
          sum_le_sum fun n hn => (hp n (mem_range.mp hn)).abs_apply_le k
      _ = ℓ := by simp
  have : ((2 * m : ℕ) : ℤ) ≤ ℓ := hbig.trans hsmall
  exact_mod_cast this

/-- The alternating pair `-e₁ + e₂, -e₁ - e₂` repeated `m` times is a root
path of length `2m = N - 1` from `0` to `e₁` on the odd grid. -/
theorem root_path_exists (m : ℕ) :
    ∃ p : ℕ → Fin 3 → ℤ, (∀ n, IsRoot (p n)) ∧
      toGrid (2 * m + 1) (∑ n ∈ range (2 * m), p n) = e (2 * m + 1) 0 := by
  set a : Fin 3 → ℤ := ε 1 - ε 0 with ha
  set b : Fin 3 → ℤ := -(ε 0 + ε 1) with hb
  refine ⟨fun n => if Even n then a else b, ?_, ?_⟩
  · intro n
    by_cases hn : Even n
    · simp only [hn, if_true]
      exact ⟨1, 0, by decide, Or.inr (Or.inr rfl)⟩
    · simp only [hn, if_false]
      exact ⟨0, 1, by decide, Or.inr (Or.inl rfl)⟩
  · have hsum : ∀ j : ℕ, ∑ n ∈ range (2 * j), (if Even n then a else b) = (j : ℤ) • (a + b) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
        have h1 : Even (2 * j) := even_two_mul j
        have h2 : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)
        simp only [h1, h2, if_true, if_false]
        push_cast
        rw [add_smul, one_smul]
        abel
    rw [hsum m]
    have hab : a + b = (-2 : ℤ) • ε 0 := by
      rw [ha, hb]
      abel
    rw [hab, smul_smul]
    funext k
    simp only [toGrid, e, ε, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    have hN := ZMod.natCast_self (2 * m + 1)
    push_cast at hN
    split_ifs
    · push_cast
      linear_combination -hN
    · simp

/-- `lem:supp-open-parity`, distance clause: the root-graph distance from `0`
to `e₁` on the odd grid `N = 2m + 1` is exactly `N - 1 = 2m`. -/
theorem root_graph_distance (m : ℕ) :
    (∀ (ℓ : ℕ) (p : ℕ → Fin 3 → ℤ), (∀ n < ℓ, IsRoot (p n)) →
      toGrid (2 * m + 1) (∑ n ∈ range ℓ, p n) = e (2 * m + 1) 0 → 2 * m ≤ ℓ) ∧
    ∃ p : ℕ → Fin 3 → ℤ, (∀ n, IsRoot (p n)) ∧
      toGrid (2 * m + 1) (∑ n ∈ range (2 * m), p n) = e (2 * m + 1) 0 :=
  ⟨fun ℓ p hp hend => root_path_length_ge m ℓ p hp hend, root_path_exists m⟩

end RenewalGeometry.RootParityConnector
