/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The pure-deficiency dark-energy algebra (GR_emergence, Phase 1)

The elementary algebra chain of the GR manuscript's deficiency
sector:

* `hubble_deficiency_lambda`, `deficiency_lambda_nonneg`,
  `deficiency_lambda_pos_iff`, `deficiency_lambda_eq_zero_iff` —
  `thm:lambda`, `thm:vacuum-trichotomy`, `cor:sign-dark-energy`;
* `common_origin_gravity_scalar` (+ `_three`, `_k4`) —
  `prop:common-origin-gravity-scalar`;
* `krein_positive_expansion_arrow` —
  `cor:krein-positive-expansion-arrow`;
* `controlled_ds_separation` — `cor:controlled-ds-separation`;
* `deficiency_eos`, `deficiency_eos_exchange`,
  `reconstructed_eos` — `prop:deficiency-eos-identities`;
* `phantom_sign_dictionary` — the sign dictionary of
  `cor:fit-free-crossing-direction`;
* `closed_vacuum_deficiency_nogo` —
  `thm:closed-source-free-deficiency-nogo` (time version);
* `renewal_gap_moment` — `thm:renewal-gap-moment`;
* `microscopic_flatness_bound` — `cor:microscopic-flatness-bound`;
* `wilson_triple_left_inverse` — `prop:conditional-wilson`;
* `worked_channel_structure` — `cor:structure`;
* `ringCGF_hasDerivAt`, `ringCGF_deriv_hasDerivAt`,
  `ring_entropy_production_nonneg` — `constr:dark-energy-ring`;
* `log_ge_two_mul_sub_div_add`, `crossing_entropy_floor` —
  `thm:crossing-entropy-floor` (the ring-model TUR floor);
* `radius_shift_bound` — `prop:six-derivative-radius-shift`;
* `scalar_drift_residual_vanishes` — `cor:tightened`;
* `late_window_ratio_bound` — `prop:late-finite-window-null`.
-/

namespace NCG

open Real

/-! ## `thm:lambda`, `thm:vacuum-trichotomy`, `cor:sign-dark-energy` -/

/-- `thm:lambda`: on the pure-deficiency branch `H = B/d`, the
maximally symmetric vacuum term is `Λ = (d-1)B²/(2d)`. -/
theorem hubble_deficiency_lambda (d B : ℝ) (hd : d ≠ 0) :
    d * (d - 1) / 2 * (B / d) ^ 2 = (d - 1) * B ^ 2 / (2 * d) := by
  field_simp

/-- `cor:sign-dark-energy`: the pure-deficiency vacuum term is
nonnegative — anti-de Sitter is excluded within the ansatz. -/
theorem deficiency_lambda_nonneg (d B : ℝ) (hd : 1 ≤ d) :
    0 ≤ (d - 1) * B ^ 2 / (2 * d) := by
  apply div_nonneg (mul_nonneg (by linarith) (sq_nonneg B))
  linarith

/-- `thm:vacuum-trichotomy` (branch classification): `Λ > 0` exactly
off the Minkowski branch `B = 0`; combined with `lt_trichotomy` on
`B` this is the expanding/Minkowski/contracting trichotomy. -/
theorem deficiency_lambda_pos_iff (d B : ℝ) (hd : 1 < d) :
    0 < (d - 1) * B ^ 2 / (2 * d) ↔ B ≠ 0 := by
  constructor
  · intro h hB
    rw [hB] at h
    simp at h
  · intro hB
    apply div_pos (mul_pos (by linarith) (by positivity))
    linarith

/-- The Minkowski branch: `Λ = 0` iff `B = 0`. -/
theorem deficiency_lambda_eq_zero_iff (d B : ℝ) (hd : 1 < d) :
    (d - 1) * B ^ 2 / (2 * d) = 0 ↔ B = 0 := by
  constructor
  · intro h
    by_contra hB
    exact absurd h (ne_of_gt ((deficiency_lambda_pos_iff d B hd).mpr hB))
  · intro h
    rw [h]
    ring

/-! ## `prop:common-origin-gravity-scalar` -/

/-- `prop:common-origin-gravity-scalar`: with screen entropy density
`η = h/(N ε^{d-1})`, coupling `G = 1/(4η)`, physical current
`B_phys = B c/ε`, and `Λ = (d-1)B_phys²/(2d)`, one has
`GΛ = N (d-1)/(8d) · B²c² ε^{d-3} / h`. -/
theorem common_origin_gravity_scalar (d : ℕ) (hd : 3 ≤ d)
    (N h B c eps : ℝ) (hh : h ≠ 0) (heps : eps ≠ 0) :
    (N * eps ^ (d - 1) / (4 * h))
      * (((d : ℝ) - 1) * (B * c / eps) ^ 2 / (2 * d))
    = N * ((d : ℝ) - 1) / (8 * d) * (B ^ 2 * c ^ 2) * eps ^ (d - 3) / h := by
  have hpow : eps ^ (d - 1) = eps ^ (d - 3) * eps ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

/-- The `d = 3`, unit-speed endpoint: `GΛ = N B²/(12 h)`. -/
theorem common_origin_gravity_scalar_three (N h B eps : ℝ)
    (hh : h ≠ 0) (heps : eps ≠ 0) :
    (N * eps ^ 2 / (4 * h)) * (2 * (B / eps) ^ 2 / 6)
      = N * B ^ 2 / (12 * h) := by
  field_simp
  ring

/-- The normalized predictive-pure uniform `K₄` screen
(`N = 1`, `h = log 3`): `GΛ = B²/(12 log 3)`. -/
theorem common_origin_gravity_scalar_k4 (B eps : ℝ) (heps : eps ≠ 0) :
    (1 * eps ^ 2 / (4 * Real.log 3)) * (2 * (B / eps) ^ 2 / 6)
      = B ^ 2 / (12 * Real.log 3) := by
  have h3 : Real.log 3 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 3)
    linarith
  field_simp
  ring

/-! ## `cor:krein-positive-expansion-arrow` -/

/-- `cor:krein-positive-expansion-arrow`: with `sinh χ* = Bε`,
`ε > 0`, the expanding branch `B > 0`, the positive rapidity
`χ* > 0`, and the positive bridge displacement `1 - e^{-2χ*} > 0`
are all equivalent. -/
theorem krein_positive_expansion_arrow (B eps chi : ℝ) (heps : 0 < eps)
    (h : Real.sinh chi = B * eps) :
    (0 < B ↔ 0 < chi) ∧ (0 < chi ↔ 0 < 1 - Real.exp (-(2 * chi))) := by
  constructor
  · constructor
    · intro hB
      have h1 : Real.sinh 0 < Real.sinh chi := by
        rw [Real.sinh_zero, h]
        positivity
      exact Real.sinh_lt_sinh.mp h1
    · intro hc
      have h1 : Real.sinh 0 < Real.sinh chi := Real.sinh_lt_sinh.mpr hc
      rw [Real.sinh_zero, h] at h1
      nlinarith
  · rw [sub_pos, ← Real.exp_zero, Real.exp_lt_exp]
    constructor <;> intro <;> linarith

/-! ## `cor:controlled-ds-separation` -/

/-- `cor:controlled-ds-separation`: with `H = B/d` and
`L_dS = d/B`, the control condition `Hε < δ` is exactly
`ε/L_dS < δ` — `B` fixes the infrared curvature scale, `ε` the
ultraviolet boundary. -/
theorem controlled_ds_separation (B d eps delta : ℝ)
    (hB : B ≠ 0) (hd : d ≠ 0) :
    B / d * eps < delta ↔ eps / (d / B) < delta := by
  have h1 : eps / (d / B) = B / d * eps := by
    field_simp
  rw [h1]

/-! ## `prop:deficiency-eos-identities` -/

/-- `prop:deficiency-eos-identities`(i): for a separately conserved
deficiency fluid `ρ_B = c B²` (conservation
`ρ̇ + dH(ρ + p) = 0` with `ρ̇ = 2cBḂ`), the equation of state is
`w_B = -1 - 2Ḃ/(dHB)`. -/
theorem deficiency_eos (c d H Bv B' p : ℝ)
    (hc : c ≠ 0) (hB : Bv ≠ 0) (hH : H ≠ 0) (hd : d ≠ 0)
    (hcons : 2 * c * Bv * B' + d * H * (c * Bv ^ 2 + p) = 0) :
    p / (c * Bv ^ 2) = -1 - 2 * B' / (d * H * Bv) := by
  have hp : p = -(c * Bv ^ 2) - 2 * c * Bv * B' / (d * H) := by
    field_simp
    linear_combination hcons
  rw [hp]
  field_simp

/-- `prop:deficiency-eos-identities`(ii): with an exchange source
`Q` (`ρ̇_B + dH(ρ_B + p_B) = Q`), the physical pressure ratio picks
up the extra term `Q/(dHcB²)`. -/
theorem deficiency_eos_exchange (c d H Bv B' p Q : ℝ)
    (hc : c ≠ 0) (hB : Bv ≠ 0) (hH : H ≠ 0) (hd : d ≠ 0)
    (hcons : 2 * c * Bv * B' + d * H * (c * Bv ^ 2 + p) = Q) :
    p / (c * Bv ^ 2)
      = -1 - 2 * B' / (d * H * Bv) + Q / (d * H * (c * Bv ^ 2)) := by
  have hp : p = -(c * Bv ^ 2) - 2 * c * Bv * B' / (d * H) + Q / (d * H) := by
    field_simp
    linear_combination hcons
  rw [hp]
  field_simp

/-- `prop:deficiency-eos-identities`(ii), reconstructed value: an
observer assuming no interaction infers
`w_rec = -1 - ρ̇/(dHρ) = -1 - 2Ḃ/(dHB)` regardless of the exchange
term. -/
theorem reconstructed_eos (c d H Bv B' : ℝ)
    (hc : c ≠ 0) (hB : Bv ≠ 0) (hH : H ≠ 0) (hd : d ≠ 0) :
    -1 - (2 * c * Bv * B') / (d * H * (c * Bv ^ 2))
      = -1 - 2 * B' / (d * H * Bv) := by
  field_simp

/-- Sign dictionary for `cor:fit-free-crossing-direction`: on an
expanding branch (`d, H, B > 0`) the reconstructed state is phantom
(`w_rec < -1`) exactly when `Ḃ > 0`; hence a `+ → -` sign change of
`Ḃ` is a `w_rec < -1 → w_rec > -1` crossing, and the reverse
crossing is excluded. -/
theorem phantom_sign_dictionary (d H Bv B' : ℝ)
    (hd : 0 < d) (hH : 0 < H) (hB : 0 < Bv) :
    -1 - 2 * B' / (d * H * Bv) < -1 ↔ 0 < B' := by
  have hden : 0 < d * H * Bv := by positivity
  constructor
  · intro h
    have ht : 0 < 2 * B' / (d * H * Bv) := by linarith
    have h2 : 0 < 2 * B' := by
      have := mul_pos ht hden
      rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at this
    linarith
  · intro h
    have : 0 < 2 * B' / (d * H * Bv) := by positivity
    linarith

/-! ## `thm:closed-source-free-deficiency-nogo` -/

/-- `thm:closed-source-free-deficiency-nogo` (time version): if the
vacuum-deficiency contribution `Λ(B) ∝ B²` is conserved
(`B·Ḃ = 0` everywhere) and `B` never vanishes, then `B` is
constant — the only nonzero closed homogeneous endpoint is the
cosmological-constant branch `w = -1`. -/
theorem closed_vacuum_deficiency_nogo {B : ℝ → ℝ}
    (hB : Differentiable ℝ B)
    (hcons : ∀ t, B t * deriv B t = 0)
    (hne : ∀ t, B t ≠ 0) :
    ∀ s t : ℝ, B s = B t := by
  have hz : ∀ t, deriv B t = 0 := by
    intro t
    rcases mul_eq_zero.mp (hcons t) with h | h
    · exact absurd h (hne t)
    · exact h
  intro s t
  exact is_const_of_deriv_eq_zero hB hz s t

/-! ## `thm:renewal-gap-moment` -/

/-- `thm:renewal-gap-moment`: for spectral weights `w ≥ 0` and rates
`μ ≥ g > 0`, the normalized response moment
`T₂ = 2 Σ w μ⁻³ / Σ w μ⁻¹` obeys `0 ≤ T₂ ≤ 2/g²`. -/
theorem renewal_gap_moment {ι : Type*} (s : Finset ι) (w mu : ι → ℝ)
    (g : ℝ) (hg : 0 < g)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmu : ∀ i ∈ s, g ≤ mu i)
    (hpos : 0 < ∑ i ∈ s, w i / mu i) :
    0 ≤ 2 * (∑ i ∈ s, w i / mu i ^ 3) / ∑ i ∈ s, w i / mu i ∧
    2 * (∑ i ∈ s, w i / mu i ^ 3) / ∑ i ∈ s, w i / mu i ≤ 2 / g ^ 2 := by
  have hnum : 0 ≤ ∑ i ∈ s, w i / mu i ^ 3 := by
    apply Finset.sum_nonneg
    intro i hi
    have hmi : 0 < mu i := lt_of_lt_of_le hg (hmu i hi)
    exact div_nonneg (hw i hi) (by positivity)
  have hterm : ∀ i ∈ s, w i / mu i ^ 3 ≤ (1 / g ^ 2) * (w i / mu i) := by
    intro i hi
    have hmi : 0 < mu i := lt_of_lt_of_le hg (hmu i hi)
    have hsq : g ^ 2 ≤ mu i ^ 2 := by nlinarith [hmu i hi]
    have hstep : w i / mu i ^ 3 = (w i / mu i) * (1 / mu i ^ 2) := by
      field_simp
    rw [hstep, mul_comm (1 / g ^ 2)]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (hw i hi) hmi.le)
    exact one_div_le_one_div_of_le (by positivity) hsq
  constructor
  · exact div_nonneg (by linarith) hpos.le
  · rw [div_le_iff₀ hpos]
    have hsum : ∑ i ∈ s, w i / mu i ^ 3
        ≤ (1 / g ^ 2) * ∑ i ∈ s, w i / mu i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    calc 2 * (∑ i ∈ s, w i / mu i ^ 3)
        ≤ 2 * ((1 / g ^ 2) * ∑ i ∈ s, w i / mu i) := by linarith
      _ = 2 / g ^ 2 * (∑ i ∈ s, w i / mu i) := by ring

/-! ## `cor:microscopic-flatness-bound` -/

/-- `cor:microscopic-flatness-bound`: with the factorized Wilson
coefficients `cᵢ = A Ĉᵢ T₂` and the spectral-gap bound
`0 ≤ T₂ ≤ 2/g²`, the flatness combination obeys
`|6c₁ + 2c₂| ≤ (2|A|/g²)·|6Ĉ₁ + 2Ĉ₂|`. -/
theorem microscopic_flatness_bound (A C1 C2 T2 g : ℝ) (_hg : 0 < g)
    (hT0 : 0 ≤ T2) (hT : T2 ≤ 2 / g ^ 2) :
    |6 * (A * C1 * T2) + 2 * (A * C2 * T2)|
      ≤ 2 * |A| / g ^ 2 * |6 * C1 + 2 * C2| := by
  have h1 : 6 * (A * C1 * T2) + 2 * (A * C2 * T2)
      = A * (6 * C1 + 2 * C2) * T2 := by ring
  rw [h1, abs_mul, abs_mul, abs_of_nonneg hT0]
  calc |A| * |6 * C1 + 2 * C2| * T2
      ≤ |A| * |6 * C1 + 2 * C2| * (2 / g ^ 2) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = 2 * |A| / g ^ 2 * |6 * C1 + 2 * C2| := by ring

/-! ## `prop:conditional-wilson` -/

/-- `prop:conditional-wilson`: the cumulant-to-Wilson map
`(κR, κS, κC) ↦ Gλ²·(κR - κS/4, κS, κC)` is invertible — the
displayed formulas recover the cumulant coordinates. -/
theorem wilson_triple_left_inverse (G lam kR kS kC : ℝ)
    (h : G * lam ^ 2 ≠ 0) :
    (G * lam ^ 2 * kS) / (G * lam ^ 2) = kS ∧
    (G * lam ^ 2 * (kR - kS / 4)) / (G * lam ^ 2)
      + ((G * lam ^ 2 * kS) / (G * lam ^ 2)) / 4 = kR ∧
    (G * lam ^ 2 * kC) / (G * lam ^ 2) = kC := by
  refine ⟨mul_div_cancel_left₀ _ h, ?_, mul_div_cancel_left₀ _ h⟩
  rw [mul_div_cancel_left₀ _ h, mul_div_cancel_left₀ _ h]
  ring

/-! ## `cor:structure` -/

/-- `cor:structure`: on the worked-channel ray
`(κR, κS, κC) = t·(5/3, 5/3, -1/4)` (`t = Gλ²Q/D² > 0`): equal
scalar and traceless-Ricci weight, Weyl ratio `-3/20`, and positive
Starobinsky-stable scalar coefficient `c₁ = (5/4)t`. -/
theorem worked_channel_structure (t : ℝ) (ht : 0 < t) :
    (t * (-(1 / 4))) / (t * (5 / 3)) = -(3 / 20) ∧
    t * (5 / 3) - t * (5 / 3) / 4 = 5 / 4 * t ∧
    0 < t * (5 / 3) - t * (5 / 3) / 4 := by
  refine ⟨?_, by ring, by linarith⟩
  rw [mul_div_mul_left _ _ (ne_of_gt ht)]
  norm_num

/-! ## `constr:dark-energy-ring` -/

/-- The tilted scaled cumulant-generating function of the three-state
exchange ring. -/
noncomputable def ringCGF (k k' chi : ℝ) : ℝ :=
  k * Real.exp chi + k' * Real.exp (-chi) - (k + k')

/-- First derivative at the origin: the oriented count rate
`λ_Q'(0) = k - k' = Q̇`. -/
theorem ringCGF_hasDerivAt (k k' : ℝ) :
    HasDerivAt (ringCGF k k') (k - k') 0 := by
  unfold ringCGF
  have h1 : HasDerivAt (fun chi : ℝ => k * Real.exp chi)
      (k * Real.exp 0) 0 := (Real.hasDerivAt_exp 0).const_mul k
  have h2 : HasDerivAt (fun chi : ℝ => Real.exp (-chi))
      (Real.exp (-(0:ℝ)) * (-1)) 0 := ((hasDerivAt_id (0:ℝ)).neg).exp
  have h3 := (h1.add (h2.const_mul k')).sub_const (k + k')
  have h4 : k * Real.exp 0 + k' * (Real.exp (-(0:ℝ)) * (-1)) = k - k' := by
    simp only [neg_zero, Real.exp_zero, mul_one, mul_neg_one]
    ring
  rw [← h4]
  exact h3

/-- Second derivative at the origin: the count variance
`λ_Q''(0) = k + k'`. -/
theorem ringCGF_deriv_hasDerivAt (k k' : ℝ) :
    HasDerivAt (fun chi => k * Real.exp chi - k' * Real.exp (-chi))
      (k + k') 0 := by
  have h1 : HasDerivAt (fun chi : ℝ => k * Real.exp chi)
      (k * Real.exp 0) 0 := (Real.hasDerivAt_exp 0).const_mul k
  have h2 : HasDerivAt (fun chi : ℝ => Real.exp (-chi))
      (Real.exp (-(0:ℝ)) * (-1)) 0 := ((hasDerivAt_id (0:ℝ)).neg).exp
  have h3 := h1.sub (h2.const_mul k')
  have h4 : k * Real.exp 0 - k' * (Real.exp (-(0:ℝ)) * (-1)) = k + k' := by
    simp only [neg_zero, Real.exp_zero, mul_one, mul_neg_one]
    ring
  rw [← h4]
  exact h3

/-- Entropy production of the ring is nonnegative:
`σ_ep = (k - k')·log(k/k') ≥ 0`, vanishing exactly at the reversible
locus. -/
theorem ring_entropy_production_nonneg (k k' : ℝ)
    (hk : 0 < k) (hk' : 0 < k') :
    0 ≤ (k - k') * Real.log (k / k') := by
  rcases le_total k' k with h | h
  · apply mul_nonneg (by linarith)
    apply Real.log_nonneg
    rw [le_div_iff₀ hk']
    linarith
  · apply mul_nonneg_iff.mpr
    right
    constructor
    · linarith
    · apply Real.log_nonpos (by positivity)
      rw [div_le_one hk']
      exact h

/-! ## `thm:crossing-entropy-floor` -/

/-- The Padé bound `log x ≥ 2(x-1)/(x+1)` for `x ≥ 1`. -/
theorem log_ge_two_mul_sub_div_add {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  set F : ℝ → ℝ := fun y => Real.log y + 4 / (y + 1) with hFdef
  have hderiv : ∀ y ∈ Set.Ioi (1:ℝ),
      HasDerivAt F (y⁻¹ + (0 * (y + 1) - 4 * 1) / (y + 1) ^ 2) y := by
    intro y hy
    have hy0 : (0:ℝ) < y := lt_trans one_pos hy
    have h1 : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log (ne_of_gt hy0)
    have h2 : HasDerivAt (fun z : ℝ => z + 1) 1 y :=
      (hasDerivAt_id y).add_const 1
    have h3 : HasDerivAt (fun z : ℝ => 4 / (z + 1))
        ((0 * (y + 1) - 4 * 1) / (y + 1) ^ 2) y :=
      (hasDerivAt_const y 4).div h2 (by positivity)
    exact h1.add h3
  have hmono : MonotoneOn F (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · apply ContinuousOn.add
      · intro y hy
        have : (1:ℝ) ≤ y := hy
        exact (Real.continuousAt_log (by linarith)).continuousWithinAt
      · apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro y hy
        have : (1:ℝ) ≤ y := hy
        linarith
    · intro y hy
      rw [interior_Ici] at hy
      exact ((hderiv y hy).differentiableAt).differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hderiv y hy).deriv]
      have hy0 : (0:ℝ) < y := lt_trans one_pos hy
      have heqd : y⁻¹ + (0 * (y + 1) - 4 * 1) / (y + 1) ^ 2
          = (y - 1) ^ 2 / (y * (y + 1) ^ 2) := by
        field_simp
        ring
      rw [heqd]
      positivity
  have h1 : Real.log 1 + 4 / (1 + 1) ≤ Real.log x + 4 / (x + 1) :=
    hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rw [Real.log_one] at h1
  norm_num at h1
  have hx1 : (0:ℝ) < x + 1 := by linarith
  have h2 : 2 * (x - 1) / (x + 1) = 2 - 4 / (x + 1) := by
    field_simp
    ring
  rw [h2]
  linarith

/-- Helper: `2(a-b)/(a+b) ≤ log a - log b` for `0 < b ≤ a`. -/
theorem two_mul_sub_div_add_le_log_sub {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    2 * (a - b) / (a + b) ≤ Real.log a - Real.log b := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hx : 1 ≤ a / b := (one_le_div hb).mpr hab
  have h := log_ge_two_mul_sub_div_add hx
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at h
  have hab' : (0:ℝ) < a + b := by linarith
  have hb' : b ≠ 0 := ne_of_gt hb
  have hs : a + b ≠ 0 := ne_of_gt hab'
  have heq : 2 * (a / b - 1) / (a / b + 1) = 2 * (a - b) / (a + b) := by
    rw [div_sub_one hb', div_add_one hb', ← mul_div_assoc,
      div_div_div_cancel_right₀]
    exact hb'
  rw [heq] at h
  exact h

/-- `thm:crossing-entropy-floor` (core inequality; the ring-model
thermodynamic uncertainty relation): for jump rates `k, k' > 0`, the
entropy production dominates twice the squared current over the
variance: `σ_ep = (k-k')log(k/k') ≥ 2(k-k')²/(k+k') = 2Q̇²/Var(Q̇)`.
In particular zero entropy production forbids an exchange-driven
crossing. -/
theorem crossing_entropy_floor (k k' : ℝ) (hk : 0 < k) (hk' : 0 < k') :
    2 * (k - k') ^ 2 / (k + k') ≤ (k - k') * Real.log (k / k') := by
  rw [Real.log_div (ne_of_gt hk) (ne_of_gt hk')]
  rcases le_total k' k with h | h
  · have hlog := two_mul_sub_div_add_le_log_sub hk' h
    have hd : 0 ≤ k - k' := by linarith
    calc 2 * (k - k') ^ 2 / (k + k')
        = (k - k') * (2 * (k - k') / (k + k')) := by ring
      _ ≤ (k - k') * (Real.log k - Real.log k') :=
          mul_le_mul_of_nonneg_left hlog hd
  · have hlog := two_mul_sub_div_add_le_log_sub hk h
    have hd : 0 ≤ k' - k := by linarith
    calc 2 * (k - k') ^ 2 / (k + k')
        = (k' - k) * (2 * (k' - k) / (k' + k)) := by ring
      _ ≤ (k' - k) * (Real.log k' - Real.log k) :=
          mul_le_mul_of_nonneg_left hlog hd
      _ = (k - k') * (Real.log k - Real.log k') := by ring

/-! ## `prop:six-derivative-radius-shift` -/

/-- `prop:six-derivative-radius-shift` (quantitative): if
`x = q(4Λ + x)³` (`q = 16πGε⁴b_dS ≥ 0`) is the constant-curvature
radius shift with the a-priori bound `|x| ≤ Λ`, then `x` equals its
leading value `64qΛ³` up to `O(q²Λ⁵) = O(ε⁸)`; dividing by `4Λ`,
`δR/(4Λ) = 256πGε⁴ b_dS Λ² + O(ε⁸)`, so the sign of the leading
radius shift is the sign of `b_dS`. -/
theorem radius_shift_bound (q L x : ℝ) (hL : 0 < L) (hq : 0 ≤ q)
    (hx : x = q * (4 * L + x) ^ 3) (hxb : |x| ≤ L) :
    |x - 64 * q * L ^ 3| ≤ 7625 * q ^ 2 * L ^ 5 := by
  have hxb' := abs_le.mp hxb
  have habs : |4 * L + x| ≤ 5 * L := by
    rw [abs_le]
    constructor <;> nlinarith [hxb'.1, hxb'.2]
  have hxsmall : |x| ≤ 125 * q * L ^ 3 := by
    rw [hx, abs_mul, abs_of_nonneg hq, abs_pow]
    calc q * |4 * L + x| ^ 3 ≤ q * (5 * L) ^ 3 := by
          apply mul_le_mul_of_nonneg_left _ hq
          exact pow_le_pow_left₀ (abs_nonneg _) habs 3
      _ = 125 * q * L ^ 3 := by ring
  have hfact : x - 64 * q * L ^ 3
      = q * x * ((4 * L + x) ^ 2 + (4 * L + x) * (4 * L) + (4 * L) ^ 2) := by
    conv_lhs => rw [hx]
    ring
  have h1 : |(4 * L + x) ^ 2| ≤ 25 * L ^ 2 := by
    rw [abs_pow]
    calc |4 * L + x| ^ 2 ≤ (5 * L) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 25 * L ^ 2 := by ring
  have h2 : |(4 * L + x) * (4 * L)| ≤ 20 * L ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * L)]
    calc |4 * L + x| * (4 * L) ≤ 5 * L * (4 * L) := by
          apply mul_le_mul_of_nonneg_right habs (by positivity)
      _ = 20 * L ^ 2 := by ring
  have h3 : |(4 * L) ^ 2| = 16 * L ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    ring
  have hbr : |(4 * L + x) ^ 2 + (4 * L + x) * (4 * L) + (4 * L) ^ 2|
      ≤ 61 * L ^ 2 := by
    calc |(4 * L + x) ^ 2 + (4 * L + x) * (4 * L) + (4 * L) ^ 2|
        ≤ |(4 * L + x) ^ 2| + |(4 * L + x) * (4 * L)| + |(4 * L) ^ 2| :=
          abs_add_three _ _ _
      _ ≤ 25 * L ^ 2 + 20 * L ^ 2 + 16 * L ^ 2 := by linarith [h3.le]
      _ = 61 * L ^ 2 := by ring
  rw [hfact, abs_mul, abs_mul, abs_of_nonneg hq]
  calc q * |x| * |(4 * L + x) ^ 2 + (4 * L + x) * (4 * L) + (4 * L) ^ 2|
      ≤ q * (125 * q * L ^ 3) * (61 * L ^ 2) := by
        apply mul_le_mul _ hbr (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hxsmall hq
    _ = 7625 * q ^ 2 * L ^ 5 := by ring

/-! ## `cor:tightened`, `prop:late-finite-window-null` -/

/-- `cor:tightened`: the scalar-drift residual `O(τ‖κ_ren + V‖)`
vanishes with the diamond size `τ → 0` — it never competes with the
leading curvature signal, so the reversible-isotropic restriction
can be deleted. -/
theorem scalar_drift_residual_vanishes (C : ℝ) :
    Filter.Tendsto (fun tau : ℝ => tau * C) (nhds 0) (nhds 0) := by
  have h : Filter.Tendsto (fun tau : ℝ => tau * C) (nhds 0) (nhds (0 * C)) :=
    (continuous_id.mul continuous_const).tendsto 0
  simpa using h

/-- `prop:late-finite-window-null`: if the local finite-window
correction is bounded by `ε²·C·(H² + |Ḣ|)` and the Einstein term has
size `E > 0`, the relative departure is at most
`ε²C(H² + |Ḣ|)/E` — an order-one late-time departure from `w = -1`
cannot be generated by the ultraviolet finite-window operators while
the renewal expansion is controlled. -/
theorem late_window_ratio_bound (corr E eps C H Hdot : ℝ)
    (hE : 0 < E)
    (hcorr : |corr| ≤ eps ^ 2 * C * (H ^ 2 + |Hdot|)) :
    |corr| / E ≤ eps ^ 2 * C * (H ^ 2 + |Hdot|) / E := by
  gcongr

end NCG
