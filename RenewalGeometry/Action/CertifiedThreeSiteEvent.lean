/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactThreeSiteGrid

/-!
# The certified `N = 3`, `h = 1/3` event: exact symbolic data
  (`eq:supp-certified-axial-polarizations`, `eq:supp-certified-mixed-waves`,
  `eq:supp-certified-mixed-polarizations`, `eq:supp-certified-mixed-profile`,
  `eq:supp-certified-ten-field`, `eq:supp-certified-calibration`, `eq:supp-certified-root-box`,
  `eq:supp-exact-balanced-family`; emergent-spacetime manuscript, subsection
  `subsec:supp-exact-certified-rapid`)

Exact encoding (over `ℝ`, with `√3` symbolic) of the data that define the certified prepared
event of the unchanged `N = 3` action on `Λ₃ = (ℤ/3)³` (`ExactThreeSite.Site`,
`δ_i = 3(S_i − S_i⁻¹)` is `ExactThreeSite.phaseDeriv`):

* the axial polarizations `T_i` (unit entries in the two off-diagonal positions transverse to
  axis `i`) and `P_1 = diag(0,1,−1)`, `P_2 = diag(1,0,−1)`, `P_3 = diag(1,−1,0)`; the axial
  profiles `f_i(n) = cos(2πn_i/3)`;
* the four mixed waves `k_1 = (1,1,0)`, `k_2 = (1,0,1)`, `k_3 = (0,1,1)`, `k_4 = (1,−1,0)`, their
  vectors `v_k = k_j e_i − k_i e_j`, `w_k = e_m`, polarizations `T_k = v wᵀ + w vᵀ`,
  `Q_k = v vᵀ − 2 w wᵀ`, and profiles `φ_k(n) = cos(2πk·n/3) + sin(2πk·n/3)/√3`;
* the ten-profile synthesis `U(q)`, `p_R(q)`, `p = √3 p_R` with `α₁ = 1`, the calibration
  `d₁(q)`, `d₂ = −43544048601/5·10⁹`, the rational centre `q_c` and the root box
  `𝓑_* = {‖q − q_c‖_∞ ≤ 10⁻⁴⁰}`.

Proved facts: the stated profile values (`f_i` takes `(1, −1/2, −1/2)`, `φ_k` takes the exact
values `(1, 0, −1)`; `axialProfile_values`, `mixedProfileVal_values`), `ω = 2N sin(π/N) = 3√3`
at `N = 3` (`omega_three`), the polarization facts of `eq:supp-exact-balanced-family` (`T_i ⊥ P_i`
in Frobenius pairing, equal Frobenius norms `2`; `frob_axialT_axialP`, `frob_axialT_self`,
`frob_axialP_self`), trace-freeness of all polarizations, and that the calibration denominator
`d₂ + d₃` is negative on the whole box (`calib_den_neg`), so `d₁` is a well-defined rational
function on `𝓑_*`.

Not encoded (not stated in the manuscript in a computable form): the seven
preparation/Fredholm equations whose root `q_*` the box encloses, the quadratic tilt `ℓ_*`, and
every derivative of the canonical Hamiltonian at `Y(q_*)` (in particular `K_g`, `D_W`, `B_W`).
-/

namespace RenewalGeometry
namespace CertifiedThreeSiteEvent

open ExactThreeSite Matrix

noncomputable section

/-- `M3 = 3 × 3` real matrices (spatial tensors). -/
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

/-- The axial transverse off-diagonal tensor `T_i`. -/
def axialT (i : Fin 3) : M3 := fun a b => if a ≠ b ∧ a ≠ i ∧ b ≠ i then 1 else 0

/-- The axial diagonal polarizations `P_1 = diag(0,1,−1)`, `P_2 = diag(1,0,−1)`,
`P_3 = diag(1,−1,0)` (`eq:supp-certified-axial-polarizations`). -/
def axialP : Fin 3 → M3 :=
  ![diagonal ![0, 1, -1], diagonal ![1, 0, -1], diagonal ![1, -1, 0]]

/-- The Frobenius pairing `⟨A, B⟩ = Σ A_ab B_ab`. -/
def frob (A B : M3) : ℝ := ∑ a, ∑ b, A a b * B a b

/-- The axial profile `f_i(n) = cos(2π n_i / 3)`. -/
def axialProfile (i : Fin 3) (n : Site) : ℝ := Real.cos (2 * Real.pi * ((n i).val : ℝ) / 3)

/-- The mixed wave vectors `k_1, …, k_4` (`eq:supp-certified-mixed-waves`). -/
def mixedK : Fin 4 → Fin 3 → ℤ := ![![1, 1, 0], ![1, 0, 1], ![0, 1, 1], ![1, -1, 0]]

/-- `v_k = k_j e_i − k_i e_j` (`i < j` the nonzero coordinates of `k`):
`(1,−1,0)`, `(1,0,−1)`, `(0,1,−1)`, `(−1,−1,0)`. -/
def mixedV : Fin 4 → Fin 3 → ℝ := ![![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, -1, 0]]

/-- `w_k = e_m` (`m` the remaining index): `e_3`, `e_2`, `e_1`, `e_3`. -/
def mixedW : Fin 4 → Fin 3 → ℝ := ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0], ![0, 0, 1]]

/-- `T_k = v_k w_kᵀ + w_k v_kᵀ` (`eq:supp-certified-mixed-polarizations`). -/
def mixedT (r : Fin 4) : M3 := vecMulVec (mixedV r) (mixedW r) + vecMulVec (mixedW r) (mixedV r)

/-- `Q_k = v_k v_kᵀ − 2 w_k w_kᵀ` (`eq:supp-certified-mixed-polarizations`). -/
def mixedQ (r : Fin 4) : M3 := vecMulVec (mixedV r) (mixedV r) - 2 • vecMulVec (mixedW r) (mixedW r)

/-- The profile value `cos(2πj/3) + sin(2πj/3)/√3`. -/
def mixedProfileVal (j : ℕ) : ℝ :=
  Real.cos (2 * Real.pi * j / 3) + Real.sin (2 * Real.pi * j / 3) / Real.sqrt 3

/-- The mixed profile `φ_k(n) = cos(2πk·n/3) + sin(2πk·n/3)/√3` (`eq:supp-certified-mixed-profile`),
evaluated on the residue `k·n ∈ ℤ/3`. -/
def mixedProfile (r : Fin 4) (n : Site) : ℝ :=
  mixedProfileVal ((∑ a, ((mixedK r a : ℤ) : ZMod 3) * n a).val)

/-- The seven chart coordinates `q = (ξ₁, ξ₂, ξ₃, ξ₄, α₂, α₃, d₃)`. -/
structure ChartPt where
  /-- the mixed amplitudes `ξ_r` -/
  xi : Fin 4 → ℝ
  /-- `α₂` -/
  alpha2 : ℝ
  /-- `α₃` -/
  alpha3 : ℝ
  /-- `d₃` -/
  d3 : ℝ

/-- The fixed calibration constant `d₂ = −43544048601/5000000000`. -/
def d2 : ℚ := -43544048601 / 5000000000

/-- The axial amplitudes `(α₁, α₂, α₃) = (1, α₂, α₃)`. -/
def alphaVec (q : ChartPt) : Fin 3 → ℝ := ![1, q.alpha2, q.alpha3]

/-- The calibration `d₁(q) = (¼(1 + α₂² + α₃²) + (4/3)Σ ξ_r² − d₂d₃)/(d₂ + d₃)`
(`eq:supp-certified-calibration`). -/
def d1 (q : ChartPt) : ℝ :=
  ((1 + q.alpha2 ^ 2 + q.alpha3 ^ 2) / 4 + 4 / 3 * ∑ r, q.xi r ^ 2 - (d2 : ℝ) * q.d3)
    / ((d2 : ℝ) + q.d3)

/-- The diagonal amplitudes `(d₁, d₂, d₃)`. -/
def dVec (q : ChartPt) : Fin 3 → ℝ := ![d1 q, d2, q.d3]

/-- **The ten-profile first field** `U = Σ_i α_i T_i f_i + Σ_r ξ_r T_{k_r} φ_{k_r}`
(`eq:supp-certified-ten-field`). -/
def fieldU (q : ChartPt) (n : Site) : M3 :=
  ∑ i, (alphaVec q i * axialProfile i n) • axialT i + ∑ r, (q.xi r * mixedProfile r n) • mixedT r

/-- **The reduced momentum** `p_R = 3(diag(d) − (Σd) I) + (3/2)Σ α_i P_i f_i
+ (3/2)Σ ξ_r Q_{k_r} φ_{k_r}` (`eq:supp-certified-ten-field`). -/
def momR (q : ChartPt) (n : Site) : M3 :=
  (3 : ℝ) • (diagonal (dVec q) - (∑ i, dVec q i) • (1 : M3))
    + ∑ i, ((3 / 2 : ℝ) * alphaVec q i * axialProfile i n) • axialP i
    + ∑ r, ((3 / 2 : ℝ) * q.xi r * mixedProfile r n) • mixedQ r

/-- The physical momentum `p = √3 p_R`. -/
def mom (q : ChartPt) (n : Site) : M3 := Real.sqrt 3 • momR q n

/-- The rational centre `q_c` (each terminating decimal is the exact rational). -/
def centre : ChartPt where
  xi := ![(1400959084176856057974567007441966391629696585723 : ℚ) / 10 ^ 50,
          (-6670489748267782012274481444791177741880525540001 : ℚ) / 10 ^ 50,
          (-14112980566976204815602958227436097020231483266058 : ℚ) / 10 ^ 50,
          (17215742625921464595401418943881609717177416130840 : ℚ) / 10 ^ 50]
  alpha2 := ((118861735067592515913699417669956560893857219610030 : ℚ) / 10 ^ 50 : ℚ)
  alpha3 := ((113194679076910720016041060163499890274825493906714 : ℚ) / 10 ^ 50 : ℚ)
  d3 := ((-781058367048738968959916622423363949380428649561582 : ℚ) / 10 ^ 50 : ℚ)

/-- The sup-distance on chart points. -/
def InBox (q : ChartPt) : Prop :=
  (∀ r, |q.xi r - centre.xi r| ≤ 1 / 10 ^ 40) ∧ |q.alpha2 - centre.alpha2| ≤ 1 / 10 ^ 40 ∧
    |q.alpha3 - centre.alpha3| ≤ 1 / 10 ^ 40 ∧ |q.d3 - centre.d3| ≤ 1 / 10 ^ 40

/-! ### Facts -/

theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; ring

theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem cos_four_pi_div_three : Real.cos (2 * Real.pi * 2 / 3) = -1 / 2 := by
  have : 2 * Real.pi * 2 / 3 = Real.pi / 3 + Real.pi := by ring
  rw [this, Real.cos_add_pi, Real.cos_pi_div_three]; ring

theorem sin_four_pi_div_three : Real.sin (2 * Real.pi * 2 / 3) = -(Real.sqrt 3 / 2) := by
  have : 2 * Real.pi * 2 / 3 = Real.pi / 3 + Real.pi := by ring
  rw [this, Real.sin_add_pi, Real.sin_pi_div_three]

/-- `f_i` takes the values `(1, −1/2, −1/2)` along its axis. -/
theorem axialProfile_values (i : Fin 3) (n : Site) :
    axialProfile i n = if (n i).val = 0 then 1 else -1 / 2 := by
  unfold axialProfile
  have hv : (n i).val < 3 := ZMod.val_lt (n i)
  interval_cases h : (n i).val
  · simp
  · simp only [Nat.cast_one, mul_one, one_ne_zero, if_false]; exact cos_two_pi_div_three
  · simp only [Nat.cast_ofNat, OfNat.ofNat_ne_zero, if_false]; exact cos_four_pi_div_three

/-- `φ_k` takes the exact values `(1, 0, −1)` along its wave coordinate. -/
theorem mixedProfileVal_values :
    mixedProfileVal 0 = 1 ∧ mixedProfileVal 1 = 0 ∧ mixedProfileVal 2 = -1 := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  refine ⟨by simp [mixedProfileVal], ?_, ?_⟩
  · unfold mixedProfileVal
    rw [show 2 * Real.pi * ((1 : ℕ) : ℝ) / 3 = 2 * Real.pi / 3 by push_cast; ring,
      cos_two_pi_div_three, sin_two_pi_div_three]
    field_simp; ring
  · unfold mixedProfileVal
    rw [show (((2 : ℕ)) : ℝ) = 2 by norm_num, cos_four_pi_div_three, sin_four_pi_div_three]
    field_simp; ring

/-- At `N = 3` the odd-grid frequency `ω_N = 2N sin(π/N)` is `3√3`. -/
theorem omega_three : 2 * (3 : ℝ) * Real.sin (Real.pi / 3) = 3 * Real.sqrt 3 := by
  rw [Real.sin_pi_div_three]; ring

/-- `T_i ⊥ P_i` in the Frobenius pairing (`eq:supp-exact-balanced-family`). -/
theorem frob_axialT_axialP (i : Fin 3) : frob (axialT i) (axialP i) = 0 := by
  fin_cases i <;> simp [frob, axialT, axialP, Fin.sum_univ_three, diagonal]

/-- `‖T_i‖_F² = 2`. -/
theorem frob_axialT_self (i : Fin 3) : frob (axialT i) (axialT i) = 2 := by
  fin_cases i <;> simp [frob, axialT, Fin.sum_univ_three] <;> norm_num

/-- `‖P_i‖_F² = 2`: the two polarizations of each axis have equal Frobenius norm. -/
theorem frob_axialP_self (i : Fin 3) : frob (axialP i) (axialP i) = 2 := by
  fin_cases i <;> simp [frob, axialP, Fin.sum_univ_three, diagonal] <;> norm_num

/-- All polarizations are trace-free. -/
theorem trace_polarizations (i : Fin 3) (r : Fin 4) :
    trace (axialT i) = 0 ∧ trace (axialP i) = 0 ∧ trace (mixedT r) = 0 ∧ trace (mixedQ r) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · fin_cases i <;> simp [trace, axialT]
  · fin_cases i <;> simp [trace, axialP, Fin.sum_univ_three]
  · fin_cases r <;> simp [trace, mixedT, mixedV, mixedW, vecMulVec, Fin.sum_univ_three]
  · fin_cases r <;> simp [trace, mixedQ, mixedV, mixedW, vecMulVec, Fin.sum_univ_three] <;>
      norm_num

/-- The calibration denominator `d₂ + d₃` is negative on the whole root box. -/
theorem calib_den_neg {q : ChartPt} (hq : InBox q) : (d2 : ℝ) + q.d3 < 0 := by
  have h := hq.2.2.2
  rw [abs_le] at h
  have hc : (centre.d3 : ℝ) = ((-781058367048738968959916622423363949380428649561582 : ℚ) /
      10 ^ 50 : ℚ) := rfl
  rw [hc] at h
  unfold d2
  push_cast at h ⊢
  linarith [h.2]

/-- Non-vacuity: the centre lies in the box. -/
theorem centre_inBox : InBox centre := by
  refine ⟨fun r => ?_, ?_, ?_, ?_⟩ <;> simp

end

end CertifiedThreeSiteEvent
end RenewalGeometry
