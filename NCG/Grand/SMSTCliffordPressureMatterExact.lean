/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Clifford pressure–matter coordinates (exact)

Exact formalization of `cor:SMST-Clifford-pressure-matter`: the
accepted-count pressure of the Clifford sign-flip indicator, its
slope, the matter-mass reading, the raw-time rescaling, and the
binary difference-reward Hessian gap.

The finite occurrence model: one opportunity is a pair
`(accepted?, flipped?)` with weights
`(1-ϑ, 0, ϑ(1-p), ϑp)`; the flip indicator `F` counts the
accepted-and-flipped outcome.

Derived content (every boxed identity):

* `flipMoment_eq`: the one-opportunity tilted likelihood is
  `1 - ϑ + ϑ[(1-p) + p·e^{-q}]`;
* `flipMoment_pos` / `pressure_scgf`: the `n`-opportunity
  partition function factorizes exactly and the accepted-count
  pressure per opportunity is the boxed
  `𝒫(q) = log(1 - ϑ + ϑ[(1-p) + p e^{-q}])` — the i.i.d. SCGF
  identity, proved by the product/sum interchange over the path
  space `Fin n → Ω₀`;
* `pressure_hasDerivAt_zero`: the boxed slope
  `𝒫'(0) = -ϑ·p`;
* `mass_from_count_slope` / `raw_time_slope` /
  `mass_from_time_slope`: the mass readings
  `𝔪 = -(2D/ϑ)𝒫'(0) = 2Dp` and the raw-time versions with the
  `11/4` mean-duration factor
  (`thm:accepted-response-renewal`, proved);
* `stationary_variance_form`: the stationary sign law
  `(d₊/D, d₋/D)` has variance form `(d₊d₋/D²)|xp-xm|²`;
* `hessian_second_moment` / `hessian_gap` / `hessian_gap_time`:
  the flip second moment `ϑp|xp-xm|²` and the boxed generalized
  gaps `σ_# = ϑpD²/(d₊d₋)`, `σ_t = (4/11)σ_#`.
-/

open Finset

namespace NCG
namespace SMSTChannel

/-- One Clifford opportunity: `(accepted?, flipped?)`. -/
abbrev CliffordSample : Type := Bool × Bool

/-- The occurrence weights: acceptance `ϑ`, conditional flip
probability `p`; an unaccepted opportunity cannot flip. -/
def flipWeight (ϑ p : ℝ) : CliffordSample → ℝ
  | (false, false) => 1 - ϑ
  | (false, true) => 0
  | (true, false) => ϑ * (1 - p)
  | (true, true) => ϑ * p

/-- The flip indicator `F`. -/
def flipCount : CliffordSample → ℕ
  | (true, true) => 1
  | _ => 0

/-- The accepted-count flip pressure
`𝒫(q) = log(1 - ϑ + ϑ[(1-p) + p·e^{-q}])`. -/
noncomputable def cliffordPressure (ϑ p q : ℝ) : ℝ :=
  Real.log (1 - ϑ + ϑ * ((1 - p) + p * Real.exp (-q)))

/-- The one-opportunity tilted likelihood. -/
theorem flipMoment_eq (ϑ p q : ℝ) :
    (∑ ω : CliffordSample,
      flipWeight ϑ p ω * Real.exp (-q * flipCount ω))
    = 1 - ϑ + ϑ * ((1 - p) + p * Real.exp (-q)) := by
  rw [Fintype.sum_prod_type]
  simp [flipWeight, flipCount]
  ring

/-- Positivity of the tilted likelihood on the physical
parameter range. -/
theorem flipMoment_pos (ϑ p q : ℝ) (hϑ0 : 0 ≤ ϑ)
    (hϑ1 : ϑ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < 1 - ϑ + ϑ * ((1 - p) + p * Real.exp (-q)) := by
  have hexp : 0 < Real.exp (-q) := Real.exp_pos _
  have hϑp : ϑ * p ≤ 1 := by nlinarith
  have hid : 1 - ϑ + ϑ * ((1 - p) + p * Real.exp (-q))
      = (1 - ϑ * p) + ϑ * p * Real.exp (-q) := by ring
  rw [hid]
  rcases lt_or_eq_of_le hϑp with h | h
  · have : 0 ≤ ϑ * p * Real.exp (-q) := by positivity
    linarith
  · rw [h]
    have : (0 : ℝ) < 1 * Real.exp (-q) := by positivity
    linarith

/-- **The SCGF identity**: the `n`-opportunity partition
function factorizes and the accepted-count pressure per
opportunity is the boxed `cliffordPressure`. -/
theorem pressure_scgf (ϑ p q : ℝ) (n : ℕ) (hn : 0 < n) :
    (1 / n) * Real.log
      (∑ g : Fin n → CliffordSample,
        (∏ i, flipWeight ϑ p (g i))
          * Real.exp (-q * (∑ i, (flipCount (g i) : ℝ))))
    = cliffordPressure ϑ p q := by
  -- factorize the path sum
  have hfact : (∑ g : Fin n → CliffordSample,
      (∏ i, flipWeight ϑ p (g i))
        * Real.exp (-q * (∑ i, (flipCount (g i) : ℝ))))
      = (∑ ω : CliffordSample,
          flipWeight ϑ p ω * Real.exp (-q * flipCount ω)) ^ n := by
    have hstep : ∀ g : Fin n → CliffordSample,
        (∏ i, flipWeight ϑ p (g i))
          * Real.exp (-q * (∑ i, (flipCount (g i) : ℝ)))
        = ∏ i, (flipWeight ϑ p (g i)
            * Real.exp (-q * flipCount (g i))) := by
      intro g
      rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
    simp_rw [hstep]
    calc (∑ g : Fin n → CliffordSample,
        ∏ i, (flipWeight ϑ p (g i)
          * Real.exp (-q * flipCount (g i))))
        = ∑ x ∈ Fintype.piFinset
            (fun _ : Fin n => (Finset.univ : Finset CliffordSample)),
            ∏ i, (flipWeight ϑ p (x i)
              * Real.exp (-q * flipCount (x i))) := by
          rw [Fintype.piFinset_univ]
      _ = ∏ _i : Fin n, ∑ ω ∈ (Finset.univ : Finset CliffordSample),
            (flipWeight ϑ p ω * Real.exp (-q * flipCount ω)) :=
          (Finset.prod_univ_sum
            (fun _ : Fin n => (Finset.univ : Finset CliffordSample))
            (fun _ ω => flipWeight ϑ p ω
              * Real.exp (-q * flipCount ω))).symm
      _ = (∑ ω : CliffordSample,
            flipWeight ϑ p ω * Real.exp (-q * flipCount ω)) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hfact, flipMoment_eq, Real.log_pow]
  have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [cliffordPressure]
  field_simp

/-- **The boxed slope** `𝒫'(0) = -ϑ·p`. -/
theorem pressure_hasDerivAt_zero (ϑ p : ℝ) (hϑ0 : 0 ≤ ϑ)
    (hϑ1 : ϑ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    HasDerivAt (fun q => cliffordPressure ϑ p q)
      (-(ϑ * p)) 0 := by
  have hexp : HasDerivAt (fun q : ℝ => Real.exp (-q))
      (-1 : ℝ) 0 := by
    have hneg : HasDerivAt (fun q : ℝ => -q) (-1) 0 :=
      (hasDerivAt_id 0).neg
    have h := (Real.hasDerivAt_exp (-(0 : ℝ))).scomp 0 hneg
    have hv : (-1 : ℝ) • Real.exp (-(0 : ℝ)) = -1 := by
      norm_num
    rw [hv] at h
    exact h
  have hinner : HasDerivAt
      (fun q : ℝ => 1 - ϑ + ϑ * ((1 - p) + p * Real.exp (-q)))
      (ϑ * (p * (-1))) 0 := by
    have h₁ : HasDerivAt
        (fun q : ℝ => p * Real.exp (-q)) (p * (-1)) 0 :=
      hexp.const_mul p
    have h₂ : HasDerivAt
        (fun q : ℝ => (1 - p) + p * Real.exp (-q))
        (p * (-1)) 0 := h₁.const_add (1 - p)
    have h₃ : HasDerivAt
        (fun q : ℝ => ϑ * ((1 - p) + p * Real.exp (-q)))
        (ϑ * (p * (-1))) 0 := h₂.const_mul ϑ
    exact h₃.const_add (1 - ϑ)
  have hne : (1 - ϑ + ϑ * ((1 - p) + p * Real.exp (-(0 : ℝ))))
      ≠ 0 := ne_of_gt (flipMoment_pos ϑ p 0 hϑ0 hϑ1 hp0 hp1)
  have h := hinner.log hne
  have hval : ϑ * (p * (-1))
      / (1 - ϑ + ϑ * ((1 - p) + p * Real.exp (-(0 : ℝ))))
      = -(ϑ * p) := by
    rw [neg_zero, Real.exp_zero]
    have : 1 - ϑ + ϑ * ((1 - p) + p * 1) = 1 := by ring
    rw [this]
    ring
  rw [hval] at h
  exact h

/-- The matter-mass reading from the count slope:
`𝔪 = -(2D/ϑ)·𝒫'(0) = 2Dp`. -/
theorem mass_from_count_slope (ϑ p D : ℝ) (hϑ : ϑ ≠ 0) :
    -(2 * D / ϑ) * (-(ϑ * p)) = 2 * D * p := by
  field_simp

/-- The raw-time slope: dividing the count slope by the mean
per-opportunity duration `11/4` gives
`𝒫_t'(0) = -(4ϑ/11)p`. -/
theorem raw_time_slope (ϑ p : ℝ) :
    (-(ϑ * p)) / (11 / 4) = -(4 * ϑ / 11) * p := by
  ring

/-- The matter-mass reading from the raw-time slope:
`𝔪 = -(11D/2ϑ)·𝒫_t'(0) = 2Dp`. -/
theorem mass_from_time_slope (ϑ p D : ℝ) (hϑ : ϑ ≠ 0) :
    -(11 * D / (2 * ϑ)) * (-(4 * ϑ / 11) * p) = 2 * D * p := by
  field_simp
  ring

/-- The stationary sign law `(d₊/D, d₋/D)` has variance form
`(d₊d₋/D²)·|xp - xm|²`. -/
theorem stationary_variance_form (dp dm xp xm : ℝ)
    (hD : dp + dm ≠ 0) :
    (dp / (dp + dm)) * xp ^ 2 + (dm / (dp + dm)) * xm ^ 2
      - ((dp * xp + dm * xm) / (dp + dm)) ^ 2
    = (dp * dm / (dp + dm) ^ 2) * (xp - xm) ^ 2 := by
  field_simp
  ring

/-- The flip second moment: a flip occurs with probability
`ϑp` and carries squared difference reward `|xp - xm|²`. -/
theorem hessian_second_moment (ϑ p xp xm : ℝ) :
    (∑ ω : CliffordSample, flipWeight ϑ p ω
      * ((flipCount ω : ℝ) * (xp - xm) ^ 2))
    = ϑ * p * (xp - xm) ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp [flipWeight, flipCount]

/-- **The boxed generalized gap**
`σ_# = ϑpD²/(d₊d₋)`: the flip Hessian form is exactly `σ_#`
times the stationary variance form. -/
theorem hessian_gap (ϑ p dp dm xp xm : ℝ) (hdp : dp ≠ 0)
    (hdm : dm ≠ 0) (hD : dp + dm ≠ 0) :
    ϑ * p * (xp - xm) ^ 2
    = (ϑ * p * (dp + dm) ^ 2 / (dp * dm))
      * ((dp * dm / (dp + dm) ^ 2) * (xp - xm) ^ 2) := by
  field_simp

/-- The raw-time gap: `σ_t = (4/11)·σ_#`. -/
theorem hessian_gap_time (ϑ p dp dm : ℝ) :
    (4 / 11) * (ϑ * p * (dp + dm) ^ 2 / (dp * dm))
    = 4 * ϑ * p * (dp + dm) ^ 2 / (11 * (dp * dm)) := by
  ring

end SMSTChannel
end NCG
