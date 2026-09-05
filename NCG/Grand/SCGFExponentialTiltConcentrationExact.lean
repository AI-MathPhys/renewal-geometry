/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DifferentiableSCGFTiltGapExact

/-!
# Exponential concentration from shifted SCGF limits

This file packages the asymptotic core of exponential tilting.  If normalized
log moments converge at `k` and `k+q`, and the corresponding shifted exponent
at a tail threshold is strictly negative, then the Chernoff envelope for that
tail converges to zero exponentially.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace NCG.SCGFExponentialTiltConcentration

/-- Normalized logarithmic moment at scale `n`. The value at `n = 0` is
irrelevant to all `atTop` statements. -/
def normalizedLogMoment (Z : ℕ → ℝ → ℝ) (n : ℕ) (k : ℝ) : ℝ :=
  Real.log (Z n k) / n

/-- Chernoff envelope under exponential tilting from `k` to `k+q`. -/
def tiltedChernoffEnvelope
    (Z : ℕ → ℝ → ℝ) (k q b : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((n : ℝ) *
    (-q * b + normalizedLogMoment Z n (k + q) -
      normalizedLogMoment Z n k))

/-- Convergence of the two normalized log moments gives convergence of the
shifted exponent inside the tilted Chernoff envelope. -/
theorem tendsto_shiftedExponent
    {Z : ℕ → ℝ → ℝ} {psi : ℝ → ℝ} {k q b : ℝ}
    (hk : Tendsto (fun n => normalizedLogMoment Z n k)
      atTop (𝓝 (psi k)))
    (hkq : Tendsto (fun n => normalizedLogMoment Z n (k + q))
      atTop (𝓝 (psi (k + q)))) :
    Tendsto (fun n =>
      -q * b + normalizedLogMoment Z n (k + q) -
        normalizedLogMoment Z n k)
      atTop (𝓝 (psi (k + q) - psi k - q * b)) := by
  have hconst : Tendsto (fun _ : ℕ => -q * b) atTop (𝓝 (-q * b)) :=
    tendsto_const_nhds
  have h := hconst.add (hkq.sub hk)
  convert h using 1
  · funext n
    ring
  · ring

/-- A strictly negative limiting shifted exponent yields an eventual explicit
exponential bound with half of that exponent. -/
theorem eventually_tiltedChernoffEnvelope_le
    {Z : ℕ → ℝ → ℝ} {psi : ℝ → ℝ} {k q b : ℝ}
    (hk : Tendsto (fun n => normalizedLogMoment Z n k)
      atTop (𝓝 (psi k)))
    (hkq : Tendsto (fun n => normalizedLogMoment Z n (k + q))
      atTop (𝓝 (psi (k + q))))
    (hgap : psi (k + q) - psi k - q * b < 0) :
    ∀ᶠ n in atTop,
      tiltedChernoffEnvelope Z k q b n ≤
        Real.exp ((n : ℝ) *
          ((psi (k + q) - psi k - q * b) / 2)) := by
  let c : ℝ := psi (k + q) - psi k - q * b
  have hc : c < c / 2 := by
    dsimp only [c]
    linarith
  have hnear : Iio (c / 2) ∈ 𝓝 c := Iio_mem_nhds hc
  have hev := (tendsto_shiftedExponent hk hkq).eventually hnear
  filter_upwards [hev] with n hn
  unfold tiltedChernoffEnvelope
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (le_of_lt hn) (Nat.cast_nonneg n)

/-- The tilted Chernoff envelope converges to zero whenever its limiting
shifted exponent is negative. -/
theorem tiltedChernoffEnvelope_tendsto_zero
    {Z : ℕ → ℝ → ℝ} {psi : ℝ → ℝ} {k q b : ℝ}
    (hk : Tendsto (fun n => normalizedLogMoment Z n k)
      atTop (𝓝 (psi k)))
    (hkq : Tendsto (fun n => normalizedLogMoment Z n (k + q))
      atTop (𝓝 (psi (k + q))))
    (hgap : psi (k + q) - psi k - q * b < 0) :
    Tendsto (tiltedChernoffEnvelope Z k q b) atTop (𝓝 0) := by
  let c : ℝ := psi (k + q) - psi k - q * b
  have hc2 : c / 2 < 0 := by
    dsimp only [c]
    linarith
  have hlinear : Tendsto (fun n : ℕ => (n : ℝ) * (c / 2))
      atTop atBot :=
    tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hc2
  have hmajor : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (c / 2)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hlinear
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => Real.exp_nonneg _
  · simpa only [c] using
      eventually_tiltedChernoffEnvelope_le hk hkq hgap
  · exact hmajor

/-- Differentiability supplies a positive upper-tail tilt whose Chernoff
envelope converges to zero. -/
theorem exists_upper_tilt_with_concentration
    {Z : ℕ → ℝ → ℝ} {psi : ℝ → ℝ} {k a delta : ℝ}
    (hderiv : HasDerivAt psi a k) (hdelta : 0 < delta)
    (hlim : ∀ q, Tendsto (fun n => normalizedLogMoment Z n q)
      atTop (𝓝 (psi q))) :
    ∃ q : ℝ, 0 < q ∧
      Tendsto (tiltedChernoffEnvelope Z k q (a + delta))
        atTop (𝓝 0) := by
  obtain ⟨q, hq, hgap⟩ :=
    NCG.DifferentiableSCGFTiltGap.exists_positive_right_tilt_gap
      hderiv hdelta
  exact ⟨q, hq,
    tiltedChernoffEnvelope_tendsto_zero (hlim k) (hlim (k + q)) hgap⟩

/-- Differentiability supplies a negative lower-tail tilt whose Chernoff
envelope converges to zero. -/
theorem exists_lower_tilt_with_concentration
    {Z : ℕ → ℝ → ℝ} {psi : ℝ → ℝ} {k a delta : ℝ}
    (hderiv : HasDerivAt psi a k) (hdelta : 0 < delta)
    (hlim : ∀ q, Tendsto (fun n => normalizedLogMoment Z n q)
      atTop (𝓝 (psi q))) :
    ∃ q : ℝ, q < 0 ∧
      Tendsto (tiltedChernoffEnvelope Z k q (a - delta))
        atTop (𝓝 0) := by
  obtain ⟨q, hq, hgap⟩ :=
    NCG.DifferentiableSCGFTiltGap.exists_negative_left_tilt_gap
      hderiv hdelta
  exact ⟨q, hq,
    tiltedChernoffEnvelope_tendsto_zero (hlim k) (hlim (k + q)) hgap⟩

end NCG.SCGFExponentialTiltConcentration
