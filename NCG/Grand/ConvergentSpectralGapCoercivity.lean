/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Uniform coercivity from a convergent positive spectral gap

If cutoff gaps converge to a strictly positive limiting gap, then half the limiting gap is an
eventual uniform lower bound.  Any cutoffwise Poincaré inequality therefore becomes one uniform
coercivity estimate with an explicit positive constant.
-/

open Filter Topology

noncomputable section

namespace NCG.SpectralGap

universe u

/-- A real sequence converging to a positive limit is eventually bounded below by half that
limit. -/
theorem eventually_half_le_of_tendsto_of_pos
    (gap : ℕ → ℝ) (gaplim : ℝ)
    (hgap : Tendsto gap atTop (nhds gaplim)) (hpos : 0 < gaplim) :
    ∀ᶠ n in atTop, gaplim / 2 ≤ gap n := by
  have hhalf : gaplim / 2 < gaplim := by linarith
  exact (hgap.eventually (Ioi_mem_nhds hhalf)).mono fun _ hn ↦ hn.le

/-- Convergent positive cutoff gaps turn pointwise Poincaré estimates into an eventual uniform
coercivity estimate with constant `gaplim / 2`. -/
theorem eventually_uniform_coercivity_of_gap_tendsto
    {E : Type u}
    (energy residual : ℕ → E → ℝ)
    (gap : ℕ → ℝ) (gaplim : ℝ)
    (hresidual : ∀ n x, 0 ≤ residual n x)
    (hcoercive : ∀ n x, gap n * residual n x ≤ energy n x)
    (hgap : Tendsto gap atTop (nhds gaplim)) (hpos : 0 < gaplim) :
    0 < gaplim / 2 ∧
      ∀ᶠ n in atTop, ∀ x, gaplim / 2 * residual n x ≤ energy n x := by
  refine ⟨half_pos hpos, ?_⟩
  filter_upwards [eventually_half_le_of_tendsto_of_pos gap gaplim hgap hpos]
    with n hn
  intro x
  exact (mul_le_mul_of_nonneg_right hn (hresidual n x)).trans (hcoercive n x)

/-- Under one eventual uniform coercivity estimate, vanishing energy forces the unprotected
residual to vanish.  This is the abstract no-soft-mode/no-escape consequence. -/
theorem residual_tendsto_zero_of_eventually_uniform_coercivity
    {E : Type u} (energy residual : ℕ → E → ℝ) (x : ℕ → E) (gamma : ℝ)
    (hgamma : 0 < gamma) (hresidual : ∀ n y, 0 ≤ residual n y)
    (hcoercive : ∀ᶠ n in atTop, ∀ y, gamma * residual n y ≤ energy n y)
    (henergy : Tendsto (fun n ↦ energy n (x n)) atTop (nhds 0)) :
    Tendsto (fun n ↦ residual n (x n)) atTop (nhds 0) := by
  have hgammaInv : 0 ≤ gamma⁻¹ := inv_nonneg.mpr hgamma.le
  have hupper : ∀ᶠ n in atTop,
      residual n (x n) ≤ gamma⁻¹ * energy n (x n) := by
    filter_upwards [hcoercive] with n hn
    calc
      residual n (x n) = (gamma⁻¹ * gamma) * residual n (x n) := by
        rw [inv_mul_cancel₀ (ne_of_gt hgamma), one_mul]
      _ = gamma⁻¹ * (gamma * residual n (x n)) := by rw [mul_assoc]
      _ ≤ gamma⁻¹ * energy n (x n) :=
        mul_le_mul_of_nonneg_left (hn (x n)) hgammaInv
  have hscaled : Tendsto (fun n ↦ gamma⁻¹ * energy n (x n)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul henergy
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun n ↦ hresidual n (x n)) hupper hscaled

/-- A positive limiting spectral gap rules out asymptotically zero-energy vectors with a
nonvanishing unprotected residual. -/
theorem residual_tendsto_zero_of_gap_tendsto
    {E : Type u} (energy residual : ℕ → E → ℝ) (x : ℕ → E)
    (gap : ℕ → ℝ) (gaplim : ℝ)
    (hresidual : ∀ n y, 0 ≤ residual n y)
    (hcoercive : ∀ n y, gap n * residual n y ≤ energy n y)
    (hgap : Tendsto gap atTop (nhds gaplim)) (hgapPos : 0 < gaplim)
    (henergy : Tendsto (fun n ↦ energy n (x n)) atTop (nhds 0)) :
    Tendsto (fun n ↦ residual n (x n)) atTop (nhds 0) := by
  obtain ⟨hhalf, huniform⟩ :=
    eventually_uniform_coercivity_of_gap_tendsto
      energy residual gap gaplim hresidual hcoercive hgap hgapPos
  exact residual_tendsto_zero_of_eventually_uniform_coercivity
    energy residual x (gaplim / 2) hhalf hresidual huniform henergy

end NCG.SpectralGap
