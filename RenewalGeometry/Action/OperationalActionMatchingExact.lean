/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ThreeCostIdentification
import RenewalGeometry.Gravity.RelationalDeSitterBranch

/-!
# Measured acceptance reconstructs the finite action
(`thm:main-operational-action-matching`, `eq:main-operational-acceptance`,
`eq:main-accepted-row-normalizer`, `eq:main-observed-cost`,
`eq:main-observed-homogeneous-action`, `eq:main-offshell-action-match`,
`eq:main-measured-einstein-mismatch`; emergent-spacetime manuscript)

For a finite proposal alphabet `F ⊂ ℝ`, a positive proposal row `p_s(y|x)` and the
measured quadratic cost `E_s` (`measuredQuadraticCost`), the acceptance
`a_s = e^{−E_s/ε}`, the total acceptance `Z_s(x) = Σ_y p a` and the accepted row
`Q_s = p a / Z_s` form the complete trial table.

* `observed_cost`: **`eq:main-observed-cost`**
  `E_s(x,y) = −ε log(Z_s(x) Q_s(y|x) / p_s(y|x))`;
* `observedWriter_eq_bulkAction`: **`eq:main-offshell-action-match`**: for every
  path `q_0, …, q_M` with `q_{j+1}` in the stage alphabet, the observed writer
  `ε Σ_j [log(Q_j/p_j) + log Z_j] + C(q_M² − q_0²)` equals the bulk action
  `−Σ_j [A (q_{j+1} − q_j)²/s_j + B s_j q̄_j²]` identically (the `C` terms
  telescope); this is a pointwise identity on the whole parametric domain, so
  all interior-amplitude and lapse first variations of the two sides coincide;
* `measuredQuadraticCost_sub_minimizer`, `minimizerRatio_isMin`: the one-step
  minimizer of `y ↦ E_s(x,y)` is `y = r(s) x` with
  `r(s) = (A − Bs²/4)/(A + Bs²/4 + Cs)`;
* `tendsto_log_minimizerRatio_div`: the proper-time amplitude drift
  `lim_{s→0} log r(s)/s = c = −C/A`, and `minimizer_skeleton_tendsto`: the
  `n`-step minimizing skeleton with step `τ/n` converges to `q_0 e^{cτ}`;
* `bulkAction_eq_discrete_rescaled`: the bulk action is `A/A_0` times the
  discrete homogeneous action with `A_0 = 8/3`, `B_0 = 2Λ_act`,
  `Λ_act = 4B/(3A)`; `geomLambda_eq_three_hubble_sq`: the constant-Hubble
  geometry of the skeleton, `H = 2c/3`, has `Λ_geom = 3H² = 4C²/(3A²)`;
* `einstein_measured_mismatch`: **`eq:main-measured-einstein-mismatch`**
  `G[g] + Λ_act g = (4𝔇/(3A²)) g` for the de Sitter metric with Hubble rate
  `H = 2c/3` (`RelationalDeSitterBranch.lorentzMetric`), and
  `einstein_matched_iff_rankDefect_zero`: the residual vanishes iff `𝔇 = 0`.

Scoped hypotheses: `A, B > 0`, `s > 0`, `0 < s√(B/A) < 2` (encoded `B s² < 4A`)
and the declared class `C² ≤ AB` for the one-step minimizer; `ε ≠ 0` and
positive proposal weights for the trial-table identities.
-/

namespace RenewalGeometry.OperationalActionMatching

open Real Finset

/-! ### The complete trial table -/

/-- The acceptance probability `a_s(x,y) = e^{−E_s(x,y)/ε}`
(`eq:main-operational-acceptance`). -/
noncomputable def stageAcceptance (A B C s ε x y : ℝ) : ℝ :=
  Real.exp (-(measuredQuadraticCost A B C s x y) / ε)

/-- The total acceptance probability `Z_s(x) = Σ_{y∈F} p_s(y|x) a_s(x,y)`
(`eq:main-accepted-row-normalizer`). -/
noncomputable def stageNormalizer (F : Finset ℝ) (p : ℝ → ℝ → ℝ) (A B C s ε x : ℝ) : ℝ :=
  ∑ y ∈ F, p x y * stageAcceptance A B C s ε x y

/-- The accepted row `Q_s(y|x) = p_s(y|x) a_s(x,y) / Z_s(x)`
(`eq:main-accepted-row-normalizer`). -/
noncomputable def stageAcceptedRow (F : Finset ℝ) (p : ℝ → ℝ → ℝ) (A B C s ε x y : ℝ) : ℝ :=
  p x y * stageAcceptance A B C s ε x y / stageNormalizer F p A B C s ε x

/-- The total acceptance is positive as soon as one alphabet member has positive
proposal weight. -/
theorem stageNormalizer_pos (F : Finset ℝ) (p : ℝ → ℝ → ℝ) (A B C s ε x : ℝ)
    (hp : ∀ y ∈ F, 0 ≤ p x y) {y₀ : ℝ} (hy₀ : y₀ ∈ F) (hp₀ : 0 < p x y₀) :
    0 < stageNormalizer F p A B C s ε x := by
  unfold stageNormalizer
  have hacc : ∀ y, 0 < stageAcceptance A B C s ε x y := fun y => Real.exp_pos _
  have h0 : 0 < p x y₀ * stageAcceptance A B C s ε x y₀ := mul_pos hp₀ (hacc y₀)
  exact lt_of_lt_of_le h0 (single_le_sum (f := fun y => p x y * stageAcceptance A B C s ε x y)
    (fun y hy => mul_nonneg (hp y hy) (hacc y).le) hy₀)

/-- `Z_s(x) Q_s(y|x) = p_s(y|x) a_s(x,y)`. -/
theorem stageNormalizer_mul_acceptedRow (F : Finset ℝ) (p : ℝ → ℝ → ℝ) (A B C s ε x y : ℝ)
    (hZ : stageNormalizer F p A B C s ε x ≠ 0) :
    stageNormalizer F p A B C s ε x * stageAcceptedRow F p A B C s ε x y
      = p x y * stageAcceptance A B C s ε x y := by
  unfold stageAcceptedRow
  field_simp

/-- **`eq:main-observed-cost`** (`thm:main-operational-action-matching`): the
complete trial table reconstructs the unnormalized cost exactly,
`E_s(x,y) = −ε log(Z_s(x) Q_s(y|x) / p_s(y|x))`, whenever `p_s(y|x) > 0`,
`Z_s(x) > 0` and `ε ≠ 0`. -/
theorem observed_cost (F : Finset ℝ) (p : ℝ → ℝ → ℝ) (A B C s ε x y : ℝ) (hε : ε ≠ 0)
    (hpy : 0 < p x y) (hZ : 0 < stageNormalizer F p A B C s ε x) :
    measuredQuadraticCost A B C s x y
      = -ε * Real.log (stageNormalizer F p A B C s ε x * stageAcceptedRow F p A B C s ε x y
          / p x y) := by
  rw [stageNormalizer_mul_acceptedRow F p A B C s ε x y hZ.ne',
    mul_div_cancel_left₀ _ hpy.ne']
  unfold stageAcceptance
  rw [Real.log_exp]
  field_simp

/-- The per-stage observed contribution `ε [log(Q/p) + log Z] = −E_s(x,y)`. -/
theorem observed_stage_eq_neg_cost (F : Finset ℝ) (p : ℝ → ℝ → ℝ) (A B C s ε x y : ℝ)
    (hε : ε ≠ 0) (hpy : 0 < p x y) (hZ : 0 < stageNormalizer F p A B C s ε x) :
    ε * (Real.log (stageAcceptedRow F p A B C s ε x y / p x y)
        + Real.log (stageNormalizer F p A B C s ε x))
      = -(measuredQuadraticCost A B C s x y) := by
  have hQ : 0 < stageAcceptedRow F p A B C s ε x y := by
    unfold stageAcceptedRow
    exact div_pos (mul_pos hpy (Real.exp_pos _)) hZ
  rw [← Real.log_mul (div_pos hQ hpy).ne' hZ.ne',
    show stageAcceptedRow F p A B C s ε x y / p x y * stageNormalizer F p A B C s ε x
      = stageNormalizer F p A B C s ε x * stageAcceptedRow F p A B C s ε x y / p x y by ring,
    observed_cost F p A B C s ε x y hε hpy hZ]
  ring

/-- The observed writer `𝒜_obs` of `eq:main-observed-homogeneous-action` for a path
`q_0, …, q_M` with stage alphabets `F j`, proposal rows `p j`, and lapse-weighted
intervals `s j`. -/
noncomputable def observedWriter (F : ℕ → Finset ℝ) (p : ℕ → ℝ → ℝ → ℝ) (A B C : ℝ)
    (s : ℕ → ℝ) (ε : ℝ) (q : ℕ → ℝ) (M : ℕ) : ℝ :=
  ε * ∑ j ∈ range M,
      (Real.log (stageAcceptedRow (F j) (p j) A B C (s j) ε (q j) (q (j + 1)) / p j (q j) (q (j + 1)))
        + Real.log (stageNormalizer (F j) (p j) A B C (s j) ε (q j)))
    + C * (q M ^ 2 - q 0 ^ 2)

/-- The bulk action `−Σ_j [A (q_{j+1} − q_j)²/s_j + B s_j q̄_j²]` of
`eq:main-offshell-action-match`. -/
noncomputable def bulkAction (A B : ℝ) (s : ℕ → ℝ) (q : ℕ → ℝ) (M : ℕ) : ℝ :=
  -∑ j ∈ range M, (A * (q (j + 1) - q j) ^ 2 / s j + B * s j * ((q j + q (j + 1)) / 2) ^ 2)

/-- **`eq:main-offshell-action-match`** (`thm:main-operational-action-matching`):
for every path with `q_{j+1} ∈ F_j` and positive proposal weights on the stage
alphabets, the observed writer equals the bulk action identically (the `C` terms
telescope against the endpoint term `C(q_M² − q_0²)`). -/
theorem observedWriter_eq_bulkAction (F : ℕ → Finset ℝ) (p : ℕ → ℝ → ℝ → ℝ) (A B C : ℝ)
    (s : ℕ → ℝ) (ε : ℝ) (q : ℕ → ℝ) (M : ℕ) (hε : ε ≠ 0)
    (hmem : ∀ j < M, q (j + 1) ∈ F j)
    (hp : ∀ j < M, ∀ y ∈ F j, 0 < p j (q j) y) :
    observedWriter F p A B C s ε q M = bulkAction A B s q M := by
  unfold observedWriter bulkAction
  rw [mul_sum]
  have hstage : ∀ j ∈ range M,
      ε * (Real.log (stageAcceptedRow (F j) (p j) A B C (s j) ε (q j) (q (j + 1))
            / p j (q j) (q (j + 1)))
        + Real.log (stageNormalizer (F j) (p j) A B C (s j) ε (q j)))
      = -(A * (q (j + 1) - q j) ^ 2 / s j + B * s j * ((q j + q (j + 1)) / 2) ^ 2)
          - C * (q (j + 1) ^ 2 - q j ^ 2) := by
    intro j hj
    have hj' := mem_range.mp hj
    have hZ : 0 < stageNormalizer (F j) (p j) A B C (s j) ε (q j) :=
      stageNormalizer_pos _ _ _ _ _ _ _ _ (fun y hy => (hp j hj' y hy).le) (hmem j hj')
        (hp j hj' _ (hmem j hj'))
    rw [observed_stage_eq_neg_cost _ _ _ _ _ _ _ _ _ hε (hp j hj' _ (hmem j hj')) hZ]
    unfold measuredQuadraticCost
    ring
  rw [sum_congr rfl hstage, sum_sub_distrib, sum_neg_distrib, ← mul_sum,
    sum_range_sub (fun j => q j ^ 2) M]
  ring

/-! ### The one-step minimizer and its drift -/

/-- The one-step minimizer ratio `r(s) = (A − Bs²/4)/(A + Bs²/4 + Cs)`: the
minimizer of `y ↦ E_s(x,y)` is `y = r(s) x`. -/
noncomputable def minimizerRatio (A B C s : ℝ) : ℝ :=
  (A - B * s ^ 2 / 4) / (A + B * s ^ 2 / 4 + C * s)

/-- The `y²`-coefficient `A/s + Bs/4 + C` of `y ↦ E_s(x,y)` is positive on the
declared class `C² ≤ AB` under `0 < s√(B/A) < 2`. -/
theorem leading_coefficient_pos (A B C s : ℝ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s)
    (hsmall : B * s ^ 2 < 4 * A) (hC : C ^ 2 ≤ A * B) :
    0 < A + B * s ^ 2 / 4 + C * s := by
  by_contra hcon
  push Not at hcon
  have h1 : C * s ≤ -(A + B * s ^ 2 / 4) := by linarith
  have h2 : 0 < A + B * s ^ 2 / 4 := by positivity
  have h3 : (A + B * s ^ 2 / 4) ^ 2 ≤ (C * s) ^ 2 := by
    have : A + B * s ^ 2 / 4 ≤ -(C * s) := by linarith
    nlinarith
  have h4 : (C * s) ^ 2 ≤ A * B * s ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hC (sq_nonneg s)
  have h5 : 0 < A - B * s ^ 2 / 4 := by linarith
  nlinarith [sq_pos_of_pos h5]

/-- Completing the square in `y`: `E_s(x,y) = E_s(x, r(s) x) + (A/s + Bs/4 + C)(y − r(s) x)²`. -/
theorem measuredQuadraticCost_sub_minimizer (A B C s x y : ℝ) (hs : s ≠ 0)
    (hL : A + B * s ^ 2 / 4 + C * s ≠ 0) :
    measuredQuadraticCost A B C s x y
      = measuredQuadraticCost A B C s x (minimizerRatio A B C s * x)
        + (A / s + B * s / 4 + C) * (y - minimizerRatio A B C s * x) ^ 2 := by
  have hr : minimizerRatio A B C s = (A - B * s ^ 2 / 4) / (A + B * s ^ 2 / 4 + C * s) := rfl
  obtain ⟨D, hD⟩ : ∃ D, D = A + B * s ^ 2 / 4 + C * s := ⟨_, rfl⟩
  rw [← hD] at hL hr
  rw [hr]
  unfold measuredQuadraticCost
  field_simp
  rw [hD]
  ring

/-- `y = r(s) x` minimizes `y ↦ E_s(x,y)` on the declared class
(`thm:main-operational-action-matching`, "one-step minimizing skeleton"). -/
theorem minimizerRatio_isMin (A B C s x y : ℝ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s)
    (hsmall : B * s ^ 2 < 4 * A) (hC : C ^ 2 ≤ A * B) :
    measuredQuadraticCost A B C s x (minimizerRatio A B C s * x)
      ≤ measuredQuadraticCost A B C s x y := by
  have hL := leading_coefficient_pos A B C s hA hB hs hsmall hC
  have hL' : 0 < A / s + B * s / 4 + C := by
    have : A / s + B * s / 4 + C = (A + B * s ^ 2 / 4 + C * s) / s := by field_simp
    rw [this]; positivity
  rw [measuredQuadraticCost_sub_minimizer A B C s x y hs.ne' hL.ne']
  have : 0 ≤ (A / s + B * s / 4 + C) * (y - minimizerRatio A B C s * x) ^ 2 :=
    mul_nonneg hL'.le (sq_nonneg _)
  linarith

/-- The proper-time amplitude drift `c = −C/A` (`thm:main-operational-action-matching`). -/
noncomputable def amplitudeDrift (A C : ℝ) : ℝ := -C / A

/-- `r(0) = 1`. -/
theorem minimizerRatio_zero (A B C : ℝ) (hA : A ≠ 0) : minimizerRatio A B C 0 = 1 := by
  unfold minimizerRatio; simp [hA]

/-- `s ↦ r(s)` has derivative `−C/A` at `s = 0`. -/
theorem hasDerivAt_minimizerRatio (A B C : ℝ) (hA : A ≠ 0) :
    HasDerivAt (fun s => minimizerRatio A B C s) (amplitudeDrift A C) 0 := by
  have hsq : HasDerivAt (fun s : ℝ => B * s ^ 2 / 4) (B * (↑(2:ℕ) * (0:ℝ) ^ (2 - 1)) / 4) 0 :=
    ((hasDerivAt_pow 2 (0:ℝ)).const_mul B).div_const 4
  have hnum : HasDerivAt (fun s : ℝ => A - B * s ^ 2 / 4)
      (0 - B * (↑(2:ℕ) * (0:ℝ) ^ (2 - 1)) / 4) 0 :=
    (hasDerivAt_const (0:ℝ) A).sub hsq
  have hden : HasDerivAt (fun s : ℝ => A + B * s ^ 2 / 4 + C * s)
      (0 + B * (↑(2:ℕ) * (0:ℝ) ^ (2 - 1)) / 4 + C * 1) 0 :=
    ((hasDerivAt_const (0:ℝ) A).add hsq).add ((hasDerivAt_id (0:ℝ)).const_mul C)
  have hne : A + B * (0:ℝ) ^ 2 / 4 + C * 0 ≠ 0 := by simp [hA]
  have h := hnum.div hden hne
  unfold minimizerRatio amplitudeDrift
  refine h.congr_deriv ?_
  norm_num
  field_simp

/-- `s ↦ log r(s)` has derivative `c = −C/A` at `s = 0`. -/
theorem hasDerivAt_log_minimizerRatio (A B C : ℝ) (hA : A ≠ 0) :
    HasDerivAt (fun s => Real.log (minimizerRatio A B C s)) (amplitudeDrift A C) 0 := by
  have h := (hasDerivAt_minimizerRatio A B C hA).log (by rw [minimizerRatio_zero A B C hA]; exact one_ne_zero)
  rwa [minimizerRatio_zero A B C hA, div_one] at h

/-- The logarithmic drift of the one-step minimizer: `log r(s)/s → c = −C/A` as
`s → 0` (`thm:main-operational-action-matching`, "proper-time amplitude drift
`c = −C/A`"). -/
theorem tendsto_log_minimizerRatio_div (A B C : ℝ) (hA : A ≠ 0) :
    Filter.Tendsto (fun s => Real.log (minimizerRatio A B C s) / s) (nhdsWithin 0 {0}ᶜ)
      (nhds (amplitudeDrift A C)) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_log_minimizerRatio A B C hA)
  refine h.congr' ?_
  filter_upwards with s
  simp [slope_def_field, minimizerRatio_zero A B C hA]

/-- The `n`-step minimizing skeleton with calibrated step `τ/n` converges to the
exponential profile `q_0 e^{cτ}` (`thm:main-operational-action-matching`, the
limiting constant-Hubble geometry of the skeleton). -/
theorem minimizer_skeleton_tendsto (A B C : ℝ) (hA : A ≠ 0) (q₀ τ : ℝ) (hτ : τ ≠ 0) :
    Filter.Tendsto (fun n : ℕ => minimizerRatio A B C (τ / n) ^ n * q₀) Filter.atTop
      (nhds (Real.exp (amplitudeDrift A C * τ) * q₀)) := by
  have hstep : Filter.Tendsto (fun n : ℕ => τ / (n : ℝ)) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat τ, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact div_ne_zero hτ (by exact_mod_cast hn.ne')
  have hlog : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * Real.log (minimizerRatio A B C (τ / n))) Filter.atTop
      (nhds (amplitudeDrift A C * τ)) := by
    have h1 := (tendsto_log_minimizerRatio_div A B C hA).comp hstep
    have h2 := h1.const_mul τ
    rw [mul_comm] at h2
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [Function.comp]
    field_simp
  have hpos : ∀ᶠ n : ℕ in Filter.atTop, 0 < minimizerRatio A B C (τ / n) := by
    have hcont : Filter.Tendsto (fun n : ℕ => minimizerRatio A B C (τ / n)) Filter.atTop
        (nhds (minimizerRatio A B C 0)) :=
      (hasDerivAt_minimizerRatio A B C hA).continuousAt.tendsto.comp
        (tendsto_const_div_atTop_nhds_zero_nat τ)
    rw [minimizerRatio_zero A B C hA] at hcont
    exact hcont.eventually (lt_mem_nhds one_pos)
  have hexp := (Real.continuous_exp.tendsto _).comp hlog
  refine (hexp.mul_const q₀).congr' ?_
  filter_upwards [hpos] with n hn
  simp only [Function.comp]
  rw [Real.exp_nat_mul, Real.exp_log hn]

/-! ### Cosmological parameters and the Einstein mismatch -/

/-- `Λ_act = 4B/(3A)`: the vacuum parameter of the measured bulk action. -/
noncomputable def actionLambda (A B : ℝ) : ℝ := 4 * B / (3 * A)

/-- `Λ_geom = 4C²/(3A²)`: the cosmological parameter of the limiting
constant-Hubble geometry of the minimizing skeleton. -/
noncomputable def geomLambda (A C : ℝ) : ℝ := 4 * C ^ 2 / (3 * A ^ 2)

/-- The Hubble rate of the skeleton's limiting geometry, `H = 2c/3` (`q = a^{3/2}`). -/
noncomputable def skeletonHubble (A C : ℝ) : ℝ := 2 * amplitudeDrift A C / 3

/-- `Λ_geom = 3H²` with `H = 2c/3`, `c = −C/A`. -/
theorem geomLambda_eq_three_hubble_sq (A C : ℝ) (hA : A ≠ 0) :
    geomLambda A C = 3 * skeletonHubble A C ^ 2 := by
  unfold geomLambda skeletonHubble amplitudeDrift
  field_simp
  ring

/-- The bulk action is `A/A_0` times the discrete homogeneous action
`eq:main-discrete-homogeneous-action` with `A_0 = 8/3` and `B_0 = 2Λ_act`, i.e.
`Λ_act = 4B/(3A)` (`thm:main-operational-action-matching`). -/
theorem bulkAction_eq_discrete_rescaled (A B : ℝ) (hA : A ≠ 0) (s q : ℕ → ℝ) (M : ℕ) :
    bulkAction A B s q M
      = (A / (8 / 3)) * bulkAction (8 / 3) (2 * actionLambda A B) s q M := by
  unfold bulkAction actionLambda
  rw [mul_neg, mul_sum]
  congr 1
  apply sum_congr rfl
  intro j _
  field_simp
  ring

/-- `Λ_act − Λ_geom = 4𝔇/(3A²)`. -/
theorem actionLambda_sub_geomLambda (A B C : ℝ) (hA : A ≠ 0) :
    actionLambda A B - geomLambda A C = 4 * rankDefect A B C / (3 * A ^ 2) := by
  unfold actionLambda geomLambda rankDefect
  field_simp

open RelationalDeSitterBranch in
/-- The Einstein tensor `G = Ric − (R/2) g` of the constant-Hubble branch. -/
noncomputable def einsteinTensor (H t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ricciTensor H t - (scalarCurvature H / 2) • lorentzMetric H t

open RelationalDeSitterBranch in
/-- **`eq:main-measured-einstein-mismatch`** (`thm:main-operational-action-matching`):
for the limiting constant-Hubble geometry of the minimizing skeleton
(`H = 2c/3`, `Λ_geom = 3H²`), `G[g] + Λ_act g = (Λ_act − Λ_geom) g = (4𝔇/(3A²)) g`. -/
theorem einstein_measured_mismatch (A B C t : ℝ) (hA : A ≠ 0) :
    einsteinTensor (skeletonHubble A C) t
        + actionLambda A B • lorentzMetric (skeletonHubble A C) t
      = (4 * rankDefect A B C / (3 * A ^ 2)) • lorentzMetric (skeletonHubble A C) t := by
  have hvac := einstein_cosmological_vacuum (skeletonHubble A C) t
  have hΛ : cosmologicalCoefficient (skeletonHubble A C) = geomLambda A C := by
    unfold cosmologicalCoefficient; rw [geomLambda_eq_three_hubble_sq A C hA]
  rw [← actionLambda_sub_geomLambda A B C hA, sub_smul, ← hΛ]
  unfold einsteinTensor
  rw [← sub_eq_zero]
  rw [← sub_eq_zero] at hvac
  rw [← hvac]
  abel

open RelationalDeSitterBranch in
/-- The local operational update and the vacuum parameter of its measured bulk action
agree exactly (`G[g] + Λ_act g = 0`) iff `𝔇 = 0`
(`thm:main-operational-action-matching`, last sentence). -/
theorem einstein_matched_iff_rankDefect_zero (A B C t : ℝ) (hA : A ≠ 0) :
    einsteinTensor (skeletonHubble A C) t
        + actionLambda A B • lorentzMetric (skeletonHubble A C) t = 0
      ↔ rankDefect A B C = 0 := by
  rw [einstein_measured_mismatch A B C t hA]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [lorentzMetric, Matrix.smul_apply] at h00
    rcases h00 with h00 | h00
    · exact h00
    · exact absurd h00 (by positivity)
  · intro h
    rw [h]; simp

end RenewalGeometry.OperationalActionMatching
