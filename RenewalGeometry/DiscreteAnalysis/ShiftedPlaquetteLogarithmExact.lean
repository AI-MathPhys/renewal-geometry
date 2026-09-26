/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Shifted plaquette logarithm: removable quotient and analytic extension
  (`lem:native-plaquette`, Einstein–Standard-Model action-closure manuscript)

For bounded elements `X Y a b` of a real Banach algebra `𝔄`, the shifted
four-link product of `eq:native-plaquettes`
`P(h) = e^{hX} e^{h(Y+ha)} e^{-h(X+hb)} e^{-hY}`
satisfies `P(h) = 1 + h² (a - b + [X,Y]) + O(h³)`
(`product_sub_secondOrder_isBigO`), is real-analytic in `h`
(`analyticAt_product`), and its removable quotient
`Q(h) = h⁻² (P(h) - 1)` (realised as a double difference quotient
`dslope (dslope P 0) 0`) is analytic at `h = 0` with `Q(0) = a - b + [X,Y]`
(`analyticAt_quotient`, `quotient_zero`, `quotient_apply_of_ne`).

The logarithm near the identity is the power series
`log (1 + z) = z · L z`, `L z = Σ_{n ≥ 0} (-1)^n z^n / (n+1)`, a
`FormalMultilinearSeries.ofScalars` series of radius exactly `1`
(`logQuotientSeries_radius`).  The paper's map
`Φ(h) = h⁻² log P(h)` is realised as `logPlaquette = Q(h) · L(h² Q(h))`:
it is analytic at `h = 0`, `Φ(0) = a - b + [X,Y]`
(`analyticAt_logPlaquette`, `logPlaquette_zero`) and
`h² Φ(h) = log P(h)` for every `h ≠ 0` (`sq_smul_logPlaquette`).

Not covered here (disclosed): the identification of the series logarithm as
the inverse of `exp` (`exp (log (1+z)) = 1 + z`), and the uniformity of the
`h`-derivative bounds over compact parameter sets `(X,Y,a,b)`.
-/

open NormedSpace Asymptotics Filter Topology

namespace RenewalGeometry
namespace ShiftedPlaquette

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

/-- The shifted four-link product `e^{hX} e^{h(Y+ha)} e^{-h(X+hb)} e^{-hY}`
of `lem:native-plaquette`. -/
noncomputable def product (h : ℝ) (X Y a b : 𝔄) : 𝔄 :=
  exp (h • X) * exp (h • Y + h ^ 2 • a) * exp (-(h • X) - h ^ 2 • b) * exp (-(h • Y))

/-- The second-order coefficient `a - b + [X,Y]` of `lem:native-plaquette`. -/
def curvature (X Y a b : 𝔄) : 𝔄 := a - b + (X * Y - Y * X)

/-- Near `h = 0`, a polynomial vanishing to third order is `O(h³)`. -/
theorem isBigO_cubic_poly (c₁ c₂ : 𝔄) :
    (fun h : ℝ => h ^ 3 • c₁ + h ^ 4 • c₂) =O[𝓝 0] fun h : ℝ => h ^ 3 := by
  refine IsBigO.of_bound (‖c₁‖ + ‖c₂‖) ?_
  have hh1 : ∀ᶠ h : ℝ in 𝓝 0, |h| ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    exact hh.le
  filter_upwards [hh1] with h hh
  have h4 : |h| ^ 4 ≤ |h| ^ 3 := by
    have := abs_nonneg h
    calc |h| ^ 4 = |h| ^ 3 * |h| := by ring
      _ ≤ |h| ^ 3 * 1 := by gcongr
      _ = |h| ^ 3 := by ring
  rw [Real.norm_eq_abs, abs_pow]
  calc ‖h ^ 3 • c₁ + h ^ 4 • c₂‖ ≤ ‖h ^ 3 • c₁‖ + ‖h ^ 4 • c₂‖ := norm_add_le _ _
    _ = |h| ^ 3 * ‖c₁‖ + |h| ^ 4 * ‖c₂‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_pow]
    _ ≤ |h| ^ 3 * ‖c₁‖ + |h| ^ 3 * ‖c₂‖ := by gcongr
    _ = (‖c₁‖ + ‖c₂‖) * |h| ^ 3 := by ring

/-- Second-order expansion of a single exponential link
`exp (h z + h² w) = 1 + h z + h² (w + z²/2) + O(h³)`. -/
theorem exp_link_expansion (z w : 𝔄) :
    (fun h : ℝ => exp (h • z + h ^ 2 • w) -
      (1 + h • z + h ^ 2 • (w + (2 : ℝ)⁻¹ • z ^ 2))) =O[𝓝 0] fun h : ℝ => h ^ 3 := by
  set u : ℝ → 𝔄 := fun h => h • z + h ^ 2 • w with hu
  have hucont : Continuous u := by
    simp only [hu]
    fun_prop
  have hu0 : Tendsto u (𝓝 0) (𝓝 0) := by
    have h0 : u 0 = 0 := by simp [hu]
    simpa [h0] using hucont.tendsto 0
  have hexp := (exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := 𝔄)).isBigO_sub_partialSum_pow 3
  have h1 := hexp.comp_tendsto hu0
  have hps : ∀ y : 𝔄, (expSeries ℝ 𝔄).partialSum 3 y = 1 + y + (2 : ℝ)⁻¹ • y ^ 2 := by
    intro y
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, expSeries_apply_eq,
      Nat.factorial]
  have hnorm : (fun h : ℝ => ‖u h‖ ^ 3) =O[𝓝 0] fun h : ℝ => h ^ 3 := by
    refine IsBigO.of_bound ((‖z‖ + ‖w‖) ^ 3) ?_
    have hh1 : ∀ᶠ h : ℝ in 𝓝 0, |h| ≤ 1 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
      exact hh.le
    filter_upwards [hh1] with h hh
    have hb : ‖u h‖ ≤ |h| * (‖z‖ + ‖w‖) := by
      have hsq : |h| ^ 2 ≤ |h| := by
        have := abs_nonneg h
        nlinarith
      calc ‖u h‖ ≤ ‖h • z‖ + ‖h ^ 2 • w‖ := norm_add_le _ _
        _ = |h| * ‖z‖ + |h| ^ 2 * ‖w‖ := by
            simp [norm_smul, Real.norm_eq_abs, abs_pow]
        _ ≤ |h| * ‖z‖ + |h| * ‖w‖ := by gcongr
        _ = |h| * (‖z‖ + ‖w‖) := by ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow, abs_norm]
    calc ‖u h‖ ^ 3 ≤ (|h| * (‖z‖ + ‖w‖)) ^ 3 := by gcongr
      _ = (‖z‖ + ‖w‖) ^ 3 * |h| ^ 3 := by ring
  have h2 : (fun h : ℝ => exp (u h) - (1 + u h + (2 : ℝ)⁻¹ • (u h) ^ 2))
      =O[𝓝 0] fun h : ℝ => h ^ 3 := by
    refine IsBigO.trans ?_ hnorm
    simpa [Function.comp_def, hps] using h1
  have h3 : (fun h : ℝ => (1 + u h + (2 : ℝ)⁻¹ • (u h) ^ 2) -
      (1 + h • z + h ^ 2 • (w + (2 : ℝ)⁻¹ • z ^ 2))) =O[𝓝 0] fun h : ℝ => h ^ 3 := by
    have hid : ∀ h : ℝ, (1 + u h + (2 : ℝ)⁻¹ • (u h) ^ 2) -
        (1 + h • z + h ^ 2 • (w + (2 : ℝ)⁻¹ • z ^ 2)) =
        h ^ 3 • ((2 : ℝ)⁻¹ • (z * w + w * z)) + h ^ 4 • ((2 : ℝ)⁻¹ • w ^ 2) := by
      intro h
      simp only [hu, sq, add_mul, mul_add, smul_mul_smul_comm, smul_add, smul_smul]
      module
    simp only [hid]
    exact isBigO_cubic_poly _ _
  have := h2.add h3
  simpa using this

/-- Product of two second-order-expanded factors. -/
theorem product_expansion {f g : ℝ → 𝔄} {α β α' β' : 𝔄}
    (hf : (fun h : ℝ => f h - (1 + h • α + h ^ 2 • β)) =O[𝓝 0] fun h : ℝ => h ^ 3)
    (hg : (fun h : ℝ => g h - (1 + h • α' + h ^ 2 • β')) =O[𝓝 0] fun h : ℝ => h ^ 3) :
    (fun h : ℝ => f h * g h - (1 + h • (α + α') + h ^ 2 • (β + β' + α * α')))
      =O[𝓝 0] fun h : ℝ => h ^ 3 := by
  set pf : ℝ → 𝔄 := fun h => 1 + h • α + h ^ 2 • β with hpf
  set pg : ℝ → 𝔄 := fun h => 1 + h • α' + h ^ 2 • β' with hpg
  have hcube : (fun h : ℝ => h ^ 3) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    rw [Real.norm_eq_abs, abs_pow, norm_one]
    have := abs_nonneg h
    nlinarith [pow_le_one₀ this hh.le (n := 3)]
  have hpfO : pf =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
    have hc : Continuous pf := by
      simp only [hpf]
      fun_prop
    exact (hc.tendsto 0).isBigO_one (F := ℝ)
  have hpgO : pg =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
    have hc : Continuous pg := by
      simp only [hpg]
      fun_prop
    exact (hc.tendsto 0).isBigO_one (F := ℝ)
  have hgO : g =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
    have h' : g = fun h => (g h - pg h) + pg h := by
      funext h
      simp
    rw [h']
    exact ((hg.trans hcube).add hpgO).trans (isBigO_const_const _ one_ne_zero _)
  have hA : (fun h : ℝ => (f h - pf h) * g h) =O[𝓝 0] fun h : ℝ => h ^ 3 := by
    have := hf.mul hgO
    simpa using this
  have hB : (fun h : ℝ => pf h * (g h - pg h)) =O[𝓝 0] fun h : ℝ => h ^ 3 := by
    have := hpfO.mul hg
    simpa using this
  have hC : (fun h : ℝ => pf h * pg h - (1 + h • (α + α') + h ^ 2 • (β + β' + α * α')))
      =O[𝓝 0] fun h : ℝ => h ^ 3 := by
    have hid : ∀ h : ℝ, pf h * pg h - (1 + h • (α + α') + h ^ 2 • (β + β' + α * α')) =
        h ^ 3 • (α * β' + β * α') + h ^ 4 • (β * β') := by
      intro h
      simp only [hpf, hpg, add_mul, mul_add, smul_mul_smul_comm, smul_add, smul_smul, one_mul,
        mul_one, smul_mul_assoc, mul_smul_comm]
      module
    simp only [hid]
    exact isBigO_cubic_poly _ _
  have hid : ∀ h : ℝ, f h * g h - (1 + h • (α + α') + h ^ 2 • (β + β' + α * α')) =
      (f h - pf h) * g h + pf h * (g h - pg h) +
        (pf h * pg h - (1 + h • (α + α') + h ^ 2 • (β + β' + α * α'))) := by
    intro h
    noncomm_ring
  simp only [hid]
  exact (hA.add hB).add hC

/-- `lem:native-plaquette`, expansion clause: the shifted four-link product is
`1 + h² (a - b + [X,Y]) + O(h³)`. -/
theorem product_sub_secondOrder_isBigO (X Y a b : 𝔄) :
    (fun h : ℝ => product h X Y a b - (1 + h ^ 2 • curvature X Y a b))
      =O[𝓝 0] fun h : ℝ => h ^ 3 := by
  have e1 := exp_link_expansion X (0 : 𝔄)
  have e2 := exp_link_expansion Y a
  have e3 := exp_link_expansion (-X) (-b)
  have e4 := exp_link_expansion (-Y) (0 : 𝔄)
  have p := product_expansion (product_expansion (product_expansion e1 e2) e3) e4
  refine p.congr_left ?_
  intro h
  have hprod : exp (h • X + h ^ 2 • (0 : 𝔄)) * exp (h • Y + h ^ 2 • a) *
      exp (h • (-X) + h ^ 2 • (-b)) * exp (h • (-Y) + h ^ 2 • (0 : 𝔄)) = product h X Y a b := by
    simp [product, smul_neg, sub_eq_add_neg]
  have hcoef : (1 : 𝔄) + h • (X + Y + -X + -Y) +
      h ^ 2 • (0 + (2 : ℝ)⁻¹ • X ^ 2 + (a + (2 : ℝ)⁻¹ • Y ^ 2) + X * Y +
        (-b + (2 : ℝ)⁻¹ • (-X) ^ 2) + (X + Y) * -X +
        (0 + (2 : ℝ)⁻¹ • (-Y) ^ 2) + (X + Y + -X) * -Y) =
      1 + h ^ 2 • curvature X Y a b := by
    have hX : X + Y + -X + -Y = 0 := by abel
    have hY : (0 : 𝔄) + (2 : ℝ)⁻¹ • X ^ 2 + (a + (2 : ℝ)⁻¹ • Y ^ 2) + X * Y +
        (-b + (2 : ℝ)⁻¹ • (-X) ^ 2) + (X + Y) * -X +
        (0 + (2 : ℝ)⁻¹ • (-Y) ^ 2) + (X + Y + -X) * -Y = curvature X Y a b := by
      simp only [curvature, sq, add_mul, mul_add, mul_neg, neg_mul, neg_neg]
      module
    rw [hX, hY, smul_zero, add_zero]
  rw [hprod, hcoef]

/-- The product is real-analytic in the mesh parameter `h`. -/
theorem analyticAt_product (X Y a b : 𝔄) (h₀ : ℝ) :
    AnalyticAt ℝ (fun h : ℝ => product h X Y a b) h₀ := by
  have hlin : ∀ z : 𝔄, AnalyticAt ℝ (fun h : ℝ => h • z) h₀ := fun z =>
    analyticAt_id.smul analyticAt_const
  have hquad : ∀ z : 𝔄, AnalyticAt ℝ (fun h : ℝ => h ^ 2 • z) h₀ := fun z =>
    (analyticAt_id.pow 2).smul analyticAt_const
  have h1 : AnalyticAt ℝ (fun h : ℝ => exp (h • X)) h₀ :=
    (exp_analytic (𝕂 := ℝ) _).comp (hlin X)
  have h2 : AnalyticAt ℝ (fun h : ℝ => exp (h • Y + h ^ 2 • a)) h₀ :=
    (exp_analytic (𝕂 := ℝ) _).comp ((hlin Y).add (hquad a))
  have h3 : AnalyticAt ℝ (fun h : ℝ => exp (-(h • X) - h ^ 2 • b)) h₀ :=
    (exp_analytic (𝕂 := ℝ) _).comp ((hlin X).neg.sub (hquad b))
  have h4 : AnalyticAt ℝ (fun h : ℝ => exp (-(h • Y))) h₀ :=
    (exp_analytic (𝕂 := ℝ) _).comp (hlin Y).neg
  exact ((h1.mul h2).mul h3).mul h4

/-- The removable quotient `Q(h) = h⁻² (P(h) - 1)`, realised as the double
difference quotient `dslope (dslope P 0) 0`. -/
noncomputable def quotient (X Y a b : 𝔄) : ℝ → 𝔄 :=
  dslope (dslope (fun h : ℝ => product h X Y a b) 0) 0

theorem product_zero (X Y a b : 𝔄) : product 0 X Y a b = 1 := by
  simp [product]

/-- The linear coefficient of the product vanishes: `P'(0) = 0`. -/
theorem hasDerivAt_product_zero (X Y a b : 𝔄) :
    HasDerivAt (fun h : ℝ => product h X Y a b) 0 0 := by
  rw [hasDerivAt_iff_isLittleO]
  have hO := product_sub_secondOrder_isBigO X Y a b
  have hsq : (fun h : ℝ => h ^ 2 • curvature X Y a b) =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine IsBigO.of_bound ‖curvature X Y a b‖ ?_
    filter_upwards with h
    rw [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm]
  have h1 : (fun h : ℝ => product h X Y a b - 1) =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    have hA := hO.trans (isLittleO_pow_pow (by norm_num : 2 < 3)).isBigO
    have := hA.add hsq
    simpa [sub_add_eq_sub_sub, sub_add_cancel] using this
  have h2 : (fun h : ℝ => product h X Y a b - 1) =o[𝓝 0] fun h : ℝ => h := by
    have := h1.trans_isLittleO (isLittleO_pow_pow (by norm_num : 1 < 2))
    simpa using this
  simpa [product_zero] using h2

/-- Off `h = 0` the removable quotient is the literal quotient `h⁻² (P(h) - 1)`. -/
theorem quotient_apply_of_ne (X Y a b : 𝔄) {h : ℝ} (hh : h ≠ 0) :
    quotient X Y a b h = (h ^ 2)⁻¹ • (product h X Y a b - 1) := by
  unfold quotient
  rw [dslope_of_ne _ hh, slope_def_module, dslope_of_ne _ hh, slope_def_module, dslope_same,
    (hasDerivAt_product_zero X Y a b).deriv, product_zero, sub_zero, sub_zero, smul_smul]
  congr 1
  rw [sq, mul_inv]

/-- The removable quotient is analytic at `h = 0`. -/
theorem analyticAt_quotient (X Y a b : 𝔄) : AnalyticAt ℝ (quotient X Y a b) 0 := by
  obtain ⟨p, hp⟩ := analyticAt_product X Y a b 0
  exact (hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope).analyticAt

/-- `Q(0) = a - b + [X,Y]`. -/
theorem quotient_zero (X Y a b : 𝔄) : quotient X Y a b 0 = curvature X Y a b := by
  have hcont : Tendsto (quotient X Y a b) (𝓝[≠] 0) (𝓝 (quotient X Y a b 0)) :=
    (analyticAt_quotient X Y a b).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (quotient X Y a b) (𝓝[≠] 0) (𝓝 (curvature X Y a b)) := by
    have hO := (product_sub_secondOrder_isBigO X Y a b).mono
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
    have h2 : (fun h : ℝ => (h ^ 2)⁻¹ • (product h X Y a b - (1 + h ^ 2 • curvature X Y a b)))
        =O[𝓝[≠] 0] fun h : ℝ => (h ^ 2)⁻¹ • h ^ 3 :=
      (isBigO_refl (fun h : ℝ => (h ^ 2)⁻¹) _).smul hO
    have h1 : (fun h : ℝ => quotient X Y a b h - curvature X Y a b) =O[𝓝[≠] 0] fun h : ℝ => h := by
      refine h2.congr' ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with h hh
        rw [quotient_apply_of_ne _ _ _ _ hh, smul_sub, smul_sub, smul_add, smul_smul,
          inv_mul_cancel₀ (pow_ne_zero 2 hh), one_smul]
        abel
      · filter_upwards [self_mem_nhdsWithin] with h hh
        rw [smul_eq_mul]
        field_simp
    have h3 : (fun h : ℝ => quotient X Y a b h - curvature X Y a b) =o[𝓝[≠] 0]
        fun _ : ℝ => (1 : ℝ) := by
      refine h1.trans_isLittleO ?_
      rw [isLittleO_one_iff]
      exact tendsto_id.mono_left nhdsWithin_le_nhds
    rw [isLittleO_one_iff] at h3
    exact tendsto_sub_nhds_zero_iff.mp h3
  exact tendsto_nhds_unique hcont hlim

/-! ### The series logarithm near the identity -/

/-- Coefficients of `log(1+z)/z = Σ_{n ≥ 0} (-1)^n z^n/(n+1)`. -/
noncomputable def logQuotientCoeff (n : ℕ) : ℝ := (-1) ^ n / ((n : ℝ) + 1)

/-- The scalar power series of `log(1+z)/z`. -/
noncomputable def logQuotientSeries (𝔄 : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] :
    FormalMultilinearSeries ℝ 𝔄 𝔄 :=
  FormalMultilinearSeries.ofScalars 𝔄 logQuotientCoeff

/-- `L z = Σ_{n ≥ 0} (-1)^n z^n/(n+1)`, so that `z · L z = log (1 + z)`. -/
noncomputable def logQuotient (z : 𝔄) : 𝔄 := (logQuotientSeries 𝔄).sum z

/-- The series logarithm near the identity: `log (1 + z) = z · L z`. -/
noncomputable def logOneAdd (z : 𝔄) : 𝔄 := z * logQuotient z

theorem norm_logQuotientCoeff (n : ℕ) : ‖logQuotientCoeff n‖ = 1 / ((n : ℝ) + 1) := by
  simp [logQuotientCoeff, norm_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]

/-- The logarithm series has radius of convergence exactly `1`. -/
theorem logQuotientSeries_radius [NormOneClass 𝔄] : (logQuotientSeries 𝔄).radius = 1 := by
  have hr : Tendsto (fun n : ℕ => ‖logQuotientCoeff n‖ / ‖logQuotientCoeff n.succ‖)
      atTop (𝓝 ((1 : NNReal) : ℝ)) := by
    have heq : (fun n : ℕ => ‖logQuotientCoeff n‖ / ‖logQuotientCoeff n.succ‖) =
        fun n : ℕ => 1 + 1 / ((n : ℝ) + 1) := by
      funext n
      rw [norm_logQuotientCoeff, norm_logQuotientCoeff, Nat.succ_eq_add_one, Nat.cast_add,
        Nat.cast_one]
      field_simp
    rw [heq]
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h0
  have := FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto 𝔄 logQuotientCoeff
    (r := 1) one_ne_zero hr
  simpa [logQuotientSeries] using this

theorem hasFPowerSeriesOnBall_logQuotient [NormOneClass 𝔄] :
    HasFPowerSeriesOnBall (logQuotient (𝔄 := 𝔄)) (logQuotientSeries 𝔄) 0 1 := by
  have := (logQuotientSeries 𝔄).hasFPowerSeriesOnBall
    (by rw [logQuotientSeries_radius]; exact one_pos)
  rwa [logQuotientSeries_radius] at this

theorem logQuotient_zero : logQuotient (0 : 𝔄) = 1 := by
  have := FormalMultilinearSeries.ofScalarsSum_zero (E := 𝔄) logQuotientCoeff
  simpa [logQuotient, logQuotientSeries, FormalMultilinearSeries.ofScalarsSum,
    logQuotientCoeff] using this

theorem analyticAt_logQuotient [NormOneClass 𝔄] {z : 𝔄} (hz : ‖z‖ < 1) :
    AnalyticAt ℝ logQuotient z := by
  refine hasFPowerSeriesOnBall_logQuotient.analyticAt_of_mem ?_
  rw [Metric.mem_eball, edist_dist, dist_zero_right, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z) |>.mpr hz

/-! ### The analytic continuation of `h⁻² log P(h)` -/

/-- The paper's `Φ(h) = h⁻² log P(h)`, written in the removable form
`Q(h) · L(h² Q(h))`, which is defined and analytic through `h = 0`. -/
noncomputable def logPlaquette (X Y a b : 𝔄) (h : ℝ) : 𝔄 :=
  quotient X Y a b h * logQuotient (h ^ 2 • quotient X Y a b h)

/-- `Φ(0) = a - b + [X,Y]`. -/
theorem logPlaquette_zero (X Y a b : 𝔄) : logPlaquette X Y a b 0 = curvature X Y a b := by
  simp [logPlaquette, quotient_zero, logQuotient_zero]

/-- `lem:native-plaquette`, analytic-extension clause: `Φ` is analytic at `h = 0`. -/
theorem analyticAt_logPlaquette [NormOneClass 𝔄] (X Y a b : 𝔄) :
    AnalyticAt ℝ (logPlaquette X Y a b) 0 := by
  have hQ := analyticAt_quotient X Y a b
  have hin : AnalyticAt ℝ (fun h : ℝ => h ^ 2 • quotient X Y a b h) 0 :=
    (analyticAt_id.pow 2).smul hQ
  have hL : AnalyticAt ℝ logQuotient (0 : 𝔄) := analyticAt_logQuotient (by simp)
  have hcomp : AnalyticAt ℝ (logQuotient ∘ fun h : ℝ => h ^ 2 • quotient X Y a b h) 0 := by
    refine AnalyticAt.comp (g := logQuotient) (f := fun h : ℝ => h ^ 2 • quotient X Y a b h)
      (x := 0) ?_ hin
    simpa using hL
  exact hQ.mul hcomp

/-- For `h ≠ 0`, `h² Φ(h) = log P(h)` with the series logarithm `log (1 + z) = z · L z`. -/
theorem sq_smul_logPlaquette (X Y a b : 𝔄) {h : ℝ} (hh : h ≠ 0) :
    h ^ 2 • logPlaquette X Y a b h = logOneAdd (product h X Y a b - 1) := by
  unfold logPlaquette logOneAdd
  rw [quotient_apply_of_ne _ _ _ _ hh, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hh), one_smul,
    ← smul_mul_assoc, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hh), one_smul]

/-- Bundled statement of `lem:native-plaquette` (analytic-extension clause): there is a
function `Φ` analytic at `h = 0` with `Φ(0) = a - b + [X,Y]` and
`h² Φ(h) = log (e^{hX} e^{h(Y+ha)} e^{-h(X+hb)} e^{-hY})` for all `h ≠ 0`. -/
theorem exists_analytic_extension [NormOneClass 𝔄] (X Y a b : 𝔄) :
    ∃ Φ : ℝ → 𝔄, AnalyticAt ℝ Φ 0 ∧ Φ 0 = curvature X Y a b ∧
      ∀ h : ℝ, h ≠ 0 → h ^ 2 • Φ h = logOneAdd (product h X Y a b - 1) :=
  ⟨logPlaquette X Y a b, analyticAt_logPlaquette X Y a b, logPlaquette_zero X Y a b,
    fun _ hh => sq_smul_logPlaquette X Y a b hh⟩

end ShiftedPlaquette
end RenewalGeometry
