/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.ShiftedPlaquetteLogarithmExact

/-!
# Shifted plaquette logarithm: the analytic branch and uniform derivative bounds
  (`lem:native-plaquette`, Einstein–Standard-Model action-closure manuscript)

This file closes the two clauses of `lem:native-plaquette` left open in
`ShiftedPlaquetteLogarithmExact`.

* **The series logarithm is the analytic branch of `log` near the identity.**
  For `‖z‖ < 1` in a real Banach algebra, `exp (logOneAdd z) = 1 + z`
  (`exp_logOneAdd`).  The proof differentiates
  `t ↦ exp (-log(1 + t z)) (1 + t z)` on `|t| < R` (`1 < R`, `R ‖z‖ < 1`): the
  logarithm series is differentiated termwise (`hasDerivAt_logSeries`), its
  derivative is `z (1 + t z)⁻¹` by the Neumann series, and `exp` is
  differentiated along the commuting family `t ↦ log(1 + t z)`
  (`hasDerivAt_exp_of_commute`, which only uses `hasFDerivAt_exp_zero` and
  `exp_add_of_commute`, so no commutativity of the algebra is needed).
  Consequently `exp (h² Φ(h)) = P(h)` for the removable-quotient map `Φ` of
  `lem:native-plaquette` whenever `‖P(h) - 1‖ < 1` (`exp_sq_smul_logPlaquette`).

* **Uniform bounds for all fixed-order derivatives on compact argument sets.**
  Writing `exp u = 1 + u + u² E(u)` with the entire function
  `E(u) = Σ_{n ≥ 0} u^n/(n+2)!` (`expRemainder`, `exp_eq_expRemainder`), the
  shifted product is `P = Π_i (1 + h w_i)` with `w_i = v_i + h v_i² E(h v_i)`,
  `(v_i) = (X, Y + ha, -(X + hb), -Y)`, and `Σ_i v_i = h (a - b)`.  Expanding the
  product gives the *explicit* removable quotient
  `P(h) - 1 = h² Q(h; X, Y, a, b)` (`jointQuotient`, `product_sub_one_eq`),
  a polynomial in `h, X, Y, a, b` and the `E(h v_i)`, hence jointly analytic in
  `(h, X, Y, a, b) ∈ ℝ × 𝔄⁴` (`analyticAt_jointQuotient`).  The joint map
  `Φ(h; X, Y, a, b) = Q · L(h² Q)` (`jointLogPlaquette`) agrees with
  `logPlaquette` for every `h` (`jointLogPlaquette_eq`), is analytic on the open
  set `‖h² Q‖ < 1 ⊇ {0} × 𝔄⁴` (`analyticAt_jointLogPlaquette`), and therefore
  every iterated Fréchet derivative (in `h` *and* in the parameters `X, Y, a, b`)
  is bounded uniformly on `[-h₀, h₀] × K` for every compact `K ⊆ 𝔄⁴` and some
  `h₀ > 0` (`exists_uniform_iteratedFDeriv_bound`), which is the second sentence
  of `lem:native-plaquette`.

Scoped hypotheses (disclosed): `𝔄` is a real Banach algebra with `‖1‖ = 1`
(`NormOneClass`), as in the analyticity clauses of the companion file.
-/

open NormedSpace Asymptotics Filter Topology

namespace RenewalGeometry
namespace ShiftedPlaquette

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

/-! ### Differentiating `exp` along a commuting family -/

/-- If `ℓ(s)` and `ℓ(t)` commute for all `s, t`, then `exp ∘ ℓ` has derivative
`exp (ℓ t) · ℓ'(t)`; only `hasFDerivAt_exp_zero` and `exp_add_of_commute` are used. -/
theorem hasDerivAt_exp_of_commute {ℓ : ℝ → 𝔄} {ℓ' : 𝔄} {t : ℝ}
    (hcomm : ∀ s, Commute (ℓ s) (ℓ t)) (hℓ : HasDerivAt ℓ ℓ' t) :
    HasDerivAt (fun s => exp (ℓ s)) (exp (ℓ t) * ℓ') t := by
  let +nondep : NormedAlgebra ℚ 𝔄 := .restrictScalars ℚ ℝ 𝔄
  have hsplit : ∀ s, exp (ℓ s) = exp (ℓ t) * exp (ℓ s - ℓ t) := by
    intro s
    rw [← exp_add_of_commute ((hcomm s).symm.sub_right (Commute.refl (ℓ t))),
      add_sub_cancel]
  have hinner : HasDerivAt (fun s => ℓ s - ℓ t) ℓ' t := hℓ.sub_const _
  have hexp0 : HasFDerivAt exp (1 : 𝔄 →L[ℝ] 𝔄) ((fun s => ℓ s - ℓ t) t) := by
    simp only [sub_self]
    exact hasFDerivAt_exp_zero
  have hexp : HasDerivAt (fun s => exp (ℓ s - ℓ t)) ℓ' t := by
    have := HasFDerivAt.comp_hasDerivAt t hexp0 hinner
    simpa [Function.comp_def] using this
  have := hexp.const_mul (exp (ℓ t))
  refine this.congr_of_eventuallyEq ?_
  filter_upwards with s
  exact hsplit s

/-! ### The logarithm series in a scalar direction -/

variable [NormOneClass 𝔄]

/-- The `n`-th term of `log (1 + t z) = Σ_n c_n (t z)^{n+1}`. -/
noncomputable def logTerm (z : 𝔄) (n : ℕ) (t : ℝ) : 𝔄 := logQuotientCoeff n • (t • z) ^ (n + 1)

/-- The termwise derivative `(-t)^n z^{n+1}`. -/
noncomputable def logTermDeriv (z : 𝔄) (n : ℕ) (t : ℝ) : 𝔄 := (-t) ^ n • z ^ (n + 1)

theorem logQuotient_eq_tsum (z : 𝔄) : logQuotient z = ∑' n, logQuotientCoeff n • z ^ n :=
  FormalMultilinearSeries.ofScalars_sum_eq logQuotientCoeff z

theorem hasSum_logQuotient {z : 𝔄} (hz : ‖z‖ < 1) :
    HasSum (fun n => logQuotientCoeff n • z ^ n) (logQuotient z) := by
  have hmem : z ∈ Metric.eball (0 : 𝔄) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z)).mpr hz
  have := hasFPowerSeriesOnBall_logQuotient (𝔄 := 𝔄) |>.hasSum hmem
  simpa [logQuotientSeries, FormalMultilinearSeries.ofScalars_apply_eq] using this

theorem logOneAdd_smul_eq_tsum (z : 𝔄) {t : ℝ} (ht : |t| * ‖z‖ < 1) :
    logOneAdd (t • z) = ∑' n, logTerm z n t := by
  have hs : Summable fun n => logQuotientCoeff n • (t • z) ^ n :=
    (hasSum_logQuotient (by rwa [norm_smul, Real.norm_eq_abs])).summable
  unfold logOneAdd logTerm
  rw [logQuotient_eq_tsum, ← hs.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [mul_smul_comm, pow_succ']

theorem hasDerivAt_logTerm (z : 𝔄) (n : ℕ) (t : ℝ) :
    HasDerivAt (logTerm z n) (logTermDeriv z n t) t := by
  have h1 : logTerm z n = fun t => (logQuotientCoeff n * t ^ (n + 1)) • z ^ (n + 1) := by
    funext t
    simp [logTerm, smul_pow, smul_smul]
  rw [h1]
  have hd := ((hasDerivAt_pow (n + 1) t).const_mul (logQuotientCoeff n)).smul_const (z ^ (n + 1))
  refine hd.congr_deriv ?_
  unfold logTermDeriv logQuotientCoeff
  congr 1
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  rw [neg_pow]
  ring

theorem norm_logTermDeriv_le (z : 𝔄) (n : ℕ) {t R : ℝ} (ht : |t| ≤ R) :
    ‖logTermDeriv z n t‖ ≤ ‖z‖ * (R * ‖z‖) ^ n := by
  unfold logTermDeriv
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_neg]
  have hR : 0 ≤ R := (abs_nonneg t).trans ht
  calc |t| ^ n * ‖z ^ (n + 1)‖ ≤ R ^ n * ‖z‖ ^ (n + 1) := by
        gcongr
        exact norm_pow_le z (n + 1)
    _ = ‖z‖ * (R * ‖z‖) ^ n := by ring

/-- The termwise derivative sums to `z · Σ_n (-(t z))^n`. -/
theorem tsum_logTermDeriv (z : 𝔄) {t : ℝ} (ht : ‖-(t • z)‖ < 1) :
    ∑' n, logTermDeriv z n t = z * ∑' n, (-(t • z)) ^ n := by
  rw [← (summable_geometric_of_norm_lt_one ht).tsum_mul_left]
  refine tsum_congr fun n => ?_
  unfold logTermDeriv
  rw [← neg_smul, smul_pow, mul_smul_comm, pow_succ']

/-- Termwise differentiation of `t ↦ log (1 + t z)` on `|t| < R` with `R ‖z‖ < 1`. -/
theorem hasDerivAt_logSeries (z : 𝔄) {R : ℝ} (hR : R * ‖z‖ < 1) {t : ℝ}
    (ht : t ∈ Metric.ball (0 : ℝ) R) :
    HasDerivAt (fun s => ∑' n, logTerm z n s) (z * ∑' n, (-(t • z)) ^ n) t := by
  have hR0 : 0 < R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    exact (abs_nonneg t).trans_lt ht
  have hu : Summable fun n : ℕ => ‖z‖ * (R * ‖z‖) ^ n :=
    (summable_geometric_of_lt_one (by positivity) hR).mul_left _
  have h0 : Summable fun n => logTerm z n 0 := by
    have : (fun n => logTerm z n 0) = fun _ => 0 := by
      funext n
      simp [logTerm]
    rw [this]
    exact summable_zero
  have htz : ‖-(t • z)‖ < 1 := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    rw [norm_neg, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖z‖ ≤ R * ‖z‖ := by gcongr
      _ < 1 := hR
  rw [← tsum_logTermDeriv z htz]
  refine hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball 0 R).isPreconnected
    (fun n y _ => hasDerivAt_logTerm z n y) (fun n y hy => ?_) (Metric.mem_ball_self hR0) h0 ht
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
  exact norm_logTermDeriv_le z n hy.le

/-- Every value `log (1 + s z)` commutes with `z`. -/
theorem commute_logSeries (z : 𝔄) (s : ℝ) : Commute z (∑' n, logTerm z n s) := by
  refine Commute.tsum_right _ fun n => ?_
  unfold logTerm
  exact (((Commute.refl z).smul_right s).pow_right (n + 1)).smul_right _

theorem commute_logSeries_logSeries (z : 𝔄) (s t : ℝ) :
    Commute (∑' n, logTerm z n s) (∑' n, logTerm z n t) := by
  refine Commute.tsum_left _ fun n => ?_
  unfold logTerm
  exact (((commute_logSeries z t).smul_left s).pow_left (n + 1)).smul_left _

/-- `lem:native-plaquette`, identification of the branch: the series logarithm inverts `exp`
near the identity, `exp (log (1 + z)) = 1 + z` for `‖z‖ < 1`. -/
theorem exp_logOneAdd {z : 𝔄} (hz : ‖z‖ < 1) : exp (logOneAdd z) = 1 + z := by
  let +nondep : NormedAlgebra ℚ 𝔄 := .restrictScalars ℚ ℝ 𝔄
  set R : ℝ := 2 / (1 + ‖z‖) with hR
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hR1 : 1 < R := by
    rw [hR, lt_div_iff₀ (by positivity)]
    linarith
  have hRz : R * ‖z‖ < 1 := by
    rw [hR, div_mul_eq_mul_div, div_lt_one (by positivity)]
    linarith
  set ℓ : ℝ → 𝔄 := fun s => ∑' n, logTerm z n s with hℓ
  set H : ℝ → 𝔄 := fun s => exp (-ℓ s) * (1 + s • z) with hH
  have hcomm : ∀ s t, Commute (-ℓ s) (-ℓ t) := fun s t =>
    (commute_logSeries_logSeries z s t).neg_left.neg_right
  -- derivative of `H` on the ball
  have hderiv : ∀ t ∈ Metric.ball (0 : ℝ) R, HasDerivAt H 0 t := by
    intro t ht
    have hℓ' : HasDerivAt (fun s => -ℓ s) (-(z * ∑' n, (-(t • z)) ^ n)) t :=
      (hasDerivAt_logSeries z hRz ht).neg
    have hE : HasDerivAt (fun s => exp (-ℓ s)) (exp (-ℓ t) * -(z * ∑' n, (-(t • z)) ^ n)) t :=
      hasDerivAt_exp_of_commute (fun s => hcomm s t) hℓ'
    have hlin : HasDerivAt (fun s : ℝ => 1 + s • z) z t := by
      have := ((hasDerivAt_id t).smul_const z).const_add (1 : 𝔄)
      simpa using this
    have hprod := hE.mul hlin
    have htz : ‖-(t • z)‖ < 1 := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      rw [norm_neg, norm_smul, Real.norm_eq_abs]
      calc |t| * ‖z‖ ≤ R * ‖z‖ := by gcongr
        _ < 1 := hRz
    have hgeom : (∑' n, (-(t • z)) ^ n) * (1 + t • z) = 1 := by
      have := geom_series_mul_neg (-(t • z)) htz
      rwa [sub_neg_eq_add] at this
    have hprod' : HasDerivAt H
        (exp (-ℓ t) * -(z * ∑' n, (-(t • z)) ^ n) * (1 + t • z) + exp (-ℓ t) * z) t := hprod
    refine hprod'.congr_deriv ?_
    rw [mul_neg, neg_mul, mul_assoc, mul_assoc, hgeom, mul_one, neg_add_cancel]
  have hdiff : DifferentiableOn ℝ H (Metric.ball 0 R) := fun t ht =>
    (hderiv t ht).differentiableAt.differentiableWithinAt
  have hzero : (Metric.ball (0 : ℝ) R).EqOn (deriv H) 0 := fun t ht => (hderiv t ht).deriv
  have hconst := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball 0 R).isPreconnected
    hdiff hzero (x := 1) (y := 0) (by
      rw [Metric.mem_ball, dist_zero_right, norm_one]; exact hR1)
    (Metric.mem_ball_self (by linarith))
  have hℓ0 : ℓ 0 = 0 := by
    simp [hℓ, logTerm]
  have hH0 : H 0 = 1 := by
    simp [hH, hℓ0]
  have hH1 : H 1 = exp (-ℓ 1) * (1 + z) := by
    simp [hH]
  rw [hH1, hH0] at hconst
  have hℓ1 : logOneAdd z = ℓ 1 := by
    have := logOneAdd_smul_eq_tsum z (t := 1) (by simpa using hz)
    simpa using this
  rw [hℓ1]
  calc exp (ℓ 1) = exp (ℓ 1) * (exp (-ℓ 1) * (1 + z)) := by rw [hconst, mul_one]
    _ = (exp (ℓ 1) * exp (-ℓ 1)) * (1 + z) := by rw [mul_assoc]
    _ = 1 + z := by
        rw [← exp_add_of_commute (Commute.refl (ℓ 1)).neg_right, add_neg_cancel, exp_zero,
          one_mul]

/-- `lem:native-plaquette`, branch clause for the plaquette: whenever the product is within
distance `1` of the identity, `exp (h² Φ(h)) = P(h)`, so `Φ` is `h⁻²` times the analytic
branch of the logarithm of the plaquette. -/
theorem exp_sq_smul_logPlaquette (X Y a b : 𝔄) {h : ℝ}
    (hP : ‖product h X Y a b - 1‖ < 1) :
    exp (h ^ 2 • logPlaquette X Y a b h) = product h X Y a b := by
  by_cases hh : h = 0
  · subst hh
    simp [product_zero]
  · rw [sq_smul_logPlaquette X Y a b hh, exp_logOneAdd hP, add_sub_cancel]


/-! ### The entire remainder `E(u) = Σ_{n ≥ 0} u^n/(n+2)!`, `exp u = 1 + u + u² E(u)` -/

/-- Coefficients `1/(n+2)!`. -/
noncomputable def expRemCoeff (n : ℕ) : ℝ := ((n + 2).factorial : ℝ)⁻¹

/-- The scalar power series of `E(u) = Σ u^n/(n+2)!`. -/
noncomputable def expRemSeries (𝔄 : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] :
    FormalMultilinearSeries ℝ 𝔄 𝔄 :=
  FormalMultilinearSeries.ofScalars 𝔄 expRemCoeff

/-- `E(u) = Σ_{n ≥ 0} u^n/(n+2)!`, so that `exp u = 1 + u + u² E(u)`. -/
noncomputable def expRemainder (u : 𝔄) : 𝔄 := (expRemSeries 𝔄).sum u

theorem expRemCoeff_ne_zero (n : ℕ) : expRemCoeff n ≠ 0 := by
  unfold expRemCoeff
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- The remainder series is entire. -/
theorem expRemSeries_radius : (expRemSeries 𝔄).radius = ⊤ := by
  refine FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto 𝔄 _
    (Eventually.of_forall expRemCoeff_ne_zero) ?_
  have heq : (fun n : ℕ => ‖expRemCoeff n.succ‖ / ‖expRemCoeff n‖) =
      fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ) + 1) := by
    funext n
    unfold expRemCoeff
    rw [Nat.succ_eq_add_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
      abs_of_pos (by positivity), show n + 1 + 2 = (n + 2) + 1 by ring, Nat.factorial_succ]
    push_cast
    field_simp
  rw [heq]
  exact (tendsto_add_atTop_iff_nat 2).mpr tendsto_one_div_add_atTop_nhds_zero_nat

theorem hasSum_expRemainder (u : 𝔄) :
    HasSum (fun n => expRemCoeff n • u ^ n) (expRemainder u) := by
  have := (expRemSeries 𝔄).hasSum (x := u)
    (by rw [expRemSeries_radius]; exact Metric.mem_eball.mpr (edist_lt_top _ _))
  unfold expRemainder expRemSeries at this ⊢
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq] using this

/-- `E` is analytic everywhere. -/
@[fun_prop]
theorem analyticAt_expRemainder (u : 𝔄) : AnalyticAt ℝ expRemainder u := by
  have h := (expRemSeries 𝔄).hasFPowerSeriesOnBall
    (by rw [expRemSeries_radius]; exact ENNReal.zero_lt_top)
  exact h.analyticAt_of_mem
    (by rw [expRemSeries_radius]; exact Metric.mem_eball.mpr (edist_lt_top _ _))

theorem expRemainder_zero : expRemainder (0 : 𝔄) = (2 : ℝ)⁻¹ • 1 := by
  have := FormalMultilinearSeries.ofScalarsSum_zero (E := 𝔄) expRemCoeff
  simpa [expRemainder, expRemSeries, FormalMultilinearSeries.ofScalarsSum, expRemCoeff,
    Nat.factorial] using this

/-- `exp u = 1 + u + u² E(u)`. -/
theorem exp_eq_expRemainder (u : 𝔄) : exp u = 1 + u + u ^ 2 * expRemainder u := by
  have hs : Summable fun n : ℕ => ((n.factorial : ℝ)⁻¹) • u ^ n :=
    expSeries_summable' (𝕂 := ℝ) u
  have hexp : exp u = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • u ^ n := by
    rw [exp_eq_tsum (𝕂 := ℝ)]
  rw [hexp, ← hs.sum_add_tsum_nat_add 2]
  have hshift : (fun n : ℕ => (((n + 2).factorial : ℝ)⁻¹) • u ^ (n + 2)) =
      fun n => u ^ 2 * (expRemCoeff n • u ^ n) := by
    funext n
    rw [pow_add, (Commute.pow_pow_self u n 2).eq, mul_smul_comm]
    rfl
  rw [hshift, ((hasSum_expRemainder u).mul_left (u ^ 2)).tsum_eq]
  simp [Finset.sum_range_succ, Nat.factorial]

/-! ### The explicit removable quotient -/

/-- `w(h, v) = v + h v² E(h v)`, so that `exp (h v) = 1 + h w(h, v)`. -/
noncomputable def linkExp (h : ℝ) (v : 𝔄) : 𝔄 := v + h • (v ^ 2 * expRemainder (h • v))

theorem exp_smul_eq_linkExp (h : ℝ) (v : 𝔄) : exp (h • v) = 1 + h • linkExp h v := by
  rw [exp_eq_expRemainder, linkExp, smul_add, smul_smul, smul_pow, ← pow_two, smul_mul_assoc,
    add_assoc]

/-- The explicit removable quotient `Q(h; X, Y, a, b)` with `P(h) - 1 = h² Q`: with
`(v_i) = (X, Y + ha, -(X + hb), -Y)` and `w_i = w(h, v_i)`,
`Q = (a - b) + Σ_i v_i² E(h v_i) + Σ_{i<j} w_i w_j + h Σ_{i<j<k} w_i w_j w_k + h² w₁w₂w₃w₄`. -/
noncomputable def quotientPoly (h : ℝ) (X Y a b : 𝔄) : 𝔄 :=
  (a - b) +
    (X ^ 2 * expRemainder (h • X) + (Y + h • a) ^ 2 * expRemainder (h • (Y + h • a)) +
      (-(X + h • b)) ^ 2 * expRemainder (h • -(X + h • b)) + (-Y) ^ 2 * expRemainder (h • -Y)) +
    (linkExp h X * linkExp h (Y + h • a) + linkExp h X * linkExp h (-(X + h • b)) +
      linkExp h X * linkExp h (-Y) + linkExp h (Y + h • a) * linkExp h (-(X + h • b)) +
      linkExp h (Y + h • a) * linkExp h (-Y) + linkExp h (-(X + h • b)) * linkExp h (-Y)) +
    h • (linkExp h X * linkExp h (Y + h • a) * linkExp h (-(X + h • b)) +
      linkExp h X * linkExp h (Y + h • a) * linkExp h (-Y) +
      linkExp h X * linkExp h (-(X + h • b)) * linkExp h (-Y) +
      linkExp h (Y + h • a) * linkExp h (-(X + h • b)) * linkExp h (-Y)) +
    h ^ 2 • (linkExp h X * linkExp h (Y + h • a) * linkExp h (-(X + h • b)) * linkExp h (-Y))

/-- Expansion of a product of four factors `1 + h w_i`. -/
theorem four_product_expansion (h : ℝ) (w₁ w₂ w₃ w₄ : 𝔄) :
    (1 + h • w₁) * (1 + h • w₂) * (1 + h • w₃) * (1 + h • w₄) - 1 =
      h • (w₁ + w₂ + w₃ + w₄) +
        h ^ 2 • (w₁ * w₂ + w₁ * w₃ + w₁ * w₄ + w₂ * w₃ + w₂ * w₄ + w₃ * w₄) +
        h ^ 3 • (w₁ * w₂ * w₃ + w₁ * w₂ * w₄ + w₁ * w₃ * w₄ + w₂ * w₃ * w₄) +
        h ^ 4 • (w₁ * w₂ * w₃ * w₄) := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc]
  module

/-- The sum of the four `w_i` carries a factor `h`. -/
theorem linkExp_sum (h : ℝ) (X Y a b : 𝔄) :
    linkExp h X + linkExp h (Y + h • a) + linkExp h (-(X + h • b)) + linkExp h (-Y) =
      h • ((a - b) +
        (X ^ 2 * expRemainder (h • X) + (Y + h • a) ^ 2 * expRemainder (h • (Y + h • a)) +
          (-(X + h • b)) ^ 2 * expRemainder (h • -(X + h • b)) +
          (-Y) ^ 2 * expRemainder (h • -Y))) := by
  simp only [linkExp]
  module

/-- The product in the `exp (h v_i)` form. -/
theorem product_eq_exp_smul (h : ℝ) (X Y a b : 𝔄) :
    product h X Y a b =
      exp (h • X) * exp (h • (Y + h • a)) * exp (h • -(X + h • b)) * exp (h • -Y) := by
  unfold product
  congr 3
  · congr 1
    rw [smul_add, smul_smul, pow_two]
  · congr 1
    rw [smul_neg, smul_add, smul_smul, pow_two, neg_add, sub_eq_add_neg]
  · rw [smul_neg]

/-- `lem:native-plaquette`, explicit removable quotient: `P(h) - 1 = h² Q(h; X, Y, a, b)`. -/
theorem product_sub_one_eq (h : ℝ) (X Y a b : 𝔄) :
    product h X Y a b - 1 = h ^ 2 • quotientPoly h X Y a b := by
  rw [product_eq_exp_smul, exp_smul_eq_linkExp, exp_smul_eq_linkExp, exp_smul_eq_linkExp,
    exp_smul_eq_linkExp, four_product_expansion, linkExp_sum, quotientPoly]
  simp only [smul_add, smul_smul]
  module

/-- The double difference quotient of `ShiftedPlaquetteLogarithmExact` is the explicit
quotient `Q`, for every `h` (including `h = 0`). -/
theorem quotient_eq_quotientPoly (X Y a b : 𝔄) (h : ℝ) :
    quotient X Y a b h = quotientPoly h X Y a b := by
  by_cases hh : h = 0
  · subst hh
    rw [quotient_zero]
    simp only [quotientPoly, linkExp, curvature, zero_smul, add_zero, expRemainder_zero,
      mul_smul_comm, mul_one, sq, neg_mul, mul_neg, neg_neg, zero_pow two_ne_zero]
    module
  · rw [quotient_apply_of_ne _ _ _ _ hh, product_sub_one_eq, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hh), one_smul]

/-! ### Joint analyticity in `(h, X, Y, a, b)` and uniform derivative bounds -/

/-- The explicit quotient as a function of the joint variable `(h, X, Y, a, b)`. -/
noncomputable def jointQuotient (p : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄) : 𝔄 :=
  quotientPoly p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

/-- The map `Φ(h; X, Y, a, b) = Q · L(h² Q)` of `lem:native-plaquette` as a function of the joint
variable `(h, X, Y, a, b)`. -/
noncomputable def jointLogPlaquette (p : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄) : 𝔄 :=
  jointQuotient p * logQuotient (p.1 ^ 2 • jointQuotient p)

/-- `Φ` of the companion file is the joint map evaluated at `(h, X, Y, a, b)`. -/
theorem jointLogPlaquette_eq (X Y a b : 𝔄) (h : ℝ) :
    logPlaquette X Y a b h = jointLogPlaquette (h, X, Y, a, b) := by
  simp only [logPlaquette, jointLogPlaquette, jointQuotient, quotient_eq_quotientPoly]

attribute [local fun_prop] analyticAt_fst analyticAt_snd

/-- The explicit quotient is jointly analytic in `(h, X, Y, a, b)`. -/
theorem analyticAt_jointQuotient (p : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄) : AnalyticAt ℝ jointQuotient p := by
  unfold jointQuotient quotientPoly linkExp
  fun_prop

theorem continuous_jointQuotient : Continuous (jointQuotient (𝔄 := 𝔄)) :=
  continuous_iff_continuousAt.mpr fun p => (analyticAt_jointQuotient p).continuousAt

/-- `lem:native-plaquette`, joint analyticity: `Φ` is analytic in `(h, X, Y, a, b)` wherever
`‖h² Q‖ < 1`, in particular on a neighbourhood of `{0} × 𝔄⁴`. -/
theorem analyticAt_jointLogPlaquette {p : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄}
    (hp : ‖p.1 ^ 2 • jointQuotient p‖ < 1) : AnalyticAt ℝ jointLogPlaquette p := by
  have hQ := analyticAt_jointQuotient p
  have hin : AnalyticAt ℝ (fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 => q.1 ^ 2 • jointQuotient q) p := by
    have h1 : AnalyticAt ℝ (fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 => q.1 ^ 2) p := analyticAt_fst.pow 2
    exact h1.smul hQ
  have hL : AnalyticAt ℝ logQuotient (p.1 ^ 2 • jointQuotient p) := analyticAt_logQuotient hp
  have hcomp : AnalyticAt ℝ (logQuotient ∘ fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 =>
      q.1 ^ 2 • jointQuotient q) p :=
    AnalyticAt.comp (g := logQuotient) (f := fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 =>
      q.1 ^ 2 • jointQuotient q) (x := p) hL hin
  exact hQ.mul hcomp

/-- The open set on which `Φ` is analytic. -/
theorem isOpen_jointDomain :
    IsOpen {p : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 | ‖p.1 ^ 2 • jointQuotient p‖ < 1} :=
  isOpen_lt ((continuous_fst.pow 2).smul continuous_jointQuotient).norm continuous_const

/-- `lem:native-plaquette`, uniform-derivative clause: for every order `k` and every compact set
`K` of parameters `(X, Y, a, b)` there are `h₀ > 0` and `C` such that all `k`-th Fréchet
derivatives of `Φ` in the joint variable `(h, X, Y, a, b)` (so in particular all `h`-derivatives
and all parameter derivatives of order `k`) are bounded by `C` for `|h| ≤ h₀` and
`(X, Y, a, b) ∈ K`. -/
theorem exists_uniform_iteratedFDeriv_bound (k : ℕ) {K : Set (𝔄 × 𝔄 × 𝔄 × 𝔄)}
    (hK : IsCompact K) :
    ∃ h₀ > 0, ∃ C : ℝ, ∀ h : ℝ, |h| ≤ h₀ → ∀ q ∈ K,
      ‖iteratedFDeriv ℝ k jointLogPlaquette (h, q)‖ ≤ C := by
  set U := {p : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 | ‖p.1 ^ 2 • jointQuotient p‖ < 1} with hU
  have hUo : IsOpen U := isOpen_jointDomain
  have hsub : ({(0 : ℝ)} : Set ℝ) ×ˢ K ⊆ U := by
    rintro ⟨h, q⟩ ⟨hh, _⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    simp [hU]
  obtain ⟨u, v, huo, -, hu0, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hUo hsub
  obtain ⟨h₀, hh₀, hball⟩ := Metric.isOpen_iff.mp huo 0 (hu0 rfl)
  refine ⟨h₀ / 2, by positivity, ?_⟩
  have hSc : IsCompact (Metric.closedBall (0 : ℝ) (h₀ / 2) ×ˢ K) :=
    (isCompact_closedBall _ _).prod hK
  have hSU : Metric.closedBall (0 : ℝ) (h₀ / 2) ×ˢ K ⊆ U := fun p hp =>
    huv ⟨hball (Metric.closedBall_subset_ball (half_lt_self hh₀) hp.1), hKv hp.2⟩
  have hcd : ContDiffOn ℝ (k : WithTop ℕ∞) jointLogPlaquette U := fun p hp =>
    (analyticAt_jointLogPlaquette hp).contDiffAt.contDiffWithinAt
  have hcont : ContinuousOn (iteratedFDeriv ℝ k jointLogPlaquette) U :=
    (hcd.continuousOn_iteratedFDerivWithin le_rfl hUo.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen k hUo).symm
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (hcont.mono hSU)
  refine ⟨C, fun h hh q hq => hC (h, q) ⟨?_, hq⟩⟩
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact hh

/-- Bundled statement of `lem:native-plaquette`: a jointly analytic map `Φ` on a neighbourhood of
`{0} × 𝔄⁴` with `Φ(0; X, Y, a, b) = a - b + [X, Y]`, `h² Φ(h) = log P(h)` for all `h ≠ 0`
(series logarithm, which inverts `exp` near the identity by `exp_logOneAdd`), and uniform bounds
on compact parameter sets for all fixed-order derivatives at small `h`. -/
theorem exists_joint_analytic_extension :
    ∃ Φ : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 → 𝔄,
      (∀ X Y a b : 𝔄, AnalyticAt ℝ Φ (0, X, Y, a, b)) ∧
      (∀ X Y a b : 𝔄, Φ (0, X, Y, a, b) = curvature X Y a b) ∧
      (∀ X Y a b : 𝔄, ∀ h : ℝ, h ≠ 0 →
        h ^ 2 • Φ (h, X, Y, a, b) = logOneAdd (product h X Y a b - 1)) ∧
      (∀ k : ℕ, ∀ K : Set (𝔄 × 𝔄 × 𝔄 × 𝔄), IsCompact K →
        ∃ h₀ > 0, ∃ C : ℝ, ∀ h : ℝ, |h| ≤ h₀ → ∀ q ∈ K, ‖iteratedFDeriv ℝ k Φ (h, q)‖ ≤ C) := by
  refine ⟨jointLogPlaquette, fun X Y a b => analyticAt_jointLogPlaquette (by simp), ?_, ?_, ?_⟩
  · intro X Y a b
    rw [← jointLogPlaquette_eq, logPlaquette_zero]
  · intro X Y a b h hh
    rw [← jointLogPlaquette_eq, sq_smul_logPlaquette X Y a b hh]
  · intro k K hK
    exact exists_uniform_iteratedFDeriv_bound k hK

end ShiftedPlaquette
end RenewalGeometry
