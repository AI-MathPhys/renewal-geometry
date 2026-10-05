/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.NormedAlgebraLogBCH
import RenewalGeometry.Analysis.PlaquetteBCHExpansion
import RenewalGeometry.DiscreteAnalysis.ShiftedPlaquetteLogarithmExact
import RenewalGeometry.DiscreteAnalysis.ShiftedPlaquetteLogarithmUniformExact
import RenewalGeometry.Analysis.StationaryContractionAnalytic

/-!
# Analytic and cubic estimates for the link remainders of the finite Palatini action
(infrastructure for `eq:supp-exact-connection-remainder`, `eq:supp-exact-stationary-connection`;
emergent-spacetime manuscript)

The explicit finite Palatini/link action contains two nonlinear link remainders, both evaluated
in a complete normed `ℝ`-algebra `𝔸` with `‖1‖ = 1` (e.g. real matrices with an operator norm):

* the **Ad-link remainder** `adRem (Y, Z) = Ad_{e^Y} Z − Z − [Y, Z]
  = e^Y Z e^{−Y} − Z − (Y Z − Z Y)`;
* the **plaquette BCH remainder** of a four-link product
  `plaqRem Y = log(e^{Y₀} e^{Y₁} e^{Y₂} e^{Y₃}) − (Y₀ + Y₁ + Y₂ + Y₃) − ½ ∑_{i<j} [Yᵢ, Yⱼ]`,
  with `log = LogBCH.logOnePlus (· − 1)` the principal (Mercator) logarithm.

## Main results

* `logOnePlus_eq_logOneAdd`, `analyticAt_logOnePlus`: the Mercator series agrees with the
  power-series logarithm `ShiftedPlaquette.logOneAdd` on the unit ball, hence is analytic there.
* `analyticAt_expProd4`, `analyticAt_adRem`, `analyticAt_plaqRem`, `analyticOnNhd_plaqRem`:
  both remainders are real-analytic (`plaqRem` on the sup-norm ball of radius `1/16`).
* `norm_adRem_le` (`‖adRem p‖ ≤ 16 ‖p‖³` for `‖p‖ ≤ 1`) and `norm_plaqRem_le`
  (`‖plaqRem Y‖ ≤ 384 ‖Y‖³` for `‖Y‖ ≤ 1/16`): explicit cubic bounds.
* `commTerm_smul`, `smul_adRem_smul`, `smul_plaqRem_smul`: the scaling identities relating the
  rescaled remainders `h⁻² ρ (h A)` to the lattice expressions.
* `exists_adRem_fderiv_lipschitz`, `exists_plaqRem_fderiv_lipschitz` (finite dimension): the
  derivative is `K' r`-Lipschitz on balls of radius `r ≤ r₀`; and the scaled corollaries
  `exists_adRem_scaled_fderiv_lipschitz`, `exists_plaqRem_scaled_fderiv_lipschitz`:
  `‖DN_h(A) − DN_h(A')‖ ≤ K' (h R) ‖A − A'‖` on the `R`-ball for `h R ≤ r₀`, i.e. the
  paper's `N_h = ∂_A r_h` is Lipschitz with constant `C h R`.
* A test instance: the hypotheses hold for `Matrix (Fin 4) (Fin 4) ℝ` with the `ℓ∞` operator
  norm.
-/

namespace RenewalGeometry.LinkRemainder

open NormedSpace Metric

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- On the unit ball the Mercator series `LogBCH.logOnePlus` coincides with the power-series
logarithm `ShiftedPlaquette.logOneAdd z = z · L z`. -/
theorem logOnePlus_eq_logOneAdd {z : 𝔸} (hz : ‖z‖ < 1) :
    LogBCH.logOnePlus z = ShiftedPlaquette.logOneAdd z := by
  have h := ShiftedPlaquette.logOneAdd_smul_eq_tsum z (t := 1) (by simpa using hz)
  rw [one_smul] at h
  rw [h, LogBCH.logOnePlus]
  refine tsum_congr fun n => ?_
  simp [LogBCH.logTerm, ShiftedPlaquette.logTerm, ShiftedPlaquette.logQuotientCoeff]

/-- The principal logarithm `log (1 + z)` is real-analytic on the unit ball. -/
theorem analyticAt_logOnePlus {z : 𝔸} (hz : ‖z‖ < 1) : AnalyticAt ℝ LogBCH.logOnePlus z := by
  have h1 : AnalyticAt ℝ (ShiftedPlaquette.logOneAdd (𝔄 := 𝔸)) z :=
    analyticAt_id.mul (ShiftedPlaquette.analyticAt_logQuotient hz)
  refine h1.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
  exact (logOnePlus_eq_logOneAdd (mem_ball_zero_iff.1 hw)).symm

/-- The ordered four-link product `e^{Y₀} e^{Y₁} e^{Y₂} e^{Y₃}` is real-analytic in
`Y : Fin 4 → 𝔸`. -/
theorem analyticAt_expProd4 (Y : Fin 4 → 𝔸) :
    AnalyticAt ℝ (fun Y : Fin 4 → 𝔸 => LogBCH.expProd [Y 0, Y 1, Y 2, Y 3]) Y := by
  have he : ∀ i : Fin 4, AnalyticAt ℝ (fun Y : Fin 4 → 𝔸 => exp (Y i)) Y := fun i =>
    AnalyticAt.comp (g := exp) (f := fun Z : Fin 4 → 𝔸 => Z i)
      (NormedSpace.exp_analytic (𝕂 := ℝ) (Y i))
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => 𝔸) i).analyticAt Y)
  simp only [LogBCH.expProd_cons, LogBCH.expProd_nil, mul_one]
  exact (he 0).mul ((he 1).mul ((he 2).mul (he 3)))

/-! ### The two link remainders and their analyticity -/

/-- The **Ad-link remainder** `Ad_{e^Y} Z − Z − [Y, Z] = e^Y Z e^{−Y} − Z − (Y Z − Z Y)`. -/
noncomputable def adRem (p : 𝔸 × 𝔸) : 𝔸 :=
  exp p.1 * p.2 * exp (-p.1) - p.2 - (p.1 * p.2 - p.2 * p.1)

/-- The **BCH remainder of a four-link product**:
`log(e^{Y₀} e^{Y₁} e^{Y₂} e^{Y₃}) − ∑ Yᵢ − ½ ∑_{i<j} [Yᵢ, Yⱼ]`. -/
noncomputable def plaqRem (Y : Fin 4 → 𝔸) : 𝔸 :=
  LogBCH.logOnePlus (LogBCH.expProd [Y 0, Y 1, Y 2, Y 3] - 1) - (Y 0 + Y 1 + Y 2 + Y 3) -
    LogBCH.commTerm [Y 0, Y 1, Y 2, Y 3]

/-- The Ad-link remainder is real-analytic everywhere. -/
theorem analyticAt_adRem (p : 𝔸 × 𝔸) : AnalyticAt ℝ adRem p := by
  have h1 : AnalyticAt ℝ (fun p : 𝔸 × 𝔸 => p.1) p := analyticAt_fst
  have h2 : AnalyticAt ℝ (fun p : 𝔸 × 𝔸 => p.2) p := analyticAt_snd
  have he1 : AnalyticAt ℝ (fun p : 𝔸 × 𝔸 => exp p.1) p :=
    AnalyticAt.comp (g := exp) (f := fun p : 𝔸 × 𝔸 => p.1) (exp_analytic (𝕂 := ℝ) _) h1
  have he2 : AnalyticAt ℝ (fun p : 𝔸 × 𝔸 => exp (-p.1)) p :=
    AnalyticAt.comp (g := exp) (f := fun p : 𝔸 × 𝔸 => -p.1) (exp_analytic (𝕂 := ℝ) _) h1.neg
  exact (((he1.mul h2).mul he2).sub h2).sub ((h1.mul h2).sub (h2.mul h1))

/-- Explicit form of the commutator term of a four-element list. -/
theorem commTerm_four (a b c d : 𝔸) :
    LogBCH.commTerm [a, b, c, d] = (1 / 2 : ℝ) • (a * (b + c + d) - (b + c + d) * a) +
      (1 / 2 : ℝ) • (b * (c + d) - (c + d) * b) + (1 / 2 : ℝ) • (c * d - d * c) := by
  simp only [LogBCH.commTerm, List.sum_cons, List.sum_nil, add_zero, sub_self, smul_zero,
    mul_zero, zero_mul, add_assoc]

/-- The plaquette remainder is real-analytic wherever the four-link product lies in the
principal chart `‖P − 1‖ < 1`. -/
theorem analyticAt_plaqRem {Y : Fin 4 → 𝔸}
    (hY : ‖LogBCH.expProd [Y 0, Y 1, Y 2, Y 3] - 1‖ < 1) : AnalyticAt ℝ plaqRem Y := by
  have hlog : AnalyticAt ℝ
      (fun Z : Fin 4 → 𝔸 => LogBCH.logOnePlus (LogBCH.expProd [Z 0, Z 1, Z 2, Z 3] - 1)) Y :=
    AnalyticAt.comp (g := LogBCH.logOnePlus)
      (f := fun Z : Fin 4 → 𝔸 => LogBCH.expProd [Z 0, Z 1, Z 2, Z 3] - 1)
      (analyticAt_logOnePlus hY) ((analyticAt_expProd4 Y).sub analyticAt_const)
  have hp : ∀ i : Fin 4, AnalyticAt ℝ (fun Z : Fin 4 → 𝔸 => Z i) Y := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => 𝔸) i).analyticAt Y
  have hc : AnalyticAt ℝ (fun Z : Fin 4 → 𝔸 => LogBCH.commTerm [Z 0, Z 1, Z 2, Z 3]) Y := by
    simp only [commTerm_four]
    have s3 := ((hp 1).add (hp 2)).add (hp 3)
    have s2 := (hp 2).add (hp 3)
    exact ((((hp 0).mul s3).sub (s3.mul (hp 0))).const_smul (c := (1 / 2 : ℝ)) |>.add
      ((((hp 1).mul s2).sub (s2.mul (hp 1))).const_smul (c := (1 / 2 : ℝ)))).add
      ((((hp 2).mul (hp 3)).sub ((hp 3).mul (hp 2))).const_smul (c := (1 / 2 : ℝ)))
  exact (hlog.sub ((((hp 0).add (hp 1)).add (hp 2)).add (hp 3))).sub hc

/-- `∑ ‖Yᵢ‖ ≤ 4 ‖Y‖` for the sup norm on `Fin 4 → 𝔸`. -/
theorem normSum_four_le (Y : Fin 4 → 𝔸) : LogBCH.normSum [Y 0, Y 1, Y 2, Y 3] ≤ 4 * ‖Y‖ := by
  simp only [LogBCH.normSum_cons, LogBCH.normSum_nil]
  have := fun i => norm_le_pi_norm Y i
  linarith [this 0, this 1, this 2, this 3]

/-- The plaquette remainder is real-analytic on the sup-norm ball of radius `1/16`
(there `∑ ‖Yᵢ‖ < 1/4`, so the product stays in the principal chart). -/
theorem analyticOnNhd_plaqRem : AnalyticOnNhd ℝ (plaqRem (𝔸 := 𝔸)) (ball 0 (1 / 16)) := by
  intro Y hY
  apply analyticAt_plaqRem
  apply LogBCH.PlaquetteBCH.norm_expProd_sub_one_lt
  have h1 := normSum_four_le Y
  have h2 := mem_ball_zero_iff.1 hY
  linarith

/-! ### Cubic bounds -/

/-- `‖a b c‖ ≤ ‖a‖ ‖b‖ ‖c‖`. -/
theorem norm_mul_mul_le (a b c : 𝔸) : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

/-- **Explicit expansion of the Ad-link remainder**: with `R₁ = e^Y − 1 − Y` and
`R₂ = e^{−Y} − 1 + Y`, `adRem (Y, Z) = Z R₂ − Y Z Y + Y Z R₂ + R₁ Z e^{−Y}`. -/
theorem adRem_eq (Y Z : 𝔸) :
    adRem (Y, Z) = Z * (exp (-Y) - 1 - -Y) - Y * Z * Y + Y * Z * (exp (-Y) - 1 - -Y) +
      (exp Y - 1 - Y) * Z * exp (-Y) := by
  simp only [adRem]
  noncomm_ring

/-- **Cubic bound for the Ad-link remainder**: `‖adRem p‖ ≤ 16 ‖p‖³` for `‖p‖ ≤ 1`. -/
theorem norm_adRem_le (p : 𝔸 × 𝔸) (hp : ‖p‖ ≤ 1) : ‖adRem p‖ ≤ 16 * ‖p‖ ^ 3 := by
  obtain ⟨Y, Z⟩ := p
  set t := ‖(Y, Z)‖
  have ht0 : 0 ≤ t := norm_nonneg _
  have hY : ‖Y‖ ≤ t := norm_fst_le (Y, Z)
  have hZ : ‖Z‖ ≤ t := norm_snd_le (Y, Z)
  have hexp : Real.exp ‖Y‖ ≤ 3 := by
    have := Real.exp_le_exp.2 (hY.trans hp)
    have := Real.exp_one_lt_d9
    linarith
  have hY2 : ‖Y‖ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hY 2
  have hR1 : ‖exp Y - 1 - Y‖ ≤ 3 * t ^ 2 := by
    refine (LogBCH.norm_exp_sub_linear_le Y).trans ?_
    nlinarith [Real.exp_pos ‖Y‖, sq_nonneg t]
  have hR2 : ‖exp (-Y) - 1 - -Y‖ ≤ 3 * t ^ 2 := by
    refine (LogBCH.norm_exp_sub_linear_le (-Y)).trans ?_
    rw [norm_neg]
    nlinarith [Real.exp_pos ‖Y‖, sq_nonneg t]
  have hE : ‖exp (-Y)‖ ≤ 3 := (LogBCH.norm_exp_le_real_exp _).trans (by rwa [norm_neg])
  rw [adRem_eq]
  have t1 : ‖Z * (exp (-Y) - 1 - -Y)‖ ≤ t * (3 * t ^ 2) :=
    (norm_mul_le _ _).trans (by gcongr)
  have t2 : ‖Y * Z * Y‖ ≤ t * t * t := (norm_mul_mul_le _ _ _).trans (by gcongr)
  have t3 : ‖Y * Z * (exp (-Y) - 1 - -Y)‖ ≤ t * t * (3 * t ^ 2) :=
    (norm_mul_mul_le _ _ _).trans (by gcongr)
  have t4 : ‖(exp Y - 1 - Y) * Z * exp (-Y)‖ ≤ 3 * t ^ 2 * t * 3 :=
    (norm_mul_mul_le _ _ _).trans (by gcongr)
  have h4 : t * t * (3 * t ^ 2) ≤ 3 * t ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.2 hp)]
  calc ‖Z * (exp (-Y) - 1 - -Y) - Y * Z * Y + Y * Z * (exp (-Y) - 1 - -Y) +
        (exp Y - 1 - Y) * Z * exp (-Y)‖
      ≤ ‖Z * (exp (-Y) - 1 - -Y)‖ + ‖Y * Z * Y‖ + ‖Y * Z * (exp (-Y) - 1 - -Y)‖ +
          ‖(exp Y - 1 - Y) * Z * exp (-Y)‖ := by
        have n1 := norm_add_le (Z * (exp (-Y) - 1 - -Y) - Y * Z * Y +
          Y * Z * (exp (-Y) - 1 - -Y)) ((exp Y - 1 - Y) * Z * exp (-Y))
        have n2 := norm_add_le (Z * (exp (-Y) - 1 - -Y) - Y * Z * Y)
          (Y * Z * (exp (-Y) - 1 - -Y))
        have n3 := norm_sub_le (Z * (exp (-Y) - 1 - -Y)) (Y * Z * Y)
        linarith
    _ ≤ 16 * t ^ 3 := by nlinarith

/-- The plaquette remainder in the form of `LogBCH.norm_log_expProd_sub_bch_le`. -/
theorem plaqRem_eq (Y : Fin 4 → 𝔸) :
    plaqRem Y = LogBCH.logOnePlus (LogBCH.expProd [Y 0, Y 1, Y 2, Y 3] - 1) -
      ([Y 0, Y 1, Y 2, Y 3].sum + LogBCH.commTerm [Y 0, Y 1, Y 2, Y 3]) := by
  simp only [plaqRem, List.sum_cons, List.sum_nil, add_zero]
  abel

/-- **Cubic bound for the plaquette remainder**: `‖plaqRem Y‖ ≤ 384 ‖Y‖³` for
`‖Y‖ ≤ 1/16` (second-order BCH with `∑ ‖Yᵢ‖ ≤ 4 ‖Y‖ ≤ 1/4`). -/
theorem norm_plaqRem_le (Y : Fin 4 → 𝔸) (hY : ‖Y‖ ≤ 1 / 16) : ‖plaqRem Y‖ ≤ 384 * ‖Y‖ ^ 3 := by
  have hs := normSum_four_le Y
  have hs0 := LogBCH.normSum_nonneg [Y 0, Y 1, Y 2, Y 3]
  rw [plaqRem_eq]
  refine (LogBCH.norm_log_expProd_sub_bch_le _ (by linarith)).trans ?_
  have := pow_le_pow_left₀ hs0 hs 3
  nlinarith

/-! ### Scaling identities -/

/-- The sum of a rescaled list is the rescaled sum. -/
theorem sum_map_smul (h : ℝ) (L : List 𝔸) : (L.map (h • ·)).sum = h • L.sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih, smul_add]

/-- The commutator term is quadratic: `commTerm (h • L) = h² • commTerm L`. -/
theorem commTerm_smul (h : ℝ) (L : List 𝔸) :
    LogBCH.commTerm (L.map (h • ·)) = h ^ 2 • LogBCH.commTerm L := by
  induction L with
  | nil => simp [LogBCH.commTerm]
  | cons x L ih =>
    simp only [List.map_cons, LogBCH.commTerm, ih, sum_map_smul, smul_mul_assoc, mul_smul_comm,
      smul_smul]
    module

/-- Four-list version of `commTerm_smul`. -/
theorem commTerm_four_smul (h : ℝ) (a b c d : 𝔸) :
    LogBCH.commTerm [h • a, h • b, h • c, h • d] = h ^ 2 • LogBCH.commTerm [a, b, c, d] := by
  simpa using commTerm_smul h [a, b, c, d]

/-- The Ad-link remainder at a rescaled pair. -/
theorem adRem_smul (h : ℝ) (a b : 𝔸) :
    adRem (h • a, h • b) = h • (exp (h • a) * b * exp (-(h • a)) - b - h • (a * b - b * a)) := by
  simp only [adRem, smul_sub, mul_smul_comm, smul_mul_assoc, smul_smul]

/-- `(h²)⁻¹ h = h⁻¹` for `h ≠ 0`. -/
theorem inv_sq_mul_self {h : ℝ} (hh : h ≠ 0) : (h ^ 2)⁻¹ * h = h⁻¹ := by
  rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ hh, mul_one]

/-- **Scaling of the Ad-link remainder**: for `h ≠ 0`,
`h⁻² adRem (h a, h b) = h⁻¹ (e^{h a} b e^{−h a} − b − h [a, b])`. -/
theorem smul_adRem_smul {h : ℝ} (hh : h ≠ 0) (a b : 𝔸) :
    (h ^ 2)⁻¹ • adRem (h • a, h • b) =
      h⁻¹ • (exp (h • a) * b * exp (-(h • a)) - b - h • (a * b - b * a)) := by
  rw [adRem_smul, smul_smul, inv_sq_mul_self hh]

/-- **Scaling of the plaquette remainder**: for `h ≠ 0`,
`h⁻² plaqRem (h X) = h⁻² log(e^{h X₀} ⋯ e^{h X₃}) − h⁻¹ ∑ Xᵢ − ½ ∑_{i<j} [Xᵢ, Xⱼ]`. -/
theorem smul_plaqRem_smul {h : ℝ} (hh : h ≠ 0) (X : Fin 4 → 𝔸) :
    (h ^ 2)⁻¹ • plaqRem (h • X) =
      (h ^ 2)⁻¹ • LogBCH.logOnePlus (LogBCH.expProd [h • X 0, h • X 1, h • X 2, h • X 3] - 1) -
        h⁻¹ • (X 0 + X 1 + X 2 + X 3) - LogBCH.commTerm [X 0, X 1, X 2, X 3] := by
  simp only [plaqRem, Pi.smul_apply, commTerm_four_smul, smul_sub, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 hh), one_smul, ← smul_add, inv_sq_mul_self hh]

/-! ### Lipschitz derivatives -/

/-- The Ad-link remainder is differentiable. -/
theorem differentiable_adRem : Differentiable ℝ (adRem (𝔸 := 𝔸)) := fun p =>
  (analyticAt_adRem p).differentiableAt

/-- The plaquette remainder is differentiable on the ball of radius `1/16`. -/
theorem differentiableOn_plaqRem : DifferentiableOn ℝ (plaqRem (𝔸 := 𝔸)) (ball 0 (1 / 16)) :=
  fun Y hY => (analyticOnNhd_plaqRem Y hY).differentiableAt.differentiableWithinAt

/-- **Lipschitz derivative of the Ad-link remainder** (finite dimension): on balls of radius
`r ≤ r₀ < 1`, `‖D adRem(p) − D adRem(p')‖ ≤ K' r ‖p − p'‖`, and `‖D adRem(p)‖ ≤ K' ‖p‖²`. -/
theorem exists_adRem_fderiv_lipschitz [FiniteDimensional ℝ 𝔸] :
    ∃ r₀, 0 < r₀ ∧ r₀ < 1 ∧ ∃ K', 0 ≤ K' ∧
      (∀ r, 0 ≤ r → r ≤ r₀ → ∀ p p' : 𝔸 × 𝔸, ‖p‖ ≤ r → ‖p'‖ ≤ r →
        ‖fderiv ℝ adRem p - fderiv ℝ adRem p'‖ ≤ K' * r * ‖p - p'‖) ∧
      (∀ p : 𝔸 × 𝔸, ‖p‖ ≤ r₀ → ‖fderiv ℝ adRem p‖ ≤ K' * ‖p‖ ^ 2) :=
  StationaryContraction.cubic_remainder_fderiv_lipschitz_of_analyticOnNhd one_pos
    (fun p _ => analyticAt_adRem p) (fun p hp => norm_adRem_le p (mem_ball_zero_iff.1 hp).le)

/-- **Lipschitz derivative of the plaquette remainder** (finite dimension): on balls of radius
`r ≤ r₀ < 1/16`, `‖D plaqRem(Y) − D plaqRem(Y')‖ ≤ K' r ‖Y − Y'‖`, and
`‖D plaqRem(Y)‖ ≤ K' ‖Y‖²`. -/
theorem exists_plaqRem_fderiv_lipschitz [FiniteDimensional ℝ 𝔸] :
    ∃ r₀, 0 < r₀ ∧ r₀ < 1 / 16 ∧ ∃ K', 0 ≤ K' ∧
      (∀ r, 0 ≤ r → r ≤ r₀ → ∀ Y Y' : Fin 4 → 𝔸, ‖Y‖ ≤ r → ‖Y'‖ ≤ r →
        ‖fderiv ℝ plaqRem Y - fderiv ℝ plaqRem Y'‖ ≤ K' * r * ‖Y - Y'‖) ∧
      (∀ Y : Fin 4 → 𝔸, ‖Y‖ ≤ r₀ → ‖fderiv ℝ plaqRem Y‖ ≤ K' * ‖Y‖ ^ 2) :=
  StationaryContraction.cubic_remainder_fderiv_lipschitz_of_analyticOnNhd (by norm_num)
    analyticOnNhd_plaqRem (fun Y hY => norm_plaqRem_le Y (mem_ball_zero_iff.1 hY).le)

/-- **Scaled Ad-link remainder** (`eq:supp-exact-connection-remainder`): for `0 < h`,
`0 ≤ R`, `h R ≤ r₀`, the derivative of `A ↦ h⁻² adRem (h A)` is `K' (h R)`-Lipschitz on the
closed `R`-ball. -/
theorem exists_adRem_scaled_fderiv_lipschitz [FiniteDimensional ℝ 𝔸] :
    ∃ r₀, 0 < r₀ ∧ ∃ K', 0 ≤ K' ∧ ∀ h R : ℝ, 0 < h → 0 ≤ R → h * R ≤ r₀ →
      ∀ A A' : 𝔸 × 𝔸, ‖A‖ ≤ R → ‖A'‖ ≤ R →
        ‖fderiv ℝ (fun B : 𝔸 × 𝔸 => (h ^ 2)⁻¹ • adRem (h • B)) A -
          fderiv ℝ (fun B : 𝔸 × 𝔸 => (h ^ 2)⁻¹ • adRem (h • B)) A'‖ ≤
          K' * (h * R) * ‖A - A'‖ := by
  obtain ⟨r₀, hr₀, hlt, K', hK', hLip, -⟩ := exists_adRem_fderiv_lipschitz (𝔸 := 𝔸)
  exact ⟨r₀, hr₀, K', hK', fun h R hh hR hhR A A' hA hA' =>
    StationaryContraction.norm_fderiv_scaled_sub_le differentiable_adRem.differentiableOn hlt
      hLip hh hR hhR hA hA'⟩

/-- **Scaled plaquette remainder** (`eq:supp-exact-connection-remainder`): for `0 < h`,
`0 ≤ R`, `h R ≤ r₀`, the derivative of `A ↦ h⁻² plaqRem (h A)` is `K' (h R)`-Lipschitz on the
closed `R`-ball. -/
theorem exists_plaqRem_scaled_fderiv_lipschitz [FiniteDimensional ℝ 𝔸] :
    ∃ r₀, 0 < r₀ ∧ ∃ K', 0 ≤ K' ∧ ∀ h R : ℝ, 0 < h → 0 ≤ R → h * R ≤ r₀ →
      ∀ A A' : Fin 4 → 𝔸, ‖A‖ ≤ R → ‖A'‖ ≤ R →
        ‖fderiv ℝ (fun B : Fin 4 → 𝔸 => (h ^ 2)⁻¹ • plaqRem (h • B)) A -
          fderiv ℝ (fun B : Fin 4 → 𝔸 => (h ^ 2)⁻¹ • plaqRem (h • B)) A'‖ ≤
          K' * (h * R) * ‖A - A'‖ := by
  obtain ⟨r₀, hr₀, hlt, K', hK', hLip, -⟩ := exists_plaqRem_fderiv_lipschitz (𝔸 := 𝔸)
  exact ⟨r₀, hr₀, K', hK', fun h R hh hR hhR A A' hA hA' =>
    StationaryContraction.norm_fderiv_scaled_sub_le differentiableOn_plaqRem hlt
      hLip hh hR hhR hA hA'⟩

/-! ### Test instance: `4 × 4` real matrices with the `ℓ∞` operator norm -/

section MatrixTest

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The standing hypotheses hold for `4 × 4` real matrices with the `ℓ∞` operator norm. -/
example : NormOneClass (Matrix (Fin 4) (Fin 4) ℝ) ∧ CompleteSpace (Matrix (Fin 4) (Fin 4) ℝ) ∧
    FiniteDimensional ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The scaled Lipschitz theorem applies to the plaquette remainder of `4 × 4` real matrices
(the statement is elaborated through the theorem, since restating it would require the operator
norm on continuous linear maps built from the local matrix-norm instances). -/
example := exists_plaqRem_scaled_fderiv_lipschitz (𝔸 := Matrix (Fin 4) (Fin 4) ℝ)

/-- The scaled Lipschitz theorem applies to the Ad-link remainder of `4 × 4` real matrices. -/
example := exists_adRem_scaled_fderiv_lipschitz (𝔸 := Matrix (Fin 4) (Fin 4) ℝ)

end MatrixTest

end RenewalGeometry.LinkRemainder
