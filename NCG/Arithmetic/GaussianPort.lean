/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.MassFlux

/-!
# Physical coupling controls a Gaussian port
  (`lemma:physical-coupling-controls-a-gaussian-port`,
   arithmetic manuscript appendix)

For a finite common source (`Ω` finite with weights `λ_ζ ≥ 0`,
Bochner data `x_ζ`, coupled endpoint positions `u_ζ, v_ζ` —
the disclosed finite rendering of the finite measure space), the
port output of the coupled difference `μ_u - μ_v` obeys the boxed
bound.  Following the manuscript proof exactly:

* each coupled pair `(x at u, -x at v)` has vanishing total mass
  and prefix field `±λx·1_{[u∧v, u∨v)}` of `L²` norm
  `λ‖x‖·|u-v|^{1/2}` (`pair_totalMass`, `pair_stepPrefix`,
  `pair_step_norm`), so `thm:mass-flux` gives the per-pair port
  bound `√Λ·λ‖x‖·|u-v|^{1/2}` (`pair_port_bound`);
* Minkowski (the `L²` triangle inequality over the finite source)
  and Cauchy–Schwarz assemble the boxed bound
  `‖𝒞_F(μ_u-μ_v)‖² ≤ Λ·(Σλ‖x‖²)(Σλ|u-v|)`
  (`physical_coupling_port`);
* for the Gaussian port `F = G_𝔞` the flux envelope is
  `Λ = sup (2πξ)²|𝓕G_𝔞|² = 1/(2𝔞e)` (`gauss_flux_bound`, via
  `𝓕G_𝔞(ξ) = e^{-4π²𝔞ξ²}` and `y·e^{-y} ≤ e^{-1}`), giving the
  boxed inequality (`physical_coupling_gaussian_port`).  In the
  manuscript's unitary Fourier convention the envelope carries the
  factor `2π` (cf. `thm:mass-flux`), so the constant reads
  `2π·(1/(2𝔞e)) = π/(𝔞e)` — the boxed `π/(𝔞e)` (disclosed).
-/

open MeasureTheory FourierTransform Complex Finset

namespace NCG

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

section Pair

variable (lam : ℝ) (xv : H) (a b : ℝ)

/-- The coupled-pair atom weights `(+λx at u∧v, -λx at u∨v)` with
the orientation sign. -/
noncomputable def pairD : ℕ → H := fun c =>
  if c = 0 then (if a ≤ b then lam • xv else -(lam • xv))
  else if c = 1 then (if a ≤ b then -(lam • xv) else lam • xv)
  else 0

/-- The coupled-pair atom positions. -/
noncomputable def pairSc : ℕ → ℝ := fun c =>
  if c = 0 then min a b else max a b

set_option linter.unusedSimpArgs false in
lemma pairSc_monotone : Monotone (pairSc a b) := by
  intro m n hmn
  by_cases hm : m = 0
  · by_cases hn : n = 0 <;> simp [pairSc, hm, hn, min_le_max]
  · have hn : n ≠ 0 := by omega
    simp [pairSc, hm, hn]

omit [CompleteSpace H] in
lemma pair_totalMass : totalMass (pairD lam xv a b) 1 = 0 := by
  by_cases h : a ≤ b <;>
    simp [totalMass, pairD, Finset.sum_range_succ, h]

omit [CompleteSpace H] in
/-- The pair port synthesis is the coupled endpoint difference. -/
lemma pair_port (F : ℝ → ℂ) (t : ℝ) :
    portSynthesis (pairD lam xv a b) (pairSc a b) 1 F t
      = lam • (F (t + a) • xv - F (t + b) • xv) := by
  have hexpand : portSynthesis (pairD lam xv a b) (pairSc a b) 1 F t
      = F (t + pairSc a b 0) • pairD lam xv a b 0
        + F (t + pairSc a b 1) • pairD lam xv a b 1 := by
    simp [portSynthesis, Finset.sum_range_succ]
  rw [hexpand]
  by_cases h : a ≤ b
  · rw [show pairSc a b 0 = a from by simp [pairSc, min_eq_left h],
      show pairSc a b 1 = b from by
        simp [pairSc, max_eq_right h],
      show pairD lam xv a b 0 = lam • xv from by simp [pairD, h],
      show pairD lam xv a b 1 = -(lam • xv) from by
        simp [pairD, h],
      smul_neg, smul_sub, smul_comm lam (F (t + a)) xv,
      smul_comm lam (F (t + b)) xv, ← sub_eq_add_neg]
  · have h' : b ≤ a := (not_le.mp h).le
    rw [show pairSc a b 0 = b from by
        simp [pairSc, min_eq_right h'],
      show pairSc a b 1 = a from by simp [pairSc, max_eq_left h'],
      show pairD lam xv a b 0 = -(lam • xv) from by
        simp [pairD, h],
      show pairD lam xv a b 1 = lam • xv from by simp [pairD, h],
      smul_neg, smul_sub, smul_comm lam (F (t + a)) xv,
      smul_comm lam (F (t + b)) xv]
    abel

omit [CompleteSpace H] in
/-- The pair prefix field is the oriented interval indicator. -/
lemma pair_stepPrefix (t : ℝ) :
    stepPrefix (pairD lam xv a b) (pairSc a b) 1 t
      = (Set.Ico (min a b) (max a b)).indicator
          (fun _ => pairD lam xv a b 0) t := by
  simp [stepPrefix, prefixMass, pairSc]

omit [CompleteSpace H] in
/-- The `L²` norm of the pair prefix field:
`‖J‖² = λ²‖x‖²·|u-v|`. -/
lemma pair_step_norm :
    ‖(memLp_stepPrefix (d := pairD lam xv a b)
        (sc := pairSc a b) (N := 1)).toLp
      (stepPrefix (pairD lam xv a b) (pairSc a b) 1)‖ ^ 2
      = ‖pairD lam xv a b 0‖ ^ 2 * |a - b| := by
  rw [norm_toLp_sq]
  have hfun : (fun t => ‖stepPrefix (pairD lam xv a b)
      (pairSc a b) 1 t‖ ^ 2)
      = fun t => (Set.Ico (min a b) (max a b)).indicator
          (fun _ => ‖pairD lam xv a b 0‖ ^ 2) t := by
    funext t
    rw [pair_stepPrefix]
    by_cases ht : t ∈ Set.Ico (min a b) (max a b) <;>
      simp [ht]
  rw [hfun, integral_indicator_const _ measurableSet_Ico,
    smul_eq_mul, Measure.real_def, Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr min_le_max),
    max_sub_min_eq_abs]
  rw [abs_sub_comm b a]
  ring

end Pair

section PortBound

variable (F : ℝ → ℂ)

/-- Per-pair port bound from `thm:mass-flux`:
`‖𝒞_F(pair)‖ ≤ √Λ·λ‖x‖·|u-v|^(1/2)`. -/
lemma pair_port_bound (hF1 : Integrable F) (hF2 : MemLp F 2 volume)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖𝓕 F ξ‖ ^ 2 ≤ Λ)
    (lam : ℝ) (hlam : 0 ≤ lam) (xv : H) (a b : ℝ) :
    (eLpNorm (portSynthesis (pairD lam xv a b) (pairSc a b) 1 F)
        2 volume).toReal
      ≤ Real.sqrt Λ * (lam * ‖xv‖ * Real.sqrt |a - b|) := by
  have hmf := mass_flux (d := pairD lam xv a b)
    (sc := pairSc a b) (N := 1) (F := F)
    (pairSc_monotone a b) hF1 hF2 hΛ0 hΛ
  rw [pair_totalMass, norm_zero, mul_zero, zero_add] at hmf
  rw [← Lp.norm_toLp
    (portSynthesis (pairD lam xv a b) (pairSc a b) 1 F)
    (memLp_portSynthesis (d := pairD lam xv a b)
      (sc := pairSc a b) (N := 1) hF2)]
  refine le_trans hmf ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg Λ)
  have h2 := pair_step_norm lam xv a b
  have hd0 : ‖pairD lam xv a b 0‖ = lam * ‖xv‖ := by
    by_cases h : a ≤ b <;>
      simp [pairD, h, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hlam]
  have h3 : ‖(memLp_stepPrefix (d := pairD lam xv a b)
      (sc := pairSc a b) (N := 1)).toLp
        (stepPrefix (pairD lam xv a b) (pairSc a b) 1)‖
      = Real.sqrt (‖pairD lam xv a b 0‖ ^ 2 * |a - b|) := by
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [h3, hd0, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]

/-- `lemma:physical-coupling-controls-a-gaussian-port`, general
flux-envelope form: for the finite coupled source,
`‖𝒞_F(μ_u - μ_v)‖² ≤ Λ·(Σλ‖x‖²)(Σλ|u-v|)` — Minkowski over the
pairs, then Cauchy–Schwarz. -/
theorem physical_coupling_port (hF1 : Integrable F)
    (hF2 : MemLp F 2 volume) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖𝓕 F ξ‖ ^ 2 ≤ Λ)
    {k : ℕ} (lam : Fin k → ℝ) (hlam : ∀ ζ, 0 ≤ lam ζ)
    (x : Fin k → H) (u v : Fin k → ℝ) :
    (eLpNorm (fun t => ∑ ζ, lam ζ
        • (F (t + u ζ) • x ζ - F (t + v ζ) • x ζ)) 2 volume).toReal
        ^ 2
      ≤ Λ * ((∑ ζ, lam ζ * ‖x ζ‖ ^ 2)
          * (∑ ζ, lam ζ * |u ζ - v ζ|)) := by
  have hfun : (fun t => ∑ ζ, lam ζ
      • (F (t + u ζ) • x ζ - F (t + v ζ) • x ζ))
      = ∑ ζ : Fin k,
          portSynthesis (pairD (lam ζ) (x ζ) (u ζ) (v ζ))
            (pairSc (u ζ) (v ζ)) 1 F := by
    funext t
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun ζ _ =>
      (pair_port (lam ζ) (x ζ) (u ζ) (v ζ) F t).symm
  rw [hfun]
  have hmem : ∀ ζ : Fin k, MemLp (portSynthesis
      (pairD (lam ζ) (x ζ) (u ζ) (v ζ)) (pairSc (u ζ) (v ζ)) 1 F)
      2 volume := fun ζ =>
    memLp_portSynthesis (d := pairD (lam ζ) (x ζ) (u ζ) (v ζ))
      (sc := pairSc (u ζ) (v ζ)) (N := 1) hF2
  have hne : ∀ ζ ∈ (Finset.univ : Finset (Fin k)),
      eLpNorm (portSynthesis (pairD (lam ζ) (x ζ) (u ζ) (v ζ))
        (pairSc (u ζ) (v ζ)) 1 F) 2 volume ≠ ⊤ :=
    fun ζ _ => (hmem ζ).2.ne
  have htri : (eLpNorm (∑ ζ : Fin k, portSynthesis
      (pairD (lam ζ) (x ζ) (u ζ) (v ζ)) (pairSc (u ζ) (v ζ)) 1 F)
      2 volume).toReal
      ≤ ∑ ζ, (eLpNorm (portSynthesis
          (pairD (lam ζ) (x ζ) (u ζ) (v ζ)) (pairSc (u ζ) (v ζ))
          1 F) 2 volume).toReal := by
    refine le_trans (ENNReal.toReal_mono
      (ENNReal.sum_ne_top.mpr hne)
      (eLpNorm_sum_le (fun ζ _ => (hmem ζ).1) (by norm_num))) ?_
    rw [ENNReal.toReal_sum hne]
  have hS : (eLpNorm (∑ ζ : Fin k, portSynthesis
      (pairD (lam ζ) (x ζ) (u ζ) (v ζ)) (pairSc (u ζ) (v ζ)) 1 F)
      2 volume).toReal
      ≤ Real.sqrt Λ
        * ∑ ζ, lam ζ * ‖x ζ‖ * Real.sqrt |u ζ - v ζ| := by
    refine le_trans htri ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun ζ _ =>
      pair_port_bound F hF1 hF2 hΛ0 hΛ (lam ζ) (hlam ζ) (x ζ)
        (u ζ) (v ζ)
  refine le_trans (pow_le_pow_left₀ ENNReal.toReal_nonneg hS 2) ?_
  rw [mul_pow, Real.sq_sqrt hΛ0]
  refine mul_le_mul_of_nonneg_left ?_ hΛ0
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin k))
    (fun ζ => Real.sqrt (lam ζ) * ‖x ζ‖)
    (fun ζ => Real.sqrt (lam ζ) * Real.sqrt |u ζ - v ζ|)
  have e1 : ∀ ζ : Fin k, (Real.sqrt (lam ζ) * ‖x ζ‖)
      * (Real.sqrt (lam ζ) * Real.sqrt |u ζ - v ζ|)
      = lam ζ * ‖x ζ‖ * Real.sqrt |u ζ - v ζ| := by
    intro ζ
    rw [show (Real.sqrt (lam ζ) * ‖x ζ‖)
        * (Real.sqrt (lam ζ) * Real.sqrt |u ζ - v ζ|)
        = (Real.sqrt (lam ζ) * Real.sqrt (lam ζ)) * ‖x ζ‖
          * Real.sqrt |u ζ - v ζ| from by ring,
      Real.mul_self_sqrt (hlam ζ)]
  have e2 : ∀ ζ : Fin k, (Real.sqrt (lam ζ) * ‖x ζ‖) ^ 2
      = lam ζ * ‖x ζ‖ ^ 2 := by
    intro ζ
    rw [mul_pow, Real.sq_sqrt (hlam ζ)]
  have e3 : ∀ ζ : Fin k,
      (Real.sqrt (lam ζ) * Real.sqrt |u ζ - v ζ|) ^ 2
      = lam ζ * |u ζ - v ζ| := by
    intro ζ
    rw [mul_pow, Real.sq_sqrt (hlam ζ),
      Real.sq_sqrt (abs_nonneg _)]
  rw [Finset.sum_congr rfl fun ζ _ => e1 ζ,
    Finset.sum_congr rfl fun ζ _ => e2 ζ,
    Finset.sum_congr rfl fun ζ _ => e3 ζ] at hcs
  exact hcs

end PortBound

section Gauss

/-- The normalized Gaussian port
`G_𝔞(t) = (4π𝔞)^(-1/2) e^(-t²/(4𝔞))`, written with the
`π`-normalized exponent `-πb t²`, `b = (4π𝔞)⁻¹`. -/
noncomputable def gaussF (A : ℝ) : ℝ → ℂ :=
  (((Real.sqrt (4 * Real.pi * A))⁻¹ : ℝ) : ℂ)
    • fun t : ℝ => Complex.exp
        (-(Real.pi : ℂ) * (((4 * Real.pi * A)⁻¹ : ℝ) : ℂ)
          * (t : ℂ) ^ 2)

/-- The Gaussian frequency profile: `𝓕G_𝔞(ξ) = e^(-4π²𝔞ξ²)`. -/
lemma gaussF_fourier (A : ℝ) (hA : 0 < A) (ξ : ℝ) :
    𝓕 (gaussF A) ξ
      = Complex.exp
          (((-(4 * Real.pi ^ 2 * A * ξ ^ 2)) : ℝ) : ℂ) := by
  have hb : (0 : ℝ) < (4 * Real.pi * A)⁻¹ := by positivity
  have hbre : (0 : ℝ)
      < ((((4 * Real.pi * A)⁻¹ : ℝ) : ℂ)).re := by
    simpa using hb
  have hgp := congrFun (fourier_gaussian_pi
    (b := (((4 * Real.pi * A)⁻¹ : ℝ) : ℂ)) hbre) ξ
  have hlin : 𝓕 ((((Real.sqrt (4 * Real.pi * A))⁻¹ : ℝ) : ℂ)
      • fun t : ℝ => Complex.exp
          (-(Real.pi : ℂ) * (((4 * Real.pi * A)⁻¹ : ℝ) : ℂ)
            * (t : ℂ) ^ 2))
      = (((Real.sqrt (4 * Real.pi * A))⁻¹ : ℝ) : ℂ)
        • 𝓕 (fun t : ℝ => Complex.exp
            (-(Real.pi : ℂ) * (((4 * Real.pi * A)⁻¹ : ℝ) : ℂ)
              * (t : ℂ) ^ 2)) :=
    VectorFourier.fourierIntegral_const_smul _ _ _ _ _
  rw [gaussF, hlin, Pi.smul_apply, hgp, smul_eq_mul]
  have hcpow : ((((4 * Real.pi * A)⁻¹ : ℝ) : ℂ)) ^ ((1 : ℂ) / 2)
      = (((Real.sqrt (4 * Real.pi * A))⁻¹ : ℝ) : ℂ) := by
    rw [show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) from by
        push_cast; ring,
      ← Complex.ofReal_cpow hb.le,
      show ((4 * Real.pi * A)⁻¹ : ℝ) ^ ((1 : ℝ) / 2)
        = Real.sqrt ((4 * Real.pi * A)⁻¹) from
        (Real.sqrt_eq_rpow _).symm,
      Real.sqrt_inv]
  rw [hcpow]
  have hs0 : ((((Real.sqrt (4 * Real.pi * A))⁻¹ : ℝ) : ℂ))
      ≠ 0 := by
    have h : Real.sqrt (4 * Real.pi * A) ≠ 0 := by positivity
    exact_mod_cast inv_ne_zero h
  rw [← mul_assoc, mul_one_div, div_self hs0, one_mul]
  congr 1
  have hne : (4 * Real.pi * A : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The dwell form of `y·e^(-y) ≤ e^(-1)`. -/
lemma mul_exp_neg_le (A t : ℝ) (hA : 0 < A) (_ht : 0 ≤ t) :
    t * Real.exp (-(2 * A) * t) ≤ 1 / (2 * A * Real.exp 1) := by
  have h1 : 2 * A * t ≤ Real.exp (2 * A * t - 1) := by
    have := Real.add_one_le_exp (2 * A * t - 1)
    linarith
  have h2 : t * Real.exp (-(2 * A) * t)
      = (1 / (2 * A))
        * ((2 * A * t) * Real.exp (-(2 * A * t))) := by
    field_simp
  rw [h2]
  have h3 : (2 * A * t) * Real.exp (-(2 * A * t))
      ≤ Real.exp (2 * A * t - 1) * Real.exp (-(2 * A * t)) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
  have h4 : Real.exp (2 * A * t - 1) * Real.exp (-(2 * A * t))
      = (Real.exp 1)⁻¹ := by
    rw [← Real.exp_add, show 2 * A * t - 1 + -(2 * A * t) = -1
      by ring, Real.exp_neg]
  calc (1 / (2 * A)) * ((2 * A * t) * Real.exp (-(2 * A * t)))
      ≤ (1 / (2 * A)) * (Real.exp 1)⁻¹ := by
        rw [← h4]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 1 / (2 * A * Real.exp 1) := by
        field_simp

/-- The Gaussian flux envelope:
`(2πξ)²|𝓕G_𝔞(ξ)|² ≤ 1/(2𝔞e)`. -/
lemma gauss_flux_bound (A : ℝ) (hA : 0 < A) (ξ : ℝ) :
    (2 * Real.pi * ξ) ^ 2 * ‖𝓕 (gaussF A) ξ‖ ^ 2
      ≤ 1 / (2 * A * Real.exp 1) := by
  rw [gaussF_fourier A hA ξ, Complex.norm_exp,
    show ((((-(4 * Real.pi ^ 2 * A * ξ ^ 2)) : ℝ) : ℂ)).re
      = -(4 * Real.pi ^ 2 * A * ξ ^ 2) from Complex.ofReal_re _]
  have hsq : Real.exp (-(4 * Real.pi ^ 2 * A * ξ ^ 2)) ^ 2
      = Real.exp (-(2 * A) * ((2 * Real.pi * ξ) ^ 2)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hsq]
  have := mul_exp_neg_le A ((2 * Real.pi * ξ) ^ 2) hA
    (sq_nonneg _)
  linarith

/-- The Gaussian port is integrable. -/
lemma gaussF_integrable (A : ℝ) (hA : 0 < A) :
    Integrable (gaussF A) := by
  have hbre : (0 : ℝ) < ((Real.pi : ℂ)
      * (((4 * Real.pi * A)⁻¹ : ℝ) : ℂ)).re := by
    rw [show (Real.pi : ℂ) * (((4 * Real.pi * A)⁻¹ : ℝ) : ℂ)
        = (((Real.pi * (4 * Real.pi * A)⁻¹ : ℝ)) : ℂ) from by
      push_cast; ring]
    simpa using
      (by positivity : (0 : ℝ) < Real.pi * (4 * Real.pi * A)⁻¹)
  have h := integrable_cexp_neg_mul_sq hbre
  have hfun : (fun t : ℝ => Complex.exp (-(Real.pi : ℂ)
      * (((4 * Real.pi * A)⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ 2))
      = fun x : ℝ => Complex.exp (-((Real.pi : ℂ)
        * (((4 * Real.pi * A)⁻¹ : ℝ) : ℂ)) * (x : ℂ) ^ 2) := by
    funext x
    congr 1
    ring
  rw [gaussF, hfun]
  exact Integrable.smul _ h

/-- The Gaussian port is square-integrable. -/
lemma gaussF_memLp (A : ℝ) (hA : 0 < A) :
    MemLp (gaussF A) 2 volume := by
  have hcont : Continuous (gaussF A) := by
    refine Continuous.const_smul ?_ _
    fun_prop
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have hpt : (fun x : ℝ => ‖gaussF A x‖ ^ 2)
      = fun x : ℝ => ((Real.sqrt (4 * Real.pi * A))⁻¹) ^ 2
        * Real.exp (-(2 * (Real.pi * (4 * Real.pi * A)⁻¹))
            * x ^ 2) := by
    funext x
    rw [gaussF, Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity),
      show (-(Real.pi : ℂ) * (((4 * Real.pi * A)⁻¹ : ℝ) : ℂ)
          * (x : ℂ) ^ 2)
        = ((-(Real.pi * (4 * Real.pi * A)⁻¹ * x ^ 2) : ℝ) : ℂ)
        from by push_cast; ring,
      Complex.norm_exp, Complex.ofReal_re, mul_pow, sq
        (a := Real.exp (-(Real.pi * (4 * Real.pi * A)⁻¹ * x ^ 2))),
      ← Real.exp_add]
    congr 2
    ring
  rw [hpt]
  exact (integrable_exp_neg_mul_sq
    (by positivity : (0 : ℝ)
      < 2 * (Real.pi * (4 * Real.pi * A)⁻¹))).const_mul _

/-- `lemma:physical-coupling-controls-a-gaussian-port`, boxed
Gaussian bound: `‖𝒞_{G_𝔞}(μ_u - μ_v)‖² ≤
(1/(2𝔞e))·(∫‖x‖²dλ)(∫|u-v|dλ)` in the `2π`-normalized Fourier
convention; the manuscript's unitary-convention constant is `2π`
times this envelope, `π/(𝔞e)` (disclosed). -/
theorem physical_coupling_gaussian_port (A : ℝ) (hA : 0 < A)
    {k : ℕ} (lam : Fin k → ℝ) (hlam : ∀ ζ, 0 ≤ lam ζ)
    (x : Fin k → H) (u v : Fin k → ℝ) :
    (eLpNorm (fun t => ∑ ζ, lam ζ
        • (gaussF A (t + u ζ) • x ζ - gaussF A (t + v ζ) • x ζ))
        2 volume).toReal ^ 2
      ≤ 1 / (2 * A * Real.exp 1)
        * ((∑ ζ, lam ζ * ‖x ζ‖ ^ 2)
          * (∑ ζ, lam ζ * |u ζ - v ζ|)) :=
  physical_coupling_port (gaussF A) (gaussF_integrable A hA)
    (gaussF_memLp A hA) (by positivity)
    (fun ξ => gauss_flux_bound A hA ξ) lam hlam x u v

end Gauss

end NCG
