/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EasyExact00

/-!
# Easy exact records, batch 01 (Gran-Tensor manuscript)

Exact formalizations of the following manuscript records:

* `thm:NS-energy-neutral-payment` — the exact energy-neutral
  viscosity-shorted payment (NSE.11–NSE.15): the minimum correction in the
  physical carrier `e^⊥` removing the positive critical stock derivative,
  its constraint identities, the attained constrained minimum with
  uniqueness, the ambient/neutral Pythagoras split, and the `δ_c` ratio.
* `cth:NS-ambient-critical-underprice` — the explicit two-dimensional
  witness on which the ambient payment distance is `ε` while the
  energy-neutral payment distance is `1`, with `δ_c = ε`.
* `cor:NS-centred-work-one-source` — the collinear decomposition
  (NSE.17–NSE.18) of the physical work projection into viscosity-matching
  and record-payment terms.
* `prop:NS-common-phase-space-panel` — the joint polarized phase-space
  resolution (NST.15): `∑ E_{j,α}^* E_{j,α} = I` in the strong sense, the
  polarized scalar split of `-Re⟪c,q⟫`, its absolute convergence, and the
  finite marginal witness showing marginals do not determine mixed
  occurrence.
* `prop:NS-paid-stress-selector` — the occupied-selector orthogonal split
  (NSR.15), the Fisher-coordinate Lipschitz bound, the translated-stress
  integral bound (NSR.16), and the scalar amplitude-vs-modulus obstruction.
* `cth:GT-lifetime-no-momentum-ancestry` — equal lifetime packets
  (energy marginal, survival kernel, lifetime density, Green matrix) with
  distinct momentum ancestry (JT.5), plus a fully explicit witness.
* `prop:GT-source-metric-transport` — the primitive source/metric defect
  decomposition (SMET.29), the normalized horizon defect (SMET.30), and the
  additive telescopes of the primitive defects.
* `cth:GT-static-residual-follower` — the explicit `2×2` packet with
  `R_ent = 1` and `R_dyn = 0` under the coupled clock.
* `cth:GT-source-metric-collapses` — the three explicit leverage-collapse
  witnesses: coordinate collapse, reserve collapse with attained minimum
  control energy, and normalized cyclic-geometry collapse.
* `thm:GT-source-action-covariance` — the variational unit-action
  covariance (SMET.5), coordinate invariance (SMET.6), the polar reserve
  factorization (SMET.7–SMET.9), spectral transport, and the reserve
  window (SMET.10).
* `cor:GT-low-island-cofinal-carrier` — summable cofinal landing from
  relative low-island moments (LIR.9), with the finite low-island floor and
  tail bounds (LIR.5, LIR.8) derived from the theorem data.

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset
open scoped ComplexOrder

namespace NCG

/-! ### Exact energy-neutral viscosity-shorted payment

Records `thm:NS-energy-neutral-payment`, `cth:NS-ambient-critical-underprice`
and `cor:NS-centred-work-one-source` (NSE.11–NSE.18).

Rendering: the theorem is a statement of Hilbert geometry about the vectors
`e = A^{1/4}u`, `v = A^{3/4}u`, `c = A^{-1/4}B(u)` on the critical carrier;
it is rendered on an arbitrary complex inner-product space with the
energy-null incidence `Re⟪c,e⟫ = 0` (NSE.4), the record positivity
`q_c > 0`, and `ν ≥ 0` as hypotheses — exactly the data the manuscript
carries at this point.  All scalar quantities (`κ̄`, `ψ`, `𝒟_c`, `𝒱_c`,
`Φ_c`, `q_c`, `δ_c`) are the manuscript formulas (NSE.2–NSE.10); the
minimality claim (NSE.13) is an `IsLeast` with a uniqueness clause. -/

section ComplexReBridges

open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `Complex.re` form of the inner-product self pairing. -/
theorem cre_inner_self (x : H) : (⟪x, x⟫).re = ‖x‖ ^ 2 := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rwa [RCLike.re_to_complex] at h

/-- `Complex.re` symmetry of the inner product. -/
theorem cre_inner_symm (x y : H) : (⟪x, y⟫).re = (⟪y, x⟫).re := by
  have h := inner_re_symm (𝕜 := ℂ) x y
  rwa [RCLike.re_to_complex, RCLike.re_to_complex] at h

/-- `Complex.re` form of the norm-of-sum expansion. -/
theorem cnorm_add_sq (x y : H) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * (⟪x, y⟫).re + ‖y‖ ^ 2 := by
  have h := norm_add_sq (𝕜 := ℂ) x y
  rwa [RCLike.re_to_complex] at h

/-- `Complex.re` form of the norm-of-difference expansion. -/
theorem cnorm_sub_sq (x y : H) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * (⟪x, y⟫).re + ‖y‖ ^ 2 := by
  have h := norm_sub_sq (𝕜 := ℂ) x y
  rwa [RCLike.re_to_complex] at h

end ComplexReBridges

section EnergyNeutralPayment

open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace NSPay

/-- The critical frequency centre `κ̄ = Re⟪e,v⟫/‖e‖²` (NSE.6). -/
noncomputable def centre (e v : H) : ℝ := (⟪e, v⟫).re / ‖e‖ ^ 2

/-- The centred target `ψ = v - κ̄ e` (NSE.7). -/
noncomputable def centred (e v : H) : H := v - (centre e v : ℂ) • e

/-- The dispersion action `𝒱_c = ‖ψ‖²` (NSE.9). -/
noncomputable def vres (e v : H) : ℝ := ‖centred e v‖ ^ 2

/-- The critical work `Φ_c = -Re⟪c,v⟫` (NSE.2). -/
noncomputable def work (c v : H) : ℝ := -(⟪c, v⟫).re

/-- The critical record rate `q_c = (Φ_c - ν 𝒟_c)₊` (NSE.3). -/
noncomputable def record (ν : ℝ) (c v : H) : ℝ := max (work c v - ν * ‖v‖ ^ 2) 0

/-- The energy-neutral payment `c_c^pay = -(q_c/𝒱_c) ψ` (NSE.11). -/
noncomputable def payment (ν : ℝ) (e c v : H) : H :=
  -((record ν c v / vres e v : ℝ) : ℂ) • centred e v

/-- The ambient unconstrained payment `g_c^pay = -(q_c/𝒟_c) v` (NSE.14). -/
noncomputable def ambient (ν : ℝ) (c v : H) : H :=
  -((record ν c v / ‖v‖ ^ 2 : ℝ) : ℂ) • v

/-- The incidence defect ratio `δ_c = (𝒱_c/𝒟_c)^{1/2}` (NSE.10). -/
noncomputable def deltaC (e v : H) : ℝ := Real.sqrt (vres e v / ‖v‖ ^ 2)

/-- The physical work projection `c_c^wrk = -(Φ_c/𝒱_c) ψ` (NSE.16). -/
noncomputable def workProj (e c v : H) : H :=
  -((work c v / vres e v : ℝ) : ℂ) • centred e v

/-- The work-orthogonal remainder `c_c^0 = c - c_c^wrk` (NSE.16). -/
noncomputable def workResid (e c v : H) : H := c - workProj e c v

/-- Real part of a pairing against a real negative multiple. -/
theorem re_inner_neg_ofReal_smul_left (r : ℝ) (x y : H) :
    (⟪(-(r : ℂ)) • x, y⟫).re = -(r * (⟪x, y⟫).re) := by
  rw [inner_smul_left, map_neg, Complex.conj_ofReal, neg_mul, Complex.neg_re,
    Complex.re_ofReal_mul]

/-- Real part of a pairing with a real negative multiple on the right. -/
theorem re_inner_neg_ofReal_smul_right (r : ℝ) (x y : H) :
    (⟪x, (-(r : ℂ)) • y⟫).re = -(r * (⟪x, y⟫).re) := by
  rw [inner_smul_right, neg_mul, Complex.neg_re, Complex.re_ofReal_mul]

/-- Real part of a pairing with a real multiple on the right. -/
theorem re_inner_ofReal_smul_right (r : ℝ) (x y : H) :
    (⟪x, (r : ℂ) • y⟫).re = r * (⟪x, y⟫).re := by
  rw [inner_smul_right, Complex.re_ofReal_mul]

/-- Real part of a pairing with a real multiple on the left. -/
theorem re_inner_ofReal_smul_left (r : ℝ) (x y : H) :
    (⟪(r : ℂ) • x, y⟫).re = r * (⟪x, y⟫).re := by
  rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]

/-- The centred target is orthogonal to the energy vector (first half of
NSE.8). -/
theorem re_inner_centred_left (e v : H) (he : e ≠ 0) :
    (⟪e, centred e v⟫).re = 0 := by
  have hne : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  unfold centred
  rw [inner_sub_right, Complex.sub_re, re_inner_ofReal_smul_right,
    cre_inner_self, centre, div_mul_cancel₀ _ hne, sub_self]

/-- Orthogonality with the roles swapped. -/
theorem re_inner_centred_right (e v : H) (he : e ≠ 0) :
    (⟪centred e v, e⟫).re = 0 := by
  rw [cre_inner_symm]
  exact re_inner_centred_left e v he

/-- The real pairing of the centred target against the full target is the
dispersion action `𝒱_c`. -/
theorem re_inner_centred_target (e v : H) (he : e ≠ 0) :
    (⟪centred e v, v⟫).re = vres e v := by
  have hpsipsi : (⟪centred e v, centred e v⟫).re = vres e v :=
    cre_inner_self (centred e v)
  have hsplit : (⟪centred e v, v⟫ : ℂ)
      = ⟪centred e v, centred e v⟫ + ⟪centred e v, (centre e v : ℂ) • e⟫ := by
    rw [← inner_add_right]
    congr 1
    unfold centred
    abel
  rw [hsplit, Complex.add_re, hpsipsi, re_inner_ofReal_smul_right,
    re_inner_centred_right e v he, mul_zero, add_zero]

/-- Subtracting the centred multiple of `e` does not change the work of an
energy-null source (second half of NSE.8): `Φ_c = -Re⟪c,ψ⟫`. -/
theorem work_eq_centred (e c v : H) (hce : (⟪c, e⟫).re = 0) :
    work c v = -(⟪c, centred e v⟫).re := by
  unfold centred work
  rw [inner_sub_right, Complex.sub_re, re_inner_ofReal_smul_right, hce,
    mul_zero, sub_zero]

/-- The target norm splits over the centred decomposition:
`𝒟_c = 𝒱_c + κ̄²‖e‖²`; in particular `𝒱_c ≤ 𝒟_c`. -/
theorem target_normsq_split (e v : H) (he : e ≠ 0) :
    ‖v‖ ^ 2 = vres e v + (centre e v) ^ 2 * ‖e‖ ^ 2 := by
  have hv : v = centred e v + (centre e v : ℂ) • e := by
    unfold centred; abel
  have h0 : (⟪centred e v, (centre e v : ℂ) • e⟫).re = 0 := by
    rw [re_inner_ofReal_smul_right, re_inner_centred_right e v he, mul_zero]
  calc ‖v‖ ^ 2 = ‖centred e v + (centre e v : ℂ) • e‖ ^ 2 := by rw [← hv]
    _ = ‖centred e v‖ ^ 2 + 2 * (⟪centred e v, (centre e v : ℂ) • e⟫).re
        + ‖(centre e v : ℂ) • e‖ ^ 2 := cnorm_add_sq _ _
    _ = vres e v + (centre e v) ^ 2 * ‖e‖ ^ 2 := by
        rw [h0, norm_smul]
        unfold vres
        rw [mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        ring

/-- On the record-positive set the dispersion action is strictly positive
(`δ_c > 0`, the branch guard for NSE.11). -/
theorem vres_pos (ν : ℝ) (e c v : H) (_he : e ≠ 0) (hce : (⟪c, e⟫).re = 0)
    (hν : 0 ≤ ν) (hq : 0 < record ν c v) : 0 < vres e v := by
  by_contra hcon
  push Not at hcon
  have hV0 : vres e v = 0 := le_antisymm hcon (by unfold vres; positivity)
  have hpsi : centred e v = 0 := by
    unfold vres at hV0
    rwa [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at hV0
  have hwork : work c v = 0 := by
    rw [work_eq_centred e c v hce, hpsi, inner_zero_right]
    simp
  have harg : work c v - ν * ‖v‖ ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg hν (sq_nonneg ‖v‖)]
  have hzero : record ν c v = 0 := max_eq_right harg
  linarith

/-- On the record-positive set the target itself is nonzero: `𝒟_c > 0`. -/
theorem dissip_pos (ν : ℝ) (e c v : H) (he : e ≠ 0) (hce : (⟪c, e⟫).re = 0)
    (hν : 0 ≤ ν) (hq : 0 < record ν c v) : 0 < ‖v‖ ^ 2 := by
  have h1 := vres_pos ν e c v he hce hν hq
  have h2 := target_normsq_split e v he
  nlinarith [sq_nonneg (centre e v), sq_nonneg ‖e‖]

/-- The record rate is nonnegative. -/
theorem record_nonneg (ν : ℝ) (c v : H) : 0 ≤ record ν c v := le_max_right _ _

/-- **NSE.12**: the payment is energy neutral and removes exactly the
positive critical stock derivative. -/
theorem payment_constraints (ν : ℝ) (e c v : H) (he : e ≠ 0)
    (hce : (⟪c, e⟫).re = 0) (hν : 0 ≤ ν) (hq : 0 < record ν c v) :
    (⟪payment ν e c v, e⟫).re = 0 ∧
      -(⟪payment ν e c v, v⟫).re = record ν c v := by
  have hV := vres_pos ν e c v he hce hν hq
  constructor
  · unfold payment
    rw [re_inner_neg_ofReal_smul_left, re_inner_centred_right e v he,
      mul_zero, neg_zero]
  · unfold payment
    rw [re_inner_neg_ofReal_smul_left, re_inner_centred_target e v he,
      neg_neg, div_mul_cancel₀ _ (ne_of_gt hV)]

/-- The squared payment norm is `q_c²/𝒱_c` (first equality in NSE.13). -/
theorem payment_normsq (ν : ℝ) (e c v : H) (he : e ≠ 0)
    (hce : (⟪c, e⟫).re = 0) (hν : 0 ≤ ν) (hq : 0 < record ν c v) :
    ‖payment ν e c v‖ ^ 2 = record ν c v ^ 2 / vres e v := by
  have hV := vres_pos ν e c v he hce hν hq
  unfold payment
  rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (record_nonneg ν c v) hV.le), mul_pow]
  unfold vres at *
  field_simp

/-- **NSE.13**: the payment attains the minimum squared norm among all
energy-neutral corrections removing the record rate. -/
theorem payment_isLeast (ν : ℝ) (e c v : H) (he : e ≠ 0)
    (hce : (⟪c, e⟫).re = 0) (hν : 0 ≤ ν) (hq : 0 < record ν c v) :
    IsLeast {r : ℝ | ∃ x : H, (⟪x, e⟫).re = 0 ∧ -(⟪x, v⟫).re = record ν c v ∧
      r = ‖x‖ ^ 2} (record ν c v ^ 2 / vres e v) := by
  have hV := vres_pos ν e c v he hce hν hq
  constructor
  · exact ⟨payment ν e c v, (payment_constraints ν e c v he hce hν hq).1,
      (payment_constraints ν e c v he hce hν hq).2,
      (payment_normsq ν e c v he hce hν hq).symm⟩
  · rintro r ⟨x, hxe, hxv, rfl⟩
    have hxpsi : -(⟪x, centred e v⟫).re = record ν c v := by
      unfold centred
      rw [inner_sub_right, Complex.sub_re, re_inner_ofReal_smul_right, hxe,
        mul_zero, sub_zero]
      exact hxv
    have hCS : |(⟪x, centred e v⟫).re| ≤ ‖x‖ * ‖centred e v‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    have hrec : record ν c v ≤ ‖x‖ * ‖centred e v‖ := by
      calc record ν c v = -(⟪x, centred e v⟫).re := hxpsi.symm
        _ ≤ |(⟪x, centred e v⟫).re| := neg_le_abs _
        _ ≤ ‖x‖ * ‖centred e v‖ := hCS
    have hVnorm : ‖centred e v‖ ^ 2 = vres e v := rfl
    rw [div_le_iff₀ hV, ← hVnorm]
    nlinarith [norm_nonneg x, norm_nonneg (centred e v), hrec,
      record_nonneg ν c v]

/-- The minimizer in NSE.13 is unique: any energy-neutral correction of
minimal norm removing the record rate equals the payment. -/
theorem payment_unique (ν : ℝ) (e c v : H) (he : e ≠ 0)
    (hce : (⟪c, e⟫).re = 0) (hν : 0 ≤ ν) (hq : 0 < record ν c v)
    (x : H) (hxe : (⟪x, e⟫).re = 0) (hxv : -(⟪x, v⟫).re = record ν c v)
    (hmin : ‖x‖ ^ 2 = record ν c v ^ 2 / vres e v) :
    x = payment ν e c v := by
  have hV := vres_pos ν e c v he hce hν hq
  have hxpsi : (⟪x, centred e v⟫).re = -record ν c v := by
    unfold centred
    rw [inner_sub_right, Complex.sub_re, re_inner_ofReal_smul_right, hxe,
      mul_zero, sub_zero]
    linarith
  have hzero : ‖x - payment ν e c v‖ ^ 2 = 0 := by
    have hexp : ‖x - payment ν e c v‖ ^ 2
        = ‖x‖ ^ 2 - 2 * (⟪x, payment ν e c v⟫).re + ‖payment ν e c v‖ ^ 2 :=
      cnorm_sub_sq _ _
    have hcross : (⟪x, payment ν e c v⟫).re = record ν c v ^ 2 / vres e v := by
      unfold payment
      rw [re_inner_neg_ofReal_smul_right, hxpsi]
      field_simp
    rw [hexp, hcross, hmin, payment_normsq ν e c v he hce hν hq]
    ring
  have hnorm := (pow_eq_zero_iff two_ne_zero).mp hzero
  rw [norm_eq_zero, sub_eq_zero] at hnorm
  exact hnorm

/-- The squared norm of the ambient payment is `q_c²/𝒟_c`. -/
theorem ambient_normsq (ν : ℝ) (c v : H) (hD : 0 < ‖v‖ ^ 2) :
    ‖ambient ν c v‖ ^ 2 = record ν c v ^ 2 / ‖v‖ ^ 2 := by
  unfold ambient
  rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (record_nonneg ν c v) hD.le), mul_pow]
  field_simp

/-- **NSE.14**: the Pythagoras split of the payment over the ambient
payment. -/
theorem payment_pythagoras (ν : ℝ) (e c v : H) (he : e ≠ 0)
    (hce : (⟪c, e⟫).re = 0) (hν : 0 ≤ ν) (hq : 0 < record ν c v) :
    ‖payment ν e c v‖ ^ 2 = ‖ambient ν c v‖ ^ 2 +
      ‖payment ν e c v - ambient ν c v‖ ^ 2 := by
  have hV := vres_pos ν e c v he hce hν hq
  have hD := dissip_pos ν e c v he hce hν hq
  have hcross : (⟪payment ν e c v, ambient ν c v⟫).re
      = record ν c v ^ 2 / ‖v‖ ^ 2 := by
    unfold payment ambient
    rw [inner_smul_left, map_neg, Complex.conj_ofReal, neg_mul, Complex.neg_re,
      Complex.re_ofReal_mul, re_inner_neg_ofReal_smul_right,
      re_inner_centred_target e v he]
    field_simp
  have hsub : ‖payment ν e c v - ambient ν c v‖ ^ 2
      = ‖payment ν e c v‖ ^ 2 - 2 * (⟪payment ν e c v, ambient ν c v⟫).re
        + ‖ambient ν c v‖ ^ 2 := cnorm_sub_sq _ _
  rw [hsub, hcross, ambient_normsq ν c v hD]
  ring

/-- **NSE.15**: the exact `δ_c` ratio and the incidence-correction size. -/
theorem payment_ratio (ν : ℝ) (e c v : H) (he : e ≠ 0)
    (hce : (⟪c, e⟫).re = 0) (hν : 0 ≤ ν) (hq : 0 < record ν c v) :
    ‖payment ν e c v‖ ^ 2 = (deltaC e v)⁻¹ ^ 2 * ‖ambient ν c v‖ ^ 2 ∧
      ‖payment ν e c v - ambient ν c v‖ ^ 2
        = record ν c v ^ 2 * ((vres e v)⁻¹ - (‖v‖ ^ 2)⁻¹) := by
  have hV := vres_pos ν e c v he hce hν hq
  have hD := dissip_pos ν e c v he hce hν hq
  have hdel : (deltaC e v) ^ 2 = vres e v / ‖v‖ ^ 2 := by
    unfold deltaC
    rw [Real.sq_sqrt (div_nonneg hV.le hD.le)]
  have hvn : ‖v‖ ≠ 0 := by
    have : 0 < ‖v‖ := by nlinarith [norm_nonneg v]
    exact this.ne'
  constructor
  · rw [payment_normsq ν e c v he hce hν hq, ambient_normsq ν c v hD,
      inv_pow, hdel]
    field_simp
  · have h14 := payment_pythagoras ν e c v he hce hν hq
    rw [payment_normsq ν e c v he hce hν hq, ambient_normsq ν c v hD] at h14
    have hval : ‖payment ν e c v - ambient ν c v‖ ^ 2
        = record ν c v ^ 2 / vres e v - record ν c v ^ 2 / ‖v‖ ^ 2 := by
      linarith
    rw [hval]
    field_simp

/-- **NSE.17** (`cor:NS-centred-work-one-source`): the source splits into
the work projection and a `ψ`-orthogonal remainder, with the exact norm
split. -/
theorem work_decomposition (e c v : H) (_he : e ≠ 0)
    (hce : (⟪c, e⟫).re = 0) (hV : 0 < vres e v) :
    c = workProj e c v + workResid e c v ∧
      (⟪workResid e c v, centred e v⟫).re = 0 ∧
      ‖c‖ ^ 2 = work c v ^ 2 / vres e v + ‖workResid e c v‖ ^ 2 := by
  have hwork := work_eq_centred e c v hce
  have hpsipsi : (⟪centred e v, centred e v⟫).re = vres e v := by
    unfold vres
    exact cre_inner_self (centred e v)
  have hcpsi : (⟪c, centred e v⟫).re = -work c v := by linarith
  have hresid : (⟪workResid e c v, centred e v⟫).re = 0 := by
    unfold workResid workProj
    rw [inner_sub_left, Complex.sub_re, re_inner_neg_ofReal_smul_left,
      hpsipsi, hcpsi, div_mul_cancel₀ _ (ne_of_gt hV)]
    ring
  refine ⟨by unfold workResid; abel, hresid, ?_⟩
  have hc : c = workProj e c v + workResid e c v := by unfold workResid; abel
  have hwp : ‖workProj e c v‖ ^ 2 = work c v ^ 2 / vres e v := by
    unfold workProj
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs]
    unfold vres at *
    field_simp
  have hcross : (⟪workProj e c v, workResid e c v⟫).re = 0 := by
    unfold workProj
    rw [re_inner_neg_ofReal_smul_left, cre_inner_symm, hresid, mul_zero,
      neg_zero]
  calc ‖c‖ ^ 2 = ‖workProj e c v + workResid e c v‖ ^ 2 := by rw [← hc]
    _ = ‖workProj e c v‖ ^ 2 + 2 * (⟪workProj e c v, workResid e c v⟫).re
        + ‖workResid e c v‖ ^ 2 := cnorm_add_sq _ _
    _ = work c v ^ 2 / vres e v + ‖workResid e c v‖ ^ 2 := by
        rw [hwp, hcross]; ring

/-- **NSE.18**: on the record-positive set the work projection is the
collinear sum of the viscosity-matching term and the record payment; the two
terms may not be counted as independent source births. -/
theorem work_collinear (ν : ℝ) (e c v : H)
    (hq : 0 < record ν c v) :
    workProj e c v
      = -((ν * ‖v‖ ^ 2 / vres e v : ℝ) : ℂ) • centred e v
        + payment ν e c v := by
  have harg : 0 < work c v - ν * ‖v‖ ^ 2 := by
    by_contra hcon
    push Not at hcon
    have : record ν c v = 0 := max_eq_right hcon
    linarith
  have hqval : record ν c v = work c v - ν * ‖v‖ ^ 2 := max_eq_left harg.le
  unfold workProj payment
  rw [hqval, ← add_smul]
  congr 1
  push_cast
  ring

end NSPay

end EnergyNeutralPayment

/-! ### Ambient critical short can underprice the physical source

Record `cth:NS-ambient-critical-underprice`: the fully explicit
two-dimensional witness.  For each `0 < ε < 1` the packet on `ℂ²` with
orthonormal `e, f`, energy-neutral source `c = -f`, zero viscosity
threshold, and target `v = √(1-ε²) e + ε f` has record rate `q_c = ε`,
ambient payment distance `ε`, energy-neutral payment distance `1`, and
`δ_c = ε`. -/

section AmbientUnderprice

open scoped ComplexInnerProductSpace

namespace NSPay

/-- The witness energy vector `e`. -/
noncomputable def wE : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

/-- The witness orthogonal direction `f`. -/
noncomputable def wF : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1

/-- The witness source `c = -f`. -/
noncomputable def wC : EuclideanSpace ℂ (Fin 2) := -wF

/-- The witness target `v = √(1-ε²) e + ε f`. -/
noncomputable def wV (ε : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  ((Real.sqrt (1 - ε ^ 2) : ℝ) : ℂ) • wE + (ε : ℂ) • wF

/-- The witness pairings: `e, f` are orthonormal. -/
theorem witness_orthonormal :
    ⟪wE, wE⟫ = 1 ∧ ⟪wF, wF⟫ = 1 ∧ ⟪wE, wF⟫ = 0 ∧ ⟪wF, wE⟫ = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [wE, wF, EuclideanSpace.inner_single_left]

/-- **`cth:NS-ambient-critical-underprice`**: on the explicit witness the
ambient payment distance is `ε` while the energy-neutral payment distance is
one, and `δ_c = ε`; hence no regulator-uniform comparison is available
without a positive lower bound on `δ_c`. -/
theorem ambient_underprice (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ‖wE‖ = 1 ∧ (⟪wC, wE⟫).re = 0 ∧ 0 < record 0 wC (wV ε) ∧
      ‖ambient 0 wC (wV ε)‖ = ε ∧ ‖payment 0 wE wC (wV ε)‖ = 1 ∧
      deltaC wE (wV ε) = ε := by
  obtain ⟨hee, hff, hef, hfe⟩ := witness_orthonormal
  have h1ε : (0 : ℝ) ≤ 1 - ε ^ 2 := by nlinarith
  have hnE : ‖wE‖ = 1 := by
    have h2 : ‖wE‖ ^ 2 = 1 := by
      rw [← cre_inner_self wE, hee]
      simp
    nlinarith [norm_nonneg wE]
  have hnF : ‖wF‖ = 1 := by
    have h2 : ‖wF‖ ^ 2 = 1 := by
      rw [← cre_inner_self wF, hff]
      simp
    nlinarith [norm_nonneg wF]
  have hEv : ⟪wE, wV ε⟫ = ((Real.sqrt (1 - ε ^ 2) : ℝ) : ℂ) := by
    unfold wV
    rw [inner_add_right, inner_smul_right, inner_smul_right, hee, hef]
    ring
  have hFv : ⟪wF, wV ε⟫ = (ε : ℂ) := by
    unfold wV
    rw [inner_add_right, inner_smul_right, inner_smul_right, hfe, hff]
    ring
  have hCv : ⟪wC, wV ε⟫ = -(ε : ℂ) := by
    unfold wC
    rw [inner_neg_left, hFv]
  have hCe : (⟪wC, wE⟫).re = 0 := by
    unfold wC
    rw [inner_neg_left, hfe]
    simp
  have hvv : ⟪wV ε, wV ε⟫ = 1 := by
    unfold wV
    simp only [inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, hee, hef, hfe, hff, Complex.conj_ofReal, mul_zero,
      mul_one, add_zero, zero_add]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h1ε]
    push_cast
    ring
  have hDc : ‖wV ε‖ ^ 2 = 1 := by
    rw [← cre_inner_self (wV ε), hvv]
    simp
  have hwork : work wC (wV ε) = ε := by
    unfold work
    rw [hCv]
    simp
  have hrec : record 0 wC (wV ε) = ε := by
    unfold record
    rw [hwork, zero_mul, sub_zero, max_eq_left hε.le]
  have hcentre : centre wE (wV ε) = Real.sqrt (1 - ε ^ 2) := by
    unfold centre
    rw [hEv, hnE]
    simp
  have hcentred : centred wE (wV ε) = (ε : ℂ) • wF := by
    unfold centred
    rw [hcentre]
    unfold wV
    abel
  have hVc : vres wE (wV ε) = ε ^ 2 := by
    unfold vres
    rw [hcentred, norm_smul, hnF, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε]
    ring
  refine ⟨hnE, hCe, by rw [hrec]; exact hε, ?_, ?_, ?_⟩
  · unfold ambient
    have hnV : ‖wV ε‖ = 1 := by nlinarith [norm_nonneg (wV ε)]
    rw [norm_smul, hrec, hDc, hnV, norm_neg, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_pos (by simpa using hε)]
    ring
  · unfold payment
    rw [hrec, hVc, hcentred, norm_smul, norm_smul, hnF, norm_neg,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hε,
      abs_of_pos (by positivity : (0 : ℝ) < ε / ε ^ 2)]
    field_simp
  · unfold deltaC
    rw [hVc, hDc]
    simp [Real.sqrt_sq hε.le]

end NSPay

end AmbientUnderprice

/-! ### A common phase-space scalar panel

Record `prop:NS-common-phase-space-panel` (NST.15).

Rendering: the spectral projections `(Q_j)_{j∈ℕ}` are self-adjoint
idempotents on a complex Hilbert space whose partial sums converge strongly
to the identity (`HasSum` of `Q_j x` to `x`); the smooth quadratic spatial
partition is any finite operator family `(η_α)` with
`∑_α η_α^* η_α = 1` — the multiplication operators
`η_α` of the manuscript satisfy exactly this.  The joint sum over `(j, α)`
is rendered as the strong sum over `j` of the finite `α`-sums, and the
polarized scalar identity together with its absolute convergence (the
Cauchy–Schwarz clause of the manuscript proof) is stated for arbitrary
`c, q`.  The insufficiency of separate marginals is witnessed by the
explicit diagonal/antidiagonal pair on `{0,1}²`. -/

section PhaseSpacePanel

open scoped ComplexInnerProductSpace

namespace PhasePanel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {A : Type*} [Fintype A]

/-- The ordered panel operator `E_{j,α} = η_α Q_j`. -/
def panelOp (η : A → H →L[ℂ] H) (Q : ℕ → H →L[ℂ] H) (j : ℕ) (a : A) :
    H →L[ℂ] H := (η a).comp (Q j)

/-- The `α`-sum of `E_{j,α}^* E_{j,α}` collapses to `Q_j` (first identity
of NST.15, fibrewise). -/
theorem panel_fiber_collapse (η : A → H →L[ℂ] H) (Q : ℕ → H →L[ℂ] H)
    (hpart : ∑ a, (ContinuousLinearMap.adjoint (η a)).comp (η a) = 1)
    (hQsa : ∀ j, ContinuousLinearMap.adjoint (Q j) = Q j)
    (hQidem : ∀ j, (Q j).comp (Q j) = Q j) (j : ℕ) :
    ∑ a, (ContinuousLinearMap.adjoint (panelOp η Q j a)).comp
      (panelOp η Q j a) = Q j := by
  have hstep : ∀ a : A, (ContinuousLinearMap.adjoint (panelOp η Q j a)).comp
      (panelOp η Q j a)
      = (ContinuousLinearMap.adjoint (Q j)).comp
        (((ContinuousLinearMap.adjoint (η a)).comp (η a)).comp (Q j)) := by
    intro a
    unfold panelOp
    rw [ContinuousLinearMap.adjoint_comp]
    ext x
    simp [ContinuousLinearMap.comp_apply]
  calc ∑ a, (ContinuousLinearMap.adjoint (panelOp η Q j a)).comp
        (panelOp η Q j a)
      = ∑ a, (ContinuousLinearMap.adjoint (Q j)).comp
          (((ContinuousLinearMap.adjoint (η a)).comp (η a)).comp (Q j)) :=
        Finset.sum_congr rfl fun a _ => hstep a
    _ = (ContinuousLinearMap.adjoint (Q j)).comp
          ((∑ a, (ContinuousLinearMap.adjoint (η a)).comp (η a)).comp (Q j)) := by
        rw [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum]
    _ = Q j := by
        rw [hpart, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
          hQsa, hQidem]

/-- **NST.15, operator half**: the ordered panel is a complete resolution,
`∑_{j,α} E_{j,α}^* E_{j,α} = I` in the strong sense. -/
theorem panel_resolution (η : A → H →L[ℂ] H) (Q : ℕ → H →L[ℂ] H)
    (hpart : ∑ a, (ContinuousLinearMap.adjoint (η a)).comp (η a) = 1)
    (hQsa : ∀ j, ContinuousLinearMap.adjoint (Q j) = Q j)
    (hQidem : ∀ j, (Q j).comp (Q j) = Q j)
    (hres : ∀ x : H, HasSum (fun j => Q j x) x) (x : H) :
    HasSum (fun j => ∑ a,
      (ContinuousLinearMap.adjoint (panelOp η Q j a)) (panelOp η Q j a x)) x := by
  have hcongr : ∀ j, ∑ a,
      (ContinuousLinearMap.adjoint (panelOp η Q j a)) (panelOp η Q j a x)
      = Q j x := by
    intro j
    have h := congrArg (fun T : H →L[ℂ] H => T x)
      (panel_fiber_collapse η Q hpart hQsa hQidem j)
    simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply] at h
    exact h
  simpa only [hcongr] using hres x

/-- **NST.15, scalar half**: the polarized resolution of the work scalar,
`-Re⟪c,q⟫ = ∑_{j,α} -Re⟪E_{j,α}c, E_{j,α}q⟫`. -/
theorem panel_scalar_split (η : A → H →L[ℂ] H) (Q : ℕ → H →L[ℂ] H)
    (hpart : ∑ a, (ContinuousLinearMap.adjoint (η a)).comp (η a) = 1)
    (hQsa : ∀ j, ContinuousLinearMap.adjoint (Q j) = Q j)
    (hQidem : ∀ j, (Q j).comp (Q j) = Q j)
    (hres : ∀ x : H, HasSum (fun j => Q j x) x) (c q : H) :
    HasSum (fun j => ∑ a,
      -(⟪panelOp η Q j a c, panelOp η Q j a q⟫).re) (-(⟪c, q⟫).re) := by
  have hterm : ∀ j, ∑ a, -(⟪panelOp η Q j a c, panelOp η Q j a q⟫).re
      = -(⟪c, Q j q⟫).re := by
    intro j
    have hpair : ∀ a, ⟪panelOp η Q j a c, panelOp η Q j a q⟫
        = ⟪c, (ContinuousLinearMap.adjoint (panelOp η Q j a))
            (panelOp η Q j a q)⟫ := fun a =>
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    have hsum : ∑ a, ⟪panelOp η Q j a c, panelOp η Q j a q⟫
        = ⟪c, Q j q⟫ := by
      calc ∑ a, ⟪panelOp η Q j a c, panelOp η Q j a q⟫
          = ∑ a, ⟪c, (ContinuousLinearMap.adjoint (panelOp η Q j a))
              (panelOp η Q j a q)⟫ := Finset.sum_congr rfl fun a _ => hpair a
        _ = ⟪c, ∑ a, (ContinuousLinearMap.adjoint (panelOp η Q j a))
              (panelOp η Q j a q)⟫ := (inner_sum _ _ _).symm
        _ = ⟪c, Q j q⟫ := by
            congr 1
            have h := congrArg (fun T : H →L[ℂ] H => T q)
              (panel_fiber_collapse η Q hpart hQsa hQidem j)
            simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply] at h
            exact h
    calc ∑ a, -(⟪panelOp η Q j a c, panelOp η Q j a q⟫).re
        = -(∑ a, ⟪panelOp η Q j a c, panelOp η Q j a q⟫).re := by
          rw [Complex.re_sum, Finset.sum_neg_distrib]
      _ = -(⟪c, Q j q⟫).re := by rw [hsum]
  have hinner : HasSum (fun j => ⟪c, Q j q⟫) ⟪c, q⟫ := by
    have := (innerSL ℂ c).hasSum (hres q)
    simpa using this
  have hre : HasSum (fun j => (⟪c, Q j q⟫).re) (⟪c, q⟫).re :=
    Complex.hasSum_re hinner
  have hneg := hre.neg
  simpa only [hterm] using hneg

/-- The polarized scalar family is absolutely convergent (the
Cauchy–Schwarz clause of the manuscript proof). -/
theorem panel_scalar_summable (η : A → H →L[ℂ] H) (Q : ℕ → H →L[ℂ] H)
    (hpart : ∑ a, (ContinuousLinearMap.adjoint (η a)).comp (η a) = 1)
    (hQsa : ∀ j, ContinuousLinearMap.adjoint (Q j) = Q j)
    (hQidem : ∀ j, (Q j).comp (Q j) = Q j)
    (hres : ∀ x : H, HasSum (fun j => Q j x) x) (c q : H) :
    Summable (fun j => ∑ a,
      ‖⟪panelOp η Q j a c, panelOp η Q j a q⟫‖) := by
  -- squared panel amplitudes are summable for each argument
  have hsq : ∀ x : H, HasSum (fun j => ∑ a, ‖panelOp η Q j a x‖ ^ 2)
      ((⟪x, x⟫).re) := by
    intro x
    have h := panel_scalar_split η Q hpart hQsa hQidem hres x x
    have hterm : ∀ j, ∑ a, -(⟪panelOp η Q j a x, panelOp η Q j a x⟫).re
        = -(∑ a, ‖panelOp η Q j a x‖ ^ 2) := by
      intro j
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [cre_inner_self]
    simp only [hterm] at h
    simpa using h.neg
  have hc := (hsq c).summable
  have hq' := (hsq q).summable
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    (((hc.add hq').mul_left (1 / 2)))
  · exact Finset.sum_nonneg fun a _ => norm_nonneg _
  · calc ∑ a, ‖⟪panelOp η Q j a c, panelOp η Q j a q⟫‖
        ≤ ∑ a, (1 / 2) * (‖panelOp η Q j a c‖ ^ 2 + ‖panelOp η Q j a q‖ ^ 2) := by
          refine Finset.sum_le_sum fun a _ => ?_
          have hCS : ‖⟪panelOp η Q j a c, panelOp η Q j a q⟫‖
              ≤ ‖panelOp η Q j a c‖ * ‖panelOp η Q j a q‖ :=
            norm_inner_le_norm _ _
          nlinarith [sq_nonneg (‖panelOp η Q j a c‖ - ‖panelOp η Q j a q‖),
            norm_nonneg (panelOp η Q j a c), norm_nonneg (panelOp η Q j a q)]
      _ = (1 / 2) * ((∑ a, ‖panelOp η Q j a c‖ ^ 2)
            + ∑ a, ‖panelOp η Q j a q‖ ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]

/-- The diagonal law on `{0,1}²`. -/
noncomputable def pDiag : Fin 2 × Fin 2 → ℝ := fun p => if p.1 = p.2 then 1 / 2 else 0

/-- The antidiagonal law on `{0,1}²`. -/
noncomputable def pAnti : Fin 2 × Fin 2 → ℝ := fun p => if p.1 = p.2 then 0 else 1 / 2

/-- **Marginal insufficiency witness** (first sentence of NST.15's record):
the diagonal and antidiagonal probabilities have identical marginals but
opposite equality incidence, so separate frequency and spatial marginals do
not determine mixed occurrence. -/
theorem marginals_do_not_determine_joint :
    (∀ p, 0 ≤ pDiag p) ∧ (∀ p, 0 ≤ pAnti p) ∧
      (∑ p : Fin 2 × Fin 2, pDiag p) = 1 ∧
      (∑ p : Fin 2 × Fin 2, pAnti p) = 1 ∧
      (∀ x : Fin 2, ∑ y, pDiag (x, y) = ∑ y, pAnti (x, y)) ∧
      (∀ y : Fin 2, ∑ x, pDiag (x, y) = ∑ x, pAnti (x, y)) ∧
      (∑ x : Fin 2, pDiag (x, x)) = 1 ∧ (∑ x : Fin 2, pAnti (x, x)) = 0 := by
  refine ⟨fun p => ?_, fun p => ?_, ?_, ?_, fun x => ?_, fun y => ?_, ?_, ?_⟩
  · unfold pDiag; split_ifs <;> norm_num
  · unfold pAnti; split_ifs <;> norm_num
  · norm_num [pDiag, Fintype.sum_prod_type, Fin.sum_univ_two]
  · norm_num [pAnti, Fintype.sum_prod_type, Fin.sum_univ_two]
  · fin_cases x <;> norm_num [pDiag, pAnti, Fin.sum_univ_two]
  · fin_cases y <;> norm_num [pDiag, pAnti, Fin.sum_univ_two]
  · norm_num [pDiag, Fin.sum_univ_two]
  · norm_num [pAnti, Fin.sum_univ_two]

end PhasePanel

end PhaseSpacePanel

/-! ### Occupied selector versus stress motion

Record `prop:NS-paid-stress-selector` (NSR.15–NSR.16).

Rendering: the trace-free symmetric carrier `Sym₀(3)` is the set of real
`3×3` matrices with `Xᵀ = X` and zero trace, with the Hilbert–Schmidt
pairing `frobDot`.  NSR.15 is the exact orthogonal split; the Fisher
coordinate bound `|θ₁-θ₀| ≤ ½|ζ₁-ζ₀|` is proved for `ζ = 2·arcsin √θ`;
NSR.16 is the translated-selector integral bound with the occupied
selector `θ(t) = sin²(ζ(t)/2)` and continuous stress data.  The closing
clause (the modulus is not supplied by an amplitude bound alone) is the
manuscript's own scalar obstruction `ρ_n(t) = 1 + sin(nt)/2`, rendered with
its uniform amplitude/L⁴ bound and the explicit failure of any uniform
`L²` translation modulus. -/

section PaidStressSelector

namespace StressSel

/-- The Hilbert–Schmidt pairing on real `3×3` matrices. -/
def frobDot (X Y : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ i, ∑ j, X i j * Y i j

/-- Membership in the trace-free symmetric carrier `Sym₀(3)`. -/
def isSym0 (X : Matrix (Fin 3) (Fin 3) ℝ) : Prop := Xᵀ = X ∧ X.trace = 0

/-- Expansion of the pairing of a difference of scaled stresses. -/
theorem frobDot_smul_sub_smul (a b : ℝ) (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    frobDot (a • X - b • Y) (a • X - b • Y)
      = a ^ 2 * frobDot X X - 2 * (a * b) * frobDot X Y
        + b ^ 2 * frobDot Y Y := by
  simp only [frobDot, Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Expansion of the pairing of a difference with a scaled subtrahend. -/
theorem frobDot_sub_smul (c : ℝ) (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    frobDot (X - c • Y) (X - c • Y)
      = frobDot X X - 2 * c * frobDot X Y + c ^ 2 * frobDot Y Y := by
  simp only [frobDot, Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Expansion of the pairing of a sum. -/
theorem frobDot_add_add (U W : Matrix (Fin 3) (Fin 3) ℝ) :
    frobDot (U + W) (U + W)
      = frobDot U U + 2 * frobDot U W + frobDot W W := by
  simp only [frobDot, Fin.sum_univ_three, Matrix.add_apply]
  ring

/-- Expansion of the pairing of a difference. -/
theorem frobDot_sub_sub (U W : Matrix (Fin 3) (Fin 3) ℝ) :
    frobDot (U - W) (U - W)
      = frobDot U U - 2 * frobDot U W + frobDot W W := by
  simp only [frobDot, Fin.sum_univ_three, Matrix.sub_apply]
  ring

/-- The pairing of a scaled stress with itself. -/
theorem frobDot_smul_self (c : ℝ) (U : Matrix (Fin 3) (Fin 3) ℝ) :
    frobDot (c • U) (c • U) = c ^ 2 * frobDot U U := by
  simp only [frobDot, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The pairing is positive semidefinite. -/
theorem frobDot_self_nonneg (X : Matrix (Fin 3) (Fin 3) ℝ) :
    0 ≤ frobDot X X :=
  Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => mul_self_nonneg (X i j)

/-- The pairing is definite. -/
theorem eq_zero_of_frobDot_self {X : Matrix (Fin 3) (Fin 3) ℝ}
    (h : frobDot X X = 0) : X = 0 := by
  ext i j
  have hrow : ∑ q, X i q * X i q = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun p _ =>
      Finset.sum_nonneg fun q _ => mul_self_nonneg (X p q)).mp h i
      (Finset.mem_univ i)
  have hentry : X i j * X i j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun q _ =>
      mul_self_nonneg (X i q)).mp hrow j (Finset.mem_univ j)
  simpa using mul_self_eq_zero.mp hentry

/-- The parallelogram-type bound `⟪u+w,u+w⟫ ≤ 2⟪u,u⟫ + 2⟪w,w⟫`. -/
theorem frobDot_add_le (U W : Matrix (Fin 3) (Fin 3) ℝ) :
    frobDot (U + W) (U + W) ≤ 2 * frobDot U U + 2 * frobDot W W := by
  have h1 := frobDot_add_add U W
  have h2 := frobDot_sub_sub U W
  have h3 := frobDot_self_nonneg (U - W)
  linarith

/-- **NSR.15**: the exact orthogonal split of the occupied-selector motion
into the off-`X₀` component and the collinear defect. -/
theorem selector_split (θ₀ θ₁ : ℝ) (_hθ₀ : θ₀ ∈ Set.Icc (0 : ℝ) 1)
    (_hθ₁ : θ₁ ∈ Set.Icc (0 : ℝ) 1) (X₀ X₁ : Matrix (Fin 3) (Fin 3) ℝ)
    (_hX₀ : isSym0 X₀) (_hX₁ : isSym0 X₁) (hne : X₀ ≠ 0) :
    frobDot (θ₁ • X₁ - θ₀ • X₀) (θ₁ • X₁ - θ₀ • X₀)
      = θ₁ ^ 2 * frobDot (X₁ - (frobDot X₁ X₀ / frobDot X₀ X₀) • X₀)
          (X₁ - (frobDot X₁ X₀ / frobDot X₀ X₀) • X₀)
        + (θ₁ * (frobDot X₁ X₀ / frobDot X₀ X₀) - θ₀) ^ 2
            * frobDot X₀ X₀ := by
  have hg : frobDot X₀ X₀ ≠ 0 := fun h => hne (eq_zero_of_frobDot_self h)
  rw [frobDot_smul_sub_smul, frobDot_sub_smul]
  field_simp
  ring

/-- The half-angle square difference bound `|sin²a - sin²b| ≤ |a-b|`. -/
theorem sin_sq_diff_le (a b : ℝ) :
    |Real.sin a ^ 2 - Real.sin b ^ 2| ≤ |a - b| := by
  have hid : Real.sin a ^ 2 - Real.sin b ^ 2
      = Real.sin (a + b) * Real.sin (a - b) := by
    rw [Real.sin_add, Real.sin_sub]
    linear_combination (Real.sin b) ^ 2 * Real.sin_sq_add_cos_sq a
      - (Real.sin a) ^ 2 * Real.sin_sq_add_cos_sq b
  rw [hid, abs_mul]
  calc |Real.sin (a + b)| * |Real.sin (a - b)|
      ≤ 1 * |a - b| :=
        mul_le_mul (Real.abs_sin_le_one _) Real.abs_sin_le_abs
          (abs_nonneg _) zero_le_one
    _ = |a - b| := one_mul _

/-- **Fisher-coordinate Lipschitz bound**: with `ζ = 2 arcsin √θ`,
`|θ₁-θ₀| ≤ ½|ζ₁-ζ₀|`. -/
theorem fisher_lipschitz (θ₀ θ₁ : ℝ) (h₀ : θ₀ ∈ Set.Icc (0 : ℝ) 1)
    (h₁ : θ₁ ∈ Set.Icc (0 : ℝ) 1) :
    |θ₁ - θ₀| ≤ (1 / 2) * |2 * Real.arcsin (Real.sqrt θ₁)
      - 2 * Real.arcsin (Real.sqrt θ₀)| := by
  set a := Real.arcsin (Real.sqrt θ₁) with ha
  set b := Real.arcsin (Real.sqrt θ₀) with hb
  have hsa : Real.sin a ^ 2 = θ₁ := by
    rw [ha, Real.sin_arcsin (le_trans (by norm_num) (Real.sqrt_nonneg _))
      (Real.sqrt_le_one.mpr h₁.2), Real.sq_sqrt h₁.1]
  have hsb : Real.sin b ^ 2 = θ₀ := by
    rw [hb, Real.sin_arcsin (le_trans (by norm_num) (Real.sqrt_nonneg _))
      (Real.sqrt_le_one.mpr h₀.2), Real.sq_sqrt h₀.1]
  have hkey := sin_sq_diff_le a b
  rw [hsa, hsb] at hkey
  have habs : |2 * a - 2 * b| = 2 * |a - b| := by
    rw [show 2 * a - 2 * b = 2 * (a - b) by ring, abs_mul]
    norm_num
  rw [habs]
  linarith

/-- The occupied selector `θ(t) = sin²(ζ(t)/2)` of the Fisher coordinate. -/
noncomputable def selector (ζ : ℝ → ℝ) (t : ℝ) : ℝ := Real.sin (ζ t / 2) ^ 2

/-- Pointwise translated-selector bound behind NSR.16. -/
theorem selector_move_bound (za zb E₀ : ℝ) (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (_hE : 0 ≤ E₀) (hB : frobDot B B ≤ E₀ ^ 2) :
    frobDot (Real.sin (za / 2) ^ 2 • A - Real.sin (zb / 2) ^ 2 • B)
        (Real.sin (za / 2) ^ 2 • A - Real.sin (zb / 2) ^ 2 • B)
      ≤ 2 * frobDot (A - B) (A - B) + E₀ ^ 2 / 2 * (za - zb) ^ 2 := by
  set θa := Real.sin (za / 2) ^ 2 with hθa
  set θb := Real.sin (zb / 2) ^ 2 with hθb
  have hθa01 : 0 ≤ θa ∧ θa ≤ 1 := by
    constructor
    · positivity
    · rw [hθa]; exact Real.sin_sq_le_one _
  have hdiff : |θa - θb| ≤ |za - zb| / 2 := by
    have := sin_sq_diff_le (za / 2) (zb / 2)
    rw [← hθa, ← hθb] at this
    calc |θa - θb| ≤ |za / 2 - zb / 2| := this
      _ = |za - zb| / 2 := by
          rw [show za / 2 - zb / 2 = (za - zb) / 2 from by ring, abs_div,
            abs_two]
  have hdec : θa • A - θb • B = θa • (A - B) + (θa - θb) • B := by module
  rw [hdec]
  have hb1 := frobDot_add_le (θa • (A - B)) ((θa - θb) • B)
  rw [frobDot_smul_self, frobDot_smul_self] at hb1
  have hterm1 : θa ^ 2 * frobDot (A - B) (A - B) ≤ frobDot (A - B) (A - B) := by
    have hnn := frobDot_self_nonneg (A - B)
    have hsq1 : θa ^ 2 ≤ 1 := by nlinarith [hθa01.1, hθa01.2]
    nlinarith [hsq1, hnn]
  have hterm2 : (θa - θb) ^ 2 * frobDot B B ≤ (za - zb) ^ 2 / 4 * E₀ ^ 2 := by
    have hsq : (θa - θb) ^ 2 ≤ (za - zb) ^ 2 / 4 := by
      nlinarith [hdiff, abs_nonneg (θa - θb), sq_abs (θa - θb),
        sq_abs (za - zb), abs_nonneg (za - zb)]
    have hBnn := frobDot_self_nonneg B
    nlinarith [sq_nonneg (za - zb), sq_nonneg E₀]
  nlinarith [hb1, hterm1, hterm2]

/-- Continuity of the pairing of two continuous stress curves. -/
theorem continuous_frobDot_curve {f g : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hf : ∀ i j, Continuous fun t => f t i j)
    (hg : ∀ i j, Continuous fun t => g t i j) :
    Continuous fun t => frobDot (f t) (g t) := by
  unfold frobDot
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (hf i j).mul (hg i j)

/-- **NSR.16**: the translated paid-stress bound
`∫‖δ_h(θX)‖² ≤ 2∫‖δ_h X‖² + (E₀²/2)∫|δ_h ζ|²`. -/
theorem paid_stress_translation_bound (T h E₀ : ℝ) (_hh : 0 ≤ h) (hhT : h ≤ T)
    (hE : 0 ≤ E₀) (X : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (ζ : ℝ → ℝ)
    (hX : ∀ i j, Continuous fun t => X t i j) (hζ : Continuous ζ)
    (_hsym : ∀ t, isSym0 (X t))
    (hXb : ∀ t, frobDot (X t) (X t) ≤ E₀ ^ 2) :
    (∫ t in (0 : ℝ)..(T - h),
        frobDot (selector ζ (t + h) • X (t + h) - selector ζ t • X t)
          (selector ζ (t + h) • X (t + h) - selector ζ t • X t))
      ≤ 2 * (∫ t in (0 : ℝ)..(T - h),
            frobDot (X (t + h) - X t) (X (t + h) - X t))
        + E₀ ^ 2 / 2 * ∫ t in (0 : ℝ)..(T - h), (ζ (t + h) - ζ t) ^ 2 := by
  have hTh : (0 : ℝ) ≤ T - h := by linarith
  have hshift : Continuous fun t : ℝ => t + h := by fun_prop
  have hθc : Continuous (selector ζ) := by
    unfold selector
    exact (Real.continuous_sin.comp (hζ.div_const 2)).pow 2
  have hZc : ∀ i j, Continuous fun t =>
      (selector ζ (t + h) • X (t + h) - selector ζ t • X t) i j := by
    intro i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (((hθc.comp hshift).mul ((hX i j).comp hshift)).sub
      (hθc.mul (hX i j)))
  have hDc : ∀ i j, Continuous fun t => (X (t + h) - X t) i j := by
    intro i j
    simp only [Matrix.sub_apply]
    exact ((hX i j).comp hshift).sub (hX i j)
  have hint1 : IntervalIntegrable (fun t =>
      frobDot (selector ζ (t + h) • X (t + h) - selector ζ t • X t)
        (selector ζ (t + h) • X (t + h) - selector ζ t • X t))
      MeasureTheory.volume 0 (T - h) :=
    (continuous_frobDot_curve hZc hZc).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t =>
      frobDot (X (t + h) - X t) (X (t + h) - X t))
      MeasureTheory.volume 0 (T - h) :=
    (continuous_frobDot_curve hDc hDc).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun t => (ζ (t + h) - ζ t) ^ 2)
      MeasureTheory.volume 0 (T - h) :=
    (((hζ.comp hshift).sub hζ).pow 2).intervalIntegrable _ _
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) (T - h),
      frobDot (selector ζ (t + h) • X (t + h) - selector ζ t • X t)
        (selector ζ (t + h) • X (t + h) - selector ζ t • X t)
      ≤ 2 * frobDot (X (t + h) - X t) (X (t + h) - X t)
        + E₀ ^ 2 / 2 * (ζ (t + h) - ζ t) ^ 2 := by
    intro t _
    exact selector_move_bound (ζ (t + h)) (ζ t) E₀ (X (t + h)) (X t) hE
      (hXb t)
  calc (∫ t in (0 : ℝ)..(T - h),
        frobDot (selector ζ (t + h) • X (t + h) - selector ζ t • X t)
          (selector ζ (t + h) • X (t + h) - selector ζ t • X t))
      ≤ ∫ t in (0 : ℝ)..(T - h),
          (2 * frobDot (X (t + h) - X t) (X (t + h) - X t)
            + E₀ ^ 2 / 2 * (ζ (t + h) - ζ t) ^ 2) :=
        intervalIntegral.integral_mono_on hTh hint1
          ((hint2.const_mul 2).add (hint3.const_mul (E₀ ^ 2 / 2))) hpt
    _ = 2 * (∫ t in (0 : ℝ)..(T - h),
            frobDot (X (t + h) - X t) (X (t + h) - X t))
        + E₀ ^ 2 / 2 * ∫ t in (0 : ℝ)..(T - h), (ζ (t + h) - ζ t) ^ 2 := by
        rw [intervalIntegral.integral_add (hint2.const_mul 2)
          (hint3.const_mul (E₀ ^ 2 / 2)),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]

/-- The scalar obstruction family `ρ_n(t) = 1 + sin(nt)/2`. -/
noncomputable def rhoObs (n : ℕ) (t : ℝ) : ℝ := 1 + Real.sin (n * t) / 2

/-- The obstruction family has a uniform amplitude bound. -/
theorem rhoObs_amplitude (n : ℕ) (t : ℝ) : |rhoObs n t| ≤ 3 / 2 := by
  unfold rhoObs
  have h1 := Real.neg_one_le_sin ((n : ℝ) * t)
  have h2 := Real.sin_le_one ((n : ℝ) * t)
  rw [abs_le]
  constructor <;> linarith

/-- Hence a uniform `L⁴` bound on every window. -/
theorem rhoObs_L4 (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    ∫ t in (0 : ℝ)..T, (rhoObs n t) ^ 4 ≤ (3 / 2) ^ 4 * T := by
  have hcont : Continuous fun t => (rhoObs n t) ^ 4 := by
    unfold rhoObs
    fun_prop
  calc ∫ t in (0 : ℝ)..T, (rhoObs n t) ^ 4
      ≤ ∫ _ in (0 : ℝ)..T, ((3:ℝ) / 2) ^ 4 := by
        refine intervalIntegral.integral_mono_on hT
          (hcont.intervalIntegrable _ _)
          (intervalIntegrable_const) fun t _ => ?_
        have := rhoObs_amplitude n t
        have habs : (rhoObs n t) ^ 4 = |rhoObs n t| ^ 4 := by
          rw [← abs_pow, abs_of_nonneg (by positivity)]
        rw [habs]
        have h32 : (0 : ℝ) ≤ 3 / 2 := by norm_num
        exact pow_le_pow_left₀ (abs_nonneg _) this 4
    _ = (3 / 2) ^ 4 * T := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]

/-- The exact `L²` mass of `sin(nt)` on a window. -/
theorem integral_sin_sq (n : ℕ) (hn : 0 < n) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, Real.sin ((n : ℝ) * t) ^ 2
      = T / 2 - Real.sin (2 * ((n : ℝ) * T)) / (4 * n) := by
  have hnR : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hder : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun u => u / 2 - Real.sin (2 * ((n : ℝ) * u)) / (4 * n))
        (Real.sin ((n : ℝ) * t) ^ 2) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => 2 * ((n : ℝ) * u)) (2 * n) t := by
      simpa [mul_assoc] using (hasDerivAt_id t).const_mul (2 * (n : ℝ))
    have h2 : HasDerivAt (fun u : ℝ => Real.sin (2 * ((n : ℝ) * u)))
        (Real.cos (2 * ((n : ℝ) * t)) * (2 * n)) t :=
      (Real.hasDerivAt_sin _).comp t h1
    have h3 := ((hasDerivAt_id t).div_const 2).sub
      (h2.div_const (4 * n))
    have hval : 1 / 2 - Real.cos (2 * ((n : ℝ) * t)) * (2 * n) / (4 * n)
        = Real.sin ((n : ℝ) * t) ^ 2 := by
      have hfrac : Real.cos (2 * ((n : ℝ) * t)) * (2 * n) / (4 * n)
          = Real.cos (2 * ((n : ℝ) * t)) / 2 := by
        field_simp
        ring
      rw [hfrac, Real.cos_two_mul]
      have hsc := Real.sin_sq_add_cos_sq ((n : ℝ) * t)
      linarith
    rw [hval] at h3
    exact h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num

/-- **Amplitude bounds do not supply a translation modulus**: the family
`ρ_n` is uniformly bounded (hence uniformly `L⁴`-bounded) but admits no
uniform `L²` time-translation modulus on `[0,T]`. -/
theorem rhoObs_no_translation_modulus (T : ℝ) (hT : 0 < T) :
    ∃ ε₀ > 0, ∀ δ > 0, ∃ (n : ℕ) (h : ℝ), 0 < h ∧ h ≤ δ ∧
      ε₀ ≤ ∫ t in (0 : ℝ)..T, (rhoObs n (t + h) - rhoObs n t) ^ 2 := by
  refine ⟨T / 4, by linarith, fun δ hδ => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max (Real.pi / δ) (1 / T))
  have hnR : (0 : ℝ) < n := by
    have h1 : (0 : ℝ) < max (Real.pi / δ) (1 / T) :=
      lt_max_of_lt_left (div_pos Real.pi_pos hδ)
    linarith
  have hnpos : 0 < n := Nat.cast_pos.mp hnR
  refine ⟨n, Real.pi / n, div_pos Real.pi_pos hnR, ?_, ?_⟩
  · have h1 : Real.pi / δ < n := lt_of_le_of_lt (le_max_left _ _) hn
    rw [div_le_iff₀ hnR]
    rw [div_lt_iff₀ hδ] at h1
    nlinarith [h1]
  · have hpt : ∀ t : ℝ, (rhoObs n (t + Real.pi / n) - rhoObs n t) ^ 2
        = Real.sin ((n : ℝ) * t) ^ 2 := by
      intro t
      unfold rhoObs
      have harg : (n : ℝ) * (t + Real.pi / n) = (n : ℝ) * t + Real.pi := by
        field_simp
      rw [harg, Real.sin_add_pi]
      ring
    have hcongr : ∫ t in (0 : ℝ)..T,
          (rhoObs n (t + Real.pi / n) - rhoObs n t) ^ 2
        = ∫ t in (0 : ℝ)..T, Real.sin ((n : ℝ) * t) ^ 2 :=
      intervalIntegral.integral_congr fun t _ => hpt t
    rw [hcongr, integral_sin_sq n hnpos T]
    have hsin : Real.sin (2 * ((n : ℝ) * T)) ≤ 1 := Real.sin_le_one _
    have hbound : Real.sin (2 * ((n : ℝ) * T)) / (4 * n) ≤ 1 / (4 * n) := by
      gcongr
    have h1T : 1 / T < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hnT : 1 < (n : ℝ) * T := by
      rw [div_lt_iff₀ hT] at h1T
      linarith
    have hb2 : 1 / (4 * (n : ℝ)) ≤ T / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith

end StressSel

end PaidStressSelector

/-! ### Equal lifetime with distinct momentum ancestry

Record `cth:GT-lifetime-no-momentum-ancestry` (JT.5).

Rendering: the joint source measure `μ_j = δ₁(dx) η_j(dq) I_E` factors as
the product of the Dirac energy law at `x = 1` with the momentum window law
`η_j`, tensored with the identity coefficient `I_E`; since the `I_E` factor
is scalar, the packet is rendered as the product measure `δ₁ ⊗ η_j` with a
matrix-decorated survival clause.  Both packets have energy marginal `δ₁`,
survival kernel `∫ e^{-sx} dδ₁ = e^{-s}`, renewal-lifetime density
`∫ x e^{-sx} dδ₁ = e^{-s}`, and zero-mass Green weight `∫₀^∞ e^{-s} ds = 1`,
while a continuous test separates the momentum marginals whenever
`η₁ ≠ η₂` (compact metrizable window).  A fully explicit witness on the
window `[0,1]` with Dirac ancestries and separating test `q ↦ q` is
provided. -/

section LifetimeAncestry

open MeasureTheory

namespace Lifetime

variable {K : Type*} [MeasurableSpace K]

/-- The scalar part of the joint lifetime packet `μ_j = δ₁ ⊗ η_j` (JT.5). -/
noncomputable def packet (η : Measure K) : Measure (ℝ × K) :=
  (Measure.dirac (1 : ℝ)).prod η

/-- The energy marginal of the packet is the Dirac law at unit energy. -/
theorem packet_energy_marginal (η : Measure K) [IsProbabilityMeasure η] :
    (packet η).map Prod.fst = Measure.dirac 1 := by
  unfold packet
  rw [Measure.map_fst_prod]
  simp

/-- The momentum marginal of the packet recovers the window law. -/
theorem packet_momentum_marginal (η : Measure K) [IsProbabilityMeasure η] :
    (packet η).map Prod.snd = η := by
  unfold packet
  rw [Measure.map_snd_prod]
  simp

/-- Both packets share the energy marginal `δ₁ I_E` (matrix-decorated). -/
theorem equal_energy_marginals {E : Type*} [DecidableEq E]
    (η₁ η₂ : Measure K) [IsProbabilityMeasure η₁] [IsProbabilityMeasure η₂] :
    (packet η₁).map Prod.fst = (packet η₂).map Prod.fst ∧
      ∀ A : Set ℝ, (((packet η₁).map Prod.fst) A).toReal • (1 : Matrix E E ℝ)
        = (((packet η₂).map Prod.fst) A).toReal • (1 : Matrix E E ℝ) := by
  refine ⟨?_, fun A => ?_⟩ <;>
    rw [packet_energy_marginal, packet_energy_marginal]

/-- The survival kernel of both packets is `e^{-s}` (times `I_E`). -/
theorem survival_kernel (η : Measure K) [IsProbabilityMeasure η] (s : ℝ) :
    ∫ x, Real.exp (-(s * x)) ∂((packet η).map Prod.fst) = Real.exp (-s) := by
  rw [packet_energy_marginal, integral_dirac]
  norm_num

/-- The renewal-lifetime density of both packets is `e^{-s} ds` (times
`I_E`). -/
theorem lifetime_density (η : Measure K) [IsProbabilityMeasure η] (s : ℝ) :
    ∫ x, x * Real.exp (-(s * x)) ∂((packet η).map Prod.fst)
      = Real.exp (-s) := by
  rw [packet_energy_marginal, integral_dirac]
  norm_num

/-- The zero-mass Green weight of the common lifetime density is one, so the
zero-mass Green matrix is `I_E`. -/
theorem green_weight {E : Type*} [DecidableEq E] :
    (∫ s in Set.Ioi (0 : ℝ), Real.exp (-s)) • (1 : Matrix E E ℝ)
      = (1 : Matrix E E ℝ) := by
  rw [integral_exp_neg_Ioi_zero, one_smul]

/-- **`cth:GT-lifetime-no-momentum-ancestry`**: on a compact metrizable
momentum window, distinct window laws give packets with identical energy
marginal, survival kernel, lifetime density and Green weight, separated by
a continuous spatial test on the momentum marginals.  The lifetime packet
is not a complete momentum-ancestry record. -/
theorem lifetime_no_momentum_ancestry {K' : Type*} [MetricSpace K']
    [CompactSpace K'] [MeasurableSpace K'] [BorelSpace K']
    (η₁ η₂ : Measure K') [IsProbabilityMeasure η₁] [IsProbabilityMeasure η₂]
    (hne : η₁ ≠ η₂) :
    (packet η₁).map Prod.fst = (packet η₂).map Prod.fst ∧
      (∀ s : ℝ, ∫ x, Real.exp (-(s * x)) ∂((packet η₁).map Prod.fst)
        = Real.exp (-s) ∧
        ∫ x, Real.exp (-(s * x)) ∂((packet η₂).map Prod.fst)
        = Real.exp (-s)) ∧
      ∃ f : C(K', ℝ), ∫ q, f q ∂((packet η₁).map Prod.snd)
        ≠ ∫ q, f q ∂((packet η₂).map Prod.snd) := by
  refine ⟨(equal_energy_marginals (E := Fin 1) η₁ η₂).1,
    fun s => ⟨survival_kernel η₁ s, survival_kernel η₂ s⟩, ?_⟩
  rw [packet_momentum_marginal, packet_momentum_marginal]
  by_contra hcon
  push Not at hcon
  refine hne (ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_)
  simpa using hcon f.toContinuousMap

/-- The explicit witness window `[0,1]` with Dirac ancestry at `r`. -/
noncomputable def witnessEta (r : Set.Icc (0 : ℝ) 1) :
    Measure (Set.Icc (0 : ℝ) 1) := Measure.dirac r

instance (r : Set.Icc (0 : ℝ) 1) : MeasureTheory.IsProbabilityMeasure (witnessEta r) := by
  unfold witnessEta
  infer_instance

/-- The low end of the witness window. -/
def wq0 : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩

/-- The high end of the witness window. -/
def wq1 : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩

/-- **Explicit witness**: the two Dirac ancestries on `[0,1]` are distinct
window laws whose packets share all lifetime data, separated by the
explicit continuous test `q ↦ q`. -/
theorem witness_lifetime_ancestry :
    witnessEta wq0 ≠ witnessEta wq1 ∧
      (packet (witnessEta wq0)).map Prod.fst
        = (packet (witnessEta wq1)).map Prod.fst ∧
      (∀ s : ℝ, ∫ x, Real.exp (-(s * x))
          ∂((packet (witnessEta wq0)).map Prod.fst) = Real.exp (-s)) ∧
      ∫ q, ((q : Set.Icc (0 : ℝ) 1) : ℝ) ∂(witnessEta wq0)
        ≠ ∫ q, ((q : Set.Icc (0 : ℝ) 1) : ℝ) ∂(witnessEta wq1) := by
  have hsep : ∫ q, ((q : Set.Icc (0 : ℝ) 1) : ℝ) ∂(witnessEta wq0)
      ≠ ∫ q, ((q : Set.Icc (0 : ℝ) 1) : ℝ) ∂(witnessEta wq1) := by
    unfold witnessEta
    rw [integral_dirac, integral_dirac]
    norm_num [wq0, wq1]
  refine ⟨fun hEq => hsep (by rw [hEq]),
    (equal_energy_marginals (E := Fin 1) _ _).1,
    fun s => survival_kernel _ s, hsep⟩

end Lifetime

end LifetimeAncestry

/-! ### Primitive transport before leverage

Record `prop:GT-source-metric-transport` (SMET.29–SMET.30).

Rendering: SMET.29 is stated for two aligned finite cards
`S_j : E → ℋ`, `M_j ≻ 0` with `Σ_j = S_j M_j⁻¹ S_j^*`; SMET.30 for two
Hermitian clocks with the entrance projections `P_i = supp Σ_i` (the
spectral support projections of the given PSD covariances), an adjacent
isometry, and matrix-valued horizon integrals `Ŵ_T = ∫₀^T e^{-tH} P e^{-tH}`
over the operator-norm Banach algebra.  The closing telescope clause is the
additive telescoping of the primitive source and metric defects along a
staged route. -/

section SourceMetricTransport

open scoped Matrix.Norms.Operator
open NCG.SourceCoercivityInfluence

namespace MetricTransport

variable {E hdim n₀ n₁ : Type*} [Fintype E] [DecidableEq E] [Fintype hdim]
  [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁]

/-- The physical covariance `Σ = S M⁻¹ S^*` of one aligned finite card. -/
noncomputable def cardSigma (S : Matrix hdim E ℂ) (M : Matrix E E ℂ) :
    Matrix hdim hdim ℂ := S * M⁻¹ * Sᴴ

omit [Fintype hdim] in
/-- **SMET.29**: the exact primitive-defect decomposition separating
source-map motion and action-metric motion. -/
theorem primitive_transport (S₀ S₁ : Matrix hdim E ℂ) (M₀ M₁ : Matrix E E ℂ)
    (hM₀ : M₀.PosDef) (hM₁ : M₁.PosDef) :
    cardSigma S₁ M₁ - cardSigma S₀ M₀
      = (S₁ - S₀) * M₁⁻¹ * S₀ᴴ + S₀ * M₁⁻¹ * (S₁ - S₀)ᴴ
        + (S₁ - S₀) * M₁⁻¹ * (S₁ - S₀)ᴴ
        - S₀ * M₁⁻¹ * (M₁ - M₀) * M₀⁻¹ * S₀ᴴ := by
  unfold cardSigma
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.conjTranspose_sub]
  have hT1 : S₀ * M₁⁻¹ * M₁ * M₀⁻¹ * S₀ᴴ = S₀ * M₀⁻¹ * S₀ᴴ := by
    rw [Matrix.mul_assoc S₀ M₁⁻¹ M₁, posDef_inv_mul_cancel hM₁,
      Matrix.mul_one]
  have hT2 : S₀ * M₁⁻¹ * M₀ * M₀⁻¹ * S₀ᴴ = S₀ * M₁⁻¹ * S₀ᴴ := by
    rw [Matrix.mul_assoc (S₀ * M₁⁻¹) M₀ M₀⁻¹, posDef_mul_inv_cancel hM₀,
      Matrix.mul_one]
  rw [hT1, hT2]
  abel

omit [Fintype E] [DecidableEq E] [Fintype hdim] in
/-- The primitive source and metric defects telescope additively along
direct and staged routes. -/
theorem defect_telescope (S : ℕ → Matrix hdim E ℂ) (M : ℕ → Matrix E E ℂ)
    (r : ℕ) :
    S r - S 0 = ∑ i ∈ Finset.range r, (S (i + 1) - S i) ∧
      M r - M 0 = ∑ i ∈ Finset.range r, (M (i + 1) - M i) := by
  exact ⟨(Finset.sum_range_sub S r).symm, (Finset.sum_range_sub M r).symm⟩

/-- The reflected clock `e^{-tH}`. -/
noncomputable def clock {n : Type*} [Fintype n] [DecidableEq n]
    (Hm : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ := NormedSpace.exp ((-t) • Hm)

/-- The adjacency defect `Δ_i(t) = e^{-tH₁} U - U e^{-tH₀}` (SMET.30). -/
noncomputable def clockDefect (H₀ : Matrix n₀ n₀ ℂ) (H₁ : Matrix n₁ n₁ ℂ)
    (U : Matrix n₁ n₀ ℂ) (t : ℝ) : Matrix n₁ n₀ ℂ :=
  clock H₁ t * U - U * clock H₀ t

/-- The normalized horizon Gramian `Ŵ_T = ∫₀^T e^{-tH} P e^{-tH} dt`. -/
noncomputable def horizonGramian {n : Type*} [Fintype n] [DecidableEq n]
    (Hm : Matrix n n ℂ) (P : Matrix n n ℂ) (T : ℝ) : Matrix n n ℂ :=
  ∫ t in (0 : ℝ)..T, clock Hm t * P * clock Hm t

/-- The clock is a continuous curve. -/
theorem continuous_clock {n : Type*} [Fintype n] [DecidableEq n]
    (Hm : Matrix n n ℂ) : Continuous (clock Hm) := by
  have h1 : Continuous fun u : ℝ => NormedSpace.exp (u • Hm) :=
    continuous_iff_continuousAt.mpr fun u =>
      (hasDerivAt_exp_smul_const' Hm u).continuousAt
  exact h1.comp continuous_neg

/-- The clock of a Hermitian generator is Hermitian. -/
theorem clock_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    {Hm : Matrix n n ℂ} (hH : Hm.IsHermitian) (t : ℝ) :
    (clock Hm t)ᴴ = clock Hm t := by
  unfold clock
  rw [← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_smul, hH.eq]
  norm_num

/-- The transpose of the adjacency defect under Hermitian clocks. -/
theorem clockDefect_conjTranspose (H₀ : Matrix n₀ n₀ ℂ)
    (H₁ : Matrix n₁ n₁ ℂ) (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix n₁ n₀ ℂ) (t : ℝ) :
    (clockDefect H₀ H₁ U t)ᴴ
      = Uᴴ * clock H₁ t - clock H₀ t * Uᴴ := by
  unfold clockDefect
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, clock_conjTranspose hH₀,
    clock_conjTranspose hH₁]

/-- The pointwise integrand identity behind SMET.30. -/
theorem clock_defect_pointwise (H₀ : Matrix n₀ n₀ ℂ) (H₁ : Matrix n₁ n₁ ℂ)
    (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian) (U : Matrix n₁ n₀ ℂ)
    (P₀ : Matrix n₀ n₀ ℂ) (P₁ : Matrix n₁ n₁ ℂ) (t : ℝ) :
    clock H₁ t * P₁ * clock H₁ t
        - U * (clock H₀ t * P₀ * clock H₀ t) * Uᴴ
      = clock H₁ t * (P₁ - U * P₀ * Uᴴ) * clock H₁ t
        + (clockDefect H₀ H₁ U t * P₀ * clock H₀ t * Uᴴ
          + U * clock H₀ t * P₀ * (clockDefect H₀ H₁ U t)ᴴ
          + clockDefect H₀ H₁ U t * P₀ * (clockDefect H₀ H₁ U t)ᴴ) := by
  rw [clockDefect_conjTranspose H₀ H₁ hH₀ hH₁ U t]
  unfold clockDefect
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **SMET.30**: the normalized horizon defect splits exactly into the
entrance-range motion and the completed-clock motion. -/
theorem horizon_defect (T : ℝ) (H₀ : Matrix n₀ n₀ ℂ) (H₁ : Matrix n₁ n₁ ℂ)
    (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian) (U : Matrix n₁ n₀ ℂ)
    (_hU : Uᴴ * U = 1) {Sg₀ : Matrix n₀ n₀ ℂ} {Sg₁ : Matrix n₁ n₁ ℂ}
    (hSg0 : Sg₀.PosSemidef) (hSg1 : Sg₁.PosSemidef) :
    horizonGramian H₁ (supportProj hSg1.1) T
        - U * horizonGramian H₀ (supportProj hSg0.1) T * Uᴴ
      = (∫ t in (0 : ℝ)..T, clock H₁ t
            * (supportProj hSg1.1 - U * supportProj hSg0.1 * Uᴴ)
            * clock H₁ t)
        + ∫ t in (0 : ℝ)..T,
            (clockDefect H₀ H₁ U t * supportProj hSg0.1 * clock H₀ t * Uᴴ
              + U * clock H₀ t * supportProj hSg0.1
                  * (clockDefect H₀ H₁ U t)ᴴ
              + clockDefect H₀ H₁ U t * supportProj hSg0.1
                  * (clockDefect H₀ H₁ U t)ᴴ) := by
  set P₀ := supportProj hSg0.1
  set P₁ := supportProj hSg1.1
  -- conjugation by the isometry as a continuous linear map
  let conjU : Matrix n₀ n₀ ℂ →L[ℂ] Matrix n₁ n₁ ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => U * X * Uᴴ
        map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]
        map_smul' := fun c X => by
          rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  -- continuity of the three integrands
  have hcΔ : Continuous fun t => clockDefect H₀ H₁ U t := by
    unfold clockDefect
    exact ((continuous_clock H₁).matrix_mul continuous_const).sub
      (continuous_const.matrix_mul (continuous_clock H₀))
  have hcΔH : Continuous fun t => (clockDefect H₀ H₁ U t)ᴴ := by
    have hfun : (fun t => (clockDefect H₀ H₁ U t)ᴴ)
        = fun t => Uᴴ * clock H₁ t - clock H₀ t * Uᴴ :=
      funext fun t => clockDefect_conjTranspose H₀ H₁ hH₀ hH₁ U t
    rw [hfun]
    exact (continuous_const.matrix_mul (continuous_clock H₁)).sub
      ((continuous_clock H₀).matrix_mul continuous_const)
  have hc0 : Continuous fun t => clock H₀ t * P₀ * clock H₀ t :=
    (((continuous_clock H₀).matrix_mul continuous_const).matrix_mul
      (continuous_clock H₀))
  have hc1 : Continuous fun t =>
      clock H₁ t * (P₁ - U * P₀ * Uᴴ) * clock H₁ t :=
    (((continuous_clock H₁).matrix_mul continuous_const).matrix_mul
      (continuous_clock H₁))
  have hc2 : Continuous fun t =>
      clockDefect H₀ H₁ U t * P₀ * clock H₀ t * Uᴴ
        + U * clock H₀ t * P₀ * (clockDefect H₀ H₁ U t)ᴴ
        + clockDefect H₀ H₁ U t * P₀ * (clockDefect H₀ H₁ U t)ᴴ := by
    refine Continuous.add (Continuous.add ?_ ?_) ?_
    · exact ((hcΔ.matrix_mul continuous_const).matrix_mul
        (continuous_clock H₀)).matrix_mul continuous_const
    · exact ((continuous_const.matrix_mul
        (continuous_clock H₀)).matrix_mul continuous_const).matrix_mul hcΔH
    · exact (hcΔ.matrix_mul continuous_const).matrix_mul hcΔH
  have hcW1 : Continuous fun t => clock H₁ t * P₁ * clock H₁ t :=
    (((continuous_clock H₁).matrix_mul continuous_const).matrix_mul
      (continuous_clock H₁))
  -- pull the conjugation through the horizon integral
  have hconj : U * horizonGramian H₀ P₀ T * Uᴴ
      = ∫ t in (0 : ℝ)..T, U * (clock H₀ t * P₀ * clock H₀ t) * Uᴴ := by
    have h := conjU.intervalIntegral_comp_comm
      (hc0.intervalIntegrable (μ := MeasureTheory.volume) 0 T)
    unfold horizonGramian
    calc U * (∫ t in (0 : ℝ)..T, clock H₀ t * P₀ * clock H₀ t) * Uᴴ
        = conjU (∫ t in (0 : ℝ)..T, clock H₀ t * P₀ * clock H₀ t) := by
          simp [conjU, LinearMap.coe_toContinuousLinearMap']
      _ = ∫ t in (0 : ℝ)..T, conjU (clock H₀ t * P₀ * clock H₀ t) := h.symm
      _ = ∫ t in (0 : ℝ)..T, U * (clock H₀ t * P₀ * clock H₀ t) * Uᴴ := by
          refine intervalIntegral.integral_congr fun t _ => ?_
          simp [conjU, LinearMap.coe_toContinuousLinearMap']
  have hcU0 : Continuous fun t => U * (clock H₀ t * P₀ * clock H₀ t) * Uᴴ :=
    (continuous_const.matrix_mul hc0).matrix_mul continuous_const
  calc horizonGramian H₁ P₁ T - U * horizonGramian H₀ P₀ T * Uᴴ
      = ∫ t in (0 : ℝ)..T, (clock H₁ t * P₁ * clock H₁ t
          - U * (clock H₀ t * P₀ * clock H₀ t) * Uᴴ) := by
        rw [hconj]
        unfold horizonGramian
        rw [← intervalIntegral.integral_sub
          (hcW1.intervalIntegrable _ _) (hcU0.intervalIntegrable _ _)]
    _ = ∫ t in (0 : ℝ)..T,
          (clock H₁ t * (P₁ - U * P₀ * Uᴴ) * clock H₁ t
            + (clockDefect H₀ H₁ U t * P₀ * clock H₀ t * Uᴴ
              + U * clock H₀ t * P₀ * (clockDefect H₀ H₁ U t)ᴴ
              + clockDefect H₀ H₁ U t * P₀ * (clockDefect H₀ H₁ U t)ᴴ)) :=
        intervalIntegral.integral_congr fun t _ =>
          clock_defect_pointwise H₀ H₁ hH₀ hH₁ U P₀ P₁ t
    _ = (∫ t in (0 : ℝ)..T, clock H₁ t * (P₁ - U * P₀ * Uᴴ) * clock H₁ t)
        + ∫ t in (0 : ℝ)..T,
            (clockDefect H₀ H₁ U t * P₀ * clock H₀ t * Uᴴ
              + U * clock H₀ t * P₀ * (clockDefect H₀ H₁ U t)ᴴ
              + clockDefect H₀ H₁ U t * P₀
                  * (clockDefect H₀ H₁ U t)ᴴ) :=
        intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
          (hc2.intervalIntegrable _ _)

end MetricTransport

end SourceMetricTransport

/-! ### A positive entrance residual can be a complete clock follower

Record `cth:GT-static-residual-follower`.

Rendering: the explicit packet `ℋ = ℝ²`, `B1 = e₁`, `Y1 = e₂`,
`H = [[1,α],[α,1]]` with `0 < |α| < 1`.  The entrance residual
`R_ent = ⟨Y,(1-P_B)Y⟩ = 1` is computed against the explicit orthogonal
projection onto the source span (with its defining clauses proved), and the
dynamic residual vanishes because the semigroup-cyclic carrier
`span{e^{-tH}B : t ≥ 0}` is all of `ℝ²`: `R_dyn = ⟨Y,(1-P)Y⟩ = 0` for any
projection `P` fixing the carrier.  Positivity of the clock (`H ⪰ 0` for
`|α| ≤ 1`) is included. -/

section StaticResidualFollower

open scoped Matrix.Norms.Operator

namespace StaticResidual

/-- The coupled clock generator `H = [[1,α],[α,1]]`. -/
def coupledH (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![1, α], ![α, 1]]

/-- The source vector `B1 = e₁`. -/
def srcB : Fin 2 → ℝ := ![1, 0]

/-- The target vector `Y1 = e₂`. -/
def tgtY : Fin 2 → ℝ := ![0, 1]

/-- The explicit entrance projection `P_B` onto the source span. -/
def entProj : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![1, 0], ![0, 0]]

/-- `P_B` is the orthogonal projection onto the span of the source. -/
theorem entProj_is_projection :
    entProj * entProj = entProj ∧ entProjᵀ = entProj ∧
      entProj *ᵥ srcB = srcB ∧
      ∀ v : Fin 2 → ℝ, srcB ⬝ᵥ (v - entProj *ᵥ v) = 0 := by
  refine ⟨?_, ?_, ?_, fun v => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [entProj, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [entProj]
  · funext i
    fin_cases i <;>
      simp [entProj, srcB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [entProj, srcB, dotProduct, Fin.sum_univ_two]

/-- The coupled clock generator is positive semidefinite for `|α| ≤ 1`. -/
theorem coupledH_posSemidef (α : ℝ) (hα : |α| ≤ 1) :
    (coupledH α).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [coupledH, Matrix.conjTranspose]
  · intro x
    have hx : star x ⬝ᵥ (coupledH α *ᵥ x)
        = x 0 * x 0 + α * (x 0 * x 1) + α * (x 1 * x 0) + x 1 * x 1 := by
      simp [coupledH, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hx]
    rcases abs_le.mp hα with ⟨h1, h2⟩
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]

/-- Eigenvector transport through the exponential clock. -/
theorem exp_mulVec_eigen {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v : n → ℝ) (mu : ℝ) (h : A *ᵥ v = mu • v) :
    NormedSpace.exp A *ᵥ v = Real.exp mu • v := by
  -- multiplication against the fixed vector, as a continuous linear map
  let mulv : Matrix n n ℝ →L[ℝ] (n → ℝ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M *ᵥ v
        map_add' := fun M N => Matrix.add_mulVec M N v
        map_smul' := fun c M => by
          rw [RingHom.id_apply]
          exact Matrix.smul_mulVec c M v }
  have hpow : ∀ k : ℕ, (A ^ k) *ᵥ v = (mu ^ k) • v := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih,
        smul_smul, pow_succ]
      ring_nf
  have hsum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have happ : HasSum (fun k => ((k.factorial : ℝ))⁻¹ • ((A ^ k) *ᵥ v))
      (NormedSpace.exp A *ᵥ v) := by
    have h0 := mulv.hasSum hsum
    have heq : ∀ k : ℕ, mulv (((k.factorial : ℝ))⁻¹ • A ^ k)
        = ((k.factorial : ℝ))⁻¹ • ((A ^ k) *ᵥ v) := fun k => by
      rw [map_smul]
      rfl
    have hval : mulv (NormedSpace.exp A) = NormedSpace.exp A *ᵥ v := rfl
    rw [← hval, ← funext heq]
    exact h0
  have h2 : HasSum (fun k => (((k.factorial : ℝ))⁻¹ * mu ^ k) • v)
      (NormedSpace.exp A *ᵥ v) := by
    simpa [hpow, smul_smul] using happ
  have h3 : HasSum (fun k => ((k.factorial : ℝ))⁻¹ • mu ^ k)
      (NormedSpace.exp mu) := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) mu
  have h4 : HasSum (fun k => (((k.factorial : ℝ))⁻¹ • mu ^ k) • v)
      ((NormedSpace.exp mu) • v) := h3.smul_const v
  have h5 := h4.unique (by simpa [smul_smul] using h2)
  rw [Real.exp_eq_exp_ℝ, ← h5]

/-- The two clock eigenvectors of the coupled generator. -/
theorem coupledH_eigen (α : ℝ) :
    coupledH α *ᵥ ![1, 1] = (1 + α) • ![1, 1] ∧
      coupledH α *ᵥ ![1, -1] = (1 - α) • ![1, -1] := by
  constructor <;>
    · funext i
      fin_cases i <;>
        simp [coupledH, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
        ring

/-- The semigroup-cyclic carrier of the source under the coupled clock. -/
def cyclicCarrier (α : ℝ) : Submodule ℝ (Fin 2 → ℝ) :=
  Submodule.span ℝ
    {v | ∃ t : ℝ, 0 ≤ t ∧ v = NormedSpace.exp ((-t) • coupledH α) *ᵥ srcB}

/-- The clock orbit of the source at time `t`. -/
theorem clock_orbit (α t : ℝ) :
    NormedSpace.exp ((-t) • coupledH α) *ᵥ srcB
      = ((1 : ℝ) / 2 * Real.exp (-t * (1 + α))) • ![1, 1]
        + ((1 : ℝ) / 2 * Real.exp (-t * (1 - α))) • ![1, -1] := by
  obtain ⟨hw1, hw2⟩ := coupledH_eigen α
  have he1 : ((-t) • coupledH α) *ᵥ ![1, 1] = (-t * (1 + α)) • ![1, 1] := by
    rw [Matrix.smul_mulVec, hw1, smul_smul]
  have he2 : ((-t) • coupledH α) *ᵥ ![1, -1] = (-t * (1 - α)) • ![1, -1] := by
    rw [Matrix.smul_mulVec, hw2, smul_smul]
  have hsrc : srcB = ((1 : ℝ) / 2) • ![1, 1] + ((1 : ℝ) / 2) • ![1, -1] := by
    funext i
    fin_cases i <;> norm_num [srcB]
  rw [hsrc, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    exp_mulVec_eigen _ _ _ he1, exp_mulVec_eigen _ _ _ he2, smul_smul,
    smul_smul]

/-- The semigroup-cyclic carrier is everything when `α ≠ 0`. -/
theorem cyclicCarrier_eq_top (α : ℝ) (hα : α ≠ 0) : cyclicCarrier α = ⊤ := by
  have hmem : ∀ t : ℝ, 0 ≤ t →
      NormedSpace.exp ((-t) • coupledH α) *ᵥ srcB ∈ cyclicCarrier α :=
    fun t ht => Submodule.subset_span ⟨t, ht, rfl⟩
  have h0 : srcB ∈ cyclicCarrier α := by
    have := hmem 0 le_rfl
    have hz : NormedSpace.exp ((-(0 : ℝ)) • coupledH α) *ᵥ srcB = srcB := by
      norm_num [NormedSpace.exp_zero, Matrix.one_mulVec]
    rwa [hz] at this
  have h1 : NormedSpace.exp ((-(1:ℝ)) • coupledH α) *ᵥ srcB
      ∈ cyclicCarrier α := hmem 1 zero_le_one
  -- extract the second basis vector
  set a := Real.exp (-(1:ℝ) * (1 + α)) with ha
  set b := Real.exp (-(1:ℝ) * (1 - α)) with hb
  have hab : a ≠ b := by
    rw [ha, hb]
    intro hcon
    have := Real.exp_injective hcon
    have : α = 0 := by linarith
    exact hα this
  have horb : NormedSpace.exp ((-(1:ℝ)) • coupledH α) *ᵥ srcB
      = ((1 : ℝ) / 2 * a) • ![1, 1] + ((1 : ℝ) / 2 * b) • ![1, -1] := by
    rw [clock_orbit α 1, ← ha, ← hb]
  have he2mem : (![0, 1] : Fin 2 → ℝ) ∈ cyclicCarrier α := by
    -- e₂ = (a-b)⁻¹ • (orbit 1 - ((a+b)/2) • srcB)
    have hc : ((a - b) / 2) ≠ 0 :=
      div_ne_zero (sub_ne_zero.mpr hab) two_ne_zero
    have hcomb : (![0, 1] : Fin 2 → ℝ)
        = ((a - b) / 2)⁻¹ •
          ((NormedSpace.exp ((-(1:ℝ)) • coupledH α) *ᵥ srcB)
            - ((a + b) / 2) • srcB) := by
      rw [horb]
      funext i
      fin_cases i
      · simp [srcB]
        field_simp
        right
        ring
      · simp [srcB]
        field_simp
        ring
    rw [hcomb]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h1
      (Submodule.smul_mem _ _ h0))
  have he1mem : (![1, 0] : Fin 2 → ℝ) ∈ cyclicCarrier α := by
    have : srcB = (![1, 0] : Fin 2 → ℝ) := by
      funext i; fin_cases i <;> norm_num [srcB]
    rwa [this] at h0
  rw [eq_top_iff]
  intro x _
  have hx : x = x 0 • (![1, 0] : Fin 2 → ℝ) + x 1 • (![0, 1] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;> simp
  rw [hx]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ he1mem)
    (Submodule.smul_mem _ _ he2mem)

/-- **`cth:GT-static-residual-follower`**: the packet has full entrance
residual `R_ent = 1` yet vanishing dynamic residual `R_dyn = 0`; a positive
entrance residual can be a complete clock follower. -/
theorem static_residual_follower (α : ℝ) (hα0 : α ≠ 0) (hα1 : |α| < 1) :
    (coupledH α).PosSemidef ∧
      tgtY ⬝ᵥ ((1 - entProj) *ᵥ tgtY) = 1 ∧
      cyclicCarrier α = ⊤ ∧
      ∀ P : Matrix (Fin 2) (Fin 2) ℝ,
        (∀ v ∈ cyclicCarrier α, P *ᵥ v = v) →
        tgtY ⬝ᵥ ((1 - P) *ᵥ tgtY) = 0 := by
  refine ⟨coupledH_posSemidef α hα1.le, ?_, cyclicCarrier_eq_top α hα0,
    fun P hP => ?_⟩
  · simp [tgtY, entProj, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.one_apply]
  · have hfix : P *ᵥ tgtY = tgtY :=
      hP tgtY (by rw [cyclicCarrier_eq_top α hα0]; trivial)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix]
    simp

end StaticResidual

end StaticResidualFollower

/-! ### Three independent leverage-collapse mechanisms

Record `cth:GT-source-metric-collapses`.

Rendering: with `c_T = (1-e^{-2T})/2`, the three explicit witnesses are
constructed in full.  (i) On the scalar carrier, `B_n = ε_n`, `M_n = ε_n²`
has `Σ = B M⁻¹ B = 1` and physical Gramian `c_T` while the raw coefficient
Gramian `c_T ε_n² → 0`: coordinate collapse only.  (ii) `B_n = 1`,
`M_n = ε_n⁻²` keeps the full scalar source range while `Σ = ε_n²` and the
minimum physical control energy (an attained `IsLeast` over continuous
controls with unit reach) diverges exactly like `(c_T ε_n²)⁻¹`.  (iii) On
`ℝ²` with `H = diag(1,2)`, `B_ε 1 = (1,ε)ᵀ`, the entrance reserve is
`1+ε²`, every finite source is clock-cyclic, the normalized horizon
Gramian and its determinant take the displayed exact values, and its
smallest eigenvalue (the infimum of unit Rayleigh quotients) tends to
zero while the limiting source loses `e₂` from its cyclic space. -/

section LeverageCollapse

open scoped Matrix.Norms.Operator
open Filter

namespace Leverage

/-- The horizon constant `c_T = (1-e^{-2T})/2`. -/
noncomputable def cT (T : ℝ) : ℝ := (1 - Real.exp (-2 * T)) / 2

/-- The scalar unit-action covariance `Σ = B M⁻¹ B`. -/
noncomputable def scalarSigma (b m : ℝ) : ℝ := b * m⁻¹ * b

/-- Exponential window integrals. -/
theorem integral_exp_neg_mul (a T : ℝ) (ha : a ≠ 0) :
    ∫ t in (0 : ℝ)..T, Real.exp (-a * t) = (1 - Real.exp (-a * T)) / a := by
  have h : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun u => (1 - Real.exp (-a * u)) / a) (Real.exp (-a * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => -a * u) (-a) t := by
      simpa using (hasDerivAt_id t).const_mul (-a)
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-a * u))
        (Real.exp (-a * t) * -a) t := (Real.hasDerivAt_exp _).comp t h1
    have h4 : HasDerivAt (fun u : ℝ => 1 - Real.exp (-a * u))
        (-(Real.exp (-a * t) * -a)) t := h2.const_sub 1
    have h5 := h4.div_const a
    have heq : -(Real.exp (-a * t) * -a) / a = Real.exp (-a * t) := by
      field_simp
    rw [heq] at h5
    exact h5
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num

/-- The horizon constant is the two-window integral and is positive. -/
theorem cT_eq_integral (T : ℝ) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, Real.exp (-2 * t)) = cT T ∧ 0 < cT T := by
  constructor
  · rw [integral_exp_neg_mul 2 T two_ne_zero]
    rfl
  · unfold cT
    have h1 : Real.exp (-2 * T) < 1 := by
      rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_lt_exp.mpr (by linarith)
    linarith

/-- **Mechanism (i): coordinate collapse.**  The rescaled packets have
constant unit covariance and constant physical Gramian `c_T`, while the raw
coefficient Gramian collapses like `c_T ε_n² → 0`. -/
theorem coordinate_collapse (T : ℝ) (hT : 0 < T) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (nhds 0)) :
    (∀ n, scalarSigma (ε n) ((ε n) ^ 2) = 1) ∧
      (∀ n, (∫ t in (0 : ℝ)..T,
          Real.exp (-t) * scalarSigma (ε n) ((ε n) ^ 2) * Real.exp (-t))
        = cT T) ∧
      (∀ n, (∫ t in (0 : ℝ)..T, Real.exp (-t) * (ε n * ε n) * Real.exp (-t))
        = cT T * (ε n) ^ 2) ∧
      Tendsto (fun n => cT T * (ε n) ^ 2) atTop (nhds 0) := by
  have hsig : ∀ n, scalarSigma (ε n) ((ε n) ^ 2) = 1 := by
    intro n
    unfold scalarSigma
    have := (hε n).ne'
    field_simp
  have hker : ∀ c : ℝ, (∫ t in (0 : ℝ)..T, Real.exp (-t) * c * Real.exp (-t))
      = cT T * c := by
    intro c
    have hpt : ∀ t : ℝ, Real.exp (-t) * c * Real.exp (-t)
        = c * Real.exp (-2 * t) := by
      intro t
      have he : Real.exp (-2 * t) = Real.exp (-t) * Real.exp (-t) := by
        rw [← Real.exp_add]
        ring_nf
      rw [he]
      ring
    rw [intervalIntegral.integral_congr fun t _ => hpt t,
      intervalIntegral.integral_const_mul, (cT_eq_integral T hT).1]
    ring
  refine ⟨hsig, fun n => ?_, fun n => ?_, ?_⟩
  · rw [hker]
    rw [hsig n]
    ring
  · rw [hker]
    ring
  · have h2 : Tendsto (fun n => (ε n) ^ 2) atTop (nhds 0) := by
      have := hlim.pow 2
      simpa using this
    have := h2.const_mul (cT T)
    simpa using this

/-- **Mechanism (ii): genuine reserve collapse.**  The source range is the
full scalar carrier for every `n`, the covariance collapses to `ε_n²`, and
the minimum physical control energy to reach the unit target is attained
and diverges exactly like `(c_T ε_n²)⁻¹`. -/
theorem reserve_collapse (T : ℝ) (hT : 0 < T) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (nhds 0)) :
    Submodule.span ℝ {(1 : ℝ)} = ⊤ ∧
      (∀ n, scalarSigma 1 (((ε n)⁻¹) ^ 2) = (ε n) ^ 2) ∧
      (∀ n, IsLeast
        {r : ℝ | ∃ u : ℝ → ℝ, Continuous u ∧
          (∫ t in (0 : ℝ)..T, Real.exp (-t) * u t) = 1 ∧
          r = ∫ t in (0 : ℝ)..T, ((ε n)⁻¹) ^ 2 * u t ^ 2}
        ((cT T * (ε n) ^ 2)⁻¹)) ∧
      Tendsto (fun n => (cT T * (ε n) ^ 2)⁻¹) atTop atTop := by
  obtain ⟨hint2, hcT⟩ := cT_eq_integral T hT
  have hcT0 : cT T ≠ 0 := hcT.ne'
  refine ⟨?_, ?_, fun n => ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    have : x = x • (1 : ℝ) := by simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · intro n
    unfold scalarSigma
    have := (hε n).ne'
    field_simp
  · have hεn := hε n
    have hεn0 : ε n ≠ 0 := hεn.ne'
    constructor
    · -- attained at the matched-filter control `u₀ = e^{-t}/c_T`
      refine ⟨fun t => Real.exp (-t) / cT T, by fun_prop, ?_, ?_⟩
      · have hpt : ∀ t : ℝ, Real.exp (-t) * (Real.exp (-t) / cT T)
            = (cT T)⁻¹ * Real.exp (-2 * t) := by
          intro t
          have he : Real.exp (-2 * t) = Real.exp (-t) * Real.exp (-t) := by
            rw [← Real.exp_add]; ring_nf
          rw [he]
          ring
        rw [intervalIntegral.integral_congr fun t _ => hpt t,
          intervalIntegral.integral_const_mul, hint2]
        field_simp
      · have hpt : ∀ t : ℝ, ((ε n)⁻¹) ^ 2 * (Real.exp (-t) / cT T) ^ 2
            = (((ε n)⁻¹) ^ 2 * (cT T)⁻¹ ^ 2) * Real.exp (-2 * t) := by
          intro t
          have he : Real.exp (-2 * t) = Real.exp (-t) * Real.exp (-t) := by
            rw [← Real.exp_add]; ring_nf
          rw [he]
          field_simp
        rw [intervalIntegral.integral_congr fun t _ => hpt t,
          intervalIntegral.integral_const_mul, hint2]
        field_simp
    · rintro r ⟨u, hu, hreach, rfl⟩
      -- Cauchy–Schwarz against the matched filter
      have hint_u : IntervalIntegrable (fun t => Real.exp (-t) * u t)
          MeasureTheory.volume 0 T := by
        apply Continuous.intervalIntegrable
        fun_prop
      have hint_usq : IntervalIntegrable (fun t => u t ^ 2)
          MeasureTheory.volume 0 T := by
        apply Continuous.intervalIntegrable
        fun_prop
      have hint_e2 : IntervalIntegrable (fun t => Real.exp (-2 * t))
          MeasureTheory.volume 0 T := by
        apply Continuous.intervalIntegrable
        fun_prop
      have hL2 : (1 : ℝ) / cT T ≤ ∫ t in (0 : ℝ)..T, u t ^ 2 := by
        have hnn : 0 ≤ ∫ t in (0 : ℝ)..T,
            (u t - Real.exp (-t) / cT T) ^ 2 := by
          apply intervalIntegral.integral_nonneg hT.le
          intro t _
          positivity
        have hexp : ∀ t : ℝ, (u t - Real.exp (-t) / cT T) ^ 2
            = u t ^ 2 - (2 / cT T) * (Real.exp (-t) * u t)
              + (cT T)⁻¹ ^ 2 * Real.exp (-2 * t) := by
          intro t
          have he : Real.exp (-2 * t) = Real.exp (-t) * Real.exp (-t) := by
            rw [← Real.exp_add]; ring_nf
          rw [he]
          field_simp
          ring
        rw [intervalIntegral.integral_congr fun t _ => hexp t] at hnn
        rw [intervalIntegral.integral_add
          (hint_usq.sub (hint_u.const_mul (2 / cT T)))
          (hint_e2.const_mul ((cT T)⁻¹ ^ 2)),
          intervalIntegral.integral_sub hint_usq
            (hint_u.const_mul (2 / cT T)),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, hreach, hint2] at hnn
        have : 0 ≤ (∫ t in (0 : ℝ)..T, u t ^ 2) - 2 / cT T + (cT T)⁻¹ := by
          have hsimp : (cT T)⁻¹ ^ 2 * cT T = (cT T)⁻¹ := by
            field_simp
          rw [mul_one] at hnn
          rw [hsimp] at hnn
          linarith
        have h2c : 2 / cT T - (cT T)⁻¹ = 1 / cT T := by
          field_simp
          norm_num
        linarith [h2c]
      have hpull : (∫ t in (0 : ℝ)..T, ((ε n)⁻¹) ^ 2 * u t ^ 2)
          = ((ε n)⁻¹) ^ 2 * ∫ t in (0 : ℝ)..T, u t ^ 2 :=
        intervalIntegral.integral_const_mul _ _
      rw [hpull]
      have hpos : (0 : ℝ) < ((ε n)⁻¹) ^ 2 := by positivity
      calc (cT T * (ε n) ^ 2)⁻¹ = ((ε n)⁻¹) ^ 2 * (1 / cT T) := by
            field_simp
        _ ≤ ((ε n)⁻¹) ^ 2 * ∫ t in (0 : ℝ)..T, u t ^ 2 := by
            exact mul_le_mul_of_nonneg_left hL2 hpos.le
  · have hpos : ∀ n, 0 < cT T * (ε n) ^ 2 := fun n => by
      have := hε n
      positivity
    have hto : Tendsto (fun n => cT T * (ε n) ^ 2) atTop (nhds 0) := by
      have h2 : Tendsto (fun n => (ε n) ^ 2) atTop (nhds 0) := by
        have := hlim.pow 2
        simpa using this
      have := h2.const_mul (cT T)
      simpa using this
    have hmem : Tendsto (fun n => cT T * (ε n) ^ 2) atTop
        (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hto
        (Filter.Eventually.of_forall hpos)
    exact tendsto_inv_nhdsGT_zero.comp hmem

/-! Mechanism (iii): normalized cyclic-geometry collapse on `ℝ²`. -/

/-- The two-level clock `H = diag(1,2)`. -/
noncomputable def diagH : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 2]

/-- The tilted source `B_ε 1 = (1, ε)ᵀ`. -/
def tiltB (ε : ℝ) : Fin 2 → ℝ := ![1, ε]

/-- The normalized entrance projection `P_B = (1+ε²)⁻¹ B Bᵀ`. -/
noncomputable def tiltProj (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 + ε ^ 2)⁻¹ • Matrix.vecMulVec (tiltB ε) (tiltB ε)

/-- `P_B` is the orthogonal projection onto the tilted source line. -/
theorem tiltProj_is_projection (ε : ℝ) :
    tiltProj ε * tiltProj ε = tiltProj ε ∧ (tiltProj ε)ᵀ = tiltProj ε ∧
      tiltProj ε *ᵥ tiltB ε = tiltB ε := by
  have hne : (1 : ℝ) + ε ^ 2 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      · simp [tiltProj, tiltB, Matrix.vecMulVec, Matrix.mul_apply,
          Fin.sum_univ_two]
        try field_simp
        try ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tiltProj, tiltB, Matrix.vecMulVec, Matrix.transpose_apply,
        mul_comm]
  · funext i
    fin_cases i <;>
      · simp [tiltProj, tiltB, Matrix.vecMulVec, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two]
        try field_simp
        try ring

/-- The entrance reserve of the tilted source is `1 + ε²`. -/
theorem tilt_reserve (ε : ℝ) : tiltB ε ⬝ᵥ tiltB ε = 1 + ε ^ 2 := by
  simp [tiltB, dotProduct, Fin.sum_univ_two]
  ring

/-- The two-level clock evaluates to the diagonal exponential. -/
theorem diagH_clock (t : ℝ) :
    NormedSpace.exp ((-t) • diagH)
      = Matrix.diagonal ![Real.exp (-t), Real.exp (-2 * t)] := by
  have hsm : (-t) • diagH = Matrix.diagonal ![-t, -2 * t] := by
    unfold diagH
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    fin_cases i <;> · simp; try ring
  rw [hsm, Matrix.exp_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [Pi.coe_exp, Real.exp_eq_exp_ℝ]

/-- The three elementary window integrals of the two-level clock. -/
theorem clock_window_integrals (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Real.exp (-t) * Real.exp (-t))
      = (1 - Real.exp (-2 * T)) / 2 ∧
    (∫ t in (0 : ℝ)..T, Real.exp (-t) * Real.exp (-2 * t))
      = (1 - Real.exp (-3 * T)) / 3 ∧
    (∫ t in (0 : ℝ)..T, Real.exp (-2 * t) * Real.exp (-2 * t))
      = (1 - Real.exp (-4 * T)) / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · have hpt : ∀ t : ℝ, Real.exp (-t) * Real.exp (-t) = Real.exp (-2 * t) := by
      intro t
      rw [← Real.exp_add]
      congr 1
      ring
    rw [intervalIntegral.integral_congr fun t _ => hpt t,
      integral_exp_neg_mul 2 T two_ne_zero]
  · have hpt : ∀ t : ℝ, Real.exp (-t) * Real.exp (-2 * t)
        = Real.exp (-3 * t) := by
      intro t
      rw [← Real.exp_add]
      congr 1
      ring
    rw [intervalIntegral.integral_congr fun t _ => hpt t,
      integral_exp_neg_mul 3 T three_ne_zero]
  · have hpt : ∀ t : ℝ, Real.exp (-2 * t) * Real.exp (-2 * t)
        = Real.exp (-4 * t) := by
      intro t
      rw [← Real.exp_add]
      congr 1
      ring
    rw [intervalIntegral.integral_congr fun t _ => hpt t,
      integral_exp_neg_mul 4 T four_ne_zero]

/-- The normalized horizon Gramian of the tilted packet. -/
noncomputable def tiltGramian (ε T : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∫ t in (0 : ℝ)..T, NormedSpace.exp ((-t) • diagH) * tiltProj ε
    * NormedSpace.exp ((-t) • diagH)

/-- The exact value of the normalized horizon Gramian (the displayed matrix
in the manuscript proof). -/
theorem tiltGramian_value (ε T : ℝ) :
    tiltGramian ε T = (1 + ε ^ 2)⁻¹ • Matrix.of
      ![![(1 - Real.exp (-2 * T)) / 2, ε * ((1 - Real.exp (-3 * T)) / 3)],
        ![ε * ((1 - Real.exp (-3 * T)) / 3),
          ε ^ 2 * ((1 - Real.exp (-4 * T)) / 4)]] := by
  obtain ⟨hI2, hI3, hI4⟩ := clock_window_integrals T
  set A2 : Matrix (Fin 2) (Fin 2) ℝ :=
    (1 + ε ^ 2)⁻¹ • Matrix.of ![![1, 0], ![0, 0]] with hA2
  set A3 : Matrix (Fin 2) (Fin 2) ℝ :=
    ((1 + ε ^ 2)⁻¹ * ε) • Matrix.of ![![0, 1], ![1, 0]] with hA3
  set A4 : Matrix (Fin 2) (Fin 2) ℝ :=
    ((1 + ε ^ 2)⁻¹ * ε ^ 2) • Matrix.of ![![0, 0], ![0, 1]] with hA4
  have hpt : ∀ t : ℝ, NormedSpace.exp ((-t) • diagH) * tiltProj ε
      * NormedSpace.exp ((-t) • diagH)
      = (Real.exp (-t) * Real.exp (-t)) • A2
        + (Real.exp (-t) * Real.exp (-2 * t)) • A3
        + (Real.exp (-2 * t) * Real.exp (-2 * t)) • A4 := by
    intro t
    rw [diagH_clock]
    ext i j
    fin_cases i <;> fin_cases j <;>
      · simp [hA2, hA3, hA4, tiltProj, tiltB, Matrix.vecMulVec,
          Matrix.mul_apply, Matrix.diagonal]
        try ring
  have hc2 : Continuous fun t : ℝ =>
      (Real.exp (-t) * Real.exp (-t)) • A2 := by fun_prop
  have hc3 : Continuous fun t : ℝ =>
      (Real.exp (-t) * Real.exp (-2 * t)) • A3 := by fun_prop
  have hc4 : Continuous fun t : ℝ =>
      (Real.exp (-2 * t) * Real.exp (-2 * t)) • A4 := by fun_prop
  unfold tiltGramian
  rw [intervalIntegral.integral_congr fun t _ => hpt t,
    intervalIntegral.integral_add ((hc2.intervalIntegrable 0 T).add
      (hc3.intervalIntegrable 0 T)) (hc4.intervalIntegrable 0 T),
    intervalIntegral.integral_add (hc2.intervalIntegrable 0 T)
      (hc3.intervalIntegrable 0 T),
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, hI2, hI3, hI4]
  ext i j
  fin_cases i <;> fin_cases j <;> · simp [hA2, hA3, hA4]; try ring

/-- The exact determinant of the normalized horizon Gramian (the displayed
determinant of the manuscript). -/
theorem tiltGramian_det (ε T : ℝ) :
    (tiltGramian ε T).det
      = ε ^ 2 / (1 + ε ^ 2) ^ 2
        * ((1 - Real.exp (-2 * T)) / 2 * ((1 - Real.exp (-4 * T)) / 4)
          - ((1 - Real.exp (-3 * T)) / 3) ^ 2) := by
  rw [tiltGramian_value, Matrix.det_smul]
  have hdet : (Matrix.of
      ![![(1 - Real.exp (-2 * T)) / 2, ε * ((1 - Real.exp (-3 * T)) / 3)],
        ![ε * ((1 - Real.exp (-3 * T)) / 3),
          ε ^ 2 * ((1 - Real.exp (-4 * T)) / 4)]]).det
      = (1 - Real.exp (-2 * T)) / 2 * (ε ^ 2 * ((1 - Real.exp (-4 * T)) / 4))
        - (ε * ((1 - Real.exp (-3 * T)) / 3)) ^ 2 := by
    rw [Matrix.det_fin_two_of]
    ring
  have hne : (1:ℝ) + ε ^ 2 ≠ 0 := by positivity
  rw [hdet]
  simp only [Fintype.card_fin]
  field_simp

/-- The bottom of the Rayleigh spectrum of a real `2×2` matrix (the
smallest eigenvalue, in Rayleigh-quotient variational form). -/
noncomputable def rayleighMin (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x : Fin 2 → ℝ, x ⬝ᵥ x ≠ 0 ∧
    r = (x ⬝ᵥ (A *ᵥ x)) / (x ⬝ᵥ x)}

/-- Real self dot-products are nonnegative. -/
theorem dot_self_nonneg (x : Fin 2 → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- The quadratic form of the tilted Gramian in closed form. -/
theorem tiltGramian_form (ε T : ℝ) (x : Fin 2 → ℝ) :
    x ⬝ᵥ (tiltGramian ε T *ᵥ x)
      = (1 + ε ^ 2)⁻¹
        * (x 0 ^ 2 * ((1 - Real.exp (-2 * T)) / 2)
          + 2 * ε * x 0 * x 1 * ((1 - Real.exp (-3 * T)) / 3)
          + ε ^ 2 * x 1 ^ 2 * ((1 - Real.exp (-4 * T)) / 4)) := by
  rw [tiltGramian_value]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply]
  ring

/-- The quadratic form is a square-window integral, hence nonnegative. -/
theorem tiltGramian_form_nonneg (ε T : ℝ) (hT : 0 ≤ T) (x : Fin 2 → ℝ) :
    0 ≤ x ⬝ᵥ (tiltGramian ε T *ᵥ x) := by
  obtain ⟨hI2, hI3, hI4⟩ := clock_window_integrals T
  have hne : (0 : ℝ) < 1 + ε ^ 2 := by positivity
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun t => Real.exp (a * t) * Real.exp (b * t))
      MeasureTheory.volume 0 T := fun a b =>
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hker : (∫ t in (0 : ℝ)..T,
      (x 0 * Real.exp (-t) + ε * x 1 * Real.exp (-2 * t)) ^ 2)
      = x 0 ^ 2 * ((1 - Real.exp (-2 * T)) / 2)
        + 2 * ε * x 0 * x 1 * ((1 - Real.exp (-3 * T)) / 3)
        + ε ^ 2 * x 1 ^ 2 * ((1 - Real.exp (-4 * T)) / 4) := by
    have hpt : ∀ t : ℝ,
        (x 0 * Real.exp (-t) + ε * x 1 * Real.exp (-2 * t)) ^ 2
        = x 0 ^ 2 * (Real.exp (-t) * Real.exp (-t))
          + (2 * ε * x 0 * x 1) * (Real.exp (-t) * Real.exp (-2 * t))
          + (ε ^ 2 * x 1 ^ 2) * (Real.exp (-2 * t) * Real.exp (-2 * t)) := by
      intro t
      ring
    have hi1 : IntervalIntegrable
        (fun t => x 0 ^ 2 * (Real.exp (-t) * Real.exp (-t)))
        MeasureTheory.volume 0 T := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hi2 : IntervalIntegrable
        (fun t => (2 * ε * x 0 * x 1) * (Real.exp (-t) * Real.exp (-2 * t)))
        MeasureTheory.volume 0 T := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hi3 : IntervalIntegrable
        (fun t => (ε ^ 2 * x 1 ^ 2)
          * (Real.exp (-2 * t) * Real.exp (-2 * t)))
        MeasureTheory.volume 0 T := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_congr fun t _ => hpt t,
      intervalIntegral.integral_add (hi1.add hi2) hi3,
      intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hI2, hI3, hI4]
  rw [tiltGramian_form, ← hker]
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..T,
      (x 0 * Real.exp (-t) + ε * x 1 * Real.exp (-2 * t)) ^ 2 := by
    apply intervalIntegral.integral_nonneg hT
    intro t _
    positivity
  positivity

/-- The Rayleigh witness pinching the bottom of the spectrum. -/
theorem tiltGramian_rayleigh_witness (ε T : ℝ) :
    ∃ x : Fin 2 → ℝ, x ⬝ᵥ x ≠ 0 ∧
      (x ⬝ᵥ (tiltGramian ε T *ᵥ x)) / (x ⬝ᵥ x)
        = ε ^ 2 / (1 + ε ^ 2) ^ 2
          * ((1 - Real.exp (-2 * T)) / 2
            - 2 * ((1 - Real.exp (-3 * T)) / 3)
            + (1 - Real.exp (-4 * T)) / 4) := by
  have hpos : (0 : ℝ) < 1 + ε ^ 2 := by positivity
  have hdot : (![-ε, (1:ℝ)] : Fin 2 → ℝ) ⬝ᵥ ![-ε, (1:ℝ)] = 1 + ε ^ 2 := by
    simp [dotProduct, Fin.sum_univ_two]
    ring
  refine ⟨![-ε, 1], ?_, ?_⟩
  · rw [hdot]
    exact hpos.ne'
  · rw [tiltGramian_form, hdot]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring

/-- **Mechanism (iii): normalized cyclic-geometry collapse.**  Along
`ε_n ↓ 0`: the entrance reserve is stable, every finite tilted source is
clock-cyclic, the Gramian determinant takes the displayed value, and the
smallest normalized-Gramian eigenvalue collapses to zero, while the
limiting source `e₁` loses `e₂` from its cyclic space. -/
theorem cyclic_geometry_collapse (T : ℝ) (hT : 0 < T) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (nhds 0)) :
    (∀ n, tiltB (ε n) ⬝ᵥ tiltB (ε n) = 1 + (ε n) ^ 2) ∧
      (∀ n, Submodule.span ℝ {v | ∃ t : ℝ, 0 ≤ t ∧
        v = NormedSpace.exp ((-t) • diagH) *ᵥ tiltB (ε n)} = ⊤) ∧
      (∀ n, (tiltGramian (ε n) T).det
        = (ε n) ^ 2 / (1 + (ε n) ^ 2) ^ 2
          * ((1 - Real.exp (-2 * T)) / 2 * ((1 - Real.exp (-4 * T)) / 4)
            - ((1 - Real.exp (-3 * T)) / 3) ^ 2)) ∧
      Tendsto (fun n => rayleighMin (tiltGramian (ε n) T)) atTop (nhds 0) ∧
      (![0, 1] : Fin 2 → ℝ) ∉ Submodule.span ℝ {v | ∃ t : ℝ, 0 ≤ t ∧
        v = NormedSpace.exp ((-t) • diagH) *ᵥ (![1, 0] : Fin 2 → ℝ)} := by
  have horbit : ∀ (b : Fin 2 → ℝ) (t : ℝ),
      NormedSpace.exp ((-t) • diagH) *ᵥ b
      = ![Real.exp (-t) * b 0, Real.exp (-2 * t) * b 1] := by
    intro b t
    rw [diagH_clock]
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
  refine ⟨fun n => tilt_reserve (ε n), fun n => ?_,
    fun n => tiltGramian_det _ T, ?_, ?_⟩
  · -- cyclicity of each tilted source
    have hεn := hε n
    have hεn0 : (ε n) ≠ 0 := hεn.ne'
    set Sp := Submodule.span ℝ {v | ∃ t : ℝ, 0 ≤ t ∧
        v = NormedSpace.exp ((-t) • diagH) *ᵥ tiltB (ε n)} with hSp
    have hmem : ∀ t : ℝ, 0 ≤ t →
        NormedSpace.exp ((-t) • diagH) *ᵥ tiltB (ε n) ∈ Sp :=
      fun t ht => Submodule.subset_span ⟨t, ht, rfl⟩
    have h0 : (![1, ε n] : Fin 2 → ℝ) ∈ Sp := by
      have h := hmem 0 le_rfl
      rw [horbit (tiltB (ε n)) 0] at h
      have hz : (![Real.exp (-0) * tiltB (ε n) 0,
          Real.exp (-2 * 0) * tiltB (ε n) 1] : Fin 2 → ℝ)
          = ![1, ε n] := by
        funext i
        fin_cases i <;> norm_num [tiltB]
      rwa [hz] at h
    have hv1 : (![(1:ℝ) / 2, ε n / 4] : Fin 2 → ℝ) ∈ Sp := by
      have h := hmem (Real.log 2) (Real.log_nonneg (by norm_num))
      rw [horbit (tiltB (ε n)) (Real.log 2)] at h
      have hexp2 : Real.exp (-Real.log 2) = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
      have hexp4 : Real.exp (-2 * Real.log 2) = 1 / 4 := by
        have harg : (-2 : ℝ) * Real.log 2 = -(Real.log 2 + Real.log 2) := by
          ring
        rw [harg, Real.exp_neg, Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
      have hz : (![Real.exp (-Real.log 2) * tiltB (ε n) 0,
          Real.exp (-2 * Real.log 2) * tiltB (ε n) 1] : Fin 2 → ℝ)
          = ![(1:ℝ) / 2, ε n / 4] := by
        funext i
        fin_cases i <;>
          · try rw [hexp2]
            try rw [hexp4]
            try simp [tiltB]
            try ring
      rwa [hz] at h
    have he1 : (![1, 0] : Fin 2 → ℝ) ∈ Sp := by
      have hcomb : (![1, 0] : Fin 2 → ℝ)
          = (4:ℝ) • (![(1:ℝ) / 2, ε n / 4] : Fin 2 → ℝ)
            + (-(1:ℝ)) • (![1, ε n] : Fin 2 → ℝ) := by
        funext i
        fin_cases i <;> · norm_num; try ring
      rw [hcomb]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hv1)
        (Submodule.smul_mem _ _ h0)
    have he2 : (![0, 1] : Fin 2 → ℝ) ∈ Sp := by
      have hcomb : (![0, 1] : Fin 2 → ℝ)
          = (ε n)⁻¹ • ((![1, ε n] : Fin 2 → ℝ)
            - (![1, 0] : Fin 2 → ℝ)) := by
        funext i
        fin_cases i <;>
          · simp
            try field_simp
      rw [hcomb]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h0 he1)
    rw [eq_top_iff]
    intro x _
    have hx : x = x 0 • (![1, 0] : Fin 2 → ℝ)
        + x 1 • (![0, 1] : Fin 2 → ℝ) := by
      funext i
      fin_cases i <;> simp
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ he1)
      (Submodule.smul_mem _ _ he2)
  · -- collapse of the smallest eigenvalue
    have hJnn : 0 ≤ (1 - Real.exp (-2 * T)) / 2
        - 2 * ((1 - Real.exp (-3 * T)) / 3) + (1 - Real.exp (-4 * T)) / 4 := by
      obtain ⟨hI2, hI3, hI4⟩ := clock_window_integrals T
      have hker : (∫ t in (0 : ℝ)..T,
          (Real.exp (-t) - Real.exp (-2 * t)) ^ 2)
          = (1 - Real.exp (-2 * T)) / 2
            - 2 * ((1 - Real.exp (-3 * T)) / 3)
            + (1 - Real.exp (-4 * T)) / 4 := by
        have hpt : ∀ t : ℝ, (Real.exp (-t) - Real.exp (-2 * t)) ^ 2
            = Real.exp (-t) * Real.exp (-t)
              - 2 * (Real.exp (-t) * Real.exp (-2 * t))
              + Real.exp (-2 * t) * Real.exp (-2 * t) := by
          intro t
          ring
        have hi1 : IntervalIntegrable
            (fun t => Real.exp (-t) * Real.exp (-t))
            MeasureTheory.volume 0 T :=
          Continuous.intervalIntegrable (by fun_prop) _ _
        have hi2 : IntervalIntegrable
            (fun t => 2 * (Real.exp (-t) * Real.exp (-2 * t)))
            MeasureTheory.volume 0 T :=
          Continuous.intervalIntegrable (by fun_prop) _ _
        have hi3 : IntervalIntegrable
            (fun t => Real.exp (-2 * t) * Real.exp (-2 * t))
            MeasureTheory.volume 0 T :=
          Continuous.intervalIntegrable (by fun_prop) _ _
        rw [intervalIntegral.integral_congr fun t _ => hpt t,
          intervalIntegral.integral_add (hi1.sub hi2) hi3,
          intervalIntegral.integral_sub hi1 hi2,
          intervalIntegral.integral_const_mul, hI2, hI3, hI4]
      rw [← hker]
      apply intervalIntegral.integral_nonneg hT.le
      intro t _
      positivity
    have hlow : ∀ n, 0 ≤ rayleighMin (tiltGramian (ε n) T) := by
      intro n
      apply le_csInf
      · obtain ⟨x, hx1, hx2⟩ := tiltGramian_rayleigh_witness (ε n) T
        exact ⟨_, x, hx1, hx2.symm⟩
      · rintro r ⟨x, _, rfl⟩
        exact div_nonneg (tiltGramian_form_nonneg (ε n) T hT.le x)
          (dot_self_nonneg x)
    have hup : ∀ n, rayleighMin (tiltGramian (ε n) T)
        ≤ (ε n) ^ 2 * ((1 - Real.exp (-2 * T)) / 2
          - 2 * ((1 - Real.exp (-3 * T)) / 3)
          + (1 - Real.exp (-4 * T)) / 4) := by
      intro n
      obtain ⟨x, hx1, hx2⟩ := tiltGramian_rayleigh_witness (ε n) T
      have hbdd : BddBelow {r : ℝ | ∃ x : Fin 2 → ℝ, x ⬝ᵥ x ≠ 0 ∧
          r = (x ⬝ᵥ (tiltGramian (ε n) T *ᵥ x)) / (x ⬝ᵥ x)} := by
        refine ⟨0, ?_⟩
        rintro r ⟨y, _, rfl⟩
        exact div_nonneg (tiltGramian_form_nonneg (ε n) T hT.le y)
          (dot_self_nonneg y)
      have hmem : (x ⬝ᵥ (tiltGramian (ε n) T *ᵥ x)) / (x ⬝ᵥ x)
          ∈ {r : ℝ | ∃ x : Fin 2 → ℝ, x ⬝ᵥ x ≠ 0 ∧
              r = (x ⬝ᵥ (tiltGramian (ε n) T *ᵥ x)) / (x ⬝ᵥ x)} :=
        ⟨x, hx1, rfl⟩
      refine (csInf_le hbdd hmem).trans ?_
      rw [hx2]
      have hfrac : (ε n) ^ 2 / (1 + (ε n) ^ 2) ^ 2 ≤ (ε n) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (ε n), sq_nonneg ((ε n) ^ 2)]
      exact mul_le_mul_of_nonneg_right hfrac hJnn
    have hto : Tendsto (fun n => (ε n) ^ 2
        * ((1 - Real.exp (-2 * T)) / 2 - 2 * ((1 - Real.exp (-3 * T)) / 3)
          + (1 - Real.exp (-4 * T)) / 4)) atTop (nhds 0) := by
      have h2 : Tendsto (fun n => (ε n) ^ 2) atTop (nhds 0) := by
        have := hlim.pow 2
        simpa using this
      have := h2.mul_const ((1 - Real.exp (-2 * T)) / 2
        - 2 * ((1 - Real.exp (-3 * T)) / 3) + (1 - Real.exp (-4 * T)) / 4)
      simpa using this
    exact squeeze_zero hlow hup hto
  · -- the limiting source loses `e₂`
    intro hmem
    have hsub : Submodule.span ℝ {v : Fin 2 → ℝ | ∃ t : ℝ, 0 ≤ t ∧
        v = NormedSpace.exp ((-t) • diagH) *ᵥ (![1, 0] : Fin 2 → ℝ)}
        ≤ LinearMap.ker
          (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) := by
      rw [Submodule.span_le]
      rintro v ⟨t, _, rfl⟩
      rw [horbit ![1, 0] t]
      simp [LinearMap.mem_ker]
    have hcontra := hsub hmem
    simp [LinearMap.mem_ker] at hcontra

end Leverage

end LeverageCollapse

/-! ### Variational covariance and polar reserve factorization

Record `thm:GT-source-action-covariance` (SMET.5–SMET.10).

Rendering: a null-cost-consistent source-action packet is a finite source
synthesis `B : E → ℋ` together with a PSD action form `M` with
`Ker M ⊆ Ker B`; `M†`, `M^{†/2}`, `G^{†/2}`, `G^{1/2}` and the support
projections are the spectral-calculus operators of the repo's
`spectralFunction` machinery.  SMET.5 is an attained `IsGreatest`;
SMET.6 is proved through the variational characterization (no
Moore–Penrose coordinate formula), with the invertible reparametrization
`S : E ≃ E`; SMET.7–SMET.9 are exact operator identities; the equal
nonzero spectrum is rendered as the two-sided nonzero-eigenvalue
transport; SMET.10 is the two-sided Loewner window with
`g₋ = λ⁺_min(G)` (`posFloor`) and `g₊ = λ_max(G)` (`hermLamMax`, which
equals `‖G‖` for the PSD supported Gram). -/

section SourceActionCovariance

open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank

namespace SourceAction

variable {e h : Type*} [Fintype e] [DecidableEq e] [Fintype h] [DecidableEq h]

/-- Null-cost consistency `Ker M ⊆ Ker B` (SMET.1). -/
def NullCost (B : Matrix h e ℂ) (M : Matrix e e ℂ) : Prop :=
  ∀ u : e → ℂ, M *ᵥ u = 0 → B *ᵥ u = 0

/-- Spectral functions of Hermitian matrices are Hermitian. -/
theorem spectralFunction_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℂ} (hS : S.IsHermitian) (f : ℝ → ℝ) :
    (spectralFunction hS f).IsHermitian := by
  have hsplit : spectralFunction hS f
      = spectralFunction hS (fun l => max (f l) 0)
        - spectralFunction hS (fun l => max (-f l) 0) := by
    rw [← spectralFunction_sub]
    refine spectralFunction_congr hS fun i => ?_
    rcases le_total (f (hS.eigenvalues i)) 0 with hl | hl
    · rw [max_eq_right hl, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left hl, max_eq_right (by linarith)]
      ring
  rw [hsplit]
  exact ((spectralFunction_posSemidef hS _ fun i => le_max_right _ _).1).sub
    ((spectralFunction_posSemidef hS _ fun i => le_max_right _ _).1)

/-- The Moore–Penrose inverse square root `M^{†/2}`. -/
noncomputable def pinvSqrtSA {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) : Matrix n n ℂ :=
  spectralFunction hM (fun l => if 0 < l then (Real.sqrt l)⁻¹ else 0)

/-- The unit-action source synthesis `B_M = B M^{†/2}` (SMET.2). -/
noncomputable def unitSource (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) : Matrix h e ℂ := B * pinvSqrtSA hM

/-- The unit-action covariance `Σ_{B,M} = B M† B^*` (SMET.2). -/
noncomputable def sigma (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) : Matrix h h ℂ := B * pinv hM * Bᴴ

/-- The supported Gram `G_{B,M} = B_M^* B_M` (SMET.3). -/
noncomputable def gram (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) : Matrix e e ℂ :=
  (unitSource B hM)ᴴ * unitSource B hM

/-- The polar factor `U_{B,M} = B_M G^{†/2}` (SMET.7). -/
noncomputable def polarU (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) : Matrix h e ℂ :=
  unitSource B hM * pinvSqrtSA (posSemidef_conjTranspose_mul_self
    (unitSource B hM)).1

/-- `M M† = supp M` (right pseudoinverse cancellation). -/
theorem mul_pinv_eq_supportProj {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    M * pinv hM = supportProj hM := by
  have hid := spectralFunction_id hM
  calc M * pinv hM
      = spectralFunction hM id
        * spectralFunction hM (fun l => if 0 < l then l⁻¹ else 0) := by
        unfold pinv
        rw [hid]
    _ = spectralFunction hM (fun l => id l * if 0 < l then l⁻¹ else 0) :=
        spectralFunction_mul hM _ _
    _ = supportProj hM := by
        unfold supportProj
        refine spectralFunction_congr hM fun i => ?_
        simp only [id]
        split_ifs with hl
        · field_simp
        · ring

/-- `supp M = M M†` in the reversed orientation. -/
theorem supportProj_eq_mul_pinv {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    supportProj hM = M * pinv hM := (mul_pinv_eq_supportProj hM).symm

/-- `M^{†/2} M^{†/2} = M†`. -/
theorem pinvSqrtSA_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    pinvSqrtSA hM * pinvSqrtSA hM = pinv hM := by
  unfold pinvSqrtSA pinv
  rw [spectralFunction_mul]
  refine spectralFunction_congr hM fun i => ?_
  split_ifs with hl
  · rw [← mul_inv, Real.mul_self_sqrt hl.le]
  · ring

/-- `M^{†/2}` is Hermitian. -/
theorem pinvSqrtSA_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (pinvSqrtSA hM).IsHermitian := spectralFunction_isHermitian hM _

/-- `M†` is Hermitian. -/
theorem pinv_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (pinv hM).IsHermitian := spectralFunction_isHermitian hM _

/-- `M†` is positive semidefinite. -/
theorem pinv_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (pinv hM).PosSemidef := by
  refine spectralFunction_posSemidef hM _ fun i => ?_
  split_ifs with hl
  · positivity
  · exact le_rfl

omit [Fintype h] [DecidableEq h] in
/-- The covariance in unit-action coordinates: `Σ = B_M B_M^*`
(SMET.2 consistency). -/
theorem sigma_eq_unitSource (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) :
    sigma B hM = unitSource B hM * (unitSource B hM)ᴴ := by
  unfold sigma unitSource
  rw [Matrix.conjTranspose_mul, (pinvSqrtSA_isHermitian hM).eq,
    ← pinvSqrtSA_mul_self hM]
  simp only [Matrix.mul_assoc]

omit [Fintype h] [DecidableEq h] in
/-- The covariance is positive semidefinite. -/
theorem sigma_posSemidef [Finite h] (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) : (sigma B hM).PosSemidef := by
  have := Fintype.ofFinite h
  rw [sigma_eq_unitSource]
  exact Matrix.posSemidef_self_mul_conjTranspose _

omit [Fintype h] [DecidableEq h] in
/-- Null-cost consistency in matrix form: `B supp M = B`. -/
theorem mul_supportProj_of_nullCost {B : Matrix h e ℂ} {M : Matrix e e ℂ}
    (hM : M.PosSemidef) (hnc : NullCost B M) :
    B * supportProj hM.1 = B := by
  have hcol : ∀ u : e → ℂ, (B * (1 - supportProj hM.1)) *ᵥ u = 0 := by
    intro u
    rw [← Matrix.mulVec_mulVec]
    apply hnc
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one,
      mul_supportProj hM, sub_self, Matrix.zero_mulVec]
  have hzero : B * (1 - supportProj hM.1) = 0 := by
    ext i j
    have h2 := congrFun (hcol (Pi.single j 1)) i
    simpa using h2
  have h3 : B - B * supportProj hM.1 = 0 := by
    calc B - B * supportProj hM.1 = B * (1 - supportProj hM.1) := by
          rw [Matrix.mul_sub, Matrix.mul_one]
      _ = 0 := hzero
  exact (sub_eq_zero.mp h3).symm

omit [Fintype h] [DecidableEq h] in
/-- The adjoint form of null-cost consistency: `supp M B^* = B^*`. -/
theorem supportProj_mul_conjTranspose_of_nullCost {B : Matrix h e ℂ}
    {M : Matrix e e ℂ} (hM : M.PosSemidef) (hnc : NullCost B M) :
    supportProj hM.1 * Bᴴ = Bᴴ := by
  have h := congrArg Matrix.conjTranspose (mul_supportProj_of_nullCost hM hnc)
  rwa [Matrix.conjTranspose_mul, (supportProj_posSemidef hM.1).1.eq] at h

omit [DecidableEq e] [DecidableEq h] in
/-- Adjoint transport of the pairing through a rectangular synthesis. -/
theorem star_dot_conjTranspose_mulVec (A : Matrix h e ℂ) (x : h → ℂ)
    (u : e → ℂ) :
    star u ⬝ᵥ (Aᴴ *ᵥ x) = star (star x ⬝ᵥ (A *ᵥ u)) := by
  rw [star_dotProduct, star_mulVec, Matrix.conjTranspose_conjTranspose,
    ← dotProduct_mulVec]

omit [DecidableEq e] in
/-- The congruence transport of a quadratic form. -/
theorem congruence_form (S M : Matrix e e ℂ) (u : e → ℂ) :
    star u ⬝ᵥ ((Sᴴ * M * S) *ᵥ u) = star (S *ᵥ u) ⬝ᵥ (M *ᵥ (S *ᵥ u)) := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
    ← star_mulVec, Matrix.mulVec_mulVec]

omit [DecidableEq h] in
/-- **SMET.5**: the attained variational characterization of the
unit-action covariance,
`⟨x, Σ x⟩ = sup_u {2 Re⟨x, Bu⟩ - ⟨u, Mu⟩}`. -/
theorem variational_covariance {B : Matrix h e ℂ} {M : Matrix e e ℂ}
    (hM : M.PosSemidef) (hnc : NullCost B M) (x : h → ℂ) :
    IsGreatest {r : ℝ | ∃ u : e → ℂ,
        r = 2 * (star x ⬝ᵥ (B *ᵥ u)).re - (star u ⬝ᵥ (M *ᵥ u)).re}
      ((star x ⬝ᵥ (sigma B hM.1 *ᵥ x)).re) := by
  have hsupp := supportProj_mul_conjTranspose_of_nullCost hM hnc
  set w : e → ℂ := pinv hM.1 *ᵥ (Bᴴ *ᵥ x) with hw
  have hMw : M *ᵥ w = Bᴴ *ᵥ x := by
    rw [hw, Matrix.mulVec_mulVec, mul_pinv_eq_supportProj hM.1,
      Matrix.mulVec_mulVec, hsupp]
  have hBw : B *ᵥ w = sigma B hM.1 *ᵥ x := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rfl
  have hσH : (sigma B hM.1).IsHermitian := (sigma_posSemidef B hM.1).1
  have hval : star w ⬝ᵥ (M *ᵥ w) = star x ⬝ᵥ (sigma B hM.1 *ᵥ x) := by
    rw [hMw, star_dot_conjTranspose_mulVec B x w, hBw,
      ← hermitian_form_conj_symm hσH x x]
  constructor
  · refine ⟨w, ?_⟩
    rw [hBw, hval]
    ring
  · rintro r ⟨u, rfl⟩
    have hexpand : star (u - w) ⬝ᵥ (M *ᵥ (u - w))
        = star u ⬝ᵥ (M *ᵥ u) - star u ⬝ᵥ (M *ᵥ w)
          - star w ⬝ᵥ (M *ᵥ u) + star w ⬝ᵥ (M *ᵥ w) := by
      rw [Matrix.mulVec_sub, star_sub, sub_dotProduct, dotProduct_sub,
        dotProduct_sub]
      ring
    have huw : (star u ⬝ᵥ (M *ᵥ w)).re = (star x ⬝ᵥ (B *ᵥ u)).re := by
      rw [hMw, star_dot_conjTranspose_mulVec B x u, Complex.star_def,
        Complex.conj_re]
    have hwu : (star w ⬝ᵥ (M *ᵥ u)).re = (star x ⬝ᵥ (B *ᵥ u)).re := by
      rw [hermitian_form_conj_symm hM.1 w u, Complex.star_def,
        Complex.conj_re, huw]
    have hnn := re_form_nonneg hM (u - w)
    have hre := congrArg Complex.re hexpand
    rw [Complex.add_re, Complex.sub_re, Complex.sub_re, huw, hwu] at hre
    have hvre := congrArg Complex.re hval
    linarith

omit [Fintype h] [DecidableEq h] in
/-- **SMET.6**: the covariance depends only on the metric-quotient source
map: invariance under invertible coordinate change `B̃ = BS`,
`M̃ = S^* M S`. -/
theorem covariance_coordinate_invariance [Finite h] {B : Matrix h e ℂ}
    {M : Matrix e e ℂ} (hM : M.PosSemidef) (hnc : NullCost B M)
    (S : Matrix e e ℂ) (hS : IsUnit S) :
    ∀ (hMt : (Sᴴ * M * S).PosSemidef), sigma (B * S) hMt.1 = sigma B hM.1 := by
  intro hMt
  have := Fintype.ofFinite h
  have hnct : NullCost (B * S) (Sᴴ * M * S) := by
    intro u hu
    have hform : star (S *ᵥ u) ⬝ᵥ (M *ᵥ (S *ᵥ u)) = 0 := by
      rw [← congruence_form S M u, hu, dotProduct_zero]
    have hMSu : M *ᵥ (S *ᵥ u) = 0 := by
      have hray := (rayleigh_eq_zero_iff hM (S *ᵥ u)).mp
      apply hray
      unfold GeometricThresholdBank.rayleigh
      rw [hform]
      simp
    rw [← Matrix.mulVec_mulVec]
    exact hnc _ hMSu
  obtain ⟨Su, hSu⟩ := hS
  have hσtH : (sigma (B * S) hMt.1).IsHermitian := (sigma_posSemidef _ _).1
  have hσH : (sigma B hM.1).IsHermitian := (sigma_posSemidef _ _).1
  refine hermitian_eq_of_re_forms hσtH hσH fun x => ?_
  have h1 := variational_covariance hMt hnct x
  have h2 := variational_covariance hM hnc x
  have hsets : {r : ℝ | ∃ u : e → ℂ,
      r = 2 * (star x ⬝ᵥ ((B * S) *ᵥ u)).re
        - (star u ⬝ᵥ ((Sᴴ * M * S) *ᵥ u)).re}
      = {r : ℝ | ∃ u : e → ℂ,
        r = 2 * (star x ⬝ᵥ (B *ᵥ u)).re - (star u ⬝ᵥ (M *ᵥ u)).re} := by
    ext r
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨S *ᵥ u, ?_⟩
      rw [← Matrix.mulVec_mulVec, congruence_form]
    · rintro ⟨v, rfl⟩
      refine ⟨(↑Su⁻¹ : Matrix e e ℂ) *ᵥ v, ?_⟩
      have hSv : S *ᵥ ((↑Su⁻¹ : Matrix e e ℂ) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, ← hSu, Units.mul_inv, Matrix.one_mulVec]
      rw [← Matrix.mulVec_mulVec, congruence_form, hSv]
  rw [hsets] at h1
  exact h1.unique h2

omit [DecidableEq e] [Fintype h] [DecidableEq h] in
/-- Matrices agreeing on all vectors are equal. -/
theorem matrix_eq_zero_of_mulVec_eq_zero {A : Matrix h e ℂ}
    (hA : ∀ v : e → ℂ, A *ᵥ v = 0) : A = 0 := by
  classical
  ext i j
  have h2 := congrFun (hA (Pi.single j 1)) i
  simpa using h2

omit [DecidableEq e] [DecidableEq h] in
/-- A vector killed by `A A^*` is killed by `A^*`. -/
theorem conjTranspose_mulVec_eq_zero {A : Matrix h e ℂ} {v : h → ℂ}
    (hv : (A * Aᴴ) *ᵥ v = 0) : Aᴴ *ᵥ v = 0 := by
  have hdot : star (Aᴴ *ᵥ v) ⬝ᵥ (Aᴴ *ᵥ v) = 0 := by
    rw [star_mulVec, Matrix.conjTranspose_conjTranspose, ← dotProduct_mulVec,
      Matrix.mulVec_mulVec, hv, dotProduct_zero]
  exact dotProduct_star_self_eq_zero.mp hdot

/-- `G^{†/2} G G^{†/2} = supp G`: the whitening identity. -/
theorem pinvSqrt_conj_eq_supportProj {n : Type*} [Fintype n] [DecidableEq n]
    {G : Matrix n n ℂ} (hG : G.PosSemidef) :
    pinvSqrtSA hG.1 * G * pinvSqrtSA hG.1 = supportProj hG.1 := by
  have hid := spectralFunction_id hG.1
  calc pinvSqrtSA hG.1 * G * pinvSqrtSA hG.1
      = spectralFunction hG.1 (fun l => if 0 < l then (Real.sqrt l)⁻¹ else 0)
        * spectralFunction hG.1 id
        * spectralFunction hG.1
          (fun l => if 0 < l then (Real.sqrt l)⁻¹ else 0) := by
        unfold pinvSqrtSA
        rw [hid]
    _ = spectralFunction hG.1 (fun l =>
          ((if 0 < l then (Real.sqrt l)⁻¹ else 0) * id l)
            * if 0 < l then (Real.sqrt l)⁻¹ else 0) := by
        rw [spectralFunction_mul, spectralFunction_mul]
    _ = supportProj hG.1 := by
        unfold supportProj
        refine spectralFunction_congr hG.1 fun i => ?_
        simp only [id]
        split_ifs with hl
        · have hs : Real.sqrt (hG.1.eigenvalues i)
              * Real.sqrt (hG.1.eigenvalues i) = hG.1.eigenvalues i :=
            Real.mul_self_sqrt hl.le
          have hsne : Real.sqrt (hG.1.eigenvalues i) ≠ 0 :=
            (Real.sqrt_pos.mpr hl).ne'
          field_simp
          linarith [hs]
        · ring

/-- `G^{†/2} G^{1/2} = supp G`. -/
theorem pinvSqrt_mul_psdSqrt {n : Type*} [Fintype n] [DecidableEq n]
    {G : Matrix n n ℂ} (hG : G.PosSemidef) :
    pinvSqrtSA hG.1 * psdSqrt hG.1 = supportProj hG.1 := by
  unfold pinvSqrtSA psdSqrt supportProj
  rw [spectralFunction_mul]
  refine spectralFunction_congr hG.1 fun i => ?_
  split_ifs with hl
  · exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hl).ne'
  · ring

omit [DecidableEq h] in
/-- The unit source is fixed by the support of its Gram. -/
theorem unitSource_mul_suppGram (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) :
    unitSource B hM * supportProj
      (posSemidef_conjTranspose_mul_self (unitSource B hM)).1
      = unitSource B hM := by
  set BM := unitSource B hM with hBM
  set hG := posSemidef_conjTranspose_mul_self BM with hhG
  set sG := supportProj hG.1 with hsG'
  have hGs' : BMᴴ * (BM * sG) = BMᴴ * BM := by
    rw [← Matrix.mul_assoc]
    exact mul_supportProj hG
  have hsG : sG * (BMᴴ * BM) = BMᴴ * BM := by
    have h := congrArg Matrix.conjTranspose (mul_supportProj hG)
    rwa [Matrix.conjTranspose_mul, (supportProj_posSemidef hG.1).1.eq,
      hG.1.eq] at h
  have hD : (BM - BM * sG)ᴴ * (BM - BM * sG) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      (supportProj_posSemidef hG.1).1.eq]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    rw [hGs', hsG]
    abel
  have hzero := Matrix.conjTranspose_mul_self_eq_zero.mp hD
  have := sub_eq_zero.mp hzero
  exact this.symm

omit [DecidableEq h] in
/-- **SMET.7–SMET.8 (initial projection)**: `U^* U = supp G`, and
`supp G` is an orthogonal projection, so `U` is a partial isometry. -/
theorem polar_partial_isometry (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) :
    (polarU B hM)ᴴ * polarU B hM
        = supportProj (posSemidef_conjTranspose_mul_self (unitSource B hM)).1
      ∧ supportProj (posSemidef_conjTranspose_mul_self (unitSource B hM)).1
          * supportProj (posSemidef_conjTranspose_mul_self (unitSource B hM)).1
        = supportProj (posSemidef_conjTranspose_mul_self (unitSource B hM)).1
      ∧ (supportProj
          (posSemidef_conjTranspose_mul_self (unitSource B hM)).1).IsHermitian := by
  set BM := unitSource B hM with hBM
  set hG := posSemidef_conjTranspose_mul_self BM with hhG
  refine ⟨?_, supportProj_idem hG.1, (supportProj_posSemidef hG.1).1⟩
  unfold polarU
  rw [Matrix.conjTranspose_mul, (pinvSqrtSA_isHermitian hG.1).eq]
  calc pinvSqrtSA hG.1 * (unitSource B hM)ᴴ
        * (unitSource B hM * pinvSqrtSA hG.1)
      = pinvSqrtSA hG.1 * ((unitSource B hM)ᴴ * unitSource B hM)
        * pinvSqrtSA hG.1 := by
        simp only [Matrix.mul_assoc]
    _ = supportProj hG.1 := pinvSqrt_conj_eq_supportProj hG

omit [DecidableEq h] in
/-- The polar range identity `U U^* = B_M G† B_M^*`. -/
theorem polarU_mul_conjTranspose (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) :
    polarU B hM * (polarU B hM)ᴴ
      = unitSource B hM
        * pinv (posSemidef_conjTranspose_mul_self (unitSource B hM)).1
        * (unitSource B hM)ᴴ := by
  set hG := posSemidef_conjTranspose_mul_self (unitSource B hM) with hhG
  unfold polarU
  rw [Matrix.conjTranspose_mul, (pinvSqrtSA_isHermitian hG.1).eq]
  calc unitSource B hM * pinvSqrtSA hG.1
        * (pinvSqrtSA hG.1 * (unitSource B hM)ᴴ)
      = unitSource B hM * (pinvSqrtSA hG.1 * pinvSqrtSA hG.1)
        * (unitSource B hM)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = unitSource B hM * pinv hG.1 * (unitSource B hM)ᴴ := by
        rw [pinvSqrtSA_mul_self]

/-- **SMET.8 (final projection)**: `U U^* = P_B = supp Σ`. -/
theorem polar_range_projection (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) :
    polarU B hM * (polarU B hM)ᴴ
      = supportProj (sigma_posSemidef B hM).1 := by
  classical
  set BM := unitSource B hM with hBM
  set hG := posSemidef_conjTranspose_mul_self BM with hhG
  set hSg := sigma_posSemidef B hM with hhSg
  set R := BM * pinv hG.1 * BMᴴ with hR
  have hRdef : polarU B hM * (polarU B hM)ᴴ = R :=
    polarU_mul_conjTranspose B hM
  have hSgBM : sigma B hM = BM * BMᴴ := sigma_eq_unitSource B hM
  -- `R` fixes the range of `Σ`
  have hRSg : R * sigma B hM = sigma B hM := by
    rw [hSgBM, hR]
    calc BM * pinv hG.1 * BMᴴ * (BM * BMᴴ)
        = BM * (pinv hG.1 * (BMᴴ * (BM * BMᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = BM * (pinv hG.1 * ((BMᴴ * BM) * BMᴴ)) := by
          rw [← Matrix.mul_assoc BMᴴ BM BMᴴ]
      _ = BM * ((pinv hG.1 * (BMᴴ * BM)) * BMᴴ) := by
          rw [← Matrix.mul_assoc (pinv hG.1) (BMᴴ * BM) BMᴴ]
      _ = BM * (supportProj hG.1 * BMᴴ) := by
          have hps : pinv hG.1 * (BMᴴ * BM) = supportProj hG.1 :=
            (supportProj_eq_pinv_mul hG.1).symm
          rw [hps]
      _ = (BM * supportProj hG.1) * BMᴴ := by rw [Matrix.mul_assoc]
      _ = BM * BMᴴ := by rw [unitSource_mul_suppGram B hM]
  -- `R` fixes the support projection of `Σ`
  have hRsupp : R * supportProj hSg.1 = supportProj hSg.1 := by
    rw [supportProj_eq_mul_pinv hSg.1, ← Matrix.mul_assoc, hRSg]
  -- `R` kills the kernel of `Σ`
  have hRkill : R * (1 - supportProj hSg.1) = 0 := by
    apply matrix_eq_zero_of_mulVec_eq_zero
    intro v
    rw [← Matrix.mulVec_mulVec]
    set y := (1 - supportProj hSg.1) *ᵥ v with hy
    have hSgy : (BM * BMᴴ) *ᵥ y = 0 := by
      rw [hy, Matrix.mulVec_mulVec, ← hSgBM, Matrix.mul_sub, Matrix.mul_one,
        mul_supportProj hSg, sub_self, Matrix.zero_mulVec]
    have hBMy : BMᴴ *ᵥ y = 0 := conjTranspose_mulVec_eq_zero hSgy
    rw [hR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBMy,
      Matrix.mulVec_zero, Matrix.mulVec_zero]
  rw [hRdef]
  calc R = R * 1 := (Matrix.mul_one R).symm
    _ = R * (supportProj hSg.1 + (1 - supportProj hSg.1)) := by
        congr 1
        abel
    _ = R * supportProj hSg.1 + R * (1 - supportProj hSg.1) := by
        rw [Matrix.mul_add]
    _ = supportProj hSg.1 := by rw [hRsupp, hRkill, add_zero]

omit [DecidableEq h] in
/-- **SMET.9**: the polar factorization `B_M = U G^{1/2}` and
`Σ = U G U^*`. -/
theorem polar_factorization (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) :
    unitSource B hM = polarU B hM
        * psdSqrt (posSemidef_conjTranspose_mul_self (unitSource B hM)).1
      ∧ sigma B hM = polarU B hM * gram B hM * (polarU B hM)ᴴ := by
  set hG := posSemidef_conjTranspose_mul_self (unitSource B hM) with hhG
  constructor
  · unfold polarU
    rw [Matrix.mul_assoc, pinvSqrt_mul_psdSqrt hG,
      unitSource_mul_suppGram B hM]
  · have hkey : sigma B hM
        = polarU B hM * ((unitSource B hM)ᴴ * unitSource B hM)
          * (polarU B hM)ᴴ := by
      calc sigma B hM = unitSource B hM * (unitSource B hM)ᴴ :=
            sigma_eq_unitSource B hM
        _ = unitSource B hM * supportProj hG.1 * (unitSource B hM)ᴴ := by
            rw [unitSource_mul_suppGram B hM]
        _ = unitSource B hM * (pinvSqrtSA hG.1
              * ((unitSource B hM)ᴴ * unitSource B hM) * pinvSqrtSA hG.1)
              * (unitSource B hM)ᴴ := by
            rw [pinvSqrt_conj_eq_supportProj hG]
        _ = polarU B hM * ((unitSource B hM)ᴴ * unitSource B hM)
              * (polarU B hM)ᴴ := by
            unfold polarU
            rw [Matrix.conjTranspose_mul, (pinvSqrtSA_isHermitian hG.1).eq]
            simp only [Matrix.mul_assoc]
    exact hkey

omit [DecidableEq h] in
/-- **SMET.10 (spectral transport)**: `G` and `Σ` have the same nonzero
eigenvalues. -/
theorem same_nonzero_spectrum (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) (μ : ℂ) (hμ : μ ≠ 0) :
    (∃ v : e → ℂ, v ≠ 0 ∧ gram B hM *ᵥ v = μ • v)
      ↔ ∃ w : h → ℂ, w ≠ 0 ∧ sigma B hM *ᵥ w = μ • w := by
  set BM := unitSource B hM with hBM
  have hSgBM : sigma B hM = BM * BMᴴ := sigma_eq_unitSource B hM
  have hgram : gram B hM = BMᴴ * BM := rfl
  constructor
  · rintro ⟨v, hv0, hv⟩
    rw [hgram] at hv
    refine ⟨BM *ᵥ v, ?_, ?_⟩
    · intro hz
      have hGv : (BMᴴ * BM) *ᵥ v = 0 := by
        rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
      rw [hv] at hGv
      exact hv0 ((smul_eq_zero.mp hGv).resolve_left hμ)
    · rw [hSgBM, Matrix.mulVec_mulVec]
      calc (BM * BMᴴ * BM) *ᵥ v = BM *ᵥ ((BMᴴ * BM) *ᵥ v) := by
            rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = μ • (BM *ᵥ v) := by rw [hv, Matrix.mulVec_smul]
  · rintro ⟨w, hw0, hw⟩
    rw [hSgBM] at hw
    refine ⟨BMᴴ *ᵥ w, ?_, ?_⟩
    · intro hz
      have hSgw : (BM * BMᴴ) *ᵥ w = 0 := by
        rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
      rw [hw] at hSgw
      exact hw0 ((smul_eq_zero.mp hSgw).resolve_left hμ)
    · rw [hgram, Matrix.mulVec_mulVec]
      calc (BMᴴ * BM * BMᴴ) *ᵥ w = BMᴴ *ᵥ ((BM * BMᴴ) *ᵥ w) := by
            rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = μ • (BMᴴ *ᵥ w) := by rw [hw, Matrix.mulVec_smul]

/-- The transport of the support of `G` through the polar factor. -/
theorem polarU_suppGram_conj (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) :
    polarU B hM
        * supportProj (posSemidef_conjTranspose_mul_self (unitSource B hM)).1
        * (polarU B hM)ᴴ
      = supportProj (sigma_posSemidef B hM).1 := by
  set hG := posSemidef_conjTranspose_mul_self (unitSource B hM) with hhG
  obtain ⟨hUU, _, _⟩ := polar_partial_isometry B hM
  calc polarU B hM * supportProj hG.1 * (polarU B hM)ᴴ
      = polarU B hM * ((polarU B hM)ᴴ * polarU B hM) * (polarU B hM)ᴴ := by
        rw [hUU]
    _ = (polarU B hM * (polarU B hM)ᴴ)
          * (polarU B hM * (polarU B hM)ᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = supportProj (sigma_posSemidef B hM).1 := by
        rw [polar_range_projection B hM]
        exact supportProj_idem (sigma_posSemidef B hM).1

/-- **SMET.10 (reserve window)**: `g₋ P_B ⪯ Σ ⪯ g₊ P_B` with
`g₋ = λ⁺_min(G)` and `g₊ = λ_max(G)`. -/
theorem reserve_window [Nonempty e] (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) :
    (sigma B hM
        - ((posFloor (posSemidef_conjTranspose_mul_self (unitSource B hM)).1
            : ℝ) : ℂ) • supportProj (sigma_posSemidef B hM).1).PosSemidef
      ∧ (((hermLamMax
            (posSemidef_conjTranspose_mul_self (unitSource B hM)).1 : ℝ) : ℂ)
          • supportProj (sigma_posSemidef B hM).1 - sigma B hM).PosSemidef := by
  classical
  set hG := posSemidef_conjTranspose_mul_self (unitSource B hM) with hhG
  have hUGU : polarU B hM
      * ((unitSource B hM)ᴴ * unitSource B hM) * (polarU B hM)ᴴ
      = sigma B hM := (polar_factorization B hM).2.symm
  have hUsupp : polarU B hM * supportProj hG.1 * (polarU B hM)ᴴ
      = supportProj (sigma_posSemidef B hM).1 := polarU_suppGram_conj B hM
  have hGsupp' : ((unitSource B hM)ᴴ * unitSource B hM) * supportProj hG.1
      = (unitSource B hM)ᴴ * unitSource B hM := mul_supportProj hG
  have hsuppG' : supportProj hG.1 * ((unitSource B hM)ᴴ * unitSource B hM)
      = (unitSource B hM)ᴴ * unitSource B hM := by
    have hh := congrArg Matrix.conjTranspose hGsupp'
    rwa [Matrix.conjTranspose_mul, (supportProj_posSemidef hG.1).1.eq,
      hG.1.eq] at hh
  constructor
  · have hfloor := floor_posSemidef hG
    have hconj := hfloor.mul_mul_conjTranspose_same (polarU B hM)
    have hexp : polarU B hM
        * ((unitSource B hM)ᴴ * unitSource B hM
          - ((posFloor hG.1 : ℝ) : ℂ) • supportProj hG.1)
        * (polarU B hM)ᴴ
        = sigma B hM - ((posFloor hG.1 : ℝ) : ℂ)
            • supportProj (sigma_posSemidef B hM).1 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        hUsupp, hUGU]
    rwa [hexp] at hconj
  · have hceil := hermLamMax_ceiling hG.1
    have hmidconj := hceil.mul_mul_conjTranspose_same (supportProj hG.1)
    have hcore : supportProj hG.1 * ((unitSource B hM)ᴴ * unitSource B hM)
        * supportProj hG.1 = (unitSource B hM)ᴴ * unitSource B hM := by
      rw [hsuppG', hGsupp']
    have hmid : supportProj hG.1
        * (((hermLamMax hG.1 : ℝ) : ℂ) • 1
          - (unitSource B hM)ᴴ * unitSource B hM)
        * (supportProj hG.1)ᴴ
        = ((hermLamMax hG.1 : ℝ) : ℂ) • supportProj hG.1
          - (unitSource B hM)ᴴ * unitSource B hM := by
      rw [(supportProj_posSemidef hG.1).1.eq, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        supportProj_idem hG.1, hcore]
    rw [hmid] at hmidconj
    have hconj2 := hmidconj.mul_mul_conjTranspose_same (polarU B hM)
    have hexp2 : polarU B hM
        * (((hermLamMax hG.1 : ℝ) : ℂ) • supportProj hG.1
          - (unitSource B hM)ᴴ * unitSource B hM)
        * (polarU B hM)ᴴ
        = ((hermLamMax hG.1 : ℝ) : ℂ)
            • supportProj (sigma_posSemidef B hM).1 - sigma B hM := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        hUsupp, hUGU]
    rwa [hexp2] at hconj2

end SourceAction

end SourceActionCovariance

/-! ### Summable cofinal landing from relative low-island moments

Record `cor:GT-low-island-cofinal-carrier` (LIR.9), with the finite
low-island floor and tail estimates (LIR.5, LIR.8) of
`thm:GT-low-island-relative-moment` derived from the theorem data.

Rendering: the `n`-dependent data are families of finite source cards
`E_n` and carriers `𝒦_n` (finite rendering of the carrier, so the
sublevel projections automatically have finite rank), source-to-carrier
maps `Q_n`, decompositions `A_n = D_n - Q_n^* Q_n ⪰ 0` with island
projections `P_n = 1_{[0,ρ]}(A_n)`, uniform window `d₋ P ⪯ PDP ⪯ d₊ P`
(`ρ < d₋`), positive carrier weights with uniform relative edges
`P K_j P ⪯ κ_j P K₀ P`, unit island vectors, radii with
`∑ R_n^{-1/2} < ∞`, inner-product-preserving embeddings `J_n` into one
comparison Hilbert space, and the summable head increments (LIR.9).  The
conclusion is strong convergence of `J_n Q_n v_n` to a nonzero limit. -/

section LowIslandCofinal

open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank
open scoped ComplexInnerProductSpace

namespace LowIsland

/-- The low spectral island `P = 1_{[0,ρ]}(A)` (LIR.1). -/
noncomputable def islandProj {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (ρ : ℝ) : Matrix m m ℂ :=
  spectralFunction hA (fun l => if l ≤ ρ then 1 else 0)

/-- The sublevel head projection `Π_R = 1_{(-∞,R]}(Ω)`. -/
noncomputable def sublevelProj {m : Type*} [Fintype m] [DecidableEq m]
    {Ω : Matrix m m ℂ} (hΩ : Ω.IsHermitian) (R : ℝ) : Matrix m m ℂ :=
  spectralFunction hΩ (fun l => if l ≤ R then 1 else 0)

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-- The island projection is Hermitian. -/
theorem islandProj_isHermitian {A : Matrix m m ℂ} (hA : A.IsHermitian)
    (ρ : ℝ) : (islandProj hA ρ).IsHermitian :=
  SourceAction.spectralFunction_isHermitian hA _

/-- The sublevel projection is Hermitian and idempotent. -/
theorem sublevelProj_projection {Ω : Matrix m m ℂ} (hΩ : Ω.IsHermitian)
    (R : ℝ) : (sublevelProj hΩ R).IsHermitian ∧
      sublevelProj hΩ R * sublevelProj hΩ R = sublevelProj hΩ R := by
  refine ⟨SourceAction.spectralFunction_isHermitian hΩ _, ?_⟩
  unfold sublevelProj
  rw [spectralFunction_mul]
  refine spectralFunction_congr hΩ fun i => ?_
  split_ifs <;> norm_num

omit [DecidableEq m] [Fintype k] [DecidableEq k] in
/-- Fixed vectors slide through Hermitian projections in pairings. -/
theorem fixed_shuffle {P : Matrix m m ℂ} (hP : P.IsHermitian) {v : m → ℂ}
    (hv : P *ᵥ v = v) (y : m → ℂ) :
    star v ⬝ᵥ (P *ᵥ y) = star v ⬝ᵥ y := by
  rw [dotProduct_mulVec]
  have hsv : star v ᵥ* P = star v := by
    have h1 : star (Pᴴ *ᵥ v) = star v ᵥ* P := by
      rw [star_mulVec, Matrix.conjTranspose_conjTranspose]
    rw [← h1, hP.eq, hv]
  rw [hsv]

omit [DecidableEq m] [Fintype k] [DecidableEq k] in
/-- Sandwich reduction of a quadratic form on a fixed island vector. -/
theorem sandwich_form {P : Matrix m m ℂ} (hP : P.IsHermitian) {v : m → ℂ}
    (hv : P *ᵥ v = v) (X : Matrix m m ℂ) :
    star v ⬝ᵥ ((P * X * P) *ᵥ v) = star v ⬝ᵥ (X *ᵥ v) := by
  have h1 : (P * X * P) *ᵥ v = P *ᵥ (X *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv]
  rw [h1, fixed_shuffle hP hv]

omit [DecidableEq m] [DecidableEq k] in
/-- The source pairing transports to the carrier. -/
theorem dot_conj_weight (Q : Matrix k m ℂ) (W : Matrix k k ℂ) (v : m → ℂ) :
    star (Q *ᵥ v) ⬝ᵥ (W *ᵥ (Q *ᵥ v))
      = star v ⬝ᵥ ((Qᴴ * W * Q) *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

omit [DecidableEq m] [DecidableEq k] in
/-- The Gram pairing transports to the carrier. -/
theorem dot_conj (Q : Matrix k m ℂ) (v : m → ℂ) :
    star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = star v ⬝ᵥ ((Qᴴ * Q) *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec]

/-- The island compression of the PSD remainder is at most `ρ`. -/
theorem island_remainder_bound {A : Matrix m m ℂ} (hA : A.PosSemidef)
    (ρ : ℝ) :
    (((ρ : ℂ)) • islandProj hA.1 ρ
      - islandProj hA.1 ρ * A * islandProj hA.1 ρ).PosSemidef := by
  have hid := spectralFunction_id hA.1
  have h2 : spectralFunction hA.1 (fun l => if l ≤ ρ then 1 else 0)
      * spectralFunction hA.1 id
      * spectralFunction hA.1 (fun l => if l ≤ ρ then 1 else 0)
      = spectralFunction hA.1
        (fun l => ((if l ≤ ρ then 1 else 0) * id l)
          * if l ≤ ρ then 1 else 0) := by
    rw [spectralFunction_mul, spectralFunction_mul]
  rw [hid] at h2
  have hsmul : ((ρ : ℂ))
      • spectralFunction hA.1 (fun l => if l ≤ ρ then 1 else 0)
      = spectralFunction hA.1 (fun l => ρ * if l ≤ ρ then 1 else 0) :=
    (spectralFunction_smul hA.1 ρ _).symm
  unfold islandProj
  rw [h2, hsmul, ← spectralFunction_sub]
  refine spectralFunction_posSemidef hA.1 _ fun i => ?_
  simp only [id]
  split_ifs with hl
  · linarith
  · norm_num

/-- The spectral tail estimate `R (1-Π_R) ⪯ Ω` (behind LIR.8). -/
theorem sublevel_tail_psd {Ω : Matrix m m ℂ} (hΩ : Ω.PosSemidef) (R : ℝ) :
    (Ω - (R : ℂ) • ((1 : Matrix m m ℂ) - sublevelProj hΩ.1 R)).PosSemidef := by
  have hid := spectralFunction_id hΩ.1
  have hone : (1 : Matrix m m ℂ) = spectralFunction hΩ.1 (fun _ => 1) := by
    rw [spectralFunction_const]
    norm_num
  have hsub : (R : ℂ) • ((1 : Matrix m m ℂ) - sublevelProj hΩ.1 R)
      = spectralFunction hΩ.1
        (fun l => R * (1 - if l ≤ R then 1 else 0)) := by
    unfold sublevelProj
    rw [hone, ← spectralFunction_sub, spectralFunction_smul]
  have hgoal : Ω - spectralFunction hΩ.1
      (fun l => R * (1 - if l ≤ R then 1 else 0))
      = spectralFunction hΩ.1
        (fun l => id l - R * (1 - if l ≤ R then 1 else 0)) := by
    rw [spectralFunction_sub, hid]
  rw [hsub, hgoal]
  refine spectralFunction_posSemidef hΩ.1 _ fun i => ?_
  have hnn := hΩ.eigenvalues_nonneg i
  simp only [id]
  split_ifs with hl
  · simpa using hnn
  · push Not at hl
    nlinarith

/-- The weighted sum applied to a vector. -/
theorem weightSum_mulVec {J : Type*} [Fintype J] (W : J → Matrix k k ℂ)
    (x : k → ℂ) :
    ((1 : Matrix k k ℂ) + ∑ j, W j) *ᵥ x = x + ∑ j, W j *ᵥ x := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  funext i
  rw [Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [Fintype m] [DecidableEq m] [Fintype k] in
/-- The weighted mass operator `Ω = 1 + ∑ W_j` is PSD (LIR.3). -/
theorem weightSum_posSemidef {J : Type*} [Fintype J] {W : J → Matrix k k ℂ}
    (hW : ∀ j, (W j).PosSemidef) :
    ((1 : Matrix k k ℂ) + ∑ j, W j).PosSemidef :=
  Matrix.PosDef.one.posSemidef.add
    (Matrix.posSemidef_sum _ fun j _ => hW j)

omit [DecidableEq k] in
/-- **LIR.5 floor**: the physical head of a unit island vector has squared
mass at least `d₋ - ρ`. -/
theorem island_floor {D : Matrix m m ℂ} {Q : Matrix k m ℂ}
    (hA : (D - Qᴴ * Q).PosSemidef) {ρ dlo : ℝ}
    (hlow : (islandProj hA.1 ρ * D * islandProj hA.1 ρ
      - ((dlo : ℂ)) • islandProj hA.1 ρ).PosSemidef)
    {v : m → ℂ} (hv : islandProj hA.1 ρ *ᵥ v = v)
    (hunit : star v ⬝ᵥ v = 1) :
    dlo - ρ ≤ (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re := by
  have hP := islandProj_isHermitian hA.1 ρ
  have hPv : star v ⬝ᵥ ((((dlo : ℂ)) • islandProj hA.1 ρ) *ᵥ v)
      = (dlo : ℂ) := by
    rw [Matrix.smul_mulVec, hv, dotProduct_smul, hunit, smul_eq_mul, mul_one]
  have h1 : dlo ≤ (star v ⬝ᵥ (D *ᵥ v)).re := by
    have hnn := re_form_nonneg hlow v
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hPv,
      sandwich_form hP hv D] at hnn
    have : ((dlo : ℂ)).re = dlo := by norm_num
    linarith [hnn, this.symm.le, this.ge]
  have h2 : (star v ⬝ᵥ ((D - Qᴴ * Q) *ᵥ v)).re ≤ ρ := by
    have hnn := re_form_nonneg (island_remainder_bound hA ρ) v
    have hPρ : star v ⬝ᵥ ((((ρ : ℂ)) • islandProj hA.1 ρ) *ᵥ v)
        = (ρ : ℂ) := by
      rw [Matrix.smul_mulVec, hv, dotProduct_smul, hunit, smul_eq_mul,
        mul_one]
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hPρ,
      sandwich_form hP hv (D - Qᴴ * Q)] at hnn
    have : ((ρ : ℂ)).re = ρ := by norm_num
    linarith
  have hsplit : (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re
      = (star v ⬝ᵥ (D *ᵥ v)).re
        - (star v ⬝ᵥ ((D - Qᴴ * Q) *ᵥ v)).re := by
    rw [dot_conj, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
    ring
  linarith

omit [DecidableEq k] in
/-- **LIR.6 upper edge**: the physical head mass is at most `d₊`. -/
theorem island_mass_upper {D : Matrix m m ℂ} {Q : Matrix k m ℂ}
    (hA : (D - Qᴴ * Q).PosSemidef) {ρ dhi : ℝ}
    (hhi : (((dhi : ℂ)) • islandProj hA.1 ρ
      - islandProj hA.1 ρ * D * islandProj hA.1 ρ).PosSemidef)
    {v : m → ℂ} (hv : islandProj hA.1 ρ *ᵥ v = v)
    (hunit : star v ⬝ᵥ v = 1) :
    (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re ≤ dhi := by
  have hP := islandProj_isHermitian hA.1 ρ
  have h1 : (star v ⬝ᵥ (D *ᵥ v)).re ≤ dhi := by
    have hnn := re_form_nonneg hhi v
    have hPd : star v ⬝ᵥ ((((dhi : ℂ)) • islandProj hA.1 ρ) *ᵥ v)
        = (dhi : ℂ) := by
      rw [Matrix.smul_mulVec, hv, dotProduct_smul, hunit, smul_eq_mul,
        mul_one]
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hPd,
      sandwich_form hP hv D] at hnn
    have : ((dhi : ℂ)).re = dhi := by norm_num
    linarith
  have h2 : 0 ≤ (star v ⬝ᵥ ((D - Qᴴ * Q) *ᵥ v)).re := re_form_nonneg hA v
  have hsplit : (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re
      = (star v ⬝ᵥ (D *ᵥ v)).re
        - (star v ⬝ᵥ ((D - Qᴴ * Q) *ᵥ v)).re := by
    rw [dot_conj, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
    ring
  linarith

set_option maxHeartbeats 1000000 in
-- the sublevel projection of the weighted mass operator forces heavy
-- spectral-calculus unification; the default heartbeat budget is too small
/-- **LIR.6/LIR.8**: the weighted carrier mass of an island head is at most
`κ_* d₊`, hence the sublevel tail obeys the spectral estimate. -/
theorem island_tail {J : Type*} [Fintype J] {D : Matrix m m ℂ}
    {Q : Matrix k m ℂ} (hA : (D - Qᴴ * Q).PosSemidef) {ρ dhi : ℝ}
    {kap : J → ℝ} (hkapnn : ∀ j, 0 ≤ kap j) {W : J → Matrix k k ℂ}
    (hW : ∀ j, (W j).PosSemidef)
    (hhi : (((dhi : ℂ)) • islandProj hA.1 ρ
      - islandProj hA.1 ρ * D * islandProj hA.1 ρ).PosSemidef)
    (hkap : ∀ j, ((kap j : ℂ)
        • (islandProj hA.1 ρ * (Qᴴ * Q) * islandProj hA.1 ρ)
      - islandProj hA.1 ρ * (Qᴴ * W j * Q)
        * islandProj hA.1 ρ).PosSemidef)
    {v : m → ℂ} (hv : islandProj hA.1 ρ *ᵥ v = v)
    (hunit : star v ⬝ᵥ v = 1) (R : ℝ) :
    R * (star (((1 : Matrix k k ℂ)
          - sublevelProj (weightSum_posSemidef hW).1 R) *ᵥ (Q *ᵥ v))
        ⬝ᵥ (((1 : Matrix k k ℂ)
          - sublevelProj (weightSum_posSemidef hW).1 R)
            *ᵥ (Q *ᵥ v))).re
      ≤ (1 + ∑ j, kap j) * dhi := by
  have hP := islandProj_isHermitian hA.1 ρ
  have hK0 : (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re ≤ dhi :=
    island_mass_upper hA hhi hv hunit
  have hK0nn : 0 ≤ (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re := by
    have := dotProduct_star_self_nonneg (Q *ᵥ v)
    exact_mod_cast (Complex.le_def.mp this).1
  -- per-weight relative edge
  have hjbound : ∀ j, (star (Q *ᵥ v) ⬝ᵥ (W j *ᵥ (Q *ᵥ v))).re
      ≤ kap j * dhi := by
    intro j
    have hnn := re_form_nonneg (hkap j) v
    have hsand1 := sandwich_form hP hv (Qᴴ * Q)
    have hsand2 := sandwich_form hP hv (Qᴴ * W j * Q)
    have hsm : star v ⬝ᵥ (((kap j : ℂ)
        • (islandProj hA.1 ρ * (Qᴴ * Q) * islandProj hA.1 ρ)) *ᵥ v)
        = (kap j : ℂ) * (star v ⬝ᵥ ((Qᴴ * Q) *ᵥ v)) := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hsand1]
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hsm, hsand2,
      Complex.re_ofReal_mul] at hnn
    have hQW : (star v ⬝ᵥ ((Qᴴ * W j * Q) *ᵥ v)).re
        = (star (Q *ᵥ v) ⬝ᵥ (W j *ᵥ (Q *ᵥ v))).re := by
      rw [dot_conj_weight]
    have hQ0 : (star v ⬝ᵥ ((Qᴴ * Q) *ᵥ v)).re
        = (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re := by
      rw [dot_conj]
    rw [hQ0, hQW] at hnn
    have := mul_le_mul_of_nonneg_left hK0 (hkapnn j)
    linarith
  -- total weighted mass
  have hmass : (star (Q *ᵥ v)
      ⬝ᵥ (((1 : Matrix k k ℂ) + ∑ j, W j) *ᵥ (Q *ᵥ v))).re
      ≤ (1 + ∑ j, kap j) * dhi := by
    rw [weightSum_mulVec, dotProduct_add, dotProduct_sum, Complex.add_re,
      Complex.re_sum]
    have hsum : ∑ j, (star (Q *ᵥ v) ⬝ᵥ (W j *ᵥ (Q *ᵥ v))).re
        ≤ ∑ j, kap j * dhi := Finset.sum_le_sum fun j _ => hjbound j
    have hdhi : 0 ≤ dhi := le_trans hK0nn hK0
    calc (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re
          + ∑ j, (star (Q *ᵥ v) ⬝ᵥ (W j *ᵥ (Q *ᵥ v))).re
        ≤ dhi + ∑ j, kap j * dhi := add_le_add hK0 hsum
      _ = (1 + ∑ j, kap j) * dhi := by
          rw [← Finset.sum_mul]
          ring
  -- spectral tail estimate
  have htail := re_form_nonneg
    (sublevel_tail_psd (weightSum_posSemidef hW) R) (Q *ᵥ v)
  set x := Q *ᵥ v with hx
  set Pi1 := (1 : Matrix k k ℂ)
    - sublevelProj (weightSum_posSemidef hW).1 R with hPi1
  have hPi1herm : Pi1.IsHermitian := by
    rw [hPi1]
    exact Matrix.isHermitian_one.sub
      (sublevelProj_projection (weightSum_posSemidef hW).1 R).1
  have hPi1idem : Pi1 * Pi1 = Pi1 := by
    rw [hPi1]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul,
      (sublevelProj_projection (weightSum_posSemidef hW).1 R).2,
      Matrix.mul_one]
    abel
  have hq : star x ⬝ᵥ (Pi1 *ᵥ x) = star (Pi1 *ᵥ x) ⬝ᵥ (Pi1 *ᵥ x) := by
    rw [dot_conj Pi1 x, hPi1herm.eq, hPi1idem]
  have hsm2 : star x ⬝ᵥ (((R : ℂ) • Pi1) *ᵥ x)
      = (R : ℂ) * (star x ⬝ᵥ (Pi1 *ᵥ x)) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hsm2, hq,
    Complex.re_ofReal_mul] at htail
  linarith

set_option maxHeartbeats 1000000 in
-- the assembled landing argument instantiates the spectral tail estimate
-- at every stage; the default heartbeat budget is too small
/-- **`cor:GT-low-island-cofinal-carrier`**: with uniform low-island
windows, relative edges, summable radii, and summable head increments
(LIR.9), the embedded physical heads `J_n Q_n v_n` converge strongly to a
nonzero limit. -/
theorem low_island_cofinal_landing
    {ι κ : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    {Hc : Type*} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    [CompleteSpace Hc] {J : Type*} [Fintype J]
    (D : ∀ n, Matrix (ι n) (ι n) ℂ) (Q : ∀ n, Matrix (κ n) (ι n) ℂ)
    (hA : ∀ n, (D n - (Q n)ᴴ * Q n).PosSemidef)
    (ρ dlo dhi : ℝ) (_hρ : 0 ≤ ρ) (hd : ρ < dlo)
    (kap : J → ℝ) (hkapnn : ∀ j, 0 ≤ kap j)
    (W : ∀ n, J → Matrix (κ n) (κ n) ℂ) (hW : ∀ n j, (W n j).PosSemidef)
    (hlow : ∀ n, (islandProj (hA n).1 ρ * D n * islandProj (hA n).1 ρ
      - ((dlo : ℂ)) • islandProj (hA n).1 ρ).PosSemidef)
    (hhi : ∀ n, (((dhi : ℂ)) • islandProj (hA n).1 ρ
      - islandProj (hA n).1 ρ * D n * islandProj (hA n).1 ρ).PosSemidef)
    (hkap : ∀ n j, ((kap j : ℂ)
        • (islandProj (hA n).1 ρ * ((Q n)ᴴ * Q n) * islandProj (hA n).1 ρ)
      - islandProj (hA n).1 ρ * ((Q n)ᴴ * W n j * Q n)
        * islandProj (hA n).1 ρ).PosSemidef)
    (v : ∀ n, ι n → ℂ) (hv : ∀ n, islandProj (hA n).1 ρ *ᵥ v n = v n)
    (hunit : ∀ n, star (v n) ⬝ᵥ v n = 1)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (_hRmono : Monotone R)
    (_hRtop : Filter.Tendsto R Filter.atTop Filter.atTop)
    (hRsum : Summable fun n => (Real.sqrt (R n))⁻¹)
    (emb : ∀ n, (κ n → ℂ) →ₗ[ℂ] Hc)
    (hemb : ∀ n (x y : κ n → ℂ), ⟪emb n x, emb n y⟫ = star x ⬝ᵥ y)
    (hheads : Summable fun n =>
      ‖emb (n + 1) (sublevelProj (weightSum_posSemidef (hW (n + 1))).1
          (R (n + 1)) *ᵥ (Q (n + 1) *ᵥ v (n + 1)))
        - emb n (sublevelProj (weightSum_posSemidef (hW n)).1 (R n)
          *ᵥ (Q n *ᵥ v n))‖) :
    ∃ L : Hc, L ≠ 0 ∧ Filter.Tendsto (fun n => emb n (Q n *ᵥ v n))
      Filter.atTop (nhds L) := by
  classical
  -- the embedding preserves squared masses
  have hnorm : ∀ n (x : κ n → ℂ), ‖emb n x‖ ^ 2 = (star x ⬝ᵥ x).re := by
    intro n x
    rw [← cre_inner_self (emb n x), hemb]
  have hkapsum : (0 : ℝ) ≤ ∑ j, kap j := Finset.sum_nonneg fun j _ => hkapnn j
  have hdhi : 0 < dhi := by
    have h1 := island_floor (hA 0) (hlow 0) (hv 0) (hunit 0)
    have h2 := island_mass_upper (hA 0) (hhi 0) (hv 0) (hunit 0)
    linarith
  have hKD : 0 ≤ (1 + ∑ j, kap j) * dhi := by
    nlinarith
  -- per-stage tail estimates
  have htail : ∀ n, ‖emb n (Q n *ᵥ v n)
      - emb n (sublevelProj (weightSum_posSemidef (hW n)).1 (R n)
        *ᵥ (Q n *ᵥ v n))‖
      ≤ Real.sqrt ((1 + ∑ j, kap j) * dhi) * (Real.sqrt (R n))⁻¹ := by
    intro n
    have hyz : emb n (Q n *ᵥ v n)
        - emb n (sublevelProj (weightSum_posSemidef (hW n)).1 (R n)
          *ᵥ (Q n *ᵥ v n))
        = emb n (((1 : Matrix (κ n) (κ n) ℂ)
            - sublevelProj (weightSum_posSemidef (hW n)).1 (R n))
          *ᵥ (Q n *ᵥ v n)) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, map_sub]
    have hbound := island_tail (hA n) hkapnn (hW n) (hhi n) (hkap n)
      (hv n) (hunit n) (R n)
    rw [hyz]
    set nu := ‖emb n (((1 : Matrix (κ n) (κ n) ℂ)
        - sublevelProj (weightSum_posSemidef (hW n)).1 (R n))
      *ᵥ (Q n *ᵥ v n))‖ with hnu
    have hsq2 : nu ^ 2 ≤ (1 + ∑ j, kap j) * dhi / R n := by
      rw [le_div_iff₀ (hRpos n), hnu, hnorm, mul_comm]
      exact hbound
    calc nu = Real.sqrt (nu ^ 2) := (Real.sqrt_sq (by rw [hnu]; positivity)).symm
      _ ≤ Real.sqrt ((1 + ∑ j, kap j) * dhi / R n) := Real.sqrt_le_sqrt hsq2
      _ = Real.sqrt ((1 + ∑ j, kap j) * dhi) * (Real.sqrt (R n))⁻¹ := by
          rw [Real.sqrt_div hKD, div_eq_mul_inv]
  -- summable stage-to-stage distances
  have hdist : ∀ n, dist (emb n (Q n *ᵥ v n))
      (emb (n + 1) (Q (n + 1) *ᵥ v (n + 1)))
      ≤ Real.sqrt ((1 + ∑ j, kap j) * dhi) * (Real.sqrt (R n))⁻¹
        + ‖emb (n + 1) (sublevelProj (weightSum_posSemidef (hW (n + 1))).1
            (R (n + 1)) *ᵥ (Q (n + 1) *ᵥ v (n + 1)))
          - emb n (sublevelProj (weightSum_posSemidef (hW n)).1 (R n)
            *ᵥ (Q n *ᵥ v n))‖
        + Real.sqrt ((1 + ∑ j, kap j) * dhi) * (Real.sqrt (R (n + 1)))⁻¹ := by
    intro n
    rw [dist_eq_norm]
    have hdecomp : emb n (Q n *ᵥ v n) - emb (n + 1) (Q (n + 1) *ᵥ v (n + 1))
        = (emb n (Q n *ᵥ v n)
            - emb n (sublevelProj (weightSum_posSemidef (hW n)).1 (R n)
              *ᵥ (Q n *ᵥ v n)))
          + (emb n (sublevelProj (weightSum_posSemidef (hW n)).1 (R n)
              *ᵥ (Q n *ᵥ v n))
            - emb (n + 1)
              (sublevelProj (weightSum_posSemidef (hW (n + 1))).1 (R (n + 1))
                *ᵥ (Q (n + 1) *ᵥ v (n + 1))))
          + (emb (n + 1)
              (sublevelProj (weightSum_posSemidef (hW (n + 1))).1 (R (n + 1))
                *ᵥ (Q (n + 1) *ᵥ v (n + 1)))
            - emb (n + 1) (Q (n + 1) *ᵥ v (n + 1))) := by
      abel
    rw [hdecomp]
    refine (norm_add₃_le).trans ?_
    refine add_le_add (add_le_add (htail n) (le_of_eq (norm_sub_rev _ _))) ?_
    rw [norm_sub_rev]
    exact htail (n + 1)
  -- summability of the increment bound
  have htau : Summable fun n =>
      Real.sqrt ((1 + ∑ j, kap j) * dhi) * (Real.sqrt (R n))⁻¹ :=
    hRsum.mul_left _
  have hb : Summable fun n =>
      Real.sqrt ((1 + ∑ j, kap j) * dhi) * (Real.sqrt (R n))⁻¹
        + ‖emb (n + 1) (sublevelProj (weightSum_posSemidef (hW (n + 1))).1
            (R (n + 1)) *ᵥ (Q (n + 1) *ᵥ v (n + 1)))
          - emb n (sublevelProj (weightSum_posSemidef (hW n)).1 (R n)
            *ᵥ (Q n *ᵥ v n))‖
        + Real.sqrt ((1 + ∑ j, kap j) * dhi) * (Real.sqrt (R (n + 1)))⁻¹ :=
    (htau.add hheads).add ((summable_nat_add_iff 1).mpr htau)
  have hcauchy : CauchySeq fun n => emb n (Q n *ᵥ v n) :=
    cauchySeq_of_dist_le_of_summable _ hdist hb
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the limit is nonzero by the island floor
  have hfloor2 : ∀ n, Real.sqrt (dlo - ρ) ≤ ‖emb n (Q n *ᵥ v n)‖ := by
    intro n
    have h2 : dlo - ρ ≤ ‖emb n (Q n *ᵥ v n)‖ ^ 2 := by
      rw [hnorm]
      exact island_floor (hA n) (hlow n) (hv n) (hunit n)
    calc Real.sqrt (dlo - ρ) ≤ Real.sqrt (‖emb n (Q n *ᵥ v n)‖ ^ 2) :=
          Real.sqrt_le_sqrt h2
      _ = ‖emb n (Q n *ᵥ v n)‖ := Real.sqrt_sq (norm_nonneg _)
  have hLnorm : Real.sqrt (dlo - ρ) ≤ ‖L‖ :=
    ge_of_tendsto' hL.norm hfloor2
  have hLne : L ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hLnorm
    have := Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < dlo - ρ)
    linarith
  exact ⟨L, hLne, hL⟩

end LowIsland

end LowIslandCofinal

end NCG
