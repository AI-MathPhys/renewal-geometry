/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Score pressure: log-partition curvature and the Hellinger localizer

Exact encoding of `thm:GT-score-pressure` (NL.5–NL.9) in directional form.

Along a one-parameter family of log-weights `φ θ ω` (direction `u` of the
parameter space) with `Z(θ) = ∑ exp(φ θ ω)`, `p_θ = exp(φ θ)/Z(θ)`:

* `log_partition_derivatives` (NL.6): `(log Z)' = E_θ[φ']` and
  `(log Z)'' = E_θ[φ''] + Var_θ(φ')`, where `Var_θ(φ') = E_θ[(φ' - E_θ φ')²]`
  is the (positive) score localizer quadratic form (NL.5, `variance_nonneg`);
* `action_form` (NL.7): for `w = e^{-A}` this reads `-E[A''] + Cov(A', A')`;
* `hasDerivAt_hellinger` / `hellinger_gram_eq_variance`: the derivative of
  `𝔥(θ) = 2√p_θ` at `0` is `√p₀ · s`, with `s = φ' - E₀ φ'` the centred score,
  so its Gram is the localizer (NL.5);
* `probe_quadratic_bound` / `polarized_localizer_bound` (NL.8–NL.9): for a
  physically executable one-sided probe with Taylor remainder
  `‖𝔥(εu) - 𝔥(0) - ε D u‖ ≤ M ε² ‖u‖² / 2` and `‖D u‖ ≤ L ‖u‖`, the probe
  forms `q_ε(u) = ε⁻²‖𝔥(εu) - 𝔥(0)‖²` and their polarization
  `𝕀_ε(x,y) = ½(q_ε(x+y) - q_ε(x) - q_ε(y))` satisfy the displayed error
  certificate, and `𝕀_ε → 𝕀` (`polarized_localizer_tendsto`).
-/

open Finset Filter Topology

namespace NCG
namespace ScorePressure

/-! ### Log-partition curvature (NL.5–NL.7) -/

section Partition

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The partition function `Z(θ) = ∑ exp(φ θ ω)`. -/
noncomputable def partition (φ : ℝ → Ω → ℝ) (θ : ℝ) : ℝ := ∑ ω, Real.exp (φ θ ω)

/-- The normalized law `p_θ = exp(φ θ)/Z(θ)`. -/
noncomputable def law (φ : ℝ → Ω → ℝ) (θ : ℝ) (ω : Ω) : ℝ :=
  Real.exp (φ θ ω) / partition φ θ

/-- Expectation under `p_θ`. -/
noncomputable def expect (φ : ℝ → Ω → ℝ) (θ : ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, law φ θ ω * f ω

/-- Variance under `p_θ`. -/
noncomputable def variance (φ : ℝ → Ω → ℝ) (θ : ℝ) (f : Ω → ℝ) : ℝ :=
  expect φ θ (fun ω => (f ω - expect φ θ f) ^ 2)

theorem partition_pos (φ : ℝ → Ω → ℝ) (θ : ℝ) : 0 < partition φ θ :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem law_nonneg (φ : ℝ → Ω → ℝ) (θ : ℝ) (ω : Ω) : 0 ≤ law φ θ ω :=
  div_nonneg (Real.exp_pos _).le (partition_pos φ θ).le

theorem law_sum (φ : ℝ → Ω → ℝ) (θ : ℝ) : ∑ ω, law φ θ ω = 1 := by
  unfold law
  rw [← Finset.sum_div]
  exact div_self (partition_pos φ θ).ne'

/-- **(NL.5)**: the score localizer quadratic form is nonnegative. -/
theorem variance_nonneg (φ : ℝ → Ω → ℝ) (θ : ℝ) (f : Ω → ℝ) : 0 ≤ variance φ θ f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (law_nonneg φ θ ω) (sq_nonneg _)

/-- `Var(f) = E[f²] - (E f)²`. -/
theorem variance_eq (φ : ℝ → Ω → ℝ) (θ : ℝ) (f : Ω → ℝ) :
    variance φ θ f = expect φ θ (fun ω => f ω ^ 2) - expect φ θ f ^ 2 := by
  have h1 := law_sum φ θ
  have hm : ∑ ω, law φ θ ω * f ω = expect φ θ f := rfl
  change ∑ ω, law φ θ ω * (f ω - expect φ θ f) ^ 2
    = (∑ ω, law φ θ ω * f ω ^ 2) - expect φ θ f ^ 2
  have hterm : ∀ ω, law φ θ ω * (f ω - expect φ θ f) ^ 2
      = law φ θ ω * f ω ^ 2 - 2 * expect φ θ f * (law φ θ ω * f ω)
        + expect φ θ f ^ 2 * law φ θ ω := fun ω => by ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hm, h1]
  ring

/-- Derivative of a finite sum of real functions. -/
theorem hasDerivAt_sum_univ {ι : Type*} [Fintype ι] (A : ι → ℝ → ℝ) (A' : ι → ℝ) (x : ℝ)
    (h : ∀ i, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y => ∑ i, A i y) (∑ i, A' i) x := by
  have := HasDerivAt.sum (u := Finset.univ) (fun i _ => h i)
  have hfun : (fun y => ∑ i, A i y) = ∑ i, A i := by
    funext y
    simp [Finset.sum_apply]
  rw [hfun]
  exact this

/-- **(NL.6)**: first and second derivatives of `log Z` along the family. -/
theorem log_partition_derivatives (φ φ' φ'' : ℝ → Ω → ℝ)
    (hφ : ∀ ω θ, HasDerivAt (fun θ => φ θ ω) (φ' θ ω) θ)
    (hφ' : ∀ ω θ, HasDerivAt (fun θ => φ' θ ω) (φ'' θ ω) θ) (θ : ℝ) :
    HasDerivAt (fun θ => Real.log (partition φ θ)) (expect φ θ (φ' θ)) θ ∧
      HasDerivAt (fun θ => expect φ θ (φ' θ))
        (expect φ θ (φ'' θ) + variance φ θ (φ' θ)) θ := by
  -- derivative of `Z`
  have hZ : ∀ θ, HasDerivAt (partition φ) (∑ ω, Real.exp (φ θ ω) * φ' θ ω) θ := by
    intro θ
    unfold partition
    exact hasDerivAt_sum_univ (fun ω θ => Real.exp (φ θ ω)) _ θ
      fun ω => (Real.hasDerivAt_exp _).comp θ (hφ ω θ)
  -- derivative of `Z₁ = ∑ exp(φ) φ'`
  have hZ1 : ∀ θ, HasDerivAt (fun θ => ∑ ω, Real.exp (φ θ ω) * φ' θ ω)
      (∑ ω, Real.exp (φ θ ω) * (φ'' θ ω + φ' θ ω ^ 2)) θ := by
    intro θ
    refine hasDerivAt_sum_univ (fun ω θ => Real.exp (φ θ ω) * φ' θ ω) _ θ fun ω => ?_
    refine (((Real.hasDerivAt_exp _).comp θ (hφ ω θ)).mul (hφ' ω θ)).congr_deriv ?_
    simp only [Function.comp_apply]
    ring
  have hZpos := partition_pos φ θ
  have hE1 : expect φ θ (φ' θ) = (∑ ω, Real.exp (φ θ ω) * φ' θ ω) / partition φ θ := by
    unfold expect law
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun ω _ => ?_
    ring
  have hE2 : expect φ θ (φ'' θ) + expect φ θ (fun ω => φ' θ ω ^ 2)
      = (∑ ω, Real.exp (φ θ ω) * (φ'' θ ω + φ' θ ω ^ 2)) / partition φ θ := by
    unfold expect law
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    ring
  constructor
  · have := (hZ θ).log hZpos.ne'
    rw [hE1]
    exact this
  · -- quotient rule for `Z₁ / Z`
    have hfun : (fun θ => expect φ θ (φ' θ))
        = fun θ => (∑ ω, Real.exp (φ θ ω) * φ' θ ω) / partition φ θ := by
      funext θ'
      unfold expect law
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun ω _ => ?_
      ring
    rw [hfun]
    refine ((hZ1 θ).div (hZ θ) hZpos.ne').congr_deriv ?_
    rw [variance_eq, hE1]
    rw [show expect φ θ (φ'' θ) + (expect φ θ (fun ω => φ' θ ω ^ 2)
          - ((∑ ω, Real.exp (φ θ ω) * φ' θ ω) / partition φ θ) ^ 2)
        = (expect φ θ (φ'' θ) + expect φ θ (fun ω => φ' θ ω ^ 2))
          - ((∑ ω, Real.exp (φ θ ω) * φ' θ ω) / partition φ θ) ^ 2 by ring, hE2]
    field_simp

/-- **(NL.7)**: for `w = e^{-A}` the curvature is `-E[A''] + Cov(A', A')`. -/
theorem action_form (A A' A'' : ℝ → Ω → ℝ)
    (hA : ∀ ω θ, HasDerivAt (fun θ => A θ ω) (A' θ ω) θ)
    (hA' : ∀ ω θ, HasDerivAt (fun θ => A' θ ω) (A'' θ ω) θ) (θ : ℝ) :
    HasDerivAt (fun θ => expect (fun θ ω => -A θ ω) θ (fun ω => -A' θ ω))
      (-expect (fun θ ω => -A θ ω) θ (A'' θ)
        + variance (fun θ ω => -A θ ω) θ (A' θ)) θ := by
  have h := (log_partition_derivatives (fun θ ω => -A θ ω) (fun θ ω => -A' θ ω)
    (fun θ ω => -A'' θ ω) (fun ω θ => (hA ω θ).neg) (fun ω θ => (hA' ω θ).neg) θ).2
  have e1 : expect (fun θ ω => -A θ ω) θ (fun ω => -A'' θ ω)
      = -expect (fun θ ω => -A θ ω) θ (A'' θ) := by
    unfold expect
    simp only [mul_neg, Finset.sum_neg_distrib]
  have e2 : variance (fun θ ω => -A θ ω) θ (fun ω => -A' θ ω)
      = variance (fun θ ω => -A θ ω) θ (A' θ) := by
    unfold variance expect
    simp only [mul_neg, Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    ring
  rw [e1, e2] at h
  exact h

/-! ### The Hellinger derivative and its Gram (NL.5) -/

/-- The Hellinger coordinates `𝔥(θ) = 2√p_θ`. -/
noncomputable def hellinger (φ : ℝ → Ω → ℝ) (θ : ℝ) (ω : Ω) : ℝ := 2 * Real.sqrt (law φ θ ω)

/-- `𝔥'(θ)(ω) = √p_θ(ω) · (φ'(ω) - E_θ φ')`: the Hellinger derivative is the
square-root-weighted centred score. -/
theorem hasDerivAt_hellinger (φ φ' : ℝ → Ω → ℝ)
    (hφ : ∀ ω θ, HasDerivAt (fun θ => φ θ ω) (φ' θ ω) θ) (θ : ℝ) (ω : Ω) :
    HasDerivAt (fun θ => hellinger φ θ ω)
      (Real.sqrt (law φ θ ω) * (φ' θ ω - expect φ θ (φ' θ))) θ := by
  have hZ : HasDerivAt (partition φ) (∑ ω, Real.exp (φ θ ω) * φ' θ ω) θ := by
    unfold partition
    exact hasDerivAt_sum_univ (fun ω θ => Real.exp (φ θ ω)) _ θ
      fun ω => (Real.hasDerivAt_exp _).comp θ (hφ ω θ)
  have hZpos := partition_pos φ θ
  have hE : expect φ θ (φ' θ)
      = (∑ ω', Real.exp (φ θ ω') * φ' θ ω') / partition φ θ := by
    unfold expect law
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    ring
  have hp : HasDerivAt (fun θ => law φ θ ω)
      (law φ θ ω * (φ' θ ω - expect φ θ (φ' θ))) θ := by
    refine (((Real.hasDerivAt_exp _).comp θ (hφ ω θ)).div hZ hZpos.ne').congr_deriv ?_
    rw [hE]
    unfold law
    simp only [Function.comp_apply]
    field_simp
  have hppos : 0 < law φ θ ω := div_pos (Real.exp_pos _) hZpos
  have hsqrt := hp.sqrt hppos.ne'
  unfold hellinger
  refine (hsqrt.const_mul 2).congr_deriv ?_
  have hs : Real.sqrt (law φ θ ω) ≠ 0 := (Real.sqrt_pos.mpr hppos).ne'
  have hq : law φ θ ω = Real.sqrt (law φ θ ω) * Real.sqrt (law φ θ ω) :=
    (Real.mul_self_sqrt hppos.le).symm
  calc 2 * (law φ θ ω * (φ' θ ω - expect φ θ (φ' θ)) / (2 * Real.sqrt (law φ θ ω)))
      = (Real.sqrt (law φ θ ω) * Real.sqrt (law φ θ ω)) * (φ' θ ω - expect φ θ (φ' θ))
        / Real.sqrt (law φ θ ω) := by
        rw [← hq]; field_simp
    _ = Real.sqrt (law φ θ ω) * (φ' θ ω - expect φ θ (φ' θ)) := by
        field_simp

/-- The Gram of the Hellinger derivative is the score localizer (variance). -/
theorem hellinger_gram_eq_variance (φ φ' : ℝ → Ω → ℝ) (θ : ℝ) :
    ∑ ω, (Real.sqrt (law φ θ ω) * (φ' θ ω - expect φ θ (φ' θ))) ^ 2
      = variance φ θ (φ' θ) := by
  unfold variance expect
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [mul_pow, Real.sq_sqrt (law_nonneg φ θ ω)]

end Partition

/-! ### One-sided probes and polarization (NL.8, NL.9) -/

section Probe

variable {U F : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The probe quadratic form `q_ε(u) = ε⁻²‖𝔥(εu) - 𝔥(0)‖²`. -/
noncomputable def probeForm (𝔥 : U → F) (ε : ℝ) (u : U) : ℝ := ε⁻¹ ^ 2 * ‖𝔥 (ε • u) - 𝔥 0‖ ^ 2

/-- The polarized probe localizer `𝕀_ε(x,y) = ½(q_ε(x+y) - q_ε(x) - q_ε(y))`. -/
noncomputable def probeLocalizer (𝔥 : U → F) (ε : ℝ) (x y : U) : ℝ :=
  (1 / 2) * (probeForm 𝔥 ε (x + y) - probeForm 𝔥 ε x - probeForm 𝔥 ε y)

/-- The exact localizer `𝕀(x,y) = ⟪Dx, Dy⟫` as a polarization of `‖D u‖²`. -/
theorem localizer_polarization (D : U →L[ℝ] F) (x y : U) :
    inner ℝ (D x) (D y) = (1 / 2) * (‖D (x + y)‖ ^ 2 - ‖D x‖ ^ 2 - ‖D y‖ ^ 2) := by
  rw [map_add, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
    real_inner_comm (D y) (D x)]
  ring

/-- **(NL.9, one direction)**: with the Taylor remainder bound and the
derivative bound, `|q_ε(u) - ‖Du‖²| ≤ M L ε ‖u‖³ + M² ε² ‖u‖⁴ / 4`. -/
theorem probe_quadratic_bound (𝔥 : U → F) (D : U →L[ℝ] F) (M L ε : ℝ) (hε : 0 < ε)
    (u : U)
    (hL : ‖D u‖ ≤ L * ‖u‖)
    (htaylor : ‖𝔥 (ε • u) - 𝔥 0 - ε • D u‖ ≤ M * ε ^ 2 * ‖u‖ ^ 2 / 2) :
    |probeForm 𝔥 ε u - ‖D u‖ ^ 2| ≤ M * L * ε * ‖u‖ ^ 3 + M ^ 2 * ε ^ 2 * ‖u‖ ^ 4 / 4 := by
  set r := 𝔥 (ε • u) - 𝔥 0 - ε • D u with hr
  have hdecomp : 𝔥 (ε • u) - 𝔥 0 = ε • D u + r := by rw [hr]; abel
  unfold probeForm
  rw [hdecomp]
  -- expand the squared norm
  have hexp : ‖ε • D u + r‖ ^ 2 = ε ^ 2 * ‖D u‖ ^ 2 + 2 * ε * inner ℝ (D u) r + ‖r‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm r (D u)]
    simp only [RCLike.conj_to_real]
    ring
  rw [hexp]
  have hεne : ε ≠ 0 := hε.ne'
  have hmain : ε⁻¹ ^ 2 * (ε ^ 2 * ‖D u‖ ^ 2 + 2 * ε * inner ℝ (D u) r + ‖r‖ ^ 2) - ‖D u‖ ^ 2
      = 2 * ε⁻¹ * inner ℝ (D u) r + ε⁻¹ ^ 2 * ‖r‖ ^ 2 := by
    field_simp
    ring
  rw [hmain]
  have hDu : 0 ≤ ‖D u‖ := norm_nonneg _
  have hinner : |inner ℝ (D u) r| ≤ ‖D u‖ * ‖r‖ := abs_real_inner_le_norm _ _
  have hr_nonneg : 0 ≤ ‖r‖ := norm_nonneg _
  have hL' : ‖D u‖ * ‖r‖ ≤ (L * ‖u‖) * (M * ε ^ 2 * ‖u‖ ^ 2 / 2) :=
    mul_le_mul hL htaylor hr_nonneg (by
      have := norm_nonneg (D u)
      linarith)
  have hr2 : ‖r‖ ^ 2 ≤ (M * ε ^ 2 * ‖u‖ ^ 2 / 2) ^ 2 :=
    pow_le_pow_left₀ hr_nonneg htaylor 2
  have hεinv : 0 < ε⁻¹ := inv_pos.mpr hε
  calc |2 * ε⁻¹ * inner ℝ (D u) r + ε⁻¹ ^ 2 * ‖r‖ ^ 2|
      ≤ |2 * ε⁻¹ * inner ℝ (D u) r| + |ε⁻¹ ^ 2 * ‖r‖ ^ 2| := abs_add_le _ _
    _ = 2 * ε⁻¹ * |inner ℝ (D u) r| + ε⁻¹ ^ 2 * ‖r‖ ^ 2 := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ε⁻¹),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ 2 * ‖r‖ ^ 2)]
    _ ≤ 2 * ε⁻¹ * ((L * ‖u‖) * (M * ε ^ 2 * ‖u‖ ^ 2 / 2))
        + ε⁻¹ ^ 2 * (M * ε ^ 2 * ‖u‖ ^ 2 / 2) ^ 2 := by
        gcongr
        exact le_trans hinner hL'
    _ = M * L * ε * ‖u‖ ^ 3 + M ^ 2 * ε ^ 2 * ‖u‖ ^ 4 / 4 := by
        field_simp
        ring

/-- **(NL.9)**: the polarized probe localizer reconstructs `⟪Dx, Dy⟫` with the
displayed finite error certificate. -/
theorem polarized_localizer_bound (𝔥 : U → F) (D : U →L[ℝ] F) (M L ε : ℝ) (hε : 0 < ε)
    (x y : U)
    (hL : ∀ u, ‖D u‖ ≤ L * ‖u‖)
    (htaylor : ∀ u, ‖𝔥 (ε • u) - 𝔥 0 - ε • D u‖ ≤ M * ε ^ 2 * ‖u‖ ^ 2 / 2) :
    |probeLocalizer 𝔥 ε x y - inner ℝ (D x) (D y)|
      ≤ (1 / 2) * ((M * L * ε * ‖x‖ ^ 3 + M ^ 2 * ε ^ 2 * ‖x‖ ^ 4 / 4)
        + (M * L * ε * ‖y‖ ^ 3 + M ^ 2 * ε ^ 2 * ‖y‖ ^ 4 / 4)
        + (M * L * ε * ‖x + y‖ ^ 3 + M ^ 2 * ε ^ 2 * ‖x + y‖ ^ 4 / 4)) := by
  rw [localizer_polarization]
  unfold probeLocalizer
  have hx := probe_quadratic_bound 𝔥 D M L ε hε x (hL x) (htaylor x)
  have hy := probe_quadratic_bound 𝔥 D M L ε hε y (hL y) (htaylor y)
  have hxy := probe_quadratic_bound 𝔥 D M L ε hε (x + y) (hL (x + y)) (htaylor (x + y))
  have hid : (1 / 2) * (probeForm 𝔥 ε (x + y) - probeForm 𝔥 ε x - probeForm 𝔥 ε y)
      - (1 / 2) * (‖D (x + y)‖ ^ 2 - ‖D x‖ ^ 2 - ‖D y‖ ^ 2)
      = (1 / 2) * ((probeForm 𝔥 ε (x + y) - ‖D (x + y)‖ ^ 2)
        - (probeForm 𝔥 ε x - ‖D x‖ ^ 2) - (probeForm 𝔥 ε y - ‖D y‖ ^ 2)) := by ring
  rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  gcongr
  calc |(probeForm 𝔥 ε (x + y) - ‖D (x + y)‖ ^ 2)
        - (probeForm 𝔥 ε x - ‖D x‖ ^ 2) - (probeForm 𝔥 ε y - ‖D y‖ ^ 2)|
      ≤ |probeForm 𝔥 ε (x + y) - ‖D (x + y)‖ ^ 2|
        + |probeForm 𝔥 ε x - ‖D x‖ ^ 2| + |probeForm 𝔥 ε y - ‖D y‖ ^ 2| := by
        have := abs_sub (probeForm 𝔥 ε (x + y) - ‖D (x + y)‖ ^ 2
          - (probeForm 𝔥 ε x - ‖D x‖ ^ 2)) (probeForm 𝔥 ε y - ‖D y‖ ^ 2)
        have h2 := abs_sub (probeForm 𝔥 ε (x + y) - ‖D (x + y)‖ ^ 2)
          (probeForm 𝔥 ε x - ‖D x‖ ^ 2)
        linarith
    _ ≤ _ := by linarith [hx, hy, hxy]

/-- **(NL.8)**: `𝕀_ε(x,y) → ⟪Dx, Dy⟫` as `ε → 0⁺` under uniform Taylor control. -/
theorem polarized_localizer_tendsto (𝔥 : U → F) (D : U →L[ℝ] F) (M L : ℝ)
    (x y : U) (hL : ∀ u, ‖D u‖ ≤ L * ‖u‖)
    (htaylor : ∀ ε > (0 : ℝ), ∀ u, ‖𝔥 (ε • u) - 𝔥 0 - ε • D u‖ ≤ M * ε ^ 2 * ‖u‖ ^ 2 / 2) :
    Tendsto (fun ε => probeLocalizer 𝔥 ε x y) (𝓝[>] 0) (𝓝 (inner ℝ (D x) (D y))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  -- the bound is a polynomial in `ε` vanishing at `0`
  set B : ℝ → ℝ := fun ε => (1 / 2) * ((M * L * ε * ‖x‖ ^ 3 + M ^ 2 * ε ^ 2 * ‖x‖ ^ 4 / 4)
    + (M * L * ε * ‖y‖ ^ 3 + M ^ 2 * ε ^ 2 * ‖y‖ ^ 4 / 4)
    + (M * L * ε * ‖x + y‖ ^ 3 + M ^ 2 * ε ^ 2 * ‖x + y‖ ^ 4 / 4)) with hB
  have hBcont : Continuous B := by fun_prop
  have hB0 : B 0 = 0 := by simp [hB]
  have hlim : Tendsto B (𝓝 0) (𝓝 0) := by
    simpa [hB0] using hBcont.tendsto 0
  rw [Metric.tendsto_nhds] at hlim
  obtain ⟨η, hη, hηB⟩ := Metric.eventually_nhds_iff.mp (hlim δ hδ)
  refine ⟨η, hη, fun ε hε0 hεη => ?_⟩
  have hεpos : 0 < ε := hε0
  have hb := polarized_localizer_bound 𝔥 D M L ε hεpos x y hL (htaylor ε hεpos)
  rw [Real.dist_eq]
  have hBε := hηB hεη
  rw [dist_zero_right, Real.norm_eq_abs] at hBε
  calc |probeLocalizer 𝔥 ε x y - inner ℝ (D x) (D y)| ≤ B ε := hb
    _ ≤ |B ε| := le_abs_self _
    _ < δ := hBε

end Probe

end ScorePressure
end NCG
