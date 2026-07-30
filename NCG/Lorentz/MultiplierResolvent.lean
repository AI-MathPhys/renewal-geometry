/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Strong resolvent convergence of multiplication operators on L²

The **L² instantiation** of the common-core strong-resolvent
criterion (`lem:app-core-resolvent`, `thm:flat-limit`(iv)) in the
multiplication-operator model.  On the Fourier side, the flat renewal
Hamiltonians act as multiplication by the (matrix) symbol fields
`hₙ(ξ), h(ξ)`, and their resolvents as multiplication by the bounded
fields `rₙ(ξ) = (hₙ(ξ) − z)⁻¹, r(ξ) = (h(ξ) − z)⁻¹`.  Strong
resolvent convergence on L² is then a dominated-convergence theorem,
proved here over an arbitrary measure:

* `aestronglyMeasurable_clm_apply` / `memLp_clm_apply` — a bounded
  measurable operator field maps L² to L²;
* `multiplier_tendsto_eLpNorm` — **strong L² convergence**: if the
  fields are uniformly bounded and converge pointwise a.e. on the
  orbit of `u ∈ L²`, then `‖(mₙ − m) u‖_{L²} → 0`;
* `tendsto_ring_inverse` — inversion is continuous at units, so
  pointwise symbol convergence `hₙ(ξ) → h(ξ)` gives pointwise
  resolvent convergence `rₙ(ξ) → r(ξ)`;
* `multiplier_resolvent_tendsto` — the packaged instantiation:
  uniformly bounded resolvent fields converging pointwise in
  operator norm converge strongly on L², for every `u ∈ L²`.

For self-adjoint symbols the uniform bound is `M = |Im z|⁻¹` and the
pointwise operator-norm convergence follows from
`tendsto_ring_inverse`; the pointwise identities
`rₙ(ξ)(hₙ(ξ) − z) = 1` are the caller's finite-dimensional matrix
facts.  This realizes the strong-resolvent clause of
`lem:app-core-resolvent` on a concrete L² space with no unbounded
operator theory: the unbounded Hamiltonian never appears, only its
bounded resolvent fields.
-/

namespace NCG

open Filter MeasureTheory ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ## Bounded operator fields on L² -/

/-- Applying a measurable operator field to a measurable vector field
is measurable. -/
theorem aestronglyMeasurable_clm_apply
    {m : X → E →L[𝕜] E} {u : X → E}
    (hm : AEStronglyMeasurable m μ)
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x => m x (u x)) μ :=
  (isBoundedBilinearMap_apply (𝕜 := 𝕜) (E := E)
    (F := E)).continuous.comp_aestronglyMeasurable (hm.prodMk hu)

/-- A bounded measurable operator field maps `L²` to `L²`. -/
theorem memLp_clm_apply {m : X → E →L[𝕜] E} {u : X → E} {M : ℝ}
    (hm : AEStronglyMeasurable m μ)
    (hbound : ∀ᵐ x ∂μ, ‖m x‖ ≤ M) (hu : MemLp u 2 μ) :
    MemLp (fun x => m x (u x)) 2 μ :=
  hu.of_le_mul (aestronglyMeasurable_clm_apply hm hu.1)
    (hbound.mono fun x hx =>
      le_trans ((m x).le_opNorm (u x))
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))

/-! ## Strong L² convergence by dominated convergence -/

/-- **Multiplier strong convergence on L²**
(`lem:app-core-resolvent` instantiated): uniformly bounded operator
fields converging pointwise a.e. on the orbit of `u ∈ L²` converge
strongly, `‖(mₙ − m)u‖_{L²} → 0`.  This is the dominated-convergence
mechanism behind strong resolvent convergence of the flat renewal
Hamiltonians in the multiplication (Fourier) picture. -/
theorem multiplier_tendsto_eLpNorm
    {mn : ℕ → X → E →L[𝕜] E} {m : X → E →L[𝕜] E} {u : X → E}
    {M : ℝ} (hM0 : 0 ≤ M)
    (hmn : ∀ n, AEStronglyMeasurable (mn n) μ)
    (hm : AEStronglyMeasurable m μ)
    (hbn : ∀ n, ∀ᵐ x ∂μ, ‖mn n x‖ ≤ M)
    (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ M)
    (hu : MemLp u 2 μ)
    (hconv : ∀ᵐ x ∂μ,
      Tendsto (fun n => mn n x (u x)) atTop (nhds (m x (u x)))) :
    Tendsto (fun n =>
        eLpNorm (fun x => mn n x (u x) - m x (u x)) 2 μ)
      atTop (nhds 0) := by
  have hDmeas : ∀ n, AEStronglyMeasurable
      (fun x => mn n x (u x) - m x (u x)) μ := fun n =>
    (aestronglyMeasurable_clm_apply (hmn n) hu.1).sub
      (aestronglyMeasurable_clm_apply hm hu.1)
  have hFmeas : ∀ n, AEMeasurable
      (fun x => ‖mn n x (u x) - m x (u x)‖ₑ ^ (2 : ℕ)) μ := fun n =>
    ((hDmeas n).enorm).pow_const 2
  -- domination
  have h_bound : ∀ n,
      (fun x => ‖mn n x (u x) - m x (u x)‖ₑ ^ (2 : ℕ))
        ≤ᵐ[μ] fun x =>
          (ENNReal.ofReal (2 * M)) ^ (2 : ℕ) * ‖u x‖ₑ ^ (2 : ℕ) := by
    intro n
    filter_upwards [hbn n, hb] with x hxn hx
    have h1 : ‖mn n x (u x) - m x (u x)‖ ≤ 2 * M * ‖u x‖ := by
      calc ‖mn n x (u x) - m x (u x)‖
          ≤ ‖mn n x (u x)‖ + ‖m x (u x)‖ := norm_sub_le _ _
        _ ≤ M * ‖u x‖ + M * ‖u x‖ := by
            have ha := le_trans ((mn n x).le_opNorm (u x))
              (mul_le_mul_of_nonneg_right hxn (norm_nonneg _))
            have hbx := le_trans ((m x).le_opNorm (u x))
              (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            linarith
        _ = 2 * M * ‖u x‖ := by ring
    have h2 : ‖mn n x (u x) - m x (u x)‖ₑ
        ≤ ENNReal.ofReal (2 * M) * ‖u x‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal h1
    calc ‖mn n x (u x) - m x (u x)‖ₑ ^ (2 : ℕ)
        ≤ (ENNReal.ofReal (2 * M) * ‖u x‖ₑ) ^ (2 : ℕ) :=
          pow_le_pow_left' h2 2
      _ = (ENNReal.ofReal (2 * M)) ^ (2 : ℕ) * ‖u x‖ₑ ^ (2 : ℕ) :=
          mul_pow _ _ 2
  -- integrability of the dominating function from `u ∈ L²`
  have husq : (∫⁻ x, ‖u x‖ₑ ^ (2 : ℕ) ∂μ) ≠ ∞ := by
    have h1 := hu.2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero
      ofNat_ne_top] at h1
    intro hcon
    have h2 : (∫⁻ x, ‖u x‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂μ) = ∞ := by
      rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by simp]
      simpa [ENNReal.rpow_natCast] using hcon
    rw [h2] at h1
    have h3 : (∞ : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞).toReal) = ∞ := by
      refine ENNReal.top_rpow_of_pos ?_
      simp
    rw [h3] at h1
    exact absurd h1 (lt_irrefl _)
  have h_fin : (∫⁻ x,
      (ENNReal.ofReal (2 * M)) ^ (2 : ℕ) * ‖u x‖ₑ ^ (2 : ℕ) ∂μ)
      ≠ ∞ := by
    rw [lintegral_const_mul'' _ (hu.1.enorm.pow_const 2)]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) husq
  -- pointwise convergence of the squared norms to zero
  have h_lim : ∀ᵐ x ∂μ, Tendsto
      (fun n => ‖mn n x (u x) - m x (u x)‖ₑ ^ (2 : ℕ))
      atTop (nhds 0) := by
    filter_upwards [hconv] with x hx
    have h0 : Tendsto (fun n => mn n x (u x) - m x (u x))
        atTop (nhds 0) := by
      have h0' := hx.sub (tendsto_const_nhds (x := (m x) (u x)))
      rwa [sub_self] at h0'
    have h1 : Tendsto (fun n => ‖mn n x (u x) - m x (u x)‖ₑ)
        atTop (nhds 0) := by
      have h1' : Tendsto (fun n => ‖mn n x (u x) - m x (u x)‖ₑ)
          atTop (nhds (‖(0 : E)‖ₑ)) :=
        (continuous_enorm.tendsto (0 : E)).comp h0
      simpa using h1'
    have h2 : Tendsto
        (fun n => ‖mn n x (u x) - m x (u x)‖ₑ ^ (2 : ℕ))
        atTop (nhds ((0 : ℝ≥0∞) ^ (2 : ℕ))) :=
      ((ENNReal.continuous_pow 2).tendsto 0).comp h1
    simpa using h2
  -- lintegral dominated convergence
  have hI : Tendsto (fun n => ∫⁻ x,
      ‖mn n x (u x) - m x (u x)‖ₑ ^ (2 : ℕ) ∂μ) atTop (nhds 0) := by
    have := tendsto_lintegral_of_dominated_convergence'
      (fun x => (ENNReal.ofReal (2 * M)) ^ (2 : ℕ)
        * ‖u x‖ₑ ^ (2 : ℕ))
      hFmeas h_bound h_fin h_lim
    simpa using this
  -- convert to the L² seminorm via the `1/2`-power
  have hEq : ∀ n, eLpNorm
      (fun x => mn n x (u x) - m x (u x)) 2 μ
      = (∫⁻ x, ‖mn n x (u x) - m x (u x)‖ₑ ^ (2 : ℕ) ∂μ)
          ^ (1 / 2 : ℝ) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero
      ofNat_ne_top]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by simp,
      ENNReal.rpow_natCast]
  have hzero : ((0 : ℝ≥0∞)) ^ (1 / 2 : ℝ) = 0 :=
    ENNReal.zero_rpow_of_pos (by norm_num)
  have hfinal : Tendsto (fun n =>
      (∫⁻ x, ‖mn n x (u x) - m x (u x)‖ₑ ^ (2 : ℕ) ∂μ)
        ^ (1 / 2 : ℝ)) atTop
      (nhds (((0 : ℝ≥0∞)) ^ (1 / 2 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp hI
  rw [hzero] at hfinal
  rw [show (fun n => eLpNorm
        (fun x => mn n x (u x) - m x (u x)) 2 μ)
      = fun n => (∫⁻ x,
          ‖mn n x (u x) - m x (u x)‖ₑ ^ (2 : ℕ) ∂μ)
            ^ (1 / 2 : ℝ) from funext hEq]
  exact hfinal

/-! ## Pointwise resolvent convergence from symbol convergence -/

/-- Inversion is continuous at units: pointwise symbol convergence
gives pointwise resolvent convergence. -/
theorem tendsto_ring_inverse {A : Type*} [NormedRing A]
    [CompleteSpace A] {an : ℕ → A} {a : A} (ha : IsUnit a)
    (h : Tendsto an atTop (nhds a)) :
    Tendsto (fun n => Ring.inverse (an n)) atTop
      (nhds (Ring.inverse a)) := by
  have hc : ContinuousAt Ring.inverse a := by
    have := NormedRing.inverse_continuousAt ha.unit
    rwa [IsUnit.unit_spec] at this
  exact hc.tendsto.comp h

/-- **L² strong resolvent convergence in the multiplication model**
(`thm:flat-limit`(iv) realized): uniformly bounded resolvent fields
converging pointwise a.e. in operator norm converge strongly on L²:
for every `u ∈ L²`, `‖(rₙ − r)u‖_{L²} → 0`.  For self-adjoint
symbols the bound is `M = |Im z|⁻¹`, and the pointwise convergence
is supplied by `tendsto_ring_inverse` from the symbol convergence
`hₙ(ξ) → h(ξ)`. -/
theorem multiplier_resolvent_tendsto
    {rn : ℕ → X → E →L[𝕜] E} {r : X → E →L[𝕜] E} {u : X → E}
    {M : ℝ} (hM0 : 0 ≤ M)
    (hrn : ∀ n, AEStronglyMeasurable (rn n) μ)
    (hr : AEStronglyMeasurable r μ)
    (hbn : ∀ n, ∀ᵐ x ∂μ, ‖rn n x‖ ≤ M)
    (hb : ∀ᵐ x ∂μ, ‖r x‖ ≤ M)
    (hu : MemLp u 2 μ)
    (hconv : ∀ᵐ x ∂μ,
      Tendsto (fun n => rn n x) atTop (nhds (r x))) :
    Tendsto (fun n =>
        eLpNorm (fun x => rn n x (u x) - r x (u x)) 2 μ)
      atTop (nhds 0) := by
  refine multiplier_tendsto_eLpNorm hM0 hrn hr hbn hb hu ?_
  filter_upwards [hconv] with x hx
  exact ((ContinuousLinearMap.apply 𝕜 E (u x)).continuous.tendsto
    (r x)).comp hx

end NCG
