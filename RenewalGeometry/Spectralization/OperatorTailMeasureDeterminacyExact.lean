/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.OperatorTailMeasureScalarizationExact
/-!
# Determinacy of positive operator-valued tail measures by their moments

This file proves `thm:supp-memory-determinacy` of `papers/predictive_spectral_geometry`
(Determinacy on controlled support) for the positive operator-valued tail measures of
`def:supp-POVM` (`PositiveTailMeasure`):

* if `μ` and `μ'` are supported in `(0, R]` and have the same moments
  `M_n = ∫ λⁿ dμ(λ)` for every `n`, then `μ = μ'`
  (`PositiveTailMeasure.eq_of_isSupportedIn_of_moment_eq`);
* the same conclusion holds on unbounded support under the exponential-moment condition
  `∫ e^{aλ} d Tr μ(λ) < ∞` for some `a > 0`
  (`PositiveTailMeasure.eq_of_integrable_exp_traceMeasure_of_moment_eq`);
* both clauses are packaged in `PositiveTailMeasure.memory_determinacy`.

The scalar core is `measure_eq_of_forall_integral_pow_eq`: two finite measures on `[0, ∞)`
with an exponential moment and equal integer moments coincide.  Its proof goes through the
complex moment generating function `complexMGF id ν`, which is analytic on the half-plane
`Re z < a` (Mathlib's `analyticOnNhd_complexMGF`), has the moments as Taylor coefficients at
the origin (`iteratedDeriv_complexMGF`), hence agrees for `ν` and `ν'` near `0` and, by the
identity theorem, on the whole half-plane; on the imaginary axis this is the characteristic
function, which determines the measure (`Measure.ext_of_charFun`).  The compact case follows
because a measure supported in `(0, R]` has all exponential moments.  The operator statement
is obtained by scalarising along the quadratic forms `ξ ↦ ⟨ξ, μ(·) ξ⟩` (file
`OperatorTailMeasureScalarizationExact`) and polarising: a matrix with vanishing quadratic
form is zero.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ComplexOrder ENNReal Matrix InnerProductSpace

namespace RenewalGeometry
namespace OperatorTailMeasure

/-! ## Scalar moment determinacy under an exponential moment -/

section Scalar

variable {ν ν' : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']

/-- For a finite measure on `[0, ∞)` with `∫ e^{a x} dν < ∞`, `e^{t x}` is integrable for every
`t ≤ a`. -/
theorem mem_integrableExpSet_of_le (hν0 : ν (Iio 0) = 0) {a : ℝ}
    (hν : Integrable (fun x => Real.exp (a * x)) ν) {t : ℝ} (ht : t ≤ a) :
    t ∈ integrableExpSet id ν := by
  show Integrable (fun x => Real.exp (t * id x)) ν
  simp only [id]
  rcases le_or_gt 0 t with h0 | h0
  · exact integrable_exp_mul_of_nonneg_of_le hν h0 ht
  · have hmem : ∀ᵐ x ∂ν, 0 ≤ x := by
      rw [ae_iff]
      exact measure_mono_null (fun x hx => not_le.mp hx) hν0
    refine Integrable.of_mem_Icc 0 1 (by fun_prop) ?_
    filter_upwards [hmem] with x hx
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg h0.le hx)⟩

/-- The open half-line `(-∞, a)` lies in the interior of the integrability set. -/
theorem Iio_subset_interior_integrableExpSet (hν0 : ν (Iio 0) = 0) {a : ℝ}
    (hν : Integrable (fun x => Real.exp (a * x)) ν) :
    Iio a ⊆ interior (integrableExpSet id ν) := by
  rw [← interior_Iic]
  exact interior_mono fun t ht => mem_integrableExpSet_of_le hν0 hν ht

/-- **Scalar moment determinacy.**  Two finite measures on `[0, ∞)` with an exponential moment
`∫ e^{a x} < ∞` (`a > 0`) and equal integer moments coincide. -/
theorem measure_eq_of_forall_integral_pow_eq (hν0 : ν (Iio 0) = 0) (hν'0 : ν' (Iio 0) = 0)
    {a : ℝ} (ha : 0 < a) (hν : Integrable (fun x => Real.exp (a * x)) ν)
    (hν' : Integrable (fun x => Real.exp (a * x)) ν')
    (h : ∀ n : ℕ, ∫ x, x ^ n ∂ν = ∫ x, x ^ n ∂ν') : ν = ν' := by
  set U : Set ℂ := {z | z.re < a} with hUdef
  have hU : IsPreconnected U := by
    have : U = Complex.reLm ⁻¹' Iio a := by
      ext z
      simp [hUdef]
    rw [this]
    exact ((convex_Iio a).linear_preimage Complex.reLm).isPreconnected
  have hF : AnalyticOnNhd ℂ (complexMGF id ν) U :=
    analyticOnNhd_complexMGF.mono fun z hz => Iio_subset_interior_integrableExpSet hν0 hν hz
  have hG : AnalyticOnNhd ℂ (complexMGF id ν') U :=
    analyticOnNhd_complexMGF.mono fun z hz => Iio_subset_interior_integrableExpSet hν'0 hν' hz
  have h0U : (0 : ℂ) ∈ U := by simpa [hUdef] using ha
  have h0ν : (0 : ℂ).re ∈ interior (integrableExpSet id ν) :=
    Iio_subset_interior_integrableExpSet hν0 hν (by simpa using ha)
  have h0ν' : (0 : ℂ).re ∈ interior (integrableExpSet id ν') :=
    Iio_subset_interior_integrableExpSet hν'0 hν' (by simpa using ha)
  -- the Taylor coefficients at the origin are the moments
  have hD : ∀ n, iteratedDeriv n (complexMGF id ν) 0 = iteratedDeriv n (complexMGF id ν') 0 := by
    intro n
    rw [iteratedDeriv_complexMGF h0ν n, iteratedDeriv_complexMGF h0ν' n]
    simp only [id, zero_mul, Complex.exp_zero, mul_one]
    simp_rw [← Complex.ofReal_pow]
    rw [integral_complex_ofReal (f := fun x : ℝ => x ^ n),
      integral_complex_ofReal (f := fun x : ℝ => x ^ n), h n]
  -- hence the moment generating functions agree near the origin
  have hfg : complexMGF id ν =ᶠ[𝓝 0] complexMGF id ν' := by
    have hA : AnalyticAt ℂ (complexMGF id ν - complexMGF id ν') 0 := (hF 0 h0U).sub (hG 0 h0U)
    have hzero : ∀ n, iteratedDeriv n (complexMGF id ν - complexMGF id ν') 0 = 0 := by
      intro n
      rw [iteratedDeriv_sub (hF 0 h0U).contDiffAt (hG 0 h0U).contDiffAt, hD n, sub_self]
    have htop : analyticOrderAt (complexMGF id ν - complexMGF id ν') 0 = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro m
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).2 fun i _ => hzero i
    have hev := analyticOrderAt_eq_top.mp htop
    filter_upwards [hev] with z hz
    exact sub_eq_zero.mp hz
  -- identity theorem on the half-plane
  have hEq : EqOn (complexMGF id ν) (complexMGF id ν') U :=
    hF.eqOn_of_preconnected_of_eventuallyEq hG hU h0U hfg
  -- the characteristic functions agree
  refine Measure.ext_of_charFun ?_
  funext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact hEq (by simpa [hUdef] using ha)

/-- **Scalar moment determinacy on compact support.**  Two finite measures supported in
`(0, R]` with equal integer moments coincide. -/
theorem measure_eq_of_forall_integral_pow_eq_of_compact {R : ℝ} (hν : ν (Ioc 0 R)ᶜ = 0)
    (hν' : ν' (Ioc 0 R)ᶜ = 0) (h : ∀ n : ℕ, ∫ x, x ^ n ∂ν = ∫ x, x ^ n ∂ν') : ν = ν' := by
  have hIio : ∀ {m : Measure ℝ}, m (Ioc 0 R)ᶜ = 0 → m (Iio 0) = 0 := fun hm =>
    measure_mono_null
      (fun x (hx : x ∈ Iio 0) => (Set.mem_compl_iff (Ioc 0 R) x).2
        fun hx' => absurd hx'.1 (not_lt.mpr (le_of_lt hx))) hm
  have hexp : ∀ {m : Measure ℝ} [IsFiniteMeasure m], m (Ioc 0 R)ᶜ = 0 →
      Integrable (fun x => Real.exp (1 * x)) m := by
    intro m _ hm
    have := integrable_exp_mul_of_le (μ := m) (X := id) 1 R zero_le_one aemeasurable_id
      (by
        rw [ae_iff]
        exact measure_mono_null
          (fun x (hx : ¬ id x ≤ R) => (Set.mem_compl_iff (Ioc 0 R) x).2 fun hx' => hx hx'.2) hm)
    simpa using this
  exact measure_eq_of_forall_integral_pow_eq (hIio hν) (hIio hν') one_pos (hexp hν) (hexp hν') h

end Scalar

/-! ## Polarisation: a matrix with vanishing quadratic form is zero -/

variable {H : Type*} [Fintype H] [DecidableEq H]

theorem quadForm_sub (ξ : H → ℂ) (M N : Matrix H H ℂ) :
    quadForm ξ (M - N) = quadForm ξ M - quadForm ξ N := by
  simp [quadForm, Matrix.sub_mulVec, dotProduct_sub]

/-- A complex matrix whose quadratic form vanishes identically is zero. -/
theorem matrix_eq_zero_of_forall_quadForm_eq_zero {N : Matrix H H ℂ}
    (h : ∀ ξ : H → ℂ, quadForm ξ N = 0) : N = 0 := by
  have hT : ∀ x : EuclideanSpace ℂ H, ⟪Matrix.toEuclideanLin N x, x⟫_ℂ = 0 := by
    intro x
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change WithLp.ofLp x ⬝ᵥ star (N *ᵥ WithLp.ofLp x) = 0
    rw [Matrix.dotProduct_star, dotProduct_comm]
    have := h (WithLp.ofLp x)
    rw [quadForm] at this
    rw [this, star_zero]
  have hzero : Matrix.toEuclideanLin N = 0 := (inner_map_self_eq_zero _).mp hT
  exact (LinearEquiv.map_eq_zero_iff _).mp hzero

namespace PositiveTailMeasure

variable (μ μ' : PositiveTailMeasure H)

/-- Positive tail measures are determined by their underlying vector measures. -/
theorem ext_iff' : μ = μ' ↔ μ.toVectorMeasure = μ'.toVectorMeasure := by
  constructor
  · rintro rfl
    rfl
  · intro h
    cases μ
    cases μ'
    congr

/-- **Polarisation.**  Two positive tail measures with the same scalarisations
`Re ⟨ξ, μ(E) ξ⟩` for every `ξ` and every Borel `E` coincide. -/
theorem toVectorMeasure_eq_of_forall_quadFormCLM_eq
    (h : ∀ (ξ : H → ℂ) (s : Set ℝ), MeasurableSet s →
      quadFormCLM ξ (μ.toVectorMeasure s) = quadFormCLM ξ (μ'.toVectorMeasure s)) :
    μ.toVectorMeasure = μ'.toVectorMeasure := by
  refine VectorMeasure.ext fun s hs => ?_
  have hq : ∀ ξ : H → ℂ,
      quadForm ξ (Matrix.of (μ.toVectorMeasure s) - Matrix.of (μ'.toVectorMeasure s)) = 0 := by
    intro ξ
    rw [quadForm_sub]
    apply Complex.ext
    · have := h ξ s hs
      simp only [quadFormCLM_apply] at this
      simp only [Complex.sub_re, Complex.zero_re, this, sub_self]
    · simp only [Complex.sub_im, Complex.zero_im,
        posSemidef_im_quadForm_eq_zero (μ.posSemidef s hs) ξ,
        posSemidef_im_quadForm_eq_zero (μ'.posSemidef s hs) ξ, sub_self]
  have hN := matrix_eq_zero_of_forall_quadForm_eq_zero hq
  exact sub_eq_zero.mp hN

/-- Scalarised moments from integrability (no support assumption). -/
theorem quadFormCLM_moment_of_integrable (ξ : H → ℂ) (n : ℕ)
    (hf : Integrable (fun x : ℝ => x ^ n) μ.toVectorMeasure.variation) :
    quadFormCLM ξ (μ.moment n) = ∫ x, x ^ n ∂(μ.formMeasure ξ) := by
  change quadFormCLM ξ (VectorMeasure.integral μ.toVectorMeasure
    (fun lam : ℝ => ((lam ^ n : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ)) = _
  rw [μ.integral_ofReal_lsmul hf, μ.quadFormCLM_integral ξ hf]

/-- The scalarised measures vanish on `(-∞, 0)`. -/
theorem formMeasure_Iio (ξ : H → ℂ) : μ.formMeasure ξ (Iio 0) = 0 :=
  measure_mono_null Iio_subset_Iic_self (μ.formMeasure_Iic ξ)

/-- The trace measure vanishes on `(-∞, 0)`. -/
theorem traceMeasure_Iio : μ.traceMeasure (Iio 0) = 0 := by
  rw [traceMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i _ => μ.formMeasure_Iio _

/-- **`thm:supp-memory-determinacy`, compact clause.**  Two positive operator-valued tail
measures supported in `(0, R]` with the same moment sequence `M_n = ∫ λⁿ dμ(λ)` coincide. -/
theorem eq_of_isSupportedIn_of_moment_eq {R : ℝ} (hR : μ.IsSupportedIn R)
    (hR' : μ'.IsSupportedIn R) (h : ∀ n : ℕ, μ.moment n = μ'.moment n) : μ = μ' := by
  rw [ext_iff']
  apply toVectorMeasure_eq_of_forall_quadFormCLM_eq
  intro ξ s hs
  have hcompl : ∀ {m : PositiveTailMeasure H}, m.IsSupportedIn R →
      m.formMeasure ξ (Ioc 0 R)ᶜ = 0 := by
    intro m hm
    refine measure_mono_null (fun x hx => ?_)
      (measure_union_null (m.formMeasure_Iic ξ) (m.formMeasure_Ioi hm ξ))
    simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hx
    exact hx
  have hform : μ.formMeasure ξ = μ'.formMeasure ξ := by
    refine measure_eq_of_forall_integral_pow_eq_of_compact (hcompl hR) (hcompl hR') fun n => ?_
    rw [← μ.quadFormCLM_moment hR ξ n, ← μ'.quadFormCLM_moment hR' ξ n, h n]
  have := congrArg (fun m : Measure ℝ => m.real s) hform
  simpa only [formMeasure_real_apply μ ξ hs, formMeasure_real_apply μ' ξ hs] using this

/-- **`thm:supp-memory-determinacy`, exponential clause.**  Two positive operator-valued tail
measures with an exponential trace moment `∫ e^{aλ} d Tr μ(λ) < ∞` (`a > 0`) and the same
moment sequence coincide. -/
theorem eq_of_integrable_exp_traceMeasure_of_moment_eq {a : ℝ} (ha : 0 < a)
    (hμ : Integrable (fun x => Real.exp (a * x)) μ.traceMeasure)
    (hμ' : Integrable (fun x => Real.exp (a * x)) μ'.traceMeasure)
    (h : ∀ n : ℕ, μ.moment n = μ'.moment n) : μ = μ' := by
  rw [ext_iff']
  apply toVectorMeasure_eq_of_forall_quadFormCLM_eq
  intro ξ s hs
  -- integrability of the powers against the variation, via the trace measure
  have hpow : ∀ {m : PositiveTailMeasure H}, Integrable (fun x => Real.exp (a * x)) m.traceMeasure →
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) m.toVectorMeasure.variation := by
    intro m hm n
    have h0 : (0 : ℝ) ∈ interior (integrableExpSet id m.traceMeasure) :=
      Iio_subset_interior_integrableExpSet m.traceMeasure_Iio hm ha
    have := integrable_pow_of_mem_interior_integrableExpSet h0 n
    exact (this.mono_measure m.variation_le_traceMeasure)
  -- exponential moment of the scalarised measures
  have hexp : ∀ {m : PositiveTailMeasure H}, Integrable (fun x => Real.exp (a * x)) m.traceMeasure →
      Integrable (fun x => Real.exp (a * x)) (m.formMeasure ξ) := fun hm =>
    Integrable.of_measure_le_smul ENNReal.ofReal_ne_top (formMeasure_le_smul_traceMeasure _ ξ) hm
  have hform : μ.formMeasure ξ = μ'.formMeasure ξ := by
    refine measure_eq_of_forall_integral_pow_eq (μ.formMeasure_Iio ξ) (μ'.formMeasure_Iio ξ) ha
      (hexp hμ) (hexp hμ') fun n => ?_
    rw [← μ.quadFormCLM_moment_of_integrable ξ n (hpow hμ n),
      ← μ'.quadFormCLM_moment_of_integrable ξ n (hpow hμ' n), h n]
  have := congrArg (fun m : Measure ℝ => m.real s) hform
  simpa only [formMeasure_real_apply μ ξ hs, formMeasure_real_apply μ' ξ hs] using this

/-- **`thm:supp-memory-determinacy` (Determinacy on controlled support).**  For positive
operator-valued tail measures (`def:supp-POVM`) the complete moment sequence
`M_n = ∫ λⁿ dμ(λ)` determines `μ` uniquely when the support is compact (`μ` supported in
`(0, R]`), and likewise on unbounded support under the exponential trace moment
`∫ e^{aλ} d Tr μ(λ) < ∞` for some `a > 0`. -/
theorem memory_determinacy :
    (∀ (R : ℝ) (μ μ' : PositiveTailMeasure H), μ.IsSupportedIn R → μ'.IsSupportedIn R →
      (∀ n : ℕ, μ.moment n = μ'.moment n) → μ = μ') ∧
    (∀ (a : ℝ), 0 < a → ∀ (μ μ' : PositiveTailMeasure H),
      Integrable (fun x => Real.exp (a * x)) μ.traceMeasure →
      Integrable (fun x => Real.exp (a * x)) μ'.traceMeasure →
      (∀ n : ℕ, μ.moment n = μ'.moment n) → μ = μ') :=
  ⟨fun _ μ μ' hR hR' h => μ.eq_of_isSupportedIn_of_moment_eq μ' hR hR' h,
    fun _ ha μ μ' hμ hμ' h => μ.eq_of_integrable_exp_traceMeasure_of_moment_eq μ' ha hμ hμ' h⟩

end PositiveTailMeasure

end OperatorTailMeasure
end RenewalGeometry
