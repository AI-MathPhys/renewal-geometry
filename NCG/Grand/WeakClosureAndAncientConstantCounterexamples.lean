/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Weak closure and ancient constant counterexamples

The oscillatory sequence used to separate weak closure from strong residual
control, and the constant-field core of the ancient Navier--Stokes
nontriviality counterexample.
-/

open Filter Topology MeasureTheory
open scoped Interval

namespace NCG
namespace WeakClosureAndAncientConstantCounterexamples

noncomputable def oscillatoryWeakSequence (N : ℕ) (t : ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * Real.sin ((((N + 1 : ℕ) : ℝ) ^ 2) * t)

/-- The exact differential residual of the oscillatory sequence. -/
noncomputable def oscillatoryWeakDerivative (N : ℕ) (t : ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) *
    Real.cos ((((N + 1 : ℕ) : ℝ) ^ 2) * t)

/-- Uniform-amplitude estimate for u_N. -/
theorem oscillatoryWeakSequence_abs_le (N : ℕ) (t : ℝ) :
    |oscillatoryWeakSequence N t| ≤ (((N + 1 : ℕ) : ℝ))⁻¹ := by
  rw [oscillatoryWeakSequence, abs_mul, abs_inv,
    abs_of_nonneg (Nat.cast_nonneg (N + 1))]
  calc
    (↑(N + 1))⁻¹ * |Real.sin (↑(N + 1) ^ 2 * t)|
        ≤ (↑(N + 1))⁻¹ * 1 := by
          exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
    _ = (↑(N + 1))⁻¹ := mul_one _

/-- The uniform amplitude tends to zero. -/
theorem oscillatoryWeakSequence_uniformly_to_zero :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
  have htop : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp htop
  simpa only [Nat.cast_add, Nat.cast_one] using hinv

/-- Exact derivative `u_N'= (N+1) cos((N+1)^2 t)`. -/
theorem oscillatoryWeakSequence_hasDerivAt (N : ℕ) (t : ℝ) :
    HasDerivAt (oscillatoryWeakSequence N)
      (oscillatoryWeakDerivative N t) t := by
  let a : ℝ := ((N + 1 : ℕ) : ℝ)
  have ha : a ≠ 0 := by positivity
  have hinner : HasDerivAt (fun s : ℝ => a ^ 2 * s) (a ^ 2) t := by
    simpa using (hasDerivAt_id t).const_mul (a ^ 2)
  have hsin := hinner.sin.const_mul a⁻¹
  have hcoef : a⁻¹ * (Real.cos (a ^ 2 * t) * a ^ 2) =
      a * Real.cos (a ^ 2 * t) := by
    field_simp [ha]
  rw [hcoef] at hsin
  change HasDerivAt (fun y : ℝ => a⁻¹ * Real.sin (a ^ 2 * y))
    (a * Real.cos (a ^ 2 * t)) t
  exact hsin

/-- On the fixed interval `[0,1]`, the `L¹` differential defect grows at
least linearly.  The proof avoids integrating `|cos|` explicitly: pointwise
`cos² ≤ |cos|`, while the exact cosine-square integral has mean at least
`1/4` at every frequency `(N+1)²`. -/
theorem oscillatoryWeakDerivative_L1_lower (N : ℕ) :
    (((N + 1 : ℕ) : ℝ) / 4) ≤
      ∫ t in (0 : ℝ)..1, |oscillatoryWeakDerivative N t| := by
  let a : ℝ := ((N + 1 : ℕ) : ℝ)
  let w : ℝ := a ^ 2
  have ha : 1 ≤ a := by
    dsimp [a]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hw : 1 ≤ w := by
    dsimp [w]
    nlinarith
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hsqint :
      (1 / 4 : ℝ) ≤ ∫ t in (0 : ℝ)..1, Real.cos (w * t) ^ 2 := by
    rw [intervalIntegral.integral_comp_mul_left (f := fun x : ℝ => Real.cos x ^ 2)
      hw0.ne']
    rw [integral_cos_sq]
    simp only [mul_zero, Real.cos_zero, Real.sin_zero, one_mul, zero_mul,
      sub_zero, zero_add]
    have htrig := Real.sin_sq_add_cos_sq w
    have hprod : -(1 / 2 : ℝ) ≤ Real.cos w * Real.sin w := by
      nlinarith [sq_nonneg (Real.cos w + Real.sin w)]
    simp only [mul_one, smul_eq_mul]
    have hwne : w ≠ 0 := ne_of_gt hw0
    field_simp [hwne]
    nlinarith
  have hcos_cont : Continuous fun t : ℝ => Real.cos (w * t) ^ 2 := by fun_prop
  have habs_cont : Continuous fun t : ℝ => |Real.cos (w * t)| := by fun_prop
  have hmono :
      (∫ t in (0 : ℝ)..1, Real.cos (w * t) ^ 2) ≤
        ∫ t in (0 : ℝ)..1, |Real.cos (w * t)| := by
    exact intervalIntegral.integral_mono_on (μ := volume)
      (f := fun t : ℝ => Real.cos (w * t) ^ 2)
      (g := fun t : ℝ => |Real.cos (w * t)|)
      (by norm_num) (hcos_cont.intervalIntegrable 0 1)
      (habs_cont.intervalIntegrable 0 1) (fun t _ => by
        have hc := Real.abs_cos_le_one (w * t)
        nlinarith [sq_abs (Real.cos (w * t)),
          abs_nonneg (Real.cos (w * t))])
  calc
    a / 4 ≤ a * (∫ t in (0 : ℝ)..1, Real.cos (w * t) ^ 2) := by
      nlinarith
    _ ≤ a * (∫ t in (0 : ℝ)..1, |Real.cos (w * t)|) :=
      mul_le_mul_of_nonneg_left hmono ha0
    _ = ∫ t in (0 : ℝ)..1, |oscillatoryWeakDerivative N t| := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      have habsa : |(((N + 1 : ℕ) : ℝ))| = a := by
        rw [abs_of_nonneg (Nat.cast_nonneg (N + 1))]
      simp only [oscillatoryWeakDerivative, abs_mul, habsa]
      rw [show (((N + 1 : ℕ) : ℝ) ^ 2) = w from rfl]

/-- Consequently the `L¹([0,1])` norm of the differential residual tends to
infinity. -/
theorem oscillatoryWeakDerivative_L1_tendsto_atTop :
    Tendsto
      (fun N : ℕ => ∫ t in (0 : ℝ)..1, |oscillatoryWeakDerivative N t|)
      atTop atTop := by
  have hbase :
      Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) / 4)) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num)
      (by
        simpa [Nat.cast_add, Nat.cast_one] using
          (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall oscillatoryWeakDerivative_L1_lower) hbase

/-- Distributional residual against a `C¹` test, in its canonical integrated
weak form.  For a classically differentiable path this is exactly the
integration-by-parts rendering of `∫ u' φ`. -/
noncomputable def oscillatoryWeakResidual (N : ℕ) (φ φ' : ℝ → ℝ)
    (T : ℝ) : ℝ :=
  oscillatoryWeakSequence N T * φ T -
    oscillatoryWeakSequence N 0 * φ 0 -
      ∫ t in (0 : ℝ)..T, φ' t * oscillatoryWeakSequence N t

/-- Quantitative weak-residual estimate obtained from the uniform amplitude
and the interval-integral norm bound. -/
theorem oscillatoryWeakResidual_abs_le
    (N : ℕ) (T C : ℝ) (hC : 0 ≤ C) (φ φ' : ℝ → ℝ)
    (hbound : ∀ t ∈ Ι (0 : ℝ) T, |φ' t| ≤ C) :
    |oscillatoryWeakResidual N φ φ' T| ≤
      (((N + 1 : ℕ) : ℝ))⁻¹ * (|φ T| + |φ 0| + C * |T|) := by
  have hint :
      |∫ t in (0 : ℝ)..T, φ' t * oscillatoryWeakSequence N t| ≤
        (((N + 1 : ℕ) : ℝ))⁻¹ * C * |T| := by
    have hpoint : ∀ t ∈ Ι (0 : ℝ) T,
        |φ' t * oscillatoryWeakSequence N t| ≤
          (((N + 1 : ℕ) : ℝ))⁻¹ * C := by
      intro t ht
      rw [abs_mul]
      calc
        |φ' t| * |oscillatoryWeakSequence N t| ≤
            C * (((N + 1 : ℕ) : ℝ))⁻¹ :=
          mul_le_mul (hbound t ht) (oscillatoryWeakSequence_abs_le N t)
            (abs_nonneg _) hC
        _ = (((N + 1 : ℕ) : ℝ))⁻¹ * C := mul_comm _ _
    simpa only [Real.norm_eq_abs, sub_zero] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := T)
        (C := (((N + 1 : ℕ) : ℝ))⁻¹ * C)
        (f := fun t => φ' t * oscillatoryWeakSequence N t) hpoint)
  have hT := mul_le_mul_of_nonneg_right
    (oscillatoryWeakSequence_abs_le N T) (abs_nonneg (φ T))
  have h0 := mul_le_mul_of_nonneg_right
    (oscillatoryWeakSequence_abs_le N 0) (abs_nonneg (φ 0))
  rw [oscillatoryWeakResidual]
  calc
    |oscillatoryWeakSequence N T * φ T -
        oscillatoryWeakSequence N 0 * φ 0 -
        ∫ t in (0 : ℝ)..T, φ' t * oscillatoryWeakSequence N t| ≤
      |oscillatoryWeakSequence N T * φ T| +
        |oscillatoryWeakSequence N 0 * φ 0| +
        |∫ t in (0 : ℝ)..T, φ' t * oscillatoryWeakSequence N t| := by
          refine (abs_sub _ _).trans ?_
          simpa only [add_assoc, add_comm, add_left_comm] using
            (add_le_add_right
              (abs_sub (oscillatoryWeakSequence N T * φ T)
                (oscillatoryWeakSequence N 0 * φ 0))
              |∫ t in (0 : ℝ)..T, φ' t * oscillatoryWeakSequence N t|)
    _ ≤ (((N + 1 : ℕ) : ℝ))⁻¹ * |φ T| +
        (((N + 1 : ℕ) : ℝ))⁻¹ * |φ 0| +
        (((N + 1 : ℕ) : ℝ))⁻¹ * C * |T| := by
          rw [abs_mul, abs_mul]
          exact add_le_add (add_le_add hT h0) hint
    _ = (((N + 1 : ℕ) : ℝ))⁻¹ * (|φ T| + |φ 0| + C * |T|) := by ring

/-- A reusable scalar squeeze for inverse-successor bounds. -/
theorem tendsto_zero_of_abs_le_inverseSucc (f : ℕ → ℝ) (K : ℝ)
    (h : ∀ N, |f N| ≤ (((N + 1 : ℕ) : ℝ))⁻¹ * K) :
    Tendsto f atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun N => abs_nonneg (f N))
    (Filter.Eventually.of_forall h)
    (by simpa using oscillatoryWeakSequence_uniformly_to_zero.mul_const K)

/-- Against every `C¹` test with bounded derivative on `[0,T]`, the integrated
weak residual tends to zero. -/
theorem oscillatoryWeakResidual_tendsto_zero
    (T C : ℝ) (hC : 0 ≤ C) (φ φ' : ℝ → ℝ)
    (hbound : ∀ t ∈ Ι (0 : ℝ) T, |φ' t| ≤ C) :
    Tendsto (fun N : ℕ => oscillatoryWeakResidual N φ φ' T) atTop (nhds 0) :=
  tendsto_zero_of_abs_le_inverseSucc _ _ fun N =>
    oscillatoryWeakResidual_abs_le N T C hC φ φ' hbound

/-- A continuous test derivative is bounded on the compact unoriented
interval between `0` and `T`. -/
theorem continuous_test_derivative_bounded (T : ℝ) (φ' : ℝ → ℝ)
    (hφ' : Continuous φ') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ι (0 : ℝ) T, |φ' t| ≤ C := by
  have hb : BddAbove ((fun t : ℝ => |φ' t|) '' Set.uIcc (0 : ℝ) T) :=
    isCompact_uIcc.bddAbove_image hφ'.abs.continuousOn
  rcases hb with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hC ⟨t, Set.uIoc_subset_uIcc ht, rfl⟩).trans (le_max_left _ _)

/-- Weak residual convergence for every `C¹` test, represented by its
continuous derivative. -/
theorem oscillatoryWeakResidual_tendsto_zero_for_continuous_test_derivative
    (T : ℝ) (φ φ' : ℝ → ℝ) (hφ' : Continuous φ') :
    Tendsto (fun N : ℕ => oscillatoryWeakResidual N φ φ' T) atTop (nhds 0) := by
  rcases continuous_test_derivative_bounded T φ' hφ' with ⟨C, hC, hbound⟩
  exact oscillatoryWeakResidual_tendsto_zero T C hC φ φ' hbound

/-- At the origin the derivative magnitude is exactly N+1, so the strong
differential defect is unbounded even though the functions converge uniformly. -/
theorem oscillatoryWeakSequence_derivative_at_zero (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) *
      Real.cos ((((N + 1 : ℕ) : ℝ) ^ 2) * 0) = (N + 1 : ℕ) := by
  simp

/-- The displayed strong derivative witness tends to infinity. -/
theorem oscillatoryWeakSequence_strong_defect_unbounded :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
  simpa [Nat.cast_add, Nat.cast_one] using
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- Exact counterexample package: the paths converge uniformly to zero and
their residuals vanish against every `C¹` test, while their strong `L¹`
differential defects diverge.  Thus a strong defect estimate is sufficient
for weak closure but is not necessary. -/
theorem strong_defect_not_necessary :
    (∀ N t, |oscillatoryWeakSequence N t| ≤ (((N + 1 : ℕ) : ℝ))⁻¹) ∧
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) ∧
    (∀ T φ φ', Continuous φ' →
      Tendsto (fun N : ℕ => oscillatoryWeakResidual N φ φ' T)
        atTop (nhds 0)) ∧
    Tendsto
      (fun N : ℕ => ∫ t in (0 : ℝ)..1, |oscillatoryWeakDerivative N t|)
      atTop atTop := by
  exact ⟨oscillatoryWeakSequence_abs_le,
    oscillatoryWeakSequence_uniformly_to_zero,
    fun T φ φ' hφ' =>
      oscillatoryWeakResidual_tendsto_zero_for_continuous_test_derivative
        T φ φ' hφ',
    oscillatoryWeakDerivative_L1_tendsto_atTop⟩

/-- A nonzero constant vector has positive cubic mass density and zero spatial
derivative; these are the two decisive facts in `cth:NS-ancient-nontrivial`. -/
theorem nonzero_constant_ancient_core {d : Type*} [Fintype d]
    (c : EuclideanSpace ℝ d) (hc : c ≠ 0) :
    0 < ‖c‖ ^ 3
      ∧ (∀ x : EuclideanSpace ℝ d,
        HasFDerivAt (fun _ : EuclideanSpace ℝ d => c)
          (0 : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) x) := by
  constructor
  · positivity
  · intro x
    exact hasFDerivAt_const c x

end WeakClosureAndAncientConstantCounterexamples
end NCG
