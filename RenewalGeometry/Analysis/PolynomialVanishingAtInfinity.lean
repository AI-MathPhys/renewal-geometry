/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Analysis.ResolventNeumannSeries

/-!
# Vector polynomials vanishing at infinity and resolvent limits along the real axis

Infrastructure for the Laurent-uniqueness step of `cor:supp-all-rational`
(`papers/predictive_spectral_geometry`).

* `coeff_eq_zero_of_tendsto_zero`: a vector-valued polynomial `∑_{k < n} t^k • c_k` which tends to
  `0` as `t → +∞` along the real axis has all coefficients `c_k = 0`.
* `tendsto_smul_inverse_sub_algebraMap`: for an element `A` of a complete normed `ℂ`-algebra,
  `t (A - t)⁻¹ → -1` as `t → +∞` (real `t`), and consequently `(A - t)⁻¹ → 0`
  (`tendsto_inverse_sub_algebraMap`).
-/

open Filter Topology

namespace RenewalGeometry

/-! ## Vector polynomials vanishing at infinity -/

section Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `(t : ℂ)⁻¹ → 0` as the real parameter `t → +∞`. -/
theorem tendsto_ofReal_inv_atTop : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹)) atTop (𝓝 0) := by
  have := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
  simpa [Function.comp_def, Complex.ofReal_inv] using this

/-- `((t : ℂ)⁻¹)^j → 0` for `j ≥ 1` as the real parameter `t → +∞`. -/
theorem tendsto_ofReal_inv_pow_atTop {j : ℕ} (hj : j ≠ 0) :
    Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ j) atTop (𝓝 0) := by
  simpa [zero_pow hj] using tendsto_ofReal_inv_atTop.pow j

theorem inv_pow_mul_pow_of_le {z : ℂ} (hz : z ≠ 0) {k n : ℕ} (hk : k ≤ n) :
    z⁻¹ ^ n * z ^ k = z⁻¹ ^ (n - k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, pow_add, mul_comm, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hz,
    one_pow, one_mul]

/-- **A vector polynomial vanishing at infinity is zero**: if
`∑_{k < n} t^k • c_k → 0` as the real parameter `t → +∞`, then `c_k = 0` for all `k < n`. -/
theorem coeff_eq_zero_of_tendsto_zero (n : ℕ) (c : ℕ → E)
    (h : Tendsto (fun t : ℝ => ∑ k ∈ Finset.range n, ((t : ℂ) ^ k) • c k) atTop (𝓝 0)) :
    ∀ k < n, c k = 0 := by
  induction n generalizing c with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    have hcn : c n = 0 := by
      have h1 : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ n •
          ∑ k ∈ Finset.range (n + 1), ((t : ℂ) ^ k) • c k) atTop (𝓝 0) := by
        cases n with
        | zero => simpa using h
        | succ m => simpa using (tendsto_ofReal_inv_pow_atTop (Nat.succ_ne_zero m)).smul h
      have h2 : Tendsto (fun t : ℝ => c n + ∑ k ∈ Finset.range n, ((t : ℂ)⁻¹) ^ (n - k) • c k)
          atTop (𝓝 (c n + ∑ k ∈ Finset.range n, (0 : ℂ) • c k)) := by
        refine tendsto_const_nhds.add (tendsto_finsetSum _ fun k hk => ?_)
        rw [Finset.mem_range] at hk
        exact (tendsto_ofReal_inv_pow_atTop (j := n - k) (by omega)).smul_const (c k)
      have heq : ∀ᶠ t : ℝ in atTop, ((t : ℂ)⁻¹) ^ n •
          ∑ k ∈ Finset.range (n + 1), ((t : ℂ) ^ k) • c k =
          c n + ∑ k ∈ Finset.range n, ((t : ℂ)⁻¹) ^ (n - k) • c k := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
        rw [Finset.sum_range_succ, smul_add, smul_smul, Finset.smul_sum, add_comm]
        congr 1
        · rw [inv_pow_mul_pow_of_le ht' le_rfl, Nat.sub_self, pow_zero, one_smul]
        · refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          rw [smul_smul, inv_pow_mul_pow_of_le ht' hk.le]
      have := tendsto_nhds_unique (h1.congr' heq) h2
      simp only [zero_smul, Finset.sum_const_zero, add_zero] at this
      exact this.symm
    have h' : Tendsto (fun t : ℝ => ∑ k ∈ Finset.range n, ((t : ℂ) ^ k) • c k) atTop (𝓝 0) := by
      refine h.congr fun t => ?_
      rw [Finset.sum_range_succ, hcn, smul_zero, add_zero]
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih c h' k hk
    · exact hcn

end Polynomial

/-! ## Resolvent limits along the real axis -/

section Resolvent

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- `(1 - t⁻¹ • A)⁻¹ → 1` as the real parameter `t → +∞`. -/
theorem tendsto_inverse_one_sub_inv_smul (A : R) :
    Tendsto (fun t : ℝ => Ring.inverse (1 - ((t : ℂ)⁻¹) • A)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ => (1 : R) - ((t : ℂ)⁻¹) • A) atTop (𝓝 (1 - (0 : ℂ) • A)) :=
    tendsto_const_nhds.sub (tendsto_ofReal_inv_atTop.smul_const A)
  rw [zero_smul, sub_zero] at h1
  have h2 : ContinuousAt (Ring.inverse : R → R) ((1 : Rˣ) : R) :=
    NormedRing.inverse_continuousAt 1
  have := h2.tendsto.comp h1
  simpa [Function.comp_def, Units.val_one, Ring.inverse_one] using this

/-- The resolvent as a scalar multiple of the Neumann factor:
`(A - t)⁻¹ = -t⁻¹ • (1 - t⁻¹ • A)⁻¹` whenever `t ≠ 0` and `1 - t⁻¹ • A` is a unit. -/
theorem inverse_sub_algebraMap_eq_neg_inv_smul (A : R) {t : ℂ} (ht : t ≠ 0)
    (hX : IsUnit (1 - t⁻¹ • A)) :
    Ring.inverse (A - algebraMap ℂ R t) = (-t⁻¹) • Ring.inverse (1 - t⁻¹ • A) := by
  set X := 1 - t⁻¹ • A with hXdef
  have hAt : A - algebraMap ℂ R t = (-t) • X := sub_algebraMap_eq_neg_smul_one_sub A ht
  have h1 : (A - algebraMap ℂ R t) * ((-t⁻¹) • Ring.inverse X) = 1 := by
    rw [hAt, smul_mul_smul_comm, Ring.mul_inverse_cancel X hX, neg_mul_neg, mul_inv_cancel₀ ht,
      one_smul]
  have h2 : ((-t⁻¹) • Ring.inverse X) * (A - algebraMap ℂ R t) = 1 := by
    rw [hAt, smul_mul_smul_comm, Ring.inverse_mul_cancel X hX, neg_mul_neg, inv_mul_cancel₀ ht,
      one_smul]
  exact Ring.inverse_unit (⟨_, _, h1, h2⟩ : Rˣ)

/-- **`t (A - t)⁻¹ → -1`** as the real parameter `t → +∞`. -/
theorem tendsto_smul_inverse_sub_algebraMap (A : R) :
    Tendsto (fun t : ℝ => (t : ℂ) • Ring.inverse (A - algebraMap ℂ R t)) atTop (𝓝 (-1)) := by
  have key : ∀ᶠ t : ℝ in atTop, (t : ℂ) • Ring.inverse (A - algebraMap ℂ R t) =
      -Ring.inverse (1 - ((t : ℂ)⁻¹) • A) := by
    filter_upwards [eventually_gt_atTop ‖A‖, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    have hz : ‖A‖ < ‖(t : ℂ)‖ := by
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have ht' : (t : ℂ) ≠ 0 := ne_zero_of_norm_lt_norm A hz
    have hX : IsUnit (1 - ((t : ℂ)⁻¹) • A) := (Units.oneSub _ (norm_inv_smul_lt_one A hz)).isUnit
    rw [inverse_sub_algebraMap_eq_neg_inv_smul A ht' hX, smul_smul, mul_neg, mul_inv_cancel₀ ht',
      neg_one_smul]
  have := (tendsto_inverse_one_sub_inv_smul A).neg
  exact this.congr' (key.mono fun t ht => ht.symm)

/-- **`(A - t)⁻¹ → 0`** as the real parameter `t → +∞`. -/
theorem tendsto_inverse_sub_algebraMap (A : R) :
    Tendsto (fun t : ℝ => Ring.inverse (A - algebraMap ℂ R t)) atTop (𝓝 0) := by
  have h := tendsto_ofReal_inv_atTop.smul (tendsto_smul_inverse_sub_algebraMap A)
  rw [zero_smul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [smul_smul, inv_mul_cancel₀ ht', one_smul]

end Resolvent

end RenewalGeometry
