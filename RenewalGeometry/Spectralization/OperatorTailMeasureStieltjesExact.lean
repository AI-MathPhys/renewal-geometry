/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
/-!
# Positive operator-valued tail measures, the Stieltjes self-energy, and escaped memory

This file covers, for `papers/predictive_spectral_geometry`,

* `def:supp-POVM` — a bounded positive operator-valued tail measure on `(0,∞)` for a
  finite-dimensional `H` (`PositiveTailMeasure`), and its Stieltjes self-energy
  `Σ_μ(z) = ∫ (λ - z)⁻¹ dμ(λ)` (`PositiveTailMeasure.stieltjesSelfEnergy`), together
  with the Euclidean memory kernel `K_μ(t) = ∫ e^{-tλ} dμ(λ)`
  (`PositiveTailMeasure.euclideanMemoryKernel`);
* `cth:supp-contact-static` — for the atoms `μ_n = λ_n Q δ_{λ_n}` with `λ_n → ∞`:
  `Σ_n(0) = Q`, `Σ_n(z) = λ_n/(λ_n - z) Q → Q`, `K_n(t) = λ_n e^{-λ_n t} Q → 0` for `t > 0`,
  and `K_n(t) dt → Q δ_0` distributionally (against bounded continuous test functions on
  `[0,∞)`), packaged in `contact_static`.

The operator measure is encoded as a Mathlib `VectorMeasure` on `ℝ` with values in the
matrix space `H → H → ℂ` (product topology; in finite dimension weak, entrywise and norm
countable additivity coincide), taking positive semidefinite values on measurable sets
and vanishing on subsets of `(-∞, 0]`.  Boundedness `‖μ((0,∞))‖ < ∞` is automatic for a
vector measure.  The operator integrals are Mathlib's vector-measure integrals paired
through scalar multiplication `ℂ × (H → H → ℂ) → (H → H → ℂ)`.
-/

open MeasureTheory Filter Topology Set
open scoped ComplexOrder

namespace RenewalGeometry
namespace OperatorTailMeasure

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- `def:supp-POVM` (Positive operator-valued tail measure): a countably additive
`B(H)`-valued measure on the Borel sets of `(0,∞)` with positive semidefinite values.  It is
modelled as a vector measure on `ℝ` (values in `H → H → ℂ` with the product topology)
that vanishes on measurable subsets of `(-∞, 0]`. -/
structure PositiveTailMeasure (H : Type*) [Fintype H] [DecidableEq H] where
  /-- The underlying countably additive set function `𝔅(ℝ) → B(H)`. -/
  toVectorMeasure : VectorMeasure ℝ (H → H → ℂ)
  /-- `μ(E) ⪰ 0` for every Borel set `E`. -/
  posSemidef : ∀ s : Set ℝ, MeasurableSet s → (Matrix.of (toVectorMeasure s)).PosSemidef
  /-- `μ` lives on `(0,∞)`: it vanishes on Borel subsets of `(-∞, 0]`. -/
  eq_zero_of_subset_Iic :
    ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Iic 0 → toVectorMeasure s = 0

namespace PositiveTailMeasure

variable (μ : PositiveTailMeasure H)

/-- The total mass `μ((0,∞))` (finite by construction). -/
noncomputable def totalMass : Matrix H H ℂ :=
  Matrix.of (μ.toVectorMeasure (Set.Ioi 0))

/-- The Stieltjes self-energy `Σ_μ(z) = ∫_{(0,∞)} (λ - z)⁻¹ dμ(λ)` (eq:supp-Stieltjes), as
the vector-measure integral of the scalar function `λ ↦ (λ - z)⁻¹` against `μ` paired
through scalar multiplication. -/
noncomputable def stieltjesSelfEnergy (z : ℂ) : Matrix H H ℂ :=
  Matrix.of (VectorMeasure.integral μ.toVectorMeasure (fun lam : ℝ => ((lam : ℂ) - z)⁻¹)
    (ContinuousLinearMap.lsmul ℝ ℂ))

/-- The Euclidean memory kernel `K_μ(t) = ∫ e^{-tλ} dμ(λ)` (eq:supp-Euclidean-memory). -/
noncomputable def euclideanMemoryKernel (t : ℝ) : Matrix H H ℂ :=
  Matrix.of (VectorMeasure.integral μ.toVectorMeasure
    (fun lam : ℝ => ((Real.exp (-t * lam) : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℝ ℂ))

/-- The `n`-th moment `M_n = ∫ λ^n dμ(λ)` (thm:supp-memory-determinacy). -/
noncomputable def moment (n : ℕ) : Matrix H H ℂ :=
  Matrix.of (VectorMeasure.integral μ.toVectorMeasure (fun lam : ℝ => ((lam ^ n : ℝ) : ℂ))
    (ContinuousLinearMap.lsmul ℝ ℂ))

/-- `μ` is supported in `(0, R]`: it vanishes on Borel subsets of `(R, ∞)` (compact support
in the sense of thm:supp-memory-determinacy). -/
def IsSupportedIn (R : ℝ) : Prop :=
  ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioi R → μ.toVectorMeasure s = 0

end PositiveTailMeasure

/-! ## The atomic tail measures `λ Q δ_λ` -/

/-- The atom `λ Q δ_λ` (`0 < λ`, `Q ⪰ 0`) as a positive tail measure. -/
noncomputable def atomic (lam : ℝ) (hlam : 0 < lam) (Q : Matrix H H ℂ) (hQ : Q.PosSemidef) :
    PositiveTailMeasure H where
  toVectorMeasure := VectorMeasure.dirac lam (Matrix.of.symm ((lam : ℂ) • Q))
  posSemidef s hs := by
    by_cases h : lam ∈ s
    · rw [VectorMeasure.dirac_apply_of_mem hs h, Equiv.apply_symm_apply]
      exact hQ.smul (Complex.zero_le_real.mpr hlam.le)
    · rw [VectorMeasure.dirac_apply_of_notMem h]
      exact Matrix.PosSemidef.zero
  eq_zero_of_subset_Iic s _ hsub :=
    VectorMeasure.dirac_apply_of_notMem fun h => absurd (hsub h) (not_le.mpr hlam)

variable {lam : ℝ} {hlam : 0 < lam} {Q : Matrix H H ℂ} {hQ : Q.PosSemidef}

/-- `Σ_n(z) = λ_n/(λ_n - z) Q` for the atom (eq:supp-contact-static). -/
theorem stieltjesSelfEnergy_atomic (z : ℂ) :
    (atomic lam hlam Q hQ).stieltjesSelfEnergy z = (((lam : ℂ) - z)⁻¹ * lam) • Q := by
  unfold PositiveTailMeasure.stieltjesSelfEnergy atomic
  simp only
  rw [VectorMeasure.integral_dirac, ContinuousLinearMap.lsmul_apply]
  ext i j
  simp [mul_assoc]

/-- `Σ_n(0) = Q` for the atom (eq:supp-contact-static). -/
theorem stieltjesSelfEnergy_atomic_zero :
    (atomic lam hlam Q hQ).stieltjesSelfEnergy 0 = Q := by
  rw [stieltjesSelfEnergy_atomic, sub_zero,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlam.ne'), one_smul]

/-- `K_n(t) = λ_n e^{-λ_n t} Q` for the atom. -/
theorem euclideanMemoryKernel_atomic (t : ℝ) :
    (atomic lam hlam Q hQ).euclideanMemoryKernel t =
      ((Real.exp (-t * lam) : ℂ) * lam) • Q := by
  unfold PositiveTailMeasure.euclideanMemoryKernel atomic
  simp only
  rw [VectorMeasure.integral_dirac, ContinuousLinearMap.lsmul_apply]
  ext i j
  simp [mul_assoc]

/-! ## Limits as `λ_n → ∞` -/

/-- `λ_n/(λ_n - z) → 1` when `λ_n → ∞`. -/
theorem tendsto_inv_sub_mul (z : ℂ) {l : ℕ → ℝ} (htop : Tendsto l atTop atTop) :
    Tendsto (fun n => ((l n : ℂ) - z)⁻¹ * l n) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => ((l n)⁻¹ : ℝ)) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp htop
  have h2 : Tendsto (fun n => ((l n : ℂ))⁻¹) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp h1
    rw [Complex.ofReal_zero] at this
    exact this.congr fun n => by simp [Function.comp]
  have h3 : Tendsto (fun n => (1 : ℂ) - z * ((l n : ℂ))⁻¹) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℂ))).sub ((tendsto_const_nhds (x := z)).mul h2)
    simpa using this
  have h4 : Tendsto (fun n => ((1 : ℂ) - z * ((l n : ℂ))⁻¹)⁻¹) atTop (𝓝 1) := by
    simpa using h3.inv₀ one_ne_zero
  refine h4.congr' ?_
  filter_upwards [htop.eventually_gt_atTop 0] with n hn
  have hl : (l n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have : (1 : ℂ) - z * ((l n : ℂ))⁻¹ = ((l n : ℂ) - z) * (l n : ℂ)⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ hl]
  rw [this, mul_inv, inv_inv]

/-- `Σ_n(z) → Q` (eq:supp-contact-static): the static self-energy of the escaping atoms
converges to `Q` for every fixed `z`. -/
theorem tendsto_stieltjesSelfEnergy_atomic (z : ℂ) {l : ℕ → ℝ} (hl : ∀ n, 0 < l n)
    (htop : Tendsto l atTop atTop) :
    Tendsto (fun n => (atomic (l n) (hl n) Q hQ).stieltjesSelfEnergy z) atTop (𝓝 Q) := by
  simp_rw [stieltjesSelfEnergy_atomic]
  have := (tendsto_inv_sub_mul z htop).smul_const Q
  simpa using this

/-- `e^{-tλ_n} λ_n → 0` for `t > 0`. -/
theorem tendsto_exp_neg_mul {t : ℝ} (ht : 0 < t) {l : ℕ → ℝ} (htop : Tendsto l atTop atTop) :
    Tendsto (fun n => Real.exp (-t * l n) * l n) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (htop.const_mul_atTop ht)
  have h' := h.const_mul t⁻¹
  rw [mul_zero] at h'
  refine h'.congr fun n => ?_
  simp only [Function.comp_apply, pow_one]
  field_simp
  try ring_nf

/-- `K_n(t) → 0` for every `t > 0` (cth:supp-contact-static): the memory of the escaping
atoms vanishes at every positive Euclidean time. -/
theorem tendsto_euclideanMemoryKernel_atomic {t : ℝ} (ht : 0 < t) {l : ℕ → ℝ}
    (hl : ∀ n, 0 < l n) (htop : Tendsto l atTop atTop) :
    Tendsto (fun n => (atomic (l n) (hl n) Q hQ).euclideanMemoryKernel t) atTop (𝓝 0) := by
  simp_rw [euclideanMemoryKernel_atomic]
  have h1 := tendsto_exp_neg_mul ht htop
  have h2 : Tendsto (fun n => ((Real.exp (-t * l n) : ℂ) * l n)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp h1
    rw [Complex.ofReal_zero] at this
    exact this.congr fun n => by simp only [Function.comp_apply, Complex.ofReal_mul]
  have h3 := h2.smul_const Q
  rw [zero_smul] at h3
  exact h3

/-! ## The approximate identity `λ e^{-λ t} dt → δ_0` -/

/-- Substitution `t = s/λ`: `∫_0^∞ φ(t) λ e^{-λ t} dt = ∫_0^∞ φ(s/λ) e^{-s} ds`. -/
theorem integral_mul_exp_eq (φ : ℝ → ℝ) {l : ℝ} (hl : 0 < l) :
    ∫ t in Ioi 0, φ t * (l * Real.exp (-l * t)) =
      ∫ s in Ioi 0, φ (s / l) * Real.exp (-s) := by
  have h := integral_comp_mul_left_Ioi' (fun s => φ (s / l) * Real.exp (-s)) 0 hl
  rw [mul_zero] at h
  rw [← h, smul_eq_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [mul_div_cancel_left₀ _ hl.ne']
  ring_nf

/-- The exponential kernels form an approximate identity at the origin: for a bounded
continuous `φ`, `∫_0^∞ φ(t) λ_n e^{-λ_n t} dt → φ(0)` when `λ_n → ∞`. -/
theorem tendsto_integral_mul_exp (φ : ℝ → ℝ) (hφ : Continuous φ) {M : ℝ} (hM : ∀ t, |φ t| ≤ M)
    {l : ℕ → ℝ} (hl : ∀ n, 0 < l n) (htop : Tendsto l atTop atTop) :
    Tendsto (fun n => ∫ t in Ioi 0, φ t * (l n * Real.exp (-l n * t))) atTop (𝓝 (φ 0)) := by
  simp_rw [fun n => integral_mul_exp_eq φ (hl n)]
  have hlim : ∫ s in Ioi 0, φ 0 * Real.exp (-s) = φ 0 := by
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun s => M * Real.exp (-s)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun n =>
      ((hφ.comp (continuous_id.div_const _)).mul
        (Real.continuous_exp.comp continuous_neg)).aestronglyMeasurable
  · refine Eventually.of_forall fun n => ae_of_all _ fun s => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hM _) (Real.exp_pos _).le
  · exact (integrableOn_exp_neg_Ioi 0).const_mul M
  · refine ae_of_all _ fun s => ?_
    have h1 : Tendsto (fun n => s / l n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop htop
    exact ((hφ.tendsto 0).comp h1).mul_const _

/-- Distributional convergence `K_n(t) dt → Q δ_0` (cth:supp-contact-static): for a bounded
continuous test function `φ`, `∫_0^∞ φ(t) K_n(t) dt = (∫_0^∞ φ(t) λ_n e^{-λ_n t} dt) Q → φ(0) Q`. -/
theorem tendsto_integral_kernel_atomic (φ : ℝ → ℝ) (hφ : Continuous φ) {M : ℝ}
    (hM : ∀ t, |φ t| ≤ M) {l : ℕ → ℝ} (hl : ∀ n, 0 < l n) (htop : Tendsto l atTop atTop) :
    Tendsto (fun n => (∫ t in Ioi 0, φ t * (l n * Real.exp (-l n * t))) • Q) atTop
      (𝓝 (φ 0 • Q)) :=
  (tendsto_integral_mul_exp φ hφ hM hl htop).smul_const Q

/-- The atomic kernel is the scalar kernel `λ e^{-λ t}` times `Q`. -/
theorem euclideanMemoryKernel_atomic_eq_real_smul (t : ℝ) :
    (atomic lam hlam Q hQ).euclideanMemoryKernel t = (lam * Real.exp (-lam * t)) • Q := by
  rw [euclideanMemoryKernel_atomic]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring_nf

/-- **`cth:supp-contact-static` (The static triple does not identify escaped memory).**
For `Q ⪰ 0` and `λ_n → ∞`, the atoms `μ_n = λ_n Q δ_{λ_n}` satisfy `Σ_n(0) = Q`,
`Σ_n(z) = λ_n/(λ_n - z) Q → Q`, while `K_n(t) = λ_n e^{-λ_n t} Q → 0` for every `t > 0` and
`K_n(t) dt → Q δ_0` against bounded continuous test functions on `[0,∞)`. -/
theorem contact_static {l : ℕ → ℝ} (hl : ∀ n, 0 < l n) (htop : Tendsto l atTop atTop) :
    (∀ n, (atomic (l n) (hl n) Q hQ).stieltjesSelfEnergy 0 = Q) ∧
    (∀ n (z : ℂ), (atomic (l n) (hl n) Q hQ).stieltjesSelfEnergy z =
      (((l n : ℂ) - z)⁻¹ * l n) • Q) ∧
    (∀ z : ℂ, Tendsto (fun n => (atomic (l n) (hl n) Q hQ).stieltjesSelfEnergy z) atTop
      (𝓝 Q)) ∧
    (∀ n (t : ℝ), (atomic (l n) (hl n) Q hQ).euclideanMemoryKernel t =
      (l n * Real.exp (-l n * t)) • Q) ∧
    (∀ t : ℝ, 0 < t →
      Tendsto (fun n => (atomic (l n) (hl n) Q hQ).euclideanMemoryKernel t) atTop (𝓝 0)) ∧
    (∀ (φ : ℝ → ℝ), Continuous φ → ∀ M : ℝ, (∀ t, |φ t| ≤ M) →
      Tendsto (fun n => (∫ t in Ioi 0, φ t * (l n * Real.exp (-l n * t))) • Q) atTop
        (𝓝 (φ 0 • Q))) :=
  ⟨fun n => stieltjesSelfEnergy_atomic_zero, fun n z => stieltjesSelfEnergy_atomic z,
    fun z => tendsto_stieltjesSelfEnergy_atomic z hl htop,
    fun n t => euclideanMemoryKernel_atomic_eq_real_smul t,
    fun t ht => tendsto_euclideanMemoryKernel_atomic ht hl htop,
    fun φ hφ M hM => tendsto_integral_kernel_atomic φ hφ hM hl htop⟩

end OperatorTailMeasure
end RenewalGeometry
