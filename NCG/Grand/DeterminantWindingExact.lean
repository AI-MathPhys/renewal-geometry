/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Jacobi's formula and the winding number of a determinant loop

Machinery for `thm:SMST-fermionic-phase-transport` (QRP.11).

* `hasDerivAt_det` (**Jacobi**): `d/dt det D(t) = tr(adj D(t) · D'(t))`, and
  `hasDerivAt_det_of_det_ne_zero`: `= det D(t) · tr(D(t)⁻¹ D'(t))` for invertible `D(t)`;
* `logLift`: the continuous logarithm `L(t) = log f(0) + ∫₀ᵗ f'/f` of a non-vanishing `C¹` path,
  with `exp (L t) = f t`;
* `exists_int_winding`: for a loop, `(1/2πi) ∫₀¹ f'/f ∈ ℤ`;
* `exists_periodic_log_iff`: a continuous periodic logarithm of the loop exists exactly when this
  integer vanishes;
* `det_winding` (**QRP.11**): `wind (det D) = (1/2πi) ∫₀¹ tr (D⁻¹ dD)`.
-/

open Matrix Finset Filter Topology intervalIntegral

namespace NCG
namespace DeterminantWinding

set_option linter.unusedSectionVars false

/-! ### Jacobi's formula -/

section Jacobi

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Leibniz term with one column replaced. -/
theorem prod_erase_mul_eq_prod_updateCol (M : Matrix n n ℂ) (c : n → ℂ) (σ : Equiv.Perm n) (i : n) :
    (∏ j ∈ univ.erase i, M (σ j) j) * c (σ i) = ∏ j, (M.updateCol i c) (σ j) j := by
  rw [← Finset.mul_prod_erase univ (fun j => (M.updateCol i c) (σ j) j) (mem_univ i)]
  rw [mul_comm]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Matrix.updateCol_apply, if_neg (Finset.ne_of_mem_erase hj)]

/-- **Jacobi's formula**: `d/dt det D(t) = tr (adj D(t) · D'(t))`. -/
theorem hasDerivAt_det {D : ℝ → Matrix n n ℂ} {D' : Matrix n n ℂ} {t : ℝ}
    (hD : ∀ i j, HasDerivAt (fun s => D s i j) (D' i j) t) :
    HasDerivAt (fun s => (D s).det) (Matrix.trace (Matrix.adjugate (D t) * D')) t := by
  have hterm : ∀ σ : Equiv.Perm n, HasDerivAt (fun s => ∏ j, D s (σ j) j)
      (∑ i, (∏ j ∈ univ.erase i, D t (σ j) j) * D' (σ i) i) t := by
    intro σ
    have := HasDerivAt.finsetProd (u := univ) (f := fun j s => D s (σ j) j)
      (f' := fun j => D' (σ j) j) (x := t) fun j _ => hD (σ j) j
    refine (this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · simp [Finset.prod_apply]
    · simp [smul_eq_mul]
  have hsum : HasDerivAt (fun s => (D s).det)
      (∑ σ : Equiv.Perm n, Equiv.Perm.sign σ *
        ∑ i, (∏ j ∈ univ.erase i, D t (σ j) j) * D' (σ i) i) t := by
    have h := HasDerivAt.sum (u := univ) (A := fun σ s => (Equiv.Perm.sign σ : ℂ) * ∏ j, D s (σ
      j) j)
      (A' := fun σ => (Equiv.Perm.sign σ : ℂ) * ∑ i, (∏ j ∈ univ.erase i, D t (σ j) j) * D' (σ i) i)
      (x := t) fun σ _ => (hterm σ).const_mul _
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [Finset.sum_apply]
    exact Matrix.det_apply' (D s)
  refine hsum.congr_deriv ?_
  -- identify the Leibniz sum with the trace of `adj D * D'`
  calc ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ *
        ∑ i, (∏ j ∈ univ.erase i, D t (σ j) j) * D' (σ i) i
      = ∑ i, ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ * ∏ j, ((D t).updateCol i fun k => D' k i)
        (σ j) j := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun σ _ => ?_
        rw [prod_erase_mul_eq_prod_updateCol (D t) (fun k => D' k i) σ i]
    _ = ∑ i, ((D t).updateCol i fun k => D' k i).det := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.det_apply']
    _ = ∑ i, (Matrix.cramer (D t) fun k => D' k i) i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.cramer_apply]
    _ = ∑ i, (Matrix.adjugate (D t) *ᵥ fun k => D' k i) i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.cramer_eq_adjugate_mulVec]
    _ = Matrix.trace (Matrix.adjugate (D t) * D') := by
        simp [Matrix.trace, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Jacobi's formula on the invertible locus: `d/dt det D = det D · tr (D⁻¹ D')`. -/
theorem hasDerivAt_det_of_det_ne_zero {D : ℝ → Matrix n n ℂ} {D' : Matrix n n ℂ} {t : ℝ}
    (hD : ∀ i j, HasDerivAt (fun s => D s i j) (D' i j) t) (hdet : (D t).det ≠ 0) :
    HasDerivAt (fun s => (D s).det) ((D t).det * Matrix.trace ((D t)⁻¹ * D')) t := by
  refine (hasDerivAt_det hD).congr_deriv ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hdet, one_mul]

end Jacobi

/-! ### Continuous logarithms of non-vanishing loops -/

section Winding

variable {f f' : ℝ → ℂ}

/-- The logarithmic lift `L(t) = log f(0) + ∫₀ᵗ f'/f`. -/
noncomputable def logLift (f f' : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.log (f 0) + ∫ s in (0 : ℝ)..t, f' s / f s

theorem logLift_zero (f f' : ℝ → ℂ) : logLift f f' 0 = Complex.log (f 0) := by
  simp [logLift]

theorem hasDerivAt_logLift (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    (hne : ∀ t, f t ≠ 0) (t : ℝ) : HasDerivAt (logLift f f') (f' t / f t) t := by
  have hcont : Continuous fun s => f' s / f s :=
    hf'.div (continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt) hne
  have := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t)
    (hcont.intervalIntegrable 0 t) (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  exact this.const_add _

/-- The lift is a logarithm: `exp (L t) = f t`. -/
theorem exp_logLift (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') (hne : ∀ t, f t ≠ 0)
    (t : ℝ) : Complex.exp (logLift f f' t) = f t := by
  -- `f · exp (-L)` has zero derivative, hence is constant
  have hg : ∀ s, HasDerivAt (fun u => f u * Complex.exp (-logLift f f' u)) 0 s := by
    intro s
    have h1 := (hf s).mul ((hasDerivAt_logLift hf hf' hne s).neg.cexp)
    refine h1.congr_deriv ?_
    field_simp [hne s]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) fun s => (hg s).deriv
  have h0 := hconst t 0
  rw [logLift_zero, Complex.exp_neg (Complex.log (f 0)), Complex.exp_log (hne 0),
    mul_inv_cancel₀ (hne 0)] at h0
  -- `f t * exp (-L t) = 1`
  have hexp := Complex.exp_ne_zero (-logLift f f' t)
  calc Complex.exp (logLift f f' t)
      = Complex.exp (logLift f f' t) * (f t * Complex.exp (-logLift f f' t)) := by rw [h0, mul_one]
    _ = f t := by
        rw [mul_comm (f t), ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
          one_mul]

/-- **Integrality of the winding number**: for a loop `f 1 = f 0`,
`∫₀¹ f'/f = 2πi k` for an integer `k`. -/
theorem exists_int_winding (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    (hne : ∀ t, f t ≠ 0) (hloop : f 1 = f 0) :
    ∃ k : ℤ, ∫ s in (0 : ℝ)..1, f' s / f s = k * (2 * Real.pi * Complex.I) := by
  have h1 := exp_logLift hf hf' hne 1
  have h0 := exp_logLift hf hf' hne 0
  rw [hloop, ← h0] at h1
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  refine ⟨k, ?_⟩
  have : logLift f f' 1 - logLift f f' 0 = ∫ s in (0 : ℝ)..1, f' s / f s := by
    simp [logLift]
  rw [← this, hk]
  ring

/-- The winding number of the loop. -/
noncomputable def winding (f f' : ℝ → ℂ) : ℂ :=
  (∫ s in (0 : ℝ)..1, f' s / f s) / (2 * Real.pi * Complex.I)

theorem winding_eq_int (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    (hne : ∀ t, f t ≠ 0) (hloop : f 1 = f 0) : ∃ k : ℤ, winding f f' = k := by
  obtain ⟨k, hk⟩ := exists_int_winding hf hf' hne hloop
  refine ⟨k, ?_⟩
  unfold winding
  rw [hk, mul_div_cancel_right₀]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

/-- Any two continuous logarithms of `f` on `[0, 1]` differ by a constant `2πi m`. -/
theorem log_unique {L M : ℝ → ℂ} (hL : ContinuousOn L (Set.Icc 0 1)) (hM : ContinuousOn M
  (Set.Icc 0 1))
    (hLf : ∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (L t) = f t)
    (hMf : ∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (M t) = f t) :
    ∃ m : ℤ, ∀ t ∈ Set.Icc (0 : ℝ) 1, M t = L t + m * (2 * Real.pi * Complex.I) := by
  have h0 : Complex.exp (M 0) = Complex.exp (L 0) := by
    rw [hMf 0 (by simp), hLf 0 (by simp)]
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h0
  refine ⟨m, ?_⟩
  -- the shifted lift agrees with `M` at `0`, hence everywhere by covering-map uniqueness
  let p : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  let g₁ : Set.Icc (0 : ℝ) 1 → ℂ := fun t => M t
  let g₂ : Set.Icc (0 : ℝ) 1 → ℂ := fun t => L t + m * (2 * Real.pi * Complex.I)
  have hg₁ : Continuous g₁ := hM.comp_continuous continuous_subtype_val fun t => t.2
  have hg₂ : Continuous g₂ :=
    (hL.comp_continuous continuous_subtype_val fun t => t.2).add continuous_const
  have he : p ∘ g₁ = p ∘ g₂ := by
    funext t
    apply Subtype.ext
    change Complex.exp (M t) = Complex.exp (L t + m * (2 * Real.pi * Complex.I))
    rw [Complex.exp_add, hMf t t.2, ← hLf t t.2]
    have : Complex.exp (m * (2 * Real.pi * Complex.I)) = 1 := Complex.exp_int_mul_two_pi_mul_I m
    rw [this, mul_one]
  have heq := Complex.isCoveringMap_exp.eq_of_comp_eq hg₁ hg₂ he ⟨0, by simp⟩ (by
    change M 0 = L 0 + m * (2 * Real.pi * Complex.I)
    exact hm)
  intro t ht
  exact congrFun heq ⟨t, ht⟩

/-- **Continuous periodic logarithm**: a continuous logarithm of the loop with `M 1 = M 0` exists
exactly when the winding number vanishes. -/
theorem exists_periodic_log_iff (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    (hne : ∀ t, f t ≠ 0) (_hloop : f 1 = f 0) :
    (∃ M : ℝ → ℂ, ContinuousOn M (Set.Icc 0 1) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (M t) = f t) ∧ M 1 = M 0) ↔
      winding f f' = 0 := by
  have hLcont : ContinuousOn (logLift f f') (Set.Icc 0 1) := fun t _ =>
    (hasDerivAt_logLift hf hf' hne t).continuousAt.continuousWithinAt
  have hdiff : logLift f f' 1 - logLift f f' 0 = ∫ s in (0 : ℝ)..1, f' s / f s := by
    simp [logLift]
  have h2πI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  constructor
  · rintro ⟨M, hM, hMf, hper⟩
    obtain ⟨m, hm⟩ := log_unique hLcont hM (fun t _ => exp_logLift hf hf' hne t) hMf
    have h1 := hm 1 (by simp)
    have h0 := hm 0 (by simp)
    have : logLift f f' 1 = logLift f f' 0 := by linear_combination h0 - h1 + hper
    unfold winding
    rw [← hdiff, this, sub_self, zero_div]
  · intro hw
    refine ⟨logLift f f', hLcont, fun t _ => exp_logLift hf hf' hne t, ?_⟩
    unfold winding at hw
    rw [div_eq_zero_iff] at hw
    rcases hw with hw | hw
    · rw [← hdiff] at hw
      exact sub_eq_zero.mp hw
    · exact absurd hw h2πI

end Winding

/-! ### The determinant loop (QRP.11) -/

section Determinant

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **(QRP.11)**: for a `C¹` loop of invertible matrices,
`wind (det D) = (1/2πi) ∫₀¹ tr (D⁻¹ dD)`, and the integral is `2πi` times an integer. -/
theorem det_winding {D : ℝ → Matrix n n ℂ} {D' : ℝ → Matrix n n ℂ}
    (hD : ∀ t i j, HasDerivAt (fun s => D s i j) (D' t i j) t)
    (hD' : ∀ i j, Continuous fun t => D' t i j) (hinv : ∀ t, (D t).det ≠ 0)
    (hloop : D 1 = D 0) :
    winding (fun t => (D t).det) (fun t => (D t).det * Matrix.trace ((D t)⁻¹ * D' t))
        = (∫ s in (0 : ℝ)..1, Matrix.trace ((D s)⁻¹ * D' s)) / (2 * Real.pi * Complex.I) ∧
      ∃ k : ℤ, ∫ s in (0 : ℝ)..1, Matrix.trace ((D s)⁻¹ * D' s) = k * (2 * Real.pi * Complex.I)
        := by
  have hderiv : ∀ t, HasDerivAt (fun s => (D s).det)
      ((D t).det * Matrix.trace ((D t)⁻¹ * D' t)) t := fun t =>
    hasDerivAt_det_of_det_ne_zero (hD t) (hinv t)
  have hDcont : ∀ i j, Continuous fun t => D t i j := fun i j =>
    continuous_iff_continuousAt.mpr fun t => (hD t i j).continuousAt
  have hdetcont : Continuous fun t => (D t).det :=
    (continuous_matrix fun i j => hDcont i j).matrix_det
  have hinvcont : Continuous fun t => (D t)⁻¹ := by
    have hDc : Continuous fun t => D t := continuous_matrix fun i j => hDcont i j
    have h1 : Continuous fun t => (D t).det⁻¹ • (D t).adjugate :=
      (hdetcont.inv₀ hinv).smul hDc.matrix_adjugate
    refine h1.congr fun t => ?_
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  have hf' : Continuous fun t => (D t).det * Matrix.trace ((D t)⁻¹ * D' t) := by
    exact hdetcont.mul (hinvcont.matrix_mul (continuous_matrix fun i j => hD' i j)).matrix_trace
  have hratio : ∀ s, (D s).det * Matrix.trace ((D s)⁻¹ * D' s) / (D s).det
      = Matrix.trace ((D s)⁻¹ * D' s) := fun s => by
    rw [mul_div_assoc, mul_comm]
    exact div_mul_cancel₀ _ (hinv s)
  constructor
  · unfold winding
    congr 1
    exact intervalIntegral.integral_congr fun s _ => hratio s
  · obtain ⟨k, hk⟩ := exists_int_winding hderiv hf' hinv (by rw [hloop])
    refine ⟨k, ?_⟩
    rw [← hk]
    exact (intervalIntegral.integral_congr fun s _ => hratio s).symm

end Determinant

end DeterminantWinding
end NCG
