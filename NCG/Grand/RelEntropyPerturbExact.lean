/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.MatFunShiftExact
import NCG.Grand.PetzSufficiencyExact

/-!
# Joint convexity of the relative entropy at singular states

Step (D4m) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: the `ε`-regularised convexity passes to
the limit at support-compatible positive **semi**definite data — the form
needed at the singular Stinespring dilations of the Weyl twirl chain.

* `supp_overlap_of_ker`: kernel inclusion `ker σ ⊆ ker ρ` gives the
  scalar support condition `qⱼ = 0 → pᵢ|Wᵢⱼ|² = 0`;
* `relEntropy_shift_tendsto`: `D(ρ+ε1‖σ+ε1) → D(ρ‖σ)` as `ε → 0` under
  the support condition — plain continuity of `x log x` in the fixed
  eigenbasis;
* `relEntropy_convex_psd`: **joint convexity at PSD data** with kernel
  inclusions, by regularisation.
-/

open Matrix Unitary Finset Filter Topology
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ρ σ S : Matrix n n ℂ}

/-! ### Kernel transfer to the scalar support condition -/

omit [DecidableEq n] in
theorem real_smul_mulVec (c : ℝ) (M : Matrix n n ℂ) (v : n → ℂ) :
    (c • M) *ᵥ v = (c : ℂ) • (M *ᵥ v) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply,
    smul_eq_mul, Complex.real_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem diag_mulVec_apply (d : n → ℂ) (v : n → ℂ) (i : n) :
    (diagonal d *ᵥ v) i = d i * v i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, ite_mul,
    zero_mul]
  rw [Finset.sum_ite_eq _ i fun k => d i * v k]
  simp

omit [DecidableEq n] in
/-- A vanishing positive semidefinite quadratic form kills the vector:
`⟨v, S v⟩ = 0 → S v = 0`. -/
theorem mulVec_eq_zero_of_quadratic_zero {v : n → ℂ} (hS : S.PosSemidef)
    (h : star v ⬝ᵥ (S *ᵥ v) = 0) : S *ᵥ v = 0 := by
  classical
  set R := Petz.sqrtMat hS.1 with hR
  have hRR : R * R = S := Petz.sqrtMat_mul_self hS
  have hRh : R.IsHermitian := by
    rw [hR]
    unfold Petz.sqrtMat
    exact Petz.matFun_isHermitian hS.1 Real.sqrt
  have hq : star (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = 0 := by
    rw [Matrix.star_mulVec, hRh.eq, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, hRR]
    exact h
  have hRv : R *ᵥ v = 0 := mulVec_self_dot_eq_zero hq
  calc S *ᵥ v = R *ᵥ (R *ᵥ v) := by rw [Matrix.mulVec_mulVec, hRR]
    _ = 0 := by rw [hRv, Matrix.mulVec_zero]

/-- **Kernel inclusion gives the scalar support condition**:
if `σ v = 0 → ρ v = 0` then `qⱼ = 0 → pᵢ |Wᵢⱼ|² = 0`. -/
theorem supp_overlap_of_ker (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hker : ∀ v, σ *ᵥ v = 0 → ρ *ᵥ v = 0) :
    ∀ i j, hσ.1.eigenvalues j = 0 →
      hρ.1.eigenvalues i * Complex.normSq (overlap hρ.1 hσ.1 i j) = 0 := by
  intro i j hq
  set U : Matrix n n ℂ := (hσ.1.eigenvectorUnitary : Matrix n n ℂ)
    with hU
  set Uρ : Matrix n n ℂ := (hρ.1.eigenvectorUnitary : Matrix n n ℂ)
    with hUρ
  have hσU : σ * U =
      U * diagonal (RCLike.ofReal ∘ hσ.1.eigenvalues) := by
    have hdec := hσ.1.spectral_theorem
    rw [conjStarAlgAut_apply] at hdec
    calc σ * U = (U * diagonal (RCLike.ofReal ∘ hσ.1.eigenvalues) *
          star U) * U := by rw [← hdec]
      _ = U * diagonal (RCLike.ofReal ∘ hσ.1.eigenvalues) *
          (star U * U) := by simp only [Matrix.mul_assoc]
      _ = U * diagonal (RCLike.ofReal ∘ hσ.1.eigenvalues) := by
          rw [star_mul_coe hσ.1.eigenvectorUnitary, Matrix.mul_one]
  have hcol : σ *ᵥ (fun k => U k j) = 0 := by
    ext k
    have h1 : (σ *ᵥ fun k => U k j) k = (σ * U) k j := by
      simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
    rw [h1, hσU, Matrix.mul_diagonal]
    simp [hq]
  have hρcol := hker _ hcol
  have hUρρ : star Uρ * ρ =
      diagonal (RCLike.ofReal ∘ hρ.1.eigenvalues) * star Uρ := by
    have hdec := hρ.1.spectral_theorem
    rw [conjStarAlgAut_apply] at hdec
    calc star Uρ * ρ = star Uρ *
          (Uρ * diagonal (RCLike.ofReal ∘ hρ.1.eigenvalues) *
            star Uρ) := by rw [← hdec]
      _ = (star Uρ * Uρ) *
          (diagonal (RCLike.ofReal ∘ hρ.1.eigenvalues) * star Uρ) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal (RCLike.ofReal ∘ hρ.1.eigenvalues) * star Uρ := by
          rw [star_mul_coe hρ.1.eigenvectorUnitary, Matrix.one_mul]
  have hzero : (diagonal (RCLike.ofReal ∘ hρ.1.eigenvalues) * star Uρ)
      *ᵥ (fun k => U k j) = 0 := by
    rw [← hUρρ, ← Matrix.mulVec_mulVec, hρcol, Matrix.mulVec_zero]
  have hentry := congrFun hzero i
  rw [← Matrix.mulVec_mulVec, diag_mulVec_apply] at hentry
  have hov : (star Uρ *ᵥ fun k => U k j) i = overlap hρ.1 hσ.1 i j := by
    simp [Matrix.mulVec, dotProduct, overlap, Matrix.mul_apply, hU, hUρ]
  rw [hov] at hentry
  simp only [Function.comp_apply, Pi.zero_apply] at hentry
  rcases mul_eq_zero.mp hentry with h0 | h0
  · have h0' : hρ.1.eigenvalues i = 0 := by
      have hre := congrArg Complex.re h0
      simpa using hre
    rw [h0', zero_mul]
  · rw [h0, Complex.normSq_zero, mul_zero]

omit [DecidableEq n] in
/-- Kernel inclusion passes to nonnegative mixtures. -/
theorem ker_sum_smul {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ j, 0 ≤ lam j) {ρmat σmat : ι → Matrix n n ℂ}
    (hσj : ∀ j, (σmat j).PosSemidef)
    (hker : ∀ j, ∀ v, σmat j *ᵥ v = 0 → ρmat j *ᵥ v = 0) :
    ∀ v, (∑ j, lam j • σmat j) *ᵥ v = 0 →
      (∑ j, lam j • ρmat j) *ᵥ v = 0 := by
  classical
  intro v hv
  have hquad : ∑ j, (lam j : ℂ) * (star v ⬝ᵥ (σmat j *ᵥ v)) = 0 := by
    have h1 : star v ⬝ᵥ ((∑ j, lam j • σmat j) *ᵥ v) = 0 := by
      rw [hv, dotProduct_zero]
    rw [Matrix.sum_mulVec] at h1
    rw [← h1, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hterm : ∀ j, (lam j : ℂ) * (star v ⬝ᵥ (σmat j *ᵥ v)) = 0 := by
    have hnn : ∀ j ∈ Finset.univ,
        (0 : ℂ) ≤ (lam j : ℂ) * (star v ⬝ᵥ (σmat j *ᵥ v)) := fun j _ =>
      mul_nonneg (by exact_mod_cast hlam j)
        ((hσj j).dotProduct_mulVec_nonneg v)
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hquad j
      (Finset.mem_univ j)
  have hcols : ∀ j, lam j • (ρmat j *ᵥ v) = 0 := by
    intro j
    rcases eq_or_lt_of_le (hlam j) with h0 | hpos
    · rw [← h0, zero_smul]
    · have hσv : σmat j *ᵥ v = 0 := by
        refine mulVec_eq_zero_of_quadratic_zero (hσj j) ?_
        have := hterm j
        have hne : (lam j : ℂ) ≠ 0 := by
          exact_mod_cast hpos.ne'
        exact (mul_eq_zero.mp this).resolve_left hne
      rw [hker j v hσv, smul_zero]
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [real_smul_mulVec]
  have := hcols j
  rw [← this]
  ext k
  simp [Complex.real_smul]

/-! ### The regularised entropy limit -/

theorem shift_klein_tendsto (p : ℝ) :
    Tendsto (fun ε : ℝ => (p + ε) * Real.log (p + ε)) (𝓝 0)
      (𝓝 (p * Real.log p)) := by
  have hshift : Tendsto (fun ε : ℝ => p + ε) (𝓝 0) (𝓝 p) := by
    simpa using (continuous_const_add p).tendsto (0 : ℝ)
  have h := (Real.continuous_mul_log.tendsto p).comp hshift
  exact h

theorem shift_cross_tendsto (p q w : ℝ) (_hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsupp : q = 0 → p * w = 0) :
    Tendsto (fun ε : ℝ => (p + ε) * Real.log (q + ε) * w) (𝓝 0)
      (𝓝 (p * Real.log q * w)) := by
  have hshift : ∀ a : ℝ, Tendsto (fun ε : ℝ => a + ε) (𝓝 0) (𝓝 a) := by
    intro a
    simpa using (continuous_const_add a).tendsto (0 : ℝ)
  rcases eq_or_lt_of_le hq with h0 | hqpos
  · -- singular column: `p·w = 0`
    rcases mul_eq_zero.mp (hsupp h0.symm) with hp0 | hw0
    · -- `p = 0`: the whole term is `ε log ε · w → 0`
      rw [← h0, hp0]
      have h1 := (shift_klein_tendsto 0).mul_const w
      simp only [zero_add] at h1 ⊢
      exact h1
    · -- `w = 0`: constant zero
      rw [hw0]
      have hfun : (fun ε : ℝ => (p + ε) * Real.log (q + ε) * 0) =
          fun _ => (0 : ℝ) := funext fun ε => mul_zero _
      rw [hfun, mul_zero]
      exact tendsto_const_nhds
  · -- regular column: plain continuity
    have hlog : Tendsto (fun ε : ℝ => Real.log (q + ε)) (𝓝 0)
        (𝓝 (Real.log q)) :=
      ((Real.continuousAt_log hqpos.ne').tendsto).comp (hshift q)
    exact ((hshift p).mul hlog).mul_const w

set_option maxHeartbeats 1600000 in -- doubly indexed continuity passage
/-- **The regularised entropy limit**: `D(ρ+ε1‖σ+ε1) → D(ρ‖σ)` as
`ε → 0`, under the scalar support condition. -/
theorem relEntropy_shift_tendsto (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ i j, hσ.1.eigenvalues j = 0 →
      hρ.1.eigenvalues i * Complex.normSq (overlap hρ.1 hσ.1 i j) = 0) :
    Tendsto (fun ε : ℝ =>
      relEntropy (shift_isHermitian hρ.1 ε) (shift_isHermitian hσ.1 ε))
      (𝓝 0) (𝓝 (relEntropy hρ.1 hσ.1)) := by
  rw [relEntropy_eq_spread hρ.1 hσ.1]
  refine Tendsto.congr
    (fun ε => (relEntropy_shift_formula hρ.1 hσ.1 ε _ _).symm) ?_
  refine Tendsto.sub ?_ ?_
  · exact tendsto_finsetSum _ fun i _ =>
      shift_klein_tendsto (hρ.1.eigenvalues i)
  · refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    exact shift_cross_tendsto _ _ _ (hρ.eigenvalues_nonneg i)
      (hσ.eigenvalues_nonneg j) (hsupp i j)

/-! ### Joint convexity at singular data -/

set_option maxHeartbeats 3200000 in -- regularised convexity passage
/-- **Joint convexity of the relative entropy at PSD data**
(Lieb–Lindblad, singular form): for probability weights and kernel
inclusions `ker σⱼ ⊆ ker ρⱼ`,
`D(Σλρ‖Σλσ) ≤ Σ λⱼ D(ρⱼ‖σⱼ)`. -/
theorem relEntropy_convex_psd {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ j, 0 ≤ lam j) (hsum : ∑ j, lam j = 1)
    {ρmat σmat : ι → Matrix n n ℂ}
    (hρj : ∀ j, (ρmat j).PosSemidef) (hσj : ∀ j, (σmat j).PosSemidef)
    (hker : ∀ j, ∀ v, σmat j *ᵥ v = 0 → ρmat j *ᵥ v = 0)
    (hρbar : (∑ j, lam j • ρmat j).PosSemidef)
    (hσbar : (∑ j, lam j • σmat j).PosSemidef) :
    relEntropy hρbar.1 hσbar.1 ≤
      ∑ j, lam j * relEntropy (hρj j).1 (hσj j).1 := by
  have hkerbar := ker_sum_smul hlam hσj hker
  have hL : Tendsto (fun ε : ℝ =>
      relEntropy (shift_isHermitian hρbar.1 ε)
        (shift_isHermitian hσbar.1 ε)) (𝓝[>] 0)
      (𝓝 (relEntropy hρbar.1 hσbar.1)) :=
    (relEntropy_shift_tendsto hρbar hσbar
      (supp_overlap_of_ker hρbar hσbar hkerbar)).mono_left
      nhdsWithin_le_nhds
  have hR : Tendsto (fun ε : ℝ => ∑ j, lam j *
      relEntropy (shift_isHermitian (hρj j).1 ε)
        (shift_isHermitian (hσj j).1 ε)) (𝓝[>] 0)
      (𝓝 (∑ j, lam j * relEntropy (hρj j).1 (hσj j).1)) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    exact (((relEntropy_shift_tendsto (hρj j) (hσj j)
      (supp_overlap_of_ker (hρj j) (hσj j) (hker j))).mono_left
      nhdsWithin_le_nhds).const_mul _)
  refine le_of_tendsto_of_tendsto hL hR ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  have hρj' : ∀ j, (ρmat j + ε • 1).PosDef := fun j =>
    posDef_add_smul_one (hρj j) hεpos
  have hσj' : ∀ j, (σmat j + ε • 1).PosDef := fun j =>
    posDef_add_smul_one (hσj j) hεpos
  have hρbar' : (∑ j, lam j • (ρmat j + ε • 1)).PosDef := by
    rw [sum_smul_shift lam hsum]
    exact posDef_add_smul_one hρbar hεpos
  have hσbar' : (∑ j, lam j • (σmat j + ε • 1)).PosDef := by
    rw [sum_smul_shift lam hsum]
    exact posDef_add_smul_one hσbar hεpos
  have hconv := relEntropy_convex_posDef hlam hρj' hσj' hρbar' hσbar'
  have hLcongr : relEntropy hρbar'.1 hσbar'.1 =
      relEntropy (shift_isHermitian hρbar.1 ε)
        (shift_isHermitian hσbar.1 ε) :=
    Petz.relEntropy_congr (sum_smul_shift lam hsum ρmat ε)
      (sum_smul_shift lam hsum σmat ε) hρbar'.1 hσbar'.1
      (shift_isHermitian hρbar.1 ε) (shift_isHermitian hσbar.1 ε)
  rw [hLcongr] at hconv
  exact hconv

end QRE
end NCG
