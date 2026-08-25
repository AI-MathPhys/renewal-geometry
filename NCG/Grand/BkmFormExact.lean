/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.AffineOpDecExact

/-!
# The BKM quadratic form and its joint convexity

Step (B3e) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
Bogoliubov–Kubo–Mori quadratic form

`g_σ(v,v) = Σᵢⱼ |v̂ᵢⱼ|² k(qᵢ, qⱼ)`

is the compact integral `∫₀¹ tQuad σ v t dt` of the affine quadratic
forms, hence **jointly convex** in `(σ, v)` — the analytic heart of the
BKM contraction QS.5.

* `bkmForm`: the BKM quadratic form;
* `bkmForm_eq_integral`: the affine integral representation;
* `tQuad_convex`: joint convexity at each `t` from the Schur lemma;
* `bkmForm_convex`: **joint convexity of the BKM form**.
-/

open Matrix Unitary Finset Filter MeasureTheory intervalIntegral
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ v S₁ S₂ : Matrix n n ℂ}

/-! ### The form and its integral representation -/

/-- **The BKM quadratic form** `g_σ(v,v) = Σᵢⱼ |v̂ᵢⱼ|² k(qᵢ,qⱼ)`. -/
noncomputable def bkmForm (hσ : σ.IsHermitian) (v : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (tangentIn hσ v i j) *
    bkmKernel (hσ.eigenvalues i) (hσ.eigenvalues j)

theorem invMat_congr (h : S₁ = S₂) (h₁ : S₁.IsHermitian)
    (h₂ : S₂.IsHermitian) : invMat h₁ = invMat h₂ := by
  subst h
  rfl

/-- Continuity of the affine sum integrand. -/
theorem sum_integrand_continuousOn (hσp : σ.PosDef) (v : Matrix n n ℂ) :
    ContinuousOn (fun t : ℝ =>
      ∑ i, ∑ j, Complex.normSq (tangentIn hσp.1 v i j) *
        (t * hσp.1.eigenvalues i +
          (1 - t) * hσp.1.eigenvalues j)⁻¹) (Set.uIcc (0:ℝ) 1) := by
  refine continuousOn_finsetSum _ fun i _ =>
    continuousOn_finsetSum _ fun j _ => ?_
  refine continuousOn_const.mul ?_
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      t * hσp.1.eigenvalues i + (1 - t) * hσp.1.eigenvalues j ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact (affine_pos (hσp.eigenvalues_pos i) (hσp.eigenvalues_pos j)
      ht.1 ht.2).ne'
  exact (((continuousOn_id.mul continuousOn_const)).add
    ((continuousOn_const.sub continuousOn_id).mul
      continuousOn_const)).inv₀ hmem

/-- Interval integrability of the affine sum integrand. -/
theorem sum_integrand_integrable (hσp : σ.PosDef) (v : Matrix n n ℂ) :
    IntervalIntegrable (fun t : ℝ =>
      ∑ i, ∑ j, Complex.normSq (tangentIn hσp.1 v i j) *
        (t * hσp.1.eigenvalues i +
          (1 - t) * hσp.1.eigenvalues j)⁻¹) volume 0 1 :=
  (sum_integrand_continuousOn hσp v).intervalIntegrable

set_option maxHeartbeats 1600000 in -- integral assembly
/-- **The affine integral representation of the BKM form**:
`g_σ(v,v) = ∫₀¹ Σᵢⱼ |v̂ᵢⱼ|² (t·qᵢ + (1−t)·qⱼ)⁻¹ dt`. -/
theorem bkmForm_eq_integral (hσp : σ.PosDef) (v : Matrix n n ℂ) :
    bkmForm hσp.1 v =
      ∫ t in (0:ℝ)..1,
        ∑ i, ∑ j, Complex.normSq (tangentIn hσp.1 v i j) *
          (t * hσp.1.eigenvalues i +
            (1 - t) * hσp.1.eigenvalues j)⁻¹ := by
  have hIntPer : ∀ p : n × n, IntervalIntegrable (fun t : ℝ =>
      Complex.normSq (tangentIn hσp.1 v p.1 p.2) *
        (t * hσp.1.eigenvalues p.1 +
          (1 - t) * hσp.1.eigenvalues p.2)⁻¹) volume 0 1 := by
    intro p
    exact (affine_integrable (hσp.eigenvalues_pos p.1)
      (hσp.eigenvalues_pos p.2)).const_mul _
  have hcongr : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      (∑ i, ∑ j, Complex.normSq (tangentIn hσp.1 v i j) *
        (t * hσp.1.eigenvalues i +
          (1 - t) * hσp.1.eigenvalues j)⁻¹) =
      ∑ p : n × n, Complex.normSq (tangentIn hσp.1 v p.1 p.2) *
        (t * hσp.1.eigenvalues p.1 +
          (1 - t) * hσp.1.eigenvalues p.2)⁻¹ := by
    intro t _
    exact (Fintype.sum_prod_type
      (f := fun p : n × n => Complex.normSq (tangentIn hσp.1 v p.1 p.2) *
        (t * hσp.1.eigenvalues p.1 +
          (1 - t) * hσp.1.eigenvalues p.2)⁻¹)).symm
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_finsetSum (fun p _ => hIntPer p)]
  unfold bkmForm
  rw [← Fintype.sum_prod_type
    (f := fun p : n × n => Complex.normSq (tangentIn hσp.1 v p.1 p.2) *
      bkmKernel (hσp.1.eigenvalues p.1) (hσp.1.eigenvalues p.2))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [intervalIntegral.integral_const_mul]
  rw [integral_affine (hσp.eigenvalues_pos p.1)
    (hσp.eigenvalues_pos p.2)]

/-! ### Joint convexity of the t-forms -/

set_option maxHeartbeats 1600000 in -- Schur transfer
/-- **Joint convexity of the affine quadratic form** at each
`t ∈ [0,1]`, from the Schur lemma. -/
theorem tQuad_convex {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ j, 0 ≤ lam j) {σs vs : ι → Matrix n n ℂ}
    (hσj : ∀ j, (σs j).PosDef)
    (hσbar : (∑ j, lam j • σs j).PosDef) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    tQuad hσbar.1 (∑ j, lam j • vs j) t ≤
      ∑ j, lam j * tQuad (hσj j).1 (vs j) t := by
  have hPj : ∀ j, (affineOp (σs j) t).PosDef := fun j =>
    affineOp_posDef (hσj j) ht0 ht1
  have hPbar : (∑ j, lam j • affineOp (σs j) t).PosDef := by
    rw [affineOp_linear]
    exact affineOp_posDef hσbar ht0 ht1
  have hconv := quadForm_convex hlam (xvec := fun j => vecM (vs j))
    hPj hPbar
  unfold tQuad
  rw [vecM_sum_smul]
  rw [invMat_congr (affineOp_linear lam σs t).symm
    (affineOp_isHermitian hσbar.1 t) hPbar.1]
  exact hconv

/-! ### Joint convexity of the BKM form -/

set_option maxHeartbeats 3200000 in -- integral comparison assembly
/-- **Joint convexity of the BKM quadratic form** (the analytic heart of
QS.5): for probability-free nonnegative weights, faithful states and
arbitrary tangents,
`g_σ̄(v̄,v̄) ≤ Σ λⱼ g_σⱼ(vⱼ,vⱼ)`. -/
theorem bkmForm_convex {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ j, 0 ≤ lam j) {σs vs : ι → Matrix n n ℂ}
    (hσj : ∀ j, (σs j).PosDef)
    (hσbar : (∑ j, lam j • σs j).PosDef) :
    bkmForm hσbar.1 (∑ j, lam j • vs j) ≤
      ∑ j, lam j * bkmForm (hσj j).1 (vs j) := by
  rw [bkmForm_eq_integral hσbar]
  have hR : ∑ j, lam j * bkmForm (hσj j).1 (vs j) =
      ∫ t in (0:ℝ)..1, ∑ j, lam j *
        (∑ i, ∑ i', Complex.normSq (tangentIn (hσj j).1 (vs j) i i') *
          (t * (hσj j).1.eigenvalues i +
            (1 - t) * (hσj j).1.eigenvalues i')⁻¹) := by
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
      (sum_integrand_integrable (hσj j) (vs j)).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul,
      ← bkmForm_eq_integral (hσj j) (vs j)]
  rw [hR]
  refine intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (sum_integrand_integrable hσbar _) ?_ ?_
  · apply ContinuousOn.intervalIntegrable
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact continuousOn_const.mul
      (sum_integrand_continuousOn (hσj j) (vs j))
  · intro t ht
    have h1 := tQuad_eq_sum hσbar (∑ j, lam j • vs j) ht.1 ht.2
    have h2 := tQuad_convex hlam hσj hσbar ht.1 ht.2 (vs := vs)
    rw [← h1]
    refine h2.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tQuad_eq_sum (hσj j) (vs j) ht.1 ht.2]

end QRE
end NCG
