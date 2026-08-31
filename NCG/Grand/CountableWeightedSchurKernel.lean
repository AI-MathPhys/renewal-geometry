/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Countable weighted Schur kernels

This file supplies the countable, rather than merely finite, convolution
algebra underlying the weighted-locality part of the Gran--Tensor manuscript.
The extended nonnegative norm is used internally so that arbitrary countable
sums and possibly non-Schur kernels are represented without a summability
side condition.  The finite-norm subspace is extracted below.
-/

open scoped ENNReal

namespace NCG
namespace CountableWeightedSchurKernel

variable {Γ : Type*}

/-! ## Finite-support Schur estimate

This estimate is stated on arbitrary finite subsets of a possibly countable
index type.  Its constant is independent of those subsets, which is the
input needed for the dense extension of kernel multiplication to l2. -/

/-- Uniform Schur estimate for finite input and output supports. -/
theorem finiteSupport_schur_sq_bound
    (K : Γ → Γ → ℂ) (f : Γ → ℂ) (s t : Finset Γ)
    (R C : ℝ) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (hRsum : ∀ x, Summable fun y => ‖K x y‖)
    (hCsum : ∀ y, Summable fun x => ‖K x y‖)
    (hR : ∀ x, ∑' y, ‖K x y‖ ≤ R)
    (hC : ∀ y, ∑' x, ‖K x y‖ ≤ C) :
    ∑ x ∈ s, ‖∑ y ∈ t, K x y * f y‖ ^ 2
      ≤ R * C * ∑ y ∈ t, ‖f y‖ ^ 2 := by
  have hentry : ∀ x,
      ‖∑ y ∈ t, K x y * f y‖
        ≤ ∑ y ∈ t, ‖K x y‖ * ‖f y‖ := by
    intro x
    exact (norm_sum_le _ _).trans_eq
      (Finset.sum_congr rfl fun y _ => norm_mul _ _)
  have hrow : ∀ x,
      ‖∑ y ∈ t, K x y * f y‖ ^ 2
        ≤ R * ∑ y ∈ t, ‖K x y‖ * ‖f y‖ ^ 2 := by
    intro x
    have h1 :
        ‖∑ y ∈ t, K x y * f y‖ ^ 2
          ≤ (∑ y ∈ t, ‖K x y‖ * ‖f y‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (hentry x) 2
    have hcs := Real.sum_sqrt_mul_sqrt_le t
      (f := fun y => ‖K x y‖)
      (g := fun y => ‖K x y‖ * ‖f y‖ ^ 2)
      (fun y => norm_nonneg _)
      (fun y => mul_nonneg (norm_nonneg _) (sq_nonneg _))
    have hterm : ∀ y,
        Real.sqrt ‖K x y‖
            * Real.sqrt (‖K x y‖ * ‖f y‖ ^ 2)
          = ‖K x y‖ * ‖f y‖ := by
      intro y
      rw [Real.sqrt_mul (norm_nonneg _), ← mul_assoc,
        Real.mul_self_sqrt (norm_nonneg _),
        Real.sqrt_sq (norm_nonneg _)]
    have h2 :
        (∑ y ∈ t, ‖K x y‖ * ‖f y‖) ^ 2
          ≤ (∑ y ∈ t, ‖K x y‖)
              * ∑ y ∈ t, ‖K x y‖ * ‖f y‖ ^ 2 := by
      rw [Finset.sum_congr rfl fun y _ => (hterm y).symm]
      have hleft : 0 ≤ ∑ y ∈ t,
          Real.sqrt ‖K x y‖
            * Real.sqrt (‖K x y‖ * ‖f y‖ ^ 2) :=
        Finset.sum_nonneg fun y _ =>
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      calc
        (∑ y ∈ t, Real.sqrt ‖K x y‖
            * Real.sqrt (‖K x y‖ * ‖f y‖ ^ 2)) ^ 2
            ≤ (Real.sqrt (∑ y ∈ t, ‖K x y‖)
                * Real.sqrt
                  (∑ y ∈ t, ‖K x y‖ * ‖f y‖ ^ 2)) ^ 2 :=
              pow_le_pow_left₀ hleft hcs 2
        _ = (∑ y ∈ t, ‖K x y‖)
              * ∑ y ∈ t, ‖K x y‖ * ‖f y‖ ^ 2 := by
            rw [mul_pow,
              Real.sq_sqrt (Finset.sum_nonneg fun y _ => norm_nonneg _),
              Real.sq_sqrt (Finset.sum_nonneg fun y _ =>
                mul_nonneg (norm_nonneg _) (sq_nonneg _))]
    have hfinite : ∑ y ∈ t, ‖K x y‖ ≤ R :=
      ((hRsum x).sum_le_tsum t fun y _ => norm_nonneg _).trans (hR x)
    exact h1.trans (h2.trans
      (mul_le_mul_of_nonneg_right hfinite
        (Finset.sum_nonneg fun y _ =>
          mul_nonneg (norm_nonneg _) (sq_nonneg _))))
  calc
    ∑ x ∈ s, ‖∑ y ∈ t, K x y * f y‖ ^ 2
        ≤ ∑ x ∈ s, R * ∑ y ∈ t, ‖K x y‖ * ‖f y‖ ^ 2 :=
      Finset.sum_le_sum fun x _ => hrow x
    _ = R * (∑ x ∈ s, ∑ y ∈ t,
          ‖K x y‖ * ‖f y‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ = R * (∑ y ∈ t, ∑ x ∈ s,
          ‖K x y‖ * ‖f y‖ ^ 2) := by
      rw [Finset.sum_comm]
    _ = R * ∑ y ∈ t,
          (∑ x ∈ s, ‖K x y‖) * ‖f y‖ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_mul]
    _ ≤ R * ∑ y ∈ t, C * ‖f y‖ ^ 2 := by
      gcongr with y hy
      have hfinite : ∑ x ∈ s, ‖K x y‖ ≤ C :=
        ((hCsum y).sum_le_tsum s fun x _ => norm_nonneg _).trans (hC y)
      exact hfinite
    _ = R * C * ∑ y ∈ t, ‖f y‖ ^ 2 := by
      rw [← Finset.mul_sum]
      ring

/-- Finite input/output truncation of a kernel as an operator on the full
countable l2 space.  It is assembled from coordinate evaluation and
coordinate insertion maps, so boundedness is automatic before the uniform
Schur estimate is applied. -/
noncomputable def truncatedKernelOperator [DecidableEq Γ]
    (K : Γ → Γ → ℂ) (s t : Finset Γ) :
    lp (fun _ : Γ => ℂ) 2 →L[ℂ] lp (fun _ : Γ => ℂ) 2 :=
  ∑ x ∈ s, ∑ y ∈ t, K x y •
    ((lp.singleContinuousLinearMap ℂ (fun _ : Γ => ℂ) 2 x).comp
      (lp.evalCLM ℂ (fun _ : Γ => ℂ) 2 y))

@[simp]
theorem truncatedKernelOperator_apply [DecidableEq Γ]
    (K : Γ → Γ → ℂ) (s t : Finset Γ)
    (f : lp (fun _ : Γ => ℂ) 2) :
    truncatedKernelOperator K s t f =
      ∑ x ∈ s, lp.single 2 x (∑ y ∈ t, K x y * f y) := by
  unfold truncatedKernelOperator
  simp only [_root_.sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    lp.evalCLM]
  apply Finset.sum_congr rfl
  intro x hx
  let S := lp.singleContinuousLinearMap ℂ (fun _ : Γ => ℂ) 2 x
  change ∑ y ∈ t, K x y • S (f y) =
    S (∑ y ∈ t, K x y * f y)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro y hy
  simpa [smul_eq_mul] using
    (S.map_smul (K x y) (f y)).symm

/-- Every finite truncation has the same l2 bound, independently of its
input and output supports. -/
theorem truncatedKernelOperator_apply_norm_le [DecidableEq Γ]
    (K : Γ → Γ → ℂ) (s t : Finset Γ) (M : ℝ) (hM0 : 0 ≤ M)
    (hRsum : ∀ x, Summable fun y => ‖K x y‖)
    (hCsum : ∀ y, Summable fun x => ‖K x y‖)
    (hR : ∀ x, ∑' y, ‖K x y‖ ≤ M)
    (hC : ∀ y, ∑' x, ‖K x y‖ ≤ M)
    (f : lp (fun _ : Γ => ℂ) 2) :
    ‖truncatedKernelOperator K s t f‖ ≤ M * ‖f‖ := by
  have hnorm := lp.norm_sum_single
    (p := (2 : ℝ≥0∞)) (E := fun _ : Γ => ℂ)
    (by norm_num)
    (fun x => ∑ y ∈ t, K x y * f y) s
  norm_num at hnorm
  have houtSq : ‖truncatedKernelOperator K s t f‖ ^ 2
      ≤ M ^ 2 * ‖f‖ ^ 2 := by
    rw [truncatedKernelOperator_apply, hnorm]
    have hfinite := finiteSupport_schur_sq_bound K (fun y => f y)
      s t M M hM0 hM0 hRsum hCsum hR hC
    have hin := lp.sum_rpow_le_norm_rpow
      (p := (2 : ℝ≥0∞)) (by norm_num) f t
    norm_num at hin
    calc
      ∑ x ∈ s, ‖∑ y ∈ t, K x y * f y‖ ^ 2
          ≤ M * M * ∑ y ∈ t, ‖f y‖ ^ 2 := hfinite
      _ ≤ M * M * ‖f‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hin (mul_nonneg hM0 hM0)
      _ = M ^ 2 * ‖f‖ ^ 2 := by ring
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hM0 (norm_nonneg f))).mp
  simpa [mul_pow] using houtSq

/-- Operator norm form of the uniform finite-truncation Schur estimate. -/
theorem truncatedKernelOperator_norm_le [DecidableEq Γ]
    (K : Γ → Γ → ℂ) (s t : Finset Γ) (M : ℝ) (hM0 : 0 ≤ M)
    (hRsum : ∀ x, Summable fun y => ‖K x y‖)
    (hCsum : ∀ y, Summable fun x => ‖K x y‖)
    (hR : ∀ x, ∑' y, ‖K x y‖ ≤ M)
    (hC : ∀ y, ∑' x, ‖K x y‖ ≤ M) :
    ‖truncatedKernelOperator K s t‖ ≤ M := by
  exact ContinuousLinearMap.opNorm_le_bound _
    hM0 (truncatedKernelOperator_apply_norm_le
      K s t M hM0 hRsum hCsum hR hC)

/-! ## Dense finite-support realization -/

/-- The canonical linear inclusion of finitely supported scalar families
into countable l2. -/
noncomputable def finsuppToL2 :
    Finsupp Γ ℂ →ₗ[ℂ] lp (fun _ : Γ => ℂ) 2 := by
  classical
  exact Finsupp.lsum ℂ fun i =>
    lp.lsingle (𝕜 := ℂ) (E := fun _ : Γ => ℂ) 2 i

/-- Finitely supported families are dense in countable l2. -/
theorem denseRange_finsuppToL2 :
    DenseRange (finsuppToL2 (Γ := Γ)) := by
  classical
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro f
  have hsum := lp.hasSum_single
    (p := (2 : ℝ≥0∞)) (E := fun _ : Γ => ℂ)
    ENNReal.ofNat_ne_top f
  apply isClosed_closure.mem_of_tendsto hsum
  filter_upwards [] with s
  apply subset_closure
  refine ⟨∑ i ∈ s, Finsupp.single i (f i), ?_⟩
  simp [map_sum, finsuppToL2, Finsupp.lsum_single]

theorem finsuppToL2_norm_sq (v : Finsupp Γ ℂ) :
    ‖finsuppToL2 (Γ := Γ) v‖ ^ 2 =
      ∑ i ∈ v.support, ‖v i‖ ^ 2 := by
  classical
  rw [finsuppToL2, Finsupp.lsum_apply]
  change ‖∑ i ∈ v.support,
    lp.single (E := fun _ : Γ => ℂ) 2 i (v i)‖ ^ 2 = _
  simpa using lp.norm_sum_single
    (p := (2 : ℝ≥0∞)) (E := fun _ : Γ => ℂ)
    (by norm_num) (fun i => v i) v.support

/-- A single kernel column, viewed as a linear map into all scalar
families. -/
def kernelColumnLinearMap (K : Γ → Γ → ℂ) (y : Γ) :
    ℂ →ₗ[ℂ] (Γ → ℂ) where
  toFun a x := K x y * a
  map_add' a b := by
    funext x
    exact mul_add _ _ _
  map_smul' c a := by
    funext x
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- Algebraic kernel action on finitely supported vectors, before
proving that its output lies in l2. -/
noncomputable def rawKernelFinsuppLinearMap (K : Γ → Γ → ℂ) :
    Finsupp Γ ℂ →ₗ[ℂ] (Γ → ℂ) :=
  Finsupp.lsum ℂ (kernelColumnLinearMap K)

theorem rawKernelFinsuppLinearMap_apply
    (K : Γ → Γ → ℂ) (v : Finsupp Γ ℂ) (x : Γ) :
    rawKernelFinsuppLinearMap K v x =
      ∑ y ∈ v.support, K x y * v y := by
  rw [rawKernelFinsuppLinearMap, Finsupp.lsum_apply]
  simp [Finsupp.sum, kernelColumnLinearMap]

theorem rawKernelFinsuppLinearMap_memL2
    (K : Γ → Γ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hRsum : ∀ x, Summable fun y => ‖K x y‖)
    (hCsum : ∀ y, Summable fun x => ‖K x y‖)
    (hR : ∀ x, ∑' y, ‖K x y‖ ≤ M)
    (hC : ∀ y, ∑' x, ‖K x y‖ ≤ M)
    (v : Finsupp Γ ℂ) :
    Memℓp (rawKernelFinsuppLinearMap K v) 2 := by
  apply memℓp_gen'
    (C := M * M * ∑ y ∈ v.support, ‖v y‖ ^ 2)
  intro s
  norm_num
  simpa only [rawKernelFinsuppLinearMap_apply] using
    finiteSupport_schur_sq_bound K (fun y => v y)
      s v.support M M hM0 hM0 hRsum hCsum hR hC

/-- The algebraic kernel action on finite-support vectors, now valued in
l2 by the uniform Schur estimate. -/
noncomputable def kernelFinsuppLinearMap
    (K : Γ → Γ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hRsum : ∀ x, Summable fun y => ‖K x y‖)
    (hCsum : ∀ y, Summable fun x => ‖K x y‖)
    (hR : ∀ x, ∑' y, ‖K x y‖ ≤ M)
    (hC : ∀ y, ∑' x, ‖K x y‖ ≤ M) :
    Finsupp Γ ℂ →ₗ[ℂ] lp (fun _ : Γ => ℂ) 2 where
  toFun v := ⟨rawKernelFinsuppLinearMap K v,
    rawKernelFinsuppLinearMap_memL2 K M hM0
      hRsum hCsum hR hC v⟩
  map_add' v w := by
    apply Subtype.ext
    exact (rawKernelFinsuppLinearMap K).map_add v w
  map_smul' c v := by
    apply Subtype.ext
    exact (rawKernelFinsuppLinearMap K).map_smul c v

@[simp]
theorem kernelFinsuppLinearMap_apply
    (K : Γ → Γ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hRsum : ∀ x, Summable fun y => ‖K x y‖)
    (hCsum : ∀ y, Summable fun x => ‖K x y‖)
    (hR : ∀ x, ∑' y, ‖K x y‖ ≤ M)
    (hC : ∀ y, ∑' x, ‖K x y‖ ≤ M)
    (v : Finsupp Γ ℂ) (x : Γ) :
    kernelFinsuppLinearMap K M hM0 hRsum hCsum hR hC v x =
      ∑ y ∈ v.support, K x y * v y :=
  rawKernelFinsuppLinearMap_apply K v x

theorem kernelFinsuppLinearMap_norm_le
    (K : Γ → Γ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hRsum : ∀ x, Summable fun y => ‖K x y‖)
    (hCsum : ∀ y, Summable fun x => ‖K x y‖)
    (hR : ∀ x, ∑' y, ‖K x y‖ ≤ M)
    (hC : ∀ y, ∑' x, ‖K x y‖ ≤ M)
    (v : Finsupp Γ ℂ) :
    ‖kernelFinsuppLinearMap K M hM0 hRsum hCsum hR hC v‖
      ≤ M * ‖finsuppToL2 v‖ := by
  apply lp.norm_le_of_forall_sum_le
    (p := (2 : ℝ≥0∞)) (by norm_num)
    (mul_nonneg hM0 (norm_nonneg _))
  intro s
  norm_num
  change (∑ x ∈ s,
    ‖∑ y ∈ v.support, K x y * v y‖ ^ 2)
      ≤ (M * ‖finsuppToL2 v‖) ^ 2
  calc
    (∑ x ∈ s, ‖∑ y ∈ v.support, K x y * v y‖ ^ 2)
        ≤ M * M * ∑ y ∈ v.support, ‖v y‖ ^ 2 :=
      finiteSupport_schur_sq_bound K (fun y => v y)
        s v.support M M hM0 hM0 hRsum hCsum hR hC
    _ = (M * ‖finsuppToL2 v‖) ^ 2 := by
      rw [← finsuppToL2_norm_sq]
      ring

/-! ## Bounded operator induced by a countable Schur kernel -/

/-- The bounded l2 operator obtained by extending kernel multiplication
from the dense finite-support subspace. -/
noncomputable def kernelOperator
    (K : Γ → Γ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hRsum : ∀ x, Summable fun y => ‖K x y‖)
    (hCsum : ∀ y, Summable fun x => ‖K x y‖)
    (hR : ∀ x, ∑' y, ‖K x y‖ ≤ M)
    (hC : ∀ y, ∑' x, ‖K x y‖ ≤ M) :
    lp (fun _ : Γ => ℂ) 2 →L[ℂ] lp (fun _ : Γ => ℂ) 2 :=
  (kernelFinsuppLinearMap K M hM0 hRsum hCsum hR hC).extendOfNorm
    finsuppToL2

theorem kernelOperator_on_finsupp
    (K : Γ → Γ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hRsum : ∀ x, Summable fun y => ‖K x y‖)
    (hCsum : ∀ y, Summable fun x => ‖K x y‖)
    (hR : ∀ x, ∑' y, ‖K x y‖ ≤ M)
    (hC : ∀ y, ∑' x, ‖K x y‖ ≤ M)
    (v : Finsupp Γ ℂ) :
    kernelOperator K M hM0 hRsum hCsum hR hC (finsuppToL2 v) =
      kernelFinsuppLinearMap K M hM0 hRsum hCsum hR hC v := by
  apply LinearMap.extendOfNorm_eq denseRange_finsuppToL2
  exact ⟨M, kernelFinsuppLinearMap_norm_le
    K M hM0 hRsum hCsum hR hC⟩

/-- Countable Schur's test in operator-norm form. -/
theorem kernelOperator_norm_le
    (K : Γ → Γ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hRsum : ∀ x, Summable fun y => ‖K x y‖)
    (hCsum : ∀ y, Summable fun x => ‖K x y‖)
    (hR : ∀ x, ∑' y, ‖K x y‖ ≤ M)
    (hC : ∀ y, ∑' x, ‖K x y‖ ≤ M) :
    ‖kernelOperator K M hM0 hRsum hCsum hR hC‖ ≤ M := by
  exact LinearMap.opNorm_extendOfNorm_le
    denseRange_finsuppToL2 hM0
    (kernelFinsuppLinearMap_norm_le
      K M hM0 hRsum hCsum hR hC)

theorem kernelOperator_on_finsupp_apply
    (K : Γ → Γ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hRsum : ∀ x, Summable fun y => ‖K x y‖)
    (hCsum : ∀ y, Summable fun x => ‖K x y‖)
    (hR : ∀ x, ∑' y, ‖K x y‖ ≤ M)
    (hC : ∀ y, ∑' x, ‖K x y‖ ≤ M)
    (v : Finsupp Γ ℂ) (x : Γ) :
    kernelOperator K M hM0 hRsum hCsum hR hC (finsuppToL2 v) x =
      ∑ y ∈ v.support, K x y * v y := by
  rw [kernelOperator_on_finsupp]
  exact kernelFinsuppLinearMap_apply
    K M hM0 hRsum hCsum hR hC v x

/-- The weighted row sum of a nonnegative scalar kernel. -/
noncomputable def row (w K : Γ → Γ → ℝ≥0∞) (x : Γ) : ℝ≥0∞ :=
  ∑' y, w x y * K x y

/-- The weighted column sum of a nonnegative scalar kernel. -/
noncomputable def col (w K : Γ → Γ → ℝ≥0∞) (y : Γ) : ℝ≥0∞ :=
  ∑' x, w x y * K x y

/-- The extended weighted Schur norm.  It is meaningful for every kernel;
membership in the weighted Schur algebra is the assertion that it is finite. -/
noncomputable def eNorm (w K : Γ → Γ → ℝ≥0∞) : ℝ≥0∞ :=
  max (⨆ x, row w K x) (⨆ y, col w K y)

/-- Absolute-kernel convolution. -/
noncomputable def comp (S T : Γ → Γ → ℝ≥0∞) : Γ → Γ → ℝ≥0∞ :=
  fun x y => ∑' z, S x z * T z y

/-- Absolute kernel of the adjoint. -/
def adj (K : Γ → Γ → ℝ≥0∞) : Γ → Γ → ℝ≥0∞ :=
  fun x y => K y x

theorem row_le_eNorm (w K : Γ → Γ → ℝ≥0∞) (x : Γ) :
    row w K x ≤ eNorm w K :=
  (le_iSup (fun x => row w K x) x).trans (le_max_left _ _)

theorem col_le_eNorm (w K : Γ → Γ → ℝ≥0∞) (y : Γ) :
    col w K y ≤ eNorm w K :=
  (le_iSup (fun y => col w K y) y).trans (le_max_right _ _)

theorem row_mono (w K L : Γ → Γ → ℝ≥0∞)
    (hKL : ∀ x y, K x y ≤ L x y) (x : Γ) :
    row w K x ≤ row w L x := by
  exact ENNReal.tsum_le_tsum fun y => mul_le_mul_right (hKL x y) _

theorem col_mono (w K L : Γ → Γ → ℝ≥0∞)
    (hKL : ∀ x y, K x y ≤ L x y) (y : Γ) :
    col w K y ≤ col w L y := by
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul_right (hKL x y) _

theorem eNorm_mono (w K L : Γ → Γ → ℝ≥0∞)
    (hKL : ∀ x y, K x y ≤ L x y) :
    eNorm w K ≤ eNorm w L := by
  unfold eNorm
  apply max_le
  · refine iSup_le fun x => ?_
    exact (row_mono w K L hKL x).trans
      ((le_iSup (fun x => row w L x) x).trans (le_max_left _ _))
  · refine iSup_le fun y => ?_
    exact (col_mono w K L hKL y).trans
      ((le_iSup (fun y => col w L y) y).trans (le_max_right _ _))

/-- Row half of countable weighted-Schur submultiplicativity. -/
theorem row_comp_le (w S T : Γ → Γ → ℝ≥0∞)
    (hw : ∀ x z y, w x y ≤ w x z * w z y) (x : Γ) :
    row w (comp S T) x ≤ eNorm w S * eNorm w T := by
  unfold row comp
  calc
    (∑' y, w x y * ∑' z, S x z * T z y)
        = ∑' y, ∑' z, w x y * (S x z * T z y) := by
            congr 1
            funext y
            exact ENNReal.tsum_mul_left.symm
    _ ≤ ∑' y, ∑' z,
          (w x z * S x z) * (w z y * T z y) := by
            exact ENNReal.tsum_le_tsum fun y =>
              ENNReal.tsum_le_tsum fun z => by
                calc
                  w x y * (S x z * T z y)
                      ≤ (w x z * w z y) * (S x z * T z y) :=
                        mul_le_mul_left (hw x z y) _
                  _ = (w x z * S x z) * (w z y * T z y) := by
                        ac_rfl
    _ = ∑' z, ∑' y,
          (w x z * S x z) * (w z y * T z y) := ENNReal.tsum_comm
    _ = ∑' z, (w x z * S x z) * (∑' y, w z y * T z y) := by
          congr 1
          funext z
          exact ENNReal.tsum_mul_left
    _ ≤ ∑' z, (w x z * S x z) * eNorm w T := by
          exact ENNReal.tsum_le_tsum fun z =>
            mul_le_mul_right (row_le_eNorm w T z) _
    _ = (∑' z, w x z * S x z) * eNorm w T := ENNReal.tsum_mul_right
    _ ≤ eNorm w S * eNorm w T :=
      mul_le_mul_left (row_le_eNorm w S x) _

/-- Column half of countable weighted-Schur submultiplicativity. -/
theorem col_comp_le (w S T : Γ → Γ → ℝ≥0∞)
    (hw : ∀ x z y, w x y ≤ w x z * w z y) (y : Γ) :
    col w (comp S T) y ≤ eNorm w S * eNorm w T := by
  unfold col comp
  calc
    (∑' x, w x y * ∑' z, S x z * T z y)
        = ∑' x, ∑' z, w x y * (S x z * T z y) := by
            congr 1
            funext x
            exact ENNReal.tsum_mul_left.symm
    _ ≤ ∑' x, ∑' z,
          (w x z * S x z) * (w z y * T z y) := by
            exact ENNReal.tsum_le_tsum fun x =>
              ENNReal.tsum_le_tsum fun z => by
                calc
                  w x y * (S x z * T z y)
                      ≤ (w x z * w z y) * (S x z * T z y) :=
                        mul_le_mul_left (hw x z y) _
                  _ = (w x z * S x z) * (w z y * T z y) := by
                        ac_rfl
    _ = ∑' z, ∑' x,
          (w x z * S x z) * (w z y * T z y) := ENNReal.tsum_comm
    _ = ∑' z, (∑' x, w x z * S x z) * (w z y * T z y) := by
          congr 1
          funext z
          exact ENNReal.tsum_mul_right
    _ ≤ ∑' z, eNorm w S * (w z y * T z y) := by
          exact ENNReal.tsum_le_tsum fun z =>
            mul_le_mul_left (col_le_eNorm w S z) _
    _ = eNorm w S * (∑' z, w z y * T z y) := ENNReal.tsum_mul_left
    _ ≤ eNorm w S * eNorm w T :=
      mul_le_mul_right (col_le_eNorm w T y) _

/-- Countable weighted-Schur convolution estimate. -/
theorem eNorm_comp_le (w S T : Γ → Γ → ℝ≥0∞)
    (hw : ∀ x z y, w x y ≤ w x z * w z y) :
    eNorm w (comp S T) ≤ eNorm w S * eNorm w T := by
  unfold eNorm
  apply max_le
  · exact iSup_le fun x => row_comp_le w S T hw x
  · exact iSup_le fun y => col_comp_le w S T hw y

theorem row_adj (w K : Γ → Γ → ℝ≥0∞)
    (hsymm : ∀ x y, w x y = w y x) (x : Γ) :
    row w (adj K) x = col w K x := by
  apply tsum_congr
  intro y
  simp only [adj, col]
  rw [hsymm]

theorem col_adj (w K : Γ → Γ → ℝ≥0∞)
    (hsymm : ∀ x y, w x y = w y x) (y : Γ) :
    col w (adj K) y = row w K y := by
  apply tsum_congr
  intro x
  simp only [adj, row]
  rw [hsymm]

/-- Adjoint invariance of the countable weighted-Schur norm. -/
theorem eNorm_adj (w K : Γ → Γ → ℝ≥0∞)
    (hsymm : ∀ x y, w x y = w y x) :
    eNorm w (adj K) = eNorm w K := by
  unfold eNorm
  simp_rw [row_adj w K hsymm, col_adj w K hsymm]
  exact max_comm _ _

/-- The genuine weighted Schur algebra consists of the kernels with finite
extended norm. -/
def Mem (w K : Γ → Γ → ℝ≥0∞) : Prop :=
  eNorm w K ≠ ∞

theorem mem_comp (w S T : Γ → Γ → ℝ≥0∞)
    (hw : ∀ x z y, w x y ≤ w x z * w z y)
    (hS : Mem w S) (hT : Mem w T) :
    Mem w (comp S T) := by
  intro htop
  have hle := eNorm_comp_le w S T hw
  rw [htop] at hle
  have hprod : eNorm w S * eNorm w T ≠ ∞ :=
    ENNReal.mul_ne_top hS hT
  exact hprod (top_unique hle)

theorem mem_adj (w K : Γ → Γ → ℝ≥0∞)
    (hsymm : ∀ x y, w x y = w y x) (hK : Mem w K) :
    Mem w (adj K) := by
  rw [Mem, eNorm_adj w K hsymm]
  exact hK

/-! ## Complex kernels

The following layer turns the absolute-kernel algebra above into the actual
complex convolution algebra.  Infinite summation is total in Lean, and the
extended-norm estimate is valid even before summability is known.  Finite
Schur norm then implies absolute summability of every convolution entry.
-/

/-- Entrywise extended norm of a complex kernel. -/
noncomputable def enormKernel (K : Γ → Γ → ℂ) : Γ → Γ → ℝ≥0∞ :=
  fun x y => ‖K x y‖ₑ

/-- Countable complex-kernel convolution. -/
noncomputable def kernelComp (S T : Γ → Γ → ℂ) : Γ → Γ → ℂ :=
  fun x y => ∑' z, S x z * T z y

/-- Complex adjoint kernel. -/
noncomputable def kernelAdj (K : Γ → Γ → ℂ) : Γ → Γ → ℂ :=
  fun x y => star (K y x)

/-- Extended weighted Schur norm of a complex kernel. -/
noncomputable def complexENorm (w : Γ → Γ → ℝ≥0∞)
    (K : Γ → Γ → ℂ) : ℝ≥0∞ :=
  eNorm w (enormKernel K)

theorem enormKernel_kernelComp_le (S T : Γ → Γ → ℂ) (x y : Γ) :
    enormKernel (kernelComp S T) x y ≤
      comp (enormKernel S) (enormKernel T) x y := by
  unfold enormKernel kernelComp comp
  simpa only [enorm_mul] using
    (enorm_tsum_le_tsum_enorm (f := fun z => S x z * T z y))

/-- Countable complex weighted-Schur submultiplicativity. -/
theorem complexENorm_comp_le (w : Γ → Γ → ℝ≥0∞)
    (S T : Γ → Γ → ℂ)
    (hw : ∀ x z y, w x y ≤ w x z * w z y) :
    complexENorm w (kernelComp S T) ≤
      complexENorm w S * complexENorm w T := by
  calc
    complexENorm w (kernelComp S T)
        ≤ eNorm w (comp (enormKernel S) (enormKernel T)) :=
          eNorm_mono w _ _ (enormKernel_kernelComp_le S T)
    _ ≤ complexENorm w S * complexENorm w T :=
      eNorm_comp_le w (enormKernel S) (enormKernel T) hw

theorem enormKernel_kernelAdj (K : Γ → Γ → ℂ) :
    enormKernel (kernelAdj K) = adj (enormKernel K) := by
  funext x y
  simp [enormKernel, kernelAdj, adj]

/-- Adjoint invariance for complex countable kernels. -/
theorem complexENorm_adj (w : Γ → Γ → ℝ≥0∞)
    (K : Γ → Γ → ℂ) (hsymm : ∀ x y, w x y = w y x) :
    complexENorm w (kernelAdj K) = complexENorm w K := by
  unfold complexENorm
  rw [enormKernel_kernelAdj, eNorm_adj w _ hsymm]

/-- Complex kernels belonging to the countable weighted Schur algebra. -/
def ComplexMem (w : Γ → Γ → ℝ≥0∞) (K : Γ → Γ → ℂ) : Prop :=
  complexENorm w K ≠ ∞

theorem complexMem_comp (w : Γ → Γ → ℝ≥0∞)
    (S T : Γ → Γ → ℂ)
    (hw : ∀ x z y, w x y ≤ w x z * w z y)
    (hS : ComplexMem w S) (hT : ComplexMem w T) :
    ComplexMem w (kernelComp S T) := by
  intro htop
  have hle := complexENorm_comp_le w S T hw
  rw [htop] at hle
  exact (ENNReal.mul_ne_top hS hT) (top_unique hle)

theorem complexMem_adj (w : Γ → Γ → ℝ≥0∞)
    (K : Γ → Γ → ℂ) (hsymm : ∀ x y, w x y = w y x)
    (hK : ComplexMem w K) :
    ComplexMem w (kernelAdj K) := by
  unfold ComplexMem at hK ⊢
  rw [complexENorm_adj w K hsymm]
  exact hK

/-- The finite real-valued norm on the weighted Schur algebra. -/
noncomputable def complexNorm (w : Γ → Γ → ℝ≥0∞)
    (K : Γ → Γ → ℂ) : ℝ :=
  (complexENorm w K).toReal

theorem complexNorm_comp_le (w : Γ → Γ → ℝ≥0∞)
    (S T : Γ → Γ → ℂ)
    (hw : ∀ x z y, w x y ≤ w x z * w z y)
    (hS : ComplexMem w S) (hT : ComplexMem w T) :
    complexNorm w (kernelComp S T) ≤
      complexNorm w S * complexNorm w T := by
  unfold complexNorm
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hS hT)
    (complexENorm_comp_le w S T hw)

theorem complexNorm_adj (w : Γ → Γ → ℝ≥0∞)
    (K : Γ → Γ → ℂ) (hsymm : ∀ x y, w x y = w y x) :
    complexNorm w (kernelAdj K) = complexNorm w K := by
  unfold complexNorm
  rw [complexENorm_adj w K hsymm]

theorem tsum_enorm_row_le_complexENorm
    (w : Γ → Γ → ℝ≥0∞) (K : Γ → Γ → ℂ)
    (hone : ∀ x y, 1 ≤ w x y) (x : Γ) :
    ∑' y, ‖K x y‖ₑ ≤ complexENorm w K := by
  calc
    (∑' y, ‖K x y‖ₑ)
        ≤ ∑' y, w x y * ‖K x y‖ₑ := by
      apply ENNReal.tsum_le_tsum
      intro y
      simpa [mul_comm] using mul_le_mul_right (hone x y) ‖K x y‖ₑ
    _ = row w (enormKernel K) x := rfl
    _ ≤ complexENorm w K := row_le_eNorm _ _ x

theorem tsum_enorm_col_le_complexENorm
    (w : Γ → Γ → ℝ≥0∞) (K : Γ → Γ → ℂ)
    (hone : ∀ x y, 1 ≤ w x y) (y : Γ) :
    ∑' x, ‖K x y‖ₑ ≤ complexENorm w K := by
  calc
    (∑' x, ‖K x y‖ₑ)
        ≤ ∑' x, w x y * ‖K x y‖ₑ := by
      apply ENNReal.tsum_le_tsum
      intro x
      simpa [mul_comm] using mul_le_mul_right (hone x y) ‖K x y‖ₑ
    _ = col w (enormKernel K) y := rfl
    _ ≤ complexENorm w K := col_le_eNorm _ _ y

theorem summable_norm_row_of_complexMem
    (w : Γ → Γ → ℝ≥0∞) (K : Γ → Γ → ℂ)
    (hone : ∀ x y, 1 ≤ w x y) (hK : ComplexMem w K) (x : Γ) :
    Summable fun y => ‖K x y‖ := by
  rw [← tsum_enorm_ne_top_iff_summable_norm]
  exact ne_top_of_le_ne_top hK
    (tsum_enorm_row_le_complexENorm w K hone x)

theorem summable_norm_col_of_complexMem
    (w : Γ → Γ → ℝ≥0∞) (K : Γ → Γ → ℂ)
    (hone : ∀ x y, 1 ≤ w x y) (hK : ComplexMem w K) (y : Γ) :
    Summable fun x => ‖K x y‖ := by
  rw [← tsum_enorm_ne_top_iff_summable_norm]
  exact ne_top_of_le_ne_top hK
    (tsum_enorm_col_le_complexENorm w K hone y)

theorem tsum_norm_row_le_complexNorm
    (w : Γ → Γ → ℝ≥0∞) (K : Γ → Γ → ℂ)
    (hone : ∀ x y, 1 ≤ w x y) (hK : ComplexMem w K) (x : Γ) :
    ∑' y, ‖K x y‖ ≤ complexNorm w K := by
  unfold complexNorm
  have h := ENNReal.toReal_mono hK
    (tsum_enorm_row_le_complexENorm w K hone x)
  rw [ENNReal.tsum_toReal_eq] at h
  · simpa using h
  · intro y
    exact enorm_ne_top

theorem tsum_norm_col_le_complexNorm
    (w : Γ → Γ → ℝ≥0∞) (K : Γ → Γ → ℂ)
    (hone : ∀ x y, 1 ≤ w x y) (hK : ComplexMem w K) (y : Γ) :
    ∑' x, ‖K x y‖ ≤ complexNorm w K := by
  unfold complexNorm
  have h := ENNReal.toReal_mono hK
    (tsum_enorm_col_le_complexENorm w K hone y)
  rw [ENNReal.tsum_toReal_eq] at h
  · simpa using h
  · intro x
    exact enorm_ne_top

/-- The bounded l2 operator canonically induced by a finite weighted
Schur kernel. -/
noncomputable def weightedKernelOperator
    (w : Γ → Γ → ℝ≥0∞) (K : Γ → Γ → ℂ)
    (hone : ∀ x y, 1 ≤ w x y) (hK : ComplexMem w K) :
    lp (fun _ : Γ => ℂ) 2 →L[ℂ] lp (fun _ : Γ => ℂ) 2 :=
  kernelOperator K (complexNorm w K) ENNReal.toReal_nonneg
    (summable_norm_row_of_complexMem w K hone hK)
    (summable_norm_col_of_complexMem w K hone hK)
    (tsum_norm_row_le_complexNorm w K hone hK)
    (tsum_norm_col_le_complexNorm w K hone hK)

theorem weightedKernelOperator_norm_le
    (w : Γ → Γ → ℝ≥0∞) (K : Γ → Γ → ℂ)
    (hone : ∀ x y, 1 ≤ w x y) (hK : ComplexMem w K) :
    ‖weightedKernelOperator w K hone hK‖ ≤ complexNorm w K :=
  kernelOperator_norm_le K (complexNorm w K) ENNReal.toReal_nonneg
    (summable_norm_row_of_complexMem w K hone hK)
    (summable_norm_col_of_complexMem w K hone hK)
    (tsum_norm_row_le_complexNorm w K hone hK)
    (tsum_norm_col_le_complexNorm w K hone hK)

theorem weightedKernelOperator_on_finsupp_apply
    (w : Γ → Γ → ℝ≥0∞) (K : Γ → Γ → ℂ)
    (hone : ∀ x y, 1 ≤ w x y) (hK : ComplexMem w K)
    (v : Finsupp Γ ℂ) (x : Γ) :
    weightedKernelOperator w K hone hK (finsuppToL2 v) x =
      ∑ y ∈ v.support, K x y * v y :=
  kernelOperator_on_finsupp_apply K (complexNorm w K)
    ENNReal.toReal_nonneg
    (summable_norm_row_of_complexMem w K hone hK)
    (summable_norm_col_of_complexMem w K hone hK)
    (tsum_norm_row_le_complexNorm w K hone hK)
    (tsum_norm_col_le_complexNorm w K hone hK) v x

/-- Finite Schur norm makes every convolution entry absolutely summable. -/
theorem summable_kernelComp (w : Γ → Γ → ℝ≥0∞)
    (S T : Γ → Γ → ℂ)
    (hw : ∀ x z y, w x y ≤ w x z * w z y)
    (hone : ∀ x y, 1 ≤ w x y)
    (hS : ComplexMem w S) (hT : ComplexMem w T)
    (x y : Γ) :
    Summable fun z => S x z * T z y := by
  apply Summable.of_norm
  rw [← tsum_enorm_ne_top_iff_summable_norm]
  have hcomp : eNorm w (comp (enormKernel S) (enormKernel T)) ≠ ∞ :=
    mem_comp w (enormKernel S) (enormKernel T) hw hS hT
  have hentry :
      comp (enormKernel S) (enormKernel T) x y ≤
        eNorm w (comp (enormKernel S) (enormKernel T)) := by
    calc
      comp (enormKernel S) (enormKernel T) x y
          ≤ w x y * comp (enormKernel S) (enormKernel T) x y :=
            (by simpa using mul_le_mul_left (hone x y) _)
      _ ≤ row w (comp (enormKernel S) (enormKernel T)) x :=
        ENNReal.le_tsum y
      _ ≤ eNorm w (comp (enormKernel S) (enormKernel T)) :=
        row_le_eNorm _ _ x
  have hfinite :
      comp (enormKernel S) (enormKernel T) x y ≠ ∞ :=
    ne_top_of_le_ne_top hcomp hentry
  simpa only [comp, enormKernel, enorm_mul] using hfinite

/-! ## Exponential metric weights -/

/-- Exponential weight associated to a real-valued distance. -/
noncomputable def expWeight (α : ℝ) (d : Γ → Γ → ℝ) :
    Γ → Γ → ℝ≥0∞ :=
  fun x y => ENNReal.ofReal (Real.exp (α * d x y))

theorem one_le_expWeight (α : ℝ) (d : Γ → Γ → ℝ)
    (hα : 0 ≤ α) (hd0 : ∀ x y, 0 ≤ d x y) (x y : Γ) :
    1 ≤ expWeight α d x y := by
  rw [expWeight, ENNReal.one_le_ofReal, Real.one_le_exp_iff]
  exact mul_nonneg hα (hd0 x y)

theorem expWeight_triangle (α : ℝ) (d : Γ → Γ → ℝ)
    (hα : 0 ≤ α) (htri : ∀ x z y, d x y ≤ d x z + d z y)
    (x z y : Γ) :
    expWeight α d x y ≤ expWeight α d x z * expWeight α d z y := by
  unfold expWeight
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  calc
    α * d x y ≤ α * (d x z + d z y) :=
      mul_le_mul_of_nonneg_left (htri x z y) hα
    _ = α * d x z + α * d z y := mul_add _ _ _

theorem expWeight_symm (α : ℝ) (d : Γ → Γ → ℝ)
    (hsymm : ∀ x y, d x y = d y x) (x y : Γ) :
    expWeight α d x y = expWeight α d y x := by
  simp [expWeight, hsymm]

/-- The manuscript weighted Schur algebra estimate for a finite or countable
scalar-block metric carrier. -/
theorem countable_weighted_schur_algebra
    (α : ℝ) (d : Γ → Γ → ℝ)
    (hα : 0 ≤ α) (hd0 : ∀ x y, 0 ≤ d x y)
    (htri : ∀ x z y, d x y ≤ d x z + d z y)
    (hsymm : ∀ x y, d x y = d y x)
    (S T : Γ → Γ → ℂ)
    (hS : ComplexMem (expWeight α d) S)
    (hT : ComplexMem (expWeight α d) T) :
    ComplexMem (expWeight α d) (kernelComp S T) ∧
      complexNorm (expWeight α d) (kernelComp S T) ≤
        complexNorm (expWeight α d) S *
          complexNorm (expWeight α d) T ∧
      complexNorm (expWeight α d) (kernelAdj T) =
        complexNorm (expWeight α d) T ∧
      (∀ x y, Summable fun z => S x z * T z y) := by
  have hw := expWeight_triangle α d hα htri
  have hone := one_le_expWeight α d hα hd0
  have hadj := expWeight_symm α d hsymm
  exact ⟨complexMem_comp _ S T hw hS hT,
    complexNorm_comp_le _ S T hw hS hT,
    complexNorm_adj _ T hadj,
    fun x y => summable_kernelComp _ S T hw hone hS hT x y⟩

/-! ## Restricted kernels and off-diagonal decay -/

/-- Restriction to an output region Y and an input region X. -/
noncomputable def restrictKernel (Y X : Set Γ) (K : Γ → Γ → ℂ) :
    Γ → Γ → ℂ := by
  classical
  exact fun y x => if y ∈ Y ∧ x ∈ X then K y x else 0

/-- The unweighted Schur weight. -/
def unitWeight : Γ → Γ → ℝ≥0∞ := fun _ _ => 1

theorem row_restrict_le (w : Γ → Γ → ℝ≥0∞)
    (Y X : Set Γ) (K : Γ → Γ → ℂ) (c : ℝ≥0∞)
    (hc : ∀ y ∈ Y, ∀ x ∈ X, 1 ≤ c * w y x) (y : Γ) :
    row unitWeight (enormKernel (restrictKernel Y X K)) y ≤
      c * eNorm w (enormKernel K) := by
  calc
    row unitWeight (enormKernel (restrictKernel Y X K)) y
        ≤ ∑' x, c * (w y x * enormKernel K y x) := by
          unfold row
          exact ENNReal.tsum_le_tsum fun x => by
            by_cases h : y ∈ Y ∧ x ∈ X
            · simp only [unitWeight, one_mul, enormKernel, restrictKernel,
                if_pos h]
              calc
                ‖K y x‖ₑ = 1 * ‖K y x‖ₑ := (one_mul _).symm
                _ ≤ (c * w y x) * ‖K y x‖ₑ :=
                  mul_le_mul_left (hc y h.1 x h.2) _
                _ = c * (w y x * ‖K y x‖ₑ) := by ac_rfl
            · simp [unitWeight, enormKernel, restrictKernel, h]
    _ = c * row w (enormKernel K) y := ENNReal.tsum_mul_left
    _ ≤ c * eNorm w (enormKernel K) :=
      mul_le_mul_right (row_le_eNorm _ _ y) _

theorem col_restrict_le (w : Γ → Γ → ℝ≥0∞)
    (Y X : Set Γ) (K : Γ → Γ → ℂ) (c : ℝ≥0∞)
    (hc : ∀ y ∈ Y, ∀ x ∈ X, 1 ≤ c * w y x) (x : Γ) :
    col unitWeight (enormKernel (restrictKernel Y X K)) x ≤
      c * eNorm w (enormKernel K) := by
  calc
    col unitWeight (enormKernel (restrictKernel Y X K)) x
        ≤ ∑' y, c * (w y x * enormKernel K y x) := by
          unfold col
          exact ENNReal.tsum_le_tsum fun y => by
            by_cases h : y ∈ Y ∧ x ∈ X
            · simp only [unitWeight, one_mul, enormKernel, restrictKernel,
                if_pos h]
              calc
                ‖K y x‖ₑ = 1 * ‖K y x‖ₑ := (one_mul _).symm
                _ ≤ (c * w y x) * ‖K y x‖ₑ :=
                  mul_le_mul_left (hc y h.1 x h.2) _
                _ = c * (w y x * ‖K y x‖ₑ) := by ac_rfl
            · simp [unitWeight, enormKernel, restrictKernel, h]
    _ = c * col w (enormKernel K) x := ENNReal.tsum_mul_left
    _ ≤ c * eNorm w (enormKernel K) :=
      mul_le_mul_right (col_le_eNorm _ _ x) _

theorem complexENorm_restrict_le (w : Γ → Γ → ℝ≥0∞)
    (Y X : Set Γ) (K : Γ → Γ → ℂ) (c : ℝ≥0∞)
    (hc : ∀ y ∈ Y, ∀ x ∈ X, 1 ≤ c * w y x) :
    complexENorm unitWeight (restrictKernel Y X K) ≤
      c * complexENorm w K := by
  unfold complexENorm eNorm
  apply max_le
  · exact iSup_le fun y => row_restrict_le w Y X K c hc y
  · exact iSup_le fun x => col_restrict_le w Y X K c hc x

theorem complexMem_restrict
    (w : Γ → Γ → ℝ≥0∞) (Y X : Set Γ)
    (K : Γ → Γ → ℂ) (c : ℝ≥0∞)
    (hc : ∀ y ∈ Y, ∀ x ∈ X, 1 ≤ c * w y x)
    (hcTop : c ≠ ∞) (hK : ComplexMem w K) :
    ComplexMem unitWeight (restrictKernel Y X K) := by
  intro htop
  have hle := complexENorm_restrict_le w Y X K c hc
  rw [htop] at hle
  exact (ENNReal.mul_ne_top hcTop hK) (top_unique hle)

theorem complexNorm_restrict_le
    (w : Γ → Γ → ℝ≥0∞) (Y X : Set Γ)
    (K : Γ → Γ → ℂ) (c : ℝ≥0∞)
    (hc : ∀ y ∈ Y, ∀ x ∈ X, 1 ≤ c * w y x)
    (hcTop : c ≠ ∞) (hK : ComplexMem w K) :
    complexNorm unitWeight (restrictKernel Y X K)
      ≤ c.toReal * complexNorm w K := by
  unfold complexNorm
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hcTop hK)
    (complexENorm_restrict_le w Y X K c hc)

/-- The bounded operator induced by the kernel restricted from X to Y. -/
noncomputable def restrictedKernelOperator
    (w : Γ → Γ → ℝ≥0∞) (Y X : Set Γ)
    (K : Γ → Γ → ℂ) (c : ℝ≥0∞)
    (hc : ∀ y ∈ Y, ∀ x ∈ X, 1 ≤ c * w y x)
    (hcTop : c ≠ ∞) (hK : ComplexMem w K) :
    lp (fun _ : Γ => ℂ) 2 →L[ℂ] lp (fun _ : Γ => ℂ) 2 :=
  weightedKernelOperator unitWeight (restrictKernel Y X K)
    (fun _ _ => le_rfl)
    (complexMem_restrict w Y X K c hc hcTop hK)

theorem restrictedKernelOperator_norm_le
    (w : Γ → Γ → ℝ≥0∞) (Y X : Set Γ)
    (K : Γ → Γ → ℂ) (c : ℝ≥0∞)
    (hc : ∀ y ∈ Y, ∀ x ∈ X, 1 ≤ c * w y x)
    (hcTop : c ≠ ∞) (hK : ComplexMem w K) :
    ‖restrictedKernelOperator w Y X K c hc hcTop hK‖
      ≤ c.toReal * complexNorm w K := by
  exact (weightedKernelOperator_norm_le unitWeight
    (restrictKernel Y X K) (fun _ _ => le_rfl)
    (complexMem_restrict w Y X K c hc hcTop hK)).trans
      (complexNorm_restrict_le w Y X K c hc hcTop hK)

/-- Countable scalar-block off-diagonal exponential Schur estimate. -/
theorem expWeight_restrict_le
    (α R : ℝ) (d : Γ → Γ → ℝ)
    (hα : 0 ≤ α) (Y X : Set Γ)
    (hdist : ∀ y ∈ Y, ∀ x ∈ X, R ≤ d y x)
    (K : Γ → Γ → ℂ) :
    complexENorm unitWeight (restrictKernel Y X K) ≤
      ENNReal.ofReal (Real.exp (-α * R)) *
        complexENorm (expWeight α d) K := by
  apply complexENorm_restrict_le
  intro y hy x hx
  unfold expWeight
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.one_le_ofReal,
    ← Real.exp_add, Real.one_le_exp_iff]
  have h := mul_le_mul_of_nonneg_left (hdist y hy x hx) hα
  linarith

/-- Countable scalar-block off-diagonal exponential operator estimate. -/
theorem expWeight_restrictedKernelOperator_norm_le
    (α R : ℝ) (d : Γ → Γ → ℝ)
    (hα : 0 ≤ α) (hd0 : ∀ x y, 0 ≤ d x y)
    (Y X : Set Γ)
    (hdist : ∀ y ∈ Y, ∀ x ∈ X, R ≤ d y x)
    (K : Γ → Γ → ℂ)
    (hK : ComplexMem (expWeight α d) K) :
    let c := ENNReal.ofReal (Real.exp (-α * R))
    ‖restrictedKernelOperator (expWeight α d) Y X K c
      (by
        intro y hy x hx
        unfold expWeight
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
          ENNReal.one_le_ofReal, ← Real.exp_add, Real.one_le_exp_iff]
        have h := mul_le_mul_of_nonneg_left (hdist y hy x hx) hα
        linarith)
      (ENNReal.ofReal_ne_top) hK‖
      ≤ Real.exp (-α * R) * complexNorm (expWeight α d) K := by
  dsimp only
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _), neg_mul] using
    restrictedKernelOperator_norm_le
    (expWeight α d) Y X K
    (ENNReal.ofReal (Real.exp (-α * R)))
    (by
      intro y hy x hx
      unfold expWeight
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ENNReal.one_le_ofReal, ← Real.exp_add, Real.one_le_exp_iff]
      have h := mul_le_mul_of_nonneg_left (hdist y hy x hx) hα
      linarith)
    ENNReal.ofReal_ne_top hK

end CountableWeightedSchurKernel
end NCG
