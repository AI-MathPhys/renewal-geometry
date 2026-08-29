/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.SpatiotemporalFeedback

/-!
# Finite weighted Schur norm and the ℓ² Schur test

This file provides the finite scalar-block weighted Schur interface used by
the Gran--Tensor localization results.  The carrier is a finite index type,
operators are complex matrices, block norms are entry moduli, and `opNorm` is
the genuine Euclidean `ℓ²` operator norm through `Matrix.toEuclideanCLM`.

The main result is the finite Schur test: the operator norm is bounded by the
maximum of the row and column absolute-sum bounds.  Later localization modules
build the Lipschitz-similarity and off-diagonal estimates on this foundation.
-/

open Matrix Finset

namespace NCG
namespace FiniteWeightedSchurNorm

/-! ## Weighted Schur interface on a finite pseudometric carrier

Scalar-block rendering of `def:GTLOC-weighted-Schur`: a finite index set `Λ`
with a pseudometric `d`, matrices as block operators, and the weighted Schur
norm (eq:GTLOC-weighted-Schur-norm) as the maximum of the weighted row and
column sums. -/

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]

/-- The `μ`-weighted row sum of `T` at `x` (row half of
eq:GTLOC-weighted-Schur-norm). -/
noncomputable def schurRow (μ : ℝ) (d : Λ → Λ → ℝ) (T : Matrix Λ Λ ℂ) (x : Λ) : ℝ :=
  ∑ y, Real.exp (μ * d x y) * ‖T x y‖

/-- The `μ`-weighted column sum of `T` at `y` (column half of
eq:GTLOC-weighted-Schur-norm). -/
noncomputable def schurCol (μ : ℝ) (d : Λ → Λ → ℝ) (T : Matrix Λ Λ ℂ) (y : Λ) : ℝ :=
  ∑ x, Real.exp (μ * d x y) * ‖T x y‖

/-- The weighted Schur norm `‖T‖_{μ,Sch}` (eq:GTLOC-weighted-Schur-norm): the
maximum of the suprema of the weighted row and column sums. -/
noncomputable def schurNorm (μ : ℝ) (d : Λ → Λ → ℝ) (T : Matrix Λ Λ ℂ) : ℝ :=
  max (Finset.univ.sup' Finset.univ_nonempty (schurRow μ d T))
    (Finset.univ.sup' Finset.univ_nonempty (schurCol μ d T))

theorem schurRow_nonneg (μ : ℝ) (d : Λ → Λ → ℝ) (T : Matrix Λ Λ ℂ) (x : Λ) :
    0 ≤ schurRow μ d T x :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem schurCol_nonneg (μ : ℝ) (d : Λ → Λ → ℝ) (T : Matrix Λ Λ ℂ) (y : Λ) :
    0 ≤ schurCol μ d T y :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem schurRow_le_schurNorm (μ : ℝ) (d : Λ → Λ → ℝ) (T : Matrix Λ Λ ℂ) (x : Λ) :
    schurRow μ d T x ≤ schurNorm μ d T :=
  le_trans (Finset.le_sup' _ (Finset.mem_univ x)) (le_max_left _ _)

theorem schurCol_le_schurNorm (μ : ℝ) (d : Λ → Λ → ℝ) (T : Matrix Λ Λ ℂ) (y : Λ) :
    schurCol μ d T y ≤ schurNorm μ d T :=
  le_trans (Finset.le_sup' _ (Finset.mem_univ y)) (le_max_right _ _)

theorem schurNorm_nonneg (μ : ℝ) (d : Λ → Λ → ℝ) (T : Matrix Λ Λ ℂ) :
    0 ≤ schurNorm μ d T :=
  le_trans (schurRow_nonneg μ d T (Classical.arbitrary Λ))
    (schurRow_le_schurNorm μ d T _)

/-- On a finite carrier, the weighted Schur norm is continuous in the
ambient matrix topology. -/
theorem continuous_schurNorm (μ : ℝ) (d : Λ → Λ → ℝ) :
    Continuous (schurNorm μ d : Matrix Λ Λ ℂ → ℝ) := by
  unfold schurNorm schurRow schurCol
  fun_prop

/-- The genuine `ℓ²` operator norm of a matrix, through the star-algebra
equivalence with continuous linear endomorphisms of Euclidean space. -/
noncomputable def opNorm (T : Matrix Λ Λ ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T‖

theorem opNorm_nonneg (T : Matrix Λ Λ ℂ) : 0 ≤ opNorm T := norm_nonneg _

theorem opNorm_mul_le (S T : Matrix Λ Λ ℂ) :
    opNorm (S * T) ≤ opNorm S * opNorm T := by
  rw [opNorm, opNorm, opNorm, map_mul]
  exact norm_mul_le _ _

/-- The exponential distance weight is submultiplicative whenever `d`
satisfies the triangle inequality and `μ ≥ 0`. -/
theorem expWeight_triangle (μ : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd : ∀ x z y, d x y ≤ d x z + d z y) :
    ∀ x z y,
      Real.exp (μ * d x y) ≤
        Real.exp (μ * d x z) * Real.exp (μ * d z y) := by
  intro x z y
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    μ * d x y ≤ μ * (d x z + d z y) :=
      mul_le_mul_of_nonneg_left (hd x z y) hμ
    _ = μ * d x z + μ * d z y := mul_add _ _ _

/-- Row half of weighted-Schur submultiplicativity. -/
theorem schurRow_mul_le (μ : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (S T : Matrix Λ Λ ℂ) (x : Λ) :
    schurRow μ d (S * T) x ≤ schurNorm μ d S * schurNorm μ d T := by
  let κ : Λ → Λ → ℝ := fun x y => Real.exp (μ * d x y)
  have hκ0 : ∀ x y, 0 ≤ κ x y := fun _ _ => (Real.exp_pos _).le
  have hκtri : ∀ x z y, κ x y ≤ κ x z * κ z y :=
    expWeight_triangle μ d hμ hd
  have hconv := (spatiotemporal_feedback κ hκ0 hκtri).1
    (fun z y => ‖T z y‖) (fun x z => ‖S x z‖)
    (schurNorm μ d T) (schurNorm μ d S)
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    (schurNorm_nonneg μ d T)
    (fun z => schurRow_le_schurNorm μ d T z)
    (fun x => schurRow_le_schurNorm μ d S x) x
  calc
    schurRow μ d (S * T) x
        ≤ ∑ y, κ x y * (∑ z, ‖S x z‖ * ‖T z y‖) := by
          unfold schurRow
          apply Finset.sum_le_sum
          intro y hy
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          rw [Matrix.mul_apply]
          calc
            ‖∑ z, S x z * T z y‖ ≤ ∑ z, ‖S x z * T z y‖ :=
              norm_sum_le _ _
            _ = ∑ z, ‖S x z‖ * ‖T z y‖ :=
              Finset.sum_congr rfl fun z _ => norm_mul _ _
    _ ≤ schurNorm μ d S * schurNorm μ d T := by
          simpa [κ, mul_comm] using hconv

/-- Column half of weighted-Schur submultiplicativity. -/
theorem schurCol_mul_le (μ : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (S T : Matrix Λ Λ ℂ) (y : Λ) :
    schurCol μ d (S * T) y ≤ schurNorm μ d S * schurNorm μ d T := by
  let κ : Λ → Λ → ℝ := fun y x => Real.exp (μ * d x y)
  have hκ0 : ∀ y x, 0 ≤ κ y x := fun _ _ => (Real.exp_pos _).le
  have hκtri : ∀ y z x, κ y x ≤ κ y z * κ z x := by
    intro y z x
    dsimp [κ]
    simpa [mul_comm] using expWeight_triangle μ d hμ hd x z y
  have hconv := (spatiotemporal_feedback κ hκ0 hκtri).1
    (fun z x => ‖S x z‖) (fun y z => ‖T z y‖)
    (schurNorm μ d S) (schurNorm μ d T)
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    (schurNorm_nonneg μ d S)
    (fun z => schurCol_le_schurNorm μ d S z)
    (fun y => schurCol_le_schurNorm μ d T y) y
  calc
    schurCol μ d (S * T) y
        ≤ ∑ x, κ y x * (∑ z, ‖T z y‖ * ‖S x z‖) := by
          unfold schurCol
          apply Finset.sum_le_sum
          intro x hx
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          rw [Matrix.mul_apply]
          calc
            ‖∑ z, S x z * T z y‖ ≤ ∑ z, ‖S x z * T z y‖ :=
              norm_sum_le _ _
            _ = ∑ z, ‖T z y‖ * ‖S x z‖ :=
              Finset.sum_congr rfl fun z _ => by rw [norm_mul, mul_comm]
    _ ≤ schurNorm μ d T * schurNorm μ d S := by
          simpa [κ] using hconv
    _ = schurNorm μ d S * schurNorm μ d T := mul_comm _ _

/-- **Weighted Schur Banach-algebra estimate** on a finite pseudometric
carrier. -/
theorem schurNorm_mul_le (μ : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (S T : Matrix Λ Λ ℂ) :
    schurNorm μ d (S * T) ≤ schurNorm μ d S * schurNorm μ d T := by
  unfold schurNorm
  apply max_le
  · exact Finset.sup'_le _ _ fun x _ => schurRow_mul_le μ d hμ hd S T x
  · exact Finset.sup'_le _ _ fun y _ => schurCol_mul_le μ d hμ hd S T y

theorem schurRow_add_le (μ : ℝ) (d : Λ → Λ → ℝ)
    (S T : Matrix Λ Λ ℂ) (x : Λ) :
    schurRow μ d (S + T) x ≤ schurRow μ d S x + schurRow μ d T x := by
  unfold schurRow
  calc
    ∑ y, Real.exp (μ * d x y) * ‖(S + T) x y‖
        ≤ ∑ y, (Real.exp (μ * d x y) * ‖S x y‖ +
          Real.exp (μ * d x y) * ‖T x y‖) := by
            apply Finset.sum_le_sum
            intro y hy
            simpa [mul_add] using
              mul_le_mul_of_nonneg_left (norm_add_le (S x y) (T x y))
                (Real.exp_pos _).le
    _ = (∑ y, Real.exp (μ * d x y) * ‖S x y‖) +
        ∑ y, Real.exp (μ * d x y) * ‖T x y‖ := Finset.sum_add_distrib

theorem schurCol_add_le (μ : ℝ) (d : Λ → Λ → ℝ)
    (S T : Matrix Λ Λ ℂ) (y : Λ) :
    schurCol μ d (S + T) y ≤ schurCol μ d S y + schurCol μ d T y := by
  unfold schurCol
  calc
    ∑ x, Real.exp (μ * d x y) * ‖(S + T) x y‖
        ≤ ∑ x, (Real.exp (μ * d x y) * ‖S x y‖ +
          Real.exp (μ * d x y) * ‖T x y‖) := by
            apply Finset.sum_le_sum
            intro x hx
            simpa [mul_add] using
              mul_le_mul_of_nonneg_left (norm_add_le (S x y) (T x y))
                (Real.exp_pos _).le
    _ = (∑ x, Real.exp (μ * d x y) * ‖S x y‖) +
        ∑ x, Real.exp (μ * d x y) * ‖T x y‖ := Finset.sum_add_distrib

theorem schurNorm_add_le (μ : ℝ) (d : Λ → Λ → ℝ)
    (S T : Matrix Λ Λ ℂ) :
    schurNorm μ d (S + T) ≤ schurNorm μ d S + schurNorm μ d T := by
  unfold schurNorm
  apply max_le
  · refine Finset.sup'_le _ _ fun x _ => ?_
    exact (schurRow_add_le μ d S T x).trans
      (add_le_add (le_trans (Finset.le_sup' _ (Finset.mem_univ x))
        (le_max_left _ _))
        (le_trans (Finset.le_sup' _ (Finset.mem_univ x))
          (le_max_left _ _)))
  · refine Finset.sup'_le _ _ fun y _ => ?_
    exact (schurCol_add_le μ d S T y).trans
      (add_le_add (le_trans (Finset.le_sup' _ (Finset.mem_univ y))
        (le_max_right _ _))
        (le_trans (Finset.le_sup' _ (Finset.mem_univ y))
          (le_max_right _ _)))

theorem schurNorm_smul_le (μ : ℝ) (d : Λ → Λ → ℝ)
    (c : ℂ) (T : Matrix Λ Λ ℂ) :
    schurNorm μ d (c • T) ≤ ‖c‖ * schurNorm μ d T := by
  unfold schurNorm
  apply max_le
  · refine Finset.sup'_le _ _ fun x _ => ?_
    calc
      schurRow μ d (c • T) x = ‖c‖ * schurRow μ d T x := by
        unfold schurRow
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        rw [Matrix.smul_apply, norm_smul]
        ring
      _ ≤ ‖c‖ * schurNorm μ d T :=
        mul_le_mul_of_nonneg_left (schurRow_le_schurNorm μ d T x)
          (norm_nonneg c)
  · refine Finset.sup'_le _ _ fun y _ => ?_
    calc
      schurCol μ d (c • T) y = ‖c‖ * schurCol μ d T y := by
        unfold schurCol
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Matrix.smul_apply, norm_smul]
        ring
      _ ≤ ‖c‖ * schurNorm μ d T :=
        mul_le_mul_of_nonneg_left (schurCol_le_schurNorm μ d T y)
          (norm_nonneg c)

theorem schurNorm_one (μ : ℝ) (d : Λ → Λ → ℝ)
    (hdiag : ∀ x, d x x = 0) :
    schurNorm μ d (1 : Matrix Λ Λ ℂ) = 1 := by
  unfold schurNorm schurRow schurCol
  have hrow : (fun x : Λ => ∑ y, Real.exp (μ * d x y) * ‖(1 : Matrix Λ Λ ℂ) x y‖) =
      fun _ => 1 := by
    funext x
    simp only [Matrix.one_apply, apply_ite, norm_one, norm_zero,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, hdiag, Real.exp_zero]
  have hcol : (fun y : Λ => ∑ x, Real.exp (μ * d x y) * ‖(1 : Matrix Λ Λ ℂ) x y‖) =
      fun _ => 1 := by
    funext y
    simp only [Matrix.one_apply, apply_ite, norm_one, norm_zero,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hdiag, Real.exp_zero]
  rw [hrow, hcol]
  simp

theorem schurNorm_pow_le (μ : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd : ∀ x z y, d x y ≤ d x z + d z y)
    (hdiag : ∀ x, d x x = 0) (T : Matrix Λ Λ ℂ) :
    ∀ k : ℕ, schurNorm μ d (T ^ k) ≤ (schurNorm μ d T) ^ k := by
  intro k
  induction k with
  | zero => simp [schurNorm_one μ d hdiag]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (schurNorm_mul_le μ d hμ hd _ _).trans
        (mul_le_mul ih le_rfl (schurNorm_nonneg μ d _) (pow_nonneg
          (schurNorm_nonneg μ d T) k))

theorem schurNorm_sum_le {ι : Type*} (μ : ℝ) (d : Λ → Λ → ℝ)
    (s : Finset ι) (F : ι → Matrix Λ Λ ℂ) :
    schurNorm μ d (∑ i ∈ s, F i) ≤ ∑ i ∈ s, schurNorm μ d (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [schurNorm, schurRow, schurCol]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (schurNorm_add_le μ d _ _).trans (add_le_add le_rfl ih)

/-- **Schur test**: the `ℓ²` operator norm is dominated by the maximum of the
(unweighted) row and column absolute sums. -/
theorem opNorm_le_max_rowCol (T : Matrix Λ Λ ℂ)
    (R C : ℝ) (hR : ∀ x, ∑ y, ‖T x y‖ ≤ R) (hC : ∀ y, ∑ x, ‖T x y‖ ≤ C)
    (hR0 : 0 ≤ R) (hC0 : 0 ≤ C) :
    opNorm T ≤ max R C := by
  have hmax0 : 0 ≤ max R C := le_trans hR0 (le_max_left _ _)
  refine ContinuousLinearMap.opNorm_le_bound _ hmax0 fun v => ?_
  have hentry : ∀ x, ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) T v) x‖
      ≤ ∑ y, ‖T x y‖ * ‖v y‖ := by
    intro x
    have hx : (Matrix.toEuclideanCLM (𝕜 := ℂ) T v) x = ∑ y, T x y * v y := by
      have := Matrix.ofLp_toEuclideanCLM (𝕜 := ℂ) T v
      calc (Matrix.toEuclideanCLM (𝕜 := ℂ) T v) x
          = (WithLp.ofLp (Matrix.toEuclideanCLM (𝕜 := ℂ) T v)) x := rfl
        _ = (T *ᵥ WithLp.ofLp v) x := by rw [this]
        _ = ∑ y, T x y * v y := by simp [Matrix.mulVec, dotProduct]
    rw [hx]
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun y _ => norm_mul _ _
  -- squared bound: ‖Tv‖² ≤ R * C * ‖v‖²
  have hsq : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T v‖ ^ 2 ≤ R * C * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hrow : ∀ x, ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) T v) x‖ ^ 2
        ≤ R * ∑ y, ‖T x y‖ * ‖v y‖ ^ 2 := by
      intro x
      have h1 : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) T v) x‖ ^ 2
          ≤ (∑ y, ‖T x y‖ * ‖v y‖) ^ 2 := by
        have hnn : 0 ≤ ∑ y, ‖T x y‖ * ‖v y‖ :=
          Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _) (hentry x) 2
      have h2 : (∑ y, ‖T x y‖ * ‖v y‖) ^ 2
          ≤ (∑ y, ‖T x y‖) * ∑ y, ‖T x y‖ * ‖v y‖ ^ 2 := by
        have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ (α := Λ))
          (f := fun y => ‖T x y‖) (g := fun y => ‖T x y‖ * ‖v y‖ ^ 2)
          (fun y => norm_nonneg _)
          (fun y => mul_nonneg (norm_nonneg _) (sq_nonneg _))
        have hterm : ∀ y : Λ, Real.sqrt ‖T x y‖ * Real.sqrt (‖T x y‖ * ‖v y‖ ^ 2)
            = ‖T x y‖ * ‖v y‖ := by
          intro y
          rw [Real.sqrt_mul (norm_nonneg _), ← mul_assoc,
            Real.mul_self_sqrt (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
        rw [Finset.sum_congr rfl fun y _ => (hterm y).symm]
        have hsq' := hcs
        have hAnn : 0 ≤ ∑ y, ‖T x y‖ :=
          Finset.sum_nonneg fun _ _ => norm_nonneg _
        have hBnn : 0 ≤ ∑ y, ‖T x y‖ * ‖v y‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
        calc (∑ y, Real.sqrt ‖T x y‖ * Real.sqrt (‖T x y‖ * ‖v y‖ ^ 2)) ^ 2
            ≤ (Real.sqrt (∑ y, ‖T x y‖) * Real.sqrt (∑ y, ‖T x y‖ * ‖v y‖ ^ 2)) ^ 2 := by
              refine pow_le_pow_left₀ ?_ hsq' 2
              exact Finset.sum_nonneg fun y _ =>
                mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          _ = (∑ y, ‖T x y‖) * ∑ y, ‖T x y‖ * ‖v y‖ ^ 2 := by
              rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hBnn]
      have h3 : (∑ y, ‖T x y‖) * (∑ y, ‖T x y‖ * ‖v y‖ ^ 2)
          ≤ R * ∑ y, ‖T x y‖ * ‖v y‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right (hR x) ?_
        exact Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
      exact le_trans h1 (le_trans h2 h3)
    calc ∑ x, ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) T v) x‖ ^ 2
        ≤ ∑ x, R * ∑ y, ‖T x y‖ * ‖v y‖ ^ 2 :=
          Finset.sum_le_sum fun x _ => hrow x
      _ = R * ∑ y, (∑ x, ‖T x y‖) * ‖v y‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun y _ => (Finset.sum_mul _ _ _).symm
      _ ≤ R * ∑ y, C * ‖v y‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hR0
          exact Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_right (hC y) (sq_nonneg _)
      _ = R * C * ‖v‖ ^ 2 := by
          rw [← Finset.mul_sum, ← mul_assoc, EuclideanSpace.norm_sq_eq]
  have hfinal : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T v‖ ^ 2
      ≤ (max R C * ‖v‖) ^ 2 := by
    refine le_trans hsq ?_
    rw [mul_pow]
    have hRC : R * C ≤ max R C ^ 2 := by
      have := mul_le_mul (le_max_left R C) (le_max_right R C) hC0 hmax0
      calc R * C ≤ max R C * max R C := this
        _ = max R C ^ 2 := (sq _).symm
    exact mul_le_mul_of_nonneg_right hRC (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hfinal

open scoped Matrix.Norms.L2Operator in
/-- If the distance and mu are nonnegative, the C-star matrix norm is
dominated by the weighted Schur norm.  This bridges weighted estimates to
ordinary matrix power-series convergence. -/
theorem norm_le_schurNorm (μ : ℝ) (d : Λ → Λ → ℝ)
    (hμ : 0 ≤ μ) (hd0 : ∀ x y, 0 ≤ d x y)
    (T : Matrix Λ Λ ℂ) :
    ‖T‖ ≤ schurNorm μ d T := by
  have hrow : ∀ x, ∑ y, ‖T x y‖ ≤ schurNorm μ d T := by
    intro x
    calc
      ∑ y, ‖T x y‖
          ≤ ∑ y, Real.exp (μ * d x y) * ‖T x y‖ := by
            apply Finset.sum_le_sum
            intro y hy
            have he : 1 ≤ Real.exp (μ * d x y) :=
              (Real.one_le_exp_iff).2 (mul_nonneg hμ (hd0 x y))
            simpa using mul_le_mul_of_nonneg_right he (norm_nonneg (T x y))
      _ = schurRow μ d T x := rfl
      _ ≤ schurNorm μ d T := schurRow_le_schurNorm μ d T x
  have hcol : ∀ y, ∑ x, ‖T x y‖ ≤ schurNorm μ d T := by
    intro y
    calc
      ∑ x, ‖T x y‖
          ≤ ∑ x, Real.exp (μ * d x y) * ‖T x y‖ := by
            apply Finset.sum_le_sum
            intro x hx
            have he : 1 ≤ Real.exp (μ * d x y) :=
              (Real.one_le_exp_iff).2 (mul_nonneg hμ (hd0 x y))
            simpa using mul_le_mul_of_nonneg_right he (norm_nonneg (T x y))
      _ = schurCol μ d T y := rfl
      _ ≤ schurNorm μ d T := schurCol_le_schurNorm μ d T y
  rw [Matrix.cstar_norm_def]
  change opNorm T ≤ schurNorm μ d T
  simpa using opNorm_le_max_rowCol T
    (schurNorm μ d T) (schurNorm μ d T) hrow hcol
    (schurNorm_nonneg μ d T) (schurNorm_nonneg μ d T)

end FiniteWeightedSchurNorm
end NCG
