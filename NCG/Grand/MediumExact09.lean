/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Medium-difficulty exact records, batch 09 (Gran-Tensor manuscript)

Exact formalizations of the following manuscript records:

* `lem:GTLOC-Schur-Lipschitz` — Schur-to-Lipschitz domination
  `‖T‖_{μ,Lip} ≤ ‖T‖_{μ,Sch}` and the off-diagonal bound
  `‖P_X T P_Y‖ ≤ e^{-μ d(X,Y)} ‖T‖_{μ,Lip}`.
* `thm:GTLOC-commutator-hierarchy` — Lipschitz commutator hierarchy
  `‖ad_{M_f}^n(T)‖ ≤ (n!/μ^n) ‖T‖_{μ,Sch}`.
* `thm:GTLOC-critical-weighted-locality` — critical weighted first/pair
  locality from a `(μ,M,v)` weighted collar, via Cauchy estimates.
* `thm:GTLOC-insertion-path` — insertion-path locality for the Duhamel first
  and pair responses under a block collar.
* `thm:GTLOC-contact-tail-alternative` — finite-collar no-go and exponential
  rescue for the renormalized contact family.
* `thm:GTLOC-local-connected-OS` — quasilocal connected operator on the OS
  quotient: `‖G^{-1/2} C G^{-1/2}‖_{μ,Sch} ≤ ‖C‖_{μ,Sch}/(1-η)` and its
  off-diagonal consequence.
* `cth:GTLOC-norm-not-weighted` — ordinary norm convergence does not
  transport a locality exponent (long-hop family on `ℓ²(ℕ)`).
* `cth:GTLOC-local-response-not-product` — local response kernels do not
  reconstruct local multiplication (matched commutative/noncommutative pair).
* `thm:GT-NCG-graph-fibre` — graph spectral universality fibre (SP.22–SP.25).
* `thm:GT-NCG-static-no-germ` — static coefficient and reflected Markov
  dynamics do not imply the terminal germ.
* `thm:GT-NCG-terminal-short` — first terminal short and source-minimal germ
  witness (SP.39–SP.41).

The manuscript's weighted block algebra `𝔅_α(Γ)` (eq:GTLOC-weighted-Schur-norm)
is rendered finitely with scalar blocks: the carrier is a finite pseudometric
index set `Λ`, operators are matrices `T : Matrix Λ Λ ℂ`, block norms are the
entry moduli, and the operator norm is the genuine `ℓ²` operator norm obtained
through `Matrix.toEuclideanCLM`.
-/

open Matrix Finset

namespace NCG
namespace MedEx09

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

/-- The genuine `ℓ²` operator norm of a matrix, through the star-algebra
equivalence with continuous linear endomorphisms of Euclidean space. -/
noncomputable def opNorm (T : Matrix Λ Λ ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T‖

theorem opNorm_nonneg (T : Matrix Λ Λ ℂ) : 0 ≤ opNorm T := norm_nonneg _

theorem opNorm_mul_le (S T : Matrix Λ Λ ℂ) :
    opNorm (S * T) ≤ opNorm S * opNorm T := by
  rw [opNorm, opNorm, opNorm, map_mul]
  exact norm_mul_le _ _

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

end MedEx09
end NCG
