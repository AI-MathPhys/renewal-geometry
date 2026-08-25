/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.RelEntropyConvexExact

/-!
# Spectral shift transport in a fixed eigenbasis

Step (D4l) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: the regularisation `ρ ↦ ρ + ε·1` keeps
the eigenbasis of `ρ`, so the whole `ε`-dependence of the perturbed
relative entropy lands in scalar formulas with **fixed** overlap weights:

`D(ρ+ε1‖σ+ε1) = Σᵢ (pᵢ+ε)log(pᵢ+ε) − Σᵢⱼ (pᵢ+ε)log(qⱼ+ε)|Wᵢⱼ|²`.

* `matFun_shift`: `f(S + ε·1) = (f ∘ (·+ε))(S)` through the polynomial
  calculus;
* `shift_eq_matFun`: `S + ε·1 = matFun hS (·+ε)`;
* `relEntropy_shift_formula`: the boxed fixed-basis formula;
* `relEntropy_eq_spread`: its `ε = 0` counterpart;
* `posDef_add_smul_one`, `sum_smul_shift`: the positivity and mixture
  bookkeeping for the regularised convexity passage.
-/

open Matrix Unitary Finset Polynomial
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ρ σ S : Matrix n n ℂ}

/-! ### The shifted matrix -/

omit [Fintype n] in
theorem smul_one_real_eq (ε : ℝ) :
    (ε • (1 : Matrix n n ℂ)) = ((ε : ℂ) • (1 : Matrix n n ℂ)) := by
  ext i j
  simp [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]

omit [Fintype n] in
theorem shift_isHermitian (hS : S.IsHermitian) (ε : ℝ) :
    (S + ε • 1).IsHermitian := by
  have h1 : ((ε : ℝ) • (1 : Matrix n n ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_one]
  exact hS.add h1

theorem aeval_shift_arg (ε : ℝ) (M : Matrix n n ℂ) (P : Polynomial ℝ) :
    Polynomial.aeval (M + ε • 1) P =
      Polynomial.aeval M (P.comp (Polynomial.X + Polynomial.C ε)) := by
  rw [Polynomial.aeval_comp]
  congr 1
  rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one]

/-- **The fixed-basis shift**: `S + ε·1 = matFun hS (·+ε)`. -/
theorem shift_eq_matFun (hS : S.IsHermitian) (ε : ℝ) :
    S + ε • 1 = matFun hS fun x => x + ε := by
  unfold matFun
  have hdiag : diagonal (RCLike.ofReal ∘ fun i => hS.eigenvalues i + ε) =
      diagonal (RCLike.ofReal ∘ hS.eigenvalues) +
        (ε : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp only [Matrix.diagonal_apply_eq, Matrix.add_apply,
        Matrix.smul_apply, Matrix.one_apply_eq, Function.comp_apply,
        smul_eq_mul, mul_one]
      push_cast
      rfl
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [hdiag, map_add, map_smul, map_one, smul_one_real_eq]
  congr 1
  exact hS.spectral_theorem

/-- **Shift transport of the spectral calculus**:
`f(S + ε·1) = (f ∘ (·+ε))(S)`. -/
theorem matFun_shift (hS : S.IsHermitian) (ε : ℝ)
    (hSε : (S + ε • 1).IsHermitian) (f : ℝ → ℝ) :
    matFun hSε f = matFun hS fun x => f (x + ε) := by
  obtain ⟨P, hPval⟩ := exists_interpolating' f
    ((Finset.image hSε.eigenvalues Finset.univ) ∪
      Finset.image (fun i => hS.eigenvalues i + ε) Finset.univ)
  have h1 : matFun hSε f = Polynomial.aeval (S + ε • 1) P :=
    matFun_eq_aeval hSε f P fun i => hPval _
      (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have h2 : matFun hS (fun x => f (x + ε)) =
      Polynomial.aeval S (P.comp (Polynomial.X + Polynomial.C ε)) := by
    refine matFun_eq_aeval hS _ _ fun i => ?_
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    exact hPval _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  rw [h1, h2, aeval_shift_arg]

/-! ### Traces in the fixed basis -/

/-- `Re Tr f(S) = Σᵢ f(pᵢ)`. -/
theorem trace_matFun_re (hS : S.IsHermitian) (f : ℝ → ℝ) :
    ((matFun hS f).trace).re = ∑ i, f (hS.eigenvalues i) := by
  unfold matFun
  rw [trace_conj, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => by simp

/-! ### Positivity of the shift -/

theorem smul_one_mulVec (ε : ℝ) (v : n → ℂ) :
    (ε • (1 : Matrix n n ℂ)) *ᵥ v = (ε : ℂ) • v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply,
    Matrix.one_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp [Complex.real_smul]
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
theorem posDef_add_smul_one (hρ : ρ.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (ρ + ε • 1).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨shift_isHermitian hρ.1 ε, fun v hv => ?_⟩
  rw [Matrix.add_mulVec, dotProduct_add, smul_one_mulVec]
  have h1 : (0 : ℂ) ≤ star v ⬝ᵥ (ρ *ᵥ v) :=
    hρ.dotProduct_mulVec_nonneg v
  have h2 : (0 : ℂ) < star v ⬝ᵥ ((ε : ℂ) • v) := by
    have hone : (0 : ℂ) < star v ⬝ᵥ ((1 : Matrix n n ℂ) *ᵥ v) :=
      (Matrix.posDef_iff_dotProduct_mulVec.mp Matrix.PosDef.one).2 hv
    rw [Matrix.one_mulVec] at hone
    rw [dotProduct_smul]
    calc (0 : ℂ) = (ε : ℂ) • (0 : ℂ) := by simp
      _ < (ε : ℂ) • (star v ⬝ᵥ v) := by
          rw [smul_eq_mul, smul_eq_mul]
          refine mul_lt_mul_of_pos_left hone ?_
          exact_mod_cast hε
  exact add_pos_of_nonneg_of_pos h1 h2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
theorem posSemidef_add_smul_one (hρ : ρ.PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) :
    (ρ + ε • 1).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (shift_isHermitian hρ.1 ε) fun v => ?_
  rw [Matrix.add_mulVec, dotProduct_add, smul_one_mulVec]
  have h1 : (0 : ℂ) ≤ star v ⬝ᵥ (ρ *ᵥ v) :=
    hρ.dotProduct_mulVec_nonneg v
  have h2 : (0 : ℂ) ≤ star v ⬝ᵥ ((ε : ℂ) • v) := by
    have hone : (0 : ℂ) ≤ star v ⬝ᵥ ((1 : Matrix n n ℂ) *ᵥ v) :=
      Matrix.PosDef.one.posSemidef.dotProduct_mulVec_nonneg v
    rw [Matrix.one_mulVec] at hone
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (by exact_mod_cast hε) hone
  exact add_nonneg h1 h2

/-! ### The mixture of shifts -/

omit [Fintype n] in
theorem sum_smul_shift {ι : Type*} [Fintype ι] (lam : ι → ℝ)
    (hsum : ∑ j, lam j = 1) (A : ι → Matrix n n ℂ) (ε : ℝ) :
    ∑ j, lam j • (A j + ε • 1) = (∑ j, lam j • A j) + ε • 1 := by
  have hsplit : ∀ j, lam j • (A j + ε • (1 : Matrix n n ℂ)) =
      lam j • A j + lam j • (ε • (1 : Matrix n n ℂ)) := fun j =>
    smul_add _ _ _
  simp only [hsplit]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_smul, hsum, one_smul]

/-! ### The fixed-basis perturbation formulas -/

/-- **The fixed-basis shift formula**:
`D(ρ+ε1‖σ+ε1) = Σᵢ(pᵢ+ε)log(pᵢ+ε) − Σᵢⱼ(pᵢ+ε)log(qⱼ+ε)|Wᵢⱼ|²`, with
`ε`-independent overlap weights. -/
theorem relEntropy_shift_formula (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (ε : ℝ) (hρε : (ρ + ε • 1).IsHermitian)
    (hσε : (σ + ε • 1).IsHermitian) :
    relEntropy hρε hσε =
      (∑ i, (hρ.eigenvalues i + ε) * Real.log (hρ.eigenvalues i + ε)) -
      ∑ i, ∑ j, (hρ.eigenvalues i + ε) *
        Real.log (hσ.eigenvalues j + ε) *
        Complex.normSq (overlap hρ hσ i j) := by
  unfold relEntropy matLog
  rw [matFun_shift hρ ε hρε Real.log, matFun_shift hσ ε hσε Real.log]
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re]
  congr 1
  · rw [shift_eq_matFun hρ ε, matFun_mul, trace_matFun_re]
  · rw [shift_eq_matFun hρ ε]
    exact trace_matFun_mul_matFun_re hρ hσ _ _

/-- The `ε = 0` counterpart of the shift formula. -/
theorem relEntropy_eq_spread (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy hρ hσ =
      (∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i)) -
      ∑ i, ∑ j, hρ.eigenvalues i * Real.log (hσ.eigenvalues j) *
        Complex.normSq (overlap hρ hσ i j) := by
  unfold relEntropy matLog
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re,
    trace_mul_matFun_self hρ Real.log, trace_mul_matFun_re hρ hσ Real.log]

end QRE
end NCG
