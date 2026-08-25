/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.HSMatrixizationExact

/-!
# The dyadic geometric-mean iterate and its joint concavity

Step (D4f) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: iterating `T ↦ Λ # T` produces the dyadic
interpolation family `Λ^{1−2⁻ᵏ} Ρ^{2⁻ᵏ}` on commuting legs; joint
concavity of every iterate follows from concavity and monotonicity of the
binary mean by induction.

* `iterMean`: the `k`-fold iterate `Λ # (Λ # (⋯ # Ρ))`;
* `psd_sub_trans`: transitivity of the Loewner order;
* `iterMean_concave`: **joint concavity of every dyadic iterate**;
* `commute_psd_mul_psd`, `sqrt_matFun_rpow`: commuting-product PSD and the
  square-root/power identity, for the closed commuting form.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {S Λ Ρ P Q : Matrix n n ℂ}

/-! ### Loewner transitivity -/

omit [Fintype n] [DecidableEq n] in
theorem psd_sub_trans {X Y Z : Matrix n n ℂ}
    (h1 : (X - Y).PosSemidef) (h2 : (Y - Z).PosSemidef) :
    (X - Z).PosSemidef := by
  have h := h1.add h2
  have heq : X - Y + (Y - Z) = X - Z := by abel
  rwa [heq] at h

/-! ### Commuting PSD products -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
theorem commute_psd_mul_psd (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (hcomm : Commute P Q) : (P * Q).PosSemidef := by
  have hsq : Commute (Petz.sqrtMat hP.1) Q :=
    (commute_matFun_right hP.1 Real.sqrt hcomm.symm).symm
  have hform : P * Q = Petz.sqrtMat hP.1 * Q * Petz.sqrtMat hP.1 := by
    calc P * Q = Petz.sqrtMat hP.1 * Petz.sqrtMat hP.1 * Q := by
          rw [Petz.sqrtMat_mul_self hP]
      _ = Petz.sqrtMat hP.1 * (Petz.sqrtMat hP.1 * Q) := by
          rw [Matrix.mul_assoc]
      _ = Petz.sqrtMat hP.1 * (Q * Petz.sqrtMat hP.1) := by
          rw [hsq.eq]
      _ = Petz.sqrtMat hP.1 * Q * Petz.sqrtMat hP.1 := by
          rw [Matrix.mul_assoc]
  rw [hform]
  exact conj_posSemidef hQ (Petz.sqrtMat_isHermitian hP.1)

/-! ### Square roots of spectral powers -/

theorem sqrt_matFun_rpow (hS : S.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hpsd : (matFun hS.1 fun x => x ^ a).PosSemidef) :
    Petz.sqrtMat hpsd.1 = matFun hS.1 fun x => x ^ (a / 2) := by
  refine (posSemidef_sqrt_unique hpsd
    (matFun_posSemidef hS.1 _ fun i =>
      Real.rpow_nonneg (hS.eigenvalues_nonneg i) _) ?_).symm
  rw [matFun_mul]
  refine Petz.matFun_congr hS.1 _ _ fun i => ?_
  rcases eq_or_lt_of_le (hS.eigenvalues_nonneg i) with h0 | hpos
  · rw [← h0]
    rw [Real.zero_rpow (by positivity : a / 2 ≠ 0),
      Real.zero_rpow ha.ne', mul_zero]
  · rw [← Real.rpow_add hpos]
    congr 1
    ring

/-! ### The dyadic iterate -/

/-- The `k`-fold geometric-mean iterate, carrying its Hermitian
certificate. -/
noncomputable def iterMeanAux (hΛ : Λ.PosDef)
    (start : {M : Matrix n n ℂ // M.IsHermitian}) :
    ℕ → {M : Matrix n n ℂ // M.IsHermitian}
  | 0 => start
  | k + 1 => ⟨geoMean hΛ (iterMeanAux hΛ start k).2,
      geoMean_isHermitian _ _⟩

/-- The dyadic interpolation `Λ #_{2⁻ᵏ} Ρ`. -/
noncomputable def iterMean (hΛ : Λ.PosDef) (hΡ : Ρ.IsHermitian)
    (k : ℕ) : Matrix n n ℂ :=
  (iterMeanAux hΛ ⟨Ρ, hΡ⟩ k).1

theorem iterMean_isHermitian (hΛ : Λ.PosDef) (hΡ : Ρ.IsHermitian)
    (k : ℕ) : (iterMean hΛ hΡ k).IsHermitian :=
  (iterMeanAux hΛ ⟨Ρ, hΡ⟩ k).2

theorem iterMean_zero (hΛ : Λ.PosDef) (hΡ : Ρ.IsHermitian) :
    iterMean hΛ hΡ 0 = Ρ := rfl

theorem iterMean_succ (hΛ : Λ.PosDef) (hΡ : Ρ.IsHermitian) (k : ℕ) :
    iterMean hΛ hΡ (k + 1) =
      geoMean hΛ (iterMean_isHermitian hΛ hΡ k) := rfl

theorem iterMean_posSemidef (hΛ : Λ.PosDef) (hΡ : Ρ.PosSemidef)
    (k : ℕ) : (iterMean hΛ hΡ.1 k).PosSemidef := by
  induction k with
  | zero => exact hΡ
  | succ k ih =>
      rw [iterMean_succ]
      exact geoMean_posSemidef hΛ ih

/-! ### Joint concavity of every iterate -/

set_option maxHeartbeats 3200000 in -- the inductive Ando chain
/-- **Joint concavity of the dyadic iterate**: for weights `λ_j ≥ 0`,
`(Σλ Λ_j) #_{2⁻ᵏ} (Σλ Ρ_j) ⪰ Σ λ_j (Λ_j #_{2⁻ᵏ} Ρ_j)`. -/
theorem iterMean_concave {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ j, 0 ≤ lam j)
    {Λmat Ρmat : ι → Matrix n n ℂ}
    (hΛj : ∀ j, (Λmat j).PosDef) (hΡj : ∀ j, (Ρmat j).PosSemidef)
    (hΛbar : (∑ j, lam j • Λmat j).PosDef)
    (hΡbar : (∑ j, lam j • Ρmat j).PosSemidef) (k : ℕ) :
    (iterMean hΛbar hΡbar.1 k -
      ∑ j, lam j • iterMean (hΛj j) (hΡj j).1 k).PosSemidef := by
  induction k with
  | zero =>
      simp only [iterMean_zero]
      rw [sub_self]
      exact Matrix.PosSemidef.zero
  | succ k ih =>
      simp only [iterMean_succ]
      -- the summed iterates are PSD and Hermitian
      have hsum_psd : (∑ j, lam j •
          iterMean (hΛj j) (hΡj j).1 k).PosSemidef := by
        refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb)
          Matrix.PosSemidef.zero fun j _ => ?_
        exact posSemidef_smul_real (hlam j)
          (iterMean_posSemidef (hΛj j) (hΡj j) k)
      have hbar_psd : (iterMean hΛbar hΡbar.1 k).PosSemidef :=
        iterMean_posSemidef hΛbar hΡbar k
      -- monotone step
      have hmono := geoMean_monotone_right hΛbar hsum_psd hbar_psd ih
      -- concave step
      have hconc := geoMean_concave hlam hΛj
        (fun j => iterMean_posSemidef (hΛj j) (hΡj j) k) hΛbar hsum_psd
      exact psd_sub_trans hmono hconc

end QRE
end NCG
