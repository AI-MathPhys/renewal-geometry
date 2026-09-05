/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.GeometricMeanExact

/-!
# Order properties of the matrix geometric mean

Step (D4d) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: joint concavity, right-monotonicity, and
the commuting collapse of the geometric mean — all from the block
certificate and its maximality.

* `geoMean_concave`: `(Σλ A_k) # (Σλ B_k) ⪰ Σ λ_k (A_k # B_k)`;
* `geoMean_monotone_right`: `B ⪯ B' → A # B ⪯ A # B'`;
* `geoMean_posSemidef`: the mean of PSD data is PSD;
* `geoMean_commute`: for commuting `A, B`, `A # B = √A √B`.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B S X : Matrix n n ℂ}

/-! ### Block sums -/

omit [Fintype n] [DecidableEq n] in
theorem fromBlocks_sum {ι : Type*} (s : Finset ι)
    (fA fB fC fD : ι → Matrix n n ℂ) :
    ∑ k ∈ s, Matrix.fromBlocks (fA k) (fB k) (fC k) (fD k) =
      Matrix.fromBlocks (∑ k ∈ s, fA k) (∑ k ∈ s, fB k)
        (∑ k ∈ s, fC k) (∑ k ∈ s, fD k) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      simp only [Finset.sum_empty]
      ext (i | i) (j | j) <;> rfl
  | cons a s ha ih =>
      simp only [Finset.sum_cons, ih, Matrix.fromBlocks_add]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [DecidableEq n] in
/-- The lower-right block padding is PSD. -/
theorem posSemidef_fromBlocks_zero {M : Matrix n n ℂ}
    (hM : M.PosSemidef) :
    (Matrix.fromBlocks (0 : Matrix n n ℂ) 0 0 M).PosSemidef := by
  have hherm : (Matrix.fromBlocks (0 : Matrix n n ℂ) 0 0 M).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.fromBlocks_conjTranspose]
    simp [hM.1.eq]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun v => ?_
  have hv : v = Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) := by
    funext i
    cases i <;> rfl
  rw [hv, Matrix.fromBlocks_mulVec, star_sum_elim, sum_elim_dot]
  simp only [Matrix.zero_mulVec, add_zero, zero_add, dotProduct_zero]
  simpa using hM.dotProduct_mulVec_nonneg fun i => v (Sum.inr i)

/-! ### Joint concavity -/

set_option maxHeartbeats 1600000 in -- summed certificates
/-- **Joint concavity of the geometric mean** (Ando):
`(Σλ A_k) # (Σλ B_k) ⪰ Σ λ_k (A_k # B_k)`. -/
theorem geoMean_concave {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ k, 0 ≤ lam k)
    {Amat Bmat : ι → Matrix n n ℂ}
    (hAk : ∀ k, (Amat k).PosDef) (hBk : ∀ k, (Bmat k).PosSemidef)
    (hAbar : (∑ k, lam k • Amat k).PosDef)
    (hBbar : (∑ k, lam k • Bmat k).PosSemidef) :
    (geoMean hAbar hBbar.1 -
      ∑ k, lam k • geoMean (hAk k) (hBk k).1).PosSemidef := by
  have hXh : (∑ k, lam k • geoMean (hAk k) (hBk k).1).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_smul, star_trivial,
      (geoMean_isHermitian (hAk k) (hBk k).1).eq]
  refine geoMean_maximal hAbar hBbar hXh ?_
  have hsum : Matrix.fromBlocks (∑ k, lam k • Amat k)
      (∑ k, lam k • geoMean (hAk k) (hBk k).1)
      (∑ k, lam k • geoMean (hAk k) (hBk k).1)
      (∑ k, lam k • Bmat k) =
      ∑ k, lam k • Matrix.fromBlocks (Amat k)
        (geoMean (hAk k) (hBk k).1)
        (geoMean (hAk k) (hBk k).1) (Bmat k) := by
    have h1 : ∀ k, lam k • Matrix.fromBlocks (Amat k)
        (geoMean (hAk k) (hBk k).1)
        (geoMean (hAk k) (hBk k).1) (Bmat k) =
        Matrix.fromBlocks (lam k • Amat k)
          (lam k • geoMean (hAk k) (hBk k).1)
          (lam k • geoMean (hAk k) (hBk k).1)
          (lam k • Bmat k) := fun k => Matrix.fromBlocks_smul _ _ _ _ _
    simp only [h1]
    rw [fromBlocks_sum]
  rw [hsum]
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb)
    Matrix.PosSemidef.zero fun k _ => ?_
  exact posSemidef_smul_real (hlam k)
    (geoMean_certificate (hAk k) (hBk k))

/-! ### Right monotonicity -/

/-- `B ⪯ B' → A # B ⪯ A # B'`. -/
theorem geoMean_monotone_right (hA : A.PosDef) {B B' : Matrix n n ℂ}
    (hB : B.PosSemidef) (hB' : B'.PosSemidef)
    (hBB' : (B' - B).PosSemidef) :
    (geoMean hA hB'.1 - geoMean hA hB.1).PosSemidef := by
  refine geoMean_maximal hA hB' (geoMean_isHermitian hA hB.1) ?_
  have hpad : Matrix.fromBlocks A (geoMean hA hB.1) (geoMean hA hB.1) B' =
      Matrix.fromBlocks A (geoMean hA hB.1) (geoMean hA hB.1) B +
        Matrix.fromBlocks 0 0 0 (B' - B) := by
    rw [Matrix.fromBlocks_add, Matrix.fromBlocks_inj]
    exact ⟨(add_zero A).symm, (add_zero _).symm, (add_zero _).symm,
      by abel⟩
  rw [hpad]
  exact (geoMean_certificate hA hB).add (posSemidef_fromBlocks_zero hBB')

/-! ### Positivity and the commuting collapse -/

theorem geoMean_posSemidef (hA : A.PosDef) (hB : B.PosSemidef) :
    (geoMean hA hB.1).PosSemidef := by
  unfold geoMean
  exact conj_posSemidef
    (sqrtMat_posSemidef (meanCore_posSemidef hA hB))
    (Petz.sqrtMat_isHermitian hA.1)

set_option maxHeartbeats 3200000 in -- commuting square-root uniqueness
/-- **The commuting collapse**: for commuting `A, B`,
`A # B = √A √B`. -/
theorem geoMean_commute (hA : A.PosDef) (hB : B.PosSemidef)
    (hcomm : Commute A B) :
    geoMean hA hB.1 = Petz.sqrtMat hA.1 * Petz.sqrtMat hB.1 := by
  have hT : (Petz.invSqrtMat hA.1).PosSemidef :=
    matFun_posSemidef hA.1 _ fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _)
  -- commutation chains
  have hBT : Commute B (Petz.invSqrtMat hA.1) :=
    commute_matFun_right hA.1 _ hcomm.symm
  have hsBT : Commute (Petz.sqrtMat hB.1) (Petz.invSqrtMat hA.1) :=
    (commute_matFun_right hB.1 Real.sqrt hBT.symm).symm
  have hsAsB : Commute (Petz.sqrtMat hA.1) (Petz.sqrtMat hB.1) := by
    have h1 : Commute A (Petz.sqrtMat hB.1) :=
      commute_matFun_right hB.1 Real.sqrt hcomm
    exact (commute_matFun_right hA.1 Real.sqrt h1.symm).symm
  -- X := √B ∘ invS is the PSD square root of the mean core
  set T := Petz.invSqrtMat hA.1 with hTdef
  set Thalf := Petz.sqrtMat hT.1 with hThdef
  have hThsq : Thalf * Thalf = T := Petz.sqrtMat_mul_self hT
  have hsBTh : Commute (Petz.sqrtMat hB.1) Thalf :=
    commute_matFun_right hT.1 Real.sqrt hsBT
  have hXpsd : (Petz.sqrtMat hB.1 * T).PosSemidef := by
    have hform : Petz.sqrtMat hB.1 * T =
        Thalf * Petz.sqrtMat hB.1 * Thalf := by
      calc Petz.sqrtMat hB.1 * T
          = Petz.sqrtMat hB.1 * (Thalf * Thalf) := by rw [hThsq]
        _ = Thalf * Petz.sqrtMat hB.1 * Thalf := by
            rw [← Matrix.mul_assoc, hsBTh.eq]
    rw [hform]
    exact conj_posSemidef (sqrtMat_posSemidef hB)
      (Petz.sqrtMat_isHermitian hT.1)
  have hXsq : (Petz.sqrtMat hB.1 * T) * (Petz.sqrtMat hB.1 * T) =
      meanCore hA B := by
    have h1 : (Petz.sqrtMat hB.1 * T) * (Petz.sqrtMat hB.1 * T) =
        (Petz.sqrtMat hB.1 * Petz.sqrtMat hB.1) * (T * T) := by
      calc (Petz.sqrtMat hB.1 * T) * (Petz.sqrtMat hB.1 * T)
          = Petz.sqrtMat hB.1 * (T * Petz.sqrtMat hB.1) * T := by
            simp only [Matrix.mul_assoc]
        _ = Petz.sqrtMat hB.1 * (Petz.sqrtMat hB.1 * T) * T := by
            rw [hsBT.eq]
        _ = (Petz.sqrtMat hB.1 * Petz.sqrtMat hB.1) * (T * T) := by
            simp only [Matrix.mul_assoc]
    rw [h1, Petz.sqrtMat_mul_self hB]
    unfold meanCore
    calc B * (T * T) = (B * T) * T := by rw [Matrix.mul_assoc]
      _ = (T * B) * T := by rw [hBT.eq]
      _ = T * B * T := rfl
  have hXeq : Petz.sqrtMat hB.1 * T =
      Petz.sqrtMat (meanCore_isHermitian hA hB.1) :=
    posSemidef_sqrt_unique (meanCore_posSemidef hA hB) hXpsd hXsq
  -- collapse
  unfold geoMean
  rw [← hXeq]
  calc Petz.sqrtMat hA.1 * (Petz.sqrtMat hB.1 * T) * Petz.sqrtMat hA.1
      = Petz.sqrtMat hB.1 * (Petz.sqrtMat hA.1 * T) * Petz.sqrtMat hA.1 := by
        rw [← Matrix.mul_assoc, hsAsB.eq]
        simp only [Matrix.mul_assoc]
    _ = Petz.sqrtMat hB.1 * Petz.sqrtMat hA.1 := by
        rw [hTdef, sqrtMat_mul_invSqrtMat hA, Matrix.mul_one]
    _ = Petz.sqrtMat hA.1 * Petz.sqrtMat hB.1 := hsAsB.eq.symm

end QRE
end NCG
