/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.PsdCalculusExact

/-!
# The matrix geometric mean: certificate and maximality

Step (D4c) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: Ando's block characterization of the
matrix geometric mean `A # B = √A (√A⁻¹ B √A⁻¹)^{1/2} √A`.

* `geoMean`: the geometric mean of a positive definite `A` and Hermitian
  `B`;
* `geoMean_certificate`: `[[A, A#B],[A#B, B]] ⪰ 0` — the Gram congruence;
* `geoMean_maximal`: any Hermitian `X` with `[[A, X],[X, B]] ⪰ 0`
  satisfies `X ⪯ A#B` — via the Schur corner, square-root uniqueness for
  `|Y|`, and Loewner monotonicity of the square root.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B S X : Matrix n n ℂ}

/-! ### Conjugation helpers -/

omit [DecidableEq n] in
theorem conj_isHermitian {M W : Matrix n n ℂ} (hM : M.IsHermitian)
    (hW : W.IsHermitian) : (W * M * W).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hM.eq, hW.eq,
    Matrix.mul_assoc]

omit [DecidableEq n] in
theorem conj_posSemidef {M W : Matrix n n ℂ} (hM : M.PosSemidef)
    (hW : W.IsHermitian) : (W * M * W).PosSemidef := by
  have h := hM.mul_mul_conjTranspose_same W
  rwa [hW.eq] at h

theorem matFun_sub (hS : S.IsHermitian) (f g : ℝ → ℝ) :
    matFun hS f - matFun hS g = matFun hS fun x => f x - g x := by
  unfold matFun
  rw [← map_sub]
  congr 1
  rw [Matrix.diagonal_sub]
  congr 1
  funext i
  simp [Function.comp]

/-! ### Square-root inverse identities -/

theorem sqrtMat_mul_invSqrtMat (hA : A.PosDef) :
    Petz.sqrtMat hA.1 * Petz.invSqrtMat hA.1 = 1 := by
  unfold Petz.sqrtMat Petz.invSqrtMat
  rw [matFun_mul]
  rw [Petz.matFun_congr hA.1 _ (fun _ => 1) fun i => ?_]
  · exact Petz.matFun_one hA.1
  · have hpos := hA.eigenvalues_pos i
    have hs : Real.sqrt (hA.1.eigenvalues i) ≠ 0 :=
      (Real.sqrt_pos.mpr hpos).ne'
    field_simp

theorem invSqrtMat_mul_sqrtMat (hA : A.PosDef) :
    Petz.invSqrtMat hA.1 * Petz.sqrtMat hA.1 = 1 := by
  unfold Petz.sqrtMat Petz.invSqrtMat
  rw [matFun_mul]
  rw [Petz.matFun_congr hA.1 _ (fun _ => 1) fun i => ?_]
  · exact Petz.matFun_one hA.1
  · have hpos := hA.eigenvalues_pos i
    have hs : Real.sqrt (hA.1.eigenvalues i) ≠ 0 :=
      (Real.sqrt_pos.mpr hpos).ne'
    field_simp

/-- Conjugating the inverse-square-root sandwich back. -/
theorem sqrt_conj_invconj (hA : A.PosDef) (M : Matrix n n ℂ) :
    Petz.sqrtMat hA.1 *
      (Petz.invSqrtMat hA.1 * M * Petz.invSqrtMat hA.1) *
      Petz.sqrtMat hA.1 = M := by
  calc Petz.sqrtMat hA.1 *
        (Petz.invSqrtMat hA.1 * M * Petz.invSqrtMat hA.1) *
        Petz.sqrtMat hA.1
      = (Petz.sqrtMat hA.1 * Petz.invSqrtMat hA.1) * M *
          (Petz.invSqrtMat hA.1 * Petz.sqrtMat hA.1) := by
        simp only [Matrix.mul_assoc]
    _ = M := by
        rw [sqrtMat_mul_invSqrtMat hA, invSqrtMat_mul_sqrtMat hA,
          Matrix.one_mul, Matrix.mul_one]

/-! ### The geometric mean -/

/-- The compressed core `√A⁻¹ B √A⁻¹`. -/
noncomputable def meanCore (hA : A.PosDef) (B : Matrix n n ℂ) :
    Matrix n n ℂ :=
  Petz.invSqrtMat hA.1 * B * Petz.invSqrtMat hA.1

theorem meanCore_isHermitian (hA : A.PosDef) (hB : B.IsHermitian) :
    (meanCore hA B).IsHermitian :=
  conj_isHermitian hB (Petz.invSqrtMat_isHermitian hA.1)

theorem meanCore_posSemidef (hA : A.PosDef) (hB : B.PosSemidef) :
    (meanCore hA B).PosSemidef :=
  conj_posSemidef hB (Petz.invSqrtMat_isHermitian hA.1)

/-- **The matrix geometric mean** `A # B = √A (√A⁻¹ B √A⁻¹)^{1/2} √A`. -/
noncomputable def geoMean (hA : A.PosDef) (hB : B.IsHermitian) :
    Matrix n n ℂ :=
  Petz.sqrtMat hA.1 * Petz.sqrtMat (meanCore_isHermitian hA hB) *
    Petz.sqrtMat hA.1

theorem geoMean_isHermitian (hA : A.PosDef) (hB : B.IsHermitian) :
    (geoMean hA hB).IsHermitian := by
  unfold geoMean
  exact conj_isHermitian
    (Petz.sqrtMat_isHermitian (meanCore_isHermitian hA hB))
    (Petz.sqrtMat_isHermitian hA.1)

/-! ### The block certificate -/

set_option maxHeartbeats 1600000 in -- block Gram congruence
/-- **The certificate**: `[[A, A#B],[A#B, B]] ⪰ 0`. -/
theorem geoMean_certificate (hA : A.PosDef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A (geoMean hA hB.1) (geoMean hA hB.1) B).PosSemidef
    := by
  have hCh := meanCore_isHermitian hA hB.1
  have hCpsd := meanCore_posSemidef hA hB
  have hRh := Petz.sqrtMat_isHermitian hCh
  -- the inner Gram block
  have hGram : (Matrix.fromBlocks 1 (Petz.sqrtMat hCh)
      (Petz.sqrtMat hCh) (meanCore hA B)).PosSemidef := by
    have hL : (Matrix.fromBlocks (1 : Matrix n n ℂ)
        (Petz.sqrtMat hCh) 0 0)ᴴ *
        Matrix.fromBlocks (1 : Matrix n n ℂ) (Petz.sqrtMat hCh) 0 0 =
        Matrix.fromBlocks 1 (Petz.sqrtMat hCh) (Petz.sqrtMat hCh)
          (meanCore hA B) := by
      rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      have hs : Petz.sqrtMat hCh * Petz.sqrtMat hCh = meanCore hA B :=
        Petz.sqrtMat_mul_self hCpsd
      simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
        Matrix.one_mul, Matrix.mul_zero, add_zero,
        Matrix.mul_one, hRh.eq, hs]
    rw [← hL]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  -- the outer congruence
  have hcong : Matrix.fromBlocks A (geoMean hA hB.1) (geoMean hA hB.1) B =
      Matrix.fromBlocks (Petz.sqrtMat hA.1) 0 0 (Petz.sqrtMat hA.1) *
        Matrix.fromBlocks 1 (Petz.sqrtMat hCh) (Petz.sqrtMat hCh)
          (meanCore hA B) *
        Matrix.fromBlocks (Petz.sqrtMat hA.1) 0 0 (Petz.sqrtMat hA.1) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
      add_zero, zero_add]
    rw [Matrix.fromBlocks_inj]
    refine ⟨(Petz.sqrtMat_mul_self hA.posSemidef).symm, rfl, rfl, ?_⟩
    change B = Petz.sqrtMat hA.1 *
      (Petz.invSqrtMat hA.1 * B * Petz.invSqrtMat hA.1) * Petz.sqrtMat hA.1
    exact (sqrt_conj_invconj hA B).symm
  rw [hcong]
  have hE : (Matrix.fromBlocks (Petz.sqrtMat hA.1) 0 0
      (Petz.sqrtMat hA.1)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.fromBlocks_conjTranspose]
    simp [Matrix.conjTranspose_zero, (Petz.sqrtMat_isHermitian hA.1).eq]
  exact conj_posSemidef hGram hE

/-! ### Maximality -/

set_option maxHeartbeats 3200000 in -- Schur corner + sqrt-order chain
/-- **Maximality of the geometric mean** (Ando): any certified Hermitian
`X` satisfies `X ⪯ A # B`. -/
theorem geoMean_maximal (hA : A.PosDef) (hB : B.PosSemidef)
    (hX : X.IsHermitian)
    (hcert : (Matrix.fromBlocks A X X B).PosSemidef) :
    (geoMean hA hB.1 - X).PosSemidef := by
  have hCh := meanCore_isHermitian hA hB.1
  have hCpsd := meanCore_posSemidef hA hB
  set Y := Petz.invSqrtMat hA.1 * X * Petz.invSqrtMat hA.1 with hYdef
  have hYh : Y.IsHermitian :=
    conj_isHermitian hX (Petz.invSqrtMat_isHermitian hA.1)
  -- compress the certificate
  have hM' : (Matrix.fromBlocks 1 Y Y (meanCore hA B)).PosSemidef := by
    have hE := hcert.mul_mul_conjTranspose_same
      (Matrix.fromBlocks (Petz.invSqrtMat hA.1) 0 0 (Petz.invSqrtMat hA.1))
    have hcomp : Matrix.fromBlocks (Petz.invSqrtMat hA.1) 0 0
        (Petz.invSqrtMat hA.1) *
        Matrix.fromBlocks A X X B *
        (Matrix.fromBlocks (Petz.invSqrtMat hA.1) 0 0
          (Petz.invSqrtMat hA.1))ᴴ =
        Matrix.fromBlocks 1 Y Y (meanCore hA B) := by
      rw [Matrix.fromBlocks_conjTranspose]
      rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        Matrix.conjTranspose_zero, (Petz.invSqrtMat_isHermitian hA.1).eq]
      rw [Matrix.fromBlocks_inj]
      exact ⟨Petz.invSqrt_conj_self hA, rfl, rfl, rfl⟩
    rwa [hcomp] at hE
  have hcorner := schur_corner hYh hM'
  -- |Y| = √(Y²)
  have hY2 : (Y * Y).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self Y
    rwa [hYh.eq] at h
  have habs_psd : (matFun hYh fun x => |x|).PosSemidef :=
    matFun_posSemidef hYh _ fun _ => abs_nonneg _
  have habs_sq : matFun hYh (fun x => |x|) * matFun hYh (fun x => |x|) =
      Y * Y := by
    rw [matFun_mul]
    have hid : matFun hYh (fun x => id x * id x) =
        matFun hYh id * matFun hYh id := (matFun_mul hYh id id).symm
    rw [Petz.matFun_congr hYh _ (fun x => id x * id x)
      fun i => abs_mul_abs_self _, hid, Petz.matFun_id hYh]
  have habs_eq : matFun hYh (fun x => |x|) = Petz.sqrtMat hY2.1 :=
    posSemidef_sqrt_unique hY2 habs_psd habs_sq
  -- √C − |Y| and |Y| − Y
  have hmono := sqrtMat_monotone hY2 hCpsd hcorner
  have habs_ge : (matFun hYh (fun x => |x|) - Y).PosSemidef := by
    have hsub : matFun hYh (fun x => |x| - x) =
        matFun hYh (fun x => |x|) - Y := by
      rw [← matFun_sub]
      congr 1
      exact Petz.matFun_id hYh
    rw [← hsub]
    exact matFun_posSemidef hYh _ fun _ => sub_nonneg.mpr (le_abs_self _)
  have hchain : (Petz.sqrtMat hCh - Y).PosSemidef := by
    have hsplit : Petz.sqrtMat hCh - Y =
        (Petz.sqrtMat hCh - Petz.sqrtMat hY2.1) +
          (matFun hYh (fun x => |x|) - Y) := by
      rw [habs_eq]
      abel
    rw [hsplit]
    exact hmono.add habs_ge
  -- conjugate back
  have hback : geoMean hA hB.1 - X =
      Petz.sqrtMat hA.1 * (Petz.sqrtMat hCh - Y) * Petz.sqrtMat hA.1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    unfold geoMean
    have hXback : Petz.sqrtMat hA.1 * Y * Petz.sqrtMat hA.1 = X := by
      rw [hYdef]
      exact sqrt_conj_invconj hA X
    rw [hXback]
  rw [hback]
  exact conj_posSemidef hchain (Petz.sqrtMat_isHermitian hA.1)

end QRE
end NCG
