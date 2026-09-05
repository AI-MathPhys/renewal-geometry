/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTAtlasCompleteness
import NCG.Grand.AtlasMissingBankExact
import NCG.Grand.PositiveOperatorNormBridgeExact
import NCG.Grand.ProtectedObservableRieszPseudoinverseExact

/-!
# The atlas margin forces source completeness

This is the missing transfer step SA.10 in `thm:GT-two-margin-closure`.
For a complete atlas with lower frame floor `m`, every genuinely missing
physical direction makes the positive completeness Gram have operator norm at
least `m`.  Hence the strict atlas margin forces the reached projection to be
the identity.
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace GTAtlasMargin

private noncomputable def eNorm {i : Type*} [Fintype i] (x : i → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℂ i)‖

/-- **SA.10 exact transfer.**  A surjective physical atlas `U` with lower
frame floor `m` cannot have a nontrivial orthogonal complement to `P` if the
completeness Gram has norm strictly below `m`. -/
theorem atlas_margin_forces_identity
    {n e : Type} [Fintype n] [Fintype e]
    [DecidableEq n] [DecidableEq e]
    (P : Matrix n n ℂ) (hP2 : P * P = P) (hPH : Pᴴ = P)
    (U : Matrix n e ℂ) (m : ℝ) (hm : 0 < m)
    (hUsurj : Function.Surjective U.mulVecLin)
    (hUfloor : ∀ x : e → ℂ, m * eNorm x ^ 2 ≤ eNorm (U *ᵥ x) ^ 2)
    (hmargin : ‖Uᴴ * (1 - P) * U‖ < m) :
    P = 1 := by
  let A : Matrix n e ℂ := (1 - P) * U
  let C : Matrix e e ℂ := Uᴴ * (1 - P) * U
  have h1P2 : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, hP2]
    abel
  have h1PH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hCA : C = Aᴴ * A := by
    unfold C A
    rw [Matrix.conjTranspose_mul, h1PH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 - P) (1 - P) U, h1P2]
  have hCpsd : C.PosSemidef := by
    rw [hCA]
    exact Matrix.posSemidef_conjTranspose_mul_self A
  have hscaledPsd : ((m⁻¹ : ℝ) • C).PosSemidef :=
    hCpsd.smul (by exact_mod_cast (inv_nonneg.mpr hm.le))
  have hscaledNorm : ‖(m⁻¹ : ℝ) • C‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
    have hCm : ‖C‖ < m := by simpa [C] using hmargin
    rw [inv_mul_lt_one₀ hm]
    exact hCm
  have hstrict : (1 - (m⁻¹ : ℝ) • C).PosDef :=
    (PositiveNormBridge.norm_lt_one_iff_posDef_one_sub hscaledPsd).mp hscaledNorm
  by_contra hPne
  have hcompne : (1 - P : Matrix n n ℂ) ≠ 0 := by
    intro hzero
    apply hPne
    exact (sub_eq_zero.mp hzero).symm
  obtain ⟨y, hy⟩ : ∃ y : n → ℂ, (1 - P) *ᵥ y ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hcompne
    ext i j
    have hcol := hnone (Pi.single j 1)
    rw [Matrix.mulVec_single_one] at hcol
    exact congrFun hcol i
  let v : n → ℂ := (1 - P) *ᵥ y
  have hvne : v ≠ 0 := hy
  have hPv : P *ᵥ v = 0 := by
    unfold v
    rw [Matrix.mulVec_mulVec]
    have hPcomp : P * (1 - P) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, hP2, sub_self]
    rw [hPcomp, Matrix.zero_mulVec]
  obtain ⟨x, hx⟩ := hUsurj v
  have hxvec : U *ᵥ x = v := hx
  have hxne : x ≠ 0 := by
    intro hx0
    apply hvne
    rw [← hxvec, hx0, Matrix.mulVec_zero]
  have hatlas := gt_atlas_completeness P hP2 hPH U
  have hvalue := hatlas.2.2 x v hxvec hPv
  have hvalueC : star x ⬝ᵥ (C *ᵥ x) = star v ⬝ᵥ v := by
    simpa [C] using hvalue
  have hqpos := hstrict.dotProduct_mulVec_pos hxne
  have hselfx :=
    ProtectedObservableRiesz.star_dot_self_eq_norm_sq x
  have hselfv :=
    ProtectedObservableRiesz.star_dot_self_eq_norm_sq v
  have hre :
      ((star x ⬝ᵥ x) - (m⁻¹ : ℂ) * (star x ⬝ᵥ (C *ᵥ x))).re > 0 := by
    simpa [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] using
      (Complex.lt_def.mp hqpos).1
  rw [hvalueC, hselfx, hselfv] at hre
  have hfloor := hUfloor x
  rw [hxvec] at hfloor
  norm_num [Complex.sub_re, Complex.mul_re] at hre
  dsimp [eNorm] at hfloor
  have hxnorm_re :
      ((↑‖(WithLp.toLp 2 x : EuclideanSpace ℂ e)‖ : ℂ) ^ 2).re =
        ‖(WithLp.toLp 2 x : EuclideanSpace ℂ e)‖ ^ 2 := by
    norm_num [pow_two, Complex.mul_re]
  have hvnorm_re :
      ((↑‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ : ℂ) ^ 2).re =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 := by
    norm_num [pow_two, Complex.mul_re]
  rw [hxnorm_re, hvnorm_re] at hre
  have hmne : m ≠ 0 := ne_of_gt hm
  nlinarith [inv_mul_cancel₀ hmne]

end GTAtlasMargin
end NCG
