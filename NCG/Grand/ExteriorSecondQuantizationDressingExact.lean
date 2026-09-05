/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCompoundMatrixExteriorPower
import NCG.Grand.PsdCalculusExact
import NCG.Grand.SqrtPolar

/-!
# One-sided dressing for exterior second quantization

This file proves `cor:SMQG-dressing` grade by grade on the concrete finite
wedge carrier.  The dressing map need not be invertible.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace ExteriorSecondQuantizationDressing

open FiniteCompoundMatrixExteriorPower

variable {d : ℕ} {F : Type*} [Fintype F]

/-- The grade-`r` instance of `K_{P,W,q}=q W* (⋀^r P) W`. -/
noncomputable def dressedExteriorKernel
    (q : ℝ) (P : Matrix (Fin d) (Fin d) ℂ) (r : ℕ)
    (W : Matrix (GradeIdx r d) F ℂ) : Matrix F F ℂ :=
  (q : ℂ) • (Wᴴ * cmpd r P * W)

/-- The canonical displayed Gram synthesis
`q^{1/2} (⋀^r P)^{1/2} W`. -/
noncomputable def dressedExteriorSynthesis
    (q : ℝ) (P : Matrix (Fin d) (Fin d) ℂ) (r : ℕ)
    (W : Matrix (GradeIdx r d) F ℂ) : Matrix (GradeIdx r d) F ℂ :=
  (Real.sqrt q : ℂ) • (CFC.sqrt (cmpd r P) * W)

/-- QG.24: one-sided dressing preserves positivity without any invertibility
hypothesis on `W`. -/
theorem dressedExteriorKernel_posSemidef
    {q : ℝ} (hq : 0 ≤ q) {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosSemidef) (r : ℕ) (W : Matrix (GradeIdx r d) F ℂ) :
    (dressedExteriorKernel q P r W).PosSemidef := by
  have hgrade : (cmpd r P).PosSemidef := cmpd_posSemidef hP
  have hcong : (Wᴴ * cmpd r P * W).PosSemidef := by
    simpa only [Matrix.mul_assoc] using hgrade.conjTranspose_mul_mul_same W
  exact QRE.posSemidef_smul_real hq hcong

/-- QG.25: the displayed synthesis has exactly the dressed kernel as its
Gram matrix. -/
theorem dressedExteriorKernel_eq_synthesisGram
    {q : ℝ} (hq : 0 ≤ q) {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosSemidef) (r : ℕ) (W : Matrix (GradeIdx r d) F ℂ) :
    dressedExteriorKernel q P r W =
      (dressedExteriorSynthesis q P r W)ᴴ *
        dressedExteriorSynthesis q P r W := by
  have hgrade : (cmpd r P).PosSemidef := cmpd_posSemidef hP
  have hsqrt : (CFC.sqrt (cmpd r P))ᴴ * CFC.sqrt (cmpd r P) = cmpd r P := by
    rw [sqrt_isHermitian, sqrt_mul_self_eq _ hgrade]
  have hqroot : (Real.sqrt q : ℂ) * (Real.sqrt q : ℂ) = (q : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt hq
  unfold dressedExteriorKernel dressedExteriorSynthesis
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Complex.star_def, Complex.conj_ofReal]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (CFC.sqrt (cmpd r P))ᴴ
    (CFC.sqrt (cmpd r P)) W]
  rw [hsqrt]
  rw [smul_smul, hqroot]

end ExteriorSecondQuantizationDressing
end NCG
