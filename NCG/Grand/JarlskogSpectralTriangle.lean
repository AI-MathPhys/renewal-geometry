/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JarlskogCommutatorIdentity

/-!
# Spectral triangle identity for the Jarlskog invariant

The imaginary part of the oriented product of three off-diagonal entries of a
three-generation Hermitian matrix is its cyclic spectral Vandermonde times the
Jarlskog quartet of any ordered pair of eigenframe columns.
-/

open Matrix

namespace NCG
namespace JarlskogSpectralTriangle

/-- Spectral-coordinate formula for `V diag(b₀,b₁,b₂) Vᴴ`. -/
def spectralHermitianMatrix (b₀ b₁ b₂ : ℝ)
    (V : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    (b₀ : ℂ) * V i 0 * star (V j 0) +
    (b₁ : ℂ) * V i 1 * star (V j 1) +
    (b₂ : ℂ) * V i 2 * star (V j 2)

lemma spectralHermitianMatrix_eq_eigenframeProduct (b₀ b₁ b₂ : ℝ)
    (V : Matrix (Fin 3) (Fin 3) ℂ) :
    spectralHermitianMatrix b₀ b₁ b₂ V =
      V * JarlskogCommutatorIdentity.eigenvalueDiagonal b₀ b₁ b₂ * Vᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spectralHermitianMatrix,
      JarlskogCommutatorIdentity.eigenvalueDiagonal,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

lemma spectralHermitianMatrix_isHermitian (b₀ b₁ b₂ : ℝ)
    (V : Matrix (Fin 3) (Fin 3) ℂ) :
    (spectralHermitianMatrix b₀ b₁ b₂ V)ᴴ =
      spectralHermitianMatrix b₀ b₁ b₂ V := by
  ext i j
  simp [spectralHermitianMatrix, Matrix.conjTranspose_apply, star_add,
    star_mul']
  ring

/-- Twice `i` times the imaginary part, written without division. -/
def skewPart (z : ℂ) : ℂ := z - star z

lemma skewPart_add (z w : ℂ) :
    skewPart (z + w) = skewPart z + skewPart w := by
  simp [skewPart]
  ring

lemma skewPart_star (z : ℂ) : skewPart (star z) = -skewPart z := by
  simp [skewPart]

lemma imaginaryPart_skewPart (z : ℂ) :
    Complex.im (skewPart z) = 2 * Complex.im z := by
  simp [skewPart]
  ring

lemma imaginaryPart_real_mul_skewPart (r : ℝ) (z : ℂ) :
    Complex.im ((r : ℂ) * skewPart z) = 2 * r * Complex.im z := by
  simp [skewPart, Complex.mul_im]
  ring

lemma skewPart_selfAdjoint_mul (w z : ℂ) (hw : star w = w) :
    skewPart (w * z) = w * skewPart z := by
  simp [skewPart, star_mul', hw]
  ring

/-- A single three-term orthogonality relation fixes the skew parts of all
oriented quartets formed from the three summands. -/
lemma threeTermOrthogonality_quartetSkew
    (x₀ x₁ x₂ : ℂ) (hzero : x₀ + x₁ + x₂ = 0) :
    skewPart (x₁ * star x₂) = -skewPart (x₁ * star x₀) ∧
    skewPart (x₂ * star x₀) = -skewPart (x₁ * star x₀) ∧
    skewPart (x₂ * star x₁) = skewPart (x₁ * star x₀) ∧
    skewPart (x₀ * star x₂) = skewPart (x₁ * star x₀) := by
  have hx₂ : x₂ = -x₀ - x₁ := by
    linear_combination hzero
  subst x₂
  constructor
  · simp [skewPart, star_mul']
    ring
  constructor
  · simp [skewPart, star_mul']
    ring
  constructor <;> simp [skewPart, star_mul'] <;> ring

/-- The spectral triangle identity after eliminating the third eigenframe
column by completeness.  The two retained columns `r,p` are orthonormal. -/
theorem twoOrthonormalColumns_spectralTriangle
    (b₀ b₁ b₂ : ℝ)
    (r₀ r₁ r₂ p₀ p₁ p₂ : ℂ)
    (hr : star r₀ * r₀ + star r₁ * r₁ + star r₂ * r₂ = 1)
    (hp : star p₀ * p₀ + star p₁ * p₁ + star p₂ * p₂ = 1)
    (hrp : star r₀ * p₀ + star r₁ * p₁ + star r₂ * p₂ = 0) :
    let x : ℂ := b₀ - b₂
    let y : ℂ := b₁ - b₂
    let B₀₁ := x * r₀ * star r₁ + y * p₀ * star p₁
    let B₁₂ := x * r₁ * star r₂ + y * p₁ * star p₂
    let B₂₀ := x * r₂ * star r₀ + y * p₂ * star p₀
    skewPart (B₀₁ * B₁₂ * B₂₀) =
      (JarlskogCommutatorIdentity.cyclicVandermonde b₀ b₁ b₂ : ℂ) *
        skewPart (r₀ * p₁ * star (p₀ * r₁)) := by
  dsimp
  let x₀ := star r₀ * p₀
  let x₁ := star r₁ * p₁
  let x₂ := star r₂ * p₂
  have hxzero : x₀ + x₁ + x₂ = 0 := by
    exact hrp
  have hx₂ : x₂ = -x₀ - x₁ := by
    linear_combination hxzero
  obtain ⟨h12, h20, h21, h02⟩ :=
    threeTermOrthogonality_quartetSkew x₀ x₁ x₂ hxzero
  have hJ : skewPart (x₁ * star x₀) =
      skewPart (r₀ * p₁ * star (p₀ * r₁)) := by
    simp [x₀, x₁, skewPart, star_mul']
    ring
  have hT :
      skewPart
        ((p₀ * star p₁) * (r₁ * star r₂) * (r₂ * star r₀) +
         (r₀ * star r₁) * (p₁ * star p₂) * (r₂ * star r₀) +
         (r₀ * star r₁) * (r₁ * star r₂) * (p₂ * star p₀)) =
        -skewPart (r₀ * p₁ * star (p₀ * r₁)) := by
    have hr' : r₀ * star r₀ + r₁ * star r₁ + r₂ * star r₂ = 1 := by
      simpa [mul_comm] using hr
    rw [← hJ]
    have hdecomp :
        (p₀ * star p₁) * (r₁ * star r₂) * (r₂ * star r₀) +
          (r₀ * star r₁) * (p₁ * star p₂) * (r₂ * star r₀) +
          (r₀ * star r₁) * (r₁ * star r₂) * (p₂ * star p₀) =
        (r₂ * star r₂) * star (x₁ * star x₀) +
          (r₀ * star r₀) * (x₁ * star x₂) +
          (r₁ * star r₁) * (x₂ * star x₀) := by
      simp [x₀, x₁, x₂, star_mul']
      ring
    rw [hdecomp, skewPart_add, skewPart_add]
    rw [skewPart_selfAdjoint_mul (r₂ * star r₂)
        (star (x₁ * star x₀)) (by simp [star_mul']; ring),
      skewPart_selfAdjoint_mul (r₀ * star r₀)
        (x₁ * star x₂) (by simp [star_mul']; ring),
      skewPart_selfAdjoint_mul (r₁ * star r₁)
        (x₂ * star x₀) (by simp [star_mul']; ring),
      skewPart_star, h12, h20, hJ]
    linear_combination
      (-skewPart (r₀ * p₁ * star (p₀ * r₁))) * hr'
  have hU :
      skewPart
        ((r₀ * star r₁) * (p₁ * star p₂) * (p₂ * star p₀) +
         (p₀ * star p₁) * (r₁ * star r₂) * (p₂ * star p₀) +
         (p₀ * star p₁) * (p₁ * star p₂) * (r₂ * star r₀)) =
        skewPart (r₀ * p₁ * star (p₀ * r₁)) := by
    have hp' : p₀ * star p₀ + p₁ * star p₁ + p₂ * star p₂ = 1 := by
      simpa [mul_comm] using hp
    rw [← hJ]
    have hdecomp :
        (r₀ * star r₁) * (p₁ * star p₂) * (p₂ * star p₀) +
          (p₀ * star p₁) * (r₁ * star r₂) * (p₂ * star p₀) +
          (p₀ * star p₁) * (p₁ * star p₂) * (r₂ * star r₀) =
        (p₂ * star p₂) * (x₁ * star x₀) +
          (p₀ * star p₀) * (x₂ * star x₁) +
          (p₁ * star p₁) * (x₀ * star x₂) := by
      simp [x₀, x₁, x₂, star_mul']
      ring
    rw [hdecomp, skewPart_add, skewPart_add]
    rw [skewPart_selfAdjoint_mul (p₂ * star p₂)
        (x₁ * star x₀) (by simp [star_mul']; ring),
      skewPart_selfAdjoint_mul (p₀ * star p₀)
        (x₂ * star x₁) (by simp [star_mul']; ring),
      skewPart_selfAdjoint_mul (p₁ * star p₁)
        (x₀ * star x₂) (by simp [star_mul']; ring),
      h21, h02, hJ]
    linear_combination
      (skewPart (r₀ * p₁ * star (p₀ * r₁))) * hp'
  rw [show (b₀ : ℂ) - b₂ = ((b₀ - b₂ : ℝ) : ℂ) by norm_num,
    show (b₁ : ℂ) - b₂ = ((b₁ - b₂ : ℝ) : ℂ) by norm_num]
  have hExpand :
      skewPart
        ((((b₀ - b₂ : ℝ) : ℂ) * r₀ * star r₁ +
            ((b₁ - b₂ : ℝ) : ℂ) * p₀ * star p₁) *
          (((b₀ - b₂ : ℝ) : ℂ) * r₁ * star r₂ +
            ((b₁ - b₂ : ℝ) : ℂ) * p₁ * star p₂) *
          (((b₀ - b₂ : ℝ) : ℂ) * r₂ * star r₀ +
            ((b₁ - b₂ : ℝ) : ℂ) * p₂ * star p₀)) =
        (((b₀ - b₂ : ℝ) : ℂ) ^ 2 * ((b₁ - b₂ : ℝ) : ℂ)) *
            skewPart
              ((p₀ * star p₁) * (r₁ * star r₂) * (r₂ * star r₀) +
               (r₀ * star r₁) * (p₁ * star p₂) * (r₂ * star r₀) +
               (r₀ * star r₁) * (r₁ * star r₂) * (p₂ * star p₀)) +
          (((b₀ - b₂ : ℝ) : ℂ) * ((b₁ - b₂ : ℝ) : ℂ) ^ 2) *
            skewPart
              ((r₀ * star r₁) * (p₁ * star p₂) * (p₂ * star p₀) +
               (p₀ * star p₁) * (r₁ * star r₂) * (p₂ * star p₀) +
               (p₀ * star p₁) * (p₁ * star p₂) * (r₂ * star r₀)) := by
    simp [skewPart, star_add, star_mul']
    ring
  calc
    _ = (((b₀ - b₂ : ℝ) : ℂ) ^ 2 * ((b₁ - b₂ : ℝ) : ℂ)) *
            skewPart
              ((p₀ * star p₁) * (r₁ * star r₂) * (r₂ * star r₀) +
               (r₀ * star r₁) * (p₁ * star p₂) * (r₂ * star r₀) +
               (r₀ * star r₁) * (r₁ * star r₂) * (p₂ * star p₀)) +
          (((b₀ - b₂ : ℝ) : ℂ) * ((b₁ - b₂ : ℝ) : ℂ) ^ 2) *
            skewPart
              ((r₀ * star r₁) * (p₁ * star p₂) * (p₂ * star p₀) +
               (p₀ * star p₁) * (r₁ * star r₂) * (p₂ * star p₀) +
               (p₀ * star p₁) * (p₁ * star p₂) * (r₂ * star r₀)) := hExpand
    _ = _ := by
      rw [hT, hU]
      simp [JarlskogCommutatorIdentity.cyclicVandermonde]
      ring

/-- The complete three-generation numerator identity in a relative unitary
eigenframe.  Both unitary equations are kept explicit: column orthonormality
drives the quartet identity and row completeness removes the third column from
the off-diagonal spectral entries. -/
theorem unitaryEigenframe_jarlskogNumerator
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℝ)
    (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hColumns : Vᴴ * V = 1)
    (hRows : V * Vᴴ = 1) :
    let A := JarlskogCommutatorIdentity.eigenvalueDiagonal a₀ a₁ a₂
    let B := spectralHermitianMatrix b₀ b₁ b₂ V
    Complex.im (((A * B - B * A) ^ 3).trace) =
      6 * JarlskogCommutatorIdentity.cyclicVandermonde a₀ a₁ a₂ *
        JarlskogCommutatorIdentity.cyclicVandermonde b₀ b₁ b₂ *
        Complex.im (V 0 0 * V 1 1 * star (V 0 1 * V 1 0)) := by
  dsimp
  have hr := congrFun (congrFun hColumns 0) 0
  have hp := congrFun (congrFun hColumns 1) 1
  have hrp := congrFun (congrFun hColumns 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at hr hp hrp
  have hrow01 := congrFun (congrFun hRows 0) 1
  have hrow12 := congrFun (congrFun hRows 1) 2
  have hrow20 := congrFun (congrFun hRows 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at hrow01 hrow12 hrow20
  simp only [starRingEnd_apply] at hr hp hrp hrow01 hrow12 hrow20
  have hB01 : spectralHermitianMatrix b₀ b₁ b₂ V 0 1 =
      ((b₀ - b₂ : ℝ) : ℂ) * V 0 0 * star (V 1 0) +
        ((b₁ - b₂ : ℝ) : ℂ) * V 0 1 * star (V 1 1) := by
    simp only [spectralHermitianMatrix]
    push_cast
    linear_combination ((b₂ : ℝ) : ℂ) * hrow01
  have hB12 : spectralHermitianMatrix b₀ b₁ b₂ V 1 2 =
      ((b₀ - b₂ : ℝ) : ℂ) * V 1 0 * star (V 2 0) +
        ((b₁ - b₂ : ℝ) : ℂ) * V 1 1 * star (V 2 1) := by
    simp only [spectralHermitianMatrix]
    push_cast
    linear_combination ((b₂ : ℝ) : ℂ) * hrow12
  have hB20 : spectralHermitianMatrix b₀ b₁ b₂ V 2 0 =
      ((b₀ - b₂ : ℝ) : ℂ) * V 2 0 * star (V 0 0) +
        ((b₁ - b₂ : ℝ) : ℂ) * V 2 1 * star (V 0 1) := by
    simp only [spectralHermitianMatrix]
    push_cast
    linear_combination ((b₂ : ℝ) : ℂ) * hrow20
  have htriangle := twoOrthonormalColumns_spectralTriangle
    b₀ b₁ b₂ (V 0 0) (V 1 0) (V 2 0)
      (V 0 1) (V 1 1) (V 2 1) hr hp hrp
  dsimp at htriangle
  have hskew :
      skewPart
        (spectralHermitianMatrix b₀ b₁ b₂ V 0 1 *
          spectralHermitianMatrix b₀ b₁ b₂ V 1 2 *
          spectralHermitianMatrix b₀ b₁ b₂ V 2 0) =
        (JarlskogCommutatorIdentity.cyclicVandermonde b₀ b₁ b₂ : ℂ) *
          skewPart (V 0 0 * V 1 1 * star (V 0 1 * V 1 0)) := by
    rw [hB01, hB12, hB20]
    simpa only [Complex.ofReal_sub, starRingEnd_apply] using htriangle
  have him := congrArg Complex.im hskew
  rw [imaginaryPart_skewPart,
    imaginaryPart_real_mul_skewPart] at him
  have htriangleIm :
      Complex.im
        (spectralHermitianMatrix b₀ b₁ b₂ V 0 1 *
          spectralHermitianMatrix b₀ b₁ b₂ V 1 2 *
          spectralHermitianMatrix b₀ b₁ b₂ V 2 0) =
        JarlskogCommutatorIdentity.cyclicVandermonde b₀ b₁ b₂ *
          Complex.im (V 0 0 * V 1 1 * star (V 0 1 * V 1 0)) := by
    linarith
  rw [JarlskogCommutatorIdentity.hermitian_diagonal_commutator_cube_imaginary_trace
    a₀ a₁ a₂ (spectralHermitianMatrix b₀ b₁ b₂ V)
    (spectralHermitianMatrix_isHermitian b₀ b₁ b₂ V)]
  rw [htriangleIm]
  simp only [starRingEnd_apply]
  ring

/-- The boxed Jarlskog quotient on the simple-spectrum branch. -/
theorem unitaryEigenframe_jarlskogFormula
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℝ)
    (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hColumns : Vᴴ * V = 1)
    (hRows : V * Vᴴ = 1)
    (hΔA : JarlskogCommutatorIdentity.cyclicVandermonde a₀ a₁ a₂ ≠ 0)
    (hΔB : JarlskogCommutatorIdentity.cyclicVandermonde b₀ b₁ b₂ ≠ 0) :
    Complex.im (V 0 0 * V 1 1 * star (V 0 1 * V 1 0)) =
      Complex.im
        ((((JarlskogCommutatorIdentity.eigenvalueDiagonal a₀ a₁ a₂) *
            spectralHermitianMatrix b₀ b₁ b₂ V -
          spectralHermitianMatrix b₀ b₁ b₂ V *
            JarlskogCommutatorIdentity.eigenvalueDiagonal a₀ a₁ a₂) ^ 3).trace) /
        (6 * JarlskogCommutatorIdentity.cyclicVandermonde a₀ a₁ a₂ *
          JarlskogCommutatorIdentity.cyclicVandermonde b₀ b₁ b₂) := by
  rw [unitaryEigenframe_jarlskogNumerator
    a₀ a₁ a₂ b₀ b₁ b₂ V hColumns hRows]
  field_simp [hΔA, hΔB]

end JarlskogSpectralTriangle
end NCG
