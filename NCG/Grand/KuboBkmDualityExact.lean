/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OmegaKernelExact

/-!
# Exact duality between the Kubo transform and the BKM metric

The Hessian of the log-partition function is naturally written in score
coordinates, whereas the Hessian of relative entropy is written in state
tangent coordinates.  The two coordinates are related by the Kubo transform
`Ω_σ`.  This file supplies the missing finite-dimensional change of
coordinates used in `cor:accepted-BKM-loss`.

In an eigenbasis of a faithful state `σ`, `Ω_σ` is entrywise multiplication by

`κ(a,b) = ∫₀¹ a^(1-s) b^s ds`.

The scalar identity `κ(a,b) * bkmKernel a b = 1` then proves exactly that the
inverse BKM quadratic form of `Ω_σ(S)` equals the Kubo quadratic form of `S`.
-/

open Matrix Unitary Finset MeasureTheory intervalIntegral
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ : Matrix n n ℂ}

/-- The scalar kernel of the Kubo transform. -/
noncomputable def kuboKernel (a b : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, a ^ (1 - s) * b ^ s

/-- The Kubo transform in spectral coordinates, reconstructed on the original
matrix carrier. -/
noncomputable def kuboTransformIn (hσ : σ.IsHermitian)
    (S : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => (kuboKernel (hσ.eigenvalues i) (hσ.eigenvalues j) : ℂ) *
    tangentIn hσ S i j

/-- The Kubo transform in spectral coordinates, reconstructed on the original
matrix carrier. -/
noncomputable def kuboTransform (hσ : σ.IsHermitian)
    (S : Matrix n n ℂ) : Matrix n n ℂ :=
  let U : Matrix n n ℂ := hσ.eigenvectorUnitary
  U * kuboTransformIn hσ S * star U

/-- The Kubo covariance quadratic form in score coordinates. -/
noncomputable def kuboForm (hσ : σ.IsHermitian)
    (S : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (tangentIn hσ S i j) *
    kuboKernel (hσ.eigenvalues i) (hσ.eigenvalues j)

theorem tangentIn_kuboTransform (hσ : σ.IsHermitian)
    (S : Matrix n n ℂ) (i j : n) :
    tangentIn hσ (kuboTransform hσ S) i j =
      (kuboKernel (hσ.eigenvalues i) (hσ.eigenvalues j) : ℂ) *
        tangentIn hσ S i j := by
  let U : Matrix n n ℂ := hσ.eigenvectorUnitary
  have hU₁ : star U * U = 1 := star_mul_coe hσ.eigenvectorUnitary
  have hU₂ : U * star U = 1 := coe_mul_star hσ.eigenvectorUnitary
  unfold tangentIn kuboTransform
  have hmat : star U * (U * kuboTransformIn hσ S * star U) * U =
      kuboTransformIn hσ S := by
    calc
      star U * (U * kuboTransformIn hσ S * star U) * U =
          (star U * U) * kuboTransformIn hσ S * (star U * U) := by
        simp only [Matrix.mul_assoc]
      _ = kuboTransformIn hσ S := by
        rw [hU₁, Matrix.one_mul, Matrix.mul_one]
  rw [hmat]
  rfl

/-- The inverse Kubo transform (the logarithmic derivative) in spectral
coordinates, reconstructed on the original matrix carrier. -/
noncomputable def inverseKuboTransformIn (hσ : σ.IsHermitian)
    (v : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => (bkmKernel (hσ.eigenvalues i) (hσ.eigenvalues j) : ℂ) *
    tangentIn hσ v i j

/-- The inverse Kubo transform on the original carrier. -/
noncomputable def inverseKuboTransform (hσ : σ.IsHermitian)
    (v : Matrix n n ℂ) : Matrix n n ℂ :=
  let U : Matrix n n ℂ := hσ.eigenvectorUnitary
  U * inverseKuboTransformIn hσ v * star U

theorem tangentIn_inverseKuboTransform (hσ : σ.IsHermitian)
    (v : Matrix n n ℂ) (i j : n) :
    tangentIn hσ (inverseKuboTransform hσ v) i j =
      (bkmKernel (hσ.eigenvalues i) (hσ.eigenvalues j) : ℂ) *
        tangentIn hσ v i j := by
  let U : Matrix n n ℂ := hσ.eigenvectorUnitary
  have hU : star U * U = 1 := star_mul_coe hσ.eigenvectorUnitary
  unfold tangentIn inverseKuboTransform
  have hmat : star U * (U * inverseKuboTransformIn hσ v * star U) * U =
      inverseKuboTransformIn hσ v := by
    calc
      star U * (U * inverseKuboTransformIn hσ v * star U) * U =
          (star U * U) * inverseKuboTransformIn hσ v * (star U * U) := by
        simp only [Matrix.mul_assoc]
      _ = inverseKuboTransformIn hσ v := by
        rw [hU, Matrix.one_mul, Matrix.mul_one]
  rw [hmat]
  rfl

/-- On a faithful state, the logarithmic divided-difference transform is a
right inverse of the Kubo transform. -/
theorem kuboTransform_inverseKuboTransform (hσ : σ.PosDef)
    (v : Matrix n n ℂ) :
    kuboTransform hσ.1 (inverseKuboTransform hσ.1 v) = v := by
  have ht : tangentIn hσ.1
      (kuboTransform hσ.1 (inverseKuboTransform hσ.1 v)) =
      tangentIn hσ.1 v := by
    ext i j
    rw [tangentIn_kuboTransform, tangentIn_inverseKuboTransform]
    have hrec := kubo_mul_bkmKernel (hσ.eigenvalues_pos i)
      (hσ.eigenvalues_pos j)
    change kuboKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) *
      bkmKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) = 1 at hrec
    have hrecC : (kuboKernel (hσ.1.eigenvalues i)
        (hσ.1.eigenvalues j) : ℂ) *
        (bkmKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) : ℂ) = 1 := by
      exact_mod_cast hrec
    rw [← mul_assoc, hrecC, one_mul]
  calc
    kuboTransform hσ.1 (inverseKuboTransform hσ.1 v) =
        (hσ.1.eigenvectorUnitary : Matrix n n ℂ) *
          tangentIn hσ.1
            (kuboTransform hσ.1 (inverseKuboTransform hσ.1 v)) *
          star (hσ.1.eigenvectorUnitary : Matrix n n ℂ) :=
      (tangentIn_reconstruct hσ.1 _).symm
    _ = (hσ.1.eigenvectorUnitary : Matrix n n ℂ) *
          tangentIn hσ.1 v *
          star (hσ.1.eigenvectorUnitary : Matrix n n ℂ) := by rw [ht]
    _ = v := tangentIn_reconstruct hσ.1 v

/-- On a faithful state, the logarithmic divided-difference transform is also
a left inverse of the Kubo transform. -/
theorem inverseKuboTransform_kuboTransform (hσ : σ.PosDef)
    (S : Matrix n n ℂ) :
    inverseKuboTransform hσ.1 (kuboTransform hσ.1 S) = S := by
  have ht : tangentIn hσ.1
      (inverseKuboTransform hσ.1 (kuboTransform hσ.1 S)) =
      tangentIn hσ.1 S := by
    ext i j
    rw [tangentIn_inverseKuboTransform, tangentIn_kuboTransform]
    have hrec := kubo_mul_bkmKernel (hσ.eigenvalues_pos i)
      (hσ.eigenvalues_pos j)
    change kuboKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) *
      bkmKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) = 1 at hrec
    have hrecC : (kuboKernel (hσ.1.eigenvalues i)
        (hσ.1.eigenvalues j) : ℂ) *
        (bkmKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) : ℂ) = 1 := by
      exact_mod_cast hrec
    calc
      (bkmKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) : ℂ) *
            ((kuboKernel (hσ.1.eigenvalues i)
              (hσ.1.eigenvalues j) : ℂ) * tangentIn hσ.1 S i j) =
          ((kuboKernel (hσ.1.eigenvalues i)
              (hσ.1.eigenvalues j) : ℂ) *
            (bkmKernel (hσ.1.eigenvalues i)
              (hσ.1.eigenvalues j) : ℂ)) *
            tangentIn hσ.1 S i j := by ring
      _ = tangentIn hσ.1 S i j := by rw [hrecC, one_mul]
  calc
    inverseKuboTransform hσ.1 (kuboTransform hσ.1 S) =
        (hσ.1.eigenvectorUnitary : Matrix n n ℂ) *
          tangentIn hσ.1
            (inverseKuboTransform hσ.1 (kuboTransform hσ.1 S)) *
          star (hσ.1.eigenvectorUnitary : Matrix n n ℂ) :=
      (tangentIn_reconstruct hσ.1 _).symm
    _ = (hσ.1.eigenvectorUnitary : Matrix n n ℂ) *
          tangentIn hσ.1 S *
          star (hσ.1.eigenvectorUnitary : Matrix n n ℂ) := by rw [ht]
    _ = S := tangentIn_reconstruct hσ.1 S

/-- Applying the Kubo transform and then the inverse BKM metric recovers the
Kubo covariance form.  This is the exact score/tangent-coordinate bridge in
the local data-processing Hessian. -/
theorem bkmForm_kuboTransform (hσ : σ.PosDef) (S : Matrix n n ℂ) :
    bkmForm hσ.1 (kuboTransform hσ.1 S) = kuboForm hσ.1 S := by
  unfold bkmForm kuboForm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tangentIn_kuboTransform]
  rw [Complex.normSq_mul]
  have hki : 0 < hσ.1.eigenvalues i := hσ.eigenvalues_pos i
  have hkj : 0 < hσ.1.eigenvalues j := hσ.eigenvalues_pos j
  have hrec : kuboKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) *
      bkmKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) = 1 := by
    exact kubo_mul_bkmKernel hki hkj
  have hprod : 0 < kuboKernel (hσ.1.eigenvalues i)
      (hσ.1.eigenvalues j) *
        bkmKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) := by
    rw [hrec]
    exact one_pos
  have hk0 : 0 < kuboKernel (hσ.1.eigenvalues i)
      (hσ.1.eigenvalues j) := by
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.1
    · exact (not_lt_of_ge (le_of_lt (bkmKernel_pos hki hkj)) h.2).elim
  have hnorm : Complex.normSq
      (kuboKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) : ℂ) =
      kuboKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) ^ 2 := by
    simp [Complex.normSq, sq]
  rw [hnorm]
  rw [pow_two]
  calc
    kuboKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) *
          kuboKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) *
          Complex.normSq (tangentIn hσ.1 S i j) *
          bkmKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) =
        Complex.normSq (tangentIn hσ.1 S i j) *
          (kuboKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) *
            bkmKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j)) *
          kuboKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) := by ring
    _ = Complex.normSq (tangentIn hσ.1 S i j) *
          kuboKernel (hσ.1.eigenvalues i) (hσ.1.eigenvalues j) := by
      rw [hrec]
      ring

/-! ### Data processing in score coordinates -/

variable {m κ : Type*} [Fintype m] [DecidableEq m] [Fintype κ]

/-- If source and output scores represent channel-related state tangents through
their respective Kubo transforms, the BKM loss is exactly the difference of
the two score-coordinate Kubo forms. -/
theorem bkmLoss_eq_kuboForm_loss
    (K : κ → Matrix m n ℂ)
    (hσ : σ.PosDef) (hbσ : (Petz.kraus K σ).PosDef)
    (S : Matrix n n ℂ) (T : Matrix m m ℂ)
    (htransport : Petz.kraus K (kuboTransform hσ.1 S) =
      kuboTransform hbσ.1 T) :
    bkmForm hσ.1 (kuboTransform hσ.1 S) -
        bkmForm hbσ.1 (Petz.kraus K (kuboTransform hσ.1 S)) =
      kuboForm hσ.1 S - kuboForm hbσ.1 T := by
  rw [bkmForm_kuboTransform hσ S, htransport,
    bkmForm_kuboTransform hbσ T]

/-- **Kubo-coordinate local data processing.**  Compatible score tangents
contract under every finite Kraus CPTP channel. -/
theorem kuboForm_loss_nonneg
    [Nonempty κ]
    (K : κ → Matrix m n ℂ) (hK : ∑ a, (K a)ᴴ * K a = 1)
    (hσ : σ.PosDef) (hbσ : (Petz.kraus K σ).PosDef)
    (S : Matrix n n ℂ) (T : Matrix m m ℂ)
    (htransport : Petz.kraus K (kuboTransform hσ.1 S) =
      kuboTransform hbσ.1 T) :
    0 ≤ kuboForm hσ.1 S - kuboForm hbσ.1 T := by
  classical
  rw [← bkmLoss_eq_kuboForm_loss K hσ hbσ S T htransport]
  exact Petz.bkmLoss_nonneg K hK hσ hbσ (kuboTransform hσ.1 S)

end QRE
end NCG
