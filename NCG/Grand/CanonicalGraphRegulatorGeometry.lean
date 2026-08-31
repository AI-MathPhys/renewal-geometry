/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTGraphRegulator
import NCG.Grand.CorrectedDualMeasureCriterion
import NCG.Grand.GeometricMeanExact
import NCG.Grand.RelEntropyInvarianceExact
import NCG.Grand.BkmScalingExact
import NCG.Grand.LoewnerSqrtExact
import NCG.Grand.GTAtlasCompleteness
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Finite geometry of the canonical graph regulator

This file supplies the projector, covariance, weighted Berry/moment, and
determinant-character layer of `thm:SMST-graph-regulator`, complementing the
block-square and gap theorem in `SMSTGraphRegulator`.
-/

open Matrix
open scoped ComplexOrder TensorProduct

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace NCG

/-! ### The normalized massive sign from finite functional calculus -/

/-- Real spectral functional calculus is covariant under unitary conjugation.
The proof uses one polynomial interpolating the scalar function simultaneously
on the spectra before and after conjugation. -/
theorem matFun_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (u : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ)
    (hA : A.IsHermitian)
    (hA' : ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ)).IsHermitian)
    (f : ℝ → ℝ) :
    QRE.matFun hA' f =
      (u : Matrix n n ℂ) * QRE.matFun hA f * star (u : Matrix n n ℂ) := by
  obtain ⟨P, hP⟩ := QRE.exists_interpolating' f
    ((Finset.image hA.eigenvalues Finset.univ) ∪
      Finset.image hA'.eigenvalues Finset.univ)
  have hleft : QRE.matFun hA' f =
      Polynomial.aeval ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ)) P :=
    QRE.matFun_eq_aeval hA' f P fun i => hP _
      (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hright : QRE.matFun hA f = Polynomial.aeval A P :=
    QRE.matFun_eq_aeval hA f P fun i => hP _
      (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  rw [hleft, hright, QRE.aeval_unitary_conj]

/-- The spectral calculus depends on the Hermitian matrix, not on the chosen
proof that it is Hermitian. -/
theorem matFun_eq_of_matrix_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hAB : A = B) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (f : ℝ → ℝ) :
    QRE.matFun hA f = QRE.matFun hB f := by
  subst B
  rfl

/-- A rectangular intertwiner transports polynomial evaluation. -/
theorem aeval_intertwine_rectangular {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (A : Matrix E E ℂ) (B : Matrix F F ℂ) (D : Matrix F E ℂ)
    (hint : B * D = D * A) (P : Polynomial ℝ) :
    Polynomial.aeval B P * D = D * Polynomial.aeval A P := by
  have hpow : ∀ k : ℕ, B ^ k * D = D * A ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
    | succ k ih =>
        rw [pow_succ, pow_succ, Matrix.mul_assoc, hint,
          ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, hpow k]

/-- A rectangular intertwiner transports every real spectral function of two
finite Hermitian matrices. -/
theorem matFun_intertwine_rectangular {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (A : Matrix E E ℂ) (B : Matrix F F ℂ) (D : Matrix F E ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hint : B * D = D * A) (f : ℝ → ℝ) :
    QRE.matFun hB f * D = D * QRE.matFun hA f := by
  obtain ⟨P, hP⟩ := QRE.exists_interpolating' f
    ((Finset.image hA.eigenvalues Finset.univ) ∪
      Finset.image hB.eigenvalues Finset.univ)
  have hAeval : QRE.matFun hA f = Polynomial.aeval A P :=
    QRE.matFun_eq_aeval hA f P fun i => hP _
      (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hBeval : QRE.matFun hB f = Polynomial.aeval B P :=
    QRE.matFun_eq_aeval hB f P fun i => hP _
      (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  rw [hAeval, hBeval]
  exact aeval_intertwine_rectangular A B D hint P

/-- Polynomial evaluation preserves a two-by-two block diagonal matrix. -/
theorem aeval_fromBlocks_diagonal {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (A : Matrix E E ℂ) (B : Matrix F F ℂ) (P : Polynomial ℝ) :
    Polynomial.aeval (Matrix.fromBlocks A 0 0 B) P =
      Matrix.fromBlocks (Polynomial.aeval A P) 0 0
        (Polynomial.aeval B P) := by
  have hpow : ∀ k : ℕ,
      (Matrix.fromBlocks A 0 0 B : Matrix (E ⊕ F) (E ⊕ F) ℂ) ^ k =
        Matrix.fromBlocks (A ^ k) 0 0 (B ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, pow_zero, ← Matrix.fromBlocks_one]
    | succ k ih =>
        rw [pow_succ, pow_succ, pow_succ, ih,
          Matrix.fromBlocks_multiply]
        simp
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Polynomial.aeval_eq_sum_range]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [hpow, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, smul_zero, Finset.sum_const_zero]

/-- Real spectral functional calculus preserves a Hermitian block diagonal
matrix. -/
theorem matFun_fromBlocks_diagonal {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (A : Matrix E E ℂ) (B : Matrix F F ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    let hAB : (Matrix.fromBlocks A 0 0 B :
      Matrix (E ⊕ F) (E ⊕ F) ℂ).IsHermitian := by
        exact hA.fromBlocks (by simp) hB
    QRE.matFun hAB f =
      Matrix.fromBlocks (QRE.matFun hA f) 0 0 (QRE.matFun hB f) := by
  dsimp only
  let hAB : (Matrix.fromBlocks A 0 0 B :
      Matrix (E ⊕ F) (E ⊕ F) ℂ).IsHermitian := by
    exact hA.fromBlocks (by simp) hB
  obtain ⟨P, hP⟩ := QRE.exists_interpolating' f
    ((Finset.image hA.eigenvalues Finset.univ) ∪
      (Finset.image hB.eigenvalues Finset.univ ∪
        Finset.image hAB.eigenvalues Finset.univ))
  have heA : QRE.matFun hA f = Polynomial.aeval A P :=
    QRE.matFun_eq_aeval hA f P fun i => hP _
      (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have heB : QRE.matFun hB f = Polynomial.aeval B P :=
    QRE.matFun_eq_aeval hB f P fun i => hP _
      (Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  have heAB : QRE.matFun hAB f =
      Polynomial.aeval (Matrix.fromBlocks A 0 0 B) P :=
    QRE.matFun_eq_aeval hAB f P fun i => hP _
      (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  rw [heAB, heA, heB]
  exact aeval_fromBlocks_diagonal A B P

/-- The normalized sign of a Hermitian matrix whose square is positive
definite.  This is the finite-dimensional functional-calculus expression
`H (H²)⁻¹ᐟ²` used by the graph regulator. -/
noncomputable def normalizedHermitianSign {n : Type*}
    [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hHsq : (H * H).PosDef) : Matrix n n ℂ :=
  H * Petz.invSqrtMat hHsq.1

/-- A Hermitian matrix commutes with the inverse square root of its square. -/
theorem commute_invSqrt_square {n : Type*}
    [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hHsq : (H * H).PosDef) :
    Commute H (Petz.invSqrtMat hHsq.1) := by
  have hcomm : Commute H (H * H) := by
    change H * (H * H) = (H * H) * H
    simp only [Matrix.mul_assoc]
  exact QRE.commute_matFun_right hHsq.1 _ hcomm

/-- The functional-calculus normalized sign is Hermitian. -/
theorem normalizedHermitianSign_isHermitian {n : Type*}
    [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hH : Hᴴ = H) (hHsq : (H * H).PosDef) :
    (normalizedHermitianSign H hHsq)ᴴ =
      normalizedHermitianSign H hHsq := by
  unfold normalizedHermitianSign
  rw [Matrix.conjTranspose_mul, Petz.invSqrtMat_isHermitian hHsq.1, hH]
  exact (commute_invSqrt_square H hHsq).eq.symm

set_option maxHeartbeats 1600000 in
-- Spectral interpolation in `commute_invSqrt_square` is elaboration-heavy.
/-- The functional-calculus normalized sign is an involution. -/
theorem normalizedHermitianSign_sq {n : Type*}
    [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hHsq : (H * H).PosDef) :
    normalizedHermitianSign H hHsq * normalizedHermitianSign H hHsq = 1 := by
  unfold normalizedHermitianSign
  let R := Petz.invSqrtMat hHsq.1
  have hcomm : H * R = R * H := (commute_invSqrt_square H hHsq).eq
  have hcommSq : (H * H) * R = R * (H * H) := by
    calc
      (H * H) * R = H * (H * R) := by simp only [Matrix.mul_assoc]
      _ = H * (R * H) := by rw [hcomm]
      _ = (H * R) * H := by simp only [Matrix.mul_assoc]
      _ = (R * H) * H := by rw [hcomm]
      _ = R * (H * H) := by simp only [Matrix.mul_assoc]
  calc
    (H * R) * (H * R) = H * (R * H) * R := by
      simp only [Matrix.mul_assoc]
    _ = H * (H * R) * R := by rw [← hcomm]
    _ = (H * H) * R * R := by simp only [Matrix.mul_assoc]
    _ = R * (H * H) * R := by rw [hcommSq]
    _ = 1 := Petz.invSqrt_conj_self hHsq

/-- The normalized Hermitian sign is covariant under unitary conjugation. -/
theorem normalizedHermitianSign_unitary_conj {n : Type*}
    [Fintype n] [DecidableEq n] (u : unitary (Matrix n n ℂ))
    (H : Matrix n n ℂ) (hHsq : (H * H).PosDef)
    (hHsq' : (((u : Matrix n n ℂ) * H * star (u : Matrix n n ℂ)) *
      ((u : Matrix n n ℂ) * H * star (u : Matrix n n ℂ))).PosDef) :
    normalizedHermitianSign
        ((u : Matrix n n ℂ) * H * star (u : Matrix n n ℂ)) hHsq' =
      (u : Matrix n n ℂ) * normalizedHermitianSign H hHsq *
        star (u : Matrix n n ℂ) := by
  let U : Matrix n n ℂ := u
  let R : Matrix n n ℂ := Petz.invSqrtMat hHsq.1
  have hsquare : (U * H * star U) * (U * H * star U) =
      U * (H * H) * star U := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U (H * star U), QRE.star_mul_coe,
      Matrix.one_mul]
  have hConj : (U * (H * H) * star U).IsHermitian := by
    rw [← hsquare]
    exact hHsq'.1
  have hR : Petz.invSqrtMat hHsq'.1 = U * R * star U := by
    unfold Petz.invSqrtMat
    calc
      QRE.matFun hHsq'.1 (fun x => (Real.sqrt x)⁻¹) =
          QRE.matFun hConj (fun x => (Real.sqrt x)⁻¹) :=
        matFun_eq_of_matrix_eq hsquare hHsq'.1 hConj _
      _ = U * R * star U :=
        matFun_unitary_conj u (H * H) hHsq.1 hConj _
  unfold normalizedHermitianSign
  change (U * H * star U) * Petz.invSqrtMat hHsq'.1 =
    U * (H * R) * star U
  rw [hR]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U (R * star U), QRE.star_mul_coe,
    Matrix.one_mul]

/-- The normalized sign is independent of replacing its matrix by an equal
matrix (and hence of the transported positivity proof). -/
theorem normalizedHermitianSign_eq_of_matrix_eq {n : Type*}
    [Fintype n] [DecidableEq n] {H K : Matrix n n ℂ}
    (hHK : H = K) (hH : (H * H).PosDef) (hK : (K * K).PosDef) :
    normalizedHermitianSign H hH = normalizedHermitianSign K hK := by
  subst K
  rfl

/-- The positive-mass chiral graph Hamiltonian. -/
def positiveGraphHamiltonian {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) : Matrix (E ⊕ F) (E ⊕ F) ℂ :=
  Matrix.fromBlocks ((m : ℂ) • 1) Dᴴ D (-(m : ℂ) • 1)

/-- The massive graph Hamiltonian is Hermitian. -/
theorem positiveGraphHamiltonian_isHermitian {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) :
    (positiveGraphHamiltonian D m)ᴴ = positiveGraphHamiltonian D m := by
  simp [positiveGraphHamiltonian, Matrix.fromBlocks_conjTranspose]

/-- Positive mass makes the square of the graph Hamiltonian positive
definite; this is the exact finite-dimensional spectral-gap input. -/
theorem positiveGraphHamiltonian_sq_posDef {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    (positiveGraphHamiltonian D m * positiveGraphHamiltonian D m).PosDef := by
  rw [positiveGraphHamiltonian, regulator_square]
  have heq :
      Matrix.fromBlocks
          (Dᴴ * D + (((m : ℂ) ^ 2)) • 1) 0 0
          (D * Dᴴ + (((m : ℂ) ^ 2)) • 1) =
        (((m ^ 2 : ℝ) : ℂ) • (1 : Matrix (E ⊕ F) (E ⊕ F) ℂ)) +
          Matrix.fromBlocks (Dᴴ * D) 0 0 (D * Dᴴ) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add]
    congr 1 <;> simp [pow_two, add_comm]
  rw [heq]
  exact (Matrix.PosDef.one.smul (sq_pos_of_pos hm)).add_posSemidef
    (regulator_gap D)

/-- The massive graph Hamiltonian has an unconditionally constructed
Hermitian involutive sign, hence no assumed functional-calculus output is
needed for its negative spectral projector. -/
theorem positiveGraphHamiltonian_sign {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    let hsq := positiveGraphHamiltonian_sq_posDef D m hm
    let S := normalizedHermitianSign (positiveGraphHamiltonian D m) hsq
    Sᴴ = S ∧ S * S = 1 := by
  dsimp only
  exact ⟨normalizedHermitianSign_isHermitian _
      (positiveGraphHamiltonian_isHermitian D m) _,
    normalizedHermitianSign_sq _ _⟩

/-- The block-diagonal unitary induced by independent source and target gauge
transformations. -/
noncomputable def graphBlockUnitary {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (uE : unitary (Matrix E E ℂ)) (uF : unitary (Matrix F F ℂ)) :
    unitary (Matrix (E ⊕ F) (E ⊕ F) ℂ) := by
  refine ⟨Matrix.fromBlocks (uE : Matrix E E ℂ) 0 0
    (uF : Matrix F F ℂ), ?_⟩
  constructor
  · change (Matrix.fromBlocks (uE : Matrix E E ℂ) 0 0
        (uF : Matrix F F ℂ))ᴴ *
        Matrix.fromBlocks (uE : Matrix E E ℂ) 0 0
          (uF : Matrix F F ℂ) = 1
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    exact ⟨by simpa [← Matrix.star_eq_conjTranspose] using uE.prop.1,
      by simp, by simp,
      by simpa [← Matrix.star_eq_conjTranspose] using uF.prop.1⟩
  · change Matrix.fromBlocks (uE : Matrix E E ℂ) 0 0
        (uF : Matrix F F ℂ) *
        (Matrix.fromBlocks (uE : Matrix E E ℂ) 0 0
          (uF : Matrix F F ℂ))ᴴ = 1
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    exact ⟨by simpa [← Matrix.star_eq_conjTranspose] using uE.prop.2,
      by simp, by simp,
      by simpa [← Matrix.star_eq_conjTranspose] using uF.prop.2⟩

/-- The massive chiral graph Hamiltonian is covariant under independent
unitary changes of source and target frames. -/
theorem positiveGraphHamiltonian_gauge_covariant {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (uE : unitary (Matrix E E ℂ)) (uF : unitary (Matrix F F ℂ))
    (D : Matrix F E ℂ) (m : ℝ) :
    positiveGraphHamiltonian
        ((uF : Matrix F F ℂ) * D * (uE : Matrix E E ℂ)ᴴ) m =
      (graphBlockUnitary uE uF : Matrix (E ⊕ F) (E ⊕ F) ℂ) *
        positiveGraphHamiltonian D m *
        star (graphBlockUnitary uE uF : Matrix (E ⊕ F) (E ⊕ F) ℂ) := by
  change Matrix.fromBlocks ((m : ℂ) • 1)
      (((uF : Matrix F F ℂ) * D * (uE : Matrix E E ℂ)ᴴ)ᴴ)
      ((uF : Matrix F F ℂ) * D * (uE : Matrix E E ℂ)ᴴ)
      (-(m : ℂ) • 1) = _
  change _ = Matrix.fromBlocks (uE : Matrix E E ℂ) 0 0
      (uF : Matrix F F ℂ) * positiveGraphHamiltonian D m *
        (Matrix.fromBlocks (uE : Matrix E E ℂ) 0 0
          (uF : Matrix F F ℂ))ᴴ
  rw [positiveGraphHamiltonian, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, positiveGraphHamiltonian,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  rw [← Matrix.star_eq_conjTranspose, QRE.coe_mul_star,
    ← Matrix.star_eq_conjTranspose, QRE.coe_mul_star]
  simp only [smul_zero, add_zero, zero_add, Matrix.mul_assoc]

/-- The functional-calculus sign of the massive graph Hamiltonian is gauge
covariant, with both signs constructed from the corresponding squared
Hamiltonians. -/
theorem positiveGraphHamiltonian_sign_gauge_covariant {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (uE : unitary (Matrix E E ℂ)) (uF : unitary (Matrix F F ℂ))
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    let D' := (uF : Matrix F F ℂ) * D * (uE : Matrix E E ℂ)ᴴ
    let U := (graphBlockUnitary uE uF : Matrix (E ⊕ F) (E ⊕ F) ℂ)
    normalizedHermitianSign (positiveGraphHamiltonian D' m)
        (positiveGraphHamiltonian_sq_posDef D' m hm) =
      U * normalizedHermitianSign (positiveGraphHamiltonian D m)
          (positiveGraphHamiltonian_sq_posDef D m hm) * Uᴴ := by
  dsimp only
  let D' := (uF : Matrix F F ℂ) * D * (uE : Matrix E E ℂ)ᴴ
  let u := graphBlockUnitary uE uF
  let U : Matrix (E ⊕ F) (E ⊕ F) ℂ := u
  let H := positiveGraphHamiltonian D m
  let H' := positiveGraphHamiltonian D' m
  have hHcov : H' = U * H * star U := by
    exact positiveGraphHamiltonian_gauge_covariant uE uF D m
  let hsq := positiveGraphHamiltonian_sq_posDef D m hm
  let hsq' := positiveGraphHamiltonian_sq_posDef D' m hm
  have hsqConj : ((U * H * star U) * (U * H * star U)).PosDef := by
    rw [← hHcov]
    exact hsq'
  calc
    normalizedHermitianSign H' hsq' =
        normalizedHermitianSign (U * H * star U) hsqConj :=
      normalizedHermitianSign_eq_of_matrix_eq hHcov hsq' hsqConj
    _ = U * normalizedHermitianSign H hsq * star U :=
      normalizedHermitianSign_unitary_conj u H hsq hsqConj
    _ = U * normalizedHermitianSign H hsq * Uᴴ := by
      rw [Matrix.star_eq_conjTranspose]

/-- Negative spectral projector written in terms of a normalized Hermitian
sign operator. -/
noncomputable def graphNegativeProjector {n : Type*} [Fintype n] [DecidableEq n]
    (signH : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (1 - signH)

/-- The functional-calculus sign involution gives an orthogonal projector. -/
theorem graphNegativeProjector_orthogonal {n : Type*}
    [Fintype n] [DecidableEq n] (signH : Matrix n n ℂ)
    (hself : signHᴴ = signH) (hsq : signH * signH = 1) :
    (graphNegativeProjector signH)ᴴ = graphNegativeProjector signH
      ∧ graphNegativeProjector signH * graphNegativeProjector signH
        = graphNegativeProjector signH := by
  constructor
  · simp [graphNegativeProjector, Matrix.conjTranspose_sub, hself]
  · simp only [graphNegativeProjector, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hsq]
    module

/-- The negative projector of the actual positive-mass graph Hamiltonian is
orthogonal, with the normalized sign constructed by finite spectral calculus. -/
theorem positiveGraphNegativeProjector_orthogonal {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    let hsq := positiveGraphHamiltonian_sq_posDef D m hm
    let S := normalizedHermitianSign (positiveGraphHamiltonian D m) hsq
    let P := graphNegativeProjector S
    Pᴴ = P ∧ P * P = P := by
  dsimp only
  apply graphNegativeProjector_orthogonal
  · exact normalizedHermitianSign_isHermitian _
      (positiveGraphHamiltonian_isHermitian D m) _
  · exact normalizedHermitianSign_sq _ _

/-- Gauge covariance of the negative projector follows from covariance of the
normalized sign and unitarity of the finite gauge transformation. -/
theorem graphNegativeProjector_covariant {n : Type*}
    [Fintype n] [DecidableEq n] (U signH : Matrix n n ℂ)
    (_hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) :
    graphNegativeProjector (U * signH * Uᴴ)
      = U * graphNegativeProjector signH * Uᴴ := by
  simp only [graphNegativeProjector, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hUU]

/-- The negative spectral projector of the actual massive chiral Hamiltonian
is covariant under independent source and target gauge unitaries. -/
theorem positiveGraphNegativeProjector_gauge_covariant {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (uE : unitary (Matrix E E ℂ)) (uF : unitary (Matrix F F ℂ))
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    let D' := (uF : Matrix F F ℂ) * D * (uE : Matrix E E ℂ)ᴴ
    let U := (graphBlockUnitary uE uF : Matrix (E ⊕ F) (E ⊕ F) ℂ)
    graphNegativeProjector
        (normalizedHermitianSign (positiveGraphHamiltonian D' m)
          (positiveGraphHamiltonian_sq_posDef D' m hm)) =
      U * graphNegativeProjector
          (normalizedHermitianSign (positiveGraphHamiltonian D m)
            (positiveGraphHamiltonian_sq_posDef D m hm)) * Uᴴ := by
  dsimp only
  let u := graphBlockUnitary uE uF
  let U : Matrix (E ⊕ F) (E ⊕ F) ℂ := u
  let S := normalizedHermitianSign (positiveGraphHamiltonian D m)
    (positiveGraphHamiltonian_sq_posDef D m hm)
  have hsign := positiveGraphHamiltonian_sign_gauge_covariant
    uE uF D m hm
  change graphNegativeProjector _ = U * graphNegativeProjector S * Uᴴ
  rw [hsign]
  apply graphNegativeProjector_covariant
  · simpa [U, u, ← Matrix.star_eq_conjTranspose] using u.prop.1
  · simpa [U, u, ← Matrix.star_eq_conjTranspose] using u.prop.2

/-! ### Exact source/target Berry weights -/

/-- The positive source mass Gram `D*D + m²`. -/
def graphSourceMassGram {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E]
    (D : Matrix F E ℂ) (m : ℝ) : Matrix E E ℂ :=
  Dᴴ * D + (((m ^ 2 : ℝ) : ℂ)) • 1

/-- The positive target mass Gram `DD* + m²`. -/
def graphTargetMassGram {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) : Matrix F F ℂ :=
  D * Dᴴ + (((m ^ 2 : ℝ) : ℂ)) • 1

/-- Positive mass makes the source mass Gram positive definite. -/
theorem graphSourceMassGram_posDef {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    (graphSourceMassGram D m).PosDef := by
  rw [graphSourceMassGram, add_comm]
  exact (Matrix.PosDef.one.smul (sq_pos_of_pos hm)).add_posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self D)

/-- Positive mass makes the target mass Gram positive definite. -/
theorem graphTargetMassGram_posDef {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    (graphTargetMassGram D m).PosDef := by
  rw [graphTargetMassGram, add_comm]
  exact (Matrix.PosDef.one.smul (sq_pos_of_pos hm)).add_posSemidef
    (Matrix.posSemidef_self_mul_conjTranspose D)

/-- The square of the positive graph Hamiltonian is the block diagonal pair
of source and target mass Grams. -/
theorem positiveGraphHamiltonian_sq_eq_massGrams {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) :
    positiveGraphHamiltonian D m * positiveGraphHamiltonian D m =
      Matrix.fromBlocks (graphSourceMassGram D m) 0 0
        (graphTargetMassGram D m) := by
  simpa [positiveGraphHamiltonian, graphSourceMassGram,
    graphTargetMassGram, pow_two] using regulator_square D (m : ℂ)

/-- The inverse square root of the squared graph Hamiltonian is block
diagonal with the source and target inverse mass radii. -/
theorem positiveGraphHamiltonian_invSqrt_sq_blocks {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    Petz.invSqrtMat (positiveGraphHamiltonian_sq_posDef D m hm).1 =
      Matrix.fromBlocks
        (Petz.invSqrtMat (graphSourceMassGram_posDef D m hm).1) 0 0
        (Petz.invSqrtMat (graphTargetMassGram_posDef D m hm).1) := by
  let hblock : (Matrix.fromBlocks (graphSourceMassGram D m) 0 0
      (graphTargetMassGram D m) :
      Matrix (E ⊕ F) (E ⊕ F) ℂ).IsHermitian :=
    (graphSourceMassGram_posDef D m hm).1.fromBlocks (by simp)
      (graphTargetMassGram_posDef D m hm).1
  unfold Petz.invSqrtMat
  calc
    QRE.matFun (positiveGraphHamiltonian_sq_posDef D m hm).1
          (fun x => (Real.sqrt x)⁻¹) =
        QRE.matFun hblock (fun x => (Real.sqrt x)⁻¹) :=
      matFun_eq_of_matrix_eq
        (positiveGraphHamiltonian_sq_eq_massGrams D m)
        (positiveGraphHamiltonian_sq_posDef D m hm).1 hblock _
    _ = Matrix.fromBlocks
          (QRE.matFun (graphSourceMassGram_posDef D m hm).1
            (fun x => (Real.sqrt x)⁻¹)) 0 0
          (QRE.matFun (graphTargetMassGram_posDef D m hm).1
            (fun x => (Real.sqrt x)⁻¹)) :=
      matFun_fromBlocks_diagonal _ _
        (graphSourceMassGram_posDef D m hm).1
        (graphTargetMassGram_posDef D m hm).1 _

/-- Explicit four-block formula for the normalized positive-mass graph sign. -/
theorem positiveGraphHamiltonian_sign_blocks {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    normalizedHermitianSign (positiveGraphHamiltonian D m)
        (positiveGraphHamiltonian_sq_posDef D m hm) =
      Matrix.fromBlocks
        ((m : ℂ) • Petz.invSqrtMat
          (graphSourceMassGram_posDef D m hm).1)
        (Dᴴ * Petz.invSqrtMat
          (graphTargetMassGram_posDef D m hm).1)
        (D * Petz.invSqrtMat
          (graphSourceMassGram_posDef D m hm).1)
        (-(m : ℂ) • Petz.invSqrtMat
          (graphTargetMassGram_posDef D m hm).1) := by
  unfold normalizedHermitianSign
  rw [positiveGraphHamiltonian_invSqrt_sq_blocks]
  rw [positiveGraphHamiltonian, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one]
  congr 1 <;> module

/-- Inverse square roots of positive matrices are positive semidefinite. -/
theorem invSqrtMat_posSemidef {n : Type*}
    [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosDef) :
    (Petz.invSqrtMat hA.1).PosSemidef := by
  unfold Petz.invSqrtMat
  exact QRE.matFun_posSemidef hA.1 _ fun i =>
    inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- The target diagonal block controlling the positive-Hamiltonian negative
graph frame is positive definite. -/
theorem positiveGraphTargetFrameBlock_posDef {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    ((1 : Matrix F F ℂ) + m • Petz.invSqrtMat
      (graphTargetMassGram_posDef D m hm).1).PosDef := by
  exact Matrix.PosDef.one.add_posSemidef
    ((invSqrtMat_posSemidef
      (graphTargetMassGram_posDef D m hm)).smul hm.le)

/-- The corresponding source diagonal block is positive definite. -/
theorem positiveGraphSourceFrameBlock_posDef {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    ((1 : Matrix E E ℂ) + m • Petz.invSqrtMat
      (graphSourceMassGram_posDef D m hm).1).PosDef := by
  exact Matrix.PosDef.one.add_posSemidef
    ((invSqrtMat_posSemidef
      (graphSourceMassGram_posDef D m hm)).smul hm.le)

/-- Explicit block formula for the negative spectral projector of `H_m^+`. -/
theorem positiveGraphNegativeProjector_blocks {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    graphNegativeProjector
        (normalizedHermitianSign (positiveGraphHamiltonian D m)
          (positiveGraphHamiltonian_sq_posDef D m hm)) =
      Matrix.fromBlocks
        ((2 : ℂ)⁻¹ • (1 - (m : ℂ) • Petz.invSqrtMat
          (graphSourceMassGram_posDef D m hm).1))
        ((2 : ℂ)⁻¹ • (-(Dᴴ * Petz.invSqrtMat
          (graphTargetMassGram_posDef D m hm).1)))
        ((2 : ℂ)⁻¹ • (-(D * Petz.invSqrtMat
          (graphSourceMassGram_posDef D m hm).1)))
        ((2 : ℂ)⁻¹ • (1 + (m : ℂ) • Petz.invSqrtMat
          (graphTargetMassGram_posDef D m hm).1)) := by
  rw [positiveGraphHamiltonian_sign_blocks D m hm]
  unfold graphNegativeProjector
  rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
  congr 1 <;> module

/-- The negative projector of `H_m^+` has rank exactly `dim F`; its
complement has rank exactly `dim E`. -/
theorem positiveGraphNegativeProjector_rank {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    let P := graphNegativeProjector
      (normalizedHermitianSign (positiveGraphHamiltonian D m)
        (positiveGraphHamiltonian_sq_posDef D m hm))
    P.rank = Fintype.card F ∧ (1 - P).rank = Fintype.card E := by
  dsimp only
  let P := graphNegativeProjector
    (normalizedHermitianSign (positiveGraphHamiltonian D m)
      (positiveGraphHamiltonian_sq_posDef D m hm))
  change P.rank = Fintype.card F ∧ (1 - P).rank = Fintype.card E
  let RE := Petz.invSqrtMat (graphSourceMassGram_posDef D m hm).1
  let RF := Petz.invSqrtMat (graphTargetMassGram_posDef D m hm).1
  have hscalar : IsUnit ((2 : ℂ)⁻¹) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  have hFbase : ((1 : Matrix F F ℂ) + (m : ℂ) • RF).PosDef := by
    simpa [RF, Complex.real_smul] using
      (positiveGraphTargetFrameBlock_posDef D m hm)
  have hEbase : ((1 : Matrix E E ℂ) + (m : ℂ) • RE).PosDef := by
    simpa [RE, Complex.real_smul] using
      (positiveGraphSourceFrameBlock_posDef D m hm)
  have hFunit : IsUnit (((2 : ℂ)⁻¹) •
      ((1 : Matrix F F ℂ) + (m : ℂ) • RF)) := by
    simpa only [Units.smul_isUnit hscalar] using
      hFbase.isUnit.smul hscalar.unit
  have hEunit : IsUnit (((2 : ℂ)⁻¹) •
      ((1 : Matrix E E ℂ) + (m : ℂ) • RE)) := by
    simpa only [Units.smul_isUnit hscalar] using
      hEbase.isUnit.smul hscalar.unit
  have hsubF : P.submatrix Sum.inr Sum.inr =
      ((2 : ℂ)⁻¹) • ((1 : Matrix F F ℂ) + (m : ℂ) • RF) := by
    dsimp only [P]
    rw [positiveGraphNegativeProjector_blocks D m hm]
    rfl
  have hsubE : (1 - P).submatrix Sum.inl Sum.inl =
      ((2 : ℂ)⁻¹) • ((1 : Matrix E E ℂ) + (m : ℂ) • RE) := by
    dsimp only [P]
    rw [positiveGraphNegativeProjector_blocks D m hm]
    rw [show (1 : Matrix (E ⊕ F) (E ⊕ F) ℂ) =
      Matrix.fromBlocks (1 : Matrix E E ℂ) 0 0
        (1 : Matrix F F ℂ) from Matrix.fromBlocks_one.symm]
    rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    change (1 : Matrix E E ℂ) -
        (2 : ℂ)⁻¹ • (1 - (m : ℂ) • RE) =
      (2 : ℂ)⁻¹ • (1 + (m : ℂ) • RE)
    norm_num
    module
  have hFle : Fintype.card F ≤ P.rank := by
    have hle := Matrix.rank_submatrix_le P Sum.inr Sum.inr
    rw [hsubF, Matrix.rank_of_isUnit _ hFunit] at hle
    exact hle
  have hEle : Fintype.card E ≤ (1 - P).rank := by
    have hle := Matrix.rank_submatrix_le (1 - P) Sum.inl Sum.inl
    rw [hsubE, Matrix.rank_of_isUnit _ hEunit] at hle
    exact hle
  have hPP : P * P = P := by
    simpa only [P] using (positiveGraphNegativeProjector_orthogonal D m hm).2
  have hPcomp : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hPcomp
  rw [Fintype.card_sum] at hsum
  omega

/-- The actual negative projector of the positive graph Hamiltonian. -/
noncomputable def positiveGraphProjector {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    Matrix (E ⊕ F) (E ⊕ F) ℂ :=
  graphNegativeProjector
    (normalizedHermitianSign (positiveGraphHamiltonian D m)
      (positiveGraphHamiltonian_sq_posDef D m hm))

/-- Canonical inclusion of the target summand. -/
def graphTargetEmbedding {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq F] :
    Matrix (E ⊕ F) F ℂ :=
  Matrix.fromRows 0 1

/-- The canonical target graph frame, obtained by applying the negative
projector to the target summand. -/
noncomputable def positiveGraphTargetFrame {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    Matrix (E ⊕ F) F ℂ :=
  Matrix.fromRows
    ((2 : ℂ)⁻¹ • (-(Dᴴ * Petz.invSqrtMat
      (graphTargetMassGram_posDef D m hm).1)))
    ((2 : ℂ)⁻¹ • (1 + (m : ℂ) • Petz.invSqrtMat
      (graphTargetMassGram_posDef D m hm).1))

/-- The lower block of the target graph frame is the invertible lower-right
projector block. -/
theorem positiveGraphTargetFrame_bottom {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    (positiveGraphTargetFrame D m hm).submatrix Sum.inr id =
      (2 : ℂ)⁻¹ • (1 + (m : ℂ) • Petz.invSqrtMat
        (graphTargetMassGram_posDef D m hm).1) := by
  rfl

/-- Applying the projector to a vector included in the target summand produces
the canonical target-frame vector. -/
theorem positiveGraphProjector_mulVec_targetEmbedding {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) (x : F → ℂ) :
    positiveGraphProjector D m hm *ᵥ (graphTargetEmbedding *ᵥ x) =
      positiveGraphTargetFrame D m hm *ᵥ x := by
  unfold positiveGraphProjector graphTargetEmbedding
  rw [positiveGraphNegativeProjector_blocks D m hm]
  unfold positiveGraphTargetFrame
  simp [Matrix.fromBlocks_mulVec, Matrix.fromRows_mulVec, Matrix.mulVec]

/-- The canonical target graph frame has independent columns. -/
theorem positiveGraphTargetFrame_injective {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    Function.Injective (positiveGraphTargetFrame D m hm).mulVec := by
  let RF := Petz.invSqrtMat (graphTargetMassGram_posDef D m hm).1
  have hscalar : IsUnit ((2 : ℂ)⁻¹) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  have hbase : ((1 : Matrix F F ℂ) + (m : ℂ) • RF).PosDef := by
    simpa [RF, Complex.real_smul] using
      (positiveGraphTargetFrameBlock_posDef D m hm)
  have hunit : IsUnit (((2 : ℂ)⁻¹) •
      ((1 : Matrix F F ℂ) + (m : ℂ) • RF)) := by
    simpa only [Units.smul_isUnit hscalar] using
      hbase.isUnit.smul hscalar.unit
  intro x y hxy
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
  rw [← positiveGraphTargetFrame_bottom D m hm]
  funext i
  have hi := congrFun hxy (Sum.inr i)
  simpa [Matrix.mulVec, Matrix.submatrix] using hi

/-- The range of the canonical target graph frame is exactly the negative
spectral subspace of `H_m^+`. -/
theorem positiveGraphTargetFrame_range {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    LinearMap.range (positiveGraphTargetFrame D m hm).mulVecLin =
      LinearMap.range (positiveGraphProjector D m hm).mulVecLin := by
  let P := positiveGraphProjector D m hm
  let T := positiveGraphTargetFrame D m hm
  let J : Matrix (E ⊕ F) F ℂ := graphTargetEmbedding
  have hle : LinearMap.range T.mulVecLin ≤ LinearMap.range P.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    refine ⟨J *ᵥ x, ?_⟩
    exact positiveGraphProjector_mulVec_targetEmbedding D m hm x
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hTinj : Function.Injective T.mulVecLin := by
    exact positiveGraphTargetFrame_injective D m hm
  have hTdim : Module.finrank ℂ (LinearMap.range T.mulVecLin) =
      Fintype.card F := by
    rw [← (LinearEquiv.ofInjective T.mulVecLin hTinj).finrank_eq,
      Module.finrank_pi]
  have hPdim : Module.finrank ℂ (LinearMap.range P.mulVecLin) =
      Fintype.card F := by
    have hr := (positiveGraphNegativeProjector_rank D m hm).1
    change P.rank = Fintype.card F at hr
    exact hr
  rw [hTdim, hPdim]

/-- Canonical frame equivalence from `F` onto the negative graph subspace of
the positive Hamiltonian. -/
noncomputable def positiveGraphRangeEquiv {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    (F → ℂ) ≃ₗ[ℂ]
      LinearMap.range (positiveGraphProjector D m hm).mulVecLin :=
  LinearEquiv.ofInjective (positiveGraphTargetFrame D m hm).mulVecLin
      (positiveGraphTargetFrame_injective D m hm) ≪≫ₗ
    LinearEquiv.ofEq _ _ (positiveGraphTargetFrame_range D m hm)

/-! ### The negative Hamiltonian and its canonical source frame -/

/-- The negative massive graph Hamiltonian `H_m^-`. -/
def negativeGraphHamiltonian {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) : Matrix (E ⊕ F) (E ⊕ F) ℂ :=
  Matrix.fromBlocks (-(m : ℂ) • 1) Dᴴ D ((m : ℂ) • 1)

/-- `H_m^-` is the negative of the positive Hamiltonian built from `-D`. -/
theorem negativeGraphHamiltonian_eq_neg_positive {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) :
    negativeGraphHamiltonian D m = -positiveGraphHamiltonian (-D) m := by
  unfold negativeGraphHamiltonian positiveGraphHamiltonian
  rw [Matrix.fromBlocks_neg]
  congr 1 <;> simp

/-- Negating a matrix negates its normalized sign; the squared matrix and its
inverse square root are unchanged. -/
theorem normalizedHermitianSign_neg {n : Type*}
    [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (hHsq : (H * H).PosDef) (hNegSq : ((-H) * (-H)).PosDef) :
    normalizedHermitianSign (-H) hNegSq =
      -normalizedHermitianSign H hHsq := by
  have hsquare : (-H) * (-H) = H * H := by simp
  have hR : Petz.invSqrtMat hNegSq.1 = Petz.invSqrtMat hHsq.1 := by
    unfold Petz.invSqrtMat
    exact matFun_eq_of_matrix_eq hsquare hNegSq.1 hHsq.1 _
  unfold normalizedHermitianSign
  rw [hR]
  exact Matrix.neg_mul H (Petz.invSqrtMat hHsq.1)

/-- Positive mass also gaps the negative graph Hamiltonian. -/
theorem negativeGraphHamiltonian_sq_posDef {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    (negativeGraphHamiltonian D m * negativeGraphHamiltonian D m).PosDef := by
  rw [negativeGraphHamiltonian_eq_neg_positive]
  simpa using positiveGraphHamiltonian_sq_posDef (-D) m hm

/-- The two diagonal mass Grams are also the exact square of `H_m^-`. -/
theorem negativeGraphHamiltonian_sq_eq_massGrams {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) :
    negativeGraphHamiltonian D m * negativeGraphHamiltonian D m =
      Matrix.fromBlocks (graphSourceMassGram D m) 0 0
        (graphTargetMassGram D m) := by
  rw [negativeGraphHamiltonian_eq_neg_positive]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  simpa [graphSourceMassGram, graphTargetMassGram] using
    positiveGraphHamiltonian_sq_eq_massGrams (-D) m

/-- The negative graph Hamiltonian is Hermitian. -/
theorem negativeGraphHamiltonian_isHermitian {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) :
    (negativeGraphHamiltonian D m)ᴴ = negativeGraphHamiltonian D m := by
  simp [negativeGraphHamiltonian, Matrix.fromBlocks_conjTranspose]

/-- The negative spectral projector of `H_m^-`, represented as the positive
spectral projector of `H_m^+(-D)`. -/
noncomputable def negativeGraphProjector {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    Matrix (E ⊕ F) (E ⊕ F) ℂ :=
  1 - positiveGraphProjector (-D) m hm

/-- The complement model is exactly the negative spectral projector obtained
from the normalized sign of `H_m^-`. -/
theorem negativeGraphProjector_eq_actual {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    negativeGraphProjector D m hm =
      graphNegativeProjector
        (normalizedHermitianSign (negativeGraphHamiltonian D m)
          (negativeGraphHamiltonian_sq_posDef D m hm)) := by
  let H := positiveGraphHamiltonian (-D) m
  let hHsq := positiveGraphHamiltonian_sq_posDef (-D) m hm
  have hNegSq : ((-H) * (-H)).PosDef := by simpa [H] using hHsq
  have hsign : normalizedHermitianSign (negativeGraphHamiltonian D m)
      (negativeGraphHamiltonian_sq_posDef D m hm) =
        -normalizedHermitianSign H hHsq := by
    calc
      normalizedHermitianSign (negativeGraphHamiltonian D m)
          (negativeGraphHamiltonian_sq_posDef D m hm) =
          normalizedHermitianSign (-H) hNegSq :=
        normalizedHermitianSign_eq_of_matrix_eq
          (negativeGraphHamiltonian_eq_neg_positive D m)
          (negativeGraphHamiltonian_sq_posDef D m hm) hNegSq
      _ = -normalizedHermitianSign H hHsq :=
        normalizedHermitianSign_neg H hHsq hNegSq
  unfold negativeGraphProjector positiveGraphProjector
  rw [hsign]
  unfold graphNegativeProjector
  module

/-- The actual negative projector of `H_m^-` is orthogonal. -/
theorem negativeGraphProjector_orthogonal {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    (negativeGraphProjector D m hm)ᴴ = negativeGraphProjector D m hm ∧
      negativeGraphProjector D m hm * negativeGraphProjector D m hm =
        negativeGraphProjector D m hm := by
  rw [negativeGraphProjector_eq_actual D m hm]
  apply graphNegativeProjector_orthogonal
  · exact normalizedHermitianSign_isHermitian _
      (negativeGraphHamiltonian_isHermitian D m) _
  · exact normalizedHermitianSign_sq _ _

/-- Gauge covariance of the negative-Hamiltonian projector. -/
theorem negativeGraphProjector_gauge_covariant {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (uE : unitary (Matrix E E ℂ)) (uF : unitary (Matrix F F ℂ))
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    let D' := (uF : Matrix F F ℂ) * D * (uE : Matrix E E ℂ)ᴴ
    let U := (graphBlockUnitary uE uF : Matrix (E ⊕ F) (E ⊕ F) ℂ)
    negativeGraphProjector D' m hm =
      U * negativeGraphProjector D m hm * Uᴴ := by
  dsimp only
  let U := (graphBlockUnitary uE uF : Matrix (E ⊕ F) (E ⊕ F) ℂ)
  have hneg : -((uF : Matrix F F ℂ) * D * (uE : Matrix E E ℂ)ᴴ) =
      (uF : Matrix F F ℂ) * (-D) * (uE : Matrix E E ℂ)ᴴ := by
    simp only [Matrix.mul_neg, Matrix.neg_mul]
  have hcov := positiveGraphNegativeProjector_gauge_covariant
    uE uF (-D) m hm
  change positiveGraphProjector
      ((uF : Matrix F F ℂ) * (-D) * (uE : Matrix E E ℂ)ᴴ) m hm =
    U * positiveGraphProjector (-D) m hm * Uᴴ at hcov
  unfold negativeGraphProjector
  rw [hneg, hcov]
  change 1 - U * positiveGraphProjector (-D) m hm * Uᴴ =
    U * (1 - positiveGraphProjector (-D) m hm) * Uᴴ
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  have hUU : U * Uᴴ = 1 := by
    simpa [U, ← Matrix.star_eq_conjTranspose] using
      (graphBlockUnitary uE uF).prop.2
  rw [hUU]

/-- Explicit blocks of the negative-Hamiltonian projector. -/
theorem negativeGraphProjector_blocks {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    negativeGraphProjector D m hm =
      Matrix.fromBlocks
        ((2 : ℂ)⁻¹ • (1 + (m : ℂ) • Petz.invSqrtMat
          (graphSourceMassGram_posDef (-D) m hm).1))
        ((2 : ℂ)⁻¹ • ((-D)ᴴ * Petz.invSqrtMat
          (graphTargetMassGram_posDef (-D) m hm).1))
        ((2 : ℂ)⁻¹ • ((-D) * Petz.invSqrtMat
          (graphSourceMassGram_posDef (-D) m hm).1))
        ((2 : ℂ)⁻¹ • (1 - (m : ℂ) • Petz.invSqrtMat
          (graphTargetMassGram_posDef (-D) m hm).1)) := by
  unfold negativeGraphProjector positiveGraphProjector
  rw [positiveGraphNegativeProjector_blocks (-D) m hm]
  rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_add]
  congr 1 <;> module

/-- Canonical inclusion of the source summand. -/
def graphSourceEmbedding {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] :
    Matrix (E ⊕ F) E ℂ :=
  Matrix.fromRows 1 0

/-- Canonical source frame for the negative Hamiltonian. -/
noncomputable def negativeGraphSourceFrame {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    Matrix (E ⊕ F) E ℂ :=
  Matrix.fromRows
    ((2 : ℂ)⁻¹ • (1 + (m : ℂ) • Petz.invSqrtMat
      (graphSourceMassGram_posDef (-D) m hm).1))
    ((2 : ℂ)⁻¹ • ((-D) * Petz.invSqrtMat
      (graphSourceMassGram_posDef (-D) m hm).1))

/-- The upper source-frame block is positive definite and hence invertible. -/
theorem negativeGraphSourceFrame_top {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    (negativeGraphSourceFrame D m hm).submatrix Sum.inl id =
      (2 : ℂ)⁻¹ • (1 + (m : ℂ) • Petz.invSqrtMat
        (graphSourceMassGram_posDef (-D) m hm).1) := by
  rfl

/-- Projecting an included source vector gives its canonical source-frame
vector. -/
theorem negativeGraphProjector_mulVec_sourceEmbedding {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) (x : E → ℂ) :
    negativeGraphProjector D m hm *ᵥ (graphSourceEmbedding *ᵥ x) =
      negativeGraphSourceFrame D m hm *ᵥ x := by
  rw [negativeGraphProjector_blocks D m hm]
  unfold graphSourceEmbedding negativeGraphSourceFrame
  simp [Matrix.fromBlocks_mulVec, Matrix.fromRows_mulVec]

/-- The canonical negative-Hamiltonian source frame has independent columns. -/
theorem negativeGraphSourceFrame_injective {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    Function.Injective (negativeGraphSourceFrame D m hm).mulVec := by
  let RE := Petz.invSqrtMat (graphSourceMassGram_posDef (-D) m hm).1
  have hscalar : IsUnit ((2 : ℂ)⁻¹) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  have hbase : ((1 : Matrix E E ℂ) + (m : ℂ) • RE).PosDef := by
    simpa [RE, Complex.real_smul] using
      (positiveGraphSourceFrameBlock_posDef (-D) m hm)
  have hunit : IsUnit (((2 : ℂ)⁻¹) •
      ((1 : Matrix E E ℂ) + (m : ℂ) • RE)) := by
    simpa only [Units.smul_isUnit hscalar] using
      hbase.isUnit.smul hscalar.unit
  intro x y hxy
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
  rw [← negativeGraphSourceFrame_top D m hm]
  funext i
  have hi := congrFun hxy (Sum.inl i)
  simpa [Matrix.mulVec, Matrix.submatrix] using hi

/-- The canonical source-frame range is exactly the negative spectral subspace
of `H_m^-`. -/
theorem negativeGraphSourceFrame_range {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    LinearMap.range (negativeGraphSourceFrame D m hm).mulVecLin =
      LinearMap.range (negativeGraphProjector D m hm).mulVecLin := by
  let P := negativeGraphProjector D m hm
  let T := negativeGraphSourceFrame D m hm
  let J : Matrix (E ⊕ F) E ℂ := graphSourceEmbedding
  have hle : LinearMap.range T.mulVecLin ≤ LinearMap.range P.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    refine ⟨J *ᵥ x, ?_⟩
    exact negativeGraphProjector_mulVec_sourceEmbedding D m hm x
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hTinj : Function.Injective T.mulVecLin := by
    exact negativeGraphSourceFrame_injective D m hm
  have hTdim : Module.finrank ℂ (LinearMap.range T.mulVecLin) =
      Fintype.card E := by
    rw [← (LinearEquiv.ofInjective T.mulVecLin hTinj).finrank_eq,
      Module.finrank_pi]
  have hPdim : Module.finrank ℂ (LinearMap.range P.mulVecLin) =
      Fintype.card E := by
    have hr := (positiveGraphNegativeProjector_rank (-D) m hm).2
    change P.rank = Fintype.card E at hr
    exact hr
  rw [hTdim, hPdim]

/-- Canonical frame equivalence from `E` onto the negative spectral subspace
of the negative Hamiltonian. -/
noncomputable def negativeGraphRangeEquiv {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    (E → ℂ) ≃ₗ[ℂ]
      LinearMap.range (negativeGraphProjector D m hm).mulVecLin :=
  LinearEquiv.ofInjective (negativeGraphSourceFrame D m hm).mulVecLin
      (negativeGraphSourceFrame_injective D m hm) ≪≫ₗ
    LinearEquiv.ofEq _ _ (negativeGraphSourceFrame_range D m hm)

/-! ### Canonical relative determinant line -/

/-- The underlying vector space of a complex exterior power.  Naming the
coercion avoids parser ambiguity when exterior powers occur inside tensor
products. -/
abbrev complexExteriorPower (k : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] :=
  ↥(ExteriorAlgebra.exteriorPower ℂ k V)

/-- A linear equivalence induces a linear equivalence on every exterior
power. -/
noncomputable def exteriorPowerLinearEquiv
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℂ V] [Module ℂ W] (k : ℕ) (e : V ≃ₗ[ℂ] W) :
    complexExteriorPower k V ≃ₗ[ℂ] complexExteriorPower k W :=
  LinearEquiv.ofBijective (exteriorPower.map k e.toLinearMap)
    ⟨exteriorPower.map_injective_field e.injective,
      exteriorPower.map_surjective e.surjective⟩

/-- The positive projector range has the expected target dimension. -/
theorem positiveGraphProjector_finrank {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    Module.finrank ℂ
        (LinearMap.range (positiveGraphProjector D m hm).mulVecLin) =
      Fintype.card F := by
  exact (positiveGraphNegativeProjector_rank D m hm).1

/-- The negative projector range has the expected source dimension. -/
theorem negativeGraphProjector_finrank {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    Module.finrank ℂ
        (LinearMap.range (negativeGraphProjector D m hm).mulVecLin) =
      Fintype.card E := by
  have hr := (positiveGraphNegativeProjector_rank (-D) m hm).2
  change (negativeGraphProjector D m hm).rank = Fintype.card E
  exact hr

/-- The relative determinant line of the two massive graph projectors, with
the exterior degrees written using the proved source/target dimensions. -/
noncomputable abbrev canonicalGraphRelativeLine {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :=
  (complexExteriorPower (Fintype.card F)
      (LinearMap.range (positiveGraphProjector D m hm).mulVecLin)) ⊗[ℂ]
    (Module.Dual ℂ
      (complexExteriorPower (Fintype.card E)
        (LinearMap.range (negativeGraphProjector D m hm).mulVecLin)))

/-- The fixed-fibre chiral determinant line `det(E)^* ⊗ det(F)`. -/
abbrev canonicalChiralDeterminantLine (E F : Type*)
    [Fintype E] [Fintype F] :=
  (Module.Dual ℂ (complexExteriorPower (Fintype.card E) (E → ℂ))) ⊗[ℂ]
    (complexExteriorPower (Fintype.card F) (F → ℂ))

/-- Canonical massive graph identification
`det Ran(P_m^+) ⊗ det Ran(P_m^-)^* ≃ det(E)^* ⊗ det(F)`. -/
noncomputable def canonicalGraphRelativeLineEquiv {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    canonicalGraphRelativeLine D m hm ≃ₗ[ℂ]
      canonicalChiralDeterminantLine E F := by
  let ePlus := exteriorPowerLinearEquiv (Fintype.card F)
    (positiveGraphRangeEquiv D m hm).symm
  let eMinus := exteriorPowerLinearEquiv (Fintype.card E)
    (negativeGraphRangeEquiv D m hm).symm
  exact TensorProduct.congr ePlus eMinus.dualMap.symm ≪≫ₗ
    TensorProduct.comm ℂ _ _

/-- The source and target mass Grams intertwine through `D`. -/
theorem graphMassGram_intertwine {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) :
    graphTargetMassGram D m * D = D * graphSourceMassGram D m := by
  unfold graphTargetMassGram graphSourceMassGram
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc]

/-- The scalar Berry weight `(√x)⁻¹(√x+m)⁻¹`. -/
noncomputable def graphBerryWeightFunction (m : ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt x)⁻¹ * (Real.sqrt x + m)⁻¹

/-- Functional-calculus Berry weight of a positive mass Gram. -/
noncomputable def graphBerryWeight {n : Type*}
    [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosDef) (m : ℝ) : Matrix n n ℂ :=
  QRE.matFun hA.1 (graphBerryWeightFunction m)

/-- The source and target Berry weights satisfy the exact rectangular
push-through relation. -/
theorem graphBerryWeight_intertwine {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    graphBerryWeight (graphTargetMassGram_posDef D m hm) m * D =
      D * graphBerryWeight (graphSourceMassGram_posDef D m hm) m := by
  unfold graphBerryWeight
  exact matFun_intertwine_rectangular
    (graphSourceMassGram D m) (graphTargetMassGram D m) D
    (graphSourceMassGram_posDef D m hm).1
    (graphTargetMassGram_posDef D m hm).1
    (graphMassGram_intertwine D m) _

/-- Scalar identity behind the graph Berry moment formula. -/
theorem graphBerryWeightFunction_mul_sub_sq (x m : ℝ)
    (hx : 0 < x) (hm : 0 < m) :
    graphBerryWeightFunction m x * (x - m ^ 2) =
      1 - m * (Real.sqrt x)⁻¹ := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsum : Real.sqrt x + m ≠ 0 := (add_pos hs hm).ne'
  have hsne : Real.sqrt x ≠ 0 := hs.ne'
  unfold graphBerryWeightFunction
  field_simp [hsne, hsum]
  nlinarith [Real.sq_sqrt hx.le]

/-- Multiplying the Berry weight by the massless part of a positive mass
Gram gives `I - m A⁻¹ᐟ²`. -/
theorem graphBerryWeight_mul_masslessPart {n : Type*}
    [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosDef) (m : ℝ) (hm : 0 < m) :
    graphBerryWeight hA m *
        (A - (((m ^ 2 : ℝ) : ℂ)) • 1) =
      1 - (m : ℂ) • Petz.invSqrtMat hA.1 := by
  have hconst : QRE.matFun hA.1 (fun _ : ℝ => m ^ 2) =
      (((m ^ 2 : ℝ) : ℂ)) • (1 : Matrix n n ℂ) := by
    calc
      QRE.matFun hA.1 (fun _ : ℝ => m ^ 2) =
          QRE.matFun hA.1 (fun x : ℝ => (m ^ 2) * (fun _ : ℝ => 1) x) := by
            congr 1
            funext x
            simp
      _ = (m ^ 2 : ℝ) • QRE.matFun hA.1 (fun _ : ℝ => 1) :=
        QRE.matFun_real_smul hA.1 (m ^ 2) _
      _ = (((m ^ 2 : ℝ) : ℂ)) • (1 : Matrix n n ℂ) := by
        rw [Petz.matFun_one]
        rfl
  have hmassless : A - (((m ^ 2 : ℝ) : ℂ)) • 1 =
      QRE.matFun hA.1 (fun x : ℝ => x - m ^ 2) := by
    calc
      A - (((m ^ 2 : ℝ) : ℂ)) • 1 =
          QRE.matFun hA.1 id - QRE.matFun hA.1 (fun _ : ℝ => m ^ 2) := by
            rw [Petz.matFun_id, hconst]
      _ = QRE.matFun hA.1 (fun x : ℝ => id x - m ^ 2) :=
        QRE.matFun_sub hA.1 _ _
      _ = QRE.matFun hA.1 (fun x : ℝ => x - m ^ 2) := by rfl
  rw [hmassless]
  unfold graphBerryWeight
  calc
    QRE.matFun hA.1 (graphBerryWeightFunction m) *
          QRE.matFun hA.1 (fun x : ℝ => x - m ^ 2) =
        QRE.matFun hA.1
          (fun x : ℝ => graphBerryWeightFunction m x * (x - m ^ 2)) :=
      QRE.matFun_mul hA.1 _ _
    _ = QRE.matFun hA.1 (fun x : ℝ => 1 - m * (Real.sqrt x)⁻¹) :=
      Petz.matFun_congr hA.1 _ _ fun i =>
        graphBerryWeightFunction_mul_sub_sq _ m (hA.eigenvalues_pos i) hm
    _ = QRE.matFun hA.1 (fun _ : ℝ => 1) -
          QRE.matFun hA.1 (fun x : ℝ => m * (Real.sqrt x)⁻¹) := by
      rw [QRE.matFun_sub]
    _ = 1 - (m : ℂ) • Petz.invSqrtMat hA.1 := by
      rw [Petz.matFun_one]
      unfold Petz.invSqrtMat
      rw [QRE.matFun_real_smul]
      rfl

/-- Source-side exact Berry identity. -/
theorem graphSourceBerryWeight_identity {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    graphBerryWeight (graphSourceMassGram_posDef D m hm) m * Dᴴ * D =
      1 - (m : ℂ) • Petz.invSqrtMat
        (graphSourceMassGram_posDef D m hm).1 := by
  have h := graphBerryWeight_mul_masslessPart
    (graphSourceMassGram_posDef D m hm) m hm
  simpa [graphSourceMassGram, Matrix.mul_assoc] using h

/-- Target-side exact Berry identity. -/
theorem graphTargetBerryWeight_identity {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    graphBerryWeight (graphTargetMassGram_posDef D m hm) m * D * Dᴴ =
      1 - (m : ℂ) • Petz.invSqrtMat
        (graphTargetMassGram_posDef D m hm).1 := by
  have h := graphBerryWeight_mul_masslessPart
    (graphTargetMassGram_posDef D m hm) m hm
  simpa [graphTargetMassGram, Matrix.mul_assoc] using h

/-- The source Berry weight sandwiched by `D,D*` is the target moment
operator. -/
theorem graphSourceBerryWeight_sandwich {E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    D * graphBerryWeight (graphSourceMassGram_posDef D m hm) m * Dᴴ =
      1 - (m : ℂ) • Petz.invSqrtMat
        (graphTargetMassGram_posDef D m hm).1 := by
  calc
    D * graphBerryWeight (graphSourceMassGram_posDef D m hm) m * Dᴴ =
        (graphBerryWeight (graphTargetMassGram_posDef D m hm) m * D) * Dᴴ := by
      rw [graphBerryWeight_intertwine D m hm]
    _ = graphBerryWeight (graphTargetMassGram_posDef D m hm) m * D * Dᴴ := by
      simp only [Matrix.mul_assoc]
    _ = 1 - (m : ℂ) • Petz.invSqrtMat
          (graphTargetMassGram_posDef D m hm).1 :=
      graphTargetBerryWeight_identity D m hm

/-- The weighted Berry connection in canonical graph frames. -/
def canonicalGraphBerryConnection {E F : Type*}
    [Fintype E] [Fintype F]
    (WE : Matrix E E ℂ) (D dD : Matrix F E ℂ) : ℝ :=
  -(Matrix.trace (WE * Dᴴ * dD)).im

/-- The vertical moment in the trace-real convention. -/
def canonicalGraphVerticalMoment {E F : Type*}
    [Fintype E] [Fintype F]
    (AE : Matrix E E ℂ) (AF : Matrix F F ℂ)
    (XE : Matrix E E ℂ) (XF : Matrix F F ℂ) : ℝ :=
  -(Matrix.trace (AF * XF)).im + (Matrix.trace (AE * XE)).im

/-- Substitution of the gauge tangent `dD = XF D - D XE` into the Berry
connection gives the spectrally weighted vertical moment.  The two push-through
identities are exactly `D f(D*D) D* = I-m R_F^{-1}` and
`f(D*D)D*D = I-m R_E^{-1}` from finite functional calculus. -/
theorem canonicalGraphBerry_vertical
    {E F : Type*} [Fintype E] [Fintype F]
    (WE AE : Matrix E E ℂ) (AF : Matrix F F ℂ)
    (D : Matrix F E ℂ) (XE : Matrix E E ℂ) (XF : Matrix F F ℂ)
    (hF : D * WE * Dᴴ = AF) (hE : WE * Dᴴ * D = AE) :
    canonicalGraphBerryConnection WE D (XF * D - D * XE)
      = canonicalGraphVerticalMoment AE AF XE XF := by
  unfold canonicalGraphBerryConnection canonicalGraphVerticalMoment
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_im]
  have hleft : Matrix.trace (WE * Dᴴ * (XF * D)) =
      Matrix.trace (AF * XF) := by
    calc
      Matrix.trace (WE * Dᴴ * (XF * D))
          = Matrix.trace ((WE * Dᴴ * XF) * D) := by
              simp only [Matrix.mul_assoc]
      _ = Matrix.trace (D * (WE * Dᴴ * XF)) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace (D * WE * Dᴴ * XF) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (AF * XF) := by rw [hF]
  have hright : Matrix.trace (WE * Dᴴ * (D * XE)) =
      Matrix.trace (AE * XE) := by
    simp only [← Matrix.mul_assoc]
    rw [hE]
  rw [hleft, hright]
  ring

/-- Exact vertical Berry formula for the actual positive-mass graph weight;
all source/target moment identities are derived from finite spectral calculus. -/
theorem canonicalGraphBerry_vertical_exact
    {E F : Type*} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m)
    (XE : Matrix E E ℂ) (XF : Matrix F F ℂ) :
    canonicalGraphBerryConnection
        (graphBerryWeight (graphSourceMassGram_posDef D m hm) m)
        D (XF * D - D * XE) =
      canonicalGraphVerticalMoment
        (1 - (m : ℂ) • Petz.invSqrtMat
          (graphSourceMassGram_posDef D m hm).1)
        (1 - (m : ℂ) • Petz.invSqrtMat
          (graphTargetMassGram_posDef D m hm).1)
        XE XF := by
  apply canonicalGraphBerry_vertical
  · exact graphSourceBerryWeight_sandwich D m hm
  · exact graphSourceBerryWeight_identity D m hm

/-- Gauge cocycle of the graph determinant line. -/
noncomputable def graphDeterminantCharacter
    {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (UE : Matrix E E ℂ) (UF : Matrix F F ℂ) : ℂ :=
  UF.det * UE.det⁻¹

/-- The graph cocycle is a multiplicative fixed-fibre character. -/
theorem graphDeterminantCharacter_mul
    {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (UE₁ UE₂ : Matrix E E ℂ) (UF₁ UF₂ : Matrix F F ℂ) :
    graphDeterminantCharacter (UE₁ * UE₂) (UF₁ * UF₂)
      = graphDeterminantCharacter UE₁ UF₁
          * graphDeterminantCharacter UE₂ UF₂ := by
  simp only [graphDeterminantCharacter, Matrix.det_mul, _root_.mul_inv_rev]
  ring

/-- Anomaly cancellation trivializes the determinant character. -/
theorem graphDeterminantCharacter_eq_one
    {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (UE : Matrix E E ℂ) (UF : Matrix F F ℂ)
    (hdet : UF.det = UE.det) (hne : UE.det ≠ 0) :
    graphDeterminantCharacter UE UF = 1 := by
  simp [graphDeterminantCharacter, hdet, hne]

/-- Exact finite-dimensional assembly of the massive graph-regulator clauses:
both square/gap identities, both actual orthogonal projectors, their source and
target dimensions, the canonical relative determinant-line equivalence, and
the spectrally weighted vertical Berry formula. -/
theorem canonical_graph_regulator_geometry_exact
    {E F : Type*} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F]
    (D : Matrix F E ℂ) (m : ℝ) (hm : 0 < m) :
    positiveGraphHamiltonian D m * positiveGraphHamiltonian D m =
        Matrix.fromBlocks (graphSourceMassGram D m) 0 0
          (graphTargetMassGram D m) ∧
    negativeGraphHamiltonian D m * negativeGraphHamiltonian D m =
        Matrix.fromBlocks (graphSourceMassGram D m) 0 0
          (graphTargetMassGram D m) ∧
    (positiveGraphHamiltonian D m * positiveGraphHamiltonian D m).PosDef ∧
    (negativeGraphHamiltonian D m * negativeGraphHamiltonian D m).PosDef ∧
    ((positiveGraphProjector D m hm)ᴴ = positiveGraphProjector D m hm ∧
      positiveGraphProjector D m hm * positiveGraphProjector D m hm =
        positiveGraphProjector D m hm) ∧
    ((negativeGraphProjector D m hm)ᴴ = negativeGraphProjector D m hm ∧
      negativeGraphProjector D m hm * negativeGraphProjector D m hm =
        negativeGraphProjector D m hm) ∧
    Module.finrank ℂ
        (LinearMap.range (positiveGraphProjector D m hm).mulVecLin) =
      Fintype.card F ∧
    Module.finrank ℂ
        (LinearMap.range (negativeGraphProjector D m hm).mulVecLin) =
      Fintype.card E ∧
    Nonempty (canonicalGraphRelativeLine D m hm ≃ₗ[ℂ]
      canonicalChiralDeterminantLine E F) ∧
    ∀ (XE : Matrix E E ℂ) (XF : Matrix F F ℂ),
      canonicalGraphBerryConnection
          (graphBerryWeight (graphSourceMassGram_posDef D m hm) m)
          D (XF * D - D * XE) =
        canonicalGraphVerticalMoment
          (1 - (m : ℂ) • Petz.invSqrtMat
            (graphSourceMassGram_posDef D m hm).1)
          (1 - (m : ℂ) • Petz.invSqrtMat
            (graphTargetMassGram_posDef D m hm).1)
          XE XF := by
  refine ⟨positiveGraphHamiltonian_sq_eq_massGrams D m,
    negativeGraphHamiltonian_sq_eq_massGrams D m,
    positiveGraphHamiltonian_sq_posDef D m hm,
    negativeGraphHamiltonian_sq_posDef D m hm,
    positiveGraphNegativeProjector_orthogonal D m hm,
    negativeGraphProjector_orthogonal D m hm,
    positiveGraphProjector_finrank D m hm,
    negativeGraphProjector_finrank D m hm,
    ⟨canonicalGraphRelativeLineEquiv D m hm⟩, ?_⟩
  intro XE XF
  exact canonicalGraphBerry_vertical_exact D m hm XE XF

/-- Generic projector/cocycle component of `thm:SMST-graph-regulator`. -/
theorem canonical_graph_regulator_geometry :
    (∀ {n : Type*} [Fintype n] [DecidableEq n]
      (S : Matrix n n ℂ), Sᴴ = S → S * S = 1 →
      (graphNegativeProjector S)ᴴ = graphNegativeProjector S
        ∧ graphNegativeProjector S * graphNegativeProjector S
          = graphNegativeProjector S)
    ∧ (∀ {E F : Type*} [Fintype E] [Fintype F]
      [DecidableEq E] [DecidableEq F]
      (UE : Matrix E E ℂ) (UF : Matrix F F ℂ),
      UF.det = UE.det → UE.det ≠ 0 →
      graphDeterminantCharacter UE UF = 1) :=
  ⟨graphNegativeProjector_orthogonal, graphDeterminantCharacter_eq_one⟩

end NCG
