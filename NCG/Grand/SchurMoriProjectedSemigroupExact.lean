/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SchurMoriEvolution
import NCG.Grand.VolterraMemory
import NCG.Grand.FiniteHermitianSemigroupLaplace

/-!
# Exact projected Schur--Mori semigroup

This file removes the abstract evolution hypotheses from the dynamic part of
`thm:modulated-renewal-Schur-Mori`.  In finite coordinates it starts with the
actual block semigroup

`exp (-t * [[A, B], [Bᴴ, C]])`

and derives the coupled visible/hidden differential equations.  These are the
input for the repository's Banach-space variation-of-constants theorem.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Interval Matrix.Norms.L2Operator

namespace NCG
namespace SchurMoriProjectedSemigroup

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

variable {m p : ℕ}

noncomputable local instance complexMatrixNormedAlgebraRat
    {n : Type*} [Fintype n] [DecidableEq n] :
    NormedAlgebra ℚ (Matrix n n ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

-- Keep the operator algebra on rectangular hidden columns explicit.  This
-- avoids typeclass ambiguity between the complex matrix norm and its real
-- restriction when elaborating `exp ((t-s) • H)`.
noncomputable local instance hiddenColumnEndomorphismNormedRing {m p : ℕ} :
    NormedRing
      (Matrix (Fin p) (Fin m) ℂ →L[ℝ] Matrix (Fin p) (Fin m) ℂ) :=
  ContinuousLinearMap.toNormedRing

noncomputable local instance hiddenColumnEndomorphismNormedAlgebra {m p : ℕ} :
    NormedAlgebra ℝ
      (Matrix (Fin p) (Fin m) ℂ →L[ℝ] Matrix (Fin p) (Fin m) ℂ) :=
  ContinuousLinearMap.toNormedAlgebra

local instance hiddenColumnEndomorphismIsTopologicalRing {m p : ℕ} :
    IsTopologicalRing
      (Matrix (Fin p) (Fin m) ℂ →L[ℝ] Matrix (Fin p) (Fin m) ℂ) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- The two-block Schur--Mori generator in chosen finite orthonormal bases. -/
def generator (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) :
    Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ :=
  fromBlocks A B Bᴴ C

/-- Continuous extraction of the visible-visible block. -/
noncomputable def visibleBlock :
    Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ →L[ℝ]
      Matrix (Fin m) (Fin m) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.toBlocks₁₁
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Continuous extraction of the hidden-visible block. -/
noncomputable def hiddenVisibleBlock :
    Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ →L[ℝ]
      Matrix (Fin p) (Fin m) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.toBlocks₂₁
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The actual visible covariance `P₁ exp(-tH) P₁`. -/
noncomputable def projectedCovariance (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p) ℂ)
    (t : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  (NormedSpace.exp (t • (-generator A B C))).toBlocks₁₁

/-- The hidden-visible column of the same actual block semigroup. -/
noncomputable def hiddenCovariance (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p) ℂ)
    (t : ℝ) : Matrix (Fin p) (Fin m) ℂ :=
  (NormedSpace.exp (t • (-generator A B C))).toBlocks₂₁

/-- The visible block of the actual semigroup satisfies the first coupled ODE. -/
theorem projectedCovariance_hasDerivAt [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) (t : ℝ) :
    HasDerivAt (projectedCovariance A B C)
      (-A * projectedCovariance A B C t - B * hiddenCovariance A B C t) t := by
  let H := generator A B C
  let Z := NormedSpace.exp (t • (-H))
  have hExp := hasDerivAt_exp_smul_const (-H) t
  have hcomm : Z * (-H) = (-H) * Z :=
    (((Commute.refl (-H)).smul_left t).exp_left).eq
  have h := (visibleBlock (m := m) (p := p)).hasFDerivAt.comp_hasDerivAt t hExp
  apply h.congr_deriv
  change (Z * (-H)).toBlocks₁₁ = _
  rw [hcomm]
  have hneg : -H = fromBlocks (-A) (-B) (-(Bᴴ)) (-C) := by
    simp [H, generator, fromBlocks_neg]
  rw [hneg, ← fromBlocks_toBlocks Z, fromBlocks_multiply, toBlocks_fromBlocks₁₁]
  simp [projectedCovariance, hiddenCovariance, H, Z, sub_eq_add_neg]

/-- The hidden-visible block satisfies the second coupled ODE. -/
theorem hiddenCovariance_hasDerivAt [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) (t : ℝ) :
    HasDerivAt (hiddenCovariance A B C)
      (-(Bᴴ) * projectedCovariance A B C t - C * hiddenCovariance A B C t) t := by
  let H := generator A B C
  let Z := NormedSpace.exp (t • (-H))
  have hExp := hasDerivAt_exp_smul_const (-H) t
  have hcomm : Z * (-H) = (-H) * Z :=
    (((Commute.refl (-H)).smul_left t).exp_left).eq
  have h := (hiddenVisibleBlock (m := m) (p := p)).hasFDerivAt.comp_hasDerivAt t hExp
  apply h.congr_deriv
  change (Z * (-H)).toBlocks₂₁ = _
  rw [hcomm]
  have hneg : -H = fromBlocks (-A) (-B) (-(Bᴴ)) (-C) := by
    simp [H, generator, fromBlocks_neg]
  rw [hneg, ← fromBlocks_toBlocks Z, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp [projectedCovariance, hiddenCovariance, H, Z, sub_eq_add_neg]

/-- The hidden covariance starts from zero. -/
theorem hiddenCovariance_zero [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) :
    hiddenCovariance A B C 0 = 0 := by
  simp [hiddenCovariance, NormedSpace.exp_zero, ← fromBlocks_one]

/-! ### Exact elimination of the hidden block -/

/-- Left multiplication by a rectangular matrix, as a real continuous linear map. -/
noncomputable def leftMul {r q n : ℕ} (M : Matrix (Fin r) (Fin q) ℂ) :
    Matrix (Fin q) (Fin n) ℂ →L[ℝ] Matrix (Fin r) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (mulLeftLinearMap (Fin n) ℝ M)

@[simp]
theorem leftMul_apply {r q n : ℕ} (M : Matrix (Fin r) (Fin q) ℂ)
    (X : Matrix (Fin q) (Fin n) ℂ) : leftMul M X = M * X := rfl

/-- The real-linear left regular representation of square hidden matrices. -/
noncomputable def leftRegularLinear (m p : ℕ) :
    Matrix (Fin p) (Fin p) ℂ →L[ℝ]
      (Matrix (Fin p) (Fin m) ℂ →L[ℝ] Matrix (Fin p) (Fin m) ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => leftMul (n := m) M
      map_add' := fun M N => by
        apply ContinuousLinearMap.ext
        intro X
        change (M + N) * X = M * X + N * X
        exact Matrix.add_mul M N X
      map_smul' := fun r M => by ext X i j; simp [Complex.real_smul] }

/-- The same left regular representation as a unital ring homomorphism. -/
noncomputable def leftRegularRingHom (m p : ℕ) :
    Matrix (Fin p) (Fin p) ℂ →+*
      (Matrix (Fin p) (Fin m) ℂ →L[ℝ] Matrix (Fin p) (Fin m) ℂ) where
  toFun := fun M => leftMul (n := m) M
  map_one' := by ext X i j; simp
  map_mul' := fun M N => by
    ext X i j
    simp [Matrix.mul_assoc]
  map_zero' := by ext X i j; simp
  map_add' := fun M N => by
    apply ContinuousLinearMap.ext
    intro X
    change (M + N) * X = M * X + N * X
    exact Matrix.add_mul M N X

/-- The exponential of hidden left multiplication acts by the literal matrix
exponential.  This is the bridge from the Banach-space Volterra theorem to the
matrix kernel printed in the manuscript. -/
theorem exp_leftMul_apply (C : Matrix (Fin p) (Fin p) ℂ)
    (X : Matrix (Fin p) (Fin m) ℂ) (u : ℝ) :
    (NormedSpace.exp (u • leftMul (n := m) C)) X =
      NormedSpace.exp (u • C) * X := by
  letI : NormedAlgebra ℚ
      (Matrix (Fin p) (Fin m) ℂ →L[ℝ] Matrix (Fin p) (Fin m) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  have hcont : Continuous (leftRegularRingHom m p) := by
    exact (leftRegularLinear m p).continuous
  have hmap := NormedSpace.map_exp (leftRegularRingHom m p) hcont (u • C)
  have happ := congrArg (fun T :
      Matrix (Fin p) (Fin m) ℂ →L[ℝ] Matrix (Fin p) (Fin m) ℂ => T X) hmap
  have hsmul : leftMul (n := m) (u • C) = u • leftMul (n := m) C := by
    ext Y i j
    simp [Complex.real_smul]
  change (leftMul (n := m) (NormedSpace.exp (u • C))) X =
    (NormedSpace.exp (leftMul (n := m) (u • C))) X at happ
  rw [hsmul] at happ
  simpa using happ.symm

/-- The true projected covariance satisfies the Mori--Zwanzig Volterra equation
with the operator exponential of hidden left multiplication.  No evolution or
integral representation is assumed. -/
theorem projectedCovariance_volterra_operator [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) (t : ℝ) :
    HasDerivAt (projectedCovariance A B C)
      ((leftMul (n := m) (-A)) (projectedCovariance A B C t) +
          (leftMul (n := m) (-B))
            ((NormedSpace.exp (t • leftMul (n := m) (-C)))
              (hiddenCovariance A B C 0)) +
        ∫ s in (0 : ℝ)..t,
          (leftMul (n := m) (-B))
            ((NormedSpace.exp ((t - s) • leftMul (n := m) (-C)))
              ((leftMul (n := m) (-(Bᴴ))) (projectedCovariance A B C s)))) t := by
  have hxcont : Continuous (projectedCovariance A B C) :=
    continuous_iff_continuousAt.mpr fun u =>
      (projectedCovariance_hasDerivAt A B C u).continuousAt
  have hx : ∀ u, HasDerivAt (projectedCovariance A B C)
      ((leftMul (n := m) (-A)) (projectedCovariance A B C u) +
        (leftMul (n := m) (-B)) (hiddenCovariance A B C u)) u := by
    intro u
    simpa [sub_eq_add_neg] using projectedCovariance_hasDerivAt A B C u
  have hy : ∀ u, HasDerivAt (hiddenCovariance A B C)
      ((leftMul (n := m) (-C)) (hiddenCovariance A B C u) +
        (leftMul (n := m) (-(Bᴴ))) (projectedCovariance A B C u)) u := by
    intro u
    simpa [sub_eq_add_neg, add_comm] using hiddenCovariance_hasDerivAt A B C u
  exact volterra_equation_with_initial_hidden
    (leftMul (n := m) (-A)) (leftMul (n := m) (-(Bᴴ)))
    (leftMul (n := m) (-B)) (leftMul (n := m) (-C))
    (projectedCovariance A B C) (hiddenCovariance A B C) hxcont hx hy t

/-- The exact projected covariance satisfies the literal matrix-valued memory
equation from the manuscript,
`U' = -AU + ∫₀ᵗ B exp(-(t-s)C) Bᴴ U(s) ds`. -/
theorem projectedCovariance_volterra [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) (t : ℝ) :
    HasDerivAt (projectedCovariance A B C)
      (-A * projectedCovariance A B C t +
        ∫ s in (0 : ℝ)..t,
          B * NormedSpace.exp ((t - s) • (-C)) * Bᴴ *
            projectedCovariance A B C s) t := by
  have h := projectedCovariance_volterra_operator A B C t
  apply h.congr_deriv
  rw [hiddenCovariance_zero A B C]
  simp only [map_zero, leftMul_apply, add_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  change (-B) *
      ((NormedSpace.exp ((t - s) • leftMul (n := m) (-C)))
        ((-Bᴴ) * projectedCovariance A B C s)) = _
  rw [exp_leftMul_apply]
  simp [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

/-! ### Exact Markov-closure obstruction -/

/-- The literal first derivative of the projected block exponential. -/
noncomputable def projectedCovarianceDeriv
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) (t : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  (NormedSpace.exp (t • (-generator A B C)) * (-generator A B C)).toBlocks₁₁

/-- The literal second derivative of the projected block exponential. -/
noncomputable def projectedCovarianceSecondDeriv
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) (t : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  (NormedSpace.exp (t • (-generator A B C)) * (-generator A B C) *
    (-generator A B C)).toBlocks₁₁

theorem projectedCovariance_hasDerivAt_exact [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) (t : ℝ) :
    HasDerivAt (projectedCovariance A B C)
      (projectedCovarianceDeriv A B C t) t := by
  exact (visibleBlock (m := m) (p := p)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const (-generator A B C) t)

theorem projectedCovarianceDeriv_hasDerivAt [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) (t : ℝ) :
    HasDerivAt (projectedCovarianceDeriv A B C)
      (projectedCovarianceSecondDeriv A B C t) t := by
  exact (visibleBlock (m := m) (p := p)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_exp_smul_const (-generator A B C) t).mul_const
      (-generator A B C))

/-- At the origin, the projected first derivative is `-A`. -/
theorem projectedCovarianceDeriv_zero [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) :
    projectedCovarianceDeriv A B C 0 = -A := by
  unfold projectedCovarianceDeriv generator
  rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mul, fromBlocks_neg,
    toBlocks_fromBlocks₁₁]

/-- At the origin, the projected second derivative is `A² + BBᴴ`. -/
theorem projectedCovarianceSecondDeriv_zero [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) :
    projectedCovarianceSecondDeriv A B C 0 = A * A + B * Bᴴ := by
  unfold projectedCovarianceSecondDeriv generator
  rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mul, neg_mul_neg,
    fromBlocks_multiply, toBlocks_fromBlocks₁₁]

/-- Exact Markov closure of the actual projected block semigroup occurs if
and only if the visible-hidden coupling vanishes. -/
theorem projectedCovariance_exact_markov_iff [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) :
    HasDerivAt (fun t => deriv (projectedCovariance A B C) t) (A * A) 0 ↔
      B = 0 := by
  have hderiv : (fun t => deriv (projectedCovariance A B C) t) =
      projectedCovarianceDeriv A B C := by
    funext t
    exact (projectedCovariance_hasDerivAt_exact A B C t).deriv
  have hU1 : HasDerivAt (projectedCovariance A B C) (-A) 0 :=
    (projectedCovariance_hasDerivAt_exact A B C 0).congr_deriv
      (projectedCovarianceDeriv_zero A B C)
  have hU2 : HasDerivAt (fun t => deriv (projectedCovariance A B C) t)
      (A * A + B * Bᴴ) 0 := by
    rw [hderiv]
    exact (projectedCovarianceDeriv_hasDerivAt A B C 0).congr_deriv
      (projectedCovarianceSecondDeriv_zero A B C)
  exact NCG.exact_markov_closure_iff A B (projectedCovariance A B C) hU1 hU2

/-! ### Exact block resolvent -/

/-- The shifted two-block generator `zI + H`, written blockwise. -/
def shiftedGenerator (z : ℂ) (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p) ℂ) :
    Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ :=
  fromBlocks (z • 1 + A) B Bᴴ (z • 1 + C)

/-- The blockwise shifted generator is literally `zI + H`. -/
theorem shiftedGenerator_eq_add_generator
    (z : ℂ) (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p) ℂ) :
    shiftedGenerator z A B C =
      z • (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) +
        generator A B C := by
  unfold shiftedGenerator generator
  rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
  simp

/-- A scalar resolvent shift factors from the full Schur--Mori semigroup as
the ordinary Laplace weight. -/
theorem exp_neg_shiftedGenerator_eq_weighted
    (z : ℝ) (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p) ℂ)
    (t : ℝ) :
    NormedSpace.exp
        ((-(t : ℂ)) • shiftedGenerator (z : ℂ) A B C) =
      Complex.exp ((-(t : ℂ)) * (z : ℂ)) •
        NormedSpace.exp (t • (-generator A B C)) := by
  rw [shiftedGenerator_eq_add_generator]
  have hsplit :
      ((-(t : ℂ)) •
          ((z : ℂ) •
            (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) +
            generator A B C)) =
        (((-(t : ℂ)) * (z : ℂ)) •
            (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ)) +
          t • (-generator A B C) := by
    ext i j
    simp [Complex.real_smul]
    ring
  rw [hsplit]
  have hcomm : Commute
      (((-(t : ℂ)) * (z : ℂ)) •
        (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ))
      (t • (-generator A B C)) := by
    rw [Algebra.smul_def, Matrix.mul_one]
    exact Algebra.commutes _ _
  rw [Matrix.exp_add_of_commute _ _ hcomm]
  have hscalar :
      NormedSpace.exp
          (((-(t : ℂ)) * (z : ℂ)) •
            (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ)) =
        Complex.exp ((-(t : ℂ)) * (z : ℂ)) •
          (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) := by
    rw [Algebra.smul_def, Matrix.mul_one,
      ← NormedSpace.algebraMap_exp_comm,
      ← Complex.exp_eq_exp_ℂ]
    simp [Algebra.smul_def]
  rw [hscalar, Matrix.smul_mul, Matrix.one_mul]

/-- Visible-block version of scalar Laplace weighting. -/
theorem shiftedSemigroup_visible_eq_weighted_projectedCovariance
    (z : ℝ) (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p) ℂ)
    (t : ℝ) :
    (NormedSpace.exp
        ((-(t : ℂ)) • shiftedGenerator (z : ℂ) A B C)).toBlocks₁₁ =
      Complex.exp ((-(t : ℂ)) * (z : ℂ)) •
        projectedCovariance A B C t := by
  rw [exp_neg_shiftedGenerator_eq_weighted]
  rfl

/-- A positive definite two-by-two block matrix has a positive definite Schur
complement of its positive definite lower-right block. -/
theorem schurComplement₂₂_posDef
    {A : Matrix (Fin m) (Fin m) ℂ} {B : Matrix (Fin m) (Fin p) ℂ}
    {D : Matrix (Fin p) (Fin p) ℂ}
    (hFull : (fromBlocks A B Bᴴ D).PosDef) (hD : D.PosDef)
    [Invertible D] :
    (A - B * D⁻¹ * Bᴴ).PosDef := by
  have hSchurHerm : (A - B * D⁻¹ * Bᴴ).IsHermitian :=
    (IsHermitian.fromBlocks₂₂ A B hD.1).mp hFull.1
  refine PosDef.of_dotProduct_mulVec_pos hSchurHerm fun x hx => ?_
  have hne : Sum.elim x (-((D⁻¹ * Bᴴ) *ᵥ x)) ≠ 0 := by
    intro hzero
    apply hx
    funext i
    simpa using congrFun hzero (Sum.inl i)
  have hq := hFull.dotProduct_mulVec_pos hne
  rw [dotProduct_mulVec,
    schur_complement_eq₂₂ _ _ _ _ hD.1, add_neg_cancel] at hq
  simpa [dotProduct_mulVec] using hq

/-- Positivity of the full Schur--Mori generator passes to its hidden
principal block. -/
theorem generator_hidden_posSemidef
    {A : Matrix (Fin m) (Fin m) ℂ} {B : Matrix (Fin m) (Fin p) ℂ}
    {C : Matrix (Fin p) (Fin p) ℂ}
    (hH : (generator A B C).PosSemidef) : C.PosSemidef := by
  have hprincipal := hH.submatrix (fun i : Fin p => Sum.inr i)
  have heq :
      (generator A B C).submatrix (fun i : Fin p => Sum.inr i)
        (fun i : Fin p => Sum.inr i) = C := by
    ext i j
    rfl
  rwa [heq] at hprincipal

/-- Visible block of the actual full resolvent. -/
noncomputable def projectedResolvent (z : ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (shiftedGenerator z A B C)⁻¹.toBlocks₁₁

/-- Hidden-visible block of the actual full resolvent. -/
noncomputable def hiddenResolvent (z : ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ) : Matrix (Fin p) (Fin m) ℂ :=
  (shiftedGenerator z A B C)⁻¹.toBlocks₂₁

/-- The positive-half-line integral of the visible block of the positively
shifted full semigroup is the visible block of the genuine full resolvent. -/
theorem integral_shiftedSemigroup_visible_eq_projectedResolvent
    [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ)
    (hH : (generator A B C).PosSemidef) (z : ℝ) (hz : 0 < z) :
    (∫ t : ℝ in Set.Ioi 0,
        (NormedSpace.exp
          ((-(t : ℂ)) • shiftedGenerator (z : ℂ) A B C)).toBlocks₁₁) =
      projectedResolvent (z : ℂ) A B C := by
  have hshift := shiftedGenerator_eq_add_generator (z : ℂ) A B C
  have hint := NCG.ImplicitEuler.integrableOn_exp_neg_shift_posSemidef hH z hz
  change MeasureTheory.Integrable
    (fun t : ℝ => NormedSpace.exp
      ((-(t : ℂ)) •
        ((z : ℂ) •
          (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) +
          generator A B C)))
    (MeasureTheory.volume.restrict (Set.Ioi 0)) at hint
  have hfull := NCG.ImplicitEuler.integral_exp_neg_shift_posSemidef_eq_inv hH z hz
  have hcomm := (visibleBlock (m := m) (p := p)).integral_comp_comm hint
  calc
    (∫ t : ℝ in Set.Ioi 0,
        (NormedSpace.exp
          ((-(t : ℂ)) • shiftedGenerator (z : ℂ) A B C)).toBlocks₁₁)
        = (visibleBlock (m := m) (p := p))
            (∫ t : ℝ in Set.Ioi 0,
              NormedSpace.exp
                ((-(t : ℂ)) •
                  ((z : ℂ) •
                    (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) +
                    generator A B C))) := by
          rw [hshift]
          exact hcomm
    _ = (visibleBlock (m := m) (p := p))
          (((z : ℂ) •
              (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) +
              generator A B C)⁻¹) := congrArg _ hfull
    _ = projectedResolvent (z : ℂ) A B C := by
      rw [← hshift]
      rfl

/-- The genuine Laplace transform of the actual projected covariance is the
visible block of the actual full resolvent. -/
theorem integral_weighted_projectedCovariance_eq_projectedResolvent
    [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ)
    (hH : (generator A B C).PosSemidef) (z : ℝ) (hz : 0 < z) :
    (∫ t : ℝ in Set.Ioi 0,
        Complex.exp ((-(t : ℂ)) * (z : ℂ)) •
          projectedCovariance A B C t) =
      projectedResolvent (z : ℂ) A B C := by
  rw [← integral_shiftedSemigroup_visible_eq_projectedResolvent
    A B C hH z hz]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  exact (shiftedSemigroup_visible_eq_weighted_projectedCovariance
    z A B C t).symm

/-- The blocks of the actual inverse satisfy both coupled resolvent equations;
these equations are derived, not supplied as hypotheses. -/
theorem projectedResolvent_block_equations
    (z : ℂ) (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p) ℂ)
    [Invertible (shiftedGenerator z A B C)] :
    ((z • 1 + A) * projectedResolvent z A B C +
        B * hiddenResolvent z A B C = 1) ∧
      (Bᴴ * projectedResolvent z A B C +
        (z • 1 + C) * hiddenResolvent z A B C = 0) := by
  have hfull : shiftedGenerator z A B C * (shiftedGenerator z A B C)⁻¹ = 1 :=
    Matrix.mul_inv_of_invertible _
  constructor
  · have h := congrArg Matrix.toBlocks₁₁ hfull
    rw [← fromBlocks_toBlocks ((shiftedGenerator z A B C)⁻¹)] at h
    rw [show shiftedGenerator z A B C =
        fromBlocks (z • 1 + A) B Bᴴ (z • 1 + C) from rfl,
      fromBlocks_multiply, toBlocks_fromBlocks₁₁] at h
    simpa [projectedResolvent, hiddenResolvent, shiftedGenerator,
      ← fromBlocks_one] using h
  · have h := congrArg Matrix.toBlocks₂₁ hfull
    rw [← fromBlocks_toBlocks ((shiftedGenerator z A B C)⁻¹)] at h
    rw [show shiftedGenerator z A B C =
        fromBlocks (z • 1 + A) B Bᴴ (z • 1 + C) from rfl,
      fromBlocks_multiply, toBlocks_fromBlocks₂₁] at h
    simpa [projectedResolvent, hiddenResolvent, shiftedGenerator,
      ← fromBlocks_one] using h

/-- The visible block of the actual full resolvent is exactly the Schur
complement resolvent.  The former top/bottom block equations are no longer
hypotheses. -/
theorem projectedResolvent_eq_schur
    (z : ℂ) (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p) ℂ)
    [Invertible (shiftedGenerator z A B C)]
    [Invertible (z • (1 : Matrix (Fin p) (Fin p) ℂ) + C)]
    [Invertible (z • (1 : Matrix (Fin m) (Fin m) ℂ) + A -
      B * (z • (1 : Matrix (Fin p) (Fin p) ℂ) + C)⁻¹ * Bᴴ)] :
    projectedResolvent z A B C =
      (z • (1 : Matrix (Fin m) (Fin m) ℂ) + A -
        B * (z • (1 : Matrix (Fin p) (Fin p) ℂ) + C)⁻¹ * Bᴴ)⁻¹ := by
  rcases projectedResolvent_block_equations z A B C with ⟨htop, hbottom⟩
  exact mori_laplace_resolvent A B C z
    (projectedResolvent z A B C) (hiddenResolvent z A B C) htop hbottom

/-- **Exact Schur--Mori Laplace formula without supplied resolvent
hypotheses.**  Positivity of the actual full generator and `z > 0`
construct all inverses appearing in the Schur formula. -/
theorem integral_weighted_projectedCovariance_eq_schur
    [Nonempty (Fin m ⊕ Fin p)]
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin p) ℂ)
    (hH : (generator A B C).PosSemidef) (z : ℝ) (hz : 0 < z) :
    (∫ t : ℝ in Set.Ioi 0,
        Complex.exp ((-(t : ℂ)) * (z : ℂ)) •
          projectedCovariance A B C t) =
      ((z : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) + A -
        B * ((z : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) + C)⁻¹ * Bᴴ)⁻¹ := by
  have hzFull :
      (((z : ℂ) •
        (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ))).PosDef := by
    simpa [Complex.real_smul] using
      (Matrix.PosDef.one.smul hz :
        (z • (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ)).PosDef)
  have hshift : (shiftedGenerator (z : ℂ) A B C).PosDef := by
    rw [shiftedGenerator_eq_add_generator]
    exact hzFull.add_posSemidef hH
  letI : Invertible (shiftedGenerator (z : ℂ) A B C) :=
    hshift.isUnit.invertible
  have hzHidden :
      (((z : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) + C)).PosDef := by
    have hzI : ((z : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ)).PosDef := by
      simpa [Complex.real_smul] using
        (Matrix.PosDef.one.smul hz :
          (z • (1 : Matrix (Fin p) (Fin p) ℂ)).PosDef)
    exact hzI.add_posSemidef (generator_hidden_posSemidef hH)
  letI : Invertible
      ((z : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) + C) :=
    hzHidden.isUnit.invertible
  have hSchur :
      ((z : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) + A -
        B * ((z : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) + C)⁻¹ * Bᴴ).PosDef := by
    apply schurComplement₂₂_posDef
    · simpa [shiftedGenerator] using hshift
    · exact hzHidden
  letI : Invertible
      ((z : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) + A -
        B * ((z : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) + C)⁻¹ * Bᴴ) :=
    hSchur.isUnit.invertible
  rw [integral_weighted_projectedCovariance_eq_projectedResolvent
    A B C hH z hz]
  exact projectedResolvent_eq_schur (z : ℂ) A B C

end SchurMoriProjectedSemigroup
end NCG
