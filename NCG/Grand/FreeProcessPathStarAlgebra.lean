/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProcessHistoryStarAlgebra
import Mathlib.Algebra.Star.Free

/-!
# The free process-path star algebra

We construct the formal path star-algebra used by the process representation.
Forward and reverse letters are exchanged by star.  Two additional letters
represent `i I` and `-i I`; their kernel relations recover complex scalar
multiplication after representation while allowing the free algebra itself to
be built over `ℝ`, where conjugation of coefficients is trivial.
-/

open Matrix

namespace NCG

/-- Oriented primitive paths, together with formal `±i` scalar letters. -/
inductive ProcessPathGenerator (Label : Type*)
  | imag
  | negImag
  | forward (σ : Label)
  | reverse (σ : Label)
  deriving DecidableEq

namespace ProcessPathGenerator

variable {Label : Type*}

/-- Formal adjoint on path generators. -/
def flip : ProcessPathGenerator Label → ProcessPathGenerator Label
  | imag => negImag
  | negImag => imag
  | forward σ => reverse σ
  | reverse σ => forward σ

@[simp] theorem flip_flip (g : ProcessPathGenerator Label) :
    flip (flip g) = g := by cases g <;> rfl

end ProcessPathGenerator

/-- The underlying free noncommutative path algebra. -/
@[reducible] def FreeProcessPathAlgebra (Label : Type*) :=
  FreeAlgebra ℝ (ProcessPathGenerator Label)

namespace FreeProcessPathAlgebra

variable {Label : Type*}

instance : Ring (FreeProcessPathAlgebra Label) := by
  unfold FreeProcessPathAlgebra
  infer_instance

instance : Algebra ℝ (FreeProcessPathAlgebra Label) := by
  unfold FreeProcessPathAlgebra
  infer_instance

/-- Generator reversal, regarded in the opposite free algebra. -/
private def generatorStarMap (g : ProcessPathGenerator Label) :
    (FreeProcessPathAlgebra Label)ᵐᵒᵖ :=
  MulOpposite.op (FreeAlgebra.ι ℝ (ProcessPathGenerator.flip g))

/-- Algebra lift of generator reversal into the opposite algebra. -/
private noncomputable def pathStarLift :
    FreeProcessPathAlgebra Label →ₐ[ℝ] (FreeProcessPathAlgebra Label)ᵐᵒᵖ :=
  FreeAlgebra.lift ℝ (generatorStarMap (Label := Label))

/-- The anti-multiplicative extension of generator reversal. -/
private noncomputable def pathStar (x : FreeProcessPathAlgebra Label) :
    FreeProcessPathAlgebra Label :=
  MulOpposite.unop (pathStarLift (Label := Label) x)

private theorem pathStar_algebraMap (r : ℝ) :
    pathStar (Label := Label)
        (algebraMap ℝ (FreeProcessPathAlgebra Label) r)
      = algebraMap ℝ (FreeProcessPathAlgebra Label) r := by
  unfold pathStar
  rw [(pathStarLift (Label := Label)).commutes]
  rfl

private theorem pathStar_of_raw (g : ProcessPathGenerator Label) :
    pathStar (Label := Label) (FreeAlgebra.ι ℝ g)
      = FreeAlgebra.ι ℝ (ProcessPathGenerator.flip g) := by
  unfold pathStar pathStarLift
  rw [FreeAlgebra.lift_ι_apply]
  rfl

private theorem pathStar_mul (a b : FreeProcessPathAlgebra Label) :
    pathStar (a * b) = pathStar b * pathStar a := by
  unfold pathStar
  rw [map_mul]
  rfl

private theorem pathStar_add (a b : FreeProcessPathAlgebra Label) :
    pathStar (a + b) = pathStar a + pathStar b := by
  unfold pathStar
  rw [map_add]
  rfl

noncomputable instance : StarRing (FreeProcessPathAlgebra Label) where
  star := pathStar
  star_involutive x := by
    refine FreeAlgebra.induction (R := ℝ) (X := ProcessPathGenerator Label)
      (motive := fun x => pathStar (pathStar x) = x)
      ?_ ?_ ?_ ?_ x
    · intro r
      rw [pathStar_algebraMap, pathStar_algebraMap]
    · intro g
      rw [pathStar_of_raw, pathStar_of_raw, ProcessPathGenerator.flip_flip]
    · intro a b ha hb
      rw [pathStar_mul, pathStar_mul, ha, hb]
    · intro a b ha hb
      rw [pathStar_add, pathStar_add, ha, hb]
  star_mul a b := by
    exact pathStar_mul a b
  star_add a b := by
    exact pathStar_add a b

/-- Inclusion of a formal oriented path generator. -/
def of (g : ProcessPathGenerator Label) : FreeProcessPathAlgebra Label :=
  FreeAlgebra.ι ℝ g

@[simp] theorem star_of (g : ProcessPathGenerator Label) :
    star (of g) = of (ProcessPathGenerator.flip g) := by
  exact pathStar_of_raw g

/-- Matrix assigned to each oriented generator. -/
def generatorMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (T : Label → Matrix n n ℂ) : ProcessPathGenerator Label → Matrix n n ℂ
  | .imag => Complex.I • 1
  | .negImag => -Complex.I • 1
  | .forward σ => T σ
  | .reverse σ => (T σ)ᴴ

@[simp] theorem generatorMatrix_flip {n : Type*} [Fintype n] [DecidableEq n]
    (T : Label → Matrix n n ℂ) (g : ProcessPathGenerator Label) :
    generatorMatrix T (ProcessPathGenerator.flip g)
      = (generatorMatrix T g)ᴴ := by
  cases g <;> simp [generatorMatrix, ProcessPathGenerator.flip]

/-- Evaluation of the free path algebra in a family of primitive matrices. -/
noncomputable def representation {n : Type*} [Fintype n] [DecidableEq n]
    (T : Label → Matrix n n ℂ) :
    FreeProcessPathAlgebra Label →ₐ[ℝ] Matrix n n ℂ :=
  FreeAlgebra.lift ℝ (generatorMatrix T)

@[simp] theorem representation_of {n : Type*} [Fintype n] [DecidableEq n]
    (T : Label → Matrix n n ℂ) (g : ProcessPathGenerator Label) :
    representation T (of g) = generatorMatrix T g := by
  exact FreeAlgebra.lift_ι_apply _ g

/-- Evaluation respects formal path adjoints. -/
theorem representation_map_star {n : Type*} [Fintype n] [DecidableEq n]
    (T : Label → Matrix n n ℂ) (x : FreeProcessPathAlgebra Label) :
    representation T (star x) = star (representation T x) := by
  refine FreeAlgebra.induction (R := ℝ) (X := ProcessPathGenerator Label) (motive := fun x =>
      representation T (star x) = star (representation T x))
    ?_ ?_ ?_ ?_ x
  · intro r
    rw [show star (algebraMap ℝ (FreeProcessPathAlgebra Label) r)
        = algebraMap ℝ (FreeProcessPathAlgebra Label) r from
          pathStar_algebraMap r]
    rw [(representation T).commutes]
    ext i j
    by_cases h : i = j
    · subst j
      simp [Algebra.algebraMap_eq_smul_one, Matrix.conjTranspose_apply,
        Matrix.one_apply]
    · simp [Algebra.algebraMap_eq_smul_one, Matrix.conjTranspose_apply,
        Matrix.one_apply, h, Ne.symm h]
  · intro g
    change representation T (star (of g)) = star (representation T (of g))
    rw [star_of, representation_of, representation_of, generatorMatrix_flip]
    rfl
  · intro a b ha hb
    rw [star_mul, map_mul, map_mul, ha, hb, star_mul]
  · intro a b ha hb
    rw [star_add, map_add, map_add, ha, hb, star_add]

/-- Bundled free path star representation. -/
noncomputable def starRepresentation {n : Type*} [Fintype n] [DecidableEq n]
    (T : Label → Matrix n n ℂ) :
    FreeProcessPathAlgebra Label →⋆ₐ[ℝ] Matrix n n ℂ where
  __ := representation T
  map_star' := representation_map_star T

/-- The forward letter, reverse letter, and imaginary scalar have exactly the
required represented values. -/
theorem starRepresentation_generators {n : Type*} [Fintype n] [DecidableEq n]
    (T : Label → Matrix n n ℂ) (a : Label) :
    starRepresentation T (of (.forward a)) = T a
    ∧ starRepresentation T (of (.reverse a)) = (T a)ᴴ
    ∧ starRepresentation T (of .imag) = Complex.I • 1 := by
  simp [starRepresentation, generatorMatrix]

/-- Although the formal path algebra is presented over `ℝ`, its represented
range is closed under arbitrary complex scalars.  The formal `imag` generator
supplies multiplication by `i`; the real and imaginary parts of the scalar
then give a preimage for every complex multiple. -/
theorem starRepresentation_range_complex_smul
    {n : Type*} [Fintype n] [DecidableEq n]
    (T : Label → Matrix n n ℂ) (z : ℂ)
    (y : (starRepresentation T).toAlgHom.range) :
    z • (y : Matrix n n ℂ) ∈ (starRepresentation T).toAlgHom.range := by
  obtain ⟨x, hx⟩ := y.property
  refine ⟨z.re • x + z.im • (of .imag * x), ?_⟩
  change representation T (z.re • x + z.im • (of .imag * x)) =
    z • (y : Matrix n n ℂ)
  change representation T x = (y : Matrix n n ℂ) at hx
  calc
    _ = representation T (z.re • x) +
        representation T (z.im • (of .imag * x)) :=
      (representation T).map_add _ _
    _ = z.re • representation T x +
        z.im • representation T (of .imag * x) := by
      have hreal : representation T (z.re • x) = z.re • representation T x :=
        (representation T).toLinearMap.map_smul z.re x
      have himag : representation T (z.im • (of .imag * x)) =
          z.im • representation T (of .imag * x) :=
        (representation T).toLinearMap.map_smul z.im (of .imag * x)
      exact congrArg₂ (· + ·) hreal himag
    _ = z • (y : Matrix n n ℂ) := by
      have hmul : representation T (of .imag * x) =
          representation T (of .imag) * representation T x :=
        (representation T).map_mul _ _
      rw [hmul, representation_of, hx]
      simp [generatorMatrix]
      ext i j
      change (z.re : ℂ) * (y : Matrix n n ℂ) i j +
        (z.im : ℂ) * (Complex.I * (y : Matrix n n ℂ) i j) =
          z * (y : Matrix n n ℂ) i j
      rw [← mul_assoc, ← add_mul, Complex.re_add_im]

/-- The represented range, equipped with the complex algebra structure
supplied by `starRepresentation_range_complex_smul`, is the concrete
finite-matrix process-history star algebra. -/
noncomputable def freeProcessHistoryImage
    {n : Type*} [Fintype n] [DecidableEq n]
    (T : Label → Matrix n n ℂ) : StarSubalgebra ℂ (Matrix n n ℂ) where
  carrier := (starRepresentation T).toAlgHom.range
  zero_mem' := (starRepresentation T).toAlgHom.range.zero_mem
  add_mem' := fun hx hy => (starRepresentation T).toAlgHom.range.add_mem hx hy
  one_mem' := (starRepresentation T).toAlgHom.range.one_mem
  mul_mem' := fun hx hy => (starRepresentation T).toAlgHom.range.mul_mem hx hy
  algebraMap_mem' := by
    intro z
    have hone : (1 : Matrix n n ℂ) ∈ (starRepresentation T).toAlgHom.range :=
      (starRepresentation T).toAlgHom.range.one_mem
    have hz := starRepresentation_range_complex_smul T z
      (⟨1, hone⟩ : (starRepresentation T).toAlgHom.range)
    simpa [Algebra.algebraMap_eq_smul_one] using hz
  star_mem' := by
    rintro y ⟨x, hx⟩
    refine ⟨star x, ?_⟩
    change representation T (star x) = star y
    change representation T x = y at hx
    rw [representation_map_star, hx]

/-- The concrete process-history star algebra is finite-dimensional over
`ℂ`, with dimension bounded by its ambient matrix algebra. -/
theorem freeProcessHistoryImage_finrank_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (T : Label → Matrix n n ℂ) :
    Module.finrank ℂ (freeProcessHistoryImage T) ≤
      Module.finrank ℂ (Matrix n n ℂ) :=
  Submodule.finrank_le (freeProcessHistoryImage T).toSubalgebra.toSubmodule

/-- The free path representation has a star-stable two-sided kernel and is
canonically isomorphic, after quotienting, to its represented range. -/
theorem freeProcessPath_quotient_representation
    {n : Type*} [Fintype n] [DecidableEq n]
    (T : Label → Matrix n n ℂ) :
    (∀ x, x ∈ RingHom.ker (starRepresentation T).toAlgHom.toRingHom →
      star x ∈ RingHom.ker (starRepresentation T).toAlgHom.toRingHom)
    ∧ Nonempty
      ((RingCon.ker (starRepresentation T).toAlgHom.toRingHom).Quotient
        ≃ₐ[ℝ] (starRepresentation T).toAlgHom.range) := by
  constructor
  · intro x hx
    change starRepresentation T (star x) = 0
    exact ((starRepresentation T).map_star' x).trans
      ((congrArg star (show starRepresentation T x = 0 from hx)).trans (star_zero _))
  · exact ⟨RingCon.quotientKerEquivRangeₐ (starRepresentation T).toAlgHom⟩

end FreeProcessPathAlgebra

end NCG
