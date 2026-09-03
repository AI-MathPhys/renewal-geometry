/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MetzlerPerronExponentExact
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Exact uniqueness for the bordered Perron eigenvalue system

The implicit-function construction of a normalized Perron eigenbranch uses a
bordered linear system.  Its homogeneous kernel is trivial when the Perron
eigenspace is one-dimensional and the left/right eigenvectors have pairing
one.  This file proves that finite-dimensional algebraic prerequisite without
assuming the existence of a differentiable or analytic branch.
-/

open Matrix Finset
open scoped BigOperators

noncomputable section

namespace NCG.PerronBorderedEigenSystem

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The normalized bordered eigenvalue system has only the zero homogeneous
solution.  This is the injectivity calculation behind the Perron
implicit-function theorem. -/
theorem bordered_homogeneous_unique
    (A : Matrix S S ℝ) (r ell y : S → ℝ) (psi a : ℝ)
    (hleft : A.vecMul ell = psi • ell)
    (hnorm : ell ⬝ᵥ r = 1)
    (hsimple : ∀ z : S → ℝ,
      A.mulVec z = psi • z → ∃ b : ℝ, z = b • r)
    (hvector : A.mulVec y = psi • y + a • r)
    (hnormalization : ell ⬝ᵥ y = 0) :
    y = 0 ∧ a = 0 := by
  have ha : a = 0 := by
    calc
      a = psi * 0 + a * 1 := by ring
      _ = ell ⬝ᵥ (psi • y + a • r) := by
        simp [dotProduct_add, dotProduct_smul,
          hnormalization, hnorm]
      _ = ell ⬝ᵥ A.mulVec y := by rw [hvector]
      _ = A.vecMul ell ⬝ᵥ y := Matrix.dotProduct_mulVec ell A y
      _ = (psi • ell) ⬝ᵥ y := by rw [hleft]
      _ = psi * (ell ⬝ᵥ y) := by simp
      _ = 0 := by rw [hnormalization, mul_zero]
  have hyEig : A.mulVec y = psi • y := by
    simpa [ha] using hvector
  obtain ⟨b, hy⟩ := hsimple y hyEig
  have hb : b = 0 := by
    rw [hy, dotProduct_smul, hnorm] at hnormalization
    simpa using hnormalization
  constructor
  · rw [hy, hb, zero_smul]
  · exact ha

/-- The bordered derivative operator for the normalized eigen-equation. -/
def borderedOperator
    (A : Matrix S S ℝ) (r ell : S → ℝ) (psi : ℝ) :
    ((S → ℝ) × ℝ) →ₗ[ℝ] ((S → ℝ) × ℝ) where
  toFun z :=
    (A.mulVec z.1 - psi • z.1 - z.2 • r, ell ⬝ᵥ z.1)
  map_add' x y := by
    apply Prod.ext
    · change A.mulVec (x.1 + y.1) - psi • (x.1 + y.1) -
          (x.2 + y.2) • r =
        (A.mulVec x.1 - psi • x.1 - x.2 • r) +
          (A.mulVec y.1 - psi • y.1 - y.2 • r)
      rw [Matrix.mulVec_add, smul_add, add_smul]
      module
    · change ell ⬝ᵥ (x.1 + y.1) = ell ⬝ᵥ x.1 + ell ⬝ᵥ y.1
      exact dotProduct_add ell x.1 y.1
  map_smul' c x := by
    apply Prod.ext
    · change A.mulVec (c • x.1) - psi • (c • x.1) -
          (c * x.2) • r =
        c • (A.mulVec x.1 - psi • x.1 - x.2 • r)
      rw [Matrix.mulVec_smul]
      module
    · change ell ⬝ᵥ (c • x.1) = c • (ell ⬝ᵥ x.1)
      rw [dotProduct_smul]

@[simp]
theorem borderedOperator_apply
    (A : Matrix S S ℝ) (r ell y : S → ℝ) (psi a : ℝ) :
    borderedOperator A r ell psi (y, a) =
      (A.mulVec y - psi • y - a • r, ell ⬝ᵥ y) := rfl

/-- One-dimensionality and normalized left/right pairing make the bordered
operator injective. -/
theorem borderedOperator_injective
    (A : Matrix S S ℝ) (r ell : S → ℝ) (psi : ℝ)
    (hleft : A.vecMul ell = psi • ell)
    (hnorm : ell ⬝ᵥ r = 1)
    (hsimple : ∀ z : S → ℝ,
      A.mulVec z = psi • z → ∃ b : ℝ, z = b • r) :
    Function.Injective (borderedOperator A r ell psi) := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  rintro ⟨y, a⟩ hmem
  have hz : borderedOperator A r ell psi (y, a) = 0 :=
    LinearMap.mem_ker.mp hmem
  have hfirst := congrArg Prod.fst hz
  have hsecond := congrArg Prod.snd hz
  have hvector : A.mulVec y = psi • y + a • r := by
    funext i
    have hi := congrFun hfirst i
    simp only [borderedOperator_apply, Prod.fst_zero, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
    linarith
  have hnormalization : ell ⬝ᵥ y = 0 := by
    simpa using hsecond
  obtain ⟨hy, ha⟩ := bordered_homogeneous_unique
    A r ell y psi a hleft hnorm hsimple hvector hnormalization
  simp [hy, ha]

/-- In finite dimension the injective bordered operator is automatically
bijective.  This is the exact nonsingularity hypothesis required by a local
implicit-function construction of the Perron eigenbranch. -/
theorem borderedOperator_bijective
    (A : Matrix S S ℝ) (r ell : S → ℝ) (psi : ℝ)
    (hleft : A.vecMul ell = psi • ell)
    (hnorm : ell ⬝ᵥ r = 1)
    (hsimple : ∀ z : S → ℝ,
      A.mulVec z = psi • z → ∃ b : ℝ, z = b • r) :
    Function.Bijective (borderedOperator A r ell psi) := by
  have hinj := borderedOperator_injective
    A r ell psi hleft hnorm hsimple
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The bordered derivative, bundled as a continuous linear endomorphism.
Continuity is automatic because the state space is finite. -/
def borderedContinuousOperator
    (A : Matrix S S ℝ) (r ell : S → ℝ) (psi : ℝ) :
    ((S → ℝ) × ℝ) →L[ℝ] ((S → ℝ) × ℝ) :=
  (borderedOperator A r ell psi).toContinuousLinearMap

@[simp]
theorem borderedContinuousOperator_apply
    (A : Matrix S S ℝ) (r ell y : S → ℝ) (psi a : ℝ) :
    borderedContinuousOperator A r ell psi (y, a) =
      (A.mulVec y - psi • y - a • r, ell ⬝ᵥ y) := rfl

/-- A bijective bordered derivative is invertible in the precise continuous
linear sense used by mathlib's inverse- and implicit-function theorems. -/
theorem borderedContinuousOperator_isInvertible
    (A : Matrix S S ℝ) (r ell : S → ℝ) (psi : ℝ)
    (hleft : A.vecMul ell = psi • ell)
    (hnorm : ell ⬝ᵥ r = 1)
    (hsimple : ∀ z : S → ℝ,
      A.mulVec z = psi • z → ∃ b : ℝ, z = b • r) :
    (borderedContinuousOperator A r ell psi).IsInvertible := by
  have hbij := borderedOperator_bijective
    A r ell psi hleft hnorm hsimple
  let e : ((S → ℝ) × ℝ) ≃ₗ[ℝ] ((S → ℝ) × ℝ) :=
    LinearEquiv.ofBijective (borderedOperator A r ell psi) hbij
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.coe_injective
  exact LinearMap.ext (fun z => rfl)

/-- For an irreducible Metzler matrix, the canonical positive Perron pair
makes the bordered homogeneous system injective. -/
theorem irreducibleMetzler_bordered_homogeneous_unique
    [Nonempty S]
    (A : Matrix S S ℝ)
    (hA : MetzlerExponentialPositivity.IsIrreducibleMetzler A)
    (r ell y : S → ℝ) (a : ℝ)
    (hr : ∀ i, 0 < r i)
    (hrEig : A.mulVec r = MetzlerPerronExponent.exponent A • r)
    (hleft : A.vecMul ell = MetzlerPerronExponent.exponent A • ell)
    (hnorm : ell ⬝ᵥ r = 1)
    (hvector : A.mulVec y =
      MetzlerPerronExponent.exponent A • y + a • r)
    (hnormalization : ell ⬝ᵥ y = 0) :
    y = 0 ∧ a = 0 := by
  apply bordered_homogeneous_unique A r ell y
    (MetzlerPerronExponent.exponent A) a
    hleft hnorm
  · intro z hz
    exact MetzlerPerronExponent.eigenspace_is_one_dimensional
      A hA hr hrEig hz
  · exact hvector
  · exact hnormalization

/-- The canonical normalized Perron bordered operator of an irreducible
Metzler matrix is bijective. -/
theorem irreducibleMetzler_borderedOperator_bijective
    [Nonempty S]
    (A : Matrix S S ℝ)
    (hA : MetzlerExponentialPositivity.IsIrreducibleMetzler A)
    (r ell : S → ℝ)
    (hr : ∀ i, 0 < r i)
    (hrEig : A.mulVec r = MetzlerPerronExponent.exponent A • r)
    (hleft : A.vecMul ell = MetzlerPerronExponent.exponent A • ell)
    (hnorm : ell ⬝ᵥ r = 1) :
    Function.Bijective
      (borderedOperator A r ell (MetzlerPerronExponent.exponent A)) := by
  apply borderedOperator_bijective A r ell
    (MetzlerPerronExponent.exponent A) hleft hnorm
  intro z hz
  exact MetzlerPerronExponent.eigenspace_is_one_dimensional
    A hA hr hrEig hz

/-- For the canonical simple Perron root of an irreducible Metzler matrix,
the bordered derivative is an invertible continuous linear map. -/
theorem irreducibleMetzler_borderedContinuousOperator_isInvertible
    [Nonempty S]
    (A : Matrix S S ℝ)
    (hA : MetzlerExponentialPositivity.IsIrreducibleMetzler A)
    (r ell : S → ℝ)
    (hr : ∀ i, 0 < r i)
    (hrEig : A.mulVec r = MetzlerPerronExponent.exponent A • r)
    (hleft : A.vecMul ell = MetzlerPerronExponent.exponent A • ell)
    (hnorm : ell ⬝ᵥ r = 1) :
    (borderedContinuousOperator A r ell
      (MetzlerPerronExponent.exponent A)).IsInvertible := by
  apply borderedContinuousOperator_isInvertible A r ell
    (MetzlerPerronExponent.exponent A) hleft hnorm
  intro z hz
  exact MetzlerPerronExponent.eigenspace_is_one_dimensional
    A hA hr hrEig hz

end NCG.PerronBorderedEigenSystem
