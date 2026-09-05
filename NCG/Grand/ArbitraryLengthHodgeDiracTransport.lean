/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Unitary transport of arbitrary-length finite Hodge--Dirac complexes

This is the arbitrary-length completion of `thm:Hodge-Dirac-transport`.
A finite complex is represented by a family of finite-dimensional degrees
indexed by `Nat`, extended by zero after its last nonzero degree.  Every result
is uniform in the degree.

Besides the Laplacian intertwining, the file constructs the harmonic-space
linear equivalence, transports exact and coexact ranges, proves equality of
the Gram characteristic polynomials (the nonzero squared singular-value
multisets), and then proves invariance of finite torsion products and the
determinant-line metric factors derived from them.
-/

open Matrix

namespace NCG
namespace ArbitraryLengthHodgeDiracTransport

variable {C : Nat -> Type*}
  [forall k, Fintype (C k)] [forall k, DecidableEq (C k)]

/-- Degree-`k+1` Hodge Laplacian
`d_k d_k^* + d_{k+1}^* d_{k+1}`. -/
def degreeLaplacian
    (d : forall k, Matrix (C (k + 1)) (C k) Complex) (k : Nat) :
    Matrix (C (k + 1)) (C (k + 1)) Complex :=
  d k * (d k)ᴴ + (d (k + 1))ᴴ * d (k + 1)

/-- Harmonic vectors in one degree. -/
def harmonicSpace
    (d : forall k, Matrix (C (k + 1)) (C k) Complex) (k : Nat) :=
  LinearMap.ker (degreeLaplacian d k).mulVecLin

/-- Taking adjoints of a unitary intertwining relation reverses its direction
in the form needed by the Hodge Laplacian. -/
theorem unitary_adjoint_intertwining
    {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    (d d' : Matrix b a Complex)
    (Ua : Matrix a a Complex) (Ub : Matrix b b Complex)
    (hUaRight : Ua * Uaᴴ = 1) (hUbLeft : Ubᴴ * Ub = 1)
    (hchain : Ub * d = d' * Ua) :
    Ua * dᴴ = d'ᴴ * Ub := by
  have hadjoint := congrArg Matrix.conjTranspose hchain
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at hadjoint
  calc
    Ua * dᴴ = Ua * dᴴ * (1 : Matrix b b Complex) := by rw [Matrix.mul_one]
    _ = Ua * dᴴ * (Ubᴴ * Ub) := by rw [hUbLeft]
    _ = Ua * (dᴴ * Ubᴴ) * Ub := by simp only [Matrix.mul_assoc]
    _ = Ua * (Uaᴴ * d'ᴴ) * Ub := by rw [hadjoint]
    _ = (Ua * Uaᴴ) * (d'ᴴ * Ub) := by simp only [Matrix.mul_assoc]
    _ = d'ᴴ * Ub := by rw [hUaRight, Matrix.one_mul]

/-- At every degree of an arbitrary-length family, a unitary chain
equivalence intertwines the Hodge Laplacians. -/
theorem arbitraryLength_hodgeLaplacian_transport
    (d d' : forall k, Matrix (C (k + 1)) (C k) Complex)
    (U : forall k, Matrix (C k) (C k) Complex)
    (hULeft : forall k, (U k)ᴴ * U k = 1)
    (hURight : forall k, U k * (U k)ᴴ = 1)
    (hchain : forall k, U (k + 1) * d k = d' k * U k)
    (k : Nat) :
    U (k + 1) * degreeLaplacian d k =
      degreeLaplacian d' k * U (k + 1) := by
  have hadjIncoming : U k * (d k)ᴴ = (d' k)ᴴ * U (k + 1) :=
    unitary_adjoint_intertwining (d k) (d' k) (U k) (U (k + 1))
      (hURight k) (hULeft (k + 1)) (hchain k)
  have hadjOutgoing : U (k + 1) * (d (k + 1))ᴴ =
      (d' (k + 1))ᴴ * U (k + 2) :=
    unitary_adjoint_intertwining (d (k + 1)) (d' (k + 1))
      (U (k + 1)) (U (k + 2)) (hURight (k + 1))
      (hULeft (k + 2)) (hchain (k + 1))
  unfold degreeLaplacian
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · calc
      U (k + 1) * (d k * (d k)ᴴ) =
          (U (k + 1) * d k) * (d k)ᴴ := by rw [Matrix.mul_assoc]
      _ = (d' k * U k) * (d k)ᴴ := by rw [hchain k]
      _ = d' k * (U k * (d k)ᴴ) := by rw [Matrix.mul_assoc]
      _ = d' k * ((d' k)ᴴ * U (k + 1)) := by rw [hadjIncoming]
      _ = d' k * (d' k)ᴴ * U (k + 1) := by rw [Matrix.mul_assoc]
  · calc
      U (k + 1) * ((d (k + 1))ᴴ * d (k + 1)) =
          (U (k + 1) * (d (k + 1))ᴴ) * d (k + 1) := by
            rw [Matrix.mul_assoc]
      _ = ((d' (k + 1))ᴴ * U (k + 2)) * d (k + 1) := by
            rw [hadjOutgoing]
      _ = (d' (k + 1))ᴴ * (U (k + 2) * d (k + 1)) := by
            rw [Matrix.mul_assoc]
      _ = (d' (k + 1))ᴴ * (d' (k + 1) * U (k + 1)) := by
            rw [hchain (k + 1)]
      _ = (d' (k + 1))ᴴ * d' (k + 1) * U (k + 1) := by
            rw [Matrix.mul_assoc]

/-- The adjoint unitary gives the reverse Laplacian intertwining. -/
theorem arbitraryLength_hodgeLaplacian_reverse_transport
    (d d' : forall k, Matrix (C (k + 1)) (C k) Complex)
    (U : forall k, Matrix (C k) (C k) Complex)
    (hULeft : forall k, (U k)ᴴ * U k = 1)
    (hURight : forall k, U k * (U k)ᴴ = 1)
    (hchain : forall k, U (k + 1) * d k = d' k * U k)
    (k : Nat) :
    (U (k + 1))ᴴ * degreeLaplacian d' k =
      degreeLaplacian d k * (U (k + 1))ᴴ := by
  have hforward := arbitraryLength_hodgeLaplacian_transport
    d d' U hULeft hURight hchain k
  calc
    (U (k + 1))ᴴ * degreeLaplacian d' k =
        (U (k + 1))ᴴ * degreeLaplacian d' k *
          (U (k + 1) * (U (k + 1))ᴴ) := by
            simp [hURight]
    _ = (U (k + 1))ᴴ *
        (degreeLaplacian d' k * U (k + 1)) * (U (k + 1))ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = (U (k + 1))ᴴ *
        (U (k + 1) * degreeLaplacian d k) * (U (k + 1))ᴴ := by
          rw [hforward]
    _ = ((U (k + 1))ᴴ * U (k + 1)) *
        degreeLaplacian d k * (U (k + 1))ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = degreeLaplacian d k * (U (k + 1))ᴴ := by
          rw [hULeft, Matrix.one_mul]

/-- The degree unitary restricts to a linear equivalence of harmonic spaces,
which is the finite Hodge model of the induced cohomology equivalence. -/
noncomputable def harmonicSpaceEquiv
    (d d' : forall k, Matrix (C (k + 1)) (C k) Complex)
    (U : forall k, Matrix (C k) (C k) Complex)
    (hULeft : forall k, (U k)ᴴ * U k = 1)
    (hURight : forall k, U k * (U k)ᴴ = 1)
    (hchain : forall k, U (k + 1) * d k = d' k * U k)
    (k : Nat) : harmonicSpace d k ≃ₗ[Complex] harmonicSpace d' k where
  toFun x := ⟨U (k + 1) *ᵥ x, by
    apply LinearMap.mem_ker.mpr
    have hx : degreeLaplacian d k *ᵥ (x : C (k + 1) -> Complex) = 0 :=
      by
        have hx' := LinearMap.mem_ker.mp x.property
        change degreeLaplacian d k *ᵥ (x : C (k + 1) -> Complex) = 0 at hx'
        exact hx'
    have hintertwine := arbitraryLength_hodgeLaplacian_transport
      d d' U hULeft hURight hchain k
    calc
      degreeLaplacian d' k *ᵥ (U (k + 1) *ᵥ (x : C (k + 1) -> Complex)) =
          (degreeLaplacian d' k * U (k + 1)) *ᵥ
            (x : C (k + 1) -> Complex) := by rw [Matrix.mulVec_mulVec]
      _ = (U (k + 1) * degreeLaplacian d k) *ᵥ
            (x : C (k + 1) -> Complex) := by rw [← hintertwine]
      _ = U (k + 1) *ᵥ
          (degreeLaplacian d k *ᵥ (x : C (k + 1) -> Complex)) := by
            rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hx]; simp⟩
  invFun y := ⟨(U (k + 1))ᴴ *ᵥ y, by
    apply LinearMap.mem_ker.mpr
    have hy : degreeLaplacian d' k *ᵥ (y : C (k + 1) -> Complex) = 0 :=
      by
        have hy' := LinearMap.mem_ker.mp y.property
        change degreeLaplacian d' k *ᵥ (y : C (k + 1) -> Complex) = 0 at hy'
        exact hy'
    have hintertwine := arbitraryLength_hodgeLaplacian_reverse_transport
      d d' U hULeft hURight hchain k
    calc
      degreeLaplacian d k *ᵥ ((U (k + 1))ᴴ *ᵥ
          (y : C (k + 1) -> Complex)) =
          (degreeLaplacian d k * (U (k + 1))ᴴ) *ᵥ
            (y : C (k + 1) -> Complex) := by rw [Matrix.mulVec_mulVec]
      _ = ((U (k + 1))ᴴ * degreeLaplacian d' k) *ᵥ
            (y : C (k + 1) -> Complex) := by rw [← hintertwine]
      _ = (U (k + 1))ᴴ *ᵥ
          (degreeLaplacian d' k *ᵥ (y : C (k + 1) -> Complex)) := by
            rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hy]; simp⟩
  left_inv x := by
    apply Subtype.ext
    change (U (k + 1))ᴴ *ᵥ (U (k + 1) *ᵥ
      (x : C (k + 1) -> Complex)) = (x : C (k + 1) -> Complex)
    calc
      (U (k + 1))ᴴ *ᵥ (U (k + 1) *ᵥ (x : C (k + 1) -> Complex)) =
          ((U (k + 1))ᴴ * U (k + 1)) *ᵥ (x : C (k + 1) -> Complex) := by
            rw [Matrix.mulVec_mulVec]
      _ = (x : C (k + 1) -> Complex) := by
        rw [hULeft, Matrix.one_mulVec]
  right_inv y := by
    apply Subtype.ext
    change U (k + 1) *ᵥ ((U (k + 1))ᴴ *ᵥ
      (y : C (k + 1) -> Complex)) = (y : C (k + 1) -> Complex)
    calc
      U (k + 1) *ᵥ ((U (k + 1))ᴴ *ᵥ (y : C (k + 1) -> Complex)) =
          (U (k + 1) * (U (k + 1))ᴴ) *ᵥ (y : C (k + 1) -> Complex) := by
            rw [Matrix.mulVec_mulVec]
      _ = (y : C (k + 1) -> Complex) := by
        rw [hURight, Matrix.one_mulVec]
  map_add' x y := by
    apply Subtype.ext
    exact Matrix.mulVec_add _ _ _
  map_smul' c x := by
    apply Subtype.ext
    exact Matrix.mulVec_smul _ _ _

/-- Harmonic dimensions, hence cohomology dimensions, agree in every degree. -/
theorem arbitraryLength_harmonic_finrank_eq
    (d d' : forall k, Matrix (C (k + 1)) (C k) Complex)
    (U : forall k, Matrix (C k) (C k) Complex)
    (hULeft : forall k, (U k)ᴴ * U k = 1)
    (hURight : forall k, U k * (U k)ᴴ = 1)
    (hchain : forall k, U (k + 1) * d k = d' k * U k)
    (k : Nat) :
    Module.finrank Complex (harmonicSpace d k) =
      Module.finrank Complex (harmonicSpace d' k) :=
  LinearEquiv.finrank_eq (harmonicSpaceEquiv d d' U hULeft hURight hchain k)

/-- Exact ranges are carried to exact ranges. -/
theorem exactRange_transport
    (d d' : forall k, Matrix (C (k + 1)) (C k) Complex)
    (U : forall k, Matrix (C k) (C k) Complex)
    (hULeft : forall k, (U k)ᴴ * U k = 1)
    (hURight : forall k, U k * (U k)ᴴ = 1)
    (hchain : forall k, U (k + 1) * d k = d' k * U k)
    (k : Nat) (x : C (k + 1) -> Complex) :
    x ∈ LinearMap.range (d k).mulVecLin ↔
      U (k + 1) *ᵥ x ∈ LinearMap.range (d' k).mulVecLin := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨U k *ᵥ y, ?_⟩
    change d' k *ᵥ (U k *ᵥ y) = U (k + 1) *ᵥ (d k *ᵥ y)
    calc
      d' k *ᵥ (U k *ᵥ y) = (d' k * U k) *ᵥ y := by
        rw [Matrix.mulVec_mulVec]
      _ = (U (k + 1) * d k) *ᵥ y := by rw [← hchain k]
      _ = U (k + 1) *ᵥ (d k *ᵥ y) := by
        rw [Matrix.mulVec_mulVec]
  · rintro ⟨y, hy⟩
    refine ⟨(U k)ᴴ *ᵥ y, ?_⟩
    have hreverse : (U (k + 1))ᴴ * d' k = d k * (U k)ᴴ := by
      calc
        (U (k + 1))ᴴ * d' k =
            (U (k + 1))ᴴ * d' k * (1 : Matrix (C k) (C k) Complex) := by
              rw [Matrix.mul_one]
        _ = (U (k + 1))ᴴ * d' k * (U k * (U k)ᴴ) := by rw [hURight]
        _ = (U (k + 1))ᴴ * (d' k * U k) * (U k)ᴴ := by
              simp only [Matrix.mul_assoc]
        _ = (U (k + 1))ᴴ * (U (k + 1) * d k) * (U k)ᴴ := by
              rw [← hchain]
        _ = ((U (k + 1))ᴴ * U (k + 1)) * d k * (U k)ᴴ := by
              simp only [Matrix.mul_assoc]
        _ = d k * (U k)ᴴ := by rw [hULeft, Matrix.one_mul]
    change d k *ᵥ ((U k)ᴴ *ᵥ y) = x
    change d' k *ᵥ y = U (k + 1) *ᵥ x at hy
    calc
      d k *ᵥ ((U k)ᴴ *ᵥ y) = (d k * (U k)ᴴ) *ᵥ y := by
        rw [Matrix.mulVec_mulVec]
      _ = ((U (k + 1))ᴴ * d' k) *ᵥ y := by rw [hreverse]
      _ = (U (k + 1))ᴴ *ᵥ (d' k *ᵥ y) := by
        rw [Matrix.mulVec_mulVec]
      _ = (U (k + 1))ᴴ *ᵥ (U (k + 1) *ᵥ x) := by rw [hy]
      _ = ((U (k + 1))ᴴ * U (k + 1)) *ᵥ x := by
        rw [Matrix.mulVec_mulVec]
      _ = x := by rw [hULeft, Matrix.one_mulVec]

/-- Coexact ranges are carried to coexact ranges. -/
theorem coexactRange_transport
    (d d' : forall k, Matrix (C (k + 1)) (C k) Complex)
    (U : forall k, Matrix (C k) (C k) Complex)
    (hULeft : forall k, (U k)ᴴ * U k = 1)
    (hURight : forall k, U k * (U k)ᴴ = 1)
    (hchain : forall k, U (k + 1) * d k = d' k * U k)
    (k : Nat) (x : C (k + 1) -> Complex) :
    x ∈ LinearMap.range ((d (k + 1))ᴴ).mulVecLin ↔
      U (k + 1) *ᵥ x ∈
        LinearMap.range ((d' (k + 1))ᴴ).mulVecLin := by
  have hadjoint := unitary_adjoint_intertwining
    (d (k + 1)) (d' (k + 1)) (U (k + 1)) (U (k + 2))
    (hURight (k + 1)) (hULeft (k + 2)) (hchain (k + 1))
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨U (k + 2) *ᵥ y, ?_⟩
    change (d' (k + 1))ᴴ *ᵥ (U (k + 2) *ᵥ y) =
      U (k + 1) *ᵥ ((d (k + 1))ᴴ *ᵥ y)
    calc
      (d' (k + 1))ᴴ *ᵥ (U (k + 2) *ᵥ y) =
          ((d' (k + 1))ᴴ * U (k + 2)) *ᵥ y := by
            rw [Matrix.mulVec_mulVec]
      _ = (U (k + 1) * (d (k + 1))ᴴ) *ᵥ y := by rw [← hadjoint]
      _ = U (k + 1) *ᵥ ((d (k + 1))ᴴ *ᵥ y) := by
        rw [Matrix.mulVec_mulVec]
  · rintro ⟨y, hy⟩
    refine ⟨(U (k + 2))ᴴ *ᵥ y, ?_⟩
    have hreverse : (U (k + 1))ᴴ * (d' (k + 1))ᴴ =
        (d (k + 1))ᴴ * (U (k + 2))ᴴ := by
      calc
        (U (k + 1))ᴴ * (d' (k + 1))ᴴ =
            (U (k + 1))ᴴ * (d' (k + 1))ᴴ *
              (U (k + 2) * (U (k + 2))ᴴ) := by
                simp [hURight]
        _ = (U (k + 1))ᴴ *
            ((d' (k + 1))ᴴ * U (k + 2)) * (U (k + 2))ᴴ := by
              simp only [Matrix.mul_assoc]
        _ = (U (k + 1))ᴴ *
            (U (k + 1) * (d (k + 1))ᴴ) * (U (k + 2))ᴴ := by
              rw [← hadjoint]
        _ = ((U (k + 1))ᴴ * U (k + 1)) *
            (d (k + 1))ᴴ * (U (k + 2))ᴴ := by
              simp only [Matrix.mul_assoc]
        _ = (d (k + 1))ᴴ * (U (k + 2))ᴴ := by
              rw [hULeft, Matrix.one_mul]
    change (d (k + 1))ᴴ *ᵥ ((U (k + 2))ᴴ *ᵥ y) = x
    change (d' (k + 1))ᴴ *ᵥ y = U (k + 1) *ᵥ x at hy
    calc
      (d (k + 1))ᴴ *ᵥ ((U (k + 2))ᴴ *ᵥ y) =
          ((d (k + 1))ᴴ * (U (k + 2))ᴴ) *ᵥ y := by
            rw [Matrix.mulVec_mulVec]
      _ = ((U (k + 1))ᴴ * (d' (k + 1))ᴴ) *ᵥ y := by rw [hreverse]
      _ = (U (k + 1))ᴴ *ᵥ ((d' (k + 1))ᴴ *ᵥ y) := by
        rw [Matrix.mulVec_mulVec]
      _ = (U (k + 1))ᴴ *ᵥ (U (k + 1) *ᵥ x) := by rw [hy]
      _ = ((U (k + 1))ᴴ * U (k + 1)) *ᵥ x := by
        rw [Matrix.mulVec_mulVec]
      _ = x := by rw [hULeft, Matrix.one_mulVec]

/-! ## Singular spectra, torsion products, and determinant metrics -/

/-- Characteristic polynomial of `d^*d`, encoding the squared singular
values with multiplicity. -/
noncomputable def squaredSingularPolynomial
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    (d : Matrix b a Complex) : Polynomial Complex :=
  (dᴴ * d).charpoly

/-- The degreewise squared singular-value polynomial is invariant. -/
theorem squaredSingularPolynomial_transport
    (d d' : forall k, Matrix (C (k + 1)) (C k) Complex)
    (U : forall k, Matrix (C k) (C k) Complex)
    (hULeft : forall k, (U k)ᴴ * U k = 1)
    (hURight : forall k, U k * (U k)ᴴ = 1)
    (hchain : forall k, U (k + 1) * d k = d' k * U k)
    (k : Nat) :
    squaredSingularPolynomial (d' k) = squaredSingularPolynomial (d k) := by
  have hdprime : d' k = U (k + 1) * d k * (U k)ᴴ := by
    calc
      d' k = d' k * (1 : Matrix (C k) (C k) Complex) := by rw [Matrix.mul_one]
      _ = d' k * (U k * (U k)ᴴ) := by rw [hURight k]
      _ = (d' k * U k) * (U k)ᴴ := by rw [Matrix.mul_assoc]
      _ = (U (k + 1) * d k) * (U k)ᴴ := by rw [← hchain k]
  have hgram : (d' k)ᴴ * d' k =
      U k * ((d k)ᴴ * d k) * (U k)ᴴ := by
    rw [hdprime]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U (k + 1))ᴴ (U (k + 1))]
    rw [hULeft, Matrix.one_mul]
  unfold squaredSingularPolynomial
  rw [hgram]
  calc
    (U k * ((d k)ᴴ * d k) * (U k)ᴴ).charpoly =
        (U k * (((d k)ᴴ * d k) * (U k)ᴴ)).charpoly := by
          rw [Matrix.mul_assoc]
    _ = (((d k)ᴴ * d k) * (U k)ᴴ * U k).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = ((d k)ᴴ * d k * ((U k)ᴴ * U k)).charpoly := by
      rw [Matrix.mul_assoc]
    _ = ((d k)ᴴ * d k).charpoly := by rw [hULeft, Matrix.mul_one]

/-- Product of the nonzero squared singular values. -/
noncomputable def nonzeroSquaredSingularProduct
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    (d : Matrix b a Complex) : Complex :=
  ((squaredSingularPolynomial d).roots.filter (fun z => z ≠ 0)).prod

theorem nonzeroSquaredSingularProduct_transport
    (d d' : forall k, Matrix (C (k + 1)) (C k) Complex)
    (U : forall k, Matrix (C k) (C k) Complex)
    (hULeft : forall k, (U k)ᴴ * U k = 1)
    (hURight : forall k, U k * (U k)ᴴ = 1)
    (hchain : forall k, U (k + 1) * d k = d' k * U k)
    (k : Nat) :
    nonzeroSquaredSingularProduct (d' k) =
      nonzeroSquaredSingularProduct (d k) := by
  rw [nonzeroSquaredSingularProduct, nonzeroSquaredSingularProduct,
    squaredSingularPolynomial_transport d d' U hULeft hURight hchain k]

/-- A finite analytic-torsion product with arbitrary integral degree weights;
the standard torsion convention is a particular choice of these weights. -/
noncomputable def finiteTorsionProduct (N : Nat)
    (weight : Fin N -> Int)
    (d : forall k, Matrix (C (k + 1)) (C k) Complex) : Complex :=
  Finset.univ.prod fun k : Fin N =>
    (nonzeroSquaredSingularProduct (d k)) ^ (weight k)

theorem finiteTorsionProduct_transport
    (N : Nat) (weight : Fin N -> Int)
    (d d' : forall k, Matrix (C (k + 1)) (C k) Complex)
    (U : forall k, Matrix (C k) (C k) Complex)
    (hULeft : forall k, (U k)ᴴ * U k = 1)
    (hURight : forall k, U k * (U k)ᴴ = 1)
    (hchain : forall k, U (k + 1) * d k = d' k * U k) :
    finiteTorsionProduct N weight d' = finiteTorsionProduct N weight d := by
  unfold finiteTorsionProduct
  apply Finset.prod_congr rfl
  intro k hk
  rw [nonzeroSquaredSingularProduct_transport d d' U
    hULeft hURight hchain k]

/-- The determinant-line metric factor is the modulus of the nonzero
singular product and is therefore transported degreewise. -/
noncomputable def determinantLineMetricFactor
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    (d : Matrix b a Complex) : Real :=
  ‖nonzeroSquaredSingularProduct d‖

theorem determinantLineMetricFactor_transport
    (d d' : forall k, Matrix (C (k + 1)) (C k) Complex)
    (U : forall k, Matrix (C k) (C k) Complex)
    (hULeft : forall k, (U k)ᴴ * U k = 1)
    (hURight : forall k, U k * (U k)ᴴ = 1)
    (hchain : forall k, U (k + 1) * d k = d' k * U k)
    (k : Nat) :
    determinantLineMetricFactor (d' k) =
      determinantLineMetricFactor (d k) := by
  rw [determinantLineMetricFactor, determinantLineMetricFactor,
    nonzeroSquaredSingularProduct_transport d d' U hULeft hURight hchain k]

/-- A unitary change of basis has determinant modulus one, the top-exterior
power statement underlying determinant-line metric preservation. -/
theorem unitary_determinant_normSq_one
    {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix a a Complex) (hULeft : Uᴴ * U = 1) :
    Complex.normSq U.det = 1 := by
  have hdet := congrArg Matrix.det hULeft
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at hdet
  have hcast : ((Complex.normSq U.det : Real) : Complex) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    simpa [Complex.star_def] using hdet
  exact_mod_cast hcast

end ArbitraryLengthHodgeDiracTransport
end NCG
