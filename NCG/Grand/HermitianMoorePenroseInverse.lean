/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral Moore--Penrose inverse of a finite Hermitian matrix

The pinned Mathlib version supplies the finite Hermitian spectral theorem but
does not package a Moore--Penrose inverse.  This module defines it by inverting
the nonzero eigenvalues and proves the Hermitian and two Penrose identities.
-/

open Matrix
open Unitary

namespace NCG
namespace HermitianMoorePenroseInverse

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Reciprocal of a Hermitian eigenvalue, extended by zero at the kernel. -/
noncomputable def reciprocalEigenvalue (A : Matrix n n Complex)
    (hA : A.IsHermitian) (i : n) : Complex :=
  if hA.eigenvalues i = 0 then 0 else (hA.eigenvalues i : Complex)⁻¹

/-- Moore--Penrose inverse obtained by applying the reciprocal-on-support
function in an orthonormal eigenbasis. -/
noncomputable def hermitianMoorePenroseInverse
    (A : Matrix n n Complex) (hA : A.IsHermitian) : Matrix n n Complex :=
  conjStarAlgAut Complex _ hA.eigenvectorUnitary
    (Matrix.diagonal (reciprocalEigenvalue A hA))

private theorem diagonal_eigenvalue_reciprocal_penrose_left
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) *
        Matrix.diagonal (reciprocalEigenvalue A hA) *
        Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) =
      Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hzero : hA.eigenvalues i = 0
    · simp [reciprocalEigenvalue, hzero]
    · simp [reciprocalEigenvalue, hzero]
  · simp [Matrix.diagonal_apply_ne _ hij]

private theorem diagonal_eigenvalue_reciprocal_penrose_right
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    Matrix.diagonal (reciprocalEigenvalue A hA) *
        Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) *
        Matrix.diagonal (reciprocalEigenvalue A hA) =
      Matrix.diagonal (reciprocalEigenvalue A hA) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hzero : hA.eigenvalues i = 0
    · simp [reciprocalEigenvalue, hzero]
    · simp [reciprocalEigenvalue, hzero]
  · simp [Matrix.diagonal_apply_ne _ hij]

/-- The spectral reciprocal is Hermitian. -/
theorem hermitianMoorePenroseInverse_isHermitian
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    (hermitianMoorePenroseInverse A hA)ᴴ =
      hermitianMoorePenroseInverse A hA := by
  have hdiag :
      (Matrix.diagonal (reciprocalEigenvalue A hA)).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    rw [isSelfAdjoint_iff]
    by_cases hzero : hA.eigenvalues i = 0 <;>
      simp [reciprocalEigenvalue, hzero]
  exact (hdiag.isSelfAdjoint.map
    (conjStarAlgAut Complex _ hA.eigenvectorUnitary)).star_eq

/-- First Penrose identity `A A^dagger A = A`. -/
theorem hermitianMoorePenroseInverse_penrose_left
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    A * hermitianMoorePenroseInverse A hA * A = A := by
  let phi := conjStarAlgAut Complex _ hA.eigenvectorUnitary
  let D := Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues)
  let R := Matrix.diagonal (reciprocalEigenvalue A hA)
  have hAphi : A = phi D := by
    simpa [phi, D] using hA.spectral_theorem
  have hdiag : D * R * D = D := by
    exact diagonal_eigenvalue_reciprocal_penrose_left A hA
  change A * phi R * A = A
  rw [hAphi]
  calc
    phi D * phi R * phi D = phi (D * R * D) := by simp
    _ = phi D := by rw [hdiag]

/-- Second Penrose identity `A^dagger A A^dagger = A^dagger`. -/
theorem hermitianMoorePenroseInverse_penrose_right
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    hermitianMoorePenroseInverse A hA * A *
        hermitianMoorePenroseInverse A hA =
      hermitianMoorePenroseInverse A hA := by
  let phi := conjStarAlgAut Complex _ hA.eigenvectorUnitary
  let D := Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues)
  let R := Matrix.diagonal (reciprocalEigenvalue A hA)
  have hAphi : A = phi D := by
    simpa [phi, D] using hA.spectral_theorem
  have hdiag : R * D * R = R := by
    exact diagonal_eigenvalue_reciprocal_penrose_right A hA
  change phi R * A * phi R = phi R
  rw [hAphi]
  calc
    phi R * phi D * phi R = phi (R * D * R) := by simp
    _ = phi R := by rw [hdiag]

omit [DecidableEq n] in
/-- Packaged existence of a Hermitian matrix satisfying both Penrose
identities. -/
theorem exists_hermitian_moorePenroseInverse
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    exists G : Matrix n n Complex,
      Gᴴ = G /\ A * G * A = A /\ G * A * G = G := by
  classical
  refine ⟨hermitianMoorePenroseInverse A hA,
    hermitianMoorePenroseInverse_isHermitian A hA,
    hermitianMoorePenroseInverse_penrose_left A hA,
    hermitianMoorePenroseInverse_penrose_right A hA⟩

end HermitianMoorePenroseInverse
end NCG
