/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MetzlerPerronExponentExact
import NCG.Grand.MetzlerSpectralAbscissaExact
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Algebraic simplicity of the irreducible Metzler Perron root

A normalized left/right pairing excludes nontrivial Jordan chains when
the eigenspace is one-dimensional. The maximal generalized eigenspace is
therefore a line, so the characteristic-polynomial root multiplicity is
exactly one. The hypotheses are then discharged by the existing positive
Perron eigenvectors for every irreducible Metzler matrix.
-/

open scoped Matrix

namespace NCG.PerronAlgebraicSimplicity

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A one-dimensional eigenspace with a nonzero normalized left pairing
has no additional generalized eigenvectors. -/
theorem maxGenEigenspace_eq_span
    (A : Matrix S S ℝ) (r ell : S → ℝ) (mu : ℝ)
    (hright : A.mulVec r = mu • r) (hleft : A.vecMul ell = mu • ell)
    (hnorm : ell ⬝ᵥ r = 1)
    (hsimple : ∀ y : S → ℝ, A.mulVec y = mu • y → ∃ c : ℝ, y = c • r) :
    Module.End.maxGenEigenspace A.toLin' mu = Submodule.span ℝ {r} := by
  let T : Module.End ℝ (S → ℝ) := A.toLin' - mu • 1
  have hT : ∀ y, T y = A.mulVec y - mu • y := by
    intro y
    simp [T, Matrix.toLin'_apply]
  have hpair : ∀ y, ell ⬝ᵥ T y = 0 := by
    intro y
    rw [hT, dotProduct_sub, Matrix.dotProduct_mulVec, hleft]
    simp
  have hkill : ∀ y, T (T y) = 0 → T y = 0 := by
    intro y hy
    have heig : A.mulVec (T y) = mu • T y := by
      exact sub_eq_zero.mp ((hT (T y)).symm.trans hy)
    obtain ⟨c, hc⟩ := hsimple (T y) heig
    have hzero := hpair y
    simp only [hc, dotProduct_smul, hnorm, smul_eq_mul, mul_one] at hzero
    simpa only [hzero, zero_smul] using hc
  have hpow : ∀ n : ℕ, ∀ y, (T ^ n) y = 0 → T y = 0 := by
    intro n
    induction n with
    | zero =>
        intro y hy
        have hy0 : y = 0 := by simpa using hy
        simp [hy0]
    | succ n ih =>
        intro y hy
        apply hkill y
        apply ih (T y)
        simpa only [pow_succ, Module.End.mul_apply] using hy
  ext y
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace A.toLin' mu y).mp hy
    have hzero := hpow n y hn
    have heig : A.mulVec y = mu • y := sub_eq_zero.mp ((hT y).symm.trans hzero)
    obtain ⟨c, hc⟩ := hsimple y heig
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · intro hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    apply (Module.End.mem_maxGenEigenspace A.toLin' mu (c • r)).mpr
    refine ⟨1, ?_⟩
    change (T ^ 1) (c • r) = 0
    rw [pow_one, map_smul, hT, hright, sub_self, smul_zero]

/-- The normalized left/right and geometric simplicity certificates imply
characteristic-polynomial root multiplicity exactly one. -/
theorem rootMultiplicity_eq_one_of_normalized_pair
    (A : Matrix S S ℝ) (r ell : S → ℝ) (mu : ℝ)
    (hright : A.mulVec r = mu • r) (hleft : A.vecMul ell = mu • ell)
    (hnorm : ell ⬝ᵥ r = 1)
    (hsimple : ∀ y : S → ℝ, A.mulVec y = mu • y → ∃ c : ℝ, y = c • r) :
    A.charpoly.rootMultiplicity mu = 1 := by
  have hr : r ≠ 0 := by
    intro hz
    simp [hz] at hnorm
  rw [← Matrix.charpoly_toLin', ← LinearMap.finrank_maxGenEigenspace_eq,
    maxGenEigenspace_eq_span A r ell mu hright hleft hnorm hsimple]
  exact finrank_span_singleton hr

/-- The canonical Perron exponent of every nonempty irreducible Metzler
matrix is algebraically simple, not merely geometrically simple. -/
theorem rootMultiplicity_exponent_eq_one [Nonempty S]
    (A : Matrix S S ℝ) (hA : MetzlerExponentialPositivity.IsIrreducibleMetzler A) :
    A.charpoly.rootMultiplicity (MetzlerPerronExponent.exponent A) = 1 := by
  obtain ⟨r, ell, hr, _, hright, hleft, hnorm⟩ :=
    MetzlerPerronExponent.exists_normalized_positive_left_right_eigenvectors A hA
  apply rootMultiplicity_eq_one_of_normalized_pair A r ell _ hright hleft hnorm
  intro y hy
  exact MetzlerPerronExponent.eigenspace_is_one_dimensional A hA hr hright hy

/-- The actual spectral bound is a simple real root of the characteristic
polynomial for every nonempty irreducible Metzler matrix. -/
theorem rootMultiplicity_spectralAbscissa_eq_one [Nonempty S]
    (A : Matrix S S ℝ) (hA : MetzlerExponentialPositivity.IsIrreducibleMetzler A) :
    A.charpoly.rootMultiplicity (MetzlerSpectralAbscissa.spectralAbscissa A) = 1 := by
  rw [MetzlerSpectralAbscissa.spectralAbscissa_eq_exponent A hA]
  exact rootMultiplicity_exponent_eq_one A hA

/-- Algebraic simplicity also holds in the complexified characteristic
polynomial used by the actual spectral-bound definition. -/
theorem complex_rootMultiplicity_spectralAbscissa_eq_one [Nonempty S]
    (A : Matrix S S ℝ) (hA : MetzlerExponentialPositivity.IsIrreducibleMetzler A) :
    (A.map Complex.ofReal).charpoly.rootMultiplicity
      (MetzlerSpectralAbscissa.spectralAbscissa A : ℂ) = 1 := by
  change (A.map (Complex.ofRealHom : ℝ →+* ℂ)).charpoly.rootMultiplicity
    (Complex.ofRealHom (MetzlerSpectralAbscissa.spectralAbscissa A)) = 1
  rw [Matrix.charpoly_map,
    ← Polynomial.eq_rootMultiplicity_map Complex.ofReal_injective]
  exact rootMultiplicity_spectralAbscissa_eq_one A hA

end

end NCG.PerronAlgebraicSimplicity
