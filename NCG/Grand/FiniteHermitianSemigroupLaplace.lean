/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianHeatSemigroup
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Laplace transforms of finite Hermitian semigroups

This file proves the finite-dimensional Laplace--resolvent identity from the
literal matrix exponential.  It first evaluates the integral in a diagonal
spectral frame and then transports it through a unitary eigenbasis.
-/

open Filter Matrix MeasureTheory Set
open scoped ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace NCG.ImplicitEuler

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Evaluation of one matrix entry, bundled continuously for the operator
norm on finite complex matrices. -/
noncomputable def matrixEntry (i j : ι) : Matrix ι ι ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp]
theorem matrixEntry_apply (i j : ι) (M : Matrix ι ι ℂ) :
    matrixEntry i j M = M i j := rfl

/-- Every entry of a strictly shifted nonnegative diagonal heat semigroup is
integrable on the positive half-line. -/
theorem integrableOn_finiteSpectralHeat_shift_entry
    (ν : ι → ℝ) (z : ℝ) (hz : 0 < z) (hν : ∀ i, 0 ≤ ν i) (i j : ι) :
    IntegrableOn
      (fun t : ℝ => (finiteSpectralHeat (fun k => z + ν k) t) i j)
      (Ioi 0) := by
  by_cases hij : i = j
  · subst j
    have hdecay : (-(((z + ν i : ℝ) : ℂ))).re < 0 := by
      change -(z + ν i) < 0
      linarith [hν i]
    have h := integrableOn_exp_mul_complex_Ioi hdecay 0
    convert h using 1
    funext t
    simp only [finiteSpectralHeat, Matrix.diagonal_apply, if_pos,
      Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  · simpa [finiteSpectralHeat, Matrix.diagonal_apply, hij] using
      (integrable_zero : Integrable
        (fun _ : ℝ => (0 : ℂ)) (volume.restrict (Ioi 0)))

/-- A strictly shifted nonnegative diagonal heat semigroup is Bochner
integrable on the positive half-line. -/
theorem integrableOn_finiteSpectralHeat_shift
    (ν : ι → ℝ) (z : ℝ) (hz : 0 < z) (hν : ∀ i, 0 ≤ ν i) :
    IntegrableOn (fun t : ℝ => finiteSpectralHeat (fun i => z + ν i) t)
      (Ioi 0) := by
  change Integrable (fun t : ℝ => finiteSpectralHeat (fun i => z + ν i) t)
    (volume.restrict (Ioi 0))
  apply Integrable.mono'
    (integrableOn_exp_mul_Ioi (a := -z) (by linarith) 0)
  · apply Continuous.aestronglyMeasurable
    unfold finiteSpectralHeat
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [finiteSpectralHeat, Matrix.l2_opNorm_diagonal]
    have htarget : 0 ≤ Real.exp (-z * t) := (Real.exp_pos _).le
    apply (pi_norm_le_iff_of_nonneg htarget).2
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have ht0 : 0 ≤ t := le_of_lt (show 0 < t from ht)
    have hprod : 0 ≤ t * ν i := mul_nonneg ht0 (hν i)
    nlinarith

/-- The positive-half-line integral of a shifted diagonal heat semigroup is
the diagonal reciprocal multiplier. -/
theorem integral_finiteSpectralHeat_shift
    (ν : ι → ℝ) (z : ℝ) (hz : 0 < z) (hν : ∀ i, 0 ≤ ν i) :
    (∫ t : ℝ in Ioi 0, finiteSpectralHeat (fun i => z + ν i) t) =
      Matrix.diagonal (fun i => (((z + ν i : ℝ) : ℂ)⁻¹)) := by
  have hint := integrableOn_finiteSpectralHeat_shift ν z hz hν
  change Integrable (fun t : ℝ => finiteSpectralHeat (fun i => z + ν i) t)
    (volume.restrict (Ioi 0)) at hint
  ext i j
  change matrixEntry i j
      (∫ t : ℝ in Ioi 0, finiteSpectralHeat (fun i => z + ν i) t) = _
  rw [← (matrixEntry i j).integral_comp_comm hint]
  by_cases hij : i = j
  · subst j
    have hdecay : (-(((z + ν i : ℝ) : ℂ))).re < 0 := by
      change -(z + ν i) < 0
      linarith [hν i]
    have hscalar := integral_exp_mul_complex_Ioi hdecay 0
    have hne : (((z + ν i : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (ne_of_gt
        (lt_of_lt_of_le hz (le_add_of_nonneg_right (hν i))))
    rw [Matrix.diagonal_apply, if_pos rfl]
    convert hscalar using 1
    · apply integral_congr_ae
      filter_upwards with t
      simp only [matrixEntry_apply, finiteSpectralHeat,
        Matrix.diagonal_apply, if_pos, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    · rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
        neg_div_neg_eq, one_div]
  · simp [matrixEntry_apply, finiteSpectralHeat, hij]

/-- Diagonal form of the Laplace--resolvent identity. -/
theorem integral_finiteSpectralHeat_shift_eq_inv
    (ν : ι → ℝ) (z : ℝ) (hz : 0 < z) (hν : ∀ i, 0 ≤ ν i) :
    (∫ t : ℝ in Ioi 0, finiteSpectralHeat (fun i => z + ν i) t) =
      (Matrix.diagonal (fun i => (((z + ν i : ℝ) : ℂ))))⁻¹ := by
  rw [integral_finiteSpectralHeat_shift ν z hz hν]
  symm
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    have hne : (((z + ν i : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (ne_of_gt
        (lt_of_lt_of_le hz (le_add_of_nonneg_right (hν i))))
    rw [Matrix.diagonal_apply, if_pos rfl, Matrix.one_apply, if_pos rfl]
    exact inv_mul_cancel₀ hne
  · simp [Matrix.diagonal_apply, hij]

/-! ### Unitary transport and Hermitian generators -/

/-- Unitary conjugation, regarded as a real continuous linear map so that it
commutes with Bochner integration. -/
noncomputable def unitaryConjugation (U : Matrix.unitaryGroup ι ℂ) :
    Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Unitary.conjStarAlgAut ℂ _ U M
      map_add' := fun M N => map_add (Unitary.conjStarAlgAut ℂ _ U) M N
      map_smul' := fun r M => by
        change Unitary.conjStarAlgAut ℂ _ U (r • M) =
          r • Unitary.conjStarAlgAut ℂ _ U M
        rw [← Complex.real_smul, ← Complex.real_smul]
        exact map_smul (Unitary.conjStarAlgAut ℂ _ U) (r : ℂ) M }

@[simp]
theorem unitaryConjugation_apply (U : Matrix.unitaryGroup ι ℂ)
    (M : Matrix ι ι ℂ) :
    unitaryConjugation U M = Unitary.conjStarAlgAut ℂ _ U M := rfl

/-- A strictly shifted nonnegative heat semigroup remains integrable after
unitary spectral transport. -/
theorem integrableOn_finiteUnitarySpectralHeat_shift
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (z : ℝ)
    (hz : 0 < z) (hν : ∀ i, 0 ≤ ν i) :
    IntegrableOn
      (fun t : ℝ => finiteUnitarySpectralHeat U (fun i => z + ν i) t)
      (Ioi 0) := by
  have hdiag := integrableOn_finiteSpectralHeat_shift ν z hz hν
  change Integrable
    (fun t : ℝ => unitaryConjugation U
      (finiteSpectralHeat (fun i => z + ν i) t))
    (volume.restrict (Ioi 0))
  exact (unitaryConjugation U).integrable_comp hdiag

/-- Unitary spectral form of the finite-dimensional Laplace--resolvent
identity. -/
theorem integral_finiteUnitarySpectralHeat_shift_eq_inv
    (U : Matrix.unitaryGroup ι ℂ) (ν : ι → ℝ) (z : ℝ)
    (hz : 0 < z) (hν : ∀ i, 0 ≤ ν i) :
    (∫ t : ℝ in Ioi 0,
        finiteUnitarySpectralHeat U (fun i => z + ν i) t) =
      (Unitary.conjStarAlgAut ℂ _ U
        (Matrix.diagonal (fun i => (((z + ν i : ℝ) : ℂ)))))⁻¹ := by
  let D : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i => (((z + ν i : ℝ) : ℂ)))
  let Dinv : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i => (((z + ν i : ℝ) : ℂ)⁻¹))
  have hdiagint := integrableOn_finiteSpectralHeat_shift ν z hz hν
  have hint :
      (∫ t : ℝ in Ioi 0,
          finiteUnitarySpectralHeat U (fun i => z + ν i) t) =
        Unitary.conjStarAlgAut ℂ _ U Dinv := by
    change (∫ t : ℝ in Ioi 0,
        unitaryConjugation U
          (finiteSpectralHeat (fun i => z + ν i) t)) = _
    rw [(unitaryConjugation U).integral_comp_comm hdiagint]
    rw [integral_finiteSpectralHeat_shift ν z hz hν]
    rfl
  rw [hint]
  symm
  apply Matrix.inv_eq_left_inv
  rw [← map_mul]
  change Unitary.conjStarAlgAut ℂ _ U (Dinv * D) = 1
  have hDD : Dinv * D = 1 := by
    rw [Dinv, D, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      have hne : (((z + ν i : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast (ne_of_gt
          (lt_of_lt_of_le hz (le_add_of_nonneg_right (hν i))))
      rw [Matrix.diagonal_apply, if_pos rfl,
        Matrix.one_apply, if_pos rfl]
      exact inv_mul_cancel₀ hne
    · simp [hij]
  rw [hDD, map_one]

/-- Spectral reconstruction of a positive Hermitian matrix after a positive
scalar shift. -/
theorem unitary_diagonal_shift_eq
    {H : Matrix ι ι ℂ} (hH : H.PosSemidef) (z : ℝ) :
    Unitary.conjStarAlgAut ℂ _ hH.1.eigenvectorUnitary
        (Matrix.diagonal
          (fun i => (((z + hH.1.eigenvalues i : ℝ) : ℂ)))) =
      ((z : ℂ) • (1 : Matrix ι ι ℂ) + H) := by
  have hspectral :
      Unitary.conjStarAlgAut ℂ _ hH.1.eigenvectorUnitary
          (Matrix.diagonal
            (fun i => ((hH.1.eigenvalues i : ℝ) : ℂ))) = H := by
    calc
      _ = Unitary.conjStarAlgAut ℂ _ hH.1.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.1.eigenvalues)) := by
        apply congrArg
          (Unitary.conjStarAlgAut ℂ _ hH.1.eigenvectorUnitary)
        ext i j
        by_cases hij : i = j
        · subst j
          simp [RCLike.ofReal]
        · simp [hij]
      _ = H := hH.1.spectral_theorem.symm
  have hdiag :
      Matrix.diagonal
          (fun i => (((z + hH.1.eigenvalues i : ℝ) : ℂ))) =
        (z : ℂ) • (1 : Matrix ι ι ℂ) +
          Matrix.diagonal
            (fun i => ((hH.1.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hdiag, map_add, map_smul, map_one, hspectral]

/-- **Finite Hermitian Laplace--resolvent identity.**  For every
positive-semidefinite Hermitian matrix `H` and every real `z > 0`, the
positive-half-line integral of `exp(-t(zI+H))` is the genuine matrix inverse
`(zI+H)⁻¹`. -/
theorem integral_exp_neg_shift_posSemidef_eq_inv
    {H : Matrix ι ι ℂ} (hH : H.PosSemidef) (z : ℝ) (hz : 0 < z) :
    (∫ t : ℝ in Ioi 0,
        NormedSpace.exp
          ((-(t : ℂ)) • ((z : ℂ) • (1 : Matrix ι ι ℂ) + H))) =
      (((z : ℂ) • (1 : Matrix ι ι ℂ) + H)⁻¹) := by
  let U := hH.1.eigenvectorUnitary
  let ν := hH.1.eigenvalues
  have hgen := unitary_diagonal_shift_eq hH z
  have hfun :
      (fun t : ℝ => NormedSpace.exp
        ((-(t : ℂ)) • ((z : ℂ) • (1 : Matrix ι ι ℂ) + H))) =
      (fun t : ℝ => finiteUnitarySpectralHeat U (fun i => z + ν i) t) := by
    funext t
    rw [finiteUnitarySpectralHeat_eq_exp_smul]
    congr 1
    exact congrArg (fun M : Matrix ι ι ℂ => (-(t : ℂ)) • M) hgen.symm
  rw [hfun, integral_finiteUnitarySpectralHeat_shift_eq_inv
    U ν z hz hH.eigenvalues_nonneg, hgen]

end NCG.ImplicitEuler
