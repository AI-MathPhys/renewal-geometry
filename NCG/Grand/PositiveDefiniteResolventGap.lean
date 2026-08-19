/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianResolventGap
import NCG.Grand.FiniteCommutantPoincareGap

/-!
# Exact shifted-resolvent norm of a positive-definite matrix

A positive-definite finite Gram matrix has no zero spectral coordinates.  Thus the zero-mode
compression in the general finite Hermitian theorem is the identity, and the norm of the literal
shifted inverse is the reciprocal of the shift plus the least eigenvalue.  The final theorem
composes this fact with the least-eigenvalue certificate used by the finite commutant audit.
-/

open Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.SpectralGap

variable {r : ℕ}

/-- A positive-definite matrix has zero zero-eigenspace projection. -/
theorem finiteUnitaryZeroSpectralProjection_eq_zero_of_posDef
    (G : Matrix (Fin r) (Fin r) ℂ) (hG : G.PosDef) :
    finiteUnitaryZeroSpectralProjection hG.1.eigenvectorUnitary hG.1.eigenvalues = 0 := by
  unfold finiteUnitaryZeroSpectralProjection
  have hdiag : finiteZeroSpectralProjection hG.1.eigenvalues = 0 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [finiteZeroSpectralProjection, ne_of_gt (hG.eigenvalues_pos i)]
    · simp [finiteZeroSpectralProjection, hij]
  rw [hdiag, map_zero]

/-- If `μ` is the attained least eigenvalue of a positive-definite matrix, the norm of its
literal shifted inverse is `(λ + μ)⁻¹`. -/
theorem norm_inv_shiftedPosDef_eq_inv_add_of_least
    (G : Matrix (Fin r) (Fin r) ℂ) (hG : G.PosDef) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ)
    (hmin : ∀ i, μ ≤ hG.1.eigenvalues i)
    (hattain : ∃ i, hG.1.eigenvalues i = μ) :
    ‖((lam : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) + G)⁻¹‖ = (lam + μ)⁻¹ := by
  have hcompressed := norm_shiftedPosSemidefiniteResolvent_zeroCompression_eq_inv_add
    hG.posSemidef lam μ hlam hμ (fun i _ ↦ hmin i) hattain
  rw [finiteUnitaryZeroSpectralProjection_eq_zero_of_posDef G hG,
    sub_zero, one_mul, mul_one] at hcompressed
  exact hcompressed

/-- The shifted inverse norm of a positive-definite matrix recovers its least eigenvalue. -/
theorem inverseNormGap_inv_shiftedPosDef_eq_least
    (G : Matrix (Fin r) (Fin r) ℂ) (hG : G.PosDef) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ)
    (hmin : ∀ i, μ ≤ hG.1.eigenvalues i)
    (hattain : ∃ i, hG.1.eigenvalues i = μ) :
    ‖((lam : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) + G)⁻¹‖⁻¹ - lam = μ := by
  rw [norm_inv_shiftedPosDef_eq_inv_add_of_least G hG lam μ hlam hμ hmin hattain,
    inv_inv]
  ring

/-- Every nonempty positive-definite matrix admits an attained least eigenvalue that satisfies the
exact shifted-resolvent norm and inverse-norm gap formulas. -/
theorem exists_leastEigenvalue_posDef_resolventGap
    (hr : 0 < r) (G : Matrix (Fin r) (Fin r) ℂ) (hG : G.PosDef)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ μ : ℝ, 0 < μ ∧
      (∃ i : Fin r, μ = hG.1.eigenvalues i) ∧
      (∀ i : Fin r, μ ≤ hG.1.eigenvalues i) ∧
      ‖((lam : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) + G)⁻¹‖ = (lam + μ)⁻¹ ∧
      ‖((lam : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) + G)⁻¹‖⁻¹ - lam = μ := by
  obtain ⟨μ, hμ, hattain, hmin, _⟩ := NCG.posDef_min_eigenvalue_quadratic hr G hG
  refine ⟨μ, hμ, hattain, hmin, ?_, ?_⟩
  · exact norm_inv_shiftedPosDef_eq_inv_add_of_least G hG lam μ hlam hμ hmin
      ⟨hattain.choose, hattain.choose_spec.symm⟩
  · exact inverseNormGap_inv_shiftedPosDef_eq_least G hG lam μ hlam hμ hmin
      ⟨hattain.choose, hattain.choose_spec.symm⟩

/-- The finite commutant certificate and the literal resolvent calculation in one theorem.  On a
nonzero kernel complement, the restricted commutator Gram has an attained least eigenvalue, its
Poincare inequality, and both exact shifted-resolvent formulas. -/
theorem matrix_commutant_least_eigenvalue_resolvent_gap
    {n : Type*} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ)
    (shift : ℝ) (hshift : 0 < shift) :
    let K : Submodule ℂ (EuclideanSpace ℂ (n × n)) :=
      (LinearMap.ker (NCG.jointCommutatorL2 c))ᗮ
    K = ⊥ ∨
      ∃ (r : ℕ) (G : Matrix (Fin r) (Fin r) ℂ)
        (hG : G.PosDef) (μ : ℝ),
        r = Module.finrank ℂ K
        ∧ 0 < μ
        ∧ (∃ i : Fin r, μ = hG.1.eigenvalues i)
        ∧ (∀ i : Fin r, μ ≤ hG.1.eigenvalues i)
        ∧ ‖((shift : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) + G)⁻¹‖ =
            (shift + μ)⁻¹
        ∧ ‖((shift : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) + G)⁻¹‖⁻¹ - shift = μ
        ∧ (∀ (X P : Matrix n n ℂ),
          (∀ j, c j * P = P * c j) →
          NCG.matrixL2 (X - P) ∈ K →
          μ * (((X - P)ᴴ * (X - P)).trace).re ≤
            ∑ j, (((c j * X - X * c j)ᴴ *
              (c j * X - X * c j)).trace).re) := by
  dsimp only
  obtain hzero | ⟨r, G, hG, μ, hr, hμ, hattain, hmin, hgap⟩ :=
    NCG.matrix_commutant_least_eigenvalue_gap c
  · exact Or.inl hzero
  · right
    have hattain' : ∃ i : Fin r, hG.1.eigenvalues i = μ :=
      ⟨hattain.choose, hattain.choose_spec.symm⟩
    refine ⟨r, G, hG, μ, hr, hμ, hattain, hmin, ?_, ?_, hgap⟩
    · exact norm_inv_shiftedPosDef_eq_inv_add_of_least
        G hG shift μ hshift hμ hmin hattain'
    · exact inverseNormGap_inv_shiftedPosDef_eq_least
        G hG shift μ hshift hμ hmin hattain'
end NCG.SpectralGap
