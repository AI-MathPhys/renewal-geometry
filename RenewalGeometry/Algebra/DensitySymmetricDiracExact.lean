/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Density-symmetric form of a Clifford-module Dirac operator (formal surrogate)

Paper `predictive_spectral_geometry`, label `lem:supp-density-symmetric`.

The continuum objects (spinor bundle, Levi-Civita spin connection `Ω_j`, the
operator `D_g = -i Σ_j c^j (∂_j + Ω_j)` on `L²(Q, S_d; ρ dx)`) are replaced by
the abstract algebra the paper's proof actually manipulates
(`CliffordModuleDerivationData`):

* a commutative algebra `F` of scalar functions with derivations `∂_j`;
* a (noncommutative) algebra `A` of operators, a ring homomorphism `M : F → A`
  (multiplication operators), covariant derivatives `∇_j ∈ A` with
  `[∇_j, M_f] = M_{∂_j f}`, and Clifford coefficients `c^j ∈ A` commuting with
  every scalar multiplication operator;
* a positive density given by an invertible square root `σ = ρ^{1/2}`, `ρ = σ²`;
* the contracted metric-compatibility identity of the paper's proof,
  `Σ_j [∇_j, c^j] = -Σ_j c^j M_{∂_j log ρ}` with `∂_j log ρ := ρ⁻¹ ∂_j ρ`
  (`contracted`).

`eq:supp-density-symmetric` (`densitySymmetric_identity`): with `U_ρ = M_σ`,
`M_σ D_g M_σ⁻¹ = -(i/2) Σ_j (c^j ∇_j + ∇_j c^j)`.  The scalar-free form
`conj_sum_eq` is also recorded.
-/

namespace RenewalGeometry.DensitySymmetricDirac

variable {F A : Type*} [CommRing F] [Algebra ℂ F] [Ring A] [Algebra ℂ A] {d : ℕ}

/-- The abstract data of the paper's computation: scalar functions `F` with
derivations `∂_j`, operators `A` with multiplication operators `M`, covariant
derivatives `∇_j`, Clifford coefficients `c j`, and a density square root `σ`. -/
structure CliffordModuleDerivationData (F A : Type*) [CommRing F] [Algebra ℂ F] [Ring A]
    (d : ℕ) where
  /-- multiplication operators -/
  M : F →+* A
  /-- coordinate derivations `∂_j` on scalar functions -/
  der : Fin d → Derivation ℂ F F
  /-- covariant derivatives `∇_j = ∂_j + Ω_j` -/
  cov : Fin d → A
  /-- Clifford coefficients `c^j` -/
  c : Fin d → A
  /-- the density square root `σ = ρ^{1/2}`, invertible -/
  σ : Fˣ
  /-- `[∇_j, M_f] = M_{∂_j f}` -/
  covariant_mul : ∀ j f, cov j * M f = M f * cov j + M (der j f)
  /-- Clifford coefficients commute with scalar multiplication operators -/
  clifford_comm : ∀ j f, c j * M f = M f * c j
  /-- the contracted metric-compatibility identity
  `Σ_j (∂_j c^j + [Ω_j, c^j] + c^j ∂_j log ρ) = 0` with `ρ = σ²` -/
  contracted : ∑ j, (cov j * c j - c j * cov j) =
    -∑ j, c j * M ((((σ * σ)⁻¹ : Fˣ) : F) * der j ((σ * σ : Fˣ) : F))

namespace CliffordModuleDerivationData

noncomputable section

variable (D : CliffordModuleDerivationData F A d)

/-- The density `ρ = σ²`. -/
def ρ : Fˣ := D.σ * D.σ

/-- The (unnormalised) geometric Dirac operator `Σ_j c^j ∇_j`. -/
def diracCore : A := ∑ j, D.c j * D.cov j

/-- The geometric Dirac operator `D_g = -i Σ_j c^j ∇_j` of `eq:supp-geometric-dirac`. -/
def dirac : A := (-Complex.I) • D.diracCore

/-- The density-symmetric operator `-(i/2) Σ_j (c^j ∇_j + ∇_j c^j)`. -/
def densitySymmetric : A := (-(Complex.I / 2)) • ∑ j, (D.c j * D.cov j + D.cov j * D.c j)

omit [Algebra ℂ A] in
/-- `∂_j log ρ = 2 σ⁻¹ ∂_j σ` for `ρ = σ²`. -/
theorem log_density_derivative (j : Fin d) :
    ((D.ρ⁻¹ : Fˣ) : F) * D.der j ((D.ρ : Fˣ) : F) =
      2 * (((D.σ⁻¹ : Fˣ) : F) * D.der j ((D.σ : Fˣ) : F)) := by
  unfold ρ
  rw [mul_inv, Units.val_mul, Units.val_mul, Derivation.leibniz]
  try simp only [smul_eq_mul]
  have hinv : ((D.σ⁻¹ : Fˣ) : F) * ((D.σ : Fˣ) : F) = 1 := D.σ.inv_mul
  linear_combination (2 * ((D.σ⁻¹ : Fˣ) : F) * D.der j ((D.σ : Fˣ) : F)) * hinv

omit [Algebra ℂ A] in
/-- `σ ∂_j(σ⁻¹) = -σ⁻¹ ∂_j σ`. -/
theorem density_sqrt_inv_derivative (j : Fin d) :
    ((D.σ : Fˣ) : F) * D.der j ((D.σ⁻¹ : Fˣ) : F) =
      -(((D.σ⁻¹ : Fˣ) : F) * D.der j ((D.σ : Fˣ) : F)) := by
  have h := D.der j |>.leibniz_of_mul_eq_one (a := ((D.σ : Fˣ) : F)) (b := ((D.σ⁻¹ : Fˣ) : F))
    D.σ.mul_inv
  try simp only [smul_eq_mul] at h
  have hinv : ((D.σ⁻¹ : Fˣ) : F) * ((D.σ : Fˣ) : F) = 1 := D.σ.inv_mul
  linear_combination ((D.σ⁻¹ : Fˣ) : F) * h -
    (((D.σ : Fˣ) : F) * D.der j ((D.σ⁻¹ : Fˣ) : F)) * hinv

omit [Algebra ℂ A] in
/-- Conjugating one term: `M_σ c^j ∇_j M_σ⁻¹ = c^j ∇_j - c^j M_{σ⁻¹ ∂_j σ}`. -/
theorem conj_term (j : Fin d) :
    D.M ((D.σ : Fˣ) : F) * (D.c j * D.cov j) * D.M ((D.σ⁻¹ : Fˣ) : F) =
      D.c j * D.cov j - D.c j * D.M (((D.σ⁻¹ : Fˣ) : F) * D.der j ((D.σ : Fˣ) : F)) := by
  have h1 : D.cov j * D.M ((D.σ⁻¹ : Fˣ) : F) = D.M ((D.σ⁻¹ : Fˣ) : F) * D.cov j + D.M (D.der j ((D.σ⁻¹ : Fˣ) : F)) :=
    D.covariant_mul j _
  have hσ : D.M ((D.σ : Fˣ) : F) * D.M ((D.σ⁻¹ : Fˣ) : F) = 1 := by
    rw [← map_mul, D.σ.mul_inv, map_one]
  have hc := D.clifford_comm j ((D.σ : Fˣ) : F)
  calc D.M ((D.σ : Fˣ) : F) * (D.c j * D.cov j) * D.M ((D.σ⁻¹ : Fˣ) : F)
      = D.c j * (D.M ((D.σ : Fˣ) : F) * (D.cov j * D.M ((D.σ⁻¹ : Fˣ) : F))) := by
        rw [← mul_assoc (D.M _) (D.c j), ← hc]
        simp only [mul_assoc]
    _ = D.c j * (D.M ((D.σ : Fˣ) : F) * D.M ((D.σ⁻¹ : Fˣ) : F) * D.cov j + D.M (((D.σ : Fˣ) : F) * D.der j ((D.σ⁻¹ : Fˣ) : F))) := by
        rw [h1, mul_add, ← mul_assoc, map_mul]
    _ = D.c j * D.cov j - D.c j * D.M (((D.σ⁻¹ : Fˣ) : F) * D.der j ((D.σ : Fˣ) : F)) := by
        rw [hσ, one_mul, density_sqrt_inv_derivative, map_neg, mul_add, mul_neg, sub_eq_add_neg]

/-- **Scalar-free form of `eq:supp-density-symmetric`.**
`M_σ (Σ_j c^j ∇_j) M_σ⁻¹ = ½ Σ_j (c^j ∇_j + ∇_j c^j)`, written as
`2 M_σ (Σ c^j ∇_j) M_σ⁻¹ = Σ (c^j ∇_j + ∇_j c^j)`. -/
theorem conj_sum_eq :
    (2 : ℂ) • (D.M ((D.σ : Fˣ) : F) * D.diracCore * D.M ((D.σ⁻¹ : Fˣ) : F)) =
      ∑ j, (D.c j * D.cov j + D.cov j * D.c j) := by
  have hcontr := D.contracted
  have hlog : ∀ j, D.M ((((D.σ * D.σ)⁻¹ : Fˣ) : F) * D.der j ((D.σ * D.σ : Fˣ) : F)) =
      (2 : ℂ) • D.M (((D.σ⁻¹ : Fˣ) : F) * D.der j ((D.σ : Fˣ) : F)) := by
    intro j
    have := D.log_density_derivative j
    unfold ρ at this
    rw [this, map_mul, map_ofNat, two_smul, two_mul]
  have hexp : D.M ((D.σ : Fˣ) : F) * D.diracCore * D.M ((D.σ⁻¹ : Fˣ) : F) =
      ∑ j, (D.c j * D.cov j - D.c j * D.M (((D.σ⁻¹ : Fˣ) : F) * D.der j ((D.σ : Fˣ) : F))) := by
    unfold diracCore
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => D.conj_term j
  have hsum : ∑ j, (D.c j * D.cov j + D.cov j * D.c j) =
      (2 : ℂ) • ∑ j, D.c j * D.cov j + ∑ j, (D.cov j * D.c j - D.c j * D.cov j) := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [two_smul]
    abel
  rw [hexp, hsum, hcontr, Finset.sum_sub_distrib, smul_sub, Finset.smul_sum, Finset.smul_sum]
  simp only [hlog, mul_smul_comm]
  rw [← Finset.smul_sum, ← Finset.smul_sum, sub_eq_add_neg]

/-- **`eq:supp-density-symmetric`.** `U_ρ D_g U_ρ⁻¹ = -(i/2) Σ_j (M_{c^j} ∇_j + ∇_j M_{c^j})`
with `U_ρ = M_{ρ^{1/2}} = M_σ`. -/
theorem densitySymmetric_identity :
    D.M ((D.σ : Fˣ) : F) * D.dirac * D.M ((D.σ⁻¹ : Fˣ) : F) = D.densitySymmetric := by
  unfold dirac densitySymmetric
  rw [← D.conj_sum_eq, smul_smul, mul_smul_comm, smul_mul_assoc]
  congr 1
  ring

end

end CliffordModuleDerivationData

end RenewalGeometry.DensitySymmetricDirac
