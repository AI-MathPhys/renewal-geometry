/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CliffordGenerates

/-!
# Minimal spatially nondegenerate external dimension
  (`thm:master-dimension-status-v036`, flagship manuscript)

The selected external factor contains a canonical
`M₄(ℂ) ≅ Cl₁,₃(ℂ)` with one anti-Hermitian negative-square
generator and three Hermitian positive-square generators — all
proved on the concrete carrier:

* `lorentzGamma0_antihermitian` / `lorentzGamma0_negative_square`:
  the timelike generator `γ₀ = iΓ₀` is anti-Hermitian with
  `γ₀² = -1`;
* `spatial_positive_square`: the three spatial generators are
  Hermitian with square `+1`;
* `lorentz_anticommute`: the Lorentz generator anticommutes with
  each spatial generator;
* `lorentz_clifford_generates`: the signed system
  `{γ₀, Γ₁, Γ₂, Γ₃}` still generates the full matrix factor
  `M₄(ℂ)` (via the proved `gamma_generates`).

Rendering disclosed: the two entrance branches (loaded clock
copies with physical Pauli Reads, and the nondegenerate finite
symplectic revision module with the rank-three minimality
clause) are the manuscript's Store–control layer; the Clifford
signature and generation content is proved here.
-/

open Matrix NCG.CommonOrigin

namespace NCG

/-- The Lorentz-signature timelike generator `γ₀ = iΓ₀`. -/
noncomputable def lorentzGamma0 :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Complex.I • NCG.CommonOrigin.gamma 0

/-- `γ₀` is anti-Hermitian. -/
theorem lorentzGamma0_antihermitian :
    lorentzGamma0ᴴ = -lorentzGamma0 := by
  rw [lorentzGamma0, Matrix.conjTranspose_smul, gamma_herm,
    Complex.star_def, Complex.conj_I, neg_smul]

/-- `γ₀` has negative square: `γ₀² = -1`. -/
theorem lorentzGamma0_negative_square :
    lorentzGamma0 * lorentzGamma0 = -1 := by
  rw [lorentzGamma0, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Complex.I_mul_I, gamma_sq, neg_smul, one_smul]

/-- The three spatial generators are Hermitian with positive
square. -/
theorem spatial_positive_square (a : Fin 4) :
    (gamma a)ᴴ = gamma a ∧ gamma a * gamma a = 1 :=
  ⟨gamma_herm a, gamma_sq a⟩

/-- The Lorentz generator anticommutes with each spatial
generator. -/
theorem lorentz_anticommute (a : Fin 4) (ha : a ≠ 0) :
    lorentzGamma0 * gamma a = -(gamma a * lorentzGamma0) := by
  rw [lorentzGamma0, Matrix.smul_mul, Matrix.mul_smul,
    gamma_anticomm 0 a (Ne.symm ha), smul_neg]

/-- The signed Lorentz system `{γ₀, Γ₁, Γ₂, Γ₃}` generates the
full matrix factor `M₄(ℂ)`. -/
theorem lorentz_clifford_generates :
    Algebra.adjoin ℂ
      ({lorentzGamma0, gamma 1, gamma 2, gamma 3} :
        Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = ⊤ := by
  rw [eq_top_iff, ← gamma_generates]
  apply Algebra.adjoin_le
  rintro X ⟨μ, rfl⟩
  have hg0 : gamma 0 ∈ Algebra.adjoin ℂ
      ({lorentzGamma0, gamma 1, gamma 2, gamma 3} :
        Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := by
    have h0 : gamma 0 = (-Complex.I) • lorentzGamma0 := by
      rw [lorentzGamma0, smul_smul]
      rw [show (-Complex.I) * Complex.I = 1 by
        rw [neg_mul, Complex.I_mul_I, neg_neg]]
      rw [one_smul]
    rw [h0]
    exact Subalgebra.smul_mem _
      (Algebra.subset_adjoin (by simp)) _
  fin_cases μ
  · exact hg0
  · exact Algebra.subset_adjoin (by simp)
  · exact Algebra.subset_adjoin (by simp)
  · exact Algebra.subset_adjoin (by simp)

end NCG
