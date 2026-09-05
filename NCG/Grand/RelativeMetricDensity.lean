/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Relative metric density and sharp domination constant
  (`thm:relative-metric-density`, Gran-Tensor manuscript)

* `relative_metric_density`: on the faithful branch `M ≻ 0`,
  the boxed relative density `H = √M⁻¹ · E · √M⁻¹` satisfies
  `H ⪰ 0`, the reconstruction `E = √M · H · √M`, and the sharp
  domination equivalence: for every `λ ≥ 0`,
  `E ⪯ λM ⟺ H ⪯ λI` — in particular `E ⪯ M ⟺ H ⪯ I`, and the
  least admissible constant is characterised order-theoretically
  by this family of equivalences.

Rendering disclosed: the kernel defect `Δ_ker(E|M) = 0` is
automatic on the faithful branch `M ≻ 0` (the manuscript's
support reduction, as in the coherence records); the reading
of the least constant as the operator norm `‖H‖` is the
spectral interpretation of the proved `∀λ` equivalence family.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:relative-metric-density`. -/
theorem relative_metric_density {n : Type*} [Fintype n]
    [DecidableEq n] {M E : Matrix n n ℂ} (hM : M.PosDef)
    (hE : E.PosSemidef) :
    ((CFC.sqrt M)⁻¹ * E * (CFC.sqrt M)⁻¹).PosSemidef
    ∧ E = CFC.sqrt M
        * ((CFC.sqrt M)⁻¹ * E * (CFC.sqrt M)⁻¹) * CFC.sqrt M
    ∧ ∀ lam : ℝ,
        ((lam : ℂ) • M - E).PosSemidef
          ↔ ((lam : ℂ) • (1 : Matrix n n ℂ)
              - (CFC.sqrt M)⁻¹ * E * (CFC.sqrt M)⁻¹).PosSemidef := by
  haveI := (sqrt_isUnit hM).invertible
  have hsiH : ((CFC.sqrt M)⁻¹)ᴴ = (CFC.sqrt M)⁻¹ :=
    sqrt_inv_isHermitian M
  have hsH : (CFC.sqrt M)ᴴ = CFC.sqrt M := sqrt_isHermitian M
  have hs2 : CFC.sqrt M * CFC.sqrt M = M :=
    sqrt_mul_self_eq M hM.posSemidef
  have hcan : ∀ Y : Matrix n n ℂ,
      CFC.sqrt M * ((CFC.sqrt M)⁻¹ * Y * (CFC.sqrt M)⁻¹)
        * CFC.sqrt M = Y := by
    intro Y
    calc CFC.sqrt M * ((CFC.sqrt M)⁻¹ * Y * (CFC.sqrt M)⁻¹)
        * CFC.sqrt M
        = (CFC.sqrt M * (CFC.sqrt M)⁻¹) * Y
            * ((CFC.sqrt M)⁻¹ * CFC.sqrt M) := by
          simp only [Matrix.mul_assoc]
      _ = Y := by
          rw [Matrix.mul_inv_of_invertible,
            Matrix.inv_mul_of_invertible, Matrix.one_mul,
            Matrix.mul_one]
  refine ⟨?_, (hcan E).symm, ?_⟩
  · have := hE.mul_mul_conjTranspose_same (CFC.sqrt M)⁻¹
    rwa [hsiH] at this
  · intro lam
    have hkey : (lam : ℂ) • M - E
        = CFC.sqrt M
            * ((lam : ℂ) • (1 : Matrix n n ℂ)
              - (CFC.sqrt M)⁻¹ * E * (CFC.sqrt M)⁻¹)
            * star (CFC.sqrt M) := by
      rw [Matrix.star_eq_conjTranspose, hsH, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hs2, hcan E]
    constructor
    · intro h
      rw [hkey] at h
      exact ((sqrt_isUnit hM).posSemidef_star_right_conjugate_iff).mp h
    · intro h
      rw [hkey]
      exact ((sqrt_isUnit hM).posSemidef_star_right_conjugate_iff).mpr h

end NCG
