import NCG.Grand.SchurAssociativity

/-!
# Exact EASY batch 31: matrix-level Schur associativity

The existing theorem proves the solve characterization on every exterior
vector.  This file records the corresponding literal matrix identity.
-/

namespace NCG

/-- `thm:Schur-associativity`, boxed matrix equality.  The right-hand side is
the exterior response obtained by solving the two internal Euler equations
simultaneously; it equals the complement obtained by eliminating `I₁` and then
`I₂`. -/
theorem schur_associativity_matrix {E I1 I2 : Type*}
    [Fintype I1] [Fintype I2] [DecidableEq I1] [DecidableEq I2]
    (A : Matrix E E ℂ) (B1 : Matrix E I1 ℂ) (B2 : Matrix E I2 ℂ)
    (C1 : Matrix I1 E ℂ) (C2 : Matrix I2 E ℂ)
    (D11 : Matrix I1 I1 ℂ) (D12 : Matrix I1 I2 ℂ)
    (D21 : Matrix I2 I1 ℂ) (D22 : Matrix I2 I2 ℂ)
    [Invertible D11]
    [Invertible (D22 - D21 * D11⁻¹ * D12)] :
    (A - B1 * D11⁻¹ * C1)
        - (B2 - B1 * D11⁻¹ * D12)
          * (D22 - D21 * D11⁻¹ * D12)⁻¹
          * (C2 - D21 * D11⁻¹ * C1)
      = A
        + B1 * (D11⁻¹ * D12
            * (D22 - D21 * D11⁻¹ * D12)⁻¹
            * (C2 - D21 * D11⁻¹ * C1) - D11⁻¹ * C1)
        - B2 * (D22 - D21 * D11⁻¹ * D12)⁻¹
            * (C2 - D21 * D11⁻¹ * C1) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  module

end NCG
