/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Legendre structure of the emergent matter sector
  (`thm:SMST-matter-Legendre`, Gran-Tensor manuscript)

* `smst_matter_legendre_quadratic`:
  (a) the exact matrix completion of the square behind the
      Legendre transform of the quadratic matter kinetic
      term: for `K ≻ 0` hermitian,
      `PᴴV + VᴴP - VᴴKV
        = PᴴK⁻¹P - (V - K⁻¹P)ᴴK(V - K⁻¹P)`,
      so the supremum over velocities `V` is attained at the
      boxed stationary point `V = K⁻¹P` with value
      `H = PᴴK⁻¹P` (the second summand is a `K`-Gram square,
      nonpositive in the Loewner order by clause (b) of
      `NCG.renormalization_cocycle`);
  (b) the reciprocity certificate `D_P²H = K⁻¹`: a candidate
      inverse-Hessian `A` satisfies the vanishing of the
      two-sided Legendre defect
      `Δ = (AK-1)ᴴ(AK-1) + (KA-1)ᴴ(KA-1) = 0`
      exactly when `A = K⁻¹`.

The passage from the fluctuation action to this quadratic
normal form (moving-frame expansion of the spectral action)
is the manuscript's analytic step; the reciprocity core
`a_r ↔ b_r` is the previously proved
`NCG.matter_legendre_reciprocity` and
`NCG.legendre_kinetic`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- `thm:SMST-matter-Legendre`, quadratic normal form. -/
theorem smst_matter_legendre_quadratic {v w : Type*}
    [Fintype v] [DecidableEq v]
    (K : Matrix v v ℂ) (hK : K.PosDef) :
    -- (a) exact Legendre completion of the square
    (∀ P V : Matrix v w ℂ,
      Pᴴ * V + Vᴴ * P - Vᴴ * K * V
        = Pᴴ * K⁻¹ * P
          - (V - K⁻¹ * P)ᴴ * K * (V - K⁻¹ * P))
    -- (b) reciprocity certificate `D_P²H = K⁻¹`
    ∧ (∀ A : Matrix v v ℂ,
        (A * K - 1)ᴴ * (A * K - 1)
          + (K * A - 1)ᴴ * (K * A - 1) = 0
        ↔ A = K⁻¹) := by
  haveI := hK.isUnit.invertible
  have hKH : Kᴴ = K := hK.isHermitian
  have hKinvH : (K⁻¹)ᴴ = K⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hKH]
  constructor
  · intro P V
    have hKcan : ∀ X : Matrix v w ℂ,
        K * (K⁻¹ * X) = X := by
      intro X
      rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
        Matrix.one_mul]
    have hKcan' : ∀ X : Matrix v w ℂ,
        K⁻¹ * (K * X) = X := by
      intro X
      rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
        Matrix.one_mul]
    simp only [Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, hKinvH,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
      hKcan, hKcan']
    abel
  · intro A
    constructor
    · intro h0
      have hpsd1 :=
        Matrix.posSemidef_conjTranspose_mul_self (A * K - 1)
      have hpsd2 :=
        Matrix.posSemidef_conjTranspose_mul_self (K * A - 1)
      have htr := congrArg Matrix.trace h0
      rw [Matrix.trace_add, Matrix.trace_zero] at htr
      have ht1 : ((A * K - 1)ᴴ * (A * K - 1)).trace = 0 := by
        have hn1 := hpsd1.trace_nonneg
        have hn2 := hpsd2.trace_nonneg
        have hle : ((A * K - 1)ᴴ * (A * K - 1)).trace ≤ 0 := by
          rw [← htr]
          exact le_add_of_nonneg_right hn2
        exact le_antisymm hle hn1
      have hAK :=
        Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht1
      have hAK1 : A * K = 1 := by
        rwa [sub_eq_zero] at hAK
      rw [← Matrix.mul_one A, ← Matrix.mul_inv_of_invertible K,
        ← Matrix.mul_assoc, hAK1, Matrix.one_mul]
    · intro hA
      subst hA
      simp [Matrix.inv_mul_of_invertible,
        Matrix.mul_inv_of_invertible]

end NCG
