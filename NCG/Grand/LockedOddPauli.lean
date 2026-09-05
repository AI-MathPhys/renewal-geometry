/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Source-native incidence factor from the locked odd route
  (`cor:locked-odd-incidence-factor`,
  Gran-Tensor manuscript)

* `locked_odd_incidence_factor`: a shortened cross-support
  coefficient `B` with equal-rank endpoint supports
  (`BᴴB = κP_R`, `BBᴴ = κP_L`, `κ > 0`):
  (i) the polar route `V = κ^{-1/2}B` is a partial isometry
      onto the two endpoint supports
      (`VᴴV = P_R`, `VVᴴ = P_L`);
  (ii) the derived axes `X = V + Vᴴ`, `Y = i(V - Vᴴ)` are
      hermitian;
  (iii) the boxed Pauli closure
      `-(i/2)[X,Y] = VᴴV - VVᴴ = P_R - P_L = Z_e` — the two
      endpoint axes of a shared-edge incidence packet are
      derived from one nonzero odd route and its reversal,
      not additional independent generators.
-/

open Matrix

namespace NCG

/-- `cor:locked-odd-incidence-factor`. -/
theorem locked_odd_incidence_factor {n : Type*} [Fintype n]
    (B PR PL : Matrix n n ℂ) (κ : ℝ) (hκ : 0 < κ)
    (hBB : Bᴴ * B = (κ : ℂ) • PR)
    (hBBH : B * Bᴴ = (κ : ℂ) • PL) :
    -- (i) the normalized route is a partial isometry
    (((Real.sqrt κ : ℂ)⁻¹ • B)ᴴ
        * ((Real.sqrt κ : ℂ)⁻¹ • B) = PR)
    ∧ (((Real.sqrt κ : ℂ)⁻¹ • B)
        * ((Real.sqrt κ : ℂ)⁻¹ • B)ᴴ = PL)
    -- (ii) the derived axes are hermitian
    ∧ (∀ V : Matrix n n ℂ,
        (V + Vᴴ)ᴴ = V + Vᴴ
        ∧ (Complex.I • (V - Vᴴ))ᴴ = Complex.I • (V - Vᴴ))
    -- (iii) the boxed Pauli closure `-(i/2)[X,Y] = Z`
    ∧ (∀ V : Matrix n n ℂ, Vᴴ * V = PR → V * Vᴴ = PL →
        (-(Complex.I/2)) • ((V + Vᴴ)
              * (Complex.I • (V - Vᴴ))
            - (Complex.I • (V - Vᴴ)) * (V + Vᴴ))
          = PR - PL) := by
  have hs : (Real.sqrt κ : ℂ) * (Real.sqrt κ : ℂ)
      = (κ : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt hκ.le
  have hsqrt : (Real.sqrt κ : ℂ)⁻¹
      * (Real.sqrt κ : ℂ)⁻¹ * (κ : ℂ) = 1 := by
    rw [← mul_inv, hs]
    exact inv_mul_cancel₀ (by exact_mod_cast hκ.ne')
  have hstar : ((Real.sqrt κ : ℂ)⁻¹ • B)ᴴ
      = (Real.sqrt κ : ℂ)⁻¹ • Bᴴ := by
    rw [Matrix.conjTranspose_smul]
    congr 1
    rw [star_inv₀]
    congr 1
    exact Complex.conj_ofReal _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hstar, Matrix.smul_mul, Matrix.mul_smul, hBB,
      smul_smul, smul_smul, hsqrt, one_smul]
  · rw [hstar, Matrix.mul_smul, Matrix.smul_mul, hBBH,
      smul_smul, smul_smul, hsqrt, one_smul]
  · intro V
    constructor
    · rw [Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose, add_comm]
    · rw [Matrix.conjTranspose_smul,
        Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose, Complex.star_def,
        Complex.conj_I, neg_smul, smul_sub, smul_sub]
      rw [neg_sub]
  · intro V hVV hVVH
    have hexp : (V + Vᴴ) * (Complex.I • (V - Vᴴ))
        - (Complex.I • (V - Vᴴ)) * (V + Vᴴ)
        = (2 * Complex.I) • (Vᴴ * V - V * Vᴴ) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul,
        Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub,
        Matrix.sub_mul]
      module
    rw [hexp, smul_smul]
    rw [show -(Complex.I/2) * (2 * Complex.I) = 1 from by
      have h := Complex.I_mul_I
      ring_nf
      rw [Complex.I_sq]
      norm_num]
    rw [one_smul, hVV, hVVH]

end NCG
