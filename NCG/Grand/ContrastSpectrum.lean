/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Contrast spectrum and the sharp-record boundary
  (`cor:locked-opportunity-contrast-spectrum`,
  Gran-Tensor manuscript)

* `locked_opportunity_contrast_spectrum`: the opportunity
  coefficient metric `M_θ = θ(I-P_c) + (12-11θ)P_c` on
  `ℂ²⁴` (`P_c` the uniform-direction projection, entrywise
  `1/24`):
  (i) `P_c` is the rank-one uniform projection
      (`P_c² = P_c`);
  (ii) every coefficient contrast orthogonal to the uniform
      direction has exact metric eigenvalue `θ`
      (`M_θ·v = θ·v` when `∑v = 0`);
  (iii) the explicit inverse
      `M_θ⁻¹ = θ⁻¹(I-P_c) + (12-11θ)⁻¹P_c`;
  (iv) the minimal-environment Parseval overlaps are the
      boxed `⟨f_j,f_k⟩ = θ·(M_θ⁻¹)_{jk}
      = -(1-θ)/(2(12-11θ))` for `j ≠ k` — the accepted
      effects are not orthogonal, so the sharp Naimark record
      is an abelian outcome algebra, not six dynamical edge
      qubits.
-/

open Matrix

namespace NCG

/-- The all-ones matrix on the 24 accepted labels. -/
def allOnes24 : Matrix (Fin 24) (Fin 24) ℂ :=
  Matrix.of fun _ _ => 1

/-- `cor:locked-opportunity-contrast-spectrum`. -/
theorem locked_opportunity_contrast_spectrum (θ : ℂ)
    (hθ : θ ≠ 0) (h12 : (12 : ℂ) - 11 * θ ≠ 0) :
    -- (i) the uniform projection
    ((24 : ℂ)⁻¹ • allOnes24) * ((24 : ℂ)⁻¹ • allOnes24)
      = (24 : ℂ)⁻¹ • allOnes24
    -- (ii) contrasts have exact metric θ
    ∧ (∀ v : Fin 24 → ℂ, (∑ i, v i = 0) →
        (θ • (1 - (24 : ℂ)⁻¹ • allOnes24)
          + ((12 : ℂ) - 11 * θ) • ((24 : ℂ)⁻¹ • allOnes24))
          *ᵥ v = θ • v)
    -- (iii) the explicit inverse
    ∧ (θ⁻¹ • (1 - (24 : ℂ)⁻¹ • allOnes24)
        + ((12 : ℂ) - 11 * θ)⁻¹ • ((24 : ℂ)⁻¹ • allOnes24))
      * (θ • (1 - (24 : ℂ)⁻¹ • allOnes24)
        + ((12 : ℂ) - 11 * θ) • ((24 : ℂ)⁻¹ • allOnes24))
      = 1
    -- (iv) the boxed nonorthogonal Parseval overlaps
    ∧ (∀ j k : Fin 24, j ≠ k →
        θ * (θ⁻¹ • (1 - (24 : ℂ)⁻¹ • allOnes24)
          + ((12 : ℂ) - 11 * θ)⁻¹
            • ((24 : ℂ)⁻¹ • allOnes24)) j k
          = -(1 - θ) / (2 * ((12 : ℂ) - 11 * θ))) := by
  have hJJ : allOnes24 * allOnes24 = (24 : ℂ) • allOnes24 := by
    ext i j
    simp [allOnes24, Matrix.mul_apply]
  have hPP : ((24 : ℂ)⁻¹ • allOnes24)
      * ((24 : ℂ)⁻¹ • allOnes24)
      = (24 : ℂ)⁻¹ • allOnes24 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hJJ, smul_smul,
      smul_smul]
    norm_num
  have hJv : ∀ v : Fin 24 → ℂ, (∑ i, v i = 0) →
      allOnes24 *ᵥ v = 0 := by
    intro v hv
    funext i
    simp [allOnes24, Matrix.mulVec, dotProduct, hv]
  refine ⟨hPP, ?_, ?_, ?_⟩
  · intro v hv
    have hPv : ((24 : ℂ)⁻¹ • allOnes24) *ᵥ v = 0 := by
      rw [Matrix.smul_mulVec, hJv v hv, smul_zero]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.sub_mulVec, hPv,
      Matrix.one_mulVec]
    simp
  · generalize hPdef : (24 : ℂ)⁻¹ • allOnes24 = P
    rw [hPdef] at hPP
    have hQP : ((1 : Matrix (Fin 24) (Fin 24) ℂ) - P)
        * P = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
    have hPQ : P * ((1 : Matrix (Fin 24) (Fin 24) ℂ)
        - P) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
    have hQQ : ((1 : Matrix (Fin 24) (Fin 24) ℂ) - P)
        * ((1 : Matrix (Fin 24) (Fin 24) ℂ) - P)
        = 1 - P := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
        Matrix.mul_one, hPP]
      abel
    calc (θ⁻¹ • (1 - P) + ((12 : ℂ) - 11 * θ)⁻¹ • P)
          * (θ • (1 - P) + ((12 : ℂ) - 11 * θ) • P)
        = (θ⁻¹ * θ) • ((1 - P) * (1 - P))
          + (θ⁻¹ * ((12 : ℂ) - 11 * θ)) • ((1 - P) * P)
          + ((((12 : ℂ) - 11 * θ)⁻¹ * θ) • (P * (1 - P))
            + (((12 : ℂ) - 11 * θ)⁻¹
                * ((12 : ℂ) - 11 * θ)) • (P * P)) := by
          simp only [Matrix.add_mul, Matrix.mul_add,
            Matrix.smul_mul, Matrix.mul_smul]
          module
      _ = 1 := by
          rw [hQP, hPQ, hQQ, hPP,
            inv_mul_cancel₀ hθ, inv_mul_cancel₀ h12,
            one_smul, one_smul, smul_zero, smul_zero,
            add_zero, zero_add, sub_add_cancel]
  · intro j k hjk
    simp only [Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply_ne hjk, allOnes24,
      Matrix.of_apply, smul_eq_mul]
    have h12' : (12 : ℂ) - θ * 11 ≠ 0 := by
      rwa [mul_comm] at h12
    field_simp [h12']
    ring

end NCG
