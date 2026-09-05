/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NativeGenerations

/-!
# Atomic opportunity rigidity and the ordered two-cycle source
  (`thm:atomic-opportunity-rigidity` and
  `thm:ordered-opportunity-cycle-source`,
  Gran-Tensor manuscript)

* `atomic_opportunity_rigidity`:
  (i) the forced counting `|Ω| = 4`: sourcewise-uniform
      atoms of weight `1/5` (resp. `1/3`) exhaust the `H`
      (resp. `P`) opportunity mass `4/5` (resp. `2/3`) in
      exactly `4` (resp. `2`) atoms;
  (ii) the boxed contrast Gram `G_Ω = ¼·P_rel`: the uniform
      direction is null and every relative contrast is an
      exact `1/4`-eigenvector (rank three,
      `λ⁺_min = 1/4`);
  (iii) the `S₄` relabelling action: permutation matrices fix
      the uniform direction and have determinant
      `sgn σ` — the boxed orientation twist
      `det(σ|V_rel) = sgn σ` on the relative carrier.

* `ordered_opportunity_cycle_source`:
  (i) the kernel of the ordered-pair boundary is exactly the
      harmonic model: for antisymmetric `f`,
      `∂f = 0 ↔ f ∈ K4Carrier ≅ H₁(K₄;ℂ)`;
  (ii) `∂∘∂* = 4` on mean-zero potentials;
  (iii) the cycle projector lands in the kernel:
      `∂(f - ¼∂*∂f) = 0` for antisymmetric `f`;
  (iv) the boxed exact sequence as the rank count
      `dim H₁(K₄) + dim V_rel = 3 + 3 = 6 = dim 𝒟⁻`.
-/

open Matrix

namespace NCG

/-- `thm:atomic-opportunity-rigidity`. -/
theorem atomic_opportunity_rigidity :
    -- (i) the forced counting |Ω| = 4
    ((1 - (1/5 : ℚ)) / (1/5) = 4 ∧ (1 - (1/3 : ℚ)) / (1/3) = 2)
    -- (ii) the contrast Gram G_Ω = ¼·P_rel
    ∧ ((Matrix.of fun i j : Fin 4 =>
        (1/4 : ℚ) * ((if i = j then 1 else 0) - 1/4))
          *ᵥ (fun _ => 1) = 0)
    ∧ (∀ v : Fin 4 → ℚ, (∑ i, v i = 0) →
        (Matrix.of fun i j : Fin 4 =>
          (1/4 : ℚ) * ((if i = j then 1 else 0) - 1/4))
            *ᵥ v = (1/4 : ℚ) • v)
    -- (iii) the S₄ relabelling twist
    ∧ (∀ σ : Equiv.Perm (Fin 4),
        (σ.permMatrix ℚ).det = (Equiv.Perm.sign σ : ℚ))
    ∧ (∀ σ : Equiv.Perm (Fin 4),
        σ.permMatrix ℚ *ᵥ (fun _ => (1 : ℚ))
          = fun _ => 1) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;>
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
        norm_num
  · intro v hv
    funext i
    have h1 : ∀ j : Fin 4,
        (1/4 : ℚ) * ((if i = j then 1 else 0) - 1/4) * v j
        = (if i = j then (1/4 : ℚ) * v j else 0)
          - (1/16) * v j := by
      intro j
      by_cases h : i = j
      · rw [if_pos h, if_pos h]
        ring
      · rw [if_neg h, if_neg h]
        ring
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul, h1]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq,
      ← Finset.mul_sum, hv, mul_zero, sub_zero]
    simp
  · intro σ
    exact Matrix.det_permutation σ
  · intro σ
    funext i
    simp [Equiv.Perm.permMatrix, Matrix.mulVec, dotProduct]

/-- `thm:ordered-opportunity-cycle-source`. -/
theorem ordered_opportunity_cycle_source :
    -- (i) kernel of the boundary = the harmonic model
    (∀ f : Fin 4 → Fin 4 → ℂ, (∀ i j, f j i = -f i j) →
      (k4Bd f = 0 ↔ f ∈ K4Carrier))
    -- (ii) `∂∘∂* = 4` on mean-zero potentials
    ∧ (∀ g : Fin 4 → ℂ, (∑ i, g i = 0) →
        k4Bd (k4Cobd g) = (4 : ℂ) • g)
    -- (iii) the cycle projector lands in the kernel
    ∧ (∀ f : Fin 4 → Fin 4 → ℂ, (∀ i j, f j i = -f i j) →
        k4Bd (fun i j => f i j
          - (4 : ℂ)⁻¹ * k4Cobd (k4Bd f) i j) = 0)
    -- (iv) the boxed exact rank count 3 + 3 = 6
    ∧ Module.finrank ℂ K4Carrier
        + Module.finrank ℂ meanZero = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    constructor
    · intro h0
      exact ⟨hf, fun i => by
        have h := congrFun h0 i
        simpa [k4Bd] using h⟩
    · intro hmem
      funext i
      simpa [k4Bd] using hmem.2 i
  · intro g hg
    have hgExp : g 0 + g 1 + g 2 + g 3 = 0 := by
      simpa [Fin.sum_univ_four] using hg
    funext i
    simp only [k4Bd, k4Cobd, Fin.sum_univ_four,
      Pi.smul_apply, smul_eq_mul]
    linear_combination (-1 : ℂ) * hgExp
  · intro f hf
    have hSexp : f 0 0 + f 0 1 + f 0 2 + f 0 3 + f 1 0
        + f 1 1 + f 1 2 + f 1 3 + f 2 0 + f 2 1 + f 2 2
        + f 2 3 + f 3 0 + f 3 1 + f 3 2 + f 3 3 = 0 := by
      linear_combination hf 0 1 + hf 0 2 + hf 0 3 + hf 1 2
        + hf 1 3 + hf 2 3 + hf 0 0 / 2 + hf 1 1 / 2
        + hf 2 2 / 2 + hf 3 3 / 2
    funext i
    simp only [k4Bd, k4Cobd, Pi.zero_apply,
      Fin.sum_univ_four]
    linear_combination ((4 : ℂ)⁻¹) * hSexp
  · rw [finrank_K4Carrier,
      (smst_record_native_generations).2.2.2.1]

end NCG
