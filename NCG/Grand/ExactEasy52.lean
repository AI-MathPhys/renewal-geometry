/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.K4Opportunity

/-!
# Exact EASY 52: ordered opportunity cycle source

The existing finite `K₄` calculation identifies the boundary kernel, proves
surjectivity onto the relative triplet, and gives the Hodge projector formula.
Here the projector and the uniform conditional Gram are named explicitly and
the missing normalization/orientation conclusions are assembled.
-/

open Matrix

namespace NCG

/-- The cycle projector `I - ¼ ∂*∂` on ordered antisymmetric pairs. -/
noncomputable def k4CycleProjection (f : Fin 4 → Fin 4 → ℂ) :
    Fin 4 → Fin 4 → ℂ :=
  fun i j => f i j - (4 : ℂ)⁻¹ * k4Cobd (k4Bd f) i j

/-- Uniformity of the twelve ordered distinct pairs gives the compressed
conditional cycle Gram `P_cyc / 12`. -/
noncomputable def k4ConditionalCycleGram (f : Fin 4 → Fin 4 → ℂ) :
    Fin 4 → Fin 4 → ℂ :=
  (12 : ℂ)⁻¹ • k4CycleProjection f

/-- Exact normalization and orientation packet for the ordered two-cycle
source.  On antisymmetric edges the projector lands in `H₁(K₄)` and is
idempotent; on the harmonic carrier it is the identity, so the conditional
Gram has exact positive margin `1/12`.  The carrier is the same standard
triplet as the relative opportunity source, whose determinant is the sign. -/
theorem ordered_opportunity_cycle_source_exact :
    (∀ f : Fin 4 → Fin 4 → ℂ, (∀ i j, f j i = -f i j) →
      k4CycleProjection f ∈ K4Carrier
      ∧ k4CycleProjection (k4CycleProjection f) = k4CycleProjection f)
    ∧ (∀ c : K4Carrier,
        k4CycleProjection c = c
        ∧ k4ConditionalCycleGram c = (12 : ℂ)⁻¹ • (c : Fin 4 → Fin 4 → ℂ))
    ∧ (0 : ℝ) < 1 / 12
    ∧ Nonempty (K4Carrier ≃ₗ[ℂ] meanZero)
    ∧ (∀ σ : Equiv.Perm (Fin 4),
        (σ.permMatrix ℚ).det = (Equiv.Perm.sign σ : ℚ)) := by
  have hbase := ordered_opportunity_cycle_source
  refine ⟨?_, ?_, by norm_num, ?_, atomic_opportunity_rigidity.2.2.2.1⟩
  · intro f hf
    have hanti : ∀ i j, k4CycleProjection f j i
        = -k4CycleProjection f i j := by
      intro i j
      simp only [k4CycleProjection, k4Cobd]
      rw [hf j i]
      ring
    have hbd : k4Bd (k4CycleProjection f) = 0 := by
      change k4Bd (fun i j => f i j
        - (4 : ℂ)⁻¹ * k4Cobd (k4Bd f) i j) = 0
      exact hbase.2.2.1 f hf
    have hmem : k4CycleProjection f ∈ K4Carrier :=
      (hbase.1 (k4CycleProjection f) hanti).mp hbd
    refine ⟨hmem, ?_⟩
    funext i j
    simp only [k4CycleProjection, hbd, k4Cobd, Pi.zero_apply,
      sub_self, mul_zero, sub_zero]
  · intro c
    have hbd : k4Bd (c : Fin 4 → Fin 4 → ℂ) = 0 := by
      funext i
      simpa only [k4Bd, Pi.zero_apply] using c.2.2 i
    have hfix : k4CycleProjection c = c := by
      funext i j
      simp [k4CycleProjection, hbd, k4Cobd]
    refine ⟨hfix, ?_⟩
    simp only [k4ConditionalCycleGram, hfix]
  · obtain ⟨e⟩ := smst_record_native_generations.2.2.2.2
    exact ⟨e.symm⟩

end NCG
