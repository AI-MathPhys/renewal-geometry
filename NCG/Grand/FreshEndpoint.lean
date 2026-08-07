/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectatorProduct

/-!
# Fresh predictive endpoint with retained private information
  (`thm:fresh-endpoint-retained-record`, Gran-Tensor manuscript)

* `fresh_endpoint_retained_record`: the completed-private reset
  channel writes the maximally mixed hub independently of the
  old private record (trace preservation and the boxed hub
  marginal `I₂/2`), the concrete retained private records have
  overlap `⟨r₀,r₁⟩ = 1/5`, and the Helstrom success probability
  is exactly `(1+√(1-|⟨r₀,r₁⟩|²))/2 = (5+2√6)/10`.

Rendering disclosed: the Helstrom optimality of
`(1+‖ρ₀-ρ₁‖₁/2)/2` for equal priors is the cited standard
detection bound; here the boxed channel form, the marginal
independence, the overlap of the retained records, and the
boxed value are proved.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- The completed-private reset channel. -/
noncomputable def hubChannel (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    ⊗ₖ (ρ 0 0 • !![1, 0; 0, 0] + ρ 1 1 • !![0, 0; 0, 1])

/-- The two retained private records. -/
noncomputable def hubR0 : Fin 2 → ℂ := ![1, 0]

/-- The second retained private record (overlap `1/5`). -/
noncomputable def hubR1 : Fin 2 → ℂ :=
  ![(1 / 5 : ℂ), ((2 * Real.sqrt 6 / 5 : ℝ) : ℂ)]

/-- `thm:fresh-endpoint-retained-record`. -/
theorem fresh_endpoint_retained_record :
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      (hubChannel ρ).trace = ρ.trace)
    ∧ (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
        partialTraceRight (hubChannel ρ)
          = ρ.trace • ((2 : ℂ)⁻¹ • 1))
    ∧ (star hubR0 ⬝ᵥ hubR0 = 1 ∧ star hubR1 ⬝ᵥ hubR1 = 1
        ∧ star hubR0 ⬝ᵥ hubR1 = 1 / 5)
    ∧ ((1 / 2 : ℝ) * (1 + Real.sqrt (1 - (1 / 5) ^ 2))
        = (5 + 2 * Real.sqrt 6) / 10) := by
  have h6 : Real.sqrt 6 ^ 2 = 6 :=
    Real.sq_sqrt (by norm_num)
  have hcollapse : ∀ (A : Matrix (Fin 2) (Fin 2) ℂ)
      (B : Matrix (Fin 2) (Fin 2) ℂ),
      partialTraceRight (A ⊗ₖ B) = B.trace • A :=
    (renewal_spectator_product LinearMap.id LinearMap.id
      (fun _ => rfl)).1
  have hinner : ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      (ρ 0 0 • (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
        + ρ 1 1 • !![0, 0; 0, 1]).trace = ρ.trace := by
    intro ρ
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_fin_two]
    simp [Matrix.trace_fin_two]
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro ρ
    unfold hubChannel
    rw [Matrix.trace_kronecker, hinner, Matrix.trace_smul,
      Matrix.trace_one]
    simp
  · intro ρ
    unfold hubChannel
    rw [hcollapse, hinner]
  · simp [hubR0, dotProduct, Fin.sum_univ_two]
  · simp only [hubR1, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.star_apply, RCLike.star_def]
    rw [show ((starRingEnd ℂ) (1 / 5 : ℂ)) = 1 / 5 from by
      rw [show (1 / 5 : ℂ) = ((1 / 5 : ℝ) : ℂ) from by
        norm_num]
      exact Complex.conj_ofReal _]
    rw [show ((starRingEnd ℂ) ((2 * Real.sqrt 6 / 5 : ℝ) : ℂ))
        = ((2 * Real.sqrt 6 / 5 : ℝ) : ℂ) from
      Complex.conj_ofReal _]
    rw [show (((2 * Real.sqrt 6 / 5 : ℝ) : ℂ)
        * ((2 * Real.sqrt 6 / 5 : ℝ) : ℂ))
        = (((2 * Real.sqrt 6 / 5) ^ 2 : ℝ) : ℂ) from by
      push_cast
      ring]
    rw [show ((2 * Real.sqrt 6 / 5) ^ 2 : ℝ) = 24 / 25 from by
      nlinarith [h6]]
    norm_num
  · simp [hubR0, hubR1, dotProduct, Fin.sum_univ_two]
  · have h1 : (1 : ℝ) - (1 / 5) ^ 2
        = (2 * Real.sqrt 6 / 5) ^ 2 := by
      nlinarith [h6]
    rw [h1, Real.sqrt_sq (by positivity)]
    ring

end NCG
