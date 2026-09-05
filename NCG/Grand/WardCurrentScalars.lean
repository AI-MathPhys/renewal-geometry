/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Ward-current scalars, provenance inversion, and sign
  information rates
  (`cor:minimal-renewal-Ward-currents`,
  `cor:covariant-provenance-inversion`,
  `cor:SMST-sign-information-rate`,
  Gran-Tensor manuscript)

* `minimal_renewal_ward_currents`: the boxed phase currents
  `J_H = a - (1-a)/4`, `J_P = s - (1-s)/2` vanish jointly
  exactly at the concrete renewal weights `a = 1/5`,
  `s = 1/3`; one scalar Ward coordinate per phase suffices.

* `covariant_provenance_inversion`: the boxed `S₄`-triplet
  Möbius transfer `α = (1-s)ρ/(1-sρ)` inverts exactly to
  `ρ = α/(1-s+sα)`, and at `s = 1/3` to `ρ = 3α/(2+α)`.

* `smst_sign_information_rate`: the boxed rates
  `𝕀_opp = θ𝕀_acc` and `𝕀_time = (4/11)θ𝕀_acc`
  (`E𝒯 = 11/4` mean interarrival), and rarity preserves
  positivity of the Fisher form.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `cor:minimal-renewal-Ward-currents`. -/
theorem minimal_renewal_ward_currents :
    -- the boxed one-scalar Ward coordinates per phase
    (∀ a : ℝ, a - (1 - a) / 4 = (5 * a - 1) / 4)
    ∧ (∀ s : ℝ, s - (1 - s) / 2 = (3 * s - 1) / 2)
    -- the boxed joint vanishing criterion
    ∧ (∀ a s : ℝ,
        (a - (1 - a) / 4 = 0 ∧ s - (1 - s) / 2 = 0)
        ↔ (a = 1 / 5 ∧ s = 1 / 3)) := by
  refine ⟨fun a => by ring, fun s => by ring, fun a s => ?_⟩
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    subst h1
    subst h2
    norm_num

/-- `cor:covariant-provenance-inversion`. -/
theorem covariant_provenance_inversion (s ρ : ℝ)
    (hs : s ≠ 1) (h1 : s * ρ ≠ 1) :
    ∀ α : ℝ, α = (1 - s) * ρ / (1 - s * ρ) →
      -- the boxed exact inverse (polynomial form)
      ρ * (1 - s + s * α) = α
      -- the boxed `s = 1/3` display (polynomial form)
      ∧ (s = 1 / 3 → ρ * (2 + α) = 3 * α) := by
  intro α hα
  have hne : (1 : ℝ) - s * ρ ≠ 0 := by
    intro h
    apply h1
    linarith
  constructor
  · rw [hα]
    have hne' : (1 : ℝ) - ρ * s ≠ 0 := by
      rw [mul_comm]
      exact hne
    field_simp
    ring
  · intro hs3
    subst hs3
    rw [hα]
    have h3 : (3 : ℝ) - ρ ≠ 0 := by
      intro h
      apply h1
      linarith
    field_simp
    ring

/-- `cor:SMST-sign-information-rate`. -/
theorem smst_sign_information_rate {n : Type*} [Finite n]
    (Iacc : Matrix n n ℂ) (θ : ℂ) (hθ : 0 ≤ θ)
    (hI : Iacc.PosSemidef) :
    -- the boxed protected-time rescaling `E𝒯 = 11/4`
    ((11 / 4 : ℂ))⁻¹ • (θ • Iacc)
      = ((4 / 11) * θ) • Iacc
    -- rarity rescales but preserves the Fisher form
    ∧ (θ • Iacc).PosSemidef
    ∧ ((((4 / 11 : ℂ)) * θ) • Iacc).PosSemidef := by
    refine ⟨?_, hI.smul hθ, ?_⟩
    · rw [smul_smul]
      congr 1
      norm_num
    · have h4 : (0 : ℂ) ≤ (4 / 11 : ℂ) := by
        rw [show ((4 : ℂ) / 11) = ((4 / 11 : ℝ) : ℂ) by
          norm_num]
        rw [Complex.zero_le_real]
        norm_num
      have h := (hI.smul hθ).smul h4
      rwa [smul_smul] at h

end NCG
