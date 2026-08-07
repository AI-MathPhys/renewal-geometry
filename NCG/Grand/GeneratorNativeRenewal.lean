/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Generator-native score–dwell renewal certificate
  (`thm:generator-native-renewal`, Gran-Tensor manuscript)

* `generator_native_renewal`: the three proved clauses of the
  certificate — (1) the fresh-collision branch effects
  `E_± = ½I` sum to the identity and give Born probability
  `½` on every unit state; (2) the transient leakage Gram is
  exactly zero once the sink wiring annihilates the contrast
  (`CJ = 0 ⟹ (CJ)ᴴ(CJ) = 0`, the record-sink nullity
  mechanism); (3) a uniform contraction bound
  `ρ_X ≤ 1 - γ₀ < 1` gives regulator-uniform geometric decay
  (`ρ_X^k ≤ (1-γ₀)^k → 0`).

Rendering disclosed: the identification of the retained
algebra with the commutant `{Z_X, L_X}'` and the spectral
formula for `ρ_X` cite the proved score–dwell spectrum and
commutant records; the autonomous-occurrence hypothesis is the
manuscript's declared physical assumption (see the firewall
following the theorem).
-/

open Matrix

namespace NCG

/-- `thm:generator-native-renewal`. -/
theorem generator_native_renewal :
    -- (1) fresh-collision branches: resolution of identity
    --     and Born probability ½ on unit states
    (∀ {d : Type} [Fintype d] [DecidableEq d] (v : d → ℂ),
      star v ⬝ᵥ v = 1 →
      ((2 : ℂ)⁻¹ • (1 : Matrix d d ℂ))
          + (2 : ℂ)⁻¹ • (1 : Matrix d d ℂ) = 1
        ∧ star v ⬝ᵥ (((2 : ℂ)⁻¹ • (1 : Matrix d d ℂ)) *ᵥ v)
            = 2⁻¹)
    -- (2) the transient leakage Gram is zero
    ∧ (∀ {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
        (C : Matrix a b ℂ) (J : Matrix b c ℂ),
        C * J = 0 → (C * J)ᴴ * (C * J) = 0)
    -- (3) uniform contraction gives regulator-uniform decay
    ∧ (∀ (ρ : ℕ → ℝ) (γ₀ : ℝ), 0 < γ₀ → γ₀ ≤ 1 →
        (∀ Y, 0 ≤ ρ Y) → (∀ Y, ρ Y ≤ 1 - γ₀) →
        (∀ Y k, ρ Y ^ k ≤ (1 - γ₀) ^ k)
          ∧ Filter.Tendsto (fun k => (1 - γ₀) ^ k)
              Filter.atTop (nhds 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d _ _ v hv
    constructor
    · rw [← add_smul]
      norm_num
    · rw [Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul, hv, smul_eq_mul, mul_one]
  · intro a b c _ _ _ C J hCJ
    rw [hCJ, Matrix.conjTranspose_zero, Matrix.zero_mul]
  · intro ρ γ₀ hγ0 hγ1 hnn hle
    refine ⟨fun Y k => pow_le_pow_left₀ (hnn Y) (hle Y) k, ?_⟩
    exact tendsto_pow_atTop_nhds_zero_of_lt_one
      (by linarith) (by linarith)

end NCG
