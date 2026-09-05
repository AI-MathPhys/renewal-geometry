/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ExactSourceSchurResidual
import NCG.Grand.RewardPressure

/-!
# Palatini--Cartan--Holst writer Hodge and reward closure

This file proves `thm:SMST-PCH-writer-closure`.  The differentiated writer is
the exact cochain `A_PCH = d₀ Σ_PCH`.  The source-range projection of `d₀`
is the Moore--Penrose projector constructed by spectral functional calculus in
`ExactSourceSchurResidual`, so the exact-range, curl, and harmonic identities
are consequences rather than hypotheses.

The reward clause uses the already proved renewal-pressure slope
reconstruction.  Applying the same nuisance short to a physical action source
and to a fixed coefficient combination of its columns preserves that
factorization; the exact singular Schur theorem then makes the Palatini Schur
residual vanish.
-/

open Matrix

namespace NCG

/-- Directional first variation of the protected PCH writer. -/
def pchWriterVariation {c₀ c₁ vEin : ℕ}
    (d₀ : Matrix (Fin c₁) (Fin c₀) ℂ)
    (Sigma : Matrix (Fin c₀) (Fin vEin) ℂ) :
    Matrix (Fin c₁) (Fin vEin) ℂ :=
  d₀ * Sigma

/-- Exact-range, curl, and harmonic closure of the differentiated PCH
writer. -/
theorem pchWriterVariation_hodgeClosure
    {c₀ c₁ c₂ vEin harm : ℕ}
    (d₀ : Matrix (Fin c₁) (Fin c₀) ℂ)
    (d₁ : Matrix (Fin c₂) (Fin c₁) ℂ)
    (Sigma : Matrix (Fin c₀) (Fin vEin) ℂ)
    (H : Matrix (Fin c₁) (Fin harm) ℂ)
    (hcomplex : d₁ * d₀ = 0)
    (hharmonic : Hᴴ * d₀ = 0) :
    let A := pchWriterVariation d₀ Sigma
    Aᴴ * (1 - sourceRangeProjection d₀) * A = 0
      ∧ d₁ * A = 0
      ∧ Hᴴ * A = 0 := by
  dsimp only [pchWriterVariation]
  have hPd₀ := (sourceGramPseudoinverse_projection d₀).2.2.2.2.2
  change sourceRangeProjection d₀ * d₀ = d₀ at hPd₀
  have hperp : (1 - sourceRangeProjection d₀) * (d₀ * Sigma) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPd₀,
      sub_self, Matrix.zero_mul]
  constructor
  · rw [Matrix.mul_assoc, hperp, Matrix.mul_zero]
  constructor
  · rw [← Matrix.mul_assoc, hcomplex, Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, hharmonic, Matrix.zero_mul]

/-- Same-function pressure reconstruction and same-short source closure. -/
theorem pchReward_pressureAndSchurClosure
    {Ω v h eP eR : ℕ}
    (S G : Matrix (Fin Ω) (Fin v) ℂ)
    (T : Matrix (Fin Ω) (Fin 1) ℂ)
    (piX : Matrix (Fin 1) (Fin v) ℂ)
    (hpressure : S = -G - T * piX)
    (Q : Matrix (Fin h) (Fin h) ℂ)
    (B : Matrix (Fin h) (Fin eP) ℂ)
    (R : Matrix (Fin h) (Fin eR) ℂ)
    (coeff : Matrix (Fin eP) (Fin eR) ℂ)
    (hreward : R = B * coeff) :
    G = -S - T * piX
      ∧ SourceRangeIncluded (Q * R) (Q * B)
      ∧ sourceSchurResidual (Q * B) (Q * R) = 0 := by
  have hrec := slope_reconstruction S G T piX hpressure
  have hrange : SourceRangeIncluded (Q * R) (Q * B) := by
    refine ⟨coeff, ?_⟩
    rw [hreward, Matrix.mul_assoc]
  exact ⟨hrec, hrange,
    (sourceSchurResidual_eq_zero_iff_rangeIncluded (Q * B) (Q * R)).2 hrange⟩

/-- `thm:SMST-PCH-writer-closure`: assembled writer-native Hodge and reward
closure. -/
theorem palatiniCartanHolst_writerClosure
    {c₀ c₁ c₂ vEin harm Ω v h eP eR : ℕ}
    (d₀ : Matrix (Fin c₁) (Fin c₀) ℂ)
    (d₁ : Matrix (Fin c₂) (Fin c₁) ℂ)
    (Sigma : Matrix (Fin c₀) (Fin vEin) ℂ)
    (H : Matrix (Fin c₁) (Fin harm) ℂ)
    (hcomplex : d₁ * d₀ = 0)
    (hharmonic : Hᴴ * d₀ = 0)
    (S G : Matrix (Fin Ω) (Fin v) ℂ)
    (T : Matrix (Fin Ω) (Fin 1) ℂ)
    (piX : Matrix (Fin 1) (Fin v) ℂ)
    (hpressure : S = -G - T * piX)
    (Q : Matrix (Fin h) (Fin h) ℂ)
    (B : Matrix (Fin h) (Fin eP) ℂ)
    (R : Matrix (Fin h) (Fin eR) ℂ)
    (coeff : Matrix (Fin eP) (Fin eR) ℂ)
    (hreward : R = B * coeff) :
    let A := pchWriterVariation d₀ Sigma
    Aᴴ * (1 - sourceRangeProjection d₀) * A = 0
      ∧ d₁ * A = 0
      ∧ Hᴴ * A = 0
      ∧ G = -S - T * piX
      ∧ SourceRangeIncluded (Q * R) (Q * B)
      ∧ sourceSchurResidual (Q * B) (Q * R) = 0 := by
  dsimp only
  obtain ⟨hexact, hcurl, hharm⟩ :=
    pchWriterVariation_hodgeClosure d₀ d₁ Sigma H hcomplex hharmonic
  obtain ⟨hrec, hrange, hschur⟩ :=
    pchReward_pressureAndSchurClosure S G T piX hpressure Q B R coeff hreward
  exact ⟨hexact, hcurl, hharm, hrec, hrange, hschur⟩

end NCG
