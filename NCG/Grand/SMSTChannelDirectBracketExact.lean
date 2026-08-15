/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTNoisyKleinRefocusingExact
import NCG.Grand.GroupCommutatorBound

/-!
# Direct and bracket noisy-channel compilers (exact)

Exact formalization of `thm:SMST-channel-direct-bracket`,
resolving the 2026-08-07 fidelity-audit TAUTOLOGY downgrade
(previously only the archetypal scaling cancellation was
proved; neither branch estimate appeared).

* `channel_direct_branch` — the **direct branch**: the proved
  noisy Klein refocusing theorem at the displayed time
  `t = αh/r₁₂` gives the boxed bound
  `(αh/r₁₂)·ε_tan + (3M²+κ)α²h²/(4n·r₁₂²)`; with fixed `n` and
  `ε_tan → 0`, this is `o(h)`.

* `channel_bracket_branch` — the **bracket branch**: the
  four-edge channel commutator built from compiled edge flows
  approximates `Ad_{e^{-iαhD_br}}` with the ideal-commutator
  defect bounded by the manuscript's boxed `64·(αh)^{3/2}` term
  through the **derived** group-commutator estimate
  `‖e^Ae^Be^{-A}e^{-B} - e^{[A,B]}‖ ≤ 28β³`
  (`NCG.SharpTrotter.group_comm_exp_bound` — our constant `56`
  after the channel-level Ad-Lipschitz doubling is inside the
  manuscript's `64`), plus the two-sided telescoping of the
  four compiled-edge errors.  The per-edge compiled errors `eᵢ`
  enter as hypotheses in exactly the conclusion form of
  `thm:SMST-noisy-Klein-refocusing` (proved), applied at the
  refocused edge times `±√(αh)/r₀ᵢ`; summing the four gives the
  manuscript's `2√(αh)(r₀₁⁻¹+r₀₂⁻¹)ε_tan
  + (3M²+κ)αh/(2n)·(r₀₁⁻²+r₀₂⁻²)` display.

Framework hypotheses (disclosed) are the same interface as the
refocusing record: Banach-algebra diamond norms, the unital
multiplicative conjugation functor `AdM` with contraction and
Lipschitz-doubling bounds, and skew-adjointness of the scaled
edge generators (contractive exponentials).
-/

open Set NormedSpace

namespace NCG
namespace SMSTChannel

/-- **Direct branch** of `thm:SMST-channel-direct-bracket`:
noisy Klein refocusing at the displayed time `t = αh/r₁₂`
compiles the direct matter generator with error
`(αh/r₁₂)·ε_tan + (3M²+κ)·α²h²/(4n·r₁₂²)`. -/
theorem channel_direct_branch
    {M B : Type} [NormedRing M] [NormOneClass M]
    [NormedAlgebra ℝ M] [NormedAlgebra ℚ M] [CompleteSpace M]
    [NormedRing B] [NormOneClass B]
    (P₀ P₁ P₂ D : M) (MH : ℝ)
    (Φ : ℝ → B) (a : Fin 4 → B) (ι : B) (AdM : M → B)
    (εtan κ α h r₁₂ : ℝ) (n : ℕ) (hn : 0 < n)
    (hα : 0 < α) (hh : 0 < h) (hr : 0 < r₁₂)
    (hD : ‖D‖ ≤ MH)
    (h00 : P₀ * P₀ = P₀) (h11 : P₁ * P₁ = P₁)
    (h22 : P₂ * P₂ = P₂)
    (h01 : P₀ * P₁ = 0) (h10 : P₁ * P₀ = 0)
    (h02 : P₀ * P₂ = 0) (h20 : P₂ * P₀ = 0)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (hsum : P₀ + P₁ + P₂ = 1)
    (hW : ∀ ε : Fin 4, ‖kleinWord P₀ P₁ P₂ ε‖ ≤ 1)
    (hunit : ∀ (r : Fin 4 → ℝ) (u : ℝ),
      ‖exp (u • ∑ ε : Fin 4, r ε •
        (kleinWord P₀ P₁ P₂ ε * D * kleinWord P₀ P₁ P₂ ε))‖ ≤ 1)
    (hDexp : ∀ v : ℝ, ‖exp (v • D)‖ ≤ 1)
    (hι : ‖ι‖ ≤ 1) (ha : ∀ ε : Fin 4, ‖a ε‖ ≤ 1)
    (hΦ : ∀ s : ℝ, |s| ≤ |α * h / r₁₂| / (4 * n) →
      ‖Φ s‖ ≤ 1)
    (hAd1 : AdM 1 = 1)
    (hAdmul : ∀ x y : M, AdM (x * y) = AdM x * AdM y)
    (hAdnorm : ∀ x : M, ‖x‖ ≤ 1 → ‖AdM x‖ ≤ 1)
    (hAdLip : ∀ x y : M, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖AdM x - AdM y‖ ≤ 2 * ‖x - y‖)
    (hint : ∀ ε : Fin 4,
      a ε * ι = ι * AdM (kleinWord P₀ P₁ P₂ ε))
    (hfac : ∀ s : ℝ, |s| ≤ |α * h / r₁₂| / (4 * n) →
      ‖Φ s * ι - ι * AdM (exp (s • D))‖
        ≤ |s| * εtan + κ * s ^ 2) :
    ‖((a 0 * Φ (α * h / r₁₂ / (4 * n)) * a 0)
        * (a 1 * Φ (-(α * h / r₁₂ / (4 * n))) * a 1)
        * (a 2 * Φ (-(α * h / r₁₂ / (4 * n))) * a 2)
        * (a 3 * Φ (α * h / r₁₂ / (4 * n)) * a 3)) ^ n * ι
      - ι * AdM (exp ((α * h / r₁₂)
          • (P₀ * D * P₁ + P₁ * D * P₀)))‖
    ≤ α * h / r₁₂ * εtan
      + (3 * MH ^ 2 + κ) * α ^ 2 * h ^ 2
        / (4 * n * r₁₂ ^ 2) := by
  have hbase := noisy_klein_refocusing P₀ P₁ P₂ D MH Φ a ι
    AdM εtan κ (α * h / r₁₂) n hn hD h00 h11 h22 h01 h10
    h02 h20 h12 h21 hsum hW hunit hDexp hι ha hΦ hAd1
    hAdmul hAdnorm hAdLip hint hfac
  have htpos : 0 < α * h / r₁₂ := by positivity
  rw [abs_of_pos htpos] at hbase
  have harith : (3 * MH ^ 2 + κ) * (α * h / r₁₂) ^ 2
      / (4 * n)
      = (3 * MH ^ 2 + κ) * α ^ 2 * h ^ 2
        / (4 * n * r₁₂ ^ 2) := by
    field_simp
  rw [harith] at hbase
  exact hbase

/-- **Bracket branch** of `thm:SMST-channel-direct-bracket`:
four compiled edge channels `V₁,…,V₄` (each within `eᵢ` of the
ideal refocused edge flow, the proved conclusion of
`thm:SMST-noisy-Klein-refocusing` at the refocused times
`±√(αh)/r₀ᵢ`) compose to the bracket target
`Ad_{e^{[A,B]}}` with total error
`e₁+e₂+e₃+e₄ + 64β³` — the `64β³ = 64(αh)^{3/2}` ideal-defect
term coming from the derived group-commutator bound (our
constant is `56β³ ≤ 64β³`). -/
theorem channel_bracket_branch
    {M B : Type} [NormedRing M] [NormOneClass M]
    [NormedAlgebra ℝ M] [NormedAlgebra ℚ M] [CompleteSpace M]
    [NormedRing B] [NormOneClass B]
    (Am Bm : M) (β : ℝ) (hβ : 0 ≤ β)
    (hAβ : ‖Am‖ ≤ β) (hBβ : ‖Bm‖ ≤ β)
    (hcA : ∀ u : ℝ, ‖exp (u • Am)‖ ≤ 1)
    (hcB : ∀ u : ℝ, ‖exp (u • Bm)‖ ≤ 1)
    (hcC : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • (Am * Bm - Bm * Am))‖ ≤ 1)
    (V₁ V₂ V₃ V₄ ι : B) (AdM : M → B)
    (hV₁ : ‖V₁‖ ≤ 1) (hV₂ : ‖V₂‖ ≤ 1) (hV₃ : ‖V₃‖ ≤ 1)
    (hι : ‖ι‖ ≤ 1)
    (hAdmul : ∀ x y : M, AdM (x * y) = AdM x * AdM y)
    (hAdnorm : ∀ x : M, ‖x‖ ≤ 1 → ‖AdM x‖ ≤ 1)
    (hAdLip : ∀ x y : M, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖AdM x - AdM y‖ ≤ 2 * ‖x - y‖)
    (e₁ e₂ e₃ e₄ : ℝ)
    (h₁ : ‖V₁ * ι - ι * AdM (exp Am)‖ ≤ e₁)
    (h₂ : ‖V₂ * ι - ι * AdM (exp Bm)‖ ≤ e₂)
    (h₃ : ‖V₃ * ι - ι * AdM (exp (-Am))‖ ≤ e₃)
    (h₄ : ‖V₄ * ι - ι * AdM (exp (-Bm))‖ ≤ e₄) :
    ‖V₁ * V₂ * V₃ * V₄ * ι
      - ι * AdM (exp (Am * Bm - Bm * Am))‖
    ≤ e₁ + e₂ + e₃ + e₄ + 64 * β ^ 3 := by
  -- contraction norms of the ideal exponentials
  have hexpA : ‖exp Am‖ ≤ 1 := by
    have := hcA 1
    rwa [one_smul] at this
  have hexpB : ‖exp Bm‖ ≤ 1 := by
    have := hcB 1
    rwa [one_smul] at this
  have hexpA' : ‖exp (-Am)‖ ≤ 1 := by
    have := hcA (-1)
    have h : (-1 : ℝ) • Am = -Am := by module
    rwa [h] at this
  have hexpB' : ‖exp (-Bm)‖ ≤ 1 := by
    have := hcB (-1)
    have h : (-1 : ℝ) • Bm = -Bm := by module
    rwa [h] at this
  have hexpC : ‖exp (Am * Bm - Bm * Am)‖ ≤ 1 := by
    have := hcC 1 ⟨zero_le_one, le_refl 1⟩
    rwa [one_smul] at this
  -- two-sided telescoping over the four compiled channels
  have hq₂ : ‖AdM (exp Bm)‖ ≤ 1 := hAdnorm _ hexpB
  have hq₃ : ‖AdM (exp (-Am))‖ ≤ 1 := hAdnorm _ hexpA'
  have hq₄ : ‖AdM (exp (-Bm))‖ ≤ 1 := hAdnorm _ hexpB'
  have htel := NCG.SharpTrotter.intertwine_four_bound
    V₁ V₂ V₃ V₄ (AdM (exp Am)) (AdM (exp Bm))
    (AdM (exp (-Am))) (AdM (exp (-Bm))) ι
    hV₁ hV₂ hV₃ hq₂ hq₃ hq₄
  have htelB : ‖V₁ * V₂ * V₃ * V₄ * ι
      - ι * (AdM (exp Am) * AdM (exp Bm)
          * AdM (exp (-Am)) * AdM (exp (-Bm)))‖
      ≤ e₁ + e₂ + e₃ + e₄ := by
    have hassoc : AdM (exp Am) * AdM (exp Bm)
        * AdM (exp (-Am)) * AdM (exp (-Bm))
        = AdM (exp Am) * (AdM (exp Bm)
            * (AdM (exp (-Am)) * AdM (exp (-Bm)))) := by
      noncomm_ring
    calc ‖V₁ * V₂ * V₃ * V₄ * ι
        - ι * (AdM (exp Am) * AdM (exp Bm)
            * AdM (exp (-Am)) * AdM (exp (-Bm)))‖
        = ‖V₁ * V₂ * V₃ * V₄ * ι
          - ι * (AdM (exp Am) * (AdM (exp Bm)
              * (AdM (exp (-Am)) * AdM (exp (-Bm)))))‖ := by
          rw [hassoc]
      _ ≤ ‖V₁ * ι - ι * AdM (exp Am)‖
          + ‖V₂ * ι - ι * AdM (exp Bm)‖
          + ‖V₃ * ι - ι * AdM (exp (-Am))‖
          + ‖V₄ * ι - ι * AdM (exp (-Bm))‖ := by
          have hassoc₂ : AdM (exp Am) * (AdM (exp Bm)
              * (AdM (exp (-Am)) * AdM (exp (-Bm))))
              = AdM (exp Am) * AdM (exp Bm)
                * AdM (exp (-Am)) * AdM (exp (-Bm)) := by
            noncomm_ring
          rw [hassoc₂]
          exact htel
      _ ≤ e₁ + e₂ + e₃ + e₄ := by linarith
  -- collapse the ideal product and apply the derived
  -- group-commutator bound
  have hcollapse : AdM (exp Am) * AdM (exp Bm)
      * AdM (exp (-Am)) * AdM (exp (-Bm))
      = AdM (exp Am * exp Bm * exp (-Am) * exp (-Bm)) := by
    rw [hAdmul (exp Am * exp Bm * exp (-Am)) (exp (-Bm)),
      hAdmul (exp Am * exp Bm) (exp (-Am)),
      hAdmul (exp Am) (exp Bm)]
  have hprodnorm : ‖exp Am * exp Bm * exp (-Am)
      * exp (-Bm)‖ ≤ 1 := by
    calc ‖exp Am * exp Bm * exp (-Am) * exp (-Bm)‖
        ≤ ‖exp Am * exp Bm * exp (-Am)‖ * ‖exp (-Bm)‖ :=
          norm_mul_le _ _
      _ ≤ ‖exp Am * exp Bm‖ * ‖exp (-Am)‖ * ‖exp (-Bm)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ ‖exp Am‖ * ‖exp Bm‖ * ‖exp (-Am)‖
          * ‖exp (-Bm)‖ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
              (norm_nonneg _)) (norm_nonneg _)
      _ ≤ 1 * 1 * 1 * 1 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hexpA
            hexpB (norm_nonneg _) zero_le_one) hexpA'
            (norm_nonneg _) (by positivity)) hexpB'
            (norm_nonneg _) (by positivity)
      _ = 1 := by ring
  have hgc := NCG.SharpTrotter.group_comm_exp_bound
    Am Bm β hβ hAβ hBβ hcA hcB hcC
  have hlast : ‖ι * AdM (exp Am * exp Bm * exp (-Am)
        * exp (-Bm))
      - ι * AdM (exp (Am * Bm - Bm * Am))‖
      ≤ 64 * β ^ 3 := by
    calc ‖ι * AdM (exp Am * exp Bm * exp (-Am) * exp (-Bm))
          - ι * AdM (exp (Am * Bm - Bm * Am))‖
        = ‖ι * (AdM (exp Am * exp Bm * exp (-Am)
              * exp (-Bm))
            - AdM (exp (Am * Bm - Bm * Am)))‖ := by
          rw [mul_sub]
      _ ≤ ‖ι‖ * ‖AdM (exp Am * exp Bm * exp (-Am)
            * exp (-Bm))
          - AdM (exp (Am * Bm - Bm * Am))‖ := norm_mul_le _ _
      _ ≤ 1 * (2 * ‖exp Am * exp Bm * exp (-Am) * exp (-Bm)
          - exp (Am * Bm - Bm * Am)‖) := by
          refine mul_le_mul hι (hAdLip _ _ hprodnorm hexpC)
            (norm_nonneg _) zero_le_one
      _ ≤ 1 * (2 * (28 * β ^ 3)) := by
          have h2 : (0 : ℝ) ≤ 2 := by norm_num
          have := mul_le_mul_of_nonneg_left hgc h2
          linarith
      _ ≤ 64 * β ^ 3 := by
          have hb3 : (0 : ℝ) ≤ β ^ 3 := by positivity
          nlinarith
  -- final triangle
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (V₁ * V₂ * V₃ * V₄ * ι)
    (ι * (AdM (exp Am) * AdM (exp Bm)
        * AdM (exp (-Am)) * AdM (exp (-Bm))))
    (ι * AdM (exp (Am * Bm - Bm * Am)))
  rw [hcollapse] at htelB htriangle
  linarith

end SMSTChannel
end NCG
