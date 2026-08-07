/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite-type energy-to-amplitude and inverse closure
  (`thm:renewal-finite-type-closure`,
  Gran-Tensor manuscript)

* `renewal_finite_type_closure`:
  (i) the boxed energy-to-amplitude bound: with typed
      panels of mass at least `ω⋆` and prototype deviation
      at most `ε`, every local amplitude obeys
      `sup_e ‖Ξ_e‖ ≤ 𝓔₂²/ω⋆ + 2ε`;
  (ii) the boxed `L^p` interpolation (power form): for
      `p ≥ 2`, the weighted `p`-th moments satisfy
      `∑ μ_e d_e^p ≤ (sup d)^{p-2} ∑ μ_e d_e²`;
  (iii) the Combes–Thomas/Neumann closure: if
      `‖D⁻¹‖ ≤ 1/σ⋆` and the conjugation defect satisfies
      `‖E‖ ≤ b⋆ < σ⋆`, then any inverse of `D + E` obeys
      the boxed bound `‖(D+E)⁻¹‖ ≤ 1/(σ⋆ - b⋆)`.

The identification of `D` with the protected-horizontal
Hodge–Dirac operator, the exponential weight `e^{μφ}` with
a one-Lipschitz `φ` (giving the boxed off-diagonal decay
`‖P_x D⁻¹ P_y‖ ≤ e^{-μd(x,y)}/(σ⋆-b⋆)`), and the two-sided
weighted Schur bound over uniformly finite exponential
volumes are the manuscript's weight/Schur layer over these
three estimates.
-/

namespace NCG

/-- `thm:renewal-finite-type-closure`. -/
theorem renewal_finite_type_closure {ι τ : Type*}
    [Fintype ι] [DecidableEq τ] :
    -- (i) the boxed energy-to-amplitude bound
    (∀ (μ x : ι → ℝ) (θ : ι → τ) (p : τ → ℝ)
        (ω ε : ℝ), 0 < ω → 0 ≤ ε →
      (∀ e, 0 ≤ μ e) → (∀ e, 0 ≤ x e) →
      (∀ e, |x e - p (θ e)| ≤ ε) →
      (∀ e, ω ≤ ∑ e' ∈ Finset.univ.filter
        (fun e' => θ e' = θ e), μ e') →
      ∀ e, x e ≤ (∑ e', μ e' * x e') / ω + 2 * ε)
    -- (ii) the boxed L^p interpolation (power form)
    ∧ (∀ (μ d : ι → ℝ) (S : ℝ) (P : ℕ), 2 ≤ P →
        (∀ e, 0 ≤ μ e) → (∀ e, 0 ≤ d e) →
        (∀ e, d e ≤ S) →
        ∑ e, μ e * d e ^ P
          ≤ S ^ (P - 2) * ∑ e, μ e * d e ^ 2)
    -- (iii) the Combes–Thomas/Neumann inverse closure
    ∧ (∀ {A : Type} [NormedRing A]
        (D E Di W : A) (σ b : ℝ),
        0 < σ → 0 ≤ b → b < σ →
        D * Di = 1 → Di * D = 1 →
        ‖Di‖ ≤ 1 / σ → ‖E‖ ≤ b →
        (D + E) * W = 1 → W * (D + E) = 1 →
        ‖W‖ ≤ 1 / (σ - b)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ x θ p ω ε hω hε hμ hx hdev hmass e
    set E2 : ℝ := ∑ e', μ e' * x e' with hE2
    have hE2nn : 0 ≤ E2 :=
      Finset.sum_nonneg fun e' _ =>
        mul_nonneg (hμ e') (hx e')
    -- the prototype of the type of `e` is energy-bounded
    have hproto : p (θ e) - ε ≤ E2 / ω := by
      have h1 : ∑ e' ∈ Finset.univ.filter
          (fun e' => θ e' = θ e), μ e' * (p (θ e) - ε)
          ≤ E2 := by
        calc ∑ e' ∈ Finset.univ.filter
              (fun e' => θ e' = θ e), μ e' * (p (θ e) - ε)
            ≤ ∑ e' ∈ Finset.univ.filter
              (fun e' => θ e' = θ e), μ e' * x e' := by
              refine Finset.sum_le_sum fun e' he' => ?_
              have hty := (Finset.mem_filter.mp he').2
              have hd := hdev e'
              rw [hty] at hd
              have := abs_le.mp hd
              exact mul_le_mul_of_nonneg_left
                (by linarith [this.1]) (hμ e')
          _ ≤ E2 :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset _ _)
                (fun e' _ _ =>
                  mul_nonneg (hμ e') (hx e'))
      rw [← Finset.sum_mul] at h1
      rcases le_or_gt (p (θ e) - ε) 0 with h | h
      · calc p (θ e) - ε ≤ 0 := h
          _ ≤ E2 / ω := div_nonneg hE2nn hω.le
      · have hm := hmass e
        have h2 : ω * (p (θ e) - ε) ≤ E2 :=
          le_trans (mul_le_mul_of_nonneg_right hm h.le) h1
        rw [le_div_iff₀ hω]
        have h3 : (p (θ e) - ε) * ω
            = ω * (p (θ e) - ε) := mul_comm _ _
        linarith [h2, h3]
    have hd := abs_le.mp (hdev e)
    calc x e ≤ p (θ e) + ε := by linarith [hd.2]
      _ ≤ E2 / ω + 2 * ε := by linarith [hproto]
  · intro μ d S P hP hμ hd hS
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    have hsplit : d e ^ P = d e ^ (P - 2) * d e ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    have hdS : d e ^ (P - 2) ≤ S ^ (P - 2) :=
      pow_le_pow_left₀ (hd e) (hS e) _
    calc μ e * d e ^ P
        = μ e * (d e ^ (P - 2) * d e ^ 2) := by
          rw [hsplit]
      _ ≤ μ e * (S ^ (P - 2) * d e ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (hμ e)
          exact mul_le_mul_of_nonneg_right hdS
            (sq_nonneg _)
      _ = S ^ (P - 2) * (μ e * d e ^ 2) := by ring
  · intro A _ D E Di W σ b hσ hb hbσ hDDi hDiD hDi hE
      hW1 hW2
    -- W = Di - Di(EW)
    have hkey : W = Di - Di * (E * W) := by
      have h1 : Di * ((D + E) * W) = Di := by
        rw [hW1, mul_one]
      have h2 : Di * ((D + E) * W)
          = W + Di * (E * W) := by
        rw [add_mul, mul_add, ← mul_assoc, hDiD, one_mul]
      rw [h2] at h1
      exact eq_sub_of_add_eq h1
    have hnorm : ‖W‖ ≤ 1 / σ + b / σ * ‖W‖ := by
      calc ‖W‖ = ‖Di - Di * (E * W)‖ := by rw [← hkey]
        _ ≤ ‖Di‖ + ‖Di * (E * W)‖ := norm_sub_le _ _
        _ ≤ ‖Di‖ + ‖Di‖ * (‖E‖ * ‖W‖) := by
            have h := norm_mul_le Di (E * W)
            have h2 := norm_mul_le E W
            have h3 : ‖Di * (E * W)‖
                ≤ ‖Di‖ * (‖E‖ * ‖W‖) :=
              le_trans h (mul_le_mul_of_nonneg_left h2
                (norm_nonneg _))
            linarith
        _ ≤ 1 / σ + b / σ * ‖W‖ := by
            have hW0 : (0 : ℝ) ≤ ‖W‖ := norm_nonneg _
            have hE0 : (0 : ℝ) ≤ ‖E‖ := norm_nonneg _
            have hDi0 : (0 : ℝ) ≤ ‖Di‖ := norm_nonneg _
            have hEW : ‖E‖ * ‖W‖ ≤ b * ‖W‖ :=
              mul_le_mul_of_nonneg_right hE hW0
            have h4 : ‖Di‖ * (‖E‖ * ‖W‖)
                ≤ 1 / σ * (b * ‖W‖) :=
              mul_le_mul hDi hEW
                (mul_nonneg hE0 hW0) (by positivity)
            have h6 : 1 / σ * (b * ‖W‖)
                = b / σ * ‖W‖ := by ring
            linarith
    have hpos : 0 < 1 - b / σ := by
      rw [sub_pos, div_lt_one hσ]
      exact hbσ
    have hσb : (0 : ℝ) < σ - b := by linarith
    calc ‖W‖ ≤ 1 / σ / (1 - b / σ) := by
          rw [le_div_iff₀ hpos]
          have hW0 : (0 : ℝ) ≤ ‖W‖ := norm_nonneg _
          nlinarith [hnorm]
      _ = 1 / (σ - b) := by
          field_simp

end NCG
