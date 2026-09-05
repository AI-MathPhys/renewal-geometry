/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Gap passage and primitive-word soft modes
  (`thm:gap-soft-mode-alternative`,
  Gran-Tensor manuscript)

* `gap_soft_mode_alternative`:
  (i) the boxed gap passage — if the finite-stage forms
      dominate the transient masses,
      `q_n[u] ≥ γ_n ‖(I - E_n)u‖²`, the kernel
      contractions converge strongly, and Mosco recovery
      sequences exist (rendered in eventual-`ε` form),
      then every eventual lower bound `c` of the gaps
      passes to the limit form:
      `q_∞[u] ≥ c·‖(I - E_∞)u‖²` — exactly the boxed
      `q_∞[u] ≥ (liminf γ_n)‖(I - E_∞)u‖²`, since the
      liminf is the supremum of the eventual lower
      bounds;
  (ii) soft modes — if the gaps are the optimal transient
      Rayleigh constants (rendered by their
      almost-minimizer property) and collapse along a
      subsequence, there are normalized transient
      vectors whose energies vanish.

The operator-core clause (approximating the witnesses by
finite primitive-word combinations in graph norm, and
reading their residuals as source-Gram panels) is the
manuscript's core layer; the identification of the
finite-stage carriers with one limit space is its
Mosco/embedding layer, entering through the recovery and
strong-convergence hypotheses.
-/

open Filter

namespace NCG

/-- `thm:gap-soft-mode-alternative` (gap passage to the
limit form, and soft-mode witnesses under gap
collapse). -/
theorem gap_soft_mode_alternative
    {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (q : ℕ → H → ℝ) (qinf : H → ℝ)
    (E : ℕ → H →L[ℝ] H) (Einf : H →L[ℝ] H)
    (γ : ℕ → ℝ) :
    -- (i) the boxed gap passage
    ((∀ n, ‖E n‖ ≤ 1) →
      (∀ u, Tendsto (fun n => E n u) atTop
        (nhds (Einf u))) →
      (∀ n u, γ n * ‖u - E n u‖ ^ 2 ≤ q n u) →
      (∀ u : H, ∃ v : ℕ → H,
        Tendsto v atTop (nhds u)
        ∧ ∀ ε > 0, ∀ᶠ n in atTop,
            q n (v n) ≤ qinf u + ε) →
      ∀ (u : H) (c : ℝ), 0 ≤ c →
        (∀ᶠ n in atTop, c ≤ γ n) →
        c * ‖u - Einf u‖ ^ 2 ≤ qinf u)
    -- (ii) collapsing gaps produce soft-mode witnesses
    ∧ ((∀ n, 0 ≤ γ n) →
        (∀ n, ∀ ε > 0, ∃ u : H,
          E n u = 0 ∧ ‖u‖ = 1 ∧ q n u < γ n + ε) →
        (∀ n u, γ n * ‖u - E n u‖ ^ 2 ≤ q n u) →
        ∀ σ : ℕ → ℕ,
          Tendsto (fun j => γ (σ j)) atTop (nhds 0) →
          ∃ v : ℕ → H,
            (∀ j, E (σ j) (v j) = 0)
            ∧ (∀ j, ‖v j‖ = 1)
            ∧ Tendsto (fun j => q (σ j) (v j)) atTop
                (nhds 0)) := by
  constructor
  · -- (i) gap passage
    intro hE1 hEs hlow hrec u c hc hev
    obtain ⟨v, hvconv, hvq⟩ := hrec u
    -- the transient masses converge
    have hmass : Tendsto
        (fun n => ‖v n - E n (v n)‖) atTop
        (nhds ‖u - Einf u‖) := by
      have hvu : Tendsto (fun n => v n - u) atTop
          (nhds 0) := by
        have := hvconv.sub (tendsto_const_nhds (x := u))
        simpa using this
      have hvunorm : Tendsto (fun n => ‖v n - u‖) atTop
          (nhds 0) := by
        have := hvu.norm
        simpa using this
      have hdiff : Tendsto (fun n =>
          (v n - E n (v n)) - (u - Einf u)) atTop
          (nhds 0) := by
        have h1 : Tendsto (fun n => Einf u - E n u)
            atTop (nhds 0) := by
          have := (tendsto_const_nhds
            (x := Einf u) (f := atTop (α := ℕ))).sub
            (hEs u)
          simpa using this
        have h2 : Tendsto (fun n => E n (v n - u))
            atTop (nhds 0) := by
          have hb : ∀ n, ‖E n (v n - u)‖
              ≤ ‖v n - u‖ := by
            intro n
            calc ‖E n (v n - u)‖
                ≤ ‖E n‖ * ‖v n - u‖ :=
                  (E n).le_opNorm _
              _ ≤ 1 * ‖v n - u‖ :=
                  mul_le_mul_of_nonneg_right (hE1 n)
                    (norm_nonneg _)
              _ = ‖v n - u‖ := one_mul _
          exact squeeze_zero_norm hb hvunorm
        have h12 := h1.sub h2
        have hadd := hvu.add h12
        rw [show (0 : H) + (0 - 0) = 0 by simp] at hadd
        apply hadd.congr
        intro n
        rw [map_sub]
        abel
      -- norms converge
      have := hdiff.norm
      simp only [norm_zero] at this
      have htri : Tendsto (fun n =>
          ‖v n - E n (v n)‖ - ‖u - Einf u‖) atTop
          (nhds 0) := by
        have hb : ∀ n, ‖(‖v n - E n (v n)‖
            - ‖u - Einf u‖ : ℝ)‖
            ≤ ‖(v n - E n (v n)) - (u - Einf u)‖ := by
          intro n
          rw [Real.norm_eq_abs]
          exact abs_norm_sub_norm_le _ _
        exact squeeze_zero_norm hb this
      have := htri.add (tendsto_const_nhds
        (x := ‖u - Einf u‖))
      simpa using this
    -- pass the eventual bound to the limit
    have hlim : Tendsto (fun n =>
        c * ‖v n - E n (v n)‖ ^ 2) atTop
        (nhds (c * ‖u - Einf u‖ ^ 2)) :=
      ((hmass.pow 2).const_mul c)
    -- conclude for every `ε`
    have hle : ∀ ε > 0,
        c * ‖u - Einf u‖ ^ 2 ≤ qinf u + ε := by
      intro ε hε
      apply le_of_tendsto hlim
      filter_upwards [hvq ε hε, hev] with n hqn hcn
      calc c * ‖v n - E n (v n)‖ ^ 2
          ≤ γ n * ‖v n - E n (v n)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hcn
              (by positivity)
        _ ≤ q n (v n) := hlow n (v n)
        _ ≤ qinf u + ε := hqn
    by_contra hlt
    push Not at hlt
    have hgap : 0 < (c * ‖u - Einf u‖ ^ 2 - qinf u) / 2 :=
      by linarith
    have := hle _ hgap
    linarith
  · -- (ii) soft-mode witnesses
    intro hγ0 hopt hlow σ hσ
    -- pick `1/(j+1)`-almost-minimizers
    have hchoice : ∀ j : ℕ, ∃ u : H,
        E (σ j) u = 0 ∧ ‖u‖ = 1
        ∧ q (σ j) u < γ (σ j) + 1 / (j + 1) :=
      fun j => hopt (σ j) (1 / (j + 1))
        (by positivity)
    choose v hv0 hv1 hvq using hchoice
    refine ⟨v, hv0, hv1, ?_⟩
    -- squeeze: `γ ≤ q < γ + 1/(j+1)`
    have hlower : ∀ j, γ (σ j) ≤ q (σ j) (v j) := by
      intro j
      have := hlow (σ j) (v j)
      rw [hv0 j, sub_zero, hv1 j] at this
      simpa using this
    have hupper : ∀ j, q (σ j) (v j)
        ≤ γ (σ j) + 1 / (j + 1) :=
      fun j => le_of_lt (hvq j)
    have hγ1 : Tendsto (fun j : ℕ =>
        γ (σ j) + 1 / (j + 1)) atTop (nhds 0) := by
      rw [show (0 : ℝ) = 0 + 0 by simp]
      exact hσ.add tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      hσ hγ1 hlower hupper

end NCG
