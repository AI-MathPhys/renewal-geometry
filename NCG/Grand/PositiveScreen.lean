/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Compact positive-screen coercive upgrade
  (`thm:SMST-positive-screen`, Gran-Tensor manuscript)

* `smst_positive_screen`:
  (i) the abstract screen-upgrade lemma: a family uniformly
      approximable at every accuracy by convergent screened
      families converges strongly (the boxed
      `Z_h → Z strongly`);
  (ii) the screen instantiation: fixed-radius screened parts
      converging for every radius, plus the boxed uniform
      tail exhaustion `lim_R sup_h ‖(I-S_{h,R})Z_h‖ = 0`
      (and the same for the limit), force strong convergence
      of the full family.

The identification of the screened parts as compact-operator
images of the weakly convergent quadratic packet (compact
operators upgrade weak to strong convergence) is the
manuscript's compactness step feeding hypothesis (ii).
-/

namespace NCG

/-- `thm:SMST-positive-screen`. -/
theorem smst_positive_screen {H : Type*}
    [NormedAddCommGroup H] (Z : ℕ → H) (Zl : H) :
    -- (i) the abstract screen-upgrade lemma
    ((∀ ε : ℝ, 0 < ε → ∃ (w : ℕ → H) (wl : H),
        Filter.Tendsto w Filter.atTop (nhds wl)
        ∧ (∀ n, ‖Z n - w n‖ ≤ ε) ∧ ‖Zl - wl‖ ≤ ε) →
      Filter.Tendsto Z Filter.atTop (nhds Zl))
    -- (ii) the screen instantiation
    ∧ (∀ (scr : ℕ → ℕ → H) (scrl : ℕ → H),
        (∀ R : ℕ, Filter.Tendsto (scr R) Filter.atTop
          (nhds (scrl R))) →
        (∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
          (∀ n, ‖Z n - scr R n‖ ≤ ε)
          ∧ ‖Zl - scrl R‖ ≤ ε) →
        Filter.Tendsto Z Filter.atTop (nhds Zl)) := by
  have hup : (∀ ε : ℝ, 0 < ε → ∃ (w : ℕ → H) (wl : H),
      Filter.Tendsto w Filter.atTop (nhds wl)
      ∧ (∀ n, ‖Z n - w n‖ ≤ ε) ∧ ‖Zl - wl‖ ≤ ε) →
      Filter.Tendsto Z Filter.atTop (nhds Zl) := by
    intro happrox
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨w, wl, hw, hZw, hZlwl⟩ :=
      happrox (ε / 4) (by positivity)
    rw [Metric.tendsto_atTop] at hw
    obtain ⟨N, hN⟩ := hw (ε / 4) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hZw n
    have h2 := hN n hn
    rw [dist_eq_norm] at h2 ⊢
    calc ‖Z n - Zl‖
        = ‖(Z n - w n) + (w n - wl) + (wl - Zl)‖ := by
          congr 1
          abel
      _ ≤ ‖(Z n - w n) + (w n - wl)‖ + ‖wl - Zl‖ :=
          norm_add_le _ _
      _ ≤ ‖Z n - w n‖ + ‖w n - wl‖ + ‖wl - Zl‖ := by
          have := norm_add_le (Z n - w n) (w n - wl)
          linarith
      _ ≤ ε / 4 + ε / 4 + ε / 4 := by
          have h3 : ‖wl - Zl‖ = ‖Zl - wl‖ :=
            norm_sub_rev _ _
          rw [h3]
          exact add_le_add (add_le_add h1 h2.le) hZlwl
      _ < ε := by linarith
  refine ⟨hup, ?_⟩
  intro scr scrl hconv htail
  apply hup
  intro ε hε
  obtain ⟨R, hR1, hR2⟩ := htail ε hε
  exact ⟨scr R, scrl R, hconv R, hR1, hR2⟩

end NCG
