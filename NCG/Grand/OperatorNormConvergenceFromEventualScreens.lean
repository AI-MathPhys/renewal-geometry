import NCG.Grand.OperatorNormConvergenceFromScreens

/-!
# Operator-norm convergence from eventual screen tails

Changing finite Fourier spaces contain any fixed screen only eventually.  The
standard three-term screen proof therefore needs no tail estimate at the
finitely many early stages.  This file records that eventual version of the
screen convergence compiler.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v

variable {K : Type u} [NontriviallyNormedField K]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace K E]

/-- Local convergence on each fixed screen and eventually uniform stage
tails, together with a small limit tail, imply global operator-norm
convergence. -/
theorem tendsto_operatorNorm_of_screenCompression_eventualTails
    (Tn : ℕ → E →L[K] E) (T : E →L[K] E)
    (S : ℕ → E →L[K] E)
    (hlocal : ∀ radius,
      Tendsto (fun n ↦ screenCompression (S radius) (Tn n)) atTop
        (𝓝 (screenCompression (S radius) T)))
    (htail : ∀ ε > 0, ∃ radius,
      (∀ᶠ n in atTop,
        ‖Tn n - screenCompression (S radius) (Tn n)‖ < ε) ∧
      ‖screenCompression (S radius) T - T‖ < ε) :
    Tendsto Tn atTop (𝓝 T) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨radius, htailN, htailT⟩ := htail (ε / 3) hε3
  obtain ⟨Ntail, htailN'⟩ := eventually_atTop.mp htailN
  obtain ⟨Nlocal, hlocal'⟩ :=
    (Metric.tendsto_atTop.mp (hlocal radius)) (ε / 3) hε3
  refine ⟨max Ntail Nlocal, fun n hn ↦ ?_⟩
  have hnTail := htailN' n ((le_max_left _ _).trans hn)
  have hnLocal := hlocal' n ((le_max_right _ _).trans hn)
  rw [dist_eq_norm] at hnLocal ⊢
  have hbound := norm_sub_le_screenCompression (S radius) (Tn n) T
  linarith

/-- Sequential epsilon form of
`tendsto_operatorNorm_of_screenCompression_eventualTails`. -/
theorem eventually_norm_sub_lt_of_screenCompression_eventualTails
    (Tn : ℕ → E →L[K] E) (T : E →L[K] E)
    (S : ℕ → E →L[K] E)
    (hlocal : ∀ radius,
      Tendsto (fun n ↦ screenCompression (S radius) (Tn n)) atTop
        (𝓝 (screenCompression (S radius) T)))
    (htail : ∀ ε > 0, ∃ radius,
      (∀ᶠ n in atTop,
        ‖Tn n - screenCompression (S radius) (Tn n)‖ < ε) ∧
      ‖screenCompression (S radius) T - T‖ < ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖Tn n - T‖ < ε := by
  have hconv := tendsto_operatorNorm_of_screenCompression_eventualTails
    Tn T S hlocal htail
  have hdist := (Metric.tendsto_atTop.mp hconv) ε hε
  exact eventually_atTop.mpr ⟨hdist.choose, fun n hn ↦ by
    simpa only [dist_eq_norm] using hdist.choose_spec n hn⟩

end NCG
