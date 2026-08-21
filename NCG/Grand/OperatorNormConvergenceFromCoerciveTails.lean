import NCG.Grand.OperatorNormConvergenceFromEventualScreens

/-!
# Operator-norm convergence from diverging coercive tails

This is the final quantitative wrapper around the common-screen argument.  A
coercivity floor `μ R` on the complement of the radius-`R` screen gives a
resolvent tail bounded by `1 / (λ + μ R)`.  If those floors diverge, the tails
can be made uniformly small and local screen convergence becomes global
operator-norm convergence.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v

variable {K : Type u} [NontriviallyNormedField K]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace K E]

/-- The fixed-screen convergence compiler with tails supplied by a diverging
coercivity floor. -/
theorem tendsto_operatorNorm_of_screenCompression_coerciveTails
    (Tn : ℕ → E →L[K] E) (T : E →L[K] E)
    (S : ℕ → E →L[K] E) (lam : ℝ) (mu : ℕ → ℝ)
    (hlam : 0 < lam) (hmu : ∀ radius, 0 ≤ mu radius)
    (hmuTop : Tendsto mu atTop atTop)
    (hlocal : ∀ radius,
      Tendsto (fun n ↦ screenCompression (S radius) (Tn n)) atTop
        (𝓝 (screenCompression (S radius) T)))
    (hstageTail : ∀ radius, ∀ᶠ n in atTop,
      ‖Tn n - screenCompression (S radius) (Tn n)‖ ≤
        1 / (lam + mu radius))
    (hlimitTail : ∀ radius,
      ‖screenCompression (S radius) T - T‖ ≤
        1 / (lam + mu radius)) :
    Tendsto Tn atTop (𝓝 T) := by
  apply tendsto_operatorNorm_of_screenCompression_eventualTails Tn T S hlocal
  intro ε hε
  have hdenom : Tendsto (fun radius ↦ lam + mu radius) atTop atTop :=
    Filter.tendsto_atTop_add_const_left atTop lam hmuTop
  have hinv : Tendsto (fun radius ↦ 1 / (lam + mu radius)) atTop (𝓝 0) := by
    simp only [one_div]
    change Tendsto ((fun r : ℝ ↦ r⁻¹) ∘
      (fun radius ↦ lam + mu radius)) atTop (𝓝 0)
    exact tendsto_inv_atTop_zero.comp hdenom
  obtain ⟨radius, hball⟩ := (Metric.tendsto_atTop.mp hinv) ε hε
  have hradius : 1 / (lam + mu radius) < ε := by
    have hradiusDist := hball radius le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hradiusDist
    · exact hradiusDist
    · exact one_div_nonneg.mpr (add_nonneg hlam.le (hmu radius))
  refine ⟨radius, ?_, (hlimitTail radius).trans_lt hradius⟩
  filter_upwards [hstageTail radius] with n hn
  exact hn.trans_lt hradius

end NCG
