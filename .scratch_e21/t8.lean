import Mathlib
open NormedSpace
variable {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [CompleteSpace 𝔅]
theorem cd : ContDiff ℝ ⊤ (exp : 𝔅 → 𝔅) := by
  have : AnalyticOnNhd ℝ (exp : 𝔅 → 𝔅) Set.univ := fun x _ => exp_analytic x
  exact contDiffOn_univ.1 this.contDiffOn_of_completeSpace
example : Continuous (fderiv ℝ (exp : 𝔅 → 𝔅)) := 
  (cd (𝔅 := 𝔅)).continuous_fderiv (by simp)
