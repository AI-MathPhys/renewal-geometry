import Mathlib
variable {T U V : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
example (f : ((V →L[ℝ] V) →L[ℝ] ℝ) →L[ℝ] ℝ) : ‖f‖ = ‖f‖ := rfl
example (f : ((V →L[ℝ] ℂ) →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] ℝ) : ‖f‖ = ‖f‖ := rfl
set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 4096 in
example (f : (T →L[ℝ] U →L[ℝ] ℝ) →L[ℝ] ℝ) : ‖f‖ = ‖f‖ := rfl
example (f : (T →L[ℝ] U →L[ℝ] ℝ) →L[ℝ] ℝ) : ‖f‖ = ‖f‖ :=
  @rfl _ (@Norm.norm _ (@ContinuousLinearMap.hasOpNorm ℝ ℝ (T →L[ℝ] U →L[ℝ] ℝ) ℝ _ _ _ _ _ _ _ _) f)
