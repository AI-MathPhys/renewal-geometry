import Mathlib
variable {T U : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup U] [NormedSpace ℝ U]
example (f : (T →L[ℝ] ℝ) →L[ℝ] ℝ) : ‖f‖ = ‖f‖ := rfl
example (f : (T →L[ℝ] U) →L[ℝ] U) : ‖f‖ = ‖f‖ := rfl
example (f : (T →L[ℝ] U →L[ℝ] ℝ) →L[ℝ] ℝ) : ‖f‖ = ‖f‖ := rfl
example (f : (U →L[ℝ] ℝ) →L[ℝ] (U →L[ℝ] ℝ)) : ‖f‖ = ‖f‖ := rfl
example (f : (T →L[ℝ] U →L[ℝ] ℝ) →L[ℝ] (U →L[ℝ] ℝ)) : ‖f‖ = ‖f‖ := rfl
