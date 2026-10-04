import Mathlib
variable {T U V : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup U] [NormedSpace ℝ U]
#synth NormedAddCommGroup (T →L[ℝ] U →L[ℝ] ℝ)
#synth NormedSpace ℝ (T →L[ℝ] U →L[ℝ] ℝ)
#synth NormedAddCommGroup ((T →L[ℝ] U →L[ℝ] ℝ) →L[ℝ] ℝ)
example : NormedAddCommGroup ((T →L[ℝ] U →L[ℝ] ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
