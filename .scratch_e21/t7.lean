import Mathlib
variable {E F A W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup W]
  [NormedSpace ℝ W]
set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 1000 in
example : NNNorm (E →L[ℝ] F →L[ℝ] A →L[ℝ] W) := inferInstance
example : NNNorm (E →L[ℝ] (F →L[ℝ] A →L[ℝ] W)) := ContinuousLinearMap.hasOpNorm.toNNNorm
