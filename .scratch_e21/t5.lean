import Mathlib
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢]
theorem zs (g : 𝓢 →L[ℝ] ℂ) : (0:ℝ) • g = 0 := by ext w; simp
theorem zs' {ι : Type*} (g : ι → 𝓢 →L[ℝ] ℂ) : (0:ℝ) • g = 0 := by funext i; exact zs (g i)
example (f g : 𝓢 →L[ℝ] ℂ) : f + (0:ℝ) • g = f := by simp [zs]
example {ι : Type*} (f g : ι → (𝓢 →L[ℝ] ℂ)) (i : ι) : (f + (0:ℝ) • g) i = f i := by simp [zs']
