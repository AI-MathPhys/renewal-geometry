import NCG.Grand.MeanNoiseShort

/-! # Exact EASY batch 41: quantitative noise-shorted Ward remainders -/

open Matrix
open scoped Norms.L2Operator

namespace NCG

/-- `thm:renewal-noise-shorted-Ward`, exact estimates behind both little-`o`
readings.  If the normalized predictable residual is `X`, its shorted Ward
form has norm exactly `‖X‖²`; after the exact raw split, the deviation from
`τ G_noise` is bounded by that square plus the noise remainder. -/
theorem renewal_noise_shorted_ward_remainder
    {e : Type*} [Fintype e] [DecidableEq e]
    (raw Gn E : Matrix e e ℂ) (X : Matrix e e ℂ) (τ : ℝ)
    (hsplit : raw = (τ : ℂ) • Gn + (Xᴴ * X + E)) :
    ‖raw - (τ : ℂ) • Gn‖ ≤ ‖X‖ ^ 2 + ‖E‖
      ∧ ‖Xᴴ * X‖ = ‖X‖ ^ 2 := by
  have hgram : ‖Xᴴ * X‖ = ‖X‖ ^ 2 := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self]
    ring
  constructor
  · rw [hsplit]
    have heq : (τ : ℂ) • Gn + (Xᴴ * X + E) - (τ : ℂ) • Gn
        = Xᴴ * X + E := by abel
    rw [heq]
    calc
      ‖Xᴴ * X + E‖ ≤ ‖Xᴴ * X‖ + ‖E‖ := norm_add_le _ _
      _ = ‖X‖ ^ 2 + ‖E‖ := by rw [hgram]
  · exact hgram

end NCG
