/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Translation Kato inequality (`lem:translation-Kato`, Einstein–SM action closure)

Setting.  Points of the chart form an additive group `M` (for the paper,
`M = ℝ⁴` or a periodic box, and the displacement is `a = s e_μ`).  The
bundle fibre is a Hilbert space `H` over `𝕜 = ℝ` or `ℂ`, the structure
group is `G`, and a unitary bundle representation is a map
`ρ : G → (H →L[𝕜] H)` taking values in `unitary (H →L[𝕜] H)`.  The
parallel transport from `x + a` back to `x` is `P x : G`, and the
covariant translation `eq:continuum-covariant-translation` is
`𝒯 Y (x) = ρ(P x) (Y (x + a))` (`katoCovariantTranslation`).

* `translation_kato_of_isometry` — the reverse-triangle argument for any
  fibre map preserving norms;
* `translation_kato` — `eq:translation-Kato`:
  `| ‖Y(x + a)‖ - ‖Y x‖ | ≤ ‖𝒯 Y (x) - Y x‖`;
* `translation_kato_eLpNorm` — the "thus" clause: for every exponent `p`
  and measure, the ordinary `Lᵖ` translation modulus of the magnitude
  `|Y|` is bounded by the covariant `Lᵖ` translation modulus (in
  particular for `p = 2`), so a vanishing covariant modulus forces a
  vanishing ordinary modulus of `|Y|` (`translation_kato_modulus_tendsto`).
-/

namespace RenewalGeometry

open MeasureTheory Filter Topology

section TranslationKato

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {M G : Type*} [AddGroup M]

/-- The continuum covariant translation `𝒯^A_{μ,s} Y (x) = ρ(P(x)) Y(x + s e_μ)`
(`eq:continuum-covariant-translation`), with displacement `a = s e_μ` and
parallel transport `P x` from `x + a` back to `x`. -/
def katoCovariantTranslation (ρ : G → H →L[𝕜] H) (P : M → G) (a : M)
    (Y : M → H) (x : M) : H :=
  ρ (P x) (Y (x + a))

/-- Reverse triangle inequality with a norm-preserving fibre map `U`:
`| ‖y‖ - ‖w‖ | ≤ ‖U y - w‖` (core of `lem:translation-Kato`). -/
theorem translation_kato_of_isometry {E : Type*} [SeminormedAddCommGroup E]
    (U : E → E) (hU : ∀ y, ‖U y‖ = ‖y‖) (y w : E) :
    |‖y‖ - ‖w‖| ≤ ‖U y - w‖ := by
  rw [← hU y]
  exact abs_norm_sub_norm_le (U y) w

/-- `lem:translation-Kato`, `eq:translation-Kato`: for a unitary bundle
representation, `| |Y(x + s e_μ)| - |Y(x)| | ≤ |𝒯^A_{μ,s} Y(x) - Y(x)|`. -/
theorem translation_kato (ρ : G → H →L[𝕜] H)
    (hρ : ∀ g, ρ g ∈ unitary (H →L[𝕜] H)) (P : M → G) (a : M) (Y : M → H)
    (x : M) :
    |‖Y (x + a)‖ - ‖Y x‖| ≤ ‖katoCovariantTranslation ρ P a Y x - Y x‖ :=
  translation_kato_of_isometry (ρ (P x))
    (fun y => ContinuousLinearMap.norm_map_of_mem_unitary (hρ (P x)) y) (Y (x + a)) (Y x)

/-- `lem:translation-Kato`, integrated ("thus") form: for every exponent `p`
and every measure, the `Lᵖ` norm of the ordinary translation difference of
the magnitude `|Y|` is at most the `Lᵖ` covariant translation modulus. -/
theorem translation_kato_eLpNorm [MeasurableSpace M] (ρ : G → H →L[𝕜] H)
    (hρ : ∀ g, ρ g ∈ unitary (H →L[𝕜] H)) (P : M → G) (a : M) (Y : M → H)
    (p : ENNReal) (μ : Measure M) :
    eLpNorm (fun x => ‖Y (x + a)‖ - ‖Y x‖) p μ ≤
      eLpNorm (fun x => katoCovariantTranslation ρ P a Y x - Y x) p μ := by
  refine eLpNorm_mono fun x => ?_
  rw [Real.norm_eq_abs]
  exact translation_kato ρ hρ P a Y x

/-- `lem:translation-Kato`, consequence: along any family of displacements
`a n` (with transports `P n`) whose covariant `Lᵖ` translation modulus of `Y`
tends to zero, the ordinary `Lᵖ` translation modulus of `|Y|` tends to zero. -/
theorem translation_kato_modulus_tendsto [MeasurableSpace M] {ι : Type*}
    {l : Filter ι} (ρ : G → H →L[𝕜] H)
    (hρ : ∀ g, ρ g ∈ unitary (H →L[𝕜] H)) (P : ι → M → G) (a : ι → M) (Y : M → H)
    (p : ENNReal) (μ : Measure M)
    (hcov : Tendsto (fun n =>
      eLpNorm (fun x => katoCovariantTranslation ρ (P n) (a n) Y x - Y x) p μ) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => ‖Y (x + a n)‖ - ‖Y x‖) p μ) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcov
    (fun _ => zero_le) (fun n => translation_kato_eLpNorm ρ hρ (P n) (a n) Y p μ)

end TranslationKato

end RenewalGeometry
