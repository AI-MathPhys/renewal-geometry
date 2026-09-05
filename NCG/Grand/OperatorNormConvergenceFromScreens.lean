/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Operator-norm convergence from fixed screens and uniform tails

This file packages the finite-box plus tail argument used for Fourier
multipliers and compact-resolvent approximations.  Once both the approximating
operators and the limit are uniformly close to one common screened
compression, operator-norm convergence on that screen upgrades to global
operator-norm convergence.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v

variable {K : Type u} [NontriviallyNormedField K]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace K E]

/-- Compress an operator on both sides by a common screen. -/
def screenCompression (S T : E →L[K] E) : E →L[K] E :=
  S.comp (T.comp S)

/-- Quantitative three-term screen decomposition. -/
theorem norm_sub_le_screenCompression
    (S T U : E →L[K] E) :
    ‖T - U‖ ≤
      ‖T - screenCompression S T‖ +
        ‖screenCompression S T - screenCompression S U‖ +
          ‖screenCompression S U - U‖ := by
  have hsplit :
      T - U =
        (T - screenCompression S T) +
          (screenCompression S T - screenCompression S U) +
            (screenCompression S U - U) := by
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) (le_refl _))

/-- A two-sided screen tail is controlled by the output tail and the screened
input tail.  This is the convenient form for Fourier multiplier estimates. -/
theorem norm_sub_screenCompression_le_input_output
    (S T : E →L[K] E) :
    ‖T - screenCompression S T‖ ≤
      ‖T - S.comp T‖ + ‖S‖ * ‖T - T.comp S‖ := by
  have hsplit :
      T - screenCompression S T =
        (T - S.comp T) + S.comp (T - T.comp S) := by
    ext x
    change T x - S (T (S x)) = (T x - S (T x)) + S (T x - T (S x))
    rw [map_sub]
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans
    (add_le_add (le_refl _) (ContinuousLinearMap.opNorm_comp_le _ _))

/-- Local operator-norm convergence on every fixed screen, together with one
common screen making the approximating and limiting tails uniformly small,
implies global operator-norm convergence. -/
theorem tendsto_operatorNorm_of_screenCompression
    (Tn : ℕ → E →L[K] E) (T : E →L[K] E)
    (S : ℕ → E →L[K] E)
    (hlocal : ∀ radius,
      Tendsto (fun n ↦ screenCompression (S radius) (Tn n)) atTop
        (𝓝 (screenCompression (S radius) T)))
    (htail : ∀ ε > 0, ∃ radius,
      (∀ n, ‖Tn n - screenCompression (S radius) (Tn n)‖ < ε) ∧
        ‖screenCompression (S radius) T - T‖ < ε) :
    Tendsto Tn atTop (𝓝 T) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨radius, htailN, htailT⟩ := htail (ε / 3) hε3
  obtain ⟨N, hmid⟩ :=
    (Metric.tendsto_atTop.mp (hlocal radius)) (ε / 3) hε3
  refine ⟨N, fun n hnN ↦ ?_⟩
  have hn := hmid n hnN
  rw [dist_eq_norm] at hn ⊢
  have hbound := norm_sub_le_screenCompression (S radius) (Tn n) T
  linarith [htailN n]

/-- Sequential epsilon form of
`tendsto_operatorNorm_of_screenCompression`, convenient for Fourier boxes. -/
theorem eventually_norm_sub_lt_of_screenCompression
    (Tn : ℕ → E →L[K] E) (T : E →L[K] E)
    (S : ℕ → E →L[K] E)
    (hlocal : ∀ radius,
      Tendsto (fun n ↦ screenCompression (S radius) (Tn n)) atTop
        (𝓝 (screenCompression (S radius) T)))
    (htail : ∀ ε > 0, ∃ radius,
      (∀ n, ‖Tn n - screenCompression (S radius) (Tn n)‖ < ε) ∧
        ‖screenCompression (S radius) T - T‖ < ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖Tn n - T‖ < ε := by
  have hconv := tendsto_operatorNorm_of_screenCompression Tn T S hlocal htail
  have hdist := (Metric.tendsto_atTop.mp hconv) ε hε
  exact eventually_atTop.mpr ⟨hdist.choose, fun n hn ↦ by
    simpa only [dist_eq_norm] using
      hdist.choose_spec n hn⟩

end NCG
