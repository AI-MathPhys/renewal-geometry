/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTPositiveScreenExact

/-!
# Regenerative screen (exact)

Exact formalization of `cor:SMST-regenerative-screen`: the
fixed-radius screens and uniform tail exhaustion required by
`thm:SMST-positive-screen` need not be separately postulated —
they follow from the quantitative energy tails supplied by the
proved Lyapunov/shorted-Hodge records
(`thm:renewal-Lyapunov-tightness`, `thm:renewal-shorted-Hodge`,
`cor:renewal-spatial-positive-screen`), transferred to the
packet variables by the uniformly faithful Legendre–conductance
comparison.

Derived content:

* `tail_exhaustion_of_energy_tail`: the conversion of a
  quantitative inverse-radius energy tail
  `‖(I - S_{h,R})Z_h‖² ≤ E/(R+1)` into the uniform tail
  exhaustion hypothesis of the screen theorem (an Archimedean
  choice of radius plus the square-root comparison);
* `regenerative_screen_strong_convergence`: the full corollary —
  bounded weakly-convergent packets with Lyapunov-type energy
  tails converge strongly, by applying the proved
  `screen_strong_convergence`; the `𝔸_h^{-1/2}` transfer to the
  physical packets is `strong_convergence_transfer`.

Framework hypotheses (disclosed): the inverse-radius energy
tails are the conclusions of the cited proved records composed
with the uniformly faithful Legendre–conductance comparison
(interface); compactness of the limit screens enters as
complete continuity, as in `thm:SMST-positive-screen`.
-/

open Filter

namespace NCG
namespace SMSTChannel

variable {Y : Type} [NormedAddCommGroup Y]
  [InnerProductSpace ℂ Y]

/-- Quantitative inverse-radius energy tails imply the uniform
tail exhaustion required by the positive-screen theorem. -/
theorem tail_exhaustion_of_energy_tail
    (f : ℕ → ℕ → ℝ) (E : ℝ) (_hE : 0 ≤ E)
    (hf0 : ∀ R n, 0 ≤ f R n)
    (htail : ∀ R n, f R n ^ 2 ≤ E / (R + 1)) :
    ∀ ε > (0 : ℝ), ∃ R₀, ∀ R ≥ R₀, ∀ n, f R n ≤ ε := by
  intro ε hε
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt (E / ε ^ 2)
  refine ⟨R₀, fun R hR n => ?_⟩
  have hR1 : (0 : ℝ) < R + 1 := by positivity
  have hRge : (R₀ : ℝ) ≤ R := by exact_mod_cast hR
  have hkey : E / (R + 1) < ε ^ 2 := by
    have h₁ : E / ε ^ 2 < R + 1 := by
      calc E / ε ^ 2 < R₀ := hR₀
        _ ≤ R := hRge
        _ ≤ R + 1 := by linarith
    have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
    rw [div_lt_iff₀ hε2] at h₁
    rw [div_lt_iff₀ hR1]
    linarith [mul_comm ((R : ℝ) + 1) (ε ^ 2)]
  have hsq : f R n ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt (htail R n) hkey
  have h0 := hf0 R n
  nlinarith

/-- **Regenerative screen**
(`cor:SMST-regenerative-screen`): bounded weakly-convergent
packet families whose screens satisfy Lyapunov-type
inverse-radius energy tails converge strongly — the tail
exhaustion of `thm:SMST-positive-screen` is derived, not
postulated. -/
theorem regenerative_screen_strong_convergence
    (Z : ℕ → Y) (Zlim : Y) (Cb : ℝ)
    (hbdd : ∀ n, ‖Z n‖ ≤ Cb)
    (hweak : WeakTendsto Z Zlim)
    (SR : ℕ → Y →L[ℂ] Y) (Sh : ℕ → ℕ → Y →L[ℂ] Y)
    (hSconv : ∀ R, Tendsto (fun n => ‖Sh R n - SR R‖)
      atTop (nhds 0))
    (hcc : ∀ R (W : ℕ → Y) (Wlim : Y) (Cw : ℝ),
      (∀ n, ‖W n‖ ≤ Cw) → WeakTendsto W Wlim →
      Tendsto (fun n => SR R (W n)) atTop
        (nhds (SR R Wlim)))
    (E : ℝ) (hE : 0 ≤ E)
    (hEtail : ∀ R n, ‖Z n - Sh R n (Z n)‖ ^ 2 ≤ E / (R + 1))
    (hEtailZ : ∀ R, ‖Zlim - SR R Zlim‖ ^ 2 ≤ E / (R + 1)) :
    Tendsto Z atTop (nhds Zlim) := by
  refine screen_strong_convergence Z Zlim Cb hbdd hweak
    SR Sh hSconv hcc ?_ ?_
  · exact tail_exhaustion_of_energy_tail
      (fun R n => ‖Z n - Sh R n (Z n)‖) E hE
      (fun R n => norm_nonneg _) hEtail
  · intro ε hε
    obtain ⟨R₀, hR₀⟩ := tail_exhaustion_of_energy_tail
      (fun R _ => ‖Zlim - SR R Zlim‖) E hE
      (fun R _ => norm_nonneg _) (fun R _ => hEtailZ R) ε hε
    exact ⟨R₀, fun R hR => hR₀ R hR 0⟩

end SMSTChannel
end NCG
