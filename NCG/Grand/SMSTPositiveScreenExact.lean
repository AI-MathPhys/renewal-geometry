/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Positive-screen strong convergence (exact)

Exact formalization of `thm:SMST-positive-screen`: on the
cylinder Hilbert space `𝒴_K`, a bounded weakly-convergent
family `Z_h ⇀ Z` with uniformly small screen tails converges
**strongly**, and the physical packets
`Y_h = 𝔸_h^{-1/2} Z_h` converge strongly as well.

Derived content (the manuscript's proof, in full):

* `screen_strong_convergence`: the double-limit ε/4 assembly of
  `Z_h - Z = (I - S_{h,R})Z_h + (S_{h,R} - S_R)Z_h
  + (S_R Z_h - S_R Z) + (S_R - I)Z` — the operator-norm
  convergence `‖S_{h,R} - S_R‖ → 0` is converted to vector
  convergence on the bounded family, the screen tails are made
  uniformly small by choosing `R`, and the compact-screen images
  converge; the limit interchange is carried out exactly;
* `strong_convergence_transfer`: the `𝔸_h^{-1/2}` leg — a
  uniformly bounded, strongly convergent operator family maps
  strongly convergent sequences to strongly convergent
  sequences, giving `Y_h → Y` from `Z_h → Z`.

Framework hypothesis (disclosed): compactness of the limit
screens `S_R` enters as **complete continuity** — `S_R` maps
bounded weakly-convergent sequences to norm-convergent ones —
which is equivalent to compactness for operators on a Hilbert
space; the discretization family is indexed by a sequence.
-/

open Filter

namespace NCG
namespace SMSTChannel

variable {Y : Type} [NormedAddCommGroup Y]
  [InnerProductSpace ℂ Y]

/-- Weak convergence of a sequence in a Hilbert space. -/
def WeakTendsto (Z : ℕ → Y) (Zlim : Y) : Prop :=
  ∀ y : Y, Tendsto (fun n => inner ℂ y (Z n)) atTop
    (nhds (inner ℂ y Zlim))

/-- **Positive-screen strong convergence**
(`thm:SMST-positive-screen`, core clause): a bounded weakly
convergent family with uniformly small screen tails converges
strongly.  Compactness of the limit screens enters as complete
continuity (`hcc`), its Hilbert-space characterization. -/
theorem screen_strong_convergence
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
    (htail : ∀ ε > (0 : ℝ), ∃ R₀, ∀ R ≥ R₀, ∀ n,
      ‖Z n - Sh R n (Z n)‖ ≤ ε)
    (htailZ : ∀ ε > (0 : ℝ), ∃ R₀, ∀ R ≥ R₀,
      ‖Zlim - SR R Zlim‖ ≤ ε) :
    Tendsto Z atTop (nhds Zlim) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 8 := by linarith
  -- choose a radius with both tails below ε/8
  obtain ⟨R₁, hR₁⟩ := htail (ε / 8) hε4
  obtain ⟨R₂, hR₂⟩ := htailZ (ε / 8) hε4
  set R := max R₁ R₂ with hR
  have htail₁ : ∀ n, ‖Z n - Sh R n (Z n)‖ ≤ ε / 8 :=
    hR₁ R (le_max_left _ _)
  have htail₂ : ‖Zlim - SR R Zlim‖ ≤ ε / 8 :=
    hR₂ R (le_max_right _ _)
  -- operator-norm convergence beats the uniform bound
  have hCb0 : (0 : ℝ) ≤ Cb := (norm_nonneg (Z 0)).trans (hbdd 0)
  have hmid : Tendsto (fun n => ‖Sh R n - SR R‖ * Cb)
      atTop (nhds 0) := by
    have := (hSconv R).mul_const Cb
    simpa using this
  have hmid' : ∀ᶠ n in atTop,
      ‖Sh R n (Z n) - SR R (Z n)‖ < ε / 4 := by
    have hev := (Metric.tendsto_atTop.mp hmid) (ε / 4)
      (by linarith)
    obtain ⟨N, hN⟩ := hev
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have h₁ := hN n hn
    rw [Real.dist_eq, sub_zero] at h₁
    have h₂ : ‖Sh R n (Z n) - SR R (Z n)‖
        ≤ ‖Sh R n - SR R‖ * Cb := by
      have h₃ : Sh R n (Z n) - SR R (Z n)
          = (Sh R n - SR R) (Z n) := by
        simp
      rw [h₃]
      calc ‖(Sh R n - SR R) (Z n)‖
          ≤ ‖Sh R n - SR R‖ * ‖Z n‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖Sh R n - SR R‖ * Cb :=
            mul_le_mul_of_nonneg_left (hbdd n)
              (norm_nonneg _)
    calc ‖Sh R n (Z n) - SR R (Z n)‖
        ≤ ‖Sh R n - SR R‖ * Cb := h₂
      _ ≤ |‖Sh R n - SR R‖ * Cb| := le_abs_self _
      _ < ε / 4 := h₁
  -- compact-screen images converge
  have hcompact := hcc R Z Zlim Cb hbdd hweak
  have hcompact' : ∀ᶠ n in atTop,
      ‖SR R (Z n) - SR R Zlim‖ < ε / 4 := by
    have hev := (Metric.tendsto_atTop.mp hcompact) (ε / 4)
      (by linarith)
    obtain ⟨N, hN⟩ := hev
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rwa [dist_eq_norm] at this
  -- assemble
  have hfinal : ∀ᶠ n in atTop, dist (Z n) Zlim < ε := by
    filter_upwards [hmid', hcompact'] with n h₁ h₂
    rw [dist_eq_norm]
    have hsplit : Z n - Zlim
        = (Z n - Sh R n (Z n))
          + (Sh R n (Z n) - SR R (Z n))
          + (SR R (Z n) - SR R Zlim)
          + (SR R Zlim - Zlim) := by
      abel
    rw [hsplit]
    have t₁ := htail₁ n
    have t₂ : ‖SR R Zlim - Zlim‖ ≤ ε / 8 := by
      rw [← norm_neg]
      have h : -(SR R Zlim - Zlim) = Zlim - SR R Zlim := by
        abel
      rw [h]
      exact htail₂
    have n₁ := norm_add_le
      ((Z n - Sh R n (Z n)) + (Sh R n (Z n) - SR R (Z n))
        + (SR R (Z n) - SR R Zlim))
      (SR R Zlim - Zlim)
    have n₂ := norm_add_le
      ((Z n - Sh R n (Z n)) + (Sh R n (Z n) - SR R (Z n)))
      (SR R (Z n) - SR R Zlim)
    have n₃ := norm_add_le (Z n - Sh R n (Z n))
      (Sh R n (Z n) - SR R (Z n))
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfinal
  exact ⟨N, hN⟩

/-- **Strong-convergence transfer** (the `𝔸_h^{-1/2}` leg of
`thm:SMST-positive-screen`): a uniformly bounded, strongly
convergent operator family maps strongly convergent sequences
to strongly convergent sequences, so `Y_h = 𝔸_h^{-1/2}Z_h → Y`
once `Z_h → Z`. -/
theorem strong_convergence_transfer
    (B : ℕ → Y →L[ℂ] Y) (Blim : Y →L[ℂ] Y) (Cm : ℝ)
    (hBbdd : ∀ n, ‖B n‖ ≤ Cm)
    (hBstrong : ∀ v : Y, Tendsto (fun n => B n v) atTop
      (nhds (Blim v)))
    (Z : ℕ → Y) (Zlim : Y)
    (hZ : Tendsto Z atTop (nhds Zlim)) :
    Tendsto (fun n => B n (Z n)) atTop
      (nhds (Blim Zlim)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hCm0 : (0 : ℝ) ≤ Cm := (norm_nonneg (B 0)).trans (hBbdd 0)
  have hCm1 : (0 : ℝ) < Cm + 1 := by linarith
  -- Z_n close to Zlim
  have hZev : ∀ᶠ n in atTop,
      ‖Z n - Zlim‖ < ε / (2 * (Cm + 1)) := by
    have hev := (Metric.tendsto_atTop.mp hZ)
      (ε / (2 * (Cm + 1))) (by positivity)
    obtain ⟨N, hN⟩ := hev
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rwa [dist_eq_norm] at this
  -- B_n Zlim close to Blim Zlim
  have hBev : ∀ᶠ n in atTop,
      ‖B n Zlim - Blim Zlim‖ < ε / 2 := by
    have hev := (Metric.tendsto_atTop.mp (hBstrong Zlim))
      (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ := hev
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rwa [dist_eq_norm] at this
  have hfinal : ∀ᶠ n in atTop,
      dist (B n (Z n)) (Blim Zlim) < ε := by
    filter_upwards [hZev, hBev] with n h₁ h₂
    rw [dist_eq_norm]
    have hsplit : B n (Z n) - Blim Zlim
        = B n (Z n - Zlim) + (B n Zlim - Blim Zlim) := by
      rw [map_sub]
      abel
    rw [hsplit]
    have t₁ : ‖B n (Z n - Zlim)‖ < ε / 2 := by
      calc ‖B n (Z n - Zlim)‖
          ≤ ‖B n‖ * ‖Z n - Zlim‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ Cm * ‖Z n - Zlim‖ :=
            mul_le_mul_of_nonneg_right (hBbdd n)
              (norm_nonneg _)
        _ ≤ (Cm + 1) * ‖Z n - Zlim‖ := by
            have := norm_nonneg (Z n - Zlim)
            nlinarith
        _ < (Cm + 1) * (ε / (2 * (Cm + 1))) := by
            refine mul_lt_mul_of_pos_left h₁ hCm1
        _ = ε / 2 := by
            field_simp
    have hntri := norm_add_le (B n (Z n - Zlim))
      (B n Zlim - Blim Zlim)
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfinal
  exact ⟨N, hN⟩

end SMSTChannel
end NCG
