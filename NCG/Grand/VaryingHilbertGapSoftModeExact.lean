/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GapSoftMode
import NCG.Grand.GraphCoreSoftModeApproximation
import NCG.Grand.VaryingHilbertRealMosco

/-!
# Gap passage and soft modes on varying Hilbert carriers

This is the native embedding layer of `thm:gap-soft-mode-alternative`.
Finite-stage vectors remain in their own Hilbert spaces and are compared only
through a `VaryingHilbert.System`; no common-space identification is assumed.
-/

open Filter Topology

noncomputable section

namespace NCG
namespace VaryingHilbertGapSoftModeExact

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)]
  [∀ n, InnerProductSpace K (Hn n)]

/-- The finite transient gap passes through genuine varying-space Mosco
convergence and strong convergence of the kernel projections. -/
theorem varyingHilbert_gap_passage
    (J : NCG.VaryingHilbert.System (K := K) (H := H) (Hn := Hn))
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (E : (n : ℕ) → Hn n →L[K] Hn n) (Einf : H →L[K] H)
    (γ : ℕ → ℝ)
    (hmosco : J.RealMoscoConverges q qlim)
    (hE : J.StrongOperatorConverges J E Einf)
    (hlow : ∀ n u, γ n * ‖u - E n u‖ ^ 2 ≤ q n u)
    (u : H) (c : ℝ) (hc : 0 ≤ c)
    (hev : ∀ᶠ n in atTop, c ≤ γ n) :
    c * ‖u - Einf u‖ ^ 2 ≤ qlim u := by
  obtain ⟨v, hv, hq⟩ := hmosco.recovery u
  have hEv := hE v u hv
  have hdiff : Tendsto
      (fun n => J.embedding n (v n - E n (v n))) atTop
      (𝓝 (u - Einf u)) := by
    simpa only [map_sub] using hv.sub hEv
  have hmass : Tendsto (fun n => ‖v n - E n (v n)‖) atTop
      (𝓝 ‖u - Einf u‖) := by
    simpa only [LinearIsometry.norm_map] using hdiff.norm
  have hleft : Tendsto
      (fun n => c * ‖v n - E n (v n)‖ ^ 2) atTop
      (𝓝 (c * ‖u - Einf u‖ ^ 2)) := (hmass.pow 2).const_mul c
  have hle : ∀ ε > 0,
      c * ‖u - Einf u‖ ^ 2 ≤ qlim u + ε := by
    intro ε hε
    apply le_of_tendsto hleft
    filter_upwards [hev, hq.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε))]
      with n hcn hqn
    calc
      c * ‖v n - E n (v n)‖ ^ 2 ≤
          γ n * ‖v n - E n (v n)‖ ^ 2 := by
        gcongr
      _ ≤ q n (v n) := hlow n (v n)
      _ ≤ qlim u + ε := hqn.le
  by_contra hnot
  have hpos : 0 < (c * ‖u - Einf u‖ ^ 2 - qlim u) / 2 := by
    push_neg at hnot
    linarith
  have := hle _ hpos
  linarith

/-- Collapsing optimal transient gaps produce normalized soft modes without
identifying the finite-stage Hilbert carriers. -/
theorem varyingHilbert_softMode_extraction
    (q : (n : ℕ) → Hn n → ℝ)
    (E : (n : ℕ) → Hn n →L[K] Hn n) (γ : ℕ → ℝ)
    (hγ0 : ∀ n, 0 ≤ γ n)
    (hopt : ∀ n, ∀ ε > 0, ∃ u : Hn n,
      E n u = 0 ∧ ‖u‖ = 1 ∧ q n u < γ n + ε)
    (hlow : ∀ n u, γ n * ‖u - E n u‖ ^ 2 ≤ q n u)
    (σ : ℕ → ℕ)
    (hσ : Tendsto (fun j => γ (σ j)) atTop (𝓝 0)) :
    ∃ v : ∀ j, Hn (σ j),
      (∀ j, E (σ j) (v j) = 0) ∧
      (∀ j, ‖v j‖ = 1) ∧
      Tendsto (fun j => q (σ j) (v j)) atTop (𝓝 0) := by
  have hchoice : ∀ j : ℕ, ∃ u : Hn (σ j),
      E (σ j) u = 0 ∧ ‖u‖ = 1 ∧
        q (σ j) u < γ (σ j) + 1 / (j + 1) :=
    fun j => hopt (σ j) (1 / (j + 1)) (by positivity)
  choose v hv0 hv1 hvq using hchoice
  refine ⟨v, hv0, hv1, ?_⟩
  have hlower : ∀ j, γ (σ j) ≤ q (σ j) (v j) := by
    intro j
    have h := hlow (σ j) (v j)
    rw [hv0 j, sub_zero, hv1 j] at h
    simpa using h
  have hupper : ∀ j, q (σ j) (v j) ≤
      γ (σ j) + 1 / (j + 1) := fun j => (hvq j).le
  have hright : Tendsto (fun j : ℕ => γ (σ j) + 1 / (j + 1))
      atTop (𝓝 0) := by
    simpa using hσ.add tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hσ hright hlower hupper

end VaryingHilbertGapSoftModeExact
end NCG
