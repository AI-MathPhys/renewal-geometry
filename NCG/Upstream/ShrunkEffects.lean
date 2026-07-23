/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Shrunk effects: dilation does not imply sharpness

The quantitative core of Proposition
`prop:dilation-does-not-imply-sharpness` (`manuscripts/renewal_emergence/renewal_emergence.tex`):
retaining the states, channels, and dilations of finite quantum
theory but admitting only the `ε`-shrunk effects

`e_{P,ε}(ρ) = ε + (1 − 2ε) Tr(Pρ)`

destroys pure sharpness while leaving the dilation structure
untouched.  We prove the three mathematical claims of the proof:

* `shrunkEffect_le` / `le_shrunkEffect` — **value pinching**: on
  every state (positive semidefinite, unit trace) and projection,
  the shrunk effect takes values in `[ε, 1−ε]`; in particular
  (`shrunkEffect_ne_one`) no shrunk effect is certain on any state;
* `shrunkEffect_separates` — **state separation**: the shrunk
  effects distinguish exactly what the projection pairings
  distinguish, so the modified theory remains reduced;
* `unit_refinement` — **the deterministic effect is not pure**: it
  splits as `u = e_{P,ε} + (u − e_{P,ε})` with both summands pinched
  in `[ε, 1−ε]`, a nontrivial refinement into admitted effects.

The pairing positivity is derived from the factorized form
`Tr((AᴴA)(BᴴB)) = Tr(MᴴM) ≥ 0` with `M = A Bᴴ`
(`pairing_factor_nonneg`), applied to `P = PᴴP` (projections) and to
`1 − P = (1−P)ᴴ(1−P)`.
-/

namespace NCG.Upstream

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of `MᴴM` is the (real, nonnegative) Frobenius square
sum. -/
theorem trace_conjTranspose_mul_self_eq (M : Matrix n n ℂ) :
    (Mᴴ * M).trace
      = ((∑ d : n, ∑ i : n, Complex.normSq (M i d) : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self]

/-- Pairing positivity in factorized form:
`Tr((AᴴA)(BᴴB))` is real and nonnegative. -/
theorem pairing_factor_nonneg (A B : Matrix n n ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ ((Aᴴ * A) * (Bᴴ * B)).trace = (r : ℂ) := by
  refine ⟨∑ d : n, ∑ i : n, Complex.normSq ((A * Bᴴ) i d),
    Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun i _ =>
      Complex.normSq_nonneg _, ?_⟩
  rw [← trace_conjTranspose_mul_self_eq]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc ((Aᴴ * A) * (Bᴴ * B)).trace
      = ((Aᴴ * (A * Bᴴ)) * B).trace := by
        congr 1
        noncomm_ring
    _ = (B * (Aᴴ * (A * Bᴴ))).trace := Matrix.trace_mul_comm _ _
    _ = ((B * Aᴴ) * (A * Bᴴ)).trace := by
        congr 1
        noncomm_ring

/-- The real pairing `Tr(Pρ)` of a state against an operator. -/
noncomputable def pairing (P ρ : Matrix n n ℂ) : ℝ :=
  ((P * ρ).trace).re

/-- Positivity of the pairing of a projection against a state. -/
theorem pairing_nonneg {P ρ : Matrix n n ℂ}
    (hP1 : Pᴴ = P) (hP2 : P * P = P) (hρ : ∃ B, ρ = Bᴴ * B) :
    0 ≤ pairing P ρ := by
  obtain ⟨B, hB⟩ := hρ
  have hPfac : P = Pᴴ * P := by rw [hP1, hP2]
  obtain ⟨r, hr0, hr⟩ := pairing_factor_nonneg P B
  unfold pairing
  rw [hB, hPfac, hr]
  simpa using hr0

/-- The pairing of a projection against a normalized state is at most
one: the complement `1 − P` is again a Hermitian idempotent. -/
theorem pairing_le_one {P ρ : Matrix n n ℂ}
    (hP1 : Pᴴ = P) (hP2 : P * P = P) (hρ : ∃ B, ρ = Bᴴ * B)
    (hτ : ρ.trace = 1) : pairing P ρ ≤ 1 := by
  have h1 : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP1]
  have h2 : (1 - P) * (1 - P) = 1 - P := by
    have h2' : (1 - P) * (1 - P) = 1 - P - P + P * P := by
      noncomm_ring
    rw [h2', hP2]
    noncomm_ring
  have h3 := pairing_nonneg h1 h2 hρ
  have h4 : pairing (1 - P) ρ = 1 - pairing P ρ := by
    unfold pairing
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
      Complex.sub_re, hτ]
    simp
  linarith

/-- **Definition of the shrunk effects**
`e_{P,ε}(ρ) = ε + (1 − 2ε)·Tr(Pρ)`. -/
noncomputable def shrunkEffect (ε : ℝ) (P ρ : Matrix n n ℂ) : ℝ :=
  ε + (1 - 2 * ε) * pairing P ρ

section Pinching

variable {ε : ℝ} {P ρ : Matrix n n ℂ}
variable (hP1 : Pᴴ = P) (hP2 : P * P = P)
variable (hρ : ∃ B, ρ = Bᴴ * B) (hτ : ρ.trace = 1)

include hP1 hP2 hρ hτ

/-- **Value pinching, lower bound**: `ε ≤ e_{P,ε}(ρ)`. -/
theorem le_shrunkEffect (hε2 : ε ≤ 1 / 2) :
    ε ≤ shrunkEffect ε P ρ := by
  unfold shrunkEffect
  have h1 := pairing_nonneg hP1 hP2 hρ
  nlinarith

/-- **Value pinching, upper bound**: `e_{P,ε}(ρ) ≤ 1 − ε`. -/
theorem shrunkEffect_le (hε2 : ε ≤ 1 / 2) :
    shrunkEffect ε P ρ ≤ 1 - ε := by
  unfold shrunkEffect
  have h1 := pairing_nonneg hP1 hP2 hρ
  have h2 := pairing_le_one hP1 hP2 hρ hτ
  nlinarith

/-- **No shrunk effect is certain on any state**: pure sharpness
fails for the admitted non-deterministic effects. -/
theorem shrunkEffect_ne_one (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    shrunkEffect ε P ρ ≠ 1 := by
  have h1 := shrunkEffect_le hP1 hP2 hρ hτ hε2
  intro h
  rw [h] at h1
  linarith

end Pinching

/-- **State separation**: the shrunk effects distinguish exactly what
the projection pairings distinguish (`1 − 2ε ≠ 0`), so the shrunk
theory remains reduced. -/
theorem shrunkEffect_separates {ε : ℝ} (hε : ε ≠ 1 / 2)
    (P ρ σ : Matrix n n ℂ) :
    shrunkEffect ε P ρ = shrunkEffect ε P σ
      ↔ pairing P ρ = pairing P σ := by
  unfold shrunkEffect
  constructor
  · intro h
    have h1 : (1 - 2 * ε) ≠ 0 := by
      intro hc
      exact hε (by linarith)
    have h2 : (1 - 2 * ε) * pairing P ρ
        = (1 - 2 * ε) * pairing P σ := by linarith
    exact mul_left_cancel₀ h1 h2
  · intro h
    rw [h]

/-- **The deterministic effect is refinable**: `u = e_{P,ε} +
(u − e_{P,ε})` with both summands pinched in `[ε, 1 − ε]` — a
nontrivial decomposition into admitted nonzero effects, so `u` is
not pure in the operational non-refinability sense and no pure
effect of the shrunk theory is certain on a normalized pure
state. -/
theorem unit_refinement {ε : ℝ} {P ρ : Matrix n n ℂ}
    (hP1 : Pᴴ = P) (hP2 : P * P = P) (hρ : ∃ B, ρ = Bᴴ * B)
    (hτ : ρ.trace = 1) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (1 : ℝ) = shrunkEffect ε P ρ + (1 - shrunkEffect ε P ρ)
      ∧ ε ≤ shrunkEffect ε P ρ
      ∧ shrunkEffect ε P ρ ≤ 1 - ε
      ∧ ε ≤ 1 - shrunkEffect ε P ρ
      ∧ 1 - shrunkEffect ε P ρ ≤ 1 - ε := by
  have h1 := le_shrunkEffect hP1 hP2 hρ hτ hε2
  have h2 := shrunkEffect_le hP1 hP2 hρ hτ hε2
  refine ⟨by ring, h1, h2, by linarith, by linarith⟩

end NCG.Upstream
