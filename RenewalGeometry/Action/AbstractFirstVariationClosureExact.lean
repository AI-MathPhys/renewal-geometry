/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# First-variation closure (`thm:abstract-closure`, Einstein–SM action closure)

Abstract setting of the lemma.

* `X` is the class of reconstructed configurations; its "specified sequential
  convergence" is an arbitrary relation `conv : (ℕ → X) → X → Prop`
  (only used in the accumulation-point clause).
* `V` is the normed space of physical tests (completeness is never used, so
  the Banach hypothesis of the paper is not needed), and the continuum
  first variation is a map `DS : X → (V →L[ℝ] ℝ)` into the dual; the dual
  norm `‖·‖_{𝒱_K^*}` is the operator norm.
* At cutoff `h` the finite action is `Sh h : W h → ℝ` on a normed space
  `W h`, its first variation at the finite record `zd h` is the Fréchet
  derivative `fderiv ℝ (Sh h) (zd h)`, the linear test lift is
  `I h : V →ₗ[ℝ] W h`, and the reconstruction is `R h : W h → X`, so
  `z_h = R_h z_h^d`.

Results:

* `abstract_first_variation_closure` — `eq:abstract-closure`:
  `‖DS(z)‖ ≤ ε_h(K) + c_h(K) + ω_h(K)` under the budgets
  `eq:abstract-budgets` (stated for all `‖v‖ ≤ 1`, i.e. as bounds on the
  suprema) with `ω_h(K) = ‖DS(z_h) - DS(z)‖`;
* `abstract_first_variation_closure_stationary` — the "in particular"
  clause: if `ω_h → 0` and `c_h + ε_h → 0` then `DS(z) = 0`;
* `abstract_first_variation_closure_accumulation` — every accumulation point
  (limit of a convergent subsequence) is stationary, when the hypotheses
  hold along every convergent subsequence (no continuity of `DS` is assumed
  beyond `ω → 0` along those subsequences);
* `abstract_first_variation_closure_exists_stationary` — with sequential
  precompactness, an accumulation point exists and is stationary;
* `abstract_first_variation_closure_defect` — the stationarity budget can be
  taken to be the defect `stationarityDefect`-style supremum
  `ε_h(K) = sup_{‖v‖≤1} |DS_h(z_h^d)[I_h v]|`.
-/

namespace RenewalGeometry

open Filter Topology

section AbstractFirstVariationClosure

variable {X V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {W : ℕ → Type*} [∀ h, NormedAddCommGroup (W h)] [∀ h, NormedSpace ℝ (W h)]

/-- `thm:abstract-closure`, estimate `eq:abstract-closure` at one cutoff `h`:
if the finite first variation `DS_h(z_h^d)[I_h v]` is within `c` of
`DS(z_h)[v]` and bounded by `ε` on the unit ball of tests, then
`‖DS(z)‖ ≤ ε + c + ‖DS(z_h) - DS(z)‖`. -/
theorem abstract_first_variation_closure_single
    (DSz DSzh : V →L[ℝ] ℝ) (Φ : V → ℝ) (c ε : ℝ)
    (hcons : ∀ v : V, ‖v‖ ≤ 1 → |Φ v - DSzh v| ≤ c)
    (hstat : ∀ v : V, ‖v‖ ≤ 1 → |Φ v| ≤ ε) :
    ‖DSz‖ ≤ ε + c + ‖DSzh - DSz‖ := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hstat 0 (by simp))
  have hc : 0 ≤ c := le_trans (abs_nonneg _) (hcons 0 (by simp))
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) ?_
  intro v hv
  have hv1 : ‖v‖ ≤ 1 := hv.le
  have hω : |DSzh v - DSz v| ≤ ‖DSzh - DSz‖ := by
    have := (DSzh - DSz).le_opNorm v
    rw [hv, mul_one] at this
    simpa [Real.norm_eq_abs] using this
  have h1 := hcons v hv1
  have h2 := hstat v hv1
  rw [Real.norm_eq_abs]
  calc |DSz v| = |Φ v - (Φ v - DSzh v) - (DSzh v - DSz v)| := by ring_nf
    _ ≤ |Φ v| + |Φ v - DSzh v| + |DSzh v - DSz v| := by
        have := abs_sub (Φ v - (Φ v - DSzh v)) (DSzh v - DSz v)
        have := abs_sub (Φ v) (Φ v - DSzh v)
        linarith
    _ ≤ ε + c + ‖DSzh - DSz‖ := by linarith

/-- `thm:abstract-closure`, `eq:abstract-closure`, in the variables of the
paper: `S_h` differentiable finite actions (first variation = Fréchet
derivative at the finite record `z_h^d`), `z_h = R_h z_h^d`, linear test
lifts `I_h`, budgets `eq:abstract-budgets` and
`ω_h(K) = ‖DS(z_h) - DS(z)‖`. -/
theorem abstract_first_variation_closure
    (DS : X → (V →L[ℝ] ℝ)) (z : X)
    (Sh : ∀ h, W h → ℝ) (zd : ∀ h, W h) (R : ∀ h, W h → X)
    (I : ∀ h, V →ₗ[ℝ] W h) (c ε : ℕ → ℝ)
    (hcons : ∀ h, ∀ v : V, ‖v‖ ≤ 1 →
      |fderiv ℝ (Sh h) (zd h) (I h v) - DS (R h (zd h)) v| ≤ c h)
    (hstat : ∀ h, ∀ v : V, ‖v‖ ≤ 1 → |fderiv ℝ (Sh h) (zd h) (I h v)| ≤ ε h)
    (h : ℕ) :
    ‖DS z‖ ≤ ε h + c h + ‖DS (R h (zd h)) - DS z‖ :=
  abstract_first_variation_closure_single (DS z) (DS (R h (zd h)))
    (fun v => fderiv ℝ (Sh h) (zd h) (I h v)) (c h) (ε h) (hcons h) (hstat h)

/-- `thm:abstract-closure`, "in particular": if `ω_h(K) → 0` (the
continuity hypothesis `eq:abstract-continuity`) and `c_h(K) + ε_h(K) → 0`,
then `DS(z) = 0`. -/
theorem abstract_first_variation_closure_stationary
    (DS : X → (V →L[ℝ] ℝ)) (z : X)
    (Sh : ∀ h, W h → ℝ) (zd : ∀ h, W h) (R : ∀ h, W h → X)
    (I : ∀ h, V →ₗ[ℝ] W h) (c ε : ℕ → ℝ)
    (hω : Tendsto (fun h => ‖DS (R h (zd h)) - DS z‖) atTop (𝓝 0))
    (hcons : ∀ h, ∀ v : V, ‖v‖ ≤ 1 →
      |fderiv ℝ (Sh h) (zd h) (I h v) - DS (R h (zd h)) v| ≤ c h)
    (hstat : ∀ h, ∀ v : V, ‖v‖ ≤ 1 → |fderiv ℝ (Sh h) (zd h) (I h v)| ≤ ε h)
    (hce : Tendsto (fun h => c h + ε h) atTop (𝓝 0)) :
    DS z = 0 := by
  have hbound : ∀ h, ‖DS z‖ ≤ (c h + ε h) + ‖DS (R h (zd h)) - DS z‖ := by
    intro h
    have := abstract_first_variation_closure DS z Sh zd R I c ε hcons hstat h
    linarith
  have hlim : Tendsto (fun h => (c h + ε h) + ‖DS (R h (zd h)) - DS z‖)
      atTop (𝓝 0) := by simpa using hce.add hω
  have hle : ‖DS z‖ ≤ 0 := ge_of_tendsto' hlim hbound
  exact norm_le_zero_iff.mp hle

/-- `thm:abstract-closure`, last clause: every accumulation point of the
reconstructed family `z_h = R_h z_h^d` (for the specified sequential
convergence `conv`) is a stationary configuration, provided the
hypotheses `eq:abstract-continuity` and `c + ε → 0` hold along every
convergent subsequence. The budgets `eq:abstract-budgets` are cutoff-wise. -/
theorem abstract_first_variation_closure_accumulation
    (conv : (ℕ → X) → X → Prop)
    (DS : X → (V →L[ℝ] ℝ))
    (Sh : ∀ h, W h → ℝ) (zd : ∀ h, W h) (R : ∀ h, W h → X)
    (I : ∀ h, V →ₗ[ℝ] W h) (c ε : ℕ → ℝ)
    (hcons : ∀ h, ∀ v : V, ‖v‖ ≤ 1 →
      |fderiv ℝ (Sh h) (zd h) (I h v) - DS (R h (zd h)) v| ≤ c h)
    (hstat : ∀ h, ∀ v : V, ‖v‖ ≤ 1 → |fderiv ℝ (Sh h) (zd h) (I h v)| ≤ ε h)
    (hsub : ∀ (φ : ℕ → ℕ) (z : X), StrictMono φ →
      conv (fun k => R (φ k) (zd (φ k))) z →
      Tendsto (fun k => ‖DS (R (φ k) (zd (φ k))) - DS z‖) atTop (𝓝 0) ∧
      Tendsto (fun k => c (φ k) + ε (φ k)) atTop (𝓝 0))
    (φ : ℕ → ℕ) (z : X) (hφ : StrictMono φ)
    (hconv : conv (fun k => R (φ k) (zd (φ k))) z) :
    DS z = 0 := by
  obtain ⟨hω, hce⟩ := hsub φ z hφ hconv
  exact abstract_first_variation_closure_stationary (W := fun k => W (φ k)) DS z
    (fun k => Sh (φ k)) (fun k => zd (φ k)) (fun k => R (φ k)) (fun k => I (φ k))
    (fun k => c (φ k)) (fun k => ε (φ k)) hω (fun k => hcons (φ k))
    (fun k => hstat (φ k)) hce

/-- `thm:abstract-closure`, last clause with sequential precompactness:
if the reconstructed family has a convergent subsequence (for `conv`), then
it has an accumulation point, and every accumulation point is stationary. -/
theorem abstract_first_variation_closure_exists_stationary
    (conv : (ℕ → X) → X → Prop)
    (DS : X → (V →L[ℝ] ℝ))
    (Sh : ∀ h, W h → ℝ) (zd : ∀ h, W h) (R : ∀ h, W h → X)
    (I : ∀ h, V →ₗ[ℝ] W h) (c ε : ℕ → ℝ)
    (hcons : ∀ h, ∀ v : V, ‖v‖ ≤ 1 →
      |fderiv ℝ (Sh h) (zd h) (I h v) - DS (R h (zd h)) v| ≤ c h)
    (hstat : ∀ h, ∀ v : V, ‖v‖ ≤ 1 → |fderiv ℝ (Sh h) (zd h) (I h v)| ≤ ε h)
    (hsub : ∀ (φ : ℕ → ℕ) (z : X), StrictMono φ →
      conv (fun k => R (φ k) (zd (φ k))) z →
      Tendsto (fun k => ‖DS (R (φ k) (zd (φ k))) - DS z‖) atTop (𝓝 0) ∧
      Tendsto (fun k => c (φ k) + ε (φ k)) atTop (𝓝 0))
    (hprecompact : ∃ (φ : ℕ → ℕ) (z : X), StrictMono φ ∧
      conv (fun k => R (φ k) (zd (φ k))) z) :
    ∃ (φ : ℕ → ℕ) (z : X), StrictMono φ ∧
      conv (fun k => R (φ k) (zd (φ k))) z ∧ DS z = 0 := by
  obtain ⟨φ, z, hφ, hconv⟩ := hprecompact
  exact ⟨φ, z, hφ, hconv, abstract_first_variation_closure_accumulation conv DS Sh zd R I
    c ε hcons hstat hsub φ z hφ hconv⟩

/-- `thm:abstract-closure` with the stationarity budget taken to be the
supremum `ε_h(K) = sup_{‖v‖≤1} |DS_h(z_h^d)[I_h v]|` itself (finite as soon as
the unit-ball values are bounded, which `hbdd` asserts). -/
theorem abstract_first_variation_closure_defect
    (DSz DSzh : V →L[ℝ] ℝ) (Φ : V → ℝ) (c : ℝ)
    (hcons : ∀ v : V, ‖v‖ ≤ 1 → |Φ v - DSzh v| ≤ c)
    (hbdd : BddAbove (Set.range fun v : {v : V // ‖v‖ ≤ 1} => |Φ v.1|)) :
    ‖DSz‖ ≤ (⨆ v : {v : V // ‖v‖ ≤ 1}, |Φ v.1|) + c + ‖DSzh - DSz‖ :=
  abstract_first_variation_closure_single DSz DSzh Φ c _ hcons
    (fun v hv => le_ciSup hbdd (⟨v, hv⟩ : {v : V // ‖v‖ ≤ 1}))

end AbstractFirstVariationClosure

end RenewalGeometry
