/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cofinal preparation under a consistency budget (abstract form)
  (`prop:supp-initial-cofinal-preparation`, `ass:supp-initial-consistency`;
  emergent-spacetime manuscript)

`ass:supp-initial-consistency` is encoded as a hypothesis structure `ConsistencyBudget` on the
*interpolated* quantities along a cofinal sequence of cutoffs: the interpolated records `e n`
(in a continuum phase space `E`), the interpolated values `c n` of the actual finite constraint
map and `w n` of the actual canonical velocity, and continuum maps `C`, `W` (continuous) with
`‖c n - C(e n)‖ + ‖w n - W(e n)‖ ≤ χ_n B`, `χ_n → 0` (`eq:supp-initial-consistency-budget` on a
bounded preparation chart).

* `ConsistencyBudget.limit_solves`: if the finite constraint values vanish exactly
  (`C_h(𝔍_h) = 0`, as in `thm:supp-action-prepared-chart`) and the interpolated records converge,
  then the limit solves the continuum constraints `C = 0` and the interpolated velocities (the
  harmonic-completion slot) converge to `W` of the limit.
* `ConsistencyBudget.subseq_limit_solves`: if the interpolated records lie in a sequentially
  compact set (Rellich compactness of a bounded `𝒫^{s+2}` set in `𝒫^{s+1}`), the same holds along a
  subsequence.
* `tendsto_of_unique_cluster`: whole-sequence convergence when every cluster point is the same
  (fixed-point uniqueness of the continuum range/mean maps).
-/

open Filter Topology

namespace RenewalGeometry.CofinalPreparation

variable {E Y V : Type*} [NormedAddCommGroup E] [NormedAddCommGroup Y] [NormedAddCommGroup V]

/-- **`ass:supp-initial-consistency` along a cofinal sequence** (abstract form). -/
structure ConsistencyBudget (C : E → Y) (W : E → V) (e : ℕ → E) (c : ℕ → Y) (w : ℕ → V) where
  /-- The consistency defect `χ_h`. -/
  χ : ℕ → ℝ
  /-- The bound of the records on the preparation chart. -/
  B : ℝ
  hC : Continuous C
  hW : Continuous W
  hχ : Tendsto χ atTop (𝓝 0)
  hc : ∀ n, ‖c n - C (e n)‖ ≤ χ n * B
  hw : ∀ n, ‖w n - W (e n)‖ ≤ χ n * B

namespace ConsistencyBudget

variable {C : E → Y} {W : E → V} {e : ℕ → E} {c : ℕ → Y} {w : ℕ → V}

theorem tendsto_defect (h : ConsistencyBudget C W e c w) :
    Tendsto (fun n => h.χ n * h.B) atTop (𝓝 0) := by
  simpa using h.hχ.mul_const h.B

/-- **Limits of exact finite zeros solve the continuum constraints**, and the interpolated
velocities converge to the continuum velocity of the limit. -/
theorem limit_solves (h : ConsistencyBudget C W e c w) (hz : ∀ n, c n = 0) {e₀ : E}
    (he : Tendsto e atTop (𝓝 e₀)) : C e₀ = 0 ∧ Tendsto w atTop (𝓝 (W e₀)) := by
  have hd := h.tendsto_defect
  have hCe : Tendsto (fun n => C (e n)) atTop (𝓝 (C e₀)) := (h.hC.tendsto e₀).comp he
  have hWe : Tendsto (fun n => W (e n)) atTop (𝓝 (W e₀)) := (h.hW.tendsto e₀).comp he
  refine ⟨?_, ?_⟩
  · -- `‖C(e n)‖ = ‖c n - C(e n)‖ ≤ χ_n B → 0`
    have h1 : Tendsto (fun n => C (e n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) hd
      have := h.hc n
      rwa [hz n, zero_sub, norm_neg] at this
    exact tendsto_nhds_unique hCe h1
  · have h2 : Tendsto (fun n => w n - W (e n)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => h.hw n) hd
    simpa using h2.add hWe

/-- **Subsequential preparation**: with a sequentially compact set containing the interpolated
records (Rellich), some subsequence converges to compatible continuum data. -/
theorem subseq_limit_solves (h : ConsistencyBudget C W e c w) (hz : ∀ n, c n = 0) {K : Set E}
    (hK : IsSeqCompact K) (heK : ∀ n, e n ∈ K) :
    ∃ e₀ ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (e ∘ φ) atTop (𝓝 e₀) ∧ C e₀ = 0 ∧
      Tendsto (w ∘ φ) atTop (𝓝 (W e₀)) := by
  obtain ⟨e₀, he₀, φ, hφ, hconv⟩ := hK heK
  have h' : ConsistencyBudget C W (e ∘ φ) (c ∘ φ) (w ∘ φ) :=
    { χ := h.χ ∘ φ
      B := h.B
      hC := h.hC
      hW := h.hW
      hχ := h.hχ.comp hφ.tendsto_atTop
      hc := fun n => h.hc (φ n)
      hw := fun n => h.hw (φ n) }
  obtain ⟨h1, h2⟩ := h'.limit_solves (fun n => hz (φ n)) hconv
  exact ⟨e₀, he₀, φ, hφ, hconv, h1, h2⟩

end ConsistencyBudget

/-- **Whole-sequence convergence from a unique cluster point**: in a sequentially compact set, if
every convergent subsequence has the same limit `e₀` (fixed-point uniqueness of the continuum
range/mean maps), the whole sequence converges to `e₀`. -/
theorem tendsto_of_unique_cluster {e : ℕ → E} {K : Set E} (hK : IsSeqCompact K)
    (heK : ∀ n, e n ∈ K) {e₀ : E}
    (huniq : ∀ (φ : ℕ → ℕ) (x : E), StrictMono φ → Tendsto (e ∘ φ) atTop (𝓝 x) → x = e₀) :
    Tendsto e atTop (𝓝 e₀) := by
  by_contra hne
  obtain ⟨U, hU, hfreq⟩ : ∃ U ∈ 𝓝 e₀, ∃ᶠ n in atTop, e n ∉ U := by
    rw [tendsto_def] at hne
    push Not at hne
    obtain ⟨U, hU, hnot⟩ := hne
    refine ⟨U, hU, ?_⟩
    rw [Filter.Frequently]
    intro hev
    exact hnot (by simpa using hev)
  obtain ⟨ψ, hψ, hψU⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨x, -, χ, hχ, hconv⟩ := hK (fun n => heK (ψ n))
  have hx := huniq (ψ ∘ χ) x (hψ.comp hχ) hconv
  subst hx
  have hev : ∀ᶠ n in atTop, (e ∘ (ψ ∘ χ)) n ∈ U := hconv hU
  obtain ⟨n, hn⟩ := hev.exists
  exact hψU (χ n) hn

end RenewalGeometry.CofinalPreparation
