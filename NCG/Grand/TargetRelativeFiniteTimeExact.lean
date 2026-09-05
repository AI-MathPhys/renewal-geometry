/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.ResponseThreadCompletionExact
import NCG.Grand.StructurePreservingResponseExact

/-!
# Target-relative finite-time responses

Record-local machinery for `cor:SMST-target-relative-finite-time`: the
(R1)–(R4) packet on a compact physical cylinder produces at least one
limiting response satisfying the declared countable weak core (the weak
matter and Einstein identities enter as that core).

* `thread_branch`: the **exact/projectively-Cauchy thread branch** of (R2) —
  a supplied coherent thread with vanishing finite-core residuals (R4) has a
  continuous completed trace, with the common continuation modulus, that
  annihilates every member of the countable core; the compactness branch of
  (R1)–(R4) is `NCG.StructureResponse.structure_preserving_response` and the
  one-scalar certification is
  `NCG.ResponseThreadCompletion.master_defect_closure`;
* `full_sequence_of_summable_adjacent`: the **(TR.6c) selection row** — a
  summable adjacent Cauchy estimate upgrades subsequential convergence of the
  selected traces to full-sequence convergence.
-/

open Filter Topology

namespace NCG
namespace TargetRelative

open ResponseThreadCompletion

/-- **The exact-thread branch of (R2) with (R4)**: a coherent thread with
vanishing finite-core residuals has a continuous completed trace with the
common continuation modulus annihilating the complete countable core. -/
theorem thread_branch {K : Type*} [MetricSpace K] [CompleteSpace K]
    (Y : Thread K)
    {k : ℕ → ℕ} (𝔡 : ∀ j, (Fin (k j) → K) → ℝ)
    (h𝔡 : ∀ j, Continuous (𝔡 j)) (q : ∀ j, Fin (k j) → ℝ)
    (depth : ℕ → ℕ) (hq : ∀ j i, q j i ∈ Y.D (depth j))
    (hres : ∀ j, Tendsto (fun m => 𝔡 j (fun i => Y.y m (q j i)))
      atTop (𝓝 0)) :
    ContinuousOn (limitTrace Y) (Set.Icc 0 Y.T) ∧
      (∀ t ∈ Set.Icc 0 Y.T, ∀ s ∈ Set.Icc 0 Y.T,
        dist (limitTrace Y t) (limitTrace Y s) ≤ Y.ω |t - s|) ∧
      ∀ j, 𝔡 j (fun i => limitTrace Y (q j i)) = 0 :=
  ⟨limitTrace_continuousOn Y,
    fun _ ht _ hs => limitTrace_modulus Y ht hs,
    fun j => cylinder_limit Y (𝔡 j) (h𝔡 j) (q j) (depth j) (hq j) (hres j)⟩

/-- **(TR.6c)**: a summable adjacent Cauchy estimate on the selected traces
upgrades subsequential convergence to full-sequence convergence. -/
theorem full_sequence_of_summable_adjacent {K : Type*} [MetricSpace K]
    [CompleteSpace K]
    (w : ℕ → K) (δ : ℕ → ℝ) (hδ : ∀ N, dist (w N) (w (N + 1)) ≤ δ N)
    (hsum : Summable δ) (z : K) (φ' : ℕ → ℕ) (hφ' : StrictMono φ')
    (hsub : Tendsto (fun m => w (φ' m)) atTop (𝓝 z)) :
    Tendsto w atTop (𝓝 z) :=
  StructureResponse.full_sequence_of_cauchy w
    (cauchySeq_of_dist_le_of_summable δ hδ hsum) z φ' hφ' hsub

end TargetRelative
end NCG
