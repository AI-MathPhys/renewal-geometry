/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Collective compactness on varying Hilbert spaces

This file adds the compactness layer used by cutoff-screen and norm-resolvent arguments.  An
operator family between varying Hilbert spaces is collectively compact when the embedded images
of every stage unit ball lie in one compact subset of the common target carrier.  This is
strictly stronger than stagewise finite dimensionality and is the uniform hypothesis needed to
prevent compact mass from escaping as the cutoff changes.

The main extraction theorem turns collective compactness into the exact sequential statement
used in applications: the outputs of any unit-bounded dependent input sequence possess a
convergent subsequence in the common carrier.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v w v' w'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {G : Type v'} [NormedAddCommGroup G] [InnerProductSpace K G]
variable {Gn : ℕ → Type w'}
variable [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace K (Gn n)]

namespace System

variable (J : System (K := K) (H := H) (Hn := Hn))
variable (L : System (K := K) (H := G) (Hn := Gn))

/-- A stage operator followed by the target embedding, as a continuous linear map into the
common target carrier. -/
def embeddedOperator (Tn : ∀ n, Hn n →L[K] Gn n) (n : ℕ) : Hn n →L[K] G :=
  (L.embedding n).toContinuousLinearMap.comp (Tn n)

@[simp]
theorem embeddedOperator_apply (Tn : ∀ n, Hn n →L[K] Gn n) (n : ℕ) (x : Hn n) :
    L.embeddedOperator Tn n x = L.embedding n (Tn n x) :=
  rfl

/-- Uniform collective compactness: all embedded stage-unit-ball images are contained in one
compact subset of the common target Hilbert space. -/
def CollectivelyCompact (Tn : ∀ n, Hn n →L[K] Gn n) : Prop :=
  ∃ C : Set G, IsCompact C ∧
    ∀ n, L.embeddedOperator Tn n '' Metric.closedBall 0 1 ⊆ C

/-- The zero operator family is collectively compact. -/
theorem collectivelyCompact_zero :
    L.CollectivelyCompact (fun n ↦ (0 : Hn n →L[K] Gn n)) := by
  refine ⟨{0}, isCompact_singleton, ?_⟩
  intro n y hy
  obtain ⟨x, -, rfl⟩ := hy
  simp [embeddedOperator]

/-- Every embedded member of a collectively compact family is a compact operator. -/
theorem CollectivelyCompact.isCompactOperator_embedded
    {Tn : ∀ n, Hn n →L[K] Gn n} (hT : L.CollectivelyCompact Tn) (n : ℕ) :
    IsCompactOperator (L.embeddedOperator Tn n) := by
  obtain ⟨C, hC, hsub⟩ := hT
  have hcompact : IsCompactOperator (L.embeddedOperator Tn n).toLinearMap := by
    apply (isCompactOperator_iff_image_closedBall_subset_compact
      (L.embeddedOperator Tn n).toLinearMap zero_lt_one).2
    refine ⟨C, hC, ?_⟩
    simpa using hsub n
  simpa using hcompact


/-- Collective compactness is preserved by arbitrary reindexing of the cutoff stages. -/
theorem CollectivelyCompact.reindex
    {Tn : ∀ n, Hn n →L[K] Gn n} (hT : L.CollectivelyCompact Tn) (φ : ℕ → ℕ) :
    (L.reindex φ).CollectivelyCompact (fun n ↦ Tn (φ n)) := by
  obtain ⟨C, hC, hsub⟩ := hT
  refine ⟨C, hC, ?_⟩
  intro n y hy
  apply hsub (φ n)
  simpa [embeddedOperator, reindex] using hy

/-- Collective compactness extracts a convergent subsequence from the embedded outputs of every
unit-bounded dependent input sequence. -/
theorem CollectivelyCompact.tendsto_output_subseq
    {Tn : ∀ n, Hn n →L[K] Gn n} (hT : L.CollectivelyCompact Tn)
    (x : ∀ n, Hn n) (hx : ∀ n, ‖x n‖ ≤ 1) :
    ∃ y : G, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ L.embedding (φ k) (Tn (φ k) (x (φ k)))) atTop (𝓝 y) := by
  obtain ⟨C, hC, hsub⟩ := hT
  let output : ℕ → G := fun n ↦ L.embedding n (Tn n (x n))
  have hout : ∀ n, output n ∈ C := by
    intro n
    apply hsub n
    exact ⟨x n, by simpa [Metric.mem_closedBall, dist_zero_right] using hx n, rfl⟩
  obtain ⟨y, -, φ, hφ, hy⟩ := hC.tendsto_subseq hout
  exact ⟨y, φ, hφ, hy⟩

/-- Subsequence extraction remains available after any prescribed sequence of cutoff indices. -/
theorem CollectivelyCompact.tendsto_reindexed_output_subseq
    {Tn : ∀ n, Hn n →L[K] Gn n} (hT : L.CollectivelyCompact Tn)
    (φ : ℕ → ℕ) (x : ∀ n, Hn (φ n)) (hx : ∀ n, ‖x n‖ ≤ 1) :
    ∃ y : G, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto
        (fun k ↦ L.embedding (φ (ψ k))
          (Tn (φ (ψ k)) (x (ψ k)))) atTop (𝓝 y) := by
  simpa only [reindex_embedding] using
    CollectivelyCompact.tendsto_output_subseq (L := L.reindex φ)
      (CollectivelyCompact.reindex (L := L) hT φ) x hx


/-- The sequential extraction theorem in bundled strong-convergence language for a subsequence
viewed as a family in the common target carrier. -/
theorem CollectivelyCompact.exists_convergent_embedded_outputs
    {Tn : ∀ n, Hn n →L[K] Gn n} (hT : L.CollectivelyCompact Tn)
    (x : ∀ n, Hn n) (hx : ∀ n, ‖x n‖ ≤ 1) :
    ∃ y : G, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ L.embeddedOperator Tn (φ k) (x (φ k))) atTop (𝓝 y) := by
  simpa only [embeddedOperator_apply] using
    CollectivelyCompact.tendsto_output_subseq (L := L) hT x hx

end System

end NCG.VaryingHilbert
