/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertRadonRiesz
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Weak compactness and unique-cluster upgrades on varying Hilbert spaces

This file isolates the subsequence engine in the Mosco minimizer argument.  If every subsequence
has a weakly convergent further subsequence, every such weak cluster point is the prescribed
limit, and the norms converge, then the original dependent sequence converges strongly.  The
proof combines the varying-space Radon--Riesz lemma with the subsequence criterion for metric
convergence.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Sequential weak precompactness of one dependent sequence in the common carrier. -/
def IsSequentiallyWeaklyPrecompact (x : ∀ n, Hn n) : Prop :=
  ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
    ∃ y : H, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y

/-- Sequential weak precompactness and uniqueness of every weak cluster point imply weak
convergence of the full dependent sequence. -/
theorem weaklyConverges_of_weakPrecompact_of_unique
    {x : ∀ n, Hn n} {xlim : H}
    (hcompact : J.IsSequentiallyWeaklyPrecompact x)
    (hunique : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        y = xlim) :
    J.WeaklyConverges x xlim := by
  intro z
  refine Filter.tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨y, ψ, hψ, hweak⟩ := hcompact ns hns
  have hy : y = xlim := hunique ns hns ψ hψ y hweak
  subst y
  exact ⟨ψ, by simpa [reindex] using hweak z⟩

/-- Weak subsequential compactness, uniqueness of all weak cluster points, and convergence of
norms imply strong convergence of the original varying-space sequence. -/
theorem stronglyConverges_of_weakPrecompact_of_unique_of_norm
    {x : ∀ n, Hn n} {xlim : H}
    (hcompact : J.IsSequentiallyWeaklyPrecompact x)
    (hunique : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        y = xlim)
    (hnorm : Tendsto (fun n ↦ ‖x n‖) atTop (𝓝 ‖xlim‖)) :
    J.StronglyConverges x xlim := by
  rw [StronglyConverges]
  refine Filter.tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨y, ψ, hψ, hweak⟩ := hcompact ns hns
  have hy : y = xlim := hunique ns hns ψ hψ y hweak
  subst y
  have hnormSub :
      Tendsto (fun k ↦ ‖x (ns (ψ k))‖) atTop (𝓝 ‖xlim‖) :=
    hnorm.comp (hns.comp hψ.tendsto_atTop)
  have hstrong := WeaklyConverges.strong_of_norm
    (J.reindex (ns ∘ ψ)) hweak hnormSub
  exact ⟨ψ, by simpa [StronglyConverges, reindex] using hstrong⟩

end NCG.VaryingHilbert.System
