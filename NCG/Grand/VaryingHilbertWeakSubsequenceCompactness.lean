/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertWeakCompactnessUpgrade
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Weak subsequence compactness on varying Hilbert spaces

Sequential Banach--Alaoglu on the weak dual, transported through the Hilbert--dual isometry,
shows that every norm-bounded dependent sequence has a weakly convergent subsequence in a
separable complete common carrier.  This supplies the equicoercive subsequence step in the
Mosco resolvent-minimizer proof.
-/

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- A uniformly norm-bounded dependent sequence has a weakly convergent subsequence in the
separable complete common Hilbert carrier. -/
theorem exists_weaklyConvergent_subsequence_of_bounded
    (x : ∀ n, Hn n) (C : ℝ) (hbound : ∀ n, ‖x n‖ ≤ C) :
    ∃ y : H, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      (J.reindex ψ).WeaklyConverges (fun k ↦ x (ψ k)) y := by
  let φ : ℕ → WeakDual K H := fun n ↦
    StrongDual.toWeakDual (innerSL K (J.embedding n (x n)))
  have hφmem : ∀ n,
      φ n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual K H) C := by
    intro n
    change dist (WeakDual.toStrongDual (φ n)) 0 ≤ C
    simpa [φ, dist_eq_norm, innerSL_apply_norm] using hbound n
  obtain ⟨φlim, -, ψ, hψ, hφlim⟩ :=
    (WeakDual.isSeqCompact_closedBall K H (0 : StrongDual K H) C) hφmem
  let y : H := (InnerProductSpace.toDual K H).symm (WeakDual.toStrongDual φlim)
  refine ⟨y, ψ, hψ, ?_⟩
  intro z
  have heval := (WeakDual.eval_continuous z).continuousAt.tendsto.comp hφlim
  simpa [φ, Function.comp_def, reindex, StrongDual.toWeakDual_apply,
    innerSL_apply_apply, y, InnerProductSpace.toDual_symm_apply,
    WeakDual.toStrongDual_apply] using heval

/-- Consequently every uniformly bounded dependent sequence is sequentially weakly precompact
in the sense used by the abstract resolvent minimizer theorem. -/
theorem isSequentiallyWeaklyPrecompact_of_bounded
    (x : ∀ n, Hn n) (C : ℝ) (hbound : ∀ n, ‖x n‖ ≤ C) :
    J.IsSequentiallyWeaklyPrecompact x := by
  intro ns hns
  obtain ⟨y, ψ, hψ, hweak⟩ :=
    exists_weaklyConvergent_subsequence_of_bounded
      (J.reindex ns) (fun n ↦ x (ns n)) C (fun n ↦ hbound (ns n))
  exact ⟨y, ψ, hψ, by simpa [reindex, Function.comp_def] using hweak⟩

end NCG.VaryingHilbert.System
