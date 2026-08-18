/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertWeakSubsequenceCompactness
import NCG.Grand.ClosedLinearPMapWeakLimit
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Sequential compactness in the weak topology of a Hilbert space

The varying-Hilbert weak subsequence theorem is converted here to convergence in mathlib's
`WeakSpace`.  This form composes directly with weak closedness of unbounded-operator graphs.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

omit [TopologicalSpace.SeparableSpace E] in
/-- Convergence of all Hilbert inner products implies convergence in `WeakSpace`. -/
theorem tendsto_toWeakSpace_of_inner
    {ι : Type*} {l : Filter ι} {x : ι → E} {xlim : E}
    (hx : ∀ z : E, Tendsto (fun i ↦ inner K (x i) z) l (𝓝 (inner K xlim z))) :
    Tendsto (fun i ↦ toWeakSpace K E (x i)) l (𝓝 (toWeakSpace K E xlim)) := by
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing K E).flip) (fun a b hab ↦ by
      by_contra hne
      obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := K) hne
      exact hf (DFunLike.congr_fun hab f))).2
  intro f
  change Tendsto (fun i ↦ f (x i)) l (𝓝 (f xlim))
  let z : E := (InnerProductSpace.toDual K E).symm f
  have hinner := hx z
  have hconj := (RCLike.continuous_conj.tendsto (inner K xlim z)).comp hinner
  change Tendsto (fun i ↦ (starRingEnd K) (inner K (x i) z)) l
    (𝓝 ((starRingEnd K) (inner K xlim z))) at hconj
  have hEval (y : E) : (starRingEnd K) (inner K y z) = f y := by
    rw [inner_conj_symm (𝕜 := K) z y]
    exact InnerProductSpace.toDual_symm_apply
  simpa only [hEval] using hconj

/-- Every norm-bounded sequence in a separable Hilbert space has a subsequence converging in
mathlib's weak topology. -/
theorem exists_tendsto_toWeakSpace_subsequence_of_bounded
    (x : ℕ → E) (C : ℝ) (hbound : ∀ n, ‖x n‖ ≤ C) :
    ∃ y : E, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun k ↦ toWeakSpace K E (x (ψ k))) atTop
        (𝓝 (toWeakSpace K E y)) := by
  obtain ⟨y, ψ, hψ, hweak⟩ :=
    VaryingHilbert.System.exists_weaklyConvergent_subsequence_of_bounded
      (J := VaryingHilbert.constantSystem K E) x C hbound
  refine ⟨y, ψ, hψ, tendsto_toWeakSpace_of_inner ?_⟩
  exact hweak

end NCG
