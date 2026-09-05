/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniform subsequence compactness with a retained Lipschitz bound

A uniformly bounded real-valued family on a compact metric domain, with a
common Lipschitz constant, has a uniformly convergent subsequence. The limit
retains the original Lipschitz constant. Compactness is derived from
Arzelà–Ascoli, not included as an extra hypothesis.
-/

open Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace NCG.UniformLipschitzSubsequenceCompactness

noncomputable section

theorem exists_uniformly_convergent_subsequence
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : ℕ → X → ℝ) (K : ℝ≥0) (M : ℝ)
    (hLip : ∀ n, LipschitzWith K (f n)) (hbound : ∀ n x, |f n x| ≤ M) :
    ∃ g : X → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ LipschitzWith K g ∧
      (∀ x, |g x| ≤ M) ∧ TendstoUniformly (fun n => f (φ n)) g atTop := by
  let F : ℕ → X →ᵇ ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨f n, (hLip n).continuous⟩
  let A : Set (X →ᵇ ℝ) := Set.range F
  have hA : Equicontinuous ((↑) : A → X → ℝ) := by
    apply (LipschitzWith.uniformEquicontinuous _ K ?_).equicontinuous
    intro a
    obtain ⟨n, hn⟩ := a.property
    rw [← hn]
    exact hLip n
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Set.Icc (-M) M) isCompact_Icc A
      (by
        intro a x ha
        obtain ⟨n, rfl⟩ := ha
        exact abs_le.mp (hbound n x)) hA
  obtain ⟨g, _, φ, hφ, hconv⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  have huni : TendstoUniformly (fun n => f (φ n)) (fun x => g x) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  refine ⟨g, φ, hφ, ?_, ?_, huni⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    exact le_of_tendsto ((huni.tendsto_at x).dist (huni.tendsto_at y))
      (Eventually.of_forall (fun n => (hLip (φ n)).dist_le_mul x y))
  · intro x
    exact le_of_tendsto (huni.tendsto_at x).abs
      (Eventually.of_forall (fun n => hbound (φ n) x))

end

end NCG.UniformLipschitzSubsequenceCompactness
