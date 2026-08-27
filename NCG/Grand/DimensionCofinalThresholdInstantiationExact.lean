/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DimensionCofinal3Plus1
import NCG.Grand.JointSourceHilbertInductiveLimit
import NCG.Grand.SummablePositiveMixedGramCorrection

/-!
# Instantiating the cofinal endpoint and edge threshold ranks

The original persistence theorem accepted the final ranks `3` and `6` as
arguments.  Here they are derived from the cofinal corrected operator chains:
positive margins on the endpoint/edge witness spaces and vanishing tails on
their complementary null witnesses force the two limit ranks, which are then
fed to the `K₄` selector.
-/

open Matrix Filter
open scoped ComplexOrder Topology

namespace NCG
namespace DimensionCofinal

/-- The complete cofinal rank instantiation: threshold witnesses of dimensions
three and six in the two corrected chains yield the limit ranks, the `K₄`
cell, and the selected `1+3` spacetime dimension. -/
theorem cofinal_dimension_selection_from_thresholdPersistence
    {nE nF : Type} [Fintype nE] [Fintype nF]
    (Aend : ℕ → Matrix nE nE ℂ) (Aend' : Matrix nE nE ℂ)
    (Aedge : ℕ → Matrix nF nF ℂ) (Aedge' : Matrix nF nF ℂ)
    (hconvEnd : ∀ i j, Tendsto (fun k => Aend k i j) atTop
      (𝓝 (Aend' i j)))
    (hconvEdge : ∀ i j, Tendsto (fun k => Aedge k i j) atTop
      (𝓝 (Aedge' i j)))
    (hpsdEnd : Aend'.PosSemidef) (hpsdEdge : Aedge'.PosSemidef)
    (VEnd WEnd : Submodule ℂ (nE → ℂ))
    (VEdge WEdge : Submodule ℂ (nF → ℂ))
    (hVEnd : Module.finrank ℂ VEnd = 3)
    (hWEnd : Module.finrank ℂ WEnd = Fintype.card nE - 3)
    (hVEdge : Module.finrank ℂ VEdge = 6)
    (hWEdge : Module.finrank ℂ WEdge = Fintype.card nF - 6)
    (hcardEnd : 3 ≤ Fintype.card nE)
    (hcardEdge : 6 ≤ Fintype.card nF)
    (hlowEnd : ∀ x ∈ VEnd, x ≠ 0 →
      ∃ δ > (0 : ℝ), ∀ k, δ ≤ qf (Aend k) x)
    (hlowEdge : ∀ x ∈ VEdge, x ≠ 0 →
      ∃ δ > (0 : ℝ), ∀ k, δ ≤ qf (Aedge k) x)
    (htailEnd : ∀ x ∈ WEnd,
      Tendsto (fun k => qf (Aend k) x) atTop (𝓝 0))
    (htailEdge : ∀ x ∈ WEdge,
      Tendsto (fun k => qf (Aedge k) x) atTop (𝓝 0))
    (N : ℕ) (hN : Even N) (hN3 : 3 ≤ N)
    (hendCell : Aend'.rank = N - 1)
    (hedgeCell : Aedge'.rank = N.choose 2) :
    Aend'.rank = 3 ∧ Aedge'.rank = 6 ∧
      N = 4 ∧ 1 + (N - 1) = 4 := by
  have hend3 : Aend'.rank = 3 :=
    exact_rank_persistence Aend Aend' 3 hconvEnd hpsdEnd
      VEnd WEnd hVEnd hWEnd hcardEnd hlowEnd htailEnd
  have hedge6 : Aedge'.rank = 6 :=
    exact_rank_persistence Aedge Aedge' 6 hconvEdge hpsdEdge
      VEdge WEdge hVEdge hWEdge hcardEdge hlowEdge htailEdge
  have hdim := cofinal_dimension_selection Aend' Aedge' N hN hN3
    hendCell hedgeCell hend3 hedge6
  exact ⟨hend3, hedge6, hdim⟩

end DimensionCofinal
end NCG
