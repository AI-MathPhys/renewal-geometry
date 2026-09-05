/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DiagonalTendsto
import NCG.Grand.VaryingHilbertMosco

/-!
# Asymptotic density from dense compatible sources

If a dense subset of the limit Hilbert space admits compatible strongly
convergent stage lifts, then every limit vector admits such a lift.  A diagonal
choice simultaneously moves the dense source toward the requested vector and
moves far enough along its stage approximation.
-/

open Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Compatible lifts of a dense source set imply asymptotic density of the
varying-Hilbert comparison system. -/
theorem isAsymptoticallyDense_of_denseSources
    (D : Set H) (hD : Dense D)
    (source : H → ∀ n, Hn n)
    (hsource : ∀ x ∈ D, J.StronglyConverges (source x) x) :
    J.IsAsymptoticallyDense := by
  intro x
  let δ : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hδpos : ∀ m, 0 < δ m := by
    intro m
    dsimp [δ]
    positivity
  have hnear : ∀ m, ∃ y ∈ D, dist y x < δ m := by
    intro m
    simpa [dist_comm] using hD.exists_dist_lt x (hδpos m)
  choose d hdD hd using hnear
  have hδ : Tendsto δ atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hd : Tendsto d atTop (nhds x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero'
    · exact Eventually.of_forall fun m ↦ dist_nonneg
    · exact Eventually.of_forall fun m ↦ (hd m).le
    · exact hδ
  have hrow : ∀ m, Tendsto
      (fun n ↦ J.embedding n (source (d m) n)) atTop (nhds (d m)) := by
    intro m
    exact hsource (d m) (hdD m)
  obtain ⟨φ, _, hdiag, _⟩ := NCG.exists_diagonal_tendsto_pair
    (fun m n ↦ J.embedding n (source (d m) n)) d x
    (fun m n ↦ J.embedding n (source (d m) n)) d x
    hrow hd hrow hd
  exact ⟨fun n ↦ source (d (φ n)) n, hdiag⟩

end NCG.VaryingHilbert.System
