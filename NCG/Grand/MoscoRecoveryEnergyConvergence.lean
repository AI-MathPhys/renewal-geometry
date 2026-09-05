/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco

/-!
# Exact convergence of Mosco recovery energies

The recovery clause is often stated with only a limsup inequality.  Combining it with the weak
liminf clause (strong convergence implies weak convergence) upgrades every such recovery to
actual convergence of the extended nonnegative energies.  This matches the manuscript's exact
form of condition (M2).
-/

open scoped ENNReal

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System.MoscoConverges

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {J : System (K := K) (H := H) (Hn := Hn)}
variable {q : (n : ℕ) → Hn n → ℝ≥0∞} {qlim : H → ℝ≥0∞}

/-- A strongly convergent sequence satisfying the recovery limsup inequality has energy
converging exactly to the limit energy. -/
theorem recovery_energy_tendsto
    (hq : J.MoscoConverges q qlim)
    {x : ∀ n, Hn n} {xlim : H}
    (hx : J.StronglyConverges x xlim)
    (hsup : limsup (fun n ↦ q n (x n)) atTop ≤ qlim xlim) :
    Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim)) := by
  apply tendsto_of_le_liminf_of_limsup_le (h := ⟨⊤, by simp⟩) (h' := ⟨0, by simp⟩)
  · exact hq.liminf_le x xlim hx.weak
  · exact hsup

/-- Every limit vector has a strongly convergent recovery sequence whose energies converge, not
merely one satisfying a limsup bound. -/
theorem exists_recovery_energy_tendsto
    (hq : J.MoscoConverges q qlim) (xlim : H) :
    ∃ x : ∀ n, Hn n,
      J.StronglyConverges x xlim ∧
        Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim)) := by
  obtain ⟨x, hx, hsup⟩ := hq.recovery xlim
  exact ⟨x, hx, hq.recovery_energy_tendsto hx hsup⟩

end NCG.VaryingHilbert.System.MoscoConverges
