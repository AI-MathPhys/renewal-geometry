/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCollectiveCompactness

/-!
# Graph-screen tightness and mass escape

This file formalizes the logical compact-screen alternative on genuinely varying stage spaces.
Eventual uniform screen tightness says that, beyond a sufficiently large screen, every sufficiently
late admissible graph vector has small tail.  Its failure produces exactly the manuscript's
mass-escape data: cofinal screen radii and cutoff indices, admissible stage vectors, and a fixed
positive lower bound on the escaped graph norm.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {Hn : ℕ → Type u}
variable {G : Type v} [NormedAddCommGroup G]

/-- Eventual uniform tightness of a family of admissible graph vectors under an increasing screen
parameter.  `tail R` is normally `I - Π_R`, while `admissible n u` records the graph-unit-ball
bound `‖u‖² + q_n[u] ≤ 1`. -/
def UniformGraphScreenTight
    (graph : ∀ n, Hn n → G) (tail : ℕ → G → G)
    (admissible : ∀ n, Hn n → Prop) : Prop :=
  ∀ ε > 0, ∃ R, ∀ S, R ≤ S →
    ∀ᶠ n in atTop, ∀ u, admissible n u → ‖tail S (graph n u)‖ < ε

/-- Failure of uniform graph-screen tightness yields a cofinal mass-escape witness with one fixed
positive escaped norm. -/
theorem massEscape_of_not_uniformGraphScreenTight
    (graph : ∀ n, Hn n → G) (tail : ℕ → G → G)
    (admissible : ∀ n, Hn n → Prop)
    (hfail : ¬ UniformGraphScreenTight graph tail admissible) :
    ∃ ε > 0, ∃ radius cutoff : ℕ → ℕ, ∃ u : ∀ j, Hn (cutoff j),
      Tendsto radius atTop atTop ∧ Tendsto cutoff atTop atTop ∧
      ∀ j, admissible (cutoff j) (u j) ∧
        ε ≤ ‖tail (radius j) (graph (cutoff j) (u j))‖ := by
  unfold UniformGraphScreenTight at hfail
  push Not at hfail
  obtain ⟨ε, hε, hbad⟩ := hfail
  have hwitness (j : ℕ) :
      ∃ R n, ∃ x : Hn n,
        j ≤ R ∧ j ≤ n ∧ admissible n x ∧
          ε ≤ ‖tail R (graph n x)‖ := by
    obtain ⟨R, hjR, hfreq⟩ := hbad j
    obtain ⟨n, hn, hjn⟩ :=
      (hfreq.and_eventually (eventually_ge_atTop j)).exists
    obtain ⟨x, hxadm, hxmass⟩ := hn
    exact ⟨R, n, x, hjR, hjn, hxadm, hxmass⟩
  choose radius cutoff u hjradius hjcutoff huadm humass using hwitness
  refine ⟨ε, hε, radius, cutoff, u, ?_, ?_, ?_⟩
  · rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact hj.trans (hjradius j)
  · rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact hj.trans (hjcutoff j)
  · intro j
    exact ⟨huadm j, humass j⟩

end NCG.VaryingHilbert
