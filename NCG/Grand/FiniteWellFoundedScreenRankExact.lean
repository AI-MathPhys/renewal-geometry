/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SourceAnchoredCofinalExact

/-!
# Natural height of a finite well-founded screen

This supplies the final well-foundedness clause of
`thm:GT-source-anchored-cofinal-descent`: once the crossing bound confines a
history to one finite well-founded screen, that screen carries a strict
natural-valued height.
-/

namespace NCG

/-- The maximum recursive predecessor height on a finite well-founded
relation. -/
noncomputable def finiteWellFoundedScreenHeight
    {S : Type*} [Fintype S] [DecidableEq S]
    (r : S → S → Prop) [DecidableRel r] (hwf : WellFounded r) : S → ℕ :=
  hwf.fix fun x ih =>
    Finset.univ.sup fun y => if h : r y x then ih y h + 1 else 0

/-- Every edge in a finite well-founded screen strictly decreases the natural
height when read from a node to its predecessor. -/
theorem finiteWellFoundedScreenHeight_lt
    {S : Type*} [Fintype S] [DecidableEq S]
    (r : S → S → Prop) [DecidableRel r] (hwf : WellFounded r)
    {y x : S} (hyx : r y x) :
    finiteWellFoundedScreenHeight r hwf y <
      finiteWellFoundedScreenHeight r hwf x := by
  unfold finiteWellFoundedScreenHeight
  conv_rhs => rw [hwf.fix_eq]
  have hle :=
    (Finset.le_sup
      (f := fun z => if h : r z x then
        hwf.fix (fun u ih => Finset.univ.sup fun v =>
          if h' : r v u then ih v h' + 1 else 0) z + 1 else 0)
      (Finset.mem_univ y))
  rw [dif_pos hyx] at hle
  exact Nat.lt_of_succ_le hle
/-- A finite well-founded relation admits a strict natural-valued rank. -/
theorem finiteWellFoundedScreen_hasRank
    {S : Type*} [Fintype S] [DecidableEq S]
    (r : S → S → Prop) [DecidableRel r] (hwf : WellFounded r) :
    ∃ rank : S → ℕ, ∀ ⦃y x⦄, r y x → rank y < rank x :=
  ⟨finiteWellFoundedScreenHeight r hwf,
    fun _ _ h => finiteWellFoundedScreenHeight_lt r hwf h⟩

namespace SourceAnchoredCofinal

/-- `thm:GT-source-anchored-cofinal-descent`, including its final global-rank
clause.  Divergent margins define `H_*`; the joint balance forbids a crossing
of that level, and the finite well-founded obstruction screen at `H_*` has a
strict natural-valued height. -/
theorem source_anchored_cofinal_descent_exact
    (δ c : ℕ → ℝ) (h₀ : ℕ) (Aprev Astar Estar : ℝ)
    (hdiv : ∀ C : ℝ, ∃ H, C < marginSum δ h₀ H)
    (hmargin : ∀ h, h₀ ≤ h →
      h ≤ crossingLevel δ h₀ (Aprev - Astar + Estar)
        (hdiv (Aprev - Astar + Estar)) → δ h ≤ c h)
    {S : Type*} [Fintype S] [DecidableEq S]
    (step : S → S → Prop) [DecidableRel step]
    (hwf : WellFounded step) :
    (¬ ∃ AH EH : ℝ,
      AH + ∑ h ∈ Finset.Icc h₀
          (crossingLevel δ h₀ (Aprev - Astar + Estar)
            (hdiv (Aprev - Astar + Estar))), c h ≤ Aprev + EH
      ∧ Astar ≤ AH ∧ EH ≤ Estar)
    ∧ ∃ rank : S → ℕ, ∀ ⦃y x⦄, step y x → rank y < rank x := by
  constructor
  · rintro ⟨AH, EH, hbalance, hAH, hEH⟩
    exact no_history_crosses δ c h₀ Aprev Astar Estar
      (hdiv (Aprev - Astar + Estar))
      (crossingLevel δ h₀ (Aprev - Astar + Estar)
        (hdiv (Aprev - Astar + Estar))) rfl hmargin
      AH EH hbalance hAH hEH
  · exact finiteWellFoundedScreen_hasRank step hwf

end SourceAnchoredCofinal
end NCG
