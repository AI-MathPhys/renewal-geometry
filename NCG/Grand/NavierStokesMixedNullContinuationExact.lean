/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NSSourceSheetFibrePythagorasExact

/-!
# Mixed-helicity and work-null Navier--Stokes continuation

This is the exact analytic handoff in `cor:NS-mixed-null-continuation`.
The already-proved NS.1/NS.2 Pythagoras identifies the total critical source
moment as the sum of its visible mixed-helicity and complete work-null parts.
Integrability of both parts therefore supplies the standard critical-source
continuation criterion.
-/

open MeasureTheory

noncomputable section

namespace NCG.NavierStokesMixedNullContinuation

/-- Integrability is preserved by the exact visible/work-null source split. -/
theorem critical_source_integrable_of_visible_and_workNull
    (total visible workNull : ℝ → ℝ) (s : Set ℝ)
    (hsplit : ∀ t, total t = visible t + workNull t)
    (hvisible : IntegrableOn visible s)
    (hworkNull : IntegrableOn workNull s) :
    IntegrableOn total s := by
  have hsum : IntegrableOn (fun t => visible t + workNull t) s :=
    hvisible.add hworkNull
  have heq : total = fun t => visible t + workNull t := funext hsplit
  rw [heq]
  exact hsum

/-- `cor:NS-mixed-null-continuation`: the two independently identified source
rows imply the full critical moment and hence continuation. -/
theorem mixed_helicity_workNull_continuation
    (ExtendsBeyondTerminalTime : Prop)
    (total visible workNull : ℝ → ℝ) (t0 T : ℝ)
    (hsplit : ∀ t, total t = visible t + workNull t)
    (hvisible : IntegrableOn visible (Set.Ioc t0 T))
    (hworkNull : IntegrableOn workNull (Set.Ioc t0 T))
    (criticalSourceContinuation :
      IntegrableOn total (Set.Ioc t0 T) → ExtendsBeyondTerminalTime) :
    IntegrableOn total (Set.Ioc t0 T) ∧ ExtendsBeyondTerminalTime := by
  have htotal := critical_source_integrable_of_visible_and_workNull
    total visible workNull (Set.Ioc t0 T) hsplit hvisible hworkNull
  exact ⟨htotal, criticalSourceContinuation htotal⟩

end NCG.NavierStokesMixedNullContinuation
