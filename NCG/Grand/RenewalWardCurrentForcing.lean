/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PhaseAxisWardRead

/-!
# Rank-minimal forcing of renewal Ward currents

This module specializes the complete permutation-fixed phase-axis theorem to
the manuscript's hub source (one neutral and four writing atoms) and private
source (one survivor and two completion atoms).  It supplies the construction
layer that connects the scalar currents to the finite labelled renewal laws.
-/

namespace NCG

/-- Hub source: one neutral atom of mass `a` and four regular writing labels. -/
noncomputable def hubRenewalSource (a : ℝ) : Fin 5 → ℝ :=
  phaseUniformLaw 4 a

/-- Private source: one survivor atom of mass `s` and two fair completions. -/
noncomputable def privateRenewalSource (s : ℝ) : Fin 3 → ℝ :=
  phaseUniformLaw 2 s

/-- The unique hub cross-fibre Ward current. -/
noncomputable def hubWardCurrent (a : ℝ) : ℝ :=
  a - (1 - a) / 4

/-- The unique private cross-fibre Ward current. -/
noncomputable def privateWardCurrent (s : ℝ) : ℝ :=
  s - (1 - s) / 2

/-- Permutation invariance leaves exactly one centered hub coordinate. -/
theorem hub_centered_invariant_axis (v : Fin 5 → ℝ)
    (hv : ∑ j, v j = 0) :
    (∀ π : Equiv.Perm (Fin 4), ∀ i : Fin 4,
        v i.succ = v (π i).succ)
      ↔ ∃ t : ℝ, v 0 = 4 * t ∧ ∀ i : Fin 4, v i.succ = -t := by
  simpa using phase_fixed_subspace 4 (by norm_num) v hv

/-- Permutation invariance leaves exactly one centered private coordinate. -/
theorem private_centered_invariant_axis (v : Fin 3 → ℝ)
    (hv : ∑ j, v j = 0) :
    (∀ π : Equiv.Perm (Fin 2), ∀ i : Fin 2,
        v i.succ = v (π i).succ)
      ↔ ∃ t : ℝ, v 0 = 2 * t ∧ ∀ i : Fin 2, v i.succ = -t := by
  simpa using phase_fixed_subspace 2 (by norm_num) v hv

/-- The regular hub law is completely uniform exactly when its single Ward
current vanishes, equivalently at neutral mass `1/5`. -/
theorem hub_renewal_weight_forced (a : ℝ) :
    (hubRenewalSource a = fun _ => (1 / 5 : ℝ))
      ↔ hubWardCurrent a = 0 ∧ a = 1 / 5 := by
  rw [show (hubRenewalSource a = fun _ => (1 / 5 : ℝ))
      ↔ hubWardCurrent a = 0 by
        convert phase_uniform_ward 4 (by norm_num) a using 1 <;>
          norm_num [hubRenewalSource, hubWardCurrent]]
  constructor
  · intro h
    refine ⟨h, ?_⟩
    have ha := (ward_coordinate 4 (by norm_num) a).1.mp h
    norm_num at ha
    exact ha
  · exact fun h => h.1

/-- The regular private law is completely uniform exactly when its single
Ward current vanishes, equivalently at survivor mass `1/3`. -/
theorem private_renewal_weight_forced (s : ℝ) :
    (privateRenewalSource s = fun _ => (1 / 3 : ℝ))
      ↔ privateWardCurrent s = 0 ∧ s = 1 / 3 := by
  rw [show (privateRenewalSource s = fun _ => (1 / 3 : ℝ))
      ↔ privateWardCurrent s = 0 by
        convert phase_uniform_ward 2 (by norm_num) s using 1 <;>
          norm_num [privateRenewalSource, privateWardCurrent]]
  constructor
  · intro h
    refine ⟨h, ?_⟩
    have hs := (ward_coordinate 2 (by norm_num) s).1.mp h
    norm_num at hs
    exact hs
  · exact fun h => h.1

/-- `cor:minimal-renewal-Ward-currents`: the labelled source constructions,
the one-dimensional invariant axes, and the joint forcing of the concrete
renewal weights. -/
theorem minimal_renewal_ward_currents_exact :
    (∀ v : Fin 5 → ℝ, ∑ j, v j = 0 →
      ((∀ π : Equiv.Perm (Fin 4), ∀ i : Fin 4,
          v i.succ = v (π i).succ)
        ↔ ∃ t : ℝ, v 0 = 4 * t ∧ ∀ i : Fin 4, v i.succ = -t))
    ∧ (∀ v : Fin 3 → ℝ, ∑ j, v j = 0 →
      ((∀ π : Equiv.Perm (Fin 2), ∀ i : Fin 2,
          v i.succ = v (π i).succ)
        ↔ ∃ t : ℝ, v 0 = 2 * t ∧ ∀ i : Fin 2, v i.succ = -t))
    ∧ (∀ a s : ℝ,
        (hubWardCurrent a = 0 ∧ privateWardCurrent s = 0)
          ↔ (a = 1 / 5 ∧ s = 1 / 3)) := by
  refine ⟨fun v hv => hub_centered_invariant_axis v hv,
    fun v hv => private_centered_invariant_axis v hv, ?_⟩
  intro a s
  constructor
  · rintro ⟨ha, hs⟩
    constructor
    · have h := (ward_coordinate 4 (by norm_num) a).1.mp ha
      norm_num at h
      exact h
    · have h := (ward_coordinate 2 (by norm_num) s).1.mp hs
      norm_num at h
      exact h
  · rintro ⟨ha, hs⟩
    constructor
    · apply (ward_coordinate 4 (by norm_num) a).1.mpr
      norm_num
      exact ha
    · apply (ward_coordinate 2 (by norm_num) s).1.mpr
      norm_num
      exact hs

end NCG
