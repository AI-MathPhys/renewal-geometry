/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The arithmetic response thread: writer reconstruction from the quotient

Machinery for `thm:arithmetic-response-thread` — the record-local content on
top of the proved response-thread anchors (`thm:GT-response-thread-completion`,
`cor:GT-response-thread-master-defect`, `thm:GT-thread-cutoff-compactness`,
and the proved relation-valued clause of `thm:GT-relation-valued-limit`):
the identifiability criterion for an independently retained arithmetic writer.

* `fibreOscillation`: the oscillation of a writer `g` on the response fibre
  over `b` — the diameter of `g` on `r⁻¹{b}`;
* `oscillation_eq_zero_iff`: zero fibre oscillation is exactly constancy of
  the writer on the fibre;
* `writer_reconstruction_iff`: **exact reconstruction from the response
  quotient holds if and only if the writer has zero oscillation on every
  response fibre** — the boxed identifiability criterion;
* `nonidentifiability_witness`: a positive fibre oscillation produces an
  explicit witness — two histories with the same response and different
  writer values — rather than a license to assign a fitted value.
-/

open Metric
open scoped ENNReal

namespace NCG
namespace ArithmeticThread

variable {α β E : Type*} [EMetricSpace E]

/-- The oscillation of a writer `g` on the response fibre over `b`. -/
noncomputable def fibreOscillation (g : α → E) (r : α → β) (b : β) : ℝ≥0∞ :=
  Metric.ediam (g '' (r ⁻¹' {b}))

/-- Zero fibre oscillation is exactly constancy of the writer on the fibre. -/
theorem oscillation_eq_zero_iff (g : α → E) (r : α → β) (b : β) :
    fibreOscillation g r b = 0 ↔
      ∀ a a', r a = b → r a' = b → g a = g a' := by
  rw [fibreOscillation, Metric.ediam_eq_zero_iff]
  constructor
  · intro hsub a a' ha ha'
    exact hsub ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
  · rintro hc _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    exact hc a a' ha ha'

omit [EMetricSpace E] in
/-- A writer descends through the response quotient exactly when it is
constant on each quotient fibre. -/
theorem descends_iff_constant (g : α → E) (r : α → β) [Nonempty E] :
    (∃ h : β → E, ∀ a, g a = h (r a)) ↔
      ∀ a a', r a = r a' → g a = g a' := by
  constructor
  · rintro ⟨h, hh⟩ a a' hr
    rw [hh a, hh a', hr]
  · intro hc
    classical
    refine ⟨fun b => if hb : ∃ a, r a = b then g hb.choose
      else Classical.arbitrary E, fun a => ?_⟩
    have hb : ∃ a', r a' = r a := ⟨a, rfl⟩
    have hval : (if hb : ∃ a', r a' = r a then g hb.choose
        else Classical.arbitrary E) = g a := by
      rw [dif_pos hb]
      exact (hc a hb.choose hb.choose_spec.symm).symm
    exact hval.symm

/-- **The boxed identifiability criterion**: exact reconstruction of an
independently retained writer from the response quotient holds if and only if
the writer has zero oscillation on every response fibre. -/
theorem writer_reconstruction_iff (g : α → E) (r : α → β) [Nonempty E] :
    (∃ h : β → E, ∀ a, g a = h (r a)) ↔
      ∀ b, fibreOscillation g r b = 0 := by
  rw [descends_iff_constant]
  constructor
  · intro hc b
    rw [oscillation_eq_zero_iff]
    intro a a' ha ha'
    exact hc a a' (ha.trans ha'.symm)
  · intro ho a a' hr
    exact (oscillation_eq_zero_iff g r (r a')).mp (ho (r a')) a a' hr rfl

/-- **The nonidentifiability witness**: a positive fibre oscillation produces
two histories with the same response and different writer values. -/
theorem nonidentifiability_witness {g : α → E} {r : α → β} {b : β}
    (h : 0 < fibreOscillation g r b) :
    ∃ a a', r a = r a' ∧ g a ≠ g a' := by
  rw [fibreOscillation, Metric.ediam_pos_iff'] at h
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨a', ha', rfl⟩, hne⟩ := h
  exact ⟨a, a', ha.trans ha'.symm, hne⟩

end ArithmeticThread
end NCG
