/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FeedbackLimitMemoryClassification

/-!
# Exact scalar Hankel-rank / recurrence bridge

Finite feedback Hankel rank means that all delayed Hankel columns lie in the
span of finitely many initial columns.  This file proves that intrinsic rank
condition equivalent to one monic constant-coefficient recurrence, closing
the bridge used by `thm:feedback-limit-classification`.
-/

namespace NCG
namespace FeedbackLimitMemoryClassification

/-- The scalar Hankel column with past delay `p`. -/
def scalarHankelColumn (K : ℕ → ℝ) (p : ℕ) : ℕ → ℝ :=
  fun f => K (f + p)

/-- Intrinsic finite scalar Hankel rank: some finite initial column panel spans
every delayed Hankel column. -/
def HasFiniteHankelRank (K : ℕ → ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ p,
    scalarHankelColumn K p ∈
      Submodule.span ℝ (Set.range fun j : Fin m => scalarHankelColumn K j)

/-- One fixed recurrence propagates every Hankel column from the first `m`
columns. -/
theorem hasFiniteRecurrence_implies_hasFiniteHankelRank
    (K : ℕ → ℝ) :
    HasFiniteRecurrence K → HasFiniteHankelRank K := by
  rintro ⟨m, hm, a, hrec⟩
  refine ⟨m, hm, ?_⟩
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
      by_cases hp : p < m
      · exact Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩
      · have hmp : m ≤ p := le_of_not_gt hp
        have hcolumn : scalarHankelColumn K p =
            ∑ j : Fin m, a j • scalarHankelColumn K (p - m + (j : ℕ)) := by
          funext f
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            scalarHankelColumn]
          have hpEq : p - m + m = p := Nat.sub_add_cancel hmp
          simpa only [Nat.add_assoc, hpEq] using hrec (f + (p - m))
        rw [hcolumn]
        apply Submodule.sum_mem
        intro j _
        apply Submodule.smul_mem
        apply ih
        omega

/-- Conversely, the first dependence of a delayed Hankel column on a finite
initial panel is exactly a monic recurrence, valid at every future row. -/
theorem hasFiniteHankelRank_implies_hasFiniteRecurrence
    (K : ℕ → ℝ) :
    HasFiniteHankelRank K → HasFiniteRecurrence K := by
  rintro ⟨m, hm, hspan⟩
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hspan m)
  refine ⟨m, hm, a, ?_⟩
  intro k
  have hk := congrFun ha k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    scalarHankelColumn] at hk
  exact hk.symm

/-- Exact recurrence/Hankel-rank bridge. -/
theorem hasFiniteRecurrence_iff_hasFiniteHankelRank (K : ℕ → ℝ) :
    HasFiniteRecurrence K ↔ HasFiniteHankelRank K :=
  ⟨hasFiniteRecurrence_implies_hasFiniteHankelRank K,
    hasFiniteHankelRank_implies_hasFiniteRecurrence K⟩

/-- The corrected four-way table can therefore be read literally as
summability times finite/infinite intrinsic Hankel rank. -/
theorem everyKernel_exactlyOneHankelMemoryBranch (K : ℕ → ℝ) :
    ((HasFiniteHankelRank K ∧ Summable K) ∨
      (HasFiniteHankelRank K ∧ ¬Summable K) ∨
      (¬HasFiniteHankelRank K ∧ Summable K) ∨
      (¬HasFiniteHankelRank K ∧ ¬Summable K)) ∧
    ((stableRationalMemory K ↔ HasFiniteHankelRank K ∧ Summable K) ∧
      (persistentRationalMemory K ↔ HasFiniteHankelRank K ∧ ¬Summable K) ∧
      (infiniteDimensionalShortMemory K ↔
        ¬HasFiniteHankelRank K ∧ Summable K) ∧
      (infiniteDimensionalLongMemory K ↔
        ¬HasFiniteHankelRank K ∧ ¬Summable K)) := by
  rw [← hasFiniteRecurrence_iff_hasFiniteHankelRank K]
  unfold stableRationalMemory persistentRationalMemory
    infiniteDimensionalShortMemory infiniteDimensionalLongMemory
  tauto

end FeedbackLimitMemoryClassification
end NCG

