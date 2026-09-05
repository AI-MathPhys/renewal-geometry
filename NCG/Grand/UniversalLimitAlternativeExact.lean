/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The universal limit alternative: profile subnet and branch exhaustion

Record-local machinery for `thm:GT-universal-limit-alternative`:

* `exists_common_profile_subsequence`: **the cofinal subnet** — countably
  many compact metrizable profile coordinates (finite-stage state spaces,
  normalized metric cones, support Grassmannians, bounded weak graph balls)
  admit one common subsequence along which every profile coordinate
  converges;
* `universal_limit_alternative`: **branch exhaustion** — given the per-axis
  alternatives supplied by the proved profile records (each axis passes or
  attaches its finite witness), every regulator family lands in one of the
  twelve listed branches: the canonical controlled continuum (U1), the
  nonunique controlled continuum (U2), the controlled trivial continuum (U3),
  or one of the witness branches (U4)–(U11); the labels are nonexclusive and
  the undeclared branch (U12) is an explicit non-claim.
-/

open Filter Topology

namespace NCG
namespace UniversalLimit

/-- **The cofinal profile subnet**: countably many compact metrizable profile
coordinates admit one common subsequence along which every coordinate
converges. -/
theorem exists_common_profile_subsequence {X : ℕ → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, TopologicalSpace.PseudoMetrizableSpace (X i)]
    (x : ℕ → ∀ i, X i) :
    ∃ (φ : ℕ → ℕ) (lim : ∀ i, X i), StrictMono φ ∧
      ∀ i, Tendsto (fun n => x (φ n) i) atTop (𝓝 (lim i)) := by
  have hcompact : IsSeqCompact (Set.univ : Set (∀ i, X i)) :=
    isCompact_univ.isSeqCompact
  obtain ⟨lim, -, φ, hφ, hconv⟩ := hcompact (fun n => Set.mem_univ (x n))
  exact ⟨φ, lim, hφ, fun i => tendsto_pi_nhds.mp hconv i⟩

/-- **Branch exhaustion**: with the per-axis pass-or-witness alternatives of
the proved profile records, every audit-ready regulator family lands in one
of the twelve branches. -/
theorem universal_limit_alternative
    (CutoffCompat SourceComplete MetricStable DomainStable FieldTight
      LocalCtrl MemoryTight Coercive StateUnique VariancePositive : Prop)
    (W4 W5 W6 W7 W8 W9 W10 W11 : Prop)
    (h4 : CutoffCompat ∨ W4) (h5 : SourceComplete ∨ W5)
    (h6 : MetricStable ∨ W6) (h7 : DomainStable ∨ W7)
    (h8 : FieldTight ∨ W8) (h9 : LocalCtrl ∨ W9)
    (h10 : MemoryTight ∨ W10) (h11 : Coercive ∨ W11) :
    (CutoffCompat ∧ SourceComplete ∧ MetricStable ∧ DomainStable ∧ FieldTight
        ∧ LocalCtrl ∧ MemoryTight ∧ Coercive ∧ StateUnique
        ∧ VariancePositive) ∨
      (CutoffCompat ∧ SourceComplete ∧ MetricStable ∧ DomainStable
        ∧ FieldTight ∧ LocalCtrl ∧ MemoryTight ∧ Coercive
        ∧ ¬StateUnique) ∨
      (CutoffCompat ∧ SourceComplete ∧ MetricStable ∧ DomainStable
        ∧ FieldTight ∧ LocalCtrl ∧ MemoryTight ∧ Coercive
        ∧ ¬VariancePositive) ∨
      W4 ∨ W5 ∨ W6 ∨ W7 ∨ W8 ∨ W9 ∨ W10 ∨ W11 := by
  classical
  rcases h4 with hc4 | hw4
  case inr => exact Or.inr (Or.inr (Or.inr (Or.inl hw4)))
  rcases h5 with hc5 | hw5
  case inr => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hw5))))
  rcases h6 with hc6 | hw6
  case inr => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hw6)))))
  rcases h7 with hc7 | hw7
  case inr => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl hw7))))))
  rcases h8 with hc8 | hw8
  case inr => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl hw8)))))))
  rcases h9 with hc9 | hw9
  case inr => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl hw9))))))))
  rcases h10 with hc10 | hw10
  case inr => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl hw10)))))))))
  rcases h11 with hc11 | hw11
  case inr => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr hw11)))))))))
  by_cases hSU : StateUnique
  · by_cases hVP : VariancePositive
    · exact Or.inl ⟨hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hSU, hVP⟩
    · exact Or.inr (Or.inr (Or.inl
        ⟨hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hVP⟩))
  · exact Or.inr (Or.inl ⟨hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hSU⟩)

end UniversalLimit
end NCG
