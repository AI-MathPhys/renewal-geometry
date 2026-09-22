/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Dimension.DimensionPairwiseCompletionExact

/-!
# The minimal faithful predictive relation branch
  (`ass:supp-relational-branch`, emergent-spacetime manuscript)

The assumption has four clauses:

1. a local relation event has one future-readable source and one
   future-readable target (`source`, `target`, distinct);
2. physical reversal retains both orientations (an involutive `reverse`
   swapping the endpoints);
3. future-minimality identifies parallel relation labels exactly when every
   continuation identifies them (the quotient `MinimalRecord` by equality of
   the complete future signature, `futureSetoid`);
4. a nonempty relation set is invariant under a group acting transitively on
   unordered endpoint pairs.

`RenewalGeometry.MinimalFaithfulRelationBranch` bundles the four clauses in
one structure extending `RenewalGeometry.FutureMinimalSerialCell` (clauses
1–3) by the symmetry group, the relation set, and clause 4.  The first
consequence, `lem:supp-pair-completion` (the relation-colour-free skeleton is
the complete graph), is `MinimalFaithfulRelationBranch.skeleton_complete`. -/

namespace RenewalGeometry

/-- **Assumption `ass:supp-relational-branch`**: a minimal faithful predictive
relation branch — a future-minimal serial relation cell (one source, one
target, involutive reversal, complete future signature) whose nonempty set
of unordered endpoint pairs is invariant under a group acting transitively on
unordered pairs of distinct endpoints. -/
structure MinimalFaithfulRelationBranch (X A F : Type*)
    extends FutureMinimalSerialCell X A F where
  /-- the symmetry group of the endpoint set -/
  symmetry : Subgroup (Equiv.Perm X)
  /-- the set of unordered endpoint pairs carried by occurring relations -/
  relations : Set (Sym2 X)
  /-- every relation letter contributes its unordered endpoint pair -/
  pair_mem : ∀ a : A, s(source a, target a) ∈ relations
  /-- the group is transitive on unordered pairs of distinct endpoints -/
  transitive : ∀ p q : Sym2 X, ¬p.IsDiag → ¬q.IsDiag →
    ∃ g ∈ symmetry, Sym2.map (⇑g) p = q
  /-- the relation set is invariant -/
  invariant : ∀ g ∈ symmetry, ∀ p ∈ relations, Sym2.map (⇑g) p ∈ relations
  /-- the relation alphabet is nonempty -/
  nonempty : Nonempty A

namespace MinimalFaithfulRelationBranch

variable {X A F : Type*} (B : MinimalFaithfulRelationBranch X A F)

/-- The relation set contains a genuine (off-diagonal) pair
(`ass:supp-relational-branch`, nonemptiness clause). -/
theorem exists_offDiag_relation : ∃ p ∈ B.relations, ¬p.IsDiag := by
  obtain ⟨a⟩ := B.nonempty
  refine ⟨s(B.source a, B.target a), B.pair_mem a, ?_⟩
  rw [Sym2.mk_isDiag_iff]
  exact B.source_ne_target a

/-- **Lemma `lem:supp-pair-completion`**: under the assumption the
relation-colour-free skeleton is the complete graph on the endpoint set. -/
theorem skeleton_complete : ∀ q : Sym2 X, ¬q.IsDiag → q ∈ B.relations :=
  dimension_pairwise_completion B.symmetry B.relations B.transitive
    B.invariant B.exists_offDiag_relation

/-- Reversal retains both orientations: the reversed letter has the same
unordered endpoint pair (`ass:supp-relational-branch`, reversal clause). -/
theorem reverse_pair (a : A) :
    s(B.source (B.reverse a), B.target (B.reverse a))
      = s(B.source a, B.target a) := by
  rw [B.reverse_source, B.reverse_target, Sym2.eq_swap]

/-- Future-minimal identification of two parallel letters is exactly
equality of their complete future signatures
(`ass:supp-relational-branch`, future-minimality clause). -/
theorem minimal_identified_iff (a b : A) :
    Quotient.mk B.toFutureMinimalSerialCell.futureSetoid a
      = Quotient.mk B.toFutureMinimalSerialCell.futureSetoid b
      ↔ B.future a = B.future b :=
  Quotient.eq

end MinimalFaithfulRelationBranch

end RenewalGeometry
-- AXIOMCHECK
#print axioms RenewalGeometry.MinimalFaithfulRelationBranch.skeleton_complete
#print axioms RenewalGeometry.MinimalFaithfulRelationBranch.reverse_pair
#print axioms RenewalGeometry.MinimalFaithfulRelationBranch.minimal_identified_iff
#print axioms RenewalGeometry.MinimalFaithfulRelationBranch.exists_offDiag_relation
