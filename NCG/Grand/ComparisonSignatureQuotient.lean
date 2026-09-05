/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NewAcceptedQuotient
import NCG.Grand.FinalPanels2

/-!
# Canonical comparison signature quotient

This file supplies the full quotient and refinement content of
`thm:accepted-comparison-quotient`: simultaneous factorization of the actual
and comparator rows, the initial universal property among deterministic
records, finite refinement termination, and reconstruction of the quotient by
any stable signature-separating partition.
-/

namespace NCG
namespace ComparisonSignatureQuotient

/-- The joint actual/comparator signature. -/
def comparisonSignature {Omega Actual Comparator : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator)
    (x : Omega) : Actual × Comparator :=
  (actual x, comparator x)

/-- The canonical comparison quotient, represented by the range of the joint
signature. -/
abbrev Quotient {Omega Actual Comparator : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator) :=
  Set.range (comparisonSignature actual comparator)

/-- Canonical surjection to the comparison quotient. -/
def quotientMap {Omega Actual Comparator : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator) :
    Omega → Quotient actual comparator := fun x ↦
  ⟨comparisonSignature actual comparator x, x, rfl⟩

theorem quotientMap_surjective {Omega Actual Comparator : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator) :
    Function.Surjective (quotientMap actual comparator) := by
  rintro ⟨signature, x, hx⟩
  subst signature
  exact ⟨x, rfl⟩

/-- Actual row read from the joint quotient. -/
def actualRow {Omega Actual Comparator : Type*}
    {actual : Omega → Actual} {comparator : Omega → Comparator} :
    Quotient actual comparator → Actual := fun q ↦ q.1.1

/-- Comparator row read from the joint quotient. -/
def comparatorRow {Omega Actual Comparator : Type*}
    {actual : Omega → Actual} {comparator : Omega → Comparator} :
    Quotient actual comparator → Comparator := fun q ↦ q.1.2

@[simp]
theorem actualRow_quotientMap {Omega Actual Comparator : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator) (x : Omega) :
    actualRow (quotientMap actual comparator x) = actual x := rfl

@[simp]
theorem comparatorRow_quotientMap {Omega Actual Comparator : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator) (x : Omega) :
    comparatorRow (quotientMap actual comparator x) = comparator x := rfl

/-- A map constant on the fibres of a surjection descends canonically. -/
noncomputable def descendThroughSurjection {Omega Theta Target : Type*}
    (record : Omega → Theta) (hrecord : Function.Surjective record)
    (target : Omega → Target)
    (_hfibre : ∀ {x y}, record x = record y → target x = target y) :
    Theta → Target := fun theta ↦
  target (Classical.choose (hrecord theta))

theorem descendThroughSurjection_comp {Omega Theta Target : Type*}
    (record : Omega → Theta) (hrecord : Function.Surjective record)
    (target : Omega → Target)
    (hfibre : ∀ {x y}, record x = record y → target x = target y) :
    descendThroughSurjection record hrecord target hfibre ∘ record = target := by
  funext x
  apply hfibre
  exact Classical.choose_spec (hrecord (record x))

theorem descendThroughSurjection_unique {Omega Theta Target : Type*}
    (record : Omega → Theta) (hrecord : Function.Surjective record)
    (target : Omega → Target) (g : Theta → Target)
    (hg : g ∘ record = target) :
    g = descendThroughSurjection record hrecord target
      (fun {x y} hxy ↦ by rw [← hg, Function.comp_apply, Function.comp_apply, hxy]) := by
  funext theta
  obtain ⟨x, rfl⟩ := hrecord theta
  calc
    g (record x) = target x := congrFun hg x
    _ = descendThroughSurjection record hrecord target _ (record x) :=
      (congrFun (descendThroughSurjection_comp record hrecord target _) x).symm

/-- Every other surjective deterministic record through which both row
families factor maps uniquely and surjectively onto the comparison quotient. -/
theorem comparisonQuotient_initial
    {Omega Actual Comparator Theta : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator)
    (record : Omega → Theta) (hrecord : Function.Surjective record)
    (actualOn : Theta → Actual) (comparatorOn : Theta → Comparator)
    (hactual : actualOn ∘ record = actual)
    (hcomparator : comparatorOn ∘ record = comparator) :
    ∃! g : Theta → Quotient actual comparator,
      Function.Surjective g ∧ g ∘ record = quotientMap actual comparator := by
  have hfibre : ∀ {x y}, record x = record y →
      quotientMap actual comparator x = quotientMap actual comparator y := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · calc
        actual x = actualOn (record x) := (congrFun hactual x).symm
        _ = actualOn (record y) := congrArg actualOn hxy
        _ = actual y := congrFun hactual y
    · calc
        comparator x = comparatorOn (record x) := (congrFun hcomparator x).symm
        _ = comparatorOn (record y) := congrArg comparatorOn hxy
        _ = comparator y := congrFun hcomparator y
  let g := descendThroughSurjection record hrecord
    (quotientMap actual comparator) hfibre
  have hgcomp : g ∘ record = quotientMap actual comparator :=
    descendThroughSurjection_comp record hrecord _ hfibre
  have hgsurj : Function.Surjective g := by
    intro q
    obtain ⟨x, hx⟩ := quotientMap_surjective actual comparator q
    refine ⟨record x, ?_⟩
    exact (congrFun hgcomp x).trans hx
  refine ⟨g, ⟨hgsurj, hgcomp⟩, ?_⟩
  intro g' hg'
  exact descendThroughSurjection_unique record hrecord
    (quotientMap actual comparator) g' hg'.2

/-- Full factorization and initiality package of the comparison quotient. -/
theorem canonical_initial_comparison_quotient
    {Omega Actual Comparator : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator) :
    actualRow ∘ quotientMap actual comparator = actual ∧
    comparatorRow ∘ quotientMap actual comparator = comparator ∧
    (∀ {Theta : Type*} (record : Omega → Theta),
      Function.Surjective record →
      ∀ (actualOn : Theta → Actual) (comparatorOn : Theta → Comparator),
      actualOn ∘ record = actual →
      comparatorOn ∘ record = comparator →
      ∃! g : Theta → Quotient actual comparator,
        Function.Surjective g ∧
          g ∘ record = quotientMap actual comparator) := by
  refine ⟨?_, ?_, ?_⟩
  · funext x
    rfl
  · funext x
    rfl
  · intro Theta record hrecord actualOn comparatorOn hactual hcomparator
    exact comparisonQuotient_initial actual comparator record hrecord
      actualOn comparatorOn hactual hcomparator

/-- A strictly refining finite partition chain has at most `|Omega|-1` strict
rounds, expressed directly through its block counts. -/
theorem strict_refinement_round_bound
    {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    {k : ℕ} (blocks : Fin (k + 1) → ℕ)
    (hpositive : ∀ i, 0 < blocks i)
    (hstrict : StrictMono blocks)
    (hbounded : ∀ i, blocks i ≤ Fintype.card Omega) :
    k ≤ Fintype.card Omega - 1 := by
  let f : Fin (k + 1) → Fin (Fintype.card Omega) := fun i ↦
    ⟨blocks i - 1, by
      have hcard : 0 < Fintype.card Omega := Fintype.card_pos
      have hibound := hbounded i
      omega⟩
  have hfstrict : StrictMono f := by
    intro i j hij
    apply Fin.mk_lt_mk.mpr
    have h := hstrict hij
    have hi := hpositive i
    have hj := hpositive j
    omega
  have hcard := refinement_termination f hfstrict
  omega

/-- A stable deterministic record whose fibres are exactly the signature
classes is canonically equivalent to the comparison quotient. -/
noncomputable def stableRecordEquivComparisonQuotient
    {Omega Actual Comparator Theta : Type*}
    (actual : Omega → Actual) (comparator : Omega → Comparator)
    (record : Omega → Theta) (hrecord : Function.Surjective record)
    (hfibres : ∀ x y, record x = record y ↔
      comparisonSignature actual comparator x =
        comparisonSignature actual comparator y) :
    Theta ≃ Quotient actual comparator := by
  let g := descendThroughSurjection record hrecord
    (quotientMap actual comparator) (fun {x y} hxy ↦ by
      apply Subtype.ext
      exact (hfibres x y).mp hxy)
  have hgcomp : g ∘ record = quotientMap actual comparator :=
    descendThroughSurjection_comp record hrecord _ _
  refine Equiv.ofBijective g ⟨?_, ?_⟩
  · intro theta₁ theta₂ htheta
    obtain ⟨x, rfl⟩ := hrecord theta₁
    obtain ⟨y, rfl⟩ := hrecord theta₂
    have hq : quotientMap actual comparator x =
        quotientMap actual comparator y := by
      calc
        quotientMap actual comparator x = g (record x) :=
          (congrFun hgcomp x).symm
        _ = g (record y) := htheta
        _ = quotientMap actual comparator y := congrFun hgcomp y
    exact (hfibres x y).mpr (Subtype.ext_iff.mp hq)
  · intro q
    obtain ⟨x, rfl⟩ := quotientMap_surjective actual comparator q
    exact ⟨record x, congrFun hgcomp x⟩

end ComparisonSignatureQuotient
end NCG
