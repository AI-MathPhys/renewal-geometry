/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.GenerationTransparency
import NCG.Matter.SMEasyV5

/-!
# Trivial generation multiplicity

This file gives the exact finite encoding of `cth:generation-number` from the
Gran-Tensor manuscript.  Tensoring a one-generation packet by `Fin g` leaves
every gauge, central-descent, and incidence label unchanged, multiplies local
anomaly sums by `g`, preserves their vanishing, and changes only the explicit
multiplicity dimension.
-/

open Matrix Kronecker

namespace NCG

/-- Lift data on one matter packet to a trivial `g`-fold generation
multiplicity. -/
def generationLift {S T : Type*} (f : S → T) (p : S × Fin g) : T := f p.1

/-- A nonempty trivial multiplicity does not change the set of gauge types
which occur. -/
theorem generationLift_typeRange {S T : Type*} (g : ℕ) (hg : 0 < g)
    (gaugeType : S → T) :
    Set.range (generationLift (g := g) gaugeType) = Set.range gaugeType := by
  ext t
  constructor
  · rintro ⟨⟨s, k⟩, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, ⟨0, hg⟩⟩, rfl⟩

/-- Any pointwise central-descent law is preserved by trivial generation
multiplicity. -/
theorem generationLift_preserves_centralDescent {S T Z : Type*}
    (g : ℕ) (gaugeType : S → T) (centralLabel : S → Z)
    (descentLaw : T → Z → Prop)
    (hdescent : ∀ s, descentLaw (gaugeType s) (centralLabel s)) :
    ∀ p : S × Fin g,
      descentLaw (generationLift gaugeType p)
        (generationLift centralLabel p) := by
  rintro ⟨s, k⟩
  exact hdescent s

/-- Any pointwise incidence-slot law is preserved by trivial generation
multiplicity. -/
theorem generationLift_preserves_incidence {S T I : Type*}
    (g : ℕ) (gaugeType : S → T) (incidenceSlot : S → I)
    (incidenceLaw : T → I → Prop)
    (hincidence : ∀ s, incidenceLaw (gaugeType s) (incidenceSlot s)) :
    ∀ p : S × Fin g,
      incidenceLaw (generationLift gaugeType p)
        (generationLift incidenceSlot p) := by
  rintro ⟨s, k⟩
  exact hincidence s

/-- Every anomaly coefficient of a trivially repeated packet is multiplied by
the number of generations. -/
theorem generationLift_anomalySum {S A : Type*} [Fintype S]
    (g : ℕ) (anomaly : A → S → ℤ) (a : A) :
    ∑ p : S × Fin g, anomaly a p.1 =
      g * ∑ s : S, anomaly a s := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Finset.mul_sum]

/-- Hence every vanishing local anomaly remains zero for every generation
number. -/
theorem generationLift_preserves_anomalyCancellation {S A : Type*}
    [Fintype S] (g : ℕ) (anomaly : A → S → ℤ)
    (hcancel : ∀ a, ∑ s : S, anomaly a s = 0) :
    ∀ a, ∑ p : S × Fin g, anomaly a p.1 = 0 := by
  intro a
  rw [generationLift_anomalySum, hcancel, mul_zero]

/-- The natural-number indicator of a weak doublet. -/
def weakDoubletIndicator {S : Type*} (isWeakDoublet : S → Bool) (s : S) : ℕ :=
  if isWeakDoublet s = true then 1 else 0

/-- A one-generation packet with four weak doublets has `4g` weak doublets
after trivial repetition, so the global `SU(2)` parity anomaly still vanishes. -/
theorem generationLift_weakDoubletParity {S : Type*} [Fintype S]
    (g : ℕ) (isWeakDoublet : S → Bool)
    (hfour : ∑ s : S, weakDoubletIndicator isWeakDoublet s = 4) :
    (∑ p : S × Fin g, weakDoubletIndicator isWeakDoublet p.1) = 4 * g ∧
      Even (∑ p : S × Fin g, weakDoubletIndicator isWeakDoublet p.1) := by
  have hcount : (∑ p : S × Fin g, weakDoubletIndicator isWeakDoublet p.1) =
      g * ∑ s : S, weakDoubletIndicator isWeakDoublet s := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ s : S, ∑ _k : Fin g, weakDoubletIndicator isWeakDoublet s =
          ∑ s : S, g * weakDoubletIndicator isWeakDoublet s := by
        apply Finset.sum_congr rfl
        intro s hs
        simp
      _ = g * ∑ s : S, weakDoubletIndicator isWeakDoublet s := by
        rw [Finset.mul_sum]
  rw [hcount, hfour]
  constructor
  · omega
  · exact ⟨2 * g, by omega⟩

/-- The dimension of the trivial multiplicity space is exactly the chosen
generation number. -/
theorem trivialMultiplicity_generationNumber (g : ℕ) :
    Fintype.card (Fin g) = g := Fintype.card_fin g

/-- Gauge matrices acting on the packet commute with matrices acting only on
the trivial generation multiplicity.  Thus the multiplicity factor lies in
the commutant of the associative gauge action. -/
theorem gaugeAction_commutes_trivialMultiplicity {S : Type*}
    [Fintype S] [DecidableEq S] (g : ℕ)
    (X : Matrix S S ℂ) (F : Matrix (Fin g) (Fin g) ℂ) :
    (X ⊗ₖ (1 : Matrix (Fin g) (Fin g) ℂ)) *
        ((1 : Matrix S S ℂ) ⊗ₖ F) =
      ((1 : Matrix S S ℂ) ⊗ₖ F) *
        (X ⊗ₖ (1 : Matrix (Fin g) (Fin g) ℂ)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- `cth:generation-number`: the assembled invariance and multiplicity
claims for every `g ≥ 1`. -/
theorem gaugeData_do_not_determine_generationNumber
    {S T Z I A : Type*} [Fintype S]
    (g : ℕ) (hg : 0 < g)
    (gaugeType : S → T) (centralLabel : S → Z) (incidenceSlot : S → I)
    (descentLaw : T → Z → Prop) (incidenceLaw : T → I → Prop)
    (anomaly : A → S → ℤ) (isWeakDoublet : S → Bool)
    (hdescent : ∀ s, descentLaw (gaugeType s) (centralLabel s))
    (hincidence : ∀ s, incidenceLaw (gaugeType s) (incidenceSlot s))
    (hcancel : ∀ a, ∑ s : S, anomaly a s = 0)
    (hfour : ∑ s : S, weakDoubletIndicator isWeakDoublet s = 4) :
    Set.range (generationLift (g := g) gaugeType) = Set.range gaugeType ∧
      (∀ p : S × Fin g,
        descentLaw (generationLift gaugeType p)
          (generationLift centralLabel p)) ∧
      (∀ p : S × Fin g,
        incidenceLaw (generationLift gaugeType p)
          (generationLift incidenceSlot p)) ∧
      (∀ a, ∑ p : S × Fin g, anomaly a p.1 = 0) ∧
      Even (∑ p : S × Fin g, weakDoubletIndicator isWeakDoublet p.1) ∧
      Fintype.card (Fin g) = g := by
  exact ⟨generationLift_typeRange g hg gaugeType,
    generationLift_preserves_centralDescent g gaugeType centralLabel
      descentLaw hdescent,
    generationLift_preserves_incidence g gaugeType incidenceSlot
      incidenceLaw hincidence,
    generationLift_preserves_anomalyCancellation g anomaly hcancel,
    (generationLift_weakDoubletParity g isWeakDoublet hfour).2,
    trivialMultiplicity_generationNumber g⟩

end NCG
