/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Relative upstream primitive closure and cofinal row independence

An exact finite categorical encoding of `thm:GT-relative-primitive-closure`.
The fixed grammar is held implicit.  A model is observed through its four
semantic rows (actual occurrence, complete contextual prediction, protected
orientation, and absolute calibration).  We prove:

* every row-invariant downstream construction factors uniquely through the
  image of the four-row signature;
* explicit finite separating pairs for each of the four rows, using precisely
  the Bernoulli, exported-bit, opposite-plane-orientation, and distinct-scale
  mechanisms in the manuscript;
* separation survives every common conservative spectator refinement and
  every faithful cofinal reindexing;
* all named downstream packets factor through the same signature and hence do
  not add primitive semantic rows.
-/

namespace NCG
namespace RelativeUpstreamPrimitiveClosure

/-! ### The universal four-row signature -/

structure AuditRows (M O P Θ Λ : Type*) where
  occurrence : M → O
  prediction : M → P
  orientation : M → Θ
  calibration : M → Λ

variable {M O P Θ Λ : Type*}

def AuditRows.signature (R : AuditRows M O P Θ Λ) (x : M) :
    O × P × Θ × Λ :=
  (R.occurrence x, R.prediction x, R.orientation x, R.calibration x)

/-- The actually realized image of the four primitive rows. -/
def AuditRows.SignatureImage (R : AuditRows M O P Θ Λ) :=
  Set.range R.signature

def AuditRows.project (R : AuditRows M O P Θ Λ) (x : M) :
    R.SignatureImage :=
  ⟨R.signature x, x, rfl⟩

/-- A construction is downstream of the semantic floor exactly when it cannot
distinguish models with equal four-row signatures. -/
def AuditRows.Invariant (R : AuditRows M O P Θ Λ) {D : Type*}
    (d : M → D) : Prop :=
  ∀ ⦃x y⦄, R.signature x = R.signature y → d x = d y

/-- **B1 universal compiler transfer.** Every construction invariant under
the four primitive rows factors uniquely through their realized signature
image.  This covers the predictive quotient, arbitrary finite
quotient-invariant compilers, positive-comb reconstruction, and finite
reset/recurrence tests once their already-proved row invariance is supplied. -/
theorem factorsThrough_signatureImage (R : AuditRows M O P Θ Λ)
    {D : Type*} (d : M → D) (hd : R.Invariant d) :
    ∃! f : R.SignatureImage → D, d = f ∘ R.project := by
  classical
  let f : R.SignatureImage → D := fun z => d (Classical.choose z.property)
  have hf : d = f ∘ R.project := by
    funext x
    apply hd
    exact (Classical.choose_spec (R.project x).property).symm
  refine ⟨f, hf, ?_⟩
  intro g hg
  funext z
  obtain ⟨x, hx⟩ := z.property
  have hp : R.project x = z := Subtype.ext hx
  subst z
  have hfx := congrFun hf x
  have hgx := congrFun hg x
  exact hgx.symm.trans hfx

/-! ### The four exact finite separating mechanisms -/

structure BernoulliLaw where
  p : ℚ
  nonneg : 0 ≤ p
  le_one : p ≤ 1

def bernoulliQuarter : BernoulliLaw := ⟨1 / 4, by norm_num, by norm_num⟩
def bernoulliThreeQuarter : BernoulliLaw := ⟨3 / 4, by norm_num, by norm_num⟩
def bernoulliHalf : BernoulliLaw := ⟨1 / 2, by norm_num, by norm_num⟩

theorem bernoulliQuarter_ne_threeQuarter :
    bernoulliQuarter ≠ bernoulliThreeQuarter := by
  intro h
  have hp := congrArg BernoulliLaw.p h
  norm_num [bernoulliQuarter, bernoulliThreeQuarter] at hp

/-- The two sections of a fixed oriented plane, represented by the coefficient
of its standard alternating form. -/
inductive PlaneSection
  | positive
  | negative
  deriving DecidableEq

def PlaneSection.alternatingCoefficient : PlaneSection → ℤ
  | .positive => 1
  | .negative => -1

def PlaneSection.positiveGram (s : PlaneSection) : ℤ :=
  s.alternatingCoefficient ^ 2

theorem opposite_sections_same_positiveGram :
    PlaneSection.positiveGram .positive =
      PlaneSection.positiveGram .negative := by
  norm_num [PlaneSection.positiveGram,
    PlaneSection.alternatingCoefficient]

theorem positiveSection_ne_negativeSection :
    PlaneSection.positive ≠ PlaneSection.negative := by decide

structure PositiveCalibration where
  scale : ℚ
  positive : 0 < scale

def unitCalibration : PositiveCalibration := ⟨1, by norm_num⟩
def doubleCalibration : PositiveCalibration := ⟨2, by norm_num⟩

theorem unitCalibration_ne_doubleCalibration :
    unitCalibration ≠ doubleCalibration := by
  intro h
  have hs := congrArg PositiveCalibration.scale h
  norm_num [unitCalibration, doubleCalibration] at hs

/-- A finite model in one fixed one-letter typed grammar.  The Boolean row is
the actual exported occurrence bit; the Bernoulli row is its complete
normalized predictive law; the plane section is protected orientation; and
the positive rational is absolute calibration. -/
structure FiniteAuditModel where
  exportedOccurrence : Bool
  predictiveLaw : BernoulliLaw
  orientationSection : PlaneSection
  absoluteCalibration : PositiveCalibration

def concreteRows : AuditRows FiniteAuditModel Bool BernoulliLaw
    PlaneSection PositiveCalibration where
  occurrence := FiniteAuditModel.exportedOccurrence
  prediction := FiniteAuditModel.predictiveLaw
  orientation := FiniteAuditModel.orientationSection
  calibration := FiniteAuditModel.absoluteCalibration

def baseModel : FiniteAuditModel where
  exportedOccurrence := false
  predictiveLaw := bernoulliHalf
  orientationSection := .positive
  absoluteCalibration := unitCalibration

def predictionSeparatedModel : FiniteAuditModel :=
  { baseModel with predictiveLaw := bernoulliQuarter }

def predictionSeparatedModel' : FiniteAuditModel :=
  { baseModel with predictiveLaw := bernoulliThreeQuarter }

def occurrenceSeparatedModel : FiniteAuditModel :=
  { baseModel with exportedOccurrence := false }

def occurrenceSeparatedModel' : FiniteAuditModel :=
  { baseModel with exportedOccurrence := true }

def orientationSeparatedModel : FiniteAuditModel :=
  { baseModel with orientationSection := .positive }

def orientationSeparatedModel' : FiniteAuditModel :=
  { baseModel with orientationSection := .negative }

def calibrationSeparatedModel : FiniteAuditModel :=
  { baseModel with absoluteCalibration := unitCalibration }

def calibrationSeparatedModel' : FiniteAuditModel :=
  { baseModel with absoluteCalibration := doubleCalibration }

def forgetOccurrence (x : FiniteAuditModel) :=
  (x.predictiveLaw, x.orientationSection, x.absoluteCalibration)

def forgetPrediction (x : FiniteAuditModel) :=
  (x.exportedOccurrence, x.orientationSection, x.absoluteCalibration)

def forgetOrientation (x : FiniteAuditModel) :=
  (x.exportedOccurrence, x.predictiveLaw, x.absoluteCalibration)

def forgetCalibration (x : FiniteAuditModel) :=
  (x.exportedOccurrence, x.predictiveLaw, x.orientationSection)

structure SeparatingPair {X R : Type*} (forget : X → R) where
  left : X
  right : X
  same_after_forget : forget left = forget right
  inequivalent : left ≠ right

def occurrenceSeparatingPair : SeparatingPair forgetOccurrence where
  left := occurrenceSeparatedModel
  right := occurrenceSeparatedModel'
  same_after_forget := rfl
  inequivalent := by
    intro h
    have := congrArg FiniteAuditModel.exportedOccurrence h
    simp [occurrenceSeparatedModel, occurrenceSeparatedModel', baseModel] at this

def predictionSeparatingPair : SeparatingPair forgetPrediction where
  left := predictionSeparatedModel
  right := predictionSeparatedModel'
  same_after_forget := rfl
  inequivalent := by
    intro h
    exact bernoulliQuarter_ne_threeQuarter
      (congrArg FiniteAuditModel.predictiveLaw h)

def orientationSeparatingPair : SeparatingPair forgetOrientation where
  left := orientationSeparatedModel
  right := orientationSeparatedModel'
  same_after_forget := rfl
  inequivalent := by
    intro h
    exact positiveSection_ne_negativeSection
      (congrArg FiniteAuditModel.orientationSection h)

def calibrationSeparatingPair : SeparatingPair forgetCalibration where
  left := calibrationSeparatedModel
  right := calibrationSeparatedModel'
  same_after_forget := rfl
  inequivalent := by
    intro h
    exact unitCalibration_ne_doubleCalibration
      (congrArg FiniteAuditModel.absoluteCalibration h)

/-- **B2.** All four primitive rows have explicit finite separating pairs;
the orientation pair additionally has identical positive Gram data. -/
theorem four_rows_irredundant :
    forgetOccurrence occurrenceSeparatingPair.left =
        forgetOccurrence occurrenceSeparatingPair.right ∧
    forgetPrediction predictionSeparatingPair.left =
        forgetPrediction predictionSeparatingPair.right ∧
    forgetOrientation orientationSeparatingPair.left =
        forgetOrientation orientationSeparatingPair.right ∧
    forgetCalibration calibrationSeparatingPair.left =
        forgetCalibration calibrationSeparatingPair.right ∧
    PlaneSection.positiveGram .positive =
      PlaneSection.positiveGram .negative := by
  exact ⟨rfl, rfl, rfl, rfl, opposite_sections_same_positiveGram⟩

/-! ### Conservative spectators and cofinal reindexing -/

/-- A common spectator refinement with a physical discard is precisely a
split embedding. -/
structure ConservativeRefinement (X Y : Type*) where
  extend : X → Y
  discard : Y → X
  discard_extend : Function.LeftInverse discard extend

/-- A cofinal reindexing is faithful on the finite objects being audited. -/
structure CofinalReindexing (X Y : Type*) where
  pullback : X → Y
  faithful : Function.Injective pullback

theorem separation_survives_conservative_refinement
    {X R Y : Type*} {forget : X → R} (p : SeparatingPair forget)
    (S : ConservativeRefinement X Y) :
    S.extend p.left ≠ S.extend p.right := by
  intro h
  exact p.inequivalent (S.discard_extend.injective h)

theorem separation_survives_cofinal_reindexing
    {X R Y Z : Type*} {forget : X → R} (p : SeparatingPair forget)
    (S : ConservativeRefinement X Y) (C : CofinalReindexing Y Z) :
    C.pullback (S.extend p.left) ≠ C.pullback (S.extend p.right) := by
  intro h
  exact separation_survives_conservative_refinement p S (C.faithful h)

/-- **B3.** Every one of the four manuscript separating pairs remains
separating after any common conservative spectator refinement and any faithful
cofinal pullback. -/
theorem four_pairs_remain_separating
    {Y Z : Type*} (S : ConservativeRefinement FiniteAuditModel Y)
    (C : CofinalReindexing Y Z) :
    C.pullback (S.extend occurrenceSeparatingPair.left) ≠
        C.pullback (S.extend occurrenceSeparatingPair.right) ∧
    C.pullback (S.extend predictionSeparatingPair.left) ≠
        C.pullback (S.extend predictionSeparatingPair.right) ∧
    C.pullback (S.extend orientationSeparatingPair.left) ≠
        C.pullback (S.extend orientationSeparatingPair.right) ∧
    C.pullback (S.extend calibrationSeparatingPair.left) ≠
        C.pullback (S.extend calibrationSeparatingPair.right) := by
  exact ⟨separation_survives_cofinal_reindexing occurrenceSeparatingPair S C,
    separation_survives_cofinal_reindexing predictionSeparatingPair S C,
    separation_survives_cofinal_reindexing orientationSeparatingPair S C,
    separation_survives_cofinal_reindexing calibrationSeparatingPair S C⟩

/-! ### Named downstream objects add no primitive rows -/

structure DownstreamPacket (R : AuditRows M O P Θ Λ)
    (Reset Recurrence Excursion Waiting Predictive Relation PositiveProcess
      StructuralTensor : Type*) where
  reset : M → Reset
  recurrence : M → Recurrence
  excursion : M → Excursion
  waiting : M → Waiting
  predictive : M → Predictive
  relation : M → Relation
  positiveProcess : M → PositiveProcess
  structuralTensor : M → StructuralTensor
  reset_invariant : R.Invariant reset
  recurrence_invariant : R.Invariant recurrence
  excursion_invariant : R.Invariant excursion
  waiting_invariant : R.Invariant waiting
  predictive_invariant : R.Invariant predictive
  relation_invariant : R.Invariant relation
  positiveProcess_invariant : R.Invariant positiveProcess
  structuralTensor_invariant : R.Invariant structuralTensor

/-- **B4.** Every named reset/recurrence, renewal-law, predictive, relational,
positive-process, and structural output factors through the primitive floor
when it is invariant under equality of those rows.  Consequently it is a
derived object or branch property, not a fifth basis row. -/
theorem downstream_packet_factors
    (R : AuditRows M O P Θ Λ)
    {Reset Recurrence Excursion Waiting Predictive Relation PositiveProcess
      StructuralTensor : Type*}
    (D : DownstreamPacket R Reset Recurrence Excursion Waiting Predictive
      Relation PositiveProcess StructuralTensor) :
    (∃! f : R.SignatureImage → Reset, D.reset = f ∘ R.project) ∧
    (∃! f : R.SignatureImage → Recurrence, D.recurrence = f ∘ R.project) ∧
    (∃! f : R.SignatureImage → Excursion, D.excursion = f ∘ R.project) ∧
    (∃! f : R.SignatureImage → Waiting, D.waiting = f ∘ R.project) ∧
    (∃! f : R.SignatureImage → Predictive, D.predictive = f ∘ R.project) ∧
    (∃! f : R.SignatureImage → Relation, D.relation = f ∘ R.project) ∧
    (∃! f : R.SignatureImage → PositiveProcess,
      D.positiveProcess = f ∘ R.project) ∧
    (∃! f : R.SignatureImage → StructuralTensor,
      D.structuralTensor = f ∘ R.project) := by
  exact ⟨factorsThrough_signatureImage R D.reset D.reset_invariant,
    factorsThrough_signatureImage R D.recurrence D.recurrence_invariant,
    factorsThrough_signatureImage R D.excursion D.excursion_invariant,
    factorsThrough_signatureImage R D.waiting D.waiting_invariant,
    factorsThrough_signatureImage R D.predictive D.predictive_invariant,
    factorsThrough_signatureImage R D.relation D.relation_invariant,
    factorsThrough_signatureImage R D.positiveProcess
      D.positiveProcess_invariant,
    factorsThrough_signatureImage R D.structuralTensor
      D.structuralTensor_invariant⟩

end RelativeUpstreamPrimitiveClosure
end NCG
