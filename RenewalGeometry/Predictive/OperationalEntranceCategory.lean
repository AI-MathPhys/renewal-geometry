/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.TypedPredictiveCategoryExact
import RenewalGeometry.Predictive.TypedFinitePredictionExact

/-!
# The category of finite typed operational-predictive models and relative row minimality
(`thm:supp-relative-primitive-floor`, emergent-spacetime manuscript)

We build the "fixed category of finite typed operational-predictive models" in which the
manuscript audits the semantic entrance `[𝔊; 𝔒, ℙ⁺, Θ, Λ]`.

* `OperationalEntrance.AnchoredGrammar` — the fixed typed potential event grammar `𝔊`:
  a finite typed event grammar (`def:supp-event-grammar`), a finite set of named potential
  events (events, writers and Reads that may or may not be physically present), and a
  finite set of named axes of an anchored real Euclidean space (the positive packet's
  anchored plane, with orthonormal named basis `anchor`).
* `OperationalEntrance.Model 𝔊` — a finite typed operational-predictive model over `𝔊`,
  given by its four semantic rows: the actual-occurrence interface `𝔒` (`occurs`, the set of
  potential events physically present), the complete predictive law `ℙ⁺` (`law`, a
  conditional operational law on the grammar), the protected orientation section `Θ`
  (`orientation`, an orientation of the anchored space, i.e. the ray of a unit alternating
  form) and the absolute physical calibration `Λ` (`calibration`, the positive physical
  duration scale `T = Λ S` of the internal waiting variable).
* `OperationalEntrance.RowIso keep M N` — anchored isomorphisms retaining the rows selected
  by `keep`: a linear automorphism of the anchored space fixing every named axis and a
  linear change of physical time unit fixing the anchored unit, carrying every retained row
  of `M` to that of `N` (named events, letters and outcomes are anchors and are fixed).
  `OperationalEntrance.Entrance 𝔊 keep` is the resulting groupoid; `Entrance 𝔊 full` is the
  category of full models and `Entrance 𝔊 (forgetting r)` the category of reducts with row
  `r` forgotten; `OperationalEntrance.reduct` is the forgetful functor.
* (R1) `typedLaw_minimal_isTerminal`, `absoluteRate_sum`, `calibration_eq_inv_sum_absoluteRate`,
  `orientation_eq_or_eq_neg_anchor`: the predictive row alone gives the terminal (unique
  coarsest reachable) predictive presentation, invariantly under full anchored isomorphism;
  winner law and calibration give the absolute rates `k_a = p_a / Λ`, which recover `Λ`; the
  orientation row is one of the two sections of the anchored orientation torsor.
* (R2) `separating_pairs`, `entrance_rows_irredundant`: for each row two anchored finite
  models with identical reducts (an anchored isomorphism of the reducts) and inequivalent
  full models (no anchored isomorphism), realized by exactly the manuscript's mechanisms:
  a Bernoulli instrument with `Pr(a) = 1/4` versus `3/4`, an adjoined potential writer `W`
  actual in one model only, opposite unit alternating forms `ω(e₁,e₂) = ±1` on a plane with
  identical positive Gram `I₂`, and physical durations `T = c₀ S` versus `T = c₁ S` with
  identical winner law but different absolute rates and waiting laws.
* (R3) `ConservativeRefinement`, `refinement_preserves_separation`,
  `no_reconstruction_after_refinement`, `spectatorRefinement`,
  `cofinal_spectator_tower_separating`: every common conservative refinement (functorial on
  every reduct, with a functorial discard that undoes it), in particular tensoring with the
  same spectator model at every cutoff of a cofinal tower, keeps every separating pair
  separating, so no reconstruction of the forgotten row which is functorial on reducts exists
  at any cutoff, on any cofinal tail, or on any refined (limit) object.
* (R4) `orientation_absorption`: when the occurrence packet contains an actual named Read
  and a deterministic decoder into the orientation torsor, the section and the Read value
  determine one another, and the two available decoders differ by global reversal (a
  relocation, not a reduction, of the orientation choice); without a decoder no map from the
  occurrence packet together with the remaining rows recovers the section.
* `relative_primitive_floor`: the bundled theorem.
-/

namespace RenewalGeometry

namespace OperationalEntrance

open FiniteTypedEventGrammar CategoryTheory

/-- The four semantic rows of the entrance `[𝔊; 𝔒, ℙ⁺, Θ, Λ]`. -/
inductive Row
  | occurrence
  | prediction
  | orientation
  | calibration
  deriving DecidableEq

/-- Retain every row. -/
abbrev full : Row → Prop := fun _ => True

/-- Retain every row except `r`. -/
abbrev forgetting (r : Row) : Row → Prop := fun r' => r' ≠ r

/-- The fixed anchored typed potential event grammar `𝔊`. -/
structure AnchoredGrammar where
  /-- the finite typed event grammar (`def:supp-event-grammar`) -/
  grammar : FiniteTypedEventGrammar
  /-- the named potential events, writers and Reads -/
  PotentialEvent : Type
  [eventFintype : Fintype PotentialEvent]
  /-- the named axes of the anchored positive space -/
  Axis : Type
  [axisFintype : Fintype Axis]
  [axisDecidableEq : DecidableEq Axis]

namespace AnchoredGrammar

attribute [instance] eventFintype axisFintype axisDecidableEq

variable (𝔊 : AnchoredGrammar)

/-- The anchored real Euclidean space of the positive packet. -/
abbrev Plane : Type := EuclideanSpace ℝ 𝔊.Axis

/-- The named orthonormal basis of the anchored space. -/
noncomputable def anchor : Module.Basis 𝔊.Axis ℝ 𝔊.Plane :=
  (EuclideanSpace.basisFun 𝔊.Axis ℝ).toBasis

/-- Orientation sections of the anchored space (rays of nonzero alternating forms). -/
abbrev Section : Type := Orientation ℝ 𝔊.Plane 𝔊.Axis

/-- The positive Gram datum of the anchored basis is the identity matrix. -/
theorem anchor_gram :
    Matrix.of (fun i j => inner ℝ (𝔊.anchor i) (𝔊.anchor j)) = (1 : Matrix 𝔊.Axis 𝔊.Axis ℝ) := by
  ext i j
  simp only [anchor, OrthonormalBasis.coe_toBasis, Matrix.of_apply, Matrix.one_apply]
  exact orthonormal_iff_ite.mp (EuclideanSpace.basisFun 𝔊.Axis ℝ).orthonormal i j

end AnchoredGrammar

/-- A finite typed operational-predictive model over the anchored grammar `𝔊`, given by its
four semantic rows. -/
structure Model (𝔊 : AnchoredGrammar) where
  /-- `𝔒`: the potential events, writers and Reads physically present -/
  occurs : Set 𝔊.PotentialEvent
  /-- `ℙ⁺`: the complete predictive law -/
  law : 𝔊.grammar.ConditionalLaw
  /-- `Θ`: the protected orientation section -/
  orientation : 𝔊.Section
  /-- `Λ`: the absolute physical calibration (duration scale) -/
  calibration : ℝ
  calibration_pos : 0 < calibration

variable {𝔊 : AnchoredGrammar}

/-- Extensionality for conditional laws. -/
theorem conditionalLaw_ext {G : FiniteTypedEventGrammar} {P Q : G.ConditionalLaw}
    (h : ∀ {s x y : G.CutType} (w : TypedWord G.Letter s x) (a : G.Letter x y),
      P.prob w a = Q.prob w a) : P = Q := by
  cases P
  cases Q
  congr
  funext s x y w a
  exact h w a

/-- An anchored isomorphism of models retaining the rows selected by `keep`. -/
structure RowIso (keep : Row → Prop) (M N : Model 𝔊) where
  /-- named potential events are anchors: retained occurrence agrees -/
  occurs_iff : keep .occurrence → ∀ e, e ∈ M.occurs ↔ e ∈ N.occurs
  /-- letters and outcomes are anchors: retained predictive laws agree -/
  prob_eq : keep .prediction → ∀ {s x y : 𝔊.grammar.CutType}
    (w : TypedWord 𝔊.grammar.Letter s x) (a : 𝔊.grammar.Letter x y),
    N.law.prob w a = M.law.prob w a
  /-- the induced map of the anchored space -/
  frame : 𝔊.Plane ≃ₗ[ℝ] 𝔊.Plane
  frame_anchor : ∀ i, frame (𝔊.anchor i) = 𝔊.anchor i
  orientation_map : keep .orientation →
    Orientation.map 𝔊.Axis frame M.orientation = N.orientation
  /-- the induced change of physical time unit -/
  clock : ℝ ≃ₗ[ℝ] ℝ
  clock_unit : clock 1 = 1
  calibration_map : keep .calibration → clock M.calibration = N.calibration

namespace RowIso

variable {keep : Row → Prop} {M N P : Model 𝔊}

/-- An anchored map of the anchored space is the identity. -/
theorem frame_eq_refl (f : RowIso keep M N) : f.frame = LinearEquiv.refl ℝ 𝔊.Plane := by
  apply LinearEquiv.toLinearMap_injective
  exact 𝔊.anchor.ext fun i => by simp [f.frame_anchor]

/-- An anchored change of physical time unit is the identity. -/
theorem clock_eq_refl (f : RowIso keep M N) : f.clock = LinearEquiv.refl ℝ ℝ := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_ring
  simp [f.clock_unit]

theorem occurs_eq (f : RowIso keep M N) (hk : keep .occurrence) : M.occurs = N.occurs :=
  Set.ext (f.occurs_iff hk)

theorem law_eq (f : RowIso keep M N) (hk : keep .prediction) : M.law = N.law :=
  conditionalLaw_ext fun w a => (f.prob_eq hk w a).symm

theorem orientation_eq (f : RowIso keep M N) (hk : keep .orientation) :
    M.orientation = N.orientation := by
  have h := f.orientation_map hk
  rw [f.frame_eq_refl, Orientation.map_refl] at h
  exact h

theorem calibration_eq (f : RowIso keep M N) (hk : keep .calibration) :
    M.calibration = N.calibration := by
  have h := f.calibration_map hk
  rw [f.clock_eq_refl] at h
  exact h

/-- An anchored isomorphism from equalities of the retained rows. -/
def ofEq (hocc : keep .occurrence → M.occurs = N.occurs)
    (hlaw : keep .prediction → M.law = N.law)
    (hor : keep .orientation → M.orientation = N.orientation)
    (hcal : keep .calibration → M.calibration = N.calibration) : RowIso keep M N where
  occurs_iff hk e := by rw [hocc hk]
  prob_eq hk := fun _ _ => by rw [hlaw hk]
  frame := LinearEquiv.refl ℝ 𝔊.Plane
  frame_anchor _ := rfl
  orientation_map hk := by rw [Orientation.map_refl, hor hk]; rfl
  clock := LinearEquiv.refl ℝ ℝ
  clock_unit := rfl
  calibration_map hk := hcal hk

instance : Subsingleton (RowIso keep M N) := by
  constructor
  intro f g
  have hf := f.frame_eq_refl
  have hg := g.frame_eq_refl
  have cf := f.clock_eq_refl
  have cg := g.clock_eq_refl
  cases f
  cases g
  simp only at hf hg cf cg
  subst hf hg cf cg
  rfl

/-- The identity anchored isomorphism. -/
def refl (M : Model 𝔊) : RowIso keep M M :=
  ofEq (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- The inverse anchored isomorphism. -/
def symm (f : RowIso keep M N) : RowIso keep N M :=
  ofEq (fun hk => (f.occurs_eq hk).symm) (fun hk => (f.law_eq hk).symm)
    (fun hk => (f.orientation_eq hk).symm) (fun hk => (f.calibration_eq hk).symm)

/-- Composition of anchored isomorphisms. -/
def trans (f : RowIso keep M N) (g : RowIso keep N P) : RowIso keep M P :=
  ofEq (fun hk => (f.occurs_eq hk).trans (g.occurs_eq hk))
    (fun hk => (f.law_eq hk).trans (g.law_eq hk))
    (fun hk => (f.orientation_eq hk).trans (g.orientation_eq hk))
    (fun hk => (f.calibration_eq hk).trans (g.calibration_eq hk))

/-- Forgetting rows: an anchored isomorphism retaining `keep` retains every `keep' ≤ keep`. -/
def weaken {keep' : Row → Prop} (h : ∀ r, keep' r → keep r) (f : RowIso keep M N) :
    RowIso keep' M N :=
  ofEq (fun hk => f.occurs_eq (h _ hk)) (fun hk => f.law_eq (h _ hk))
    (fun hk => f.orientation_eq (h _ hk)) (fun hk => f.calibration_eq (h _ hk))

/-- Full anchored isomorphisms are exactly equalities of the four rows. -/
theorem nonempty_full_iff :
    Nonempty (RowIso full M N) ↔
      M.occurs = N.occurs ∧ M.law = N.law ∧ M.orientation = N.orientation ∧
        M.calibration = N.calibration :=
  ⟨fun ⟨f⟩ => ⟨f.occurs_eq trivial, f.law_eq trivial, f.orientation_eq trivial,
      f.calibration_eq trivial⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨ofEq (fun _ => h1) (fun _ => h2) (fun _ => h3) (fun _ => h4)⟩⟩

end RowIso

/-- The groupoid of models over `𝔊` with anchored isomorphisms retaining the rows `keep`:
`Entrance 𝔊 full` is the category of full models, `Entrance 𝔊 (forgetting r)` the category of
reducts with the row `r` forgotten. -/
def Entrance (𝔊 : AnchoredGrammar) (_keep : Row → Prop) : Type := Model 𝔊

/-- A model regarded as an object of `Entrance 𝔊 keep`. -/
def Entrance.of (keep : Row → Prop) (M : Model 𝔊) : Entrance 𝔊 keep := M

/-- The underlying model of an object of `Entrance 𝔊 keep`. -/
def Entrance.model {keep : Row → Prop} (X : Entrance 𝔊 keep) : Model 𝔊 := X

instance (keep : Row → Prop) : Category (Entrance 𝔊 keep) where
  Hom X Y := RowIso keep X.model Y.model
  id X := RowIso.refl X.model
  comp f g := RowIso.trans f g
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

instance (keep : Row → Prop) (X Y : Entrance 𝔊 keep) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (RowIso keep X.model Y.model))

instance (keep : Row → Prop) : Groupoid (Entrance 𝔊 keep) where
  inv f := RowIso.symm f
  inv_comp _ := Subsingleton.elim _ _
  comp_inv _ := Subsingleton.elim _ _

/-- The forgetful (reduct) functor `Entrance 𝔊 keep ⥤ Entrance 𝔊 keep'` for `keep' ≤ keep`. -/
def reduct {keep keep' : Row → Prop} (h : ∀ r, keep' r → keep r) :
    Entrance 𝔊 keep ⥤ Entrance 𝔊 keep' where
  obj X := X
  map f := RowIso.weaken h f
  map_id _ := Subsingleton.elim (α := RowIso keep' _ _) _ _
  map_comp _ _ := Subsingleton.elim (α := RowIso keep' _ _) _ _

/-- The reduct forgetting the row `r`. -/
abbrev forgetRow (r : Row) : Entrance 𝔊 full ⥤ Entrance 𝔊 (forgetting r) :=
  reduct fun _ _ => trivial

/-- A separating pair for the row `r`: the reducts with `r` forgotten are isomorphic in the
reduct category, while the full models are not isomorphic. -/
def IsSeparatingPair (r : Row) (M N : Model 𝔊) : Prop :=
  Nonempty ((forgetRow r).obj (Entrance.of full M) ≅ (forgetRow r).obj (Entrance.of full N)) ∧
    IsEmpty (Entrance.of full M ≅ Entrance.of full N)

theorem isSeparatingPair_iff (r : Row) (M N : Model 𝔊) :
    IsSeparatingPair r M N ↔
      Nonempty (RowIso (forgetting r) M N) ∧ ¬ Nonempty (RowIso full M N) := by
  constructor
  · rintro ⟨⟨e⟩, hne⟩
    exact ⟨⟨e.hom⟩, fun ⟨f⟩ => hne.false (Groupoid.isoEquivHom _ _ |>.symm f)⟩
  · rintro ⟨⟨f⟩, hne⟩
    refine ⟨⟨Groupoid.isoEquivHom _ _ |>.symm f⟩, ⟨fun e => hne ⟨e.hom⟩⟩⟩

/-- Isomorphic objects of the groupoid of full models are exactly anchored-isomorphic models. -/
theorem nonempty_iso_full_iff (M N : Model 𝔊) :
    Nonempty (Entrance.of full M ≅ Entrance.of full N) ↔ Nonempty (RowIso full M N) :=
  ⟨fun ⟨e⟩ => ⟨e.hom⟩, fun ⟨f⟩ => ⟨Groupoid.isoEquivHom _ _ |>.symm f⟩⟩

/-! ## Changing one row -/

namespace Model

/-- Replace the occurrence row. -/
def withOccurs (M : Model 𝔊) (S : Set 𝔊.PotentialEvent) : Model 𝔊 := { M with occurs := S }

/-- Replace the predictive row. -/
def withLaw (M : Model 𝔊) (P : 𝔊.grammar.ConditionalLaw) : Model 𝔊 := { M with law := P }

/-- Replace the orientation row. -/
def withOrientation (M : Model 𝔊) (o : 𝔊.Section) : Model 𝔊 := { M with orientation := o }

/-- Replace the calibration row. -/
def withCalibration (M : Model 𝔊) (c : ℝ) (hc : 0 < c) : Model 𝔊 :=
  { M with calibration := c, calibration_pos := hc }

end Model

/-- Changing the occurrence row to a different set gives a separating pair. -/
theorem separating_withOccurs (M : Model 𝔊) (S : Set 𝔊.PotentialEvent) (hS : M.occurs ≠ S) :
    IsSeparatingPair .occurrence M (M.withOccurs S) :=
  (isSeparatingPair_iff _ _ _).2
    ⟨⟨RowIso.ofEq (fun h => absurd rfl h) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩,
      fun ⟨f⟩ => hS (f.occurs_eq trivial)⟩

/-- Changing the predictive row to a different law gives a separating pair. -/
theorem separating_withLaw (M : Model 𝔊) (P : 𝔊.grammar.ConditionalLaw) (hP : M.law ≠ P) :
    IsSeparatingPair .prediction M (M.withLaw P) :=
  (isSeparatingPair_iff _ _ _).2
    ⟨⟨RowIso.ofEq (fun _ => rfl) (fun h => absurd rfl h) (fun _ => rfl) (fun _ => rfl)⟩,
      fun ⟨f⟩ => hP (f.law_eq trivial)⟩

/-- Reversing the protected orientation gives a separating pair. -/
theorem separating_reverseOrientation (M : Model 𝔊) :
    IsSeparatingPair .orientation M (M.withOrientation (-M.orientation)) :=
  (isSeparatingPair_iff _ _ _).2
    ⟨⟨RowIso.ofEq (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h) (fun _ => rfl)⟩,
      fun ⟨f⟩ => Module.Ray.ne_neg_self M.orientation (f.orientation_eq trivial)⟩

/-- Changing the absolute calibration gives a separating pair. -/
theorem separating_withCalibration (M : Model 𝔊) (c : ℝ) (hc : 0 < c)
    (hne : M.calibration ≠ c) :
    IsSeparatingPair .calibration M (M.withCalibration c hc) :=
  (isSeparatingPair_iff _ _ _).2
    ⟨⟨RowIso.ofEq (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h)⟩,
      fun ⟨f⟩ => hne (f.calibration_eq trivial)⟩

/-- **(R2), general form.**  Over any anchored grammar, a model `M`, a potential writer `W`
not actual in `M`, and a second law `P ≠ M.law` produce one anchored separating pair for each
of the four rows: adjoin `W` to the actual interface; replace the law; reverse the protected
orientation; rescale the physical calibration. -/
theorem separating_pairs (M : Model 𝔊) (W : 𝔊.PotentialEvent) (hW : W ∉ M.occurs)
    (P : 𝔊.grammar.ConditionalLaw) (hP : M.law ≠ P) :
    IsSeparatingPair .occurrence M (M.withOccurs (insert W M.occurs)) ∧
    IsSeparatingPair .prediction M (M.withLaw P) ∧
    IsSeparatingPair .orientation M (M.withOrientation (-M.orientation)) ∧
    IsSeparatingPair .calibration M
      (M.withCalibration (2 * M.calibration) (by linarith [M.calibration_pos])) := by
  refine ⟨separating_withOccurs M _ ?_, separating_withLaw M P hP,
    separating_reverseOrientation M, separating_withCalibration M _ _ ?_⟩
  · intro h
    exact hW (h ▸ Set.mem_insert W M.occurs)
  · intro h
    linarith [M.calibration_pos]

/-! ## (R1) What the rows supply -/

/-- The predictive row as a typed operational law (`TypedPredictiveCategory`), with the
trivial Read. -/
def Model.typedLaw (M : Model 𝔊) : TypedPredictiveCategory.TypedOperationalLaw where
  grammar := 𝔊.grammar
  law := M.law
  ReadValue := Unit
  read _ := ()
  read_congr _ := rfl

/-- **(R1), predictive part.**  The predictive row alone yields the minimum future quotient
`Z^min` as the terminal object of the category of reachable predictive presentations (the
unique coarsest reachable deterministic predictive realization,
`prop:supp-predictive-category`), and this carrier is unchanged along every anchored
isomorphism retaining the predictive row. -/
theorem typedLaw_minimal_isTerminal (M : Model 𝔊) :
    Nonempty (Limits.IsTerminal (TypedPredictiveCategory.minimal M.typedLaw)) ∧
    ∀ {keep : Row → Prop} {N : Model 𝔊}, RowIso keep M N → keep .prediction →
      M.typedLaw = N.typedLaw := by
  refine ⟨⟨TypedPredictiveCategory.minimal_isTerminal⟩, fun f hk => ?_⟩
  simp only [Model.typedLaw, f.law_eq hk]

/-- The absolute rate `k_a = p_a / Λ` of the letter `a` after the history `w`: the winner law
`p` of the predictive row read in the physical units of the calibration row. -/
noncomputable def absoluteRate (M : Model 𝔊) {s x y : 𝔊.grammar.CutType}
    (w : TypedWord 𝔊.grammar.Letter s x) (a : 𝔊.grammar.Letter x y) : ℝ :=
  M.law.prob w a / M.calibration

/-- The total absolute rate after a reachable history is `1/Λ`. -/
theorem absoluteRate_sum (M : Model 𝔊) {s x : 𝔊.grammar.CutType}
    (w : TypedWord 𝔊.grammar.Letter s x) (hw : 𝔊.grammar.Reachable w) :
    ∑ y : 𝔊.grammar.CutType, ∑ a : 𝔊.grammar.Letter x y, absoluteRate M w a
      = M.calibration⁻¹ := by
  simp only [absoluteRate, div_eq_mul_inv, ← Finset.sum_mul, M.law.sum_prob w hw, one_mul]

/-- **(R1), calibration part.**  The absolute rates recover the calibration
(`Λ = (Σ_a k_a)⁻¹`) and the winner law as their projective part (`p_a = k_a / Σ_b k_b`). -/
theorem calibration_eq_inv_sum_absoluteRate (M : Model 𝔊) {s x : 𝔊.grammar.CutType}
    (w : TypedWord 𝔊.grammar.Letter s x) (hw : 𝔊.grammar.Reachable w) :
    M.calibration =
        (∑ y : 𝔊.grammar.CutType, ∑ a : 𝔊.grammar.Letter x y, absoluteRate M w a)⁻¹ ∧
    ∀ {y : 𝔊.grammar.CutType} (a : 𝔊.grammar.Letter x y),
      M.law.prob w a = absoluteRate M w a /
        ∑ y : 𝔊.grammar.CutType, ∑ b : 𝔊.grammar.Letter x y, absoluteRate M w b := by
  have hc := M.calibration_pos.ne'
  refine ⟨by rw [absoluteRate_sum M w hw, inv_inv], fun a => ?_⟩
  rw [absoluteRate_sum M w hw, absoluteRate, div_inv_eq_mul, div_mul_cancel₀ _ hc]

/-- The physical waiting law of `T = Λ S` with `S ∼ Exp(1)`, through its survival function
`Pr(T > t) = e^{-t/Λ}`. -/
noncomputable def physicalSurvival (M : Model 𝔊) (t : ℝ) : ℝ := Real.exp (-t / M.calibration)

/-- **(R1), orientation part.**  The orientation row is one of the two sections of the
anchored orientation torsor. -/
theorem orientation_eq_or_eq_neg_anchor (M : Model 𝔊) :
    M.orientation = 𝔊.anchor.orientation ∨ M.orientation = -𝔊.anchor.orientation :=
  𝔊.anchor.orientation_eq_or_eq_neg M.orientation

/-! ## (R3) Conservative refinement and cofinal reindexing -/

/-- A common conservative refinement of the models over `𝔊` into a row-structured target `Y`
(`rel keep` is anchored isomorphism retaining the rows `keep` in the refined theory): the
refinement is functorial on every reduct, and a physical discard, functorial on full models,
undoes it up to anchored isomorphism. -/
structure ConservativeRefinement (𝔊 : AnchoredGrammar) (Y : Type*)
    (rel : (Row → Prop) → Y → Y → Prop) where
  /-- refine (append spectator records) -/
  extend : Model 𝔊 → Y
  /-- discard the spectator records -/
  discard : Y → Model 𝔊
  extend_rel : ∀ (keep : Row → Prop) (M N : Model 𝔊), Nonempty (RowIso keep M N) →
    rel keep (extend M) (extend N)
  discard_rel : ∀ X X' : Y, rel full X X' → Nonempty (RowIso full (discard X) (discard X'))
  discard_extend : ∀ M : Model 𝔊, Nonempty (RowIso full (discard (extend M)) M)

/-- **(R3).**  A separating pair stays separating after every common conservative refinement:
the refined reducts are still related, the refined full models are not. -/
theorem refinement_preserves_separation {Y : Type*} {rel : (Row → Prop) → Y → Y → Prop}
    (F : ConservativeRefinement 𝔊 Y rel) {r : Row} {M N : Model 𝔊}
    (h : IsSeparatingPair r M N) :
    rel (forgetting r) (F.extend M) (F.extend N) ∧ ¬ rel full (F.extend M) (F.extend N) := by
  obtain ⟨hred, hfull⟩ := (isSeparatingPair_iff _ _ _).1 h
  refine ⟨F.extend_rel _ M N hred, fun hrel => hfull ?_⟩
  obtain ⟨g⟩ := F.discard_rel _ _ hrel
  obtain ⟨eM⟩ := F.discard_extend M
  obtain ⟨eN⟩ := F.discard_extend N
  exact ⟨(eM.symm.trans g).trans eN⟩

/-- **(R3), no reconstruction.**  After any common conservative refinement in which full
anchored isomorphism is an equivalence relation, no reconstruction `Rec` of the full refined
model which is functorial on the reducts forgetting `r` exists, once `r` has a separating
pair. -/
theorem no_reconstruction_after_refinement {Y : Type*} {rel : (Row → Prop) → Y → Y → Prop}
    (F : ConservativeRefinement 𝔊 Y rel)
    (hsymm : ∀ X X' : Y, rel full X X' → rel full X' X)
    (htrans : ∀ X X' X'' : Y, rel full X X' → rel full X' X'' → rel full X X'')
    {r : Row} {M N : Model 𝔊} (h : IsSeparatingPair r M N) :
    ¬ ∃ Rec : Y → Y, (∀ X X' : Y, rel (forgetting r) X X' → rel full (Rec X) (Rec X')) ∧
      ∀ X : Y, rel full (Rec X) X := by
  rintro ⟨Rec, hfun, hrec⟩
  obtain ⟨hred, hfull⟩ := refinement_preserves_separation F h
  exact hfull (htrans _ _ _ (hsymm _ _ (hrec _)) (htrans _ _ _ (hfun _ _ hred) (hrec _)))

/-- The trivial refinement (the theory at the base cutoff itself). -/
def identityRefinement (𝔊 : AnchoredGrammar) :
    ConservativeRefinement 𝔊 (Model 𝔊) (fun keep M N => Nonempty (RowIso keep M N)) where
  extend := id
  discard := id
  extend_rel _ _ _ h := h
  discard_rel _ _ h := h
  discard_extend M := ⟨RowIso.refl M⟩

/-- **(R3), categorical form at a cutoff.**  Once `r` has a separating pair, no functor from
the reducts forgetting `r` back to full models is a section of the forgetful functor up to
natural isomorphism. -/
theorem no_functorial_reconstruction {r : Row} {M N : Model 𝔊} (h : IsSeparatingPair r M N)
    (Rec : Entrance 𝔊 (forgetting r) ⥤ Entrance 𝔊 full) :
    IsEmpty (forgetRow r ⋙ Rec ≅ 𝟭 (Entrance 𝔊 full)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨⟨i⟩, hfull⟩ := h
  exact hfull.false ((e.app _).symm ≪≫ Rec.mapIso i ≪≫ e.app _)

/-- Independent composition with a spectator: the pair `(M, S)` with anchored isomorphisms
componentwise (`prop:supp-grand-monoidal` identifies the independent composite with the
pair). -/
def pairRel {𝔖 : AnchoredGrammar} (keep : Row → Prop) (X X' : Model 𝔊 × Model 𝔖) : Prop :=
  Nonempty (RowIso keep X.1 X'.1) ∧ Nonempty (RowIso keep X.2 X'.2)

theorem pairRel_symm {𝔖 : AnchoredGrammar} (keep : Row → Prop) (X X' : Model 𝔊 × Model 𝔖)
    (h : pairRel keep X X') : pairRel keep X' X :=
  ⟨h.1.map RowIso.symm, h.2.map RowIso.symm⟩

theorem pairRel_trans {𝔖 : AnchoredGrammar} (keep : Row → Prop)
    (X X' X'' : Model 𝔊 × Model 𝔖) (h : pairRel keep X X') (h' : pairRel keep X' X'') :
    pairRel keep X X'' :=
  ⟨⟨h.1.some.trans h'.1.some⟩, ⟨h.2.some.trans h'.2.some⟩⟩

/-- Tensoring with the same spectator model `S`, with spectator discard. -/
def spectatorRefinement {𝔖 : AnchoredGrammar} (S : Model 𝔖) :
    ConservativeRefinement 𝔊 (Model 𝔊 × Model 𝔖) pairRel where
  extend M := (M, S)
  discard := Prod.fst
  extend_rel _ _ _ h := ⟨h, ⟨RowIso.refl S⟩⟩
  discard_rel _ _ h := h.1
  discard_extend M := ⟨RowIso.refl M⟩

/-- **(R3), cofinal form.**  Along any tower of cutoffs `n`, each tensoring both members of a
separating pair with the same spectator model `S n` and discarding only spectator records:
at every cutoff the refined reducts are anchored isomorphic and the refined full models are
not; consequently no full anchored isomorphism appears on any cofinal tail, and no
reconstruction functorial on reducts exists at any cutoff. -/
theorem cofinal_spectator_tower_separating (𝔖 : ℕ → AnchoredGrammar) (S : ∀ n, Model (𝔖 n))
    {r : Row} {M N : Model 𝔊} (h : IsSeparatingPair r M N) :
    (∀ n, pairRel (forgetting r) (M, S n) (N, S n) ∧ ¬ pairRel full (M, S n) (N, S n)) ∧
    (¬ ∃ n₀, ∀ n ≥ n₀, pairRel full (M, S n) (N, S n)) ∧
    (∀ n, ¬ ∃ Rec : Model 𝔊 × Model (𝔖 n) → Model 𝔊 × Model (𝔖 n),
      (∀ X X', pairRel (forgetting r) X X' → pairRel full (Rec X) (Rec X')) ∧
        ∀ X, pairRel full (Rec X) X) := by
  have key := fun n => refinement_preserves_separation (spectatorRefinement (𝔊 := 𝔊) (S n)) h
  refine ⟨key, fun ⟨n₀, hn⟩ => (key n₀).2 (hn n₀ le_rfl), fun n => ?_⟩
  exact no_reconstruction_after_refinement (spectatorRefinement (S n)) (pairRel_symm full)
    (pairRel_trans full) h

/-! ## (R4) Absorbing the orientation into occurrence -/

/-- A deterministic physical decoder from the binary Read value into the orientation torsor. -/
abbrev OrientationDecoder (𝔊 : AnchoredGrammar) : Type := ℤˣ ≃ 𝔊.Section

/-- A named Read of the occurrence packet with its recorded binary value. -/
structure ReadRecord (𝔊 : AnchoredGrammar) where
  /-- the named Read -/
  read : 𝔊.PotentialEvent
  /-- its recorded value -/
  value : ℤˣ

/-- The orientation of `M` is absorbed into occurrence through the actual Read `K` and the
decoder `d`. -/
def Absorbs (d : OrientationDecoder 𝔊) (K : ReadRecord 𝔊) (M : Model 𝔊) : Prop :=
  K.read ∈ M.occurs ∧ M.orientation = d K.value

/-- The reversed decoder. -/
def OrientationDecoder.reverse (d : OrientationDecoder 𝔊) : OrientationDecoder 𝔊 :=
  d.trans (Equiv.neg _)

theorem ne_neg_of_section (o : 𝔊.Section) : o ≠ -o := Module.Ray.ne_neg_self o

/-- Every decoder is `d` or its reversal. -/
theorem decoder_eq_or_eq_reverse (d d' : OrientationDecoder 𝔊) : d' = d ∨ d' = d.reverse := by
  have two : ∀ o o' : 𝔊.Section, o' = o ∨ o' = -o := fun o o' =>
    Orientation.eq_or_eq_neg o' o finrank_euclideanSpace.symm
  have hd : d (-1) = -(d 1) := by
    rcases two (d 1) (d (-1)) with h | h
    · exact absurd (d.injective h) (by decide)
    · exact h
  have hd' : d' (-1) = -(d' 1) := by
    rcases two (d' 1) (d' (-1)) with h | h
    · exact absurd (d'.injective h) (by decide)
    · exact h
  rcases two (d 1) (d' 1) with h | h
  · left
    ext v
    rcases Int.units_eq_one_or v with rfl | rfl
    · exact h
    · rw [hd, hd', h]
  · right
    ext v
    rcases Int.units_eq_one_or v with rfl | rfl
    · exact h
    · change d' (-1) = -(d (-1))
      rw [hd, hd', h]

/-- **(R4).**  (a) With an actual named Read and a decoder, the section and the Read value
determine each other.  (b) The decoder is itself one of exactly two choices exchanged by
global reversal, and the reversed decoder decodes every value to the opposite section: the
bundling relocates, and does not reduce, the orientation choice.  (c) Without a decoder, no
map from the occurrence packet (actual interface and Read value) and the remaining rows to
sections is correct: some model with identical occurrence, law and calibration has a
different orientation. -/
theorem orientation_absorption :
    (∀ (d : OrientationDecoder 𝔊) (K : ReadRecord 𝔊) (M : Model 𝔊), Absorbs d K M →
      d.symm M.orientation = K.value) ∧
    (∀ (d : OrientationDecoder 𝔊) (K K' : ReadRecord 𝔊) (M M' : Model 𝔊),
      Absorbs d K M → Absorbs d K' M' →
        (M.orientation = M'.orientation ↔ K.value = K'.value)) ∧
    (∀ (d : OrientationDecoder 𝔊) (v : ℤˣ), d.reverse v = -(d v) ∧ d.reverse v ≠ d v) ∧
    (∀ d d' : OrientationDecoder 𝔊, d' = d ∨ d' = d.reverse) ∧
    (∀ (f : Set 𝔊.PotentialEvent → ℤˣ → 𝔊.grammar.ConditionalLaw → ℝ → 𝔊.Section)
      (M : Model 𝔊) (K : ReadRecord 𝔊), ∃ M' : Model 𝔊,
        M'.occurs = M.occurs ∧ M'.law = M.law ∧ M'.calibration = M.calibration ∧
        M'.orientation ≠ f M.occurs K.value M.law M.calibration) := by
  refine ⟨fun d K M h => by rw [h.2, Equiv.symm_apply_apply], fun d K K' M M' h h' => ?_,
    fun d v => ⟨rfl, fun hv => ne_neg_of_section (d v) hv.symm⟩, decoder_eq_or_eq_reverse,
    fun f M K => ?_⟩
  · rw [h.2, h'.2]
    exact d.injective.eq_iff
  · by_cases hM : M.orientation = f M.occurs K.value M.law M.calibration
    · refine ⟨M.withOrientation (-M.orientation), rfl, rfl, rfl, fun h => ?_⟩
      exact ne_neg_of_section M.orientation (hM.trans h.symm)
    · exact ⟨M, rfl, rfl, rfl, hM⟩

/-! ## The manuscript's anchored finite models -/

/-- The anchored grammar of the manuscript's audit: one complete binary instrument with named
outcomes `a = true`, `b = false` on one cut type (the binary grammar of
`TypedFinitePredictionCountermodel`), two named potential events (the base event `false` and
a potential deterministic writer `W = true`), and an anchored real two-plane with named basis
`e₁, e₂`. -/
abbrev entranceGrammar : AnchoredGrammar where
  grammar := TypedFinitePredictionCountermodel.grammar
  PotentialEvent := Bool
  Axis := Fin 2

/-- The Bernoulli law `Pr(a) = p` of the complete binary instrument, after every history. -/
noncomputable def bernoulliLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entranceGrammar.grammar.ConditionalLaw where
  prob := fun _ a => if (a : Bool) then p else 1 - p
  prob_nonneg := by
    intro s x y h a
    cases a
    · simp only [Bool.false_eq_true, ite_false]
      linarith
    · simpa using hp0
  prob_eq_zero_of_not_admissible := fun _ _ ha => absurd trivial ha
  sum_prob := by
    intro s x h _
    change ∑ y : Unit, ∑ a : Bool, (if (a : Bool) then p else 1 - p) = 1
    simp

/-- `Pr(a) = p` at every history. -/
theorem bernoulliLaw_prob_a (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {s x y : Unit}
    (w : TypedWord entranceGrammar.grammar.Letter s x) :
    (bernoulliLaw p hp0 hp1).prob (y := y) w (true : Bool) = p := rfl

theorem bernoulliLaw_ne {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hpq : p ≠ q) : bernoulliLaw p hp0 hp1 ≠ bernoulliLaw q hq0 hq1 := by
  intro h
  apply hpq
  have := congrArg (fun P : entranceGrammar.grammar.ConditionalLaw =>
    P.prob (s := ()) (x := ()) (y := ()) (TypedWord.nil ()) (true : Bool)) h
  simpa [bernoulliLaw_prob_a] using this

/-- The base model: only the base event is actual, fair instrument, the anchored orientation
`ω(e₁,e₂) = +1`, unit calibration. -/
noncomputable def baseModel : Model entranceGrammar where
  occurs := {false}
  law := bernoulliLaw (1 / 2) (by norm_num) (by norm_num)
  orientation := entranceGrammar.anchor.orientation
  calibration := 1
  calibration_pos := one_pos

/-- The prediction pair: `Pr(a) = 1/4` versus `Pr(a) = 3/4`. -/
noncomputable def predictionLeft : Model entranceGrammar :=
  baseModel.withLaw (bernoulliLaw (1 / 4) (by norm_num) (by norm_num))

noncomputable def predictionRight : Model entranceGrammar :=
  predictionLeft.withLaw (bernoulliLaw (3 / 4) (by norm_num) (by norm_num))

/-- The occurrence pair: the writer `W` is actual in the second model only. -/
noncomputable def occurrenceRight : Model entranceGrammar :=
  baseModel.withOccurs {false, true}

/-- The orientation pair: `ω(e₁,e₂) = -1`. -/
noncomputable def orientationRight : Model entranceGrammar :=
  baseModel.withOrientation (-baseModel.orientation)

/-- The calibration pair: physical durations `T = 2 S` instead of `T = S`. -/
noncomputable def calibrationRight : Model entranceGrammar :=
  baseModel.withCalibration 2 two_pos

/-- **(R2), the manuscript's mechanisms.**  The four explicit anchored separating pairs:
(ℙ⁺) Bernoulli laws `Pr(a) = 1/4` and `3/4`; (𝔒) the writer `W` actual in one model only,
with identical structural and probabilistic data; (Θ) the same anchored plane with positive
Gram `I₂` in both models and opposite unit alternating forms, `ω(e₁,e₂) = +1` (the ray of
`det_e`) and `-1` (the ray of `-det_e`); (Λ) identical winner law and different physical
durations `T = S`, `T = 2S`, hence different absolute rates `k_a = p_a/Λ` and different
waiting laws `Pr(T > t) = e^{-t/Λ}`. -/
theorem entrance_separating_mechanisms :
    (IsSeparatingPair .prediction predictionLeft predictionRight ∧
      predictionLeft.law.prob (s := ()) (x := ()) (y := ()) (TypedWord.nil ()) (true : Bool)
        = 1 / 4 ∧
      predictionRight.law.prob (s := ()) (x := ()) (y := ()) (TypedWord.nil ()) (true : Bool)
        = 3 / 4) ∧
    (IsSeparatingPair .occurrence baseModel occurrenceRight ∧
      true ∉ baseModel.occurs ∧ true ∈ occurrenceRight.occurs ∧
      occurrenceRight.law = baseModel.law) ∧
    (IsSeparatingPair .orientation baseModel orientationRight ∧
      Matrix.of (fun i j => inner ℝ (entranceGrammar.anchor i) (entranceGrammar.anchor j))
        = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      entranceGrammar.anchor.det entranceGrammar.anchor = 1 ∧
      (-entranceGrammar.anchor.det) entranceGrammar.anchor = -1 ∧
      baseModel.orientation = rayOfNeZero ℝ _ entranceGrammar.anchor.det_ne_zero ∧
      orientationRight.orientation =
        rayOfNeZero ℝ _ (neg_ne_zero.2 entranceGrammar.anchor.det_ne_zero)) ∧
    (IsSeparatingPair .calibration baseModel calibrationRight ∧
      calibrationRight.law = baseModel.law ∧
      absoluteRate baseModel (s := ()) (x := ()) (y := ()) (TypedWord.nil ()) (true : Bool)
        = 1 / 2 ∧
      absoluteRate calibrationRight (s := ()) (x := ()) (y := ()) (TypedWord.nil ())
        (true : Bool) = 1 / 4 ∧
      physicalSurvival baseModel 1 ≠ physicalSurvival calibrationRight 1) := by
  refine ⟨⟨separating_withLaw _ _
      (bernoulliLaw_ne (p := 1 / 4) (q := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)), rfl, rfl⟩,
    ⟨separating_withOccurs _ _ ?_, by simp [baseModel], by simp [occurrenceRight,
      Model.withOccurs], rfl⟩,
    ⟨separating_reverseOrientation _, entranceGrammar.anchor_gram,
      entranceGrammar.anchor.det_self,
      by rw [AlternatingMap.neg_apply, Module.Basis.det_self], rfl, ?_⟩,
    ⟨separating_withCalibration _ _ _ (by norm_num [baseModel]), rfl, ?_, ?_, ?_⟩⟩
  · intro h
    have : true ∈ ({false} : Set Bool) := by
      change true ∈ baseModel.occurs
      rw [h]
      simp
    simp at this
  · change -entranceGrammar.anchor.orientation = _
    rw [Module.Basis.orientation, neg_rayOfNeZero]
  · simp [absoluteRate, baseModel, bernoulliLaw_prob_a]
  · simp only [absoluteRate, calibrationRight, Model.withCalibration, baseModel,
      bernoulliLaw_prob_a]
    norm_num
  · simp only [physicalSurvival, baseModel, calibrationRight, Model.withCalibration]
    intro h
    have := Real.exp_injective h
    norm_num at this

/-! ## The bundled theorem -/

/-- **`thm:supp-relative-primitive-floor`.**  In the groupoid `Entrance entranceGrammar full`
of finite typed operational-predictive models over the fixed anchored grammar (with reducts
`Entrance entranceGrammar (forgetting r)` and forgetful functors `forgetRow r`):

* (R1) the predictive row gives the minimum future quotient as the terminal reachable
  predictive presentation, invariantly under anchored isomorphism; the calibration row is
  recovered from the absolute rates `k_a = p_a/Λ` (and the winner law is their projective
  part); the orientation row is one of the two sections of the anchored torsor;
* (R2)–(R3) every row `r` has an anchored separating pair (isomorphic reducts, non-isomorphic
  full models) which stays separating after every common conservative refinement, admits no
  reconstruction functorial on refined reducts, no functorial section of `forgetRow r`, and
  no full isomorphism on any cofinal tail of a spectator tower;
* (R4) orientation is absorbed into occurrence exactly through an actual Read with a decoder,
  which is a relocation of the two-valued choice; without the decoder no map from the
  occurrence packet and the other rows recovers it. -/
theorem relative_primitive_floor :
    (∀ M : Model entranceGrammar,
      Nonempty (Limits.IsTerminal (TypedPredictiveCategory.minimal M.typedLaw)) ∧
      (∀ {keep : Row → Prop} {N : Model entranceGrammar}, RowIso keep M N → keep .prediction →
        M.typedLaw = N.typedLaw) ∧
      (∀ {s x : Unit} (w : TypedWord entranceGrammar.grammar.Letter s x),
        M.calibration = (∑ y : Unit, ∑ a : entranceGrammar.grammar.Letter x y,
          absoluteRate M w a)⁻¹) ∧
      (M.orientation = entranceGrammar.anchor.orientation ∨
        M.orientation = -entranceGrammar.anchor.orientation)) ∧
    (∀ r : Row, ∃ M N : Model entranceGrammar, IsSeparatingPair r M N ∧
      (∀ (n : ℕ → AnchoredGrammar) (S : ∀ k, Model (n k)),
        (∀ k, pairRel (forgetting r) (M, S k) (N, S k) ∧ ¬ pairRel full (M, S k) (N, S k)) ∧
        ¬ ∃ k₀, ∀ k ≥ k₀, pairRel full (M, S k) (N, S k)) ∧
      (∀ Rec : Entrance entranceGrammar (forgetting r) ⥤ Entrance entranceGrammar full,
        IsEmpty (forgetRow r ⋙ Rec ≅ 𝟭 _))) ∧
    (∀ {Y : Type} {rel : (Row → Prop) → Y → Y → Prop}
      (F : ConservativeRefinement entranceGrammar Y rel) (r : Row) (M N : Model entranceGrammar),
      IsSeparatingPair r M N →
        rel (forgetting r) (F.extend M) (F.extend N) ∧ ¬ rel full (F.extend M) (F.extend N)) ∧
    ((∀ (d : OrientationDecoder entranceGrammar) (K : ReadRecord entranceGrammar)
        (M : Model entranceGrammar), Absorbs d K M → d.symm M.orientation = K.value) ∧
      (∀ d d' : OrientationDecoder entranceGrammar, d' = d ∨ d' = d.reverse) ∧
      (∀ (d : OrientationDecoder entranceGrammar) (v : ℤˣ), d.reverse v ≠ d v) ∧
      (∀ (f : Set Bool → ℤˣ → entranceGrammar.grammar.ConditionalLaw → ℝ →
          entranceGrammar.Section) (M : Model entranceGrammar) (K : ReadRecord entranceGrammar),
        ∃ M' : Model entranceGrammar,
          M'.occurs = M.occurs ∧ M'.law = M.law ∧ M'.calibration = M.calibration ∧
          M'.orientation ≠ f M.occurs K.value M.law M.calibration)) := by
  obtain ⟨hP, hO, hT, hL⟩ := entrance_separating_mechanisms
  have pairs : ∀ r : Row, ∃ M N : Model entranceGrammar, IsSeparatingPair r M N := by
    intro r
    cases r
    · exact ⟨_, _, hO.1⟩
    · exact ⟨_, _, hP.1⟩
    · exact ⟨_, _, hT.1⟩
    · exact ⟨_, _, hL.1⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := orientation_absorption (𝔊 := entranceGrammar)
  refine ⟨fun M => ⟨(typedLaw_minimal_isTerminal M).1, (typedLaw_minimal_isTerminal M).2,
      fun w => (calibration_eq_inv_sum_absoluteRate M w trivial).1,
      orientation_eq_or_eq_neg_anchor M⟩,
    fun r => ?_, fun F r M N h => refinement_preserves_separation F h,
    a1, a4, fun d v => (a3 d v).2, a5⟩
  obtain ⟨M, N, h⟩ := pairs r
  refine ⟨M, N, h, fun n S => ?_, fun Rec => no_functorial_reconstruction h Rec⟩
  obtain ⟨t1, t2, -⟩ := cofinal_spectator_tower_separating n S h
  exact ⟨t1, t2⟩

end OperationalEntrance

end RenewalGeometry
