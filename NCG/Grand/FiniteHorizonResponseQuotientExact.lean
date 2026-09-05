/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Data.Setoid.Basic

/-!
# Canonical finite-horizon response quotient

Exact encoding of `def:GT-finite-horizon-response` and
`thm:GT-finite-horizon-response-quotient`.

* `responseTrace h Φ T hcont x : C(Icc 0 T, K)` is `t ↦ h(Φ_t x)`;
* `responsePseudometric` is `d_T^h(x,y) = ‖Σ_T x - Σ_T y‖_{C([0,T];K)}`
  (the sup metric on `C(Icc 0 T, K)`), and `responseSetoid` identifies
  exactly the fibres of `Σ_T` (`responseSetoid_iff`);
* `responseQuotient` is `Q_T^h = X / {d_T^h = 0}`, carrying the quotient
  metric `responseQuotientMetric`, and `responseLift : Q_T^h → C(Icc 0 T, K)`
  is an **isometry** (`responseLift_isometry`) whose range is `Σ_T(X)`
  (`responseLift_range`) — so `Q_T^h ≅ Σ_T(X)` (`responseQuotientEquivRange`),
  a compact set (`responseRange_isCompact`);
* `response_quotient_coarsest`: if every response coordinate factors through
  `q : X → Z`, there is a unique map `range q → Q_T^h` compatible with the
  response maps, and it is surjective (universal property);
* `restrictTrace` and `responseRestriction`: for `T₁ ≤ T₂` restriction of
  traces descends to a canonical surjection `Q_{T₂}^h → Q_{T₁}^h`;
* `allFuture_descends` / `allFuture_iff`: the all-horizon quotient (the
  kernel of the whole family) maps onto each `Q_T^h` and identifies two
  points exactly when every finite horizon does; `allFuture_strictly_finer`
  exhibits a packet where the all-horizon quotient is strictly finer than a
  given finite-horizon quotient.

Scope: the record is stated for a compact admitted space `X`; compactness is
used only for the compactness of the image. The "constant-rank distribution /
smooth atlas not required" clause is reflected by the absence of any such
hypothesis.
-/

open Set Topology

namespace NCG
namespace FiniteHorizonResponseQuotient

variable {X K : Type*} [MetricSpace K]

/-- The finite-horizon response trace `Σ_T(x)(t) = h(Φ_{t,0} x)`. -/
noncomputable def responseTrace (h : X → K) (Φ : ℝ → X → X) (T : ℝ)
    (hcont : ∀ x, Continuous fun t : Icc (0 : ℝ) T => h (Φ t x)) (x : X) :
    C(Icc (0 : ℝ) T, K) :=
  ⟨fun t => h (Φ t x), hcont x⟩

@[simp] theorem responseTrace_apply (h : X → K) (Φ : ℝ → X → X) (T : ℝ)
    (hcont : ∀ x, Continuous fun t : Icc (0 : ℝ) T => h (Φ t x)) (x : X)
    (t : Icc (0 : ℝ) T) : responseTrace h Φ T hcont x t = h (Φ t x) := rfl

section Abstract

/-! The quotient construction only uses the trace map `Tr : X → Y` into a
metric space of traces; we develop it for an arbitrary such map and
specialize to `responseTrace`. -/

variable {Y : Type*}

/-- The response pseudometric `d(x,y) = dist (Tr x) (Tr y)` (TR.1). -/
noncomputable def responsePseudometric [MetricSpace Y] (Tr : X → Y) (x y : X) : ℝ :=
  dist (Tr x) (Tr y)

/-- Points at response distance zero: exactly the fibres of `Tr`. -/
abbrev responseSetoid (Tr : X → Y) : Setoid X := Setoid.ker Tr

theorem responseSetoid_iff [MetricSpace Y] (Tr : X → Y) (x y : X) :
    (responseSetoid Tr) x y ↔ responsePseudometric Tr x y = 0 := by
  change Tr x = Tr y ↔ dist (Tr x) (Tr y) = 0
  exact dist_eq_zero.symm

/-- The deterministic finite-horizon response quotient `Q = X / {d = 0}`. -/
abbrev responseQuotient (Tr : X → Y) : Type _ := Quotient (responseSetoid Tr)

/-- The class of a point. -/
def responseClass (Tr : X → Y) (x : X) : responseQuotient Tr :=
  Quotient.mk (responseSetoid Tr) x

theorem responseClass_surjective (Tr : X → Y) : Function.Surjective (responseClass Tr) :=
  Quotient.mk_surjective

theorem responseClass_eq_iff (Tr : X → Y) (x y : X) :
    responseClass Tr x = responseClass Tr y ↔ Tr x = Tr y := by
  unfold responseClass
  exact Quotient.eq

/-- The map induced by `Tr` on the quotient. -/
def responseLift (Tr : X → Y) : responseQuotient Tr → Y :=
  Quotient.lift Tr (fun _ _ h => Setoid.ker_def.mp h)

@[simp] theorem responseLift_class (Tr : X → Y) (x : X) :
    responseLift Tr (responseClass Tr x) = Tr x := rfl

theorem responseLift_injective (Tr : X → Y) : Function.Injective (responseLift Tr) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
      exact Quotient.sound (Setoid.ker_def.mpr hab)

theorem responseLift_range (Tr : X → Y) : Set.range (responseLift Tr) = Set.range Tr := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    induction a using Quotient.inductionOn with
    | h x => exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨responseClass Tr x, rfl⟩

/-- The quotient metric: the response pseudometric descended to classes. -/
noncomputable instance responseQuotientMetric [MetricSpace Y] (Tr : X → Y) :
    MetricSpace (responseQuotient Tr) :=
  MetricSpace.induced (responseLift Tr) (responseLift_injective Tr) inferInstance

theorem responseQuotient_dist [MetricSpace Y] (Tr : X → Y) (x y : X) :
    dist (responseClass Tr x) (responseClass Tr y) = responsePseudometric Tr x y := rfl

/-- **(TR.2)**: the induced map is an isometry of `Q` onto `Σ(X)`. -/
theorem responseLift_isometry [MetricSpace Y] (Tr : X → Y) : Isometry (responseLift Tr) :=
  Isometry.of_dist_eq fun _ _ => rfl

/-- `Q ≅ Σ(X)`: the quotient is isometric to the range of the lift, which is
the trace image `Σ(X)` by `responseLift_range`. -/
noncomputable def responseQuotientEquivRange [MetricSpace Y] (Tr : X → Y) :
    responseQuotient Tr ≃ᵢ Set.range (responseLift Tr) :=
  (responseLift_isometry Tr).isometryEquivOnRange

/-- The trace image is compact when `X` is compact and `Tr` continuous. -/
theorem responseRange_isCompact [TopologicalSpace Y] [TopologicalSpace X] [CompactSpace X]
    (Tr : X → Y)
    (hTr : Continuous Tr) :
    IsCompact (Set.range Tr) :=
  isCompact_range hTr

/-- **Universal property**: if every response factors through `q : X → Z`
(two points with the same `q`-value have the same trace), then there is a
unique map from the image of `q` to `Q` compatible with the response maps,
and it is surjective. -/
theorem response_quotient_coarsest {Z : Type*} (Tr : X → Y) (q : X → Z)
    (hq : ∀ x y, q x = q y → Tr x = Tr y) :
    ∃! d : Set.range q → responseQuotient Tr,
      ∀ x, d ⟨q x, x, rfl⟩ = responseClass Tr x := by
  classical
  refine ⟨fun z => responseClass Tr (Classical.choose z.2), ?_, ?_⟩
  · intro x
    apply Quotient.sound
    change Tr _ = Tr _
    exact hq _ _ (Classical.choose_spec (⟨x, rfl⟩ : q x ∈ Set.range q))
  · intro d hd
    funext z
    obtain ⟨w, hw⟩ := z.2
    have hz : z = ⟨q w, w, rfl⟩ := Subtype.ext hw.symm
    subst hz
    rw [hd w]
    apply Quotient.sound
    change Tr _ = Tr _
    exact (hq _ _ (Classical.choose_spec (⟨w, rfl⟩ : q w ∈ Set.range q))).symm

theorem response_quotient_coarsest_surjective {Z : Type*} (Tr : X → Y) (q : X → Z)
    (d : Set.range q → responseQuotient Tr)
    (hd : ∀ x, d ⟨q x, x, rfl⟩ = responseClass Tr x) :
    Function.Surjective d := by
  intro a
  induction a using Quotient.inductionOn with
  | h x => exact ⟨⟨q x, x, rfl⟩, hd x⟩

end Abstract

/-! ### The concrete packet -/

section Concrete

variable (h : X → K) (Φ : ℝ → X → X)

/-- Restriction of a trace on `[0, T₂]` to the shorter horizon `[0, T₁]`. -/
def restrictTrace {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) (f : C(Icc (0 : ℝ) T₂, K)) :
    C(Icc (0 : ℝ) T₁, K) :=
  f.comp ⟨Set.inclusion (Set.Icc_subset_Icc le_rfl hT), continuous_inclusion _⟩

theorem restrictTrace_responseTrace {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hcont₂ : ∀ x, Continuous fun t : Icc (0 : ℝ) T₂ => h (Φ t x))
    (hcont₁ : ∀ x, Continuous fun t : Icc (0 : ℝ) T₁ => h (Φ t x)) (x : X) :
    restrictTrace hT (responseTrace h Φ T₂ hcont₂ x) = responseTrace h Φ T₁ hcont₁ x := by
  ext t
  rfl

/-- **Canonical restriction surjection** `Q_{T₂}^h → Q_{T₁}^h` for `T₁ ≤ T₂`. -/
noncomputable def responseRestriction {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hcont₂ : ∀ x, Continuous fun t : Icc (0 : ℝ) T₂ => h (Φ t x))
    (hcont₁ : ∀ x, Continuous fun t : Icc (0 : ℝ) T₁ => h (Φ t x)) :
    responseQuotient (responseTrace h Φ T₂ hcont₂) →
      responseQuotient (responseTrace h Φ T₁ hcont₁) :=
  Quotient.map' id (fun x y hxy => by
    have hxy' : responseTrace h Φ T₂ hcont₂ x = responseTrace h Φ T₂ hcont₂ y :=
      Setoid.ker_def.mp hxy
    refine Setoid.ker_def.mpr ?_
    change responseTrace h Φ T₁ hcont₁ x = responseTrace h Φ T₁ hcont₁ y
    rw [← restrictTrace_responseTrace h Φ hT hcont₂ hcont₁,
      ← restrictTrace_responseTrace h Φ hT hcont₂ hcont₁, hxy'])

theorem responseRestriction_class {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hcont₂ : ∀ x, Continuous fun t : Icc (0 : ℝ) T₂ => h (Φ t x))
    (hcont₁ : ∀ x, Continuous fun t : Icc (0 : ℝ) T₁ => h (Φ t x)) (x : X) :
    responseRestriction h Φ hT hcont₂ hcont₁ (responseClass _ x) = responseClass _ x := rfl

theorem responseRestriction_surjective {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hcont₂ : ∀ x, Continuous fun t : Icc (0 : ℝ) T₂ => h (Φ t x))
    (hcont₁ : ∀ x, Continuous fun t : Icc (0 : ℝ) T₁ => h (Φ t x)) :
    Function.Surjective (responseRestriction h Φ hT hcont₂ hcont₁) := by
  intro a
  induction a using Quotient.inductionOn with
  | h x => exact ⟨responseClass _ x, rfl⟩

/-- The all-future trace: the whole family of finite-horizon traces. -/
noncomputable def allFutureTrace
    (hcont : ∀ T : ℝ, ∀ x, Continuous fun t : Icc (0 : ℝ) T => h (Φ t x)) (x : X) :
    (T : ℝ) → C(Icc (0 : ℝ) T, K) :=
  fun T => responseTrace h Φ T (hcont T) x

/-- Two points are identified in the all-future quotient exactly when they are
identified in every finite-horizon quotient (inverse-limit description). -/
theorem allFuture_iff
    (hcont : ∀ T : ℝ, ∀ x, Continuous fun t : Icc (0 : ℝ) T => h (Φ t x)) (x y : X) :
    allFutureTrace h Φ hcont x = allFutureTrace h Φ hcont y ↔
      ∀ T : ℝ, responseClass (responseTrace h Φ T (hcont T)) x
        = responseClass (responseTrace h Φ T (hcont T)) y := by
  unfold allFutureTrace
  simp only [responseClass_eq_iff]
  exact funext_iff

/-- The all-future quotient maps onto every finite-horizon quotient. -/
theorem allFuture_descends
    (hcont : ∀ T : ℝ, ∀ x, Continuous fun t : Icc (0 : ℝ) T => h (Φ t x)) (T : ℝ) :
    ∃ d : Quotient (Setoid.ker (allFutureTrace h Φ hcont)) →
        responseQuotient (responseTrace h Φ T (hcont T)),
      Function.Surjective d ∧
        ∀ x, d (Quotient.mk _ x) = responseClass (responseTrace h Φ T (hcont T)) x := by
  refine ⟨Quotient.map' id (fun x y hxy => ?_), ?_, fun x => rfl⟩
  · exact Setoid.ker_def.mpr ((responseClass_eq_iff _ _ _).mp
      ((allFuture_iff h Φ hcont x y).mp (Setoid.ker_def.mp hxy) T))
  · intro a
    induction a using Quotient.inductionOn with
    | h x => exact ⟨Quotient.mk _ x, rfl⟩

end Concrete

/-- **Strictness witness**: a packet (`X = K = ℝ`, unit-speed translation,
`h = |·| ∧ 1`-type reading via `max`) in which two initial data have identical
responses on `[0, 1]` but different responses at horizon `2`, so the
all-future quotient is strictly finer than `Q_1^h`. -/
theorem allFuture_strictly_finer :
    ∃ (h : ℝ → ℝ) (Φ : ℝ → ℝ → ℝ)
      (hcont : ∀ T : ℝ, ∀ x, Continuous fun t : Icc (0 : ℝ) T => h (Φ t x)),
      ∃ x y : ℝ,
        responseClass (responseTrace h Φ 1 (hcont 1)) x
            = responseClass (responseTrace h Φ 1 (hcont 1)) y ∧
          allFutureTrace h Φ hcont x ≠ allFutureTrace h Φ hcont y := by
  -- `h(u) = max u 0`, `Φ_t x = x + t`; initial data `-1` and `-2` both read
  -- `0` on `[0, 1]` but differ at time `2`.
  refine ⟨fun u => max u 0, fun t x => x + t, fun T x => ?_, -1, -2, ?_, ?_⟩
  · exact (continuous_const.add continuous_subtype_val).max continuous_const
  · rw [responseClass_eq_iff]
    ext t
    simp only [responseTrace_apply]
    have h1 : (t : ℝ) ≤ 1 := t.2.2
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  · intro hxy
    have := congrFun hxy 2
    have h2 := congrArg (fun f : C(Icc (0 : ℝ) 2, ℝ) => f ⟨2, by norm_num, le_rfl⟩) this
    simp only [allFutureTrace, responseTrace_apply] at h2
    norm_num at h2

end FiniteHorizonResponseQuotient
end NCG
