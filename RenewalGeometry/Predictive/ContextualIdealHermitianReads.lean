/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.ContextualFutureNullIdeal
import RenewalGeometry.Predictive.ContextualEnvelope

/-!
# Contextual nullity under adjoint-closed Reads (`lem:supp-contextual-ideal`)

The emergent-spacetime manuscript (`lem:supp-contextual-ideal`) calls a represented
element *contextually null* when every admitted left and right history context
and every terminal Read has zero matrix coefficient on it, and claims that the
set `𝒥^ctx` of such elements is the largest two-sided `*`-ideal invisible in
every admitted context, so that `𝒜^hist = 𝒜^raw / 𝒥^ctx` is the unique minimum
context-preserving separated history envelope.

The star-free null set is `RenewalGeometry.contextualNull R`
(`ContextualEnvelope.lean`).  Its star-closure is the manuscript's step
"reversing the context shows that `a*` is null"; this needs the Read family to
be closed under reversal of the matrix coefficient, which is exactly the case
for matrix coefficients `⟪ξ, π(x) η⟫` of a `*`-representation (reversal swaps
`ξ` and `η`).  This file:

* `ReadsAdjointClosed`: every Read `R k` has a reversed Read `R k'` with
  `R k' (x*) = conj (R k x)`; `ReadsHermitian` (each Read Hermitian) is the
  special case `k' = k` (`readsAdjointClosed_of_hermitian`).
* `matrixCoefficientRead`: the paper's Reads, matrix coefficients
  `⟪v i, π(x) v j⟫` of a `*`-representation `π` on a complex Hilbert space
  between any family of terminal vectors; `matrixCoefficientRead_adjointClosed`
  derives adjoint closure from this definition (no extra hypothesis).
* `contextualNull_star_mem`, `contextualNull_eq_contextualFutureNull`: under
  adjoint-closed Reads the manuscript's star-free null set is star-closed, and
  equals the complete null set `contextualFutureNull R`.
* `contextualNullTwoSidedIdeal` and `contextualNull_isGreatest`: the null set is
  a two-sided `*`-ideal, it is invisible to every Read, and it contains every
  two-sided ideal on which all Reads vanish — so it is the greatest element of
  the set of invisible two-sided `*`-ideals (in fact of all invisible two-sided
  ideals).
* `ContextualHistoryEnvelope`: the quotient ring `𝒜/𝒥` by the complete null
  ideal, with its induced star, `ℂ`-algebra structure, descended Reads, the
  quotient `*`-algebra map `historyQuotientMap`; it is context preserving and
  contextually separated (`historyEnvelope_separated`).
* `historyEnvelope_minimum`: for every context-preserving surjective
  `*`-algebra map `π : 𝒜 →⋆ₐ[ℂ] 𝓑` (a context-preserving envelope), `ker π ⊆ 𝒥`
  and there is a unique ring map `ψ : 𝓑 → 𝒜/𝒥` with `ψ ∘ π = q`; it is a
  `*`-algebra map; when `𝓑` is contextually separated `ψ` is bijective, i.e.
  `historyEnvelope_unique_separated` gives a `*`-algebra isomorphism
  `𝓑 ≃⋆ₐ[ℂ] 𝒜/𝒥` over `𝒜`.

Rendering disclosed: admitted contexts range over the whole represented algebra
(represented words span it, and the null condition is linear), and Reads are
additive maps to `ℂ`.  Non-vacuity: `M₂(ℂ)` with its entry Reads (matrix
coefficients between basis vectors) satisfies the hypotheses and its null ideal
is proper.
-/

namespace RenewalGeometry

namespace ContextualIdeal

open scoped ComplexConjugate

/-! ### Adjoint-closed Read families -/

/-- A Read family is *adjoint closed* when every Read has a reversed Read:
`R k' (x*) = conj (R k x)` for all `x`. -/
def ReadsAdjointClosed {A : Type*} [Ring A] [StarRing A] {κ : Type*}
    (R : κ → A →+ ℂ) : Prop :=
  ∀ k, ∃ k', ∀ x, R k' (star x) = conj (R k x)

/-- Each Read is Hermitian: `R k (x*) = conj (R k x)`. -/
def ReadsHermitian {A : Type*} [Ring A] [StarRing A] {κ : Type*}
    (R : κ → A →+ ℂ) : Prop :=
  ∀ k x, R k (star x) = conj (R k x)

theorem readsAdjointClosed_of_hermitian {A : Type*} [Ring A] [StarRing A] {κ : Type*}
    {R : κ → A →+ ℂ} (hR : ReadsHermitian R) : ReadsAdjointClosed R :=
  fun k => ⟨k, hR k⟩

/-- Matrix-coefficient Reads of a `*`-representation `π` of `A` on a complex
Hilbert space `E`, between a family `v` of terminal vectors:
`(i, j) ↦ (x ↦ ⟪v i, π x (v j)⟫)`. -/
noncomputable def matrixCoefficientRead {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : A →⋆ₐ[ℂ] (E →L[ℂ] E)) {σ : Type*} (v : σ → E) : σ × σ → A →+ ℂ :=
  fun ij =>
    { toFun := fun x => inner ℂ (v ij.1) (π x (v ij.2))
      map_zero' := by simp
      map_add' := fun x y => by simp }

theorem matrixCoefficientRead_apply {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : A →⋆ₐ[ℂ] (E →L[ℂ] E)) {σ : Type*} (v : σ → E) (i j : σ) (x : A) :
    matrixCoefficientRead π v (i, j) x = inner ℂ (v i) (π x (v j)) := rfl

/-- Matrix-coefficient Reads are adjoint closed: reversing the coefficient
`(i, j) ↦ (j, i)` conjugates it on the adjoint. -/
theorem matrixCoefficientRead_adjointClosed {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (π : A →⋆ₐ[ℂ] (E →L[ℂ] E)) {σ : Type*} (v : σ → E) :
    ReadsAdjointClosed (matrixCoefficientRead π v) := by
  rintro ⟨i, j⟩
  refine ⟨(j, i), fun x => ?_⟩
  rw [matrixCoefficientRead_apply, matrixCoefficientRead_apply, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_conj_symm]

/-! ### Star closure of the star-free null set -/

section NullSet

variable {A : Type*} [Ring A] [StarRing A] {κ : Type*} (R : κ → A →+ ℂ)

/-- `lem:supp-contextual-ideal`, star step: for adjoint-closed Reads the
star-free contextual null set is closed under the involution (reverse the
context: `R_{k'}(u q* v) = conj R_k(v* q u*)`). -/
theorem contextualNull_star_mem (hR : ReadsAdjointClosed R) {q : A}
    (hq : q ∈ contextualNull R) : star q ∈ contextualNull R := by
  intro k u v
  obtain ⟨k', hk'⟩ := hR k
  have hrev : star (u * star q * v) = star v * q * star u := by
    simp [star_mul, mul_assoc]
  have h := hk' (u * star q * v)
  rw [hrev, hq k' (star v) (star u)] at h
  exact (map_eq_zero_iff (starRingEnd ℂ) (RingHom.injective _)).1 h.symm

/-- Under adjoint-closed Reads the manuscript's star-free null set is the
complete (star-tested) contextual null set. -/
theorem contextualNull_eq_contextualFutureNull (hR : ReadsAdjointClosed R) :
    contextualNull R = contextualFutureNull R := by
  ext q
  constructor
  · intro hq
    exact ⟨hq, contextualNull_star_mem R hR hq⟩
  · intro hq
    exact hq.1

/-- Contextually null elements are invisible to every Read (take the trivial
contexts `u = v = 1`). -/
theorem contextualNull_read_eq_zero {q : A} (hq : q ∈ contextualNull R) (k : κ) :
    R k q = 0 := by
  simpa using hq k 1 1

/-- The star-free contextual null set as a two-sided ideal. -/
def contextualNullTwoSidedIdeal : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (contextualNull R)
    (contextual_null_absorption R).1
    (fun {p q} hp hq => (contextual_null_absorption R).2.1 p q hp hq)
    (fun {q} hq => (contextual_null_absorption R).2.2.1 q hq)
    (fun {a q} hq => (contextual_null_absorption R).2.2.2.1 a q hq)
    (fun {q a} hq => (contextual_null_absorption R).2.2.2.2 a q hq)

theorem mem_contextualNullTwoSidedIdeal {q : A} :
    q ∈ contextualNullTwoSidedIdeal R ↔ q ∈ contextualNull R :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ q

/-- A two-sided ideal is *invisible* when every Read vanishes on it. -/
def IsInvisibleIdeal (I : TwoSidedIdeal A) : Prop :=
  ∀ q ∈ I, ∀ k, R k q = 0

/-- A two-sided ideal is a `*`-ideal when it is closed under the involution. -/
def IsStarIdeal (I : TwoSidedIdeal A) : Prop :=
  ∀ q ∈ I, star q ∈ I

/-- Every invisible two-sided ideal is contained in the contextual null set:
for `q ∈ I` the whole context `u q v` stays in `I`, where every Read vanishes. -/
theorem le_contextualNullTwoSidedIdeal_of_invisible {I : TwoSidedIdeal A}
    (hI : IsInvisibleIdeal R I) : I ≤ contextualNullTwoSidedIdeal R := by
  intro q hq
  rw [mem_contextualNullTwoSidedIdeal]
  intro k u v
  exact hI _ (I.mul_mem_right _ _ (I.mul_mem_left _ _ hq)) k

/-- `lem:supp-contextual-ideal`, first sentence.  For adjoint-closed Reads the
contextual null set is the **largest two-sided `*`-ideal invisible in every
admitted context**: it is a two-sided ideal, star closed, invisible, and it
contains every invisible two-sided ideal (star closed or not). -/
theorem contextualNull_isGreatest (hR : ReadsAdjointClosed R) :
    IsGreatest {I : TwoSidedIdeal A | IsStarIdeal I ∧ IsInvisibleIdeal R I}
      (contextualNullTwoSidedIdeal R) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro q hq
    rw [mem_contextualNullTwoSidedIdeal] at hq ⊢
    exact contextualNull_star_mem R hR hq
  · intro q hq k
    rw [mem_contextualNullTwoSidedIdeal] at hq
    exact contextualNull_read_eq_zero R hq k
  · rintro I ⟨-, hI⟩
    exact le_contextualNullTwoSidedIdeal_of_invisible R hI

/-- The ideals invisible in every admitted context are exactly the ideals
inside the null set. -/
theorem le_contextualNullTwoSidedIdeal_iff (I : TwoSidedIdeal A) :
    I ≤ contextualNullTwoSidedIdeal R ↔
      ∀ q ∈ I, ∀ k (u v : A), R k (u * q * v) = 0 := by
  constructor
  · intro h q hq k u v
    have := h hq
    rw [mem_contextualNullTwoSidedIdeal] at this
    exact this k u v
  · intro h q hq
    rw [mem_contextualNullTwoSidedIdeal]
    exact h q hq

end NullSet

/-! ### The complete null ideal and the history envelope -/

section Envelope

variable {A : Type*} [Ring A] [StarRing A] {κ : Type*} (R : κ → A →+ ℂ)

/-- The complete (star-tested) contextual null set as a two-sided ideal; under
adjoint-closed Reads it is the same set as `contextualNullTwoSidedIdeal R`
(`completeNullIdeal_eq`). -/
def completeNullIdeal : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (contextualFutureNull R)
    (contextualFutureNullIdeal R).zero_mem
    (fun hp hq => (contextualFutureNullIdeal R).add_mem hp hq)
    (fun hq => (contextualFutureNullIdeal R).neg_mem hq)
    (fun {a _} hq => (contextualFutureNullIdeal R).mul_mem_left a hq)
    (fun {_ a} hq => (contextualFutureNullIdeal R).mul_mem_right a hq)

theorem mem_completeNullIdeal {q : A} :
    q ∈ completeNullIdeal R ↔ q ∈ contextualFutureNull R :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ q

theorem completeNullIdeal_star_mem {q : A} (hq : q ∈ completeNullIdeal R) :
    star q ∈ completeNullIdeal R := by
  rw [mem_completeNullIdeal] at hq ⊢
  exact contextualFutureNullIdeal_star_mem R hq

/-- For adjoint-closed Reads the complete null ideal and the manuscript's
star-free null ideal coincide. -/
theorem completeNullIdeal_eq (hR : ReadsAdjointClosed R) :
    completeNullIdeal R = contextualNullTwoSidedIdeal R := by
  apply TwoSidedIdeal.ext
  intro q
  rw [mem_completeNullIdeal, mem_contextualNullTwoSidedIdeal,
    contextualNull_eq_contextualFutureNull R hR]

/-- The history envelope `𝒜^hist = 𝒜^raw / 𝒥^ctx`: the quotient ring by the
complete contextual null ideal. -/
abbrev ContextualHistoryEnvelope : Type _ := (completeNullIdeal R).ringCon.Quotient

/-- The quotient map `𝒜 → 𝒜/𝒥` as a ring homomorphism. -/
abbrev historyQuotientRingHom : A →+* ContextualHistoryEnvelope R :=
  (completeNullIdeal R).ringCon.mk'

theorem historyQuotientRingHom_surjective :
    Function.Surjective (historyQuotientRingHom R) :=
  RingCon.mk'_surjective _

theorem historyQuotientRingHom_eq_zero_iff (x : A) :
    historyQuotientRingHom R x = 0 ↔ x ∈ completeNullIdeal R := by
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

theorem historyQuotientRingHom_eq_iff (x y : A) :
    historyQuotientRingHom R x = historyQuotientRingHom R y ↔
      x - y ∈ completeNullIdeal R := by
  rw [← sub_eq_zero, ← map_sub, historyQuotientRingHom_eq_zero_iff]

/-- The induced involution on the history envelope. -/
instance : Star (ContextualHistoryEnvelope R) where
  star := Quotient.lift (fun a : A => historyQuotientRingHom R (star a)) (by
    intro a b hab
    change (completeNullIdeal R).ringCon a b at hab
    rw [TwoSidedIdeal.rel_iff] at hab
    rw [historyQuotientRingHom_eq_iff, ← star_sub]
    exact completeNullIdeal_star_mem R hab)

theorem star_historyQuotientRingHom (a : A) :
    star (historyQuotientRingHom R a) = historyQuotientRingHom R (star a) := rfl

instance : StarRing (ContextualHistoryEnvelope R) where
  star_involutive := by
    intro x
    obtain ⟨a, rfl⟩ := historyQuotientRingHom_surjective R x
    rw [star_historyQuotientRingHom, star_historyQuotientRingHom, star_star]
  star_mul := by
    intro x y
    obtain ⟨a, rfl⟩ := historyQuotientRingHom_surjective R x
    obtain ⟨b, rfl⟩ := historyQuotientRingHom_surjective R y
    rw [← map_mul, star_historyQuotientRingHom, star_historyQuotientRingHom,
      star_historyQuotientRingHom, star_mul, map_mul]
  star_add := by
    intro x y
    obtain ⟨a, rfl⟩ := historyQuotientRingHom_surjective R x
    obtain ⟨b, rfl⟩ := historyQuotientRingHom_surjective R y
    rw [← map_add, star_historyQuotientRingHom, star_historyQuotientRingHom,
      star_historyQuotientRingHom, star_add, map_add]

/-- The Reads descend to the history envelope. -/
noncomputable def historyRead (k : κ) : ContextualHistoryEnvelope R →+ ℂ where
  toFun := Quotient.lift (fun a : A => R k a) (by
    intro a b hab
    change (completeNullIdeal R).ringCon a b at hab
    rw [TwoSidedIdeal.rel_iff, mem_completeNullIdeal] at hab
    have := hab.1 k 1 1
    simp only [one_mul, mul_one, map_sub] at this
    exact sub_eq_zero.mp this)
  map_zero' := by
    change R k 0 = 0
    exact map_zero _
  map_add' := by
    intro x y
    obtain ⟨a, rfl⟩ := historyQuotientRingHom_surjective R x
    obtain ⟨b, rfl⟩ := historyQuotientRingHom_surjective R y
    rw [← map_add]
    exact map_add (R k) a b

/-- Context preservation: the descended Reads composed with the quotient map are
the original Reads. -/
theorem historyRead_comp (k : κ) (a : A) :
    historyRead R k (historyQuotientRingHom R a) = R k a := rfl

/-- The history envelope is contextually separated: an element invisible in
every context (in both test families) is zero. -/
theorem historyEnvelope_separated (b : ContextualHistoryEnvelope R)
    (hb : b ∈ contextualFutureNull (historyRead R)) : b = 0 := by
  obtain ⟨a, rfl⟩ := historyQuotientRingHom_surjective R b
  rw [historyQuotientRingHom_eq_zero_iff, mem_completeNullIdeal]
  refine ⟨fun k u v => ?_, fun k u v => ?_⟩
  · have := hb.1 k (historyQuotientRingHom R u) (historyQuotientRingHom R v)
    rwa [← map_mul, ← map_mul, historyRead_comp] at this
  · have := hb.2 k (historyQuotientRingHom R u) (historyQuotientRingHom R v)
    rwa [star_historyQuotientRingHom, ← map_mul, ← map_mul, historyRead_comp] at this

/-- Under adjoint-closed Reads separation already holds for the star-free
family of tests. -/
theorem historyEnvelope_separated_starFree (hR : ReadsAdjointClosed R)
    (b : ContextualHistoryEnvelope R) (hb : b ∈ contextualNull (historyRead R)) :
    b = 0 := by
  obtain ⟨a, rfl⟩ := historyQuotientRingHom_surjective R b
  rw [historyQuotientRingHom_eq_zero_iff, completeNullIdeal_eq R hR,
    mem_contextualNullTwoSidedIdeal]
  intro k u v
  have := hb k (historyQuotientRingHom R u) (historyQuotientRingHom R v)
  rwa [← map_mul, ← map_mul, historyRead_comp] at this

end Envelope

/-! ### Universal property: the unique minimum separated envelope -/

section Universal

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] {κ : Type*} (R : κ → A →+ ℂ)

/-- The quotient map `𝒜^raw → 𝒜^hist` as a `*`-algebra homomorphism. -/
noncomputable def historyQuotientMap : A →⋆ₐ[ℂ] ContextualHistoryEnvelope R :=
  { RingCon.mkₐ ℂ (completeNullIdeal R).ringCon with
    map_star' := fun _ => rfl }

theorem historyQuotientMap_apply (a : A) :
    historyQuotientMap R a = historyQuotientRingHom R a := rfl

theorem historyQuotientMap_surjective : Function.Surjective (historyQuotientMap R) :=
  historyQuotientRingHom_surjective R

/-- A context-preserving envelope of `(𝒜, R)`: a surjective `*`-algebra map
`π : 𝒜 →⋆ₐ[ℂ] 𝓑` through which every Read factors. -/
structure ContextPreservingEnvelope (B : Type*) [Ring B] [StarRing B] [Algebra ℂ B] where
  /-- The envelope map. -/
  map : A →⋆ₐ[ℂ] B
  /-- The envelope is generated by the image. -/
  surjective : Function.Surjective map
  /-- The Reads on the envelope. -/
  read : κ → B →+ ℂ
  /-- Context preservation. -/
  read_comp : ∀ k x, R k x = read k (map x)

/-- An envelope is *separated* when every element invisible in every context
of the envelope (both test families) vanishes. -/
def ContextPreservingEnvelope.Separated {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    {R : κ → A →+ ℂ} (E : ContextPreservingEnvelope R B) : Prop :=
  ∀ b ∈ contextualFutureNull E.read, b = 0

/-- The history envelope itself is a context-preserving envelope. -/
noncomputable def historyEnvelope :
    ContextPreservingEnvelope R (ContextualHistoryEnvelope R) where
  map := historyQuotientMap R
  surjective := historyQuotientMap_surjective R
  read := historyRead R
  read_comp _ _ := rfl

theorem historyEnvelope_isSeparated : (historyEnvelope R).Separated :=
  historyEnvelope_separated R

variable {R}
variable {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]

/-- Kernel inclusion: the kernel of every context-preserving envelope is
contained in the contextual null ideal. -/
theorem ContextPreservingEnvelope.ker_le (E : ContextPreservingEnvelope R B) (x : A)
    (hx : E.map x = 0) : x ∈ completeNullIdeal R := by
  rw [mem_completeNullIdeal]
  refine ⟨fun k u v => ?_, fun k u v => ?_⟩
  · rw [E.read_comp, map_mul E.map, map_mul E.map, hx, mul_zero, zero_mul, map_zero]
  · rw [E.read_comp, map_mul E.map, map_mul E.map, map_star E.map, hx, star_zero,
      mul_zero, zero_mul, map_zero]

/-- On a separated envelope the kernel is exactly the contextual null ideal. -/
theorem ContextPreservingEnvelope.ker_eq (E : ContextPreservingEnvelope R B)
    (hE : E.Separated) (x : A) : E.map x = 0 ↔ x ∈ completeNullIdeal R := by
  refine ⟨E.ker_le x, fun hx => hE _ ?_⟩
  rw [mem_completeNullIdeal] at hx
  refine ⟨fun k u v => ?_, fun k u v => ?_⟩
  · obtain ⟨a, rfl⟩ := E.surjective u
    obtain ⟨c, rfl⟩ := E.surjective v
    rw [← map_mul, ← map_mul, ← E.read_comp]
    exact hx.1 k a c
  · obtain ⟨a, rfl⟩ := E.surjective u
    obtain ⟨c, rfl⟩ := E.surjective v
    rw [← map_star, ← map_mul, ← map_mul, ← E.read_comp]
    exact hx.2 k a c

/-- The comparison map from any context-preserving envelope onto the history
envelope (as a ring map). -/
noncomputable def ContextPreservingEnvelope.toHistoryRingHom
    (E : ContextPreservingEnvelope R B) : B →+* ContextualHistoryEnvelope R :=
  (E.map : A →+* B).liftOfSurjective E.surjective
    ⟨historyQuotientRingHom R, fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      rw [historyQuotientRingHom_eq_zero_iff]
      exact E.ker_le x hx⟩

theorem ContextPreservingEnvelope.toHistoryRingHom_comp
    (E : ContextPreservingEnvelope R B) (x : A) :
    E.toHistoryRingHom (E.map x) = historyQuotientMap R x :=
  (E.map : A →+* B).liftOfRightInverse_comp_apply _ _ _ x

/-- The comparison map is a `*`-algebra homomorphism. -/
noncomputable def ContextPreservingEnvelope.toHistory
    (E : ContextPreservingEnvelope R B) : B →⋆ₐ[ℂ] ContextualHistoryEnvelope R :=
  { E.toHistoryRingHom with
    commutes' := fun c => by
      change E.toHistoryRingHom (algebraMap ℂ B c) = _
      rw [← AlgHomClass.commutes E.map c, E.toHistoryRingHom_comp]
      exact (historyQuotientMap R).commutes c
    map_star' := fun b => by
      obtain ⟨a, rfl⟩ := E.surjective b
      change E.toHistoryRingHom (star (E.map a)) = star (E.toHistoryRingHom (E.map a))
      rw [← map_star, E.toHistoryRingHom_comp, E.toHistoryRingHom_comp, map_star] }

theorem ContextPreservingEnvelope.toHistory_comp
    (E : ContextPreservingEnvelope R B) (x : A) :
    E.toHistory (E.map x) = historyQuotientMap R x :=
  E.toHistoryRingHom_comp x

/-- Uniqueness of the comparison map: any ring map `ψ` with `ψ ∘ π = q` is
`E.toHistory`. -/
theorem ContextPreservingEnvelope.toHistory_unique
    (E : ContextPreservingEnvelope R B) (ψ : B →+* ContextualHistoryEnvelope R)
    (hψ : ∀ x, ψ (E.map x) = historyQuotientMap R x) (b : B) :
    ψ b = E.toHistory b := by
  obtain ⟨a, rfl⟩ := E.surjective b
  rw [hψ, E.toHistory_comp]

/-- On a separated envelope the comparison map is bijective. -/
theorem ContextPreservingEnvelope.toHistory_bijective
    (E : ContextPreservingEnvelope R B) (hE : E.Separated) :
    Function.Bijective E.toHistory := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨a, rfl⟩ := E.surjective b
    rw [E.toHistory_comp, historyQuotientMap_apply,
      historyQuotientRingHom_eq_zero_iff] at hb
    exact (E.ker_eq hE a).2 hb
  · intro y
    obtain ⟨a, rfl⟩ := historyQuotientMap_surjective R y
    exact ⟨E.map a, E.toHistory_comp a⟩

/-- `lem:supp-contextual-ideal`, envelope clause: `𝒜^hist = 𝒜^raw/𝒥^ctx` is the
**unique minimum context-preserving separated history envelope**.

For every context-preserving envelope `E : 𝒜 ↠ 𝓑`:
* (kernel) `ker π ⊆ 𝒥`;
* (minimum) there is a `*`-algebra map `ψ : 𝓑 → 𝒜^hist` with `ψ ∘ π = q`, and
  it is the unique ring map with this property;
* (uniqueness among separated envelopes) if `𝓑` is separated then `ψ` is
  bijective, hence a `*`-algebra isomorphism over `𝒜`, and the Reads agree:
  `R'_k = R^hist_k ∘ ψ`.

Moreover `𝒜^hist` is itself context preserving and separated
(`historyEnvelope`, `historyEnvelope_isSeparated`), and for adjoint-closed
Reads its ideal is the manuscript's star-free null set
(`completeNullIdeal_eq`). -/
theorem historyEnvelope_minimum (E : ContextPreservingEnvelope R B) :
    (∀ x, E.map x = 0 → x ∈ completeNullIdeal R)
    ∧ (∃ ψ : B →⋆ₐ[ℂ] ContextualHistoryEnvelope R,
        (∀ x, ψ (E.map x) = historyQuotientMap R x)
        ∧ ∀ ψ' : B →+* ContextualHistoryEnvelope R,
            (∀ x, ψ' (E.map x) = historyQuotientMap R x) → ∀ b, ψ' b = ψ b)
    ∧ (E.Separated → Function.Bijective E.toHistory
        ∧ ∀ k b, E.read k b = historyRead R k (E.toHistory b)) := by
  refine ⟨E.ker_le, ⟨E.toHistory, E.toHistory_comp, fun ψ' hψ' => E.toHistory_unique ψ' hψ'⟩,
    fun hE => ⟨E.toHistory_bijective hE, fun k b => ?_⟩⟩
  obtain ⟨a, rfl⟩ := E.surjective b
  rw [E.toHistory_comp, ← E.read_comp]
  rfl

/-- Any separated context-preserving envelope is `*`-isomorphic to the history
envelope, compatibly with the maps from `𝒜`. -/
noncomputable def ContextPreservingEnvelope.historyEquiv
    (E : ContextPreservingEnvelope R B) (hE : E.Separated) :
    B ≃⋆ₐ[ℂ] ContextualHistoryEnvelope R :=
  StarAlgEquiv.ofBijective E.toHistory (E.toHistory_bijective hE)

theorem ContextPreservingEnvelope.historyEquiv_comp
    (E : ContextPreservingEnvelope R B) (hE : E.Separated) (x : A) :
    E.historyEquiv hE (E.map x) = historyQuotientMap R x :=
  E.toHistory_comp x

/-- `lem:supp-contextual-ideal` (bundled, for adjoint-closed Reads, in
particular matrix-coefficient Reads): the manuscript's null set `𝒥^ctx` is the
largest two-sided `*`-ideal invisible in every admitted context, it equals the
ideal by which the history envelope is formed, and every separated
context-preserving envelope is `*`-isomorphic to `𝒜/𝒥^ctx` over `𝒜`. -/
theorem contextual_ideal_hermitianReads (hR : ReadsAdjointClosed R) :
    IsGreatest {I : TwoSidedIdeal A | IsStarIdeal I ∧ IsInvisibleIdeal R I}
      (contextualNullTwoSidedIdeal R)
    ∧ completeNullIdeal R = contextualNullTwoSidedIdeal R
    ∧ (historyEnvelope R).Separated
    ∧ ∀ (E : ContextPreservingEnvelope R B), E.Separated →
        ∃ Φ : B ≃⋆ₐ[ℂ] ContextualHistoryEnvelope R,
          ∀ x, Φ (E.map x) = historyQuotientMap R x := by
  exact ⟨contextualNull_isGreatest R hR, completeNullIdeal_eq R hR,
    historyEnvelope_isSeparated R,
    fun E hE => ⟨E.historyEquiv hE, E.historyEquiv_comp hE⟩⟩

end Universal

/-! ### Non-vacuity: `M₂(ℂ)` with its entry Reads -/

/-- Entry Reads on `M₂(ℂ)`: the matrix coefficients `⟪e_i, x e_j⟫ = x i j`. -/
def matrixEntryRead : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ →+ ℂ :=
  fun ij =>
    { toFun := fun x => x ij.1 ij.2
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem matrixEntryRead_adjointClosed : ReadsAdjointClosed matrixEntryRead := by
  rintro ⟨i, j⟩
  refine ⟨(j, i), fun x => ?_⟩
  rfl

/-- The entry Reads are not Hermitian one by one (so adjoint closure, not
Hermiticity, is the operative hypothesis), and the null ideal is proper:
the identity is visible. -/
example : ¬ ReadsHermitian matrixEntryRead ∧
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ∉ contextualNull matrixEntryRead ∧
    IsGreatest {I : TwoSidedIdeal (Matrix (Fin 2) (Fin 2) ℂ) |
        IsStarIdeal I ∧ IsInvisibleIdeal matrixEntryRead I}
      (contextualNullTwoSidedIdeal matrixEntryRead) := by
  refine ⟨fun h => ?_, fun h => ?_, contextualNull_isGreatest _ matrixEntryRead_adjointClosed⟩
  · have h01 := h (0, 1) (Matrix.of ![![0, 1], ![0, 0]])
    change (star (Matrix.of ![![(0 : ℂ), 1], ![0, 0]])) 0 1 =
      starRingEnd ℂ ((Matrix.of ![![(0 : ℂ), 1], ![0, 0]]) 0 1) at h01
    simp [Matrix.star_apply] at h01
  · have h00 := h (0, 0) 1 1
    change (((1 : Matrix (Fin 2) (Fin 2) ℂ) * 1 * 1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0) = 0
      at h00
    simp at h00

/-- Non-vacuity of the matrix-coefficient Reads: the identity representation of
`B(ℂ²)` with all vectors as terminal Reads satisfies the bundled lemma. -/
example :
    ReadsAdjointClosed (matrixCoefficientRead
      (StarAlgHom.id ℂ (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
      (id : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2))) :=
  matrixCoefficientRead_adjointClosed _ _

example :
    completeNullIdeal (matrixCoefficientRead
      (StarAlgHom.id ℂ (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
      (id : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2))) =
    contextualNullTwoSidedIdeal (matrixCoefficientRead
      (StarAlgHom.id ℂ (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
      (id : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2))) :=
  (contextual_ideal_hermitianReads (B := ContextualHistoryEnvelope (matrixCoefficientRead
      (StarAlgHom.id ℂ (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
      (id : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2))))
    (matrixCoefficientRead_adjointClosed _ _)).2.1

end ContextualIdeal

end RenewalGeometry
