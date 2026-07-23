/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.Memory

/-!
# The predictive quotient

Two histories are **predictively equivalent** when they induce the same
accumulated channel (manuscript, Definition `def:predictive-quotient`):

`w ∼_CP w'  ↔  Φ_w = Φ_{w'}`.

Because the accumulated channel `acc : FreeMonoid E →* M` is a monoid
homomorphism, this equivalence is the *kernel congruence* `Con.ker acc`.  In
particular it is automatically a **two-sided** shift congruence — this
subsumes the manuscript's Lemma `lem:shift-congruence` (left shift
congruence), and endows the predictive quotient `𝒲_CP` with a monoid
structure, identifying it with the channel monoid `ℳ` (the image of `acc`).

The **quotient length** `Λ_min [w] = 1 + min { |v| : Φ_v = Φ_w }` of
Definition `def:predictive-quotient` is defined via `sInf` on `ℕ` and is
attained (`NCG.RenewalMemory.exists_quotLength_rep`).

## Main definitions

* `NCG.RenewalMemory.predCon` — the predictive congruence `∼_CP`;
* `NCG.RenewalMemory.PredictiveQuotient` — the quotient `𝒲_CP`, a monoid;
* `NCG.RenewalMemory.mkQ` — the projection onto predictive classes;
* `NCG.RenewalMemory.shift` — the descended shift `Ŝ_σ [w] = [σ w]`;
* `NCG.RenewalMemory.quotLength` — the quotient length `Λ_min`.

## Main results

* `NCG.RenewalMemory.shift_congruence` — Lemma `lem:shift-congruence`;
* `NCG.RenewalMemory.quotientEquivRange` — the predictive quotient is
  isomorphic to the accumulated-channel monoid `ℳ ⊆ M`;
* `NCG.RenewalMemory.one_le_quotLength`,
  `NCG.RenewalMemory.quotLength_mkQ_le`,
  `NCG.RenewalMemory.exists_quotLength_rep` — basic properties of `Λ_min`.
-/

namespace NCG.RenewalMemory

variable {E : Type*} {M : Type*} [Monoid M] (R : RenewalMemory E M)

/-- **Predictive equivalence** `∼_CP` (Definition `def:predictive-quotient`):
the kernel congruence of the accumulated-channel homomorphism.  Being a
congruence, it is compatible with concatenation of histories on both sides. -/
def predCon : Con (History E) := Con.ker R.acc

theorem predCon_iff (w w' : History E) :
    R.predCon w w' ↔ R.acc w = R.acc w' :=
  Iff.rfl

/-- **Lemma `lem:shift-congruence`** (predictive collapse is a left shift
congruence): if `w ∼_CP w'` then `σw ∼_CP σw'`.  In fact `∼_CP` is a
two-sided congruence; this is the special case of left concatenation by a
single reset. -/
theorem shift_congruence {w w' : History E} (h : R.predCon w w') (σ : E) :
    R.predCon (FreeMonoid.of σ * w) (FreeMonoid.of σ * w') :=
  R.predCon.mul (R.predCon.refl (FreeMonoid.of σ)) h

/-- The **predictive quotient** `𝒲_CP = E^* / ∼_CP` (Definition
`def:predictive-quotient`).  It carries a monoid structure since `∼_CP` is a
congruence. -/
def PredictiveQuotient := R.predCon.Quotient

instance : Monoid R.PredictiveQuotient :=
  inferInstanceAs (Monoid R.predCon.Quotient)

/-- The canonical projection of a history onto its predictive class. -/
def mkQ : History E →* R.PredictiveQuotient := R.predCon.mk'

theorem mkQ_surjective : Function.Surjective R.mkQ :=
  Con.mk'_surjective

theorem mkQ_eq_mkQ_iff {w w' : History E} :
    R.mkQ w = R.mkQ w' ↔ R.acc w = R.acc w' :=
  Con.eq _

/-- The **descended shift** `Ŝ_σ` on the predictive quotient:
`Ŝ_σ [w] = [σ w]` (Lemma `lem:shift-congruence`).  In monoid language it is
left multiplication by the class of the one-letter history `σ`. -/
def shift (σ : E) : R.PredictiveQuotient → R.PredictiveQuotient :=
  fun x => R.mkQ (FreeMonoid.of σ) * x

@[simp]
theorem shift_mkQ (σ : E) (w : History E) :
    R.shift σ (R.mkQ w) = R.mkQ (FreeMonoid.of σ * w) := by
  simp [shift, map_mul]

/-- **Proposition `prop:fibres-monoid`** (cancellative fibres): when the
memory monoid is left-cancellative, every descended shift `Ŝ_σ` is
injective on the predictive quotient — distinct predictive classes stay
distinct after a reset, so the shift fibres are singletons and the
renewal dynamics acts freely on classes. -/
theorem shift_injective [IsLeftCancelMul M] (σ : E) :
    Function.Injective (R.shift σ) := by
  intro x y h
  obtain ⟨w, rfl⟩ := R.mkQ_surjective x
  obtain ⟨w', rfl⟩ := R.mkQ_surjective y
  rw [shift_mkQ, shift_mkQ, mkQ_eq_mkQ_iff, map_mul, map_mul] at h
  rw [mkQ_eq_mkQ_iff]
  exact mul_left_cancel h

/-- The predictive quotient is canonically isomorphic to the **channel
monoid** `ℳ = {Φ_w : w ∈ E^*}`, the image of the accumulated-channel map.
"Geometry is what prediction remembers." -/
noncomputable def quotientEquivRange :
    R.PredictiveQuotient ≃* MonoidHom.mrange R.acc :=
  Con.quotientKerEquivRange R.acc

/-- The **quotient length** `Λ_min` (Definition `def:predictive-quotient`):
`Λ_min x = 1 + min { |v| : [v] = x }`, the length of a shortest history
representing the predictive class, plus one. -/
noncomputable def quotLength (x : R.PredictiveQuotient) : ℕ :=
  1 + sInf {n : ℕ | ∃ w : History E, R.mkQ w = x ∧ w.length = n}

theorem lengthSet_nonempty (x : R.PredictiveQuotient) :
    {n : ℕ | ∃ w : History E, R.mkQ w = x ∧ w.length = n}.Nonempty := by
  obtain ⟨w, rfl⟩ := R.mkQ_surjective x
  exact ⟨w.length, w, rfl, rfl⟩

/-- The quotient length is at least `1`. -/
theorem one_le_quotLength (x : R.PredictiveQuotient) : 1 ≤ R.quotLength x :=
  Nat.le_add_right _ _

/-- The quotient length of a class is at most `1` plus the length of any
representative history. -/
theorem quotLength_mkQ_le (w : History E) :
    R.quotLength (R.mkQ w) ≤ 1 + w.length := by
  have hmem : w.length ∈
      {n : ℕ | ∃ v : History E, R.mkQ v = R.mkQ w ∧ v.length = n} :=
    ⟨w, rfl, rfl⟩
  exact Nat.add_le_add_left (Nat.sInf_le hmem) 1

/-- The infimum in the definition of `Λ_min` is attained: every predictive
class has a shortest representative history. -/
theorem exists_quotLength_rep (x : R.PredictiveQuotient) :
    ∃ w : History E, R.mkQ w = x ∧ R.quotLength x = 1 + w.length := by
  obtain ⟨w, hw, hlen⟩ := Nat.sInf_mem (R.lengthSet_nonempty x)
  exact ⟨w, hw, by rw [quotLength, hlen]⟩

/-- The empty history has quotient length `1` (the manuscript's convention
`Λ_min([∅]) = 1`). -/
@[simp]
theorem quotLength_one : R.quotLength (R.mkQ 1) = 1 := by
  have h := R.quotLength_mkQ_le 1
  have h' := R.one_le_quotLength (R.mkQ 1)
  simp only [FreeMonoid.length_one, Nat.add_zero] at h
  omega

end NCG.RenewalMemory
