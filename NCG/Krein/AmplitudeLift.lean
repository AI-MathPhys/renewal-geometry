/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Amplitude lifts: the `ℤ/4 → ℤ/2` reduction

The manuscript's amplitude-lift theory (`def:amplitude-lift`,
`lem:z4-lift-surjects`, `thm:minimal-z4-amplitude-lift`) replaces the signed
`ℤ/2`-cover by a finite `ℤ/4` phase lift whenever holonomy acts on
amplitudes: a nontrivial sign needs a unitary square root, and the minimal
finite phase group carrying one is `ℤ/4`, whose mod-2 reduction recovers the
principal double cover.

This file certifies the coordinatewise core of
Lemma `lem:z4-lift-surjects` by a finite kernel-checked enumeration
(`decide`): the reduction `ℤ/4 → ℤ/2` is surjective, so on a wedge of `r`
circles every signed class `H¹(G, ℤ/4) ≅ (ℤ/4)^r → (ℤ/2)^r ≅ H¹(G, ℤ/2)`
admits (exactly `2^r`) amplitude lifts.  The square-root order computation
`u² = −1 ⟹ ord(u) = 4` of `thm:minimal-z4-amplitude-lift` is also
enumerated on `ℤ/4`'s unit circle avatar.
-/

namespace NCG

/-- **Coordinatewise core of Lemma `lem:z4-lift-surjects`**, certified by
kernel enumeration: the mod-2 reduction `ℤ/4 → ℤ/2` is surjective, so every
signed cohomology class on a wedge of circles admits an amplitude lift. -/
theorem zmod4_reduction_surjective :
    ∀ b : ZMod 2, ∃ a : ZMod 4, ((a.val : ZMod 2) = b) := by
  decide

/-- Each fibre of the reduction has exactly two elements: a signed class on
a wedge of `r` circles has `2^r` amplitude lifts
(Lemma `lem:z4-lift-surjects`), certified by enumeration. -/
theorem zmod4_reduction_fibre_card :
    ∀ b : ZMod 2, (Finset.univ.filter
      fun a : ZMod 4 => (a.val : ZMod 2) = b).card = 2 := by
  decide

/-- **Definition `def:amplitude-lift`**, phase realisation: the unitary
phase `i^k` attached to a lifted exponent `k ∈ ℤ/4`. -/
noncomputable def amplitudePhase (k : ZMod 4) : ℂ := Complex.I ^ k.val

/-- The **real signed shadow** of an amplitude lift
(Definition `def:amplitude-lift`): `(i^k)² = (−1)^k` — squaring the
lifted phase recovers the `ℤ/2` sign. -/
theorem amplitudePhase_sq (k : ZMod 4) :
    amplitudePhase k ^ 2 = (-1 : ℂ) ^ k.val := by
  unfold amplitudePhase
  rw [← pow_mul, mul_comm, pow_mul, Complex.I_sq]

/-- **Corollary `cor:z4-conservative-real-layer`** (conservativity over
the real/Krein layer): two amplitude lifts with the same mod-2 reduction
have the same real signed shadow — the `ℤ/4` datum is extra amplitude
information above the real quotient, and every construction depending
only on the `ℤ/2` sign (double cover, fundamental symmetry, exchange
signs, commutator polar form) is unchanged by the choice of lift. -/
theorem amplitudePhase_sq_eq_of_reduction_eq {k₁ k₂ : ZMod 4}
    (h : ((k₁.val : ZMod 2)) = ((k₂.val : ZMod 2))) :
    amplitudePhase k₁ ^ 2 = amplitudePhase k₂ ^ 2 := by
  rw [amplitudePhase_sq, amplitudePhase_sq]
  have hmod : k₁.val % 2 = k₂.val % 2 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  rw [← Nat.div_add_mod k₁.val 2, ← Nat.div_add_mod k₂.val 2,
    pow_add, pow_add, pow_mul, pow_mul, neg_one_sq, hmod]
  simp

/-- The mod-2 reduction on `r` coordinates: under the bouquet
identifications `H¹(G, ℤ/4) ≅ (ℤ/4)^r` and `H¹(G, ℤ/2) ≅ (ℤ/2)^r`
(cf. `NCG.Multigraph.H1BouquetEquiv`), this is the amplitude-lift
reduction `ρ` of Lemma `lem:z4-lift-surjects`. -/
def zmod4PiReduction (r : ℕ) (g : Fin r → ZMod 4) : Fin r → ZMod 2 :=
  fun i => ((g i).val : ZMod 2)

/-- **Lemma `lem:z4-lift-surjects`, surjectivity**: on a graph with
`b₁ = r`, every signed class `[c] ∈ H¹(G, ℤ/2) ≅ (ℤ/2)^r` admits an
amplitude lift `[c̃] ∈ H¹(G, ℤ/4) ≅ (ℤ/4)^r` with `ρ([c̃]) = [c]`. -/
theorem zmod4PiReduction_surjective (r : ℕ) :
    Function.Surjective (zmod4PiReduction r) := by
  intro b
  choose a ha using fun i => zmod4_reduction_surjective (b i)
  exact ⟨a, funext ha⟩

/-- **Lemma `lem:z4-lift-surjects`, fibre count**: every signed class on a
graph with `b₁ = r` has exactly `2^r` amplitude lifts — the fibres of the
reduction `ρ : (ℤ/4)^r → (ℤ/2)^r` all have cardinality `2^r`. -/
theorem card_zmod4PiReduction_fibre (r : ℕ) (b : Fin r → ZMod 2) :
    Fintype.card {g : Fin r → ZMod 4 // zmod4PiReduction r g = b}
      = 2 ^ r := by
  have e1 : {g : Fin r → ZMod 4 // zmod4PiReduction r g = b} ≃
      {g : Fin r → ZMod 4 // ∀ i, ((g i).val : ZMod 2) = b i} :=
    Equiv.subtypeEquivRight fun g =>
      ⟨fun h i => congrFun h i, fun h => funext fun i => h i⟩
  have e2 : {g : Fin r → ZMod 4 // ∀ i, ((g i).val : ZMod 2) = b i} ≃
      ∀ i : Fin r, {a : ZMod 4 // ((a.val : ZMod 2)) = b i} :=
    Equiv.subtypePiEquivPi
      (p := fun (i : Fin r) (a : ZMod 4) => ((a.val : ZMod 2)) = b i)
  rw [Fintype.card_congr (e1.trans e2), Fintype.card_pi]
  calc ∏ i : Fin r, Fintype.card {a : ZMod 4 // ((a.val : ZMod 2)) = b i}
      = ∏ _i : Fin r, 2 :=
        Finset.prod_congr rfl fun i _ => by
          rw [Fintype.card_subtype]
          exact zmod4_reduction_fibre_card (b i)
    _ = 2 ^ r := by simp

/-- **The minimal square root of `−1` has order four**
(`thm:minimal-z4-amplitude-lift`, enumerated core): in `ℤ/4` (written
additively, the exponent group of the phase `i^k`), the elements doubling to
the sign generator `2` — i.e. the fourth-root phases with `(i^k)² = −1` —
are exactly the two generators `1` and `3`, each of additive order four. -/
theorem zmod4_sqrt_neg_one :
    ∀ a : ZMod 4, (a + a = 2 ↔ (a = 1 ∨ a = 3)) := by
  decide

/-- **Theorem `thm:minimal-z4-amplitude-lift`** (minimal finite square-root
completion): any unitary square root of a nontrivial sign has order exactly
four, so every finite phase group carrying such a square root contains a
cyclic subgroup `ℤ/4`.  The minimal finite amplitude completion of a
nontrivial signed sector is therefore `ℤ/4`, whose mod-2 reduction is the
principal double cover. -/
theorem orderOf_eq_four_of_sq_eq_neg_one {M : Type*} [Monoid M]
    [HasDistribNeg M] (u : M) (hu : u ^ 2 = -1) (hne : (-1 : M) ≠ 1) :
    orderOf u = 4 := by
  have h4 : u ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hu, neg_one_sq]
  have h2 : u ^ 2 ≠ 1 := by
    rw [hu]
    exact hne
  have hfin : IsOfFinOrder u :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, h4⟩
  have hpos : 0 < orderOf u := hfin.orderOf_pos
  have hdvd : orderOf u ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hle : orderOf u ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : orderOf u
  · -- order 1: `u = 1` contradicts `u² = −1 ≠ 1`
    exact absurd (by rw [orderOf_eq_one_iff.mp h]; norm_num : u ^ 2 = 1) h2
  · -- order 2 contradicts `u² ≠ 1`
    exact absurd (by rw [← h]; exact pow_orderOf_eq_one u) h2
  · -- order 3 does not divide 4
    norm_num at hdvd
  · rfl

end NCG
