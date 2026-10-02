/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Pfaffian of an alternating matrix

Mathlib has no Pfaffian.  We build it for an arbitrary function `A : ι → ι → R` on a linearly
ordered index type, as the Pfaffian `pfaff A s` of the principal submatrix on a finite set
`s : Finset ι`, defined by expansion along the largest index of `s`:

`Pf_s(A) = ∑_{i ∈ s, i ≠ L} (-1)^{pos_s i} A i L Pf_{s ∖ {i, L}}(A)`,  `L = max s`,
`Pf_∅(A) = 1`,

where `pos_s i` is the (zero-based) position of `i` in `s`.  Working with sub-*sets* of one
index type (instead of re-indexed submatrices) makes every minor a smaller finset and keeps
all sign bookkeeping in terms of positions.  For `A` alternating (`A j i = -A i j`,
`A i i = 0`) we prove:

* `pfaff_pair`: `Pf_{a<b}(A) = A a b` (the convention `Pf [[0,k],[-k,0]] = k`);
  `pfaff_of_odd`: odd sets have Pfaffian `0`;
* `pfaff_expand`: **expansion along an arbitrary index** `k ∈ s`,
  `Pf_s = ∑_{j ≠ k} (-1)^{pos k + pos j + 1 + [k > j]} A k j Pf_{s ∖ {k,j}}`;
* `pfaff_move`: moving one index past others costs the sign `(-1)^{#between}`;
* `pfaff_eq_zero_of_row_eq`: an alternating matrix with two equal rows has Pfaffian `0`;
* `sum_mul_adjE`: the **Pfaffian adjugate identity** `A P(A) = Pf(A) I` on `s`;
* `pfaff_ne_zero_of_injOnSet`: over a field of characteristic zero, if the principal submatrix
  on `s` is injective (nonsingular), its Pfaffian is nonzero (induction through the adjugate
  identity and the complementary-minor argument for the inverse);
* `pfaff_map`, `pfaff_congr`: invariance under order embeddings and dependence only on the
  entries inside `s`;
* `pfaff_insert_insert`: **the two-border expansion**
  `Pf_{s ∪ {x<y}} = ∑_{a,b ∈ s} A a x P_s(a,b) A b y` when `x, y` lie above `s` and
  `A x y = 0`.

The matrix layer (`Matrix (Fin n) (Fin n) R`) is `Pf`, `pfAdj` (the paper's polynomial Pfaffian
adjugate `P(K)_{ij} = (-1)^{i+j} Pf(K_{îĵ})` for `i < j`, skew completion),
`mul_pfAdj : K * pfAdj K = Pf K • 1`, `pfAdj_mul`, `Pf_two`, `Pf_zero_size`, and
`Pf_ne_zero_iff : Pf K ≠ 0 ↔ IsUnit K.det` (alternating `K`, characteristic zero).
The identity `Pf² = det` is not proved here (only the nonvanishing criterion it implies is).
-/

namespace RenewalGeometry
namespace SkewPfaffian

open Finset

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

/-- `pos s i` is the number of elements of `s` strictly below `i` (zero-based position of
`i` in `s`). -/
def pos (s : Finset ι) (i : ι) : ℕ := (s.filter (· < i)).card

/-- The Pfaffian of the principal submatrix of `A` on the finite set `s`, defined by expansion
along the largest index `L` of `s`: `Pf_s = ∑_{i ∈ s ∖ L} (-1)^{pos_s i} A i L Pf_{s∖{i,L}}`,
`Pf_∅ = 1`. -/
def pfaff (A : ι → ι → R) (s : Finset ι) : R :=
  if h : s.Nonempty then
    ∑ i ∈ (s.erase (s.max' h)).attach,
      (-1) ^ pos s i.1 * A i.1 (s.max' h) * pfaff A ((s.erase (s.max' h)).erase i.1)
  else 1
termination_by s.card
decreasing_by
  have h1 := Finset.card_erase_lt_of_mem (Finset.max'_mem s h)
  have h2 := Finset.card_erase_lt_of_mem i.2
  omega

@[simp] theorem pfaff_empty (A : ι → ι → R) : pfaff A ∅ = 1 := by
  rw [pfaff]; simp

theorem pos_insert_of_lt {s : Finset ι} {y i : ι} (h : i < y) :
    pos (insert y s) i = pos s i := by
  unfold pos
  rw [Finset.filter_insert, if_neg (not_lt.mpr h.le)]

theorem pos_insert {s : Finset ι} {y : ι} (hy : y ∉ s) (i : ι) :
    pos (insert y s) i = pos s i + if y < i then 1 else 0 := by
  unfold pos
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => hy (Finset.mem_filter.1 h').1)]
  · simp

theorem pos_erase {s : Finset ι} {y : ι} (hy : y ∈ s) (i : ι) :
    pos s i = pos (s.erase y) i + if y < i then 1 else 0 := by
  conv_lhs => rw [← Finset.insert_erase hy]
  exact pos_insert (Finset.notMem_erase y s) i

theorem pos_of_forall_lt {s : Finset ι} {y : ι} (h : ∀ z ∈ s, z < y) : pos s y = s.card := by
  unfold pos
  rw [Finset.filter_true_of_mem h]

/-- The defining expansion along the maximum, without `attach`. -/
theorem pfaff_eq_sum (A : ι → ι → R) {s : Finset ι} (h : s.Nonempty) :
    pfaff A s = ∑ i ∈ s.erase (s.max' h),
      (-1) ^ pos s i * A i (s.max' h) * pfaff A ((s.erase (s.max' h)).erase i) := by
  rw [pfaff, dif_pos h]
  exact Finset.sum_attach (s.erase (s.max' h))
    (fun i => (-1) ^ pos s i * A i (s.max' h) * pfaff A ((s.erase (s.max' h)).erase i))

/-- Unfolding at an index above the whole set. -/
theorem pfaff_insert_max (A : ι → ι → R) {s : Finset ι} {y : ι} (h : ∀ z ∈ s, z < y) :
    pfaff A (insert y s) =
      ∑ i ∈ s, (-1) ^ pos s i * A i y * pfaff A (s.erase i) := by
  have hy : y ∉ s := fun hy => lt_irrefl _ (h y hy)
  have hmax : (insert y s).max' (Finset.insert_nonempty y s) = y := by
    apply le_antisymm
    · apply Finset.max'_le
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact le_rfl
      · exact (h z hz).le
    · exact Finset.le_max' _ _ (Finset.mem_insert_self y s)
  rw [pfaff_eq_sum A (Finset.insert_nonempty y s)]
  simp only [hmax, Finset.erase_insert hy]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [pos_insert_of_lt (h i hi)]

/-- Every nonempty set is its maximum inserted into the rest. -/
theorem eq_insert_max (s : Finset ι) (h : s.Nonempty) :
    s = insert (s.max' h) (s.erase (s.max' h)) :=
  (Finset.insert_erase (Finset.max'_mem s h)).symm

theorem lt_max'_of_mem_erase {s : Finset ι} (h : s.Nonempty) {z : ι}
    (hz : z ∈ s.erase (s.max' h)) : z < s.max' h :=
  lt_of_le_of_ne (Finset.le_max' s z (Finset.mem_of_mem_erase hz)) (Finset.ne_of_mem_erase hz)

theorem pfaff_singleton (A : ι → ι → R) (a : ι) : pfaff A {a} = 0 := by
  have : ({a} : Finset ι) = insert a ∅ := rfl
  rw [this, pfaff_insert_max A (s := ∅) (by simp)]
  simp

/-- `Pf_{a<b}(A) = A a b`: the convention `Pf [[0,k],[-k,0]] = k`. -/
theorem pfaff_pair (A : ι → ι → R) {a b : ι} (hab : a < b) : pfaff A {a, b} = A a b := by
  have : ({a, b} : Finset ι) = insert b {a} := Finset.pair_comm a b
  rw [this, pfaff_insert_max A (s := {a}) (by simpa using hab)]
  simp [pos, Finset.filter_singleton]

/-- Sets of odd cardinality have Pfaffian zero. -/
theorem pfaff_of_odd (A : ι → ι → R) : ∀ (n : ℕ) (s : Finset ι), s.card = n → Odd n →
    pfaff A s = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hodd
    have hne : s.Nonempty := by
      rw [← Finset.card_pos, hs]; exact hodd.pos
    rw [eq_insert_max s hne, pfaff_insert_max A (fun z hz => lt_max'_of_mem_erase hne hz)]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : ((s.erase (s.max' hne)).erase i).card = n - 2 := by
      rw [Finset.card_erase_of_mem hi, Finset.card_erase_of_mem (Finset.max'_mem s hne), hs]
      omega
    have hn : 2 ≤ n := by
      have := Finset.card_erase_lt_of_mem hi
      have := Finset.card_erase_of_mem (Finset.max'_mem s hne)
      rcases hodd with ⟨k, hk⟩
      omega
    rw [ih (n - 2) (by omega) _ hcard (by
      rcases hodd with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩), mul_zero]

/-! ### Expansion along an arbitrary index -/

/-- The sign of the `(k, j)` term in the expansion of `Pf_s` along `k`:
`(-1)^{pos k + pos j + 1 + [k > j]}`. -/
def sgnE (s : Finset ι) (k j : ι) : R := (if j < k then 1 else -1) * (-1) ^ (pos s k + pos s j)

theorem sgnE_ne_zero [Nontrivial R] (s : Finset ι) (k j : ι) : (sgnE s k j : R) ≠ 0 := by
  have hu : IsUnit (sgnE s k j : R) := by
    unfold sgnE
    refine IsUnit.mul ?_ ((isUnit_one.neg).pow _)
    split_ifs
    · exact isUnit_one
    · exact isUnit_one.neg
  exact hu.ne_zero

private theorem neg_one_pow_odd' {n : ℕ} (h : ¬ Even n) : ((-1 : R) ^ n) = -1 :=
  (Nat.not_even_iff_odd.1 h).neg_one_pow

/-- **Expansion of the Pfaffian along an arbitrary index** `k ∈ s`. -/
theorem pfaff_expand (A : ι → ι → R) (hA : ∀ i j, A j i = -A i j) :
    ∀ (n : ℕ) (s : Finset ι), s.card = n → ∀ k ∈ s,
      pfaff A s = ∑ j ∈ s.erase k, sgnE s k j * A k j * pfaff A ((s.erase k).erase j) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs k hk
    by_cases hodd : Odd n
    · rw [pfaff_of_odd A n s hs hodd]
      refine (Finset.sum_eq_zero fun j hj => ?_).symm
      have hj' := Finset.mem_of_mem_erase hj
      have h1 := Finset.card_erase_of_mem hk
      have h2 := Finset.card_erase_of_mem hj
      have hn : 2 ≤ n := by
        have := Finset.card_erase_lt_of_mem hj
        rcases hodd with ⟨m, hm⟩; omega
      rw [pfaff_of_odd A (n - 2) _ (by rw [h2, h1, hs]; omega)
        (by rcases hodd with ⟨m, hm⟩; exact ⟨m - 1, by omega⟩), mul_zero]
    have heven : Even n := Nat.not_odd_iff_even.1 hodd
    have hne : s.Nonempty := ⟨k, hk⟩
    obtain ⟨L, t, hLt, rfl⟩ : ∃ L t, (∀ z ∈ t, z < L) ∧ s = insert L t :=
      ⟨s.max' hne, s.erase (s.max' hne), fun z hz => lt_max'_of_mem_erase hne hz,
        eq_insert_max s hne⟩
    have hL : L ∉ t := fun h => lt_irrefl _ (hLt L h)
    have htcard : t.card + 1 = n := by rw [← hs, Finset.card_insert_of_notMem hL]
    have htodd : ¬ Even t.card := by
      intro h; exact hodd (by rw [← htcard]; exact h.add_one)
    rw [pfaff_insert_max A hLt]
    have hposL : pos (insert L t) L = t.card := by
      rw [pos_insert hL, if_neg (lt_irrefl L), add_zero, pos_of_forall_lt hLt]
    rcases Finset.mem_insert.1 hk with rfl | hkt
    · -- expansion along the maximum itself
      rw [Finset.erase_insert hL]
      refine Finset.sum_congr rfl fun j hj => ?_
      unfold sgnE
      rw [if_pos (hLt j hj), hposL, pos_insert_of_lt (hLt j hj), pow_add,
        neg_one_pow_odd' htodd, hA j k]
      ring
    · have hkL : L ≠ k := fun h => hL (h ▸ hkt)
      have hLu : L ∉ t.erase k := fun h => hL (Finset.mem_of_mem_erase h)
      rw [Finset.erase_insert_of_ne hkL, Finset.sum_insert hLu, ← Finset.add_sum_erase t _ hkt]
      congr 1
      · rw [Finset.erase_insert hLu]
        unfold sgnE
        rw [if_neg (not_lt.2 (hLt k hkt).le), hposL, pos_insert_of_lt (hLt k hkt), pow_add,
          neg_one_pow_odd' htodd]
        ring
      · have hu : ∀ i ∈ t.erase k, pfaff A (t.erase i) = ∑ j ∈ (t.erase k).erase i,
            sgnE (t.erase i) k j * A k j * pfaff A (((t.erase k).erase i).erase j) := by
          intro i hi
          have hit := Finset.mem_of_mem_erase hi
          have hik := Finset.ne_of_mem_erase hi
          have hc : (t.erase i).card = n - 2 := by rw [Finset.card_erase_of_mem hit]; omega
          rw [ih (n - 2) (by omega) (t.erase i) hc k (Finset.mem_erase.2 ⟨hik.symm, hkt⟩),
            Finset.erase_right_comm]
        have hv : ∀ j ∈ t.erase k, pfaff A ((insert L (t.erase k)).erase j) =
            ∑ i ∈ (t.erase k).erase j, (-1) ^ pos ((t.erase k).erase j) i * A i L *
              pfaff A (((t.erase k).erase i).erase j) := by
          intro j hj
          have hLj : L ≠ j := fun h => hL (h ▸ Finset.mem_of_mem_erase hj)
          rw [Finset.erase_insert_of_ne hLj, pfaff_insert_max A
            (fun z hz => hLt z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)))]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.erase_right_comm (s := t.erase k) (a := j) (b := i)]
        refine (Finset.sum_congr rfl fun i hi => by rw [hu i hi]).trans ?_
        refine Eq.trans ?_ (Finset.sum_congr rfl fun j hj => by rw [hv j hj]).symm
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm' (t' := t.erase k) (s' := fun j => (t.erase k).erase j)
          (fun i j => by
            simp only [Finset.mem_erase]
            exact ⟨fun ⟨⟨a, b⟩, c, d, e⟩ => ⟨⟨fun h => c h.symm, a, b⟩, d, e⟩,
              fun ⟨⟨a, b, c⟩, d, e⟩ => ⟨⟨b, c⟩, fun h => a h.symm, d, e⟩⟩)]
        refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => ?_
        have hju := hj
        have hjt := Finset.mem_of_mem_erase hj
        have hit := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
        have e1 := pos_erase hit k
        have e2 := pos_erase hit j
        have e3 := pos_erase hkt i
        have e4 := pos_erase hju i
        unfold sgnE
        rw [pos_insert_of_lt (hLt k hkt), pos_insert_of_lt (hLt j hjt), e1, e2, e3, e4]
        generalize pos (t.erase i) k = a
        generalize pos (t.erase i) j = b
        generalize pos ((t.erase k).erase j) i = c
        generalize (if j < k then (1 : R) else -1) = σ
        rcases lt_or_gt_of_ne hik with h1 | h1 <;> rcases lt_or_gt_of_ne hij with h2 | h2 <;>
          simp [h1, h2, not_lt.2 h1.le, not_lt.2 h2.le, pow_add, pow_succ] <;> ring

/-! ### Dependence on the entries inside `s` -/

/-- The Pfaffian on `s` depends only on the entries of `A` inside `s × s`. -/
theorem pfaff_congr (A B : ι → ι → R) : ∀ (n : ℕ) (s : Finset ι), s.card = n →
    (∀ x ∈ s, ∀ y ∈ s, A x y = B x y) → pfaff A s = pfaff B s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hAB
    by_cases hne : s.Nonempty
    · rw [pfaff_eq_sum A hne, pfaff_eq_sum B hne]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_of_mem_erase hi
      have hc1 := Finset.card_erase_lt_of_mem (Finset.max'_mem s hne)
      have hc2 := Finset.card_erase_lt_of_mem hi
      rw [hAB i hi' _ (Finset.max'_mem s hne),
        ih _ (by omega) _ rfl (fun x hx y hy => hAB x
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)) y
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)))]
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp

/-! ### Moving an index, equal rows -/

/-- Number of elements of `u` strictly between `k` and `l`. -/
def btw (u : Finset ι) (k l : ι) : ℕ :=
  (u.filter (fun y => (k < y ∧ y < l) ∨ (l < y ∧ y < k))).card

theorem card_filter_erase_add {u : Finset ι} {y : ι} (hy : y ∈ u) (p : ι → Prop)
    [DecidablePred p] :
    (u.filter p).card = ((u.erase y).filter p).card + if p y then 1 else 0 := by
  conv_lhs => rw [← Finset.insert_erase hy]
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => Finset.notMem_erase y u
      (Finset.mem_filter.1 h').1)]
  · simp

theorem btw_erase {u : Finset ι} {y : ι} (hy : y ∈ u) (k l : ι) :
    btw u k l = btw (u.erase y) k l + if (k < y ∧ y < l) ∨ (l < y ∧ y < k) then 1 else 0 :=
  card_filter_erase_add hy _

theorem btw_comm (u : Finset ι) (k l : ι) : btw u k l = btw u l k := by
  unfold btw
  congr 1
  ext y
  simp only [Finset.mem_filter]
  tauto

theorem pos_add_btw {u : Finset ι} {k l : ι} (hkl : k < l) (hk : k ∉ u) :
    pos u l = pos u k + btw u k l := by
  unfold pos btw
  have h1 : u.filter (· < l) = u.filter (· < k) ∪
      u.filter (fun y => (k < y ∧ y < l) ∨ (l < y ∧ y < k)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hy, hyl⟩
      rcases lt_trichotomy y k with h | h | h
      · exact Or.inl ⟨hy, h⟩
      · exact (hk (h ▸ hy)).elim
      · exact Or.inr ⟨hy, Or.inl ⟨h, hyl⟩⟩
    · rintro (⟨hy, h⟩ | ⟨hy, ⟨_, h⟩ | ⟨h, h'⟩⟩)
      · exact ⟨hy, h.trans hkl⟩
      · exact ⟨hy, h⟩
      · exact (lt_irrefl _ ((hkl.trans h).trans h')).elim
  rw [h1, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro y hy hy'
  simp only [Finset.mem_filter] at hy hy'
  rcases hy'.2 with ⟨h, _⟩ | ⟨h, _⟩
  · exact lt_asymm hy.2 h
  · exact lt_asymm (hy.2.trans hkl) h

/-- **Moving an index.** If the rows of `k` and `l` agree on `u` (`k, l ∉ u`), then
`Pf_{u ∪ {l}} = (-1)^{#(u ∩ (k,l))} Pf_{u ∪ {k}}`. -/
theorem pfaff_move (A : ι → ι → R) (hA : ∀ i j, A j i = -A i j) :
    ∀ (n : ℕ) (u : Finset ι), u.card = n → ∀ k l : ι, k ∉ u → l ∉ u → k ≠ l →
      (∀ x ∈ u, A k x = A l x) →
      pfaff A (insert l u) = (-1) ^ btw u k l * pfaff A (insert k u) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hu k l hk hl hkl hrow
    by_cases hne : u.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
      simp [pfaff_singleton]
    obtain ⟨x, hx⟩ := hne
    have hxl : l ≠ x := fun h => hl (h ▸ hx)
    have hxk : k ≠ x := fun h => hk (h ▸ hx)
    have hlu : l ∉ u.erase x := fun h => hl (Finset.mem_of_mem_erase h)
    have hku : k ∉ u.erase x := fun h => hk (Finset.mem_of_mem_erase h)
    rw [pfaff_expand A hA _ _ rfl x (Finset.mem_insert_of_mem hx),
      pfaff_expand A hA _ _ rfl x (Finset.mem_insert_of_mem hx),
      Finset.erase_insert_of_ne hxl, Finset.erase_insert_of_ne hxk,
      Finset.sum_insert hlu, Finset.sum_insert hku, Finset.erase_insert hlu,
      Finset.erase_insert hku, mul_add, Finset.mul_sum]
    have hAxl : A x l = A x k := by rw [hA l x, hA k x, hrow x hx]
    have epl := pos_insert hl
    have epk := pos_insert hk
    congr 1
    · -- the moved index itself
      rw [hAxl]
      unfold sgnE
      rw [epl x, epl l, epk x, epk k, if_neg (lt_irrefl l), if_neg (lt_irrefl k), add_zero,
        add_zero]
      have key : ∀ (c : Prop) [Decidable c] (p : ℕ),
          ((if c then (1 : R) else -1) * (-1) ^ (p + if c then 1 else 0)) = -(-1) ^ p := by
        intro c _ p
        split_ifs <;> simp [pow_succ]
      rcases lt_or_gt_of_ne hkl with h | h
      · rw [pos_add_btw h hk]
        have e1 : pos u x + (if l < x then 1 else 0) + (pos u k + btw u k l)
            = (pos u x + pos u k + btw u k l) + (if l < x then 1 else 0) := by ring
        have e2 : pos u x + (if k < x then 1 else 0) + pos u k
            = (pos u x + pos u k) + (if k < x then 1 else 0) := by ring
        rw [e1, e2, key, key, pow_add]
        ring
      · rw [btw_comm, pos_add_btw h hl]
        have e1 : pos u x + (if k < x then 1 else 0) + (pos u l + btw u l k)
            = (pos u x + pos u l + btw u l k) + (if k < x then 1 else 0) := by ring
        have e2 : pos u x + (if l < x then 1 else 0) + pos u l
            = (pos u x + pos u l) + (if l < x then 1 else 0) := by ring
        rw [e1, e2, key, key, pow_add, pow_add]
        have : ((-1 : R) ^ btw u l k) * (-1) ^ btw u l k = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; simp
        linear_combination ((-1 : R) ^ (pos u x + pos u l) * A x k * pfaff A (u.erase x)) * this
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjx : j ≠ x := Finset.ne_of_mem_erase hj
      have hju : j ∈ u := Finset.mem_of_mem_erase hj
      have hlj : l ≠ j := fun h => hl (h ▸ hju)
      have hkj : k ≠ j := fun h => hk (h ▸ hju)
      rw [Finset.erase_insert_of_ne hlj, Finset.erase_insert_of_ne hkj]
      have hc : ((u.erase x).erase j).card < n := by
        have := Finset.card_erase_lt_of_mem hj
        have := Finset.card_erase_lt_of_mem hx
        omega
      rw [ih _ hc _ rfl k l (fun h => hku (Finset.mem_of_mem_erase h))
        (fun h => hlu (Finset.mem_of_mem_erase h)) hkl
        (fun z hz => hrow z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)))]
      have eb1 := btw_erase hx k l
      have eb2 := btw_erase hj k l
      unfold sgnE
      rw [epl x, epl j, epk x, epk j, eb1, eb2]
      generalize pos u x = px
      generalize pos u j = pj
      generalize btw ((u.erase x).erase j) k l = b
      generalize (if j < x then (1 : R) else -1) = σ
      generalize pfaff A (insert k ((u.erase x).erase j)) = P
      rcases lt_or_gt_of_ne hkl with h0 | h0 <;>
      rcases lt_or_gt_of_ne hxk with h1 | h1 <;> rcases lt_or_gt_of_ne hxl with h2 | h2 <;>
      rcases lt_or_gt_of_ne hkj with h3 | h3 <;> rcases lt_or_gt_of_ne hlj with h4 | h4 <;>
      simp [h1, h2, h3, h4, not_lt.2 h1.le, not_lt.2 h2.le,
        not_lt.2 h3.le, not_lt.2 h4.le, pow_add, pow_succ] <;> ring

/-- **Equal rows.** An alternating `A` whose rows `k ≠ l` agree on `s ∋ k, l` has
`Pf_s(A) = 0`. -/
theorem pfaff_eq_zero_of_row_eq (A : ι → ι → R) (hA : ∀ i j, A j i = -A i j)
    (hdiag : ∀ i, A i i = 0) :
    ∀ (n : ℕ) (s : Finset ι), s.card = n → ∀ k l : ι, k ∈ s → l ∈ s → k ≠ l →
      (∀ x ∈ s, A k x = A l x) → pfaff A s = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs k l hk hl hkl hrow
    have hAkl : A k l = 0 := by rw [hrow l hl, hdiag]
    by_cases hm : ∃ m ∈ s, m ≠ k ∧ m ≠ l
    · obtain ⟨m, hm, hmk, hml⟩ := hm
      rw [pfaff_expand A hA n s hs m hm]
      have hkm : k ∈ s.erase m := Finset.mem_erase.2 ⟨hmk.symm, hk⟩
      have hlm : l ∈ s.erase m := Finset.mem_erase.2 ⟨hml.symm, hl⟩
      rw [Finset.sum_eq_add_of_mem k l hkm hlm hkl (fun c hc hckl => by
        have hcs := Finset.mem_of_mem_erase hc
        have hcm := Finset.ne_of_mem_erase hc
        have hcard : ((s.erase m).erase c).card < n := by
          have := Finset.card_erase_lt_of_mem hc
          have := Finset.card_erase_lt_of_mem hm
          omega
        rw [ih _ hcard _ rfl k l
          (Finset.mem_erase.2 ⟨hckl.1.symm, hkm⟩) (Finset.mem_erase.2 ⟨hckl.2.symm, hlm⟩) hkl
          (fun x hx => hrow x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))),
          mul_zero])]
      set u := ((s.erase m).erase k).erase l with hu
      have hlu' : l ∈ (s.erase m).erase k := Finset.mem_erase.2 ⟨hkl.symm, hlm⟩
      have hku' : k ∈ (s.erase m).erase l := Finset.mem_erase.2 ⟨hkl, hkm⟩
      have h1 : (s.erase m).erase k = insert l u := (Finset.insert_erase hlu').symm
      have h2 : (s.erase m).erase l = insert k u := by
        rw [hu, Finset.erase_right_comm (s := s.erase m) (a := k) (b := l)]
        exact (Finset.insert_erase hku').symm
      have hku : k ∉ u := fun h => by
        simp [hu] at h
      have hlu : l ∉ u := fun h => by simp [hu] at h
      rw [h1, h2, pfaff_move A hA _ u rfl k l hku hlu hkl
        (fun x hx => hrow x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
          (Finset.mem_of_mem_erase hx))))]
      have hAm : A m l = A m k := by rw [hA l m, hA k m, hrow m hm]
      rw [hAm]
      -- positions in `s` through `u`
      have hmu : m ∉ u := fun h => by simp [hu] at h
      have hsu : s = insert m (insert k (insert l u)) := by
        rw [Finset.insert_erase hlu', Finset.insert_erase hkm, Finset.insert_erase hm]
      have hku2 : k ∉ insert l u := by simp [hkl, hku]
      have hmu2 : m ∉ insert k (insert l u) := by simp [hmk, hml, hmu]
      have pk : pos s k = pos u k + (if l < k then 1 else 0) + (if m < k then 1 else 0) := by
        rw [hsu, pos_insert hmu2, pos_insert hku2, if_neg (lt_irrefl k), add_zero,
          pos_insert hlu]
      have pl : pos s l = pos u l + (if k < l then 1 else 0) + (if m < l then 1 else 0) := by
        rw [hsu, pos_insert hmu2, pos_insert hku2, pos_insert hlu, if_neg (lt_irrefl l),
          add_zero]
      unfold sgnE
      rw [pk, pl]
      generalize pos s m = pm
      generalize pfaff A (insert k u) = P
      rcases lt_or_gt_of_ne hkl with h0 | h0
      · rw [pos_add_btw h0 hku]
        generalize pos u k = pk'
        generalize btw u k l = b
        rcases lt_or_gt_of_ne hmk with h1 | h1 <;> rcases lt_or_gt_of_ne hml with h2 | h2 <;>
        simp [h0, h1, h2, not_lt.2 h0.le, not_lt.2 h1.le, not_lt.2 h2.le, pow_add,
          pow_succ] <;> ring
      · rw [btw_comm, pos_add_btw h0 hlu]
        generalize pos u l = pl'
        generalize btw u l k = b
        have hb : ((-1 : R) ^ (b * 2)) = 1 := Even.neg_one_pow ⟨b, by ring⟩
        rcases lt_or_gt_of_ne hmk with h1 | h1 <;> rcases lt_or_gt_of_ne hml with h2 | h2 <;>
        simp [h0, h1, h2, not_lt.2 h0.le, not_lt.2 h1.le, not_lt.2 h2.le, pow_add,
          pow_succ] <;> ring_nf <;> rw [hb] <;> ring
    · push_neg at hm
      rw [pfaff_expand A hA n s hs k hk]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjk := Finset.ne_of_mem_erase hj
      have hjl : j = l := by
        by_contra h
        exact h (hm j (Finset.mem_of_mem_erase hj) hjk)
      rw [hjl, hAkl]; ring

/-! ### The Pfaffian adjugate -/

/-- The Pfaffian adjugate on `s`: `adjE A s j l = sgnE s l j · Pf_{s ∖ {l, j}}` for `j ≠ l`,
and `0` on the diagonal.  For `s = univ` on `Fin n` this is the paper's
`P(K)_{jl} = (-1)^{j+l} Pf(K_{ĵl̂})` (`j < l`) with skew completion (`pfAdj_eq_adjE`). -/
def adjE (A : ι → ι → R) (s : Finset ι) (j l : ι) : R :=
  if j = l then 0 else sgnE s l j * pfaff A ((s.erase l).erase j)

/-- **The Pfaffian adjugate identity** `A P(A) = Pf(A) I` on `s`. -/
theorem sum_mul_adjE (A : ι → ι → R) (hA : ∀ i j, A j i = -A i j) (hdiag : ∀ i, A i i = 0)
    (s : Finset ι) {a l : ι} (ha : a ∈ s) (hl : l ∈ s) :
    ∑ j ∈ s, A a j * adjE A s j l = if a = l then pfaff A s else 0 := by
  rw [← Finset.add_sum_erase s _ hl]
  have h0 : adjE A s l l = 0 := by simp [adjE]
  have hsum : ∑ j ∈ s.erase l, A a j * adjE A s j l =
      ∑ j ∈ s.erase l, sgnE s l j * A a j * pfaff A ((s.erase l).erase j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [adjE, if_neg (Finset.ne_of_mem_erase hj)]; ring
  rw [h0, mul_zero, zero_add, hsum]
  by_cases hal : a = l
  · subst hal
    rw [if_pos rfl]
    exact (pfaff_expand A hA _ s rfl a ha).symm
  · rw [if_neg hal]
    -- replace row/column `l` by row/column `a`
    set ρ : ι → ι := fun x => if x = l then a else x with hρ
    set A' : ι → ι → R := fun x y => A (ρ x) (ρ y) with hA'
    have hA's : ∀ i j, A' j i = -A' i j := fun i j => hA _ _
    have hA'd : ∀ i, A' i i = 0 := fun i => hdiag _
    have hρa : ρ a = a := by simp [hρ, hal]
    have hρl : ρ l = a := by simp [hρ]
    have hzero := pfaff_eq_zero_of_row_eq A' hA's hA'd _ s rfl a l ha hl hal
      (fun x _ => by simp only [hA', hρa, hρl])
    rw [pfaff_expand A' hA's _ s rfl l hl] at hzero
    rw [← hzero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjl := Finset.ne_of_mem_erase hj
    have hρj : ρ j = j := by simp [hρ, hjl]
    have hA'lj : A' l j = A a j := by simp only [hA', hρl, hρj]
    rw [hA'lj, pfaff_congr A' A _ _ rfl (fun x hx y hy => by
      have hx' : x ≠ l := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
      have hy' : y ≠ l := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)
      simp [hA', hρ, hx', hy'])]

/-! ### Order embeddings and the two-border expansion -/

theorem pos_map {κ : Type*} [LinearOrder κ] (f : ι ↪o κ) (t : Finset ι) (i : ι) :
    pos (t.map f.toEmbedding) (f i) = pos t i := by
  unfold pos
  rw [Finset.filter_map, Finset.card_map]
  congr 2
  ext x
  simp

/-- Invariance of the Pfaffian under order embeddings of the index set. -/
theorem pfaff_map {κ : Type*} [LinearOrder κ] (f : ι ↪o κ) (A : κ → κ → R) :
    ∀ (n : ℕ) (s : Finset ι), s.card = n →
      pfaff (fun i j => A (f i) (f j)) s = pfaff A (s.map f.toEmbedding) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    by_cases hne : s.Nonempty
    · obtain ⟨L, t, hLt, rfl⟩ : ∃ L t, (∀ z ∈ t, z < L) ∧ s = insert L t :=
        ⟨s.max' hne, s.erase (s.max' hne), fun z hz => lt_max'_of_mem_erase hne hz,
          eq_insert_max s hne⟩
      have hL : L ∉ t := fun h => lt_irrefl _ (hLt L h)
      rw [Finset.map_insert, pfaff_insert_max _ hLt, pfaff_insert_max A (s := t.map f.toEmbedding)
        (fun z hz => by
          obtain ⟨z', hz', rfl⟩ := Finset.mem_map.1 hz
          exact f.lt_iff_lt.2 (hLt z' hz')), Finset.sum_map]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hc : (t.erase i).card < n := by
        rw [← hs, Finset.card_insert_of_notMem hL]
        exact (Finset.card_erase_lt_of_mem hi).trans (Nat.lt_succ_self _)
      simp only [RelEmbedding.coe_toEmbedding]
      rw [pos_map, ih _ hc _ rfl]
      simp [Finset.map_erase]
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp

theorem adjE_map {κ : Type*} [LinearOrder κ] (f : ι ↪o κ) (A : κ → κ → R) (s : Finset ι)
    (j l : ι) :
    adjE (fun i j => A (f i) (f j)) s j l = adjE A (s.map f.toEmbedding) (f j) (f l) := by
  unfold adjE sgnE
  by_cases h : j = l
  · simp [h]
  · rw [if_neg h, if_neg (fun h' => h (f.injective h')), pos_map, pos_map,
      pfaff_map f A _ _ rfl, Finset.map_erase, Finset.map_erase]
    simp only [RelEmbedding.coe_toEmbedding, OrderEmbedding.lt_iff_lt]

/-- **Two-border expansion.** If `x < y` lie above `s` and `A x y = 0`, then
`Pf_{s ∪ {x, y}}(A) = ∑_{a, b ∈ s} A a x · P_s(a, b) · A b y`, i.e. `xᵀ P(A_s) y` for the
border columns `x = A(·, x)`, `y = A(·, y)`. -/
theorem pfaff_insert_insert (A : ι → ι → R) {s : Finset ι} {x y : ι}
    (hx : ∀ z ∈ s, z < x) (hxy : x < y) (h0 : A x y = 0) :
    pfaff A (insert y (insert x s)) =
      ∑ a ∈ s, ∑ b ∈ s, A a x * adjE A s a b * A b y := by
  have hxs : x ∉ s := fun h => lt_irrefl _ (hx x h)
  rw [pfaff_insert_max A (fun z hz => by
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hxy
      · exact (hx z hz).trans hxy),
    Finset.sum_insert hxs, h0, mul_zero, zero_mul, zero_add]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hxi : x ≠ i := fun h => hxs (h ▸ hi)
  rw [pos_insert_of_lt (hx i hi), Finset.erase_insert_of_ne hxi,
    pfaff_insert_max A (fun z hz => hx z (Finset.mem_of_mem_erase hz)),
    ← Finset.add_sum_erase s (fun a => A a x * adjE A s a i * A i y) hi]
  simp only [adjE, ↓reduceIte, mul_zero, zero_mul, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  rw [if_neg hji]
  unfold sgnE
  rw [pos_erase hi j]
  generalize pos (s.erase i) j = p
  rcases lt_or_gt_of_ne hji with h | h <;>
    simp [h, not_lt.2 h.le, pow_add, pow_succ] <;> ring

/-! ### Nonvanishing on nonsingular principal submatrices -/

section Field

variable {𝕜 : Type*} [Field 𝕜]

/-- The principal submatrix of `A` on `s` is injective (nonsingular). -/
def InjOnSet (A : ι → ι → 𝕜) (s : Finset ι) : Prop :=
  ∀ v : ι → 𝕜, (∀ a ∈ s, ∑ b ∈ s, A a b * v b = 0) → ∀ b ∈ s, v b = 0

/-- A nonsingular principal submatrix has a two-sided inverse on `s`. -/
theorem exists_inv_of_injOnSet {A : ι → ι → 𝕜} {s : Finset ι} (h : InjOnSet A s) :
    ∃ N : ι → ι → 𝕜,
      (∀ a ∈ s, ∀ i ∈ s, ∑ b ∈ s, A a b * N b i = if a = i then 1 else 0) ∧
      (∀ a ∈ s, ∀ i ∈ s, ∑ b ∈ s, N a b * A b i = if a = i then 1 else 0) := by
  classical
  let M : Matrix s s 𝕜 := fun a b => A a b
  have hker : ∀ w : s → 𝕜, M.mulVecLin w = 0 → w = 0 := by
    intro w hw
    let v : ι → 𝕜 := fun b => if hb : b ∈ s then w ⟨b, hb⟩ else 0
    have hv : ∀ a ∈ s, ∑ b ∈ s, A a b * v b = 0 := by
      intro a ha
      have := congrFun hw ⟨a, ha⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at this
      rw [← Finset.sum_coe_sort s]
      simpa [v, M] using this
    funext b
    have := h v hv b b.2
    simpa [v] using this
  have hinj : Function.Injective M.mulVec :=
    LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 hker)
  have hdet : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_injective_iff_isUnit.1 hinj)
  refine ⟨fun b i => if hb : b ∈ s then if hi : i ∈ s then M⁻¹ ⟨b, hb⟩ ⟨i, hi⟩ else 0 else 0,
    ?_, ?_⟩
  · intro a ha i hi
    have := congrFun (congrFun (Matrix.mul_nonsing_inv M hdet) ⟨a, ha⟩) ⟨i, hi⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← Finset.sum_coe_sort s]
    simpa [M, hi, Subtype.ext_iff] using this
  · intro a ha i hi
    have := congrFun (congrFun (Matrix.nonsing_inv_mul M hdet) ⟨a, ha⟩) ⟨i, hi⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← Finset.sum_coe_sort s]
    simpa [M, ha, Subtype.ext_iff] using this


/-- The inverse of a nonsingular alternating principal submatrix is skew on `s`. -/
theorem inv_skew_of_injOnSet {A : ι → ι → 𝕜} (hA : ∀ i j, A j i = -A i j) {s : Finset ι}
    (h : InjOnSet A s) {N : ι → ι → 𝕜}
    (hR : ∀ a ∈ s, ∀ i ∈ s, ∑ b ∈ s, A a b * N b i = if a = i then 1 else 0)
    (hL : ∀ a ∈ s, ∀ i ∈ s, ∑ b ∈ s, N a b * A b i = if a = i then 1 else 0) :
    ∀ i ∈ s, ∀ j ∈ s, N j i = -N i j := by
  intro i hi j hj
  -- `-Nᵀ` is also a right inverse; uniqueness of right inverses
  have hzero := h (fun b => N b i + N i b) (fun a ha => by
    have h1 := hR a ha i hi
    have h2 := hL i hi a ha
    have h3 : ∑ b ∈ s, A a b * N i b = -∑ b ∈ s, N i b * A b a := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hA b a]; ring
    simp only [mul_add, Finset.sum_add_distrib]
    rw [h1, h3, h2]
    by_cases hai : a = i
    · subst hai; simp
    · rw [if_neg hai, if_neg (Ne.symm hai)]; simp) j hj
  linear_combination hzero

/-- **Nonvanishing.** Over a field of characteristic zero, the Pfaffian of a nonsingular
alternating principal submatrix is nonzero. -/
theorem pfaff_ne_zero_of_injOnSet [CharZero 𝕜] (A : ι → ι → 𝕜) (hA : ∀ i j, A j i = -A i j)
    (hdiag : ∀ i, A i i = 0) :
    ∀ (n : ℕ) (s : Finset ι), s.card = n → InjOnSet A s → pfaff A s ≠ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs h
    by_cases hne : s.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
    obtain ⟨N, hR, hL⟩ := exists_inv_of_injOnSet h
    have hskew := inv_skew_of_injOnSet hA h hR hL
    have hNd : ∀ i ∈ s, N i i = 0 := by
      intro i hi
      have := hskew i hi i hi
      have h2 : (2 : 𝕜) * N i i = 0 := by linear_combination this
      simpa using h2
    -- a nonzero off-diagonal entry of the inverse
    obtain ⟨i, hi, j, hj, hij, hN⟩ : ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ N i j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨a, ha⟩ := hne
      have := hR a ha a ha
      rw [if_pos rfl, Finset.sum_eq_zero (fun b hb => by
        by_cases hba : b = a
        · rw [hba, hNd a ha, mul_zero]
        · rw [hcon b hb a ha hba, mul_zero])] at this
      exact zero_ne_one this
    set t := (s.erase j).erase i with ht
    have hit : i ∉ t := by simp [ht]
    have hjt : j ∉ t := by simp [ht]
    have hts : ∀ b ∈ t, b ∈ s := fun b hb => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)
    -- the complementary principal submatrix is nonsingular
    have htinj : InjOnSet A t := by
      intro v hv
      set w : ι → 𝕜 := fun b => if b ∈ t then v b else 0 with hw
      set c : ι → 𝕜 := fun a => ∑ b ∈ s, A a b * w b with hc
      have hcv : ∀ a, c a = ∑ b ∈ t, A a b * v b := by
        intro a
        simp only [hc, hw, mul_ite, mul_zero]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hts]
      have hct : ∀ a ∈ t, c a = 0 := fun a ha => by rw [hcv]; exact hv a ha
      -- `w = N c` on `s`
      have hwN : ∀ e ∈ s, w e = ∑ b ∈ s, N e b * c b := by
        intro e he
        simp only [hc, Finset.mul_sum]
        rw [Finset.sum_comm]
        have : ∀ a ∈ s, ∑ b ∈ s, N e b * (A b a * w a) = (if e = a then 1 else 0) * w a := by
          intro a ha
          rw [← hL e he a ha, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [Finset.sum_congr rfl this]
        simp [he]
      have htwo : ∀ e ∈ s, w e = N e i * c i + N e j * c j := by
        intro e he
        rw [hwN e he, Finset.sum_eq_add_of_mem i j hi hj hij (fun b hb hbij => by
          have hbt : b ∈ t := by simp [ht, hbij.1, hbij.2, hb]
          rw [hct b hbt, mul_zero])]
      have hwi : w i = 0 := by simp [hw, hit]
      have hwj : w j = 0 := by simp [hw, hjt]
      have hcj : c j = 0 := by
        have := htwo i hi
        rw [hwi, hNd i hi, zero_mul, zero_add] at this
        exact (mul_eq_zero.1 this.symm).resolve_left hN
      have hci : c i = 0 := by
        have := htwo j hj
        rw [hwj, hNd j hj, hcj, mul_zero, add_zero, hskew i hi j hj] at this
        exact (mul_eq_zero.1 this.symm).resolve_left (neg_ne_zero.2 hN)
      intro b hb
      have := htwo b (hts b hb)
      rw [hci, hcj, mul_zero, mul_zero, add_zero] at this
      simpa [hw, hb] using this
    have htcard : t.card < n := by
      rw [ht]
      have := Finset.card_erase_lt_of_mem (Finset.mem_erase.2 ⟨hij, hi⟩)
      have := Finset.card_erase_lt_of_mem hj
      omega
    have hpt := ih _ htcard t rfl htinj
    intro hps
    -- column `j` of the adjugate is a kernel vector
    have hker := h (fun b => adjE A s b j) (fun a ha => by
      rw [sum_mul_adjE A hA hdiag s ha hj, hps]; simp) i hi
    rw [adjE, if_neg hij] at hker
    exact hpt ((mul_eq_zero.1 hker).resolve_left (sgnE_ne_zero s j i))

end Field

/-! ### The matrix layer on `Fin n` -/

section Matrix

open Matrix

variable {n : ℕ}

/-- The Pfaffian of a square matrix on `Fin n` (meaningful for alternating matrices). -/
def Pf (K : Matrix (Fin n) (Fin n) R) : R := pfaff K Finset.univ

/-- The paper's polynomial Pfaffian adjugate: `P(K)_{ij} = (-1)^{i+j} Pf(K_{îĵ})` for `i < j`
(the parity of `i + j` is the same for zero- and one-based indices), skew completion, zero
diagonal. -/
def pfAdj (K : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := fun i j =>
  if i < j then (-1) ^ ((i : ℕ) + j) * pfaff K ((Finset.univ.erase i).erase j)
  else if j < i then -((-1) ^ ((j : ℕ) + i) * pfaff K ((Finset.univ.erase j).erase i))
  else 0

theorem pos_univ_fin (k : Fin n) : pos (Finset.univ : Finset (Fin n)) k = k := by
  unfold pos
  have : (Finset.univ.filter (· < k)) = Finset.Iio k := by ext; simp
  rw [this, Fin.card_Iio]

theorem pfAdj_eq_adjE (K : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    pfAdj K i j = adjE K Finset.univ i j := by
  unfold pfAdj adjE sgnE
  rw [pos_univ_fin, pos_univ_fin]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [if_pos h, if_neg h.ne, if_pos h, Finset.erase_right_comm, add_comm (j : ℕ)]; ring
  · simp
  · rw [if_neg (not_lt.2 h.le), if_pos h, if_neg h.ne', if_neg (not_lt.2 h.le)]; ring

theorem pfAdj_skew (K : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    pfAdj K j i = -pfAdj K i j := by
  unfold pfAdj
  rcases lt_trichotomy i j with h | rfl | h
  · rw [if_neg (not_lt.2 h.le), if_pos h, if_pos h]
  · simp
  · rw [if_pos h, if_neg (not_lt.2 h.le), if_pos h]; ring

/-- **`K P(K) = Pf(K) I`** for an alternating matrix `K`. -/
theorem mul_pfAdj (K : Matrix (Fin n) (Fin n) R) (hK : ∀ i j, K j i = -K i j)
    (hd : ∀ i, K i i = 0) : K * pfAdj K = Pf K • (1 : Matrix (Fin n) (Fin n) R) := by
  ext a l
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [pfAdj_eq_adjE]
  rw [sum_mul_adjE K hK hd Finset.univ (Finset.mem_univ a) (Finset.mem_univ l), Pf]
  split_ifs <;> simp

/-- `P(K) K = Pf(K) I`. -/
theorem pfAdj_mul (K : Matrix (Fin n) (Fin n) R) (hK : ∀ i j, K j i = -K i j)
    (hd : ∀ i, K i i = 0) : pfAdj K * K = Pf K • (1 : Matrix (Fin n) (Fin n) R) := by
  have h := congrArg Matrix.transpose (mul_pfAdj K hK hd)
  rw [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_one] at h
  have h1 : (pfAdj K)ᵀ = -pfAdj K := by ext i j; simp [pfAdj_skew K i j]
  have h2 : Kᵀ = -K := by ext i j; simp [hK i j]
  rw [h1, h2, neg_mul_neg] at h
  exact h

theorem Pf_zero_size (K : Matrix (Fin 0) (Fin 0) R) : Pf K = 1 := by
  rw [Pf, Finset.univ_eq_empty]; exact pfaff_empty K

/-- The convention `Pf [[0, k], [-k, 0]] = k`. -/
theorem Pf_two (K : Matrix (Fin 2) (Fin 2) R) : Pf K = K 0 1 := by
  have : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [Pf, this, pfaff_pair K (show (0 : Fin 2) < 1 by decide)]

/-- Alternating hypotheses from `Kᵀ = -K` over a ring without `2`-torsion issues. -/
theorem alt_of_transpose_eq_neg {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {K : Matrix (Fin n) (Fin n) 𝕜} (hK : Kᵀ = -K) :
    (∀ i j, K j i = -K i j) ∧ ∀ i, K i i = 0 := by
  have h1 : ∀ i j, K j i = -K i j := fun i j => by
    have := congrFun (congrFun hK i) j
    simpa using this
  refine ⟨h1, fun i => ?_⟩
  have := h1 i i
  have h2 : (2 : 𝕜) * K i i = 0 := by linear_combination this
  simpa using h2

/-- **Pfaffian criterion for nonsingularity.** For an alternating matrix over a field of
characteristic zero, `Pf K ≠ 0 ↔ K` is invertible. -/
theorem Pf_ne_zero_iff {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (K : Matrix (Fin n) (Fin n) 𝕜)
    (hK : ∀ i j, K j i = -K i j) (hd : ∀ i, K i i = 0) : Pf K ≠ 0 ↔ IsUnit K.det := by
  constructor
  · intro h
    have hinv : K * ((Pf K)⁻¹ • pfAdj K) = 1 := by
      rw [Matrix.mul_smul, mul_pfAdj K hK hd, smul_smul, inv_mul_cancel₀ h, one_smul]
    exact Matrix.isUnit_det_of_right_inverse hinv
  · intro h
    refine pfaff_ne_zero_of_injOnSet K hK hd _ Finset.univ rfl fun v hv b _ => ?_
    have hmv : K *ᵥ v = 0 := by
      funext a
      have := hv a (Finset.mem_univ a)
      simpa [Matrix.mulVec, dotProduct] using this
    have hinj := Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det K).2 h)
    have : v = 0 := hinj (by rw [hmv, Matrix.mulVec_zero])
    simp [this]

end Matrix

end SkewPfaffian
end RenewalGeometry
