/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact minimal-record partition refinement and robust recovery

This file proves all five clauses of `thm:minimal-record-audit` on an actual
finite record automaton: bounded-word refinement exactness, finite termination,
identification of the stable partition with future-word equivalence, the finite
signature residual criterion, and positive-margin robust recovery.
-/

open Filter Matrix

noncomputable section

namespace NCG

/-! ## `thm:minimal-record-audit`: termination, exactness, and record margin -/

namespace MinimalRecordPartitionRefinement

variable {R A X : Type*}

/-- Run a future word through the record dynamics, one letter at a time. -/
def run (u : A → R → R) (w : List A) (r : R) : R :=
  w.foldl (fun x a => u a x) r

@[simp] theorem run_nil (u : A → R → R) (r : R) : run u [] r = r := rfl

theorem run_cons (u : A → R → R) (a : A) (w : List A) (r : R) :
    run u (a :: w) r = run u w (u a r) := rfl

/-- The `k`-th round of the partition-refinement algorithm: records agree on
their immediate response coordinates and, recursively, on every one-letter
update for `k` further rounds. -/
def eqv (out : R → X → ℝ) (u : A → R → R) : ℕ → R → R → Prop
  | 0, r, s => out r = out s
  | k + 1, r, s => out r = out s ∧ ∀ a, eqv out u k (u a r) (u a s)

theorem eqv_zero (out : R → X → ℝ) (u : A → R → R) (r s : R) :
    eqv out u 0 r s ↔ out r = out s := Iff.rfl

theorem eqv_succ (out : R → X → ℝ) (u : A → R → R) (k : ℕ) (r s : R) :
    eqv out u (k + 1) r s ↔
      out r = out s ∧ ∀ a, eqv out u k (u a r) (u a s) := Iff.rfl

/-- Separation by future words of length at most `k`. -/
def sep (out : R → X → ℝ) (u : A → R → R) (k : ℕ) (r s : R) : Prop :=
  ∀ w : List A, w.length ≤ k → out (run u w r) = out (run u w s)

/-- Full word equivalence: no future word of any length separates. -/
def wordEqv (out : R → X → ℝ) (u : A → R → R) (r s : R) : Prop :=
  ∀ w : List A, out (run u w r) = out (run u w s)

variable (out : R → X → ℝ) (u : A → R → R)

/-- **(P1)** The `k`-th refinement identifies exactly the records not
separated by a future word of length at most `k`. -/
theorem eqv_iff_sep : ∀ (k : ℕ) (r s : R),
    eqv out u k r s ↔ sep out u k r s := by
  intro k
  induction k with
  | zero =>
      intro r s
      constructor
      · intro h w hw
        have hnil : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
        subst hnil
        exact h
      · intro h
        exact h [] (by simp)
  | succ k ih =>
      intro r s
      constructor
      · rintro ⟨h0, hrec⟩ w hw
        cases w with
        | nil => exact h0
        | cons a w' =>
            have hw' : w'.length ≤ k := by
              have : w'.length + 1 ≤ k + 1 := by simpa using hw
              omega
            exact (ih (u a r) (u a s)).mp (hrec a) w' hw'
      · intro h
        refine ⟨h [] (by simp), fun a => (ih _ _).mpr ?_⟩
        intro w hw
        exact h (a :: w) (by simpa using Nat.succ_le_succ hw)

/-- Each refinement round refines the previous one. -/
theorem eqv_succ_imp : ∀ (k : ℕ) (r s : R),
    eqv out u (k + 1) r s → eqv out u k r s := by
  intro k
  induction k with
  | zero => exact fun r s h => h.1
  | succ k ih => exact fun r s h => ⟨h.1, fun a => ih _ _ (h.2 a)⟩

/-- Monotonicity of the refinement rounds. -/
theorem eqv_of_le : ∀ (k j : ℕ), j ≤ k → ∀ r s : R,
    eqv out u k r s → eqv out u j r s := by
  intro k
  induction k with
  | zero =>
      intro j hj r s h
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      exact h
  | succ k ih =>
      intro j hj r s h
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · exact h
      · exact ih j (Nat.lt_succ_iff.mp hlt) r s (eqv_succ_imp out u k r s h)

/-- Once round `k+1` equals round `k`, every later round equals round `k`. -/
theorem eqv_stable_propagates {k : ℕ}
    (hst : ∀ r s : R, eqv out u (k + 1) r s ↔ eqv out u k r s) :
    ∀ (j : ℕ), k ≤ j → ∀ r s : R, eqv out u j r s ↔ eqv out u k r s := by
  intro j
  induction j with
  | zero =>
      intro hj r s
      obtain rfl : k = 0 := Nat.le_zero.mp hj
      exact Iff.rfl
  | succ j ih =>
      intro hj r s
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · exact Iff.rfl
      · have hkj : k ≤ j := Nat.lt_succ_iff.mp hlt
        constructor
        · intro h
          exact (hst r s).mp ⟨h.1, fun a => (ih hkj _ _).mp (h.2 a)⟩
        · intro h
          have h1 := (hst r s).mpr h
          exact ⟨h1.1, fun a => (ih hkj _ _).mpr (h1.2 a)⟩

/-- The refinement setoid at round `k`. -/
def eqvSetoid (k : ℕ) : Setoid R where
  r := eqv out u k
  iseqv := by
    refine ⟨fun r => ?_, fun {r s} h => ?_, fun {r s t} h1 h2 => ?_⟩
    · exact (eqv_iff_sep out u k r r).mpr fun w _ => rfl
    · exact (eqv_iff_sep out u k s r).mpr fun w hw =>
        ((eqv_iff_sep out u k r s).mp h w hw).symm
    · exact (eqv_iff_sep out u k r t).mpr fun w hw =>
        ((eqv_iff_sep out u k r s).mp h1 w hw).trans
          ((eqv_iff_sep out u k s t).mp h2 w hw)

section Termination

variable [Fintype R]

/-- A strict refinement round strictly increases the number of blocks. -/
theorem card_quotient_lt_of_strict {k : ℕ}
    (hstrict : ¬ ∀ r s : R, eqv out u (k + 1) r s ↔ eqv out u k r s) :
    ∀ (c c' : ℕ), c = Nat.card (Quotient (eqvSetoid out u k)) →
      c' = Nat.card (Quotient (eqvSetoid out u (k + 1))) → c < c' := by
  classical
  intro c c' hc hc'
  -- the canonical surjection from the finer quotient onto the coarser one
  let f : Quotient (eqvSetoid out u (k + 1)) → Quotient (eqvSetoid out u k) :=
    Quotient.map' id (fun r s h => eqv_succ_imp out u k r s h)
  have hfsurj : Function.Surjective f := by
    intro q
    refine Quotient.inductionOn q fun r => ⟨Quotient.mk'' r, rfl⟩
  have hfnotinj : ¬ Function.Injective f := by
    intro hinj
    apply hstrict
    intro r s
    refine ⟨fun h => eqv_succ_imp out u k r s h, fun h => ?_⟩
    have : f (Quotient.mk'' r) = f (Quotient.mk'' s) := Quotient.sound' h
    have := hinj this
    exact Quotient.exact' this
  have hlt : Fintype.card (Quotient (eqvSetoid out u k)) <
      Fintype.card (Quotient (eqvSetoid out u (k + 1))) :=
    Fintype.card_lt_of_surjective_not_injective f hfsurj hfnotinj
  rw [hc, hc', Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hlt

/-- Some round at or below `n_rec - 1` is already stable. -/
theorem exists_stable_round :
    ∃ k ≤ Fintype.card R - 1,
      ∀ r s : R, eqv out u (k + 1) r s ↔ eqv out u k r s := by
  classical
  cases isEmpty_or_nonempty R with
  | inl hemp =>
      exact ⟨0, Nat.zero_le _, fun r s => (hemp.false r).elim⟩
  | inr hne =>
      by_contra hcon
      set n := Fintype.card R with hn
      have hstrict : ∀ k ≤ n - 1,
          ¬ ∀ r s : R, eqv out u (k + 1) r s ↔ eqv out u k r s := by
        intro k hk hstable
        exact hcon ⟨k, by simpa [n] using hk, hstable⟩
      have hstep : ∀ k ≤ n - 1,
          Nat.card (Quotient (eqvSetoid out u k)) <
            Nat.card (Quotient (eqvSetoid out u (k + 1))) := by
        intro k hk
        exact card_quotient_lt_of_strict out u (hstrict k hk) _ _ rfl rfl
      have hgrow : ∀ k ≤ n, k + 1 ≤ Nat.card (Quotient (eqvSetoid out u k)) := by
        intro k
        induction k with
        | zero =>
            intro _
            have : Nonempty (Quotient (eqvSetoid out u 0)) :=
              Nonempty.map (fun r => Quotient.mk'' r) hne
            letI : Nonempty (Quotient (eqvSetoid out u 0)) := this
            have hpos : 0 < Nat.card (Quotient (eqvSetoid out u 0)) :=
              Nat.card_pos
            omega
        | succ k ih =>
            intro hk
            have hk' : k ≤ n - 1 := by omega
            have h1 := ih (by omega)
            have h2 := hstep k hk'
            omega
      have hub : Nat.card (Quotient (eqvSetoid out u n)) ≤ n := by
        have : Fintype.card (Quotient (eqvSetoid out u n)) ≤ Fintype.card R :=
          Fintype.card_quotient_le _
      -- rewrite through `Nat.card`
        rw [Nat.card_eq_fintype_card]
        exact this
      have := hgrow n le_rfl
      omega

/-- **(P2)** The refinement stabilizes at round `n_rec - 1`: every later round
gives the same partition, and every strict round happens strictly before
`n_rec - 1`. -/
theorem refinement_stabilizes :
    (∀ j, Fintype.card R - 1 ≤ j → ∀ r s : R,
      eqv out u j r s ↔ eqv out u (Fintype.card R - 1) r s)
    ∧ (∀ k, (¬ ∀ r s : R, eqv out u (k + 1) r s ↔ eqv out u k r s) →
        k < Fintype.card R - 1) := by
  obtain ⟨k₀, hk₀, hst⟩ := exists_stable_round out u
  have hprop := eqv_stable_propagates out u hst
  constructor
  · intro j hj r s
    rw [hprop j (le_trans hk₀ hj) r s, hprop (Fintype.card R - 1) hk₀ r s]
  · intro k hk
    by_contra hcon
    push Not at hcon
    apply hk
    intro r s
    rw [hprop (k + 1) (by omega) r s, hprop k (le_trans hk₀ hcon) r s]

/-- **(P3)** The stable partition is exactly full word equivalence — the
minimal record partition. -/
theorem stable_eq_wordEqv (r s : R) :
    eqv out u (Fintype.card R - 1) r s ↔ wordEqv out u r s := by
  constructor
  · intro h w
    have hj := (refinement_stabilizes out u).1
      (max (Fintype.card R - 1) w.length) (le_max_left _ _) r s
    have hjw : eqv out u (max (Fintype.card R - 1) w.length) r s := hj.mpr h
    exact (eqv_iff_sep out u _ r s).mp hjw w (le_max_right _ _)
  · intro h
    exact (eqv_iff_sep out u _ r s).mpr fun w _ => h w

end Termination

section Signatures

variable [Fintype R] [Fintype A] [Fintype X]

/-- The finite panel of response coordinates encountered before
stabilization: all future words of length at most `k`, paired with the
immediate response coordinates. -/
abbrev SigIndex (A X : Type*) (k : ℕ) : Type _ :=
  ((j : Fin (k + 1)) × (Fin (j : ℕ) → A)) × X

/-- The signature vector of a record: its responses along every future word
of length at most `k`, as a point of the finite Euclidean panel space. -/
def signature (k : ℕ) (r : R) : EuclideanSpace ℝ (SigIndex A X k) :=
  WithLp.toLp 2 fun p => out (run u (List.ofFn p.1.2) r) p.2

theorem signature_apply (k : ℕ) (r : R) (p : SigIndex A X k) :
    signature out u k r p = out (run u (List.ofFn p.1.2) r) p.2 := rfl

/-- The squared signature residual is the finite sum of squared coordinate
differences. -/
theorem signature_dist_sq (k : ℕ) (r s : R) :
    ‖signature out u k r - signature out u k s‖ ^ 2 =
      ∑ p : SigIndex A X k,
        (out (run u (List.ofFn p.1.2) r) p.2
          - out (run u (List.ofFn p.1.2) s) p.2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun p _ => ?_
  have happ : (signature out u k r - signature out u k s) p =
      out (run u (List.ofFn p.1.2) r) p.2
        - out (run u (List.ofFn p.1.2) s) p.2 := rfl
  rw [happ, Real.norm_eq_abs, sq_abs]

/-- **(P4)** The boxed criterion: two records are equivalent in the minimal
partition exactly when their signature residual `‖v(r) - v(s)‖²` vanishes. -/
theorem wordEqv_iff_signature_residual (r s : R) :
    wordEqv out u r s ↔
      ‖signature out u (Fintype.card R - 1) r
        - signature out u (Fintype.card R - 1) s‖ ^ 2 = 0 := by
  rw [signature_dist_sq]
  constructor
  · intro h
    refine Finset.sum_eq_zero fun p _ => ?_
    have := congrFun (h (List.ofFn p.1.2)) p.2
    rw [this, sub_self]
    exact zero_pow (by norm_num)
  · intro h
    have hcoord : ∀ p : SigIndex A X (Fintype.card R - 1),
        out (run u (List.ofFn p.1.2) r) p.2
          = out (run u (List.ofFn p.1.2) s) p.2 := by
      intro p
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun q _ => sq_nonneg _)).mp h p (Finset.mem_univ p)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith [sub_eq_zero.mp this]
    -- every word of length at most `n_rec - 1` arises from the panel
    have hsep : sep out u (Fintype.card R - 1) r s := by
      intro w hw
      funext x
      have hjlt : w.length < Fintype.card R - 1 + 1 := Nat.lt_succ_of_le hw
      have hofn : List.ofFn (fun i : Fin w.length => w.get i) = w :=
        List.ofFn_get w
      have := hcoord ⟨⟨⟨w.length, hjlt⟩, fun i => w.get i⟩, x⟩
      simpa [hofn] using this
    exact (stable_eq_wordEqv out u r s).mp
      ((eqv_iff_sep out u _ r s).mpr hsep)

/-- The set of separated record pairs. -/
def strictPairs : Finset (R × R) :=
  @Finset.filter _ (fun p => ¬ wordEqv out u p.1 p.2)
    (Classical.decPred _) Finset.univ

/-- The minimum nonzero signature distance `δ_rec`. -/
def recordMargin : ℝ :=
  if h : (strictPairs out u).Nonempty then
    (strictPairs out u).inf' h fun p =>
      ‖signature out u (Fintype.card R - 1) p.1
        - signature out u (Fintype.card R - 1) p.2‖
  else 0

/-- If at least two classes occur, the minimum nonzero signature distance is
positive. -/
theorem recordMargin_pos
    (h : ∃ r s : R, ¬ wordEqv out u r s) :
    0 < recordMargin out u := by
  classical
  obtain ⟨r, s, hrs⟩ := h
  have hmem : (r, s) ∈ strictPairs out u := by
    unfold strictPairs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hrs
  have hne : (strictPairs out u).Nonempty := ⟨(r, s), hmem⟩
  rw [recordMargin, dif_pos hne]
  rw [Finset.lt_inf'_iff]
  intro p hp
  have hpnot : ¬ wordEqv out u p.1 p.2 := by
    have := hp
    unfold strictPairs at this
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using this
  have hres : ‖signature out u (Fintype.card R - 1) p.1
      - signature out u (Fintype.card R - 1) p.2‖ ^ 2 ≠ 0 := by
    intro h0
    exact hpnot ((wordEqv_iff_signature_residual out u p.1 p.2).mpr h0)
  have : ‖signature out u (Fintype.card R - 1) p.1
      - signature out u (Fintype.card R - 1) p.2‖ ≠ 0 := by
    intro h0
    exact hres (by rw [h0]; ring)
  exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm this)

/-- The margin is a lower bound on the distance of separated signatures. -/
theorem recordMargin_le (r s : R) (h : ¬ wordEqv out u r s) :
    recordMargin out u ≤
      ‖signature out u (Fintype.card R - 1) r
        - signature out u (Fintype.card R - 1) s‖ := by
  classical
  have hmem : (r, s) ∈ strictPairs out u := by
    unfold strictPairs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have hne : (strictPairs out u).Nonempty := ⟨(r, s), hmem⟩
  rw [recordMargin, dif_pos hne]
  exact Finset.inf'_le _ hmem

/-- **(P5)** Robust recovery: if every estimated signature is within `ε` and
`4ε < δ_rec`, the `2ε`-threshold classifier recovers the minimal record
partition exactly. -/
theorem robust_recovery
    (est : R → EuclideanSpace ℝ (SigIndex A X (Fintype.card R - 1)))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hest : ∀ r, ‖est r - signature out u (Fintype.card R - 1) r‖ ≤ ε)
    (hmargin : 4 * ε < recordMargin out u) (r s : R) :
    wordEqv out u r s ↔ ‖est r - est s‖ ≤ 2 * ε := by
  set v : R → EuclideanSpace ℝ (SigIndex A X (Fintype.card R - 1)) :=
    signature out u (Fintype.card R - 1) with hv
  constructor
  · intro h
    have hveq : v r = v s := by
      have := (wordEqv_iff_signature_residual out u r s).mp h
      have hnorm : ‖v r - v s‖ = 0 := by
        have h0 : ‖v r - v s‖ ^ 2 = 0 := this
        nlinarith [norm_nonneg (v r - v s)]
      rwa [norm_sub_eq_zero_iff] at hnorm
    have hdec : est r - est s = (est r - v r) - (est s - v s) := by
      rw [hveq]; abel
    calc ‖est r - est s‖ = ‖(est r - v r) - (est s - v s)‖ := by rw [hdec]
      _ ≤ ‖est r - v r‖ + ‖est s - v s‖ := norm_sub_le _ _
      _ ≤ ε + ε := add_le_add (hest r) (hest s)
      _ = 2 * ε := by ring
  · intro h
    by_contra hnot
    have hlow := recordMargin_le out u r s hnot
    have htri : ‖v r - v s‖ ≤ ‖v r - est r‖ + ‖est r - est s‖
        + ‖est s - v s‖ := by
      have hdec : v r - v s = (v r - est r) + (est r - est s)
          + (est s - v s) := by abel
      rw [hdec]
      exact norm_add₃_le
    have h1 : ‖v r - est r‖ ≤ ε := by rw [norm_sub_rev]; exact hest r
    have h2 : ‖est s - v s‖ ≤ ε := hest s
    linarith

/-- **`thm:minimal-record-audit`, exact form.** (P1) each refinement round
identifies exactly the records not separated by a future word of that length;
(P2) the refinement stabilizes at round `n_rec - 1` and every strict round is
earlier; (P3) the stable partition is full word equivalence; (P4) the boxed
zero-residual criterion; (P5) positive margin and exact `4ε < δ_rec` robust
recovery. -/
theorem minimal_record_audit_exact :
    (∀ (k : ℕ) (r s : R), eqv out u k r s ↔ sep out u k r s)
    ∧ ((∀ j, Fintype.card R - 1 ≤ j → ∀ r s : R,
          eqv out u j r s ↔ eqv out u (Fintype.card R - 1) r s)
        ∧ (∀ k, (¬ ∀ r s : R, eqv out u (k + 1) r s ↔ eqv out u k r s) →
            k < Fintype.card R - 1))
    ∧ (∀ r s : R, eqv out u (Fintype.card R - 1) r s ↔ wordEqv out u r s)
    ∧ (∀ r s : R, wordEqv out u r s ↔
        ‖signature out u (Fintype.card R - 1) r
          - signature out u (Fintype.card R - 1) s‖ ^ 2 = 0)
    ∧ ((∃ r s : R, ¬ wordEqv out u r s) → 0 < recordMargin out u)
    ∧ (∀ (est : R → EuclideanSpace ℝ (SigIndex A X (Fintype.card R - 1)))
        (ε : ℝ), 0 ≤ ε →
        (∀ r, ‖est r - signature out u (Fintype.card R - 1) r‖ ≤ ε) →
        4 * ε < recordMargin out u →
        ∀ r s : R, wordEqv out u r s ↔ ‖est r - est s‖ ≤ 2 * ε) :=
  ⟨eqv_iff_sep out u, refinement_stabilizes out u, stable_eq_wordEqv out u,
    wordEqv_iff_signature_residual out u, recordMargin_pos out u,
    robust_recovery out u⟩

end Signatures

end MinimalRecordPartitionRefinement

end NCG
