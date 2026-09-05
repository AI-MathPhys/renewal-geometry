/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteGeneratorTransitionSemigroupExact
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Data.List.InsertIdx

/-!
# Exact marginalization of finite ordered Markov weights

This file isolates the algebra behind finite-dimensional consistency of a
continuous-time finite-state Markov process.  A path segment is a list of
time--state pairs.  Summing out a state at the end uses row normalization;
summing out an interior state uses Chapman--Kolmogorov.  The main theorem
iterates this local calculation through an arbitrary preceding path prefix.
-/

open Matrix Finset
open scoped BigOperators

noncomputable section

namespace NCG.FiniteOrderedMarkovMarginal

variable {T S : Type*} [Fintype S]

/-- Product of transition weights along a time--state list, conditional on
the preceding time and state. -/
def tailWeight (K : T → T → S → S → ℝ) :
    T → S → List (T × S) → ℝ
  | _, _, [] => 1
  | t, x, (u, y) :: ys => K t u x y * tailWeight K u y ys

/-- A finite ordered Markov weight with a time-dependent entrance law. -/
def chainWeight (μ : T → S → ℝ) (K : T → T → S → S → ℝ) :
    List (T × S) → ℝ
  | [] => 1
  | (t, x) :: xs => μ t x * tailWeight K t x xs

/-- Summing out the final state uses stochastic row normalization. -/
theorem sum_tailWeight_singleton
    (K : T → T → S → S → ℝ)
    (hrow : ∀ t u x, ∑ y, K t u x y = 1)
    (t u : T) (x : S) :
    ∑ y, tailWeight K t x [(u, y)] = 1 := by
  simpa [tailWeight] using hrow t u x

/-- Summing out one interior state composes the two neighboring kernels. -/
theorem sum_tailWeight_two
    (K : T → T → S → S → ℝ)
    (hchapman : ∀ s t u x z,
      ∑ y, K s t x y * K t u y z = K s u x z)
    (s t u : T) (x z : S) (zs : List (T × S)) :
    ∑ y, tailWeight K s x ((t, y) :: (u, z) :: zs) =
      tailWeight K s x ((u, z) :: zs) := by
  simp only [tailWeight]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [hchapman s t u x z]

/-- A state can be marginalized after any already-fixed prefix.  This is the
local consistency theorem used when passing from a larger ordered cylinder to
one obtained by deleting a single observation time. -/
theorem sum_tailWeight_insert_after_prefix
    (K : T → T → S → S → ℝ)
    (hrow : ∀ t u x, ∑ y, K t u x y = 1)
    (hchapman : ∀ s t u x z,
      ∑ y, K s t x y * K t u y z = K s u x z) :
    ∀ (s : T) (x : S) (pre : List (T × S))
      (t : T) (suffix : List (T × S)),
      (∑ y, tailWeight K s x
        (pre ++ (t, y) :: suffix)) =
        tailWeight K s x (pre ++ suffix) := by
  intro s x pre
  induction pre generalizing s x with
  | nil =>
      intro t suffix
      cases suffix with
      | nil => exact sum_tailWeight_singleton K hrow s t x
      | cons uz zs =>
          rcases uz with ⟨u, z⟩
          exact sum_tailWeight_two K hchapman s t u x z zs
  | cons az pre ih =>
      intro t suffix
      rcases az with ⟨a, w⟩
      simp only [List.cons_append, tailWeight]
      rw [← Finset.mul_sum]
      rw [ih a w t suffix]

/-- Summing out an appended final state needs only row normalization. -/
theorem sum_tailWeight_append_singleton
    (K : T → T → S → S → ℝ)
    (hrow : ∀ t u x, ∑ y, K t u x y = 1) :
    ∀ (s : T) (x : S) (pre : List (T × S)) (t : T),
      (∑ y, tailWeight K s x (pre ++ [(t, y)])) =
        tailWeight K s x pre := by
  intro s x pre
  induction pre generalizing s x with
  | nil =>
      intro t
      simpa [tailWeight] using sum_tailWeight_singleton K hrow s t x
  | cons uw pre ih =>
      intro t
      rcases uw with ⟨u, w⟩
      simp only [List.cons_append, tailWeight]
      rw [← Finset.mul_sum, ih u w t]

/-- Summing a singleton chain gives one when the entrance law is normalized. -/
theorem sum_chainWeight_singleton
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    (hμ : ∀ t, ∑ x, μ t x = 1) (t : T) :
    ∑ x, chainWeight μ K [(t, x)] = 1 := by
  simpa [chainWeight, tailWeight] using hμ t

/-- Summing out the first state transports the entrance law to the next
observation time. -/
theorem sum_chainWeight_head
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    (hentrance : ∀ t u y,
      ∑ x, μ t x * K t u x y = μ u y)
    (t u : T) (y : S) (ys : List (T × S)) :
    ∑ x, chainWeight μ K ((t, x) :: (u, y) :: ys) =
      chainWeight μ K ((u, y) :: ys) := by
  simp only [chainWeight, tailWeight]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [hentrance t u y]

/-- Exact one-coordinate projectivity for a finite ordered Markov weight.
The deleted observation may occur at the beginning, after an arbitrary
prefix, or at the end. -/
theorem sum_chainWeight_insert_after_prefix
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    (hμ : ∀ t, ∑ x, μ t x = 1)
    (hentrance : ∀ t u y,
      ∑ x, μ t x * K t u x y = μ u y)
    (hrow : ∀ t u x, ∑ y, K t u x y = 1)
    (hchapman : ∀ s t u x z,
      ∑ y, K s t x y * K t u y z = K s u x z) :
    ∀ (pre : List (T × S)) (t : T) (suffix : List (T × S)),
      (∑ x, chainWeight μ K
        (pre ++ (t, x) :: suffix)) =
        chainWeight μ K (pre ++ suffix) := by
  intro pre
  cases pre with
  | nil =>
      intro t suffix
      cases suffix with
      | nil => exact sum_chainWeight_singleton μ K hμ t
      | cons uy ys =>
          rcases uy with ⟨u, y⟩
          exact sum_chainWeight_head μ K hentrance t u y ys
  | cons sx pre =>
      intro t suffix
      rcases sx with ⟨s, x⟩
      simp only [List.cons_append, chainWeight]
      rw [← Finset.mul_sum]
      rw [sum_tailWeight_insert_after_prefix K hrow hchapman s x pre t suffix]

/-- Summing an appended final state from a full chain needs only entrance
normalization and stochastic rows. -/
theorem sum_chainWeight_append_singleton
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    (hμ : ∀ t, ∑ x, μ t x = 1)
    (hrow : ∀ t u x, ∑ y, K t u x y = 1) :
    ∀ (pre : List (T × S)) (t : T),
      (∑ y, chainWeight μ K (pre ++ [(t, y)])) =
        chainWeight μ K pre := by
  intro pre
  cases pre with
  | nil =>
      intro t
      exact sum_chainWeight_singleton μ K hμ t
  | cons sx pre =>
      intro t
      rcases sx with ⟨s, x⟩
      simp only [List.cons_append, chainWeight]
      rw [← Finset.mul_sum, sum_tailWeight_append_singleton K hrow s x pre t]

/-- Markov chain weight written on an ordered `Fin n` time tuple. -/
def finChainWeight {n : ℕ} (μ : T → S → ℝ)
    (K : T → T → S → S → ℝ) (times : Fin n → T)
    (states : Fin n → S) : ℝ :=
  chainWeight μ K (List.ofFn fun i => (times i, states i))

/-- Enumerating a tuple after inserting one coordinate is ordinary list
insertion at the same index. -/
theorem ofFn_insertNth {α : Type*} {n : ℕ}
    (p : Fin (n + 1)) (x : α) (f : Fin n → α) :
    List.ofFn (p.insertNth x f) = (List.ofFn f).insertIdx p x := by
  apply List.ext_getElem
  · have hp : p.val ≤ n := Nat.lt_succ_iff.mp p.isLt
    simp [List.length_insertIdx, hp]
  · intro i hleft hright
    let q : Fin (n + 1) := ⟨i, by simpa using hleft⟩
    obtain hq | ⟨j, hq⟩ := p.eq_self_or_eq_succAbove q
    · have hi : i = p.val := congrArg Fin.val hq
      subst i
      rw [List.getElem_ofFn, Fin.insertNth_apply_same,
        List.getElem_insertIdx_self]
    · have hi : i = (p.succAbove j).val := congrArg Fin.val hq
      subst i
      rw [List.getElem_ofFn, Fin.insertNth_apply_succAbove,
        List.getElem_insertIdx]
      by_cases hj : j.castSucc < p
      · have hs : (p.succAbove j).val = j.val := by
          exact congrArg Fin.val (Fin.succAbove_of_castSucc_lt p j hj)
        have hjval : j.val < p.val := hj
        simp [hs, hjval]
      · have hle : p ≤ j.castSucc := Fin.not_lt.mp hj
        have hleval : p.val ≤ j.val := hle
        have hs : (p.succAbove j).val = j.val + 1 := by
          exact congrArg Fin.val (Fin.succAbove_of_le_castSucc p j hle)
        have hnot : ¬j.val + 1 < p.val := by omega
        have hne : j.val + 1 ≠ p.val := by omega
        simp [hs, hnot, hne]

/-- A list insertion at an in-range index is the corresponding take/cons/drop
decomposition. -/
theorem insertIdx_eq_take_append_cons_drop {α : Type*}
    (l : List α) (n : ℕ) (a : α) (hn : n ≤ l.length) :
    l.insertIdx n a = l.take n ++ a :: l.drop n := by
  induction l generalizing n with
  | nil =>
      simp at hn
      subst n
      simp
  | cons b l ih =>
      cases n with
      | zero => simp
      | succ n =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at hn
          simp [ih n hn]

/-- Exact marginalization of an arbitrary coordinate of a finite time tuple.
The remaining times retain their inherited order through `Fin.removeNth`. -/
theorem sum_finChainWeight_insertNth
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    (hμ : ∀ t, ∑ x, μ t x = 1)
    (hentrance : ∀ t u y,
      ∑ x, μ t x * K t u x y = μ u y)
    (hrow : ∀ t u x, ∑ y, K t u x y = 1)
    (hchapman : ∀ s t u x z,
      ∑ y, K s t x y * K t u y z = K s u x z)
    {n : ℕ} (times : Fin (n + 1) → T) (p : Fin (n + 1))
    (states : Fin n → S) :
    (∑ x, finChainWeight μ K times (p.insertNth x states)) =
      finChainWeight μ K (p.removeNth times) states := by
  let rest : List (T × S) :=
    List.ofFn fun i : Fin n => (times (p.succAbove i), states i)
  have hfull (x : S) :
      (List.ofFn fun i : Fin (n + 1) =>
        (times i, p.insertNth x states i)) =
        rest.insertIdx p (times p, x) := by
    let full : Fin (n + 1) → T × S := fun i =>
      (times i, p.insertNth (α := fun _ => S) x states i)
    let inserted : Fin (n + 1) → T × S :=
      p.insertNth (α := fun _ => T × S) (times p, x)
        (fun i : Fin n => (times (p.succAbove i), states i))
    have hpairs : full = inserted := by
      apply funext
      intro i
      induction i using p.succAboveCases <;> simp [full, inserted]
    change List.ofFn full = _
    rw [hpairs]
    change List.ofFn
      (p.insertNth (times p, x)
        (fun i : Fin n => (times (p.succAbove i), states i))) = _
    rw [ofFn_insertNth]
  have hdecomp (x : S) :
      rest.insertIdx p (times p, x) =
        rest.take p ++ (times p, x) :: rest.drop p := by
    exact insertIdx_eq_take_append_cons_drop rest p (times p, x)
      (by simpa [rest] using (Nat.lt_succ_iff.mp p.isLt))
  simp only [finChainWeight]
  simp_rw [hfull, hdecomp]
  rw [sum_chainWeight_insert_after_prefix μ K hμ hentrance hrow
    hchapman (rest.take p) (times p) (rest.drop p)]
  rw [List.take_append_drop]
  rfl

/-- The finite ordered Markov weights sum to one on every finite time tuple.
This derives normalization by repeatedly summing out the last state. -/
theorem sum_finChainWeight
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    (hμ : ∀ t, ∑ x, μ t x = 1)
    (hentrance : ∀ t u y,
      ∑ x, μ t x * K t u x y = μ u y)
    (hrow : ∀ t u x, ∑ y, K t u x y = 1)
    (hchapman : ∀ s t u x z,
      ∑ y, K s t x y * K t u y z = K s u x z) :
    ∀ {n : ℕ} (times : Fin n → T),
      ∑ states : Fin n → S, finChainWeight μ K times states = 1 := by
  intro n
  induction n with
  | zero =>
      intro times
      simp [finChainWeight, chainWeight]
  | succ n ih =>
      intro times
      let e := Fin.snocEquiv (fun _ : Fin (n + 1) => S)
      rw [← e.sum_comp]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      calc
        (∑ states : Fin n → S, ∑ x : S,
            finChainWeight μ K times (e (x, states))) =
            ∑ states : Fin n → S,
              finChainWeight μ K (fun i => times i.castSucc) states := by
          apply Finset.sum_congr rfl
          intro states _
          change (∑ x : S, chainWeight μ K
              (List.ofFn fun i => (times i, e (x, states) i))) = _
          have hlist (x : S) :
              (List.ofFn fun i => (times i, e (x, states) i)) =
                (List.ofFn fun i : Fin n => (times i.castSucc, states i)) ++
                  [(times (Fin.last n), x)] := by
            rw [List.ofFn_succ']
            simp [e]
          simp_rw [hlist]
          simpa [finChainWeight] using
            (sum_chainWeight_insert_after_prefix μ K hμ hentrance hrow
              hchapman (List.ofFn fun i : Fin n =>
                (times i.castSucc, states i)) (times (Fin.last n)) [])
        _ = 1 := ih (fun i => times i.castSucc)

/-- Finite-chain normalization in its minimal form: entrance normalization
and stochastic rows suffice. -/
theorem sum_finChainWeight_of_rowStochastic
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    (hμ : ∀ t, ∑ x, μ t x = 1)
    (hrow : ∀ t u x, ∑ y, K t u x y = 1) :
    ∀ {n : ℕ} (times : Fin n → T),
      ∑ states : Fin n → S, finChainWeight μ K times states = 1 := by
  intro n
  induction n with
  | zero =>
      intro times
      simp [finChainWeight, chainWeight]
  | succ n ih =>
      intro times
      let e := Fin.snocEquiv (fun _ : Fin (n + 1) => S)
      rw [← e.sum_comp]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      calc
        (∑ states : Fin n → S, ∑ x : S,
            finChainWeight μ K times (e (x, states))) =
            ∑ states : Fin n → S,
              finChainWeight μ K (fun i => times i.castSucc) states := by
          apply Finset.sum_congr rfl
          intro states _
          change (∑ x : S, chainWeight μ K
              (List.ofFn fun i => (times i, e (x, states) i))) = _
          have hlist (x : S) :
              (List.ofFn fun i => (times i, e (x, states) i)) =
                (List.ofFn fun i : Fin n => (times i.castSucc, states i)) ++
                  [(times (Fin.last n), x)] := by
            rw [List.ofFn_succ']
            simp [e]
          simp_rw [hlist]
          simpa [finChainWeight] using
            (sum_chainWeight_append_singleton μ K hμ hrow
              (List.ofFn fun i : Fin n =>
                (times i.castSucc, states i)) (times (Fin.last n)))
        _ = 1 := ih (fun i => times i.castSucc)

/-- Conditional transition products are nonnegative when every kernel entry
is nonnegative. -/
theorem tailWeight_nonnegative
    (K : T → T → S → S → ℝ)
    (hK : ∀ t u x y, 0 ≤ K t u x y) :
    ∀ t x xs, 0 ≤ tailWeight K t x xs := by
  intro t x xs
  induction xs generalizing t x with
  | nil => simp [tailWeight]
  | cons uy ys ih =>
      rcases uy with ⟨u, y⟩
      exact mul_nonneg (hK t u x y) (ih u y)

/-- Full finite-chain weights are nonnegative under nonnegative entrance and
transition weights. -/
theorem chainWeight_nonnegative
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    (hμ0 : ∀ t x, 0 ≤ μ t x)
    (hK : ∀ t u x y, 0 ≤ K t u x y) :
    ∀ xs, 0 ≤ chainWeight μ K xs := by
  intro xs
  cases xs with
  | nil => simp [chainWeight]
  | cons tx ys =>
      rcases tx with ⟨t, x⟩
      exact mul_nonneg (hμ0 t x) (tailWeight_nonnegative K hK t x ys)

/-- The genuine atomic finite-dimensional law associated with an ordered
finite time tuple. -/
def finChainLaw [MeasurableSpace S] {n : ℕ}
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    (times : Fin n → T) : MeasureTheory.Measure (Fin n → S) :=
  MeasureTheory.Measure.sum fun states =>
    ENNReal.ofReal (finChainWeight μ K times states) •
      MeasureTheory.Measure.dirac states

/-- An atom of the finite-chain law has exactly the corresponding chain
weight. -/
theorem finChainLaw_apply_singleton [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    {n : ℕ} (times : Fin n → T) (states : Fin n → S) :
    finChainLaw μ K times {states} =
      ENNReal.ofReal (finChainWeight μ K times states) := by
  rw [finChainLaw, MeasureTheory.Measure.sum_apply_of_countable]
  rw [tsum_eq_single states]
  · simp
  · intro other hne
    simp [hne]

/-- A one-coordinate real-weight marginalization identity lifts exactly to
the corresponding projection identity for the atomic finite-chain laws. -/
theorem finChainLaw_map_removeNth [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    {n : ℕ} (times : Fin (n + 1) → T) (p : Fin (n + 1))
    (hweight : ∀ states : Fin (n + 1) → S,
      0 ≤ finChainWeight μ K times states)
    (hmarginal : ∀ states : Fin n → S,
      (∑ x, finChainWeight μ K times (p.insertNth x states)) =
        finChainWeight μ K (p.removeNth times) states) :
    finChainLaw μ K (p.removeNth times) =
      MeasureTheory.Measure.map (p.removeNth ·) (finChainLaw μ K times) := by
  classical
  apply MeasureTheory.Measure.ext_of_singleton
  intro states
  rw [finChainLaw_apply_singleton]
  rw [MeasureTheory.Measure.map_apply
    (measurable_of_finite (p.removeNth ·))
    (MeasurableSet.singleton states)]
  rw [finChainLaw, MeasureTheory.Measure.sum_apply_of_countable]
  rw [← (p.insertNthEquiv (fun _ => S)).tsum_eq]
  rw [tsum_fintype]
  rw [Fintype.sum_prod_type]
  simp only [MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.dirac_apply,
    Set.mem_preimage, Set.mem_singleton_iff, smul_eq_mul]
  have hindicator (x : S) (xs : Fin n → S) :
      ((fun z : Fin (n + 1) → S => p.removeNth z) ⁻¹'
          ({states} : Set (Fin n → S))).indicator
          (1 : (Fin (n + 1) → S) → ENNReal)
          (p.insertNth (α := fun _ => S) x xs) =
        if xs = states then (1 : ENNReal) else 0 := by
    by_cases hxs : xs = states
    · subst xs
      simp
    · simp [Set.indicator_of_notMem, hxs]
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk]
  simp_rw [hindicator]
  simp
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · exact congrArg ENNReal.ofReal (hmarginal states).symm
  · intro x _
    exact hweight (p.insertNth x states)

/-- Normalized nonnegative finite-chain weights define a probability
measure, with no additional measure-theoretic existence assumption. -/
theorem finChainLaw_isProbabilityMeasure [MeasurableSpace S]
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    (hμ0 : ∀ t x, 0 ≤ μ t x)
    (hK : ∀ t u x y, 0 ≤ K t u x y)
    (hμ : ∀ t, ∑ x, μ t x = 1)
    (hentrance : ∀ t u y,
      ∑ x, μ t x * K t u x y = μ u y)
    (hrow : ∀ t u x, ∑ y, K t u x y = 1)
    (hchapman : ∀ s t u x z,
      ∑ y, K s t x y * K t u y z = K s u x z)
    {n : ℕ} (times : Fin n → T) :
    MeasureTheory.IsProbabilityMeasure (finChainLaw μ K times) := by
  apply HasSum.isProbabilityMeasure_sum_dirac
  · intro states
    exact chainWeight_nonnegative μ K hμ0 hK _
  · convert hasSum_fintype (fun states : Fin n → S =>
      finChainWeight μ K times states) using 1
    exact (sum_finChainWeight μ K hμ hentrance hrow hchapman times).symm

/-- Minimal probability-law constructor: positivity is required only for the
particular ordered tuple, while normalization uses only stochastic rows. -/
theorem finChainLaw_isProbabilityMeasure_of_weights [MeasurableSpace S]
    (μ : T → S → ℝ) (K : T → T → S → S → ℝ)
    (hμ : ∀ t, ∑ x, μ t x = 1)
    (hrow : ∀ t u x, ∑ y, K t u x y = 1)
    {n : ℕ} (times : Fin n → T)
    (hweight : ∀ states : Fin n → S,
      0 ≤ finChainWeight μ K times states) :
    MeasureTheory.IsProbabilityMeasure (finChainLaw μ K times) := by
  apply HasSum.isProbabilityMeasure_sum_dirac hweight
  convert hasSum_fintype (fun states : Fin n → S =>
    finChainWeight μ K times states) using 1
  exact (sum_finChainWeight_of_rowStochastic μ K hμ hrow times).symm

/-! ## The actual finite-generator transition kernel -/

variable [DecidableEq S]

open NCG.FiniteGeneratorTransitionSemigroup

/-- The two-time kernel associated with a finite generator. -/
def generatorKernel (L : Matrix S S ℝ) (s t : ℝ) (x y : S) : ℝ :=
  transition L (t - s) x y

/-- Every two-time generator kernel has rows summing to one, including at
arbitrary real algebraic time differences. -/
theorem generatorKernel_row_sum
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (s t : ℝ) (x : S) :
    ∑ y, generatorKernel L s t x y = 1 := by
  exact transition_row_sum L hL (t - s) x

/-- Exact Chapman--Kolmogorov identity for the two-time generator kernel. -/
theorem generatorKernel_chapman
    (L : Matrix S S ℝ) (s t u : ℝ) (x z : S) :
    ∑ y, generatorKernel L s t x y * generatorKernel L t u y z =
      generatorKernel L s u x z := by
  have hadd : (t - s) + (u - t) = u - s := by ring
  simp only [generatorKernel]
  rw [← Matrix.mul_apply]
  rw [← transition_add, hadd]

/-- Entrance law obtained by evolving an initial row distribution from time
zero with the actual generator semigroup. -/
def evolvedEntrance (p : S → ℝ) (L : Matrix S S ℝ) (t : ℝ) (y : S) : ℝ :=
  ∑ x, p x * transition L t x y

/-- Semigroup evolution preserves normalization of the entrance law. -/
theorem evolvedEntrance_sum
    (p : S → ℝ) (hp : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (t : ℝ) :
    ∑ y, evolvedEntrance p L t y = 1 := by
  simp only [evolvedEntrance]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [transition_row_sum L hL t]
  simpa using hp

/-- Evolved entrance laws are exactly consistent with every later two-time
generator kernel. -/
theorem evolvedEntrance_consistent
    (p : S → ℝ) (L : Matrix S S ℝ) (t u : ℝ) (y : S) :
    ∑ x, evolvedEntrance p L t x * generatorKernel L t u x y =
      evolvedEntrance p L u y := by
  simp only [evolvedEntrance, generatorKernel]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [← Matrix.mul_apply]
  have htime : t + (u - t) = u := by ring
  rw [← transition_add, htime]

/-- For nonnegative times an evolved nonnegative initial law remains
nonnegative. -/
theorem evolvedEntrance_nonnegative
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    {t : ℝ} (ht : 0 ≤ t) (y : S) :
    0 ≤ evolvedEntrance p L t y := by
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (hp x) (transition_nonnegative L hL ht x y)

/-- A generator transition product is nonnegative along a chronologically
ordered observation list.  No assertion is made for backward time
differences, where a matrix exponential need not be stochastic. -/
theorem tailWeight_generator_nonnegative_of_ordered
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L) :
    ∀ (s : ℝ) (x : S) (xs : List (ℝ × S)),
      xs.Pairwise (fun a b => a.1 ≤ b.1) →
      (∀ q ∈ xs, s ≤ q.1) →
      0 ≤ tailWeight (generatorKernel L) s x xs := by
  intro s x xs
  induction xs generalizing s x with
  | nil =>
      intro _ _
      simp [tailWeight]
  | cons uy ys ih =>
      rcases uy with ⟨u, y⟩
      intro hordered hafter
      rw [List.pairwise_cons] at hordered
      simp only [tailWeight]
      apply mul_nonneg
      · exact transition_nonnegative L hL
          (sub_nonneg.mpr (hafter (u, y) (by simp))) x y
      · exact ih u y hordered.2 hordered.1

/-- The complete generator-chain weight is nonnegative on a nonnegative,
chronologically ordered observation list. -/
theorem evolved_generator_chainWeight_nonnegative_of_ordered
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (xs : List (ℝ × S))
    (hordered : xs.Pairwise (fun a b => a.1 ≤ b.1))
    (hnonnegative : ∀ q ∈ xs, 0 ≤ q.1) :
    0 ≤ chainWeight (evolvedEntrance p L) (generatorKernel L) xs := by
  cases xs with
  | nil => simp [chainWeight]
  | cons tx ys =>
      rcases tx with ⟨t, x⟩
      rw [List.pairwise_cons] at hordered
      simp only [chainWeight]
      exact mul_nonneg
        (evolvedEntrance_nonnegative p hp L hL
          (hnonnegative (t, x) (by simp)) x)
        (tailWeight_generator_nonnegative_of_ordered L hL t x ys
          hordered.2 hordered.1)

/-- Ordered nonnegative time tuples give nonnegative atomic weights for the
finite-generator process. -/
theorem evolved_generator_finChainWeight_nonnegative
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    {n : ℕ} (times : Fin n → ℝ)
    (htimes : Monotone times) (htimes0 : ∀ i, 0 ≤ times i)
    (states : Fin n → S) :
    0 ≤ finChainWeight (evolvedEntrance p L) (generatorKernel L)
      times states := by
  apply evolved_generator_chainWeight_nonnegative_of_ordered p hp L hL
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact htimes hij.le
  · intro q hq
    rw [List.mem_ofFn] at hq
    obtain ⟨i, rfl⟩ := hq
    exact htimes0 i

/-- The actual finite-dimensional law of a finite-state generator at an
ordered nonnegative time tuple. -/
def evolvedGeneratorFinChainLaw [MeasurableSpace S]
    (p : S → ℝ) (L : Matrix S S ℝ) {n : ℕ}
    (times : Fin n → ℝ) : MeasureTheory.Measure (Fin n → S) :=
  finChainLaw (evolvedEntrance p L) (generatorKernel L) times

/-- The generator finite-dimensional law is a probability measure, derived
solely from a nonnegative normalized initial law, the generator identities,
and chronological ordering of the observation tuple. -/
theorem evolvedGeneratorFinChainLaw_isProbabilityMeasure
    [MeasurableSpace S]
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp_sum : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    {n : ℕ} (times : Fin n → ℝ)
    (htimes : Monotone times) (htimes0 : ∀ i, 0 ≤ times i) :
    MeasureTheory.IsProbabilityMeasure
      (evolvedGeneratorFinChainLaw p L times) := by
  apply finChainLaw_isProbabilityMeasure_of_weights
    (evolvedEntrance p L) (generatorKernel L)
    (evolvedEntrance_sum p hp_sum L hL) (generatorKernel_row_sum L hL)
  exact evolved_generator_finChainWeight_nonnegative p hp L hL
    times htimes htimes0

/-- Consequently every finite-generator chain weight satisfies exact
one-coordinate marginalization once its entrance family is normalized and
consistent with the transition semigroup. -/
theorem sum_generator_chainWeight_insert_after_prefix
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (μ : ℝ → S → ℝ)
    (hμ : ∀ t, ∑ x, μ t x = 1)
    (hentrance : ∀ t u y,
      ∑ x, μ t x * generatorKernel L t u x y = μ u y)
    (pre : List (ℝ × S)) (t : ℝ) (suffix : List (ℝ × S)) :
    (∑ x, chainWeight μ (generatorKernel L)
      (pre ++ (t, x) :: suffix)) =
      chainWeight μ (generatorKernel L) (pre ++ suffix) := by
  exact sum_chainWeight_insert_after_prefix μ (generatorKernel L)
    hμ hentrance (generatorKernel_row_sum L hL)
    (generatorKernel_chapman L) pre t suffix

/-- The canonical generator-evolved entrance family needs no additional
consistency assumption: exact one-coordinate marginalization follows solely
from initial normalization and the generator laws. -/
theorem sum_evolved_generator_chainWeight_insert_after_prefix
    (p : S → ℝ) (hp : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (pre : List (ℝ × S)) (t : ℝ) (suffix : List (ℝ × S)) :
    (∑ x, chainWeight (evolvedEntrance p L) (generatorKernel L)
      (pre ++ (t, x) :: suffix)) =
      chainWeight (evolvedEntrance p L) (generatorKernel L)
        (pre ++ suffix) := by
  exact sum_generator_chainWeight_insert_after_prefix L hL
    (evolvedEntrance p L) (evolvedEntrance_sum p hp L hL)
    (evolvedEntrance_consistent p L) pre t suffix

/-- The canonical generator weights marginalize at an arbitrary coordinate
of a finite ordered tuple. -/
theorem sum_evolved_generator_finChainWeight_insertNth
    (p₀ : S → ℝ) (hp₀ : ∑ x, p₀ x = 1)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    {n : ℕ} (times : Fin (n + 1) → ℝ) (p : Fin (n + 1))
    (states : Fin n → S) :
    (∑ x, finChainWeight (evolvedEntrance p₀ L) (generatorKernel L)
      times (p.insertNth x states)) =
      finChainWeight (evolvedEntrance p₀ L) (generatorKernel L)
        (p.removeNth times) states := by
  exact sum_finChainWeight_insertNth
    (evolvedEntrance p₀ L) (generatorKernel L)
    (evolvedEntrance_sum p₀ hp₀ L hL)
    (evolvedEntrance_consistent p₀ L)
    (generatorKernel_row_sum L hL) (generatorKernel_chapman L)
    times p states

/-- Removing any observation coordinate from an ordered generator chain law
is exactly the pushforward under the corresponding tuple projection. -/
theorem evolvedGeneratorFinChainLaw_map_removeNth
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (p₀ : S → ℝ) (hp₀_nonneg : ∀ x, 0 ≤ p₀ x)
    (hp₀_sum : ∑ x, p₀ x = 1)
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    {n : ℕ} (times : Fin (n + 1) → ℝ)
    (htimes : Monotone times) (htimes0 : ∀ i, 0 ≤ times i)
    (p : Fin (n + 1)) :
    evolvedGeneratorFinChainLaw p₀ L (p.removeNth times) =
      MeasureTheory.Measure.map (p.removeNth ·)
        (evolvedGeneratorFinChainLaw p₀ L times) := by
  apply finChainLaw_map_removeNth
  · exact evolved_generator_finChainWeight_nonnegative
      p₀ hp₀_nonneg L hL times htimes htimes0
  · exact sum_evolved_generator_finChainWeight_insertNth
      p₀ hp₀_sum L hL times p

end NCG.FiniteOrderedMarkovMarginal
