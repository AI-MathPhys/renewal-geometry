/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteRecurrenceAndPredictiveCarriers

/-!
# Canonical obstruction-return graph

Exact finite encoding of `def:GT-source-stopping-packet` and
`thm:GT-obstruction-return-graph` (GW.1) as a Myhill–Nerode quotient.

A stopping packet is a finite set of stopping records `V`, stop-to-stop
cylinders `E` acting partially (`step v e : Option V`, `none` when the
cylinder is not admitted from `v`), terminal queries `query : V → Q`, and a
terminal basin `B`.  The complete future signature of a record is the map
`w ↦ (run v w).map query` on all stop-words.

* `futureEquiv` is future equivalence (equal complete signatures);
* `futureEquiv_step` (right congruence): equivalent records have equivalent
  (or simultaneously inadmissible) successors, so source, target and
  concatenation descend to the quotient `ObGraph` (`descendStep`);
* `ObGraph` is future separated (`obGraph_separated`) and is the unique
  coarsest record sufficient for the declared queries: any record map
  through which all signatures factor descends uniquely and surjectively
  (`obGraph_coarsest`);
* backward signature refinement: `depthEquiv n` (equality of signatures on
  words of length `≤ n`) refines by one letter per round
  (`depthEquiv_succ_iff`), every strict round shrinks the finite relation
  (`depthEquiv_antitone`, `exists_stable_depth`), and stability at depth `n`
  reconstructs future equivalence (`depthEquiv_stable_eq`);
* unread refinements do not enlarge the graph:
  `FiniteRecurrenceAndPredictiveCarriers.unread_refinement_same_future_quotient`.
-/

namespace NCG
namespace ObstructionReturnGraph

variable {V E Q : Type*}

/-- Run a stop-word from a record (partial, letters in list order). -/
def run (step : V → E → Option V) : V → List E → Option V
  | v, [] => some v
  | v, e :: w => (step v e).bind fun v' => run step v' w

theorem run_nil (step : V → E → Option V) (v : V) : run step v [] = some v := rfl

theorem run_cons (step : V → E → Option V) (v : V) (e : E) (w : List E) :
    run step v (e :: w) = (step v e).bind fun v' => run step v' w := rfl

/-- The complete future signature of a record. -/
def signature (step : V → E → Option V) (query : V → Q) (v : V) : List E → Option Q :=
  fun w => (run step v w).map query

/-- The depth-`n` signature: words of length `≤ n`. -/
def depthSignature (step : V → E → Option V) (query : V → Q) (n : ℕ) (v : V) :
    {w : List E // w.length ≤ n} → Option Q :=
  fun w => (run step v w.1).map query

/-- Future equivalence: equal complete signatures. -/
def futureEquiv (step : V → E → Option V) (query : V → Q) : Setoid V :=
  Setoid.ker (signature step query)

/-- Depth-`n` equivalence. -/
def depthEquiv (step : V → E → Option V) (query : V → Q) (n : ℕ) : Setoid V :=
  Setoid.ker (depthSignature step query n)

theorem futureEquiv_iff (step : V → E → Option V) (query : V → Q) (v v' : V) :
    futureEquiv step query v v' ↔ ∀ w, (run step v w).map query = (run step v' w).map query := by
  change signature step query v = signature step query v' ↔ _
  exact funext_iff

theorem depthEquiv_iff (step : V → E → Option V) (query : V → Q) (n : ℕ) (v v' : V) :
    depthEquiv step query n v v' ↔
      ∀ w : List E, w.length ≤ n → (run step v w).map query = (run step v' w).map query := by
  change depthSignature step query n v = depthSignature step query n v' ↔ _
  rw [funext_iff]
  constructor
  · intro h w hw; exact h ⟨w, hw⟩
  · intro h w; exact h w.1 w.2

/-- **Right congruence**: future-equivalent records have simultaneously
admitted cylinders with future-equivalent targets. -/
theorem futureEquiv_step (step : V → E → Option V) (query : V → Q) {v v' : V}
    (h : futureEquiv step query v v') (e : E) :
    (step v e = none ∧ step v' e = none) ∨
      ∃ u u', step v e = some u ∧ step v' e = some u' ∧ futureEquiv step query u u' := by
  rw [futureEquiv_iff] at h
  have h0 := h [e]
  simp only [run_cons, run_nil] at h0
  rcases hu : step v e with _ | u <;> rcases hu' : step v' e with _ | u'
  · exact Or.inl ⟨rfl, rfl⟩
  · rw [hu, hu'] at h0; simp at h0
  · rw [hu, hu'] at h0; simp at h0
  · refine Or.inr ⟨u, u', rfl, rfl, ?_⟩
    rw [futureEquiv_iff]
    intro w
    have := h (e :: w)
    simp only [run_cons, hu, hu', Option.bind_some] at this
    exact this

/-- The canonical obstruction-return graph: vertices are future classes. -/
def ObGraph (step : V → E → Option V) (query : V → Q) : Type _ :=
  Quotient (futureEquiv step query)

/-- The class of a record. -/
def obClass (step : V → E → Option V) (query : V → Q) (v : V) : ObGraph step query :=
  Quotient.mk (futureEquiv step query) v

/-- Descended (partial) cylinder action on classes. -/
def descendStep (step : V → E → Option V) (query : V → Q) :
    ObGraph step query → E → Option (ObGraph step query) :=
  fun c e => Quotient.lift (fun v => (step v e).map (obClass step query)) (by
    intro v v' hvv'
    rcases futureEquiv_step step query hvv' e with ⟨h1, h2⟩ | ⟨u, u', h1, h2, huu'⟩
    · rw [h1, h2]
    · rw [h1, h2]
      simp only [Option.map_some]
      exact congrArg some (Quotient.sound huu')) c

theorem descendStep_class (step : V → E → Option V) (query : V → Q) (v : V) (e : E) :
    descendStep step query (obClass step query v) e = (step v e).map (obClass step query) := rfl

/-- Descended terminal query. -/
def descendQuery (step : V → E → Option V) (query : V → Q) : ObGraph step query → Q :=
  Quotient.lift query (by
    intro v v' h
    have := (futureEquiv_iff step query v v').mp h []
    simpa [run_nil] using this)

/-- The descended basin. -/
def descendBasin (step : V → E → Option V) (query : V → Q) (B : Set V) :
    Set (ObGraph step query) :=
  obClass step query '' B

/-- **Future separation**: distinct classes have distinct complete signatures. -/
theorem obGraph_separated (step : V → E → Option V) (query : V → Q) (v v' : V) :
    obClass step query v = obClass step query v' ↔
      signature step query v = signature step query v' :=
  Quotient.eq

/-- **Coarsest sufficient record**: any record map `q` through which every
signature factors descends uniquely and surjectively onto the graph. -/
theorem obGraph_coarsest {Z : Type*} (step : V → E → Option V) (query : V → Q) (q : V → Z)
    (hq : ∀ v v', q v = q v' → signature step query v = signature step query v') :
    ∃! d : Set.range q → ObGraph step query, ∀ v, d ⟨q v, v, rfl⟩ = obClass step query v := by
  classical
  refine ⟨fun z => obClass step query (Classical.choose z.2), ?_, ?_⟩
  · intro v
    apply Quotient.sound
    exact hq _ _ (Classical.choose_spec (⟨v, rfl⟩ : q v ∈ Set.range q))
  · intro d hd
    funext z
    obtain ⟨w, hw⟩ := z.2
    have hz : z = ⟨q w, w, rfl⟩ := Subtype.ext hw.symm
    subst hz
    rw [hd w]
    apply Quotient.sound
    exact (hq _ _ (Classical.choose_spec (⟨w, rfl⟩ : q w ∈ Set.range q))).symm

theorem obGraph_coarsest_surjective {Z : Type*} (step : V → E → Option V) (query : V → Q)
    (q : V → Z) (d : Set.range q → ObGraph step query)
    (hd : ∀ v, d ⟨q v, v, rfl⟩ = obClass step query v) : Function.Surjective d := by
  intro c
  induction c using Quotient.inductionOn with
  | h v => exact ⟨⟨q v, v, rfl⟩, hd v⟩

/-! ### Backward signature refinement -/

/-- Depth-`0` equivalence is the immediate query partition. -/
theorem depthEquiv_zero_iff (step : V → E → Option V) (query : V → Q) (v v' : V) :
    depthEquiv step query 0 v v' ↔ query v = query v' := by
  rw [depthEquiv_iff]
  constructor
  · intro h
    have := h [] (by simp)
    simpa [run_nil] using this
  · intro h w hw
    have hnil : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)
    subst hnil
    simp [run_nil, h]

/-- **One refinement round**: depth-`(n+1)` equivalence is depth-`n`
equivalence together with depth-`n` equivalence of all one-cylinder
successors. -/
theorem depthEquiv_succ_iff (step : V → E → Option V) (query : V → Q) (n : ℕ) (v v' : V) :
    depthEquiv step query (n + 1) v v' ↔
      depthEquiv step query n v v' ∧
        ∀ e, (step v e = none ∧ step v' e = none) ∨
          ∃ u u', step v e = some u ∧ step v' e = some u' ∧ depthEquiv step query n u u' := by
  simp only [depthEquiv_iff]
  constructor
  · intro h
    refine ⟨fun w hw => h w (by omega), fun e => ?_⟩
    have h0 := h [e] (by simp)
    simp only [run_cons, run_nil] at h0
    rcases hu : step v e with _ | u <;> rcases hu' : step v' e with _ | u'
    · exact Or.inl ⟨rfl, rfl⟩
    · rw [hu, hu'] at h0; simp at h0
    · rw [hu, hu'] at h0; simp at h0
    · refine Or.inr ⟨u, u', rfl, rfl, fun w hw => ?_⟩
      have := h (e :: w) (by simp; omega)
      simp only [run_cons, hu, hu', Option.bind_some] at this
      exact this
  · rintro ⟨h0, hstep⟩ w hw
    cases w with
    | nil => exact h0 [] (by simp)
    | cons e w' =>
      simp only [run_cons]
      rcases hstep e with ⟨h1, h2⟩ | ⟨u, u', h1, h2, huu'⟩
      · rw [h1, h2]
      · rw [h1, h2]
        simp only [Option.bind_some]
        exact huu' w' (by simp at hw; omega)

/-- The refinement chain is decreasing (finer with depth). -/
theorem depthEquiv_antitone (step : V → E → Option V) (query : V → Q) {m n : ℕ} (hmn : m ≤ n)
    (v v' : V) (h : depthEquiv step query n v v') : depthEquiv step query m v v' := by
  rw [depthEquiv_iff] at h ⊢
  intro w hw
  exact h w (le_trans hw hmn)

/-- Future equivalence is the intersection of all depth equivalences. -/
theorem futureEquiv_iff_forall_depth (step : V → E → Option V) (query : V → Q) (v v' : V) :
    futureEquiv step query v v' ↔ ∀ n, depthEquiv step query n v v' := by
  rw [futureEquiv_iff]
  simp only [depthEquiv_iff]
  constructor
  · intro h n w _; exact h w
  · intro h w; exact h w.length w le_rfl

/-- **Stability reconstructs future equivalence**: if depth `n` and depth
`n + 1` agree, then depth `n` agrees with every deeper depth, hence with
future equivalence. -/
theorem depthEquiv_stable_eq (step : V → E → Option V) (query : V → Q) (n : ℕ)
    (hstable : ∀ v v', depthEquiv step query n v v' → depthEquiv step query (n + 1) v v') :
    ∀ v v', depthEquiv step query n v v' ↔ futureEquiv step query v v' := by
  have hall : ∀ m, n ≤ m → ∀ v v', depthEquiv step query n v v' → depthEquiv step query m v v' := by
    intro m hm
    induction m with
    | zero =>
      intro v v' h
      exact depthEquiv_antitone step query (Nat.zero_le n) v v' h
    | succ m ih =>
      intro v v' h
      rcases Nat.lt_or_ge m n with hlt | hge
      · have : n = m + 1 := by omega
        subst this; exact h
      · have hm' := ih hge v v' h
        -- one more refinement round: successors are depth-`m` equivalent by induction
        rw [depthEquiv_succ_iff]
        refine ⟨hm', fun e => ?_⟩
        have hn1 := hstable v v' h
        rw [depthEquiv_succ_iff] at hn1
        rcases hn1.2 e with ⟨h1, h2⟩ | ⟨u, u', h1, h2, huu'⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨u, u', h1, h2, ih hge u u' huu'⟩
  intro v v'
  constructor
  · intro h
    rw [futureEquiv_iff_forall_depth]
    intro m
    rcases Nat.lt_or_ge m n with hlt | hge
    · exact depthEquiv_antitone step query hlt.le v v' h
    · exact hall m hge v v' h
  · intro h
    exact (futureEquiv_iff_forall_depth step query v v').mp h n

set_option linter.unusedDecidableInType false in
/-- **Termination**: on a finite packet the refinement chain stabilizes within
`|V|²` rounds (each strict round removes a related pair). -/
theorem exists_stable_depth [Fintype V] [DecidableEq V] (step : V → E → Option V)
    (query : V → Q) [∀ n v v', Decidable (depthEquiv step query n v v')] :
    ∃ n ≤ Fintype.card V * Fintype.card V,
      ∀ v v', depthEquiv step query n v v' → depthEquiv step query (n + 1) v v' := by
  classical
  -- the relation at depth `n` as a finset of pairs
  let rel : ℕ → Finset (V × V) := fun n =>
    Finset.univ.filter fun p => depthEquiv step query n p.1 p.2
  have hanti : ∀ n, rel (n + 1) ⊆ rel n := by
    intro n p hp
    simp only [rel, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact depthEquiv_antitone step query (Nat.le_succ n) _ _ hp
  by_contra hcon
  push Not at hcon
  have hstrict : ∀ n ≤ Fintype.card V * Fintype.card V, (rel (n + 1)).card < (rel n).card := by
    intro n hn
    obtain ⟨v, v', hvv', hnot⟩ := hcon n hn
    refine Finset.card_lt_card ⟨hanti n, fun hsub => hnot ?_⟩
    have hmem : (v, v') ∈ rel n := by
      simp only [rel, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hvv'
    have := hsub hmem
    simpa [rel] using this
  have hdrop : ∀ k, k ≤ Fintype.card V * Fintype.card V + 1 →
      (rel k).card + k ≤ Fintype.card V * Fintype.card V := by
    intro k
    induction k with
    | zero =>
      intro _
      have := Finset.card_le_univ (rel 0)
      simpa [Fintype.card_prod] using this
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hstrict k (by omega)
      omega
  have := hdrop (Fintype.card V * Fintype.card V + 1) le_rfl
  omega

end ObstructionReturnGraph
end NCG
