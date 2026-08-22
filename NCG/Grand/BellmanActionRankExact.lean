/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Bellman amortization and the physical action rank

Exact encoding of `thm:GT-Bellman-action-rank` (GW.5–GW.8) on a finite directed
graph with source/target maps `s t : E → V` and a scalar edge current `c`.

* `Walk s t a b es`: the edge list `es` is a directed walk from `a` to `b`;
* `exists_potential` (GW.5 ⇒ GW.6): if every closed walk has mean current at
  least `η` (`η * length ≤ ∑ c`), then there is a vertex potential `h` with
  `c e + h (s e) - h (t e) ≥ η` on every edge.  The potential is the infimum of
  the `(c - η)`-weight over all walks ending at the vertex; the infimum is finite
  because closed sub-walks can be spliced out without increasing the weight
  (`exists_short_walk`), so only walks of length `≤ |V|` matter;
* `lyapunov_decrease` (GW.7): along a retained history with
  `A (j+1) ≤ A j - c (e j)`, `Ψ j = A j + h (v j)` decreases by at least `η`;
* `rank_nonneg` / `rank_strict_decrease` (GW.8): the ceiling rank
  `R j = ⌈(Ψ j - A_* - min h) / η⌉` is natural-valued and strictly decreasing.
-/

open Finset

namespace NCG
namespace BellmanActionRank

set_option linter.unusedFintypeInType false

variable {V E : Type*}

/-- Directed walks: `Walk s t a b es` means the edge list `es` runs from `a` to `b`. -/
inductive Walk (s t : E → V) : V → V → List E → Prop
  | nil (a : V) : Walk s t a a []
  | cons {a b c : V} (e : E) (hs : s e = a) (ht : t e = b) {es : List E}
      (h : Walk s t b c es) : Walk s t a c (e :: es)

variable {s t : E → V}

theorem Walk.append {a b c : V} {es es' : List E} (h : Walk s t a b es)
    (h' : Walk s t b c es') : Walk s t a c (es ++ es') := by
  induction h with
  | nil => simpa using h'
  | cons e hs ht _ ih => exact Walk.cons e hs ht (ih h')

theorem Walk.split {a c : V} (es₁ : List E) {es₂ : List E}
    (h : Walk s t a c (es₁ ++ es₂)) : ∃ b, Walk s t a b es₁ ∧ Walk s t b c es₂ := by
  induction es₁ generalizing a with
  | nil => exact ⟨a, Walk.nil a, by simpa using h⟩
  | cons e es ih =>
    rw [List.cons_append] at h
    cases h with
    | cons _ hs ht h' =>
      obtain ⟨b, hb₁, hb₂⟩ := ih h'
      exact ⟨b, Walk.cons e hs ht hb₁, hb₂⟩

theorem Walk.end_unique {a b b' : V} {es : List E} (h : Walk s t a b es)
    (h' : Walk s t a b' es) : b = b' := by
  induction h generalizing b' with
  | nil => cases h'; rfl
  | cons e hs ht _ ih =>
    cases h' with
    | cons _ hs' ht' h'' =>
      rw [← ht', ht] at h''
      exact ih h''

theorem Walk.single {a b : V} {e : E} (hs : s e = a) (ht : t e = b) :
    Walk s t a b [e] := Walk.cons e hs ht (Walk.nil b)

/-- The weight of an edge list. -/
def weight (w : E → ℝ) (es : List E) : ℝ := (es.map w).sum

theorem weight_append (w : E → ℝ) (es es' : List E) :
    weight w (es ++ es') = weight w es + weight w es' := by
  simp [weight]

theorem weight_single (w : E → ℝ) (e : E) : weight w [e] = w e := by simp [weight]

theorem weight_nil (w : E → ℝ) : weight w [] = 0 := by simp [weight]

/-- `∑ (c - η) = ∑ c - η · length`. -/
theorem weight_sub_const (c : E → ℝ) (η : ℝ) (es : List E) :
    weight (fun e => c e - η) es = weight c es - η * es.length := by
  induction es with
  | nil => simp [weight]
  | cons e es ih =>
    simp only [weight, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-- A crude lower bound for the weight of a list of bounded length. -/
theorem weight_ge_of_length_le [Fintype E] (w : E → ℝ) (es : List E) :
    -(es.length * ∑ e, |w e|) ≤ weight w es := by
  induction es with
  | nil => simp [weight]
  | cons e es ih =>
    simp only [weight, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    have h1 : -(∑ e', |w e'|) ≤ w e := by
      have : |w e| ≤ ∑ e', |w e'| := single_le_sum (fun e' _ => abs_nonneg (w e')) (mem_univ e)
      linarith [neg_abs_le (w e)]
    push_cast
    nlinarith [ih, h1]

section cycles

variable (s t)

/-- **(GW.5)**: every closed walk has mean current at least `η`. -/
def MeanCycleFloor (c : E → ℝ) (η : ℝ) : Prop :=
  ∀ v (es : List E), Walk s t v v es → η * es.length ≤ weight c es

variable {s t}

/-- Closed walks have nonnegative `(c - η)`-weight under (GW.5). -/
theorem closed_weight_nonneg {c : E → ℝ} {η : ℝ} (hc : MeanCycleFloor s t c η) {v : V}
    {es : List E} (h : Walk s t v v es) : 0 ≤ weight (fun e => c e - η) es := by
  rw [weight_sub_const]
  linarith [hc v es h]

/-- **Cycle splicing**: any walk has a walk with the same endpoints, length at most
`|V|`, and no larger `(c - η)`-weight. -/
theorem exists_short_walk [Fintype V] {c : E → ℝ} {η : ℝ} (hc : MeanCycleFloor s t c η) {a b : V}
    (es : List E) (h : Walk s t a b es) :
    ∃ es' : List E, Walk s t a b es' ∧ es'.length ≤ Fintype.card V ∧
      weight (fun e => c e - η) es' ≤ weight (fun e => c e - η) es := by
  suffices H : ∀ n, ∀ (a b : V) (es : List E), es.length = n → Walk s t a b es →
      ∃ es' : List E, Walk s t a b es' ∧ es'.length ≤ Fintype.card V ∧
        weight (fun e => c e - η) es' ≤ weight (fun e => c e - η) es from H _ a b es rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b es hlen h
  by_cases hn : n ≤ Fintype.card V
  · exact ⟨es, h, by rw [hlen]; exact hn, le_rfl⟩
  rw [not_le] at hn
  have hsplit : ∀ i : Fin (n + 1),
      ∃ v, Walk s t a v (es.take i) ∧ Walk s t v b (es.drop i) := fun i =>
    Walk.split (es.take i) (by rw [List.take_append_drop]; exact h)
  choose vert hvert using hsplit
  obtain ⟨i, j, hij, hv⟩ := Fintype.exists_ne_map_eq_of_card_lt vert
    (by simp only [Fintype.card_fin]; omega)
  have key : ∀ i j : Fin (n + 1), i < j → vert i = vert j →
      ∃ es' : List E, Walk s t a b es' ∧ es'.length < n ∧
        weight (fun e => c e - η) es' ≤ weight (fun e => c e - η) es := by
    intro i j hlt hv
    have hij' : (i : ℕ) < j := hlt
    have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
    have hsplitj : es.take j = es.take i ++ (es.take j).drop i := by
      conv_lhs => rw [← List.take_append_drop (i : ℕ) (es.take (j : ℕ))]
      rw [List.take_take, min_eq_left hij'.le]
    obtain ⟨b', hb'₁, hb'₂⟩ := Walk.split (es.take i) (hsplitj ▸ (hvert j).1)
    have hb' : b' = vert i := Walk.end_unique hb'₁ (hvert i).1
    subst hb'
    rw [← hv] at hb'₂
    refine ⟨es.take i ++ es.drop j, (hvert i).1.append (by rw [hv]; exact (hvert j).2), ?_, ?_⟩
    · rw [List.length_append, List.length_take, List.length_drop, hlen]
      omega
    · have hW : weight (fun e => c e - η) es
          = weight (fun e => c e - η) (es.take i) + weight (fun e => c e - η) ((es.take j).drop i)
            + weight (fun e => c e - η) (es.drop j) := by
        conv_lhs => rw [← List.take_append_drop (j : ℕ) es, hsplitj]
        rw [weight_append, weight_append]
      rw [weight_append, hW]
      linarith [closed_weight_nonneg hc hb'₂]
  obtain ⟨es', hw', hlen', hW'⟩ : ∃ es' : List E, Walk s t a b es' ∧ es'.length < n ∧
      weight (fun e => c e - η) es' ≤ weight (fun e => c e - η) es := by
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact key i j hlt hv
    · exact key j i hlt hv.symm
  obtain ⟨es'', h1, h2, h3⟩ := ih es'.length hlen' a b es' rfl hw'
  exact ⟨es'', h1, h2, h3.trans hW'⟩

end cycles

/-! ### The Bellman potential -/

section potential

variable (s t)

/-- The set of `(c - η)`-weights of walks ending at `v`. -/
def arrivalWeights (c : E → ℝ) (η : ℝ) (v : V) : Set ℝ :=
  {x | ∃ (a : V) (es : List E), Walk s t a v es ∧ x = weight (fun e => c e - η) es}

/-- **(GW.6)**: the Bellman potential `h(v) = inf { ∑ (c - η) over walks ending at v }`. -/
noncomputable def potential (c : E → ℝ) (η : ℝ) (v : V) : ℝ :=
  sInf (arrivalWeights s t c η v)

variable {s t}

theorem arrivalWeights_nonempty (c : E → ℝ) (η : ℝ) (v : V) :
    (arrivalWeights s t c η v).Nonempty :=
  ⟨0, v, [], Walk.nil v, (weight_nil _).symm⟩

theorem arrivalWeights_bddBelow [Fintype V] [Fintype E] {c : E → ℝ} {η : ℝ}
    (hc : MeanCycleFloor s t c η) (v : V) :
    BddBelow (arrivalWeights s t c η v) := by
  refine ⟨-(Fintype.card V * ∑ e, |c e - η|), ?_⟩
  rintro x ⟨a, es, hw, rfl⟩
  obtain ⟨es', -, hlen, hW⟩ := exists_short_walk hc es hw
  have h1 := weight_ge_of_length_le (fun e => c e - η) es'
  have h2 : (es'.length : ℝ) * ∑ e, |c e - η| ≤ Fintype.card V * ∑ e, |c e - η| := by
    gcongr
  linarith

theorem potential_le_weight [Fintype V] [Fintype E] {c : E → ℝ} {η : ℝ}
    (hc : MeanCycleFloor s t c η) {a v : V}
    {es : List E} (h : Walk s t a v es) :
    potential s t c η v ≤ weight (fun e => c e - η) es :=
  csInf_le (arrivalWeights_bddBelow hc v) ⟨a, es, h, rfl⟩

/-- **(GW.6)**: the reduced current is at least `η` on every edge. -/
theorem potential_edge [Fintype V] [Fintype E] {c : E → ℝ} {η : ℝ}
    (hc : MeanCycleFloor s t c η) (e : E) :
    η ≤ c e + potential s t c η (s e) - potential s t c η (t e) := by
  have key : potential s t c η (t e) - (c e - η) ≤ potential s t c η (s e) := by
    refine le_csInf (arrivalWeights_nonempty c η (s e)) ?_
    rintro x ⟨a, es, hw, rfl⟩
    have := potential_le_weight hc (hw.append (Walk.single (s := s) (t := t) rfl rfl))
    rw [weight_append, weight_single] at this
    linarith
  linarith

/-- **(GW.5 ⇒ GW.6)**: existence of a vertex potential with reduced current `≥ η`. -/
theorem exists_potential [Fintype V] [Fintype E] {c : E → ℝ} {η : ℝ}
    (hc : MeanCycleFloor s t c η) :
    ∃ h : V → ℝ, ∀ e, η ≤ c e + h (s e) - h (t e) :=
  ⟨potential s t c η, potential_edge hc⟩

end potential

/-! ### Lyapunov decrease and the action rank (GW.7–GW.8) -/

section rank

variable {c : E → ℝ} {η : ℝ} {h : V → ℝ}

/-- **(GW.7)**: if `h` satisfies (GW.6) and the source action pays the current along
the retained history, then `Ψ j = A j + h (v j)` drops by at least `η` per step. -/
theorem lyapunov_decrease (hpot : ∀ e, η ≤ c e + h (s e) - h (t e)) (A : ℕ → ℝ)
    (v : ℕ → V) (e : ℕ → E) (hs : ∀ j, s (e j) = v j) (ht : ∀ j, t (e j) = v (j + 1))
    (hA : ∀ j, A (j + 1) ≤ A j - c (e j)) (j : ℕ) :
    A (j + 1) + h (v (j + 1)) ≤ A j + h (v j) - η := by
  have := hpot (e j)
  rw [hs j, ht j] at this
  linarith [hA j]

/-- **(GW.8)**: the ceiling rank `R j = ⌈(Ψ j - A_* - min h) / η⌉`. -/
noncomputable def rank [Fintype V] [Nonempty V] (h : V → ℝ) (η A_star : ℝ) (A : ℕ → ℝ)
    (v : ℕ → V) (j : ℕ) : ℤ :=
  ⌈(A j + h (v j) - A_star - (univ.inf' univ_nonempty h)) / η⌉

/-- **(GW.8)**: the rank is natural-valued on the retained history. -/
theorem rank_nonneg [Fintype V] [Nonempty V] (hη : 0 < η) {A_star : ℝ} (A : ℕ → ℝ) (v : ℕ → V)
    (hlow : ∀ j, A_star ≤ A j) (j : ℕ) : 0 ≤ rank h η A_star A v j := by
  unfold rank
  apply Int.ceil_nonneg
  apply div_nonneg _ hη.le
  have := inf'_le h (mem_univ (v j))
  linarith [hlow j]

/-- **(GW.8)**: the rank strictly decreases at every internal transition. -/
theorem rank_strict_decrease [Fintype V] [Nonempty V] (hη : 0 < η)
    (hpot : ∀ e, η ≤ c e + h (s e) - h (t e)) {A_star : ℝ} (A : ℕ → ℝ) (v : ℕ → V)
    (e : ℕ → E) (hs : ∀ j, s (e j) = v j) (ht : ∀ j, t (e j) = v (j + 1))
    (hA : ∀ j, A (j + 1) ≤ A j - c (e j)) (j : ℕ) :
    rank h η A_star A v (j + 1) + 1 ≤ rank h η A_star A v j := by
  unfold rank
  have hd := lyapunov_decrease hpot A v e hs ht hA j
  set m := univ.inf' univ_nonempty h
  have : (A (j + 1) + h (v (j + 1)) - A_star - m) / η
      ≤ (A j + h (v j) - A_star - m) / η - 1 := by
    rw [div_sub_one hη.ne', div_le_div_iff_of_pos_right hη]
    linarith
  have := Int.ceil_mono this
  rw [Int.ceil_sub_one] at this
  omega

end rank

end BellmanActionRank
end NCG
