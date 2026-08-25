/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The accepted weighted Hall theorem

Exact formalization for `thm:accepted-weighted-Hall` (AO.3–AO.4).

* **AO.3** (`accepted_weighted_Hall`, first clause): an admitted coupling with
  marginals `α`, `β` supported on the admitted edge set `E` exists iff
  `α(U) ≤ β(N(U))` for every source set `U`;
* **AO.4** (second clause): the maximum transportable mass equals
  `(∑ α) - 𝔥_E(α, β)` where `𝔥_E(α, β) = max_U [α(U) - β(N(U))]₊` is the Hall
  deficiency (`hallDef`; the `∅` term makes the positive part automatic) — a positive
  deficiency is the exact mass no admitted transition can route.

The proof is a self-contained finite max-flow/min-cut argument: sub-couplings form a
compact convex set (`exists_max_subCoupling`); an inductive alternating-reachability
predicate (`Reach`) supports a quantitative augmenting-path lemma (`reach_augment`)
showing every neighbour column of a reachable source is tight at an optimum
(`col_tight_of_reach`); the reachable-set counting identity then pins the optimal
mass to the worst Hall deficit (`optimal_mass_ge` + `mass_le_total_sub_hallDef`).
-/

open Finset

namespace NCG
namespace WeightedHall

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

/-- Total transported mass. -/
def mass (π : S × T → ℝ) : ℝ := ∑ p, π p

/-- A sub-coupling: nonnegative, supported on the admitted edges, with sub-marginals. -/
def SubCoupling (E : Finset (S × T)) (α : S → ℝ) (β : T → ℝ) (π : S × T → ℝ) : Prop :=
  (∀ p, 0 ≤ π p) ∧ (∀ p, p ∉ E → π p = 0) ∧
    (∀ x, ∑ y, π (x, y) ≤ α x) ∧ (∀ y, ∑ x, π (x, y) ≤ β y)

/-- An admitted coupling: exact marginals `α` and `β` on the admitted edges. -/
def IsCoupling (E : Finset (S × T)) (α : S → ℝ) (β : T → ℝ) (π : S × T → ℝ) : Prop :=
  (∀ p, 0 ≤ π p) ∧ (∀ p, p ∉ E → π p = 0) ∧
    (∀ x, ∑ y, π (x, y) = α x) ∧ (∀ y, ∑ x, π (x, y) = β y)

/-- Admitted neighbourhood of a source set. -/
def neigh (E : Finset (S × T)) (U : Finset S) : Finset T :=
  Finset.univ.filter fun y => ∃ x ∈ U, (x, y) ∈ E

/-- The Hall deficiency `max_U [α(U) - β(N(U))]₊` (the `∅` term supplies the positive
part). -/
noncomputable def hallDef (E : Finset (S × T)) (α : S → ℝ) (β : T → ℝ) : ℝ :=
  Finset.sup' Finset.univ.powerset ⟨∅, Finset.empty_mem_powerset _⟩
    fun U => (∑ x ∈ U, α x) - ∑ y ∈ neigh E U, β y

omit [DecidableEq S] [DecidableEq T] in
theorem mass_eq_sum_row (π : S × T → ℝ) : mass π = ∑ x, ∑ y, π (x, y) :=
  Fintype.sum_prod_type _

omit [DecidableEq S] [DecidableEq T] in
theorem mass_eq_sum_col (π : S × T → ℝ) : mass π = ∑ y, ∑ x, π (x, y) := by
  rw [mass_eq_sum_row, Finset.sum_comm]

theorem hallDef_nonneg (E : Finset (S × T)) (α : S → ℝ) (β : T → ℝ) :
    0 ≤ hallDef E α β := by
  have h := Finset.le_sup'
    (fun U => (∑ x ∈ U, α x) - ∑ y ∈ neigh E U, β y)
    (Finset.empty_mem_powerset (Finset.univ (α := S)))
  have hneigh : neigh E (∅ : Finset S) = ∅ := by
    rw [neigh]
    refine Finset.filter_false_of_mem fun y _ => ?_
    rintro ⟨x, hx, -⟩
    exact absurd hx (Finset.notMem_empty x)
  rw [Finset.sum_empty, hneigh, Finset.sum_empty, sub_zero] at h
  exact h

/-- Rows of sources in `U` are supported inside `neigh E U`. -/
theorem row_sum_eq_neigh {E : Finset (S × T)} {α : S → ℝ} {β : T → ℝ} {π : S × T → ℝ}
    (hsub : SubCoupling E α β π) (U : Finset S) {x : S} (hx : x ∈ U) :
    ∑ y, π (x, y) = ∑ y ∈ neigh E U, π (x, y) := by
  refine (Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_).symm
  refine hsub.2.1 _ fun hE => ?_
  exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hx, hE⟩⟩)

/-- The `U`-rows carry at most the `neigh E U` capacity. -/
theorem sum_row_le_neigh {E : Finset (S × T)} {α : S → ℝ} {β : T → ℝ} {π : S × T → ℝ}
    (hsub : SubCoupling E α β π) (U : Finset S) :
    ∑ x ∈ U, ∑ y, π (x, y) ≤ ∑ y ∈ neigh E U, β y :=
  calc ∑ x ∈ U, ∑ y, π (x, y) = ∑ x ∈ U, ∑ y ∈ neigh E U, π (x, y) :=
        Finset.sum_congr rfl fun _ hx => row_sum_eq_neigh hsub U hx
    _ = ∑ y ∈ neigh E U, ∑ x ∈ U, π (x, y) := Finset.sum_comm
    _ ≤ ∑ y ∈ neigh E U, ∑ x, π (x, y) :=
        Finset.sum_le_sum fun y _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun x _ _ => hsub.1 (x, y)
    _ ≤ ∑ y ∈ neigh E U, β y := Finset.sum_le_sum fun y _ => hsub.2.2.2 y

/-- **Easy direction of AO.4**: every sub-coupling respects every Hall cut. -/
theorem mass_le {E : Finset (S × T)} {α : S → ℝ} {β : T → ℝ} {π : S × T → ℝ}
    (hsub : SubCoupling E α β π) (U : Finset S) :
    mass π ≤ (∑ x, α x) - ((∑ x ∈ U, α x) - ∑ y ∈ neigh E U, β y) := by
  have hsplit : (∑ x ∈ U, ∑ y, π (x, y)) + ∑ x ∈ Uᶜ, ∑ y, π (x, y) = mass π := by
    rw [mass_eq_sum_row]
    exact Finset.sum_add_sum_compl U _
  have h1 := sum_row_le_neigh hsub U
  have h2 : ∑ x ∈ Uᶜ, ∑ y, π (x, y) ≤ ∑ x ∈ Uᶜ, α x :=
    Finset.sum_le_sum fun x _ => hsub.2.2.1 x
  have h3 : (∑ x ∈ U, α x) + ∑ x ∈ Uᶜ, α x = ∑ x, α x :=
    Finset.sum_add_sum_compl U α
  linarith

theorem mass_le_total_sub_hallDef {E : Finset (S × T)} {α : S → ℝ} {β : T → ℝ}
    {π : S × T → ℝ} (hsub : SubCoupling E α β π) :
    mass π ≤ (∑ x, α x) - hallDef E α β := by
  have h : hallDef E α β ≤ (∑ x, α x) - mass π := by
    refine Finset.sup'_le _ _ fun U _ => ?_
    have := mass_le hsub U
    linarith
  linarith

/-! ### Single-entry bumps -/

/-- Add `ε` to the single entry `q`. -/
def bump (π : S × T → ℝ) (q : S × T) (ε : ℝ) : S × T → ℝ :=
  fun p => π p + if p = q then ε else 0

omit [Fintype S] [Fintype T] in
theorem bump_apply_self (π : S × T → ℝ) (q : S × T) (ε : ℝ) :
    bump π q ε q = π q + ε := by simp [bump]

omit [Fintype S] [Fintype T] in
theorem bump_apply_ne (π : S × T → ℝ) (q : S × T) (ε : ℝ) {p : S × T} (h : p ≠ q) :
    bump π q ε p = π p := by simp [bump, h]

omit [Fintype S] in
theorem bump_row (π : S × T → ℝ) (x₀ : S) (y₀ : T) (ε : ℝ) (a : S) :
    ∑ b, bump π (x₀, y₀) ε (a, b)
      = (∑ b, π (a, b)) + if a = x₀ then ε else 0 := by
  simp only [bump]
  rw [Finset.sum_add_distrib]
  congr 1
  by_cases h : a = x₀
  · subst h
    simp
  · simp [h]

omit [Fintype T] in
theorem bump_col (π : S × T → ℝ) (x₀ : S) (y₀ : T) (ε : ℝ) (w : T) :
    ∑ a, bump π (x₀, y₀) ε (a, w)
      = (∑ a, π (a, w)) + if w = y₀ then ε else 0 := by
  simp only [bump]
  rw [Finset.sum_add_distrib]
  congr 1
  by_cases h : w = y₀
  · subst h
    simp
  · simp [h]

theorem bump_mass (π : S × T → ℝ) (q : S × T) (ε : ℝ) :
    mass (bump π q ε) = mass π + ε := by
  simp only [bump, mass]
  rw [Finset.sum_add_distrib]
  congr 1
  simp

/-! ### Alternating reachability and augmentation -/

/-- Alternating reachability from an unsaturated source: forward along admitted
edges, backward along positively loaded entries. -/
inductive Reach (E : Finset (S × T)) (α : S → ℝ) (π : S × T → ℝ) : S → Prop
  | base {x : S} (hslack : ∑ y, π (x, y) < α x) : Reach E α π x
  | step {x x' : S} {y : T} (hx : Reach E α π x) (hE : (x, y) ∈ E)
      (hπ : 0 < π (x', y)) : Reach E α π x'

/-- **Quantitative augmenting lemma**: from a reachable source, `ε` of fresh mass can
be injected into any admitted neighbour column, at total-mass gain exactly `ε`,
without raising any other column, while lowering every entry by at most `C·ε`. -/
theorem reach_augment {E : Finset (S × T)} {α : S → ℝ} {β : T → ℝ} {π : S × T → ℝ}
    (hsub : SubCoupling E α β π) {x : S} (hx : Reach E α π x) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ z : T, (x, z) ∈ E →
      ∃ π' : S × T → ℝ,
        (∀ p, 0 ≤ π' p) ∧ (∀ p, p ∉ E → π' p = 0) ∧
        (∀ a, ∑ b, π' (a, b) ≤ α a) ∧
        (∀ w, w ≠ z → ∑ a, π' (a, w) ≤ ∑ a, π (a, w)) ∧
        (∑ a, π' (a, z) ≤ (∑ a, π (a, z)) + ε) ∧
        mass π' = mass π + ε ∧
        (∀ p, π p - C * ε ≤ π' p) := by
  induction hx with
  | @base x hslack =>
    refine ⟨α x - ∑ y, π (x, y), by linarith, 1, one_pos, ?_⟩
    intro ε hε hεδ z hz
    refine ⟨bump π (x, z) ε, ?_, ?_, ?_, ?_, ?_, bump_mass π (x, z) ε, ?_⟩
    · intro p
      by_cases hp : p = (x, z)
      · rw [hp, bump_apply_self]
        linarith [hsub.1 (x, z)]
      · rw [bump_apply_ne _ _ _ hp]
        exact hsub.1 p
    · intro p hpE
      have hne : p ≠ (x, z) := fun h => hpE (h ▸ hz)
      rw [bump_apply_ne _ _ _ hne]
      exact hsub.2.1 p hpE
    · intro a
      rw [bump_row]
      by_cases ha : a = x
      · subst ha
        rw [if_pos rfl]
        linarith
      · rw [if_neg ha]
        simpa using hsub.2.2.1 a
    · intro w hw
      rw [bump_col, if_neg hw, add_zero]
    · exact le_of_eq (by rw [bump_col, if_pos rfl])
    · intro p
      by_cases hp : p = (x, z)
      · rw [hp, bump_apply_self]
        linarith
      · rw [bump_apply_ne _ _ _ hp]
        linarith
  | @step x x' y hx hE hπ ih =>
    obtain ⟨δ, hδ, C, hC, hgen⟩ := ih
    have hC1 : (0 : ℝ) < C + 1 := by linarith
    refine ⟨min δ (π (x', y) / (C + 1)), lt_min hδ (div_pos hπ hC1),
      C + 1, hC1, ?_⟩
    intro ε hε hεδ z hz
    have hεδ' : ε ≤ δ := hεδ.trans (min_le_left _ _)
    have hεπ : (C + 1) * ε ≤ π (x', y) := by
      have h := hεδ.trans (min_le_right _ _)
      rw [le_div_iff₀ hC1] at h
      linarith
    obtain ⟨π₁, h1nn, h1E, h1row, h1colw, h1coly, h1mass, h1ent⟩ :=
      hgen ε hε hεδ' y hE
    have hEy : (x', y) ∈ E := by
      by_contra hc
      exact absurd (hsub.2.1 _ hc) (ne_of_gt hπ)
    set π₂ := bump π₁ (x', y) (-ε) with hπ₂
    set π' := bump π₂ (x', z) ε with hπ'
    have hval : ∀ p, π' p
        = π₁ p + (if p = (x', y) then -ε else 0) + (if p = (x', z) then ε else 0) := by
      intro p
      simp only [hπ', hπ₂, bump]
    have hrowval : ∀ a, ∑ b, π' (a, b)
        = (∑ b, π₁ (a, b)) + (if a = x' then -ε else 0)
          + (if a = x' then ε else 0) := by
      intro a
      rw [hπ', bump_row, hπ₂, bump_row]
    have hcolval : ∀ w, ∑ a, π' (a, w)
        = (∑ a, π₁ (a, w)) + (if w = y then -ε else 0)
          + (if w = z then ε else 0) := by
      intro w
      rw [hπ', bump_col, hπ₂, bump_col]
    refine ⟨π', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p
      rw [hval p]
      by_cases h1 : p = (x', y) <;> by_cases h2 : p = (x', z)
      · rw [if_pos h1, if_pos h2]
        linarith [h1nn p]
      · rw [if_pos h1, if_neg h2]
        have h3 : π (x', y) - C * ε ≤ π₁ p := by
          rw [h1]
          exact h1ent (x', y)
        linarith
      · rw [if_neg h1, if_pos h2]
        linarith [h1nn p]
      · rw [if_neg h1, if_neg h2]
        simpa using h1nn p
    · intro p hpE
      have hne1 : p ≠ (x', y) := fun h => hpE (h ▸ hEy)
      have hne2 : p ≠ (x', z) := fun h => hpE (h ▸ hz)
      rw [hval p, if_neg hne1, if_neg hne2, h1E p hpE]
      ring
    · intro a
      rw [hrowval a]
      by_cases ha : a = x'
      · rw [if_pos ha, if_pos ha]
        linarith [h1row a]
      · rw [if_neg ha, if_neg ha]
        simpa using h1row a
    · intro w hw
      rw [hcolval w, if_neg hw]
      by_cases hwy : w = y
      · rw [if_pos hwy]
        have h3 : ∑ a, π₁ (a, w) ≤ (∑ a, π (a, w)) + ε := by
          rw [hwy]
          exact h1coly
        linarith
      · rw [if_neg hwy]
        have h3 := h1colw w hwy
        linarith
    · rw [hcolval z, if_pos rfl]
      by_cases hzy : z = y
      · rw [if_pos hzy]
        have h3 : ∑ a, π₁ (a, z) ≤ (∑ a, π (a, z)) + ε := by
          rw [hzy]
          exact h1coly
        linarith
      · rw [if_neg hzy]
        have h3 := h1colw z hzy
        linarith
    · rw [hπ', bump_mass, hπ₂, bump_mass, h1mass]
      ring
    · intro p
      rw [hval p]
      have h3 := h1ent p
      by_cases h1 : p = (x', y) <;> by_cases h2 : p = (x', z)
      · rw [if_pos h1, if_pos h2]
        linarith
      · rw [if_pos h1, if_neg h2]
        linarith
      · rw [if_neg h1, if_pos h2]
        linarith
      · rw [if_neg h1, if_neg h2]
        linarith

/-- At an optimum, every admitted neighbour column of a reachable source is tight. -/
theorem col_tight_of_reach {E : Finset (S × T)} {α : S → ℝ} {β : T → ℝ}
    {π : S × T → ℝ} (hsub : SubCoupling E α β π)
    (hopt : ∀ π', SubCoupling E α β π' → mass π' ≤ mass π)
    {x : S} {z : T} (hx : Reach E α π x) (hE : (x, z) ∈ E) :
    ∑ a, π (a, z) = β z := by
  by_contra hne
  have hlt : ∑ a, π (a, z) < β z := lt_of_le_of_ne (hsub.2.2.2 z) hne
  obtain ⟨δ, hδ, C, _, hgen⟩ := reach_augment hsub hx
  set ε := min δ (β z - ∑ a, π (a, z)) with hε
  have hεpos : 0 < ε := lt_min hδ (by linarith)
  obtain ⟨π', hnn, hoffE, hrow, hcolw, hcolz, hmass, _⟩ :=
    hgen ε hεpos (min_le_left _ _) z hE
  have hsub' : SubCoupling E α β π' := by
    refine ⟨hnn, hoffE, hrow, ?_⟩
    intro w
    by_cases hw : w = z
    · subst hw
      have h2 : ε ≤ β w - ∑ a, π (a, w) := by
        rw [hε]
        exact min_le_right _ _
      linarith [hcolz]
    · exact (hcolw w hw).trans (hsub.2.2.2 w)
  have h := hopt π' hsub'
  rw [hmass] at h
  linarith

/-- **Hard direction of AO.4**: an optimal sub-coupling realizes the worst Hall cut. -/
theorem optimal_mass_ge {E : Finset (S × T)} {α : S → ℝ} {β : T → ℝ}
    {π : S × T → ℝ} (hsub : SubCoupling E α β π)
    (hopt : ∀ π', SubCoupling E α β π' → mass π' ≤ mass π) :
    (∑ x, α x) - hallDef E α β ≤ mass π := by
  classical
  set U : Finset S := Finset.univ.filter (fun x => Reach E α π x) with hU
  have hmemU : ∀ x, x ∈ U ↔ Reach E α π x := by
    intro x
    rw [hU, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hrow_tight : ∀ x, x ∉ U → ∑ y, π (x, y) = α x := by
    intro x hx
    by_contra hne
    exact hx ((hmemU x).mpr (Reach.base (lt_of_le_of_ne (hsub.2.2.1 x) hne)))
  have hcol_tight : ∀ y ∈ neigh E U, ∑ x, π (x, y) = β y := by
    intro y hy
    obtain ⟨x, hxU, hxE⟩ := (Finset.mem_filter.mp hy).2
    exact col_tight_of_reach hsub hopt ((hmemU x).mp hxU) hxE
  have hcross : ∀ x, x ∉ U → ∀ y ∈ neigh E U, π (x, y) = 0 := by
    intro x hx y hy
    by_contra hne
    have hpos : 0 < π (x, y) := lt_of_le_of_ne (hsub.1 _) (Ne.symm hne)
    obtain ⟨x₁, hx₁U, hx₁E⟩ := (Finset.mem_filter.mp hy).2
    exact hx ((hmemU x).mpr (Reach.step ((hmemU x₁).mp hx₁U) hx₁E hpos))
  have hkey : ∑ y ∈ neigh E U, β y = ∑ x ∈ U, ∑ y, π (x, y) :=
    calc ∑ y ∈ neigh E U, β y = ∑ y ∈ neigh E U, ∑ x, π (x, y) :=
          Finset.sum_congr rfl fun y hy => (hcol_tight y hy).symm
      _ = ∑ y ∈ neigh E U, ∑ x ∈ U, π (x, y) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          exact (Finset.sum_subset (Finset.subset_univ _)
            fun x _ hx => hcross x hx y hy).symm
      _ = ∑ x ∈ U, ∑ y ∈ neigh E U, π (x, y) := Finset.sum_comm
      _ = ∑ x ∈ U, ∑ y, π (x, y) :=
          Finset.sum_congr rfl fun _ hx => (row_sum_eq_neigh hsub U hx).symm
  have hmass : mass π = (∑ x ∈ U, ∑ y, π (x, y)) + ∑ x ∈ Uᶜ, α x := by
    rw [mass_eq_sum_row, ← Finset.sum_add_sum_compl U (fun x => ∑ y, π (x, y))]
    congr 1
    refine Finset.sum_congr rfl fun x hx => hrow_tight x ?_
    simpa using hx
  have hU_le : (∑ x ∈ U, α x) - ∑ y ∈ neigh E U, β y ≤ hallDef E α β :=
    Finset.le_sup' (fun V => (∑ x ∈ V, α x) - ∑ y ∈ neigh E V, β y)
      (Finset.mem_powerset.mpr (Finset.subset_univ U))
  have hcompl : (∑ x ∈ U, α x) + ∑ x ∈ Uᶜ, α x = ∑ x, α x :=
    Finset.sum_add_sum_compl U α
  rw [hmass, ← hkey]
  linarith

/-! ### Existence of an optimal sub-coupling -/

theorem isClosed_subCoupling (E : Finset (S × T)) (α : S → ℝ) (β : T → ℝ) :
    IsClosed {π : S × T → ℝ | SubCoupling E α β π} := by
  have h1 : IsClosed {π : S × T → ℝ | ∀ p, 0 ≤ π p} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun p => isClosed_le continuous_const (continuous_apply p)
  have h2 : IsClosed {π : S × T → ℝ | ∀ p, p ∉ E → π p = 0} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun p => ?_
    by_cases hp : p ∈ E
    · have he : {π : S × T → ℝ | p ∉ E → π p = 0} = Set.univ := by
        ext π
        simp [hp]
      rw [he]
      exact isClosed_univ
    · have he : {π : S × T → ℝ | p ∉ E → π p = 0} = {π | π p = 0} := by
        ext π
        simp [hp]
      rw [he]
      exact isClosed_eq (continuous_apply p) continuous_const
  have h3 : IsClosed {π : S × T → ℝ | ∀ x, ∑ y, π (x, y) ≤ α x} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_le
      (continuous_finsetSum _ fun y _ => continuous_apply (x, y)) continuous_const
  have h4 : IsClosed {π : S × T → ℝ | ∀ y, ∑ x, π (x, y) ≤ β y} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun y => isClosed_le
      (continuous_finsetSum _ fun x _ => continuous_apply (x, y)) continuous_const
  have he : {π : S × T → ℝ | SubCoupling E α β π}
      = {π : S × T → ℝ | ∀ p, 0 ≤ π p} ∩ ({π | ∀ p, p ∉ E → π p = 0}
        ∩ ({π | ∀ x, ∑ y, π (x, y) ≤ α x} ∩ {π | ∀ y, ∑ x, π (x, y) ≤ β y})) := by
    ext π
    simp only [SubCoupling, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [he]
  exact h1.inter (h2.inter (h3.inter h4))

theorem exists_max_subCoupling (E : Finset (S × T)) (α : S → ℝ) (β : T → ℝ)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y) :
    ∃ π, SubCoupling E α β π ∧ ∀ π', SubCoupling E α β π' → mass π' ≤ mass π := by
  set K := {π : S × T → ℝ | SubCoupling E α β π} with hK
  have hzero : (fun _ => (0 : ℝ)) ∈ K := by
    refine ⟨fun _ => le_refl 0, fun _ _ => rfl, fun x => ?_, fun y => ?_⟩
    · simpa using hα x
    · simpa using hβ y
  have hsubB : K ⊆ Set.univ.pi fun p : S × T => Set.Icc 0 (β p.2) := by
    intro π hπ
    rw [Set.mem_univ_pi]
    intro p
    refine ⟨hπ.1 p, ?_⟩
    calc π p ≤ ∑ a, π (a, p.2) :=
          Finset.single_le_sum (fun a _ => hπ.1 (a, p.2)) (Finset.mem_univ p.1)
      _ ≤ β p.2 := hπ.2.2.2 p.2
  have hB : IsCompact (Set.univ.pi fun p : S × T => Set.Icc (0 : ℝ) (β p.2)) :=
    isCompact_univ_pi fun p => isCompact_Icc
  have hKcomp : IsCompact K := hB.of_isClosed_subset (isClosed_subCoupling E α β) hsubB
  have hcont : ContinuousOn mass K :=
    (continuous_finsetSum _ fun p _ => continuous_apply p).continuousOn
  obtain ⟨π, hπK, hmax⟩ := hKcomp.exists_isMaxOn ⟨_, hzero⟩ hcont
  exact ⟨π, hπK, fun π' hπ' => hmax hπ'⟩

/-! ### The accepted weighted Hall theorem -/

/-- **Bundle for `thm:accepted-weighted-Hall`** (AO.3 + AO.4): an admitted coupling
exists iff every Hall inequality `α(U) ≤ β(N(U))` holds, and the maximum
transportable mass is exactly `(∑ α) - 𝔥_E(α, β)`. -/
theorem accepted_weighted_Hall (E : Finset (S × T)) (α : S → ℝ) (β : T → ℝ)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y) (htot : ∑ x, α x = ∑ y, β y) :
    ((∃ π, IsCoupling E α β π) ↔
      ∀ U : Finset S, ∑ x ∈ U, α x ≤ ∑ y ∈ neigh E U, β y) ∧
    ∃ π, SubCoupling E α β π ∧ mass π = (∑ x, α x) - hallDef E α β ∧
      ∀ π', SubCoupling E α β π' → mass π' ≤ mass π := by
  obtain ⟨π₀, hπ₀, hopt⟩ := exists_max_subCoupling E α β hα hβ
  have hπ₀mass : mass π₀ = (∑ x, α x) - hallDef E α β :=
    le_antisymm (mass_le_total_sub_hallDef hπ₀) (optimal_mass_ge hπ₀ hopt)
  refine ⟨⟨?_, ?_⟩, π₀, hπ₀, hπ₀mass, hopt⟩
  · -- coupling → Hall inequalities
    rintro ⟨π, hπ⟩ U
    have hsub : SubCoupling E α β π :=
      ⟨hπ.1, hπ.2.1, fun x => le_of_eq (hπ.2.2.1 x), fun y => le_of_eq (hπ.2.2.2 y)⟩
    have h1 := sum_row_le_neigh hsub U
    have h2 : ∑ x ∈ U, ∑ y, π (x, y) = ∑ x ∈ U, α x :=
      Finset.sum_congr rfl fun x _ => hπ.2.2.1 x
    linarith
  · -- Hall inequalities → coupling
    intro hHall
    have hdef0 : hallDef E α β = 0 := by
      refine le_antisymm ?_ (hallDef_nonneg E α β)
      refine Finset.sup'_le _ _ fun U _ => ?_
      have := hHall U
      linarith
    have hmassval : mass π₀ = ∑ x, α x := by
      rw [hπ₀mass, hdef0, sub_zero]
    have hrows : ∀ x, ∑ y, π₀ (x, y) = α x := by
      have hsum : ∑ x, ∑ y, π₀ (x, y) = ∑ x, α x := by
        rw [← mass_eq_sum_row, hmassval]
      have h := (Finset.sum_eq_sum_iff_of_le
        (fun x _ => hπ₀.2.2.1 x)).mp hsum
      exact fun x => h x (Finset.mem_univ x)
    have hcols : ∀ y, ∑ x, π₀ (x, y) = β y := by
      have hsum : ∑ y, ∑ x, π₀ (x, y) = ∑ y, β y := by
        rw [← mass_eq_sum_col, hmassval, htot]
      have h := (Finset.sum_eq_sum_iff_of_le
        (fun y _ => hπ₀.2.2.2 y)).mp hsum
      exact fun y => h y (Finset.mem_univ y)
    exact ⟨π₀, hπ₀.1, hπ₀.2.1, hrows, hcols⟩

/-- **AO.4 as displayed**: for probability rows, the maximum transportable mass is
`1 - 𝔥_E(α, β)`. -/
theorem max_mass_eq_one_sub_hallDef (E : Finset (S × T)) (α : S → ℝ) (β : T → ℝ)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y) (hα1 : ∑ x, α x = 1) :
    ∃ π, SubCoupling E α β π ∧ mass π = 1 - hallDef E α β ∧
      ∀ π', SubCoupling E α β π' → mass π' ≤ mass π := by
  obtain ⟨π₀, hπ₀, hopt⟩ := exists_max_subCoupling E α β hα hβ
  refine ⟨π₀, hπ₀, ?_, hopt⟩
  have h := le_antisymm (mass_le_total_sub_hallDef hπ₀) (optimal_mass_ge hπ₀ hopt)
  rw [h, hα1]

end WeightedHall
end NCG
