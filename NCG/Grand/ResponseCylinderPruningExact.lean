/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Existential inverse limit and canonical response pruning

Machinery for `thm:GT-response-cylinder-pruning`.  A one-sided compact response-cylinder system
(`def:GT-one-sided-response-cylinders`) consists of nonempty compact sets `C m ⊆ K^{D m}` over
nested query sets `D m`, closed under restriction `r_{m+1,m}(C (m+1)) ⊆ C m` (TRP.2).  With the
stages `C_m^{[n]} = r_{n,m}(C n)` and the stable sets `C_m^∞ = ⋂_{n ≥ m} C_m^{[n]}` (TRP.3):

* `invLimit_nonempty` (TRP.4): the inverse limit of compatible threads is nonempty;
* `stable_nonempty`, `isCompact_stable` (P1);
* `restrict_image_stable` (TRP.5, P2): the stable system is fibrewise surjective;
* `stable_eq_image_invLimit` (P3): `C_m^∞` is the level-`m` projection of the inverse limit;
* `subsystem_subset_stable`, `stable_isExtendible` (P4): `(C_m^∞)` is the largest subsystem in
  which every coarse response extends indefinitely.
-/

open Set Filter Topology

namespace NCG
namespace ResponseCylinder

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
variable {ι : Type*} {D : ℕ → Set ι}

/-- Restriction `r_{n,m} : K^{D n} → K^{D m}` along the inclusion `D m ⊆ D n`. -/
def restrict (hD : Monotone D) {m n : ℕ} (h : m ≤ n) (z : D n → K) : D m → K :=
  fun x => z ⟨x.1, hD h x.2⟩

variable (hD : Monotone D)

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] in
theorem restrict_restrict {m n p : ℕ} (h1 : m ≤ n) (h2 : n ≤ p) (z : D p → K) :
    restrict hD h1 (restrict hD h2 z) = restrict hD (h1.trans h2) z := rfl

omit [CompactSpace K] [T2Space K] in
theorem continuous_restrict {m n : ℕ} (h : m ≤ n) : Continuous (restrict (K := K) hD h) :=
  continuous_pi fun _ => continuous_apply _

/-- A one-sided compact response-cylinder system (TRP.1–TRP.2). -/
structure System (hD : Monotone D) (C : ∀ m, Set (D m → K)) : Prop where
  nonempty : ∀ m, (C m).Nonempty
  compact : ∀ m, IsCompact (C m)
  closed : ∀ m, restrict hD (Nat.le_succ m) '' C (m + 1) ⊆ C m

variable {C : ∀ m, Set (D m → K)}

/-- The stage `C_m^{[n]} = r_{n,m}(C n)`. -/
def stage (hD : Monotone D) (C : ∀ m, Set (D m → K)) {m n : ℕ} (h : m ≤ n) : Set (D m → K) :=
  restrict hD h '' C n

/-- The stable set `C_m^∞ = ⋂_{n ≥ m} C_m^{[n]}` (TRP.3). -/
def stable (hD : Monotone D) (C : ∀ m, Set (D m → K)) (m : ℕ) : Set (D m → K) :=
  ⋂ n : ℕ, ⋂ h : m ≤ n, stage hD C h

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] in
theorem mem_stable_iff {m : ℕ} {a : D m → K} :
    a ∈ stable hD C m ↔ ∀ n : ℕ, ∀ h : m ≤ n, a ∈ stage hD C h := by
  simp [stable, mem_iInter]

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] in
theorem stage_self (m : ℕ) : stage hD C (le_refl m) = C m := by
  ext z
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hc
  · intro hz
    exact ⟨z, hz, rfl⟩

omit [CompactSpace K] [T2Space K] in
/-- Stages decrease with the depth. -/
theorem stage_succ_subset (hS : System hD C) {m n : ℕ} (h : m ≤ n) :
    stage hD C (h.trans (Nat.le_succ n)) ⊆ stage hD C h := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨restrict hD (Nat.le_succ n) c, hS.closed n ⟨c, hc, rfl⟩, rfl⟩

omit [CompactSpace K] [T2Space K] in
theorem stage_antitone (hS : System hD C) {m n p : ℕ} (h1 : m ≤ n) (h2 : n ≤ p) :
    stage hD C (h1.trans h2) ⊆ stage hD C h1 := by
  induction p, h2 using Nat.le_induction with
  | base => exact subset_rfl
  | succ p hnp ih => exact (stage_succ_subset hD hS (h1.trans hnp)).trans ih

omit [CompactSpace K] [T2Space K] in
theorem stage_subset (hS : System hD C) {m n : ℕ} (h : m ≤ n) : stage hD C h ⊆ C m := by
  rw [← stage_self hD (C := C) m]
  exact stage_antitone hD hS le_rfl h

omit [CompactSpace K] [T2Space K] in
theorem isCompact_stage (hS : System hD C) {m n : ℕ} (h : m ≤ n) : IsCompact (stage hD C h) :=
  (hS.compact n).image (continuous_restrict hD h)

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] in
theorem stable_subset (m : ℕ) : stable hD C m ⊆ C m := by
  intro a ha
  rw [mem_stable_iff] at ha
  rw [← stage_self hD (C := C) m]
  exact ha m le_rfl

/-- A nested sequence of nonempty compact sets has nonempty intersection. -/
theorem nonempty_iInter_of_nested {X : Type*} [TopologicalSpace X] [T2Space X] (t : ℕ → Set X)
    (hnested : ∀ i, t (i + 1) ⊆ t i) (hne : ∀ i, (t i).Nonempty) (hcpt : ∀ i, IsCompact (t i)) :
    (⋂ i, t i).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hnested hne (hcpt 0)
    fun i => (hcpt i).isClosed

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] in
theorem stable_eq_iInter (m : ℕ) :
    stable hD C m = ⋂ i : ℕ, stage hD C (Nat.le_add_right m i) := by
  ext a
  rw [mem_stable_iff, mem_iInter]
  constructor
  · intro h i
    exact h (m + i) _
  · intro h n hn
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact h i

omit [CompactSpace K] in
/-- **(P1)**: the stable sets are nonempty. -/
theorem stable_nonempty (hS : System hD C) (m : ℕ) : (stable hD C m).Nonempty := by
  rw [stable_eq_iInter]
  refine nonempty_iInter_of_nested _ (fun i => ?_) (fun i => ?_) (fun i => isCompact_stage hD hS _)
  · exact stage_succ_subset hD hS _
  · obtain ⟨c, hc⟩ := hS.nonempty (m + i)
    exact ⟨_, c, hc, rfl⟩

/-- **(P1)**: the stable sets are compact. -/
theorem isCompact_stable (hS : System hD C) (m : ℕ) : IsCompact (stable hD C m) := by
  rw [stable_eq_iInter]
  exact (isClosed_iInter fun i => (isCompact_stage hD hS _).isClosed).isCompact

/-! ### The inverse limit (TRP.4) -/

/-- The inverse limit: compatible threads `(z m)_m` with `z m ∈ C m`. -/
def invLimit (hD : Monotone D) (C : ∀ m, Set (D m → K)) : Set (∀ m, D m → K) :=
  {z | (∀ m, z m ∈ C m) ∧ ∀ m, restrict hD (Nat.le_succ m) (z (m + 1)) = z m}

/-- Threads satisfying the first `M` compatibility equations. -/
def partialThreads (hD : Monotone D) (C : ∀ m, Set (D m → K)) (M : ℕ) : Set (∀ m, D m → K) :=
  (⋂ m, (fun z : ∀ m, D m → K => z m) ⁻¹' C m) ∩
    ⋂ m, ⋂ (_ : m < M), {z : ∀ m, D m → K | restrict hD (Nat.le_succ m) (z (m + 1)) = z m}

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] in
theorem mem_partialThreads {M : ℕ} {z : ∀ m, D m → K} :
    z ∈ partialThreads hD C M ↔
      (∀ m, z m ∈ C m) ∧ ∀ m < M, restrict hD (Nat.le_succ m) (z (m + 1)) = z m := by
  simp [partialThreads, mem_iInter]

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] in
theorem partialThreads_succ_subset (M : ℕ) :
    partialThreads hD C (M + 1) ⊆ partialThreads hD C M := by
  intro z hz
  rw [mem_partialThreads] at hz ⊢
  exact ⟨hz.1, fun m hm => hz.2 m (Nat.lt_succ_of_lt hm)⟩

omit [CompactSpace K] in
theorem isClosed_partialThreads (hS : System hD C) (M : ℕ) :
    IsClosed (partialThreads hD C M) := by
  refine IsClosed.inter (isClosed_iInter fun m => ?_) (isClosed_iInter fun m => isClosed_iInter
    fun _ => isClosed_eq ((continuous_restrict hD _).comp (continuous_apply _))
      (continuous_apply m))
  exact (hS.compact m).isClosed.preimage (continuous_apply m)

omit [CompactSpace K] [T2Space K] in
theorem partialThreads_nonempty (hS : System hD C) (M : ℕ) :
    (partialThreads hD C M).Nonempty := by
  classical
  obtain ⟨zM, hzM⟩ := hS.nonempty M
  refine ⟨fun m => if h : m ≤ M then restrict hD h zM else (hS.nonempty m).some, ?_⟩
  rw [mem_partialThreads]
  refine ⟨fun m => ?_, fun m hm => ?_⟩
  · by_cases h : m ≤ M
    · simp only [dif_pos h]
      exact stage_subset hD hS h ⟨zM, hzM, rfl⟩
    · simp only [dif_neg h]
      exact (hS.nonempty m).some_mem
  · have h1 : m + 1 ≤ M := hm
    have h0 : m ≤ M := Nat.le_of_lt hm
    simp only [dif_pos h1, dif_pos h0]
    rfl

/-- **(TRP.4)**: the inverse limit is nonempty. -/
theorem invLimit_nonempty (hS : System hD C) : (invLimit hD C).Nonempty := by
  obtain ⟨z, hz⟩ := nonempty_iInter_of_nested (partialThreads hD C)
    (partialThreads_succ_subset hD) (partialThreads_nonempty hD hS)
    (fun M => (isClosed_partialThreads hD hS M).isCompact)
  rw [mem_iInter] at hz
  exact ⟨z, fun m => ((mem_partialThreads hD).mp (hz 0)).1 m,
    fun m => ((mem_partialThreads hD).mp (hz (m + 1))).2 m (Nat.lt_succ_self m)⟩

/-! ### Fibrewise surjectivity of the stable system (TRP.5) -/

omit [CompactSpace K] in
/-- **(P2)**: `r_{m+1,m}(C_{m+1}^∞) = C_m^∞`. -/
theorem restrict_image_stable (hS : System hD C) (m : ℕ) :
    restrict hD (Nat.le_succ m) '' stable hD C (m + 1) = stable hD C m := by
  apply Subset.antisymm
  · rintro _ ⟨b, hb, rfl⟩
    rw [mem_stable_iff] at hb ⊢
    intro n hn
    rcases Nat.lt_or_ge n (m + 1) with h | h
    · have hnm : n = m := by omega
      subst hnm
      have hbC := hb (n + 1) le_rfl
      rw [stage_self] at hbC
      rw [stage_self]
      exact hS.closed n ⟨b, hbC, rfl⟩
    · obtain ⟨c, hc, rfl⟩ := hb n h
      exact ⟨c, hc, rfl⟩
  · intro a ha
    set B : ℕ → Set (D (m + 1) → K) := fun i =>
      stage hD C (Nat.le_add_right (m + 1) i) ∩ {b | restrict hD (Nat.le_succ m) b = a} with hB
    have hne : ∀ i, (B i).Nonempty := by
      intro i
      obtain ⟨c, hc, hca⟩ := (mem_stable_iff hD).mp ha (m + 1 + i) (by omega)
      exact ⟨restrict hD (Nat.le_add_right (m + 1) i) c, ⟨c, hc, rfl⟩, hca⟩
    have hnested : ∀ i, B (i + 1) ⊆ B i := fun i b hb =>
      ⟨stage_succ_subset hD hS _ hb.1, hb.2⟩
    have hcpt : ∀ i, IsCompact (B i) := fun i =>
      (isCompact_stage hD hS _).inter_right
        (isClosed_eq (continuous_restrict hD _) continuous_const)
    obtain ⟨b, hb⟩ := nonempty_iInter_of_nested B hnested hne hcpt
    rw [mem_iInter] at hb
    refine ⟨b, ?_, (hb 0).2⟩
    rw [mem_stable_iff]
    intro n hn
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (hb i).1

/-! ### The stable sets as projections of the inverse limit (P3) -/

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] in
theorem mem_stable_of_mem_invLimit {z : ∀ m, D m → K} (hz : z ∈ invLimit hD C) (m : ℕ) :
    z m ∈ stable hD C m := by
  rw [mem_stable_iff]
  intro n hn
  have key : ∀ i, restrict hD (Nat.le_add_right m i) (z (m + i)) = z m := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [← ih, ← hz.2 (m + i)]
      rfl
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨z (m + i), hz.1 _, key i⟩

omit [CompactSpace K] in
/-- Every stable point extends to a compatible thread. -/
theorem exists_thread_of_mem_stable (hS : System hD C) {m : ℕ} {a : D m → K}
    (ha : a ∈ stable hD C m) : ∃ z ∈ invLimit hD C, z m = a := by
  classical
  have step : ∀ n, ∀ b ∈ stable hD C n,
      ∃ b' ∈ stable hD C (n + 1), restrict hD (Nat.le_succ n) b' = b := by
    intro n b hb
    rw [← restrict_image_stable hD hS n] at hb
    obtain ⟨b', hb', hbb⟩ := hb
    exact ⟨b', hb', hbb⟩
  choose up hup_mem hup_eq using step
  -- the upward chain through `a`, indexed by `n ≥ m`
  let next : ∀ {k : ℕ}, {b : D k → K // b ∈ stable hD C k} →
      {b : D (k + 1) → K // b ∈ stable hD C (k + 1)} :=
    fun {k} b => ⟨up k b.1 b.2, hup_mem k b.1 b.2⟩
  let w : ∀ n, m ≤ n → {b : D n → K // b ∈ stable hD C n} :=
    fun n h => Nat.leRecOn h (fun {k} b => next b) ⟨a, ha⟩
  have w_self : (w m le_rfl).1 = a := by
    simp only [w, Nat.leRecOn_self]
  have w_succ : ∀ n (h : m ≤ n),
      (w (n + 1) (h.trans (Nat.le_succ n))).1 = up n (w n h).1 (w n h).2 := by
    intro n h
    simp only [w, Nat.leRecOn_succ h]
    rfl
  refine ⟨fun n => if h : m ≤ n then (w n h).1 else restrict hD (le_of_lt (Nat.lt_of_not_le h)) a,
    ⟨fun n => ?_, fun n => ?_⟩, ?_⟩
  · by_cases h : m ≤ n
    · simp only [dif_pos h]
      exact stable_subset hD n (w n h).2
    · simp only [dif_neg h]
      exact stage_subset hD hS _ ⟨a, stable_subset hD m ha, rfl⟩
  · by_cases h : m ≤ n
    · have h' : m ≤ n + 1 := h.trans (Nat.le_succ n)
      simp only [dif_pos h, dif_pos h']
      rw [w_succ n h]
      exact hup_eq n (w n h).1 (w n h).2
    · by_cases h' : m ≤ n + 1
      · have hm : m = n + 1 := by omega
        subst hm
        simp only [dif_pos h', dif_neg h]
        rw [w_self]
      · simp only [dif_neg h, dif_neg h']
        rfl
  · simp only [dif_pos le_rfl]
    exact w_self

omit [CompactSpace K] in
/-- **(P3)**: `C_m^∞` is the level-`m` projection of the inverse limit. -/
theorem stable_eq_image_invLimit (hS : System hD C) (m : ℕ) :
    stable hD C m = (fun z : ∀ m, D m → K => z m) '' invLimit hD C := by
  ext a
  constructor
  · intro ha
    obtain ⟨z, hz, hzm⟩ := exists_thread_of_mem_stable hD hS ha
    exact ⟨z, hz, hzm⟩
  · rintro ⟨z, hz, rfl⟩
    exact mem_stable_of_mem_invLimit hD hz m

/-! ### Maximality (P4) -/

/-- A subsystem of `(C m)` in which every coarse response extends indefinitely. -/
structure IsExtendible (hD : Monotone D) (C E : ∀ m, Set (D m → K)) : Prop where
  subset : ∀ m, E m ⊆ C m
  extend : ∀ m, ∀ e ∈ E m, ∃ e' ∈ E (m + 1), restrict hD (Nat.le_succ m) e' = e

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] in
/-- **(P4)**: every indefinitely extendible subsystem lies in the stable system. -/
theorem subsystem_subset_stable {E : ∀ m, Set (D m → K)} (hE : IsExtendible hD C E) (m : ℕ) :
    E m ⊆ stable hD C m := by
  intro e he
  rw [mem_stable_iff]
  intro n hn
  have hext : ∀ i, ∃ e' ∈ E (m + i), restrict hD (Nat.le_add_right m i) e' = e := by
    intro i
    induction i with
    | zero => exact ⟨e, he, rfl⟩
    | succ i ih =>
      obtain ⟨e', he', hee⟩ := ih
      obtain ⟨e'', he'', h2⟩ := hE.extend _ e' he'
      refine ⟨e'', he'', ?_⟩
      rw [← hee, ← h2]
      rfl
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨e', he', hee⟩ := hext i
  exact ⟨e', hE.subset _ he', hee⟩

omit [CompactSpace K] in
/-- **(P4)**: the stable system itself is indefinitely extendible. -/
theorem stable_isExtendible (hS : System hD C) : IsExtendible hD C (stable hD C) := by
  refine ⟨stable_subset hD, fun m e he => ?_⟩
  rw [← restrict_image_stable hD hS m] at he
  obtain ⟨e', he', h⟩ := he
  exact ⟨e', he', h⟩

/-- **`thm:GT-response-cylinder-pruning`**: (TRP.4) nonempty inverse limit, (P1) nonempty compact
stable sets, (P2) fibrewise surjectivity (TRP.5), (P3) the stable sets are the projections of the
inverse limit, (P4) the stable system is the largest indefinitely extendible subsystem. -/
theorem response_cylinder_pruning (hS : System hD C) :
    (invLimit hD C).Nonempty ∧
      (∀ m, (stable hD C m).Nonempty ∧ IsCompact (stable hD C m)) ∧
      (∀ m, restrict hD (Nat.le_succ m) '' stable hD C (m + 1) = stable hD C m) ∧
      (∀ m, stable hD C m = (fun z : ∀ m, D m → K => z m) '' invLimit hD C) ∧
      IsExtendible hD C (stable hD C) ∧
      ∀ E : ∀ m, Set (D m → K), IsExtendible hD C E → ∀ m, E m ⊆ stable hD C m :=
  ⟨invLimit_nonempty hD hS, fun m => ⟨stable_nonempty hD hS m, isCompact_stable hD hS m⟩,
    restrict_image_stable hD hS, stable_eq_image_invLimit hD hS, stable_isExtendible hD hS,
    fun _ hE m => subsystem_subset_stable hD hE m⟩

end ResponseCylinder
end NCG
