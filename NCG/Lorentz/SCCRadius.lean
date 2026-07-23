/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.BlockRadius
import NCG.Graph.Condensation

/-!
# The growth rate is attained on a strongly connected component

The full m-block form of clause (ii) of `prop:terminal-component`
(`manuscripts/renewal_emergence/renewal_emergence.tex`): for a nonnegative matrix `B` with a
diagonal witness, the Gelfand–Fekete growth rate satisfies

`pRad B = max_j pRad (B|_{C_j})`

over the strongly connected components `C_j` of the support graph of
`B`.  The two halves are

* `pRad_sccBlock_le` — every component block is dominated
  (`pRad_submatrix_le`, batch M18);
* `pRad_attained_on_component` — **the maximum is attained**: there
  is a component whose block carries a diagonal witness and realizes
  the full growth rate.

The proof is a strong induction on the number of vertices that peels
one *minimal* strongly connected component `P` (one that no other
component reaches) per step.  Since no edge enters `P` from outside,
the matrix is block triangular for the split `P / ¬P`, and

* if both blocks carry diagonal witnesses, the two-block bound
  `pRad_blockTriangular_le` (batch M19) applies and the induction
  continues in the block attaining the maximum;
* a block without a diagonal witness is **nilpotent**
  (`pow_card_eq_zero_of_no_witness` — a long positive chain must
  revisit a vertex, closing a positive cycle), and a truncated
  resolvent through the nilpotent block
  (`nilpotent_supersolution`) glues with the super-solution of the
  other block, so the nilpotent block drops out of the bound.

Positive chains (`PosChain`) mediate between entries of matrix powers
and the support graph: `chain_of_pow_pos`, `pow_pos_of_chain`,
`chain_restrict` (restriction to forward-closed vertex sets) and
`chain_scc_lift` (a closed chain lifts into the block of its own
strongly connected component).
-/

namespace NCG

open Filter

attribute [local instance 10] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## Positive chains and the support graph -/

/-- The support adjacency of a nonnegative matrix. -/
def supportAdj (B : Matrix V V ℝ) : V → V → Prop := fun x y => 0 < B x y

/-- Membership in the strongly connected component of `x` in the
support graph of `B`. -/
def sccMem (B : Matrix V V ℝ) (x y : V) : Prop :=
  Condense.MutualReach (supportAdj B) x y

theorem sccMem_refl (B : Matrix V V ℝ) (x : V) : sccMem B x x :=
  (Condense.mutualReach_equivalence (supportAdj B)).refl x

instance (B : Matrix V V ℝ) (x : V) : Nonempty {y // sccMem B x y} :=
  ⟨⟨x, sccMem_refl B x⟩⟩

/-- The principal block of the strongly connected component of `x`. -/
def sccBlock (B : Matrix V V ℝ) (x : V) :
    Matrix {y // sccMem B x y} {y // sccMem B x y} ℝ :=
  B.submatrix (Function.Embedding.subtype _) (Function.Embedding.subtype _)

theorem sccBlock_nonneg {B : Matrix V V ℝ} (hB : EntryNonneg B) (x : V) :
    EntryNonneg (sccBlock B x) := fun a b => hB _ _

/-- A positive-entry chain of length `k` from `x` to `y`. -/
def PosChain (B : Matrix V V ℝ) (k : ℕ) (x y : V) : Prop :=
  ∃ p : ℕ → V, p 0 = x ∧ p k = y ∧ ∀ t, t < k → 0 < B (p t) (p (t + 1))

theorem posChain_zero (B : Matrix V V ℝ) (x : V) : PosChain B 0 x x :=
  ⟨fun _ => x, rfl, rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩

theorem posChain_single {B : Matrix V V ℝ} {a b : V} (h : 0 < B a b) :
    PosChain B 1 a b := by
  refine ⟨fun t => if t = 0 then a else b, if_pos rfl, if_neg one_ne_zero, ?_⟩
  intro t ht
  interval_cases t
  simpa using h

/-- Chains concatenate. -/
theorem PosChain.trans {B : Matrix V V ℝ} {k l : ℕ} {x y z : V}
    (h1 : PosChain B k x y) (h2 : PosChain B l y z) :
    PosChain B (k + l) x z := by
  obtain ⟨p, hp0, hpk, hps⟩ := h1
  obtain ⟨q, hq0, hql, hqs⟩ := h2
  refine ⟨fun t => if t ≤ k then p t else q (t - k), ?_, ?_, ?_⟩
  · simp [hp0]
  · dsimp only
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · have h3 : y = z := by rw [← hq0, hql]
      simpa using hpk.trans h3
    · have h4 : ¬ (k + l ≤ k) := by omega
      rw [if_neg h4]
      have h5 : k + l - k = l := by omega
      rw [h5, hql]
  · intro t ht
    dsimp only
    rcases lt_trichotomy t k with h | h | h
    · have h6 : t ≤ k := h.le
      have h7 : t + 1 ≤ k := h
      rw [if_pos h6, if_pos h7]
      exact hps t h
    · subst h
      have hl : 0 < l := by omega
      rw [if_pos le_rfl, if_neg (by omega : ¬ (t + 1 ≤ t))]
      have h8 : t + 1 - t = 1 := by omega
      rw [h8, hpk]
      have h9 := hqs 0 hl
      rw [hq0] at h9
      exact h9
    · rw [if_neg (by omega : ¬ (t ≤ k)), if_neg (by omega : ¬ (t + 1 ≤ k))]
      have h10 : t + 1 - k = (t - k) + 1 := by omega
      rw [h10]
      exact hqs (t - k) (by omega)

/-- Entry products along a split dominate the entry of the summed
power. -/
theorem pow_add_entry_ge {B : Matrix V V ℝ} (hB : EntryNonneg B)
    (j k : ℕ) (x y z : V) :
    (B ^ j) x y * (B ^ k) y z ≤ (B ^ (j + k)) x z := by
  rw [pow_add, Matrix.mul_apply]
  exact Finset.single_le_sum
    (f := fun w => (B ^ j) x w * (B ^ k) w z)
    (fun w _ => mul_nonneg (entryNonneg_pow hB j x w)
      (entryNonneg_pow hB k w z))
    (Finset.mem_univ y)

/-- A positive entry of a matrix power yields a positive chain. -/
theorem chain_of_pow_pos {B : Matrix V V ℝ} (hB : EntryNonneg B) :
    ∀ (k : ℕ) (x y : V), 0 < (B ^ k) x y → PosChain B k x y := by
  intro k
  induction k with
  | zero =>
    intro x y hpos
    rw [pow_zero] at hpos
    rcases eq_or_ne x y with rfl | hxy
    · exact posChain_zero B x
    · rw [Matrix.one_apply_ne hxy] at hpos
      exact absurd hpos (lt_irrefl 0)
  | succ k ih =>
    intro x y hpos
    rw [pow_succ, Matrix.mul_apply] at hpos
    have h1 : ∃ z, 0 < (B ^ k) x z * B z y := by
      by_contra hno
      push_neg at hno
      have h2 : ∑ z, (B ^ k) x z * B z y ≤ 0 :=
        Finset.sum_nonpos fun z _ => hno z
      linarith
    obtain ⟨z, hz⟩ := h1
    have hxz : 0 < (B ^ k) x z := by
      by_contra hle
      push_neg at hle
      have h3 : (B ^ k) x z = 0 :=
        le_antisymm hle (entryNonneg_pow hB k x z)
      rw [h3, zero_mul] at hz
      exact lt_irrefl 0 hz
    have hzy : 0 < B z y := by
      by_contra hle
      push_neg at hle
      have h3 : B z y = 0 := le_antisymm hle (hB z y)
      rw [h3, mul_zero] at hz
      exact lt_irrefl 0 hz
    exact (ih x z hxz).trans (posChain_single hzy)

/-- A positive chain between indexed points yields a positive entry
of the corresponding matrix power. -/
theorem pow_entry_pos_of_chain {B : Matrix V V ℝ} (hB : EntryNonneg B)
    {p : ℕ → V} {i j : ℕ} (hij : i ≤ j)
    (hstep : ∀ t, i ≤ t → t < j → 0 < B (p t) (p (t + 1))) :
    0 < (B ^ (j - i)) (p i) (p j) := by
  induction j, hij using Nat.le_induction with
  | base =>
    rw [Nat.sub_self, pow_zero, Matrix.one_apply_eq]
    exact zero_lt_one
  | succ j hij ih =>
    have h1 : 0 < (B ^ (j - i)) (p i) (p j) :=
      ih fun t ht htj => hstep t ht (htj.trans (Nat.lt_succ_self j))
    have h2 : 0 < B (p j) (p (j + 1)) :=
      hstep j hij (Nat.lt_succ_self j)
    have h3 : (B ^ (j - i)) (p i) (p j) * (B ^ 1) (p j) (p (j + 1))
        ≤ (B ^ (j - i + 1)) (p i) (p (j + 1)) :=
      pow_add_entry_ge hB (j - i) 1 (p i) (p j) (p (j + 1))
    have h4 : j + 1 - i = j - i + 1 := by omega
    rw [h4]
    refine lt_of_lt_of_le ?_ h3
    rw [pow_one]
    exact mul_pos h1 h2

/-- A positive chain yields a positive entry of the power. -/
theorem pow_pos_of_chain {B : Matrix V V ℝ} (hB : EntryNonneg B)
    {k : ℕ} {x y : V} (hc : PosChain B k x y) : 0 < (B ^ k) x y := by
  obtain ⟨p, hp0, hpk, hstep⟩ := hc
  have h1 := pow_entry_pos_of_chain hB (Nat.zero_le k)
    (fun t _ htk => hstep t htk)
  rw [Nat.sub_zero, hp0, hpk] at h1
  exact h1

/-- Chains generate reachability in the support graph. -/
theorem reaches_of_chain {B : Matrix V V ℝ} {p : ℕ → V} {i j : ℕ}
    (hij : i ≤ j)
    (hstep : ∀ t, i ≤ t → t < j → 0 < B (p t) (p (t + 1))) :
    Condense.Reaches (supportAdj B) (p i) (p j) := by
  induction j, hij using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ j hij ih =>
    have h1 := ih fun t ht htj => hstep t ht (htj.trans (Nat.lt_succ_self j))
    exact h1.tail (hstep j hij (Nat.lt_succ_self j))

theorem reaches_of_posChain {B : Matrix V V ℝ} {k : ℕ} {x y : V}
    (hc : PosChain B k x y) :
    Condense.Reaches (supportAdj B) x y := by
  obtain ⟨p, hp0, hpk, hstep⟩ := hc
  have h1 := reaches_of_chain (B := B) (p := p) (Nat.zero_le k)
    (fun t _ htk => hstep t htk)
  rwa [hp0, hpk] at h1

/-! ## Restriction of chains to forward-closed sets -/

/-- A chain starting in a forward-closed vertex set restricts to the
principal block on that set. -/
theorem chain_restrict {B : Matrix V V ℝ} {Q : V → Prop}
    (hQ : ∀ a b, Q a → 0 < B a b → Q b) {x y : V} {k : ℕ}
    (hx : Q x) (hc : PosChain B k x y) :
    ∃ hy : Q y, PosChain
      (B.submatrix (Function.Embedding.subtype Q)
        (Function.Embedding.subtype Q)) k ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨p, hp0, hpk, hstep⟩ := hc
  have hall : ∀ t, t ≤ k → Q (p t) := by
    intro t
    induction t with
    | zero => intro _; rw [hp0]; exact hx
    | succ t iht =>
      intro htk
      exact hQ _ _ (iht (by omega)) (hstep t (by omega))
  have hy : Q y := by rw [← hpk]; exact hall k le_rfl
  refine ⟨hy, fun t => if h : Q (p t) then ⟨p t, h⟩ else ⟨x, hx⟩,
    ?_, ?_, ?_⟩
  · dsimp only
    rw [dif_pos (show Q (p 0) by rw [hp0]; exact hx)]
    exact Subtype.ext hp0
  · dsimp only
    rw [dif_pos (hall k le_rfl)]
    exact Subtype.ext hpk
  · intro t htk
    dsimp only
    rw [dif_pos (hall t htk.le), dif_pos (hall (t + 1) htk)]
    exact hstep t htk

/-- Reachability restricts to a forward-closed vertex set. -/
theorem reaches_restrict {B : Matrix V V ℝ} {Q : V → Prop}
    (hQ : ∀ a b, Q a → 0 < B a b → Q b) {x y : V}
    (hx : Q x) (h : Condense.Reaches (supportAdj B) x y) :
    ∃ hy : Q y, Condense.Reaches
      (supportAdj (B.submatrix (Function.Embedding.subtype Q)
        (Function.Embedding.subtype Q))) ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
  | tail hxz hstep ih =>
    obtain ⟨hz, hrz⟩ := ih
    exact ⟨hQ _ _ hz hstep, hrz.tail hstep⟩

/-- Reachability in a principal block maps to reachability in the
ambient support graph. -/
theorem reaches_of_restrict {B : Matrix V V ℝ} {Q : V → Prop}
    {u w : {y // Q y}}
    (h : Condense.Reaches
      (supportAdj (B.submatrix (Function.Embedding.subtype Q)
        (Function.Embedding.subtype Q))) u w) :
    Condense.Reaches (supportAdj B) u.val w.val := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep

/-! ## Witness localization into the strongly connected component -/

/-- A chain with a positive return chain lifts into the block of the
strongly connected component of its starting point. -/
theorem chain_scc_lift {B : Matrix V V ℝ} {x : V} :
    ∀ (k : ℕ) (z : V) (l : ℕ), PosChain B k x z → PosChain B l z x →
    ∃ hz : sccMem B x z,
      PosChain (sccBlock B x) k ⟨x, sccMem_refl B x⟩ ⟨z, hz⟩ := by
  intro k
  induction k with
  | zero =>
    intro z l hc _
    obtain ⟨p, hp0, hpk, _⟩ := hc
    have hxz : x = z := by rw [← hp0, hpk]
    subst hxz
    exact ⟨sccMem_refl B x, posChain_zero _ _⟩
  | succ k ih =>
    intro z l hc hr
    obtain ⟨p, hp0, hpk1, hstep⟩ := hc
    have hcw : PosChain B k x (p k) :=
      ⟨p, hp0, rfl, fun t ht => hstep t (ht.trans (Nat.lt_succ_self k))⟩
    have hwz : 0 < B (p k) z := by
      have h1 := hstep k (Nat.lt_succ_self k)
      rwa [hpk1] at h1
    have hrw : PosChain B (1 + l) (p k) x :=
      (posChain_single hwz).trans hr
    obtain ⟨hw, hblockchain⟩ := ih (p k) (1 + l) hcw hrw
    have hz : sccMem B x z := by
      constructor
      · exact reaches_of_posChain (⟨p, hp0, hpk1, hstep⟩ : PosChain B (k + 1) x z)
      · exact reaches_of_posChain hr
    refine ⟨hz, hblockchain.trans (posChain_single ?_)⟩
    exact hwz

/-- **Witness localization**: a diagonal witness of `B` localizes to
the block of the strongly connected component of its base point. -/
theorem hasDiagWitness_sccBlock {B : Matrix V V ℝ}
    (hB : EntryNonneg B) {x : V} {m : ℕ} (hm : 0 < m)
    (hpos : 0 < (B ^ m) x x) : HasDiagWitness (sccBlock B x) := by
  have hc := chain_of_pow_pos hB m x x hpos
  obtain ⟨hz, hblockchain⟩ := chain_scc_lift m x 0 hc (posChain_zero B x)
  have h1 : (⟨x, hz⟩ : {y // sccMem B x y}) = ⟨x, sccMem_refl B x⟩ :=
    Subtype.ext rfl
  rw [h1] at hblockchain
  exact ⟨⟨x, sccMem_refl B x⟩, m, hm,
    pow_pos_of_chain (sccBlock_nonneg hB x) hblockchain⟩

/-! ## Blocks without witnesses are nilpotent -/

/-- **No witness forces nilpotency**: a long positive chain revisits
a vertex and closes a positive cycle, which would be a diagonal
witness. -/
theorem pow_card_eq_zero_of_no_witness {N : Matrix V V ℝ}
    (hN : EntryNonneg N) (hw : ¬ HasDiagWitness N) :
    N ^ (Fintype.card V) = 0 := by
  ext a b
  by_contra hab
  have hpos : 0 < (N ^ (Fintype.card V)) a b :=
    lt_of_le_of_ne (entryNonneg_pow hN _ a b) (Ne.symm hab)
  obtain ⟨p, hp0, hpk, hstep⟩ :=
    chain_of_pow_pos hN (Fintype.card V) a b hpos
  have hcard : Fintype.card V < Fintype.card (Fin (Fintype.card V + 1)) := by
    simp
  obtain ⟨i, j, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card V + 1) => p i) hcard
  have hkey : ∀ i j : Fin (Fintype.card V + 1), (i : ℕ) < (j : ℕ) →
      p i = p j → False := by
    intro i j hij hpeq
    have h1 : 0 < (N ^ ((j : ℕ) - (i : ℕ))) (p i) (p j) :=
      pow_entry_pos_of_chain hN hij.le
        (fun t _ htj => hstep t (by omega))
    rw [← hpeq] at h1
    exact hw ⟨p i, (j : ℕ) - (i : ℕ), by omega, h1⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact hkey i j (Fin.lt_iff_val_lt_val.mp h) heq
  · exact hkey j i (Fin.lt_iff_val_lt_val.mp h) heq.symm

/-- **Truncated resolvent through a nilpotent block**: an exact
super-solution equation `Nw + u + 1 = μw` with `w` bounded below. -/
theorem nilpotent_supersolution {N : Matrix V V ℝ}
    (hN : EntryNonneg N) (hnil : N ^ (Fintype.card V) = 0)
    {μ : ℝ} (hμ : 0 < μ) (u : V → ℝ) (hu : ∀ a, 0 ≤ u a) :
    ∃ w : V → ℝ, (∀ a, μ⁻¹ * (u a + 1) ≤ w a)
      ∧ ∀ a, N.mulVec w a + u a + 1 = μ * w a := by
  set n := Fintype.card V with hn
  set v : V → ℝ := fun a => u a + 1 with hv
  have hv0 : ∀ a, 0 ≤ v a := fun a => by
    have := hu a
    simp only [hv]
    linarith
  have hvterm : ∀ (k : ℕ) (a : V), 0 ≤ μ⁻¹ ^ (k + 1) * (N ^ k).mulVec v a := by
    intro k a
    refine mul_nonneg (pow_nonneg (by positivity) _) ?_
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun b _ =>
      mul_nonneg (entryNonneg_pow hN k a b) (hv0 b)
  refine ⟨fun a => ∑ k ∈ Finset.range n,
    μ⁻¹ ^ (k + 1) * (N ^ k).mulVec v a, ?_, ?_⟩
  · intro a
    have h0 : μ⁻¹ ^ (0 + 1) * (N ^ 0).mulVec v a = μ⁻¹ * v a := by
      rw [pow_zero, pow_one, Matrix.one_mulVec]
    have hmem : 0 ∈ Finset.range n := by
      rw [Finset.mem_range, hn]
      exact Fintype.card_pos
    calc μ⁻¹ * (u a + 1) = μ⁻¹ ^ (0 + 1) * (N ^ 0).mulVec v a := by
          rw [h0]
      _ ≤ ∑ k ∈ Finset.range n, μ⁻¹ ^ (k + 1) * (N ^ k).mulVec v a :=
          Finset.single_le_sum (fun k _ => hvterm k a) hmem
  · intro a
    -- N w = Σ_k μ^{-(k+1)} N^{k+1} v
    have hNw : N.mulVec (fun a => ∑ k ∈ Finset.range n,
        μ⁻¹ ^ (k + 1) * (N ^ k).mulVec v a) a
        = ∑ k ∈ Finset.range n,
            μ⁻¹ ^ (k + 1) * (N ^ (k + 1)).mulVec v a := by
      rw [Matrix.mulVec, dotProduct]
      have h1 : ∀ b, N a b * (∑ k ∈ Finset.range n,
          μ⁻¹ ^ (k + 1) * (N ^ k).mulVec v b)
          = ∑ k ∈ Finset.range n,
              μ⁻¹ ^ (k + 1) * (N a b * (N ^ k).mulVec v b) := by
        intro b
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      rfl
    rw [hNw]
    -- reindex with f j := μ^{-j} (N^j v) a
    set f : ℕ → ℝ := fun j => μ⁻¹ ^ j * (N ^ j).mulVec v a with hf
    have hshift : ∀ k, μ⁻¹ ^ (k + 1) * (N ^ (k + 1)).mulVec v a
        = f (k + 1) := fun k => rfl
    have hsum1 : ∑ k ∈ Finset.range n,
        μ⁻¹ ^ (k + 1) * (N ^ (k + 1)).mulVec v a
        = (∑ j ∈ Finset.range (n + 1), f j) - f 0 := by
      rw [Finset.sum_range_succ']
      simp only [hshift]
      ring
    have hfn : f n = 0 := by
      simp only [hf, hn]
      rw [hnil, Matrix.zero_mulVec]
      simp
    have hsum2 : ∑ j ∈ Finset.range (n + 1), f j
        = ∑ j ∈ Finset.range n, f j := by
      rw [Finset.sum_range_succ, hfn, add_zero]
    have hf0 : f 0 = v a := by
      simp only [hf]
      rw [pow_zero, pow_zero, Matrix.one_mulVec, one_mul]
    have hmul : μ * ∑ k ∈ Finset.range n,
        μ⁻¹ ^ (k + 1) * (N ^ k).mulVec v a
        = ∑ j ∈ Finset.range n, f j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hf]
      rw [pow_succ]
      field_simp
    rw [hsum1, hsum2, hf0, ← hmul]
    simp only [hv]
    ring

/-! ## Reindexing invariance of the growth rate -/

section Reindex

variable {S : Type*} [Fintype S] [DecidableEq S]
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem pow_submatrix_equiv (e : S ≃ T) (B : Matrix T T ℝ) (k : ℕ) :
    (B.submatrix ⇑e ⇑e) ^ k = (B ^ k).submatrix ⇑e ⇑e := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (Matrix.submatrix_one_equiv e).symm
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, Matrix.submatrix_mul_equiv]

theorem entrySum_submatrix_equiv (e : S ≃ T) (B : Matrix T T ℝ) :
    entrySum (B.submatrix ⇑e ⇑e) = entrySum B := by
  unfold entrySum
  rw [← Equiv.sum_comp e (fun x => ∑ y, B x y)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Equiv.sum_comp e (fun y => B (e x) y)]
  rfl

theorem growthSeq_submatrix_equiv (e : S ≃ T) (B : Matrix T T ℝ)
    (k : ℕ) : growthSeq (B.submatrix ⇑e ⇑e) k = growthSeq B k := by
  unfold growthSeq
  rw [pow_submatrix_equiv, entrySum_submatrix_equiv]

theorem pRad_submatrix_equiv [Nonempty S] [Nonempty T]
    (e : S ≃ T) (B : Matrix T T ℝ) :
    pRad (B.submatrix ⇑e ⇑e) = pRad B := by
  unfold pRad
  have h1 : (fun k : ℕ => growthSeq (B.submatrix ⇑e ⇑e) k / k)
      = fun k : ℕ => growthSeq B k / k := by
    funext k
    rw [growthSeq_submatrix_equiv]
  rw [h1]

theorem hasDiagWitness_submatrix_equiv (e : S ≃ T) {B : Matrix T T ℝ}
    (hw : HasDiagWitness B) : HasDiagWitness (B.submatrix ⇑e ⇑e) := by
  obtain ⟨x, m, hm, hpos⟩ := hw
  refine ⟨e.symm x, m, hm, ?_⟩
  rw [pow_submatrix_equiv]
  show 0 < (B ^ m) (e (e.symm x)) (e (e.symm x))
  rwa [Equiv.apply_symm_apply]

/-- Embeddings with equal range induce an equiv intertwining them. -/
theorem embedding_range_congr (e₁ : S ↪ V) (e₂ : T ↪ V)
    (hr : Set.range ⇑e₁ = Set.range ⇑e₂) :
    ∃ f : S ≃ T, ∀ s, e₂ (f s) = e₁ s := by
  refine ⟨(Equiv.ofInjective ⇑e₁ e₁.injective).trans
    ((Equiv.setCongr hr).trans
      (Equiv.ofInjective ⇑e₂ e₂.injective).symm), fun s => ?_⟩
  simp only [Equiv.trans_apply]
  rw [Equiv.apply_ofInjective_symm e₂.injective]
  rfl

theorem submatrix_range_congr (e₁ : S ↪ V) (e₂ : T ↪ V)
    (hr : Set.range ⇑e₁ = Set.range ⇑e₂) (B : Matrix V V ℝ) :
    ∃ f : S ≃ T, B.submatrix ⇑e₁ ⇑e₁
      = (B.submatrix ⇑e₂ ⇑e₂).submatrix ⇑f ⇑f := by
  obtain ⟨f, hf⟩ := embedding_range_congr e₁ e₂ hr
  refine ⟨f, ?_⟩
  ext a b
  simp only [Matrix.submatrix_apply, hf]

theorem pRad_submatrix_range_congr [Nonempty S] (e₁ : S ↪ V)
    (e₂ : T ↪ V) (hr : Set.range ⇑e₁ = Set.range ⇑e₂)
    (B : Matrix V V ℝ) :
    pRad (B.submatrix ⇑e₁ ⇑e₁) = pRad (B.submatrix ⇑e₂ ⇑e₂) := by
  obtain ⟨f, hmat⟩ := submatrix_range_congr e₁ e₂ hr B
  haveI : Nonempty T := ⟨f (Classical.arbitrary S)⟩
  rw [hmat, pRad_submatrix_equiv]

theorem hasDiagWitness_submatrix_range_congr (e₁ : S ↪ V)
    (e₂ : T ↪ V) (hr : Set.range ⇑e₁ = Set.range ⇑e₂)
    {B : Matrix V V ℝ}
    (hw : HasDiagWitness (B.submatrix ⇑e₂ ⇑e₂)) :
    HasDiagWitness (B.submatrix ⇑e₁ ⇑e₁) := by
  obtain ⟨f, hmat⟩ := submatrix_range_congr e₁ e₂ hr B
  rw [hmat]
  exact hasDiagWitness_submatrix_equiv f hw

end Reindex

/-! ## Gluing through a nilpotent block -/

section Nilpotent

variable {P : V → Prop}

/-- **First block nilpotent**: when no transition leads from `¬P`
back to `P` and the `P` block carries no diagonal witness, the growth
rate is dominated by the complementary block alone. -/
theorem pRad_le_of_nilpotent_first
    [Nonempty {x // P x}] [Nonempty {x // ¬P x}]
    {B : Matrix V V ℝ} (hB : EntryNonneg B) (hw : HasDiagWitness B)
    (hwC : HasDiagWitness (B.submatrix
      (Function.Embedding.subtype (fun x => ¬P x))
      (Function.Embedding.subtype (fun x => ¬P x))))
    (hnilS : ¬ HasDiagWitness (B.submatrix
      (Function.Embedding.subtype P) (Function.Embedding.subtype P)))
    (hblock : ∀ x y, ¬P x → P y → B x y = 0) :
    pRad B ≤ pRad (B.submatrix
      (Function.Embedding.subtype (fun x => ¬P x))
      (Function.Embedding.subtype (fun x => ¬P x))) := by
  set BS := B.submatrix (Function.Embedding.subtype P)
    (Function.Embedding.subtype P) with hBS
  set BC := B.submatrix (Function.Embedding.subtype (fun x => ¬P x))
    (Function.Embedding.subtype (fun x => ¬P x)) with hBC
  have hBSnn : EntryNonneg BS := fun x y => hB _ _
  have hBCnn : EntryNonneg BC := fun x y => hB _ _
  have hnil := pow_card_eq_zero_of_no_witness hBSnn hnilS
  have key : ∀ μ : ℝ, pRad BC < μ → pRad B ≤ μ := by
    intro μ hμ
    have hμpos : 0 < μ := lt_trans (pRad_pos BC) hμ
    obtain ⟨vC, hvC1, hvCsup⟩ := exists_supersolution hBCnn hwC hμ
    set u : {x // P x} → ℝ :=
      fun x => ∑ y : {y // ¬P y}, B x (y : V) * vC y with hu
    have hu0 : ∀ x, 0 ≤ u x := fun x =>
      Finset.sum_nonneg fun y _ => mul_nonneg (hB _ _)
        (le_trans zero_le_one (hvC1 y))
    obtain ⟨wS, hwSlb, hwSeq⟩ :=
      nilpotent_supersolution hBSnn hnil hμpos u hu0
    set w : V → ℝ := fun x =>
      if hx : P x then wS ⟨x, hx⟩ else vC ⟨x, hx⟩ with hwdef
    have hwpos : ∀ x, 0 < w x := by
      intro x
      simp only [hwdef]
      by_cases hx : P x
      · rw [dif_pos hx]
        refine lt_of_lt_of_le ?_ (hwSlb ⟨x, hx⟩)
        have := hu0 ⟨x, hx⟩
        positivity
      · rw [dif_neg hx]
        exact lt_of_lt_of_le zero_lt_one (hvC1 _)
    have hsup : ∀ x, B.mulVec w x ≤ μ * w x := by
      intro x
      have hsplit : B.mulVec w x
          = (∑ y : {y // P y}, B x (y : V) * wS y)
            + ∑ y : {y // ¬P y}, B x (y : V) * vC y := by
        rw [Matrix.mulVec, dotProduct,
          ← Fintype.sum_subtype_add_sum_subtype P
            (fun y => B x y * w y)]
        congr 1
        · refine Finset.sum_congr rfl fun y _ => ?_
          congr 1
          simp only [hwdef]
          rw [dif_pos y.2]
        · refine Finset.sum_congr rfl fun y _ => ?_
          congr 1
          simp only [hwdef]
          rw [dif_neg y.2]
      by_cases hx : P x
      · have hS : ∑ y : {y // P y}, B x (y : V) * wS y
            = BS.mulVec wS ⟨x, hx⟩ := by
          rw [Matrix.mulVec, dotProduct]
          rfl
        have hwx : w x = wS ⟨x, hx⟩ := by
          simp only [hwdef]
          rw [dif_pos hx]
        rw [hsplit, hS, hwx]
        have heq := hwSeq ⟨x, hx⟩
        have hux : u ⟨x, hx⟩
            = ∑ y : {y // ¬P y}, B x (y : V) * vC y := rfl
        rw [← hux]
        linarith [heq]
      · have hzero : ∑ y : {y // P y}, B x (y : V) * wS y = 0 :=
          Finset.sum_eq_zero fun y _ => by
            rw [hblock x y hx y.2, zero_mul]
        have hC : ∑ y : {y // ¬P y}, B x (y : V) * vC y
            = BC.mulVec vC ⟨x, hx⟩ := by
          rw [Matrix.mulVec, dotProduct]
          rfl
        have hwx : w x = vC ⟨x, hx⟩ := by
          simp only [hwdef]
          rw [dif_neg hx]
        rw [hsplit, hzero, zero_add, hC, hwx]
        exact hvCsup ⟨x, hx⟩
    exact pRad_le_of_supersolution hB hw hμpos hwpos hsup
  by_contra hcon
  push_neg at hcon
  have h1 := key ((pRad BC + pRad B) / 2) (by linarith)
  linarith

/-- **Second block nilpotent**: when no transition leads from `¬P`
back to `P` and the `¬P` block carries no diagonal witness, the
growth rate is dominated by the `P` block alone. -/
theorem pRad_le_of_nilpotent_second
    [Nonempty {x // P x}] [Nonempty {x // ¬P x}]
    {B : Matrix V V ℝ} (hB : EntryNonneg B) (hw : HasDiagWitness B)
    (hwS : HasDiagWitness (B.submatrix
      (Function.Embedding.subtype P) (Function.Embedding.subtype P)))
    (hnilC : ¬ HasDiagWitness (B.submatrix
      (Function.Embedding.subtype (fun x => ¬P x))
      (Function.Embedding.subtype (fun x => ¬P x))))
    (hblock : ∀ x y, ¬P x → P y → B x y = 0) :
    pRad B ≤ pRad (B.submatrix
      (Function.Embedding.subtype P) (Function.Embedding.subtype P)) := by
  set BS := B.submatrix (Function.Embedding.subtype P)
    (Function.Embedding.subtype P) with hBS
  set BC := B.submatrix (Function.Embedding.subtype (fun x => ¬P x))
    (Function.Embedding.subtype (fun x => ¬P x)) with hBC
  have hBSnn : EntryNonneg BS := fun x y => hB _ _
  have hBCnn : EntryNonneg BC := fun x y => hB _ _
  have hnil := pow_card_eq_zero_of_no_witness hBCnn hnilC
  have key : ∀ μ : ℝ, pRad BS < μ → pRad B ≤ μ := by
    intro μ hμ
    have hμpos : 0 < μ := lt_trans (pRad_pos BS) hμ
    set μ₁ : ℝ := (pRad BS + μ) / 2 with hμ₁
    have hμ₁pos : 0 < μ₁ := by
      have := pRad_pos BS
      rw [hμ₁]
      linarith
    have hSlt : pRad BS < μ₁ := by rw [hμ₁]; linarith
    have h1μ : μ₁ < μ := by rw [hμ₁]; linarith
    obtain ⟨vS, hvS1, hvSsup⟩ := exists_supersolution hBSnn hwS hSlt
    -- resolvent super-solution on the nilpotent block, `u = 0`
    obtain ⟨wC, hwClb, hwCeq⟩ :=
      nilpotent_supersolution hBCnn hnil hμpos (fun _ => 0)
        (fun _ => le_rfl)
    have hwC0 : ∀ y, 0 < wC y := fun y =>
      lt_of_lt_of_le (by positivity) (hwClb y)
    -- the cross bound
    set CT := Finset.univ.sup' Finset.univ_nonempty
      (fun x : V => ∑ y : {y // ¬P y}, B x (y : V) * wC y) with hCT
    have hCT0 : 0 ≤ CT := by
      rw [hCT]
      refine le_trans ?_ (Finset.le_sup'
        (f := fun x : V => ∑ y : {y // ¬P y}, B x (y : V) * wC y)
        (Finset.mem_univ (Classical.arbitrary V)))
      exact Finset.sum_nonneg fun y _ => mul_nonneg (hB _ _)
        (hwC0 y).le
    set t := CT / (μ - μ₁) + 1 with ht
    have ht1 : 1 ≤ t := by
      rw [ht]
      have h3 : 0 ≤ CT / (μ - μ₁) := div_nonneg hCT0 (by linarith)
      linarith
    set w : V → ℝ := fun x =>
      if hx : P x then t * vS ⟨x, hx⟩ else wC ⟨x, hx⟩ with hwdef
    have hwpos : ∀ x, 0 < w x := by
      intro x
      simp only [hwdef]
      by_cases hx : P x
      · rw [dif_pos hx]
        have h4 := hvS1 ⟨x, hx⟩
        nlinarith
      · rw [dif_neg hx]
        exact hwC0 _
    have hsup : ∀ x, B.mulVec w x ≤ μ * w x := by
      intro x
      have hsplit : B.mulVec w x
          = (∑ y : {y // P y}, B x (y : V) * (t * vS y))
            + ∑ y : {y // ¬P y}, B x (y : V) * wC y := by
        rw [Matrix.mulVec, dotProduct,
          ← Fintype.sum_subtype_add_sum_subtype P
            (fun y => B x y * w y)]
        congr 1
        · refine Finset.sum_congr rfl fun y _ => ?_
          congr 1
          simp only [hwdef]
          rw [dif_pos y.2]
        · refine Finset.sum_congr rfl fun y _ => ?_
          congr 1
          simp only [hwdef]
          rw [dif_neg y.2]
      by_cases hx : P x
      · have hS : ∑ y : {y // P y}, B x (y : V) * (t * vS y)
            = t * BS.mulVec vS ⟨x, hx⟩ := by
          rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          have h5 : BS ⟨x, hx⟩ y = B x (y : V) := rfl
          rw [h5]
          ring
        have hcross : ∑ y : {y // ¬P y}, B x (y : V) * wC y
            ≤ CT := by
          rw [hCT]
          exact Finset.le_sup'
            (f := fun x : V =>
              ∑ y : {y // ¬P y}, B x (y : V) * wC y)
            (Finset.mem_univ x)
        have hwx : w x = t * vS ⟨x, hx⟩ := by
          simp only [hwdef]
          rw [dif_pos hx]
        rw [hsplit, hS, hwx]
        have h6 : t * BS.mulVec vS ⟨x, hx⟩
            ≤ t * (μ₁ * vS ⟨x, hx⟩) :=
          mul_le_mul_of_nonneg_left (hvSsup _) (by linarith)
        have h7 := hvS1 ⟨x, hx⟩
        have heqt : (μ - μ₁) * t = CT + (μ - μ₁) := by
          rw [ht]
          have hne : μ - μ₁ ≠ 0 := by linarith
          field_simp
        nlinarith [mul_nonneg (mul_nonneg
          (show (0:ℝ) ≤ μ - μ₁ by linarith)
          (show (0:ℝ) ≤ t by linarith))
          (show (0:ℝ) ≤ vS ⟨x, hx⟩ - 1 by linarith)]
      · have hzero : ∑ y : {y // P y}, B x (y : V) * (t * vS y)
            = 0 :=
          Finset.sum_eq_zero fun y _ => by
            rw [hblock x y hx y.2, zero_mul]
        have hC : ∑ y : {y // ¬P y}, B x (y : V) * wC y
            = BC.mulVec wC ⟨x, hx⟩ := by
          rw [Matrix.mulVec, dotProduct]
          rfl
        have hwx : w x = wC ⟨x, hx⟩ := by
          simp only [hwdef]
          rw [dif_neg hx]
        rw [hsplit, hzero, zero_add, hC, hwx]
        have heq := hwCeq ⟨x, hx⟩
        linarith [heq]
    exact pRad_le_of_supersolution hB hw hμpos hwpos hsup
  by_contra hcon
  push_neg at hcon
  have h1 := key ((pRad BS + pRad B) / 2) (by linarith)
  linarith

end Nilpotent

/-! ## A minimal strongly connected component -/

/-- Every finite graph has a vertex whose component is minimal for
reachability: whatever reaches it is reached back. -/
theorem exists_min_vertex (adj : V → V → Prop) :
    ∃ x₀ : V, ∀ y, Condense.Reaches adj y x₀ →
      Condense.Reaches adj x₀ y := by
  obtain ⟨x₀, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun x => (Finset.univ.filter
      (fun z => Condense.Reaches adj z x)).card)
    Finset.univ_nonempty
  refine ⟨x₀, fun y hy => ?_⟩
  by_contra hxy
  -- the down-set of `y` is strictly smaller
  have hsub : Finset.univ.filter (fun z => Condense.Reaches adj z y)
      ⊆ Finset.univ.filter (fun z => Condense.Reaches adj z x₀) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨Finset.mem_univ z, hz.2.trans hy⟩
  have hne : x₀ ∈ Finset.univ.filter
      (fun z => Condense.Reaches adj z x₀) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ x₀, Relation.ReflTransGen.refl⟩
  have hnotin : x₀ ∉ Finset.univ.filter
      (fun z => Condense.Reaches adj z y) := by
    rw [Finset.mem_filter]
    intro h
    exact hxy h.2
  have hlt : (Finset.univ.filter
      (fun z => Condense.Reaches adj z y)).card
      < (Finset.univ.filter
        (fun z => Condense.Reaches adj z x₀)).card :=
    Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.mpr
      ⟨x₀, hne, hnotin⟩)
  exact absurd (hmin y (Finset.mem_univ y)) (not_le.mpr hlt)

/-! ## The main induction -/

/-- The inductive core: the growth rate of a nonnegative matrix with
a diagonal witness is bounded by the growth rate of the block of one
strongly connected component that itself carries a witness. -/
private theorem pRad_attained_aux : ∀ (n : ℕ) (V : Type u)
    [Fintype V] [DecidableEq V] [Nonempty V] (B : Matrix V V ℝ),
    Fintype.card V ≤ n → EntryNonneg B → HasDiagWitness B →
    ∃ x : V, HasDiagWitness (sccBlock B x)
      ∧ pRad B ≤ pRad (sccBlock B x) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ B hcard _ _
    exact absurd hcard (by
      have : 0 < Fintype.card V := Fintype.card_pos
      omega)
  | succ n ih =>
    intro V _ _ _ B hcard hB hw
    obtain ⟨x₀, hx₀min⟩ := exists_min_vertex (supportAdj B)
    set P : V → Prop :=
      fun y => Condense.Reaches (supportAdj B) y x₀ with hPdef
    have hPx₀ : P x₀ := Relation.ReflTransGen.refl
    -- no transition from `¬P` into `P`
    have hblock : ∀ x y, ¬P x → P y → B x y = 0 := by
      intro x y hnx hy
      by_contra hne
      have hpos : 0 < B x y := lt_of_le_of_ne (hB x y) (Ne.symm hne)
      exact hnx ((Relation.ReflTransGen.single
        (show supportAdj B x y from hpos)).trans hy)
    -- `¬P` is forward closed
    have hQclosed : ∀ a b, ¬P a → 0 < B a b → ¬P b := by
      intro a b ha hab hb
      exact ha ((Relation.ReflTransGen.single
        (show supportAdj B a b from hab)).trans hb)
    -- `P` is exactly the component of `x₀`
    have hPscc : ∀ y, P y ↔ sccMem B x₀ y := by
      intro y
      constructor
      · intro hy
        exact ⟨hx₀min y hy, hy⟩
      · intro hy
        exact hy.2
    by_cases hPall : ∀ y, P y
    · -- one single component: reindex
      have hall : ∀ y, sccMem B x₀ y := fun y => (hPscc y).mp (hPall y)
      have hmat : sccBlock B x₀
          = B.submatrix ⇑(Equiv.subtypeUnivEquiv hall)
              ⇑(Equiv.subtypeUnivEquiv hall) := by
        ext a b
        rfl
      refine ⟨x₀, ?_, ?_⟩
      · rw [hmat]
        exact hasDiagWitness_submatrix_equiv _ hw
      · rw [hmat, pRad_submatrix_equiv]
    · push_neg at hPall
      obtain ⟨x₁, hx₁⟩ := hPall
      haveI : Nonempty {y // ¬P y} := ⟨⟨x₁, hx₁⟩⟩
      haveI : Nonempty {y // P y} := ⟨⟨x₀, hPx₀⟩⟩
      set BS := B.submatrix (Function.Embedding.subtype P)
        (Function.Embedding.subtype P) with hBSdef
      set BC := B.submatrix
        (Function.Embedding.subtype (fun y => ¬P y))
        (Function.Embedding.subtype (fun y => ¬P y)) with hBCdef
      have hBSnn : EntryNonneg BS := fun x y => hB _ _
      have hBCnn : EntryNonneg BC := fun x y => hB _ _
      have hcardC : Fintype.card {y // ¬P y} ≤ n := by
        have h1 : Fintype.card {y // ¬P y} < Fintype.card V :=
          Fintype.card_subtype_lt (x := x₀) (by
            intro h
            exact h hPx₀)
        omega
      -- the `P` block is range-congruent to the component block
      have hrangeS : Set.range
          ⇑(Function.Embedding.subtype (sccMem B x₀))
          = Set.range ⇑(Function.Embedding.subtype P) := by
        rw [Function.Embedding.coe_subtype,
          Function.Embedding.coe_subtype,
          Subtype.range_coe_subtype, Subtype.range_coe_subtype]
        exact Set.ext fun y => (hPscc y).symm
      have hsccS : sccBlock B x₀
          = B.submatrix
              ⇑(Function.Embedding.subtype (sccMem B x₀))
              ⇑(Function.Embedding.subtype (sccMem B x₀)) := rfl
      -- conclusion when the bound lands on the `P` block
      have hconclS : HasDiagWitness BS → pRad B ≤ pRad BS →
          ∃ x : V, HasDiagWitness (sccBlock B x)
            ∧ pRad B ≤ pRad (sccBlock B x) := by
        intro hwS hle
        refine ⟨x₀, ?_, ?_⟩
        · rw [hsccS]
          exact hasDiagWitness_submatrix_range_congr _ _ hrangeS hwS
        · rw [hsccS, pRad_submatrix_range_congr _ _ hrangeS]
          exact hle
      -- conclusion when the bound lands on the `¬P` block: recurse
      have hconclC : HasDiagWitness BC → pRad B ≤ pRad BC →
          ∃ x : V, HasDiagWitness (sccBlock B x)
            ∧ pRad B ≤ pRad (sccBlock B x) := by
        intro hwC hle
        obtain ⟨x', hwx', hbound'⟩ :=
          ih {y // ¬P y} BC hcardC hBCnn hwC
        -- identify the component of `x'` inside `¬P` with the
        -- ambient component of `x'.val`
        have hkey : ∀ w : V,
            (∃ hw : ¬P w, sccMem BC x' ⟨w, hw⟩)
              ↔ sccMem B x'.val w := by
          intro w
          constructor
          · rintro ⟨hw, hm1, hm2⟩
            exact ⟨reaches_of_restrict hm1, reaches_of_restrict hm2⟩
          · rintro ⟨h1, h2⟩
            obtain ⟨hwQ, h1'⟩ := reaches_restrict hQclosed x'.2 h1
            obtain ⟨hx'Q, h2'⟩ := reaches_restrict hQclosed hwQ h2
            refine ⟨hwQ, ?_, ?_⟩
            · have hx'eq : (⟨x'.val, x'.2⟩ : {y // ¬P y}) = x' :=
                Subtype.ext rfl
              rwa [hx'eq] at h1'
            · have hx'eq : (⟨x'.val, hx'Q⟩ : {y // ¬P y}) = x' :=
                Subtype.ext rfl
              rwa [hx'eq] at h2'
        -- the composite embedding of the recursive component
        set e₂ : {w // sccMem BC x' w} ↪ V :=
          (Function.Embedding.subtype (sccMem BC x')).trans
            (Function.Embedding.subtype (fun y => ¬P y)) with he₂
        have hrange : Set.range
            ⇑(Function.Embedding.subtype (sccMem B x'.val))
            = Set.range ⇑e₂ := by
          ext w
          rw [Function.Embedding.coe_subtype,
            Subtype.range_coe_subtype]
          simp only [he₂, Function.Embedding.trans,
            Function.Embedding.coe_subtype, Set.mem_range,
            Set.mem_setOf_eq, Function.Embedding.coeFn_mk,
            Function.comp_apply]
          constructor
          · intro hm
            obtain ⟨hw, hm'⟩ := (hkey w).mpr hm
            exact ⟨⟨⟨w, hw⟩, hm'⟩, rfl⟩
          · rintro ⟨⟨⟨w', hw'⟩, hm'⟩, rfl⟩
            exact (hkey w').mp ⟨hw', hm'⟩
        have hmat2 : B.submatrix ⇑e₂ ⇑e₂ = sccBlock BC x' := by
          ext a b
          rfl
        refine ⟨x'.val, ?_, ?_⟩
        · show HasDiagWitness (B.submatrix
            ⇑(Function.Embedding.subtype (sccMem B x'.val))
            ⇑(Function.Embedding.subtype (sccMem B x'.val)))
          refine hasDiagWitness_submatrix_range_congr _ e₂ hrange ?_
          rw [hmat2]
          exact hwx'
        · show pRad B ≤ pRad (B.submatrix
            ⇑(Function.Embedding.subtype (sccMem B x'.val))
            ⇑(Function.Embedding.subtype (sccMem B x'.val)))
          rw [pRad_submatrix_range_congr _ e₂ hrange, hmat2]
          exact le_trans hle hbound'
      by_cases hwC : HasDiagWitness BC
      · by_cases hwS : HasDiagWitness BS
        · -- both blocks carry witnesses: two-block bound
          have hmain := pRad_blockTriangular_le (P := P)
            hB hw hwS hwC hblock
          rcases le_total (pRad BC) (pRad BS) with hmax | hmax
          · exact hconclS hwS (by
              rw [max_eq_left hmax] at hmain
              exact hmain)
          · exact hconclC hwC (by
              rw [max_eq_right hmax] at hmain
              exact hmain)
        · -- `P` block nilpotent
          exact hconclC hwC
            (pRad_le_of_nilpotent_first hB hw hwC hwS hblock)
      · -- `¬P` block nilpotent: the witness of `B` localizes in `P`
        obtain ⟨xw, m, hm, hpos⟩ := hw
        by_cases hxwP : P xw
        · -- component of the witness is the component of `x₀`
          have hbw : HasDiagWitness (sccBlock B xw) :=
            hasDiagWitness_sccBlock hB hm hpos
          have hcompeq : ∀ y, sccMem B xw y ↔ sccMem B x₀ y := by
            intro y
            have hx₀xw : sccMem B x₀ xw := (hPscc xw).mp hxwP
            constructor
            · intro hy
              exact (Condense.mutualReach_equivalence
                (supportAdj B)).trans hx₀xw hy
            · intro hy
              exact (Condense.mutualReach_equivalence
                (supportAdj B)).trans
                ((Condense.mutualReach_equivalence
                  (supportAdj B)).symm hx₀xw) hy
          have hrangeW : Set.range
              ⇑(Function.Embedding.subtype P)
              = Set.range
                  ⇑(Function.Embedding.subtype (sccMem B xw)) := by
            rw [Function.Embedding.coe_subtype,
              Function.Embedding.coe_subtype,
              Subtype.range_coe_subtype, Subtype.range_coe_subtype]
            exact Set.ext fun y => by
              rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hPscc y,
                ← hcompeq y]
          have hwS : HasDiagWitness BS :=
            hasDiagWitness_submatrix_range_congr _ _ hrangeW hbw
          exact hconclS hwS
            (pRad_le_of_nilpotent_second hB
              ⟨xw, m, hm, hpos⟩ hwS hwC hblock)
        · -- the witness would localize inside the nilpotent block
          exfalso
          have hc := chain_of_pow_pos hB m xw xw hpos
          obtain ⟨hy, hc'⟩ := chain_restrict hQclosed hxwP hc
          have hend : (⟨xw, hy⟩ : {y // ¬P y}) = ⟨xw, hxwP⟩ :=
            Subtype.ext rfl
          rw [hend] at hc'
          exact hwC ⟨⟨xw, hxwP⟩, m, hm,
            pow_pos_of_chain hBCnn hc'⟩

/-- **Clause (ii) of `prop:terminal-component`, attained maximum**:
the growth rate of a nonnegative matrix with a diagonal witness
equals the growth rate of the block of one strongly connected
component of its support graph, and that block carries a diagonal
witness. -/
theorem pRad_attained_on_component {B : Matrix V V ℝ}
    (hB : EntryNonneg B) (hw : HasDiagWitness B) :
    ∃ x : V, HasDiagWitness (sccBlock B x)
      ∧ pRad B = pRad (sccBlock B x) := by
  obtain ⟨x, hwx, hle⟩ :=
    pRad_attained_aux (Fintype.card V) V B le_rfl hB hw
  exact ⟨x, hwx, le_antisymm hle (pRad_submatrix_le hB _ hwx hw)⟩

/-- **Clause (ii), domination half**: every component block carrying
a witness is dominated by the full growth rate, so together with
`pRad_attained_on_component` the growth rate is the maximum of the
component growth rates. -/
theorem pRad_sccBlock_le {B : Matrix V V ℝ} (hB : EntryNonneg B)
    (hw : HasDiagWitness B) (x : V)
    (hwx : HasDiagWitness (sccBlock B x)) :
    pRad (sccBlock B x) ≤ pRad B :=
  pRad_submatrix_le hB _ hwx hw

end NCG
