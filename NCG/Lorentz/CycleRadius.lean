/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.BlockRadius

/-!
# Noncycle supercriticality of the depth transfer

`lem:app-rho-one-cycle` of the flagship manuscript: a strongly
connected directed multigraph has growth rate (spectral radius) one
exactly when it is a single directed cycle.  In the Gelfand–Fekete
implementation `pRad` this becomes the outdegree dichotomy proved
here:

* `diag_le_pRad_pow` — a diagonal entry `θ ≤ (A^c)_{xx}` forces
  `θ ≤ pRad A ^ c` (the growth limit evaluated along the subsequence
  `k ↦ k·c` dominates `log θ / c`);
* `one_lt_pRad_of_two_le_diag` — a diagonal entry `≥ 2` at some
  positive power forces `pRad A > 1`;
* `one_lt_pRad_of_branching` — a strongly connected multigraph with
  a **branch vertex** (two distinct outgoing edges at one vertex) has
  `pRad > 1`: the two return loops through the branch pad to a common
  length, giving a diagonal entry `≥ 2`;
* `pRad_eq_one_of_outdeg_le_one` — conversely, outdegree at most one
  everywhere (with an edge and strong connectivity) forces
  `pRad = 1`, the single-cycle phase.

Under strong connectivity, "not a single directed cycle" is exactly
"some vertex has two distinct outgoing edges", so the two statements
together are the manuscript's dichotomy.  The corollaries
`one_lt_pressureRate_zero_of_branching` and
`exists_unique_pressure_root_of_branching` discharge the
supercriticality hypothesis `1 < r(0)` of `pressure_selects_beta`
from the branching phase criterion (P1), completing
`thm:signed-clock`(iv) for the unweighted depth transfer `B(s)` and,
more generally, for capacities `q ≥ 1`.
-/

namespace NCG

open Filter

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E]

/-! ## Entry chain bounds -/

/-- Off-diagonal analogue of `diag_pow_add`: a two-leg walk bound
`(A^j)_{xz} (A^k)_{zy} ≤ (A^{j+k})_{xy}` for entrywise-nonnegative
`A`. -/
theorem entry_pow_chain {A : Matrix V V ℝ} (hA : EntryNonneg A)
    (x z y : V) (j k : ℕ) :
    (A ^ j) x z * (A ^ k) z y ≤ (A ^ (j + k)) x y := by
  rw [pow_add, Matrix.mul_apply]
  exact Finset.single_le_sum
    (f := fun w => (A ^ j) x w * (A ^ k) w y)
    (fun w _ => mul_nonneg (entryNonneg_pow hA j x w)
      (entryNonneg_pow hA k w y))
    (Finset.mem_univ z)

/-- Two distinct first steps contribute additively to a diagonal
entry: for `u ≠ v`,
`A_{xu}(A^n)_{ux} + A_{xv}(A^n)_{vx} ≤ (A^{n+1})_{xx}`. -/
theorem two_branch_diag {A : Matrix V V ℝ} (hA : EntryNonneg A)
    {u v : V} (huv : u ≠ v) (x : V) (n : ℕ) :
    A x u * (A ^ n) u x + A x v * (A ^ n) v x
      ≤ (A ^ (n + 1)) x x := by
  rw [pow_succ', Matrix.mul_apply]
  have hpair : ∑ w ∈ ({u, v} : Finset V),
      A x w * (A ^ n) w x
      = A x u * (A ^ n) u x + A x v * (A ^ n) v x :=
    Finset.sum_pair huv
  calc A x u * (A ^ n) u x + A x v * (A ^ n) v x
      = ∑ w ∈ ({u, v} : Finset V), A x w * (A ^ n) w x :=
        hpair.symm
    _ ≤ ∑ w, A x w * (A ^ n) w x :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _)
          (fun w _ _ => mul_nonneg (hA x w)
            (entryNonneg_pow hA n w x))

/-- A unit diagonal entry propagates along multiples:
`1 ≤ (A^a)_{xx}` gives `1 ≤ (A^{k a})_{xx}` for every `k`. -/
theorem one_le_diag_pow_mul {A : Matrix V V ℝ}
    (hA : EntryNonneg A) {x : V} {a : ℕ}
    (h : 1 ≤ (A ^ a) x x) :
    ∀ k : ℕ, 1 ≤ (A ^ (k * a)) x x := by
  intro k
  induction k with
  | zero => simp
  | succ j ih =>
    have h1 : (j + 1) * a = j * a + a := by ring
    rw [h1]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (A ^ (j * a)) x x * (A ^ a) x x :=
          mul_le_mul ih h one_pos.le (le_trans one_pos.le ih)
      _ ≤ (A ^ (j * a + a)) x x := diag_pow_add hA x _ _

/-! ## Diagonal lower bounds for the growth rate -/

/-- **Diagonal lower bound for the Gelfand–Fekete rate**: a diagonal
entry `θ ≤ (A^c)_{xx}` with `θ ≥ 1`, `c ≥ 1` forces
`θ ≤ pRad A ^ c`.  The growth limit is evaluated along the
subsequence `k ↦ k·c`, where diagonal supermultiplicativity gives
`θ^k ≤ entrySum (A^{k c})`. -/
theorem diag_le_pRad_pow [Nonempty V] {A : Matrix V V ℝ}
    (hA : EntryNonneg A) {x : V} {c : ℕ} {θ : ℝ}
    (hc : 0 < c) (hθ : 1 ≤ θ) (hd : θ ≤ (A ^ c) x x) :
    θ ≤ pRad A ^ c := by
  have hθ0 : (0 : ℝ) < θ := lt_of_lt_of_le one_pos hθ
  have hdpos : 0 < (A ^ c) x x := lt_of_lt_of_le hθ0 hd
  have hw : HasDiagWitness A := ⟨x, c, hc, hdpos⟩
  have htend := tendsto_growthSeq hA hw
  -- the subsequence `k ↦ k * c` tends to infinity
  have hmul : Tendsto (fun k : ℕ => k * c) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => ?_⟩
    calc b ≤ k := hk
      _ ≤ k * c := Nat.le_mul_of_pos_right k hc
  have hsub : Tendsto
      (fun k : ℕ => growthSeq A (k * c) / ((k * c : ℕ) : ℝ))
      atTop (nhds (Real.log (pRad A))) := by
    simpa [Function.comp_def] using htend.comp hmul
  -- every subsequence term with `k ≥ 1` dominates `log θ / c`
  have hbound : ∀ᶠ k : ℕ in atTop,
      Real.log θ / (c : ℝ)
        ≤ growthSeq A (k * c) / ((k * c : ℕ) : ℝ) := by
    refine eventually_atTop.mpr ⟨1, fun k hk => ?_⟩
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    have h1 : θ ^ k ≤ (A ^ (k * c)) x x := by
      calc θ ^ k ≤ ((A ^ c) x x) ^ k :=
            pow_le_pow_left₀ hθ0.le hd k
        _ ≤ (A ^ (k * c)) x x := diag_pow_mul_pos hA hdpos k hk
    have h2 : θ ^ k ≤ entrySum (A ^ (k * c)) :=
      le_trans h1 (le_entrySum (entryNonneg_pow hA _) x x)
    have h3 : (k : ℝ) * Real.log θ ≤ growthSeq A (k * c) := by
      have hlog : Real.log (θ ^ k)
          ≤ Real.log (entrySum (A ^ (k * c))) :=
        Real.log_le_log (pow_pos hθ0 k) h2
      rwa [Real.log_pow] at hlog
    push_cast
    rw [div_le_div_iff₀ hcpos (mul_pos hkpos hcpos)]
    calc Real.log θ * ((k : ℝ) * (c : ℝ))
        = ((k : ℝ) * Real.log θ) * (c : ℝ) := by ring
      _ ≤ growthSeq A (k * c) * (c : ℝ) :=
          mul_le_mul_of_nonneg_right h3 hcpos.le
  have hlim : Real.log θ / (c : ℝ) ≤ Real.log (pRad A) :=
    ge_of_tendsto hsub hbound
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  calc θ = Real.exp (Real.log θ) := (Real.exp_log hθ0).symm
    _ ≤ Real.exp ((c : ℝ) * Real.log (pRad A)) := by
        refine Real.exp_le_exp.mpr ?_
        have h4 := (div_le_iff₀ hcpos).mp hlim
        linarith
    _ = pRad A ^ c := by
        rw [Real.exp_nat_mul, Real.exp_log (pRad_pos A)]

/-- A diagonal entry `≥ 2` at a positive power forces a
supercritical growth rate. -/
theorem one_lt_pRad_of_two_le_diag [Nonempty V]
    {A : Matrix V V ℝ} (hA : EntryNonneg A) {x : V} {c : ℕ}
    (hc : 0 < c) (hd : (2 : ℝ) ≤ (A ^ c) x x) :
    1 < pRad A := by
  by_contra hle
  push Not at hle
  have h2 : (2 : ℝ) ≤ pRad A ^ c :=
    diag_le_pRad_pow hA hc one_le_two hd
  have h1 : pRad A ^ c ≤ 1 := pow_le_one₀ (pRad_pos A).le hle
  linarith

/-- A unit diagonal entry at a positive power forces a critical or
supercritical growth rate. -/
theorem one_le_pRad_of_one_le_diag [Nonempty V]
    {A : Matrix V V ℝ} (hA : EntryNonneg A) {x : V} {c : ℕ}
    (hc : 0 < c) (hd : (1 : ℝ) ≤ (A ^ c) x x) :
    1 ≤ pRad A := by
  by_contra hlt
  push Not at hlt
  have h2 : (1 : ℝ) ≤ pRad A ^ c :=
    diag_le_pRad_pow hA hc le_rfl hd
  have h1 : pRad A ^ c < 1 :=
    pow_lt_one₀ (pRad_pos A).le hlt hc.ne'
  linarith

/-! ## The edge-count adjacency matrix and walks -/

/-- Edge-count adjacency matrix of the resolved multigraph
`(E, src, tgt)`: the `(x,y)` entry is the number of edges `x → y`.
This is the unweighted depth transfer `B(0)` of
`thm:signed-clock`(iv). -/
noncomputable def edgeCountMatrix (src tgt : E → V) :
    Matrix V V ℝ :=
  Matrix.of fun x y =>
    (((Finset.univ.filter fun e => src e = x ∧ tgt e = y).card : ℕ)
      : ℝ)

omit [Fintype V] in
theorem edgeCountMatrix_nonneg (src tgt : E → V) :
    EntryNonneg (edgeCountMatrix src tgt) :=
  fun _ _ => Nat.cast_nonneg _

omit [Fintype V] in
theorem one_le_edgeCountMatrix {src tgt : E → V} {e : E}
    {x y : V} (hs : src e = x) (ht : tgt e = y) :
    (1 : ℝ) ≤ edgeCountMatrix src tgt x y := by
  have hmem : e ∈ Finset.univ.filter
      fun e => src e = x ∧ tgt e = y :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ e, hs, ht⟩
  have hcard : 1 ≤ (Finset.univ.filter
      fun e => src e = x ∧ tgt e = y).card :=
    Finset.card_pos.mpr ⟨e, hmem⟩
  simp only [edgeCountMatrix, Matrix.of_apply]
  exact_mod_cast hcard

omit [Fintype V] in
theorem two_le_edgeCountMatrix {src tgt : E → V} {e₁ e₂ : E}
    (hne : e₁ ≠ e₂) {x y : V} (hs₁ : src e₁ = x)
    (ht₁ : tgt e₁ = y) (hs₂ : src e₂ = x) (ht₂ : tgt e₂ = y) :
    (2 : ℝ) ≤ edgeCountMatrix src tgt x y := by
  have h₁ : e₁ ∈ Finset.univ.filter
      fun e => src e = x ∧ tgt e = y :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs₁, ht₁⟩
  have h₂ : e₂ ∈ Finset.univ.filter
      fun e => src e = x ∧ tgt e = y :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs₂, ht₂⟩
  have hcard : 1 < (Finset.univ.filter
      fun e => src e = x ∧ tgt e = y).card :=
    Finset.one_lt_card.mpr ⟨e₁, h₁, e₂, h₂, hne⟩
  simp only [edgeCountMatrix, Matrix.of_apply]
  exact_mod_cast hcard

/-- A directed walk of a given length in the multigraph
`(E, src, tgt)`. -/
inductive ReachesIn (src tgt : E → V) : ℕ → V → V → Prop
  | refl (x : V) : ReachesIn src tgt 0 x x
  | tail {n : ℕ} {x : V} (e : E)
      (h : ReachesIn src tgt n x (src e)) :
      ReachesIn src tgt (n + 1) x (tgt e)

/-- A walk of length `n` gives a unit lower bound on the
corresponding entry of the `n`-th adjacency power. -/
theorem one_le_pow_edgeCountMatrix {src tgt : E → V}
    {n : ℕ} {x y : V} (h : ReachesIn src tgt n x y) :
    (1 : ℝ) ≤ (edgeCountMatrix src tgt ^ n) x y := by
  induction h with
  | refl x => simp
  | @tail n x e h ih =>
    have hedge : (1 : ℝ)
        ≤ edgeCountMatrix src tgt (src e) (tgt e) :=
      one_le_edgeCountMatrix rfl rfl
    have hchain := entry_pow_chain
      (edgeCountMatrix_nonneg src tgt) x (src e) (tgt e) n 1
    rw [pow_one] at hchain
    have h1 : (1 : ℝ)
        ≤ (edgeCountMatrix src tgt ^ n) x (src e)
          * edgeCountMatrix src tgt (src e) (tgt e) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ _ := mul_le_mul ih hedge one_pos.le
              (le_trans one_pos.le ih)
    linarith

/-- Strong connectivity: every ordered pair of vertices is joined by
a directed walk. -/
def IsStronglyConnected (src tgt : E → V) : Prop :=
  ∀ x y : V, ∃ n : ℕ, ReachesIn src tgt n x y

/-! ## The branching (noncycle) theorem -/

/-- A one-edge loop bound: an edge `x → y` and a return walk
`y →ⁿ x` give a unit diagonal entry at power `1 + n`. -/
theorem one_le_diag_of_edge_walk {src tgt : E → V} {e : E}
    {r : ℕ} (hr : ReachesIn src tgt r (tgt e) (src e)) :
    (1 : ℝ)
      ≤ (edgeCountMatrix src tgt ^ (1 + r)) (src e) (src e) := by
  have hchain := entry_pow_chain (edgeCountMatrix_nonneg src tgt)
    (src e) (tgt e) (src e) 1 r
  rw [pow_one] at hchain
  have h1 : (1 : ℝ)
      ≤ edgeCountMatrix src tgt (src e) (tgt e)
        * (edgeCountMatrix src tgt ^ r) (tgt e) (src e) := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (one_le_edgeCountMatrix rfl rfl)
            (one_le_pow_edgeCountMatrix hr) one_pos.le
            (le_trans one_pos.le (one_le_edgeCountMatrix rfl rfl))
  linarith

/-- Any edge together with strong connectivity supplies a diagonal
witness for the adjacency matrix. -/
theorem hasDiagWitness_edgeCountMatrix {src tgt : E → V}
    (hconn : IsStronglyConnected src tgt) (e : E) :
    HasDiagWitness (edgeCountMatrix src tgt) := by
  obtain ⟨r, hr⟩ := hconn (tgt e) (src e)
  exact ⟨src e, 1 + r, by omega,
    lt_of_lt_of_le one_pos (one_le_diag_of_edge_walk hr)⟩

/-- **Branching supercriticality** (`lem:app-rho-one-cycle`, forward
direction): a strongly connected multigraph with two distinct edges
out of one vertex has adjacency growth rate strictly above one.  The
two return loops through the branch vertex are padded to the common
length `a·b`, producing a diagonal entry `≥ 2`. -/
theorem one_lt_pRad_of_branching [Nonempty V]
    {src tgt : E → V} (hconn : IsStronglyConnected src tgt)
    {e₁ e₂ : E} (hne : e₁ ≠ e₂) (hsrc : src e₁ = src e₂) :
    1 < pRad (edgeCountMatrix src tgt) := by
  have hAnn : EntryNonneg (edgeCountMatrix src tgt) :=
    edgeCountMatrix_nonneg src tgt
  by_cases hy : tgt e₁ = tgt e₂
  · -- parallel branch: a double edge and one return walk
    obtain ⟨r, hr⟩ := hconn (tgt e₁) (src e₁)
    have hdouble : (2 : ℝ)
        ≤ edgeCountMatrix src tgt (src e₁) (tgt e₁) :=
      two_le_edgeCountMatrix hne rfl rfl hsrc.symm hy.symm
    have hchain := entry_pow_chain hAnn
      (src e₁) (tgt e₁) (src e₁) 1 r
    rw [pow_one] at hchain
    have h2 : (2 : ℝ)
        ≤ (edgeCountMatrix src tgt ^ (1 + r)) (src e₁) (src e₁) := by
      have hmul : (2 : ℝ) * 1
          ≤ edgeCountMatrix src tgt (src e₁) (tgt e₁)
            * (edgeCountMatrix src tgt ^ r) (tgt e₁) (src e₁) :=
        mul_le_mul hdouble (one_le_pow_edgeCountMatrix hr)
          one_pos.le (le_trans (by norm_num) hdouble)
      linarith
    exact one_lt_pRad_of_two_le_diag hAnn (by omega) h2
  · -- genuine branch: pad the two loops to the common length
    obtain ⟨r₁, hr₁⟩ := hconn (tgt e₁) (src e₁)
    obtain ⟨r₂, hr₂⟩ := hconn (tgt e₂) (src e₁)
    -- unit loops of lengths `1+r₁` and `1+r₂` at the branch vertex
    have hloopa : (1 : ℝ) ≤ (edgeCountMatrix src tgt ^ (1 + r₁))
        (src e₁) (src e₁) := one_le_diag_of_edge_walk hr₁
    have hloopb : (1 : ℝ) ≤ (edgeCountMatrix src tgt ^ (1 + r₂))
        (src e₁) (src e₁) := by
      have := one_le_diag_of_edge_walk (e := e₂)
        (by rwa [← hsrc] : ReachesIn src tgt r₂ (tgt e₂) (src e₂))
      rwa [← hsrc] at this
    -- both return legs stretch to length `(1+r₁)(1+r₂) − 1`
    have key1 : (1 + r₁) * (1 + r₂) - 1 = r₁ + r₂ * (1 + r₁) := by
      have h : (1 + r₁) * (1 + r₂)
          = (r₁ + r₂ * (1 + r₁)) + 1 := by ring
      omega
    have key2 : (1 + r₁) * (1 + r₂) - 1 = r₂ + r₁ * (1 + r₂) := by
      have h : (1 + r₁) * (1 + r₂)
          = (r₂ + r₁ * (1 + r₂)) + 1 := by ring
      omega
    have hleg1 : (1 : ℝ)
        ≤ (edgeCountMatrix src tgt ^ ((1 + r₁) * (1 + r₂) - 1))
            (tgt e₁) (src e₁) := by
      rw [key1]
      have hpad : (1 : ℝ)
          ≤ (edgeCountMatrix src tgt ^ (r₂ * (1 + r₁)))
              (src e₁) (src e₁) :=
        one_le_diag_pow_mul hAnn hloopa r₂
      have hchain := entry_pow_chain hAnn (tgt e₁) (src e₁)
        (src e₁) r₁ (r₂ * (1 + r₁))
      have hmul : (1 : ℝ) * 1
          ≤ (edgeCountMatrix src tgt ^ r₁) (tgt e₁) (src e₁)
            * (edgeCountMatrix src tgt ^ (r₂ * (1 + r₁)))
                (src e₁) (src e₁) :=
        mul_le_mul (one_le_pow_edgeCountMatrix hr₁) hpad
          one_pos.le
          (le_trans one_pos.le (one_le_pow_edgeCountMatrix hr₁))
      linarith
    have hleg2 : (1 : ℝ)
        ≤ (edgeCountMatrix src tgt ^ ((1 + r₁) * (1 + r₂) - 1))
            (tgt e₂) (src e₁) := by
      rw [key2]
      have hpad : (1 : ℝ)
          ≤ (edgeCountMatrix src tgt ^ (r₁ * (1 + r₂)))
              (src e₁) (src e₁) :=
        one_le_diag_pow_mul hAnn hloopb r₁
      have hchain := entry_pow_chain hAnn (tgt e₂) (src e₁)
        (src e₁) r₂ (r₁ * (1 + r₂))
      have hmul : (1 : ℝ) * 1
          ≤ (edgeCountMatrix src tgt ^ r₂) (tgt e₂) (src e₁)
            * (edgeCountMatrix src tgt ^ (r₁ * (1 + r₂)))
                (src e₁) (src e₁) :=
        mul_le_mul (one_le_pow_edgeCountMatrix hr₂) hpad
          one_pos.le
          (le_trans one_pos.le (one_le_pow_edgeCountMatrix hr₂))
      linarith
    -- the two branches add on the diagonal at the common length
    have hprod : 1 ≤ (1 + r₁) * (1 + r₂) :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
    have hstep := two_branch_diag hAnn hy (src e₁)
      ((1 + r₁) * (1 + r₂) - 1)
    rw [show (1 + r₁) * (1 + r₂) - 1 + 1
        = (1 + r₁) * (1 + r₂) by omega] at hstep
    have hedge₁ : (1 : ℝ)
        ≤ edgeCountMatrix src tgt (src e₁) (tgt e₁) :=
      one_le_edgeCountMatrix rfl rfl
    have hedge₂ : (1 : ℝ)
        ≤ edgeCountMatrix src tgt (src e₁) (tgt e₂) :=
      one_le_edgeCountMatrix hsrc.symm rfl
    have hsum : (2 : ℝ)
        ≤ (edgeCountMatrix src tgt ^ ((1 + r₁) * (1 + r₂)))
            (src e₁) (src e₁) := by
      have h₁ : (1 : ℝ) * 1
          ≤ edgeCountMatrix src tgt (src e₁) (tgt e₁)
            * (edgeCountMatrix src tgt ^ ((1 + r₁) * (1 + r₂) - 1))
                (tgt e₁) (src e₁) :=
        mul_le_mul hedge₁ hleg1 one_pos.le
          (le_trans one_pos.le hedge₁)
      have h₂ : (1 : ℝ) * 1
          ≤ edgeCountMatrix src tgt (src e₁) (tgt e₂)
            * (edgeCountMatrix src tgt ^ ((1 + r₁) * (1 + r₂) - 1))
                (tgt e₂) (src e₁) :=
        mul_le_mul hedge₂ hleg2 one_pos.le
          (le_trans one_pos.le hedge₂)
      linarith
    exact one_lt_pRad_of_two_le_diag hAnn (by omega) hsum

/-! ## The single-cycle converse -/

/-- Row sums of the adjacency matrix are the outdegrees. -/
theorem edgeCountMatrix_rowSum (src tgt : E → V) (x : V) :
    ∑ y, edgeCountMatrix src tgt x y
      = ((Finset.univ.filter fun e => src e = x).card : ℝ) := by
  simp only [edgeCountMatrix, Matrix.of_apply]
  rw [← Nat.cast_sum]
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise
    (f := tgt) (t := Finset.univ)
    (fun e _ => Finset.mem_univ (tgt e))]
  refine (Finset.sum_congr rfl fun y _ => ?_).symm
  rw [Finset.filter_filter]

/-- **Single-cycle criticality** (`lem:app-rho-one-cycle`, converse
direction): outdegree at most one everywhere — the cycle phase under
strong connectivity — pins the growth rate at one. -/
theorem pRad_eq_one_of_outdeg_le_one [Nonempty V]
    {src tgt : E → V}
    (hconn : IsStronglyConnected src tgt) (e : E)
    (hout : ∀ x : V,
      (Finset.univ.filter fun e => src e = x).card ≤ 1) :
    pRad (edgeCountMatrix src tgt) = 1 := by
  have hAnn := edgeCountMatrix_nonneg (V := V) src tgt
  have hw := hasDiagWitness_edgeCountMatrix hconn e
  refine le_antisymm ?_ ?_
  · -- the constant vector `1` is a super-solution at `μ = 1`
    refine pRad_le_of_supersolution hAnn hw one_pos
      (v := fun _ => 1) (fun _ => one_pos) fun x => ?_
    have hmv : (edgeCountMatrix src tgt).mulVec
        (fun _ => (1 : ℝ)) x
        = ∑ y, edgeCountMatrix src tgt x y := by
      simp [Matrix.mulVec, dotProduct]
    rw [hmv, edgeCountMatrix_rowSum src tgt x, mul_one]
    exact_mod_cast hout x
  · -- a closed walk gives a unit diagonal entry
    obtain ⟨r, hr⟩ := hconn (tgt e) (src e)
    exact one_le_pRad_of_one_le_diag hAnn (by omega)
      (one_le_diag_of_edge_walk hr)

/-! ## Discharging the supercritical pressure hypothesis -/

variable {src tgt : E → V} {q ℓ : E → ℝ}

omit [Fintype V] in
/-- At `s = 0`, capacities `q ≥ 1` dominate the edge count. -/
theorem edgeCountMatrix_le_pressureKernel_zero
    (hq : ∀ e, 1 ≤ q e) (x y : V) :
    edgeCountMatrix src tgt x y
      ≤ pressureKernel src tgt q ℓ 0 x y := by
  simp only [edgeCountMatrix, pressureKernel, Matrix.of_apply,
    zero_mul, neg_zero, Real.exp_zero, mul_one]
  calc (((Finset.univ.filter
        fun e => src e = x ∧ tgt e = y).card : ℕ) : ℝ)
      = ∑ _e ∈ Finset.univ.filter
          (fun e => src e = x ∧ tgt e = y), (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ e ∈ Finset.univ.filter
          (fun e => src e = x ∧ tgt e = y), q e :=
        Finset.sum_le_sum fun e _ => hq e

/-- **Supercriticality from branching**: in the branching strongly
connected phase, any transfer with capacities `q ≥ 1` (in particular
the unweighted depth transfer `B`) is supercritical at `s = 0`.  This
discharges the hypothesis `1 < r(0)` of `pressure_selects_beta`. -/
theorem one_lt_pressureRate_zero_of_branching [Nonempty V]
    (hq : ∀ e, 1 ≤ q e)
    (hconn : IsStronglyConnected src tgt)
    {e₁ e₂ : E} (hne : e₁ ≠ e₂) (hsrc : src e₁ = src e₂) :
    1 < pressureRate src tgt q ℓ 0 := by
  have hle : pRad (edgeCountMatrix src tgt)
      ≤ pRad (pressureKernel src tgt q ℓ 0) :=
    pRad_le_of_entry_le (edgeCountMatrix_nonneg src tgt)
      (hasDiagWitness_edgeCountMatrix hconn e₁)
      (edgeCountMatrix_le_pressureKernel_zero hq)
  exact lt_of_lt_of_le
    (one_lt_pRad_of_branching hconn hne hsrc) hle

/-- **`thm:signed-clock`(iv), unconditional form**: on a strongly
connected branching recurrent support with positive depths in
`[ℓ₀, ℓ₁]` and capacities `q ≥ 1`, the pressure equation
`r(β) = 1` has a unique positive root.  This is
`pressure_selects_beta` with its supercriticality hypothesis
discharged by `lem:app-rho-one-cycle`. -/
theorem exists_unique_pressure_root_of_branching [Nonempty V]
    (hq : ∀ e, 1 ≤ q e) {ℓ₀ ℓ₁ : ℝ} (hℓ₀pos : 0 < ℓ₀)
    (hℓ₀ : ∀ e, ℓ₀ ≤ ℓ e) (hℓ₁ : ∀ e, ℓ e ≤ ℓ₁)
    (hconn : IsStronglyConnected src tgt)
    {e₁ e₂ : E} (hne : e₁ ≠ e₂) (hsrc : src e₁ = src e₂) :
    ∃! β : ℝ, 0 < β ∧ pressureRate src tgt q ℓ β = 1 := by
  have hq0 : ∀ e, 0 < q e :=
    fun e => lt_of_lt_of_le one_pos (hq e)
  -- diagonal witness for the kernel, dominated from the edge count
  have hwadj := hasDiagWitness_edgeCountMatrix hconn e₁
  have hwker : HasDiagWitness (pressureKernel src tgt q ℓ 0) := by
    obtain ⟨x, m, hm, hpos⟩ := hwadj
    refine ⟨x, m, hm, lt_of_lt_of_le hpos ?_⟩
    exact entry_pow_le (edgeCountMatrix_nonneg src tgt)
      (edgeCountMatrix_le_pressureKernel_zero hq) m x x
  have hmain := pressure_selects_beta src tgt q ℓ hq0 hℓ₀pos
    hℓ₀ hℓ₁ hwker
  exact hmain.2.2.2.1
    (one_lt_pressureRate_zero_of_branching hq hconn hne hsrc)

end NCG
