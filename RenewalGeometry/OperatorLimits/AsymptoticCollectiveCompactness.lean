/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.TransportedMoscoAsymptoticCompactness
import RenewalGeometry.OperatorLimits.VaryingHilbertCollectiveCompactness
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Sequences
import Mathlib.Data.Nat.Nth

/-!
# Asymptotic compactness gives collective compactness

`lem:collective-compactness` of the spacetime–gauge duality paper, on the
varying-Hilbert `System` carrier of `TransportedMoscoAsymptoticCompactness.lean`
(`def:asymptotic-compactness` = `System.AsymptoticallyCompact`, `LimitFormCompact`).

## Resolvent vectors

The paper's transported resolvent vector `u_X = (𝓛_X + I)⁻¹ J_X^* f` is the minimizer of
`F_{X,f}(u) = q_X(u) + ‖u‖² − 2 Re⟨J_X u, f⟩` (`transportedObjective`).  We only use the
comparison of the minimizer with `u = 0` (`IsTransportedResolvent`), which yields the
energy bound `eq:resolvent-energy-bound` in the form `‖u‖² + q_X(u) ≤ 8‖f‖²`
(`IsTransportedResolvent.energy_bound`; the sharp constant `1` of the paper uses the
Euler identity and is immaterial here).

## Results

* `exists_convergent_subseq_resolvent`: for bounded sources `(f_X)` the transported
  resolvent outputs `J_X (𝓛_X + I)⁻¹ J_X^* f_X` have a strongly convergent subsequence;
* `System.SeqCollectivelyCompact`: the sequential (one output per stage) notion of a
  collectively compact family; `seqCollectivelyCompact_resolvent` establishes it for
  the transported resolvents, and `CollectivelyCompact.seqCollectivelyCompact` shows it
  is implied by the compact-container notion of `VaryingHilbertCollectiveCompactness.lean`;
* `isCompactOperator_limitResolvent`: the limiting resolvent
  `J_∞ (𝓛_∞ + I)⁻¹ J_∞^*` is a compact operator (`LimitFormCompact` applied to
  arbitrary bounded sources);
* `collectivelyCompact_of_seq_of_stage_compact`: the compact-container notion follows
  from the sequential one **provided** it holds along every strictly monotone
  reindexing and every stage operator is compact.

**Scope.**  The paper's definition of asymptotic compactness quantifies over sequences
with one member per stage.  This gives exactly the sequential statement above (which is
also all that the paper's proof of `lem:collective-norm` uses); the stronger
compact-container form of collective compactness additionally needs compactness of each
stage resolvent (for `q_X = X‖·‖²` on a fixed infinite-dimensional `H` the family is
asymptotically compact but no `R_X = (X + 1)⁻¹ I` is compact), so it is recorded with
that hypothesis in `collectivelyCompact_of_seq_of_stage_compact`.
-/

open scoped ENNReal

open Filter Topology

noncomputable section

namespace RenewalGeometry.VaryingHilbert

universe u v w w'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {Hlim : Type w'} [NormedAddCommGroup Hlim] [InnerProductSpace K Hlim]

/-- The paper's resolvent objective `F_{X,f}(u) = q_X(u) + ‖u‖² − 2 Re⟨J u, f⟩` for a real
form `q` on a stage space `E` embedded by `J` into the common carrier. -/
def transportedObjective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace K E]
    (J : E →ₗᵢ[K] H) (q : E → ℝ) (f : H) (u : E) : ℝ :=
  q u + ‖u‖ ^ 2 - 2 * RCLike.re (inner K (J u) f)

/-- Comparison with `u = 0` bounds a nonnegative-energy competitor: `‖u‖ ≤ 2‖f‖` and
`q u ≤ 4‖f‖²`. -/
theorem bounds_of_transportedObjective_le_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace K E] (J : E →ₗᵢ[K] H) (q : E → ℝ) (f : H) (u : E)
    (hq : 0 ≤ q u) (hmin : transportedObjective J q f u ≤ 0) :
    ‖u‖ ≤ 2 * ‖f‖ ∧ q u ≤ 4 * ‖f‖ ^ 2 := by
  have hre : RCLike.re (inner K (J u) f) ≤ ‖u‖ * ‖f‖ := by
    calc RCLike.re (inner K (J u) f) ≤ ‖inner K (J u) f‖ := RCLike.re_le_norm _
      _ ≤ ‖J u‖ * ‖f‖ := norm_inner_le_norm _ _
      _ = ‖u‖ * ‖f‖ := by rw [J.norm_map]
  have hobj : q u + ‖u‖ ^ 2 - 2 * RCLike.re (inner K (J u) f) ≤ 0 := hmin
  have hnormu := norm_nonneg u
  have hnormf := norm_nonneg f
  have h1 : ‖u‖ ≤ 2 * ‖f‖ := by
    by_contra hc
    push_neg at hc
    nlinarith
  refine ⟨h1, ?_⟩
  nlinarith

/-- **Transported resolvent vectors**: `R n f ∈ D(q_n)` minimizes `F_{n,f}` (recorded
through the comparison with `0`), with `q_n(0) = 0`. -/
structure IsTransportedResolvent (J : System (K := K) (H := H) (Hn := Hn))
    (q : (n : ℕ) → Hn n → ℝ≥0∞) (R : (n : ℕ) → H → Hn n) : Prop where
  /-- the resolvent vector lies in the form domain -/
  finite : ∀ n f, q n (R n f) ≠ ∞
  /-- the form vanishes at `0` -/
  zero : ∀ n, q n 0 = 0
  /-- the resolvent vector does at least as well as `0` in the objective -/
  minimal : ∀ n f,
    transportedObjective (J.embedding n) (fun u => (q n u).toReal) f (R n f) ≤ 0

/-- **`eq:resolvent-energy-bound`** (with constant `8`): `‖R_n f‖² + q_n(R_n f) ≤ 8‖f‖²`. -/
theorem IsTransportedResolvent.energy_bound {J : System (K := K) (H := H) (Hn := Hn)}
    {q : (n : ℕ) → Hn n → ℝ≥0∞} {R : (n : ℕ) → H → Hn n}
    (hR : IsTransportedResolvent J q R) (n : ℕ) (f : H) :
    ENNReal.ofReal (‖R n f‖ ^ 2) + q n (R n f) ≤ ENNReal.ofReal (8 * ‖f‖ ^ 2) := by
  obtain ⟨h1, h2⟩ := bounds_of_transportedObjective_le_zero (J.embedding n)
    (fun u => (q n u).toReal) f (R n f) ENNReal.toReal_nonneg (hR.minimal n f)
  rw [← ENNReal.ofReal_toReal (hR.finite n f), ← ENNReal.ofReal_add (sq_nonneg _)
    ENNReal.toReal_nonneg]
  apply ENNReal.ofReal_le_ofReal
  have hnormu := norm_nonneg (R n f)
  have hnormf := norm_nonneg f
  nlinarith

/-- **`lem:collective-compactness`, first clause**: under asymptotic compactness, for every
bounded source sequence `(f_X)` the transported resolvent outputs
`J_X (𝓛_X + I)⁻¹ J_X^* f_X` have a strongly convergent subsequence. -/
theorem exists_convergent_subseq_resolvent (J : System (K := K) (H := H) (Hn := Hn))
    {q : (n : ℕ) → Hn n → ℝ≥0∞} {R : (n : ℕ) → H → Hn n}
    (hac : J.AsymptoticallyCompact q) (hR : IsTransportedResolvent J q R)
    (f : ℕ → H) (F : ℝ) (hf : ∀ n, ‖f n‖ ≤ F) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ y : H, Tendsto (fun k ↦ J.embedding (φ k) (R (φ k) (f (φ k)))) atTop (𝓝 y) := by
  refine hac (fun n ↦ R n (f n)) ⟨ENNReal.ofReal (8 * F ^ 2), ENNReal.ofReal_ne_top, fun n ↦ ?_⟩
  refine (hR.energy_bound n (f n)).trans (ENNReal.ofReal_le_ofReal ?_)
  have := hf n
  have := norm_nonneg (f n)
  nlinarith

namespace System

variable (L : System (K := K) (H := H) (Hn := Hn))

/-- **Sequential collective compactness** of a stage-operator family with a common source
space `E`: the embedded outputs of every unit-bounded input sequence (one input per
stage) have a convergent subsequence in the common carrier.  This is the notion the
paper's proofs of `lem:collective-compactness` and `lem:collective-norm` use. -/
def SeqCollectivelyCompact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace K E]
    (Tn : ∀ n, E →L[K] Hn n) : Prop :=
  ∀ x : ℕ → E, (∀ n, ‖x n‖ ≤ 1) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ y : H, Tendsto (fun k ↦ L.embedding (φ k) (Tn (φ k) (x (φ k)))) atTop (𝓝 y)

/-- The compact-container notion of `VaryingHilbertCollectiveCompactness.lean` implies the
sequential one. -/
theorem CollectivelyCompact.seqCollectivelyCompact {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace K E] {Tn : ∀ n, E →L[K] Hn n}
    (hT : L.CollectivelyCompact Tn) :
    L.SeqCollectivelyCompact Tn := by
  intro x hx
  obtain ⟨y, φ, hφ, hy⟩ := CollectivelyCompact.tendsto_output_subseq (L := L) hT x hx
  exact ⟨φ, hφ, y, hy⟩

/-- **`lem:collective-compactness`, second clause**: the transported resolvents form a
(sequentially) collectively compact family. -/
theorem seqCollectivelyCompact_resolvent {q : (n : ℕ) → Hn n → ℝ≥0∞}
    {R : (n : ℕ) → H →L[K] Hn n}
    (hac : L.AsymptoticallyCompact q) (hR : IsTransportedResolvent L q fun n ↦ (R n : H → Hn n)) :
    L.SeqCollectivelyCompact R := fun x hx =>
  exists_convergent_subseq_resolvent L hac hR x 1 hx

end System

/-! ### Compactness of the limiting resolvent -/

/-- A set every sequence of which has a convergent subsequence (in the ambient space)
has sequentially compact closure. -/
theorem isSeqCompact_closure_of_subseq {X : Type*} [PseudoMetricSpace X] (s : Set X)
    (h : ∀ x : ℕ → X, (∀ m, x m ∈ s) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : X, Tendsto (x ∘ φ) atTop (𝓝 y)) :
    IsSeqCompact (closure s) := by
  intro y hy
  have happrox : ∀ m, ∃ b ∈ s, dist (y m) b < 1 / ((m : ℝ) + 1) := fun m =>
    Metric.mem_closure_iff.mp (hy m) _ (by positivity)
  choose x hxs hxd using happrox
  obtain ⟨φ, hφ, z, hz⟩ := h x hxs
  refine ⟨z, ?_, φ, hφ, ?_⟩
  · exact isClosed_closure.mem_of_tendsto hz
      (Eventually.of_forall fun k => subset_closure (hxs (φ k)))
  · rw [tendsto_iff_dist_tendsto_zero]
    have hle : ∀ k, dist (y (φ k)) z ≤ 1 / ((k : ℝ) + 1) + dist (x (φ k)) z := by
      intro k
      calc dist (y (φ k)) z ≤ dist (y (φ k)) (x (φ k)) + dist (x (φ k)) z := dist_triangle _ _ _
        _ ≤ 1 / ((φ k : ℝ) + 1) + dist (x (φ k)) z := by
          gcongr
          exact (hxd (φ k)).le
        _ ≤ 1 / ((k : ℝ) + 1) + dist (x (φ k)) z := by
          gcongr
          exact_mod_cast hφ.id_le k
    refine squeeze_zero (fun k => dist_nonneg) hle ?_
    have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun k => dist (x (φ k)) z) atTop (𝓝 0) := by
      rw [← tendsto_iff_dist_tendsto_zero]
      exact hz
    simpa using h1.add h2

/-- A continuous linear map whose image of the unit ball has the subsequence property is
a compact operator. -/
theorem isCompactOperator_of_subseq {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (T : E →L[K] F)
    (h : ∀ x : ℕ → E, (∀ m, ‖x m‖ ≤ 1) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : F, Tendsto (fun k ↦ T (x (φ k))) atTop (𝓝 y)) :
    IsCompactOperator T := by
  have hlin : IsCompactOperator T.toLinearMap := by
    rw [isCompactOperator_iff_image_closedBall_subset_compact T.toLinearMap zero_lt_one]
    refine ⟨closure (T '' Metric.closedBall 0 1), ?_, subset_closure⟩
    apply IsSeqCompact.isCompact
    apply isSeqCompact_closure_of_subseq
    intro y hy
    choose x hx hxy using hy
    obtain ⟨φ, hφ, z, hz⟩ := h x fun m => by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx m
    refine ⟨φ, hφ, z, ?_⟩
    have : (y ∘ φ) = fun k => T (x (φ k)) := funext fun k => (hxy (φ k)).symm
    rw [this]
    exact hz
  simpa using hlin

/-- **`lem:collective-compactness`, third clause**: the limiting resolvent
`J_∞ (𝓛_∞ + I)⁻¹ J_∞^*` is a compact operator, by the limit clause of asymptotic form
compactness applied to arbitrary bounded sources. -/
theorem isCompactOperator_limitResolvent (Jlim : Hlim →ₗᵢ[K] H) (qlim : Hlim → ℝ≥0∞)
    (Rlim : H →L[K] Hlim) (hlim : LimitFormCompact Jlim qlim)
    (hR : IsTransportedResolvent (constantEmbeddingSystem Jlim) (fun _ ↦ qlim)
      (fun _ ↦ (Rlim : H → Hlim))) :
    IsCompactOperator (Jlim.toContinuousLinearMap.comp Rlim) := by
  apply isCompactOperator_of_subseq
  intro x hx
  obtain ⟨φ, hφ, y, hy⟩ := exists_convergent_subseq_resolvent (constantEmbeddingSystem Jlim)
    hlim hR x 1 hx
  exact ⟨φ, hφ, y, hy⟩

/-! ### From the sequential notion to the compact-container notion -/

/-- From an unbounded sequence of stage indices one extracts a strictly increasing
subsequence with strictly increasing stages. -/
theorem exists_strictMono_comp_strictMono (m : ℕ → ℕ) (hm : ∀ N, ∃ k, N < m k) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ StrictMono (m ∘ ψ) := by
  classical
  -- `next k` is an index beyond `k` with a larger stage than every stage up to `k`
  have hnext : ∀ k, ∃ k', k < k' ∧ m k < m k' := by
    intro k
    obtain ⟨k', hk'⟩ := hm ((Finset.range (k + 1)).sup m)
    refine ⟨k', ?_, ?_⟩
    · by_contra hle
      push_neg at hle
      have : m k' ≤ (Finset.range (k + 1)).sup m :=
        Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      omega
    · have : m k ≤ (Finset.range (k + 1)).sup m :=
        Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self k))
      omega
  choose next hnext_gt hnext_stage using hnext
  let ψ : ℕ → ℕ := fun j => Nat.rec 0 (fun _ k => next k) j
  have hψ_succ : ∀ j, ψ (j + 1) = next (ψ j) := fun j => rfl
  refine ⟨ψ, strictMono_nat_of_lt_succ fun j => ?_, strictMono_nat_of_lt_succ fun j => ?_⟩
  · rw [hψ_succ]; exact hnext_gt _
  · show m (ψ j) < m (ψ (j + 1))
    rw [hψ_succ]; exact hnext_stage _

variable (L : System (K := K) (H := H) (Hn := Hn))

/-- **Compact-container collective compactness from the sequential notion**: if the
sequential property holds along every strictly monotone reindexing of the stages and
every embedded stage operator is compact, then the family is collectively compact in
the sense of `VaryingHilbertCollectiveCompactness.lean`. -/
theorem collectivelyCompact_of_seq_of_stage_compact {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace K E] (Tn : ∀ n, E →L[K] Hn n)
    (hseq : ∀ φ : ℕ → ℕ, StrictMono φ →
      (L.reindex φ).SeqCollectivelyCompact (Hn := fun k ↦ Hn (φ k)) fun k ↦ Tn (φ k))
    (hstage : ∀ n, IsCompactOperator (L.embeddedOperator (Hn := fun _ ↦ E) Tn n)) :
    L.CollectivelyCompact Tn := by
  classical
  refine ⟨closure (⋃ n, L.embeddedOperator (Hn := fun _ ↦ E) Tn n '' Metric.closedBall 0 1),
    ?_, fun n => (Set.subset_iUnion
      (fun n => L.embeddedOperator (Hn := fun _ ↦ E) Tn n '' Metric.closedBall 0 1) n).trans
      subset_closure⟩
  apply IsSeqCompact.isCompact
  apply isSeqCompact_closure_of_subseq
  intro y hy
  -- each `y k` is the embedded output of a unit input at some stage `m k`
  have hy' : ∀ k, ∃ m : ℕ, ∃ x : E, ‖x‖ ≤ 1 ∧ L.embedding m (Tn m x) = y k := by
    intro k
    obtain ⟨m, x, hx, hxy⟩ := Set.mem_iUnion.mp (hy k)
    exact ⟨m, x, by simpa [Metric.mem_closedBall, dist_zero_right] using hx, hxy⟩
  choose m x hx hxy using hy'
  by_cases hbdd : ∃ N, ∀ k, m k ≤ N
  · -- bounded stages: some stage occurs infinitely often, use its compactness
    obtain ⟨N, hN⟩ := hbdd
    let mf : ℕ → Fin (N + 1) := fun k => ⟨m k, Nat.lt_succ_of_le (hN k)⟩
    obtain ⟨n₀, hn₀⟩ := Finite.exists_infinite_fiber mf
    have hinf : (Set.ofPred fun k => mf k = n₀).Infinite := by
      rw [← Set.infinite_coe_iff]
      exact hn₀
    let ψ : ℕ → ℕ := Nat.nth fun k => mf k = n₀
    have hψ : StrictMono ψ := Nat.nth_strictMono hinf
    have hψst : ∀ k, m (ψ k) = (n₀ : ℕ) := fun k =>
      congrArg Fin.val (Nat.nth_mem_of_infinite hinf k)
    have key : ∀ k, y (ψ k) = L.embeddedOperator (Hn := fun _ ↦ E) Tn n₀ (x (ψ k)) := by
      intro k
      rw [← hxy (ψ k), System.embeddedOperator_apply, hψst k]
    obtain ⟨C, hC, hsub⟩ := (isCompactOperator_iff_image_closedBall_subset_compact
      (L.embeddedOperator (Hn := fun _ ↦ E) Tn n₀).toLinearMap zero_lt_one).mp
      (by simpa using hstage n₀)
    have hmem : ∀ k, y (ψ k) ∈ C := fun k => by
      rw [key k]
      exact hsub ⟨x (ψ k), by simpa [Metric.mem_closedBall, dist_zero_right] using hx (ψ k), rfl⟩
    obtain ⟨z, -, φ, hφ, hz⟩ := hC.tendsto_subseq hmem
    exact ⟨ψ ∘ φ, hψ.comp hφ, z, hz⟩
  · -- unbounded stages: pass to strictly increasing stages and use the sequential property
    push_neg at hbdd
    obtain ⟨ψ, hψ, hmψ⟩ := exists_strictMono_comp_strictMono m hbdd
    obtain ⟨φ, hφ, z, hz⟩ := hseq (m ∘ ψ) hmψ (fun k => x (ψ k)) (fun k => hx (ψ k))
    have hz' : Tendsto (y ∘ (ψ ∘ φ)) atTop (𝓝 z) := by
      refine hz.congr fun k => ?_
      simp only [Function.comp_apply, System.reindex_embedding]
      exact hxy (ψ (φ k))
    exact ⟨ψ ∘ φ, hψ.comp hφ, z, hz'⟩

end RenewalGeometry.VaryingHilbert
