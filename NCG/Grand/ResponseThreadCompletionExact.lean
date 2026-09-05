/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Projectively Cauchy response-thread completion

Exact encoding of `thm:GT-response-thread-completion` (TR.3–TR.6) and
`cor:GT-response-thread-master-defect` (TR.6a–TR.6b).

A finite-query thread is a sequence `y m : ℝ → K` of responses on an increasing
family of query sets `D m ⊆ [0, T]` whose union is dense in `[0, T]`, with a common
modulus `ω` (TR.3) and a projective Cauchy defect bound `η m` (TR.4):
`d(y n t, y m t) ≤ η m` for `n ≥ m`, `t ∈ D m`, `η m → 0`.

* `limitTrace` is the completed trace `y`; `limitTrace_modulus`, `limitTrace_continuousOn`,
  `limitTrace_defect` (TR.5) and `limitTrace_unique` give the unique trace with modulus `ω`
  and `max_{t ∈ D m} d(y t, y m t) ≤ η m`;
* `adjacent_defect_bound`: summable adjacent defects `δ` give `η m ≤ ∑_{j ≥ m} δ j`;
* `cylinder_limit` (TR.6): a continuous cylinder functional on finitely many query
  times with `𝔡(y m) → 0` vanishes on the completed trace;
* `lipschitz_cylinder_bound` (TR.6a) and `master_defect_closure` (TR.6b): the one-scalar
  master defect `Δ m = η m + ∑_{j ≤ m} 2^{-j} min(1, 𝔡_j[y m]) → 0` certifies a
  continuous limit satisfying the whole countable defect core.
-/

open Filter Topology Finset

namespace NCG
namespace ResponseThreadCompletion

set_option linter.unusedSectionVars false

variable {K : Type*} [MetricSpace K] [CompleteSpace K]

/-- A finite-query response thread with its query hierarchy, modulus and defect bound. -/
structure Thread (K : Type*) [MetricSpace K] where
  /-- the horizon -/
  T : ℝ
  /-- the query sets `D m ⊆ [0, T]` -/
  D : ℕ → Set ℝ
  /-- the finite responses -/
  y : ℕ → ℝ → K
  /-- the common modulus -/
  ω : ℝ → ℝ
  /-- the projective Cauchy defect bound -/
  η : ℕ → ℝ
  D_subset : ∀ m, D m ⊆ Set.Icc 0 T
  D_mono : Monotone D
  D_dense : ∀ t ∈ Set.Icc 0 T, ∀ ε > 0, ∃ m, ∃ s ∈ D m, |s - t| < ε
  ω_cont : Continuous ω
  ω_zero : ω 0 = 0
  /-- (TR.3) -/
  modulus : ∀ m, ∀ t ∈ D m, ∀ s ∈ D m, dist (y m t) (y m s) ≤ ω (|t - s|)
  /-- (TR.4) -/
  defect : ∀ m n, m ≤ n → ∀ t ∈ D m, dist (y n t) (y m t) ≤ η m
  η_nonneg : ∀ m, 0 ≤ η m
  η_tendsto : Tendsto η atTop (𝓝 0)

variable (Y : Thread K)

/-- The union of the query sets. -/
def queries : Set ℝ := ⋃ m, Y.D m

theorem mem_queries {t : ℝ} : t ∈ queries Y ↔ ∃ m, t ∈ Y.D m := Set.mem_iUnion

theorem queries_subset : queries Y ⊆ Set.Icc 0 Y.T := by
  intro t ht
  obtain ⟨m, hm⟩ := (mem_queries Y).mp ht
  exact Y.D_subset m hm

/-- On a query `t ∈ D m`, the values `y n t` form a Cauchy sequence. -/
theorem cauchySeq_at {t : ℝ} {m : ℕ} (ht : t ∈ Y.D m) :
    CauchySeq (fun n => Y.y n t) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp Y.η_tendsto) (ε / 2) (by positivity)
  refine ⟨max m N, fun a ha b hb => ?_⟩
  have hma : m ≤ a := le_trans (le_max_left _ _) ha
  have hmb : m ≤ b := le_trans (le_max_left _ _) hb
  have hta : t ∈ Y.D a := Y.D_mono hma ht
  have hNa := hN a (le_trans (le_max_right _ _) ha)
  have hNb := hN b (le_trans (le_max_right _ _) hb)
  rw [Real.dist_eq, sub_zero] at hNa hNb
  have hηa : Y.η a < ε / 2 := lt_of_le_of_lt (le_abs_self _) hNa
  have hηb : Y.η b < ε / 2 := lt_of_le_of_lt (le_abs_self _) hNb
  rcases le_total a b with hab | hab
  · have := Y.defect a b hab t hta
    calc dist (Y.y a t) (Y.y b t) = dist (Y.y b t) (Y.y a t) := dist_comm _ _
      _ ≤ Y.η a := this
      _ < ε := by linarith
  · have htb : t ∈ Y.D b := Y.D_mono hmb ht
    have := Y.defect b a hab t htb
    calc dist (Y.y a t) (Y.y b t) ≤ Y.η b := this
      _ < ε := by linarith

open Classical in
/-- The limit of the thread on the query union (and `y 0 t` off it, irrelevant). -/
noncomputable def queryLimit (t : ℝ) : K :=
  if h : ∃ m, t ∈ Y.D m then
    Classical.choose (cauchySeq_tendsto_of_complete (cauchySeq_at Y h.choose_spec))
  else Y.y 0 t

theorem tendsto_queryLimit {t : ℝ} {m : ℕ} (ht : t ∈ Y.D m) :
    Tendsto (fun n => Y.y n t) atTop (𝓝 (queryLimit Y t)) := by
  have h : ∃ m, t ∈ Y.D m := ⟨m, ht⟩
  unfold queryLimit
  rw [dif_pos h]
  exact Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_at Y h.choose_spec))

/-- (TR.5 on the queries): `d(ŷ t, y m t) ≤ η m` for `t ∈ D m`. -/
theorem dist_queryLimit_le {t : ℝ} {m : ℕ} (ht : t ∈ Y.D m) :
    dist (queryLimit Y t) (Y.y m t) ≤ Y.η m := by
  have hlim := tendsto_queryLimit Y ht
  have : Tendsto (fun n => dist (Y.y n t) (Y.y m t)) atTop (𝓝 (dist (queryLimit Y t) (Y.y m t))) :=
    (hlim.dist tendsto_const_nhds)
  refine le_of_tendsto this ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  exact Y.defect m n hn t ht

/-- The modulus passes to the limit on the query union. -/
theorem queryLimit_modulus {t s : ℝ} (ht : t ∈ queries Y) (hs : s ∈ queries Y) :
    dist (queryLimit Y t) (queryLimit Y s) ≤ Y.ω (|t - s|) := by
  obtain ⟨m, hm⟩ := (mem_queries Y).mp ht
  obtain ⟨k, hk⟩ := (mem_queries Y).mp hs
  have hlt := tendsto_queryLimit Y hm
  have hls := tendsto_queryLimit Y hk
  refine le_of_tendsto (hlt.dist hls) ?_
  filter_upwards [eventually_ge_atTop (max m k)] with n hn
  exact Y.modulus n t (Y.D_mono (le_trans (le_max_left _ _) hn) hm) s
    (Y.D_mono (le_trans (le_max_right _ _) hn) hk)

open Classical in
/-- An approximating query sequence for every `t ∈ [0, T]`. -/
noncomputable def approx (t : ℝ) (k : ℕ) : ℝ :=
  if h : t ∈ Set.Icc 0 Y.T then
    Classical.choose (Classical.choose_spec (Y.D_dense t h (1 / ((k : ℝ) + 1)) (by positivity)))
  else t

theorem approx_spec {t : ℝ} (ht : t ∈ Set.Icc 0 Y.T) (k : ℕ) :
    approx Y t k ∈ queries Y ∧ |approx Y t k - t| < 1 / ((k : ℝ) + 1) := by
  unfold approx
  rw [dif_pos ht]
  obtain ⟨hm, hlt⟩ :=
    Classical.choose_spec (Classical.choose_spec (Y.D_dense t ht (1 / ((k : ℝ) + 1))
      (by positivity)))
  exact ⟨(mem_queries Y).mpr ⟨_, hm⟩, hlt⟩

theorem approx_tendsto {t : ℝ} (ht : t ∈ Set.Icc 0 Y.T) :
    Tendsto (approx Y t) atTop (𝓝 t) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq]
  have h1 := (approx_spec Y ht k).2
  have h2 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    gcongr
  linarith

/-- The approximating values are Cauchy. -/
theorem cauchySeq_approx {t : ℝ} (ht : t ∈ Set.Icc 0 Y.T) :
    CauchySeq (fun k => queryLimit Y (approx Y t k)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  -- `ω` is continuous at `0` with `ω 0 = 0`
  have hω : Tendsto Y.ω (𝓝 0) (𝓝 0) := by
    have := Y.ω_cont.tendsto 0
    rwa [Y.ω_zero] at this
  obtain ⟨δ, hδ, hδω⟩ := Metric.tendsto_nhds_nhds.mp hω ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hδ)
  refine ⟨N, fun a ha b hb => ?_⟩
  have h1 := (approx_spec Y ht a)
  have h2 := (approx_spec Y ht b)
  have hab : |approx Y t a - approx Y t b| < δ := by
    have ha' : (1 : ℝ) / ((a : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by gcongr
    have hb' : (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by gcongr
    calc |approx Y t a - approx Y t b|
        = |(approx Y t a - t) - (approx Y t b - t)| := by ring_nf
      _ ≤ |approx Y t a - t| + |approx Y t b - t| := abs_sub _ _
      _ < δ := by linarith [h1.2, h2.2]
  have := queryLimit_modulus Y h1.1 h2.1
  have hωab : dist (Y.ω (|approx Y t a - approx Y t b|)) 0 < ε := by
    apply hδω
    rw [Real.dist_eq, sub_zero, abs_abs]
    exact hab
  rw [Real.dist_eq, sub_zero] at hωab
  calc dist (queryLimit Y (approx Y t a)) (queryLimit Y (approx Y t b))
      ≤ Y.ω (|approx Y t a - approx Y t b|) := this
    _ ≤ |Y.ω (|approx Y t a - approx Y t b|)| := le_abs_self _
    _ < ε := hωab

open Classical in
/-- **The completed trace** `y : [0, T] → K`. -/
noncomputable def limitTrace (t : ℝ) : K :=
  if h : t ∈ Set.Icc 0 Y.T then
    Classical.choose (cauchySeq_tendsto_of_complete (cauchySeq_approx Y h))
  else Y.y 0 t

theorem tendsto_limitTrace {t : ℝ} (ht : t ∈ Set.Icc 0 Y.T) :
    Tendsto (fun k => queryLimit Y (approx Y t k)) atTop (𝓝 (limitTrace Y t)) := by
  unfold limitTrace
  rw [dif_pos ht]
  exact Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_approx Y ht))

/-- The trace agrees with the query limit on the queries. -/
theorem limitTrace_eq_queryLimit {t : ℝ} (ht : t ∈ queries Y) :
    limitTrace Y t = queryLimit Y t := by
  have htI := queries_subset Y ht
  have h1 := tendsto_limitTrace Y htI
  -- the approximants converge to `queryLimit t` by the modulus
  have h2 : Tendsto (fun k => queryLimit Y (approx Y t k)) atTop (𝓝 (queryLimit Y t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hω : Tendsto Y.ω (𝓝 0) (𝓝 0) := by
      have := Y.ω_cont.tendsto 0
      rwa [Y.ω_zero] at this
    obtain ⟨δ, hδ, hδω⟩ := Metric.tendsto_nhds_nhds.mp hω ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun k hk => ?_⟩
    have hk' := approx_spec Y htI k
    have hlt : |approx Y t k - t| < δ := by
      have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by gcongr
      linarith [hk'.2]
    have hωk : dist (Y.ω (|approx Y t k - t|)) 0 < ε := by
      apply hδω
      rw [Real.dist_eq, sub_zero, abs_abs]
      exact hlt
    rw [Real.dist_eq, sub_zero] at hωk
    calc dist (queryLimit Y (approx Y t k)) (queryLimit Y t)
        ≤ Y.ω (|approx Y t k - t|) := queryLimit_modulus Y hk'.1 ht
      _ ≤ |Y.ω (|approx Y t k - t|)| := le_abs_self _
      _ < ε := hωk
  exact tendsto_nhds_unique h1 h2

/-- **(TR.3 for the limit)**: the completed trace has modulus `ω` on `[0, T]`. -/
theorem limitTrace_modulus {t s : ℝ} (ht : t ∈ Set.Icc 0 Y.T) (hs : s ∈ Set.Icc 0 Y.T) :
    dist (limitTrace Y t) (limitTrace Y s) ≤ Y.ω (|t - s|) := by
  have h1 := (tendsto_limitTrace Y ht).dist (tendsto_limitTrace Y hs)
  have h2 : Tendsto (fun k => Y.ω (|approx Y t k - approx Y s k|)) atTop (𝓝 (Y.ω (|t - s|))) :=
    Y.ω_cont.continuousAt.tendsto.comp
      (((approx_tendsto Y ht).sub (approx_tendsto Y hs)).abs)
  refine le_of_tendsto_of_tendsto' h1 h2 fun k => ?_
  exact queryLimit_modulus Y (approx_spec Y ht k).1 (approx_spec Y hs k).1

/-- The completed trace is continuous on `[0, T]`. -/
theorem limitTrace_continuousOn : ContinuousOn (limitTrace Y) (Set.Icc 0 Y.T) := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hω : Tendsto Y.ω (𝓝 0) (𝓝 0) := by
    have := Y.ω_cont.tendsto 0
    rwa [Y.ω_zero] at this
  obtain ⟨δ, hδ, hδω⟩ := Metric.tendsto_nhds_nhds.mp hω ε hε
  refine ⟨δ, hδ, fun s hs hst => ?_⟩
  have hωs : dist (Y.ω (|s - t|)) 0 < ε := by
    apply hδω
    rw [Real.dist_eq, sub_zero, abs_abs]
    rwa [Real.dist_eq] at hst
  rw [Real.dist_eq, sub_zero] at hωs
  calc dist (limitTrace Y s) (limitTrace Y t) ≤ Y.ω (|s - t|) := limitTrace_modulus Y hs ht
    _ ≤ |Y.ω (|s - t|)| := le_abs_self _
    _ < ε := hωs

/-- **(TR.5)**: `max_{t ∈ D m} d(y t, y m t) ≤ η m`. -/
theorem limitTrace_defect {t : ℝ} {m : ℕ} (ht : t ∈ Y.D m) :
    dist (limitTrace Y t) (Y.y m t) ≤ Y.η m := by
  rw [limitTrace_eq_queryLimit Y ((mem_queries Y).mpr ⟨m, ht⟩)]
  exact dist_queryLimit_le Y ht

/-- **Uniqueness**: any continuous trace satisfying (TR.5) is the completed trace. -/
theorem limitTrace_unique (z : ℝ → K) (hz : ContinuousOn z (Set.Icc 0 Y.T))
    (hzd : ∀ m, ∀ t ∈ Y.D m, dist (z t) (Y.y m t) ≤ Y.η m) :
    ∀ t ∈ Set.Icc 0 Y.T, z t = limitTrace Y t := by
  -- agreement on the queries
  have hq : ∀ t ∈ queries Y, z t = limitTrace Y t := by
    intro t ht
    obtain ⟨m, hm⟩ := (mem_queries Y).mp ht
    rw [limitTrace_eq_queryLimit Y ht]
    have hlim := tendsto_queryLimit Y hm
    refine tendsto_nhds_unique ?_ hlim
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp Y.η_tendsto) ε hε
    refine ⟨max m N, fun n hn => ?_⟩
    have hηn := hN n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq, sub_zero] at hηn
    have := hzd n t (Y.D_mono (le_trans (le_max_left _ _) hn) hm)
    calc dist (Y.y n t) (z t) = dist (z t) (Y.y n t) := dist_comm _ _
      _ ≤ Y.η n := this
      _ ≤ |Y.η n| := le_abs_self _
      _ < ε := hηn
  intro t ht
  -- both sides are limits along the approximating queries
  have h1 : Tendsto (fun k => z (approx Y t k)) atTop (𝓝 (z t)) :=
    (hz t ht).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨approx_tendsto Y ht, Eventually.of_forall fun k => queries_subset Y (approx_spec Y ht k).1⟩)
  have h2 : Tendsto (fun k => limitTrace Y (approx Y t k)) atTop (𝓝 (limitTrace Y t)) :=
    (limitTrace_continuousOn Y t ht).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨approx_tendsto Y ht, Eventually.of_forall fun k => queries_subset Y (approx_spec Y ht k).1⟩)
  have heq : (fun k => z (approx Y t k)) = fun k => limitTrace Y (approx Y t k) :=
    funext fun k => hq _ (approx_spec Y ht k).1
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-! ### Adjacent restriction defects -/

/-- **Telescoping**: if `d(y (m+1) t, y m t) ≤ δ m` on `D m`, then on `D m`,
`d(y n t, y m t) ≤ ∑_{j ∈ [m, n)} δ j`. -/
theorem telescoping (D : ℕ → Set ℝ) (hD : Monotone D) (y : ℕ → ℝ → K) (δ : ℕ → ℝ)
    (hδ : ∀ m, ∀ t ∈ D m, dist (y (m + 1) t) (y m t) ≤ δ m) (m n : ℕ) (hmn : m ≤ n)
    {t : ℝ} (ht : t ∈ D m) :
    dist (y n t) (y m t) ≤ ∑ j ∈ Finset.Ico m n, δ j := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [Finset.sum_Ico_succ_top hmn]
    calc dist (y (n + 1) t) (y m t)
        ≤ dist (y (n + 1) t) (y n t) + dist (y n t) (y m t) := dist_triangle _ _ _
      _ ≤ δ n + ∑ j ∈ Finset.Ico m n, δ j :=
        add_le_add (hδ n t (hD hmn ht)) ih
      _ = _ := by ring

/-- **Adjacent-defect bound**: summable adjacent defects give the tail bound
`η m ≤ ∑_{j ≥ m} δ j`, i.e. the tails are admissible defect bounds. -/
theorem adjacent_defect_bound (D : ℕ → Set ℝ) (hD : Monotone D) (y : ℕ → ℝ → K) (δ : ℕ → ℝ)
    (hδ0 : ∀ j, 0 ≤ δ j) (hsum : Summable δ)
    (hδ : ∀ m, ∀ t ∈ D m, dist (y (m + 1) t) (y m t) ≤ δ m) (m n : ℕ) (hmn : m ≤ n)
    {t : ℝ} (ht : t ∈ D m) :
    dist (y n t) (y m t) ≤ ∑' j, δ (j + m) := by
  refine (telescoping D hD y δ hδ m n hmn ht).trans ?_
  have hshift : Summable fun j => δ (j + m) := (summable_nat_add_iff m).mpr hsum
  have e : ∑ j ∈ Finset.Ico m n, δ j = ∑ j ∈ Finset.range (n - m), δ (j + m) := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun j => δ j) 0 (n - m) m]
    congr 1
    simp [Nat.sub_add_cancel hmn]
  rw [e]
  exact hshift.sum_le_tsum _ (fun j _ => hδ0 _)

/-- The tails of a summable nonnegative sequence tend to zero. -/
theorem tail_tendsto_zero (δ : ℕ → ℝ) :
    Tendsto (fun m => ∑' j, δ (j + m)) atTop (𝓝 0) :=
  tendsto_sum_nat_add δ

/-! ### Cylinder functionals (TR.6) -/

/-- **(TR.6)**: a continuous cylinder functional on finitely many query times, evaluated
on the thread, vanishes on the completed trace if its thread values tend to zero. -/
theorem cylinder_limit {k : ℕ} (𝔡 : (Fin k → K) → ℝ) (h𝔡 : Continuous 𝔡) (q : Fin k → ℝ)
    (depth : ℕ) (hq : ∀ i, q i ∈ Y.D depth)
    (hlim : Tendsto (fun m => 𝔡 (fun i => Y.y m (q i))) atTop (𝓝 0)) :
    𝔡 (fun i => limitTrace Y (q i)) = 0 := by
  have hconv : Tendsto (fun m => fun i => Y.y m (q i)) atTop
      (𝓝 (fun i => limitTrace Y (q i))) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [limitTrace_eq_queryLimit Y ((mem_queries Y).mpr ⟨depth, hq i⟩)]
    exact tendsto_queryLimit Y (hq i)
  exact tendsto_nhds_unique (h𝔡.continuousAt.tendsto.comp hconv) hlim

/-! ### The master defect (TR.6a–TR.6b) -/

/-- **(TR.6a)**: Lipschitz cylinder functionals satisfy `𝔡(y) ≤ 𝔡[y m] + L η m`. -/
theorem lipschitz_cylinder_bound {k : ℕ} (𝔡 : (Fin k → K) → ℝ) {L : NNReal}
    (h𝔡 : LipschitzWith L 𝔡) (q : Fin k → ℝ) (m : ℕ) (hq : ∀ i, q i ∈ Y.D m) :
    𝔡 (fun i => limitTrace Y (q i)) ≤ 𝔡 (fun i => Y.y m (q i)) + L * Y.η m := by
  have hd : dist (fun i => limitTrace Y (q i)) (fun i => Y.y m (q i)) ≤ Y.η m := by
    rw [dist_pi_le_iff (Y.η_nonneg m)]
    intro i
    exact limitTrace_defect Y (hq i)
  have := h𝔡.dist_le_mul (fun i => limitTrace Y (q i)) (fun i => Y.y m (q i))
  have h1 : 𝔡 (fun i => limitTrace Y (q i)) - 𝔡 (fun i => Y.y m (q i))
      ≤ L * Y.η m := by
    calc 𝔡 (fun i => limitTrace Y (q i)) - 𝔡 (fun i => Y.y m (q i))
        ≤ |𝔡 (fun i => limitTrace Y (q i)) - 𝔡 (fun i => Y.y m (q i))| := le_abs_self _
      _ = dist (𝔡 (fun i => limitTrace Y (q i))) (𝔡 (fun i => Y.y m (q i))) :=
        (Real.dist_eq _ _).symm
      _ ≤ L * dist (fun i => limitTrace Y (q i)) (fun i => Y.y m (q i)) := this
      _ ≤ L * Y.η m := mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg L)
  linarith


/-- **(TR.6b)**: the scalar master defect
`Δ m = η m + ∑_{j < m} 2^{-(j+1)} min(1, 𝔡_j[y m])`. -/
noncomputable def masterDefect {k : ℕ → ℕ} (𝔡 : ∀ j, (Fin (k j) → K) → ℝ)
    (q : ∀ j, Fin (k j) → ℝ) (m : ℕ) : ℝ :=
  Y.η m + ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ (j + 1) * min 1 (𝔡 j (fun i => Y.y m (q j i)))

/-- **One-scalar thread certificate**: if the master defect tends to zero, the completed
trace satisfies every member of the countable defect core. -/
theorem master_defect_closure {k : ℕ → ℕ} (𝔡 : ∀ j, (Fin (k j) → K) → ℝ)
    (h𝔡 : ∀ j, Continuous (𝔡 j)) (h𝔡0 : ∀ j v, 0 ≤ 𝔡 j v) (q : ∀ j, Fin (k j) → ℝ)
    (depth : ℕ → ℕ) (hq : ∀ j i, q j i ∈ Y.D (depth j))
    (hΔ : Tendsto (masterDefect Y 𝔡 q) atTop (𝓝 0)) (j : ℕ) :
    𝔡 j (fun i => limitTrace Y (q j i)) = 0 := by
  refine cylinder_limit Y (𝔡 j) (h𝔡 j) (q j) (depth j) (hq j) ?_
  -- the `j`-th summand is dominated by the master defect for `m > j`
  have hterm : ∀ m, j < m →
      (1 / 2 : ℝ) ^ (j + 1) * min 1 (𝔡 j (fun i => Y.y m (q j i))) ≤ masterDefect Y 𝔡 q m := by
    intro m hm
    unfold masterDefect
    have h1 : (1 / 2 : ℝ) ^ (j + 1) * min 1 (𝔡 j (fun i => Y.y m (q j i)))
        ≤ ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ (i + 1) * min 1 (𝔡 i (fun l => Y.y m (q i l))) :=
      Finset.single_le_sum
        (f := fun i => (1 / 2 : ℝ) ^ (i + 1) * min 1 (𝔡 i (fun l => Y.y m (q i l))))
        (fun i _ => mul_nonneg (by positivity) (le_min zero_le_one (h𝔡0 i _)))
        (Finset.mem_range.mpr hm)
    linarith [Y.η_nonneg m]
  have hmin : Tendsto (fun m => min 1 (𝔡 j (fun i => Y.y m (q j i)))) atTop (𝓝 0) := by
    have hc : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hΔ) ((1 / 2 : ℝ) ^ (j + 1) * ε) (by positivity)
    refine ⟨max N (j + 1), fun m hm => ?_⟩
    have hΔm := hN m (le_trans (le_max_left _ _) hm)
    rw [Real.dist_eq, sub_zero] at hΔm
    have hjm : j < m := lt_of_lt_of_le (Nat.lt_succ_self j) (le_trans (le_max_right _ _) hm)
    have ht := hterm m hjm
    have hnn : 0 ≤ min 1 (𝔡 j (fun i => Y.y m (q j i))) := le_min zero_le_one (h𝔡0 j _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    have hΔnn : 0 ≤ masterDefect Y 𝔡 q m := le_trans (mul_nonneg hc.le hnn) ht
    rw [abs_of_nonneg hΔnn] at hΔm
    by_contra hcon
    push Not at hcon
    have : (1 / 2 : ℝ) ^ (j + 1) * ε ≤ (1 / 2 : ℝ) ^ (j + 1) * min 1 (𝔡 j fun i => Y.y m (q j i)) :=
      mul_le_mul_of_nonneg_left hcon hc.le
    linarith
  -- `min 1 x → 0` with `x ≥ 0` forces `x → 0`
  rw [Metric.tendsto_atTop] at hmin ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hmin (min 1 ε) (lt_min one_pos hε)
  refine ⟨N, fun m hm => ?_⟩
  have h := hN m hm
  rw [Real.dist_eq, sub_zero] at h ⊢
  have hnn := h𝔡0 j (fun i => Y.y m (q j i))
  rw [abs_of_nonneg (le_min zero_le_one hnn)] at h
  rw [abs_of_nonneg hnn]
  by_contra hcon
  push Not at hcon
  have : min 1 ε ≤ min 1 (𝔡 j fun i => Y.y m (q j i)) := le_min (min_le_left _ _)
    (le_trans (min_le_right _ _) hcon)
  linarith

end ResponseThreadCompletion
end NCG
