/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.MeshGraphRatioSlack

/-!
# Mesh graph distance convergence under the approximate chain property

Paper `predictive_spectral_geometry`, label `thm:supp-global-metric`.

`MeshGraphDistanceConvergenceExact` and `MeshGraphRatioSlack` prove the theorem on a
pseudometric space with the *exact* chain property `HasChains` (partition of a minimising
geodesic).  A Riemannian distance is only an infimum of path lengths, so minimising curves need
not be available.  This file weakens the hypothesis to the **approximate chain property**
`HasApproxChains`: for every scale `ρ > 0` and every slack `δ > 0`, any two points are joined by a
chain whose steps are `≤ ρ + δ` (and `≥ ρ/2` when `ρ ≤ d(x,y)`), with at most `d(x,y)/ρ + 1`
steps, of total length `≤ d(x,y) + δ`.

* `hasApproxChains_of_nearGeodesic`: a space in which any two points are joined by continuous
  `δ`-near-geodesic paths (`d(x,γ s) + d(γ s,γ t) + d(γ t,y) ≤ d(x,y) + δ` for `s ≤ t`) has the
  approximate chain property.  The chain points are the first times the path reaches the
  distances `i d(x,y)/n` from `x` (intermediate value theorem).  This is how a Riemannian
  manifold is handled (`Analysis/RiemannianDistanceChains`).
* All results of the two surrogate files are re-proved under `HasApproxChains` (the additive
  `δ` is removed by letting `δ → 0` for a fixed mesh):
  `MeshGraph.graphDistance_le_dist_add_of_approx`,
  `ApproxMeshSequence.exists_error_tendsto_zero_of_approx`
  (**`eq:supp-global-metric-convergence`**), `MeshSequence.tendsto_edgeLipschitz_of_approx`,
  `ApproxMeshSequence.tendsto_edgeLipschitz_of_approx` and the packaged
  `ApproxMeshSequence.global_metric_of_approx`.
-/

open Filter Topology Set
open RenewalGeometry.EndpointBlockMetricHead

namespace RenewalGeometry.MeshGraphDistanceConvergence

variable {X : Type*} [PseudoMetricSpace X]

/-! ### Approximate chains -/

/-- An approximate chain from `x` to `y` at scale `ρ` with slack `δ`: at most `d(x,y)/ρ + 1`
steps, each of length `≤ ρ + δ` (and `≥ ρ/2` when `ρ ≤ d(x,y)`), of total length
`≤ d(x,y) + δ`. -/
structure ApproxChain (ρ δ : ℝ) (x y : X) where
  /-- number of steps -/
  n : ℕ
  /-- the chain points -/
  pts : Fin (n + 1) → X
  n_pos : 0 < n
  head : pts 0 = x
  last : pts (Fin.last n) = y
  step_le : ∀ i : Fin n, dist (pts i.castSucc) (pts i.succ) ≤ ρ + δ
  sum_le : ∑ i : Fin n, dist (pts i.castSucc) (pts i.succ) ≤ dist x y + δ
  count_le : (n : ℝ) ≤ dist x y / ρ + 1
  step_ge : ρ ≤ dist x y → ∀ i : Fin n, ρ / 2 ≤ dist (pts i.castSucc) (pts i.succ)

/-- The approximate chain property: approximate chains at every scale and every slack between
all pairs of points (the surrogate of a length space such as a Riemannian manifold). -/
def HasApproxChains (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ ρ > (0 : ℝ), ∀ δ > (0 : ℝ), ∀ x y : X, Nonempty (ApproxChain ρ δ x y)

/-- An exact chain is an approximate chain with any nonnegative slack. -/
def Chain.toApproxChain {ρ δ : ℝ} {x y : X} (c : Chain ρ x y) (hδ : 0 ≤ δ) :
    ApproxChain ρ δ x y where
  n := c.n
  pts := c.pts
  n_pos := c.n_pos
  head := c.head
  last := c.last
  step_le i := (c.step_le i).trans (by linarith)
  sum_le := c.sum_le.trans (by linarith)
  count_le := c.count_le
  step_ge := c.step_ge

/-- The exact chain property implies the approximate one. -/
theorem HasChains.hasApproxChains (hX : HasChains X) : HasApproxChains X :=
  fun ρ hρ _ hδ x y => (hX ρ hρ x y).map fun c => c.toApproxChain hδ.le

/-- **Near-geodesic paths give approximate chains.**  If any two points `x, y` are joined, for
every `δ > 0`, by a path `γ` continuous on `[0,1]` with `γ 0 = x`, `γ 1 = y` and
`d(x,γ s) + d(γ s,γ t) + d(γ t,y) ≤ d(x,y) + δ` for `0 ≤ s ≤ t ≤ 1` (for instance, a curve of
length `< d(x,y) + δ` in a length space), then the space has the approximate chain property. -/
theorem hasApproxChains_of_nearGeodesic
    (h : ∀ (x y : X) (δ : ℝ), 0 < δ → ∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧ γ 0 = x ∧
      γ 1 = y ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
        dist x (γ s) + dist (γ s) (γ t) + dist (γ t) y ≤ dist x y + δ) :
    HasApproxChains X := by
  intro ρ hρ δ hδ x y
  set d : ℝ := dist x y with hd
  have hd0 : 0 ≤ d := dist_nonneg
  set n : ℕ := max ⌈d / ρ⌉₊ 1 with hn
  have hn1 : 1 ≤ n := le_max_right _ _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnR : (n : ℝ) ≤ d / ρ + 1 := by
    rcases le_max_iff.mp (le_refl n) with h | h
    · have h' : n = ⌈d / ρ⌉₊ := le_antisymm h (le_max_left _ _)
      rw [h']
      exact (Nat.ceil_lt_add_one (by positivity)).le
    · have h' : n = 1 := le_antisymm h hn1
      rw [h']
      simp only [Nat.cast_one]
      linarith [show 0 ≤ d / ρ by positivity]
  have hdn : d / ρ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
  obtain ⟨γ, hγc, hγ0, hγ1, hγ⟩ := h x y (δ / n) (by positivity)
  -- the distance from `x` along the path
  set g : ℝ → ℝ := fun t => dist x (γ t) with hg
  have hgc : ContinuousOn g (Icc 0 1) :=
    continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγc)
  have hg0 : g 0 = 0 := by simp [hg, hγ0]
  have hg1 : g 1 = d := by simp [hg, hγ1, hd]
  -- first hitting times
  let S : ℝ → Set ℝ := fun c => Icc (0 : ℝ) 1 ∩ g ⁻¹' Ici c
  let τ : ℝ → ℝ := fun c => sInf (S c)
  have hSclosed : ∀ c, IsClosed (S c) := fun c =>
    hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSbdd : ∀ c, BddBelow (S c) := fun c => ⟨0, fun t ht => ht.1.1⟩
  have hSne : ∀ c, c ≤ d → (S c).Nonempty := fun c hc =>
    ⟨1, ⟨⟨zero_le_one, le_rfl⟩, by simp [hg1, hc]⟩⟩
  have hτmem : ∀ c, c ≤ d → τ c ∈ S c := fun c hc =>
    (hSclosed c).csInf_mem (hSne c hc) (hSbdd c)
  have hτg : ∀ c, 0 ≤ c → c ≤ d → g (τ c) = c := by
    intro c hc0 hcd
    have hm := hτmem c hcd
    refine le_antisymm ?_ hm.2
    by_contra hlt
    push Not at hlt
    have hτ0 : 0 ≤ τ c := hm.1.1
    have hivt := intermediate_value_Icc hτ0 (hgc.mono (Icc_subset_Icc le_rfl hm.1.2))
    obtain ⟨s, hs, hgs⟩ := hivt ⟨by rw [hg0]; exact hc0, hlt.le⟩
    have hsS : s ∈ S c := ⟨⟨hs.1, hs.2.trans hm.1.2⟩, by simp [hgs]⟩
    have hle : τ c ≤ s := csInf_le (hSbdd c) hsS
    have hse : s = τ c := le_antisymm hs.2 hle
    rw [← hse, hgs] at hlt
    exact lt_irrefl _ hlt
  have hτmono : ∀ c c', c ≤ c' → c' ≤ d → τ c ≤ τ c' := by
    intro c c' hcc' hc'd
    exact csInf_le_csInf (hSbdd c) (hSne c' hc'd) fun t ht => ⟨ht.1, le_trans hcc' ht.2⟩
  have hτ0 : τ 0 = 0 := by
    have hS0 : S 0 = Icc 0 1 := by
      ext t
      simp only [S, mem_inter_iff, mem_preimage, mem_Ici, and_iff_left_iff_imp]
      intro _
      exact dist_nonneg
    simp only [τ, hS0]
    exact csInf_Icc zero_le_one
  -- the parameter times: `τ (i d / n)` for `i < n`, and `1` at the end
  let T : ℕ → ℝ := fun i => if i < n then τ (i * d / n) else 1
  have hval : ∀ i : ℕ, i ≤ n → 0 ≤ (i : ℝ) * d / n ∧ (i : ℝ) * d / n ≤ d := by
    intro i hi
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hnpos]
    have : (i : ℝ) ≤ n := by exact_mod_cast hi
    nlinarith
  have hTmem : ∀ i : ℕ, i ≤ n → T i ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    by_cases hin : i < n
    · simp only [T, hin, ite_true]
      exact (hτmem _ (hval i hi).2).1
    · simp only [T, hin, ite_false]
      exact ⟨zero_le_one, le_rfl⟩
  have hTg : ∀ i : ℕ, i ≤ n → g (T i) = (i : ℝ) * d / n := by
    intro i hi
    by_cases hin : i < n
    · simp only [T, hin, ite_true]
      exact hτg _ (hval i hi).1 (hval i hi).2
    · simp only [T, hin, ite_false]
      have : i = n := le_antisymm hi (not_lt.mp hin)
      subst this
      rw [hg1]
      field_simp
  have hTmono : ∀ i : ℕ, i < n → T i ≤ T (i + 1) := by
    intro i hi
    have hTi : T i = τ (i * d / n) := by simp [T, hi]
    rw [hTi]
    by_cases hi1 : i + 1 < n
    · simp only [T, hi1, ite_true]
      refine hτmono _ _ ?_ (hval (i + 1) hi1.le).2
      push_cast
      gcongr
      linarith
    · simp only [T, hi1, ite_false]
      exact (hτmem _ (hval i hi.le).2).1.2
  have hT0 : T 0 = 0 := by simp [T, Nat.pos_of_ne_zero (by omega : n ≠ 0), hτ0]
  have hTn : T n = 1 := by simp [T]
  -- the step estimate
  have hstep : ∀ i : ℕ, i < n →
      d / n ≤ dist (γ (T i)) (γ (T (i + 1))) ∧ dist (γ (T i)) (γ (T (i + 1))) ≤ d / n + δ / n := by
    intro i hi
    have hgi := hTg i hi.le
    have hgi1 := hTg (i + 1) hi
    have hmi := hTmem i hi.le
    have hmi1 := hTmem (i + 1) hi
    have hnear := hγ (T i) (T (i + 1)) hmi.1 (hTmono i hi) hmi1.2
    have htri1 : g (T (i + 1)) ≤ g (T i) + dist (γ (T i)) (γ (T (i + 1))) := dist_triangle _ _ _
    have htri2 : d ≤ g (T (i + 1)) + dist (γ (T (i + 1))) y := dist_triangle _ _ _
    simp only [hg] at hgi hgi1 htri1 htri2
    have e : ((i + 1 : ℕ) : ℝ) * d / n = (i : ℝ) * d / n + d / n := by push_cast; ring
    rw [e] at hgi1
    constructor
    · linarith
    · linarith
  refine ⟨⟨n, fun i => γ (T i), by omega, ?_, ?_, ?_, ?_, hnR, ?_⟩⟩
  · simp [hT0, hγ0]
  · simp [hTn, hγ1]
  · intro i
    have := (hstep i i.isLt).2
    simp only [Fin.val_castSucc, Fin.val_succ]
    refine this.trans (add_le_add ?_ ?_)
    · rw [div_le_iff₀ hnpos]
      calc d = d / ρ * ρ := by field_simp
        _ ≤ n * ρ := by gcongr
        _ = ρ * n := mul_comm _ _
    · exact div_le_self hδ.le (by exact_mod_cast hn1)
  · calc ∑ i : Fin n, dist (γ (T i.castSucc)) (γ (T i.succ))
        ≤ ∑ _i : Fin n, (d / n + δ / n) := Finset.sum_le_sum fun i _ => by
          simpa using (hstep i i.isLt).2
      _ = d + δ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  · intro hρd i
    have := (hstep i i.isLt).1
    simp only [Fin.val_castSucc, Fin.val_succ]
    refine le_trans ?_ this
    rw [le_div_iff₀ hnpos]
    have : (n : ℝ) ≤ 2 * d / ρ := by
      calc (n : ℝ) ≤ d / ρ + 1 := hnR
        _ ≤ d / ρ + d / ρ := by
            gcongr
            rw [le_div_iff₀ hρ]; linarith
        _ = 2 * d / ρ := by ring
    calc ρ / 2 * n ≤ ρ / 2 * (2 * d / ρ) := by gcongr
      _ = d := by field_simp

/-! ### A limit lemma removing the additive slack -/

/-- If `a ≤ F δ` for all small `δ > 0` and `F` is continuous at `0`, then `a ≤ F 0`. -/
theorem le_of_forall_small_le {a ρ : ℝ} {F : ℝ → ℝ} (hρ : 0 < ρ) (hF : ContinuousAt F 0)
    (h : ∀ δ, 0 < δ → δ < ρ → a ≤ F δ) : a ≤ F 0 := by
  have ht : Tendsto F (𝓝[>] 0) (𝓝 (F 0)) := hF.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT hρ] with δ hδ using h δ hδ.1 hδ.2

/-- Continuity at `0` of the slack bound `δ ↦ A + δ + (B/(r - δ) + 1) c`. -/
theorem continuousAt_slackBound (A B c r : ℝ) (hr : 0 < r) :
    ContinuousAt (fun δ : ℝ => A + δ + (B / (r - δ) + 1) * c) 0 := by
  refine (continuousAt_const.add continuousAt_id).add
    (((continuousAt_const.div (continuousAt_const.sub continuousAt_id) ?_).add
      continuousAt_const).mul continuousAt_const)
  simpa using hr.ne'

/-! ### Meshes under the approximate chain property -/

namespace MeshGraph

variable {V E : Type*} (M : MeshGraph X V E)

/-- **Geodesic partitioning with slack.** Under the approximate chain property, for every
`0 < δ < ρ`, any two vertices are joined by a walk of length at most
`d + δ + (d/(ρ - δ) + 1)(2h + κ)`. -/
theorem exists_walk_length_le_of_approx (hX : HasApproxChains X) (x y : V) {δ : ℝ}
    (hδ : 0 < δ) (hδρ : δ < M.ρ) :
    ∃ w, IsWalk M.graph x w y ∧
      walkLength M.graph w ≤ dist (M.point x) (M.point y) + δ +
        (dist (M.point x) (M.point y) / (M.ρ - δ) + 1) * (2 * M.h + M.κ) := by
  classical
  obtain ⟨c⟩ := hX (M.ρ - δ) (by linarith) δ hδ (M.point x) (M.point y)
  choose v' hv' using fun i : Fin (c.n + 1) => M.net (c.pts i)
  let v : Fin (c.n + 1) → V := fun i =>
    if i = 0 then x else if i = Fin.last c.n then y else v' i
  have hlast_ne : Fin.last c.n ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at this
    exact c.n_pos.ne' this
  have hv0 : v 0 = x := by simp [v]
  have hvl : v (Fin.last c.n) = y := by simp [v, hlast_ne]
  have hv : ∀ i, dist (c.pts i) (M.point (v i)) ≤ M.h := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      rw [hv0, c.head, dist_self]
      exact M.h_nonneg
    · by_cases hl : i = Fin.last c.n
      · subst hl
        rw [hvl, c.last, dist_self]
        exact M.h_nonneg
      · simp only [v, h0, hl, ite_false]
        exact hv' i
  have hclose : ∀ i : Fin c.n, dist (M.point (v i.castSucc)) (M.point (v i.succ)) ≤
      dist (c.pts i.castSucc) (c.pts i.succ) + 2 * M.h := by
    intro i
    calc dist (M.point (v i.castSucc)) (M.point (v i.succ))
        ≤ dist (M.point (v i.castSucc)) (c.pts i.castSucc) +
          dist (c.pts i.castSucc) (c.pts i.succ) + dist (c.pts i.succ) (M.point (v i.succ)) :=
          dist_triangle4 _ _ _ _
      _ ≤ M.h + dist (c.pts i.castSucc) (c.pts i.succ) + M.h := by
          gcongr
          · rw [dist_comm]; exact hv _
          · exact hv _
      _ = dist (c.pts i.castSucc) (c.pts i.succ) + 2 * M.h := by ring
  have hstep : ∀ i : Fin c.n, v i.castSucc = v i.succ ∨
      ∃ e, M.graph.src e = v i.castSucc ∧ M.graph.tgt e = v i.succ ∧
        M.graph.len e ≤ dist (c.pts i.castSucc) (c.pts i.succ) + 2 * M.h + M.κ := by
    intro i
    by_cases hvv : v i.castSucc = v i.succ
    · exact Or.inl hvv
    obtain ⟨e, hs, ht, hl⟩ := M.edge_of_close _ _ hvv
      ((hclose i).trans (by linarith [c.step_le i]))
    exact Or.inr ⟨e, hs, ht, by linarith [hclose i]⟩
  obtain ⟨w, hw, hl⟩ := exists_walk_of_steps M.graph c.n v _
    (fun i => by linarith [dist_nonneg (x := c.pts i.castSucc) (y := c.pts i.succ),
      M.h_nonneg, M.κ_nonneg]) hstep
  rw [hv0, hvl] at hw
  refine ⟨w, hw, hl.trans ?_⟩
  calc ∑ i : Fin c.n, (dist (c.pts i.castSucc) (c.pts i.succ) + 2 * M.h + M.κ)
      _ = ∑ i : Fin c.n, dist (c.pts i.castSucc) (c.pts i.succ) + c.n * (2 * M.h + M.κ) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ dist (M.point x) (M.point y) + δ +
          (dist (M.point x) (M.point y) / (M.ρ - δ) + 1) * (2 * M.h + M.κ) :=
          add_le_add c.sum_le (mul_le_mul_of_nonneg_right c.count_le
            (by linarith [M.h_nonneg, M.κ_nonneg]))

theorem connected_of_approx (hX : HasApproxChains X) : Connected M.graph := fun x y =>
  (M.exists_walk_length_le_of_approx hX x y (half_pos M.ρ_pos) (half_lt_self M.ρ_pos)).imp
    fun _ hw => hw.1

/-- `d_g ≤ d_h^met` under the approximate chain property. -/
theorem dist_le_graphDistance_of_approx (hX : HasApproxChains X) (x y : V) :
    dist (M.point x) (M.point y) ≤ graphDistance M.graph x y := by
  have := abs_sub_le_graphDistance (M.connected_of_approx hX)
    (fun v => dist (M.point v) (M.point y)) (fun e => ?_) x y
  · simpa [abs_of_nonneg dist_nonneg] using this
  · refine (abs_dist_sub_le _ _ _).trans ?_
    rw [dist_comm]
    exact M.len_ge e

/-- **Upper bound** `d_h^met ≤ d_g + (d_g/ρ + 1)(2h + κ)` under the approximate chain property
(the same bound as `graphDistance_le_dist_add`; the slack `δ` is sent to `0`). -/
theorem graphDistance_le_dist_add_of_approx (hX : HasApproxChains X) (x y : V) :
    graphDistance M.graph x y ≤ dist (M.point x) (M.point y) +
      (dist (M.point x) (M.point y) / M.ρ + 1) * (2 * M.h + M.κ) := by
  have := le_of_forall_small_le M.ρ_pos
    (continuousAt_slackBound (dist (M.point x) (M.point y)) (dist (M.point x) (M.point y))
      (2 * M.h + M.κ) M.ρ M.ρ_pos) fun δ hδ hδρ => by
    obtain ⟨w, hw, hl⟩ := M.exists_walk_length_le_of_approx hX x y hδ hδρ
    exact (graphDistance_le_walkLength M.len_nonneg hw).trans hl
  simpa using this

theorem abs_graphDistance_sub_dist_le_of_approx (hX : HasApproxChains X) (x y : V) :
    |graphDistance M.graph x y - dist (M.point x) (M.point y)| ≤
      (dist (M.point x) (M.point y) / M.ρ + 1) * (2 * M.h + M.κ) := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [M.graphDistance_le_dist_add_of_approx hX x y]
  · linarith [M.dist_le_graphDistance_of_approx hX x y,
      show 0 ≤ (dist (M.point x) (M.point y) / M.ρ + 1) * (2 * M.h + M.κ) by
        have := M.ρ_pos; have := M.h_nonneg; have := M.κ_nonneg; positivity]

end MeshGraph

/-! ### Exact-length mesh sequences under the approximate chain property -/

namespace MeshSequence

variable {V E : ℕ → Type*} (S : MeshSequence X V E)

/-- **`eq:supp-global-metric-convergence`** for exact-length meshes under the approximate chain
property, on a space of diameter `≤ Dm`. -/
theorem exists_error_tendsto_zero_of_approx (hX : HasApproxChains X) {Dm : ℝ}
    (hD : ∀ z w : X, dist z w ≤ Dm) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ n (x y : V n), |graphDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n := by
  refine ⟨S.errorBound Dm, S.errorBound_tendsto Dm, fun n x y => ?_⟩
  refine ((S.mesh n).abs_graphDistance_sub_dist_le_of_approx hX x y).trans ?_
  have := (S.mesh n).ρ_pos; have := (S.mesh n).h_nonneg; have := (S.mesh n).κ_nonneg
  unfold errorBound
  gcongr
  exact hD _ _

/-- Lower bound for the edge Lipschitz seminorm under the approximate chain property: if `L` is
the optimal Lipschitz constant of `f`, then eventually `L_h^met(f|_{V_h}) ≥ L - ε`.  An
approximate chain at scale `ρ/2` with slack `ηρ` contains a step on which `f` almost realises
`L - 3ε/4`; it is moved to mesh vertices within `h`. -/
theorem eventually_sub_le_edgeLipschitz_of_approx [∀ n, Fintype (E n)] (hX : HasApproxChains X)
    {L : NNReal} {f : X → ℝ} (hf : LipschitzWith L f)
    (hopt : ∀ ε > (0 : ℝ), ∃ x y : X, 0 < dist x y ∧ ((L : ℝ) - ε) * dist x y ≤ |f x - f y|)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (L : ℝ) - ε ≤ edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point) := by
  rcases le_or_gt ((L : ℝ) - ε) 0 with hneg | hpos
  · exact Eventually.of_forall fun n => hneg.trans (edgeLipschitz_nonneg _ _)
  obtain ⟨x, y, hd, hxy⟩ := hopt (ε / 2) (by positivity)
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  set η : ℝ := ε / (100 * ((L : ℝ) + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hL1 : (0 : ℝ) < L + 1 := by positivity
  have hLη : (L : ℝ) * η ≤ ε / 100 := by
    rw [hη, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  filter_upwards [S.ρ_tendsto.eventually (gt_mem_nhds hd),
    S.h_div_ρ.eventually (gt_mem_nhds hηpos), S.κ_div_ρ.eventually (gt_mem_nhds hηpos)]
    with n hρd hhρ hκρ
  set M := S.mesh n with hM
  have hρ := M.ρ_pos
  have hh := M.h_nonneg
  have hκ := M.κ_nonneg
  have hhρ' : M.h < η * M.ρ := by rwa [div_lt_iff₀ hρ] at hhρ
  have hκρ' : M.κ < η * M.ρ := by rwa [div_lt_iff₀ hρ] at hκρ
  have hεL : ε < L := by linarith
  have hη100 : η < 1 / 100 := by
    rw [hη, div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  obtain ⟨c⟩ := hX (M.ρ / 2) (by positivity) (η * M.ρ) (by positivity) x y
  -- telescoping along the chain and pigeonhole
  have htel : |f x - f y| ≤ ∑ i : Fin c.n, |f (c.pts i.castSucc) - f (c.pts i.succ)| := by
    have := abs_sub_last_le_sum c.n (fun i => f (c.pts i))
    simpa [c.head, c.last] using this
  have hL3 : 0 ≤ (L : ℝ) - 3 * ε / 4 := by linarith
  have hex : ∃ i : Fin c.n, ((L : ℝ) - 3 * ε / 4) * dist (c.pts i.castSucc) (c.pts i.succ) ≤
      |f (c.pts i.castSucc) - f (c.pts i.succ)| := by
    by_contra hcon
    push Not at hcon
    have hne : (Finset.univ : Finset (Fin c.n)).Nonempty := ⟨⟨0, c.n_pos⟩, Finset.mem_univ _⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne fun i _ => hcon i
    have hsum : ∑ i : Fin c.n, ((L : ℝ) - 3 * ε / 4) * dist (c.pts i.castSucc) (c.pts i.succ) ≤
        ((L : ℝ) - 3 * ε / 4) * (dist x y + η * M.ρ) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left c.sum_le hL3
    have h1 : ((L : ℝ) - 3 * ε / 4) * (η * M.ρ) ≤ (L : ℝ) * η * dist x y := by
      calc ((L : ℝ) - 3 * ε / 4) * (η * M.ρ) ≤ (L : ℝ) * (η * M.ρ) := by
            gcongr; linarith
        _ ≤ (L : ℝ) * (η * dist x y) := by gcongr
        _ = (L : ℝ) * η * dist x y := by ring
    have h2 : (L : ℝ) * η * dist x y ≤ ε / 100 * dist x y :=
      mul_le_mul_of_nonneg_right hLη hd.le
    nlinarith
  obtain ⟨i, hi⟩ := hex
  set za := c.pts i.castSucc with hza
  set zb := c.pts i.succ with hzb
  have hdi_le : dist za zb ≤ M.ρ / 2 + η * M.ρ := c.step_le i
  have hdi_ge : M.ρ / 2 / 2 ≤ dist za zb := c.step_ge (by linarith) i
  obtain ⟨va, hva⟩ := M.net za
  obtain ⟨vb, hvb⟩ := M.net zb
  have hclose : dist (M.point va) (M.point vb) ≤ dist za zb + 2 * M.h := by
    calc dist (M.point va) (M.point vb)
        ≤ dist (M.point va) za + dist za zb + dist zb (M.point vb) := dist_triangle4 _ _ _ _
      _ ≤ M.h + dist za zb + M.h :=
          add_le_add (add_le_add (by rw [dist_comm]; exact hva) le_rfl) hvb
      _ = dist za zb + 2 * M.h := by ring
  have hfar : dist za zb ≤ dist (M.point va) (M.point vb) + 2 * M.h := by
    calc dist za zb
        ≤ dist za (M.point va) + dist (M.point va) (M.point vb) + dist (M.point vb) zb :=
          dist_triangle4 _ _ _ _
      _ ≤ M.h + dist (M.point va) (M.point vb) + M.h :=
          add_le_add (add_le_add hva le_rfl) (by rw [dist_comm]; exact hvb)
      _ = dist (M.point va) (M.point vb) + 2 * M.h := by ring
  have hηρ : η * M.ρ < M.ρ / 100 := by nlinarith
  have hpv : 0 < dist (M.point va) (M.point vb) := by linarith
  have hne : va ≠ vb := fun h => by rw [h, dist_self] at hpv; exact lt_irrefl _ hpv
  obtain ⟨e, hs, ht, hl⟩ := M.edge_of_close va vb hne (hclose.trans (by linarith))
  have hlen_le : M.graph.len e ≤ dist za zb + 2 * M.h + M.κ := by linarith
  have hlen_ge : dist za zb - 2 * M.h ≤ M.graph.len e := by
    have h1 := M.len_ge e
    rw [hs, ht] at h1
    linarith
  have hlen_pos : 0 < M.graph.len e := by linarith
  have hf_ab : ((L : ℝ) - 3 * ε / 4) * dist za zb - 2 * L * M.h ≤
      |f (M.point vb) - f (M.point va)| := by
    have h1 : |f zb - f (M.point vb)| ≤ L * M.h := by
      rw [← Real.dist_eq]
      exact (hf.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hvb hL0)
    have h2 : |f (M.point va) - f za| ≤ L * M.h := by
      rw [← Real.dist_eq, dist_comm]
      exact (hf.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hva hL0)
    have h3 : |f za - f zb| ≤ |f (M.point va) - f za| + |f (M.point vb) - f (M.point va)| +
        |f zb - f (M.point vb)| := by
      have : f za - f zb = -((f (M.point va) - f za) + (f (M.point vb) - f (M.point va)) +
          (f zb - f (M.point vb))) := by ring
      rw [this, abs_neg]
      exact abs_add_three _ _ _
    linarith
  -- the small-parameter inequality
  have hkey : (L : ℝ) * (4 * M.h + M.κ) ≤ M.ρ * ε / 16 := by
    calc (L : ℝ) * (4 * M.h + M.κ) ≤ L * (5 * η * M.ρ) := by
          gcongr
          linarith
      _ = 5 * ((L : ℝ) * η) * M.ρ := by ring
      _ ≤ 5 * (ε / 100) * M.ρ := by gcongr
      _ ≤ M.ρ * ε / 16 := by nlinarith
  have hquot : (L : ℝ) - ε ≤ |edgeQuotient M.graph (f ∘ M.point) e| := by
    unfold edgeQuotient
    simp only [Function.comp, hs, ht]
    rw [abs_div, abs_of_pos hlen_pos, le_div_iff₀ hlen_pos]
    have hstep1 : ((L : ℝ) - ε) * M.graph.len e ≤ ((L : ℝ) - ε) * (dist za zb + 2 * M.h + M.κ) :=
      mul_le_mul_of_nonneg_left hlen_le hpos.le
    have hstep2 : ((L : ℝ) - ε) * (2 * M.h + M.κ) ≤ L * (2 * M.h + M.κ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hstep3 : ε / 4 * (M.ρ / 2 / 2) ≤ ε / 4 * dist za zb :=
      mul_le_mul_of_nonneg_left hdi_ge (by positivity)
    nlinarith
  exact hquot.trans (abs_edgeQuotient_le_edgeLipschitz _ _ e)

/-- **Smooth seminorm clause** for exact-length meshes under the approximate chain property:
`L_h^met(f|_{V_h}) → L` for `f` with optimal Lipschitz constant `L`. -/
theorem tendsto_edgeLipschitz_of_approx [∀ n, Fintype (E n)] (hX : HasApproxChains X)
    {L : NNReal} {f : X → ℝ} (hf : LipschitzWith L f)
    (hopt : ∀ ε > (0 : ℝ), ∃ x y : X, 0 < dist x y ∧ ((L : ℝ) - ε) * dist x y ≤ |f x - f y|) :
    Tendsto (fun n => edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point)) atTop
      (𝓝 (L : ℝ)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hε : 0 < ((L : ℝ) - a) / 2 := by linarith
    filter_upwards [S.eventually_sub_le_edgeLipschitz_of_approx hX hf hopt hε] with n hn
    linarith
  · exact Eventually.of_forall fun n =>
      ((S.mesh n).edgeLipschitz_le_of_lipschitz hf).trans_lt ha

end MeshSequence

/-! ### Approximate-length meshes under the approximate chain property -/

namespace ApproxMeshGraph

variable {V E : Type*} (M : ApproxMeshGraph X V E)

theorem connected_of_approx (hX : HasApproxChains X) (hρ : 2 * M.h < M.ρ) :
    Connected M.graph := fun x y => by
  obtain ⟨w, hw⟩ := (M.toMeshGraph hρ).connected_of_approx hX x y
  exact ⟨_, (M.isWalk_map hw).1⟩

/-- `(1 - ε) d_g ≤ d_h^met` under the approximate chain property. -/
theorem one_sub_mul_dist_le_graphDistance_of_approx (hX : HasApproxChains X)
    (hρ : 2 * M.h < M.ρ) (x y : V) :
    (1 - M.ε) * dist (M.point x) (M.point y) ≤ graphDistance M.graph x y := by
  have h1 : 0 ≤ 1 - M.ε := by linarith [M.ε_lt_one]
  have := abs_sub_le_graphDistance (M.connected_of_approx hX hρ)
    (fun v => (1 - M.ε) * dist (M.point v) (M.point y)) (fun e => ?_) x y
  · simpa [abs_of_nonneg (mul_nonneg h1 dist_nonneg)] using this
  · rw [← mul_sub, abs_mul, abs_of_nonneg h1]
    refine le_trans ?_ (M.le_len e)
    gcongr
    refine (abs_dist_sub_le _ _ _).trans ?_
    rw [dist_comm]
    rfl

/-- `d_h^met ≤ (1 + ε)(d_g + (d_g/(ρ - 2h) + 1) 2h)` under the approximate chain property. -/
theorem graphDistance_le_of_approx (hX : HasApproxChains X) (hρ : 2 * M.h < M.ρ) (x y : V) :
    graphDistance M.graph x y ≤ (1 + M.ε) * (dist (M.point x) (M.point y) +
      (dist (M.point x) (M.point y) / (M.ρ - 2 * M.h) + 1) * (2 * M.h)) := by
  have hρ' : 0 < M.ρ - 2 * M.h := by linarith
  have hcont : ContinuousAt (fun δ : ℝ => (1 + M.ε) * (dist (M.point x) (M.point y) + δ +
      (dist (M.point x) (M.point y) / ((M.ρ - 2 * M.h) - δ) + 1) * (2 * M.h + 0))) 0 :=
    continuousAt_const.mul (continuousAt_slackBound _ _ _ _ hρ')
  have := le_of_forall_small_le hρ' hcont fun δ hδ hδρ => by
    obtain ⟨w, hw, hl⟩ := (M.toMeshGraph hρ).exists_walk_length_le_of_approx hX x y hδ hδρ
    obtain ⟨hw', hl'⟩ := M.isWalk_map hw
    refine (graphDistance_le_walkLength (fun e => (M.len_pos e).le) hw').trans (hl'.trans ?_)
    have : (1 : ℝ) + M.ε ≥ 0 := by linarith [M.ε_nonneg]
    exact mul_le_mul_of_nonneg_left (by simpa [toMeshGraph] using hl) this
  simpa using this

/-- Two-sided error under the approximate chain property. -/
theorem abs_graphDistance_sub_dist_le_of_approx (hX : HasApproxChains X) (hρ : 2 * M.h < M.ρ)
    (x y : V) :
    |graphDistance M.graph x y - dist (M.point x) (M.point y)| ≤
      M.ε * dist (M.point x) (M.point y) + (1 + M.ε) *
        ((dist (M.point x) (M.point y) / (M.ρ - 2 * M.h) + 1) * (2 * M.h)) := by
  have hu := M.graphDistance_le_of_approx hX hρ x y
  have hl := M.one_sub_mul_dist_le_graphDistance_of_approx hX hρ x y
  have hd : 0 ≤ dist (M.point x) (M.point y) := dist_nonneg
  have hρ' : 0 < M.ρ - 2 * M.h := by linarith
  have h0 : 0 ≤ (1 + M.ε) * ((dist (M.point x) (M.point y) / (M.ρ - 2 * M.h) + 1) * (2 * M.h)) := by
    have := M.ε_nonneg; have := M.h_nonneg; positivity
  rw [abs_sub_le_iff]
  constructor <;> nlinarith [M.ε_nonneg]

end ApproxMeshGraph

namespace ApproxMeshSequence

variable {V E : ℕ → Type*} (S : ApproxMeshSequence X V E)

/-- **`eq:supp-global-metric-convergence`** under the general mesh assumptions and the
approximate chain property, on a space of diameter `≤ Dm`. -/
theorem exists_error_tendsto_zero_of_approx (hX : HasApproxChains X) {Dm : ℝ}
    (hD : ∀ z w : X, dist z w ≤ Dm) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ x y : V n, |graphDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n := by
  refine ⟨S.errorBound Dm, S.errorBound_tendsto Dm, ?_⟩
  filter_upwards [S.eventually_four_h_le] with n hn x y
  set M := S.mesh n
  have hρ := M.ρ_pos
  have hh := M.h_nonneg
  have hε := M.ε_nonneg
  have h2 : 2 * M.h < M.ρ := by linarith
  have hb := M.abs_graphDistance_sub_dist_le_of_approx hX h2 x y
  set d := dist (M.point x) (M.point y)
  have hd0 : 0 ≤ d := dist_nonneg
  have hdD : d ≤ Dm := hD _ _
  have hρ' : M.ρ / 2 ≤ M.ρ - 2 * M.h := by linarith
  have hq : d / (M.ρ - 2 * M.h) ≤ 2 * Dm / M.ρ := by
    rw [div_le_div_iff₀ (by linarith) hρ]
    nlinarith
  refine hb.trans ?_
  unfold errorBound
  have e1 : (2 * Dm / M.ρ + 1) * (2 * M.h) = 4 * Dm * (M.h / M.ρ) + 2 * M.h := by
    field_simp; ring
  rw [← e1]
  gcongr

/-- The same on a compact space. -/
theorem exists_error_tendsto_zero_of_approx_of_compactSpace [CompactSpace X]
    (hX : HasApproxChains X) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ x y : V n, |graphDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n :=
  S.exists_error_tendsto_zero_of_approx hX fun z w =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ z) (mem_univ w)

/-- **Smooth seminorm clause** under the general mesh assumptions and the approximate chain
property: `L_h^met(f|_{V_h}) → L` for `f` with optimal Lipschitz constant `L`. -/
theorem tendsto_edgeLipschitz_of_approx [∀ n, Fintype (E n)] (hX : HasApproxChains X)
    {L : NNReal} {f : X → ℝ} (hf : LipschitzWith L f)
    (hopt : ∀ ε > (0 : ℝ), ∃ x y : X, 0 < dist x y ∧ ((L : ℝ) - ε) * dist x y ≤ |f x - f y|) :
    Tendsto (fun n => edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point)) atTop
      (𝓝 (L : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp S.eventually_four_h_le
  rw [← tendsto_add_atTop_iff_nat N]
  have hex := (S.exactShift N hN).tendsto_edgeLipschitz_of_approx hX hf hopt
  have hεN := S.ε_tendsto.comp (tendsto_add_atTop_nat N)
  have hlow : Tendsto (fun n => edgeLipschitz (S.exactShift N hN |>.mesh n).graph
      (f ∘ (S.exactShift N hN |>.mesh n).point) / (1 + (S.mesh (n + N)).ε)) atTop
      (𝓝 (L : ℝ)) := by
    have := hex.div ((tendsto_const_nhds (x := (1 : ℝ))).add hεN) (by norm_num)
    simp only [add_zero, div_one] at this
    exact this
  have hup : Tendsto (fun n => edgeLipschitz (S.exactShift N hN |>.mesh n).graph
      (f ∘ (S.exactShift N hN |>.mesh n).point) / (1 - (S.mesh (n + N)).ε)) atTop
      (𝓝 (L : ℝ)) := by
    have := hex.div ((tendsto_const_nhds (x := (1 : ℝ))).sub hεN) (by norm_num)
    simp only [sub_zero, div_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n => ?_) (fun n => ?_)
  · set M := S.mesh (n + N)
    have h1 : 0 < 1 + M.ε := by linarith [M.ε_nonneg]
    rw [div_le_iff₀ h1, mul_comm]
    exact M.edgeLipschitz_exact_le _
  · set M := S.mesh (n + N)
    have h1 : 0 < 1 - M.ε := by linarith [M.ε_lt_one]
    rw [le_div_iff₀ h1, mul_comm]
    exact M.one_sub_mul_edgeLipschitz_le _

end ApproxMeshSequence

/-! ### The packaged theorem under the approximate chain property -/

section Packaged

open scoped Matrix.Norms.L2Operator

/-- **`thm:supp-global-metric` under the general mesh assumptions and the approximate chain
property** (compact pseudometric space in which any two points are joined by near-minimising
chains, e.g. a compact Riemannian manifold).  For a refining sequence of approximate meshes:
1. `‖[D_h^met, π_h(f)]‖ = max_e |f(x_e) - f(y_e)|/ℓ_e` (`eq:supp-edge-lip`);
2. eventually the pure-state Connes distance is the graph shortest-path metric;
3. `sup_{x,y ∈ V_h} |d_h^met(x,y) - d(x,y)| → 0` (`eq:supp-global-metric-convergence`);
4. for `f` with optimal Lipschitz constant `L`, `L_h^met(f|_{V_h}) → L`. -/
theorem ApproxMeshSequence.global_metric_of_approx {V E : ℕ → Type*}
    (S : ApproxMeshSequence X V E) [∀ n, Fintype (E n)] [∀ n, DecidableEq (E n)]
    [CompactSpace X] (hX : HasApproxChains X) :
    (∀ n (g : V n → ℝ),
      ‖metricDirac (S.mesh n).graph * endpointRepresentation (S.mesh n).graph g -
        endpointRepresentation (S.mesh n).graph g * metricDirac (S.mesh n).graph‖ =
        edgeLipschitz (S.mesh n).graph g) ∧
    (∀ᶠ n in atTop, ∀ x y : V n,
      edgeConnesDistance (S.mesh n).graph x y = graphDistance (S.mesh n).graph x y) ∧
    (∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ x y : V n, |graphDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n) ∧
    (∀ {L : NNReal} {f : X → ℝ}, LipschitzWith L f →
      (∀ ε > (0 : ℝ), ∃ x y : X, 0 < dist x y ∧ ((L : ℝ) - ε) * dist x y ≤ |f x - f y|) →
      Tendsto (fun n => edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point)) atTop
        (𝓝 (L : ℝ))) := by
  refine ⟨fun n g => norm_commutator_eq_edgeLipschitz _ g, ?_,
    S.exists_error_tendsto_zero_of_approx_of_compactSpace hX,
    fun hf hopt => S.tendsto_edgeLipschitz_of_approx hX hf hopt⟩
  filter_upwards [S.eventually_four_h_le] with n h4 x y
  have h2 : 2 * (S.mesh n).h < (S.mesh n).ρ := by
    linarith [(S.mesh n).ρ_pos, (S.mesh n).h_nonneg]
  exact edgeConnesDistance_eq_graphDistance _ (S.mesh n).len_pos
    ((S.mesh n).connected_of_approx hX h2) x y

end Packaged

end RenewalGeometry.MeshGraphDistanceConvergence
