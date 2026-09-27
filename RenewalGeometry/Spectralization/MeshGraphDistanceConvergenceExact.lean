/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.EndpointBlockMetricHeadExact
import RenewalGeometry.Spectralization.A3ConnesFlatUniformConvergenceExact

/-!
# Geodesic convergence of mesh graph distances (metric-space surrogate)

Paper `predictive_spectral_geometry`, label `thm:supp-global-metric`, third clause
`eq:supp-global-metric-convergence` (also `eq:compact-spin-distance-main` of
`thm:compact-spin-main`), and the smooth seminorm clause.

Mathlib has no Riemannian distance on manifolds, so the closed Riemannian manifold
`(M, d_g)` is replaced by a (pseudo)metric space `X` with the **chain property**
`HasChains X`: every pair `x, y` is joined, at every scale `ρ > 0`, by a chain of at
most `d(x,y)/ρ + 1` points with consecutive distances `≤ ρ` summing to at most `d(x,y)`
(and `≥ ρ/2` when `d(x,y) ≥ ρ`).  This is exactly what partitioning a minimising
geodesic gives on a complete Riemannian manifold (Hopf–Rinow); it is proved here for
real normed spaces (`hasChains_of_normedSpace`).

A mesh (`MeshGraph`) is a finite edge-weighted graph (`EdgeGraph`) whose vertices are
placed in `X` so that (i) every point of `X` is within `h` of a vertex (an `h`-net),
(ii) every edge length dominates the distance of its endpoints (the edge is the length
of an actual curve), and (iii) any two vertices within `ρ + 2h` are joined by an edge of
length at most their distance plus a slack `κ` (a short curve of almost minimal length).

* `dist_le_graphDistance`: `d_g ≤ d_h^met` (telescoping).
* `graphDistance_le_dist_add`: `d_h^met ≤ d_g + (d_g/ρ + 1)(2h + κ)` — the paper's bound
  `d_g + C(ρ + h/ρ)` (with the geodesic partition, and `κ = 0` for exact edge lengths).
* `MeshSequence.exists_error_tendsto_zero` (**`eq:supp-global-metric-convergence`**): along
  meshes with `h/ρ → 0`, `κ/ρ → 0`, `ρ → 0` on a bounded chain space,
  `sup_{x,y ∈ V_h} |d_h^met(x,y) - d_g(x,y)| → 0` (an explicit error sequence bounds every
  pair and tends to zero); `..._of_compactSpace` is the closed-manifold form.
* `MeshSequence.tendsto_edgeLipschitz` (smooth seminorm clause): for a Lipschitz `f` whose
  optimal Lipschitz constant is `L` (for smooth `f` on a closed Riemannian manifold this is
  `‖∇_g f‖_∞`), `L_h^met(f|_{V_h}) → L`.
* `a3_flat_error_tendsto_zero`: the concrete flat `A₃` case
  (`A3ConnesFlatUniformConvergenceExact`) in the same error-sequence form.
-/

open Filter Topology Set
open RenewalGeometry.EndpointBlockMetricHead

namespace RenewalGeometry.MeshGraphDistanceConvergence

/-! ### Walks indexed by `Fin` -/

section walks

variable {V E : Type*}

/-- A vertex sequence `v : Fin (n+1) → V` with edges `e i` from `v i` to `v (i+1)` is a walk
`List.ofFn e` from `v 0` to `v (Fin.last n)`. -/
theorem isWalk_ofFn (Γ : EdgeGraph V E) :
    ∀ (n : ℕ) (v : Fin (n + 1) → V) (e : Fin n → E),
      (∀ i, Γ.src (e i) = v i.castSucc) → (∀ i, Γ.tgt (e i) = v i.succ) →
      IsWalk Γ (v 0) (List.ofFn e) (v (Fin.last n))
  | 0, v, e, _, _ => by
    rw [List.ofFn_zero]
    exact IsWalk.nil (Γ := Γ) (v 0)
  | n + 1, v, e, hs, ht => by
    rw [List.ofFn_succ]
    refine IsWalk.forward (by simpa using hs 0) ?_
    rw [ht 0]
    have := isWalk_ofFn Γ n (fun i => v i.succ) (fun i => e i.succ)
      (fun i => by simpa using hs i.succ) (fun i => by simpa using ht i.succ)
    simpa [Fin.succ_last] using this

theorem walkLength_ofFn (Γ : EdgeGraph V E) {n : ℕ} (e : Fin n → E) :
    walkLength Γ (List.ofFn e) = ∑ i, Γ.len (e i) := by
  simp [walkLength, List.map_ofFn, List.sum_ofFn]

/-- A vertex sequence whose consecutive vertices either coincide or are joined by an edge of
length `≤ b i` yields a walk of length `≤ Σ b i`. -/
theorem exists_walk_of_steps (Γ : EdgeGraph V E) :
    ∀ (n : ℕ) (v : Fin (n + 1) → V) (b : Fin n → ℝ), (∀ i, 0 ≤ b i) →
      (∀ i, v i.castSucc = v i.succ ∨
        ∃ e, Γ.src e = v i.castSucc ∧ Γ.tgt e = v i.succ ∧ Γ.len e ≤ b i) →
      ∃ w, IsWalk Γ (v 0) w (v (Fin.last n)) ∧ walkLength Γ w ≤ ∑ i, b i
  | 0, v, _, _, _ => ⟨[], IsWalk.nil _, by simp [walkLength_nil]⟩
  | n + 1, v, b, hb, hstep => by
    obtain ⟨w, hw, hl⟩ := exists_walk_of_steps Γ n (fun i => v i.succ) (fun i => b i.succ)
      (fun i => hb _) (fun i => hstep i.succ)
    rw [Fin.sum_univ_succ]
    simp only [Fin.succ_last] at hw
    rcases hstep 0 with heq | ⟨e, hs, ht, hle⟩
    · refine ⟨w, ?_, by linarith [hb 0]⟩
      simp only [Fin.castSucc_zero] at heq
      rw [heq]
      exact hw
    · refine ⟨e :: w, ?_, ?_⟩
      · refine IsWalk.forward (by simpa using hs) ?_
        rw [ht]
        exact hw
      · rw [walkLength_cons]
        linarith

end walks

/-! ### The chain property (surrogate of geodesic partitioning) -/

variable {X : Type*} [PseudoMetricSpace X]

/-- A chain of points from `x` to `y` at scale `ρ`: at most `d(x,y)/ρ + 1` steps, each of
length `≤ ρ` (and `≥ ρ/2` when `d(x,y) ≥ ρ`), of total length `≤ d(x,y)`.  On a complete
Riemannian manifold this is the partition of a minimising geodesic into equal pieces. -/
structure Chain (ρ : ℝ) (x y : X) where
  /-- number of steps -/
  n : ℕ
  /-- the chain points -/
  pts : Fin (n + 1) → X
  n_pos : 0 < n
  head : pts 0 = x
  last : pts (Fin.last n) = y
  step_le : ∀ i : Fin n, dist (pts i.castSucc) (pts i.succ) ≤ ρ
  sum_le : ∑ i : Fin n, dist (pts i.castSucc) (pts i.succ) ≤ dist x y
  count_le : (n : ℝ) ≤ dist x y / ρ + 1
  step_ge : ρ ≤ dist x y → ∀ i : Fin n, ρ / 2 ≤ dist (pts i.castSucc) (pts i.succ)

/-- The chain property: chains at every scale between all pairs of points (the surrogate
of "closed Riemannian manifold with its geodesic distance"). -/
def HasChains (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ ρ > (0 : ℝ), ∀ x y : X, Nonempty (Chain ρ x y)

/-- Real normed spaces have the chain property (equal subdivision of the segment). -/
theorem hasChains_of_normedSpace {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F] :
    HasChains F := by
  intro ρ hρ x y
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
  let pts : Fin (n + 1) → F := fun i => x + ((i : ℝ) / n) • (y - x)
  have hstep : ∀ i : Fin n, dist (pts i.castSucc) (pts i.succ) = d / n := by
    intro i
    simp only [pts, dist_eq_norm, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have e1 : x + ((i : ℝ) / n) • (y - x) - (x + (((i : ℝ) + 1) / n) • (y - x)) =
        ((i : ℝ) / n - ((i : ℝ) + 1) / n) • (y - x) := by
      rw [sub_smul]; abel
    have e2 : ((i : ℝ) / n - ((i : ℝ) + 1) / n) = -(1 / n) := by ring
    rw [e1, e2, neg_smul, norm_neg, norm_smul, hd, dist_eq_norm, norm_sub_rev, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  refine ⟨⟨n, pts, hn1, ?_, ?_, ?_, ?_, hnR, ?_⟩⟩
  · simp [pts]
  · simp [pts, hnpos.ne']
  · intro i
    rw [hstep i, div_le_iff₀ hnpos]
    calc d = d / ρ * ρ := by field_simp
      _ ≤ n * ρ := by gcongr
      _ = ρ * n := mul_comm _ _
  · simp only [hstep, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hnpos.ne']
  · intro hρd i
    rw [hstep i, le_div_iff₀ hnpos]
    have : (n : ℝ) ≤ 2 * d / ρ := by
      calc (n : ℝ) ≤ d / ρ + 1 := hnR
        _ ≤ d / ρ + d / ρ := by
            gcongr
            rw [le_div_iff₀ hρ]; linarith
        _ = 2 * d / ρ := by ring
    calc ρ / 2 * n ≤ ρ / 2 * (2 * d / ρ) := by gcongr
      _ = d := by field_simp

/-! ### Meshes -/

/-- A mesh on `X`: a finite edge-weighted graph placed in `X` by `point`, which is an `h`-net,
whose edge lengths dominate the endpoint distances, and in which vertices within `ρ + 2h`
are joined by an edge of length at most their distance plus the slack `κ`. -/
structure MeshGraph (X : Type*) [PseudoMetricSpace X] (V E : Type*) where
  /-- the finite metric head -/
  graph : EdgeGraph V E
  /-- vertex positions -/
  point : V → X
  /-- net scale `h` -/
  h : ℝ
  /-- mesoscopic radius `ρ_h` -/
  ρ : ℝ
  /-- slack of the edge lengths over the endpoint distance (`0` for minimising curves) -/
  κ : ℝ
  h_nonneg : 0 ≤ h
  ρ_pos : 0 < ρ
  κ_nonneg : 0 ≤ κ
  /-- every edge has the length of an actual curve: `ℓ_e ≥ d_g(x_e, y_e)` -/
  len_ge : ∀ e, dist (point (graph.src e)) (point (graph.tgt e)) ≤ graph.len e
  /-- the vertices form an `h`-net -/
  net : ∀ z : X, ∃ v, dist z (point v) ≤ h
  /-- distinct nearby vertices are joined by short edges -/
  edge_of_close : ∀ u v, u ≠ v → dist (point u) (point v) ≤ ρ + 2 * h →
    ∃ e, graph.src e = u ∧ graph.tgt e = v ∧ graph.len e ≤ dist (point u) (point v) + κ

namespace MeshGraph

variable {V E : Type*} (M : MeshGraph X V E)

theorem len_nonneg (e : E) : 0 ≤ M.graph.len e := dist_nonneg.trans (M.len_ge e)

/-- **Geodesic partitioning.** Replacing the points of a chain from `x` to `y` by mesh
vertices within `h` yields a walk of length at most
`d_g(x,y) + (d_g(x,y)/ρ + 1)(2h + κ)`. -/
theorem exists_walk_length_le (hX : HasChains X) (x y : V) :
    ∃ w, IsWalk M.graph x w y ∧
      walkLength M.graph w ≤ dist (M.point x) (M.point y) +
        (dist (M.point x) (M.point y) / M.ρ + 1) * (2 * M.h + M.κ) := by
  classical
  obtain ⟨c⟩ := hX M.ρ M.ρ_pos (M.point x) (M.point y)
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
      _ ≤ dist (M.point x) (M.point y) +
          (dist (M.point x) (M.point y) / M.ρ + 1) * (2 * M.h + M.κ) :=
          add_le_add c.sum_le (mul_le_mul_of_nonneg_right c.count_le
            (by linarith [M.h_nonneg, M.κ_nonneg]))

theorem connected (hX : HasChains X) : Connected M.graph :=
  fun x y => (M.exists_walk_length_le hX x y).imp fun _ hw => hw.1

/-- **Lower bound** `d_g ≤ d_h^met`: every graph edge has the length of an actual curve, so
telescoping along any walk dominates the distance. -/
theorem dist_le_graphDistance (hX : HasChains X) (x y : V) :
    dist (M.point x) (M.point y) ≤ graphDistance M.graph x y := by
  have := abs_sub_le_graphDistance (M.connected hX)
    (fun v => dist (M.point v) (M.point y)) (fun e => ?_) x y
  · simpa [abs_of_nonneg dist_nonneg] using this
  · refine (abs_dist_sub_le _ _ _).trans ?_
    rw [dist_comm]
    exact M.len_ge e

/-- **Upper bound** `d_h^met ≤ d_g + (d_g/ρ + 1)(2h + κ)`, the paper's
`d_g + C(ρ_h + h/ρ_h)`. -/
theorem graphDistance_le_dist_add (hX : HasChains X) (x y : V) :
    graphDistance M.graph x y ≤ dist (M.point x) (M.point y) +
      (dist (M.point x) (M.point y) / M.ρ + 1) * (2 * M.h + M.κ) := by
  obtain ⟨w, hw, hl⟩ := M.exists_walk_length_le hX x y
  exact (graphDistance_le_walkLength M.len_nonneg hw).trans hl

theorem abs_graphDistance_sub_dist_le (hX : HasChains X) (x y : V) :
    |graphDistance M.graph x y - dist (M.point x) (M.point y)| ≤
      (dist (M.point x) (M.point y) / M.ρ + 1) * (2 * M.h + M.κ) := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [M.graphDistance_le_dist_add hX x y]
  · linarith [M.dist_le_graphDistance hX x y, show 0 ≤ (dist (M.point x) (M.point y) / M.ρ + 1) *
      (2 * M.h + M.κ) by
        have := M.ρ_pos; have := M.h_nonneg; have := M.κ_nonneg; positivity]

/-- Uniform error on a space of diameter at most `Dm`. -/
theorem abs_graphDistance_sub_dist_le_uniform (hX : HasChains X) {Dm : ℝ}
    (hD : ∀ z w : X, dist z w ≤ Dm) (x y : V) :
    |graphDistance M.graph x y - dist (M.point x) (M.point y)| ≤
      (Dm / M.ρ + 1) * (2 * M.h + M.κ) := by
  refine (M.abs_graphDistance_sub_dist_le hX x y).trans ?_
  have := M.ρ_pos; have := M.h_nonneg; have := M.κ_nonneg
  gcongr
  exact hD _ _

/-! ### The edge Lipschitz seminorm of a Lipschitz function -/

/-- Upper bound: for `L`-Lipschitz `f`, `L_h^met(f|_{V_h}) ≤ L`. -/
theorem edgeLipschitz_le_of_lipschitz [Fintype E] {L : NNReal} {f : X → ℝ}
    (hf : LipschitzWith L f) :
    edgeLipschitz M.graph (f ∘ M.point) ≤ L := by
  rw [edgeLipschitz_le_iff _ _ L.coe_nonneg]
  intro e
  unfold edgeQuotient
  simp only [Function.comp]
  rcases (M.len_nonneg e).lt_or_eq with hpos | hzero
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |f (M.point (M.graph.tgt e)) - f (M.point (M.graph.src e))|
        ≤ L * dist (M.point (M.graph.tgt e)) (M.point (M.graph.src e)) := by
          rw [← Real.dist_eq]; exact hf.dist_le_mul _ _
      _ ≤ L * M.graph.len e := by
          gcongr
          rw [dist_comm]; exact M.len_ge e
  · rw [← hzero, div_zero, abs_zero]
    exact L.coe_nonneg

end MeshGraph

/-! ### Refining mesh sequences -/

/-- A sequence of meshes with `h_n/ρ_n → 0`, `κ_n/ρ_n → 0` and `ρ_n → 0` (for example
`ρ_h = h^{1/2}`, `κ = 0`). -/
structure MeshSequence (X : Type*) [PseudoMetricSpace X] (V E : ℕ → Type*) where
  /-- the meshes -/
  mesh : ∀ n, MeshGraph X (V n) (E n)
  h_div_ρ : Tendsto (fun n => (mesh n).h / (mesh n).ρ) atTop (𝓝 0)
  κ_div_ρ : Tendsto (fun n => (mesh n).κ / (mesh n).ρ) atTop (𝓝 0)
  ρ_tendsto : Tendsto (fun n => (mesh n).ρ) atTop (𝓝 0)

namespace MeshSequence

variable {V E : ℕ → Type*} (S : MeshSequence X V E)

/-- The uniform error bound of a mesh sequence on a space of diameter `≤ Dm`. -/
noncomputable def errorBound (Dm : ℝ) (n : ℕ) : ℝ :=
  (Dm / (S.mesh n).ρ + 1) * (2 * (S.mesh n).h + (S.mesh n).κ)

theorem h_tendsto : Tendsto (fun n => (S.mesh n).h) atTop (𝓝 0) := by
  have := S.ρ_tendsto.mul S.h_div_ρ
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  field_simp [(S.mesh n).ρ_pos.ne']

theorem κ_tendsto : Tendsto (fun n => (S.mesh n).κ) atTop (𝓝 0) := by
  have := S.ρ_tendsto.mul S.κ_div_ρ
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  field_simp [(S.mesh n).ρ_pos.ne']

theorem errorBound_tendsto (Dm : ℝ) : Tendsto (S.errorBound Dm) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => Dm * (2 * ((S.mesh n).h / (S.mesh n).ρ) +
      (S.mesh n).κ / (S.mesh n).ρ) + (2 * (S.mesh n).h + (S.mesh n).κ)) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := Dm)).mul
      (((tendsto_const_nhds (x := (2 : ℝ))).mul S.h_div_ρ).add S.κ_div_ρ)).add
      (((tendsto_const_nhds (x := (2 : ℝ))).mul S.h_tendsto).add S.κ_tendsto)
    simpa using this
  refine h1.congr fun n => ?_
  unfold errorBound
  field_simp [(S.mesh n).ρ_pos.ne']

/-- **`eq:supp-global-metric-convergence`** (metric-space surrogate).  On a bounded chain
space, the graph distances of a refining mesh sequence converge to the distance uniformly
over all vertex pairs: an explicit error sequence tending to zero bounds
`|d_h^met(x,y) - d_g(x,y)|` for every `n` and every `x, y ∈ V_h`. -/
theorem exists_error_tendsto_zero (hX : HasChains X) {Dm : ℝ} (hD : ∀ z w : X, dist z w ≤ Dm) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ n (x y : V n), |graphDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n :=
  ⟨S.errorBound Dm, S.errorBound_tendsto Dm,
    fun n x y => (S.mesh n).abs_graphDistance_sub_dist_le_uniform hX hD x y⟩

/-- The same on a compact chain space (the surrogate of a closed manifold). -/
theorem exists_error_tendsto_zero_of_compactSpace [CompactSpace X] (hX : HasChains X) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ n (x y : V n), |graphDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n :=
  S.exists_error_tendsto_zero hX fun z w =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ z) (mem_univ w)

/-- `ε`–`N` form: for every `ε > 0`, eventually all vertex pairs have error `< ε`. -/
theorem eventually_forall_abs_lt (hX : HasChains X) {Dm : ℝ} (hD : ∀ z w : X, dist z w ≤ Dm)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x y : V n, |graphDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| < ε := by
  obtain ⟨err, herr, hb⟩ := S.exists_error_tendsto_zero hX hD
  filter_upwards [herr.eventually (gt_mem_nhds hε)] with n hn x y
  exact (hb n x y).trans_lt hn

/-- The pure-state Connes distances of the metric heads converge to the distance as well
(`edgeConnesDistance = graphDistance` on every stage). -/
theorem exists_error_tendsto_zero_connes [∀ n, Fintype (E n)] (hX : HasChains X) {Dm : ℝ}
    (hD : ∀ z w : X, dist z w ≤ Dm) (hpos : ∀ n e, 0 < (S.mesh n).graph.len e) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ n (x y : V n), |edgeConnesDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n := by
  obtain ⟨err, herr, hb⟩ := S.exists_error_tendsto_zero hX hD
  refine ⟨err, herr, fun n x y => ?_⟩
  rw [edgeConnesDistance_eq_graphDistance _ (hpos n) ((S.mesh n).connected hX)]
  exact hb n x y

/-! ### The smooth seminorm clause: `L_h^met(f|_{V_h}) → Lip(f)` -/

/-- Telescoping along a `Fin`-indexed chain. -/
theorem abs_sub_last_le_sum : ∀ (n : ℕ) (g : Fin (n + 1) → ℝ),
    |g 0 - g (Fin.last n)| ≤ ∑ i : Fin n, |g i.castSucc - g i.succ|
  | 0, g => by simp
  | n + 1, g => by
    rw [Fin.sum_univ_succ]
    have ih := abs_sub_last_le_sum n (fun i => g i.succ)
    simp only [Fin.succ_last, Fin.succ_castSucc] at ih
    calc |g 0 - g (Fin.last (n + 1))|
        ≤ |g 0 - g (Fin.succ 0)| + |g (Fin.succ 0) - g (Fin.last (n + 1))| := abs_sub_le _ _ _
      _ ≤ |g (Fin.castSucc 0) - g (Fin.succ 0)| +
          ∑ i : Fin n, |g i.succ.castSucc - g i.succ.succ| :=
          add_le_add (le_of_eq (by simp)) ih

/-- Lower bound: if `L` is the optimal Lipschitz constant of `f` (witnessed by pairs
`x ≠ y` with `|f x - f y| ≥ (L - ε) d(x,y)`), then eventually
`L_h^met(f|_{V_h}) ≥ L - ε`.  A chain step where `f` almost realises `L - ε/2` is moved
to mesh vertices within `h`, and the corresponding short edge has quotient `≥ L - ε`
once `h/ρ` and `κ/ρ` are small. -/
theorem eventually_sub_le_edgeLipschitz [∀ n, Fintype (E n)] (hX : HasChains X) {L : NNReal}
    {f : X → ℝ} (hf : LipschitzWith L f)
    (hopt : ∀ ε > (0 : ℝ), ∃ x y : X, 0 < dist x y ∧ ((L : ℝ) - ε) * dist x y ≤ |f x - f y|)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (L : ℝ) - ε ≤ edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point) := by
  rcases le_or_gt ((L : ℝ) - ε) 0 with hneg | hpos
  · exact Eventually.of_forall fun n => hneg.trans (edgeLipschitz_nonneg _ _)
  obtain ⟨x, y, hd, hxy⟩ := hopt (ε / 2) (by positivity)
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  set η : ℝ := ε / (20 * ((L : ℝ) + 1)) with hη
  have hηpos : 0 < η := by positivity
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
  have hη20 : η < 1 / 20 := by
    rw [hη, div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  obtain ⟨c⟩ := hX M.ρ hρ x y
  -- telescoping along the chain and pigeonhole
  have htel : |f x - f y| ≤ ∑ i : Fin c.n, |f (c.pts i.castSucc) - f (c.pts i.succ)| := by
    have := abs_sub_last_le_sum c.n (fun i => f (c.pts i))
    simpa [c.head, c.last] using this
  have hL2 : 0 ≤ (L : ℝ) - ε / 2 := by linarith
  have hex : ∃ i : Fin c.n, ((L : ℝ) - ε / 2) * dist (c.pts i.castSucc) (c.pts i.succ) ≤
      |f (c.pts i.castSucc) - f (c.pts i.succ)| := by
    by_contra hcon
    push Not at hcon
    have hne : (Finset.univ : Finset (Fin c.n)).Nonempty := ⟨⟨0, c.n_pos⟩, Finset.mem_univ _⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne fun i _ => hcon i
    have hsum : ∑ i : Fin c.n, ((L : ℝ) - ε / 2) * dist (c.pts i.castSucc) (c.pts i.succ) ≤
        ((L : ℝ) - ε / 2) * dist x y := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left c.sum_le hL2
    linarith
  obtain ⟨i, hi⟩ := hex
  set za := c.pts i.castSucc with hza
  set zb := c.pts i.succ with hzb
  have hdi_le : dist za zb ≤ M.ρ := c.step_le i
  have hdi_ge : M.ρ / 2 ≤ dist za zb := c.step_ge hρd.le i
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
  have h2h : 2 * M.h < M.ρ / 2 := by nlinarith
  have hpv : 0 < dist (M.point va) (M.point vb) := by linarith
  have hne : va ≠ vb := fun h => by rw [h, dist_self] at hpv; exact lt_irrefl _ hpv
  obtain ⟨e, hs, ht, hl⟩ := M.edge_of_close va vb hne (hclose.trans (by linarith))
  have hlen_le : M.graph.len e ≤ dist za zb + 2 * M.h + M.κ := by linarith
  have hlen_ge : dist za zb - 2 * M.h ≤ M.graph.len e := by
    have h1 := M.len_ge e
    rw [hs, ht] at h1
    linarith
  have hlen_pos : 0 < M.graph.len e := by linarith
  have hf_ab : ((L : ℝ) - ε / 2) * dist za zb - 2 * L * M.h ≤
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
  have hkey : (L : ℝ) * (4 * M.h + M.κ) ≤ M.ρ * ε / 4 := by
    have hL1 : (0 : ℝ) < L + 1 := by positivity
    calc (L : ℝ) * (4 * M.h + M.κ) ≤ L * (5 * η * M.ρ) := by
          gcongr
          linarith
      _ = M.ρ * ε / 4 * ((L : ℝ) / (L + 1)) := by
          rw [hη]; field_simp; ring
      _ ≤ M.ρ * ε / 4 * 1 := by
          gcongr
          rw [div_le_one hL1]; linarith
      _ = M.ρ * ε / 4 := mul_one _
  have hquot : (L : ℝ) - ε ≤ |edgeQuotient M.graph (f ∘ M.point) e| := by
    unfold edgeQuotient
    simp only [Function.comp, hs, ht]
    rw [abs_div, abs_of_pos hlen_pos, le_div_iff₀ hlen_pos]
    have hstep1 : ((L : ℝ) - ε) * M.graph.len e ≤ ((L : ℝ) - ε) * (dist za zb + 2 * M.h + M.κ) :=
      mul_le_mul_of_nonneg_left hlen_le hpos.le
    have hstep2 : ((L : ℝ) - ε) * (2 * M.h + M.κ) ≤ L * (2 * M.h + M.κ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hstep3 : ε / 2 * (M.ρ / 2) ≤ ε / 2 * dist za zb :=
      mul_le_mul_of_nonneg_left hdi_ge (by positivity)
    nlinarith
  exact hquot.trans (abs_edgeQuotient_le_edgeLipschitz _ _ e)

/-- **Smooth seminorm clause of `thm:supp-global-metric`** (metric surrogate).  If `f` is
`L`-Lipschitz and `L` is its optimal Lipschitz constant (for smooth `f` on a closed
Riemannian manifold, `L = ‖∇_g f‖_∞`), then the finite Lip-norms of the metric heads
converge: `L_h^met(f|_{V_h}) → L`. -/
theorem tendsto_edgeLipschitz [∀ n, Fintype (E n)] (hX : HasChains X) {L : NNReal}
    {f : X → ℝ} (hf : LipschitzWith L f)
    (hopt : ∀ ε > (0 : ℝ), ∃ x y : X, 0 < dist x y ∧ ((L : ℝ) - ε) * dist x y ≤ |f x - f y|) :
    Tendsto (fun n => edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point)) atTop
      (𝓝 (L : ℝ)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hε : 0 < ((L : ℝ) - a) / 2 := by linarith
    filter_upwards [S.eventually_sub_le_edgeLipschitz hX hf hopt hε] with n hn
    linarith
  · exact Eventually.of_forall fun n =>
      ((S.mesh n).edgeLipschitz_le_of_lipschitz hf).trans_lt ha

end MeshSequence

/-! ### Existence of refining meshes on a compact space -/

universe u

/-- **Existence of finite metric triples on refining meshes.** Every compact metric space
admits a refining mesh sequence (`h_n = (n+1)⁻²`, `ρ_n = (n+1)⁻¹`, exact edge lengths
`κ = 0`) with finite vertex and edge sets and strictly positive edge lengths: the vertices
are finite `h_n`-nets (`finite_cover_balls_of_compact`) and the edges join distinct vertices
within `ρ_n + 2h_n`, weighted by their distance. -/
theorem exists_meshSequence {X : Type u} [MetricSpace X] [CompactSpace X] :
    ∃ (Vh Eh : ℕ → Type u) (_ : ∀ n, Fintype (Vh n)) (_ : ∀ n, Fintype (Eh n))
      (S : MeshSequence X Vh Eh), ∀ n e, 0 < (S.mesh n).graph.len e := by
  classical
  have hh : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) ^ 2 := fun n => by positivity
  choose t ht using fun n : ℕ => finite_cover_balls_of_compact (isCompact_univ (X := X)) (hh n)
  let Vh : ℕ → Type u := fun n => ↥(t n)
  let Eh : ℕ → Type u := fun n => {p : Vh n × Vh n // p.1 ≠ p.2 ∧
    dist (p.1 : X) (p.2 : X) ≤ 1 / ((n : ℝ) + 1) + 2 * (1 / ((n : ℝ) + 1) ^ 2)}
  let _ : ∀ n, Fintype (Vh n) := fun n => (ht n).2.1.fintype
  let mesh : ∀ n, MeshGraph X (Vh n) (Eh n) := fun n =>
    { graph := { src := fun e => e.1.1, tgt := fun e => e.1.2,
                 len := fun e => dist (e.1.1 : X) (e.1.2 : X) }
      point := fun v => (v : X)
      h := 1 / ((n : ℝ) + 1) ^ 2
      ρ := 1 / ((n : ℝ) + 1)
      κ := 0
      h_nonneg := (hh n).le
      ρ_pos := by positivity
      κ_nonneg := le_rfl
      len_ge := fun _ => le_rfl
      net := fun z => by
        have hz := (ht n).2.2 (Set.mem_univ z)
        rw [Set.mem_iUnion₂] at hz
        obtain ⟨x, hx, hxz⟩ := hz
        exact ⟨⟨x, hx⟩, (Metric.mem_ball.mp hxz).le⟩
      edge_of_close := fun u v huv hd => ⟨⟨(u, v), huv, hd⟩, rfl, rfl, by simp⟩ }
  have hρ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨Vh, Eh, inferInstance, fun n => Subtype.fintype _,
    { mesh := mesh
      h_div_ρ := ?_
      κ_div_ρ := ?_
      ρ_tendsto := hρ }, ?_⟩
  · refine hρ.congr fun n => ?_
    show 1 / ((n : ℝ) + 1) = (1 / ((n : ℝ) + 1) ^ 2) / (1 / ((n : ℝ) + 1))
    field_simp
  · refine (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr fun n => ?_
    show (0 : ℝ) = 0 / (1 / ((n : ℝ) + 1))
    rw [zero_div]
  · intro n e
    exact dist_pos.mpr (Subtype.val_injective.ne e.2.1)

/-! ### The flat `A₃` instance -/

open A3ConnesFlatUniformConvergence in
/-- The concrete flat torus case (`A3ConnesFlatUniformConvergenceExact`): the periodic `A₃`
Connes distances converge to the flat quotient distance uniformly, in the same
error-sequence form as `MeshSequence.exists_error_tendsto_zero`. -/
theorem a3_flat_error_tendsto_zero :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ n (x y : A3PeriodicGraphSampling.Vertex (n + 1)),
        |FiniteConnesDistanceAttainment.connesDistance (A3PeriodicGraphSampling.mass (n + 1))
            (A3PeriodicGraphSampling.conductance (n + 1)) x y -
          A3FlatTorusMetric.flatDistance (A3PeriodicGraphSampling.point (n + 1) x)
            (A3PeriodicGraphSampling.point (n + 1) y)| ≤ err n := by
  refine ⟨distanceError, tendsto_distanceError_zero, fun n x y => ?_⟩
  have := norm_le_pi_norm (fun xy : A3PeriodicGraphSampling.Vertex (n + 1) ×
    A3PeriodicGraphSampling.Vertex (n + 1) =>
    FiniteConnesDistanceAttainment.connesDistance (A3PeriodicGraphSampling.mass (n + 1))
      (A3PeriodicGraphSampling.conductance (n + 1)) xy.1 xy.2 -
      A3FlatTorusMetric.flatDistance (A3PeriodicGraphSampling.point (n + 1) xy.1)
        (A3PeriodicGraphSampling.point (n + 1) xy.2)) (x, y)
  simpa [distanceError, Real.norm_eq_abs] using this

end RenewalGeometry.MeshGraphDistanceConvergence
