/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.MeshGraphDistanceConvergenceExact

/-!
# Geodesic convergence of endpoint metric triples with approximate edge lengths

Paper `predictive_spectral_geometry`, label `thm:supp-global-metric`, under the paper's general
mesh assumptions: an `h`-net `V_h`, a mesoscopic radius `ρ_h` with `h/ρ_h → 0`, `ρ_h → 0`, every
pair of vertices with `d(x,y) ≤ ρ_h` joined by an (unoriented) edge, and **positive edge lengths
with `sup_{E_h} |ℓ_h/d - 1| ≤ ε_h → 0`** (lengths may undershoot the distance).  The
closed Riemannian manifold is replaced, as in `MeshGraphDistanceConvergenceExact`, by a
pseudometric space with the chain property `HasChains` (geodesic partitioning).

* `ApproxMeshGraph`: the mesh data with ratio slack `ε` (`ε = 0` is `ℓ_h = d_g`);
* `ApproxMeshGraph.toMeshGraph`: when `2h < ρ`, the same vertices with both orientations of every
  edge and exact lengths `d` form a `MeshGraph` at radius `ρ - 2h` (slack `κ = 0`);
* `ApproxMeshGraph.one_sub_mul_dist_le_graphDistance`: `(1 - ε) d ≤ d_h^met`;
* `ApproxMeshGraph.graphDistance_le`: `d_h^met ≤ (1 + ε)(d + (d/(ρ-2h) + 1) 2h)`;
* `ApproxMeshSequence.exists_error_tendsto_zero` (**`eq:supp-global-metric-convergence`**):
  an explicit error sequence tending to zero eventually bounds `|d_h^met(x,y) - d(x,y)|` for all
  vertex pairs; `exists_error_tendsto_zero_connes` for the pure-state Connes distance;
* `ApproxMeshSequence.tendsto_edgeLipschitz` (smooth seminorm clause):
  `L_h^met(f|_{V_h}) → L` for `f` with optimal Lipschitz constant `L` (`= ‖∇_g f‖_∞` for smooth
  `f` on a closed Riemannian manifold).

The first two clauses (`eq:supp-edge-lip` and Connes distance = graph distance) hold for any
positive lengths (`EndpointBlockMetricHeadExact`).
-/

open Filter Topology Set
open RenewalGeometry.EndpointBlockMetricHead

namespace RenewalGeometry.MeshGraphDistanceConvergence

variable {X : Type*} [PseudoMetricSpace X]

/-- A mesh with approximate edge lengths (the paper's general mesh assumptions): an `h`-net,
every pair of distinct vertices at distance `≤ ρ` joined by an unoriented edge, and positive
edge lengths with `|ℓ_e / d(x_e, y_e) - 1| ≤ ε`. -/
structure ApproxMeshGraph (X : Type*) [PseudoMetricSpace X] (V E : Type*) where
  /-- the finite metric head -/
  graph : EdgeGraph V E
  /-- vertex positions -/
  point : V → X
  /-- net scale `h` -/
  h : ℝ
  /-- mesoscopic radius `ρ_h` -/
  ρ : ℝ
  /-- ratio slack `ε_h` of the edge lengths -/
  ε : ℝ
  h_nonneg : 0 ≤ h
  ρ_pos : 0 < ρ
  ε_nonneg : 0 ≤ ε
  ε_lt_one : ε < 1
  /-- positive edge lengths -/
  len_pos : ∀ e, 0 < graph.len e
  /-- `|ℓ_h / d_g - 1| ≤ ε` on every edge -/
  len_ratio : ∀ e, |graph.len e / dist (point (graph.src e)) (point (graph.tgt e)) - 1| ≤ ε
  /-- the vertices form an `h`-net -/
  net : ∀ z : X, ∃ v, dist z (point v) ≤ h
  /-- every pair of distinct vertices within `ρ` is joined by an (unoriented) edge -/
  edge_of_close : ∀ u v, u ≠ v → dist (point u) (point v) ≤ ρ →
    ∃ e, (graph.src e = u ∧ graph.tgt e = v) ∨ (graph.src e = v ∧ graph.tgt e = u)

namespace ApproxMeshGraph

variable {V E : Type*} (M : ApproxMeshGraph X V E)

/-- The distance of the endpoints of an edge (`d_g(x_e, y_e)`). -/
noncomputable def edgeDist (e : E) : ℝ := dist (M.point (M.graph.src e)) (M.point (M.graph.tgt e))

theorem edgeDist_pos (e : E) : 0 < M.edgeDist e := by
  rcases (dist_nonneg : 0 ≤ M.edgeDist e).lt_or_eq with h | h
  · exact h
  · have := M.len_ratio e
    have h' : M.edgeDist e = 0 := h.symm
    rw [← edgeDist, h', div_zero, zero_sub, abs_neg, abs_one] at this
    exact absurd M.ε_lt_one (not_lt.mpr this)

theorem len_le (e : E) : M.graph.len e ≤ (1 + M.ε) * M.edgeDist e := by
  have h := (abs_sub_le_iff.mp (M.len_ratio e)).1
  have hd := M.edgeDist_pos e
  rw [← edgeDist, sub_le_iff_le_add, div_le_iff₀ hd] at h
  linarith

theorem le_len (e : E) : (1 - M.ε) * M.edgeDist e ≤ M.graph.len e := by
  have h := (abs_sub_le_iff.mp (M.len_ratio e)).2
  have hd := M.edgeDist_pos e
  rw [← edgeDist, sub_le_comm, le_div_iff₀ hd] at h
  linarith

/-- Both orientations of every edge, with exact lengths `d(x_e, y_e)`. -/
noncomputable def exactGraph : EdgeGraph V (E ⊕ E) where
  src := Sum.elim M.graph.src M.graph.tgt
  tgt := Sum.elim M.graph.tgt M.graph.src
  len e' := dist (M.point (Sum.elim M.graph.src M.graph.tgt e'))
    (M.point (Sum.elim M.graph.tgt M.graph.src e'))

theorem exactGraph_len_inl (e : E) : M.exactGraph.len (Sum.inl e) = M.edgeDist e := rfl

theorem exactGraph_len_inr (e : E) : M.exactGraph.len (Sum.inr e) = M.edgeDist e := dist_comm _ _

/-- For `2h < ρ`, the exact-length doubled graph is a `MeshGraph` at radius `ρ - 2h` with slack
`κ = 0`. -/
noncomputable def toMeshGraph (hρ : 2 * M.h < M.ρ) : MeshGraph X V (E ⊕ E) where
  graph := M.exactGraph
  point := M.point
  h := M.h
  ρ := M.ρ - 2 * M.h
  κ := 0
  h_nonneg := M.h_nonneg
  ρ_pos := by linarith
  κ_nonneg := le_rfl
  len_ge _ := le_rfl
  net := M.net
  edge_of_close u v huv hd := by
    obtain ⟨e, he⟩ := M.edge_of_close u v huv (by linarith)
    rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact ⟨Sum.inl e, hs, ht, by simp [exactGraph, hs, ht]⟩
    · exact ⟨Sum.inr e, ht, hs, by simp [exactGraph, hs, ht]⟩

theorem len_elim_le (e' : E ⊕ E) :
    M.graph.len (Sum.elim id id e') ≤ (1 + M.ε) * M.exactGraph.len e' := by
  rcases e' with e | e
  · exact M.len_le e
  · rw [exactGraph_len_inr]; exact M.len_le e

/-- Walks of the doubled exact graph are walks of the mesh, with length inflated by at most
`1 + ε`. -/
theorem isWalk_map {x y : V} {w : List (E ⊕ E)} (hw : IsWalk M.exactGraph x w y) :
    IsWalk M.graph x (w.map (Sum.elim id id)) y ∧
      walkLength M.graph (w.map (Sum.elim id id)) ≤ (1 + M.ε) * walkLength M.exactGraph w := by
  induction hw with
  | nil x => exact ⟨IsWalk.nil x, by simp [walkLength_nil]⟩
  | @forward x y e' w h hw ih =>
    refine ⟨?_, ?_⟩
    · rcases e' with e | e
      · exact IsWalk.forward h ih.1
      · exact IsWalk.backward h ih.1
    · rw [List.map_cons, walkLength_cons, walkLength_cons, mul_add]
      exact add_le_add (M.len_elim_le e') ih.2
  | @backward x y e' w h hw ih =>
    refine ⟨?_, ?_⟩
    · rcases e' with e | e
      · exact IsWalk.backward h ih.1
      · exact IsWalk.forward h ih.1
    · rw [List.map_cons, walkLength_cons, walkLength_cons, mul_add]
      exact add_le_add (M.len_elim_le e') ih.2

theorem connected (hX : HasChains X) (hρ : 2 * M.h < M.ρ) : Connected M.graph := fun x y => by
  obtain ⟨w, hw⟩ := (M.toMeshGraph hρ).connected hX x y
  exact ⟨_, (M.isWalk_map hw).1⟩

/-- **Lower bound** `(1 - ε) d_g ≤ d_h^met` (telescoping with the allowed approximate
lengths). -/
theorem one_sub_mul_dist_le_graphDistance (hX : HasChains X) (hρ : 2 * M.h < M.ρ) (x y : V) :
    (1 - M.ε) * dist (M.point x) (M.point y) ≤ graphDistance M.graph x y := by
  have h1 : 0 ≤ 1 - M.ε := by linarith [M.ε_lt_one]
  have := abs_sub_le_graphDistance (M.connected hX hρ)
    (fun v => (1 - M.ε) * dist (M.point v) (M.point y)) (fun e => ?_) x y
  · simpa [abs_of_nonneg (mul_nonneg h1 dist_nonneg)] using this
  · rw [← mul_sub, abs_mul, abs_of_nonneg h1]
    refine le_trans ?_ (M.le_len e)
    gcongr
    refine (abs_dist_sub_le _ _ _).trans ?_
    rw [dist_comm]
    rfl

/-- **Upper bound** `d_h^met ≤ (1 + ε)(d_g + (d_g/(ρ - 2h) + 1) 2h)` (geodesic partitioning at
scale `ρ - 2h` and replacement of the partition points by net vertices). -/
theorem graphDistance_le (hX : HasChains X) (hρ : 2 * M.h < M.ρ) (x y : V) :
    graphDistance M.graph x y ≤ (1 + M.ε) * (dist (M.point x) (M.point y) +
      (dist (M.point x) (M.point y) / (M.ρ - 2 * M.h) + 1) * (2 * M.h)) := by
  obtain ⟨w, hw, hl⟩ := (M.toMeshGraph hρ).exists_walk_length_le hX x y
  obtain ⟨hw', hl'⟩ := M.isWalk_map hw
  refine (graphDistance_le_walkLength (fun e => (M.len_pos e).le) hw').trans (hl'.trans ?_)
  have : (1 : ℝ) + M.ε ≥ 0 := by linarith [M.ε_nonneg]
  have hl2 : walkLength M.exactGraph w ≤ dist (M.point x) (M.point y) +
      (dist (M.point x) (M.point y) / (M.ρ - 2 * M.h) + 1) * (2 * M.h) := by
    simpa [toMeshGraph] using hl
  exact mul_le_mul_of_nonneg_left hl2 this

/-- Two-sided error `|d_h^met - d_g| ≤ ε d_g + (1 + ε)(d_g/(ρ - 2h) + 1) 2h`. -/
theorem abs_graphDistance_sub_dist_le (hX : HasChains X) (hρ : 2 * M.h < M.ρ) (x y : V) :
    |graphDistance M.graph x y - dist (M.point x) (M.point y)| ≤
      M.ε * dist (M.point x) (M.point y) + (1 + M.ε) *
        ((dist (M.point x) (M.point y) / (M.ρ - 2 * M.h) + 1) * (2 * M.h)) := by
  have hu := M.graphDistance_le hX hρ x y
  have hl := M.one_sub_mul_dist_le_graphDistance hX hρ x y
  have hd : 0 ≤ dist (M.point x) (M.point y) := dist_nonneg
  have hρ' : 0 < M.ρ - 2 * M.h := by linarith
  have h0 : 0 ≤ (1 + M.ε) * ((dist (M.point x) (M.point y) / (M.ρ - 2 * M.h) + 1) * (2 * M.h)) := by
    have := M.ε_nonneg; have := M.h_nonneg; positivity
  rw [abs_sub_le_iff]
  constructor <;> nlinarith [M.ε_nonneg]

/-! ### Edge Lipschitz seminorms of the approximate and exact meshes -/

variable [Fintype E]

theorem abs_edgeQuotient_exact (f : V → ℝ) (e : E) :
    |edgeQuotient M.exactGraph f (Sum.inl e)| =
      |f (M.graph.tgt e) - f (M.graph.src e)| / M.edgeDist e ∧
    |edgeQuotient M.exactGraph f (Sum.inr e)| =
      |f (M.graph.tgt e) - f (M.graph.src e)| / M.edgeDist e := by
  have hd := M.edgeDist_pos e
  constructor
  · simp only [edgeQuotient, exactGraph_len_inl]
    rw [abs_div, abs_of_pos hd]
    rfl
  · simp only [edgeQuotient, exactGraph_len_inr]
    rw [abs_div, abs_of_pos hd, abs_sub_comm]
    rfl

/-- `(1 - ε) L_h^met(f) ≤ L^exact(f)`. -/
theorem one_sub_mul_edgeLipschitz_le (f : V → ℝ) :
    (1 - M.ε) * edgeLipschitz M.graph f ≤ edgeLipschitz M.exactGraph f := by
  have h1 : 0 < 1 - M.ε := by linarith [M.ε_lt_one]
  rw [← le_div_iff₀' h1, edgeLipschitz_le_iff _ _ (div_nonneg (edgeLipschitz_nonneg _ _) h1.le)]
  intro e
  have hd := M.edgeDist_pos e
  have hq := abs_edgeQuotient_le_edgeLipschitz M.exactGraph f (Sum.inl e)
  rw [(M.abs_edgeQuotient_exact f e).1] at hq
  rw [le_div_iff₀' h1]
  unfold edgeQuotient
  rw [abs_div, abs_of_pos (M.len_pos e)]
  calc (1 - M.ε) * (|f (M.graph.tgt e) - f (M.graph.src e)| / M.graph.len e)
      ≤ (1 - M.ε) * (|f (M.graph.tgt e) - f (M.graph.src e)| / ((1 - M.ε) * M.edgeDist e)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos h1 hd) (M.le_len e)) h1.le
    _ = |f (M.graph.tgt e) - f (M.graph.src e)| / M.edgeDist e := by
        field_simp
    _ ≤ edgeLipschitz M.exactGraph f := hq

/-- `L^exact(f) ≤ (1 + ε) L_h^met(f)`. -/
theorem edgeLipschitz_exact_le (f : V → ℝ) :
    edgeLipschitz M.exactGraph f ≤ (1 + M.ε) * edgeLipschitz M.graph f := by
  have hε := M.ε_nonneg
  rw [edgeLipschitz_le_iff _ _ (mul_nonneg (by linarith) (edgeLipschitz_nonneg _ _))]
  have key : ∀ e, |f (M.graph.tgt e) - f (M.graph.src e)| / M.edgeDist e ≤
      (1 + M.ε) * edgeLipschitz M.graph f := by
    intro e
    have hd := M.edgeDist_pos e
    have hq := abs_edgeQuotient_le_edgeLipschitz M.graph f e
    unfold edgeQuotient at hq
    rw [abs_div, abs_of_pos (M.len_pos e)] at hq
    rw [div_le_iff₀ hd]
    calc |f (M.graph.tgt e) - f (M.graph.src e)|
        = |f (M.graph.tgt e) - f (M.graph.src e)| / M.graph.len e * M.graph.len e := by
          field_simp [(M.len_pos e).ne']
      _ ≤ edgeLipschitz M.graph f * ((1 + M.ε) * M.edgeDist e) :=
          mul_le_mul hq (M.len_le e) (M.len_pos e).le (edgeLipschitz_nonneg _ _)
      _ = (1 + M.ε) * edgeLipschitz M.graph f * M.edgeDist e := by ring
  rintro (e | e)
  · rw [(M.abs_edgeQuotient_exact f e).1]; exact key e
  · rw [(M.abs_edgeQuotient_exact f e).2]; exact key e

end ApproxMeshGraph

/-! ### Refining sequences of approximate meshes -/

/-- A sequence of approximate meshes with `h_n/ρ_n → 0`, `ρ_n → 0` and `ε_n → 0`
(`sup_{E_h} |ℓ_h/d_g - 1| → 0`). -/
structure ApproxMeshSequence (X : Type*) [PseudoMetricSpace X] (V E : ℕ → Type*) where
  /-- the meshes -/
  mesh : ∀ n, ApproxMeshGraph X (V n) (E n)
  h_div_ρ : Tendsto (fun n => (mesh n).h / (mesh n).ρ) atTop (𝓝 0)
  ε_tendsto : Tendsto (fun n => (mesh n).ε) atTop (𝓝 0)
  ρ_tendsto : Tendsto (fun n => (mesh n).ρ) atTop (𝓝 0)

namespace ApproxMeshSequence

variable {V E : ℕ → Type*} (S : ApproxMeshSequence X V E)

theorem h_tendsto : Tendsto (fun n => (S.mesh n).h) atTop (𝓝 0) := by
  have := S.ρ_tendsto.mul S.h_div_ρ
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  field_simp [(S.mesh n).ρ_pos.ne']

theorem eventually_four_h_le : ∀ᶠ n in atTop, 4 * (S.mesh n).h ≤ (S.mesh n).ρ := by
  filter_upwards [S.h_div_ρ.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))]
    with n hn
  rw [div_le_iff₀ (S.mesh n).ρ_pos] at hn
  linarith

/-- The explicit error bound `ε_n D + (1 + ε_n)(4 D h_n/ρ_n + 2 h_n)`. -/
noncomputable def errorBound (Dm : ℝ) (n : ℕ) : ℝ :=
  (S.mesh n).ε * Dm + (1 + (S.mesh n).ε) *
    (4 * Dm * ((S.mesh n).h / (S.mesh n).ρ) + 2 * (S.mesh n).h)

theorem errorBound_tendsto (Dm : ℝ) : Tendsto (S.errorBound Dm) atTop (𝓝 0) := by
  have := (S.ε_tendsto.mul (tendsto_const_nhds (x := Dm))).add
    (((tendsto_const_nhds (x := (1 : ℝ))).add S.ε_tendsto).mul
      (((tendsto_const_nhds (x := 4 * Dm)).mul S.h_div_ρ).add
        ((tendsto_const_nhds (x := (2 : ℝ))).mul S.h_tendsto)))
  unfold errorBound
  simpa using this

/-- **`eq:supp-global-metric-convergence`** under the general mesh assumptions (approximate
lengths with `sup |ℓ_h/d_g - 1| → 0`), metric-space surrogate: on a chain space of diameter
`≤ Dm`, an explicit error sequence tending to zero eventually bounds
`|d_h^met(x,y) - d_g(x,y)|` uniformly over all vertex pairs. -/
theorem exists_error_tendsto_zero (hX : HasChains X) {Dm : ℝ} (hD : ∀ z w : X, dist z w ≤ Dm) :
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
  have hb := M.abs_graphDistance_sub_dist_le hX h2 x y
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

/-- The pure-state Connes distances converge as well (`edgeConnesDistance = graphDistance`
for positive lengths on a connected graph). -/
theorem exists_error_tendsto_zero_connes [∀ n, Fintype (E n)] (hX : HasChains X) {Dm : ℝ}
    (hD : ∀ z w : X, dist z w ≤ Dm) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ x y : V n, |edgeConnesDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n := by
  obtain ⟨err, herr, hb⟩ := S.exists_error_tendsto_zero hX hD
  refine ⟨err, herr, ?_⟩
  filter_upwards [hb, S.eventually_four_h_le] with n hn h4 x y
  have h2 : 2 * (S.mesh n).h < (S.mesh n).ρ := by
    linarith [(S.mesh n).ρ_pos, (S.mesh n).h_nonneg]
  rw [edgeConnesDistance_eq_graphDistance _ (S.mesh n).len_pos ((S.mesh n).connected hX h2)]
  exact hn x y

/-- The same on a compact chain space (the surrogate of a closed manifold). -/
theorem exists_error_tendsto_zero_of_compactSpace [CompactSpace X] (hX : HasChains X) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ x y : V n, |graphDistance (S.mesh n).graph x y -
        dist ((S.mesh n).point x) ((S.mesh n).point y)| ≤ err n :=
  S.exists_error_tendsto_zero hX fun z w =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ z) (mem_univ w)

/-- The shifted sequence of exact doubled meshes, a `MeshSequence` (from the index `N` on,
where `4h ≤ ρ`). -/
noncomputable def exactShift (N : ℕ) (hN : ∀ n ≥ N, 4 * (S.mesh n).h ≤ (S.mesh n).ρ) :
    MeshSequence X (fun n => V (n + N)) (fun n => E (n + N) ⊕ E (n + N)) where
  mesh n := (S.mesh (n + N)).toMeshGraph (by
    have := hN (n + N) (Nat.le_add_left _ _)
    linarith [(S.mesh (n + N)).ρ_pos, (S.mesh (n + N)).h_nonneg])
  h_div_ρ := by
    have hr := S.h_div_ρ.comp (tendsto_add_atTop_nat N)
    have := hr.div ((tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hr)) (by norm_num)
    simp only [mul_zero, sub_zero, div_one] at this
    refine this.congr fun n => ?_
    have hρ := (S.mesh (n + N)).ρ_pos
    simp only [Function.comp_apply, Pi.div_apply, ApproxMeshGraph.toMeshGraph]
    have e : 1 - 2 * ((S.mesh (n + N)).h / (S.mesh (n + N)).ρ) =
        ((S.mesh (n + N)).ρ - 2 * (S.mesh (n + N)).h) / (S.mesh (n + N)).ρ := by
      field_simp
    rw [e, div_div_div_cancel_right₀ hρ.ne']
  κ_div_ρ := by
    simp only [ApproxMeshGraph.toMeshGraph, zero_div]
    exact tendsto_const_nhds
  ρ_tendsto := by
    have := (S.ρ_tendsto.comp (tendsto_add_atTop_nat N)).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul (S.h_tendsto.comp (tendsto_add_atTop_nat N)))
    simp only [mul_zero, sub_zero] at this
    exact this

/-- **Smooth seminorm clause of `thm:supp-global-metric`** under the general mesh assumptions
(metric surrogate): if `f` is `L`-Lipschitz with optimal constant `L` (for smooth `f` on a
closed Riemannian manifold, `L = ‖∇_g f‖_∞`), then `L_h^met(f|_{V_h}) → L`. -/
theorem tendsto_edgeLipschitz [∀ n, Fintype (E n)] (hX : HasChains X) {L : NNReal}
    {f : X → ℝ} (hf : LipschitzWith L f)
    (hopt : ∀ ε > (0 : ℝ), ∃ x y : X, 0 < dist x y ∧ ((L : ℝ) - ε) * dist x y ≤ |f x - f y|) :
    Tendsto (fun n => edgeLipschitz (S.mesh n).graph (f ∘ (S.mesh n).point)) atTop
      (𝓝 (L : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp S.eventually_four_h_le
  rw [← tendsto_add_atTop_iff_nat N]
  have hex := (S.exactShift N hN).tendsto_edgeLipschitz hX hf hopt
  have hεN := S.ε_tendsto.comp (tendsto_add_atTop_nat N)
  have hlow : Tendsto (fun n => edgeLipschitz (S.exactShift N hN |>.mesh n).graph
      (f ∘ (S.exactShift N hN |>.mesh n).point) / (1 + (S.mesh (n + N)).ε)) atTop (𝓝 (L : ℝ)) := by
    have := hex.div ((tendsto_const_nhds (x := (1 : ℝ))).add hεN) (by norm_num)
    simp only [add_zero, div_one] at this
    exact this
  have hup : Tendsto (fun n => edgeLipschitz (S.exactShift N hN |>.mesh n).graph
      (f ∘ (S.exactShift N hN |>.mesh n).point) / (1 - (S.mesh (n + N)).ε)) atTop (𝓝 (L : ℝ)) := by
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

/-! ### Exact lengths are the `ε = 0` instance -/

/-- Exact edge lengths `ℓ_h = d_g` (with positive endpoint distances) give an approximate mesh
with `ε = 0`. -/
noncomputable def ApproxMeshGraph.ofExact {V E : Type*} (Γ : EdgeGraph V E) (point : V → X)
    (h ρ : ℝ) (hh : 0 ≤ h) (hρ : 0 < ρ)
    (hlen : ∀ e, Γ.len e = dist (point (Γ.src e)) (point (Γ.tgt e)))
    (hpos : ∀ e, 0 < Γ.len e) (net : ∀ z : X, ∃ v, dist z (point v) ≤ h)
    (hedge : ∀ u v, u ≠ v → dist (point u) (point v) ≤ ρ →
      ∃ e, (Γ.src e = u ∧ Γ.tgt e = v) ∨ (Γ.src e = v ∧ Γ.tgt e = u)) :
    ApproxMeshGraph X V E where
  graph := Γ
  point := point
  h := h
  ρ := ρ
  ε := 0
  h_nonneg := hh
  ρ_pos := hρ
  ε_nonneg := le_rfl
  ε_lt_one := one_pos
  len_pos := hpos
  len_ratio e := by
    rw [← hlen e, div_self (hpos e).ne', sub_self, abs_zero]
  net := net
  edge_of_close := hedge

/-! ### The packaged theorem -/

section Packaged

open scoped Matrix.Norms.L2Operator

/-- **`thm:supp-global-metric` under the general mesh assumptions** (metric-space surrogate of
the closed Riemannian manifold: a compact pseudometric space with the chain property).  For a
refining sequence of approximate meshes (`h/ρ → 0`, `ρ → 0`, `sup |ℓ_h/d - 1| → 0`, all pairs
within `ρ_h` joined, positive lengths):
1. `‖[D_h^met, π_h(f)]‖ = max_e |f(x_e) - f(y_e)|/ℓ_e` (`eq:supp-edge-lip`);
2. eventually the pure-state Connes distance is the graph shortest-path metric;
3. `sup_{x,y ∈ V_h} |d_h^met(x,y) - d(x,y)| → 0` (`eq:supp-global-metric-convergence`);
4. for `f` with optimal Lipschitz constant `L` (`‖∇_g f‖_∞` in the smooth case),
   `L_h^met(f|_{V_h}) → L`. -/
theorem ApproxMeshSequence.global_metric {V E : ℕ → Type*} (S : ApproxMeshSequence X V E)
    [∀ n, Fintype (E n)] [∀ n, DecidableEq (E n)] [CompactSpace X] (hX : HasChains X) :
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
    S.exists_error_tendsto_zero_of_compactSpace hX,
    fun hf hopt => S.tendsto_edgeLipschitz hX hf hopt⟩
  filter_upwards [S.eventually_four_h_le] with n h4 x y
  have h2 : 2 * (S.mesh n).h < (S.mesh n).ρ := by
    linarith [(S.mesh n).ρ_pos, (S.mesh n).h_nonneg]
  exact edgeConnesDistance_eq_graphDistance _ (S.mesh n).len_pos ((S.mesh n).connected hX h2) x y

end Packaged

end RenewalGeometry.MeshGraphDistanceConvergence
