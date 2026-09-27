/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Continuum.LipschitzLimitGradientBoundExact
import RenewalGeometry.Spectralization.A3ConnesFlatUniformConvergenceExact

/-!
# Sharp gradient bound for limits of discrete unit-Lipschitz functions on the `A₃` graphs

Paper `predictive_spectral_geometry`, label `lem:supp-A3-compactness`, sharp constant
`eq:supp-A3-limit-Lip`.

A discrete unit-ball function `f_n` (`graphLipschitz ≤ 1`) satisfies
`|f_n x - f_n y| ≤ d_n(x, y)` for the finite Connes distance `d_n`
(`abs_sub_le_connesDistance`), and the Connes distances converge uniformly to the flat
torus distance (`A3ConnesFlatUniformConvergenceExact`).  Hence the uniform limit `F` of the
Lipschitz extensions is `1`-Lipschitz for the flat distance on the fundamental parallelepiped
of the period lattice (`parallelepiped basis`, the torus `M` as a set), and Rademacher's
theorem gives `‖∇F‖ ≤ 1` almost everywhere on it (`a3_limit_sharp_gradient_bound`).

Compared with the paper: the periodic piecewise-affine interpolants on `M` are replaced by
the exact Euclidean Lipschitz extensions of `A3DiscreteLipschitzExtensionExact`, and the
torus `M` by the fundamental parallelepiped (whose boundary is a null set).
-/

open Filter MeasureTheory Topology Set
open RenewalGeometry.A3FiniteDifferenceConsistency RenewalGeometry.A3PeriodicGraphSampling
open RenewalGeometry.FiniteWeightedGraphHodgeDirac RenewalGeometry.A3PeriodicSmoothEnergy
open RenewalGeometry.A3FlatTorusMetric RenewalGeometry.FiniteConnesDistanceAttainment
open RenewalGeometry.A3ConnesFlatUniformConvergence RenewalGeometry.LipschitzLimitGradientBound
open RenewalGeometry.A3PeriodicConnesSmoothLowerBound RenewalGeometry.A3ConnesDistanceUniformBounds

namespace RenewalGeometry.A3SharpLipschitzLimit

noncomputable section

/-! ### Unit-ball functions are dominated by the Connes distance -/

/-- A commutator-feasible function changes by at most the finite Connes distance. -/
theorem abs_sub_le_connesDistance (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) (x y : Vertex d) :
    |f x - f y| ≤ connesDistance (mass d) (conductance d) x y :=
  le_csSup (isCompact_distanceValues (mass d) (conductance d) x y
    (fun _ => pow_pos (mesh_pos d) _) (conductance_connected d)).bddAbove ⟨f, hf, rfl⟩

/-- The actual supremum error bounds every pair. -/
theorem abs_connesDistance_sub_flatDistance_le (n : ℕ) (x y : Vertex (n + 1)) :
    |connesDistance (mass (n + 1)) (conductance (n + 1)) x y -
      flatDistance (point (n + 1) x) (point (n + 1) y)| ≤ distanceError n := by
  have := norm_le_pi_norm (fun xy : Vertex (n + 1) × Vertex (n + 1) =>
    connesDistance (mass (n + 1)) (conductance (n + 1)) xy.1 xy.2 -
      flatDistance (point (n + 1) xy.1) (point (n + 1) xy.2)) (x, y)
  simpa [distanceError, Real.norm_eq_abs] using this

/-! ### Joint continuity of the flat distance -/

theorem abs_flatDistance_sub_le (x y x' y' : Space) :
    |flatDistance x y - flatDistance x' y'| ≤ ‖x - x'‖ + ‖y - y'‖ := by
  have h1 := PeriodicQuotientDistance.distance_triangle lattice x x' y
  have h2 := PeriodicQuotientDistance.distance_triangle lattice x' y' y
  have h3 := PeriodicQuotientDistance.distance_triangle lattice x' x y'
  have h4 := PeriodicQuotientDistance.distance_triangle lattice x y y'
  have l1 := PeriodicQuotientDistance.distance_le_norm lattice x x'
  have l2 := PeriodicQuotientDistance.distance_le_norm lattice y' y
  have l3 := PeriodicQuotientDistance.distance_le_norm lattice x' x
  have l4 := PeriodicQuotientDistance.distance_le_norm lattice y y'
  rw [norm_sub_rev x' x] at l3
  rw [norm_sub_rev y' y] at l2
  unfold flatDistance
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem tendsto_flatDistance {p p' : ℕ → Space} {z z' : Space} (hp : Tendsto p atTop (𝓝 z))
    (hp' : Tendsto p' atTop (𝓝 z')) :
    Tendsto (fun n => flatDistance (p n) (p' n)) atTop (𝓝 (flatDistance z z')) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun n => ‖p n - z‖ + ‖p' n - z'‖) (fun n => norm_nonneg _)
    (fun n => ?_) ?_
  · rw [Real.norm_eq_abs]
    exact abs_flatDistance_sub_le _ _ _ _
  · have := (tendsto_iff_norm_sub_tendsto_zero.mp hp).add (tendsto_iff_norm_sub_tendsto_zero.mp hp')
    simpa using this

/-! ### Vertex approximation of points of the fundamental parallelepiped -/

/-- Grid index of `t ∈ [0,1]` at resolution `n + 1` (clamped to `n`). -/
def gridIndex (n : ℕ) (t : ℝ) : ℕ := min ⌊((n : ℝ) + 1) * t⌋₊ n

theorem gridIndex_lt (n : ℕ) (t : ℝ) : gridIndex n t < n + 1 :=
  Nat.lt_succ_of_le (min_le_right _ _)

theorem abs_gridIndex_div_sub_le (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |(gridIndex n t : ℝ) / ((n : ℝ) + 1) - t| ≤ 2 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hfl : (⌊((n : ℝ) + 1) * t⌋₊ : ℝ) ≤ ((n : ℝ) + 1) * t := Nat.floor_le (by positivity)
  have hfl' : ((n : ℝ) + 1) * t < ⌊((n : ℝ) + 1) * t⌋₊ + 1 := Nat.lt_floor_add_one _
  have hg1 : (gridIndex n t : ℝ) ≤ ((n : ℝ) + 1) * t :=
    (Nat.cast_le.mpr (min_le_left _ _)).trans hfl
  have hg2 : ((n : ℝ) + 1) * t - 2 ≤ gridIndex n t := by
    unfold gridIndex
    rcases le_or_gt ⌊((n : ℝ) + 1) * t⌋₊ n with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h.le]
      have : ((n : ℝ) + 1) * t ≤ ((n : ℝ) + 1) * 1 := mul_le_mul_of_nonneg_left ht1 hn.le
      linarith
  rw [show (gridIndex n t : ℝ) / ((n : ℝ) + 1) - t =
      ((gridIndex n t : ℝ) - ((n : ℝ) + 1) * t) / ((n : ℝ) + 1) by field_simp]
  rw [abs_div, abs_of_pos hn, div_le_div_iff_of_pos_right hn, abs_le]
  constructor <;> linarith

/-- The mesh vertex approximating `Σ t_i basis_i`. -/
def approxVertex (n : ℕ) (t : Fin 3 → ℝ) : Vertex (n + 1) :=
  fun i => (gridIndex n (t i) : ZMod (n + 1))

theorem point_approxVertex (n : ℕ) (t : Fin 3 → ℝ) :
    point (n + 1) (approxVertex n t) =
      ∑ i, ((gridIndex n (t i) : ℝ) / ((n : ℝ) + 1)) • basis i := by
  unfold point LatticeGridSampling.embed approxVertex
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (gridIndex_lt n (t i))]
  push_cast
  rfl

theorem tendsto_gridIndex_div (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Tendsto (fun n : ℕ => (gridIndex n t : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 t) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun n : ℕ => 2 / ((n : ℝ) + 1)) (fun n => norm_nonneg _)
    (fun n => ?_) ?_
  · rw [Real.norm_eq_abs]
    exact abs_gridIndex_div_sub_le n t ht0 ht1
  · have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    ring

theorem tendsto_point_approxVertex (t : Fin 3 → ℝ) (ht : t ∈ Icc (0 : Fin 3 → ℝ) 1) :
    Tendsto (fun n => point (n + 1) (approxVertex n t)) atTop (𝓝 (∑ i, t i • basis i)) := by
  simp only [point_approxVertex]
  refine tendsto_finsetSum _ fun i _ => ?_
  exact (tendsto_gridIndex_div (t i) (ht.1 i) (ht.2 i)).smul_const _

/-! ### The sharp Lipschitz bound of the limit -/

/-- **`lem:supp-A3-compactness`, sharp constant `1`** (`eq:supp-A3-limit-Lip`).  For anchored
discrete unit-ball sequences on the `A₃` graphs, the Euclidean Lipschitz extensions converge
uniformly on the ball of radius `6` (which contains all mesh vertices and the fundamental
parallelepiped) along a subsequence to the restriction of `F : Space → ℝ`, which is
`1`-Lipschitz for the flat torus distance on the fundamental parallelepiped of the period
lattice, hence `1`-Lipschitz there for the Euclidean distance, with `‖∇F‖ ≤ 1` almost
everywhere on the parallelepiped (Rademacher). -/
theorem a3_limit_sharp_gradient_bound
    (f : (n : ℕ) → Vertex (n + 1) → ℝ)
    (hf : ∀ n, graphLipschitz (mass (n + 1)) (conductance (n + 1)) (f n) ≤ 1)
    (hzero : ∀ n, f n 0 = 0) :
    ∃ G : ℕ → Space → ℝ,
      (∀ n, LipschitzWith 18 (G n)) ∧
      (∀ n x, G n (point (n + 1) x) = f n x) ∧
      ∃ F : Space → ℝ, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ LipschitzWith 18 F ∧
        TendstoUniformly (fun n (x : Metric.closedBall (0 : Space) 6) => G (φ n) x)
          (fun x => F x) atTop ∧
        (∀ z ∈ parallelepiped basis, ∀ z' ∈ parallelepiped basis,
          |F z - F z'| ≤ flatDistance z z') ∧
        LipschitzOnWith 1 F (parallelepiped basis) ∧
        ∀ᵐ x ∂(volume : Measure Space), x ∈ parallelepiped basis →
          DifferentiableAt ℝ F x ∧ ‖fderiv ℝ F x‖ ≤ 1 := by
  obtain ⟨G, hLip, heq, F, φ, hφ, hF, hconv, hae⟩ := a3_limit_ae_gradient_bound f hf hzero 6
  refine ⟨G, hLip, heq, F, φ, hφ, hF, hconv, ?_⟩
  -- one-sided bound on the parallelepiped
  have hkey : ∀ z ∈ parallelepiped basis, ∀ z' ∈ parallelepiped basis,
      F z - F z' ≤ flatDistance z z' := by
    intro z hz z' hz'
    obtain ⟨t, ht, rfl⟩ := (mem_parallelepiped_iff _ _).mp hz
    obtain ⟨t', ht', rfl⟩ := (mem_parallelepiped_iff _ _).mp hz'
    set p : ℕ → Space := fun n => point (φ n + 1) (approxVertex (φ n) t) with hp_def
    set p' : ℕ → Space := fun n => point (φ n + 1) (approxVertex (φ n) t') with hp'_def
    have hp : Tendsto p atTop (𝓝 (∑ i, t i • basis i)) :=
      (tendsto_point_approxVertex t ht).comp hφ.tendsto_atTop
    have hp' : Tendsto p' atTop (𝓝 (∑ i, t' i • basis i)) :=
      (tendsto_point_approxVertex t' ht').comp hφ.tendsto_atTop
    have hzball : (∑ i, t i • basis i) ∈ Metric.closedBall (0 : Space) 6 :=
      Metric.isClosed_closedBall.mem_of_tendsto hp
        (Eventually.of_forall fun n => point_mem_closedBall _ _)
    have hz'ball : (∑ i, t' i • basis i) ∈ Metric.closedBall (0 : Space) 6 :=
      Metric.isClosed_closedBall.mem_of_tendsto hp'
        (Eventually.of_forall fun n => point_mem_closedBall _ _)
    have hFc : ContinuousAt (fun x : Metric.closedBall (0 : Space) 6 => F x) ⟨_, hzball⟩ :=
      (hF.continuous.comp continuous_subtype_val).continuousAt
    have hFc' : ContinuousAt (fun x : Metric.closedBall (0 : Space) 6 => F x) ⟨_, hz'ball⟩ :=
      (hF.continuous.comp continuous_subtype_val).continuousAt
    have hG : Tendsto (fun n => G (φ n) (p n)) atTop (𝓝 (F (∑ i, t i • basis i))) :=
      hconv.tendsto_comp (g := fun n => ⟨p n, point_mem_closedBall _ _⟩) hFc
        (tendsto_subtype_rng.2 hp)
    have hG' : Tendsto (fun n => G (φ n) (p' n)) atTop (𝓝 (F (∑ i, t' i • basis i))) :=
      hconv.tendsto_comp (g := fun n => ⟨p' n, point_mem_closedBall _ _⟩) hFc'
        (tendsto_subtype_rng.2 hp')
    have hbound : ∀ n, G (φ n) (p n) - G (φ n) (p' n) ≤
        flatDistance (p n) (p' n) + distanceError (φ n) := by
      intro n
      simp only [hp_def, hp'_def, heq]
      have h1 := abs_sub_le_connesDistance (φ n + 1) (f (φ n)) (hf (φ n))
        (approxVertex (φ n) t) (approxVertex (φ n) t')
      have h2 := (abs_le.mp (abs_connesDistance_sub_flatDistance_le (φ n)
        (approxVertex (φ n) t) (approxVertex (φ n) t'))).2
      linarith [le_abs_self (f (φ n) (approxVertex (φ n) t) - f (φ n) (approxVertex (φ n) t'))]
    have hrhs : Tendsto (fun n => flatDistance (p n) (p' n) + distanceError (φ n)) atTop
        (𝓝 (flatDistance (∑ i, t i • basis i) (∑ i, t' i • basis i) + 0)) :=
      (tendsto_flatDistance hp hp').add (tendsto_distanceError_zero.comp hφ.tendsto_atTop)
    have := le_of_tendsto_of_tendsto (hG.sub hG') hrhs (Eventually.of_forall hbound)
    simpa using this
  have habs : ∀ z ∈ parallelepiped basis, ∀ z' ∈ parallelepiped basis,
      |F z - F z'| ≤ flatDistance z z' := by
    intro z hz z' hz'
    rw [abs_sub_le_iff]
    refine ⟨hkey z hz z' hz', ?_⟩
    rw [flatDistance, PeriodicQuotientDistance.distance_comm]
    exact hkey z' hz' z hz
  have hLipOn : LipschitzOnWith 1 F (parallelepiped basis) := by
    refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    exact (habs z hz z' hz').trans (PeriodicQuotientDistance.distance_le_norm lattice z z')
  refine ⟨habs, hLipOn, ?_⟩
  have hfront : (volume : Measure Space) (frontier (parallelepiped basis)) = 0 :=
    (convex_parallelepiped (⇑basis)).addHaar_frontier volume
  have hae2 : ∀ᵐ x ∂(volume : Measure Space), x ∉ frontier (parallelepiped basis) :=
    measure_eq_zero_iff_ae_notMem.mp hfront
  filter_upwards [hae, hae2] with x hx hx2 hxP
  refine ⟨hx.1, ?_⟩
  have hint : x ∈ interior (parallelepiped basis) := by
    by_contra h
    exact hx2 ⟨subset_closure hxP, h⟩
  have := hx.1.hasFDerivAt.le_of_lipschitzOn (mem_interior_iff_mem_nhds.mp hint) hLipOn
  simpa using this

end

end RenewalGeometry.A3SharpLipschitzLimit
