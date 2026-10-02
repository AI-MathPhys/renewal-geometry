/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Continuum.A3SharpLipschitzLimitExact
import RenewalGeometry.DiscreteAnalysis.A3KuhnInterpolationExact
import RenewalGeometry.Continuum.UniformLipschitzSubsequenceCompactnessExact

/-!
# Compactness of the piecewise-affine interpolants of discrete `A₃` unit-ball functions

Paper `predictive_spectral_geometry`, label `lem:supp-A3-compactness`.

Let `h_n = 1/(m_n + 1) → 0` and `f_n : V_{h_n} → ℝ` with `L_{h_n}(f_n) ≤ 1`, each vanishing at
some vertex.  The Kuhn interpolants `I_{h_n} f_n` of `lem:A3-periodic-triangulation`
(`A3KuhnInterpolation.interp`) are periodic and uniformly `√24`-Lipschitz, hence (Arzelà–Ascoli
on a ball containing a fundamental domain, then periodicity) a subsequence converges uniformly
on all of `Space` to a periodic `F` (`a3_interpolant_compactness`).  The sharp bound uses the
finite Connes distance: `|f_n x - f_n y| ≤ d_n(x, y)` and the uniform convergence `d_n → d_g`
(`A3ConnesFlatUniformConvergence.tendsto_distanceError_zero`) give
`|F z - F z'| ≤ d_g(z, z') ≤ ‖z - z'‖`.  Hence `F` is `1`-Lipschitz, so it lies in
`W^{1,∞}(M)` (a periodic Lipschitz function), is differentiable almost everywhere (Rademacher)
and `|∇F| ≤ 1` (`eq:supp-A3-limit-Lip`).

The convergence `x_{0,n} → x₀` of the anchors assumed in the paper is not needed: one zero of
each `f_n` suffices.
-/

open Filter MeasureTheory Topology Set
open scoped NNReal Matrix.Norms.L2Operator

namespace RenewalGeometry.A3KuhnInterpolantCompactness

open A3FiniteDifferenceConsistency A3PeriodicGraphSampling FiniteWeightedGraphHodgeDirac
open A3PeriodicSmoothEnergy A3FlatTorusMetric A3ConnesFlatUniformConvergence
open A3ConnesDistanceUniformBounds A3SharpLipschitzLimit A3KuhnInterpolation
open LatticePeriodicDifferentiation UniformLipschitzSubsequenceCompactness

noncomputable section

/-- Every point is a parallelepiped point plus a period. -/
theorem exists_parallelepiped_add_lattice (z : Space) :
    ∃ w ∈ parallelepiped basis, ∃ q : lattice, z = w + q := by
  let t : Fin 3 → ℝ := fun i => Int.fract (coordinates z i)
  refine ⟨∑ i, t i • basis i, (mem_parallelepiped_iff _ _).mpr ⟨t, ⟨fun i => Int.fract_nonneg _,
    fun i => (Int.fract_lt_one _).le⟩, rfl⟩,
    ⟨integerCombination basis (fun i => ⌊coordinates z i⌋), ⟨_, rfl⟩⟩, ?_⟩
  apply coordinates.injective
  funext i
  simp only [map_add, Pi.add_apply, coordinates_integerCombination]
  have h : coordinates (∑ j, t j • basis j) i = t i := by
    change basis.repr (∑ j, t j • basis j) i = t i
    rw [basis.repr_sum_self]
  rw [h]
  exact (Int.fract_add_floor (coordinates z i)).symm

theorem flatDistance_add_lattice (w w' : Space) (q q' : lattice) :
    flatDistance (w + q) (w' + q') = flatDistance w w' := by
  unfold flatDistance
  rw [PeriodicQuotientDistance.distance_periodic_right, PeriodicQuotientDistance.distance_comm,
    PeriodicQuotientDistance.distance_periodic_right, PeriodicQuotientDistance.distance_comm]

theorem lipschitzWith_interp_of_le_one (d : ℕ) [NeZero d] (f : Vertex d → ℝ)
    (hf : graphLipschitz (mass d) (conductance d) f ≤ 1) :
    LipschitzWith ⟨Real.sqrt 24, Real.sqrt_nonneg _⟩ (interp d f) := by
  apply LipschitzWith.of_dist_le_mul
  intro q p
  rw [Real.dist_eq, dist_eq_norm]
  refine (abs_interp_sub_le d f p q).trans ?_
  have := graphLipschitz_nonneg d f
  change _ ≤ Real.sqrt 24 * ‖q - p‖
  have h24 := Real.sqrt_nonneg 24
  have hn := norm_nonneg (q - p)
  nlinarith [mul_le_mul_of_nonneg_left hf (mul_nonneg h24 hn)]

/-- **`lem:supp-A3-compactness`.**  For mesh sizes `h_n = 1/(m_n + 1) → 0` and discrete
unit-ball functions `f_n` (`L_{h_n}(f_n) ≤ 1`) each vanishing at some vertex, a subsequence of the
piecewise-affine interpolants `I_{h_n} f_n` converges uniformly on `Space` to a lattice-periodic
`F` (a function on `M`) with `|F z - F z'| ≤ d_g(z, z')`; in particular `F` is `1`-Lipschitz
(so `F ∈ W^{1,∞}(M)`), `‖∇F‖ ≤ 1` at every point, and `F` is differentiable with `‖∇F‖ ≤ 1`
almost everywhere (`eq:supp-A3-limit-Lip`). -/
theorem a3_interpolant_compactness
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (f : (n : ℕ) → Vertex (m n + 1) → ℝ)
    (hf : ∀ n, graphLipschitz (mass (m n + 1)) (conductance (m n + 1)) (f n) ≤ 1)
    (hanchor : ∀ n, ∃ x, f n x = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : Space → ℝ,
      TendstoUniformly (fun n => interp (m (φ n) + 1) (f (φ n))) F atTop ∧
      (∀ (q : lattice) (p : Space), F (p + q) = F p) ∧
      (∀ z z', |F z - F z'| ≤ flatDistance z z') ∧
      LipschitzWith 1 F ∧
      (∀ p, ‖fderiv ℝ F p‖ ≤ 1) ∧
      ∀ᵐ p ∂(volume : Measure Space), DifferentiableAt ℝ F p ∧ ‖fderiv ℝ F p‖ ≤ 1 := by
  set Fn : ℕ → Space → ℝ := fun n => interp (m n + 1) (f n) with hFn
  have hLip : ∀ n, LipschitzWith ⟨Real.sqrt 24, Real.sqrt_nonneg _⟩ (Fn n) :=
    fun n => lipschitzWith_interp_of_le_one _ _ (hf n)
  have hper : ∀ n (q : lattice) (p : Space), Fn n (p + q) = Fn n p :=
    fun n q p => interp_periodic _ _ q p
  choose x hx using hanchor
  have hFx : ∀ n, Fn n (point (m n + 1) (x n)) = 0 := fun n => by
    simp only [hFn]; rw [interp_point, hx n]
  -- Arzelà–Ascoli on the ball of radius 6
  have hbound : ∀ n (y : Metric.closedBall (0 : Space) 6), |Fn n y| ≤ Real.sqrt 24 * 12 := by
    intro n y
    have h1 := (hLip n).dist_le_mul (y : Space) (point (m n + 1) (x n))
    rw [hFx n, Real.dist_eq, sub_zero, dist_eq_norm] at h1
    have hy : ‖(y : Space)‖ ≤ 6 := by
      have := y.property
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hp : ‖point (m n + 1) (x n)‖ ≤ 6 := by
      simpa using point_mem_closedBall (m n + 1) (x n)
    have : ‖(y : Space) - point (m n + 1) (x n)‖ ≤ 12 :=
      (norm_sub_le _ _).trans (by linarith)
    refine h1.trans ?_
    change Real.sqrt 24 * _ ≤ _
    exact mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
  have hLipX : ∀ n, LipschitzWith ⟨Real.sqrt 24, Real.sqrt_nonneg _⟩
      (fun y : Metric.closedBall (0 : Space) 6 => Fn n y) := fun n => by
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [Subtype.dist_eq]
    exact (hLip n).dist_le_mul y y'
  obtain ⟨g, φ, hφ, -, -, hconv⟩ := exists_uniformly_convergent_subsequence
    (fun n (y : Metric.closedBall (0 : Space) 6) => Fn n y) _ _ hLipX hbound
  -- reduction modulo the lattice
  have hcover : ∀ p : Space, ∃ q : lattice, ‖p - q‖ ≤ 6 := by
    intro p
    obtain ⟨q, hq⟩ := periodLattice_bounded_cover basis p
    refine ⟨q, hq.trans ?_⟩
    calc
      _ ≤ ∑ _i : Fin 3, (2 : ℝ) := Finset.sum_le_sum (fun i _ => by
        rw [basis_eq_selected_root]; exact A3UniformEnergyConsistency.root_norm_le_two _)
      _ = 6 := by norm_num
  choose qr hqr using hcover
  let red : Space → Metric.closedBall (0 : Space) 6 := fun p =>
    ⟨p - qr p, by rw [Metric.mem_closedBall, dist_zero_right]; exact hqr p⟩
  let F : Space → ℝ := fun p => g (red p)
  have hred : ∀ n p, Fn n p = Fn n (red p) := by
    intro n p
    have := hper n (qr p) (p - qr p)
    rw [sub_add_cancel] at this
    exact this
  have hT : TendstoUniformly (fun n => Fn (φ n)) F atTop := by
    rw [Metric.tendstoUniformly_iff] at hconv ⊢
    intro ε hε
    filter_upwards [hconv ε hε] with n hn p
    rw [hred (φ n) p]
    exact hn (red p)
  have hcont : Continuous F :=
    hT.continuous (Eventually.of_forall fun n => (hLip (φ n)).continuous).frequently
  have hFper : ∀ (q : lattice) (p : Space), F (p + q) = F p := by
    intro q p
    have h1 := hT.tendsto_at (p + q)
    have h2 := hT.tendsto_at p
    simp only [hper] at h1
    exact tendsto_nhds_unique h1 h2
  have hmφ : Tendsto (fun n => m (φ n)) atTop atTop := hm.comp hφ.tendsto_atTop
  -- one-sided flat bound on the parallelepiped
  have hkey : ∀ w ∈ parallelepiped basis, ∀ w' ∈ parallelepiped basis,
      F w - F w' ≤ flatDistance w w' := by
    intro w hw w' hw'
    obtain ⟨t, ht, rfl⟩ := (mem_parallelepiped_iff _ _).mp hw
    obtain ⟨t', ht', rfl⟩ := (mem_parallelepiped_iff _ _).mp hw'
    set p : ℕ → Space := fun n => point (m (φ n) + 1) (approxVertex (m (φ n)) t) with hp_def
    set p' : ℕ → Space := fun n => point (m (φ n) + 1) (approxVertex (m (φ n)) t') with hp'_def
    have hp : Tendsto p atTop (𝓝 (∑ i, t i • basis i)) :=
      (tendsto_point_approxVertex t ht).comp hmφ
    have hp' : Tendsto p' atTop (𝓝 (∑ i, t' i • basis i)) :=
      (tendsto_point_approxVertex t' ht').comp hmφ
    have hG : Tendsto (fun n => Fn (φ n) (p n)) atTop (𝓝 (F (∑ i, t i • basis i))) :=
      hT.tendsto_comp hcont.continuousAt hp
    have hG' : Tendsto (fun n => Fn (φ n) (p' n)) atTop (𝓝 (F (∑ i, t' i • basis i))) :=
      hT.tendsto_comp hcont.continuousAt hp'
    have hbd : ∀ n, Fn (φ n) (p n) - Fn (φ n) (p' n) ≤
        flatDistance (p n) (p' n) + distanceError (m (φ n)) := by
      intro n
      simp only [hp_def, hp'_def, hFn, interp_point]
      have h1 := abs_sub_le_connesDistance (m (φ n) + 1) (f (φ n)) (hf (φ n))
        (approxVertex (m (φ n)) t) (approxVertex (m (φ n)) t')
      have h2 := (abs_le.mp (abs_connesDistance_sub_flatDistance_le (m (φ n))
        (approxVertex (m (φ n)) t) (approxVertex (m (φ n)) t'))).2
      linarith [le_abs_self (f (φ n) (approxVertex (m (φ n)) t) -
        f (φ n) (approxVertex (m (φ n)) t'))]
    have hrhs : Tendsto (fun n => flatDistance (p n) (p' n) + distanceError (m (φ n))) atTop
        (𝓝 (flatDistance (∑ i, t i • basis i) (∑ i, t' i • basis i) + 0)) :=
      (tendsto_flatDistance hp hp').add (tendsto_distanceError_zero.comp hmφ)
    have := le_of_tendsto_of_tendsto (hG.sub hG') hrhs (Eventually.of_forall hbd)
    simpa using this
  have hflat : ∀ z z', |F z - F z'| ≤ flatDistance z z' := by
    have hone : ∀ z z', F z - F z' ≤ flatDistance z z' := by
      intro z z'
      obtain ⟨w, hw, q, rfl⟩ := exists_parallelepiped_add_lattice z
      obtain ⟨w', hw', q', rfl⟩ := exists_parallelepiped_add_lattice z'
      rw [hFper, hFper, flatDistance_add_lattice]
      exact hkey w hw w' hw'
    intro z z'
    rw [abs_sub_le_iff]
    refine ⟨hone z z', ?_⟩
    rw [flatDistance, PeriodicQuotientDistance.distance_comm]
    exact hone z' z
  have hLip1 : LipschitzWith 1 F := by
    refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    exact (hflat z z').trans (PeriodicQuotientDistance.distance_le_norm lattice z z')
  have hderiv : ∀ p, ‖fderiv ℝ F p‖ ≤ 1 := fun p => by
    simpa using norm_fderiv_le_of_lipschitz ℝ hLip1 (x₀ := p)
  refine ⟨φ, hφ, F, hT, hFper, hflat, hLip1, hderiv, ?_⟩
  filter_upwards [hLip1.ae_differentiableAt (μ := (volume : Measure Space))] with p hp
  exact ⟨hp, hderiv p⟩

/-- Non-vacuity: the hypotheses of `a3_interpolant_compactness` are satisfied by the zero
functions on the full mesh sequence. -/
example : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : Space → ℝ,
    TendstoUniformly (fun n => interp (id (φ n) + 1) (fun _ : Vertex (id (φ n) + 1) => (0 : ℝ)))
      F atTop ∧
      (∀ (q : lattice) (p : Space), F (p + q) = F p) ∧
      (∀ z z', |F z - F z'| ≤ flatDistance z z') ∧ LipschitzWith 1 F ∧
      (∀ p, ‖fderiv ℝ F p‖ ≤ 1) ∧
      ∀ᵐ p ∂(volume : Measure Space), DifferentiableAt ℝ F p ∧ ‖fderiv ℝ F p‖ ≤ 1 :=
  a3_interpolant_compactness id tendsto_id (fun n _ => 0) (fun n => by
    have h := graphLipschitz_smul (mass (id n + 1)) (conductance (id n + 1)) 0
      (fun _ : Vertex (id n + 1) => (0 : ℝ))
    simp only [zero_smul, abs_zero, zero_mul] at h
    show graphLipschitz (mass (id n + 1)) (conductance (id n + 1)) (0 : Vertex (id n + 1) → ℝ) ≤ 1
    rw [h]; norm_num) (fun n => ⟨0, rfl⟩)

end

end RenewalGeometry.A3KuhnInterpolantCompactness
