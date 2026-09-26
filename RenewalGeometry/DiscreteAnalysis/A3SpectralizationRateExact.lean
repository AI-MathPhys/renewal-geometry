/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.A3PeriodicGraphSamplingExact

/-!
# Exact finite `A₃` spectralization: the `O(h)` Lipschitz rate and the generator limit

The two analytic clauses of `thm:supp-A3-finite` of the predictive spectral geometry paper,
on the actual finite periodic `A₃` graph of `A3PeriodicGraphSamplingExact`
(vertices `V_h = hΛ/Λ`, mesh `h = 1/d`, rates `k = 1/(8h²)`, masses `h³`).

* `rootDifference_error_le`: the first-order Taylor remainder along a root,
  `|(F(x+hα) − F(x))/h − α·∇F(x)| ≤ ‖α‖² Lip(∇F) h = 2 Lip(∇F) h`;
* `exists_vertex_near`: every point of the torus is within `h ∑_i ‖b_i‖` of a mesh vertex after
  a lattice translation (`b` the period basis);
* `graphLipschitz_rate` — **`eq:supp-A3-Lip-convergence`**: for a lattice-periodic `C¹` field
  `F` whose gradient is `M₂`-Lipschitz (`M₂ ≤ ‖F‖_{C²}`),
  `|L_h(F|_{V_h}) − ‖∇F‖_{L^∞(M)}| ≤ (4 + ∑_i ‖b_i‖) M₂ h`, with `L_h` the graph Lipschitz
  seminorm of `eq:supp-A3-Lip` and `‖∇F‖_{L^∞(M)} = sup_y ‖∇F(y)‖`;
* `generator`: the generator `(𝓛_h F)(x) = (1/(8h²)) ∑_α (F(x+hα) − F(x))` of
  `eq:supp-A3-square`; `generator_sample_eq`: at the vertices it is the finite-graph generator
  applied to the sample `F|_{V_h}` (root steps reduced modulo the period);
* `second_order_remainder`: the uniform second-order Taylor remainder for a `C²` field with
  uniformly continuous Hessian; `sum_root_bilinear`: the polarized tight-frame identity
  `∑_α B(α, α) = 8 ∑_i B(e_i, e_i)` (`lem:supp-A3-frame`);
* `tendstoUniformly_generator` — **the generator limit** `𝓛_h F → ½ ΔF` uniformly on the torus
  for every lattice-periodic `C²` field `F` (the paper asks `F ∈ C⁴(M)`; only `C²` is used,
  the Hessian being uniformly continuous by periodicity).

Renderings.  The paper's `C²` norm enters the rate only through the Lipschitz constant of `∇F`,
so the theorem is stated with that constant (`‖D²F‖_∞ ≤ ‖F‖_{C²}` dominates it); the explicit
constant is `C_{A₃} = 4 + ∑_i ‖b_i‖ = 4 + 3√2`.  The generator clause is proved as uniform
convergence (no rate), exactly as stated in the theorem.
-/

open Filter Set
open scoped BigOperators Topology Matrix.Norms.L2Operator

namespace RenewalGeometry.A3SpectralizationRate

open A3FiniteDifferenceConsistency A3UniformEnergyConsistency A3PeriodicSmoothEnergy
  LatticePeriodicDifferentiation LatticeGridSampling A3PeriodicGraphSampling
  FiniteWeightedGraphHodgeDirac

noncomputable section

/-! ### First-order Taylor remainder with a Lipschitz gradient -/

/-- `|(F(x+hα) − F(x))/h − α·∇F(x)| ≤ M₂ h ‖α‖² = 2 M₂ h` when `∇F` is `M₂`-Lipschitz. -/
theorem rootDifference_error_le (f : Space → ℝ) (v : Space → Space)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (v x)) x) (M₂ : ℝ) (hM : 0 ≤ M₂)
    (hlip : ∀ x y, ‖v y - v x‖ ≤ M₂ * ‖y - x‖) (x : Space) (h : ℝ) (hh : 0 < h) (r : Fin 12) :
    |rootDifference f x h r - inner ℝ (v x) (root r)| ≤ 2 * M₂ * h := by
  set α := root r with hα
  have hρ : 0 ≤ h * ‖α‖ := by positivity
  have key : ‖f (x + h • α) - f x - (innerSL ℝ (v x)) ((x + h • α) - x)‖ ≤
      (M₂ * (h * ‖α‖)) * ‖(x + h • α) - x‖ := by
    refine (convex_closedBall x (h * ‖α‖)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f' := fun z => innerSL ℝ (v z)) (φ := innerSL ℝ (v x))
      (fun z _ => (hf z).hasFDerivWithinAt) (fun z hz => ?_)
      (Metric.mem_closedBall_self hρ) ?_
    · rw [← map_sub, innerSL_apply_norm]
      refine (hlip x z).trans (mul_le_mul_of_nonneg_left ?_ hM)
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hz
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hh]
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs h, abs_of_pos hh, map_smul,
    innerSL_apply_apply, smul_eq_mul, Real.norm_eq_abs] at key
  have hnorm2 : ‖α‖ ^ 2 = 2 := root_norm_sq r
  have hid : rootDifference f x h r - inner ℝ (v x) α =
      (f (x + h • α) - f x - h * inner ℝ (v x) α) / h := by
    unfold rootDifference
    rw [← hα]
    field_simp
  rw [hid, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  calc |f (x + h • α) - f x - h * inner ℝ (v x) α|
      ≤ M₂ * (h * ‖α‖) * (h * ‖α‖) := key
    _ = M₂ * h ^ 2 * ‖α‖ ^ 2 := by ring
    _ = 2 * M₂ * h * h := by rw [hnorm2]; ring

/-- Pointwise error of the square-root sampled energy. -/
theorem sqrt_sampledEnergy_error_le (f : Space → ℝ) (v : Space → Space)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (v x)) x) (M₂ : ℝ) (hM : 0 ≤ M₂)
    (hlip : ∀ x y, ‖v y - v x‖ ≤ M₂ * ‖y - x‖) (x : Space) (h : ℝ) (hh : 0 < h) :
    |Real.sqrt (sampledEnergy f x h) - ‖v x‖| ≤ 4 * M₂ * h := by
  have := sqrt_energy_error_le f x (v x) h (2 * M₂ * h) (by positivity)
    (fun r => rootDifference_error_le f v hf M₂ hM hlip x h hh r)
  linarith

/-! ### The mesh covers the torus -/

theorem point_eq_sum (d : ℕ) (x : Vertex d) :
    point d x = ∑ i, (((x i).val : ℝ) / (d : ℝ)) • basis i := rfl

theorem integerCombination_eq_sum (z : Fin 3 → ℤ) :
    integerCombination basis z = ∑ i, (z i : ℝ) • basis i := rfl

/-- Every point is, after a lattice translation, within `h ∑_i ‖b_i‖` of a mesh vertex. -/
theorem exists_vertex_near (d : ℕ) [NeZero d] (y : Space) :
    ∃ (x : Vertex d) (p : lattice), ‖(y - p) - point d x‖ ≤ mesh d * ∑ i, ‖basis i‖ := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set c : Fin 3 → ℝ := fun i => basis.repr y i with hc
  set k : Fin 3 → ℤ := fun i => ⌊c i * d⌋ with hk
  set q : Fin 3 → ℤ := fun i => k i / (d : ℤ) with hq
  refine ⟨fun i => (k i : ZMod d), ⟨integerCombination basis q, ⟨q, rfl⟩⟩, ?_⟩
  have hval : ∀ i, ((((k i : ZMod d)).val : ℕ) : ℝ) = (k i : ℝ) - (d : ℝ) * (q i : ℝ) := by
    intro i
    have h1 : (((k i : ZMod d)).val : ℤ) = k i % (d : ℤ) := ZMod.val_intCast (k i)
    have h2 : (((k i : ZMod d)).val : ℝ) = ((k i % (d : ℤ) : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h2, Int.emod_def]
    push_cast
    rfl
  have hy : y = ∑ i, c i • basis i := (basis.sum_repr y).symm
  have hdecomp : (y - integerCombination basis q) - point d (fun i => (k i : ZMod d)) =
      ∑ i, (c i - (k i : ℝ) / d) • basis i := by
    rw [point_eq_sum, integerCombination_eq_sum]
    conv_lhs => rw [hy]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, ← sub_smul, hval i]
    congr 1
    field_simp
    ring
  rw [hdecomp]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hfl : (k i : ℝ) ≤ c i * d := Int.floor_le _
  have hfl' : c i * d < (k i : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor
  · rw [mesh]
    have : (k i : ℝ) / d ≤ c i := by rw [div_le_iff₀ hd]; exact hfl
    have : 0 < 1 / (d : ℝ) := by positivity
    linarith
  · rw [mesh, sub_le_iff_le_add, ← add_div, le_div_iff₀ hd]
    linarith

/-- The gradient of a lattice-periodic field is lattice-periodic. -/
theorem gradient_periodic (f : Space → ℝ) (v : Space → Space)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (v x)) x)
    (hperiod : ∀ p : lattice, ∀ y : Space, f (y + p) = f y) (p : lattice) (y : Space) :
    v (y + p) = v y := by
  have h := derivative_periodic lattice f (fun x => innerSL ℝ (v x)) hf hperiod p y
  have h2 : ‖v (y + p) - v y‖ = 0 := by
    rw [← innerSL_apply_norm ℝ, map_sub, h, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h2)

/-! ### The `O(h)` rate for the graph Lipschitz seminorm -/

/-- **`eq:supp-A3-Lip-convergence`.**  For a lattice-periodic `C¹` field with `M₂`-Lipschitz
gradient, `|L_h(F|_{V_h}) − ‖∇F‖_{L^∞(M)}| ≤ (4 + ∑_i ‖b_i‖) M₂ h`. -/
theorem graphLipschitz_rate (f : Space → ℝ) (v : Space → Space)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (v x)) x)
    (hperiod : ∀ p : lattice, ∀ y : Space, f (y + p) = f y)
    (M₂ : ℝ) (hM : 0 ≤ M₂) (hlip : ∀ x y, ‖v y - v x‖ ≤ M₂ * ‖y - x‖)
    (d : ℕ) [NeZero d] :
    |graphLipschitz (mass d) (conductance d) (fun y => f (point d y)) -
        sSup (Set.range fun y => ‖v y‖)| ≤ (4 + ∑ i, ‖basis i‖) * M₂ * mesh d := by
  set h := mesh d with hh_def
  have hh : 0 < h := mesh_pos d
  set ρ := ∑ i, ‖basis i‖ with hρ
  have hρ0 : 0 ≤ ρ := Finset.sum_nonneg fun i _ => norm_nonneg _
  set A := graphLipschitz (mass d) (conductance d) (fun y => f (point d y)) with hA
  have hA0 : 0 ≤ A := by rw [hA]; unfold graphLipschitz; exact norm_nonneg _
  set E : Vertex d → ℝ := fun x => sampledEnergy f (point d x) h with hE
  have hA2 : A ^ 2 = ‖E‖ := graphLipschitz_sample_sq_eq d f hperiod
  have hE0 : ∀ x, 0 ≤ E x := fun x => sampledEnergy_nonneg _ _ _
  have hEle : ∀ x, E x ≤ A ^ 2 := by
    intro x
    rw [hA2]
    have := norm_le_pi_norm (G := fun _ : Vertex d => ℝ) E x
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hsqrt_le : ∀ x, Real.sqrt (E x) ≤ A := fun x =>
    (Real.sqrt_le_left hA0).mpr (hEle x)
  have herr : ∀ x : Vertex d, |Real.sqrt (E x) - ‖v (point d x)‖| ≤ 4 * M₂ * h :=
    fun x => sqrt_sampledEnergy_error_le f v hf M₂ hM hlip (point d x) h hh
  -- every gradient value is controlled by the mesh
  have hup : ∀ y : Space, ‖v y‖ ≤ A + (4 + ρ) * M₂ * h := by
    intro y
    obtain ⟨x, p, hxp⟩ := exists_vertex_near d y
    have hper : v y = v (y - p) := by
      have := gradient_periodic f v hf hperiod p (y - p)
      rw [sub_add_cancel] at this
      exact this
    have h1 : ‖v (y - p)‖ ≤ ‖v (point d x)‖ + M₂ * (ρ * h) := by
      have := hlip (point d x) (y - p)
      have h2 := norm_le_norm_add_norm_sub' (v (y - p)) (v (point d x))
      have h3 : M₂ * ‖y - p - point d x‖ ≤ M₂ * (ρ * h) := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        rw [mul_comm]; exact hxp
      linarith
    have h4 : ‖v (point d x)‖ ≤ Real.sqrt (E x) + 4 * M₂ * h := by
      have := (abs_le.mp (herr x)).1
      linarith
    rw [hper]
    have := hsqrt_le x
    nlinarith
  have hbdd : BddAbove (Set.range fun y => ‖v y‖) := ⟨_, by rintro _ ⟨y, rfl⟩; exact hup y⟩
  have hne : (Set.range fun y => ‖v y‖).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  set G := sSup (Set.range fun y => ‖v y‖) with hG
  have hG_le : G ≤ A + (4 + ρ) * M₂ * h := csSup_le hne (by rintro _ ⟨y, rfl⟩; exact hup y)
  have hG_ge : ∀ y, ‖v y‖ ≤ G := fun y => le_csSup hbdd ⟨y, rfl⟩
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG_ge 0)
  have hA_le : A ≤ G + 4 * M₂ * h := by
    have hpos : 0 ≤ G + 4 * M₂ * h := by positivity
    rw [← sq_le_sq₀ hA0 hpos, hA2]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hE0 x)]
    have h1 : Real.sqrt (E x) ≤ G + 4 * M₂ * h := by
      have := (abs_le.mp (herr x)).2
      linarith [hG_ge (point d x)]
    have h2 : E x = Real.sqrt (E x) ^ 2 := (Real.sq_sqrt (hE0 x)).symm
    rw [h2]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hρM : 0 ≤ ρ * M₂ * h := by positivity
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-! ### The generator `𝓛_h` -/

/-- The finite-difference generator `(𝓛_h F)(x) = (1/(8h²)) ∑_α (F(x+hα) − F(x))` of
`eq:supp-A3-square`. -/
def generator (f : Space → ℝ) (x : Space) (h : ℝ) : ℝ :=
  (∑ r, (f (x + h • root r) - f x)) / (8 * h ^ 2)

/-- At the mesh vertices the generator is the finite-graph generator applied to the sample:
root steps are reduced modulo the period. -/
theorem generator_sample_eq (d : ℕ) [NeZero d] (f : Space → ℝ)
    (hperiod : ∀ p : lattice, ∀ y : Space, f (y + p) = f y) (x : Vertex d) :
    generator f (point d x) (mesh d) =
      (∑ r, (f (point d (rootStep d x r)) - f (point d x))) / (8 * mesh d ^ 2) := by
  unfold generator
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sample_rootStep_eq_translate d x r f hperiod]

/-- The Euclidean Laplacian `ΔF = ∑_i D²F(e_i, e_i)` from the Hessian. -/
def laplacian (d2f : Space → Space →L[ℝ] Space →L[ℝ] ℝ) (x : Space) : ℝ :=
  ∑ i, d2f x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

/-! #### The polarized tight-frame identity -/

theorem root_apply (r : Fin 12) (i : Fin 3) : root r i = a3Roots r i := rfl

theorem sum_root : ∑ r, root r = 0 := by
  ext i
  fin_cases i <;> simp [root, a3Roots, Fin.sum_univ_succ]

theorem sum_root_mul (i j : Fin 3) :
    ∑ r, root r i * root r j = if i = j then 8 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [root, a3Roots, Fin.sum_univ_succ]

theorem eq_sum_single (w : Space) :
    w = ∑ i, w i • (EuclideanSpace.single i (1 : ℝ) : Space) := by
  have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  simp only [EuclideanSpace.basisFun_apply] at this
  exact this.symm

theorem bilinear_expand (B : Space →L[ℝ] Space →L[ℝ] ℝ) (w : Space) :
    B w w = ∑ i, ∑ j, w i * w j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hw := eq_sum_single w
  calc B w w = B (∑ i, w i • (EuclideanSpace.single i (1 : ℝ) : Space))
        (∑ j, w j • (EuclideanSpace.single j (1 : ℝ) : Space)) := by rw [← hw]
    _ = ∑ i, ∑ j, w i * w j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
      rw [map_sum B, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_smul, ContinuousLinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

/-- **`lem:supp-A3-frame`, polarized**: `∑_α B(α, α) = 8 ∑_i B(e_i, e_i)` for every bilinear
form `B`. -/
theorem sum_root_bilinear (B : Space →L[ℝ] Space →L[ℝ] ℝ) :
    ∑ r, B (root r) (root r) =
      8 * ∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  calc ∑ r, B (root r) (root r)
      = ∑ r, ∑ i, ∑ j, root r i * root r j *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
        Finset.sum_congr rfl fun r _ => bilinear_expand B (root r)
    _ = ∑ i, ∑ r, ∑ j, root r i * root r j *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ r, root r i * root r j *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ j, (∑ r, root r i * root r j) *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
        simp_rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, (if i = j then (8 : ℝ) else 0) *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
        simp_rw [sum_root_mul]
    _ = 8 * ∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
        simp [ite_mul, Finset.sum_ite_eq, Finset.mul_sum]

/-! #### The uniform second-order remainder -/

/-- Uniform second-order Taylor remainder: if the Hessian varies by less than `ε` on balls of
radius `δ`, then `|F(x+u) − F(x) − DF(x)u − ½ D²F(x)(u,u)| ≤ ε ‖u‖²` for `‖u‖ ≤ δ`. -/
theorem second_order_remainder (f : Space → ℝ) (df : Space → Space →L[ℝ] ℝ)
    (d2f : Space → Space →L[ℝ] Space →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : ∀ x, HasFDerivAt df (d2f x) x)
    (ε δ : ℝ) (hmod : ∀ a b : Space, dist a b ≤ δ → ‖d2f a - d2f b‖ ≤ ε)
    (x u : Space) (hu : ‖u‖ ≤ δ) :
    |f (x + u) - f x - df x u - (1 / 2) * d2f x u u| ≤ ε * ‖u‖ ^ 2 := by
  have hε : 0 ≤ ε := (norm_nonneg (d2f x - d2f x)).trans
    (hmod x x (by rw [dist_self]; exact (norm_nonneg u).trans hu))
  -- the line `t ↦ x + t • u`
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • u) u t := by
    intro t
    have := ((hasDerivAt_id t).smul_const u).const_add x
    simpa using this
  -- first derivative along the line
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (x + s • u)) (df (x + t • u) u) t := by
    intro t
    exact (hf (x + t • u)).comp_hasDerivAt t (hline t)
  -- second derivative along the line
  have hχ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => df (x + s • u) u) (d2f (x + t • u) u u) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => df (x + s • u)) (d2f (x + t • u) u) t :=
      (hdf (x + t • u)).comp_hasDerivAt t (hline t)
    have h2 := h1.clm_apply (hasDerivAt_const t u)
    simpa using h2
  -- bound on the Hessian variation along the segment
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖d2f (x + t • u) u u - d2f x u u‖ ≤ ε * ‖u‖ ^ 2 := by
    intro t ht
    have hdist : dist (x + t • u) x ≤ δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖u‖ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ = ‖u‖ := one_mul _
        _ ≤ δ := hu
    have h1 : d2f (x + t • u) u u - d2f x u u = (d2f (x + t • u) - d2f x) u u := by
      simp
    rw [h1]
    calc ‖(d2f (x + t • u) - d2f x) u u‖
        ≤ ‖(d2f (x + t • u) - d2f x) u‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖d2f (x + t • u) - d2f x‖ * ‖u‖ * ‖u‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ε * ‖u‖ * ‖u‖ := by
          gcongr
          exact hmod _ _ hdist
      _ = ε * ‖u‖ ^ 2 := by ring
  -- first mean value: `χ t := df(x+tu)u − t · D²F(x)(u,u)` is `ε‖u‖²`-Lipschitz on `[0,1]`
  have hχ' : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => df (x + s • u) u - s * d2f x u u)
        (d2f (x + t • u) u u - d2f x u u) (Icc 0 1) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => df (x + s • u) u - s * d2f x u u)
        (d2f (x + t • u) u u - d2f x u u) t :=
      ((hχ t).sub ((hasDerivAt_id t).mul_const (d2f x u u))).congr_deriv (by simp)
    exact h1.hasDerivWithinAt
  have hψ'bound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖df (x + t • u) u - df x u - t * d2f x u u‖ ≤ ε * ‖u‖ ^ 2 := by
    intro t ht
    have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hχ' hbound
      (left_mem_Icc.mpr zero_le_one) ht
    simp only [zero_smul, add_zero, zero_mul, sub_zero, Real.norm_eq_abs] at hmv
    have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    have hC : 0 ≤ ε * ‖u‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs]
    calc |df (x + t • u) u - df x u - t * d2f x u u|
        = |df (x + t • u) u - t * d2f x u u - df x u| := by congr 1; ring
      _ ≤ ε * ‖u‖ ^ 2 * |t| := hmv
      _ ≤ ε * ‖u‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left ht1 hC
      _ = ε * ‖u‖ ^ 2 := mul_one _
  -- second mean value: `ψ t := F(x+tu) − t DF(x)u − (t²/2) D²F(x)(u,u)`
  have hψ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => f (x + s • u) - s * df x u - (s ^ 2 / 2) * d2f x u u)
        (df (x + t • u) u - df x u - t * d2f x u u) (Icc 0 1) t := by
    intro t _
    have h1 : HasDerivAt
        (fun s : ℝ => f (x + s • u) - s * df x u - (s ^ 2 / 2) * d2f x u u)
        (df (x + t • u) u - df x u - t * d2f x u u) t :=
      (((hφ t).sub ((hasDerivAt_id t).mul_const (df x u))).sub
        (((hasDerivAt_pow 2 t).div_const 2).mul_const (d2f x u u))).congr_deriv
        (by push_cast; ring)
    exact h1.hasDerivWithinAt
  have hfinal := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hψ hψ'bound
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  simp only [one_smul, one_mul, one_pow, zero_smul, add_zero, zero_mul, sub_zero, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div, Real.norm_eq_abs] at hfinal
  have hfinal2 : |f (x + u) - df x u - 1 / 2 * d2f x u u - f x| ≤ ε * ‖u‖ ^ 2 := by
    simpa using hfinal
  calc |f (x + u) - f x - df x u - (1 / 2) * d2f x u u|
      = |f (x + u) - df x u - 1 / 2 * d2f x u u - f x| := by congr 1; ring
    _ ≤ ε * ‖u‖ ^ 2 := hfinal2

/-! #### The generator limit -/

/-- **`thm:supp-A3-finite`, generator clause**: for a lattice-periodic `C²` field,
`𝓛_h F → ½ ΔF` uniformly on the torus as `h ↓ 0`. -/
theorem tendstoUniformly_generator (f : Space → ℝ) (df : Space → Space →L[ℝ] ℝ)
    (d2f : Space → Space →L[ℝ] Space →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : ∀ x, HasFDerivAt df (d2f x) x)
    (hd2f : Continuous d2f)
    (hperiod : ∀ p : lattice, ∀ y : Space, f (y + p) = f y) :
    TendstoUniformly (fun h x => generator f x h) (fun x => (1 / 2) * laplacian d2f x)
      (𝓝[>] (0 : ℝ)) := by
  -- the Hessian is periodic, hence uniformly continuous
  have hdfper : ∀ p : lattice, ∀ y : Space, df (y + p) = df y :=
    derivative_periodic lattice f df hf hperiod
  have hd2fper : ∀ p : lattice, ∀ y : Space, d2f (y + p) = d2f y :=
    derivative_periodic lattice df d2f hdf hdfper
  have huc := uniformContinuous_of_lattice_periodic basis d2f hd2f hd2fper
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp huc (ε / 8) (by positivity)
  have hmod' : ∀ a b : Space, dist a b ≤ δ / 2 → ‖d2f a - d2f b‖ ≤ ε / 8 := by
    intro a b hab
    have := hmod (lt_of_le_of_lt hab (by linarith))
    rw [dist_eq_norm] at this
    exact this.le
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < δ / 4 by positivity)).filter_mono nhdsWithin_le_nhds]
    with h hh hsmall
  intro x
  have hh' : (0 : ℝ) < h := hh
  -- remainder along every root
  have hrem : ∀ r, |f (x + h • root r) - f x - df x (h • root r) -
      (1 / 2) * d2f x (h • root r) (h • root r)| ≤ ε / 8 * (2 * h ^ 2) := by
    intro r
    have hu : ‖h • root r‖ ≤ δ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh']
      calc h * ‖root r‖ ≤ h * 2 := mul_le_mul_of_nonneg_left (root_norm_le_two r) hh'.le
        _ ≤ δ / 4 * 2 := by nlinarith
        _ = δ / 2 := by ring
    have := second_order_remainder f df d2f hf hdf (ε / 8) (δ / 2) hmod' x (h • root r) hu
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh', mul_pow, root_norm_sq] at this
    exact this.trans (le_of_eq (by ring))
  -- the sum of the linear terms vanishes, the quadratic terms give `4h² ΔF`
  have hlin : ∑ r, df x (h • root r) = 0 := by
    rw [← map_sum, ← Finset.smul_sum, sum_root, smul_zero, map_zero]
  have hquad : ∑ r, (1 / 2 : ℝ) * d2f x (h • root r) (h • root r) = 4 * h ^ 2 * laplacian d2f x := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    simp_rw [show ∀ r, h * (h * d2f x (root r) (root r)) = h ^ 2 * d2f x (root r) (root r) from
      fun r => by ring]
    rw [← Finset.mul_sum, sum_root_bilinear]
    unfold laplacian
    ring
  have hsum : generator f x h - (1 / 2) * laplacian d2f x =
      (∑ r, (f (x + h • root r) - f x - df x (h • root r) -
        (1 / 2) * d2f x (h • root r) (h • root r))) / (8 * h ^ 2) := by
    unfold generator
    have hR : ∑ r, (f (x + h • root r) - f x - df x (h • root r) -
        (1 / 2) * d2f x (h • root r) (h • root r)) =
        ∑ r, (f (x + h • root r) - f x) - ∑ r, df x (h • root r) -
          ∑ r, (1 / 2) * d2f x (h • root r) (h • root r) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    rw [hR, hlin, hquad]
    field_simp
    ring
  rw [Real.dist_eq, abs_sub_comm, hsum, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * h ^ 2),
    div_lt_iff₀ (by positivity)]
  calc |∑ r, (f (x + h • root r) - f x - df x (h • root r) -
        (1 / 2) * d2f x (h • root r) (h • root r))|
      ≤ ∑ r : Fin 12, ε / 8 * (2 * h ^ 2) := (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun r _ => hrem r)
    _ = 3 * ε * h ^ 2 := by simp; ring
    _ < ε * (8 * h ^ 2) := by nlinarith [pow_pos hh' 2]

end

end RenewalGeometry.A3SpectralizationRate
