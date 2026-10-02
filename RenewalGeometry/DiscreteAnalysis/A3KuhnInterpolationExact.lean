/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.KuhnLovaszExtensionExact
import RenewalGeometry.DiscreteAnalysis.A3PeriodicLiftOscillationExact

/-!
# The periodic Kuhn triangulation of the `A₃` torus and its piecewise-affine interpolant

Paper `predictive_spectral_geometry`, label `lem:A3-periodic-triangulation`.

The Euclidean realization `Space = ℝ³` of `W₀` carries the period lattice `Λ_{A₃}` with root
basis `b₁, b₂, b₃` (`A3PeriodicSmoothEnergy.basis`, three of the twelve roots); `coordinates`
is `T⁻¹`.  For `h = 1/d` put `scaledCoords d p = T⁻¹ p / h` (`scaledEquiv d`, a linear
isomorphism).  Then:

* `meshSimplex d k σ = hT(k + K_σ)` (the preimage of the Kuhn simplex `k + K_σ`), with vertices
  `meshVertex d k σ m = hT v_m`;
* `exists_mem_meshSimplex`, `mem_convexHull_common_meshVertices`: the mesh simplices cover
  `Space` and meet face to face (a triangulation); `add_mem_meshSimplex_iff`: the family is
  invariant under the period lattice (`k ↦ k + d z`), so it descends to the torus;
  `meshVertex_sub_point_mem_lattice`, `vertexOf_kuhnVertex_injective`: its vertices project onto
  `V_h` (`point_eq_meshVertex`: every point of `V_h` is a vertex) and the four vertices of each
  simplex stay distinct in `V_h` (`d ≥ 2`); the projection is injective on every simplex
  (`eq_of_mem_meshSimplex_of_sub_mem_lattice`, `d ≥ 2`) and for `d ≥ 3` a simplex meets another
  in at most one lattice translate (`lattice_translate_unique`), so the projected simplices meet
  in single common faces;
* `ball_subset_meshSimplex`, `norm_sub_le_of_mem_meshSimplex`: every mesh simplex contains a
  Euclidean ball of radius `h/8` and has diameter at most `6h` (shape regularity, ratio `48`
  independent of `h`);
* `meshVertex_sub_eq_sum_root_steps`: the endpoints of every mesh edge are joined by at most three
  root steps `h α`;
* `interp d f = I_h f` is the continuous piecewise-affine interpolant: it agrees with `f` on `V_h`
  (`interp_point`, `interp_meshVertex`), is affine on every mesh simplex
  (`interp_eq_barycentric`, `exists_affine_eq_interp_on_meshSimplex`) and is periodic
  (`interp_periodic`);
* `abs_interp_sub_le`, `norm_fderiv_interp_le` (`eq:A3-interpolation-bound`):
  `|I_h f q - I_h f p| ≤ √24 L_h(f) ‖q - p‖`, hence `‖∇ I_h f‖_∞ ≤ √24 L_h(f)`;
* the cells `Q_{h,x} = x + hT[0,1)³` (`cell d x`): `cell_eq` (`= point d x + h • Q₁`),
  `volume_cell` (measure `h³` times the measure of the fundamental cell, i.e. normalized Haar
  measure `h³`), `norm_sub_le_of_mem_cell` (diameter `≤ 6h`), `exists_add_mem_cell_index` and
  `index_eq_of_mem_cell` with `index_periodic` (the projected cells partition the torus);
* `abs_lift_sub_interp_le` (`eq:A3-cell-interpolation-bound`):
  `|f̂_h - I_h f| ≤ 3√8 h L_h(f)` everywhere, where `f̂_h = A3PeriodicStepFunctionLift.lift`
  equals `f(x)` on `Q_{h,x}` (`lift_eq_of_mem_cell`).

`a3_kuhn_interpolant_properties` bundles the analytic clauses.
-/

open MeasureTheory Set Module
open scoped BigOperators Pointwise Matrix.Norms.L2Operator

namespace RenewalGeometry.A3KuhnInterpolation

open A3FiniteDifferenceConsistency A3PeriodicSmoothEnergy A3PeriodicGraphSampling
open LatticePeriodicDifferentiation A3DiscreteUnitBallEquicontinuity A3PeriodicStepFunctionLift
open FiniteWeightedGraphHodgeDirac FiniteRootGraphEnergy FiniteRootGraphUnitBallBounds
open A3PeriodicConnesSmoothLowerBound KuhnLovaszExtension

noncomputable section

/-! ### Coordinates -/

/-- Scaled root-basis coordinates `u = T⁻¹ p / h`, `h = 1/d`. -/
def scaledCoords (d : ℕ) (p : Space) : Fin 3 → ℝ := fun i => (d : ℝ) * coordinates p i

/-- `scaledCoords` as a linear isomorphism (`d ≠ 0`). -/
def scaledEquiv (d : ℕ) [NeZero d] : Space ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  coordinates.trans (LinearEquiv.smulOfNeZero ℝ (Fin 3 → ℝ) (d : ℝ)
    (by exact_mod_cast NeZero.ne d))

theorem scaledEquiv_apply (d : ℕ) [NeZero d] (p : Space) : scaledEquiv d p = scaledCoords d p := by
  funext i
  simp [scaledEquiv, scaledCoords]

theorem scaledCoords_add (d : ℕ) (p q : Space) :
    scaledCoords d (p + q) = scaledCoords d p + scaledCoords d q := by
  funext i; simp [scaledCoords, mul_add]

theorem scaledCoords_sub (d : ℕ) (p q : Space) :
    scaledCoords d (p - q) = scaledCoords d p - scaledCoords d q := by
  funext i; simp [scaledCoords, mul_sub]

/-- `Σᵢ (T⁻¹ w)ᵢ² ≤ ‖w‖²`: the smallest singular value of `T` is one. -/
theorem sum_sq_coordinates_le (w : Space) : ∑ i, (coordinates w i) ^ 2 ≤ ‖w‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three, coordinates, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  nlinarith [sq_nonneg (w 0 + w 1 + w 2)]

theorem abs_coordinates_le_norm (w : Space) (i : Fin 3) : |coordinates w i| ≤ ‖w‖ := by
  have h := sum_sq_coordinates_le w
  have hi : (coordinates w i) ^ 2 ≤ ∑ j, (coordinates w j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (coordinates w j) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h' := Real.abs_le_sqrt (hi.trans h)
  rwa [Real.sqrt_sq (norm_nonneg w)] at h'

/-- `Σᵢ |(T⁻¹ w)ᵢ| ≤ √3 ‖w‖`. -/
theorem sum_abs_coordinates_le (w : Space) : ∑ i, |coordinates w i| ≤ Real.sqrt 3 * ‖w‖ := by
  have h := sum_sq_coordinates_le w
  have hcs : (∑ i, |coordinates w i|) ^ 2 ≤ 3 * ‖w‖ ^ 2 := by
    simp only [Fin.sum_univ_three] at h ⊢
    have e0 := sq_abs (coordinates w 0)
    have e1 := sq_abs (coordinates w 1)
    have e2 := sq_abs (coordinates w 2)
    nlinarith [sq_nonneg (|coordinates w 0| - |coordinates w 1|),
      sq_nonneg (|coordinates w 1| - |coordinates w 2|),
      sq_nonneg (|coordinates w 0| - |coordinates w 2|)]
  have hs : Real.sqrt (3 * ‖w‖ ^ 2) = Real.sqrt 3 * ‖w‖ := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg w)]
  have := Real.abs_le_sqrt hcs
  rw [hs] at this
  exact (le_abs_self _).trans this

/-! ### Lattice data and the interpolant -/

/-- The vertex of `V_h = (ℤ/d)³` represented by `k ∈ ℤ³`. -/
def vertexOf (d : ℕ) (k : Fin 3 → ℤ) : Vertex d := fun i => (k i : ZMod d)

/-- `f` pulled back to `ℤ³`. -/
def latticeData (d : ℕ) (f : Vertex d → ℝ) : (Fin 3 → ℤ) → ℝ := fun k => f (vertexOf d k)

/-- **The interpolant `I_h f`**: the Kuhn extension of `f` in scaled root-basis coordinates. -/
def interp (d : ℕ) (f : Vertex d → ℝ) (p : Space) : ℝ :=
  kuhnExt (latticeData d f) (scaledCoords d p)

theorem vertexOf_add_single (d : ℕ) (k : Fin 3 → ℤ) (i : Fin 3) :
    vertexOf d (k + Pi.single i 1) = vertexOf d k + Pi.single i 1 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [vertexOf]
  · simp [vertexOf, hj]

theorem vertexOf_add_mul (d : ℕ) (k z : Fin 3 → ℤ) :
    vertexOf d (k + fun i => (d : ℤ) * z i) = vertexOf d k := by
  funext i
  simp [vertexOf]

theorem scaledCoords_point (d : ℕ) [NeZero d] (x : Vertex d) :
    scaledCoords d (point d x) = fun i => (((x i).val : ℤ) : ℝ) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  funext i
  simp [scaledCoords, coordinates_point, mul_div_cancel₀ _ hd]

theorem vertexOf_val (d : ℕ) [NeZero d] (x : Vertex d) :
    vertexOf d (fun i => ((x i).val : ℤ)) = x := by
  funext i
  simp [vertexOf]

/-- `I_h f` agrees with `f` on the vertex set `V_h`. -/
theorem interp_point (d : ℕ) [NeZero d] (f : Vertex d → ℝ) (x : Vertex d) :
    interp d f (point d x) = f x := by
  rw [interp, scaledCoords_point, kuhnExt_intCast, latticeData, vertexOf_val]

theorem scaledCoords_integerCombination (d : ℕ) (p : Space) (z : Fin 3 → ℤ) :
    scaledCoords d (p + integerCombination basis z) =
      scaledCoords d p + fun i => (((d : ℤ) * z i : ℤ) : ℝ) := by
  funext i
  simp [scaledCoords, coordinates_integerCombination, mul_add]

/-- `I_h f` is periodic under the period lattice, so it descends to the torus `M`. -/
theorem interp_periodic (d : ℕ) (f : Vertex d → ℝ) (q : lattice) (p : Space) :
    interp d f (p + q) = interp d f p := by
  obtain ⟨z, hz⟩ := q.property
  rw [interp, interp, ← hz, scaledCoords_integerCombination]
  apply kuhnExt_add_intCast_of_periodic
  intro k
  simp only [latticeData]
  rw [vertexOf_add_mul]

/-! ### The interpolation bound `‖∇ I_h f‖ ≤ √24 L_h(f)` -/

theorem graphLipschitz_nonneg (d : ℕ) [NeZero d] (f : Vertex d → ℝ) :
    0 ≤ graphLipschitz (mass d) (conductance d) f := by
  unfold graphLipschitz
  exact norm_nonneg _

/-- Every single root difference is at most `√8 h L_h(f)`. -/
theorem abs_step_le (d : ℕ) [NeZero d] (f : Vertex d → ℝ) (x : Vertex d) (i : Fin 3) :
    |f (x + Pi.single i 1) - f x| ≤
      Real.sqrt 8 * mesh d * graphLipschitz (mass d) (conductance d) f := by
  set L := graphLipschitz (mass d) (conductance d) f with hL
  have hLnn : 0 ≤ L := graphLipschitz_nonneg d f
  have hh := mesh_pos d
  have hloc := localEnergy_le_graphLipschitz_sq (mass d) (conductance d) f x
  unfold mass conductance at hloc
  change _ ≤ L ^ 2 at hloc
  rw [localEnergy_eq_root_difference_sum (rootStep d) (1 / 8) (mesh d) (by norm_num) hh] at hloc
  have hterm : ((f (rootStep d x (![0, 4, 8] i)) - f x) / mesh d) ^ 2 ≤
      ∑ r : Fin 12, ((f (rootStep d x r) - f x) / mesh d) ^ 2 :=
    Finset.single_le_sum (f := fun r => ((f (rootStep d x r) - f x) / mesh d) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
  rw [rootStep_selected_basis] at hterm
  have hsq : ((f (x + Pi.single i 1) - f x) / mesh d) ^ 2 ≤ 8 * L ^ 2 := by
    linarith
  have habs := Real.abs_le_sqrt hsq
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hLnn, abs_div, abs_of_pos hh,
    div_le_iff₀ hh] at habs
  linarith

theorem abs_latticeData_step_le (d : ℕ) [NeZero d] (f : Vertex d → ℝ) (i : Fin 3)
    (k : Fin 3 → ℤ) :
    |latticeData d f (k + Pi.single i 1) - latticeData d f k| ≤
      Real.sqrt 8 * mesh d * graphLipschitz (mass d) (conductance d) f := by
  simp only [latticeData]
  rw [vertexOf_add_single]
  exact abs_step_le d f (vertexOf d k) i

/-- **`eq:A3-interpolation-bound`, Lipschitz form.**
`|I_h f q - I_h f p| ≤ √24 L_h(f) ‖q - p‖`. -/
theorem abs_interp_sub_le (d : ℕ) [NeZero d] (f : Vertex d → ℝ) (p q : Space) :
    |interp d f q - interp d f p| ≤
      Real.sqrt 24 * graphLipschitz (mass d) (conductance d) f * ‖q - p‖ := by
  set L := graphLipschitz (mass d) (conductance d) f with hL
  have hLnn : 0 ≤ L := graphLipschitz_nonneg d f
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hmesh : mesh d * (d : ℝ) = 1 := by unfold mesh; field_simp
  have h := abs_kuhnExt_sub_le (latticeData d f) (fun _ => Real.sqrt 8 * mesh d * L)
    (fun i k => abs_latticeData_step_le d f i k) (scaledCoords d p) (scaledCoords d q)
  have hdiff : ∀ i, |scaledCoords d q i - scaledCoords d p i| =
      (d : ℝ) * |coordinates (q - p) i| := by
    intro i
    rw [show scaledCoords d q i - scaledCoords d p i = (d : ℝ) * coordinates (q - p) i by
      simp [scaledCoords, mul_sub], abs_mul, Nat.abs_cast]
  simp only [hdiff] at h
  have hsum : ∑ i : Fin 3, Real.sqrt 8 * mesh d * L * ((d : ℝ) * |coordinates (q - p) i|) =
      Real.sqrt 8 * L * ∑ i, |coordinates (q - p) i| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show Real.sqrt 8 * mesh d * L * ((d : ℝ) * |coordinates (q - p) i|) =
      Real.sqrt 8 * L * (mesh d * d) * |coordinates (q - p) i| by ring, hmesh, mul_one]
  rw [hsum] at h
  have h24 : Real.sqrt 24 = Real.sqrt 8 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  calc
    |interp d f q - interp d f p| ≤ Real.sqrt 8 * L * ∑ i, |coordinates (q - p) i| := h
    _ ≤ Real.sqrt 8 * L * (Real.sqrt 3 * ‖q - p‖) :=
      mul_le_mul_of_nonneg_left (sum_abs_coordinates_le _) (by positivity)
    _ = Real.sqrt 24 * L * ‖q - p‖ := by rw [h24]; ring

theorem lipschitzWith_interp (d : ℕ) [NeZero d] (f : Vertex d → ℝ) :
    LipschitzWith ⟨Real.sqrt 24 * graphLipschitz (mass d) (conductance d) f,
      mul_nonneg (Real.sqrt_nonneg _) (graphLipschitz_nonneg d f)⟩ (interp d f) := by
  apply LipschitzWith.of_dist_le_mul
  intro q p
  rw [Real.dist_eq, dist_eq_norm]
  exact abs_interp_sub_le d f p q

theorem continuous_interp (d : ℕ) [NeZero d] (f : Vertex d → ℝ) : Continuous (interp d f) :=
  (lipschitzWith_interp d f).continuous

/-- **`eq:A3-interpolation-bound`.**  `‖∇ I_h f‖ ≤ √24 L_h(f)` at every point. -/
theorem norm_fderiv_interp_le (d : ℕ) [NeZero d] (f : Vertex d → ℝ) (p : Space) :
    ‖fderiv ℝ (interp d f) p‖ ≤ Real.sqrt 24 * graphLipschitz (mass d) (conductance d) f :=
  norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_interp d f)

/-! ### Comparison with the cell lift (`eq:A3-cell-interpolation-bound`) -/

theorem lift_eq_latticeData_floor (d : ℕ) (f : Vertex d → ℝ) (p : Space) :
    lift d f p = latticeData d f (floorVec (scaledCoords d p)) := rfl

/-- **`eq:A3-cell-interpolation-bound`.**  `|f̂_h - I_h f| ≤ 3√8 h L_h(f)` everywhere. -/
theorem abs_lift_sub_interp_le (d : ℕ) [NeZero d] (f : Vertex d → ℝ) (p : Space) :
    |lift d f p - interp d f p| ≤
      3 * (Real.sqrt 8 * mesh d * graphLipschitz (mass d) (conductance d) f) := by
  rw [abs_sub_comm, lift_eq_latticeData_floor, interp]
  have h := abs_kuhnExt_sub_floor_le (latticeData d f)
    (fun _ => Real.sqrt 8 * mesh d * graphLipschitz (mass d) (conductance d) f)
    (fun i k => abs_latticeData_step_le d f i k) (scaledCoords d p)
  simp only [Fin.sum_univ_three] at h
  linarith

/-! ### The periodic mesh `hT(k + K_σ)` -/

/-- The mesh simplex `hT(k + K_σ)`. -/
def meshSimplex (d : ℕ) (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) : Set Space :=
  scaledCoords d ⁻¹' kuhnSimplex k σ

/-- The mesh vertex `hT v_m`. -/
def meshVertex (d : ℕ) [NeZero d] (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (m : ℕ) : Space :=
  (scaledEquiv d).symm (kuhnVertexR k σ m)

/-- The barycentre `hT c_σ` of a mesh simplex. -/
def meshCenter (d : ℕ) [NeZero d] (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) : Space :=
  (scaledEquiv d).symm (kuhnCenter k σ)

variable {d : ℕ} [NeZero d] {k k' : Fin 3 → ℤ} {σ σ' : Equiv.Perm (Fin 3)}

theorem scaledCoords_scaledEquiv_symm (u : Fin 3 → ℝ) :
    scaledCoords d ((scaledEquiv d).symm u) = u := by
  rw [← scaledEquiv_apply, LinearEquiv.apply_symm_apply]

theorem scaledCoords_meshVertex (m : ℕ) :
    scaledCoords d (meshVertex d k σ m) = kuhnVertexR k σ m :=
  scaledCoords_scaledEquiv_symm _

theorem meshVertex_mem_meshSimplex (m : Fin 4) : meshVertex d k σ m ∈ meshSimplex d k σ := by
  simp only [meshSimplex, mem_preimage, scaledCoords_meshVertex]
  exact subset_convexHull ℝ _ ⟨m, rfl⟩

/-- `I_h f` takes the value `f(x)` at the mesh vertex over `x`. -/
theorem interp_meshVertex (f : Vertex d → ℝ) (m : ℕ) :
    interp d f (meshVertex d k σ m) = f (vertexOf d (kuhnVertex k σ m)) := by
  rw [interp, scaledCoords_meshVertex]
  exact kuhnExt_intCast _ _

/-- **Covering.** -/
theorem exists_mem_meshSimplex (d : ℕ) (p : Space) : ∃ k σ, p ∈ meshSimplex d k σ :=
  exists_mem_kuhnSimplex (scaledCoords d p)

/-- **Face-to-face compatibility of the mesh.** -/
theorem mem_convexHull_common_meshVertices {p : Space} (hp : p ∈ meshSimplex d k σ)
    (hp' : p ∈ meshSimplex d k' σ') :
    p ∈ convexHull ℝ ((Set.range fun m : Fin 4 => meshVertex d k σ m) ∩
      Set.range fun m : Fin 4 => meshVertex d k' σ' m) := by
  have h := mem_convexHull_common_vertices hp hp'
  set e := scaledEquiv d
  have himg := LinearMap.image_convexHull (e.symm : (Fin 3 → ℝ) →ₗ[ℝ] Space)
    ((Set.range fun m : Fin 4 => kuhnVertexR k σ m) ∩
      Set.range fun m : Fin 4 => kuhnVertexR k' σ' m)
  have hp_eq : e.symm (scaledCoords d p) = p := by
    rw [← scaledEquiv_apply, LinearEquiv.symm_apply_apply]
  have hmem : p ∈ (e.symm : (Fin 3 → ℝ) →ₗ[ℝ] Space) '' convexHull ℝ
      ((Set.range fun m : Fin 4 => kuhnVertexR k σ m) ∩
        Set.range fun m : Fin 4 => kuhnVertexR k' σ' m) := ⟨_, h, hp_eq⟩
  rw [himg, Set.image_inter (f := ⇑(e.symm : (Fin 3 → ℝ) →ₗ[ℝ] Space)) e.symm.injective,
    ← Set.range_comp, ← Set.range_comp] at hmem
  exact hmem

/-- **Periodicity of the mesh**: translating by a period `T z` maps `hT(k + K_σ)` onto
`hT(k + d z + K_σ)`. -/
theorem add_mem_meshSimplex_iff (z : Fin 3 → ℤ) (p : Space) :
    p + integerCombination basis z ∈ meshSimplex d (k + fun i => (d : ℤ) * z i) σ ↔
      p ∈ meshSimplex d k σ := by
  simp only [meshSimplex, mem_preimage, mem_kuhnSimplex_iff, scaledCoords_integerCombination]
  have hc : ∀ a, kuhnCoord (k + fun i => (d : ℤ) * z i) σ
      (scaledCoords d p + fun i => (((d : ℤ) * z i : ℤ) : ℝ)) a =
        kuhnCoord k σ (scaledCoords d p) a := by
    intro a
    simp only [kuhnCoord, Pi.add_apply]
    push_cast
    ring
  simp only [KuhnOrdered, hc]

theorem coordinates_scaledEquiv_symm (u : Fin 3 → ℝ) (i : Fin 3) :
    coordinates ((scaledEquiv d).symm u) i = u i / d := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have h := congrFun (scaledCoords_scaledEquiv_symm (d := d) u) i
  simp only [scaledCoords] at h
  rw [← h]
  field_simp

/-- **The mesh vertices project onto `V_h`.** -/
theorem meshVertex_sub_point_mem_lattice (k : Fin 3 → ℤ) :
    (scaledEquiv d).symm (fun i => (k i : ℝ)) - point d (vertexOf d k) ∈ lattice := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  refine ⟨fun i => k i / (d : ℤ), ?_⟩
  apply coordinates.injective
  rw [coordinates_integerCombination]
  funext i
  rw [map_sub, Pi.sub_apply, coordinates_scaledEquiv_symm, coordinates_point]
  have hval : (((vertexOf d k i).val : ℤ) : ℝ) = ((k i % (d : ℤ) : ℤ) : ℝ) := by
    rw [vertexOf, ZMod.val_intCast]
  have hdiv : (k i : ℝ) = (d : ℝ) * ((k i / (d : ℤ) : ℤ) : ℝ) + ((k i % (d : ℤ) : ℤ) : ℝ) := by
    have := Int.mul_ediv_add_emod (k i) (d : ℤ)
    exact_mod_cast this.symm
  have hv : ((vertexOf d k i).val : ℝ) = ((k i % (d : ℤ) : ℤ) : ℝ) := by exact_mod_cast hval
  rw [hv, hdiv]
  field_simp
  ring

theorem meshVertex_sub_point_vertex_mem_lattice (m : ℕ) :
    meshVertex d k σ m - point d (vertexOf d (kuhnVertex k σ m)) ∈ lattice :=
  meshVertex_sub_point_mem_lattice _

/-- For `d ≥ 2` the four vertices of each mesh simplex project to four distinct points of
`V_h`. -/
theorem vertexOf_kuhnVertex_injective (hd : 2 ≤ d) (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) :
    Function.Injective fun m : Fin 4 => vertexOf d (kuhnVertex k σ m) := by
  have : Fact (1 < d) := ⟨by omega⟩
  have key : ∀ m m' : Fin 4, (m : ℕ) < m' →
      vertexOf d (kuhnVertex k σ m) ≠ vertexOf d (kuhnVertex k σ m') := by
    intro m m' hlt heq
    have hm3 : (m : ℕ) < 3 := by omega
    have h := congrFun heq (σ ⟨m, hm3⟩)
    simp only [vertexOf, kuhnVertex_apply_perm] at h
    rw [if_neg (by simp), if_pos (by simpa using hlt)] at h
    push_cast at h
    have : (1 : ZMod d) = 0 := by
      have h' := congrArg (fun t => t - ((k (σ ⟨m, hm3⟩) : ℤ) : ZMod d)) h
      simpa using h'.symm
    exact one_ne_zero this
  intro m m' h
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · exact key m m' hlt h
  · exact key m' m hlt h.symm

/-- `‖w‖ ≤ 6c` when all root-basis coordinates of `w` are at most `c` in modulus. -/
theorem norm_le_of_abs_coordinates_le (w : Space) (c : ℝ)
    (h : ∀ i, |coordinates w i| ≤ c) : ‖w‖ ≤ 6 * c := by
  have hw : ∑ i, coordinates w i • basis i = w := by
    have := basis.sum_repr w
    simpa [basis] using this
  have hb : ∀ i, ‖basis i‖ ≤ 2 := fun i => by
    rw [basis_eq_selected_root]; exact A3UniformEnergyConsistency.root_norm_le_two _
  have hc : 0 ≤ c := (abs_nonneg _).trans (h 0)
  rw [← hw]
  calc
    ‖∑ i, coordinates w i • basis i‖ ≤ ∑ i, ‖coordinates w i • basis i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, c * 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (h i) (hb i) (norm_nonneg _) hc
    _ = 6 * c := by simp; ring

/-- **Shape regularity, inner ball.**  Every mesh simplex contains the Euclidean ball of radius
`h/8` about its barycentre. -/
theorem ball_subset_meshSimplex :
    Metric.ball (meshCenter d k σ) (mesh d / 8) ⊆ meshSimplex d k σ := by
  intro p hp
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  apply mem_kuhnSimplex_of_near_center
  intro j
  have hc : scaledCoords d (meshCenter d k σ) = kuhnCenter k σ :=
    scaledCoords_scaledEquiv_symm _
  have he : scaledCoords d p j - kuhnCenter k σ j =
      (d : ℝ) * coordinates (p - meshCenter d k σ) j := by
    rw [← hc]
    simp [scaledCoords, mul_sub]
  rw [he, abs_mul, Nat.abs_cast]
  rw [Metric.mem_ball, dist_eq_norm] at hp
  calc
    (d : ℝ) * |coordinates (p - meshCenter d k σ) j| ≤ d * ‖p - meshCenter d k σ‖ :=
      mul_le_mul_of_nonneg_left (abs_coordinates_le_norm _ _) hd.le
    _ < d * (mesh d / 8) := mul_lt_mul_of_pos_left hp hd
    _ = 1 / 8 := by unfold mesh; field_simp

/-- **Shape regularity, diameter.**  Every mesh simplex has diameter at most `6h`. -/
theorem norm_sub_le_of_mem_meshSimplex {p p' : Space} (hp : p ∈ meshSimplex d k σ)
    (hp' : p' ∈ meshSimplex d k σ) : ‖p - p'‖ ≤ 6 * mesh d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  apply norm_le_of_abs_coordinates_le
  intro i
  have h := abs_sub_le_one_of_mem_kuhnSimplex hp hp' i
  have he : scaledCoords d p i - scaledCoords d p' i = (d : ℝ) * coordinates (p - p') i := by
    simp [scaledCoords, mul_sub]
  rw [he, abs_mul, Nat.abs_cast] at h
  unfold mesh
  rw [le_div_iff₀ hd]
  linarith

theorem scaledEquiv_symm_single (j : Fin 3) :
    (scaledEquiv d).symm (Pi.single j 1) = mesh d • root (![0, 4, 8] j) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [← basis_eq_selected_root]
  apply (scaledEquiv d).injective
  rw [LinearEquiv.apply_symm_apply, scaledEquiv_apply]
  funext i
  simp only [scaledCoords, map_smul, Pi.smul_apply, smul_eq_mul]
  have hb : coordinates (basis j) i = (Pi.single j (1 : ℝ) : Fin 3 → ℝ) i := by
    simp [basis]
  rw [hb]
  unfold mesh
  field_simp

/-- **Edges are at most three root steps.**  For `a ≤ b` the mesh vertices satisfy
`hT v_b - hT v_a = Σ h α_c` over the (at most three) `c` with `a ≤ c < b`, each `α_c` a root. -/
theorem meshVertex_sub_eq_sum_root_steps {a b : ℕ} (hab : a ≤ b) :
    meshVertex d k σ b - meshVertex d k σ a =
      ∑ c ∈ Finset.univ.filter (fun c : Fin 3 => a ≤ (c : ℕ) ∧ (c : ℕ) < b),
        mesh d • root (![0, 4, 8] (σ c)) := by
  have hv : kuhnVertexR k σ b - kuhnVertexR k σ a =
      ∑ c ∈ Finset.univ.filter (fun c : Fin 3 => a ≤ (c : ℕ) ∧ (c : ℕ) < b),
        (Pi.single (σ c) 1 : Fin 3 → ℝ) := by
    funext j
    have h := congrFun (kuhnVertex_eq_add_steps k σ hab) j
    simp only [Pi.add_apply, Finset.sum_apply] at h
    simp only [kuhnVertexR, Pi.sub_apply, Finset.sum_apply, h]
    push_cast
    simp only [add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hj : j = σ c
    · subst hj; simp
    · simp [hj]
  rw [meshVertex, meshVertex, ← map_sub, hv, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact scaledEquiv_symm_single (σ c)

theorem card_root_steps_le_three (a b : ℕ) :
    (Finset.univ.filter (fun c : Fin 3 => a ≤ (c : ℕ) ∧ (c : ℕ) < b)).card ≤ 3 :=
  (Finset.card_le_univ _).trans (by simp)

/-- **`I_h f` is affine on every mesh simplex** (barycentric form). -/
theorem interp_eq_barycentric (f : Vertex d → ℝ) {p : Space} (hp : p ∈ meshSimplex d k σ) :
    interp d f p = ∑ m : Fin 4,
      kuhnWeights k σ (scaledCoords d p) m * f (vertexOf d (kuhnVertex k σ m)) :=
  kuhnExt_eq_barycentric _ hp

/-- **`I_h f` is affine on every mesh simplex.** -/
theorem exists_affine_eq_interp_on_meshSimplex (f : Vertex d → ℝ) (k : Fin 3 → ℤ)
    (σ : Equiv.Perm (Fin 3)) :
    ∃ (ℓ : Space →ₗ[ℝ] ℝ) (c : ℝ), ∀ p ∈ meshSimplex d k σ, interp d f p = ℓ p + c := by
  let g : ℕ → ℝ := fun m => f (vertexOf d (kuhnVertex k σ m))
  let δ : Fin 3 → ℝ := ![g 1 - g 0, g 2 - g 1, g 3 - g 2]
  let ℓ : Space →ₗ[ℝ] ℝ :=
    ∑ a : Fin 3, δ a • ((LinearMap.proj (σ a)).comp (scaledEquiv d).toLinearMap)
  refine ⟨ℓ, g 0 - ∑ a : Fin 3, δ a * (k (σ a) : ℝ), fun p hp => ?_⟩
  rw [interp_eq_barycentric f hp]
  simp only [ℓ, δ, g, Fin.sum_univ_four, kuhnWeights, kuhnCoord]
  simp [scaledEquiv_apply, Fin.sum_univ_three]
  ring

/-! ### The cells `Q_{h,x} = x + hT[0,1)³` -/

/-- The cell `Q_{h,x}`. -/
def cell (d : ℕ) (x : Vertex d) : Set Space :=
  {p | ∀ i, scaledCoords d p i - ((x i).val : ℝ) ∈ Ico (0 : ℝ) 1}

/-- The fundamental cell `T[0,1)³` of the period lattice. -/
def fundamentalCell : Set Space := {p | ∀ i, coordinates p i ∈ Ico (0 : ℝ) 1}

theorem index_eq_of_mem_cell {x : Vertex d} {p : Space} (hp : p ∈ cell d x) :
    index d p = x := by
  funext i
  have h := hp i
  have hfl : integerIndex d p i = ((x i).val : ℤ) := by
    rw [integerIndex, Int.floor_eq_iff]
    simp only [scaledCoords] at h
    push_cast
    constructor <;> linarith [h.1, h.2]
  change ((integerIndex d p i : ℤ) : ZMod d) = x i
  rw [hfl]
  simp

/-- `f̂_h = f(x)` on `Q_{h,x}`. -/
theorem lift_eq_of_mem_cell (f : Vertex d → ℝ) {x : Vertex d} {p : Space}
    (hp : p ∈ cell d x) : lift d f p = f x := by
  rw [lift, index_eq_of_mem_cell hp]

theorem index_periodic (q : lattice) (p : Space) : index d (p + q) = index d p := by
  obtain ⟨z, hz⟩ := q.property
  funext i
  change (integerIndex d (p + q.val) i : ZMod d) = (integerIndex d p i : ZMod d)
  rw [← hz, integerIndex_lattice_translate]
  simp

/-- Every point is a lattice translate of a point of the cell of its own index; with
`index_eq_of_mem_cell` and `index_periodic`, the projected cells partition the torus. -/
theorem exists_add_mem_cell_index (p : Space) :
    ∃ q ∈ lattice, p + q ∈ cell d (index d p) := by
  have hd : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set F : Fin 3 → ℤ := fun i => ⌊(d : ℝ) * coordinates p i⌋ with hF
  refine ⟨integerCombination basis (fun i => -(F i / d)), ⟨_, rfl⟩, fun i => ?_⟩
  rw [scaledCoords_integerCombination]
  have hval : (((index d p i).val : ℕ) : ℝ) = ((F i % (d : ℤ) : ℤ) : ℝ) := by
    have h1 : ((index d p i).val : ℤ) = F i % (d : ℤ) := by
      change (((F i : ℤ) : ZMod d).val : ℤ) = _
      rw [ZMod.val_intCast]
    exact_mod_cast h1
  have hdiv : ((F i : ℤ) : ℝ) = (d : ℝ) * ((F i / (d : ℤ) : ℤ) : ℝ) + ((F i % (d : ℤ) : ℤ) : ℝ) := by
    have := Int.mul_ediv_add_emod (F i) (d : ℤ)
    exact_mod_cast this.symm
  have hfl : ((F i : ℤ) : ℝ) ≤ (d : ℝ) * coordinates p i := Int.floor_le _
  have hfl' : (d : ℝ) * coordinates p i < ((F i : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  simp only [Pi.add_apply, scaledCoords, hval]
  push_cast
  constructor <;> linarith [hdiv]

theorem cell_eq (x : Vertex d) : cell d x = point d x +ᵥ (mesh d • fundamentalCell) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hm : mesh d ≠ 0 := (mesh_pos d).ne'
  ext p
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_smul_set_iff_inv_smul_mem₀ hm]
  simp only [cell, fundamentalCell, mem_setOf_eq, vadd_eq_add, map_smul, map_add, map_neg,
    Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul, scaledCoords, coordinates_point]
  have hinv : (mesh d)⁻¹ = d := by unfold mesh; simp
  rw [hinv]
  constructor <;> intro h i <;> have := h i <;> field_simp at this ⊢ <;>
    simpa [mul_comm, add_comm, sub_eq_add_neg] using this

/-- **Cell measure.**  `|Q_{h,x}| = h³ |T[0,1)³|`: each cell has normalized Haar measure `h³`. -/
theorem volume_cell (x : Vertex d) :
    volume (cell d x) = ENNReal.ofReal (mesh d ^ 3) * volume fundamentalCell := by
  rw [cell_eq, measure_vadd, Measure.addHaar_smul, finrank_euclideanSpace_fin,
    abs_of_pos (pow_pos (mesh_pos d) 3)]

/-- **Cell diameter.**  Two points of `Q_{h,x}` are at distance at most `6h`. -/
theorem norm_sub_le_of_mem_cell {x : Vertex d} {p p' : Space} (hp : p ∈ cell d x)
    (hp' : p' ∈ cell d x) : ‖p - p'‖ ≤ 6 * mesh d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  apply norm_le_of_abs_coordinates_le
  intro i
  have h := hp i
  have h' := hp' i
  have he : (d : ℝ) * coordinates (p - p') i = scaledCoords d p i - scaledCoords d p' i := by
    simp [scaledCoords, mul_sub]
  have hb : |(d : ℝ) * coordinates (p - p') i| ≤ 1 := by
    rw [he, abs_le]
    constructor <;> linarith [h.1, h.2, h'.1, h'.2]
  rw [abs_mul, Nat.abs_cast] at hb
  unfold mesh
  rw [le_div_iff₀ hd]
  linarith

/-! ### Descent to the torus and the bundled statement -/

theorem scaledCoords_sub_integerCombination (p p' : Space) (z : Fin 3 → ℤ)
    (h : p - p' = integerCombination basis z) (i : Fin 3) :
    scaledCoords d p i - scaledCoords d p' i = (d : ℝ) * (z i : ℝ) := by
  have := congrArg (fun w => scaledCoords d w i) h
  simp only [scaledCoords, map_sub, Pi.sub_apply, coordinates_integerCombination] at this
  rw [← this]
  simp [scaledCoords, mul_sub]

/-- For `d ≥ 2` the projection to the torus is injective on every mesh simplex. -/
theorem eq_of_mem_meshSimplex_of_sub_mem_lattice (hd : 2 ≤ d) {p p' : Space}
    (hp : p ∈ meshSimplex d k σ) (hp' : p' ∈ meshSimplex d k σ) (hq : p - p' ∈ lattice) :
    p = p' := by
  obtain ⟨z, hz⟩ := hq
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hz0 : z = 0 := by
    funext i
    have h1 := abs_sub_le_one_of_mem_kuhnSimplex hp hp' i
    rw [scaledCoords_sub_integerCombination p p' z hz.symm i, abs_mul, Nat.abs_cast] at h1
    by_contra hne
    have : (1 : ℝ) ≤ |(z i : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
    nlinarith [abs_nonneg ((z i : ℝ))]
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

/-- For `d ≥ 3` a mesh simplex meets a given mesh simplex in at most one lattice translate, so
the projected simplices intersect in single common faces (the quotient is a simplicial mesh). -/
theorem lattice_translate_unique (hd : 3 ≤ d) {p p' : Space} {z z' : Fin 3 → ℤ}
    (hp : p ∈ meshSimplex d k σ) (hp' : p' ∈ meshSimplex d k σ)
    (hq : p + integerCombination basis z ∈ meshSimplex d k' σ')
    (hq' : p' + integerCombination basis z' ∈ meshSimplex d k' σ') : z = z' := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  funext i
  have h1 := abs_sub_le_one_of_mem_kuhnSimplex hp hp' i
  have h2 := abs_sub_le_one_of_mem_kuhnSimplex hq hq' i
  simp only [scaledCoords_integerCombination, Pi.add_apply] at h2
  have he : ((d : ℤ) * z i : ℤ) - ((d : ℤ) * z' i : ℤ) = (d : ℤ) * (z i - z' i) := by ring
  have hb : |(d : ℝ) * ((z i - z' i : ℤ) : ℝ)| ≤ 2 := by
    have : (d : ℝ) * ((z i - z' i : ℤ) : ℝ) =
        (scaledCoords d p i + (((d : ℤ) * z i : ℤ) : ℝ) -
          (scaledCoords d p' i + (((d : ℤ) * z' i : ℤ) : ℝ))) -
        (scaledCoords d p i - scaledCoords d p' i) := by push_cast; ring
    rw [this]
    exact (abs_sub _ _).trans (by linarith)
  by_contra hne
  have hne' : z i - z' i ≠ 0 := sub_ne_zero.mpr hne
  have : (1 : ℝ) ≤ |((z i - z' i : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne'
  rw [abs_mul, Nat.abs_cast] at hb
  nlinarith [abs_nonneg (((z i - z' i : ℤ) : ℝ))]

/-- Every vertex of `V_h` is a mesh vertex. -/
theorem point_eq_meshVertex (x : Vertex d) (σ : Equiv.Perm (Fin 3)) :
    point d x = meshVertex d (fun i => ((x i).val : ℤ)) σ 0 := by
  apply (scaledEquiv d).injective
  rw [meshVertex, LinearEquiv.apply_symm_apply, scaledEquiv_apply, scaledCoords_point]
  funext j
  simp [kuhnVertexR, kuhnVertex]

/-- **Bundled analytic content of `lem:A3-periodic-triangulation`.**  `I_h f` interpolates `f`
on `V_h`, is continuous, periodic, affine on every mesh simplex, satisfies
`‖∇ I_h f‖ ≤ √24 L_h(f)` (`eq:A3-interpolation-bound`) and
`|f̂_h - I_h f| ≤ 3√8 h L_h(f)` (`eq:A3-cell-interpolation-bound`). -/
theorem a3_kuhn_interpolant_properties (f : Vertex d → ℝ) :
    (∀ x, interp d f (point d x) = f x) ∧ Continuous (interp d f) ∧
      (∀ (q : lattice) (p : Space), interp d f (p + q) = interp d f p) ∧
      (∀ k σ, ∃ (ℓ : Space →ₗ[ℝ] ℝ) (c : ℝ), ∀ p ∈ meshSimplex d k σ,
        interp d f p = ℓ p + c) ∧
      (∀ p, ‖fderiv ℝ (interp d f) p‖ ≤
        Real.sqrt 24 * graphLipschitz (mass d) (conductance d) f) ∧
      (∀ p, |lift d f p - interp d f p| ≤
        3 * Real.sqrt 8 * mesh d * graphLipschitz (mass d) (conductance d) f) :=
  ⟨interp_point d f, continuous_interp d f, interp_periodic d f,
    exists_affine_eq_interp_on_meshSimplex f, norm_fderiv_interp_le d f,
    fun p => by have := abs_lift_sub_interp_le d f p; linarith⟩

end

end RenewalGeometry.A3KuhnInterpolation
