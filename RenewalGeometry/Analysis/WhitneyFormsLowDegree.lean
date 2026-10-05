/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Whitney forms of degrees 0 and 1 on a simplex (`lem:Whitney`, local part)

Einstein–Standard-Model action-closure manuscript, `eq:Whitney` and `lem:Whitney`
("Commuting reconstruction and positive comparison norm"), for `k = 0, 1` on one nondegenerate
simplex `S = conv(v₀, …, v_n)` of a finite-dimensional real inner product space `E`
(`dim E = n`), with barycentric coordinates `λ_i` (`AffineBasis.coord`):

* `W0 c = Σ_i c_i λ_i` (`eq:Whitney`, `k = 0`) and `W1 c = ½ Σ_{i,j} c_{ij} w_{ij}`,
  `w_{ij} = λ_i dλ_j - λ_j dλ_i` (`eq:Whitney`, `k = 1`, `1! = 1`) on oriented (antisymmetric)
  1-cochains `c_{ji} = -c_{ij}`, i.e. `W1 c = Σ_{i<j} c_{ij} w_{ij}`;
* de Rham maps `R0 f = (f(v_i))_i`, `R1 ω = (∫_{[v_k,v_l]} ω)_{kl}` (line integral along the
  oriented edge);
* `R0_W0`, `R1_W1`: `R_h W_h = I` (Kronecker pairing; the edge integrand of `w_{ij}` on
  `[v_k, v_l]` is the constant `δ_{ik}δ_{jl} - δ_{il}δ_{jk}`);
* `fderiv_W0`: `d W_h = W_h d_h` in degree 0 (from `Σ λ_i = 1`, `Σ dλ_i = 0`);
* `R1_fderiv`: `R_h d = d_h R_h` on smooth functions (fundamental theorem of calculus on edges);
* `mass0_pos`, `mass1_pos`: the comparison norms `∫_S |W c|²` are positive definite on cochains
  (injectivity from `R_h W_h = I`, nonempty interior of `S`, Haar measure).

Not covered (disclosed): degrees `k ≥ 2`, the assembly over a shape-regular mesh (conformity across
faces), the uniform cellwise scaling constants, and the strong convergence `P_h^k → I` of the
orthogonal projections. The comparison norm of 1-forms is the dual (operator) norm of `E →L ℝ`,
which is the Hilbert norm of the dual of the inner product space `E`.
-/

open MeasureTheory Set

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace WhitneyLow

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (b : AffineBasis ι ℝ E)

/-- Kronecker delta. -/
def δ (i j : ι) : ℝ := if i = j then 1 else 0

/-- The barycentric coordinate `λ_i`. -/
def lam (i : ι) (x : E) : ℝ := b.coord i x

/-- Its differential `dλ_i`. -/
def dlam (i : ι) : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i).linear

theorem lam_vertex (i j : ι) : lam b i (b j) = δ i j := b.coord_apply i j

theorem sum_lam (x : E) : ∑ i, lam b i x = 1 := b.sum_coord_apply_eq_one x

theorem lam_add (i : ι) (x v : E) : lam b i (x + v) = lam b i x + dlam b i v := by
  have := (b.coord i).map_vadd x v
  simp only [vadd_eq_add, smul_eq_mul] at this
  rw [lam, add_comm x v, this, add_comm]; rfl

theorem sum_dlam (v : E) : ∑ i, dlam b i v = 0 := by
  have h1 := sum_lam b (0 + v)
  have h0 := sum_lam b 0
  simp only [lam_add, Finset.sum_add_distrib] at h1
  linarith

theorem dlam_vertex_sub (j k l : ι) : dlam b j (b l - b k) = δ j l - δ j k := by
  have := lam_add b j (b k) (b l - b k)
  rw [add_sub_cancel, lam_vertex, lam_vertex] at this
  linarith

theorem continuous_lam (i : ι) : Continuous (lam b i) :=
  (b.coord i).continuous_of_finiteDimensional

theorem hasFDerivAt_lam (i : ι) (x : E) : HasFDerivAt (lam b i) (dlam b i) x := by
  have e : lam b i = fun y => dlam b i y + lam b i 0 := funext fun y => by
    have := lam_add b i 0 y
    rw [zero_add] at this
    rw [this, add_comm]
  rw [e]
  exact (dlam b i).hasFDerivAt.add_const _

/-! ### Degree 0 -/

/-- The Whitney 0-form reconstruction `W0 c = Σ_i c_i λ_i` (piecewise-affine interpolation). -/
def W0 (c : ι → ℝ) (x : E) : ℝ := ∑ i, c i * lam b i x

/-- The de Rham map in degree 0: vertex values. -/
def R0 (f : E → ℝ) : ι → ℝ := fun i => f (b i)

/-- **`R_h W_h = I` in degree 0.** -/
theorem R0_W0 (c : ι → ℝ) : R0 b (W0 b c) = c := by
  funext j
  simp only [R0, W0, lam_vertex, δ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-! ### Degree 1 -/

/-- The Whitney 1-form `w_{ij} = λ_i dλ_j - λ_j dλ_i`. -/
def w1 (i j : ι) (x : E) : E →L[ℝ] ℝ := lam b i x • dlam b j - lam b j x • dlam b i

/-- The Whitney 1-form reconstruction of an oriented 1-cochain (`c_{ji} = -c_{ij}`):
`W1 c = ½ Σ_{i,j} c_{ij} w_{ij} = Σ_{i<j} c_{ij} w_{ij}`. -/
def W1 (c : ι → ι → ℝ) (x : E) : E →L[ℝ] ℝ := (1 / 2 : ℝ) • ∑ i, ∑ j, c i j • w1 b i j x

/-- The oriented edge `t ↦ v_k + t (v_l - v_k)`. -/
def edgePath (k l : ι) (t : ℝ) : E := b k + t • (b l - b k)

/-- The de Rham map in degree 1: line integrals along the oriented edges. -/
def R1 (ω : E → E →L[ℝ] ℝ) (k l : ι) : ℝ :=
  ∫ t in (0 : ℝ)..1, ω (edgePath b k l t) (b l - b k)

/-- The coboundary `d_h : C⁰ → C¹`. -/
def d0 (c : ι → ℝ) : ι → ι → ℝ := fun i j => c j - c i

/-- Oriented (antisymmetric) 1-cochains. -/
def Antisymm (c : ι → ι → ℝ) : Prop := ∀ i j, c j i = -c i j

theorem antisymm_d0 (c : ι → ℝ) : Antisymm (d0 c) := fun i j => by simp [d0]

theorem lam_edgePath (i k l : ι) (t : ℝ) :
    lam b i (edgePath b k l t) = (1 - t) * δ i k + t * δ i l := by
  rw [edgePath, lam_add, map_smul, dlam_vertex_sub, lam_vertex, smul_eq_mul]
  ring

/-- The edge integrand of `w_{ij}` along `[v_k, v_l]` is the constant
`δ_{ik}δ_{jl} - δ_{il}δ_{jk}`. -/
theorem w1_edgePath (i j k l : ι) (t : ℝ) :
    w1 b i j (edgePath b k l t) (b l - b k) = δ i k * δ j l - δ i l * δ j k := by
  simp only [w1, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    lam_edgePath, dlam_vertex_sub]
  ring

/-- **`R_h W_h = I` in degree 1** (Kronecker pairing of Whitney 1-forms with oriented edges). -/
theorem R1_W1 {c : ι → ι → ℝ} (hc : Antisymm c) (k l : ι) : R1 b (W1 b c) k l = c k l := by
  have hconst : ∀ t, W1 b c (edgePath b k l t) (b l - b k) = (1 / 2 : ℝ) * (c k l - c l k) := by
    intro t
    simp only [W1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
      Finset.sum_apply, smul_eq_mul, w1_edgePath, δ]
    congr 1
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      one_mul]
    simp [Finset.sum_ite_eq', Finset.sum_ite_eq]
  rw [R1, intervalIntegral.integral_congr (g := fun _ => (1 / 2 : ℝ) * (c k l - c l k))
    (fun t _ => hconst t), intervalIntegral.integral_const, hc k l]
  simp; ring

/-- **`d W_h = W_h d_h` in degree 0**: the differential of the Whitney 0-form reconstruction is
the Whitney 1-form reconstruction of the coboundary. -/
theorem hasFDerivAt_W0 (c : ι → ℝ) (x : E) : HasFDerivAt (W0 b c) (W1 b (d0 c) x) x := by
  have hd : HasFDerivAt (fun y => ∑ i, c i * lam b i y) (∑ i, c i • dlam b i) x :=
    HasFDerivAt.fun_sum fun i _ => (hasFDerivAt_lam b i x).const_mul (c i)
  have heq : (∑ i, c i • dlam b i) = W1 b (d0 c) x := by
    ext v
    simp only [W1, d0, w1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
      Finset.sum_apply, smul_eq_mul, ContinuousLinearMap.sub_apply]
    set a : ι → ℝ := fun i => dlam b i v
    set lx : ι → ℝ := fun i => lam b i x
    have hl : ∑ i, lx i = 1 := sum_lam b x
    have ha : ∑ i, a i = 0 := sum_dlam b v
    have e : ∀ i j, (c j - c i) * (lam b i x * dlam b j v - lam b j x * dlam b i v) =
        lx i * (c j * a j) - a i * (c j * lx j) - (c i * lx i) * a j + (c i * a i) * lx j :=
      fun i j => by simp only [lx, a]; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul_sum, hl, ha]
    simp only [a]
    ring
  rw [← heq]
  exact hd

theorem fderiv_W0 (c : ι → ℝ) (x : E) : fderiv ℝ (W0 b c) x = W1 b (d0 c) x :=
  (hasFDerivAt_W0 b c x).fderiv

/-- **`R_h d = d_h R_h`** on `C¹` functions (fundamental theorem of calculus on the edges). -/
theorem R1_fderiv {f : E → ℝ} (hf : ContDiff ℝ 1 f) (k l : ι) :
    R1 b (fderiv ℝ f) k l = d0 (R0 b f) k l := by
  have hdf : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hγ : ∀ t, HasDerivAt (edgePath b k l) (b l - b k) t := fun t => by
    have := ((hasDerivAt_id t).smul_const (b l - b k)).const_add (b k)
    simp only [id, one_smul] at this
    exact this
  have hd : ∀ t, HasDerivAt (fun t => f (edgePath b k l t))
      (fderiv ℝ f (edgePath b k l t) (b l - b k)) t := fun t =>
    (hdf _).hasFDerivAt.comp_hasDerivAt t (hγ t)
  have hcont : Continuous fun t => fderiv ℝ f (edgePath b k l t) (b l - b k) :=
    ((hf.continuous_fderiv (by norm_num)).comp (continuous_const.add
      (continuous_id.smul continuous_const))).clm_apply continuous_const
  rw [R1, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hcont.intervalIntegrable 0 1)]
  simp [d0, R0, edgePath]

/-- Injectivity of the reconstruction (from `R_h W_h = I`). -/
theorem W1_injective {c c' : ι → ι → ℝ} (hc : Antisymm c) (hc' : Antisymm c')
    (h : W1 b c = W1 b c') : c = c' := by
  funext k l
  rw [← R1_W1 b hc k l, ← R1_W1 b hc' k l, h]

/-! ### Positivity of the comparison mass norms -/

/-- The closed simplex `S = conv(v_i)`. -/
def simplex : Set E := convexHull ℝ (range b)

theorem isCompact_simplex : IsCompact (simplex b) :=
  (Set.finite_range b).isCompact_convexHull (𝕜 := ℝ)

theorem interior_simplex_nonempty : (interior (simplex b)).Nonempty :=
  interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr b.tot

theorem closure_interior_simplex : closure (interior (simplex b)) = simplex b := by
  have h1 := interior_simplex_nonempty b
  have h2 := isCompact_simplex b
  unfold simplex at *
  rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
    h1, h2.isClosed.closure_eq]

theorem edgePath_mem (k l : ι) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    edgePath b k l t ∈ simplex b := by
  refine segment_subset_convexHull (mem_range_self k) (mem_range_self l) ?_
  refine ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, ?_⟩
  simp only [edgePath, smul_sub, sub_smul, one_smul]
  abel

theorem continuous_W0 (c : ι → ℝ) : Continuous (W0 b c) := by
  have hl := continuous_lam b
  unfold W0; fun_prop

theorem continuous_W1 (c : ι → ι → ℝ) : Continuous (W1 b c) := by
  have hl := continuous_lam b
  unfold W1 w1; fun_prop

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A continuous function vanishing nowhere on a nonempty open subset of `S` has positive mass. -/
theorem pos_of_ne_zero_on_interior {F : Type*} [NormedAddCommGroup F] {g : E → F}
    (hg : Continuous g) (h : ∃ p ∈ interior (simplex b), g p ≠ 0) :
    0 < ∫ x in simplex b, ‖g x‖ ^ 2 ∂μ := by
  obtain ⟨p, hp, hgp⟩ := h
  have hint : IntegrableOn (fun x => ‖g x‖ ^ 2) (simplex b) μ :=
    (hg.norm.pow 2).continuousOn.integrableOn_compact (isCompact_simplex b)
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun x => by positivity) hint]
  set U := {x | g x ≠ 0} ∩ interior (simplex b)
  have hU : IsOpen U := (isOpen_ne_fun hg continuous_const).inter isOpen_interior
  have hUne : U.Nonempty := ⟨p, hgp, hp⟩
  refine lt_of_lt_of_le (hU.measure_pos μ hUne) (measure_mono fun x hx => ⟨?_, ?_⟩)
  · simp only [Function.mem_support]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx.1)
  · exact interior_subset hx.2

/-- **Positivity of the degree-0 comparison norm**: `c ≠ 0 → ∫_S |W0 c|² > 0`. -/
theorem mass0_pos {c : ι → ℝ} (hc : c ≠ 0) : 0 < ∫ x in simplex b, ‖W0 b c x‖ ^ 2 ∂μ := by
  refine pos_of_ne_zero_on_interior b μ (continuous_W0 b c) ?_
  by_contra hcon
  push_neg at hcon
  have hS : ∀ x ∈ simplex b, W0 b c x = 0 := by
    have hcl : IsClosed {x | W0 b c x = 0} := isClosed_eq (continuous_W0 b c) continuous_const
    intro x hx
    rw [← closure_interior_simplex] at hx
    exact (hcl.closure_subset_iff.mpr hcon) hx
  apply hc
  rw [← R0_W0 b c]
  funext i
  exact hS _ (subset_convexHull ℝ _ (mem_range_self i))

/-- **Positivity of the degree-1 comparison norm (the mass matrix is positive definite)**:
for a nonzero oriented 1-cochain, `∫_S ‖W1 c‖² > 0`. -/
theorem mass1_pos {c : ι → ι → ℝ} (hc : Antisymm c) (hne : c ≠ 0) :
    0 < ∫ x in simplex b, ‖W1 b c x‖ ^ 2 ∂μ := by
  refine pos_of_ne_zero_on_interior b μ (continuous_W1 b c) ?_
  by_contra hcon
  push_neg at hcon
  have hS : ∀ x ∈ simplex b, W1 b c x = 0 := by
    have hcl : IsClosed {x | W1 b c x = 0} := isClosed_eq (continuous_W1 b c) continuous_const
    intro x hx
    rw [← closure_interior_simplex] at hx
    exact (hcl.closure_subset_iff.mpr hcon) hx
  apply hne
  funext k l
  rw [← R1_W1 b hc k l, R1, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))
    (fun t ht => by
      rw [uIcc_of_le zero_le_one] at ht
      simp [hS _ (edgePath_mem b k l ht)])]
  simp

/-- Non-vacuity: every finite-dimensional space carries a nondegenerate simplex, and the
coboundary of a nonconstant vertex function has positive Whitney mass on it. -/
example : ∃ b : AffineBasis (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + 1)) ℝ
    (EuclideanSpace ℝ (Fin 2)), 0 < ∫ x in simplex b,
      ‖W1 b (d0 fun i => if i = 0 then (1 : ℝ) else 0) x‖ ^ 2 := by
  obtain ⟨b, -, -⟩ := exists_mem_interior_convexHull_affineBasis
    (Filter.univ_mem (f := nhds (0 : EuclideanSpace ℝ (Fin 2))))
  refine ⟨b, mass1_pos b volume (antisymm_d0 _) fun h => ?_⟩
  have := congrFun (congrFun h 0) 1
  simp [d0] at this

end WhitneyLow
end RenewalGeometry
