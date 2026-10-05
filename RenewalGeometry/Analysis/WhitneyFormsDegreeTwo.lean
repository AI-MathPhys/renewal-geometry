/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.WhitneyFormsLowDegree

/-!
# Whitney 2-forms on a simplex and the commuting identity in degree 1
  (`lem:Whitney`, local part, `k = 2`)

Einstein–Standard-Model action-closure manuscript, `eq:Whitney` for `k = 2` and `lem:Whitney`
("Commuting reconstruction and positive comparison norm"), on one nondegenerate simplex
`S = conv(v₀, …, v_n)` of a finite-dimensional real inner product space (continuing
`WhitneyFormsLowDegree`, whose barycentric coordinates `λ_i`, `dλ_i`, Whitney 1-forms `W1` and
coboundary `d0` are reused):

* 2-forms are alternating bilinear maps `E →L E →L ℝ`; `wedge α β = α ⊗ β - β ⊗ α`;
* `w2 i j k = 2(λ_i dλ_j∧dλ_k - λ_j dλ_i∧dλ_k + λ_k dλ_i∧dλ_j)` (`eq:Whitney`, `k = 2`, `2! = 2`)
  and `W2 φ = (1/3!) Σ_{i,j,k} φ_{ijk} w_{ijk} = Σ_{i<j<k} φ_{ijk} w_{ijk}` on alternating
  2-cochains;
* `extDeriv1`: the exterior derivative `dω(u, v) = Dω(u)(v) - Dω(v)(u)` of a 1-form field;
* the de Rham map `R2 ω (a, b, c) = ∫_{T₂} ω(v_a + s e₁ + t e₂)(e₁, e₂) ds dt`
  (`e₁ = v_b - v_a`, `e₂ = v_c - v_a`, `T₂` the open standard triangle) and the coboundary
  `d1 c (i, j, k) = c_{jk} - c_{ik} + c_{ij}`;
* `R2_W2`: **`R_h W_h = I` in degree 2** (the pullback of `W2 φ` to the oriented triangle
  `[v_a, v_b, v_c]` is the constant `2 φ_{abc}` and `|T₂| = ½`);
* `extDeriv1_W1`: **`d W_h = W_h d_h` in degree 1** (`d(W1 c) = W2 (d1 c)`, from `Σ λ_i = 1`,
  `Σ dλ_i = 0`); with `extDeriv1_W1_d0` (`d d = 0` on reconstructions);
* `W2_injective`, `mass2_pos`: the degree-2 comparison norm `∫_S ‖W2 φ‖²` is positive definite
  on nonzero alternating 2-cochains (reference mass matrix positive definite);
* `W1_trace_local`, `W2_trace_local`: **trace locality** — on a face spanned by a vertex set
  `F` (points with `λ_i = 0` and tangent vectors with `dλ_i = 0` for `i ∉ F`) the Whitney
  reconstructions only see the cochain values on `F`;
* `W1_facePt`, `W2_facePt` (explicit trace formulas in face coordinates) and
  **`W0_conforming`, `W1_conforming`, `W2_conforming`**: two simplices (two affine bases)
  sharing the vertices of a face, with cochains agreeing on that face, have Whitney
  reconstructions with the same value (`k = 0`) / tangential trace (`k = 1, 2`) on the face —
  the inter-element conformity used by the mesh assembly.

Not covered (disclosed): degrees `k = 3, 4`, the global mesh object and the distributional
identity `d W_h = W_h d_h` across faces (only its two ingredients, the cellwise identity and
the tangential conformity, are proved), the shape-regular scaling constants and the strong
convergence `P_h^k → I`.

The 2-form comparison norm is the operator norm of `E →L E →L ℝ` (equivalent, in finite
dimension, to the Hilbert norm of `Λ²E*`).
-/

open MeasureTheory Set

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace WhitneyTwo

open WhitneyLow

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (b : AffineBasis ι ℝ E)

/-! ### 2-forms -/

/-- The wedge product of two 1-forms, `(α ∧ β)(u, v) = α(u)β(v) - β(u)α(v)`. -/
def wedge (α β : E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ := α.smulRight β - β.smulRight α

@[simp] theorem wedge_apply (α β : E →L[ℝ] ℝ) (u v : E) :
    wedge α β u v = α u * β v - β u * α v := by
  simp [wedge, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- The Whitney 2-form `w_{ijk} = 2(λ_i dλ_j∧dλ_k - λ_j dλ_i∧dλ_k + λ_k dλ_i∧dλ_j)`. -/
def w2 (i j k : ι) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (2 : ℝ) • (lam b i x • wedge (dlam b j) (dlam b k) - lam b j x • wedge (dlam b i) (dlam b k) +
    lam b k x • wedge (dlam b i) (dlam b j))

/-- Alternating 2-cochains. -/
def Alt3 (φ : ι → ι → ι → ℝ) : Prop :=
  (∀ i j k, φ j i k = -φ i j k) ∧ (∀ i j k, φ i k j = -φ i j k)

/-- The Whitney reconstruction of a 2-cochain, `W2 φ = (1/3!) Σ_{i,j,k} φ_{ijk} w_{ijk}`. -/
def W2 (φ : ι → ι → ι → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 6 : ℝ) • ∑ i, ∑ j, ∑ k, φ i j k • w2 b i j k x

/-- The coboundary `d_h : C¹ → C²`, `(d1 c)_{ijk} = c_{jk} - c_{ik} + c_{ij}`. -/
def d1 (c : ι → ι → ℝ) : ι → ι → ι → ℝ := fun i j k => c j k - c i k + c i j

theorem alt3_d1 {c : ι → ι → ℝ} (hc : Antisymm c) : Alt3 (d1 c) := by
  refine ⟨fun i j k => ?_, fun i j k => ?_⟩
  · simp only [d1]; rw [hc i j]; ring
  · simp only [d1]; rw [hc j k, hc k j]; ring

/-- `d_h d_h = 0`: `d1 (d0 f) = 0`. -/
theorem d1_d0 (f : ι → ℝ) : d1 (d0 f) = 0 := by
  funext i j k; simp only [d1, d0, Pi.zero_apply]; ring

theorem alt3_self₁ {φ : ι → ι → ι → ℝ} (hφ : Alt3 φ) (i k : ι) : φ i i k = 0 := by
  have := hφ.1 i i k; linarith

theorem alt3_self₂ {φ : ι → ι → ι → ℝ} (hφ : Alt3 φ) (i j : ι) : φ i j j = 0 := by
  have := hφ.2 i j j; linarith

theorem alt3_cyc {φ : ι → ι → ι → ℝ} (hφ : Alt3 φ) (i j k : ι) : φ j k i = φ i j k := by
  rw [hφ.2 j i k, hφ.1 i j k, neg_neg]

theorem sum3_swap12 (f : ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ j, ∑ k, f j i k := Finset.sum_comm

theorem sum3_cycle (f : ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ j, ∑ k, f j k i := by
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- `W2 φ` evaluated on two vectors. -/
theorem W2_apply (φ : ι → ι → ι → ℝ) (x u v : E) :
    W2 b φ x u v = (1 / 6) * ∑ i, ∑ j, ∑ k, φ i j k * (2 *
      (lam b i x * (dlam b j u * dlam b k v - dlam b k u * dlam b j v) -
        lam b j x * (dlam b i u * dlam b k v - dlam b k u * dlam b i v) +
        lam b k x * (dlam b i u * dlam b j v - dlam b j u * dlam b i v))) := by
  simp only [W2, w2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, wedge_apply,
    smul_eq_mul]

/-- For an alternating 2-cochain, `W2 φ (u, v) = Σ_{i,j,k} φ_{ijk} λ_i (dλ_j∧dλ_k)(u, v)`. -/
theorem W2_apply_alt {φ : ι → ι → ι → ℝ} (hφ : Alt3 φ) (x u v : E) :
    W2 b φ x u v = ∑ i, ∑ j, ∑ k, φ i j k *
      (lam b i x * (dlam b j u * dlam b k v - dlam b k u * dlam b j v)) := by
  rw [W2_apply]
  set F : ι → ι → ι → ℝ := fun i j k => φ i j k *
    (lam b i x * (dlam b j u * dlam b k v - dlam b k u * dlam b j v)) with hF
  have e2 : ∑ i, ∑ j, ∑ k, φ i j k *
      (lam b j x * (dlam b i u * dlam b k v - dlam b k u * dlam b i v)) =
      -∑ i, ∑ j, ∑ k, F i j k := by
    rw [sum3_swap12]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    simp only [hF, hφ.1 i j k]; ring
  have e3 : ∑ i, ∑ j, ∑ k, φ i j k *
      (lam b k x * (dlam b i u * dlam b j v - dlam b j u * dlam b i v)) =
      ∑ i, ∑ j, ∑ k, F i j k := by
    rw [sum3_cycle]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    simp only [hF, alt3_cyc hφ]
  have hsplit : ∑ i, ∑ j, ∑ k, φ i j k * (2 *
      (lam b i x * (dlam b j u * dlam b k v - dlam b k u * dlam b j v) -
        lam b j x * (dlam b i u * dlam b k v - dlam b k u * dlam b i v) +
        lam b k x * (dlam b i u * dlam b j v - dlam b j u * dlam b i v))) =
      2 * (∑ i, ∑ j, ∑ k, F i j k - ∑ i, ∑ j, ∑ k, φ i j k *
        (lam b j x * (dlam b i u * dlam b k v - dlam b k u * dlam b i v)) +
        ∑ i, ∑ j, ∑ k, φ i j k *
        (lam b k x * (dlam b i u * dlam b j v - dlam b j u * dlam b i v))) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, hF]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsplit, e2, e3]
  ring

/-! ### The exterior derivative of a 1-form field -/

/-- The exterior derivative `dω(x)(u, v) = Dω(x)(u)(v) - Dω(x)(v)(u)` of a 1-form field. -/
def extDeriv1 (ω : E → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ ω x - (fderiv ℝ ω x).flip

theorem extDeriv1_apply (ω : E → E →L[ℝ] ℝ) (x u v : E) :
    extDeriv1 ω x u v = fderiv ℝ ω x u v - fderiv ℝ ω x v u := by
  simp [extDeriv1]

theorem hasFDerivAt_W1 (c : ι → ι → ℝ) (x : E) :
    HasFDerivAt (W1 b c) ((1 / 2 : ℝ) • ∑ i, ∑ j, c i j •
      ((dlam b i).smulRight (dlam b j) - (dlam b j).smulRight (dlam b i))) x := by
  have hw : ∀ i j, HasFDerivAt (w1 b i j)
      ((dlam b i).smulRight (dlam b j) - (dlam b j).smulRight (dlam b i)) x := by
    intro i j
    have h1 : HasFDerivAt (fun y => lam b i y • dlam b j) ((dlam b i).smulRight (dlam b j)) x :=
      (hasFDerivAt_lam b i x).smul_const (dlam b j)
    have h2 : HasFDerivAt (fun y => lam b j y • dlam b i) ((dlam b j).smulRight (dlam b i)) x :=
      (hasFDerivAt_lam b j x).smul_const (dlam b i)
    exact h1.sub h2
  have h : HasFDerivAt (fun y => ∑ i, ∑ j, c i j • w1 b i j y)
      (∑ i, ∑ j, c i j • ((dlam b i).smulRight (dlam b j) - (dlam b j).smulRight (dlam b i))) x :=
    HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => (hw i j).const_smul (c i j)
  show HasFDerivAt (fun y => (1 / 2 : ℝ) • ∑ i, ∑ j, c i j • w1 b i j y) _ x
  exact h.const_smul (1 / 2 : ℝ)

/-- **`d W_h = W_h d_h` in degree 1**: `d(W1 c) = W2(d1 c)` for every oriented 1-cochain. -/
theorem extDeriv1_W1 {c : ι → ι → ℝ} (hc : Antisymm c) (x : E) :
    extDeriv1 (W1 b c) x = W2 b (d1 c) x := by
  ext u v
  rw [extDeriv1_apply, (hasFDerivAt_W1 b c x).fderiv, W2_apply_alt b (alt3_d1 hc)]
  set L : ι → ℝ := fun i => lam b i x
  set a : ι → ℝ := fun i => dlam b i u
  set w : ι → ℝ := fun i => dlam b i v
  have hL : ∑ i, L i = 1 := sum_lam b x
  have ha : ∑ i, a i = 0 := sum_dlam b u
  have hw : ∑ i, w i = 0 := sum_dlam b v
  -- left side: `Σ_{ij} c_{ij} (a_i w_j - a_j w_i)`
  have hlhs : ((1 / 2 : ℝ) • ∑ i, ∑ j, c i j •
      ((dlam b i).smulRight (dlam b j) - (dlam b j).smulRight (dlam b i))) u v -
      ((1 / 2 : ℝ) • ∑ i, ∑ j, c i j •
      ((dlam b i).smulRight (dlam b j) - (dlam b j).smulRight (dlam b i))) v u =
      ∑ i, ∑ j, c i j * (a i * w j - a j * w i) := by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [a, w]; ring
  rw [hlhs]
  -- right side: separate the three coboundary terms
  set X : ι → ι → ℝ := fun j k => a j * w k - a k * w j with hX
  have hXj : ∀ k, ∑ j, X j k = 0 := fun k => by
    simp only [hX, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ha, hw]; ring
  have hXk : ∀ j, ∑ k, X j k = 0 := fun j => by
    simp only [hX, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ha, hw]; ring
  have hsplit : ∑ i, ∑ j, ∑ k, d1 c i j k * (L i * X j k) =
      ∑ i, ∑ j, ∑ k, L i * (c j k * X j k) - ∑ i, ∑ j, ∑ k, c i k * L i * X j k +
        ∑ i, ∑ j, ∑ k, c i j * L i * X j k := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    simp only [d1]; ring
  have h1 : ∑ i, ∑ j, ∑ k, L i * (c j k * X j k) = ∑ j, ∑ k, c j k * X j k := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hL, one_mul]
  have h2 : ∑ i, ∑ j, ∑ k, c i k * L i * X j k = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.mul_sum, hXj k, mul_zero]
  have h3 : ∑ i, ∑ j, ∑ k, c i j * L i * X j k = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.mul_sum, hXk j, mul_zero]
  show ∑ i, ∑ j, c i j * (a i * w j - a j * w i) = ∑ i, ∑ j, ∑ k, d1 c i j k * (L i * X j k)
  rw [hsplit, h1, h2, h3, sub_zero, add_zero]

/-- `d d = 0` on reconstructions: `d(W1 (d0 f)) = 0`. -/
theorem extDeriv1_W1_d0 (f : ι → ℝ) (x : E) : extDeriv1 (W1 b (d0 f)) x = 0 := by
  rw [extDeriv1_W1 b (antisymm_d0 f) x, d1_d0]
  ext u v
  rw [W2_apply]
  simp

/-! ### The de Rham map in degree 2 -/

/-- The open standard triangle `T₂ = {(s, t) : 0 < s, 0 < t, s + t < 1}`. -/
def tri : Set (ℝ × ℝ) := regionBetween (fun _ => (0 : ℝ)) (fun s => 1 - s) (Ioo 0 1)

theorem mem_tri {p : ℝ × ℝ} : p ∈ tri ↔ 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1 := by
  simp only [tri, regionBetween, mem_setOf_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, h3⟩; exact ⟨h1, h2, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩

theorem measurableSet_tri : MeasurableSet tri :=
  measurableSet_regionBetween measurable_const (measurable_const.sub measurable_id)
    measurableSet_Ioo

/-- `|T₂| = ½`. -/
theorem volume_tri : (volume tri).toReal = 1 / 2 := by
  have h := volume_regionBetween_eq_integral (μ := volume) (f := fun _ => (0 : ℝ))
    (g := fun s => 1 - s) (s := Ioo 0 1) (integrableOn_const (by simp))
    ((continuous_const.sub continuous_id).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    measurableSet_Ioo (fun x hx => by simp; linarith [hx.2])
  rw [Measure.volume_eq_prod, tri, h, ENNReal.toReal_ofReal]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    simp only [Pi.sub_apply, sub_zero]
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp [integral_id]
    norm_num
  · refine setIntegral_nonneg measurableSet_Ioo fun x hx => ?_
    simp; linarith [hx.2]

/-- The oriented triangle `(s, t) ↦ v_a + s (v_b - v_a) + t (v_c - v_a)`. -/
def triPoint (a a' a'' : ι) (p : ℝ × ℝ) : E :=
  b a + p.1 • (b a' - b a) + p.2 • (b a'' - b a)

/-- **The de Rham map in degree 2**: integrals over the oriented triangles
`[v_a, v_{a'}, v_{a''}]`. -/
def R2 (ω : E → E →L[ℝ] E →L[ℝ] ℝ) (a a' a'' : ι) : ℝ :=
  ∫ p in tri, ω (triPoint b a a' a'' p) (b a' - b a) (b a'' - b a)

theorem lam_triPoint (i a a' a'' : ι) (p : ℝ × ℝ) :
    lam b i (triPoint b a a' a'' p) = δ i a + p.1 * (δ i a' - δ i a) + p.2 * (δ i a'' - δ i a) := by
  rw [triPoint, lam_add, lam_add, map_smul, map_smul, dlam_vertex_sub, dlam_vertex_sub, lam_vertex,
    smul_eq_mul, smul_eq_mul]

/-- The trilinear form `T(u, v, w) = Σ φ_{ijk} u_i (v_j w_k - v_k w_j)`. -/
def T3 (φ : ι → ι → ι → ℝ) (u v w : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, φ i j k * (u i * (v j * w k - v k * w j))

theorem T3_add₁ (φ : ι → ι → ι → ℝ) (u u' v w : ι → ℝ) :
    T3 φ (u + u') v w = T3 φ u v w + T3 φ u' v w := by
  simp only [T3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply]; ring

theorem T3_smul₁ (φ : ι → ι → ι → ℝ) (r : ℝ) (u v w : ι → ℝ) :
    T3 φ (r • u) v w = r * T3 φ u v w := by
  simp only [T3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem T3_sub₁ (φ : ι → ι → ι → ℝ) (u u' v w : ι → ℝ) :
    T3 φ (u - u') v w = T3 φ u v w - T3 φ u' v w := by
  simp only [T3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.sub_apply]; ring

theorem T3_sub₂ (φ : ι → ι → ι → ℝ) (u v v' w : ι → ℝ) :
    T3 φ u (v - v') w = T3 φ u v w - T3 φ u v' w := by
  simp only [T3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.sub_apply]; ring

theorem T3_sub₃ (φ : ι → ι → ι → ℝ) (u v w w' : ι → ℝ) :
    T3 φ u v (w - w') = T3 φ u v w - T3 φ u v w' := by
  simp only [T3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.sub_apply]; ring

/-- The coordinate vector `e_p = (δ_{ip})_i`. -/
def ev (p : ι) : ι → ℝ := fun i => δ i p

theorem sum3_delta (f : ι → ι → ι → ℝ) (p q r : ι) :
    ∑ i, ∑ j, ∑ k, f i j k * (δ i p * (δ j q * δ k r)) = f p q r := by
  rw [Finset.sum_eq_single p (fun i _ hi => by simp [δ, hi]) (by simp)]
  rw [Finset.sum_eq_single q (fun j _ hj => by simp [δ, hj]) (by simp)]
  rw [Finset.sum_eq_single r (fun k _ hk => by simp [δ, hk]) (by simp)]
  simp [δ]

theorem T3_ev (φ : ι → ι → ι → ℝ) (p q r : ι) :
    T3 φ (ev p) (ev q) (ev r) = φ p q r - φ p r q := by
  have h1 := sum3_delta φ p q r
  have h2 := sum3_delta φ p r q
  have e : T3 φ (ev p) (ev q) (ev r) =
      ∑ i, ∑ j, ∑ k, φ i j k * (δ i p * (δ j q * δ k r)) -
        ∑ i, ∑ j, ∑ k, φ i j k * (δ i p * (δ j r * δ k q)) := by
    simp only [T3, ev, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e, h1, h2]

/-- The pullback of `W2 φ` to an oriented triangle of the simplex is the constant `2 φ_{a a' a''}`. -/
theorem W2_triPoint {φ : ι → ι → ι → ℝ} (hφ : Alt3 φ) (a a' a'' : ι) (p : ℝ × ℝ) :
    W2 b φ (triPoint b a a' a'' p) (b a' - b a) (b a'' - b a) = 2 * φ a a' a'' := by
  rw [W2_apply_alt b hφ]
  have hL : (fun i => lam b i (triPoint b a a' a'' p)) =
      ev a + p.1 • (ev a' - ev a) + p.2 • (ev a'' - ev a) := by
    funext i; rw [lam_triPoint]; simp [ev]
  have hA : (fun j => dlam b j (b a' - b a)) = ev a' - ev a := by
    funext j; rw [dlam_vertex_sub]; simp [ev]
  have hB : (fun k => dlam b k (b a'' - b a)) = ev a'' - ev a := by
    funext k; rw [dlam_vertex_sub]; simp [ev]
  have hT : ∑ i, ∑ j, ∑ k, φ i j k * (lam b i (triPoint b a a' a'' p) *
      (dlam b j (b a' - b a) * dlam b k (b a'' - b a) -
        dlam b k (b a' - b a) * dlam b j (b a'' - b a))) =
      T3 φ (fun i => lam b i (triPoint b a a' a'' p)) (fun j => dlam b j (b a' - b a))
        (fun k => dlam b k (b a'' - b a)) := rfl
  rw [hT, hL, hA, hB, T3_add₁, T3_add₁, T3_smul₁, T3_smul₁, T3_sub₁, T3_sub₁]
  simp only [T3_sub₂, T3_sub₃, T3_ev]
  have z1 : ∀ i k, φ i i k = 0 := alt3_self₁ hφ
  have z2 : ∀ i j, φ i j j = 0 := alt3_self₂ hφ
  have z3 : ∀ i j, φ i j i = 0 := fun i j => by rw [hφ.2 i i j, z1]; simp
  have s1 : φ a a'' a' = -φ a a' a'' := hφ.2 a a' a''
  have s2 : φ a' a a'' = -φ a a' a'' := hφ.1 a a' a''
  have s3 : φ a' a'' a = φ a a' a'' := alt3_cyc hφ a a' a''
  have s4 : φ a'' a a' = φ a a' a'' := by rw [alt3_cyc hφ a' a'' a, alt3_cyc hφ a a' a'']
  have s5 : φ a'' a' a = -φ a a' a'' := by rw [hφ.2 a'' a a', s4]
  have s6 : φ a' a a' = 0 := z3 a' a
  simp only [z1, z2, z3, s1, s2, s3, s4, s5]
  ring

/-- **`R_h W_h = I` in degree 2** (Kronecker pairing of Whitney 2-forms with oriented triangles). -/
theorem R2_W2 {φ : ι → ι → ι → ℝ} (hφ : Alt3 φ) (a a' a'' : ι) :
    R2 b (W2 b φ) a a' a'' = φ a a' a'' := by
  rw [R2, setIntegral_congr_fun measurableSet_tri (fun p _ => W2_triPoint b hφ a a' a'' p),
    setIntegral_const, smul_eq_mul, Measure.real, volume_tri]
  ring

theorem W2_injective {φ φ' : ι → ι → ι → ℝ} (hφ : Alt3 φ) (hφ' : Alt3 φ')
    (h : W2 b φ = W2 b φ') : φ = φ' := by
  funext i j k
  rw [← R2_W2 b hφ i j k, ← R2_W2 b hφ' i j k, h]

/-! ### Positivity of the degree-2 comparison norm -/

theorem continuous_W2 (φ : ι → ι → ι → ℝ) : Continuous (W2 b φ) := by
  refine continuous_clm_apply.mpr fun u => continuous_clm_apply.mpr fun v => ?_
  have hl := continuous_lam b
  simp only [W2_apply]
  fun_prop

theorem triPoint_mem (a a' a'' : ι) {p : ℝ × ℝ} (hp : p ∈ tri) :
    triPoint b a a' a'' p ∈ simplex b := by
  rw [mem_tri] at hp
  rw [simplex, b.convexHull_eq_nonneg_coord]
  intro i
  have := lam_triPoint b i a a' a'' p
  simp only [lam] at this
  rw [this]
  simp only [δ]
  split_ifs <;> nlinarith [hp.1, hp.2.1, hp.2.2]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Positivity of the degree-2 comparison norm (the reference mass matrix is positive
definite)**: for a nonzero alternating 2-cochain, `∫_S ‖W2 φ‖² > 0`. -/
theorem mass2_pos {φ : ι → ι → ι → ℝ} (hφ : Alt3 φ) (hne : φ ≠ 0) :
    0 < ∫ x in simplex b, ‖W2 b φ x‖ ^ 2 ∂μ := by
  refine pos_of_ne_zero_on_interior (F := E →L[ℝ] E →L[ℝ] ℝ) b μ (continuous_W2 b φ) ?_
  by_contra hcon
  push_neg at hcon
  have hS : ∀ x ∈ simplex b, W2 b φ x = 0 := by
    have hcl : IsClosed {x | W2 b φ x = 0} := isClosed_eq (continuous_W2 b φ) continuous_const
    intro x hx
    rw [← closure_interior_simplex] at hx
    exact (hcl.closure_subset_iff.mpr hcon) hx
  apply hne
  funext i j k
  rw [← R2_W2 b hφ i j k, R2, setIntegral_congr_fun measurableSet_tri (g := fun _ => (0 : ℝ))
    (fun p hp => by simp [hS _ (triPoint_mem b i j k hp)])]
  simp

/-! ### Conformity: trace locality on faces -/

/-- **Trace locality in degree 1**: at a point of the face spanned by `F` (all barycentric
coordinates outside `F` vanish) and along a tangent vector of that face, `W1 c` only depends on
the values of the cochain on `F`. -/
theorem W1_trace_local (F : Finset ι) {c c' : ι → ι → ℝ}
    (hcc : ∀ i ∈ F, ∀ j ∈ F, c i j = c' i j) {x u : E} (hx : ∀ i ∉ F, lam b i x = 0)
    (hu : ∀ i ∉ F, dlam b i u = 0) : W1 b c x u = W1 b c' x u := by
  simp only [W1, w1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : i ∈ F
  · by_cases hj : j ∈ F
    · rw [hcc i hi j hj]
    · simp [hx j hj, hu j hj]
  · simp [hx i hi, hu i hi]

/-- **Trace locality in degree 2**: on the face spanned by `F`, along two tangent vectors of the
face, `W2 φ` only depends on the values of the cochain on `F`. -/
theorem W2_trace_local (F : Finset ι) {φ φ' : ι → ι → ι → ℝ}
    (hφφ : ∀ i ∈ F, ∀ j ∈ F, ∀ k ∈ F, φ i j k = φ' i j k) {x u v : E}
    (hx : ∀ i ∉ F, lam b i x = 0) (hu : ∀ i ∉ F, dlam b i u = 0)
    (hv : ∀ i ∉ F, dlam b i v = 0) : W2 b φ x u v = W2 b φ' x u v := by
  rw [W2_apply, W2_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  by_cases hi : i ∈ F
  · by_cases hj : j ∈ F
    · by_cases hk : k ∈ F
      · rw [hφφ i hi j hj k hk]
      · simp [hx k hk, hu k hk, hv k hk]
    · simp [hx j hj, hu j hj, hv j hj]
  · simp [hx i hi, hu i hi, hv i hi]

/-- The triangle `[v_a, v_{a'}, v_{a''}]` lies in the face spanned by `{a, a', a''}`. -/
theorem triPoint_face (a a' a'' : ι) (p : ℝ × ℝ) :
    (∀ i ∉ ({a, a', a''} : Finset ι), lam b i (triPoint b a a' a'' p) = 0) ∧
      (∀ i ∉ ({a, a', a''} : Finset ι), dlam b i (b a' - b a) = 0) ∧
      (∀ i ∉ ({a, a', a''} : Finset ι), dlam b i (b a'' - b a) = 0) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi <;>
    simp [lam_triPoint, dlam_vertex_sub, δ, hi.1, hi.2.1, hi.2.2]

/-! ### Conformity across shared faces (inter-element tangential continuity) -/

section Conforming

variable {F : Type*} [Fintype F]

/-- Extension by zero of face weights `w : F → ℝ` along a vertex labelling `f : F → ι`. -/
def ext (f : F → ι) (w : F → ℝ) : ι → ℝ := fun i => ∑ p, if f p = i then w p else 0

theorem sum_mul_ext {f : F → ι} (hf : Function.Injective f) (g : ι → ℝ) (w : F → ℝ) :
    ∑ i, g i * ext f w i = ∑ p, g (f p) * w p := by
  simp only [ext, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem sum_ext {f : F → ι} (hf : Function.Injective f) (w : F → ℝ) :
    ∑ i, ext f w i = ∑ p, w p := by
  have := sum_mul_ext hf (fun _ => (1 : ℝ)) w
  simpa using this

theorem ext_add (f : F → ι) (w t : F → ℝ) : ext f (w + t) = ext f w + ext f t := by
  funext i; simp only [ext, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp

/-- The face point (or face vector) `Σ_p w_p v_{f p}`. -/
def facePt (f : F → ι) (w : F → ℝ) : E := ∑ p, w p • b (f p)

theorem facePt_eq {f : F → ι} (hf : Function.Injective f) (w : F → ℝ) :
    facePt b f w = ∑ i, ext f w i • b i := by
  simp only [facePt, ext, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]
  simp

/-- Barycentric coordinates of a face point: `λ_i(x) = w_p` for `i = f p`, `0` off the face. -/
theorem lam_facePt {f : F → ι} (hf : Function.Injective f) {w : F → ℝ} (hw : ∑ p, w p = 1)
    (i : ι) : lam b i (facePt b f w) = ext f w i := by
  have hW : ∑ i, ext f w i = 1 := (sum_ext hf w).trans hw
  rw [facePt_eq b hf, ← Finset.univ.affineCombination_eq_linear_combination _ _ hW, lam]
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hW

/-- Differentials along a face vector `u = Σ_p t_p v_{f p}` (`Σ t = 0`): `dλ_i(u) = t_p` for
`i = f p`, `0` off the face. -/
theorem dlam_faceVec {f : F → ι} (hf : Function.Injective f) {w t : F → ℝ} (hw : ∑ p, w p = 1)
    (ht : ∑ p, t p = 0) (i : ι) : dlam b i (facePt b f t) = ext f t i := by
  have hwt : ∑ p, (w + t) p = 1 := by simp [Finset.sum_add_distrib, hw, ht]
  have h1 := lam_facePt b hf hwt i
  have h2 := lam_facePt b hf hw i
  have hsplit : facePt b f (w + t) = facePt b f w + facePt b f t := by
    simp only [facePt, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  rw [hsplit, lam_add, h2, ext_add] at h1
  simp only [Pi.add_apply] at h1
  linarith

/-- **Trace formula in degree 1**: the tangential trace of `W1 c` on the face labelled by `f`
is `Σ_{p,q} c_{f p, f q} w_p t_q` — it only depends on the cochain on the face and on the
face coordinates. -/
theorem W1_facePt {f : F → ι} (hf : Function.Injective f) {c : ι → ι → ℝ} (hc : Antisymm c)
    {w t : F → ℝ} (hw : ∑ p, w p = 1) (ht : ∑ p, t p = 0) :
    W1 b c (facePt b f w) (facePt b f t) = ∑ p, ∑ q, c (f p) (f q) * (w p * t q) := by
  simp only [W1, w1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.sub_apply, smul_eq_mul, lam_facePt b hf hw,
    dlam_faceVec b hf hw ht]
  have hsym : ∑ i, ∑ j, c i j * (ext f w j * ext f t i) =
      -∑ i, ∑ j, c i j * (ext f w i * ext f t j) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc j i]; ring
  have hmain : ∑ i, ∑ j, c i j * (ext f w i * ext f t j) =
      ∑ p, ∑ q, c (f p) (f q) * (w p * t q) := by
    calc ∑ i, ∑ j, c i j * (ext f w i * ext f t j)
        = ∑ i, ∑ q, c i (f q) * ext f w i * t q := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← sum_mul_ext hf (fun j => c i j * ext f w i) t]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ q, ∑ i, (c i (f q) * t q) * ext f w i := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ q, ∑ p, (c (f p) (f q) * t q) * w p := by
          exact Finset.sum_congr rfl fun q _ => sum_mul_ext hf (fun i => c i (f q) * t q) w
      _ = ∑ p, ∑ q, c (f p) (f q) * (w p * t q) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  have hsplit : ∑ i, ∑ j, c i j * (ext f w i * ext f t j - ext f w j * ext f t i) =
      ∑ i, ∑ j, c i j * (ext f w i * ext f t j) -
        ∑ i, ∑ j, c i j * (ext f w j * ext f t i) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsplit, hsym, hmain]
  ring

/-- **Conformity in degree 1**: two simplices (affine bases `b`, `b'`) sharing the vertices of a
face (`b (f p) = b' (f' p)`), with oriented cochains agreeing on that face, have Whitney
reconstructions with the same tangential trace on the face. -/
theorem W1_conforming {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b' : AffineBasis ι' ℝ E)
    {f : F → ι} {f' : F → ι'} (hf : Function.Injective f) (hf' : Function.Injective f')
    (hv : ∀ p, b (f p) = b' (f' p)) {c : ι → ι → ℝ} {c' : ι' → ι' → ℝ} (hc : Antisymm c)
    (hc' : Antisymm c') (hcc : ∀ p q, c (f p) (f q) = c' (f' p) (f' q)) {w t : F → ℝ}
    (hw : ∑ p, w p = 1) (ht : ∑ p, t p = 0) :
    facePt b f w = facePt b' f' w ∧ facePt b f t = facePt b' f' t ∧
      W1 b c (facePt b f w) (facePt b f t) = W1 b' c' (facePt b' f' w) (facePt b' f' t) := by
  have hpt : ∀ s : F → ℝ, facePt b f s = facePt b' f' s := fun s => by
    simp only [facePt, hv]
  refine ⟨hpt w, hpt t, ?_⟩
  rw [W1_facePt b hf hc hw ht, W1_facePt b' hf' hc' hw ht]
  simp only [hcc]

/-- Reindexing a triple sum against extended face weights. -/
theorem sum3_ext {f : F → ι} (hf : Function.Injective f) (g : ι → ι → ι → ℝ) (w t s : F → ℝ) :
    ∑ i, ∑ j, ∑ k, g i j k * (ext f w i * (ext f t j * ext f s k)) =
      ∑ p, ∑ q, ∑ r, g (f p) (f q) (f r) * (w p * (t q * s r)) := by
  calc ∑ i, ∑ j, ∑ k, g i j k * (ext f w i * (ext f t j * ext f s k))
      = ∑ i, ∑ j, ∑ r, (g i j (f r) * ext f w i * ext f t j) * s r := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [← sum_mul_ext hf (fun k => g i j k * ext f w i * ext f t j) s]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ i, ∑ q, ∑ r, (g i (f q) (f r) * ext f w i * s r) * t q := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        rw [Finset.sum_comm (f := fun q r => (g i (f q) (f r) * ext f w i * s r) * t q)]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← sum_mul_ext hf (fun j => g i j (f r) * ext f w i * s r) t]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, (∑ q, ∑ r, g i (f q) (f r) * (t q * s r)) * ext f w i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun r _ => by ring
    _ = ∑ p, (∑ q, ∑ r, g (f p) (f q) (f r) * (t q * s r)) * w p :=
        sum_mul_ext hf (fun i => ∑ q, ∑ r, g i (f q) (f r) * (t q * s r)) w
    _ = ∑ p, ∑ q, ∑ r, g (f p) (f q) (f r) * (w p * (t q * s r)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun r _ => by ring

/-- **Trace formula in degree 2**: the tangential trace of `W2 φ` on the face labelled by `f` is
`Σ_{p,q,r} φ_{f p, f q, f r} w_p (t_q s_r - t_r s_q)`. -/
theorem W2_facePt {f : F → ι} (hf : Function.Injective f) {φ : ι → ι → ι → ℝ} (hφ : Alt3 φ)
    {w t s : F → ℝ} (hw : ∑ p, w p = 1) (ht : ∑ p, t p = 0) (hs : ∑ p, s p = 0) :
    W2 b φ (facePt b f w) (facePt b f t) (facePt b f s) =
      ∑ p, ∑ q, ∑ r, φ (f p) (f q) (f r) * (w p * (t q * s r - t r * s q)) := by
  rw [W2_apply_alt b hφ]
  simp only [lam_facePt b hf hw, dlam_faceVec b hf hw ht, dlam_faceVec b hf hw hs]
  have hsplit : ∑ i, ∑ j, ∑ k, φ i j k *
      (ext f w i * (ext f t j * ext f s k - ext f t k * ext f s j)) =
      ∑ i, ∑ j, ∑ k, φ i j k * (ext f w i * (ext f t j * ext f s k)) -
        ∑ i, ∑ j, ∑ k, φ i j k * (ext f w i * (ext f s j * ext f t k)) := by
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsplit, sum3_ext hf, sum3_ext hf, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **Conformity in degree 2**: two simplices sharing a face, with alternating 2-cochains agreeing
on it, have Whitney 2-form reconstructions with the same tangential trace on the face. -/
theorem W2_conforming {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b' : AffineBasis ι' ℝ E)
    {f : F → ι} {f' : F → ι'} (hf : Function.Injective f) (hf' : Function.Injective f')
    (hv : ∀ p, b (f p) = b' (f' p)) {φ : ι → ι → ι → ℝ} {φ' : ι' → ι' → ι' → ℝ} (hφ : Alt3 φ)
    (hφ' : Alt3 φ') (hφφ : ∀ p q r, φ (f p) (f q) (f r) = φ' (f' p) (f' q) (f' r))
    {w t s : F → ℝ} (hw : ∑ p, w p = 1) (ht : ∑ p, t p = 0) (hs : ∑ p, s p = 0) :
    W2 b φ (facePt b f w) (facePt b f t) (facePt b f s) =
      W2 b' φ' (facePt b' f' w) (facePt b' f' t) (facePt b' f' s) := by
  rw [W2_facePt b hf hφ hw ht hs, W2_facePt b' hf' hφ' hw ht hs]
  simp only [hφφ]

/-- **Continuity of the degree-0 reconstruction across shared faces.** -/
theorem W0_conforming {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b' : AffineBasis ι' ℝ E)
    {f : F → ι} {f' : F → ι'} (hf : Function.Injective f) (hf' : Function.Injective f')
    (hv : ∀ p, b (f p) = b' (f' p)) {c : ι → ℝ} {c' : ι' → ℝ} (hcc : ∀ p, c (f p) = c' (f' p))
    {w : F → ℝ} (hw : ∑ p, w p = 1) :
    W0 b c (facePt b f w) = W0 b' c' (facePt b' f' w) := by
  have hpt : facePt b f w = facePt b' f' w := by simp only [facePt, hv]
  rw [← hpt]
  simp only [W0, lam_facePt b hf hw]
  rw [show (fun i => c i * ext f w i) = fun i => c i * ext f w i from rfl, sum_mul_ext hf c w]
  rw [hpt]
  simp only [lam_facePt b' hf' hw]
  rw [sum_mul_ext hf' c' w]
  simp only [hcc]

end Conforming

/-- Non-vacuity: on every nondegenerate triangle (three vertices), the Whitney reconstruction
of the coboundary of the oriented edge cochain `c₀₁ = 1` has positive mass. -/
example (b : AffineBasis (Fin 3) ℝ E) :
    0 < ∫ x in simplex b,
      ‖W2 b (d1 (fun i j : Fin 3 => if i = 0 ∧ j = 1 then (1 : ℝ) else
        if i = 1 ∧ j = 0 then -1 else 0)) x‖ ^ 2 ∂μ := by
  refine mass2_pos b μ (alt3_d1 fun i j => ?_) fun h => ?_
  · fin_cases i <;> fin_cases j <;> simp
  · have := congrFun (congrFun (congrFun h 0) 1) 2
    simp [d1] at this

end WhitneyTwo
end RenewalGeometry
