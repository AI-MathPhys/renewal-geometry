/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.WhitneyFormsDegreeTwo

/-!
# Whitney forms of every degree on a simplex and on a simplicial mesh (`lem:Whitney`)

Einstein–Standard-Model action-closure manuscript, `eq:Whitney` and `lem:Whitney` ("Commuting
reconstruction and positive comparison norm").  This file extends `WhitneyFormsLowDegree.lean`
(`k = 0, 1`) and `WhitneyFormsDegreeTwo.lean` (`k = 2`) to **every degree `k`** (in particular the
degrees `3, 4` of the paper's 4D mesh), on one nondegenerate simplex `S = conv(v_ι)` of a
finite-dimensional real inner product space (affine basis `b`, barycentric coordinates `λ_i`), and
assembles the **global mesh object**.

* `stdSimp k`, `volume_stdSimp`: the standard simplex `Δ_k = {t ≥ 0, Σ t ≤ 1}` has volume `1/k!`
  (Fubini induction).
* `wedgeL`: `f₀ ∧ ⋯ ∧ f_{m-1}` as a continuous alternating map, `(v_q) ↦ det(f_p(v_q))`.
* `whit k i`: the Whitney form `w_i = k! Σ_j (-1)^j λ_{i_j} dλ_{i₀} ∧ ⋯ ∧ (dλ_{i_j} omitted) ∧ ⋯ ∧
  dλ_{i_k}` of `eq:Whitney` (values: `whit_apply`, `k!` times the barycentric determinant);
  `W k c = (1/(k+1)!) Σ_i c_i w_i` on cochains indexed by all vertex tuples, alternating cochains
  `IsAlt` (`= Σ_{i₀<⋯<i_k} c_i w_i`).
* `R k α a = ∫_{Δ_k} α(φ_a(t))(v_{a₁} - v_{a₀}, …)`: the de Rham map (integral over the oriented
  face `[a₀, …, a_k]`).
* **`R_W`: `R_h W_h = I` in every degree** (the pullback of `W c` to the face `a` is the constant
  `k! c_a`, `W_faceMap`: barycentric matrix = incidence matrix × unimodular transition matrix,
  `baryMat_faceMap`, `det_transMat`, and `Σ_i c_i det[i_p = a_r] = (k+1)! c_a`, `sum_mul_det_incMat`).
* **`extDeriv_W`: `d W_h = W_h d_h` in every degree**, with Mathlib's exterior derivative `extDeriv`
  and the simplicial coboundary `dCoch` (`(dc)_m = Σ_j (-1)^j c(m without m_j)`), from Laplace
  expansions and `Σ λ_l = 1`, `Σ dλ_l = 0`.
* `mass_pos`, `W_injective`: the comparison norm `∫_S ‖W c‖²` is positive definite on alternating
  cochains (the reference mass matrix is positive definite), in every degree.
* `W_facePt`, `W_conforming`: the trace formula and **inter-element conformity in every degree**:
  two simplices sharing a face, with cochains agreeing on it, have Whitney reconstructions with the
  same tangential trace on the face.
* **Global mesh** (`WhitneyMesh`): finitely many vertices with positions, finitely many cells (affine
  simplices on `n+1` distinct vertices) with the shared-face condition and disjoint open cells;
  global cochains, the global de Rham map `RG`, the cellwise reconstruction `WCell`, the global
  reconstruction `WG` (cellwise on the open cells); `RG_WCell` (global `R_h W_h = I`),
  `WCell_conforming` (global tangential conformity), `extDeriv_WG` (global `d W_h = W_h d_h` on the
  open cells, a full-measure set).

Not covered (disclosed): the shape-regular cellwise scaling constants of the mass matrices, the
strong convergence `P_h^k → I` of the orthogonal projections (equivalently of `W_h R_h α → α` for
smooth `α` plus density), and the distributional form of `d W_h = W_h d_h` across faces (its two
ingredients, the cellwise identity and tangential conformity, are proved).  Comparison norms are
operator norms of alternating maps (equivalent in finite dimension to the Hilbert norms of `Λ^k E*`).
-/

open MeasureTheory Set Finset Filter Topology
open scoped Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace WhitneyGen

/-! ### The standard simplex and its volume -/

/-- The standard `k`-simplex `Δ_k = {t ∈ ℝ^k : t ≥ 0, Σ t ≤ 1}`. -/
def stdSimp (k : ℕ) : Set (Fin k → ℝ) := {t | (∀ q, 0 ≤ t q) ∧ ∑ q, t q ≤ 1}

theorem measurableSet_stdSimp (k : ℕ) : MeasurableSet (stdSimp k) := by
  have h1 : MeasurableSet {t : Fin k → ℝ | ∀ q, 0 ≤ t q} := by
    rw [setOf_forall]
    exact MeasurableSet.iInter fun q => measurableSet_le measurable_const (measurable_pi_apply q)
  have h2 : MeasurableSet {t : Fin k → ℝ | ∑ q, t q ≤ 1} :=
    measurableSet_le (Finset.measurable_sum _ fun q _ => measurable_pi_apply q) measurable_const
  exact h1.inter h2

theorem zero_mem_stdSimp (k : ℕ) : (0 : Fin k → ℝ) ∈ stdSimp k :=
  ⟨fun _ => le_rfl, by simp⟩

theorem slice_eq_smul (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    {t : Fin k → ℝ | (∀ q, 0 ≤ t q) ∧ s + ∑ q, t q ≤ 1} = (1 - s) • stdSimp k := by
  ext t
  simp only [mem_setOf_eq, Set.mem_smul_set]
  constructor
  · rintro ⟨ht0, ht1⟩
    rcases lt_or_eq_of_le hs1 with hlt | rfl
    · refine ⟨(1 - s)⁻¹ • t, ⟨fun q => ?_, ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.mpr (by linarith)) (ht0 q)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [inv_mul_le_iff₀ (by linarith)]
        linarith
      · rw [smul_smul, mul_inv_cancel₀ (by linarith), one_smul]
    · refine ⟨0, zero_mem_stdSimp k, ?_⟩
      have hsum : ∑ q, t q = 0 := le_antisymm (by linarith)
        (Finset.sum_nonneg fun q _ => ht0 q)
      have hz : t = 0 := by
        funext q
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => ht0 q)).mp hsum q (Finset.mem_univ _)
      rw [hz, smul_zero]
  · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
    refine ⟨fun q => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by linarith) (hu0 q)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      nlinarith

theorem integral_one_sub_pow (k : ℕ) :
    ∫ s in Icc (0 : ℝ) 1, (1 - s) ^ k = 1 / (k + 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left (fun x => x ^ k), integral_pow]
  simp

/-- **The volume of the standard simplex**: `|Δ_k| = 1/k!`. -/
theorem volume_stdSimp (k : ℕ) : volume (stdSimp k) = ENNReal.ofReal (1 / k.factorial) := by
  induction k with
  | zero =>
    have : stdSimp 0 = univ := by
      ext t; simp [stdSimp]
    rw [this, volume_pi, Measure.pi_univ]
    simp
  | succ k ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
    set A : Set (ℝ × (Fin k → ℝ)) := {p | 0 ≤ p.1 ∧ (∀ q, 0 ≤ p.2 q) ∧ p.1 + ∑ q, p.2 q ≤ 1}
    have hA : MeasurableSet A := by
      have h1 : MeasurableSet {p : ℝ × (Fin k → ℝ) | 0 ≤ p.1} :=
        measurableSet_le measurable_const measurable_fst
      have h2 : MeasurableSet {p : ℝ × (Fin k → ℝ) | ∀ q, 0 ≤ p.2 q} := by
        rw [setOf_forall]
        exact MeasurableSet.iInter fun q =>
          measurableSet_le measurable_const ((measurable_pi_apply q).comp measurable_snd)
      have h3 : MeasurableSet {p : ℝ × (Fin k → ℝ) | p.1 + ∑ q, p.2 q ≤ 1} :=
        measurableSet_le (measurable_fst.add (Finset.measurable_sum _ fun q _ =>
          (measurable_pi_apply q).comp measurable_snd)) measurable_const
      exact h1.inter (h2.inter h3)
    have hpre : stdSimp (k + 1) = e ⁻¹' A := by
      ext t
      simp [stdSimp, A, e, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.removeNth_zero, Fin.tail,
        and_assoc]
    rw [hpre, (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).measure_preimage
      hA.nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_apply hA]
    have hslice : ∀ s : ℝ, volume (Prod.mk s ⁻¹' A) =
        (Icc (0 : ℝ) 1).indicator (fun s => ENNReal.ofReal ((1 - s) ^ k) * volume (stdSimp k)) s := by
      intro s
      by_cases hs : s ∈ Icc (0 : ℝ) 1
      · rw [indicator_of_mem hs]
        have : Prod.mk s ⁻¹' A = {t : Fin k → ℝ | (∀ q, 0 ≤ t q) ∧ s + ∑ q, t q ≤ 1} := by
          ext t; simp [A, hs.1]
        rw [this, slice_eq_smul k hs.1 hs.2, Measure.addHaar_smul_of_nonneg _ (by linarith [hs.2]),
          Module.finrank_fin_fun]
      · rw [indicator_of_notMem hs]
        have : Prod.mk s ⁻¹' A = ∅ := by
          ext t
          simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
          rintro ⟨h0, ht, h1⟩
          apply hs
          refine ⟨h0, ?_⟩
          have := Finset.sum_nonneg fun q (_ : q ∈ Finset.univ) => ht q
          linarith
        rw [this, measure_empty]
    simp_rw [hslice]
    rw [lintegral_indicator measurableSet_Icc, lintegral_mul_const _ (by fun_prop), ih,
      ← ofReal_integral_eq_lintegral_ofReal, integral_one_sub_pow, ← ENNReal.ofReal_mul (by positivity)]
    · congr 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    · exact (continuous_const.sub continuous_id).pow k |>.integrableOn_Icc
    · exact ae_restrict_of_forall_mem measurableSet_Icc fun s hs =>
        pow_nonneg (by linarith [hs.2]) k

/-! ### Wedge products of 1-forms -/

section Wedge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The wedge product `f₀ ∧ ⋯ ∧ f_{m-1}` of 1-forms: `(v_q) ↦ det (f_p(v_q))`. -/
def wedgeL {m : ℕ} (f : Fin m → E →L[ℝ] ℝ) : E [⋀^Fin m]→L[ℝ] ℝ :=
  let A : E [⋀^Fin m]→ₗ[ℝ] ℝ :=
    Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun p => (f p : E →ₗ[ℝ] ℝ))
  { A with
    cont := by
      have : (fun v : Fin m → E => A v) = fun v => (Matrix.of fun q p => f p (v q)).det := rfl
      change Continuous fun v : Fin m → E => A v
      rw [this]
      refine Continuous.matrix_det ?_
      exact continuous_pi fun q => continuous_pi fun p => (f p).continuous.comp (continuous_apply q) }

theorem wedgeL_apply {m : ℕ} (f : Fin m → E →L[ℝ] ℝ) (v : Fin m → E) :
    wedgeL f v = (Matrix.of fun p q => f p (v q)).det := by
  change (Matrix.of fun q p => f p (v q)).det = _
  rw [← Matrix.det_transpose]
  rfl

end Wedge

/-! ### Whitney forms of degree `k` -/

open WhitneyLow

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (b : AffineBasis ι ℝ E)

/-- The barycentric matrix of a vertex tuple `i`, a point `x` and vectors `v`:
column `0` is `(λ_{i_p}(x))_p`, column `q + 1` is `(dλ_{i_p}(v_q))_p`. -/
def baryMat {k : ℕ} (i : Fin (k + 1) → ι) (x : E) (v : Fin k → E) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun p => Fin.cons (lam b (i p) x) fun q => dlam b (i p) (v q)

/-- **The Whitney `k`-form** of an oriented vertex tuple `i = (i₀, …, i_k)` (`eq:Whitney`):
`w_i = k! Σ_j (-1)^j λ_{i_j} dλ_{i₀} ∧ ⋯ ∧ (dλ_{i_j} omitted) ∧ ⋯ ∧ dλ_{i_k}`. -/
def whit (k : ℕ) (i : Fin (k + 1) → ι) (x : E) : E [⋀^Fin k]→L[ℝ] ℝ :=
  (k.factorial : ℝ) • ∑ j : Fin (k + 1),
    ((-1 : ℝ) ^ (j : ℕ) * lam b (i j) x) • wedgeL fun p => dlam b (i (j.succAbove p))

/-- The value of a Whitney form is `k!` times the determinant of the barycentric matrix. -/
theorem whit_apply (k : ℕ) (i : Fin (k + 1) → ι) (x : E) (v : Fin k → E) :
    whit b k i x v = k.factorial * (baryMat b i x v).det := by
  rw [Matrix.det_succ_column_zero]
  simp only [whit, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply,
    smul_eq_mul, wedgeL_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [baryMat, Matrix.of_apply, Fin.cons_zero, Matrix.submatrix, Fin.cons_succ]

/-- Alternating `k`-cochains: `c(i ∘ σ) = sign σ · c(i)`. -/
def IsAlt {k : ℕ} (c : (Fin (k + 1) → ι) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1) → ι),
    c (i ∘ σ) = (Equiv.Perm.sign σ : ℝ) * c i

/-- **The Whitney reconstruction** `W c = (1/(k+1)!) Σ_i c_i w_i` (sum over all vertex tuples;
on alternating cochains this is `Σ_{i₀<⋯<i_k} c_i w_i`). -/
def W (k : ℕ) (c : (Fin (k + 1) → ι) → ℝ) (x : E) : E [⋀^Fin k]→L[ℝ] ℝ :=
  (1 / ((k + 1).factorial : ℝ)) • ∑ i, c i • whit b k i x

theorem W_apply (k : ℕ) (c : (Fin (k + 1) → ι) → ℝ) (x : E) (v : Fin k → E) :
    W b k c x v =
      1 / ((k + 1).factorial : ℝ) * ∑ i, c i * (k.factorial * (baryMat b i x v).det) := by
  simp only [W, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply,
    smul_eq_mul, whit_apply]

/-! ### The de Rham map -/

/-- The parametrisation `t ↦ v_{a₀} + Σ_q t_q (v_{a_{q+1}} - v_{a₀})` of the face `[a₀, …, a_k]`. -/
def faceMap {k : ℕ} (a : Fin (k + 1) → ι) (t : Fin k → ℝ) : E :=
  b (a 0) + ∑ q, t q • (b (a q.succ) - b (a 0))

/-- The edge vectors `v_{a_{q+1}} - v_{a₀}` of the face. -/
def edges {k : ℕ} (a : Fin (k + 1) → ι) : Fin k → E := fun q => b (a q.succ) - b (a 0)

/-- **The de Rham map** `R α = (∫_σ α)_σ`: the integral of the pullback of `α` over the standard
simplex for the oriented face `σ = [a₀, …, a_k]`. -/
def R (k : ℕ) (α : E → E [⋀^Fin k]→L[ℝ] ℝ) (a : Fin (k + 1) → ι) : ℝ :=
  ∫ t in stdSimp k, α (faceMap b a t) (edges b a)

/-- The barycentric weights of a point of the standard simplex. -/
def mu {k : ℕ} (t : Fin k → ℝ) : Fin (k + 1) → ℝ := Fin.cons (1 - ∑ q, t q) t

/-- The incidence matrix `M_{pr} = [i_p = a_r]`. -/
def incMat {k : ℕ} (i a : Fin (k + 1) → ι) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun p r => if i p = a r then 1 else 0

/-- The transition matrix `T(t)`: column `0` is `μ(t)`, column `q+1` is `e_{q+1} - e_0`. -/
def transMat {k : ℕ} (t : Fin k → ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun r => Fin.cons (mu t r) fun q => (if r = q.succ then 1 else 0) - if r = 0 then 1 else 0

theorem lam_faceMap {k : ℕ} (m : ι) (a : Fin (k + 1) → ι) (t : Fin k → ℝ) :
    lam b m (faceMap b a t) = ∑ r, (if m = a r then 1 else 0) * mu t r := by
  rw [faceMap, lam_add, lam_vertex, map_sum, Fin.sum_univ_succ]
  simp only [map_smul, smul_eq_mul, dlam_vertex_sub, mu, Fin.cons_zero, Fin.cons_succ, δ,
    mul_sub, Finset.sum_sub_distrib, mul_one, Finset.mul_sum]
  simp only [mul_comm (t _)]
  ring

theorem dlam_edges {k : ℕ} (m : ι) (a : Fin (k + 1) → ι) (q : Fin k) :
    dlam b m (edges b a q) = (if m = a q.succ then 1 else 0) - if m = a 0 then 1 else 0 := by
  rw [edges, dlam_vertex_sub]; rfl

/-- **The pullback of the barycentric matrix to a face** factors through the incidence matrix. -/
theorem baryMat_faceMap {k : ℕ} (i a : Fin (k + 1) → ι) (t : Fin k → ℝ) :
    baryMat b i (faceMap b a t) (edges b a) = incMat i a * transMat t := by
  ext p c
  refine Fin.cases ?_ (fun q => ?_) c
  · simp only [baryMat, Matrix.of_apply, Fin.cons_zero, Matrix.mul_apply, incMat, transMat,
      lam_faceMap]
  · simp only [baryMat, Matrix.of_apply, Fin.cons_succ, Matrix.mul_apply, incMat, transMat,
      dlam_edges, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem zero_ne_succ' {k : ℕ} (x : Fin k) : (0 : Fin (k + 1)) ≠ x.succ := (Fin.succ_ne_zero x).symm

/-- The transition matrix is unimodular: `T = U L` with `U` upper and `L` lower unitriangular. -/
theorem det_transMat {k : ℕ} (t : Fin k → ℝ) : (transMat t).det = 1 := by
  set U : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
    Matrix.of fun r c => if r = c then 1 else if r = 0 then -1 else 0
  set L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
    Matrix.of fun r c => if r = c then 1 else if c = 0 then mu t r else 0
  have hT : transMat t = U * L := by
    ext r c
    simp only [Matrix.mul_apply, U, L, transMat, Matrix.of_apply]
    refine Fin.cases ?_ (fun r' => ?_) r <;> refine Fin.cases ?_ (fun c' => ?_) c
    · simp [Fin.sum_univ_succ, mu, Fin.succ_ne_zero, zero_ne_succ', sub_eq_add_neg]
    · simp [Fin.sum_univ_succ, Fin.succ_ne_zero, zero_ne_succ']
    · simp [Fin.sum_univ_succ, mu, Fin.succ_ne_zero, zero_ne_succ', Fin.succ_inj]
    · simp [Fin.sum_univ_succ, Fin.succ_ne_zero, zero_ne_succ', Fin.succ_inj]
  have hU : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [U]
    · intro r c hrc
      have hrc' : c < r := hrc
      have h1 : r ≠ c := hrc'.ne'
      have h2 : r ≠ 0 := Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le c) hrc')
      simp [U, h1, h2]
  have hL : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · simp [L]
    · intro r c hrc
      have hrc' : r < c := hrc
      have h1 : r ≠ c := hrc'.ne
      have h2 : c ≠ 0 := Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le r) hrc')
      simp [L, h1, h2]
  rw [hT, Matrix.det_mul, hU, hL, mul_one]

/-- **The Kronecker pairing on alternating cochains**: `Σ_i c_i det[i_p = a_r] = (k+1)! c_a`. -/
theorem sum_mul_det_incMat {k : ℕ} {c : (Fin (k + 1) → ι) → ℝ} (hc : IsAlt c)
    (a : Fin (k + 1) → ι) :
    ∑ i, c i * (incMat i a).det = ((k + 1).factorial : ℝ) * c a := by
  simp only [Matrix.det_apply', incMat, Matrix.of_apply, Fintype.prod_boole, Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ σ : Equiv.Perm (Fin (k + 1)), ∑ i : Fin (k + 1) → ι,
      c i * ((Equiv.Perm.sign σ : ℝ) * if ∀ r, i (σ r) = a r then 1 else 0) = c a := by
    intro σ
    have hiff : ∀ i : Fin (k + 1) → ι, (∀ r, i (σ r) = a r) ↔ i = a ∘ σ.symm := by
      intro i
      constructor
      · intro h; funext r; simpa using h (σ.symm r)
      · rintro rfl r; simp
    simp only [hiff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hc σ.symm a, Equiv.Perm.sign_symm]
    have hε : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    linear_combination (c a) * hε
  rw [Finset.sum_congr rfl fun σ _ => by convert key σ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

/-- The Whitney reconstruction pulled back to any face is constant: on the edge vectors of the face
`a` its value is `k! c_a`. -/
theorem W_faceMap {k : ℕ} {c : (Fin (k + 1) → ι) → ℝ} (hc : IsAlt c) (a : Fin (k + 1) → ι)
    (t : Fin k → ℝ) : W b k c (faceMap b a t) (edges b a) = (k.factorial : ℝ) * c a := by
  rw [W_apply]
  simp only [baryMat_faceMap, Matrix.det_mul, det_transMat, mul_one]
  have : ∑ i, c i * ((k.factorial : ℝ) * (incMat i a).det) =
      (k.factorial : ℝ) * ∑ i, c i * (incMat i a).det := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, sum_mul_det_incMat hc, Nat.factorial_succ]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **`R_h W_h = I` in every degree** (Kronecker pairing of Whitney forms with oriented faces). -/
theorem R_W {k : ℕ} {c : (Fin (k + 1) → ι) → ℝ} (hc : IsAlt c) (a : Fin (k + 1) → ι) :
    R b k (W b k c) a = c a := by
  rw [R, setIntegral_congr_fun (measurableSet_stdSimp k) (fun t _ => W_faceMap b hc a t),
    setIntegral_const, measureReal_def, volume_stdSimp, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp


/-! ### The commuting identity `d W_h = W_h d_h` in every degree -/

/-- The simplicial coboundary `(d c)_m = Σ_j (-1)^j c(m₀, …, \widehat{m_j}, …, m_{k+1})`. -/
def dCoch {k : ℕ} (c : (Fin (k + 1) → ι) → ℝ) (m : Fin (k + 2) → ι) : ℝ :=
  ∑ j : Fin (k + 2), (-1 : ℝ) ^ (j : ℕ) * c (m ∘ j.succAbove)

/-- The differential matrix `(dλ_{i_p}(v_q))_{p,q}`. -/
def dMat {k : ℕ} (i : Fin (k + 1) → ι) (v : Fin (k + 1) → E) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun p q => dlam b (i p) (v q)

/-- The Whitney reconstruction as an explicit affine function of the point. -/
theorem W_apply_expand (k : ℕ) (c : (Fin (k + 1) → ι) → ℝ) (y : E) (u : Fin k → E) :
    W b k c y u = ∑ i, ∑ j : Fin (k + 1), (1 / ((k + 1).factorial : ℝ) * c i * k.factorial *
      (-1 : ℝ) ^ (j : ℕ) * (wedgeL fun p => dlam b (i (j.succAbove p))) u) * lam b (i j) y := by
  simp only [W, whit, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hasFDerivAt_W_apply (k : ℕ) (c : (Fin (k + 1) → ι) → ℝ) (u : Fin k → E) (x : E) :
    HasFDerivAt (fun y => W b k c y u) (∑ i, ∑ j : Fin (k + 1),
      (1 / ((k + 1).factorial : ℝ) * c i * k.factorial * (-1 : ℝ) ^ (j : ℕ) *
        (wedgeL fun p => dlam b (i (j.succAbove p))) u) • dlam b (i j)) x := by
  have e : (fun y => W b k c y u) = fun y => ∑ i, ∑ j : Fin (k + 1),
      (1 / ((k + 1).factorial : ℝ) * c i * k.factorial * (-1 : ℝ) ^ (j : ℕ) *
        (wedgeL fun p => dlam b (i (j.succAbove p))) u) * lam b (i j) y :=
    funext fun y => W_apply_expand b k c y u
  rw [e]
  exact HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ =>
    (hasFDerivAt_lam b (i j) x).const_mul _

theorem W_eq_sum (k : ℕ) (c : (Fin (k + 1) → ι) → ℝ) :
    W b k c = fun y => ∑ i, ∑ j : Fin (k + 1), (1 / ((k + 1).factorial : ℝ) * c i * k.factorial *
      (-1 : ℝ) ^ (j : ℕ) * lam b (i j) y) • wedgeL fun p => dlam b (i (j.succAbove p)) := by
  funext y; ext u
  rw [W_apply_expand]
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem differentiableAt_W (k : ℕ) (c : (Fin (k + 1) → ι) → ℝ) (x : E) :
    DifferentiableAt ℝ (W b k c) x := by
  have hl : ∀ m, Differentiable ℝ (lam b m) := fun m y => (hasFDerivAt_lam b m y).differentiableAt
  rw [W_eq_sum]
  exact DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ =>
    DifferentiableAt.smul_const ((hl _ x).const_mul _) _

/-- Laplace expansion: `Σ_r (-1)^r A_{jr} det A^{(j,r)} = (-1)^j det A`. -/
theorem laplace_row {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (j : Fin (k + 1)) :
    ∑ r : Fin (k + 1), (-1 : ℝ) ^ (r : ℕ) * A j r * (A.submatrix j.succAbove r.succAbove).det =
      (-1 : ℝ) ^ (j : ℕ) * A.det := by
  rw [Matrix.det_succ_row A j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pow_add]
  have : ((-1 : ℝ) ^ (j : ℕ)) * (-1) ^ (j : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (-(A j r * (A.submatrix j.succAbove r.succAbove).det * (-1) ^ (r : ℕ))) * this

/-- **The exterior derivative of the Whitney reconstruction** (Mathlib's `extDeriv`):
`d(W c)(v) = Σ_i c_i det(dλ_{i_p}(v_q))`. -/
theorem extDeriv_W_apply (k : ℕ) (c : (Fin (k + 1) → ι) → ℝ) (x : E) (v : Fin (k + 1) → E) :
    extDeriv (W b k c) x v = ∑ i, c i * (dMat b i v).det := by
  rw [extDeriv_apply (differentiableAt_W b k c x)]
  simp only [(hasFDerivAt_W_apply b k c _ x).fderiv, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, wedgeL_apply]
  have hrem : ∀ (r : Fin (k + 1)) (i : Fin (k + 1) → ι) (j : Fin (k + 1)),
      (Matrix.of fun p q => dlam b (i (j.succAbove p)) (r.removeNth v q)).det =
        ((dMat b i v).submatrix j.succAbove r.succAbove).det := fun r i j => rfl
  simp only [hrem]
  have hsum : ∀ i : Fin (k + 1) → ι, ∑ j : Fin (k + 1), ∑ r : Fin (k + 1),
      (-1 : ℝ) ^ (r : ℕ) * ((-1 : ℝ) ^ (j : ℕ) * dMat b i v j r *
        ((dMat b i v).submatrix j.succAbove r.succAbove).det) = (k + 1) * (dMat b i v).det := by
    intro i
    have : ∀ j : Fin (k + 1), ∑ r : Fin (k + 1), (-1 : ℝ) ^ (r : ℕ) * ((-1 : ℝ) ^ (j : ℕ) *
        dMat b i v j r * ((dMat b i v).submatrix j.succAbove r.succAbove).det) =
        (dMat b i v).det := by
      intro j
      have h := laplace_row (dMat b i v) j
      have h2 : ((-1 : ℝ) ^ (j : ℕ)) * (-1) ^ (j : ℕ) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      calc _ = (-1 : ℝ) ^ (j : ℕ) * ∑ r : Fin (k + 1), (-1 : ℝ) ^ (r : ℕ) * dMat b i v j r *
            ((dMat b i v).submatrix j.succAbove r.succAbove).det := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
        _ = _ := by rw [h, ← mul_assoc, h2, one_mul]
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hfac : (1 / ((k + 1).factorial : ℝ)) * k.factorial * (k + 1) = 1 := by
    rw [Nat.factorial_succ]; push_cast
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have hci : (1 / ((k + 1).factorial : ℝ) * c i * k.factorial) * ((k + 1) * (dMat b i v).det) =
      c i * (dMat b i v).det := by
    linear_combination (c i * (dMat b i v).det) * hfac
  rw [← hci, ← hsum i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [dMat, Matrix.of_apply]
  ring

/-- Laplace expansion of the barycentric matrix along the inserted row: summing over the inserted
vertex uses `Σ_l λ_l = 1`, `Σ_l dλ_l = 0`. -/
theorem sum_det_baryMat_insertNth {k : ℕ} (j : Fin (k + 2)) (i : Fin (k + 1) → ι) (x : E)
    (v : Fin (k + 1) → E) :
    ∑ l, (baryMat b (Fin.insertNth j l i) x v).det = (-1 : ℝ) ^ (j : ℕ) * (dMat b i v).det := by
  set G : Matrix (Fin (k + 1)) (Fin (k + 2)) ℝ :=
    Matrix.of fun p => Fin.cons (lam b (i p) x) fun q => dlam b (i p) (v q)
  have hsub : ∀ l (c : Fin (k + 2)), (baryMat b (Fin.insertNth j l i) x v).submatrix j.succAbove
      c.succAbove = G.submatrix id c.succAbove := by
    intro l c; ext p q
    simp [baryMat, G, Fin.insertNth_apply_succAbove]
  have hrow : ∀ l (c : Fin (k + 2)), baryMat b (Fin.insertNth j l i) x v j c =
      (Fin.cons (lam b l x) (fun q => dlam b l (v q)) : Fin (k + 2) → ℝ) c := by
    intro l c; simp [baryMat]
  simp only [fun l => Matrix.det_succ_row (baryMat b (Fin.insertNth j l i) x v) j, hsub, hrow]
  rw [Finset.sum_comm]
  rw [Fin.sum_univ_succ]
  have h0 : ∑ l, (-1 : ℝ) ^ ((j : ℕ) + ((0 : Fin (k + 2)) : ℕ)) *
      (Fin.cons (lam b l x) (fun q => dlam b l (v q)) : Fin (k + 2) → ℝ) 0 *
        (G.submatrix id (0 : Fin (k + 2)).succAbove).det =
      (-1 : ℝ) ^ (j : ℕ) * (dMat b i v).det := by
    simp only [Fin.cons_zero, Fin.val_zero, add_zero]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_lam, mul_one]
    rfl
  have hs : ∀ q : Fin (k + 1), ∑ l, (-1 : ℝ) ^ ((j : ℕ) + (q.succ : ℕ)) *
      (Fin.cons (lam b l x) (fun q => dlam b l (v q)) : Fin (k + 2) → ℝ) q.succ *
        (G.submatrix id q.succ.succAbove).det = 0 := by
    intro q
    simp only [Fin.cons_succ]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_dlam, mul_zero, zero_mul]
  rw [h0, Finset.sum_eq_zero fun q _ => hs q, add_zero]

/-- **`d W_h = W_h d_h` in every degree** (on one simplex; Mathlib's `extDeriv`). -/
theorem extDeriv_W (k : ℕ) (c : (Fin (k + 1) → ι) → ℝ) (x : E) :
    extDeriv (W b k c) x = W b (k + 1) (dCoch c) x := by
  ext v
  rw [extDeriv_W_apply, W_apply]
  have hre : ∀ j : Fin (k + 2), ∑ m : Fin (k + 2) → ι, (-1 : ℝ) ^ (j : ℕ) * c (m ∘ j.succAbove) *
      (baryMat b m x v).det = ∑ i, c i * (dMat b i v).det := by
    intro j
    rw [← Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => ι) j)
      (fun p => (-1 : ℝ) ^ (j : ℕ) * c (Fin.insertNth j p.1 p.2 ∘ j.succAbove) *
        (baryMat b (Fin.insertNth j p.1 p.2) x v).det) _ (fun p => rfl),
      Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.insertNth_comp_succAbove]
    rw [← Finset.mul_sum, sum_det_baryMat_insertNth]
    have h2 : ((-1 : ℝ) ^ (j : ℕ)) * (-1) ^ (j : ℕ) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination (c i * (dMat b i v).det) * h2
  have : ∑ m, dCoch c m * (((k + 1).factorial : ℝ) * (baryMat b m x v).det) =
      ((k + 1).factorial : ℝ) * ∑ j : Fin (k + 2), ∑ m : Fin (k + 2) → ι,
        (-1 : ℝ) ^ (j : ℕ) * c (m ∘ j.succAbove) * (baryMat b m x v).det := by
    simp only [dCoch, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by ring
  rw [this, Finset.sum_congr rfl fun j _ => hre j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.factorial_succ (k + 1)]
  push_cast
  have : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring


/-! ### Positivity of the comparison mass norm in every degree -/

theorem continuous_W (k : ℕ) (c : (Fin (k + 1) → ι) → ℝ) : Continuous (W b k c) := by
  rw [W_eq_sum]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_const.mul (continuous_lam b _)).smul continuous_const

theorem faceMap_eq_sum {k : ℕ} (a : Fin (k + 1) → ι) (t : Fin k → ℝ) :
    faceMap b a t = ∑ r, mu t r • b (a r) := by
  rw [faceMap, Fin.sum_univ_succ]
  simp only [mu, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul,
    one_smul, ← Finset.sum_smul]
  abel

theorem faceMap_mem {k : ℕ} (a : Fin (k + 1) → ι) {t : Fin k → ℝ} (ht : t ∈ stdSimp k) :
    faceMap b a t ∈ simplex b := by
  rw [faceMap_eq_sum]
  refine (convex_convexHull ℝ _).sum_mem (fun r _ => ?_) ?_ (fun r _ =>
    subset_convexHull ℝ _ (mem_range_self _))
  · refine Fin.cases ?_ (fun q => ?_) r
    · simp only [mu, Fin.cons_zero]; linarith [ht.2]
    · simp only [mu, Fin.cons_succ]; exact ht.1 q
  · rw [Fin.sum_univ_succ]
    simp [mu]




variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Positivity of the degree-`k` comparison norm (the mass matrix is positive definite)**: for a
nonzero alternating `k`-cochain, `∫_S ‖W c‖² > 0`. -/
theorem mass_pos {k : ℕ} {c : (Fin (k + 1) → ι) → ℝ} (hc : IsAlt c) (hne : c ≠ 0) :
    0 < ∫ x in simplex b, ‖W b k c x‖ ^ 2 ∂μ := by
  refine pos_of_ne_zero_on_interior b μ (continuous_W b k c) ?_
  by_contra hcon
  push_neg at hcon
  have hS : ∀ x ∈ simplex b, W b k c x = 0 := by
    have hcl : IsClosed {x | W b k c x = 0} := isClosed_eq (continuous_W b k c) continuous_const
    intro x hx
    rw [← closure_interior_simplex] at hx
    exact (hcl.closure_subset_iff.mpr hcon) hx
  apply hne
  funext a
  rw [← R_W b hc a, R, setIntegral_congr_fun (measurableSet_stdSimp k) (g := fun _ => (0 : ℝ))
    (fun t ht => by simp [hS _ (faceMap_mem b a ht)])]
  simp

theorem W_injective {k : ℕ} {c c' : (Fin (k + 1) → ι) → ℝ} (hc : IsAlt c) (hc' : IsAlt c')
    (h : W b k c = W b k c') : c = c' := by
  funext a
  rw [← R_W b hc a, ← R_W b hc' a, h]

/-! ### Conformity across shared faces in every degree -/

section Conforming

open WhitneyTwo (ext facePt lam_facePt dlam_faceVec)

variable {F : Type*} [Fintype F]

/-- The barycentric matrix in face coordinates. -/
def faceBary {k : ℕ} (j : Fin (k + 1) → F) (w : F → ℝ) (s : Fin k → F → ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun p => Fin.cons (w (j p)) fun q => s q (j p)

theorem ext_apply_self {f : F → ι} (hf : Function.Injective f) (w : F → ℝ) (p : F) :
    ext f w (f p) = w p := by
  simp only [WhitneyTwo.ext]
  rw [Finset.sum_eq_single p]
  · simp
  · intro p' _ hp'
    rw [if_neg]
    intro h
    exact hp' (hf h)
  · simp

theorem ext_apply_of_not_mem {f : F → ι} (w : F → ℝ) {i : ι} (hi : i ∉ Set.range f) :
    ext f w i = 0 := by
  simp only [WhitneyTwo.ext]
  exact Finset.sum_eq_zero fun p _ => by
    rw [if_neg]; intro h; exact hi ⟨p, h⟩

/-- **Trace formula in every degree**: at a point of the face labelled by `f` and on tangent face
vectors, the Whitney reconstruction only depends on the cochain on the face and on the face
coordinates. -/
theorem W_facePt {k : ℕ} {f : F → ι} (hf : Function.Injective f) (c : (Fin (k + 1) → ι) → ℝ)
    {w : F → ℝ} (hw : ∑ p, w p = 1) {s : Fin k → F → ℝ} (hs : ∀ q, ∑ p, s q p = 0) :
    W b k c (facePt b f w) (fun q => facePt b f (s q)) =
      1 / ((k + 1).factorial : ℝ) *
        ∑ j : Fin (k + 1) → F, c (f ∘ j) * (k.factorial * (faceBary j w s).det) := by
  rw [W_apply]
  congr 1
  have hbary : ∀ i : Fin (k + 1) → ι, baryMat b i (facePt b f w) (fun q => facePt b f (s q)) =
      Matrix.of fun p => Fin.cons (ext f w (i p)) fun q => ext f (s q) (i p) := by
    intro i; ext p r
    refine Fin.cases ?_ (fun q => ?_) r
    · simp [baryMat, lam_facePt b hf hw]
    · simp [baryMat, dlam_faceVec b hf hw (hs q)]
  symm
  refine Fintype.sum_of_injective (fun j => f ∘ j) (fun j j' h => ?_) _ _ ?_ ?_
  · funext p; exact hf (congrFun h p)
  · intro i hi
    have : ∃ p, i p ∉ Set.range f := by
      by_contra hcon
      push_neg at hcon
      exact hi ⟨fun p => (hcon p).choose, funext fun p => (hcon p).choose_spec⟩
    obtain ⟨p, hp⟩ := this
    rw [hbary, Matrix.det_eq_zero_of_row_eq_zero p, mul_zero, mul_zero]
    intro r
    refine Fin.cases ?_ (fun q => ?_) r
    · simp [ext_apply_of_not_mem _ hp]
    · simp [ext_apply_of_not_mem _ hp]
  · intro j
    rw [hbary]
    congr 3
    ext p r
    refine Fin.cases ?_ (fun q => ?_) r
    · simp [faceBary, ext_apply_self hf]
    · simp [faceBary, ext_apply_self hf]

/-- **Inter-element conformity in every degree**: two simplices (affine bases) sharing the
vertices of a face, with cochains agreeing on that face, have Whitney reconstructions with the
same tangential trace on the face. -/
theorem W_conforming {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b' : AffineBasis ι' ℝ E)
    {k : ℕ} {f : F → ι} {f' : F → ι'} (hf : Function.Injective f) (hf' : Function.Injective f')
    (hpos : ∀ p, b (f p) = b' (f' p)) (c : (Fin (k + 1) → ι) → ℝ) (c' : (Fin (k + 1) → ι') → ℝ)
    (hcc : ∀ j : Fin (k + 1) → F, c (f ∘ j) = c' (f' ∘ j)) {w : F → ℝ} (hw : ∑ p, w p = 1)
    {s : Fin k → F → ℝ} (hs : ∀ q, ∑ p, s q p = 0) :
    W b k c (facePt b f w) (fun q => facePt b f (s q)) =
      W b' k c' (facePt b f w) (fun q => facePt b f (s q)) := by
  have hx : ∀ u : F → ℝ, facePt b' f' u = facePt b f u := fun u => by
    simp only [WhitneyTwo.facePt, hpos]
  rw [W_facePt b hf c hw hs]
  simp only [← hx]
  rw [W_facePt b' hf' c' hw hs]
  simp only [hcc]

end Conforming


/-! ### Scaling to a reference simplex -/

section Scaling

variable (bh : AffineBasis ι ℝ E) (φ : E ≃ᵃ[ℝ] E) (hb : ∀ i, b i = φ (bh i))

include hb in
/-- Barycentric coordinates are natural under affine maps. -/
theorem lam_map (i : ι) (ξ : E) : lam b i (φ ξ) = lam bh i ξ := by
  have hξ := bh.affineCombination_coord_eq_self ξ
  have hw : ∑ j, bh.coord j ξ = 1 := bh.sum_coord_apply_eq_one ξ
  have hmap := Finset.map_affineCombination Finset.univ bh (fun j => bh.coord j ξ) hw
    (φ : E →ᵃ[ℝ] E)
  simp only [AffineEquiv.coe_toAffineMap] at hmap
  have : φ ξ = Finset.univ.affineCombination ℝ b fun j => bh.coord j ξ := by
    conv_lhs => rw [← hξ]
    rw [hmap, show (⇑φ ∘ ⇑bh) = ⇑b from funext fun j => (hb j).symm]
  rw [this, lam, b.coord_apply_combination_of_mem (Finset.mem_univ i) hw]
  rfl

include hb in
theorem dlam_map (i : ι) (u : E) : dlam b i (φ.linear u) = dlam bh i u := by
  have h1 := lam_add b i (φ 0) (φ.linear u)
  have h2 := lam_add bh i 0 u
  have hφ : φ 0 + φ.linear u = φ (0 + u) := by
    have := φ.map_vadd 0 u
    rw [vadd_eq_add, vadd_eq_add, add_zero] at this
    rw [zero_add, this, add_comm]
  rw [hφ, lam_map b bh φ hb, lam_map b bh φ hb] at h1
  linarith

include hb in
theorem baryMat_map {k : ℕ} (i : Fin (k + 1) → ι) (ξ : E) (u : Fin k → E) :
    baryMat b i (φ ξ) (fun q => φ.linear (u q)) = baryMat bh i ξ u := by
  ext p r
  refine Fin.cases ?_ (fun q => ?_) r
  · simp [baryMat, lam_map b bh φ hb]
  · simp [baryMat, dlam_map b bh φ hb]

include hb in
/-- **Naturality of the Whitney reconstruction** under the affine map `φ` of the reference simplex
onto the cell: `W_T c(φ ξ)(A u) = Ŵ c(ξ)(u)`. -/
theorem W_map {k : ℕ} (c : (Fin (k + 1) → ι) → ℝ) (ξ : E) (u : Fin k → E) :
    W b k c (φ ξ) (fun q => φ.linear (u q)) = W bh k c ξ u := by
  rw [W_apply, W_apply]
  simp only [baryMat_map b bh φ hb]

/-- The linear part of `φ` as a continuous linear map. -/
def linA : E →L[ℝ] E := LinearMap.toContinuousLinearMap φ.linear.toLinearMap

/-- The inverse linear part. -/
def linAinv : E →L[ℝ] E := LinearMap.toContinuousLinearMap φ.linear.symm.toLinearMap

include hb in
theorem norm_W_ref_le {k : ℕ} (c : (Fin (k + 1) → ι) → ℝ) (ξ : E) :
    ‖W bh k c ξ‖ ≤ ‖W b k c (φ ξ)‖ * ‖linA φ‖ ^ k := by
  have : W bh k c ξ = (W b k c (φ ξ)).compContinuousLinearMap (linA φ) := by
    ext u
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, ← W_map b bh φ hb]
    rfl
  rw [this]
  simpa using ContinuousAlternatingMap.norm_compContinuousLinearMap_le (W b k c (φ ξ)) (linA φ)

include hb in
theorem norm_W_le_ref {k : ℕ} (c : (Fin (k + 1) → ι) → ℝ) (ξ : E) :
    ‖W b k c (φ ξ)‖ ≤ ‖W bh k c ξ‖ * ‖linAinv φ‖ ^ k := by
  have : W b k c (φ ξ) = (W bh k c ξ).compContinuousLinearMap (linAinv φ) := by
    ext u
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, ← W_map b bh φ hb]
    congr 1
    funext q
    simp [linAinv]
  rw [this]
  simpa using ContinuousAlternatingMap.norm_compContinuousLinearMap_le (W bh k c ξ) (linAinv φ)

include hb in
theorem simplex_map : simplex b = φ '' simplex bh := by
  have hr : Set.range b = φ '' Set.range bh := by
    ext x; simp [hb]
  rw [simplex, simplex, hr]
  have := (φ : E →ᵃ[ℝ] E).image_convexHull (Set.range bh)
  simp only [AffineEquiv.coe_toAffineMap] at this
  exact this.symm

theorem hasFDerivAt_affineEquiv (x : E) : HasFDerivAt φ (linA φ) x := by
  have e : (φ : E → E) = fun y => linA φ y + φ 0 := by
    funext y
    have := φ.map_vadd 0 y
    simp only [vadd_eq_add, add_zero] at this
    rw [this]
    rfl
  rw [e]
  exact (linA φ).hasFDerivAt.add_const _

include hb in
/-- **Change of variables for the mass**: `∫_T ‖W c‖² = |det A| ∫_{T̂} ‖W c ∘ φ‖²`. -/
theorem mass_map {k : ℕ} (c : (Fin (k + 1) → ι) → ℝ) :
    ∫ x in simplex b, ‖W b k c x‖ ^ 2 =
      |(linA φ).det| * ∫ ξ in simplex bh, ‖W b k c (φ ξ)‖ ^ 2 := by
  rw [simplex_map b bh φ hb, integral_image_eq_integral_abs_det_fderiv_smul volume
    (isCompact_simplex bh).isClosed.measurableSet
    (fun x _ => (hasFDerivAt_affineEquiv φ x).hasFDerivWithinAt) φ.injective.injOn,
    ← integral_const_mul]
  rfl

include hb in
/-- **Two-sided scaling of the mass to the reference simplex**:
`|det A| ∫_{T̂} ‖Ŵ c‖² ≤ ‖A‖^{2k} ∫_T ‖W c‖²` and
`∫_T ‖W c‖² ≤ |det A| ‖A⁻¹‖^{2k} ∫_{T̂} ‖Ŵ c‖²`. -/
theorem mass_scaling {k : ℕ} (c : (Fin (k + 1) → ι) → ℝ) :
    |(linA φ).det| * ∫ ξ in simplex bh, ‖W bh k c ξ‖ ^ 2 ≤
        ‖linA φ‖ ^ (2 * k) * ∫ x in simplex b, ‖W b k c x‖ ^ 2 ∧
      ∫ x in simplex b, ‖W b k c x‖ ^ 2 ≤
        |(linA φ).det| * ‖linAinv φ‖ ^ (2 * k) * ∫ ξ in simplex bh, ‖W bh k c ξ‖ ^ 2 := by
  have hcφ : Continuous fun ξ => ‖W b k c (φ ξ)‖ ^ 2 :=
    ((continuous_W b k c).comp φ.continuous_of_finiteDimensional).norm.pow 2
  have hch : Continuous fun ξ => ‖W bh k c ξ‖ ^ 2 := ((continuous_W bh k c).norm.pow 2)
  have hiφ := hcφ.continuousOn.integrableOn_compact (μ := volume) (isCompact_simplex bh)
  have hih := hch.continuousOn.integrableOn_compact (μ := volume) (isCompact_simplex bh)
  rw [mass_map b bh φ hb]
  have hdet : 0 ≤ |(linA φ).det| := abs_nonneg _
  constructor
  · rw [← mul_assoc, mul_comm (‖linA φ‖ ^ (2 * k)), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hdet
    rw [← integral_const_mul]
    refine setIntegral_mono_on hih (hiφ.const_mul _) (isCompact_simplex bh).isClosed.measurableSet
      fun ξ _ => ?_
    have h := norm_W_ref_le b bh φ hb c ξ
    calc ‖W bh k c ξ‖ ^ 2 ≤ (‖W b k c (φ ξ)‖ * ‖linA φ‖ ^ k) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = ‖linA φ‖ ^ (2 * k) * ‖W b k c (φ ξ)‖ ^ 2 := by ring
  · rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hdet
    rw [← integral_const_mul]
    refine setIntegral_mono_on hiφ (hih.const_mul _) (isCompact_simplex bh).isClosed.measurableSet
      fun ξ _ => ?_
    have h := norm_W_le_ref b bh φ hb c ξ
    calc ‖W b k c (φ ξ)‖ ^ 2 ≤ (‖W bh k c ξ‖ * ‖linAinv φ‖ ^ k) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = ‖linAinv φ‖ ^ (2 * k) * ‖W bh k c ξ‖ ^ 2 := by ring

include hb in
/-- **Shape-regular cellwise scaling constants**: if the affine map of the reference simplex onto the
cell satisfies `‖A‖ ≤ C h`, `‖A⁻¹‖ ≤ C h⁻¹` and `c₀ hⁿ ≤ |det A| ≤ C hⁿ` (shape regularity at mesh
size `h`), then the cell mass is comparable to `h^{n-2k}` times the reference mass, with constants
depending only on `C, c₀, k`:
`c₀ hⁿ M̂(c) ≤ C^{2k} h^{2k} M_T(c)` and `h^{2k} M_T(c) ≤ C^{2k+1} hⁿ M̂(c)`. -/
theorem mass_shape_regular {k n : ℕ} (c : (Fin (k + 1) → ι) → ℝ) {h C c₀ : ℝ} (hh : 0 < h)
    (hC : 0 ≤ C) (hA : ‖linA φ‖ ≤ C * h) (hAinv : ‖linAinv φ‖ ≤ C * h⁻¹)
    (hdet1 : c₀ * h ^ n ≤ |(linA φ).det|) (hdet2 : |(linA φ).det| ≤ C * h ^ n) :
    c₀ * h ^ n * ∫ ξ in simplex bh, ‖W bh k c ξ‖ ^ 2 ≤
        C ^ (2 * k) * h ^ (2 * k) * ∫ x in simplex b, ‖W b k c x‖ ^ 2 ∧
      h ^ (2 * k) * ∫ x in simplex b, ‖W b k c x‖ ^ 2 ≤
        C ^ (2 * k + 1) * h ^ n * ∫ ξ in simplex bh, ‖W bh k c ξ‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := mass_scaling b bh φ hb c
  have hMh : 0 ≤ ∫ ξ in simplex bh, ‖W bh k c ξ‖ ^ 2 :=
    setIntegral_nonneg (isCompact_simplex bh).isClosed.measurableSet fun _ _ => by positivity
  have hM : 0 ≤ ∫ x in simplex b, ‖W b k c x‖ ^ 2 :=
    setIntegral_nonneg (isCompact_simplex b).isClosed.measurableSet fun _ _ => by positivity
  have hpA : ‖linA φ‖ ^ (2 * k) ≤ C ^ (2 * k) * h ^ (2 * k) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hA _
  have hpAi : h ^ (2 * k) * ‖linAinv φ‖ ^ (2 * k) ≤ C ^ (2 * k) := by
    rw [← mul_pow]
    calc (h * ‖linAinv φ‖) ^ (2 * k) ≤ (h * (C * h⁻¹)) ^ (2 * k) :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hAinv hh.le) _
      _ = C ^ (2 * k) := by rw [mul_comm C, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
  constructor
  · calc c₀ * h ^ n * ∫ ξ in simplex bh, ‖W bh k c ξ‖ ^ 2
        ≤ |(linA φ).det| * ∫ ξ in simplex bh, ‖W bh k c ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hdet1 hMh
      _ ≤ ‖linA φ‖ ^ (2 * k) * ∫ x in simplex b, ‖W b k c x‖ ^ 2 := h1
      _ ≤ C ^ (2 * k) * h ^ (2 * k) * ∫ x in simplex b, ‖W b k c x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hpA hM
  · calc h ^ (2 * k) * ∫ x in simplex b, ‖W b k c x‖ ^ 2
        ≤ h ^ (2 * k) * (|(linA φ).det| * ‖linAinv φ‖ ^ (2 * k) *
            ∫ ξ in simplex bh, ‖W bh k c ξ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (h ^ (2 * k) * ‖linAinv φ‖ ^ (2 * k)) * |(linA φ).det| *
            ∫ ξ in simplex bh, ‖W bh k c ξ‖ ^ 2 := by ring
      _ ≤ C ^ (2 * k) * (C * h ^ n) * ∫ ξ in simplex bh, ‖W bh k c ξ‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hpAi hdet2 (abs_nonneg _) (by positivity))
            hMh
      _ = C ^ (2 * k + 1) * h ^ n * ∫ ξ in simplex bh, ‖W bh k c ξ‖ ^ 2 := by ring

end Scaling

/-! ### The global mesh object -/

section Mesh

variable (E)

/-- **A simplicial mesh** of dimension `n` in `E`: finitely many vertices with positions, finitely
many cells, each an affine simplex (affine basis) on `n + 1` distinct mesh vertices, with the
shared-face condition (two closed cells meet in the convex hull of their common vertices) and
pairwise disjoint open cells. -/
structure WhitneyMesh (n : ℕ) where
  /-- mesh vertices -/
  V : Type
  [vFintype : Fintype V]
  [vDecEq : DecidableEq V]
  /-- vertex positions -/
  pos : V → E
  /-- cells -/
  Cell : Type
  [cellFintype : Fintype Cell]
  /-- the vertices of a cell -/
  vert : Cell → Fin (n + 1) → V
  vert_injective : ∀ T, Function.Injective (vert T)
  /-- the cell as an affine simplex -/
  basis : Cell → AffineBasis (Fin (n + 1)) ℝ E
  basis_apply : ∀ T p, basis T p = pos (vert T p)
  /-- shared-face condition -/
  shared_face : ∀ T T', simplex (basis T) ∩ simplex (basis T') =
    convexHull ℝ (pos '' (Set.range (vert T) ∩ Set.range (vert T')))
  /-- open cells are pairwise disjoint -/
  interior_disjoint : ∀ T T', T ≠ T' →
    Disjoint (interior (simplex (basis T))) (interior (simplex (basis T')))

variable {E}

namespace WhitneyMesh

variable {n : ℕ} (M : WhitneyMesh E n)

attribute [instance] vFintype vDecEq cellFintype

/-- The restriction of a global cochain to a cell. -/
def cellCoch {k : ℕ} (T : M.Cell) (c : (Fin (k + 1) → M.V) → ℝ) :
    (Fin (k + 1) → Fin (n + 1)) → ℝ := fun i => c (M.vert T ∘ i)

/-- Alternating global cochains. -/
def IsAltG {k : ℕ} (c : (Fin (k + 1) → M.V) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin (k + 1))) (a : Fin (k + 1) → M.V),
    c (a ∘ σ) = (Equiv.Perm.sign σ : ℝ) * c a

theorem isAlt_cellCoch {k : ℕ} {c : (Fin (k + 1) → M.V) → ℝ} (hc : M.IsAltG c) (T : M.Cell) :
    IsAlt (M.cellCoch T c) := fun σ i => hc σ (M.vert T ∘ i)

/-- The global simplicial coboundary. -/
def dG {k : ℕ} (c : (Fin (k + 1) → M.V) → ℝ) (m : Fin (k + 2) → M.V) : ℝ :=
  ∑ j : Fin (k + 2), (-1 : ℝ) ^ (j : ℕ) * c (m ∘ j.succAbove)

theorem cellCoch_dG {k : ℕ} (T : M.Cell) (c : (Fin (k + 1) → M.V) → ℝ) :
    M.cellCoch T (M.dG c) = dCoch (M.cellCoch T c) := rfl

/-- **The global de Rham map**: integrals over the oriented mesh simplices `[a₀, …, a_k]`
(parametrised by the standard simplex through the vertex positions). -/
def RG {k : ℕ} (α : E → E [⋀^Fin k]→L[ℝ] ℝ) (a : Fin (k + 1) → M.V) : ℝ :=
  ∫ t in stdSimp k, α (M.pos (a 0) + ∑ q, t q • (M.pos (a q.succ) - M.pos (a 0)))
    fun q => M.pos (a q.succ) - M.pos (a 0)

/-- The Whitney reconstruction on a closed cell. -/
def WCell {k : ℕ} (T : M.Cell) (c : (Fin (k + 1) → M.V) → ℝ) (x : E) : E [⋀^Fin k]→L[ℝ] ℝ :=
  W (M.basis T) k (M.cellCoch T c) x

theorem RG_eq_R {k : ℕ} (T : M.Cell) (α : E → E [⋀^Fin k]→L[ℝ] ℝ)
    (i : Fin (k + 1) → Fin (n + 1)) : M.RG α (M.vert T ∘ i) = R (M.basis T) k α i := by
  simp only [RG, R, faceMap, Function.comp_apply, M.basis_apply]
  refine setIntegral_congr_fun (measurableSet_stdSimp k) fun t _ => ?_
  congr 1
  funext q
  unfold edges
  rw [M.basis_apply, M.basis_apply]

/-- **Global `R_h W_h = I`**: on every mesh simplex `a` of every cell `T`, the de Rham map of the
cellwise Whitney reconstruction returns the cochain. -/
theorem RG_WCell {k : ℕ} {c : (Fin (k + 1) → M.V) → ℝ} (hc : M.IsAltG c) (T : M.Cell)
    (i : Fin (k + 1) → Fin (n + 1)) : M.RG (M.WCell T c) (M.vert T ∘ i) = c (M.vert T ∘ i) := by
  rw [RG_eq_R]
  exact R_W (M.basis T) (M.isAlt_cellCoch hc T) i

/-- **Conformity of the global Whitney space**: two cells sharing a mesh face (an injective vertex
tuple of both cells) give Whitney reconstructions with the same tangential trace on that face. -/
theorem WCell_conforming {l m : ℕ} (c : (Fin (l + 1) → M.V) → ℝ) {T T' : M.Cell}
    {i i' : Fin (m + 1) → Fin (n + 1)} (hi : Function.Injective i) (hi' : Function.Injective i')
    (hii : M.vert T ∘ i = M.vert T' ∘ i') {w : Fin (m + 1) → ℝ} (hw : ∑ p, w p = 1)
    {s : Fin l → Fin (m + 1) → ℝ} (hs : ∀ q, ∑ p, s q p = 0) :
    M.WCell T c (WhitneyTwo.facePt (M.basis T) i w)
        (fun q => WhitneyTwo.facePt (M.basis T) i (s q)) =
      M.WCell T' c (WhitneyTwo.facePt (M.basis T) i w)
        (fun q => WhitneyTwo.facePt (M.basis T) i (s q)) := by
  refine W_conforming (M.basis T) (M.basis T') hi hi' (fun p => ?_) _ _ (fun j => ?_) hw hs
  · rw [M.basis_apply, M.basis_apply]
    exact congrArg M.pos (congrFun hii p)
  · show c (M.vert T ∘ (i ∘ j)) = c (M.vert T' ∘ (i' ∘ j))
    rw [← Function.comp_assoc, hii, Function.comp_assoc]

/-- **The global Whitney reconstruction** `W_h c`, defined on the open cells (a full-measure set)
by the cellwise reconstructions. -/
def WG {k : ℕ} (c : (Fin (k + 1) → M.V) → ℝ) (x : E) : E [⋀^Fin k]→L[ℝ] ℝ :=
  ∑ T, (interior (simplex (M.basis T))).indicator (fun y => M.WCell T c y) x

theorem WG_eq_of_mem {k : ℕ} (c : (Fin (k + 1) → M.V) → ℝ) {T : M.Cell} {x : E}
    (hx : x ∈ interior (simplex (M.basis T))) : M.WG c x = M.WCell T c x := by
  rw [WG, Finset.sum_eq_single T]
  · exact Set.indicator_of_mem hx _
  · intro T' _ hT'
    refine Set.indicator_of_notMem (fun hx' => ?_) _
    exact Set.disjoint_left.mp (M.interior_disjoint T T' (Ne.symm hT')) hx hx'
  · simp

theorem WG_eventuallyEq {k : ℕ} (c : (Fin (k + 1) → M.V) → ℝ) {T : M.Cell} {x : E}
    (hx : x ∈ interior (simplex (M.basis T))) : M.WG c =ᶠ[𝓝 x] M.WCell T c := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact M.WG_eq_of_mem c hy

/-- **Global `d W_h = W_h d_h`** on the open cells (Mathlib's `extDeriv`). -/
theorem extDeriv_WG {k : ℕ} (c : (Fin (k + 1) → M.V) → ℝ) {T : M.Cell} {x : E}
    (hx : x ∈ interior (simplex (M.basis T))) : extDeriv (M.WG c) x = M.WG (M.dG c) x := by
  rw [(M.WG_eventuallyEq c hx).extDeriv_eq, M.WG_eq_of_mem _ hx]
  show extDeriv (W (M.basis T) k (M.cellCoch T c)) x = W (M.basis T) (k + 1) (M.cellCoch T (M.dG c)) x
  rw [cellCoch_dG]
  exact extDeriv_W (M.basis T) k _ x

end WhitneyMesh

end Mesh

end WhitneyGen
end RenewalGeometry
