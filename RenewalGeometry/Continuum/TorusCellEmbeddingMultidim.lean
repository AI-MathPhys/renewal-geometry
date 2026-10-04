/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.TorusPiecewiseConstantEmbedding

/-!
# The piecewise-constant cell embedding of the periodic lattice into `L²(𝕋ᵈ)`

The `d`-dimensional version of `TorusPiecewiseConstantEmbedding` (which treats `d = 3`), with the
additional structure needed for norm-resolvent convergence of lattice operators (paper
`predictive_spectral_geometry`, `cor:supp-flat-torus-spin`).  The unit torus
`𝕋ᵈ = UnitAddTorus (Fin d)` carries the Haar probability measure of Mathlib's multidimensional
Fourier theory; for the mesh `h = 1/n` the grid point `x ∈ (ℤ/n)ᵈ` owns the cell
`Q_x = Π_i (x_i/n, (x_i+1)/n]`.

* `pcEmbedding n : ℓ²((ℤ/n)ᵈ) →ₗᵢ L²(𝕋ᵈ)`: `u ↦ Σ_x n^{d/2} u(x) 1_{Q_x}`, the isometric
  piecewise-constant reconstruction `𝒥⁰_h` (unweighted `ℓ²` on the stage side, equivalently
  `u_phys = n^{d/2} u` with cell weight `h^d`).
* `pcEmbedding_mode_dist_le`, `tendsto_pcEmbedding_mode`: the embedded sample of a Fourier
  mode `e_κ` is within `2π Σ|κ_i| / n` of `e_κ`.
* `tendsto_pcEmbedding_adjoint` (**(A1), `𝒥⁰_h (𝒥⁰_h)^* → I` strongly**): proved from the
  best-approximation property of the orthogonal projection `𝒥 𝒥^*` and density of
  trigonometric polynomials.
* Translation structure: `index_add_shiftVec` (`index(y + e_j/n) = index(y) + e_j`), hence the
  cell averages of a mode are a lattice plane wave: `pcEmbedding_adjoint_mode`
  (`𝒥^* e_κ = γ_n(κ) · modeSample κ`) with `γ_n(κ) → 1` (`tendsto_modeFactor`).
* Aliasing: `inner_mode_pcEmbedding_modeSample_eq_zero`: `⟪e_k, 𝒥 (modeSample κ)⟫ = 0` unless
  `k ≡ κ (mod n)`; consequently the interpolation errors `e_{k̃} - 𝒥(modeSample k̃)` of
  distinct grid frequencies are orthogonal (`inner_modeError_eq_zero`) and
  `norm_sum_modeError_sq` gives the Pythagorean identity for their combinations.
-/

open MeasureTheory Set Finset ComplexConjugate UnitAddTorus Filter Topology
open scoped BigOperators Real ENNReal InnerProductSpace

noncomputable section

namespace RenewalGeometry.TorusCellEmbedding

open LatticeTorusPlancherel
open TorusPiecewiseConstant (rep rep_mem coe_rep rep_coe cell1 measurableSet_cell1 volume_cell1
  cell1_disjoint index1 mem_cell1_index1 norm_exp_sub_exp_le fourier_coe_eq)

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {d n : ℕ} [NeZero n]

theorem n_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

/-! ### Cells -/

/-- The cell `Q_x = Π_i (x_i/n, (x_i + 1)/n]`. -/
def cell (x : Grid d n) : Set (UnitAddTorus (Fin d)) := Set.pi univ fun i => cell1 n (x i)

theorem measurableSet_cell (x : Grid d n) : MeasurableSet (cell x) :=
  MeasurableSet.univ_pi fun i => measurableSet_cell1 (x i)

theorem volume_cell (x : Grid d n) : volume (cell x) = ENNReal.ofReal (1 / n) ^ d := by
  rw [cell, volume_pi_pi]
  simp [volume_cell1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem volume_cell_ne_top (x : Grid d n) : volume (cell x) ≠ ∞ := by
  rw [volume_cell]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

theorem volume_real_cell (x : Grid d n) : volume.real (cell x) = ((n : ℝ) ^ d)⁻¹ := by
  rw [measureReal_def, volume_cell, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  rw [one_div, inv_pow]

theorem cell_disjoint {x y : Grid d n} (h : x ≠ y) : Disjoint (cell x) (cell y) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra hc; push Not at hc; exact h (funext hc)
  rw [Set.disjoint_left]
  intro z hz hz'
  exact Set.disjoint_left.mp (cell1_disjoint hi) (hz i (mem_univ i)) (hz' i (mem_univ i))

/-- The grid index of a point of the torus. -/
def index (n : ℕ) (y : UnitAddTorus (Fin d)) : Grid d n := fun i => index1 n (y i)

theorem mem_cell_index (y : UnitAddTorus (Fin d)) : y ∈ cell (index n y) :=
  fun i _ => mem_cell1_index1 (y i)

theorem mem_cell_iff (x : Grid d n) (y : UnitAddTorus (Fin d)) : y ∈ cell x ↔ index n y = x := by
  constructor
  · intro hy
    by_contra hne
    exact Set.disjoint_left.mp (cell_disjoint hne) (mem_cell_index y) hy
  · rintro rfl; exact mem_cell_index y

/-! ### The isometric embedding -/

/-- The normalisation `n^{d/2}`. -/
def scale (n d : ℕ) : ℝ := Real.sqrt n ^ d

theorem scale_pos : 0 < scale n d := pow_pos (Real.sqrt_pos.mpr n_pos) d

theorem scale_sq : scale n d ^ 2 = (n : ℝ) ^ d := by
  rw [scale, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- The normalised cell indicator `φ_x = n^{d/2} 1_{Q_x}`. -/
def cellFn (x : Grid d n) : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d))) :=
  indicatorConstLp 2 (measurableSet_cell x) (volume_cell_ne_top x) ((scale n d : ℝ) : ℂ)

theorem orthonormal_cellFn : Orthonormal ℂ (cellFn (d := d) (n := n)) := by
  rw [orthonormal_iff_ite]
  intro x y
  rw [cellFn, cellFn, L2.inner_indicatorConstLp_indicatorConstLp]
  split_ifs with hxy
  · subst hxy
    rw [Set.inter_self, volume_real_cell, inner_self_eq_norm_sq_to_K, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg scale_pos.le, Complex.real_smul]
    have hn : ((n : ℝ) ^ d) ≠ 0 := (pow_pos n_pos d).ne'
    have key : ((n : ℝ) ^ d)⁻¹ * scale n d ^ 2 = 1 := by rw [scale_sq, inv_mul_cancel₀ hn]
    have h2 := congrArg Complex.ofReal key
    push_cast at h2 ⊢
    exact h2
  · rw [Set.disjoint_iff_inter_eq_empty.mp (cell_disjoint hxy)]
    simp

/-- The linear map `u ↦ Σ_x u(x) φ_x`. -/
def pcLinear (d n : ℕ) [NeZero n] :
    EuclideanSpace ℂ (Grid d n) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d))) where
  toFun f := ∑ x, f x • cellFn x
  map_add' f g := by simp [add_smul, sum_add_distrib]
  map_smul' c f := by simp [smul_sum, smul_smul]

theorem pcLinear_comp_basis :
    (pcLinear d n) ∘ (EuclideanSpace.basisFun (Grid d n) ℂ).toBasis = cellFn := by
  funext x
  simp only [Function.comp_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    pcLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

/-- **The isometric piecewise-constant embedding `𝒥⁰_h`.** -/
def pcEmbedding (d n : ℕ) [NeZero n] :
    EuclideanSpace ℂ (Grid d n) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d))) :=
  (pcLinear d n).isometryOfOrthonormal (v := (EuclideanSpace.basisFun (Grid d n) ℂ).toBasis)
    (by rw [OrthonormalBasis.coe_toBasis]; exact (EuclideanSpace.basisFun _ ℂ).orthonormal)
    (by rw [pcLinear_comp_basis]; exact orthonormal_cellFn)

theorem pcEmbedding_apply (f : EuclideanSpace ℂ (Grid d n)) :
    pcEmbedding d n f = ∑ x, f x • cellFn x := rfl

theorem coeFn_sum_cellFn (c : Grid d n → ℂ) :
    (⇑(∑ x, c x • cellFn x) : UnitAddTorus (Fin d) → ℂ) =ᵐ[volume]
      fun y => ∑ x, c x * (cell x).indicator (fun _ => ((scale n d : ℝ) : ℂ)) y := by
  have key : ∀ s : Finset (Grid d n), (⇑(∑ x ∈ s, c x • cellFn x) : UnitAddTorus (Fin d) → ℂ)
      =ᵐ[volume] fun y => ∑ x ∈ s, c x * (cell x).indicator (fun _ => ((scale n d : ℝ) : ℂ)) y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [sum_empty]
      exact Lp.coeFn_zero _ _ _
    | insert a s ha ih =>
      simp only [sum_insert ha]
      have hφ : (⇑(cellFn a) : UnitAddTorus (Fin d) → ℂ) =ᵐ[volume]
          (cell a).indicator (fun _ => ((scale n d : ℝ) : ℂ)) :=
        indicatorConstLp_coeFn
      filter_upwards [Lp.coeFn_add (c a • cellFn a) (∑ x ∈ s, c x • cellFn x),
        Lp.coeFn_smul (c a) (cellFn a), ih, hφ] with y h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  exact key univ

/-- The embedded function equals `n^{d/2} u(x)` on the cell `Q_x`. -/
theorem coeFn_pcEmbedding (f : EuclideanSpace ℂ (Grid d n)) :
    (⇑(pcEmbedding d n f) : UnitAddTorus (Fin d) → ℂ) =ᵐ[volume]
      fun y => ((scale n d : ℝ) : ℂ) * f (index n y) := by
  have h := coeFn_sum_cellFn (d := d) (n := n) (fun x => f x)
  rw [← pcEmbedding_apply] at h
  refine h.mono fun y hy => ?_
  rw [hy]
  dsimp only
  rw [sum_eq_single (index n y)]
  · rw [Set.indicator_of_mem (mem_cell_index y)]; ring
  · intro x _ hx
    rw [Set.indicator_of_notMem (fun h => hx ((mem_cell_iff x y).mp h).symm), mul_zero]
  · simp

/-! ### Embedded samples of Fourier modes -/

/-- The grid point `x/n` of the torus. -/
def samplePt (x : Grid d n) : UnitAddTorus (Fin d) := fun i => (((x i).val : ℝ) / n : ℝ)

/-- Reduction of an integer frequency modulo `n`. -/
def zcast (n : ℕ) (κ : Fin d → ℤ) : Grid d n := fun i => (κ i : ZMod n)

theorem mFourier_samplePt (κ : Fin d → ℤ) (x : Grid d n) :
    mFourier κ (samplePt x) = latticeChar (zcast n κ) x := by
  simp only [mFourier, ContinuousMap.coe_mk, latticeChar, samplePt, zcast]
  refine prod_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  have e : (κ i : ZMod n) * x i = (((κ i * ((x i).val : ℤ) : ℤ) : ZMod n)) := by
    push_cast
    simp
  rw [e, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- The stage vector `n^{-d/2} e_κ(x/n)`. -/
def modeSample (n : ℕ) [NeZero n] (κ : Fin d → ℤ) : EuclideanSpace ℂ (Grid d n) :=
  WithLp.toLp 2 fun x => ((scale n d : ℝ) : ℂ)⁻¹ * mFourier κ (samplePt x)

theorem modeSample_apply (κ : Fin d → ℤ) (x : Grid d n) :
    modeSample n κ x = ((scale n d : ℝ) : ℂ)⁻¹ * latticeChar (zcast n κ) x := by
  simp [modeSample, mFourier_samplePt]

theorem norm_latticeChar' (ℓ x : Grid d n) : ‖latticeChar ℓ x‖ = 1 := by
  simp [latticeChar, norm_prod]

theorem norm_modeSample (κ : Fin d → ℤ) : ‖modeSample (d := d) n κ‖ = 1 := by
  have h : ‖modeSample (d := d) n κ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [modeSample_apply, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos scale_pos, norm_latticeChar', mul_one, inv_pow, scale_sq]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card (Grid d n) : ℝ) = (n : ℝ) ^ d := by
      simp [LatticeTorusPlancherel.Grid, ZMod.card]
    rw [hc]
    exact mul_inv_cancel₀ (pow_pos n_pos d).ne'
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (h.trans (one_pow 2).symm)

/-- Telescoping bound for products of unimodular numbers. -/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i, ‖a i‖ = 1) (hb : ∀ i, ‖b i‖ = 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj]
    have hsplit : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, ha j, one_mul, norm_prod, Finset.prod_eq_one (fun i _ => hb i),
      mul_one]
    linarith

/-- Pointwise: on `Q_x`, `|e_κ(y) - e_κ(x/n)| ≤ 2π Σ_i |κ_i| / n`. -/
theorem mFourier_sub_sample_le (κ : Fin d → ℤ) (y : UnitAddTorus (Fin d)) :
    ‖mFourier κ y - mFourier κ (samplePt (index n y))‖ ≤ 2 * π * (∑ i, |(κ i : ℝ)|) / n := by
  have hN := n_pos (n := n)
  have hcoord : ∀ i, ‖(fourier (κ i) (y i) : ℂ) - fourier (κ i) (samplePt (index n y) i)‖ ≤
      2 * π * |(κ i : ℝ)| / n := by
    intro i
    have hy := mem_cell1_index1 (N := n) (y i)
    simp only [cell1, Set.mem_preimage, Set.mem_Ioc] at hy
    have e1 : fourier (κ i) (y i) = fourier (κ i) ((rep (y i) : ℝ) : UnitAddCircle) := by
      rw [coe_rep]
    have e2 : samplePt (index n y) i = ((((index1 n (y i)).val : ℝ) / n : ℝ) : UnitAddCircle) :=
      rfl
    rw [e2, e1, fourier_coe_eq, fourier_coe_eq]
    refine (norm_exp_sub_exp_le _ _).trans ?_
    have hd : |rep (y i) - ((index1 n (y i)).val : ℝ) / n| ≤ 1 / n := by
      rw [abs_le]
      constructor
      · have : ((index1 n (y i)).val : ℝ) / n < rep (y i) := hy.1
        have h0 : (0 : ℝ) ≤ 1 / n := by positivity
        linarith
      · have : rep (y i) ≤ (((index1 n (y i)).val : ℝ) + 1) / n := hy.2
        rw [add_div] at this
        linarith
    calc |2 * π * (κ i : ℝ) * rep (y i) - 2 * π * (κ i : ℝ) * (((index1 n (y i)).val : ℝ) / n)|
        = 2 * π * |(κ i : ℝ)| * |rep (y i) - ((index1 n (y i)).val : ℝ) / n| := by
          rw [← mul_sub, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      _ ≤ 2 * π * |(κ i : ℝ)| * (1 / n) := by gcongr
      _ = 2 * π * |(κ i : ℝ)| / n := by ring
  simp only [mFourier, ContinuousMap.coe_mk]
  refine (norm_prod_sub_prod_le univ _ _ (fun i => Circle.norm_coe _)
    (fun i => Circle.norm_coe _)).trans ?_
  calc ∑ i, ‖(fourier (κ i) (y i) : ℂ) - fourier (κ i) (samplePt (index n y) i)‖
      ≤ ∑ i, 2 * π * |(κ i : ℝ)| / n := sum_le_sum fun i _ => hcoord i
    _ = 2 * π * (∑ i, |(κ i : ℝ)|) / n := by
        rw [← Finset.sum_div, ← Finset.mul_sum]

/-- `‖𝒥(n^{-d/2} e_κ(·/n)) - e_κ‖_{L²} ≤ 2π Σ_i |κ_i| / n`. -/
theorem pcEmbedding_mode_dist_le (κ : Fin d → ℤ) :
    ‖pcEmbedding d n (modeSample n κ) - mFourierLp 2 κ‖ ≤ 2 * π * (∑ i, |(κ i : ℝ)|) / n := by
  have hs : ((scale n d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (scale_pos (n := n) (d := d)).ne'
  have hae : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin d))),
      ‖(pcEmbedding d n (modeSample n κ) - mFourierLp 2 κ) y‖ ≤
        2 * π * (∑ i, |(κ i : ℝ)|) / n := by
    filter_upwards [Lp.coeFn_sub (pcEmbedding d n (modeSample n κ)) (mFourierLp 2 κ),
      coeFn_pcEmbedding (modeSample n κ), coeFn_mFourierLp 2 κ] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    simp only [modeSample, PiLp.toLp_apply]
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul, norm_sub_rev]
    exact mFourier_sub_sample_le κ y
  have hC : 0 ≤ 2 * π * (∑ i, |(κ i : ℝ)|) / n := by positivity
  refine (Lp.norm_le_of_ae_bound hC hae).trans (le_of_eq ?_)
  simp [measureUnivNNReal]

theorem tendsto_pcEmbedding_mode (κ : Fin d → ℤ) :
    Tendsto (fun m : ℕ => pcEmbedding d (m + 1) (modeSample (m + 1) κ)) atTop
      (𝓝 (mFourierLp 2 κ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => pcEmbedding_mode_dist_le κ) ?_
  have : Tendsto (fun m : ℕ => (2 * π * ∑ i, |(κ i : ℝ)|) * (1 / ((m : ℝ) + 1)))
      atTop (𝓝 ((2 * π * ∑ i, |(κ i : ℝ)|) * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  rw [mul_zero] at this
  refine this.congr fun m => ?_
  push_cast
  ring

/-! ### Strong convergence `𝒥 𝒥^* → I` -/

section adjoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- `W^* W = 1` for an isometry. -/
theorem adjoint_apply_self (W : E →ₗᵢ[ℂ] F) (x : E) :
    ContinuousLinearMap.adjoint W.toContinuousLinearMap (W x) = x := by
  apply ext_inner_right ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact W.inner_map_map x v

/-- **Best approximation.** For an isometry `W`, `W W^*` is the orthogonal projection onto the
range of `W`: `‖f - W W^* f‖ ≤ ‖f - W g‖` for every `g`. -/
theorem norm_sub_adjoint_le (W : E →ₗᵢ[ℂ] F) (f : F) (g : E) :
    ‖f - W (ContinuousLinearMap.adjoint W.toContinuousLinearMap f)‖ ≤ ‖f - W g‖ := by
  set A := ContinuousLinearMap.adjoint W.toContinuousLinearMap
  set r := f - W (A f)
  have horth : ∀ e : E, ⟪W e, r⟫_ℂ = 0 := by
    intro e
    have : ⟪W e, r⟫_ℂ = ⟪e, A r⟫_ℂ := by
      rw [ContinuousLinearMap.adjoint_inner_right]; rfl
    rw [this]
    have hAr : A r = 0 := by
      simp only [r, map_sub, A, adjoint_apply_self, sub_self]
    rw [hAr, inner_zero_right]
  have hdecomp : f - W g = r + W (A f - g) := by
    simp only [r, map_sub]; abel
  have hsq : ‖f - W g‖ ^ 2 = ‖r‖ ^ 2 + ‖W (A f - g)‖ ^ 2 := by
    rw [hdecomp]
    have h0 : ⟪r, W (A f - g)⟫_ℂ = 0 := by
      rw [← inner_conj_symm, horth, map_zero]
    rw [sq, sq, sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero r _ h0
  have : ‖r‖ ^ 2 ≤ ‖f - W g‖ ^ 2 := by rw [hsq]; nlinarith [sq_nonneg ‖W (A f - g)‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

theorem norm_adjoint_apply_le (W : E →ₗᵢ[ℂ] F) (f : F) :
    ‖ContinuousLinearMap.adjoint W.toContinuousLinearMap f‖ ≤ ‖f‖ := by
  calc _ ≤ ‖ContinuousLinearMap.adjoint W.toContinuousLinearMap‖ * ‖f‖ :=
        ContinuousLinearMap.le_opNorm _ f
    _ ≤ 1 * ‖f‖ := by
        gcongr
        rw [LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint]
        exact W.norm_toContinuousLinearMap_le
    _ = ‖f‖ := one_mul _

/-- Strong convergence of uniformly bounded operators extends from a set with dense span. -/
theorem tendsto_apply_of_dense_span {T : ℕ → F →L[ℂ] F} {C : ℝ}
    (hT : ∀ m, ‖T m‖ ≤ C) (S : Set F)
    (hS : (Submodule.span ℂ S).topologicalClosure = ⊤)
    (hconv : ∀ s ∈ S, Tendsto (fun m => T m s) atTop (𝓝 s)) (f : F) :
    Tendsto (fun m => T m f) atTop (𝓝 f) := by
  have hspan : ∀ g ∈ Submodule.span ℂ S, Tendsto (fun m => T m g) atTop (𝓝 g) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => exact hconv x hx
    | zero => simp
    | add x y _ _ hx hy => simpa using hx.add hy
    | smul a x _ hx => simpa using hx.const_smul a
  have hC : 0 ≤ C := (norm_nonneg _).trans (hT 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hdense : f ∈ closure (Submodule.span ℂ S : Set F) := by
    rw [← Submodule.topologicalClosure_coe, hS]; trivial
  rw [Metric.mem_closure_iff] at hdense
  obtain ⟨g, hg, hfg⟩ := hdense (ε / (2 * (C + 1))) (by positivity)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 (hspan g hg) (ε / 2) (half_pos hε)
  refine ⟨M, fun m hm => ?_⟩
  have h1 : dist (T m f) (T m g) ≤ C * dist f g := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hT m)
  have h2 := hM m hm
  have hδ' : (C + 1) * dist f g < ε / 2 := by
    have := mul_lt_mul_of_pos_left hfg (by positivity : (0 : ℝ) < C + 1)
    calc _ < (C + 1) * (ε / (2 * (C + 1))) := this
      _ = ε / 2 := by field_simp
  calc dist (T m f) f ≤ dist (T m f) (T m g) + dist (T m g) g + dist g f :=
        dist_triangle4 _ _ _ _
    _ ≤ C * dist f g + dist (T m g) g + dist f g := by
        rw [dist_comm g f]; gcongr
    _ = (C + 1) * dist f g + dist (T m g) g := by ring
    _ < ε / 2 + ε / 2 := add_lt_add hδ' h2
    _ = ε := by ring

end adjoint

/-- `‖𝒥 𝒥^*‖ ≤ 1`. -/
theorem norm_pcProj_le (d n : ℕ) [NeZero n] :
    ‖(pcEmbedding d n).toContinuousLinearMap ∘L
      ContinuousLinearMap.adjoint (pcEmbedding d n).toContinuousLinearMap‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map, one_mul]
  exact norm_adjoint_apply_le _ f

/-- **(A1) for the cell embedding**: `𝒥⁰_h (𝒥⁰_h)^* f → f` for every `f ∈ L²(𝕋ᵈ)`. -/
theorem tendsto_pcEmbedding_adjoint (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
    Tendsto (fun m : ℕ => pcEmbedding d (m + 1)
      (ContinuousLinearMap.adjoint (pcEmbedding d (m + 1)).toContinuousLinearMap f)) atTop
      (𝓝 f) := by
  have h := tendsto_apply_of_dense_span
    (T := fun m : ℕ => (pcEmbedding d (m + 1)).toContinuousLinearMap ∘L
      ContinuousLinearMap.adjoint (pcEmbedding d (m + 1)).toContinuousLinearMap)
    (C := 1) (fun m => norm_pcProj_le d (m + 1)) (Set.range (mFourierLp 2))
    (span_mFourierLp_closure_eq_top (by norm_num)) ?_ f
  · simpa using h
  rintro _ ⟨κ, rfl⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hm := tendsto_pcEmbedding_mode (d := d) κ
  rw [tendsto_iff_norm_sub_tendsto_zero] at hm
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hm
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [norm_sub_rev, norm_sub_rev (pcEmbedding d (m + 1) _)]
  exact norm_sub_adjoint_le _ _ _

/-! ### Translation by one cell -/

/-- The translation vector `e_j / n`. -/
def shiftVec (n : ℕ) (j : Fin d) : UnitAddTorus (Fin d) :=
  Pi.single j (((n : ℝ)⁻¹ : ℝ) : UnitAddCircle)

/-- `index(t + 1/n) = index(t) + 1` on the circle. -/
theorem index1_add_inv (t : UnitAddCircle) :
    index1 n (t + (((n : ℝ)⁻¹ : ℝ) : UnitAddCircle)) = index1 n t + 1 := by
  have hN := n_pos (n := n)
  obtain ⟨r0, r1⟩ := rep_mem t
  set r := rep t with hr
  set c := ⌈(n : ℝ) * r⌉ with hc
  have hc1 : 1 ≤ c := by rw [hc, Int.one_le_ceil_iff]; positivity
  have hcN : c ≤ n := by rw [hc, Int.ceil_le]; push_cast; nlinarith
  have hval : index1 n t = (((c - 1).toNat : ℕ) : ZMod n) := by
    unfold index1; rw [← hr, ← hc]
  have ht : t = ((r : ℝ) : UnitAddCircle) := (coe_rep t).symm
  rw [hval]
  by_cases hcase : r + (n : ℝ)⁻¹ ≤ 1
  · have hpos : 0 < r + (n : ℝ)⁻¹ := by positivity
    have hsum : t + (((n : ℝ)⁻¹ : ℝ) : UnitAddCircle) =
        ((r + (n : ℝ)⁻¹ : ℝ) : UnitAddCircle) := by
      rw [ht, ← AddCircle.coe_add]
    have hrep : rep (t + (((n : ℝ)⁻¹ : ℝ) : UnitAddCircle)) = r + (n : ℝ)⁻¹ := by
      rw [hsum]; exact rep_coe ⟨hpos, hcase⟩
    unfold index1
    rw [hrep]
    have hceil : ⌈(n : ℝ) * (r + (n : ℝ)⁻¹)⌉ = c + 1 := by
      rw [mul_add, mul_inv_cancel₀ hN.ne', hc]
      exact Int.ceil_add_one _
    rw [hceil, add_sub_cancel_right]
    have h1 : c.toNat = (c - 1).toNat + 1 := by omega
    rw [h1]
    push_cast
    ring
  · push Not at hcase
    have hlt : (n : ℝ) - 1 < (n : ℝ) * r := by
      have := mul_lt_mul_of_pos_left hcase hN
      rw [mul_add, mul_inv_cancel₀ hN.ne', mul_one] at this
      linarith
    have hcn : c = n := by
      refine le_antisymm hcN ?_
      have h2 : ((n : ℤ) : ℝ) - 1 < c := by
        push_cast
        exact hlt.trans_le (Int.le_ceil _)
      have : ((n : ℤ) - 1 : ℤ) < c := by exact_mod_cast h2
      omega
    have hpos : 0 < r + (n : ℝ)⁻¹ - 1 := by linarith
    have hle : r + (n : ℝ)⁻¹ - 1 ≤ 1 := by
      have : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
      linarith
    have hsum : t + (((n : ℝ)⁻¹ : ℝ) : UnitAddCircle) =
        ((r + (n : ℝ)⁻¹ - 1 : ℝ) : UnitAddCircle) := by
      rw [ht, ← AddCircle.coe_add, AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
    have hrep : rep (t + (((n : ℝ)⁻¹ : ℝ) : UnitAddCircle)) = r + (n : ℝ)⁻¹ - 1 := by
      rw [hsum]; exact rep_coe ⟨hpos, hle⟩
    unfold index1
    rw [hrep]
    have hceil : ⌈(n : ℝ) * (r + (n : ℝ)⁻¹ - 1)⌉ = 1 := by
      rw [mul_sub, mul_add, mul_inv_cancel₀ hN.ne', mul_one, Int.ceil_eq_iff]
      constructor
      · push_cast; linarith
      · push_cast
        have : (n : ℝ) * r ≤ n := by nlinarith
        linarith
    rw [hceil, hcn]
    simp only [sub_self, Int.toNat_zero, Nat.cast_zero]
    have h1 : ((n : ℤ) - 1).toNat + 1 = n := by
      have := Nat.pos_of_ne_zero (NeZero.ne n); omega
    have h2 : ((((n : ℤ) - 1).toNat : ℕ) : ZMod n) + 1 = ((n : ℕ) : ZMod n) := by
      have h3 : ((((n : ℤ) - 1).toNat + 1 : ℕ) : ZMod n) = ((n : ℕ) : ZMod n) := by rw [h1]
      rw [Nat.cast_add, Nat.cast_one] at h3
      exact h3
    rw [h2, ZMod.natCast_self]

theorem index_add_shiftVec (y : UnitAddTorus (Fin d)) (j : Fin d) :
    index n (y + shiftVec n j) = index n y + Pi.single j 1 := by
  funext i
  simp only [index, Pi.add_apply, shiftVec]
  by_cases hij : i = j
  · subst hij
    simp only [Pi.single_eq_same]
    exact index1_add_inv (y i)
  · simp only [Pi.single_eq_of_ne hij, add_zero]

theorem mFourier_add_apply' (k : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
    mFourier k (x + y) = mFourier k x * mFourier k y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

theorem mFourier_shiftVec (k : Fin d → ℤ) (j : Fin d) :
    mFourier k (shiftVec n j) = latticeChar (zcast n k) (Pi.single j 1) := by
  rw [latticeChar_single]
  simp only [mFourier, ContinuousMap.coe_mk, shiftVec, zcast]
  rw [Finset.prod_eq_single j]
  · rw [Pi.single_eq_same, fourier_coe_apply, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    field_simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, fourier_apply, smul_zero, AddCircle.toCircle_zero, Circle.coe_one]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ### Cell averages of modes -/

/-- The cell coefficient `⟪φ_x, e_k⟫ = n^{d/2} ∫_{Q_x} e_k`. -/
theorem inner_cellFn_mode (x : Grid d n) (k : Fin d → ℤ) :
    ⟪cellFn x, mFourierLp 2 k⟫_ℂ =
      ∫ y, (cell x).indicator (fun y => ((scale n d : ℝ) : ℂ) * mFourier k y) y := by
  rw [cellFn, L2.inner_indicatorConstLp_eq_setIntegral_inner, ← integral_indicator
    (measurableSet_cell x)]
  refine integral_congr_ae ((coeFn_mFourierLp 2 k).mono fun y hy => ?_)
  by_cases hy' : y ∈ cell x
  · simp only [Set.indicator_of_mem hy', hy, RCLike.inner_apply', Complex.conj_ofReal]
  · simp only [Set.indicator_of_notMem hy']

theorem inner_cellFn_mode_add (x : Grid d n) (k : Fin d → ℤ) (j : Fin d) :
    ⟪cellFn (x + Pi.single j 1), mFourierLp 2 k⟫_ℂ =
      latticeChar (zcast n k) (Pi.single j 1) * ⟪cellFn x, mFourierLp 2 k⟫_ℂ := by
  rw [inner_cellFn_mode, inner_cellFn_mode, ← integral_const_mul]
  rw [← integral_add_left_eq_self (μ := (volume : Measure (UnitAddTorus (Fin d))))
    ((cell (x + Pi.single j 1)).indicator
      (fun y => ((scale n d : ℝ) : ℂ) * mFourier k y)) (shiftVec n j)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [add_comm (shiftVec n j) y]
  have hiff : y + shiftVec n j ∈ cell (x + Pi.single j 1) ↔ y ∈ cell x := by
    rw [mem_cell_iff, mem_cell_iff, index_add_shiftVec, add_left_inj]
  by_cases hy : y ∈ cell x
  · rw [Set.indicator_of_mem (hiff.2 hy), Set.indicator_of_mem hy, mFourier_add_apply',
      mFourier_shiftVec]
    ring
  · rw [Set.indicator_of_notMem (fun h => hy (hiff.1 h)), Set.indicator_of_notMem hy, mul_zero]

/-- The coordinates of `𝒥^* f` are the cell coefficients. -/
theorem pcEmbedding_adjoint_apply (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d))))
    (x : Grid d n) :
    (ContinuousLinearMap.adjoint (pcEmbedding d n).toContinuousLinearMap f) x =
      ⟪cellFn x, f⟫_ℂ := by
  have h1 : pcEmbedding d n (EuclideanSpace.single x 1) = cellFn x := by
    rw [pcEmbedding_apply, sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · simp
  have h2 := ContinuousLinearMap.adjoint_inner_right (pcEmbedding d n).toContinuousLinearMap
    (EuclideanSpace.single x 1) f
  rw [EuclideanSpace.inner_single_left, map_one, one_mul] at h2
  rw [h2, LinearIsometry.coe_toContinuousLinearMap, h1]

/-! ### Lattice plane waves -/

/-- DFT inversion on the lattice torus: `u(x) = Σ_ℓ e(ℓ·x) û(ℓ)`. -/
theorem dft_inversion' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Grid d n → E) (x : Grid d n) : ∑ ℓ, latticeChar ℓ x • dft u ℓ = u x := by
  have hn : ((n : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne n))
  unfold dft
  simp only [smul_sum, smul_smul]
  rw [sum_comm]
  have hrow : ∀ y : Grid d n, ∑ ℓ : Grid d n, (latticeChar ℓ x * (((n : ℂ) ^ d)⁻¹ *
      conj (latticeChar ℓ y))) • u y =
      (((n : ℂ) ^ d)⁻¹ * ∑ ℓ : Grid d n, latticeChar ℓ (x - y)) • u y := by
    intro y
    rw [← sum_smul, mul_sum]
    congr 1
    refine sum_congr rfl fun ℓ _ => ?_
    rw [latticeChar_sub_right]
    ring
  simp only [hrow, sum_latticeChar, sub_eq_zero]
  rw [Finset.sum_eq_single x]
  · rw [ite_eq_left rfl, inv_mul_cancel₀ hn, one_smul]
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

/-- A lattice function that is multiplied by `e(ℓ_j)` under every unit shift is a multiple of
the plane wave `e(ℓ·x)`. -/
theorem eq_latticeChar_mul_of_shift (ℓ : Grid d n) (a : Grid d n → ℂ)
    (ha : ∀ x j, a (x + Pi.single j 1) = latticeChar ℓ (Pi.single j 1) * a x) (x : Grid d n) :
    a x = latticeChar ℓ x * a 0 := by
  have hdft : ∀ m, m ≠ ℓ → dft a m = 0 := by
    intro m hm
    obtain ⟨j, hj⟩ : ∃ j, m j ≠ ℓ j := by
      by_contra hc; push Not at hc; exact hm (funext hc)
    have h1 := dft_shift a j m
    have h2 : shift j a = latticeChar ℓ (Pi.single j 1) • a := by
      funext y; simp [shift, ha]
    rw [h2, dft_smul, latticeChar_single] at h1
    have hne : ZMod.stdAddChar (ℓ j) ≠ ZMod.stdAddChar (m j) := fun h =>
      hj (ZMod.injective_stdAddChar h).symm
    have : (ZMod.stdAddChar (ℓ j) - ZMod.stdAddChar (m j)) * dft a m = 0 := by
      rw [smul_eq_mul, smul_eq_mul] at h1
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have hinv : ∀ y, a y = latticeChar ℓ y * dft a ℓ := by
    intro y
    rw [← dft_inversion' a y, Finset.sum_eq_single ℓ]
    · rfl
    · intro m _ hm; rw [hdft m hm, smul_zero]
    · simp
  rw [hinv x, hinv 0, latticeChar_zero_right, one_mul]

/-- The factor `γ_n(κ) = n^{d/2} ⟪φ_0, e_κ⟫` (`= n^d ∫_{Q_0} e_κ`). -/
def modeFactor (n : ℕ) [NeZero n] (κ : Fin d → ℤ) : ℂ :=
  ((scale n d : ℝ) : ℂ) * ⟪cellFn (0 : Grid d n), mFourierLp 2 κ⟫_ℂ

/-- **The cell averages of a mode are a lattice plane wave**:
`𝒥^* e_κ = γ_n(κ) · modeSample κ`. -/
theorem pcEmbedding_adjoint_mode (κ : Fin d → ℤ) :
    ContinuousLinearMap.adjoint (pcEmbedding d n).toContinuousLinearMap (mFourierLp 2 κ) =
      modeFactor n κ • modeSample n κ := by
  have hs : ((scale n d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (scale_pos (n := n) (d := d)).ne'
  ext x
  rw [pcEmbedding_adjoint_apply, PiLp.smul_apply, modeSample_apply, smul_eq_mul, modeFactor]
  rw [eq_latticeChar_mul_of_shift (zcast n κ) (fun x => ⟪cellFn x, mFourierLp 2 κ⟫_ℂ)
    (fun x j => inner_cellFn_mode_add x κ j) x]
  field_simp

theorem tendsto_modeFactor (κ : Fin d → ℤ) :
    Tendsto (fun m : ℕ => modeFactor (d := d) (m + 1) κ) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hA := tendsto_pcEmbedding_adjoint (d := d) (mFourierLp 2 κ)
  have hB := tendsto_pcEmbedding_mode (d := d) κ
  rw [tendsto_iff_norm_sub_tendsto_zero] at hA hB
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) (by simpa using hA.add hB)
  have hnorm : ‖pcEmbedding d (m + 1) (modeSample (m + 1) κ)‖ = 1 := by
    rw [LinearIsometry.norm_map, norm_modeSample]
  calc ‖modeFactor (m + 1) κ - 1‖
      = ‖(modeFactor (m + 1) κ - 1) • pcEmbedding d (m + 1) (modeSample (m + 1) κ)‖ := by
        rw [norm_smul, hnorm, mul_one]
    _ = ‖(pcEmbedding d (m + 1) (ContinuousLinearMap.adjoint
          (pcEmbedding d (m + 1)).toContinuousLinearMap (mFourierLp 2 κ)) - mFourierLp 2 κ) +
          (mFourierLp 2 κ - pcEmbedding d (m + 1) (modeSample (m + 1) κ))‖ := by
        rw [pcEmbedding_adjoint_mode, LinearIsometry.map_smul, sub_smul, one_smul]
        congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ = _ := by rw [norm_sub_rev (mFourierLp 2 κ)]

/-! ### Aliasing and orthogonality of the interpolation errors -/

theorem inner_modeSample (k κ : Fin d → ℤ) :
    ⟪modeSample (d := d) n k, modeSample n κ⟫_ℂ = if zcast n k = zcast n κ then 1 else 0 := by
  have hs : ((scale n d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (scale_pos (n := n) (d := d)).ne'
  have hsq : (((scale n d : ℝ) : ℂ) ^ 2) = ((n : ℂ) ^ d) := by
    have := congrArg Complex.ofReal (scale_sq (n := n) (d := d))
    push_cast at this
    exact this
  have hexp : ⟪modeSample (d := d) n k, modeSample n κ⟫_ℂ =
      (((scale n d : ℝ) : ℂ) ^ 2)⁻¹ * ∑ x : Grid d n, latticeChar (zcast n κ - zcast n k) x := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, mul_sum]
    simp only [dotProduct]
    refine sum_congr rfl fun x _ => ?_
    simp only [modeSample_apply, Pi.star_apply, star_mul', RCLike.star_def, map_inv₀,
      Complex.conj_ofReal]
    rw [latticeChar_comm (zcast n κ - zcast n k) x, latticeChar_sub_right,
      latticeChar_comm x (zcast n κ), latticeChar_comm x (zcast n k)]
    field_simp
  have hsum : ∑ x : Grid d n, latticeChar (zcast n κ - zcast n k) x =
      ∑ x : Grid d n, latticeChar x (zcast n κ - zcast n k) :=
    sum_congr rfl fun x _ => latticeChar_comm _ _
  rw [hexp, hsum, sum_latticeChar]
  by_cases h : zcast n k = zcast n κ
  · have h' : zcast n κ - zcast n k = 0 := by rw [h, sub_self]
    rw [ite_eq_left h', ite_eq_left h, hsq]
    exact inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne n)))
  · have h' : zcast n κ - zcast n k ≠ 0 := fun e => h (sub_eq_zero.1 e).symm
    rw [ite_eq_right h', ite_eq_right h, mul_zero]

/-- **Aliasing**: `⟪e_k, 𝒥 (modeSample κ)⟫ = 0` unless `k ≡ κ (mod n)`. -/
theorem inner_mode_pcEmbedding_modeSample_eq_zero (k κ : Fin d → ℤ)
    (h : zcast n k ≠ zcast n κ) :
    ⟪mFourierLp 2 k, pcEmbedding d n (modeSample n κ)⟫_ℂ = 0 := by
  rw [← LinearIsometry.coe_toContinuousLinearMap, ← ContinuousLinearMap.adjoint_inner_left,
    pcEmbedding_adjoint_mode, inner_smul_left, inner_modeSample, ite_eq_right h, mul_zero]

/-- The signed representative `ℓ̃ ∈ (-n/2, n/2]ᵈ` of a grid frequency. -/
def signedRep (ℓ : Grid d n) : Fin d → ℤ := fun i => (ℓ i).valMinAbs

theorem zcast_signedRep (ℓ : Grid d n) : zcast n (signedRep ℓ) = ℓ := by
  funext i; exact ZMod.coe_valMinAbs (ℓ i)

theorem abs_signedRep_le (ℓ : Grid d n) (i : Fin d) : |(signedRep ℓ i : ℝ)| * 2 ≤ n := by
  have h := (ℓ i).valMinAbs_mem_Ioc
  have h2 : |(ℓ i).valMinAbs| * 2 ≤ (n : ℤ) := by
    rcases h with ⟨h1, h2⟩
    rcases abs_cases (ℓ i).valMinAbs with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> omega
  unfold signedRep
  exact_mod_cast h2

/-- The interpolation error of the grid frequency `ℓ`: `e_{ℓ̃} - 𝒥(modeSample ℓ̃)`. -/
def modeError (ℓ : Grid d n) : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d))) :=
  mFourierLp 2 (signedRep ℓ) - pcEmbedding d n (modeSample n (signedRep ℓ))

theorem norm_modeError_le (ℓ : Grid d n) :
    ‖modeError ℓ‖ ≤ 2 * π * (∑ i, |(signedRep ℓ i : ℝ)|) / n := by
  rw [modeError, norm_sub_rev]
  exact pcEmbedding_mode_dist_le _

/-- **Orthogonality of the interpolation errors of distinct grid frequencies.** -/
theorem inner_modeError_eq_zero {ℓ ℓ' : Grid d n} (h : ℓ ≠ ℓ') :
    ⟪modeError ℓ, modeError ℓ'⟫_ℂ = 0 := by
  have hz : zcast n (signedRep ℓ) ≠ zcast n (signedRep ℓ') := by
    rwa [zcast_signedRep, zcast_signedRep]
  have hk : signedRep ℓ ≠ signedRep ℓ' := fun e => hz (by rw [e])
  have h1 : ⟪mFourierLp 2 (signedRep ℓ), mFourierLp 2 (signedRep ℓ')⟫_ℂ = 0 := by
    have := orthonormal_mFourier (d := Fin d)
    rw [orthonormal_iff_ite] at this
    rw [this, ite_eq_right hk]
  have h2 := inner_mode_pcEmbedding_modeSample_eq_zero (n := n) _ _ hz
  have h3 : ⟪pcEmbedding d n (modeSample n (signedRep ℓ)),
      mFourierLp 2 (signedRep ℓ')⟫_ℂ = 0 := by
    rw [← inner_conj_symm, inner_mode_pcEmbedding_modeSample_eq_zero _ _ (Ne.symm hz), map_zero]
  have h4 : ⟪pcEmbedding d n (modeSample n (signedRep ℓ)),
      pcEmbedding d n (modeSample n (signedRep ℓ'))⟫_ℂ = 0 := by
    rw [LinearIsometry.inner_map_map, inner_modeSample, ite_eq_right hz]
  rw [modeError, modeError, inner_sub_left, inner_sub_right, inner_sub_right, h1, h2, h3, h4]
  simp

/-- **Pythagoras for the interpolation errors**: `‖Σ_ℓ c_ℓ w_ℓ‖² = Σ_ℓ |c_ℓ|² ‖w_ℓ‖²`. -/
theorem norm_sum_modeError_sq (c : Grid d n → ℂ) :
    ‖∑ ℓ, c ℓ • modeError ℓ‖ ^ 2 = ∑ ℓ, ‖c ℓ‖ ^ 2 * ‖modeError ℓ‖ ^ 2 := by
  have hdiag : ⟪∑ ℓ, c ℓ • modeError ℓ, ∑ ℓ, c ℓ • modeError ℓ⟫_ℂ =
      ∑ ℓ, ⟪c ℓ • modeError ℓ, c ℓ • modeError ℓ⟫_ℂ := by
    rw [sum_inner]
    refine sum_congr rfl fun ℓ _ => ?_
    rw [inner_sum, Finset.sum_eq_single ℓ]
    · intro ℓ' _ hℓ'
      rw [inner_smul_left, inner_smul_right, inner_modeError_eq_zero (Ne.symm hℓ'), mul_zero,
        mul_zero]
    · simp
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hdiag, map_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [inner_self_eq_norm_sq (𝕜 := ℂ), norm_smul, mul_pow]

end RenewalGeometry.TorusCellEmbedding
