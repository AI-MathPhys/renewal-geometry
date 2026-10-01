/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridInterpolation

/-!
# Piecewise-constant embedding of periodic grid functions into `L²(𝕋³)`

The unit torus `𝕋³ = UnitAddTorus (Fin 3)` carries Mathlib's Haar probability measure (the
measure of `Mathlib.Analysis.Fourier.AddCircleMulti`).  For a mesh `h = 1/N` the grid point
`x ∈ (ℤ/N)³` owns the cell `Q_x = Π_i (x_i/N, (x_i + 1)/N]` (`cell`); the cells are measurable,
pairwise disjoint, cover the torus and have measure `N⁻³`.

* `pcEmbedding N : EuclideanSpace ℂ (Grid N) →ₗᵢ[ℂ] L²(𝕋³)` sends `f` to the piecewise-constant
  function equal to `N^{3/2} f(x)` on `Q_x`.  With the vertex mass `m_h = h³` this is exactly the
  natural piecewise-constant embedding `L²(V_h, m_h) → L²(𝕋³)` (`f ↦ Σ_x f(x) 1_{Q_x}`) composed
  with the unitary rescaling `ℓ²(V_h) ≅ L²(V_h, h³)`.
* `pcEmbedding_mode_dist_le`: the embedded grid sample of a Fourier mode `e_κ` is within
  `2π Σ_i |κ_i| / N` of `e_κ` in `L²`; hence the samples converge strongly to `e_κ`.
-/

open MeasureTheory Set Finset ComplexConjugate UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.TorusPiecewiseConstant

open PeriodicGridSobolev LatticeTorusPlancherel

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### One-dimensional cells -/

/-- The representative of a point of the unit circle in `(0, 1]`. -/
noncomputable def rep (t : UnitAddCircle) : ℝ := (AddCircle.equivIoc 1 0 t : ℝ)

theorem rep_mem (t : UnitAddCircle) : rep t ∈ Ioc (0 : ℝ) 1 := by
  have := (AddCircle.equivIoc 1 0 t).2
  simp only [zero_add] at this
  exact this

theorem coe_rep (t : UnitAddCircle) : ((rep t : ℝ) : UnitAddCircle) = t :=
  AddCircle.coe_equivIoc

theorem rep_coe {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) : rep (s : UnitAddCircle) = s := by
  unfold rep
  rw [AddCircle.equivIoc_coe_of_mem (by simpa using hs)]

theorem measurable_rep : Measurable rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 0).measurable

variable {N : ℕ} [NeZero N]

/-- The one-dimensional cell `(j/N, (j+1)/N]` of the grid index `j`. -/
def cell1 (N : ℕ) (j : ZMod N) : Set UnitAddCircle :=
  rep ⁻¹' Ioc ((j.val : ℝ) / N) (((j.val : ℝ) + 1) / N)

theorem measurableSet_cell1 (j : ZMod N) : MeasurableSet (cell1 N j) :=
  measurable_rep measurableSet_Ioc

theorem haar_eq_volume_global (U : Set UnitAddCircle) :
    (volume : Measure UnitAddCircle) U = (@volume _ (AddCircle.measureSpace 1)) U := by
  change AddCircle.haarAddCircle U = _
  rw [show (@volume _ (AddCircle.measureSpace 1)) =
    ENNReal.ofReal 1 • AddCircle.haarAddCircle from AddCircle.volume_eq_smul_haarAddCircle]
  simp

theorem volume_cell1 (j : ZMod N) : volume (cell1 N j) = ENNReal.ofReal (1 / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hj : (j.val : ℝ) + 1 ≤ N := by exact_mod_cast j.val_lt
  rw [haar_eq_volume_global, AddCircle.add_projection_respects_measure 1 0 (measurableSet_cell1 j)]
  have hset : ((↑) : ℝ → UnitAddCircle) ⁻¹' cell1 N j ∩ Ioc 0 (0 + 1) =
      Ioc ((j.val : ℝ) / N) (((j.val : ℝ) + 1) / N) := by
    ext s
    simp only [cell1, Set.mem_inter_iff, Set.mem_preimage, zero_add]
    constructor
    · rintro ⟨h1, h2⟩
      rwa [rep_coe h2] at h1
    · intro h
      have h0 : (0 : ℝ) ≤ (j.val : ℝ) / N := by positivity
      have hs : s ∈ Ioc (0 : ℝ) 1 := by
        refine ⟨lt_of_le_of_lt h0 h.1, h.2.trans ?_⟩
        rw [div_le_one hN]; exact hj
      exact ⟨by rw [rep_coe hs]; exact h, hs⟩
  rw [hset, Real.volume_Ioc]
  congr 1
  field_simp
  ring

theorem cell1_disjoint {j j' : ZMod N} (h : j ≠ j') : Disjoint (cell1 N j) (cell1 N j') := by
  rw [Set.disjoint_left]
  intro t h1 h2
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  simp only [cell1, Set.mem_preimage, Set.mem_Ioc] at h1 h2
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  rw [div_lt_iff₀ hN] at a1 b1
  rw [le_div_iff₀ hN] at a2 b2
  apply h
  apply ZMod.val_injective
  have e1 : (j.val : ℝ) < j'.val + 1 := by linarith
  have e2 : (j'.val : ℝ) < j.val + 1 := by linarith
  have e1' : j.val < j'.val + 1 := by exact_mod_cast e1
  have e2' : j'.val < j.val + 1 := by exact_mod_cast e2
  omega

/-- The grid index of a point of the circle: `⌈N rep t⌉ - 1`. -/
noncomputable def index1 (N : ℕ) (t : UnitAddCircle) : ZMod N :=
  ((⌈(N : ℝ) * rep t⌉ - 1).toNat : ZMod N)

theorem mem_cell1_index1 (t : UnitAddCircle) : t ∈ cell1 N (index1 N t) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨r0, r1⟩ := rep_mem t
  set c := ⌈(N : ℝ) * rep t⌉ with hc
  have hc1 : 1 ≤ c := by
    rw [hc, Int.one_le_ceil_iff]; positivity
  have hcN : c ≤ N := by
    rw [hc, Int.ceil_le]; push_cast; nlinarith
  have hm : ((c - 1).toNat : ℤ) = c - 1 := Int.toNat_of_nonneg (by omega)
  have hlt : (c - 1).toNat < N := by omega
  have hval : (index1 N t).val = (c - 1).toNat := by
    unfold index1
    rw [← hc, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  simp only [cell1, Set.mem_preimage, Set.mem_Ioc, hval]
  have hmR : (((c - 1).toNat : ℕ) : ℝ) = (c : ℝ) - 1 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hm
    push_cast at this ⊢
    linarith
  rw [hmR, div_lt_iff₀ hN, le_div_iff₀ hN]
  constructor
  · have := Int.ceil_lt_add_one ((N : ℝ) * rep t)
    rw [← hc] at this
    linarith
  · have := Int.le_ceil ((N : ℝ) * rep t)
    rw [← hc] at this
    linarith

/-! ### Three-dimensional cells -/

/-- The cell `Q_x = Π_i (x_i/N, (x_i + 1)/N]` of the grid point `x`. -/
def cell (x : Grid N) : Set (UnitAddTorus (Fin 3)) := Set.pi univ fun i => cell1 N (x i)

theorem measurableSet_cell (x : Grid N) : MeasurableSet (cell x) :=
  MeasurableSet.univ_pi fun i => measurableSet_cell1 (x i)

theorem volume_cell (x : Grid N) : volume (cell x) = ENNReal.ofReal (1 / N) ^ 3 := by
  rw [cell, volume_pi_pi]
  simp [volume_cell1, Fin.prod_univ_three, pow_three]

theorem volume_cell_ne_top (x : Grid N) : volume (cell x) ≠ ∞ := by
  rw [volume_cell]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

theorem volume_real_cell (x : Grid N) : volume.real (cell x) = ((N : ℝ) ^ 3)⁻¹ := by
  rw [measureReal_def, volume_cell, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  field_simp

theorem cell_disjoint {x y : Grid N} (h : x ≠ y) : Disjoint (cell x) (cell y) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra hc; push Not at hc; exact h (funext hc)
  rw [Set.disjoint_left]
  intro z hz hz'
  exact Set.disjoint_left.mp (cell1_disjoint hi) (hz i (mem_univ i)) (hz' i (mem_univ i))

/-- The grid index of a point of the torus. -/
noncomputable def index (N : ℕ) (y : UnitAddTorus (Fin 3)) : Grid N := fun i => index1 N (y i)

theorem mem_cell_index (y : UnitAddTorus (Fin 3)) : y ∈ cell (index N y) :=
  fun i _ => mem_cell1_index1 (y i)

theorem mem_cell_iff (x : Grid N) (y : UnitAddTorus (Fin 3)) : y ∈ cell x ↔ index N y = x := by
  constructor
  · intro hy
    by_contra hne
    exact Set.disjoint_left.mp (cell_disjoint hne) (mem_cell_index y) hy
  · rintro rfl; exact mem_cell_index y

/-! ### The isometric embedding -/

/-- The normalised cell indicator `φ_x = N^{3/2} 1_{Q_x}`. -/
noncomputable def cellFn (x : Grid N) : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) :=
  indicatorConstLp 2 (measurableSet_cell x) (volume_cell_ne_top x) ((Real.sqrt N ^ 3 : ℝ) : ℂ)

theorem orthonormal_cellFn : Orthonormal ℂ (cellFn (N := N)) := by
  rw [orthonormal_iff_ite]
  intro x y
  rw [cellFn, cellFn, L2.inner_indicatorConstLp_indicatorConstLp]
  have hs : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  split_ifs with hxy
  · subst hxy
    have hr : (Real.sqrt N ^ 3) ^ 2 = (N : ℝ) ^ 3 := by
      rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, hs]
    rw [Set.inter_self, volume_real_cell, inner_self_eq_norm_sq_to_K, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.real_smul]
    have key : ((N : ℝ) ^ 3)⁻¹ * (Real.sqrt N ^ 3) ^ 2 = (1 : ℝ) := by
      rw [hr]; field_simp
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) key
    simp only [Complex.ofReal_mul, Complex.ofReal_one] at h2
    first
      | exact h2
      | (simpa using h2)
      | (convert h2 using 2 <;> simp)
  · rw [Set.disjoint_iff_inter_eq_empty.mp (cell_disjoint hxy)]
    simp

/-- The linear map `f ↦ Σ_x f(x) φ_x`. -/
noncomputable def pcLinear (N : ℕ) [NeZero N] :
    EuclideanSpace ℂ (Grid N) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) where
  toFun f := ∑ x, f x • cellFn x
  map_add' f g := by simp [add_smul, sum_add_distrib]
  map_smul' c f := by simp [smul_sum, smul_smul]

theorem pcLinear_comp_basis :
    (pcLinear N) ∘ (EuclideanSpace.basisFun (Grid N) ℂ).toBasis = cellFn := by
  funext x
  simp only [Function.comp_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    pcLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_eq_single x]
  · simp
  · intro y _ hy
    simp [PiLp.single_apply, hy]
  · simp

/-- The natural piecewise-constant embedding (isometric). -/
noncomputable def pcEmbedding (N : ℕ) [NeZero N] :
    EuclideanSpace ℂ (Grid N) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) :=
  (pcLinear N).isometryOfOrthonormal (v := (EuclideanSpace.basisFun (Grid N) ℂ).toBasis)
    (by rw [OrthonormalBasis.coe_toBasis]; exact (EuclideanSpace.basisFun _ ℂ).orthonormal)
    (by rw [pcLinear_comp_basis]; exact orthonormal_cellFn)

theorem pcEmbedding_apply (f : EuclideanSpace ℂ (Grid N)) :
    pcEmbedding N f = ∑ x, f x • cellFn x := rfl

/-- A.e. representative of a finite combination of cell functions. -/
theorem coeFn_sum_cellFn (c : Grid N → ℂ) :
    (⇑(∑ x, c x • cellFn x) : UnitAddTorus (Fin 3) → ℂ) =ᵐ[volume]
      fun y => ∑ x, c x * (cell x).indicator (fun _ => ((Real.sqrt N ^ 3 : ℝ) : ℂ)) y := by
  have key : ∀ s : Finset (Grid N), (⇑(∑ x ∈ s, c x • cellFn x) : UnitAddTorus (Fin 3) → ℂ)
      =ᵐ[volume] fun y => ∑ x ∈ s, c x *
        (cell x).indicator (fun _ => ((Real.sqrt N ^ 3 : ℝ) : ℂ)) y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [sum_empty]
      exact Lp.coeFn_zero _ _ _
    | insert a s ha ih =>
      simp only [sum_insert ha]
      have hφ : (⇑(cellFn a) : UnitAddTorus (Fin 3) → ℂ) =ᵐ[volume]
          (cell a).indicator (fun _ => ((Real.sqrt N ^ 3 : ℝ) : ℂ)) :=
        indicatorConstLp_coeFn
      filter_upwards [Lp.coeFn_add (c a • cellFn a) (∑ x ∈ s, c x • cellFn x),
        Lp.coeFn_smul (c a) (cellFn a), ih, hφ] with y h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  exact key univ

/-- The value of an embedded grid function on its cell. -/
theorem coeFn_pcEmbedding (f : EuclideanSpace ℂ (Grid N)) :
    (⇑(pcEmbedding N f) : UnitAddTorus (Fin 3) → ℂ) =ᵐ[volume]
      fun y => ((Real.sqrt N ^ 3 : ℝ) : ℂ) * f (index N y) := by
  have h := coeFn_sum_cellFn (N := N) (fun x => f x)
  rw [← pcEmbedding_apply] at h
  refine h.mono fun y hy => ?_
  rw [hy]
  dsimp only
  rw [sum_eq_single (index N y)]
  · rw [Set.indicator_of_mem (mem_cell_index y)]; ring
  · intro x _ hx
    rw [Set.indicator_of_notMem (fun h => hx ((mem_cell_iff x y).mp h).symm), mul_zero]
  · simp

/-! ### Embedded samples of Fourier modes -/

/-- The stage vector `N^{-3/2} e_κ(x/N)`: its embedding is the piecewise-constant function
equal to the sample `e_κ(x/N)` on `Q_x`. -/
noncomputable def modeSample (N : ℕ) [NeZero N] (κ : Fin 3 → ℤ) : EuclideanSpace ℂ (Grid N) :=
  WithLp.toLp 2 fun x => ((Real.sqrt N ^ 3 : ℝ) : ℂ)⁻¹ * mFourier κ (samplePt x)

theorem norm_exp_sub_exp_le (θ φ : ℝ) :
    ‖Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * φ)‖ ≤ |θ - φ| := by
  have h : Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * φ) =
      Complex.exp (Complex.I * φ) * (Complex.exp (Complex.I * ((θ - φ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq (Real.norm_eq_abs _))

theorem fourier_coe_eq (n : ℤ) (s : ℝ) :
    fourier n (s : UnitAddCircle) = Complex.exp (Complex.I * ((2 * π * n * s : ℝ) : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- Pointwise: on the cell `Q_x`, `|e_κ(y) - e_κ(x/N)| ≤ 2π Σ_i |κ_i| / N`. -/
theorem mFourier_sub_sample_le (κ : Fin 3 → ℤ) (y : UnitAddTorus (Fin 3)) :
    ‖mFourier κ y - mFourier κ (samplePt (index N y))‖ ≤
      2 * π * (∑ i, |(κ i : ℝ)|) / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- coordinatewise representatives
  have hcoord : ∀ i, ‖fourier (κ i) (y i) - fourier (κ i) (samplePt (index N y) i)‖ ≤
      2 * π * |(κ i : ℝ)| / N := by
    intro i
    have hy := mem_cell1_index1 (N := N) (y i)
    simp only [cell1, Set.mem_preimage, Set.mem_Ioc] at hy
    have e1 : fourier (κ i) (y i) = fourier (κ i) ((rep (y i) : ℝ) : UnitAddCircle) := by
      rw [coe_rep]
    have e2 : samplePt (index N y) i = ((((index1 N (y i)).val : ℝ) / N : ℝ) : UnitAddCircle) :=
      rfl
    rw [e2, e1, fourier_coe_eq, fourier_coe_eq]
    refine (norm_exp_sub_exp_le _ _).trans ?_
    have hd : |rep (y i) - ((index1 N (y i)).val : ℝ) / N| ≤ 1 / N := by
      rw [abs_le]
      constructor
      · have : ((index1 N (y i)).val : ℝ) / N < rep (y i) := hy.1
        have h0 : (0 : ℝ) ≤ 1 / N := by positivity
        linarith
      · have : rep (y i) ≤ (((index1 N (y i)).val : ℝ) + 1) / N := hy.2
        rw [add_div] at this
        linarith
    calc |2 * π * (κ i : ℝ) * rep (y i) - 2 * π * (κ i : ℝ) * (((index1 N (y i)).val : ℝ) / N)|
        = 2 * π * |(κ i : ℝ)| * |rep (y i) - ((index1 N (y i)).val : ℝ) / N| := by
          rw [← mul_sub, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      _ ≤ 2 * π * |(κ i : ℝ)| * (1 / N) := by gcongr
      _ = 2 * π * |(κ i : ℝ)| / N := by ring
  simp only [mFourier, ContinuousMap.coe_mk, Fin.prod_univ_three]
  set a0 := fourier (κ 0) (y 0)
  set a1 := fourier (κ 1) (y 1)
  set a2 := fourier (κ 2) (y 2)
  set b0 := fourier (κ 0) (samplePt (index N y) 0)
  set b1 := fourier (κ 1) (samplePt (index N y) 1)
  set b2 := fourier (κ 2) (samplePt (index N y) 2)
  have na1 : ‖(a1 : ℂ)‖ = 1 := Circle.norm_coe _
  have na2 : ‖(a2 : ℂ)‖ = 1 := Circle.norm_coe _
  have nb0 : ‖(b0 : ℂ)‖ = 1 := Circle.norm_coe _
  have nb1 : ‖(b1 : ℂ)‖ = 1 := Circle.norm_coe _
  have hsplit : (a0 : ℂ) * a1 * a2 - b0 * b1 * b2 =
      (a0 - b0) * a1 * a2 + b0 * (a1 - b1) * a2 + b0 * b1 * (a2 - b2) := by ring
  rw [hsplit]
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  calc ‖((a0 : ℂ) - b0) * a1 * a2 + b0 * (a1 - b1) * a2 + b0 * b1 * (a2 - b2)‖
      ≤ ‖((a0 : ℂ) - b0) * a1 * a2‖ + ‖(b0 : ℂ) * (a1 - b1) * a2‖ + ‖(b0 : ℂ) * b1 * (a2 - b2)‖ :=
        norm_add₃_le
    _ = ‖(a0 : ℂ) - b0‖ + ‖(a1 : ℂ) - b1‖ + ‖(a2 : ℂ) - b2‖ := by
        simp only [norm_mul, na1, na2, nb0, nb1, mul_one, one_mul]
    _ ≤ 2 * π * |(κ 0 : ℝ)| / N + 2 * π * |(κ 1 : ℝ)| / N + 2 * π * |(κ 2 : ℝ)| / N := by
        gcongr
    _ = 2 * π * (∑ i, |(κ i : ℝ)|) / N := by
        rw [Fin.sum_univ_three]; ring

/-- `‖J_N(N^{-3/2} e_κ(·/N)) - e_κ‖_{L²} ≤ 2π Σ_i |κ_i| / N`. -/
theorem pcEmbedding_mode_dist_le (κ : Fin 3 → ℤ) :
    ‖pcEmbedding N (modeSample N κ) - mFourierLp 2 κ‖ ≤ 2 * π * (∑ i, |(κ i : ℝ)|) / N := by
  have hs : ((Real.sqrt N ^ 3 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt N ^ 3 := by
      have : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
      positivity
    exact_mod_cast this.ne'
  have hae : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin 3))),
      ‖(pcEmbedding N (modeSample N κ) - mFourierLp 2 κ) y‖ ≤
        2 * π * (∑ i, |(κ i : ℝ)|) / N := by
    filter_upwards [Lp.coeFn_sub (pcEmbedding N (modeSample N κ)) (mFourierLp 2 κ),
      coeFn_pcEmbedding (modeSample N κ), coeFn_mFourierLp 2 κ] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    simp only [modeSample, PiLp.toLp_apply]
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul, norm_sub_rev]
    exact mFourier_sub_sample_le κ y
  have hC : 0 ≤ 2 * π * (∑ i, |(κ i : ℝ)|) / N := by positivity
  refine (Lp.norm_le_of_ae_bound hC hae).trans (le_of_eq ?_)
  simp [measureUnivNNReal]

theorem tendsto_pcEmbedding_mode (κ : Fin 3 → ℤ) :
    Filter.Tendsto (fun n : ℕ => pcEmbedding (n + 1) (modeSample (n + 1) κ)) Filter.atTop
      (nhds (mFourierLp 2 κ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => pcEmbedding_mode_dist_le κ) ?_
  have : Filter.Tendsto (fun n : ℕ => (2 * π * ∑ i, |(κ i : ℝ)|) * (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds ((2 * π * ∑ i, |(κ i : ℝ)|) * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  push_cast
  ring

end RenewalGeometry.TorusPiecewiseConstant
