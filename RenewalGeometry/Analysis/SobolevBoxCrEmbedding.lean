/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevTorusBridge
import RenewalGeometry.Analysis.TorusSobolevDerivatives

/-!
# The Sobolev embedding `H^m_0 ↪ C^r` for `m > r + d/2` on a slab box, by periodisation

Generic infrastructure (no renewal notions), serving the `H^{-m}` clauses of `cor:reduced-stress`
and `cor:stress-topology` of the Einstein–Standard-Model action-closure manuscript ("use
`H_0^m(K) ↪ C^{r}(K)` for `m > r + 2` in four dimensions").

## Periodic functions on `ℝ^d` and the torus

* `torusMk`, `descendFun`: a `ℤ^d`-periodic function `g` on `ℝ^d` descends to `𝕋^d`
  (`descendFun_mk`); it is continuous when `g` is (`continuous_descendFun`, `torusMk` is an open
  quotient map).
* `integral_lineDeriv_eq_zero`, `mFourierCoeff_of_isLineDeriv` (**Fourier rule** on `𝕋^d`, any
  finite index type): a continuous line derivative has coefficients `2πi nᵢ F̂(n)`.
* `iterPd g w`: the classical iterated partial derivative `∂_{w 0} ∂_{w 1} ⋯ g` along a sequence
  of directions; `iteratedFDeriv_single`: it is `D^n g(x)(e_{w 0}, …, e_{w (n-1)})`;
  `mFourierCoeff_descend_iterPd`: its coefficients are `(2πi n)^{α(w)} ĝ(n)`.
* `sobSq_descend_le`: `‖g‖²_{H^m(𝕋^d)} ≤ (d+1)^m (‖g‖²_{L²} + ‖D^m g‖²_{L²})` (integer `m`, the
  `L²` norms over the unit cube) — the Fourier norm is controlled by classical derivatives;
* `norm_iterPd_le`, `norm_le_sum_single`, **`norm_iteratedFDeriv_le_periodic`**: for smooth
  periodic `g` and `m > j + d/2`,
  `‖D^j g(x)‖ ≤ C_{d,m,j} (‖g‖²_{L²(cube)} + ‖D^m g‖²_{L²(cube)})^{1/2}` for every `x`
  (through `TorusSobolev.norm_le_of_memH`); `exists_norm_iteratedFDeriv_le_periodic` is the
  vector-valued form (finite-dimensional targets).

## Slab boxes

`slabBox i₀ t₀ t₁ = {x | x_{i₀} ∈ (t₀,t₁), x_i ∈ (0,1) (i ≠ i₀)}`.  A smooth function `f` on
`ℝ^d`, `ℤ`-periodic in the coordinates `i ≠ i₀` and vanishing for `x_{i₀} ∉ [a,b] ⊂ (t₀,t₁)`
(a compactly supported test on the slab `(t₀,t₁) × 𝕋^{d-1}`), is rescaled and periodised in the
`i₀` direction (`slabPeriodize`, smooth and `ℤ^d`-periodic), and

* **`exists_slab_cr_bound`**: `‖D^j f(x)‖ ≤ C (‖f‖²_{L²(slabBox)} + ‖D^m f‖²_{L²(slabBox)})^{1/2}`
  for every `x ∈ ℝ^d`, `m > j + d/2`, with `C` independent of `f` — the Sobolev embedding
  `H^m_0 ↪ C^j` on the slab (`d = 4`: `m > j + 2`).
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped BigOperators Real ENNReal ContDiff

noncomputable section

namespace RenewalGeometry.SobolevBoxCr

open TorusSobolev SobolevOpen

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Line derivatives on the torus -/

theorem lineShift_add (i : d) (s t : ℝ) :
    lineShift i (s + t) = lineShift i s + lineShift i t := by
  unfold lineShift
  rw [AddCircle.coe_add, Pi.single_add]

/-- A line derivative at `0` everywhere is a line derivative at every `s`. -/
theorem lineDeriv_hasDerivAt_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {i : d}
    {F F' : UnitAddTorus d → E} (h : IsLineDeriv i F F') (x : UnitAddTorus d) (s : ℝ) :
    HasDerivAt (fun t : ℝ => F (x + lineShift i t)) (F' (x + lineShift i s)) s := by
  have h1 := h (x + lineShift i s)
  have h1' : HasDerivAt (fun t : ℝ => F (x + lineShift i s + lineShift i t))
      (F' (x + lineShift i s)) (s - s) := by rw [sub_self]; exact h1
  refine (h1'.comp_sub_const s s).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only
  rw [add_assoc, ← lineShift_add, add_sub_cancel]

/-- **`∫_{𝕋^d} ∂ᵢF = 0`** for a continuous `F` with continuous line derivative `F'`. -/
theorem integral_lineDeriv_eq_zero {F F' : UnitAddTorus d → ℂ} (i : d) (hF : Continuous F)
    (hF' : Continuous F') (h : IsLineDeriv i F F') : ∫ y, F' y = 0 := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖F' y‖ ≤ C :=
    ⟨‖(⟨F', hF'⟩ : C(UnitAddTorus d, ℂ))‖, fun y =>
      (⟨F', hF'⟩ : C(UnitAddTorus d, ℂ)).norm_coe_le_norm y⟩
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0 : ℝ))
    (F := fun t y => F (y + lineShift i t)) (F' := fun t y => F' (y + lineShift i t))
    (bound := fun _ => C) Filter.univ_mem
    (Eventually.of_forall fun t =>
      (hF.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    ((hF.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact
      isCompact_univ |> integrableOn_univ.mp)
    ((hF'.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun y t _ => hC _) (integrable_const C)
    (Eventually.of_forall fun y t _ => lineDeriv_hasDerivAt_at h y t)
  have hconst : (fun t : ℝ => ∫ y, F (y + lineShift i t)) = fun _ => ∫ y, F y := by
    funext t
    exact integral_add_right_eq_self (μ := volume) F (lineShift i t)
  have h0 := key.2
  rw [hconst] at h0
  have h1 := h0.unique (hasDerivAt_const (0 : ℝ) (∫ y, F y))
  simpa [lineShift] using h1

/-- **Fourier rule for classical line derivatives on `𝕋^d`**: if `F'` is the continuous line
derivative of the continuous `F` in direction `i`, then `F̂'(n) = 2πi nᵢ F̂(n)`. -/
theorem mFourierCoeff_of_isLineDeriv {F F' : UnitAddTorus d → ℂ} {i : d} (hF : Continuous F)
    (hF' : Continuous F') (h : IsLineDeriv i F F') (n : d → ℤ) :
    mFourierCoeff F' n = (2 * π * Complex.I * n i) * mFourierCoeff F n := by
  set c : ℂ := 2 * π * Complex.I * n i
  set e : UnitAddTorus d → ℂ := fun y => mFourier (-n) y
  have he : Continuous e := (mFourier (-n)).continuous
  set G' : UnitAddTorus d → ℂ := fun y => e y * F' y + (-c) * (e y * F y)
  have hG : IsLineDeriv i (fun y => e y * F y) G' := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => e (x + lineShift i t)) (e x * (-c)) 0 := by
      have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-c * t)) (-c) 0 := by
        have h2 : HasDerivAt (fun t : ℝ => -c * (t : ℂ)) (-c) 0 := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (-c)
        simpa using h2.cexp
      have e1 : (fun t : ℝ => e (x + lineShift i t)) =
          fun t : ℝ => e x * Complex.exp (-c * (t : ℂ)) := by
        funext t
        simp only [e, mFourier_add_apply, mFourier_lineShift, c, Pi.neg_apply, Int.cast_neg]
        congr 2
        push_cast
        ring
      rw [e1]
      exact hexp.const_mul (e x)
    have h2 := h1.mul (h x)
    have e0 : x + lineShift i 0 = x := by rw [lineShift_zero, add_zero]
    rw [e0] at h2
    have h3 : HasDerivAt (fun t => e (x + lineShift i t) * F (x + lineShift i t))
        (e x * -c * F x + e x * F' x) 0 := h2
    refine h3.congr_deriv ?_
    simp only [G']
    ring
  have hG'c : Continuous G' := (he.mul hF').add (continuous_const.mul (he.mul hF))
  have hzero := integral_lineDeriv_eq_zero i (he.mul hF) hG'c hG
  have hi1 : Integrable (fun y => e y * F' y) :=
    (he.mul hF').continuousOn.integrableOn_compact isCompact_univ |> integrableOn_univ.mp
  have hi2 : Integrable (fun y => (-c) * (e y * F y)) :=
    (continuous_const.mul (he.mul hF)).continuousOn.integrableOn_compact isCompact_univ
      |> integrableOn_univ.mp
  simp only [G'] at hzero
  rw [integral_add hi1 hi2, integral_const_mul] at hzero
  unfold mFourierCoeff
  simp only [smul_eq_mul]
  change ∫ y, e y * F' y = c * ∫ y, e y * F y
  linear_combination hzero

/-! ### Periodic functions on `ℝ^d` descend to `𝕋^d` -/

/-- The covering map `ℝ^d → 𝕋^d`. -/
def torusMk (x : d → ℝ) : UnitAddTorus d := fun i => (x i : UnitAddCircle)

theorem torusMk_add (x y : d → ℝ) : torusMk (x + y) = torusMk x + torusMk y := by
  funext i; simp [torusMk]

theorem isOpenQuotientMap_torusMk : IsOpenQuotientMap (torusMk (d := d)) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem continuous_torusMk : Continuous (torusMk (d := d)) :=
  isOpenQuotientMap_torusMk.continuous

theorem torusMk_torusRep (t : UnitAddTorus d) : torusMk (torusRep t) = t := mk_torusRep t

theorem lineShift_eq_torusMk (i : d) (t : ℝ) :
    lineShift i t = torusMk (t • (Pi.single i 1 : d → ℝ)) := by
  funext j
  by_cases h : j = i
  · subst h; simp [lineShift, torusMk]
  · simp [lineShift, torusMk, h]

/-- `ℤ^d`-periodicity of a function on `ℝ^d`. -/
def IsPeriodic {E : Type*} (g : (d → ℝ) → E) : Prop :=
  ∀ (n : d → ℤ) (x : d → ℝ), g (x + fun i => (n i : ℝ)) = g x

theorem torusMk_eq_iff {x y : d → ℝ} : torusMk x = torusMk y ↔ ∃ n : d → ℤ,
    y = x + fun i => (n i : ℝ) := by
  constructor
  · intro h
    have : ∀ i, ∃ k : ℤ, y i = x i + k := by
      intro i
      have hi := congrFun h i
      simp only [torusMk] at hi
      have hk := (QuotientAddGroup.eq).mp hi
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hk
      refine ⟨m, ?_⟩
      simp only [zsmul_eq_mul, mul_one] at hm
      linarith
    choose n hn using this
    exact ⟨n, funext fun i => by simp [hn i]⟩
  · rintro ⟨n, rfl⟩
    rw [torusMk_add]
    have : torusMk (fun i => (n i : ℝ)) = (0 : UnitAddTorus d) := by
      funext i
      simp only [torusMk, Pi.zero_apply]
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨n i, by simp⟩
    rw [this, add_zero]

/-- The function on `𝕋^d` induced by `g`: `t ↦ g(rep t)`. -/
def descendFun {E : Type*} (g : (d → ℝ) → E) (t : UnitAddTorus d) : E := g (torusRep t)

theorem descendFun_mk {E : Type*} {g : (d → ℝ) → E} (hg : IsPeriodic g) (x : d → ℝ) :
    descendFun g (torusMk x) = g x := by
  unfold descendFun
  obtain ⟨n, hn⟩ := torusMk_eq_iff.mp (torusMk_torusRep (torusMk x))
  calc g (torusRep (torusMk x)) = g (torusRep (torusMk x) + fun i => (n i : ℝ)) := (hg n _).symm
    _ = g x := by rw [← hn]

theorem continuous_descendFun {E : Type*} [TopologicalSpace E] {g : (d → ℝ) → E}
    (hc : Continuous g) (hg : IsPeriodic g) : Continuous (descendFun g) := by
  rw [← isOpenQuotientMap_torusMk.continuous_comp_iff]
  have : descendFun g ∘ torusMk = g := funext fun x => descendFun_mk hg x
  rw [this]; exact hc

/-- The continuous function on `𝕋^d` induced by a continuous periodic `g`. -/
def descend {g : (d → ℝ) → ℂ} (hc : Continuous g) (hg : IsPeriodic g) : C(UnitAddTorus d, ℂ) :=
  ⟨descendFun g, continuous_descendFun hc hg⟩

theorem IsPeriodic.pd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : (d → ℝ) → E}
    (hg : IsPeriodic g) (i : d) : IsPeriodic (pd g i) := by
  intro n x
  unfold SobolevOpen.pd
  have : (fun y => g (y + fun i => (n i : ℝ))) = g := funext fun y => hg n y
  rw [← fderiv_comp_add_right, this]

/-- **Classical derivatives descend**: the descended partial derivative is the line derivative
of the descended function. -/
theorem isLineDeriv_descend {g : (d → ℝ) → ℂ} (hd : Differentiable ℝ g) (hg : IsPeriodic g)
    (i : d) : IsLineDeriv i (descendFun g) (descendFun (pd g i)) := by
  intro x
  set y := torusRep x
  have hy : torusMk y = x := torusMk_torusRep x
  have e1 : (fun t : ℝ => descendFun g (x + lineShift i t)) =
      fun t => g (y + t • (Pi.single i 1 : d → ℝ)) := by
    funext t
    rw [lineShift_eq_torusMk, ← hy, ← torusMk_add, descendFun_mk hg]
  rw [e1, ← hy, descendFun_mk (hg.pd i)]
  have hl : HasDerivAt (fun t : ℝ => y + t • (Pi.single i 1 : d → ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : d → ℝ)).const_add y
  have := (hd (y + (0 : ℝ) • (Pi.single i 1 : d → ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  simpa [Function.comp_def, SobolevOpen.pd] using this

/-! ### Iterated partial derivatives along a sequence of directions -/

/-- `iterPd g w = ∂_{w 0} ∂_{w 1} ⋯ ∂_{w (n-1)} g`. -/
def iterPd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : (d → ℝ) → E) :
    {n : ℕ} → (Fin n → d) → (d → ℝ) → E
  | 0, _ => g
  | _ + 1, w => pd (iterPd g (Fin.tail w)) (w 0)

/-- The multi-index `α(w)` counting the directions of `w`. -/
def idx : {n : ℕ} → (Fin n → d) → d → ℕ
  | 0, _ => 0
  | _ + 1, w => idx (Fin.tail w) + Pi.single (w 0) 1

theorem mOrder_idx : ∀ {n : ℕ} (w : Fin n → d), mOrder (idx w) = n
  | 0, _ => by simp [idx, mOrder]
  | n + 1, w => by rw [idx, mOrder_add_single, mOrder_idx]

theorem contDiff_iterPd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (d → ℝ) → E} (hg : ContDiff ℝ ∞ g) : ∀ {n : ℕ} (w : Fin n → d), ContDiff ℝ ∞ (iterPd g w)
  | 0, _ => hg
  | _ + 1, w => contDiff_pd (contDiff_iterPd hg (Fin.tail w)) (w 0)

theorem isPeriodic_iterPd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (d → ℝ) → E} (hg : IsPeriodic g) : ∀ {n : ℕ} (w : Fin n → d), IsPeriodic (iterPd g w)
  | 0, _ => hg
  | _ + 1, w => (isPeriodic_iterPd hg (Fin.tail w)).pd (w 0)

/-- **Iterated partial derivatives are the iterated Fréchet derivative on unit vectors.** -/
theorem iteratedFDeriv_single {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (d → ℝ) → E} (hg : ContDiff ℝ ∞ g) :
    ∀ {n : ℕ} (w : Fin n → d) (x : d → ℝ),
      iteratedFDeriv ℝ n g x (fun k => Pi.single (w k) 1) = iterPd g w x
  | 0, w, x => by simp [iterPd]
  | n + 1, w, x => by
    rw [iteratedFDeriv_succ_apply_left]
    have ih : iterPd g (Fin.tail w) =
        fun y => iteratedFDeriv ℝ n g y (fun k => Pi.single (Fin.tail w k) 1) :=
      funext fun y => (iteratedFDeriv_single hg (Fin.tail w) y).symm
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x :=
      (hg.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) x
    simp only [iterPd, SobolevOpen.pd, ih]
    rw [fderiv_continuousMultilinear_apply_const_apply hdiff]
    rfl

theorem symbol_idx_const (i : d) : ∀ (m : ℕ) (n : d → ℤ),
    symbol (idx (fun _ : Fin m => i)) n = (2 * π * Complex.I * n i) ^ m
  | 0, n => by simp [idx, symbol]
  | m + 1, n => by
    rw [idx, ← symbol_add_single, pow_succ]
    have : (Fin.tail fun _ : Fin (m + 1) => i) = fun _ : Fin m => i := rfl
    rw [this, symbol_idx_const i m n]
    ring

/-- **Fourier coefficients of iterated partial derivatives**: `(2πi n)^{α(w)} ĝ(n)`. -/
theorem mFourierCoeff_descend_iterPd {g : (d → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hp : IsPeriodic g) : ∀ {k : ℕ} (w : Fin k → d) (n : d → ℤ),
      mFourierCoeff (descendFun (iterPd g w)) n = symbol (idx w) n * mFourierCoeff (descendFun g) n
  | 0, w, n => by simp [iterPd, idx, symbol]
  | k + 1, w, n => by
    have hc := contDiff_iterPd hg (Fin.tail w)
    have hpp := isPeriodic_iterPd hp (Fin.tail w)
    have h1 := mFourierCoeff_of_isLineDeriv (continuous_descendFun hc.continuous hpp)
      (continuous_descendFun (contDiff_pd hc (w 0)).continuous (hpp.pd (w 0)))
      (isLineDeriv_descend (hc.differentiable (by simp)) hpp (w 0)) n
    simp only [iterPd, idx]
    rw [h1, mFourierCoeff_descend_iterPd hg hp (Fin.tail w) n, ← symbol_add_single]
    ring


/-! ### Sup bounds from the Fourier norm -/

/-- **`‖∂^w g‖_∞ ≤ C_{m-k,d} ‖g‖_{H^m(𝕋^d)}`** for `m > k + d/2`, `k = |w|`. -/
theorem norm_iterPd_le {g : (d → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hp : IsPeriodic g) {m : ℝ}
    (hF : MemH m (descendFun g)) {k : ℕ} (w : Fin k → d)
    (hm : (Fintype.card d : ℝ) / 2 + k < m) (x : d → ℝ) :
    ‖iterPd g w x‖ ≤ embConst d (m - k) * sobNorm m (descendFun g) := by
  set c := mFourierCoeff (descendFun g)
  have hcoef : mFourierCoeff (descendFun (iterPd g w)) = derivCoeff (idx w) c :=
    funext fun n => by rw [mFourierCoeff_descend_iterPd hg hp w n]; rfl
  obtain ⟨h1, h2⟩ := coeffMemH_derivCoeff hF (idx w)
  rw [mOrder_idx] at h1 h2
  have hmem : MemH (m - k) (descendFun (iterPd g w)) := by
    unfold MemH; rw [hcoef]; exact h1
  have hcont := continuous_descendFun (contDiff_iterPd hg w).continuous (isPeriodic_iterPd hp w)
  have h3 := norm_apply_le_of_memH (s := m - k) (by linarith) ⟨_, hcont⟩ hmem (torusMk x)
  rw [ContinuousMap.coe_mk, descendFun_mk (isPeriodic_iterPd hp w)] at h3
  refine h3.trans (mul_le_mul_of_nonneg_left ?_ (embConst_nonneg _))
  unfold sobNorm sobSq
  rw [hcoef]
  exact Real.sqrt_le_sqrt h2

/-- For a multilinear map on `ℝ^d` (sup norm), `‖M‖ ≤ Σ_w ‖M(e_{w 0}, …, e_{w (k-1)})‖`. -/
theorem norm_le_sum_single {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => d → ℝ) E) :
    ‖M‖ ≤ ∑ w : Fin k → d, ‖M (fun j => Pi.single (w j) 1)‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = fun j => ∑ i, v j i • (Pi.single i 1 : d → ℝ) :=
    funext fun j => pi_eq_sum_univ' (v j)
  conv_lhs => rw [hv, M.map_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [M.map_smul_univ, norm_smul, norm_prod, mul_comm]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    fun j _ => norm_le_pi_norm (v j) (w j)) (norm_nonneg _)

theorem card_fun_fin (k : ℕ) : Fintype.card (Fin k → d) = Fintype.card d ^ k := by
  simp

/-- **`H^m(𝕋^d) ⊂ C^k` for smooth periodic functions, `m > k + d/2`**:
`‖D^k g(x)‖ ≤ d^k C_{m-k,d} ‖g‖_{H^m(𝕋^d)}` at every point. -/
theorem norm_iteratedFDeriv_le_of_memH {g : (d → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hp : IsPeriodic g) {m : ℝ} (hF : MemH m (descendFun g)) {k : ℕ}
    (hm : (Fintype.card d : ℝ) / 2 + k < m) (x : d → ℝ) :
    ‖iteratedFDeriv ℝ k g x‖ ≤
      (Fintype.card d : ℝ) ^ k * embConst d (m - k) * sobNorm m (descendFun g) := by
  refine (norm_le_sum_single _).trans ?_
  have hb : ∀ w : Fin k → d, ‖iteratedFDeriv ℝ k g x (fun j => Pi.single (w j) 1)‖ ≤
      embConst d (m - k) * sobNorm m (descendFun g) := fun w => by
    rw [iteratedFDeriv_single hg w x]; exact norm_iterPd_le hg hp hF w hm x
  refine (Finset.sum_le_sum fun w _ => hb w).trans ?_
  rw [Finset.sum_const, Finset.card_univ, card_fun_fin, nsmul_eq_mul, Nat.cast_pow, mul_assoc]

/-! ### The Fourier norm is controlled by classical derivatives -/

theorem memLp_descendFun {G : (d → ℝ) → ℂ} (hc : Continuous G) (hp : IsPeriodic G) :
    MemLp (descendFun G) 2 volume := by
  set F : C(UnitAddTorus d, ℂ) := ⟨descendFun G, continuous_descendFun hc hp⟩
  exact MemLp.of_bound F.continuous.aestronglyMeasurable ‖F‖
    (Eventually.of_forall fun t => F.norm_coe_le_norm t)

theorem integral_descendFun_sq {G : (d → ℝ) → ℂ} (hp : IsPeriodic G) :
    ∫ t, ‖descendFun G t‖ ^ 2 = ∫ y in unitCube, ‖G y‖ ^ 2 := by
  rw [integral_torus_eq_unitCube]
  refine setIntegral_congr_fun measurableSet_unitCube fun y _ => ?_
  change ‖descendFun G (torusMk y)‖ ^ 2 = _
  rw [descendFun_mk hp]

theorem hasSum_sq_descend {G : (d → ℝ) → ℂ} (hc : Continuous G) (hp : IsPeriodic G) :
    HasSum (fun n => ‖mFourierCoeff (descendFun G) n‖ ^ 2) (∫ y in unitCube, ‖G y‖ ^ 2) := by
  rw [← integral_descendFun_sq hp]
  exact hasSum_sq_mFourierCoeff_of_memLp (memLp_descendFun hc hp)

/-- `(1 + Σ_i a_i)^{n+1} ≤ (d+1)^n (1 + Σ_i a_i^{n+1})` for `a ≥ 0` (power mean). -/
theorem one_add_sum_pow_le {a : d → ℝ} (ha : ∀ i, 0 ≤ a i) (n : ℕ) :
    (1 + ∑ i, a i) ^ (n + 1) ≤ ((Fintype.card d : ℝ) + 1) ^ n * (1 + ∑ i, a i ^ (n + 1)) := by
  set f : Option d → ℝ := fun o => o.elim 1 a
  have hf : ∀ o ∈ (Finset.univ : Finset (Option d)), 0 ≤ f o := by
    intro o _
    cases o with
    | none => simp [f]
    | some i => exact ha i
  have h := pow_sum_le_card_mul_sum_pow hf n
  simp only [Fintype.sum_option, f, Option.elim, one_pow, Finset.card_univ,
    Fintype.card_option] at h
  push_cast at h
  exact h

theorem sobWeight_eq (n : d → ℤ) : sobWeight n = 1 + ∑ i, (2 * π * n i) ^ 2 := by
  unfold sobWeight
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem norm_symbol_pow_sq (i : d) (n : d → ℤ) (m : ℕ) (c : ℂ) :
    ‖(2 * π * Complex.I * n i) ^ m * c‖ ^ 2 = ((2 * π * n i) ^ 2) ^ m * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm m 2, pow_mul, norm_symbol_sq]

/-- `‖∂_i^m g(y)‖ ≤ ‖D^m g(y)‖`. -/
theorem norm_iterPd_const_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (d → ℝ) → E} (hg : ContDiff ℝ ∞ g) (i : d) (m : ℕ) (y : d → ℝ) :
    ‖iterPd g (fun _ : Fin m => i) y‖ ≤ ‖iteratedFDeriv ℝ m g y‖ := by
  rw [← iteratedFDeriv_single hg]
  refine ((iteratedFDeriv ℝ m g y).le_opNorm _).trans ?_
  have h1 : ‖(Pi.single i 1 : d → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by
      by_cases h : j = i
      · subst h; simp
      · simp [h]
  calc ‖iteratedFDeriv ℝ m g y‖ * ∏ _j : Fin m, ‖(Pi.single i 1 : d → ℝ)‖
      ≤ ‖iteratedFDeriv ℝ m g y‖ * 1 :=
        mul_le_mul_of_nonneg_left (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => h1)
          (norm_nonneg _)
    _ = _ := mul_one _

theorem integrableOn_unitCube {G : (d → ℝ) → ℝ} (hc : Continuous G) :
    IntegrableOn G unitCube := by
  have hsub : (unitCube : Set (d → ℝ)) ⊆ Icc 0 1 := fun y hy =>
    ⟨fun i => (hy i).1.le, fun i => (hy i).2⟩
  exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub

/-- **The Fourier `H^m` norm of a smooth periodic function is controlled by classical
derivatives**: `g ∈ H^m(𝕋^d)` and
`‖g‖²_{H^m(𝕋^d)} ≤ (d+1)^m (‖g‖²_{L²(cube)} + ‖D^m g‖²_{L²(cube)})` for integers `m ≥ 1`. -/
theorem sobSq_descend_le {g : (d → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hp : IsPeriodic g) (m : ℕ)
    (hm : 1 ≤ m) :
    MemH m (descendFun g) ∧ sobSq m (descendFun g) ≤ ((Fintype.card d : ℝ) + 1) ^ m *
      ((∫ y in unitCube, ‖g y‖ ^ 2) + ∫ y in unitCube, ‖iteratedFDeriv ℝ m g y‖ ^ 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  set c := mFourierCoeff (descendFun g)
  set A := ∫ y in unitCube, ‖g y‖ ^ 2
  set B := ∫ y in unitCube, ‖iteratedFDeriv ℝ (n + 1) g y‖ ^ 2
  set D : d → (d → ℝ) → ℂ := fun i => iterPd g (fun _ : Fin (n + 1) => i)
  set Bi : d → ℝ := fun i => ∫ y in unitCube, ‖D i y‖ ^ 2
  have hA := hasSum_sq_descend hg.continuous hp
  have hB : ∀ i, HasSum (fun k => ((2 * π * k i) ^ 2) ^ (n + 1) * ‖c k‖ ^ 2) (Bi i) := by
    intro i
    have h := hasSum_sq_descend (contDiff_iterPd hg (fun _ : Fin (n + 1) => i)).continuous
      (isPeriodic_iterPd hp (fun _ : Fin (n + 1) => i))
    refine h.congr_fun fun k => ?_
    rw [mFourierCoeff_descend_iterPd hg hp, symbol_idx_const, norm_symbol_pow_sq]
  set K : ℝ := ((Fintype.card d : ℝ) + 1) ^ n
  have hS := (hA.add (hasSum_sum (s := Finset.univ) fun i _ => hB i)).mul_left K
  have hle : ∀ k, sobWeight k ^ ((n + 1 : ℕ) : ℝ) * ‖c k‖ ^ 2 ≤
      K * (‖c k‖ ^ 2 + ∑ i, ((2 * π * k i) ^ 2) ^ (n + 1) * ‖c k‖ ^ 2) := by
    intro k
    rw [Real.rpow_natCast, sobWeight_eq, ← Finset.sum_mul, ← one_add_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (one_add_sum_pow_le (fun i => sq_nonneg _) n)
      (sq_nonneg _)
  have hsum : CoeffMemH ((n + 1 : ℕ) : ℝ) c :=
    Summable.of_nonneg_of_le (coeffSobSq_term_nonneg _ _) hle hS.summable
  refine ⟨hsum, ?_⟩
  have h1 : sobSq ((n + 1 : ℕ) : ℝ) (descendFun g) ≤ K * (A + ∑ i, Bi i) :=
    (Summable.tsum_le_tsum hle hsum hS.summable).trans hS.tsum_eq.le
  have hBi : ∀ i, Bi i ≤ B := by
    intro i
    refine setIntegral_mono_on ?_ ?_ measurableSet_unitCube fun y _ => ?_
    · exact integrableOn_unitCube ((contDiff_iterPd hg _).continuous.norm.pow 2)
    · exact integrableOn_unitCube
        ((hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.pow 2)
    · exact pow_le_pow_left₀ (norm_nonneg _) (norm_iterPd_const_le hg i (n + 1) y) 2
  have hA0 : 0 ≤ A := setIntegral_nonneg measurableSet_unitCube fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_unitCube fun _ _ => sq_nonneg _
  have h2 : ∑ i, Bi i ≤ (Fintype.card d : ℝ) * B := by
    refine (Finset.sum_le_sum fun i _ => hBi i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hK : 0 ≤ K := by positivity
  calc sobSq ((n + 1 : ℕ) : ℝ) (descendFun g) ≤ K * (A + ∑ i, Bi i) := h1
    _ ≤ K * (((Fintype.card d : ℝ) + 1) * (A + B)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        nlinarith
    _ = ((Fintype.card d : ℝ) + 1) ^ (n + 1) * (A + B) := by
        simp only [K]; ring

/-- The constant of `norm_iteratedFDeriv_le_periodic`. -/
def perConst (d : Type*) [Fintype d] (m k : ℕ) : ℝ :=
  (Fintype.card d : ℝ) ^ k * embConst d (m - k) * Real.sqrt (((Fintype.card d : ℝ) + 1) ^ m)

theorem perConst_nonneg (m k : ℕ) : 0 ≤ perConst d m k := by
  unfold perConst
  have := embConst_nonneg (d := d) (m - k)
  positivity

/-- **Sobolev embedding for smooth periodic functions, classical form**: for `m > k + d/2`,
`‖D^k g(x)‖ ≤ C_{d,m,k} (‖g‖²_{L²(cube)} + ‖D^m g‖²_{L²(cube)})^{1/2}` at every `x ∈ ℝ^d`. -/
theorem norm_iteratedFDeriv_le_periodic {g : (d → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hp : IsPeriodic g) {m k : ℕ} (hm : (Fintype.card d : ℝ) / 2 + k < m) (x : d → ℝ) :
    ‖iteratedFDeriv ℝ k g x‖ ≤ perConst d m k *
      Real.sqrt ((∫ y in unitCube, ‖g y‖ ^ 2) + ∫ y in unitCube, ‖iteratedFDeriv ℝ m g y‖ ^ 2) := by
  have hm1 : 1 ≤ m := by
    have h0 : (0 : ℝ) ≤ (Fintype.card d : ℝ) / 2 + k := by positivity
    have h := lt_of_le_of_lt h0 hm
    rcases Nat.eq_zero_or_pos m with h' | h'
    · subst h'; simp at h
    · exact h'
  obtain ⟨hmem, hsq⟩ := sobSq_descend_le hg hp m hm1
  refine (norm_iteratedFDeriv_le_of_memH hg hp hmem hm x).trans ?_
  unfold perConst sobNorm
  rw [mul_assoc _ (Real.sqrt _), ← Real.sqrt_mul (by positivity)]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) ?_
  have := embConst_nonneg (d := d) (m - k)
  positivity


/-! ### Finite-dimensional targets -/

/-- The `j`-th coordinate of a basis, as a continuous real-linear map into `ℂ`. -/
def coordC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι' : Type*} (b : Module.Basis ι' ℝ E) (j : ι') : E →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (b.coord j))

theorem norm_le_sum_coordC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι' : Type*} [Fintype ι'] (b : Module.Basis ι' ℝ E) {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => d → ℝ) E) :
    ‖M‖ ≤ ∑ j, ‖b j‖ * ‖(coordC b j).compContinuousMultilinearMap M‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => by positivity) fun v => ?_
  conv_lhs => rw [← b.sum_repr (M v)]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_smul, mul_comm, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have e1 : ‖b.repr (M v) j‖ = ‖(coordC b j).compContinuousMultilinearMap M v‖ := by
    simp [coordC, Module.Basis.coord_apply]
  rw [e1]
  exact ((coordC b j).compContinuousMultilinearMap M).le_opNorm v

/-- **Sobolev embedding for smooth periodic functions, finite-dimensional targets**: for
`m > k + d/2` there is `C` with `‖D^k g(x)‖ ≤ C (‖g‖²_{L²(cube)} + ‖D^m g‖²_{L²(cube)})^{1/2}` for
every smooth periodic `g : ℝ^d → E` and every `x`. -/
theorem exists_norm_iteratedFDeriv_le_periodic (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m k : ℕ}
    (hm : (Fintype.card d : ℝ) / 2 + k < m) :
    ∃ C, 0 ≤ C ∧ ∀ g : (d → ℝ) → E, ContDiff ℝ ∞ g → IsPeriodic g → ∀ x,
      ‖iteratedFDeriv ℝ k g x‖ ≤ C * Real.sqrt ((∫ y in unitCube, ‖g y‖ ^ 2) +
        ∫ y in unitCube, ‖iteratedFDeriv ℝ m g y‖ ^ 2) := by
  set b := Module.finBasis ℝ E
  refine ⟨∑ j, ‖b j‖ * (perConst d m k * ‖coordC b j‖),
    Finset.sum_nonneg fun j _ => by have := perConst_nonneg (d := d) m k; positivity,
    fun g hg hp x => ?_⟩
  set A := ∫ y in unitCube, ‖g y‖ ^ 2
  set B := ∫ y in unitCube, ‖iteratedFDeriv ℝ m g y‖ ^ 2
  have hA0 : 0 ≤ A := setIntegral_nonneg measurableSet_unitCube fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_unitCube fun _ _ => sq_nonneg _
  refine (norm_le_sum_coordC b _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  set ℓ := coordC b j
  have hgj : ContDiff ℝ ∞ (ℓ ∘ g) := ℓ.contDiff.comp hg
  have hpj : IsPeriodic (ℓ ∘ g) := fun n y => by simp [hp n y]
  have hcomp : ∀ (i : ℕ) (y : d → ℝ), iteratedFDeriv ℝ i (ℓ ∘ g) y =
      ℓ.compContinuousMultilinearMap (iteratedFDeriv ℝ i g y) := fun i y =>
    ℓ.iteratedFDeriv_comp_left hg.contDiffAt (by exact_mod_cast le_top)
  have h1 := norm_iteratedFDeriv_le_periodic hgj hpj hm x
  rw [hcomp] at h1
  refine h1.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (perConst_nonneg m k)
  have hcg : Continuous g := hg.continuous
  have hcD : Continuous fun y => iteratedFDeriv ℝ m g y :=
    hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hA : ∫ y in unitCube, ‖(ℓ ∘ g) y‖ ^ 2 ≤ ‖ℓ‖ ^ 2 * A := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_unitCube ((ℓ.continuous.comp hcg).norm.pow 2))
      (integrableOn_unitCube (continuous_const.mul (hcg.norm.pow 2))) measurableSet_unitCube
      fun y _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (ℓ.le_opNorm _) 2
  have hB : ∫ y in unitCube, ‖iteratedFDeriv ℝ m (ℓ ∘ g) y‖ ^ 2 ≤ ‖ℓ‖ ^ 2 * B := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_unitCube
      ((hgj.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.pow 2))
      (integrableOn_unitCube (continuous_const.mul (hcD.norm.pow 2))) measurableSet_unitCube
      fun y _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (ℓ.norm_iteratedFDeriv_comp_left hg.contDiffAt (by exact_mod_cast le_top)) 2
  calc Real.sqrt ((∫ y in unitCube, ‖(ℓ ∘ g) y‖ ^ 2) +
        ∫ y in unitCube, ‖iteratedFDeriv ℝ m (ℓ ∘ g) y‖ ^ 2)
      ≤ Real.sqrt (‖ℓ‖ ^ 2 * (A + B)) := Real.sqrt_le_sqrt (by nlinarith)
    _ = ‖ℓ‖ * Real.sqrt (A + B) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-! ### Slab boxes: rescaling and periodisation in one direction -/

section Slab

variable (i₀ : d)

/-- The weights `(L at i₀, 1 elsewhere)`. -/
def slabW (L : ℝ) : d → ℝ := Function.update 1 i₀ L

@[simp] theorem slabW_self (L : ℝ) : slabW i₀ L i₀ = L := by simp [slabW]

theorem slabW_ne (L : ℝ) {i : d} (h : i ≠ i₀) : slabW i₀ L i = 1 := by simp [slabW, h]

/-- The diagonal scaling `y ↦ (L y_{i₀}, y_i (i ≠ i₀))`. -/
def slabScale (L : ℝ) : (d → ℝ) →L[ℝ] (d → ℝ) :=
  ContinuousLinearMap.pi fun i => slabW i₀ L i • ContinuousLinearMap.proj i

@[simp] theorem slabScale_apply (L : ℝ) (y : d → ℝ) (i : d) :
    slabScale i₀ L y i = slabW i₀ L i * y i := rfl

theorem slabScale_inv_apply {L : ℝ} (hL : L ≠ 0) (y : d → ℝ) :
    slabScale i₀ L⁻¹ (slabScale i₀ L y) = y := by
  funext i
  by_cases h : i = i₀
  · subst h; simp [hL]
  · simp [slabW_ne i₀ _ h]

theorem slabScale_apply_inv {L : ℝ} (hL : L ≠ 0) (y : d → ℝ) :
    slabScale i₀ L (slabScale i₀ L⁻¹ y) = y := by
  funext i
  by_cases h : i = i₀
  · subst h; simp [hL]
  · simp [slabW_ne i₀ _ h]

/-- The scaling as a continuous linear equivalence. -/
def slabScaleEquiv {L : ℝ} (hL : L ≠ 0) : (d → ℝ) ≃L[ℝ] (d → ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (slabScale i₀ L) (slabScale i₀ L⁻¹)
    (slabScale_inv_apply i₀ hL) (slabScale_apply_inv i₀ hL)

theorem det_slabScale (L : ℝ) :
    LinearMap.det (slabScale i₀ L : (d → ℝ) →ₗ[ℝ] (d → ℝ)) = L := by
  have e : (slabScale i₀ L : (d → ℝ) →ₗ[ℝ] (d → ℝ)) =
      Matrix.toLin' (Matrix.diagonal (slabW i₀ L)) := by
    ext y i
    simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rw [e, LinearMap.det_toLin', Matrix.det_diagonal, slabW,
    Finset.prod_update_of_mem (Finset.mem_univ i₀)]
  simp

/-- **Change of variables** `∫ H(c + Λy) dy = L⁻¹ ∫ H`. -/
theorem integral_comp_slabAffine {L : ℝ} (hL : 0 < L) (c : d → ℝ) (H : (d → ℝ) → ℝ) :
    ∫ y, H (c + slabScale i₀ L y) = L⁻¹ * ∫ x, H x := by
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (d → ℝ)))
    (f := (slabScale i₀ L : (d → ℝ) →ₗ[ℝ] (d → ℝ))) (by rw [det_slabScale]; exact hL.ne')
  rw [ContinuousLinearMap.coe_coe, det_slabScale] at hmap
  set e := (slabScaleEquiv i₀ hL.ne').toHomeomorph.toMeasurableEquiv
  have he : ⇑e = ⇑(slabScale i₀ L) := rfl
  have h1 := integral_map_equiv (μ := (volume : Measure (d → ℝ))) e (fun z => H (c + z))
  rw [he, hmap, integral_smul_measure, integral_add_left_eq_self] at h1
  rw [← h1, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, abs_of_pos hL, smul_eq_mul]

/-- Lower corner of the slab box. -/
def slabLo (t₀ : ℝ) : d → ℝ := Function.update 0 i₀ t₀
/-- Upper corner of the slab box. -/
def slabHi (t₁ : ℝ) : d → ℝ := Function.update 1 i₀ t₁

/-- **The slab box** `{x | x_{i₀} ∈ (t₀,t₁), x_i ∈ (0,1) (i ≠ i₀)}`. -/
def slabBox (t₀ t₁ : ℝ) : Set (d → ℝ) := univ.pi fun i => Ioo (slabLo i₀ t₀ i) (slabHi i₀ t₁ i)

/-- The half-open slab box. -/
def slabBoxIoc (t₀ t₁ : ℝ) : Set (d → ℝ) :=
  univ.pi fun i => Ioc (slabLo i₀ t₀ i) (slabHi i₀ t₁ i)

theorem measurableSet_slabBox (t₀ t₁ : ℝ) : MeasurableSet (slabBox i₀ t₀ t₁) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem measurableSet_slabBoxIoc (t₀ t₁ : ℝ) : MeasurableSet (slabBoxIoc i₀ t₀ t₁) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem slabBoxIoc_ae_eq (t₀ t₁ : ℝ) :
    slabBoxIoc i₀ t₀ t₁ =ᵐ[(volume : Measure (d → ℝ))] slabBox i₀ t₀ t₁ := by
  have h1 : slabBoxIoc i₀ t₀ t₁ =ᵐ[(volume : Measure (d → ℝ))]
      Icc (slabLo i₀ t₀) (slabHi i₀ t₁) := by
    rw [volume_pi]; exact Measure.univ_pi_Ioc_ae_eq_Icc
  have h2 : slabBox i₀ t₀ t₁ =ᵐ[(volume : Measure (d → ℝ))]
      Icc (slabLo i₀ t₀) (slabHi i₀ t₁) := by
    rw [volume_pi]; exact Measure.univ_pi_Ioo_ae_eq_Icc
  exact h1.trans h2.symm

variable {i₀}

/-- The affine charts `φ_k(y) = t₀ e_{i₀} + Λ(y - k e_{i₀})`, `Λ = diag(t₁ - t₀ at i₀, 1)`. -/
def slabMap (t₀ t₁ : ℝ) (k : ℝ) (y : d → ℝ) : d → ℝ :=
  Pi.single i₀ t₀ + slabScale i₀ (t₁ - t₀) (y - k • Pi.single i₀ 1)

theorem slabMap_self (t₀ t₁ k : ℝ) (y : d → ℝ) :
    slabMap (i₀ := i₀) t₀ t₁ k y i₀ = t₀ + (t₁ - t₀) * (y i₀ - k) := by
  simp [slabMap]; ring

theorem slabMap_ne (t₀ t₁ k : ℝ) (y : d → ℝ) {i : d} (h : i ≠ i₀) :
    slabMap (i₀ := i₀) t₀ t₁ k y i = y i := by
  simp [slabMap, slabW_ne i₀ _ h, h]

theorem slabMap_eq (t₀ t₁ k : ℝ) (y : d → ℝ) :
    slabMap (i₀ := i₀) t₀ t₁ k y = (Pi.single i₀ t₀ - slabScale i₀ (t₁ - t₀)
      (k • Pi.single i₀ 1)) + slabScale i₀ (t₁ - t₀) y := by
  simp only [slabMap, map_sub]; abel

/-- **Periodisation in the `i₀` direction after rescaling `(t₀,t₁)` to `(0,1)`**. -/
def slabPeriodize {E : Type*} (t₀ t₁ : ℝ) (f : (d → ℝ) → E) (y : d → ℝ) : E :=
  f (slabMap (i₀ := i₀) t₀ t₁ (⌊y i₀⌋ : ℝ) y)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iteratedFDeriv_comp_affine {f : (d → ℝ) → E} (hf : ContDiff ℝ ∞ f)
    (Λ : (d → ℝ) →L[ℝ] (d → ℝ)) (c : d → ℝ) (n : ℕ) (y : d → ℝ) :
    iteratedFDeriv ℝ n (fun y => f (c + Λ y)) y =
      (iteratedFDeriv ℝ n f (c + Λ y)).compContinuousLinearMap fun _ => Λ := by
  have hc : ContDiff ℝ ∞ fun z => f (c + z) := hf.comp (contDiff_const.add contDiff_id)
  have e : (fun y => f (c + Λ y)) = (fun z => f (c + z)) ∘ Λ := rfl
  rw [e, Λ.iteratedFDeriv_comp_right hc y (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left]

theorem norm_iteratedFDeriv_comp_affine_le {f : (d → ℝ) → E} (hf : ContDiff ℝ ∞ f)
    (Λ : (d → ℝ) →L[ℝ] (d → ℝ)) (c : d → ℝ) (n : ℕ) (y : d → ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => f (c + Λ y)) y‖ ≤ ‖iteratedFDeriv ℝ n f (c + Λ y)‖ * ‖Λ‖ ^ n := by
  rw [iteratedFDeriv_comp_affine hf]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp

variable {t₀ t₁ a b : ℝ} {f : (d → ℝ) → E}

/-- Vanishing of all derivatives outside the time support. -/
theorem iteratedFDeriv_eq_zero_of_time (hz : ∀ x, x i₀ ∉ Icc a b → f x = 0) (n : ℕ) {x : d → ℝ}
    (hx : x i₀ ∉ Icc a b) : iteratedFDeriv ℝ n f x = 0 := by
  have hts : tsupport f ⊆ {x | x i₀ ∈ Icc a b} :=
    closure_minimal (fun x hx' => by_contra fun h => hx' (hz x h))
      (isClosed_Icc.preimage (continuous_apply i₀))
  have : x ∉ tsupport f := fun h => hx (hts h)
  exact Function.notMem_support.mp fun h => this (support_iteratedFDeriv_subset n h)

theorem slabPeriodize_eventuallyEq (h01 : t₀ < t₁) (ha : t₀ < a) (hb : b < t₁)
    (hz : ∀ x, x i₀ ∉ Icc a b → f x = 0) (y : d → ℝ) :
    slabPeriodize (i₀ := i₀) t₀ t₁ f =ᶠ[𝓝 y]
      fun y' => f (slabMap (i₀ := i₀) t₀ t₁ (⌊y i₀⌋ : ℝ) y') := by
  set L := t₁ - t₀
  have hL : 0 < L := sub_pos.mpr h01
  set k : ℤ := ⌊y i₀⌋
  set δ : ℝ := min (min (a - t₀) (t₁ - b) / L) 1
  have hδ0 : 0 < δ := lt_min (div_pos (lt_min (by linarith) (by linarith)) hL) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδL : δ * L ≤ t₁ - b := by
    have : δ ≤ min (a - t₀) (t₁ - b) / L := min_le_left _ _
    rw [le_div_iff₀ hL] at this
    exact this.trans (min_le_right _ _)
  set U : Set (d → ℝ) := (fun y' => y' i₀) ⁻¹' Ioo ((k : ℝ) - δ) (k + 1)
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_apply i₀)
  have hyU : y ∈ U := ⟨by linarith [Int.floor_le (y i₀)], Int.lt_floor_add_one (y i₀)⟩
  refine Filter.eventuallyEq_of_mem (hU.mem_nhds hyU) fun y' hy' => ?_
  simp only [slabPeriodize]
  by_cases hk : (k : ℝ) ≤ y' i₀
  · have : ⌊y' i₀⌋ = k := Int.floor_eq_iff.mpr ⟨hk, hy'.2⟩
    rw [this]
  · push Not at hk
    have hfl : ⌊y' i₀⌋ = k - 1 := Int.floor_eq_iff.mpr ⟨by push_cast; linarith [hy'.1], by
      push_cast; linarith⟩
    rw [hfl]
    rw [hz _ (fun h => ?_), hz _ (fun h => ?_)]
    · have h2 := h.1
      rw [slabMap_self] at h2
      have : L * (y' i₀ - k) < 0 := mul_neg_of_pos_of_neg hL (by linarith)
      linarith
    · have h2 := h.2
      rw [slabMap_self] at h2
      push_cast at h2
      have h3 : L * (y' i₀ - (k - 1)) > L * (1 - δ) :=
        mul_lt_mul_of_pos_left (by linarith [hy'.1]) hL
      nlinarith

theorem contDiff_slabMap (t₀ t₁ k : ℝ) : ContDiff ℝ ∞ (slabMap (i₀ := i₀) t₀ t₁ k) := by
  unfold slabMap
  exact contDiff_const.add ((slabScale i₀ _).contDiff.comp (contDiff_id.sub contDiff_const))

theorem contDiff_slabPeriodize (hf : ContDiff ℝ ∞ f) (h01 : t₀ < t₁) (ha : t₀ < a)
    (hb : b < t₁) (hz : ∀ x, x i₀ ∉ Icc a b → f x = 0) :
    ContDiff ℝ ∞ (slabPeriodize (i₀ := i₀) t₀ t₁ f) :=
  contDiff_iff_contDiffAt.mpr fun y =>
    ((hf.comp (contDiff_slabMap t₀ t₁ _)).contDiffAt).congr_of_eventuallyEq
      (slabPeriodize_eventuallyEq h01 ha hb hz y)

theorem isPeriodic_slabPeriodize
    (hper : ∀ n : d → ℤ, n i₀ = 0 → ∀ x, f (x + fun i => (n i : ℝ)) = f x) :
    IsPeriodic (slabPeriodize (i₀ := i₀) t₀ t₁ f) := by
  intro n y
  simp only [slabPeriodize]
  have hfl : ⌊(y + fun i => (n i : ℝ)) i₀⌋ = ⌊y i₀⌋ + n i₀ := by
    simp only [Pi.add_apply]; exact Int.floor_add_intCast _ _
  rw [hfl]
  have e : slabMap (i₀ := i₀) t₀ t₁ ((⌊y i₀⌋ + n i₀ : ℤ) : ℝ) (y + fun i => (n i : ℝ)) =
      slabMap (i₀ := i₀) t₀ t₁ (⌊y i₀⌋ : ℝ) y + fun i => ((Function.update n i₀ 0 i : ℤ) : ℝ) := by
    funext i
    by_cases h : i = i₀
    · subst h; simp only [Pi.add_apply, slabMap_self]; simp
    · simp only [Pi.add_apply, slabMap_ne _ _ _ _ h, Function.update_of_ne h]
  rw [e, hper _ (by simp)]

theorem slabMap_mem_Ioc_iff (h01 : t₀ < t₁) (y : d → ℝ) :
    slabMap (i₀ := i₀) t₀ t₁ 0 y ∈ slabBoxIoc i₀ t₀ t₁ ↔ y ∈ unitCube := by
  have hL : 0 < t₁ - t₀ := sub_pos.mpr h01
  simp only [slabBoxIoc, unitCube, Set.mem_pi, mem_univ, true_implies, mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  by_cases h : i = i₀
  · subst h
    simp only [slabMap_self, slabLo, slabHi, Function.update_self, mem_Ioc, sub_zero]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  · simp [slabMap_ne _ _ _ _ h, slabLo, slabHi, h]

theorem slabPeriodize_eq_on_cube (h01 : t₀ < t₁) (ha : t₀ < a) (hb : b < t₁)
    (hz : ∀ x, x i₀ ∉ Icc a b → f x = 0) {y : d → ℝ} (hy : y ∈ unitCube) :
    slabPeriodize (i₀ := i₀) t₀ t₁ f y = f (slabMap (i₀ := i₀) t₀ t₁ 0 y) := by
  simp only [slabPeriodize]
  rcases (hy i₀).2.lt_or_eq with h1 | h1
  · have : ⌊y i₀⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simpa using (hy i₀).1.le, by simpa using h1⟩
    rw [this]; simp
  · have : ⌊y i₀⌋ = 1 := by rw [h1]; simp
    rw [this, hz _ (fun h => ?_), hz _ (fun h => ?_)]
    · have h2 := h.2; rw [slabMap_self, h1] at h2; simp at h2; linarith
    · have h2 := h.1; rw [slabMap_self, h1] at h2; simp at h2; linarith

theorem norm_iteratedFDeriv_slabPeriodize_le (hf : ContDiff ℝ ∞ f) (h01 : t₀ < t₁)
    (ha : t₀ < a) (hb : b < t₁) (hz : ∀ x, x i₀ ∉ Icc a b → f x = 0) (n : ℕ) {y : d → ℝ}
    (hy : y ∈ unitCube) :
    ‖iteratedFDeriv ℝ n (slabPeriodize (i₀ := i₀) t₀ t₁ f) y‖ ≤
      ‖iteratedFDeriv ℝ n f (slabMap (i₀ := i₀) t₀ t₁ 0 y)‖ *
        ‖slabScale i₀ (t₁ - t₀)‖ ^ n := by
  have hev := (slabPeriodize_eventuallyEq h01 ha hb hz y).iteratedFDeriv ℝ n
  rw [hev.self_of_nhds]
  have hform : ∀ k : ℝ, (fun y' => f (slabMap (i₀ := i₀) t₀ t₁ k y')) = fun y' =>
      f ((Pi.single i₀ t₀ - slabScale i₀ (t₁ - t₀) (k • Pi.single i₀ 1)) +
        slabScale i₀ (t₁ - t₀) y') := fun k => funext fun y' => by rw [slabMap_eq]
  rcases (hy i₀).2.lt_or_eq with h1 | h1
  · have : ⌊y i₀⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simpa using (hy i₀).1.le, by simpa using h1⟩
    rw [this, Int.cast_zero, hform]
    refine (norm_iteratedFDeriv_comp_affine_le hf _ _ n y).trans_eq ?_
    rw [← slabMap_eq]
  · have : ⌊y i₀⌋ = 1 := by rw [h1]; simp
    rw [this, Int.cast_one, hform, iteratedFDeriv_comp_affine hf, ← slabMap_eq,
      iteratedFDeriv_eq_zero_of_time hz n (fun h => ?_)]
    · have h0 : (0 : ContinuousMultilinearMap ℝ (fun _ : Fin n => d → ℝ) E).compContinuousLinearMap
          (fun _ => slabScale i₀ (t₁ - t₀)) = 0 := by ext v; simp
      rw [h0, norm_zero]
      positivity
    · have h2 := h.1; rw [slabMap_self, h1] at h2; simp at h2; linarith

/-- **Classical derivatives of `f` from those of its periodisation.** -/
theorem exists_norm_iteratedFDeriv_le_slabPeriodize (hf : ContDiff ℝ ∞ f) (h01 : t₀ < t₁)
    (ha : t₀ < a) (hb : b < t₁) (hz : ∀ x, x i₀ ∉ Icc a b → f x = 0) (n : ℕ) (x : d → ℝ) :
    ∃ y, ‖iteratedFDeriv ℝ n f x‖ ≤
      ‖iteratedFDeriv ℝ n (slabPeriodize (i₀ := i₀) t₀ t₁ f) y‖ *
        ‖slabScale i₀ (t₁ - t₀)⁻¹‖ ^ n := by
  have hL : 0 < t₁ - t₀ := sub_pos.mpr h01
  set Λi := slabScale i₀ (t₁ - t₀)⁻¹
  set c' : d → ℝ := -Λi (Pi.single i₀ t₀)
  by_cases hx : x i₀ ∈ Ioo t₀ t₁
  · refine ⟨c' + Λi x, ?_⟩
    set V : Set (d → ℝ) := (fun x' => x' i₀) ⁻¹' Ioo t₀ t₁
    have hV : IsOpen V := isOpen_Ioo.preimage (continuous_apply i₀)
    have hev : f =ᶠ[𝓝 x] fun x' => slabPeriodize (i₀ := i₀) t₀ t₁ f (c' + Λi x') := by
      refine Filter.eventuallyEq_of_mem (hV.mem_nhds hx) fun x' hx' => ?_
      have hz0 : (c' + Λi x') i₀ = (t₁ - t₀)⁻¹ * (x' i₀ - t₀) := by
        simp [c', Λi]; ring
      have hfl : ⌊(c' + Λi x') i₀⌋ = 0 := by
        rw [Int.floor_eq_iff, hz0]
        have h1 := hx'.1; have h2 := hx'.2
        constructor
        · push_cast; exact mul_nonneg (inv_nonneg.mpr hL.le) (by linarith)
        · push_cast
          rw [zero_add, inv_mul_lt_iff₀ hL]; linarith
      simp only [slabPeriodize, hfl, Int.cast_zero]
      congr 1
      funext i
      by_cases h : i = i₀
      · subst h; rw [slabMap_self, sub_zero, hz0]; field_simp; ring
      · rw [slabMap_ne _ _ _ _ h]; simp [c', Λi, slabW_ne i₀ _ h, h]
    rw [(hev.iteratedFDeriv ℝ n).self_of_nhds]
    exact norm_iteratedFDeriv_comp_affine_le
      (contDiff_slabPeriodize hf h01 ha hb hz) Λi c' n x
  · refine ⟨0, ?_⟩
    rw [iteratedFDeriv_eq_zero_of_time hz n (fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩),
      norm_zero]
    positivity

end Slab


/-- **Sobolev embedding `H^m_0 ↪ C^j` on a slab box, `m > j + d/2`.**  For every finite-dimensional
target `E` there is `C` such that every smooth `f : ℝ^d → E` which is `ℤ`-periodic in the
coordinates `i ≠ i₀` and vanishes for `x_{i₀} ∉ [a,b] ⊂ (t₀,t₁)` satisfies
`‖D^j f(x)‖ ≤ C (‖f‖²_{L²(slabBox)} + ‖D^m f‖²_{L²(slabBox)})^{1/2}` at every point. -/
theorem exists_slab_cr_bound (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (i₀ : d) {t₀ t₁ : ℝ} (h01 : t₀ < t₁) {m j : ℕ}
    (hm : (Fintype.card d : ℝ) / 2 + j < m) :
    ∃ C, 0 ≤ C ∧ ∀ f : (d → ℝ) → E, ContDiff ℝ ∞ f →
      (∀ n : d → ℤ, n i₀ = 0 → ∀ x, f (x + fun i => (n i : ℝ)) = f x) →
      ∀ a b, t₀ < a → b < t₁ → (∀ x, x i₀ ∉ Icc a b → f x = 0) →
      ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C * Real.sqrt ((∫ y in slabBox i₀ t₀ t₁, ‖f y‖ ^ 2) +
        ∫ y in slabBox i₀ t₀ t₁, ‖iteratedFDeriv ℝ m f y‖ ^ 2) := by
  obtain ⟨Cv, hCv0, hCv⟩ := exists_norm_iteratedFDeriv_le_periodic (d := d) E hm
  set L := t₁ - t₀
  have hL : 0 < L := sub_pos.mpr h01
  set Λ := slabScale i₀ L
  set Λi := slabScale i₀ L⁻¹
  refine ⟨Cv * Real.sqrt (L⁻¹ * (1 + ‖Λ‖ ^ (2 * m))) * ‖Λi‖ ^ j, by positivity, ?_⟩
  intro f hf hper a b ha hb hz x
  set g := slabPeriodize (i₀ := i₀) t₀ t₁ f
  have hg : ContDiff ℝ ∞ g := contDiff_slabPeriodize hf h01 ha hb hz
  have hgp : IsPeriodic g := isPeriodic_slabPeriodize hper
  set A := ∫ y in slabBox i₀ t₀ t₁, ‖f y‖ ^ 2
  set B := ∫ y in slabBox i₀ t₀ t₁, ‖iteratedFDeriv ℝ m f y‖ ^ 2
  have hcov : ∀ H : (d → ℝ) → ℝ, ∫ y in unitCube, H (slabMap (i₀ := i₀) t₀ t₁ 0 y) =
      L⁻¹ * ∫ x in slabBox i₀ t₀ t₁, H x := by
    intro H
    rw [← integral_indicator measurableSet_unitCube,
      ← setIntegral_congr_set (slabBoxIoc_ae_eq i₀ t₀ t₁),
      ← integral_indicator (measurableSet_slabBoxIoc i₀ t₀ t₁)]
    have e : (indicator unitCube fun y => H (slabMap (i₀ := i₀) t₀ t₁ 0 y)) =
        fun y => (indicator (slabBoxIoc i₀ t₀ t₁) H) (Pi.single i₀ t₀ + Λ y) := by
      funext y
      have hm' : slabMap (i₀ := i₀) t₀ t₁ 0 y = Pi.single i₀ t₀ + Λ y := by simp [slabMap, Λ, L]
      by_cases hy : y ∈ unitCube
      · rw [indicator_of_mem hy, ← hm', indicator_of_mem ((slabMap_mem_Ioc_iff h01 y).mpr hy)]
      · rw [indicator_of_notMem hy, ← hm',
          indicator_of_notMem (fun h => hy ((slabMap_mem_Ioc_iff h01 y).mp h))]
    rw [e, integral_comp_slabAffine i₀ hL]
  have hA : ∫ y in unitCube, ‖g y‖ ^ 2 = L⁻¹ * A := by
    rw [← hcov]
    exact setIntegral_congr_fun measurableSet_unitCube fun y hy => by
      simp only [g]; rw [slabPeriodize_eq_on_cube h01 ha hb hz hy]
  have hcf : Continuous fun y => iteratedFDeriv ℝ m f y :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hB : ∫ y in unitCube, ‖iteratedFDeriv ℝ m g y‖ ^ 2 ≤ ‖Λ‖ ^ (2 * m) * (L⁻¹ * B) := by
    rw [← hcov, ← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_unitCube
      ((hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.pow 2))
      (integrableOn_unitCube (continuous_const.mul
        ((hcf.comp (contDiff_slabMap t₀ t₁ 0).continuous).norm.pow 2))) measurableSet_unitCube
      fun y hy => ?_
    have h1 := norm_iteratedFDeriv_slabPeriodize_le hf h01 ha hb hz m hy
    calc ‖iteratedFDeriv ℝ m g y‖ ^ 2
        ≤ (‖iteratedFDeriv ℝ m f (slabMap (i₀ := i₀) t₀ t₁ 0 y)‖ * ‖Λ‖ ^ m) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ‖Λ‖ ^ (2 * m) * ‖iteratedFDeriv ℝ m f (slabMap (i₀ := i₀) t₀ t₁ 0 y)‖ ^ 2 := by ring
  obtain ⟨y, hy⟩ := exists_norm_iteratedFDeriv_le_slabPeriodize hf h01 ha hb hz j x
  have hgy := hCv g hg hgp y
  have hA0 : 0 ≤ A := setIntegral_nonneg (measurableSet_slabBox i₀ t₀ t₁) fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ B := setIntegral_nonneg (measurableSet_slabBox i₀ t₀ t₁) fun _ _ => sq_nonneg _
  have hsq : Real.sqrt ((∫ y in unitCube, ‖g y‖ ^ 2) +
      ∫ y in unitCube, ‖iteratedFDeriv ℝ m g y‖ ^ 2) ≤
      Real.sqrt (L⁻¹ * (1 + ‖Λ‖ ^ (2 * m))) * Real.sqrt (A + B) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [hA]
    have hΛ : 0 ≤ ‖Λ‖ ^ (2 * m) := by positivity
    have hLi : 0 < L⁻¹ := inv_pos.mpr hL
    nlinarith [mul_nonneg hLi.le hB0, mul_nonneg (mul_nonneg hLi.le hΛ) hA0]
  calc ‖iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℝ j g y‖ * ‖Λi‖ ^ j := hy
    _ ≤ (Cv * (Real.sqrt (L⁻¹ * (1 + ‖Λ‖ ^ (2 * m))) * Real.sqrt (A + B))) * ‖Λi‖ ^ j := by
        gcongr
        exact hgy.trans (mul_le_mul_of_nonneg_left hsq hCv0)
    _ = Cv * Real.sqrt (L⁻¹ * (1 + ‖Λ‖ ^ (2 * m))) * ‖Λi‖ ^ j * Real.sqrt (A + B) := by ring

end RenewalGeometry.SobolevBoxCr
