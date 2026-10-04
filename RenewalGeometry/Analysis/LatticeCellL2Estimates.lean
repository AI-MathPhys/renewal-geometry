/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# `L²` estimates for cell averaging and local averages on `ℝᵈ`

General infrastructure for the `L²`/Sobolev form of the smooth-core consistency estimate of the
paper `predictive_spectral_geometry` (`lem:supp-general-core`, `eq:supp-general-core`,
`eq:Wilson-core-smallness`).  All estimates are stated with lower Lebesgue integrals of
extended norms, so no integrability side conditions are needed.

* `lintegral_sq_le_measure_mul`: Cauchy–Schwarz `(∫⁻ G dν)² ≤ ν(univ) ∫⁻ G² dν`.
* `lintegral_sq_lintegral_add_le` (**Young/Minkowski for translation kernels**): for a finite
  measure `ν` on any space and offsets `φ`, `∫⁻_y (∫⁻_s g(y + φ s) dν)² ≤ ν(univ)² ∫⁻ g²`.
* Line Taylor bounds with integral remainders (`enorm_sub_le_lintegral_fderiv`,
  `enorm_taylor_one_le`): `‖f(p + t e) - f(p)‖ ≤ ∫_{-h}^{h} ‖Df(p + s e)‖ ds` and
  `‖f(p + t e) - f(p) - t Df(p) e‖ ≤ |t| ∫_{-h}^{h} ‖D²f(p + s e)‖ ds` for `|t| ≤ h`, `‖e‖ ≤ 1`.
* The cell decomposition of `ℝᵈ` at mesh `h` (`cellIdx`, `cell`, `cellAvg`): the cell of
  `x ∈ ℤᵈ` is `Π_i [h x_i, h x_i + h)`, `cellAvg h f x = h^{-d} ∫_{cell x} f` is the cell-average
  sampling `S_h = (𝒥⁰_h)^*`, and `y ↦ u(cellIdx h y)` is the piecewise-constant reconstruction
  `𝒥⁰_h u`.
* `lintegral_cell_shift_le`: an integral over a cell of a translate by at most `h` is dominated by
  the integral over the sup-norm ball of radius `2h` around any point of the cell.
* `lintegral_cellAvg_sub_sq_le` (**cell Poincaré**): `‖𝒥⁰_h S_h f - f‖²_{L²} ≤ 2ᵈ h² ‖Df‖²_{L²}`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.LatticeCellL2

/-! ### Cauchy–Schwarz and translation kernels -/

/-- Cauchy–Schwarz for a lower integral against a measure: `(∫⁻ G)² ≤ ν(univ) ∫⁻ G²`. -/
theorem lintegral_sq_le_measure_mul {S : Type*} [MeasurableSpace S] (ν : Measure S)
    {G : S → ℝ≥0∞} (hG : AEMeasurable G ν) :
    (∫⁻ s, G s ∂ν) ^ 2 ≤ ν univ * ∫⁻ s, G s ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hG
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have e1 : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have e2 : (fun s => G s ^ (2 : ℝ)) = fun s => G s ^ 2 := by
    funext s
    exact ENNReal.rpow_two (G s)
  rw [e2] at h
  calc (∫⁻ s, G s ∂ν) ^ 2
      ≤ ((∫⁻ s, G s ^ 2 ∂ν) ^ (1 / 2 : ℝ) * ν univ ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ bot_le h 2
    _ = ν univ * ∫⁻ s, G s ^ 2 ∂ν := by rw [mul_pow, e1, e1, mul_comm]

variable {d : ℕ}

/-- **Translation kernels are bounded on `L²`.**  For a finite measure `ν` on any measurable
space and measurable offsets `φ`, `∫⁻_y (∫⁻_s g(y + φ s) dν)² ≤ ν(univ)² ∫⁻ g²` (Lebesgue measure
on `ℝᵈ`). -/
theorem lintegral_sq_lintegral_add_le {S : Type*} [MeasurableSpace S] (ν : Measure S)
    [SFinite ν] (φ : S → (Fin d → ℝ)) (hφ : Measurable φ) {g : (Fin d → ℝ) → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ y, (∫⁻ s, g (y + φ s) ∂ν) ^ 2 ≤ ν univ ^ 2 * ∫⁻ y, g y ^ 2 := by
  have hjoint : Measurable fun p : (Fin d → ℝ) × S => g (p.1 + φ p.2) ^ 2 :=
    (hg.comp (measurable_fst.add (hφ.comp measurable_snd))).pow_const 2
  calc ∫⁻ y, (∫⁻ s, g (y + φ s) ∂ν) ^ 2
      ≤ ∫⁻ y, ν univ * ∫⁻ s, g (y + φ s) ^ 2 ∂ν := by
        refine lintegral_mono fun y => lintegral_sq_le_measure_mul ν ?_
        exact (hg.comp (measurable_const.add hφ)).aemeasurable
    _ = ν univ * ∫⁻ y, ∫⁻ s, g (y + φ s) ^ 2 ∂ν :=
        lintegral_const_mul _ hjoint.lintegral_prod_right'
    _ = ν univ * ∫⁻ s, (∫⁻ y, g (y + φ s) ^ 2) ∂ν := by
        rw [lintegral_lintegral_swap hjoint.aemeasurable]
    _ = ν univ * ∫⁻ s, (∫⁻ y, g y ^ 2) ∂ν := by
        congr 1
        refine lintegral_congr fun s => ?_
        exact lintegral_add_right_eq_self (fun y => g y ^ 2) (φ s)
    _ = ν univ ^ 2 * ∫⁻ y, g y ^ 2 := by
        rw [lintegral_const]
        ring

/-! ### Line Taylor bounds with integral remainders -/

section line

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem hasDerivAt_line {f : E → F} (hf : Differentiable ℝ f) (p e : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (p + s • e)) (fderiv ℝ f (p + t • e) e) t := by
  have h1 : HasDerivAt (fun s : ℝ => p + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add p
  exact (hf (p + t • e)).hasFDerivAt.comp_hasDerivAt t h1

/-- `‖∫_a^b g‖ₑ ≤ ∫⁻_{[min a b, max a b]} ‖g‖ₑ`. -/
theorem enorm_intervalIntegral_le (g : ℝ → F) (a b : ℝ) :
    ‖∫ s in a..b, g s‖ₑ ≤ ∫⁻ s in Icc (min a b) (max a b), ‖g s‖ₑ := by
  have h1 : ‖∫ s in a..b, g s‖ₑ = ‖∫ s in uIoc a b, g s‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm,
      intervalIntegral.norm_integral_eq_norm_integral_uIoc]
  rw [h1]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine lintegral_mono_set ?_
  intro s hs
  exact ⟨hs.1.le, hs.2⟩

/-- **First-order line bound.**  For a `C¹` map, `|t| ≤ h` and `‖e‖ ≤ 1`,
`‖f(p + t e) - f(p)‖ ≤ ∫_{[-h,h]} ‖Df(p + s e)‖ ds`. -/
theorem enorm_sub_le_lintegral_fderiv {f : E → F} (hf : ContDiff ℝ 1 f) (p e : E)
    (he : ‖e‖ ≤ 1) {h t : ℝ} (ht : |t| ≤ h) :
    ‖f (p + t • e) - f p‖ₑ ≤ ∫⁻ s in Icc (-h) h, ‖fderiv ℝ f (p + s • e)‖ₑ := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hcont : Continuous fun s : ℝ => fderiv ℝ f (p + s • e) e :=
    ((hf.continuous_fderiv (by norm_num)).comp (continuous_const.add
      (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hftc : ∫ s in (0 : ℝ)..t, fderiv ℝ f (p + s • e) e = f (p + t • e) - f p := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_line hd p e s)
      (hcont.intervalIntegrable _ _)]
    simp
  rw [← hftc]
  refine (enorm_intervalIntegral_le _ 0 t).trans ?_
  have hsub : Icc (min 0 t) (max 0 t) ⊆ Icc (-h) h := by
    intro s hs
    have h1 := abs_le.mp ht
    constructor
    · exact le_trans (by simp only [le_min_iff]; constructor <;> linarith [abs_nonneg t])
        hs.1
    · exact le_trans hs.2 (by simp only [max_le_iff]; constructor <;> linarith [abs_nonneg t])
  refine (lintegral_mono_set hsub).trans' ?_
  refine lintegral_mono fun s => ?_
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖fderiv ℝ f (p + s • e) e‖ ≤ ‖fderiv ℝ f (p + s • e)‖ * ‖e‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ f (p + s • e)‖ * 1 := by gcongr
    _ = _ := mul_one _

/-- The norm of the second derivative as the norm of the derivative of the derivative. -/
theorem norm_fderiv_fderiv_eq (f : E → F) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

/-- **Derivative increment along a line.**  For a `C²` map, `|t| ≤ h`, `‖e‖ ≤ 1`,
`‖Df(p + t e) - Df(p)‖ ≤ ∫_{[-h,h]} ‖D²f(p + s e)‖ ds`. -/
theorem enorm_fderiv_sub_le {f : E → F} (hf : ContDiff ℝ 2 f) (p e : E) (he : ‖e‖ ≤ 1)
    {h t : ℝ} (ht : |t| ≤ h) :
    ‖fderiv ℝ f (p + t • e) - fderiv ℝ f p‖ₑ ≤
      ∫⁻ s in Icc (-h) h, ‖iteratedFDeriv ℝ 2 f (p + s • e)‖ₑ := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  refine (enorm_sub_le_lintegral_fderiv h1 p e he ht).trans (le_of_eq ?_)
  refine lintegral_congr fun s => ?_
  rw [← ofReal_norm, ← ofReal_norm, norm_fderiv_fderiv_eq]

/-- **First-order Taylor bound with integral remainder.**  For a `C²` map, `|t| ≤ h`,
`‖e‖ ≤ 1`: `‖f(p + t e) - f(p) - t Df(p) e‖ ≤ |t| ∫_{[-h,h]} ‖D²f(p + s e)‖ ds`. -/
theorem enorm_taylor_one_le {f : E → F} (hf : ContDiff ℝ 2 f) (p e : E) (he : ‖e‖ ≤ 1)
    {h t : ℝ} (ht : |t| ≤ h) :
    ‖f (p + t • e) - f p - t • fderiv ℝ f p e‖ₑ ≤
      ENNReal.ofReal |t| * ∫⁻ s in Icc (-h) h, ‖iteratedFDeriv ℝ 2 f (p + s • e)‖ₑ := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hcont : Continuous fun s : ℝ => fderiv ℝ f (p + s • e) e :=
    ((hf.continuous_fderiv (by norm_num)).comp (continuous_const.add
      (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hftc : ∫ s in (0 : ℝ)..t, (fderiv ℝ f (p + s • e) e - fderiv ℝ f p e) =
      f (p + t • e) - f p - t • fderiv ℝ f p e := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_line hd p e s)
        (hcont.intervalIntegrable _ _)]
    simp
  rw [← hftc]
  set I := ∫⁻ s in Icc (-h) h, ‖iteratedFDeriv ℝ 2 f (p + s • e)‖ₑ
  refine (enorm_intervalIntegral_le _ 0 t).trans ?_
  have hpt : ∀ s ∈ Icc (min 0 t) (max 0 t),
      ‖fderiv ℝ f (p + s • e) e - fderiv ℝ f p e‖ₑ ≤ I := by
    intro s hs
    have hs' : |s| ≤ h := by
      have h1 := abs_le.mp ht
      rw [abs_le]
      constructor
      · exact le_trans (by simp only [le_min_iff]; constructor <;> linarith [abs_nonneg t])
          hs.1
      · exact le_trans hs.2 (by simp only [max_le_iff]; constructor <;> linarith [abs_nonneg t])
    have h2 := enorm_fderiv_sub_le hf p e he hs'
    refine le_trans ?_ h2
    rw [← ContinuousLinearMap.sub_apply, ← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖(fderiv ℝ f (p + s • e) - fderiv ℝ f p) e‖
        ≤ ‖fderiv ℝ f (p + s • e) - fderiv ℝ f p‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ f (p + s • e) - fderiv ℝ f p‖ * 1 := by gcongr
      _ = _ := mul_one _
  calc ∫⁻ s in Icc (min 0 t) (max 0 t), ‖fderiv ℝ f (p + s • e) e - fderiv ℝ f p e‖ₑ
      ≤ ∫⁻ _ in Icc (min 0 t) (max 0 t), I := setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal |t| * I := by
        rw [setLIntegral_const, Real.volume_Icc, mul_comm]
        congr 2
        rcases le_total 0 t with h0 | h0
        · rw [min_eq_left h0, max_eq_right h0, abs_of_nonneg h0, sub_zero]
        · rw [min_eq_right h0, max_eq_left h0, abs_of_nonpos h0, zero_sub]

end line

/-! ### The cell decomposition of `ℝᵈ` -/

section cells

variable {d : ℕ}

/-- The index `x ∈ ℤᵈ` of the mesh-`h` cell containing `y`: `x_i = ⌊y_i / h⌋`. -/
def cellIdx (h : ℝ) (y : Fin d → ℝ) : Fin d → ℤ := fun i => ⌊y i / h⌋

/-- The mesh-`h` cell of `x ∈ ℤᵈ` (equal to `Π_i [h x_i, h x_i + h)` for `h > 0`). -/
def cell (h : ℝ) (x : Fin d → ℤ) : Set (Fin d → ℝ) := {y | cellIdx h y = x}

/-- The lattice vector `h v` of `v ∈ ℤᵈ`. -/
def latticeVec (h : ℝ) (v : Fin d → ℤ) : Fin d → ℝ := fun i => h * (v i : ℝ)

theorem mem_cell_cellIdx (h : ℝ) (y : Fin d → ℝ) : y ∈ cell h (cellIdx h y) := rfl

theorem measurable_cellIdx (h : ℝ) : Measurable (cellIdx (d := d) h) := by
  apply measurable_pi_lambda
  intro i
  have hi : Measurable fun y : Fin d → ℝ => y i := measurable_pi_apply i
  exact (hi.div_const h).floor

theorem measurableSet_cell (h : ℝ) (x : Fin d → ℤ) : MeasurableSet (cell h x) :=
  measurable_cellIdx h (measurableSet_singleton x)

theorem cell_eq_pi {h : ℝ} (hh : 0 < h) (x : Fin d → ℤ) :
    cell h x = univ.pi fun i => Ico (h * x i) (h * x i + h) := by
  ext y
  simp only [cell, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico]
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  show ⌊y i / h⌋ = x i ↔ _
  rw [Int.floor_eq_iff, le_div_iff₀ hh, div_lt_iff₀ hh]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

theorem volume_cell {h : ℝ} (hh : 0 < h) (x : Fin d → ℤ) :
    volume (cell h x) = ENNReal.ofReal (h ^ d) := by
  rw [cell_eq_pi hh, Real.volume_pi_Ico]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hh.le]

theorem norm_sub_lt_of_mem_cell {h : ℝ} (hh : 0 < h) {x : Fin d → ℤ} {y z : Fin d → ℝ}
    (hy : y ∈ cell h x) (hz : z ∈ cell h x) : ‖z - y‖ < h := by
  rw [cell_eq_pi hh] at hy hz
  rw [pi_norm_lt_iff hh]
  intro i
  have h1 := hy i (mem_univ i)
  have h2 := hz i (mem_univ i)
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem convex_cell {h : ℝ} (hh : 0 < h) (x : Fin d → ℤ) : Convex ℝ (cell h x) := by
  rw [cell_eq_pi hh]
  exact convex_pi fun i _ => convex_Ico _ _

theorem cellIdx_add_latticeVec {h : ℝ} (hh : 0 < h) (y : Fin d → ℝ) (v : Fin d → ℤ) :
    cellIdx h (y + latticeVec h v) = cellIdx h y + v := by
  funext i
  simp only [cellIdx, latticeVec, Pi.add_apply]
  rw [add_div, mul_div_cancel_left₀ _ hh.ne', Int.floor_add_intCast]

theorem mem_cell_add_latticeVec_iff {h : ℝ} (hh : 0 < h) (x v : Fin d → ℤ)
    (y : Fin d → ℝ) : y + latticeVec h v ∈ cell h (x + v) ↔ y ∈ cell h x := by
  simp only [cell, mem_setOf_eq, cellIdx_add_latticeVec hh]
  exact add_left_inj v

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Cell-average sampling** `S_h f (x) = h^{-d} ∫_{cell x} f` (the adjoint of the isometric
piecewise-constant reconstruction for the cell weight `h^d`). -/
def cellAvg (h : ℝ) (f : (Fin d → ℝ) → F) (x : Fin d → ℤ) : F :=
  (h ^ d)⁻¹ • ∫ y in cell h x, f y

/-- Lattice translation of the cell integral: `∫_{cell (x+v)} f = ∫_{cell x} f(z + h v)`. -/
theorem setIntegral_cell_add {h : ℝ} (hh : 0 < h) (f : (Fin d → ℝ) → F) (x v : Fin d → ℤ) :
    ∫ y in cell h (x + v), f y = ∫ z in cell h x, f (z + latticeVec h v) := by
  rw [← integral_indicator (measurableSet_cell h _), ← integral_indicator (measurableSet_cell h _)]
  rw [← integral_add_right_eq_self (μ := volume)
    (fun y => (cell h (x + v)).indicator f y) (latticeVec h v)]
  congr 1
  funext z
  by_cases hz : z ∈ cell h x
  · rw [indicator_of_mem hz, indicator_of_mem ((mem_cell_add_latticeVec_iff hh x v z).mpr hz)]
  · rw [indicator_of_notMem hz,
      indicator_of_notMem (fun h' => hz ((mem_cell_add_latticeVec_iff hh x v z).mp h'))]

theorem cellAvg_add {h : ℝ} (hh : 0 < h) (f : (Fin d → ℝ) → F) (x v : Fin d → ℤ) :
    cellAvg h f (x + v) = (h ^ d)⁻¹ • ∫ z in cell h x, f (z + latticeVec h v) := by
  rw [cellAvg, setIntegral_cell_add hh]

/-- **Domination of cell integrals of translates.**  If `y` lies in the cell of `x` and
`‖v‖ ≤ h`, the integral over the cell of `G(· + v)` is at most the integral of `G` over the
sup-norm ball of radius `2h` around `y`. -/
theorem lintegral_cell_shift_le {h : ℝ} (hh : 0 < h) {x : Fin d → ℤ} {y : Fin d → ℝ}
    (hy : y ∈ cell h x) (v : Fin d → ℝ) (hv : ‖v‖ ≤ h) {G : (Fin d → ℝ) → ℝ≥0∞} :
    ∫⁻ z in cell h x, G (z + v) ≤
      ∫⁻ τ in Metric.closedBall (0 : Fin d → ℝ) (2 * h), G (y + τ) := by
  rw [← lintegral_indicator (measurableSet_cell h x),
    ← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  rw [← lintegral_add_right_eq_self (μ := volume)
    (fun z => (cell h x).indicator (fun z => G (z + v)) z) (y - v)]
  refine lintegral_mono fun τ => ?_
  by_cases hτ : τ + (y - v) ∈ cell h x
  · rw [indicator_of_mem hτ]
    have hball : τ ∈ Metric.closedBall (0 : Fin d → ℝ) (2 * h) := by
      rw [mem_closedBall_zero_iff]
      have h1 := norm_sub_lt_of_mem_cell hh hy hτ
      have h2 : τ = (τ + (y - v) - y) + v := by abel
      rw [h2]
      calc ‖τ + (y - v) - y + v‖ ≤ ‖τ + (y - v) - y‖ + ‖v‖ := norm_add_le _ _
        _ ≤ 2 * h := by linarith
    rw [indicator_of_mem hball]
    have : τ + (y - v) + v = y + τ := by abel
    rw [this]
  · rw [indicator_of_notMem hτ]
    exact bot_le

/-- The local average kernel `h^{-d} 1_{‖τ‖ ≤ 2h} dτ` has total mass `4ᵈ`. -/
theorem ballKernel_mass {h : ℝ} (hh : 0 < h) :
    (ENNReal.ofReal (h ^ d))⁻¹ * volume (Metric.closedBall (0 : Fin d → ℝ) (2 * h)) =
      4 ^ d := by
  rw [Real.volume_pi_closedBall _ (by positivity), Fintype.card_fin]
  have hpos : 0 < h ^ d := pow_pos hh d
  have hc : ENNReal.ofReal (h ^ d) ≠ 0 := by simpa using hpos
  rw [show (2 * (2 * h)) ^ d = 4 ^ d * h ^ d by rw [← mul_pow]; ring_nf,
    ENNReal.ofReal_mul (by positivity), ← mul_assoc, mul_comm _ (ENNReal.ofReal (4 ^ d)),
    mul_assoc, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, mul_one,
    ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- **`L²` bound for the local average at scale `2h`**:
`∫⁻_y (h^{-d} ∫_{‖τ‖ ≤ 2h} g(y + τ))² ≤ 16ᵈ ∫⁻ g²`. -/
theorem lintegral_sq_ballAverage_le {h : ℝ} (hh : 0 < h) {g : (Fin d → ℝ) → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ y, ((ENNReal.ofReal (h ^ d))⁻¹ *
        ∫⁻ τ in Metric.closedBall (0 : Fin d → ℝ) (2 * h), g (y + τ)) ^ 2 ≤
      16 ^ d * ∫⁻ y, g y ^ 2 := by
  set ν : Measure (Fin d → ℝ) := (ENNReal.ofReal (h ^ d))⁻¹ •
    volume.restrict (Metric.closedBall (0 : Fin d → ℝ) (2 * h))
  have hmass : ν univ = 4 ^ d := by
    simp only [ν, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul]
    exact ballKernel_mass hh
  have hfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hmass]
    exact ENNReal.pow_lt_top (by norm_num)
  have h1 := lintegral_sq_lintegral_add_le ν id measurable_id hg
  have heq : ∀ y, ∫⁻ s, g (y + id s) ∂ν = (ENNReal.ofReal (h ^ d))⁻¹ *
      ∫⁻ τ in Metric.closedBall (0 : Fin d → ℝ) (2 * h), g (y + τ) := by
    intro y
    simp only [ν, lintegral_smul_measure, id, smul_eq_mul]
  simp only [heq, hmass] at h1
  calc _ ≤ (4 ^ d) ^ 2 * ∫⁻ y, g y ^ 2 := h1
    _ = 16 ^ d * ∫⁻ y, g y ^ 2 := by
        congr 1
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num

end cells

/-! ### The cell Poincaré inequality -/

section poincare

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Mean value bound with integral remainder along a segment:
`‖f(p + e) - f(p)‖ ≤ ‖e‖ ∫_0^1 ‖Df(p + s e)‖ ds`. -/
theorem enorm_sub_le_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → F}
    (hf : ContDiff ℝ 1 f) (p e : E) :
    ‖f (p + e) - f p‖ₑ ≤ ‖e‖ₑ * ∫⁻ s in Icc (0 : ℝ) 1, ‖fderiv ℝ f (p + s • e)‖ₑ := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hcont : Continuous fun s : ℝ => fderiv ℝ f (p + s • e) e :=
    ((hf.continuous_fderiv (by norm_num)).comp (continuous_const.add
      (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hftc : ∫ s in (0 : ℝ)..1, fderiv ℝ f (p + s • e) e = f (p + e) - f p := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_line hd p e s)
      (hcont.intervalIntegrable _ _)]
    simp
  rw [← hftc]
  refine (enorm_intervalIntegral_le _ 0 1).trans ?_
  rw [min_eq_left zero_le_one, max_eq_right zero_le_one, ← lintegral_const_mul' _ _ enorm_ne_top]
  refine lintegral_mono fun s => ?_
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_comm]
  exact ContinuousLinearMap.le_opNorm _ _

/-- Affine change of variables: `∫⁻ u, G(r u + w) = (rᵈ)⁻¹ ∫⁻ G` for `r > 0`. -/
theorem lintegral_comp_smul_add {G : (Fin d → ℝ) → ℝ≥0∞} (hG : Measurable G) {r : ℝ}
    (hr : 0 < r) (w : Fin d → ℝ) :
    ∫⁻ u, G (r • u + w) = (ENNReal.ofReal (r ^ d))⁻¹ * ∫⁻ u, G u := by
  have h1 : ∫⁻ u, G (r • u + w) = ∫⁻ u, (fun v => G (v + w)) u
      ∂(Measure.map (r • ·) volume) :=
    (lintegral_map (f := fun v => G (v + w)) (hG.comp (measurable_add_const w))
      (measurable_const_smul r)).symm
  rw [h1, Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure,
    lintegral_add_right_eq_self (fun v => G v) w, Module.finrank_fin_fun, smul_eq_mul]
  congr 1
  rw [abs_of_pos (inv_pos.mpr (pow_pos hr d)), ENNReal.ofReal_inv_of_pos (pow_pos hr d)]

theorem measurableSet_sameCell (h : ℝ) :
    MeasurableSet {p : (Fin d → ℝ) × (Fin d → ℝ) | cellIdx h p.2 = cellIdx h p.1} :=
  measurableSet_eq_fun ((measurable_cellIdx h).comp measurable_snd)
    ((measurable_cellIdx h).comp measurable_fst)

theorem indicator_cell_eq (h : ℝ) (G : (Fin d → ℝ) → ℝ≥0∞) :
    (fun p : (Fin d → ℝ) × (Fin d → ℝ) => (cell h (cellIdx h p.1)).indicator G p.2) =
      {p : (Fin d → ℝ) × (Fin d → ℝ) | cellIdx h p.2 = cellIdx h p.1}.indicator
        (fun p => G p.2) := by
  funext p
  by_cases hp : cellIdx h p.2 = cellIdx h p.1
  · rw [indicator_of_mem (show p.2 ∈ cell h (cellIdx h p.1) from hp),
      indicator_of_mem (show p ∈ {p : (Fin d → ℝ) × (Fin d → ℝ) |
        cellIdx h p.2 = cellIdx h p.1} from hp)]
  · rw [indicator_of_notMem (show p.2 ∉ cell h (cellIdx h p.1) from hp),
      indicator_of_notMem (show p ∉ {p : (Fin d → ℝ) × (Fin d → ℝ) |
        cellIdx h p.2 = cellIdx h p.1} from hp)]

/-- The joint integral over pairs of points in a common cell of `G` at a convex combination. -/
theorem lintegral_lintegral_cell_comb_le {h : ℝ} (hh : 0 < h) {G : (Fin d → ℝ) → ℝ≥0∞}
    (hG : Measurable G) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ v, ∫⁻ u, (if cellIdx h u = cellIdx h v then G (r • u + (1 - r) • v) else 0) ≤
      (ENNReal.ofReal (r ^ d))⁻¹ * ENNReal.ofReal (h ^ d) * ∫⁻ w, G w := by
  have hpt : ∀ v u, (if cellIdx h u = cellIdx h v then G (r • u + (1 - r) • v) else 0) ≤
      (cell h (cellIdx h v)).indicator G (r • u + (1 - r) • v) := by
    intro v u
    split_ifs with huv
    · have hmem : r • u + (1 - r) • v ∈ cell h (cellIdx h v) := by
        have hu : u ∈ cell h (cellIdx h v) := huv
        exact convex_cell hh _ hu (mem_cell_cellIdx h v) hr0.le (by linarith) (by ring)
      rw [indicator_of_mem hmem]
    · exact bot_le
  have hGi : ∀ v, Measurable ((cell h (cellIdx h v)).indicator G) :=
    fun v => hG.indicator (measurableSet_cell h _)
  have hjm : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      (cell h (cellIdx h p.1)).indicator G p.2 := by
    rw [indicator_cell_eq]
    exact (hG.comp measurable_snd).indicator (measurableSet_sameCell h)
  calc ∫⁻ v, ∫⁻ u, (if cellIdx h u = cellIdx h v then G (r • u + (1 - r) • v) else 0)
      ≤ ∫⁻ v, ∫⁻ u, (cell h (cellIdx h v)).indicator G (r • u + (1 - r) • v) :=
        lintegral_mono fun v => lintegral_mono fun u => hpt v u
    _ = ∫⁻ v, (ENNReal.ofReal (r ^ d))⁻¹ * ∫⁻ w, (cell h (cellIdx h v)).indicator G w := by
        refine lintegral_congr fun v => ?_
        exact lintegral_comp_smul_add (hGi v) hr0 _
    _ = (ENNReal.ofReal (r ^ d))⁻¹ * ∫⁻ v, ∫⁻ w, (cell h (cellIdx h v)).indicator G w := by
        rw [lintegral_const_mul]
        exact hjm.lintegral_prod_right'
    _ = (ENNReal.ofReal (r ^ d))⁻¹ * ∫⁻ w, ∫⁻ v, (cell h (cellIdx h v)).indicator G w := by
        rw [lintegral_lintegral_swap hjm.aemeasurable]
    _ = (ENNReal.ofReal (r ^ d))⁻¹ * ∫⁻ w, ENNReal.ofReal (h ^ d) * G w := by
        congr 1
        refine lintegral_congr fun w => ?_
        have : (fun v => (cell h (cellIdx h v)).indicator G w) =
            (cell h (cellIdx h w)).indicator (fun _ => G w) := by
          funext v
          by_cases hv : cellIdx h v = cellIdx h w
          · have h1 : w ∈ cell h (cellIdx h v) := hv.symm
            have h2 : v ∈ cell h (cellIdx h w) := hv
            rw [indicator_of_mem h1, indicator_of_mem h2]
          · have h1 : w ∉ cell h (cellIdx h v) := fun h' => hv h'.symm
            have h2 : v ∉ cell h (cellIdx h w) := hv
            rw [indicator_of_notMem h1, indicator_of_notMem h2]
        rw [this, lintegral_indicator_const (measurableSet_cell h _), volume_cell hh, mul_comm]
    _ = (ENNReal.ofReal (r ^ d))⁻¹ * ENNReal.ofReal (h ^ d) * ∫⁻ w, G w := by
        rw [lintegral_const_mul _ hG, mul_assoc]

/-- **Cell Poincaré inequality** on `ℝᵈ` at mesh `h`:
`‖𝒥⁰_h S_h f - f‖²_{L²} = ∫ ‖S_h f(cellIdx y) - f(y)‖² dy ≤ 2ᵈ h² ∫ ‖Df‖²`. -/
theorem lintegral_cellAvg_sub_sq_le {f : (Fin d → ℝ) → F} (hf : ContDiff ℝ 1 f) {h : ℝ}
    (hh : 0 < h) :
    ∫⁻ y, ‖cellAvg h f (cellIdx h y) - f y‖ₑ ^ 2 ≤
      2 ^ d * ENNReal.ofReal (h ^ 2) * ∫⁻ y, ‖fderiv ℝ f y‖ₑ ^ 2 := by
  set G : (Fin d → ℝ) → ℝ≥0∞ := fun w => ‖fderiv ℝ f w‖ₑ ^ 2 with hGdef
  have hG : Measurable G :=
    ((hf.continuous_fderiv (by norm_num)).enorm.measurable).pow_const 2
  have hhd : 0 < h ^ d := pow_pos hh d
  have hcd : ENNReal.ofReal (h ^ d) ≠ 0 := by simpa using hhd
  -- Step 1: pointwise bound
  have hstep1 : ∀ y, ‖cellAvg h f (cellIdx h y) - f y‖ₑ ^ 2 ≤
      (ENNReal.ofReal (h ^ d))⁻¹ * ENNReal.ofReal (h ^ 2) *
        ∫⁻ z in cell h (cellIdx h y), ∫⁻ s in Icc (0 : ℝ) 1,
          G (y + s • (z - y)) := by
    intro y
    set Q := cell h (cellIdx h y)
    have hQb : Q ⊆ Metric.closedBall y h := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact (norm_sub_lt_of_mem_cell hh (mem_cell_cellIdx h y) hz).le
    have hint : IntegrableOn f Q :=
      (hf.continuous.continuousOn.integrableOn_compact (isCompact_closedBall y h)).mono_set hQb
    have hQvol : volume Q = ENNReal.ofReal (h ^ d) := volume_cell hh _
    have hvol : volume.real Q = h ^ d := by
      rw [Measure.real, hQvol, ENNReal.toReal_ofReal hhd.le]
    have heq : cellAvg h f (cellIdx h y) - f y = (h ^ d)⁻¹ • ∫ z in Q, (f z - f y) := by
      rw [integral_sub hint (integrableOn_const (by rw [hQvol]; exact ENNReal.ofReal_ne_top)),
        setIntegral_const, smul_sub, cellAvg, hvol, smul_smul,
        inv_mul_cancel₀ hhd.ne', one_smul]
    have hb1 : ‖cellAvg h f (cellIdx h y) - f y‖ₑ ≤
        (ENNReal.ofReal (h ^ d))⁻¹ * ∫⁻ z in Q, ‖f z - f y‖ₑ := by
      rw [heq, enorm_smul, ← ofReal_norm, Real.norm_eq_abs, abs_inv, abs_of_pos hhd,
        ENNReal.ofReal_inv_of_pos hhd]
      exact mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)
    have hb2 : ∀ z ∈ Q, ‖f z - f y‖ₑ ^ 2 ≤ ENNReal.ofReal (h ^ 2) *
        ∫⁻ s in Icc (0 : ℝ) 1, G (y + s • (z - y)) := by
      intro z hz
      have h1 := enorm_sub_le_segment hf y (z - y)
      rw [add_sub_cancel] at h1
      have hzy : ‖z - y‖ₑ ≤ ENNReal.ofReal h := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal
          (norm_sub_lt_of_mem_cell hh (mem_cell_cellIdx h y) hz).le
      have h2 := lintegral_sq_le_measure_mul (volume.restrict (Icc (0 : ℝ) 1))
        (G := fun s => ‖fderiv ℝ f (y + s • (z - y))‖ₑ)
        (((hf.continuous_fderiv (by norm_num)).comp (continuous_const.add
          (continuous_id.smul continuous_const))).enorm.measurable.aemeasurable)
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc, sub_zero,
        ENNReal.ofReal_one, one_mul] at h2
      calc ‖f z - f y‖ₑ ^ 2
          ≤ (‖z - y‖ₑ * ∫⁻ s in Icc (0 : ℝ) 1, ‖fderiv ℝ f (y + s • (z - y))‖ₑ) ^ 2 :=
            pow_le_pow_left₀ bot_le h1 2
        _ ≤ (ENNReal.ofReal h *
              ∫⁻ s in Icc (0 : ℝ) 1, ‖fderiv ℝ f (y + s • (z - y))‖ₑ) ^ 2 := by
            gcongr
        _ = ENNReal.ofReal (h ^ 2) *
              (∫⁻ s in Icc (0 : ℝ) 1, ‖fderiv ℝ f (y + s • (z - y))‖ₑ) ^ 2 := by
            rw [mul_pow, ← ENNReal.ofReal_pow hh.le]
        _ ≤ ENNReal.ofReal (h ^ 2) * ∫⁻ s in Icc (0 : ℝ) 1, G (y + s • (z - y)) := by
            gcongr
    calc ‖cellAvg h f (cellIdx h y) - f y‖ₑ ^ 2
        ≤ ((ENNReal.ofReal (h ^ d))⁻¹ * ∫⁻ z in Q, ‖f z - f y‖ₑ) ^ 2 :=
          pow_le_pow_left₀ bot_le hb1 2
      _ = (ENNReal.ofReal (h ^ d))⁻¹ ^ 2 * (∫⁻ z in Q, ‖f z - f y‖ₑ) ^ 2 := mul_pow _ _ _
      _ ≤ (ENNReal.ofReal (h ^ d))⁻¹ ^ 2 * (ENNReal.ofReal (h ^ d) *
            ∫⁻ z in Q, ‖f z - f y‖ₑ ^ 2) := by
          gcongr
          have := lintegral_sq_le_measure_mul (volume.restrict Q)
            (G := fun z => ‖f z - f y‖ₑ)
            ((hf.continuous.sub continuous_const).enorm.measurable.aemeasurable)
          rwa [Measure.restrict_apply MeasurableSet.univ, univ_inter, hQvol] at this
      _ = (ENNReal.ofReal (h ^ d))⁻¹ * ∫⁻ z in Q, ‖f z - f y‖ₑ ^ 2 := by
          rw [sq, mul_assoc, ← mul_assoc _ (ENNReal.ofReal (h ^ d)),
            ENNReal.inv_mul_cancel hcd ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal (h ^ d))⁻¹ * ∫⁻ z in Q, ENNReal.ofReal (h ^ 2) *
            ∫⁻ s in Icc (0 : ℝ) 1, G (y + s • (z - y)) :=
          mul_le_mul' le_rfl (setLIntegral_mono' (measurableSet_cell h _) hb2)
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc]
  -- Step 2: integrate and use Tonelli
  set K : ℝ → ℝ≥0∞ := fun s => ∫⁻ y, ∫⁻ z,
    (if cellIdx h z = cellIdx h y then G (y + s • (z - y)) else 0) with hK
  have hjoint : Measurable fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ =>
      (if cellIdx h q.1.2 = cellIdx h q.1.1 then G (q.1.1 + q.2 • (q.1.2 - q.1.1)) else 0) := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_sameCell h).preimage measurable_fst
    · exact hG.comp ((measurable_fst.comp measurable_fst).add (measurable_snd.smul
        ((measurable_snd.comp measurable_fst).sub (measurable_fst.comp measurable_fst))))
  have hstep2 : ∫⁻ y, ∫⁻ z in cell h (cellIdx h y), ∫⁻ s in Icc (0 : ℝ) 1,
      G (y + s • (z - y)) = ∫⁻ s in Icc (0 : ℝ) 1, K s := by
    have e1 : ∀ y, ∫⁻ z in cell h (cellIdx h y), ∫⁻ s in Icc (0 : ℝ) 1, G (y + s • (z - y)) =
        ∫⁻ z, ∫⁻ s in Icc (0 : ℝ) 1,
          (if cellIdx h z = cellIdx h y then G (y + s • (z - y)) else 0) := by
      intro y
      rw [← lintegral_indicator (measurableSet_cell h _)]
      refine lintegral_congr fun z => ?_
      by_cases hz : cellIdx h z = cellIdx h y
      · rw [indicator_of_mem (show z ∈ cell h (cellIdx h y) from hz)]
        simp only [hz, if_true]
      · rw [indicator_of_notMem (show z ∉ cell h (cellIdx h y) from hz)]
        simp only [hz, if_false, lintegral_zero]
    simp_rw [e1]
    have e2 : ∀ y, ∫⁻ z, ∫⁻ s in Icc (0 : ℝ) 1,
        (if cellIdx h z = cellIdx h y then G (y + s • (z - y)) else 0) =
        ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ z,
        (if cellIdx h z = cellIdx h y then G (y + s • (z - y)) else 0) := by
      intro y
      refine lintegral_lintegral_swap ?_
      exact (hjoint.comp ((measurable_const.prodMk measurable_fst).prodMk
        measurable_snd)).aemeasurable
    simp_rw [e2]
    rw [hK]
    refine lintegral_lintegral_swap ?_
    exact (Measurable.lintegral_prod_right' (ν := volume)
      (f := fun q : ((Fin d → ℝ) × ℝ) × (Fin d → ℝ) =>
        (if cellIdx h q.2 = cellIdx h q.1.1 then G (q.1.1 + q.1.2 • (q.2 - q.1.1)) else 0))
      (hjoint.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd
        |>.prodMk (measurable_snd.comp measurable_fst)))).aemeasurable
  -- Step 3: bound `K s`
  have hstep3 : ∀ s ∈ Icc (0 : ℝ) 1, K s ≤ 2 ^ d * ENNReal.ofReal (h ^ d) * ∫⁻ w, G w := by
    intro s hs
    have hcomb : ∀ y z : Fin d → ℝ, y + s • (z - y) = (1 - s) • y + s • z := by
      intro y z
      rw [smul_sub, sub_smul, one_smul]
      abel
    have hpow : ∀ r : ℝ, 0 < r → 1 / 2 ≤ r →
        (ENNReal.ofReal (r ^ d))⁻¹ ≤ (2 : ℝ≥0∞) ^ d := by
      intro r hr hr2
      rw [← ENNReal.ofReal_inv_of_pos (pow_pos hr d)]
      have h2 : (2 : ℝ≥0∞) ^ d = ENNReal.ofReal (2 ^ d) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        norm_num
      rw [h2]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ d
      rw [inv_le_comm₀ hr (by norm_num)]
      linarith
    rcases le_total s (1 / 2) with hs2 | hs2
    · -- substitute in `y`
      have hr0 : 0 < 1 - s := by linarith
      have h1 : K s = ∫⁻ z, ∫⁻ y, (if cellIdx h y = cellIdx h z then
          G ((1 - s) • y + (1 - (1 - s)) • z) else 0) := by
        rw [hK]
        dsimp only
        rw [lintegral_lintegral_swap]
        · refine lintegral_congr fun z => lintegral_congr fun y => ?_
          rw [hcomb, sub_sub_cancel]
          by_cases hyz : cellIdx h y = cellIdx h z
          · simp [hyz]
          · have : ¬ cellIdx h z = cellIdx h y := fun h' => hyz h'.symm
            simp [hyz, this]
        · exact (hjoint.comp (measurable_id.prodMk measurable_const)).aemeasurable
      rw [h1]
      refine (lintegral_lintegral_cell_comb_le hh hG hr0 (by linarith [hs.1])).trans ?_
      gcongr
      exact hpow _ hr0 (by linarith)
    · -- substitute in `z`
      have hr0 : 0 < s := by linarith
      have h1 : K s = ∫⁻ y, ∫⁻ z, (if cellIdx h z = cellIdx h y then
          G (s • z + (1 - s) • y) else 0) := by
        rw [hK]
        refine lintegral_congr fun y => lintegral_congr fun z => ?_
        rw [hcomb, add_comm]
      rw [h1]
      refine (lintegral_lintegral_cell_comb_le hh hG hr0 hs.2).trans ?_
      gcongr
      exact hpow _ hr0 hs2
  -- Step 4: assemble
  calc ∫⁻ y, ‖cellAvg h f (cellIdx h y) - f y‖ₑ ^ 2
      ≤ ∫⁻ y, (ENNReal.ofReal (h ^ d))⁻¹ * ENNReal.ofReal (h ^ 2) *
          ∫⁻ z in cell h (cellIdx h y), ∫⁻ s in Icc (0 : ℝ) 1, G (y + s • (z - y)) :=
        lintegral_mono hstep1
    _ = (ENNReal.ofReal (h ^ d))⁻¹ * ENNReal.ofReal (h ^ 2) *
          ∫⁻ y, ∫⁻ z in cell h (cellIdx h y), ∫⁻ s in Icc (0 : ℝ) 1, G (y + s • (z - y)) := by
        rw [lintegral_const_mul']
        exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hcd) ENNReal.ofReal_ne_top
    _ = (ENNReal.ofReal (h ^ d))⁻¹ * ENNReal.ofReal (h ^ 2) * ∫⁻ s in Icc (0 : ℝ) 1, K s := by
        rw [hstep2]
    _ ≤ (ENNReal.ofReal (h ^ d))⁻¹ * ENNReal.ofReal (h ^ 2) *
          ∫⁻ _ in Icc (0 : ℝ) 1, 2 ^ d * ENNReal.ofReal (h ^ d) * ∫⁻ w, G w :=
        mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Icc hstep3)
    _ = 2 ^ d * ENNReal.ofReal (h ^ 2) * ∫⁻ y, ‖fderiv ℝ f y‖ₑ ^ 2 := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
        rw [show (ENNReal.ofReal (h ^ d))⁻¹ * ENNReal.ofReal (h ^ 2) *
            (2 ^ d * ENNReal.ofReal (h ^ d) * ∫⁻ w, G w) =
            ((ENNReal.ofReal (h ^ d))⁻¹ * ENNReal.ofReal (h ^ d)) *
              (2 ^ d * ENNReal.ofReal (h ^ 2) * ∫⁻ w, G w) by ring]
        rw [ENNReal.inv_mul_cancel hcd ENNReal.ofReal_ne_top, one_mul]

end poincare

end RenewalGeometry.LatticeCellL2
