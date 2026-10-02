/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterEnergyIdentity

/-!
# The positive `A₃ ≅ D₃` rate lift of a small metric
  (`eq:supp-open-d3-roots`, `eq:supp-open-rate-lift`, `eq:supp-open-rate-inversion`;
  clause (O3) of `thm:main-open-3plus1`; emergent-spacetime manuscript)

**Root data.**  The six `D₃` roots `r_a` of `eq:supp-open-d3-roots` are indexed by
`a = (k, σ) ∈ Fin 3 × Bool` (`D3Root`): `k` is the *remaining* coordinate index of the pair
`(i, j) = (k + 1, k + 2)` (mod 3) and `σ` the sign, `r_{k,σ} = e_i + sgn σ · e_j` (`rootVec`).

**The rate lift** (`eq:supp-open-rate-lift`).  For a `3 × 3` matrix `B` and a vector `β`,
* `liftC B a = (B_ii + B_jj - B_kk)/4 + sgn σ · B_ij / 2` (the manuscript's `c_{ij,±}`),
* `liftD β a = (r_a · β)/4` (`d_a`),
* `liftK h B β a s = c_a/(2h²) + sgn s · d_a/(2h)` (`k_a^±`).

* `rate_inversion_matrix`, `rate_inversion_shift` — **`eq:supp-open-rate-inversion`**: for
  symmetric `B` and `h ≠ 0`, `h² Σ_a (k_a⁺ + k_a⁻) r_a r_aᵀ = B` and `h Σ_a (k_a⁺ - k_a⁻) r_a = β`.
* `liftC_near`, `liftD_le`, `liftK_cone` — at the flat point all `c_a = 1/4`; if
  `|B_ij - δ_ij| ≤ κ` and `|β_i| ≤ κ` then `|c_a - 1/4| ≤ 5κ/4`, `|d_a| ≤ κ/2`, and for
  `0 < h ≤ 1`, `κ ≤ 1/14`: `1/16 ≤ h² k_a^± ≤ 3/16` (all twelve rates positive and comparable to
  `h⁻²`: the interior cone).

**ADM data of a metric record** (`g : MetricRec`, `g_{μν}`, index `0` = time):
`γ_ij = g_{i+1,j+1}` (`spatialMetric`), `γ⁻¹` inverted at type `Matrix` (`spatialInv`),
`β_i = g_{0,i+1}` (`shiftLow`), `β^i = γ^{ij} β_j` (`shiftUp`), `N² = β_i β^i - g_{00}`
(`lapseSq`; the ADM form `g_{00} = -N² + β_i β^i`), `B = N² γ⁻¹` (`rateMatrix`) and
`ϱ = √det γ` (`volumeDensity`).

* `adm_chart` — continuity at Minkowski: for every `κ > 0` there is `r > 0` with
  `‖g - η‖ < r ⇒ det γ ≠ 0, |B_ij - δ_ij|, |β^i|, |N² - 1|, |det γ - 1|, |γ_ij - δ_ij| < κ`.
* `rateLift_chart` — **the positive rate lift of a small metric** (O3): there is `r > 0` such
  that every symmetric record `g` with `‖g - η‖ < r` and every mesh `0 < h ≤ 1` satisfy: the
  inversion identities with `B = N²γ⁻¹`, `β = shiftUp g` (so the ADM reconstruction returns the
  same `B`, `β`); `|c_a - 1/4| ≤ 5/56`; `1/16 ≤ h² k_a^± ≤ 3/16`; and the pointwise noncollapse
  bounds `1/2 ≤ N² ≤ 2`, `1/2 ≤ det γ ≤ 2`, `1/2 ≤ ϱ ≤ 2`, `ξᵀγξ ≥ |ξ|²/2`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RenewalGeometry.OpenWriterRateLift

open OpenWriterEnergy

noncomputable section

/-! ### Root data and the rate lift -/

/-- The sign `±1` of a Boolean. -/
def sgn (σ : Bool) : ℝ := if σ then 1 else -1

@[simp] theorem sgn_true : sgn true = 1 := rfl
@[simp] theorem sgn_false : sgn false = -1 := rfl

theorem sgn_sq (σ : Bool) : sgn σ ^ 2 = 1 := by cases σ <;> norm_num [sgn]

theorem abs_sgn (σ : Bool) : |sgn σ| = 1 := by cases σ <;> norm_num [sgn]

/-- Index of a `D₃` root `e_i + sgn σ · e_j`: the remaining index `k` of the pair
`(i, j) = (k + 1, k + 2)` and the sign `σ`. -/
abbrev D3Root := Fin 3 × Bool

/-- The `D₃` root vector `r_{k,σ} = e_{k+1} + sgn σ · e_{k+2}` (`eq:supp-open-d3-roots`). -/
def rootVec (a : D3Root) : Fin 3 → ℝ :=
  fun m => (if m = a.1 + 1 then 1 else 0) + sgn a.2 * (if m = a.1 + 2 then 1 else 0)

/-- The six roots are exactly `(1,±1,0), (1,0,±1), (0,1,±1)` up to the overall sign
(`eq:supp-open-d3-roots`). -/
theorem rootVec_values :
    rootVec (2, true) = ![1, 1, 0] ∧ rootVec (2, false) = ![1, -1, 0] ∧
    rootVec (1, true) = ![1, 0, 1] ∧ rootVec (1, false) = ![-1, 0, 1] ∧
    rootVec (0, true) = ![0, 1, 1] ∧ rootVec (0, false) = ![0, 1, -1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext m <;> fin_cases m <;>
    simp [rootVec, sgn]

/-- The coefficient `c_{ij,±} = (B_ii + B_jj - B_kk)/4 ± B_ij/2` of `eq:supp-open-rate-lift`. -/
def liftC (B : Matrix (Fin 3) (Fin 3) ℝ) (a : D3Root) : ℝ :=
  (B (a.1 + 1) (a.1 + 1) + B (a.1 + 2) (a.1 + 2) - B a.1 a.1) / 4 +
    sgn a.2 * B (a.1 + 1) (a.1 + 2) / 2

/-- The drift coefficient `d_a = (r_a · β)/4` of `eq:supp-open-rate-lift`. -/
def liftD (β : Fin 3 → ℝ) (a : D3Root) : ℝ := (∑ m, rootVec a m * β m) / 4

/-- The directed rates `k_a^± = c_a/(2h²) ± d_a/(2h)` of `eq:supp-open-rate-lift`
(`s = true` is the `+` direction `+h r_a`, `s = false` the `-` direction). -/
def liftK (h : ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ) (β : Fin 3 → ℝ) (a : D3Root) (s : Bool) : ℝ :=
  liftC B a / (2 * h ^ 2) + sgn s * liftD β a / (2 * h)

theorem liftK_add (h : ℝ) (hh : h ≠ 0) (B : Matrix (Fin 3) (Fin 3) ℝ) (β : Fin 3 → ℝ)
    (a : D3Root) : h ^ 2 * (liftK h B β a true + liftK h B β a false) = liftC B a := by
  unfold liftK; field_simp; simp [sgn]; ring

theorem liftK_sub (h : ℝ) (hh : h ≠ 0) (B : Matrix (Fin 3) (Fin 3) ℝ) (β : Fin 3 → ℝ)
    (a : D3Root) : h * (liftK h B β a true - liftK h B β a false) = liftD β a := by
  unfold liftK; field_simp; simp [sgn]; ring

/-- `Σ_a c_a r_a r_aᵀ = B` for symmetric `B`. -/
theorem sum_liftC_root_root (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : ∀ i j, B i j = B j i)
    (i j : Fin 3) : ∑ a : D3Root, liftC B a * rootVec a i * rootVec a j = B i j := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool]
  have h01 := hB 0 1; have h02 := hB 0 2; have h12 := hB 1 2
  fin_cases i <;> fin_cases j <;> simp [liftC, rootVec, sgn] <;> linarith [h01, h02, h12]

/-- `Σ_a d_a r_a = β`. -/
theorem sum_liftD_root (β : Fin 3 → ℝ) (i : Fin 3) :
    ∑ a : D3Root, liftD β a * rootVec a i = β i := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool]
  fin_cases i <;> simp [liftD, rootVec, sgn, Fin.sum_univ_three] <;> ring

/-- **`eq:supp-open-rate-inversion`, first identity**: `h² Σ_a (k_a⁺ + k_a⁻) r_a r_aᵀ = B`
(symmetric `B`, `h ≠ 0`). -/
theorem rate_inversion_matrix (h : ℝ) (hh : h ≠ 0) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j, B i j = B j i) (β : Fin 3 → ℝ) (i j : Fin 3) :
    h ^ 2 * ∑ a : D3Root, (liftK h B β a true + liftK h B β a false) * rootVec a i * rootVec a j =
      B i j := by
  rw [Finset.mul_sum]
  rw [← sum_liftC_root_root B hB i j]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← liftK_add h hh B β a]; ring

/-- **`eq:supp-open-rate-inversion`, second identity**: `h Σ_a (k_a⁺ - k_a⁻) r_a = β`. -/
theorem rate_inversion_shift (h : ℝ) (hh : h ≠ 0) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (β : Fin 3 → ℝ) (i : Fin 3) :
    h * ∑ a : D3Root, (liftK h B β a true - liftK h B β a false) * rootVec a i = β i := by
  rw [Finset.mul_sum, ← sum_liftD_root β i]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← liftK_sub h hh B β a]; ring

/-- At the flat point (`B = I`) every coefficient is `c_a = 1/4`. -/
theorem liftC_one (a : D3Root) : liftC 1 a = 1 / 4 := by
  obtain ⟨k, σ⟩ := a
  fin_cases k <;> simp [liftC]

/-- Perturbation of the coefficients: `|B_ij - δ_ij| ≤ κ ⇒ |c_a - 1/4| ≤ 5κ/4`. -/
theorem liftC_near (B : Matrix (Fin 3) (Fin 3) ℝ) {κ : ℝ}
    (hB : ∀ i j, |B i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ κ) (a : D3Root) :
    |liftC B a - 1 / 4| ≤ 5 / 4 * κ := by
  have e : liftC B a - 1 / 4 = liftC (B - 1) a := by
    have h1 := liftC_one a
    unfold liftC at h1 ⊢
    simp only [Matrix.sub_apply] at h1 ⊢
    linarith
  rw [e]
  unfold liftC
  simp only [Matrix.sub_apply]
  have h1 := hB (a.1 + 1) (a.1 + 1)
  have h2 := hB (a.1 + 2) (a.1 + 2)
  have h3 := hB a.1 a.1
  have h4 := hB (a.1 + 1) (a.1 + 2)
  have hs := abs_sgn a.2
  set x1 := B (a.1 + 1) (a.1 + 1) - (1 : Matrix (Fin 3) (Fin 3) ℝ) (a.1 + 1) (a.1 + 1)
  set x2 := B (a.1 + 2) (a.1 + 2) - (1 : Matrix (Fin 3) (Fin 3) ℝ) (a.1 + 2) (a.1 + 2)
  set x3 := B a.1 a.1 - (1 : Matrix (Fin 3) (Fin 3) ℝ) a.1 a.1
  set x4 := B (a.1 + 1) (a.1 + 2) - (1 : Matrix (Fin 3) (Fin 3) ℝ) (a.1 + 1) (a.1 + 2)
  have hmul : |sgn a.2 * x4| ≤ κ := by rw [abs_mul, hs, one_mul]; exact h4
  rw [abs_le] at h1 h2 h3 hmul ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, hmul.1, hmul.2]

/-- `|β_i| ≤ κ ⇒ |d_a| ≤ κ/2`. -/
theorem liftD_le (β : Fin 3 → ℝ) {κ : ℝ} (hβ : ∀ i, |β i| ≤ κ) (a : D3Root) :
    |liftD β a| ≤ κ / 2 := by
  obtain ⟨k, σ⟩ := a
  have h0 := hβ 0; have h1 := hβ 1; have h2 := hβ 2
  rw [abs_le] at h0 h1 h2
  rw [abs_le]
  fin_cases k <;> cases σ <;> simp [liftD, rootVec, sgn, Fin.sum_univ_three] <;> norm_num <;>
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-- **The interior cone**: for `0 < h ≤ 1`, `κ ≤ 1/14`, `|B_ij - δ_ij| ≤ κ`, `|β_i| ≤ κ`, all
twelve directed rates satisfy `1/16 ≤ h² k_a^± ≤ 3/16` (positive and comparable to `h⁻²`). -/
theorem liftK_cone (B : Matrix (Fin 3) (Fin 3) ℝ) (β : Fin 3 → ℝ) {κ h : ℝ} (hκ : κ ≤ 1 / 14)
    (hB : ∀ i j, |B i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ κ) (hβ : ∀ i, |β i| ≤ κ)
    (hh : 0 < h) (hh1 : h ≤ 1) (a : D3Root) (s : Bool) :
    1 / 16 ≤ h ^ 2 * liftK h B β a s ∧ h ^ 2 * liftK h B β a s ≤ 3 / 16 := by
  have hc := liftC_near B hB a
  have hd := liftD_le β hβ a
  have e : h ^ 2 * liftK h B β a s = liftC B a / 2 + h * (sgn s * liftD β a) / 2 := by
    unfold liftK; field_simp
  rw [e]
  have hsd : |sgn s * liftD β a| ≤ κ / 2 := by rw [abs_mul, abs_sgn, one_mul]; exact hd
  have hhsd : |h * (sgn s * liftD β a)| ≤ κ / 2 := by
    rw [abs_mul, abs_of_pos hh]
    calc h * |sgn s * liftD β a| ≤ 1 * |sgn s * liftD β a| :=
          mul_le_mul_of_nonneg_right hh1 (abs_nonneg _)
      _ ≤ κ / 2 := by rw [one_mul]; exact hsd
  have hκ0 : 0 ≤ κ := le_trans (abs_nonneg _) (hβ 0)
  rw [abs_le] at hc hhsd
  constructor <;> nlinarith [hc.1, hc.2, hhsd.1, hhsd.2]

/-! ### ADM data of a metric record -/

/-- The spatial metric `γ_ij = g_{i+1, j+1}`. -/
def spatialMetric (g : MetricRec) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => g i.succ j.succ

/-- Its inverse `γ^{ij}`, taken at type `Matrix`. -/
def spatialInv (g : MetricRec) : Matrix (Fin 3) (Fin 3) ℝ := (spatialMetric g)⁻¹

/-- The lower shift `β_i = g_{0,i+1}`. -/
def shiftLow (g : MetricRec) : Fin 3 → ℝ := fun i => g 0 i.succ

/-- The upper shift `β^i = γ^{ij} β_j`. -/
def shiftUp (g : MetricRec) : Fin 3 → ℝ := (spatialInv g).mulVec (shiftLow g)

/-- The squared lapse `N² = β_i β^i - g_{00}` (ADM form `g_{00} = -N² + β_i β^i`). -/
def lapseSq (g : MetricRec) : ℝ := shiftLow g ⬝ᵥ shiftUp g - g 0 0

/-- The rate matrix `B = N² γ⁻¹` of `eq:supp-open-rate-lift`. -/
def rateMatrix (g : MetricRec) : Matrix (Fin 3) (Fin 3) ℝ := lapseSq g • spatialInv g

/-- The volume density `ϱ = √det γ`. -/
def volumeDensity (g : MetricRec) : ℝ := Real.sqrt (spatialMetric g).det

theorem spatialMetric_minkowski : spatialMetric minkowski = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [spatialMetric, minkowski, Fin.succ_ne_zero]
  · simp [spatialMetric, minkowski, h, Matrix.one_apply_ne h]

theorem spatialInv_minkowski : spatialInv minkowski = 1 := by
  simp [spatialInv, spatialMetric_minkowski]

theorem shiftLow_minkowski : shiftLow minkowski = 0 := by
  funext i; simp [shiftLow, minkowski, (Fin.succ_ne_zero i).symm]

theorem shiftUp_minkowski : shiftUp minkowski = 0 := by
  simp [shiftUp, shiftLow_minkowski]

theorem lapseSq_minkowski : lapseSq minkowski = 1 := by
  simp [lapseSq, shiftLow_minkowski, minkowski]

theorem rateMatrix_minkowski : rateMatrix minkowski = 1 := by
  simp [rateMatrix, lapseSq_minkowski, spatialInv_minkowski]

theorem spatialMetric_symm {g : MetricRec} (hg : ∀ μ ν, g μ ν = g ν μ) (i j : Fin 3) :
    spatialMetric g i j = spatialMetric g j i := by
  simp [spatialMetric, hg]

theorem spatialInv_symm {g : MetricRec} (hg : ∀ μ ν, g μ ν = g ν μ) (i j : Fin 3) :
    spatialInv g i j = spatialInv g j i := by
  have hT : Matrix.transpose (spatialMetric g) = spatialMetric g := by
    ext i j; simp [Matrix.transpose_apply, spatialMetric_symm hg]
  have := congrFun (congrFun (Matrix.transpose_nonsing_inv (spatialMetric g)) j) i
  rw [hT] at this
  simpa [spatialInv, Matrix.transpose_apply] using this

theorem rateMatrix_symm {g : MetricRec} (hg : ∀ μ ν, g μ ν = g ν μ) (i j : Fin 3) :
    rateMatrix g i j = rateMatrix g j i := by
  simp [rateMatrix, spatialInv_symm hg i j]

/-! ### Continuity at Minkowski -/

theorem continuous_spatialMetric : Continuous spatialMetric := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [spatialMetric, Matrix.of_apply]
  exact (continuous_apply j.succ).comp (continuous_apply i.succ)

theorem continuousAt_spatialInv_entry (i j : Fin 3) :
    ContinuousAt (fun g => spatialInv g i j) minkowski := by
  have e : (fun g => spatialInv g i j) =
      fun g => ((spatialMetric g).det)⁻¹ * (spatialMetric g).adjugate i j := by
    funext g
    rw [spatialInv, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  have hdet : Continuous fun g => (spatialMetric g).det :=
    continuous_spatialMetric.matrix_det
  have hadj : Continuous fun g => (spatialMetric g).adjugate i j :=
    (continuous_spatialMetric.matrix_adjugate.matrix_elem i j)
  refine (hdet.continuousAt.inv₀ ?_).mul hadj.continuousAt
  rw [spatialMetric_minkowski, Matrix.det_one]; norm_num

theorem continuousAt_shiftUp (i : Fin 3) : ContinuousAt (fun g => shiftUp g i) minkowski := by
  simp only [shiftUp, Matrix.mulVec, dotProduct]
  refine tendsto_finsetSum _ fun j _ => (continuousAt_spatialInv_entry i j).mul ?_
  simp only [shiftLow]
  exact ((continuous_apply j.succ).comp (continuous_apply 0)).continuousAt

theorem continuousAt_lapseSq : ContinuousAt lapseSq minkowski := by
  unfold lapseSq
  refine ContinuousAt.sub ?_ ((continuous_apply 0).comp (continuous_apply 0)).continuousAt
  simp only [dotProduct]
  refine tendsto_finsetSum _ fun j _ => ContinuousAt.mul ?_ (continuousAt_shiftUp j)
  simp only [shiftLow]
  exact ((continuous_apply j.succ).comp (continuous_apply 0)).continuousAt

theorem continuousAt_rateMatrix_entry (i j : Fin 3) :
    ContinuousAt (fun g => rateMatrix g i j) minkowski := by
  simp only [rateMatrix, Matrix.smul_apply, smul_eq_mul]
  exact continuousAt_lapseSq.mul (continuousAt_spatialInv_entry i j)

/-- Eventual closeness of a function continuous at Minkowski to its value there. -/
theorem eventually_near {f : MetricRec → ℝ} (hf : ContinuousAt f minkowski) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ g in 𝓝 minkowski, |f g - f minkowski| < κ := by
  have := (Metric.tendsto_nhds.mp hf.tendsto) κ hκ
  filter_upwards [this] with g hg
  rwa [Real.dist_eq] at hg

/-- **The ADM chart around Minkowski**: for every `κ > 0` there is `r > 0` such that
`‖g - η‖ < r` implies `det γ ≠ 0`, `|B_ij - δ_ij| < κ` (`B = N²γ⁻¹`), `|β^i| < κ`,
`|N² - 1| < κ`, `|det γ - 1| < κ` and `|γ_ij - δ_ij| < κ`. -/
theorem adm_chart {κ : ℝ} (hκ : 0 < κ) : ∃ r > 0, ∀ g : MetricRec, ‖g - minkowski‖ < r →
    (spatialMetric g).det ≠ 0 ∧
    (∀ i j, |rateMatrix g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < κ) ∧
    (∀ i, |shiftUp g i| < κ) ∧ |lapseSq g - 1| < κ ∧ |(spatialMetric g).det - 1| < κ ∧
    (∀ i j, |spatialMetric g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < κ) := by
  have hB : ∀ᶠ g in 𝓝 minkowski, ∀ i j,
      |rateMatrix g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < κ := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have := eventually_near (continuousAt_rateMatrix_entry i j) hκ
    simpa [rateMatrix_minkowski] using this
  have hβ : ∀ᶠ g in 𝓝 minkowski, ∀ i, |shiftUp g i| < κ := by
    refine eventually_all.2 fun i => ?_
    have := eventually_near (continuousAt_shiftUp i) hκ
    simpa [shiftUp_minkowski] using this
  have hN : ∀ᶠ g in 𝓝 minkowski, |lapseSq g - 1| < κ := by
    have := eventually_near continuousAt_lapseSq hκ
    simpa [lapseSq_minkowski] using this
  have hdetc : ContinuousAt (fun g => (spatialMetric g).det) minkowski :=
    continuous_spatialMetric.matrix_det.continuousAt
  have hD : ∀ᶠ g in 𝓝 minkowski, |(spatialMetric g).det - 1| < κ := by
    have := eventually_near hdetc hκ
    simpa [spatialMetric_minkowski] using this
  have hD0 : ∀ᶠ g in 𝓝 minkowski, (spatialMetric g).det ≠ 0 :=
    hdetc.eventually_ne (by rw [spatialMetric_minkowski, Matrix.det_one]; norm_num)
  have hG : ∀ᶠ g in 𝓝 minkowski, ∀ i j,
      |spatialMetric g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < κ := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have hc : ContinuousAt (fun g => spatialMetric g i j) minkowski :=
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_spatialMetric)).continuousAt
    have := eventually_near hc hκ
    simpa [spatialMetric_minkowski] using this
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hD0.and (hB.and (hβ.and (hN.and (hD.and hG)))))
  refine ⟨r, hr, fun g hg => ?_⟩
  have := hball (y := g) (by rwa [dist_eq_norm])
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩

/-- Uniform ellipticity of a near-identity symmetric `3 × 3` matrix:
`|γ_ij - δ_ij| ≤ 1/6 ⇒ ξᵀγξ ≥ |ξ|²/2`. -/
theorem quadForm_ge_of_near (γ : Matrix (Fin 3) (Fin 3) ℝ)
    (hγ : ∀ i j, |γ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 / 6) (ξ : Fin 3 → ℝ) :
    (∑ i, ξ i ^ 2) / 2 ≤ ∑ i, ∑ j, ξ i * γ i j * ξ j := by
  have hdev : ∀ i j, |ξ i * (γ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) * ξ j| ≤
      1 / 6 * (|ξ i| * |ξ j|) := by
    intro i j
    rw [abs_mul, abs_mul]
    have := hγ i j
    have h1 := abs_nonneg (ξ i); have h2 := abs_nonneg (ξ j)
    nlinarith [mul_nonneg h1 h2]
  have e : ∑ i, ∑ j, ξ i * γ i j * ξ j = ∑ i, ξ i ^ 2 +
      ∑ i, ∑ j, ξ i * (γ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) * ξ j := by
    simp only [Fin.sum_univ_three, Matrix.one_apply]
    simp
    ring
  rw [e]
  have hsum : |∑ i, ∑ j, ξ i * (γ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) * ξ j| ≤
      1 / 6 * (∑ i, |ξ i|) ^ 2 := by
    calc |∑ i, ∑ j, ξ i * (γ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) * ξ j|
        ≤ ∑ i, ∑ j, |ξ i * (γ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) * ξ j| :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j, 1 / 6 * (|ξ i| * |ξ j|) := sum_le_sum fun i _ => sum_le_sum fun j _ => hdev i j
      _ = 1 / 6 * (∑ i, |ξ i|) ^ 2 := by
          simp only [Fin.sum_univ_three]; ring
  have hcs : (∑ i, |ξ i|) ^ 2 ≤ 3 * ∑ i, ξ i ^ 2 := by
    simp only [Fin.sum_univ_three]
    have a0 := sq_abs (ξ 0); have a1 := sq_abs (ξ 1); have a2 := sq_abs (ξ 2)
    nlinarith [sq_nonneg (|ξ 0| - |ξ 1|), sq_nonneg (|ξ 0| - |ξ 2|), sq_nonneg (|ξ 1| - |ξ 2|)]
  have := (abs_le.mp hsum).1
  nlinarith

/-- **The positive rate lift of a small metric** (clause (O3) of `thm:main-open-3plus1`,
pointwise).  There is `r > 0` such that for every symmetric record `g` with `‖g - η‖ < r` and
every mesh `0 < h ≤ 1`, with `B = N² γ⁻¹` (`rateMatrix`) and `β = shiftUp g`:
* (inversion, `eq:supp-open-rate-inversion`) `h² Σ_a (k_a⁺ + k_a⁻) r_a r_aᵀ = B` and
  `h Σ_a (k_a⁺ - k_a⁻) r_a = β`, so the ADM reconstruction returns the same data;
* (interior cone) `|c_a - 1/4| ≤ 5/56` and `1/16 ≤ h² k_a^± ≤ 3/16` for all twelve rates;
* (noncollapse) `1/2 ≤ N² ≤ 2`, `1/2 ≤ det γ ≤ 2`, `1/2 ≤ ϱ ≤ 2`, `ξᵀγξ ≥ |ξ|²/2`. -/
theorem rateLift_chart : ∃ r > 0, ∀ g : MetricRec, (∀ μ ν, g μ ν = g ν μ) →
    ‖g - minkowski‖ < r → ∀ h : ℝ, 0 < h → h ≤ 1 →
      (∀ i j, h ^ 2 * ∑ a : D3Root, (liftK h (rateMatrix g) (shiftUp g) a true +
          liftK h (rateMatrix g) (shiftUp g) a false) * rootVec a i * rootVec a j =
          rateMatrix g i j) ∧
      (∀ i, h * ∑ a : D3Root, (liftK h (rateMatrix g) (shiftUp g) a true -
          liftK h (rateMatrix g) (shiftUp g) a false) * rootVec a i = shiftUp g i) ∧
      (∀ a, |liftC (rateMatrix g) a - 1 / 4| ≤ 5 / 56) ∧
      (∀ a s, 1 / 16 ≤ h ^ 2 * liftK h (rateMatrix g) (shiftUp g) a s ∧
        h ^ 2 * liftK h (rateMatrix g) (shiftUp g) a s ≤ 3 / 16) ∧
      (1 / 2 ≤ lapseSq g ∧ lapseSq g ≤ 2) ∧
      (1 / 2 ≤ (spatialMetric g).det ∧ (spatialMetric g).det ≤ 2) ∧
      (1 / 2 ≤ volumeDensity g ∧ volumeDensity g ≤ 2) ∧
      ∀ ξ : Fin 3 → ℝ, (∑ i, ξ i ^ 2) / 2 ≤ ∑ i, ∑ j, ξ i * spatialMetric g i j * ξ j := by
  obtain ⟨r, hr, hc⟩ := adm_chart (κ := 1 / 14) (by norm_num)
  refine ⟨r, hr, fun g hg hgr h hh hh1 => ?_⟩
  obtain ⟨-, hB, hβ, hN, hD, hG⟩ := hc g hgr
  have hB' : ∀ i j, |rateMatrix g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 / 14 :=
    fun i j => (hB i j).le
  have hβ' : ∀ i, |shiftUp g i| ≤ 1 / 14 := fun i => (hβ i).le
  rw [abs_lt] at hN hD
  have hD1 : 1 / 2 ≤ (spatialMetric g).det := by linarith
  have hD2 : (spatialMetric g).det ≤ 2 := by linarith
  refine ⟨fun i j => rate_inversion_matrix h hh.ne' _ (rateMatrix_symm hg) _ i j,
    fun i => rate_inversion_shift h hh.ne' _ _ i,
    fun a => (liftC_near _ hB' a).trans (by norm_num),
    fun a s => liftK_cone _ _ (by norm_num) hB' hβ' hh hh1 a s,
    ⟨by linarith, by linarith⟩, ⟨hD1, hD2⟩, ⟨?_, ?_⟩,
    quadForm_ge_of_near _ fun i j => (hG i j).le.trans (by norm_num)⟩
  · unfold volumeDensity
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  · unfold volumeDensity
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)

/-- Non-vacuity: the flat metric satisfies all hypotheses of `rateLift_chart`, and its rate lift
has `c_a = 1/4`, `k_a^± = 1/(8h²)`. -/
example : (∀ μ ν, minkowski μ ν = minkowski ν μ) ∧ rateMatrix minkowski = 1 ∧
    shiftUp minkowski = 0 ∧ ∀ (h : ℝ) (a : D3Root) (s : Bool),
      liftK h (rateMatrix minkowski) (shiftUp minkowski) a s = 1 / (8 * h ^ 2) := by
  refine ⟨fun μ ν => ?_, rateMatrix_minkowski, shiftUp_minkowski, fun h a s => ?_⟩
  · unfold minkowski; by_cases h : μ = ν
    · subst h; rfl
    · simp [h, Ne.symm h]
  · rw [rateMatrix_minkowski, shiftUp_minkowski, liftK, liftC_one]
    simp [liftD]
    ring

end

end RenewalGeometry.OpenWriterRateLift
