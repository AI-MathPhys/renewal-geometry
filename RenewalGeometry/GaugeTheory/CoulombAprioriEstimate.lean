/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.LogarithmicCurvatureSplit

/-!
# The critical discrete Coulomb a priori estimate
  (first display of the proof of `thm:native-discrete-Coulomb`, eq. `eq:native-Coulomb-first-exit`
  of `thm:finite-Coulomb-normalization`; Einstein–SM action closure)

Setting.  The periodic grid `(ℤ/n)^ι`, `card ι = 4` (linearly ordered directions), mesh `h > 0`,
side `L = n h`; links `e^{hA_μ(x)}` in a complete normed `ℝ`-algebra `𝔸` with `‖1‖ = 1`, and the
Lie-algebra values read in a real inner product space `E` through a continuous linear map
`T : 𝔸 →L[ℝ] E` with `‖X‖ ≤ c ‖T X‖` (for `𝔲(N)`: `T` = the Frobenius identification,
`c = 1`).  Norms (all computed through `T`):
* `oneL4 h T A = Σ_μ ‖T A_μ‖_{4,h}` (`‖A‖_{4,h}`), `oneL2 h T A = (Σ_μ ‖T A_μ‖²_{2,h})^{1/2}`;
* `packetL2 h T F = (Σ_{μ<ν} ‖T F_{μν}‖²_{2,h})^{1/2}` and `curvL2 h T A = packetL2 (F^h(A))`
  (the literal curvature packet norm `‖𝔽_h‖_{2,h}`);
* `‖A‖_{1,h}² = Σ_ν ‖T A_ν‖²_{2,h} + Σ_{μ,ν} ‖D^+_μ T A_ν‖²_{2,h}` (`periodicHodgeH1NormSq`).

Main result (`coulomb_apriori`): if `δ_h(T A) = 0` and the scaled chart condition
`h |W_{μν}(A)(x)| ≤ 1/8` holds everywhere, then with `K = 21 ‖T‖ c²`
* `‖D^+ T A‖_{2,h} ≤ ‖𝔽_h(A)‖_{2,h} + 192 K ‖A‖²_{4,h}`,
* `‖A‖_{4,h} ≤ 12 ‖𝔽_h(A)‖_{2,h} + 12 · 192 K ‖A‖²_{4,h} + (8/L) ‖A‖_{2,h}`,
* `‖A‖_{1,h} ≤ ‖A‖_{2,h} + ‖𝔽_h(A)‖_{2,h} + 192 K ‖A‖²_{4,h}`,

uniformly in `n` and `h` — the Hodge identity (`periodicHodge_identity`), the exact curvature
split with its quadratic envelope (`CurvatureSplit.curvRem_L2_le`) and the uniform grid Sobolev
inequality (`GridSobolev.grid_sobolev_L4`).  This is the estimate
`‖A_h‖_{1,h} ≤ C(‖F_h(A_h)‖_{2,h} + ‖A_h‖²_{4,h} + ‖A_h‖_{2,h})` of the proof of
`thm:native-discrete-Coulomb` and `a ≤ C₀ b + C₁ a²` of `eq:native-Coulomb-first-exit`.
-/

open Finset

namespace RenewalGeometry.CoulombApriori

open GridSobolev CurvatureSplit

noncomputable section

/-- **Minkowski's inequality** in `ℓ²` for nonnegative-index sums. -/
theorem sqrt_sum_add_sq_le {α : Type*} (s : Finset α) (a b : α → ℝ) :
    √(∑ i ∈ s, (a i + b i) ^ 2) ≤ √(∑ i ∈ s, a i ^ 2) + √(∑ i ∈ s, b i ^ 2) := by
  have hA : 0 ≤ ∑ i ∈ s, a i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ ∑ i ∈ s, b i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s a b
  rw [Real.sqrt_le_left (by positivity)]
  have e : ∑ i ∈ s, (a i + b i) ^ 2 = ∑ i ∈ s, a i ^ 2 + 2 * ∑ i ∈ s, a i * b i +
      ∑ i ∈ s, b i ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  nlinarith

/-- `√(Σ_s x_i²) ≤ Σ_s x_i` for nonnegative `x`. -/
theorem sqrt_sum_sq_le_sum {α : Type*} (s : Finset α) (a : α → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    √(∑ i ∈ s, a i ^ 2) ≤ ∑ i ∈ s, a i := by
  rw [Real.sqrt_le_left (sum_nonneg ha)]
  rw [sq (∑ i ∈ s, a i), sum_mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [sq]
  exact single_le_sum (f := fun j => a i * a j) (fun j hj => mul_nonneg (ha i hi) (ha j hj)) hi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {n : ℕ} [NeZero n]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The ordered pairs `μ < ν`. -/
def pairs (ι : Type*) [Fintype ι] [LinearOrder ι] : Finset (ι × ι) :=
  univ.filter fun p => p.1 < p.2

/-- The one-form read through `T`. -/
def bar (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸) : ι → (ι → ZMod n) → E :=
  fun μ x => T (A μ x)

/-- `‖A‖_{4,h} = Σ_μ ‖T A_μ‖_{4,h}`. -/
def oneL4 (h : ℝ) (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸) : ℝ :=
  ∑ μ, gridL4Norm h (bar T A μ)

/-- `‖A‖_{2,h} = (Σ_μ ‖T A_μ‖²_{2,h})^{1/2}`. -/
def oneL2 (h : ℝ) (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸) : ℝ :=
  √(∑ μ, periodicHodgeNormSq ι h (bar T A μ))

/-- `‖F‖_{2,h} = (Σ_{μ<ν} ‖T F_{μν}‖²_{2,h})^{1/2}` for a two-form packet. -/
def packetL2 (h : ℝ) (T : 𝔸 →L[ℝ] E) (F : ι → ι → (ι → ZMod n) → 𝔸) : ℝ :=
  √(∑ p ∈ pairs ι, gridL2Norm h (fun x => T (F p.1 p.2 x)) ^ 2)

/-- The literal curvature packet norm `‖𝔽_h(A)‖_{2,h}`. -/
def curvL2 (h : ℝ) (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸) : ℝ :=
  packetL2 h T (curvature h A)

/-- `‖D^+ A‖_{2,h} = (Σ_{μ,ν} ‖D^+_μ T A_ν‖²_{2,h})^{1/2}`. -/
def gradL2 (h : ℝ) (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸) : ℝ :=
  √(∑ μ, ∑ ν, periodicHodgeNormSq ι h (periodicHodgeFwd h gridStep μ (bar T A ν)))

/-- `‖A‖_{1,h} = (‖A‖²_{2,h} + ‖D^+A‖²_{2,h})^{1/2}`. -/
def oneH1 (h : ℝ) (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸) : ℝ :=
  √(periodicHodgeH1NormSq h gridStep (bar T A))

theorem oneL4_nonneg {h : ℝ} (hh : 0 ≤ h) (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸) :
    0 ≤ oneL4 h T A :=
  sum_nonneg fun _ _ => gridL4Norm_nonneg hh _

theorem gridL4_le_oneL4 {h : ℝ} (hh : 0 ≤ h) (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸)
    (μ : ι) : gridL4Norm h (bar T A μ) ≤ oneL4 h T A :=
  single_le_sum (f := fun μ => gridL4Norm h (bar T A μ)) (fun _ _ => gridL4Norm_nonneg hh _)
    (mem_univ μ)

theorem T_extD (T : 𝔸 →L[ℝ] E) (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι) (x : ι → ZMod n) :
    T (extD h A μ ν x) = periodicHodgeExtD h gridStep (bar T A) μ ν x := by
  simp [extD, periodicHodgeExtD, periodicHodgeFwd, gridFwd, bar, map_sub, map_smul]

theorem gridL2Norm_sq' {h : ℝ} (hh : 0 ≤ h) (u : (ι → ZMod n) → E) :
    gridL2Norm h u ^ 2 = periodicHodgeNormSq ι h u :=
  Real.sq_sqrt (periodicHodgeNormSq_nonneg hh u)

/-- The nonlinear packet: `Σ_{μ<ν} ‖T 𝒩_{μν}(A)‖_{2,h} ≤ 16 · 12 K ‖A‖²_{4,h}`. -/
theorem sum_pairs_curvRem_le (hι : Fintype.card ι = 4) (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖) {h : ℝ} (hh : 0 < h) (A : ι → (ι → ZMod n) → 𝔸)
    (hs : ∀ μ ν x, h * slotNorm A μ ν x ≤ 1 / 8) :
    ∑ p ∈ pairs ι, gridL2Norm h (fun x => T (curvRem h A p.1 p.2 x)) ≤
      192 * (21 * ‖T‖ * c ^ 2) * oneL4 h T A ^ 2 := by
  set K := 21 * ‖T‖ * c ^ 2
  have hK : 0 ≤ K := by positivity
  set a := oneL4 h T A
  have ha : 0 ≤ a := oneL4_nonneg hh.le T A
  have hp : ∀ p ∈ pairs ι, gridL2Norm h (fun x => T (curvRem h A p.1 p.2 x)) ≤ 12 * K * a ^ 2 := by
    intro p hpm
    refine (curvRem_L2_le hι T hc0 hc hh A p.1 p.2 (hs p.1 p.2)).trans ?_
    have h1 := gridL4_le_oneL4 hh.le T A p.1
    have h2 := gridL4_le_oneL4 hh.le T A p.2
    have n1 := gridL4Norm_nonneg hh.le (bar T A p.1)
    have n2 := gridL4Norm_nonneg hh.le (bar T A p.2)
    have hpp : p.1 ≠ p.2 := (mem_filter.1 hpm).2.ne
    have hsum : gridL4Norm h (bar T A p.1) + gridL4Norm h (bar T A p.2) ≤ a := by
      have := sum_le_sum_of_subset_of_nonneg (f := fun μ => gridL4Norm h (bar T A μ))
        (subset_univ {p.1, p.2}) (fun _ _ _ => gridL4Norm_nonneg hh.le _)
      rwa [sum_pair hpp] at this
    have : gridL4Norm h (fun x => T (A p.1 x)) ^ 2 + gridL4Norm h (fun x => T (A p.2 x)) ^ 2 ≤
        a ^ 2 := by
      change gridL4Norm h (bar T A p.1) ^ 2 + gridL4Norm h (bar T A p.2) ^ 2 ≤ a ^ 2
      nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  refine (sum_le_sum hp).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hcard : ((pairs ι).card : ℝ) ≤ 16 := by
    have : (pairs ι).card ≤ Fintype.card (ι × ι) := card_le_univ _
    rw [Fintype.card_prod, hι] at this
    exact_mod_cast this
  calc ((pairs ι).card : ℝ) * (12 * K * a ^ 2) ≤ 16 * (12 * K * a ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 192 * K * a ^ 2 := by ring

theorem periodicHodgeNormSq_zero (h : ℝ) :
    periodicHodgeNormSq ι h (0 : (ι → ZMod n) → E) = 0 := by
  simp [periodicHodgeNormSq]

/-- **Hodge identity + exact split** (Coulomb gauge, scaled chart):
`‖D^+ A‖_{2,h} ≤ ‖𝔽_h(A)‖_{2,h} + 192 K ‖A‖²_{4,h}`, `K = 21 ‖T‖ c²`. -/
theorem gradL2_le (hι : Fintype.card ι = 4) (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖) {h : ℝ} (hh : 0 < h) (A : ι → (ι → ZMod n) → 𝔸)
    (hcod : periodicHodgeCodiff h gridStep (bar T A) = 0)
    (hs : ∀ μ ν x, h * slotNorm A μ ν x ≤ 1 / 8) :
    gradL2 h T A ≤ curvL2 h T A + 192 * (21 * ‖T‖ * c ^ 2) * oneL4 h T A ^ 2 := by
  have hH := periodicHodge_identity h gridStep (bar T A)
  rw [hcod, periodicHodgeNormSq_zero, add_zero] at hH
  have hN := sum_pairs_curvRem_le hι T hc0 hc hh A hs
  set f : ι × ι → ℝ := fun p => gridL2Norm h (fun x => T (curvature h A p.1 p.2 x))
  set g : ι × ι → ℝ := fun p => gridL2Norm h (fun x => T (curvRem h A p.1 p.2 x))
  have hext : ∀ p : ι × ι, periodicHodgeNormSq ι h (periodicHodgeExtD h gridStep (bar T A) p.1 p.2)
      ≤ (f p + g p) ^ 2 := by
    intro p
    have e : periodicHodgeExtD h gridStep (bar T A) p.1 p.2 =
        (fun x => T (curvature h A p.1 p.2 x)) - (fun x => T (curvRem h A p.1 p.2 x)) := by
      funext x
      rw [← T_extD, Pi.sub_apply, ← map_sub, curvRem, sub_sub_cancel]
    rw [e, ← gridL2Norm_sq' hh.le]
    exact pow_le_pow_left₀ (gridL2Norm_nonneg _ _) (gridL2Norm_sub_le hh _ _) 2
  unfold gradL2
  rw [hH]
  have hD : periodicHodgeExtDNormSq h gridStep (bar T A) ≤ ∑ p ∈ pairs ι, (f p + g p) ^ 2 :=
    sum_le_sum fun p _ => hext p
  calc √(periodicHodgeExtDNormSq h gridStep (bar T A)) ≤ √(∑ p ∈ pairs ι, (f p + g p) ^ 2) :=
        Real.sqrt_le_sqrt hD
    _ ≤ √(∑ p ∈ pairs ι, f p ^ 2) + √(∑ p ∈ pairs ι, g p ^ 2) := sqrt_sum_add_sq_le _ _ _
    _ ≤ curvL2 h T A + ∑ p ∈ pairs ι, g p := by
        gcongr
        · exact le_rfl
        · exact sqrt_sum_sq_le_sum _ _ fun p _ => gridL2Norm_nonneg _ _
    _ ≤ _ := by gcongr

/-- **Uniform grid Sobolev for one-forms**: `‖A‖_{4,h} ≤ 12 ‖D^+A‖_{2,h} + (8/L) ‖A‖_{2,h}`,
`L = n h`. -/
theorem oneL4_le (hι : Fintype.card ι = 4) (T : 𝔸 →L[ℝ] E) {h : ℝ} (hh : 0 < h)
    (A : ι → (ι → ZMod n) → 𝔸) :
    oneL4 h T A ≤ 12 * gradL2 h T A + 8 / (n * h) * oneL2 h T A := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hS : ∀ ν, gridL4Norm h (bar T A ν) ≤ 3 * ∑ μ, gridL2Norm h (gridFwd h μ (bar T A ν)) +
      4 / (n * h) * gridL2Norm h (bar T A ν) := fun ν => grid_sobolev_L4 hh hι _
  have h1 : ∀ ν, ∑ μ, gridL2Norm h (gridFwd h μ (bar T A ν)) ≤
      2 * √(∑ μ, periodicHodgeNormSq ι h (periodicHodgeFwd h gridStep μ (bar T A ν))) := by
    intro ν
    have := sum_le_two_mul_sqrt_sum_sq hι (fun μ => gridL2Norm h (gridFwd h μ (bar T A ν)))
    simp only [gridL2Norm_sq' hh.le] at this
    exact this
  have h2 : ∑ ν, √(∑ μ, periodicHodgeNormSq ι h (periodicHodgeFwd h gridStep μ (bar T A ν))) ≤
      2 * gradL2 h T A := by
    have := sum_le_two_mul_sqrt_sum_sq hι
      (fun ν => √(∑ μ, periodicHodgeNormSq ι h (periodicHodgeFwd h gridStep μ (bar T A ν))))
    refine this.trans (le_of_eq ?_)
    unfold gradL2
    congr 2
    rw [sum_comm]
    refine sum_congr rfl fun ν _ => Real.sq_sqrt ?_
    exact sum_nonneg fun _ _ => periodicHodgeNormSq_nonneg hh.le _
  have h3 : ∑ ν, gridL2Norm h (bar T A ν) ≤ 2 * oneL2 h T A := by
    have := sum_le_two_mul_sqrt_sum_sq hι (fun ν => gridL2Norm h (bar T A ν))
    simpa only [gridL2Norm_sq' hh.le, oneL2] using this
  unfold oneL4
  calc ∑ ν, gridL4Norm h (bar T A ν)
      ≤ ∑ ν, (3 * ∑ μ, gridL2Norm h (gridFwd h μ (bar T A ν)) +
          4 / (n * h) * gridL2Norm h (bar T A ν)) := sum_le_sum fun ν _ => hS ν
    _ = 3 * ∑ ν, ∑ μ, gridL2Norm h (gridFwd h μ (bar T A ν)) +
          4 / (n * h) * ∑ ν, gridL2Norm h (bar T A ν) := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ 3 * ∑ ν, 2 * √(∑ μ, periodicHodgeNormSq ι h (periodicHodgeFwd h gridStep μ
          (bar T A ν))) + 4 / (n * h) * (2 * oneL2 h T A) := by
        gcongr with ν
        exact h1 ν
    _ ≤ 3 * (2 * (2 * gradL2 h T A)) + 4 / (n * h) * (2 * oneL2 h T A) := by
        rw [← mul_sum]; gcongr
    _ = 12 * gradL2 h T A + 8 / (n * h) * oneL2 h T A := by ring

theorem oneH1_le {h : ℝ} (hh : 0 < h) (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸) :
    oneH1 h T A ≤ oneL2 h T A + gradL2 h T A := by
  unfold oneH1 oneL2 gradL2 periodicHodgeH1NormSq
  set S₁ := ∑ ν, periodicHodgeNormSq ι h (bar T A ν)
  set S₂ := ∑ μ, ∑ ν, periodicHodgeNormSq ι h (periodicHodgeFwd h gridStep μ (bar T A ν))
  have h1 : 0 ≤ S₁ := sum_nonneg fun _ _ => periodicHodgeNormSq_nonneg hh.le _
  have h2 : 0 ≤ S₂ := sum_nonneg fun _ _ => sum_nonneg fun _ _ => periodicHodgeNormSq_nonneg hh.le _
  have hx := Real.sq_sqrt h1
  have hy := Real.sq_sqrt h2
  have hxy : 0 ≤ √S₁ * √S₂ := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  calc S₁ + S₂ = √S₁ ^ 2 + √S₂ ^ 2 := by rw [hx, hy]
    _ ≤ √S₁ ^ 2 + √S₂ ^ 2 + 2 * (√S₁ * √S₂) := by linarith
    _ = (√S₁ + √S₂) ^ 2 := by ring

/-- **The critical discrete Coulomb a priori estimate** (proof of `thm:native-discrete-Coulomb`,
eq. `eq:native-Coulomb-first-exit`): if `δ_h A = 0` and the scaled chart condition holds, then,
with `K = 21 ‖T‖ c²` and `L = n h`, uniformly in `n` and `h`,
`‖A‖_{4,h} ≤ 12 ‖𝔽_h(A)‖_{2,h} + (8/L) ‖A‖_{2,h} + 12·192 K ‖A‖²_{4,h}` and
`‖A‖_{1,h} ≤ ‖A‖_{2,h} + ‖𝔽_h(A)‖_{2,h} + 192 K ‖A‖²_{4,h}`. -/
theorem coulomb_apriori (hι : Fintype.card ι = 4) (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖) {h : ℝ} (hh : 0 < h) (A : ι → (ι → ZMod n) → 𝔸)
    (hcod : periodicHodgeCodiff h gridStep (bar T A) = 0)
    (hs : ∀ μ ν x, h * slotNorm A μ ν x ≤ 1 / 8) :
    oneL4 h T A ≤ 12 * curvL2 h T A + 8 / (n * h) * oneL2 h T A +
        12 * 192 * (21 * ‖T‖ * c ^ 2) * oneL4 h T A ^ 2 ∧
      oneH1 h T A ≤ oneL2 h T A + curvL2 h T A + 192 * (21 * ‖T‖ * c ^ 2) * oneL4 h T A ^ 2 := by
  have hg := gradL2_le hι T hc0 hc hh A hcod hs
  have h4 := oneL4_le hι T hh A
  have h1 := oneH1_le hh T A
  constructor <;> nlinarith

end

end RenewalGeometry.CoulombApriori
