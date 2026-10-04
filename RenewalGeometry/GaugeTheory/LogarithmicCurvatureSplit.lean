/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.SeriesLogChart
import RenewalGeometry.DiscreteAnalysis.GridSobolevInequality
import RenewalGeometry.DiscreteAnalysis.PeriodicForwardDifferenceHodgeIdentityExact

/-!
# The exact split of the logarithmic plaquette curvature and its quadratic envelope
  (`eq:native-plaquettes`, `eq:native-YM-split`, `eq:native-YM-envelope` (first line);
  Einstein–SM action closure)

Setting.  The periodic grid `(ℤ/n)^ι` (unit steps `gridStep`, mesh `h > 0`); the link variables
are `U_μ(x) = e^{h A_μ(x)}` in a complete normed `ℝ`-algebra `𝔸` with `‖1‖ = 1` (for the gauge
group `U(N)` or `SU(3) × SU(2)`: complex matrices with the operator norm, or block matrices);
the logarithm is the analytic branch near the identity `SeriesLogChart.logChart`.

* `plaquette h A μ ν x = U_μ(x) U_ν(x + h e_μ) U_μ(x + h e_ν)⁻¹ U_ν(x)⁻¹` and
  `curvature h A μ ν x = h⁻² log(plaquette)` — the literal logarithmic plaquette `F^h_{μν}` of
  `eq:native-plaquettes`;
* `curvRem = F^h - d_h^+ A` — the nonlinear part `𝒩_h` of `eq:native-YM-split`, where
  `(d_h^+A)_{μν} = D^+_μ A_ν - D^+_ν A_μ` (`periodicHodgeExtD`);
* `norm_curvRem_le` (**first line of `eq:native-YM-envelope`**): on the scaled chart
  `h |W_{μν}(A)(x)| ≤ 1/8`, with `|W_{μν}(A)(x)| = ‖A_μ(x)‖ + ‖A_ν(x+e_μ)‖ + ‖A_μ(x+e_ν)‖ +
  ‖A_ν(x)‖` the four slots, `‖𝒩_{μν}(A)(x)‖ ≤ 21 |W_{μν}(A)(x)|²` and
  `‖plaquette - 1‖ ≤ 4 h |W|`;
* `norm_map_curvRem_le`, `curvRem_L2_le`: the same estimate read through any linear
  identification `T : 𝔸 →L[ℝ] E` of the Lie-algebra values with an inner product space
  (`‖X‖ ≤ c ‖T X‖`), and its `L²_h` consequence
  `‖T 𝒩_{μν}(A)‖_{2,h} ≤ 12·21 ‖T‖ c² (‖T A_μ‖²_{4,h} + ‖T A_ν‖²_{4,h})` in four dimensions,
  uniformly in `n` and `h`.
-/

open NormedSpace Finset

namespace RenewalGeometry.CurvatureSplit

open SeriesLogChart GridSobolev

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The plaquette `U_μ(x) U_ν(x + e_μ) U_μ(x + e_ν)⁻¹ U_ν(x)⁻¹` of the links `U = e^{hA}`
(`eq:native-plaquettes`). -/
def plaquette (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι) (x : ι → ZMod n) : 𝔸 :=
  exp (h • A μ x) * exp (h • A ν (x + gridStep μ)) * exp (-(h • A μ (x + gridStep ν))) *
    exp (-(h • A ν x))

/-- The logarithmic plaquette curvature `F^h_{μν}(x) = h⁻² log(plaquette)`
(`eq:native-plaquettes`). -/
def curvature (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι) (x : ι → ZMod n) : 𝔸 :=
  (h ^ 2)⁻¹ • logChart (plaquette h A μ ν x)

/-- The slot size `|W_{μν}(A)(x)|` (sum of the norms of the four slots). -/
def slotNorm (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι) (x : ι → ZMod n) : ℝ :=
  ‖A μ x‖ + ‖A ν (x + gridStep μ)‖ + ‖A μ (x + gridStep ν)‖ + ‖A ν x‖

/-- The forward exterior derivative `(d_h^+ A)_{μν} = D^+_μ A_ν - D^+_ν A_μ` of an `𝔸`-valued
one-form (the same formula as `periodicHodgeExtD`). -/
def extD (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι) (x : ι → ZMod n) : 𝔸 :=
  gridFwd h μ (A ν) x - gridFwd h ν (A μ) x

/-- The nonlinear part `𝒩_{μν}(A) = F^h_{μν}(A) - (D^+_μ A_ν - D^+_ν A_μ)` of
`eq:native-YM-split`. -/
def curvRem (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι) (x : ι → ZMod n) : 𝔸 :=
  curvature h A μ ν x - extD h A μ ν x

/-- **`eq:native-YM-split`** (definitional form): `F^h = d_h^+ A + 𝒩_h(A)`. -/
theorem curvature_eq_split (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι) (x : ι → ZMod n) :
    curvature h A μ ν x = extD h A μ ν x + curvRem h A μ ν x := by
  rw [curvRem]; abel

theorem extD_eq (h : ℝ) (hh : h ≠ 0) (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι) (x : ι → ZMod n) :
    extD h A μ ν x = (h ^ 2)⁻¹ • (h • A μ x + h • A ν (x + gridStep μ) +
      -(h • A μ (x + gridStep ν)) + -(h • A ν x)) := by
  simp only [extD, gridFwd]
  rw [show h • A μ x + h • A ν (x + gridStep μ) + -(h • A μ (x + gridStep ν)) + -(h • A ν x) =
    h • (A ν (x + gridStep μ) - A ν x - (A μ (x + gridStep ν) - A μ x)) by
      simp only [smul_sub]; abel]
  rw [smul_smul, show (h ^ 2)⁻¹ * h = h⁻¹ by field_simp]
  simp only [smul_sub]

/-- **Quadratic envelope of the plaquette** (`eq:native-YM-envelope`, first line, pointwise):
on the scaled chart `h |W| ≤ 1/8`, `‖𝒩_{μν}(A)(x)‖ ≤ 21 |W_{μν}(A)(x)|²`, and the plaquette
is in the logarithm chart with `‖plaquette - 1‖ ≤ 4 h |W|`. -/
theorem norm_curvRem_le {h : ℝ} (hh : 0 < h) (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι)
    (x : ι → ZMod n) (hs : h * slotNorm A μ ν x ≤ 1 / 8) :
    ‖curvRem h A μ ν x‖ ≤ 21 * slotNorm A μ ν x ^ 2 ∧
      ‖plaquette h A μ ν x - 1‖ ≤ 4 * (h * slotNorm A μ ν x) := by
  have hn : ‖h • A μ x‖ + ‖h • A ν (x + gridStep μ)‖ + ‖-(h • A μ (x + gridStep ν))‖ +
      ‖-(h • A ν x)‖ = h * slotNorm A μ ν x := by
    simp only [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh, slotNorm]; ring
  obtain ⟨h1, h2⟩ := norm_logChart_exp4_sub_le (h • A μ x) (h • A ν (x + gridStep μ))
    (-(h • A μ (x + gridStep ν))) (-(h • A ν x)) (by rw [hn]; exact hs)
  rw [hn] at h1 h2
  refine ⟨?_, h1⟩
  rw [curvRem, curvature, extD_eq h hh.ne', ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hp : plaquette h A μ ν x = exp (h • A μ x) * exp (h • A ν (x + gridStep μ)) *
      exp (-(h • A μ (x + gridStep ν))) * exp (-(h • A ν x)) := rfl
  rw [hp]
  calc (h ^ 2)⁻¹ * ‖logChart (exp (h • A μ x) * exp (h • A ν (x + gridStep μ)) *
        exp (-(h • A μ (x + gridStep ν))) * exp (-(h • A ν x))) -
        (h • A μ x + h • A ν (x + gridStep μ) + -(h • A μ (x + gridStep ν)) + -(h • A ν x))‖
      ≤ (h ^ 2)⁻¹ * (21 * (h * slotNorm A μ ν x) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 21 * slotNorm A μ ν x ^ 2 := by field_simp

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The slot size measured through `T`. -/
def slotNormT (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι) (x : ι → ZMod n) : ℝ :=
  ‖T (A μ x)‖ + ‖T (A ν (x + gridStep μ))‖ + ‖T (A μ (x + gridStep ν))‖ + ‖T (A ν x)‖

theorem slotNorm_le (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖)
    (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι) (x : ι → ZMod n) :
    slotNorm A μ ν x ≤ c * slotNormT T A μ ν x := by
  simp only [slotNorm, slotNormT, mul_add]
  gcongr <;> exact hc _

/-- The envelope read in `E`: `‖T 𝒩‖ ≤ 21 ‖T‖ c² |W|_T²` on the chart `h |W| ≤ 1/8`. -/
theorem norm_map_curvRem_le (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖) {h : ℝ} (hh : 0 < h) (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι)
    (x : ι → ZMod n) (hs : h * slotNorm A μ ν x ≤ 1 / 8) :
    ‖T (curvRem h A μ ν x)‖ ≤ 21 * ‖T‖ * c ^ 2 * slotNormT T A μ ν x ^ 2 := by
  have hsl := slotNorm_le T hc A μ ν x
  have h1 := (norm_curvRem_le hh A μ ν x hs).1
  have h0 : 0 ≤ slotNorm A μ ν x := by unfold slotNorm; positivity
  calc ‖T (curvRem h A μ ν x)‖ ≤ ‖T‖ * ‖curvRem h A μ ν x‖ := T.le_opNorm _
    _ ≤ ‖T‖ * (21 * slotNorm A μ ν x ^ 2) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ ‖T‖ * (21 * (c * slotNormT T A μ ν x) ^ 2) := by
        gcongr
    _ = 21 * ‖T‖ * c ^ 2 * slotNormT T A μ ν x ^ 2 := by ring

theorem pow_four_sum_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (a + b + c + d) ^ 4 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
  have h1 : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
      sq_nonneg (b - d), sq_nonneg (c - d)]
  have h2 : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 ≤ 4 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - d ^ 2),
      sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (c ^ 2 - d ^ 2)]
  have h0 : 0 ≤ (a + b + c + d) ^ 2 := sq_nonneg _
  calc (a + b + c + d) ^ 4 = ((a + b + c + d) ^ 2) ^ 2 := by ring
    _ ≤ (4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 16 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 := by ring
    _ ≤ 16 * (4 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4)) := by gcongr
    _ = 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by ring

variable [NeZero n]

theorem gridL4Norm_pow_four {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ}
    (hh : 0 ≤ h) (u : (ι → ZMod n) → F) :
    gridL4Norm h u ^ 4 = h ^ Fintype.card ι * ∑ x, ‖u x‖ ^ 4 := by
  rw [gridL4Norm, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- **`L²_h` form of the quadratic envelope** (four dimensions, uniformly in `n`, `h`): if the
scaled chart condition `h |W_{μν}| ≤ 1/8` holds at every site, then
`‖T 𝒩_{μν}(A)‖_{2,h} ≤ 12 · 21 ‖T‖ c² (‖T A_μ‖²_{4,h} + ‖T A_ν‖²_{4,h})`. -/
theorem curvRem_L2_le (hι : Fintype.card ι = 4) (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖) {h : ℝ} (hh : 0 < h) (A : ι → (ι → ZMod n) → 𝔸) (μ ν : ι)
    (hs : ∀ x, h * slotNorm A μ ν x ≤ 1 / 8) :
    gridL2Norm h (fun x => T (curvRem h A μ ν x)) ≤
      12 * (21 * ‖T‖ * c ^ 2) * (gridL4Norm h (fun x => T (A μ x)) ^ 2 +
        gridL4Norm h (fun x => T (A ν x)) ^ 2) := by
  set K := 21 * ‖T‖ * c ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set a := gridL4Norm h (fun x => T (A μ x))
  set b := gridL4Norm h (fun x => T (A ν x))
  have ha : 0 ≤ a := gridL4Norm_nonneg hh.le _
  have hb : 0 ≤ b := gridL4Norm_nonneg hh.le _
  -- pointwise bound
  have hpt : ∀ x, ‖T (curvRem h A μ ν x)‖ ^ 2 ≤ K ^ 2 * (64 * (‖T (A μ x)‖ ^ 4 +
      ‖T (A ν (x + gridStep μ))‖ ^ 4 + ‖T (A μ (x + gridStep ν))‖ ^ 4 + ‖T (A ν x)‖ ^ 4)) := by
    intro x
    have h1 := norm_map_curvRem_le T hc0 hc hh A μ ν x (hs x)
    have h0 : 0 ≤ slotNormT T A μ ν x := by unfold slotNormT; positivity
    have h4 := pow_four_sum_le (norm_nonneg (T (A μ x))) (norm_nonneg (T (A ν (x + gridStep μ))))
      (norm_nonneg (T (A μ (x + gridStep ν)))) (norm_nonneg (T (A ν x)))
    calc ‖T (curvRem h A μ ν x)‖ ^ 2 ≤ (K * slotNormT T A μ ν x ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = K ^ 2 * slotNormT T A μ ν x ^ 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  -- summation, using translation invariance of the sums
  have hshμ : ∑ x, ‖T (A ν (x + gridStep μ))‖ ^ 4 = ∑ x, ‖T (A ν x)‖ ^ 4 :=
    sum_add_gridStep (fun x => ‖T (A ν x)‖ ^ 4) μ
  have hshν : ∑ x, ‖T (A μ (x + gridStep ν))‖ ^ 4 = ∑ x, ‖T (A μ x)‖ ^ 4 :=
    sum_add_gridStep (fun x => ‖T (A μ x)‖ ^ 4) ν
  have hsum : h ^ 4 * ∑ x, ‖T (curvRem h A μ ν x)‖ ^ 2 ≤ 128 * K ^ 2 * (a ^ 4 + b ^ 4) := by
    have ha4 := gridL4Norm_pow_four hh.le (fun x => T (A μ x))
    have hb4 := gridL4Norm_pow_four hh.le (fun x => T (A ν x))
    rw [hι] at ha4 hb4
    calc h ^ 4 * ∑ x, ‖T (curvRem h A μ ν x)‖ ^ 2
        ≤ h ^ 4 * ∑ x, K ^ 2 * (64 * (‖T (A μ x)‖ ^ 4 + ‖T (A ν (x + gridStep μ))‖ ^ 4 +
          ‖T (A μ (x + gridStep ν))‖ ^ 4 + ‖T (A ν x)‖ ^ 4)) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => hpt x) (by positivity)
      _ = 128 * K ^ 2 * (h ^ 4 * ∑ x, ‖T (A μ x)‖ ^ 4 + h ^ 4 * ∑ x, ‖T (A ν x)‖ ^ 4) := by
          simp only [← mul_sum, sum_add_distrib, hshμ, hshν]; ring
      _ = 128 * K ^ 2 * (a ^ 4 + b ^ 4) := by rw [ha4, hb4]
  rw [gridL2Norm, periodicHodgeNormSq, hι]
  have hrhs : 0 ≤ 12 * K * (a ^ 2 + b ^ 2) := by positivity
  rw [Real.sqrt_le_left hrhs]
  calc h ^ 4 * ∑ x, ‖T (curvRem h A μ ν x)‖ ^ 2 ≤ 128 * K ^ 2 * (a ^ 4 + b ^ 4) := hsum
    _ ≤ (12 * K * (a ^ 2 + b ^ 2)) ^ 2 := by
        have hab : 0 ≤ a ^ 2 * b ^ 2 := by positivity
        have : a ^ 4 + b ^ 4 ≤ (a ^ 2 + b ^ 2) ^ 2 := by
          have e : (a ^ 2 + b ^ 2) ^ 2 = a ^ 4 + b ^ 4 + 2 * (a ^ 2 * b ^ 2) := by ring
          rw [e]; linarith
        calc 128 * K ^ 2 * (a ^ 4 + b ^ 4) ≤ 128 * K ^ 2 * (a ^ 2 + b ^ 2) ^ 2 := by gcongr
          _ ≤ 144 * K ^ 2 * (a ^ 2 + b ^ 2) ^ 2 := by gcongr; norm_num
          _ = (12 * K * (a ^ 2 + b ^ 2)) ^ 2 := by ring

end Transport

end

end RenewalGeometry.CurvatureSplit
