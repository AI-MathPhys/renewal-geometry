/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.TorusCellEmbeddingMultidim
import RenewalGeometry.Continuum.TorusPiecewiseConstantTranslation
import RenewalGeometry.Analysis.TorusCurvatureConvergence
import RenewalGeometry.DiscreteAnalysis.GridSobolevInequality

/-!
# Trigonometric and piecewise-constant reconstructions on `𝕋^d`: comparison and Fourier calculus

Generic infrastructure (no renewal notions) for `lem:native-reconstruction-identification`
and `lem:native-critical-grid` of the Einstein–SM action-closure manuscript
(`papers/einstein_sm_action_closure`, Appendix `app:native-critical-closure`).

## Setting and rendering

The manuscript works on the periodic box of side `L = 2π`, on odd grids with `n` nodes per
direction, mesh `h = 2π/n`, nodal norms `‖u‖²_{2,h} = h⁴ Σ_x |u(x)|²` and forward differences
`D⁺_{μ,h} u(x) = (u(x + h e_μ) - u(x))/h`.  We work on the unit torus
`𝕋^d = UnitAddTorus (Fin d)` (Haar probability measure, Mathlib's Fourier monomials
`mFourier m`, `m ∈ ℤ^d`) with the grid `(ℤ/N)^d`, mesh `1/N`, nodal norm
`gridNorm u = (N^{-d} Σ_g |u(g)|²)^{1/2}` and `Dp μ u = N (u(· + e_μ) - u)`
(`GridSobolev.gridFwd (1/N)`).  The dilation `x ↦ 2π x` maps one setting onto the other; it
multiplies every `L²` norm by `(2π)^{d/2}` and every derivative by `(2π)^{-1}`, so all
inequalities below hold in the paper's normalisation with constants changed by fixed factors,
and all convergence statements are unchanged.  The paper's odd `n` is allowed (every `N ≥ 1` is).

* `trigInterp u = Σ_k û(k) e_{k̃}` (`𝓘_h^trig`): the trigonometric interpolant with the
  normalised DFT coefficients `û = LatticeTorusPlancherel.dft u` on the symmetric frequency
  set `k̃ = signedRep k ∈ (-N/2, N/2]^d` (the cube `{-m, …, m}^d` for `N = 2m + 1`);
  `coef u m` are its Fourier coefficients (`mFourierCoeff_trigInterp`).
* `hasSum_coef_sq` (Parseval): `Σ_m |coef u m|² = ‖u‖²_{2,h}`.
* `coef_Dp`: `Dp μ` is the Fourier multiplier `sym N μ m = N (e^{2πi m_μ/N} - 1)`;
  `four_mul_abs_le_norm_sym`, `norm_sym_le`, `norm_sym_sub_le`: the sine-symbol bounds
  `4|m_μ| ≤ |sym| ≤ 2π|m_μ|` on the represented range and `sym → 2πi m_μ`.
* `sobSq_trigInterp_le` (**second half of `eq:native-reconstruction-comparison`**):
  `‖𝓘_h u‖²_{H¹} ≤ ‖u‖²_{2,h} + (π/2)² Σ_μ ‖D⁺_μ u‖²_{2,h}`.
* Generic `ℓ²` facts over any countable index: `tendsto_tsum_sq_sub_of_pointwise`
  (Radon–Riesz: pointwise convergence + convergence of the squared norms gives norm
  convergence) and `tendsto_tsum_sq_mul_sub` (bounded multipliers converging pointwise preserve
  `ℓ²` convergence).
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus ComplexConjugate
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.TorusTrigReconstruction

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-! ### Generic `ℓ²` lemmas over a countable index -/

section L2Seq

variable {J : Type*} [DecidableEq J] {α : Type*} {l : Filter α}

/-- Splitting a summable family along a finite set. -/
theorem tsum_eq_sum_add_tsum_ite {f : J → ℝ} (hf : Summable f) (S : Finset J) :
    ∑' j, f j = ∑ j ∈ S, f j + ∑' j, (if j ∈ S then 0 else f j) := by
  classical
  have h1 : Summable fun j => if j ∈ S then f j else 0 :=
    (hasSum_sum_of_ne_finset_zero (s := S) (fun j hj => if_neg hj)).summable
  have h2 : Summable fun j => if j ∈ S then (0 : ℝ) else f j := by
    have : (fun j => if j ∈ S then (0 : ℝ) else f j) = fun j => f j - if j ∈ S then f j else 0 := by
      funext j; split_ifs <;> simp
    rw [this]; exact hf.sub h1
  have hsplit : (fun j => f j) = fun j => (if j ∈ S then f j else 0) + (if j ∈ S then 0 else f j) := by
    funext j; split_ifs <;> simp
  conv_lhs => rw [hsplit]
  rw [h1.tsum_add h2]
  congr 1
  rw [(hasSum_sum_of_ne_finset_zero (s := S) (fun j hj => if_neg hj)).tsum_eq]
  exact Finset.sum_congr rfl fun j hj => if_pos hj

/-- Tail estimate: the `S`-tail of a nonnegative summable family is the difference of the
total and the partial sum. -/
theorem tsum_ite_eq_sub {f : J → ℝ} (hf : Summable f) (S : Finset J) :
    ∑' j, (if j ∈ S then 0 else f j) = ∑' j, f j - ∑ j ∈ S, f j := by
  rw [tsum_eq_sum_add_tsum_ite hf S]; ring

theorem summable_ite_compl {f : J → ℝ} (hf : Summable f) (S : Finset J) :
    Summable fun j => if j ∈ S then (0 : ℝ) else f j := by
  classical
  have h1 : Summable fun j => if j ∈ S then f j else 0 :=
    (hasSum_sum_of_ne_finset_zero (s := S) (fun j hj => if_neg hj)).summable
  have : (fun j => if j ∈ S then (0 : ℝ) else f j) = fun j => f j - if j ∈ S then f j else 0 := by
    funext j; split_ifs <;> simp
  rw [this]; exact hf.sub h1

theorem norm_sub_sq_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith [norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

theorem summable_norm_sub_sq {x y : J → ℂ} (hx : Summable fun j => ‖x j‖ ^ 2)
    (hy : Summable fun j => ‖y j‖ ^ 2) : Summable fun j => ‖x j - y j‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => norm_sub_sq_le (x j) (y j))
    ((hx.mul_left 2).add (hy.mul_left 2))

/-- **Radon–Riesz in `ℓ²`.**  If `x_a → x₀` pointwise and `Σ |x_a|² → Σ |x₀|²`, then
`Σ |x_a - x₀|² → 0`. -/
theorem tendsto_tsum_sq_sub_of_pointwise {x : α → J → ℂ} {x₀ : J → ℂ}
    (hx : ∀ a, Summable fun j => ‖x a j‖ ^ 2) (hx₀ : Summable fun j => ‖x₀ j‖ ^ 2)
    (hpt : ∀ j, Tendsto (fun a => x a j) l (𝓝 (x₀ j)))
    (hnorm : Tendsto (fun a => ∑' j, ‖x a j‖ ^ 2) l (𝓝 (∑' j, ‖x₀ j‖ ^ 2))) :
    Tendsto (fun a => ∑' j, ‖x a j - x₀ j‖ ^ 2) l (𝓝 0) := by
  classical
  rw [tendsto_order]
  refine ⟨fun c hc => Eventually.of_forall fun a => lt_of_lt_of_le hc
    (tsum_nonneg fun j => sq_nonneg _), fun ε hε => ?_⟩
  -- a finite set carrying all but `ε/16` of the limit mass
  obtain ⟨S, hS⟩ : ∃ S : Finset J, ∑' j, ‖x₀ j‖ ^ 2 - ∑ j ∈ S, ‖x₀ j‖ ^ 2 < ε / 16 := by
    have h := hx₀.hasSum
    rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop] at h
    obtain ⟨S, hS⟩ := h (ε / 16) (by positivity)
    refine ⟨S, ?_⟩
    have := hS S le_rfl
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).1
    linarith
  -- the bound
  have hle : ∀ a, ∑' j, ‖x a j - x₀ j‖ ^ 2 ≤ ∑ j ∈ S, ‖x a j - x₀ j‖ ^ 2 +
      2 * (∑' j, ‖x a j‖ ^ 2 - ∑ j ∈ S, ‖x a j‖ ^ 2) +
      2 * (∑' j, ‖x₀ j‖ ^ 2 - ∑ j ∈ S, ‖x₀ j‖ ^ 2) := by
    intro a
    have hs := summable_norm_sub_sq (hx a) hx₀
    rw [tsum_eq_sum_add_tsum_ite hs S]
    have htail : ∑' j, (if j ∈ S then (0 : ℝ) else ‖x a j - x₀ j‖ ^ 2) ≤
        ∑' j, (if j ∈ S then (0 : ℝ) else 2 * ‖x a j‖ ^ 2 + 2 * ‖x₀ j‖ ^ 2) := by
      refine Summable.tsum_le_tsum (fun j => ?_) (summable_ite_compl hs S)
        (summable_ite_compl (((hx a).mul_left 2).add (hx₀.mul_left 2)) S)
      split_ifs
      · exact le_rfl
      · exact norm_sub_sq_le _ _
    have heq : ∑' j, (if j ∈ S then (0 : ℝ) else 2 * ‖x a j‖ ^ 2 + 2 * ‖x₀ j‖ ^ 2) =
        2 * (∑' j, ‖x a j‖ ^ 2 - ∑ j ∈ S, ‖x a j‖ ^ 2) +
          2 * (∑' j, ‖x₀ j‖ ^ 2 - ∑ j ∈ S, ‖x₀ j‖ ^ 2) := by
      rw [tsum_ite_eq_sub (((hx a).mul_left 2).add (hx₀.mul_left 2)) S,
        ((hx a).mul_left 2).tsum_add (hx₀.mul_left 2), tsum_mul_left, tsum_mul_left,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    linarith
  have hBlim : Tendsto (fun a => ∑ j ∈ S, ‖x a j - x₀ j‖ ^ 2 +
      2 * (∑' j, ‖x a j‖ ^ 2 - ∑ j ∈ S, ‖x a j‖ ^ 2) +
      2 * (∑' j, ‖x₀ j‖ ^ 2 - ∑ j ∈ S, ‖x₀ j‖ ^ 2)) l (𝓝 (∑ j ∈ S, ‖x₀ j - x₀ j‖ ^ 2 +
      2 * (∑' j, ‖x₀ j‖ ^ 2 - ∑ j ∈ S, ‖x₀ j‖ ^ 2) +
      2 * (∑' j, ‖x₀ j‖ ^ 2 - ∑ j ∈ S, ‖x₀ j‖ ^ 2))) := by
    refine ((tendsto_finset_sum S fun j _ =>
      (((hpt j).sub tendsto_const_nhds).norm).pow 2).add
      ((hnorm.sub (tendsto_finset_sum S fun j _ => ((hpt j).norm).pow 2)).const_mul 2)).add
      tendsto_const_nhds
  have hval : ∑ j ∈ S, ‖x₀ j - x₀ j‖ ^ 2 + 2 * (∑' j, ‖x₀ j‖ ^ 2 - ∑ j ∈ S, ‖x₀ j‖ ^ 2) +
      2 * (∑' j, ‖x₀ j‖ ^ 2 - ∑ j ∈ S, ‖x₀ j‖ ^ 2) < ε := by
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, zero_add]
    linarith
  filter_upwards [(tendsto_order.1 hBlim).2 ε hval] with a ha
  exact (hle a).trans_lt ha

/-- **Bounded multipliers preserve `ℓ²` convergence.**  If `Σ |x_a - x₀|² → 0`, `|m_a| ≤ M` and
`m_a → m₀` pointwise, then `Σ |m_a x_a - m₀ x₀|² → 0`. -/
theorem tendsto_tsum_sq_mul_sub {x : α → J → ℂ} {x₀ : J → ℂ} {m : α → J → ℂ} {m₀ : J → ℂ}
    {M : ℝ} (hx : ∀ a, Summable fun j => ‖x a j - x₀ j‖ ^ 2)
    (hx₀ : Summable fun j => ‖x₀ j‖ ^ 2)
    (hconv : Tendsto (fun a => ∑' j, ‖x a j - x₀ j‖ ^ 2) l (𝓝 0))
    (hm : ∀ a j, ‖m a j‖ ≤ M) (hm₀ : ∀ j, Tendsto (fun a => m a j) l (𝓝 (m₀ j))) :
    Tendsto (fun a => ∑' j, ‖m a j * x a j - m₀ j * x₀ j‖ ^ 2) l (𝓝 0) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hM₀ : ∀ j, ‖m₀ j‖ ≤ M := fun j =>
    le_of_tendsto (hm₀ j).norm (Eventually.of_forall fun a => hm a j)
  have hpt : ∀ a j, ‖m a j * x a j - m₀ j * x₀ j‖ ^ 2 ≤
      2 * M ^ 2 * ‖x a j - x₀ j‖ ^ 2 + 2 * (‖m a j - m₀ j‖ ^ 2 * ‖x₀ j‖ ^ 2) := by
    intro a j
    have hM : 0 ≤ M := (norm_nonneg _).trans (hm a j)
    have hsplit : m a j * x a j - m₀ j * x₀ j = m a j * (x a j - x₀ j) + (m a j - m₀ j) * x₀ j := by
      ring
    rw [hsplit]
    have h0 := norm_add_le (m a j * (x a j - x₀ j)) ((m a j - m₀ j) * x₀ j)
    have h1 : ‖m a j * (x a j - x₀ j)‖ ≤ M * ‖x a j - x₀ j‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hm a j) (norm_nonneg _)
    have h2 : ‖(m a j - m₀ j) * x₀ j‖ = ‖m a j - m₀ j‖ * ‖x₀ j‖ := norm_mul _ _
    have hA := norm_nonneg (m a j * (x a j - x₀ j) + (m a j - m₀ j) * x₀ j)
    nlinarith [norm_nonneg (m a j * (x a j - x₀ j)), norm_nonneg ((m a j - m₀ j) * x₀ j),
      sq_nonneg (M * ‖x a j - x₀ j‖ - ‖m a j - m₀ j‖ * ‖x₀ j‖), norm_nonneg (x a j - x₀ j)]
  have hsum2 : ∀ a, Summable fun j => ‖m a j - m₀ j‖ ^ 2 * ‖x₀ j‖ ^ 2 := by
    intro a
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) (hx₀.mul_left ((2 * M) ^ 2))
    have : ‖m a j - m₀ j‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hm a j, hM₀ j])
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) this 2) (sq_nonneg _)
  have hsumL : ∀ a, Summable fun j => ‖m a j * x a j - m₀ j * x₀ j‖ ^ 2 := fun a =>
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) (hpt a)
      (((hx a).mul_left (2 * M ^ 2)).add ((hsum2 a).mul_left 2))
  have hdom : Tendsto (fun a => ∑' j, ‖m a j - m₀ j‖ ^ 2 * ‖x₀ j‖ ^ 2) l (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (f := fun a j => ‖m a j - m₀ j‖ ^ 2 * ‖x₀ j‖ ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun j => (2 * M) ^ 2 * ‖x₀ j‖ ^ 2) (𝓕 := l)
      (hx₀.mul_left _) (fun j => by
        have := ((((hm₀ j).sub_const (m₀ j)).norm).pow 2).mul_const (‖x₀ j‖ ^ 2)
        simpa using this) (Eventually.of_forall fun a j => by
          rw [Real.norm_of_nonneg (by positivity)]
          have : ‖m a j - m₀ j‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hm a j, hM₀ j])
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) this 2) (sq_nonneg _))
    simpa using h
  have hup : Tendsto (fun a => 2 * M ^ 2 * ∑' j, ‖x a j - x₀ j‖ ^ 2 +
      2 * ∑' j, ‖m a j - m₀ j‖ ^ 2 * ‖x₀ j‖ ^ 2) l (𝓝 0) := by
    simpa using (hconv.const_mul (2 * M ^ 2)).add (hdom.const_mul 2)
  refine squeeze_zero (fun a => tsum_nonneg fun j => sq_nonneg _) (fun a => ?_) hup
  rw [← tsum_mul_left, ← tsum_mul_left, ← ((hx a).mul_left _).tsum_add ((hsum2 a).mul_left _)]
  exact Summable.tsum_le_tsum (hpt a) (hsumL a) (((hx a).mul_left _).add ((hsum2 a).mul_left _))

end L2Seq

/-! ### The trigonometric interpolant and its Fourier coefficients -/

section Interp

open LatticeTorusPlancherel TorusCellEmbedding TorusPiecewiseConstantTranslation

variable {d N : ℕ} [NeZero N]

/-- **The trigonometric interpolant** `𝓘_h^trig u = Σ_k û(k) e_{k̃}` with the normalised DFT
coefficients `û = dft u` on the symmetric frequency set `k̃ = signedRep k ∈ (-N/2, N/2]^d`. -/
def trigInterp (u : Grid d N → ℂ) : C(UnitAddTorus (Fin d), ℂ) :=
  ∑ k, dft u k • mFourier (signedRep k)

/-- The Fourier coefficients of `𝓘_h^trig u` (`û(k)` at `m = k̃`, zero off the represented
frequencies). -/
def coef (u : Grid d N → ℂ) (m : Fin d → ℤ) : ℂ :=
  ∑ k, if signedRep k = m then dft u k else 0

theorem mFourierCoeff_trigInterp (u : Grid d N → ℂ) (m : Fin d → ℤ) :
    mFourierCoeff (trigInterp u) m = coef u m :=
  TorusSobolev.mFourierCoeff_finset_sum univ (dft u) signedRep m

theorem signedRep_injective : Function.Injective (signedRep (d := d) (n := N)) := by
  intro k k' h
  rw [← zcast_signedRep k, ← zcast_signedRep k', h]

/-- On the represented range the signed representative of `m mod N` is `m`. -/
theorem signedRep_zcast {m : Fin d → ℤ} (hm : ∀ i, 2 * |m i| < N) :
    signedRep (zcast N m) = m := by
  funext i
  simp only [signedRep, zcast]
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩
  · have := hm i; have := neg_abs_le (m i); omega
  · have := hm i; have := le_abs_self (m i); omega

theorem coef_eq (u : Grid d N → ℂ) (m : Fin d → ℤ) :
    coef u m = if signedRep (zcast N m) = m then dft u (zcast N m) else 0 := by
  unfold coef
  split_ifs with h
  · rw [Finset.sum_eq_single (zcast N m)]
    · rw [if_pos h]
    · intro k _ hk
      rw [if_neg]
      intro hk'
      exact hk (by rw [← zcast_signedRep k, hk'])
    · simp
  · refine Finset.sum_eq_zero fun k _ => if_neg fun hk => h ?_
    rw [← hk, zcast_signedRep]

theorem coef_signedRep (u : Grid d N → ℂ) (k : Grid d N) : coef u (signedRep k) = dft u k := by
  rw [coef_eq, zcast_signedRep, if_pos rfl]

theorem signedRep_zcast_of_coef_ne_zero {u : Grid d N → ℂ} {m : Fin d → ℤ}
    (h : coef u m ≠ 0) : signedRep (zcast N m) = m := by
  rw [coef_eq] at h
  by_contra h'
  exact h (if_neg h')

theorem abs_le_of_coef_ne_zero {u : Grid d N → ℂ} {m : Fin d → ℤ} (h : coef u m ≠ 0)
    (i : Fin d) : |(m i : ℝ)| * 2 ≤ N := by
  have := abs_signedRep_le (zcast N m) i
  rwa [signedRep_zcast_of_coef_ne_zero h] at this

theorem coef_eq_zero_of_not_mem (u : Grid d N → ℂ) {m : Fin d → ℤ}
    (hm : m ∉ (univ : Finset (Grid d N)).image signedRep) : coef u m = 0 := by
  refine Finset.sum_eq_zero fun k _ => if_neg fun hk => hm ?_
  exact Finset.mem_image.2 ⟨k, mem_univ _, hk⟩

theorem coef_sub (u v : Grid d N → ℂ) (m : Fin d → ℤ) : coef (u - v) m = coef u m - coef v m := by
  simp only [coef, dft_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem coef_add (u v : Grid d N → ℂ) (m : Fin d → ℤ) : coef (u + v) m = coef u m + coef v m := by
  simp only [coef, dft_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem coef_smul (c : ℂ) (u : Grid d N → ℂ) (m : Fin d → ℤ) : coef (c • u) m = c * coef u m := by
  simp only [coef, dft_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem gridNorm_sq (u : Grid d N → ℂ) :
    gridNorm u ^ 2 = ((N : ℝ) ^ d)⁻¹ * ∑ x, ‖u x‖ ^ 2 := by
  unfold gridNorm
  rw [Real.sq_sqrt (by positivity), Fintype.card_fin, one_div, inv_pow]

/-- **Parseval for the interpolant**: `Σ_m |coef u m|² = ‖u‖²_{2,h}`. -/
theorem hasSum_coef_sq (u : Grid d N → ℂ) :
    HasSum (fun m => ‖coef u m‖ ^ 2) (gridNorm u ^ 2) := by
  have h := hasSum_sum_of_ne_finset_zero (f := fun m => ‖coef u m‖ ^ 2)
    (s := (univ : Finset (Grid d N)).image signedRep)
    (L := SummationFilter.unconditional (Fin d → ℤ))
    (fun m hm => by simp [coef_eq_zero_of_not_mem u hm])
  rw [Finset.sum_image (fun k _ k' _ h => signedRep_injective h)] at h
  simp only [coef_signedRep] at h
  rw [sum_norm_dft_sq, ← gridNorm_sq] at h
  exact h

theorem summable_coef_sq (u : Grid d N → ℂ) : Summable fun m => ‖coef u m‖ ^ 2 :=
  (hasSum_coef_sq u).summable

theorem tsum_coef_sq (u : Grid d N → ℂ) : ∑' m, ‖coef u m‖ ^ 2 = gridNorm u ^ 2 :=
  (hasSum_coef_sq u).tsum_eq

/-- Every finite-support weighted family of coefficients is summable. -/
theorem summable_mul_coef (w : (Fin d → ℤ) → ℝ) (u : Grid d N → ℂ) :
    Summable fun m => w m * ‖coef u m‖ ^ 2 :=
  summable_of_ne_finset_zero (s := (univ : Finset (Grid d N)).image signedRep)
    (fun m hm => by simp [coef_eq_zero_of_not_mem u hm])

/-! ### The forward difference as a Fourier multiplier -/

/-- The symbol of the scaled forward difference: `sym N μ m = N (e^{2πi m_μ/N} - 1)`. -/
def sym (N : ℕ) (μ : Fin d) (m : Fin d → ℤ) : ℂ :=
  (N : ℂ) * (Complex.exp (2 * π * Complex.I * (m μ : ℂ) / N) - 1)

/-- The scaled forward difference `D⁺_μ u = N (u(· + e_μ) - u)` (mesh `1/N`). -/
def Dp (μ : Fin d) (u : Grid d N → ℂ) : Grid d N → ℂ := GridSobolev.gridFwd ((N : ℝ)⁻¹) μ u

theorem Dp_apply (μ : Fin d) (u : Grid d N → ℂ) (x : Grid d N) :
    Dp μ u x = (N : ℂ) * (u (x + Pi.single μ 1) - u x) := by
  simp [Dp, GridSobolev.gridFwd, GridSobolev.gridStep, Complex.real_smul]

theorem Dp_sub (μ : Fin d) (u v : Grid d N → ℂ) : Dp μ (u - v) = Dp μ u - Dp μ v := by
  funext x; simp only [Dp_apply, Pi.sub_apply]; ring

theorem stdAddChar_eq_exp (k : Grid d N) (μ : Fin d) :
    (ZMod.stdAddChar (k μ) : ℂ) =
      Complex.exp (2 * π * Complex.I * ((signedRep k μ : ℤ) : ℂ) / N) := by
  conv_lhs => rw [← ZMod.coe_valMinAbs (k μ)]
  rw [ZMod.stdAddChar_coe]
  rfl

theorem dft_Dp (μ : Fin d) (u : Grid d N → ℂ) (k : Grid d N) :
    dft (Dp μ u) k = sym N μ (signedRep k) * dft u k := by
  have e : Dp μ u = (N : ℂ) • (LatticeTorusPlancherel.shift μ u - u) := by
    funext x; simp [Dp_apply, LatticeTorusPlancherel.shift]
  rw [e, dft_smul, dft_sub, dft_shift, stdAddChar_eq_exp, sym, smul_eq_mul, smul_eq_mul]
  ring

/-- `D⁺_μ` is the Fourier multiplier `sym N μ` on the coefficients of the interpolant. -/
theorem coef_Dp (μ : Fin d) (u : Grid d N → ℂ) (m : Fin d → ℤ) :
    coef (Dp μ u) m = sym N μ m * coef u m := by
  unfold coef
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rw [dft_Dp, h]
  · rw [mul_zero]

theorem two_pi_mul_div_eq (N : ℕ) (r : ℤ) :
    2 * π * Complex.I * (r : ℂ) / N = Complex.I * ((2 * π * r / N : ℝ) : ℂ) := by
  push_cast; ring

/-- `|sym N μ m| ≤ 2π |m_μ|`. -/
theorem norm_sym_le (N : ℕ) (μ : Fin d) (m : Fin d → ℤ) :
    ‖sym N μ m‖ ≤ 2 * π * |(m μ : ℝ)| := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · simp only [sym, h0, CharP.cast_eq_zero, zero_mul, norm_zero]; positivity
  have hN : (0 : ℝ) < N := by exact_mod_cast hpos
  rw [sym, two_pi_mul_div_eq, norm_mul, Complex.norm_natCast]
  calc (N : ℝ) * ‖Complex.exp (Complex.I * ((2 * π * (m μ : ℤ) / N : ℝ) : ℂ)) - 1‖
      ≤ N * ‖(2 * π * (m μ : ℤ) / N : ℝ)‖ :=
        mul_le_mul_of_nonneg_left Real.norm_exp_I_mul_ofReal_sub_one_le hN.le
    _ = 2 * π * |(m μ : ℝ)| := by
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
          abs_of_pos hN]
        field_simp

theorem abs_sin_ge {y : ℝ} (hy : |y| ≤ π / 2) : 2 / π * |y| ≤ |Real.sin y| := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h] at hy ⊢
    exact (Real.mul_le_sin h hy).trans (le_abs_self _)
  · rw [abs_of_neg h] at hy ⊢
    have := Real.mul_le_sin (by linarith : 0 ≤ -y) hy
    rw [Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

/-- **The sine bound**: on the represented range `2|m_μ| ≤ N`, `4|m_μ| ≤ |sym N μ m|`. -/
theorem four_mul_abs_le_norm_sym {N : ℕ} (μ : Fin d) {m : Fin d → ℤ}
    (hm : |(m μ : ℝ)| * 2 ≤ N) : 4 * |(m μ : ℝ)| ≤ ‖sym N μ m‖ := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · simp only [h0, CharP.cast_eq_zero] at hm
    have : |(m μ : ℝ)| = 0 := le_antisymm (by linarith) (abs_nonneg _)
    rw [this, mul_zero]; exact norm_nonneg _
  have hN : (0 : ℝ) < N := by exact_mod_cast hpos
  rw [sym, two_pi_mul_div_eq, norm_mul, Complex.norm_natCast,
    Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have habs : |2 * π * ((m μ : ℤ) : ℝ) / N / 2| = π * |(m μ : ℝ)| / N := by
    rw [abs_div, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
      abs_of_pos hN, abs_two]
    field_simp
  have hy : |2 * π * ((m μ : ℤ) : ℝ) / N / 2| ≤ π / 2 := by
    rw [habs, div_le_div_iff₀ hN (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have hs := abs_sin_ge hy
  rw [habs] at hs
  have e2 : 2 / π * (π * |(m μ : ℝ)| / N) = 2 * |(m μ : ℝ)| / N := by
    field_simp
  rw [e2] at hs
  rw [abs_two]
  calc 4 * |(m μ : ℝ)| = N * (2 * (2 * |(m μ : ℝ)| / N)) := by field_simp; ring
    _ ≤ N * (2 * |Real.sin (2 * π * ((m μ : ℤ) : ℝ) / N / 2)|) := by gcongr

/-- `(2π m_μ)² ≤ (π/2)² |sym N μ m|²` on the represented range. -/
theorem sq_two_pi_le_sym {N : ℕ} (μ : Fin d) {m : Fin d → ℤ} (hm : |(m μ : ℝ)| * 2 ≤ N) :
    (2 * π * m μ) ^ 2 ≤ (π / 2) ^ 2 * ‖sym N μ m‖ ^ 2 := by
  have h := four_mul_abs_le_norm_sym μ hm
  have h2 : (2 * π * m μ) ^ 2 = (π / 2) ^ 2 * (4 * |(m μ : ℝ)|) ^ 2 := by
    rw [mul_pow (4 : ℝ), sq_abs]; ring
  rw [h2]
  gcongr

/-- `|sym N μ m - 2πi m_μ| ≤ (2π|m_μ|)²/N` once `2π|m_μ| ≤ N`. -/
theorem norm_sym_sub_le {N : ℕ} (μ : Fin d) {m : Fin d → ℤ}
    (hm : 2 * π * |(m μ : ℝ)| ≤ N) (hN : 0 < N) :
    ‖sym N μ m - 2 * π * Complex.I * m μ‖ ≤ (2 * π * |(m μ : ℝ)|) ^ 2 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set x : ℂ := 2 * π * Complex.I * (m μ : ℂ) / N with hx
  have hxn : ‖x‖ = 2 * π * |(m μ : ℝ)| / N := by
    rw [hx, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_natCast,
      Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_intCast]
    ring
  have hx1 : ‖x‖ ≤ 1 := by rw [hxn, div_le_one hN']; exact hm
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNx : (N : ℂ) * x = 2 * π * Complex.I * m μ := by rw [hx]; field_simp
  have e : sym N μ m - 2 * π * Complex.I * m μ = (N : ℂ) * (Complex.exp x - 1 - x) := by
    simp only [sym]
    rw [← hx]
    linear_combination hNx
  rw [e, norm_mul, Complex.norm_natCast]
  calc (N : ℝ) * ‖Complex.exp x - 1 - x‖ ≤ N * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_sub_id_le hx1) hN'.le
    _ = (2 * π * |(m μ : ℝ)|) ^ 2 / N := by rw [hxn]; field_simp

/-- `sym N μ m → 2πi m_μ` as `N → ∞`. -/
theorem tendsto_sym {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (μ : Fin d) (m : Fin d → ℤ) :
    Tendsto (fun k => sym (n k) μ m) atTop (𝓝 (2 * π * Complex.I * m μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hn' : Tendsto (fun k => ((n k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hev : ∀ᶠ k in atTop, 2 * π * |(m μ : ℝ)| + 1 ≤ (n k : ℝ) :=
    hn'.eventually_ge_atTop _
  have hlim : Tendsto (fun k => (2 * π * |(m μ : ℝ)|) ^ 2 / (n k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn'
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hlim
  filter_upwards [hev] with k hk
  have h0 : 0 ≤ 2 * π * |(m μ : ℝ)| := by positivity
  have hpos : 0 < n k := by
    have : (0 : ℝ) < n k := by linarith
    exact_mod_cast this
  exact norm_sym_sub_le μ (by linarith) hpos

/-! ### The `H¹` bound of the interpolant -/

/-- Pointwise weight comparison on the represented range. -/
theorem sobWeight_mul_coef_le (u : Grid d N → ℂ) (m : Fin d → ℤ) :
    TorusSobolev.sobWeight m * ‖coef u m‖ ^ 2 ≤
      ‖coef u m‖ ^ 2 + (π / 2) ^ 2 * ∑ μ, ‖coef (Dp μ u) m‖ ^ 2 := by
  by_cases h : coef u m = 0
  · rw [h]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_add]
    positivity
  · simp only [coef_Dp, norm_mul, mul_pow]
    unfold TorusSobolev.sobWeight
    have hle : ∀ μ, (2 * π * m μ) ^ 2 * ‖coef u m‖ ^ 2 ≤
        (π / 2) ^ 2 * (‖sym N μ m‖ ^ 2 * ‖coef u m‖ ^ 2) := by
      intro μ
      have := sq_two_pi_le_sym (N := N) μ (abs_le_of_coef_ne_zero h μ)
      nlinarith [sq_nonneg ‖coef u m‖]
    have hsum := Finset.sum_le_sum fun μ (_ : μ ∈ (univ : Finset (Fin d))) => hle μ
    rw [← Finset.mul_sum] at hsum
    have e : (1 + 4 * π ^ 2 * ∑ i, ((m i : ℤ) : ℝ) ^ 2) * ‖coef u m‖ ^ 2 =
        ‖coef u m‖ ^ 2 + ∑ μ, (2 * π * m μ) ^ 2 * ‖coef u m‖ ^ 2 := by
      rw [add_mul, one_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun μ _ => ?_
      ring
    rw [e]
    linarith

/-- **`‖𝓘_h u‖²_{H¹} ≤ ‖u‖²_{2,h} + (π/2)² Σ_μ ‖D⁺_μ u‖²_{2,h}`** (second half of
`eq:native-reconstruction-comparison`, via the sine bound). -/
theorem sobSq_trigInterp_le (u : Grid d N → ℂ) :
    TorusSobolev.sobSq 1 (trigInterp u) ≤
      gridNorm u ^ 2 + (π / 2) ^ 2 * ∑ μ, gridNorm (Dp μ u) ^ 2 := by
  unfold TorusSobolev.sobSq TorusSobolev.coeffSobSq
  simp only [Real.rpow_one]
  have hc : (fun n => mFourierCoeff (⇑(trigInterp u)) n) = coef u :=
    funext (mFourierCoeff_trigInterp u)
  simp only [hc]
  simp only [← tsum_coef_sq]
  have hS : ∀ μ, Summable fun m => ‖coef (Dp μ u) m‖ ^ 2 := fun μ => summable_coef_sq _
  rw [← Summable.tsum_finsetSum (fun μ _ => hS μ), ← tsum_mul_left,
    ← (summable_coef_sq u).tsum_add ((summable_sum fun μ _ => hS μ).mul_left _)]
  refine Summable.tsum_le_tsum (fun m => ?_) (summable_mul_coef _ u)
    ((summable_coef_sq u).add ((summable_sum fun μ _ => hS μ).mul_left _))
  exact sobWeight_mul_coef_le u m

/-- The paper's form: `‖𝓘_h u‖_{H¹} ≤ (π/2) ‖u‖_{1,h}`,
`‖u‖²_{1,h} = ‖u‖²_{2,h} + Σ_μ ‖D⁺_μ u‖²_{2,h}`. -/
theorem sobNorm_trigInterp_le (u : Grid d N → ℂ) :
    TorusSobolev.sobNorm 1 (trigInterp u) ≤
      π / 2 * Real.sqrt (gridNorm u ^ 2 + ∑ μ, gridNorm (Dp μ u) ^ 2) := by
  unfold TorusSobolev.sobNorm
  have hpi : 1 ≤ (π / 2) ^ 2 := by
    have := Real.pi_gt_three; nlinarith
  have hS : 0 ≤ ∑ μ, gridNorm (Dp μ u) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← Real.sqrt_sq (by positivity : 0 ≤ π / 2), ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ((sobSq_trigInterp_le u).trans ?_)
  nlinarith [sq_nonneg (gridNorm u)]

end Interp

/-! ### Raw versus trigonometric reconstruction: `eq:native-reconstruction-comparison` -/

section Compare

open LatticeTorusPlancherel TorusCellEmbedding TorusPiecewiseConstantTranslation

variable {d N : ℕ} [NeZero N]

theorem index_add_samplePt (y : UnitAddTorus (Fin d)) (g : Grid d N) :
    TorusPiecewiseConstantTranslation.index N (y + samplePt g) =
      TorusPiecewiseConstantTranslation.index N y + g := by
  funext i
  simp only [TorusPiecewiseConstantTranslation.index, Pi.add_apply, samplePt]
  have h := TorusPiecewiseConstantTranslation.index1_add_int (N := N) (y i) ((g i).val : ℤ)
  have e1 : (((g i).val : ℤ) : ℝ) = ((g i).val : ℝ) := Int.cast_natCast _
  have e2 : (((g i).val : ℤ) : ZMod N) = g i := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [e1, e2] at h
  exact h

theorem trigInterp_apply (u : Grid d N → ℂ) (y : UnitAddTorus (Fin d)) :
    trigInterp u y = ∑ k, dft u k * mFourier (signedRep k) y := by
  simp only [trigInterp, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]

theorem trigInterp_add_samplePt (u : Grid d N → ℂ) (y : UnitAddTorus (Fin d)) (g : Grid d N) :
    trigInterp u (y + samplePt g) =
      ∑ k, (dft u k * mFourier (signedRep k) y) * latticeChar k g := by
  rw [trigInterp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mFourier_add_apply', mFourier_samplePt, zcast_signedRep]
  ring

theorem apply_add_eq_sum (u : Grid d N → ℂ) (c g : Grid d N) :
    u (c + g) = ∑ k, (dft u k * latticeChar k c) * latticeChar k g := by
  rw [← dft_inversion' u (c + g)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [latticeChar_add_right, smul_eq_mul]
  ring

/-- The DFT of a lattice trigonometric sum returns its coefficients. -/
theorem dft_trigSum (a : Grid d N → ℂ) (ℓ : Grid d N) :
    dft (fun g => ∑ k, a k * latticeChar k g) ℓ = a ℓ := by
  have hn : ((N : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hinner : ∑ g : Grid d N, (starRingEnd ℂ) (latticeChar ℓ g) * ∑ k, a k * latticeChar k g =
      ∑ k, a k * ∑ g : Grid d N, latticeChar g (k - ℓ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun g _ => ?_
    rw [latticeChar_sub_right, latticeChar_comm g k, latticeChar_comm g ℓ]
    ring
  unfold dft
  simp only [smul_eq_mul]
  rw [hinner]
  simp only [sum_latticeChar, sub_eq_zero]
  rw [Finset.sum_eq_single ℓ]
  · rw [if_pos rfl]; field_simp
  · intro k _ hk; rw [if_neg hk, mul_zero]
  · simp

/-- Parseval for lattice trigonometric sums: `Σ_g |Σ_k a_k e(k·g)|² = N^d Σ_k |a_k|²`. -/
theorem sum_norm_trigSum_sq (a : Grid d N → ℂ) :
    ∑ g, ‖∑ k, a k * latticeChar k g‖ ^ 2 = (N : ℝ) ^ d * ∑ k, ‖a k‖ ^ 2 := by
  have h := sum_norm_dft_sq (fun g => ∑ k, a k * latticeChar k g)
  simp only [dft_trigSum] at h
  have hN : (0 : ℝ) < (N : ℝ) ^ d := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) d
  rw [h, ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]

/-- The comparison weight `min(4, (2π Σ_i |m_i| / N)²)`. -/
def cmpW (N : ℕ) (m : Fin d → ℤ) : ℝ := min 4 ((2 * π * (∑ i, |(m i : ℝ)|) / N) ^ 2)

theorem cmpW_nonneg (N : ℕ) (m : Fin d → ℤ) : 0 ≤ cmpW N m := le_min (by norm_num) (sq_nonneg _)

theorem cmpW_le_four (N : ℕ) (m : Fin d → ℤ) : cmpW N m ≤ 4 := min_le_left _ _

theorem norm_mFourier_sub_latticeChar_sq_le (k : Grid d N) (y : UnitAddTorus (Fin d)) :
    ‖mFourier (signedRep k) y - latticeChar k (TorusPiecewiseConstantTranslation.index N y)‖ ^ 2
      ≤ cmpW N (signedRep k) := by
  have e : latticeChar k (TorusPiecewiseConstantTranslation.index N y) =
      mFourier (signedRep k) (samplePt (TorusCellEmbedding.index N y)) := by
    rw [mFourier_samplePt, zcast_signedRep]; rfl
  rw [e]
  refine le_min ?_ ?_
  · have h2 : ‖mFourier (signedRep k) y - mFourier (signedRep k)
        (samplePt (TorusCellEmbedding.index N y))‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by rw [TorusSobolev.norm_mFourier_apply, TorusSobolev.norm_mFourier_apply]; norm_num)
    nlinarith [norm_nonneg (mFourier (signedRep k) y - mFourier (signedRep k)
        (samplePt (TorusCellEmbedding.index N y)))]
  · exact pow_le_pow_left₀ (norm_nonneg _) (mFourier_sub_sample_le _ y) 2

/-- Pointwise identity behind the comparison: averaging over the grid translates of a point. -/
theorem sum_norm_trigInterp_sub_pc_sq (u : Grid d N → ℂ) (y : UnitAddTorus (Fin d)) :
    ∑ g : Grid d N, ‖trigInterp u (y + samplePt g) - pc u (y + samplePt g)‖ ^ 2 =
      (N : ℝ) ^ d * ∑ k, ‖dft u k‖ ^ 2 *
        ‖mFourier (signedRep k) y - latticeChar k (TorusPiecewiseConstantTranslation.index N y)‖
          ^ 2 := by
  set c := TorusPiecewiseConstantTranslation.index N y
  have hpt : ∀ g : Grid d N, trigInterp u (y + samplePt g) - pc u (y + samplePt g) =
      ∑ k, (dft u k * (mFourier (signedRep k) y - latticeChar k c)) * latticeChar k g := by
    intro g
    rw [trigInterp_add_samplePt]
    have : pc u (y + samplePt g) = u (c + g) := by
      simp only [pc, index_add_samplePt]; rfl
    rw [this, apply_add_eq_sum u c g, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [hpt]
  rw [sum_norm_trigSum_sq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, mul_pow]

theorem measurable_trigInterp_sub_pc (u : Grid d N → ℂ) :
    Measurable fun y : UnitAddTorus (Fin d) => trigInterp u y - pc u y :=
  (trigInterp u).continuous.measurable.sub (stronglyMeasurable_pc u).measurable

/-- **The comparison estimate (integrated form).**
`∫ |𝓘_h u - R_h^0 u|² ≤ Σ_k |û(k)|² min(4, (2π Σ_i |k̃_i|/N)²)`. -/
theorem lintegral_trigInterp_sub_pc_le (u : Grid d N → ℂ) :
    ∫⁻ y, ‖trigInterp u y - pc u y‖ₑ ^ 2 ≤
      ENNReal.ofReal (∑ k, ‖dft u k‖ ^ 2 * cmpW N (signedRep k)) := by
  set G : UnitAddTorus (Fin d) → ℂ := fun y => trigInterp u y - pc u y with hG
  set S := ∑ k, ‖dft u k‖ ^ 2 * cmpW N (signedRep k)
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (cmpW_nonneg _ _)
  have hmeas : ∀ g : Grid d N, Measurable fun y => ‖G (y + samplePt g)‖ₑ ^ 2 := fun g =>
    ((measurable_trigInterp_sub_pc u).comp (measurable_add_const _)).enorm.pow_const 2
  have htr : ∀ g : Grid d N, ∫⁻ y, ‖G (y + samplePt g)‖ₑ ^ 2 = ∫⁻ y, ‖G y‖ₑ ^ 2 := fun g =>
    lintegral_add_right_eq_self (fun y => ‖G y‖ₑ ^ 2) (samplePt g)
  have hsum : (Fintype.card (Grid d N) : ℝ≥0∞) * ∫⁻ y, ‖G y‖ₑ ^ 2 =
      ∫⁻ y, ∑ g : Grid d N, ‖G (y + samplePt g)‖ₑ ^ 2 := by
    rw [lintegral_finsetSum' _ fun g _ => (hmeas g).aemeasurable]
    simp only [htr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hpt : ∀ y, ∑ g : Grid d N, ‖G (y + samplePt g)‖ₑ ^ 2 ≤
      ENNReal.ofReal ((N : ℝ) ^ d * S) := by
    intro y
    have e : ∑ g : Grid d N, ‖G (y + samplePt g)‖ₑ ^ 2 =
        ENNReal.ofReal (∑ g : Grid d N, ‖G (y + samplePt g)‖ ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun g _ => sq_nonneg _)]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    rw [e]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hG]
    rw [sum_norm_trigInterp_sub_pc_sq]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left (norm_mFourier_sub_latticeChar_sq_le k y) (sq_nonneg _)
  have hint : ∫⁻ y, ∑ g : Grid d N, ‖G (y + samplePt g)‖ₑ ^ 2 ≤
      ENNReal.ofReal ((N : ℝ) ^ d * S) := by
    calc ∫⁻ y, ∑ g : Grid d N, ‖G (y + samplePt g)‖ₑ ^ 2
        ≤ ∫⁻ _y : UnitAddTorus (Fin d), ENNReal.ofReal ((N : ℝ) ^ d * S) := lintegral_mono hpt
      _ = ENNReal.ofReal ((N : ℝ) ^ d * S) := by
          rw [lintegral_const, measure_univ, mul_one]
  rw [← hsum] at hint
  have hcard : (Fintype.card (Grid d N) : ℝ≥0∞) = ENNReal.ofReal ((N : ℝ) ^ d) := by
    rw [← ENNReal.ofReal_natCast]
    congr 1
    simp [LatticeTorusPlancherel.Grid, ZMod.card]
  rw [hcard, ENNReal.ofReal_mul (by positivity)] at hint
  have hN0 : ENNReal.ofReal ((N : ℝ) ^ d) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) d
  exact (ENNReal.mul_le_mul_iff_right hN0 ENNReal.ofReal_ne_top).1 hint

/-- The comparison sum in terms of the Fourier coefficients of the interpolant. -/
theorem sum_dft_cmpW_eq (u : Grid d N → ℂ) :
    ∑ k, ‖dft u k‖ ^ 2 * cmpW N (signedRep k) = ∑' m, cmpW N m * ‖coef u m‖ ^ 2 := by
  have h := hasSum_sum_of_ne_finset_zero (f := fun m => cmpW N m * ‖coef u m‖ ^ 2)
    (s := (univ : Finset (Grid d N)).image signedRep)
    (L := SummationFilter.unconditional (Fin d → ℤ))
    (fun m hm => by simp [coef_eq_zero_of_not_mem u hm])
  rw [Finset.sum_image (fun k _ k' _ h => signedRep_injective h)] at h
  simp only [coef_signedRep] at h
  rw [h.tsum_eq]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **`eq:native-reconstruction-comparison` (sharp form).**
`‖𝓘_h u - R_h^0 u‖_{L²} ≤ (Σ_m min(4, (2π|m|₁/N)²) |coef u m|²)^{1/2}`. -/
theorem eLpNorm_trigInterp_sub_pc_le (u : Grid d N → ℂ) :
    eLpNorm (fun y => trigInterp u y - pc u y) 2 (volume : Measure (UnitAddTorus (Fin d))) ≤
      ENNReal.ofReal (Real.sqrt (∑' m, cmpW N m * ‖coef u m‖ ^ 2)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  have h := lintegral_trigInterp_sub_pc_le u
  rw [sum_dft_cmpW_eq] at h
  have hS : 0 ≤ ∑' m, cmpW N m * ‖coef u m‖ ^ 2 :=
    tsum_nonneg fun m => mul_nonneg (cmpW_nonneg _ _) (sq_nonneg _)
  have e : ∀ y, ‖trigInterp u y - pc u y‖ₑ ^ (2 : ℝ) = ‖trigInterp u y - pc u y‖ₑ ^ 2 := fun y =>
    ENNReal.rpow_two _
  simp only [e]
  calc (∫⁻ y, ‖trigInterp u y - pc u y‖ₑ ^ 2) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (∑' m, cmpW N m * ‖coef u m‖ ^ 2)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (∑' m, cmpW N m * ‖coef u m‖ ^ 2)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hS (by norm_num), Real.sqrt_eq_rpow]

/-- `cmpW N m ≤ (π/2)² d Σ_μ |sym N μ m|² / N²` on the represented range. -/
theorem cmpW_le_sym {u : Grid d N → ℂ} {m : Fin d → ℤ} (h : coef u m ≠ 0) :
    cmpW N m ≤ (π / 2) ^ 2 * d / (N : ℝ) ^ 2 * ∑ μ, ‖sym N μ m‖ ^ 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine (min_le_right _ _).trans ?_
  have hcs : (∑ i, |(m i : ℝ)|) ^ 2 ≤ d * ∑ i, |(m i : ℝ)| ^ 2 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin d)))
      (f := fun i => |(m i : ℝ)|)
    simpa using h1
  have hsym : ∀ i, (2 * π * |(m i : ℝ)|) ^ 2 ≤ (π / 2) ^ 2 * ‖sym N i m‖ ^ 2 := by
    intro i
    have := sq_two_pi_le_sym (N := N) i (abs_le_of_coef_ne_zero h i)
    have e : (2 * π * |(m i : ℝ)|) ^ 2 = (2 * π * m i) ^ 2 := by
      rw [mul_pow, sq_abs, ← mul_pow]
    rw [e]; exact this
  rw [div_pow, mul_pow, mul_pow]
  have hsum : (2 : ℝ) ^ 2 * π ^ 2 * (∑ i, |(m i : ℝ)|) ^ 2 ≤
      (d : ℝ) * ((π / 2) ^ 2 * ∑ μ, ‖sym N μ m‖ ^ 2) := by
    calc (2 : ℝ) ^ 2 * π ^ 2 * (∑ i, |(m i : ℝ)|) ^ 2
        ≤ (2 : ℝ) ^ 2 * π ^ 2 * ((d : ℝ) * ∑ i, |(m i : ℝ)| ^ 2) := by gcongr
      _ = (d : ℝ) * ∑ i, (2 * π * |(m i : ℝ)|) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ (d : ℝ) * ∑ i, (π / 2) ^ 2 * ‖sym N i m‖ ^ 2 := by
          gcongr with i
          exact hsym i
      _ = (d : ℝ) * ((π / 2) ^ 2 * ∑ μ, ‖sym N μ m‖ ^ 2) := by
          congr 1; exact (Finset.mul_sum _ _ _).symm
  rw [div_le_iff₀ (by positivity)]
  calc (2 : ℝ) ^ 2 * π ^ 2 * (∑ i, |(m i : ℝ)|) ^ 2
      ≤ (d : ℝ) * ((π / 2) ^ 2 * ∑ μ, ‖sym N μ m‖ ^ 2) := hsum
    _ = (π / 2) ^ 2 * d / (N : ℝ) ^ 2 * (∑ μ, ‖sym N μ m‖ ^ 2) * (N : ℝ) ^ 2 := by
        field_simp

/-- **`eq:native-reconstruction-comparison`, first half** (paper form):
`‖𝓘_h u - R_h^0 u‖_{L²} ≤ C h ‖D⁺ u‖_{2,h}` with `h = 1/N`, `C = (π/2)√d` and
`‖D⁺u‖²_{2,h} = Σ_μ ‖D⁺_μ u‖²_{2,h}`. -/
theorem eLpNorm_trigInterp_sub_pc_le_grad (u : Grid d N → ℂ) :
    eLpNorm (fun y => trigInterp u y - pc u y) 2 (volume : Measure (UnitAddTorus (Fin d))) ≤
      ENNReal.ofReal (π / 2 * Real.sqrt d * (1 / N) *
        Real.sqrt (∑ μ, gridNorm (Dp μ u) ^ 2)) := by
  refine (eLpNorm_trigInterp_sub_pc_le u).trans (ENNReal.ofReal_le_ofReal ?_)
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hle : ∑' m, cmpW N m * ‖coef u m‖ ^ 2 ≤
      (π / 2) ^ 2 * d / (N : ℝ) ^ 2 * ∑ μ, gridNorm (Dp μ u) ^ 2 := by
    simp only [← tsum_coef_sq]
    rw [← Summable.tsum_finsetSum (fun μ _ => summable_coef_sq _), ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun m => ?_) (summable_mul_coef _ u)
      ((summable_sum fun μ _ => summable_coef_sq _).mul_left _)
    by_cases h : coef u m = 0
    · rw [h]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
    · simp only [coef_Dp, norm_mul, mul_pow, ← Finset.sum_mul]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (cmpW_le_sym h) (sq_nonneg _)
  rw [show π / 2 * Real.sqrt d * (1 / N) * Real.sqrt (∑ μ, gridNorm (Dp μ u) ^ 2) =
      Real.sqrt ((π / 2) ^ 2 * d / (N : ℝ) ^ 2 * ∑ μ, gridNorm (Dp μ u) ^ 2) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity), Real.sqrt_sq hN.le]
    ring]
  exact Real.sqrt_le_sqrt hle

end Compare

/-! ### Fourier coefficients of raw reconstructions and the `ℓ²` equivalence -/

section Coefficients

open LatticeTorusPlancherel TorusCellEmbedding TorusPiecewiseConstantTranslation

variable {d N : ℕ} [NeZero N]

/-- The trigonometric interpolant as an element of `L²(𝕋^d)`. -/
def trigLp (u : Grid d N → ℂ) : L²(UnitAddTorus (Fin d)) :=
  ContinuousMap.toLp 2 volume ℂ (trigInterp u)

theorem mFourierCoeff_trigLp (u : Grid d N → ℂ) (m : Fin d → ℤ) :
    mFourierCoeff (trigLp u) m = coef u m := by
  rw [trigLp, mFourierCoeff_toLp, mFourierCoeff_trigInterp]

/-- `∫ G(index y) dy = N^{-d} Σ_g G(g)`. -/
theorem integral_comp_index (G : Grid d N → ℂ) :
    ∫ y, G (TorusPiecewiseConstantTranslation.index N y) = ((N : ℂ) ^ d)⁻¹ * ∑ g, G g := by
  have h := pc_eq_sum_indicator (d := Fin d) (N := N) G
  have e : (fun y => G (TorusPiecewiseConstantTranslation.index N y)) =
      fun y => ∑ g, (cellD g).indicator (fun _ => G g) y := by
    funext y
    rw [← Finset.sum_apply, ← h]
    rfl
  rw [e, integral_finset_sum _ fun g _ =>
    (integrable_const (G g)).indicator (measurableSet_cellD g)]
  simp_rw [integral_indicator_const _ (measurableSet_cellD _)]
  have hv : ∀ g : Grid d N, (volume : Measure (UnitAddTorus (Fin d))).real (cellD g) =
      ((N : ℝ) ^ d)⁻¹ := by
    intro g
    rw [Measure.real_def, volume_cellD, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
      Fintype.card_fin, one_div, inv_pow]
  simp only [hv, Complex.real_smul, Finset.mul_sum]
  push_cast
  rfl

theorem coeFn_pcLp (u : Grid d N → ℂ) :
    ((pcLp u : L²(UnitAddTorus (Fin d))) : UnitAddTorus (Fin d) → ℂ) =ᵐ[volume] pc u :=
  (memLp_pc u).coeFn_toLp

theorem coeFn_trigLp (u : Grid d N → ℂ) :
    ((trigLp u : L²(UnitAddTorus (Fin d))) : UnitAddTorus (Fin d) → ℂ) =ᵐ[volume] trigInterp u :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (trigInterp u)

/-- `⟪R^0 v, R^0 u⟫ = N^{-d} Σ_g conj(v g) u g`. -/
theorem inner_pcLp (v u : Grid d N → ℂ) :
    inner ℂ (pcLp v) (pcLp u) = ((N : ℂ) ^ d)⁻¹ * ∑ g, (starRingEnd ℂ) (v g) * u g := by
  rw [L2.inner_def]
  have hae : (fun y => inner ℂ ((pcLp v : UnitAddTorus (Fin d) → ℂ) y)
      ((pcLp u : UnitAddTorus (Fin d) → ℂ) y)) =ᵐ[volume]
      fun y => (fun g => (starRingEnd ℂ) (v g) * u g)
        (TorusPiecewiseConstantTranslation.index N y) := by
    filter_upwards [coeFn_pcLp v, coeFn_pcLp u] with y h1 h2
    rw [h1, h2, RCLike.inner_apply, mul_comm]
    rfl
  rw [integral_congr_ae hae]
  exact integral_comp_index (N := N) (fun g => (starRingEnd ℂ) (v g) * u g)

/-- The DFT as an `L²` pairing of raw reconstructions. -/
theorem dft_eq_inner (u : Grid d N → ℂ) (ℓ : Grid d N) :
    dft u ℓ = inner ℂ (pcLp (fun x => latticeChar ℓ x)) (pcLp u) := by
  rw [inner_pcLp, dft]
  simp only [smul_eq_mul]

theorem mFourierCoeff_eq_inner' (f : L²(UnitAddTorus (Fin d))) (m : Fin d → ℤ) :
    mFourierCoeff f m = inner ℂ (mFourierLp 2 m) f := by
  rw [← mFourierBasis_repr, HilbertBasis.repr_apply_apply, coe_mFourierBasis]

/-- The raw reconstruction of a sampled mode is within `2π |m|₁ / N` of the mode in `L²`. -/
theorem norm_pcLp_mode_sub_le (m : Fin d → ℤ) :
    ‖pcLp (fun x : Grid d N => latticeChar (zcast N m) x) - mFourierLp 2 m‖ ≤
      2 * π * (∑ i, |(m i : ℝ)|) / N := by
  have hae : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin d))),
      ‖(pcLp (fun x : Grid d N => latticeChar (zcast N m) x) - mFourierLp 2 m) y‖ ≤
        2 * π * (∑ i, |(m i : ℝ)|) / N := by
    filter_upwards [Lp.coeFn_sub (pcLp (fun x : Grid d N => latticeChar (zcast N m) x))
      (mFourierLp 2 m), coeFn_pcLp (fun x : Grid d N => latticeChar (zcast N m) x),
      coeFn_mFourierLp 2 m] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, norm_sub_rev]
    simp only [pc]
    rw [← mFourier_samplePt]
    exact mFourier_sub_sample_le m y
  have hC : 0 ≤ 2 * π * (∑ i, |(m i : ℝ)|) / N := by positivity
  refine (Lp.norm_le_of_ae_bound hC hae).trans (le_of_eq ?_)
  simp [measureUnivNNReal]

/-- **Fourier coefficients of raw arrays.**
`|û(m mod N) - f̂(m)| ≤ (2π |m|₁ / N) ‖u‖_{2,h} + ‖R^0 u - f‖_{L²}`. -/
theorem norm_dft_sub_mFourierCoeff_le (u : Grid d N → ℂ) (f : L²(UnitAddTorus (Fin d)))
    (m : Fin d → ℤ) :
    ‖dft u (zcast N m) - mFourierCoeff f m‖ ≤
      2 * π * (∑ i, |(m i : ℝ)|) / N * gridNorm u + ‖pcLp u - f‖ := by
  rw [dft_eq_inner, mFourierCoeff_eq_inner']
  set P := pcLp (fun x : Grid d N => latticeChar (zcast N m) x)
  set E := (mFourierLp 2 m : L²(UnitAddTorus (Fin d)))
  have hsplit : inner ℂ P (pcLp u) - inner ℂ E f =
      inner ℂ (P - E) (pcLp u) + inner ℂ E (pcLp u - f) := by
    rw [inner_sub_left, inner_sub_right]; ring
  have hE : ‖E‖ = 1 := (orthonormal_mFourier (d := Fin d)).1 m
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_pcLp]
    exact mul_le_mul_of_nonneg_right (norm_pcLp_mode_sub_le m) (gridNorm_nonneg _)
  · refine (norm_inner_le_norm _ _).trans ?_
    rw [hE, one_mul]

theorem eventually_two_abs_lt {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (m : Fin d → ℤ) :
    ∀ᶠ k in atTop, ∀ i, 2 * |m i| < n k := by
  rw [Filter.eventually_all]
  intro i
  filter_upwards [hn.eventually_gt_atTop (2 * |m i|).toNat] with k hk
  have := Int.self_le_toNat (2 * |m i|)
  omega

/-- **Strong raw `L²` convergence gives convergence of every fixed Fourier coefficient** of the
trigonometric interpolants. -/
theorem tendsto_coef_of_tendsto_pcLp {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) {u : ∀ k, Grid d (n k) → ℂ} {f : L²(UnitAddTorus (Fin d))}
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0)) (m : Fin d → ℤ) :
    Tendsto (fun k => coef (u k) m) atTop (𝓝 (mFourierCoeff f m)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set c := 2 * π * (∑ i, |(m i : ℝ)|)
  have hn' : Tendsto (fun k => ((n k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hlim : Tendsto (fun k => c / (n k : ℝ) * (‖f‖ + ‖pcLp (u k) - f‖) + ‖pcLp (u k) - f‖)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => c / (n k : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hn'
    have h2 : Tendsto (fun k => ‖f‖ + ‖pcLp (u k) - f‖) atTop (𝓝 (‖f‖ + 0)) :=
      tendsto_const_nhds.add hu
    simpa using (h1.mul h2).add hu
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_two_abs_lt hn m] with k hk
  rw [coef_eq, if_pos (signedRep_zcast hk)]
  refine (norm_dft_sub_mFourierCoeff_le (u k) f m).trans (add_le_add ?_ le_rfl)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← norm_pcLp]
  calc ‖pcLp (u k)‖ = ‖(pcLp (u k) - f) + f‖ := by rw [sub_add_cancel]
    _ ≤ ‖pcLp (u k) - f‖ + ‖f‖ := norm_add_le _ _
    _ = ‖f‖ + ‖pcLp (u k) - f‖ := add_comm _ _

/-- **Raw `L²` convergence implies `ℓ²` convergence of the interpolant coefficients** (the
"vanishing high-frequency tail" step of the manuscript's proof):
`R_h^0 u_h → f` in `L²` gives `Σ_m |coef u_h m - f̂(m)|² → 0`, i.e. `𝓘_h u_h → f` in `L²`. -/
theorem tendsto_tsum_coef_sub_sq {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) {u : ∀ k, Grid d (n k) → ℂ} {f : L²(UnitAddTorus (Fin d))}
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0)) :
    Tendsto (fun k => ∑' m, ‖coef (u k) m - mFourierCoeff f m‖ ^ 2) atTop (𝓝 0) := by
  have hf := KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff f
  refine tendsto_tsum_sq_sub_of_pointwise (fun k => summable_coef_sq _) hf.summable
    (tendsto_coef_of_tendsto_pcLp hn hu) ?_
  rw [hf.tsum_eq]
  simp only [tsum_coef_sq, ← norm_pcLp]
  have : Tendsto (fun k => pcLp (u k)) atTop (𝓝 f) := tendsto_iff_norm_sub_tendsto_zero.2 hu
  exact (this.norm).pow 2

theorem norm_trigLp_sub_sq (u : Grid d N → ℂ) (f : L²(UnitAddTorus (Fin d))) :
    ‖trigLp u - f‖ ^ 2 = ∑' m, ‖coef u m - mFourierCoeff f m‖ ^ 2 := by
  have h := KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff (trigLp u - f)
  rw [← h.tsum_eq]
  congr 1
  funext m
  rw [TorusSobolev.mFourierCoeff_Lp_sub, mFourierCoeff_trigLp]

theorem norm_pcLp_sub_trigLp_le (u : Grid d N → ℂ) :
    ‖pcLp u - trigLp u‖ ≤ Real.sqrt (∑' m, cmpW N m * ‖coef u m‖ ^ 2) := by
  rw [Lp.norm_def]
  have hae : ((pcLp u - trigLp u : L²(UnitAddTorus (Fin d))) : UnitAddTorus (Fin d) → ℂ) =ᵐ[volume]
      fun y => -(trigInterp u y - pc u y) := by
    filter_upwards [Lp.coeFn_sub (pcLp u) (trigLp u), coeFn_pcLp u, coeFn_trigLp u] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    ring
  have hneg : (fun y => -(trigInterp u y - pc u y)) = -(fun y => trigInterp u y - pc u y) := rfl
  rw [eLpNorm_congr_ae hae, hneg, eLpNorm_neg]
  exact ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) (eLpNorm_trigInterp_sub_pc_le u)

/-- **`ℓ²` convergence of the coefficients implies raw `L²` convergence**: if
`Σ_m |coef u_h m - f̂(m)|² → 0` (i.e. `𝓘_h u_h → f` in `L²`), then `R_h^0 u_h → f` in `L²`. -/
theorem tendsto_pcLp_of_tsum_coef {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) {u : ∀ k, Grid d (n k) → ℂ} {f : L²(UnitAddTorus (Fin d))}
    (hc : Tendsto (fun k => ∑' m, ‖coef (u k) m - mFourierCoeff f m‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0) := by
  have hf := (KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff f).summable
  have hn' : Tendsto (fun k => ((n k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  -- the comparison weights tend to zero pointwise
  have hw : ∀ m : Fin d → ℤ, Tendsto (fun k => cmpW (n k) m) atTop (𝓝 0) := by
    intro m
    have h1 : Tendsto (fun k => (2 * π * (∑ i, |(m i : ℝ)|) / (n k : ℝ)) ^ 2) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := 2 * π * (∑ i, |(m i : ℝ)|))).div_atTop hn').pow 2
    exact squeeze_zero (fun k => cmpW_nonneg _ _) (fun k => min_le_right _ _) h1
  have hdom : Tendsto (fun k => ∑' m, cmpW (n k) m * ‖mFourierCoeff f m‖ ^ 2) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (f := fun k m => cmpW (n k) m *
      ‖mFourierCoeff f m‖ ^ 2) (g := fun _ => (0 : ℝ)) (bound := fun m => 4 * ‖mFourierCoeff f m‖ ^ 2)
      (𝓕 := atTop) (hf.mul_left 4) (fun m => by simpa using (hw m).mul_const (‖mFourierCoeff f m‖ ^ 2))
      (Eventually.of_forall fun k m => by
        rw [Real.norm_of_nonneg (mul_nonneg (cmpW_nonneg _ _) (sq_nonneg _))]
        exact mul_le_mul_of_nonneg_right (cmpW_le_four _ _) (sq_nonneg _))
    simpa using h
  have hsumd : ∀ k, Summable fun m => ‖coef (u k) m - mFourierCoeff f m‖ ^ 2 := fun k =>
    summable_norm_sub_sq (summable_coef_sq _) hf
  have hsumw : ∀ k, Summable fun m => cmpW (n k) m * ‖mFourierCoeff f m‖ ^ 2 := fun k =>
    Summable.of_nonneg_of_le (fun m => mul_nonneg (cmpW_nonneg _ _) (sq_nonneg _))
      (fun m => mul_le_mul_of_nonneg_right (cmpW_le_four _ _) (sq_nonneg _)) (hf.mul_left 4)
  have hcmp : ∀ k, ∑' m, cmpW (n k) m * ‖coef (u k) m‖ ^ 2 ≤
      8 * ∑' m, ‖coef (u k) m - mFourierCoeff f m‖ ^ 2 +
        2 * ∑' m, cmpW (n k) m * ‖mFourierCoeff f m‖ ^ 2 := by
    intro k
    rw [← tsum_mul_left, ← tsum_mul_left, ← ((hsumd k).mul_left 8).tsum_add ((hsumw k).mul_left 2)]
    refine Summable.tsum_le_tsum (fun m => ?_) (summable_mul_coef _ _)
      (((hsumd k).mul_left 8).add ((hsumw k).mul_left 2))
    have h1 := norm_sub_sq_le (coef (u k) m - mFourierCoeff f m) (-mFourierCoeff f m)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at h1
    have h4 := cmpW_le_four (n k) m
    have h0 := cmpW_nonneg (n k) m
    nlinarith [sq_nonneg ‖coef (u k) m - mFourierCoeff f m‖, sq_nonneg ‖mFourierCoeff f m‖]
  have hupper : Tendsto (fun k => Real.sqrt (8 * ∑' m, ‖coef (u k) m - mFourierCoeff f m‖ ^ 2 +
      2 * ∑' m, cmpW (n k) m * ‖mFourierCoeff f m‖ ^ 2) +
      Real.sqrt (∑' m, ‖coef (u k) m - mFourierCoeff f m‖ ^ 2)) atTop (𝓝 0) := by
    have h1 := ((hc.const_mul 8).add (hdom.const_mul 2)).sqrt
    have h2 := hc.sqrt
    simpa using h1.add h2
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hupper
  calc ‖pcLp (u k) - f‖ = ‖(pcLp (u k) - trigLp (u k)) + (trigLp (u k) - f)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖pcLp (u k) - trigLp (u k)‖ + ‖trigLp (u k) - f‖ := norm_add_le _ _
    _ ≤ _ := by
        refine add_le_add ((norm_pcLp_sub_trigLp_le (u k)).trans (Real.sqrt_le_sqrt (hcmp k)))
          (le_of_eq ?_)
        rw [← norm_trigLp_sub_sq, Real.sqrt_sq (norm_nonneg _)]

end Coefficients

/-! ### Identification of first jets and strong `H¹` convergence of the interpolants -/

section Identification

open LatticeTorusPlancherel TorusCellEmbedding TorusPiecewiseConstantTranslation

variable {d : ℕ}

theorem sobWeight_mul_eq (m : Fin d → ℤ) (a : ℂ) :
    TorusSobolev.sobWeight m * ‖a‖ ^ 2 =
      ‖a‖ ^ 2 + ∑ μ, ‖(2 * π * Complex.I * m μ : ℂ) * a‖ ^ 2 := by
  have h : ∀ μ, ‖(2 * π * Complex.I * m μ : ℂ) * a‖ ^ 2 = (2 * π * m μ) ^ 2 * ‖a‖ ^ 2 :=
    fun μ => by rw [norm_mul, mul_pow, TorusSobolev.norm_symbol_sq]
  simp only [h]
  unfold TorusSobolev.sobWeight
  rw [add_mul, one_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

/-- **Identification of the limit of forward differences** (Fourier form):
if `R_h^0 u_h → f` and `R_h^0 D⁺_μ u_h → v` strongly in `L²`, then `v̂(m) = 2πi m_μ f̂(m)` for
every `m`, i.e. `v = ∂_μ f` as a distribution on `𝕋^d`. -/
theorem mFourierCoeff_eq_of_tendsto {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) {u : ∀ k, Grid d (n k) → ℂ} {f v : L²(UnitAddTorus (Fin d))}
    {μ : Fin d} (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0))
    (hv : Tendsto (fun k => ‖pcLp (Dp μ (u k)) - v‖) atTop (𝓝 0)) (m : Fin d → ℤ) :
    mFourierCoeff v m = 2 * π * Complex.I * m μ * mFourierCoeff f m := by
  refine tendsto_nhds_unique (tendsto_coef_of_tendsto_pcLp hn hv m) ?_
  simp_rw [coef_Dp]
  exact (tendsto_sym hn μ m).mul (tendsto_coef_of_tendsto_pcLp hn hu m)

/-- Under the hypotheses of the identification, the limit lies in `H¹(𝕋^d)`. -/
theorem memH_one_of_tendsto {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) {u : ∀ k, Grid d (n k) → ℂ} {f : L²(UnitAddTorus (Fin d))}
    {v : Fin d → L²(UnitAddTorus (Fin d))}
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0))
    (hv : ∀ μ, Tendsto (fun k => ‖pcLp (Dp μ (u k)) - v μ‖) atTop (𝓝 0)) :
    TorusSobolev.MemH 1 f := by
  unfold TorusSobolev.MemH TorusSobolev.CoeffMemH
  simp only [Real.rpow_one, sobWeight_mul_eq]
  refine (KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff f).summable.add
    (summable_sum fun μ _ => ?_)
  have h := (KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff (v μ)).summable
  simp only [mFourierCoeff_eq_of_tendsto hn hu (hv μ)] at h
  exact h

/-- **`v_μ = ∂_μ u`**: the strong `L²` limit of `R_h^0 D⁺_μ u_h` is the weak derivative
(`TorusSobolev.weakDeriv`, the Fourier multiplier `2πi m_μ`) of the limit of `R_h^0 u_h`. -/
theorem weakDeriv_eq_of_tendsto {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) {u : ∀ k, Grid d (n k) → ℂ} {f : L²(UnitAddTorus (Fin d))}
    {v : Fin d → L²(UnitAddTorus (Fin d))}
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0))
    (hv : ∀ μ, Tendsto (fun k => ‖pcLp (Dp μ (u k)) - v μ‖) atTop (𝓝 0)) (μ : Fin d) :
    TorusSobolev.weakDeriv μ f = v μ := by
  have hf := memH_one_of_tendsto hn hu hv
  apply mFourierBasis.repr.injective
  ext m
  rw [mFourierBasis_repr, mFourierBasis_repr, TorusSobolev.mFourierCoeff_weakDeriv hf,
    mFourierCoeff_eq_of_tendsto hn hu (hv μ)]

/-- The ratio of the trigonometric to the forward-difference symbol, cut off outside the
represented range. -/
def symRatio (N : ℕ) (μ : Fin d) (m : Fin d → ℤ) : ℂ :=
  if |(m μ : ℝ)| * 2 ≤ N then 2 * π * Complex.I * m μ / sym N μ m else 0

theorem norm_symRatio_le (N : ℕ) (μ : Fin d) (m : Fin d → ℤ) : ‖symRatio N μ m‖ ≤ π / 2 := by
  unfold symRatio
  split_ifs with h
  · rw [norm_div]
    by_cases hs : ‖sym N μ m‖ = 0
    · rw [hs, div_zero]; positivity
    · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs))]
      have h4 := four_mul_abs_le_norm_sym μ h
      have : ‖(2 * π * Complex.I * m μ : ℂ)‖ = 2 * π * |(m μ : ℝ)| := by
        have := TorusSobolev.norm_symbol_sq μ m
        rw [← Real.sqrt_sq (norm_nonneg _), this, Real.sqrt_sq_eq_abs, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      rw [this]
      nlinarith [Real.pi_pos]
  · rw [norm_zero]; positivity

theorem symRatio_mul_coef_Dp {N : ℕ} [NeZero N] (μ : Fin d) (u : Grid d N → ℂ) (m : Fin d → ℤ) :
    symRatio N μ m * coef (Dp μ u) m = 2 * π * Complex.I * m μ * coef u m := by
  by_cases h : coef u m = 0
  · rw [coef_Dp, h]; ring
  have hr := abs_le_of_coef_ne_zero h μ
  rw [coef_Dp, symRatio, if_pos hr]
  by_cases hs : sym N μ m = 0
  · have h4 := four_mul_abs_le_norm_sym μ hr
    rw [hs, norm_zero] at h4
    have : (m μ : ℝ) = 0 := abs_nonpos_iff.1 (by linarith)
    have hm : (m μ : ℂ) = 0 := by exact_mod_cast this
    rw [hs, hm]; ring
  · field_simp

theorem tendsto_symRatio {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (μ : Fin d)
    (m : Fin d → ℤ) :
    Tendsto (fun k => symRatio (n k) μ m) atTop (𝓝 (if m μ = 0 then 0 else 1)) := by
  split_ifs with h0
  · refine tendsto_const_nhds.congr fun k => ?_
    simp [symRatio, h0]
  · have hev : ∀ᶠ k in atTop, |(m μ : ℝ)| * 2 ≤ n k := by
      have := (tendsto_natCast_atTop_atTop.comp hn).eventually_ge_atTop (|(m μ : ℝ)| * 2)
      exact this
    have hne : (2 * π * Complex.I * m μ : ℂ) ≠ 0 := by
      have : (m μ : ℂ) ≠ 0 := by exact_mod_cast h0
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, Complex.I_ne_zero, this]
    have hlim := (tendsto_const_nhds (x := (2 * π * Complex.I * m μ : ℂ))).div
      (tendsto_sym hn μ m) hne
    rw [div_self hne] at hlim
    refine hlim.congr' ?_
    filter_upwards [hev] with k hk
    simp [symRatio, hk]

/-- **Strong `H¹` convergence of the trigonometric interpolants**: if `R_h^0 u_h → f` and
`R_h^0 D⁺_μ u_h → v_μ` strongly in `L²` for every `μ`, then `‖𝓘_h u_h - f‖_{H¹} → 0`. -/
theorem tendsto_sobSq_trigLp_sub {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) {u : ∀ k, Grid d (n k) → ℂ} {f : L²(UnitAddTorus (Fin d))}
    {v : Fin d → L²(UnitAddTorus (Fin d))}
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0))
    (hv : ∀ μ, Tendsto (fun k => ‖pcLp (Dp μ (u k)) - v μ‖) atTop (𝓝 0)) :
    Tendsto (fun k => TorusSobolev.sobSq 1 ⇑(trigLp (u k) - f)) atTop (𝓝 0) := by
  have hf := (KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff f).summable
  have hvs : ∀ μ, Summable fun m => ‖mFourierCoeff (v μ) m‖ ^ 2 := fun μ =>
    (KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff (v μ)).summable
  have hcoef : ∀ k m, mFourierCoeff (⇑(trigLp (u k) - f)) m = coef (u k) m - mFourierCoeff f m :=
    fun k m => by rw [TorusSobolev.mFourierCoeff_Lp_sub, mFourierCoeff_trigLp]
  -- the derivative parts
  have hder : ∀ μ, Tendsto (fun k => ∑' m, ‖(2 * π * Complex.I * m μ : ℂ) * coef (u k) m -
      (2 * π * Complex.I * m μ : ℂ) * mFourierCoeff f m‖ ^ 2) atTop (𝓝 0) := by
    intro μ
    have h1 := tendsto_tsum_coef_sub_sq hn (hv μ)
    have h2 := tendsto_tsum_sq_mul_sub (x := fun k => coef (Dp μ (u k)))
      (x₀ := fun m => mFourierCoeff (v μ) m) (m := fun k => symRatio (n k) μ)
      (m₀ := fun m => if m μ = 0 then 0 else 1) (M := π / 2)
      (fun k => summable_norm_sub_sq (summable_coef_sq _) (hvs μ)) (hvs μ) h1
      (fun k m => norm_symRatio_le _ _ _) (fun m => tendsto_symRatio hn μ m)
    refine h2.congr fun k => ?_
    refine tsum_congr fun m => ?_
    rw [symRatio_mul_coef_Dp, mFourierCoeff_eq_of_tendsto hn hu (hv μ)]
    congr 2
    split_ifs with h0
    · simp [h0]
    · ring
  have hsplit : ∀ k, TorusSobolev.sobSq 1 ⇑(trigLp (u k) - f) =
      ∑' m, ‖coef (u k) m - mFourierCoeff f m‖ ^ 2 + ∑ μ, ∑' m,
        ‖(2 * π * Complex.I * m μ : ℂ) * coef (u k) m -
          (2 * π * Complex.I * m μ : ℂ) * mFourierCoeff f m‖ ^ 2 := by
    intro k
    unfold TorusSobolev.sobSq TorusSobolev.coeffSobSq
    simp only [Real.rpow_one, hcoef, sobWeight_mul_eq, mul_sub]
    have hs0 := summable_norm_sub_sq (summable_coef_sq (u k)) hf
    have hs1 : ∀ μ, Summable fun m => ‖(2 * π * Complex.I * m μ : ℂ) * coef (u k) m -
        (2 * π * Complex.I * m μ : ℂ) * mFourierCoeff f m‖ ^ 2 := by
      intro μ
      refine summable_norm_sub_sq (summable_of_ne_finset_zero
        (s := (univ : Finset (Grid d (n k))).image signedRep) fun m hm => ?_) ?_
      · simp [coef_eq_zero_of_not_mem (u k) hm]
      · have := hvs μ
        simp only [mFourierCoeff_eq_of_tendsto hn hu (hv μ)] at this
        exact this
    rw [hs0.tsum_add (summable_sum fun μ _ => hs1 μ), Summable.tsum_finsetSum fun μ _ => hs1 μ]
  simp only [hsplit]
  simpa using (tendsto_tsum_coef_sub_sq hn hu).add (tendsto_finset_sum _ fun μ _ => hder μ)

end Identification

/-! ### Sampled trigonometric polynomials -/

section Sampled

open LatticeTorusPlancherel TorusCellEmbedding TorusPiecewiseConstantTranslation TorusSobolev

variable {d N : ℕ} [NeZero N]

/-- Grid sampling `𝒮_h P (g) = P(g/N)`. -/
def samp (N : ℕ) (P : C(UnitAddTorus (Fin d), ℂ)) : Grid d N → ℂ := fun g => P (samplePt g)

theorem trigPoly_apply (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (y : UnitAddTorus (Fin d)) :
    trigPoly S c y = ∑ m ∈ S, c m * mFourier m y := by
  simp only [trigPoly, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]

theorem mFourier_samplePt_add_single (m : Fin d → ℤ) (g : Grid d N) (μ : Fin d) :
    mFourier m (samplePt (g + Pi.single μ 1)) =
      mFourier m (samplePt g) * Complex.exp (2 * π * Complex.I * (m μ : ℂ) / N) := by
  rw [mFourier_samplePt, mFourier_samplePt, latticeChar_add_right, latticeChar_single]
  congr 1
  simp only [zcast]
  rw [ZMod.stdAddChar_coe]

theorem Dp_samp_trigPoly (μ : Fin d) (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ)
    (g : Grid d N) :
    Dp μ (samp N (trigPoly S c)) g = ∑ m ∈ S, c m * sym N μ m * mFourier m (samplePt g) := by
  rw [Dp_apply]
  simp only [samp, trigPoly_apply, mFourier_samplePt_add_single, ← Finset.sum_sub_distrib,
    Finset.mul_sum, sym]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- Uniform consistency of sampling: `|R^0 𝒮_h P - P| ≤ Σ_{m ∈ S} |c_m| 2π|m|₁/N`. -/
theorem norm_pc_samp_sub_le (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ)
    (y : UnitAddTorus (Fin d)) :
    ‖pc (samp N (trigPoly S c)) y - trigPoly S c y‖ ≤
      ∑ m ∈ S, ‖c m‖ * (2 * π * (∑ i, |(m i : ℝ)|) / N) := by
  simp only [pc, samp, trigPoly_apply, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [← mul_sub, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_sub_rev]
  exact mFourier_sub_sample_le m y

/-- Uniform consistency of sampled forward differences:
`|R^0 D⁺_μ 𝒮_h P - ∂_μ P| ≤ Σ_{m ∈ S} |c_m| (|sym - 2πi m_μ| + 2π|m_μ| 2π|m|₁/N)`. -/
theorem norm_pc_Dp_samp_sub_le (μ : Fin d) (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ)
    (y : UnitAddTorus (Fin d)) :
    ‖pc (Dp μ (samp N (trigPoly S c))) y -
        trigPoly S (fun m => 2 * π * Complex.I * m μ * c m) y‖ ≤
      ∑ m ∈ S, ‖c m‖ * (‖sym N μ m - 2 * π * Complex.I * m μ‖ +
        2 * π * |(m μ : ℝ)| * (2 * π * (∑ i, |(m i : ℝ)|) / N)) := by
  simp only [pc, Dp_samp_trigPoly, trigPoly_apply, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  set a := mFourier m (samplePt (TorusPiecewiseConstantTranslation.index N y))
  set b := mFourier m y
  have hsplit : c m * sym N μ m * a - 2 * π * Complex.I * m μ * c m * b =
      c m * ((sym N μ m - 2 * π * Complex.I * m μ) * a + 2 * π * Complex.I * m μ * (a - b)) := by
    ring
  rw [hsplit, norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _)
  · rw [norm_mul, TorusSobolev.norm_mFourier_apply, mul_one]
  · rw [norm_mul]
    have hs : ‖(2 * π * Complex.I * m μ : ℂ)‖ = 2 * π * |(m μ : ℝ)| := by
      have := TorusSobolev.norm_symbol_sq μ m
      rw [← Real.sqrt_sq (norm_nonneg _), this, Real.sqrt_sq_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    rw [hs, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (mFourier_sub_sample_le (n := N) m y) (by positivity)

theorem tendsto_bound_samp {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (S : Finset (Fin d → ℤ))
    (c : (Fin d → ℤ) → ℂ) :
    Tendsto (fun k => ∑ m ∈ S, ‖c m‖ * (2 * π * (∑ i, |(m i : ℝ)|) / (n k : ℝ))) atTop (𝓝 0) := by
  have hn' : Tendsto (fun k => ((n k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have := tendsto_finset_sum S fun m _ =>
    ((tendsto_const_nhds (x := 2 * π * (∑ i, |(m i : ℝ)|))).div_atTop hn').const_mul ‖c m‖
  simpa using this

theorem tendsto_bound_Dp_samp {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (μ : Fin d)
    (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    Tendsto (fun k => ∑ m ∈ S, ‖c m‖ * (‖sym (n k) μ m - 2 * π * Complex.I * m μ‖ +
        2 * π * |(m μ : ℝ)| * (2 * π * (∑ i, |(m i : ℝ)|) / (n k : ℝ)))) atTop (𝓝 0) := by
  have hn' : Tendsto (fun k => ((n k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have := tendsto_finset_sum S fun m _ =>
    ((((tendsto_sym hn μ m).sub_const (2 * π * Complex.I * m μ)).norm.add
      (((tendsto_const_nhds (x := 2 * π * (∑ i, |(m i : ℝ)|))).div_atTop hn').const_mul
        (2 * π * |(m μ : ℝ)|))).const_mul ‖c m‖)
  simpa using this

end Sampled

/-! ### The critical endpoint: strong `L⁴` convergence of raw reconstructions in four dimensions -/

section Endpoint

open LatticeTorusPlancherel TorusCellEmbedding TorusPiecewiseConstantTranslation TorusSobolev

variable {d N : ℕ} [NeZero N]

/-- The raw reconstruction is an isometry `L⁴_h → L⁴`. -/
theorem eLpNorm_pc_four (w : Grid d N → ℂ) :
    eLpNorm (pc w) 4 (volume : Measure (UnitAddTorus (Fin d))) =
      ENNReal.ofReal (GridSobolev.gridL4Norm ((N : ℝ)⁻¹) w) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top]
  have h := lintegral_comp_index (d := Fin d) (N := N) fun g => ‖w g‖ₑ ^ ((4 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat] at h ⊢
  change (∫⁻ y, ‖w (TorusPiecewiseConstantTranslation.index N y)‖ₑ ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) = _
  rw [h, GridSobolev.gridL4Norm, Fintype.card_fin]
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have hS : ∀ g, ‖w g‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (‖w g‖ ^ 4) := by
    intro g
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num
  simp_rw [hS]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => by positivity),
    ← ENNReal.ofReal_pow hN, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), one_div (N : ℝ), inv_pow]

theorem memLp_pc_four (w : Grid d N → ℂ) : MemLp (pc w) 4 (volume : Measure (UnitAddTorus (Fin d))) :=
  ⟨(stronglyMeasurable_pc w).aestronglyMeasurable, by rw [eLpNorm_pc_four]; exact ENNReal.ofReal_lt_top⟩

theorem gridL2Norm_eq_gridNorm (w : Grid d N → ℂ) :
    GridSobolev.gridL2Norm ((N : ℝ)⁻¹) w = gridNorm w := by
  have hN : (0 : ℝ) < (N : ℝ)⁻¹ := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  rw [GridSobolev.gridL2Norm_eq hN, gridNorm, Real.sqrt_mul (by positivity), one_div]

/-- **`eq:native-grid-Sobolev-a` on the unit four-torus**:
`‖R^0 w‖_{L⁴} ≤ 3 Σ_μ ‖D⁺_μ w‖_{2,h} + 4 ‖w‖_{2,h}`, uniformly in `N`. -/
theorem eLpNorm_pc_four_le (w : Grid 4 N → ℂ) :
    eLpNorm (pc w) 4 (volume : Measure (UnitAddTorus (Fin 4))) ≤
      ENNReal.ofReal (3 * ∑ μ, gridNorm (Dp μ w) + 4 * gridNorm w) := by
  rw [eLpNorm_pc_four]
  refine ENNReal.ofReal_le_ofReal ?_
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h := GridSobolev.grid_sobolev_L4 (inv_pos.2 hN) (Fintype.card_fin 4) w
  rw [mul_inv_cancel₀ hN.ne', div_one] at h
  simp only [gridL2Norm_eq_gridNorm] at h
  exact h

theorem norm_toLp_sub_toLp (P Q : C(UnitAddTorus (Fin d), ℂ)) :
    ‖ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ P -
      ContinuousMap.toLp (E := ℂ) 2 volume ℂ Q‖ = ‖ContinuousMap.toLp (E := ℂ) 2
        (volume : Measure (UnitAddTorus (Fin d))) ℂ (P - Q)‖ := by
  rw [map_sub]

/-- Fourier coefficients of the truncations used in the endpoint argument. -/
theorem mFourierCoeff_sub_trigPoly (f : L²(UnitAddTorus (Fin d))) (S : Finset (Fin d → ℤ))
    (c : (Fin d → ℤ) → ℂ) (hc : ∀ m ∈ S, c m = mFourierCoeff f m) (m : Fin d → ℤ) :
    mFourierCoeff (⇑(f - ContinuousMap.toLp 2 volume ℂ (trigPoly S c))) m =
      if m ∈ S then 0 else mFourierCoeff f m := by
  rw [mFourierCoeff_Lp_sub, mFourierCoeff_toLp, mFourierCoeff_trigPoly]
  split_ifs with h
  · rw [hc m h, sub_self]
  · rw [sub_zero]

theorem norm_sub_trigPoly_sq (f : L²(UnitAddTorus (Fin d))) (S : Finset (Fin d → ℤ))
    (c : (Fin d → ℤ) → ℂ) (hc : ∀ m ∈ S, c m = mFourierCoeff f m) :
    ‖f - ContinuousMap.toLp 2 volume ℂ (trigPoly S c)‖ ^ 2 =
      ∑' m, ‖mFourierCoeff f m‖ ^ 2 - ∑ m ∈ S, ‖mFourierCoeff f m‖ ^ 2 := by
  have h := KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff
    (f - ContinuousMap.toLp 2 volume ℂ (trigPoly S c))
  rw [← h.tsum_eq]
  simp only [mFourierCoeff_sub_trigPoly f S c hc]
  have := tsum_ite_eq_sub (KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff f).summable S
  rw [← this]
  congr 1; funext m; split_ifs <;> simp

theorem tendsto_norm_sub_trigPoly_box (f : L²(UnitAddTorus (Fin d))) :
    Tendsto (fun R : ℕ => ‖f - ContinuousMap.toLp 2 volume ℂ
      (trigPoly (TorusSobolev.box R) (mFourierCoeff f))‖) atTop (𝓝 0) := by
  have hf := KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff f
  have h1 : Tendsto (fun R : ℕ => ∑ m ∈ TorusSobolev.box R, ‖mFourierCoeff f m‖ ^ 2) atTop
      (𝓝 (∑' m, ‖mFourierCoeff f m‖ ^ 2)) := by
    rw [hf.tsum_eq]
    exact hf.comp tendsto_box
  have h2 : Tendsto (fun R : ℕ => ‖f - ContinuousMap.toLp 2 volume ℂ
      (trigPoly (TorusSobolev.box R) (mFourierCoeff f))‖ ^ 2) atTop (𝓝 0) := by
    simp only [norm_sub_trigPoly_sq f _ _ (fun m _ => rfl)]
    have := (tendsto_const_nhds (x := ∑' m, ‖mFourierCoeff f m‖ ^ 2)).sub h1
    rw [sub_self] at this
    exact this
  have h3 := h2.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h3
  exact h3

end Endpoint

/-! ### The endpoint theorem -/

section EndpointTheorem

open LatticeTorusPlancherel TorusCellEmbedding TorusPiecewiseConstantTranslation TorusSobolev

local instance fact_one_le_four : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

theorem pcLp_sub {d N : ℕ} [NeZero N] (u v : Grid d N → ℂ) :
    pcLp (u - v) = pcLp u - pcLp v :=
  (memLp_pc u).toLp_sub (memLp_pc v)

theorem norm_pcLp_sub_toLp_le {d N : ℕ} [NeZero N] (w : Grid d N → ℂ)
    (P : C(UnitAddTorus (Fin d), ℂ)) {C : ℝ} (hC : 0 ≤ C) (h : ∀ y, ‖pc w y - P y‖ ≤ C) :
    ‖pcLp w - ContinuousMap.toLp 2 volume ℂ P‖ ≤ C := by
  have hae : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin d))),
      ‖(pcLp w - ContinuousMap.toLp 2 volume ℂ P) y‖ ≤ C := by
    filter_upwards [Lp.coeFn_sub (pcLp w) (ContinuousMap.toLp 2 volume ℂ P), coeFn_pcLp w,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume P] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    exact h y
  refine (Lp.norm_le_of_ae_bound hC hae).trans (le_of_eq ?_)
  simp [measureUnivNNReal]

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- The key estimate behind the endpoint: for any trigonometric polynomial `P` (with derivative
`∂_μ P = D_μ`), eventually
`‖R^0 u_h - P‖_{L⁴} ≤ 3 Σ_μ ‖v_μ - D_μ‖_{L²} + 4 ‖f - P‖_{L²} + ε`
(discrete Sobolev applied to `u_h - 𝒮_h P`, plus sampling consistency). -/
theorem eventually_eLpNorm_four_pc_sub_le (hn : Tendsto n atTop atTop)
    {u : ∀ k, Grid 4 (n k) → ℂ} {f : L²(UnitAddTorus (Fin 4))} {v : Fin 4 → L²(UnitAddTorus (Fin 4))}
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0))
    (hv : ∀ μ, Tendsto (fun k => ‖pcLp (Dp μ (u k)) - v μ‖) atTop (𝓝 0))
    (S : Finset (Fin 4 → ℤ)) (c : (Fin 4 → ℤ) → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, eLpNorm (fun y => pc (u k) y - trigPoly S c y) 4 volume ≤
      ENNReal.ofReal (3 * ∑ μ, ‖v μ - ContinuousMap.toLp 2 volume ℂ
          (trigPoly S (fun m => 2 * π * Complex.I * m μ * c m))‖ +
        4 * ‖f - ContinuousMap.toLp 2 volume ℂ (trigPoly S c)‖ + ε) := by
  set P := trigPoly S c
  set D : Fin 4 → C(UnitAddTorus (Fin 4), ℂ) := fun μ =>
    trigPoly S (fun m => 2 * π * Complex.I * m μ * c m)
  set b : ℕ → ℝ := fun k => ∑ m ∈ S, ‖c m‖ * (2 * π * (∑ i, |(m i : ℝ)|) / (n k : ℝ))
  set bD : Fin 4 → ℕ → ℝ := fun μ k => ∑ m ∈ S, ‖c m‖ * (‖sym (n k) μ m - 2 * π * Complex.I * m μ‖ +
        2 * π * |(m μ : ℝ)| * (2 * π * (∑ i, |(m i : ℝ)|) / (n k : ℝ)))
  have hb0 : ∀ k, 0 ≤ b k := fun k => Finset.sum_nonneg fun m _ => by positivity
  have hbD0 : ∀ μ k, 0 ≤ bD μ k := fun μ k => Finset.sum_nonneg fun m _ => by positivity
  -- the error sequence
  set e : ℕ → ℝ := fun k => 3 * ∑ μ, (‖pcLp (Dp μ (u k)) - v μ‖ + bD μ k) +
    4 * (‖pcLp (u k) - f‖ + b k) + b k
  have he : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ∑ μ, (‖pcLp (Dp μ (u k)) - v μ‖ + bD μ k)) atTop (𝓝 0) := by
      simpa using tendsto_finset_sum (univ : Finset (Fin 4)) fun μ _ =>
        (hv μ).add (tendsto_bound_Dp_samp hn μ S c)
    have h2 := tendsto_bound_samp hn S c
    simpa using ((h1.const_mul 3).add ((hu.add h2).const_mul 4)).add h2
  filter_upwards [(tendsto_order.1 he).2 ε hε] with k hk
  have hN : NeZero (n k) := inferInstance
  set w := u k - samp (n k) P
  -- splitting
  have hsplit : (fun y => pc (u k) y - P y) = (fun y => pc w y) + fun y => pc (samp (n k) P) y - P y := by
    funext y; simp only [w, pc_sub, Pi.add_apply, Pi.sub_apply]; ring
  have hm1 : AEStronglyMeasurable (fun y => pc w y) (volume : Measure (UnitAddTorus (Fin 4))) :=
    (stronglyMeasurable_pc w).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun y => pc (samp (n k) P) y - P y)
      (volume : Measure (UnitAddTorus (Fin 4))) :=
    ((stronglyMeasurable_pc _).aestronglyMeasurable).sub P.continuous.aestronglyMeasurable
  rw [hsplit]
  refine (eLpNorm_add_le hm1 hm2 (by norm_num)).trans ?_
  -- the sampling error
  have hsamp : eLpNorm (fun y => pc (samp (n k) P) y - P y) 4 volume ≤ ENNReal.ofReal (b k) := by
    refine (eLpNorm_le_of_ae_bound (Eventually.of_forall fun y =>
      norm_pc_samp_sub_le S c y)).trans (le_of_eq ?_)
    simp [b]
  -- the discrete Sobolev part
  have hgrad : ∀ μ, gridNorm (Dp μ w) ≤ ‖pcLp (Dp μ (u k)) - v μ‖ +
      ‖v μ - ContinuousMap.toLp 2 volume ℂ (D μ)‖ + bD μ k := by
    intro μ
    rw [← norm_pcLp, Dp_sub, pcLp_sub]
    have h3 : ‖pcLp (Dp μ (samp (n k) P)) - ContinuousMap.toLp 2 volume ℂ (D μ)‖ ≤ bD μ k :=
      norm_pcLp_sub_toLp_le _ _ (hbD0 μ k) fun y => norm_pc_Dp_samp_sub_le μ S c y
    calc ‖pcLp (Dp μ (u k)) - pcLp (Dp μ (samp (n k) P))‖
        = ‖(pcLp (Dp μ (u k)) - v μ) + (v μ - ContinuousMap.toLp 2 volume ℂ (D μ)) -
            (pcLp (Dp μ (samp (n k) P)) - ContinuousMap.toLp 2 volume ℂ (D μ))‖ := by
          congr 1; abel
      _ ≤ ‖pcLp (Dp μ (u k)) - v μ‖ + ‖v μ - ContinuousMap.toLp 2 volume ℂ (D μ)‖ +
            ‖pcLp (Dp μ (samp (n k) P)) - ContinuousMap.toLp 2 volume ℂ (D μ)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add le_rfl h3
  have hval : gridNorm w ≤ ‖pcLp (u k) - f‖ + ‖f - ContinuousMap.toLp 2 volume ℂ P‖ + b k := by
    rw [← norm_pcLp, pcLp_sub]
    have h3 : ‖pcLp (samp (n k) P) - ContinuousMap.toLp 2 volume ℂ P‖ ≤ b k :=
      norm_pcLp_sub_toLp_le _ _ (hb0 k) fun y => norm_pc_samp_sub_le S c y
    calc ‖pcLp (u k) - pcLp (samp (n k) P)‖
        = ‖(pcLp (u k) - f) + (f - ContinuousMap.toLp 2 volume ℂ P) -
            (pcLp (samp (n k) P) - ContinuousMap.toLp 2 volume ℂ P)‖ := by
          congr 1; abel
      _ ≤ ‖pcLp (u k) - f‖ + ‖f - ContinuousMap.toLp 2 volume ℂ P‖ +
            ‖pcLp (samp (n k) P) - ContinuousMap.toLp 2 volume ℂ P‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add le_rfl h3
  have hsob := eLpNorm_pc_four_le w
  have hsum : 3 * ∑ μ, gridNorm (Dp μ w) + 4 * gridNorm w + b k ≤
      3 * ∑ μ, ‖v μ - ContinuousMap.toLp 2 volume ℂ (D μ)‖ +
        4 * ‖f - ContinuousMap.toLp 2 volume ℂ P‖ + ε := by
    have h1 : ∑ μ, gridNorm (Dp μ w) ≤ ∑ μ, ‖v μ - ContinuousMap.toLp 2 volume ℂ (D μ)‖ +
        ∑ μ, (‖pcLp (Dp μ (u k)) - v μ‖ + bD μ k) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun μ _ => by linarith [hgrad μ]
    have hk' : e k < ε := hk
    simp only [e] at hk'
    nlinarith
  calc eLpNorm (fun y => pc w y) 4 volume + eLpNorm (fun y => pc (samp (n k) P) y - P y) 4 volume
      ≤ ENNReal.ofReal (3 * ∑ μ, gridNorm (Dp μ w) + 4 * gridNorm w) + ENNReal.ofReal (b k) :=
        add_le_add hsob hsamp
    _ = ENNReal.ofReal (3 * ∑ μ, gridNorm (Dp μ w) + 4 * gridNorm w + b k) := by
        rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg (by norm_num)
          (Finset.sum_nonneg fun _ _ => gridNorm_nonneg _)) (mul_nonneg (by norm_num)
            (gridNorm_nonneg _))) (hb0 k)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsum

/-- The raw reconstruction as an element of `L⁴(𝕋⁴)`. -/
def pcLp4 {N : ℕ} [NeZero N] (w : Grid 4 N → ℂ) : Lp ℂ 4 (volume : Measure (UnitAddTorus (Fin 4))) :=
  (memLp_pc_four w).toLp _

/-- **The critical endpoint (`lem:native-reconstruction-identification`, last clause).**
On the unit four-torus, if `R_h^0 u_h → f` and `R_h^0 D⁺_μ u_h → v_μ` strongly in `L²` for every
`μ`, then `f ∈ L⁴` and `R_h^0 u_h → f` strongly in `L⁴`.  The proof follows the manuscript:
discrete Sobolev (`GridSobolev.grid_sobolev_L4`) for `u_h - 𝒮_h P` with trigonometric
truncations `P` of `f`; no continuum `H¹ ⊂ L⁴` embedding is used (the sequence is shown to be
Cauchy in `L⁴` and its limit is identified with `f` through `L²`). -/
theorem tendsto_eLpNorm_four_pc (hn : Tendsto n atTop atTop)
    {u : ∀ k, Grid 4 (n k) → ℂ} {f : L²(UnitAddTorus (Fin 4))} {v : Fin 4 → L²(UnitAddTorus (Fin 4))}
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0))
    (hv : ∀ μ, Tendsto (fun k => ‖pcLp (Dp μ (u k)) - v μ‖) atTop (𝓝 0)) :
    MemLp (f : UnitAddTorus (Fin 4) → ℂ) 4 volume ∧
      Tendsto (fun k => eLpNorm (fun y => pc (u k) y - f y) 4 volume) atTop (𝓝 0) := by
  -- the truncations and their defects
  set P : ℕ → C(UnitAddTorus (Fin 4), ℂ) := fun R => trigPoly (TorusSobolev.box R) (mFourierCoeff f)
  have hvc : ∀ μ, (fun m : Fin 4 → ℤ => 2 * π * Complex.I * m μ * mFourierCoeff f m) =
      mFourierCoeff (v μ) := fun μ => funext fun m =>
    (mFourierCoeff_eq_of_tendsto hn hu (hv μ) m).symm
  set δ : ℕ → ℝ := fun R => 3 * ∑ μ, ‖v μ - ContinuousMap.toLp 2 volume ℂ
      (trigPoly (TorusSobolev.box R) (fun m => 2 * π * Complex.I * m μ * mFourierCoeff f m))‖ +
    4 * ‖f - ContinuousMap.toLp 2 volume ℂ (P R)‖
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℕ => ∑ μ, ‖v μ - ContinuousMap.toLp 2 volume ℂ
        (trigPoly (TorusSobolev.box R) (fun m => 2 * π * Complex.I * m μ * mFourierCoeff f m))‖)
        atTop (𝓝 0) := by
      simp only [hvc]
      simpa using tendsto_finset_sum (univ : Finset (Fin 4)) fun μ _ =>
        tendsto_norm_sub_trigPoly_box (v μ)
    simpa using (h1.const_mul 3).add ((tendsto_norm_sub_trigPoly_box f).const_mul 4)
  -- distances in `L⁴`
  have hdist : ∀ k R, dist (pcLp4 (u k)) (ContinuousMap.toLp 4 volume ℂ (P R)) =
      (eLpNorm (fun y => pc (u k) y - P R y) 4 volume).toReal := by
    intro k R
    rw [Lp.dist_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [(memLp_pc_four (u k)).coeFn_toLp,
      ContinuousMap.coeFn_toLp (p := 4) (𝕜 := ℂ) volume (P R)] with y h1 h2
    simp only [pcLp4] at *
    rw [Pi.sub_apply, h1, h2]
  have hcauchy : CauchySeq fun k => pcLp4 (u k) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨R, hR⟩ := ((tendsto_order.1 hδ).2 (ε / 4) (by positivity)).exists
    have hev := eventually_eLpNorm_four_pc_sub_le hn hu hv (TorusSobolev.box R) (mFourierCoeff f)
      (ε := ε / 8) (by positivity)
    obtain ⟨K, hK⟩ := eventually_atTop.1 hev
    refine ⟨K, fun a ha b hb => ?_⟩
    have hle : ∀ j ≥ K, dist (pcLp4 (u j)) (ContinuousMap.toLp 4 volume ℂ (P R)) < ε / 2 := by
      intro j hj
      rw [hdist]
      have h := hK j hj
      have hδR : δ R + ε / 8 < ε / 2 := by linarith
      have hpos : 0 ≤ δ R + ε / 8 := by
        have : 0 ≤ δ R := by positivity
        linarith
      calc (eLpNorm (fun y => pc (u j) y - P R y) 4 volume).toReal ≤ δ R + ε / 8 :=
            ENNReal.toReal_le_of_le_ofReal hpos h
        _ < ε / 2 := hδR
    calc dist (pcLp4 (u a)) (pcLp4 (u b))
        ≤ dist (pcLp4 (u a)) (ContinuousMap.toLp 4 volume ℂ (P R)) +
          dist (pcLp4 (u b)) (ContinuousMap.toLp 4 volume ℂ (P R)) := dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hle a ha) (hle b hb)
      _ = ε := by ring
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hw4 : Tendsto (fun k => eLpNorm (fun y => pc (u k) y - w y) 4 volume) atTop (𝓝 0) := by
    have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (f := fun k => pcLp4 (u k)) (f_lim := w)).1 hw
    refine this.congr fun k => eLpNorm_congr_ae ?_
    filter_upwards [(memLp_pc_four (u k)).coeFn_toLp] with y h1
    simp only [pcLp4, Pi.sub_apply]
    rw [h1]
  -- identification of the `L⁴` limit with `f`
  have h2f : Tendsto (fun k => eLpNorm (fun y => pc (u k) y - f y) 2 volume) atTop (𝓝 0) := by
    have : ∀ k, eLpNorm (fun y => pc (u k) y - f y) 2 volume = ENNReal.ofReal ‖pcLp (u k) - f‖ := by
      intro k
      rw [← TorusSobolev.eLpNorm_coe_sub_eq]
      refine eLpNorm_congr_ae ?_
      filter_upwards [coeFn_pcLp (u k)] with y h1
      rw [Pi.sub_apply, h1]
    simp only [this]
    simpa using ENNReal.tendsto_ofReal hu
  have hwf : (w : UnitAddTorus (Fin 4) → ℂ) =ᵐ[volume] (f : UnitAddTorus (Fin 4) → ℂ) := by
    have hmw : AEStronglyMeasurable (w : UnitAddTorus (Fin 4) → ℂ) volume := (Lp.memLp w).1
    have hmf : AEStronglyMeasurable (f : UnitAddTorus (Fin 4) → ℂ) volume := (Lp.memLp f).1
    have hbound : ∀ k, eLpNorm (fun y => w y - f y) 2 volume ≤
        eLpNorm (fun y => pc (u k) y - w y) 4 volume +
          eLpNorm (fun y => pc (u k) y - f y) 2 volume := by
      intro k
      have hpc : AEStronglyMeasurable (pc (u k)) (volume : Measure (UnitAddTorus (Fin 4))) :=
        (stronglyMeasurable_pc _).aestronglyMeasurable
      have e : (fun y => w y - f y) = (fun y => -(pc (u k) y - w y)) + fun y => pc (u k) y - f y := by
        funext y; simp only [Pi.add_apply]; ring
      rw [e]
      refine (eLpNorm_add_le (hpc.sub hmw).neg (hpc.sub hmf) (by norm_num)).trans
        (add_le_add ?_ le_rfl)
      rw [eLpNorm_neg]
      exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hpc.sub hmw)
    have hlim : Tendsto (fun k => eLpNorm (fun y => pc (u k) y - w y) 4 volume +
        eLpNorm (fun y => pc (u k) y - f y) 2 volume) atTop (𝓝 0) := by
      simpa using hw4.add h2f
    have hz : eLpNorm (fun y => w y - f y) 2 volume = 0 :=
      le_antisymm (ge_of_tendsto' hlim hbound) zero_le
    have := (eLpNorm_eq_zero_iff (hmw.sub hmf) (by norm_num)).1 hz
    filter_upwards [this] with y hy
    exact sub_eq_zero.1 hy
  refine ⟨(Lp.memLp w).ae_eq hwf, hw4.congr fun k => eLpNorm_congr_ae ?_⟩
  filter_upwards [hwf] with y hy
  rw [hy]

end EndpointTheorem

/-! ### `lem:native-reconstruction-identification`, assembled -/

section Assembled

open LatticeTorusPlancherel TorusCellEmbedding TorusPiecewiseConstantTranslation TorusSobolev

/-- **`lem:native-reconstruction-identification`** (unit-torus rendering of the odd periodic grids
of side `2π`; the two estimates of `eq:native-reconstruction-comparison` are
`eLpNorm_trigInterp_sub_pc_le_grad` and `sobNorm_trigInterp_le`, valid on every grid).
If `R_h^0 u_h → f` and `R_h^0 D⁺_μ u_h → v_μ` strongly in `L²(𝕋⁴)` for every `μ`, then
`v_μ = ∂_μ f` (weak derivative; `f ∈ H¹`), `𝓘_h^trig u_h → f` strongly in `H¹`, and
`R_h^0 u_h → f` strongly in `L⁴` (with `f ∈ L⁴`). -/
theorem native_reconstruction_identification {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) {u : ∀ k, Grid 4 (n k) → ℂ} {f : L²(UnitAddTorus (Fin 4))}
    {v : Fin 4 → L²(UnitAddTorus (Fin 4))}
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0))
    (hv : ∀ μ, Tendsto (fun k => ‖pcLp (Dp μ (u k)) - v μ‖) atTop (𝓝 0)) :
    (∀ μ, weakDeriv μ f = v μ) ∧ MemH 1 f ∧
      Tendsto (fun k => sobSq 1 ⇑(trigLp (u k) - f)) atTop (𝓝 0) ∧
      MemLp (f : UnitAddTorus (Fin 4) → ℂ) 4 volume ∧
      Tendsto (fun k => eLpNorm (fun y => pc (u k) y - f y) 4 volume) atTop (𝓝 0) :=
  ⟨weakDeriv_eq_of_tendsto hn hu hv, memH_one_of_tendsto hn hu hv,
    tendsto_sobSq_trigLp_sub hn hu hv, (tendsto_eLpNorm_four_pc hn hu hv).1,
    (tendsto_eLpNorm_four_pc hn hu hv).2⟩

/-- Sampled trigonometric polynomials satisfy the hypotheses: `R_h^0 𝒮_h P → P` in `L²`. -/
theorem tendsto_pcLp_samp {d : ℕ} {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    Tendsto (fun k => ‖pcLp (samp (n k) (trigPoly S c)) -
      ContinuousMap.toLp 2 volume ℂ (trigPoly S c)‖) atTop (𝓝 0) :=
  squeeze_zero (fun k => norm_nonneg _)
    (fun k => norm_pcLp_sub_toLp_le _ _ (Finset.sum_nonneg fun m _ => by positivity)
      fun y => norm_pc_samp_sub_le S c y) (tendsto_bound_samp hn S c)

/-- ... and `R_h^0 D⁺_μ 𝒮_h P → ∂_μ P` in `L²`. -/
theorem tendsto_pcLp_Dp_samp {d : ℕ} {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    (μ : Fin d) (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    Tendsto (fun k => ‖pcLp (Dp μ (samp (n k) (trigPoly S c))) -
      ContinuousMap.toLp 2 volume ℂ (trigPoly S (fun m => 2 * π * Complex.I * m μ * c m))‖)
      atTop (𝓝 0) :=
  squeeze_zero (fun k => norm_nonneg _)
    (fun k => norm_pcLp_sub_toLp_le _ _ (Finset.sum_nonneg fun m _ => by positivity)
      fun y => norm_pc_Dp_samp_sub_le μ S c y) (tendsto_bound_Dp_samp hn μ S c)

/-- **Non-vacuity** of `native_reconstruction_identification`: the samples of a single Fourier
mode `e_{m₀}` on the grids `N = k + 1` satisfy its hypotheses, so all its conclusions hold for
them (in particular `R_h^0 𝒮_h e_{m₀} → e_{m₀}` in `L⁴`). -/
example (m₀ : Fin 4 → ℤ) :
    Tendsto (fun k => eLpNorm (fun y => pc (samp (k + 1) (trigPoly {m₀} fun _ => 1)) y -
      (ContinuousMap.toLp 2 volume ℂ (trigPoly {m₀} fun _ => (1 : ℂ))) y) 4 volume)
      atTop (𝓝 0) :=
  (native_reconstruction_identification (n := fun k => k + 1) (tendsto_add_atTop_nat 1)
    (tendsto_pcLp_samp (tendsto_add_atTop_nat 1) {m₀} fun _ => 1)
    (fun μ => tendsto_pcLp_Dp_samp (tendsto_add_atTop_nat 1) μ {m₀} fun _ => 1)).2.2.2.2

end Assembled

end

end RenewalGeometry.TorusTrigReconstruction
