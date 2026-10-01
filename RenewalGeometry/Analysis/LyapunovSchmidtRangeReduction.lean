/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.AnalyticImplicitFunction

/-!
# Lyapunov–Schmidt range reduction for a map with quadratic nonlinearity

General machinery behind `lem:supp-initial-calculus` (Taylor half) and `lem:supp-initial-range`
(nonlinear half) of the emergent-spacetime manuscript.  Everything is stated in arbitrary real
normed spaces with **explicit constants**, so that a family of such data indexed by the cutoff
`h` with uniform constants gives uniform radii and bounds.

## Taylor half

* `norm_sub_le_of_fderiv_bound`: if `‖DN(x)‖ ≤ C ‖x‖` on the ball `B(0, ρ)`, then for
  `‖x‖, ‖y‖ ≤ s < ρ`, `‖N x - N y‖ ≤ C s ‖x - y‖`.
* `norm_le_sq_of_fderiv_bound`: if moreover `N 0 = 0`, then `‖N x‖ ≤ C ‖x‖²`
  (the two bounds `eq:supp-initial-nonlinear-bounds`).
* `taylor_remainder_bounds`: for any `Φ` with `Φ 0 = 0` whose derivative is `K`-Lipschitz at
  `0` on `B(0, ρ)`, the remainder `𝒩 = Φ - DΦ(0)` has derivative `DΦ(x) - DΦ(0)` of norm
  `≤ K ‖x‖` and `‖𝒩 x‖ ≤ K ‖x‖²` ("Taylor's theorem gives eq:supp-initial-nonlinear-bounds").

## Range half

`RangeData` packages: a linear map `L : E → F` (the linearised constraint map `L_h`), a right
inverse `R : F → E` on the range of an idempotent `P` (`P_⊥`, the mean-zero projection; `L R y = y`
when `P y = y`, `P L = L`), a "mean" map `P₀ : F → F₀` with `P₀ L = 0` such that `(P, P₀)` is
jointly injective, and a nonlinearity `N` with `N 0 = 0`, `‖DN x‖ ≤ C ‖x‖` on `B(0, ρ)`;
`a ≥ ‖R‖`, `p ≥ ‖P‖`.  The full map is `𝒞 = L + N`.

* `RangeData.exists_unique_solution`: for radii `σ, δ` satisfying the explicit smallness
  conditions `radiiOK a p C ρ σ δ`, every `z ∈ ker L` with `‖z‖ ≤ δ` has a **unique** `y` with
  `P y = y` (mean-zero), `‖y‖ ≤ σ` and `P 𝒞(z + R y) = 0` (`eq:supp-initial-range-zero`); the
  proof is the paper's: `y = -P N(z + R y)` is a `½`-contraction of the closed mean-zero
  `σ`-ball.
* `RangeData.sol`, `RangeData.norm_sol_le`: the solution `y(z)` satisfies
  `‖y(z)‖ ≤ 2 p C ‖z‖²` (`y_h(z) = O(‖z‖²)`), `RangeData.sol_zero`: `y(0) = 0`.
* `RangeData.meanMap` (`Θ(z) = P₀ 𝒞(z + R y(z))`): `meanMap_zero` (zero constant jet),
  `norm_meanMap_le` (`‖Θ z‖ ≤ ‖P₀‖ C (1 + 2 a p C δ)² ‖z‖²`) and
  `hasFDerivAt_meanMap_zero` (zero linear jet on `ker L`).
* `RangeData.full_zero_of_meanMap_eq_zero`: `Θ(z) = 0` implies `𝒞(z + R y(z)) = 0`, and
  `norm_record_le` bounds the record: `‖z + R y(z)‖ ≤ (1 + 2 a p C δ) ‖z‖`.
* `exists_radiiOK`: admissible radii exist and depend only on `(a, p, C, ρ)`, hence are
  uniform over any family with uniform constants.
-/

open Metric Set Filter Asymptotics
open scoped Topology NNReal

namespace RenewalGeometry
namespace LyapunovSchmidt

variable {E F F₀ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]

/-! ### Taylor half -/

section Taylor

/-- Mean value bound on a ball for a map whose derivative grows at most linearly:
if `‖DN(x)‖ ≤ C ‖x‖` on `B(0, ρ)` and `‖x‖, ‖y‖ ≤ s < ρ`, then
`‖N x - N y‖ ≤ C s ‖x - y‖`. -/
theorem norm_sub_le_of_fderiv_bound {N : E → F} {DN : E → E →L[ℝ] F} {ρ C s : ℝ}
    (hN : ∀ x ∈ ball (0 : E) ρ, HasFDerivAt N (DN x) x)
    (hDN : ∀ x ∈ ball (0 : E) ρ, ‖DN x‖ ≤ C * ‖x‖) (hC : 0 ≤ C) (hs : s < ρ)
    {x y : E} (hx : ‖x‖ ≤ s) (hy : ‖y‖ ≤ s) : ‖N x - N y‖ ≤ C * s * ‖x - y‖ := by
  have hsub : closedBall (0 : E) s ⊆ ball 0 ρ := closedBall_subset_ball hs
  have hbound : ∀ z ∈ closedBall (0 : E) s, ‖DN z‖ ≤ C * s := fun z hz =>
    (hDN z (hsub hz)).trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hC)
  exact (convex_closedBall (0 : E) s).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hN z (hsub hz)).hasFDerivWithinAt) hbound
    (mem_closedBall_zero_iff.mpr hy) (mem_closedBall_zero_iff.mpr hx)

/-- Quadratic bound: if `N 0 = 0` and `‖DN(x)‖ ≤ C ‖x‖` on `B(0, ρ)`, then `‖N x‖ ≤ C ‖x‖²`
on `B(0, ρ)` (first half of `eq:supp-initial-nonlinear-bounds`). -/
theorem norm_le_sq_of_fderiv_bound {N : E → F} {DN : E → E →L[ℝ] F} {ρ C : ℝ}
    (hN : ∀ x ∈ ball (0 : E) ρ, HasFDerivAt N (DN x) x)
    (hDN : ∀ x ∈ ball (0 : E) ρ, ‖DN x‖ ≤ C * ‖x‖) (hC : 0 ≤ C) (h0 : N 0 = 0)
    {x : E} (hx : x ∈ ball (0 : E) ρ) : ‖N x‖ ≤ C * ‖x‖ ^ 2 := by
  have h := norm_sub_le_of_fderiv_bound hN hDN hC (s := ‖x‖) (x := x) (y := 0)
    (mem_ball_zero_iff.mp hx)
    le_rfl (by simp)
  rw [h0, sub_zero, sub_zero] at h
  calc ‖N x‖ ≤ C * ‖x‖ * ‖x‖ := h
    _ = C * ‖x‖ ^ 2 := by ring

/-- **Taylor remainder bounds** ("Taylor's theorem gives `eq:supp-initial-nonlinear-bounds`").
If `Φ 0 = 0` and the derivative of `Φ` satisfies `‖DΦ(x) - DΦ(0)‖ ≤ K ‖x‖` on `B(0, ρ)`, then
the nonlinear remainder `𝒩 = Φ - DΦ(0)` has derivative `DΦ(x) - DΦ(0)` (of norm `≤ K ‖x‖`) and
`‖𝒩(x)‖ ≤ K ‖x‖²` on `B(0, ρ)`. -/
theorem taylor_remainder_bounds {Φ : E → F} {DΦ : E → E →L[ℝ] F} {ρ K : ℝ}
    (hΦ : ∀ x ∈ ball (0 : E) ρ, HasFDerivAt Φ (DΦ x) x)
    (hL : ∀ x ∈ ball (0 : E) ρ, ‖DΦ x - DΦ 0‖ ≤ K * ‖x‖) (hK : 0 ≤ K) (h0 : Φ 0 = 0) :
    (∀ x ∈ ball (0 : E) ρ, HasFDerivAt (fun y => Φ y - DΦ 0 y) (DΦ x - DΦ 0) x) ∧
      (∀ x ∈ ball (0 : E) ρ, ‖Φ x - DΦ 0 x‖ ≤ K * ‖x‖ ^ 2) := by
  have hd : ∀ x ∈ ball (0 : E) ρ, HasFDerivAt (fun y => Φ y - DΦ 0 y) (DΦ x - DΦ 0) x :=
    fun x hx => (hΦ x hx).sub (DΦ 0).hasFDerivAt
  refine ⟨hd, fun x hx => ?_⟩
  exact norm_le_sq_of_fderiv_bound (N := fun y => Φ y - DΦ 0 y) hd hL hK (by simp [h0]) hx

end Taylor

/-! ### Range half -/

/-- The explicit smallness conditions on the radii `σ` (target ball) and `δ` (kernel ball)
for the range contraction, in terms of `a ≥ ‖R‖`, `p ≥ ‖P‖`, the quadratic constant `C` and
the analyticity radius `ρ`. -/
def radiiOK (a p C ρ σ δ : ℝ) : Prop :=
  0 < σ ∧ 0 ≤ δ ∧ δ + a * σ < ρ ∧ p * C * a * (δ + a * σ) ≤ 1 / 2 ∧
    p * C * (δ + a * σ) ^ 2 ≤ σ

/-- **Admissible radii exist, depending only on `(a, p, C, ρ)`.**  In particular they are
uniform over any family (e.g. indexed by the cutoff) with uniform constants. -/
theorem exists_radiiOK {a p C ρ : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hC : 0 ≤ C) (hρ : 0 < ρ) :
    ∃ σ δ, 0 < δ ∧ radiiOK a p C ρ σ δ := by
  set k : ℝ := (p * C + 1) * (1 + a) ^ 2 with hk
  have hk1 : 1 ≤ k := by
    have h1 : 1 ≤ p * C + 1 := by nlinarith [mul_nonneg hp hC]
    have h2 : 1 ≤ (1 + a) ^ 2 := by nlinarith
    nlinarith
  set σ : ℝ := min (ρ / (2 * (1 + a))) (1 / (2 * k)) with hσ
  have hσpos : 0 < σ := lt_min (by positivity) (by positivity)
  have hσ1 : σ ≤ ρ / (2 * (1 + a)) := min_le_left _ _
  have hσ2 : σ ≤ 1 / (2 * k) := min_le_right _ _
  have hs : σ + a * σ = (1 + a) * σ := by ring
  have hs1 : (1 + a) * σ ≤ ρ / 2 := by
    have := mul_le_mul_of_nonneg_left hσ1 (by linarith : (0 : ℝ) ≤ 1 + a)
    calc (1 + a) * σ ≤ (1 + a) * (ρ / (2 * (1 + a))) := this
      _ = ρ / 2 := by field_simp
  have hks : k * σ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hσ2 (by linarith : (0 : ℝ) ≤ k)
    calc k * σ ≤ k * (1 / (2 * k)) := this
      _ = 1 / 2 := by field_simp
  refine ⟨σ, σ, hσpos, hσpos, hσpos.le, by rw [hs]; linarith, ?_, ?_⟩
  · rw [hs]
    have hpC : 0 ≤ p * C := mul_nonneg hp hC
    calc p * C * a * ((1 + a) * σ) = (p * C) * (a * (1 + a)) * σ := by ring
      _ ≤ (p * C + 1) * (1 + a) ^ 2 * σ := by
          apply mul_le_mul_of_nonneg_right _ hσpos.le
          apply mul_le_mul (by linarith) (by nlinarith) (by positivity) (by positivity)
      _ = k * σ := by rw [hk]
      _ ≤ 1 / 2 := hks
  · rw [hs]
    have hpC : 0 ≤ p * C := mul_nonneg hp hC
    calc p * C * ((1 + a) * σ) ^ 2 = (p * C) * (1 + a) ^ 2 * σ * σ := by ring
      _ ≤ k * σ * σ := by
          apply mul_le_mul_of_nonneg_right _ hσpos.le
          apply mul_le_mul_of_nonneg_right _ hσpos.le
          rw [hk]
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 1 / 2 * σ := mul_le_mul_of_nonneg_right hks hσpos.le
      _ ≤ σ := by linarith

/-- Hypothesis packet of the range reduction (`lem:supp-initial-range`, nonlinear half):
`L` linear, `R` a right inverse of `L` on the fixed space of the idempotent `P` (`P_⊥`),
`P L = L`, the mean map `P₀` kills the range of `L` and is jointly injective with `P`, and the
nonlinearity `N` (`𝒩_h`) satisfies the bounds of `eq:supp-initial-nonlinear-bounds` on
`B(0, ρ)`.  The constants `a ≥ ‖R‖`, `p ≥ ‖P‖`, `C` are the uniform constants. -/
structure RangeData (E F F₀ : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] where
  /-- The linearised map `L_h`. -/
  L : E →L[ℝ] F
  /-- The range inverse `R_h`. -/
  R : F →L[ℝ] E
  /-- The projection `P_⊥ = I - P₀` onto the mean-zero targets. -/
  P : F →L[ℝ] F
  /-- The mean map (spatial averaging) `P₀`. -/
  P0 : F →L[ℝ] F₀
  /-- The nonlinear remainder `𝒩_h = 𝒞_h - L_h`. -/
  N : E → F
  /-- Its derivative. -/
  DN : E → E →L[ℝ] F
  /-- Radius of the common ball. -/
  ρ : ℝ
  /-- Quadratic constant. -/
  C : ℝ
  /-- Bound for `‖R‖`. -/
  a : ℝ
  /-- Bound for `‖P‖`. -/
  p : ℝ
  hPP : ∀ w, P (P w) = P w
  hPL : ∀ x, P (L x) = L x
  hLR : ∀ y, P y = y → L (R y) = y
  hP0L : ∀ x, P0 (L x) = 0
  hsplit : ∀ w, P w = 0 → P0 w = 0 → w = 0
  hN : ∀ x ∈ ball (0 : E) ρ, HasFDerivAt N (DN x) x
  hDN : ∀ x ∈ ball (0 : E) ρ, ‖DN x‖ ≤ C * ‖x‖
  hN0 : N 0 = 0
  hC : 0 ≤ C
  ha : ‖R‖ ≤ a
  hp : ‖P‖ ≤ p

namespace RangeData

variable (D : RangeData E F F₀)

/-- The full map `𝒞 = L + N`. -/
def full (x : E) : F := D.L x + D.N x

theorem a_nonneg : 0 ≤ D.a := (norm_nonneg _).trans D.ha

theorem p_nonneg : 0 ≤ D.p := (norm_nonneg _).trans D.hp

/-- The fixed-point map `T_z(y) = -P N(z + R y)` of the range equation. -/
def T (z : E) (y : F) : F := -(D.P (D.N (z + D.R y)))

/-- The closed mean-zero `σ`-ball. -/
def S (σ : ℝ) : Set F := {y | D.P y = y ∧ ‖y‖ ≤ σ}

theorem isClosed_S (σ : ℝ) : IsClosed (D.S σ) := by
  have h1 : IsClosed {y : F | D.P y = y} := isClosed_eq D.P.continuous continuous_id
  have h2 : IsClosed {y : F | ‖y‖ ≤ σ} := isClosed_le continuous_norm continuous_const
  exact h1.inter h2

theorem zero_mem_S {σ : ℝ} (hσ : 0 ≤ σ) : (0 : F) ∈ D.S σ := by
  simp [S, hσ]

/-- The range equation is the fixed-point equation of `T_z`: for `z ∈ ker L` and mean-zero
`y`, `P 𝒞(z + R y) = y + P N(z + R y)`. -/
theorem P_full_eq {z : E} (hz : D.L z = 0) {y : F} (hy : D.P y = y) :
    D.P (D.full (z + D.R y)) = y + D.P (D.N (z + D.R y)) := by
  simp only [full, map_add, hz, D.hLR y hy, zero_add, hy]

theorem norm_arg_le {σ δ : ℝ} {z : E} (hzδ : ‖z‖ ≤ δ) {y : F} (hy : y ∈ D.S σ) :
    ‖z + D.R y‖ ≤ δ + D.a * σ := by
  calc ‖z + D.R y‖ ≤ ‖z‖ + ‖D.R y‖ := norm_add_le _ _
    _ ≤ δ + ‖D.R‖ * ‖y‖ := add_le_add hzδ (D.R.le_opNorm y)
    _ ≤ δ + D.a * σ := by
        gcongr
        · exact D.a_nonneg
        · exact D.ha
        · exact hy.2

theorem mapsTo_T {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z : E} (hzδ : ‖z‖ ≤ δ) :
    MapsTo (D.T z) (D.S σ) (D.S σ) := by
  intro y hy
  obtain ⟨hσ, hδ, hρ, hc, hm⟩ := hr
  have harg := D.norm_arg_le hzδ hy
  have hball : z + D.R y ∈ ball (0 : E) D.ρ := mem_ball_zero_iff.mpr (harg.trans_lt hρ)
  refine ⟨?_, ?_⟩
  · simp only [T, map_neg, D.hPP]
  · have hN := norm_le_sq_of_fderiv_bound D.hN D.hDN D.hC D.hN0 hball
    calc ‖D.T z y‖ = ‖D.P (D.N (z + D.R y))‖ := by simp [T]
      _ ≤ ‖D.P‖ * ‖D.N (z + D.R y)‖ := D.P.le_opNorm _
      _ ≤ D.p * (D.C * (δ + D.a * σ) ^ 2) := by
          gcongr
          · exact D.p_nonneg
          · exact D.hp
          · exact hN.trans (by gcongr; exact D.hC)
      _ ≤ σ := by linarith [hm]

theorem norm_T_sub_le {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z : E} (hzδ : ‖z‖ ≤ δ)
    {y y' : F} (hy : y ∈ D.S σ) (hy' : y' ∈ D.S σ) :
    ‖D.T z y - D.T z y'‖ ≤ 1 / 2 * ‖y - y'‖ := by
  obtain ⟨hσ, hδ, hρ, hc, hm⟩ := hr
  have h1 := D.norm_arg_le hzδ hy
  have h2 := D.norm_arg_le hzδ hy'
  have hlip := norm_sub_le_of_fderiv_bound D.hN D.hDN D.hC hρ h1 h2
  have hR : ‖(z + D.R y) - (z + D.R y')‖ ≤ D.a * ‖y - y'‖ := by
    rw [add_sub_add_left_eq_sub, ← map_sub]
    exact (D.R.le_opNorm _).trans (by gcongr; exact D.ha)
  have hpCs : 0 ≤ D.p * (D.C * (δ + D.a * σ)) := by
    have : 0 ≤ δ + D.a * σ := (norm_nonneg _).trans h1
    exact mul_nonneg D.p_nonneg (mul_nonneg D.hC this)
  calc ‖D.T z y - D.T z y'‖ = ‖D.P (D.N (z + D.R y) - D.N (z + D.R y'))‖ := by
        simp only [T, map_sub]; rw [← norm_neg]; congr 1; abel
    _ ≤ D.p * ‖D.N (z + D.R y) - D.N (z + D.R y')‖ :=
        (D.P.le_opNorm _).trans (by gcongr; exact D.hp)
    _ ≤ D.p * (D.C * (δ + D.a * σ) * (D.a * ‖y - y'‖)) := by
        gcongr
        · exact D.p_nonneg
        · exact hlip.trans (by
            gcongr
            exact mul_nonneg D.hC ((norm_nonneg _).trans h1))
    _ = (D.p * D.C * D.a * (δ + D.a * σ)) * ‖y - y'‖ := by ring
    _ ≤ 1 / 2 * ‖y - y'‖ := by gcongr

/-- **Existence and uniqueness for the nonlinear range equation**
(`eq:supp-initial-range-zero`): for `z ∈ ker L` with `‖z‖ ≤ δ` there is a unique mean-zero
`y` with `‖y‖ ≤ σ` and `P 𝒞(z + R y) = 0`. -/
theorem exists_unique_solution [CompleteSpace F] {σ δ : ℝ}
    (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z : E} (hz : D.L z = 0) (hzδ : ‖z‖ ≤ δ) :
    ∃! y, y ∈ D.S σ ∧ D.P (D.full (z + D.R y)) = 0 := by
  have hσ : 0 < σ := hr.1
  have hmaps := D.mapsTo_T hr hzδ
  have hfix : ∀ y ∈ D.S σ, (D.P (D.full (z + D.R y)) = 0 ↔ D.T z y = y) := by
    intro y hy
    rw [D.P_full_eq hz hy.1, T]
    constructor
    · intro h; rw [add_eq_zero_iff_eq_neg] at h; exact h.symm
    · intro h; rw [add_eq_zero_iff_eq_neg]; exact h.symm
  -- contraction on the complete set `S σ`
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict (D.T z) (D.S σ) (D.S σ)) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have := D.norm_T_sub_le hr hzδ y.2 y'.2
    simpa using this
  obtain ⟨y, hyS, hyfix, -⟩ := hcontr.exists_fixedPoint' (D.isClosed_S σ).isComplete hmaps
    (D.zero_mem_S hσ.le) (edist_ne_top _ _)
  refine ⟨y, ⟨hyS, (hfix y hyS).mpr hyfix⟩, ?_⟩
  rintro y' ⟨hy'S, hy'eq⟩
  have hy'fix : D.T z y' = y' := (hfix y' hy'S).mp hy'eq
  have h := D.norm_T_sub_le hr hzδ hy'S hyS
  rw [hy'fix, show D.T z y = y from hyfix] at h
  have : ‖y' - y‖ = 0 := by linarith [norm_nonneg (y' - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

open scoped Classical in
/-- The range solution `y(z)` (zero outside the admissible domain). -/
noncomputable def sol [CompleteSpace F] (σ δ : ℝ) (z : E) : F :=
  if h : radiiOK D.a D.p D.C D.ρ σ δ ∧ D.L z = 0 ∧ ‖z‖ ≤ δ then
    (D.exists_unique_solution h.1 h.2.1 h.2.2).exists.choose
  else 0

theorem sol_spec [CompleteSpace F] {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z : E}
    (hz : D.L z = 0) (hzδ : ‖z‖ ≤ δ) :
    D.sol σ δ z ∈ D.S σ ∧ D.P (D.full (z + D.R (D.sol σ δ z))) = 0 := by
  have h : radiiOK D.a D.p D.C D.ρ σ δ ∧ D.L z = 0 ∧ ‖z‖ ≤ δ := ⟨hr, hz, hzδ⟩
  rw [sol, dite_cond_eq_true (eq_true h)]
  exact (D.exists_unique_solution h.1 h.2.1 h.2.2).exists.choose_spec

/-- Uniqueness: any mean-zero `y` in the `σ`-ball solving the range equation is `y(z)`. -/
theorem eq_sol [CompleteSpace F] {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z : E}
    (hz : D.L z = 0) (hzδ : ‖z‖ ≤ δ) {y : F} (hy : y ∈ D.S σ)
    (heq : D.P (D.full (z + D.R y)) = 0) : y = D.sol σ δ z :=
  (D.exists_unique_solution hr hz hzδ).unique ⟨hy, heq⟩ (D.sol_spec hr hz hzδ)

/-- `y(0) = 0`. -/
theorem sol_zero [CompleteSpace F] {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) :
    D.sol σ δ 0 = 0 := by
  have hδ : ‖(0 : E)‖ ≤ δ := by simpa using hr.2.1
  refine (D.eq_sol hr (map_zero _) hδ (D.zero_mem_S hr.1.le) ?_).symm
  simp [full, D.hN0]

/-- **`y_h(z) = O(‖z‖²)`**: `‖y(z)‖ ≤ 2 p C ‖z‖²`. -/
theorem norm_sol_le [CompleteSpace F] {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z : E}
    (hz : D.L z = 0) (hzδ : ‖z‖ ≤ δ) : ‖D.sol σ δ z‖ ≤ 2 * D.p * D.C * ‖z‖ ^ 2 := by
  obtain ⟨hyS, hyeq⟩ := D.sol_spec hr hz hzδ
  set y := D.sol σ δ z
  have hfix : D.T z y = y := by
    rw [D.P_full_eq hz hyS.1, add_eq_zero_iff_eq_neg] at hyeq
    rw [T]; exact hyeq.symm
  have hlip := D.norm_T_sub_le hr hzδ hyS (D.zero_mem_S hr.1.le)
  rw [hfix, sub_zero] at hlip
  have hzball : z ∈ ball (0 : E) D.ρ := by
    obtain ⟨hσ, hδ, hρ, -, -⟩ := hr
    have : 0 ≤ D.a * σ := mul_nonneg D.a_nonneg hσ.le
    exact mem_ball_zero_iff.mpr (by linarith)
  have hT0 : ‖D.T z 0‖ ≤ D.p * D.C * ‖z‖ ^ 2 := by
    simp only [T, map_zero, add_zero, norm_neg]
    calc ‖D.P (D.N z)‖ ≤ ‖D.P‖ * ‖D.N z‖ := D.P.le_opNorm _
      _ ≤ D.p * (D.C * ‖z‖ ^ 2) := by
          gcongr
          · exact D.p_nonneg
          · exact D.hp
          · exact norm_le_sq_of_fderiv_bound D.hN D.hDN D.hC D.hN0 hzball
      _ = D.p * D.C * ‖z‖ ^ 2 := by ring
  have : ‖y‖ ≤ ‖y - D.T z 0‖ + ‖D.T z 0‖ := by
    calc ‖y‖ = ‖(y - D.T z 0) + D.T z 0‖ := by abel_nf
      _ ≤ _ := norm_add_le _ _
  linarith

/-- The prepared record `z + R y(z)` is bounded by `(1 + 2 a p C δ) ‖z‖`. -/
theorem norm_record_le [CompleteSpace F] {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z : E}
    (hz : D.L z = 0) (hzδ : ‖z‖ ≤ δ) :
    ‖z + D.R (D.sol σ δ z)‖ ≤ (1 + 2 * D.a * D.p * D.C * δ) * ‖z‖ := by
  have hy := D.norm_sol_le hr hz hzδ
  have hpC : 0 ≤ D.p * D.C := mul_nonneg D.p_nonneg D.hC
  calc ‖z + D.R (D.sol σ δ z)‖ ≤ ‖z‖ + D.a * ‖D.sol σ δ z‖ :=
        (norm_add_le _ _).trans (add_le_add_right
          ((D.R.le_opNorm _).trans (mul_le_mul_of_nonneg_right D.ha (norm_nonneg _))) _)
    _ ≤ ‖z‖ + D.a * (2 * D.p * D.C * ‖z‖ ^ 2) := by gcongr; exact D.a_nonneg
    _ = ‖z‖ + 2 * D.a * (D.p * D.C) * ‖z‖ * ‖z‖ := by ring
    _ ≤ ‖z‖ + 2 * D.a * (D.p * D.C) * δ * ‖z‖ := by
        gcongr
        exact mul_nonneg (mul_nonneg (by norm_num) D.a_nonneg) hpC
    _ = (1 + 2 * D.a * D.p * D.C * δ) * ‖z‖ := by ring

/-- The remaining mean map `Θ(z) = P₀ 𝒞(z + R y(z))`. -/
noncomputable def meanMap [CompleteSpace F] (σ δ : ℝ) (z : E) : F₀ :=
  D.P0 (D.full (z + D.R (D.sol σ δ z)))

theorem meanMap_eq [CompleteSpace F] (σ δ : ℝ) (z : E) :
    D.meanMap σ δ z = D.P0 (D.N (z + D.R (D.sol σ δ z))) := by
  simp [meanMap, full, D.hP0L]

/-- **Zero constant jet** of the mean map: `Θ(0) = 0`. -/
theorem meanMap_zero [CompleteSpace F] {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) :
    D.meanMap σ δ 0 = 0 := by
  rw [meanMap_eq, D.sol_zero hr]; simp [D.hN0]

/-- Quadratic bound for the mean map: `‖Θ(z)‖ ≤ ‖P₀‖ C (1 + 2 a p C δ)² ‖z‖²`. -/
theorem norm_meanMap_le [CompleteSpace F] {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ)
    {z : E} (hz : D.L z = 0) (hzδ : ‖z‖ ≤ δ) :
    ‖D.meanMap σ δ z‖ ≤ ‖D.P0‖ * D.C * (1 + 2 * D.a * D.p * D.C * δ) ^ 2 * ‖z‖ ^ 2 := by
  rw [meanMap_eq]
  have hyS := (D.sol_spec hr hz hzδ).1
  have harg := D.norm_arg_le hzδ hyS
  have hball : z + D.R (D.sol σ δ z) ∈ ball (0 : E) D.ρ :=
    mem_ball_zero_iff.mpr (harg.trans_lt hr.2.2.1)
  have hN := norm_le_sq_of_fderiv_bound D.hN D.hDN D.hC D.hN0 hball
  have hrec := D.norm_record_le hr hz hzδ
  calc ‖D.P0 (D.N (z + D.R (D.sol σ δ z)))‖ ≤ ‖D.P0‖ * ‖D.N (z + D.R (D.sol σ δ z))‖ :=
        D.P0.le_opNorm _
    _ ≤ ‖D.P0‖ * (D.C * ((1 + 2 * D.a * D.p * D.C * δ) * ‖z‖) ^ 2) := by
        gcongr
        exact hN.trans (by gcongr; exact D.hC)
    _ = ‖D.P0‖ * D.C * (1 + 2 * D.a * D.p * D.C * δ) ^ 2 * ‖z‖ ^ 2 := by ring

/-- **Zero linear jet** of the mean map on `ker L`: the restriction of `Θ` to the kernel has
derivative `0` at `0`. -/
theorem hasFDerivAt_meanMap_zero [CompleteSpace F] {σ δ : ℝ}
    (hr : radiiOK D.a D.p D.C D.ρ σ δ) (hδ : 0 < δ) :
    HasFDerivAt (fun z : LinearMap.ker (D.L : E →ₗ[ℝ] F) => D.meanMap σ δ (z : E))
      (0 : _ →L[ℝ] F₀) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, ZeroMemClass.coe_zero, D.meanMap_zero hr, sub_zero,
    ContinuousLinearMap.zero_apply]
  have hO : (fun z : LinearMap.ker (D.L : E →ₗ[ℝ] F) => D.meanMap σ δ (z : E)) =O[𝓝 0]
      (fun z : LinearMap.ker (D.L : E →ₗ[ℝ] F) => ‖z‖ ^ 2) := by
    refine IsBigO.of_bound (‖D.P0‖ * D.C * (1 + 2 * D.a * D.p * D.C * δ) ^ 2) ?_
    filter_upwards [ball_mem_nhds (0 : LinearMap.ker (D.L : E →ₗ[ℝ] F)) hδ] with z hz
    have hz' : ‖(z : E)‖ ≤ δ := by
      have := mem_ball_zero_iff.mp hz
      exact (by simpa using this.le)
    have hzL : D.L z = 0 := z.2
    have := D.norm_meanMap_le hr hzL hz'
    simpa [norm_pow, Submodule.coe_norm] using this
  exact hO.trans_isLittleO (isLittleO_norm_pow_id (by norm_num))

/-- **Complete zero.**  If the mean map vanishes at `z`, the prepared record `z + R y(z)` is an
exact zero of the full map `𝒞 = L + N`. -/
theorem full_zero_of_meanMap_eq_zero [CompleteSpace F] {σ δ : ℝ}
    (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z : E} (hz : D.L z = 0) (hzδ : ‖z‖ ≤ δ)
    (hΘ : D.meanMap σ δ z = 0) : D.full (z + D.R (D.sol σ δ z)) = 0 :=
  D.hsplit _ (D.sol_spec hr hz hzδ).2 hΘ

/-! ### Lipschitz dependence and analyticity of the range solution -/

/-- The solution is a fixed point of `T_z`. -/
theorem T_sol [CompleteSpace F] {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z : E}
    (hz : D.L z = 0) (hzδ : ‖z‖ ≤ δ) : D.T z (D.sol σ δ z) = D.sol σ δ z := by
  obtain ⟨hyS, hyeq⟩ := D.sol_spec hr hz hzδ
  rw [D.P_full_eq hz hyS.1, add_eq_zero_iff_eq_neg] at hyeq
  rw [T]; exact hyeq.symm

/-- **Lipschitz dependence of the range solution on the free record**:
`‖y(z) - y(z')‖ ≤ 2 p C (δ + a σ) ‖z - z'‖`. -/
theorem norm_sol_sub_le [CompleteSpace F] {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ)
    {z z' : E} (hz : D.L z = 0) (hz' : D.L z' = 0) (hzδ : ‖z‖ ≤ δ) (hz'δ : ‖z'‖ ≤ δ) :
    ‖D.sol σ δ z - D.sol σ δ z'‖ ≤ 2 * (D.p * D.C * (δ + D.a * σ)) * ‖z - z'‖ := by
  have hy := (D.sol_spec hr hz hzδ).1
  have hy' := (D.sol_spec hr hz' hz'δ).1
  have hfix := D.T_sol hr hz hzδ
  have hfix' := D.T_sol hr hz' hz'δ
  set y := D.sol σ δ z
  set y' := D.sol σ δ z'
  have h1 := D.norm_T_sub_le hr hzδ hy hy'
  have ha1 := D.norm_arg_le hzδ hy'
  have ha2 := D.norm_arg_le hz'δ hy'
  have hlip := norm_sub_le_of_fderiv_bound D.hN D.hDN D.hC hr.2.2.1 ha1 ha2
  have h2 : ‖D.T z y' - D.T z' y'‖ ≤ D.p * (D.C * (δ + D.a * σ)) * ‖z - z'‖ := by
    calc ‖D.T z y' - D.T z' y'‖ = ‖D.P (D.N (z + D.R y') - D.N (z' + D.R y'))‖ := by
          simp only [T, map_sub]; rw [← norm_neg]; congr 1; abel
      _ ≤ D.p * ‖D.N (z + D.R y') - D.N (z' + D.R y')‖ :=
          (D.P.le_opNorm _).trans (mul_le_mul_of_nonneg_right D.hp (norm_nonneg _))
      _ ≤ D.p * (D.C * (δ + D.a * σ) * ‖z - z'‖) := by
          gcongr
          · exact D.p_nonneg
          · simpa [add_sub_add_right_eq_sub] using hlip
      _ = D.p * (D.C * (δ + D.a * σ)) * ‖z - z'‖ := by ring
  have h3 : ‖y - y'‖ ≤ ‖D.T z y - D.T z y'‖ + ‖D.T z y' - D.T z' y'‖ := by
    calc ‖y - y'‖ = ‖(D.T z y - D.T z y') + (D.T z y' - D.T z' y')‖ := by
          rw [hfix, hfix']; abel_nf
      _ ≤ _ := norm_add_le _ _
  nlinarith

/-- The kernel of `L` (free records). -/
abbrev K : Submodule ℝ E := LinearMap.ker (D.L : E →ₗ[ℝ] F)

/-- The mean-zero subspace `{y | P y = y}`. -/
abbrev M : Submodule ℝ F :=
  LinearMap.ker ((ContinuousLinearMap.id ℝ F - D.P : F →L[ℝ] F) : F →ₗ[ℝ] F)

theorem mem_M {y : F} : y ∈ D.M ↔ D.P y = y := by
  rw [LinearMap.mem_ker]
  change y - D.P y = 0 ↔ _
  rw [sub_eq_zero, eq_comm]

instance instCompleteK [CompleteSpace E] : CompleteSpace D.K :=
  D.L.isClosed_ker.completeSpace_coe

instance instCompleteM [CompleteSpace F] : CompleteSpace D.M :=
  (ContinuousLinearMap.id ℝ F - D.P).isClosed_ker.completeSpace_coe

/-- The corestriction of `P` to the mean-zero subspace. -/
noncomputable def Pc : F →L[ℝ] D.M :=
  D.P.codRestrict D.M (fun w => D.mem_M.mpr (D.hPP w))

theorem coe_Pc (w : F) : (D.Pc w : F) = D.P w := rfl

theorem norm_Pc_le : ‖D.Pc‖ ≤ D.p :=
  ContinuousLinearMap.opNorm_le_bound _ D.p_nonneg fun w => by
    rw [Submodule.coe_norm, coe_Pc]
    exact (D.P.le_opNorm w).trans (mul_le_mul_of_nonneg_right D.hp (norm_nonneg _))

/-- The range solution is continuous on the open `δ`-ball of the kernel. -/
theorem continuousOn_sol [CompleteSpace F] {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) :
    ContinuousOn (fun z : D.K => D.sol σ δ (z : E)) (ball (0 : D.K) δ) := by
  set k : ℝ := 2 * (D.p * D.C * (δ + D.a * σ))
  have hk : 0 ≤ k := by
    have h1 : 0 ≤ δ + D.a * σ := by
      have := mul_nonneg D.a_nonneg hr.1.le
      linarith [hr.2.1]
    have := mul_nonneg (mul_nonneg D.p_nonneg D.hC) h1
    positivity
  refine (LipschitzOnWith.of_dist_le_mul (K := k.toNNReal) fun z hz z' hz' => ?_).continuousOn
  rw [Real.coe_toNNReal _ hk, dist_eq_norm, dist_eq_norm]
  have hzK : D.L z = 0 := LinearMap.mem_ker.mp z.2
  have hz'K : D.L z' = 0 := LinearMap.mem_ker.mp z'.2
  have hzδ : ‖(z : E)‖ ≤ δ := by
    have := mem_ball_zero_iff.mp hz; rw [Submodule.coe_norm] at this; exact this.le
  have hz'δ : ‖(z' : E)‖ ≤ δ := by
    have := mem_ball_zero_iff.mp hz'; rw [Submodule.coe_norm] at this; exact this.le
  have := D.norm_sol_sub_le hr hzK hz'K hzδ hz'δ
  rw [← Submodule.coe_sub, ← Submodule.coe_norm] at this
  exact this

/-- **Analyticity of the range solution** (`lem:supp-initial-range`): if the nonlinearity is
analytic on the ball `B(0, ρ)`, then `z ↦ y(z)` is analytic at every point of the open
`δ`-ball of `ker L`.  Proof: analytic implicit function theorem for
`f(z, y) = P_⊥ (y + N(z + R y))` on `ker L × {P y = y}` (partial derivative
`I + P_⊥ DN R`, at distance `≤ ½` from the identity), identified with `y(z)` through the
continuity of `y` and the local uniqueness of the implicit function. -/
theorem analyticAt_sol [CompleteSpace E] [CompleteSpace F]
    (hNa : ∀ x ∈ ball (0 : E) D.ρ, AnalyticAt ℝ D.N x) {σ δ : ℝ}
    (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z0 : D.K} (hz0 : ‖(z0 : E)‖ < δ) :
    AnalyticAt ℝ (fun z : D.K => D.sol σ δ (z : E)) z0 := by
  have hz0K : D.L z0 = 0 := LinearMap.mem_ker.mp z0.2
  have hsol0 := D.sol_spec hr hz0K hz0.le
  set ι : D.K × D.M →L[ℝ] E := D.K.subtypeL ∘L ContinuousLinearMap.fst ℝ D.K D.M +
    D.R ∘L D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M with hι
  set f : D.K × D.M → D.M := fun v => D.Pc ((v.2 : F) + D.N (ι v)) with hf
  set y0 : D.M := ⟨D.sol σ δ z0, D.mem_M.mpr hsol0.1.1⟩ with hy0
  set u : D.K × D.M := (z0, y0) with hu
  have hιu : ι u = (z0 : E) + D.R (D.sol σ δ z0) := rfl
  have hιball : ι u ∈ ball (0 : E) D.ρ := by
    rw [hιu]; exact mem_ball_zero_iff.mpr ((D.norm_arg_le hz0.le hsol0.1).trans_lt hr.2.2.1)
  have hfa : AnalyticAt ℝ f u := by
    have h1 : AnalyticAt ℝ (fun v : D.K × D.M => (D.M.subtypeL ∘L
        ContinuousLinearMap.snd ℝ D.K D.M) v + D.N (ι v)) u :=
      ((D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M).analyticAt u).add
        ((hNa _ hιball).comp (ι.analyticAt u))
    exact (D.Pc.analyticAt _).comp h1
  have hfd : HasFDerivAt f (D.Pc ∘L (D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M +
      D.DN (ι u) ∘L ι)) u := by
    have h1 : HasFDerivAt (fun v : D.K × D.M => (D.M.subtypeL ∘L
        ContinuousLinearMap.snd ℝ D.K D.M) v + D.N (ι v))
        (D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M + D.DN (ι u) ∘L ι) u :=
      ((D.M.subtypeL ∘L ContinuousLinearMap.snd ℝ D.K D.M).hasFDerivAt).add
        ((D.hN _ hιball).comp u ι.hasFDerivAt)
    exact D.Pc.hasFDerivAt.comp u h1
  set B : D.M →L[ℝ] D.M := D.Pc ∘L D.DN (ι u) ∘L D.R ∘L D.M.subtypeL with hB
  have hpartial : fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ D.K D.M = 1 + B := by
    rw [hfd.fderiv]
    ext y
    have hyM : D.P y = y := D.mem_M.mp y.2
    simp [hι, hB, coe_Pc, hyM]
  have hBnorm : ‖B‖ ≤ 1 / 2 := by
    have hs : ‖ι u‖ ≤ δ + D.a * σ := by rw [hιu]; exact D.norm_arg_le hz0.le hsol0.1
    have hDN : ‖D.DN (ι u)‖ ≤ D.C * (δ + D.a * σ) :=
      (D.hDN _ hιball).trans (mul_le_mul_of_nonneg_left hs D.hC)
    have hsub : ‖D.M.subtypeL‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by simp
    have hs0 : 0 ≤ δ + D.a * σ := (norm_nonneg _).trans hs
    calc ‖B‖ ≤ ‖D.Pc‖ * (‖D.DN (ι u)‖ * (‖D.R‖ * ‖D.M.subtypeL‖)) := by
          rw [hB]
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          gcongr
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ D.p * (D.C * (δ + D.a * σ) * (D.a * 1)) := by
          have i1 : ‖D.R‖ * ‖D.M.subtypeL‖ ≤ D.a * 1 :=
            mul_le_mul D.ha hsub (ContinuousLinearMap.opNorm_nonneg _) D.a_nonneg
          have i2 : ‖D.DN (ι u)‖ * (‖D.R‖ * ‖D.M.subtypeL‖) ≤ D.C * (δ + D.a * σ) * (D.a * 1) :=
            mul_le_mul hDN i1 (by positivity) (mul_nonneg D.hC hs0)
          exact mul_le_mul D.norm_Pc_le i2 (by positivity) D.p_nonneg
      _ = D.p * D.C * D.a * (δ + D.a * σ) := by ring
      _ ≤ 1 / 2 := hr.2.2.2.1
  have hinv : (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ D.K D.M).IsInvertible := by
    rw [hpartial]
    have hlt : ‖-B‖ < 1 := by
      convert (show ‖B‖ < 1 by linarith) using 1
      exact norm_neg B
    refine ⟨ContinuousLinearEquiv.unitsEquiv ℝ D.M (Units.oneSub (-B) hlt), ?_⟩
    ext y
    simp [Units.val_oneSub]
  obtain ⟨ψ, -, hψa, -, hlev, -⟩ := AnalyticImplicit.analytic_implicit_function hfa hinv
  have hball0 : z0 ∈ ball (0 : D.K) δ := by
    rw [mem_ball_zero_iff, Submodule.coe_norm]; exact hz0
  have hcont : ContinuousAt (fun z : D.K => D.sol σ δ (z : E)) z0 :=
    (D.continuousOn_sol hr).continuousAt (isOpen_ball.mem_nhds hball0)
  set φ : D.K → D.K × D.M := fun z => (z, D.Pc (D.sol σ δ (z : E))) with hφ
  have hφu : φ z0 = u := by
    refine Prod.ext rfl (Subtype.ext ?_)
    show D.P (D.sol σ δ z0) = D.sol σ δ z0
    exact hsol0.1.1
  have hT : Tendsto φ (𝓝 z0) (𝓝 u) := by
    rw [← hφu]
    exact (continuousAt_id.prodMk (D.Pc.continuous.continuousAt.comp hcont))
  have hzero : ∀ z : D.K, ‖(z : E)‖ ≤ δ → f (φ z) = 0 ∧ (D.Pc (D.sol σ δ (z : E)) : F) =
      D.sol σ δ (z : E) := by
    intro z hzδ
    have hzK : D.L z = 0 := LinearMap.mem_ker.mp z.2
    have hs := D.sol_spec hr hzK hzδ
    have hPy : (D.Pc (D.sol σ δ (z : E)) : F) = D.sol σ δ (z : E) := hs.1.1
    refine ⟨Subtype.ext ?_, hPy⟩
    have hιz : ι (φ z) = (z : E) + D.R (D.sol σ δ (z : E)) := by
      simp only [hι, hφ, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Submodule.subtypeL_apply,
        hPy]
    have h2 := hs.2
    rw [D.P_full_eq hzK hs.1.1] at h2
    have h3 : (f (φ z) : F) = D.P ((φ z).2 : F) + D.P (D.N (ι (φ z))) := by
      show ((D.Pc (((φ z).2 : F) + D.N (ι (φ z))) : D.M) : F) = _
      rw [coe_Pc, map_add]
    rw [h3, hιz]
    rw [show D.P ((φ z).2 : F) = D.sol σ δ (z : E) by
      simp only [hφ]; rw [hPy]; exact hs.1.1]
    simpa using h2
  have hfu : f u = 0 := by rw [← hφu]; exact (hzero z0 hz0.le).1
  have hev : ∀ᶠ z : D.K in 𝓝 z0, (D.sol σ δ (z : E)) = (ψ z : F) := by
    filter_upwards [hT.eventually hlev, isOpen_ball.mem_nhds hball0] with z hz hzb
    have hzδ : ‖(z : E)‖ ≤ δ := by
      have := mem_ball_zero_iff.mp hzb; rw [Submodule.coe_norm] at this; exact this.le
    obtain ⟨h0, hPy⟩ := hzero z hzδ
    have h4 := hz.mp (by rw [h0, hfu])
    rw [← hPy]
    exact congrArg Subtype.val h4.symm
  exact ((D.M.subtypeL.analyticAt _).comp hψa).congr (by
    filter_upwards [hev] with z hz
    simp [hz])

/-- **Analyticity of the mean map** (`lem:supp-initial-range`): under analyticity of the
nonlinearity, `Θ` is analytic at every point of the open `δ`-ball of `ker L`. -/
theorem analyticAt_meanMap [CompleteSpace E] [CompleteSpace F]
    (hNa : ∀ x ∈ ball (0 : E) D.ρ, AnalyticAt ℝ D.N x) {σ δ : ℝ}
    (hr : radiiOK D.a D.p D.C D.ρ σ δ) {z0 : D.K} (hz0 : ‖(z0 : E)‖ < δ) :
    AnalyticAt ℝ (fun z : D.K => D.meanMap σ δ (z : E)) z0 := by
  have hz0K : D.L z0 = 0 := LinearMap.mem_ker.mp z0.2
  have hsol0 := D.sol_spec hr hz0K hz0.le
  have hball : (z0 : E) + D.R (D.sol σ δ z0) ∈ ball (0 : E) D.ρ :=
    mem_ball_zero_iff.mpr ((D.norm_arg_le hz0.le hsol0.1).trans_lt hr.2.2.1)
  have hin : AnalyticAt ℝ (fun z : D.K => (z : E) + D.R (D.sol σ δ (z : E))) z0 :=
    (D.K.subtypeL.analyticAt z0).add ((D.R.analyticAt _).comp (D.analyticAt_sol hNa hr hz0))
  have h := (D.P0.analyticAt _).comp ((hNa _ hball).comp_of_eq hin rfl)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp [Function.comp, meanMap_eq]

end RangeData

/-- Non-vacuity of the range packet: `E = F = ℝ`, `L = R = P = id`, `P₀ = 0`,
`N(x) = x²` (`DN(x) = 2x`), with constants `ρ = 1`, `C = 2`, `a = p = 1`. -/
noncomputable example : RangeData ℝ ℝ ℝ where
  L := ContinuousLinearMap.id ℝ ℝ
  R := ContinuousLinearMap.id ℝ ℝ
  P := ContinuousLinearMap.id ℝ ℝ
  P0 := 0
  N := fun x => x ^ 2
  DN := fun x => (2 * x) • ContinuousLinearMap.id ℝ ℝ
  ρ := 1
  C := 2
  a := 1
  p := 1
  hPP := fun _ => rfl
  hPL := fun _ => rfl
  hLR := fun _ _ => rfl
  hP0L := fun _ => rfl
  hsplit := fun w h _ => by simpa using h
  hN := fun x _ => ((hasDerivAt_pow 2 x).hasFDerivAt).congr_fderiv (by ext; simp)
  hDN := fun x _ => by
    rw [norm_smul]
    calc ‖2 * x‖ * ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ ‖2 * x‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = 2 * ‖x‖ := by rw [norm_mul]; norm_num
  hN0 := by norm_num
  hC := by norm_num
  ha := ContinuousLinearMap.norm_id_le
  hp := ContinuousLinearMap.norm_id_le

end LyapunovSchmidt
end RenewalGeometry
