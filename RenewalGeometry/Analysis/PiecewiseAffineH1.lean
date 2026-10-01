/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.PiecewisePolynomialJetGluing

/-!
# Piecewise-affine paths on a uniform grid and their `H¹` distance

Infrastructure for `thm:main-explicit-operational-family` (emergent-spacetime manuscript):
the "successful piecewise-affine paths converge strongly in `H¹` and uniformly".

For a step `s > 0`, `M ≥ 1` cells and nodal values `q : ℕ → ℝ`, `affineInterp M s q` is the
continuous piecewise-affine interpolant of the values `q j` at the nodes `j s` (built as the
order-`1` glued word of `SplineGluing.splinePath`, extended affinely outside `[0, Ms]`).

* `continuous_affineInterp`: the interpolant is continuous;
* `affineInterp_eq`: on its cell it is `q_j + (τ − j s)(q_{j+1} − q_j)/s`;
* `hasDerivAt_affineInterp`: off the nodes `j s` it is differentiable with derivative the cell
  slope `(q_{j+1} − q_j)/s` — so it is an `H¹` (indeed `W^{1,∞}`) function on `[0, Ms]` whose
  weak derivative is the slope step function;
* `h1DistSq f g a b = ∫_a^b (f − g)² + ∫_a^b (f' − g')²` (with `f' = deriv f`) is the squared
  `H¹(a,b)` distance;
* `affineInterp_sup_le_and_h1DistSq_le`: if on every cell `[j s, (j+1) s]` the two nodal values
  are within `A` of a differentiable `g` and the cell slope is within `B` of `g'`, then
  `|affineInterp − g| ≤ A` on `[0, Ms]` and `h1DistSq (affineInterp) g 0 (Ms) ≤ Ms (A² + B²)`.
-/

open Set Filter Topology MeasureTheory

namespace RenewalGeometry.PiecewiseAffine

open SplineGluing TwoPointHermite

noncomputable section

/-- The uniform nodes `t_j = j s`. -/
def nodeTimes (s : ℝ) : ℕ → ℝ := fun j => j * s

/-- The affine letter of cell `j`: value `q j` and slope `(q (j+1) − q j)/s`. -/
def affineLetters (s : ℝ) (q : ℕ → ℝ) : ℕ → Fin 2 → ℝ := fun j => ![q j, (q (j + 1) - q j) / s]

/-- The continuous piecewise-affine interpolant of the nodal values `q j` at the nodes `j s`. -/
def affineInterp (M : ℕ) (s : ℝ) (q : ℕ → ℝ) : ℝ → ℝ :=
  splinePath (nodeTimes s) M (affineLetters s q) 0

/-- The cell index `j` of a time (`j ≤ M − 1`). -/
def cell (M : ℕ) (s : ℝ) (τ : ℝ) : ℕ := cellIdx (nodeTimes s) M τ

/-- The squared `H¹(a,b)` distance `∫_a^b (f − g)² + ∫_a^b (f' − g')²`. -/
def h1DistSq (f g : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ t in a..b, (f t - g t) ^ 2) + ∫ t in a..b, (deriv f t - deriv g t) ^ 2

theorem nodeTimes_strictMono {s : ℝ} (hs : 0 < s) : StrictMono (nodeTimes s) := by
  intro i j hij
  simp only [nodeTimes]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hs

theorem polyCurveDeriv_zero_two (c : Fin 2 → ℝ) (τ : ℝ) : polyCurveDeriv 0 c τ = c 0 + τ * c 1 := by
  simp [polyCurveDeriv, Fin.sum_univ_two]

theorem polyCurveDeriv_one_two (c : Fin 2 → ℝ) (τ : ℝ) : polyCurveDeriv 1 c τ = c 1 := by
  simp [polyCurveDeriv, Fin.sum_univ_two]

theorem affineInterp_eq (M : ℕ) (s : ℝ) (q : ℕ → ℝ) (τ : ℝ) :
    affineInterp M s q τ
      = q (cell M s τ) + (τ - cell M s τ * s) * ((q (cell M s τ + 1) - q (cell M s τ)) / s) := by
  simp only [affineInterp, splinePath, polyCurveDeriv_zero_two, affineLetters, nodeTimes, cell]
  simp

theorem jetsMatch_affine {s : ℝ} (hs : 0 < s) (M : ℕ) (q : ℕ → ℝ) :
    JetsMatch (nodeTimes s) M (affineLetters s q) 0 := by
  intro j _ k hk
  have hk0 : k = 0 := by omega
  subst hk0
  simp only [polyCurveDeriv_zero_two, affineLetters, nodeTimes]
  simp
  field_simp
  ring

/-- The piecewise-affine interpolant is continuous. -/
theorem continuous_affineInterp {s : ℝ} (hs : 0 < s) (M : ℕ) (q : ℕ → ℝ) :
    Continuous (affineInterp M s q) :=
  continuous_splinePath (nodeTimes_strictMono hs) (jetsMatch_affine hs M q) le_rfl

/-- The cell of a time of `[0, Ms]`: `j < M` and `j s ≤ τ ≤ (j+1) s`. -/
theorem cell_spec {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 1 ≤ M) {τ : ℝ} (h0 : 0 ≤ τ)
    (hT : τ ≤ M * s) :
    cell M s τ < M ∧ (cell M s τ : ℝ) * s ≤ τ ∧ τ ≤ ((cell M s τ : ℝ) + 1) * s := by
  have hle : cell M s τ ≤ M - 1 := cellIdx_le _ _ _
  refine ⟨by omega, ?_, ?_⟩
  · by_cases h : cell M s τ = 0
    · rw [h]; simpa using h0
    · exact cellIdx_spec h
  · by_cases h : cell M s τ + 1 ≤ M - 1
    · have := lt_of_cellIdx (t := nodeTimes s) h
      simp only [nodeTimes] at this
      push_cast at this
      exact this.le
    · have hj : cell M s τ = M - 1 := by omega
      rw [hj]
      have : ((M - 1 : ℕ) : ℝ) + 1 = M := by
        rw [Nat.cast_sub hM]; push_cast; ring
      rw [this]; exact hT

/-- **Derivative off the nodes**: at a time which is not a node `j s`, the interpolant has
derivative the slope `(q_{j+1} − q_j)/s` of its cell. -/
theorem hasDerivAt_affineInterp {s : ℝ} (hs : 0 < s) (M : ℕ) (q : ℕ → ℝ) {τ : ℝ}
    (hτ : ∀ j : ℕ, τ ≠ j * s) :
    HasDerivAt (affineInterp M s q) ((q (cell M s τ + 1) - q (cell M s τ)) / s) τ := by
  have ht := nodeTimes_strictMono hs
  set c := affineLetters s q
  set j := cell M s τ with hjdef
  have hval : affineInterp M s q τ = polyCurveDeriv 0 (c j) (τ - nodeTimes s j) := rfl
  have hder : polyCurveDeriv 1 (c j) (τ - nodeTimes s j) = (q (j + 1) - q j) / s := by
    rw [polyCurveDeriv_one_two]; simp [c, affineLetters]
  have hlet := hasDerivAt_letter (c j) (nodeTimes s j) 0 τ
  rw [hder] at hlet
  have hR : HasDerivWithinAt (affineInterp M s q) ((q (j + 1) - q j) / s) (Ici τ) τ :=
    hlet.hasDerivWithinAt.congr_of_eventuallyEq (eventually_right ht c 0 τ) hval
  have hne : cellIdx (nodeTimes s) M τ = 0 ∨ nodeTimes s (cellIdx (nodeTimes s) M τ) < τ := by
    by_cases h0 : cellIdx (nodeTimes s) M τ = 0
    · exact Or.inl h0
    · right
      exact lt_of_le_of_ne (cellIdx_spec h0) (fun h => hτ _ (by rw [← h]; rfl))
  have hL : HasDerivWithinAt (affineInterp M s q) ((q (j + 1) - q j) / s) (Iic τ) τ :=
    hlet.hasDerivWithinAt.congr_of_eventuallyEq (eventually_left_of_ne ht c 0 hne) hval
  have h := hL.union hR
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h

/-- **Sup and `H¹` bounds for the piecewise-affine interpolant.**  Let `s > 0`, `M ≥ 1`,
`g` differentiable with derivative `g'`.  If on every cell `[j s, (j+1) s]` (`j < M`) both nodal
values are within `A` of `g` and the slope is within `B` of `g'`, then the interpolant is within
`A` of `g` on `[0, Ms]` and `0 ≤ h1DistSq (affineInterp M s q) g 0 (Ms) ≤ Ms (A² + B²)`. -/
theorem affineInterp_sup_le_and_h1DistSq_le {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 1 ≤ M)
    (q : ℕ → ℝ) {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) {A B : ℝ}
    (hA : ∀ j < M, ∀ t ∈ Icc ((j : ℝ) * s) (((j : ℝ) + 1) * s),
      |q j - g t| ≤ A ∧ |q (j + 1) - g t| ≤ A)
    (hB : ∀ j < M, ∀ t ∈ Icc ((j : ℝ) * s) (((j : ℝ) + 1) * s),
      |(q (j + 1) - q j) / s - g' t| ≤ B) :
    (∀ t ∈ Icc 0 (M * s), |affineInterp M s q t - g t| ≤ A) ∧
      0 ≤ h1DistSq (affineInterp M s q) g 0 (M * s) ∧
      h1DistSq (affineInterp M s q) g 0 (M * s) ≤ M * s * (A ^ 2 + B ^ 2) := by
  have hMs : 0 ≤ (M : ℝ) * s := by positivity
  -- the sup bound
  have hsup : ∀ t ∈ Icc 0 (M * s), |affineInterp M s q t - g t| ≤ A := by
    intro t ht
    obtain ⟨hjM, hj1, hj2⟩ := cell_spec hs hM ht.1 ht.2
    set j := cell M s t
    obtain ⟨h1, h2⟩ := hA j hjM t ⟨hj1, hj2⟩
    set θ := (t - j * s) / s with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hs.le
    have hθ1 : θ ≤ 1 := by rw [div_le_one hs]; linarith
    have heq : affineInterp M s q t - g t = (1 - θ) * (q j - g t) + θ * (q (j + 1) - g t) := by
      have hc : cell M s t = j := rfl
      rw [affineInterp_eq, hθ, hc]; field_simp; ring
    rw [heq]
    calc |(1 - θ) * (q j - g t) + θ * (q (j + 1) - g t)|
        ≤ |(1 - θ) * (q j - g t)| + |θ * (q (j + 1) - g t)| := abs_add_le _ _
      _ = (1 - θ) * |q j - g t| + θ * |q (j + 1) - g t| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
      _ ≤ (1 - θ) * A + θ * A := by gcongr
      _ = A := by ring
  -- the derivative bound off the nodes
  have hderiv : ∀ t ∈ Icc 0 (M * s), (∀ j : ℕ, t ≠ j * s) →
      |deriv (affineInterp M s q) t - deriv g t| ≤ B := by
    intro t ht hnode
    obtain ⟨hjM, hj1, hj2⟩ := cell_spec hs hM ht.1 ht.2
    rw [(hasDerivAt_affineInterp hs M q hnode).deriv, (hg t).deriv]
    exact hB _ hjM t ⟨hj1, hj2⟩
  have hnodes : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ range (nodeTimes s) :=
    (countable_range _).ae_notMem _
  have hI1 : ‖∫ t in (0)..(M * s), (affineInterp M s q t - g t) ^ 2‖ ≤ A ^ 2 * |M * s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae (Eventually.of_forall ?_)
    intro t ht
    rw [uIoc_of_le hMs] at ht
    have := hsup t (Ioc_subset_Icc_self ht)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (by linarith [abs_le.1 this]) (abs_le.1 this).2
  have hI2 : ‖∫ t in (0)..(M * s), (deriv (affineInterp M s q) t - deriv g t) ^ 2‖
      ≤ B ^ 2 * |M * s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
    filter_upwards [hnodes] with t hnt ht
    rw [uIoc_of_le hMs] at ht
    have := hderiv t (Ioc_subset_Icc_self ht) (fun j hj => hnt ⟨j, hj.symm⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (by linarith [abs_le.1 this]) (abs_le.1 this).2
  have hn1 : 0 ≤ ∫ t in (0)..(M * s), (affineInterp M s q t - g t) ^ 2 :=
    intervalIntegral.integral_nonneg hMs fun _ _ => sq_nonneg _
  have hn2 : 0 ≤ ∫ t in (0)..(M * s), (deriv (affineInterp M s q) t - deriv g t) ^ 2 :=
    intervalIntegral.integral_nonneg hMs fun _ _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hn1, sub_zero, abs_of_nonneg hMs] at hI1
  rw [Real.norm_eq_abs, abs_of_nonneg hn2, sub_zero, abs_of_nonneg hMs] at hI2
  refine ⟨hsup, add_nonneg hn1 hn2, ?_⟩
  unfold h1DistSq
  nlinarith

end

end RenewalGeometry.PiecewiseAffine
