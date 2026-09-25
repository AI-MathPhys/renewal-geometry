/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.FiniteHomogeneousStationarityExact

/-!
# Full finite variation controlled by the residual energy
(`lem:supp-homogeneous-euler-control`, `eq:supp-homogeneous-residual`,
`eq:supp-homogeneous-square-factor`, `eq:supp-homogeneous-variation-norm`,
`eq:supp-homogeneous-euler-bound`, `eq:supp-homogeneous-path-control`;
emergent-spacetime manuscript)

For the finite lapse-varied homogeneous action `S_d` of
`RenewalGeometry.Gravity.FiniteHomogeneousStationarityExact` with `B₀ = A₀ ω²`
and a sign `σ ∈ {±1}`, the residuals are
`R_j^σ = q_{j+1} − q_j − σ ω s_j q̄_j` (`residual`) and the residual energy is
`𝓔 = A₀ Σ_{j<M} (R_j^σ)²/s_j` (`residualEnergy`).

* `discreteAction_eq_residualEnergy` (**`eq:supp-homogeneous-square-factor`**):
  `S_d = −𝓔 − A₀ σ ω (q_M² − q_0²)` whenever the `s_j` are nonzero.
* `hasDerivAt_discreteAction_perturbed`: the first variation
  `δS_d[w, s n] = d/dε S_d(q + ε w, s(1 + ε n))|_{ε=0}` for endpoint-vanishing
  `w` equals `firstVariation = −A₀ Σ_j (2 R_j b_j − R_j² n_j/s_j)`, where
  `b_j = (w_{j+1} − w_j)/s_j − σ ω w̄_j − σ ω q̄_j n_j` (`variationRate`) and
  `𝓑_s(w,n;q) = Σ_j s_j b_j²` (`variationNorm`, **`eq:supp-homogeneous-variation-norm`**).
* `abs_firstVariation_le` (**`eq:supp-homogeneous-euler-bound`**):
  `|δS_d[w, s n]| ≤ 2 √(A₀ 𝓔) √𝓑_s + 𝓔 ‖n‖_∞` for any bound `‖n‖_∞ ≥ |n_j|`.
* `path_control_of_recurrence`, `path_control_residualEnergy`
  (**`eq:supp-homogeneous-path-control`**): if `q*` is the exact common-sign
  recurrence with the same `q_0` and `s_j`, `ω s_j/2 ≤ b < 1`, and `q*` stays in
  the positive amplitude range `[q_lo, q_hi]`, then
  `max_{j≤M} |q_j − q*_j| ≤ C √𝓔` with the explicit constant
  `C = q_hi/(q_lo (1 − b)) · √(T/A₀)`, `T = Σ_{j<M} s_j`.

Scoped conventions (as in the parent file): paths are `ℕ → ℝ` sequences, only the
indices `j ≤ M` (resp. `j < M`) enter; the "fixed positive amplitude range" of
the paper is the explicit hypothesis `q_lo ≤ q*_j ≤ q_hi`.
-/

namespace RenewalGeometry.FiniteHomogeneousStationarity

open Real Finset

/-! ### Residuals and the exact square factorization -/

/-- The signed residual `R_j^σ = q_{j+1} − q_j − σ ω s_j q̄_j`
(`eq:supp-homogeneous-residual`). -/
noncomputable def residual (ω σ : ℝ) (q s : ℕ → ℝ) (j : ℕ) : ℝ :=
  q (j + 1) - q j - σ * ω * s j * midAmp q j

/-- The residual energy `𝓔 = A₀ Σ_{j<M} (R_j^σ)²/s_j`. -/
noncomputable def residualEnergy (A₀ ω σ : ℝ) (M : ℕ) (q s : ℕ → ℝ) : ℝ :=
  A₀ * ∑ j ∈ range M, residual ω σ q s j ^ 2 / s j

/-- One edge term of `S_d` with `B₀ = A₀ ω²` is `A₀ R_j²/s_j + A₀ σ ω (q_{j+1}² − q_j²)`. -/
theorem edgeTerm_eq_residual (A₀ ω σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (q s : ℕ → ℝ) (j : ℕ)
    (hs : s j ≠ 0) :
    edgeTerm A₀ (A₀ * ω ^ 2) q s j
      = A₀ * (residual ω σ q s j ^ 2 / s j) + A₀ * σ * ω * (q (j + 1) ^ 2 - q j ^ 2) := by
  unfold edgeTerm residual midAmp
  rcases hσ with rfl | rfl <;> field_simp <;> ring

/-- **`eq:supp-homogeneous-square-factor`**: the exact factorization
`S_d = −A₀ Σ_j (R_j^σ)²/s_j − A₀ σ ω (q_M² − q_0²)`. -/
theorem discreteAction_eq_residualEnergy (A₀ ω σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (M : ℕ)
    (q s : ℕ → ℝ) (hs : ∀ j < M, s j ≠ 0) :
    discreteAction A₀ (A₀ * ω ^ 2) M q s
      = -residualEnergy A₀ ω σ M q s - A₀ * σ * ω * (q M ^ 2 - q 0 ^ 2) := by
  unfold discreteAction residualEnergy
  have h : ∑ j ∈ range M, edgeTerm A₀ (A₀ * ω ^ 2) q s j
      = ∑ j ∈ range M, A₀ * (residual ω σ q s j ^ 2 / s j)
        + A₀ * σ * ω * ∑ j ∈ range M, (q (j + 1) ^ 2 - q j ^ 2) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [edgeTerm_eq_residual A₀ ω σ hσ q s j (hs j (mem_range.mp hj))]
  rw [h, sum_range_sub (fun j => q j ^ 2), mul_sum]
  ring

/-- At fixed endpoints the residual energy is nonnegative when `A₀ ≥ 0` and the
`s_j` are positive. -/
theorem residualEnergy_nonneg (A₀ ω σ : ℝ) (hA : 0 ≤ A₀) (M : ℕ) (q s : ℕ → ℝ)
    (hs : ∀ j < M, 0 < s j) : 0 ≤ residualEnergy A₀ ω σ M q s := by
  unfold residualEnergy
  exact mul_nonneg hA (sum_nonneg fun j hj =>
    div_nonneg (sq_nonneg _) (hs j (mem_range.mp hj)).le)

/-! ### The first variation -/

/-- The variation rate `b_j = (w_{j+1} − w_j)/s_j − σ ω w̄_j − σ ω q̄_j n_j`. -/
noncomputable def variationRate (ω σ : ℝ) (q s w n : ℕ → ℝ) (j : ℕ) : ℝ :=
  (w (j + 1) - w j) / s j - σ * ω * midAmp w j - σ * ω * midAmp q j * n j

/-- The variation norm `𝓑_s(w,n;q) = Σ_{j<M} s_j b_j²`
(`eq:supp-homogeneous-variation-norm`). -/
noncomputable def variationNorm (ω σ : ℝ) (M : ℕ) (q s w n : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range M, s j * variationRate ω σ q s w n j ^ 2

/-- The first variation `δS_d[w, s n] = −A₀ Σ_j (2 R_j b_j − R_j² n_j/s_j)` obtained by
differentiating `eq:supp-homogeneous-square-factor`. -/
noncomputable def firstVariation (A₀ ω σ : ℝ) (M : ℕ) (q s w n : ℕ → ℝ) : ℝ :=
  -A₀ * ∑ j ∈ range M, (2 * residual ω σ q s j * variationRate ω σ q s w n j
    - residual ω σ q s j ^ 2 * n j / s j)

/-- The perturbed nodal path `q + ε w`. -/
noncomputable def perturbedPath (q w : ℕ → ℝ) (ε : ℝ) : ℕ → ℝ := fun j => q j + ε * w j

/-- The perturbed lapse intervals `s (1 + ε n)`, i.e. `δs_j = s_j n_j`. -/
noncomputable def perturbedLapse (s n : ℕ → ℝ) (ε : ℝ) : ℕ → ℝ :=
  fun j => s j + ε * (s j * n j)

/-- Derivative in `ε` at `ε = 0` of one edge term along the perturbation
`(q + ε w, s(1 + ε n))`. -/
theorem hasDerivAt_edgeTerm_perturbed (A₀ B₀ : ℝ) (q s w n : ℕ → ℝ) (j : ℕ)
    (hs : s j ≠ 0) :
    HasDerivAt (fun ε => edgeTerm A₀ B₀ (perturbedPath q w ε) (perturbedLapse s n ε) j)
      (A₀ * (2 * (q (j + 1) - q j) * (w (j + 1) - w j) / s j
          - (q (j + 1) - q j) ^ 2 * n j / s j)
        + B₀ * (s j * n j * midAmp q j ^ 2 + 2 * s j * midAmp q j * midAmp w j)) 0 := by
  have hq : ∀ i, HasDerivAt (fun ε : ℝ => q i + ε * w i) (w i) 0 := fun i => by
    simpa using (hasDerivAt_mul_const (w i)).const_add (q i)
  have hsn : HasDerivAt (fun ε : ℝ => s j + ε * (s j * n j)) (s j * n j) 0 := by
    simpa using (hasDerivAt_mul_const (s j * n j)).const_add (s j)
  have hΔ := (hq (j + 1)).sub (hq j)
  have hnum := (hΔ.pow 2).const_mul A₀
  have hden0 : s j + (0 : ℝ) * (s j * n j) ≠ 0 := by simpa using hs
  have h1 := hnum.div hsn hden0
  have hmid := ((hq j).add (hq (j + 1))).div_const 2
  have h2 := (hsn.const_mul B₀).mul (hmid.pow 2)
  have h := h1.add h2
  have hfun : (fun ε => edgeTerm A₀ B₀ (perturbedPath q w ε) (perturbedLapse s n ε) j)
      = fun ε => A₀ * ((q (j + 1) + ε * w (j + 1)) - (q j + ε * w j)) ^ 2
          / (s j + ε * (s j * n j))
        + B₀ * (s j + ε * (s j * n j))
          * (((q j + ε * w j) + (q (j + 1) + ε * w (j + 1))) / 2) ^ 2 := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [midAmp, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, zero_mul, add_zero,
    Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]
  field_simp

/-- Per-edge identity: the edge derivative equals `A₀(2 R_j b_j − R_j² n_j/s_j)` up to the
telescoping term `2A₀σω(q_{j+1} w_{j+1} − q_j w_j)`. -/
theorem edge_derivative_eq (A₀ ω σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (q s w n : ℕ → ℝ) (j : ℕ)
    (hs : s j ≠ 0) :
    A₀ * (2 * (q (j + 1) - q j) * (w (j + 1) - w j) / s j
          - (q (j + 1) - q j) ^ 2 * n j / s j)
        + A₀ * ω ^ 2 * (s j * n j * midAmp q j ^ 2 + 2 * s j * midAmp q j * midAmp w j)
      = A₀ * (2 * residual ω σ q s j * variationRate ω σ q s w n j
          - residual ω σ q s j ^ 2 * n j / s j)
        + 2 * A₀ * σ * ω * (q (j + 1) * w (j + 1) - q j * w j) := by
  unfold residual variationRate midAmp
  rcases hσ with rfl | rfl <;> field_simp <;> ring

/-- The first variation of `S_d` along `(q + ε w, s(1 + ε n))` with endpoint-vanishing
`w` is `firstVariation` (the derivative of `eq:supp-homogeneous-square-factor`). -/
theorem hasDerivAt_discreteAction_perturbed (A₀ ω σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (M : ℕ)
    (q s w n : ℕ → ℝ) (hs : ∀ j < M, s j ≠ 0) (hw0 : w 0 = 0) (hwM : w M = 0) :
    HasDerivAt
      (fun ε => discreteAction A₀ (A₀ * ω ^ 2) M (perturbedPath q w ε) (perturbedLapse s n ε))
      (firstVariation A₀ ω σ M q s w n) 0 := by
  have hsum := HasDerivAt.fun_sum (u := range M) (x := (0 : ℝ))
    (fun j hj => hasDerivAt_edgeTerm_perturbed A₀ (A₀ * ω ^ 2) q s w n j
      (hs j (mem_range.mp hj)))
  have h := hsum.neg
  have hfun : (fun ε => discreteAction A₀ (A₀ * ω ^ 2) M (perturbedPath q w ε)
      (perturbedLapse s n ε))
      = fun ε => -∑ j ∈ range M,
          edgeTerm A₀ (A₀ * ω ^ 2) (perturbedPath q w ε) (perturbedLapse s n ε) j := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  unfold firstVariation
  rw [sum_congr rfl (fun j hj => edge_derivative_eq A₀ ω σ hσ q s w n j
    (hs j (mem_range.mp hj))), sum_add_distrib, ← mul_sum, ← mul_sum,
    sum_range_sub (fun j => q j * w j), hw0, hwM]
  ring

/-- **`eq:supp-homogeneous-euler-bound`**:
`|δS_d[w, s n]| ≤ 2 √(A₀ 𝓔) √𝓑_s(w,n;q) + 𝓔 ‖n‖_∞`, for any `‖n‖_∞ ≥ |n_j|` (`j < M`). -/
theorem abs_firstVariation_le (A₀ ω σ : ℝ) (hA : 0 ≤ A₀) (M : ℕ) (q s w n : ℕ → ℝ)
    (hs : ∀ j < M, 0 < s j) (ninf : ℝ) (hn : ∀ j < M, |n j| ≤ ninf) :
    |firstVariation A₀ ω σ M q s w n|
      ≤ 2 * √(A₀ * residualEnergy A₀ ω σ M q s) * √(variationNorm ω σ M q s w n)
        + residualEnergy A₀ ω σ M q s * ninf := by
  have hE : residualEnergy A₀ ω σ M q s
      = A₀ * ∑ j ∈ range M, residual ω σ q s j ^ 2 / s j := rfl
  have hB : variationNorm ω σ M q s w n
      = ∑ j ∈ range M, s j * variationRate ω σ q s w n j ^ 2 := rfl
  have hX0 : 0 ≤ ∑ j ∈ range M, |residual ω σ q s j| * |variationRate ω σ q s w n j| :=
    sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hS0 : 0 ≤ ∑ j ∈ range M, residual ω σ q s j ^ 2 / s j :=
    sum_nonneg fun j hj => div_nonneg (sq_nonneg _) (hs j (mem_range.mp hj)).le
  have hB0 : 0 ≤ ∑ j ∈ range M, s j * variationRate ω σ q s w n j ^ 2 :=
    sum_nonneg fun j hj => mul_nonneg (hs j (mem_range.mp hj)).le (sq_nonneg _)
  -- Step 1: triangle inequality term by term.
  have h1 : |firstVariation A₀ ω σ M q s w n|
      ≤ A₀ * (2 * ∑ j ∈ range M, |residual ω σ q s j| * |variationRate ω σ q s w n j|
        + ∑ j ∈ range M, residual ω σ q s j ^ 2 / s j * |n j|) := by
    unfold firstVariation
    rw [abs_mul, abs_neg, abs_of_nonneg hA]
    refine mul_le_mul_of_nonneg_left ?_ hA
    rw [mul_sum, ← sum_add_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
    have hsj := hs j (mem_range.mp hj)
    calc |2 * residual ω σ q s j * variationRate ω σ q s w n j
          - residual ω σ q s j ^ 2 * n j / s j|
        ≤ |2 * residual ω σ q s j * variationRate ω σ q s w n j|
          + |residual ω σ q s j ^ 2 * n j / s j| := abs_sub _ _
      _ = 2 * (|residual ω σ q s j| * |variationRate ω σ q s w n j|)
          + residual ω σ q s j ^ 2 / s j * |n j| := by
          rw [abs_mul, abs_mul, abs_div, abs_mul, abs_two, abs_of_pos hsj, abs_pow, sq_abs]
          ring
  -- Step 2: the sup-norm bound on the lapse variation.
  have h2 : ∑ j ∈ range M, residual ω σ q s j ^ 2 / s j * |n j|
      ≤ (∑ j ∈ range M, residual ω σ q s j ^ 2 / s j) * ninf := by
    rw [sum_mul]
    refine sum_le_sum fun j hj => ?_
    exact mul_le_mul_of_nonneg_left (hn j (mem_range.mp hj))
      (div_nonneg (sq_nonneg _) (hs j (mem_range.mp hj)).le)
  -- Step 3: weighted Cauchy--Schwarz.
  have h3 : (∑ j ∈ range M, |residual ω σ q s j| * |variationRate ω σ q s w n j|) ^ 2
      ≤ (∑ j ∈ range M, residual ω σ q s j ^ 2 / s j)
        * ∑ j ∈ range M, s j * variationRate ω σ q s w n j ^ 2 := by
    have hcs := sum_mul_sq_le_sq_mul_sq (range M)
      (fun j => |residual ω σ q s j| / √(s j))
      (fun j => √(s j) * |variationRate ω σ q s w n j|)
    have e1 : ∀ j ∈ range M, |residual ω σ q s j| / √(s j)
        * (√(s j) * |variationRate ω σ q s w n j|)
        = |residual ω σ q s j| * |variationRate ω σ q s w n j| := fun j hj => by
      have := Real.sqrt_pos.mpr (hs j (mem_range.mp hj))
      field_simp
    have e2 : ∀ j ∈ range M, (|residual ω σ q s j| / √(s j)) ^ 2
        = residual ω σ q s j ^ 2 / s j := fun j hj => by
      rw [div_pow, sq_abs, Real.sq_sqrt (hs j (mem_range.mp hj)).le]
    have e3 : ∀ j ∈ range M, (√(s j) * |variationRate ω σ q s w n j|) ^ 2
        = s j * variationRate ω σ q s w n j ^ 2 := fun j hj => by
      rw [mul_pow, sq_abs, Real.sq_sqrt (hs j (mem_range.mp hj)).le]
    rwa [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at hcs
  -- Step 4: `A₀ X ≤ √(A₀ 𝓔) √𝓑`.
  have h4 : A₀ * ∑ j ∈ range M, |residual ω σ q s j| * |variationRate ω σ q s w n j|
      ≤ √(A₀ * residualEnergy A₀ ω σ M q s) * √(variationNorm ω σ M q s w n) := by
    rw [hE, hB, ← Real.sqrt_mul (mul_nonneg hA (mul_nonneg hA hS0)),
      ← Real.sqrt_sq (mul_nonneg hA hX0)]
    apply Real.sqrt_le_sqrt
    calc (A₀ * ∑ j ∈ range M, |residual ω σ q s j| * |variationRate ω σ q s w n j|) ^ 2
        = A₀ ^ 2 * (∑ j ∈ range M,
            |residual ω σ q s j| * |variationRate ω σ q s w n j|) ^ 2 := by ring
      _ ≤ A₀ ^ 2 * ((∑ j ∈ range M, residual ω σ q s j ^ 2 / s j)
          * ∑ j ∈ range M, s j * variationRate ω σ q s w n j ^ 2) := by gcongr
      _ = A₀ * (A₀ * ∑ j ∈ range M, residual ω σ q s j ^ 2 / s j)
          * ∑ j ∈ range M, s j * variationRate ω σ q s w n j ^ 2 := by ring
  calc |firstVariation A₀ ω σ M q s w n|
      ≤ A₀ * (2 * ∑ j ∈ range M, |residual ω σ q s j| * |variationRate ω σ q s w n j|
        + ∑ j ∈ range M, residual ω σ q s j ^ 2 / s j * |n j|) := h1
    _ = 2 * (A₀ * ∑ j ∈ range M, |residual ω σ q s j| * |variationRate ω σ q s w n j|)
        + A₀ * ∑ j ∈ range M, residual ω σ q s j ^ 2 / s j * |n j| := by ring
    _ ≤ 2 * (√(A₀ * residualEnergy A₀ ω σ M q s) * √(variationNorm ω σ M q s w n))
        + A₀ * ((∑ j ∈ range M, residual ω σ q s j ^ 2 / s j) * ninf) := by
          gcongr
    _ = 2 * √(A₀ * residualEnergy A₀ ω σ M q s) * √(variationNorm ω σ M q s w n)
        + residualEnergy A₀ ω σ M q s * ninf := by rw [hE]; ring

/-! ### Path control by the residual energy -/

/-- One step of the forced recurrence in relative coordinates: with
`q*_{j+1} = q*_j (1 + σωs_j/2)/(1 − σωs_j/2)` and `f_j = (q_j − q*_j)/q*_j`,
`f_{j+1} = f_j + R_j/((1 − σωs_j/2) q*_{j+1})`. -/
theorem relative_error_step (ω σ : ℝ) (q s qs : ℕ → ℝ) (j : ℕ)
    (hd : 1 - σ * ω * s j / 2 ≠ 0) (hqs : qs j ≠ 0) (hqs' : qs (j + 1) ≠ 0)
    (hrec : qs (j + 1) = qs j * ((1 + σ * ω * s j / 2) / (1 - σ * ω * s j / 2))) :
    (q (j + 1) - qs (j + 1)) / qs (j + 1)
      = (q j - qs j) / qs j
        + residual ω σ q s j / ((1 - σ * ω * s j / 2) * qs (j + 1)) := by
  unfold residual midAmp
  have hu : (1 + σ * ω * s j / 2) ≠ 0 := by
    intro h0
    apply hqs'
    rw [hrec, h0]
    simp
  have hd2 : (2 : ℝ) - σ * ω * s j ≠ 0 := by
    intro h0; apply hd; linarith
  have hu2 : (2 : ℝ) + σ * ω * s j ≠ 0 := by
    intro h0; apply hu; linarith
  rw [hrec]
  field_simp
  ring

/-- Iterated relative error: `|f_j| ≤ Σ_{i<j} |R_i| / ((1 − b) q_lo)` for `j ≤ M`. -/
theorem relative_error_le (ω σ b : ℝ) (hω : 0 < ω) (hσ : σ = 1 ∨ σ = -1) (hb : b < 1)
    (M : ℕ) (q s qs : ℕ → ℝ) (hs : ∀ j < M, 0 < s j) (hsb : ∀ j < M, ω * s j / 2 ≤ b)
    (hrec : SatisfiesRecurrence ω σ M qs s) (hq0 : qs 0 = q 0)
    (qlo : ℝ) (hlo : 0 < qlo) (hrange : ∀ j ≤ M, qlo ≤ qs j) :
    ∀ j ≤ M, |(q j - qs j) / qs j|
      ≤ (∑ i ∈ range j, |residual ω σ q s i|) / ((1 - b) * qlo) := by
  intro j
  induction j with
  | zero => intro _; simp [hq0]
  | succ j ih =>
    intro hj
    have hjM : j < M := by omega
    have ihj := ih (by omega)
    have hsj := hs j hjM
    have hsbj := hsb j hjM
    have hxb : σ * ω * s j / 2 ≤ b := by
      rcases hσ with rfl | rfl
      · simpa using hsbj
      · have : 0 ≤ ω * s j / 2 := by positivity
        linarith
    have hd : 0 < 1 - σ * ω * s j / 2 := by linarith
    have hqsj : 0 < qs j := lt_of_lt_of_le hlo (hrange j (by omega))
    have hqsj' : 0 < qs (j + 1) := lt_of_lt_of_le hlo (hrange (j + 1) hj)
    have hstep := relative_error_step ω σ q s qs j hd.ne' hqsj.ne' hqsj'.ne' (hrec j hjM).2
    rw [hstep, sum_range_succ, add_div]
    refine (abs_add_le _ _).trans (add_le_add ihj ?_)
    rw [abs_div, abs_of_pos (mul_pos hd hqsj')]
    refine div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (by linarith) hlo) ?_
    have h1 : 1 - b ≤ 1 - σ * ω * s j / 2 := by linarith
    exact mul_le_mul h1 (hrange (j + 1) hj) hlo.le hd.le

/-- **`eq:supp-homogeneous-path-control`**, raw form: if `q*` is the exact common-sign
recurrence with the same `q_0` and `s_j`, `ω s_j/2 ≤ b < 1`, and `q*` stays in the
positive amplitude range `[q_lo, q_hi]`, then
`|q_j − q*_j| ≤ q_hi/(q_lo(1 − b)) Σ_{i<M} |R_i|` for all `j ≤ M`. -/
theorem path_control_of_recurrence (ω σ b : ℝ) (hω : 0 < ω) (hσ : σ = 1 ∨ σ = -1)
    (hb : b < 1) (M : ℕ) (q s qs : ℕ → ℝ) (hs : ∀ j < M, 0 < s j)
    (hsb : ∀ j < M, ω * s j / 2 ≤ b)
    (hrec : SatisfiesRecurrence ω σ M qs s) (hq0 : qs 0 = q 0)
    (qlo qhi : ℝ) (hlo : 0 < qlo) (hrange : ∀ j ≤ M, qlo ≤ qs j ∧ qs j ≤ qhi) :
    ∀ j ≤ M, |q j - qs j|
      ≤ qhi / (qlo * (1 - b)) * ∑ i ∈ range M, |residual ω σ q s i| := by
  intro j hj
  have hqsj : 0 < qs j := lt_of_lt_of_le hlo (hrange j hj).1
  have hrel := relative_error_le ω σ b hω hσ hb M q s qs hs hsb hrec hq0 qlo hlo
    (fun j hj => (hrange j hj).1) j hj
  have hsub : ∑ i ∈ range j, |residual ω σ q s i| ≤ ∑ i ∈ range M, |residual ω σ q s i| :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hj) (fun i _ _ => abs_nonneg _)
  have h1b : 0 < 1 - b := by linarith
  have hqhi : 0 < qhi := lt_of_lt_of_le hqsj (hrange j hj).2
  calc |q j - qs j| = qs j * |(q j - qs j) / qs j| := by
        rw [abs_div, abs_of_pos hqsj]; field_simp
    _ ≤ qhi * ((∑ i ∈ range M, |residual ω σ q s i|) / ((1 - b) * qlo)) := by
        refine mul_le_mul (hrange j hj).2 (hrel.trans ?_) (abs_nonneg _) hqhi.le
        exact div_le_div_of_nonneg_right hsub (mul_pos h1b hlo).le
    _ = qhi / (qlo * (1 - b)) * ∑ i ∈ range M, |residual ω σ q s i| := by
        field_simp

/-- Cauchy--Schwarz: `Σ_{i<M} |R_i| ≤ √(T Σ_i R_i²/s_i)` with `T = Σ_{i<M} s_i`. -/
theorem sum_abs_residual_le (ω σ : ℝ) (M : ℕ) (q s : ℕ → ℝ) (hs : ∀ j < M, 0 < s j) :
    ∑ i ∈ range M, |residual ω σ q s i|
      ≤ √((∑ i ∈ range M, s i) * ∑ i ∈ range M, residual ω σ q s i ^ 2 / s i) := by
  have hcs := sum_mul_sq_le_sq_mul_sq (range M) (fun i => √(s i))
    (fun i => |residual ω σ q s i| / √(s i))
  have e1 : ∀ i ∈ range M, √(s i) * (|residual ω σ q s i| / √(s i))
      = |residual ω σ q s i| := fun i hi => by
    have := Real.sqrt_pos.mpr (hs i (mem_range.mp hi))
    field_simp
  have e2 : ∀ i ∈ range M, √(s i) ^ 2 = s i := fun i hi =>
    Real.sq_sqrt (hs i (mem_range.mp hi)).le
  have e3 : ∀ i ∈ range M, (|residual ω σ q s i| / √(s i)) ^ 2
      = residual ω σ q s i ^ 2 / s i := fun i hi => by
    rw [div_pow, sq_abs, Real.sq_sqrt (hs i (mem_range.mp hi)).le]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at hcs
  have h0 : 0 ≤ ∑ i ∈ range M, |residual ω σ q s i| := sum_nonneg fun i _ => abs_nonneg _
  rw [← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt hcs

/-- **`eq:supp-homogeneous-path-control`**: `max_{j≤M} |q_j − q*_j| ≤ C √𝓔` with the
explicit constant `C = q_hi/(q_lo(1 − b)) · √(T/A₀)`, `T = Σ_{j<M} s_j`, on the
positive amplitude range `q_lo ≤ q*_j ≤ q_hi`. -/
theorem path_control_residualEnergy (A₀ ω σ b : ℝ) (hA : 0 < A₀) (hω : 0 < ω)
    (hσ : σ = 1 ∨ σ = -1) (hb : b < 1) (M : ℕ) (q s qs : ℕ → ℝ) (hs : ∀ j < M, 0 < s j)
    (hsb : ∀ j < M, ω * s j / 2 ≤ b)
    (hrec : SatisfiesRecurrence ω σ M qs s) (hq0 : qs 0 = q 0)
    (qlo qhi : ℝ) (hlo : 0 < qlo) (hrange : ∀ j ≤ M, qlo ≤ qs j ∧ qs j ≤ qhi) :
    ∀ j ≤ M, |q j - qs j|
      ≤ qhi / (qlo * (1 - b)) * √((∑ i ∈ range M, s i) / A₀)
        * √(residualEnergy A₀ ω σ M q s) := by
  intro j hj
  have hT : 0 ≤ ∑ i ∈ range M, s i := sum_nonneg fun i hi => (hs i (mem_range.mp hi)).le
  have hC : 0 ≤ qhi / (qlo * (1 - b)) := by
    have hqhi : 0 < qhi := lt_of_lt_of_le hlo ((hrange 0 (Nat.zero_le _)).1.trans
      (hrange 0 (Nat.zero_le _)).2)
    have : 0 < 1 - b := by linarith
    positivity
  have hkey : √((∑ i ∈ range M, s i) * ∑ i ∈ range M, residual ω σ q s i ^ 2 / s i)
      = √((∑ i ∈ range M, s i) / A₀) * √(residualEnergy A₀ ω σ M q s) := by
    rw [← Real.sqrt_mul (div_nonneg hT hA.le)]
    congr 1
    unfold residualEnergy
    field_simp
  calc |q j - qs j|
      ≤ qhi / (qlo * (1 - b)) * ∑ i ∈ range M, |residual ω σ q s i| :=
        path_control_of_recurrence ω σ b hω hσ hb M q s qs hs hsb hrec hq0 qlo qhi hlo hrange
          j hj
    _ ≤ qhi / (qlo * (1 - b))
        * √((∑ i ∈ range M, s i) * ∑ i ∈ range M, residual ω σ q s i ^ 2 / s i) :=
        mul_le_mul_of_nonneg_left (sum_abs_residual_le ω σ M q s hs) hC
    _ = qhi / (qlo * (1 - b)) * √((∑ i ∈ range M, s i) / A₀)
        * √(residualEnergy A₀ ω σ M q s) := by rw [hkey, mul_assoc]

end RenewalGeometry.FiniteHomogeneousStationarity
