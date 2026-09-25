/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniform fourth-order multiplier bounds
  (`lem:supp-law-multiplier`, `eq:supp-law-laplacian`,
  `eq:supp-law-domination`, `eq:supp-law-orders`;
  emergent-spacetime manuscript)

## Physical-space domination (`eq:supp-law-domination`)

On a finite periodic grid `G` (the paper's `(hℤ/ℤ)³`, `G = Fin 3 → ZMod N`)
with unit steps `e i`, forward and backward differences
`D_i^+ w = h⁻¹ (S_i w - w)`, `D_i^- w = h⁻¹ (w - S_i^{-1} w)` and the
positive Laplacian `Λ_h = -∑_i D_i^- D_i^+` (`eq:supp-law-laplacian`),
`grid_laplacian_domination` proves
`h² ‖Λ_h w‖_h² ≤ 12 ∑_i ‖D_i^+ w‖_h²` for every array `w` with values in
any normed space, without Fourier analysis: pointwise
`‖a₁ + a₂ + a₃‖² ≤ 3 ∑ ‖a_i‖²`, the backward difference bound
`‖D_i^- v‖_h² ≤ 4 h⁻² ‖v‖_h²` (translation invariance of the grid sum).

## Fourier-side order bounds (`eq:supp-law-orders`)

`symbol_bounds`: the symbol `ℓ_h(k) = 4h⁻² ∑_i sin²(π h k_i)` satisfies
`0 ≤ h² ℓ_h ≤ 12`.  On the mode side the paper's argument is scalar: with
Sobolev norms `‖q‖_{r,h}² = ∑_k (1 + ℓ_k)^r |q̂_k|²` and `Λ_h` acting by
`ℓ_k`, `fourth_order_bounds` proves the four bounds
`h² ‖Λ_h² q‖_{s-1} ≤ 12 ‖q‖_{s+1}`,
`h² ‖Λ_h² q‖_{s-2} ≤ √12 h ‖q‖_{s+1}`,
`h² ‖Λ_h² q‖_{s-3} ≤ h² ‖q‖_{s+1}`,
`h² ‖Λ_h² v‖_{s-3} ≤ √12 h ‖v‖_s`
for every real index `s`, from the bounded ratios
`h²ℓ²/(1+ℓ) ≤ 12`, `h²ℓ²/(1+ℓ)^{3/2} ≤ √12 h`, `h²ℓ²/(1+ℓ)² ≤ h²`.

What is *not* formalised: the finite Fourier transform on the grid
(Parseval) identifying `Λ_h` with the multiplier `ℓ_h`, and the uniform
equivalence of the forward-difference Sobolev norms `eq:supp-open-norms`
with the Fourier weights (`lem:supp-open-calculus`), which the paper's proof
invokes to pass from the mode-side statement to `‖·‖_{r,h}`.
-/

namespace RenewalGeometry
namespace LawMultiplier

open Finset

noncomputable section

/-! ### Physical-space domination -/

section Grid

variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Forward difference `D_i^+ w (x) = h⁻¹ (w (x + e) - w x)` in the step `e`. -/
def forwardDiff (h : ℝ) (e : G) (w : G → F) : G → F :=
  fun x => h⁻¹ • (w (x + e) - w x)

/-- Backward difference `D_i^- w (x) = h⁻¹ (w x - w (x - e))` in the step `e`. -/
def backwardDiff (h : ℝ) (e : G) (w : G → F) : G → F :=
  fun x => h⁻¹ • (w x - w (x - e))

/-- The positive grid Laplacian `Λ_h = -∑_i D_i^- D_i^+`
(`eq:supp-law-laplacian`) for the three unit steps `e i`. -/
def gridLaplacian (h : ℝ) (e : Fin 3 → G) (w : G → F) : G → F :=
  fun x => -∑ i, backwardDiff h (e i) (forwardDiff h (e i) w) x

/-- The squared grid norm `‖w‖_h² = h³ ∑_x ‖w x‖²`. -/
def gridNormSq (h : ℝ) (w : G → F) : ℝ := h ^ 3 * ∑ x, ‖w x‖ ^ 2

omit [AddCommGroup G] [NormedSpace ℝ F] in
theorem gridNormSq_nonneg (h : ℝ) (hh : 0 ≤ h) (w : G → F) : 0 ≤ gridNormSq h w := by
  unfold gridNormSq; positivity

omit [NormedSpace ℝ F] in
/-- Translation invariance of the grid sum. -/
theorem sum_norm_sq_sub (e : G) (v : G → F) :
    ∑ x, ‖v (x - e)‖ ^ 2 = ∑ x, ‖v x‖ ^ 2 :=
  (Equiv.subRight e).sum_comp fun x => ‖v x‖ ^ 2

omit [NormedSpace ℝ F] in
/-- `‖a - b‖² ≤ 2 ‖a‖² + 2 ‖b‖²`. -/
theorem norm_sub_sq_le (a b : F) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 := norm_sub_le a b
  have h2 := norm_nonneg (a - b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- The backward difference bound `∑_x ‖D^- v x‖² ≤ 4 h⁻² ∑_x ‖v x‖²`. -/
theorem sum_backwardDiff_sq_le (h : ℝ) (e : G) (v : G → F) :
    ∑ x, ‖backwardDiff h e v x‖ ^ 2 ≤ 4 * h⁻¹ ^ 2 * ∑ x, ‖v x‖ ^ 2 := by
  have hpt : ∀ x, ‖backwardDiff h e v x‖ ^ 2
      ≤ h⁻¹ ^ 2 * (2 * ‖v x‖ ^ 2 + 2 * ‖v (x - e)‖ ^ 2) := by
    intro x
    unfold backwardDiff
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left (norm_sub_sq_le _ _) (sq_nonneg _)
  refine (Finset.sum_le_sum fun x _ => hpt x).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_norm_sq_sub]
  nlinarith [sq_nonneg h⁻¹, Finset.sum_nonneg fun x (_ : x ∈ univ) => sq_nonneg ‖v x‖]

omit [NormedSpace ℝ F] in
/-- `‖a₁ + a₂ + a₃‖² ≤ 3 (‖a₁‖² + ‖a₂‖² + ‖a₃‖²)`. -/
theorem norm_sum_three_sq_le (a : Fin 3 → F) :
    ‖∑ i, a i‖ ^ 2 ≤ 3 * ∑ i, ‖a i‖ ^ 2 := by
  have h1 : ‖∑ i, a i‖ ≤ ∑ i, ‖a i‖ := norm_sum_le _ _
  simp only [Fin.sum_univ_three] at h1 ⊢
  have h0 : 0 ≤ ‖a 0 + a 1 + a 2‖ := norm_nonneg _
  have h2 : ‖a 0 + a 1 + a 2‖ ^ 2 ≤ (‖a 0‖ + ‖a 1‖ + ‖a 2‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
  nlinarith [sq_nonneg (‖a 0‖ - ‖a 1‖), sq_nonneg (‖a 0‖ - ‖a 2‖), sq_nonneg (‖a 1‖ - ‖a 2‖)]

/-- **`eq:supp-law-domination`.** For every array `w`,
`h² ‖Λ_h w‖_h² ≤ 12 ∑_i ‖D_i^+ w‖_h²`. -/
theorem grid_laplacian_domination (h : ℝ) (hh : 0 < h) (e : Fin 3 → G) (w : G → F) :
    h ^ 2 * gridNormSq h (gridLaplacian h e w)
      ≤ 12 * ∑ i, gridNormSq h (forwardDiff h (e i) w) := by
  unfold gridNormSq gridLaplacian
  have hpt : ∀ x, ‖-∑ i, backwardDiff h (e i) (forwardDiff h (e i) w) x‖ ^ 2
      ≤ 3 * ∑ i, ‖backwardDiff h (e i) (forwardDiff h (e i) w) x‖ ^ 2 := by
    intro x
    rw [norm_neg]
    exact norm_sum_three_sq_le fun i => backwardDiff h (e i) (forwardDiff h (e i) w) x
  have hsum : ∑ x, ‖-∑ i, backwardDiff h (e i) (forwardDiff h (e i) w) x‖ ^ 2
      ≤ 3 * ∑ i, 4 * h⁻¹ ^ 2 * ∑ x, ‖forwardDiff h (e i) w x‖ ^ 2 := by
    refine (Finset.sum_le_sum fun x _ => hpt x).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun i _ => sum_backwardDiff_sq_le h (e i) _
  have hh2 : h ^ 2 * h⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hh.ne', one_pow]
  calc h ^ 2 * (h ^ 3 * ∑ x, ‖-∑ i, backwardDiff h (e i) (forwardDiff h (e i) w) x‖ ^ 2)
      ≤ h ^ 2 * (h ^ 3 * (3 * ∑ i, 4 * h⁻¹ ^ 2 * ∑ x, ‖forwardDiff h (e i) w x‖ ^ 2)) := by
        gcongr
    _ = 12 * ∑ i, h ^ 3 * ∑ x, ‖forwardDiff h (e i) w x‖ ^ 2 := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
        linear_combination (12 * h ^ 3 * ‖forwardDiff h (e i) w x‖ ^ 2) * hh2

/-- The periodic grid `(hℤ/ℤ)³` of the paper as `Fin 3 → ZMod N`. -/
abbrev PeriodicGrid (N : ℕ) : Type := Fin 3 → ZMod N

/-- The unit steps of the periodic grid. -/
def unitStep (N : ℕ) (i : Fin 3) : PeriodicGrid N := Pi.single i 1

/-- `eq:supp-law-domination` on the periodic grid `(hℤ/ℤ)³` with
`N = 2m + 1` points per axis. -/
theorem periodic_laplacian_domination (N : ℕ) [NeZero N] (h : ℝ) (hh : 0 < h)
    (w : PeriodicGrid N → F) :
    h ^ 2 * gridNormSq h (gridLaplacian h (unitStep N) w)
      ≤ 12 * ∑ i, gridNormSq h (forwardDiff h (unitStep N i) w) :=
  grid_laplacian_domination h hh (unitStep N) w

end Grid

/-! ### The symbol and the Fourier-side order bounds -/

/-- The symbol `ℓ_h(k) = 4 h⁻² ∑_i sin²(π h k_i)` of `Λ_h`
(`eq:supp-law-laplacian`). -/
noncomputable def laplaceSymbol (h : ℝ) (k : Fin 3 → ℝ) : ℝ :=
  4 * h⁻¹ ^ 2 * ∑ i, Real.sin (Real.pi * h * k i) ^ 2

/-- `0 ≤ h² ℓ_h(k) ≤ 12` (`eq:supp-law-laplacian`). -/
theorem symbol_bounds (h : ℝ) (hh : 0 < h) (k : Fin 3 → ℝ) :
    0 ≤ h ^ 2 * laplaceSymbol h k ∧ h ^ 2 * laplaceSymbol h k ≤ 12 := by
  have hh2 : h ^ 2 * h⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hh.ne', one_pow]
  have hsum : ∑ i, Real.sin (Real.pi * h * k i) ^ 2 ≤ 3 := by
    calc ∑ i, Real.sin (Real.pi * h * k i) ^ 2 ≤ ∑ _i : Fin 3, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Real.sin_sq_le_one _
      _ = 3 := by simp
  have hpos : 0 ≤ ∑ i, Real.sin (Real.pi * h * k i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  unfold laplaceSymbol
  constructor
  · positivity
  · calc h ^ 2 * (4 * h⁻¹ ^ 2 * ∑ i, Real.sin (Real.pi * h * k i) ^ 2)
        = 4 * (h ^ 2 * h⁻¹ ^ 2) * ∑ i, Real.sin (Real.pi * h * k i) ^ 2 := by ring
      _ = 4 * ∑ i, Real.sin (Real.pi * h * k i) ^ 2 := by rw [hh2, mul_one]
      _ ≤ 12 := by linarith

section Fourier

variable {K : Type*} [Fintype K]

/-- Fourier-weighted Sobolev norm of order `r`:
`‖q‖_{r}² = ∑_k (1 + ℓ_k)^r |q̂_k|²`, for real mode amplitudes. -/
noncomputable def sobolevNormSq (ℓ : K → ℝ) (r : ℝ) (q : K → ℝ) : ℝ :=
  ∑ k, (1 + ℓ k) ^ r * q k ^ 2

/-- The Fourier-weighted Sobolev norm. -/
noncomputable def sobolevNorm (ℓ : K → ℝ) (r : ℝ) (q : K → ℝ) : ℝ :=
  Real.sqrt (sobolevNormSq ℓ r q)

/-- The multiplier `Λ_h²` on the mode side: `q̂_k ↦ ℓ_k² q̂_k`. -/
def biharmonicMultiplier (ℓ : K → ℝ) (q : K → ℝ) : K → ℝ := fun k => ℓ k ^ 2 * q k

theorem sobolevNormSq_nonneg (ℓ : K → ℝ) (hℓ : ∀ k, 0 ≤ ℓ k) (r : ℝ) (q : K → ℝ) :
    0 ≤ sobolevNormSq ℓ r q :=
  Finset.sum_nonneg fun k _ => mul_nonneg (Real.rpow_nonneg (by linarith [hℓ k]) _) (sq_nonneg _)

/-- Mode-wise reduction: if `w_k ≤ c² w'_k` termwise then the square roots of
the weighted sums compare with the factor `c ≥ 0`. -/
theorem sqrt_sum_le_of_termwise (c : ℝ) (hc : 0 ≤ c) (u v : K → ℝ)
    (huv : ∀ k, u k ≤ c ^ 2 * v k) :
    Real.sqrt (∑ k, u k) ≤ c * Real.sqrt (∑ k, v k) := by
  calc Real.sqrt (∑ k, u k) ≤ Real.sqrt (c ^ 2 * ∑ k, v k) := by
        apply Real.sqrt_le_sqrt
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ => huv k
    _ = c * Real.sqrt (∑ k, v k) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Termwise ratio bounds for the biharmonic multiplier: for
`0 ≤ ℓ`, `h² ℓ ≤ 12` and `t = 1 + ℓ`,
`h⁴ ℓ⁴ ≤ 144 t²`, `h⁴ ℓ⁴ ≤ 12 h² t³`, `h⁴ ℓ⁴ ≤ h⁴ t⁴`. -/
theorem ratio_bounds {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 ≤ ℓ) (hℓ12 : h ^ 2 * ℓ ≤ 12) :
    h ^ 4 * ℓ ^ 4 ≤ 144 * (1 + ℓ) ^ 2 ∧
    h ^ 4 * ℓ ^ 4 ≤ 12 * h ^ 2 * (1 + ℓ) ^ 3 ∧
    h ^ 4 * ℓ ^ 4 ≤ h ^ 4 * (1 + ℓ) ^ 4 := by
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  have hℓ1 : ℓ ≤ 1 + ℓ := by linarith
  have hℓ2 : ℓ ^ 2 ≤ (1 + ℓ) ^ 2 := by gcongr
  have hℓ3 : ℓ ^ 3 ≤ (1 + ℓ) ^ 3 := by gcongr
  have hℓ4 : ℓ ^ 4 ≤ (1 + ℓ) ^ 4 := by gcongr
  have hkey : h ^ 2 * ℓ ^ 2 ≤ 12 * (1 + ℓ) := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul hkey hkey (by positivity) (by positivity)]
  · have : h ^ 4 * ℓ ^ 4 = (h ^ 2 * ℓ) * (h ^ 2 * ℓ ^ 3) := by ring
    rw [this]
    have h1 : 0 ≤ h ^ 2 * ℓ ^ 3 := by positivity
    calc (h ^ 2 * ℓ) * (h ^ 2 * ℓ ^ 3) ≤ 12 * (h ^ 2 * ℓ ^ 3) :=
          mul_le_mul_of_nonneg_right hℓ12 h1
      _ ≤ 12 * (h ^ 2 * (1 + ℓ) ^ 3) := by gcongr
      _ = 12 * h ^ 2 * (1 + ℓ) ^ 3 := by ring
  · exact mul_le_mul_of_nonneg_left hℓ4 (by positivity)

theorem rpow_add_two (t : ℝ) (ht : 0 < t) (r : ℝ) : t ^ (r + 2) = t ^ r * t ^ 2 := by
  rw [Real.rpow_add ht, Real.rpow_two]

theorem rpow_add_three (t : ℝ) (ht : 0 < t) (r : ℝ) : t ^ (r + 3) = t ^ r * t ^ 3 := by
  rw [Real.rpow_add ht, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem rpow_add_four (t : ℝ) (ht : 0 < t) (r : ℝ) : t ^ (r + 4) = t ^ r * t ^ 4 := by
  rw [Real.rpow_add ht, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **`eq:supp-law-orders` on the mode side.** For a symbol `ℓ` with
`0 ≤ ℓ` and `h² ℓ ≤ 12`, the Fourier-weighted norms satisfy, at every index
`s`,
`h² ‖Λ² q‖_{s-1} ≤ 12 ‖q‖_{s+1}`, `h² ‖Λ² q‖_{s-2} ≤ √12 h ‖q‖_{s+1}`,
`h² ‖Λ² q‖_{s-3} ≤ h² ‖q‖_{s+1}`, `h² ‖Λ² v‖_{s-3} ≤ √12 h ‖v‖_s`. -/
theorem fourth_order_bounds (ℓ : K → ℝ) (h : ℝ) (hh : 0 < h) (hℓ : ∀ k, 0 ≤ ℓ k)
    (hℓ12 : ∀ k, h ^ 2 * ℓ k ≤ 12) (s : ℝ) (q v : K → ℝ) :
    h ^ 2 * sobolevNorm ℓ (s - 1) (biharmonicMultiplier ℓ q)
        ≤ 12 * sobolevNorm ℓ (s + 1) q ∧
    h ^ 2 * sobolevNorm ℓ (s - 2) (biharmonicMultiplier ℓ q)
        ≤ Real.sqrt 12 * h * sobolevNorm ℓ (s + 1) q ∧
    h ^ 2 * sobolevNorm ℓ (s - 3) (biharmonicMultiplier ℓ q)
        ≤ h ^ 2 * sobolevNorm ℓ (s + 1) q ∧
    h ^ 2 * sobolevNorm ℓ (s - 3) (biharmonicMultiplier ℓ v)
        ≤ Real.sqrt 12 * h * sobolevNorm ℓ s v := by
  have hpos : ∀ k, 0 < 1 + ℓ k := fun k => by linarith [hℓ k]
  have hweight : ∀ (r : ℝ) (k : K), 0 ≤ (1 + ℓ k) ^ r :=
    fun r k => Real.rpow_nonneg (hpos k).le r
  -- generic reduction: a bound on `h² ‖Λ² q‖_{r}` by `c ‖q‖_{r'}` from termwise bounds
  have generic : ∀ (r r' c : ℝ) (q : K → ℝ), 0 ≤ c →
      (∀ k, h ^ 4 * (1 + ℓ k) ^ r * ℓ k ^ 4 ≤ c ^ 2 * (1 + ℓ k) ^ r') →
      h ^ 2 * sobolevNorm ℓ r (biharmonicMultiplier ℓ q) ≤ c * sobolevNorm ℓ r' q := by
    intro r r' c q hc hterm
    unfold sobolevNorm sobolevNormSq biharmonicMultiplier
    have hh2 : h ^ 2 = Real.sqrt ((h ^ 2) ^ 2) := (Real.sqrt_sq (sq_nonneg h)).symm
    rw [hh2, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
    refine sqrt_sum_le_of_termwise c hc _ _ fun k => ?_
    have := mul_le_mul_of_nonneg_right (hterm k) (sq_nonneg (q k))
    calc (h ^ 2) ^ 2 * ((1 + ℓ k) ^ r * (ℓ k ^ 2 * q k) ^ 2)
        = h ^ 4 * (1 + ℓ k) ^ r * ℓ k ^ 4 * q k ^ 2 := by ring
      _ ≤ c ^ 2 * (1 + ℓ k) ^ r' * q k ^ 2 := this
      _ = c ^ 2 * ((1 + ℓ k) ^ r' * q k ^ 2) := by ring
  have h12 : (0 : ℝ) ≤ Real.sqrt 12 := Real.sqrt_nonneg _
  have h12sq : Real.sqrt 12 ^ 2 = 12 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine generic (s - 1) (s + 1) 12 q (by norm_num) fun k => ?_
    obtain ⟨h1, -, -⟩ := ratio_bounds hh (hℓ k) (hℓ12 k)
    have : (1 + ℓ k) ^ (s + 1) = (1 + ℓ k) ^ (s - 1) * (1 + ℓ k) ^ 2 := by
      rw [← rpow_add_two _ (hpos k)]; ring_nf
    rw [this]
    calc h ^ 4 * (1 + ℓ k) ^ (s - 1) * ℓ k ^ 4
        = (1 + ℓ k) ^ (s - 1) * (h ^ 4 * ℓ k ^ 4) := by ring
      _ ≤ (1 + ℓ k) ^ (s - 1) * (144 * (1 + ℓ k) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (hweight _ _)
      _ = 12 ^ 2 * ((1 + ℓ k) ^ (s - 1) * (1 + ℓ k) ^ 2) := by ring
  · refine generic (s - 2) (s + 1) (Real.sqrt 12 * h) q (by positivity) fun k => ?_
    obtain ⟨-, h2, -⟩ := ratio_bounds hh (hℓ k) (hℓ12 k)
    have : (1 + ℓ k) ^ (s + 1) = (1 + ℓ k) ^ (s - 2) * (1 + ℓ k) ^ 3 := by
      rw [← rpow_add_three _ (hpos k)]; ring_nf
    rw [this]
    calc h ^ 4 * (1 + ℓ k) ^ (s - 2) * ℓ k ^ 4
        = (1 + ℓ k) ^ (s - 2) * (h ^ 4 * ℓ k ^ 4) := by ring
      _ ≤ (1 + ℓ k) ^ (s - 2) * (12 * h ^ 2 * (1 + ℓ k) ^ 3) :=
          mul_le_mul_of_nonneg_left h2 (hweight _ _)
      _ = (Real.sqrt 12 * h) ^ 2 * ((1 + ℓ k) ^ (s - 2) * (1 + ℓ k) ^ 3) := by
          rw [mul_pow, h12sq]; ring
  · refine generic (s - 3) (s + 1) (h ^ 2) q (by positivity) fun k => ?_
    obtain ⟨-, -, h3⟩ := ratio_bounds hh (hℓ k) (hℓ12 k)
    have : (1 + ℓ k) ^ (s + 1) = (1 + ℓ k) ^ (s - 3) * (1 + ℓ k) ^ 4 := by
      rw [← rpow_add_four _ (hpos k)]; ring_nf
    rw [this]
    calc h ^ 4 * (1 + ℓ k) ^ (s - 3) * ℓ k ^ 4
        = (1 + ℓ k) ^ (s - 3) * (h ^ 4 * ℓ k ^ 4) := by ring
      _ ≤ (1 + ℓ k) ^ (s - 3) * (h ^ 4 * (1 + ℓ k) ^ 4) :=
          mul_le_mul_of_nonneg_left h3 (hweight _ _)
      _ = (h ^ 2) ^ 2 * ((1 + ℓ k) ^ (s - 3) * (1 + ℓ k) ^ 4) := by ring
  · refine generic (s - 3) s (Real.sqrt 12 * h) v (by positivity) fun k => ?_
    obtain ⟨-, h2, -⟩ := ratio_bounds hh (hℓ k) (hℓ12 k)
    have : (1 + ℓ k) ^ s = (1 + ℓ k) ^ (s - 3) * (1 + ℓ k) ^ 3 := by
      rw [← rpow_add_three _ (hpos k)]; ring_nf
    rw [this]
    calc h ^ 4 * (1 + ℓ k) ^ (s - 3) * ℓ k ^ 4
        = (1 + ℓ k) ^ (s - 3) * (h ^ 4 * ℓ k ^ 4) := by ring
      _ ≤ (1 + ℓ k) ^ (s - 3) * (12 * h ^ 2 * (1 + ℓ k) ^ 3) :=
          mul_le_mul_of_nonneg_left h2 (hweight _ _)
      _ = (Real.sqrt 12 * h) ^ 2 * ((1 + ℓ k) ^ (s - 3) * (1 + ℓ k) ^ 3) := by
          rw [mul_pow, h12sq]; ring

end Fourier

end

end LawMultiplier
end RenewalGeometry
