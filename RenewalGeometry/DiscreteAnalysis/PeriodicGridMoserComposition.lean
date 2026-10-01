/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridSobolevCalculus

/-!
# Discrete Moser estimates: analytic composition on the periodic grid
  (`lem:supp-open-calculus`, "analytic coefficient compositions"; emergent-spacetime manuscript)

On the periodic grid `(ℤ/N)³` (mesh `h = 1/N`) with the grid Sobolev norms
`‖u‖_{r,h} = sobNorm r u` of `PeriodicGridSobolevCalculus`, every constant below is independent
of `N`.

* `sobNorm_add_le`, `sobNorm_smul`, `sobNorm_sum_le`: `sobNorm r` is a seminorm.
* `norm_le_sobNorm_two` (**uniform discrete embedding** `H²_h ⊂ ℓ^∞`):
  `|u(x)| ≤ √K ‖u‖_{2,h}` with `K = Kprod = 2c₁³`.
* `sobNorm_mul_le`, `sobNorm_prod_le`: the product algebra for `r ≥ 2` in norm form, and
  `‖Π_{k<n+1} f_k‖_{r,h} ≤ A_r^n Π_k ‖f_k‖_{r,h}`.
* `sobNorm_multilinear_le`: for a continuous multilinear `p : Eⁿ → ℝ` on a finite-dimensional
  real space with basis `b`, the array `x ↦ p(u(x), …, u(x))` obeys
  `‖·‖_{r,h} ≤ ‖p‖ A_r^{n-1} (B S)^n`, `S = Σ_j ‖u_j‖_{r,h}` the sum of the coordinate norms,
  `B ≥ max_j ‖b_j‖`.
* `moser_composition_order` (**discrete Moser estimate**): for `A : E → ℝ` analytic at `c`,
  `r ≥ 2` and `m ≥ 1` such that the power series of `A` at `c` has no terms of order
  `1, …, m-1`, there are `δ, C > 0` (independent of `N`) such that every array `u : grid → E`
  with `S(u) ≤ δ` satisfies `‖A(c + u) - A(c)‖_{r,h} ≤ C S(u)^m`.  `moser_composition` is the
  case `m = 1` (no hypothesis); `m = 2` applies when `DA(c) = 0`.
* `sobNorm_multilinear_slots_le`: the multilinear bound with different arrays in the slots,
  `‖x ↦ p(u₀(x), …, u_n(x))‖_{r,h} ≤ ‖p‖ B^{n+1} A_r^n Π_k S_r(u_k)`.
* `moser_lipschitz` (**Lipschitz form**): with mesh-independent `δ, C`,
  `‖A(c + u) - A(c + w)‖_{r,h} ≤ C S_r(u - w)` whenever `S_r(u), S_r(w) ≤ δ` (telescoping of the
  power series via `MultilinearMap.map_sub_map_piecewise`).
-/

open Finset Filter Topology
open scoped BigOperators

namespace RenewalGeometry.PeriodicGridSobolev

namespace Moser

open LatticeTorusPlancherel

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### `sobNorm` is a seminorm -/

theorem sobNorm_nonneg (r : ℕ) (u : Grid N → ℂ) : 0 ≤ sobNorm r u := Real.sqrt_nonneg _

theorem sobSq_eq_sum_gridNorm_sq (r : ℕ) (u : Grid N → ℂ) :
    sobSq r u = ∑ α ∈ multiIndices r, gridNorm (Dα α u) ^ 2 := by
  unfold sobSq; simp only [gridNorm_sq]

theorem sobNorm_add_le (r : ℕ) (u w : Grid N → ℂ) :
    sobNorm r (u + w) ≤ sobNorm r u + sobNorm r w := by
  set a : (Fin 3 → ℕ) → ℝ := fun α => gridNorm (Dα α u)
  set b : (Fin 3 → ℕ) → ℝ := fun α => gridNorm (Dα α w)
  have h1 : sobSq r (u + w) ≤ ∑ α ∈ multiIndices r, (a α + b α) ^ 2 := by
    rw [sobSq_eq_sum_gridNorm_sq]
    refine sum_le_sum fun α _ => ?_
    rw [map_add]
    exact pow_le_pow_left₀ (gridNorm_nonneg _) (gridNorm_add_le _ _) 2
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (multiIndices r) a b
  have hA : sobNorm r u = Real.sqrt (∑ α ∈ multiIndices r, a α ^ 2) := by
    rw [sobNorm, sobSq_eq_sum_gridNorm_sq]
  have hB : sobNorm r w = Real.sqrt (∑ α ∈ multiIndices r, b α ^ 2) := by
    rw [sobNorm, sobSq_eq_sum_gridNorm_sq]
  have hsq : ∑ α ∈ multiIndices r, (a α + b α) ^ 2 ≤ (sobNorm r u + sobNorm r w) ^ 2 := by
    have e : ∑ α ∈ multiIndices r, (a α + b α) ^ 2 = ∑ α ∈ multiIndices r, a α ^ 2 +
        2 * ∑ α ∈ multiIndices r, a α * b α + ∑ α ∈ multiIndices r, b α ^ 2 := by
      rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun _ _ => by ring
    rw [e, add_sq, hA, hB, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
    linarith
  rw [← Real.sqrt_sq (add_nonneg (sobNorm_nonneg r u) (sobNorm_nonneg r w)), sobNorm]
  exact Real.sqrt_le_sqrt (h1.trans hsq)

theorem sobNorm_smul (r : ℕ) (c : ℂ) (u : Grid N → ℂ) :
    sobNorm r (c • u) = ‖c‖ * sobNorm r u := by
  have : sobSq r (c • u) = ‖c‖ ^ 2 * sobSq r u := by
    rw [sobSq_eq_sum_gridNorm_sq, sobSq_eq_sum_gridNorm_sq, mul_sum]
    refine sum_congr rfl fun α _ => ?_
    rw [map_smul, gridNorm_smul, mul_pow]
  rw [sobNorm, this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), sobNorm]

theorem sobNorm_neg (r : ℕ) (u : Grid N → ℂ) : sobNorm r (-u) = sobNorm r u := by
  rw [← neg_one_smul ℂ u, sobNorm_smul]; simp

theorem sobNorm_sub_le (r : ℕ) (u w : Grid N → ℂ) :
    sobNorm r (u - w) ≤ sobNorm r u + sobNorm r w := by
  rw [sub_eq_add_neg]
  exact (sobNorm_add_le r _ _).trans (by rw [sobNorm_neg])

theorem sobNorm_zero (r : ℕ) : sobNorm r (0 : Grid N → ℂ) = 0 := by
  have := sobNorm_smul r 0 (0 : Grid N → ℂ)
  simpa using this

theorem sobNorm_sum_le {ι : Type*} (r : ℕ) (s : Finset ι) (f : ι → Grid N → ℂ) :
    sobNorm r (∑ i ∈ s, f i) ≤ ∑ i ∈ s, sobNorm r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sobNorm_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (sobNorm_add_le r _ _).trans (by linarith)

theorem sobNorm_mono {r r' : ℕ} (h : r ≤ r') (u : Grid N → ℂ) : sobNorm r u ≤ sobNorm r' u :=
  Real.sqrt_le_sqrt (sobSq_mono h u)

theorem continuous_sobNorm (r : ℕ) : Continuous (sobNorm (N := N) r) := by
  have hD : ∀ α : Fin 3 → ℕ, Continuous (Dα (N := N) α) := fun α =>
    LinearMap.continuous_of_finiteDimensional _
  unfold sobNorm sobSq gridNormSq
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun α _ => ?_)
  refine continuous_const.mul (continuous_finsetSum _ fun x _ => ?_)
  exact ((continuous_apply x).comp (hD α)).norm.pow 2

/-! ### Uniform embedding `H²_h ⊂ ℓ^∞` -/

/-- **Uniform discrete Sobolev embedding**: `|u(x)| ≤ √K ‖u‖_{2,h}`, `K = 2c₁³`, for every
`N`. -/
theorem norm_le_sobNorm_two (u : Grid N → ℂ) (x : Grid N) :
    ‖u x‖ ≤ Real.sqrt Kprod * sobNorm 2 u := by
  rw [← dft_inversion u x]
  have hcw : ∀ k : Grid N, 0 < cubeWeight k := fun k =>
    lt_of_lt_of_le one_pos (one_le_cubeWeight k)
  calc ‖∑ k, latticeChar k x * dft u k‖ ≤ ∑ k, ‖dft u k‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
        rw [norm_mul]
        simp [latticeChar]
    _ = ∑ k, (cubeWeight k)⁻¹ * (cubeWeight k * ‖dft u k‖) := by
        refine sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, inv_mul_cancel₀ (hcw k).ne', one_mul]
    _ ≤ Real.sqrt (∑ k, ((cubeWeight k)⁻¹) ^ 2) *
          Real.sqrt (∑ k, (cubeWeight k * ‖dft u k‖) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (c1 ^ 3) * Real.sqrt (2 * sobSq 2 u) := by
        gcongr
        · refine le_trans (le_of_eq (sum_congr rfl fun k _ => by rw [inv_pow])) ?_
          exact sum_inv_cubeWeight_sq_le
        · rw [sobSq_eq_weight, mul_sum]
          refine sum_le_sum fun k _ => ?_
          have := cubeWeight_sq_le_gridWeight_two k
          rw [mul_pow]
          nlinarith [sq_nonneg ‖dft u k‖]
    _ = Real.sqrt Kprod * sobNorm 2 u := by
        rw [Kprod, sobNorm, ← Real.sqrt_mul (by have := c1_nonneg; positivity),
          ← Real.sqrt_mul (by have := c1_nonneg; positivity)]
        congr 1; ring

/-! ### The product algebra in norm form -/

/-- The algebra constant `A_r = max 1 √(K Σ_{|α| ≤ r} B(α)²)`. -/
noncomputable def algConst (r : ℕ) : ℝ :=
  max 1 (Real.sqrt (Kprod * ∑ α ∈ multiIndices r, binomMass α ^ 2))

theorem one_le_algConst (r : ℕ) : 1 ≤ algConst r := le_max_left _ _

theorem algConst_pos (r : ℕ) : 0 < algConst r := lt_of_lt_of_le one_pos (one_le_algConst r)

/-- Product algebra, norm form: `‖f w‖_{r,h} ≤ A_r ‖f‖_{r,h} ‖w‖_{r,h}` for `r ≥ 2`. -/
theorem sobNorm_mul_le (r : ℕ) (hr : 2 ≤ r) (f w : Grid N → ℂ) :
    sobNorm r (f * w) ≤ algConst r * sobNorm r f * sobNorm r w := by
  have h := sobSq_mul_le r hr f w
  have hK : 0 ≤ Kprod * ∑ α ∈ multiIndices r, binomMass α ^ 2 :=
    mul_nonneg Kprod_nonneg (sum_nonneg fun _ _ => sq_nonneg _)
  calc sobNorm r (f * w) ≤ Real.sqrt ((Kprod * ∑ α ∈ multiIndices r, binomMass α ^ 2) *
        sobSq r f * sobSq r w) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (Kprod * ∑ α ∈ multiIndices r, binomMass α ^ 2) * sobNorm r f *
        sobNorm r w := by
        rw [Real.sqrt_mul (mul_nonneg hK (sobSq_nonneg _ _)), Real.sqrt_mul hK, sobNorm, sobNorm]
    _ ≤ algConst r * sobNorm r f * sobNorm r w := by
        have := sobNorm_nonneg r f; have := sobNorm_nonneg r w
        gcongr
        exact le_max_right _ _

/-- Products of `n + 1` arrays: `‖Π_k f_k‖_{r,h} ≤ A_r^n Π_k ‖f_k‖_{r,h}`. -/
theorem sobNorm_prod_le (r : ℕ) (hr : 2 ≤ r) (n : ℕ) (f : Fin (n + 1) → Grid N → ℂ) :
    sobNorm r (∏ k, f k) ≤ algConst r ^ n * ∏ k, sobNorm r (f k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ (n := n + 1), Fin.prod_univ_succ (n := n + 1)]
    refine (sobNorm_mul_le r hr _ _).trans ?_
    have h1 := ih (fun k => f k.succ)
    have := sobNorm_nonneg r (f 0)
    have := algConst_pos r
    calc algConst r * sobNorm r (f 0) * sobNorm r (∏ k : Fin (n + 1), f k.succ)
        ≤ algConst r * sobNorm r (f 0) * (algConst r ^ n * ∏ k : Fin (n + 1),
            sobNorm r (f k.succ)) := by gcongr
      _ = algConst r ^ (n + 1) * (sobNorm r (f 0) * ∏ k : Fin (n + 1), sobNorm r (f k.succ)) := by
          ring

/-! ### Multilinear evaluations of arrays -/

section Multilinear

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]

/-- The complexified `j`-th coordinate array `x ↦ b.repr (u x) j` of an `E`-valued array. -/
noncomputable def coordArr (b : Module.Basis ι ℝ E) (u : Grid N → E) (j : ι) : Grid N → ℂ :=
  fun x => ((b.repr (u x) j : ℝ) : ℂ)

/-- The coordinate size `S_r(u) = Σ_j ‖u_j‖_{r,h}` of an `E`-valued array. -/
noncomputable def coordSum (r : ℕ) (b : Module.Basis ι ℝ E) (u : Grid N → E) : ℝ :=
  ∑ j, sobNorm r (coordArr b u j)

theorem coordSum_nonneg (r : ℕ) (b : Module.Basis ι ℝ E) (u : Grid N → E) :
    0 ≤ coordSum r b u := sum_nonneg fun _ _ => sobNorm_nonneg _ _

theorem coordSum_mono {r r' : ℕ} (h : r ≤ r') (b : Module.Basis ι ℝ E) (u : Grid N → E) :
    coordSum r b u ≤ coordSum r' b u := sum_le_sum fun _ _ => sobNorm_mono h _

/-- Coordinate expansion of a multilinear evaluation on the diagonal. -/
theorem multilinear_diag_eq {n : ℕ} (b : Module.Basis ι ℝ E)
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) (y : E) :
    p (fun _ => y) = ∑ ρ : Fin n → ι, (∏ k, b.repr y (ρ k)) * p (fun k => b (ρ k)) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [p.map_sum (fun _ j => b.repr y j • b j)]
  refine sum_congr rfl fun ρ _ => ?_
  rw [p.map_smul_univ (fun k => b.repr y (ρ k)) (fun k => b (ρ k)), smul_eq_mul]

/-- Pointwise bound `‖u(x)‖ ≤ B √K S_2(u)` for `B ≥ ‖b_j‖`. -/
theorem norm_le_coordSum (b : Module.Basis ι ℝ E) {B : ℝ} (hB : ∀ j, ‖b j‖ ≤ B)
    (u : Grid N → E) (x : Grid N) :
    ‖u x‖ ≤ B * (Real.sqrt Kprod * coordSum 2 b u) := by
  calc ‖u x‖ = ‖∑ j, b.repr (u x) j • b j‖ := by rw [b.sum_repr]
    _ ≤ ∑ j, ‖coordArr b u j x‖ * B := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        rw [norm_smul, coordArr, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left (hB j) (norm_nonneg _)
    _ ≤ ∑ j, Real.sqrt Kprod * sobNorm 2 (coordArr b u j) * B := by
        refine sum_le_sum fun j _ => ?_
        have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB j)
        exact mul_le_mul_of_nonneg_right (norm_le_sobNorm_two _ x) hB0
    _ = B * (Real.sqrt Kprod * coordSum 2 b u) := by
        rw [coordSum, mul_sum, mul_sum]
        exact sum_congr rfl fun _ _ => by ring

/-- The diagonal array of a multilinear form, as a combination of coordinate products. -/
theorem multilinear_array_eq {n : ℕ} (b : Module.Basis ι ℝ E)
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) (u : Grid N → E) :
    (fun x => ((p (fun _ => u x) : ℝ) : ℂ)) =
      ∑ ρ : Fin n → ι, ((p (fun k => b (ρ k)) : ℝ) : ℂ) • ∏ k, coordArr b u (ρ k) := by
  funext x
  rw [multilinear_diag_eq b p (u x)]
  simp only [Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, coordArr, smul_eq_mul]
  push_cast
  exact sum_congr rfl fun _ _ => by ring

/-- **Multilinear bound**: for `r ≥ 2`, a continuous multilinear `p : E^{n+1} → ℝ` and
`‖b_j‖ ≤ B`, `‖x ↦ p(u(x), …, u(x))‖_{r,h} ≤ ‖p‖ B^{n+1} A_r^n S_r(u)^{n+1}`. -/
theorem sobNorm_multilinear_le (r : ℕ) (hr : 2 ≤ r) {n : ℕ} (b : Module.Basis ι ℝ E) {B : ℝ}
    (hB : ∀ j, ‖b j‖ ≤ B) (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ)
    (u : Grid N → E) :
    sobNorm r (fun x => ((p (fun _ => u x) : ℝ) : ℂ)) ≤
      ‖p‖ * B ^ (n + 1) * algConst r ^ n * coordSum r b u ^ (n + 1) := by
  rw [multilinear_array_eq b p u]
  refine (sobNorm_sum_le r _ _).trans ?_
  have hterm : ∀ ρ : Fin (n + 1) → ι,
      sobNorm r (((p (fun k => b (ρ k)) : ℝ) : ℂ) • ∏ k, coordArr b u (ρ k)) ≤
        ‖p‖ * B ^ (n + 1) * algConst r ^ n * ∏ k, sobNorm r (coordArr b u (ρ k)) := by
    intro ρ
    rw [sobNorm_smul, Complex.norm_real]
    have h1 : ‖p (fun k => b (ρ k))‖ ≤ ‖p‖ * B ^ (n + 1) := by
      refine (p.le_opNorm _).trans ?_
      gcongr
      calc ∏ k, ‖b (ρ k)‖ ≤ ∏ _k : Fin (n + 1), B :=
            prod_le_prod (fun _ _ => norm_nonneg _) (fun k _ => hB (ρ k))
        _ = B ^ (n + 1) := by simp
    have h2 := sobNorm_prod_le r hr n (fun k => coordArr b u (ρ k))
    have h3 : 0 ≤ ∏ k, sobNorm r (coordArr b u (ρ k)) :=
      prod_nonneg fun _ _ => sobNorm_nonneg _ _
    have := algConst_pos r
    calc ‖p (fun k => b (ρ k))‖ * sobNorm r (∏ k, coordArr b u (ρ k))
        ≤ (‖p‖ * B ^ (n + 1)) * (algConst r ^ n * ∏ k, sobNorm r (coordArr b u (ρ k))) :=
          mul_le_mul h1 h2 (sobNorm_nonneg _ _) ((norm_nonneg _).trans h1)
      _ = _ := by ring
  refine (sum_le_sum fun ρ _ => hterm ρ).trans (le_of_eq ?_)
  rw [← mul_sum, coordSum, ← Fintype.prod_sum (fun (_ : Fin (n + 1)) j =>
    sobNorm r (coordArr b u j))]
  simp

/-! ### The discrete Moser estimate -/

/-- **Discrete Moser estimate of order `m`.**  Let `E` be a finite-dimensional real space with
basis `b`, `A : E → ℝ` with power series `p` at `c` on a ball of radius `R > 0`, `r ≥ 2`, and
`m ≥ 1` with `p n = 0` for `0 < n < m`.  There are `δ > 0`, `C ≥ 0`, independent of the mesh,
such that for every `N` and every array `u : (ℤ/N)³ → E` with `S_r(u) = Σ_j ‖u_j‖_{r,h} ≤ δ`,
`‖A(c + u) - A(c)‖_{r,h} ≤ C S_r(u)^m`. -/
theorem moser_composition_order (r : ℕ) (hr : 2 ≤ r) (b : Module.Basis ι ℝ E) {A : E → ℝ}
    {c : E} {p : FormalMultilinearSeries ℝ E ℝ} {R : ENNReal}
    (hA : HasFPowerSeriesOnBall A p c R) (m : ℕ) (hm : 1 ≤ m)
    (hp : ∀ n, 0 < n → n < m → p n = 0) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (u : Grid N → E), coordSum r b u ≤ δ →
      sobNorm r (fun x => ((A (c + u x) - A c : ℝ) : ℂ)) ≤ C * coordSum r b u ^ m := by
  obtain ⟨ρ, hρ0, hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hA.r_pos
  obtain ⟨K, hK, hKp⟩ := p.norm_mul_pow_le_of_lt_radius (hρR.trans_le hA.r_le)
  set B : ℝ := 1 + ∑ j, ‖b j‖ with hBdef
  have hB : ∀ j, ‖b j‖ ≤ B := fun j => by
    have := single_le_sum (f := fun j => ‖b j‖) (fun _ _ => norm_nonneg _) (mem_univ j)
    linarith
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ∑ j, ‖b j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hρ0)
  set Al := algConst r
  have hAl := algConst_pos r
  set L : ℝ := B * (Al + Real.sqrt Kprod) with hLdef
  have hL : 0 < L := mul_pos (by linarith) (by positivity)
  refine ⟨ρ / (2 * L), by positivity, 2 * K / Al * (B * Al / ρ) ^ m, by positivity, ?_⟩
  intro N _ u hu
  set S := coordSum r b u
  have hS0 : 0 ≤ S := coordSum_nonneg r b u
  -- the pointwise expansion
  set x0 : ℝ := B * Al * S / ρ with hx0
  have hx0nn : 0 ≤ x0 := by positivity
  have hx0le : x0 ≤ 1 / 2 := by
    rw [hx0, div_le_iff₀ hρ]
    have h1 : B * Al * S ≤ L * S := by
      rw [hLdef]; gcongr; linarith [Real.sqrt_nonneg Kprod]
    have h2 : L * S ≤ ρ / 2 := by
      calc L * S ≤ L * (ρ / (2 * L)) := mul_le_mul_of_nonneg_left hu hL.le
        _ = ρ / 2 := by field_simp
    linarith
  have hpt : ∀ x, ‖u x‖ < ρ := by
    intro x
    have h1 := norm_le_coordSum b hB u x
    have h2 : coordSum 2 b u ≤ S := coordSum_mono hr b u
    have h3 : B * (Real.sqrt Kprod * coordSum 2 b u) ≤ L * S := by
      rw [hLdef]
      have := Real.sqrt_nonneg Kprod
      have := coordSum_nonneg 2 b u
      calc B * (Real.sqrt Kprod * coordSum 2 b u) ≤ B * (Real.sqrt Kprod * S) := by gcongr
        _ ≤ B * ((Al + Real.sqrt Kprod) * S) := by gcongr; linarith
        _ = B * (Al + Real.sqrt Kprod) * S := by ring
    have h4 : L * S ≤ ρ / 2 := by
      calc L * S ≤ L * (ρ / (2 * L)) := mul_le_mul_of_nonneg_left hu hL.le
        _ = ρ / 2 := by field_simp
    linarith
  have hsum : ∀ x, HasSum (fun n => p (n + m) (fun _ => u x)) (A (c + u x) - A c) := by
    intro x
    have hmem : u x ∈ Metric.eball (0 : E) R := by
      rw [Metric.mem_eball, edist_zero_right]
      refine lt_of_le_of_lt ?_ hρR
      rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
      exact (hpt x).le
    have h := (hasSum_nat_add_iff' m).mpr (hA.hasSum hmem)
    have hfirst : ∑ i ∈ range m, p i (fun _ => u x) = A c := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [sum_range_succ']
      have hz : ∑ i ∈ range m', p (i + 1) (fun _ => u x) = 0 :=
        sum_eq_zero fun i hi => by
          rw [hp (i + 1) (by omega) (by simp at hi; omega)]; rfl
      rw [hz, zero_add, hA.hasFPowerSeriesAt.coeff_zero]
    rwa [hfirst] at h
  -- array partial sums
  set arr : ℕ → Grid N → ℂ := fun n x => ((p n (fun _ => u x) : ℝ) : ℂ)
  have hlim : Tendsto (fun M => ∑ n ∈ range M, arr (n + m)) atTop
      (𝓝 (fun x => ((A (c + u x) - A c : ℝ) : ℂ))) := by
    rw [tendsto_pi_nhds]
    intro x
    have := ((hsum x).tendsto_sum_nat).ofReal
    simpa [arr, Finset.sum_apply] using this
  have hterm : ∀ n, sobNorm r (arr (n + m)) ≤ K / Al * (x0 ^ m * (1 / 2) ^ n) := by
    intro n
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 := sobNorm_multilinear_le r hr (n := n + m') b hB (p (n + (m' + 1))) u
    have hpn : ‖p (n + (m' + 1))‖ ≤ K / (ρ : ℝ) ^ (n + (m' + 1)) := by
      rw [le_div_iff₀ (by positivity)]; exact hKp _
    have hxn : x0 ^ (n + (m' + 1)) ≤ x0 ^ (m' + 1) * (1 / 2) ^ n := by
      rw [pow_add, mul_comm]
      gcongr
    calc sobNorm r (arr (n + (m' + 1)))
        ≤ ‖p (n + (m' + 1))‖ * B ^ (n + m' + 1) * Al ^ (n + m') * S ^ (n + m' + 1) := h1
      _ ≤ K / (ρ : ℝ) ^ (n + (m' + 1)) * B ^ (n + m' + 1) * Al ^ (n + m') *
            S ^ (n + m' + 1) := by gcongr
      _ = K / Al * x0 ^ (n + (m' + 1)) := by
          rw [hx0, div_pow, mul_pow, mul_pow, show n + (m' + 1) = n + m' + 1 by ring,
            pow_succ Al (n + m')]
          field_simp
          rw [mul_div_assoc, div_self hAl.ne', mul_one]
      _ ≤ K / Al * (x0 ^ (m' + 1) * (1 / 2) ^ n) := by gcongr
  have hbound : ∀ M, sobNorm r (∑ n ∈ range M, arr (n + m)) ≤
      2 * K / Al * (B * Al / ρ) ^ m * S ^ m := by
    intro M
    refine (sobNorm_sum_le r _ _).trans ?_
    refine (sum_le_sum fun n _ => hterm n).trans ?_
    rw [← mul_sum, ← mul_sum]
    have hg := sum_geometric_two_le M
    have hx0m : x0 ^ m = (B * Al / ρ) ^ m * S ^ m := by
      rw [hx0, ← mul_pow]; ring
    calc K / Al * (x0 ^ m * ∑ i ∈ range M, (1 / 2 : ℝ) ^ i) ≤ K / Al * (x0 ^ m * 2) := by
          gcongr
      _ = 2 * K / Al * (B * Al / ρ) ^ m * S ^ m := by rw [hx0m]; ring
  exact le_of_tendsto ((continuous_sobNorm r).tendsto _ |>.comp hlim)
    (Eventually.of_forall hbound)

/-- **Discrete Moser estimate** (`m = 1`): for `A : E → ℝ` with a power series at `c` and
`r ≥ 2`, there are mesh-independent `δ > 0`, `C ≥ 0` with
`‖A(c + u) - A(c)‖_{r,h} ≤ C S_r(u)` whenever `S_r(u) ≤ δ`. -/
theorem moser_composition (r : ℕ) (hr : 2 ≤ r) (b : Module.Basis ι ℝ E) {A : E → ℝ} {c : E}
    {p : FormalMultilinearSeries ℝ E ℝ} {R : ENNReal} (hA : HasFPowerSeriesOnBall A p c R) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (u : Grid N → E), coordSum r b u ≤ δ →
      sobNorm r (fun x => ((A (c + u x) - A c : ℝ) : ℂ)) ≤ C * coordSum r b u := by
  obtain ⟨δ, hδ, C, hC, h⟩ := moser_composition_order r hr b hA 1 le_rfl
    (fun n h1 h2 => absurd h2 (by omega))
  exact ⟨δ, hδ, C, hC, fun N _ u hu => by simpa using h N u hu⟩

/-- **Discrete Moser estimate for analytic maps** (`AnalyticAt` form). -/
theorem moser_analyticAt_order (r : ℕ) (hr : 2 ≤ r) (b : Module.Basis ι ℝ E) {A : E → ℝ}
    {c : E} (hA : AnalyticAt ℝ A c) (m : ℕ) (hm : 1 ≤ m)
    (hvan : ∀ p : FormalMultilinearSeries ℝ E ℝ, HasFPowerSeriesAt A p c →
      ∀ n, 0 < n → n < m → p n = 0) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (u : Grid N → E), coordSum r b u ≤ δ →
      sobNorm r (fun x => ((A (c + u x) - A c : ℝ) : ℂ)) ≤ C * coordSum r b u ^ m := by
  obtain ⟨p, R, hp⟩ := hA
  exact moser_composition_order r hr b hp m hm (hvan p hp.hasFPowerSeriesAt)


/-! ### Lipschitz form of the discrete Moser estimate -/

theorem coordArr_sub (b : Module.Basis ι ℝ E) (u w : Grid N → E) (j : ι) :
    coordArr b (u - w) j = coordArr b u j - coordArr b w j := by
  funext x; simp [coordArr]

/-- Coordinate expansion of a multilinear evaluation with different arguments. -/
theorem multilinear_eq {n : ℕ} (b : Module.Basis ι ℝ E)
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) (y : Fin n → E) :
    p y = ∑ ρ : Fin n → ι, (∏ k, b.repr (y k) (ρ k)) * p (fun k => b (ρ k)) := by
  conv_lhs => rw [show y = fun k => ∑ j, b.repr (y k) j • b j from
    funext fun k => (b.sum_repr (y k)).symm]
  rw [p.map_sum (fun k j => b.repr (y k) j • b j)]
  refine sum_congr rfl fun ρ _ => ?_
  rw [p.map_smul_univ (fun k => b.repr (y k) (ρ k)) (fun k => b (ρ k)), smul_eq_mul]

/-- **Multilinear bound, general slots**: `‖x ↦ p(u₀(x), …, u_n(x))‖_{r,h} ≤
‖p‖ B^{n+1} A_r^n Π_k S_r(u_k)`. -/
theorem sobNorm_multilinear_slots_le (r : ℕ) (hr : 2 ≤ r) {n : ℕ} (b : Module.Basis ι ℝ E)
    {B : ℝ} (hB : ∀ j, ‖b j‖ ≤ B) (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ)
    (u : Fin (n + 1) → Grid N → E) :
    sobNorm r (fun x => ((p (fun k => u k x) : ℝ) : ℂ)) ≤
      ‖p‖ * B ^ (n + 1) * algConst r ^ n * ∏ k, coordSum r b (u k) := by
  have harr : (fun x => ((p (fun k => u k x) : ℝ) : ℂ)) =
      ∑ ρ : Fin (n + 1) → ι, ((p (fun k => b (ρ k)) : ℝ) : ℂ) • ∏ k, coordArr b (u k) (ρ k) := by
    funext x
    rw [multilinear_eq b p (fun k => u k x)]
    simp only [Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, coordArr, smul_eq_mul]
    push_cast
    exact sum_congr rfl fun _ _ => by ring
  rw [harr]
  refine (sobNorm_sum_le r _ _).trans ?_
  have hterm : ∀ ρ : Fin (n + 1) → ι,
      sobNorm r (((p (fun k => b (ρ k)) : ℝ) : ℂ) • ∏ k, coordArr b (u k) (ρ k)) ≤
        ‖p‖ * B ^ (n + 1) * algConst r ^ n * ∏ k, sobNorm r (coordArr b (u k) (ρ k)) := by
    intro ρ
    rw [sobNorm_smul, Complex.norm_real]
    have h1 : ‖p (fun k => b (ρ k))‖ ≤ ‖p‖ * B ^ (n + 1) := by
      refine (p.le_opNorm _).trans ?_
      gcongr
      calc ∏ k, ‖b (ρ k)‖ ≤ ∏ _k : Fin (n + 1), B :=
            prod_le_prod (fun _ _ => norm_nonneg _) (fun k _ => hB (ρ k))
        _ = B ^ (n + 1) := by simp
    have h2 := sobNorm_prod_le r hr n (fun k => coordArr b (u k) (ρ k))
    calc ‖p (fun k => b (ρ k))‖ * sobNorm r (∏ k, coordArr b (u k) (ρ k))
        ≤ (‖p‖ * B ^ (n + 1)) * (algConst r ^ n * ∏ k, sobNorm r (coordArr b (u k) (ρ k))) :=
          mul_le_mul h1 h2 (sobNorm_nonneg _ _) ((norm_nonneg _).trans h1)
      _ = _ := by ring
  refine (sum_le_sum fun ρ _ => hterm ρ).trans (le_of_eq ?_)
  rw [← mul_sum]
  congr 1
  rw [← Fintype.prod_sum (fun k j => sobNorm r (coordArr b (u k) j))]
  rfl

theorem sum_succ_mul_half_pow_le (M : ℕ) : ∑ n ∈ range M, ((n : ℝ) + 1) * (1 / 2) ^ n ≤ 4 := by
  have key : ∀ M : ℕ, ∑ n ∈ range M, ((n : ℝ) + 1) * (1 / 2) ^ n =
      4 - (2 * M + 4) * (1 / 2) ^ M := by
    intro M
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [sum_range_succ, ih, pow_succ]; push_cast; ring
  rw [key]
  have : 0 ≤ (2 * (M : ℝ) + 4) * (1 / 2) ^ M := by positivity
  linarith

set_option maxHeartbeats 1000000 in
/-- **Discrete Moser estimate, Lipschitz form**: for `A : E → ℝ` with a power series at `c` and
`r ≥ 2` there are mesh-independent `δ > 0`, `C ≥ 0` such that for all arrays `u, w` with
`S_r(u), S_r(w) ≤ δ`, `‖A(c + u) - A(c + w)‖_{r,h} ≤ C S_r(u - w)`. -/
theorem moser_lipschitz (r : ℕ) (hr : 2 ≤ r) (b : Module.Basis ι ℝ E) {A : E → ℝ}
    {c : E} {p : FormalMultilinearSeries ℝ E ℝ} {R : ENNReal}
    (hA : HasFPowerSeriesOnBall A p c R) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (u w : Grid N → E), coordSum r b u ≤ δ →
      coordSum r b w ≤ δ →
      sobNorm r (fun x => ((A (c + u x) - A (c + w x) : ℝ) : ℂ)) ≤ C * coordSum r b (u - w) := by
  obtain ⟨ρ, hρ0, hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hA.r_pos
  obtain ⟨K, hK, hKp⟩ := p.norm_mul_pow_le_of_lt_radius (hρR.trans_le hA.r_le)
  set B : ℝ := 1 + ∑ j, ‖b j‖ with hBdef
  have hB : ∀ j, ‖b j‖ ≤ B := fun j => by
    have := single_le_sum (f := fun j => ‖b j‖) (fun _ _ => norm_nonneg _) (mem_univ j)
    linarith
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ∑ j, ‖b j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hρ0)
  set Al := algConst r
  have hAl := algConst_pos r
  set L : ℝ := B * (Al + Real.sqrt Kprod) with hLdef
  have hL : 0 < L := mul_pos (by linarith) (by positivity)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ρ / (2 * L) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  refine ⟨δ, hδ, 4 * K * B / ρ, by positivity, ?_⟩
  intro N _ u w hu hw
  set D := coordSum r b (u - w)
  have hD0 : 0 ≤ D := coordSum_nonneg r b (u - w)
  set x0 : ℝ := B * Al * δ / ρ with hx0
  have hx0nn : 0 ≤ x0 := by positivity
  have hx0le : x0 ≤ 1 / 2 := by
    rw [hx0, div_le_iff₀ hρ]
    have h1 : B * Al * δ ≤ L * δ := by
      rw [hLdef]; gcongr; linarith [Real.sqrt_nonneg Kprod]
    have h2 : L * δ = ρ / 2 := by rw [hδdef]; field_simp
    linarith
  have hpt : ∀ (v : Grid N → E), coordSum r b v ≤ δ → ∀ x, ‖v x‖ < ρ := by
    intro v hv x
    have h1 := norm_le_coordSum b hB v x
    have h2 : coordSum 2 b v ≤ δ := (coordSum_mono hr b v).trans hv
    have h3 : B * (Real.sqrt Kprod * coordSum 2 b v) ≤ L * δ := by
      rw [hLdef]
      have := Real.sqrt_nonneg Kprod
      have := coordSum_nonneg 2 b v
      calc B * (Real.sqrt Kprod * coordSum 2 b v) ≤ B * (Real.sqrt Kprod * δ) := by gcongr
        _ ≤ B * ((Al + Real.sqrt Kprod) * δ) := by gcongr; linarith
        _ = B * (Al + Real.sqrt Kprod) * δ := by ring
    have h4 : L * δ = ρ / 2 := by rw [hδdef]; field_simp
    linarith
  have hmem : ∀ (v : Grid N → E), coordSum r b v ≤ δ → ∀ x, v x ∈ Metric.eball (0 : E) R := by
    intro v hv x
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_le_of_lt ?_ hρR
    rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
    exact (hpt v hv x).le
  -- the difference series, shifted by one
  set dterm : ℕ → Grid N → ℂ := fun n x =>
    ((p (n + 1) (fun _ => u x) - p (n + 1) (fun _ => w x) : ℝ) : ℂ)
  have hsum : ∀ x, HasSum (fun n => p (n + 1) (fun _ => u x) - p (n + 1) (fun _ => w x))
      (A (c + u x) - A (c + w x)) := by
    intro x
    have h := (hA.hasSum (hmem u hu x)).sub (hA.hasSum (hmem w hw x))
    have h' := (hasSum_nat_add_iff' 1).mpr h
    have h0 : ∑ i ∈ range 1, (p i (fun _ => u x) - p i (fun _ => w x)) = 0 := by
      rw [sum_range_one, sub_eq_zero]
      congr 1
      funext k; exact k.elim0
    rwa [h0, sub_zero] at h'
  have hlim : Tendsto (fun M => ∑ n ∈ range M, dterm n) atTop
      (𝓝 (fun x => ((A (c + u x) - A (c + w x) : ℝ) : ℂ))) := by
    rw [tendsto_pi_nhds]
    intro x
    have := ((hsum x).tendsto_sum_nat).ofReal
    simpa [dterm, Finset.sum_apply] using this
  -- telescoping
  have hterm : ∀ n, sobNorm r (dterm n) ≤ K * B / ρ * ((n + 1) * x0 ^ n) * D := by
    intro n
    set slot : Fin (n + 1) → Fin (n + 1) → Grid N → E := fun i j =>
      if j < i then u else if i = j then u - w else w
    have harr : dterm n = ∑ i : Fin (n + 1),
        fun x => ((p (n + 1) (fun j => slot i j x) : ℝ) : ℂ) := by
      funext x
      have := (p (n + 1)).toMultilinearMap.map_sub_map_piecewise (fun _ => u x) (fun _ => w x)
        univ
      rw [Finset.piecewise_univ] at this
      simp only [dterm, Finset.sum_apply]
      rw [ContinuousMultilinearMap.coe_coe] at this
      rw [this]
      push_cast
      refine sum_congr rfl fun i _ => ?_
      congr 2
      funext j
      simp only [slot, mem_univ, true_implies]
      split_ifs <;> simp
    rw [harr]
    refine (sobNorm_sum_le r _ _).trans ?_
    have hslot : ∀ i : Fin (n + 1), ∏ j, coordSum r b (slot i j) ≤ D * δ ^ n := by
      intro i
      rw [Fin.prod_univ_succAbove _ i]
      have hi : coordSum r b (slot i i) = D := by
        show coordSum r b (if i < i then u else if i = i then u - w else w) = D
        rw [if_neg (lt_irrefl i), if_pos rfl]
      rw [hi]
      gcongr
      calc ∏ j : Fin n, coordSum r b (slot i (i.succAbove j)) ≤ ∏ _j : Fin n, δ :=
            prod_le_prod (fun _ _ => coordSum_nonneg _ _ _) (fun j _ => by
              simp only [slot]
              split_ifs with h1 h2
              · exact hu
              · exact absurd h2.symm (Fin.succAbove_ne i j)
              · exact hw)
        _ = δ ^ n := by simp
    have hpn : ‖p (n + 1)‖ ≤ K / (ρ : ℝ) ^ (n + 1) := by
      rw [le_div_iff₀ (by positivity)]; exact hKp _
    calc ∑ i : Fin (n + 1), sobNorm r (fun x => ((p (n + 1) (fun j => slot i j x) : ℝ) : ℂ))
        ≤ ∑ _i : Fin (n + 1), K / (ρ : ℝ) ^ (n + 1) * B ^ (n + 1) * Al ^ n * (D * δ ^ n) := by
          refine sum_le_sum fun i _ => ?_
          refine (sobNorm_multilinear_slots_le r hr b hB (p (n + 1)) (slot i)).trans ?_
          have := algConst_pos r
          have hp0 : 0 ≤ ∏ j, coordSum r b (slot i j) :=
            prod_nonneg fun _ _ => coordSum_nonneg _ _ _
          refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpn
            (by positivity)) (by positivity)) (hslot i) hp0 ?_
          have : 0 ≤ K / (ρ : ℝ) ^ (n + 1) := by positivity
          positivity
      _ = K * B / ρ * ((n + 1) * x0 ^ n) * D := by
          have e : x0 ^ n = B ^ n * Al ^ n * δ ^ n / (ρ : ℝ) ^ n := by
            rw [hx0, div_pow, mul_pow, mul_pow]
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, e, pow_succ (ρ : ℝ) n,
            pow_succ B n]
          push_cast
          field_simp
  have hbound : ∀ M, sobNorm r (∑ n ∈ range M, dterm n) ≤ 4 * K * B / ρ * D := by
    intro M
    refine (sobNorm_sum_le r _ _).trans ((sum_le_sum fun n _ => hterm n).trans ?_)
    rw [← sum_mul, ← mul_sum]
    have h1 : ∑ i ∈ range M, ((i : ℝ) + 1) * x0 ^ i ≤ ∑ i ∈ range M, ((i : ℝ) + 1) * (1 / 2) ^ i :=
      sum_le_sum fun i _ => by gcongr
    have h2 := sum_succ_mul_half_pow_le M
    have : 0 ≤ K * B / ρ := by positivity
    calc (K * B / ρ * ∑ i ∈ range M, ((i : ℝ) + 1) * x0 ^ i) * D
        ≤ K * B / ρ * 4 * D := by gcongr; linarith
      _ = 4 * K * B / ρ * D := by ring
  exact le_of_tendsto ((continuous_sobNorm r).tendsto _ |>.comp hlim)
    (Eventually.of_forall hbound)

end Multilinear

end Moser

end RenewalGeometry.PeriodicGridSobolev
