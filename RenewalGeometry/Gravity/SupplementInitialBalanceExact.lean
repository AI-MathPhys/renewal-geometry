/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact four-mode mean calibration
  (`lem:supp-initial-balance`, `eq:supp-initial-seed`,
  `eq:supp-initial-quadratic-mean`, `eq:supp-initial-balance-root`;
  emergent-spacetime manuscript)

On the odd grid `(hℤ/ℤ)³`, `N = 2m + 1 ≥ 3`, `h = 1/N`, with the transverse
trace-free directions `T_i` (two off-diagonal entries `1/√2`) and the seed
`u_* = ∑_i T_i cos(2π x_i)`, `p(ϑ) = -(2/3) κ I + ∑_i b_i T_i sin(2π x_i)`
(`eq:supp-initial-seed`), the quadratic Hamiltonian of the paper's proof,
`ℋ_h^{[2]}(u, π; N, β) = N (‖π‖_h² - ½‖tr π‖_h² + ¼ ∑_i ‖δ_i u‖_h²)
+ ∑_i β^i ⟨π, δ_i u⟩_h`, is affine in the lapse and shift; its mean jet
`Q_h = (-∂_N ℋ, ∂_β ℋ)` on the seed is computed exactly from the
orthogonality of the constant and unit Fourier modes on the odd grid.

* `sum_exp_eq_zero`, `sum_cos_eq_zero`, `sum_sin_eq_zero`, `sum_sin_sq`:
  roots-of-unity sums `∑_{a<N} e^{2πi m a/N} = 0` (`N ∤ m`) and
  `∑_{a<N} sin²(2πa/N) = N/2` for `N ≥ 3`.
* `sum_grid_sinMode_sq`, `sum_grid_sinMode_mul`: orthogonality of the unit
  modes on the grid `(Fin 3 → Fin N)`.
* `frob_T_T`, `frob_one_T`, `trace_T`: the `T_i` are orthonormal, trace-free
  and orthogonal to `I` for the Frobenius pairing.
* `quadHam`, `meanJet`, `quadHam_eq_affine`: the quadratic Hamiltonian and
  its lapse/shift coefficients.
* `meanJet_seed`: **`eq:supp-initial-quadratic-mean`** — with `δ_i` acting on
  the unit modes by the odd phase symbol (`δ_i cos(2πx_i) = -ω_h sin(2πx_i)`,
  `δ_j cos(2πx_i) = 0` for `j ≠ i`, packaged as the hypothesis
  `δ_i u_* = -ω_h sin(2πx_i) T_i`), the mean jet on the seed is
  `Q_h(ϑ) = (⅔κ² - ½∑b_i² - ⅜ω_h², -½ω_h b_1, -½ω_h b_2, -½ω_h b_3)`.
* `Qh_root`, `Qh_root_neg`, `Qh_expansion`, `Qh_hasFDerivAt`:
  **`eq:supp-initial-balance-root`** — the exact root `ϑ_h^* = (3ω_h/4, 0)`
  (and the opposite-sign second branch), the Jacobian
  `DQ_h(ϑ_h^*) = diag(ω_h, -ω_h/2, -ω_h/2, -ω_h/2)`.
* `omega_ge_four`, `jacobianInv_apply_bound`: `ω_h = 2h⁻¹ sin(πh) ≥ 4` for
  `h ≤ 1/2`, so the inverse Jacobian is uniformly bounded (entries `≤ 1/2`).

Scoping: the identification of the displayed `ℋ_h^{[2]}` with the quadratic
jet of the full retained action (the paper's assertion that the complete
link remainder is cubic at flat data) is the input of the paper's proof and
is not formalised; `ℋ_h^{[2]}` is taken as the definition.
-/

namespace RenewalGeometry
namespace InitialBalance

open Finset Real

noncomputable section

/-! ### Trigonometric sums on the odd grid -/

/-- Roots-of-unity sum: `∑_{a<N} exp(2πi m a/N) = 0` when `N ∤ m`. -/
theorem sum_exp_eq_zero (N m : ℕ) (hN : 0 < N) (hm : ¬ N ∣ m) :
    ∑ a ∈ range N, Complex.exp (2 * π * Complex.I * m * a / N) = 0 := by
  set ζ : ℂ := Complex.exp (2 * π * Complex.I * m / N) with hζ
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpow : ∀ a : ℕ, Complex.exp (2 * π * Complex.I * m * a / N) = ζ ^ a := by
    intro a
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1; ring
  have hζN : ζ ^ N = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    rw [show (N : ℂ) * (2 * π * Complex.I * m / N) = m * (2 * π * Complex.I) by
      field_simp]
    exact Complex.exp_nat_mul_two_pi_mul_I m
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [hζ, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    rw [div_eq_iff hN'] at hn
    have h3 : (m : ℂ) * (2 * π * Complex.I) = (n * N) * (2 * π * Complex.I) := by
      linear_combination hn
    have h4 : (m : ℂ) = n * N := mul_right_cancel₀ Complex.two_pi_I_ne_zero h3
    have hz : (m : ℤ) = n * N := by exact_mod_cast h4
    exact hm (Int.natCast_dvd_natCast.mp ⟨n, by rw [hz]; ring⟩)
  simp_rw [hpow]
  rw [geom_sum_eq hζ1, hζN, sub_self, zero_div]

theorem sum_cos_eq_zero (N m : ℕ) (hN : 0 < N) (hm : ¬ N ∣ m) :
    ∑ a ∈ range N, Real.cos (2 * π * m * a / N) = 0 := by
  have h := congrArg Complex.re (sum_exp_eq_zero N m hN hm)
  rw [Complex.re_sum, Complex.zero_re] at h
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast; ring

theorem sum_sin_eq_zero (N m : ℕ) (hN : 0 < N) (hm : ¬ N ∣ m) :
    ∑ a ∈ range N, Real.sin (2 * π * m * a / N) = 0 := by
  have h := congrArg Complex.im (sum_exp_eq_zero N m hN hm)
  rw [Complex.im_sum, Complex.zero_im] at h
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.exp_ofReal_mul_I_im]
  congr 2
  push_cast; ring

/-- `∑_{a<N} sin²(2πa/N) = N/2` for `N ≥ 3`. -/
theorem sum_sin_sq (N : ℕ) (hN : 3 ≤ N) :
    ∑ a ∈ range N, Real.sin (2 * π * a / N) ^ 2 = N / 2 := by
  have h2 : ¬ N ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hc := sum_cos_eq_zero N 2 (by omega) h2
  have hpt : ∀ a : ℕ, Real.sin (2 * π * a / N) ^ 2
      = 1 / 2 - Real.cos (2 * π * (2 : ℕ) * a / N) / 2 := by
    intro a
    rw [Real.sin_sq, Real.cos_sq, show 2 * π * ((2 : ℕ) : ℝ) * a / N = 2 * (2 * π * a / N) by
      push_cast; ring]
    ring
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.sum_div, hc]
  simp
  ring

/-! ### The grid and the unit modes -/

/-- The odd grid `(hℤ/ℤ)³` with `N` points per axis. -/
abbrev Grid (N : ℕ) := Fin 3 → Fin N

/-- The unit sine mode `sin(2π x_i)` at the grid point `x` (`x_i = a_i/N`). -/
def sinMode (N : ℕ) (i : Fin 3) (x : Grid N) : ℝ :=
  Real.sin (2 * π * ((x i : ℕ) : ℝ) / N)

/-- The unit cosine mode `cos(2π x_i)`. -/
def cosMode (N : ℕ) (i : Fin 3) (x : Grid N) : ℝ :=
  Real.cos (2 * π * ((x i : ℕ) : ℝ) / N)

theorem sum_fin_sin_sq (N : ℕ) (hN : 3 ≤ N) :
    ∑ a : Fin N, Real.sin (2 * π * ((a : ℕ) : ℝ) / N) ^ 2 = N / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => Real.sin (2 * π * (a : ℝ) / N) ^ 2) N]
  exact sum_sin_sq N hN

theorem sum_fin_sin (N : ℕ) (hN : 3 ≤ N) :
    ∑ a : Fin N, Real.sin (2 * π * ((a : ℕ) : ℝ) / N) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => Real.sin (2 * π * (a : ℝ) / N)) N]
  have h1 : ¬ N ∣ 1 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have := sum_sin_eq_zero N 1 (by omega) h1
  simpa using this

theorem card_grid (N : ℕ) : (Fintype.card (Grid N) : ℝ) = (N : ℝ) ^ 3 := by
  simp [Fintype.card_pi, Fintype.card_fin]

/-- `∑_x sin²(2π x_i) = N³/2`. -/
theorem sum_grid_sinMode_sq (N : ℕ) (hN : 3 ≤ N) (i : Fin 3) :
    ∑ x : Grid N, sinMode N i x ^ 2 = (N : ℝ) ^ 3 / 2 := by
  have hpt : ∀ x : Grid N, sinMode N i x ^ 2
      = ∏ k, (if k = i then Real.sin (2 * π * ((x k : ℕ) : ℝ) / N) ^ 2 else 1) := by
    intro x; rw [Finset.prod_ite_eq']; simp [sinMode]
  simp_rw [hpt]
  have hfac : (∑ x : Grid N, ∏ k, (if k = i then Real.sin (2 * π * ((x k : ℕ) : ℝ) / N) ^ 2
        else (1 : ℝ)))
      = ∏ k, ∑ a : Fin N, (if k = i then Real.sin (2 * π * ((a : ℕ) : ℝ) / N) ^ 2 else (1 : ℝ)) :=
    (Fintype.prod_sum fun k (a : Fin N) =>
      if k = i then Real.sin (2 * π * ((a : ℕ) : ℝ) / N) ^ 2 else (1 : ℝ)).symm
  rw [hfac]
  have hk : ∀ k : Fin 3, (∑ a : Fin N, if k = i then Real.sin (2 * π * ((a : ℕ) : ℝ) / N) ^ 2
      else (1 : ℝ)) = if k = i then (N : ℝ) / 2 else N := by
    intro k
    split_ifs
    · exact sum_fin_sin_sq N hN
    · simp
  simp_rw [hk]
  rw [Fin.prod_univ_three]
  fin_cases i <;> simp <;> ring

/-- `∑_x sin(2π x_i) sin(2π x_j) = 0` for `i ≠ j`. -/
theorem sum_grid_sinMode_mul (N : ℕ) (hN : 3 ≤ N) {i j : Fin 3} (hij : i ≠ j) :
    ∑ x : Grid N, sinMode N i x * sinMode N j x = 0 := by
  have hpt : ∀ x : Grid N, sinMode N i x * sinMode N j x
      = ∏ k, (if k = i ∨ k = j then Real.sin (2 * π * ((x k : ℕ) : ℝ) / N) else 1) := by
    intro x
    rw [Fin.prod_univ_three]
    unfold sinMode
    fin_cases i <;> fin_cases j <;> simp_all <;> ring
  simp_rw [hpt]
  have hfac : (∑ x : Grid N, ∏ k, (if k = i ∨ k = j then Real.sin (2 * π * ((x k : ℕ) : ℝ) / N)
        else (1 : ℝ)))
      = ∏ k, ∑ a : Fin N, (if k = i ∨ k = j then Real.sin (2 * π * ((a : ℕ) : ℝ) / N)
        else (1 : ℝ)) :=
    (Fintype.prod_sum fun k (a : Fin N) =>
      if k = i ∨ k = j then Real.sin (2 * π * ((a : ℕ) : ℝ) / N) else (1 : ℝ)).symm
  rw [hfac]
  have hk : ∀ k : Fin 3, (∑ a : Fin N, if k = i ∨ k = j then Real.sin (2 * π * ((a : ℕ) : ℝ) / N)
      else (1 : ℝ)) = if k = i ∨ k = j then (0 : ℝ) else (N : ℝ) := by
    intro k
    split_ifs
    · exact sum_fin_sin N hN
    · simp
  simp_rw [hk]
  rw [Fin.prod_univ_three]
  fin_cases i <;> fin_cases j <;> simp_all

/-! ### The transverse trace-free directions -/

/-- Frobenius pairing on `3 × 3` real matrices. -/
def frob (A B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- `1/√2`. -/
def c2 : ℝ := (Real.sqrt 2)⁻¹

theorem c2_mul_self : c2 * c2 = 1 / 2 := by
  unfold c2
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The directions `T_i ∈ Sym₃`: the two off-diagonal entries transverse to
`i` equal `1/√2`, all other entries zero (`eq:supp-initial-seed`). -/
def T : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ :=
  ![!![0, 0, 0; 0, 0, c2; 0, c2, 0], !![0, 0, c2; 0, 0, 0; c2, 0, 0],
    !![0, c2, 0; c2, 0, 0; 0, 0, 0]]

theorem frob_add_left (A B C : Matrix (Fin 3) (Fin 3) ℝ) :
    frob (A + B) C = frob A C + frob B C := by
  simp [frob, add_mul, Finset.sum_add_distrib]

theorem frob_add_right (A B C : Matrix (Fin 3) (Fin 3) ℝ) :
    frob A (B + C) = frob A B + frob A C := by
  simp [frob, mul_add, Finset.sum_add_distrib]

theorem frob_smul_left (r : ℝ) (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    frob (r • A) B = r * frob A B := by
  simp [frob, Finset.mul_sum, mul_assoc]

theorem frob_smul_right (r : ℝ) (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    frob A (r • B) = r * frob A B := by
  simp [frob, Finset.mul_sum, mul_left_comm]

theorem frob_T_T (i j : Fin 3) : frob (T i) (T j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [frob, T, Fin.sum_univ_three] <;>
    linear_combination (2 : ℝ) * c2_mul_self

theorem frob_one_T (i : Fin 3) : frob 1 (T i) = 0 := by
  fin_cases i <;> simp [frob, T, Fin.sum_univ_three, Matrix.one_apply]

theorem frob_T_one (i : Fin 3) : frob (T i) 1 = 0 := by
  fin_cases i <;> simp [frob, T, Fin.sum_univ_three, Matrix.one_apply]

theorem frob_one_one : frob (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 = 3 := by
  simp [frob, Matrix.one_apply]

theorem trace_T (i : Fin 3) : (T i).trace = 0 := by
  fin_cases i <;> simp [T, Matrix.trace, Fin.sum_univ_three]

/-! ### Seed, norms and the quadratic Hamiltonian -/

/-- The configuration seed `u_* = ∑_i T_i cos(2π x_i)`. -/
def uStar (N : ℕ) (x : Grid N) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ i, cosMode N i x • T i

/-- The momentum seed `p(ϑ) = -(2/3) κ I + ∑_i b_i T_i sin(2π x_i)`. -/
def pSeed (N : ℕ) (κ : ℝ) (b : Fin 3 → ℝ) (x : Grid N) : Matrix (Fin 3) (Fin 3) ℝ :=
  (-(2 / 3) * κ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) + ∑ i, (b i * sinMode N i x) • T i

/-- The grid pairing `⟨u, v⟩_h = h³ ∑_x u(x) : v(x)`, `h = 1/N`. -/
def gridInner (N : ℕ) (u v : Grid N → Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ((N : ℝ)⁻¹) ^ 3 * ∑ x, frob (u x) (v x)

/-- The grid norm `‖u‖_h²`. -/
def gridNormSq (N : ℕ) (u : Grid N → Matrix (Fin 3) (Fin 3) ℝ) : ℝ := gridInner N u u

/-- The scalar grid norm `‖f‖_h² = h³ ∑_x f(x)²`. -/
def scalarNormSq (N : ℕ) (f : Grid N → ℝ) : ℝ := ((N : ℝ)⁻¹) ^ 3 * ∑ x, f x ^ 2

/-- The quadratic Hamiltonian
`ℋ_h^{[2]}(u, π; N, β) = N (‖π‖_h² - ½‖tr π‖_h² + ¼∑_i ‖δ_i u‖_h²) + ∑_i β^i ⟨π, δ_i u⟩_h`
with constant lapse `N` and shift `β`, for phase derivatives `δ_i`. -/
def quadHam (N : ℕ) (δ : Fin 3 → (Grid N → Matrix (Fin 3) (Fin 3) ℝ) →
      (Grid N → Matrix (Fin 3) (Fin 3) ℝ))
    (u pm : Grid N → Matrix (Fin 3) (Fin 3) ℝ) (lapse : ℝ) (β : Fin 3 → ℝ) : ℝ :=
  lapse * (gridNormSq N pm - 1 / 2 * scalarNormSq N (fun x => (pm x).trace)
      + 1 / 4 * ∑ i, gridNormSq N (δ i u))
    + ∑ i, β i * gridInner N pm (δ i u)

/-- The mean jet `(-∂_N ℋ, ∂_β ℋ)`: the lapse and shift coefficients of the
affine function `ℋ_h^{[2]}(u, π; ·, ·)`. -/
def meanJet (N : ℕ) (δ : Fin 3 → (Grid N → Matrix (Fin 3) (Fin 3) ℝ) →
      (Grid N → Matrix (Fin 3) (Fin 3) ℝ))
    (u pm : Grid N → Matrix (Fin 3) (Fin 3) ℝ) : ℝ × (Fin 3 → ℝ) :=
  (-(gridNormSq N pm - 1 / 2 * scalarNormSq N (fun x => (pm x).trace)
      + 1 / 4 * ∑ i, gridNormSq N (δ i u)),
    fun i => gridInner N pm (δ i u))

/-- `ℋ_h^{[2]}` is affine in `(N, β)` with coefficients `(-Q₀, Q_i)`. -/
theorem quadHam_eq_affine (N : ℕ) (δ) (u pm : Grid N → Matrix (Fin 3) (Fin 3) ℝ)
    (lapse : ℝ) (β : Fin 3 → ℝ) :
    quadHam N δ u pm lapse β
      = lapse * (-(meanJet N δ u pm).1) + ∑ i, β i * (meanJet N δ u pm).2 i := by
  simp [quadHam, meanJet]

/-! ### The exact computation on the seed -/

section Seed

variable (N : ℕ) (κ ω : ℝ) (b : Fin 3 → ℝ)

theorem frob_pSeed_self (x : Grid N) :
    frob (pSeed N κ b x) (pSeed N κ b x)
      = 4 / 3 * κ ^ 2 + ∑ j, b j ^ 2 * sinMode N j x ^ 2 := by
  simp only [pSeed, Fin.sum_univ_three, frob_add_left, frob_add_right, frob_smul_left,
    frob_smul_right, frob_one_one, frob_one_T, frob_T_one, frob_T_T]
  simp
  ring

theorem trace_pSeed (x : Grid N) : (pSeed N κ b x).trace = -2 * κ := by
  simp [pSeed, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum, trace_T, Matrix.trace_one]
  ring

theorem frob_pSeed_T (x : Grid N) (i : Fin 3) :
    frob (pSeed N κ b x) ((-(ω * sinMode N i x)) • T i)
      = -(ω * b i) * sinMode N i x ^ 2 := by
  simp only [pSeed, Fin.sum_univ_three, frob_add_left, frob_smul_left, frob_smul_right,
    frob_one_T, frob_T_T]
  fin_cases i <;> simp <;> try ring

theorem gridNormSq_pSeed (hN : 3 ≤ N) :
    gridNormSq N (pSeed N κ b) = 4 / 3 * κ ^ 2 + 1 / 2 * ∑ j, b j ^ 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold gridNormSq gridInner
  simp_rw [frob_pSeed_self]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_grid,
    Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_grid_sinMode_sq N hN]
  rw [← Finset.sum_mul]
  field_simp
  try ring

theorem scalarNormSq_trace_pSeed (hN : 3 ≤ N) :
    scalarNormSq N (fun x => (pSeed N κ b x).trace) = 4 * κ ^ 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold scalarNormSq
  simp_rw [trace_pSeed]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_grid]
  field_simp
  ring

theorem gridNormSq_delta_uStar (hN : 3 ≤ N) (i : Fin 3) :
    gridNormSq N (fun x => (-(ω * sinMode N i x)) • T i) = ω ^ 2 / 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold gridNormSq gridInner
  simp only [frob_smul_left, frob_smul_right, frob_T_T, ite_true, mul_one]
  have : ∀ x : Grid N, -(ω * sinMode N i x) * -(ω * sinMode N i x) = ω ^ 2 * sinMode N i x ^ 2 :=
    fun x => by ring
  simp_rw [this]
  rw [← Finset.mul_sum, sum_grid_sinMode_sq N hN]
  field_simp
  try ring

theorem gridInner_pSeed_delta (hN : 3 ≤ N) (i : Fin 3) :
    gridInner N (pSeed N κ b) (fun x => (-(ω * sinMode N i x)) • T i) = -(ω / 2) * b i := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold gridInner
  simp_rw [frob_pSeed_T]
  rw [← Finset.mul_sum, sum_grid_sinMode_sq N hN]
  field_simp
  try ring

/-- **`eq:supp-initial-quadratic-mean`.** With the phase derivatives acting
on the seed by the odd symbol, `δ_i u_* = -ω_h sin(2πx_i) T_i`, the mean
jet of `ℋ_h^{[2]}` on the seed `(u_*, p(ϑ))` is
`Q_h(ϑ) = (⅔κ² - ½∑_i b_i² - ⅜ω_h², (-½ω_h b_i)_i)`. -/
theorem meanJet_seed (hN : 3 ≤ N)
    (δ : Fin 3 → (Grid N → Matrix (Fin 3) (Fin 3) ℝ) → (Grid N → Matrix (Fin 3) (Fin 3) ℝ))
    (hδ : ∀ i, δ i (uStar N) = fun x => (-(ω * sinMode N i x)) • T i) :
    meanJet N δ (uStar N) (pSeed N κ b)
      = (2 / 3 * κ ^ 2 - 1 / 2 * ∑ i, b i ^ 2 - 3 / 8 * ω ^ 2,
          fun i => -(ω / 2) * b i) := by
  unfold meanJet
  simp_rw [hδ]
  rw [gridNormSq_pSeed N κ b hN, scalarNormSq_trace_pSeed N κ b hN]
  simp_rw [gridNormSq_delta_uStar N ω hN, gridInner_pSeed_delta N κ ω b hN]
  simp only [Fin.sum_univ_three]
  refine Prod.ext ?_ rfl
  simp only
  ring

end Seed

/-! ### Root, Jacobian and uniform invertibility -/

/-- The mean jet as an explicit map of `ϑ = (κ, b)`
(`eq:supp-initial-quadratic-mean`). -/
def Qh (ω : ℝ) (ϑ : ℝ × (Fin 3 → ℝ)) : ℝ × (Fin 3 → ℝ) :=
  (2 / 3 * ϑ.1 ^ 2 - 1 / 2 * ∑ i, ϑ.2 i ^ 2 - 3 / 8 * ω ^ 2, fun i => -(ω / 2) * ϑ.2 i)

/-- The exact root `ϑ_h^* = (3ω_h/4, 0, 0, 0)` (`eq:supp-initial-balance-root`). -/
theorem Qh_root (ω : ℝ) : Qh ω (3 * ω / 4, 0) = 0 := by
  refine Prod.ext ?_ (funext fun i => ?_) <;> simp [Qh] <;> ring

/-- The second branch: the opposite sign of the first component. -/
theorem Qh_root_neg (ω : ℝ) : Qh ω (-(3 * ω / 4), 0) = 0 := by
  refine Prod.ext ?_ (funext fun i => ?_) <;> simp [Qh] <;> ring

/-- Exact expansion at the root: `Q_h(ϑ^* + (s, v)) = (ω s, -½ω v)` plus the
explicit quadratic remainder `(⅔s² - ½|v|², 0)`; the linear part is the
Jacobian `diag(ω, -ω/2, -ω/2, -ω/2)`. -/
theorem Qh_expansion (ω s : ℝ) (v : Fin 3 → ℝ) :
    Qh ω (3 * ω / 4 + s, v)
      = (ω * s + (2 / 3 * s ^ 2 - 1 / 2 * ∑ i, v i ^ 2), fun i => -(ω / 2) * v i) := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · simp only [Qh]; ring
  · simp only [Qh]

/-- The Jacobian `diag(ω, -ω/2, -ω/2, -ω/2)` as a continuous linear map. -/
def jacobian (ω : ℝ) : ℝ × (Fin 3 → ℝ) →L[ℝ] ℝ × (Fin 3 → ℝ) :=
  (ω • ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)).prod
    ((-(ω / 2)) • ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))

@[simp]
theorem jacobian_apply (ω : ℝ) (p : ℝ × (Fin 3 → ℝ)) :
    jacobian ω p = (ω * p.1, fun i => -(ω / 2) * p.2 i) := by
  refine Prod.ext ?_ (funext fun i => ?_) <;> simp [jacobian]

/-- **`eq:supp-initial-balance-root`, Jacobian.** `DQ_h(ϑ_h^*) = jacobian ω`. -/
theorem Qh_hasFDerivAt (ω : ℝ) : HasFDerivAt (Qh ω) (jacobian ω) (3 * ω / 4, 0) := by
  set x₀ : ℝ × (Fin 3 → ℝ) := (3 * ω / 4, 0) with hx₀
  -- first component
  have hA : HasFDerivAt (fun ϑ : ℝ × (Fin 3 → ℝ) => 2 / 3 * ϑ.1 ^ 2)
      (ω • ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)) x₀ := by
    refine ((hasFDerivAt_fst (𝕜 := ℝ) (p := x₀)).pow 2).const_mul (2 / 3) |>.congr_fderiv ?_
    ext p <;> simp [hx₀] <;> ring
  have hi : ∀ i : Fin 3, HasFDerivAt (fun ϑ : ℝ × (Fin 3 → ℝ) => ϑ.2 i ^ 2)
      (0 : ℝ × (Fin 3 → ℝ) →L[ℝ] ℝ) x₀ := by
    intro i
    refine (((hasFDerivAt_apply i x₀.2).comp x₀ (hasFDerivAt_snd (𝕜 := ℝ) (p := x₀))).pow 2)
      |>.congr_fderiv ?_
    ext p <;> simp [hx₀]
  have hB : HasFDerivAt (fun ϑ : ℝ × (Fin 3 → ℝ) => 1 / 2 * ∑ i, ϑ.2 i ^ 2)
      (0 : ℝ × (Fin 3 → ℝ) →L[ℝ] ℝ) x₀ := by
    refine (HasFDerivAt.sum (u := Finset.univ) fun i _ => hi i).const_mul (1 / 2) |>.congr_fderiv ?_
    simp
  have h1 : HasFDerivAt (fun ϑ : ℝ × (Fin 3 → ℝ) => 2 / 3 * ϑ.1 ^ 2 - 1 / 2 * ∑ i, ϑ.2 i ^ 2
      - 3 / 8 * ω ^ 2) (ω • ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)) x₀ := by
    refine ((hA.sub hB).sub_const (3 / 8 * ω ^ 2)).congr_fderiv ?_
    simp
  -- second component
  have h2 : HasFDerivAt (fun ϑ : ℝ × (Fin 3 → ℝ) => fun i => -(ω / 2) * ϑ.2 i)
      ((-(ω / 2)) • ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)) x₀ :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := x₀)).const_smul (-(ω / 2))
  exact h1.prodMk h2

/-- `ω_h = 2h⁻¹ sin(πh) ≥ 4` for `0 < h ≤ 1/2` (`sin(πh) ≥ 2h`). -/
theorem omega_ge_four (h : ℝ) (hh : 0 < h) (hh2 : h ≤ 1 / 2) :
    4 ≤ 2 * h⁻¹ * Real.sin (π * h) := by
  have hsin : 2 * h ≤ Real.sin (π * h) := by
    have := Real.mul_le_sin (x := π * h) (by positivity) (by nlinarith [Real.pi_pos])
    rw [show 2 / π * (π * h) = 2 * h by field_simp] at this
    exact this
  calc (4 : ℝ) = 2 * h⁻¹ * (2 * h) := by field_simp; ring
    _ ≤ 2 * h⁻¹ * Real.sin (π * h) := by gcongr

/-- The inverse Jacobian `diag(1/ω, -2/ω, -2/ω, -2/ω)`. -/
def jacobianInv (ω : ℝ) (y : ℝ × (Fin 3 → ℝ)) : ℝ × (Fin 3 → ℝ) :=
  (y.1 / ω, fun i => -(2 / ω) * y.2 i)

theorem jacobian_jacobianInv (ω : ℝ) (hω : ω ≠ 0) (y : ℝ × (Fin 3 → ℝ)) :
    jacobian ω (jacobianInv ω y) = y := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · simp [jacobianInv]; field_simp
  · simp [jacobianInv]; field_simp; try ring

/-- Uniform bound of the inverse Jacobian: for `ω ≥ 4` every entry of
`(DQ_h)⁻¹ y` is at most half the corresponding entry of `y`. -/
theorem jacobianInv_apply_bound (ω : ℝ) (hω : 4 ≤ ω) (y : ℝ × (Fin 3 → ℝ)) :
    |(jacobianInv ω y).1| ≤ 1 / 2 * |y.1| ∧
    ∀ i, |(jacobianInv ω y).2 i| ≤ 1 / 2 * |y.2 i| := by
  have hω0 : 0 < ω := by linarith
  constructor
  · simp only [jacobianInv, abs_div, abs_of_pos hω0]
    rw [div_le_iff₀ hω0]
    nlinarith [abs_nonneg y.1]
  · intro i
    simp only [jacobianInv, abs_mul, abs_neg, abs_div, abs_of_pos hω0, abs_two]
    rw [div_mul_eq_mul_div, div_le_iff₀ hω0]
    nlinarith [abs_nonneg (y.2 i)]

end

end InitialBalance
end RenewalGeometry
