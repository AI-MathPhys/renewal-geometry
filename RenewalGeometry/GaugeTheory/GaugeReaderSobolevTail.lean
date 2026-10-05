/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.LatticeTorusPlancherel
import RenewalGeometry.Action.SobolevReaderCriterionExact

/-!
# The all-mode `H^q` reader from finite differences and the sharp tail (`app:gauge-reader`)

Clause-level infrastructure for `cor:gauge-robust-reader` (Einstein–SM action-closure manuscript,
last step of "Gauge-covariant realization of the weak-sector reader": "Parseval and the
discrete-difference symbol estimate then yield an all-mode `H^q` bound and, by
`eq:app-sharp-tail`, the tail estimate `eq:gauge-robust-tail`").

Setting: the periodic grid `(ℤ/n)⁴` (`n` nodes per direction, side `2π`, mesh `h = 2π/n`),
records `u` with values in a complex inner product space, the normalised DFT
`û(ℓ) = n⁻⁴ Σ_x e(-ℓ·x) u(x)` (`LatticeTorusPlancherel.dft`), the centred mode box
`Λ_h = {ℓ ∈ ℤ⁴ : |ℓ|_∞ ≤ (n-1)/2}` (`SobolevReader.box`), forward differences
`δ_j u(x) = h⁻¹(u(x + e_j) - u(x))` and the discrete `H^q` difference energy
`E_q(u) = Σ_{r ≤ q} Σ_{w ∈ {1..4}^r} ‖δ_{w_1} ⋯ δ_{w_r} u‖²_{2,h}`, `‖v‖²_{2,h} = h⁴ Σ_x ‖v(x)‖²`.

* `dft_fwdDiff`, `dft_iterDiff`: the difference symbol `σ_j(ℓ) = h⁻¹(e(ℓ_j) - 1)`;
* `norm_symbol_ge`: `|σ_j(ℓ)| ≥ (2/π)|ℓ_j|` for centred `|ℓ_j| ≤ n/2`, `h = 2π/n`;
* **`sobolevSq_le_diffEnergy`** (the all-mode `H^q` reader):
  `Σ_{ℓ ∈ Λ_h} (1 + |ℓ|²)^q ‖û(ℓ)‖² ≤ (π²/2)^q (2π)⁻⁴ E_q(u)`;
* **`tail_le_diffEnergy`** (`eq:gauge-robust-tail` from a difference bound):
  `τ_{h,m}(K) ≤ C_{q,m} K^{2-q} √E_q(u)` for `q > m + 2`, `1 ≤ K ≤ (n-1)/2`.

The gauge-covariant part of the corollary (link-independent covariant embeddings, the
normalised chain-rule hierarchy and the temporal-gauge Grönwall step, which produce the
ordinary-difference bound `E_q ≤ C` for the normalised record from the covariant jet energy) is
not formalised here.
-/

open Finset ComplexConjugate
open scoped Real

noncomputable section

namespace RenewalGeometry.GaugeReaderTail

open LatticeTorusPlancherel

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### Forward differences and their symbol -/

/-- The forward difference `δ_j u(x) = h⁻¹(u(x + e_j) - u(x))`. -/
def fwdDiff (h : ℝ) (j : Fin 4) (u : Grid 4 n → E) : Grid 4 n → E :=
  fun x => ((h⁻¹ : ℝ) : ℂ) • (u (x + Pi.single j 1) - u x)

/-- Iterated forward differences along a word. -/
def iterDiff (h : ℝ) : List (Fin 4) → (Grid 4 n → E) → Grid 4 n → E
  | [], u => u
  | j :: w, u => fwdDiff h j (iterDiff h w u)

/-- The difference symbol `σ_j(ℓ) = h⁻¹(e(ℓ_j) - 1)`. -/
def symbol (h : ℝ) (j : Fin 4) (ℓ : Grid 4 n) : ℂ :=
  ((h⁻¹ : ℝ) : ℂ) * ((ZMod.stdAddChar (ℓ j) : ℂ) - 1)

theorem dft_fwdDiff (h : ℝ) (j : Fin 4) (u : Grid 4 n → E) (ℓ : Grid 4 n) :
    dft (fwdDiff h j u) ℓ = symbol h j ℓ • dft u ℓ := by
  have e : fwdDiff h j u = ((h⁻¹ : ℝ) : ℂ) • (shift j u - u) := by
    funext x; simp [fwdDiff, shift]
  rw [e, dft_smul, dft_sub, dft_shift, symbol, mul_smul, sub_smul, one_smul]

theorem dft_iterDiff (h : ℝ) :
    ∀ (w : List (Fin 4)) (u : Grid 4 n → E) (ℓ : Grid 4 n),
      dft (iterDiff h w u) ℓ = (w.map fun j => symbol h j ℓ).prod • dft u ℓ
  | [], u, ℓ => by simp [iterDiff]
  | j :: w, u, ℓ => by
    rw [iterDiff, dft_fwdDiff, dft_iterDiff h w u ℓ, List.map_cons, List.prod_cons, mul_smul]

/-- `‖e(t) - 1‖ ≥ 4|t|/n` for an integer `|t| ≤ n/2`. -/
theorem norm_char_sub_one_ge (t : ℤ) (ht : 2 * |(t : ℝ)| ≤ n) :
    4 * |(t : ℝ)| / n ≤ ‖(ZMod.stdAddChar (t : ZMod n) : ℂ) - 1‖ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_intCast]
  have e : (2 * (π : ℂ) * Complex.I * (t : ℂ) / (n : ℂ)) =
      Complex.I * ((2 * π * t / n : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  set y := 2 * π * (t : ℝ) / n / 2 with hy
  have hy' : y = π * t / n := by rw [hy]; ring
  have hya : |y| ≤ π / 2 := by
    rw [hy', abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hn, div_le_div_iff₀ hn
      (by norm_num)]
    nlinarith [Real.pi_pos]
  have hsin : 2 / π * |y| ≤ |Real.sin y| := by
    rcases le_total 0 y with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0
        (by linarith [abs_of_nonneg h0 ▸ hya, Real.pi_pos]))]
      exact Real.mul_le_sin h0 (abs_of_nonneg h0 ▸ hya)
    · have hs : |Real.sin y| = Real.sin (-y) := by
        rw [Real.sin_neg, abs_of_nonpos]
        exact Real.sin_nonpos_of_nonpos_of_neg_pi_le h0
          (by linarith [abs_of_nonpos h0 ▸ hya, Real.pi_pos])
      rw [abs_of_nonpos h0, hs]
      exact Real.mul_le_sin (by linarith) (abs_of_nonpos h0 ▸ hya)
  have h2 : |y| = π * |(t : ℝ)| / n := by
    rw [hy', abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hn]
  rw [h2] at hsin
  calc 4 * |(t : ℝ)| / n = 2 * (2 / π * (π * |(t : ℝ)| / n)) := by
        field_simp; ring
    _ ≤ 2 * |Real.sin y| := by linarith

/-- **The difference-symbol estimate**: on the grid of side `2π` (`h = 2π/n`), for an integer
representative `t` of `ℓ_j` with `|t| ≤ n/2`, `|σ_j(ℓ)| ≥ (2/π)|t|`. -/
theorem norm_symbol_ge {h : ℝ} (hh : h = 2 * π / n) (j : Fin 4) (ℓ : Grid 4 n) (t : ℤ)
    (hℓ : ℓ j = (t : ZMod n)) (ht : 2 * |(t : ℝ)| ≤ n) :
    2 / π * |(t : ℝ)| ≤ ‖symbol h j ℓ‖ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [symbol, norm_mul, Complex.norm_real, Real.norm_eq_abs, hℓ, hh]
  have h1 := norm_char_sub_one_ge (n := n) t ht
  have hinv : |(2 * π / n)⁻¹| = n / (2 * π) := by
    rw [inv_div, abs_of_pos (div_pos hn (by positivity))]
  rw [hinv]
  calc 2 / π * |(t : ℝ)| = n / (2 * π) * (4 * |(t : ℝ)| / n) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (div_pos hn (by positivity)).le

/-! ### Centred modes and the all-mode `H^q` bound -/

open SobolevReader

/-- A centred integer mode as a frequency of the grid. -/
def castMode (ℓ : Mode) : Grid 4 n := fun μ => (ℓ μ : ZMod n)

/-- The DFT coefficients of a record on the centred modes. -/
def coefMode (u : Grid 4 n → E) (ℓ : Mode) : E := dft u (castMode ℓ)

/-- `‖v‖²_{2,h} = h⁴ Σ_x ‖v(x)‖²`. -/
def gridSq (h : ℝ) (v : Grid 4 n → E) : ℝ := h ^ 4 * ∑ x, ‖v x‖ ^ 2

/-- The discrete `H^q` difference energy `E_q(u) = Σ_{r ≤ q} Σ_{w ∈ {1..4}^r} ‖δ_w u‖²_{2,h}`. -/
def diffEnergy (h : ℝ) (q : ℕ) (u : Grid 4 n → E) : ℝ :=
  ∑ r ∈ range (q + 1), ∑ w : Fin r → Fin 4, gridSq h (iterDiff h (List.ofFn w) u)

theorem castMode_injOn {r : ℕ} (hr : 2 * r < n) : Set.InjOn (castMode (n := n)) (SobolevReader.box r) := by
  intro ℓ hℓ ℓ' hℓ' h
  funext μ
  have h1 := congrFun h μ
  simp only [castMode] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have hb : ∀ ν, |ℓ ν| ≤ r := fun ν => by
    have := Fintype.mem_piFinset.1 (show ℓ ∈ SobolevReader.box r from hℓ) ν
    rw [Finset.mem_Icc] at this; exact abs_le.2 this
  have hb' : ∀ ν, |ℓ' ν| ≤ r := fun ν => by
    have := Fintype.mem_piFinset.1 (show ℓ' ∈ SobolevReader.box r from hℓ') ν
    rw [Finset.mem_Icc] at this; exact abs_le.2 this
  have hlt : |ℓ' μ - ℓ μ| < n := by
    have := abs_sub (ℓ' μ) (ℓ μ)
    have h2 : (2 * r : ℤ) < n := by exact_mod_cast hr
    linarith [hb μ, hb' μ]
  have := Int.eq_zero_of_abs_lt_dvd h1 hlt
  linarith

/-- `(1 + s)^q ≤ (2/a)^q Σ_{r ≤ q} (a s)^r` for `s ≥ 0`, `0 < a ≤ 1`. -/
theorem one_add_pow_le_sum {s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (ha1 : a ≤ 1) (q : ℕ) :
    (1 + s) ^ q ≤ (2 / a) ^ q * ∑ r ∈ range (q + 1), (a * s) ^ r := by
  have hsum0 : ∀ r ∈ range (q + 1), 0 ≤ (a * s) ^ r := fun r _ => by positivity
  have h2a : 2 ≤ 2 / a := by rw [le_div_iff₀ ha]; linarith
  rcases le_total s 1 with h | h
  · have h1 : (1 + s) ^ q ≤ 2 ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
    have h3 : (1 : ℝ) ≤ ∑ r ∈ range (q + 1), (a * s) ^ r := by
      have := Finset.single_le_sum hsum0 (Finset.mem_range.2 (Nat.succ_pos q))
      simpa using this
    calc (1 + s) ^ q ≤ 2 ^ q := h1
      _ ≤ (2 / a) ^ q := pow_le_pow_left₀ (by norm_num) h2a q
      _ ≤ (2 / a) ^ q * ∑ r ∈ range (q + 1), (a * s) ^ r :=
          le_mul_of_one_le_right (by positivity) h3
  · have h1 : (1 + s) ^ q ≤ (2 * s) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
    have h3 : (a * s) ^ q ≤ ∑ r ∈ range (q + 1), (a * s) ^ r :=
      Finset.single_le_sum hsum0 (Finset.mem_range.2 (Nat.lt_succ_self q))
    calc (1 + s) ^ q ≤ (2 * s) ^ q := h1
      _ = (2 / a) ^ q * (a * s) ^ q := by rw [← mul_pow]; congr 1; field_simp
      _ ≤ (2 / a) ^ q * ∑ r ∈ range (q + 1), (a * s) ^ r :=
          mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The per-mode estimate: `(1 + |ℓ|²)^q ‖û(ℓ)‖² ≤ (π²/2)^q Σ_{r ≤ q} Σ_w ‖(δ_w u)^(ℓ)‖²`. -/
theorem mode_le {h : ℝ} (hh : h = 2 * π / n) {r : ℕ} (hr : 2 * r < n) {ℓ : Mode}
    (hℓ : ℓ ∈ SobolevReader.box r) (q : ℕ) (u : Grid 4 n → E) :
    (1 + l2sq ℓ) ^ q * ‖coefMode u ℓ‖ ^ 2 ≤ (π ^ 2 / 2) ^ q *
      ∑ r ∈ range (q + 1), ∑ w : Fin r → Fin 4,
        ‖dft (iterDiff h (List.ofFn w) u) (castMode ℓ)‖ ^ 2 := by
  set a : ℝ := 4 / π ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have hb : ∀ ν, 2 * |(ℓ ν : ℝ)| ≤ n := fun ν => by
    have := Fintype.mem_piFinset.1 (show ℓ ∈ SobolevReader.box r from hℓ) ν
    rw [Finset.mem_Icc] at this
    have h1 : |ℓ ν| ≤ r := abs_le.2 this
    have h2 : (2 * |ℓ ν| : ℤ) ≤ n := by
      have : (2 * r : ℤ) < n := by exact_mod_cast hr
      linarith
    have h3 : ((2 * |ℓ ν| : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at h3; exact h3
  set σ2 : Fin 4 → ℝ := fun j => ‖symbol h j (castMode (n := n) ℓ)‖ ^ 2 with hσ2
  have hσ : a * l2sq ℓ ≤ ∑ j, σ2 j := by
    rw [l2sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := norm_symbol_ge hh j (castMode ℓ) (ℓ j) rfl (hb j)
    have h0 : 0 ≤ 2 / π * |(ℓ j : ℝ)| := by positivity
    calc a * (ℓ j : ℝ) ^ 2 = (2 / π * |(ℓ j : ℝ)|) ^ 2 := by
          rw [ha, mul_pow, sq_abs]; ring
      _ ≤ σ2 j := pow_le_pow_left₀ h0 h1 2
  have hw : ∀ r' : ℕ, ∑ w : Fin r' → Fin 4,
      ‖dft (iterDiff h (List.ofFn w) u) (castMode ℓ)‖ ^ 2 =
        (∑ j, σ2 j) ^ r' * ‖coefMode u ℓ‖ ^ 2 := by
    intro r'
    rw [Fintype.sum_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [dft_iterDiff, norm_smul, mul_pow, List.map_ofFn, List.prod_ofFn, norm_prod,
      ← Finset.prod_pow]
    rfl
  simp_rw [hw]
  rw [← Finset.sum_mul, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hpi : (π ^ 2 / 2) = 2 / a := by rw [ha]; field_simp; norm_num
  rw [hpi]
  refine (one_add_pow_le_sum (l2sq_nonneg ℓ) ha0 ha1 q).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r' _ => ?_) (by positivity)
  exact pow_le_pow_left₀ (mul_nonneg ha0.le (l2sq_nonneg ℓ)) hσ r'

/-- **The all-mode `H^q` reader from finite differences**: on the grid of side `2π`
(`h = 2π/n`) and the centred box `|ℓ|_∞ ≤ r`, `2r < n`,
`Σ_ℓ (1 + |ℓ|²)^q ‖û(ℓ)‖² ≤ (π²/2)^q (2π)⁻⁴ E_q(u)`. -/
theorem sobolevSq_le_diffEnergy {h : ℝ} (hh : h = 2 * π / n) {r : ℕ} (hr : 2 * r < n)
    (q : ℕ) (u : Grid 4 n → E) :
    sobolevSq (SobolevReader.box r) q (coefMode u) ≤ (π ^ 2 / 2) ^ q / (2 * π) ^ 4 * diffEnergy h q u := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold sobolevSq
  simp_rw [Real.rpow_natCast]
  have hPars : ∀ v : Grid 4 n → E, ∑ ℓ' : Grid 4 n, ‖dft v ℓ'‖ ^ 2 =
      gridSq h v / (2 * π) ^ 4 := by
    intro v
    rw [sum_norm_dft_sq, gridSq, hh]
    field_simp
  calc ∑ ℓ ∈ SobolevReader.box r, (1 + l2sq ℓ) ^ q * ‖coefMode u ℓ‖ ^ 2
      ≤ ∑ ℓ ∈ SobolevReader.box r, (π ^ 2 / 2) ^ q * ∑ r' ∈ range (q + 1), ∑ w : Fin r' → Fin 4,
          ‖dft (iterDiff h (List.ofFn w) u) (castMode ℓ)‖ ^ 2 :=
        Finset.sum_le_sum fun ℓ hℓ => mode_le hh hr hℓ q u
    _ = (π ^ 2 / 2) ^ q * ∑ r' ∈ range (q + 1), ∑ w : Fin r' → Fin 4,
          ∑ ℓ ∈ SobolevReader.box r, ‖dft (iterDiff h (List.ofFn w) u) (castMode ℓ)‖ ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r' _ => Finset.sum_comm
    _ ≤ (π ^ 2 / 2) ^ q * ∑ r' ∈ range (q + 1), ∑ w : Fin r' → Fin 4,
          ∑ ℓ' : Grid 4 n, ‖dft (iterDiff h (List.ofFn w) u) ℓ'‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r' _ => Finset.sum_le_sum
          fun w _ => ?_) (by positivity)
        rw [← Finset.sum_image (f := fun ℓ' => ‖dft (iterDiff h (List.ofFn w) u) ℓ'‖ ^ 2)
          (castMode_injOn hr)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => sq_nonneg _
    _ = (π ^ 2 / 2) ^ q / (2 * π) ^ 4 * diffEnergy h q u := by
        simp_rw [hPars]
        rw [diffEnergy, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r' _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        ring

/-- **`eq:gauge-robust-tail` from a difference bound**: for `q > m + 2`, `1 ≤ K ≤ r`, `2r < n`
(e.g. `r = (n-1)/2` on the odd grid), the measured tail of the DFT record on the centred box
obeys `τ_{h,m}(K) ≤ C_{q,m} K^{2-q} √E_q(u)` with
`C_{q,m} = √(80·25^m/(2q - 2m - 4)) · √((π²/2)^q/(2π)⁴)`. -/
theorem tail_le_diffEnergy {h : ℝ} (hh : h = 2 * π / n) {r : ℕ} (hr : 2 * r < n) {q m K : ℕ}
    (hqm : (m : ℝ) + 2 < q) (hK : 1 ≤ K) (hKr : K ≤ r) (u : Grid 4 n → E) :
    tail (SobolevReader.box r) m K (coefMode u) ≤
      Real.sqrt (80 * 25 ^ m / (2 * q - 2 * m - 4)) * (K : ℝ) ^ (2 - (q : ℝ)) *
        Real.sqrt ((π ^ 2 / 2) ^ q / (2 * π) ^ 4 * diffEnergy h q u) := by
  refine (tail_le_sobolev (SobolevReader.box r) m K r q hqm hK hKr (fun ℓ hℓ => mem_box.1 hℓ)
    (coefMode u)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (sobolevSq_le_diffEnergy hh hr q u))
    (by positivity)

/-- Non-vacuity: the hypotheses of `tail_le_diffEnergy` hold on the odd grid `n = 5`
(`r = 2`, `K = 1`, `m = 1`, `q = 4`) for every `ℂ`-valued record. -/
example (u : Grid 4 5 → ℂ) :
    tail (SobolevReader.box 2) 1 1 (coefMode u) ≤
      Real.sqrt (80 * 25 ^ 1 / (2 * 4 - 2 * 1 - 4)) * ((1 : ℕ) : ℝ) ^ (2 - ((4 : ℕ) : ℝ)) *
        Real.sqrt ((π ^ 2 / 2) ^ 4 / (2 * π) ^ 4 * diffEnergy (2 * π / 5) 4 u) := by
  have := tail_le_diffEnergy (n := 5) (h := 2 * π / 5) (by norm_num) (r := 2) (by norm_num)
    (q := 4) (m := 1) (K := 1) (by norm_num) le_rfl (by norm_num) u
  simpa using this

end RenewalGeometry.GaugeReaderTail
