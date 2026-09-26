/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# A sufficient nodal-accuracy condition for the measured spectral tail
  (`prop:native-rounding`, Einstein–Standard-Model action-closure manuscript)

On the periodic grid `Grid n = Fin 4 → ZMod n` we set up the normalized
four-dimensional discrete Fourier transform
`û(ℓ) = n⁻⁴ Σ_x e(-ℓ·x) u(x)` (`dft4`) with the product character
`e(ℓ·x) = ∏_μ stdAddChar (ℓ_μ x_μ)` (`char4`), prove the character
orthogonality `Σ_ℓ e(ℓ·x) = n⁴ [x = 0]` (`sum_char4`) and Parseval's identity
`Σ_ℓ ‖û(ℓ)‖² = n⁻⁴ Σ_x ‖u(x)‖²` (`sum_norm_dft4_sq`).

Modes are measured by centred representatives `ℓ_μ = (ℓ_μ).valMinAbs`, with
`|ℓ|₁ = Σ_μ |ℓ_μ|` (`l1`) and the tail set `|ℓ|_∞ > K` (`tailSet`); the
weighted measured tail `τ_{h,j}(K) = Σ_{|ℓ|_∞ > K} (1 + |ℓ|₁/K)^j ‖û(ℓ)‖`
of `eq:native-tail` is `tau`.

`tau_le_of_bandLimited_add` is `eq:native-rounding-tail`: if `u = u^b + e`
with `u^b` Fourier-supported in `|ℓ|_∞ ≤ K` and `max_x ‖e(x)‖ ≤ ε`, then with
`h = 2π/n` and `hK ≤ 1`,
`τ_{h,j}(K) ≤ (1 + 4π)^j · 4π² · ε · h⁻² (hK)⁻ʲ`,
i.e. `C_j = (1 + 4π)^j 4π²`.  `tau_le_of_tolerance` is the
`eq:native-rounding-tolerance` consequence `τ_{h,m} ≤ C · h K²`.
The fields are modelled as maps into a complex inner-product space `E`
(real-valued records embed in `ℂ^d`).
-/

open Finset ZMod ComplexConjugate

namespace RenewalGeometry
namespace NodalRounding

/-- The periodic four-dimensional grid / mode lattice with `n` nodes per direction. -/
abbrev Grid (n : ℕ) := Fin 4 → ZMod n

variable {n : ℕ} [NeZero n]

/-- The four-dimensional character `e(ℓ·x) = ∏_μ e(ℓ_μ x_μ)`. -/
noncomputable def char4 (ℓ x : Grid n) : ℂ := ∏ μ, stdAddChar (ℓ μ * x μ)

theorem char4_zero_right (ℓ : Grid n) : char4 ℓ 0 = 1 := by
  simp [char4]

theorem char4_add_right (ℓ x y : Grid n) : char4 ℓ (x + y) = char4 ℓ x * char4 ℓ y := by
  simp [char4, mul_add, AddChar.map_add_eq_mul, prod_mul_distrib]

theorem char4_neg_right (ℓ x : Grid n) : char4 ℓ (-x) = conj (char4 ℓ x) := by
  unfold char4
  rw [map_prod]
  refine prod_congr rfl fun μ _ => ?_
  rw [Pi.neg_apply, mul_neg, AddChar.map_neg_eq_inv, stdAddChar_apply, ← Circle.coe_inv,
    Circle.coe_inv_eq_conj]

theorem char4_sub_right (ℓ x y : Grid n) : char4 ℓ (x - y) = char4 ℓ x * conj (char4 ℓ y) := by
  rw [sub_eq_add_neg, char4_add_right, char4_neg_right]

/-- One-dimensional character orthogonality on `ZMod n`. -/
theorem sum_stdAddChar_mul (t : ZMod n) :
    ∑ i : ZMod n, stdAddChar (i * t) = if t = 0 then (n : ℂ) else 0 := by
  have h' : ∀ i : ZMod n, stdAddChar (i * t) = stdAddChar (t * i) := fun i => by rw [mul_comm]
  simp_rw [h']
  split_ifs with h
  · simp [h, card_univ, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar n h)

/-- Four-dimensional character orthogonality: `Σ_ℓ e(ℓ·x) = n⁴ [x = 0]`. -/
theorem sum_char4 (x : Grid n) :
    ∑ ℓ : Grid n, char4 ℓ x = if x = 0 then ((n : ℂ) ^ 4) else 0 := by
  unfold char4
  have hprod := Finset.prod_univ_sum (fun _ : Fin 4 => (univ : Finset (ZMod n)))
    (fun μ (k : ZMod n) => stdAddChar (k * x μ))
  rw [Fintype.piFinset_univ] at hprod
  rw [← hprod]
  simp_rw [sum_stdAddChar_mul]
  by_cases hx : x = 0
  · subst hx
    simp
  · obtain ⟨μ, hμ⟩ : ∃ μ, x μ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (funext hc)
    rw [ite_eq_right_iff.mpr (fun h => absurd h hx)]
    exact prod_eq_zero (mem_univ μ) (by simp [hμ])

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The normalized four-dimensional DFT `û(ℓ) = n⁻⁴ Σ_x e(-ℓ·x) u(x)`. -/
noncomputable def dft4 (u : Grid n → E) (ℓ : Grid n) : E :=
  ((n : ℂ) ^ 4)⁻¹ • ∑ x, conj (char4 ℓ x) • u x

theorem dft4_add (u v : Grid n → E) (ℓ : Grid n) :
    dft4 (u + v) ℓ = dft4 u ℓ + dft4 v ℓ := by
  simp [dft4, smul_add, sum_add_distrib]

theorem inner_dft4_self (u : Grid n → E) (ℓ : Grid n) :
    inner ℂ (dft4 u ℓ) (dft4 u ℓ) =
      (((n : ℂ) ^ 4)⁻¹) ^ 2 * ∑ x, ∑ y, char4 ℓ (x - y) * inner ℂ (u x) (u y) := by
  unfold dft4
  simp only [inner_smul_left, inner_smul_right, sum_inner, inner_sum, char4_sub_right,
    map_inv₀, map_pow, map_natCast, Complex.conj_conj, mul_sum]
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  ring

theorem sum_inner_dft4_self (u : Grid n → E) :
    ∑ ℓ, inner ℂ (dft4 u ℓ) (dft4 u ℓ) = ((n : ℂ) ^ 4)⁻¹ * ∑ x, inner ℂ (u x) (u x) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp_rw [inner_dft4_self]
  rw [← mul_sum, sum_comm]
  have hswap : ∀ x : Grid n, ∑ ℓ : Grid n, ∑ y, char4 ℓ (x - y) * inner ℂ (u x) (u y) =
      ∑ y, (∑ ℓ : Grid n, char4 ℓ (x - y)) * inner ℂ (u x) (u y) := by
    intro x
    rw [sum_comm]
    simp_rw [sum_mul]
  simp only [hswap, sum_char4, sub_eq_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ,
    ite_true]
  rw [← mul_sum]
  field_simp

/-- Parseval's identity for the normalized four-dimensional DFT. -/
theorem sum_norm_dft4_sq (u : Grid n → E) :
    ∑ ℓ, ‖dft4 u ℓ‖ ^ 2 = ((n : ℝ) ^ 4)⁻¹ * ∑ x, ‖u x‖ ^ 2 := by
  have h := sum_inner_dft4_self u
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

/-! ### Centred mode sizes, the tail set and the weighted tail -/

/-- `|ℓ|₁ = Σ_μ |ℓ_μ|` with centred representatives `|ℓ_μ| ≤ (n-1)/2`. -/
def l1 (ℓ : Grid n) : ℕ := ∑ μ, (ℓ μ).valMinAbs.natAbs

theorem l1_le (ℓ : Grid n) : (l1 ℓ : ℝ) ≤ 2 * n := by
  unfold l1
  push_cast
  have : ∀ μ : Fin 4, ((ℓ μ).valMinAbs.natAbs : ℝ) ≤ (n : ℝ) / 2 := by
    intro μ
    have h1 := ZMod.natAbs_valMinAbs_le (ℓ μ)
    have h2 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
    exact (Nat.cast_le.mpr h1).trans h2
  calc ∑ μ : Fin 4, ((ℓ μ).valMinAbs.natAbs : ℝ) ≤ ∑ _μ : Fin 4, (n : ℝ) / 2 :=
        sum_le_sum fun μ _ => this μ
    _ = 2 * n := by simp; ring

/-- The measured tail set `|ℓ|_∞ > K` (some centred component exceeds `K`). -/
noncomputable def tailSet (K : ℝ) : Finset (Grid n) :=
  univ.filter fun ℓ => ∃ μ, K < ((ℓ μ).valMinAbs.natAbs : ℝ)

/-- The weighted measured tail `τ_{h,j}(K) = Σ_{|ℓ|_∞ > K} (1 + |ℓ|₁/K)^j ‖û(ℓ)‖`
(`eq:native-tail`). -/
noncomputable def tau (K : ℝ) (j : ℕ) (u : Grid n → E) : ℝ :=
  ∑ ℓ ∈ tailSet K, (1 + (l1 ℓ : ℝ) / K) ^ j * ‖dft4 u ℓ‖

/-- Grid-spectrum weight bound: `(1 + |ℓ|₁/K)^j ≤ ((1 + 4π)/(hK))^j` when `h = 2π/n`, `hK ≤ 1`. -/
theorem weight_le (ℓ : Grid n) {K h : ℝ} (hK : 0 < K) (hh : h = 2 * Real.pi / n)
    (hhK : h * K ≤ 1) (j : ℕ) :
    (1 + (l1 ℓ : ℝ) / K) ^ j ≤ ((1 + 4 * Real.pi) / (h * K)) ^ j := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hhpos : 0 < h := by rw [hh]; positivity
  have hhK0 : 0 < h * K := mul_pos hhpos hK
  refine pow_le_pow_left₀ (by positivity) ?_ j
  have hl1 := l1_le ℓ
  rw [le_div_iff₀ hhK0]
  have hnh : (n : ℝ) * h = 2 * Real.pi := by
    rw [hh]
    field_simp
  have hl1h : (l1 ℓ : ℝ) * h ≤ 4 * Real.pi := by
    calc (l1 ℓ : ℝ) * h ≤ 2 * n * h := by gcongr
      _ = 4 * Real.pi := by rw [mul_assoc, hnh]; ring
  have hexp : (1 + (l1 ℓ : ℝ) / K) * (h * K) = h * K + (l1 ℓ : ℝ) * h := by
    field_simp
  rw [hexp]
  linarith

/-- The ℓ¹ sum of the Fourier coefficients is bounded by `n² · max_x ‖e(x)‖`
(Parseval and Cauchy–Schwarz over the `n⁴` modes). -/
theorem sum_norm_dft4_le (e : Grid n → E) {ε : ℝ} (he : ∀ x, ‖e x‖ ≤ ε) :
    ∑ ℓ, ‖dft4 e ℓ‖ ≤ (n : ℝ) ^ 2 * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (he 0)
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hcard : (Fintype.card (Grid n) : ℝ) = (n : ℝ) ^ 4 := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    push_cast
    ring
  have hcs : ∑ ℓ, ‖dft4 e ℓ‖ ≤
      Real.sqrt (∑ _ℓ : Grid n, (1 : ℝ) ^ 2) * Real.sqrt (∑ ℓ, ‖dft4 e ℓ‖ ^ 2) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Grid n)) (fun _ => (1 : ℝ))
      (fun ℓ => ‖dft4 e ℓ‖)
    simpa using this
  have hpar : ∑ ℓ, ‖dft4 e ℓ‖ ^ 2 ≤ ε ^ 2 := by
    rw [sum_norm_dft4_sq]
    calc ((n : ℝ) ^ 4)⁻¹ * ∑ x, ‖e x‖ ^ 2 ≤ ((n : ℝ) ^ 4)⁻¹ * ∑ _x : Grid n, ε ^ 2 := by
          gcongr with x _
          exact he x
      _ = ε ^ 2 := by
          rw [sum_const, card_univ, nsmul_eq_mul, hcard]
          field_simp
  calc ∑ ℓ, ‖dft4 e ℓ‖ ≤ Real.sqrt (∑ _ℓ : Grid n, (1 : ℝ) ^ 2) *
        Real.sqrt (∑ ℓ, ‖dft4 e ℓ‖ ^ 2) := hcs
    _ ≤ Real.sqrt ((n : ℝ) ^ 4) * Real.sqrt (ε ^ 2) := by
        gcongr
        rw [sum_const, card_univ, nsmul_eq_mul, hcard]
        simp
    _ = (n : ℝ) ^ 2 * ε := by
        rw [Real.sqrt_sq hε, show (n : ℝ) ^ 4 = ((n : ℝ) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]

/-- `prop:native-rounding`, `eq:native-rounding-tail`: if `u = u^b + e` with `u^b`
Fourier-supported in `|ℓ|_∞ ≤ K` and `max_x ‖e(x)‖ ≤ ε`, then for `h = 2π/n`, `hK ≤ 1`,
`τ_{h,j}(K) ≤ C_j ε h⁻² (hK)⁻ʲ` with `C_j = (1 + 4π)^j · 4π²`. -/
theorem tau_le_of_bandLimited_add {u ub e : Grid n → E} (hu : u = ub + e) {K : ℝ} (hK : 0 < K)
    (hb : ∀ ℓ ∈ tailSet K, dft4 ub ℓ = 0) {ε : ℝ} (he : ∀ x, ‖e x‖ ≤ ε) (j : ℕ) {h : ℝ}
    (hh : h = 2 * Real.pi / n) (hhK : h * K ≤ 1) :
    tau K j u ≤ ((1 + 4 * Real.pi) ^ j * (4 * Real.pi ^ 2)) * ε * h⁻¹ ^ 2 * (h * K)⁻¹ ^ j := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (he 0)
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hhpos : 0 < h := by rw [hh]; positivity
  have hhK0 : 0 < h * K := mul_pos hhpos hK
  set W : ℝ := ((1 + 4 * Real.pi) / (h * K)) ^ j with hW
  have hW0 : 0 ≤ W := by positivity
  have hcoef : ∀ ℓ ∈ tailSet K, dft4 u ℓ = dft4 e ℓ := by
    intro ℓ hℓ
    rw [hu, dft4_add, hb ℓ hℓ, zero_add]
  have h1 : tau K j u ≤ W * ∑ ℓ ∈ tailSet K, ‖dft4 e ℓ‖ := by
    unfold tau
    rw [mul_sum]
    refine sum_le_sum fun ℓ hℓ => ?_
    rw [hcoef ℓ hℓ]
    exact mul_le_mul_of_nonneg_right (weight_le ℓ hK hh hhK j) (norm_nonneg _)
  have h2 : ∑ ℓ ∈ tailSet K, ‖dft4 e ℓ‖ ≤ ∑ ℓ, ‖dft4 e ℓ‖ :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => norm_nonneg _
  have h3 := sum_norm_dft4_le e he
  have hn' : (n : ℝ) ^ 2 = 4 * Real.pi ^ 2 * h⁻¹ ^ 2 := by
    rw [hh]
    field_simp
    ring
  calc tau K j u ≤ W * ∑ ℓ ∈ tailSet K, ‖dft4 e ℓ‖ := h1
    _ ≤ W * ((n : ℝ) ^ 2 * ε) := by gcongr; exact h2.trans h3
    _ = ((1 + 4 * Real.pi) ^ j * (4 * Real.pi ^ 2)) * ε * h⁻¹ ^ 2 * (h * K)⁻¹ ^ j := by
        rw [hn', hW, div_pow, div_eq_mul_inv, ← inv_pow]
        ring

/-- `prop:native-rounding`, `eq:native-rounding-tolerance`: under the tolerance
`ε ≤ c h^{m+3} K^{m+2}` the measured tail obeys `τ_{h,m}(K) ≤ C_m c · h K²`. -/
theorem tau_le_of_tolerance {u ub e : Grid n → E} (hu : u = ub + e) {K : ℝ} (hK : 0 < K)
    (hb : ∀ ℓ ∈ tailSet K, dft4 ub ℓ = 0) {ε : ℝ} (he : ∀ x, ‖e x‖ ≤ ε) (m : ℕ) {h : ℝ}
    (hh : h = 2 * Real.pi / n) (hhK : h * K ≤ 1) {c : ℝ}
    (htol : ε ≤ c * h ^ (m + 3) * K ^ (m + 2)) :
    tau K m u ≤ ((1 + 4 * Real.pi) ^ m * (4 * Real.pi ^ 2)) * c * (h * K ^ 2) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hhpos : 0 < h := by rw [hh]; positivity
  have hC : 0 ≤ (1 + 4 * Real.pi) ^ m * (4 * Real.pi ^ 2) := by positivity
  refine (tau_le_of_bandLimited_add hu hK hb he m hh hhK).trans ?_
  have hh0 : h ≠ 0 := hhpos.ne'
  have hK0 : K ≠ 0 := hK.ne'
  have hid : c * h ^ (m + 3) * K ^ (m + 2) * h⁻¹ ^ 2 * (h * K)⁻¹ ^ m = c * (h * K ^ 2) := by
    rw [mul_inv, mul_pow, inv_pow, inv_pow, inv_pow]
    field_simp
    ring
  calc ((1 + 4 * Real.pi) ^ m * (4 * Real.pi ^ 2)) * ε * h⁻¹ ^ 2 * (h * K)⁻¹ ^ m
      ≤ ((1 + 4 * Real.pi) ^ m * (4 * Real.pi ^ 2)) * (c * h ^ (m + 3) * K ^ (m + 2)) *
          h⁻¹ ^ 2 * (h * K)⁻¹ ^ m := by gcongr
    _ = ((1 + 4 * Real.pi) ^ m * (4 * Real.pi ^ 2)) * c * (h * K ^ 2) := by
        rw [show ((1 + 4 * Real.pi) ^ m * (4 * Real.pi ^ 2)) * (c * h ^ (m + 3) * K ^ (m + 2)) *
          h⁻¹ ^ 2 * (h * K)⁻¹ ^ m = ((1 + 4 * Real.pi) ^ m * (4 * Real.pi ^ 2)) *
          (c * h ^ (m + 3) * K ^ (m + 2) * h⁻¹ ^ 2 * (h * K)⁻¹ ^ m) by ring, hid]
        ring

/-- `prop:native-rounding`, final clause: with `m = k + 2` and the tolerance
`ε ≤ c h^{m+3} K^{m+2}`, the second-order tail is `τ_{h,2}(K) ≤ C_2 c (h^k K^{k+1}) · hK`; on the
rate families `K ≍ h^{-β}` of `cor:native-rate` (`β < 1/(k+4)`, so `β(k+1) ≤ k`) the factor
`h^k K^{k+1}` is bounded, giving `τ_{h,2} = O(hK)`. -/
theorem tau_two_le_of_tolerance {u ub e : Grid n → E} (hu : u = ub + e) {K : ℝ} (hK : 0 < K)
    (hb : ∀ ℓ ∈ tailSet K, dft4 ub ℓ = 0) {ε : ℝ} (he : ∀ x, ‖e x‖ ≤ ε) (k : ℕ) {h : ℝ}
    (hh : h = 2 * Real.pi / n) (hhK : h * K ≤ 1) {c A : ℝ}
    (htol : ε ≤ c * h ^ (k + 2 + 3) * K ^ (k + 2 + 2)) (hfam : h ^ k * K ^ (k + 1) ≤ A) :
    tau K 2 u ≤ ((1 + 4 * Real.pi) ^ 2 * (4 * Real.pi ^ 2)) * c * A * (h * K) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hhpos : 0 < h := by rw [hh]; positivity
  have hC : 0 ≤ (1 + 4 * Real.pi) ^ 2 * (4 * Real.pi ^ 2) := by positivity
  have hε : 0 ≤ ε := (norm_nonneg _).trans (he 0)
  have hc : 0 ≤ c := by
    have hpos : 0 < h ^ (k + 2 + 3) * K ^ (k + 2 + 2) := by positivity
    by_contra hneg
    push Not at hneg
    have hlt := mul_neg_of_neg_of_pos hneg hpos
    have h' : c * h ^ (k + 2 + 3) * K ^ (k + 2 + 2) =
        c * (h ^ (k + 2 + 3) * K ^ (k + 2 + 2)) := by ring
    linarith
  refine (tau_le_of_bandLimited_add hu hK hb he 2 hh hhK).trans ?_
  have hh0 : h ≠ 0 := hhpos.ne'
  have hK0 : K ≠ 0 := hK.ne'
  have hid : c * h ^ (k + 2 + 3) * K ^ (k + 2 + 2) * h⁻¹ ^ 2 * (h * K)⁻¹ ^ 2 =
      c * (h ^ k * K ^ (k + 1)) * (h * K) := by
    field_simp
    ring
  calc ((1 + 4 * Real.pi) ^ 2 * (4 * Real.pi ^ 2)) * ε * h⁻¹ ^ 2 * (h * K)⁻¹ ^ 2
      ≤ ((1 + 4 * Real.pi) ^ 2 * (4 * Real.pi ^ 2)) *
          (c * h ^ (k + 2 + 3) * K ^ (k + 2 + 2)) * h⁻¹ ^ 2 * (h * K)⁻¹ ^ 2 := by gcongr
    _ = ((1 + 4 * Real.pi) ^ 2 * (4 * Real.pi ^ 2)) * c * (h ^ k * K ^ (k + 1)) * (h * K) := by
        rw [show ((1 + 4 * Real.pi) ^ 2 * (4 * Real.pi ^ 2)) *
          (c * h ^ (k + 2 + 3) * K ^ (k + 2 + 2)) * h⁻¹ ^ 2 * (h * K)⁻¹ ^ 2 =
          ((1 + 4 * Real.pi) ^ 2 * (4 * Real.pi ^ 2)) *
          (c * h ^ (k + 2 + 3) * K ^ (k + 2 + 2) * h⁻¹ ^ 2 * (h * K)⁻¹ ^ 2) by ring, hid]
        ring
    _ ≤ ((1 + 4 * Real.pi) ^ 2 * (4 * Real.pi ^ 2)) * c * A * (h * K) := by
        gcongr

end NodalRounding
end RenewalGeometry
