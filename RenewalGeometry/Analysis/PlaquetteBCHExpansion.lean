/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.NormedAlgebraLogBCH

/-!
# Second-order BCH without a unital norm, and the four-link plaquette expansion
(infrastructure for `thm:main-literal-link-compactness`, `eq:supp-literal-magnetic-limit`;
emergent-spacetime manuscript)

`Analysis/NormedAlgebraLogBCH.lean` proves the second-order BCH bound in a complete normed
algebra with `‖1‖ = 1`.  The literal-link records use the Frobenius norm on `n × n` matrices,
for which `‖1‖ = √n`.  Here:

* `PlaquetteBCH.lreg`: the left-regular representation `x ↦ (y ↦ x y)` of a complete normed
  `ℝ`-algebra `𝔸` into the bounded operators `𝔸 →L[ℝ] 𝔸` (a continuous ring hom into an algebra
  with `‖1‖ = 1`), with `‖lreg x‖ ≤ ‖x‖ ≤ ‖1‖ ‖lreg x‖`; it commutes with `exp`, ordered
  products of exponentials, the commutator term and the Mercator logarithm.
* `PlaquetteBCH.norm_log_expProd_sub_bch_le'`: for **any** complete normed `ℝ`-algebra (no
  `NormOneClass`), `s = ∑ ‖xᵢ‖ ≤ 1/4` gives
  `‖log(e^{x₁} ⋯ e^{x_m}) − (∑ xᵢ + ½ ∑_{i<j}[xᵢ,xⱼ])‖ ≤ 6 κ s³`, `κ = max ‖1‖ 1`.
* `PlaquetteBCH.plaquette_expansion`: the **four-link plaquette expansion**
  `U_p = e^{h a} e^{h b'} e^{−h a'} e^{−h b}` (`a = A_i(x)`, `b' = A_j(x+e_i)`, `a' = A_i(x+e_j)`,
  `b = A_j(x)`): the `h⁻²` logarithmic plaquette coefficient satisfies
  `‖h⁻² log U_p − (h⁻¹((b' − b) − (a' − a)) + [a, b])‖
     ≤ 2(‖a'−a‖ + ‖b'−b‖)(‖a‖ + ‖b‖ + ‖a'−a‖ + ‖b'−b‖) + 6κ h (‖a‖+‖b‖+‖a'‖+‖b'‖)³`
  whenever `h(‖a‖+‖b‖+‖a'‖+‖b'‖) ≤ 1/4`: linear part the discrete curl, quadratic part the
  commutator, translation errors and a cubic remainder (the pointwise algebra behind
  `eq:supp-literal-magnetic-limit`).
* `PlaquetteBCH.plaquetteRecord`, `PlaquetteBCH.norm_plaquetteRecord_sub_le`: the same on an
  additive lattice `G` with forward differences `D⁺_i u(x) = h⁻¹(u(x+e_i) − u(x))`:
  `‖F_{ij}(x) − (D⁺_i A_j − D⁺_j A_i + [A_i, A_j])(x)‖
     ≤ 2h(‖D⁺_jA_i‖ + ‖D⁺_iA_j‖)(‖A_i‖ + ‖A_j‖ + h‖D⁺_jA_i‖ + h‖D⁺_iA_j‖) + 6κh(…)³`,
  under the identity chart `h(‖A_i(x)‖ + ‖A_j(x)‖ + ‖A_i(x+e_j)‖ + ‖A_j(x+e_i)‖) ≤ 1/4`
  (implied by `h‖A‖ ≤ δ_* ≤ 1/16`).
-/

namespace RenewalGeometry.LogBCH.PlaquetteBCH

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-! ### The left-regular representation -/

/-- Left-regular representation `x ↦ (y ↦ x y)` as a ring hom into bounded operators. -/
noncomputable def lreg : 𝔸 →+* (𝔸 →L[ℝ] 𝔸) where
  toFun x := ContinuousLinearMap.mul ℝ 𝔸 x
  map_one' := by ext y; simp
  map_mul' x y := by ext z; simp [mul_assoc]
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

theorem lreg_apply (x y : 𝔸) : lreg x y = x * y := rfl

theorem lreg_eq (x : 𝔸) : lreg x = ContinuousLinearMap.mul ℝ 𝔸 x := rfl

theorem lreg_smul (c : ℝ) (x : 𝔸) : lreg (c • x) = c • lreg x := by
  ext y; simp [lreg_apply]

theorem continuous_lreg : Continuous (lreg : 𝔸 → (𝔸 →L[ℝ] 𝔸)) :=
  (ContinuousLinearMap.mul ℝ 𝔸).continuous

theorem norm_lreg_le (x : 𝔸) : ‖lreg x‖ ≤ ‖x‖ := ContinuousLinearMap.opNorm_mul_apply_le ℝ 𝔸 x

theorem norm_le_norm_one_mul_norm_lreg (x : 𝔸) : ‖x‖ ≤ ‖(1 : 𝔸)‖ * ‖lreg x‖ := by
  have h := (lreg x).le_opNorm 1
  rw [lreg_apply, mul_one] at h
  linarith [mul_comm ‖lreg x‖ ‖(1 : 𝔸)‖]

theorem lreg_exp (x : 𝔸) : lreg (exp x) = exp (lreg x) :=
  map_exp_of_mem_ball (𝕂 := ℝ) lreg continuous_lreg x
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

theorem lreg_expProd (L : List 𝔸) : lreg (expProd L) = expProd (L.map lreg) := by
  induction L with
  | nil => simp [expProd]
  | cons x L ih =>
    simp only [expProd, List.map_cons, List.prod_cons, map_mul, lreg_exp] at ih ⊢
    rw [ih]

theorem lreg_sum (L : List 𝔸) : lreg L.sum = (L.map lreg).sum := map_list_sum lreg L

theorem lreg_commTerm (L : List 𝔸) : lreg (commTerm L) = commTerm (L.map lreg) := by
  induction L with
  | nil => simp [commTerm]
  | cons x L ih =>
    simp only [commTerm, List.map_cons, map_add, lreg_smul, map_sub, map_mul, lreg_sum, ih]

theorem normSum_cons' (x : 𝔸) (L : List 𝔸) : normSum (x :: L) = ‖x‖ + normSum L := by
  simp [normSum]

theorem normSum_nonneg' (L : List 𝔸) : 0 ≤ normSum L := by
  induction L with
  | nil => simp [normSum]
  | cons x L ih => rw [normSum_cons']; exact add_nonneg (norm_nonneg _) ih

theorem normSum_map_lreg_le (L : List 𝔸) : normSum (L.map lreg) ≤ normSum L := by
  induction L with
  | nil => simp [normSum]
  | cons x L ih =>
    rw [List.map_cons, normSum_cons', normSum_cons']
    exact add_le_add (norm_lreg_le x) ih

theorem lreg_logTerm (Y : 𝔸) (n : ℕ) : lreg (logTerm Y n) = logTerm (lreg Y) n := by
  simp [logTerm, lreg_smul, map_pow]

/-! ### BCH in an arbitrary complete normed algebra -/

/-- `‖expProd L − 1‖ < 1` for `∑ ‖xᵢ‖ ≤ 1/4` (unital-norm algebras). -/
theorem norm_expProd_sub_one_lt {𝔹 : Type*} [NormedRing 𝔹] [NormedAlgebra ℝ 𝔹] [NormOneClass 𝔹]
    [CompleteSpace 𝔹] (L : List 𝔹) (hs : normSum L ≤ 1 / 4) : ‖expProd L - 1‖ < 1 := by
  set s := normSum L
  have hs0 : 0 ≤ s := normSum_nonneg L
  have hE := norm_expProd_sub_le L
  have h2 := norm_secondOrder_le L
  have hS := norm_sum_le_normSum L
  have hes : Real.exp s ≤ 3 := by
    have := Real.exp_le_exp.2 (show s ≤ 1 by linarith)
    have h1 := Real.exp_one_lt_d9
    linarith
  have e : expProd L - 1 = L.sum + secondOrder L + (expProd L - (1 + L.sum + secondOrder L)) := by
    abel
  rw [e]
  have h3 : s ^ 3 * Real.exp s ≤ s ^ 3 * 3 := mul_le_mul_of_nonneg_left hes (by positivity)
  have n1 := norm_add_le (L.sum + secondOrder L) (expProd L - (1 + L.sum + secondOrder L))
  have n2 := norm_add_le L.sum (secondOrder L)
  have h4 : s ^ 3 * 3 ≤ 3 / 64 := by
    have : s ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ hs0 hs 3
    linarith
  have h5 : s ^ 2 / 2 ≤ 1 / 32 := by
    have : s ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hs0 hs 2
    linarith
  linarith

/-- **Second-order BCH without `‖1‖ = 1`**: in any complete normed `ℝ`-algebra, if
`s = ∑ ‖xᵢ‖ ≤ 1/4` then `‖log(e^{x₁} ⋯ e^{x_m}) − (∑ xᵢ + ½∑_{i<j}[xᵢ,xⱼ])‖ ≤ 6 κ s³` with
`κ = max ‖1‖ 1` (e.g. `κ = √n` for the Frobenius norm on `n × n` matrices). -/
theorem norm_log_expProd_sub_bch_le' (L : List 𝔸) (hs : normSum L ≤ 1 / 4) :
    ‖logOnePlus (expProd L - 1) - (L.sum + commTerm L)‖
      ≤ 6 * max ‖(1 : 𝔸)‖ 1 * normSum L ^ 3 := by
  rcases subsingleton_or_nontrivial 𝔸 with h𝔸 | h𝔸
  · rw [Subsingleton.elim (logOnePlus (expProd L - 1) - (L.sum + commTerm L)) 0, norm_zero]
    have := normSum_nonneg' L
    positivity
  set L' := L.map lreg
  have hs' : normSum L' ≤ 1 / 4 := (normSum_map_lreg_le L).trans hs
  set Y := expProd L - 1
  have hY' : lreg Y = expProd L' - 1 := by simp [Y, L', map_sub, lreg_expProd]
  have hr : ‖lreg Y‖ < 1 := by rw [hY']; exact norm_expProd_sub_one_lt L' hs'
  -- summability of the Mercator series in `𝔸`
  have hsum : Summable (logTerm Y) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg _) hr).mul_left (‖(1 : 𝔸)‖ * ‖lreg Y‖))
      fun n => ?_
    calc ‖logTerm Y n‖ ≤ ‖(1 : 𝔸)‖ * ‖lreg (logTerm Y n)‖ := norm_le_norm_one_mul_norm_lreg _
      _ = ‖(1 : 𝔸)‖ * ‖logTerm (lreg Y) n‖ := by rw [lreg_logTerm]
      _ ≤ ‖(1 : 𝔸)‖ * ‖lreg Y‖ ^ (n + 1) := by
          gcongr; exact norm_logTerm_le _ n
      _ = ‖(1 : 𝔸)‖ * ‖lreg Y‖ * ‖lreg Y‖ ^ n := by ring
  have hlog : lreg (logOnePlus Y) = logOnePlus (lreg Y) := by
    rw [logOnePlus, lreg_eq, ContinuousLinearMap.map_tsum _ hsum, logOnePlus]
    congr 1; funext n; exact lreg_logTerm Y n
  have key := norm_log_expProd_sub_bch_le L' hs'
  have hmap : lreg (logOnePlus Y - (L.sum + commTerm L))
      = logOnePlus (expProd L' - 1) - (L'.sum + commTerm L') := by
    rw [map_sub, hlog, hY', map_add, lreg_sum, lreg_commTerm]
  calc ‖logOnePlus Y - (L.sum + commTerm L)‖
      ≤ ‖(1 : 𝔸)‖ * ‖lreg (logOnePlus Y - (L.sum + commTerm L))‖ :=
        norm_le_norm_one_mul_norm_lreg _
    _ ≤ max ‖(1 : 𝔸)‖ 1 * (6 * normSum L' ^ 3) := by
        rw [hmap]; gcongr
        · exact le_max_left _ _
    _ ≤ max ‖(1 : 𝔸)‖ 1 * (6 * normSum L ^ 3) := by
        have := normSum_nonneg' L'
        gcongr
        exact normSum_map_lreg_le L
    _ = 6 * max ‖(1 : 𝔸)‖ 1 * normSum L ^ 3 := by ring

/-! ### The four-link plaquette -/

/-- The commutator term of the plaquette list `[a, b', −a', −b]`. -/
theorem commTerm_plaquette (a b a' b' : 𝔸) :
    commTerm [a, b', -a', -b]
      = (a * b - b * a) + ((a * (b' - b) - (b' - b) * a)
        - (1 / 2 : ℝ) • (a * (a' - a) - (a' - a) * a)
        + ((a' - a) * b - b * (a' - a))
        - (1 / 2 : ℝ) • ((b' - b) * (a' - a) - (a' - a) * (b' - b))
        - (1 / 2 : ℝ) • ((b' - b) * b - b * (b' - b))) := by
  simp only [commTerm, List.sum_cons, List.sum_nil, add_zero]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, smul_add, smul_sub, smul_neg,
    mul_zero, zero_mul]
  module

theorem norm_comm_le (x y : 𝔸) : ‖x * y - y * x‖ ≤ 2 * (‖x‖ * ‖y‖) := by
  calc ‖x * y - y * x‖ ≤ ‖x * y‖ + ‖y * x‖ := norm_sub_le _ _
    _ ≤ ‖x‖ * ‖y‖ + ‖y‖ * ‖x‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * (‖x‖ * ‖y‖) := by ring

/-- The translation part of the plaquette commutator term is bounded by
`2(‖p‖ + ‖q‖)(‖a‖ + ‖b‖ + ‖p‖ + ‖q‖)` with `p = a' − a`, `q = b' − b`. -/
theorem norm_commTerm_plaquette_sub_le (a b a' b' : 𝔸) :
    ‖commTerm [a, b', -a', -b] - (a * b - b * a)‖
      ≤ 2 * (‖a' - a‖ + ‖b' - b‖) * (‖a‖ + ‖b‖ + ‖a' - a‖ + ‖b' - b‖) := by
  rw [commTerm_plaquette, add_sub_cancel_left]
  set p := a' - a
  set q := b' - b
  have h1 := norm_comm_le a q
  have h2 := norm_comm_le a p
  have h3 := norm_comm_le p b
  have h4 := norm_comm_le q p
  have h5 := norm_comm_le q b
  have hp := norm_nonneg p
  have hq := norm_nonneg q
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hh : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  have k1 := mul_nonneg hp hq
  have k2 := mul_nonneg hp hp
  have k3 := mul_nonneg hq hq
  have k4 := mul_nonneg ha hp
  have k5 := mul_nonneg hb hq
  calc ‖(a * q - q * a) - (1 / 2 : ℝ) • (a * p - p * a) + (p * b - b * p)
        - (1 / 2 : ℝ) • (q * p - p * q) - (1 / 2 : ℝ) • (q * b - b * q)‖
      ≤ ‖a * q - q * a‖ + 1 / 2 * ‖a * p - p * a‖ + ‖p * b - b * p‖
        + 1 / 2 * ‖q * p - p * q‖ + 1 / 2 * ‖q * b - b * q‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl
          (by rw [norm_smul, hh]))) le_rfl)) (by rw [norm_smul, hh]))) (by rw [norm_smul, hh]))
    _ ≤ 2 * (‖a‖ * ‖q‖) + 1 / 2 * (2 * (‖a‖ * ‖p‖)) + 2 * (‖p‖ * ‖b‖)
        + 1 / 2 * (2 * (‖q‖ * ‖p‖)) + 1 / 2 * (2 * (‖q‖ * ‖b‖)) := by gcongr
    _ ≤ 2 * (‖p‖ + ‖q‖) * (‖a‖ + ‖b‖ + ‖p‖ + ‖q‖) := by nlinarith

/-- **Four-link plaquette expansion** (pointwise algebra of `eq:supp-literal-magnetic-limit`):
for `h > 0` and `h(‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) ≤ 1/4`, the `h⁻²` logarithmic coefficient of
`U_p = e^{h a} e^{h b'} e^{−h a'} e^{−h b}` equals the discrete curl `h⁻¹((b' − b) − (a' − a))`
plus the commutator `[a, b]`, up to the translation errors and a cubic remainder. -/
theorem plaquette_expansion {h : ℝ} (hh : 0 < h) (a b a' b' : 𝔸)
    (hs : h * (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) ≤ 1 / 4) :
    ‖(h ^ 2)⁻¹ • logOnePlus (expProd [h • a, h • b', -(h • a'), -(h • b)] - 1)
        - (h⁻¹ • ((b' - b) - (a' - a)) + (a * b - b * a))‖
      ≤ 2 * (‖a' - a‖ + ‖b' - b‖) * (‖a‖ + ‖b‖ + ‖a' - a‖ + ‖b' - b‖)
        + 6 * max ‖(1 : 𝔸)‖ 1 * h * (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) ^ 3 := by
  set L : List 𝔸 := [h • a, h • b', -(h • a'), -(h • b)]
  have hns : normSum L = h * (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) := by
    simp only [L, normSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    ring
  have hbch := norm_log_expProd_sub_bch_le' L (hns ▸ hs)
  have hsum : L.sum = h • (a + b' - a' - b) := by
    simp only [L, List.sum_cons, List.sum_nil]; module
  have hcomm : commTerm L = (h ^ 2) • commTerm [a, b', -a', -b] := by
    simp only [L, commTerm, List.sum_cons, List.sum_nil, add_zero]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, smul_mul_smul_comm,
      smul_add, smul_sub, smul_neg, mul_zero, zero_mul]
    module
  have hh2 : h ^ 2 ≠ 0 := by positivity
  have hdecomp : (h ^ 2)⁻¹ • logOnePlus (expProd L - 1)
        - (h⁻¹ • ((b' - b) - (a' - a)) + (a * b - b * a))
      = (h ^ 2)⁻¹ • (logOnePlus (expProd L - 1) - (L.sum + commTerm L))
        + (commTerm [a, b', -a', -b] - (a * b - b * a)) := by
    have hh0 := hh.ne'
    rw [hsum, hcomm]
    match_scalars <;> field_simp <;> ring
  rw [hdecomp]
  have hc := norm_commTerm_plaquette_sub_le a b a' b'
  have hn : ‖(h ^ 2)⁻¹ • (logOnePlus (expProd L - 1) - (L.sum + commTerm L))‖
      ≤ 6 * max ‖(1 : 𝔸)‖ 1 * h * (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) ^ 3 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hns] at hbch
    rw [inv_mul_le_iff₀ (by positivity)]
    calc _ ≤ 6 * max ‖(1 : 𝔸)‖ 1 * (h * (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖)) ^ 3 := hbch
      _ = h ^ 2 * (6 * max ‖(1 : 𝔸)‖ 1 * h * (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) ^ 3) := by ring
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hn hc
    _ = _ := by ring

/-! ### Lattice form -/

variable {G : Type*} [AddCommGroup G]

/-- Forward difference `D⁺_e u(x) = h⁻¹(u(x + e) − u(x))`. -/
noncomputable def fwd (h : ℝ) (e : G) (u : G → 𝔸) (x : G) : 𝔸 := h⁻¹ • (u (x + e) - u x)

/-- The literal **magnetic record** `F_{ij}(x)`: the `h⁻²` logarithmic coefficient of the plaquette
holonomy `U_i(x) U_j(x+e_i) U_i(x+e_j)⁻¹ U_j(x)⁻¹`, `U_k = exp(h A_k)`, on the identity chart. -/
noncomputable def plaquetteRecord (h : ℝ) (ei ej : G) (Ai Aj : G → 𝔸) (x : G) : 𝔸 :=
  (h ^ 2)⁻¹ • logOnePlus
    (expProd [h • Ai x, h • Aj (x + ei), -(h • Ai (x + ej)), -(h • Aj x)] - 1)

/-- **Pointwise plaquette expansion of the magnetic record**:
`‖F_{ij} − (D⁺_iA_j − D⁺_jA_i + [A_i, A_j])‖ ≤
   2h(‖D⁺_jA_i‖ + ‖D⁺_iA_j‖)(‖A_i‖ + ‖A_j‖ + h‖D⁺_jA_i‖ + h‖D⁺_iA_j‖) + 6κh m³`,
`m = ‖A_i(x)‖ + ‖A_j(x)‖ + ‖A_i(x+e_j)‖ + ‖A_j(x+e_i)‖`, on the chart `h m ≤ 1/4`. -/
theorem norm_plaquetteRecord_sub_le {h : ℝ} (hh : 0 < h) (ei ej : G) (Ai Aj : G → 𝔸) (x : G)
    (hs : h * (‖Ai x‖ + ‖Aj x‖ + ‖Ai (x + ej)‖ + ‖Aj (x + ei)‖) ≤ 1 / 4) :
    ‖plaquetteRecord h ei ej Ai Aj x
        - (fwd h ei Aj x - fwd h ej Ai x + (Ai x * Aj x - Aj x * Ai x))‖
      ≤ 2 * h * (‖fwd h ej Ai x‖ + ‖fwd h ei Aj x‖)
          * (‖Ai x‖ + ‖Aj x‖ + h * ‖fwd h ej Ai x‖ + h * ‖fwd h ei Aj x‖)
        + 6 * max ‖(1 : 𝔸)‖ 1 * h
          * (‖Ai x‖ + ‖Aj x‖ + ‖Ai (x + ej)‖ + ‖Aj (x + ei)‖) ^ 3 := by
  have key := plaquette_expansion hh (Ai x) (Aj x) (Ai (x + ej)) (Aj (x + ei)) hs
  have hp : ‖Ai (x + ej) - Ai x‖ = h * ‖fwd h ej Ai x‖ := by
    rw [fwd, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hh, ← mul_assoc,
      mul_inv_cancel₀ hh.ne', one_mul]
  have hq : ‖Aj (x + ei) - Aj x‖ = h * ‖fwd h ei Aj x‖ := by
    rw [fwd, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hh, ← mul_assoc,
      mul_inv_cancel₀ hh.ne', one_mul]
  have e : h⁻¹ • ((Aj (x + ei) - Aj x) - (Ai (x + ej) - Ai x)) = fwd h ei Aj x - fwd h ej Ai x := by
    rw [fwd, fwd, smul_sub]
  rw [e, hp, hq] at key
  unfold plaquetteRecord
  refine key.trans (le_of_eq ?_)
  ring

section Frobenius

attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- Non-vacuity / intended instance: complex `n × n` matrices with the Frobenius norm (the norm of
the literal-link records, `‖1‖ = √n`) satisfy the hypotheses of `plaquette_expansion`. -/
theorem plaquette_expansion_frobenius (n : ℕ) {h : ℝ} (hh : 0 < h)
    (a b a' b' : Matrix (Fin n) (Fin n) ℂ) (hs : h * (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) ≤ 1 / 4) :
    ‖(h ^ 2)⁻¹ • logOnePlus (expProd [h • a, h • b', -(h • a'), -(h • b)] - 1)
        - (h⁻¹ • ((b' - b) - (a' - a)) + (a * b - b * a))‖
      ≤ 2 * (‖a' - a‖ + ‖b' - b‖) * (‖a‖ + ‖b‖ + ‖a' - a‖ + ‖b' - b‖)
        + 6 * max ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ 1 * h * (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) ^ 3 :=
  plaquette_expansion hh a b a' b' hs

end Frobenius

end RenewalGeometry.LogBCH.PlaquetteBCH
