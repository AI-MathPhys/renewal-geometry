/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicForwardDifferenceHodgeIdentityExact

/-!
# Uniform discrete Sobolev and Poincaré inequalities on the periodic grid `(ℤ/n)^d`
  (`eq:native-grid-Sobolev-a`, `eq:native-grid-Sobolev-b` of `lem:native-critical-grid`;
  the periodic Poincaré/Sobolev bound used in `lem:native-FP-inverse` and
  `lem:determinant-Hodge-stability`, Einstein–SM action closure)

Setting.  The periodic grid is `ι → ZMod n` (`n ≥ 1` nodes per direction, `d = card ι`
directions, unit steps `gridStep i = e_i`).  In the paper `ι = Fin 4`, the box has side
`L = 2π` and mesh `h = L/n`, discrete norms are `‖u‖_{p,h}^p = h⁴ Σ_x |u(x)|^p` and
`D^+_{i,h} u(x) = (u(x + e_i) - u(x))/h`.  Every constant below is explicit and independent of
`n` (and of `h`, `L`).

## Generic results
* `sum_prod_lineSum_rpow_le` — the **discrete Loomis–Whitney / grid-lines inequality** on a
  finite product `Π i, X i` of finite types (`d = card ι ≥ 2`):
  `Σ_x Π_i (Σ_t F(x[i ↦ t]))^{1/(d-1)} ≤ (Σ_x F x)^{d/(d-1)}` for `F ≥ 0`, obtained from
  Mathlib's grid-lines lemma `MeasureTheory.lintegral_prod_lintegral_pow_le` with counting
  measures.
* `norm_le_lineSum` — on the periodic grid, `‖v x‖` is bounded by the line sum of
  `‖Δ_i v‖ + ‖v‖/n` along every coordinate line through `x` (telescoping + averaging).
* `sum_norm_rpow_le_gagliardo` — the **periodic discrete Gagliardo–Nirenberg inequality**
  `Σ_x ‖v x‖^{d/(d-1)} ≤ (Σ_x Σ_i (‖v(x+e_i) - v x‖ + ‖v x‖/n))^{d/(d-1)}`, any normed group.
* `sum_pow_four_le_of_nonneg`, `sum_norm_pow_four_le_of_kato`, `sum_norm_pow_four_le`,
  `sum_norm_pow_four_le_covariant` — the **critical 4D inequality** (apply Gagliardo–Nirenberg
  to `|u|³`): `Σ‖u‖⁴ ≤ (Σ_i 3 ‖w_i‖_{ℓ²} + (4/n) ‖u‖_{ℓ²})⁴` whenever
  `|‖u(x+e_i)‖ - ‖u x‖| ≤ w_i(x)`; in particular for `w_i = ‖Δ_i u‖` and, by the discrete Kato
  inequality, for `w_i = ‖R_i(x) u(x+e_i) - u(x)‖` with norm-preserving (unitary) transports `R`.
* `grid_sobolev_L4`, `grid_sobolev_L4_covariant` — scaled forms
  `‖u‖_{4,h} ≤ 3 Σ_i ‖D^+_i u‖_{2,h} + (4/L) ‖u‖_{2,h}` (`L = n h`) and the covariant form with
  `D^U_i u = (R_i T_i u - u)/h`: `eq:native-grid-Sobolev-a,b` with `C = max(3, 4/L)`
  (`C = 3` for `L = 2π`, `grid_sobolev_L4_two_pi`).
* `sum_norm_sq_le_poincare`, `grid_poincare` — the **periodic discrete Poincaré inequality**
  for mean-zero functions with values in any real inner product space:
  `‖u‖_{2,h} ≤ (L/√2) Σ_i ‖D^+_i u‖_{2,h}` (position-space proof: variance identity and
  subadditivity of the `ℓ²` translation modulus).
* `grid_sobolev_L4_meanZero` — mean-zero 4D Sobolev: `‖u‖_{4,h} ≤ (3 + 2√2) Σ_i ‖D^+_i u‖_{2,h}`,
  and `grid_sobolev_poincare_meanZero_l2` with the `ℓ²`-sum
  `‖D^+u‖_{2,h} = (Σ_i ‖D^+_i u‖²_{2,h})^{1/2}`.
* `gridHolder` — weighted Hölder `L⁴ × L⁴ × L²`; `gridFwd_le_covFwd_add`, `gridFwd_le_graphNorm` —
  `D^+_i u = D^U_i u - B_i T_i u` with `B_i = (R_i - I)/h`, so a bounded graph norm and bounded
  `L⁴_h` link coefficients control the ordinary discrete `H¹` norm (`lem:native-critical-grid`).
-/

open MeasureTheory Finset

namespace RenewalGeometry.GridSobolev

noncomputable section

/-! ### The discrete grid-lines (Loomis–Whitney) inequality -/

/-- Lebesgue integral against the product of counting measures on a finite product is the
finite sum. -/
theorem lintegral_pi_count_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (f : (∀ i, X i) → ENNReal) :
    ∫⁻ x, f x ∂(Measure.pi fun i => (Measure.count : Measure (X i))) = ∑ x, f x := by
  rw [lintegral_fintype]
  refine sum_congr rfl fun x _ => ?_
  have : ({x} : Set (∀ i, X i)) = Set.univ.pi fun i => {x i} := by
    ext y; simp [funext_iff]
  rw [this, Measure.pi_pi]
  simp

/-- **Discrete grid-lines (Loomis–Whitney–Gagliardo) inequality.**  For finite types `X i`,
`d = card ι ≥ 2` and `F ≥ 0` on `Π i, X i`:
`Σ_x Π_i (Σ_t F(x[i ↦ t]))^{1/(d-1)} ≤ (Σ_x F x)^{d/(d-1)}`. -/
theorem sum_prod_lineSum_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] (F : (∀ i, X i) → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hd : 2 ≤ Fintype.card ι) :
    ∑ x, ∏ i, (∑ t, F (Function.update x i t)) ^ ((1 : ℝ) / (Fintype.card ι - 1)) ≤
      (∑ x, F x) ^ ((Fintype.card ι : ℝ) / (Fintype.card ι - 1)) := by
  let _ : ∀ i, MeasurableSpace (X i) := fun _ => ⊤
  have _ : ∀ i, MeasurableSingletonClass (X i) := fun _ => ⟨fun _ => trivial⟩
  have hd' : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hconj : (Fintype.card ι : ℝ).HolderConjugate ((Fintype.card ι : ℝ) / (Fintype.card ι - 1)) :=
    Real.HolderConjugate.conjExponent hd'
  have key := lintegral_prod_lintegral_pow_le (fun i => (Measure.count : Measure (X i))) hconj
    (f := fun x => ENNReal.ofReal (F x)) (measurable_of_countable _)
  simp only [lintegral_pi_count_eq_sum] at key
  have hq : (0 : ℝ) ≤ 1 / (Fintype.card ι - 1) := by
    have : (0 : ℝ) < Fintype.card ι - 1 := by linarith
    positivity
  have hp : (0 : ℝ) ≤ (Fintype.card ι : ℝ) / (Fintype.card ι - 1) := by
    have : (0 : ℝ) < Fintype.card ι - 1 := by linarith
    positivity
  have hline : ∀ (x : ∀ i, X i) (i : ι), ∫⁻ t, ENNReal.ofReal (F (Function.update x i t)) ∂(Measure.count : Measure (X i)) =
      ENNReal.ofReal (∑ t, F (Function.update x i t)) := by
    intro x i
    rw [lintegral_fintype]
    simp only [Measure.count_singleton, mul_one]
    rw [ENNReal.ofReal_sum_of_nonneg fun t _ => hF _]
  simp only [hline] at key
  rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => hF x,
    ENNReal.ofReal_rpow_of_nonneg (sum_nonneg fun x _ => hF x) hp] at key
  simp_rw [ENNReal.ofReal_rpow_of_nonneg (sum_nonneg fun t _ => hF _) hq] at key
  rw [Finset.sum_congr rfl fun x _ => (ENNReal.ofReal_prod_of_nonneg fun i _ =>
      Real.rpow_nonneg (sum_nonneg fun t _ => hF _) _).symm,
    ← ENNReal.ofReal_sum_of_nonneg fun x _ => prod_nonneg fun i _ =>
      Real.rpow_nonneg (sum_nonneg fun t _ => hF _) _] at key
  exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg (sum_nonneg fun x _ => hF x) _)).1 key

section Periodic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The unit lattice step `e_i` of the periodic grid `ι → ZMod n`. -/
def gridStep (i : ι) : ι → ZMod n := Pi.single i 1

/-- Stepping along the `i`-line: `x[i ↦ s] + e_i = x[i ↦ s+1]`. -/
theorem update_add_gridStep (x : ι → ZMod n) (i : ι) (s : ZMod n) :
    Function.update x i s + gridStep i = Function.update x i (s + 1) := by
  funext j
  by_cases h : j = i
  · subst h; simp [gridStep]
  · simp [gridStep, h]

variable [NeZero n]

/-- Translation invariance of periodic sums. -/
theorem sum_add_gridStep {M : Type*} [AddCommMonoid M] (g : (ι → ZMod n) → M) (i : ι) :
    ∑ x, g (x + gridStep i) = ∑ x, g x :=
  Fintype.sum_equiv (Equiv.addRight (gridStep i)) _ _ (fun _ => rfl)
variable {E : Type*} [SeminormedAddCommGroup E]

/-- Telescoping along a coordinate line. -/
theorem norm_sub_le_range_sum (v : (ι → ZMod n) → E) (x : ι → ZMod n) (i : ι) (t : ZMod n) :
    ∀ k : ℕ, ‖v (Function.update x i (t + k)) - v (Function.update x i t)‖ ≤
      ∑ j ∈ range k, ‖v (Function.update x i (t + j) + gridStep i) -
        v (Function.update x i (t + j))‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, update_add_gridStep]
    calc ‖v (Function.update x i (t + ((k + 1 : ℕ) : ZMod n))) - v (Function.update x i t)‖
        = ‖(v (Function.update x i (t + k + 1)) - v (Function.update x i (t + k))) +
            (v (Function.update x i (t + k)) - v (Function.update x i t))‖ := by
          rw [sub_add_sub_cancel]; push_cast; rw [add_assoc]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by rw [add_comm]; exact add_le_add ih le_rfl

/-- At most `n` consecutive points of `ZMod n` are distinct. -/
theorem range_sum_le_univ_sum (g : ZMod n → ℝ) (hg : ∀ s, 0 ≤ g s) (t : ZMod n) {k : ℕ}
    (hk : k ≤ n) : ∑ j ∈ range k, g (t + j) ≤ ∑ s, g s := by
  rw [← sum_image (f := g) (s := range k) (g := fun j : ℕ => t + (j : ZMod n))]
  · exact sum_le_univ_sum_of_nonneg hg
  · intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h2 : ((a : ℕ) : ZMod n) = (b : ZMod n) := add_left_cancel hab
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    rwa [Nat.mod_eq_of_lt (lt_of_lt_of_le ha hk), Nat.mod_eq_of_lt (lt_of_lt_of_le hb hk)] at h2

/-- **Line bound.**  On the periodic grid, for every coordinate direction `i`,
`‖v x‖ ≤ Σ_t (‖v(y_t + e_i) - v(y_t)‖ + ‖v(y_t)‖/n)` where `y_t = x[i ↦ t]` runs over the
`i`-line through `x` (telescoping from each `y_t`, then averaging over `t`). -/
theorem norm_le_lineSum (v : (ι → ZMod n) → E) (x : ι → ZMod n) (i : ι) :
    ‖v x‖ ≤ ∑ t : ZMod n, (‖v (Function.update x i t + gridStep i) - v (Function.update x i t)‖ +
      ‖v (Function.update x i t)‖ / n) := by
  set S := ∑ s : ZMod n, ‖v (Function.update x i s + gridStep i) - v (Function.update x i s)‖
  have hstep : ∀ t : ZMod n, ‖v x‖ ≤ ‖v (Function.update x i t)‖ + S := by
    intro t
    have hk : t + (((x i - t).val : ℕ) : ZMod n) = x i := by
      rw [ZMod.natCast_zmod_val]; ring
    have h1 := norm_sub_le_range_sum v x i t (x i - t).val
    rw [hk, Function.update_eq_self] at h1
    have h2 := range_sum_le_univ_sum
      (fun s => ‖v (Function.update x i s + gridStep i) - v (Function.update x i s)‖)
      (fun s => norm_nonneg _) t (ZMod.val_lt (x i - t)).le
    have h3 := norm_le_norm_add_norm_sub' (v x) (v (Function.update x i t))
    linarith
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hsum : (n : ℝ) * ‖v x‖ ≤ ∑ t : ZMod n, ‖v (Function.update x i t)‖ + n * S := by
    have := sum_le_sum fun t (_ : t ∈ (univ : Finset (ZMod n))) => hstep t
    rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul, sum_add_distrib, sum_const, card_univ,
      ZMod.card, nsmul_eq_mul] at this
    exact this
  rw [sum_add_distrib, ← sum_div]
  rw [show S + (∑ t : ZMod n, ‖v (Function.update x i t)‖) / n =
    (n * S + ∑ t : ZMod n, ‖v (Function.update x i t)‖) / n by field_simp]
  rw [le_div_iff₀ hn]; linarith

/-- **Periodic discrete Gagliardo–Nirenberg inequality** (`L¹ → L^{d/(d-1)}` form): for
`d = card ι ≥ 2` and any `v` with values in a seminormed group,
`Σ_x ‖v x‖^{d/(d-1)} ≤ (Σ_x Σ_i (‖v(x+e_i) - v x‖ + ‖v x‖/n))^{d/(d-1)}`.  Scaled by
`h = L/n` this is `‖v‖_{d/(d-1),h} ≤ Σ_i ‖D^+_i v‖_{1,h} + (d/L)‖v‖_{1,h}`. -/
theorem sum_norm_rpow_le_gagliardo (v : (ι → ZMod n) → E) (hd : 2 ≤ Fintype.card ι) :
    ∑ x, ‖v x‖ ^ ((Fintype.card ι : ℝ) / (Fintype.card ι - 1)) ≤
      (∑ x, ∑ i, (‖v (x + gridStep i) - v x‖ + ‖v x‖ / n)) ^
        ((Fintype.card ι : ℝ) / (Fintype.card ι - 1)) := by
  set F : (ι → ZMod n) → ℝ := fun x => ∑ i, (‖v (x + gridStep i) - v x‖ + ‖v x‖ / n) with hFdef
  have hF : ∀ x, 0 ≤ F x := fun x => sum_nonneg fun i _ => by positivity
  have hd' : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hq : (0 : ℝ) ≤ 1 / (Fintype.card ι - 1) := by
    have : (0 : ℝ) < Fintype.card ι - 1 := by linarith
    positivity
  have hline : ∀ x i, ‖v x‖ ≤ ∑ t, F (Function.update x i t) := by
    intro x i
    refine (norm_le_lineSum v x i).trans (sum_le_sum fun t _ => ?_)
    exact single_le_sum (f := fun j => ‖v (Function.update x i t + gridStep j) -
      v (Function.update x i t)‖ + ‖v (Function.update x i t)‖ / n)
      (fun j _ => by positivity) (mem_univ i)
  have hpt : ∀ x, ‖v x‖ ^ ((Fintype.card ι : ℝ) / (Fintype.card ι - 1)) ≤
      ∏ i, (∑ t, F (Function.update x i t)) ^ ((1 : ℝ) / (Fintype.card ι - 1)) := by
    intro x
    have hprod : ‖v x‖ ^ ((Fintype.card ι : ℝ) / (Fintype.card ι - 1)) =
        ∏ _i : ι, ‖v x‖ ^ ((1 : ℝ) / (Fintype.card ι - 1)) := by
      rw [prod_const, card_univ, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      ring
    rw [hprod]
    exact prod_le_prod (fun i _ => by positivity)
      (fun i _ => Real.rpow_le_rpow (norm_nonneg _) (hline x i) hq)
  exact (sum_le_sum fun x _ => hpt x).trans (sum_prod_lineSum_rpow_le F hF hd)

omit [Fintype ι] [DecidableEq ι] [NeZero n] in
/-- `|b³ - a³| ≤ (3/2)(b² + a²)|b - a|` for `a, b ≥ 0`. -/
theorem abs_cube_sub_cube_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |b ^ 3 - a ^ 3| ≤ 3 / 2 * (b ^ 2 + a ^ 2) * |b - a| := by
  have h : b ^ 3 - a ^ 3 = (b - a) * (b ^ 2 + b * a + a ^ 2) := by ring
  rw [h, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ b ^ 2 + b * a + a ^ 2), mul_comm]
  exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (b - a)]) (abs_nonneg _)

/-- The difference of cubes, summed: `Σ_x |f(x+e_i)³ - f(x)³| ≤ 3 ‖f‖₄² ‖Δ_i f‖₂`. -/
theorem sum_abs_cube_diff_le (f : (ι → ZMod n) → ℝ) (hf : ∀ x, 0 ≤ f x) (i : ι) :
    ∑ x, |f (x + gridStep i) ^ 3 - f x ^ 3| ≤
      3 * √(∑ x, f x ^ 4) * √(∑ x, (f (x + gridStep i) - f x) ^ 2) := by
  have h1 : ∑ x, |f (x + gridStep i) ^ 3 - f x ^ 3| ≤
      3 / 2 * ∑ x, (f (x + gridStep i) ^ 2 + f x ^ 2) * |f (x + gridStep i) - f x| := by
    rw [mul_sum]
    exact sum_le_sum fun x _ => by
      rw [← mul_assoc]; exact abs_cube_sub_cube_le (hf x) (hf _)
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt univ (fun x => f (x + gridStep i) ^ 2 + f x ^ 2)
    (fun x => |f (x + gridStep i) - f x|)
  have h3 : ∑ x, (f (x + gridStep i) ^ 2 + f x ^ 2) ^ 2 ≤ 4 * ∑ x, f x ^ 4 := by
    have hs : ∑ x, f (x + gridStep i) ^ 4 = ∑ x, f x ^ 4 :=
      sum_add_gridStep (fun x => f x ^ 4) i
    calc ∑ x, (f (x + gridStep i) ^ 2 + f x ^ 2) ^ 2
        ≤ ∑ x, (2 * f (x + gridStep i) ^ 4 + 2 * f x ^ 4) :=
          sum_le_sum fun x _ => by nlinarith [sq_nonneg (f (x + gridStep i) ^ 2 - f x ^ 2)]
      _ = 4 * ∑ x, f x ^ 4 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hs]; ring
  have h4 : √(∑ x, (f (x + gridStep i) ^ 2 + f x ^ 2) ^ 2) ≤ 2 * √(∑ x, f x ^ 4) := by
    calc √(∑ x, (f (x + gridStep i) ^ 2 + f x ^ 2) ^ 2) ≤ √(4 * ∑ x, f x ^ 4) :=
          Real.sqrt_le_sqrt h3
      _ = 2 * √(∑ x, f x ^ 4) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  simp only [sq_abs] at h2
  have h5 : 0 ≤ √(∑ x, (f (x + gridStep i) - f x) ^ 2) := Real.sqrt_nonneg _
  calc ∑ x, |f (x + gridStep i) ^ 3 - f x ^ 3| ≤ _ := h1
    _ ≤ 3 / 2 * (√(∑ x, (f (x + gridStep i) ^ 2 + f x ^ 2) ^ 2) *
          √(∑ x, (f (x + gridStep i) - f x) ^ 2)) := by gcongr
    _ ≤ 3 / 2 * (2 * √(∑ x, f x ^ 4) * √(∑ x, (f (x + gridStep i) - f x) ^ 2)) := by gcongr
    _ = _ := by ring

/-- `Σ f³ ≤ (Σ f⁴)^{1/2} (Σ f²)^{1/2}` (Cauchy–Schwarz). -/
theorem sum_cube_le (f : (ι → ZMod n) → ℝ) :
    ∑ x, f x ^ 3 ≤ √(∑ x, f x ^ 4) * √(∑ x, f x ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt univ (fun x => f x ^ 2) f
  have e1 : ∀ x, f x ^ 2 * f x = f x ^ 3 := fun x => by ring
  have e2 : ∀ x, (f x ^ 2) ^ 2 = f x ^ 4 := fun x => by ring
  simp only [e1, e2] at h
  exact h

/-- **Uniform critical discrete Sobolev inequality on the periodic 4D grid** (unscaled form,
nonnegative scalar functions): with `S₄ = Σ f⁴`, `S₂ = Σ f²`,
`S₄ ≤ (3 Σ_i ‖Δ_i f‖_{ℓ²} + (4/n) ‖f‖_{ℓ²})⁴`. -/
theorem sum_pow_four_le_of_nonneg (f : (ι → ZMod n) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hι : Fintype.card ι = 4) :
    ∑ x, f x ^ 4 ≤ (∑ i, 3 * √(∑ x, (f (x + gridStep i) - f x) ^ 2) +
      4 / n * √(∑ x, f x ^ 2)) ^ 4 := by
  have GN := sum_norm_rpow_le_gagliardo (fun x => f x ^ 3) (by omega)
  rw [hι] at GN
  have hexp : ((4 : ℕ) : ℝ) / ((4 : ℕ) - 1) = 4 / 3 := by norm_num
  rw [hexp] at GN
  have hnorm : ∀ x, ‖f x ^ 3‖ = f x ^ 3 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf x) 3)]
  simp only [hnorm, Real.norm_eq_abs] at GN
  have hlhs : ∀ x, (f x ^ 3) ^ ((4 : ℝ) / 3) = f x ^ 4 := fun x => by
    rw [← Real.rpow_natCast (f x) 3, ← Real.rpow_mul (hf x)]
    norm_num
  simp only [hlhs] at GN
  set Q := √(∑ x, f x ^ 4) with hQ
  set B := ∑ i, 3 * √(∑ x, (f (x + gridStep i) - f x) ^ 2) + 4 / n * √(∑ x, f x ^ 2) with hB
  have hS4 : ∑ x, f x ^ 4 = Q ^ 2 := by
    rw [hQ, Real.sq_sqrt (sum_nonneg fun x _ => by positivity)]
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hT : ∑ x, ∑ i, (|f (x + gridStep i) ^ 3 - f x ^ 3| + f x ^ 3 / n) ≤ Q * B := by
    rw [sum_comm]
    simp only [sum_add_distrib]
    have hc : ∑ _i : ι, ∑ x, f x ^ 3 / n = (4 : ℕ) • ((∑ x, f x ^ 3) / n) := by
      rw [sum_const, card_univ, hι, sum_div]
    rw [hc]
    have h1 : ∑ i, ∑ x, |f (x + gridStep i) ^ 3 - f x ^ 3| ≤
        ∑ i, 3 * Q * √(∑ x, (f (x + gridStep i) - f x) ^ 2) :=
      sum_le_sum fun i _ => sum_abs_cube_diff_le f hf i
    have h2 := sum_cube_le f
    rw [← hQ] at h2
    have h3 : (4 : ℕ) • ((∑ x, f x ^ 3) / n) ≤ 4 / n * (Q * √(∑ x, f x ^ 2)) := by
      rw [nsmul_eq_mul, div_eq_mul_inv, div_eq_mul_inv]
      have : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      push_cast
      nlinarith
    calc _ ≤ ∑ i, 3 * Q * √(∑ x, (f (x + gridStep i) - f x) ^ 2) +
          4 / n * (Q * √(∑ x, f x ^ 2)) := add_le_add h1 h3
      _ = Q * B := by rw [hB, mul_add, mul_sum]; congr 1; · exact sum_congr rfl fun i _ => by ring
                      · ring
  have hB0 : 0 ≤ B := by
    rw [hB]; exact add_nonneg (sum_nonneg fun i _ => by positivity) (by positivity)
  have hT0 : 0 ≤ ∑ x, ∑ i, (|f (x + gridStep i) ^ 3 - f x ^ 3| + f x ^ 3 / n) :=
    sum_nonneg fun x _ => sum_nonneg fun i _ => add_nonneg (abs_nonneg _)
      (div_nonneg (pow_nonneg (hf x) 3) hn.le)
  have hmain : Q ^ 2 ≤ (Q * B) ^ ((4 : ℝ) / 3) := by
    rw [← hS4]
    exact GN.trans (Real.rpow_le_rpow hT0 hT (by norm_num))
  have hcube : (Q ^ 2) ^ 3 ≤ (Q * B) ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hmain 3
    rwa [← Real.rpow_natCast ((Q * B) ^ ((4 : ℝ) / 3)), ← Real.rpow_mul (by positivity),
      show (4 : ℝ) / 3 * ((3 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  rw [hS4]
  rcases hQ0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp; positivity
  · have : Q ^ 4 * Q ^ 2 ≤ Q ^ 4 * B ^ 4 := by nlinarith [hcube]
    have hQ4 : 0 < Q ^ 4 := by positivity
    have := le_of_mul_le_mul_left this hQ4
    exact this

/-- **Critical 4D inequality, Kato form.**  If `|‖u(x+e_i)‖ - ‖u x‖| ≤ w_i(x)` for all `x, i`,
then `Σ_x ‖u x‖⁴ ≤ (Σ_i 3 (Σ_x w_i(x)²)^{1/2} + (4/n)(Σ_x ‖u x‖²)^{1/2})⁴`. -/
theorem sum_norm_pow_four_le_of_kato (u : (ι → ZMod n) → E) (w : ι → (ι → ZMod n) → ℝ)
    (hw : ∀ i x, |‖u (x + gridStep i)‖ - ‖u x‖| ≤ w i x) (hι : Fintype.card ι = 4) :
    ∑ x, ‖u x‖ ^ 4 ≤ (∑ i, 3 * √(∑ x, w i x ^ 2) + 4 / n * √(∑ x, ‖u x‖ ^ 2)) ^ 4 := by
  refine (sum_pow_four_le_of_nonneg (fun x => ‖u x‖) (fun x => norm_nonneg _) hι).trans ?_
  have hB0 : 0 ≤ ∑ i, 3 * √(∑ x, (‖u (x + gridStep i)‖ - ‖u x‖) ^ 2) +
      4 / n * √(∑ x, ‖u x‖ ^ 2) := by positivity
  refine pow_le_pow_left₀ hB0 (add_le_add_left (sum_le_sum fun i _ => ?_) _) 4
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (sum_le_sum fun x _ => ?_)) (by norm_num)
  have := hw i x
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

/-- **Critical 4D inequality** (unscaled `eq:native-grid-Sobolev-a`):
`Σ_x ‖u x‖⁴ ≤ (Σ_i 3 ‖Δ_i u‖_{ℓ²} + (4/n) ‖u‖_{ℓ²})⁴` with `Δ_i u(x) = u(x+e_i) - u(x)`. -/
theorem sum_norm_pow_four_le (u : (ι → ZMod n) → E) (hι : Fintype.card ι = 4) :
    ∑ x, ‖u x‖ ^ 4 ≤ (∑ i, 3 * √(∑ x, ‖u (x + gridStep i) - u x‖ ^ 2) +
      4 / n * √(∑ x, ‖u x‖ ^ 2)) ^ 4 :=
  sum_norm_pow_four_le_of_kato u (fun i x => ‖u (x + gridStep i) - u x‖)
    (fun _ _ => abs_norm_sub_norm_le _ _) hι

omit [Fintype ι] [DecidableEq ι] [NeZero n] in
/-- **Discrete Kato inequality**: for a norm-preserving transport `R` (e.g. a unitary
`ρ(U_i(x))`), `|‖a‖ - ‖b‖| ≤ ‖R a - b‖`; with `a = u(x+e_i)`, `b = u(x)` this is
`|D^+_i |u|| ≤ |D^U_i u|`. -/
theorem abs_norm_sub_norm_le_transport (R : E → E) (hR : ∀ v, ‖R v‖ = ‖v‖) (a b : E) :
    |‖a‖ - ‖b‖| ≤ ‖R a - b‖ := by
  rw [← hR a]; exact abs_norm_sub_norm_le _ _

/-- **Covariant critical 4D inequality** (unscaled `eq:native-grid-Sobolev-b`): for
norm-preserving (unitary) link transports `R x i`,
`Σ_x ‖u x‖⁴ ≤ (Σ_i 3 ‖R_i T_i u - u‖_{ℓ²} + (4/n) ‖u‖_{ℓ²})⁴`. -/
theorem sum_norm_pow_four_le_covariant (u : (ι → ZMod n) → E)
    (R : (ι → ZMod n) → ι → E → E) (hR : ∀ x i v, ‖R x i v‖ = ‖v‖) (hι : Fintype.card ι = 4) :
    ∑ x, ‖u x‖ ^ 4 ≤ (∑ i, 3 * √(∑ x, ‖R x i (u (x + gridStep i)) - u x‖ ^ 2) +
      4 / n * √(∑ x, ‖u x‖ ^ 2)) ^ 4 :=
  sum_norm_pow_four_le_of_kato u (fun i x => ‖R x i (u (x + gridStep i)) - u x‖)
    (fun i x => abs_norm_sub_norm_le_transport (R x i) (hR x i) _ _) hι

end Periodic

/-! ### Scaled norms and the scaled inequalities -/

section Scaled

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scaled forward difference `D^+_{i,h} u(x) = (u(x + e_i) - u(x))/h`
(`eq:native-critical-norms`). -/
def gridFwd (h : ℝ) (i : ι) (u : (ι → ZMod n) → E) (x : ι → ZMod n) : E :=
  h⁻¹ • (u (x + gridStep i) - u x)

/-- The covariant difference `D^U_{i,h} u(x) = (R_i(x) u(x + e_i) - u(x))/h`
(`eq:native-internal-graph`, `R_i(x) = ρ(U_{i,h}(x))`). -/
def gridCovFwd (h : ℝ) (R : (ι → ZMod n) → ι → E → E) (i : ι) (u : (ι → ZMod n) → E)
    (x : ι → ZMod n) : E :=
  h⁻¹ • (R x i (u (x + gridStep i)) - u x)

/-- The discrete `L²` norm `‖u‖_{2,h} = (h^d Σ_x ‖u x‖²)^{1/2}` (`d = card ι`). -/
def gridL2Norm (h : ℝ) (u : (ι → ZMod n) → E) : ℝ :=
  √(periodicHodgeNormSq ι h u)

/-- The discrete `L⁴` norm `‖u‖_{4,h} = (h^d Σ_x ‖u x‖⁴)^{1/4}`. -/
def gridL4Norm (h : ℝ) (u : (ι → ZMod n) → E) : ℝ :=
  (h ^ Fintype.card ι * ∑ x, ‖u x‖ ^ 4) ^ ((1 : ℝ) / 4)

omit [NormedSpace ℝ E] in
theorem gridL2Norm_nonneg (h : ℝ) (u : (ι → ZMod n) → E) : 0 ≤ gridL2Norm h u :=
  Real.sqrt_nonneg _

omit [NormedSpace ℝ E] in
theorem gridL2Norm_eq {h : ℝ} (hh : 0 < h) (u : (ι → ZMod n) → E) :
    gridL2Norm h u = √(h ^ Fintype.card ι) * √(∑ x, ‖u x‖ ^ 2) := by
  rw [gridL2Norm, periodicHodgeNormSq, Real.sqrt_mul (by positivity)]

theorem gridL2Norm_gridFwd {h : ℝ} (hh : 0 < h) (i : ι) (u : (ι → ZMod n) → E) :
    gridL2Norm h (gridFwd h i u) =
      h⁻¹ * √(h ^ Fintype.card ι) * √(∑ x, ‖u (x + gridStep i) - u x‖ ^ 2) := by
  rw [gridL2Norm_eq hh]
  have : ∀ x, ‖gridFwd h i u x‖ ^ 2 = (h⁻¹) ^ 2 * ‖u (x + gridStep i) - u x‖ ^ 2 := fun x => by
    rw [gridFwd, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [this, ← mul_sum]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

theorem gridL2Norm_gridCovFwd {h : ℝ} (hh : 0 < h) (R : (ι → ZMod n) → ι → E → E) (i : ι)
    (u : (ι → ZMod n) → E) :
    gridL2Norm h (gridCovFwd h R i u) =
      h⁻¹ * √(h ^ Fintype.card ι) * √(∑ x, ‖R x i (u (x + gridStep i)) - u x‖ ^ 2) := by
  rw [gridL2Norm_eq hh]
  have : ∀ x, ‖gridCovFwd h R i u x‖ ^ 2 =
      (h⁻¹) ^ 2 * ‖R x i (u (x + gridStep i)) - u x‖ ^ 2 := fun x => by
    rw [gridCovFwd, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [this, ← mul_sum]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

omit [NormedSpace ℝ E] in
/-- Scaled form of an unscaled fourth-power bound. -/
theorem gridL4Norm_le_of_sum_le {h : ℝ} (hh : 0 < h) (hι : Fintype.card ι = 4)
    (u : (ι → ZMod n) → E) {B : ℝ} (hB : 0 ≤ B) (hS : ∑ x, ‖u x‖ ^ 4 ≤ B ^ 4) :
    gridL4Norm h u ≤ h * B := by
  rw [gridL4Norm, hι]
  have h1 : h ^ 4 * ∑ x, ‖u x‖ ^ 4 ≤ (h * B) ^ 4 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hS (by positivity)
  calc (h ^ 4 * ∑ x, ‖u x‖ ^ 4) ^ ((1 : ℝ) / 4) ≤ ((h * B) ^ 4) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    _ = h * B := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num

/-- **`eq:native-grid-Sobolev-a`** (scaled, uniform in `n`): on `(ℤ/n)⁴` with mesh `h > 0` and
side `L = n h`, `‖u‖_{4,h} ≤ 3 Σ_i ‖D^+_{i,h} u‖_{2,h} + (4/L) ‖u‖_{2,h}`. -/
theorem grid_sobolev_L4 {h : ℝ} (hh : 0 < h) (hι : Fintype.card ι = 4) (u : (ι → ZMod n) → E) :
    gridL4Norm h u ≤ 3 * ∑ i, gridL2Norm h (gridFwd h i u) + 4 / (n * h) * gridL2Norm h u := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  refine (gridL4Norm_le_of_sum_le hh hι u (by positivity) (sum_norm_pow_four_le u hι)).trans
    (le_of_eq ?_)
  simp only [gridL2Norm_gridFwd hh, gridL2Norm_eq hh, hι]
  have hs : √(h ^ 4) = h ^ 2 := by
    rw [show h ^ 4 = (h ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hs, mul_add, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    field_simp
  · field_simp

/-- **`eq:native-grid-Sobolev-b`** (scaled, uniform in `n`): for norm-preserving (unitary)
transports `R`, `‖u‖_{4,h} ≤ 3 Σ_i ‖D^U_{i,h} u‖_{2,h} + (4/L) ‖u‖_{2,h}`. -/
theorem grid_sobolev_L4_covariant {h : ℝ} (hh : 0 < h) (hι : Fintype.card ι = 4)
    (R : (ι → ZMod n) → ι → E → E) (hR : ∀ x i v, ‖R x i v‖ = ‖v‖) (u : (ι → ZMod n) → E) :
    gridL4Norm h u ≤
      3 * ∑ i, gridL2Norm h (gridCovFwd h R i u) + 4 / (n * h) * gridL2Norm h u := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  refine (gridL4Norm_le_of_sum_le hh hι u (by positivity)
    (sum_norm_pow_four_le_covariant u R hR hι)).trans (le_of_eq ?_)
  simp only [gridL2Norm_gridCovFwd hh, gridL2Norm_eq hh, hι]
  have hs : √(h ^ 4) = h ^ 2 := by
    rw [show h ^ 4 = (h ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hs, mul_add, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    field_simp
  · field_simp

/-- **`eq:native-grid-Sobolev-a,b` on the paper's box `L = 2π`** with the explicit
cutoff-independent constant `C = 3`:
`‖u‖_{4,h} ≤ 3 (‖u‖_{2,h} + Σ_i ‖D^+_i u‖_{2,h})`, and the same with `D^U` for unitary `R`. -/
theorem grid_sobolev_L4_two_pi {h : ℝ} (hh : 0 < h) (hL : (n : ℝ) * h = 2 * Real.pi)
    (hι : Fintype.card ι = 4) (u : (ι → ZMod n) → E) :
    gridL4Norm h u ≤ 3 * (gridL2Norm h u + ∑ i, gridL2Norm h (gridFwd h i u)) ∧
    ∀ (R : (ι → ZMod n) → ι → E → E), (∀ x i v, ‖R x i v‖ = ‖v‖) →
      gridL4Norm h u ≤ 3 * (gridL2Norm h u + ∑ i, gridL2Norm h (gridCovFwd h R i u)) := by
  have hc : 4 / ((n : ℝ) * h) ≤ 3 := by
    rw [hL, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
  have h0 := gridL2Norm_nonneg h u
  refine ⟨(grid_sobolev_L4 hh hι u).trans ?_,
    fun R hR => (grid_sobolev_L4_covariant hh hι R hR u).trans ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hc h0]
  · nlinarith [mul_le_mul_of_nonneg_right hc h0]

end Scaled

/-! ### The periodic discrete Poincaré inequality -/

section Poincare

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `ℓ²` translation modulus `τ(z) = (Σ_x ‖u(x+z) - u x‖²)^{1/2}`. -/
def transModulus (u : (ι → ZMod n) → E) (z : ι → ZMod n) : ℝ :=
  √(∑ x, ‖u (x + z) - u x‖ ^ 2)

theorem transModulus_eq_norm (u : (ι → ZMod n) → E) (z : ι → ZMod n) :
    transModulus u z = ‖WithLp.toLp 2 (fun x => u (x + z) - u x)‖ := by
  rw [PiLp.norm_eq_of_L2]; rfl

theorem transModulus_zero (u : (ι → ZMod n) → E) : transModulus u 0 = 0 := by
  simp [transModulus]

/-- Subadditivity of the translation modulus. -/
theorem transModulus_add_le (u : (ι → ZMod n) → E) (a b : ι → ZMod n) :
    transModulus u (a + b) ≤ transModulus u a + transModulus u b := by
  have hsplit : (fun x => u (x + (a + b)) - u x) =
      (fun x => u ((x + b) + a) - u (x + b)) + (fun x => u (x + b) - u x) := by
    funext x; simp only [Pi.add_apply]; rw [show x + (a + b) = x + b + a by abel]; abel
  have hshift : ‖WithLp.toLp 2 (fun x => u ((x + b) + a) - u (x + b))‖ = transModulus u a := by
    rw [PiLp.norm_eq_of_L2, transModulus]
    congr 1
    exact Fintype.sum_equiv (Equiv.addRight b) _ (fun x => ‖u (x + a) - u x‖ ^ 2)
      (fun _ => rfl)
  rw [transModulus_eq_norm u (a + b), hsplit, WithLp.toLp_add, ← hshift, transModulus_eq_norm]
  exact norm_add_le _ _

theorem transModulus_nsmul_le (u : (ι → ZMod n) → E) (a : ι → ZMod n) (k : ℕ) :
    transModulus u (k • a) ≤ k * transModulus u a := by
  induction k with
  | zero => simp [transModulus_zero]
  | succ k ih =>
    rw [succ_nsmul]
    refine (transModulus_add_le u _ _).trans ?_
    push_cast; linarith

theorem transModulus_sum_le (u : (ι → ZMod n) → E) (s : Finset ι) (a : ι → ι → ZMod n) :
    transModulus u (∑ i ∈ s, a i) ≤ ∑ i ∈ s, transModulus u (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [transModulus_zero]
  | insert j s hj ih =>
    rw [sum_insert hj, sum_insert hj]
    exact (transModulus_add_le u _ _).trans (add_le_add le_rfl ih)

omit [Fintype ι] in
theorem single_eq_val_nsmul (z : ι → ZMod n) (i : ι) :
    Pi.single i (z i) = (z i).val • (gridStep i : ι → ZMod n) := by
  funext j
  by_cases h : j = i
  · subst h; simp [gridStep]
  · simp [gridStep, h]

/-- Every translation modulus is at most `n Σ_i τ(e_i)`. -/
theorem transModulus_le (u : (ι → ZMod n) → E) (z : ι → ZMod n) :
    transModulus u z ≤ n * ∑ i, transModulus u (gridStep i) := by
  calc transModulus u z = transModulus u (∑ i, Pi.single i (z i)) :=
        congrArg (transModulus u) (univ_sum_single z).symm
    _ ≤ ∑ i, transModulus u (Pi.single i (z i)) := transModulus_sum_le u _ _
    _ ≤ ∑ i, (n : ℝ) * transModulus u (gridStep i) := by
        refine sum_le_sum fun i _ => ?_
        rw [single_eq_val_nsmul]
        refine (transModulus_nsmul_le u _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (ZMod.val_lt (z i)).le)
          (Real.sqrt_nonneg _)
    _ = _ := by rw [mul_sum]

/-- The variance identity `Σ_z Σ_x ‖u(x+z) - u x‖² = 2N Σ_x ‖u x‖² - 2‖Σ_x u x‖²`. -/
theorem sum_sum_norm_sub_sq (u : (ι → ZMod n) → E) :
    ∑ z, ∑ x, ‖u (x + z) - u x‖ ^ 2 =
      2 * Fintype.card (ι → ZMod n) * ∑ x, ‖u x‖ ^ 2 - 2 * ‖∑ x, u x‖ ^ 2 := by
  simp only [norm_sub_sq_real, sum_add_distrib, sum_sub_distrib]
  have h1 : ∀ z : ι → ZMod n, ∑ x, ‖u (x + z)‖ ^ 2 = ∑ x, ‖u x‖ ^ 2 := fun z =>
    Fintype.sum_equiv (Equiv.addRight z) _ _ (fun _ => rfl)
  have h2 : ∑ z : ι → ZMod n, ∑ x, 2 * inner ℝ (u (x + z)) (u x) = 2 * ‖∑ x, u x‖ ^ 2 := by
    have hx : ∀ x : ι → ZMod n, ∑ z, u (x + z) = ∑ y, u y := fun x =>
      Fintype.sum_equiv (Equiv.addLeft x) (fun z => u (x + z)) u (fun _ => rfl)
    rw [sum_comm, ← real_inner_self_eq_norm_sq, sum_inner, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [← mul_sum, ← sum_inner, hx, real_inner_comm]
  simp only [h1, h2, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- **Periodic discrete Poincaré inequality** (unscaled): for mean-zero `u`,
`Σ_x ‖u x‖² ≤ (n²/2) (Σ_i ‖Δ_i u‖_{ℓ²})²`. -/
theorem sum_norm_sq_le_poincare (u : (ι → ZMod n) → E) (hu : ∑ x, u x = 0) :
    ∑ x, ‖u x‖ ^ 2 ≤ (n : ℝ) ^ 2 / 2 * (∑ i, transModulus u (gridStep i)) ^ 2 := by
  have hvar := sum_sum_norm_sub_sq u
  rw [hu, norm_zero] at hvar
  set G := ∑ i, transModulus u (gridStep i)
  have hG : 0 ≤ G := sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hz : ∀ z, ∑ x, ‖u (x + z) - u x‖ ^ 2 ≤ ((n : ℝ) * G) ^ 2 := by
    intro z
    have h := transModulus_le u z
    have h0 : 0 ≤ transModulus u z := Real.sqrt_nonneg _
    have := pow_le_pow_left₀ h0 h 2
    rwa [transModulus, Real.sq_sqrt (sum_nonneg fun x _ => by positivity)] at this
  have hsum := sum_le_sum fun z (_ : z ∈ (univ : Finset (ι → ZMod n))) => hz z
  rw [hvar, sum_const, card_univ, nsmul_eq_mul] at hsum
  have hN : (0 : ℝ) < Fintype.card (ι → ZMod n) := by exact_mod_cast Fintype.card_pos
  nlinarith

/-- **Periodic discrete Poincaré inequality** (scaled; mean-zero `u`, mesh `h > 0`, side
`L = n h`): `‖u‖_{2,h} ≤ (L/√2) Σ_i ‖D^+_{i,h} u‖_{2,h}`.  Any dimension, values in any real
inner product space. -/
theorem grid_poincare {h : ℝ} (hh : 0 < h) (u : (ι → ZMod n) → E) (hu : ∑ x, u x = 0) :
    gridL2Norm h u ≤ n * h / √2 * ∑ i, gridL2Norm h (gridFwd h i u) := by
  have hP := sum_norm_sq_le_poincare u hu
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set G := ∑ i, transModulus u (gridStep i) with hG
  have hG0 : 0 ≤ G := sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hsq : √(∑ x, ‖u x‖ ^ 2) ≤ n / √2 * G := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
    calc _ ≤ _ := hP
      _ = _ := by ring
  have hfwd : ∑ i, gridL2Norm h (gridFwd h i u) = h⁻¹ * √(h ^ Fintype.card ι) * G := by
    simp only [gridL2Norm_gridFwd hh, hG, mul_sum]; rfl
  rw [gridL2Norm_eq hh, hfwd]
  calc √(h ^ Fintype.card ι) * √(∑ x, ‖u x‖ ^ 2) ≤ √(h ^ Fintype.card ι) * (n / √2 * G) :=
        mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
    _ = _ := by field_simp

end Poincare

/-! ### Mean-zero critical Sobolev inequality -/

section MeanZero

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Mean-zero critical Sobolev inequality** on `(ℤ/n)⁴`, uniform in `n`:
`‖u‖_{4,h} ≤ (3 + 2√2) Σ_i ‖D^+_{i,h} u‖_{2,h}` for `Σ_x u x = 0`. -/
theorem grid_sobolev_L4_meanZero {h : ℝ} (hh : 0 < h) (hι : Fintype.card ι = 4)
    (u : (ι → ZMod n) → E) (hu : ∑ x, u x = 0) :
    gridL4Norm h u ≤ (3 + 2 * √2) * ∑ i, gridL2Norm h (gridFwd h i u) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hS := grid_sobolev_L4 hh hι u
  have hP := grid_poincare hh u hu
  set G := ∑ i, gridL2Norm h (gridFwd h i u)
  have h2 : 4 / (n * h) * gridL2Norm h u ≤ 2 * √2 * G := by
    calc 4 / (n * h) * gridL2Norm h u ≤ 4 / (n * h) * (n * h / √2 * G) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = 2 * √2 * G := by
          have hs : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          have hs0 : 0 < √2 := by positivity
          field_simp
          rw [hs]; ring
  linarith

omit [DecidableEq ι] in
/-- `Σ_i a_i ≤ 2 (Σ_i a_i²)^{1/2}` for four directions. -/
theorem sum_le_two_mul_sqrt_sum_sq (hι : Fintype.card ι = 4) (a : ι → ℝ) :
    ∑ i, a i ≤ 2 * √(∑ i, a i ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt univ (fun _ => (1 : ℝ)) a
  simp only [one_mul, one_pow, sum_const, card_univ, hι, nsmul_eq_mul, mul_one] at h
  rwa [show √((4 : ℕ) : ℝ) = 2 by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h

/-- Mean-zero critical Sobolev and Poincaré in terms of the `ℓ²`-sum
`‖D^+u‖_{2,h} = (Σ_i ‖D^+_{i,h} u‖²_{2,h})^{1/2}` (the norm of `𝒵_h` in `lem:native-FP-inverse`):
`‖u‖_{4,h} ≤ 2(3 + 2√2) ‖D^+u‖_{2,h}` and `‖u‖_{2,h} ≤ √2 L ‖D^+u‖_{2,h}`. -/
theorem grid_sobolev_poincare_meanZero_l2 {h : ℝ} (hh : 0 < h) (hι : Fintype.card ι = 4)
    (u : (ι → ZMod n) → E) (hu : ∑ x, u x = 0) :
    gridL4Norm h u ≤ 2 * (3 + 2 * √2) * √(∑ i, gridL2Norm h (gridFwd h i u) ^ 2) ∧
    gridL2Norm h u ≤ √2 * (n * h) * √(∑ i, gridL2Norm h (gridFwd h i u) ^ 2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hsum := sum_le_two_mul_sqrt_sum_sq hι (fun i => gridL2Norm h (gridFwd h i u))
  constructor
  · refine (grid_sobolev_L4_meanZero hh hι u hu).trans ?_
    have : (0 : ℝ) ≤ 3 + 2 * √2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsum this]
  · refine (grid_poincare hh u hu).trans ?_
    have hs : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 < √2 := by positivity
    calc n * h / √2 * ∑ i, gridL2Norm h (gridFwd h i u)
        ≤ n * h / √2 * (2 * √(∑ i, gridL2Norm h (gridFwd h i u) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = √2 * (n * h) * √(∑ i, gridL2Norm h (gridFwd h i u) ^ 2) := by
          field_simp
          rw [hs]

end MeanZero

/-! ### Weighted Hölder and the graph-norm control of `D^+` -/

section GraphNorm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]

omit [Fintype ι] [DecidableEq ι] [NeZero n] in
theorem sum_mul_mul_le {X : Type*} [Fintype X] (a b c : X → ℝ) :
    ∑ x, a x * b x * c x ≤ √(√(∑ x, a x ^ 4)) * √(√(∑ x, b x ^ 4)) * √(∑ x, c x ^ 2) := by
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt univ (fun x => a x * b x) c
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt univ (fun x => a x ^ 2) (fun x => b x ^ 2)
  have e1 : ∀ x, (a x * b x) ^ 2 = a x ^ 2 * b x ^ 2 := fun x => by ring
  have e2 : ∀ x, (a x ^ 2) ^ 2 = a x ^ 4 := fun x => by ring
  have e3 : ∀ x, (b x ^ 2) ^ 2 = b x ^ 4 := fun x => by ring
  simp only [e2, e3] at h2
  simp only [e1] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  rw [← Real.sqrt_mul (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt h2

theorem gridL4Norm_eq_sqrt_sqrt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ}
    (hh : 0 ≤ h) (u : (ι → ZMod n) → F) :
    gridL4Norm h u = √(√(h ^ Fintype.card ι * ∑ x, ‖u x‖ ^ 4)) := by
  have h0 : 0 ≤ h ^ Fintype.card ι * ∑ x, ‖u x‖ ^ 4 := by positivity
  rw [gridL4Norm, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h0]
  norm_num

/-- Weighted Hölder `L⁴ × L⁴ × L²` for four-dimensional grid norms. -/
theorem gridHolder {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    (a : (ι → ZMod n) → F) (b : (ι → ZMod n) → G) (c : (ι → ZMod n) → K) :
    h ^ 4 * ∑ x, ‖a x‖ * ‖b x‖ * ‖c x‖ ≤ gridL4Norm h a * gridL4Norm h b * gridL2Norm h c := by
  rw [gridL4Norm_eq_sqrt_sqrt hh.le, gridL4Norm_eq_sqrt_sqrt hh.le, gridL2Norm_eq hh, hι]
  have hH := sum_mul_mul_le (fun x => ‖a x‖) (fun x => ‖b x‖) (fun x => ‖c x‖)
  have hw : h ^ 4 = √(√(h ^ 4)) * √(√(h ^ 4)) * √(h ^ 4) := by
    rw [Real.mul_self_sqrt (Real.sqrt_nonneg _), Real.mul_self_sqrt (by positivity)]
  have e1 : √(√(h ^ 4 * ∑ x, ‖a x‖ ^ 4)) = √(√(h ^ 4)) * √(√(∑ x, ‖a x‖ ^ 4)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (Real.sqrt_nonneg _)]
  have e2 : √(√(h ^ 4 * ∑ x, ‖b x‖ ^ 4)) = √(√(h ^ 4)) * √(√(∑ x, ‖b x‖ ^ 4)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (Real.sqrt_nonneg _)]
  rw [e1, e2]
  have hp : 0 ≤ √(√(h ^ 4)) * √(√(h ^ 4)) * √(h ^ 4) := by positivity
  calc h ^ 4 * ∑ x, ‖a x‖ * ‖b x‖ * ‖c x‖
      = √(√(h ^ 4)) * √(√(h ^ 4)) * √(h ^ 4) * ∑ x, ‖a x‖ * ‖b x‖ * ‖c x‖ := by rw [← hw]
    _ ≤ √(√(h ^ 4)) * √(√(h ^ 4)) * √(h ^ 4) * (√(√(∑ x, ‖a x‖ ^ 4)) *
          √(√(∑ x, ‖b x‖ ^ 4)) * √(∑ x, ‖c x‖ ^ 2)) := mul_le_mul_of_nonneg_left hH hp
    _ = _ := by ring


theorem gridL2Norm_sub_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ}
    (hh : 0 < h) (f g : (ι → ZMod n) → F) :
    gridL2Norm h (f - g) ≤ gridL2Norm h f + gridL2Norm h g := by
  have e : ∀ w : (ι → ZMod n) → F, gridL2Norm h w =
      √(h ^ Fintype.card ι) * ‖WithLp.toLp 2 w‖ := fun w => by
    rw [gridL2Norm_eq hh, PiLp.norm_eq_of_L2]
  rw [e, e, e, WithLp.toLp_sub, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.sqrt_nonneg _)

theorem gridL4Norm_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ}
    (hh : 0 ≤ h) (u : (ι → ZMod n) → F) : 0 ≤ gridL4Norm h u := by
  unfold gridL4Norm; positivity

/-- `‖B · T_i u‖_{2,h} ≤ ‖B‖_{4,h} ‖u‖_{4,h}` for an operator field `B` (pointwise operator norm). -/
theorem gridL2Norm_apply_shift_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    (B : (ι → ZMod n) → F →L[ℝ] G) (u : (ι → ZMod n) → F) (i : ι) :
    gridL2Norm h (fun x => B x (u (x + gridStep i))) ≤ gridL4Norm h B * gridL4Norm h u := by
  set w : (ι → ZMod n) → G := fun x => B x (u (x + gridStep i))
  have hshift : gridL4Norm h (fun x => u (x + gridStep i)) = gridL4Norm h u := by
    unfold gridL4Norm
    rw [sum_add_gridStep (fun x => ‖u x‖ ^ 4) i]
  have hH := gridHolder hι hh B (fun x => u (x + gridStep i)) w
  rw [hshift] at hH
  have hw2 : gridL2Norm h w ^ 2 ≤ h ^ 4 * ∑ x, ‖B x‖ * ‖u (x + gridStep i)‖ * ‖w x‖ := by
    rw [gridL2Norm, periodicHodgeNormSq, Real.sq_sqrt (mul_nonneg (pow_nonneg hh.le _)
      (sum_nonneg fun _ _ => sq_nonneg _)), hι]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => ?_) (by positivity)
    rw [sq]
    exact mul_le_mul_of_nonneg_right ((B x).le_opNorm _) (norm_nonneg _)
  have h0 := gridL2Norm_nonneg h w
  have hP : 0 ≤ gridL4Norm h B * gridL4Norm h u :=
    mul_nonneg (gridL4Norm_nonneg hh.le _) (gridL4Norm_nonneg hh.le _)
  rcases h0.eq_or_lt with hz | hpos
  · rw [← hz]; exact hP
  · nlinarith

/-- `D^+_i u = D^U_i u - B_i · T_i u` with `B_i = (R_i - I)/h`, hence
`‖D^+_i u‖_{2,h} ≤ ‖D^U_i u‖_{2,h} + ‖B_i‖_{4,h} ‖u‖_{4,h}`. -/
theorem gridFwd_le_covFwd_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    (R : (ι → ZMod n) → ι → E →L[ℝ] E) (i : ι) (u : (ι → ZMod n) → E) :
    gridL2Norm h (gridFwd h i u) ≤
      gridL2Norm h (gridCovFwd h (fun x j => R x j) i u) +
        gridL4Norm h (fun x => h⁻¹ • (R x i - 1)) * gridL4Norm h u := by
  have hsplit : gridFwd h i u = gridCovFwd h (fun x j => R x j) i u -
      fun x => (h⁻¹ • (R x i - 1)) (u (x + gridStep i)) := by
    funext x
    simp only [gridFwd, gridCovFwd, Pi.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ← smul_sub]
    congr 1; abel
  rw [hsplit]
  exact (gridL2Norm_sub_le hh _ _).trans (add_le_add le_rfl
    (gridL2Norm_apply_shift_le hι hh (fun x => h⁻¹ • (R x i - 1)) u i))

/-- **Graph norm controls the ordinary discrete `H¹` norm** (last assertion of
`lem:native-critical-grid`, finite part): on the paper's box `L = n h = 2π`, for norm-preserving
(unitary) links `R`, with link coefficients `B_i = (R_i - I)/h`,
`‖D^+_i u‖_{2,h} ≤ ‖D^U_i u‖_{2,h} + 3 ‖B_i‖_{4,h} (‖u‖_{2,h} + Σ_j ‖D^U_j u‖_{2,h})`. -/
theorem gridFwd_le_graphNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h) (hL : (n : ℝ) * h = 2 * Real.pi)
    (R : (ι → ZMod n) → ι → E →L[ℝ] E) (hR : ∀ x i v, ‖R x i v‖ = ‖v‖) (i : ι)
    (u : (ι → ZMod n) → E) :
    gridL2Norm h (gridFwd h i u) ≤
      gridL2Norm h (gridCovFwd h (fun x j => R x j) i u) +
        3 * gridL4Norm h (fun x => h⁻¹ • (R x i - 1)) *
          (gridL2Norm h u + ∑ j, gridL2Norm h (gridCovFwd h (fun x j => R x j) j u)) := by
  have h1 := gridFwd_le_covFwd_add hι hh R i u
  have h2 := (grid_sobolev_L4_two_pi hh hL hι u).2 (fun x j => R x j) hR
  have hB := gridL4Norm_nonneg hh.le (fun x => h⁻¹ • (R x i - 1))
  nlinarith [mul_le_mul_of_nonneg_left h2 hB]

end GraphNorm

end

end RenewalGeometry.GridSobolev
