/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.GridSobolevInequality
import RenewalGeometry.GaugeTheory.WeakSectorReaderIdentities

/-!
# Link-independent covariant embeddings on the periodic 4D grid (`eq:gauge-cov-embed`)

Clause of `cor:gauge-robust-reader` (Einstein–SM action-closure manuscript, `app:gauge-reader`:
"The discrete Kato inequality `eq:gauge-Kato` and ordinary Sobolev inequalities on the fixed grid
imply, for `d ≤ 4`, `‖F‖_{∞,h} ≤ C_d J_{h,3}(F;U)`, `max_{|I| ≤ L-3} ‖D_I^U F‖_{∞,h} ≤
C_{d,L} J_{h,L}(F;U)`, with constants independent of the links").

Setting: the periodic grid `ι → ZMod n` (`card ι = 4`), mesh `h > 0`, side `L = nh`, unitary
represented links `ρ(U_i(x))` (linear isometries of a real normed fibre), covariant differences
`D_i^U` of `WeakReader.covDiff`, scaled norms `‖u‖_{p,h} = (h⁴ Σ ‖u‖^p)^{1/p}`.

* **`morrey_lattice`** — a **discrete Morrey inequality** on the periodic grid, any dimension,
  uniform in `n`: for `p > d`, `|g(z)| ≤ n^α/(2^α - 1) Σ_i ‖w_i‖_{ℓ^p} + (2/n)^{d/p} ‖g‖_{ℓ^p}`
  whenever `|g(x + e_i) - g(x)| ≤ w_i(x)` (`α = 1 - d/p`; dyadic box averages `boxAvg`,
  telescoping along lattice lines and Hölder on embedded boxes).
* `sum_rpow_le_GN` — the `ℓ⁴ → ℓ^{16/3}` Gagliardo–Nirenberg step in four dimensions
  (`GridSobolev.sum_norm_rpow_le_gagliardo` applied to `g⁴`).
* `gridL163_le` (covariant `L⁴ → L^{16/3}`), `morrey_covariant` (covariant Morrey with
  `p = 16/3`), both through the discrete Kato inequality, link-independent.
* `covWord`, `jetEnergy` (`eq:gauge-jet-energy`), **`gauge_cov_embed`** and
  **`gauge_cov_embed_words`** — the two clauses of `eq:gauge-cov-embed` with the explicit
  constant `embC (nh)` (depending only on the box side), independent of the links and of `n`.

Disclosed: the dimension is `d = 4` (the manuscript's spacetime grid; the lower-dimensional
cases are not formalised); the fibre is any real normed space with isometric link action
(`SU(2)` on `ℂ²` realified is a special case).
-/

open Finset

noncomputable section

namespace RenewalGeometry.GaugeCovEmbed

open GridSobolev

set_option linter.unusedSectionVars false

/-! ### A discrete Morrey inequality on the periodic grid -/

section Morrey

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]

/-- The embedding of the index box `[0, r)^d` into the periodic grid. -/
def castV {r : ℕ} (v : ι → Fin r) : ι → ZMod n := fun i => ((v i : ℕ) : ZMod n)

theorem castV_injective {r : ℕ} (hr : r ≤ n) : Function.Injective (castV (ι := ι) (n := n) (r := r)) := by
  intro v v' h
  funext i
  have hi := congrFun h i
  simp only [castV] at hi
  rw [ZMod.natCast_eq_natCast_iff'] at hi
  rw [Nat.mod_eq_of_lt ((v i).2.trans_le hr), Nat.mod_eq_of_lt ((v' i).2.trans_le hr)] at hi
  exact Fin.ext hi

/-- The average of `g` over the box `z + [0, r)^d`. -/
def boxAvg (r : ℕ) (g : (ι → ZMod n) → ℝ) (z : ι → ZMod n) : ℝ :=
  (∑ v : ι → Fin r, g (z + castV v)) / ((r : ℝ) ^ Fintype.card ι)

/-- Sums over an embedded box are bounded by sums over the grid (nonnegative terms). -/
theorem sum_box_le {r : ℕ} (hr : r ≤ n) (f : (ι → ZMod n) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (z : ι → ZMod n) : ∑ v : ι → Fin r, f (z + castV v) ≤ ∑ x, f x := by
  have hinj : Function.Injective fun v : ι → Fin r => z + castV (n := n) v :=
    fun v v' h => castV_injective hr (add_left_cancel h)
  calc ∑ v : ι → Fin r, f (z + castV v) = ∑ x ∈ univ.image (fun v : ι → Fin r => z + castV v), f x := by
        rw [sum_image fun v _ v' _ h => hinj h]
    _ ≤ ∑ x, f x := sum_le_univ_sum_of_nonneg hf

/-- **Hölder on an embedded box**: `Σ_{v ∈ [0,r)^d} G(z + v) ≤ (r^d)^{1 - 1/p} ‖G‖_{ℓ^p}`. -/
theorem sum_box_le_holder {r : ℕ} (hr : r ≤ n) {p : ℝ} (hp : 1 < p) (G : (ι → ZMod n) → ℝ)
    (hG : ∀ x, 0 ≤ G x) (z : ι → ZMod n) :
    ∑ v : ι → Fin r, G (z + castV v) ≤
      ((r : ℝ) ^ Fintype.card ι) ^ (1 - 1 / p) * (∑ x, G x ^ p) ^ (1 / p) := by
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := univ) (f := fun _ : ι → Fin r => (1 : ℝ))
    (g := fun v => G (z + castV v)) hpq.symm (fun _ _ => zero_le_one) (fun v _ => hG _)
  simp only [one_mul, Real.one_rpow, sum_const, card_univ, Fintype.card_pi, Fintype.card_fin,
    prod_const, nsmul_eq_mul, mul_one] at h
  refine h.trans ?_
  have e1 : 1 / (p / (p - 1)) = 1 - 1 / p := by field_simp
  rw [e1]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.rpow_le_rpow (sum_nonneg fun v _ => Real.rpow_nonneg (hG _) _) ?_ (by positivity)
  exact sum_box_le hr (fun x => G x ^ p) (fun x => Real.rpow_nonneg (hG x) _) z

/-- **Shifting a box by its side along a lattice direction** changes the box average by at most
`r (r^d)^{-1/p} ‖w_i‖_{ℓ^p}` when `|g(x + e_i) - g(x)| ≤ w_i(x)` (telescoping and Hölder). -/
theorem boxAvg_shift_le {r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) {p : ℝ} (hp : 1 < p)
    (g : (ι → ZMod n) → ℝ) (w : ι → (ι → ZMod n) → ℝ) (hw0 : ∀ i x, 0 ≤ w i x)
    (hw : ∀ i x, |g (x + gridStep i) - g x| ≤ w i x) (i : ι) (z : ι → ZMod n) :
    |boxAvg r g (z + r • gridStep i) - boxAvg r g z| ≤
      r * ((r : ℝ) ^ Fintype.card ι) ^ (-(1 / p)) * (∑ x, w i x ^ p) ^ (1 / p) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hrd : (0 : ℝ) < (r : ℝ) ^ Fintype.card ι := by positivity
  have htel : ∀ y : ι → ZMod n, g (y + r • gridStep i) - g y =
      ∑ t ∈ range r, (g (y + t • gridStep i + gridStep i) - g (y + t • gridStep i)) := by
    intro y
    have := sum_range_sub (fun t : ℕ => g (y + t • gridStep i)) r
    simp only [succ_nsmul, ← add_assoc, zero_nsmul, add_zero] at this
    rw [this]
  have hdiff : boxAvg r g (z + r • gridStep i) - boxAvg r g z =
      (∑ v : ι → Fin r, ∑ t ∈ range r, (g (z + t • gridStep i + castV v + gridStep i) -
        g (z + t • gridStep i + castV v))) / ((r : ℝ) ^ Fintype.card ι) := by
    rw [boxAvg, boxAvg, ← sub_div, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun v _ => ?_
    rw [show z + r • gridStep i + castV v = (z + castV v) + r • gridStep i by abel, htel]
    refine sum_congr rfl fun t _ => ?_
    congr 1 <;> congr 1 <;> abel
  rw [hdiff, abs_div, abs_of_pos hrd, div_le_iff₀ hrd]
  have hb : ∀ t : ℕ, ∑ v : ι → Fin r, w i (z + t • gridStep i + castV v) ≤
      ((r : ℝ) ^ Fintype.card ι) ^ (1 - 1 / p) * (∑ x, w i x ^ p) ^ (1 / p) := fun t =>
    sum_box_le_holder (r := r) hrn hp (w i) (hw0 i) (z + t • gridStep i)
  calc |∑ v : ι → Fin r, ∑ t ∈ range r, (g (z + t • gridStep i + castV v + gridStep i) -
        g (z + t • gridStep i + castV v))|
      ≤ ∑ v : ι → Fin r, ∑ t ∈ range r, w i (z + t • gridStep i + castV v) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => ?_)
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ => hw i _)
    _ = ∑ t ∈ range r, ∑ v : ι → Fin r, w i (z + t • gridStep i + castV v) := sum_comm
    _ ≤ ∑ _t ∈ range r, ((r : ℝ) ^ Fintype.card ι) ^ (1 - 1 / p) * (∑ x, w i x ^ p) ^ (1 / p) :=
        sum_le_sum fun t _ => hb t
    _ = r * ((r : ℝ) ^ Fintype.card ι) ^ (1 - 1 / p) * (∑ x, w i x ^ p) ^ (1 / p) := by
        rw [sum_const, card_range, nsmul_eq_mul, mul_assoc]
    _ = r * ((r : ℝ) ^ Fintype.card ι) ^ (-(1 / p)) * (∑ x, w i x ^ p) ^ (1 / p) *
          (r : ℝ) ^ Fintype.card ι := by
        rw [show (1 : ℝ) - 1 / p = -(1 / p) + 1 by ring, Real.rpow_add hrd, Real.rpow_one]
        ring

/-- The shift of a box by `r` in every direction of `S`. -/
def shiftS (r : ℕ) (S : Finset ι) : ι → ZMod n := ∑ i ∈ S, r • gridStep i

/-- **Shifting by `r` in a set of directions** changes the box average by at most
`r (r^d)^{-1/p} Σ_{i ∈ S} ‖w_i‖_{ℓ^p}`. -/
theorem boxAvg_shiftS_le {r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) {p : ℝ} (hp : 1 < p)
    (g : (ι → ZMod n) → ℝ) (w : ι → (ι → ZMod n) → ℝ) (hw0 : ∀ i x, 0 ≤ w i x)
    (hw : ∀ i x, |g (x + gridStep i) - g x| ≤ w i x) (S : Finset ι) (z : ι → ZMod n) :
    |boxAvg r g (z + shiftS r S) - boxAvg r g z| ≤
      r * ((r : ℝ) ^ Fintype.card ι) ^ (-(1 / p)) * ∑ i ∈ S, (∑ x, w i x ^ p) ^ (1 / p) := by
  induction S using Finset.induction_on with
  | empty => simp [shiftS]
  | insert a S ha ih =>
    have e : z + shiftS r (insert a S) = (z + shiftS r S) + r • gridStep a := by
      rw [shiftS, sum_insert ha, ← shiftS]; abel
    rw [e, sum_insert ha, mul_add]
    have h1 := boxAvg_shift_le hr1 hrn hp g w hw0 hw a (z + shiftS r S)
    calc |boxAvg r g (z + shiftS r S + r • gridStep a) - boxAvg r g z|
        ≤ |boxAvg r g (z + shiftS r S + r • gridStep a) - boxAvg r g (z + shiftS r S)| +
          |boxAvg r g (z + shiftS r S) - boxAvg r g z| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 ih

/-- The doubling equivalence `[0,2)^d × [0,r)^d ≃ [0,2r)^d`, `(ε, v) ↦ v + rε`. -/
def dblEquiv (r : ℕ) : (ι → Fin 2) × (ι → Fin r) ≃ (ι → Fin (2 * r)) :=
  (Equiv.arrowProdEquivProdArrow ι (fun _ => Fin 2) (fun _ => Fin r)).symm.trans
    (Equiv.piCongrRight fun _ => finProdFinEquiv)

theorem shiftS_apply (r : ℕ) (S : Finset ι) (i : ι) :
    shiftS (n := n) r S i = if i ∈ S then (r : ZMod n) else 0 := by
  rw [shiftS, Finset.sum_apply]
  have : ∀ c, (r • gridStep (n := n) c : ι → ZMod n) i = if i = c then (r : ZMod n) else 0 := by
    intro c
    by_cases h : i = c
    · subst h; simp [gridStep]
    · simp [gridStep, h]
  simp only [this, Finset.sum_ite_eq]

theorem castV_dblEquiv (r : ℕ) (ε : ι → Fin 2) (v : ι → Fin r) :
    castV (n := n) (dblEquiv r (ε, v)) = castV v + shiftS r (univ.filter fun i => ε i = 1) := by
  funext i
  rw [Pi.add_apply, shiftS_apply]
  have hv : ((dblEquiv r (ε, v) i : Fin (2 * r)) : ℕ) = v i + r * ε i := rfl
  simp only [castV, hv]
  by_cases he : ε i = 1
  · simp [he]
  · have h0 : (ε i : ℕ) = 0 := by
      have h2 : (ε i : ℕ) < 2 := (ε i).2
      have : (ε i : ℕ) ≠ 1 := fun h => he (Fin.ext h)
      omega
    simp [he, h0]

/-- **The doubled box average is the mean of the `2^d` sub-box averages.** -/
theorem boxAvg_double (r : ℕ) (hr : 1 ≤ r) (g : (ι → ZMod n) → ℝ) (z : ι → ZMod n) :
    boxAvg (2 * r) g z = (∑ ε : ι → Fin 2, boxAvg r g (z + shiftS r (univ.filter fun i => ε i = 1))) /
      (2 : ℝ) ^ Fintype.card ι := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  rw [boxAvg]
  have e : ∑ u : ι → Fin (2 * r), g (z + castV u) =
      ∑ ε : ι → Fin 2, ∑ v : ι → Fin r, g (z + castV v + shiftS r (univ.filter fun i => ε i = 1)) := by
    rw [← Fintype.sum_prod_type', ← (dblEquiv r).sum_comp]
    refine Fintype.sum_congr _ _ fun p => ?_
    rw [castV_dblEquiv]; congr 1; abel
  rw [e]
  simp only [boxAvg]
  rw [← sum_div, div_div]
  congr 1
  · refine sum_congr rfl fun ε _ => sum_congr rfl fun v _ => ?_
    congr 1; abel
  · push_cast; ring

/-- One dyadic step: `|avg_r g(z) - avg_{2r} g(z)| ≤ r (r^d)^{-1/p} Σ_i ‖w_i‖_{ℓ^p}`. -/
theorem boxAvg_sub_double_le {r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) {p : ℝ} (hp : 1 < p)
    (g : (ι → ZMod n) → ℝ) (w : ι → (ι → ZMod n) → ℝ) (hw0 : ∀ i x, 0 ≤ w i x)
    (hw : ∀ i x, |g (x + gridStep i) - g x| ≤ w i x) (z : ι → ZMod n) :
    |boxAvg r g z - boxAvg (2 * r) g z| ≤
      r * ((r : ℝ) ^ Fintype.card ι) ^ (-(1 / p)) * ∑ i, (∑ x, w i x ^ p) ^ (1 / p) := by
  set B := r * ((r : ℝ) ^ Fintype.card ι) ^ (-(1 / p)) * ∑ i, (∑ x, w i x ^ p) ^ (1 / p)
  have h2d : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι := by positivity
  have hcard : (Fintype.card (ι → Fin 2) : ℝ) = (2 : ℝ) ^ Fintype.card ι := by
    simp [Fintype.card_pi]
  rw [boxAvg_double r hr1 g z]
  have e : boxAvg r g z - (∑ ε : ι → Fin 2,
      boxAvg r g (z + shiftS r (univ.filter fun i => ε i = 1))) / (2 : ℝ) ^ Fintype.card ι =
      (∑ ε : ι → Fin 2, (boxAvg r g z -
        boxAvg r g (z + shiftS r (univ.filter fun i => ε i = 1)))) / (2 : ℝ) ^ Fintype.card ι := by
    rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, hcard]
    field_simp
  rw [e, abs_div, abs_of_pos h2d, div_le_iff₀ h2d]
  have hB : ∀ ε : ι → Fin 2,
      |boxAvg r g z - boxAvg r g (z + shiftS r (univ.filter fun i => ε i = 1))| ≤ B := by
    intro ε
    rw [abs_sub_comm]
    refine (boxAvg_shiftS_le hr1 hrn hp g w hw0 hw _ z).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ =>
      Real.rpow_nonneg (sum_nonneg fun x _ => Real.rpow_nonneg (hw0 i x) p) _
  calc |∑ ε : ι → Fin 2, (boxAvg r g z - boxAvg r g (z + shiftS r (univ.filter fun i => ε i = 1)))|
      ≤ ∑ ε : ι → Fin 2, |boxAvg r g z - boxAvg r g (z + shiftS r (univ.filter fun i => ε i = 1))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ε : ι → Fin 2, B := sum_le_sum fun ε _ => hB ε
    _ = B * (2 : ℝ) ^ Fintype.card ι := by rw [sum_const, card_univ, nsmul_eq_mul, hcard]; ring

theorem boxAvg_one (g : (ι → ZMod n) → ℝ) (z : ι → ZMod n) : boxAvg 1 g z = g z := by
  have : ∀ v : ι → Fin 1, castV (n := n) v = 0 := fun v => by
    funext i; simp [castV, Fin.val_eq_zero (v i)]
  simp [boxAvg, this]

/-- The top box average is bounded by the `ℓ^p` norm: `|avg_r g| ≤ (r^d)^{-1/p} ‖g‖_{ℓ^p}`. -/
theorem abs_boxAvg_le {r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) {p : ℝ} (hp : 1 < p)
    (g : (ι → ZMod n) → ℝ) (z : ι → ZMod n) :
    |boxAvg r g z| ≤ ((r : ℝ) ^ Fintype.card ι) ^ (-(1 / p)) * (∑ x, |g x| ^ p) ^ (1 / p) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hrd : (0 : ℝ) < (r : ℝ) ^ Fintype.card ι := by positivity
  rw [boxAvg, abs_div, abs_of_pos hrd, div_le_iff₀ hrd]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_box_le_holder hrn hp (fun x => |g x|) (fun x => abs_nonneg _) z).trans
    (le_of_eq ?_)
  rw [show (1 : ℝ) - 1 / p = -(1 / p) + 1 by ring, Real.rpow_add hrd, Real.rpow_one]
  ring

/-- `r (r^d)^{-1/p} = r^{1 - d/p}`. -/
theorem mul_rpow_neg_eq {r : ℝ} (hr : 0 < r) (d : ℕ) (p : ℝ) :
    r * (r ^ d) ^ (-(1 / p)) = r ^ (1 - d / p) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, Real.rpow_sub hr, Real.rpow_one]
  rw [show (d : ℝ) * -(1 / p) = -(d / p) by ring, Real.rpow_neg hr.le]
  field_simp

/-- **Dyadic chain**: for `2^K ≤ n`,
`|g(z)| ≤ Σ_{k<K} (2^k)^{1-d/p} Σ_i ‖w_i‖_{ℓ^p} + (2^{Kd})^{-1/p} ‖g‖_{ℓ^p}`. -/
theorem abs_le_dyadic {p : ℝ} (hp : 1 < p) (g : (ι → ZMod n) → ℝ) (w : ι → (ι → ZMod n) → ℝ)
    (hw0 : ∀ i x, 0 ≤ w i x) (hw : ∀ i x, |g (x + gridStep i) - g x| ≤ w i x)
    (z : ι → ZMod n) : ∀ K : ℕ, 2 ^ K ≤ n →
      |g z| ≤ (∑ k ∈ range K, ((2 : ℝ) ^ k) ^ (1 - Fintype.card ι / p)) *
          ∑ i, (∑ x, w i x ^ p) ^ (1 / p) +
        (((2 : ℝ) ^ K) ^ Fintype.card ι) ^ (-(1 / p)) * (∑ x, |g x| ^ p) ^ (1 / p) := by
  set W := ∑ i, (∑ x, w i x ^ p) ^ (1 / p) with hW
  -- telescoping in `k`
  have key : ∀ K : ℕ, 2 ^ K ≤ n →
      |g z - boxAvg (2 ^ K) g z| ≤ (∑ k ∈ range K, ((2 : ℝ) ^ k) ^ (1 - Fintype.card ι / p)) * W := by
    intro K
    induction K with
    | zero => intro _; simp [boxAvg_one]
    | succ K ih =>
      intro hK
      have hK' : 2 ^ K ≤ n := le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)) hK
      have h1 := boxAvg_sub_double_le (r := 2 ^ K) (Nat.one_le_two_pow) hK' hp g w hw0 hw z
      rw [show 2 * 2 ^ K = 2 ^ (K + 1) by ring] at h1
      have h2 : ((2 ^ K : ℕ) : ℝ) * (((2 ^ K : ℕ) : ℝ) ^ Fintype.card ι) ^ (-(1 / p)) =
          ((2 : ℝ) ^ K) ^ (1 - Fintype.card ι / p) := by
        rw [mul_rpow_neg_eq (by positivity)]; push_cast; rfl
      rw [h2] at h1
      rw [sum_range_succ, add_mul]
      calc |g z - boxAvg (2 ^ (K + 1)) g z|
          ≤ |g z - boxAvg (2 ^ K) g z| + |boxAvg (2 ^ K) g z - boxAvg (2 ^ (K + 1)) g z| :=
            abs_sub_le _ _ _
        _ ≤ _ := add_le_add (ih hK') h1
  intro K hK
  have h1 := key K hK
  have h2 := abs_boxAvg_le (r := 2 ^ K) Nat.one_le_two_pow hK hp g z
  push_cast at h2
  calc |g z| ≤ |g z - boxAvg (2 ^ K) g z| + |boxAvg (2 ^ K) g z| := by
        have := abs_sub_abs_le_abs_sub (g z) (boxAvg (2 ^ K) g z)
        linarith
    _ ≤ _ := add_le_add h1 h2

/-- **Discrete Morrey inequality on the periodic grid** (lattice units, uniform in `n`): for
`p > d = card ι`, `α = 1 - d/p`, and `|g(x + e_i) - g(x)| ≤ w_i(x)`,
`|g(z)| ≤ n^α/(2^α - 1) Σ_i ‖w_i‖_{ℓ^p} + (2/n)^{d/p} ‖g‖_{ℓ^p}`.  Proof: dyadic box averages,
each doubling step costing `(2^k)^α Σ_i ‖w_i‖_{ℓ^p}` (telescoping along lattice lines and Hölder
on the boxes), and the top box `2^K ≤ n < 2^{K+1}`. -/
theorem morrey_lattice {p : ℝ} (hp : (Fintype.card ι : ℝ) < p) (hd : 1 ≤ Fintype.card ι)
    (g : (ι → ZMod n) → ℝ) (w : ι → (ι → ZMod n) → ℝ) (hw0 : ∀ i x, 0 ≤ w i x)
    (hw : ∀ i x, |g (x + gridStep i) - g x| ≤ w i x) (z : ι → ZMod n) :
    |g z| ≤ (n : ℝ) ^ (1 - Fintype.card ι / p) / ((2 : ℝ) ^ (1 - Fintype.card ι / p) - 1) *
        ∑ i, (∑ x, w i x ^ p) ^ (1 / p) +
      (2 / (n : ℝ)) ^ (Fintype.card ι / p) * (∑ x, |g x| ^ p) ^ (1 / p) := by
  set d := Fintype.card ι with hdd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  set α := 1 - (d : ℝ) / p with hα
  have hα0 : 0 < α := by
    rw [hα, sub_pos, div_lt_one hp0]; exact hp
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set K := Nat.log 2 n with hK
  have hK1 : 2 ^ K ≤ n := Nat.pow_log_le_self 2 hnpos.ne'
  have hK2 : n < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h := abs_le_dyadic hp1 g w hw0 hw z K hK1
  set W := ∑ i, (∑ x, w i x ^ p) ^ (1 / p) with hW
  set Gp := (∑ x, |g x| ^ p) ^ (1 / p) with hGp
  have hW0 : 0 ≤ W := sum_nonneg fun i _ =>
    Real.rpow_nonneg (sum_nonneg fun x _ => Real.rpow_nonneg (hw0 i x) p) _
  have hGp0 : 0 ≤ Gp := by positivity
  have h2α : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow (by norm_num) hα0
  -- the geometric sum
  have hgeom : ∑ k ∈ range K, ((2 : ℝ) ^ k) ^ α ≤ (n : ℝ) ^ α / ((2 : ℝ) ^ α - 1) := by
    have e : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ α = ((2 : ℝ) ^ α) ^ k := fun k => by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num), mul_comm]
    simp only [e]
    rw [geom_sum_eq h2α.ne', le_div_iff₀ (by linarith), div_mul_cancel₀ _ (by linarith)]
    have : ((2 : ℝ) ^ α) ^ K ≤ (n : ℝ) ^ α := by
      rw [← e K]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hK1) hα0.le
    linarith
  -- the top box
  have htop : (((2 : ℝ) ^ K) ^ d) ^ (-(1 / p)) ≤ (2 / (n : ℝ)) ^ ((d : ℝ) / p) := by
    have hn : (0 : ℝ) < n := by exact_mod_cast hnpos
    have h2K : (n : ℝ) / 2 < (2 : ℝ) ^ K := by
      have : (n : ℝ) < (2 : ℝ) ^ (K + 1) := by exact_mod_cast hK2
      rw [pow_succ] at this; linarith
    rw [← Real.rpow_natCast ((2 : ℝ) ^ K) d, ← Real.rpow_mul (by positivity),
      show (d : ℝ) * -(1 / p) = -((d : ℝ) / p) by ring, Real.rpow_neg (by positivity),
      ← Real.inv_rpow (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
    exact h2K.le
  refine h.trans (add_le_add (mul_le_mul_of_nonneg_right hgeom hW0)
    (mul_le_mul_of_nonneg_right htop hGp0))

end Morrey

/-! ### The `L⁴ → L^{16/3}` Gagliardo–Nirenberg step in four dimensions -/

section GN

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]

theorem abs_pow_four_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a ^ 4 - b ^ 4| ≤ 2 * |a - b| * (a ^ 3 + b ^ 3) := by
  have e : a ^ 4 - b ^ 4 = (a - b) * ((a + b) * (a ^ 2 + b ^ 2)) := by ring
  rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (a + b) * (a ^ 2 + b ^ 2))]
  have h : (a + b) * (a ^ 2 + b ^ 2) ≤ 2 * (a ^ 3 + b ^ 3) := by
    nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]
  nlinarith [abs_nonneg (a - b)]

/-- Hölder `ℓ⁴ × ℓ^{4/3}`: `Σ w g³ ≤ (Σ w⁴)^{1/4} (Σ g⁴)^{3/4}` for nonnegative `w, g`. -/
theorem sum_mul_cube_le {X : Type*} [Fintype X] (w g : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hg : ∀ x, 0 ≤ g x) :
    ∑ x, w x * g x ^ 3 ≤ (∑ x, w x ^ 4) ^ ((1 : ℝ) / 4) * (∑ x, g x ^ 4) ^ ((3 : ℝ) / 4) := by
  have hpq : (4 : ℝ).HolderConjugate (4 / 3) := by
    rw [Real.holderConjugate_iff]; norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := univ) (f := w) (g := fun x => g x ^ 3) hpq
    (fun x _ => hw x) (fun x _ => pow_nonneg (hg x) 3)
  have e1 : ∀ x, w x ^ (4 : ℝ) = w x ^ 4 := fun x => by norm_cast
  have e2 : ∀ x, (g x ^ 3) ^ ((4 : ℝ) / 3) = g x ^ 4 := fun x => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hg x)]; norm_num
  simp only [e1, e2] at h
  refine h.trans (le_of_eq ?_)
  congr 2; norm_num

/-- **The `L⁴ → L^{16/3}` step** (`d = 4`, lattice units, uniform in `n`): for `g ≥ 0` with
`|g(x + e_i) - g(x)| ≤ w_i(x)`,
`Σ g^{16/3} ≤ (4 Σ_i ‖w_i‖_{ℓ⁴} ‖g‖_{ℓ⁴}³ + (4/n) ‖g‖⁴_{ℓ⁴})^{4/3}` (Gagliardo–Nirenberg
`sum_norm_rpow_le_gagliardo` applied to `g⁴`). -/
theorem sum_rpow_le_GN (hι : Fintype.card ι = 4) (g : (ι → ZMod n) → ℝ) (hg : ∀ x, 0 ≤ g x)
    (w : ι → (ι → ZMod n) → ℝ) (hw0 : ∀ i x, 0 ≤ w i x)
    (hw : ∀ i x, |g (x + gridStep i) - g x| ≤ w i x) :
    ∑ x, g x ^ ((16 : ℝ) / 3) ≤
      (∑ i, 4 * ((∑ x, w i x ^ 4) ^ ((1 : ℝ) / 4) * (∑ x, g x ^ 4) ^ ((3 : ℝ) / 4)) +
        4 / n * ∑ x, g x ^ 4) ^ ((4 : ℝ) / 3) := by
  have GN := sum_norm_rpow_le_gagliardo (fun x => g x ^ 4) (by omega : 2 ≤ Fintype.card ι)
  rw [hι] at GN
  have hexp : ((4 : ℕ) : ℝ) / ((4 : ℕ) - 1) = 4 / 3 := by norm_num
  rw [hexp] at GN
  have hL : ∀ x, ‖g x ^ 4‖ ^ ((4 : ℝ) / 3) = g x ^ ((16 : ℝ) / 3) := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hg x) 4), ← Real.rpow_natCast,
      ← Real.rpow_mul (hg x)]
    norm_num
  simp only [hL] at GN
  refine GN.trans (Real.rpow_le_rpow (sum_nonneg fun x _ => sum_nonneg fun i _ => by positivity)
    ?_ (by norm_num))
  set S := ∑ x, g x ^ 4 with hS
  have hstep : ∀ i, ∑ x, ‖g (x + gridStep i) ^ 4 - g x ^ 4‖ ≤
      4 * ((∑ x, w i x ^ 4) ^ ((1 : ℝ) / 4) * S ^ ((3 : ℝ) / 4)) := by
    intro i
    have h1 : ∀ x, ‖g (x + gridStep i) ^ 4 - g x ^ 4‖ ≤
        2 * (w i x * g (x + gridStep i) ^ 3) + 2 * (w i x * g x ^ 3) := by
      intro x
      rw [Real.norm_eq_abs]
      refine (abs_pow_four_sub_le (hg _) (hg _)).trans ?_
      have := hw i x
      have h3 : 0 ≤ g (x + gridStep i) ^ 3 + g x ^ 3 := by
        have := hg (x + gridStep i); have := hg x; positivity
      nlinarith [mul_le_mul_of_nonneg_right this h3]
    have h2 := sum_mul_cube_le (w i) (fun x => g (x + gridStep i)) (hw0 i) (fun x => hg _)
    have h3 := sum_mul_cube_le (w i) g (hw0 i) hg
    have hshift : ∑ x, g (x + gridStep i) ^ 4 = S := sum_add_gridStep (fun x => g x ^ 4) i
    rw [hshift] at h2
    calc ∑ x, ‖g (x + gridStep i) ^ 4 - g x ^ 4‖
        ≤ ∑ x, (2 * (w i x * g (x + gridStep i) ^ 3) + 2 * (w i x * g x ^ 3)) :=
          sum_le_sum fun x _ => h1 x
      _ = 2 * ∑ x, w i x * g (x + gridStep i) ^ 3 + 2 * ∑ x, w i x * g x ^ 3 := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ _ := by linarith
  rw [sum_comm]
  simp only [sum_add_distrib]
  have hc : ∑ i : ι, ∑ x, ‖g x ^ 4‖ / (n : ℝ) = 4 / n * S := by
    have : ∀ x, ‖g x ^ 4‖ = g x ^ 4 := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hg x) 4)]
    simp only [this, ← sum_div, sum_const, card_univ, hι, nsmul_eq_mul]
    rw [hS]; push_cast; ring
  rw [hc]
  exact add_le_add (sum_le_sum fun i _ => hstep i) le_rfl

end GN

/-! ### Scaled covariant embeddings -/

section Covariant

open WeakReader

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The discrete `L^{16/3}` norm `‖u‖_{16/3,h} = (h^d Σ_x ‖u x‖^{16/3})^{3/16}`. -/
def gridL163 (h : ℝ) (u : (ι → ZMod n) → V) : ℝ :=
  (h ^ Fintype.card ι * ∑ x, ‖u x‖ ^ ((16 : ℝ) / 3)) ^ ((3 : ℝ) / 16)

theorem gridL163_nonneg (h : ℝ) (hh : 0 < h) (u : (ι → ZMod n) → V) : 0 ≤ gridL163 h u := by
  unfold gridL163; positivity

/-- The scaled covariant difference of `WeakReader` on the periodic grid. -/
abbrev Dc (h : ℝ) (ρU : (ι → ZMod n) → ι → V →L[ℝ] V) (i : ι) (u : (ι → ZMod n) → V) :
    (ι → ZMod n) → V :=
  covDiff gridStep h ρU i u

/-- Kato in lattice units: `|‖u(x+e_i)‖ - ‖u(x)‖| ≤ h ‖D_i^U u(x)‖`. -/
theorem kato_lattice {h : ℝ} (hh : 0 < h) {ρU : (ι → ZMod n) → ι → V →L[ℝ] V}
    (hiso : ∀ x i (v : V), ‖ρU x i v‖ = ‖v‖) (i : ι) (u : (ι → ZMod n) → V) (x : ι → ZMod n) :
    |‖u (x + gridStep i)‖ - ‖u x‖| ≤ h * ‖Dc h ρU i u x‖ := by
  have := abs_kato_le gridStep hh hiso i u x
  rw [abs_div, abs_of_pos hh, div_le_iff₀ hh] at this
  linarith

theorem rpow_three_quarters (S : ℝ) (hS : 0 ≤ S) :
    S ^ ((3 : ℝ) / 4) = (S ^ ((1 : ℝ) / 4)) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hS]; norm_num

theorem sum_mul_pow_rpow {X : Type*} [Fintype X] {h : ℝ} (hh : 0 ≤ h) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p) :
    (∑ x, (h * f x) ^ p) ^ (1 / p) = h * (∑ x, f x ^ p) ^ (1 / p) := by
  simp only [Real.mul_rpow hh (hf _)]
  rw [← mul_sum, Real.mul_rpow (by positivity) (sum_nonneg fun x _ => by have := hf x; positivity),
    ← Real.rpow_mul hh, mul_one_div_cancel hp.ne', Real.rpow_one]

theorem rpow_le_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4) ≤ x + y := by
  have h1 : x ^ ((3 : ℝ) / 4) ≤ (x + y) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow hx (by linarith) (by norm_num)
  have h2 : y ^ ((1 : ℝ) / 4) ≤ (x + y) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hy (by linarith) (by norm_num)
  calc x ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4) ≤ (x + y) ^ ((3 : ℝ) / 4) * (x + y) ^ ((1 : ℝ) / 4) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = x + y := by rw [← Real.rpow_add' (by linarith) (by norm_num)]; norm_num

/-- **Covariant `L⁴ → L^{16/3}` embedding** (`d = 4`, link-independent, uniform in `n`): for
unitary links, `‖u‖_{16/3,h} ≤ ‖u‖_{4,h} + 4 Σ_i ‖D_i^U u‖_{4,h} + (4/L) ‖u‖_{4,h}`, `L = nh`. -/
theorem gridL163_le (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    {ρU : (ι → ZMod n) → ι → V →L[ℝ] V} (hiso : ∀ x i (v : V), ‖ρU x i v‖ = ‖v‖)
    (u : (ι → ZMod n) → V) :
    gridL163 h u ≤ gridL4Norm h u + (4 * ∑ i, gridL4Norm h (Dc h ρU i u) +
      4 / (n * h) * gridL4Norm h u) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set g : (ι → ZMod n) → ℝ := fun x => ‖u x‖ with hg
  have GN := sum_rpow_le_GN hι g (fun x => norm_nonneg _) (fun i x => h * ‖Dc h ρU i u x‖)
    (fun i x => by positivity) (fun i x => kato_lattice hh hiso i u x)
  set S := ∑ x, g x ^ 4 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun x _ => by positivity
  obtain ⟨a, ha⟩ : ∃ a, a = S ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  obtain ⟨b, hb⟩ : ∃ b : ι → ℝ, b = fun i => (∑ x, ‖Dc h ρU i u x‖ ^ 4) ^ ((1 : ℝ) / 4) :=
    ⟨_, rfl⟩
  have hb0 : ∀ i, 0 ≤ b i := fun i => by rw [hb]; positivity
  have hwb : ∀ i, (∑ x, (h * ‖Dc h ρU i u x‖) ^ 4) ^ ((1 : ℝ) / 4) = h * b i := by
    intro i
    rw [hb]
    simp only [mul_pow]
    rw [← mul_sum, Real.mul_rpow (by positivity) (sum_nonneg fun x _ => by positivity),
      ← Real.rpow_natCast h 4, ← Real.rpow_mul hh.le]
    norm_num
  have hS34 : S ^ ((3 : ℝ) / 4) = a ^ 3 := by rw [rpow_three_quarters S hS0, ha]
  have hS4 : S = a ^ 4 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hS0]; norm_num
  obtain ⟨c, hc⟩ : ∃ c, c = 4 * h * ∑ i, b i + 4 / n * a := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    have : 0 ≤ ∑ i, b i := sum_nonneg fun i _ => hb0 i
    rw [hc]; positivity
  have hinner : ∑ i, 4 * ((∑ x, (h * ‖Dc h ρU i u x‖) ^ 4) ^ ((1 : ℝ) / 4) * S ^ ((3 : ℝ) / 4)) +
      4 / n * S = a ^ 3 * c := by
    rw [hS34]
    simp only [hwb]
    rw [hc, hS4, mul_add, mul_sum, mul_sum]
    congr 1
    · exact sum_congr rfl fun i _ => by ring
    · ring
  rw [hinner] at GN
  -- scaled norms
  have h4 : gridL4Norm h u = h * a := by
    rw [gridL4Norm, hι, Real.mul_rpow (by positivity) hS0, ← Real.rpow_natCast,
      ← Real.rpow_mul hh.le]
    norm_num
    exact Or.inl ha.symm
  have h4D : ∀ i, gridL4Norm h (Dc h ρU i u) = h * b i := by
    intro i
    rw [gridL4Norm, hι, Real.mul_rpow (by positivity) (sum_nonneg fun x _ => by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num
    exact Or.inl (by rw [hb])
  have hcs : c = 4 * ∑ i, gridL4Norm h (Dc h ρU i u) + 4 / (n * h) * gridL4Norm h u := by
    simp only [h4D, h4, hc, ← mul_sum]
    field_simp
  have hmain : gridL163 h u ≤ (h * a) ^ ((3 : ℝ) / 4) * c ^ ((1 : ℝ) / 4) := by
    rw [gridL163, hι]
    have hsum0 : 0 ≤ ∑ x, ‖u x‖ ^ ((16 : ℝ) / 3) := sum_nonneg fun x _ => by positivity
    calc ((h ^ 4 : ℝ) * ∑ x, ‖u x‖ ^ ((16 : ℝ) / 3)) ^ ((3 : ℝ) / 16)
        ≤ ((h ^ 4 : ℝ) * (a ^ 3 * c) ^ ((4 : ℝ) / 3)) ^ ((3 : ℝ) / 16) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left GN (by positivity)
      _ = (h * a) ^ ((3 : ℝ) / 4) * c ^ ((1 : ℝ) / 4) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
            Real.mul_rpow (by positivity) hc0, Real.mul_rpow hh.le ha0]
          rw [← Real.rpow_natCast h 4, ← Real.rpow_mul hh.le, ← Real.rpow_natCast a 3,
            ← Real.rpow_mul ha0]
          norm_num
          ring
  rw [hcs] at hmain
  refine hmain.trans ?_
  rw [← h4]
  exact rpow_le_add (by rw [h4]; positivity) (by rw [← hcs]; exact hc0)

theorem gridL163_eq (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h) (u : (ι → ZMod n) → V) :
    gridL163 h u = h ^ ((3 : ℝ) / 4) * (∑ x, ‖u x‖ ^ ((16 : ℝ) / 3)) ^ ((3 : ℝ) / 16) := by
  rw [gridL163, hι, Real.mul_rpow (by positivity) (sum_nonneg fun x _ => by positivity),
    ← Real.rpow_natCast h 4, ← Real.rpow_mul hh.le]
  norm_num

/-- **Covariant discrete Morrey inequality** (`d = 4`, scaled, link-independent, uniform in `n`):
for unitary links and `L = nh`,
`‖u(z)‖ ≤ L^{1/4}/(2^{1/4} - 1) Σ_i ‖D_i^U u‖_{16/3,h} + (2/L)^{3/4} ‖u‖_{16/3,h}`
(`morrey_lattice` with `p = 16/3 > 4` for `|u|`, the discrete Kato inequality). -/
theorem morrey_covariant (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    {ρU : (ι → ZMod n) → ι → V →L[ℝ] V} (hiso : ∀ x i (v : V), ‖ρU x i v‖ = ‖v‖)
    (u : (ι → ZMod n) → V) (z : ι → ZMod n) :
    ‖u z‖ ≤ (n * h) ^ ((1 : ℝ) / 4) / ((2 : ℝ) ^ ((1 : ℝ) / 4) - 1) *
        ∑ i, gridL163 h (Dc h ρU i u) + (2 / (n * h)) ^ ((3 : ℝ) / 4) * gridL163 h u := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hM := morrey_lattice (p := 16 / 3) (by rw [hι]; norm_num) (by omega)
    (fun x => ‖u x‖) (fun i x => h * ‖Dc h ρU i u x‖) (fun i x => by positivity)
    (fun i x => kato_lattice hh hiso i u x) z
  rw [hι] at hM
  have e1 : (1 : ℝ) - ((4 : ℕ) : ℝ) / (16 / 3) = 1 / 4 := by norm_num
  have e2 : ((4 : ℕ) : ℝ) / (16 / 3) = 3 / 4 := by norm_num
  have e3 : (1 : ℝ) / (16 / 3) = 3 / 16 := by norm_num
  rw [e1, e2, e3] at hM
  simp only [abs_norm] at hM
  have hD : ∀ i, (∑ x, (h * ‖Dc h ρU i u x‖) ^ ((16 : ℝ) / 3)) ^ ((3 : ℝ) / 16) =
      h ^ ((1 : ℝ) / 4) * gridL163 h (Dc h ρU i u) := by
    intro i
    have := sum_mul_pow_rpow hh.le (fun x => ‖Dc h ρU i u x‖) (fun x => norm_nonneg _)
      (p := 16 / 3) (by norm_num)
    rw [e3] at this
    rw [this, gridL163_eq hι hh, ← mul_assoc, ← Real.rpow_add hh]
    norm_num
  have hU : (2 / (n : ℝ)) ^ ((3 : ℝ) / 4) * (∑ x, ‖u x‖ ^ ((16 : ℝ) / 3)) ^ ((3 : ℝ) / 16) =
      (2 / (n * h)) ^ ((3 : ℝ) / 4) * gridL163 h u := by
    rw [gridL163_eq hι hh, ← mul_assoc, ← Real.mul_rpow (by positivity) hh.le]
    congr 2
    field_simp
  simp only [hD] at hM
  rw [hU] at hM
  refine hM.trans (le_of_eq ?_)
  congr 1
  rw [← mul_sum, Real.mul_rpow hn.le hh.le]
  ring

/-! ### The covariant jet energy and `eq:gauge-cov-embed` -/

/-- The covariant word derivative `D_I^U F = D_{i₁}^U ⋯ D_{i_ℓ}^U F` (`eq:gauge-covdiff`). -/
def covWord (h : ℝ) (ρU : (ι → ZMod n) → ι → V →L[ℝ] V) :
    List ι → ((ι → ZMod n) → V) → (ι → ZMod n) → V
  | [], F => F
  | i :: I, F => Dc h ρU i (covWord h ρU I F)

theorem covWord_append (h : ℝ) (ρU : (ι → ZMod n) → ι → V →L[ℝ] V) (K I : List ι)
    (F : (ι → ZMod n) → V) : covWord h ρU (K ++ I) F = covWord h ρU K (covWord h ρU I F) := by
  induction K with
  | nil => rfl
  | cons i K ih => simp only [List.cons_append, covWord, ih]

/-- **The finite covariant-jet energy** `J_{h,L}(F;U) = (Σ_{ℓ ≤ L} Σ_{|I| = ℓ} ‖D_I^U F‖²_{2,h})^{1/2}`
(`eq:gauge-jet-energy`; words are ordered). -/
def jetEnergy (h : ℝ) (ρU : (ι → ZMod n) → ι → V →L[ℝ] V) (L : ℕ) (F : (ι → ZMod n) → V) : ℝ :=
  √(∑ ℓ ∈ range (L + 1), ∑ I : Fin ℓ → ι, gridL2Norm h (covWord h ρU (List.ofFn I) F) ^ 2)

theorem gridL2Norm_le_jetEnergy (h : ℝ) (ρU : (ι → ZMod n) → ι → V →L[ℝ] V) {L : ℕ}
    (F : (ι → ZMod n) → V) (K : List ι) (hK : K.length ≤ L) :
    gridL2Norm h (covWord h ρU K F) ≤ jetEnergy h ρU L F := by
  rw [jetEnergy]
  refine Real.le_sqrt_of_sq_le ?_
  have h1 : gridL2Norm h (covWord h ρU K F) ^ 2 ≤
      ∑ I : Fin K.length → ι, gridL2Norm h (covWord h ρU (List.ofFn I) F) ^ 2 := by
    have := Finset.single_le_sum (f := fun I : Fin K.length → ι =>
      gridL2Norm h (covWord h ρU (List.ofFn I) F) ^ 2) (fun I _ => sq_nonneg _)
      (Finset.mem_univ K.get)
    simpa [List.ofFn_get] using this
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun ℓ => ∑ I : Fin ℓ → ι,
    gridL2Norm h (covWord h ρU (List.ofFn I) F) ^ 2)
    (fun ℓ _ => sum_nonneg fun I _ => sq_nonneg _) (mem_range.2 (Nat.lt_succ_of_le hK))

/-- The embedding constant (depends only on the box side `L = nh`). -/
def embC (Lb : ℝ) : ℝ :=
  (4 * Lb ^ ((1 : ℝ) / 4) / ((2 : ℝ) ^ ((1 : ℝ) / 4) - 1) + (2 / Lb) ^ ((3 : ℝ) / 4)) *
    ((12 + 4 / Lb) * (17 + 4 / Lb))

theorem two_rpow_quarter_gt_one : 1 < (2 : ℝ) ^ ((1 : ℝ) / 4) :=
  Real.one_lt_rpow (by norm_num) (by norm_num)

/-- **The core covariant embedding**: if all covariant words of length `≤ 3` of `u` are bounded
by `B` in `L²_h`, then `‖u‖_∞ ≤ C(L) B` (`L = nh`), with `C` independent of the links and of `n`
(covariant `L⁴` Sobolev, covariant `L^{16/3}` Gagliardo–Nirenberg, covariant Morrey). -/
theorem sup_le_of_words (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    {ρU : (ι → ZMod n) → ι → V →L[ℝ] V} (hiso : ∀ x i (v : V), ‖ρU x i v‖ = ‖v‖)
    (u : (ι → ZMod n) → V) {B : ℝ}
    (hB : ∀ K : List ι, K.length ≤ 3 → gridL2Norm h (covWord h ρU K u) ≤ B) (z : ι → ZMod n) :
    ‖u z‖ ≤ embC (n * h) * B := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set Lb := (n : ℝ) * h with hLb
  have hLb0 : 0 < Lb := by positivity
  have hB0 : 0 ≤ B := (gridL2Norm_nonneg h u).trans (hB [] (by simp))
  have hcard : ∀ c : ℝ, ∑ _i : ι, c = 4 * c := fun c => by
    rw [sum_const, card_univ, hι, nsmul_eq_mul]; norm_num
  set a := 12 + 4 / Lb with ha
  set b := a * (17 + 4 / Lb) with hb
  have ha0 : 0 ≤ a := by positivity
  -- (A) `L⁴` bounds for words of length `≤ 2`
  have hA : ∀ K : List ι, K.length ≤ 2 → gridL4Norm h (covWord h ρU K u) ≤ a * B := by
    intro K hK
    have hS := grid_sobolev_L4_covariant hh hι (fun x i v => ρU x i v) hiso
      (covWord h ρU K u)
    refine hS.trans ?_
    have h1 : ∑ i, gridL2Norm h (gridCovFwd h (fun x i v => ρU x i v) i (covWord h ρU K u)) ≤
        4 * B := by
      rw [← hcard]
      refine sum_le_sum fun i _ => ?_
      exact hB (i :: K) (by simp; omega)
    have h2 := hB K (by omega)
    have h3 : 4 / (n * h) * gridL2Norm h (covWord h ρU K u) ≤ 4 / Lb * B :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [ha]; nlinarith
  -- (B) `L^{16/3}` bounds for words of length `≤ 1`
  have hBb : ∀ K : List ι, K.length ≤ 1 → gridL163 h (covWord h ρU K u) ≤ b * B := by
    intro K hK
    refine (gridL163_le hι hh hiso (covWord h ρU K u)).trans ?_
    have h1 := hA K (by omega)
    have h2 : ∑ i, gridL4Norm h (Dc h ρU i (covWord h ρU K u)) ≤ 4 * (a * B) := by
      rw [← hcard]
      exact sum_le_sum fun i _ => hA (i :: K) (by simp; omega)
    have h3 : 4 / (n * h) * gridL4Norm h (covWord h ρU K u) ≤ 4 / Lb * (a * B) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hb]; nlinarith
  -- (C) Morrey
  refine (morrey_covariant hι hh hiso u z).trans ?_
  have h1 : ∑ i, gridL163 h (Dc h ρU i u) ≤ 4 * (b * B) := by
    rw [← hcard]
    exact sum_le_sum fun i _ => hBb [i] (by simp)
  have h2 := hBb [] (by simp)
  have hq : 0 < (2 : ℝ) ^ ((1 : ℝ) / 4) - 1 := by linarith [two_rpow_quarter_gt_one]
  have hc1 : 0 ≤ Lb ^ ((1 : ℝ) / 4) / ((2 : ℝ) ^ ((1 : ℝ) / 4) - 1) := by positivity
  have hc2 : 0 ≤ (2 / Lb) ^ ((3 : ℝ) / 4) := by positivity
  calc Lb ^ ((1 : ℝ) / 4) / ((2 : ℝ) ^ ((1 : ℝ) / 4) - 1) * ∑ i, gridL163 h (Dc h ρU i u) +
        (2 / Lb) ^ ((3 : ℝ) / 4) * gridL163 h (covWord h ρU [] u)
      ≤ Lb ^ ((1 : ℝ) / 4) / ((2 : ℝ) ^ ((1 : ℝ) / 4) - 1) * (4 * (b * B)) +
        (2 / Lb) ^ ((3 : ℝ) / 4) * (b * B) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hc1) (mul_le_mul_of_nonneg_left h2 hc2)
    _ = embC Lb * B := by rw [embC, hb, ha]; ring

/-- **`eq:gauge-cov-embed`, first clause** (`d ≤ 4`, here `d = 4`): on the periodic grid
`(ℤ/n)⁴` with mesh `h` and side `L = nh`, for unitary links (any real normed fibre),
`‖F‖_{∞,h} ≤ C_L J_{h,3}(F; U)` with `C_L = embC L` independent of the links and of `n`. -/
theorem gauge_cov_embed (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    {ρU : (ι → ZMod n) → ι → V →L[ℝ] V} (hiso : ∀ x i (v : V), ‖ρU x i v‖ = ‖v‖)
    (F : (ι → ZMod n) → V) (z : ι → ZMod n) :
    ‖F z‖ ≤ embC (n * h) * jetEnergy h ρU 3 F :=
  sup_le_of_words hι hh hiso F (fun K hK => gridL2Norm_le_jetEnergy h ρU F K hK) z

/-- **`eq:gauge-cov-embed`, second clause**: `max_{|I| ≤ L-3} ‖D_I^U F‖_{∞,h} ≤ C_L J_{h,L}(F; U)`,
with the same link- and `n`-independent constant. -/
theorem gauge_cov_embed_words (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    {ρU : (ι → ZMod n) → ι → V →L[ℝ] V} (hiso : ∀ x i (v : V), ‖ρU x i v‖ = ‖v‖)
    (L : ℕ) (F : (ι → ZMod n) → V) (I : List ι) (hI : I.length + 3 ≤ L) (z : ι → ZMod n) :
    ‖covWord h ρU I F z‖ ≤ embC (n * h) * jetEnergy h ρU L F := by
  refine sup_le_of_words hι hh hiso (covWord h ρU I F) (fun K hK => ?_) z
  rw [← covWord_append]
  exact gridL2Norm_le_jetEnergy h ρU F (K ++ I) (by simp; omega)

/-! ### Non-vacuity -/

/-- **Non-vacuity of `gauge_cov_embed`**: on `(ℤ/3)⁴` with `h = 1`, trivial (identity) links and
a real fibre, the hypotheses hold and the embedding applies to every field. -/
example (F : (Fin 4 → ZMod 3) → ℝ) (z : Fin 4 → ZMod 3) :
    ‖F z‖ ≤ embC ((3 : ℕ) * (1 : ℝ)) *
      jetEnergy (ι := Fin 4) (n := 3) 1 (fun _ _ => ContinuousLinearMap.id ℝ ℝ) 3 F :=
  gauge_cov_embed (by simp) one_pos (fun _ _ _ => rfl) F z

end Covariant

end RenewalGeometry.GaugeCovEmbed
