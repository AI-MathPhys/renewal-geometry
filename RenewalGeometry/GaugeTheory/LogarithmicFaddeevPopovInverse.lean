/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.OperatorHalfCoth
import RenewalGeometry.DiscreteAnalysis.GridSobolevInequality

/-!
# The uniform transverse inverse of the logarithmic discrete Faddeev–Popov operator
  (`lem:native-FP-inverse`, eqs. `eq:native-FP`, `eq:native-FP-coercivity`,
  `eq:native-FP-dual-inverse`, `eq:native-FP-divergence-inverse`; Einstein–SM action closure)

Setting.  The periodic grid `(ℤ/n)^ι` with `card ι = 4` (unit steps `gridStep`), mesh `h > 0`,
side `L = n h`.  The Lie algebra is a finite-dimensional real inner product space `E` with a
continuous bilinear bracket `br a b = [a, b]` whose inner product is invariant,
`⟪[a, b], c⟫ = -⟪b, [a, c]⟫` (`ad_a` skew-adjoint; the Jacobi identity is not used).  For a nodal
Lie-algebra one-form `A : ι → (ι → ZMod n) → E` and a site field `ξ`:
* `midAvg μ ξ = ½(ξ + T_μ ξ)` (`m_μ`), `gridFwd h μ ξ = D^+_μ ξ`;
* `fpFlux br h A ξ μ = 𝒦(h ad_{A_μ}) D^+_μ ξ + [A_μ, m_μ ξ]` with
  `𝒦(Z) = (Z/2)coth(Z/2) = ½ 𝒥(Z)⁻¹(I + e^Z)` (`OperatorHalfCoth.halfCoth`);
* `fpOp br h A ξ = δ_h (fpFlux br h A ξ)` (`eq:native-FP`, `δ_h = -Σ_μ D^-_μ`).

Results (the threshold `rFP br = 1/(64(‖br‖+1))` depends only on the bracket norm, not on `n`
or `h`; `‖A_μ‖_{4,h} < rFP` for every direction is implied by the paper's `‖A‖_{4,h} < r_FP`):
* `fp_coercive` — `⟨M_A ξ, ξ⟩_{2,h} ≥ ½ ‖D^+ξ‖²_{2,h}` on the mean-zero space `𝒵_h`;
* `fp_bijective` — `M_A : 𝒵_h → 𝒵_h` is bijective;
* `fp_dual_inverse`, `fp_dual_inverse_sSup` — `‖D^+ M_A⁻¹ f‖_{2,h} ≤ 2‖f‖_{\dot H^{-1}_h}`;
* `fp_divergence_inverse` — `‖M_A⁻¹ δ_h R‖_{2,h} + ‖M_A⁻¹ δ_h R‖_{4,h} + ‖D^+ M_A⁻¹ δ_h R‖_{2,h}
  ≤ C ‖R‖_{2,h}` with `C = 2 + 2√2 L + 4(3 + 2√2)`;
* `fp_inverse_contDiffOn` — smooth dependence of the inverse on `A`.
-/

open Finset

namespace RenewalGeometry.FaddeevPopov

open GridSobolev OperatorHalfCoth

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Grid inner products, Dirichlet energy, summation by parts -/

/-- `⟨f, g⟩_{2,h} = h^d Σ_x ⟪f x, g x⟫`. -/
def gridInner (h : ℝ) (f g : (ι → ZMod n) → E) : ℝ :=
  h ^ Fintype.card ι * ∑ x, inner ℝ (f x) (g x)

/-- `‖D^+ξ‖²_{2,h} = Σ_μ ‖D^+_μ ξ‖²_{2,h}`. -/
def dirSq (h : ℝ) (ξ : (ι → ZMod n) → E) : ℝ :=
  ∑ μ, periodicHodgeNormSq ι h (gridFwd h μ ξ)

omit [Fintype ι] [NeZero n] in
theorem gridFwd_eq_periodicHodgeFwd (h : ℝ) (μ : ι) (u : (ι → ZMod n) → E) :
    gridFwd h μ u = periodicHodgeFwd h gridStep μ u := rfl

theorem normSq_nonneg {F : Type*} [NormedAddCommGroup F] {h : ℝ} (hh : 0 ≤ h)
    (u : (ι → ZMod n) → F) : 0 ≤ periodicHodgeNormSq ι h u :=
  mul_nonneg (pow_nonneg hh _) (sum_nonneg fun _ _ => sq_nonneg _)

theorem dirSq_nonneg {h : ℝ} (hh : 0 ≤ h) (ξ : (ι → ZMod n) → E) : 0 ≤ dirSq h ξ :=
  sum_nonneg fun _ _ => normSq_nonneg hh _

theorem gridL2Norm_sq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ} (hh : 0 ≤ h)
    (u : (ι → ZMod n) → F) : gridL2Norm h u ^ 2 = periodicHodgeNormSq ι h u :=
  Real.sq_sqrt (normSq_nonneg hh u)

theorem dirSq_eq_sum_sq {h : ℝ} (hh : 0 ≤ h) (ξ : (ι → ZMod n) → E) :
    dirSq h ξ = ∑ μ, gridL2Norm h (gridFwd h μ ξ) ^ 2 := by
  simp only [dirSq, gridL2Norm_sq hh]

/-- Summation by parts: `⟨δ_h W, ξ⟩ = Σ_μ ⟨W_μ, D^+_μ ξ⟩`. -/
theorem sum_inner_codiff (h : ℝ) (W : ι → (ι → ZMod n) → E) (ξ : (ι → ZMod n) → E) :
    ∑ x, inner ℝ (periodicHodgeCodiff h gridStep W x) (ξ x) =
      ∑ μ, ∑ x, inner ℝ (W μ x) (gridFwd h μ ξ x) := by
  simp only [periodicHodgeCodiff, periodicHodgeBwd, gridFwd, inner_neg_left, sum_inner,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, sum_neg_distrib]
  rw [sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun μ _ => ?_
  have hsh : ∑ x, inner ℝ (W μ (x - gridStep μ)) (ξ x) =
      ∑ x, inner ℝ (W μ x) (ξ (x + gridStep μ)) :=
    (Fintype.sum_equiv (Equiv.addRight (gridStep μ)) _ _ (fun x => by simp)).symm
  simp only [RCLike.conj_to_real, ← mul_sum, sum_sub_distrib, hsh]
  ring

/-- A grid field with vanishing forward differences is constant. -/
theorem eq_const_of_fwd_zero {M : Type*} [AddCommGroup M] (g : (ι → ZMod n) → M)
    (hg : ∀ i y, g (y + gridStep i) = g y) (x : ι → ZMod n) : g x = g 0 := by
  have hk : ∀ i (k : ℕ) y, g (y + k • gridStep i) = g y := by
    intro i k
    induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [succ_nsmul, ← add_assoc, hg, ih]
  have hs : ∀ (s : Finset ι) y, g (y + ∑ i ∈ s, (x i).val • gridStep i) = g y := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert j s hj ih => intro y; rw [sum_insert hj, ← add_assoc, ih, hk]
  have hx : x = ∑ i, (x i).val • (gridStep i : ι → ZMod n) := by
    conv_lhs => rw [← univ_sum_single x]
    exact sum_congr rfl fun i _ => single_eq_val_nsmul x i
  have := hs univ 0
  rwa [zero_add, ← hx] at this

/-- A mean-zero field with zero Dirichlet energy vanishes. -/
theorem eq_zero_of_dirSq_eq_zero {h : ℝ} (hh : 0 < h) (ξ : (ι → ZMod n) → E)
    (hs : ∑ x, ξ x = 0) (hd : dirSq h ξ = 0) : ξ = 0 := by
  have h1 : ∀ μ, periodicHodgeNormSq ι h (gridFwd h μ ξ) = 0 := fun μ =>
    (sum_eq_zero_iff_of_nonneg fun μ _ => normSq_nonneg hh.le _).1 hd μ (mem_univ μ)
  have h2 : ∀ μ x, ξ (x + gridStep μ) = ξ x := by
    intro μ x
    have := h1 μ
    rw [periodicHodgeNormSq, mul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 (pow_ne_zero _ hh.ne')
    · have hx := (sum_eq_zero_iff_of_nonneg fun x _ => sq_nonneg ‖gridFwd h μ ξ x‖).1 h0 x
        (mem_univ x)
      have : gridFwd h μ ξ x = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hx)
      rw [gridFwd, smul_eq_zero] at this
      rcases this with h3 | h3
      · exact absurd h3 (inv_ne_zero hh.ne')
      · exact sub_eq_zero.1 h3
  have hc := eq_const_of_fwd_zero ξ h2
  have hsum : ∑ x : ι → ZMod n, ξ x = (Fintype.card (ι → ZMod n)) • ξ 0 := by
    rw [sum_congr rfl fun x _ => hc x, sum_const, card_univ]
  rw [hs] at hsum
  have h0 : ξ 0 = 0 := by
    have hN : Fintype.card (ι → ZMod n) ≠ 0 := Fintype.card_ne_zero
    have := hsum.symm
    rw [← Nat.cast_smul_eq_nsmul ℝ] at this
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hN)
  funext x; rw [hc, h0]; rfl

/-! ### The midpoint average -/

/-- The midpoint average `m_μ ξ = ½(ξ + T_μ ξ)`. -/
def midAvg (μ : ι) (ξ : (ι → ZMod n) → E) (x : ι → ZMod n) : E :=
  (1 / 2 : ℝ) • (ξ x + ξ (x + gridStep μ))

omit [DecidableEq ι] [NeZero n] in
theorem pow_four_mid_le (p q : ℝ) :
    ((p + q) / 2) ^ 4 ≤ (p ^ 4 + q ^ 4) / 2 := by
  have h1 : ((p + q) / 2) ^ 2 ≤ (p ^ 2 + q ^ 2) / 2 := by nlinarith [sq_nonneg (p - q)]
  have h2 : ((p ^ 2 + q ^ 2) / 2) ^ 2 ≤ (p ^ 4 + q ^ 4) / 2 := by nlinarith [sq_nonneg (p ^ 2 - q ^ 2)]
  calc ((p + q) / 2) ^ 4 = (((p + q) / 2) ^ 2) ^ 2 := by ring
    _ ≤ ((p ^ 2 + q ^ 2) / 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ ≤ _ := h2

/-- `‖m_μ ξ‖_{4,h} ≤ ‖ξ‖_{4,h}`. -/
theorem gridL4Norm_midAvg_le {h : ℝ} (hh : 0 ≤ h) (μ : ι) (ξ : (ι → ZMod n) → E) :
    gridL4Norm h (midAvg μ ξ) ≤ gridL4Norm h ξ := by
  rw [gridL4Norm, gridL4Norm]
  refine Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left ?_ (by positivity))
    (by norm_num)
  have hpt : ∀ x, ‖midAvg μ ξ x‖ ^ 4 ≤ (‖ξ x‖ ^ 4 + ‖ξ (x + gridStep μ)‖ ^ 4) / 2 := by
    intro x
    have hn : ‖midAvg μ ξ x‖ ≤ (‖ξ x‖ + ‖ξ (x + gridStep μ)‖) / 2 := by
      rw [midAvg, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := norm_add_le (ξ x) (ξ (x + gridStep μ))
      linarith
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 4).trans
      (pow_four_mid_le _ _)
  have hsh : ∑ x, ‖ξ (x + gridStep μ)‖ ^ 4 = ∑ x, ‖ξ x‖ ^ 4 :=
    sum_add_gridStep (fun x => ‖ξ x‖ ^ 4) μ
  calc ∑ x, ‖midAvg μ ξ x‖ ^ 4 ≤ ∑ x, (‖ξ x‖ ^ 4 + ‖ξ (x + gridStep μ)‖ ^ 4) / 2 :=
        sum_le_sum fun x _ => hpt x
    _ = ∑ x, ‖ξ x‖ ^ 4 := by rw [← sum_div, sum_add_distrib, hsh]; ring

/-- Pointwise control by the `L⁴` norm (cell mass `h⁴`): `h ‖a(x)‖ ≤ ‖a‖_{4,h}`. -/
theorem mul_norm_le_gridL4Norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h) (a : (ι → ZMod n) → F) (x : ι → ZMod n) :
    h * ‖a x‖ ≤ gridL4Norm h a := by
  rw [gridL4Norm, hι]
  have h1 : (h * ‖a x‖) ^ 4 ≤ h ^ 4 * ∑ y, ‖a y‖ ^ 4 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (single_le_sum (f := fun y => ‖a y‖ ^ 4)
      (fun y _ => by positivity) (mem_univ x)) (by positivity)
  calc h * ‖a x‖ = ((h * ‖a x‖) ^ 4) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 (by norm_num)

/-! ### The logarithmic Faddeev–Popov operator and its coercivity -/

section Operator

variable [FiniteDimensional ℝ E] [Nontrivial E]

/-- The flux `𝒦(h ad_{A_μ}) D^+_μ ξ + [A_μ, m_μ ξ]` of `eq:native-FP`. -/
def fpFlux (br : E →L[ℝ] E →L[ℝ] E) (h : ℝ) (A : ι → (ι → ZMod n) → E)
    (ξ : (ι → ZMod n) → E) (μ : ι) (x : ι → ZMod n) : E :=
  halfCoth (h • br (A μ x)) (gridFwd h μ ξ x) + br (A μ x) (midAvg μ ξ x)

/-- **The logarithmic discrete Faddeev–Popov operator** (`eq:native-FP`):
`M_A ξ = δ_h(𝒦(h ad_{A_μ}) D^+_μ ξ + [A_μ, m_μ ξ])_μ`. -/
def fpOp (br : E →L[ℝ] E →L[ℝ] E) (h : ℝ) (A : ι → (ι → ZMod n) → E)
    (ξ : (ι → ZMod n) → E) : (ι → ZMod n) → E :=
  periodicHodgeCodiff h gridStep (fpFlux br h A ξ)

/-- The `h`- and `n`-independent threshold `r_FP = 1/(64(‖[·,·]‖ + 1))`. -/
def rFP (br : E →L[ℝ] E →L[ℝ] E) : ℝ := 1 / (64 * (‖br‖ + 1))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem rFP_pos (br : E →L[ℝ] E →L[ℝ] E) : 0 < rFP br := by
  unfold rFP; have := br.opNorm_nonneg; positivity

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem norm_br_mul_rFP_le (br : E →L[ℝ] E →L[ℝ] E) : ‖br‖ * rFP br ≤ 1 / 64 := by
  unfold rFP
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [br.opNorm_nonneg]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Pointwise lower bound `⟪K v + b, v⟫ ≥ ‖v‖² - κ‖v‖² - ‖b‖‖v‖` when `‖K - I‖ ≤ κ`. -/
theorem inner_flux_ge (K : E →L[ℝ] E) (v b : E) {κ : ℝ} (hK : ‖K - 1‖ ≤ κ) :
    ‖v‖ ^ 2 - κ * ‖v‖ ^ 2 - ‖b‖ * ‖v‖ ≤ inner ℝ (K v + b) v := by
  have e : K v + b = v + ((K - 1) v + b) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]; abel
  rw [e, inner_add_left, inner_add_left, real_inner_self_eq_norm_sq]
  have h1 : -(‖(K - 1) v‖ * ‖v‖) ≤ inner ℝ ((K - 1) v) v :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have h2 : -(‖b‖ * ‖v‖) ≤ inner ℝ b v := neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have h3 : ‖(K - 1) v‖ ≤ κ * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  nlinarith [norm_nonneg v]

/-- **`eq:native-FP-coercivity`**: if `‖A_μ‖_{4,h} < r_FP` for every `μ`, then
`⟨M_A ξ, ξ⟩_{2,h} ≥ ½ ‖D^+ξ‖²_{2,h}` for every mean-zero `ξ` (uniformly in `n` and `h`). -/
theorem fp_coercive (hι : Fintype.card ι = 4) (br : E →L[ℝ] E →L[ℝ] E) {h : ℝ} (hh : 0 < h)
    (A : ι → (ι → ZMod n) → E) (hA : ∀ μ, gridL4Norm h (A μ) < rFP br)
    (ξ : (ι → ZMod n) → E) (hξ : ∑ x, ξ x = 0) :
    1 / 2 * dirSq h ξ ≤ gridInner h (fpOp br h A ξ) ξ := by
  set r := rFP br
  set ρ := ‖br‖ * r with hρ
  have hρ0 : 0 ≤ ρ := mul_nonneg br.opNorm_nonneg (rFP_pos br).le
  have hρ1 : ρ ≤ 1 / 64 := norm_br_mul_rFP_le br
  -- the chart and the bound on `𝒦 - I`
  have hZ : ∀ μ x, ‖h • br (A μ x)‖ ≤ ρ := by
    intro μ x
    calc ‖h • br (A μ x)‖ = h * ‖br (A μ x)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      _ ≤ h * (‖br‖ * ‖A μ x‖) := mul_le_mul_of_nonneg_left (br.le_opNorm _) hh.le
      _ = ‖br‖ * (h * ‖A μ x‖) := by ring
      _ ≤ ‖br‖ * r := mul_le_mul_of_nonneg_left
          ((mul_norm_le_gridL4Norm hι hh (A μ) x).trans (hA μ).le) br.opNorm_nonneg
  have hK : ∀ μ x, ‖halfCoth (h • br (A μ x)) - 1‖ ≤ 12 * ρ ^ 2 := by
    intro μ x
    refine (norm_halfCoth_sub_one_le _ ((hZ μ x).trans (by linarith))).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hZ μ x) 2) (by norm_num)
  -- pointwise lower bound
  have hpt : ∀ μ x, ‖gridFwd h μ ξ x‖ ^ 2 - 12 * ρ ^ 2 * ‖gridFwd h μ ξ x‖ ^ 2 -
      ‖br‖ * (‖A μ x‖ * ‖midAvg μ ξ x‖ * ‖gridFwd h μ ξ x‖) ≤
      inner ℝ (fpFlux br h A ξ μ x) (gridFwd h μ ξ x) := by
    intro μ x
    have hb : ‖br (A μ x) (midAvg μ ξ x)‖ ≤ ‖br‖ * ‖A μ x‖ * ‖midAvg μ ξ x‖ :=
      br.le_opNorm₂ _ _
    have := inner_flux_ge (halfCoth (h • br (A μ x))) (gridFwd h μ ξ x)
      (br (A μ x) (midAvg μ ξ x)) (hK μ x)
    have h4 : ‖br (A μ x) (midAvg μ ξ x)‖ * ‖gridFwd h μ ξ x‖ ≤
        ‖br‖ * (‖A μ x‖ * ‖midAvg μ ξ x‖ * ‖gridFwd h μ ξ x‖) := by
      calc _ ≤ ‖br‖ * ‖A μ x‖ * ‖midAvg μ ξ x‖ * ‖gridFwd h μ ξ x‖ :=
            mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ = _ := by ring
    simp only [fpFlux]
    linarith
  -- summation
  have hsum : gridInner h (fpOp br h A ξ) ξ =
      h ^ 4 * ∑ μ, ∑ x, inner ℝ (fpFlux br h A ξ μ x) (gridFwd h μ ξ x) := by
    rw [gridInner, fpOp, sum_inner_codiff, hι]
  have hdir : h ^ 4 * ∑ μ, ∑ x, ‖gridFwd h μ ξ x‖ ^ 2 = dirSq h ξ := by
    rw [dirSq, mul_sum]; simp only [periodicHodgeNormSq, hι]
  -- Hölder and Sobolev for the bracket term
  set S := √(dirSq h ξ) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSS : S ^ 2 = dirSq h ξ := Real.sq_sqrt (dirSq_nonneg hh.le ξ)
  have hT : ∑ μ, gridL2Norm h (gridFwd h μ ξ) ≤ 2 * S := by
    have := sum_le_two_mul_sqrt_sum_sq hι (fun μ => gridL2Norm h (gridFwd h μ ξ))
    rwa [← dirSq_eq_sum_sq hh.le] at this
  have hL4 : gridL4Norm h ξ ≤ 2 * (3 + 2 * √2) * S := by
    have := (grid_sobolev_poincare_meanZero_l2 hh hι ξ hξ).1
    rwa [← dirSq_eq_sum_sq hh.le] at this
  have hHol : ∀ μ, h ^ 4 * ∑ x, ‖A μ x‖ * ‖midAvg μ ξ x‖ * ‖gridFwd h μ ξ x‖ ≤
      r * gridL4Norm h ξ * gridL2Norm h (gridFwd h μ ξ) := by
    intro μ
    refine (gridHolder hι hh (A μ) (midAvg μ ξ) (gridFwd h μ ξ)).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul (hA μ).le (gridL4Norm_midAvg_le hh.le μ ξ)
      (by unfold gridL4Norm; positivity) (rFP_pos br).le) (gridL2Norm_nonneg _ _)
  have hbr : ‖br‖ * ∑ μ, h ^ 4 * ∑ x, ‖A μ x‖ * ‖midAvg μ ξ x‖ * ‖gridFwd h μ ξ x‖ ≤
      4 * (3 + 2 * √2) * ρ * dirSq h ξ := by
    have hL40 : 0 ≤ gridL4Norm h ξ := by unfold gridL4Norm; positivity
    calc ‖br‖ * ∑ μ, h ^ 4 * ∑ x, ‖A μ x‖ * ‖midAvg μ ξ x‖ * ‖gridFwd h μ ξ x‖
        ≤ ‖br‖ * ∑ μ, r * gridL4Norm h ξ * gridL2Norm h (gridFwd h μ ξ) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun μ _ => hHol μ) br.opNorm_nonneg
      _ = ρ * gridL4Norm h ξ * ∑ μ, gridL2Norm h (gridFwd h μ ξ) := by
          rw [hρ, ← mul_sum]; ring
      _ ≤ ρ * (2 * (3 + 2 * √2) * S) * (2 * S) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hL4 hρ0) hT
            (sum_nonneg fun μ _ => gridL2Norm_nonneg _ _) (by positivity)
      _ = 4 * (3 + 2 * √2) * ρ * dirSq h ξ := by rw [← hSS]; ring
  -- assemble
  have hlow : h ^ 4 * ∑ μ, ∑ x, (‖gridFwd h μ ξ x‖ ^ 2 - 12 * ρ ^ 2 * ‖gridFwd h μ ξ x‖ ^ 2 -
      ‖br‖ * (‖A μ x‖ * ‖midAvg μ ξ x‖ * ‖gridFwd h μ ξ x‖)) ≤
      gridInner h (fpOp br h A ξ) ξ := by
    rw [hsum]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun μ _ => sum_le_sum fun x _ => hpt μ x)
      (by positivity)
  have hexp : h ^ 4 * ∑ μ, ∑ x, (‖gridFwd h μ ξ x‖ ^ 2 - 12 * ρ ^ 2 * ‖gridFwd h μ ξ x‖ ^ 2 -
      ‖br‖ * (‖A μ x‖ * ‖midAvg μ ξ x‖ * ‖gridFwd h μ ξ x‖)) =
      (1 - 12 * ρ ^ 2) * dirSq h ξ -
        ‖br‖ * ∑ μ, h ^ 4 * ∑ x, ‖A μ x‖ * ‖midAvg μ ξ x‖ * ‖gridFwd h μ ξ x‖ := by
    rw [← hdir]
    simp only [sum_sub_distrib, ← mul_sum, mul_sub]
    ring
  have hs2 : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hD0 := dirSq_nonneg hh.le ξ
  rw [hexp] at hlow
  have hfin : 1 / 2 * dirSq h ξ ≤ (1 - 12 * ρ ^ 2) * dirSq h ξ -
      4 * (3 + 2 * √2) * ρ * dirSq h ξ := by
    have hc : 12 * ρ ^ 2 + 4 * (3 + 2 * √2) * ρ ≤ 1 / 2 := by nlinarith
    nlinarith
  linarith

end Operator

/-! ### Linearity, the mean-zero space and invertibility -/

section Inverse

variable [FiniteDimensional ℝ E] [Nontrivial E]

omit [Fintype ι] [NeZero n] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem gridFwd_add (h : ℝ) (μ : ι) (ξ η : (ι → ZMod n) → E) :
    gridFwd h μ (ξ + η) = gridFwd h μ ξ + gridFwd h μ η := by
  funext x; simp only [gridFwd, Pi.add_apply, ← smul_add]; congr 1; abel

omit [Fintype ι] [NeZero n] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem gridFwd_smul (h c : ℝ) (μ : ι) (ξ : (ι → ZMod n) → E) :
    gridFwd h μ (c • ξ) = c • gridFwd h μ ξ := by
  funext x; simp only [gridFwd, Pi.smul_apply, ← smul_sub, smul_comm c]

omit [Fintype ι] [NeZero n] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem midAvg_add (μ : ι) (ξ η : (ι → ZMod n) → E) :
    midAvg μ (ξ + η) = midAvg μ ξ + midAvg μ η := by
  funext x; simp only [midAvg, Pi.add_apply, ← smul_add]; congr 1; abel

omit [Fintype ι] [NeZero n] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem midAvg_smul (c : ℝ) (μ : ι) (ξ : (ι → ZMod n) → E) :
    midAvg μ (c • ξ) = c • midAvg μ ξ := by
  funext x; simp only [midAvg, Pi.smul_apply, ← smul_add, smul_comm c]

omit [Fintype ι] [NeZero n] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem fpFlux_add (br : E →L[ℝ] E →L[ℝ] E) (h : ℝ) (A : ι → (ι → ZMod n) → E)
    (ξ η : (ι → ZMod n) → E) (μ : ι) (x : ι → ZMod n) :
    fpFlux br h A (ξ + η) μ x = fpFlux br h A ξ μ x + fpFlux br h A η μ x := by
  simp only [fpFlux, gridFwd_add, midAvg_add, Pi.add_apply, map_add]; abel

omit [Fintype ι] [NeZero n] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem fpFlux_smul (br : E →L[ℝ] E →L[ℝ] E) (h c : ℝ) (A : ι → (ι → ZMod n) → E)
    (ξ : (ι → ZMod n) → E) (μ : ι) (x : ι → ZMod n) :
    fpFlux br h A (c • ξ) μ x = c • fpFlux br h A ξ μ x := by
  simp only [fpFlux, gridFwd_smul, midAvg_smul, Pi.smul_apply, map_smul, smul_add]

/-- `M_A` as a linear map. -/
def fpLin (br : E →L[ℝ] E →L[ℝ] E) (h : ℝ) (A : ι → (ι → ZMod n) → E) :
    ((ι → ZMod n) → E) →ₗ[ℝ] ((ι → ZMod n) → E) where
  toFun := fpOp br h A
  map_add' ξ η := by
    funext x
    simp only [fpOp, periodicHodgeCodiff, periodicHodgeBwd, fpFlux_add, Pi.add_apply,
      ← sum_add_distrib, ← neg_add, ← smul_add]
    congr 1; refine sum_congr rfl fun μ _ => ?_; congr 1; abel
  map_smul' c ξ := by
    funext x
    simp only [fpOp, periodicHodgeCodiff, periodicHodgeBwd, fpFlux_smul, Pi.smul_apply,
      RingHom.id_apply, smul_neg, smul_sum, ← smul_sub, smul_comm c]

omit [NeZero n] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem fpLin_apply (br : E →L[ℝ] E →L[ℝ] E) (h : ℝ) (A : ι → (ι → ZMod n) → E)
    (ξ : (ι → ZMod n) → E) : fpLin br h A ξ = fpOp br h A ξ := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The range of a discrete divergence has zero mean. -/
theorem sum_codiff (h : ℝ) (W : ι → (ι → ZMod n) → E) :
    ∑ x, periodicHodgeCodiff h gridStep W x = 0 := by
  simp only [periodicHodgeCodiff, periodicHodgeBwd, sum_neg_distrib]
  rw [sum_comm, neg_eq_zero]
  refine sum_eq_zero fun μ _ => ?_
  rw [← smul_sum, sum_sub_distrib, sub_eq_zero.2, smul_zero]
  exact (Fintype.sum_equiv (Equiv.subRight (gridStep μ)) _ _ (fun _ => rfl)).symm

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem sum_fpOp (br : E →L[ℝ] E →L[ℝ] E) (h : ℝ) (A : ι → (ι → ZMod n) → E)
    (ξ : (ι → ZMod n) → E) : ∑ x, fpOp br h A ξ x = 0 := sum_codiff h _

/-- Coercivity implies injectivity on `𝒵_h`. -/
theorem fp_injective (hι : Fintype.card ι = 4) (br : E →L[ℝ] E →L[ℝ] E) {h : ℝ} (hh : 0 < h)
    (A : ι → (ι → ZMod n) → E) (hA : ∀ μ, gridL4Norm h (A μ) < rFP br)
    (ξ : (ι → ZMod n) → E) (hξ : ∑ x, ξ x = 0) (h0 : fpOp br h A ξ = 0) : ξ = 0 := by
  have hc := fp_coercive hι br hh A hA ξ hξ
  rw [h0] at hc
  simp only [gridInner, Pi.zero_apply, inner_zero_left, sum_const_zero, mul_zero] at hc
  exact eq_zero_of_dirSq_eq_zero hh ξ hξ (le_antisymm (by linarith) (dirSq_nonneg hh.le ξ))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The mean-zero site space `𝒵_h`. -/
def meanZero : Submodule ℝ ((ι → ZMod n) → E) where
  carrier := {ξ | ∑ x, ξ x = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Pi.add_apply, sum_add_distrib] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq, Pi.smul_apply, ← smul_sum] at *
    rw [ha, smul_zero]

/-- **`M_A : 𝒵_h → 𝒵_h` is invertible** for `‖A_μ‖_{4,h} < r_FP`: every mean-zero `f` is
`M_A ξ` for exactly one mean-zero `ξ`. -/
theorem fp_bijective (hι : Fintype.card ι = 4) (br : E →L[ℝ] E →L[ℝ] E) {h : ℝ} (hh : 0 < h)
    (A : ι → (ι → ZMod n) → E) (hA : ∀ μ, gridL4Norm h (A μ) < rFP br)
    (f : (ι → ZMod n) → E) (hf : ∑ x, f x = 0) :
    ∃! ξ : (ι → ZMod n) → E, ∑ x, ξ x = 0 ∧ fpOp br h A ξ = f := by
  let T : meanZero (ι := ι) (n := n) (E := E) →ₗ[ℝ] meanZero (ι := ι) (n := n) (E := E) :=
    (fpLin br h A).restrict (p := meanZero) (q := meanZero) (fun ξ _ => sum_fpOp br h A ξ)
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ξ hξ
    have h1 : fpOp br h A ξ = 0 := by
      have := congrArg Subtype.val hξ
      exact this
    exact Subtype.ext (fp_injective hι br hh A hA ξ ξ.2 h1)
  obtain ⟨ξ, hξ⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨f, hf⟩
  have hξ' : fpOp br h A ξ = f := by
    have := congrArg Subtype.val hξ
    exact this
  refine ⟨ξ, ⟨ξ.2, hξ'⟩, fun η hη => ?_⟩
  have hd : fpOp br h A (η - ξ) = 0 := by
    rw [← fpLin_apply, map_sub, fpLin_apply, fpLin_apply, hη.2, hξ', sub_self]
  have hs : ∑ x, (η - ξ) x = 0 := by
    have h2 : ∑ x, (ξ : (ι → ZMod n) → E) x = 0 := ξ.2
    simp only [Pi.sub_apply, sum_sub_distrib, hη.1, h2, sub_zero]
  exact sub_eq_zero.1 (fp_injective hι br hh A hA (η - ξ) hs hd)

/-- **`eq:native-FP-dual-inverse`** with an arbitrary admissible dual bound: if
`|⟨M_A ξ, ζ⟩_{2,h}| ≤ B ‖D^+ζ‖_{2,h}` for all mean-zero `ζ`, then `‖D^+ξ‖_{2,h} ≤ 2B`. -/
theorem fp_dual_inverse (hι : Fintype.card ι = 4) (br : E →L[ℝ] E →L[ℝ] E) {h : ℝ} (hh : 0 < h)
    (A : ι → (ι → ZMod n) → E) (hA : ∀ μ, gridL4Norm h (A μ) < rFP br)
    (ξ : (ι → ZMod n) → E) (hξ : ∑ x, ξ x = 0) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ ζ : (ι → ZMod n) → E, ∑ x, ζ x = 0 →
      |gridInner h (fpOp br h A ξ) ζ| ≤ B * √(dirSq h ζ)) :
    √(dirSq h ξ) ≤ 2 * B := by
  have hc := fp_coercive hι br hh A hA ξ hξ
  have hb := (le_abs_self _).trans (hB ξ hξ)
  set S := √(dirSq h ξ)
  have hS : S ^ 2 = dirSq h ξ := Real.sq_sqrt (dirSq_nonneg hh.le ξ)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  rw [← hS] at hc
  nlinarith

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Weighted Cauchy–Schwarz: `h^d Σ_x ‖f‖‖g‖ ≤ ‖f‖_{2,h}‖g‖_{2,h}`. -/
theorem sum_norm_mul_le_gridL2 {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {h : ℝ} (hh : 0 < h)
    (f : (ι → ZMod n) → F) (g : (ι → ZMod n) → G) :
    h ^ Fintype.card ι * ∑ x, ‖f x‖ * ‖g x‖ ≤ gridL2Norm h f * gridL2Norm h g := by
  rw [gridL2Norm_eq hh, gridL2Norm_eq hh]
  have := Real.sum_mul_le_sqrt_mul_sqrt univ (fun x => ‖f x‖) (fun x => ‖g x‖)
  have hw : h ^ Fintype.card ι = √(h ^ Fintype.card ι) * √(h ^ Fintype.card ι) :=
    (Real.mul_self_sqrt (by positivity)).symm
  calc h ^ Fintype.card ι * ∑ x, ‖f x‖ * ‖g x‖
      = √(h ^ Fintype.card ι) * √(h ^ Fintype.card ι) * ∑ x, ‖f x‖ * ‖g x‖ := by rw [← hw]
    _ ≤ √(h ^ Fintype.card ι) * √(h ^ Fintype.card ι) *
          (√(∑ x, ‖f x‖ ^ 2) * √(∑ x, ‖g x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- `|⟨δ_h R, ζ⟩_{2,h}| ≤ ‖R‖_{2,h} ‖D^+ζ‖_{2,h}`, i.e. `‖δ_h R‖_{\dot H^{-1}_h} ≤ ‖R‖_{2,h}`. -/
theorem abs_gridInner_codiff_le {h : ℝ} (hh : 0 < h) (R : ι → (ι → ZMod n) → E)
    (ζ : (ι → ZMod n) → E) :
    |gridInner h (periodicHodgeCodiff h gridStep R) ζ| ≤
      √(∑ μ, periodicHodgeNormSq ι h (R μ)) * √(dirSq h ζ) := by
  rw [gridInner, sum_inner_codiff, mul_sum]
  have h1 : ∀ μ, |h ^ Fintype.card ι * ∑ x, inner ℝ (R μ x) (gridFwd h μ ζ x)| ≤
      gridL2Norm h (R μ) * gridL2Norm h (gridFwd h μ ζ) := by
    intro μ
    rw [abs_mul, abs_of_nonneg (by positivity)]
    refine (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans
      (sum_le_sum fun x _ => abs_real_inner_le_norm _ _)) (by positivity)).trans ?_
    exact sum_norm_mul_le_gridL2 hh _ _
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun μ _ => h1 μ).trans ?_)
  have := Real.sum_mul_le_sqrt_mul_sqrt univ (fun μ => gridL2Norm h (R μ))
    (fun μ => gridL2Norm h (gridFwd h μ ζ))
  simp only [gridL2Norm_sq hh.le] at this
  exact this

/-- **`eq:native-FP-divergence-inverse`**: for any link array `R`, the mean-zero solution
`ξ = M_A⁻¹ δ_h R` satisfies
`‖ξ‖_{2,h} + ‖ξ‖_{4,h} + ‖D^+ξ‖_{2,h} ≤ (2 + 2√2 L + 4(3+2√2)) ‖R‖_{2,h}`, `L = n h`. -/
theorem fp_divergence_inverse (hι : Fintype.card ι = 4) (br : E →L[ℝ] E →L[ℝ] E) {h : ℝ}
    (hh : 0 < h) (A : ι → (ι → ZMod n) → E) (hA : ∀ μ, gridL4Norm h (A μ) < rFP br)
    (R : ι → (ι → ZMod n) → E) (ξ : (ι → ZMod n) → E) (hξ : ∑ x, ξ x = 0)
    (hM : fpOp br h A ξ = periodicHodgeCodiff h gridStep R) :
    gridL2Norm h ξ + gridL4Norm h ξ + √(dirSq h ξ) ≤
      (2 + 2 * √2 * (n * h) + 4 * (3 + 2 * √2)) * √(∑ μ, periodicHodgeNormSq ι h (R μ)) := by
  set B := √(∑ μ, periodicHodgeNormSq ι h (R μ))
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hD := fp_dual_inverse hι br hh A hA ξ hξ hB0 (fun ζ _ => by
    rw [hM]; exact abs_gridInner_codiff_le hh R ζ)
  obtain ⟨h4, h2⟩ := grid_sobolev_poincare_meanZero_l2 hh hι ξ hξ
  rw [← dirSq_eq_sum_sq hh.le] at h4 h2
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hS0 : 0 ≤ √(dirSq h ξ) := Real.sqrt_nonneg _
  have e2 : gridL2Norm h ξ ≤ 2 * √2 * (n * h) * B := by
    calc gridL2Norm h ξ ≤ √2 * (n * h) * √(dirSq h ξ) := h2
      _ ≤ √2 * (n * h) * (2 * B) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = _ := by ring
  have e4 : gridL4Norm h ξ ≤ 4 * (3 + 2 * √2) * B := by
    calc gridL4Norm h ξ ≤ 2 * (3 + 2 * √2) * √(dirSq h ξ) := h4
      _ ≤ 2 * (3 + 2 * √2) * (2 * B) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = _ := by ring
  nlinarith

end Inverse

/-! ### The dual norm `‖·‖_{\dot H^{-1}_h}` -/

section DualNorm

theorem normSq_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h c : ℝ) (w : (ι → ZMod n) → F) :
    periodicHodgeNormSq ι h (c • w) = c ^ 2 * periodicHodgeNormSq ι h w := by
  simp only [periodicHodgeNormSq, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    ← mul_sum]
  ring

theorem dirSq_smul (h c : ℝ) (ζ : (ι → ZMod n) → E) : dirSq h (c • ζ) = c ^ 2 * dirSq h ζ := by
  simp only [dirSq, gridFwd_smul, normSq_smul, mul_sum]

theorem gridInner_smul_right (h c : ℝ) (f ζ : (ι → ZMod n) → E) :
    gridInner h f (c • ζ) = c * gridInner h f ζ := by
  simp only [gridInner, Pi.smul_apply, inner_smul_right, ← mul_sum]; ring

theorem abs_gridInner_le {h : ℝ} (hh : 0 < h) (f ζ : (ι → ZMod n) → E) :
    |gridInner h f ζ| ≤ gridL2Norm h f * gridL2Norm h ζ := by
  rw [gridInner, abs_mul, abs_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun x _ => abs_real_inner_le_norm _ _)) (by positivity)).trans ?_
  exact sum_norm_mul_le_gridL2 hh _ _

/-- Poincaré with the `ℓ²` Dirichlet energy, any dimension. -/
theorem gridL2Norm_le_dirSq {h : ℝ} (hh : 0 < h) (ζ : (ι → ZMod n) → E) (hζ : ∑ x, ζ x = 0) :
    gridL2Norm h ζ ≤ n * h / √2 * Fintype.card ι * √(dirSq h ζ) := by
  refine (grid_poincare hh ζ hζ).trans ?_
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : ∀ μ, gridL2Norm h (gridFwd h μ ζ) ≤ √(dirSq h ζ) := fun μ =>
    Real.sqrt_le_sqrt (single_le_sum (f := fun μ => periodicHodgeNormSq ι h (gridFwd h μ ζ))
      (fun μ _ => normSq_nonneg hh.le _) (mem_univ μ))
  calc n * h / √2 * ∑ μ, gridL2Norm h (gridFwd h μ ζ)
      ≤ n * h / √2 * ∑ _μ : ι, √(dirSq h ζ) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun μ _ => h1 μ) (by positivity)
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring

/-- The dual norm `‖f‖_{\dot H^{-1}_h} = sup {|⟨f, ζ⟩_{2,h}| : ζ ∈ 𝒵_h, ‖D^+ζ‖_{2,h} = 1}`. -/
def dualNorm (h : ℝ) (f : (ι → ZMod n) → E) : ℝ :=
  sSup ((fun ζ => |gridInner h f ζ|) '' {ζ | ∑ x, ζ x = 0 ∧ dirSq h ζ = 1})

theorem dualNorm_nonneg (h : ℝ) (f : (ι → ZMod n) → E) : 0 ≤ dualNorm h f :=
  Real.sSup_nonneg fun _ ⟨_, _, hy⟩ => hy ▸ abs_nonneg _

/-- `|⟨f, ζ⟩_{2,h}| ≤ ‖f‖_{\dot H^{-1}_h} ‖D^+ζ‖_{2,h}` on `𝒵_h`. -/
theorem abs_gridInner_le_dualNorm {h : ℝ} (hh : 0 < h) (f ζ : (ι → ZMod n) → E)
    (hζ : ∑ x, ζ x = 0) : |gridInner h f ζ| ≤ dualNorm h f * √(dirSq h ζ) := by
  have hbdd : BddAbove ((fun ζ => |gridInner h f ζ|) '' {ζ | ∑ x, ζ x = 0 ∧ dirSq h ζ = 1}) := by
    refine ⟨gridL2Norm h f * (n * h / √2 * Fintype.card ι), ?_⟩
    rintro _ ⟨η, ⟨hη, hη1⟩, rfl⟩
    refine (abs_gridInner_le hh f η).trans (mul_le_mul_of_nonneg_left ?_ (gridL2Norm_nonneg _ _))
    have := gridL2Norm_le_dirSq hh η hη
    rwa [hη1, Real.sqrt_one, mul_one] at this
  set S := √(dirSq h ζ)
  rcases (Real.sqrt_nonneg (dirSq h ζ)).eq_or_lt with h0 | hpos
  · have hd : dirSq h ζ = 0 := by
      have := Real.sqrt_eq_zero (dirSq_nonneg hh.le ζ) |>.1 h0.symm; exact this
    have hz := eq_zero_of_dirSq_eq_zero hh ζ hζ hd
    subst hz
    simp only [gridInner, Pi.zero_apply, inner_zero_right, sum_const_zero, mul_zero, abs_zero]
    exact mul_nonneg (dualNorm_nonneg _ _) (Real.sqrt_nonneg _)
  · have hS2 : S ^ 2 = dirSq h ζ := Real.sq_sqrt (dirSq_nonneg hh.le ζ)
    have hmem : |gridInner h f (S⁻¹ • ζ)| ≤ dualNorm h f := by
      refine le_csSup hbdd ⟨S⁻¹ • ζ, ⟨?_, ?_⟩, rfl⟩
      · simp only [Pi.smul_apply, ← smul_sum, hζ, smul_zero]
      · rw [dirSq_smul, inv_pow, ← hS2, inv_mul_cancel₀ (pow_ne_zero 2 hpos.ne')]
    rw [gridInner_smul_right, abs_mul, abs_of_pos (inv_pos.2 hpos)] at hmem
    rw [inv_mul_le_iff₀ hpos] at hmem
    linarith

end DualNorm

/-- **`eq:native-FP-dual-inverse`**: `‖D^+ M_A⁻¹ f‖_{2,h} ≤ 2 ‖f‖_{\dot H^{-1}_h}`, i.e. for every
mean-zero `ξ`, `‖D^+ ξ‖_{2,h} ≤ 2 ‖M_A ξ‖_{\dot H^{-1}_h}`. -/
theorem fp_dual_inverse_sSup [FiniteDimensional ℝ E] [Nontrivial E] (hι : Fintype.card ι = 4)
    (br : E →L[ℝ] E →L[ℝ] E) {h : ℝ} (hh : 0 < h)
    (A : ι → (ι → ZMod n) → E) (hA : ∀ μ, gridL4Norm h (A μ) < rFP br)
    (ξ : (ι → ZMod n) → E) (hξ : ∑ x, ξ x = 0) :
    √(dirSq h ξ) ≤ 2 * dualNorm h (fpOp br h A ξ) :=
  fp_dual_inverse hι br hh A hA ξ hξ (dualNorm_nonneg _ _)
    (fun ζ hζ => abs_gridInner_le_dualNorm hh _ ζ hζ)

/-! ### Smooth dependence of the inverse on `A` -/

section Smooth

variable [FiniteDimensional ℝ E] [Nontrivial E]

/-- The constant field with the mean value of `ξ`. -/
def avgOp (ξ : (ι → ZMod n) → E) : (ι → ZMod n) → E :=
  fun _ => ((Fintype.card (ι → ZMod n) : ℝ)⁻¹) • ∑ y, ξ y

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem sum_avgOp (ξ : (ι → ZMod n) → E) : ∑ x, avgOp ξ x = ∑ y, ξ y := by
  have hN : (Fintype.card (ι → ZMod n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avgOp, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ hN, one_smul]

/-- `ξ ↦ ξ̄` as a linear map. -/
def avgLin : ((ι → ZMod n) → E) →ₗ[ℝ] ((ι → ZMod n) → E) where
  toFun := avgOp
  map_add' ξ η := by funext x; simp only [avgOp, Pi.add_apply, sum_add_distrib, smul_add]
  map_smul' c ξ := by
    funext x; simp only [avgOp, Pi.smul_apply, RingHom.id_apply, ← smul_sum, smul_comm c]

/-- The extension `N_A ξ = M_A(ξ - ξ̄) + ξ̄` of `M_A|_{𝒵_h}` to all site fields; on `𝒵_h` its
inverse is `M_A⁻¹`. -/
def nLin (br : E →L[ℝ] E →L[ℝ] E) (h : ℝ) (A : ι → (ι → ZMod n) → E) :
    ((ι → ZMod n) → E) →ₗ[ℝ] ((ι → ZMod n) → E) :=
  fpLin br h A ∘ₗ (LinearMap.id - avgLin) + avgLin

/-- `N_A` as a continuous linear operator. -/
def nCLM (br : E →L[ℝ] E →L[ℝ] E) (h : ℝ) (A : ι → (ι → ZMod n) → E) :
    ((ι → ZMod n) → E) →L[ℝ] ((ι → ZMod n) → E) :=
  LinearMap.toContinuousLinearMap (nLin br h A)

omit [Nontrivial E] in
theorem nCLM_apply (br : E →L[ℝ] E →L[ℝ] E) (h : ℝ) (A : ι → (ι → ZMod n) → E)
    (ξ : (ι → ZMod n) → E) : nCLM br h A ξ = fpOp br h A (ξ - avgOp ξ) + avgOp ξ := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem avgOp_eq_zero (ξ : (ι → ZMod n) → E) (hξ : ∑ x, ξ x = 0) : avgOp ξ = 0 := by
  funext x; simp [avgOp, hξ]

/-- If `N_A ξ = f` with `f` mean-zero, then `ξ` is mean-zero and `M_A ξ = f`. -/
theorem fp_of_nCLM (br : E →L[ℝ] E →L[ℝ] E) (h : ℝ) (A : ι → (ι → ZMod n) → E)
    (ξ f : (ι → ZMod n) → E) (hf : ∑ x, f x = 0) (hN : nCLM br h A ξ = f) :
    ∑ x, ξ x = 0 ∧ fpOp br h A ξ = f := by
  rw [nCLM_apply] at hN
  have hs := congrArg (fun g : (ι → ZMod n) → E => ∑ x, g x) hN
  simp only [Pi.add_apply, sum_add_distrib, sum_fpOp, zero_add, sum_avgOp, hf] at hs
  refine ⟨hs, ?_⟩
  rw [avgOp_eq_zero ξ hs, sub_zero, add_zero] at hN
  exact hN

theorem nCLM_isUnit (hι : Fintype.card ι = 4) (br : E →L[ℝ] E →L[ℝ] E) {h : ℝ} (hh : 0 < h)
    (A : ι → (ι → ZMod n) → E) (hA : ∀ μ, gridL4Norm h (A μ) < rFP br) :
    IsUnit (nCLM br h A) := by
  have hinj : Function.Injective (nLin br h A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ξ hξ
    have h1 := fp_of_nCLM br h A ξ 0 (by simp) hξ
    exact fp_injective hι br hh A hA ξ h1.1 h1.2
  let e := (LinearEquiv.ofInjectiveEndo (nLin br h A) hinj).toContinuousLinearEquiv
  refine ⟨⟨nCLM br h A, (e.symm : ((ι → ZMod n) → E) →L[ℝ] ((ι → ZMod n) → E)), ?_, ?_⟩, rfl⟩
  · ext1 x; exact e.apply_symm_apply x
  · ext1 x; exact e.symm_apply_apply x

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The chart condition `‖h ad_{A_μ(x)}‖ < 1/4`, implied by `‖A_μ‖_{4,h} < r_FP`. -/
theorem chart_of_small (hι : Fintype.card ι = 4) (br : E →L[ℝ] E →L[ℝ] E) {h : ℝ} (hh : 0 < h)
    (A : ι → (ι → ZMod n) → E) (hA : ∀ μ, gridL4Norm h (A μ) < rFP br) (μ : ι)
    (x : ι → ZMod n) : ‖h • br (A μ x)‖ < 1 / 4 := by
  calc ‖h • br (A μ x)‖ = h * ‖br (A μ x)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    _ ≤ h * (‖br‖ * ‖A μ x‖) := mul_le_mul_of_nonneg_left (br.le_opNorm _) hh.le
    _ = ‖br‖ * (h * ‖A μ x‖) := by ring
    _ ≤ ‖br‖ * rFP br := mul_le_mul_of_nonneg_left
        ((mul_norm_le_gridL4Norm hι hh (A μ) x).trans (hA μ).le) br.opNorm_nonneg
    _ ≤ 1 / 64 := norm_br_mul_rFP_le br
    _ < 1 / 4 := by norm_num

theorem contDiffAt_fpFlux {k : WithTop ℕ∞} (br : E →L[ℝ] E →L[ℝ] E) (h : ℝ)
    (η : (ι → ZMod n) → E) (μ : ι) (y : ι → ZMod n) (A : ι → (ι → ZMod n) → E)
    (hZ : ‖h • br (A μ y)‖ < 1 / 4) :
    ContDiffAt ℝ k (fun A : ι → (ι → ZMod n) → E => fpFlux br h A η μ y) A := by
  have hev : ContDiff ℝ k (fun A : ι → (ι → ZMod n) → E => A μ y) := by fun_prop
  have hZd : ContDiff ℝ k (fun A : ι → (ι → ZMod n) → E => h • br (A μ y)) :=
    (br.contDiff.comp hev).const_smul h
  have hK : ContDiffAt ℝ k (halfCoth (𝔸 := E →L[ℝ] E)) (h • br (A μ y)) :=
    contDiffAt_halfCoth _ hZ
  have h1 : ContDiffAt ℝ k (fun A : ι → (ι → ZMod n) → E =>
      halfCoth (h • br (A μ y)) (gridFwd h μ η y)) A :=
    (hK.comp A hZd.contDiffAt).clm_apply contDiffAt_const
  have h2 : ContDiff ℝ k (fun A : ι → (ι → ZMod n) → E => br (A μ y) (midAvg μ η y)) :=
    ((ContinuousLinearMap.apply ℝ E (midAvg μ η y)).comp br).contDiff.comp hev
  exact h1.add h2.contDiffAt

/-- **Smooth dependence of the inverse** (`lem:native-FP-inverse`, last assertion): on the set
`{A : ‖A_μ‖_{4,h} < r_FP ∀ μ}` the operator `N_A` is invertible, `A ↦ N_A⁻¹` is `C^k` for every
`k` (in particular `C^∞`), and for mean-zero `f`, `ξ = N_A⁻¹ f` is the mean-zero solution of
`M_A ξ = f`, i.e. `N_A⁻¹|_{𝒵_h} = M_A⁻¹`. -/
theorem fp_inverse_contDiffOn {k : WithTop ℕ∞} (hι : Fintype.card ι = 4)
    (br : E →L[ℝ] E →L[ℝ] E) {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ k (fun A => Ring.inverse (nCLM br h A))
        {A : ι → (ι → ZMod n) → E | ∀ μ, gridL4Norm h (A μ) < rFP br} ∧
      ∀ A : ι → (ι → ZMod n) → E, (∀ μ, gridL4Norm h (A μ) < rFP br) →
        ∀ f : (ι → ZMod n) → E, ∑ x, f x = 0 →
          ∑ x, Ring.inverse (nCLM br h A) f x = 0 ∧
            fpOp br h A (Ring.inverse (nCLM br h A) f) = f := by
  set U := {A : ι → (ι → ZMod n) → E | ∀ μ, gridL4Norm h (A μ) < rFP br}
  have hN : ContDiffOn ℝ k (nCLM br h) U := by
    rw [contDiffOn_clm_apply]
    intro ξ
    rw [contDiffOn_pi]
    intro x A hA
    refine ContDiffAt.contDiffWithinAt ?_
    simp only [nCLM_apply, Pi.add_apply, fpOp, periodicHodgeCodiff, periodicHodgeBwd]
    refine ContDiffAt.add ?_ contDiffAt_const
    refine ContDiffAt.neg (ContDiffAt.sum fun μ _ => ContDiffAt.const_smul _ (ContDiffAt.sub ?_ ?_))
    · exact contDiffAt_fpFlux br h _ μ x A (chart_of_small hι br hh A hA μ x)
    · exact contDiffAt_fpFlux br h _ μ _ A (chart_of_small hι br hh A hA μ _)
  refine ⟨fun A hA => ?_, fun A hA f hf => ?_⟩
  · obtain ⟨u, hu⟩ := nCLM_isUnit hι br hh A hA
    have hinv := contDiffAt_ringInverse ℝ
      (R := ((ι → ZMod n) → E) →L[ℝ] ((ι → ZMod n) → E)) (n := k) u
    rw [hu] at hinv
    exact hinv.comp_contDiffWithinAt A (hN A hA)
  · have hu := nCLM_isUnit hι br hh A hA
    have hsol : nCLM br h A (Ring.inverse (nCLM br h A) f) = f := by
      have := congrArg (fun T : ((ι → ZMod n) → E) →L[ℝ] ((ι → ZMod n) → E) => T f)
        (Ring.mul_inverse_cancel _ hu)
      simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using this
    exact fp_of_nCLM br h A _ f hf hsol

end Smooth


/-! ### Non-vacuity -/

/-- The hypotheses are satisfiable: for the zero connection (any bracket, e.g. the abelian one on
`ℝ`), `‖A_μ‖_{4,h} = 0 < r_FP`, and `M_0 = δ_h D^+` is invertible on `𝒵_h`. -/
example (n : ℕ) [NeZero n] {h : ℝ} (hh : 0 < h) (f : (Fin 4 → ZMod n) → ℝ) (hf : ∑ x, f x = 0) :
    ∃! ξ : (Fin 4 → ZMod n) → ℝ, ∑ x, ξ x = 0 ∧ fpOp (0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) h 0 ξ = f := by
  refine fp_bijective (by simp) 0 hh 0 (fun μ => ?_) f hf
  have : gridL4Norm h ((0 : Fin 4 → (Fin 4 → ZMod n) → ℝ) μ) = 0 := by
    simp [gridL4Norm]
  rw [this]; exact rFP_pos _

end

end RenewalGeometry.FaddeevPopov
