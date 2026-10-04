/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.NormedAlgebraLogBCH
import RenewalGeometry.Algebra.SeriesLogChart

/-!
# A Cauchy estimate for the derivative of the BCH remainder of an ordered exponential product

Infrastructure for `eq:native-YM-envelope` (second line) and `eq:native-YM-variation`
("the same analytic expansion holds after one physical variation") of the Einstein–SM
action-closure manuscript.

Let `𝔸` be a complete normed **complex** algebra with `‖1‖ = 1` (e.g. complex matrices with an
operator norm; the compact gauge algebras `𝔲(N)`, `𝔰𝔲(3) ⊕ 𝔰𝔲(2) ⊕ 𝔲(1)` are real subspaces of
such algebras).  For a list `L = [x₁, …, x_m]` put `s = Σ ‖xᵢ‖` and let

`bchRem L = log(e^{x₁} ⋯ e^{x_m}) - (Σ xᵢ + ½ Σ_{i<j}[xᵢ, xⱼ])`

be the cubic remainder of the second-order BCH expansion (`LogBCH.norm_log_expProd_sub_bch_le`:
`‖bchRem L‖ ≤ 6 s³` for `s ≤ 1/4`), with the principal (Mercator) logarithm.

* `differentiableOn_bchRem_lineList`: along a complex line `z ↦ L + z W` (`lineList`) the remainder
  is complex-differentiable wherever `Σ ‖xᵢ + z wᵢ‖ ≤ 1/4` (the logarithm series is a locally
  uniform limit of polynomials in the entire functions `e^{xᵢ + z wᵢ}`).
* `norm_deriv_bchRem_le` (**the derivative bound**): if `s ≤ 1/32`, the derivative of
  `z ↦ bchRem (L + z W)` at `0` exists and is bounded by `48 s² Σ ‖wᵢ‖` (Cauchy's estimate on
  the circle `|z| = s/Σ‖wᵢ‖`, where the remainder is `≤ 6 (2s)³`).
* `hasDerivAt_real_bchRem`: the same derivative along the real direction `t ↦ L + t W`.
-/

open NormedSpace Filter Topology Metric

namespace RenewalGeometry.PlaquetteLogDerivative

open LogBCH

noncomputable section

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- The complex line `z ↦ (xᵢ + z wᵢ)ᵢ` through the list `L` in the direction `W`. -/
def lineList (L W : List 𝔸) (z : ℂ) : List 𝔸 := List.zipWith (fun a b => a + z • b) L W

/-- The cubic remainder of the second-order BCH expansion of `log(e^{x₁} ⋯ e^{x_m})`. -/
def bchRem (L : List 𝔸) : 𝔸 := logOnePlus (expProd L - 1) - (L.sum + commTerm L)

theorem normSum_lineList_le (L W : List 𝔸) (z : ℂ) :
    normSum (lineList L W z) ≤ normSum L + ‖z‖ * normSum W := by
  induction L generalizing W with
  | nil => simp [lineList, mul_nonneg (norm_nonneg z) (normSum_nonneg W)]
  | cons a L ih =>
      cases W with
      | nil =>
          simp only [lineList, List.zipWith_nil_right, normSum_nil, normSum_cons, mul_zero,
            add_zero]
          exact add_nonneg (norm_nonneg _) (normSum_nonneg _)
      | cons b W =>
          have h := ih W
          simp only [lineList] at h ⊢
          simp only [List.zipWith_cons_cons, normSum_cons]
          have hb : ‖a + z • b‖ ≤ ‖a‖ + ‖z‖ * ‖b‖ :=
            (norm_add_le _ _).trans (by rw [norm_smul])
          nlinarith

theorem normSum_eq_zero {W : List 𝔸} (h : normSum W = 0) : ∀ b ∈ W, b = 0 := by
  induction W with
  | nil => simp
  | cons b W ih =>
      rw [normSum_cons] at h
      have h1 : ‖b‖ = 0 := le_antisymm (by linarith [normSum_nonneg W]) (norm_nonneg _)
      have h2 : normSum W = 0 := le_antisymm (by linarith [norm_nonneg b]) (normSum_nonneg _)
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact norm_eq_zero.1 h1
      · exact ih h2 c hc

theorem lineList_of_normSum_eq_zero {L W : List 𝔸} (h : normSum W = 0) (z : ℂ) :
    lineList L W z = lineList L W 0 := by
  induction L generalizing W with
  | nil => simp [lineList]
  | cons a L ih =>
      cases W with
      | nil => simp [lineList]
      | cons b W =>
          have hb : b = 0 := normSum_eq_zero h b (by simp)
          have hW : normSum W = 0 := by
            rw [normSum_cons, hb, norm_zero, zero_add] at h; exact h
          have := ih hW
          simp only [lineList] at this ⊢
          simp only [List.zipWith_cons_cons, hb, smul_zero, this]

/-! ### Elementary bounds -/

/-- `‖e^{x₁} ⋯ e^{x_m} - 1‖ ≤ e^{2 s} - 1` when `s = Σ ‖xᵢ‖ ≤ 1`. -/
theorem norm_expProd_sub_one_le (L : List 𝔸) (hL : normSum L ≤ 1) :
    ‖expProd L - 1‖ ≤ Real.exp (2 * normSum L) - 1 := by
  induction L with
  | nil => simp
  | cons x L ih =>
      rw [normSum_cons] at hL
      have hx : ‖x‖ ≤ 1 := by linarith [normSum_nonneg L]
      have hL' : normSum L ≤ 1 := by linarith [norm_nonneg x]
      have h1 := ih hL'
      have h2 : ‖exp x - 1‖ ≤ 2 * ‖x‖ := SeriesLogChart.norm_exp_sub_one_le hx
      have h3 : ‖exp x‖ ≤ 1 + 2 * ‖x‖ := SeriesLogChart.norm_exp_le_one_add hx
      have e : expProd (x :: L) - 1 = exp x * (expProd L - 1) + (exp x - 1) := by
        rw [expProd_cons]; noncomm_ring
      rw [e, normSum_cons]
      have hE : 1 + 2 * ‖x‖ ≤ Real.exp (2 * ‖x‖) := by
        have := Real.add_one_le_exp (2 * ‖x‖); linarith
      have hP0 : 0 ≤ Real.exp (2 * normSum L) - 1 := by
        have := Real.add_one_le_exp (2 * normSum L)
        linarith [normSum_nonneg L]
      calc ‖exp x * (expProd L - 1) + (exp x - 1)‖
          ≤ ‖exp x‖ * ‖expProd L - 1‖ + ‖exp x - 1‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
        _ ≤ Real.exp (2 * ‖x‖) * (Real.exp (2 * normSum L) - 1) + (Real.exp (2 * ‖x‖) - 1) := by
            gcongr
            · exact h3.trans hE
            · linarith
        _ = Real.exp (2 * (‖x‖ + normSum L)) - 1 := by
            rw [mul_add, Real.exp_add]; ring

theorem exp_half_sub_one_lt : Real.exp (1 / 2) - 1 < 1 := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

/-! ### Complex differentiability along a line -/

theorem real_smul_eq (r : ℝ) (x : 𝔸) : r • x = (r : ℂ) • x :=
  RCLike.real_smul_eq_coe_smul (K := ℂ) r x

theorem differentiable_line (a b : 𝔸) : Differentiable ℂ fun z : ℂ => a + z • b :=
  (differentiable_const a).add (differentiable_id.smul_const b)

theorem differentiable_expProd_lineList (L W : List 𝔸) :
    Differentiable ℂ fun z => expProd (lineList L W z) := by
  induction L generalizing W with
  | nil => simp [lineList]
  | cons a L ih =>
      cases W with
      | nil => simp [lineList]
      | cons b W =>
          have h := ih W
          simp only [lineList] at h ⊢
          simp only [List.zipWith_cons_cons, expProd_cons]
          intro z
          refine DifferentiableAt.fun_mul ?_ (h z)
          exact ((NormedSpace.exp_analytic (𝕂 := ℂ) (a + z • b)).differentiableAt).comp z
            (differentiable_line a b z)

theorem differentiable_sum_lineList (L W : List 𝔸) :
    Differentiable ℂ fun z => (lineList L W z).sum := by
  induction L generalizing W with
  | nil => simp [lineList]
  | cons a L ih =>
      cases W with
      | nil => simp [lineList]
      | cons b W =>
          have h := ih W
          simp only [lineList] at h ⊢
          simp only [List.zipWith_cons_cons, List.sum_cons]
          exact (differentiable_line a b).add h

theorem differentiable_commTerm_lineList (L W : List 𝔸) :
    Differentiable ℂ fun z => commTerm (lineList L W z) := by
  induction L generalizing W with
  | nil => simp [lineList, commTerm]
  | cons a L ih =>
      cases W with
      | nil => simp [lineList, commTerm]
      | cons b W =>
          have h := ih W
          have hs := differentiable_sum_lineList L W
          simp only [lineList] at h hs ⊢
          simp only [List.zipWith_cons_cons, commTerm]
          simp_rw [real_smul_eq]
          exact Differentiable.add (Differentiable.const_smul
            (((differentiable_line a b).mul hs).sub (hs.mul (differentiable_line a b)))
            (((1 / 2 : ℝ) : ℂ))) h

theorem differentiable_logTerm {f : ℂ → 𝔸} (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ fun z => logTerm (f z) n := by
  unfold logTerm
  simp_rw [real_smul_eq]
  exact (hf.pow (n + 1)).const_smul ((((-1 : ℝ) ^ n / ((n : ℝ) + 1) : ℝ) : ℂ))

/-- **The Mercator logarithm of a holomorphic function** with values in a ball `‖·‖ ≤ q < 1` is
holomorphic (Weierstrass M-test, `differentiableOn_tsum_of_summable_norm`). -/
theorem differentiableOn_logOnePlus_comp {f : ℂ → 𝔸} (hf : Differentiable ℂ f) {U : Set ℂ}
    (hU : IsOpen U) {q : ℝ} (hq : q < 1) (hfq : ∀ z ∈ U, ‖f z‖ ≤ q) :
    DifferentiableOn ℂ (fun z => logOnePlus (f z)) U := by
  by_cases hU0 : U.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hU0
    have hq0 : 0 ≤ q := (norm_nonneg _).trans (hfq z₀ hz₀)
    have hsum : Summable fun n : ℕ => q ^ (n + 1) := by
      simpa [pow_succ] using (summable_geometric_of_lt_one hq0 hq).mul_right q
    refine Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun n => (differentiable_logTerm hf n).differentiableOn) hU fun n z hz => ?_
    exact (norm_logTerm_le (f z) n).trans (pow_le_pow_left₀ (norm_nonneg _) (hfq z hz) _)
  · rw [Set.not_nonempty_iff_eq_empty] at hU0
    rw [hU0]; exact differentiableOn_empty

/-- The BCH remainder along a line is holomorphic on the open set where `Σ ‖xᵢ + z wᵢ‖ < 1/4`
(more precisely on any open `U` where it is `≤ 1/4`). -/
theorem differentiableOn_bchRem_lineList (L W : List 𝔸) {U : Set ℂ} (hU : IsOpen U)
    (hUs : ∀ z ∈ U, normSum (lineList L W z) ≤ 1 / 4) :
    DifferentiableOn ℂ (fun z => bchRem (lineList L W z)) U := by
  unfold bchRem
  refine DifferentiableOn.sub ?_ ((differentiable_sum_lineList L W).add
    (differentiable_commTerm_lineList L W)).differentiableOn
  refine differentiableOn_logOnePlus_comp ((differentiable_expProd_lineList L W).sub_const 1) hU
    exp_half_sub_one_lt fun z hz => ?_
  refine (norm_expProd_sub_one_le _ ((hUs z hz).trans (by norm_num))).trans ?_
  have : Real.exp (2 * normSum (lineList L W z)) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.2 (by linarith [hUs z hz])
  linarith

/-! ### The derivative bound -/

/-- The derivative bound with an auxiliary radius `r ≥ s`, `0 < r ≤ 1/16`. -/
theorem norm_deriv_bchRem_le_of_le (L W : List 𝔸) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 16)
    (hL : normSum L ≤ r) :
    DifferentiableAt ℂ (fun z => bchRem (lineList L W z)) 0 ∧
      ‖deriv (fun z => bchRem (lineList L W z)) 0‖ ≤ 48 * r ^ 2 * normSum W := by
  set sW := normSum W
  have hsW : 0 ≤ sW := normSum_nonneg W
  rcases hsW.lt_or_eq with hpos | hzero
  · set ρ := r / sW
    have hρ : 0 < ρ := div_pos hr hpos
    have hU : ∀ z ∈ ball (0 : ℂ) (3 * ρ), normSum (lineList L W z) ≤ 1 / 4 := by
      intro z hz
      rw [mem_ball_zero_iff] at hz
      refine (normSum_lineList_le L W z).trans ?_
      have : ‖z‖ * sW ≤ 3 * ρ * sW := mul_le_mul_of_nonneg_right hz.le hsW
      have e : 3 * ρ * sW = 3 * r := by simp only [ρ]; field_simp
      linarith
    have hd := differentiableOn_bchRem_lineList L W isOpen_ball hU
    have hdiff : DifferentiableAt ℂ (fun z => bchRem (lineList L W z)) 0 :=
      hd.differentiableAt (ball_mem_nhds 0 (by positivity))
    refine ⟨hdiff, ?_⟩
    have hcl : closedBall (0 : ℂ) ρ ⊆ ball 0 (3 * ρ) :=
      closedBall_subset_ball (by linarith)
    have hsph : ∀ z ∈ sphere (0 : ℂ) ρ, ‖bchRem (lineList L W z)‖ ≤ 48 * r ^ 3 := by
      intro z hz
      rw [mem_sphere_zero_iff_norm] at hz
      have hs : normSum (lineList L W z) ≤ 2 * r := by
        refine (normSum_lineList_le L W z).trans ?_
        rw [hz]
        have e : ρ * sW = r := by simp only [ρ]; field_simp
        linarith
      have hb := norm_log_expProd_sub_bch_le (lineList L W z) (by linarith)
      refine hb.trans ?_
      have h0 := normSum_nonneg (lineList L W z)
      have : normSum (lineList L W z) ^ 3 ≤ (2 * r) ^ 3 := pow_le_pow_left₀ h0 hs 3
      nlinarith
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ (hd.diffContOnCl_ball hcl) hsph
    refine hc.trans (le_of_eq ?_)
    simp only [ρ]
    field_simp
  · -- `W = 0`: the line is constant
    have hconst : (fun z => bchRem (lineList L W z)) = fun _ => bchRem (lineList L W 0) := by
      funext z; rw [lineList_of_normSum_eq_zero hzero.symm z]
    rw [hconst, deriv_const, norm_zero, ← hzero, mul_zero]
    exact ⟨differentiableAt_const _, le_rfl⟩

/-- **Derivative bound for the BCH remainder.**  If `s = Σ ‖xᵢ‖ ≤ 1/32`, then
`z ↦ bchRem (L + z W)` is complex-differentiable at `0` and
`‖(d/dz) bchRem (L + z W)|_{z=0}‖ ≤ 48 s² Σ ‖wᵢ‖`. -/
theorem norm_deriv_bchRem_le (L W : List 𝔸) (hL : normSum L ≤ 1 / 32) :
    DifferentiableAt ℂ (fun z => bchRem (lineList L W z)) 0 ∧
      ‖deriv (fun z => bchRem (lineList L W z)) 0‖ ≤ 48 * normSum L ^ 2 * normSum W := by
  refine ⟨(norm_deriv_bchRem_le_of_le L W (r := 1 / 32) (by norm_num) (by norm_num) hL).1, ?_⟩
  have hs0 : 0 ≤ normSum L := normSum_nonneg L
  -- approximate radii `r = s + δ`
  have hlim : Tendsto (fun δ : ℝ => 48 * (normSum L + δ) ^ 2 * normSum W) (𝓝[>] 0)
      (𝓝 (48 * normSum L ^ 2 * normSum W)) := by
    have : Continuous fun δ : ℝ => 48 * (normSum L + δ) ^ 2 * normSum W := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 32 by norm_num)] with δ hδ
  exact (norm_deriv_bchRem_le_of_le L W (r := normSum L + δ) (by linarith [hδ.1])
    (by linarith [hδ.2]) (by linarith [hδ.1])).2

/-- The real directional derivative: `t ↦ bchRem (L + t W)` (`t ∈ ℝ`) has derivative
`D = (d/dz) bchRem(L + z W)|₀` at `0`, with `‖D‖ ≤ 48 s² Σ ‖wᵢ‖` for `s ≤ 1/32`. -/
theorem hasDerivAt_real_bchRem (L W : List 𝔸) (hL : normSum L ≤ 1 / 32) :
    HasDerivAt (fun t : ℝ => bchRem (lineList L W (t : ℂ)))
      (deriv (fun z => bchRem (lineList L W z)) 0) 0 := by
  have h := (norm_deriv_bchRem_le L W hL).1.hasDerivAt
  have h' : HasDerivAt (fun z => bchRem (lineList L W z))
      (deriv (fun z => bchRem (lineList L W z)) 0) ((0 : ℝ) : ℂ) := by simpa using h
  have := h'.scomp (0 : ℝ) Complex.ofRealCLM.hasDerivAt
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul, Function.comp_def] using this

/-! ### The polarisation of the commutator term -/

section Polarisation

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- The real line `t ↦ (xᵢ + t wᵢ)ᵢ`. -/
def lineListR (L W : List 𝔸) (t : ℝ) : List 𝔸 := List.zipWith (fun a b => a + t • b) L W

/-- The polarisation `D(½ Σ_{i<j}[xᵢ,xⱼ])[w]` of the commutator term. -/
def commPol : List 𝔸 → List 𝔸 → 𝔸
  | x :: L, w :: W => (1 / 2 : ℝ) • (x * W.sum + w * L.sum - L.sum * w - W.sum * x) + commPol L W
  | _, _ => 0

theorem sum_lineListR (L W : List 𝔸) (h : L.length = W.length) (t : ℝ) :
    (lineListR L W t).sum = L.sum + t • W.sum := by
  induction L generalizing W with
  | nil => cases W with
    | nil => simp [lineListR]
    | cons b W => simp at h
  | cons a L ih => cases W with
    | nil => simp at h
    | cons b W =>
        have := ih W (by simpa using h)
        simp only [lineListR] at this ⊢
        simp only [List.zipWith_cons_cons, List.sum_cons, this, smul_add]
        abel

theorem commTerm_lineListR (L W : List 𝔸) (h : L.length = W.length) (t : ℝ) :
    commTerm (lineListR L W t) = commTerm L + t • commPol L W + (t ^ 2) • commTerm W := by
  induction L generalizing W with
  | nil => cases W with
    | nil => simp [lineListR, commTerm, commPol]
    | cons b W => simp at h
  | cons a L ih => cases W with
    | nil => simp at h
    | cons b W =>
        have hl : L.length = W.length := by simpa using h
        have := ih W hl
        have hs := sum_lineListR L W hl t
        simp only [lineListR] at this hs ⊢
        simp only [List.zipWith_cons_cons, commTerm, commPol, this, hs]
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub,
          smul_smul]
        module

theorem hasDerivAt_commTerm_lineListR (L W : List 𝔸) (h : L.length = W.length) :
    HasDerivAt (fun t : ℝ => commTerm (lineListR L W t)) (commPol L W) 0 := by
  simp_rw [commTerm_lineListR L W h]
  have h1 : HasDerivAt (fun t : ℝ => t • commPol L W) ((1 : ℝ) • commPol L W) 0 :=
    (hasDerivAt_id (0 : ℝ)).smul_const _
  have h2 : HasDerivAt (fun t : ℝ => (t ^ 2) • commTerm W)
      (((2 : ℕ) * (0 : ℝ) ^ (2 - 1)) • commTerm W) 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).smul_const _
  exact (((hasDerivAt_const (0 : ℝ) (commTerm L)).add h1).add h2).congr_deriv (by simp)

theorem hasDerivAt_sum_lineListR (L W : List 𝔸) (h : L.length = W.length) :
    HasDerivAt (fun t : ℝ => (lineListR L W t).sum) W.sum 0 := by
  simp_rw [sum_lineListR L W h]
  exact ((hasDerivAt_const (0 : ℝ) L.sum).add ((hasDerivAt_id (0 : ℝ)).smul_const W.sum)).congr_deriv
    (by simp)

theorem sum_map_smul' (c : ℝ) (L : List 𝔸) : (L.map fun w => c • w).sum = c • L.sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih, smul_add]

theorem commPol_map_smul (c : ℝ) (L W : List 𝔸) :
    commPol (L.map fun w => c • w) (W.map fun w => c • w) = (c ^ 2) • commPol L W := by
  induction L generalizing W with
  | nil => simp [commPol]
  | cons a L ih => cases W with
    | nil => simp [commPol]
    | cons b W =>
        simp only [List.map_cons, commPol, ih, sum_map_smul']
        simp only [smul_mul_smul_comm, smul_sub, smul_add, smul_smul]
        module

/-- The explicit polarisation of four slots. -/
theorem commPol_four (a b c e α β γ ε : 𝔸) :
    commPol [a, b, c, e] [α, β, γ, ε] =
      (1 / 2 : ℝ) • (a * (β + γ + ε) + α * (b + c + e) - (b + c + e) * α - (β + γ + ε) * a) +
      ((1 / 2 : ℝ) • (b * (γ + ε) + β * (c + e) - (c + e) * β - (γ + ε) * b) +
      ((1 / 2 : ℝ) • (c * ε + γ * e - e * γ - ε * c))) := by
  simp only [commPol, List.sum_cons, List.sum_nil, add_zero, mul_zero, zero_mul, sub_zero,
    smul_zero, add_assoc]

/-- In the limit `W = (p, q, -p, -q)`, `w = (α, β, -α, -β)` the polarisation is
`[p, β] + [α, q]`. -/
theorem commPol_limit (p q α β : 𝔸) :
    commPol [p, q, -p, -q] [α, β, -α, -β] = (p * β - β * p) + (α * q - q * α) := by
  rw [commPol_four]
  simp only [mul_add, add_mul, mul_neg, neg_mul, neg_neg, smul_sub, smul_add, smul_neg]
  module

/-- `‖D(½Σ[xᵢ,xⱼ])[w]‖ ≤ (Σ‖xᵢ‖)(Σ‖wᵢ‖)`. -/
theorem norm_commPol_le (L W : List 𝔸) : ‖commPol L W‖ ≤ normSum L * normSum W := by
  induction L generalizing W with
  | nil => simp [commPol, normSum_nonneg]
  | cons x L ih => cases W with
    | nil => simp [commPol, normSum_nonneg, mul_nonneg]
    | cons w W =>
        simp only [commPol, normSum_cons]
        have h1 := ih W
        have hL := norm_sum_le_normSum L
        have hW := norm_sum_le_normSum W
        have h0L := normSum_nonneg L
        have h0W := normSum_nonneg W
        have hx := norm_nonneg x
        have hw := norm_nonneg w
        have hq : ‖x * W.sum + w * L.sum - L.sum * w - W.sum * x‖ ≤
            2 * ‖x‖ * normSum W + 2 * ‖w‖ * normSum L := by
          have := norm_sub_le (x * W.sum + w * L.sum - L.sum * w) (W.sum * x)
          have := norm_sub_le (x * W.sum + w * L.sum) (L.sum * w)
          have := norm_add_le (x * W.sum) (w * L.sum)
          have := norm_mul_le x W.sum
          have := norm_mul_le w L.sum
          have := norm_mul_le L.sum w
          have := norm_mul_le W.sum x
          nlinarith [mul_le_mul_of_nonneg_left hW hx, mul_le_mul_of_nonneg_left hL hw,
            mul_le_mul_of_nonneg_right hL hw, mul_le_mul_of_nonneg_right hW hx]
        calc ‖(1 / 2 : ℝ) • (x * W.sum + w * L.sum - L.sum * w - W.sum * x) + commPol L W‖
            ≤ 1 / 2 * (2 * ‖x‖ * normSum W + 2 * ‖w‖ * normSum L) + normSum L * normSum W := by
              refine (norm_add_le _ _).trans (add_le_add ?_ h1)
              rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
              exact mul_le_mul_of_nonneg_left hq (by norm_num)
          _ ≤ (‖x‖ + normSum L) * (‖w‖ + normSum W) := by nlinarith [mul_nonneg hx hw]

/-- The difference list `(xᵢ - yᵢ)ᵢ`. -/
def subList (L L' : List 𝔸) : List 𝔸 := List.zipWith (fun a b => a - b) L L'

theorem length_subList {L L' : List 𝔸} (h : L.length = L'.length) :
    (subList L L').length = L'.length := by
  simp [subList, h]

theorem lineListR_subList_one {L L' : List 𝔸} (h : L.length = L'.length) :
    lineListR L' (subList L L') 1 = L := by
  induction L generalizing L' with
  | nil => cases L' with
    | nil => rfl
    | cons b L' => simp at h
  | cons a L ih => cases L' with
    | nil => simp at h
    | cons b L' =>
        have := ih (L' := L') (by simpa using h)
        simp only [lineListR, subList] at this ⊢
        simp only [List.zipWith_cons_cons, one_smul, add_sub_cancel] at this ⊢
        rw [this]

theorem lineListR_zero {L W : List 𝔸} (h : L.length = W.length) : lineListR L W 0 = L := by
  induction L generalizing W with
  | nil => rfl
  | cons a L ih => cases W with
    | nil => simp at h
    | cons b W =>
        have := ih (W := W) (by simpa using h)
        simp only [lineListR] at this ⊢
        simp only [List.zipWith_cons_cons, zero_smul, add_zero] at this ⊢
        rw [this]

theorem lineListR_lineListR (L W : List 𝔸) (t u : ℝ) :
    lineListR (lineListR L W t) W u = lineListR L W (t + u) := by
  induction L generalizing W with
  | nil => rfl
  | cons a L ih => cases W with
    | nil => rfl
    | cons b W =>
        have := ih W
        simp only [lineListR] at this ⊢
        simp only [List.zipWith_cons_cons, this, add_smul, add_assoc]

theorem length_lineListR {L W : List 𝔸} (h : L.length = W.length) (t : ℝ) :
    (lineListR L W t).length = L.length := by
  simp [lineListR, h]

theorem normSum_subList_le (L L' : List 𝔸) :
    normSum (subList L L') ≤ normSum L + normSum L' := by
  induction L generalizing L' with
  | nil => simp [subList, normSum_nonneg]
  | cons a L ih => cases L' with
    | nil => simp [subList]; exact add_nonneg (norm_nonneg _) (normSum_nonneg _)
    | cons b L' =>
        have := ih L'
        simp only [subList] at this ⊢
        simp only [List.zipWith_cons_cons, normSum_cons]
        have := norm_sub_le a b
        linarith

/-- Along the segment from `L'` to `L`, `Σ ‖yᵢ + t(xᵢ - yᵢ)‖ ≤ (1-t) Σ‖yᵢ‖ + t Σ‖xᵢ‖`. -/
theorem normSum_lineListR_subList_le {L L' : List 𝔸} (h : L.length = L'.length) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    normSum (lineListR L' (subList L L') t) ≤ (1 - t) * normSum L' + t * normSum L := by
  induction L generalizing L' with
  | nil => cases L' with
    | nil => simp [lineListR, subList]
    | cons b L' => simp at h
  | cons a L ih => cases L' with
    | nil => simp at h
    | cons b L' =>
        have := ih (L' := L') (by simpa using h)
        simp only [lineListR, subList] at this ⊢
        simp only [List.zipWith_cons_cons, normSum_cons]
        have e : b + t • (a - b) = (1 - t) • b + t • a := by
          simp only [smul_sub, sub_smul, one_smul]; abel
        have hb : ‖b + t • (a - b)‖ ≤ (1 - t) * ‖b‖ + t * ‖a‖ := by
          rw [e]
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
        nlinarith

/-- **Lipschitz bound for the commutator term**:
`‖½Σ[xᵢ,xⱼ] - ½Σ[yᵢ,yⱼ]‖ ≤ (Σ‖xᵢ‖ + 2Σ‖yᵢ‖) Σ‖xᵢ - yᵢ‖`. -/
theorem norm_commTerm_sub_le {L L' : List 𝔸} (h : L.length = L'.length) :
    ‖commTerm L - commTerm L'‖ ≤ (normSum L + 2 * normSum L') * normSum (subList L L') := by
  set D := subList L L'
  have hl : L'.length = D.length := (length_subList h).symm
  have e := commTerm_lineListR L' D hl 1
  rw [lineListR_subList_one h] at e
  rw [e]
  simp only [one_smul, one_pow]
  rw [show commTerm L' + commPol L' D + commTerm D - commTerm L' = commPol L' D + commTerm D by
    abel]
  have h1 := norm_commPol_le L' D
  have h2 := norm_commTerm_le D
  have hD := normSum_subList_le L L'
  have h0 := normSum_nonneg D
  have h0' := normSum_nonneg L'
  calc ‖commPol L' D + commTerm D‖ ≤ normSum L' * normSum D + normSum D ^ 2 / 2 :=
        (norm_add_le _ _).trans (add_le_add h1 h2)
    _ ≤ (normSum L + 2 * normSum L') * normSum D := by nlinarith

end Polarisation

/-! ### Lipschitz bound for the BCH remainder -/

section Lipschitz

theorem lineList_eq_lineListR (L W : List 𝔸) (t : ℝ) :
    lineList L W (t : ℂ) = lineListR L W t := by
  simp only [lineList, lineListR, real_smul_eq]

/-- **Lipschitz bound for the cubic BCH remainder** (from the Cauchy derivative bound and the mean
value inequality): for lists of equal length with `Σ‖xᵢ‖, Σ‖yᵢ‖ ≤ m ≤ 1/32`,
`‖bchRem L - bchRem L'‖ ≤ 48 m² Σ‖xᵢ - yᵢ‖`. -/
theorem norm_bchRem_sub_le {L L' : List 𝔸} (h : L.length = L'.length) {m : ℝ}
    (hm : m ≤ 1 / 32) (hL : normSum L ≤ m) (hL' : normSum L' ≤ m) :
    ‖bchRem L - bchRem L'‖ ≤ 48 * m ^ 2 * normSum (subList L L') := by
  set D := subList L L'
  have hl : L'.length = D.length := (length_subList h).symm
  set g : ℝ → 𝔸 := fun t => bchRem (lineListR L' D t)
  have hs : ∀ t ∈ Set.Icc (0 : ℝ) 1, normSum (lineListR L' D t) ≤ m := by
    intro t ht
    refine (normSum_lineListR_subList_le h ht.1 ht.2).trans ?_
    nlinarith [ht.1, ht.2]
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ g' : 𝔸, HasDerivAt g g' t ∧
      ‖g'‖ ≤ 48 * m ^ 2 * normSum D := by
    intro t ht
    set M := lineListR L' D t
    have hM : normSum M ≤ 1 / 32 := (hs t ht).trans hm
    have hd := hasDerivAt_real_bchRem M D hM
    have hb := (norm_deriv_bchRem_le M D hM).2
    simp_rw [lineList_eq_lineListR, M, lineListR_lineListR] at hd
    refine ⟨_, ?_, hb.trans ?_⟩
    · have hd' : HasDerivAt (fun u => bchRem (lineListR L' D (t + u)))
          (deriv (fun z => bchRem (lineList M D z)) 0) (t - t) := by rwa [sub_self]
      have := hd'.comp_sub_const t t
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
      simp only [g, add_sub_cancel]
    · have h0 := normSum_nonneg M
      have h0D := normSum_nonneg D
      have : normSum M ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ h0 (hs t ht) 2
      nlinarith
  choose! g' hg' hg'b using hderiv
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := g')
    (fun t ht => (hg' t ht).hasDerivWithinAt) (fun t ht => hg'b t (Set.Ico_subset_Icc_self ht))
    1 ⟨zero_le_one, le_rfl⟩
  have e1 : g 1 = bchRem L := by
    show bchRem (lineListR L' (subList L L') 1) = _
    rw [lineListR_subList_one h]
  have e0 : g 0 = bchRem L' := by
    show bchRem (lineListR L' D 0) = _
    rw [lineListR_zero hl]
  rw [e1, e0] at hmv
  simpa using hmv

end Lipschitz

end

end RenewalGeometry.PlaquetteLogDerivative
