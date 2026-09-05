/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Process-stock Jordan accounting and assembly-before-payment

Machinery for `thm:GT-process-stock-Jordan`.  On a filtered probability space `(Ω, ℱ, μ)` with
a stock `Bₙ` and a declared inflow `iₙ₊₁`, the predictable signed drift is
`dₙ₊₁ = Bₙ + iₙ₊₁ - E[Bₙ₊₁ | ℱₙ]`, with Jordan parts `pₙ₊₁ = (dₙ₊₁)₊`, `rₙ₊₁ = (dₙ₊₁)₋` and the
martingale innovation `ξₙ₊₁ = Bₙ₊₁ - E[Bₙ₊₁ | ℱₙ]`.

* (SC.4a) `Bₙ₊₁ = Bₙ + iₙ₊₁ - pₙ₊₁ + rₙ₊₁ + ξₙ₊₁`, `pₙ₊₁ rₙ₊₁ = 0`, `E[ξₙ₊₁ | ℱₙ] = 0`
  (`jordan_decomp`, `pay_mul_repl`, `condExp_inno`);
* (SC.4b) the stock balance `E Bₙ + ∑ E pₖ₊₁ = E B₀ + ∑ E iₖ₊₁ + ∑ E rₖ₊₁` (`stock_balance`);
* (SC.4c) any other nonnegative accounting `(a, b)` of the same stock is `(p + h, r + h)` for a
  unique nonnegative duplicated turnover `h`, predictable when `a` is (`unique_turnover`);
* (SC.4d) assembling component drifts before taking positive parts erases exactly
  `h_assm = ½(∑|dₐ| - |∑ dₐ|) ≥ 0` (`assembly_turnover`);
* (SC.4e) a declared debit `c` paid by the stock satisfies `c ≤ p + ε` (`debit_le_pay`).
-/

open MeasureTheory

namespace NCG
namespace StockJordan

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (ℱ : Filtration ℕ mΩ) (B : ℕ → Ω → ℝ) (i : ℕ → Ω → ℝ)

/-- The predictable signed drift `dₙ₊₁ = Bₙ + iₙ₊₁ - E[Bₙ₊₁ | ℱₙ]`. -/
noncomputable def drift (n : ℕ) : Ω → ℝ :=
  fun ω => B n ω + i (n + 1) ω - (μ[B (n + 1) | ℱ n]) ω

/-- The debit `pₙ₊₁ = (dₙ₊₁)₊`. -/
noncomputable def pay (n : ℕ) : Ω → ℝ := fun ω => max (drift μ ℱ B i n ω) 0

/-- The replenishment `rₙ₊₁ = (dₙ₊₁)₋`. -/
noncomputable def repl (n : ℕ) : Ω → ℝ := fun ω => max (-(drift μ ℱ B i n ω)) 0

/-- The martingale innovation `ξₙ₊₁ = Bₙ₊₁ - E[Bₙ₊₁ | ℱₙ]`. -/
noncomputable def inno (n : ℕ) : Ω → ℝ := fun ω => B (n + 1) ω - (μ[B (n + 1) | ℱ n]) ω

/-! ### (SC.4a) -/

omit [IsProbabilityMeasure μ] in
/-- **(SC.4a)**: `Bₙ₊₁ = Bₙ + iₙ₊₁ - pₙ₊₁ + rₙ₊₁ + ξₙ₊₁`. -/
theorem jordan_decomp (n : ℕ) (ω : Ω) :
    B (n + 1) ω = B n ω + i (n + 1) ω - pay μ ℱ B i n ω + repl μ ℱ B i n ω
      + inno μ ℱ B n ω := by
  simp only [pay, repl, inno, drift]
  rcases le_total 0 (B n ω + i (n + 1) ω - (μ[B (n + 1) | ℱ n]) ω) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

omit [IsProbabilityMeasure μ] in
/-- **(SC.4a)**: no simultaneous debit and replenishment. -/
theorem pay_mul_repl (n : ℕ) (ω : Ω) : pay μ ℱ B i n ω * repl μ ℱ B i n ω = 0 := by
  simp only [pay, repl]
  rcases le_total 0 (drift μ ℱ B i n ω) with h | h
  · rw [max_eq_right (by linarith : -(drift μ ℱ B i n ω) ≤ 0), mul_zero]
  · rw [max_eq_right h, zero_mul]

/-- **(SC.4a)**: the innovation is a martingale difference. -/
theorem condExp_inno (n : ℕ) (hB : Integrable (B (n + 1)) μ) :
    μ[inno μ ℱ B n | ℱ n] =ᵐ[μ] 0 := by
  have h := condExp_sub hB (integrable_condExp (m := ℱ n) (f := B (n + 1))) (ℱ n)
  rw [condExp_of_stronglyMeasurable (ℱ.le n) stronglyMeasurable_condExp integrable_condExp,
    sub_self] at h
  exact h

theorem integral_inno (n : ℕ) (hB : Integrable (B (n + 1)) μ) :
    ∫ ω, inno μ ℱ B n ω ∂μ = 0 := by
  change ∫ ω, (B (n + 1) ω - (μ[B (n + 1) | ℱ n]) ω) ∂μ = 0
  rw [integral_sub hB integrable_condExp, integral_condExp (ℱ.le n), sub_self]

/-! ### Integrability and predictability -/

omit [IsProbabilityMeasure μ] in
theorem integrable_drift (n : ℕ) (hBn : Integrable (B n) μ) (hin : Integrable (i (n + 1)) μ) :
    Integrable (drift μ ℱ B i n) μ :=
  (hBn.add hin).sub integrable_condExp

omit [IsProbabilityMeasure μ] in
theorem integrable_pay (n : ℕ) (hBn : Integrable (B n) μ) (hin : Integrable (i (n + 1)) μ) :
    Integrable (pay μ ℱ B i n) μ :=
  (integrable_drift μ ℱ B i n hBn hin).pos_part

omit [IsProbabilityMeasure μ] in
theorem integrable_repl (n : ℕ) (hBn : Integrable (B n) μ) (hin : Integrable (i (n + 1)) μ) :
    Integrable (repl μ ℱ B i n) μ :=
  (integrable_drift μ ℱ B i n hBn hin).neg_part

omit [IsProbabilityMeasure μ] in
/-- The drift is predictable (`ℱₙ`-measurable). -/
theorem stronglyMeasurable_drift (n : ℕ) (hBn : StronglyMeasurable[ℱ n] (B n))
    (hin : StronglyMeasurable[ℱ n] (i (n + 1))) : StronglyMeasurable[ℱ n] (drift μ ℱ B i n) := by
  exact ((hBn.measurable.add hin.measurable).sub
    stronglyMeasurable_condExp.measurable).stronglyMeasurable

omit [IsProbabilityMeasure μ] in
theorem stronglyMeasurable_pay (n : ℕ) (hBn : StronglyMeasurable[ℱ n] (B n))
    (hin : StronglyMeasurable[ℱ n] (i (n + 1))) : StronglyMeasurable[ℱ n] (pay μ ℱ B i n) := by
  exact ((stronglyMeasurable_drift μ ℱ B i n hBn hin).measurable.max
    measurable_const).stronglyMeasurable

omit [IsProbabilityMeasure μ] in
theorem stronglyMeasurable_repl (n : ℕ) (hBn : StronglyMeasurable[ℱ n] (B n))
    (hin : StronglyMeasurable[ℱ n] (i (n + 1))) : StronglyMeasurable[ℱ n] (repl μ ℱ B i n) := by
  exact ((stronglyMeasurable_drift μ ℱ B i n hBn hin).measurable.neg.max
    measurable_const).stronglyMeasurable

/-! ### (SC.4b): the stock balance -/

/-- One step of the stock balance. -/
theorem integral_step (n : ℕ) (hBn : Integrable (B n) μ) (hBn1 : Integrable (B (n + 1)) μ)
    (hin : Integrable (i (n + 1)) μ) :
    ∫ ω, B (n + 1) ω ∂μ + ∫ ω, pay μ ℱ B i n ω ∂μ
      = ∫ ω, B n ω ∂μ + ∫ ω, i (n + 1) ω ∂μ + ∫ ω, repl μ ℱ B i n ω ∂μ := by
  have hpay := integrable_pay μ ℱ B i n hBn hin
  have hrepl := integrable_repl μ ℱ B i n hBn hin
  have hinno : Integrable (inno μ ℱ B n) μ := hBn1.sub integrable_condExp
  have h1 : Integrable (fun ω => B n ω + i (n + 1) ω) μ := hBn.add hin
  have h2 : Integrable (fun ω => B n ω + i (n + 1) ω - pay μ ℱ B i n ω) μ := h1.sub hpay
  have h3 : Integrable (fun ω => B n ω + i (n + 1) ω - pay μ ℱ B i n ω + repl μ ℱ B i n ω) μ :=
    h2.add hrepl
  have h : ∫ ω, B (n + 1) ω ∂μ
      = ∫ ω, (B n ω + i (n + 1) ω - pay μ ℱ B i n ω + repl μ ℱ B i n ω
          + inno μ ℱ B n ω) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => jordan_decomp μ ℱ B i n ω)
  rw [integral_add h3 hinno, integral_add h2 hrepl, integral_sub h1 hpay, integral_add hBn hin,
    integral_inno μ ℱ B n hBn1] at h
  rw [h]
  ring

/-- **(SC.4b)**: `E B_N + ∑_{n<N} E pₙ₊₁ = E B₀ + ∑_{n<N} E iₙ₊₁ + ∑_{n<N} E rₙ₊₁`. -/
theorem stock_balance (hB : ∀ n, Integrable (B n) μ) (hi : ∀ n, Integrable (i (n + 1)) μ)
    (N : ℕ) :
    ∫ ω, B N ω ∂μ + ∑ n ∈ Finset.range N, ∫ ω, pay μ ℱ B i n ω ∂μ
      = ∫ ω, B 0 ω ∂μ + ∑ n ∈ Finset.range N, ∫ ω, i (n + 1) ω ∂μ
        + ∑ n ∈ Finset.range N, ∫ ω, repl μ ℱ B i n ω ∂μ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have := integral_step μ ℱ B i N (hB N) (hB (N + 1)) (hi N)
    linarith

/-! ### (SC.4c): uniqueness of the Jordan accounting -/

omit [IsProbabilityMeasure μ] in
/-- **(SC.4c)**: any nonnegative accounting `(a, b)` of the same stock differs from `(p, r)` by a
unique nonnegative duplicated turnover `h`. -/
theorem unique_turnover (n : ℕ) (a b : Ω → ℝ) (ha : ∀ ω, 0 ≤ a ω) (hb : ∀ ω, 0 ≤ b ω)
    (hab : ∀ ω, B (n + 1) ω = B n ω + i (n + 1) ω - a ω + b ω + inno μ ℱ B n ω) :
    ∃! h : Ω → ℝ, (∀ ω, 0 ≤ h ω) ∧ a = pay μ ℱ B i n + h ∧ b = repl μ ℱ B i n + h := by
  have key : ∀ ω, a ω - b ω = pay μ ℱ B i n ω - repl μ ℱ B i n ω := by
    intro ω
    have h1 := jordan_decomp μ ℱ B i n ω
    have h2 := hab ω
    linarith
  refine ⟨a - pay μ ℱ B i n, ⟨fun ω => ?_, ?_, ?_⟩, ?_⟩
  · simp only [Pi.sub_apply, sub_nonneg]
    rcases le_total 0 (drift μ ℱ B i n ω) with h | h
    · have hp : pay μ ℱ B i n ω = drift μ ℱ B i n ω := max_eq_left h
      have hr : repl μ ℱ B i n ω = 0 := max_eq_right (by linarith)
      have := key ω
      have := hb ω
      linarith
    · have hp : pay μ ℱ B i n ω = 0 := max_eq_right h
      rw [hp]
      exact ha ω
  · ext ω
    simp
  · ext ω
    simp only [Pi.add_apply, Pi.sub_apply]
    have := key ω
    linarith
  · rintro h ⟨_, rfl, _⟩
    ext ω
    simp

omit [IsProbabilityMeasure μ] in
/-- The duplicated turnover is predictable when the alternative debit is. -/
theorem stronglyMeasurable_turnover (n : ℕ) (a : Ω → ℝ) (ha : StronglyMeasurable[ℱ n] a)
    (hBn : StronglyMeasurable[ℱ n] (B n)) (hin : StronglyMeasurable[ℱ n] (i (n + 1))) :
    StronglyMeasurable[ℱ n] (a - pay μ ℱ B i n) := by
  exact (ha.measurable.sub
    (stronglyMeasurable_pay μ ℱ B i n hBn hin).measurable).stronglyMeasurable

/-! ### (SC.4d): assembly before payment -/

/-- The turnover erased by assembling component drifts before taking positive parts:
`h_assm = ½(∑|dₐ| - |∑ dₐ|)`. -/
noncomputable def assmTurnover {m : Type*} (s : Finset m) (d : m → ℝ) : ℝ :=
  (∑ α ∈ s, |d α| - |∑ α ∈ s, d α|) / 2

theorem max_zero_eq (x : ℝ) : max x 0 = (|x| + x) / 2 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

theorem max_neg_zero_eq (x : ℝ) : max (-x) 0 = (|x| - x) / 2 := by
  rw [max_zero_eq, abs_neg]; ring

/-- **(SC.4d)**: `∑ (dₐ)₊ = (∑ dₐ)₊ + h_assm`, `∑ (dₐ)₋ = (∑ dₐ)₋ + h_assm`, `h_assm ≥ 0`. -/
theorem assembly_turnover {m : Type*} (s : Finset m) (d : m → ℝ) :
    ∑ α ∈ s, max (d α) 0 = max (∑ α ∈ s, d α) 0 + assmTurnover s d ∧
      ∑ α ∈ s, max (-(d α)) 0 = max (-(∑ α ∈ s, d α)) 0 + assmTurnover s d ∧
      0 ≤ assmTurnover s d := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [max_zero_eq, assmTurnover]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    ring
  · simp only [max_neg_zero_eq, assmTurnover]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  · unfold assmTurnover
    have := Finset.abs_sum_le_sum_abs d s
    linarith

/-! ### (SC.4e): declared debits paid by the stock -/

omit [IsProbabilityMeasure μ] in
/-- **(SC.4e)**: if `E[Bₙ₊₁ | ℱₙ] ≤ Bₙ + iₙ₊₁ - cₙ₊₁ + εₙ₊₁` with `ε ≥ 0`, then `c ≤ p + ε`. -/
theorem debit_le_pay (n : ℕ) (c ε : Ω → ℝ) (ω : Ω)
    (hpaid : (μ[B (n + 1) | ℱ n]) ω ≤ B n ω + i (n + 1) ω - c ω + ε ω) :
    c ω ≤ pay μ ℱ B i n ω + ε ω := by
  simp only [pay, drift]
  have := le_max_left (B n ω + i (n + 1) ω - (μ[B (n + 1) | ℱ n]) ω) 0
  linarith

/-- **`thm:GT-process-stock-Jordan`**: (SC.4a) the Jordan decomposition of the stock step with
`p r = 0` and martingale innovation; (SC.4b) the stock balance; (SC.4c) uniqueness of the
accounting up to a nonnegative duplicated turnover; (SC.4d) the assembly turnover identity;
(SC.4e) declared debits are dominated by the Jordan debit. -/
theorem process_stock_jordan (hB : ∀ n, Integrable (B n) μ) (hi : ∀ n, Integrable (i (n + 1)) μ) :
    (∀ n ω, B (n + 1) ω = B n ω + i (n + 1) ω - pay μ ℱ B i n ω + repl μ ℱ B i n ω
        + inno μ ℱ B n ω) ∧
      (∀ n ω, pay μ ℱ B i n ω * repl μ ℱ B i n ω = 0) ∧
      (∀ n, μ[inno μ ℱ B n | ℱ n] =ᵐ[μ] 0) ∧
      (∀ N, ∫ ω, B N ω ∂μ + ∑ n ∈ Finset.range N, ∫ ω, pay μ ℱ B i n ω ∂μ
        = ∫ ω, B 0 ω ∂μ + ∑ n ∈ Finset.range N, ∫ ω, i (n + 1) ω ∂μ
          + ∑ n ∈ Finset.range N, ∫ ω, repl μ ℱ B i n ω ∂μ) ∧
      (∀ n (a b : Ω → ℝ), (∀ ω, 0 ≤ a ω) → (∀ ω, 0 ≤ b ω) →
        (∀ ω, B (n + 1) ω = B n ω + i (n + 1) ω - a ω + b ω + inno μ ℱ B n ω) →
        ∃! h : Ω → ℝ, (∀ ω, 0 ≤ h ω) ∧ a = pay μ ℱ B i n + h ∧ b = repl μ ℱ B i n + h) ∧
      (∀ {m : Type} (s : Finset m) (d : m → ℝ),
        ∑ α ∈ s, max (d α) 0 = max (∑ α ∈ s, d α) 0 + assmTurnover s d ∧
        ∑ α ∈ s, max (-(d α)) 0 = max (-(∑ α ∈ s, d α)) 0 + assmTurnover s d ∧
        0 ≤ assmTurnover s d) ∧
      ∀ n (c ε : Ω → ℝ) (ω : Ω), 0 ≤ ε ω →
        (μ[B (n + 1) | ℱ n]) ω ≤ B n ω + i (n + 1) ω - c ω + ε ω →
        c ω ≤ pay μ ℱ B i n ω + ε ω :=
  ⟨jordan_decomp μ ℱ B i, pay_mul_repl μ ℱ B i, fun n => condExp_inno μ ℱ B n (hB (n + 1)),
    stock_balance μ ℱ B i hB hi, fun n a b ha hb hab => unique_turnover μ ℱ B i n a b ha hb hab,
    fun s d => assembly_turnover s d, fun n c ε ω _ hpaid => debit_le_pay μ ℱ B i n c ε ω hpaid⟩

end StockJordan
end NCG
