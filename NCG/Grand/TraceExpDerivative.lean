/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Derivatives of trace exponentials and the Duhamel/BKM series
  (machinery for `thm:renewal-memory-cumulant`)

Finite-dimensional differentiation of `t ↦ Tr(exp(H + tX) C)`
by term-wise differentiation of the exponential series, with
the locally uniform summable bounds required by
`hasFDerivAt_tsum_of_isPreconnected`:

* `traceExpMul_eq_tsum`: the trace of `exp(M) C` is the
  convergent series `∑ (m!)⁻¹ Tr(Mᵐ C)`;
* `hasDerivAt_pow_affine`: the derivative of `t ↦ (H + tX)ᵐ`
  is the two-sided Leibniz sum;
* `hasDerivAt_traceExpMul`: on the unit interval,
  `t ↦ Tr(exp(H + tX) C)` is differentiable with term-wise
  derivative series;
* `hasDerivAt_traceExp`: the first-derivative collapse
  `d/dt Tr exp(H + tX) = Tr(exp(H + tX) X)` by trace
  cyclicity;
* `bkmSeries` and `hasDerivAt_traceExpMul_zero`: the mixed
  second-derivative series
  `∑ (m!)⁻¹ ∑_{a+b=m-1} Tr(Hᵃ Y Hᵇ X)` — the Duhamel/BKM
  kernel in series form.
-/

open Matrix Filter
open scoped Topology Matrix.Norms.Operator

namespace NCG
namespace TraceExp

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- Entry bound for the `L∞` operator norm. -/
theorem entry_norm_le (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h1 : ‖A i j‖₊ ≤ ∑ j' : n, ‖A i j'‖₊ :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖₊)
      (fun _ _ => zero_le) (Finset.mem_univ j)
  have h2 : (∑ j' : n, ‖A i j'‖₊)
      ≤ Finset.univ.sup fun i' => ∑ j' : n, ‖A i' j'‖₊ :=
    Finset.le_sup (f := fun i' => ∑ j' : n, ‖A i' j'‖₊)
      (Finset.mem_univ i)
  have h3 : ‖A‖ = ↑(Finset.univ.sup
      fun i' => ∑ j' : n, ‖A i' j'‖₊) :=
    Matrix.linfty_opNorm_def A
  rw [h3]
  exact_mod_cast h1.trans h2

omit [Nonempty n] in
/-- Trace bound for the `L∞` operator norm. -/
theorem trace_norm_le (A : Matrix n n ℂ) :
    ‖A.trace‖ ≤ (Fintype.card n : ℝ) * ‖A‖ := by
  calc ‖A.trace‖ = ‖∑ i : n, A i i‖ := rfl
    _ ≤ ∑ i : n, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, ‖A‖ :=
        Finset.sum_le_sum fun i _ => entry_norm_le A i i
    _ = (Fintype.card n : ℝ) * ‖A‖ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- Trace against a fixed factor, as a continuous linear
map. -/
noncomputable def traceMulCLM (C : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap n ℂ ℂ).comp
      (LinearMap.mulRight ℂ C))

omit [Nonempty n] in
@[simp] theorem traceMulCLM_apply (C M : Matrix n n ℂ) :
    traceMulCLM C M = (M * C).trace := rfl

omit [Nonempty n] in
/-- The exponential-trace series against a fixed factor. -/
theorem traceExpMul_eq_tsum (M C : Matrix n n ℂ) :
    ((NormedSpace.exp M) * C).trace
      = ∑' m : ℕ, ((m.factorial : ℂ))⁻¹
          • ((M ^ m) * C).trace := by
  have h1 : ((NormedSpace.exp M) * C).trace
      = traceMulCLM C (NormedSpace.exp M) := rfl
  rw [h1, NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [ContinuousLinearMap.map_tsum (traceMulCLM C)
    (NormedSpace.expSeries_summable' (𝕂 := ℂ) M)]
  refine tsum_congr fun m => ?_
  rw [ContinuousLinearMap.map_smul]
  rfl

omit [DecidableEq n] [Nonempty n] in
set_option linter.unusedFintypeInType false in
/-- The affine path and its constant derivative.
(`Fintype n` is retained: the matrix norm instance needs it.) -/
theorem hasDerivAt_affine (H X : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => H + s • X) X t := by
  have h1 : HasDerivAt (fun s : ℝ => s • X)
      ((1 : ℝ) • X) t := (hasDerivAt_id t).smul_const X
  rw [one_smul] at h1
  exact h1.const_add H

omit [Nonempty n] in
/-- Two-sided Leibniz derivative of a matrix power along an
affine path. -/
theorem hasDerivAt_pow_affine (H X : Matrix n n ℂ) (m : ℕ)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => (H + s • X) ^ m)
      (∑ j ∈ Finset.range m,
        (H + t • X) ^ j * X * (H + t • X) ^ (m - 1 - j))
      t := by
  induction m with
  | zero =>
    have h0 := hasDerivAt_const (𝕜 := ℝ) t
      (1 : Matrix n n ℂ)
    have he : (∑ j ∈ Finset.range 0,
        (H + t • X) ^ j * X * (H + t • X) ^ (0 - 1 - j))
        = (0 : Matrix n n ℂ) := by
      rw [Finset.range_zero, Finset.sum_empty]
    rw [he]
    have hf : (fun _ : ℝ => (1 : Matrix n n ℂ))
        = fun s : ℝ => (H + s • X) ^ 0 := by
      funext s
      rw [pow_zero]
    rw [hf] at h0
    exact h0
  | succ m ih =>
    have hmul := (hasDerivAt_affine H X t).mul ih
    have hfun : ((fun s : ℝ => H + s • X)
        * fun s : ℝ => (H + s • X) ^ m)
        = fun s : ℝ => (H + s • X) ^ (m + 1) := by
      funext s
      rw [Pi.mul_apply, ← pow_succ']
    rw [hfun] at hmul
    have hsum : X * (H + t • X) ^ m
        + (H + t • X) * (∑ j ∈ Finset.range m,
          (H + t • X) ^ j * X * (H + t • X) ^ (m - 1 - j))
        = ∑ j ∈ Finset.range (m + 1),
          (H + t • X) ^ j * X
            * (H + t • X) ^ (m + 1 - 1 - j) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, Matrix.one_mul, Nat.sub_zero,
        Nat.add_sub_cancel]
      rw [add_comm, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [show m - (j + 1) = m - 1 - j from by omega,
        pow_succ', Matrix.mul_assoc, Matrix.mul_assoc,
        Matrix.mul_assoc]
    exact hsum ▸ hmul

omit [Nonempty n] in
/-- The Leibniz derivative of `t ↦ Tr((H + tX)ᵐ C)`. -/
theorem hasDerivAt_trace_pow_mul (H X C : Matrix n n ℂ)
    (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (((H + s • X) ^ m) * C).trace)
      (∑ j ∈ Finset.range m,
        ((H + t • X) ^ j * X
          * ((H + t • X) ^ (m - 1 - j) * C)).trace)
      t := by
  have h1 := HasFDerivAt.comp_hasDerivAt t
    (((traceMulCLM C).restrictScalars ℝ).hasFDerivAt
      (x := (H + t • X) ^ m))
    (hasDerivAt_pow_affine H X m t)
  have h2 : (⇑((traceMulCLM C).restrictScalars ℝ)
        ∘ fun s : ℝ => (H + s • X) ^ m)
      = fun s : ℝ => (((H + s • X) ^ m) * C).trace := by
    funext s
    rfl
  rw [h2] at h1
  have hval : ((traceMulCLM C).restrictScalars ℝ)
      (∑ j ∈ Finset.range m,
        (H + t • X) ^ j * X * (H + t • X) ^ (m - 1 - j))
      = ∑ j ∈ Finset.range m,
        ((H + t • X) ^ j * X
          * ((H + t • X) ^ (m - 1 - j) * C)).trace := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    change (((H + t • X) ^ j * X * (H + t • X) ^ (m - 1 - j))
        * C).trace
      = ((H + t • X) ^ j * X
          * ((H + t • X) ^ (m - 1 - j) * C)).trace
    rw [Matrix.mul_assoc]
  exact hval ▸ h1

/-- Norm bound for the Leibniz derivative terms. -/
theorem leibniz_term_bound (H X C : Matrix n n ℂ) (m : ℕ)
    (t : ℝ) (ht : |t| ≤ 1) :
    ‖∑ j ∈ Finset.range m,
      ((H + t • X) ^ j * X
        * ((H + t • X) ^ (m - 1 - j) * C)).trace‖
    ≤ (m : ℝ) * ((Fintype.card n : ℝ)
        * ((‖H‖ + ‖X‖ + 1) ^ (m - 1) * (‖X‖ * ‖C‖))) := by
  have hM : ‖H + t • X‖ ≤ ‖H‖ + ‖X‖ + 1 := by
    calc ‖H + t • X‖ ≤ ‖H‖ + ‖t • X‖ := norm_add_le _ _
      _ = ‖H‖ + |t| * ‖X‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖H‖ + 1 * ‖X‖ := by
          have := mul_le_mul_of_nonneg_right ht
            (norm_nonneg X)
          linarith
      _ ≤ ‖H‖ + ‖X‖ + 1 := by linarith
  have hterm : ∀ j ∈ Finset.range m,
      ‖((H + t • X) ^ j * X
        * ((H + t • X) ^ (m - 1 - j) * C)).trace‖
      ≤ (Fintype.card n : ℝ)
        * ((‖H‖ + ‖X‖ + 1) ^ (m - 1) * (‖X‖ * ‖C‖)) := by
    intro j hj
    have hjm := Finset.mem_range.mp hj
    have h2 : ‖(H + t • X) ^ j‖
        ≤ (‖H‖ + ‖X‖ + 1) ^ j :=
      (norm_pow_le _ _).trans
        (pow_le_pow_left₀ (norm_nonneg _) hM j)
    have h3 : ‖(H + t • X) ^ (m - 1 - j)‖
        ≤ (‖H‖ + ‖X‖ + 1) ^ (m - 1 - j) :=
      (norm_pow_le _ _).trans
        (pow_le_pow_left₀ (norm_nonneg _) hM _)
    have h4 : (‖H‖ + ‖X‖ + 1) ^ j
        * (‖H‖ + ‖X‖ + 1) ^ (m - 1 - j)
        ≤ (‖H‖ + ‖X‖ + 1) ^ (m - 1) := by
      rw [← pow_add]
      refine pow_le_pow_right₀ ?_ ?_
      · linarith [norm_nonneg H, norm_nonneg X]
      · omega
    have hb : ‖(H + t • X) ^ j * X
        * ((H + t • X) ^ (m - 1 - j) * C)‖
        ≤ (‖H‖ + ‖X‖ + 1) ^ (m - 1) * (‖X‖ * ‖C‖) := by
      calc ‖(H + t • X) ^ j * X
          * ((H + t • X) ^ (m - 1 - j) * C)‖
          ≤ ‖(H + t • X) ^ j * X‖
            * ‖(H + t • X) ^ (m - 1 - j) * C‖ :=
            norm_mul_le _ _
        _ ≤ (‖(H + t • X) ^ j‖ * ‖X‖)
            * (‖(H + t • X) ^ (m - 1 - j)‖ * ‖C‖) :=
            mul_le_mul (norm_mul_le _ _) (norm_mul_le _ _)
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ ((‖H‖ + ‖X‖ + 1) ^ j * ‖X‖)
            * ((‖H‖ + ‖X‖ + 1) ^ (m - 1 - j) * ‖C‖) := by
            gcongr
        _ = (‖H‖ + ‖X‖ + 1) ^ j
            * (‖H‖ + ‖X‖ + 1) ^ (m - 1 - j)
            * (‖X‖ * ‖C‖) := by ring
        _ ≤ (‖H‖ + ‖X‖ + 1) ^ (m - 1)
            * (‖X‖ * ‖C‖) :=
            mul_le_mul_of_nonneg_right h4
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    calc ‖((H + t • X) ^ j * X
        * ((H + t • X) ^ (m - 1 - j) * C)).trace‖
        ≤ (Fintype.card n : ℝ) * ‖(H + t • X) ^ j * X
          * ((H + t • X) ^ (m - 1 - j) * C)‖ :=
          trace_norm_le _
      _ ≤ (Fintype.card n : ℝ)
          * ((‖H‖ + ‖X‖ + 1) ^ (m - 1) * (‖X‖ * ‖C‖)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
  calc ‖∑ j ∈ Finset.range m,
      ((H + t • X) ^ j * X
        * ((H + t • X) ^ (m - 1 - j) * C)).trace‖
      ≤ ∑ j ∈ Finset.range m,
        ‖((H + t • X) ^ j * X
          * ((H + t • X) ^ (m - 1 - j) * C)).trace‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range m,
        (Fintype.card n : ℝ)
          * ((‖H‖ + ‖X‖ + 1) ^ (m - 1) * (‖X‖ * ‖C‖)) :=
        Finset.sum_le_sum hterm
    _ = (m : ℝ) * ((Fintype.card n : ℝ)
        * ((‖H‖ + ‖X‖ + 1) ^ (m - 1) * (‖X‖ * ‖C‖))) := by
        rw [Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]

/-- The real bound sequence for the derivative series. -/
noncomputable def uBound (H X C : Matrix n n ℂ) (m : ℕ) :
    ℝ :=
  ((m.factorial : ℝ))⁻¹ * ((m : ℝ) * ((Fintype.card n : ℝ)
    * ((‖H‖ + ‖X‖ + 1) ^ (m - 1) * (‖X‖ * ‖C‖))))

theorem uBound_summable (H X C : Matrix n n ℂ) :
    Summable (uBound H X C) := by
  rw [← summable_nat_add_iff 1]
  have hs := (Real.summable_pow_div_factorial
    (‖H‖ + ‖X‖ + 1)).mul_left
    ((Fintype.card n : ℝ) * (‖X‖ * ‖C‖))
  refine hs.congr fun k => ?_
  rw [uBound]
  simp only [Nat.add_sub_cancel]
  have hfact : ((k + 1).factorial : ℝ)
      = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfact]
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hkf : ((k.factorial : ℝ)) ≠ 0 := by positivity
  field_simp

theorem norm_inv_factorial (m : ℕ) :
    ‖((m.factorial : ℂ))⁻¹‖ = ((m.factorial : ℝ))⁻¹ := by
  rw [norm_inv, Complex.norm_natCast]

/-- **Term-wise differentiation of the exponential trace**:
on the open unit interval, `t ↦ Tr(exp(H + tX) C)` has the
term-wise derivative series. -/
theorem hasDerivAt_traceExpMul (H X C : Matrix n n ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt
      (fun t : ℝ => ((NormedSpace.exp (H + t • X))
        * C).trace)
      (∑' m : ℕ, ((m.factorial : ℂ))⁻¹
        • ∑ j ∈ Finset.range m,
          ((H + t₀ • X) ^ j * X
            * ((H + t₀ • X) ^ (m - 1 - j) * C)).trace)
      t₀ := by
  have hfun : (fun t : ℝ =>
      ((NormedSpace.exp (H + t • X)) * C).trace)
      = fun t : ℝ => ∑' m : ℕ, ((m.factorial : ℂ))⁻¹
          • (((H + t • X) ^ m) * C).trace := by
    funext t
    exact traceExpMul_eq_tsum (H + t • X) C
  rw [hfun]
  have hmain := hasFDerivAt_tsum_of_isPreconnected
    (𝕜 := ℝ) (E := ℝ) (F := ℂ)
    (u := uBound H X C)
    (f := fun m t => ((m.factorial : ℂ))⁻¹
      • (((H + t • X) ^ m) * C).trace)
    (f' := fun m t => ContinuousLinearMap.toSpanSingleton
      ℝ (((m.factorial : ℂ))⁻¹
        • ∑ j ∈ Finset.range m,
          ((H + t • X) ^ j * X
            * ((H + t • X) ^ (m - 1 - j) * C)).trace))
    (s := Set.Ioo (-1:ℝ) 1) (x₀ := 0) (x := t₀)
    (uBound_summable H X C) isOpen_Ioo
    (isPreconnected_Ioo)
    (fun m t _ =>
      ((hasDerivAt_trace_pow_mul H X C m t).const_smul
        (((m.factorial : ℂ))⁻¹)).hasFDerivAt)
    (fun m t ht => by
      rw [ContinuousLinearMap.norm_toSpanSingleton,
        norm_smul, norm_inv_factorial]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact leibniz_term_bound H X C m t
        (abs_le.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
    (by
      constructor <;> norm_num)
    (by
      refine Summable.of_norm_bounded
        (g := fun m => ((Fintype.card n : ℝ) * ‖C‖)
          * ((‖H‖ + ‖X‖ + 1) ^ m / (m.factorial : ℝ)))
        ((Real.summable_pow_div_factorial
          (‖H‖ + ‖X‖ + 1)).mul_left _) ?_
      intro m
      rw [norm_smul, norm_inv_factorial]
      have h1 : ‖(((H + (0:ℝ) • X) ^ m) * C).trace‖
          ≤ (Fintype.card n : ℝ)
            * ((‖H‖ + ‖X‖ + 1) ^ m * ‖C‖) := by
        refine (trace_norm_le _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_
          (by positivity)
        refine (norm_mul_le _ _).trans ?_
        refine mul_le_mul_of_nonneg_right ?_
          (norm_nonneg C)
        refine (norm_pow_le _ _).trans ?_
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ m
        rw [zero_smul, add_zero]
        linarith [norm_nonneg X]
      calc ((m.factorial : ℝ))⁻¹
          * ‖(((H + (0:ℝ) • X) ^ m) * C).trace‖
          ≤ ((m.factorial : ℝ))⁻¹
            * ((Fintype.card n : ℝ)
              * ((‖H‖ + ‖X‖ + 1) ^ m * ‖C‖)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ((Fintype.card n : ℝ) * ‖C‖)
            * ((‖H‖ + ‖X‖ + 1) ^ m
              / (m.factorial : ℝ)) := by
            field_simp)
    ht₀
  have hvsum : Summable (fun m : ℕ =>
      ((m.factorial : ℂ))⁻¹ • ∑ j ∈ Finset.range m,
        ((H + t₀ • X) ^ j * X
          * ((H + t₀ • X) ^ (m - 1 - j) * C)).trace) := by
    refine Summable.of_norm_bounded (g := uBound H X C)
      (uBound_summable H X C) ?_
    intro m
    rw [norm_smul, norm_inv_factorial]
    exact mul_le_mul_of_nonneg_left
      (leibniz_term_bound H X C m t₀
        (abs_le.mpr ⟨le_of_lt ht₀.1, le_of_lt ht₀.2⟩))
      (by positivity)
  have hswap : (∑' m : ℕ,
      ContinuousLinearMap.toSpanSingleton ℝ
        (((m.factorial : ℂ))⁻¹ • ∑ j ∈ Finset.range m,
          ((H + t₀ • X) ^ j * X
            * ((H + t₀ • X) ^ (m - 1 - j) * C)).trace))
      = ContinuousLinearMap.toSpanSingleton ℝ
        (∑' m : ℕ, ((m.factorial : ℂ))⁻¹
          • ∑ j ∈ Finset.range m,
            ((H + t₀ • X) ^ j * X
              * ((H + t₀ • X) ^ (m - 1 - j) * C)).trace) :=
    (ContinuousLinearMap.map_tsum
      ((ContinuousLinearMap.smulRightL ℝ ℝ ℂ)
        (1 : ℝ →L[ℝ] ℝ)) hvsum).symm
  rw [hswap] at hmain
  have hd := hmain.hasDerivAt
  rw [show (ContinuousLinearMap.toSpanSingleton ℝ
      (∑' m : ℕ, ((m.factorial : ℂ))⁻¹
        • ∑ j ∈ Finset.range m,
          ((H + t₀ • X) ^ j * X
            * ((H + t₀ • X) ^ (m - 1 - j) * C)).trace))
      (1 : ℝ)
    = ∑' m : ℕ, ((m.factorial : ℂ))⁻¹
        • ∑ j ∈ Finset.range m,
          ((H + t₀ • X) ^ j * X
            * ((H + t₀ • X) ^ (m - 1 - j) * C)).trace
    from by
      rw [ContinuousLinearMap.toSpanSingleton_apply,
        one_smul]] at hd
  exact hd

omit [Nonempty n] in
/-- Trace cyclicity collapses the Leibniz sum when the fixed
factor is `1`. -/
theorem cyclic_collapse (H X : Matrix n n ℂ) (m : ℕ) :
    (∑ j ∈ Finset.range m,
      (H ^ j * X * (H ^ (m - 1 - j) * 1)).trace)
    = (m : ℂ) * (H ^ (m - 1) * X).trace := by
  have hterm : ∀ j ∈ Finset.range m,
      (H ^ j * X * (H ^ (m - 1 - j) * 1)).trace
        = (H ^ (m - 1) * X).trace := by
    intro j hj
    have hjm := Finset.mem_range.mp hj
    rw [Matrix.mul_one, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, ← pow_add,
      show m - 1 - j + j = m - 1 from by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]

/-- **First-derivative collapse**:
`d/dt Tr exp(H + tX) |₀ = Tr(exp(H) X)`. -/
theorem hasDerivAt_traceExp (H X : Matrix n n ℂ) :
    HasDerivAt
      (fun t : ℝ => (NormedSpace.exp (H + t • X)).trace)
      ((NormedSpace.exp H * X).trace) 0 := by
  have h0 := hasDerivAt_traceExpMul H X 1 0
    (by constructor <;> norm_num)
  have hfun : (fun t : ℝ =>
      ((NormedSpace.exp (H + t • X)) * 1).trace)
      = fun t : ℝ =>
        (NormedSpace.exp (H + t • X)).trace := by
    funext t
    rw [Matrix.mul_one]
  rw [hfun] at h0
  have hH0 : H + (0:ℝ) • X = H := by
    rw [zero_smul, add_zero]
  rw [hH0] at h0
  have hsummable : Summable (fun m : ℕ =>
      ((m.factorial : ℂ))⁻¹ * ((m : ℂ)
        * (H ^ (m - 1) * X).trace)) := by
    refine Summable.of_norm_bounded
      (g := uBound H X 1) (uBound_summable H X 1) ?_
    intro m
    rw [← cyclic_collapse H X m, ← smul_eq_mul,
      norm_smul, norm_inv_factorial]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hb := leibniz_term_bound H X 1 m 0
      (by norm_num)
    rw [show H + (0:ℝ) • X = H from by
      rw [zero_smul, add_zero]] at hb
    exact hb
  have hval : (∑' m : ℕ, ((m.factorial : ℂ))⁻¹
      • ∑ j ∈ Finset.range m,
        (H ^ j * X * (H ^ (m - 1 - j) * 1)).trace)
      = (NormedSpace.exp H * X).trace := by
    have hcongr : ∀ m : ℕ, ((m.factorial : ℂ))⁻¹
        • ∑ j ∈ Finset.range m,
          (H ^ j * X * (H ^ (m - 1 - j) * 1)).trace
        = ((m.factorial : ℂ))⁻¹ * ((m : ℂ)
          * (H ^ (m - 1) * X).trace) := by
      intro m
      rw [cyclic_collapse H X m, smul_eq_mul]
    rw [tsum_congr hcongr, hsummable.tsum_eq_zero_add]
    have hzero : ((Nat.factorial 0 : ℂ))⁻¹ * (((0:ℕ) : ℂ)
        * (H ^ (0 - 1) * X).trace) = 0 := by
      norm_num
    rw [hzero, zero_add]
    have hshift : ∀ k : ℕ,
        (((k + 1).factorial : ℂ))⁻¹ * (((k + 1 : ℕ) : ℂ)
          * (H ^ (k + 1 - 1) * X).trace)
        = ((k.factorial : ℂ))⁻¹
          • ((H ^ k * X).trace) := by
      intro k
      rw [Nat.add_sub_cancel, Nat.factorial_succ,
        smul_eq_mul]
      have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      have hkf : ((k.factorial : ℂ)) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      push_cast
      field_simp
    rw [tsum_congr hshift, ← traceExpMul_eq_tsum H X]
  rw [hval] at h0
  exact h0

/-- The Duhamel/BKM kernel in series form:
`∑ (m!)⁻¹ ∑_{a+b=m-1} Tr(Hᵃ Y Hᵇ X)`. -/
noncomputable def bkmSeries (H Y X : Matrix n n ℂ) : ℂ :=
  ∑' m : ℕ, ((m.factorial : ℂ))⁻¹
    • ∑ j ∈ Finset.range m,
      (H ^ j * Y * (H ^ (m - 1 - j) * X)).trace

/-- **The mixed second derivative**: the derivative of
`u ↦ Tr(exp(H + uY) X)` at `0` is the Duhamel/BKM series. -/
theorem hasDerivAt_traceExpMul_zero (H Y X : Matrix n n ℂ) :
    HasDerivAt
      (fun u : ℝ => ((NormedSpace.exp (H + u • Y))
        * X).trace)
      (bkmSeries H Y X) 0 := by
  have h0 := hasDerivAt_traceExpMul H Y X 0
    (by constructor <;> norm_num)
  rw [show H + (0:ℝ) • Y = H from by
    rw [zero_smul, add_zero]] at h0
  exact h0

/-! ### The spectral form of the BKM kernel -/

omit [DecidableEq n] [Nonempty n] in
/-- Trace of a doubly conjugated sandwich reduces to the
conjugated observables. -/
theorem trace_conj_sandwich (U D E A B : Matrix n n ℂ) :
    ((U * D * Uᴴ) * A * ((U * E * Uᴴ) * B)).trace
      = (D * ((Uᴴ * A * U) * (E * ((Uᴴ * B) * U)))).trace := by
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm U]
  simp only [Matrix.mul_assoc]

omit [Nonempty n] in
/-- Conjugated powers. -/
theorem conj_pow (U D : Matrix n n ℂ) (hU : U * Uᴴ = 1)
    (hU' : Uᴴ * U = 1) (k : ℕ) :
    (U * D * Uᴴ) ^ k = U * D ^ k * Uᴴ := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.mul_one]
    exact hU.symm
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc U * D ^ k * Uᴴ * (U * D * Uᴴ)
        = U * D ^ k * ((Uᴴ * U) * (D * Uᴴ)) := by
          simp only [Matrix.mul_assoc]
      _ = U * (D ^ k * D) * Uᴴ := by
          rw [hU', Matrix.one_mul]
          simp only [Matrix.mul_assoc]

omit [Nonempty n] in
/-- Conjugated exponentials. -/
theorem conj_exp (U D : Matrix n n ℂ) (hU : U * Uᴴ = 1) :
    NormedSpace.exp (U * D * Uᴴ)
      = U * NormedSpace.exp D * Uᴴ := by
  have hUinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv hU
  have hUnit : IsUnit U :=
    (Matrix.isUnit_iff_isUnit_det U).mpr
      (Matrix.isUnit_det_of_right_inverse hU)
  rw [← hUinv, Matrix.exp_conj U D hUnit]

omit [Nonempty n] in
/-- Left multiplication by a diagonal matrix, entrywise. -/
theorem diag_mul_apply (v : n → ℂ) (M : Matrix n n ℂ)
    (i j : n) :
    ((Matrix.diagonal v) * M) i j = v i * M i j := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single i
      (fun k _ hk => by
        rw [Matrix.diagonal_apply_ne v (Ne.symm hk),
          zero_mul])
      (fun h => absurd (Finset.mem_univ i) h),
    Matrix.diagonal_apply_eq]

omit [Nonempty n] in
/-- Diagonal sandwich trace as a double sum. -/
theorem trace_diag_sandwich (d e : n → ℂ)
    (A B : Matrix n n ℂ) :
    ((Matrix.diagonal d) * A
      * ((Matrix.diagonal e) * B)).trace
    = ∑ i : n, ∑ j : n, d i * A i j * (e j * B j i) := by
  simp only [Matrix.trace, Matrix.diag]
  have houter : ∀ i : n,
      ((Matrix.diagonal d * A)
        * (Matrix.diagonal e * B)) i i
      = ∑ j : n, (d i * A i j) * (e j * B j i) := by
    intro i
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => by
      rw [diag_mul_apply d A, diag_mul_apply e B]
  rw [Finset.sum_congr rfl fun i _ => houter i]

/-! ### The scalar Duhamel kernel -/

/-- Summability of the scalar geometric-factorial series. -/
theorem scalar_geom_summable (x y : ℝ) :
    Summable (fun m : ℕ => ((m.factorial : ℝ))⁻¹
      * ∑ j ∈ Finset.range m, x ^ j * y ^ (m - 1 - j)) := by
  set c : ℝ := |x| + |y| + 1 with hc
  have hc1 : 1 ≤ c := by
    have := abs_nonneg x
    have := abs_nonneg y
    linarith
  have hxc : |x| ≤ c := by
    have := abs_nonneg y
    linarith
  have hyc : |y| ≤ c := by
    have := abs_nonneg x
    linarith
  refine Summable.of_norm_bounded
    (g := fun m : ℕ => ((m.factorial : ℝ))⁻¹
      * ((m : ℝ) * c ^ (m - 1))) ?_ ?_
  · rw [← summable_nat_add_iff 1]
    have hs := (Real.summable_pow_div_factorial c).mul_left 1
    refine hs.congr fun k => ?_
    simp only [Nat.add_sub_cancel]
    have hfact : ((k + 1).factorial : ℝ)
        = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfact]
    have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hkf : ((k.factorial : ℝ)) ≠ 0 := by positivity
    field_simp
  · intro m
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity :
        (0:ℝ) ≤ ((m.factorial : ℝ))⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |∑ j ∈ Finset.range m, x ^ j * y ^ (m - 1 - j)|
        ≤ ∑ j ∈ Finset.range m, |x ^ j * y ^ (m - 1 - j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range m, c ^ (m - 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjm := Finset.mem_range.mp hj
          rw [abs_mul, abs_pow, abs_pow]
          calc |x| ^ j * |y| ^ (m - 1 - j)
              ≤ c ^ j * c ^ (m - 1 - j) := by
                gcongr
            _ = c ^ (j + (m - 1 - j)) := by rw [pow_add]
            _ ≤ c ^ (m - 1) :=
                pow_le_pow_right₀ hc1 (by omega)
      _ = (m : ℝ) * c ^ (m - 1) := by
          rw [Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]

/-- **The scalar Duhamel identity**:
`∑ (m!)⁻¹ ∑_{a+b=m-1} xᵃ yᵇ = ∫₀¹ e^{sx+(1-s)y} ds`. -/
theorem scalar_bkm (x y : ℝ) :
    (∑' m : ℕ, ((m.factorial : ℝ))⁻¹
      * ∑ j ∈ Finset.range m, x ^ j * y ^ (m - 1 - j))
    = ∫ s in (0:ℝ)..1, Real.exp (s * x + (1 - s) * y) := by
  have hexp : ∀ z : ℝ,
      Real.exp z = ∑' m : ℕ, z ^ m / (m.factorial : ℝ) := by
    intro z
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsummexp : ∀ z : ℝ,
      Summable (fun m : ℕ => z ^ m / (m.factorial : ℝ)) :=
    fun z => Real.summable_pow_div_factorial z
  by_cases hxy : x = y
  · subst hxy
    have hcongr : ∀ m : ℕ, ((m.factorial : ℝ))⁻¹
        * ∑ j ∈ Finset.range m, x ^ j * x ^ (m - 1 - j)
        = ((m.factorial : ℝ))⁻¹
          * ((m : ℝ) * x ^ (m - 1)) := by
      intro m
      congr 1
      have hj' : ∀ j ∈ Finset.range m,
          x ^ j * x ^ (m - 1 - j) = x ^ (m - 1) := by
        intro j hj
        have hjm := Finset.mem_range.mp hj
        rw [← pow_add,
          show j + (m - 1 - j) = m - 1 from by omega]
      rw [Finset.sum_congr rfl hj', Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
    rw [tsum_congr hcongr]
    have hsum : Summable (fun m : ℕ =>
        ((m.factorial : ℝ))⁻¹
          * ((m : ℝ) * x ^ (m - 1))) :=
      (scalar_geom_summable x x).congr hcongr
    rw [hsum.tsum_eq_zero_add]
    have hz : ((Nat.factorial 0 : ℝ))⁻¹
        * (((0:ℕ) : ℝ) * x ^ (0 - 1)) = 0 := by
      norm_num
    rw [hz, zero_add]
    have hshift : ∀ k : ℕ,
        (((k + 1).factorial : ℝ))⁻¹
          * (((k + 1 : ℕ) : ℝ) * x ^ (k + 1 - 1))
        = x ^ k / (k.factorial : ℝ) := by
      intro k
      rw [Nat.add_sub_cancel, Nat.factorial_succ]
      have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hkf : ((k.factorial : ℝ)) ≠ 0 := by positivity
      push_cast
      field_simp
    rw [tsum_congr hshift, ← hexp x]
    have hint : Set.EqOn
        (fun s : ℝ => Real.exp (s * x + (1 - s) * x))
        (fun _ : ℝ => Real.exp x) (Set.uIcc (0:ℝ) 1) := by
      intro s _
      change Real.exp (s * x + (1 - s) * x) = Real.exp x
      congr 1
      ring
    rw [intervalIntegral.integral_congr hint,
      intervalIntegral.integral_const]
    norm_num
  · have hc : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hterm : ∀ m : ℕ,
        (((m.factorial : ℝ))⁻¹
          * ∑ j ∈ Finset.range m, x ^ j * y ^ (m - 1 - j))
          * (x - y)
        = x ^ m / (m.factorial : ℝ)
          - y ^ m / (m.factorial : ℝ) := by
      intro m
      rw [mul_assoc, geom_sum₂_mul, mul_sub,
        inv_mul_eq_div, inv_mul_eq_div]
    have hL : (∑' m : ℕ, ((m.factorial : ℝ))⁻¹
        * ∑ j ∈ Finset.range m, x ^ j * y ^ (m - 1 - j))
        * (x - y) = Real.exp x - Real.exp y := by
      rw [← tsum_mul_right, tsum_congr hterm,
        (hsummexp x).tsum_sub (hsummexp y), ← hexp x,
        ← hexp y]
    have hLval : (∑' m : ℕ, ((m.factorial : ℝ))⁻¹
        * ∑ j ∈ Finset.range m, x ^ j * y ^ (m - 1 - j))
        = (Real.exp x - Real.exp y) / (x - y) := by
      rw [eq_div_iff hc]
      exact hL
    rw [hLval]
    have hint : Set.EqOn
        (fun s : ℝ => Real.exp (s * x + (1 - s) * y))
        (fun s : ℝ => Real.exp y
          * Real.exp ((x - y) * s)) (Set.uIcc (0:ℝ) 1) := by
      intro s _
      change Real.exp (s * x + (1 - s) * y)
        = Real.exp y * Real.exp ((x - y) * s)
      rw [← Real.exp_add]
      congr 1
      ring
    rw [intervalIntegral.integral_congr hint,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left Real.exp hc,
      integral_exp, smul_eq_mul, mul_one, mul_zero,
      Real.exp_zero]
    rw [Real.exp_sub]
    have hey : Real.exp y ≠ 0 := Real.exp_ne_zero y
    field_simp

/-! ### The BKM series as a Duhamel integral -/

omit [Nonempty n] in
/-- The diagonal case of the BKM/Duhamel identity: for a real
diagonal `diag d`, the BKM series against `P, Q` equals the
Duhamel integral of the diagonal sandwich. -/
theorem bkm_diag_integral (dr : n → ℝ) (P Q : Matrix n n ℂ) :
    (∑' m : ℕ, ((m.factorial : ℂ))⁻¹
      • ∑ j ∈ Finset.range m,
          ((Matrix.diagonal fun i => (dr i : ℂ)) ^ j * P
            * ((Matrix.diagonal fun i => (dr i : ℂ)) ^ (m - 1 - j)
              * Q)).trace)
    = ∫ s in (0:ℝ)..1,
        ((Matrix.diagonal
            fun i => Complex.exp ((s * dr i : ℝ) : ℂ)) * P
          * ((Matrix.diagonal
              fun i => Complex.exp (((1 - s) * dr i : ℝ) : ℂ))
            * Q)).trace := by
  have hterm : ∀ m j : ℕ,
      ((Matrix.diagonal fun i => (dr i : ℂ)) ^ j * P
        * ((Matrix.diagonal fun i => (dr i : ℂ)) ^ (m - 1 - j)
          * Q)).trace
      = ∑ i : n, ∑ k : n, (dr i : ℂ) ^ j * P i k
          * ((dr k : ℂ) ^ (m - 1 - j) * Q k i) := by
    intro m j
    rw [Matrix.diagonal_pow, Matrix.diagonal_pow,
      trace_diag_sandwich]
    simp only [Pi.pow_apply]
  have hm : ∀ m : ℕ,
      ((m.factorial : ℂ))⁻¹
        • ∑ j ∈ Finset.range m,
            ((Matrix.diagonal fun i => (dr i : ℂ)) ^ j * P
              * ((Matrix.diagonal
                  fun i => (dr i : ℂ)) ^ (m - 1 - j)
                * Q)).trace
      = ∑ i : n, ∑ k : n,
          ((((m.factorial : ℝ))⁻¹
            * ∑ j ∈ Finset.range m,
                dr i ^ j * dr k ^ (m - 1 - j) : ℝ) : ℂ)
            * (P i k * Q k i) := by
    intro m
    rw [Finset.sum_congr rfl fun j _ => hterm m j,
      Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul]
    push_cast
    rw [mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsum : ∀ i k : n,
      Summable (fun m : ℕ =>
        ((((m.factorial : ℝ))⁻¹
          * ∑ j ∈ Finset.range m,
              dr i ^ j * dr k ^ (m - 1 - j) : ℝ) : ℂ)
          * (P i k * Q k i)) := fun i k =>
    (Complex.summable_ofReal.mpr
      (scalar_geom_summable (dr i) (dr k))).mul_right _
  have hc1 : ∀ i k : n, Continuous (fun s : ℝ =>
      Complex.exp ((s * dr i : ℝ) : ℂ) * P i k
        * (Complex.exp (((1 - s) * dr k : ℝ) : ℂ)
          * Q k i)) := by
    intro i k
    fun_prop
  have hc2 : ∀ i : n, Continuous (fun s : ℝ =>
      ∑ k : n, Complex.exp ((s * dr i : ℝ) : ℂ) * P i k
        * (Complex.exp (((1 - s) * dr k : ℝ) : ℂ)
          * Q k i)) :=
    fun i => continuous_finsetSum _ fun k _ => hc1 i k
  have hs : ∀ (i k : n) (s : ℝ),
      Complex.exp ((s * dr i : ℝ) : ℂ) * P i k
        * (Complex.exp (((1 - s) * dr k : ℝ) : ℂ) * Q k i)
      = (P i k * Q k i)
        * ((Real.exp (s * dr i + (1 - s) * dr k) : ℝ) : ℂ) := by
    intro i k s
    rw [Complex.ofReal_exp, Complex.ofReal_add,
      Complex.exp_add]
    ring
  have hR : (∫ s in (0:ℝ)..1,
      ((Matrix.diagonal
          fun i => Complex.exp ((s * dr i : ℝ) : ℂ)) * P
        * ((Matrix.diagonal
            fun i => Complex.exp (((1 - s) * dr i : ℝ) : ℂ))
          * Q)).trace)
      = ∑ i : n, ∑ k : n,
          ((∫ s in (0:ℝ)..1,
            Real.exp (s * dr i + (1 - s) * dr k) : ℝ) : ℂ)
            * (P i k * Q k i) := by
    simp only [trace_diag_sandwich]
    rw [intervalIntegral.integral_finsetSum
      (fun i _ => (hc2 i).intervalIntegrable 0 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum
      (fun k _ => (hc1 i k).intervalIntegrable 0 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hs i k]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal]
    exact mul_comm _ _
  refine Eq.trans (tsum_congr hm) ?_
  refine Eq.trans (Summable.tsum_finsetSum
    (fun i _ => summable_sum fun k _ => hsum i k)) ?_
  refine Eq.trans (Finset.sum_congr rfl fun i _ =>
    Summable.tsum_finsetSum (fun k _ => hsum i k)) ?_
  refine Eq.trans (Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun k _ => ?_) hR.symm
  rw [tsum_mul_right, ← Complex.ofReal_tsum, scalar_bkm]

omit [Nonempty n] in
/-- The eigenvector unitary is a left inverse. -/
theorem eigenvectorUnitary_conjTranspose_mul
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ
      * (hH.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
  UnitaryGroup.star_mul_self hH.eigenvectorUnitary

omit [Nonempty n] in
/-- The eigenvector unitary is a right inverse. -/
theorem eigenvectorUnitary_mul_conjTranspose
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix n n ℂ)
      * (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 :=
  mul_eq_one_comm.mp
    (eigenvectorUnitary_conjTranspose_mul H hH)

omit [Nonempty n] in
/-- Spectral decomposition in explicit sandwich form. -/
theorem hermitian_spectral (H : Matrix n n ℂ)
    (hH : H.IsHermitian) :
    H = (hH.eigenvectorUnitary : Matrix n n ℂ)
        * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
        * (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have h := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

omit [Nonempty n] in
/-- Real powers of a Hermitian exponential in eigenbasis form:
`exp(cH) = U diag(e^{cλᵢ}) Uᴴ`. -/
theorem exp_smul_hermitian (H : Matrix n n ℂ)
    (hH : H.IsHermitian) (c : ℝ) :
    NormedSpace.exp (c • H)
      = (hH.eigenvectorUnitary : Matrix n n ℂ)
          * Matrix.diagonal (fun i =>
              Complex.exp ((c * hH.eigenvalues i : ℝ) : ℂ))
          * (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have hD : Matrix.diagonal
      (fun i => ((c * hH.eigenvalues i : ℝ) : ℂ))
      = c • Matrix.diagonal
          (fun i => (hH.eigenvalues i : ℂ)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp [Complex.real_smul, Complex.ofReal_mul]
  have h1 : c • H = (hH.eigenvectorUnitary : Matrix n n ℂ)
      * Matrix.diagonal
        (fun i => ((c * hH.eigenvalues i : ℝ) : ℂ))
      * (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    conv_lhs => rw [hermitian_spectral H hH]
    rw [hD, Matrix.mul_smul, Matrix.smul_mul]
  rw [h1, conj_exp _ _
    (eigenvectorUnitary_mul_conjTranspose H hH),
    Matrix.exp_diagonal]
  have h2 : NormedSpace.exp
      (fun i => ((c * hH.eigenvalues i : ℝ) : ℂ))
      = fun i =>
          Complex.exp ((c * hH.eigenvalues i : ℝ) : ℂ) := by
    funext i
    exact (Pi.coe_exp _ i).trans
      (congrFun Complex.exp_eq_exp_ℂ
        ((c * hH.eigenvalues i : ℝ) : ℂ)).symm
  rw [h2]

omit [Nonempty n] in
/-- **The BKM/Duhamel integral representation**: for Hermitian
`H`, the BKM series equals the Duhamel integral
`∫₀¹ Tr(e^{sH} Y e^{(1-s)H} X) ds`. -/
theorem bkmSeries_eq_integral (H Y X : Matrix n n ℂ)
    (hH : H.IsHermitian) :
    bkmSeries H Y X
      = ∫ s in (0:ℝ)..1,
          ((NormedSpace.exp (s • H)) * Y
            * ((NormedSpace.exp ((1 - s) • H)) * X)).trace := by
  obtain ⟨U, dr, hU, hU', hspec⟩ :
      ∃ (U : Matrix n n ℂ) (dr : n → ℝ),
        U * Uᴴ = 1 ∧ Uᴴ * U = 1
          ∧ H = U * Matrix.diagonal (fun i => (dr i : ℂ))
              * Uᴴ :=
    ⟨hH.eigenvectorUnitary, hH.eigenvalues,
      mul_eq_one_comm.mp
        (UnitaryGroup.star_mul_self hH.eigenvectorUnitary),
      UnitaryGroup.star_mul_self hH.eigenvectorUnitary,
      by
        have h := hH.spectral_theorem
        rw [Unitary.conjStarAlgAut_apply] at h
        exact h⟩
  have hpow : ∀ k : ℕ, H ^ k
      = U * (Matrix.diagonal fun i => (dr i : ℂ)) ^ k
          * Uᴴ := by
    intro k
    rw [hspec]
    exact conj_pow U _ hU hU' k
  have hterm : ∀ a b : ℕ,
      (H ^ a * Y * (H ^ b * X)).trace
      = ((Matrix.diagonal fun i => (dr i : ℂ)) ^ a
          * (Uᴴ * Y * U)
          * ((Matrix.diagonal fun i => (dr i : ℂ)) ^ b
            * (Uᴴ * X * U))).trace := by
    intro a b
    rw [hpow, hpow, trace_conj_sandwich]
    congr 1
    simp only [Matrix.mul_assoc]
  have hexp : ∀ c : ℝ,
      NormedSpace.exp (c • H)
        = U * Matrix.diagonal
            (fun i => Complex.exp ((c * dr i : ℝ) : ℂ))
          * Uᴴ := by
    intro c
    have hD : Matrix.diagonal
        (fun i => ((c * dr i : ℝ) : ℂ))
        = c • Matrix.diagonal (fun i => (dr i : ℂ)) := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      simp [Complex.real_smul, Complex.ofReal_mul]
    have h1 : c • H = U * Matrix.diagonal
        (fun i => ((c * dr i : ℝ) : ℂ)) * Uᴴ := by
      rw [hspec, hD, Matrix.mul_smul, Matrix.smul_mul]
    rw [h1, conj_exp U _ hU, Matrix.exp_diagonal]
    have h2 : NormedSpace.exp
        (fun i => ((c * dr i : ℝ) : ℂ))
        = fun i => Complex.exp ((c * dr i : ℝ) : ℂ) := by
      funext i
      exact (Pi.coe_exp _ i).trans
        (congrFun Complex.exp_eq_exp_ℂ
          ((c * dr i : ℝ) : ℂ)).symm
    rw [h2]
  have hintg : ∀ s : ℝ,
      ((NormedSpace.exp (s • H)) * Y
        * ((NormedSpace.exp ((1 - s) • H)) * X)).trace
      = ((Matrix.diagonal
            fun i => Complex.exp ((s * dr i : ℝ) : ℂ))
          * (Uᴴ * Y * U)
          * ((Matrix.diagonal
              fun i => Complex.exp (((1 - s) * dr i : ℝ) : ℂ))
            * (Uᴴ * X * U))).trace := by
    intro s
    rw [hexp s, hexp (1 - s), trace_conj_sandwich]
    congr 1
    simp only [Matrix.mul_assoc]
  have hLHS : bkmSeries H Y X
      = ∑' m : ℕ, ((m.factorial : ℂ))⁻¹
          • ∑ j ∈ Finset.range m,
              ((Matrix.diagonal fun i => (dr i : ℂ)) ^ j
                * (Uᴴ * Y * U)
                * ((Matrix.diagonal
                    fun i => (dr i : ℂ)) ^ (m - 1 - j)
                  * (Uᴴ * X * U))).trace :=
    tsum_congr fun m =>
      congrArg (fun z => ((m.factorial : ℂ))⁻¹ • z)
        (Finset.sum_congr rfl fun j _ =>
          hterm j (m - 1 - j))
  rw [hLHS, bkm_diag_integral dr (Uᴴ * Y * U) (Uᴴ * X * U)]
  exact intervalIntegral.integral_congr
    fun s _ => (hintg s).symm

end TraceExp
end NCG
