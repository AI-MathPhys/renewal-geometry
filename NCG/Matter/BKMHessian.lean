/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Gravity.VolterraML

/-!
# The BKM path curvature (`thm:bkm-hessian`, SM_emergence)

Duhamel/trace-exponential derivative calculus on a finite matrix
factor, built from scratch (Mathlib has no noncommutative
exponential-derivative calculus):

* `hasDerivAt_path_pow` / `hasDerivAt_trace_pow` — the product-rule
  derivative of `t ↦ (A + tB)^m` and its cyclic trace collapse
  `d/dt Tr(A+tB)^m = m·Tr((A+tB)^{m-1}B)`.

Later sections add the exponential-series exchanges, the
Beta-function evaluation of the BKM integral, positivity, and the
assembled `ψ''(0)` identity.
-/

namespace NCG.BKM

open Matrix NormedSpace

open scoped Norms.Operator ComplexOrder

noncomputable section

variable {d : ℕ}

/-- Trace as a continuous `ℝ`-linear functional. -/
private def traceCLM : Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap (Fin d) ℂ ℂ).restrictScalars ℝ)

private lemma traceCLM_apply (X : Matrix (Fin d) (Fin d) ℂ) :
    traceCLM X = Matrix.trace X := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma hasDerivAt_path (A B : Matrix (Fin d) (Fin d) ℂ) (q : ℝ) :
    HasDerivAt (fun t : ℝ => A + t • B) B q := by
  have h1 : HasDerivAt (fun t : ℝ => t • B) B q := by
    simpa using (hasDerivAt_id q).smul_const B
  exact h1.const_add A

set_option backward.isDefEq.respectTransparency false in
private lemma hasDerivAt_path_pow (A B : Matrix (Fin d) (Fin d) ℂ)
    (m : ℕ) (q : ℝ) :
    HasDerivAt (fun t : ℝ => (A + t • B) ^ m)
      (∑ k ∈ Finset.range m,
        (A + q • B) ^ k * B * (A + q • B) ^ (m - 1 - k)) q := by
  induction m with
  | zero =>
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty]
    exact hasDerivAt_const q 1
  | succ m ih =>
    have hmul := (hasDerivAt_path A B q).mul ih
    rw [show ((fun t : ℝ => A + t • B) * fun t : ℝ => (A + t • B) ^ m)
        = fun t : ℝ => (A + t • B) ^ (m + 1) from
      funext fun t => by rw [Pi.mul_apply, ← pow_succ']] at hmul
    have hterm : ∀ k ∈ Finset.range m,
        (A + q • B) ^ (k + 1) * B * (A + q • B) ^ (m + 1 - 1 - (k + 1))
          = (A + q • B) * ((A + q • B) ^ k * B
              * (A + q • B) ^ (m - 1 - k)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← pow_succ']
      congr 2
      omega
    refine hmul.congr_deriv ?_
    rw [Finset.mul_sum, Finset.sum_range_succ', Finset.sum_congr rfl hterm]
    have h0 : (A + q • B) ^ 0 * B * (A + q • B) ^ (m + 1 - 1 - 0)
        = B * (A + q • B) ^ m := by
      rw [pow_zero, Matrix.one_mul]
      norm_num
    rw [h0]
    exact add_comm _ _

set_option backward.isDefEq.respectTransparency false in
private lemma hasDerivAt_trace_pow (A B : Matrix (Fin d) (Fin d) ℂ)
    (m : ℕ) (q : ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.trace ((A + t • B) ^ m))
      ((m : ℂ) * Matrix.trace ((A + q • B) ^ (m - 1) * B)) q := by
  have h := (traceCLM.hasFDerivAt).comp_hasDerivAt q
    (hasDerivAt_path_pow A B m q)
  have hval : traceCLM (∑ k ∈ Finset.range m,
      (A + q • B) ^ k * B * (A + q • B) ^ (m - 1 - k))
      = (m : ℂ) * Matrix.trace ((A + q • B) ^ (m - 1) * B) := by
    rw [map_sum]
    have hterm : ∀ k ∈ Finset.range m,
        traceCLM ((A + q • B) ^ k * B * (A + q • B) ^ (m - 1 - k))
          = Matrix.trace ((A + q • B) ^ (m - 1) * B) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [traceCLM_apply, Matrix.trace_mul_cycle, ← pow_add]
      have hexp : m - 1 - k + k = m - 1 := by omega
      rw [hexp]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  rw [← hval]
  exact h

/-! ## The exponential series of the tilted trace -/

set_option backward.isDefEq.respectTransparency false in
private lemma exp_series (M : Matrix (Fin d) (Fin d) ℂ) :
    exp M = ∑' m : ℕ, ((m.factorial : ℂ))⁻¹ • M ^ m :=
  congrFun (exp_eq_tsum (𝕂 := ℂ)) M

set_option backward.isDefEq.respectTransparency false in
private lemma exp_summable (M : Matrix (Fin d) (Fin d) ℂ) :
    Summable fun m : ℕ => ((m.factorial : ℂ))⁻¹ • M ^ m :=
  expSeries_summable' (𝕂 := ℂ) M

private lemma trace_exp_eq_tsum (M : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (exp M)
      = ∑' m : ℕ, ((m.factorial : ℂ))⁻¹ * Matrix.trace (M ^ m) := by
  rw [← traceCLM_apply, exp_series,
    ContinuousLinearMap.map_tsum traceCLM (exp_summable M)]
  exact tsum_congr fun m => by
    rw [traceCLM_apply, Matrix.trace_smul, smul_eq_mul]

private lemma trace_summable (M : Matrix (Fin d) (Fin d) ℂ) :
    Summable fun m : ℕ =>
      ((m.factorial : ℂ))⁻¹ * Matrix.trace (M ^ m) := by
  have h := ((exp_summable M).map traceCLM.toLinearMap.toAddMonoidHom
    traceCLM.continuous)
  refine h.congr fun m => ?_
  simp only [Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    ContinuousLinearMap.coe_coe]
  rw [traceCLM_apply, Matrix.trace_smul, smul_eq_mul]

/-- `X ↦ Tr(X·C)` as a continuous `ℝ`-linear functional. -/
private def traceMulCLM (C : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Matrix.trace (X * C)
      map_add' := fun X Y => by rw [Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun r X => by
        rw [smul_mul_assoc, Matrix.trace_smul, RingHom.id_apply] }

private lemma traceMulCLM_apply (C X : Matrix (Fin d) (Fin d) ℂ) :
    traceMulCLM C X = Matrix.trace (X * C) := rfl

/-- The trace-norm constant. -/
private def trC (d : ℕ) : ℝ := d

private lemma trC_nonneg : 0 ≤ trC d := Nat.cast_nonneg d

set_option backward.isDefEq.respectTransparency false in
private lemma trace_norm_le (X : Matrix (Fin d) (Fin d) ℂ) :
    ‖Matrix.trace X‖ ≤ trC d * ‖X‖ := by
  have hentry : ∀ i : Fin d, ‖X i i‖ ≤ ‖X‖ := by
    intro i
    have h1 : ‖X i i‖₊ ≤ ‖X‖₊ := by
      rw [Matrix.linfty_opNNNorm_def]
      calc ‖X i i‖₊ ≤ ∑ j : Fin d, ‖X i j‖₊ :=
            Finset.single_le_sum (f := fun j => ‖X i j‖₊)
              (fun j _ => zero_le) (Finset.mem_univ i)
      _ ≤ _ := Finset.le_sup (f := fun i => ∑ j : Fin d, ‖X i j‖₊)
            (Finset.mem_univ i)
    exact_mod_cast h1
  calc ‖Matrix.trace X‖ ≤ ∑ i : Fin d, ‖X i i‖ :=
        norm_sum_le _ _
  _ ≤ ∑ _i : Fin d, ‖X‖ := Finset.sum_le_sum fun i _ => hentry i
  _ = trC d * ‖X‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, trC]

set_option backward.isDefEq.respectTransparency false in
private lemma path_norm_le (A B : Matrix (Fin d) (Fin d) ℂ) {t : ℝ}
    (ht : |t| ≤ 1) : ‖A + t • B‖ ≤ ‖A‖ + ‖B‖ := by
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg B) ht

set_option backward.isDefEq.respectTransparency false in
private lemma norm_pow_path (X : Matrix (Fin d) (Fin d) ℂ) (j : ℕ)
    {K : ℝ} (hX : ‖X‖ ≤ K) (hK : 0 ≤ K) : ‖X ^ j‖ ≤ K ^ j := by
  induction j with
  | zero =>
    simp only [pow_zero]
    have h1 : ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖₊ ≤ 1 := by
      rw [Matrix.linfty_opNNNorm_def]
      refine Finset.sup_le fun i _ => ?_
      have hone : ∀ j : Fin d,
          ‖(1 : Matrix (Fin d) (Fin d) ℂ) i j‖₊
            = if i = j then 1 else 0 := by
        intro j
        rw [Matrix.one_apply, apply_ite nnnorm, nnnorm_one, nnnorm_zero]
      rw [Finset.sum_congr rfl fun j _ => hone j, Finset.sum_ite_eq,
        if_pos (Finset.mem_univ i)]
    exact_mod_cast h1
  | succ j ih =>
    calc ‖X ^ (j + 1)‖ = ‖X ^ j * X‖ := by rw [pow_succ]
    _ ≤ ‖X ^ j‖ * ‖X‖ := norm_mul_le _ _
    _ ≤ K ^ j * K :=
        mul_le_mul ih hX (norm_nonneg _) (pow_nonneg hK j)
    _ = K ^ (j + 1) := (pow_succ K j).symm

set_option backward.isDefEq.respectTransparency false in
private lemma pow_mul_norm_le (A B : Matrix (Fin d) (Fin d) ℂ) {t : ℝ}
    (ht : |t| ≤ 1) (j : ℕ) :
    ‖(A + t • B) ^ j * B‖ ≤ (‖A‖ + ‖B‖) ^ j * ‖B‖ := by
  refine (norm_mul_le _ _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg B)
  exact norm_pow_path _ j (path_norm_le A B ht) (by positivity)

/-! ## First derivative: `F'(q) = Tr(exp(A+qB)·B)` -/

/-- The derivative-series bound. -/
private def ubound (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) : ℝ :=
  m * (m.factorial : ℝ)⁻¹ * (trC d * ((‖A‖ + ‖B‖) ^ (m - 1) * ‖B‖))

private lemma ubound_summable (A B : Matrix (Fin d) (Fin d) ℂ) :
    Summable (ubound d A B) := by
  rw [← summable_nat_add_iff 1]
  have hsum := (Real.summable_pow_div_factorial (‖A‖ + ‖B‖)).mul_right
    (trC d * ‖B‖)
  refine hsum.congr fun m => ?_
  rw [ubound]
  simp only [Nat.add_sub_cancel]
  have hfac : ((m + 1).factorial : ℝ) = (m + 1) * (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ m
  have hne : ((m.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos m).ne'
  push_cast
  rw [hfac]
  field_simp

private lemma gderiv_bound (A B : Matrix (Fin d) (Fin d) ℂ) (m : ℕ)
    {t : ℝ} (ht : |t| ≤ 1) :
    ‖(m : ℂ) * ((m.factorial : ℂ))⁻¹
        * Matrix.trace ((A + t • B) ^ (m - 1) * B)‖
      ≤ ubound d A B m := by
  have h1 : ‖(m : ℂ)‖ = (m : ℝ) := by simp
  have h2 : ‖((m.factorial : ℂ))⁻¹‖ = ((m.factorial : ℝ))⁻¹ := by
    rw [norm_inv]
    congr 1
    simp
  calc ‖(m : ℂ) * ((m.factorial : ℂ))⁻¹
      * Matrix.trace ((A + t • B) ^ (m - 1) * B)‖
      = (m : ℝ) * ((m.factorial : ℝ))⁻¹
        * ‖Matrix.trace ((A + t • B) ^ (m - 1) * B)‖ := by
        rw [norm_mul, norm_mul, h1, h2]
  _ ≤ (m : ℝ) * ((m.factorial : ℝ))⁻¹
        * (trC d * ((‖A‖ + ‖B‖) ^ (m - 1) * ‖B‖)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (trace_norm_le _).trans
        (mul_le_mul_of_nonneg_left (pow_mul_norm_le A B ht (m - 1))
          trC_nonneg)
  _ = ubound d A B m := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma hasDerivAt_gcoef (A B : Matrix (Fin d) (Fin d) ℂ) (m : ℕ)
    (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ((m.factorial : ℂ))⁻¹
        * Matrix.trace ((A + s • B) ^ m))
      ((m : ℂ) * ((m.factorial : ℂ))⁻¹
        * Matrix.trace ((A + t • B) ^ (m - 1) * B)) t := by
  have h := (hasDerivAt_trace_pow A B m t).const_mul
    (((m.factorial : ℂ))⁻¹)
  exact h.congr_deriv (by ring)

set_option backward.isDefEq.respectTransparency false in
/-- The first-derivative identity on the unit ball:
`d/dq Tr exp(A+qB) = Tr(exp(A+qB)·B)`. -/
private lemma hasDerivAt_traceExp (A B : Matrix (Fin d) (Fin d) ℂ)
    {q : ℝ} (hq : q ∈ Metric.ball (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => Matrix.trace (exp (A + t • B)))
      (Matrix.trace (exp (A + q • B) * B)) q := by
  have hball : ∀ t : ℝ, t ∈ Metric.ball (0 : ℝ) 1 → |t| ≤ 1 := by
    intro t htb
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at htb
    exact htb.le
  have hder := hasDerivAt_tsum_of_isPreconnected
    (ubound_summable A B) Metric.isOpen_ball
    (convex_ball (0 : ℝ) 1).isPreconnected
    (fun m t _ => hasDerivAt_gcoef A B m t)
    (fun m t htb => gderiv_bound A B m (hball t htb))
    (Metric.mem_ball_self one_pos)
    (trace_summable (A + (0 : ℝ) • B)) hq
  have hfun : (fun t : ℝ => ∑' m : ℕ, ((m.factorial : ℂ))⁻¹
      * Matrix.trace ((A + t • B) ^ m))
      = fun t : ℝ => Matrix.trace (exp (A + t • B)) := by
    funext t
    rw [trace_exp_eq_tsum]
  rw [hfun] at hder
  refine hder.congr_deriv ?_
  set M := A + q • B with hM
  have habs : |q| ≤ 1 := hball q hq
  have hsummable : Summable (fun m : ℕ => (m : ℂ)
      * ((m.factorial : ℂ))⁻¹ * Matrix.trace (M ^ (m - 1) * B)) := by
    refine Summable.of_norm ?_
    exact (ubound_summable A B).of_nonneg_of_le
      (fun m => norm_nonneg _) (fun m => gderiv_bound A B m habs)
  have h1 : (∑' m : ℕ, (m : ℂ) * ((m.factorial : ℂ))⁻¹
      * Matrix.trace (M ^ (m - 1) * B))
      = ∑' m : ℕ, ((m.factorial : ℂ))⁻¹ * Matrix.trace (M ^ m * B) := by
    rw [hsummable.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    refine tsum_congr fun m => ?_
    simp only [Nat.add_sub_cancel]
    have hfac : (((m + 1).factorial : ℂ))
        = ((m + 1 : ℕ) : ℂ) * ((m.factorial : ℂ)) := by
      push_cast [Nat.factorial_succ]
      ring
    have hne1 : ((m + 1 : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    have hne2 : ((m.factorial : ℂ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
    rw [hfac]
    field_simp
  have h2 : (∑' m : ℕ, ((m.factorial : ℂ))⁻¹
      * Matrix.trace (M ^ m * B)) = Matrix.trace (exp M * B) := by
    rw [← traceMulCLM_apply, exp_series,
      ContinuousLinearMap.map_tsum (traceMulCLM B) (exp_summable M)]
    exact tsum_congr fun m => by
      rw [traceMulCLM_apply, smul_mul_assoc, Matrix.trace_smul,
        smul_eq_mul]
  rw [h1, h2]

/-! ## Second derivative at `0` -/

private lemma trace_exp_mul_eq_tsum (M B : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (exp M * B)
      = ∑' m : ℕ, ((m.factorial : ℂ))⁻¹ * Matrix.trace (M ^ m * B) := by
  rw [← traceMulCLM_apply, exp_series,
    ContinuousLinearMap.map_tsum (traceMulCLM B) (exp_summable M)]
  exact (tsum_congr fun m => by
    rw [traceMulCLM_apply, smul_mul_assoc, Matrix.trace_smul,
      smul_eq_mul]).symm

private lemma traceMul_summable (M B : Matrix (Fin d) (Fin d) ℂ) :
    Summable fun m : ℕ =>
      ((m.factorial : ℂ))⁻¹ * Matrix.trace (M ^ m * B) := by
  have h := ((exp_summable M).map
    (traceMulCLM B).toLinearMap.toAddMonoidHom (traceMulCLM B).continuous)
  refine h.congr fun m => ?_
  simp only [Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    ContinuousLinearMap.coe_coe]
  rw [traceMulCLM_apply, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
private lemma sum_word_norm_le (A B : Matrix (Fin d) (Fin d) ℂ) (m : ℕ)
    {t : ℝ} (ht : |t| ≤ 1) :
    ‖∑ k ∈ Finset.range m,
        (A + t • B) ^ k * B * (A + t • B) ^ (m - 1 - k)‖
      ≤ m * ((‖A‖ + ‖B‖) ^ (m - 1) * ‖B‖) := by
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range m,
      ‖(A + t • B) ^ k * B * (A + t • B) ^ (m - 1 - k)‖
        ≤ (‖A‖ + ‖B‖) ^ (m - 1) * ‖B‖ := by
    intro k hk
    rw [Finset.mem_range] at hk
    set K := ‖A‖ + ‖B‖ with hK
    have hK0 : 0 ≤ K := by positivity
    calc ‖(A + t • B) ^ k * B * (A + t • B) ^ (m - 1 - k)‖
        ≤ ‖(A + t • B) ^ k * B‖ * ‖(A + t • B) ^ (m - 1 - k)‖ :=
          norm_mul_le _ _
    _ ≤ K ^ k * ‖B‖ * (K ^ (m - 1 - k)) := by
        refine mul_le_mul (pow_mul_norm_le A B ht k)
          (norm_pow_path _ _ (path_norm_le A B ht) hK0)
          (norm_nonneg _) (by positivity)
    _ = K ^ (k + (m - 1 - k)) * ‖B‖ := by
        rw [pow_add]
        ring
    _ = K ^ (m - 1) * ‖B‖ := by
        congr 2
        omega
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
private lemma hasDerivAt_traceMul_pow (A B : Matrix (Fin d) (Fin d) ℂ)
    (m : ℕ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ((m.factorial : ℂ))⁻¹
        * Matrix.trace ((A + s • B) ^ m * B))
      (((m.factorial : ℂ))⁻¹
        * Matrix.trace ((∑ k ∈ Finset.range m,
            (A + t • B) ^ k * B * (A + t • B) ^ (m - 1 - k)) * B)) t := by
  have h := ((traceMulCLM B).hasFDerivAt).comp_hasDerivAt t
    (hasDerivAt_path_pow A B m t)
  exact h.const_mul (((m.factorial : ℂ))⁻¹)

/-- The second-derivative series bound. -/
private def ubound2 (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) :
    ℝ :=
  ubound d A B m * ‖B‖

private lemma ubound2_summable (A B : Matrix (Fin d) (Fin d) ℂ) :
    Summable (ubound2 d A B) :=
  (ubound_summable A B).mul_right ‖B‖

private lemma gderiv2_bound (A B : Matrix (Fin d) (Fin d) ℂ) (m : ℕ)
    {t : ℝ} (ht : |t| ≤ 1) :
    ‖((m.factorial : ℂ))⁻¹
        * Matrix.trace ((∑ k ∈ Finset.range m,
            (A + t • B) ^ k * B * (A + t • B) ^ (m - 1 - k)) * B)‖
      ≤ ubound2 d A B m := by
  have h2 : ‖((m.factorial : ℂ))⁻¹‖ = ((m.factorial : ℝ))⁻¹ := by
    rw [norm_inv]
    congr 1
    simp
  calc ‖((m.factorial : ℂ))⁻¹
      * Matrix.trace ((∑ k ∈ Finset.range m,
          (A + t • B) ^ k * B * (A + t • B) ^ (m - 1 - k)) * B)‖
      = ((m.factorial : ℝ))⁻¹ * ‖Matrix.trace ((∑ k ∈ Finset.range m,
          (A + t • B) ^ k * B * (A + t • B) ^ (m - 1 - k)) * B)‖ := by
        rw [norm_mul, h2]
  _ ≤ ((m.factorial : ℝ))⁻¹
        * (trC d * (m * ((‖A‖ + ‖B‖) ^ (m - 1) * ‖B‖) * ‖B‖)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (trace_norm_le _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ trC_nonneg
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (sum_word_norm_le A B m ht)
        (norm_nonneg _)
  _ = ubound2 d A B m := by
      rw [ubound2, ubound]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- The second derivative of the tilted trace at `0`:
`F''(0) = Σ'_m (m!)⁻¹ Σ_{k<m} Tr(Aᵏ B A^{m-1-k} B)`. -/
private lemma hasDerivAt_traceExpMul (A B : Matrix (Fin d) (Fin d) ℂ) :
    HasDerivAt (fun t : ℝ => Matrix.trace (exp (A + t • B) * B))
      (∑' m : ℕ, ((m.factorial : ℂ))⁻¹
        * Matrix.trace ((∑ k ∈ Finset.range m,
            A ^ k * B * A ^ (m - 1 - k)) * B)) 0 := by
  have hball : ∀ t : ℝ, t ∈ Metric.ball (0 : ℝ) 1 → |t| ≤ 1 := by
    intro t htb
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at htb
    exact htb.le
  have hder := hasDerivAt_tsum_of_isPreconnected
    (ubound2_summable A B) Metric.isOpen_ball
    (convex_ball (0 : ℝ) 1).isPreconnected
    (fun m t _ => hasDerivAt_traceMul_pow A B m t)
    (fun m t htb => gderiv2_bound A B m (hball t htb))
    (Metric.mem_ball_self one_pos)
    (traceMul_summable (A + (0 : ℝ) • B) B)
    (Metric.mem_ball_self one_pos)
  have hfun : (fun t : ℝ => ∑' m : ℕ, ((m.factorial : ℂ))⁻¹
      * Matrix.trace ((A + t • B) ^ m * B))
      = fun t : ℝ => Matrix.trace (exp (A + t • B) * B) := by
    funext t
    rw [trace_exp_mul_eq_tsum]
  rw [hfun] at hder
  refine hder.congr_deriv (tsum_congr fun m => ?_)
  simp

/-! ## The BKM integrand series and the Beta evaluation -/

/-- `X ↦ Tr(P·X·Q)` as a continuous `ℝ`-linear functional. -/
private def traceSandwichCLM (P Q : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Matrix.trace (P * X * Q)
      map_add' := fun X Y => by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun r X => by
        rw [mul_smul_comm, smul_mul_assoc, Matrix.trace_smul,
          RingHom.id_apply] }

private lemma traceSandwichCLM_apply (P Q X : Matrix (Fin d) (Fin d) ℂ) :
    traceSandwichCLM P Q X = Matrix.trace (P * X * Q) := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma coeff_smul_pow (a : ℝ) (M : Matrix (Fin d) (Fin d) ℂ)
    (l : ℕ) :
    ((l.factorial : ℂ))⁻¹ • (a • M) ^ l
      = (((a : ℂ)) ^ l * ((l.factorial : ℂ))⁻¹) • M ^ l := by
  rw [smul_pow]
  have hcast : (a ^ l : ℝ) • (M ^ l) = (((a : ℂ)) ^ l) • M ^ l := by
    rw [← algebraMap_smul ℂ (a ^ l : ℝ) (M ^ l)]
    norm_num
  rw [hcast, smul_smul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
private lemma inner_series (P Q M : Matrix (Fin d) (Fin d) ℂ) (a : ℝ) :
    Matrix.trace (P * exp (a • M) * Q)
      = ∑' l : ℕ, ((a : ℂ)) ^ l * ((l.factorial : ℂ))⁻¹
          * Matrix.trace (P * M ^ l * Q) := by
  rw [← traceSandwichCLM_apply, exp_series,
    ContinuousLinearMap.map_tsum _ (exp_summable _)]
  refine tsum_congr fun l => ?_
  rw [coeff_smul_pow, traceSandwichCLM_apply, mul_smul_comm,
    smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
private lemma outer_series (A B : Matrix (Fin d) (Fin d) ℂ) (s : ℝ) :
    Matrix.trace (exp ((1 - s) • A) * B * exp (s • A) * B)
      = ∑' k : ℕ, ((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
          * Matrix.trace (A ^ k * B * exp (s • A) * B) := by
  have hassoc : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      X * B * exp (s • A) * B = X * (B * exp (s • A) * B) := by
    intro X
    simp only [Matrix.mul_assoc]
  rw [hassoc, ← traceMulCLM_apply, exp_series ((1 - s) • A),
    ContinuousLinearMap.map_tsum _ (exp_summable _)]
  refine tsum_congr fun k => ?_
  rw [coeff_smul_pow, traceMulCLM_apply, smul_mul_assoc,
    Matrix.trace_smul, smul_eq_mul, ← hassoc]

private lemma beta_nat (k l : ℕ) :
    (∫ s in (0 : ℝ)..1, (1 - s) ^ k * s ^ l)
      = (k.factorial * l.factorial : ℝ) / ((k + l + 1).factorial) := by
  have hb := real_beta_convolution (al := (k : ℝ) + 1)
    (be := (l : ℝ) + 1) (t := 1) (by positivity) (by positivity)
    one_pos
  have hcongr : (∫ s in (0 : ℝ)..1,
      s ^ ((l : ℝ) + 1 - 1) * (1 - s) ^ ((k : ℝ) + 1 - 1))
      = ∫ s in (0 : ℝ)..1, (1 - s) ^ k * s ^ l := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show (l : ℝ) + 1 - 1 = (l : ℝ) by ring,
      show (k : ℝ) + 1 - 1 = (k : ℝ) by ring,
      Real.rpow_natCast, Real.rpow_natCast]
    ring
  rw [← hcongr, hb]
  rw [show (k : ℝ) + 1 + ((l : ℝ) + 1) - 1 = ((k + l + 1 : ℕ) : ℝ) by
      push_cast; ring]
  rw [Real.one_rpow, one_mul]
  rw [show (k : ℝ) + 1 + ((l : ℝ) + 1) = ((k + l + 1 : ℕ) : ℝ) + 1 by
      push_cast; ring]
  rw [Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    Real.Gamma_nat_eq_factorial]

/-! ## The two integral–series exchanges -/

set_option backward.isDefEq.respectTransparency false in
private lemma exists_exp_bound (A : Matrix (Fin d) (Fin d) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖exp (s • A)‖ ≤ C := by
  have hcont : ContinuousOn (fun s : ℝ => exp (s • A))
      (Set.Icc (0 : ℝ) 1) :=
    (exp_continuous.comp (continuous_id.smul continuous_const)).continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨max C 0, le_max_right _ _,
    fun s hs => (hC s hs).trans (le_max_left _ _)⟩

set_option backward.isDefEq.respectTransparency false in
private lemma hk_continuous (A B : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    Continuous (fun s : ℝ =>
      Matrix.trace (A ^ k * B * exp (s • A) * B)) := by
  have h : (fun s : ℝ => Matrix.trace (A ^ k * B * exp (s • A) * B))
      = fun s : ℝ => traceSandwichCLM (A ^ k * B) B (exp (s • A)) := by
    funext s
    rw [traceSandwichCLM_apply]
  rw [h]
  exact (traceSandwichCLM (A ^ k * B) B).continuous.comp
    (exp_continuous.comp (continuous_id.smul continuous_const))

private lemma trace_word_bound (A B : Matrix (Fin d) (Fin d) ℂ)
    (k l : ℕ) :
    ‖Matrix.trace (A ^ k * B * A ^ l * B)‖
      ≤ trC d * (‖A‖ ^ (k + l) * ‖B‖ ^ 2) := by
  refine (trace_norm_le _).trans
    (mul_le_mul_of_nonneg_left ?_ trC_nonneg)
  calc ‖A ^ k * B * A ^ l * B‖
      ≤ ‖A ^ k * B * A ^ l‖ * ‖B‖ := norm_mul_le _ _
  _ ≤ ‖A ^ k * B‖ * ‖A ^ l‖ * ‖B‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
  _ ≤ ‖A ^ k‖ * ‖B‖ * ‖A ^ l‖ * ‖B‖ := by
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        (norm_nonneg _)
  _ ≤ ‖A‖ ^ k * ‖B‖ * ‖A‖ ^ l * ‖B‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine mul_le_mul ?_ (norm_pow_path A l le_rfl (norm_nonneg A))
        (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (norm_pow_path A k le_rfl (norm_nonneg A)) (norm_nonneg _)
  _ = ‖A‖ ^ (k + l) * ‖B‖ ^ 2 := by
      rw [pow_add]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- Interval-to-set conversion plus the outer exchange: the BKM
integral as a `k`-series. -/
private lemma bkm_outer_swap (A B : Matrix (Fin d) (Fin d) ℂ) :
    (∫ s in (0 : ℝ)..1,
        Matrix.trace (exp ((1 - s) • A) * B * exp (s • A) * B))
      = ∑' k : ℕ, ∫ s in (0 : ℝ)..1,
          ((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
            * Matrix.trace (A ^ k * B * exp (s • A) * B) := by
  obtain ⟨C, hC0, hC⟩ := exists_exp_bound A
  rw [intervalIntegral.integral_congr fun s _ => outer_series A B s]
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← MeasureTheory.integral_tsum_of_summable_integral_norm]
  · exact tsum_congr fun k => by
      rw [intervalIntegral.integral_of_le zero_le_one]
  · intro k
    refine (Continuous.integrableOn_Ioc ?_)
    have hc1 : Continuous fun s : ℝ => ((1 - s : ℝ) : ℂ) ^ k :=
      (Complex.continuous_ofReal.comp
        (continuous_const.sub continuous_id)).pow k
    exact (hc1.mul continuous_const).mul (hk_continuous A B k)
  · -- summable integral bounds
    have hbound : ∀ k : ℕ, (∫ s in Set.Ioc (0 : ℝ) 1,
        ‖((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
          * Matrix.trace (A ^ k * B * exp (s • A) * B)‖)
        ≤ ((k.factorial : ℝ))⁻¹
          * (trC d * (‖A‖ ^ k * (‖B‖ ^ 2 * C))) := by
      intro k
      have hptw : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
          ‖((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
            * Matrix.trace (A ^ k * B * exp (s • A) * B)‖
          ≤ ((k.factorial : ℝ))⁻¹
            * (trC d * (‖A‖ ^ k * (‖B‖ ^ 2 * C))) := by
        intro s hs
        have hs1 : ‖((1 - s : ℝ) : ℂ) ^ k‖ ≤ 1 := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
          refine pow_le_one₀ (abs_nonneg _) ?_
          rw [abs_le]
          constructor <;> [linarith [hs.2]; linarith [hs.1]]
        have hfac : ‖((k.factorial : ℂ))⁻¹‖
            = ((k.factorial : ℝ))⁻¹ := by
          rw [norm_inv]
          congr 1
          simp
        have htr : ‖Matrix.trace (A ^ k * B * exp (s • A) * B)‖
            ≤ trC d * (‖A‖ ^ k * (‖B‖ ^ 2 * C)) := by
          refine (trace_norm_le _).trans
            (mul_le_mul_of_nonneg_left ?_ trC_nonneg)
          calc ‖A ^ k * B * exp (s • A) * B‖
              ≤ ‖A ^ k‖ * ‖B‖ * ‖exp (s • A)‖ * ‖B‖ := by
                refine (norm_mul_le _ _).trans ?_
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                refine (norm_mul_le _ _).trans ?_
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                exact norm_mul_le _ _
          _ ≤ ‖A‖ ^ k * ‖B‖ * C * ‖B‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
              · exact mul_le_mul_of_nonneg_right
                  (norm_pow_path A k le_rfl (norm_nonneg A))
                  (norm_nonneg _)
              · exact hC s ⟨hs.1.le, hs.2⟩
          _ = ‖A‖ ^ k * (‖B‖ ^ 2 * C) := by ring
        calc ‖((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
            * Matrix.trace (A ^ k * B * exp (s • A) * B)‖
            = ‖((1 - s : ℝ) : ℂ) ^ k‖ * ‖((k.factorial : ℂ))⁻¹‖
              * ‖Matrix.trace (A ^ k * B * exp (s • A) * B)‖ := by
              rw [norm_mul, norm_mul]
        _ ≤ 1 * ((k.factorial : ℝ))⁻¹
              * (trC d * (‖A‖ ^ k * (‖B‖ ^ 2 * C))) := by
            rw [hfac]
            refine mul_le_mul ?_ htr (norm_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_right hs1 (by positivity)
        _ = ((k.factorial : ℝ))⁻¹
              * (trC d * (‖A‖ ^ k * (‖B‖ ^ 2 * C))) := by ring
      calc (∫ s in Set.Ioc (0 : ℝ) 1,
          ‖((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
            * Matrix.trace (A ^ k * B * exp (s • A) * B)‖)
          ≤ ∫ _s in Set.Ioc (0 : ℝ) 1,
            ((k.factorial : ℝ))⁻¹
              * (trC d * (‖A‖ ^ k * (‖B‖ ^ 2 * C))) := by
            refine MeasureTheory.setIntegral_mono_on ?_ ?_
              measurableSet_Ioc hptw
            · refine ((Continuous.integrableOn_Ioc ?_).norm)
              have hc1 : Continuous fun s : ℝ =>
                  ((1 - s : ℝ) : ℂ) ^ k :=
                (Complex.continuous_ofReal.comp
                  (continuous_const.sub continuous_id)).pow k
              exact (hc1.mul continuous_const).mul (hk_continuous A B k)
            · exact continuous_const.integrableOn_Ioc
      _ ≤ ((k.factorial : ℝ))⁻¹
            * (trC d * (‖A‖ ^ k * (‖B‖ ^ 2 * C))) := by
          rw [MeasureTheory.setIntegral_const]
          simp [MeasureTheory.measureReal_def, Real.volume_Ioc]
    refine Summable.of_nonneg_of_le
      (fun k => MeasureTheory.integral_nonneg fun s => norm_nonneg _)
      hbound ?_
    have hsum := (Real.summable_pow_div_factorial ‖A‖).mul_right
      (trC d * (‖B‖ ^ 2 * C))
    refine hsum.congr fun k => ?_
    rw [div_eq_mul_inv]
    ring

set_option backward.isDefEq.respectTransparency false in
/-- The inner exchange and Beta evaluation: each `k`-term of the BKM
integral is an `l`-series with coefficient `1/(k+l+1)!`. -/
private lemma bkm_inner_swap (A B : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    (∫ s in (0 : ℝ)..1,
        ((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
          * Matrix.trace (A ^ k * B * exp (s • A) * B))
      = ∑' l : ℕ, (((k + l + 1).factorial : ℂ))⁻¹
          * Matrix.trace (A ^ k * B * A ^ l * B) := by
  have hcongr : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      ((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
          * Matrix.trace (A ^ k * B * exp (s • A) * B)
        = ∑' l : ℕ, ((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
            * (((s : ℝ) : ℂ) ^ l * ((l.factorial : ℂ))⁻¹
              * Matrix.trace (A ^ k * B * A ^ l * B)) := by
    intro s _
    rw [inner_series (A ^ k * B) B A s, ← tsum_mul_left]
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_of_le zero_le_one,
    ← MeasureTheory.integral_tsum_of_summable_integral_norm]
  · refine tsum_congr fun l => ?_
    rw [← intervalIntegral.integral_of_le (a := (0 : ℝ)) zero_le_one]
    have hpull : (∫ s in (0 : ℝ)..1,
        ((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
          * (((s : ℝ) : ℂ) ^ l * ((l.factorial : ℂ))⁻¹
            * Matrix.trace (A ^ k * B * A ^ l * B)))
        = (((k.factorial : ℂ))⁻¹ * ((l.factorial : ℂ))⁻¹
            * Matrix.trace (A ^ k * B * A ^ l * B))
          * ∫ s in (0 : ℝ)..1,
            ((1 - s : ℝ) : ℂ) ^ k * ((s : ℝ) : ℂ) ^ l := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    rw [hpull]
    have hbeta : (∫ s in (0 : ℝ)..1,
        ((1 - s : ℝ) : ℂ) ^ k * ((s : ℝ) : ℂ) ^ l)
        = (((k.factorial * l.factorial : ℝ)
            / ((k + l + 1).factorial) : ℝ) : ℂ) := by
      have hre : (∫ s in (0 : ℝ)..1,
          ((1 - s : ℝ) : ℂ) ^ k * ((s : ℝ) : ℂ) ^ l)
          = ∫ s in (0 : ℝ)..1, (((1 - s) ^ k * s ^ l : ℝ) : ℂ) := by
        refine intervalIntegral.integral_congr fun s _ => ?_
        push_cast
        ring
      rw [hre, intervalIntegral.integral_ofReal, beta_nat]
    rw [hbeta]
    have hkne : ((k.factorial : ℂ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne'
    have hlne : ((l.factorial : ℂ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_pos l).ne'
    have hklne : (((k + l + 1).factorial : ℂ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
    push_cast
    field_simp
  · intro l
    refine Continuous.integrableOn_Ioc ?_
    have hc1 : Continuous fun s : ℝ => ((1 - s : ℝ) : ℂ) ^ k :=
      (Complex.continuous_ofReal.comp
        (continuous_const.sub continuous_id)).pow k
    have hc2 : Continuous fun s : ℝ => ((s : ℝ) : ℂ) ^ l :=
      Complex.continuous_ofReal.pow l
    exact ((hc1.mul continuous_const).mul
      ((hc2.mul continuous_const).mul continuous_const))
  · have hbnd : ∀ l : ℕ, (∫ s in Set.Ioc (0 : ℝ) 1,
        ‖((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
          * (((s : ℝ) : ℂ) ^ l * ((l.factorial : ℂ))⁻¹
            * Matrix.trace (A ^ k * B * A ^ l * B))‖)
        ≤ ((l.factorial : ℝ))⁻¹
          * (‖A‖ ^ l * (trC d * (‖A‖ ^ k * ‖B‖ ^ 2))) := by
      intro l
      have hptw : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
          ‖((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
            * (((s : ℝ) : ℂ) ^ l * ((l.factorial : ℂ))⁻¹
              * Matrix.trace (A ^ k * B * A ^ l * B))‖
          ≤ ((l.factorial : ℝ))⁻¹
            * (‖A‖ ^ l * (trC d * (‖A‖ ^ k * ‖B‖ ^ 2))) := by
        intro s hs
        have h1s : ‖((1 - s : ℝ) : ℂ) ^ k‖ ≤ 1 := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
          refine pow_le_one₀ (abs_nonneg _) ?_
          rw [abs_le]
          constructor <;> [linarith [hs.2]; linarith [hs.1]]
        have h2s : ‖((s : ℝ) : ℂ) ^ l‖ ≤ 1 := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
          refine pow_le_one₀ (abs_nonneg _) ?_
          rw [abs_le]
          constructor <;> [linarith [hs.1]; linarith [hs.2]]
        have hkfac : ‖((k.factorial : ℂ))⁻¹‖ ≤ 1 := by
          rw [norm_inv]
          refine inv_le_one_of_one_le₀ ?_
          have : (1 : ℝ) ≤ (k.factorial : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr
              (Nat.factorial_pos k).ne'
          simpa using this
        have hlfac : ‖((l.factorial : ℂ))⁻¹‖
            = ((l.factorial : ℝ))⁻¹ := by
          rw [norm_inv]
          congr 1
          simp
        calc ‖((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
            * (((s : ℝ) : ℂ) ^ l * ((l.factorial : ℂ))⁻¹
              * Matrix.trace (A ^ k * B * A ^ l * B))‖
            = ‖((1 - s : ℝ) : ℂ) ^ k‖ * ‖((k.factorial : ℂ))⁻¹‖
              * (‖((s : ℝ) : ℂ) ^ l‖ * ((l.factorial : ℝ))⁻¹
                * ‖Matrix.trace (A ^ k * B * A ^ l * B)‖) := by
              simp only [norm_mul]
              rw [hlfac]
        _ ≤ 1 * 1 * (1 * ((l.factorial : ℝ))⁻¹
              * (trC d * (‖A‖ ^ (k + l) * ‖B‖ ^ 2))) := by
            (gcongr;
              first
                | exact h1s
                | exact hkfac
                | exact h2s
                | exact trace_word_bound A B k l)
        _ = ((l.factorial : ℝ))⁻¹
              * (‖A‖ ^ l * (trC d * (‖A‖ ^ k * ‖B‖ ^ 2))) := by
            rw [pow_add]
            ring
      calc (∫ s in Set.Ioc (0 : ℝ) 1,
          ‖((1 - s : ℝ) : ℂ) ^ k * ((k.factorial : ℂ))⁻¹
            * (((s : ℝ) : ℂ) ^ l * ((l.factorial : ℂ))⁻¹
              * Matrix.trace (A ^ k * B * A ^ l * B))‖)
          ≤ ∫ _s in Set.Ioc (0 : ℝ) 1,
            ((l.factorial : ℝ))⁻¹
              * (‖A‖ ^ l * (trC d * (‖A‖ ^ k * ‖B‖ ^ 2))) := by
            refine MeasureTheory.setIntegral_mono_on ?_ ?_
              measurableSet_Ioc hptw
            · refine (Continuous.integrableOn_Ioc ?_).norm
              have hc1 : Continuous fun s : ℝ =>
                  ((1 - s : ℝ) : ℂ) ^ k :=
                (Complex.continuous_ofReal.comp
                  (continuous_const.sub continuous_id)).pow k
              have hc2 : Continuous fun s : ℝ => ((s : ℝ) : ℂ) ^ l :=
                Complex.continuous_ofReal.pow l
              exact ((hc1.mul continuous_const).mul
                ((hc2.mul continuous_const).mul continuous_const))
            · exact continuous_const.integrableOn_Ioc
      _ ≤ ((l.factorial : ℝ))⁻¹
            * (‖A‖ ^ l * (trC d * (‖A‖ ^ k * ‖B‖ ^ 2))) := by
          rw [MeasureTheory.setIntegral_const]
          simp [MeasureTheory.measureReal_def, Real.volume_Ioc]
    refine Summable.of_nonneg_of_le
      (fun l => MeasureTheory.integral_nonneg fun s => norm_nonneg _)
      hbnd ?_
    have hsum := (Real.summable_pow_div_factorial ‖A‖).mul_right
      (trC d * (‖A‖ ^ k * ‖B‖ ^ 2))
    refine hsum.congr fun l => ?_
    rw [div_eq_mul_inv]
    ring

/-- The BKM integral as the double series `Σ T(k,l)/(k+l+1)!`. -/
private lemma bkm_integral_double (A B : Matrix (Fin d) (Fin d) ℂ) :
    (∫ s in (0 : ℝ)..1,
        Matrix.trace (exp ((1 - s) • A) * B * exp (s • A) * B))
      = ∑' k : ℕ, ∑' l : ℕ, (((k + l + 1).factorial : ℂ))⁻¹
          * Matrix.trace (A ^ k * B * A ^ l * B) := by
  rw [bkm_outer_swap]
  exact tsum_congr fun k => bkm_inner_swap A B k

/-! ## Diagonal regrouping: the double series is `F''(0)` -/

private lemma diag_regroup {f : ℕ × ℕ → ℂ} (hf : Summable f) :
    (∑' k : ℕ, ∑' l : ℕ, f (k, l))
      = ∑' j : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j, f kl := by
  have hσ : Summable fun x :
      Σ j : ℕ, Finset.HasAntidiagonal.antidiagonal j =>
      f (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd x) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hf
  calc (∑' k : ℕ, ∑' l : ℕ, f (k, l))
      = ∑' p : ℕ × ℕ, f p :=
      (hf.tsum_prod' fun b => hf.prod_factor b).symm
  _ = ∑' x : Σ j : ℕ, Finset.HasAntidiagonal.antidiagonal j,
        f (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd x) :=
      (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f).symm
  _ = ∑' j : ℕ, ∑' kl : Finset.HasAntidiagonal.antidiagonal j, f kl :=
      hσ.tsum_sigma' fun j => (hasSum_fintype _).summable
  _ = ∑' j : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j, f kl :=
      tsum_congr fun j => Finset.tsum_subtype _ _

private lemma factorial_prod_le (k l : ℕ) :
    (k.factorial * l.factorial : ℝ) ≤ ((k + l + 1).factorial : ℝ) := by
  have h1 : k.factorial * l.factorial ≤ (k + l).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add k l)
  have h2 : (k + l).factorial ≤ (k + l + 1).factorial :=
    Nat.factorial_le (by omega)
  exact_mod_cast h1.trans h2

set_option backward.isDefEq.respectTransparency false in
private lemma double_summable (A B : Matrix (Fin d) (Fin d) ℂ) :
    Summable fun p : ℕ × ℕ =>
      (((p.1 + p.2 + 1).factorial : ℂ))⁻¹
        * Matrix.trace (A ^ p.1 * B * A ^ p.2 * B) := by
  refine Summable.of_norm ?_
  have hprod : Summable fun p : ℕ × ℕ =>
      (‖A‖ ^ p.1 / p.1.factorial)
        * (‖A‖ ^ p.2 / p.2.factorial * (trC d * ‖B‖ ^ 2)) :=
    (Real.summable_pow_div_factorial ‖A‖).mul_of_nonneg
      ((Real.summable_pow_div_factorial ‖A‖).mul_right (trC d * ‖B‖ ^ 2))
      (fun k => div_nonneg (pow_nonneg (norm_nonneg A) k)
        (Nat.cast_nonneg _))
      (fun l => mul_nonneg
        (div_nonneg (pow_nonneg (norm_nonneg A) l) (Nat.cast_nonneg _))
        (mul_nonneg trC_nonneg (pow_nonneg (norm_nonneg B) 2)))
  refine hprod.of_nonneg_of_le (fun p => norm_nonneg _) fun p => ?_
  obtain ⟨k, l⟩ := p
  have hfacpos : (0 : ℝ) < (k.factorial * l.factorial : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos l)
  have hinv : (((k + l + 1).factorial : ℝ))⁻¹
      ≤ ((k.factorial * l.factorial : ℝ))⁻¹ := by
    have h := one_div_le_one_div_of_le hfacpos (factorial_prod_le k l)
    rwa [one_div, one_div] at h
  have hnorm : ‖(((k + l + 1).factorial : ℂ))⁻¹
      * Matrix.trace (A ^ k * B * A ^ l * B)‖
      = (((k + l + 1).factorial : ℝ))⁻¹
        * ‖Matrix.trace (A ^ k * B * A ^ l * B)‖ := by
    rw [norm_mul, norm_inv]
    congr 2
    simp
  rw [hnorm]
  calc (((k + l + 1).factorial : ℝ))⁻¹
      * ‖Matrix.trace (A ^ k * B * A ^ l * B)‖
      ≤ ((k.factorial * l.factorial : ℝ))⁻¹
        * (trC d * (‖A‖ ^ (k + l) * ‖B‖ ^ 2)) :=
        mul_le_mul hinv (trace_word_bound A B k l)
          (norm_nonneg _) (by positivity)
  _ = ‖A‖ ^ k / k.factorial
        * (‖A‖ ^ l / l.factorial * (trC d * ‖B‖ ^ 2)) := by
        rw [pow_add, mul_inv]
        field_simp

set_option backward.isDefEq.respectTransparency false in
/-- The second derivative of the tilted trace equals the BKM
integral: `F''(0) = ∫₀¹ Tr(e^{(1-s)A} B e^{sA} B) ds`. -/
private lemma second_deriv_eq_bkm (A B : Matrix (Fin d) (Fin d) ℂ) :
    (∑' m : ℕ, ((m.factorial : ℂ))⁻¹
        * Matrix.trace ((∑ k ∈ Finset.range m,
            A ^ k * B * A ^ (m - 1 - k)) * B))
      = ∫ s in (0 : ℝ)..1,
          Matrix.trace (exp ((1 - s) • A) * B * exp (s • A) * B) := by
  rw [bkm_integral_double, diag_regroup (double_summable A B)]
  -- expand the trace of the word sum
  have hLm : ∀ m : ℕ, ((m.factorial : ℂ))⁻¹
      * Matrix.trace ((∑ k ∈ Finset.range m,
          A ^ k * B * A ^ (m - 1 - k)) * B)
      = ∑ k ∈ Finset.range m, ((m.factorial : ℂ))⁻¹
          * Matrix.trace (A ^ k * B * A ^ (m - 1 - k) * B) := by
    intro m
    rw [Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]
  rw [tsum_congr hLm]
  -- summability of the word-sum series (from the derivative bounds)
  have hsum2 : Summable fun m : ℕ =>
      ∑ k ∈ Finset.range m, ((m.factorial : ℂ))⁻¹
        * Matrix.trace (A ^ k * B * A ^ (m - 1 - k) * B) := by
    refine Summable.of_norm ?_
    refine (ubound2_summable A B).of_nonneg_of_le
      (fun m => norm_nonneg _) fun m => ?_
    have h := gderiv2_bound A B m (t := 0) (by simp)
    simp only [zero_smul, add_zero] at h
    rw [← hLm m]
    exact h
  rw [hsum2.tsum_eq_zero_add]
  simp only [Finset.range_zero, Finset.sum_empty, zero_add]
  refine tsum_congr fun j => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have he1 : j + 1 - 1 - k = j - k := by omega
  have he2 : k + (j - k) + 1 = j + 1 := by omega
  rw [he1, he2]

/-! ## The BKM Hessian: main statements -/

set_option backward.isDefEq.respectTransparency false in
/-- `thm:bkm-hessian` (first Duhamel derivative): on the unit ball,
`d/dq Tr exp(A + qB) = Tr(exp(A+qB)·B)`. -/
theorem trace_exp_hasDerivAt (A B : Matrix (Fin d) (Fin d) ℂ) {q : ℝ}
    (hq : q ∈ Metric.ball (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => Matrix.trace (exp (A + t • B)))
      (Matrix.trace (exp (A + q • B) * B)) q :=
  hasDerivAt_traceExp A B hq

set_option backward.isDefEq.respectTransparency false in
/-- `thm:bkm-hessian` (Duhamel/BKM second derivative): the derivative
of `q ↦ Tr(exp(A+qB)·B)` at `0` is the BKM integral
`∫₀¹ Tr(e^{(1-s)A} B e^{sA} B) ds`. -/
theorem trace_exp_second_deriv (A B : Matrix (Fin d) (Fin d) ℂ) :
    HasDerivAt (fun t : ℝ => Matrix.trace (exp (A + t • B) * B))
      (∫ s in (0 : ℝ)..1,
        Matrix.trace (exp ((1 - s) • A) * B * exp (s • A) * B)) 0 :=
  (hasDerivAt_traceExpMul A B).congr_deriv (second_deriv_eq_bkm A B)

set_option backward.isDefEq.respectTransparency false in
private lemma exp_smul_add (A : Matrix (Fin d) (Fin d) ℂ) (a b : ℝ) :
    exp ((a + b) • A) = exp (a • A) * exp (b • A) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _
    (((Commute.refl A).smul_left a).smul_right b)

set_option backward.isDefEq.respectTransparency false in
/-- The centering identity: with `ρ = exp A` normalized
(`Tr ρ = 1`) and `c = Tr(ρS)`, the centered BKM integrand differs
from the uncentered one by `c²` pointwise. -/
theorem bkm_centering (A S : Matrix (Fin d) (Fin d) ℂ)
    (hnorm : Matrix.trace (exp A) = 1) (s : ℝ) :
    Matrix.trace (exp ((1 - s) • A)
        * (S - Matrix.trace (exp A * S) • 1)
        * exp (s • A) * (S - Matrix.trace (exp A * S) • 1))
      = Matrix.trace (exp ((1 - s) • A) * S * exp (s • A) * S)
        - Matrix.trace (exp A * S) ^ 2 := by
  set c : ℂ := Matrix.trace (exp A * S) with hc
  have hmerge : exp ((1 - s) • A) * exp (s • A) = exp A := by
    rw [← exp_smul_add]
    norm_num
  have hmerge' : exp (s • A) * exp ((1 - s) • A) = exp A := by
    rw [← exp_smul_add]
    norm_num
  have hexp : exp ((1 - s) • A) * (S - c • 1) * exp (s • A) * (S - c • 1)
      = exp ((1 - s) • A) * S * exp (s • A) * S
        - c • (exp ((1 - s) • A) * S * exp (s • A))
        - c • (exp ((1 - s) • A) * exp (s • A) * S)
        + (c * c) • (exp ((1 - s) • A) * exp (s • A)) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm,
      smul_mul_assoc, Matrix.mul_one, smul_sub, smul_smul]
    abel
  rw [hexp]
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    hmerge]
  have hcyc : Matrix.trace (exp ((1 - s) • A) * S * exp (s • A)) = c := by
    rw [Matrix.trace_mul_cycle, hmerge', ← hc]
  rw [hcyc, ← hc, hnorm]
  simp only [smul_eq_mul, mul_one]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- `thm:bkm-hessian` (positivity): for Hermitian `A` and `S` the BKM
integrand is a trace of `Z Zᴴ` with `Z = e^{(1-s)A/2} S e^{sA/2}`,
hence real and nonnegative. -/
theorem bkm_integrand_nonneg (A S : Matrix (Fin d) (Fin d) ℂ)
    (hA : Aᴴ = A) (hS : Sᴴ = S) (s : ℝ) :
    (0 : ℂ) ≤ Matrix.trace (exp ((1 - s) • A) * S * exp (s • A) * S) := by
  have hexpH : ∀ r : ℝ, (exp (r • A))ᴴ = exp (r • A) := by
    intro r
    rw [← Matrix.exp_conjTranspose]
    congr 1
    rw [Matrix.conjTranspose_smul, hA, star_trivial]
  set Z : Matrix (Fin d) (Fin d) ℂ :=
    exp (((1 - s) / 2) • A) * S * exp ((s / 2) • A) with hZ
  have hZH : Zᴴ = exp ((s / 2) • A)
      * (S * exp (((1 - s) / 2) • A)) := by
    rw [hZ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hexpH,
      hexpH, hS]
  have hb : exp ((s / 2) • A) * exp ((s / 2) • A) = exp (s • A) := by
    rw [← exp_smul_add]
    norm_num
  have ha : exp (((1 - s) / 2) • A) * exp (((1 - s) / 2) • A)
      = exp ((1 - s) • A) := by
    rw [← exp_smul_add]
    norm_num
  have htr : Matrix.trace (Z * Zᴴ)
      = Matrix.trace (exp ((1 - s) • A) * S * exp (s • A) * S) := by
    rw [hZH, hZ]
    have h1 : exp (((1 - s) / 2) • A) * S * exp ((s / 2) • A)
        * (exp ((s / 2) • A) * (S * exp (((1 - s) / 2) • A)))
        = exp (((1 - s) / 2) • A)
          * (S * (exp (s • A) * (S * exp (((1 - s) / 2) • A)))) := by
      simp only [Matrix.mul_assoc]
      rw [show exp ((s / 2) • A) * (exp ((s / 2) • A)
          * (S * exp (((1 - s) / 2) • A)))
          = exp (s • A) * (S * exp (((1 - s) / 2) • A)) from by
        rw [← Matrix.mul_assoc, hb]]
    rw [h1, Matrix.trace_mul_comm]
    rw [show S * (exp (s • A) * (S * exp (((1 - s) / 2) • A)))
        * exp (((1 - s) / 2) • A)
        = S * exp (s • A) * S
          * (exp (((1 - s) / 2) • A) * exp (((1 - s) / 2) • A)) from by
      simp only [Matrix.mul_assoc]]
    rw [ha, Matrix.trace_mul_comm]
    rw [show exp ((1 - s) • A) * (S * exp (s • A) * S)
        = exp ((1 - s) • A) * S * exp (s • A) * S from by
      simp only [Matrix.mul_assoc]]
  rw [← htr]
  exact (Matrix.posSemidef_self_mul_conjTranspose Z).trace_nonneg

set_option backward.isDefEq.respectTransparency false in
/-- `thm:bkm-hessian` (assembled): for the normalized path state
`ρ = exp A` (`Tr ρ = 1`) and score `S`, the second derivative of the
tilted trace at `q = 0` is the centered BKM curvature plus the
squared mean, `F''(0) = ∫₀¹ Tr(ρ^{1-s} S̃ ρ^s S̃) ds + Tr(ρS)²`, with
`ρ^t := exp(tA)` and `S̃ = S − Tr(ρS)·1`; for Hermitian data the
centered integrand is pointwise real-nonnegative
(`bkm_integrand_nonneg`), so `ψ''(0) = F''(0) − F'(0)² ≥ 0`. -/
theorem bkm_hessian (A S : Matrix (Fin d) (Fin d) ℂ)
    (hnorm : Matrix.trace (exp A) = 1) :
    HasDerivAt (fun t : ℝ => Matrix.trace (exp (A + t • S) * S))
      ((∫ s in (0 : ℝ)..1,
        Matrix.trace (exp ((1 - s) • A)
          * (S - Matrix.trace (exp A * S) • 1)
          * exp (s • A) * (S - Matrix.trace (exp A * S) • 1)))
        + Matrix.trace (exp A * S) ^ 2) 0 := by
  refine (trace_exp_second_deriv A S).congr_deriv ?_
  set c : ℂ := Matrix.trace (exp A * S) with hc
  have hexp1 : Continuous fun s : ℝ => exp ((1 - s) • A) :=
    exp_continuous.comp
      ((continuous_const.sub continuous_id).smul continuous_const)
  have hexp2 : Continuous fun s : ℝ => exp (s • A) :=
    exp_continuous.comp (continuous_id.smul continuous_const)
  have hcont : Continuous fun s : ℝ =>
      Matrix.trace (exp ((1 - s) • A) * S * exp (s • A) * S) := by
    have hshape : (fun s : ℝ =>
        Matrix.trace (exp ((1 - s) • A) * S * exp (s • A) * S))
        = fun s : ℝ =>
          traceCLM (exp ((1 - s) • A) * S * exp (s • A) * S) := by
      funext s
      rw [traceCLM_apply]
    rw [hshape]
    exact traceCLM.continuous.comp
      (((hexp1.mul continuous_const).mul hexp2).mul continuous_const)
  calc (∫ s in (0 : ℝ)..1,
      Matrix.trace (exp ((1 - s) • A) * S * exp (s • A) * S))
      = (∫ s in (0 : ℝ)..1,
          (Matrix.trace (exp ((1 - s) • A) * S * exp (s • A) * S)
            - c ^ 2)) + c ^ 2 := by
        rw [intervalIntegral.integral_sub
          (hcont.intervalIntegrable _ _) intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp
  _ = (∫ s in (0 : ℝ)..1,
        Matrix.trace (exp ((1 - s) • A) * (S - c • 1)
          * exp (s • A) * (S - c • 1))) + c ^ 2 := by
      congr 1
      refine (intervalIntegral.integral_congr fun s _ => ?_).symm
      rw [bkm_centering A S hnorm s, ← hc]

end

end NCG.BKM
