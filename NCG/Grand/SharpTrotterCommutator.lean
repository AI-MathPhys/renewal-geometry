/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ChannelEstimates

/-!
# Sharp commutator Trotter bounds for contractive exponentials

The sharp product-formula estimates behind the SMST noisy-channel
compiler constants (`thm:SMST-noisy-Klein-refocusing`,
`thm:SMST-channel-direct-bracket`): for exponentials that are
**contractions** (`‖e^{u•X}‖ ≤ 1`, as for skew-adjoint generators
in a C*-algebra), the product defect is governed by commutators —

* `exp_comm_le`: the commutator integral bound
  `‖e^{s•X}Y - Ye^{s•X}‖ ≤ s·‖XY - YX‖`;
* `exp_mul_exp_sub_exp_add_le_half_comm`: the **sharp pairwise
  Trotter bound** `‖e^X e^Y - e^{X+Y}‖ ≤ ‖[X,Y]‖/2`;
* `four_exp_sub_exp_add_le`: the four-factor version with the
  pairwise commutator sum `½·∑_{i<j}‖[Xᵢ,Xⱼ]‖`;
* `pow_sub_pow_bound`: contraction power telescoping
  `‖uⁿ - vⁿ‖ ≤ n·‖u - v‖`;
* `intertwine_pow_bound` / `prod_intertwine_bound`: two-sided
  telescoping through an encoder `ι`
  (`‖∏f·ι - ι·∏g‖ ≤ ∑‖fᵢι - ιgᵢ‖` for contraction factors).

Everything is derived in a Banach algebra; the only structural
inputs are the contraction hypotheses themselves, which is
exactly what unitarity supplies in the intended C*-instance.
The pairwise bound is proved by the interpolation curve
`K(s) = e^{(1-s)•(X+Y)}·e^{s•X}·e^{s•Y}`, whose derivative is
`e^{(1-s)•(X+Y)}·[e^{s•X}, Y]·e^{s•Y}`, together with the
commutator integral representation — the classical argument that
gives the constant `½` with no exponential factor, which the
naive series estimates cannot reach.
-/

open Set intervalIntegral NormedSpace

namespace NCG
namespace SharpTrotter

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A]

/-- The exponential curve `u ↦ e^{u•X}` is continuous. -/
theorem continuous_expCurve (X : A) :
    Continuous (fun u : ℝ => exp (u • X)) :=
  continuous_iff_continuousAt.mpr fun u =>
    (hasDerivAt_exp_smul_const' X u).continuousAt

/-- `e^{u•X}` commutes with `X` (uniqueness of the derivative of
the exponential curve). -/
theorem expCurve_comm (X : A) (u : ℝ) :
    exp (u • X) * X = X * exp (u • X) :=
  (hasDerivAt_exp_smul_const X u).unique
    (hasDerivAt_exp_smul_const' X u)

/-- **Commutator integral bound**: conjugation defect of a
contractive exponential, `‖e^{s•X}Y - Ye^{s•X}‖ ≤ s·‖XY-YX‖`. -/
theorem exp_comm_le (X Y : A) (s : ℝ) (hs : 0 ≤ s)
    (hX : ∀ u ∈ Icc (0 : ℝ) s, ‖exp (u • X)‖ ≤ 1) :
    ‖exp (s • X) * Y - Y * exp (s • X)‖
      ≤ s * ‖X * Y - Y * X‖ := by
  -- the interpolation curve `φ(u) = e^{u•X}·Y·e^{(s-u)•X}`
  set φ : ℝ → A :=
    fun u => exp (u • X) * Y * exp ((s - u) • X) with hφdef
  have hderiv : ∀ u : ℝ, HasDerivAt φ
      (exp (u • X) * (X * Y - Y * X) * exp ((s - u) • X)) u := by
    intro u
    have h₁ : HasDerivAt (fun u : ℝ => exp (u • X) * Y)
        (exp (u • X) * X * Y) u :=
      (hasDerivAt_exp_smul_const X u).mul_const Y
    have h₂ : HasDerivAt (fun u : ℝ => exp ((s - u) • X))
        (-(X * exp ((s - u) • X))) u := by
      have hinner : HasDerivAt (fun u : ℝ => s - u) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub s
      have h := (hasDerivAt_exp_smul_const' X (s - u)).scomp
        u hinner
      rw [neg_one_smul] at h
      exact h
    have hmul := h₁.mul h₂
    have hval : exp (u • X) * X * Y * exp ((s - u) • X)
        + exp (u • X) * Y * -(X * exp ((s - u) • X))
        = exp (u • X) * (X * Y - Y * X) * exp ((s - u) • X) := by
      noncomm_ring
    rw [hval] at hmul
    exact hmul
  -- endpoints
  have hφs : φ s = exp (s • X) * Y := by
    simp [hφdef, exp_zero]
  have hφ0 : φ 0 = Y * exp (s • X) := by
    simp [hφdef, exp_zero]
  -- fundamental theorem of calculus
  have hcont : Continuous fun u : ℝ =>
      exp (u • X) * (X * Y - Y * X) * exp ((s - u) • X) := by
    refine ((continuous_expCurve X).mul continuous_const).mul ?_
    exact (continuous_expCurve X).comp
      (continuous_const.sub continuous_id)
  have hftc :
      (∫ u in (0 : ℝ)..s,
        exp (u • X) * (X * Y - Y * X) * exp ((s - u) • X))
      = φ s - φ 0 :=
    integral_eq_sub_of_hasDerivAt
      (fun u _ => hderiv u) (hcont.intervalIntegrable 0 s)
  rw [← hφs, ← hφ0, ← hftc]
  -- uniform bound on the integrand
  have hbound : ∀ u ∈ uIoc (0 : ℝ) s,
      ‖exp (u • X) * (X * Y - Y * X) * exp ((s - u) • X)‖
        ≤ ‖X * Y - Y * X‖ := by
    intro u hu
    rw [uIoc_of_le hs] at hu
    have hu1 : ‖exp (u • X)‖ ≤ 1 :=
      hX u ⟨hu.1.le, hu.2⟩
    have hu2 : ‖exp ((s - u) • X)‖ ≤ 1 :=
      hX (s - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    calc ‖exp (u • X) * (X * Y - Y * X) * exp ((s - u) • X)‖
        ≤ ‖exp (u • X) * (X * Y - Y * X)‖
          * ‖exp ((s - u) • X)‖ := norm_mul_le _ _
      _ ≤ ‖exp (u • X)‖ * ‖X * Y - Y * X‖
          * ‖exp ((s - u) • X)‖ := by
          refine mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖X * Y - Y * X‖ * 1 := by
          refine mul_le_mul ?_ hu2 (norm_nonneg _) ?_
          · exact mul_le_mul_of_nonneg_right hu1
              (norm_nonneg _)
          · positivity
      _ = ‖X * Y - Y * X‖ := by ring
  calc ‖∫ u in (0 : ℝ)..s,
        exp (u • X) * (X * Y - Y * X) * exp ((s - u) • X)‖
      ≤ ‖X * Y - Y * X‖ * |s - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = s * ‖X * Y - Y * X‖ := by
        rw [sub_zero, abs_of_nonneg hs]
        ring

/-- **Sharp pairwise Trotter bound** for contractive
exponentials: `‖e^X·e^Y - e^{X+Y}‖ ≤ ‖XY-YX‖/2`, with no
exponential prefactor. -/
theorem exp_mul_exp_sub_exp_add_le_half_comm (X Y : A)
    (hX : ∀ u ∈ Icc (0 : ℝ) 1, ‖exp (u • X)‖ ≤ 1)
    (hY : ∀ u ∈ Icc (0 : ℝ) 1, ‖exp (u • Y)‖ ≤ 1)
    (hXY : ∀ u ∈ Icc (0 : ℝ) 1, ‖exp (u • (X + Y))‖ ≤ 1) :
    ‖exp X * exp Y - exp (X + Y)‖
      ≤ ‖X * Y - Y * X‖ / 2 := by
  -- interpolation curve `K(s) = e^{(1-s)•(X+Y)}·e^{s•X}·e^{s•Y}`
  set K : ℝ → A := fun s =>
    exp ((1 - s) • (X + Y)) * exp (s • X) * exp (s • Y)
    with hKdef
  have hderiv : ∀ s : ℝ, HasDerivAt K
      (exp ((1 - s) • (X + Y))
        * (exp (s • X) * Y - Y * exp (s • X))
        * exp (s • Y)) s := by
    intro s
    have h₁ : HasDerivAt
        (fun s : ℝ => exp ((1 - s) • (X + Y)))
        (-((X + Y) * exp ((1 - s) • (X + Y)))) s := by
      have hinner : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
        simpa using (hasDerivAt_id s).const_sub (1 : ℝ)
      have h := (hasDerivAt_exp_smul_const' (X + Y) (1 - s)).scomp
        s hinner
      rw [neg_one_smul] at h
      exact h
    have h₂ := hasDerivAt_exp_smul_const' X s
    have h₃ := hasDerivAt_exp_smul_const' Y s
    have hmul := (h₁.mul h₂).mul h₃
    -- an atom-level identity: the only fact used is that `X+Y`
    -- passes through its own exponential
    have hgen : ∀ E₁ E₂ E₃ : A,
        E₁ * (X + Y) = (X + Y) * E₁ →
        (-((X + Y) * E₁) * E₂ + E₁ * (X * E₂)) * E₃
          + E₁ * E₂ * (Y * E₃)
        = E₁ * (E₂ * Y - Y * E₂) * E₃ := by
      intro E₁ E₂ E₃ hc
      have hneg : -((X + Y) * E₁) * E₂
          = -(E₁ * (X + Y)) * E₂ := by rw [hc]
      rw [hneg]
      noncomm_ring
    have hval := hgen (exp ((1 - s) • (X + Y)))
      (exp (s • X)) (exp (s • Y))
      (expCurve_comm (X + Y) (1 - s))
    simp only [Pi.mul_apply] at hmul
    rw [hval] at hmul
    exact hmul
  -- endpoints
  have hK1 : K 1 = exp X * exp Y := by
    simp [hKdef, exp_zero]
  have hK0 : K 0 = exp (X + Y) := by
    simp [hKdef, exp_zero]
  -- fundamental theorem of calculus
  have hcont : Continuous fun s : ℝ =>
      exp ((1 - s) • (X + Y))
        * (exp (s • X) * Y - Y * exp (s • X))
        * exp (s • Y) := by
    have hc₁ : Continuous fun s : ℝ =>
        exp ((1 - s) • (X + Y)) :=
      (continuous_expCurve (X + Y)).comp
        (continuous_const.sub continuous_id)
    have hc₂ : Continuous fun s : ℝ =>
        exp (s • X) * Y - Y * exp (s • X) :=
      ((continuous_expCurve X).mul continuous_const).sub
        (continuous_const.mul (continuous_expCurve X))
    exact (hc₁.mul hc₂).mul (continuous_expCurve Y)
  have hftc :
      (∫ s in (0 : ℝ)..1,
        exp ((1 - s) • (X + Y))
          * (exp (s • X) * Y - Y * exp (s • X))
          * exp (s • Y))
      = K 1 - K 0 :=
    integral_eq_sub_of_hasDerivAt
      (fun s _ => hderiv s) (hcont.intervalIntegrable 0 1)
  rw [← hK1, ← hK0, ← hftc]
  -- integrand bound `s·‖[X,Y]‖`
  have hboundInt : IntervalIntegrable
      (fun s : ℝ => s * ‖X * Y - Y * X‖)
      MeasureTheory.volume 0 1 :=
    (continuous_id.mul continuous_const).intervalIntegrable 0 1
  calc ‖∫ s in (0 : ℝ)..1,
        exp ((1 - s) • (X + Y))
          * (exp (s • X) * Y - Y * exp (s • X))
          * exp (s • Y)‖
      ≤ ∫ s in (0 : ℝ)..1, s * ‖X * Y - Y * X‖ := by
        refine intervalIntegral.norm_integral_le_of_norm_le
          zero_le_one
          (MeasureTheory.ae_of_all _ fun s hs => ?_) hboundInt
        have hs0 : (0 : ℝ) ≤ s := hs.1.le
        have hs1 : s ≤ 1 := hs.2
        have hcommBound :
            ‖exp (s • X) * Y - Y * exp (s • X)‖
              ≤ s * ‖X * Y - Y * X‖ :=
          exp_comm_le X Y s hs0
            (fun u hu => hX u ⟨hu.1, hu.2.trans hs1⟩)
        have h₁ : ‖exp ((1 - s) • (X + Y))‖ ≤ 1 :=
          hXY (1 - s) ⟨by linarith, by linarith⟩
        have h₂ : ‖exp (s • Y)‖ ≤ 1 := hY s ⟨hs0, hs1⟩
        calc ‖exp ((1 - s) • (X + Y))
              * (exp (s • X) * Y - Y * exp (s • X))
              * exp (s • Y)‖
            ≤ ‖exp ((1 - s) • (X + Y))
                * (exp (s • X) * Y - Y * exp (s • X))‖
              * ‖exp (s • Y)‖ := norm_mul_le _ _
          _ ≤ ‖exp ((1 - s) • (X + Y))‖
              * ‖exp (s • X) * Y - Y * exp (s • X)‖
              * ‖exp (s • Y)‖ := by
              refine mul_le_mul_of_nonneg_right
                (norm_mul_le _ _) (norm_nonneg _)
          _ ≤ 1 * (s * ‖X * Y - Y * X‖) * 1 := by
              refine mul_le_mul ?_ h₂ (norm_nonneg _) ?_
              · exact mul_le_mul h₁ hcommBound
                  (norm_nonneg _) zero_le_one
              · positivity
          _ = s * ‖X * Y - Y * X‖ := by ring
    _ = ‖X * Y - Y * X‖ / 2 := by
        rw [intervalIntegral.integral_mul_const, integral_id]
        ring

/-- Four-factor sharp Trotter bound: the defect of
`e^{X₀}e^{X₁}e^{X₂}e^{X₃}` against `e^{X₀+X₁+X₂+X₃}` is at most
half the sum of the six pairwise commutator norms. -/
theorem four_exp_sub_exp_add_le (X₀ X₁ X₂ X₃ : A)
    (h₀ : ∀ u ∈ Icc (0 : ℝ) 1, ‖exp (u • X₀)‖ ≤ 1)
    (h₁ : ∀ u ∈ Icc (0 : ℝ) 1, ‖exp (u • X₁)‖ ≤ 1)
    (h₂ : ∀ u ∈ Icc (0 : ℝ) 1, ‖exp (u • X₂)‖ ≤ 1)
    (h₃ : ∀ u ∈ Icc (0 : ℝ) 1, ‖exp (u • X₃)‖ ≤ 1)
    (h₀₁ : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • (X₀ + X₁))‖ ≤ 1)
    (h₀₁₂ : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • (X₀ + X₁ + X₂))‖ ≤ 1)
    (h₀₁₂₃ : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • (X₀ + X₁ + X₂ + X₃))‖ ≤ 1) :
    ‖exp X₀ * exp X₁ * exp X₂ * exp X₃
      - exp (X₀ + X₁ + X₂ + X₃)‖
    ≤ (‖X₀ * X₁ - X₁ * X₀‖
        + (‖X₀ * X₂ - X₂ * X₀‖ + ‖X₁ * X₂ - X₂ * X₁‖)
        + (‖X₀ * X₃ - X₃ * X₀‖ + ‖X₁ * X₃ - X₃ * X₁‖
            + ‖X₂ * X₃ - X₃ * X₂‖)) / 2 := by
  have hn₂ : ‖exp X₂‖ ≤ 1 := by
    have := h₂ 1 ⟨zero_le_one, le_refl 1⟩
    rwa [one_smul] at this
  have hn₃ : ‖exp X₃‖ ≤ 1 := by
    have := h₃ 1 ⟨zero_le_one, le_refl 1⟩
    rwa [one_smul] at this
  -- step 1: contract `e^{X₀}e^{X₁}` to `e^{X₀+X₁}`
  have hstep₁ : ‖exp X₀ * exp X₁ * exp X₂ * exp X₃
      - exp (X₀ + X₁) * exp X₂ * exp X₃‖
      ≤ ‖X₀ * X₁ - X₁ * X₀‖ / 2 := by
    have hid : exp X₀ * exp X₁ * exp X₂ * exp X₃
        - exp (X₀ + X₁) * exp X₂ * exp X₃
        = (exp X₀ * exp X₁ - exp (X₀ + X₁))
          * exp X₂ * exp X₃ := by
      noncomm_ring
    rw [hid]
    calc ‖(exp X₀ * exp X₁ - exp (X₀ + X₁))
          * exp X₂ * exp X₃‖
        ≤ ‖(exp X₀ * exp X₁ - exp (X₀ + X₁)) * exp X₂‖
          * ‖exp X₃‖ := norm_mul_le _ _
      _ ≤ ‖exp X₀ * exp X₁ - exp (X₀ + X₁)‖ * ‖exp X₂‖
          * ‖exp X₃‖ := by
          refine mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖X₀ * X₁ - X₁ * X₀‖ / 2 * 1 * 1 := by
          refine mul_le_mul ?_ hn₃ (norm_nonneg _) ?_
          · exact mul_le_mul
              (exp_mul_exp_sub_exp_add_le_half_comm
                X₀ X₁ h₀ h₁ h₀₁)
              hn₂ (norm_nonneg _) (by positivity)
          · positivity
      _ = ‖X₀ * X₁ - X₁ * X₀‖ / 2 := by ring
  -- step 2: contract `e^{X₀+X₁}e^{X₂}` to `e^{X₀+X₁+X₂}`
  have hstep₂ : ‖exp (X₀ + X₁) * exp X₂ * exp X₃
      - exp (X₀ + X₁ + X₂) * exp X₃‖
      ≤ (‖X₀ * X₂ - X₂ * X₀‖ + ‖X₁ * X₂ - X₂ * X₁‖) / 2 := by
    have hid : exp (X₀ + X₁) * exp X₂ * exp X₃
        - exp (X₀ + X₁ + X₂) * exp X₃
        = (exp (X₀ + X₁) * exp X₂ - exp (X₀ + X₁ + X₂))
          * exp X₃ := by
      noncomm_ring
    rw [hid]
    have hpair := exp_mul_exp_sub_exp_add_le_half_comm
      (X₀ + X₁) X₂ h₀₁ h₂ h₀₁₂
    have hcommSplit : ‖(X₀ + X₁) * X₂ - X₂ * (X₀ + X₁)‖
        ≤ ‖X₀ * X₂ - X₂ * X₀‖ + ‖X₁ * X₂ - X₂ * X₁‖ := by
      have hid₂ : (X₀ + X₁) * X₂ - X₂ * (X₀ + X₁)
          = (X₀ * X₂ - X₂ * X₀) + (X₁ * X₂ - X₂ * X₁) := by
        noncomm_ring
      rw [hid₂]
      exact norm_add_le _ _
    calc ‖(exp (X₀ + X₁) * exp X₂ - exp (X₀ + X₁ + X₂))
          * exp X₃‖
        ≤ ‖exp (X₀ + X₁) * exp X₂ - exp (X₀ + X₁ + X₂)‖
          * ‖exp X₃‖ := norm_mul_le _ _
      _ ≤ ‖(X₀ + X₁) * X₂ - X₂ * (X₀ + X₁)‖ / 2 * 1 :=
          mul_le_mul hpair hn₃ (norm_nonneg _) (by positivity)
      _ ≤ (‖X₀ * X₂ - X₂ * X₀‖ + ‖X₁ * X₂ - X₂ * X₁‖) / 2 := by
          rw [mul_one]
          linarith
  -- step 3: contract the final pair
  have hstep₃ : ‖exp (X₀ + X₁ + X₂) * exp X₃
      - exp (X₀ + X₁ + X₂ + X₃)‖
      ≤ (‖X₀ * X₃ - X₃ * X₀‖ + ‖X₁ * X₃ - X₃ * X₁‖
          + ‖X₂ * X₃ - X₃ * X₂‖) / 2 := by
    have hpair := exp_mul_exp_sub_exp_add_le_half_comm
      (X₀ + X₁ + X₂) X₃ h₀₁₂ h₃ h₀₁₂₃
    have hcommSplit : ‖(X₀ + X₁ + X₂) * X₃ - X₃ * (X₀ + X₁ + X₂)‖
        ≤ ‖X₀ * X₃ - X₃ * X₀‖ + ‖X₁ * X₃ - X₃ * X₁‖
          + ‖X₂ * X₃ - X₃ * X₂‖ := by
      have hid₃ : (X₀ + X₁ + X₂) * X₃ - X₃ * (X₀ + X₁ + X₂)
          = ((X₀ * X₃ - X₃ * X₀) + (X₁ * X₃ - X₃ * X₁))
            + (X₂ * X₃ - X₃ * X₂) := by
        noncomm_ring
      rw [hid₃]
      calc ‖(X₀ * X₃ - X₃ * X₀) + (X₁ * X₃ - X₃ * X₁)
            + (X₂ * X₃ - X₃ * X₂)‖
          ≤ ‖(X₀ * X₃ - X₃ * X₀) + (X₁ * X₃ - X₃ * X₁)‖
            + ‖X₂ * X₃ - X₃ * X₂‖ := norm_add_le _ _
        _ ≤ ‖X₀ * X₃ - X₃ * X₀‖ + ‖X₁ * X₃ - X₃ * X₁‖
            + ‖X₂ * X₃ - X₃ * X₂‖ := by
            have := norm_add_le (X₀ * X₃ - X₃ * X₀)
              (X₁ * X₃ - X₃ * X₁)
            linarith
    linarith
  -- assemble the triangle chain
  have htriangle :
      ‖exp X₀ * exp X₁ * exp X₂ * exp X₃
        - exp (X₀ + X₁ + X₂ + X₃)‖
      ≤ ‖exp X₀ * exp X₁ * exp X₂ * exp X₃
          - exp (X₀ + X₁) * exp X₂ * exp X₃‖
        + ‖exp (X₀ + X₁) * exp X₂ * exp X₃
            - exp (X₀ + X₁ + X₂) * exp X₃‖
        + ‖exp (X₀ + X₁ + X₂) * exp X₃
            - exp (X₀ + X₁ + X₂ + X₃)‖ := by
    have h₁₂ := norm_add_le
      (exp X₀ * exp X₁ * exp X₂ * exp X₃
        - exp (X₀ + X₁) * exp X₂ * exp X₃)
      (exp (X₀ + X₁) * exp X₂ * exp X₃
        - exp (X₀ + X₁ + X₂) * exp X₃)
    have h₁₂₃ := norm_add_le
      (exp X₀ * exp X₁ * exp X₂ * exp X₃
        - exp (X₀ + X₁ + X₂) * exp X₃)
      (exp (X₀ + X₁ + X₂) * exp X₃
        - exp (X₀ + X₁ + X₂ + X₃))
    have hsum₁ :
        exp X₀ * exp X₁ * exp X₂ * exp X₃
          - exp (X₀ + X₁) * exp X₂ * exp X₃
        + (exp (X₀ + X₁) * exp X₂ * exp X₃
            - exp (X₀ + X₁ + X₂) * exp X₃)
        = exp X₀ * exp X₁ * exp X₂ * exp X₃
          - exp (X₀ + X₁ + X₂) * exp X₃ := by
      abel
    have hsum₂ :
        exp X₀ * exp X₁ * exp X₂ * exp X₃
          - exp (X₀ + X₁ + X₂) * exp X₃
        + (exp (X₀ + X₁ + X₂) * exp X₃
            - exp (X₀ + X₁ + X₂ + X₃))
        = exp X₀ * exp X₁ * exp X₂ * exp X₃
          - exp (X₀ + X₁ + X₂ + X₃) := by
      abel
    rw [hsum₁] at h₁₂
    rw [hsum₂] at h₁₂₃
    linarith
  linarith

variable [NormOneClass A]

omit [NormOneClass A] in
/-- Conjugation by an involution passes through the exponential:
`w·e^z·w = e^{wzw}` when `w² = 1`. -/
theorem exp_conj_of_invol (w z : A) (hw : w * w = 1) :
    w * exp z * w = exp (w * z * w) := by
  have hpow : ∀ k : ℕ, (w * z * w) ^ k = w * z ^ k * w := by
    intro k
    induction k with
    | zero => simp [hw]
    | succ k ih =>
      rw [pow_succ, ih]
      have h₂ : w * z ^ k * w * (w * z * w)
          = w * z ^ k * (w * w) * (z * w) := by
        noncomm_ring
      rw [h₂, hw, mul_one, pow_succ]
      noncomm_ring
  have hz := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) z
  have hz' : HasSum
      (fun k : ℕ => (k.factorial : ℝ)⁻¹ • (w * z ^ k * w))
      (w * exp z * w) := by
    have h₁ := (hz.mul_left w).mul_right w
    have hfun : (fun k : ℕ =>
        w * ((k.factorial : ℝ)⁻¹ • z ^ k) * w)
        = fun k : ℕ =>
          (k.factorial : ℝ)⁻¹ • (w * z ^ k * w) := by
      funext k
      rw [mul_smul_comm, smul_mul_assoc]
    rwa [hfun] at h₁
  have htarget := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    (w * z * w)
  have htarget' : HasSum
      (fun k : ℕ => (k.factorial : ℝ)⁻¹ • (w * z ^ k * w))
      (exp (w * z * w)) := by
    have hfun : (fun k : ℕ =>
        (k.factorial : ℝ)⁻¹ • (w * z * w) ^ k)
        = fun k : ℕ =>
          (k.factorial : ℝ)⁻¹ • (w * z ^ k * w) := by
      funext k
      rw [hpow]
    rwa [hfun] at htarget
  exact hz'.unique htarget'

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- Contraction power telescoping: `‖uⁿ - vⁿ‖ ≤ n·‖u - v‖`. -/
theorem pow_sub_pow_bound (u v : A) (hu : ‖u‖ ≤ 1)
    (hv : ‖v‖ ≤ 1) (n : ℕ) :
    ‖u ^ n - v ^ n‖ ≤ n * ‖u - v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : u ^ (n + 1) - v ^ (n + 1)
        = u ^ n * (u - v) + (u ^ n - v ^ n) * v := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    rw [hid]
    have hun : ‖u ^ n‖ ≤ 1 := by
      calc ‖u ^ n‖ ≤ ‖u‖ ^ n := norm_pow_le _ _
        _ ≤ 1 := pow_le_one₀ (norm_nonneg u) hu
    calc ‖u ^ n * (u - v) + (u ^ n - v ^ n) * v‖
        ≤ ‖u ^ n * (u - v)‖ + ‖(u ^ n - v ^ n) * v‖ :=
          norm_add_le _ _
      _ ≤ ‖u ^ n‖ * ‖u - v‖ + ‖u ^ n - v ^ n‖ * ‖v‖ := by
          have := norm_mul_le (u ^ n) (u - v)
          have := norm_mul_le (u ^ n - v ^ n) v
          linarith
      _ ≤ 1 * ‖u - v‖ + (n * ‖u - v‖) * 1 := by
          have h₁ := mul_le_mul_of_nonneg_right hun
            (norm_nonneg (u - v))
          have h₂ := mul_le_mul ih hv (norm_nonneg v)
            (by positivity)
          linarith
      _ = (n + 1 : ℕ) * ‖u - v‖ := by
          push_cast
          ring

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- Two-sided contraction power telescoping through an encoder:
`‖pⁿ·ι - ι·qⁿ‖ ≤ n·‖p·ι - ι·q‖`. -/
theorem intertwine_pow_bound (p q ι : A) (hp : ‖p‖ ≤ 1)
    (hq : ‖q‖ ≤ 1) (n : ℕ) :
    ‖p ^ n * ι - ι * q ^ n‖ ≤ n * ‖p * ι - ι * q‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : p ^ (n + 1) * ι - ι * q ^ (n + 1)
        = p ^ n * (p * ι - ι * q)
          + (p ^ n * ι - ι * q ^ n) * q := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    rw [hid]
    have hpn : ‖p ^ n‖ ≤ 1 := by
      calc ‖p ^ n‖ ≤ ‖p‖ ^ n := norm_pow_le _ _
        _ ≤ 1 := pow_le_one₀ (norm_nonneg p) hp
    calc ‖p ^ n * (p * ι - ι * q)
          + (p ^ n * ι - ι * q ^ n) * q‖
        ≤ ‖p ^ n * (p * ι - ι * q)‖
          + ‖(p ^ n * ι - ι * q ^ n) * q‖ := norm_add_le _ _
      _ ≤ ‖p ^ n‖ * ‖p * ι - ι * q‖
          + ‖p ^ n * ι - ι * q ^ n‖ * ‖q‖ := by
          have := norm_mul_le (p ^ n) (p * ι - ι * q)
          have := norm_mul_le (p ^ n * ι - ι * q ^ n) q
          linarith
      _ ≤ 1 * ‖p * ι - ι * q‖
          + (n * ‖p * ι - ι * q‖) * 1 := by
          have h₁ := mul_le_mul_of_nonneg_right hpn
            (norm_nonneg (p * ι - ι * q))
          have h₂ := mul_le_mul ih hq (norm_nonneg q)
            (by positivity)
          linarith
      _ = (n + 1 : ℕ) * ‖p * ι - ι * q‖ := by
          push_cast
          ring

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- **Two-sided telescoping through an encoder**: for contraction
factors, `‖∏f·ι - ι·∏g‖ ≤ ∑ᵢ‖fᵢ·ι - ι·gᵢ‖`. -/
theorem prod_intertwine_bound (f g : ℕ → A) (ι : A) (n : ℕ)
    (hf : ∀ i < n, ‖f i‖ ≤ 1) (hg : ∀ i < n, ‖g i‖ ≤ 1) :
    ‖((List.range n).map f).prod * ι
      - ι * ((List.range n).map g).prod‖
    ≤ ∑ i ∈ Finset.range n, ‖f i * ι - ι * g i‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append,
      List.prod_append, List.prod_append]
    simp only [List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    have hid : ((List.range n).map f).prod * f n * ι
        - ι * (((List.range n).map g).prod * g n)
        = ((List.range n).map f).prod * (f n * ι - ι * g n)
          + (((List.range n).map f).prod * ι
              - ι * ((List.range n).map g).prod) * g n := by
      noncomm_ring
    rw [hid]
    have hfn : ‖((List.range n).map f).prod‖ ≤ 1 := by
      have := NCG.ChannelEstimates.prod_le_pow f 1 le_rfl n
        (fun i hi => hf i (by omega))
      simpa using this
    have hsum : ∑ i ∈ Finset.range (n + 1),
        ‖f i * ι - ι * g i‖
        = ∑ i ∈ Finset.range n, ‖f i * ι - ι * g i‖
          + ‖f n * ι - ι * g n‖ :=
      Finset.sum_range_succ _ n
    rw [hsum]
    have hih := ih (fun i hi => hf i (by omega))
      (fun i hi => hg i (by omega))
    calc ‖((List.range n).map f).prod * (f n * ι - ι * g n)
          + (((List.range n).map f).prod * ι
              - ι * ((List.range n).map g).prod) * g n‖
        ≤ ‖((List.range n).map f).prod * (f n * ι - ι * g n)‖
          + ‖(((List.range n).map f).prod * ι
              - ι * ((List.range n).map g).prod) * g n‖ :=
          norm_add_le _ _
      _ ≤ ‖((List.range n).map f).prod‖ * ‖f n * ι - ι * g n‖
          + ‖((List.range n).map f).prod * ι
              - ι * ((List.range n).map g).prod‖ * ‖g n‖ := by
          have := norm_mul_le ((List.range n).map f).prod
            (f n * ι - ι * g n)
          have := norm_mul_le
            (((List.range n).map f).prod * ι
              - ι * ((List.range n).map g).prod) (g n)
          linarith
      _ ≤ 1 * ‖f n * ι - ι * g n‖
          + (∑ i ∈ Finset.range n, ‖f i * ι - ι * g i‖) * 1 := by
          have h₁ := mul_le_mul_of_nonneg_right hfn
            (norm_nonneg (f n * ι - ι * g n))
          have h₂ := mul_le_mul hih (hg n (by omega))
            (norm_nonneg _) ?_
          · linarith
          · positivity
      _ = ∑ i ∈ Finset.range n, ‖f i * ι - ι * g i‖
          + ‖f n * ι - ι * g n‖ := by ring

omit [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- Four-factor two-sided telescoping through an encoder. -/
theorem intertwine_four_bound
    (f₀ f₁ f₂ f₃ q₀ q₁ q₂ q₃ ι : A)
    (hf₀ : ‖f₀‖ ≤ 1) (hf₁ : ‖f₁‖ ≤ 1) (hf₂ : ‖f₂‖ ≤ 1)
    (hq₁ : ‖q₁‖ ≤ 1) (hq₂ : ‖q₂‖ ≤ 1) (hq₃ : ‖q₃‖ ≤ 1) :
    ‖f₀ * f₁ * f₂ * f₃ * ι - ι * (q₀ * q₁ * q₂ * q₃)‖
      ≤ ‖f₀ * ι - ι * q₀‖ + ‖f₁ * ι - ι * q₁‖
        + ‖f₂ * ι - ι * q₂‖ + ‖f₃ * ι - ι * q₃‖ := by
  have hid : f₀ * f₁ * f₂ * f₃ * ι - ι * (q₀ * q₁ * q₂ * q₃)
      = f₀ * f₁ * f₂ * (f₃ * ι - ι * q₃)
        + f₀ * f₁ * (f₂ * ι - ι * q₂) * q₃
        + f₀ * (f₁ * ι - ι * q₁) * q₂ * q₃
        + (f₀ * ι - ι * q₀) * q₁ * q₂ * q₃ := by
    noncomm_ring
  rw [hid]
  have hf01 : ‖f₀ * f₁‖ ≤ 1 := by
    calc ‖f₀ * f₁‖ ≤ ‖f₀‖ * ‖f₁‖ := norm_mul_le _ _
      _ ≤ 1 := by nlinarith [norm_nonneg f₀, norm_nonneg f₁]
  have hf012 : ‖f₀ * f₁ * f₂‖ ≤ 1 := by
    calc ‖f₀ * f₁ * f₂‖ ≤ ‖f₀ * f₁‖ * ‖f₂‖ := norm_mul_le _ _
      _ ≤ 1 := by nlinarith [norm_nonneg (f₀ * f₁), norm_nonneg f₂]
  have t3 : ‖f₀ * f₁ * f₂ * (f₃ * ι - ι * q₃)‖
      ≤ ‖f₃ * ι - ι * q₃‖ := by
    calc ‖f₀ * f₁ * f₂ * (f₃ * ι - ι * q₃)‖
        ≤ ‖f₀ * f₁ * f₂‖ * ‖f₃ * ι - ι * q₃‖ := norm_mul_le _ _
      _ ≤ 1 * ‖f₃ * ι - ι * q₃‖ :=
          mul_le_mul_of_nonneg_right hf012 (norm_nonneg _)
      _ = ‖f₃ * ι - ι * q₃‖ := one_mul _
  have t2 : ‖f₀ * f₁ * (f₂ * ι - ι * q₂) * q₃‖
      ≤ ‖f₂ * ι - ι * q₂‖ := by
    calc ‖f₀ * f₁ * (f₂ * ι - ι * q₂) * q₃‖
        ≤ ‖f₀ * f₁ * (f₂ * ι - ι * q₂)‖ * ‖q₃‖ := norm_mul_le _ _
      _ ≤ ‖f₀ * f₁‖ * ‖f₂ * ι - ι * q₂‖ * ‖q₃‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ 1 * ‖f₂ * ι - ι * q₂‖ * 1 := by
          refine mul_le_mul ?_ hq₃ (norm_nonneg _) ?_
          · exact mul_le_mul_of_nonneg_right hf01 (norm_nonneg _)
          · positivity
      _ = ‖f₂ * ι - ι * q₂‖ := by ring
  have t1 : ‖f₀ * (f₁ * ι - ι * q₁) * q₂ * q₃‖
      ≤ ‖f₁ * ι - ι * q₁‖ := by
    calc ‖f₀ * (f₁ * ι - ι * q₁) * q₂ * q₃‖
        ≤ ‖f₀ * (f₁ * ι - ι * q₁) * q₂‖ * ‖q₃‖ := norm_mul_le _ _
      _ ≤ ‖f₀ * (f₁ * ι - ι * q₁)‖ * ‖q₂‖ * ‖q₃‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ ‖f₀‖ * ‖f₁ * ι - ι * q₁‖ * ‖q₂‖ * ‖q₃‖ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ 1 * ‖f₁ * ι - ι * q₁‖ * 1 * 1 := by
          refine mul_le_mul ?_ hq₃ (norm_nonneg _) ?_
          · refine mul_le_mul ?_ hq₂ (norm_nonneg _) ?_
            · exact mul_le_mul_of_nonneg_right hf₀ (norm_nonneg _)
            · positivity
          · positivity
      _ = ‖f₁ * ι - ι * q₁‖ := by ring
  have t0 : ‖(f₀ * ι - ι * q₀) * q₁ * q₂ * q₃‖
      ≤ ‖f₀ * ι - ι * q₀‖ := by
    calc ‖(f₀ * ι - ι * q₀) * q₁ * q₂ * q₃‖
        ≤ ‖(f₀ * ι - ι * q₀) * q₁ * q₂‖ * ‖q₃‖ := norm_mul_le _ _
      _ ≤ ‖(f₀ * ι - ι * q₀) * q₁‖ * ‖q₂‖ * ‖q₃‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ ‖f₀ * ι - ι * q₀‖ * ‖q₁‖ * ‖q₂‖ * ‖q₃‖ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ‖f₀ * ι - ι * q₀‖ * 1 * 1 * 1 := by
          refine mul_le_mul ?_ hq₃ (norm_nonneg _) ?_
          · refine mul_le_mul ?_ hq₂ (norm_nonneg _) ?_
            · exact mul_le_mul_of_nonneg_left hq₁ (norm_nonneg _)
            · positivity
          · positivity
      _ = ‖f₀ * ι - ι * q₀‖ := by ring
  calc ‖f₀ * f₁ * f₂ * (f₃ * ι - ι * q₃)
        + f₀ * f₁ * (f₂ * ι - ι * q₂) * q₃
        + f₀ * (f₁ * ι - ι * q₁) * q₂ * q₃
        + (f₀ * ι - ι * q₀) * q₁ * q₂ * q₃‖
      ≤ ‖f₀ * f₁ * f₂ * (f₃ * ι - ι * q₃)
          + f₀ * f₁ * (f₂ * ι - ι * q₂) * q₃
          + f₀ * (f₁ * ι - ι * q₁) * q₂ * q₃‖
        + ‖(f₀ * ι - ι * q₀) * q₁ * q₂ * q₃‖ := norm_add_le _ _
    _ ≤ ‖f₀ * f₁ * f₂ * (f₃ * ι - ι * q₃)
          + f₀ * f₁ * (f₂ * ι - ι * q₂) * q₃‖
        + ‖f₀ * (f₁ * ι - ι * q₁) * q₂ * q₃‖
        + ‖(f₀ * ι - ι * q₀) * q₁ * q₂ * q₃‖ := by
        have := norm_add_le
          (f₀ * f₁ * f₂ * (f₃ * ι - ι * q₃)
            + f₀ * f₁ * (f₂ * ι - ι * q₂) * q₃)
          (f₀ * (f₁ * ι - ι * q₁) * q₂ * q₃)
        linarith
    _ ≤ ‖f₀ * f₁ * f₂ * (f₃ * ι - ι * q₃)‖
        + ‖f₀ * f₁ * (f₂ * ι - ι * q₂) * q₃‖
        + ‖f₀ * (f₁ * ι - ι * q₁) * q₂ * q₃‖
        + ‖(f₀ * ι - ι * q₀) * q₁ * q₂ * q₃‖ := by
        have := norm_add_le
          (f₀ * f₁ * f₂ * (f₃ * ι - ι * q₃))
          (f₀ * f₁ * (f₂ * ι - ι * q₂) * q₃)
        linarith
    _ ≤ ‖f₃ * ι - ι * q₃‖ + ‖f₂ * ι - ι * q₂‖
        + ‖f₁ * ι - ι * q₁‖ + ‖f₀ * ι - ι * q₀‖ := by
        linarith
    _ = ‖f₀ * ι - ι * q₀‖ + ‖f₁ * ι - ι * q₁‖
        + ‖f₂ * ι - ι * q₂‖ + ‖f₃ * ι - ι * q₃‖ := by ring

/-! ### Second-order commutator machinery -/

omit [NormOneClass A] in
/-- The commutator integral representation
`[e^{s•X}, Y] = ∫₀ˢ e^{u•X}·[X,Y]·e^{(s-u)•X} du`. -/
theorem exp_comm_integral (X Y : A) (s : ℝ) :
    exp (s • X) * Y - Y * exp (s • X)
      = ∫ u in (0 : ℝ)..s,
          exp (u • X) * (X * Y - Y * X) * exp ((s - u) • X) := by
  set φ : ℝ → A :=
    fun u => exp (u • X) * Y * exp ((s - u) • X) with hφdef
  have hderiv : ∀ u : ℝ, HasDerivAt φ
      (exp (u • X) * (X * Y - Y * X) * exp ((s - u) • X)) u := by
    intro u
    have h₁ : HasDerivAt (fun u : ℝ => exp (u • X) * Y)
        (exp (u • X) * X * Y) u :=
      (hasDerivAt_exp_smul_const X u).mul_const Y
    have h₂ : HasDerivAt (fun u : ℝ => exp ((s - u) • X))
        (-(X * exp ((s - u) • X))) u := by
      have hinner : HasDerivAt (fun u : ℝ => s - u) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub s
      have h := (hasDerivAt_exp_smul_const' X (s - u)).scomp
        u hinner
      rw [neg_one_smul] at h
      exact h
    have hmul := h₁.mul h₂
    have hval : exp (u • X) * X * Y * exp ((s - u) • X)
        + exp (u • X) * Y * -(X * exp ((s - u) • X))
        = exp (u • X) * (X * Y - Y * X)
          * exp ((s - u) • X) := by
      noncomm_ring
    rw [hval] at hmul
    exact hmul
  have hφs : φ s = exp (s • X) * Y := by
    simp [hφdef, exp_zero]
  have hφ0 : φ 0 = Y * exp (s • X) := by
    simp [hφdef, exp_zero]
  have hcont : Continuous fun u : ℝ =>
      exp (u • X) * (X * Y - Y * X) * exp ((s - u) • X) := by
    refine ((continuous_expCurve X).mul continuous_const).mul ?_
    exact (continuous_expCurve X).comp
      (continuous_const.sub continuous_id)
  have hftc :
      (∫ u in (0 : ℝ)..s,
        exp (u • X) * (X * Y - Y * X) * exp ((s - u) • X))
      = φ s - φ 0 :=
    integral_eq_sub_of_hasDerivAt
      (fun u _ => hderiv u) (hcont.intervalIntegrable 0 s)
  rw [hftc, hφs, hφ0]

omit [NormOneClass A] in
/-- Contractive exponentials are within `s·‖X‖` of the
identity. -/
theorem exp_sub_one_le_contr (X : A) (s : ℝ) (hs : 0 ≤ s)
    (hX : ∀ u ∈ Icc (0 : ℝ) s, ‖exp (u • X)‖ ≤ 1) :
    ‖exp (s • X) - 1‖ ≤ s * ‖X‖ := by
  have hftc : (∫ u in (0 : ℝ)..s, X * exp (u • X))
      = exp (s • X) - 1 := by
    have h := integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => exp (u • X))
      (f' := fun u : ℝ => X * exp (u • X))
      (fun u _ => hasDerivAt_exp_smul_const' X u)
      ((continuous_const.mul
        (continuous_expCurve X)).intervalIntegrable 0 s)
    rw [h]
    simp [exp_zero]
  rw [← hftc]
  have hbound : ∀ u ∈ uIoc (0 : ℝ) s,
      ‖X * exp (u • X)‖ ≤ ‖X‖ := by
    intro u hu
    rw [uIoc_of_le hs] at hu
    calc ‖X * exp (u • X)‖ ≤ ‖X‖ * ‖exp (u • X)‖ :=
          norm_mul_le _ _
      _ ≤ ‖X‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (hX u ⟨hu.1.le, hu.2⟩) (norm_nonneg _)
      _ = ‖X‖ := mul_one _
  calc ‖∫ u in (0 : ℝ)..s, X * exp (u • X)‖
      ≤ ‖X‖ * |s - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          hbound
    _ = s * ‖X‖ := by
        rw [sub_zero, abs_of_nonneg hs]
        ring

section GroupCommutator

variable [NormedAlgebra ℚ A]

omit [NormOneClass A] in
/-- **Second-order commutator expansion**:
`‖[e^{s•X}, Y] - s•[X,Y]‖ ≤ 2s²·‖X‖·‖[X,Y]‖` for contractive
exponentials. -/
theorem comm_exp_second_order (X Y : A) (s : ℝ) (hs : 0 ≤ s)
    (hX : ∀ u ∈ Icc (0 : ℝ) s, ‖exp (u • X)‖ ≤ 1) :
    ‖exp (s • X) * Y - Y * exp (s • X)
        - s • (X * Y - Y * X)‖
      ≤ 2 * s ^ 2 * ‖X‖ * ‖X * Y - Y * X‖ := by
  set K : A := X * Y - Y * X with hK
  have hrep := exp_comm_integral X Y s
  have hconst : (∫ _u in (0 : ℝ)..s, K) = s • K := by
    rw [intervalIntegral.integral_const, sub_zero]
  have hcont : Continuous fun u : ℝ =>
      exp (u • X) * K * exp ((s - u) • X) := by
    refine ((continuous_expCurve X).mul continuous_const).mul ?_
    exact (continuous_expCurve X).comp
      (continuous_const.sub continuous_id)
  have hsub : exp (s • X) * Y - Y * exp (s • X) - s • K
      = ∫ u in (0 : ℝ)..s,
          (exp (u • X) * K * exp ((s - u) • X) - K) := by
    rw [intervalIntegral.integral_sub
      (hcont.intervalIntegrable 0 s)
      (continuous_const.intervalIntegrable 0 s),
      hconst, ← hrep]
  rw [hsub]
  have hbound : ∀ u ∈ Ioc (0 : ℝ) s,
      ‖exp (u • X) * K * exp ((s - u) • X) - K‖
        ≤ 2 * ‖X‖ * ‖K‖ * u + s * ‖X‖ * ‖K‖ := by
    intro u hu
    have hu0 : (0 : ℝ) ≤ u := hu.1.le
    have hus : u ≤ s := hu.2
    have hmerge : exp (u • X) * exp ((s - u) • X)
        = exp (s • X) := by
      have hcomm : Commute (u • X) ((s - u) • X) :=
        ((Commute.refl X).smul_left u).smul_right (s - u)
      rw [← exp_add_of_commute hcomm]
      congr 1
      module
    have hid : exp (u • X) * K * exp ((s - u) • X) - K
        = (exp (u • X) * K - K * exp (u • X))
            * exp ((s - u) • X)
          + K * (exp (u • X) * exp ((s - u) • X) - 1) := by
      noncomm_ring
    rw [hid]
    have hcommle := exp_comm_le X K u hu0
      (fun v hv => hX v ⟨hv.1, hv.2.trans hus⟩)
    have hXK : ‖X * K - K * X‖ ≤ 2 * ‖X‖ * ‖K‖ := by
      have hm₁ := norm_mul_le X K
      have hm₂ := norm_mul_le K X
      have hm₃ := norm_sub_le (X * K) (K * X)
      linarith
    have hexps : ‖exp ((s - u) • X)‖ ≤ 1 :=
      hX (s - u) ⟨by linarith, by linarith⟩
    have h₁ : ‖(exp (u • X) * K - K * exp (u • X))
        * exp ((s - u) • X)‖ ≤ 2 * ‖X‖ * ‖K‖ * u := by
      have hstep : ‖exp (u • X) * K - K * exp (u • X)‖
          ≤ u * (2 * ‖X‖ * ‖K‖) :=
        hcommle.trans (mul_le_mul_of_nonneg_left hXK hu0)
      calc ‖(exp (u • X) * K - K * exp (u • X))
            * exp ((s - u) • X)‖
          ≤ ‖exp (u • X) * K - K * exp (u • X)‖
            * ‖exp ((s - u) • X)‖ := norm_mul_le _ _
        _ ≤ (u * (2 * ‖X‖ * ‖K‖)) * 1 := by
            refine mul_le_mul hstep hexps (norm_nonneg _) ?_
            positivity
        _ = 2 * ‖X‖ * ‖K‖ * u := by ring
    have h₂ : ‖K * (exp (u • X) * exp ((s - u) • X) - 1)‖
        ≤ s * ‖X‖ * ‖K‖ := by
      rw [hmerge]
      have hone := exp_sub_one_le_contr X s hs hX
      calc ‖K * (exp (s • X) - 1)‖
          ≤ ‖K‖ * ‖exp (s • X) - 1‖ := norm_mul_le _ _
        _ ≤ ‖K‖ * (s * ‖X‖) :=
            mul_le_mul_of_nonneg_left hone (norm_nonneg _)
        _ = s * ‖X‖ * ‖K‖ := by ring
    calc ‖(exp (u • X) * K - K * exp (u • X))
          * exp ((s - u) • X)
          + K * (exp (u • X) * exp ((s - u) • X) - 1)‖
        ≤ ‖(exp (u • X) * K - K * exp (u • X))
            * exp ((s - u) • X)‖
          + ‖K * (exp (u • X) * exp ((s - u) • X) - 1)‖ :=
          norm_add_le _ _
      _ ≤ 2 * ‖X‖ * ‖K‖ * u + s * ‖X‖ * ‖K‖ := by
          linarith
  have hlin : IntervalIntegrable
      (fun u : ℝ => 2 * ‖X‖ * ‖K‖ * u)
      MeasureTheory.volume 0 s := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hgint : IntervalIntegrable
      (fun u : ℝ => 2 * ‖X‖ * ‖K‖ * u + s * ‖X‖ * ‖K‖)
      MeasureTheory.volume 0 s :=
    hlin.add (intervalIntegrable_const)
  calc ‖∫ u in (0 : ℝ)..s,
        (exp (u • X) * K * exp ((s - u) • X) - K)‖
      ≤ ∫ u in (0 : ℝ)..s,
          (2 * ‖X‖ * ‖K‖ * u + s * ‖X‖ * ‖K‖) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hs
          (MeasureTheory.ae_of_all _ fun u hu => hbound u hu)
          hgint
    _ = 2 * s ^ 2 * ‖X‖ * ‖K‖ := by
        rw [intervalIntegral.integral_add hlin
          (intervalIntegrable_const),
          intervalIntegral.integral_const_mul, integral_id,
          intervalIntegral.integral_const]
        ring

end GroupCommutator

end SharpTrotter
end NCG
