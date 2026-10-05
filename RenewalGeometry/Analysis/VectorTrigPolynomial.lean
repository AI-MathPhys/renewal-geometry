/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TrigBernsteinSup

/-!
# Vector-valued real trigonometric polynomials on `ℝ^d`: derivatives, tails and Bernstein

Generic infrastructure (no renewal notions) for the measured-leakage estimates of the
Einstein–Standard-Model action-closure manuscript (`app:native-tails`, `lem:native-tail-transfer`,
`thm:native-source`): the reconstruction of a real record with values in a real normed space `V`
on the periodic box of period `2π` is a real trigonometric polynomial
`P(x) = Σ_{ℓ ∈ S} (cos(ℓ·x) a_ℓ + sin(ℓ·x) b_ℓ)`, `S ⊂ ℤ^d` finite, `a_ℓ, b_ℓ ∈ V`
(`tp S c`, `c ℓ = (a_ℓ, b_ℓ)`), the real form of `Σ_ℓ û(ℓ) e^{iℓ·x}`.

`ℝ^d = Fin d → ℝ` carries the sup norm; iterated derivatives are Mathlib's `iteratedFDeriv`
(operator norms).

## Main results

* `hasFDerivAt_tp`, `fderiv_tp_apply`: `DP(x)v = Σ_μ v_μ ∂_μP(x)` with `∂_μP = tp S (dco μ c)`,
  `dco μ c ℓ = (ℓ_μ b_ℓ, -ℓ_μ a_ℓ)` (again a trigonometric polynomial on the same frequencies);
  `contDiff_tp`.
* `norm_iteratedFDeriv_tp_le_Bd`: `‖D^jP(x)‖ ≤ Bd j c x`, the sum over all `j`-fold iterated
  coordinate derivatives of `‖∂_{μ₁}⋯∂_{μ_j}P(x)‖`.
* **`norm_iteratedFDeriv_tp_le`** (termwise / tail bound): `‖D^jP(x)‖ ≤ Σ_ℓ |ℓ|₁^j (|a_ℓ| + |b_ℓ|)`.
* **`norm_tp_dco_le`** (Bernstein along a coordinate, sup norm): if `|P| ≤ M` on `ℝ^d` and every
  frequency has `|ℓ_μ| ≤ K`, then `|∂_μP| ≤ 60 K M` (via a norming functional and the
  one-dimensional `TrigBernstein.norm_trigDeriv_le` along the line `t ↦ x + t e_μ`).
* **`norm_iteratedFDeriv_tp_le_bernstein`**: if `|P| ≤ M` and every frequency has `|ℓ|_∞ ≤ K`, then
  `‖D^jP(x)‖ ≤ (60 d K)^j M` for every `j` and `x`.
-/

open Finset

namespace RenewalGeometry.VecTrig

noncomputable section

set_option linter.unusedSectionVars false

variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Phases and trigonometric polynomials -/

/-- The phase `ℓ·x = Σ_μ ℓ_μ x_μ`. -/
def phase (ℓ : Fin d → ℤ) (x : Fin d → ℝ) : ℝ := ∑ μ, (ℓ μ : ℝ) * x μ

/-- The phase as a continuous linear functional. -/
def phaseL (ℓ : Fin d → ℤ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ μ, (ℓ μ : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) μ

theorem phaseL_apply (ℓ : Fin d → ℤ) (x : Fin d → ℝ) : phaseL ℓ x = phase ℓ x := by
  simp [phaseL, phase]

theorem phase_eq_phaseL (ℓ : Fin d → ℤ) : phase ℓ = phaseL ℓ := by
  funext x; exact (phaseL_apply ℓ x).symm

theorem phase_add_single (ℓ : Fin d → ℤ) (x : Fin d → ℝ) (μ : Fin d) (t : ℝ) :
    phase ℓ (x + t • Pi.single μ 1) = phase ℓ x + (ℓ μ : ℝ) * t := by
  unfold phase
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν; simp [Pi.single_apply, hν]
  · simp

/-- Coefficients `ℓ ↦ (a_ℓ, b_ℓ)`. -/
abbrev Coef (d : ℕ) (V : Type*) := (Fin d → ℤ) → V × V

/-- The trigonometric polynomial `P(x) = Σ_{ℓ ∈ S} (cos(ℓ·x) a_ℓ + sin(ℓ·x) b_ℓ)`. -/
def tp (S : Finset (Fin d → ℤ)) (c : Coef d V) (x : Fin d → ℝ) : V :=
  ∑ ℓ ∈ S, (Real.cos (phase ℓ x) • (c ℓ).1 + Real.sin (phase ℓ x) • (c ℓ).2)

/-- The coefficients of the coordinate derivative `∂_μP`: `(ℓ_μ b_ℓ, -ℓ_μ a_ℓ)`. -/
def dco (μ : Fin d) (c : Coef d V) : Coef d V :=
  fun ℓ => ((ℓ μ : ℝ) • (c ℓ).2, -((ℓ μ : ℝ) • (c ℓ).1))

/-- The coefficient size `|a_ℓ| + |b_ℓ|`. -/
def cn (c : Coef d V) (ℓ : Fin d → ℤ) : ℝ := ‖(c ℓ).1‖ + ‖(c ℓ).2‖

theorem cn_nonneg (c : Coef d V) (ℓ : Fin d → ℤ) : 0 ≤ cn c ℓ := by unfold cn; positivity

theorem cn_dco (μ : Fin d) (c : Coef d V) (ℓ : Fin d → ℤ) :
    cn (dco μ c) ℓ = |(ℓ μ : ℝ)| * cn c ℓ := by
  simp only [cn, dco, norm_neg, norm_smul, Real.norm_eq_abs]; ring

/-- `|ℓ|₁ = Σ_μ |ℓ_μ|`. -/
def l1 (ℓ : Fin d → ℤ) : ℝ := ∑ μ, |(ℓ μ : ℝ)|

theorem l1_nonneg (ℓ : Fin d → ℤ) : 0 ≤ l1 ℓ := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem norm_tp_le (S : Finset (Fin d → ℤ)) (c : Coef d V) (x : Fin d → ℝ) :
    ‖tp S c x‖ ≤ ∑ ℓ ∈ S, cn c ℓ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓ _ => ?_)
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, Real.norm_eq_abs, cn]
  gcongr
  · exact (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _))
  · exact (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _))

theorem tp_add (S : Finset (Fin d → ℤ)) (c c' : Coef d V) (x : Fin d → ℝ) :
    tp S (c + c') x = tp S c x + tp S c' x := by
  simp only [tp, Pi.add_apply, Prod.fst_add, Prod.snd_add, smul_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  abel

theorem tp_sub (S : Finset (Fin d → ℤ)) (c c' : Coef d V) (x : Fin d → ℝ) :
    tp S (c - c') x = tp S c x - tp S c' x := by
  simp only [tp, Pi.sub_apply, Prod.fst_sub, Prod.snd_sub, smul_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  abel

theorem dco_sub (μ : Fin d) (c c' : Coef d V) : dco μ (c - c') = dco μ c - dco μ c' := by
  funext ℓ; simp only [dco, Pi.sub_apply, Prod.fst_sub, Prod.snd_sub, smul_sub, Prod.mk_sub_mk]
  congr 1; abel

/-- Restriction of the frequency support: `tp` over `S` of `c` agrees with `tp` over `T ⊇ S` when
`c` vanishes on `T \ S`. -/
theorem tp_subset {S T : Finset (Fin d → ℤ)} (hST : S ⊆ T) (c : Coef d V)
    (hc : ∀ ℓ ∈ T, ℓ ∉ S → c ℓ = 0) (x : Fin d → ℝ) : tp S c x = tp T c x := by
  unfold tp
  refine Finset.sum_subset hST fun ℓ hT hS => ?_
  rw [hc ℓ hT hS]; simp

/-! ### Smoothness and the first derivative -/

theorem contDiff_tp (S : Finset (Fin d → ℤ)) (c : Coef d V) {n : WithTop ℕ∞} :
    ContDiff ℝ n (tp S c) := by
  unfold tp
  refine ContDiff.sum fun ℓ _ => ?_
  rw [phase_eq_phaseL]
  exact ((Real.contDiff_cos.comp (phaseL ℓ).contDiff).smul contDiff_const).add
    ((Real.contDiff_sin.comp (phaseL ℓ).contDiff).smul contDiff_const)

theorem hasFDerivAt_tp_aux (S : Finset (Fin d → ℤ)) (c : Coef d V) (x : Fin d → ℝ) :
    HasFDerivAt (tp S c) (∑ ℓ ∈ S, (((-Real.sin (phase ℓ x)) • phaseL ℓ).smulRight (c ℓ).1 +
      (Real.cos (phase ℓ x) • phaseL ℓ).smulRight (c ℓ).2)) x := by
  unfold tp
  refine HasFDerivAt.fun_sum fun ℓ _ => ?_
  have hL : HasFDerivAt (phase ℓ) (phaseL ℓ) x := by
    rw [phase_eq_phaseL]; exact (phaseL ℓ).hasFDerivAt
  exact (hL.cos.smul_const (c ℓ).1).add (hL.sin.smul_const (c ℓ).2)

/-- `DP(x)v = Σ_μ v_μ ∂_μP(x)`. -/
theorem fderiv_tp_apply (S : Finset (Fin d → ℤ)) (c : Coef d V) (x v : Fin d → ℝ) :
    fderiv ℝ (tp S c) x v = ∑ μ, v μ • tp S (dco μ c) x := by
  rw [(hasFDerivAt_tp_aux S c x).fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, phaseL_apply, tp, dco,
    smul_eq_mul]
  simp only [phase, Finset.smul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul, smul_add,
    smul_neg, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro μ _
  module

/-- The first derivative as a function: `DP = Σ_μ (e_μ^* ⊗ ∂_μP)`. -/
theorem fderiv_tp (S : Finset (Fin d → ℤ)) (c : Coef d V) :
    fderiv ℝ (tp S c) = fun x => ∑ μ, ContinuousLinearMap.smulRightL ℝ (Fin d → ℝ) V
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) μ) (tp S (dco μ c) x) := by
  funext x
  ext v
  rw [fderiv_tp_apply]
  simp

theorem norm_proj_le (μ : Fin d) :
    ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) μ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]; exact norm_le_pi_norm v μ

theorem norm_smulRightL_proj_le (μ : Fin d) :
    ‖ContinuousLinearMap.smulRightL ℝ (Fin d → ℝ) V
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) μ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.norm_smulRight_apply, one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_proj_le μ)

/-! ### Iterated derivatives -/

/-- The sum over all `j`-fold iterated coordinate derivatives of `‖∂_{μ₁}⋯∂_{μ_j}P(x)‖`. -/
def Bd (S : Finset (Fin d → ℤ)) : ℕ → Coef d V → (Fin d → ℝ) → ℝ
  | 0, c, x => ‖tp S c x‖
  | j + 1, c, x => ∑ μ, Bd S j (dco μ c) x

theorem norm_iteratedFDeriv_tp_le_Bd (S : Finset (Fin d → ℤ)) (j : ℕ) :
    ∀ (c : Coef d V) (x : Fin d → ℝ), ‖iteratedFDeriv ℝ j (tp S c) x‖ ≤ Bd S j c x := by
  induction j with
  | zero => intro c x; rw [norm_iteratedFDeriv_zero]; rfl
  | succ j ih =>
    intro c x
    rw [← norm_iteratedFDeriv_fderiv, fderiv_tp, Bd]
    set L : Fin d → V →L[ℝ] ((Fin d → ℝ) →L[ℝ] V) := fun μ =>
      ContinuousLinearMap.smulRightL ℝ (Fin d → ℝ) V
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) μ) with hL
    rw [iteratedFDeriv_sum (f := fun (μ : Fin d) (y : Fin d → ℝ) => L μ (tp S (dco μ c) y))
      (fun μ _ => by exact (L μ).contDiff.comp (contDiff_tp S (dco μ c)))]
    rw [Finset.sum_apply]
    apply le_trans (norm_sum_le _ _)
    refine Finset.sum_le_sum fun μ _ => ?_
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (L μ)
      ((contDiff_tp S (dco μ c) (n := ⊤)).contDiffAt (x := x)) (n := j) (by exact_mod_cast le_top)
    have e : iteratedFDeriv ℝ j (fun y => L μ (tp S (dco μ c) y)) x =
        iteratedFDeriv ℝ j (⇑(L μ) ∘ tp S (dco μ c)) x := rfl
    rw [e]
    refine h.trans ?_
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_smulRightL_proj_le μ)).trans (ih _ x)

theorem Bd_le_l1 (S : Finset (Fin d → ℤ)) (j : ℕ) :
    ∀ (c : Coef d V) (x : Fin d → ℝ), Bd S j c x ≤ ∑ ℓ ∈ S, l1 ℓ ^ j * cn c ℓ := by
  induction j with
  | zero => intro c x; simpa [Bd] using norm_tp_le S c x
  | succ j ih =>
    intro c x
    rw [Bd]
    refine (Finset.sum_le_sum fun μ _ => ih (dco μ c) x).trans (le_of_eq ?_)
    simp only [cn_dco]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [pow_succ, l1, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring

/-- **Termwise derivative bound**: `‖D^jP(x)‖ ≤ Σ_{ℓ ∈ S} |ℓ|₁^j (|a_ℓ| + |b_ℓ|)`. -/
theorem norm_iteratedFDeriv_tp_le (S : Finset (Fin d → ℤ)) (c : Coef d V) (j : ℕ)
    (x : Fin d → ℝ) : ‖iteratedFDeriv ℝ j (tp S c) x‖ ≤ ∑ ℓ ∈ S, l1 ℓ ^ j * cn c ℓ :=
  (norm_iteratedFDeriv_tp_le_Bd S j c x).trans (Bd_le_l1 S j c x)

/-! ### Bernstein's inequality along a coordinate -/

/-- `cos(θ + s) α + sin(θ + s) β = ½(α - iβ)e^{iθ}e^{is} + ½(α + iβ)e^{-iθ}e^{-is}`. -/
theorem cos_sin_eq_exp (α β θ s : ℝ) :
    ((Real.cos (θ + s) * α + Real.sin (θ + s) * β : ℝ) : ℂ) =
      ((α : ℂ) - (β : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) / 2 *
          Complex.exp ((s : ℂ) * Complex.I) +
        ((α : ℂ) + (β : ℂ) * Complex.I) * Complex.exp (-(θ : ℂ) * Complex.I) / 2 *
          Complex.exp (-(s : ℂ) * Complex.I) := by
  have hc := Complex.two_cos ((θ + s : ℝ) : ℂ)
  have hs := Complex.two_sin ((θ + s : ℝ) : ℂ)
  have e1 : Complex.exp (((θ + s : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((s : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : Complex.exp (-((θ + s : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp (-(s : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e1, e2] at hc hs
  push_cast
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at *
  push_cast at hc hs ⊢
  linear_combination (α / 2 : ℂ) * hc + (β / 2 : ℂ) * hs

/-- **Bernstein's inequality along a coordinate** (sup norm, vector valued): if `|P| ≤ M` on `ℝ^d`
and `|ℓ_μ| ≤ K` for every frequency `ℓ ∈ S`, then `|∂_μP(x)| ≤ 60 K M` for every `x`. -/
theorem norm_tp_dco_le (S : Finset (Fin d → ℤ)) (c : Coef d V) {K : ℕ} (μ : Fin d)
    (hS : ∀ ℓ ∈ S, |(ℓ μ : ℝ)| ≤ K) {M : ℝ} (hM : ∀ y, ‖tp S c y‖ ≤ M) (x : Fin d → ℝ) :
    ‖tp S (dco μ c) x‖ ≤ 60 * K * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set v := tp S (dco μ c) x with hv
  by_cases hv0 : v = 0
  · rw [hv0, norm_zero]; positivity
  obtain ⟨φ, hφ1, hφv⟩ := exists_dual_vector ℝ v (norm_ne_zero_iff.mpr hv0)
  -- the line `t ↦ x + t e_μ`
  set e : Fin d → ℝ := Pi.single μ 1
  set J := {ℓ // ℓ ∈ S} × Bool
  let dd : J → ℂ := fun j => if j.2 then
      ((φ (c j.1).1 : ℂ) - (φ (c j.1).2 : ℂ) * Complex.I) *
        Complex.exp ((phase j.1 x : ℂ) * Complex.I) / 2
    else ((φ (c j.1).1 : ℂ) + (φ (c j.1).2 : ℂ) * Complex.I) *
        Complex.exp (-(phase j.1 x : ℂ) * Complex.I) / 2
  let mm : J → ℤ := fun j => if j.2 then j.1.1 μ else -(j.1.1 μ)
  have hline : ∀ t : ℝ, TrigBernstein.tsum' dd mm t = ((φ (tp S c (x + t • e)) : ℝ) : ℂ) := by
    intro t
    unfold TrigBernstein.tsum'
    rw [Fintype.sum_prod_type, tp, map_sum, Complex.ofReal_sum, ← Finset.sum_attach S,
      Finset.attach_eq_univ]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Fintype.sum_bool]
    show ((φ (c ℓ).1 : ℂ) - (φ (c ℓ).2 : ℂ) * Complex.I) *
          Complex.exp ((phase ℓ.1 x : ℂ) * Complex.I) / 2 *
          Complex.exp (((ℓ.1 μ : ℤ) : ℂ) * (t : ℂ) * Complex.I) +
        ((φ (c ℓ).1 : ℂ) + (φ (c ℓ).2 : ℂ) * Complex.I) *
          Complex.exp (-(phase ℓ.1 x : ℂ) * Complex.I) / 2 *
          Complex.exp (((-(ℓ.1 μ) : ℤ) : ℂ) * (t : ℂ) * Complex.I) = _
    rw [phase_add_single, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      cos_sin_eq_exp]
    push_cast
    ring_nf
  have hder : HasDerivAt (fun t : ℝ => ((φ (tp S c (x + t • e)) : ℝ) : ℂ))
      ((φ v : ℝ) : ℂ) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
    have h2 := (hasFDerivAt_tp_aux S c x).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    have h3 := (φ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2).ofReal_comp
    have hval : (∑ ℓ ∈ S, (((-Real.sin (phase ℓ x)) • phaseL ℓ).smulRight (c ℓ).1 +
        (Real.cos (phase ℓ x) • phaseL ℓ).smulRight (c ℓ).2)) e = v := by
      rw [← (hasFDerivAt_tp_aux S c x).fderiv, fderiv_tp_apply, hv]
      rw [Finset.sum_eq_single μ]
      · simp [e]
      · intro ν _ hν; simp [e, Pi.single_apply, hν]
      · simp
    have hfun : (fun t : ℝ => ((φ (tp S c (x + t • e)) : ℝ) : ℂ)) =
        (fun y => ((((⇑φ ∘ tp S c) ∘ fun t => x + t • e) y : ℝ) : ℂ)) := rfl
    rw [hfun]
    refine h3.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hval]
  have heq : TrigBernstein.tsumDeriv dd mm 0 = ((φ v : ℝ) : ℂ) := by
    have hfun : TrigBernstein.tsum' dd mm = fun t : ℝ => ((φ (tp S c (x + t • e)) : ℝ) : ℂ) :=
      funext hline
    have := TrigBernstein.hasDerivAt_tsum' dd mm 0
    rw [hfun] at this
    exact this.unique hder
  have hmK : ∀ j, |(mm j : ℝ)| ≤ K := by
    intro j
    simp only [mm]
    split_ifs
    · exact hS _ j.1.2
    · push_cast; rw [abs_neg]; exact hS _ j.1.2
  have hMline : ∀ s, ‖TrigBernstein.tsum' dd mm s‖ ≤ M := by
    intro s
    rw [hline, Complex.norm_real, Real.norm_eq_abs]
    refine (φ.le_opNorm _).trans ?_
    rw [hφ1, one_mul]; exact hM _
  have hB := TrigBernstein.norm_trigDeriv_le dd mm hmK hMline 0
  have hφv' : φ v = ‖v‖ := by simpa using hφv
  rw [heq, Complex.norm_real, Real.norm_eq_abs, hφv', abs_of_nonneg (norm_nonneg _)] at hB
  exact hB

/-- **Bernstein's inequality for all derivatives** (sup norm, vector valued): if `|P| ≤ M` on
`ℝ^d` and every frequency `ℓ ∈ S` has `|ℓ|_∞ ≤ K`, then `‖D^jP(x)‖ ≤ (60 d K)^j M`. -/
theorem norm_iteratedFDeriv_tp_le_bernstein (S : Finset (Fin d → ℤ)) {K : ℕ}
    (hS : ∀ ℓ ∈ S, ∀ μ, |(ℓ μ : ℝ)| ≤ K) (j : ℕ) :
    ∀ (c : Coef d V) {M : ℝ}, (∀ y, ‖tp S c y‖ ≤ M) → ∀ x,
      ‖iteratedFDeriv ℝ j (tp S c) x‖ ≤ (60 * d * K) ^ j * M := by
  have key : ∀ j : ℕ, ∀ (c : Coef d V) {M : ℝ}, (∀ y, ‖tp S c y‖ ≤ M) → ∀ x,
      Bd S j c x ≤ (60 * d * K) ^ j * M := by
    intro j
    induction j with
    | zero => intro c M hM x; simpa [Bd] using hM x
    | succ j ih =>
      intro c M hM x
      rw [Bd]
      calc ∑ μ, Bd S j (dco μ c) x ≤ ∑ _μ : Fin d, (60 * d * K) ^ j * (60 * K * M) :=
            Finset.sum_le_sum fun μ _ =>
              ih (dco μ c) (fun y => norm_tp_dco_le S c μ (fun ℓ hℓ => hS ℓ hℓ μ) hM y) x
        _ = (60 * d * K) ^ (j + 1) * M := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_succ]
            ring
  intro c M hM x
  exact (norm_iteratedFDeriv_tp_le_Bd S j c x).trans (key j c hM x)

end

end RenewalGeometry.VecTrig
