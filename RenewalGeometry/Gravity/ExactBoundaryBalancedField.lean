/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The balanced field of an amplitude-graded unbalanced chart

Emergent-spacetime manuscript, `ass:supp-graded-exact-chart` item (C3) and
`lem:supp-exact-balanced-field`.

Item (C3) of the graded chart writes the constrained field, in unbalanced free coordinates
`v = (v_s, v_f)` and slow time `s = t/a³`, as (`eq:supp-exact-unbalanced-field`)
`v_s' = a³ b_s + R_s(a, v)`, `v_f' = C_red v_s + B v_f + a³ b_w + R_f(a, v)`,
with the graded remainder bounds `eq:supp-exact-graded-remainders` and the transport identity
`C_red b_s + B b_w = 0`.  `ExactBoundaryChart.UnbalancedField` carries these data (`R_s, R_f` with
their derivatives) and `ExactBoundaryChart.Graded` the identity and the four bounds on a common
neighbourhood `0 < a < a₀`, `‖v‖ ≤ ρ₀`.

The balanced field is the conjugate by `diag(aI, I)` (the proof of the lemma:
"Conjugate (C3) by diag(aI₂₉₄, I₂₉)"): `𝓗_a(w) = diag(a⁻¹, 1) V(a, diag(a, 1) w)`, and the
reference is `w_ref(s) = s ω_a`, `ω_a = (a² b_s, a³ b_w)` (`eq:supp-exact-reference`).
Proved here (`lem:supp-exact-balanced-field`, the clauses that follow from (C3)):

* `ExactBoundaryChart.hasFDerivAt_Hbal`: `𝓗_a` is differentiable on the tube with the explicit
  derivative `DHbal`;
* `ExactBoundaryChart.norm_DHbal_sub_le`: `‖D_w𝓗_a - D‖ ≤ C_{M₀} a` on `‖w‖ ≤ M₀ a`, with
  `D = diag(0, B)` and `C_{M₀} = ‖C_red‖ + C(1 + M₀)`;
* `ExactBoundaryChart.norm_src_le`: `‖f_a(s)‖ ≤ C(1 + cβ + c²β²) a³` for `0 ≤ s`, `s a ≤ c`;
* `ExactBoundaryChart.norm_src_deriv_le`: `‖f_a'(s)‖ = ‖D𝓗_a(w_ref(s)) ω_a‖ ≤ C(1 + cβ) β a⁴`;
* `ExactBoundaryChart.norm_wref_le`, `ExactBoundaryChart.norm_omega_le`:
  `‖w_ref(s)‖ ≤ cβ a`, `‖w_ref'‖ ≤ β a²` (`β = ‖(b_s, b_w)‖`).

Not derivable from (C3) as written (kept open): the bounds `‖D^j𝓗_a‖ ≤ C_j` for `2 ≤ j ≤ 4`
(they need the analytic divisibility of the slow remainder by `a` with Cauchy estimates, which the
manuscript asserts but (C3) does not quantify) and the extra `a²` of the canonical row
`(𝓗_a)_q = aΛF(Θ_a(w))` (it needs (C2), (C4) and `lem:supp-exact-normal-coordinates`).
-/

open Set Metric

namespace RenewalGeometry
namespace ExactBoundaryChart

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {Es Ef : Type*} [NormedAddCommGroup Es] [NormedSpace ℝ Es] [NormedAddCommGroup Ef]
  [NormedSpace ℝ Ef]

/-- The balancing map `w = (x, y) ↦ v = (a x, y)`. -/
def balL (a : ℝ) : Es × Ef →L[ℝ] Es × Ef :=
  (a • ContinuousLinearMap.fst ℝ Es Ef).prod (ContinuousLinearMap.snd ℝ Es Ef)

/-- The data of the unbalanced constrained field of item (C3): sources `b_s, b_w`, the reduced
coupling `C_red`, the weak block `B`, the remainders `R_s, R_f` and their derivatives in `v`. -/
structure UnbalancedField (Es Ef : Type*) [NormedAddCommGroup Es] [NormedSpace ℝ Es]
    [NormedAddCommGroup Ef] [NormedSpace ℝ Ef] where
  bs : Es
  bw : Ef
  Cred : Es →L[ℝ] Ef
  B : Ef →L[ℝ] Ef
  Rs : ℝ → Es × Ef → Es
  Rf : ℝ → Es × Ef → Ef
  DRs : ℝ → Es × Ef → (Es × Ef →L[ℝ] Es)
  DRf : ℝ → Es × Ef → (Es × Ef →L[ℝ] Ef)

/-- The graded hypotheses of item (C3) on the common neighbourhood `0 < a < a₀`, `‖v‖ ≤ ρ₀`:
transport identity, differentiability of the remainders, and `eq:supp-exact-graded-remainders`. -/
structure Graded (V : UnbalancedField Es Ef) (C ρ₀ a₀ : ℝ) : Prop where
  C_nonneg : 0 ≤ C
  transport : V.Cred V.bs + V.B V.bw = 0
  hasDeriv_s : ∀ a ∈ Ioo 0 a₀, ∀ v : Es × Ef, ‖v‖ ≤ ρ₀ → HasFDerivAt (V.Rs a) (V.DRs a v) v
  hasDeriv_f : ∀ a ∈ Ioo 0 a₀, ∀ v : Es × Ef, ‖v‖ ≤ ρ₀ → HasFDerivAt (V.Rf a) (V.DRf a v) v
  Rs_le : ∀ a ∈ Ioo 0 a₀, ∀ v : Es × Ef, ‖v‖ ≤ ρ₀ →
    ‖V.Rs a v‖ ≤ C * (a ^ 4 + a ^ 2 * ‖v‖ + a * ‖v‖ ^ 2)
  DRs_le : ∀ a ∈ Ioo 0 a₀, ∀ v : Es × Ef, ‖v‖ ≤ ρ₀ → ‖V.DRs a v‖ ≤ C * (a ^ 2 + a * ‖v‖)
  Rf_le : ∀ a ∈ Ioo 0 a₀, ∀ v : Es × Ef, ‖v‖ ≤ ρ₀ →
    ‖V.Rf a v‖ ≤ C * (a ^ 4 + a * ‖v‖ + ‖v‖ ^ 2)
  DRf_le : ∀ a ∈ Ioo 0 a₀, ∀ v : Es × Ef, ‖v‖ ≤ ρ₀ → ‖V.DRf a v‖ ≤ C * (a + ‖v‖)

namespace UnbalancedField

variable (V : UnbalancedField Es Ef)

/-- The unbalanced field `eq:supp-exact-unbalanced-field`. -/
def field (a : ℝ) (v : Es × Ef) : Es × Ef :=
  (a ^ 3 • V.bs + V.Rs a v, V.Cred v.1 + V.B v.2 + a ^ 3 • V.bw + V.Rf a v)

/-- The linear part `D = diag(0₂₉₄, B)`. -/
def Dlin : Es × Ef →L[ℝ] Es × Ef :=
  (0 : Es × Ef →L[ℝ] Es).prod (V.B.comp (ContinuousLinearMap.snd ℝ Es Ef))

/-- The balanced field `𝓗_a(w) = diag(a⁻¹, 1) V(a, diag(a, 1) w)`. -/
def Hbal (a : ℝ) (w : Es × Ef) : Es × Ef :=
  (a⁻¹ • (V.field a (balL a w)).1, (V.field a (balL a w)).2)

/-- Its derivative. -/
def DHbal (a : ℝ) (w : Es × Ef) : Es × Ef →L[ℝ] Es × Ef :=
  (a⁻¹ • (V.DRs a (balL a w)).comp (balL a)).prod
    (V.Cred.comp (a • ContinuousLinearMap.fst ℝ Es Ef) + V.B.comp (ContinuousLinearMap.snd ℝ Es Ef)
      + (V.DRf a (balL a w)).comp (balL a))

/-- The balanced reference velocity `ω_a = (a² b_s, a³ b_w)`; `w_ref(s) = s ω_a`. -/
def omega (a : ℝ) : Es × Ef := (a ^ 2 • V.bs, a ^ 3 • V.bw)

/-- `β = ‖(b_s, b_w)‖`. -/
def beta : ℝ := ‖((V.bs, V.bw) : Es × Ef)‖

end UnbalancedField

open UnbalancedField

variable {V : UnbalancedField Es Ef} {C ρ₀ a₀ : ℝ}

theorem balL_apply (a : ℝ) (w : Es × Ef) : balL a w = (a • w.1, w.2) := rfl

theorem norm_balL_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (w : Es × Ef) :
    ‖balL a w‖ ≤ ‖w‖ := by
  rw [balL_apply, Prod.norm_mk, norm_smul, Real.norm_of_nonneg ha]
  refine max_le ((mul_le_of_le_one_left (norm_nonneg _) ha1).trans (norm_fst_le w))
    (norm_snd_le w)

/-- **Differentiability of the balanced field** on the tube where the balanced point lies in
the (C3) neighbourhood. -/
theorem hasFDerivAt_Hbal (hG : Graded V C ρ₀ a₀) {a : ℝ} (ha : a ∈ Ioo 0 a₀) {w : Es × Ef}
    (hw : ‖balL a w‖ ≤ ρ₀) : HasFDerivAt (V.Hbal a) (V.DHbal a w) w := by
  have hs : HasFDerivAt (fun w => V.Rs a (balL a w)) ((V.DRs a (balL a w)).comp (balL a))
      w := (hG.hasDeriv_s a ha _ hw).comp w (balL a : Es × Ef →L[ℝ] Es × Ef).hasFDerivAt
  have hf : HasFDerivAt (fun w => V.Rf a (balL a w)) ((V.DRf a (balL a w)).comp (balL a))
      w := (hG.hasDeriv_f a ha _ hw).comp w (balL a : Es × Ef →L[ℝ] Es × Ef).hasFDerivAt
  have h1 : HasFDerivAt (fun w => a⁻¹ • (a ^ 3 • V.bs + V.Rs a (balL a w)))
      (a⁻¹ • (V.DRs a (balL a w)).comp (balL a)) w :=
    (hs.const_add _).const_smul a⁻¹
  have h2 : HasFDerivAt (fun w => (V.Cred.comp (a • ContinuousLinearMap.fst ℝ Es Ef)) w
      + (V.B.comp (ContinuousLinearMap.snd ℝ Es Ef)) w + a ^ 3 • V.bw + V.Rf a (balL a w))
      (V.Cred.comp (a • ContinuousLinearMap.fst ℝ Es Ef) + V.B.comp (ContinuousLinearMap.snd ℝ Es Ef)
        + (V.DRf a (balL a w)).comp (balL a)) w :=
    (((V.Cred.comp (a • ContinuousLinearMap.fst ℝ Es Ef)).hasFDerivAt.add
      (V.B.comp (ContinuousLinearMap.snd ℝ Es Ef)).hasFDerivAt).add_const (a ^ 3 • V.bw)).add hf
  have hfun : V.Hbal a = fun x => (a⁻¹ • (a ^ 3 • V.bs + V.Rs a (balL a x)),
      (V.Cred.comp (a • ContinuousLinearMap.fst ℝ Es Ef)) x
        + (V.B.comp (ContinuousLinearMap.snd ℝ Es Ef)) x + a ^ 3 • V.bw + V.Rf a (balL a x)) := by
    funext x; rfl
  rw [hfun]
  exact h1.prodMk h2

/-- The balanced error of the derivative: `(D𝓗_a - D)h = (a⁻¹ DR_s(v)(Λh), a C_red h_s + DR_f(v)(Λh))`. -/
theorem DHbal_sub_apply (a : ℝ) (w h : Es × Ef) :
    (V.DHbal a w - V.Dlin) h = (a⁻¹ • V.DRs a (balL a w) (balL a h),
      a • V.Cred h.1 + V.DRf a (balL a w) (balL a h)) := by
  simp only [DHbal, Dlin, ContinuousLinearMap.sub_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, Prod.mk_sub_mk, sub_zero,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', map_smul]
  congr 1
  abel

/-- **First balanced-derivative estimate** of `lem:supp-exact-balanced-field`:
`‖D_w𝓗_a - D‖ ≤ (‖C_red‖ + C(1 + M₀)) a` on `‖w‖ ≤ M₀ a`. -/
theorem norm_DHbal_sub_le (hG : Graded V C ρ₀ a₀) {a M₀ : ℝ} (ha : a ∈ Ioo 0 a₀) (ha1 : a ≤ 1)
    {w : Es × Ef} (hw : ‖w‖ ≤ M₀ * a) (hρ : M₀ * a ≤ ρ₀) :
    ‖V.DHbal a w - V.Dlin‖ ≤ (‖V.Cred‖ + C * (1 + M₀)) * a := by
  have ha0 : 0 < a := ha.1
  have hv : ‖balL a w‖ ≤ M₀ * a := (norm_balL_le ha0.le ha1 w).trans hw
  have hvρ : ‖balL a w‖ ≤ ρ₀ := hv.trans hρ
  have hC := hG.C_nonneg
  have hM₀ : 0 ≤ M₀ * a := (norm_nonneg _).trans hw
  refine ContinuousLinearMap.opNorm_le_bound _ (by
    have : 0 ≤ M₀ := nonneg_of_mul_nonneg_left hM₀ ha0
    positivity) fun h => ?_
  rw [DHbal_sub_apply, Prod.norm_mk]
  have hbh := norm_balL_le ha0.le ha1 h
  have hDs : ‖V.DRs a (balL a w)‖ ≤ C * (a ^ 2 + a * (M₀ * a)) :=
    (hG.DRs_le a ha _ hvρ).trans (by gcongr)
  have hDf : ‖V.DRf a (balL a w)‖ ≤ C * (a + M₀ * a) :=
    (hG.DRf_le a ha _ hvρ).trans (by gcongr)
  refine max_le ?_ ?_
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha0.le)]
    calc a⁻¹ * ‖V.DRs a (balL a w) (balL a h)‖
        ≤ a⁻¹ * (C * (a ^ 2 + a * (M₀ * a)) * ‖h‖) := by
          gcongr
          exact ((V.DRs a _).le_opNorm _).trans (mul_le_mul hDs hbh (norm_nonneg _)
            (by positivity))
      _ = C * (1 + M₀) * a * ‖h‖ := by field_simp
      _ ≤ (‖V.Cred‖ + C * (1 + M₀)) * a * ‖h‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left (norm_nonneg _)) ha0.le) (norm_nonneg _)
  · calc ‖a • V.Cred h.1 + V.DRf a (balL a w) (balL a h)‖
        ≤ a * (‖V.Cred‖ * ‖h‖) + C * (a + M₀ * a) * ‖h‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_of_nonneg ha0.le]
            gcongr
            exact (V.Cred.le_opNorm _).trans (by gcongr; exact norm_fst_le h)
          · exact ((V.DRf a _).le_opNorm _).trans (mul_le_mul hDf hbh (norm_nonneg _)
              (by positivity))
      _ = (‖V.Cred‖ + C * (1 + M₀)) * a * ‖h‖ := by ring

/-- `‖ω_a‖ ≤ β a²` (`|w_ref'| ≤ C a²`). -/
theorem norm_omega_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : ‖V.omega a‖ ≤ V.beta * a ^ 2 := by
  simp only [omega, beta, Prod.norm_mk, norm_smul, Real.norm_of_nonneg (pow_nonneg ha _)]
  have h3 : a ^ 3 ≤ a ^ 2 := pow_le_pow_of_le_one ha ha1 (by norm_num)
  refine max_le ?_ ?_
  · rw [mul_comm]; gcongr; exact le_max_left _ _
  · calc a ^ 3 * ‖V.bw‖ ≤ a ^ 2 * ‖V.bw‖ := by gcongr
      _ ≤ _ := by rw [mul_comm]; gcongr; exact le_max_right _ _

/-- `‖w_ref(s)‖ ≤ c β a` for `0 ≤ s`, `s a ≤ c`. -/
theorem norm_wref_le {a s c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 ≤ s) (hsc : s * a ≤ c) :
    ‖s • V.omega a‖ ≤ c * V.beta * a := by
  rw [norm_smul, Real.norm_of_nonneg hs]
  have hb : 0 ≤ V.beta := norm_nonneg _
  calc s * ‖V.omega a‖ ≤ s * (V.beta * a ^ 2) := by gcongr; exact norm_omega_le ha.le ha1
    _ = (s * a) * V.beta * a := by ring
    _ ≤ c * V.beta * a := by gcongr

/-- The balanced reference point: `diag(a,1) w_ref(s) = (s a³)(b_s, b_w)`. -/
theorem balL_wref (a s : ℝ) : balL a (s • V.omega a) = (s * a ^ 3) • ((V.bs, V.bw) : Es × Ef) := by
  simp only [balL_apply, omega, Prod.smul_mk, smul_smul]
  congr 2 <;> ring

theorem norm_balL_wref_le {a s c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 ≤ s)
    (hsc : s * a ≤ c) : ‖balL a (s • V.omega a)‖ ≤ c * V.beta * a ^ 2 := by
  rw [balL_wref, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hb : 0 ≤ V.beta := norm_nonneg _
  calc s * a ^ 3 * ‖((V.bs, V.bw) : Es × Ef)‖ = (s * a) * V.beta * a ^ 2 := by
        simp only [beta]; ring
    _ ≤ c * V.beta * a ^ 2 := by gcongr

/-- The reference residual reduces to the remainders: `f_a(s) = (a⁻¹ R_s(v_ref), R_f(v_ref))`
(transport identity). -/
theorem src_eq (hG : Graded V C ρ₀ a₀) {a : ℝ} (ha : a ≠ 0) (s : ℝ) :
    V.Hbal a (s • V.omega a) - V.omega a =
      (a⁻¹ • V.Rs a (balL a (s • V.omega a)), V.Rf a (balL a (s • V.omega a))) := by
  set v := balL a (s • V.omega a) with hv
  have hlin : V.Cred v.1 + V.B v.2 = 0 := by
    rw [hv, balL_wref]
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, ← smul_add, hG.transport, smul_zero]
  refine Prod.ext ?_ ?_
  · show a⁻¹ • (a ^ 3 • V.bs + V.Rs a v) - a ^ 2 • V.bs = a⁻¹ • V.Rs a v
    rw [smul_add, smul_smul, show a⁻¹ * a ^ 3 = a ^ 2 by field_simp]
    abel
  · show V.Cred v.1 + V.B v.2 + a ^ 3 • V.bw + V.Rf a v - a ^ 3 • V.bw = V.Rf a v
    rw [hlin, zero_add, add_sub_cancel_left]

/-- **Reference residual estimate** of `lem:supp-exact-balanced-field`:
`‖f_a(s)‖ ≤ C(1 + cβ + c²β²) a³` for `0 ≤ s`, `s a ≤ c`. -/
theorem norm_src_le (hG : Graded V C ρ₀ a₀) {a s c : ℝ} (ha : a ∈ Ioo 0 a₀) (ha1 : a ≤ 1)
    (hs : 0 ≤ s) (hsc : s * a ≤ c) (hρ : c * V.beta * a ^ 2 ≤ ρ₀) :
    ‖V.Hbal a (s • V.omega a) - V.omega a‖
      ≤ C * (1 + c * V.beta + (c * V.beta) ^ 2) * a ^ 3 := by
  have ha0 := ha.1
  have hC := hG.C_nonneg
  have hc : 0 ≤ c := (mul_nonneg hs ha0.le).trans hsc
  have hb : 0 ≤ V.beta := norm_nonneg _
  set v := balL a (s • V.omega a)
  have hv : ‖v‖ ≤ c * V.beta * a ^ 2 := norm_balL_wref_le ha0 ha1 hs hsc
  have hvρ : ‖v‖ ≤ ρ₀ := hv.trans hρ
  have ha3 : a ^ 4 ≤ a ^ 3 := pow_le_pow_of_le_one ha0.le ha1 (by norm_num)
  have hRs : ‖V.Rs a v‖ ≤ C * (a ^ 4 + a ^ 2 * (c * V.beta * a ^ 2)
      + a * (c * V.beta * a ^ 2) ^ 2) := (hG.Rs_le a ha v hvρ).trans (by gcongr)
  have hRf : ‖V.Rf a v‖ ≤ C * (a ^ 4 + a * (c * V.beta * a ^ 2) + (c * V.beta * a ^ 2) ^ 2) :=
    (hG.Rf_le a ha v hvρ).trans (by gcongr)
  have hq : (c * V.beta) ^ 2 * a ≤ (c * V.beta) ^ 2 := mul_le_of_le_one_right (by positivity) ha1
  rw [src_eq hG ha0.ne', Prod.norm_mk]
  refine max_le ?_ ?_
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha0.le)]
    calc a⁻¹ * ‖V.Rs a v‖ ≤ a⁻¹ * (C * (a ^ 4 + a ^ 2 * (c * V.beta * a ^ 2)
          + a * (c * V.beta * a ^ 2) ^ 2)) := mul_le_mul_of_nonneg_left hRs (inv_nonneg.2 ha0.le)
      _ = C * (1 + c * V.beta + (c * V.beta) ^ 2 * a) * a ^ 3 := by field_simp
      _ ≤ C * (1 + c * V.beta + (c * V.beta) ^ 2) * a ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC) (by positivity)
  · calc ‖V.Rf a v‖ ≤ C * (a ^ 4 + a * (c * V.beta * a ^ 2) + (c * V.beta * a ^ 2) ^ 2) := hRf
      _ = C * (a + c * V.beta + (c * V.beta) ^ 2 * a) * a ^ 3 := by ring
      _ ≤ C * (1 + c * V.beta + (c * V.beta) ^ 2) * a ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC) (by positivity)

/-- **Derivative of the reference residual** of `lem:supp-exact-balanced-field`:
`f_a'(s) = D𝓗_a(w_ref(s)) ω_a` and `‖f_a'(s)‖ ≤ C(1 + cβ) β a⁴`. -/
theorem norm_src_deriv_le (hG : Graded V C ρ₀ a₀) {a s c : ℝ} (ha : a ∈ Ioo 0 a₀) (ha1 : a ≤ 1)
    (hs : 0 ≤ s) (hsc : s * a ≤ c) (hρ : c * V.beta * a ^ 2 ≤ ρ₀) :
    ‖V.DHbal a (s • V.omega a) (V.omega a)‖ ≤ C * (1 + c * V.beta) * V.beta * a ^ 4 := by
  have ha0 := ha.1
  have hC := hG.C_nonneg
  have hc : 0 ≤ c := (mul_nonneg hs ha0.le).trans hsc
  have hb : 0 ≤ V.beta := norm_nonneg _
  set v := balL a (s • V.omega a)
  have hv : ‖v‖ ≤ c * V.beta * a ^ 2 := norm_balL_wref_le ha0 ha1 hs hsc
  have hvρ : ‖v‖ ≤ ρ₀ := hv.trans hρ
  have hΛ : balL a (V.omega a) = a ^ 3 • ((V.bs, V.bw) : Es × Ef) := by
    have := balL_wref (V := V) a 1
    simpa using this
  have hΛn : ‖balL a (V.omega a)‖ = a ^ 3 * V.beta := by
    rw [hΛ, norm_smul, Real.norm_of_nonneg (by positivity)]; rfl
  have hlin : V.Cred (a • (V.omega a).1) + V.B (V.omega a).2 = 0 := by
    simp only [omega, smul_smul, map_smul]
    rw [show a * a ^ 2 = a ^ 3 by ring, ← smul_add, hG.transport, smul_zero]
  have happ : V.DHbal a (s • V.omega a) (V.omega a)
      = (a⁻¹ • V.DRs a v (balL a (V.omega a)), V.DRf a v (balL a (V.omega a))) := by
    simp only [DHbal, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', v]
    congr 1
    rw [hlin, zero_add]
  have hDs : ‖V.DRs a v (balL a (V.omega a))‖
      ≤ C * (a ^ 2 + a * (c * V.beta * a ^ 2)) * (a ^ 3 * V.beta) := by
    refine ((V.DRs a v).le_opNorm _).trans ?_
    rw [hΛn]
    exact mul_le_mul_of_nonneg_right ((hG.DRs_le a ha v hvρ).trans (by gcongr)) (by positivity)
  have hDf : ‖V.DRf a v (balL a (V.omega a))‖
      ≤ C * (a + c * V.beta * a ^ 2) * (a ^ 3 * V.beta) := by
    refine ((V.DRf a v).le_opNorm _).trans ?_
    rw [hΛn]
    exact mul_le_mul_of_nonneg_right ((hG.DRf_le a ha v hvρ).trans (by gcongr)) (by positivity)
  have hq : c * V.beta * a ≤ c * V.beta := mul_le_of_le_one_right (by positivity) ha1
  have hfin : C * (1 + c * V.beta * a) * V.beta * a ^ 4 ≤ C * (1 + c * V.beta) * V.beta * a ^ 4 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hC) hb) (by positivity)
  rw [happ, Prod.norm_mk]
  refine max_le ?_ ?_
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha0.le)]
    calc a⁻¹ * ‖V.DRs a v (balL a (V.omega a))‖
        ≤ a⁻¹ * (C * (a ^ 2 + a * (c * V.beta * a ^ 2)) * (a ^ 3 * V.beta)) :=
          mul_le_mul_of_nonneg_left hDs (inv_nonneg.2 ha0.le)
      _ = C * (1 + c * V.beta * a) * V.beta * a ^ 4 := by field_simp
      _ ≤ _ := hfin
  · calc ‖V.DRf a v (balL a (V.omega a))‖
        ≤ C * (a + c * V.beta * a ^ 2) * (a ^ 3 * V.beta) := hDf
      _ = C * (1 + c * V.beta * a) * V.beta * a ^ 4 := by ring
      _ ≤ _ := hfin

end

end ExactBoundaryChart
end RenewalGeometry
