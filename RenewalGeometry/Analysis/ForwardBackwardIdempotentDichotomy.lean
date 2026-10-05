/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.ForwardBackwardFieldSweep

/-!
# Explicit exponential dichotomies (non-vacuity of the sweep hypotheses)

* `FBIdem.exp_smul_idempotent`: for an idempotent `P` of a real Banach algebra,
  `exp(tP) = (1 - P) + e^t P`.
* `FBIdem.dichotomy_of_idempotent`: if `P` is idempotent with `‖P‖ ≤ 1` and `‖1 - P‖ ≤ 1`, then
  `D = P` has the exponential dichotomy `eq:supp-exact-dichotomy` with `Π₊ = P`, `Π₋ = 1 - P`,
  `M = 1`, `κ = 1` (`e^{tD}Π₋ = Π₋`, `e^{-tD}Π₊ = e^{-t}Π₊`).
* `FBIdem.diagP`: the diagonal operator `diag(0, 1)` on `ℝ × ℝ` — the shape `diag(0_slow, B)` of the
  manuscript with a one-dimensional unstable weak block — is such an idempotent
  (`FBIdem.diag_dichotomy`).
* `FBIdem.diag_fieldData`: the field `H(w) = diag(0,1) w + (0, δ)` with `w_ref = 0` satisfies all
  hypotheses of `FBField.FieldData` (on `[0, S]`, `R = 2 S |δ|`); its boundary history is
  nontrivial for `δ ≠ 0` (`FBIdem.diag_history_nontrivial`).
-/

open Set Metric
open scoped Nat

namespace RenewalGeometry
namespace FBIdem

open FBVariation FBGreen FBSweep FBField

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-- `exp(tP) = (1 - P) + e^t P` for an idempotent `P`. -/
theorem exp_smul_idempotent {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {P : A} (hP : IsIdempotentElem P) (t : ℝ) :
    NormedSpace.exp (t • P) = 1 - P + Real.exp t • P := by
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • P)
  have h2 : HasSum (fun n : ℕ => ((n !⁻¹ : ℝ) * t ^ n) • P + if n = 0 then (1 - P) else 0)
      (Real.exp t • P + (1 - P)) := by
    refine HasSum.add ?_ (hasSum_ite_eq 0 (1 - P))
    have := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) t
    rw [← Real.exp_eq_exp_ℝ] at this
    simpa [smul_eq_mul] using this.smul_const P
  have heq : (fun n : ℕ => (n !⁻¹ : ℝ) • (t • P) ^ n)
      = fun n => ((n !⁻¹ : ℝ) * t ^ n) • P + if n = 0 then (1 - P) else 0 := by
    funext n
    cases n with
    | zero => simp
    | succ k => rw [smul_pow, hP.pow_succ_eq k]; simp [mul_smul]
  rw [heq] at h1
  rw [h1.unique h2]
  abel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem prop_idempotent {P : E →L[ℝ] E} (hP : IsIdempotentElem P) (t : ℝ) :
    prop P t = 1 - P + Real.exp t • P :=
  exp_smul_idempotent hP t

/-- **An explicit exponential dichotomy**: `D = P` idempotent, `Π₊ = P`, `Π₋ = 1 - P`. -/
theorem dichotomy_of_idempotent {P : E →L[ℝ] E} (hP : IsIdempotentElem P) (h1 : ‖P‖ ≤ 1)
    (h2 : ‖1 - P‖ ≤ 1) : Dichotomy P P (1 - P) 1 1 where
  sum := add_sub_cancel P 1
  comm_p := Commute.refl P
  comm_m := (Commute.one_right P).sub_right (Commute.refl P)
  idem_p := hP.eq
  idem_m := hP.one_sub.eq
  kappa_pos := one_pos
  bound_m := fun t _ => by
    have hm : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP.eq, sub_self]
    have : prop P t * (1 - P) = 1 - P := by
      rw [prop_idempotent hP, add_mul, smul_mul_assoc, hm, smul_zero, add_zero, hP.one_sub.eq]
    rw [this]; exact h2
  bound_p := fun t ht => by
    have hm : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP.eq, sub_self]
    have : prop P (-t) * P = Real.exp (-t) • P := by
      rw [prop_idempotent hP, add_mul, smul_mul_assoc, hm, zero_add, hP.eq]
    rw [this, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul, one_mul]
    exact mul_le_of_le_one_right (Real.exp_pos _).le h1

/-- `diag(0, 1)` on `ℝ × ℝ`. -/
noncomputable def diagP : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem diagP_apply (v : ℝ × ℝ) : diagP v = (0, v.2) := rfl

theorem one_sub_diagP_apply (v : ℝ × ℝ) : (1 - diagP) v = (v.1, 0) := by
  simp [diagP_apply, Prod.ext_iff]

theorem diagP_idem : IsIdempotentElem diagP := by
  ext <;> simp [diagP_apply]

theorem diag_dichotomy : Dichotomy diagP diagP (1 - diagP) 1 1 := by
  refine dichotomy_of_idempotent diagP_idem ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [diagP_apply, one_mul, Prod.norm_mk, norm_zero]
    exact max_le ((norm_nonneg _).trans (norm_snd_le v)) (norm_snd_le v)
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_sub_diagP_apply, one_mul, Prod.norm_mk, norm_zero]
    exact max_le (norm_fst_le v) ((norm_nonneg _).trans (norm_fst_le v))

/-- **Non-vacuity of `FieldData`**: `H(w) = diag(0,1) w + (0, δ)`, `w_ref = 0`, on `[0, S]` with
`R = 2 S |δ|` (and `ρ = R`, `ε = 0`). -/
theorem diag_fieldData (δ S : ℝ) (hS : 0 ≤ S) :
    FieldData diagP diagP (1 - diagP) 1 1 (fun w => diagP w + (0, δ)) (fun _ => diagP) 0
      (2 * S * |δ|) 0 S (2 * S * |δ|) |δ| where
  dich := diag_dichotomy
  S_nonneg := hS
  deriv := fun w _ => (diagP.hasFDerivAt).add_const _
  deriv_close := fun w _ => by simp
  tube := fun s _ => by simp
  src_bound := fun s _ => by simp [diagP_apply]
  q_le := by norm_num
  source_le := by ring_nf; rfl

/-- The boundary history of the example is the explicit nontrivial curve
`w(s) = (0, δ(e^{s-S} - 1))`: it solves `w' = H(w)`, `Π₋w(0) = 0`, `Π₊w(S) = 0`. -/
theorem diag_history_nontrivial (δ S : ℝ) (hS : 0 < S) :
    IsBoundaryHistory diagP diagP (1 - diagP) (fun w => diagP w + (0, δ)) 0 S (2 * S * |δ|)
      (fun s => (0, δ * (Real.exp (s - S) - 1))) := by
  refine ⟨Continuous.continuousOn (by fun_prop), fun s _ => ?_, ?_, ?_, fun s hs => ?_⟩
  · have h := ((Real.hasDerivAt_exp (s - S)).comp s ((hasDerivAt_id s).sub_const S))
    have hp := (hasDerivAt_const s (0 : ℝ)).prodMk ((h.sub_const 1).const_mul δ)
    refine hp.congr_deriv ?_
    show _ = diagP (0, δ * (Real.exp (s - S) - 1)) + (0, δ)
    rw [diagP_apply]
    simp only [Prod.mk_add_mk, add_zero]
    congr 1
    ring
  · simp [diagP_apply]
  · simp [diagP_apply]
  · simp only [smul_zero, sub_zero, Prod.norm_mk, norm_zero]
    refine max_le (by positivity) ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have he1 : Real.exp (s - S) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hs.2])
    have he2 : s - S + 1 ≤ Real.exp (s - S) := Real.add_one_le_exp _
    have h1 : |Real.exp (s - S) - 1| ≤ 2 * S := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith [hs.1]
    calc |δ| * |Real.exp (s - S) - 1| ≤ |δ| * (2 * S) := by gcongr
      _ = 2 * S * |δ| := by ring

end FBIdem
end RenewalGeometry
