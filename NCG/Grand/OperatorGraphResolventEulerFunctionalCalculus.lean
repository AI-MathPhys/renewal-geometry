/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventShiftFunctionalCalculus

/-!
# Actual graph-resolvent Euler powers as one-resolvent functional calculus

The shifted weak resolvent at `k / t`, after multiplication by its shift, is exactly the
one-reference-resolvent Euler-root functional calculus.  Consequently its `k`th operator power is
the canonical Euler operator constructed from the fixed reference resolvent.
-/

open Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert

universe v w

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The scaled weak resolvent at shift `k / t` is the Euler-root functional calculus of a fixed
reference resolvent. -/
theorem scaled_operatorGraphResolvent_eq_cfc_resolventEulerRoot
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t)
    (k : ℕ) (hk : 0 < k) :
    (((((k : ℕ) : ℝ) / t : ℝ) : ℂ)) • R (((k : ℕ) : ℝ) / t) =
      cfc (NCG.ImplicitEuler.resolventEulerRoot b t k) (R b) := by
  let a : ℝ := (k : ℝ) / t
  let q : ℝ → ℝ := fun r ↦ 1 + (a - b) * r
  let f : ℝ → ℝ := fun r ↦ r / q r
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha : 0 < a := div_pos hkReal ht
  have hself : IsSelfAdjoint (R b) :=
    (operatorGraphResolvent_isSymmetric D A b (R b) (hequation b hb)).isSelfAdjoint
  have hidCont : ContinuousOn (fun r : ℝ ↦ r) (spectrum ℝ (R b)) :=
    continuous_id.continuousOn
  have hqCont : ContinuousOn q (spectrum ℝ (R b)) := by
    fun_prop
  have hqNe : ∀ r ∈ spectrum ℝ (R b), q r ≠ 0 := by
    intro r hr
    exact ne_of_gt (operatorGraphResolvent_shiftDenominator_pos
      D A R hequation a b ha hb hr)
  have hfCont : ContinuousOn f (spectrum ℝ (R b)) :=
    hidCont.div hqCont hqNe
  have hshift : R a = cfc f (R b) :=
    operatorGraphResolvent_eq_cfc_shiftTransform
      D A R hequation a b ha hb
  calc
    (((a : ℝ) : ℂ)) • R a = a • R a := by
      exact (RCLike.real_smul_eq_coe_smul (K := ℂ) a (R a)).symm
    _ = a • cfc f (R b) := congrArg (fun T : E →L[ℂ] E ↦ a • T) hshift
    _ = cfc (fun r ↦ a * f r) (R b) :=
      (cfc_const_mul a f (R b) hfCont).symm
    _ = cfc (NCG.ImplicitEuler.resolventEulerRoot b t k) (R b) := by
      apply cfc_congr
      intro r hr
      change a * (r / (1 + (a - b) * r)) =
        (((k : ℝ) / t) * r) / (1 + (((k : ℝ) / t) - b) * r)
      rw [show a = (k : ℝ) / t from rfl]
      ring

/-- The actual `k`th implicit-Euler power of the weak graph resolvent is the canonical
one-reference-resolvent Euler operator. -/
theorem scaled_operatorGraphResolvent_pow_eq_operatorGraphResolventEuler
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t)
    (k : ℕ) (hk : 0 < k) :
    (((((((k : ℕ) : ℝ) / t : ℝ) : ℂ)) • R (((k : ℕ) : ℝ) / t)) ^ k) =
      operatorGraphResolventEuler (R b) b t k := by
  have hspectrum := operatorGraphResolvent_realSpectrum_subset_Icc
    D A b hb (R b) (hequation b hb)
  have hself : IsSelfAdjoint (R b) :=
    (operatorGraphResolvent_isSymmetric D A b (R b) (hequation b hb)).isSelfAdjoint
  have hrootCont : ContinuousOn
      (NCG.ImplicitEuler.resolventEulerRoot b t k) (spectrum ℝ (R b)) :=
    (NCG.ImplicitEuler.continuousOn_resolventEulerRoot b t k hb ht hk).mono hspectrum
  rw [scaled_operatorGraphResolvent_eq_cfc_resolventEulerRoot
    D A R hequation b t hb ht k hk]
  rw [operatorGraphResolventEuler,
    cfc_pow (NCG.ImplicitEuler.resolventEulerRoot b t k) k (R b) hrootCont hself]

/-- The actual implicit-Euler power formed from the all-shift weak resolvent satisfies the same
dimension-free operator-norm heat approximation bound as its scalar multiplier. -/
theorem norm_scaled_operatorGraphResolvent_pow_sub_heat_le_inv_sqrt
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t)
    (k : ℕ) (hk : 0 < k) :
    ‖(((((((k : ℕ) : ℝ) / t : ℝ) : ℂ)) • R (((k : ℕ) : ℝ) / t)) ^ k) -
        operatorGraphResolventHeat (R b) b t‖ ≤
      (Real.sqrt (k : ℝ))⁻¹ := by
  rw [scaled_operatorGraphResolvent_pow_eq_operatorGraphResolventEuler
    D A R hequation b t hb ht k hk]
  exact norm_operatorGraphResolventEuler_sub_heat_le_inv_sqrt
    D A b t hb ht k hk (R b) (hequation b hb)

/-- Zero-indexed form of the actual graph-resolvent Euler error bound. -/
theorem norm_scaled_operatorGraphResolvent_succ_pow_sub_heat_le_errorRate
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t) (m : ℕ) :
    ‖(((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
          R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) -
        operatorGraphResolventHeat (R b) b t‖ ≤
      NCG.ImplicitEuler.errorRate m := by
  simpa [NCG.ImplicitEuler.errorRate, Nat.cast_add, Nat.cast_one] using
    norm_scaled_operatorGraphResolvent_pow_sub_heat_le_inv_sqrt
      D A R hequation b t hb ht (m + 1) (Nat.succ_pos m)

/-- Actual implicit-Euler powers of all positive-shift graph resolvents converge in operator norm
to the heat operator constructed from one fixed reference resolvent. -/
theorem tendsto_scaled_operatorGraphResolvent_succ_pow_heat
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t) :
    Tendsto
      (fun m ↦
        (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
          R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)))
      atTop (nhds (operatorGraphResolventHeat (R b) b t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero
    (fun m ↦ norm_nonneg _)
    (fun m ↦ norm_scaled_operatorGraphResolvent_succ_pow_sub_heat_le_errorRate
      D A R hequation b t hb ht m)
    NCG.ImplicitEuler.errorRate_tendsto_zero

/-- Vectorwise Euler convergence follows from the stronger operator-norm convergence. -/
theorem tendsto_scaled_operatorGraphResolvent_succ_pow_apply_heat
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t) (x : E) :
    Tendsto
      (fun m ↦
        (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
          R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) x)
      atTop (nhds (operatorGraphResolventHeat (R b) b t x)) := by
  exact (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    ((tendsto_scaled_operatorGraphResolvent_succ_pow_heat
      D A R hequation b t hb ht).prodMk_nhds tendsto_const_nhds)

end NCG.VaryingHilbert
