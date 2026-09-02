/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventShiftFunctionalCalculus
import NCG.Grand.OperatorGraphResolventHeatSemigroup
import NCG.Grand.ResolventHeatMultiplierLaplace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral

/-!
# Laplace transform of the canonical graph-resolvent heat semigroup

Mathlib's integral continuous-functional-calculus theorem lifts the scalar
Laplace identity for the one-resolvent heat multiplier to operators.  The
result identifies the Laplace transform of the canonical heat family with
the actual weak graph resolvent at every positive shift.
-/

open Function MeasureTheory Set Topology

noncomputable section

namespace NCG.VaryingHilbert

universe v w

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Operator-valued Laplace representation of every positive graph
resolvent through the canonical heat family built from one reference
resolvent. -/
theorem integral_smul_operatorGraphResolventHeat_eq_resolvent
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b lam : ℝ) (hb : 0 < b) (hlam : 0 < lam) :
    (∫ t : ℝ in Ioi 0,
        Real.exp (-lam * t) • operatorGraphResolventHeat (R b) b t) =
      R lam := by
  let f : ℝ → ℝ → ℝ := fun t r ↦
    Real.exp (-lam * t) *
      NCG.ImplicitEuler.resolventHeatMultiplier b t r
  let bound : ℝ → ℝ := fun t ↦ Real.exp (-lam * t)
  have hself : IsSelfAdjoint (R b) :=
    (operatorGraphResolvent_isSymmetric D A b (R b)
      (hequation b hb)).isSelfAdjoint
  have hspectrum : spectrum ℝ (R b) ⊆ Icc 0 b⁻¹ :=
    operatorGraphResolvent_realSpectrum_subset_Icc
      D A b hb (R b) (hequation b hb)
  have hfContinuous :
      ContinuousOn (uncurry f) (Ioi 0 ×ˢ spectrum ℝ (R b)) := by
    have hweight : Continuous
        (fun p : ℝ × ℝ ↦ Real.exp (-lam * p.1)) := by
      fun_prop
    have hsubset :
        Ioi (0 : ℝ) ×ˢ spectrum ℝ (R b) ⊆
          Ioi 0 ×ˢ Icc 0 b⁻¹ :=
      fun _ hp ↦ ⟨hp.1, hspectrum hp.2⟩
    have hheat :=
      (NCG.ImplicitEuler.continuousOn_uncurry_resolventHeatMultiplier
        b hb).mono hsubset
    exact hweight.continuousOn.mul hheat
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      ∀ r ∈ spectrum ℝ (R b), ‖f t r‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro r hr
    have hheat :=
      NCG.ImplicitEuler.abs_resolventHeatMultiplier_le_one
        b t r (show 0 ≤ t from le_of_lt ht)
        (hspectrum hr).1 (hspectrum hr).2
    simp only [f, bound, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-lam * t) *
          |NCG.ImplicitEuler.resolventHeatMultiplier b t r|
          ≤ Real.exp (-lam * t) * 1 :=
        mul_le_mul_of_nonneg_left hheat (Real.exp_pos _).le
      _ = Real.exp (-lam * t) := mul_one _
  have hboundIntegrable :
      HasFiniteIntegral bound (volume.restrict (Ioi 0)) := by
    have h :
        IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t)) (Ioi 0) := by
      convert integrableOn_exp_mul_Ioi (a := -lam) (by linarith) 0 using 1
    exact h.hasFiniteIntegral
  have hcfc :=
    cfc_setIntegral (𝕜 := ℝ) measurableSet_Ioi f bound (R b)
      hfContinuous hbound hboundIntegrable hself
  have hcfcPoint : ∀ t ∈ Ioi (0 : ℝ),
      cfc (f t) (R b) =
        Real.exp (-lam * t) • operatorGraphResolventHeat (R b) b t := by
    intro t ht
    have hmult : ContinuousOn
        (NCG.ImplicitEuler.resolventHeatMultiplier b t)
        (spectrum ℝ (R b)) :=
      (NCG.ImplicitEuler.continuousOn_resolventHeatMultiplier
        b t hb ht).mono hspectrum
    rw [show f t = fun r ↦ Real.exp (-lam * t) *
      NCG.ImplicitEuler.resolventHeatMultiplier b t r by rfl]
    rw [cfc_const_mul _ _ _ hmult]
    rfl
  calc
    (∫ t : ℝ in Ioi 0,
        Real.exp (-lam * t) • operatorGraphResolventHeat (R b) b t) =
        ∫ t : ℝ in Ioi 0, cfc (f t) (R b) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact (hcfcPoint t ht).symm
    _ = cfc (fun r ↦ ∫ t : ℝ in Ioi 0, f t r) (R b) := hcfc.symm
    _ = cfc (fun r : ℝ ↦ r / (1 + (lam - b) * r)) (R b) := by
          apply cfc_congr
          intro r hr
          exact NCG.ImplicitEuler.integral_exp_mul_resolventHeatMultiplier
            b lam r hlam (hspectrum hr).1 (hspectrum hr).2
    _ = R lam :=
      (operatorGraphResolvent_eq_cfc_shiftTransform
        D A R hequation lam b hlam hb).symm

/-- Applied-vector Laplace representation of the canonical graph-resolvent
heat family. -/
theorem integral_smul_operatorGraphResolventHeat_apply_eq_resolvent
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b lam : ℝ) (hb : 0 < b) (hlam : 0 < lam) (x : E) :
    (∫ t : ℝ in Ioi 0,
        ((Real.exp (-lam * t) : ℝ) : ℂ) •
          operatorGraphResolventHeat (R b) b t x) =
      R lam x := by
  let f : ℝ → ℝ → ℝ := fun t r ↦
    Real.exp (-lam * t) *
      NCG.ImplicitEuler.resolventHeatMultiplier b t r
  let bound : ℝ → ℝ := fun t ↦ Real.exp (-lam * t)
  have hself : IsSelfAdjoint (R b) :=
    (operatorGraphResolvent_isSymmetric D A b (R b)
      (hequation b hb)).isSelfAdjoint
  have hspectrum : spectrum ℝ (R b) ⊆ Icc 0 b⁻¹ :=
    operatorGraphResolvent_realSpectrum_subset_Icc
      D A b hb (R b) (hequation b hb)
  have hfContinuous :
      ContinuousOn (uncurry f) (Ioi 0 ×ˢ spectrum ℝ (R b)) := by
    have hweight : Continuous
        (fun p : ℝ × ℝ ↦ Real.exp (-lam * p.1)) := by
      fun_prop
    have hsubset :
        Ioi (0 : ℝ) ×ˢ spectrum ℝ (R b) ⊆
          Ioi 0 ×ˢ Icc 0 b⁻¹ :=
      fun _ hp ↦ ⟨hp.1, hspectrum hp.2⟩
    have hheat :=
      (NCG.ImplicitEuler.continuousOn_uncurry_resolventHeatMultiplier
        b hb).mono hsubset
    exact hweight.continuousOn.mul hheat
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      ∀ r ∈ spectrum ℝ (R b), ‖f t r‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro r hr
    have hheat :=
      NCG.ImplicitEuler.abs_resolventHeatMultiplier_le_one
        b t r (show 0 ≤ t from le_of_lt ht)
        (hspectrum hr).1 (hspectrum hr).2
    simp only [f, bound, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left hheat (Real.exp_pos _).le).trans_eq
      (mul_one _)
  have hboundIntegrable :
      HasFiniteIntegral bound (volume.restrict (Ioi 0)) := by
    have h :
        IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t)) (Ioi 0) := by
      convert integrableOn_exp_mul_Ioi (a := -lam) (by linarith) 0 using 1
    exact h.hasFiniteIntegral
  have hintCfc :=
    integrableOn_cfc measurableSet_Ioi f bound (R b)
      hfContinuous hbound hboundIntegrable hself
  have hintHeat : IntegrableOn
      (fun t : ℝ ↦ Real.exp (-lam * t) •
        operatorGraphResolventHeat (R b) b t)
      (Ioi 0) := by
    apply hintCfc.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hmult : ContinuousOn
        (NCG.ImplicitEuler.resolventHeatMultiplier b t)
        (spectrum ℝ (R b)) :=
      (NCG.ImplicitEuler.continuousOn_resolventHeatMultiplier
        b t hb ht).mono hspectrum
    rw [show f t = fun r ↦ Real.exp (-lam * t) *
      NCG.ImplicitEuler.resolventHeatMultiplier b t r by rfl]
    rw [cfc_const_mul _ _ _ hmult]
    rfl
  have hcomm :=
    ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).integral_comp_comm
      hintHeat
  rw [integral_smul_operatorGraphResolventHeat_eq_resolvent
    D A R hequation b lam hb hlam] at hcomm
  simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using hcomm

end NCG.VaryingHilbert
