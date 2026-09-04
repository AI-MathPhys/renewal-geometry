/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LorentzBivectorCommutantExact

/-!
# Lorentz-invariant curvature pairings and alternating coframe volume

Every invariant real bilinear form on actual spacetime bivectors is a
unique combination of the induced metric pairing and the wedge pairing.
Every alternating four-coframe scalar is a unique multiple of determinant.
These are algebraic classification results, not a claim about the analytic
Einstein-variation limit.
-/

open Matrix
open scoped BigOperators

namespace NCG.LorentzInvariantDensityClassification

open BivectorRotationCommutant LorentzBivectorAction
  LorentzBivectorInvariantForms LorentzBivectorCommutant

noncomputable section

def InvariantBivectorPairing (B : BivectorMatrix) : Prop :=
  ∀ L : SpacetimeMatrix, IsProperTimeOrientedLorentz L →
    (bivectorAction L)ᵀ * B * bivectorAction L = B

theorem raised_pairing_lorentzNatural (B : BivectorMatrix)
    (hB : InvariantBivectorPairing B) : LorentzNatural (bivectorMetric * B) := by
  intro L hL
  let W := bivectorAction L
  have hQ : Wᵀ * bivectorMetric * W = bivectorMetric :=
    bivectorAction_preserves_metric L hL.1
  have hleft : (bivectorMetric * Wᵀ * bivectorMetric) * W = 1 := by
    calc
      _ = bivectorMetric * (Wᵀ * bivectorMetric * W) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQ, bivectorMetric_squared]
  have hright : W * (bivectorMetric * Wᵀ * bivectorMetric) = 1 :=
    Matrix.mul_eq_one_comm.mp hleft
  have hWQW : W * bivectorMetric * Wᵀ = bivectorMetric := by
    calc
      _ = (W * (bivectorMetric * Wᵀ * bivectorMetric)) * bivectorMetric := by
        simp only [Matrix.mul_assoc, bivectorMetric_squared, Matrix.mul_one]
      _ = bivectorMetric := by rw [hright, Matrix.one_mul]
  change (bivectorMetric * B) * W = W * (bivectorMetric * B)
  calc
    _ = (W * bivectorMetric * Wᵀ) * B * W := by rw [hWQW]
    _ = W * bivectorMetric * (Wᵀ * B * W) := by simp only [Matrix.mul_assoc]
    _ = W * (bivectorMetric * B) := by rw [hB L hL, Matrix.mul_assoc]

theorem metric_mul_hodgeStar : bivectorMetric * hodgeStar = -wedgePairing := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [bivectorMetric, wedgePairing, hodgeStar, scalarBlocks, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_two]

theorem invariant_pairing_eq_metric_add_wedge (B : BivectorMatrix)
    (hB : InvariantBivectorPairing B) :
    ∃ a b : ℝ, B = a • bivectorMetric + b • wedgePairing := by
  have h := lorentzNatural_eq_identity_add_hodge _ (raised_pairing_lorentzNatural B hB)
  refine ⟨(bivectorMetric * B) (0, 0) (0, 0),
    -(bivectorMetric * B) (0, 0) (1, 0), ?_⟩
  have hh := congrArg (fun T => bivectorMetric * T) h
  simpa only [← Matrix.mul_assoc, bivectorMetric_squared, Matrix.one_mul,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, metric_mul_hodgeStar,
    smul_neg, neg_smul] using hh

theorem metric_add_wedge_invariant (a b : ℝ) :
    InvariantBivectorPairing (a • bivectorMetric + b • wedgePairing) := by
  intro L hL
  have hQ := bivectorAction_preserves_metric L hL.1
  have hE := bivectorAction_wedgePairing L
  rw [hL.2.1, one_smul] at hE
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hQ, hE]

theorem metric_wedge_coefficients_unique (a b c d : ℝ)
    (h : a • bivectorMetric + b • wedgePairing = c • bivectorMetric + d • wedgePairing) :
    a = c ∧ b = d := by
  have ha := congrFun (congrFun h (0, 0)) (0, 0)
  have hb := congrFun (congrFun h (0, 0)) (1, 0)
  simpa [bivectorMetric, wedgePairing, scalarBlocks] using And.intro ha hb

theorem invariant_pairing_iff_existsUnique (B : BivectorMatrix) :
    InvariantBivectorPairing B ↔
      ∃! ab : ℝ × ℝ, B = ab.1 • bivectorMetric + ab.2 • wedgePairing := by
  constructor
  · intro hB
    obtain ⟨a, b, hab⟩ := invariant_pairing_eq_metric_add_wedge B hB
    refine ⟨(a, b), hab, ?_⟩
    intro cd hcd
    have h := metric_wedge_coefficients_unique cd.1 cd.2 a b (hcd.symm.trans hab)
    exact Prod.ext h.1 h.2
  · rintro ⟨ab, hab, _⟩
    rw [hab]
    exact metric_add_wedge_invariant _ _

abbrev Coframe := Fin 4 → Fin 4 → ℝ
abbrev AlternatingCoframeScalar := (Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ

/-- Existence does not assume that the four-form already has determinant form. -/
theorem alternating_coframe_scalar_eq_determinant (f : AlternatingCoframeScalar)
    (e : Coframe) : f e = f (Pi.basisFun ℝ (Fin 4)) * (Matrix.of e).det := by
  have hf := f.eq_smul_basis_det (Pi.basisFun ℝ (Fin 4))
  have h := congrArg (fun g : AlternatingCoframeScalar => g e) hf
  simpa only [AlternatingMap.smul_apply, Pi.basisFun_det_apply, smul_eq_mul] using h

theorem alternating_coframe_scalar_unique (f : AlternatingCoframeScalar) :
    ∃! c : ℝ, ∀ e : Coframe, f e = c * (Matrix.of e).det := by
  refine ⟨f (Pi.basisFun ℝ (Fin 4)), alternating_coframe_scalar_eq_determinant f, ?_⟩
  intro c hc
  have h := hc (Pi.basisFun ℝ (Fin 4))
  have hb : (Matrix.of (Pi.basisFun ℝ (Fin 4))).det = 1 := by
    rw [← Pi.basisFun_det_apply]
    exact Module.Basis.det_self _
  rw [hb, mul_one] at h
  exact h.symm

/-- Lorentz covariance of the actual coframe determinant, not a supplied volume law. -/
theorem alternating_coframe_scalar_lorentz_invariant (f : AlternatingCoframeScalar)
    (L : SpacetimeMatrix) (hL : IsProperTimeOrientedLorentz L) (e : Coframe) :
    f (Matrix.of e * Lᵀ) = f e := by
  rw [alternating_coframe_scalar_eq_determinant,
    alternating_coframe_scalar_eq_determinant]
  simp only [Matrix.of_apply, Matrix.det_mul, Matrix.det_transpose, hL.2.1, mul_one]

end

end NCG.LorentzInvariantDensityClassification
