/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LorentzBivectorInvariantFormsExact

/-!
# Classification of real Lorentz-natural bivector endomorphisms

The commutant of the actual exterior-square representation of the proper,
time-oriented Lorentz group is exactly the real span of identity and Hodge
star. Necessity uses two actual rotations and one actual rational boost;
sufficiency uses Hodge naturality for every Lorentz matrix.
-/

open Matrix
open scoped BigOperators

namespace NCG.LorentzBivectorCommutant

open BivectorRotationCommutant LorentzBivectorAction LorentzBivectorInvariantForms

noncomputable section

def LorentzNatural (T : BivectorMatrix) : Prop :=
  ∀ L : SpacetimeMatrix, IsProperTimeOrientedLorentz L →
    T * bivectorAction L = bivectorAction L * T

theorem boost_forces_hodge_blocks (C : Matrix (Fin 2) (Fin 2) ℝ)
    (h : scalarBlocks C * bivectorAction rationalBoost =
      bivectorAction rationalBoost * scalarBlocks C) :
    C 1 1 = C 0 0 ∧ C 1 0 = -C 0 1 := by
  have hd := congrFun (congrFun h (0, 1)) (1, 2)
  have ho := congrFun (congrFun h (0, 1)) (0, 2)
  norm_num [scalarBlocks, bivectorAction, rationalBoost, framePair,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three] at hd ho
  constructor <;> linarith

theorem scalarBlocks_eq_identity_add_hodge (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : C 1 1 = C 0 0) (ho : C 1 0 = -C 0 1) :
    scalarBlocks C = C 0 0 • (1 : BivectorMatrix) + C 0 1 • hodgeStar := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [scalarBlocks, hodgeStar, hd, ho, Matrix.one_apply]

/-- Explicit coefficient extraction from any genuinely Lorentz-natural map. -/
theorem lorentzNatural_eq_identity_add_hodge (T : BivectorMatrix)
    (hT : LorentzNatural T) :
    T = T (0, 0) (0, 0) • (1 : BivectorMatrix) + T (0, 0) (1, 0) • hodgeStar := by
  have hh := hT halfTurnRotation halfTurnRotation_lorentz
  have hc := hT cycleRotation cycleRotation_lorentz
  rw [bivectorAction_halfTurnRotation] at hh
  rw [bivectorAction_cycleRotation] at hc
  have hs := rotation_commutant_scalar_blocks T hh hc
  have hb := hT rationalBoost rationalBoost_lorentz
  rw [hs] at hb
  obtain ⟨hd, ho⟩ := boost_forces_hodge_blocks _ hb
  exact hs.trans (scalarBlocks_eq_identity_add_hodge _ hd ho)

theorem identity_add_hodge_lorentzNatural (a b : ℝ) :
    LorentzNatural (a • (1 : BivectorMatrix) + b • hodgeStar) := by
  intro L hL
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [hodgeStar_commutes_lorentz L hL]

theorem identity_hodge_coefficients_unique (a b c d : ℝ)
    (h : a • (1 : BivectorMatrix) + b • hodgeStar = c • 1 + d • hodgeStar) :
    a = c ∧ b = d := by
  have ha := congrFun (congrFun h (0, 0)) (0, 0)
  have hb := congrFun (congrFun h (0, 0)) (1, 0)
  simpa [hodgeStar, scalarBlocks, Matrix.one_apply] using And.intro ha hb

/-- The real commutant classification, with uniquely determined coefficients. -/
theorem lorentzNatural_iff_existsUnique (T : BivectorMatrix) :
    LorentzNatural T ↔ ∃! ab : ℝ × ℝ, T = ab.1 • (1 : BivectorMatrix) + ab.2 • hodgeStar := by
  constructor
  · intro hT
    refine ⟨(T (0, 0) (0, 0), T (0, 0) (1, 0)),
      lorentzNatural_eq_identity_add_hodge T hT, ?_⟩
    intro ab hab
    have h := identity_hodge_coefficients_unique ab.1 ab.2
      (T (0, 0) (0, 0)) (T (0, 0) (1, 0))
      (hab.symm.trans (lorentzNatural_eq_identity_add_hodge T hT))
    exact Prod.ext h.1 h.2
  · rintro ⟨ab, hab, _⟩
    rw [hab]
    exact identity_add_hodge_lorentzNatural _ _

end

end NCG.LorentzBivectorCommutant
