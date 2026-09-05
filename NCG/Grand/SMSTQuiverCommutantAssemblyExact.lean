/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTCommutant

/-!
# Complete finite multiplicity-quiver commutant packet

This assembles the central-block calculation of SMSTCommutant into the two
actual spaces appearing in thm:SMST-quiver-commutant. The ambient commutant
consists of residual central families commuting with every reconstructed
typed arrow. The quiver endomorphism space consists of the coefficientwise
intertwiners. The canonical equivalence is the identity on the residual
family, with its two well-definedness directions supplied by the proved
block-expansion theorem.
-/

open Matrix

namespace NCG
namespace SMSTQuiverCommutantAssembly

/-- Residual central families that commute with every reconstructed typed
arrow of a finite multiplicity packet. -/
def AmbientCommutant
    {A J : Type} [Fintype J]
    (V N : A → Type*) [∀ a, Fintype (V a)] [∀ a, Fintype (N a)]
    [∀ a, DecidableEq (V a)] [∀ a, Nonempty (N a)]
    (src dst : J → A)
    (B : ∀ j, V (dst j) → V (src j) →
      Matrix (N (dst j)) (N (src j)) ℂ) :=
  {X : ∀ a, Matrix (N a) (N a) ℂ //
    ∀ j,
      quiverMatMul (quiverResidual (X (dst j))) (quiverAssemble (B j)) =
        quiverMatMul (quiverAssemble (B j))
          (quiverResidual (X (src j)))}

/-- Endomorphisms of the associated finite multiplicity quiver. -/
def QuiverEndomorphism
    {A J : Type} [Fintype J]
    (V N : A → Type*) [∀ a, Fintype (V a)] [∀ a, Fintype (N a)]
    (src dst : J → A)
    (B : ∀ j, V (dst j) → V (src j) →
      Matrix (N (dst j)) (N (src j)) ℂ) :=
  {X : ∀ a, Matrix (N a) (N a) ℂ //
    ∀ j vb va,
      X (dst j) * B j vb va = B j vb va * X (src j)}

/-- The boxed commutant/quiver identification. After central decomposition
the equivalence is literally the identity on the family of multiplicity
operators. -/
def commutantEquivEndomorphism
    {A J : Type} [Fintype J]
    (V N : A → Type*) [∀ a, Fintype (V a)] [∀ a, Fintype (N a)]
    [∀ a, DecidableEq (V a)] [∀ a, Nonempty (N a)]
    (src dst : J → A)
    (B : ∀ j, V (dst j) → V (src j) →
      Matrix (N (dst j)) (N (src j)) ℂ) :
    AmbientCommutant V N src dst B ≃
      QuiverEndomorphism V N src dst B where
  toFun X :=
    ⟨X.1, (finite_typed_quiver_commutant_iff_endomorphism
      V N src dst B X.1).mp X.2⟩
  invFun X :=
    ⟨X.1, (finite_typed_quiver_commutant_iff_endomorphism
      V N src dst B X.1).mpr X.2⟩
  left_inv X := by cases X; rfl
  right_inv X := by cases X; rfl

@[simp]
theorem commutantEquivEndomorphism_apply
    {A J : Type} [Fintype J]
    (V N : A → Type*) [∀ a, Fintype (V a)] [∀ a, Fintype (N a)]
    [∀ a, DecidableEq (V a)] [∀ a, Nonempty (N a)]
    (src dst : J → A)
    (B : ∀ j, V (dst j) → V (src j) →
      Matrix (N (dst j)) (N (src j)) ℂ)
    (X : AmbientCommutant V N src dst B) :
    (commutantEquivEndomorphism V N src dst B X).1 = X.1 := rfl

/-- Complete theorem packet: canonical commutant equivalence, exact
Hilbert--Schmidt coefficient expansion, and kernel equal to the quiver
endomorphism space. -/
theorem smst_quiver_commutant_complete
    {A J : Type} [Fintype J]
    (V N : A → Type*) [∀ a, Fintype (V a)] [∀ a, Fintype (N a)]
    [∀ a, DecidableEq (V a)] [∀ a, Nonempty (N a)]
    (src dst : J → A)
    (B : ∀ j, V (dst j) → V (src j) →
      Matrix (N (dst j)) (N (src j)) ℂ)
    (X : ∀ a, Matrix (N a) (N a) ℂ)
    (volume : ℝ) (hvolume : 0 < volume) :
    Nonempty (AmbientCommutant V N src dst B ≃
      QuiverEndomorphism V N src dst B)
      ∧ (volume⁻¹ * ∑ j,
          quiverHSSq
            (quiverMatMul (quiverResidual (X (dst j)))
                (quiverAssemble (B j))
              - quiverMatMul (quiverAssemble (B j))
                  (quiverResidual (X (src j)))) =
        volume⁻¹ * ∑ j, ∑ vb, ∑ va,
          quiverHSSq
            (X (dst j) * B j vb va - B j vb va * X (src j)))
      ∧ ((volume⁻¹ * ∑ j, ∑ vb, ∑ va,
          quiverHSSq
            (X (dst j) * B j vb va - B j vb va * X (src j)) = 0)
        ↔ ∀ j vb va,
          X (dst j) * B j vb va = B j vb va * X (src j)) := by
  refine ⟨⟨commutantEquivEndomorphism V N src dst B⟩, ?_, ?_⟩
  · exact finite_typed_quiver_hs_expansion
      V N src dst B X volume
  · exact finite_typed_quiver_form_kernel
      V N src dst B X volume hvolume

end SMSTQuiverCommutantAssembly
end NCG
