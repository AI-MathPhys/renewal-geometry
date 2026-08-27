/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AnomalyForcedWeights
import NCG.Grand.DeterminantIncidenceExact
import NCG.Grand.InternalAssemblyExact
import NCG.Grand.SMGaugeQuotientExact
import NCG.Grand.SMActiveStructural
import NCG.Grand.WeakResetGenerationExact

/-!
# Active finite structural Standard Model: exact assembly

This is the one-theorem assembly requested by `thm:SM-active-SM-I`.  It combines the already
proved positive-colour internal algebra, exact global gauge quotient, anomaly classification,
three-dimensional generation carrier, weak-doublet generation, normalized grading-odd Dirac
seed, and determinant-incidence reconstruction in one typed packet.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- The seven displayed integral weights, with the sterile-neutrino zero inserted before the
Higgs weight. -/
def smActiveHyperchargeWeights (a b : ℤ) : Fin 7 → ℤ :=
  ![smCentralWeights a b 0, smCentralWeights a b 1, smCentralWeights a b 2,
    smCentralWeights a b 3, smCentralWeights a b 4, 0, smCentralWeights a b 5]

/-- The exact anomaly classification used by the active finite assembly. -/
def SMAnomalyClassification : Prop :=
  (∀ a b : ℚ,
      ((3 * a + 2 * b) / 2 = 0
        ∧ 3 * (3 * a + 2 * b) = 0
        ∧ 3 * (3 * a + 2 * b) * (3 * a ^ 2 + 2 * b ^ 2) = 0)
      ↔ 3 * a + 2 * b = 0)
    ∧ (∀ a b : ℤ, 3 * a + 2 * b = 0 ↔
        ∃ t : ℤ, a = -2 * t ∧ b = 3 * t)
    ∧ (∀ a b : ℤ, 3 * a + 2 * b = 0 → IsCoprime a b →
        (a = -2 ∧ b = 3) ∨ (a = 2 ∧ b = -3))
    ∧ (smCentralWeights (-2) 3 = ![1, 4, -2, -3, -6, 3])

/-- The left/right tight-frame identities and orbit-span identity for the single normalized
grading-odd finite Dirac seed. -/
def SMActive.HasExactOddOrbit {H : Type} [Fintype H] [Nonempty H] [DecidableEq H]
    (D0 : Matrix H H ℂ) : Prop :=
  (SMActive.Bedge D0 0 1)ᴴ * SMActive.Bedge D0 0 1
      + (SMActive.Bedge D0 0 2)ᴴ * SMActive.Bedge D0 0 2
      + (SMActive.Bedge D0 0 3)ᴴ * SMActive.Bedge D0 0 3
      + (SMActive.Bedge D0 1 2)ᴴ * SMActive.Bedge D0 1 2
      + (SMActive.Bedge D0 1 3)ᴴ * SMActive.Bedge D0 1 3
      + (SMActive.Bedge D0 2 3)ᴴ * SMActive.Bedge D0 2 3
    = ((2 : ℂ) • ((1 : Matrix ActiveResidual.V ActiveResidual.V ℂ)
        - (4 : ℂ)⁻¹ • Matrix.of (fun _ _ => (1 : ℂ))))
      ⊗ₖ (1 : Matrix H H ℂ)
  ∧ SMActive.Bedge D0 0 1 * (SMActive.Bedge D0 0 1)ᴴ
      + SMActive.Bedge D0 0 2 * (SMActive.Bedge D0 0 2)ᴴ
      + SMActive.Bedge D0 0 3 * (SMActive.Bedge D0 0 3)ᴴ
      + SMActive.Bedge D0 1 2 * (SMActive.Bedge D0 1 2)ᴴ
      + SMActive.Bedge D0 1 3 * (SMActive.Bedge D0 1 3)ᴴ
      + SMActive.Bedge D0 2 3 * (SMActive.Bedge D0 2 3)ᴴ
    = ((2 : ℂ) • ((1 : Matrix ActiveResidual.V ActiveResidual.V ℂ)
        - (4 : ℂ)⁻¹ • Matrix.of (fun _ _ => (1 : ℂ))))
      ⊗ₖ (1 : Matrix H H ℂ)
  ∧ SMActive.Bedge D0 0 1 + SMActive.Bedge D0 0 2 + SMActive.Bedge D0 0 3
      + SMActive.Bedge D0 1 2 + SMActive.Bedge D0 1 3 + SMActive.Bedge D0 2 3
    = (2 : ℂ) • (((1 : Matrix ActiveResidual.V ActiveResidual.V ℂ)
        - (4 : ℂ)⁻¹ • Matrix.of (fun _ _ => (1 : ℂ))) ⊗ₖ D0)

/-- A single typed carrier containing all five conclusions of the active finite structural
Standard Model theorem. -/
structure ActiveFiniteStructuralStandardModelPacket
    {H : Type} [Fintype H] [Nonempty H] [DecidableEq H]
    (u : Matrix (Fin 7) (Fin 7) ℂ) (D0 Γ : Matrix H H ℂ)
    (t h : Fin 2 → ℂ) (T : DetIncidence.Shadow) where
  internalAlgebra : Algebra.adjoin ℂ (InternalAssembly.gens7 u) =
    InternalAssembly.blockAlgebra
  gaugeQuotient : SMGaugeCover ⧸ smGaugeHom.ker ≃* SMGaugeGroup
  gaugeCoverSurjective : Function.Surjective smGaugeHom
  anomalyClassification : SMAnomalyClassification
  hyperchargeTable : smActiveHyperchargeWeights (-2) 3 = ![1, 4, -2, -3, -6, 0, 3]
  generationRank : Module.finrank ℂ (LinearMap.ker SMActive.sumF) = 3
  weakDoubletGenerated : Algebra.adjoin ℂ
    {Matrix.vecMulVec t (star t), Matrix.vecMulVec h (star h)} = ⊤
  diracSelfAdjoint : D0ᴴ = D0
  diracGradingOdd : Γ * D0 = -(D0 * Γ)
  diracNonzero : D0 ≠ 0
  cliffordFlip : (Γ * D0) * (Γ * D0) = -1
  exactOddOrbit : SMActive.HasExactOddOrbit D0
  determinantReconstruction : DetIncidence.theta (DetIncidence.alt T) = T
  determinantSeed : ∃ τ : ℂ, τ ≠ 0 ∧ T = DetIncidence.theta τ

/-- **Unconditional active finite structural Standard Model (`thm:SM-active-SM-I`).**
Under precisely the positive colour bridge, weak reset, normalized self-adjoint grading-odd
Dirac seed, and nonzero fully alternating typed-word hypotheses, all structural conclusions are
assembled in one packet.  No extra Hilbert-space factor occurs in the construction. -/
theorem activeFiniteStructuralStandardModel
    {H : Type} [Fintype H] [Nonempty H] [DecidableEq H]
    (u : Matrix (Fin 7) (Fin 7) ℂ)
    (hsupp : InternalAssembly.ColourSupported u)
    (hcol : 0 < InternalAssembly.omega7 u)
    (D0 Γ : Matrix H H ℂ)
    (hDl : D0ᴴ * D0 = 1) (hDr : D0 * D0ᴴ = 1)
    (hself : D0ᴴ = D0) (hodd : Γ * D0 = -(D0 * Γ))
    (hΓ : Γ * Γ = 1)
    (t h : Fin 2 → ℂ)
    (hind : t 0 * h 1 - t 1 * h 0 ≠ 0)
    (hover : (∑ m, star (t m) * h m) ≠ 0)
    (T : DetIncidence.Shadow) (hT : DetIncidence.FullyAlternating T)
    (hdet : 0 < DetIncidence.mdet T) :
    Nonempty (ActiveFiniteStructuralStandardModelPacket u D0 Γ t h T) := by
  have hDsq : D0 * D0 = 1 := by
    calc
      D0 * D0 = D0 * D0ᴴ := by rw [hself]
      _ = 1 := hDr
  have hD0 : D0 ≠ 0 := by
    intro hz
    rw [hz, Matrix.conjTranspose_zero, Matrix.zero_mul] at hDl
    exact zero_ne_one hDl
  refine ⟨
    { internalAlgebra := (InternalAssembly.assembled_dichotomy u hsupp).2 hcol
      gaugeQuotient := smGaugeQuotientEquiv
      gaugeCoverSurjective := smGaugeHom_surjective
      anomalyClassification := by
        simpa [SMAnomalyClassification] using anomaly_forced_weights
      hyperchargeTable := by native_decide
      generationRank := SMActive.generation_rank
      weakDoubletGenerated := WeakReset.two_lines_generate t h hind hover
      diracSelfAdjoint := hself
      diracGradingOdd := hodd
      diracNonzero := hD0
      cliffordFlip := SMActive.clifford_flip Γ D0 hodd hΓ hDsq
      exactOddOrbit := ⟨SMActive.odd_orbit_tight_left D0 hDl,
        SMActive.odd_orbit_tight_right D0 hDr, SMActive.odd_orbit_span D0⟩
      determinantReconstruction := DetIncidence.theta_of_alternating hT
      determinantSeed := (DetIncidence.mdet_pos_iff hT).1 hdet }⟩

end NCG



