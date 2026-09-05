/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ArithmeticRecordMargins
import NCG.Grand.PeanoMultiplicationHistory
import NCG.Grand.PeanoLadder
import NCG.Grand.ZetaIncidence
import NCG.Grand.ArFiniteEuler
import NCG.Grand.ContractionChainStability
import NCG.Grand.ScalarLoadingClassification
import NCG.Grand.ArDerivedPacket
import NCG.Grand.RecordCutoff
import NCG.Grand.AbsorbingCutoff
import NCG.Grand.ArForwardGeneration
import NCG.Grand.ArStandardComparison
import NCG.Grand.ArCompilerRouting
import NCG.Grand.ArithmeticChronologyCornerConservativity

/-!
# Canonical arithmetic loading

The old `ArithmeticLoading` declaration contained only three generic matrix
lemmas.  This module assembles the actual cutoff chronology and its canonical
arithmetic histories.  Each field below is a concrete clause of A1--A10 and is
filled by the corresponding proved finite theorem; no arithmetic history is
passed in as an assumption.
-/

open Matrix

namespace NCG

/-- Concrete ten-clause arithmetic loading certificate at a positive cutoff.
The more elaborate loaded-word hierarchy is represented by its canonical
finite generating algebra and exact cutoff corners. -/
structure CanonicalArithmeticLoadingCertificate (X : ℕ) (hX : 0 < X) : Prop where
  /-- A1: protected chronology reads are orthonormal. -/
  chronologyGram : ∀ i j : Fin X,
    star (Pi.single i (1 : ℂ)) ⬝ᵥ
      ((recS X) ^ (j : ℕ) *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) =
        if i = j then 1 else 0
  /-- A1: predictable backflow vanishes. -/
  backflowZero : recBackflow X = 0
  /-- A2: anchor and covariance uniquely determine multiplication. -/
  peanoUnique : ∀ (a : ℕ) (ha : 1 ≤ a) (M : Matrix (Fin X) (Fin X) ℂ),
    M *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
        recS X ^ (a - 1) *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 →
    M * recS X = recS X ^ a * M → M = peanoL X a
  /-- A2: the canonical multiplication histories multiply exactly. -/
  peanoMultiplicative : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    peanoL X a * peanoL X b = peanoL X (a * b)
  /-- A2: the count history is rigid. -/
  countRigid : ∀ D : Matrix (Fin X) (Fin X) ℂ,
    D *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
        Pi.single (⟨0, hX⟩ : Fin X) 1 →
    D * recS X - recS X * D = recS X →
    D = Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ))
  /-- A3: the zeta history is the unit-weight divisibility incidence matrix. -/
  zetaIncidence : ∀ m b : Fin X,
    Matrix.single m m (1 : ℂ) * zetaX X * Matrix.single b b 1 =
      if ((b : ℕ) + 1) ∣ ((m : ℕ) + 1)
      then Matrix.single m b 1 else 0
  /-- A3: the zeta nilpotent part terminates at the cutoff. -/
  zetaTerminates : (zetaX X - 1) ^ X = 0
  /-- A3: the logarithmic commutator recovers von Mangoldt. -/
  vonMangoldtColumn :
    (countLog X * logZop X - logZop X * countLog X) *ᵥ
        Pi.single (⟨0, hX⟩ : Fin X) 1 =
      fun i : Fin X =>
        (ArithmeticFunction.vonMangoldt ((i : ℕ) + 1) : ℂ)
  /-- A4: every unitary chronology intertwiner transports count and Peano. -/
  chronologyNatural : ∀ U : Matrix (Fin X) (Fin X) ℂ,
    Uᴴ * U = 1 → U * Uᴴ = 1 → U * recS X = recS X * U →
    (U * Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ)) =
      Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ)) * U) ∧
    (∀ a : ℕ, U * peanoL X a = peanoL X a * U) ∧
    (U *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
      Pi.single (⟨0, hX⟩ : Fin X) 1 → U = 1)
  /-- A5: normalized prime weights recover exactly the canonical zeta. -/
  normalizedWeights : ∀ (c : ℕ → ℂ), c 1 = 1 →
    (∀ a b, 1 ≤ a → 1 ≤ b → c (a * b) = c a * c b) →
    (∀ p, p.Prime → p ≤ X → c p = 1) →
    weightedZeta X c = zetaX X
  /-- A6: Peano and count residuals vanish only at the canonical histories. -/
  residualRigidity : ∀ (a : ℕ) (ha : 1 ≤ a)
      (A D : Matrix (Fin X) (Fin X) ℂ),
    (peanoResidual hX a A = 0 ↔ A = peanoL X a) ∧
    (countResidual hX D = 0 ↔
      D = Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ)))
  /-- A6: the explicit finite stability inequalities. -/
  residualStability : ∀ (a : ℕ) (ha : 1 ≤ a)
      (A D : Matrix (Fin X) (Fin X) ℂ),
    hsMatrixSq (A - peanoL X a) ≤ (X : ℝ) ^ 2 * peanoResidual hX a A ∧
    hsMatrixSq (D - Matrix.diagonal
      (fun i : Fin X => ((i : ℕ) + 1 : ℂ))) ≤
        (X : ℝ) ^ 2 * countResidual hX D
  /-- A7: forward records plus adjoints generate the full finite history
  algebra (finite flatness of the concrete hierarchy). -/
  fullStarGeneration : StarAlgebra.adjoin ℂ
    ({recS X} : Set (Matrix (Fin X) (Fin X) ℂ)) = ⊤
  /-- A8: every forward chronology/multiplication history compresses exactly. -/
  cutoffExact : ∀ (Y a : ℕ), X ≤ Y →
    (cornerJ X Y)ᴴ * recS Y * cornerJ X Y = recS X ∧
    (cornerJ X Y)ᴴ * peanoL Y a * cornerJ X Y = peanoL X a
  /-- A9: a source-fixing standard chronology comparison is unique. -/
  standardRecognition : ∀ U : Matrix (Fin X) (Fin X) ℂ,
    U * Matrix.diagonal (fun i : Fin X => (((i : ℕ) + 1 : ℕ) : ℂ)) =
        Matrix.diagonal (fun i : Fin X => (((i : ℕ) + 1 : ℕ) : ℂ)) * U →
    U * recS X = recS X * U →
    U *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
        Pi.single (⟨0, hX⟩ : Fin X) 1 → U = 1
  /-- A10: every intrinsic diagonal readout routes through the canonical
  von-Mangoldt source column. -/
  compilerReadout : ∀ χw : ℕ → ℂ,
    diagFn X χw *ᵥ ((countLog X * logZop X - logZop X * countLog X) *ᵥ
      Pi.single (⟨0, hX⟩ : Fin X) 1) =
      fun i : Fin X => χw ((i : ℕ) + 1) *
        (ArithmeticFunction.vonMangoldt ((i : ℕ) + 1) : ℂ)

/-- `thm:arithmetic-loading`: the canonical arithmetic packet is constructed
unconditionally from the protected positive chronology record. -/
theorem canonical_arithmetic_loading (X : ℕ) (hX : 0 < X) :
    CanonicalArithmeticLoadingCertificate X hX := by
  have hmargins := arithmetic_record_margins_exact X hX
  have heuler := ar_finite_euler hX
  have hforward := ar_forward_generation hX
  refine {
    chronologyGram := hmargins.1
    backflowZero := hmargins.2.1
    peanoUnique := ?_
    peanoMultiplicative := ?_
    countRigid := count_rigidity hX
    zetaIncidence := (zeta_incidence (X := X)).2.1
    zetaTerminates := (zeta_incidence (X := X)).2.2.2.2
    vonMangoldtColumn := heuler.2.2.1
    chronologyNatural := peano_naturality hX
    normalizedWeights := prime_normalization_recovers_zeta hX
    residualRigidity := ?_
    residualStability := ?_
    fullStarGeneration := hforward.2.2.2
    cutoffExact := ?_
    standardRecognition := ar_standard_comparison hX
    compilerReadout := (ar_derived_packet hX).2.2.2.2 }
  · intro a ha M hanchor hcov
    exact (peano_multiplication_exact hX a ha).1 M hanchor hcov
  · intro a b ha hb
    exact (peano_multiplication_exact hX a ha).2.2.2.1 b hb
  · intro a ha A D
    exact (ar_peano_stability_exact hX a ha A D).1
  · intro a ha A D
    exact (ar_peano_stability_exact hX a ha A D).2
  · intro Y a hXY
    have h := record_cutoff hXY a
    exact ⟨h.1, h.2.2⟩

end NCG
