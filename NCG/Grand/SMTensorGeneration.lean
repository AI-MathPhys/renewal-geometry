/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.TensorExteriorAnomalyPacket
import NCG.Flagship.MinimalNaturality

/-!
# Tensor generation of one chiral Standard Model packet

Finite representation data for `thm:SM-generation`.  The tensor, dual, and
exterior-square constructions produce the six exact dimension/charge labels.
The weak alternating tensor and the evaluation tensor are then shown to span
one-dimensional solution spaces; the colour intertwiner is scalar by the
full-matrix commutant theorem.  These are the three Yukawa intertwiner lines.
-/

open Matrix

namespace NCG
namespace SMTensorGeneration

/-- Finite label `(colour dimension, weak dimension, integer charge)`. -/
structure MatterLabel where
  colourDim : ℕ
  weakDim : ℕ
  charge : ℤ
  deriving DecidableEq

/-- The six tensor-generated rows `Q,u,d,L,e,H`. -/
def generatedMatterLabels : Fin 6 → MatterLabel :=
  ![⟨3, 2, 1⟩, ⟨3, 1, 4⟩, ⟨3, 1, -2⟩,
    ⟨1, 2, -3⟩, ⟨1, 1, -6⟩, ⟨1, 2, 3⟩]

/-- Tensor dimensions and exterior-square dimensions give exactly the
manuscript's colour/weak size table. -/
theorem generatedMatter_dimension_table :
    (3 * 2 = (generatedMatterLabels 0).colourDim *
        (generatedMatterLabels 0).weakDim) ∧
    (Nat.choose 3 2 = (generatedMatterLabels 1).colourDim) ∧
    (3 = (generatedMatterLabels 2).colourDim) ∧
    (2 = (generatedMatterLabels 3).weakDim) ∧
    (Nat.choose 2 2 = (generatedMatterLabels 4).weakDim) ∧
    (2 = (generatedMatterLabels 5).weakDim) := by
  decide

/-- Propagating the primitive charges `C ↦ -2`, `W ↦ 3` through tensor,
dual, and exterior square gives all six integer charges. -/
theorem generatedMatter_charge_table :
    tensorExteriorCentralWeights (-2) 3 =
      fun i => ((generatedMatterLabels i).charge : ℚ) := by
  funext i
  fin_cases i <;> norm_num [tensorExteriorCentralWeights,
    generatedMatterLabels]

/-- Standard alternating tensor on the weak doublet. -/
def weakAlternating : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; -1, 0]

theorem weakAlternating_skew (i j : Fin 2) :
    weakAlternating i j = -weakAlternating j i := by
  fin_cases i <;> fin_cases j <;> simp [weakAlternating]

/-- Every alternating bilinear form on a two-dimensional complex space is a
unique scalar multiple of the standard epsilon tensor. -/
theorem alternatingWeakIntertwiner_unique
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ i j, A i j = -A j i) :
    ∃! c : ℂ, A = c • weakAlternating := by
  have h00 : A 0 0 = 0 := by
    have h := hA 0 0
    linear_combination h / 2
  have h11 : A 1 1 = 0 := by
    have h := hA 1 1
    linear_combination h / 2
  have h10 : A 1 0 = -A 0 1 := hA 1 0
  refine ⟨A 0 1, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weakAlternating, h00, h11, h10]
  · intro c hc
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hc
    simpa [weakAlternating] using h.symm

/-- Evaluation is the unique weak endomorphism commuting with the full weak
matrix algebra. -/
theorem evaluationWeakIntertwiner_unique
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, X * A = A * X) :
    ∃ c : ℂ, A = c • 1 :=
  full_commutant_scalar A hA

/-- The colour factor in either quark Yukawa channel is likewise a unique
scalar multiple of the identity intertwiner. -/
theorem colourIntertwiner_unique
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, X * A = A * X) :
    ∃ c : ℂ, A = c • 1 :=
  full_commutant_scalar A hA

/-- The three seed Yukawa channels are one-dimensional: the up and lepton
weak contractions are alternating lines, the down weak contraction is the
evaluation line, and the quark colour transport is the identity line. -/
theorem yukawaIntertwinerLines
    (upWeak downWeak leptonWeak : Matrix (Fin 2) (Fin 2) ℂ)
    (upColour downColour : Matrix (Fin 3) (Fin 3) ℂ)
    (hup : ∀ i j, upWeak i j = -upWeak j i)
    (hlepton : ∀ i j, leptonWeak i j = -leptonWeak j i)
    (hdown : ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
      X * downWeak = downWeak * X)
    (hupColour : ∀ X : Matrix (Fin 3) (Fin 3) ℂ,
      X * upColour = upColour * X)
    (hdownColour : ∀ X : Matrix (Fin 3) (Fin 3) ℂ,
      X * downColour = downColour * X) :
    (∃! c : ℂ, upWeak = c • weakAlternating) ∧
    (∃ c : ℂ, downWeak = c • 1) ∧
    (∃! c : ℂ, leptonWeak = c • weakAlternating) ∧
    (∃ c : ℂ, upColour = c • 1) ∧
    (∃ c : ℂ, downColour = c • 1) :=
  ⟨alternatingWeakIntertwiner_unique upWeak hup,
    evaluationWeakIntertwiner_unique downWeak hdown,
    alternatingWeakIntertwiner_unique leptonWeak hlepton,
    colourIntertwiner_unique upColour hupColour,
    colourIntertwiner_unique downColour hdownColour⟩

/-- Exact tensor-generation bundle: label table, exterior-square dimensions,
and all three one-dimensional Yukawa intertwiner spaces. -/
theorem sm_tensor_generation_exact :
    tensorExteriorCentralWeights (-2) 3 =
      (fun i => ((generatedMatterLabels i).charge : ℚ)) ∧
    Nat.choose 3 2 = 3 ∧ Nat.choose 2 2 = 1 ∧
    (∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i j, A i j = -A j i) →
        ∃! c : ℂ, A = c • weakAlternating) ∧
    (∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      (∀ X, X * A = A * X) → ∃ c : ℂ, A = c • 1) ∧
    (∀ A : Matrix (Fin 3) (Fin 3) ℂ,
      (∀ X, X * A = A * X) → ∃ c : ℂ, A = c • 1) := by
  refine ⟨generatedMatter_charge_table, by norm_num, by norm_num,
    ?_, ?_, ?_⟩
  · exact fun A hA => alternatingWeakIntertwiner_unique A hA
  · exact fun A hA => evaluationWeakIntertwiner_unique A hA
  · exact fun A hA => colourIntertwiner_unique A hA

end SMTensorGeneration
end NCG
