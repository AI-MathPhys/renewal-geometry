/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExceptionalS4MultiplicityMatrixAssembly

/-!
# Amplified Schur reduction for the exceptional `S₄` panel

The concrete carrier calculation classifies each irreducible matrix slice.
This file performs the previously implicit amplification step: applying that
classification at every pair of multiplicity indices assembles the slice
scalars into one multiplicity matrix.  Thus the three surviving amplified
blocks are genuinely `I₁ ⊗ A₁`, `I₃ ⊗ A₃`, and `C₂₂ ⊗ A₂`.
-/

open Matrix

namespace NCG
namespace ExceptionalS4AmplifiedSchurExact

noncomputable section

open ExceptionalS4GeneratorSchurCertificate

/-- The irreducible-carrier slice of an amplified block at fixed target and
source multiplicity indices. -/
def amplifiedSlice {a b m n : Type*}
    (A : Matrix (a × m) (b × n) ℂ) (μ : m) (ν : n) : Matrix a b ℂ :=
  fun i j => A (i, μ) (j, ν)

/-- Generic amplification of a one-dimensional carrier intertwiner space.
If every multiplicity slice is a scalar multiple of the same carrier matrix
`J`, those scalars assemble into one rectangular multiplicity matrix. -/
theorem amplified_factor_of_slice_classifier
    {a b m n : Type*} (A : Matrix (a × m) (b × n) ℂ)
    (J : Matrix a b ℂ) (P : Matrix a b ℂ → Prop)
    (hclass : ∀ X, P X → ∃ z : ℂ, X = z • J)
    (hP : ∀ μ ν, P (amplifiedSlice A μ ν)) :
    ∃ C : Matrix m n ℂ, ∀ i μ j ν,
      A (i, μ) (j, ν) = C μ ν * J i j := by
  let coeff : m → n → ℂ := fun μ ν =>
    Classical.choose (hclass (amplifiedSlice A μ ν) (hP μ ν))
  refine ⟨coeff, ?_⟩
  intro i μ j ν
  have hs := Classical.choose_spec
    (hclass (amplifiedSlice A μ ν) (hP μ ν))
  have hij := congrFun (congrFun hs i) j
  simpa [amplifiedSlice, coeff, Matrix.smul_apply, mul_comm] using hij

/-- Exact arbitrary-multiplicity reduction of the three surviving exceptional
blocks.  This is the amplified Schur step needed before self-adjointness and
contraction positivity are packaged by `SelfAdjointCovariantMultiplicityData`.
-/
theorem exceptionalS4_threeAmplifiedBlocks_factor
    {m1 msgn m31 m211 m22 : Type*}
    (T1 : Matrix (Fin 1 × msgn) (Fin 1 × m1) ℂ)
    (T3 : Matrix (Fin 3 × m211) (Fin 3 × m31) ℂ)
    (T2 : Matrix (Fin 2 × m22) (Fin 2 × m22) ℂ)
    (h3S : ∀ μ ν,
      standardTransposition * amplifiedSlice T3 μ ν =
        amplifiedSlice T3 μ ν * standardTransposition)
    (h3R : ∀ μ ν,
      standardFourCycle * amplifiedSlice T3 μ ν =
        amplifiedSlice T3 μ ν * standardFourCycle)
    (h2S : ∀ μ ν,
      pairingTransposition * amplifiedSlice T2 μ ν =
        -(amplifiedSlice T2 μ ν * pairingTransposition))
    (h2R : ∀ μ ν,
      pairingFourCycle * amplifiedSlice T2 μ ν =
        -(amplifiedSlice T2 μ ν * pairingFourCycle)) :
    ∃ (A1 : Matrix msgn m1 ℂ) (A3 : Matrix m211 m31 ℂ)
      (A2 : Matrix m22 m22 ℂ),
      (∀ i μ j ν, T1 (i, μ) (j, ν) = A1 μ ν) ∧
      (∀ i μ j ν,
        T3 (i, μ) (j, ν) = A3 μ ν * (1 : Matrix (Fin 3) (Fin 3) ℂ) i j) ∧
      (∀ i μ j ν,
        T2 (i, μ) (j, ν) = A2 μ ν * pairingSignTwist i j) := by
  let A1 : Matrix msgn m1 ℂ := fun μ ν => T1 (0, μ) (0, ν)
  obtain ⟨A3, hA3⟩ := amplified_factor_of_slice_classifier T3
    (1 : Matrix (Fin 3) (Fin 3) ℂ)
    (fun X =>
      standardTransposition * X = X * standardTransposition ∧
      standardFourCycle * X = X * standardFourCycle)
    (fun X h => standard_generator_commutant X h.1 h.2)
    (fun μ ν => ⟨h3S μ ν, h3R μ ν⟩)
  obtain ⟨A2, hA2⟩ := amplified_factor_of_slice_classifier T2
    pairingSignTwist
    (fun X =>
      pairingTransposition * X = -(X * pairingTransposition) ∧
      pairingFourCycle * X = -(X * pairingFourCycle))
    (fun X h => pairing_generator_anticommutant X h.1 h.2)
    (fun μ ν => ⟨h2S μ ν, h2R μ ν⟩)
  refine ⟨A1, A3, A2, ?_, hA3, hA2⟩
  intro i μ j ν
  fin_cases i
  fin_cases j
  rfl

end
end ExceptionalS4AmplifiedSchurExact
end NCG
