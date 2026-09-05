/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandInterface2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Positive-gauge reconstruction of a block Jacobi chain

This module supplies the uniqueness clause of
`thm:matrix-continued-fraction` from the Gran-Tensor manuscript.  The constant
and inverse-energy coefficients of each tail response recover the diagonal
block and the coupling Gram.  Positivity makes the coupling itself the unique
positive square root, and the reverse Schur recursion exposes the next tail.
-/

open Filter Matrix
open scoped Topology MatrixOrder

namespace NCG
namespace PositiveGaugeJacobiLayerReconstruction

variable {b : Type*} [Fintype b] [DecidableEq b]

abbrev Block (b : Type*) := Matrix b b ℂ

/-- The imaginary high-energy ray used for coefficient extraction. -/
def imaginaryEnergy (t : ℝ) : ℂ := Complex.I * t

/-- The response after subtracting its leading `zI` term. -/
def constantCoefficientProbe (Λ : ℂ → Block b) (t : ℝ) : Block b :=
  Λ (imaginaryEnergy t) - imaginaryEnergy t • (1 : Block b)

/-- After the constant coefficient is restored, multiplication by `z`
extracts the inverse-energy coefficient. -/
def inverseCoefficientProbe (Λ : ℂ → Block b) (C : Block b) (t : ℝ) : Block b :=
  imaginaryEnergy t •
    (Λ (imaginaryEnergy t) - imaginaryEnergy t • (1 : Block b) + C)

/-- A validated positive-gauge block Jacobi response tower.  Its asymptotic
fields are exactly
`Λ_k(z) = zI - C_k - z⁻¹ B_kᴴB_k + O(z⁻²)`, expressed by coefficient limits;
`strip` is the reverse Schur recursion already proved by `NCG.layer_stripping`.
-/
structure PositiveGaugeJacobiChain (layers : ℕ) where
  response : Fin (layers + 1) → ℂ → Block b
  center : Fin (layers + 1) → Block b
  coupling : Fin layers → Block b
  constantAsymptotic : ∀ k,
    Tendsto (constantCoefficientProbe (response k)) atTop (𝓝 (-center k))
  inverseAsymptotic : ∀ k : Fin layers,
    Tendsto
      (inverseCoefficientProbe (response k.castSucc) (center k.castSucc))
      atTop (𝓝 (-(coupling k)ᴴ * coupling k))
  couplingPositive : ∀ k, 0 ≤ coupling k
  strip : ∀ (k : Fin layers) (z : ℂ),
    response k.succ z =
      -(coupling k *
        (response k.castSucc z - z • (1 : Block b) + center k.castSucc)⁻¹ *
        (coupling k)ᴴ)

theorem center_eq_of_response_eq {layers : ℕ}
    (P Q : PositiveGaugeJacobiChain (b := b) layers)
    (k : Fin (layers + 1))
    (hΛ : P.response k = Q.response k) :
    P.center k = Q.center k := by
  have hprobe : constantCoefficientProbe (P.response k) =
      constantCoefficientProbe (Q.response k) := by
    rw [hΛ]
  have hlimP := P.constantAsymptotic k
  have hlimQ := Q.constantAsymptotic k
  rw [hprobe] at hlimP
  exact neg_injective (tendsto_nhds_unique hlimP hlimQ)

theorem couplingGram_eq_of_response_eq {layers : ℕ}
    (P Q : PositiveGaugeJacobiChain (b := b) layers)
    (k : Fin layers)
    (hΛ : P.response k.castSucc = Q.response k.castSucc) :
    (P.coupling k)ᴴ * P.coupling k =
      (Q.coupling k)ᴴ * Q.coupling k := by
  have hC : P.center k.castSucc = Q.center k.castSucc :=
    center_eq_of_response_eq P Q k.castSucc hΛ
  have hprobe :
      inverseCoefficientProbe (P.response k.castSucc) (P.center k.castSucc) =
      inverseCoefficientProbe (Q.response k.castSucc) (Q.center k.castSucc) := by
    rw [hΛ, hC]
  have hlimP := P.inverseAsymptotic k
  have hlimQ := Q.inverseAsymptotic k
  rw [hprobe] at hlimP
  have hneg := tendsto_nhds_unique hlimP hlimQ
  have hneg' : -((P.coupling k)ᴴ * P.coupling k) =
      -((Q.coupling k)ᴴ * Q.coupling k) := by
    simpa only [neg_mul] using hneg
  exact neg_injective hneg'

/-- In positive gauge the recovered Gram matrix determines the coupling, by
uniqueness of the positive square root in the matrix C*-algebra. -/
theorem coupling_eq_of_response_eq {layers : ℕ}
    (P Q : PositiveGaugeJacobiChain (b := b) layers)
    (k : Fin layers)
    (hΛ : P.response k.castSucc = Q.response k.castSucc) :
    P.coupling k = Q.coupling k := by
  have hgram := couplingGram_eq_of_response_eq P Q k hΛ
  have hP := P.couplingPositive k
  have hQ := Q.couplingPositive k
  have hPstar : (P.coupling k)ᴴ = P.coupling k := by
    rw [← star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  have hQstar : (Q.coupling k)ᴴ = Q.coupling k := by
    rw [← star_eq_conjTranspose]
    exact hQ.isSelfAdjoint.star_eq
  have hsq : P.coupling k * P.coupling k =
      Q.coupling k * Q.coupling k := by
    simpa only [hPstar, hQstar] using hgram
  exact (CFC.mul_self_eq_mul_self_iff
    (P.coupling k) (Q.coupling k) hP hQ).mp hsq

/-- Equality of one tail response reconstructs the next response after the
center and positive coupling have been extracted. -/
theorem next_response_eq_of_response_eq {layers : ℕ}
    (P Q : PositiveGaugeJacobiChain (b := b) layers)
    (k : Fin layers)
    (hΛ : P.response k.castSucc = Q.response k.castSucc) :
    P.response k.succ = Q.response k.succ := by
  have hC := center_eq_of_response_eq P Q k.castSucc hΛ
  have hB := coupling_eq_of_response_eq P Q k hΛ
  funext z
  rw [P.strip, Q.strip, hΛ, hC, hB]

/-- `thm:matrix-continued-fraction`, positive-gauge uniqueness clause: the
complete boundary response `Λ₀` uniquely reconstructs every diagonal block,
every positive coupling, and every successive tail response. -/
theorem completeResponse_unique_reconstruction {layers : ℕ}
    (P Q : PositiveGaugeJacobiChain (b := b) layers)
    (h₀ : P.response 0 = Q.response 0) :
    P.center = Q.center ∧ P.coupling = Q.coupling ∧
      P.response = Q.response := by
  have hresponse : ∀ n (hn : n ≤ layers),
      P.response ⟨n, Nat.lt_succ_iff.mpr hn⟩ =
        Q.response ⟨n, Nat.lt_succ_iff.mpr hn⟩ := by
    intro n hn
    induction n with
    | zero => simpa using h₀
    | succ n ih =>
        have hn' : n ≤ layers := Nat.le_trans (Nat.le_succ n) hn
        let k : Fin layers := ⟨n, Nat.lt_of_succ_le hn⟩
        have hk : P.response k.castSucc = Q.response k.castSucc := by
          simpa [k] using ih hn'
        simpa [k] using next_response_eq_of_response_eq P Q k hk
  have hcenter : P.center = Q.center := by
    funext k
    exact center_eq_of_response_eq P Q k
      (hresponse k.1 (Nat.le_of_lt_succ k.2))
  have hcoupling : P.coupling = Q.coupling := by
    funext k
    exact coupling_eq_of_response_eq P Q k
      (hresponse k.1 (Nat.le_of_lt k.2))
  have hresponses : P.response = Q.response := by
    funext k
    exact hresponse k.1 (Nat.le_of_lt_succ k.2)
  exact ⟨hcenter, hcoupling, hresponses⟩

/-- Combined theorem package: the already-proved reverse continued fraction
and the positive-gauge uniqueness theorem. -/
theorem matrixContinuedFractionAndLayerReconstruction :
    (∀ (Lk Ln C B : Block b) (z : ℂ),
      Invertible B → Invertible Ln →
      Lk = z • (1 : Block b) - C - Bᴴ * Ln⁻¹ * B →
      Ln = -(B * (Lk - z • (1 : Block b) + C)⁻¹ * Bᴴ))
    ∧ (∀ (layers : ℕ)
      (P Q : PositiveGaugeJacobiChain (b := b) layers),
      P.response 0 = Q.response 0 →
      P.center = Q.center ∧ P.coupling = Q.coupling ∧
        P.response = Q.response) := by
  constructor
  · intro Lk Ln C B z hB hLn hrec
    letI : Invertible B := hB
    letI : Invertible Ln := hLn
    exact NCG.layer_stripping Lk Ln C B z hrec
  · exact fun _ P Q => completeResponse_unique_reconstruction P Q

end PositiveGaugeJacobiLayerReconstruction
end NCG
