/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.PositiveHeadTailEnclosure
import NCG.Grand.MomentLeakageUnwhitening
import NCG.Grand.GradedWeightedSchurOperator

/-!
# Saturated block-first upper bridge

This module assembles the three exact ingredients of
`thm:GRH-block-first-bridge`:

* a source-saturating family is represented by the statement that its joined
  finite Krylov heads fill the selected carrier;
* the moment-exact leakage Gram of the head-to-tail block `B` is `Bᴴ * B`,
  whose norm is exactly `‖B‖²`;
* the positive head-tail enclosure therefore gives the manuscript's boxed
  bound with `ν = ‖BᴴB‖`, and the strict determinant criterion gives the exact
  upper bridge. The predeclared graded alternative is supplied by the
  operator-level weighted Schur theorem.

The saturation hypothesis selects an exhaustive family of heads. The
head-tail estimate is valid for every individual head, so its proof is
strictly stronger and does not otherwise use exhaustivity.
-/

open Matrix Real
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG

/-- A family of finite source/Krylov heads is source saturating when their
join is the whole selected finite carrier. -/
def SourceSaturating {ι E : Type*} [AddCommMonoid E]
    [Module ℂ E] (K : ι → Submodule ℂ E) : Prop :=
  ⨆ i, K i = ⊤

/-- The moment-exact leakage Gram attached to a head-to-tail block. -/
def momentExactHeadLeakageGram {h t : Type*} [Fintype h]
    (B : Matrix h t ℂ) : Matrix t t ℂ :=
  Bᴴ * B

/-- The norm of the moment-exact leakage Gram is the squared head-to-tail
coupling norm. -/
theorem norm_momentExactHeadLeakageGram {h t : Type*} [Fintype h]
    [Fintype t] [DecidableEq t]
    (B : Matrix h t ℂ) :
    ‖momentExactHeadLeakageGram B‖ = ‖B‖ ^ 2 := by
  rw [momentExactHeadLeakageGram,
    Matrix.l2_opNorm_conjTranspose_mul_self]
  ring

/-- `thm:GRH-block-first-bridge`, exact block-first branch.

The contextual saturation premise is retained explicitly. The two
conclusions are the boxed norm enclosure and, under the sharp determinant
margin, both strict contraction and the Loewner upper bridge `H ≤ I`. -/
theorem saturated_block_first_upper_bridge
    {ι E h t : Type*} [AddCommMonoid E] [Module ℂ E]
    [Fintype h] [Fintype t] [DecidableEq h] [DecidableEq t]
    (K : ι → Submodule ℂ E) (_hsat : SourceSaturating K)
    (A : Matrix h h ℂ) (B : Matrix h t ℂ) (D : Matrix t t ℂ)
    (hH : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    let H := Matrix.fromBlocks A B Bᴴ D
    let nu := ‖momentExactHeadLeakageGram B‖
    ‖H‖ ≤
        (‖A‖ + ‖D‖ + Real.sqrt ((‖A‖ - ‖D‖) ^ 2 + 4 * nu)) / 2
      ∧ (‖A‖ < 1 → ‖D‖ < 1 → nu < (1 - ‖A‖) * (1 - ‖D‖) →
        H ≤ 1 ∧ ‖H‖ < 1) := by
  dsimp only
  let H : Matrix (h ⊕ t) (h ⊕ t) ℂ :=
    Matrix.fromBlocks A B Bᴴ D
  have hnu : ‖momentExactHeadLeakageGram B‖ = ‖B‖ ^ 2 :=
    norm_momentExactHeadLeakageGram B
  have henclosure := sharp_positive_head_tail_opNorm A B D hH
  refine ⟨?_, ?_⟩
  · simpa only [hnu] using henclosure
  · intro hA hD hmargin
    have hlambda :
        (‖A‖ + ‖D‖ + Real.sqrt
          ((‖A‖ - ‖D‖) ^ 2 + 4 * ‖B‖ ^ 2)) / 2 < 1 :=
      (sharp_positive_head_tail.2 ‖A‖ ‖B‖ ‖D‖
        (norm_nonneg B) hA hD).2 (by simpa only [hnu] using hmargin)
    have hstrict : ‖H‖ < 1 := henclosure.trans_lt hlambda
    have hnonneg : (0 : Matrix (h ⊕ t) (h ⊕ t) ℂ) ≤ H := hH.nonneg
    letI : CStarAlgebra (Matrix (h ⊕ t) (h ⊕ t) ℂ) := by
      refine { norm_mul_self_le := fun x =>
        (CStarRing.norm_star_mul_self (x := x)).ge }
    have horder : H ≤
        algebraMap ℝ (Matrix (h ⊕ t) (h ⊕ t) ℂ) 1 :=
      (CStarAlgebra.norm_le_iff_le_algebraMap H zero_le_one
        (ha := hnonneg)).1 hstrict.le
    refine ⟨?_, hstrict⟩
    simpa using horder

/-- `thm:GRH-block-first-bridge`, exact predeclared-grading alternative.
The weighted block criterion controls the operator norm, and at `κ ≤ 1`
it yields the same Loewner upper bridge. -/
theorem saturated_block_first_weighted_bridge
    {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] [Nonempty I] [Nonempty K]
    (H : Matrix (I × K) (I × K) ℂ) (hH : H.PosSemidef)
    (c : I → I → ℝ) (w : I → ℝ) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hc : ∀ i j, 0 ≤ c i j) (hsymm : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hk : ∀ i, ∑ j, c i j * w j ≤ kappa * w i)
    (hblock : ∀ x i j, gradedBlockQuadratic H x i j ≤
      c i j * gradedFiberNorm x i * gradedFiberNorm x j) :
    ‖H‖ ≤ kappa ∧ (kappa ≤ 1 → H ≤ 1) := by
  have hnorm := graded_weighted_schur_operatorNorm H hH c w kappa hkappa
    hc hsymm hw hk hblock
  refine ⟨hnorm, fun hkappaOne => ?_⟩
  have hnonneg : (0 : Matrix (I × K) (I × K) ℂ) ≤ H := hH.nonneg
  letI : CStarAlgebra (Matrix (I × K) (I × K) ℂ) := by
    refine { norm_mul_self_le := fun x =>
      (CStarRing.norm_star_mul_self (x := x)).ge }
  have horder : H ≤
      algebraMap ℝ (Matrix (I × K) (I × K) ℂ) 1 :=
    (CStarAlgebra.norm_le_iff_le_algebraMap H zero_le_one
      (ha := hnonneg)).1 (hnorm.trans hkappaOne)
  simpa using horder

end NCG
