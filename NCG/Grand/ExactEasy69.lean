/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ExactEasy68
import NCG.Grand.MomentLeakage

/-!
# Exact EASY 69: support unwhitening for moment-exact leakage

On the support of the zeroth moment, its Moore--Penrose inverse square root is
intrinsically characterized by `Rᴴ = R` and `R H0 R = 1`.  These identities
make `W = C R` an isometry and identify its compressed first and second
moments with the manuscript's displayed formulas.  The whitened leakage
factorization then gives the exact norm, rank, and invariance statements.
-/

open Matrix
open scoped ComplexOrder Norms.L2Operator

namespace NCG

noncomputable def momentLeakageNewComponent {h k : Type*}
    [Fintype h] [Fintype k] [DecidableEq h]
    (W : Matrix h k ℂ) (T : Matrix h h ℂ) : Submodule ℂ (h → ℂ) :=
  LinearMap.range (Matrix.mulVecLin ((1 - W * Wᴴ) * T * W))

/-- The range dimension of the head-to-tail map is its matrix rank. -/
lemma finrank_momentLeakageNewComponent {h k : Type*}
    [Fintype h] [Fintype k] [DecidableEq h]
    (W : Matrix h k ℂ) (T : Matrix h h ℂ) :
    Module.finrank ℂ (momentLeakageNewComponent W T)
      = ((1 - W * Wᴴ) * T * W).rank := rfl

/-- Support inverse-square-root whitening, including all three moment
identities used by the manuscript. -/
theorem moment_support_whitening {h k : Type*}
    [Fintype h] [Fintype k] [DecidableEq k]
    (C : Matrix h k ℂ) (R : Matrix k k ℂ) (T : Matrix h h ℂ)
    (hR : Rᴴ = R) (hwhite : R * (Cᴴ * C) * R = 1) :
    let W := C * R
    Wᴴ * W = 1
    ∧ Wᴴ * T * W = R * (Cᴴ * T * C) * R
    ∧ Wᴴ * (T * T) * W = R * (Cᴴ * (T * T) * C) * R := by
  dsimp only
  have hgram : (C * R)ᴴ * (C * R) = R * (Cᴴ * C) * R := by
    rw [Matrix.conjTranspose_mul, hR]
    simp only [Matrix.mul_assoc]
  refine ⟨hgram.trans hwhite, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, hR]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.conjTranspose_mul, hR]
    simp only [Matrix.mul_assoc]

/-- The head-to-tail rank is exactly the dimension gained by adjoining the
next moment columns `T W` to the current isometric head `W`. -/
theorem moment_head_growth_rank {h k : Type*}
    [Fintype h] [Fintype k] [DecidableEq h] [DecidableEq k]
    (W : Matrix h k ℂ) (T : Matrix h h ℂ) (hW : Wᴴ * W = 1) :
    (Matrix.fromCols W (T * W)).rank - W.rank
      = ((1 - W * Wᴴ) * T * W).rank := by
  let P : Matrix h h ℂ := W * Wᴴ
  have hP2 : P * P = P := by
    dsimp [P]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W Wᴴ, hW, Matrix.one_mul]
  have hfix : W.transpose * P.transpose = W.transpose := by
    rw [← Matrix.transpose_mul]
    dsimp [P]
    rw [Matrix.mul_assoc, hW, Matrix.mul_one]
  have hrankP : P.transpose.rank = W.transpose.rank := by
    rw [Matrix.rank_transpose, Matrix.rank_transpose]
    dsimp [P]
    exact Matrix.rank_self_mul_conjTranspose W
  have hstack := stacked_rank_innovation W.transpose (T * W).transpose
    P.transpose (by simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hP2)
    hfix hrankP
  rw [← Matrix.transpose_fromCols] at hstack
  simp only [Matrix.rank_transpose] at hstack
  have hres : ((T * W).transpose * (1 - P.transpose)).transpose
      = (1 - W * Wᴴ) * T * W := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_transpose]
    dsimp [P]
    simp only [Matrix.transpose_transpose, Matrix.mul_assoc]
  let Y : Matrix k h ℂ := (T * W).transpose * (1 - P.transpose)
  have hrtranspose : Y.rank = Y.transpose.rank :=
    (Matrix.rank_transpose Y).symm
  have hrres : Y.transpose.rank = ((1 - W * Wᴴ) * T * W).rank := by
    exact congrArg (fun M : Matrix h k ℂ => M.rank) hres
  exact hstack.trans (hrtranspose.trans hrres)

/-- `thm:universal-moment-leakage`, with the singular support whitening
rendered by its exact inverse-square-root identities. -/
theorem universal_moment_leakage_exact {h k : Type*}
    [Fintype h] [Fintype k] [DecidableEq h] [DecidableEq k]
    (C : Matrix h k ℂ) (R : Matrix k k ℂ) (T : Matrix h h ℂ)
    (hR : Rᴴ = R) (hwhite : R * (Cᴴ * C) * R = 1)
    (hT : Tᴴ = T) :
    let H1 := Cᴴ * T * C
    let H2 := Cᴴ * (T * T) * C
    let W := C * R
    let A := R * H1 * R
    let V := R * H2 * R - A * A
    let X := (1 - W * Wᴴ) * T * W
    V = Xᴴ * X
    ∧ V.PosSemidef
    ∧ ‖V‖ = ‖X‖ ^ 2
    ∧ V.rank = Module.finrank ℂ (momentLeakageNewComponent W T)
    ∧ V.rank = (Matrix.fromCols W (T * W)).rank - W.rank
    ∧ (V = 0 ↔ X = 0) := by
  dsimp only
  let W : Matrix h k ℂ := C * R
  let X : Matrix h k ℂ := (1 - W * Wᴴ) * T * W
  obtain ⟨hW, hM1, hM2⟩ := moment_support_whitening C R T hR hwhite
  have hbase := universal_moment_leakage W T hW hT
  obtain ⟨hfac, hpos, hrank, hzero⟩ := hbase
  have hV : R * (Cᴴ * (T * T) * C) * R
        - (R * (Cᴴ * T * C) * R) * (R * (Cᴴ * T * C) * R)
      = Wᴴ * (T * T) * W - (Wᴴ * T * W) * (Wᴴ * T * W) := by
    rw [hM1, hM2]
  rw [hV]
  change (Wᴴ * (T * T) * W - (Wᴴ * T * W) * (Wᴴ * T * W) = Xᴴ * X)
    ∧ (Wᴴ * (T * T) * W - (Wᴴ * T * W) * (Wᴴ * T * W)).PosSemidef
    ∧ ‖Wᴴ * (T * T) * W - (Wᴴ * T * W) * (Wᴴ * T * W)‖ = ‖X‖ ^ 2
    ∧ (Wᴴ * (T * T) * W - (Wᴴ * T * W) * (Wᴴ * T * W)).rank
        = Module.finrank ℂ (momentLeakageNewComponent W T)
    ∧ (Wᴴ * (T * T) * W - (Wᴴ * T * W) * (Wᴴ * T * W)).rank
        = (Matrix.fromCols W (T * W)).rank - W.rank
    ∧ (Wᴴ * (T * T) * W - (Wᴴ * T * W) * (Wᴴ * T * W) = 0 ↔ X = 0)
  refine ⟨hfac, hpos, ?_, ?_, ?_, hzero⟩
  · rw [hfac, Matrix.l2_opNorm_conjTranspose_mul_self]
    ring
  · rw [finrank_momentLeakageNewComponent, hrank]
  · rw [hrank, moment_head_growth_rank W T hW]

end NCG
