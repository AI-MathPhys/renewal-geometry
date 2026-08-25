/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.ThreeCylinderActionResponseExact

/-!
# Cutoff transport of the three-cylinder action-response alternative

Machinery for `cor:SMST-three-cylinder-action-response` (AR.17 and the T1/T2
alternative): the record-local content on top of the proved anchors
`thm:GT-reflected-endpoint-action` and `thm:GT-three-cylinder-action-response`.

* `residual_eq_zero_iff` (AR.17): the Hilbert–Schmidt residual
  `Δ = ‖G − Y^*(I−T)Y‖²_HS` vanishes exactly when the reconstructed common
  action `G` coincides with the reflected mean transfer action `Y^*(I−T)Y`;
* `rank_conj` / `posSemidef_transport`: conjugation by an invertible cutoff
  intertwiner preserves rank and positivity;
* `moment_transport`: an exact transport `S ↦ S·V` of the writer bank
  conjugates the three moment matrices, `Mₙ ↦ V^* Mₙ V`;
* `blockGram_transport`: the block moment Gram is conjugated by the
  block-diagonal intertwiner `V ⊕ V`;
* `innovationRank_transport`: the innovation rank is preserved — via the
  proved rank identity (AR.15) `rank 𝔹 − rank M₀ = rank 𝕀`, with no
  pseudoinverse computations;
* `innovation_zero_transport`: the reducing-head alternative (T1 vs. T2) is
  preserved by the transport;
* `smst_three_cylinder_action_response`: the record-level bundle.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace ThreeCylinderTransport

open ThreeCylinderActionResponse

variable {h d : ℕ}

/-! ### AR.17: the Hilbert–Schmidt identification residual -/

/-- The squared Hilbert–Schmidt residual `Δ = ‖G − Y^*(I−T)Y‖²_HS` (AR.17)
between the reconstructed common action and the reflected mean transfer
action. -/
noncomputable def residual (G : Matrix (Fin d) (Fin d) ℂ)
    (Y : Matrix (Fin h) (Fin d) ℂ) (T : Matrix (Fin h) (Fin h) ℂ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    Complex.normSq ((G - Yᴴ * ((1 : Matrix (Fin h) (Fin h) ℂ) - T) * Y) i j)

theorem residual_nonneg (G : Matrix (Fin d) (Fin d) ℂ)
    (Y : Matrix (Fin h) (Fin d) ℂ) (T : Matrix (Fin h) (Fin h) ℂ) :
    0 ≤ residual G Y T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- **(AR.17)**: the residual vanishes exactly when the reconstructed common
action is the reflected mean transfer action. -/
theorem residual_eq_zero_iff (G : Matrix (Fin d) (Fin d) ℂ)
    (Y : Matrix (Fin h) (Fin d) ℂ) (T : Matrix (Fin h) (Fin h) ℂ) :
    residual G Y T = 0 ↔ G = Yᴴ * ((1 : Matrix (Fin h) (Fin h) ℂ) - T) * Y := by
  constructor
  · intro hz
    unfold residual at hz
    have hz1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => Finset.sum_nonneg
        fun j _ => Complex.normSq_nonneg _)).mp hz
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => Complex.normSq_nonneg _)).mp
      (hz1 i (Finset.mem_univ i)) j (Finset.mem_univ j)
    have h2 := Complex.normSq_eq_zero.mp h1
    rw [Matrix.sub_apply] at h2
    exact sub_eq_zero.mp h2
  · intro hG
    unfold residual
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [hG]
    simp

/-! ### Conjugation invariance of rank, positivity, and vanishing -/

/-- Rank is invariant under conjugation by an invertible intertwiner. -/
theorem rank_conj {n : Type*} [Fintype n] [DecidableEq n]
    (V A : Matrix n n ℂ) (hV : IsUnit V.det) :
    (Vᴴ * A * V).rank = A.rank := by
  have hVH : IsUnit (Vᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr hV
  rw [Matrix.rank_mul_eq_left_of_isUnit_det V (Vᴴ * A) hV,
    Matrix.rank_mul_eq_right_of_isUnit_det (Vᴴ) A hVH]

/-- A matrix over `ℂ` has rank zero exactly when it vanishes. -/
theorem rank_eq_zero_iff {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : A.rank = 0 ↔ A = 0 := by
  classical
  constructor
  · intro hr
    have hbot : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hr
    have hf : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hbot
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [← Matrix.mulVecLin_apply, hf, Matrix.zero_mulVec]
    simp
  · rintro rfl
    exact Matrix.rank_zero

/-- Positivity is preserved by conjugation. -/
theorem posSemidef_transport {n : Type*} [Fintype n]
    (V : Matrix n n ℂ) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (Vᴴ * A * V).PosSemidef := by
  have h1 := hA.mul_mul_conjTranspose_same (Vᴴ)
  rwa [Matrix.conjTranspose_conjTranspose] at h1

/-! ### Transport of the three moment matrices and the block Gram -/

variable (V : Matrix (Fin d) (Fin d) ℂ)

/-- Exact cutoff transport of the writer bank conjugates every moment matrix:
`Mₙ(S·V) = V^* Mₙ(S) V`. -/
theorem moment_transport (S : Matrix (Fin h) (Fin d) ℂ)
    (P : Matrix (Fin h) (Fin h) ℂ) (n : ℕ) :
    moment (S * V) P n = Vᴴ * moment S P n * V := by
  unfold moment
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The block-diagonal cutoff intertwiner acting on the two-cylinder
coefficient space. -/
def blockV : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  Matrix.fromBlocks V 0 0 V

theorem blockV_det_isUnit (hV : IsUnit V.det) : IsUnit (blockV V).det := by
  rw [blockV, Matrix.det_fromBlocks_zero₂₁]
  exact hV.mul hV

/-- The block moment Gram (AR.15) is conjugated by the block-diagonal
intertwiner `V ⊕ V` under the cutoff transport. -/
theorem blockGram_transport (S : Matrix (Fin h) (Fin d) ℂ)
    (P : Matrix (Fin h) (Fin h) ℂ) :
    blockGram (S * V) P = (blockV V)ᴴ * blockGram S P * blockV V := by
  simp only [blockGram, blockV, moment_transport,
    Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]

/-! ### Transport of the innovation rank and the reducing-head alternative -/

/-- **Transport of the innovation rank**: the exact cutoff transport preserves
the rank of the first temporal-memory innovation, via the proved rank identity
(AR.15) — no pseudoinverse computations required. -/
theorem innovationRank_transport (S : Matrix (Fin h) (Fin d) ℂ)
    (P : Matrix (Fin h) (Fin h) ℂ) (hP : P.IsHermitian) (hV : IsUnit V.det) :
    (innovation (S * V) P).rank = (innovation S P).rank := by
  rw [← blockGram_rank (S * V) P hP, blockGram_transport V S P,
    moment_transport V S P 0, rank_conj (blockV V) _ (blockV_det_isUnit V hV),
    rank_conj V _ hV, blockGram_rank S P hP]

/-- **Transport of the reducing-head alternative**: which branch of the T1/T2
alternative holds is invariant under the exact cutoff transport. -/
theorem innovation_zero_transport (S : Matrix (Fin h) (Fin d) ℂ)
    (P : Matrix (Fin h) (Fin h) ℂ) (hP : P.IsHermitian) (hV : IsUnit V.det) :
    innovation (S * V) P = 0 ↔ innovation S P = 0 := by
  rw [← rank_eq_zero_iff, ← rank_eq_zero_iff,
    innovationRank_transport V S P hP hV]

/-! ### The record-level bundle -/

/-- **The three-cylinder action-response corollary**: on the accepted branch,
(i) the residual (AR.17) vanishes exactly when the reconstructed common action
is the reflected mean transfer action; (ii) the first temporal closure is the
exact alternative T1/T2; (iii) on the T1 branch the joint action-response head
reduces the accepted transfer; and (iv) the exact cutoff transport preserves
the innovation rank and the branch of the alternative, so temporal
common-action completeness is a finite population problem. -/
theorem smst_three_cylinder_action_response
    (G : Matrix (Fin d) (Fin d) ℂ) (Y S : Matrix (Fin h) (Fin d) ℂ)
    (T P : Matrix (Fin h) (Fin h) ℂ) (hP : P.IsHermitian) (hV : IsUnit V.det) :
    (residual G Y T = 0 ↔ G = Yᴴ * ((1 : Matrix (Fin h) (Fin h) ℂ) - T) * Y) ∧
      (innovation S P = 0 ∨ innovation S P ≠ 0) ∧
      (innovation S P = 0 → rangeProj S * P = P * rangeProj S) ∧
      (innovation (S * V) P).rank = (innovation S P).rank ∧
      (innovation (S * V) P = 0 ↔ innovation S P = 0) := by
  refine ⟨residual_eq_zero_iff G Y T, em _, fun hz => ?_,
    innovationRank_transport V S P hP hV,
    innovation_zero_transport V S P hP hV⟩
  obtain ⟨h1, h2⟩ := innovation_eq_zero_iff S P hP
  exact h2.mp (h1.mp hz)

end ThreeCylinderTransport
end NCG
