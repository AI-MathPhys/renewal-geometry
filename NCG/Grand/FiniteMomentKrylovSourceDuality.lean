/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PointedTetrahedralSourceIsometryAndKrylovUniqueness
import NCG.Matter.K4Carrier

/-!
# Finite-moment Krylov source duality

This file proves the finite-panel refinement in `thm:cycle-flavour`.  For a
Krylov horizon `d = r + 1`, moments only through order `2d - 1 = 2r + 1`
construct the unique source-fixing unitary intertwiner.  The earlier
all-moment theorem used the Gram at horizon `d + 1`; here that step is replaced
by the fact that a square isometry is automatically unitary, eliminating the
unneeded order-`2d` moment.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Finite-panel source duality.  Equality of moments through `2d - 1`, where
`d` is a source-minimal Krylov horizon, determines a unique source-fixing
unitary intertwiner. -/
theorem finiteMoment_sourceFixingIntertwiner_existsUnique
    {u p : Type*} [Fintype u] [Fintype p]
    [DecidableEq u]
    (G G' : Matrix u u ℂ) (B B' : Matrix u p ℂ)
    (hG : Gᴴ = G) (hG' : G'ᴴ = G')
    (d : ℕ) (hd : 0 < d)
    (hmin : Function.Surjective (krylovMat G B d).mulVec)
    (hmom : ∀ n : ℕ, n ≤ 2 * d - 1 →
      Bᴴ * G ^ n * B = B'ᴴ * G' ^ n * B') :
    ∃! W : Matrix u u ℂ,
      Wᴴ * W = 1 ∧ W * B = B' ∧ W * G = G' * W := by
  classical
  set K := krylovMat G B d with hK
  set K' := krylovMat G' B' d with hK'
  set Kb := krylovMat G B (d + 1) with hKb
  set Kb' := krylovMat G' B' (d + 1) with hKb'
  have hgram : Kᴴ * K = K'ᴴ * K' := by
    ext mq nr
    rw [hK, hK', block_hankel_gram G B hG,
      block_hankel_gram G' B' hG']
    apply congrFun (congrFun (hmom ((mq.1 : ℕ) + (nr.1 : ℕ)) ?_)
      mq.2) nr.2
    have hmq := mq.1.isLt
    have hnr := nr.1.isLt
    omega
  have hgram2 : Kᴴ * Kb = K'ᴴ * Kb' := by
    ext mq nr
    rw [hK, hKb, hK', hKb', block_hankel_gram G B hG,
      block_hankel_gram G' B' hG']
    apply congrFun (congrFun (hmom ((mq.1 : ℕ) + (nr.1 : ℕ)) ?_)
      mq.2) nr.2
    have hmq := mq.1.isLt
    have hnr := nr.1.isLt
    omega
  have hPD : (K * Kᴴ).PosDef :=
    ((hodge_cycle_observability K).2.1).mp hmin
  have hdet : IsUnit (K * Kᴴ).det :=
    isUnit_iff_ne_zero.mpr hPD.det_pos.ne'
  have hHerm : (K * Kᴴ)⁻¹ᴴ = (K * Kᴴ)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  set W : Matrix u u ℂ := K' * Kᴴ * (K * Kᴴ)⁻¹ with hW
  set P : Matrix (Fin d × p) (Fin d × p) ℂ :=
    Kᴴ * (K * Kᴴ)⁻¹ * K with hP
  have hKP : K * P = K := by
    rw [hP, show K * (Kᴴ * (K * Kᴴ)⁻¹ * K)
        = (K * Kᴴ) * (K * Kᴴ)⁻¹ * K from by
          simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  have hKP' : K' * P = K' := by
    have hzero : (K' * (1 - P))ᴴ * (K' * (1 - P)) = 0 := by
      rw [Matrix.conjTranspose_mul,
        show (1 - P)ᴴ * K'ᴴ * (K' * (1 - P))
          = (1 - P)ᴴ * (K'ᴴ * K') * (1 - P) from by
            simp only [Matrix.mul_assoc], ← hgram]
      rw [show (1 - P)ᴴ * (Kᴴ * K) * (1 - P)
          = (K * (1 - P))ᴴ * (K * (1 - P)) from by
            rw [Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]]
      rw [Matrix.mul_sub, Matrix.mul_one, hKP, sub_self,
        Matrix.conjTranspose_zero, Matrix.mul_zero]
    have h0 := Matrix.conjTranspose_mul_self_eq_zero.mp hzero
    rw [Matrix.mul_sub, Matrix.mul_one] at h0
    exact (sub_eq_zero.mp h0).symm
  have hWu : Wᴴ * W = 1 := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hHerm, Matrix.conjTranspose_conjTranspose]
    rw [show (K * Kᴴ)⁻¹ * (K * K'ᴴ) *
          (K' * Kᴴ * (K * Kᴴ)⁻¹)
        = (K * Kᴴ)⁻¹ * (K * (K'ᴴ * K') * Kᴴ) *
          (K * Kᴴ)⁻¹ from by simp only [Matrix.mul_assoc], ← hgram]
    rw [show (K * Kᴴ)⁻¹ * (K * (Kᴴ * K) * Kᴴ) *
          (K * Kᴴ)⁻¹
        = ((K * Kᴴ)⁻¹ * (K * Kᴴ)) *
          ((K * Kᴴ) * (K * Kᴴ)⁻¹) from by
            simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul _ hdet,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  have hWW : W * Wᴴ = 1 := by
    exact mul_eq_one_comm.mp hWu
  have hWK : W * K = K' := by
    rw [hW, show K' * Kᴴ * (K * Kᴴ)⁻¹ * K = K' * P from by
      rw [hP]
      simp only [Matrix.mul_assoc], hKP']
  have hWB : W * B = B' := by
    have hEB := krylov_zero_block G B d hd
    have hEB' := krylov_zero_block G' B' d hd
    rw [← hEB, ← hEB', ← Matrix.mul_assoc, hWK]
  have hWHKb : Wᴴ * Kb' = Kb := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hHerm, Matrix.conjTranspose_conjTranspose]
    rw [show (K * Kᴴ)⁻¹ * (K * K'ᴴ) * Kb'
        = (K * Kᴴ)⁻¹ * (K * (K'ᴴ * Kb')) from by
          simp only [Matrix.mul_assoc], ← hgram2,
      show (K * Kᴴ)⁻¹ * (K * (Kᴴ * Kb))
        = ((K * Kᴴ)⁻¹ * (K * Kᴴ)) * Kb from by
          simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have hWKb : W * Kb = Kb' := by
    calc
      W * Kb = W * (Wᴴ * Kb') := by rw [hWHKb]
      _ = (W * Wᴴ) * Kb' := (Matrix.mul_assoc W Wᴴ Kb').symm
      _ = Kb' := by rw [hWW, Matrix.one_mul]
  have hshiftK := krylov_shift G B d
  have hshiftK' := krylov_shift G' B' d
  have hint : (W * G - G' * W) * K = 0 := by
    rw [Matrix.sub_mul]
    rw [show W * G * K = W * (G * K) from Matrix.mul_assoc _ _ _,
      hshiftK, ← Matrix.mul_assoc, hWKb]
    rw [show G' * W * K = G' * (W * K) from Matrix.mul_assoc _ _ _,
      hWK, hshiftK', sub_self]
  have hfinal : W * G - G' * W = 0 := by
    have h1 : (W * G - G' * W) * K * Kᴴ * (K * Kᴴ)⁻¹ = 0 := by
      rw [hint, Matrix.zero_mul, Matrix.zero_mul]
    rw [show (W * G - G' * W) * K * Kᴴ * (K * Kᴴ)⁻¹
        = (W * G - G' * W) * ((K * Kᴴ) * (K * Kᴴ)⁻¹) from by
          simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one] at h1
    exact h1
  refine ⟨W, ⟨hWu, hWB, sub_eq_zero.mp hfinal⟩, ?_⟩
  intro V hV
  exact source_fixing_intertwiner_unique G G' B B' d hmin
    V W hV.2.1 hWB hV.2.2 (sub_eq_zero.mp hfinal)

/-- Manuscript indexing: a packet stabilized at depth `r` uses the horizon
`d = r + 1`, so moments through `2r + 1` suffice. -/
theorem cycleFlavour_finiteMoment_sourceDuality
    {u p : Type*} [Fintype u] [Fintype p]
    [DecidableEq u]
    (Tflav Tcyc : Matrix u u ℂ) (Sflav Scyc : Matrix u p ℂ)
    (hTflav : Tflavᴴ = Tflav) (hTcyc : Tcycᴴ = Tcyc)
    (r : ℕ)
    (hminimal : Function.Surjective
      (krylovMat Tflav Sflav (r + 1)).mulVec)
    (hmom : ∀ n : ℕ, n ≤ 2 * r + 1 →
      Sflavᴴ * Tflav ^ n * Sflav =
        Scycᴴ * Tcyc ^ n * Scyc) :
    ∃! U : Matrix u u ℂ,
      Uᴴ * U = 1 ∧ U * Sflav = Scyc ∧ U * Tflav = Tcyc * U := by
  apply finiteMoment_sourceFixingIntertwiner_existsUnique
    Tflav Tcyc Sflav Scyc hTflav hTcyc (r + 1) (by omega)
    hminimal
  intro n hn
  apply hmom n
  omega

/-- The concrete `K₄` cycle carrier has the three-dimensional conclusion used
in the final clause of `thm:cycle-flavour`. -/
theorem cycleFlavour_K4_cycleDimension :
    Module.finrank ℂ K4Carrier = 3 := finrank_K4Carrier

end NCG
