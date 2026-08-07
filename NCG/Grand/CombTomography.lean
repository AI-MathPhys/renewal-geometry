/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectatorProduct
import NCG.Grand.OccurrenceChoiSource

/-!
# Finite process-comb tomography
  (`thm:comb-tomography`, Gran-Tensor manuscript)

* `comb_tomography`:
  (1) frame independence / uniqueness of the Riesz tensor: two
      hermitian tensors giving the same pairing against a
      spanning family of probes are equal (trace separation
      through the matrix units);
  (2) Choi positivity is necessary: the Choi tensor of a
      Kraus-form process is the positive dyad sum (from the
      proved occurrence Choi source);
  (3) the boxed recursive trace identity is necessary: for a
      trace-preserving Kraus family, the partial trace of the
      Choi dyad sum over the output leg is the identity
      (`Tr₂ J = (ΣV_αᴴV_α)ᵀ = I`).

Rendering disclosed: sufficiency (linking minimal purifications
of the positive prefixes into a sequential process) is the
canonical comb dilation record; the probability table and its
multilinear pairing are the declared tomographic inputs.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:comb-tomography`. -/
theorem comb_tomography {m : Type*} [Fintype m] :
    -- (1) frame-independent uniqueness by trace separation
    (∀ R R' : Matrix m m ℂ,
      (∀ M : Matrix m m ℂ, (R * M).trace = (R' * M).trace) →
      R = R')
    -- (2) Choi positivity of Kraus processes: dyad sum
    ∧ (∀ {ι : Type} [Fintype ι] (V : ι → Matrix m m ℂ),
        (∑ α, Matrix.vecMulVec
            (fun p : m × m => V α p.2 p.1)
            (star fun p : m × m => V α p.2 p.1)).PosSemidef)
    -- (3) the boxed causal trace recursion is necessary
    ∧ (∀ {ι : Type} [Fintype ι] (V : ι → Matrix m m ℂ),
        partialTraceRight (dA := m) (dK := m)
            (∑ α, Matrix.vecMulVec
              (fun p : m × m => V α p.2 p.1)
              (star fun p : m × m => V α p.2 p.1))
          = (∑ α, (V α)ᴴ * V α)ᵀ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro R R' hpair
    classical
    ext i j
    have hRs : ∀ S : Matrix m m ℂ,
        (S * Matrix.single j i (1 : ℂ)).trace = S i j := by
      intro S
      rw [Matrix.trace]
      simp only [Matrix.diag_apply, Matrix.mul_apply,
        Matrix.single_apply]
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · rw [if_pos ⟨rfl, rfl⟩, mul_one]
        · intro b _ hb
          rw [if_neg (fun hand => hb hand.1.symm), mul_zero]
        · intro hb
          exact absurd (Finset.mem_univ _) hb
      · intro a _ ha
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [if_neg (fun hand => ha hand.2.symm), mul_zero]
      · intro ha
        exact absurd (Finset.mem_univ _) ha
    have h := hpair (Matrix.single j i (1 : ℂ))
    rw [hRs R, hRs R'] at h
    exact h
  · intro ι _ V
    exact Finset.sum_induction _ _
      (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero
      (fun α _ => Matrix.posSemidef_vecMulVec_self_star _)
  · intro ι _ V
    ext a c
    simp only [partialTraceRight, Matrix.of_apply,
      Matrix.sum_apply, Matrix.vecMulVec_apply,
      Pi.star_apply, Matrix.transpose_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end NCG
