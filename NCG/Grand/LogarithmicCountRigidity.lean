import NCG.Grand.PeanoLadder

/-!
# logarithmic count rigidity

The count covariance formulas were already proved in `PeanoLadder`.  This file
adds the manuscript's remaining uniqueness assertion for the logarithmic
grading.
-/

namespace NCG

/-- A Peano history sends the anchor to its numbered endpoint. -/
lemma peanoL_anchor_endpoint {X n : ℕ} (hn : 1 ≤ n) (hnX : n ≤ X) :
    Matrix.mulVec (peanoL X n) (Pi.single (⟨0, by omega⟩ : Fin X) 1)
      = Pi.single (⟨n - 1, by omega⟩ : Fin X) 1 := by
  funext j
  rw [mulVec_single_col, peanoL, Matrix.of_apply, Pi.single_apply]
  by_cases hj : j = (⟨n - 1, by omega⟩ : Fin X)
  · rw [if_pos hj]
    rw [if_pos]
    simpa [hj] using (show n - 1 + 1 = n by omega)
  · rw [if_neg hj]
    rw [if_neg]
    intro heq
    apply hj
    apply Fin.ext
    simp only
    simp at heq
    omega

/-- `thm:ar-count-rigidity`, final clause: the logarithmic count is the
unique operator killing the anchor and satisfying the Peano commutator laws. -/
theorem log_count_rigidity {X : ℕ} (hX : 0 < X)
    (K : Matrix (Fin X) (Fin X) ℂ)
    (hanchor : Matrix.mulVec K (Pi.single (⟨0, hX⟩ : Fin X) 1) = 0)
    (hcomm : ∀ a : ℕ, 1 ≤ a → a ≤ X →
      K * peanoL X a - peanoL X a * K
        = (Real.log a : ℂ) • peanoL X a) :
    K = Matrix.diagonal
      (fun i : Fin X => (Real.log ((i : ℕ) + 1) : ℂ)) := by
  have hcols : ∀ i : Fin X,
      Matrix.mulVec K (Pi.single i 1)
        = (Real.log ((i : ℕ) + 1) : ℂ) • Pi.single i 1 := by
    intro i
    let a : ℕ := (i : ℕ) + 1
    have ha : 1 ≤ a := by omega
    have haX : a ≤ X := by dsimp [a]; omega
    have hact : Matrix.mulVec (peanoL X a) (Pi.single (⟨0, hX⟩ : Fin X) 1)
        = Pi.single i 1 := by
      have hp := peanoL_anchor_endpoint ha haX
      simpa [a, Fin.ext_iff] using hp
    have hc := congrArg
      (fun M : Matrix (Fin X) (Fin X) ℂ =>
        Matrix.mulVec M (Pi.single (⟨0, hX⟩ : Fin X) 1))
      (hcomm a ha haX)
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hact, hanchor, Matrix.mulVec_zero,
      sub_zero, Matrix.smul_mulVec, hact] at hc
    simpa [a] using hc
  ext j i
  have hc := congrFun (hcols i) j
  rw [mulVec_single_col, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul] at hc
  rw [Matrix.diagonal_apply]
  by_cases hji : j = i
  · simpa [hji] using hc
  · simpa [hji] using hc

end NCG
