import NCG.Grand.GrandScoreBus

/-!
# Exact EASY batch 27: typed-route source rank

`route_amplitude` already proves the route effect and nonvanishing.  Here the
rank-one source of the bridge is made explicit, closing the remaining source
rank clause of `cor:SM-route-amplitude`.
-/

open Matrix Kronecker ComplexOrder

namespace NCG

private lemma rank_smul_one_of_ne_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] (c : ℂ) (hc : c ≠ 0) :
    Matrix.rank (c • (1 : Matrix ι ι ℂ)) = Fintype.card ι := by
  apply le_antisymm (Matrix.rank_le_card_width _) ?_
  have h := Matrix.rank_mul_le_right
    (c⁻¹ • (1 : Matrix ι ι ℂ)) (c • (1 : Matrix ι ι ℂ))
  have hprod : (c⁻¹ • (1 : Matrix ι ι ℂ)) * (c • 1) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    simp [hc]
  rw [hprod, Matrix.rank_one] at h
  exact h

/-- `cor:SM-route-amplitude`, including the residual source-rank clause.
The bridge source is a single line (`Unique b'`), so tensoring the carrier row
with the normalized nonzero bridge preserves its source rank. -/
theorem route_amplitude_exact {q y b b' : Type*}
    [Fintype q] [Fintype y] [Fintype b] [Fintype b']
    [DecidableEq q] [DecidableEq b'] [Nonempty q] [Unique b']
    (C : Matrix y q ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (hC : Cᴴ * C = κ • 1)
    (B : Matrix b b' ℂ) (hB : Bᴴ * B = (1 / 2 : ℂ) • 1) :
    ((C ⊗ₖ B)ᴴ * (C ⊗ₖ B)
        = (κ / 2) • (1 : Matrix (q × b') (q × b') ℂ))
      ∧ C ⊗ₖ B ≠ 0
      ∧ Matrix.rank (C ⊗ₖ B) = Matrix.rank C := by
  have hr := route_amplitude C κ hC B hB
  have hk2 : κ / 2 ≠ 0 := div_ne_zero hκ (by norm_num)
  refine ⟨hr.1, hr.2 hκ inferInstance, ?_⟩
  calc
    Matrix.rank (C ⊗ₖ B)
        = Matrix.rank ((C ⊗ₖ B)ᴴ * (C ⊗ₖ B)) :=
          (Matrix.rank_conjTranspose_mul_self _).symm
    _ = Matrix.rank ((κ / 2) •
          (1 : Matrix (q × b') (q × b') ℂ)) := by rw [hr.1]
    _ = Fintype.card (q × b') := rank_smul_one_of_ne_zero _ hk2
    _ = Fintype.card q := by simp [Fintype.card_prod]
    _ = Matrix.rank (κ • (1 : Matrix q q ℂ)) :=
          (rank_smul_one_of_ne_zero κ hκ).symm
    _ = Matrix.rank (Cᴴ * C) := by rw [hC]
    _ = Matrix.rank C := Matrix.rank_conjTranspose_mul_self C

end NCG
