import NCG.Grand.GrandTransparentBridge

/-!
# Exact EASY batch 28: full bridge transparency

The existing all-depth moment factorization is supplemented by the rank,
flatness, and equality/residual invariances obtained after the manuscript's
one-dimensional normalized bridge source is made explicit.
-/

open Matrix Kronecker

namespace NCG

private lemma rank_kronecker_one_unique {p u : Type*}
    [Fintype p] [Fintype u] [DecidableEq p] [DecidableEq u] [Unique u]
    (M : Matrix p p ℂ) :
    Matrix.rank (M ⊗ₖ (1 : Matrix u u ℂ)) = Matrix.rank M := by
  let e : p × u ≃ p := Equiv.prodUnique p u
  have hreindex :
      (M ⊗ₖ (1 : Matrix u u ℂ)).reindex e e = M := by
    ext i j
    simp [e, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Equiv.prodUnique_symm_apply]
  calc
    Matrix.rank (M ⊗ₖ (1 : Matrix u u ℂ))
        = Matrix.rank ((M ⊗ₖ (1 : Matrix u u ℂ)).reindex e e) :=
          (Matrix.rank_reindex e e _).symm
    _ = Matrix.rank M := by rw [hreindex]

private lemma kronecker_one_injective {p u : Type*}
    [Fintype u] [DecidableEq u] [Unique u]
    (A C : Matrix p p ℂ) :
    A ⊗ₖ (1 : Matrix u u ℂ) = C ⊗ₖ (1 : Matrix u u ℂ) ↔ A = C := by
  constructor
  · intro h
    ext i j
    have hij := congrArg
      (fun M : Matrix (p × u) (p × u) ℂ =>
        M (i, default) (j, default)) h
    simpa [Matrix.kroneckerMap_apply] using hij
  · exact fun h => congrArg (fun M => M ⊗ₖ (1 : Matrix u u ℂ)) h

/-- `cor:SM-K4-transparent`, exact bundle.  All normalized moments factor,
their ranks and rank-saturation tests are unchanged, and every equality-valued
transfer residual or source-whitened cycle comparison is reflected as well as
preserved by the bridge. -/
theorem k4_transparent_exact {n p g u : Type*}
    [Fintype n] [Fintype p] [Fintype g] [Fintype u]
    [DecidableEq n] [DecidableEq p] [DecidableEq g] [DecidableEq u]
    [Unique u]
    (T : Matrix n n ℂ) (S : Matrix n p ℂ)
    (B : Matrix g u ℂ) (hB : Bᴴ * B = 1) :
    (∀ k : ℕ,
      (S ⊗ₖ B)ᴴ * ((T ⊗ₖ (1 : Matrix g g ℂ)) ^ k) * (S ⊗ₖ B)
        = (Sᴴ * T ^ k * S) ⊗ₖ (1 : Matrix u u ℂ))
    ∧ (∀ k : ℕ,
      Matrix.rank ((S ⊗ₖ B)ᴴ
          * ((T ⊗ₖ (1 : Matrix g g ℂ)) ^ k) * (S ⊗ₖ B))
        = Matrix.rank (Sᴴ * T ^ k * S))
    ∧ (∀ k l : ℕ,
      (Matrix.rank ((S ⊗ₖ B)ᴴ
          * ((T ⊗ₖ (1 : Matrix g g ℂ)) ^ k) * (S ⊗ₖ B))
        = Matrix.rank ((S ⊗ₖ B)ᴴ
          * ((T ⊗ₖ (1 : Matrix g g ℂ)) ^ l) * (S ⊗ₖ B)))
      ↔ Matrix.rank (Sᴴ * T ^ k * S) = Matrix.rank (Sᴴ * T ^ l * S))
    ∧ (∀ A C : Matrix p p ℂ,
      A ⊗ₖ (1 : Matrix u u ℂ) = C ⊗ₖ (1 : Matrix u u ℂ) ↔ A = C) := by
  have hm : ∀ k : ℕ,
      (S ⊗ₖ B)ᴴ * ((T ⊗ₖ (1 : Matrix g g ℂ)) ^ k) * (S ⊗ₖ B)
        = (Sᴴ * T ^ k * S) ⊗ₖ (1 : Matrix u u ℂ) :=
    fun k => k4_transparent T S B hB k
  refine ⟨hm, ?_, ?_, kronecker_one_injective⟩
  · intro k
    rw [hm k]
    exact rank_kronecker_one_unique _
  · intro k l
    rw [hm k, hm l, rank_kronecker_one_unique,
      rank_kronecker_one_unique]

end NCG
