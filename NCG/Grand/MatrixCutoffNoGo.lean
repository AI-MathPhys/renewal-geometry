/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.SkolemNoether
import NCG.Algebra.MarkedFactor

/-!
# No unital matrix cutoff
  (`cth:ar-no-unital-matrix-cutoff`, Gran-Tensor manuscript)

* `no_unital_matrix_cutoff`: for `X, Y ≥ 2` a unital
  `*`-homomorphism `M_X(ℂ) → M_Y(ℂ)` exists **iff** `X ∣ Y` —
  the diagonal matrix units map to idempotents with one common
  natural trace summing to `Y`, so ordinary cutoff inclusions
  `X ≤ Y` cannot in general be represented by unital
  `*`-homomorphisms of the full matrix closures.  The forward
  projective algebra and absorbing-corner rule are
  mathematically necessary, not an ad hoc weakening.

Rendering disclosed: the constructed embedding for `X ∣ Y` is
the block embedding `g ↦ g ⊗ 1_k` transported along
`Fin X × Fin k ≃ Fin (X·k)`.
-/

open Matrix Kronecker

set_option linter.style.show false

namespace NCG

/-- `cth:ar-no-unital-matrix-cutoff`: unital `*`-homomorphisms
of full matrix algebras exist exactly for divisible sizes. -/
theorem no_unital_matrix_cutoff (X Y : ℕ) (hX : 2 ≤ X)
    (hY : 2 ≤ Y) :
    (∃ φ : Matrix (Fin X) (Fin X) ℂ
        →ₐ[ℂ] Matrix (Fin Y) (Fin Y) ℂ,
      ∀ M, φ Mᴴ = (φ M)ᴴ) ↔ X ∣ Y := by
  constructor
  · rintro ⟨φ, -⟩
    have hXpos : 0 < X := by omega
    have hPidem : ∀ i : Fin X,
        φ (Matrix.single i i 1) * φ (Matrix.single i i 1)
          = φ (Matrix.single i i 1) := by
      intro i
      rw [← map_mul, Matrix.single_mul_single_same, one_mul]
    have htreq : ∀ i : Fin X,
        (φ (Matrix.single i i 1)).trace
          = (φ (Matrix.single (⟨0, hXpos⟩ : Fin X)
              (⟨0, hXpos⟩ : Fin X) 1)).trace := by
      intro i
      have hsplit : Matrix.single i i (1 : ℂ)
          = Matrix.single i (⟨0, hXpos⟩ : Fin X) 1
            * Matrix.single (⟨0, hXpos⟩ : Fin X) i 1 := by
        rw [Matrix.single_mul_single_same, one_mul]
      have hsplit0 : Matrix.single (⟨0, hXpos⟩ : Fin X)
            (⟨0, hXpos⟩ : Fin X) (1 : ℂ)
          = Matrix.single (⟨0, hXpos⟩ : Fin X) i 1
            * Matrix.single i (⟨0, hXpos⟩ : Fin X) 1 := by
        rw [Matrix.single_mul_single_same, one_mul]
      rw [hsplit, hsplit0, map_mul, map_mul,
        Matrix.trace_mul_comm]
    have hsum : (∑ i : Fin X,
        (φ (Matrix.single i i 1)).trace) = (Y : ℂ) := by
      rw [← Matrix.trace_sum, ← map_sum,
        sum_single_diag_eq_one, map_one, Matrix.trace_one]
      simp
    have hXt : (X : ℂ)
        * (φ (Matrix.single (⟨0, hXpos⟩ : Fin X)
            (⟨0, hXpos⟩ : Fin X) 1)).trace = (Y : ℂ) := by
      rw [← hsum,
        Finset.sum_congr rfl (fun i _ => htreq i),
        Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [trace_isIdempotentElem
      (hPidem (⟨0, hXpos⟩ : Fin X))] at hXt
    refine ⟨Module.finrank ℂ (LinearMap.range (Matrix.toLin'
      (φ (Matrix.single (⟨0, hXpos⟩ : Fin X)
        (⟨0, hXpos⟩ : Fin X) 1)))), ?_⟩
    exact_mod_cast hXt.symm
  · rintro ⟨k, rfl⟩
    refine ⟨((Matrix.reindexAlgEquiv ℂ ℂ
        finProdFinEquiv).toAlgHom).comp
      CommonOrigin.leftKron, ?_⟩
    intro M
    show (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv)
        (CommonOrigin.leftKron Mᴴ)
      = ((Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv)
        (CommonOrigin.leftKron M))ᴴ
    rw [CommonOrigin.leftKron_apply, CommonOrigin.leftKron_apply]
    rw [show Mᴴ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)
        = (M ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ))ᴴ from by
      rw [Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one]]
    simp only [Matrix.coe_reindexAlgEquiv]
    rw [Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix]

end NCG
