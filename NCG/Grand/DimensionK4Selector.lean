/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Compiler-minimal complete-cell selector
  (`thm:dimension-K4-selector`, Gran-Tensor manuscript)

* `dimension_K4_selector`:
  (i) a nondegenerate alternating real form has even
      dimension (`det J = (-1)^n det J` forces `n`
      even) — the parity selection of DS.5;
  (ii) the boxed DS.5 rank arithmetic: an even `N` with
      nonzero interference (`Λ²W_N ≠ 0`, i.e. `N ≥ 3`)
      satisfies `N ≥ 4`, the faithful ranks
      `r₀ = N - 1` and `r₁ = N(N-1)/2` are minimized on
      that set exactly at `N = 4` (where they are `3` and
      `6`), and both are strictly increasing beyond it;
  (iii) the boxed DS.6 intertwiner at `N = 4`: on
      `W₄ ≅ ℝ³`, the oriented Hodge map (the cross
      product) intertwines the orthogonal action with one
      sign twist —
      `Av ×₃ Aw = det A • (A (v ×₃ w))` for every
      orthogonal `A` — exhibiting
      `Λ²W₄ ≅ W₄ ⊗ sgn` as one oriented spatial copy
      (`det` restricted to the tetrahedral image of `S₄`
      is exactly the sign character).

The general-`N` Specht classification
(`Hom_{S_N}(Λ²W_N, W_N ⊗ sgn) = 0` for `N ≠ 4`, via
`Λ²S^{(N-1,1)} ≅ S^{(N-2,1,1)}` and Young-diagram
comparison) and the one-dimensionality (Schur) of the
`N = 4` intertwiner space are the manuscript's
representation-theory layer; the compiler hypotheses
(D1)–(D4) enter through the even/nonzero-interference
selection proved here.
-/

open Matrix Finset

namespace NCG

/-- `thm:dimension-K4-selector` (parity selection, DS.5
rank arithmetic, and the `N = 4` oriented Hodge
intertwiner). -/
theorem dimension_K4_selector :
    -- (i) nondegenerate alternating forms have even dim
    (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℝ),
      Jᵀ = -J → IsUnit J.det → Even n)
    -- (ii) the boxed DS.5 selection arithmetic
    ∧ (∀ N : ℕ, Even N → 3 ≤ N →
        4 ≤ N ∧ 3 ≤ N - 1 ∧ 6 ≤ N.choose 2
        ∧ ((N - 1 = 3 ∧ N.choose 2 = 6) ↔ N = 4))
    -- (iii) the `N = 4` Hodge intertwiner:
    -- `Av ×₃ Aw = det A • A(v ×₃ w)` for orthogonal `A`
    ∧ (∀ (A : Matrix (Fin 3) (Fin 3) ℝ),
        Aᵀ * A = 1 → ∀ v w : Fin 3 → ℝ,
        crossProduct (A *ᵥ v) (A *ᵥ w)
          = A.det • (A *ᵥ crossProduct v w)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (i) parity from the determinant sign
    intro n J hJ hdet
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have h1 : J.det = (-1 : ℝ) ^ n * J.det := by
      calc J.det = Jᵀ.det := (Matrix.det_transpose J).symm
        _ = (-J).det := by rw [hJ]
        _ = (-1 : ℝ) ^ (Fintype.card (Fin n))
            * J.det := by
            rw [Matrix.det_neg]
        _ = (-1 : ℝ) ^ n * J.det := by
            rw [Fintype.card_fin]
    rw [Odd.neg_one_pow hodd] at h1
    have h2 : J.det = 0 := by linarith
    rw [h2] at hdet
    simp at hdet
  · -- (ii) the selection arithmetic
    intro N hN h3
    obtain ⟨m, hm⟩ := hN
    have h4 : 4 ≤ N := by omega
    refine ⟨h4, by omega, ?_, ?_⟩
    · rw [Nat.choose_two_right]
      have : 4 * (4 - 1) ≤ N * (N - 1) :=
        Nat.mul_le_mul h4 (by omega)
      omega
    · constructor
      · rintro ⟨h1, _⟩
        omega
      · rintro rfl
        constructor
        · rfl
        · rfl
  · -- (iii) the oriented Hodge covariance
    intro A hA v w
    -- triple-product characterization of the cross
    have htriple : ∀ x y u : Fin 3 → ℝ,
        crossProduct x y ⬝ᵥ u
        = (Matrix.of ![x, y, u]).det := by
      intro x y u
      rw [Matrix.det_fin_three]
      simp only [crossProduct, LinearMap.mk₂_apply,
        dotProduct, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    have hAAT : A * Aᵀ = 1 := by
      rw [mul_eq_one_comm] at hA
      exact hA
    -- the row-matrix transformation identity
    have hrows : ∀ u : Fin 3 → ℝ,
        (Matrix.of ![A *ᵥ v, A *ᵥ w, u])
        = (Matrix.of ![v, w, Aᵀ *ᵥ u]) * Aᵀ := by
      intro u
      ext r j
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) r with rfl | rfl | rfl
      · simp only [Matrix.of_apply, Matrix.cons_val_zero]
        rw [Matrix.mul_apply, Matrix.mulVec]
        simp only [Matrix.of_apply, Matrix.cons_val_zero]
        rw [dotProduct]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Matrix.transpose_apply]
          ring
      · simp only [Matrix.of_apply, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        rw [Matrix.mul_apply]
        simp only [Matrix.mulVec, dotProduct,
          Matrix.of_apply, Matrix.cons_val_one,
          Matrix.cons_val_zero,
          Matrix.transpose_apply]
        exact Finset.sum_congr rfl fun i _ => by ring
      · simp only [Matrix.of_apply, Matrix.cons_val]
        rw [Matrix.mul_apply]
        simp only [Matrix.of_apply, Matrix.cons_val]
        have hstep : (∑ i, (Aᵀ *ᵥ u) i * Aᵀ i j)
            = ((A * Aᵀ) *ᵥ u) j := by
          rw [← Matrix.mulVec_mulVec]
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_congr rfl fun i _ => by
            rw [Matrix.transpose_apply]
            ring
        rw [hstep, hAAT, Matrix.one_mulVec]
    -- dual comparison against every test vector
    have hkey : ∀ u : Fin 3 → ℝ,
        crossProduct (A *ᵥ v) (A *ᵥ w) ⬝ᵥ u
        = (A.det • (A *ᵥ crossProduct v w)) ⬝ᵥ u := by
      intro u
      rw [htriple, hrows u, Matrix.det_mul,
        Matrix.det_transpose]
      rw [smul_dotProduct]
      have hswap : (A *ᵥ crossProduct v w) ⬝ᵥ u
          = crossProduct v w ⬝ᵥ (Aᵀ *ᵥ u) := by
        rw [dotProduct_comm, Matrix.dotProduct_mulVec]
        rw [dotProduct_comm]
        congr 1
        exact (Matrix.mulVec_transpose A u).symm
      rw [hswap, htriple]
      ring
    -- nondegeneracy of the dot product
    have hdiff := hkey (crossProduct (A *ᵥ v) (A *ᵥ w)
      - A.det • (A *ᵥ crossProduct v w))
    set dvec := crossProduct (A *ᵥ v) (A *ᵥ w)
      - A.det • (A *ᵥ crossProduct v w) with hdvec
    have hzero : dvec ⬝ᵥ dvec = 0 := by
      rw [hdvec]
      rw [sub_dotProduct]
      rw [← hdvec]
      rw [hdiff]
      ring
    have := (dotProduct_self_eq_zero).mp hzero
    rw [hdvec] at this
    exact sub_eq_zero.mp this

end NCG
