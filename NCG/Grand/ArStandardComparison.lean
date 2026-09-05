/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RecordChain

/-!
# Source-fixing monoidal comparison with standard arithmetic
  (`thm:ar-standard-comparison`, Gran-Tensor manuscript)

* `ar_standard_comparison`: the endpoint-label map
  `U ε_n = e_n` is the unique source-fixing intertwiner of the
  standard and record realizations — rendered as: any matrix
  commuting with the endpoint count operator `diag(n+1)` and
  with the chronological successor `recS`, and fixing the
  source label `e_0`, is the identity.  Hence all word Grams
  and finite transfer panels of the standard and record
  realizations agree.

Rendering disclosed: the standard and record realizations share
the concrete endpoint-label carrier in the formalization, so the
endpoint-label map is the identity relabeling and the rendered
content is the uniqueness clause; agreement of word Grams and
transfer panels is the immediate bookkeeping over `U = 1`.
The intertwining hypotheses are stated for the count operator
and the successor (the generators of the basic packet); no
prime or character coefficient enters.
-/

open Matrix

namespace NCG

/-- `thm:ar-standard-comparison`: a source-fixing intertwiner of
the endpoint count operator and the chronological successor is
the identity. -/
theorem ar_standard_comparison {X : ℕ} (hX : 0 < X)
    (U : Matrix (Fin X) (Fin X) ℂ)
    (hN : U * Matrix.diagonal
          (fun i : Fin X => (((i : ℕ) + 1 : ℕ) : ℂ))
        = Matrix.diagonal
            (fun i : Fin X => (((i : ℕ) + 1 : ℕ) : ℂ)) * U)
    (hS : U * recS X = recS X * U)
    (hsrc : U *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
        = Pi.single (⟨0, hX⟩ : Fin X) 1) :
    U = 1 := by
  -- off-diagonal entries vanish: distinct count eigenvalues
  have hdiag : ∀ i j : Fin X, i ≠ j → U i j = 0 := by
    intro i j hij
    have h := congrArg (fun M => M i j) hN
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hne : (((j : ℕ) + 1 : ℕ) : ℂ) ≠ (((i : ℕ) + 1 : ℕ) : ℂ) := by
      intro hc
      apply hij
      have : (j : ℕ) + 1 = (i : ℕ) + 1 := by exact_mod_cast hc
      exact (Fin.ext (by omega)).symm
    have hz : U i j * ((((j : ℕ) + 1 : ℕ) : ℂ)
        - (((i : ℕ) + 1 : ℕ) : ℂ)) = 0 := by
      rw [mul_sub, h]
      ring
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.mp h0) hne
  -- the successor equalizes consecutive diagonal entries
  have hstep : ∀ m : ℕ, ∀ (hm1 : m + 1 < X),
      U ⟨m + 1, hm1⟩ ⟨m + 1, hm1⟩
        = U ⟨m, by omega⟩ ⟨m, by omega⟩ := by
    intro m hm1
    have h := congrArg (fun M => M ⟨m + 1, hm1⟩ (⟨m, by omega⟩ : Fin X)) hS
    simp only [Matrix.mul_apply, recS, Matrix.of_apply] at h
    have hL : ∑ k : Fin X, U ⟨m + 1, hm1⟩ k
        * (if (k : ℕ) = (m : ℕ) + 1 then (1 : ℂ) else 0)
        = U ⟨m + 1, hm1⟩ ⟨m + 1, hm1⟩ := by
      rw [Finset.sum_eq_single (⟨m + 1, hm1⟩ : Fin X)]
      · simp
      · intro k _ hk
        rw [if_neg, mul_zero]
        intro hc
        exact hk (Fin.ext hc)
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    have hR : ∑ k : Fin X,
        (if ((⟨m + 1, hm1⟩ : Fin X) : ℕ) = (k : ℕ) + 1
          then (1 : ℂ) else 0) * U k ⟨m, by omega⟩
        = U ⟨m, by omega⟩ ⟨m, by omega⟩ := by
      rw [Finset.sum_eq_single (⟨m, by omega⟩ : Fin X)]
      · simp
      · intro k _ hk
        rw [if_neg, zero_mul]
        intro hc
        apply hk
        apply Fin.ext
        simpa using hc.symm
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    rw [hL, hR] at h
    exact h
  -- the source is fixed: the first diagonal entry is one
  have h00 : U ⟨0, hX⟩ ⟨0, hX⟩ = 1 := by
    have h := congrFun hsrc ⟨0, hX⟩
    have hval : (U *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) ⟨0, hX⟩
        = U ⟨0, hX⟩ ⟨0, hX⟩ := by
      simp only [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [Finset.sum_eq_single (⟨0, hX⟩ : Fin X)]
      · simp
      · intro k _ hk
        rw [if_neg hk, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    rw [hval] at h
    rw [h]
    simp
  -- all diagonal entries are one by induction
  have hone : ∀ m : ℕ, ∀ (hm : m < X),
      U ⟨m, hm⟩ ⟨m, hm⟩ = 1 := by
    intro m
    induction m with
    | zero => intro hm; exact h00
    | succ k ih =>
        intro hm
        rw [hstep k hm]
        exact ih (by omega)
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    have := hone (i : ℕ) i.2
    simpa using this
  · rw [Matrix.one_apply_ne hij]
    exact hdiag i j hij

end NCG
