/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandInterface2

/-!
# Canonical faithful trace
  (`thm:regular-trace`, Gran-Tensor manuscript)

* `regular_trace`: on `𝒜 ≅ ⊕_λ M_{n_λ}(ℂ)` the boxed regular
  trace `τ_reg(a) = Σ_λ n_λ Tr(a_λ)` is tracial and faithful,
  and `dim_ℂ 𝒜 = Σ_λ n_λ²`.

Rendering disclosed: the algebra is rendered in its Wedderburn
coordinates (the product of matrix blocks); invariance of the
regular trace under every `*`-isomorphism is the manuscript's
uniqueness-of-Wedderburn-coordinates bookkeeping, and the
normalization of the tracial state is the division by
`Σ_λ n_λ²`.
-/

open Matrix

namespace NCG

/-- `thm:regular-trace`: the regular trace on a product of
matrix blocks is tracial and faithful, with the block dimension
formula. -/
theorem regular_trace {L : Type*} [Fintype L] (nd : L → ℕ) :
    (∀ a b : (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ),
      ∑ l, (nd l : ℂ) * (a l * b l).trace
        = ∑ l, (nd l : ℂ) * (b l * a l).trace)
    ∧ (∀ a : (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ),
        ∑ l, (nd l : ℂ) * ((a l)ᴴ * a l).trace = 0 →
        (∀ l, 0 < nd l) → a = 0)
    ∧ Module.finrank ℂ
        (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ)
      = ∑ l, nd l ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.trace_mul_comm]
  · intro a ha hpos
    have hre : ∑ l, (nd l : ℝ) * (((a l)ᴴ * a l).trace).re
        = 0 := by
      have h := congrArg Complex.re ha
      rw [Complex.re_sum, Complex.zero_re] at h
      calc ∑ l, (nd l : ℝ) * (((a l)ᴴ * a l).trace).re
          = ∑ l, ((nd l : ℂ) * ((a l)ᴴ * a l).trace).re := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Complex.mul_re]
            simp
        _ = 0 := h
    have hterm : ∀ l ∈ Finset.univ,
        0 ≤ (nd l : ℝ) * (((a l)ᴴ * a l).trace).re := by
      intro l _
      apply mul_nonneg (Nat.cast_nonneg _)
      rw [trace_conj_self_re]
      exact Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp
      hre
    funext l
    have hl := hzero l (Finset.mem_univ l)
    have hnd : (0 : ℝ) < (nd l : ℝ) := by
      exact_mod_cast hpos l
    have htr : (((a l)ᴴ * a l).trace).re = 0 := by
      rcases mul_eq_zero.mp hl with h | h
      · exact absurd h hnd.ne'
      · exact h
    exact trace_conj_self_re_eq_zero (a l) |>.mp htr
  · rw [Module.finrank_pi_fintype]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Module.finrank_matrix, Fintype.card_fin,
      Module.finrank_self, mul_one, sq]

end NCG
