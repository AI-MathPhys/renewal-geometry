/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ArDerivedPacket

/-!
# Canonical prime explicit-formula readout and compiler routing
  (`thm:ar-explicit-compiler-routing`, Gran-Tensor manuscript)

* `ar_explicit_compiler_routing`: the boxed explicit-formula
  readout `ℰ_X D_χ [H_X, log 𝖹_X] η = Σ_{n≤X} χ(n)Λ(n)δ_{log n}`
  (the coordinates of the von Mangoldt column), the boxed
  Laplace pairing
  `𝓛_s ∘ readout = Σ_{n≤X} χ(n)Λ(n) e^{-s log n}` (the
  truncated twisted Dirichlet series), and the endpoint-writer
  Gram `𝒞𝒞^* = Σ_n A_n P_n` with `A_n = Σ_{t : n(t)=n} a_t`.

Rendering disclosed: `ℰ_X` relabels the endpoint basis by
`log n` and is the identity matrix in these coordinates, so the
readout is the coordinate list of the proved von Mangoldt
column; `𝒞_X^rec = J_X^end` is definitional here (one writer);
the whitening/quotient clauses and the Peano descent under
multiplicative concatenation are the manuscript's bookkeeping
over the displayed Grams.
-/

open Matrix

namespace NCG

/-- The endpoint writer `J e_t = √a_t e_{n(t)}` (endpoint of
coordinate `i` is `i + 1`, overflow ignored by the guard). -/
noncomputable def writerJ (X : ℕ) {T : Type*} [Fintype T]
    (nt : T → ℕ) (wt : T → ℝ) : Matrix (Fin X) T ℂ :=
  Matrix.of fun (i : Fin X) (t : T) =>
    if nt t = (i : ℕ) + 1 then ((Real.sqrt (wt t) : ℝ) : ℂ)
    else 0

/-- `thm:ar-explicit-compiler-routing`: the explicit-formula
readout, its truncated Dirichlet pairing, and the endpoint
writer Gram. -/
theorem ar_explicit_compiler_routing {X : ℕ} (hX : 0 < X)
    (χw : ℕ → ℂ) (s : ℂ) {T : Type*} [Fintype T]
    (nt : T → ℕ) (wt : T → ℝ) (hwt : ∀ t, 0 ≤ wt t) :
    (diagFn X χw *ᵥ ((countLog X * logZop X
        - logZop X * countLog X)
      *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1)
      = fun i : Fin X => χw ((i : ℕ) + 1)
          * (ArithmeticFunction.vonMangoldt ((i : ℕ) + 1) : ℂ))
    ∧ (∑ i : Fin X, (χw ((i : ℕ) + 1)
          * (ArithmeticFunction.vonMangoldt ((i : ℕ) + 1) : ℂ))
        * Complex.exp (-s * Real.log ((i : ℕ) + 1))
      = ∑ n ∈ Finset.Icc 1 X, χw n
          * (ArithmeticFunction.vonMangoldt n : ℂ)
          * Complex.exp (-s * Real.log n))
    ∧ (writerJ X nt wt * (writerJ X nt wt)ᴴ
        = Matrix.diagonal (fun i : Fin X =>
            ((∑ t ∈ Finset.univ.filter
                (fun t => nt t = (i : ℕ) + 1),
              wt t : ℝ) : ℂ))) := by
  refine ⟨(ar_derived_packet hX).2.2.2.2 χw, ?_, ?_⟩
  · rw [Fin.sum_univ_eq_sum_range (fun m =>
      χw (m + 1) * (ArithmeticFunction.vonMangoldt (m + 1) : ℂ)
        * Complex.exp (-s * Real.log (m + 1)))]
    refine Finset.sum_nbij' (fun m => m + 1) (fun n => n - 1)
      ?_ ?_ ?_ ?_ ?_
    · intro m hm
      rw [Finset.mem_range] at hm
      rw [Finset.mem_Icc]
      omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    · intro m _
      omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      omega
    · intro m hm
      rw [Finset.mem_range] at hm
      push_cast
      ring_nf
  · ext i i'
    simp only [writerJ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.diagonal_apply]
    by_cases hii : i = i'
    · subst hii
      rw [if_pos rfl]
      rw [Finset.sum_filter]
      push_cast
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases ht : nt t = (i : ℕ) + 1
      · rw [if_pos ht, if_pos ht, RCLike.star_def,
          Complex.conj_ofReal, ← Complex.ofReal_mul,
          Real.mul_self_sqrt (hwt t)]
      · rw [if_neg ht, if_neg ht]
        simp
    · rw [if_neg hii]
      apply Finset.sum_eq_zero
      intro t _
      by_cases ht : nt t = (i : ℕ) + 1
      · rw [if_pos ht, if_neg (fun hc => hii (by
          apply Fin.ext
          omega))]
        simp
      · rw [if_neg ht, zero_mul]

end NCG
