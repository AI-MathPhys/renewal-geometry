/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RecordChain

/-!
# Internal character, affine, Mellin, and factor-depth histories
  (`thm:ar-derived-packet`, Gran-Tensor manuscript)

* `ar_derived_packet`: the diagonal endpoint histories compose
  as pointwise products (`D_χD_ψ = D_{χψ}`) with involution
  `D_χ^* = D_{χ̄}`; the shifts have the exact partial-isometry
  boundary action `T_h e_n = e_{n+h}` (zero past the cutoff);
  and the boxed von Mangoldt column holds: for every diagonal
  endpoint weight `f` (subsuming the character, affine, Mellin,
  and heat columns at once),
  `D_f [H_X, log 𝖹_X] η^rec = (f(n)Λ(n) e_n)_{n ≤ X}`.

Rendering disclosed: all diagonal histories (character, affine
`e^{2πinθ}`, Mellin `n^{-σ-iτ}e^{-t(log n)²}`, Liouville,
Möbius, factor depth) are instances of the one diagonal
functional calculus `diagFn`, so the packet clauses are stated
for an arbitrary endpoint weight; `log 𝖹_X` is rendered by its
terminating prime-power expansion `Σ_{2≤n≤X}(Λ(n)/log n)·L_n`
(the coefficient vanishes off prime powers and equals `1/k` at
`p^k`); membership of every operator in `M_X(ℂ)` is by
construction.
-/

open Matrix

namespace NCG

/-- Diagonal endpoint history with weight `f` (coordinate `i`
carries endpoint `i + 1`). -/
def diagFn (X : ℕ) (f : ℕ → ℂ) : Matrix (Fin X) (Fin X) ℂ :=
  Matrix.diagonal (fun i => f ((i : ℕ) + 1))

/-- The shift `T_h e_n = e_{n+h}` with overflow to zero. -/
def shiftT (X h : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  Matrix.of fun (j i : Fin X) =>
    if (j : ℕ) = (i : ℕ) + h then 1 else 0

/-- The endpoint logarithm history `H_X = diag(log n)`. -/
noncomputable def countLog (X : ℕ) :
    Matrix (Fin X) (Fin X) ℂ :=
  diagFn X (fun n => (Real.log n : ℂ))

/-- The terminating operator logarithm
`log 𝖹_X = Σ_{p^k ≤ X} L_{p^k}/k`, packaged through the
von Mangoldt coefficient `Λ(n)/log n`. -/
noncomputable def logZop (X : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  ∑ n ∈ Finset.Icc 2 X,
    ((ArithmeticFunction.vonMangoldt n / Real.log n : ℝ) : ℂ)
      • peanoL X n

/-- `thm:ar-derived-packet`: diagonal composition, involution,
shift boundary action, and the boxed von Mangoldt column. -/
theorem ar_derived_packet {X : ℕ} (hX : 0 < X) :
    (∀ f g : ℕ → ℂ, diagFn X f * diagFn X g
        = diagFn X (fun n => f n * g n))
    ∧ (∀ f : ℕ → ℂ, (diagFn X f)ᴴ
        = diagFn X (fun n => starRingEnd ℂ (f n)))
    ∧ (∀ (h : ℕ) (i : Fin X) (hi : (i : ℕ) + h < X),
        shiftT X h *ᵥ Pi.single i 1
          = Pi.single (⟨(i : ℕ) + h, hi⟩ : Fin X) 1)
    ∧ (∀ (h : ℕ) (i : Fin X), ¬ ((i : ℕ) + h < X) →
        shiftT X h *ᵥ Pi.single i 1 = 0)
    ∧ (∀ f : ℕ → ℂ,
        diagFn X f *ᵥ ((countLog X * logZop X
            - logZop X * countLog X)
          *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1)
        = fun i : Fin X => f ((i : ℕ) + 1)
            * (ArithmeticFunction.vonMangoldt ((i : ℕ) + 1)
              : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f g
    rw [diagFn, diagFn, diagFn, Matrix.diagonal_mul_diagonal]
  · intro f
    rw [diagFn, diagFn, Matrix.diagonal_conjTranspose]
    congr 1
  · intro h i hi
    funext j
    simp only [shiftT, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · by_cases hj : (j : ℕ) = (i : ℕ) + h
      · rw [if_pos hj, if_pos rfl,
          if_pos (Fin.ext (a := j) hj)]
        simp
      · rw [if_neg hj,
          if_neg (fun hc : j = (⟨(i : ℕ) + h, hi⟩ : Fin X) =>
            hj (by rw [hc]))]
        simp
    · intro k _ hk
      rw [if_neg (fun hc : k = i => hk hc), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  · intro h i hi
    funext j
    simp only [shiftT, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Pi.single_apply, Pi.zero_apply]
    rw [Finset.sum_eq_single i]
    · rw [if_neg (fun hc : (j : ℕ) = (i : ℕ) + h =>
        hi (hc ▸ j.2)), zero_mul]
    · intro k _ hk
      rw [if_neg (fun hc : k = i => hk hc), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  · intro f
    have hbracket : ∀ n : ℕ, 2 ≤ n →
        countLog X * peanoL X n - peanoL X n * countLog X
          = ((Real.log n : ℝ) : ℂ) • peanoL X n := by
      intro n hn
      ext j i
      simp only [Matrix.sub_apply, Matrix.smul_apply,
        countLog, diagFn, peanoL, Matrix.diagonal_mul,
        Matrix.mul_diagonal, Matrix.of_apply, smul_eq_mul]
      by_cases hcond : (j : ℕ) + 1 = n * ((i : ℕ) + 1)
      · rw [if_pos hcond]
        have hj : (((j : ℕ) : ℝ) + 1)
            = (n : ℝ) * (((i : ℕ) : ℝ) + 1) := by
          exact_mod_cast congrArg (Nat.cast (R := ℝ)) hcond
        have hlog : Real.log (((j : ℕ) : ℝ) + 1)
            = Real.log n + Real.log (((i : ℕ) : ℝ) + 1) := by
          rw [hj, Real.log_mul (by positivity) (by positivity)]
        push_cast [hlog]
        ring
      · rw [if_neg hcond]
        ring
    have hcomm : countLog X * logZop X - logZop X * countLog X
        = ∑ n ∈ Finset.Icc 2 X,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
              • peanoL X n := by
      rw [logZop, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub,
        hbracket n hn2, smul_smul]
      congr 1
      have hlog0 : Real.log n ≠ 0 := by
        have h1 : (1 : ℝ) < n := by exact_mod_cast hn2
        exact (Real.log_pos h1).ne'
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp
    have hcol : ∀ n : ℕ, 2 ≤ n → n ≤ X →
        ∀ i : Fin X,
        (peanoL X n *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) i
          = if (i : ℕ) + 1 = n then 1 else 0 := by
      intro n hn2 hnX i
      simp only [peanoL, Matrix.mulVec, dotProduct,
        Matrix.of_apply, Pi.single_apply]
      rw [Finset.sum_eq_single (⟨0, hX⟩ : Fin X)]
      · rw [if_pos rfl, mul_one]
        congr 1
        simp
      · intro k _ hk
        rw [if_neg (fun hc : k = (⟨0, hX⟩ : Fin X) => hk hc),
          mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    have heta : ((countLog X * logZop X
        - logZop X * countLog X)
        *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1)
        = fun i : Fin X =>
            (ArithmeticFunction.vonMangoldt ((i : ℕ) + 1)
              : ℂ) := by
      rw [hcomm]
      funext i
      rw [Matrix.sum_mulVec, Finset.sum_apply]
      have hterm : ∀ n ∈ Finset.Icc 2 X,
          ((((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
            • peanoL X n) *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) i
          = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
            * (if (i : ℕ) + 1 = n then 1 else 0) := by
        intro n hn
        obtain ⟨hn2, hnX⟩ := Finset.mem_Icc.mp hn
        rw [Matrix.smul_mulVec, Pi.smul_apply,
          hcol n hn2 hnX i, smul_eq_mul]
      rw [Finset.sum_congr rfl hterm]
      by_cases hi1 : 1 ≤ (i : ℕ)
      · have hmem : (i : ℕ) + 1 ∈ Finset.Icc 2 X := by
          rw [Finset.mem_Icc]
          have := i.2
          omega
        rw [Finset.sum_eq_single_of_mem ((i : ℕ) + 1) hmem]
        · rw [if_pos rfl, mul_one]
        · intro b _ hb
          rw [if_neg (fun hc => hb (by omega)), mul_zero]
      · have hi0 : (i : ℕ) = 0 := by omega
        rw [Finset.sum_eq_zero, hi0]
        · simp [ArithmeticFunction.vonMangoldt_apply_one]
        · intro b hb
          have hb2 : 2 ≤ b := (Finset.mem_Icc.mp hb).1
          rw [if_neg (by omega), mul_zero]
    rw [heta]
    funext i
    simp only [diagFn, Matrix.mulVec, dotProduct,
      Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg (fun hc : i = k => hk hc.symm), zero_mul]
    · intro hk
      exact absurd (Finset.mem_univ _) hk

end NCG
