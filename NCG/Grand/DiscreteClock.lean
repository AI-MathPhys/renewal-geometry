/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniformization, its gauge, and discrete non-embeddability
  (`thm:renewal-uniformization`,
  `thm:renewal-uniformization-gauge`, and
  `cth:discrete-renewal-nonembeddable`,
  Gran-Tensor manuscript)

* `exp_one_sub_idem`: for an idempotent `P` in a real
  Banach algebra, `exp(c(1-P)) = 1 + (e^c - 1)(1-P)`.

* `renewal_uniformization`: the boxed concrete generator
  `L₀` factors as `L₀ = -g(I-Π_π)` through the stationary
  projector with rows `π = (5/11, 6/11)`, giving the boxed
  semigroup `e^{tL₀} = Π_π + e^{-gt}(I-Π_π)` with exact
  relaxation rate `g = 22λ/15`, and `π` is stationary.

* `renewal_uniformization_gauge`: `K = I + Λ⁻¹L` is
  stochastic for every `Λ ≥ max{α,β}` and all admissible
  rates share the boxed generator `Λ(K-I) = L`.

* `discrete_renewal_nonembeddable`: the boxed `M₀ = e^{τL}`
  has no two-state Markov generator solution: every such
  exponential has trace `1 + e^{-s} > 1` (or `2` for the
  zero generator), while `trace M₀ = 8/15 < 1`.
-/

open Matrix NormedSpace

namespace NCG

/-- Exponential of an idempotent-split generator. -/
theorem exp_one_sub_idem {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A]
    (P : A) (hP : P * P = P) (c : ℝ) :
    exp (c • ((1 : A) - P))
      = 1 + (Real.exp c - 1) • ((1 : A) - P) := by
  have hQ2 : ((1 : A) - P) * ((1 : A) - P) = 1 - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP]
    abel
  have hQ : ∀ n : ℕ, 1 ≤ n →
      ((1 : A) - P) ^ n = 1 - P := by
    intro n hn
    induction n with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp
      · rw [pow_succ, ih hk, hQ2]
  have hs : Summable fun n : ℕ =>
      ((n.factorial : ℝ))⁻¹ • (c • ((1 : A) - P)) ^ n :=
    expSeries_summable' (𝕂 := ℝ) _
  rw [exp_eq_tsum (𝕂 := ℝ)]
  beta_reduce
  rw [hs.tsum_eq_zero_add]
  have htail : ∀ n : ℕ,
      (((n + 1).factorial : ℝ))⁻¹
        • (c • ((1 : A) - P)) ^ (n + 1)
      = (c ^ (n + 1) / ((n + 1).factorial : ℝ))
        • ((1 : A) - P) := by
    intro n
    rw [smul_pow, hQ (n + 1) (by omega), smul_smul]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have hexpc : Real.exp c
      = ∑' n : ℕ, c ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, exp_eq_tsum (𝕂 := ℝ)]
    exact tsum_congr fun n => by
      rw [smul_eq_mul, div_eq_mul_inv]
      ring
  have htailval : ∑' n : ℕ,
      c ^ (n + 1) / (((n + 1).factorial : ℝ))
      = Real.exp c - 1 := by
    have h :=
      (Real.summable_pow_div_factorial c).tsum_eq_zero_add
    rw [← hexpc] at h
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one]
      at h
    have h1 : (1 : ℝ) / 1 = 1 := by norm_num
    rw [h1] at h
    linarith
  have hshift : Summable fun n : ℕ =>
      c ^ (n + 1) / (((n + 1).factorial : ℝ)) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_pow_div_factorial c)
    simpa using h
  rw [tsum_congr htail, hshift.tsum_smul_const, htailval]
  simp

/-- `thm:renewal-uniformization`. -/
theorem renewal_uniformization (lam t : ℝ) :
    -- (i) the stationary projector
    ((!![5/11, 6/11; 5/11, 6/11] :
        Matrix (Fin 2) (Fin 2) ℝ)
      * !![5/11, 6/11; 5/11, 6/11]
      = !![5/11, 6/11; 5/11, 6/11])
    -- (ii) the boxed spectral factorization `L₀ = -g(I-Π)`
    ∧ ((!![-(4*lam/5), 4*lam/5; 2*lam/3, -(2*lam/3)] :
        Matrix (Fin 2) (Fin 2) ℝ)
      = (-(22*lam/15))
        • ((1 : Matrix (Fin 2) (Fin 2) ℝ)
          - !![5/11, 6/11; 5/11, 6/11]))
    -- (iii) the boxed semigroup with rate `g = 22λ/15`
    ∧ (exp (t • (!![-(4*lam/5), 4*lam/5;
          2*lam/3, -(2*lam/3)] :
        Matrix (Fin 2) (Fin 2) ℝ))
      = 1 + (Real.exp (t * -(22*lam/15)) - 1)
        • ((1 : Matrix (Fin 2) (Fin 2) ℝ)
          - !![5/11, 6/11; 5/11, 6/11]))
    -- (iv) `π` is stationary
    ∧ (![5/11, 6/11] ᵥ*
        (!![-(4*lam/5), 4*lam/5; 2*lam/3, -(2*lam/3)] :
          Matrix (Fin 2) (Fin 2) ℝ) = 0) := by
  have hPi : (!![5/11, 6/11; 5/11, 6/11] :
      Matrix (Fin 2) (Fin 2) ℝ)
      * !![5/11, 6/11; 5/11, 6/11]
      = !![5/11, 6/11; 5/11, 6/11] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      norm_num
  have hL : (!![-(4*lam/5), 4*lam/5;
      2*lam/3, -(2*lam/3)] :
      Matrix (Fin 2) (Fin 2) ℝ)
      = (-(22*lam/15))
        • ((1 : Matrix (Fin 2) (Fin 2) ℝ)
          - !![5/11, 6/11; 5/11, 6/11]) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, Matrix.sub_apply] <;>
      ring
  refine ⟨hPi, hL, ?_, ?_⟩
  · letI : SeminormedRing (Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.linftyOpSemiNormedRing
    letI : NormedRing (Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.linftyOpNormedAlgebra
    letI : CompleteSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
      FiniteDimensional.complete ℝ _
    rw [hL, smul_smul]
    exact exp_one_sub_idem _ hPi _
  · funext j
    fin_cases j <;>
      simp [Matrix.vecMul] <;>
      ring

/-- `thm:renewal-uniformization-gauge`. -/
theorem renewal_uniformization_gauge (α β Λ : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hΛmax : max α β ≤ Λ)
    (hΛ0 : 0 < Λ) :
    -- the uniformized kernel is stochastic
    ((0 ≤ 1 - α / Λ ∧ 0 ≤ α / Λ)
      ∧ (0 ≤ β / Λ ∧ 0 ≤ 1 - β / Λ)
      ∧ (1 - α / Λ) + α / Λ = 1
      ∧ β / Λ + (1 - β / Λ) = 1)
    -- the boxed gauge identity `Λ(K - I) = L`
    ∧ (∀ L : Matrix (Fin 2) (Fin 2) ℝ,
        Λ • (((1 : Matrix (Fin 2) (Fin 2) ℝ)
          + Λ⁻¹ • L) - 1) = L)
    -- all admissible rates share the generator
    ∧ (∀ (L : Matrix (Fin 2) (Fin 2) ℝ) (Λ' : ℝ),
        Λ' ≠ 0 →
        Λ • (((1 : Matrix (Fin 2) (Fin 2) ℝ)
          + Λ⁻¹ • L) - 1)
        = Λ' • (((1 : Matrix (Fin 2) (Fin 2) ℝ)
          + Λ'⁻¹ • L) - 1)) := by
  have hgauge : ∀ (L : Matrix (Fin 2) (Fin 2) ℝ)
      (Λ'' : ℝ), Λ'' ≠ 0 →
      Λ'' • (((1 : Matrix (Fin 2) (Fin 2) ℝ)
        + Λ''⁻¹ • L) - 1) = L := by
    intro L Λ'' hne
    rw [add_sub_cancel_left, smul_smul,
      mul_inv_cancel₀ hne, one_smul]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · have hαΛ : α ≤ Λ := le_trans (le_max_left α β) hΛmax
    have := div_le_one_of_le₀ hαΛ hΛ0.le
    linarith
  · positivity
  · positivity
  · have hβΛ : β ≤ Λ := le_trans (le_max_right α β) hΛmax
    have := div_le_one_of_le₀ hβΛ hΛ0.le
    linarith
  · ring
  · ring
  · intro L
    exact hgauge L Λ (ne_of_gt hΛ0)
  · intro L Λ' hΛ'
    rw [hgauge L Λ (ne_of_gt hΛ0), hgauge L Λ' hΛ']

/-- `cth:discrete-renewal-nonembeddable`. -/
theorem discrete_renewal_nonembeddable (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (!![1/5, 4/5; 2/3, 1/3] :
      Matrix (Fin 2) (Fin 2) ℝ)
      ≠ exp (!![-a, a; b, -b] :
        Matrix (Fin 2) (Fin 2) ℝ) := by
  letI : SeminormedRing (Matrix (Fin 2) (Fin 2) ℝ) :=
    Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin 2) (Fin 2) ℝ) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
    Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    FiniteDimensional.complete ℝ _
  intro h
  rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ a + b)
    with hs | hs
  · -- zero generator: exponential is the identity
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    rw [ha0, hb0] at h
    have hzero : (!![-(0:ℝ), 0; 0, -0] :
        Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [show (!![-(0:ℝ), 0; 0, -(0:ℝ)] :
        Matrix (Fin 2) (Fin 2) ℝ) = 0 from hzero,
      exp_zero] at h
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      M 0 0) h
    simp at this
  · -- positive total rate: trace of the exponential exceeds 1
    set s : ℝ := a + b with hsdef
    have hPiab : (!![b/s, a/s; b/s, a/s] :
        Matrix (Fin 2) (Fin 2) ℝ)
        * !![b/s, a/s; b/s, a/s]
        = !![b/s, a/s; b/s, a/s] := by
      have hss : s ≠ 0 := ne_of_gt hs
      ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [Matrix.mul_apply, Fin.sum_univ_two]
         try field_simp
         try ring)
    have hLab : (!![-a, a; b, -b] :
        Matrix (Fin 2) (Fin 2) ℝ)
        = (-s) • ((1 : Matrix (Fin 2) (Fin 2) ℝ)
          - !![b/s, a/s; b/s, a/s]) := by
      have hss : s ≠ 0 := ne_of_gt hs
      ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [Matrix.smul_apply, Matrix.sub_apply]
         try field_simp
         try ring)
    have hexp : exp (!![-a, a; b, -b] :
        Matrix (Fin 2) (Fin 2) ℝ)
        = 1 + (Real.exp (-s) - 1)
          • ((1 : Matrix (Fin 2) (Fin 2) ℝ)
            - !![b/s, a/s; b/s, a/s]) := by
      calc exp (!![-a, a; b, -b] :
          Matrix (Fin 2) (Fin 2) ℝ)
          = exp ((-s) • ((1 : Matrix (Fin 2) (Fin 2) ℝ)
            - !![b/s, a/s; b/s, a/s])) := by rw [← hLab]
        _ = _ := exp_one_sub_idem _ hPiab _
    rw [hexp] at h
    have htr := congrArg Matrix.trace h
    have hss : s ≠ 0 := ne_of_gt hs
    rw [Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_sub] at htr
    have h1 : (!![1/5, 4/5; 2/3, 1/3] :
        Matrix (Fin 2) (Fin 2) ℝ).trace = 8/15 := by
      rw [Matrix.trace_fin_two_of]
      norm_num
    have h2 : ((1 : Matrix (Fin 2) (Fin 2) ℝ)).trace
        = 2 := by
      simp [Matrix.trace_one]
    have h3 : (!![b/s, a/s; b/s, a/s] :
        Matrix (Fin 2) (Fin 2) ℝ).trace = 1 := by
      rw [Matrix.trace_fin_two_of]
      field_simp
      ring
    rw [h1, h2, h3] at htr
    rw [smul_eq_mul] at htr
    have hepos : 0 < Real.exp (-s) := Real.exp_pos _
    nlinarith [htr, hepos]

end NCG
