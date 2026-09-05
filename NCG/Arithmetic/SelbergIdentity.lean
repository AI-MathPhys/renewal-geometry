/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.SignedSeparator

/-!
# The Selberg degree-two identity `Λ₂ = Λ·log + Λ∗Λ`
  (`lem:v003-selberg`, arithmetic monograph — full form)

The manuscript proves the identity via Dirichlet series
(`ζ''/ζ = -A' + A²`). Here we give the finite combinatorial proof
through the log-derivation on the Dirichlet ring:

* `pmul_log_mul` — `L(f∗g) = Lf∗g + f∗Lg` where `(Lf)(n) = f(n)log n`
  (the pointwise-log operator is a derivation for Dirichlet
  convolution);
* `selberg_af` — applying the derivation to `Λ∗ζ = log` and
  Möbius-inverting: `μ∗log² = Λ·log + Λ∗Λ` as arithmetic
  functions;
* `lambdaJ_one_eq_vonMangoldt` / `lambdaJ_two_eq` /
  `lambdaConv_eq` — the bridge from the monograph's
  `Λ_j(n) = Σ_{d|n} μ(d)log^j(n/d)` to the Mathlib Dirichlet ring;
* `selberg_identity` — `Λ₂(n) = Λ(n)·log n + (Λ∗Λ)(n)` for every
  `n ≠ 0` (not only the squarefree stratum).
-/

namespace NCG

open Finset

open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-- The pointwise-log operator is a derivation for Dirichlet
convolution: `L(f∗g) = Lf∗g + f∗Lg`. -/
lemma pmul_log_mul (f g : ArithmeticFunction ℝ) :
    ArithmeticFunction.log.pmul (f * g)
      = (ArithmeticFunction.log.pmul f) * g
        + f * (ArithmeticFunction.log.pmul g) := by
  ext n
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hx1 : x.1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxn
    exact hn0 hxn.symm
  have hx2 : x.2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hxn
    exact hn0 hxn.symm
  have hlog : Real.log n = Real.log x.1 + Real.log x.2 := by
    rw [← hxn]
    push_cast
    exact Real.log_mul (Nat.cast_ne_zero.mpr hx1)
      (Nat.cast_ne_zero.mpr hx2)
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.log_apply, ArithmeticFunction.log_apply,
    ArithmeticFunction.log_apply, hlog]
  ring

/-- `L(ζ) = log`: the zeta function absorbs the pointwise log. -/
lemma pmul_log_zeta :
    ArithmeticFunction.log.pmul (ζ : ArithmeticFunction ℝ)
      = ArithmeticFunction.log := by
  ext n
  rcases eq_or_ne n 0 with h | h
  · subst h
    simp
  · rw [ArithmeticFunction.pmul_apply,
      ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne h]
    push_cast
    rw [mul_one]

/-- The Selberg identity at the level of arithmetic functions:
`μ∗log² = Λ·log + Λ∗Λ`. -/
theorem selberg_af :
    (ArithmeticFunction.moebius : ArithmeticFunction ℤ)
        * (ArithmeticFunction.log.pmul ArithmeticFunction.log)
      = ArithmeticFunction.log.pmul ArithmeticFunction.vonMangoldt
        + ArithmeticFunction.vonMangoldt
          * ArithmeticFunction.vonMangoldt := by
  have h1 : ArithmeticFunction.log.pmul
        (ArithmeticFunction.vonMangoldt * (ζ : ArithmeticFunction ℝ))
      = (ArithmeticFunction.log.pmul
            ArithmeticFunction.vonMangoldt)
          * (ζ : ArithmeticFunction ℝ)
        + ArithmeticFunction.vonMangoldt
          * ArithmeticFunction.log := by
    rw [pmul_log_mul, pmul_log_zeta]
  rw [ArithmeticFunction.vonMangoldt_mul_zeta] at h1
  rw [h1]
  have hz : (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
      * (ζ : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hm : (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
      * ArithmeticFunction.log = ArithmeticFunction.vonMangoldt :=
    ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
  linear_combination
    (ArithmeticFunction.log.pmul ArithmeticFunction.vonMangoldt)
        * hz
      + ArithmeticFunction.vonMangoldt * hm

/-- The monograph's `Λ_j` rewritten with `log(n/d)`. -/
lemma lambdaJ_eq_div_form (j : ℕ) {n : ℕ} (hn : n ≠ 0) :
    lambdaJ j n = ∑ d ∈ n.divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)
        * (Real.log ((n / d : ℕ) : ℝ)) ^ j := by
  rw [lambdaJ]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr hd0),
    Real.log_div (Nat.cast_ne_zero.mpr hn)
      (Nat.cast_ne_zero.mpr hd0)]

/-- `Λ₁ = Λ`: the monograph's degree-one function is the von
Mangoldt function. -/
theorem lambdaJ_one_eq_vonMangoldt {n : ℕ} (hn : n ≠ 0) :
    lambdaJ 1 n = ArithmeticFunction.vonMangoldt n := by
  rw [← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt,
    ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun a b =>
        ((ArithmeticFunction.moebius : ArithmeticFunction ℝ)) a
          * ArithmeticFunction.log b),
    lambdaJ_eq_div_form 1 hn]
  apply Finset.sum_congr rfl
  intro d _
  rw [ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.log_apply, pow_one]

/-- `Λ₂ = μ∗log²` in the Dirichlet ring. -/
lemma lambdaJ_two_eq {n : ℕ} (hn : n ≠ 0) :
    lambdaJ 2 n
      = ((ArithmeticFunction.moebius : ArithmeticFunction ℝ)
          * (ArithmeticFunction.log.pmul ArithmeticFunction.log))
          n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun a b =>
        ((ArithmeticFunction.moebius : ArithmeticFunction ℝ)) a
          * (ArithmeticFunction.log.pmul
              ArithmeticFunction.log) b),
    lambdaJ_eq_div_form 2 hn]
  apply Finset.sum_congr rfl
  intro d _
  rw [ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.pmul_apply,
    ArithmeticFunction.log_apply]
  ring

/-- The monograph's autocorrelation is `Λ∗Λ`. -/
theorem lambdaConv_eq {n : ℕ} (hn : n ≠ 0) :
    lambdaConv n
      = (ArithmeticFunction.vonMangoldt
          * ArithmeticFunction.vonMangoldt) n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun a b => ArithmeticFunction.vonMangoldt a
        * ArithmeticFunction.vonMangoldt b),
    lambdaConv]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hnd0 : n / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd)
      (Nat.pos_of_ne_zero hd0)).ne'
  rw [lambdaJ_one_eq_vonMangoldt hd0,
    lambdaJ_one_eq_vonMangoldt hnd0]

/-- `lem:v003-selberg` (full form): the Selberg degree-two identity
`Λ₂(n) = Λ(n)·log n + (Λ∗Λ)(n)` for every `n ≠ 0`. -/
theorem selberg_identity {n : ℕ} (hn : n ≠ 0) :
    lambdaJ 2 n = lambdaJ 1 n * Real.log n + lambdaConv n := by
  calc lambdaJ 2 n
      = ((ArithmeticFunction.moebius : ArithmeticFunction ℝ)
          * (ArithmeticFunction.log.pmul ArithmeticFunction.log))
          n := lambdaJ_two_eq hn
    _ = (ArithmeticFunction.log.pmul ArithmeticFunction.vonMangoldt
          + ArithmeticFunction.vonMangoldt
            * ArithmeticFunction.vonMangoldt) n := by
        rw [← selberg_af]
    _ = Real.log n * ArithmeticFunction.vonMangoldt n
        + (ArithmeticFunction.vonMangoldt
            * ArithmeticFunction.vonMangoldt) n := by
        rw [ArithmeticFunction.add_apply,
          ArithmeticFunction.pmul_apply,
          ArithmeticFunction.log_apply]
    _ = lambdaJ 1 n * Real.log n + lambdaConv n := by
        rw [lambdaJ_one_eq_vonMangoldt hn, lambdaConv_eq hn]
        ring

end NCG
