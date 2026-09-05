/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact imprimitive Euler correction
  (`prop:v002-imprimitive`, arithmetic manuscript)

For a character `χ* mod q` induced to level `Q` (rendered by
Mathlib's `DirichletCharacter.changeLevel` along `q ∣ Q`):

* the boxed finite Euler correction
  `L(s,χ) = L(s,χ*)·∏_{p∣Q, p∤q} (1 - χ*(p)p^{-s})`
  (`imprimitive_euler_correction`, from Mathlib's
  `LFunction_changeLevel` by dropping the factors at `p ∣ q`,
  which equal one);
* the boxed logarithmic-derivative identity
  `-L'/L(s,χ) = -L'/L(s,χ*) - ∑_{p∣Q, p∤q}
  χ*(p)(log p)p^{-s}/(1 - χ*(p)p^{-s})`
  (`imprimitive_log_deriv`, away from `s = 1`, zeros, and zeros
  of the added factors);
* every zero of an added Euler factor lies on `Re s = 0`
  (`added_factor_zero_re`, since `|χ*(p)| = 1` there);
* hence in the strip `Re s > 0` the zeros of `L(s,χ)` are
  precisely the zeros of `L(s,χ*)`
  (`imprimitive_strip_zeros`).

The multiplicity statement is subsumed by the identity of the
two functions up to the nonvanishing entire correction factor on
the strip; the corollary reducing Dirichlet GRH to primitive
characters is prose.
-/

open DirichletCharacter Finset

namespace NCG

variable {M N : ℕ} [NeZero M] [NeZero N]

/-- `prop:v002-imprimitive`, first box: the exact finite Euler
correction over the primes dividing the level but not the
conductor. -/
theorem imprimitive_euler_correction (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) :
    LFunction (changeLevel hMN χ) s
      = LFunction χ s
        * ∏ p ∈ N.primeFactors with ¬p ∣ M,
            (1 - χ p * (p : ℂ) ^ (-s)) := by
  rw [LFunction_changeLevel hMN χ h]
  congr 1
  refine (Finset.prod_subset (Finset.filter_subset _ _)
    fun p hp hnp => ?_).symm
  have hpM : p ∣ M := by
    simp only [Finset.mem_filter, not_and, not_not] at hnp
    exact hnp hp
  have hchi : χ p = 0 := by
    refine χ.map_nonunit ?_
    rw [ZMod.isUnit_prime_iff_not_dvd
      (Nat.prime_of_mem_primeFactors hp)]
    exact fun hcon => hcon hpM
  rw [hchi, zero_mul, sub_zero]

/-- Every zero of an added Euler factor lies on the imaginary
axis. -/
theorem added_factor_zero_re (p : ℕ) (hp : p.Prime)
    (χ : DirichletCharacter ℂ M) {s : ℂ}
    (h : (1 : ℂ) - χ p * (p : ℂ) ^ (-s) = 0) : s.re = 0 := by
  have heq : χ p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hchi_ne : χ p ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at heq
    exact zero_ne_one heq
  have hunit : IsUnit ((p : ZMod M)) := by
    by_contra hnu
    exact hchi_ne (χ.map_nonunit hnu)
  have hnorm : ‖χ p‖ = 1 := by
    obtain ⟨u, hu⟩ := hunit
    rw [← hu]
    exact χ.unit_norm_eq_one u
  have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by
    norm_cast
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hnorm2 : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s).re := by
    rw [hcast]
    exact Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (-s)
  have h1 : (p : ℝ) ^ (-s).re = 1 := by
    have h2 := congrArg norm heq
    rw [norm_mul, hnorm, one_mul, hnorm2, norm_one] at h2
    exact h2
  have hplog : (-s).re * Real.log (p : ℝ) = 0 := by
    rw [← Real.log_rpow hp_pos, h1, Real.log_one]
  have hlogp : Real.log (p : ℝ) ≠ 0 := by
    have hlt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    exact ne_of_gt (Real.log_pos hlt)
  rcases mul_eq_zero.mp hplog with h2 | h2
  · have : -s.re = 0 := by simpa using h2
    linarith
  · exact absurd h2 hlogp

/-- `prop:v002-imprimitive`, zero identification: in the strip
`Re s > 0` the induced and the primitive `L`-function vanish
together. -/
theorem imprimitive_strip_zeros (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re)
    (h : χ ≠ 1 ∨ s ≠ 1) :
    LFunction (changeLevel hMN χ) s = 0
      ↔ LFunction χ s = 0 := by
  rw [LFunction_changeLevel hMN χ h, mul_eq_zero]
  constructor
  · rintro (h0 | h0)
    · exact h0
    · exfalso
      obtain ⟨p, hp, hfac⟩ := Finset.prod_eq_zero_iff.mp h0
      have hre := added_factor_zero_re p
        (Nat.prime_of_mem_primeFactors hp) χ hfac
      rw [hre] at hs
      exact lt_irrefl 0 hs
  · exact Or.inl

/-- `prop:v002-imprimitive`, second box: the exact
logarithmic-derivative correction, away from `s = 1`, zeros of
`L(s,χ*)`, and zeros of the added factors. -/
theorem imprimitive_log_deriv (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs1 : s ≠ 1)
    (hL : LFunction χ s ≠ 0)
    (hfac : ∀ p ∈ N.primeFactors,
      (1 : ℂ) - χ p * (p : ℂ) ^ (-s) ≠ 0) :
    -logDeriv (LFunction (changeLevel hMN χ)) s
      = -logDeriv (LFunction χ) s
        - ∑ p ∈ N.primeFactors with ¬p ∣ M,
            (χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s))
              / (1 - χ p * (p : ℂ) ^ (-s)) := by
  classical
  set g : ℂ → ℂ :=
    fun z => ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z))
    with hg
  have hp0 : ∀ p ∈ N.primeFactors, ((p : ℕ) : ℂ) ≠ 0 := by
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hdfac : ∀ p ∈ N.primeFactors,
      DifferentiableAt ℂ
        (fun z => (1 : ℂ) - χ p * (p : ℂ) ^ (-z)) s := by
    intro p hp
    exact (differentiableAt_const (1 : ℂ)).sub
      (((differentiableAt_id.neg).const_cpow
        (.inl (hp0 p hp))).const_mul (χ p))
  have hgdiff : DifferentiableAt ℂ g s :=
    DifferentiableAt.fun_finsetProd fun p hp => hdfac p hp
  have hgne : g s ≠ 0 := Finset.prod_ne_zero_iff.mpr hfac
  have hEE : LFunction (changeLevel hMN χ)
      =ᶠ[nhds s] fun z => LFunction χ z * g z := by
    refine Filter.eventually_of_mem
      (isOpen_compl_singleton.mem_nhds (by simpa using hs1)) ?_
    intro z hz
    exact LFunction_changeLevel hMN χ (.inr (by simpa using hz))
  have hlogeq : logDeriv (LFunction (changeLevel hMN χ)) s
      = logDeriv (fun z => LFunction χ z * g z) s := by
    rw [logDeriv_apply, logDeriv_apply, hEE.deriv_eq,
      hEE.eq_of_nhds]
  have hfactor : ∀ p ∈ N.primeFactors,
      logDeriv (fun z => (1 : ℂ) - χ p * (p : ℂ) ^ (-z)) s
        = (χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s))
            / (1 - χ p * (p : ℂ) ^ (-s)) := by
    intro p hp
    have hlog : ((Real.log (p : ℝ) : ℝ) : ℂ)
        = Complex.log ((p : ℕ) : ℂ) := by
      rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) by
        norm_cast]
      exact Complex.ofReal_log (Nat.cast_nonneg p)
    have hd : HasDerivAt
        (fun z : ℂ => (1 : ℂ) - χ p * (p : ℂ) ^ (-z))
        (-(χ p * ((p : ℂ) ^ (-s) * Complex.log (p : ℂ)
          * (-1)))) s := by
      have h1 : HasDerivAt (fun z : ℂ => -z) (-1) s :=
        (hasDerivAt_id s).neg
      have h2 := h1.const_cpow (c := ((p : ℕ) : ℂ))
        (.inl (hp0 p hp))
      exact (h2.const_mul (χ p)).const_sub 1
    rw [logDeriv_apply, hd.deriv, hlog]
    ring
  have hsub : (∑ p ∈ N.primeFactors with ¬p ∣ M,
        (χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s))
          / (1 - χ p * (p : ℂ) ^ (-s)))
      = ∑ p ∈ N.primeFactors,
        (χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s))
          / (1 - χ p * (p : ℂ) ^ (-s)) := by
    refine Finset.sum_subset (Finset.filter_subset _ _)
      fun p hp hnp => ?_
    have hpM : p ∣ M := by
      simp only [Finset.mem_filter, not_and, not_not] at hnp
      exact hnp hp
    have hchi : χ p = 0 := by
      refine χ.map_nonunit ?_
      rw [ZMod.isUnit_prime_iff_not_dvd
        (Nat.prime_of_mem_primeFactors hp)]
      exact fun hcon => hcon hpM
    rw [hchi]
    simp
  rw [hlogeq, logDeriv_mul s hL hgne
    (differentiableAt_LFunction χ s (.inl hs1)) hgdiff,
    show logDeriv g s = ∑ p ∈ N.primeFactors,
        logDeriv (fun z => (1 : ℂ) - χ p * (p : ℂ) ^ (-z)) s
      from logDeriv_prod hfac hdfac,
    Finset.sum_congr rfl hfactor, hsub]
  ring

end NCG
