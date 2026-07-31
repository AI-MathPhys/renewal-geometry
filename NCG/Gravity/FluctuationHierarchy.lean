/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The exact expansion-current cumulant hierarchy
  (`cor:expansion-cumulant-hierarchy`, GR_emergence)

The Gallavotti–Cohen symmetry `Λ_B(-𝒜-χ) = Λ_B(χ)` of the
physical-depth pressure forces `Λ_B(-𝒜) = Λ_B(0) = 0`.  If the
pressure is represented by its cumulant Taylor series on the closed
disk `|χ| ≤ |𝒜|`, evaluating at `-𝒜` and peeling the first two
terms yields the boxed hierarchy

  `𝒜·C₁ = Σ_{n≥2} (-1)ⁿ 𝒜ⁿ/n!·Cₙ`,

with `Cₙ = ∂_χⁿΛ_B(0)`, and the entropy-production expansion
`σ_ep = 𝒜C₁` follows by multiplying through.  At the reversible
locus `𝒜 = 0` the symmetry makes `Λ_B` even, so every odd cumulant
vanishes:

* `gc_pressure_vanishes_at_affinity` — `Λ_B(-𝒜) = 0`;
* `cumulant_hierarchy` — the boxed identity;
* `entropy_production_expansion` — the `σ_ep` series;
* `reversible_odd_cumulants_vanish` — odd cumulants vanish for even
  pressures (via `iteratedDeriv_comp_neg`).

The e-fold rescaling `Cₙ^{𝒩} = Cₙ/dⁿ` is definitional in the
manuscript and carries no separate content.
-/

namespace NCG

/-- Under the Gallavotti–Cohen symmetry, the pressure vanishes at the
negated affinity. -/
theorem gc_pressure_vanishes_at_affinity {Lam : ℝ → ℝ} {A : ℝ}
    (hsym : ∀ x, Lam (-A - x) = Lam x) (h0 : Lam 0 = 0) :
    Lam (-A) = 0 := by
  have h := hsym 0
  rw [sub_zero] at h
  rw [h, h0]

/-- `cor:expansion-cumulant-hierarchy` (boxed identity): if the
pressure is represented by its cumulant Taylor series on the closed
affinity disk and satisfies the Gallavotti–Cohen symmetry, then
`𝒜·C₁ = Σ_{n≥0} (-1)ⁿ 𝒜^{n+2}/(n+2)!·C_{n+2}`. -/
theorem cumulant_hierarchy {Lam : ℝ → ℝ} {A : ℝ}
    (hrep : ∀ x : ℝ, |x| ≤ |A| → HasSum
      (fun n : ℕ => iteratedDeriv n Lam 0 / n.factorial * x ^ n)
      (Lam x))
    (hsym : ∀ x, Lam (-A - x) = Lam x) (h0 : Lam 0 = 0) :
    A * iteratedDeriv 1 Lam 0
      = ∑' n : ℕ, (-1 : ℝ) ^ n * A ^ (n + 2) / (n + 2).factorial
          * iteratedDeriv (n + 2) Lam 0 := by
  have hA := gc_pressure_vanishes_at_affinity hsym h0
  have hs := hrep (-A) (by rw [abs_neg])
  rw [hA] at hs
  have hsm := hs.summable
  have ht : (0 : ℝ) = ∑' n : ℕ,
      iteratedDeriv n Lam 0 / n.factorial * (-A) ^ n := hs.tsum_eq.symm
  rw [hsm.tsum_eq_zero_add,
    ((summable_nat_add_iff 1).mpr hsm).tsum_eq_zero_add] at ht
  have hc0 : iteratedDeriv 0 Lam 0 / (Nat.factorial 0) * (-A) ^ 0
      = 0 := by
    rw [iteratedDeriv_zero, h0]
    simp
  rw [hc0] at ht
  have hshift : (∑' n : ℕ, iteratedDeriv (n + 1 + 1) Lam 0
        / (n + 1 + 1).factorial * (-A) ^ (n + 1 + 1))
      = ∑' n : ℕ, (-1 : ℝ) ^ n * A ^ (n + 2) / (n + 2).factorial
          * iteratedDeriv (n + 2) Lam 0 := by
    apply tsum_congr
    intro n
    have h21 : n + 1 + 1 = n + 2 := by omega
    rw [h21, show ((-A) : ℝ) ^ (n + 2) = (-1) ^ (n + 2) * A ^ (n + 2)
      from neg_pow A (n + 2),
      show ((-1 : ℝ)) ^ (n + 2) = (-1) ^ n from by
        rw [pow_add]; norm_num]
    ring
  rw [hshift] at ht
  have h1fac : iteratedDeriv 1 Lam 0 / (Nat.factorial 1) * (-A) ^ 1
      = -(A * iteratedDeriv 1 Lam 0) := by
    simp only [Nat.factorial_one, Nat.cast_one, div_one, pow_one]
    ring
  rw [h1fac] at ht
  linarith [ht]

/-- `cor:expansion-cumulant-hierarchy` (entropy production): the mean
entropy-production rate `σ_ep = 𝒜C₁` expands as
`Σ_{n≥0} (-1)ⁿ 𝒜^{n+3}/(n+2)!·C_{n+2}` — the boxed
`𝒜²C₂/2 - 𝒜³C₃/6 + ⋯` series. -/
theorem entropy_production_expansion {Lam : ℝ → ℝ} {A : ℝ}
    (hrep : ∀ x : ℝ, |x| ≤ |A| → HasSum
      (fun n : ℕ => iteratedDeriv n Lam 0 / n.factorial * x ^ n)
      (Lam x))
    (hsym : ∀ x, Lam (-A - x) = Lam x) (h0 : Lam 0 = 0) :
    A * (A * iteratedDeriv 1 Lam 0)
      = ∑' n : ℕ, (-1 : ℝ) ^ n * A ^ (n + 3) / (n + 2).factorial
          * iteratedDeriv (n + 2) Lam 0 := by
  rw [cumulant_hierarchy hrep hsym h0, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [show n + 3 = n + 2 + 1 from by omega, pow_succ]
  ring

/-- `cor:expansion-cumulant-hierarchy` (reversible locus): at zero
affinity the pressure is even, so every odd cumulant vanishes. -/
theorem reversible_odd_cumulants_vanish {Lam : ℝ → ℝ}
    (hsym : ∀ x, Lam (-x) = Lam x) {n : ℕ} (hodd : Odd n) :
    iteratedDeriv n Lam 0 = 0 := by
  have hfun : (fun x : ℝ => Lam (-x)) = Lam := funext hsym
  have h := iteratedDeriv_comp_neg n Lam (0 : ℝ)
  rw [hfun, neg_zero, smul_eq_mul, hodd.neg_one_pow] at h
  linarith [h]

end NCG
