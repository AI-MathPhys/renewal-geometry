/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.AffineRadicalReflectionExact

/-!
# The second-order Euler-factor expansion

Analytic machinery for `thm:affine-radical-reflection` (AFF.3): near `z = 0`,

`𝓔_m(z) = z^{k-1} ∏_{p∣m} log p · (1 - (z/2) log r(m) + O_m(z²))`,

with `k = ω(m)` — in particular the singularity at `z = 0` is removable.  The proof
expands each factor `1 - p^{-z} = z log p - (z log p)²/2 + O(z³)` by the exponential
Taylor bound and multiplies the jets by finite induction (`prod_one_sub_exp_jet`).
-/

open Filter Asymptotics

namespace NCG
namespace AffineRadical

/-- Near zero, `z` is bounded. -/
theorem id_isBigO_one : (fun z : ℝ => z) =O[nhds 0] fun _ : ℝ => (1 : ℝ) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  have hev : ∀ᶠ z : ℝ in nhds 0, |z| ≤ 1 := by
    have h1 : Filter.Tendsto (fun z : ℝ => |z|) (nhds 0) (nhds 0) := by
      simpa using continuous_abs.tendsto (0 : ℝ)
    exact h1.eventually_le_const one_pos
  filter_upwards [hev] with z hz
  simpa using hz

/-- The second-order jet of a single factor `1 - e^{-cz}`. -/
theorem one_sub_exp_jet (c : ℝ) :
    (fun z : ℝ => (1 - Real.exp (-(c * z))) - (c * z - (c * z) ^ 2 / 2))
      =O[nhds 0] fun z => z ^ 3 := by
  have hev : ∀ᶠ z : ℝ in nhds 0, |c * z| ≤ 1 := by
    have hc : Filter.Tendsto (fun z : ℝ => |c * z|) (nhds 0) (nhds 0) := by
      have h1 : Filter.Tendsto (fun z : ℝ => c * z) (nhds 0) (nhds 0) := by
        simpa using (tendsto_id :
          Filter.Tendsto (fun z : ℝ => z) (nhds 0) (nhds 0)).const_mul c
      simpa using h1.abs
    exact hc.eventually_le_const one_pos
  rw [isBigO_iff]
  refine ⟨|c| ^ 3, ?_⟩
  filter_upwards [hev] with z hz
  have hb := Real.exp_bound (x := -(c * z)) (by rwa [abs_neg]) (n := 3) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 3, (-(c * z)) ^ m / m.factorial)
      = 1 - c * z + (c * z) ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num
    ring
  rw [hsum] at hb
  have hid : (1 - Real.exp (-(c * z))) - (c * z - (c * z) ^ 2 / 2)
      = -(Real.exp (-(c * z)) - (1 - c * z + (c * z) ^ 2 / 2)) := by ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hid, abs_neg]
  have hconst : ((3 : ℕ).succ : ℝ) / ((3 : ℕ).factorial * 3) ≤ 1 := by norm_num
  calc |Real.exp (-(c * z)) - (1 - c * z + (c * z) ^ 2 / 2)|
      ≤ |(-(c * z))| ^ 3 * (((3 : ℕ).succ : ℝ) / ((3 : ℕ).factorial * 3)) := hb
    _ ≤ |(-(c * z))| ^ 3 * 1 := by
        have h0 : (0 : ℝ) ≤ |(-(c * z))| ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_left hconst h0
    _ = |c| ^ 3 * |z ^ 3| := by
        rw [mul_one, abs_neg, abs_mul, mul_pow, abs_pow z 3]
    _ ≤ |c| ^ 3 * |z ^ 3| := le_refl _

/-- **Finite product of second-order jets**: the product of the factor jets is the
`(k, k+1)`-jet with leading coefficient `∏ c` and subleading `-(∏c)(∑c)/2`. -/
theorem prod_one_sub_exp_jet {ι : Type*} (s : Finset ι) (c : ι → ℝ) :
    (fun z : ℝ => (∏ p ∈ s, (1 - Real.exp (-(c p * z))))
        - ((∏ p ∈ s, c p) * z ^ s.card
          - (∏ p ∈ s, c p) * (∑ p ∈ s, c p) / 2 * z ^ (s.card + 1)))
      =O[nhds 0] fun z => z ^ (s.card + 2) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hfun : (fun z : ℝ => (∏ p ∈ (∅ : Finset ι), (1 - Real.exp (-(c p * z))))
        - ((∏ p ∈ (∅ : Finset ι), c p) * z ^ (∅ : Finset ι).card
          - (∏ p ∈ (∅ : Finset ι), c p) * (∑ p ∈ (∅ : Finset ι), c p) / 2
            * z ^ ((∅ : Finset ι).card + 1))) = fun _ => (0 : ℝ) := by
      funext z
      simp
    rw [hfun]
    exact isBigO_zero _ _
  | insert a s ha ih =>
    set k := s.card with hk
    set C := ∏ p ∈ s, c p with hC
    set S := ∑ p ∈ s, c p with hS
    -- the exact pointwise decomposition into four controlled terms
    have key : ∀ z : ℝ,
        (∏ p ∈ insert a s, (1 - Real.exp (-(c p * z))))
          - ((∏ p ∈ insert a s, c p) * z ^ (insert a s).card
            - (∏ p ∈ insert a s, c p) * (∑ p ∈ insert a s, c p) / 2
              * z ^ ((insert a s).card + 1))
        = (c a ^ 2 * (C * S / 2) / 2) * (z ^ k * z ^ 3)
          + ((c a * z - (c a * z) ^ 2 / 2)
            * ((∏ p ∈ s, (1 - Real.exp (-(c p * z))))
              - (C * z ^ k - C * S / 2 * z ^ (k + 1)))
          + (((1 - Real.exp (-(c a * z))) - (c a * z - (c a * z) ^ 2 / 2))
            * (C * z ^ k - C * S / 2 * z ^ (k + 1))
          + ((1 - Real.exp (-(c a * z))) - (c a * z - (c a * z) ^ 2 / 2))
            * ((∏ p ∈ s, (1 - Real.exp (-(c p * z))))
              - (C * z ^ k - C * S / 2 * z ^ (k + 1))))) := by
      intro z
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
        Finset.card_insert_of_notMem ha]
      rw [show z ^ (k + 1 + 1) = z ^ k * z * z from by rw [pow_succ, pow_succ],
        show z ^ (k + 1) = z ^ k * z from pow_succ z k,
        show z ^ 3 = z * z * z from by ring]
      ring
    -- the four O-estimates
    have hz1 := id_isBigO_one
    have hterm1 : (fun z : ℝ => (c a ^ 2 * (C * S / 2) / 2) * (z ^ k * z ^ 3))
        =O[nhds 0] fun z => z ^ (k + 3) := by
      have hb := (isBigO_refl (fun z : ℝ => z ^ (k + 3)) (nhds 0)).const_mul_left
        (c a ^ 2 * (C * S / 2) / 2)
      refine hb.congr' ?_ EventuallyEq.rfl
      filter_upwards with z
      rw [pow_add]
    have hjet1 : (fun z : ℝ => c a * z - (c a * z) ^ 2 / 2) =O[nhds 0]
        fun z => z := by
      have h1 : (fun z : ℝ => c a * z) =O[nhds 0] fun z => z :=
        (isBigO_refl _ _).const_mul_left _
      have hzz : (fun z : ℝ => z * z) =O[nhds 0] fun z => z := by
        have := hz1.mul (isBigO_refl (fun z : ℝ => z) (nhds 0))
        refine this.congr' EventuallyEq.rfl ?_
        filter_upwards with z
        rw [one_mul]
      have h2 : (fun z : ℝ => (c a * z) ^ 2 / 2) =O[nhds 0] fun z => z := by
        refine (hzz.const_mul_left (c a ^ 2 / 2)).congr' ?_ EventuallyEq.rfl
        filter_upwards with z
        ring
      exact h1.sub h2
    have hJs : (fun z : ℝ => C * z ^ k - C * S / 2 * z ^ (k + 1)) =O[nhds 0]
        fun z => z ^ k := by
      refine ((isBigO_refl (fun z : ℝ => z ^ k) _).const_mul_left C).sub ?_
      have := ((isBigO_refl (fun z : ℝ => z ^ k) (nhds 0)).mul hz1).const_mul_left
        (C * S / 2)
      refine this.congr' ?_ ?_
      · filter_upwards with z
        rw [pow_succ]
      · filter_upwards with z
        rw [mul_one]
    have hEa := one_sub_exp_jet (c a)
    have hT2 : (fun z : ℝ => (c a * z - (c a * z) ^ 2 / 2)
        * ((∏ p ∈ s, (1 - Real.exp (-(c p * z))))
          - (C * z ^ k - C * S / 2 * z ^ (k + 1)))) =O[nhds 0]
        fun z => z ^ (k + 3) := by
      refine (hjet1.mul ih).congr' EventuallyEq.rfl ?_
      filter_upwards with z
      have hzz : z * z ^ (k + 2) = z ^ (k + 3) := by
        rw [pow_succ]
        ring
      rw [hzz]
    have hT3 : (fun z : ℝ => ((1 - Real.exp (-(c a * z))) - (c a * z - (c a * z) ^ 2 / 2))
        * (C * z ^ k - C * S / 2 * z ^ (k + 1))) =O[nhds 0]
        fun z => z ^ (k + 3) := by
      refine (hEa.mul hJs).congr' EventuallyEq.rfl ?_
      filter_upwards with z
      have hzz : z ^ 3 * z ^ k = z ^ (k + 3) := by
        rw [pow_add]
        ring
      rw [hzz]
    have hT4 : (fun z : ℝ => ((1 - Real.exp (-(c a * z))) - (c a * z - (c a * z) ^ 2 / 2))
        * ((∏ p ∈ s, (1 - Real.exp (-(c p * z))))
          - (C * z ^ k - C * S / 2 * z ^ (k + 1)))) =O[nhds 0]
        fun z => z ^ (k + 3) := by
      have h1 := hEa.mul ih
      -- z³ · z^{k+2} = z^{k+3} · z², and z² is bounded near zero
      have h2 : (fun z : ℝ => z ^ 3 * z ^ (k + 2)) =O[nhds 0]
          fun z => z ^ (k + 3) := by
        have hb := (isBigO_refl (fun z : ℝ => z ^ (k + 3)) (nhds 0)).mul
          ((hz1.mul hz1).congr' EventuallyEq.rfl (by filter_upwards with z; rw [one_mul]))
        refine (hb.congr' ?_ ?_)
        · filter_upwards with z
          have hzz : z ^ (k + 3) * (z * z) = z ^ 3 * z ^ (k + 2) := by
            rw [pow_add, pow_add]
            ring
          rw [hzz]
        · filter_upwards with z
          rw [mul_one]
      exact h1.trans h2
    -- assemble
    have hsum := (hterm1.add ((hT2.add (hT3.add hT4))))
    refine (hsum.congr' ?_ ?_)
    · filter_upwards with z
      exact (key z).symm
    · filter_upwards with z
      rw [Finset.card_insert_of_notMem ha]

/-- **AFF.3**: near `z = 0`,
`𝓔_m(z) = (∏ log p) z^{k-1} - (∏ log p)(log r(m)/2) z^k + O_m(z^{k+1})` — the exact
second-order expansion; in particular the singularity at zero is removable. -/
theorem eulerFactor_expansion (m : ℕ) (hm : 1 < m) :
    (fun z : ℝ => eulerFactor m z
        - ((∏ p ∈ m.primeFactors, Real.log p) * z ^ (m.primeFactors.card - 1)
          - (∏ p ∈ m.primeFactors, Real.log p) * Real.log (rad m) / 2
            * z ^ m.primeFactors.card))
      =O[nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ] fun z => z ^ (m.primeFactors.card + 1) := by
  have hk : 1 ≤ m.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hm)
  have hppos : ∀ p ∈ m.primeFactors, (0 : ℝ) < p := fun p hp =>
    Nat.cast_pos.mpr (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))
  have hfac : ∀ (z : ℝ), ∀ p ∈ m.primeFactors,
      (1 : ℝ) - (p : ℝ) ^ (-z) = 1 - Real.exp (-(Real.log (p : ℕ) * z)) := by
    intro z p hp
    rw [Real.rpow_def_of_pos (hppos p hp),
      show Real.log (p : ℕ) * -z = -(Real.log (p : ℕ) * z) from by ring]
  have hlograd : Real.log ((rad m : ℕ) : ℝ)
      = ∑ p ∈ m.primeFactors, Real.log (p : ℕ) := by
    rw [rad]
    push_cast
    exact Real.log_prod fun p hp => (hppos p hp).ne'
  have hbase := prod_one_sub_exp_jet m.primeFactors fun p => Real.log (p : ℕ)
  have hmul := (isBigO_refl (fun z : ℝ => z⁻¹)
    (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ)).mul (hbase.mono nhdsWithin_le_nhds)
  refine hmul.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz
    have hzk : z⁻¹ * z ^ m.primeFactors.card = z ^ (m.primeFactors.card - 1) := by
      have h1 : z ^ m.primeFactors.card = z ^ (m.primeFactors.card - 1) * z := by
        rw [← pow_succ, Nat.sub_add_cancel hk]
      rw [h1, show z⁻¹ * (z ^ (m.primeFactors.card - 1) * z)
        = z ^ (m.primeFactors.card - 1) * (z⁻¹ * z) from by ring,
        inv_mul_cancel₀ hz0, mul_one]
    have hzk1 : z⁻¹ * z ^ (m.primeFactors.card + 1) = z ^ m.primeFactors.card := by
      rw [pow_succ, show z⁻¹ * (z ^ m.primeFactors.card * z)
        = z ^ m.primeFactors.card * (z⁻¹ * z) from by ring,
        inv_mul_cancel₀ hz0, mul_one]
    rw [eulerFactor, Finset.prod_congr rfl (hfac z), hlograd]
    rw [mul_sub]
    congr 1
    rw [mul_sub,
      show z⁻¹ * ((∏ p ∈ m.primeFactors, Real.log (p : ℕ)) * z ^ m.primeFactors.card)
        = (∏ p ∈ m.primeFactors, Real.log (p : ℕ)) * (z⁻¹ * z ^ m.primeFactors.card)
        from by ring,
      show z⁻¹ * ((∏ p ∈ m.primeFactors, Real.log (p : ℕ))
          * (∑ p ∈ m.primeFactors, Real.log (p : ℕ)) / 2
          * z ^ (m.primeFactors.card + 1))
        = (∏ p ∈ m.primeFactors, Real.log (p : ℕ))
          * (∑ p ∈ m.primeFactors, Real.log (p : ℕ)) / 2
          * (z⁻¹ * z ^ (m.primeFactors.card + 1)) from by ring,
      hzk, hzk1]
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz
    rw [pow_succ,
      show z⁻¹ * (z ^ (m.primeFactors.card + 1) * z)
        = z ^ (m.primeFactors.card + 1) * (z⁻¹ * z) from by ring,
      inv_mul_cancel₀ hz0, mul_one]

end AffineRadical
end NCG
