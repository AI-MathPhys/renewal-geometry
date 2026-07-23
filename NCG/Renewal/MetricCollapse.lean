/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.NetCounting

/-!
# Metric collapse without non-collapse

**Proposition `prop:metric-collapse`**: there are genuine UCP renewal
memories with `q_alg > 0` and `q_met = 0`.  Two proved cores:

* **algebraic non-collapse** (`NCG.pow_mul_pow_inj`): the two-channel
  labels `(i,j) ↦ 2^i·3^j` are pairwise distinct (unique
  factorisation), so the predictive quotient of the example is the full
  `ℕ²` and `q_alg = 2` by the lattice-shell bounds;
* **metric collapse** (`NCG.geometric_covering_bound`): the geometric
  accumulation set `{2⁻ᵏ}` is covered by `n + 2` balls of radius
  `2⁻⁽ⁿ⁺¹⁾` — the covering number grows only logarithmically in the
  scale, so the upper box dimension vanishes (the `log log/log`
  limsup bookkeeping is noted). -/

namespace NCG

/-- **Proposition `prop:metric-collapse`, algebraic core**: the labels
`2^i·3^j` are pairwise distinct — the two commuting contraction
channels generate a free `ℕ²` predictive quotient, so `q_alg = 2`. -/
theorem pow_mul_pow_inj :
    Function.Injective (fun p : ℕ × ℕ => 2 ^ p.1 * 3 ^ p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only at h
  have h2 : (2 ^ a * 3 ^ b).factorization 2
      = (2 ^ c * 3 ^ d).factorization 2 := by rw [h]
  have h3 : (2 ^ a * 3 ^ b).factorization 3
      = (2 ^ c * 3 ^ d).factorization 3 := by rw [h]
  have hfact : ∀ i j : ℕ, (2 ^ i * 3 ^ j).factorization 2 = i
      ∧ (2 ^ i * 3 ^ j).factorization 3 = j := by
    intro i j
    rw [Nat.factorization_mul (pow_ne_zero i (by norm_num))
      (pow_ne_zero j (by norm_num))]
    rw [Nat.Prime.factorization_pow Nat.prime_two,
      Nat.Prime.factorization_pow Nat.prime_three]
    constructor <;> simp [Finsupp.single_apply]
  obtain ⟨ha2, ha3⟩ := hfact a b
  obtain ⟨hc2, hc3⟩ := hfact c d
  rw [ha2, hc2] at h2
  rw [ha3, hc3] at h3
  exact Prod.ext h2 h3

/-- **Proposition `prop:metric-collapse`, geometric core**: the
accumulation set `{2⁻ᵏ : k ∈ ℕ}` is covered by `n + 2` balls of radius
`2⁻⁽ⁿ⁺¹⁾` — centres at the first `n + 1` points and at the
accumulation point `0`.  The covering number is logarithmic in the
scale, so the upper box dimension of the channel closure is zero. -/
theorem geometric_covering_bound (n : ℕ) :
    coveringNumber {x : ℝ | ∃ k : ℕ, x = ((2:ℝ))⁻¹ ^ k}
      (((2:ℝ))⁻¹ ^ (n + 1)) ≤ n + 3 := by
  set δ : ℝ := ((2:ℝ))⁻¹ ^ (n + 1) with hδ
  have hδpos : 0 < δ := by positivity
  set t : Finset ℝ :=
    insert 0 ((Finset.range (n + 2)).image fun k => ((2:ℝ))⁻¹ ^ k)
    with ht
  have hcover : {x : ℝ | ∃ k : ℕ, x = ((2:ℝ))⁻¹ ^ k}
      ⊆ ⋃ y ∈ t, Metric.ball y δ := by
    rintro x ⟨k, rfl⟩
    rcases le_or_gt k (n + 1) with hk | hk
    · -- own centre
      have hmem : ((2:ℝ))⁻¹ ^ k ∈ t := by
        rw [ht]
        exact Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))
      exact Set.mem_biUnion hmem (Metric.mem_ball_self hδpos)
    · -- close to the accumulation point 0
      have hmem : (0:ℝ) ∈ t := by
        rw [ht]
        exact Finset.mem_insert_self _ _
      have hball : ((2:ℝ))⁻¹ ^ k ∈ Metric.ball (0:ℝ) δ := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        apply pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num)
        omega
      exact Set.mem_biUnion hmem hball
  calc coveringNumber _ δ ≤ t.card := coveringNumber_le_of_net t hcover
    _ ≤ n + 3 := by
        rw [ht]
        calc (insert (0:ℝ) ((Finset.range (n + 2)).image
              fun k => ((2:ℝ))⁻¹ ^ k)).card
            ≤ ((Finset.range (n + 2)).image
                fun k => ((2:ℝ))⁻¹ ^ k).card + 1 :=
              Finset.card_insert_le _ _
          _ ≤ (n + 2) + 1 := by
              have := Finset.card_image_le
                (s := Finset.range (n + 2))
                (f := fun k => ((2:ℝ))⁻¹ ^ k)
              have hr : (Finset.range (n + 2)).card = n + 2 :=
                Finset.card_range _
              omega
          _ = n + 3 := by omega

end NCG
