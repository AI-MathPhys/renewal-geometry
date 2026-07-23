/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.CurieWeiss
import NCG.Upstream.CWPressure

/-!
# The finite-dimensional Laplace principle for the Curie–Weiss
orientation measure

Covers `thm:cw-laplace-principle` from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* the partition function is a binomial sum over magnetization
  fibres, and the elementary type-counting estimates
  `e^{N s(m_k)}/(N+1) ≤ C(N,k) ≤ e^{N s(m_k)}` sandwich each fibre
  (the lower bound via the mode of the `k/N`-tilted binomial law);
* hence `e^{NΨ(m_k)}/(N+1) ≤ Z_N ≤ (N+1) e^{N sup Ψ}`;
* the pressure converges: `(1/N) log Z_N → sup_{[-1,1]} Ψ_{λ,h}`;
* the magnetization satisfies finite-`N` large-deviation bounds:
  events with pressure at most `L` have measure at most
  `(N+1)² e^{N(L − sup Ψ)}`, and each fibre has measure at least
  `e^{N(Ψ(m_k) − sup Ψ)}/(N+1)²`.
-/

namespace NCG.Upstream

open Finset Filter Real

variable (N : ℕ)

/-! ## Counting configurations by orientation number -/

/-- The number of oriented (`true`) cells. -/
def countTrue (η : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun i => η i = true).card

theorem countTrue_le (η : Fin N → Bool) : countTrue N η ≤ N := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

/-- The magnetization grid point `m_k = (2k − N)/N`. -/
noncomputable def mGrid (k : ℕ) : ℝ := (2 * k - N) / N

theorem magSum_eq_countTrue (η : Fin N → Bool) :
    magSum N η = 2 * (countTrue N η : ℝ) - N := by
  unfold magSum countTrue
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => η i = true) (fun i => spin (η i))]
  have h1 : ∀ i ∈ Finset.univ.filter fun i => η i = true,
      spin (η i) = 1 := by
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
    rfl
  have h2 : ∀ i ∈ Finset.univ.filter fun i => ¬η i = true,
      spin (η i) = -1 := by
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    rw [Bool.not_eq_true] at this
    rw [this]
    rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h3 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i => η i = true)
  rw [Finset.card_univ, Fintype.card_fin] at h3
  have h4 : ((Finset.univ.filter fun i => ¬η i = true).card : ℝ)
      = (N : ℝ) - (countTrue N η : ℝ) := by
    unfold countTrue
    have h5 : (Finset.univ.filter fun i => η i = true).card ≤ N := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      simp
    push_cast [← h3]
    ring
  rw [h4]
  unfold countTrue
  ring

/-- The fibre over orientation number `k` has `C(N,k)` elements. -/
theorem card_countTrue_fiber (k : ℕ) :
    (Finset.univ.filter fun η : Fin N → Bool =>
      countTrue N η = k).card = N.choose k := by
  have hcard : (Finset.powersetCard k
      (Finset.univ : Finset (Fin N))).card = N.choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_bij
    (fun η _ => Finset.univ.filter fun i => η i = true) ?_ ?_ ?_
  · intro η hη
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _,
      (Finset.mem_filter.mp hη).2⟩
  · intro η₁ h₁ η₂ h₂ heq
    funext i
    have hiff : (η₁ i = true) ↔ (η₂ i = true) := by
      constructor
      · intro h
        have : i ∈ Finset.univ.filter fun j => η₁ j = true :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
        rw [heq] at this
        exact (Finset.mem_filter.mp this).2
      · intro h
        have : i ∈ Finset.univ.filter fun j => η₂ j = true :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
        rw [← heq] at this
        exact (Finset.mem_filter.mp this).2
    cases hb₁ : η₁ i <;> cases hb₂ : η₂ i
    · rfl
    · exact absurd (hiff.mpr hb₂) (by rw [hb₁]; simp)
    · exact absurd (hiff.mp hb₁) (by rw [hb₂]; simp)
    · rfl
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    refine ⟨fun i => decide (i ∈ S), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold countTrue
      rw [← hS.2]
      congr 1
      ext i
      simp
    · ext i
      simp

/-- Fibre decomposition of a count-dependent configuration sum. -/
theorem sum_count_fiber (F : ℕ → ℝ) :
    ∑ η : Fin N → Bool, F (countTrue N η)
      = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * F k := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := countTrue N) (t := Finset.range (N + 1))
    (fun η _ => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (countTrue_le N η)))
    (fun η => F (countTrue N η))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl
    (fun η hη => by rw [(Finset.mem_filter.mp hη).2]),
    Finset.sum_const, card_countTrue_fiber, nsmul_eq_mul]

/-! ## The type-counting estimates -/

section TypeBounds

variable {N} (hN : 0 < N)

include hN in
theorem mGrid_mem {k : ℕ} (hk : k ≤ N) :
    mGrid N k ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold mGrid
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  constructor
  · rw [le_div_iff₀ hN']
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  · rw [div_le_one hN']
    have : (k : ℝ) ≤ N := Nat.cast_le.mpr hk
    linarith

include hN in
/-- The entropy–probability identity on interior grid points. -/
theorem exp_entropy_mul (k : ℕ) (hk0 : 0 < k) (hkN : k < N) :
    Real.exp ((N : ℝ) * cwEntropy (mGrid N k))
      * (((k : ℝ) / N) ^ k * (((N : ℝ) - k) / N) ^ (N - k)) = 1 := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hp : (0 : ℝ) < (k : ℝ) / N :=
    div_pos (Nat.cast_pos.mpr hk0) hN'
  have hq : (0 : ℝ) < ((N : ℝ) - k) / N := by
    refine div_pos ?_ hN'
    have : (k : ℝ) < N := Nat.cast_lt.mpr hkN
    linarith
  have hpe : (1 + mGrid N k) / 2 = (k : ℝ) / N := by
    unfold mGrid
    field_simp
    ring
  have hqe : (1 - mGrid N k) / 2 = ((N : ℝ) - k) / N := by
    unfold mGrid
    field_simp
    ring
  have hNs : (N : ℝ) * cwEntropy (mGrid N k)
      = -((k : ℝ) * Real.log ((k : ℝ) / N))
        - ((N : ℝ) - k) * Real.log (((N : ℝ) - k) / N) := by
    unfold cwEntropy
    rw [hpe, hqe]
    unfold Real.negMulLog
    field_simp
    ring
  rw [hNs]
  have hcast : ((N - k : ℕ) : ℝ) = (N : ℝ) - k :=
    Nat.cast_sub hkN.le
  rw [show -((k : ℝ) * Real.log ((k : ℝ) / N))
      - ((N : ℝ) - k) * Real.log (((N : ℝ) - k) / N)
      = -((k : ℝ) * Real.log ((k : ℝ) / N))
        + -(((N - k : ℕ) : ℝ)
          * Real.log (((N : ℝ) - k) / N)) from by
    rw [hcast]; ring]
  rw [Real.exp_add, Real.exp_neg, Real.exp_neg,
    Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log hp, Real.exp_log hq]
  field_simp

/-- Upper type bound: a single binomial term is at most the whole
binomial sum. -/
theorem choose_mul_pow_le_one (k : ℕ) (hk : k ≤ N) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    (N.choose k : ℝ) * (p ^ k * q ^ (N - k)) ≤ 1 := by
  have h1 := add_pow p q N
  rw [hpq, one_pow] at h1
  have h2 : p ^ k * q ^ (N - k) * (N.choose k : ℝ)
      ≤ ∑ m ∈ Finset.range (N + 1),
        p ^ m * q ^ (N - m) * (N.choose m : ℝ) := by
    refine Finset.single_le_sum
      (f := fun m => p ^ m * q ^ (N - m) * (N.choose m : ℝ))
      (fun j _ => by positivity) ?_
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  rw [← h1] at h2
  have h3 : (N.choose k : ℝ) * (p ^ k * q ^ (N - k))
      = p ^ k * q ^ (N - k) * (N.choose k : ℝ) := by ring
  rw [h3]
  exact h2

include hN in
/-- `C(N,k) ≤ e^{N s(m_k)}`. -/
theorem choose_le_exp_entropy (k : ℕ) (hk : k ≤ N) :
    (N.choose k : ℝ)
      ≤ Real.exp ((N : ℝ) * cwEntropy (mGrid N k)) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hm : mGrid N 0 = -1 := by
      unfold mGrid
      rw [Nat.cast_zero, mul_zero, zero_sub, neg_div,
        div_self hN'.ne']
    rw [hm, Nat.choose_zero_right]
    have hs : cwEntropy (-1) = 0 := by
      unfold cwEntropy
      norm_num
    rw [hs, mul_zero, Real.exp_zero]
    norm_num
  rcases eq_or_lt_of_le hk with rfl | hkN
  · have hm : mGrid k k = 1 := by
      unfold mGrid
      rw [show 2 * (k : ℝ) - k = (k : ℝ) from by ring,
        div_self hN'.ne']
    rw [hm, Nat.choose_self]
    have hs : cwEntropy 1 = 0 := by
      unfold cwEntropy
      norm_num
    rw [hs, mul_zero, Real.exp_zero]
    norm_num
  · have hid := exp_entropy_mul hN k hk0 hkN
    have htype := choose_mul_pow_le_one (N := N) k hk
      (p := (k : ℝ) / N) (q := ((N : ℝ) - k) / N)
      (by positivity)
      (by
        have : (k : ℝ) < N := Nat.cast_lt.mpr hkN
        positivity)
      (by field_simp; ring)
    set E := Real.exp ((N : ℝ) * cwEntropy (mGrid N k))
    set B := ((k : ℝ) / N) ^ k * (((N : ℝ) - k) / N) ^ (N - k)
    have hE : (0 : ℝ) < E := Real.exp_pos _
    have hB : (0 : ℝ) < B := by
      have hp : (0 : ℝ) < (k : ℝ) / N :=
        div_pos (Nat.cast_pos.mpr hk0) hN'
      have hq : (0 : ℝ) < ((N : ℝ) - k) / N := by
        refine div_pos ?_ hN'
        have : (k : ℝ) < N := Nat.cast_lt.mpr hkN
        linarith
      positivity
    nlinarith [htype, hid, hE, hB,
      (show (0 : ℝ) ≤ (N.choose k : ℝ) from Nat.cast_nonneg _)]

include hN in
/-- The binomial law tilted at `p = k/N` has its mode at `k`. -/
theorem binom_mode (k : ℕ) (hk : k ≤ N) (j : ℕ) (hj : j ≤ N) :
    (N.choose j : ℝ) * (((k : ℝ) / N) ^ j
      * (((N : ℝ) - k) / N) ^ (N - j))
    ≤ (N.choose k : ℝ) * (((k : ℝ) / N) ^ k
      * (((N : ℝ) - k) / N) ^ (N - k)) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set p : ℝ := (k : ℝ) / N with hp_def
  set q : ℝ := ((N : ℝ) - k) / N with hq_def
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by
    rw [hq_def]
    have : (k : ℝ) ≤ N := Nat.cast_le.mpr hk
    positivity
  set B : ℕ → ℝ := fun j => (N.choose j : ℝ) * (p ^ j * q ^ (N - j))
    with hB_def
  -- the cast ratio identity
  have hratio : ∀ j : ℕ, j < N →
      ((N.choose (j + 1) : ℝ)) * ((j : ℝ) + 1)
        = (N.choose j : ℝ) * ((N : ℝ) - j) := by
    intro j hjN
    have h1 := Nat.choose_succ_right_eq N j
    have h2 : ((N.choose (j + 1) * (j + 1) : ℕ) : ℝ)
        = ((N.choose j * (N - j) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) h1
    push_cast [Nat.cast_sub hjN.le] at h2
    linarith
  -- one step up below the mode
  have hstep_up : ∀ j : ℕ, j < k → B j ≤ B (j + 1) := by
    intro j hjk
    have hjN : j < N := lt_of_lt_of_le hjk hk
    have hkey : ((N : ℝ) - j) * p ≥ ((j : ℝ) + 1) * q := by
      have h3 : ((j : ℝ) + 1) ≤ k := by
        exact_mod_cast Nat.succ_le_of_lt hjk
      have h4 : (N : ℝ) - k ≤ (N : ℝ) - j := by
        have h4a : (j : ℝ) ≤ k := by exact_mod_cast hjk.le
        linarith
      have h5 : (0 : ℝ) ≤ (N : ℝ) - k := by
        have h5a : (k : ℝ) ≤ N := by exact_mod_cast hk
        linarith
      have h6 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hkey0 : ((j : ℝ) + 1) * ((N : ℝ) - k)
          ≤ ((N : ℝ) - j) * k := by nlinarith
      rw [hp_def, hq_def, ge_iff_le, ← mul_div_assoc,
        ← mul_div_assoc]
      exact (div_le_div_iff_of_pos_right hN').mpr hkey0
    -- B (j+1) * (j+1) ≥ B j * (j+1)
    have hpow : q ^ (N - j) = q * q ^ (N - (j + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    have hBj1 : B (j + 1) * ((j : ℝ) + 1)
        = (N.choose j : ℝ) * ((N : ℝ) - j)
          * (p ^ (j + 1) * q ^ (N - (j + 1))) := by
      simp only [hB_def]
      linear_combination
        (p ^ (j + 1) * q ^ (N - (j + 1))) * hratio j hjN
    have hBj : B j * ((j : ℝ) + 1)
        = (N.choose j : ℝ) * (((j : ℝ) + 1)
          * (p ^ j * (q * q ^ (N - (j + 1))))) := by
      simp only [hB_def]
      rw [hpow]
      ring
    have hcompare : B j * ((j : ℝ) + 1)
        ≤ B (j + 1) * ((j : ℝ) + 1) := by
      rw [hBj, hBj1]
      have hc0 : (0 : ℝ) ≤ (N.choose j : ℝ) :=
        Nat.cast_nonneg _
      have hpj : (0 : ℝ) ≤ p ^ j := pow_nonneg hp0 j
      have hqj : (0 : ℝ) ≤ q ^ (N - (j + 1)) :=
        pow_nonneg hq0 _
      have hexp : p ^ (j + 1) = p * p ^ j := by
        rw [pow_succ']
      rw [hexp]
      nlinarith [hkey, mul_nonneg (mul_nonneg hc0 hpj) hqj,
        hc0, hpj, hqj, hp0, hq0]
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    exact le_of_mul_le_mul_right hcompare hj1
  -- one step down above the mode
  have hstep_down : ∀ j : ℕ, k ≤ j → j < N → B (j + 1) ≤ B j := by
    intro j hkj hjN
    have hkey : ((N : ℝ) - j) * p ≤ ((j : ℝ) + 1) * q := by
      have h3 : (k : ℝ) ≤ (j : ℝ) + 1 := by
        have h3a : (k : ℝ) ≤ j := by exact_mod_cast hkj
        linarith
      have h4 : (N : ℝ) - j ≤ (N : ℝ) - k := by
        have h4a : (k : ℝ) ≤ j := by exact_mod_cast hkj
        linarith
      have h5 : (0 : ℝ) ≤ (N : ℝ) - j := by
        have h5a : (j : ℝ) ≤ N := by exact_mod_cast hjN.le
        linarith
      have h6 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hkey0 : ((N : ℝ) - j) * k
          ≤ ((j : ℝ) + 1) * ((N : ℝ) - k) := by nlinarith
      rw [hp_def, hq_def, ← mul_div_assoc, ← mul_div_assoc]
      exact (div_le_div_iff_of_pos_right hN').mpr hkey0
    have hpow : q ^ (N - j) = q * q ^ (N - (j + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    have hBj1 : B (j + 1) * ((j : ℝ) + 1)
        = (N.choose j : ℝ) * ((N : ℝ) - j)
          * (p ^ (j + 1) * q ^ (N - (j + 1))) := by
      simp only [hB_def]
      linear_combination
        (p ^ (j + 1) * q ^ (N - (j + 1))) * hratio j hjN
    have hBj : B j * ((j : ℝ) + 1)
        = (N.choose j : ℝ) * (((j : ℝ) + 1)
          * (p ^ j * (q * q ^ (N - (j + 1))))) := by
      simp only [hB_def]
      rw [hpow]
      ring
    have hcompare : B (j + 1) * ((j : ℝ) + 1)
        ≤ B j * ((j : ℝ) + 1) := by
      rw [hBj, hBj1]
      have hc0 : (0 : ℝ) ≤ (N.choose j : ℝ) :=
        Nat.cast_nonneg _
      have hpj : (0 : ℝ) ≤ p ^ j := pow_nonneg hp0 j
      have hqj : (0 : ℝ) ≤ q ^ (N - (j + 1)) :=
        pow_nonneg hq0 _
      have hexp : p ^ (j + 1) = p * p ^ j := by
        rw [pow_succ']
      rw [hexp]
      nlinarith [hkey, mul_nonneg (mul_nonneg hc0 hpj) hqj,
        hc0, hpj, hqj, hp0, hq0]
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    exact le_of_mul_le_mul_right hcompare hj1
  -- climb to the mode
  have hup : ∀ d : ℕ, ∀ j : ℕ, j + d = k → B j ≤ B k := by
    intro d
    induction d with
    | zero =>
      intro j hj
      rw [← hj, Nat.add_zero]
    | succ e ih =>
      intro j hj
      have hjk : j < k := by omega
      calc B j ≤ B (j + 1) := hstep_up j hjk
        _ ≤ B k := ih (j + 1) (by omega)
  have hdown : ∀ d : ℕ, ∀ j : ℕ, j = k + d → j ≤ N → B j ≤ B k := by
    intro d
    induction d with
    | zero =>
      intro j hj _
      rw [hj, Nat.add_zero]
    | succ e ih =>
      intro j hj hjN
      have hjpos : 0 < j := by omega
      have hstep : B j ≤ B (j - 1) := by
        have h := hstep_down (j - 1) (by omega) (by omega)
        rwa [show j - 1 + 1 = j from by omega] at h
      calc B j ≤ B (j - 1) := hstep
        _ ≤ B k := ih (j - 1) (by omega) (by omega)
  rcases le_total j k with hjk | hkj
  · exact hup (k - j) j (by omega)
  · exact hdown (j - k) j (by omega) hj

include hN in
/-- `e^{N s(m_k)} ≤ (N+1) C(N,k)`, via the mode of the tilted
binomial law. -/
theorem exp_entropy_le_choose (k : ℕ) (hk : k ≤ N) :
    Real.exp ((N : ℝ) * cwEntropy (mGrid N k))
      ≤ ((N : ℝ) + 1) * (N.choose k : ℝ) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hm : mGrid N 0 = -1 := by
      unfold mGrid
      rw [Nat.cast_zero, mul_zero, zero_sub, neg_div,
        div_self hN'.ne']
    rw [hm, Nat.choose_zero_right]
    have hs : cwEntropy (-1) = 0 := by
      unfold cwEntropy
      norm_num
    rw [hs, mul_zero, Real.exp_zero]
    push_cast
    linarith
  rcases eq_or_lt_of_le hk with rfl | hkN
  · have hm : mGrid k k = 1 := by
      unfold mGrid
      rw [show 2 * (k : ℝ) - k = (k : ℝ) from by ring,
        div_self hN'.ne']
    rw [hm, Nat.choose_self]
    have hs : cwEntropy 1 = 0 := by
      unfold cwEntropy
      norm_num
    rw [hs, mul_zero, Real.exp_zero]
    push_cast
    linarith
  · set p : ℝ := (k : ℝ) / N with hp_def
    set q : ℝ := ((N : ℝ) - k) / N with hq_def
    have hp0 : 0 ≤ p := by positivity
    have hq0 : 0 ≤ q := by
      rw [hq_def]
      have : (k : ℝ) ≤ N := Nat.cast_le.mpr hk
      positivity
    have hpq : p + q = 1 := by
      rw [hp_def, hq_def]
      field_simp
      ring
    have hsum : ∑ j ∈ Finset.range (N + 1),
        (N.choose j : ℝ) * (p ^ j * q ^ (N - j)) = 1 := by
      have h1 := add_pow p q N
      rw [hpq, one_pow] at h1
      rw [show (∑ j ∈ Finset.range (N + 1),
          (N.choose j : ℝ) * (p ^ j * q ^ (N - j)))
          = ∑ j ∈ Finset.range (N + 1),
            p ^ j * q ^ (N - j) * (N.choose j : ℝ) from
        Finset.sum_congr rfl fun j _ => by ring]
      exact h1.symm
    have hmode : (1 : ℝ) ≤ ((N : ℝ) + 1)
        * ((N.choose k : ℝ) * (p ^ k * q ^ (N - k))) := by
      have h3 : ∀ j ∈ Finset.range (N + 1),
          (N.choose j : ℝ) * (p ^ j * q ^ (N - j))
            ≤ (N.choose k : ℝ) * (p ^ k * q ^ (N - k)) := by
        intro j hj
        exact binom_mode hN k hk j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      calc (1 : ℝ)
          = ∑ j ∈ Finset.range (N + 1),
            (N.choose j : ℝ) * (p ^ j * q ^ (N - j)) := hsum.symm
        _ ≤ ∑ _j ∈ Finset.range (N + 1),
            (N.choose k : ℝ) * (p ^ k * q ^ (N - k)) :=
            Finset.sum_le_sum h3
        _ = ((N : ℝ) + 1)
            * ((N.choose k : ℝ) * (p ^ k * q ^ (N - k))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hid := exp_entropy_mul hN k hk0 hkN
    rw [← hp_def, ← hq_def] at hid
    set E := Real.exp ((N : ℝ) * cwEntropy (mGrid N k))
    set B := p ^ k * q ^ (N - k)
    have hE : (0 : ℝ) < E := Real.exp_pos _
    have hB0 : (0 : ℝ) ≤ B := by positivity
    -- 1 ≤ (N+1)·C·B and E·B = 1 give E ≤ (N+1)·C
    nlinarith [hmode, hid, hE, hB0,
      (show (0 : ℝ) ≤ (N.choose k : ℝ) from Nat.cast_nonneg _),
      mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ)+1)
        (show (0 : ℝ) ≤ (N.choose k : ℝ) from Nat.cast_nonneg _))
        hB0]

end TypeBounds

/-! ## The partition-function sandwich -/

section Sandwich

variable {N : ℕ} (hN : 0 < N) (lam h : ℝ)

include hN

theorem weight_exponent_eq (k : ℕ) :
    lam / (2 * (N : ℝ)) * (2 * (k : ℝ) - N) ^ 2
      + h * (2 * (k : ℝ) - N)
    = (N : ℝ) * (cwPressure lam h (mGrid N k)
      - cwEntropy (mGrid N k)) := by
  unfold cwPressure mGrid
  have hN' : ((N : ℝ)) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  field_simp
  ring

theorem cwPartition_fiber_eq :
    cwPartition N lam h = ∑ k ∈ Finset.range (N + 1),
      (N.choose k : ℝ) * Real.exp ((N : ℝ)
        * (cwPressure lam h (mGrid N k)
          - cwEntropy (mGrid N k))) := by
  have hw : ∀ η : Fin N → Bool, cwWeight N lam h η
      = Real.exp ((N : ℝ)
        * (cwPressure lam h (mGrid N (countTrue N η))
          - cwEntropy (mGrid N (countTrue N η)))) := by
    intro η
    unfold cwWeight
    rw [magSum_eq_countTrue, ← weight_exponent_eq hN lam h]
  unfold cwPartition
  rw [Finset.sum_congr rfl fun η _ => hw η]
  exact sum_count_fiber N (fun k => Real.exp ((N : ℝ)
    * (cwPressure lam h (mGrid N k) - cwEntropy (mGrid N k))))

/-- Upper Laplace bound: `Z_N ≤ (N+1) e^{N Ψ⋆}`. -/
theorem cwPartition_le {mmax : ℝ}
    (hmax : IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) mmax) :
    cwPartition N lam h
      ≤ ((N : ℝ) + 1) * Real.exp ((N : ℝ)
        * cwPressure lam h mmax) := by
  rw [cwPartition_fiber_eq hN lam h]
  have hterm : ∀ k ∈ Finset.range (N + 1), (N.choose k : ℝ)
      * Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
        - cwEntropy (mGrid N k)))
      ≤ Real.exp ((N : ℝ) * cwPressure lam h mmax) := by
    intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 := choose_le_exp_entropy hN k hkN
    have h2 : cwPressure lam h (mGrid N k)
        ≤ cwPressure lam h mmax := by
      have := hmax (mGrid_mem hN hkN)
      simpa using this
    calc (N.choose k : ℝ) * Real.exp ((N : ℝ)
          * (cwPressure lam h (mGrid N k) - cwEntropy (mGrid N k)))
        ≤ Real.exp ((N : ℝ) * cwEntropy (mGrid N k))
          * Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
            - cwEntropy (mGrid N k))) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp ((N : ℝ) * cwPressure lam h (mGrid N k)) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp ((N : ℝ) * cwPressure lam h mmax) := by
          refine Real.exp_le_exp.mpr ?_
          exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg N)
  calc ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ)
        * Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
          - cwEntropy (mGrid N k)))
      ≤ ∑ _k ∈ Finset.range (N + 1),
        Real.exp ((N : ℝ) * cwPressure lam h mmax) :=
        Finset.sum_le_sum hterm
    _ = ((N : ℝ) + 1) * Real.exp ((N : ℝ)
        * cwPressure lam h mmax) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- Lower Laplace bound: `e^{N Ψ(m_k)}/(N+1) ≤ Z_N` for every grid
point. -/
theorem le_cwPartition (k : ℕ) (hk : k ≤ N) :
    Real.exp ((N : ℝ) * cwPressure lam h (mGrid N k))
      / ((N : ℝ) + 1) ≤ cwPartition N lam h := by
  rw [cwPartition_fiber_eq hN lam h]
  have hterm : Real.exp ((N : ℝ) * cwPressure lam h (mGrid N k))
      / ((N : ℝ) + 1)
      ≤ (N.choose k : ℝ) * Real.exp ((N : ℝ)
        * (cwPressure lam h (mGrid N k)
          - cwEntropy (mGrid N k))) := by
    have h1 := exp_entropy_le_choose hN k hk
    have hsplit : Real.exp ((N : ℝ) * cwPressure lam h (mGrid N k))
        = Real.exp ((N : ℝ) * cwEntropy (mGrid N k))
          * Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
            - cwEntropy (mGrid N k))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit, div_le_iff₀ (by positivity : (0:ℝ) < (N : ℝ) + 1)]
    have hE2 : (0 : ℝ) < Real.exp ((N : ℝ)
        * (cwPressure lam h (mGrid N k)
          - cwEntropy (mGrid N k))) := Real.exp_pos _
    nlinarith [h1, hE2]
  refine le_trans hterm ?_
  refine Finset.single_le_sum (f := fun j => (N.choose j : ℝ)
    * Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N j)
      - cwEntropy (mGrid N j)))) ?_ ?_
  · intro j _
    positivity
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)

end Sandwich

/-! ## The pressure limit -/

theorem tendsto_log_succ_div :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) / N) atTop
      (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h3 := h1.comp h2
  have h4 : Tendsto (fun N : ℕ =>
      2 * (Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1))) atTop
      (nhds 0) := by
    have := h3.const_mul (2 : ℝ)
    simpa using this
  refine squeeze_zero' ?_ ?_ h4
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hlog : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) := by
      refine Real.log_nonneg ?_
      linarith
    exact div_nonneg hlog hN'.le
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hlog : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) := by
      refine Real.log_nonneg ?_
      linarith
    rw [div_le_iff₀ hN']
    have hexp : 2 * (Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1))
        * (N : ℝ)
        = Real.log ((N : ℝ) + 1)
          * (2 * (N : ℝ) / ((N : ℝ) + 1)) := by
      field_simp
    rw [hexp]
    have hfrac : (1 : ℝ) ≤ 2 * (N : ℝ) / ((N : ℝ) + 1) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < (N : ℝ) + 1)]
      linarith
    nlinarith [hlog, hfrac]

/-- **Theorem `thm:cw-laplace-principle` (pressure limit)**:
`(1/N) log Z_{N,λ,h} → sup_{[-1,1]} Ψ_{λ,h}`. -/
theorem cw_pressure_tendsto (lam h : ℝ) {mmax : ℝ}
    (hmem : mmax ∈ Set.Icc (-1 : ℝ) 1)
    (hmax : IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) mmax) :
    Tendsto (fun N : ℕ => Real.log (cwPartition N lam h) / N) atTop
      (nhds (cwPressure lam h mmax)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- uniform continuity modulus on [-1,1]
  have hucont : UniformContinuousOn (cwPressure lam h)
      (Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (continuous_cwPressure lam h).continuousOn
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp hucont
    (ε / 2) (by linarith)
  -- eventually the log correction and grid mesh are small
  have hev1 := (Metric.tendsto_atTop.mp tendsto_log_succ_div)
    (ε / 2) (by linarith)
  obtain ⟨N₁, hN₁⟩ := hev1
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / δ)
  refine ⟨max (max N₁ N₂) 1, fun N hNge => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) hNge)
  have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (le_max_right _ _) hNge)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hNge)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hZpos := cwPartition_pos N lam h
  -- choose the grid point below mmax
  set k : ℕ := ⌊(1 + mmax) / 2 * N⌋₊ with hk_def
  have hhalf0 : (0 : ℝ) ≤ (1 + mmax) / 2 := by
    have := hmem.1
    linarith
  have hhalf1 : (1 + mmax) / 2 ≤ 1 := by
    have := hmem.2
    linarith
  have hkN : k ≤ N := by
    rw [hk_def]
    refine Nat.floor_le_of_le ?_
    calc (1 + mmax) / 2 * (N : ℝ) ≤ 1 * N := by nlinarith
      _ = (N : ℝ) := one_mul _
  have hkfloor : (1 + mmax) / 2 * (N : ℝ) - 1 < (k : ℝ) := by
    rw [hk_def]
    exact Nat.sub_one_lt_floor _
  have hkfloor2 : (k : ℝ) ≤ (1 + mmax) / 2 * N := by
    rw [hk_def]
    exact Nat.floor_le (by positivity)
  have hgrid_close : |mGrid N k - mmax| ≤ 2 / N := by
    unfold mGrid
    have heq : (2 * (k : ℝ) - N) / N - mmax
        = (2 * (k : ℝ) - N - mmax * N) / N := by
      field_simp
    rw [abs_le, heq]
    constructor
    · rw [neg_le, ← neg_div]
      refine (div_le_div_iff_of_pos_right hN').mpr ?_
      nlinarith [hkfloor2]
    · refine (div_le_div_iff_of_pos_right hN').mpr ?_
      nlinarith [hkfloor]
  have hmesh : (2 : ℝ) / N < δ := by
    rw [div_lt_iff₀ hN']
    have h6 : (2 : ℝ) / δ < N₂ := hN₂
    have h7 : (N₂ : ℝ) ≤ N := Nat.cast_le.mpr hN2
    rw [div_lt_iff₀ hδ0] at h6
    nlinarith
  have hΨclose : |cwPressure lam h (mGrid N k)
      - cwPressure lam h mmax| < ε / 2 := by
    have := hδ (mGrid N k) (mGrid_mem hNpos hkN) mmax hmem
      (by
        rw [Real.dist_eq]
        exact lt_of_le_of_lt hgrid_close hmesh)
    rwa [Real.dist_eq] at this
  have hlogN := hN₁ N hN1
  rw [Real.dist_eq, sub_zero] at hlogN
  have hlogN' : Real.log ((N : ℝ) + 1) / N < ε / 2 :=
    lt_of_abs_lt hlogN
  have hlog0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  -- upper estimate
  have hup := cwPartition_le hNpos lam h hmax
  have hupper : Real.log (cwPartition N lam h) / N
      ≤ cwPressure lam h mmax + Real.log ((N : ℝ) + 1) / N := by
    have h8 := Real.log_le_log hZpos hup
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_exp] at h8
    rw [div_le_iff₀ hN']
    have hdivN : Real.log ((N : ℝ) + 1) / N * N
        = Real.log ((N : ℝ) + 1) := div_mul_cancel₀ _ hN'.ne'
    nlinarith [h8, hdivN]
  -- lower estimate
  have hlo := le_cwPartition hNpos lam h k hkN
  have hlower : cwPressure lam h mmax - ε / 2
      - Real.log ((N : ℝ) + 1) / N
      ≤ Real.log (cwPartition N lam h) / N := by
    have h9 := Real.log_le_log (by positivity) hlo
    rw [Real.log_div (Real.exp_ne_zero _) (by positivity),
      Real.log_exp] at h9
    have h10 : cwPressure lam h mmax - ε / 2
        ≤ cwPressure lam h (mGrid N k) := by
      have := abs_lt.mp hΨclose
      linarith [this.1]
    rw [le_div_iff₀ hN']
    have hdivN : Real.log ((N : ℝ) + 1) / N * N
        = Real.log ((N : ℝ) + 1) := div_mul_cancel₀ _ hN'.ne'
    nlinarith [h9, h10, hdivN, hN'.le]
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith
  · linarith

/-! ## Finite-`N` large-deviation bounds -/

section LDP

variable {N : ℕ} (hN : 0 < N) (lam h : ℝ)

include hN

/-- Fibre decomposition of the measure of a magnetization event. -/
theorem cwProb_fiber (P : ℕ → Prop) [DecidablePred P] :
    ∑ η ∈ Finset.univ.filter
      (fun η : Fin N → Bool => P (countTrue N η)),
        cwMeasure N lam h η
    = (∑ k ∈ (Finset.range (N + 1)).filter P, (N.choose k : ℝ)
        * Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
          - cwEntropy (mGrid N k)))) / cwPartition N lam h := by
  unfold cwMeasure
  rw [← Finset.sum_div]
  congr 1
  have hw : ∀ η : Fin N → Bool, cwWeight N lam h η
      = Real.exp ((N : ℝ)
        * (cwPressure lam h (mGrid N (countTrue N η))
          - cwEntropy (mGrid N (countTrue N η)))) := by
    intro η
    unfold cwWeight
    rw [magSum_eq_countTrue, ← weight_exponent_eq hN lam h]
  rw [Finset.sum_congr rfl fun η hη => hw η]
  rw [Finset.sum_filter, Finset.sum_filter]
  have hstep := sum_count_fiber N (fun k => if P k then
    Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
      - cwEntropy (mGrid N k))) else 0)
  rw [show (∑ η : Fin N → Bool, if P (countTrue N η) then
      Real.exp ((N : ℝ)
        * (cwPressure lam h (mGrid N (countTrue N η))
          - cwEntropy (mGrid N (countTrue N η)))) else 0)
    = ∑ η : Fin N → Bool, (fun k => if P k then
      Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
        - cwEntropy (mGrid N k))) else 0) (countTrue N η) from rfl]
  rw [hstep]
  refine Finset.sum_congr rfl fun k _ => ?_
  split
  · rfl
  · rw [mul_zero]

/-- **Theorem `thm:cw-laplace-principle` (upper large-deviation
bound)**: an event on which the pressure is at most `L` has measure
at most `(N+1)² e^{N(L − Ψ(m_{k₀}))}` for every reference grid
point `k₀`. -/
theorem cw_ldp_upper (P : ℕ → Prop) [DecidablePred P] (L : ℝ)
    (hL : ∀ k ≤ N, P k → cwPressure lam h (mGrid N k) ≤ L)
    (k₀ : ℕ) (hk₀ : k₀ ≤ N) :
    ∑ η ∈ Finset.univ.filter
      (fun η : Fin N → Bool => P (countTrue N η)),
        cwMeasure N lam h η
    ≤ ((N : ℝ) + 1) ^ 2 * Real.exp ((N : ℝ)
        * (L - cwPressure lam h (mGrid N k₀))) := by
  rw [cwProb_fiber hN lam h P]
  have hnum : ∑ k ∈ (Finset.range (N + 1)).filter P,
      (N.choose k : ℝ) * Real.exp ((N : ℝ)
        * (cwPressure lam h (mGrid N k) - cwEntropy (mGrid N k)))
      ≤ ((N : ℝ) + 1) * Real.exp ((N : ℝ) * L) := by
    have hterm : ∀ k ∈ (Finset.range (N + 1)).filter P,
        (N.choose k : ℝ) * Real.exp ((N : ℝ)
          * (cwPressure lam h (mGrid N k) - cwEntropy (mGrid N k)))
        ≤ Real.exp ((N : ℝ) * L) := by
      intro k hk
      have hkmem := Finset.mem_filter.mp hk
      have hkN : k ≤ N :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hkmem.1)
      have h1 := choose_le_exp_entropy hN k hkN
      have h2 := hL k hkN hkmem.2
      calc (N.choose k : ℝ) * Real.exp ((N : ℝ)
            * (cwPressure lam h (mGrid N k)
              - cwEntropy (mGrid N k)))
          ≤ Real.exp ((N : ℝ) * cwEntropy (mGrid N k))
            * Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
              - cwEntropy (mGrid N k))) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = Real.exp ((N : ℝ)
            * cwPressure lam h (mGrid N k)) := by
            rw [← Real.exp_add]
            congr 1
            ring
        _ ≤ Real.exp ((N : ℝ) * L) := by
            refine Real.exp_le_exp.mpr ?_
            exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg N)
    calc ∑ k ∈ (Finset.range (N + 1)).filter P,
          (N.choose k : ℝ) * Real.exp ((N : ℝ)
            * (cwPressure lam h (mGrid N k)
              - cwEntropy (mGrid N k)))
        ≤ ∑ _k ∈ (Finset.range (N + 1)).filter P,
          Real.exp ((N : ℝ) * L) := Finset.sum_le_sum hterm
      _ ≤ ((N : ℝ) + 1) * Real.exp ((N : ℝ) * L) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have := Finset.card_filter_le (Finset.range (N + 1)) P
          calc (((Finset.range (N + 1)).filter P).card : ℝ)
              ≤ ((Finset.range (N + 1)).card : ℝ) :=
                Nat.cast_le.mpr this
            _ = ((N : ℝ) + 1) := by
                rw [Finset.card_range]
                push_cast
                ring
  have hden := le_cwPartition hN lam h k₀ hk₀
  have hden0 : (0 : ℝ) < Real.exp ((N : ℝ)
      * cwPressure lam h (mGrid N k₀)) / ((N : ℝ) + 1) := by
    positivity
  calc (∑ k ∈ (Finset.range (N + 1)).filter P, (N.choose k : ℝ)
        * Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
          - cwEntropy (mGrid N k)))) / cwPartition N lam h
      ≤ (((N : ℝ) + 1) * Real.exp ((N : ℝ) * L))
        / (Real.exp ((N : ℝ) * cwPressure lam h (mGrid N k₀))
          / ((N : ℝ) + 1)) := by
        refine div_le_div₀ (by positivity) hnum hden0 hden
    _ = ((N : ℝ) + 1) ^ 2 * Real.exp ((N : ℝ)
        * (L - cwPressure lam h (mGrid N k₀))) := by
        have hsplit2 : Real.exp ((N : ℝ)
            * (L - cwPressure lam h (mGrid N k₀)))
            = Real.exp ((N : ℝ) * L)
              / Real.exp ((N : ℝ)
                * cwPressure lam h (mGrid N k₀)) := by
          rw [← Real.exp_sub]
          congr 1
          ring
        rw [hsplit2, div_div_eq_mul_div]
        field_simp [Real.exp_ne_zero]

/-- **Theorem `thm:cw-laplace-principle` (lower large-deviation
bound)**: each magnetization fibre has measure at least
`e^{N(Ψ(m_k) − Ψ⋆)}/(N+1)²`. -/
theorem cw_ldp_lower (k : ℕ) (hk : k ≤ N) {mmax : ℝ}
    (hmax : IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) mmax) :
    Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
      - cwPressure lam h mmax)) / ((N : ℝ) + 1) ^ 2
    ≤ ∑ η ∈ Finset.univ.filter
      (fun η : Fin N → Bool => countTrue N η = k),
        cwMeasure N lam h η := by
  have hgoal_eq : (∑ η ∈ Finset.univ.filter
      (fun η : Fin N → Bool => countTrue N η = k),
        cwMeasure N lam h η)
      = (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j = k),
          (N.choose j : ℝ) * Real.exp ((N : ℝ)
            * (cwPressure lam h (mGrid N j)
              - cwEntropy (mGrid N j)))) / cwPartition N lam h :=
    cwProb_fiber hN lam h (fun j => j = k)
  rw [hgoal_eq]
  have hnum : Real.exp ((N : ℝ) * cwPressure lam h (mGrid N k))
      / ((N : ℝ) + 1)
      ≤ ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j = k),
        (N.choose j : ℝ) * Real.exp ((N : ℝ)
          * (cwPressure lam h (mGrid N j)
            - cwEntropy (mGrid N j))) := by
    have hfilter : (Finset.range (N + 1)).filter (fun j => j = k)
        = {k} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range,
        Finset.mem_singleton]
      constructor
      · exact fun hj => hj.2
      · intro hj
        exact ⟨by omega, hj⟩
    rw [hfilter, Finset.sum_singleton]
    have h1 := exp_entropy_le_choose hN k hk
    have hsplit : Real.exp ((N : ℝ)
        * cwPressure lam h (mGrid N k))
        = Real.exp ((N : ℝ) * cwEntropy (mGrid N k))
          * Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
            - cwEntropy (mGrid N k))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit, div_le_iff₀ (by positivity : (0:ℝ) < (N : ℝ) + 1)]
    have hE2 : (0 : ℝ) < Real.exp ((N : ℝ)
        * (cwPressure lam h (mGrid N k)
          - cwEntropy (mGrid N k))) := Real.exp_pos _
    nlinarith [h1, hE2]
  have hden := cwPartition_le hN lam h hmax
  have hZpos := cwPartition_pos N lam h
  calc Real.exp ((N : ℝ) * (cwPressure lam h (mGrid N k)
        - cwPressure lam h mmax)) / ((N : ℝ) + 1) ^ 2
      = (Real.exp ((N : ℝ) * cwPressure lam h (mGrid N k))
          / ((N : ℝ) + 1))
        / (((N : ℝ) + 1) * Real.exp ((N : ℝ)
          * cwPressure lam h mmax)) := by
        have hsplit2 : Real.exp ((N : ℝ)
            * (cwPressure lam h (mGrid N k)
              - cwPressure lam h mmax))
            = Real.exp ((N : ℝ) * cwPressure lam h (mGrid N k))
              / Real.exp ((N : ℝ) * cwPressure lam h mmax) := by
          rw [← Real.exp_sub]
          congr 1
          ring
        rw [hsplit2, div_div, div_div]
        congr 1
        ring
    _ ≤ (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j = k),
        (N.choose j : ℝ) * Real.exp ((N : ℝ)
          * (cwPressure lam h (mGrid N j)
            - cwEntropy (mGrid N j)))) / cwPartition N lam h := by
        refine div_le_div₀ ?_ hnum (by positivity) hden
        positivity

end LDP



end NCG.Upstream
