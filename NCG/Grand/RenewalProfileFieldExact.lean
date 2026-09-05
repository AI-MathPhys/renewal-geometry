/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.RenewalProfileWalshExact

/-!
# The concrete renewal continuum profile: the field layer

Second machinery layer for `thm:concrete-renewal-continuum-profile` — the
count-field statements, proved exactly on the finite `m`-cell product law:

* `expect_single` / `expect_pair`: the product-weight marginal factorization
  (independence of distinct cells);
* `count_mean` / `count_var`: `𝔼[N_m] = 6m/11` and the variance
  `Var(N_m) = 30m/121`;
* `density_l2` / `density_lln`: `𝔼[(ρ_m − 6/11)²] = 30/(121m) → 0` — the
  `L²` law of large numbers for the phase density;
* `fluct_second_moment`: the normalized fluctuation field has exact second
  moment `30/121`, uniformly in the volume;
* `chebyshev` / `fluct_tight`: the finite Chebyshev bound makes `F_m`
  uniformly tight, with tail weight at most `(30/121)/R²`;
* `count_nontight`: the raw count `N_m` is nontight — the weight of any
  fixed window vanishes as the volume grows.
-/

open Finset Filter Topology

noncomputable section

namespace NCG
namespace RenewalField

open NCG.RenewalWalsh

variable {m : ℕ}

/-- The `m`-cell product weight. -/
def w (x : Fin m → Fin 2) : ℝ := ∏ i, piw (x i)

/-- Expectation for the product law. -/
def expect (f : (Fin m → Fin 2) → ℝ) : ℝ := ∑ x, w x * f x

/-- The private-phase indicator. -/
def ind : Fin 2 → ℝ := ![0, 1]

/-- The phase count `N_m`. -/
def Ncount (x : Fin m → Fin 2) : ℝ := ∑ i, ind (x i)

theorem piw_nonneg : ∀ b, 0 ≤ piw b := by
  intro b
  fin_cases b <;> norm_num [piw]

theorem w_nonneg (x : Fin m → Fin 2) : 0 ≤ w x :=
  Finset.prod_nonneg fun i _ => piw_nonneg (x i)

theorem cell_ind_mean : ∑ b, piw b * ind b = 6/11 := by
  norm_num [piw, ind, Fin.sum_univ_two]

theorem cell_ind_sq : ∑ b, piw b * (ind b * ind b) = 6/11 := by
  norm_num [piw, ind, Fin.sum_univ_two]

/-- The total product weight is one. -/
theorem weight_total : ∑ x : Fin m → Fin 2, w x = 1 := by
  classical
  unfold w
  rw [← Fintype.piFinset_univ,
    Finset.sum_prod_piFinset Finset.univ (fun _ b => piw b),
    Finset.prod_congr rfl fun i _ => cell_mass, Finset.prod_const_one]

/-- The single-coordinate marginal factorization. -/
theorem expect_single (g : Fin 2 → ℝ) (i0 : Fin m) :
    expect (fun x => g (x i0)) = ∑ b, piw b * g b := by
  classical
  have hmerge : ∀ x : Fin m → Fin 2,
      w x * g (x i0)
        = ∏ i, (piw (x i) * if i = i0 then g (x i) else 1) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i0
      (fun i => g (x i))]
    simp [w]
  calc expect (fun x => g (x i0))
      = ∑ x : Fin m → Fin 2,
          ∏ i, (piw (x i) * if i = i0 then g (x i) else 1) :=
        Finset.sum_congr rfl fun x _ => hmerge x
    _ = ∑ x ∈ Fintype.piFinset
          (fun _ : Fin m => (Finset.univ : Finset (Fin 2))),
          ∏ i, (piw (x i) * if i = i0 then g (x i) else 1) := by
        rw [Fintype.piFinset_univ]
    _ = ∏ i, ∑ b, (piw b * if i = i0 then g b else 1) :=
        Finset.sum_prod_piFinset Finset.univ
          (fun i b => piw b * if i = i0 then g b else 1)
    _ = ∏ i, (if i = i0 then ∑ b, piw b * g b else 1) := by
        have hfact : piw 0 + piw 1 = (1 : ℝ) := by norm_num [piw]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases hi : i = i0
        · simp [hi]
        · simp [hi, hfact]
    _ = ∑ b, piw b * g b := by
        rw [Finset.prod_ite_eq' Finset.univ i0
          (fun _ => ∑ b, piw b * g b)]
        simp

/-- The two-coordinate marginal factorization: independence of distinct
cells. -/
theorem expect_pair (g h : Fin 2 → ℝ) (i0 j0 : Fin m) (hij : i0 ≠ j0) :
    expect (fun x => g (x i0) * h (x j0))
      = (∑ b, piw b * g b) * (∑ b, piw b * h b) := by
  classical
  have hcollapse : ∀ (c d : ℝ),
      ∏ i : Fin m, (if i = i0 then c else if i = j0 then d else 1)
        = c * d := by
    intro c d
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
      if_pos rfl,
      ← Finset.mul_prod_erase (Finset.univ.erase i0) _
        (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j0⟩),
      if_neg (Ne.symm hij), if_pos rfl]
    have hrest : ∀ i ∈ (Finset.univ.erase i0).erase j0,
        (if i = i0 then c else if i = j0 then d else 1) = 1 := by
      intro i hi
      have hi1 := (Finset.mem_erase.mp hi).1
      have hi2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      rw [if_neg hi2, if_neg hi1]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const_one, mul_one]
  have hmerge : ∀ x : Fin m → Fin 2,
      w x * (g (x i0) * h (x j0))
        = ∏ i, (piw (x i) *
            (if i = i0 then g (x i) else if i = j0 then h (x i) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib]
    have hsplit : ∏ i, (if i = i0 then g (x i)
        else if i = j0 then h (x i) else 1) = g (x i0) * h (x j0) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
        if_pos rfl,
        ← Finset.mul_prod_erase (Finset.univ.erase i0) _
          (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j0⟩),
        if_neg (Ne.symm hij), if_pos rfl]
      have hrest : ∀ i ∈ (Finset.univ.erase i0).erase j0,
          (if i = i0 then g (x i) else if i = j0 then h (x i) else 1) = 1 := by
        intro i hi
        have hi1 := (Finset.mem_erase.mp hi).1
        have hi2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        rw [if_neg hi2, if_neg hi1]
      rw [Finset.prod_congr rfl hrest, Finset.prod_const_one, mul_one]
    rw [hsplit, w]
  calc expect (fun x => g (x i0) * h (x j0))
      = ∑ x : Fin m → Fin 2,
          ∏ i, (piw (x i) *
            (if i = i0 then g (x i) else if i = j0 then h (x i) else 1)) :=
        Finset.sum_congr rfl fun x _ => hmerge x
    _ = ∑ x ∈ Fintype.piFinset
          (fun _ : Fin m => (Finset.univ : Finset (Fin 2))),
          ∏ i, (piw (x i) *
            (if i = i0 then g (x i) else if i = j0 then h (x i) else 1)) := by
        rw [Fintype.piFinset_univ]
    _ = ∏ i, ∑ b, (piw b *
          (if i = i0 then g b else if i = j0 then h b else 1)) :=
        Finset.sum_prod_piFinset Finset.univ
          (fun i b => piw b *
            (if i = i0 then g b else if i = j0 then h b else 1))
    _ = ∏ i, (if i = i0 then ∑ b, piw b * g b
          else if i = j0 then ∑ b, piw b * h b else 1) := by
        have hfact : piw 0 + piw 1 = (1 : ℝ) := by norm_num [piw]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases hi : i = i0
        · simp [hi]
        · by_cases hj : i = j0
          · simp [hj]
          · simp [hi, hj, hfact]
    _ = (∑ b, piw b * g b) * (∑ b, piw b * h b) := hcollapse _ _

/-- **The count mean**: `𝔼[N_m] = 6m/11`. -/
theorem count_mean : expect (Ncount (m := m)) = m * (6/11) := by
  calc expect (Ncount (m := m))
      = ∑ x : Fin m → Fin 2, ∑ i, w x * ind (x i) :=
        Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _
    _ = ∑ i : Fin m, ∑ x : Fin m → Fin 2, w x * ind (x i) :=
        Finset.sum_comm
    _ = ∑ _i : Fin m, (6/11 : ℝ) :=
        Finset.sum_congr rfl fun i _ =>
          (expect_single ind i).trans cell_ind_mean
    _ = m * (6/11) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

/-- **The count second moment**. -/
theorem count_sq : expect (fun x : Fin m → Fin 2 => Ncount x * Ncount x)
    = m * (6/11) + ((m : ℝ)^2 - m) * (6/11)^2 := by
  classical
  calc expect (fun x : Fin m → Fin 2 => Ncount x * Ncount x)
      = ∑ x : Fin m → Fin 2, w x * (Ncount x * Ncount x) := rfl
    _ = ∑ x : Fin m → Fin 2, ∑ i, ∑ j, w x * (ind (x i) * ind (x j)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [show Ncount x * Ncount x
            = ∑ i, ∑ j, ind (x i) * ind (x j) by
          rw [Ncount, Finset.sum_mul_sum]]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    _ = ∑ i : Fin m, ∑ j : Fin m,
          ∑ x : Fin m → Fin 2, w x * (ind (x i) * ind (x j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : Fin m, ∑ j : Fin m,
          (if i = j then (6/11 : ℝ) else (6/11) * (6/11)) := by
        refine Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => ?_
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl]
          exact (expect_single (fun b => ind b * ind b) i).trans cell_ind_sq
        · rw [if_neg hij]
          have h := expect_pair ind ind i j hij
          rw [cell_ind_mean] at h
          exact h
    _ = m * (6/11) + ((m : ℝ)^2 - m) * (6/11)^2 := by
        have hrow : ∀ i : Fin m,
            ∑ j : Fin m, (if i = j then (6/11 : ℝ) else (6/11) * (6/11))
              = 6/11 + ((m : ℝ) - 1) * ((6/11) * (6/11)) := by
          intro i
          have hm1 : 1 ≤ m := i.pos
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
            if_pos rfl]
          congr 1
          rw [Finset.sum_congr rfl (fun j hj =>
            if_neg (Ne.symm (Finset.mem_erase.mp hj).1)),
            Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          congr 1
          push_cast [hm1]
          ring
        rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The boxed count variance**: `Var(N_m) = 30m/121`. -/
theorem count_var :
    expect (fun x : Fin m → Fin 2 => (Ncount x - m * (6/11))^2)
      = m * (30/121) := by
  have hunfold : expect (fun x : Fin m → Fin 2 => (Ncount x - m * (6/11))^2)
      = ∑ x : Fin m → Fin 2, w x * (Ncount x - m * (6/11))^2 := rfl
  rw [hunfold]
  have hexp : ∀ x : Fin m → Fin 2,
      w x * (Ncount x - m * (6/11))^2
        = w x * (Ncount x * Ncount x)
          - (2 * ((m : ℝ) * (6/11))) * (w x * Ncount x)
          + ((m : ℝ) * (6/11))^2 * w x := by
    intro x
    ring
  rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ x : Fin m → Fin 2, w x * (Ncount x * Ncount x)
      = m * (6/11) + ((m : ℝ)^2 - m) * (6/11)^2 := count_sq
  have h2 : ∑ x : Fin m → Fin 2, w x * Ncount x = m * (6/11) := count_mean
  rw [h1, h2, weight_total]
  ring

/-- **The `L²` law of large numbers for the phase density**:
`𝔼[(ρ_m − 6/11)²] = 30/(121m)`. -/
theorem density_l2 (hm : 0 < m) :
    expect (fun x : Fin m → Fin 2 => (Ncount x / m - 6/11)^2)
      = 30 / (121 * m) := by
  have hunfold : expect (fun x : Fin m → Fin 2 => (Ncount x / m - 6/11)^2)
      = ∑ x : Fin m → Fin 2, w x * (Ncount x / m - 6/11)^2 := rfl
  rw [hunfold]
  have hc : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hpt : ∀ x : Fin m → Fin 2,
      (Ncount x / m - 6/11)^2
        = (Ncount x - m * (6/11))^2 * ((m : ℝ)^2)⁻¹ := by
    intro x
    field_simp
  rw [Finset.sum_congr rfl fun x _ => by rw [hpt x]]
  rw [Finset.sum_congr rfl fun x _ =>
    (mul_assoc (w x) _ (((m : ℝ)^2)⁻¹)).symm]
  have hv : ∑ x : Fin m → Fin 2, w x * (Ncount x - m * (6/11))^2
      = (m : ℝ) * (30/121) := count_var
  rw [← Finset.sum_mul, hv]
  field_simp

/-- The density LLN rate vanishes with the volume. -/
theorem density_lln :
    Tendsto (fun m : ℕ => (30 : ℝ) / (121 * m)) atTop (𝓝 0) := by
  have h : (fun m : ℕ => (30 : ℝ) / (121 * m))
      = fun m : ℕ => (30 / 121 : ℝ) / m := by
    funext m
    exact (div_div 30 121 (m : ℝ)).symm
  rw [h]
  exact tendsto_const_div_atTop_nhds_zero_nat _

/-- **The normalized fluctuation second moment is exactly `30/121`**,
uniformly in the volume. -/
theorem fluct_second_moment (hm : 0 < m) :
    expect (fun x : Fin m → Fin 2 =>
      ((Ncount x - m * (6/11)) / Real.sqrt m)^2) = 30/121 := by
  have hunfold : expect (fun x : Fin m → Fin 2 =>
      ((Ncount x - m * (6/11)) / Real.sqrt m)^2)
      = ∑ x : Fin m → Fin 2,
          w x * ((Ncount x - m * (6/11)) / Real.sqrt m)^2 := rfl
  rw [hunfold]
  have hc : (0 : ℝ) < m := by exact_mod_cast hm
  have hpt : ∀ x : Fin m → Fin 2,
      ((Ncount x - m * (6/11)) / Real.sqrt m)^2
        = (Ncount x - m * (6/11))^2 * ((m : ℝ))⁻¹ := by
    intro x
    rw [div_pow, Real.sq_sqrt hc.le, div_eq_mul_inv]
  rw [Finset.sum_congr rfl fun x _ => by rw [hpt x]]
  rw [Finset.sum_congr rfl fun x _ =>
    (mul_assoc (w x) _ (((m : ℝ))⁻¹)).symm]
  have hv : ∑ x : Fin m → Fin 2, w x * (Ncount x - m * (6/11))^2
      = (m : ℝ) * (30/121) := count_var
  rw [← Finset.sum_mul, hv]
  field_simp

/-- **The finite Chebyshev bound** for the product law. -/
theorem chebyshev (f : (Fin m → Fin 2) → ℝ) (R : ℝ) (hR : 0 < R) :
    ∑ x ∈ Finset.univ.filter (fun x => R ≤ |f x|), w x
      ≤ expect (fun x => f x ^ 2) / R ^ 2 := by
  have hle : ∀ x ∈ Finset.univ.filter
      (fun x : Fin m → Fin 2 => R ≤ |f x|),
      w x ≤ w x * f x ^ 2 / R ^ 2 := by
    intro x hx
    have hfx := (Finset.mem_filter.mp hx).2
    have hf2 : R ^ 2 ≤ f x ^ 2 := by
      nlinarith [abs_nonneg (f x), sq_abs (f x)]
    have hw := w_nonneg x
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc ∑ x ∈ Finset.univ.filter (fun x => R ≤ |f x|), w x
      ≤ ∑ x ∈ Finset.univ.filter (fun x => R ≤ |f x|),
          w x * f x ^ 2 / R ^ 2 := Finset.sum_le_sum hle
    _ ≤ ∑ x : Fin m → Fin 2, w x * f x ^ 2 / R ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun x _ _ =>
            div_nonneg (mul_nonneg (w_nonneg x) (sq_nonneg _))
              (sq_nonneg R)
    _ = expect (fun x => f x ^ 2) / R ^ 2 := by
        rw [← Finset.sum_div]
        rfl

/-- **Uniform tightness of the fluctuation field**: the tail weight of `F_m`
beyond `R` is at most `(30/121)/R²`, uniformly in the volume. -/
theorem fluct_tight (hm : 0 < m) (R : ℝ) (hR : 0 < R) :
    ∑ x ∈ Finset.univ.filter
      (fun x : Fin m → Fin 2 =>
        R ≤ |(Ncount x - m * (6/11)) / Real.sqrt m|), w x
      ≤ (30/121) / R ^ 2 := by
  calc ∑ x ∈ Finset.univ.filter (fun x : Fin m → Fin 2 =>
        R ≤ |(Ncount x - m * (6/11)) / Real.sqrt m|), w x
      ≤ expect (fun x : Fin m → Fin 2 =>
          ((Ncount x - m * (6/11)) / Real.sqrt m) ^ 2) / R ^ 2 :=
        chebyshev _ R hR
    _ = (30/121) / R ^ 2 := by rw [fluct_second_moment hm]

/-- **Nontightness of the raw count**: the weight of any fixed window
vanishes as the volume grows. -/
theorem count_nontight (R : ℝ) :
    Tendsto (fun m : ℕ => ∑ x ∈ Finset.univ.filter
      (fun x : Fin m → Fin 2 => Ncount x ≤ R), w x) atTop (𝓝 0) := by
  have hub : ∀ᶠ m : ℕ in atTop,
      ∑ x ∈ Finset.univ.filter
        (fun x : Fin m → Fin 2 => Ncount x ≤ R), w x
        ≤ (30 * 121 / 9 : ℝ) / m := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (11 * |R| / 3) + 1)]
      with m hm
    have hm0 : 0 < m := lt_of_lt_of_le (Nat.succ_pos _) hm
    have hmc : (0 : ℝ) < m := by exact_mod_cast hm0
    have hRm : |R| ≤ 3 * m / 11 := by
      have h1 : (11 * |R| / 3 : ℝ) ≤ Nat.ceil (11 * |R| / 3) :=
        Nat.le_ceil _
      have h2 : (Nat.ceil (11 * |R| / 3) : ℝ) + 1 ≤ m := by
        exact_mod_cast hm
      nlinarith
    have hthr : (0 : ℝ) < 3 * m / 11 := by positivity
    have hsub : Finset.univ.filter
        (fun x : Fin m → Fin 2 => Ncount x ≤ R)
        ⊆ Finset.univ.filter
          (fun x : Fin m → Fin 2 =>
            3 * m / 11 ≤ |Ncount x - m * (6/11)|) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      have hxle : Ncount x ≤ R := hx.2
      have hR' : R ≤ |R| := le_abs_self R
      have hmean : Ncount x - m * (6/11) ≤ -(3 * m / 11) := by
        nlinarith
      calc (3 * m / 11 : ℝ) ≤ -(Ncount x - m * (6/11)) := by nlinarith
        _ ≤ |Ncount x - m * (6/11)| := neg_le_abs _
    calc ∑ x ∈ Finset.univ.filter (fun x : Fin m → Fin 2 =>
          Ncount x ≤ R), w x
        ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin m → Fin 2 =>
            3 * m / 11 ≤ |Ncount x - m * (6/11)|), w x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            fun x _ _ => w_nonneg x
      _ ≤ expect (fun x : Fin m → Fin 2 => (Ncount x - m * (6/11)) ^ 2)
            / (3 * m / 11) ^ 2 := chebyshev _ _ hthr
      _ = (m * (30/121)) / (3 * m / 11) ^ 2 := by rw [count_var]
      _ = (30 * 121 / 9 : ℝ) / m / 121 := by
          field_simp
          ring
      _ ≤ (30 * 121 / 9 : ℝ) / m := by
          have hpos : (0 : ℝ) ≤ (30 * 121 / 9 : ℝ) / m := by positivity
          nlinarith
  have hlb : ∀ᶠ m : ℕ in atTop,
      (0 : ℝ) ≤ ∑ x ∈ Finset.univ.filter
        (fun x : Fin m → Fin 2 => Ncount x ≤ R), w x :=
    Eventually.of_forall fun m =>
      Finset.sum_nonneg fun x _ => w_nonneg x
  have hzero : Tendsto (fun m : ℕ => (30 * 121 / 9 : ℝ) / m)
      atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  exact squeeze_zero' hlb hub hzero

end RenewalField
end NCG

end
