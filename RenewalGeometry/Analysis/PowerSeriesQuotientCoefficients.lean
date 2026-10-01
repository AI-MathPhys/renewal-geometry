/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Coefficients of `v = D⁻¹ χ` and pole tests for a Laurent defect

Infrastructure for `thm:supp-finite-acc-coefficients` (emergent-spacetime manuscript).

* `coeff_recursion_of_mul_eq` (Cauchy-product recursion): in formal power series over an
  arbitrary (noncommutative) ring `A`, if `D * v = χ` then for every `j`,
  `D₀ v_j = χ_j - ∑_{i=1}^{j} D_i v_{j-i}` (`eq:supp-finite-acc-recursion`);
  `coeff_eq_of_mul_eq_of_isUnit`: when `D₀` is a unit, `v_j = D₀⁻¹ (χ_j - ∑ D_i v_{j-i})`, so all
  coefficients are obtained with the single inverse `D₀⁻¹`; `coeff_eq_zero_of_mul_eq` records the
  simplification `χ₀ = χ₁ = χ₂ = 0 ⇒ v₀ = v₁ = v₂ = 0, v₃ = D₀⁻¹ χ₃`.
* `tendsto_laurent_iff` (pole test): a function
  `e(a) = a⁻³ c₀ + a⁻² c₁ + a⁻¹ c₂ + c₃ + r(a)` with `r(a) → 0` has a finite limit at `0`
  (along `a ≠ 0`) iff `c₀ = c₁ = c₂ = 0`, and then the limit is `c₃`.
* `defect_tendsto_iff`: for `v` with a power series at `0` (coefficients `v_j`) and
  `θ(a) = ∑_{k=-3}^{0} a^k θ_k + ρ(a)`, `ρ → 0`, the defect `-a⁻³ p v(a) - θ(a)` has a finite
  limit iff `p v_j + θ_{j-3} = 0` for `j < 3`, and its value is `-p v₃ - θ₀`
  (`eq:supp-finite-acc-poles`, `eq:supp-finite-acc-verdict`).
-/

open Filter Finset
open scoped Topology

namespace RenewalGeometry

namespace PowerSeriesQuotient

/-! ### The Cauchy-product recursion -/

section Recursion

variable {A : Type*} [Ring A]

/-- **Cauchy-product recursion** (`eq:supp-finite-acc-recursion`).  If `D * v = χ` in `A⟦X⟧`,
then `D₀ v_j = χ_j - ∑_{i ∈ (0, j]} D_i v_{j-i}`. -/
theorem coeff_recursion_of_mul_eq {D v χ : PowerSeries A} (h : D * v = χ) (j : ℕ) :
    PowerSeries.coeff 0 D * PowerSeries.coeff j v =
      PowerSeries.coeff j χ -
        ∑ i ∈ Ioc 0 j, PowerSeries.coeff i D * PowerSeries.coeff (j - i) v := by
  rw [← h, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i k => PowerSeries.coeff i D * PowerSeries.coeff k v)]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos j)]
  simp only [Nat.sub_zero]
  have : Ico (0 + 1) (j + 1) = Ioc 0 j := by
    ext i; simp [Nat.lt_succ_iff]; omega
  rw [this]
  abel

/-- With `D₀` a unit, every coefficient of `v` is computed by the recursion using only `D₀⁻¹`. -/
theorem coeff_eq_of_mul_eq_of_isUnit {D v χ : PowerSeries A} (h : D * v = χ)
    (hD : IsUnit (PowerSeries.coeff 0 D)) (j : ℕ) :
    PowerSeries.coeff j v = hD.unit⁻¹ *
      (PowerSeries.coeff j χ -
        ∑ i ∈ Ioc 0 j, PowerSeries.coeff i D * PowerSeries.coeff (j - i) v) := by
  rw [← coeff_recursion_of_mul_eq h j, ← mul_assoc]
  have : (↑hD.unit⁻¹ : A) * PowerSeries.coeff 0 D = 1 := hD.val_inv_mul
  rw [this, one_mul]

/-- The simplification of `thm:supp-finite-acc-coefficients`: if `χ₀ = χ₁ = χ₂ = 0` then
`v₀ = v₁ = v₂ = 0` and `v₃ = D₀⁻¹ χ₃`. -/
theorem coeff_eq_zero_of_mul_eq {D v χ : PowerSeries A} (h : D * v = χ)
    (hD : IsUnit (PowerSeries.coeff 0 D)) (hχ : ∀ j < 3, PowerSeries.coeff j χ = 0) :
    (∀ j < 3, PowerSeries.coeff j v = 0) ∧
      PowerSeries.coeff 3 v = hD.unit⁻¹ * PowerSeries.coeff 3 χ := by
  have hlow : ∀ j < 3, PowerSeries.coeff j v = 0 := by
    intro j hj
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      rw [coeff_eq_of_mul_eq_of_isUnit h hD j, hχ j hj, zero_sub]
      have : ∑ i ∈ Ioc 0 j, PowerSeries.coeff i D * PowerSeries.coeff (j - i) v = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_Ioc] at hi
        rw [ih (j - i) (by omega) (by omega), mul_zero]
      rw [this, neg_zero, mul_zero]
  refine ⟨hlow, ?_⟩
  rw [coeff_eq_of_mul_eq_of_isUnit h hD 3]
  congr 1
  have : ∑ i ∈ Ioc 0 3, PowerSeries.coeff i D * PowerSeries.coeff (3 - i) v = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_Ioc] at hi
    rw [hlow (3 - i) (by omega), mul_zero]
  rw [this, sub_zero]

end Recursion

/-! ### Pole tests -/

section Poles

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]

theorem scalar_identities {a : ℝ} (ha : a ≠ 0) :
    a ^ 3 * a⁻¹ ^ 3 = 1 ∧ a ^ 3 * a⁻¹ ^ 2 = a ∧ a ^ 3 * a⁻¹ = a ^ 2 ∧ a⁻¹ * a = 1 ∧
      a⁻¹ * a ^ 2 = a ∧ a⁻¹ * a ^ 3 = a ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp

theorem eq_of_eventually_eq_of_tendsto {f g : ℝ → U} {x y : U}
    (hf : Tendsto f (𝓝[≠] 0) (𝓝 x)) (hg : Tendsto g (𝓝[≠] 0) (𝓝 y))
    (h : ∀ a, a ≠ 0 → f a = g a) : x = y := by
  refine tendsto_nhds_unique hf (hg.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (h a ha).symm

/-- **Pole test.**  If `e(a) = a⁻³ c₀ + a⁻² c₁ + a⁻¹ c₂ + c₃ + r(a)` for `a ≠ 0` with
`r(a) → 0`, then `e` has a limit at `0` (along `a ≠ 0`) iff `c₀ = c₁ = c₂ = 0`; the limit is
then `c₃`. -/
theorem tendsto_laurent_iff (e r : ℝ → U) (c₀ c₁ c₂ c₃ : U)
    (he : ∀ a, a ≠ 0 → e a = (a⁻¹ ^ 3) • c₀ + (a⁻¹ ^ 2) • c₁ + a⁻¹ • c₂ + c₃ + r a)
    (hr : Tendsto r (𝓝[≠] 0) (𝓝 0)) :
    ((∃ L, Tendsto e (𝓝[≠] 0) (𝓝 L)) ↔ c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0) ∧
      (c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 → Tendsto e (𝓝[≠] 0) (𝓝 c₃)) := by
  have hid : Tendsto (fun a : ℝ => a) (𝓝[≠] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  have hconv : c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 → Tendsto e (𝓝[≠] 0) (𝓝 c₃) := by
    rintro ⟨rfl, rfl, rfl⟩
    have h : Tendsto (fun a => c₃ + r a) (𝓝[≠] 0) (𝓝 (c₃ + 0)) := tendsto_const_nhds.add hr
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [he a ha]
    simp
  refine ⟨⟨?_, fun h => ⟨c₃, hconv h⟩⟩, hconv⟩
  rintro ⟨L, hL⟩
  set m : ℝ → U := fun a => e a - c₃ - r a with hmdef
  have hm : Tendsto m (𝓝[≠] 0) (𝓝 (L - c₃ - 0)) := (hL.sub tendsto_const_nhds).sub hr
  have hmeq : ∀ a, a ≠ 0 → m a = (a⁻¹ ^ 3) • c₀ + (a⁻¹ ^ 2) • c₁ + a⁻¹ • c₂ := by
    intro a ha
    simp only [hmdef, he a ha]
    abel
  have hpow : ∀ k : ℕ, 0 < k → Tendsto (fun a : ℝ => a ^ k • m a) (𝓝[≠] 0) (𝓝 0) := by
    intro k hk
    have := (hid.pow k).smul hm
    simpa [zero_pow hk.ne'] using this
  have key : ∀ a, a ≠ 0 → c₀ + a • c₁ + a ^ 2 • c₂ = a ^ 3 • m a := by
    intro a ha
    obtain ⟨e1, e2, e3, -, -, -⟩ := scalar_identities ha
    rw [hmeq a ha, smul_add, smul_add, smul_smul, smul_smul, smul_smul, e1, e2, e3, one_smul]
  have hc₀ : c₀ = 0 := by
    have hpoly : Tendsto (fun a : ℝ => c₀ + a • c₁ + a ^ 2 • c₂) (𝓝[≠] 0)
        (𝓝 (c₀ + (0 : ℝ) • c₁ + (0 : ℝ) ^ 2 • c₂)) :=
      (tendsto_const_nhds.add (hid.smul tendsto_const_nhds)).add
        ((hid.pow 2).smul tendsto_const_nhds)
    simp only [zero_smul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at hpoly
    exact eq_of_eventually_eq_of_tendsto hpoly (hpow 3 (by norm_num)) key
  have key2 : ∀ a, a ≠ 0 → c₁ + a • c₂ = a ^ 2 • m a := by
    intro a ha
    obtain ⟨-, -, -, f1, f2, f3⟩ := scalar_identities ha
    have := congrArg (fun x => a⁻¹ • x) (key a ha)
    simp only [hc₀, zero_add, smul_add, smul_smul, f1, f2, f3, one_smul] at this
    exact this
  have hc₁ : c₁ = 0 := by
    have hpoly : Tendsto (fun a : ℝ => c₁ + a • c₂) (𝓝[≠] 0) (𝓝 (c₁ + (0 : ℝ) • c₂)) :=
      tendsto_const_nhds.add (hid.smul tendsto_const_nhds)
    rw [zero_smul, add_zero] at hpoly
    exact eq_of_eventually_eq_of_tendsto hpoly (hpow 2 (by norm_num)) key2
  have key3 : ∀ a, a ≠ 0 → c₂ = a • m a := by
    intro a ha
    obtain ⟨-, -, -, f1, f2, -⟩ := scalar_identities ha
    have := congrArg (fun x => a⁻¹ • x) (key2 a ha)
    simp only [hc₁, zero_add, smul_smul, f1, f2, one_smul] at this
    exact this
  have hc₂ : c₂ = 0 := by
    have h1 := hpow 1 one_pos
    simp only [pow_one] at h1
    exact eq_of_eventually_eq_of_tendsto tendsto_const_nhds h1 key3
  exact ⟨hc₀, hc₁, hc₂⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The cubic Taylor remainder of an analytic function, divided by `a³`, tends to `0`. -/
theorem tendsto_taylor_remainder (v : ℝ → V) (pv : FormalMultilinearSeries ℝ ℝ V)
    (hv : HasFPowerSeriesAt v pv 0) :
    Tendsto (fun a : ℝ => (a⁻¹ ^ 3) • (v a - ∑ k ∈ range 4, a ^ k • pv.coeff k)) (𝓝[≠] 0)
      (𝓝 0) := by
  have hO := hv.isBigO_sub_partialSum_pow 4
  obtain ⟨C, hC⟩ := hO.bound
  have hpart : ∀ a : ℝ, pv.partialSum 4 a = ∑ k ∈ range 4, a ^ k • pv.coeff k := by
    intro a
    simp [FormalMultilinearSeries.partialSum]
  have hbound : ∀ᶠ a in 𝓝[≠] (0 : ℝ),
      ‖(a⁻¹ ^ 3) • (v a - ∑ k ∈ range 4, a ^ k • pv.coeff k)‖ ≤ C * |a| := by
    filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with a ha ha0
    simp only [zero_add, hpart, Real.norm_eq_abs, abs_abs, norm_pow] at ha
    rw [norm_smul, norm_pow, norm_inv, Real.norm_eq_abs]
    have hpos : 0 < |a| := abs_pos.2 ha0
    calc |a|⁻¹ ^ 3 * ‖v a - ∑ k ∈ range 4, a ^ k • pv.coeff k‖
        ≤ |a|⁻¹ ^ 3 * (C * |a| ^ 4) := by gcongr
      _ = C * |a| := by field_simp
  have hlim : Tendsto (fun a : ℝ => C * |a|) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun a : ℝ => C * |a|) (𝓝 0) (𝓝 (C * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    rw [abs_zero, mul_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  exact squeeze_zero_norm' hbound hlim

/-- **Acceleration-defect pole test** (`eq:supp-finite-acc-poles`, `eq:supp-finite-acc-verdict`).
Let `v` have a power series at `0` with coefficients `v_j = pv.coeff j`, `p` linear, and
`θ(a) = a⁻³ θ₋₃ + a⁻² θ₋₂ + a⁻¹ θ₋₁ + θ₀ + ρ(a)` with `ρ → 0`.  Then the defect
`-a⁻³ p v(a) - θ(a)` has a finite limit at `0` iff `p v_j + θ_{j-3} = 0` for `j = 0, 1, 2`, and
the limit is then `-p v₃ - θ₀`. -/
theorem defect_tendsto_iff (v : ℝ → V) (pv : FormalMultilinearSeries ℝ ℝ V)
    (hv : HasFPowerSeriesAt v pv 0) (p : V →L[ℝ] U) (θm3 θm2 θm1 θ0 : U) (θ ρ : ℝ → U)
    (hθ : ∀ a, a ≠ 0 → θ a = (a⁻¹ ^ 3) • θm3 + (a⁻¹ ^ 2) • θm2 + a⁻¹ • θm1 + θ0 + ρ a)
    (hρ : Tendsto ρ (𝓝[≠] 0) (𝓝 0)) :
    ((∃ L, Tendsto (fun a => -((a⁻¹ ^ 3) • p (v a)) - θ a) (𝓝[≠] 0) (𝓝 L)) ↔
        p (pv.coeff 0) + θm3 = 0 ∧ p (pv.coeff 1) + θm2 = 0 ∧ p (pv.coeff 2) + θm1 = 0) ∧
      (p (pv.coeff 0) + θm3 = 0 ∧ p (pv.coeff 1) + θm2 = 0 ∧ p (pv.coeff 2) + θm1 = 0 →
        Tendsto (fun a => -((a⁻¹ ^ 3) • p (v a)) - θ a) (𝓝[≠] 0)
          (𝓝 (-(p (pv.coeff 3)) - θ0))) := by
  set R : ℝ → V := fun a => (a⁻¹ ^ 3) • (v a - ∑ k ∈ range 4, a ^ k • pv.coeff k) with hRdef
  have hR : Tendsto R (𝓝[≠] 0) (𝓝 0) := tendsto_taylor_remainder v pv hv
  set r : ℝ → U := fun a => -(p (R a)) - ρ a with hrdef
  have hr : Tendsto r (𝓝[≠] 0) (𝓝 0) := by
    have := ((p.continuous.tendsto 0).comp hR).neg.sub hρ
    simpa [r] using this
  have he : ∀ a, a ≠ 0 → -((a⁻¹ ^ 3) • p (v a)) - θ a =
      (a⁻¹ ^ 3) • (-(p (pv.coeff 0) + θm3)) + (a⁻¹ ^ 2) • (-(p (pv.coeff 1) + θm2)) +
        a⁻¹ • (-(p (pv.coeff 2) + θm1)) + (-(p (pv.coeff 3)) - θ0) + r a := by
    intro a ha
    have hva : v a = ∑ k ∈ range 4, a ^ k • pv.coeff k + a ^ 3 • R a := by
      simp only [hRdef, smul_smul]
      rw [show a ^ 3 * a⁻¹ ^ 3 = 1 by field_simp, one_smul]
      abel
    rw [hθ a ha, hva]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_add, map_smul, smul_add,
      smul_smul, hrdef]
    have e1 : a⁻¹ ^ 3 * a ^ 0 = a⁻¹ ^ 3 := by ring
    have e2 : a⁻¹ ^ 3 * a ^ 1 = a⁻¹ ^ 2 := by field_simp
    have e3 : a⁻¹ ^ 3 * a ^ 2 = a⁻¹ := by field_simp
    have e4 : a⁻¹ ^ 3 * a ^ 3 = 1 := by field_simp
    rw [e1, e2, e3, e4, one_smul, one_smul]
    simp only [zero_add, smul_neg, smul_add, map_zero, smul_zero]
    abel
  have := tendsto_laurent_iff _ r _ _ _ _ he hr
  simp only [neg_eq_zero] at this
  exact this

end Poles

end PowerSeriesQuotient

end RenewalGeometry
