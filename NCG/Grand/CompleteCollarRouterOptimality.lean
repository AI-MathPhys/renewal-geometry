/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FinitePressureFlowMaxCut

/-!
# Exact router constants for a complete collar

This file supplies the optimizer layer of
`thm:hierarchy-linear-router-distinction`.  Demands on `Fin k` are centered
and measured in the coordinate maximum norm; currents are antisymmetric and
measured edgewise.  The nonlinear result is obtained from the finite
max-flow/min-cut theorem, while the linear lower bound is a finite trace
identity.
-/

open scoped BigOperators

noncomputable section

namespace NCG
namespace CompleteCollarRouterOptimality

/-- Unit capacity on every edge of the loopless complete graph. -/
def completeCapacity {k : ℕ} (i j : Fin k) : ℝ :=
  if i = j then 0 else 1

theorem completeCapacity_nonneg {k : ℕ} (i j : Fin k) :
    0 ≤ completeCapacity i j := by
  by_cases h : i = j <;> simp [completeCapacity, h]

theorem completeCapacity_symm {k : ℕ} (i j : Fin k) :
    completeCapacity i j = completeCapacity j i := by
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    simp [completeCapacity, h, h']

/-- A complete-graph cut has `|A| (k-|A|)` unit-capacity edges. -/
theorem completeCapacity_cut {k : ℕ} (A : Finset (Fin k)) :
    finiteCutCapacity (completeCapacity : Fin k → Fin k → ℝ) A =
      A.card * (k - A.card) := by
  classical
  rw [finiteCutCapacity]
  have hinner : ∀ u ∈ A,
      (∑ v ∈ Aᶜ, completeCapacity u v) = ((Aᶜ).card : ℝ) := by
    intro u hu
    have huv : ∀ v ∈ Aᶜ, u ≠ v := by
      intro v hv huv
      subst v
      exact (Finset.mem_compl.mp hv) hu
    calc
      (∑ v ∈ Aᶜ, completeCapacity u v) =
          ∑ v ∈ Aᶜ, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [completeCapacity, if_neg (huv v hv)]
      _ = ((Aᶜ).card : ℝ) := by simp
  calc
    (∑ u ∈ A, ∑ v ∈ Aᶜ, completeCapacity u v)
        = ∑ u ∈ A, ((Aᶜ).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro u hu
          exact hinner u hu
    _ = (A.card : ℝ) * (Aᶜ).card := by simp
    _ = A.card * (k - A.card) := by
      have hcard : A.card ≤ k := by
        simpa using Finset.card_le_univ A
      rw [Finset.card_compl]
      simp [hcard]

/-- The larger side of a split of `k` vertices has at least
`ceil(k/2)` vertices. -/
def ceilingHalf (k : ℕ) : ℕ := (k + 1) / 2

theorem min_side_mul_ceilingHalf_le_cut
    (k r : ℕ) (hr : r ≤ k) :
    min r (k - r) * ceilingHalf k ≤ r * (k - r) := by
  by_cases hside : r ≤ k - r
  · have hhalf : ceilingHalf k ≤ k - r := by
      simp only [ceilingHalf]
      omega
    rw [min_eq_left hside]
    exact Nat.mul_le_mul_left r hhalf
  · have hside' : k - r ≤ r := Nat.le_of_lt (lt_of_not_ge hside)
    have hhalf : ceilingHalf k ≤ r := by
      simp only [ceilingHalf]
      omega
    rw [min_eq_right hside']
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (k - r) hhalf

theorem ceilingHalf_pos {k : ℕ} (hk : 0 < k) : 0 < ceilingHalf k := by
  simp only [ceilingHalf]
  omega

/-- A coordinatewise bound controls the mass of every subset. -/
theorem abs_subset_sum_le_card_mul
    {k : ℕ} (b : Fin k → ℝ) (M : ℝ)
    (hM : ∀ i, |b i| ≤ M) (A : Finset (Fin k)) :
    |∑ i ∈ A, b i| ≤ A.card * M := by
  calc
    |∑ i ∈ A, b i| ≤ ∑ i ∈ A, |b i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ A, M := by
      gcongr with i hi
      exact hM i
    _ = A.card * M := by simp

/-- Centering identifies the demand through a cut with minus the demand
through its complementary cut. -/
theorem sum_compl_eq_neg_sum
    {k : ℕ} (b : Fin k → ℝ) (hcenter : ∑ i, b i = 0)
    (A : Finset (Fin k)) :
    ∑ i ∈ Aᶜ, b i = -(∑ i ∈ A, b i) := by
  have hsplit := Finset.sum_add_sum_compl A b
  rw [hcenter] at hsplit
  linarith

/-- The cut demand is bounded by the smaller side times the coordinate
maximum. -/
theorem abs_subset_sum_le_min_side_mul
    {k : ℕ} (b : Fin k → ℝ) (M : ℝ)
    (hcenter : ∑ i, b i = 0) (hM : ∀ i, |b i| ≤ M)
    (A : Finset (Fin k)) :
    |∑ i ∈ A, b i| ≤ min A.card (k - A.card) * M := by
  have hA := abs_subset_sum_le_card_mul b M hM A
  have hAc := abs_subset_sum_le_card_mul b M hM Aᶜ
  rw [sum_compl_eq_neg_sum b hcenter A, abs_neg, Finset.card_compl] at hAc
  simp only [Fintype.card_fin] at hAc
  by_cases hside : A.card ≤ k - A.card
  · rw [min_eq_left hside]
    exact hA
  · rw [min_eq_right (Nat.le_of_lt (lt_of_not_ge hside))]
    exact hAc

/-- The elementary arithmetic which turns the smaller-side demand bound into
the complete-graph cut condition. -/
theorem min_side_bound_le_complete_cut
    {k : ℕ} (hk : 0 < k) (r : ℕ) (hr : r ≤ k)
    (M : ℝ) (hM : 0 ≤ M) :
    (min r (k - r) : ℕ) * M ≤
      (M / ceilingHalf k) * (r * (k - r) : ℕ) := by
  have hq : (0 : ℝ) < ceilingHalf k := by
    exact_mod_cast ceilingHalf_pos hk
  have hnat := min_side_mul_ceilingHalf_le_cut k r hr
  have hreal :
      ((min r (k - r) * ceilingHalf k : ℕ) : ℝ) ≤
        ((r * (k - r) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    (min r (k - r) : ℕ) * M =
        (M / ceilingHalf k) *
          ((min r (k - r) * ceilingHalf k : ℕ) : ℝ) := by
            push_cast
            field_simp
    _ ≤ (M / ceilingHalf k) * (r * (k - r) : ℕ) := by
      exact mul_le_mul_of_nonneg_left hreal (div_nonneg hM hq.le)

/-- Every centered complete-collar demand with coordinate size at most `M`
has a (demand-dependent) current of congestion at most
`M / ceil(k/2)`.  This is the max-flow half of the exact nonlinear optimum. -/
theorem complete_pointwise_router_upper
    {k : ℕ} (hk : 0 < k) (b : Fin k → ℝ) (M : ℝ)
    (hM0 : 0 ≤ M) (hcenter : ∑ i, b i = 0)
    (hM : ∀ i, |b i| ≤ M) :
    ∃ j, j ∈ finiteCapacityCurrentSet
        (completeCapacity : Fin k → Fin k → ℝ)
        (M / ceilingHalf k) ∧
      finiteDivergence j = b := by
  have hkne : k ≠ 0 := Nat.ne_of_gt hk
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  apply (finite_transshipment_flow_cut_iff
    (completeCapacity : Fin k → Fin k → ℝ)
    completeCapacity_nonneg completeCapacity_symm b
    (M / ceilingHalf k)
    (div_nonneg hM0 (by positivity)) hcenter).2
  intro A
  calc
    |∑ v ∈ A, b v| ≤ min A.card (k - A.card) * M :=
      abs_subset_sum_le_min_side_mul b M hcenter hM A
    _ ≤ (M / ceilingHalf k) *
        (A.card * (k - A.card) : ℕ) := by
      exact min_side_bound_le_complete_cut hk A.card
        (by simpa using Finset.card_le_univ A) M hM0
    _ = (M / ceilingHalf k) *
        finiteCutCapacity (completeCapacity : Fin k → Fin k → ℝ) A := by
      rw [completeCapacity_cut]
      have hcard : A.card ≤ k := by
        simpa using Finset.card_le_univ A
      push_cast [hcard]
      ring

/-- The centered demand which is `1` on `A` and distributes the compensating
negative mass uniformly on the complement. -/
def balancedCutDemand {k : ℕ} (A : Finset (Fin k)) (i : Fin k) : ℝ :=
  if i ∈ A then 1 else -(A.card : ℝ) / (Aᶜ).card

theorem balancedCutDemand_centered {k : ℕ} (A : Finset (Fin k))
    (hAc : 0 < (Aᶜ).card) :
    ∑ i, balancedCutDemand A i = 0 := by
  classical
  have hsumA :
      (∑ i ∈ A, balancedCutDemand A i) = (A.card : ℝ) := by
    calc
      (∑ i ∈ A, balancedCutDemand A i) = ∑ _i ∈ A, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [balancedCutDemand, hi]
      _ = (A.card : ℝ) := by simp
  have hsumAc :
      (∑ i ∈ Aᶜ, balancedCutDemand A i) =
        (Aᶜ).card * (-(A.card : ℝ) / (Aᶜ).card) := by
    calc
      (∑ i ∈ Aᶜ, balancedCutDemand A i) =
          ∑ _i ∈ Aᶜ, (-(A.card : ℝ) / (Aᶜ).card) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hiA : i ∉ A := Finset.mem_compl.mp hi
            simp [balancedCutDemand, hiA]
      _ = (Aᶜ).card * (-(A.card : ℝ) / (Aᶜ).card) := by simp
  calc
    ∑ i, balancedCutDemand A i =
        (∑ i ∈ A, balancedCutDemand A i) +
          ∑ i ∈ Aᶜ, balancedCutDemand A i := by
            exact (Finset.sum_add_sum_compl A _).symm
    _ = (A.card : ℝ) + (Aᶜ).card *
        (-(A.card : ℝ) / (Aᶜ).card) := by rw [hsumA, hsumAc]
    _ = 0 := by
      have hAcR : ((Aᶜ).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hAc
      field_simp
      ring

theorem balancedCutDemand_on_cut {k : ℕ} (A : Finset (Fin k)) :
    ∑ i ∈ A, balancedCutDemand A i = A.card := by
  classical
  calc
    (∑ i ∈ A, balancedCutDemand A i) = ∑ _i ∈ A, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [balancedCutDemand, hi]
    _ = (A.card : ℝ) := by simp

theorem balancedCutDemand_abs_le_one {k : ℕ} (A : Finset (Fin k))
    (hside : A.card ≤ (Aᶜ).card) (hAc : 0 < (Aᶜ).card) :
    ∀ i, |balancedCutDemand A i| ≤ 1 := by
  intro i
  classical
  by_cases hi : i ∈ A
  · simp [balancedCutDemand, hi]
  · rw [balancedCutDemand, if_neg hi, abs_div, abs_neg]
    rw [abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg _)]
    exact (div_le_one (by positivity)).2 (by exact_mod_cast hside)

/-- A number is a uniform normalized pointwise-router bound when every
centered demand in the coordinate unit cube has a current in that capacity
box. -/
def IsUniformPointwiseBound (k : ℕ) (κ : ℝ) : Prop :=
  ∀ b : Fin k → ℝ, (∑ i, b i = 0) → (∀ i, |b i| ≤ 1) →
    ∃ j, j ∈ finiteCapacityCurrentSet
        (completeCapacity : Fin k → Fin k → ℝ) κ ∧
      finiteDivergence j = b

/-- The balanced half cut forces every uniform nonlinear router bound to be
at least `1 / ceil(k/2)`. -/
theorem complete_pointwise_router_lower
    {k : ℕ} (hk : 2 ≤ k) (κ : ℝ)
    (hκ : IsUniformPointwiseBound k κ) :
    1 / (ceilingHalf k : ℕ) ≤ κ := by
  classical
  let r := k / 2
  have hrk : r ≤ k := by
    dsimp [r]
    omega
  have hrUniv : r ≤ (Finset.univ : Finset (Fin k)).card := by
    simpa using hrk
  obtain ⟨A, -, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin k))) hrUniv
  have hAcCard : (Aᶜ).card = k - r := by
    rw [Finset.card_compl, hAcard]
    simp
  have hrpos : 0 < A.card := by
    rw [hAcard]
    simp [r]
    omega
  have hAcpos : 0 < (Aᶜ).card := by
    rw [hAcCard]
    omega
  have hside : A.card ≤ (Aᶜ).card := by
    rw [hAcard, hAcCard]
    simp [r]
    omega
  obtain ⟨j, hj, hjdiv⟩ := hκ (balancedCutDemand A)
    (balancedCutDemand_centered A hAcpos)
    (balancedCutDemand_abs_le_one A hside hAcpos)
  have hweak := flow_cut_weak_duality j
    (completeCapacity : Fin k → Fin k → ℝ) hj.1 A κ hj.2
  change (∑ v ∈ A, finiteDivergence j v) ≤
    κ * finiteCutCapacity
      (completeCapacity : Fin k → Fin k → ℝ) A at hweak
  rw [hjdiv, balancedCutDemand_on_cut, completeCapacity_cut] at hweak
  have hqCard : (Aᶜ).card = ceilingHalf k := by
    rw [hAcCard]
    dsimp [ceilingHalf, r]
    omega
  have hcutNat : k - A.card = ceilingHalf k := by
    rw [hAcard]
    dsimp [ceilingHalf, r]
    omega
  have hcardle : A.card ≤ k := by
    simpa using Finset.card_le_univ A
  have hcutReal : (k : ℝ) - A.card = (ceilingHalf k : ℕ) := by
    rw [← Nat.cast_sub hcardle]
    exact_mod_cast hcutNat
  rw [hcutReal] at hweak
  have hrR : (0 : ℝ) < A.card := by exact_mod_cast hrpos
  have hqR : (0 : ℝ) < ceilingHalf k := by
    exact_mod_cast ceilingHalf_pos (by omega : 0 < k)
  have hweak' :
      (A.card : ℝ) * 1 ≤
        (A.card : ℝ) * (κ * (ceilingHalf k : ℕ)) := by
    push_cast at hweak ⊢
    nlinarith
  have hone : (1 : ℝ) ≤ κ * (ceilingHalf k : ℕ) := by
    nlinarith
  exact (div_le_iff₀ hqR).2 (by simpa [mul_comm] using hone)

/-- The normalized nonlinear complete-collar optimum is exactly
`1 / ceil(k/2)`, expressed without hiding existence behind an infimum. -/
theorem complete_pointwise_bound_iff
    {k : ℕ} (hk : 2 ≤ k) (κ : ℝ) :
    IsUniformPointwiseBound k κ ↔
      1 / (ceilingHalf k : ℕ) ≤ κ := by
  constructor
  · exact complete_pointwise_router_lower hk κ
  · intro hκ b hcenter hb
    obtain ⟨j, hj, hjdiv⟩ := complete_pointwise_router_upper
      (by omega : 0 < k) b 1 (by norm_num) hcenter hb
    refine ⟨j, ⟨hj.1, ?_⟩, hjdiv⟩
    intro i l
    calc
      |j i l| ≤ (1 / (ceilingHalf k : ℕ)) * completeCapacity i l := hj.2 i l
      _ ≤ κ * completeCapacity i l := by
        exact mul_le_mul_of_nonneg_right hκ (completeCapacity_nonneg i l)

/-! ## The best one linear router -/

/-- The symmetric complete-graph right inverse `k⁻¹ B*`. -/
def canonicalLinearRouter (k : ℕ) :
    (Fin k → ℝ) →ₗ[ℝ] (Fin k → Fin k → ℝ) where
  toFun g i j := (g i - g j) / k
  map_add' g h := by
    funext i j
    simp only [Pi.add_apply]
    ring
  map_smul' a g := by
    funext i j
    change (a * g i - a * g j) / (k : ℝ) =
      a * ((g i - g j) / (k : ℝ))
    ring

theorem canonicalLinearRouter_antisymm (k : ℕ) (g : Fin k → ℝ) (i j : Fin k) :
    canonicalLinearRouter k g i j = -canonicalLinearRouter k g j i := by
  simp [canonicalLinearRouter]
  ring

theorem canonicalLinearRouter_rightInverse
    {k : ℕ} (hk : 0 < k) (g : Fin k → ℝ)
    (hcenter : ∑ i, g i = 0) :
    finiteDivergence (canonicalLinearRouter k g) = g := by
  funext i
  change (∑ u, (g i - g u) / (k : ℝ)) = g i
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hcenter]
  simp
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  field_simp

theorem canonicalLinearRouter_bound
    {k : ℕ} (hk : 0 < k) (g : Fin k → ℝ)
    (hg : ∀ i, |g i| ≤ 1) (i j : Fin k) :
    |canonicalLinearRouter k g i j| ≤ 2 / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  change |(g i - g j) / (k : ℝ)| ≤ 2 / (k : ℝ)
  rw [abs_div]
  rw [abs_of_nonneg hkR.le]
  apply (div_le_div_iff_of_pos_right hkR).2
  calc
    |g i - g j| ≤ |g i| + |g j| := abs_sub _ _
    _ ≤ 2 := by linarith [hg i, hg j]

/-- A uniform linear bound is witnessed by one linear antisymmetric current
assignment which is a right inverse on every centered demand. -/
def IsUniformLinearBound (k : ℕ) (κ : ℝ) : Prop :=
  ∃ R : (Fin k → ℝ) →ₗ[ℝ] (Fin k → Fin k → ℝ),
    (∀ g i j, R g i j = -R g j i) ∧
    (∀ g, (∑ i, g i = 0) → finiteDivergence (R g) = g) ∧
    ∀ g, (∑ i, g i = 0) → (∀ i, |g i| ≤ 1) →
      ∀ i j, |R g i j| ≤ κ

theorem canonical_isUniformLinearBound {k : ℕ} (hk : 0 < k) :
    IsUniformLinearBound k (2 / k) := by
  refine ⟨canonicalLinearRouter k, canonicalLinearRouter_antisymm k,
    canonicalLinearRouter_rightInverse hk, ?_⟩
  intro g _ hg i j
  exact canonicalLinearRouter_bound hk g hg i j

/-- The centered vertex atom `eᵢ - k⁻¹ 1`. -/
def centeredVertex {k : ℕ} (i : Fin k) (x : Fin k) : ℝ :=
  (if x = i then 1 else 0) - 1 / k

theorem centeredVertex_centered {k : ℕ} (hk : 0 < k) (i : Fin k) :
    ∑ x, centeredVertex i x = 0 := by
  classical
  unfold centeredVertex
  rw [Finset.sum_sub_distrib]
  simp
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  field_simp
  ring

theorem centeredVertex_sub_abs_le_one {k : ℕ} (i j x : Fin k) :
    |centeredVertex i x - centeredVertex j x| ≤ 1 := by
  classical
  unfold centeredVertex
  by_cases hxi : x = i <;> by_cases hxj : x = j
  · have hij : i = j := hxi.symm.trans hxj
    simp [hxi, hxj, hij]
  · have hij : i ≠ j := by
      intro hij
      exact hxj (hxi.trans hij)
    simp [hxi, hxj, hij]
  · have hij : j ≠ i := by
      intro hij
      exact hxi (hxj.trans hij)
    simp [hxi, hxj, hij]
    have heq : -(k : ℝ)⁻¹ - (1 - (k : ℝ)⁻¹) = -1 := by ring
    rw [heq]
    norm_num
  · simp [hxi, hxj]

theorem centeredVertex_sub_centered {k : ℕ} (hk : 0 < k) (i j : Fin k) :
    ∑ x, (centeredVertex i - centeredVertex j) x = 0 := by
  simp only [Pi.sub_apply, Finset.sum_sub_distrib,
    centeredVertex_centered hk]
  ring

theorem sum_centeredVertex_diagonal {k : ℕ} (hk : 0 < k) :
    ∑ i : Fin k, centeredVertex i i = (k : ℝ) - 1 := by
  classical
  simp only [centeredVertex, if_pos, Finset.sum_const, nsmul_eq_mul,
    Fintype.card_fin]
  rw [show (Finset.univ : Finset (Fin k)).card = k by simp]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  field_simp

/-- The finite trace identity behind the optimal linear lower bound. -/
theorem linear_router_trace_identity
    {k : ℕ} (hk : 0 < k)
    (R : (Fin k → ℝ) →ₗ[ℝ] (Fin k → Fin k → ℝ))
    (hanti : ∀ g i j, R g i j = -R g j i)
    (hright : ∀ g, (∑ i, g i = 0) → finiteDivergence (R g) = g) :
    (∑ i, ∑ j, R (centeredVertex i - centeredVertex j) i j) =
      2 * ((k : ℝ) - 1) := by
  let S : ℝ := ∑ i, ∑ j, R (centeredVertex i) i j
  have hS : S = (k : ℝ) - 1 := by
    calc
      S = ∑ i, finiteDivergence (R (centeredVertex i)) i := rfl
      _ = ∑ i, centeredVertex i i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hright (centeredVertex i) (centeredVertex_centered hk i)]
      _ = k - 1 := sum_centeredVertex_diagonal hk
  have hswap :
      (∑ i, ∑ j, R (centeredVertex j) i j) = -S := by
    calc
      (∑ i, ∑ j, R (centeredVertex j) i j) =
          ∑ j, ∑ i, R (centeredVertex j) i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -R (centeredVertex j) j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        exact hanti (centeredVertex j) i j
      _ = -S := by simp [S]
  rw [show (∑ i, ∑ j, R (centeredVertex i - centeredVertex j) i j) =
      S - ∑ i, ∑ j, R (centeredVertex j) i j by
    simp only [map_sub, Pi.sub_apply, Finset.sum_sub_distrib, S]]
  rw [hswap, hS]
  ring

/-- Any one linear complete-collar right inverse has normalized congestion at
least `2/k`.  The proof is the preceding trace identity plus the `k(k-1)`
off-diagonal coefficient bounds. -/
theorem complete_linear_router_lower
    {k : ℕ} (hk : 2 ≤ k) (κ : ℝ)
    (hκ : IsUniformLinearBound k κ) :
    2 / (k : ℝ) ≤ κ := by
  obtain ⟨R, hanti, hright, hbound⟩ := hκ
  have htrace := linear_router_trace_identity (by omega : 0 < k) R hanti hright
  have hκ0 : 0 ≤ κ := by
    let i : Fin k := ⟨0, by omega⟩
    have hb := hbound (0 : Fin k → ℝ) (by simp) (by simp) i i
    simpa using hb
  have hterm : ∀ i j : Fin k,
      R (centeredVertex i - centeredVertex j) i j ≤
        if i = j then 0 else κ := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · exact (le_abs_self _).trans
        (hbound (centeredVertex i - centeredVertex j)
          (centeredVertex_sub_centered (by omega : 0 < k) i j)
          (centeredVertex_sub_abs_le_one i j) i j) |>.trans_eq (if_neg hij).symm
  have hsum :
      (∑ i, ∑ j, R (centeredVertex i - centeredVertex j) i j) ≤
        ∑ i : Fin k, ∑ j : Fin k, if i = j then 0 else κ := by
    gcongr with i j
    exact hterm i j
  rw [htrace] at hsum
  have hrhs :
      (∑ i : Fin k, ∑ j : Fin k, if i = j then 0 else κ) =
        (k : ℝ) * ((k : ℝ) - 1) * κ := by
    classical
    have hinner : ∀ i : Fin k,
        (∑ j : Fin k, if i = j then 0 else κ) =
          ((k : ℝ) - 1) * κ := by
      intro i
      calc
        (∑ j : Fin k, if i = j then 0 else κ) =
            ∑ j : Fin k, (κ - if i = j then κ else 0) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hij : i = j <;> simp [hij]
        _ = (∑ _j : Fin k, κ) -
            ∑ j : Fin k, if i = j then κ else 0 := by
              rw [Finset.sum_sub_distrib]
        _ = ((k : ℝ) - 1) * κ := by
              simp
              ring
    simp_rw [hinner]
    simp
    ring
  rw [hrhs] at hsum
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2R : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm1R : (0 : ℝ) < (k : ℝ) - 1 := by
    linarith
  apply (div_le_iff₀ hkR).2
  nlinarith

/-- The normalized best-linear complete-collar constant is exactly `2/k`. -/
theorem complete_linear_bound_iff
    {k : ℕ} (hk : 2 ≤ k) (κ : ℝ) :
    IsUniformLinearBound k κ ↔ 2 / (k : ℝ) ≤ κ := by
  constructor
  · exact complete_linear_router_lower hk κ
  · intro hκ
    obtain ⟨R, hanti, hright, hbound⟩ :=
      canonical_isUniformLinearBound (by omega : 0 < k)
    refine ⟨R, hanti, hright, ?_⟩
    intro g hg0 hg i j
    exact (hbound g hg0 hg i j).trans hκ

end CompleteCollarRouterOptimality
end NCG
