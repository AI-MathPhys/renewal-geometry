/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical entropic occurrence law and information Pythagoras

Machinery for `thm:accepted-entropic-projection`.  On the finite transport polytope
`Π_E(α, β)` of nonnegative couplings supported on the admitted edge set `E` with source and
target marginals `α`, `β`, the relative entropy `D(π‖R) = ∑ π log(π/R)` to a positive
reference `R` has

* (AO.5) an attained minimum (`exists_min`) at a unique coupling (`min_unique`, via strict
  convexity of `x log x`);
* (AO.6) if a feasible coupling has the Gibbs product form `π₀ = R e^{a(x)+b(y)}` on `E`, then
  it is the entropic projection (`gibbs_isMin`), and the potentials are unique up to the gauge
  `a ↦ a + c`, `b ↦ b - c` on a connected feasible support (`gibbs_gauge`);
* (AO.7) the information Pythagoras `D(π‖R) = D(π‖π₀) + D(π₀‖R)` for every feasible `π`
  (`kl_pythagoras`);
* (AO.8) for an observed feasible coupling the selection residual `D(π^obs‖π₀)` vanishes
  exactly at the projection (`selection_residual_eq_zero_iff`), and the occurrence cost
  `D(π₀‖R)` vanishes exactly when the reference itself is feasible (`occurrence_zero_iff`).
-/

open Finset

namespace NCG
namespace EntropicProjection

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The relative-entropy summand `a log a - a log r` (equal to `a log(a/r)`, with
`0 log 0 = 0`). -/
noncomputable def klTerm (a r : ℝ) : ℝ := a * Real.log a - a * Real.log r

theorem klTerm_eq {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) : klTerm a r = a * Real.log (a / r) := by
  rcases ha.lt_or_eq with ha' | ha'
  · rw [klTerm, Real.log_div ha'.ne' hr.ne']
    ring
  · rw [klTerm, ← ha']
    ring

theorem klTerm_self {a : ℝ} : klTerm a a = 0 := by rw [klTerm]; ring

/-- `D(π‖R) = ∑ π log(π/R)`. -/
noncomputable def kl (π R : X × Y → ℝ) : ℝ := ∑ p, klTerm (π p) (R p)

theorem kl_self (π : X × Y → ℝ) : kl π π = 0 := by
  simp [kl, klTerm_self]

/-- The transport polytope `Π_E(α, β)`. -/
def feasible (E : Set (X × Y)) (α : X → ℝ) (β : Y → ℝ) : Set (X × Y → ℝ) :=
  {π | (∀ p, 0 ≤ π p) ∧ (∀ p, p ∉ E → π p = 0) ∧
    (∀ x, ∑ y, π (x, y) = α x) ∧ (∀ y, ∑ x, π (x, y) = β y)}

variable {E : Set (X × Y)} {α : X → ℝ} {β : Y → ℝ}

theorem sum_eq_of_feasible {π : X × Y → ℝ} (hπ : π ∈ feasible E α β) :
    ∑ p, π p = ∑ x, α x := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => hπ.2.2.1 x

/-! ### (AO.5): existence -/

theorem convex_feasible : Convex ℝ (feasible E α β) := by
  intro π hπ π' hπ' a b ha hb hab
  refine ⟨fun p => ?_, fun p hp => ?_, fun x => ?_, fun y => ?_⟩
  · exact add_nonneg (mul_nonneg ha (hπ.1 p)) (mul_nonneg hb (hπ'.1 p))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hπ.2.1 p hp, hπ'.2.1 p hp, mul_zero,
      add_zero]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hπ.2.2.1 x, hπ'.2.2.1 x, ← add_mul, hab, one_mul]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hπ.2.2.2 y, hπ'.2.2.2 y, ← add_mul, hab, one_mul]

theorem isClosed_feasible : IsClosed (feasible E α β) := by
  have h : feasible E α β = (⋂ p, {π : X × Y → ℝ | 0 ≤ π p}) ∩
      (⋂ p ∈ Eᶜ, {π : X × Y → ℝ | π p = 0}) ∩
      (⋂ x, {π : X × Y → ℝ | ∑ y, π (x, y) = α x}) ∩
      ⋂ y, {π : X × Y → ℝ | ∑ x, π (x, y) = β y} := by
    ext π
    simp only [feasible, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
    tauto
  rw [h]
  refine (((isClosed_iInter fun p => isClosed_le continuous_const (continuous_apply p)).inter
    (isClosed_biInter fun p _ => isClosed_eq (continuous_apply p) continuous_const)).inter
    (isClosed_iInter fun x =>
      isClosed_eq (continuous_finsetSum _ fun y _ => continuous_apply (x, y))
        continuous_const)).inter
    (isClosed_iInter fun y =>
      isClosed_eq (continuous_finsetSum _ fun x _ => continuous_apply (x, y)) continuous_const)

theorem isCompact_feasible : IsCompact (feasible E α β) := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_feasible ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨∑ x, |α x|, fun π hπ => ?_⟩
  have hnonneg : 0 ≤ ∑ x, |α x| := Finset.sum_nonneg fun x _ => abs_nonneg _
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (hπ.1 p)]
  calc π p ≤ ∑ y, π (p.1, y) :=
        Finset.single_le_sum (fun y _ => hπ.1 (p.1, y)) (Finset.mem_univ p.2)
    _ = α p.1 := hπ.2.2.1 p.1
    _ ≤ |α p.1| := le_abs_self _
    _ ≤ ∑ x, |α x| := Finset.single_le_sum (fun x _ => abs_nonneg (α x)) (Finset.mem_univ p.1)

theorem continuous_kl (R : X × Y → ℝ) : Continuous fun π : X × Y → ℝ => kl π R := by
  refine continuous_finsetSum _ fun p _ => ?_
  unfold klTerm
  exact ((Real.continuous_mul_log.comp (continuous_apply p)).sub
    ((continuous_apply p).mul continuous_const))

/-- **(AO.5), existence**: the entropic projection is attained. -/
theorem exists_min (R : X × Y → ℝ) (hne : (feasible E α β).Nonempty) :
    ∃ π₀ ∈ feasible E α β, ∀ π ∈ feasible E α β, kl π₀ R ≤ kl π R := by
  obtain ⟨π₀, h₀, hmin⟩ := isCompact_feasible.exists_isMinOn hne (continuous_kl R).continuousOn
  exact ⟨π₀, h₀, fun π hπ => hmin hπ⟩

/-! ### (AO.5): uniqueness -/

/-- Strict convexity of the summand in its first argument, for a positive reference. -/
theorem klTerm_midpoint_lt {r : ℝ} {a₁ a₂ : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (hne : a₁ ≠ a₂) :
    klTerm ((a₁ + a₂) / 2) r < (klTerm a₁ r + klTerm a₂ r) / 2 := by
  have hconv := Real.strictConvexOn_mul_log.2 h₁ h₂ hne (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  simp only [smul_eq_mul] at hconv
  have e1 : (1 : ℝ) / 2 * a₁ + 1 / 2 * a₂ = (a₁ + a₂) / 2 := by ring
  rw [e1] at hconv
  unfold klTerm
  nlinarith [hconv]

theorem klTerm_midpoint_le {r : ℝ} {a₁ a₂ : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) :
    klTerm ((a₁ + a₂) / 2) r ≤ (klTerm a₁ r + klTerm a₂ r) / 2 := by
  rcases eq_or_ne a₁ a₂ with h | h
  · rw [h]
    ring_nf
    exact le_rfl
  · exact (klTerm_midpoint_lt h₁ h₂ h).le

/-- **(AO.5), uniqueness**: the entropic projection is unique. -/
theorem min_unique (R : X × Y → ℝ) {π₁ π₂ : X × Y → ℝ} (h₁ : π₁ ∈ feasible E α β)
    (h₂ : π₂ ∈ feasible E α β) (hmin₁ : ∀ π ∈ feasible E α β, kl π₁ R ≤ kl π R)
    (hmin₂ : ∀ π ∈ feasible E α β, kl π₂ R ≤ kl π R) : π₁ = π₂ := by
  by_contra hne
  obtain ⟨p, hp⟩ : ∃ p, π₁ p ≠ π₂ p := by
    by_contra h
    push Not at h
    exact hne (funext h)
  set πm : X × Y → ℝ := fun q => (π₁ q + π₂ q) / 2 with hπm
  have hmem : πm ∈ feasible E α β := by
    have := convex_feasible (E := E) (α := α) (β := β) h₁ h₂
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    convert this using 1
    funext q
    simp [hπm]
    ring
  have heq : kl π₁ R = kl π₂ R := le_antisymm (hmin₁ π₂ h₂) (hmin₂ π₁ h₁)
  have hlt : kl πm R < (kl π₁ R + kl π₂ R) / 2 := by
    unfold kl
    rw [div_eq_inv_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_lt_sum (fun q _ => ?_) ⟨p, Finset.mem_univ p, ?_⟩
    · have := klTerm_midpoint_le (r := R q) (h₁.1 q) (h₂.1 q)
      calc klTerm (πm q) (R q) ≤ (klTerm (π₁ q) (R q) + klTerm (π₂ q) (R q)) / 2 := this
        _ = 2⁻¹ * (klTerm (π₁ q) (R q) + klTerm (π₂ q) (R q)) := by ring
    · have := klTerm_midpoint_lt (r := R p) (h₁.1 p) (h₂.1 p) hp
      calc klTerm (πm p) (R p) < (klTerm (π₁ p) (R p) + klTerm (π₂ p) (R p)) / 2 := this
        _ = 2⁻¹ * (klTerm (π₁ p) (R p) + klTerm (π₂ p) (R p)) := by ring
  rw [heq] at hlt
  have : kl πm R < kl π₂ R := by linarith
  exact absurd (hmin₂ πm hmem) (not_le.mpr this)

/-! ### Gibbs couplings, (AO.6)–(AO.7) -/

variable (R : X × Y → ℝ) (a : X → ℝ) (b : Y → ℝ)

/-- The Gibbs product form on the admitted edges. -/
def IsGibbsOn (π₀ : X × Y → ℝ) : Prop :=
  ∀ p ∈ E, π₀ p = R p * Real.exp (a p.1 + b p.2)

/-- The potential pairing `∑ π (a + b)` of a feasible coupling depends only on the
marginals. -/
theorem sum_potential (π : X × Y → ℝ) (hπ : π ∈ feasible E α β) :
    ∑ p, π p * (a p.1 + b p.2) = ∑ x, α x * a x + ∑ y, β y * b y := by
  rw [Fintype.sum_prod_type]
  have h : ∀ x, ∑ y, π (x, y) * (a x + b y) = α x * a x + ∑ y, π (x, y) * b y := by
    intro x
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hπ.2.2.1 x]
  simp only [h, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_mul, hπ.2.2.2 y]

/-- **(AO.7)**: the information Pythagoras for a feasible Gibbs coupling. -/
theorem kl_pythagoras (hR : ∀ p, 0 < R p) {π₀ : X × Y → ℝ}
    (h₀ : π₀ ∈ feasible E α β) (hg : IsGibbsOn R a b (E := E) π₀) {π : X × Y → ℝ}
    (hπ : π ∈ feasible E α β) : kl π R = kl π π₀ + kl π₀ R := by
  have key : ∀ π' : X × Y → ℝ, π' ∈ feasible E α β →
      kl π' R - kl π' π₀ = ∑ x, α x * a x + ∑ y, β y * b y := by
    intro π' hπ'
    have hterm : ∀ p, klTerm (π' p) (R p) - klTerm (π' p) (π₀ p)
        = π' p * (a p.1 + b p.2) := by
      intro p
      by_cases hE : p ∈ E
      · rw [klTerm, klTerm, hg p hE, Real.log_mul (hR p).ne' (Real.exp_pos _).ne',
          Real.log_exp]
        ring
      · rw [hπ'.2.1 p hE, klTerm, klTerm]
        ring
    rw [kl, kl, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun p _ => hterm p]
    exact sum_potential a b π' hπ'
  have h1 := key π hπ
  have h2 := key π₀ h₀
  rw [kl_self] at h2
  linarith

/-- Gibbs' inequality: `D(π‖ρ) ≥ 0` for equal total masses, absolutely continuous supports. -/
theorem klTerm_ge {aa r : ℝ} (ha : 0 < aa) (hr : 0 < r) : aa - r ≤ klTerm aa r := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hr ha)
  rw [Real.log_div hr.ne' ha.ne'] at hlog
  rw [klTerm]
  have h1 : aa * (Real.log r - Real.log aa) ≤ aa * (r / aa - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) ha.le
  have e : aa * (r / aa - 1) = r - aa := by field_simp
  nlinarith

theorem klTerm_gt {aa r : ℝ} (ha : 0 < aa) (hr : 0 < r) (hne : aa ≠ r) :
    aa - r < klTerm aa r := by
  have hlog := Real.log_lt_sub_one_of_pos (div_pos hr ha)
    (by
      intro h
      rw [div_eq_iff ha.ne', one_mul] at h
      exact hne h.symm)
  rw [Real.log_div hr.ne' ha.ne'] at hlog
  rw [klTerm]
  have h1 : aa * (Real.log r - Real.log aa) < aa * (r / aa - 1) :=
    mul_lt_mul_of_pos_left (by linarith) ha
  have e : aa * (r / aa - 1) = r - aa := by field_simp
  nlinarith

theorem kl_eq_sum_support {π ρ : X × Y → ℝ} (hπ : ∀ p, 0 ≤ π p) :
    kl π ρ = ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), klTerm (π p) (ρ p) := by
  classical
  rw [kl]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun p _ hp => ?_).symm
  rw [Finset.mem_filter, not_and] at hp
  have h0 : π p = 0 := le_antisymm (not_lt.mp (hp (Finset.mem_univ p))) (hπ p)
  rw [h0, klTerm]
  ring

theorem sum_support_ge {π ρ : X × Y → ℝ} (hπ : ∀ p, 0 ≤ π p) (hρ : ∀ p, 0 ≤ ρ p)
    (hsum : ∑ p, π p = ∑ p, ρ p) :
    0 ≤ ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), (π p - ρ p) := by
  classical
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), π p = ∑ p, π p := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun p _ hp => ?_
    rw [Finset.mem_filter, not_and] at hp
    exact le_antisymm (not_lt.mp (hp (Finset.mem_univ p))) (hπ p)
  have h2 : ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), ρ p ≤ ∑ p, ρ p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ => hρ p
  rw [h1, hsum]
  linarith

theorem kl_nonneg {π ρ : X × Y → ℝ} (hπ : ∀ p, 0 ≤ π p) (hρ : ∀ p, 0 ≤ ρ p)
    (hac : ∀ p, 0 < π p → 0 < ρ p) (hsum : ∑ p, π p = ∑ p, ρ p) : 0 ≤ kl π ρ := by
  classical
  rw [kl_eq_sum_support hπ]
  calc (0 : ℝ) ≤ ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), (π p - ρ p) :=
        sum_support_ge hπ hρ hsum
    _ ≤ ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), klTerm (π p) (ρ p) :=
        Finset.sum_le_sum fun p hp => klTerm_ge (Finset.mem_filter.mp hp).2
          (hac p (Finset.mem_filter.mp hp).2)

/-- Strict Gibbs inequality: `D(π‖ρ) = 0` with equal masses forces `π = ρ`. -/
theorem eq_of_kl_eq_zero {π ρ : X × Y → ℝ} (hπ : ∀ p, 0 ≤ π p) (hρ : ∀ p, 0 ≤ ρ p)
    (hac : ∀ p, 0 < π p → 0 < ρ p) (hsum : ∑ p, π p = ∑ p, ρ p) (h0 : kl π ρ = 0) : π = ρ := by
  classical
  by_contra hne
  obtain ⟨q, hq⟩ : ∃ q, π q ≠ ρ q := by
    by_contra h
    push Not at h
    exact hne (funext h)
  by_cases hcase : ∀ p, 0 < π p → π p = ρ p
  · -- every supported coordinate agrees, so the difference lives off the support
    have hq0 : π q = 0 := by
      by_contra h
      exact hq (hcase q (lt_of_le_of_ne (hπ q) (Ne.symm h)))
    have hρq : 0 < ρ q := lt_of_le_of_ne (hρ q) fun h => hq (by rw [hq0, ← h])
    have h1 : ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), ρ p
        = ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), π p :=
      Finset.sum_congr rfl fun p hp => ((hcase p (Finset.mem_filter.mp hp).2)).symm
    have h2 : ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), π p = ∑ p, π p := by
      refine Finset.sum_subset (Finset.filter_subset _ _) fun p _ hp => ?_
      rw [Finset.mem_filter, not_and] at hp
      exact le_antisymm (not_lt.mp (hp (Finset.mem_univ p))) (hπ p)
    have h3 : ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), ρ p < ∑ p, ρ p := by
      refine Finset.sum_lt_sum_of_subset (Finset.filter_subset _ _) (Finset.mem_univ q) ?_ hρq
        fun j _ _ => hρ j
      rw [Finset.mem_filter, not_and]
      intro _
      rw [hq0]
      exact lt_irrefl 0
    rw [h1, h2, hsum] at h3
    exact lt_irrefl _ h3
  · push Not at hcase
    obtain ⟨p, hp, hp'⟩ := hcase
    have hlt : ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), (π p - ρ p)
        < ∑ p ∈ Finset.univ.filter (fun p => 0 < π p), klTerm (π p) (ρ p) := by
      refine Finset.sum_lt_sum (fun r hr => klTerm_ge (Finset.mem_filter.mp hr).2
        (hac r (Finset.mem_filter.mp hr).2)) ⟨p, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
      · exact klTerm_gt hp (hac p hp) hp'
    have := sum_support_ge hπ hρ hsum
    rw [kl_eq_sum_support hπ] at h0
    linarith

/-- **(AO.6)**: a feasible Gibbs coupling is the entropic projection. -/
theorem gibbs_isMin (hR : ∀ p, 0 < R p) {π₀ : X × Y → ℝ} (h₀ : π₀ ∈ feasible E α β)
    (hg : IsGibbsOn R a b (E := E) π₀) : ∀ π ∈ feasible E α β, kl π₀ R ≤ kl π R := by
  intro π hπ
  rw [kl_pythagoras R a b hR h₀ hg hπ]
  have hnn : 0 ≤ kl π π₀ := by
    refine kl_nonneg hπ.1 h₀.1 (fun p hp => ?_) ?_
    · by_cases hE : p ∈ E
      · rw [hg p hE]
        exact mul_pos (hR p) (Real.exp_pos _)
      · exact absurd (hπ.2.1 p hE) hp.ne'
    · rw [sum_eq_of_feasible hπ, sum_eq_of_feasible h₀]
  linarith

/-! ### (AO.8): residual split -/

/-- **(AO.8), selection**: the selection residual vanishes exactly at the projection. -/
theorem selection_residual_eq_zero_iff (hR : ∀ p, 0 < R p) {π₀ : X × Y → ℝ}
    (h₀ : π₀ ∈ feasible E α β) (hg : IsGibbsOn R a b (E := E) π₀) {π : X × Y → ℝ}
    (hπ : π ∈ feasible E α β) : kl π π₀ = 0 ↔ π = π₀ := by
  constructor
  · intro h0
    refine eq_of_kl_eq_zero hπ.1 h₀.1 (fun p hp => ?_) ?_ h0
    · by_cases hE : p ∈ E
      · rw [hg p hE]
        exact mul_pos (hR p) (Real.exp_pos _)
      · exact absurd (hπ.2.1 p hE) hp.ne'
    · rw [sum_eq_of_feasible hπ, sum_eq_of_feasible h₀]
  · rintro rfl
    exact kl_self π

/-- **(AO.8), occurrence**: the occurrence cost vanishes exactly when the reference is itself
feasible (for the stationary reading, exactly when `νQ = ν`). -/
theorem occurrence_zero_iff (hR : ∀ p, 0 < R p) {π₀ : X × Y → ℝ} (h₀ : π₀ ∈ feasible E α β)
    (hg : IsGibbsOn R a b (E := E) π₀) (hRsum : ∑ p, R p = ∑ x, α x) :
    kl π₀ R = 0 ↔ R ∈ feasible E α β := by
  constructor
  · intro h0
    have hEq : π₀ = R := by
      refine eq_of_kl_eq_zero h₀.1 (fun p => (hR p).le) (fun p _ => hR p) ?_ h0
      rw [sum_eq_of_feasible h₀, hRsum]
    rw [← hEq]
    exact h₀
  · intro hRf
    have h1 := gibbs_isMin R a b hR h₀ hg R hRf
    rw [kl_self] at h1
    have h2 : 0 ≤ kl π₀ R := by
      refine kl_nonneg h₀.1 (fun p => (hR p).le) (fun p _ => hR p) ?_
      rw [sum_eq_of_feasible h₀, hRsum]
    linarith

/-! ### (AO.6): gauge uniqueness of the potentials -/

/-- The bipartite step relation of the admitted support. -/
inductive Step (E : Set (X × Y)) : X ⊕ Y → X ⊕ Y → Prop
  | fwd {x : X} {y : Y} : (x, y) ∈ E → Step E (Sum.inl x) (Sum.inr y)
  | bwd {x : X} {y : Y} : (x, y) ∈ E → Step E (Sum.inr y) (Sum.inl x)

omit [Fintype X] [Fintype Y] in
/-- **(AO.6), gauge**: on a connected feasible support, two Gibbs potential pairs for the same
coupling differ by the gauge `a ↦ a + c`, `b ↦ b - c`. -/
theorem gibbs_gauge [Nonempty X] (hR : ∀ p, 0 < R p) {π₀ : X × Y → ℝ}
    (hg : IsGibbsOn R a b (E := E) π₀) {a' : X → ℝ} {b' : Y → ℝ}
    (hg' : IsGibbsOn R a' b' (E := E) π₀)
    (hconn : ∀ u v : X ⊕ Y, Relation.ReflTransGen (Step E) u v) :
    ∃ c : ℝ, (∀ x, a' x = a x + c) ∧ ∀ y, b' y = b y - c := by
  have hedge : ∀ p ∈ E, a p.1 + b p.2 = a' p.1 + b' p.2 := by
    intro p hp
    have h1 := hg p hp
    have h2 := hg' p hp
    rw [h1] at h2
    have := mul_left_cancel₀ (hR p).ne' h2
    exact Real.exp_injective this
  set d : X ⊕ Y → ℝ := Sum.elim (fun x => a' x - a x) (fun y => b y - b' y) with hd
  have hstep : ∀ {u v : X ⊕ Y}, Step E u v → d u = d v := by
    intro u v h
    cases h with
    | fwd hmem =>
      have := hedge _ hmem
      simp only [hd, Sum.elim_inl, Sum.elim_inr]
      linarith
    | bwd hmem =>
      have := hedge _ hmem
      simp only [hd, Sum.elim_inl, Sum.elim_inr]
      linarith
  have hconst : ∀ u v : X ⊕ Y, d u = d v := by
    intro u v
    induction hconn u v with
    | refl => rfl
    | tail _ hstep' ih => exact ih.trans (hstep hstep')
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  refine ⟨a' x₀ - a x₀, fun x => ?_, fun y => ?_⟩
  · have := hconst (Sum.inl x) (Sum.inl x₀)
    simp only [hd, Sum.elim_inl] at this
    linarith
  · have := hconst (Sum.inr y) (Sum.inl x₀)
    simp only [hd, Sum.elim_inl, Sum.elim_inr] at this
    linarith

/-- **`thm:accepted-entropic-projection`**: (AO.5) the entropic occurrence problem has an
attained, unique minimizer; given the Gibbs form (AO.6) of a feasible coupling (its existence
is the Lagrange-multiplier step, taken as an interface hypothesis) that coupling is the
projection, its potentials are gauge-unique on a connected support, (AO.7) the information
Pythagoras holds for every feasible coupling, and (AO.8) the selection residual vanishes
exactly at the projection while the occurrence cost vanishes exactly when the reference is
feasible. -/
theorem accepted_entropic_projection (hR : ∀ p, 0 < R p) (hne : (feasible E α β).Nonempty) :
    (∃ πm ∈ feasible E α β, ∀ π ∈ feasible E α β, kl πm R ≤ kl π R) ∧
      (∀ π₁ π₂ : X × Y → ℝ, π₁ ∈ feasible E α β → π₂ ∈ feasible E α β →
        (∀ π ∈ feasible E α β, kl π₁ R ≤ kl π R) → (∀ π ∈ feasible E α β, kl π₂ R ≤ kl π R) →
        π₁ = π₂) ∧
      ∀ π₀ : X × Y → ℝ, π₀ ∈ feasible E α β → IsGibbsOn R a b (E := E) π₀ →
        (∀ π ∈ feasible E α β, kl π₀ R ≤ kl π R) ∧
        (∀ π ∈ feasible E α β, kl π R = kl π π₀ + kl π₀ R) ∧
        (∀ π ∈ feasible E α β, (kl π π₀ = 0 ↔ π = π₀)) ∧
        ((∑ p, R p = ∑ x, α x) → (kl π₀ R = 0 ↔ R ∈ feasible E α β)) ∧
        ∀ [Nonempty X], ∀ (a' : X → ℝ) (b' : Y → ℝ), IsGibbsOn R a' b' (E := E) π₀ →
          (∀ u v : X ⊕ Y, Relation.ReflTransGen (Step E) u v) →
          ∃ c : ℝ, (∀ x, a' x = a x + c) ∧ ∀ y, b' y = b y - c :=
  ⟨exists_min R hne,
    fun _ _ h₁ h₂ hm₁ hm₂ => min_unique R h₁ h₂ hm₁ hm₂,
    fun _π₀ h₀ hg =>
      ⟨gibbs_isMin R a b hR h₀ hg, fun _ hπ => kl_pythagoras R a b hR h₀ hg hπ,
        fun _ hπ => selection_residual_eq_zero_iff R a b hR h₀ hg hπ,
        fun hRsum => occurrence_zero_iff R a b hR h₀ hg hRsum,
        fun _ _ hg' hconn => gibbs_gauge R a b hR hg hg' hconn⟩⟩

end EntropicProjection
end NCG
