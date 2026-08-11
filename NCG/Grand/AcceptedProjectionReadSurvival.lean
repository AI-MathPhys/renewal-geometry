/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Protected reads under an accepted partition projection

This file gives the exact finite conditional-expectation model used in
`thm:accepted-projection-read-survival`.  It proves the preservation/refinement
equivalence, rigidity for a separating family of reads, the exchangeable count
projection formulas, annihilation of nonconstant Fourier modes, and the
separate-factor preservation identity.
-/

namespace NCG

/-- Uniform conditional expectation onto the fibres of a finite record `C`. -/
noncomputable def acceptedPartitionAverage
    {Ω B : Type*} [Fintype Ω] [DecidableEq B]
    (C : Ω → B) (f : Ω → ℂ) (x : Ω) : ℂ :=
  ((Finset.univ.filter fun y => C y = C x).card : ℂ)⁻¹ *
    ∑ y ∈ Finset.univ.filter (fun y => C y = C x), f y

private theorem acceptedPartitionFiber_card_ne_zero
    {Ω B : Type*} [Fintype Ω] [DecidableEq B]
    (C : Ω → B) (x : Ω) :
    (Finset.univ.filter fun y => C y = C x).card ≠ 0 := by
  classical
  apply Nat.ne_of_gt
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- The conditional average has the same value at points in the same block. -/
theorem acceptedPartitionAverage_eq_of_sameBlock
    {Ω B : Type*} [Fintype Ω] [DecidableEq B]
    (C : Ω → B) (f : Ω → ℂ) {x y : Ω} (hxy : C x = C y) :
    acceptedPartitionAverage C f x = acceptedPartitionAverage C f y := by
  classical
  have hf : Finset.univ.filter (fun z => C z = C x) =
      Finset.univ.filter (fun z => C z = C y) := by
    ext z
    simp [hxy]
  simp only [acceptedPartitionAverage, hf]

/-- A partition expectation preserves every function of a read exactly when
each partition block is contained in a fibre of that read. -/
theorem acceptedPartitionAverage_preserves_functions_iff
    {Ω B V : Type*} [Fintype Ω] [DecidableEq B]
    (C : Ω → B) (G : Ω → V) :
    (∀ φ : V → ℂ,
        acceptedPartitionAverage C (φ ∘ G) = φ ∘ G) ↔
      ∀ ⦃x y : Ω⦄, C x = C y → G x = G y := by
  classical
  constructor
  · intro hpres x y hxy
    let φ : V → ℂ := fun z => if z = G x then 1 else 0
    have hx := congrFun (hpres φ) x
    have hy := congrFun (hpres φ) y
    have havg := acceptedPartitionAverage_eq_of_sameBlock C (φ ∘ G) hxy
    have hφ : φ (G x) = φ (G y) := by
      change (φ ∘ G) x = (φ ∘ G) y
      rw [← hx, ← hy]
      exact havg
    by_contra hne
    have hneyx : G y ≠ G x := Ne.symm hne
    simp [φ, hneyx] at hφ
  · intro hblock φ
    funext x
    rw [acceptedPartitionAverage]
    have hterm : ∀ y ∈ Finset.univ.filter (fun y => C y = C x),
        (φ ∘ G) y = φ (G x) := by
      intro y hy
      exact congrArg φ (hblock (Finset.mem_filter.mp hy).2)
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    have hcard :
        (((Finset.univ.filter fun y => C y = C x).card : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast acceptedPartitionFiber_card_ne_zero C x
    field_simp
    rfl

/-- Conditional expectation onto a finite partition is idempotent. -/
theorem acceptedPartitionAverage_idempotent
    {Ω B : Type*} [Fintype Ω] [DecidableEq B]
    (C : Ω → B) (f : Ω → ℂ) :
    acceptedPartitionAverage C (acceptedPartitionAverage C f) =
      acceptedPartitionAverage C f := by
  classical
  have hblock : ∀ ⦃x y : Ω⦄, C x = C y →
      acceptedPartitionAverage C f x = acceptedPartitionAverage C f y := by
    intro x y hxy
    exact acceptedPartitionAverage_eq_of_sameBlock C f hxy
  have hp := (acceptedPartitionAverage_preserves_functions_iff C
    (acceptedPartitionAverage C f)).2 hblock
  simpa using hp id

/-- If retained reads separate configurations, a partition projection that
preserves every function of every retained read is the identity. -/
theorem acceptedPartitionAverage_eq_identity_of_separatingReads
    {Ω B R : Type*} [Fintype Ω] [DecidableEq B]
    (C : Ω → B) (G : R → Ω → Ω)
    (hsep : ∀ ⦃x y : Ω⦄, (∀ r, G r x = G r y) → x = y)
    (hpres : ∀ r (φ : Ω → ℂ),
      acceptedPartitionAverage C (φ ∘ G r) = φ ∘ G r) :
    ∀ f : Ω → ℂ, acceptedPartitionAverage C f = f := by
  classical
  have hrefine : ∀ ⦃x y : Ω⦄, C x = C y → x = y := by
    intro x y hxy
    apply hsep
    intro r
    exact (acceptedPartitionAverage_preserves_functions_iff C (G r)).1
      (hpres r) hxy
  intro f
  apply (acceptedPartitionAverage_preserves_functions_iff C id).2
  intro x y hxy
  exact hrefine hxy

/-- Point read on one of `M` exchangeable cells. -/
def exchangeablePointRead {M : Type*} [DecidableEq M] (i : M) : M → ℝ :=
  fun j => if j = i then 1 else 0

/-- Orthogonal projection of the first cell-chaos onto the constant/count
direction. -/
noncomputable def exchangeableCountProjection
    {M : Type*} [Fintype M] (v : M → ℝ) : M → ℝ :=
  fun _ => ((Fintype.card M : ℝ)⁻¹) * ∑ j, v j

/-- The count projection sends every point read to the empirical mean, and
the discarded point component has squared norm `1 - 1/M`. -/
theorem exchangeableCountProjection_pointRead
    {M : Type*} [Fintype M] [DecidableEq M]
    (i : M) (hM : 0 < Fintype.card M) :
    (exchangeableCountProjection (exchangeablePointRead i) =
        fun _ => (Fintype.card M : ℝ)⁻¹)
    ∧ (∑ j, (exchangeablePointRead i j -
          exchangeableCountProjection (exchangeablePointRead i) j) ^ 2)
        = 1 - (Fintype.card M : ℝ)⁻¹ := by
  classical
  have hsum : ∑ j, exchangeablePointRead i j = 1 := by
    simp [exchangeablePointRead]
  have hsumSq : ∑ j, (exchangeablePointRead i j) ^ 2 = 1 := by
    simp [exchangeablePointRead]
  have hcardR : (Fintype.card M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hM)
  constructor
  · funext j
    simp [exchangeableCountProjection, hsum]
  · simp only [exchangeableCountProjection, hsum, mul_one]
    let a : ℝ := (Fintype.card M : ℝ)⁻¹
    change (∑ j, (exchangeablePointRead i j - a) ^ 2) = 1 - a
    calc
      (∑ j, (exchangeablePointRead i j - a) ^ 2) =
          ∑ j, ((exchangeablePointRead i j) ^ 2
            + (-2 * a) * exchangeablePointRead i j + a ^ 2) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = (∑ j, (exchangeablePointRead i j) ^ 2)
          + (-2 * a) * (∑ j, exchangeablePointRead i j)
          + (Fintype.card M : ℝ) * a ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul]
      _ = 1 - a := by
            rw [hsumSq, hsum]
            dsimp [a]
            field_simp
            ring

/-- Every zero-sum (hence every nonconstant Fourier) mode is annihilated by
the count projection. -/
theorem exchangeableCountProjection_eq_zero_of_sum_eq_zero
    {M : Type*} [Fintype M] (v : M → ℝ) (hv : ∑ j, v j = 0) :
    exchangeableCountProjection v = 0 := by
  funext i
  simp [exchangeableCountProjection, hv]

/-- Product projection acting only on the microscopic factor. -/
def microscopicFactorProjection
    {X M : Type*} (R : (M → ℂ) → (M → ℂ))
    (f : X × M → ℂ) : X × M → ℂ :=
  fun xm => R (fun m => f (xm.1, m)) xm.2

/-- A projection confined to a separate microscopic factor preserves every
geometric read exactly. -/
theorem microscopicFactorProjection_preserves_geometricRead
    {X M : Type*} (R : (M → ℂ) → (M → ℂ))
    (hconst : ∀ c : ℂ, R (fun _ => c) = fun _ => c)
    (g : X → ℂ) :
    microscopicFactorProjection R (fun xm => g xm.1) =
      fun xm => g xm.1 := by
  funext xm
  change R (fun _ => g xm.1) xm.2 = g xm.1
  rw [hconst]

end NCG
