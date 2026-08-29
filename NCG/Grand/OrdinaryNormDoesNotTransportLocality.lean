/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MovingRankOneStrongResolventCounterexample
import Mathlib.Data.Nat.Dist

/-!
# Ordinary norm convergence does not transport a locality exponent

This is the exact countable-carrier witness from
`cth:GTLOC-norm-not-weighted`. On complex `ℓ²(ℕ)`, the operator supported on
the two directed matrix entries `(0,n)` and `(n,0)` has ordinary operator
norm equal to its amplitude. The exponentially weighted row and column
suprema multiply the same amplitude by `exp (α n)`.
-/

open Filter Topology
open scoped lp

noncomputable section

namespace NCG
namespace OrdinaryNormDoesNotTransportLocality

abbrev Space := ℓ²(ℕ, ℂ)

/-- Standard coordinate vector in complex `ℓ²(ℕ)`. -/
def basisVector (n : ℕ) : Space := lp.single 2 n 1

@[simp] theorem norm_basisVector (n : ℕ) : ‖basisVector n‖ = 1 := by
  simp [basisVector, lp.norm_single]

@[simp] theorem basisVector_apply (n i : ℕ) :
    basisVector n i = if n = i then 1 else 0 := by
  classical
  by_cases h : n = i
  · subst i
    simp [basisVector, lp.single_apply]
  · simp [basisVector, lp.single_apply, h]

@[simp] theorem inner_basisVector_left (n : ℕ) (x : Space) :
    inner ℂ (basisVector n) x = x n := by
  simp [basisVector, lp.inner_single_left]

@[simp] theorem inner_basisVector_basisVector {n m : ℕ} (h : n ≠ m) :
    inner ℂ (basisVector n) (basisVector m) = 0 := by
  simp [basisVector, lp.inner_single_left, lp.single_apply, h]

@[simp] theorem inner_basisVector_basisVector_ite (n m : ℕ) :
    inner ℂ (basisVector n) (basisVector m) = if n = m then 1 else 0 := by
  by_cases h : n = m
  · subst m
    simp [basisVector]
  · simp [inner_basisVector_basisVector h, h]

/-- The unscaled two-site hop `|e₀><eₙ| + |eₙ><e₀|`. -/
def twoSiteHop (n : ℕ) : Space →L[ℂ] Space :=
  InnerProductSpace.rankOne ℂ (basisVector 0) (basisVector n) +
    InnerProductSpace.rankOne ℂ (basisVector n) (basisVector 0)

theorem twoSiteHop_apply (n : ℕ) (x : Space) :
    twoSiteHop n x = x n • basisVector 0 + x 0 • basisVector n := by
  simp [twoSiteHop, InnerProductSpace.rankOne_apply]

/-- The two-coordinate part of an `ℓ²` vector cannot exceed its full norm. -/
theorem two_coordinate_sq_le {n : ℕ} (hn : n ≠ 0) (x : Space) :
    ‖x n‖ ^ 2 + ‖x 0‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (p := (2 : ENNReal))
    (by norm_num) x ({n, 0} : Finset ℕ)
  simpa [ENNReal.toReal_ofNat, hn] using h

/-- For distinct sites, the unscaled two-site hop has genuine operator norm one. -/
theorem norm_twoSiteHop {n : ℕ} (hn : n ≠ 0) : ‖twoSiteHop n‖ = 1 := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [twoSiteHop_apply]
    have horth : inner ℂ (x n • basisVector 0) (x 0 • basisVector n) = 0 := by
      simp [inner_smul_left, inner_smul_right,
        inner_basisVector_basisVector hn.symm]
    have hsquare :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (x n • basisVector 0) (x 0 • basisVector n) horth
    simp only [norm_smul, norm_basisVector, mul_one] at hsquare
    have hle := two_coordinate_sq_le hn x
    nlinarith [norm_nonneg (x n • basisVector 0 + x 0 • basisVector n),
      norm_nonneg x]
  · have happly : twoSiteHop n (basisVector 0) = basisVector n := by
      rw [twoSiteHop_apply]
      simp [basisVector, lp.single_apply, hn]
    have hbound := ContinuousLinearMap.le_opNorm (twoSiteHop n) (basisVector 0)
    rw [happly, norm_basisVector, norm_basisVector, mul_one] at hbound
    exact hbound

/-- The manuscript's long-hop family. -/
def longHop (α : ℝ) (n : ℕ) : Space →L[ℂ] Space :=
  (Real.exp (-α * n / 2) : ℂ) • twoSiteHop n

/-- Genuine operator norm of the long hop. -/
theorem norm_longHop {α : ℝ} {n : ℕ} (hn : n ≠ 0) :
    ‖longHop α n‖ = Real.exp (-α * n / 2) := by
  rw [longHop, norm_smul, norm_twoSiteHop hn, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Scalar block kernel of the same operator. -/
def longHopKernel (α : ℝ) (n i j : ℕ) : ℂ :=
  if (i = 0 ∧ j = n) ∨ (i = n ∧ j = 0)
  then Real.exp (-α * n / 2)
  else 0

/-- Matrix coefficients of the genuine `ℓ²` operator equal the displayed kernel. -/
theorem longHop_matrixCoefficient {α : ℝ} {n i j : ℕ} (hn : n ≠ 0) :
    inner ℂ (basisVector i) (longHop α n (basisVector j)) =
      longHopKernel α n i j := by
  rw [longHop, smul_apply, twoSiteHop_apply]
  by_cases hi0 : i = 0 <;> by_cases hin : i = n <;>
    by_cases hj0 : j = 0 <;> by_cases hjn : j = n <;>
    simp [longHopKernel, hi0, hin, hj0, hjn, hn, Ne.symm hn] <;> omega

/-- Weighted row sum on the countable scalar-block carrier. -/
def weightedRow (α : ℝ) (K : ℕ → ℕ → ℂ) (i : ℕ) : ℝ :=
  ∑' j : ℕ, Real.exp (α * Nat.dist i j) * ‖K i j‖

/-- Weighted column sum on the countable scalar-block carrier. -/
def weightedCol (α : ℝ) (K : ℕ → ℕ → ℂ) (j : ℕ) : ℝ :=
  ∑' i : ℕ, Real.exp (α * Nat.dist i j) * ‖K i j‖

/-- Countable scalar-block version of the manuscript weighted Schur norm. -/
def weightedSchurNorm (α : ℝ) (K : ℕ → ℕ → ℂ) : ℝ :=
  max (⨆ i : ℕ, weightedRow α K i) (⨆ j : ℕ, weightedCol α K j)

theorem exp_weight_mul_amplitude (α : ℝ) (n : ℕ) :
    Real.exp (α * n) * Real.exp (-α * n / 2) = Real.exp (α * n / 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

@[simp] theorem norm_longHop_amplitude (α : ℝ) (n : ℕ) :
    ‖(Real.exp (-α * n / 2) : ℂ)‖ = Real.exp (-α * n / 2) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem weightedRow_longHopKernel {α : ℝ} {n i : ℕ} (hn : n ≠ 0) :
    weightedRow α (longHopKernel α n) i =
      if i = 0 ∨ i = n then Real.exp (α * n / 2) else 0 := by
  by_cases hi0 : i = 0
  · subst i
    rw [if_pos (Or.inl rfl), weightedRow]
    have hfun : (fun j : ℕ => Real.exp (α * Nat.dist 0 j) *
        ‖longHopKernel α n 0 j‖) = fun j =>
        if j = n then Real.exp (α * n) * Real.exp (-α * n / 2) else 0 := by
      funext j
      by_cases hj : j = n
      · subst j
        simp [longHopKernel, hn, Ne.symm hn, Complex.norm_exp,
          Nat.dist_zero_left]
      · simp [longHopKernel, hj, Ne.symm hn]
    rw [hfun, tsum_ite_eq]
    exact exp_weight_mul_amplitude α n
  · by_cases hin : i = n
    · subst i
      rw [if_pos (Or.inr rfl), weightedRow]
      have hfun : (fun j : ℕ => Real.exp (α * Nat.dist n j) *
          ‖longHopKernel α n n j‖) = fun j =>
          if j = 0 then Real.exp (α * n) * Real.exp (-α * n / 2) else 0 := by
        funext j
        by_cases hj : j = 0
        · subst j
          simp [longHopKernel, hn, Ne.symm hn, Complex.norm_exp,
            Nat.dist_zero_right]
        · simp [longHopKernel, hj, hn]
      rw [hfun, tsum_ite_eq]
      exact exp_weight_mul_amplitude α n
    · simp [weightedRow, longHopKernel, hi0, hin]

theorem weightedCol_longHopKernel {α : ℝ} {n j : ℕ} (hn : n ≠ 0) :
    weightedCol α (longHopKernel α n) j =
      if j = 0 ∨ j = n then Real.exp (α * n / 2) else 0 := by
  by_cases hj0 : j = 0
  · subst j
    rw [if_pos (Or.inl rfl), weightedCol]
    have hfun : (fun i : ℕ => Real.exp (α * Nat.dist i 0) *
        ‖longHopKernel α n i 0‖) = fun i =>
        if i = n then Real.exp (α * n) * Real.exp (-α * n / 2) else 0 := by
      funext i
      by_cases hi : i = n
      · subst i
        simp [longHopKernel, hn, Ne.symm hn, Complex.norm_exp,
          Nat.dist_zero_right]
      · simp [longHopKernel, hi, Ne.symm hn]
    rw [hfun, tsum_ite_eq]
    exact exp_weight_mul_amplitude α n
  · by_cases hjn : j = n
    · subst j
      rw [if_pos (Or.inr rfl), weightedCol]
      have hfun : (fun i : ℕ => Real.exp (α * Nat.dist i n) *
          ‖longHopKernel α n i n‖) = fun i =>
          if i = 0 then Real.exp (α * n) * Real.exp (-α * n / 2) else 0 := by
        funext i
        by_cases hi : i = 0
        · subst i
          simp [longHopKernel, hn, Ne.symm hn, Complex.norm_exp,
            Nat.dist_zero_left]
        · simp [longHopKernel, hi, hn]
      rw [hfun, tsum_ite_eq]
      exact exp_weight_mul_amplitude α n
    · simp [weightedCol, longHopKernel, hj0, hjn]

theorem iSup_weightedRow_longHopKernel {α : ℝ} {n : ℕ} (hn : n ≠ 0) :
    (⨆ i : ℕ, weightedRow α (longHopKernel α n) i) =
      Real.exp (α * n / 2) := by
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    rw [weightedRow_longHopKernel hn]
    by_cases h : i = 0 ∨ i = n
    · rw [if_pos h]
    · rw [if_neg h]
      exact (Real.exp_pos _).le
  · have hbdd : BddAbove (Set.range fun i : ℕ =>
        weightedRow α (longHopKernel α n) i) := by
      refine ⟨Real.exp (α * n / 2), ?_⟩
      rintro _ ⟨i, rfl⟩
      change weightedRow α (longHopKernel α n) i ≤ Real.exp (α * n / 2)
      rw [weightedRow_longHopKernel hn]
      by_cases h : i = 0 ∨ i = n
      · rw [if_pos h]
      · rw [if_neg h]
        exact (Real.exp_pos _).le
    calc Real.exp (α * n / 2)
        = weightedRow α (longHopKernel α n) 0 := by
          rw [weightedRow_longHopKernel hn]
          simp
      _ ≤ ⨆ i : ℕ, weightedRow α (longHopKernel α n) i :=
        le_ciSup hbdd 0

theorem iSup_weightedCol_longHopKernel {α : ℝ} {n : ℕ} (hn : n ≠ 0) :
    (⨆ j : ℕ, weightedCol α (longHopKernel α n) j) =
      Real.exp (α * n / 2) := by
  apply le_antisymm
  · refine ciSup_le fun j => ?_
    rw [weightedCol_longHopKernel hn]
    by_cases h : j = 0 ∨ j = n
    · rw [if_pos h]
    · rw [if_neg h]
      exact (Real.exp_pos _).le
  · have hbdd : BddAbove (Set.range fun j : ℕ =>
        weightedCol α (longHopKernel α n) j) := by
      refine ⟨Real.exp (α * n / 2), ?_⟩
      rintro _ ⟨j, rfl⟩
      change weightedCol α (longHopKernel α n) j ≤ Real.exp (α * n / 2)
      rw [weightedCol_longHopKernel hn]
      by_cases h : j = 0 ∨ j = n
      · rw [if_pos h]
      · rw [if_neg h]
        exact (Real.exp_pos _).le
    calc Real.exp (α * n / 2)
        = weightedCol α (longHopKernel α n) 0 := by
          rw [weightedCol_longHopKernel hn]
          simp
      _ ≤ ⨆ j : ℕ, weightedCol α (longHopKernel α n) j :=
        le_ciSup hbdd 0

/-- Exact weighted Schur norm of the long-hop kernel. -/
theorem weightedSchurNorm_longHopKernel {α : ℝ} {n : ℕ} (hn : n ≠ 0) :
    weightedSchurNorm α (longHopKernel α n) = Real.exp (α * n / 2) := by
  rw [weightedSchurNorm, iSup_weightedRow_longHopKernel hn,
    iSup_weightedCol_longHopKernel hn, max_self]

/-- Ordinary norm tends to zero while the fixed-`α` weighted Schur norm diverges. -/
theorem ordinary_norm_convergence_does_not_transport_locality (hα : 0 < α) :
    (∀ n : ℕ, ‖longHop α (n + 1)‖ = Real.exp (-α * (n + 1) / 2)) ∧
    Tendsto (fun n : ℕ => ‖longHop α (n + 1)‖) atTop (𝓝 0) ∧
    (∀ n : ℕ, weightedSchurNorm α (longHopKernel α (n + 1)) =
      Real.exp (α * (n + 1) / 2)) ∧
    Tendsto (fun n : ℕ => weightedSchurNorm α
      (longHopKernel α (n + 1))) atTop atTop := by
  have hnz : ∀ n : ℕ, n + 1 ≠ 0 := fun n => Nat.succ_ne_zero n
  refine ⟨fun n => by simpa [Nat.cast_add, Nat.cast_one] using
      (norm_longHop (α := α) (hnz n)), ?_,
    fun n => by simpa [Nat.cast_add, Nat.cast_one] using
      (weightedSchurNorm_longHopKernel (α := α) (hnz n)), ?_⟩
  · have htop : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hneg : Tendsto (fun n : ℕ => -α * (n + 1 : ℝ) / 2) atTop atBot := by
      have hc : -α / 2 < 0 := by linarith
      have hraw := (tendsto_const_mul_atBot_of_neg hc).mpr htop
      exact hraw.congr fun n => by ring
    have hexp : Tendsto (fun n : ℕ => Real.exp
        (-α * (n + 1 : ℝ) / 2)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp hneg
    exact hexp.congr' (Eventually.of_forall fun n => by
      change Real.exp (-α * (n + 1 : ℝ) / 2) = ‖longHop α (n + 1)‖
      symm
      simpa [Nat.cast_add, Nat.cast_one] using
        (norm_longHop (α := α) (hnz n)))
  · have htop : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hpos : 0 < α / 2 := by positivity
    have hscale : Tendsto (fun n : ℕ => α * (n + 1 : ℝ) / 2) atTop atTop := by
      have hraw := (tendsto_const_mul_atTop_of_pos hpos).mpr htop
      exact hraw.congr fun n => by ring
    have hexp : Tendsto (fun n : ℕ => Real.exp
        (α * (n + 1 : ℝ) / 2)) atTop atTop := by
      simpa [Function.comp_def] using Real.tendsto_exp_atTop.comp hscale
    exact hexp.congr' (Eventually.of_forall fun n => by
      change Real.exp (α * (n + 1 : ℝ) / 2) =
        weightedSchurNorm α (longHopKernel α (n + 1))
      symm
      simpa [Nat.cast_add, Nat.cast_one] using
        (weightedSchurNorm_longHopKernel (α := α) (hnz n)))

end OrdinaryNormDoesNotTransportLocality
end NCG
