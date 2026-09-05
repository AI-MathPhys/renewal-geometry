/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HardCoreConnectedSourceAssembly
import NCG.Grand.HardCoreCorrectorProfile

/-!
# Exact all-degree assembly for the hard-core corrector

For a finite Walsh packet at every volume, totalMass, lowMass, and tailMass
are actual finite sums, and their decomposition is proved by partitioning the
degree index.  The fixed-ceiling inverse-square estimate and exponential
localization then imply disappearance of the entire corrector.
-/

open scoped BigOperators Topology
open Filter

namespace NCG.HardCoreAllDegreeAssemblyExact

set_option maxHeartbeats 800000
variable {ι : ℕ → Type*} [∀ N, Fintype (ι N)]

/-- Total square mass of the finite Walsh packet at volume N. -/
def totalMass (y : ∀ N, ι N → ℝ) (N : ℕ) : ℝ :=
  ∑ i, y N i

/-- Square mass in degrees strictly below the ceiling R. -/
def lowMass (degree : ∀ N, ι N → ℕ) (y : ∀ N, ι N → ℝ)
    (N R : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => degree N i < R), y N i

/-- Square mass in degrees at least the ceiling R. -/
def tailMass (degree : ∀ N, ι N → ℕ) (y : ∀ N, ι N → ℝ)
    (N R : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => R ≤ degree N i), y N i

/-- The low/high splitting is an identity of the actual degree sums. -/
theorem totalMass_eq_lowMass_add_tailMass
    (degree : ∀ N, ι N → ℕ) (y : ∀ N, ι N → ℝ) (N R : ℕ) :
    totalMass y N = lowMass degree y N R + tailMass degree y N R := by
  classical
  unfold totalMass lowMass tailMass
  calc
    ∑ i, y N i =
        (∑ i ∈ Finset.univ.filter (fun i => degree N i < R), y N i) +
        ∑ i ∈ Finset.univ.filter (fun i => ¬ degree N i < R), y N i :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => degree N i < R) (fun i => y N i)).symm
    _ = _ := by simp only [not_lt]

/-- A nonnegative fixed-ceiling mass with an explicit inverse-square bound
tends to zero.  The shift N+1 avoids a special zero-volume case. -/
theorem tendsto_zero_of_invSq_bound
    (u : ℕ → ℝ) (C : ℝ)
    (hu : ∀ N, 0 ≤ u N)
    (hbound : ∀ N, u N ≤ C / (((N + 1 : ℕ) : ℝ) ^ 2)) :
    Tendsto u atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => C / ((n : ℝ) ^ 2))
      atTop (𝓝 0) :=
    tendsto_const_div_pow C 2 (by omega)
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hupper : Tendsto
      (fun N : ℕ => C / (((N + 1 : ℕ) : ℝ) ^ 2))
      atTop (𝓝 0) := by
    change Tendsto
      ((fun n : ℕ => C / ((n : ℝ) ^ 2)) ∘ (fun N : ℕ => N + 1))
      atTop (𝓝 0)
    exact hbase.comp hshift
  exact squeeze_zero' (Eventually.of_forall hu)
    (Eventually.of_forall hbound) hupper

/-- The exponential factor produced by Walsh localization is uniformly
small after choosing a sufficiently high degree ceiling. -/
theorem exponentialDegreeTail_eventually_small
    {α K ε : ℝ} (hα : 0 < α) (_hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ R : ℕ, Real.exp (-2 * α * ((R : ℝ) - 2)) * K < ε := by
  have hlim : Tendsto
      (fun R : ℕ => Real.exp (-2 * α * ((R : ℝ) - 2)) * K)
      atTop (𝓝 0) := by
    have hnat : Tendsto (fun R : ℕ => (R : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have haff : Tendsto (fun R : ℕ => 2 * α * ((R : ℝ) - 2))
        atTop atTop := by
      have hsub : Tendsto (fun R : ℕ => (R : ℝ) - 2) atTop atTop :=
        tendsto_atTop_add_const_right atTop (-2) hnat
      exact hsub.const_mul_atTop (by positivity)
    have hneg : Tendsto (fun R : ℕ => -(2 * α * ((R : ℝ) - 2)))
        atTop atBot :=
      tendsto_neg_atBot_iff.mpr haff
    have hexp : Tendsto
        (fun R : ℕ => Real.exp (-(2 * α * ((R : ℝ) - 2))))
        atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    simpa [neg_mul, mul_comm] using hexp.const_mul K
  have hev : ∀ᶠ R : ℕ in atTop,
      Real.exp (-2 * α * ((R : ℝ) - 2)) * K < ε :=
    (tendsto_order.1 hlim).2 _ hε
  exact hev.exists

/-- All-degree hard-core disappearance from the literal degree partition,
the fixed-ceiling inverse-square bound, and weighted Walsh localization. -/
theorem allDegree_corrector_disappears
    (degree : ∀ N, ι N → ℕ) (y : ∀ N, ι N → ℝ)
    (α ρ sourceNorm : ℝ) (weightedNorm : ℕ → ℝ)
    (C : ℕ → ℝ)
    (hy : ∀ N i, 0 ≤ y N i)
    (hα : 0 < α) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hsource : 0 ≤ sourceNorm)
    (hweightedNorm : ∀ N, 0 ≤ weightedNorm N)
    (hweighted : ∀ N, weightedNorm N ≤ sourceNorm / (1 - ρ))
    (hsq : ∀ N,
      ∑ i, Real.exp (2 * α * ((degree N i : ℝ) - 2)) * y N i
        ≤ weightedNorm N ^ 2)
    (_hC : ∀ R, 0 ≤ C R)
    (hlowBound : ∀ N R,
      lowMass degree y N R ≤ C R / (((N + 1 : ℕ) : ℝ) ^ 2)) :
    Tendsto (fun N => totalMass y N) atTop (𝓝 0) := by
  classical
  let total : ℕ → ℕ → ℝ := fun N _ => totalMass y N
  let low : ℕ → ℕ → ℝ := lowMass degree y
  let tail : ℕ → ℕ → ℝ := tailMass degree y
  apply NCG.hard_core_corrector_disappears total low tail
  · intro N R
    exact totalMass_eq_lowMass_add_tailMass degree y N R
  · intro R
    apply tendsto_zero_of_invSq_bound (fun N => low N R) (C R)
    · intro N
      exact Finset.sum_nonneg fun i hi => hy N i
    · intro N
      exact hlowBound N R
  · intro ε hε
    let K := (sourceNorm / (1 - ρ)) ^ 2
    have hK : 0 ≤ K := sq_nonneg _
    obtain ⟨R, hR⟩ :=
      exponentialDegreeTail_eventually_small hα hK hε
    refine ⟨R, fun N => ?_⟩
    have htail_nonneg : 0 ≤ tail N R :=
      Finset.sum_nonneg fun i hi => hy N i
    rw [abs_of_nonneg htail_nonneg]
    calc
      tail N R ≤ Real.exp (-2 * α * ((R : ℝ) - 2)) * K := by
        simpa [tail, tailMass, K] using
          (NCG.renewal_chaos_localization
            (fun i => (degree N i : ℝ)) (y N) (hy N)
            α (R : ℝ) ρ sourceNorm (weightedNorm N)
            (le_of_lt hα) hρ0 hρ hsource (hweightedNorm N)
            (hweighted N) (hsq N))
      _ ≤ ε := hR.le
  · intro N R S
    rfl

end NCG.HardCoreAllDegreeAssemblyExact
