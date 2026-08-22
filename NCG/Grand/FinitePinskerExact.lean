/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Pinsker's inequality for finite probability vectors

`pinsker`: for strictly positive probability vectors `q g : ι → ℝ` on a finite type,
`(∑ |q i - g i|)² ≤ 2 ∑ q i log(q i / g i)`.

The proof is the classical one: the log-sum inequality (Jensen for `x log x`) reduces
the relative entropy to the binary relative entropy of the masses of the set
`A = {q ≥ g}`, the total variation is `2 (q(A) - g(A))`, and the binary Pinsker
inequality `d(p ‖ r) ≥ 2 (p - r)²` follows from a monotonicity argument in `r`.
-/

open Finset Real

namespace NCG
namespace FinitePinsker

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- The relative entropy `∑ q log(q / g)`. -/
noncomputable def kl {ι : Type*} [Fintype ι] (q g : ι → ℝ) : ℝ := ∑ i, q i * log (q i / g i)

/-- The total variation norm `∑ |q - g|`. -/
noncomputable def tv {ι : Type*} [Fintype ι] (q g : ι → ℝ) : ℝ := ∑ i, |q i - g i|

/-- The binary relative entropy `d(p ‖ r)`. -/
noncomputable def binKl (p r : ℝ) : ℝ := p * log (p / r) + (1 - p) * log ((1 - p) / (1 - r))

/-! ### The binary Pinsker inequality -/

/-- `f r = d(p ‖ r) - 2 (p - r)²` written without quotients inside the logarithms. -/
noncomputable def binF (p r : ℝ) : ℝ :=
  p * (log p - log r) + (1 - p) * (log (1 - p) - log (1 - r)) - 2 * (p - r) ^ 2

theorem binF_eq {p r : ℝ} (hp : 0 < p) (hp1 : p < 1) (hr : 0 < r) (hr1 : r < 1) :
    binF p r = binKl p r - 2 * (p - r) ^ 2 := by
  unfold binF binKl
  rw [log_div hp.ne' hr.ne', log_div (by linarith) (by linarith)]

theorem hasDerivAt_binF (p : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (binF p) (-(p / r) + (1 - p) / (1 - r) + 4 * (p - r)) r := by
  have h1 : HasDerivAt (fun r : ℝ => log r) r⁻¹ r := Real.hasDerivAt_log hr.ne'
  have h2 : HasDerivAt (fun r : ℝ => log (1 - r)) (-1 / (1 - r)) r := by
    have := ((hasDerivAt_id r).const_sub 1).log (by simp only [id]; linarith)
    simpa using this
  have h3 : HasDerivAt (fun r : ℝ => 2 * (p - r) ^ 2) (2 * (2 * (p - r) * (-1))) r := by
    have := (((hasDerivAt_id r).const_sub p).pow 2).const_mul 2
    simpa using this
  have := ((((h1.const_sub (log p)).const_mul p).add
    ((h2.const_sub (log (1 - p))).const_mul (1 - p))).sub h3)
  refine this.congr_deriv ?_
  field_simp
  ring

/-- **Binary Pinsker**: `d(p ‖ r) ≥ 2 (p - r)²` for `p, r ∈ (0, 1)`. -/
theorem binKl_ge {p r : ℝ} (hp : 0 < p) (hp1 : p < 1) (hr : 0 < r) (hr1 : r < 1) :
    2 * (p - r) ^ 2 ≤ binKl p r := by
  have key : 0 ≤ binF p r := by
    have hderiv_sign : ∀ s : ℝ, 0 < s → s < 1 →
        (-(p / s) + (1 - p) / (1 - s) + 4 * (p - s)) = (s - p) * (1 / (s * (1 - s)) - 4) := by
      intro s hs hs1
      have h1 : s ≠ 0 := hs.ne'
      have h2 : (1 - s) ≠ 0 := by linarith
      field_simp
      ring
    have hbracket : ∀ s : ℝ, 0 < s → s < 1 → 0 ≤ 1 / (s * (1 - s)) - 4 := by
      intro s hs hs1
      have hpos : 0 < s * (1 - s) := mul_pos hs (by linarith)
      have : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
      rw [sub_nonneg, le_div_iff₀ hpos]
      linarith
    have hF0 : binF p p = 0 := by unfold binF; ring
    rcases le_or_gt p r with hpr | hpr
    · -- monotone on `[p, r]`
      have hmono : MonotoneOn (binF p) (Set.Icc p r) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
        · intro x hx
          exact (hasDerivAt_binF p (by linarith [hx.1])
            (by linarith [hx.2])).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hasDerivAt_binF p (by linarith [hx.1])
            (by linarith [hx.2])).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hasDerivAt_binF p (by linarith [hx.1]) (by linarith [hx.2])).deriv,
            hderiv_sign x (by linarith [hx.1]) (by linarith [hx.2])]
          exact mul_nonneg (by linarith [hx.1])
            (hbracket x (by linarith [hx.1]) (by linarith [hx.2]))
      have := hmono ⟨le_rfl, hpr⟩ ⟨hpr, le_rfl⟩ hpr
      rwa [hF0] at this
    · -- antitone on `[r, p]`
      have hanti : AntitoneOn (binF p) (Set.Icc r p) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
        · intro x hx
          exact (hasDerivAt_binF p (by linarith [hx.1])
            (by linarith [hx.2])).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hasDerivAt_binF p (by linarith [hx.1])
            (by linarith [hx.2])).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hasDerivAt_binF p (by linarith [hx.1]) (by linarith [hx.2])).deriv,
            hderiv_sign x (by linarith [hx.1]) (by linarith [hx.2])]
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2])
            (hbracket x (by linarith [hx.1]) (by linarith [hx.2]))
      have := hanti ⟨le_rfl, hpr.le⟩ ⟨hpr.le, le_rfl⟩ hpr.le
      rwa [hF0] at this
  rw [binF_eq hp hp1 hr hr1] at key
  linarith

/-! ### The log-sum inequality -/

/-- **Log-sum inequality** on a nonempty subset: `∑_S q log(q/g) ≥ q(S) log(q(S)/g(S))`. -/
theorem logsum {ι : Type*} [Fintype ι] {q g : ι → ℝ} (hq : ∀ i, 0 < q i) (hg : ∀ i, 0 < g i)
    (S : Finset ι) (hS : S.Nonempty) :
    (∑ i ∈ S, q i) * log ((∑ i ∈ S, q i) / ∑ i ∈ S, g i)
      ≤ ∑ i ∈ S, q i * log (q i / g i) := by
  set P := ∑ i ∈ S, q i with hP
  set G := ∑ i ∈ S, g i with hG
  have hGpos : 0 < G := sum_pos (fun i _ => hg i) hS
  have hPpos : 0 < P := sum_pos (fun i _ => hq i) hS
  -- Jensen for `x ↦ x log x` with weights `g i / G` at the points `q i / g i`
  have hj := Real.convexOn_mul_log.map_sum_le (t := S) (w := fun i => g i / G)
    (p := fun i => q i / g i) (fun i _ => (div_pos (hg i) hGpos).le)
    (by rw [← sum_div, div_self hGpos.ne'])
    (fun i _ => Set.mem_Ici.mpr (div_pos (hq i) (hg i)).le)
  have hmean : ∑ i ∈ S, (g i / G) • (q i / g i) = P / G := by
    rw [hP, sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul]
    have := (hg i).ne'
    field_simp
  rw [hmean] at hj
  simp only [smul_eq_mul] at hj
  have : ∑ i ∈ S, g i / G * (q i / g i * log (q i / g i))
      = (∑ i ∈ S, q i * log (q i / g i)) / G := by
    rw [sum_div]
    refine sum_congr rfl fun i _ => ?_
    have := (hg i).ne'
    field_simp
  rw [this, le_div_iff₀ hGpos] at hj
  calc P * log (P / G) = P / G * log (P / G) * G := by field_simp
    _ ≤ _ := hj

/-! ### Pinsker -/

/-- **Pinsker's inequality** for strictly positive finite probability vectors:
`(∑ |q - g|)² ≤ 2 ∑ q log(q / g)`. -/
theorem pinsker {ι : Type*} [Fintype ι] [DecidableEq ι] {q g : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hg : ∀ i, 0 < g i) (hq1 : ∑ i, q i = 1) (hg1 : ∑ i, g i = 1) :
    tv q g ^ 2 ≤ 2 * kl q g := by
  classical
  haveI : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hq1
  set A : Finset ι := univ.filter fun i => g i ≤ q i with hA
  -- the masses of `A`
  set P := ∑ i ∈ A, q i with hP
  set G := ∑ i ∈ A, g i with hG
  have hsplit_q : ∑ i ∈ A, q i + ∑ i ∈ Aᶜ, q i = 1 := by rw [sum_add_sum_compl, hq1]
  have hsplit_g : ∑ i ∈ A, g i + ∑ i ∈ Aᶜ, g i = 1 := by rw [sum_add_sum_compl, hg1]
  -- total variation
  have htv : tv q g = 2 * (P - G) := by
    unfold tv
    rw [← sum_add_sum_compl A]
    have h1 : ∑ i ∈ A, |q i - g i| = ∑ i ∈ A, (q i - g i) :=
      sum_congr rfl fun i hi => abs_of_nonneg (by rw [hA, mem_filter] at hi; linarith [hi.2])
    have h2 : ∑ i ∈ Aᶜ, |q i - g i| = ∑ i ∈ Aᶜ, (g i - q i) :=
      sum_congr rfl fun i hi => by
        rw [mem_compl, hA, mem_filter] at hi
        push Not at hi
        rw [abs_of_neg (by linarith [hi (mem_univ i)])]
        ring
    rw [h1, h2, sum_sub_distrib, sum_sub_distrib]
    linarith
  -- `A` is nonempty
  have hAne : A.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have : ∀ i, q i < g i := fun i => by
      by_contra h
      push Not at h
      have : i ∈ A := by rw [hA, mem_filter]; exact ⟨mem_univ i, h⟩
      rw [hne] at this
      exact absurd this (notMem_empty i)
    have := sum_lt_sum_of_nonempty univ_nonempty fun i _ => this i
    · rw [hq1, hg1] at this; exact lt_irrefl _ this
  by_cases hAc : Aᶜ.Nonempty
  · -- both masses are strictly between `0` and `1`
    have hPpos : 0 < P := sum_pos (fun i _ => hq i) hAne
    have hGpos : 0 < G := sum_pos (fun i _ => hg i) hAne
    have hP1 : P < 1 := by
      have : 0 < ∑ i ∈ Aᶜ, q i := sum_pos (fun i _ => hq i) hAc
      linarith
    have hG1 : G < 1 := by
      have : 0 < ∑ i ∈ Aᶜ, g i := sum_pos (fun i _ => hg i) hAc
      linarith
    -- log-sum on both parts
    have hl1 := logsum hq hg A hAne
    have hl2 := logsum hq hg Aᶜ hAc
    have hqc : ∑ i ∈ Aᶜ, q i = 1 - P := by linarith
    have hgc : ∑ i ∈ Aᶜ, g i = 1 - G := by linarith
    rw [hqc, hgc] at hl2
    have hkl : kl q g = ∑ i ∈ A, q i * log (q i / g i) + ∑ i ∈ Aᶜ, q i * log (q i / g i) := by
      unfold kl; rw [sum_add_sum_compl]
    have hbin : binKl P G ≤ kl q g := by
      rw [hkl]; unfold binKl; linarith
    have hpin := binKl_ge hPpos hP1 hGpos hG1
    rw [htv]
    nlinarith
  · -- `Aᶜ = ∅`: `q ≥ g` everywhere with equal totals, so `q = g`
    rw [not_nonempty_iff_eq_empty] at hAc
    have hqg : ∀ i, q i = g i := by
      intro i
      have hi : i ∈ A := by
        by_contra h
        have : i ∈ Aᶜ := mem_compl.mpr h
        rw [hAc] at this
        exact absurd this (notMem_empty i)
      rw [hA, mem_filter] at hi
      by_contra hne
      have hlt : g i < q i := lt_of_le_of_ne hi.2 (Ne.symm hne)
      have hle : ∀ j ∈ univ, g j ≤ q j := fun j _ => by
        have hj : j ∈ A := by
          by_contra h
          have : j ∈ Aᶜ := mem_compl.mpr h
          rw [hAc] at this
          exact absurd this (notMem_empty j)
        rw [hA, mem_filter] at hj
        exact hj.2
      have := sum_lt_sum hle ⟨i, mem_univ i, hlt⟩
      rw [hq1, hg1] at this
      exact lt_irrefl _ this
    have htv0 : tv q g = 0 := by unfold tv; simp [hqg]
    have hkl0 : kl q g = 0 := by unfold kl; simp [hqg]
    rw [htv0, hkl0]; norm_num

end FinitePinsker
end NCG
