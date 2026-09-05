/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Parameter-free action marginality selects `D = 4`
  (`thm:action-marginality-updated`, SM_emergence)

The canonically normalized microscopic action scales as
`S_h ~ (h⁴/h^D)·c` with `c > 0` the curvature integral.  The
continuum-limit trichotomy:

* `marginality_vanishes` — for `D < 4` the limit is `0`;
* `marginality_diverges` — for `D > 4` the action diverges;
* `marginality_critical` — for `D = 4` the action is identically `c`
  on the physical cutoff range;
* `action_marginality_selects` — if the limit exists, is finite and
  nonzero, then `D = 4` (hence `d = D - 1 = 3`): the unique
  rank-four selector, with no inserted cutoff power.
-/

namespace NCG

open Filter Set

/-- The cutoff scaling of the canonically normalized action. -/
noncomputable def actionScale (D : ℕ) (c : ℝ) (h : ℝ) : ℝ :=
  h ^ 4 / h ^ D * c

/-- For `D < 4` the continuum limit vanishes. -/
theorem marginality_vanishes {D : ℕ} (hD : D < 4) (c : ℝ) :
    Tendsto (actionScale D c) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcongr : ∀ h ∈ Ioi (0 : ℝ),
      actionScale D c h = h ^ (4 - D) * c := by
    intro h hh
    unfold actionScale
    rw [pow_sub₀ h (ne_of_gt hh) hD.le]
    ring
  have hbase : Tendsto (fun h : ℝ => h ^ (4 - D) * c)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hk : 1 ≤ 4 - D := by omega
    have h1 : Tendsto (fun h : ℝ => h ^ (4 - D))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have hcont : Tendsto (fun h : ℝ => h ^ (4 - D)) (nhds 0)
          (nhds ((0 : ℝ) ^ (4 - D))) :=
        (continuous_pow (4 - D)).tendsto 0
      rw [zero_pow (by omega : 4 - D ≠ 0)] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    simpa using h1.mul_const c
  exact hbase.congr' (by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (hcongr h hh).symm)

/-- For `D > 4` the action diverges (positive curvature integral). -/
theorem marginality_diverges {D : ℕ} (hD : 4 < D) {c : ℝ}
    (hc : 0 < c) :
    Tendsto (actionScale D c) (nhdsWithin 0 (Ioi 0)) atTop := by
  have hcongr : ∀ h ∈ Ioi (0 : ℝ),
      actionScale D c h = c * (h ^ (D - 4))⁻¹ := by
    intro h hh
    unfold actionScale
    rw [pow_sub₀ h (ne_of_gt hh) hD.le]
    field_simp
  have hpow : Tendsto (fun h : ℝ => h ^ (D - 4))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : Tendsto (fun h : ℝ => h ^ (D - 4)) (nhds 0)
          (nhds ((0 : ℝ) ^ (D - 4))) :=
        (continuous_pow (D - 4)).tendsto 0
      rw [zero_pow (by omega : D - 4 ≠ 0)] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact pow_pos (Set.mem_Ioi.mp hh) _
  have hinv : Tendsto (fun h : ℝ => (h ^ (D - 4))⁻¹)
      (nhdsWithin 0 (Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hpow
  have := hinv.const_mul_atTop hc
  exact this.congr' (by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (hcongr h hh).symm)

/-- At `D = 4` the action is identically the curvature integral on
the physical cutoff range. -/
theorem marginality_critical (c : ℝ) {h : ℝ} (hh : 0 < h) :
    actionScale 4 c h = c := by
  unfold actionScale
  field_simp

/-- `thm:action-marginality-updated`: a finite nonzero continuum
limit with no inserted cutoff power forces `D = 4` (hence `d = 3`). -/
theorem action_marginality_selects {D : ℕ} {c L : ℝ} (hc : 0 < c)
    (hL : L ≠ 0)
    (hlim : Tendsto (actionScale D c) (nhdsWithin 0 (Ioi 0))
      (nhds L)) :
    D = 4 ∧ D - 1 = 3 := by
  have hD : D = 4 := by
    rcases lt_trichotomy D 4 with h | h | h
    · exfalso
      have h0 := marginality_vanishes h c
      have := tendsto_nhds_unique hlim h0
      exact hL this
    · exact h
    · exact absurd (marginality_diverges h hc)
        (hlim.not_tendsto (disjoint_nhds_atTop L))
  exact ⟨hD, by omega⟩

end NCG
