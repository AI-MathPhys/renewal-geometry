/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite gauge–matter source certificate bridge
  (`thm:finite-SM-bridge`, flagship manuscript)

The provable assembly under the six displayed certificates
(current writer, KMS balance, incidence Ward, rank-one Majorana,
Higgs reality, source-response nondegeneracy):

* `bridge_coupling_matching`: one common current writer and KMS
  normalization make the three sector Grams equal, so the bare
  couplings match — `g₁ = g₂ = g₃`;
* `weak_angle`: the canonical hypercharge level `k_Y = 5/3`
  (the trace normalization `1/g_Y² = 1/g² + 2/(3g²)`) gives
  `g_Y² = (3/5)g²` and `sin²θ_W = g_Y²/(g² + g_Y²) = 3/8`;
* `one_generation_numerics`: the one-generation table passes the
  `ℤ₆` kernel congruence and all five anomaly sums plus Witten
  parity — the finite representation/trace computations of the
  listed quotient and anomaly freedom;
* `saturation_removal`: with the loaded Krylov head saturating
  the retained space (`thm:primitive-sector-saturation`,
  displayed as `K = ⊤`), every future-invisible ambient summand
  (`N ≤ Kᗮ`) vanishes;
* `finite_sm_bridge`: the bundle.

Rendering disclosed: the identification of each certificate with
its finite gauge–matter record (Pati–Salam parent, descent,
hypercharge direction `Y = T³_R + (B-L)/2`, one-Higgs-doublet
reduction, four Yukawa channel types) is the cited SM-branch
ledger; per the manuscript's continuum firewall, no interacting
renormalized continuum Standard Model, running couplings, Higgs
minimum, or flavour parameters are claimed.
-/

namespace NCG

/-- One common current writer and KMS normalization: equal
sector Grams force equal positive couplings. -/
theorem bridge_coupling_matching (g : Fin 3 → ℝ) (c : ℝ)
    (hpos : ∀ i, 0 < g i) (hgram : ∀ i, g i ^ 2 = c) :
    g 0 = g 1 ∧ g 1 = g 2 := by
  have key : ∀ i j, g i = g j := by
    intro i j
    have hsq : g i ^ 2 = g j ^ 2 := by
      rw [hgram i, hgram j]
    have hfac : (g i - g j) * (g i + g j) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · nlinarith [hpos i, hpos j]
  exact ⟨key 0 1, key 1 2⟩

/-- The canonical level `k_Y = 5/3`: the trace normalization
gives `5g_Y² = 3g²` and the boxed weak angle
`sin²θ_W = g_Y²/(g² + g_Y²) = 3/8`. -/
theorem weak_angle (g gY : ℝ) (hg : 0 < g) (hgY : 0 < gY)
    (hrel : 1 / gY ^ 2 = 1 / g ^ 2 + 2 / (3 * g ^ 2)) :
    5 * gY ^ 2 = 3 * g ^ 2
    ∧ gY ^ 2 / (g ^ 2 + gY ^ 2) = 3 / 8 := by
  have hg2 : g ^ 2 ≠ 0 := by positivity
  have hgY2 : gY ^ 2 ≠ 0 := by positivity
  have h5 : 1 / gY ^ 2 = 5 / (3 * g ^ 2) := by
    rw [hrel]
    field_simp
    ring
  have hmatch : 5 * gY ^ 2 = 3 * g ^ 2 := by
    field_simp at h5
    linarith
  refine ⟨hmatch, ?_⟩
  have hden : g ^ 2 + gY ^ 2 ≠ 0 := by positivity
  field_simp
  linarith [hmatch]

/-- The one-generation table: `ℤ₆` kernel congruence, the five
anomaly sums, and Witten parity. -/
theorem one_generation_numerics :
    (∀ r ∈ [((1 : ℤ), (1 : ℤ), (1 : ℤ)),
        (0, 1, -3), (-1, 0, -4), (-1, 0, 2),
        (0, 0, 6), (0, 0, 0)],
      (6 : ℤ) ∣ 2 * r.1 + 3 * r.2.1 + r.2.2)
    ∧ (((2 : ℚ) * 1 + 1 * (-1) + 1 * (-1) = 0)
      ∧ ((2 : ℚ) * (1/2) * (1/6) + (1/2) * (-2/3)
          + (1/2) * (1/3) = 0)
      ∧ ((3 : ℚ) * (1/2) * (1/6) + (1/2) * (-1/2) = 0)
      ∧ ((6 : ℚ) * (1/6)^3 + 3 * (-2/3)^3 + 3 * (1/3)^3
          + 2 * (-1/2)^3 + 1^3 = 0)
      ∧ ((6 : ℚ) * (1/6) + 3 * (-2/3) + 3 * (1/3)
          + 2 * (-1/2) + 1 = 0)
      ∧ (3 + 1) % 2 = 0) := by
  constructor
  · decide
  · norm_num

/-- Sector-saturation removal: with the loaded head saturating
the retained space, every future-invisible ambient summand
vanishes. -/
theorem saturation_removal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (K N : Submodule ℂ E)
    (hsat : K = ⊤) (hinv : N ≤ Kᗮ) : N = ⊥ := by
  rw [hsat, Submodule.top_orthogonal_eq_bot] at hinv
  exact le_bot_iff.mp hinv

/-- `thm:finite-SM-bridge`: the assembled bridge — under the six
displayed certificates, the couplings match, the weak angle is
`3/8`, the one-generation table passes its kernel and anomaly
audits, and every unused ambient sector is removed. -/
theorem finite_sm_bridge (g : Fin 3 → ℝ) (c : ℝ)
    -- current-writer/KMS certificates: one common Gram
    (hpos : ∀ i, 0 < g i)
    (hgram : ∀ i, g i ^ 2 = c)
    -- hypercharge normalization certificate: k_Y = 5/3
    (gY : ℝ) (hgY : 0 < gY)
    (hrel : 1 / gY ^ 2 = 1 / (g 0) ^ 2 + 2 / (3 * (g 0) ^ 2))
    -- saturation certificate (`thm:primitive-sector-saturation`)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K N : Submodule ℂ E) (hsat : K = ⊤) (hinv : N ≤ Kᗮ) :
    (g 0 = g 1 ∧ g 1 = g 2)
    ∧ (5 * gY ^ 2 = 3 * (g 0) ^ 2
      ∧ gY ^ 2 / ((g 0) ^ 2 + gY ^ 2) = 3 / 8)
    ∧ ((∀ r ∈ [((1 : ℤ), (1 : ℤ), (1 : ℤ)),
          (0, 1, -3), (-1, 0, -4), (-1, 0, 2),
          (0, 0, 6), (0, 0, 0)],
        (6 : ℤ) ∣ 2 * r.1 + 3 * r.2.1 + r.2.2))
    ∧ N = ⊥ :=
  ⟨bridge_coupling_matching g c hpos hgram,
    weak_angle (g 0) gY (hpos 0) hgY hrel,
    one_generation_numerics.1,
    saturation_removal K N hsat hinv⟩

end NCG
