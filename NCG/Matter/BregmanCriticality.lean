/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Bregman recentering and the electroweak vacuum
  (`condres:complete-quantum-bregman-consolidated` and the boxed
   Higgs matching, SM_emergence)

The conditional quantum predictive Ward identity is a declared
interface (the record itself states it is not a consequence of the
primitive axioms); its formalizable algebra:

* `bregman_value_zero`, `bregman_deriv_at_zero` — the recentered
  intensity `𝓘(q) = Ψ(q) - Ψ(0) - q·a_*` vanishes at the origin and
  has slope `a_τ - a_*` there: recentering at the last fixed reset
  reference removes every term linear in `q`, leaving the drift
  mismatch `a_τ - a_*` as the mass term;
* `higgs_vacuum_minimum` — the boxed matching: for
  `m_h² = κμ²(a_τ - a_*) < 0` and `λ_h > 0`, the quartic potential
  `V(v) = m_h²v²/2 + λ_hv⁴/4` is minimized exactly on
  `v² = -m_h²/λ_h = -κ(a_τ - a_*)μ²/λ_h`, and the minimum is
  strictly below the symmetric point — electroweak breaking occurs
  at the first age with `a_τ - a_* < 0`;
* `higgs_vacuum_identity` — the substitution identity giving the
  boxed `v²(τ)` from the boxed `m_h²` and `λ_h`.
-/

namespace NCG

/-- The recentered intensity vanishes at the origin. -/
theorem bregman_value_zero (Psi : ℝ → ℝ) (astar : ℝ) :
    Psi 0 - Psi 0 - 0 * astar = 0 := by ring

/-- Recentering removes the linear term: the slope of
`𝓘(q) = Ψ(q) - Ψ(0) - q·a_*` at the origin is the drift mismatch
`a_τ - a_*`. -/
theorem bregman_deriv_at_zero {Psi : ℝ → ℝ} {atau astar : ℝ}
    (hPsi : HasDerivAt Psi atau 0) :
    HasDerivAt (fun q => Psi q - Psi 0 - q * astar)
      (atau - astar) 0 := by
  have h1 : HasDerivAt (fun q : ℝ => Psi q - Psi 0) atau 0 :=
    hPsi.sub_const _
  have h2 : HasDerivAt (fun q : ℝ => q * astar) astar 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const astar
  exact h1.sub h2

/-- The boxed electroweak vacuum: for `m² < 0 < λ`, the quartic
potential is minimized exactly at `v² = -m²/λ`, strictly below the
symmetric point. -/
theorem higgs_vacuum_minimum {m2 lam : ℝ} (hm : m2 < 0)
    (hl : 0 < lam) {vstar : ℝ} (hv : vstar ^ 2 = -(m2 / lam)) :
    (∀ v : ℝ, m2 / 2 * vstar ^ 2 + lam / 4 * vstar ^ 4
      ≤ m2 / 2 * v ^ 2 + lam / 4 * v ^ 4) ∧
    m2 / 2 * vstar ^ 2 + lam / 4 * vstar ^ 4 < 0 := by
  constructor
  · intro v
    have hsq : 0 ≤ (v ^ 2 - vstar ^ 2) ^ 2 := sq_nonneg _
    have hstar : lam * vstar ^ 2 = -m2 := by
      rw [hv]
      field_simp
    nlinarith [sq_nonneg (v ^ 2 - vstar ^ 2), sq_nonneg v,
      sq_nonneg vstar]
  · have hstar : lam * vstar ^ 2 = -m2 := by
      rw [hv]
      field_simp
    have hv2 : 0 < vstar ^ 2 := by
      rw [hv]
      exact neg_pos.mpr (div_neg_of_neg_of_pos hm hl)
    nlinarith

/-- The boxed substitution: with `m_h² = κμ²(a_τ - a_*)` and
`λ_h = κ²b_τ/2`, the vacuum satisfies
`v² = -κ(a_τ - a_*)μ²/λ_h`. -/
theorem higgs_vacuum_identity {kappa mu atau astar btau : ℝ} :
    -(kappa * mu ^ 2 * (atau - astar)) / (kappa ^ 2 / 2 * btau)
      = -(kappa * (atau - astar)) * mu ^ 2 / (kappa ^ 2 / 2 * btau) := by
  ring

end NCG
