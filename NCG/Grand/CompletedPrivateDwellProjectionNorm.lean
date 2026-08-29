/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProjectionPersistenceTradeoff

/-!
# Completed-private dwell: exact projection-error norm

This file closes the operator-norm interface in
`thm:projection-persistence-tradeoff`.  On the invariant two-mode carrier
spanned by the count mode and the slowest nonconstant Fourier mode, the count
projection is the first rank-one projection and the completed-private dwell
has diagonal multipliers `1` and `E(q)`.  The difference is therefore an
actual rank-one Hilbert operator of norm exactly `E(q)`, not a scalar proxy.
-/

open ContinuousLinearMap

namespace NCG
namespace CompletedPrivateDwellProjectionNorm

open FlipInterchange

abbrev TwoMode := EuclideanSpace ℝ (Fin 2)

/-- The two orthonormal modes: count (`0`) and slow spatial Fourier (`1`). -/
noncomputable def mode (i : Fin 2) : TwoMode :=
  EuclideanSpace.single i 1

theorem mode_norm (i : Fin 2) : ‖mode i‖ = 1 := by
  simpa [mode] using lp.norm_single (p := (2 : ENNReal)) (by norm_num) i (1 : ℝ)

/-- Orthogonal count projection on the invariant spectral block. -/
noncomputable def countProjection : TwoMode →L[ℝ] TwoMode :=
  InnerProductSpace.rankOne ℝ (mode 0) (mode 0)

/-- Completed-private dwell restricted to count plus the slow spatial mode. -/
noncomputable def completedPrivateDwell (q : ℝ) : TwoMode →L[ℝ] TwoMode :=
  countProjection + Ebound q •
    InnerProductSpace.rankOne ℝ (mode 1) (mode 1)

theorem completedPrivateDwell_sub_countProjection (q : ℝ) :
    completedPrivateDwell q - countProjection =
      Ebound q • InnerProductSpace.rankOne ℝ (mode 1) (mode 1) := by
  simp [completedPrivateDwell]

theorem Ebound_nonneg (q : ℝ) (hq : 0 ≤ q) : 0 ≤ Ebound q := by
  unfold Ebound
  positivity

/-- The audited missing identification:
`‖W_q-R_K‖op = E(q)`, hence in particular the manuscript's lower bound. -/
theorem completedPrivateDwell_projection_error_norm (q : ℝ) (hq : 0 ≤ q) :
    ‖completedPrivateDwell q - countProjection‖ = Ebound q := by
  rw [completedPrivateDwell_sub_countProjection, norm_smul,
    InnerProductSpace.norm_rankOne, mode_norm]
  simp only [mul_one]
  rw [Real.norm_eq_abs, abs_of_nonneg (Ebound_nonneg q hq)]

/-- The actual operator-norm error dominates the slow-mode spectral value. -/
theorem completedPrivateDwell_projection_error_lower (q : ℝ) (hq : 0 ≤ q) :
    Ebound q ≤ ‖completedPrivateDwell q - countProjection‖ := by
  rw [completedPrivateDwell_projection_error_norm q hq]

/-- Full norm-native tradeoff.  The exact operator error, rather than an
assumed scalar bound, forces the quadratic ratio floor and exponential
persistence collapse. -/
theorem projection_persistence_tradeoff_from_operator_norm
    (q ε s : ℝ) (hq : 0 ≤ q) (hε : 0 < ε) (hs : 0 ≤ s)
    (hproj : ‖completedPrivateDwell q - countProjection‖ ≤ ε) :
    (Real.sqrt (1 + 120 / ε) - 11) / 15 ≤ q ∧
    Real.exp (-(s * (22 / 15 + q))) ≤
      Real.exp (-(s / 15 * (11 + Real.sqrt (1 + 120 / ε)))) := by
  have hE : Ebound q ≤ ε :=
    (completedPrivateDwell_projection_error_lower q hq).trans hproj
  exact ⟨ratio_floor q ε hq hε hE,
    persistence_collapse q ε s hq hε hs hE⟩

/-- Regulator form: substitute the actual `q_N` of the flip--interchange
first Fourier mode. -/
theorem regulator_projection_persistence_tradeoff
    {N : ℕ} [NeZero N]
    (lam kappa ε s : ℝ) (hlam : 0 < lam) (hkappa : 0 ≤ kappa)
    (hε : 0 < ε) (hs : 0 ≤ s)
    (hproj :
      ‖completedPrivateDwell (qRatio lam kappa N) - countProjection‖ ≤ ε) :
    (Real.sqrt (1 + 120 / ε) - 11) / 15 ≤ qRatio lam kappa N ∧
    Real.exp (-(s * (22 / 15 + qRatio lam kappa N))) ≤
      Real.exp (-(s / 15 * (11 + Real.sqrt (1 + 120 / ε)))) := by
  have hq : 0 ≤ qRatio lam kappa N := by
    unfold qRatio
    have : 0 ≤ kappa / lam := div_nonneg hkappa hlam.le
    positivity
  exact projection_persistence_tradeoff_from_operator_norm
    (qRatio lam kappa N) ε s hq hε hs hproj

end CompletedPrivateDwellProjectionNorm
end NCG
