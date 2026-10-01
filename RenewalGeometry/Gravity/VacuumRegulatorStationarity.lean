/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.RenewalFriedmannExact
import RenewalGeometry.Gravity.VacuumRegulatorAssembly

/-!
# The flat and de Sitter regulator profiles solve the renewal Euler system
(`mt:vacuum` (i), first half; emergent-spacetime manuscript)

`desitterProfile_isStationaryRenewalSolution`: for every Hubble rate `H` the profile
`a(t) = e^{H t}`, lapse `N = 1`, proper time `τ = t`, is a positive connected stationary solution
of the lapse-varied homogeneous renewal-rate action of `thm:main-homogeneous-friedmann` with
`Λ = 3H²` — both Euler expressions `E_u` (lapse/conductance) and `E_v` (density) vanish
identically on `ℝ`.  `H = 0` is the flat branch.  `vacuum_regulator_assembly_with_stationarity`
adds this clause to `VacuumRegulatorAssembly.vacuum_regulator_assembly`.
-/

open Filter

namespace RenewalGeometry

namespace VacuumRegulatorStationarity

/-- The regulator scale factor `a(t) = e^{H t}`. -/
noncomputable def profile (H : ℝ) (t : ℝ) : ℝ := Real.exp (H * t)

theorem logDensity_profile (H : ℝ) : logDensity (profile H) = fun t => 3 * H * t := by
  funext t
  unfold logDensity profile
  rw [← Real.exp_nat_mul, Real.log_exp]
  push_cast
  ring

theorem logConductance_profile (H : ℝ) :
    logConductance (profile H) (fun _ => 1) = fun t => -2 * H * t := by
  funext t
  unfold logConductance profile
  rw [one_pow, one_div, ← Real.exp_nat_mul, ← Real.exp_neg, Real.log_exp]
  push_cast
  ring

theorem hasDerivAt_linear (c t : ℝ) : HasDerivAt (fun t => c * t) c t := by
  simpa using (hasDerivAt_id t).const_mul c

/-- **`mt:vacuum` (i), first half.**  The flat (`H = 0`) and de Sitter regulator profile
`a = e^{H t}`, `N = 1`, `τ = t` solves the lapse-varied renewal Euler system of
`thm:main-homogeneous-friedmann` with `Λ = 3H²`. -/
theorem desitterProfile_isStationaryRenewalSolution (H : ℝ) :
    IsStationaryRenewalSolution (3 * H ^ 2) Set.univ (profile H) (fun t => H * profile H t)
      (fun _ => 1) id := by
  have hv : logDensity (profile H) = fun t => 3 * H * t := logDensity_profile H
  have hu : logConductance (profile H) (fun _ => 1) = fun t => -2 * H * t :=
    logConductance_profile H
  refine ⟨isOpen_univ, isPreconnected_univ, fun t _ => Real.exp_pos _, fun _ _ => one_pos,
    fun t _ => ?_, fun t _ => hasDerivAt_id t, ?_, continuousOn_const, fun t _ => ?_⟩
  · unfold profile
    simpa [mul_comm] using ((hasDerivAt_linear H t).exp)
  · exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      continuous_id))).continuousOn
  · rw [hu, hv]
    have du : deriv (fun t => -2 * H * t) = fun _ => -2 * H := by
      funext s; exact (hasDerivAt_linear _ s).deriv
    have dv : deriv (fun t => 3 * H * t) = fun _ => 3 * H := by
      funext s; exact (hasDerivAt_linear _ s).deriv
    rw [du, dv]
    rw [renewal_stationary_iff_friedmann (3 * H ^ 2) (v'' := fun _ => 0)
      (by simpa using hasDerivAt_linear (-2 * H) t) (by simpa using hasDerivAt_linear (3 * H) t)
      (hasDerivAt_const t _)]
    have hH : hubbleRate (renewalScaleFactor fun t => 3 * H * t)
        (renewalScaleFactorDeriv (fun t => 3 * H * t) fun _ => 3 * H)
        (renewalLapse (fun t => -2 * H * t) fun t => 3 * H * t) = fun _ => H := by
      funext s
      unfold hubbleRate renewalScaleFactor renewalScaleFactorDeriv renewalLapse
      rw [show -2 * H * s / 2 + 3 * H * s / 3 = 0 by ring, Real.exp_zero, one_mul]
      have := Real.exp_pos (3 * H * s / 3)
      field_simp
    refine ⟨by rw [hH], ?_⟩
    unfold properTimeDeriv
    rw [hH, deriv_const, mul_zero]

/-- `mt:vacuum` with clause (i) complete: the de Sitter profile solves the renewal Euler
system (`desitterProfile_isStationaryRenewalSolution`), together with all clauses of
`VacuumRegulatorAssembly.vacuum_regulator_assembly` (finite-to-continuum half of (i), (ii)–(vi)). -/
theorem vacuum_regulator_assembly_with_stationarity (H : ℝ) (hH : 0 ≤ H) :
    IsStationaryRenewalSolution (3 * H ^ 2) Set.univ (profile H) (fun t => H * profile H t)
      (fun _ => 1) id ∧
    (∀ (σ b h : ℝ), 0 < H → (σ = 1 ∨ σ = -1) → 0 ≤ b → b < 1 → (3 * H / 2) * h / 2 ≤ b →
      ∀ (M : ℕ) (q s : ℕ → ℝ), 0 < q 0 → (∀ j < M, 0 < s j) → (∀ j < M, s j ≤ h) →
        FiniteHomogeneousStationarity.SatisfiesRecurrence (3 * H / 2) σ M q s →
        ∀ j ≤ M, |Real.log (q j ^ (2 / 3 : ℝ) / q 0 ^ (2 / 3 : ℝ)) -
            σ * H * FiniteHomogeneousStationarity.renewalTime s j|
          ≤ (2 / 3) * ((3 * H / 2) ^ 3 * FiniteHomogeneousStationarity.renewalTime s M * h ^ 2 /
            (12 * (1 - b ^ 2)))) ∧
    (∀ t, RelationalDeSitterBranch.speedDensity H t = Real.exp (3 * H * t) ∧
      RelationalDeSitterBranch.spatialMetric H t = Real.exp (2 * H * t) • 1 ∧
      RelationalDeSitterBranch.lapse H t = 1 ∧ RelationalDeSitterBranch.shift H t = 0) ∧
    (∀ t, RelationalDeSitterBranch.ricciTensor H t -
        (RelationalDeSitterBranch.scalarCurvature H / 2) • RelationalDeSitterBranch.lorentzMetric H t
        + RelationalDeSitterBranch.cosmologicalCoefficient H •
          RelationalDeSitterBranch.lorentzMetric H t = 0) ∧
    RelationalDeSitterBranch.cosmologicalCoefficient H = 3 * H ^ 2 ∧
    Summable (RelationalDeSitterBranch.normalizedTorsionDefect H) ∧
    Summable (RelationalDeSitterBranch.normalizedCurvatureDefect H) ∧
    Summable (RelationalDeSitterBranch.normalizedPalatiniDefect H) := by
  obtain ⟨h1, h2, -, -, h3, h4, -, -, -, -, h5, h6, h7⟩ :=
    VacuumRegulatorAssembly.vacuum_regulator_assembly H hH
  exact ⟨desitterProfile_isStationaryRenewalSolution H, h1, h2, h3, h4, h5, h6, h7⟩

end VacuumRegulatorStationarity

end RenewalGeometry
