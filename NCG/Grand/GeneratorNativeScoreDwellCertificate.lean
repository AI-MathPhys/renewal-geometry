/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CollisionSinkUniformization
import NCG.Grand.ScoreDwellSpectralAssembly
import NCG.Grand.GeneratorNativeRenewal

/-!
# Generator-native score--dwell renewal certificate

This module assembles the actual fresh collision, the global score--dwell
spectral calculation, and the one-way transient sink.  Unlike the earlier
interface theorem, the fair branch effects are derived from the collision
Kraus operators and the contraction factor is the norm of the explicitly
assembled residual multiplier vector.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NCG

/-- Each physical fresh-collision branch has effect `I/2` and therefore Born
probability `1/2` on every unit vector. -/
theorem freshCollision_branch_probability
    (m : ℤ) (hm : m = 1 ∨ m = -1) (v : Fin 2 → ℂ)
    (hv : star v ⬝ᵥ v = 1) :
    (collideK m)ᴴ * collideK m = (1 / 2 : ℂ) • 1
    ∧ star v ⬝ᵥ (((collideK m)ᴴ * collideK m) *ᵥ v) = 2⁻¹ := by
  have heffect := (one_clock_score_collision_exact.2 m hm
    (0 : Matrix (Fin 2) (Fin 2) ℂ)).1
  refine ⟨heffect, ?_⟩
  rw [heffect, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, hv, smul_eq_mul, mul_one]
  norm_num

/-- Exact one-cutoff generator-native certificate.  The autonomous occurrence
of the collision and the one-way sink wiring are represented by the concrete
collision operator and by the sink hypotheses, respectively. -/
theorem generatorNativeScoreDwellCertificate
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {t h e : Type*} [Fintype t] [DecidableEq t] [Fintype h]
    (μ : J → ℝ) (φ : ℝ → ℂ)
    (hzero : φ 0 = 1)
    (hmean : ∀ j k, j ≠ k → φ (μ j - μ k) ≠ 1)
    (hdifference : ∀ j k, φ (μ j + μ k) ≠ 1)
    (x : ScoreDwellMode J → ℂ) (n : ℕ) (hn : 0 < n)
    (C : Matrix h t ℂ) (P Q : Matrix t t ℂ) (Jrec : Matrix t e ℂ)
    (hP : P * P = P) (hPQ : P + Q = 1)
    (hCQ : C * Q = 0) (hQJ : Q * Jrec = Jrec) :
    -- fair physical collision branches
    (∀ (m : ℤ), m = 1 ∨ m = -1 → ∀ v : Fin 2 → ℂ,
      star v ⬝ᵥ v = 1 →
      (collideK m)ᴴ * collideK m = (1 / 2 : ℂ) • 1
      ∧ star v ⬝ᵥ (((collideK m)ᴴ * collideK m) *ᵥ v) = 2⁻¹)
    -- retained algebra and exact hidden contraction power
    ∧ (scoreDwellDiagonalEvolution (scoreDwellModeMultiplier μ φ) *ᵥ x = x ↔
      ∀ mode, scoreDwellRetainedMode mode = false → x mode = 0)
    ∧ (‖scoreDwellDiagonalEvolution (scoreDwellModeMultiplier μ φ) ^ n -
          scoreDwellRetainedExpectation scoreDwellRetainedMode‖ =
        ‖scoreDwellResidualMultiplier scoreDwellRetainedMode
          (scoreDwellModeMultiplier μ φ)‖ ^ n)
    -- unique sink factorization, null future map, and zero leakage Gram
    ∧ (∃! Cbar : Matrix h t ℂ,
        Cbar = Cbar * P ∧ C = Cbar * P)
    ∧ C * Jrec = 0
    ∧ Jrecᴴ * (Cᴴ * C) * Jrec = 0 := by
  have hspectral := scoreDwell_global_fixedAlgebra_and_powerNorm
    μ φ hzero hmean hdifference x n hn
  have hsink := record_sink_nullity_exact C P Q Jrec hP hPQ hCQ hQJ
  exact ⟨fun m hm v hv => freshCollision_branch_probability m hm v hv,
    hspectral.1, hspectral.2, hsink.1, hsink.2.1, hsink.2.2⟩

/-- A uniform upper bound on the explicit residual radii gives regulator-
uniform geometric decay, exactly as stated in the manuscript. -/
theorem generatorNativeScoreDwell_regulatorUniform
    (rho : ℕ → ℝ) (gamma : ℝ) (hgamma : 0 < gamma)
    (hgamma1 : gamma ≤ 1) (hrho0 : ∀ X, 0 ≤ rho X)
    (huniform : ∀ X, rho X ≤ 1 - gamma) :
    (∀ X n, rho X ^ n ≤ (1 - gamma) ^ n)
      ∧ Filter.Tendsto (fun n => (1 - gamma) ^ n)
        Filter.atTop (nhds 0) :=
  (generator_native_renewal.2.2 rho gamma hgamma hgamma1 hrho0 huniform)

end NCG
