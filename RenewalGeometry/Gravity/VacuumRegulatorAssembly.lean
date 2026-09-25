/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.RelationalDeSitterBranch
import RenewalGeometry.Gravity.RelationalFlatVacuum
import RenewalGeometry.Gravity.FiniteHomogeneousStationarityExact

/-!
# Stationary flat and de Sitter renewal regulators: assembly
(`mt:vacuum`, emergent-spacetime manuscript)

`vacuum_regulator_assembly` conjoins, for the de Sitter branch with Hubble rate `H ≥ 0`
(`Λ = 3H²`; `H = 0` is the flat branch), the already established clauses of
`mt:vacuum`:

* (i, finite-to-continuum half) the finite stationary system of
  `thm:main-finite-homogeneous-stationarity` with `ω = 3H/2` (`Λ = 3H²`,
  `ω = √(3Λ/4)`) converges with second-order logarithmic error to the exponential
  profile `a(τ) = a_0 e^{σHτ}` (`scale_factor_log_error_le`);
* (ii) the `A₃` root law reconstructs the displayed ADM variables: speed density
  `e^{3Ht}`, spatial metric `e^{2Ht} I`, lapse `1`, shift `0`, and on the flat branch the
  tight-frame identity `Σ_α α αᵀ = 8 I` with conductance `h/8`;
* (iii) `Ric − (R/2) g + Λ g = 0` with `Λ = 3H²` for the de Sitter metric
  (`eq:desitter-einstein-main`), which is the flat metric for `H = 0`;
* (iv) on every slab `|t| ≤ T` one positive common lower constant bounds the cut,
  Poincaré, counting and screen margins;
* (v) the reconstructed curvature is the explicit constant-sectional-curvature tensor
  `H²(δδ − δδ)` (identically zero on the flat branch);
* (vi) the time transport is metric-unitary and the normalised torsion, curvature and
  Palatini defects along `h_n = 2^{−n²}` are summable.

Still missing for `mt:vacuum`: the first half of (i) (the profiles solve the lapse-varied
Euler system of `thm:main-homogeneous-friedmann`; proved separately in
`Gravity/RenewalFriedmannExact.lean`, not imported here to keep this assembly
independent of that concurrent file) and the closing sentence (the accept/reject
realisation of `thm:main-explicit-operational-family`, hard).
-/

namespace RenewalGeometry.VacuumRegulatorAssembly

open Real _root_.Matrix RelationalDeSitterBranch FiniteHomogeneousStationarity

/-- The Hubble rate `H` corresponds to `ω = √(3Λ/4) = 3H/2` when `Λ = 3H²`. -/
theorem omega_of_hubble (H : ℝ) (hH : 0 ≤ H) :
    Real.sqrt (3 * (3 * H ^ 2) / 4) = 3 * H / 2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  ring

/-- **`mt:vacuum`** (assembly of clauses (ii)–(vi) and the finite-to-continuum half of (i))
for the de Sitter branch with Hubble rate `H ≥ 0` (`Λ = 3H²`, flat for `H = 0`). -/
theorem vacuum_regulator_assembly (H : ℝ) (hH : 0 ≤ H) :
    -- (i, finite half): finite stationary recurrence converges to `a_0 e^{σHτ}`
    (∀ (σ b h : ℝ), 0 < H → (σ = 1 ∨ σ = -1) → 0 ≤ b → b < 1 → (3 * H / 2) * h / 2 ≤ b →
      ∀ (M : ℕ) (q s : ℕ → ℝ), 0 < q 0 → (∀ j < M, 0 < s j) → (∀ j < M, s j ≤ h) →
        SatisfiesRecurrence (3 * H / 2) σ M q s →
        ∀ j ≤ M, |Real.log (q j ^ (2 / 3 : ℝ) / q 0 ^ (2 / 3 : ℝ)) - σ * H * renewalTime s j|
          ≤ (2 / 3) * ((3 * H / 2) ^ 3 * renewalTime s M * h ^ 2 / (12 * (1 - b ^ 2)))) ∧
    -- (ii): ADM variables from the root law; flat tight frame and conductance
    (∀ t, speedDensity H t = Real.exp (3 * H * t) ∧ spatialMetric H t = Real.exp (2 * H * t) • 1
      ∧ lapse H t = 1 ∧ shift H t = 0) ∧
    ((∑ r, vecMulVec (a3Roots r) (a3Roots r)) = (8 : ℝ) • 1) ∧
    (∀ h : ℝ, h ≠ 0 → h ^ 3 * (1 / (8 * h ^ 2)) = h / 8) ∧
    -- (iii): Einstein equation with `Λ = 3H²`
    (∀ t, ricciTensor H t - (scalarCurvature H / 2) • lorentzMetric H t
        + cosmologicalCoefficient H • lorentzMetric H t = 0) ∧
    cosmologicalCoefficient H = 3 * H ^ 2 ∧
    -- (iv): uniform slab margins
    (∀ (T t cutMargin poincareMargin countingMargin screenMargin : ℝ), |t| ≤ T →
      0 < cutMargin → 0 < poincareMargin → 0 < countingMargin → 0 < screenMargin →
      0 < slabSpatialCommonLower H T cutMargin poincareMargin countingMargin screenMargin ∧
      slabSpatialCommonLower H T cutMargin poincareMargin countingMargin screenMargin
        ≤ Real.exp (H * t) * cutMargin ∧
      slabSpatialCommonLower H T cutMargin poincareMargin countingMargin screenMargin
        ≤ Real.exp (H * t) * poincareMargin ∧
      slabSpatialCommonLower H T cutMargin poincareMargin countingMargin screenMargin
        ≤ Real.exp (H * t) * countingMargin ∧
      slabSpatialCommonLower H T cutMargin poincareMargin countingMargin screenMargin
        ≤ Real.exp (H * t) * screenMargin) ∧
    -- (v): explicit constant-curvature tensor, zero on the flat branch
    (∀ A B C D : Fin 4, constantCurvatureTensor H A B C D = H ^ 2 *
      ((if A = C then 1 else 0) * (if B = D then 1 else 0) -
        (if A = D then 1 else 0) * (if B = C then 1 else 0))) ∧
    (H = 0 → ∀ A B C D : Fin 4, constantCurvatureTensor H A B C D = 0) ∧
    -- (vi): metric-unitary transport and summable normalised defects
    (∀ t s, (timeTransport H t s).transpose * spatialMetric H s * timeTransport H t s
      = spatialMetric H t) ∧
    Summable (normalizedTorsionDefect H) ∧ Summable (normalizedCurvatureDefect H) ∧
    Summable (normalizedPalatiniDefect H) := by
  obtain ⟨hflat1, hflat2⟩ := relational_flat_vacuum
  obtain ⟨hs1, hs2, hs3⟩ := explicit_geometric_defects_summable H
  refine ⟨?_, adm_variables_exact H, hflat1, hflat2, einstein_cosmological_vacuum H, rfl,
    fun T t c p n s ht hc hp hn hs =>
      slab_spatial_constants_common_lower H T t c p n s hH ht hc hp hn hs,
    cartan_constant_sectional_curvature H, ?_, timeTransport_metric_unitary H, hs1, hs2, hs3⟩
  · intro σ b h hHpos hσ hb0 hb hωb M q s hq0 hs hsh hrec j hj
    have hω : 0 < 3 * H / 2 := by positivity
    have := scale_factor_log_error_le (3 * H / 2) σ b h hω hσ hb0 hb hωb M q s hq0 hs hsh hrec j hj
    rwa [show σ * (2 * (3 * H / 2) / 3) = σ * H by ring] at this
  · intro h0 A B C D
    rw [cartan_constant_sectional_curvature, h0]
    ring

end RenewalGeometry.VacuumRegulatorAssembly
