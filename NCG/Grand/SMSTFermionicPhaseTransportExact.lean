/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FermionicPhaseTransportExact
import NCG.Grand.DeterminantWindingExact

/-!
# Fermionic gap, spectral-flow, and gauge-line alternatives (record theorem)

Exact encoding of `thm:SMST-fermionic-phase-transport`:

* **(F1)/(F2)** `reduced_gap_alternative`: along any sequence of finite Dirac operators exactly one
  of a uniform reduced gap or a vanishing reduced singular value occurs;
* **(QRP.10)** `det_sign_spectral_flow`: for a Hermitian path with continuous eigenvalue branches
  crossing zero transversally, `sgn det H(1) = (-1)^{sf} sgn det H(0)`, encoded as
  `0 < det H(1) det H(0) ⇔ sf even` with both endpoint determinants nonzero;
* **(QRP.11)** `det_winding` / `exists_periodic_log_iff`: for a `C¹` loop in `GL_n(ℂ)`,
  `wind (det D) = (1/2πi) ∫ tr (D⁻¹ dD) ∈ ℤ`, and a continuous periodic determinant logarithm
  exists exactly when this integer vanishes;
* **(QRP.12)** `scalarizable_iff_stabilizer_trivial`: a gauge-line cocycle on one orbit is
  scalarizable exactly when it is trivial on the stabilizer; `scalarization_unique`: the residual
  edge cochain of two scalarizations is a constant phase.

The package is collected in `fermionic_phase_transport`.
-/

open Filter Topology
open NCG.FermionicPhaseTransport NCG.DeterminantWinding

namespace NCG
namespace SMSTFermionicPhaseTransport

set_option linter.unusedSectionVars false

/-- **Fermionic gap, spectral-flow, and gauge-line alternatives.** -/
theorem fermionic_phase_transport {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} {G Ω A : Type*} [Group G] [MulAction G Ω] [CommGroup A] :
    -- (F1)/(F2)
    (∀ D : ℕ → E →ₗ[ℂ] E,
      ((∃ γ : ℝ, 0 < γ ∧ UniformReducedGap D γ) ∨ VanishingReducedGap D) ∧
        ¬ ((∃ γ : ℝ, 0 < γ ∧ UniformReducedGap D γ) ∧ VanishingReducedGap D)) ∧
    -- (QRP.10)
    (∀ (H : ℝ → Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ → ℝ),
      (∀ t, (H t).det = ((∏ i, lam i t : ℝ) : ℂ)) →
      ∀ (Z : Fin n → Finset ℝ) (d : Fin n → ℝ → ℝ), (∀ i, ContinuousOn (lam i) (Set.Icc 0 1)) →
      (∀ i, (↑(Z i) : Set ℝ) ⊆ Set.Ioo 0 1) → (∀ i, ∀ t ∈ Set.Icc 0 1, lam i t = 0 ↔ t ∈ Z i) →
      (∀ i, ∀ z ∈ Z i, d i z ≠ 0 ∧ HasDerivAt (lam i) (d i z) z) →
      (0 < ((H 1).det * (H 0).det).re ↔ Even (spectralFlow Z d)) ∧
        (H 1).det ≠ 0 ∧ (H 0).det ≠ 0) ∧
    -- (QRP.11)
    (∀ (D D' : ℝ → Matrix (Fin n) (Fin n) ℂ),
      (∀ t i j, HasDerivAt (fun s => D s i j) (D' t i j) t) →
      (∀ i j, Continuous fun t => D' t i j) → (∀ t, (D t).det ≠ 0) → D 1 = D 0 →
      (winding (fun t => (D t).det) (fun t => (D t).det * Matrix.trace ((D t)⁻¹ * D' t))
          = (∫ s in (0 : ℝ)..1, Matrix.trace ((D s)⁻¹ * D' s)) / (2 * Real.pi * Complex.I)) ∧
        (∃ k : ℤ, ∫ s in (0 : ℝ)..1, Matrix.trace ((D s)⁻¹ * D' s)
          = k * (2 * Real.pi * Complex.I)) ∧
        ((∃ M : ℝ → ℂ, ContinuousOn M (Set.Icc 0 1) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (M t) = (D t).det) ∧ M 1 = M 0) ↔
          winding (fun t => (D t).det) (fun t => (D t).det * Matrix.trace ((D t)⁻¹ * D' t)) = 0)) ∧
    -- (QRP.12)
    (∀ (a : G → Ω → A), IsCocycle a → ∀ ω₀ : Ω,
      ((∃ b : Ω → A, IsScalarization a ω₀ b) ↔ ∀ h ∈ MulAction.stabilizer G ω₀, a h ω₀ = 1) ∧
      ∀ b b' : Ω → A, IsScalarization a ω₀ b → IsScalarization a ω₀ b' →
        ∀ ω ∈ MulAction.orbit G ω₀, b' ω * (b ω)⁻¹ = b' ω₀ * (b ω₀)⁻¹) := by
  refine ⟨fun D => reduced_gap_alternative D, ?_, ?_, ?_⟩
  · intro H lam hdet Z d hcont hZ hzero htr
    exact det_sign_spectral_flow hdet Z d hcont hZ hzero htr
  · intro D D' hD hD' hinv hloop
    obtain ⟨h1, h2⟩ := det_winding hD hD' hinv hloop
    refine ⟨h1, h2, ?_⟩
    have hderiv : ∀ t, HasDerivAt (fun s => (D s).det)
        ((D t).det * Matrix.trace ((D t)⁻¹ * D' t)) t := fun t =>
      hasDerivAt_det_of_det_ne_zero (hD t) (hinv t)
    have hDcont : ∀ i j, Continuous fun t => D t i j := fun i j =>
      continuous_iff_continuousAt.mpr fun t => (hD t i j).continuousAt
    have hDc : Continuous fun t => D t := continuous_matrix fun i j => hDcont i j
    have hdetcont : Continuous fun t => (D t).det := hDc.matrix_det
    have hinvcont : Continuous fun t => (D t)⁻¹ := by
      have h1 : Continuous fun t => (D t).det⁻¹ • (D t).adjugate :=
        (hdetcont.inv₀ hinv).smul hDc.matrix_adjugate
      refine h1.congr fun t => ?_
      rw [Matrix.inv_def, Ring.inverse_eq_inv]
    have hf' : Continuous fun t => (D t).det * Matrix.trace ((D t)⁻¹ * D' t) :=
      hdetcont.mul (hinvcont.matrix_mul (continuous_matrix fun i j => hD' i j)).matrix_trace
    exact exists_periodic_log_iff hderiv hf' hinv (by rw [hloop])
  · intro a ha ω₀
    exact ⟨scalarizable_iff_stabilizer_trivial ha ω₀,
      fun b b' hb hb' => scalarization_unique hb hb'⟩

end SMSTFermionicPhaseTransport
end NCG
