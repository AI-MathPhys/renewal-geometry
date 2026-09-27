/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Analysis.CompactSelfAdjointMinMax
import RenewalGeometry.OperatorLimits.RieszProjectionStability
import RenewalGeometry.OperatorLimits.NearbyProjectionRankStability
import RenewalGeometry.OperatorLimits.CircleRieszProjectionIdempotence
import RenewalGeometry.OperatorLimits.CompactCircleRieszProjection

/-!
# Low-spectrum convergence

This file closes `lem:low-spectrum-convergence` of the spacetime–gauge duality paper.

For a compact positive operator `R` on a Hilbert space, the ordered eigenvalues
`μ₀ ≥ μ₁ ≥ ⋯` repeated with multiplicity are the Courant–Fischer min–max values
`courantValue R k` (`RenewalGeometry.Analysis.CompactSelfAdjointMinMax`); the theorem
`orderedEigenvalues_spec_of_compact_isPositive` records the identification (antitone, nonnegative,
multiplicity of every positive value equals the eigenspace dimension, every positive value is an
eigenvalue and every positive eigenvalue occurs).

The lemma itself: if `‖R_X - R_∞‖ → 0` then `μ_{k,X} → μ_{k,∞}` for every `k`, and
`λ_{k,X} = 1/μ_{k,X} - 1 → λ_{k,∞}` whenever `μ_{k,∞} > 0` (the limiting eigenvalue is finite);
circle-contour Riesz projections converge in operator norm under uniform resolvent bounds on the
contour, and their ranks are eventually equal.
-/

open Filter Topology RCLike
open RenewalGeometry.CourantFischer

noncomputable section

namespace RenewalGeometry.LowSpectrum

section Identification

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The `k`-th ordered eigenvalue (zero-indexed, decreasing, repeated with multiplicity) of a
compact positive operator, realised as its `k`-th Courant–Fischer value.  Beyond the rank of a
finite-rank operator the value is `0`. -/
abbrev orderedEigenvalue (R : H →L[𝕜] H) (k : ℕ) : ℝ := courantValue R k

/-- **Ordered eigenvalues of a compact positive operator.**  The min–max values of a compact
positive operator form a nonnegative antitone sequence; for every `lam > 0` the number of indices
`k` with `orderedEigenvalue R k = lam` is the dimension of the `lam`-eigenspace; every positive
value is an eigenvalue and every positive eigenvalue occurs.  This is the statement that
`orderedEigenvalue R` enumerates the positive eigenvalues of `R` in decreasing order, repeated
with multiplicity. -/
theorem orderedEigenvalues_spec_of_compact_isPositive (R : H →L[𝕜] H)
    (hcompact : IsCompactOperator R) (hpos : R.IsPositive) :
    Antitone (orderedEigenvalue R) ∧
    (∀ k, 0 ≤ orderedEigenvalue R k) ∧
    (∀ lam : ℝ, 0 < lam →
      Module.finrank 𝕜 (Module.End.eigenspace (R : H →ₗ[𝕜] H) (lam : 𝕜)) =
        {k : ℕ | orderedEigenvalue R k = lam}.ncard) ∧
    (∀ lam : ℝ, 0 < lam → {k : ℕ | orderedEigenvalue R k = lam}.Finite) ∧
    (∀ k, 0 < orderedEigenvalue R k →
      Module.End.HasEigenvalue (R : H →ₗ[𝕜] H) ((orderedEigenvalue R k : ℝ) : 𝕜)) ∧
    (∀ lam : ℝ, 0 < lam → Module.End.HasEigenvalue (R : H →ₗ[𝕜] H) (lam : 𝕜) →
      ∃ k, orderedEigenvalue R k = lam) := by
  have hsymm : LinearMap.IsSymmetric (R : H →ₗ[𝕜] H) := hpos.isSymmetric
  refine ⟨courantValue_antitone_of_isPositive hpos,
    courantValue_nonneg_of_isPositive hpos,
    fun lam hlam ↦ finrank_eigenspace_eq_ncard R hsymm hcompact lam hlam,
    fun lam hlam ↦ finite_setOf_courantValue_eq R hsymm hcompact lam hlam,
    fun k hk ↦ hasEigenvalue_of_courantValue_pos R hsymm hcompact k hk,
    fun lam hlam heig ↦ exists_courantValue_eq_of_hasEigenvalue R hsymm hcompact lam hlam heig⟩

omit [CompleteSpace H] in
/-- Weyl-type stability of the ordered eigenvalues: `|μ_k(A) - μ_k(B)| ≤ ‖A - B‖`. -/
theorem abs_orderedEigenvalue_sub_le (A B : H →L[𝕜] H) (k : ℕ) :
    |orderedEigenvalue A k - orderedEigenvalue B k| ≤ ‖A - B‖ :=
  abs_courantValue_sub_le A B k

omit [CompleteSpace H] in
/-- Norm convergence of operators gives convergence of every ordered eigenvalue
(`μ_{k,X} → μ_{k,∞}`). -/
theorem tendsto_orderedEigenvalue {ι : Type*} {l : Filter ι} {Rseq : ι → H →L[𝕜] H}
    {R : H →L[𝕜] H} (hconv : Tendsto Rseq l (𝓝 R)) (k : ℕ) :
    Tendsto (fun i ↦ orderedEigenvalue (Rseq i) k) l (𝓝 (orderedEigenvalue R k)) :=
  tendsto_courantValue hconv k

/-- Convergence of the transformed eigenvalues `λ_k = 1/μ_k - shift` whenever the limiting
eigenvalue is finite, i.e. `μ_{k,∞} > 0`. -/
theorem tendsto_shiftedInverse_orderedEigenvalue {ι : Type*} {l : Filter ι}
    {Rseq : ι → H →L[𝕜] H} {R : H →L[𝕜] H} (hconv : Tendsto Rseq l (𝓝 R)) (shift : ℝ)
    (k : ℕ) (hk : 0 < orderedEigenvalue R k) :
    Tendsto (fun i ↦ (orderedEigenvalue (Rseq i) k)⁻¹ - shift) l
      (𝓝 ((orderedEigenvalue R k)⁻¹ - shift)) :=
  ((tendsto_orderedEigenvalue hconv k).inv₀ hk.ne').sub_const shift

end Identification

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open RenewalGeometry.ResolventStability RenewalGeometry.ProjectionStability

/-- **Low-spectrum convergence** (`lem:low-spectrum-convergence`).  Let `R_X → R_∞` in operator
norm, all compact and symmetric.  Then

* every ordered eigenvalue converges, `μ_{k,X} → μ_{k,∞}`;
* whenever `μ_{k,∞} > 0`, the shifted inverses `λ_{k,X} = 1/μ_{k,X} - 1 → λ_{k,∞}`;
* for every circle `Γ = ∂B(center, radius)` avoiding `0`, lying in the resolvent set of `R_∞`
  and eventually of `R_X`, with uniform resolvent bounds on `Γ`, the Riesz projections
  `Π_X(Γ) → Π_∞(Γ)` in operator norm and their (finite) ranks are eventually equal. -/
theorem lowSpectrumConvergence (Rseq : ℕ → H →L[ℂ] H) (R : H →L[ℂ] H)
    (hconv : Tendsto Rseq atTop (𝓝 R))
    (hcompact : IsCompactOperator R)
    (hsymm : LinearMap.IsSymmetric (R : H →ₗ[ℂ] H))
    (hcompact_seq : ∀ᶠ n in atTop, IsCompactOperator (Rseq n))
    (hsymm_seq : ∀ᶠ n in atTop, LinearMap.IsSymmetric (Rseq n : H →ₗ[ℂ] H)) :
    (∀ k, Tendsto (fun n ↦ orderedEigenvalue (Rseq n) k) atTop (𝓝 (orderedEigenvalue R k))) ∧
    (∀ k, 0 < orderedEigenvalue R k →
      Tendsto (fun n ↦ (orderedEigenvalue (Rseq n) k)⁻¹ - 1) atTop
        (𝓝 ((orderedEigenvalue R k)⁻¹ - 1))) ∧
    (∀ (center : ℂ) (radius : ℝ), 0 < radius →
      (0 : ℂ) ∉ Metric.closedBall center radius →
      ∀ M N : ℝ, 0 ≤ M →
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ R) →
      (∀ z ∈ Metric.sphere center radius, ‖resolvent R z‖ ≤ M) →
      (∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ (Rseq n)) →
      (∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius, ‖resolvent (Rseq n) z‖ ≤ N) →
      Tendsto (fun n ↦ circleRieszProjection (Rseq n) center radius) atTop
        (𝓝 (circleRieszProjection R center radius)) ∧
      ∀ᶠ n in atTop,
        Module.finrank ℂ (LinearMap.range (circleRieszProjection (Rseq n) center radius).toLinearMap) =
          Module.finrank ℂ (LinearMap.range (circleRieszProjection R center radius).toLinearMap)) := by
  refine ⟨fun k ↦ tendsto_orderedEigenvalue hconv k,
    fun k hk ↦ tendsto_shiftedInverse_orderedEigenvalue hconv 1 k hk, ?_⟩
  intro center radius hradius hzero M N hM hlimit_unit hlimit_bound hstage_unit hstage_bound
  have hproj : Tendsto (fun n ↦ circleRieszProjection (Rseq n) center radius) atTop
      (𝓝 (circleRieszProjection R center radius)) :=
    circleRieszProjection_tendsto hconv center radius hradius.le M N hM
      hlimit_unit hlimit_bound hstage_unit hstage_bound
  refine ⟨hproj, ?_⟩
  have : Module.Finite ℂ (LinearMap.range (circleRieszProjection R center radius).toLinearMap) :=
    finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric R hcompact hsymm
      center radius hradius hzero hlimit_unit
  refine eventually_finrank_range_eq_of_tendsto _ _ hproj ?_ ?_ ?_
  · filter_upwards [hcompact_seq, hsymm_seq, hstage_unit] with n hc hs hu
    exact circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric (Rseq n) hc hs
      center radius hradius hu
  · exact circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric R hcompact hsymm
      center radius hradius hlimit_unit
  · filter_upwards [hcompact_seq, hsymm_seq, hstage_unit] with n hc hs hu
    exact finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric (Rseq n) hc hs
      center radius hradius hzero hu

end Complex

end RenewalGeometry.LowSpectrum
