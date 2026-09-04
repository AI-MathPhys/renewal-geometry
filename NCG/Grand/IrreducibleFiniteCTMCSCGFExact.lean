/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCPathSCGFExact
import NCG.Grand.IrreducibleGeneratorEscapeExact
import NCG.Grand.PerronAnalyticEigenbranchExact
import NCG.Grand.MetzlerSpectralAbscissaExact

/-!
# Analytic SCGF of the genuine irreducible finite-state process

For a nontrivial irreducible finite generator, the path construction, actual
Feynman--Kac formula, long-time exponential-moment limit, and real analyticity
are assembled with no supplied escape-rate, tilted-irreducibility, analytic
branch, or path/matrix expectation hypotheses. The limiting exponent is also
identified with the independently defined complex spectral abscissa. Singleton
processes, general reducible processes, algebraic simplicity, and the full
large-deviation principle are not asserted by this file.
-/

open Filter Topology
open scoped BigOperators

namespace NCG.IrreducibleFiniteCTMCSCGF

open DrivenProcess DrivenProcess.FinitePath FiniteCTMCFeynmanKacPathMoment
open FiniteCTMCInitialMixture FiniteCTMCPathSCGF IrreducibleGeneratorEscape
open MetzlerExponentialPositivity MetzlerPerronExponent

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] [Nontrivial S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Feynman--Kac for the genuine irreducible process: positivity of escape
rates is derived from irreducibility of the original generator. -/
theorem pathMoment_eq_tiltedSemigroup
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x)
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    pathMoment x₀ p L hL (escapeRate_pos L hL hirr) v g k T f =
      ∑ x, p x * Matrix.mulVec (Matrix.exponentialEntry (T • tilt L v g k)) f x :=
  pathMoment_eq_exponentialEntry_pairing L hL (escapeRate_pos L hL hirr)
    x₀ p hp v g k T f hT

/-- The stochastic SCGF limit at every real tilt, requiring irreducibility
only of the original generator and no full-support initial distribution. -/
theorem tendsto_scaled_log_pathMoment
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    Tendsto
      (fun T : ℝ => Real.log (pathMoment x₀ p L hL (escapeRate_pos L hL hirr)
        v g k T (fun _ => 1)) / T)
      atTop (𝓝 (exponent (tilt L v g k))) :=
  tendsto_scaled_log_pathMoment_of_probability L hL (escapeRate_pos L hL hirr)
    x₀ p hp hsum v g k (tilt_isIrreducibleMetzler L hL hirr v g k)

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- The canonical exponent identified by the actual path limit is analytic
at every real tilt, from the original generator hypotheses alone. -/
theorem analyticAt_scgf
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    AnalyticAt ℝ (fun q => exponent (tilt L v g q)) k :=
  PerronAnalyticEigenbranch.analyticAt_tiltedPerronExponent L v g
    (tilt_isIrreducibleMetzler L hL hirr v g) k

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- Probability preservation forces the SCGF to vanish at zero tilt. -/
theorem scgf_zero
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (v : S → ℝ) (g : S → S → ℝ) : exponent (tilt L v g 0) = 0 := by
  rw [tilt_zero]
  symm
  apply eigenvalue_eq_exponent L hirr (r := fun _ => 1) (fun _ => zero_lt_one)
  ext i
  simpa [Matrix.mulVec, dotProduct] using hL.row_sum i

/-- The genuine path SCGF equals the actual complex spectral bound appearing
in the manuscript, rather than just an unspecified positive-vector eigenvalue. -/
theorem tendsto_scaled_log_pathMoment_spectralAbscissa
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (x₀ : S) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    Tendsto
      (fun T : ℝ => Real.log (pathMoment x₀ p L hL (escapeRate_pos L hL hirr)
        v g k T (fun _ => 1)) / T)
      atTop (𝓝 (MetzlerSpectralAbscissa.spectralAbscissa (tilt L v g k))) := by
  rw [MetzlerSpectralAbscissa.spectralAbscissa_eq_exponent _
    (tilt_isIrreducibleMetzler L hL hirr v g k)]
  exact tendsto_scaled_log_pathMoment L hL hirr x₀ p hp hsum v g k

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- Real analyticity of the independently defined tilted complex spectral bound. -/
theorem analyticAt_spectralAbscissa
    (L : Matrix S S ℝ) (hL : IsGenerator L) (hirr : IsIrreducibleMetzler L)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    AnalyticAt ℝ (fun q => MetzlerSpectralAbscissa.spectralAbscissa (tilt L v g q)) k := by
  have heq : (fun q => MetzlerSpectralAbscissa.spectralAbscissa (tilt L v g q)) =
      (fun q => exponent (tilt L v g q)) := by
    funext q
    exact MetzlerSpectralAbscissa.spectralAbscissa_eq_exponent _
      (tilt_isIrreducibleMetzler L hL hirr v g q)
  rw [heq]
  exact analyticAt_scgf L hL hirr v g k

end

end NCG.IrreducibleFiniteCTMCSCGF
