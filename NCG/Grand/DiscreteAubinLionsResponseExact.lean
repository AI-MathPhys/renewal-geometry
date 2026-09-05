/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StructurePreservingResponseExact

/-!
# Discrete Aubin--Lions closure for structure-preserving response

The coercive spatial bound enters through the uniform interpolation estimate
`dist² ≤ C · weakDist`; the discrete update supplies
`weakDist ≤ L |t-s|`.  Their composition gives the square-root time modulus
required by the compact response-thread extraction.  This removes the
previously assumed equicontinuity output from the finite-scheme descent.
-/

open Filter Topology

namespace NCG
namespace StructureResponse

/-- Quantitative discrete Aubin--Lions interpolation: a compact spatial
embedding estimate and a negative-norm time-translation estimate imply a
uniform square-root modulus in the target metric. -/
theorem discrete_aubin_lions_modulus
    {K : Type*} [PseudoMetricSpace K]
    (y : ℕ → ℝ → K) (weakDist : ℕ → ℝ → ℝ → ℝ)
    (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hinterpolation : ∀ N t s,
      dist (y N t) (y N s) ^ 2 ≤ C * weakDist N t s)
    (htime : ∀ N t s,
      weakDist N t s ≤ L * |t - s|) :
    ∀ N t s,
      dist (y N t) (y N s) ≤ Real.sqrt (C * L * |t - s|) := by
  intro N t s
  have hsq : dist (y N t) (y N s) ^ 2 ≤ C * L * |t - s| := by
    calc
      dist (y N t) (y N s) ^ 2
          ≤ C * weakDist N t s := hinterpolation N t s
      _ ≤ C * (L * |t - s|) :=
        mul_le_mul_of_nonneg_left (htime N t s) hC
      _ = C * L * |t - s| := by ring
  have hrhs : 0 ≤ C * L * |t - s| := by positivity
  have hsqrt := Real.sq_sqrt hrhs
  have hdist : 0 ≤ dist (y N t) (y N s) := dist_nonneg
  have hsqrtnonneg := Real.sqrt_nonneg (C * L * |t - s|)
  nlinarith

/-- Structure-preserving finite-scheme descent with the discrete Aubin--Lions
step discharged from its native interpolation and negative-norm estimates.
The only compactness assumption is the manuscript's compact target-writer
topology. -/
theorem structure_preserving_response_of_discrete_aubin_lions
    {K : Type*} [MetricSpace K] [CompactSpace K] [CompleteSpace K]
    (T : ℝ) (q : ℕ → ℝ) (y : ℕ → ℝ → K)
    (weakDist : ℕ → ℝ → ℝ → ℝ) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hq_mem : ∀ jq, q jq ∈ Set.Icc 0 T)
    (hdense : ∀ t ∈ Set.Icc 0 T, ∀ ε > 0, ∃ jq, |q jq - t| < ε)
    (hinterpolation : ∀ N, ∀ t ∈ Set.Icc 0 T, ∀ s ∈ Set.Icc 0 T,
      dist (y N t) (y N s) ^ 2 ≤ C * weakDist N t s)
    (htime : ∀ N, ∀ t ∈ Set.Icc 0 T, ∀ s ∈ Set.Icc 0 T,
      weakDist N t s ≤ L * |t - s|)
    {k : ℕ → ℕ} (𝔡 : ∀ j, (Fin (k j) → K) → ℝ)
    (h𝔡 : ∀ j, Continuous (𝔡 j)) (qs : ∀ j, Fin (k j) → ℝ)
    (hqs : ∀ j i, ∃ jq, qs j i = q jq)
    (hres : ∀ j, Tendsto (fun N => 𝔡 j (fun i => y N (qs j i)))
      atTop (nhds 0)) :
    ∃ (z : ℝ → K) (φ' : ℕ → ℕ), StrictMono φ' ∧
      ContinuousOn z (Set.Icc 0 T) ∧
      (∀ t ∈ Set.Icc 0 T, ∀ s ∈ Set.Icc 0 T,
        dist (z t) (z s) ≤ Real.sqrt (C * L * |t - s|)) ∧
      (∀ j, 𝔡 j (fun i => z (qs j i)) = 0) ∧
      (∀ jq, Tendsto (fun m => y (φ' m) (q jq))
        atTop (nhds (z (q jq)))) := by
  let ω : ℝ → ℝ := fun r => Real.sqrt (C * L * r)
  have hω_cont : Continuous ω := by
    exact Real.continuous_sqrt.comp
      ((continuous_const.mul continuous_const).mul continuous_id)
  have hω_zero : ω 0 = 0 := by simp [ω]
  have hmod : ∀ N, ∀ t ∈ Set.Icc 0 T, ∀ s ∈ Set.Icc 0 T,
      dist (y N t) (y N s) ≤ ω |t - s| := by
    intro N t ht s hs
    have hsq : dist (y N t) (y N s) ^ 2 ≤ C * L * |t - s| := by
      calc
        dist (y N t) (y N s) ^ 2
            ≤ C * weakDist N t s := hinterpolation N t ht s hs
        _ ≤ C * (L * |t - s|) :=
          mul_le_mul_of_nonneg_left (htime N t ht s hs) hC
        _ = C * L * |t - s| := by ring
    have hrhs : 0 ≤ C * L * |t - s| := by positivity
    have hsqrt := Real.sq_sqrt hrhs
    have hdist : 0 ≤ dist (y N t) (y N s) := dist_nonneg
    have hsqrtnonneg := Real.sqrt_nonneg (C * L * |t - s|)
    dsimp only [ω]
    nlinarith
  simpa [ω] using structure_preserving_response T q y ω hq_mem hdense
    hω_cont hω_zero hmod 𝔡 h𝔡 qs hqs hres

end StructureResponse
end NCG
