/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphEnergyCompactScreenAlternative
import NCG.Grand.OperatorGraphResolventDenseRange
import NCG.Grand.VaryingHilbertCompressedSpectralConsequences

/-!
# Compact spectral convergence or graph-energy mass escape

This module packages the two branches of the manuscript's compact-screen
alternative in one theorem.  The positive branch contains the complete
automatic-circle spectral and source-Gram conclusions; the negative branch
contains effective-domain vectors satisfying `‖u‖² + q_n(u) ≤ 1` whose
graph-screen tails retain one fixed positive mass.
-/

open Complex Filter Set Topology
open NCG.ResolventStability
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w z z' x

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]
variable {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]

/-- Exact compact-screen dichotomy: either the compressed resolvents satisfy
the full compact spectral approximation package, or graph energy escapes
along cofinal screens and cutoffs. -/
theorem operatorGraphResolvent_fullSpectralConsequences_or_energyMassEscape
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule ℂ (Hn n))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (Rn : ∀ n, Hn n →L[ℂ] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst)
    (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Rn T)
    (hlimSymm : LinearMap.IsSymmetric T.toLinearMap)
    (center : ℂ) (hcenter : center ≠ 0)
    (source : ℕ → ι → H) (sourceLim : ι → H)
    (hsource : ∀ i, Tendsto (fun n ↦ source n i) atTop (𝓝 (sourceLim i))) :
    (J.CollectivelyCompact Rn ∧
      ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) ∧
      IsCompactOperator T ∧
      LinearMap.range (circleRieszProjection T center radius).toLinearMap =
        Module.End.eigenspace T.toLinearMap center ∧
      Tendsto (J.compressedOperator Rn) atTop (𝓝 T) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Rn n) center radius) atTop
        (𝓝 (circleRieszProjection T center radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection
                (J.compressedOperator Rn n) center radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection T center radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (circleRieszProjection
            (J.compressedOperator Rn n) center radius) (source n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (circleRieszProjection T center radius) sourceLim))) ∨
      (∃ ε > 0, ∃ radius cutoff : ℕ → ℕ,
        ∃ x : ∀ j, Dn (cutoff j),
          Tendsto radius atTop atTop ∧ Tendsto cutoff atTop atTop ∧
          ∀ j,
            ‖(x j : Hn (cutoff j))‖ ^ 2 +
                (ennrealOperatorGraphEnergy
                  (Dn (cutoff j)) (An (cutoff j))
                  (x j : Hn (cutoff j))).toReal ≤ 1 ∧
            ε ≤ ‖L.embedding (cutoff j)
                (operatorGraphNormInclusion
                  (Dn (cutoff j)) (An (cutoff j))
                  (operatorGraphNormVector
                    (Dn (cutoff j)) (An (cutoff j)) (x j))) -
              screen (radius j)
                (L.embedding (cutoff j)
                  (operatorGraphNormInclusion
                    (Dn (cutoff j)) (An (cutoff j))
                    (operatorGraphNormVector
                      (Dn (cutoff j)) (An (cutoff j)) (x j))))‖) := by
  rcases J.operatorGraphResolvent_collectivelyCompact_or_energyMassEscape
      L Dn An Rn lam hlam hEquation screen hcompact hfst with
    hcollective | hescape
  · left
    exact ⟨hcollective,
      J.compressedOperator_spectralConsequences_of_collectivelyCompact_automaticCircle
        Rn T hdense hstrong hcollective
          (fun n ↦ operatorGraphResolvent_isSymmetric
            (Dn n) (An n) lam (Rn n) (hEquation n))
          hlimSymm center hcenter source sourceLim hsource⟩
  · exact Or.inr hescape

end NCG.VaryingHilbert.System
