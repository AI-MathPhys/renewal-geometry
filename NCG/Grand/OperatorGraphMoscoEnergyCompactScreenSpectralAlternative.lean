/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphEnergyCompactScreenSpectralAlternative
import NCG.Grand.OperatorGraphMoscoResolventConvergence

/-!
# Graph-Mosco compact spectral convergence or energy mass escape

This module joins the exact graph-energy compact-screen dichotomy to cofinal
Mosco convergence.  Mosco convergence supplies strong resolvent convergence,
while the weak graph equations supply symmetry.  Thus a model only has to
provide compact graph screens and compatibility of their first coordinates.
-/

open Complex Filter Set Topology
open NCG.ResolventStability
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w z z' x

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
variable {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ ℂ (Fn n)]

/-- Cofinal Mosco convergence and compact graph screens give either the full
compact spectral approximation package at a positive shift, or an explicit
cofinal sequence of graph-energy unit vectors whose screen tails retain a
fixed positive mass. -/
theorem operatorGraphMosco_fullSpectralConsequences_or_energyMassEscape
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule ℂ (Hn n))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (Rn : ℝ → ∀ n, Hn n →L[ℂ] Hn n) (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn lam n f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (a : ℝ) (ha : 0 < a)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst)
    (hdense : J.IsAsymptoticallyDense)
    (center : ℂ) (hcenter : center ≠ 0)
    (source : ℕ → ι → H) (sourceLim : ι → H)
    (hsource : ∀ i, Tendsto (fun n ↦ source n i) atTop (𝓝 (sourceLim i))) :
    (J.CollectivelyCompact (Rn a) ∧
      ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ (R a)) ∧
      IsCompactOperator (R a) ∧
      LinearMap.range (circleRieszProjection (R a) center radius).toLinearMap =
        Module.End.eigenspace (R a).toLinearMap center ∧
      Tendsto (J.compressedOperator (Rn a)) atTop (𝓝 (R a)) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator (Rn a) n) center radius) atTop
        (𝓝 (circleRieszProjection (R a) center radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection
                (J.compressedOperator (Rn a) n) center radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection (R a) center radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (circleRieszProjection
            (J.compressedOperator (Rn a) n) center radius) (source n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (circleRieszProjection (R a) center radius) sourceLim))) ∨
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
  have hstrong : J.StrongOperatorConverges J (Rn a) (R a) :=
    J.operatorGraphMosco_strongResolvents_allPositive
      Dn An D A Rn R hmosco hstageEquation hlimitEquation a ha
  have hlimSymm : LinearMap.IsSymmetric (R a).toLinearMap :=
    operatorGraphResolvent_isSymmetric D A a (R a) (hlimitEquation a ha)
  exact J.operatorGraphResolvent_fullSpectralConsequences_or_energyMassEscape
    L Dn An (Rn a) a ha (hstageEquation a ha) screen hcompact hfst
      (R a) hdense hstrong hlimSymm center hcenter source sourceLim hsource

end NCG.VaryingHilbert.System
