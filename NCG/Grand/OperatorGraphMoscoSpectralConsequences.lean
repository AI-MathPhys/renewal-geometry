/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OneShiftResolventSpectralConsequences
import NCG.Grand.ExtendedENNRealMoscoResolventConvergenceFromConvexity
import NCG.Grand.ENNRealOperatorGraphResolventMinimizer
import NCG.Grand.ENNRealResolventIdentityFromConvexity
import NCG.Grand.ENNRealResolventOperatorBound

/-!
# Spectral consequences of Mosco-convergent operator graphs

For squared operator-graph energies, weak Euler equations automatically supply finite-energy
resolvent ranges and variational minimality.  Convexity and two-homogeneity are also automatic.
Consequently cofinal Mosco convergence produces the initial strong resolvent limit, while the
same data produce uniform positive-shift bounds and both orientations of the resolvent identity.
This file compiles those facts into the one-shift compact spectral-screen theorem.
-/

open Complex Filter Set Topology
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w x z

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ ℂ (Fn n)]

/-- Cofinal Mosco convergence of squared operator graphs, weak resolvent equations at every
positive shift, and collective compactness at one shift imply the complete compact spectral
conclusion for every selected positive shift. -/
theorem operatorGraphMosco_spectralConsequences
    {ι : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
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
    (a : ℝ) (haPos : 0 < a)
    (hdense : J.IsAsymptoticallyDense)
    (haCompact : J.CollectivelyCompact (Rn a))
    (hsymm : ∀ b, 0 < b → ∀ n,
      LinearMap.IsSymmetric (Rn b n).toLinearMap)
    (hlimSymm : ∀ b, 0 < b → LinearMap.IsSymmetric (R b).toLinearMap)
    (b : ℝ) (hbPos : 0 < b)
    (center radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall (center : ℂ) radius)
    (hlimitLeft : ((center - radius : ℝ) : ℂ) ∈ resolventSet ℂ (R b))
    (hlimitRight : ((center + radius : ℝ) : ℂ) ∈ resolventSet ℂ (R b))
    (v : ℕ → ι → H) (vlim : ι → H)
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i))) :
    IsCompactOperator (R b) ∧
      Tendsto (J.compressedOperator (Rn b)) atTop (𝓝 (R b)) ∧
      Tendsto
        (fun n ↦ NCG.ResolventStability.circleRieszProjection
          (J.compressedOperator (Rn b) n) (center : ℂ) radius) atTop
        (𝓝 (NCG.ResolventStability.circleRieszProjection
          (R b) (center : ℂ) radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (J.compressedOperator (Rn b) n) (center : ℂ) radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (R b) (center : ℂ) radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (J.compressedOperator (Rn b) n) (center : ℂ) radius) (v n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (R b) (center : ℂ) radius) vlim)) := by
  let qn : (n : ℕ) → Hn n → ℝ≥0∞ :=
    fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n)
  let q : H → ℝ≥0∞ := ennrealOperatorGraphEnergy D A
  have hstageFinite : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      qn n (Rn lam n f) ≠ ∞ := by
    intro lam hlam n f
    simpa [qn] using (hstageEquation lam hlam n f).mem
  have hlimitFinite : ∀ lam, 0 < lam → ∀ f : H,
      q (R lam f) ≠ ∞ := by
    intro lam hlam f
    simpa [q] using (hlimitEquation lam hlam f).mem
  have hstageMin : ∀ lam, 0 < lam → ∀ n (f z : Hn n), qn n z ≠ ∞ →
      resolventObjective (K := ℂ) (fun w ↦ (qn n w).toReal) lam f (Rn lam n f) ≤
        resolventObjective (K := ℂ) (fun w ↦ (qn n w).toReal) lam f z := by
    intro lam hlam n f z hz
    apply operatorGraph_resolventObjective_minimizer
      (Dn n) (An n) lam hlam.le f (Rn lam n f)
        (hstageEquation lam hlam n f) z
    simpa [qn] using hz
  have hlimitMin : ∀ lam, 0 < lam → ∀ (f z : H), q z ≠ ∞ →
      resolventObjective (K := ℂ) (fun w ↦ (q w).toReal) lam f (R lam f) ≤
        resolventObjective (K := ℂ) (fun w ↦ (q w).toReal) lam f z := by
    intro lam hlam f z hz
    apply operatorGraph_resolventObjective_minimizer
      D A lam hlam.le f (R lam f) (hlimitEquation lam hlam f) z
    simpa [q] using hz
  have hstageConvex : ∀ n,
      ConvexOn ℝ {z : Hn n | qn n z ≠ ∞} (fun z ↦ (qn n z).toReal) := by
    intro n
    simpa [qn] using convexOn_ennrealOperatorGraphEnergy (Dn n) (An n)
  have hlimitConvex :
      ConvexOn ℝ {z : H | q z ≠ ∞} (fun z ↦ (q z).toReal) := by
    simpa [q] using convexOn_ennrealOperatorGraphEnergy D A
  have haStrong : J.StrongOperatorConverges J (Rn a) (R a) := by
    apply J.strongOperatorConverges_resolvents_of_extendedCofinalMosco_minimizers
      qn q (by simpa [qn, q] using hmosco) a haPos (Rn a) (R a)
    · intro n
      simp [qn]
    · exact hstageFinite a haPos
    · exact hlimitFinite a haPos
    · exact hstageConvex
    · exact hlimitConvex
    · exact hstageMin a haPos
    · exact hlimitMin a haPos
  have hbound : ∀ lam, 0 < lam → ∃ C : ℝ, ∀ n, ‖Rn lam n‖ ≤ C := by
    intro lam hlam
    refine ⟨1 / lam, fun n ↦ ?_⟩
    apply ennrealResolvent_opNorm_le_inv (qn n) (Rn lam n) lam hlam
    exact ennrealResolvent_energy_eq_inner_of_twoHomogeneous
      (qn n) (by simpa [qn] using
        isENNRealTwoHomogeneous_operatorGraphEnergy (Dn n) (An n))
      (Rn lam n) lam hlam (hstageFinite lam hlam n) (hstageMin lam hlam n)
  have hstage : ∀ c d, 0 < c → 0 < d → ∀ n,
      Rn d n - Rn c n = ((c - d : ℝ) : ℂ) •
        ((Rn d n).comp (Rn c n)) := by
    intro c d hc hd n
    exact realSecondResolventIdentity_of_convexMinimizers
      (qn n) (fun lam ↦ Rn lam n) (hstageConvex n)
      (fun lam hlam ↦ hstageFinite lam hlam n)
      (fun lam hlam ↦ hstageMin lam hlam n) d c hd hc
  have hlimit : ∀ c d, 0 < c → 0 < d →
      R c - R d = ((d - c : ℝ) : ℂ) • ((R c).comp (R d)) := by
    intro c d hc hd
    exact realSecondResolventIdentity_of_convexMinimizers
      q R hlimitConvex hlimitFinite hlimitMin c d hc hd
  have hstageReversed : ∀ d, 0 < d → ∀ n,
      Rn d n = Rn a n + ((a - d : ℝ) : ℂ) •
        ((Rn a n).comp (Rn d n)) := by
    intro d hd n
    have hid := realSecondResolventIdentity_of_convexMinimizers
      (qn n) (fun lam ↦ Rn lam n) (hstageConvex n)
      (fun lam hlam ↦ hstageFinite lam hlam n)
      (fun lam hlam ↦ hstageMin lam hlam n) a d haPos hd
    rw [sub_eq_iff_eq_add] at hid
    have hscalar : ((a - d : ℝ) : ℂ) = -((d - a : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hscalar, neg_smul, ← sub_eq_add_neg]
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hid.symm)
  have hnormAt := compressedResolvents_tendsto_operatorNorm_allPositive_of_oneShift
    J Rn R a haPos hdense haStrong haCompact hbound hstage hstageReversed
      hlimit hsymm hlimSymm b hbPos
  have hspectral := compressedResolvent_spectralConsequences_of_oneShift
    J Rn R a haPos hdense haStrong haCompact hbound hstage hstageReversed
      hlimit hsymm hlimSymm b hbPos center radius hR hzero hlimitLeft
        hlimitRight v vlim hv
  exact ⟨hnormAt.1, hnormAt.2, hspectral.2⟩

end NCG.VaryingHilbert.System
