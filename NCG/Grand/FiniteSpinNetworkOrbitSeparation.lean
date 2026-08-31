/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteSpinNetworkCompleteness

/-!
# Finite spin networks separate gauge orbits

The explicit edge-irrep/vertex-intertwiner family is already an orthonormal
basis of the complete finite gauge-invariant Hilbert space.  This file applies
that completeness theorem to orbit indicators and proves that equality of all
contracted spin-network coefficients is exactly finite gauge equivalence.
-/

noncomputable section

namespace NCG
namespace FiniteSpinNetwork

open NCG.FinitePeterWeyl

variable {G V E : Type*} [Group G] [Fintype G] [Fintype V]
  [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Two finite edge configurations are gauge equivalent when one is obtained
from the other by one vertex gauge transformation. -/
def GaugeEquivalent (t s : E → V) (x y : E → G) : Prop :=
  ∃ h : V → G, NCG.gaugeAct t s h x = y

noncomputable instance gaugeEquivalentDecidable (t s : E → V)
    (x y : E → G) : Decidable (GaugeEquivalent t s x y) :=
  Classical.propDecidable _

theorem gaugeEquivalent_gaugeAct_iff (t s : E → V)
    (k : V → G) (x z : E → G) :
    GaugeEquivalent t s x (NCG.gaugeAct t s k z) ↔
      GaugeEquivalent t s x z := by
  have hmul := (NCG.spin_network (G := G) t s).2.1
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨k⁻¹ * h, ?_⟩
    rw [hmul, hh]
    rw [← hmul, inv_mul_cancel]
    exact (NCG.spin_network (G := G) t s).1 z
  · rintro ⟨h, hh⟩
    refine ⟨k * h, ?_⟩
    rw [hmul, hh]

/-- The indicator of a finite gauge orbit, viewed as a vector in the finite
holonomy Hilbert space. -/
def gaugeOrbitIndicator (t s : E → V) (x : E → G) :
    EuclideanSpace ℂ (E → G) := by
  classical
  exact WithLp.toLp 2 (fun z => if GaugeEquivalent t s x z then 1 else 0)

@[simp] theorem gaugeOrbitIndicator_apply (t s : E → V)
    (x z : E → G) :
    (gaugeOrbitIndicator t s x).ofLp z =
      if GaugeEquivalent t s x z then 1 else 0 := by
  classical
  simp [gaugeOrbitIndicator]

/-- The orbit indicator is a gauge-invariant vector. -/
def gaugeOrbitIndicatorInvariant (t s : E → V) (x : E → G) :
    GaugeInvariantSubspace (G := G) t s := by
  classical
  refine ⟨gaugeOrbitIndicator t s x, ?_⟩
  intro h z
  change (if GaugeEquivalent t s x (NCG.gaugeAct t s h z) then 1 else 0) =
    if GaugeEquivalent t s x z then 1 else 0
  have hiff := gaugeEquivalent_gaugeAct_iff (G := G) t s h x z
  by_cases hz : GaugeEquivalent t s x z
  · have hgz := hiff.mpr hz
    simp [hz, hgz]
  · have hgz : ¬ GaugeEquivalent t s x (NCG.gaugeAct t s h z) :=
      fun hgz => hz (hiff.mp hgz)
    simp [hz, hgz]

/-- Equality on the complete explicit spin-network family is equivalent to
belonging to the same finite vertex-gauge orbit. -/
theorem contractedSpinNetworks_separate_gauge_orbits
    (D : MatrixBlockDecomposition G) (t s : E → V) (x y : E → G) :
    (∀ L : Label D t s,
      contractedPeterWeylVector D t s L x =
        contractedPeterWeylVector D t s L y) ↔
      GaugeEquivalent t s x y := by
  classical
  constructor
  · intro hcoeff
    have hall : ∀ f : GaugeInvariantSubspace (G := G) t s,
        f.1.ofLp x = f.1.ofLp y := by
      intro f
      have hexp := explicitSpinNetworkExpansion D t s f
      have hx := congrArg
        (fun F : GaugeInvariantSubspace (G := G) t s => F.1.ofLp x) hexp
      have hy := congrArg
        (fun F : GaugeInvariantSubspace (G := G) t s => F.1.ofLp y) hexp
      calc
        f.1.ofLp x = ∑ L : Label D t s,
            ((explicitSpinNetworkCoefficientTransform D t s f).ofLp L) *
              contractedPeterWeylVector D t s L x := by simpa using hx
        _ = ∑ L : Label D t s,
            ((explicitSpinNetworkCoefficientTransform D t s f).ofLp L) *
              contractedPeterWeylVector D t s L y := by
              apply Finset.sum_congr rfl
              intro L _
              rw [hcoeff L]
        _ = f.1.ofLp y := by simpa using hy.symm
    have hind := hall (gaugeOrbitIndicatorInvariant t s x)
    change (gaugeOrbitIndicator t s x).ofLp x =
      (gaugeOrbitIndicator t s x).ofLp y at hind
    have hself : GaugeEquivalent t s x x :=
      ⟨1, (NCG.spin_network (G := G) t s).1 x⟩
    rw [gaugeOrbitIndicator_apply, gaugeOrbitIndicator_apply, if_pos hself] at hind
    by_contra hxy
    rw [if_neg hxy] at hind
    exact one_ne_zero hind
  · rintro ⟨h, rfl⟩ L
    exact (contractedPeterWeylVector_gaugeInvariant D t s L h x).symm

/-- The complete coefficient family determines every finite gauge-invariant
function and separates precisely the distinct gauge orbits. -/
theorem closed_spin_networks_separate_gauge_orbits
    (D : MatrixBlockDecomposition G) (t s : E → V) :
    (∀ f : GaugeInvariantSubspace (G := G) t s,
      f = ∑ L : Label D t s,
        ((explicitSpinNetworkCoefficientTransform D t s f).ofLp L) •
          contractedPeterWeylInvariantVector D t s L) ∧
    (∀ x y : E → G,
      (∀ L : Label D t s,
        contractedPeterWeylVector D t s L x =
          contractedPeterWeylVector D t s L y) ↔
        GaugeEquivalent t s x y) :=
  ⟨explicitSpinNetworkExpansion D t s,
    contractedSpinNetworks_separate_gauge_orbits D t s⟩

end FiniteSpinNetwork
end NCG
