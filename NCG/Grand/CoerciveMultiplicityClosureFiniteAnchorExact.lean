/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteAnchorHoweActualExact
import NCG.Grand.MultiplicityClosureTransportExact
import NCG.Grand.CoherentClosure
import NCG.Grand.CoherentClosureSchurEstimateExact
import NCG.Grand.ProtectedSpectralProjectionRigidity

/-!
# Coercive multiplicity closure at a finite Howe anchor

This is the finite-anchor branch of
`thm:SMST-coercive-multiplicity-closure`.  It compiles the actual joint
commutator estimate, uniqueness of the orthogonal commutant projection,
two presentations of the same multiplicity-quiver algebra, isometric
transport of the rank-three endpoint source, and the exact coherent writer.

The continuum alternative (including compact graph-screen exhaustion and
norm convergence of the commutant projections) is the theorem
`NCG.VaryingHilbert.System.coerciveContinuumHoweDuality_exact`.
-/

open Filter Matrix NormedSpace Set Topology
open scoped ComplexOrder

noncomputable section

namespace NCG

/-- **Coercive SM--spacetime multiplicity closure, finite-anchor branch.**

None of the displayed closure conclusions is assumed: commutant equality and
the spectral floor come from the finite-anchor perturbation theorem;
projection stability comes from uniqueness of orthogonal projections;
quiver stability is the comparison of two exact presentations; endpoint
rank and its positive Gram floor are transported through an isometry; and
the two coherent-writer conclusions follow from the reducing entire-series
identity and the local principal-log estimate. -/
theorem coerciveMultiplicityClosure_finiteAnchor_exact
    {n m q : Type*} [Fintype n] [Fintype m] [Fintype q]
    [DecidableEq n] [DecidableEq q]
    {s : ℕ}
    (c₀ c : Fin s → Matrix n n ℂ)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (γ₀ C C₀ ε : ℝ)
    (hγ : 0 < γ₀) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hε : 0 ≤ ε)
    (hM₀ : M ≤ LinearMap.ker (jointCommutatorL2 c₀))
    (hM : M ≤ LinearMap.ker (jointCommutatorL2 c))
    (hanchor : ∀ x ∈ Mᗮ,
      γ₀ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 c₀ x‖ ^ 2)
    (hpert : ∀ x,
      |‖jointCommutatorL2 c x‖ ^ 2 - ‖jointCommutatorL2 c₀ x‖ ^ 2|
        ≤ 4 * (C + C₀) * ε * ‖x‖ ^ 2)
    (hsmall : 4 * (C + C₀) * ε < γ₀)
    (P₀ P : EuclideanSpace ℂ (n × n) →L[ℂ]
      EuclideanSpace ℂ (n × n))
    (hP₀ : IsStarProjection P₀) (hP : IsStarProjection P)
    (hP₀range : LinearMap.range P₀.toLinearMap = M)
    (hPrange : LinearMap.range P.toLinearMap =
      LinearMap.ker (jointCommutatorL2 c))
    {Q₀ Q QEnd : Type*}
    [Semiring Q₀] [Algebra ℂ Q₀] [Semiring Q] [Algebra ℂ Q]
    [Semiring QEnd] [Algebra ℂ QEnd]
    (quiver₀ : Q₀ ≃ₐ[ℂ] QEnd) (quiver : Q ≃ₐ[ℂ] QEnd)
    (I : Matrix m n ℂ) (S : Matrix n q ℂ)
    (hI : Iᴴ * I = 1) (η : ℝ) (hη : 0 < η)
    (hSrank : S.rank = 3)
    (hSlow : (Sᴴ * S - (η : ℂ) • 1).PosSemidef)
    {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A]
    (x v y : A) (W : ℝ → A) (t : ℝ) (ht : t ≠ 0)
    (hred : x * v = v * y)
    (hseries : HasSum (fun k : ℕ =>
      (t ^ (2 * k) / (((2 * k + 1).factorial : ℝ))) •
        y ^ (2 * k)) (W t))
    (K : ℝ) (hK : 0 ≤ K)
    (hquad : ∀ᶠ u in nhdsWithin 0 (Ioi 0),
      ‖W u - 1‖ ≤ K * u ^ 2)
    (hhalf : ∀ᶠ u in nhdsWithin 0 (Ioi 0),
      ‖W u - 1‖ ≤ 1 / 2) :
    LinearMap.ker (jointCommutatorL2 c) = M
    ∧ 0 < γ₀ - 4 * (C + C₀) * ε
    ∧ (∀ z ∈ Mᗮ,
        (γ₀ - 4 * (C + C₀) * ε) * ‖z‖ ^ 2
          ≤ ‖jointCommutatorL2 c z‖ ^ 2)
    ∧ P = P₀
    ∧ Nonempty (Q₀ ≃ₐ[ℂ] Q)
    ∧ (I * S).rank = 3
    ∧ 0 < η
    ∧ ((I * S)ᴴ * (I * S) - (η : ℂ) • 1).PosSemidef
    ∧ (2 * t)⁻¹ • (exp (t • x) - exp (-(t • x))) * v
        - (x * v) * W t = 0
    ∧ Tendsto (fun u : ℝ => (2 * u)⁻¹ •
        CoherentClosureSchurEstimateExact.localPrincipalLog (W u))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  obtain ⟨hker, hgap, hfloor, _, _⟩ :=
    finiteAnchorHowe_actualJointCommutator c₀ c M γ₀ C C₀ ε
      hγ hC hC₀ hε hM₀ hM hanchor hpert hsmall
  have hProj : P = P₀ := by
    apply ContinuousLinearMap.IsStarProjection.ext hP hP₀
    rw [hPrange, hker, hP₀range]
  have hquiver : Nonempty (Q₀ ≃ₐ[ℂ] Q) :=
    ⟨quiver₀.trans quiver.symm⟩
  have hrank : (I * S).rank = 3 := by
    rw [MultiplicityClosure.isometric_rank_invariant I S hI, hSrank]
  have hlower :
      ((I * S)ᴴ * (I * S) - (η : ℂ) • 1).PosSemidef :=
    MultiplicityClosure.gram_lower_bound_invariant I S hI (η : ℂ) hSlow
  have hclosure := (reducing_coherent_closure x v y (W t) t ht hred hseries).1
  have hresidual :
      (2 * t)⁻¹ • (exp (t • x) - exp (-(t • x))) * v
          - (x * v) * W t = 0 := sub_eq_zero.mpr hclosure
  have hlog :=
    CoherentClosureSchurEstimateExact.localPrincipalLog_div_physicalStep_tendsto_zero
      W K hK hquad hhalf
  exact ⟨hker, hgap, hfloor, hProj, hquiver, hrank, hη, hlower,
    hresidual, hlog⟩

end NCG
