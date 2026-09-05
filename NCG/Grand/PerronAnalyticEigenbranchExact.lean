/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AnalyticImplicitFunctionExact
import NCG.Grand.PerronBorderedEigenSystemExact
import NCG.Grand.PerronEigenvalueDerivativeExact
import NCG.Grand.MetzlerIrreducibilityTransportExact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Analytic Perron eigenbranches for finite protected tilts

This file applies the analytic implicit-function compiler to the normalized
Perron eigen-equation of the manuscript's finite protected tilted generator.
The residual includes both the eigen-equation and a fixed left-eigenvector
normalization.  Its derivative in the eigenpair variables is exactly the
bordered Perron operator.
-/

open Matrix Finset Filter Topology
open scoped BigOperators

noncomputable section

namespace NCG.PerronAnalyticEigenbranch

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Eigen-equation plus fixed-left normalization residual. -/
def eigenResidual (L : Matrix S S ℝ) (v : S → ℝ)
    (g : S → S → ℝ) (ell : S → ℝ) :
    ℝ × ((S → ℝ) × ℝ) → ((S → ℝ) × ℝ) :=
  fun z =>
    ((DrivenProcess.tilt L v g z.1).mulVec z.2.1 - z.2.2 • z.2.1,
      ell ⬝ᵥ z.2.1 - 1)

/-- The protected-tilt eigen-residual is real analytic in the tilt and the
candidate normalized eigenpair. -/
theorem eigenResidual_analyticAt
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (ell : S → ℝ) (z : ℝ × ((S → ℝ) × ℝ)) :
    AnalyticAt ℝ (eigenResidual L v g ell) z := by
  have hk : AnalyticAt ℝ
      (fun x : ℝ × ((S → ℝ) × ℝ) => x.1) z := analyticAt_fst
  have hpair : AnalyticAt ℝ
      (fun x : ℝ × ((S → ℝ) × ℝ) => x.2) z := analyticAt_snd
  have hstate : AnalyticAt ℝ
      (fun x : ℝ × ((S → ℝ) × ℝ) => x.2.1) z :=
    analyticAt_fst.comp hpair
  have heigenvalue : AnalyticAt ℝ
      (fun x : ℝ × ((S → ℝ) × ℝ) => x.2.2) z :=
    analyticAt_snd.comp hpair
  have hcoord (j : S) : AnalyticAt ℝ
      (fun x : ℝ × ((S → ℝ) × ℝ) => x.2.1 j) z :=
    by
      simpa using!
        ((ContinuousLinearMap.proj (R := ℝ) j) ∘L
          ContinuousLinearMap.fst ℝ (S → ℝ) ℝ ∘L
          ContinuousLinearMap.snd ℝ ℝ ((S → ℝ) × ℝ)).analyticAt z
  unfold eigenResidual
  apply AnalyticAt.prod
  · apply AnalyticAt.pi
    intro i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, DrivenProcess.tilt]
    apply AnalyticAt.sub
    · have hterm (j : S) : AnalyticAt ℝ
          (fun x : ℝ × ((S → ℝ) × ℝ) =>
            (if i = j then L i i + x.1 * v i
              else L i j * Real.exp (x.1 * g i j)) * x.2.1 j) z := by
          by_cases hij : i = j
          · simpa [hij] using!
              (analyticAt_const.add (hk.mul analyticAt_const)).mul (hcoord j)
          · simpa [hij] using!
              (analyticAt_const.mul
                (analyticAt_rexp.comp (hk.mul analyticAt_const))).mul (hcoord j)
      have hs := Finset.univ.analyticAt_fun_sum
        (𝕜 := ℝ)
        (f := fun (j : S) (x : ℝ × ((S → ℝ) × ℝ)) =>
          (if i = j then L i i + x.1 * v i
            else L i j * Real.exp (x.1 * g i j)) * x.2.1 j)
        (fun j _ => hterm j)
      simpa using! hs
    · exact heigenvalue.mul (hcoord i)
  · simp only [dotProduct]
    apply AnalyticAt.sub
    · have hterm (j : S) : AnalyticAt ℝ
          (fun x : ℝ × ((S → ℝ) × ℝ) => ell j * x.2.1 j) z :=
          analyticAt_const.mul (hcoord j)
      have hs := Finset.univ.analyticAt_fun_sum
        (𝕜 := ℝ)
        (f := fun (j : S) (x : ℝ × ((S → ℝ) × ℝ)) => ell j * x.2.1 j)
        (fun j _ => hterm j)
      simpa using! hs
    · exact analyticAt_const

/-- At a fixed tilt, the Fréchet derivative of the normalized eigen-residual
in `(right eigenvector, eigenvalue)` is the bordered Perron operator. -/
theorem hasFDerivAt_eigenResidual_fixedTilt
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (ell r : S → ℝ) (k psi : ℝ) :
    HasFDerivAt
      (fun y : (S → ℝ) × ℝ => eigenResidual L v g ell (k, y))
      (PerronBorderedEigenSystem.borderedContinuousOperator
        (DrivenProcess.tilt L v g k) r ell psi)
      (r, psi) := by
  let A := DrivenProcess.tilt L v g k
  let Amul : (S → ℝ) →L[ℝ] (S → ℝ) :=
    A.mulVecLin.toContinuousLinearMap
  let ellDot : (S → ℝ) →L[ℝ] ℝ :=
    (dotProductBilin ℝ ℝ ell).toContinuousLinearMap
  have hmul : HasFDerivAt
      (fun y : (S → ℝ) × ℝ => A.mulVec y.1)
      (Amul ∘L ContinuousLinearMap.fst ℝ (S → ℝ) ℝ) (r, psi) := by
    simpa [Amul, A] using
      Amul.hasFDerivAt.comp (r, psi) hasFDerivAt_fst
  have hscale : HasFDerivAt
      (fun y : (S → ℝ) × ℝ => y.2 • y.1)
      (psi • ContinuousLinearMap.fst ℝ (S → ℝ) ℝ +
        (ContinuousLinearMap.snd ℝ (S → ℝ) ℝ).smulRight r)
      (r, psi) := by
    have hsnd : HasFDerivAt
        (fun y : (S → ℝ) × ℝ => y.2)
        (ContinuousLinearMap.snd ℝ (S → ℝ) ℝ) (r, psi) :=
      hasFDerivAt_snd
    have hfst : HasFDerivAt
        (fun y : (S → ℝ) × ℝ => y.1)
        (ContinuousLinearMap.fst ℝ (S → ℝ) ℝ) (r, psi) :=
      hasFDerivAt_fst
    exact hsnd.smul hfst
  have hfirst := hmul.sub hscale
  have hdot : HasFDerivAt
      (fun y : (S → ℝ) × ℝ => ell ⬝ᵥ y.1)
      (ellDot ∘L ContinuousLinearMap.fst ℝ (S → ℝ) ℝ) (r, psi) := by
    change HasFDerivAt
      (fun y : (S → ℝ) × ℝ => (dotProductBilin ℝ ℝ ell) y.1)
      (ellDot ∘L ContinuousLinearMap.fst ℝ (S → ℝ) ℝ) (r, psi)
    exact ellDot.hasFDerivAt.comp (r, psi) hasFDerivAt_fst
  have hsecond : HasFDerivAt
      (fun y : (S → ℝ) × ℝ => ell ⬝ᵥ y.1 - 1)
      (ellDot ∘L ContinuousLinearMap.fst ℝ (S → ℝ) ℝ) (r, psi) := by
    simpa using hdot.sub_const 1
  let D : ((S → ℝ) × ℝ) →L[ℝ] ((S → ℝ) × ℝ) :=
    (Amul ∘L ContinuousLinearMap.fst ℝ (S → ℝ) ℝ -
      (psi • ContinuousLinearMap.fst ℝ (S → ℝ) ℝ +
        (ContinuousLinearMap.snd ℝ (S → ℝ) ℝ).smulRight r)).prod
      (ellDot ∘L ContinuousLinearMap.fst ℝ (S → ℝ) ℝ)
  have hD : D = PerronBorderedEigenSystem.borderedContinuousOperator
      (DrivenProcess.tilt L v g k) r ell psi := by
    apply ContinuousLinearMap.ext
    rintro ⟨y, a⟩
    apply Prod.ext
    · ext i
      change (D (y, a)).1 i =
        ((DrivenProcess.tilt L v g k).mulVec y - psi • y - a • r) i
      simp [D, Amul, A,
        PerronBorderedEigenSystem.borderedContinuousOperator,
        PerronBorderedEigenSystem.borderedOperator]
      ring
    · simp [D, Amul, ellDot, A,
        PerronBorderedEigenSystem.borderedContinuousOperator,
        PerronBorderedEigenSystem.borderedOperator]
  rw [← hD]
  change HasFDerivAt
    (fun y : (S → ℝ) × ℝ =>
      (A.mulVec y.1 - y.2 • y.1, ell ⬝ᵥ y.1 - 1)) D (r, psi)
  exact hfirst.prodMk hsecond

/-- The partial derivative of the full residual in the eigenpair variables
is exactly the bordered Perron operator. -/
theorem fderiv_eigenResidual_comp_inr
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (ell r : S → ℝ) (k psi : ℝ) :
    fderiv ℝ (eigenResidual L v g ell) (k, (r, psi)) ∘L
        ContinuousLinearMap.inr ℝ ℝ ((S → ℝ) × ℝ) =
      PerronBorderedEigenSystem.borderedContinuousOperator
        (DrivenProcess.tilt L v g k) r ell psi := by
  have hfull :=
    (eigenResidual_analyticAt L v g ell (k, (r, psi))).hasStrictFDerivAt.hasFDerivAt
  have hinclusion : HasFDerivAt
      (fun y : (S → ℝ) × ℝ => (k, y))
      (ContinuousLinearMap.inr ℝ ℝ ((S → ℝ) × ℝ)) (r, psi) := by
    simpa using!
      (hasFDerivAt_const (x := (r, psi)) (c := k)).prodMk
        (hasFDerivAt_id (𝕜 := ℝ) (x := (r, psi)))
  exact (hfull.comp (r, psi) hinclusion).unique
    (hasFDerivAt_eigenResidual_fixedTilt L v g ell r k psi)

/-- A simple normalized eigenpair of a protected finite tilt extends to a
local real-analytic eigenpair branch.  The branch keeps the fixed-left
normalization and remains strictly positive near the base point when the
base right eigenvector is strictly positive. -/
theorem exists_local_analytic_eigenbranch
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (ell r : S → ℝ) (k psi : ℝ)
    (hr : ∀ i, 0 < r i)
    (hright : (DrivenProcess.tilt L v g k).mulVec r = psi • r)
    (hleft : (DrivenProcess.tilt L v g k).vecMul ell = psi • ell)
    (hnorm : ell ⬝ᵥ r = 1)
    (hsimple : ∀ z : S → ℝ,
      (DrivenProcess.tilt L v g k).mulVec z = psi • z →
        ∃ b : ℝ, z = b • r) :
    ∃ (rBranch : ℝ → S → ℝ) (psiBranch : ℝ → ℝ),
      AnalyticAt ℝ rBranch k ∧
      AnalyticAt ℝ psiBranch k ∧
      rBranch k = r ∧ psiBranch k = psi ∧
      (∀ᶠ q in 𝓝 k, (∀ i, 0 < rBranch q i) ∧
        (DrivenProcess.tilt L v g q).mulVec (rBranch q) =
          psiBranch q • rBranch q ∧
        ell ⬝ᵥ rBranch q = 1) := by
  let hf := eigenResidual_analyticAt L v g ell (k, (r, psi))
  let dfu := hf.hasStrictFDerivAt
  have hpartial :
      (fderiv ℝ (eigenResidual L v g ell) (k, (r, psi)) ∘L
        ContinuousLinearMap.inr ℝ ℝ ((S → ℝ) × ℝ)).IsInvertible := by
    rw [fderiv_eigenResidual_comp_inr]
    exact PerronBorderedEigenSystem.borderedContinuousOperator_isInvertible
      (DrivenProcess.tilt L v g k) r ell psi hleft hnorm hsimple
  let branch : ℝ → ((S → ℝ) × ℝ) :=
    dfu.implicitFunctionOfProdDomain hpartial
  have hbranchAnalytic : AnalyticAt ℝ branch k := by
    simpa [branch, dfu, hf] using
      (AnalyticImplicitFunction.analyticAt_implicitFunctionOfProdDomain
        (eigenResidual_analyticAt L v g ell (k, (r, psi))) hpartial)
  have hbranchBase : branch k = (r, psi) := by
    have hiff :=
      (dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain
        hpartial).self_of_nhds
    exact hiff.mp rfl
  let rBranch : ℝ → S → ℝ := fun q => (branch q).1
  let psiBranch : ℝ → ℝ := fun q => (branch q).2
  have hrAnalytic : AnalyticAt ℝ rBranch k := by
    simpa [rBranch] using! analyticAt_fst.comp hbranchAnalytic
  have hpsiAnalytic : AnalyticAt ℝ psiBranch k := by
    simpa [psiBranch] using! analyticAt_snd.comp hbranchAnalytic
  have hrBase : rBranch k = r := by
    simpa [rBranch] using congrArg Prod.fst hbranchBase
  have hpsiBase : psiBranch k = psi := by
    simpa [psiBranch] using congrArg Prod.snd hbranchBase
  have hpositive : ∀ᶠ q in 𝓝 k, ∀ i, 0 < rBranch q i := by
    rw [Filter.eventually_all]
    intro i
    have htend : Tendsto (fun q => rBranch q i) (𝓝 k) (𝓝 (r i)) := by
      have htend0 : Tendsto (fun q => rBranch q i) (𝓝 k) (𝓝 (rBranch k i)) := by
        exact (continuous_apply i).continuousAt.comp_of_eq
          hrAnalytic.continuousAt rfl
      rw [congrFun hrBase i] at htend0
      exact htend0
    exact htend (Ioi_mem_nhds (hr i))
  have hresidualBase : eigenResidual L v g ell (k, (r, psi)) = 0 := by
    apply Prod.ext
    · change (DrivenProcess.tilt L v g k).mulVec r - psi • r = 0
      rw [hright]
      exact sub_self _
    · change ell ⬝ᵥ r - 1 = 0
      rw [hnorm]
      norm_num
  have hresidual : ∀ᶠ q in 𝓝 k,
      eigenResidual L v g ell (q, branch q) = 0 := by
    have hevent := dfu.eventually_apply_implicitFunctionOfProdDomain hpartial
    simpa [branch, hresidualBase] using hevent
  refine ⟨rBranch, psiBranch, hrAnalytic, hpsiAnalytic,
    hrBase, hpsiBase, ?_⟩
  filter_upwards [hpositive, hresidual] with q hqpos hqres
  have hfirst := congrArg Prod.fst hqres
  have hsecond := congrArg Prod.snd hqres
  refine ⟨hqpos, ?_, ?_⟩
  · change (DrivenProcess.tilt L v g q).mulVec (rBranch q) -
      psiBranch q • rBranch q = 0 at hfirst
    exact sub_eq_zero.mp hfirst
  · change ell ⬝ᵥ rBranch q - 1 = 0 at hsecond
    linarith

/-- When every protected tilt is irreducible Metzler, the canonical Perron
exponent is real analytic at every tilt parameter.  This identifies the local
implicit-function eigenvalue branch with the repository's explicit SCGF
exponent rather than leaving it as an unspecified eigenvalue. -/
theorem analyticAt_tiltedPerronExponent
    [Nonempty S]
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (hirr : ∀ q : ℝ,
      MetzlerExponentialPositivity.IsIrreducibleMetzler
        (DrivenProcess.tilt L v g q))
    (k : ℝ) :
    AnalyticAt ℝ
      (fun q => MetzlerPerronExponent.exponent
        (DrivenProcess.tilt L v g q)) k := by
  obtain ⟨r, ell, hr, _hell, hright, hleft, hnorm⟩ :=
    MetzlerPerronExponent.exists_normalized_positive_left_right_eigenvectors
      (DrivenProcess.tilt L v g k) (hirr k)
  have hsimple : ∀ z : S → ℝ,
      (DrivenProcess.tilt L v g k).mulVec z =
          MetzlerPerronExponent.exponent (DrivenProcess.tilt L v g k) • z →
        ∃ b : ℝ, z = b • r := by
    intro z hz
    exact MetzlerPerronExponent.eigenspace_is_one_dimensional
      (DrivenProcess.tilt L v g k) (hirr k) hr hright hz
  obtain ⟨rBranch, psiBranch, _hrAnalytic, hpsiAnalytic,
      _hrBase, _hpsiBase, hbranch⟩ :=
    exists_local_analytic_eigenbranch L v g ell r k
      (MetzlerPerronExponent.exponent (DrivenProcess.tilt L v g k))
      hr hright hleft hnorm hsimple
  apply hpsiAnalytic.congr
  filter_upwards [hbranch] with q hq
  exact MetzlerPerronExponent.eigenvalue_eq_exponent
    (DrivenProcess.tilt L v g q) (hirr q) hq.1 hq.2.1

/-- The derivative of the canonical finite-tilt Perron exponent is the
normalized left/right Perron pairing with the differentiated tilt.  The
analytic branch and its differentiability are constructed internally. -/
theorem hasDerivAt_tiltedPerronExponent
    [Nonempty S]
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (hirr : ∀ q : ℝ,
      MetzlerExponentialPositivity.IsIrreducibleMetzler
        (DrivenProcess.tilt L v g q))
    (k : ℝ) (r ell : S → ℝ)
    (hr : ∀ i, 0 < r i)
    (hright : (DrivenProcess.tilt L v g k).mulVec r =
      MetzlerPerronExponent.exponent (DrivenProcess.tilt L v g k) • r)
    (hleft : (DrivenProcess.tilt L v g k).vecMul ell =
      MetzlerPerronExponent.exponent (DrivenProcess.tilt L v g k) • ell)
    (hnorm : ell ⬝ᵥ r = 1) :
    HasDerivAt
      (fun q => MetzlerPerronExponent.exponent
        (DrivenProcess.tilt L v g q))
      (ell ⬝ᵥ (PerronEigenvalueDerivative.tiltDerivative L v g k).mulVec r)
      k := by
  have hsimple : ∀ z : S → ℝ,
      (DrivenProcess.tilt L v g k).mulVec z =
          MetzlerPerronExponent.exponent (DrivenProcess.tilt L v g k) • z →
        ∃ b : ℝ, z = b • r := by
    intro z hz
    exact MetzlerPerronExponent.eigenspace_is_one_dimensional
      (DrivenProcess.tilt L v g k) (hirr k) hr hright hz
  obtain ⟨rBranch, psiBranch, hrAnalytic, hpsiAnalytic,
      hrBase, hpsiBase, hbranch⟩ :=
    exists_local_analytic_eigenbranch L v g ell r k
      (MetzlerPerronExponent.exponent (DrivenProcess.tilt L v g k))
      hr hright hleft hnorm hsimple
  let r' : S → ℝ := fun i => deriv (fun q => rBranch q i) k
  let psi' : ℝ := deriv psiBranch k
  have hrDeriv : ∀ i, HasDerivAt (fun q => rBranch q i) (r' i) k := by
    intro i
    apply DifferentiableAt.hasDerivAt
    have hc := ((ContinuousLinearMap.proj (R := ℝ) i).analyticAt (rBranch k)).comp
      hrAnalytic
    exact hc.differentiableAt
  have hpsiDeriv : HasDerivAt psiBranch psi' k := by
    exact hpsiAnalytic.differentiableAt.hasDerivAt
  have heig : ∀ᶠ q in 𝓝 k,
      (DrivenProcess.tilt L v g q).mulVec (rBranch q) =
        psiBranch q • rBranch q := hbranch.mono fun q hq => hq.2.1
  have hformula : psi' =
      ell ⬝ᵥ (PerronEigenvalueDerivative.tiltDerivative L v g k).mulVec r := by
    have hbranchFormula :=
      PerronEigenvalueDerivative.tilted_eigenvalue_derivative_of_eventual_branch
        L v g rBranch psiBranch k r' ell psi'
        hrDeriv hpsiDeriv heig
        (by simpa [hpsiBase] using hleft)
        (by simpa [hrBase] using hnorm)
    simpa [hrBase] using hbranchFormula
  have heq : psiBranch =ᶠ[𝓝 k]
      fun q => MetzlerPerronExponent.exponent
        (DrivenProcess.tilt L v g q) := by
    filter_upwards [hbranch] with q hq
    exact MetzlerPerronExponent.eigenvalue_eq_exponent
      (DrivenProcess.tilt L v g q) (hirr q) hq.1 hq.2.1
  exact (hpsiDeriv.congr_of_eventuallyEq heq.symm).congr_deriv hformula

/-- For a nontrivial finite generator, irreducibility at one protected tilt
automatically supplies the all-parameter irreducibility needed for analytic
Perron perturbation. -/
theorem analyticAt_tiltedPerronExponent_of_generator
    [Nontrivial S]
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hk : MetzlerExponentialPositivity.IsIrreducibleMetzler
      (DrivenProcess.tilt L v g k)) :
    AnalyticAt ℝ
      (fun q => MetzlerPerronExponent.exponent
        (DrivenProcess.tilt L v g q)) k := by
  apply analyticAt_tiltedPerronExponent L v g
  intro q
  exact MetzlerIrreducibilityTransport.tilt_isIrreducibleMetzler_of_base
    L hL v g k q hk

/-- Generator-specialized canonical SCGF derivative formula, requiring
irreducibility only at the differentiation parameter. -/
theorem hasDerivAt_tiltedPerronExponent_of_generator
    [Nontrivial S]
    (L : Matrix S S ℝ) (hL : DrivenProcess.IsGenerator L)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hk : MetzlerExponentialPositivity.IsIrreducibleMetzler
      (DrivenProcess.tilt L v g k))
    (r ell : S → ℝ)
    (hr : ∀ i, 0 < r i)
    (hright : (DrivenProcess.tilt L v g k).mulVec r =
      MetzlerPerronExponent.exponent (DrivenProcess.tilt L v g k) • r)
    (hleft : (DrivenProcess.tilt L v g k).vecMul ell =
      MetzlerPerronExponent.exponent (DrivenProcess.tilt L v g k) • ell)
    (hnorm : ell ⬝ᵥ r = 1) :
    HasDerivAt
      (fun q => MetzlerPerronExponent.exponent
        (DrivenProcess.tilt L v g q))
      (ell ⬝ᵥ (PerronEigenvalueDerivative.tiltDerivative L v g k).mulVec r)
      k := by
  apply hasDerivAt_tiltedPerronExponent L v g
    (fun q => MetzlerIrreducibilityTransport.tilt_isIrreducibleMetzler_of_base
      L hL v g k q hk) k r ell hr hright hleft hnorm

end NCG.PerronAnalyticEigenbranch
