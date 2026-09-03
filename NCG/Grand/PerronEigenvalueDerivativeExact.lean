/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MetzlerPerronExponentExact

/-!
# Exact derivative compiler for finite Perron eigenvalues

This file isolates two reusable ingredients in analytic finite-state
Feynman--Kac arguments.  First, it differentiates the concrete protected
state/jump tilted generator entry by entry.  Second, it proves the normalized
left/right eigenvector derivative formula by cancelling the derivative of the
right eigenvector from the differentiated eigen-equation.

Existence of a differentiable eigenbranch is deliberately not assumed away:
the final theorem takes that differentiability data explicitly.  It is the
linear-algebra endpoint needed after an implicit-function or analytic
perturbation construction.
-/

open Matrix Finset Filter Topology
open scoped BigOperators

noncomputable section

namespace NCG.PerronEigenvalueDerivative

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Entrywise derivative of the protected tilted generator with respect to
the tilt parameter. -/
def tiltDerivative (L : Matrix S S ℝ) (v : S → ℝ)
    (g : S → S → ℝ) (k : ℝ) : Matrix S S ℝ :=
  fun u w => if u = w then v u
    else L u w * (Real.exp (k * g u w) * g u w)

/-- Every entry of the concrete protected tilt is differentiable, with the
corresponding entry of `tiltDerivative` as derivative. -/
theorem hasDerivAt_tilt_entry (L : Matrix S S ℝ) (v : S → ℝ)
    (g : S → S → ℝ) (k : ℝ) (u w : S) :
    HasDerivAt (fun q : ℝ => DrivenProcess.tilt L v g q u w)
      (tiltDerivative L v g k u w) k := by
  by_cases huw : u = w
  · subst w
    simpa [DrivenProcess.tilt, tiltDerivative] using
      (hasDerivAt_id k).mul_const (v u)
  · have hinner : HasDerivAt (fun q : ℝ => q * g u w) (g u w) k := by
      simpa using (hasDerivAt_id k).mul_const (g u w)
    have hexp : HasDerivAt
        (fun q : ℝ => Real.exp (q * g u w))
        (Real.exp (k * g u w) * g u w) k := by
      simpa using hinner.exp
    simpa [DrivenProcess.tilt, tiltDerivative, huw] using
      hexp.const_mul (L u w)

/-- Normalized finite-dimensional left/right eigenvector differentiation.
If the eigen-equation has been differentiated, pairing with a normalized left
eigenvector eliminates the unknown derivative of the right eigenvector. -/
theorem eigenvalue_derivative_of_differentiated_equation
    (A A' : Matrix S S ℝ) (r r' ell : S → ℝ)
    (psi psi' : ℝ)
    (hleft : A.vecMul ell = psi • ell)
    (hnorm : ell ⬝ᵥ r = 1)
    (hdiff : A'.mulVec r + A.mulVec r' =
      psi' • r + psi • r') :
    psi' = ell ⬝ᵥ A'.mulVec r := by
  have hpair := congrArg (fun z : S → ℝ => ell ⬝ᵥ z) hdiff
  have hcancel : ell ⬝ᵥ A.mulVec r' = psi * (ell ⬝ᵥ r') := by
    rw [Matrix.dotProduct_mulVec, hleft]
    simp
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul,
    hnorm, mul_one] at hpair
  rw [hcancel] at hpair
  linarith

/-- Specialized derivative formula for the protected state/jump tilt. -/
theorem tilted_eigenvalue_derivative
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (r r' ell : S → ℝ) (psi psi' : ℝ)
    (hleft : (DrivenProcess.tilt L v g k).vecMul ell = psi • ell)
    (hnorm : ell ⬝ᵥ r = 1)
    (hdiff : (tiltDerivative L v g k).mulVec r +
        (DrivenProcess.tilt L v g k).mulVec r' =
      psi' • r + psi • r') :
    psi' = ell ⬝ᵥ (tiltDerivative L v g k).mulVec r :=
  eigenvalue_derivative_of_differentiated_equation
    (DrivenProcess.tilt L v g k) (tiltDerivative L v g k)
    r r' ell psi psi' hleft hnorm hdiff

/-- Differentiate a finite matrix eigen-equation coordinatewise.  This is the
calculus bridge between differentiable matrix/eigenvector branches and the
algebraic cancellation theorem above. -/
theorem differentiated_eigen_equation
    (A : ℝ → Matrix S S ℝ) (r : ℝ → S → ℝ) (psi : ℝ → ℝ)
    (k : ℝ) (A' : Matrix S S ℝ) (r' : S → ℝ) (psi' : ℝ)
    (hA : ∀ i j, HasDerivAt (fun q => A q i j) (A' i j) k)
    (hr : ∀ i, HasDerivAt (fun q => r q i) (r' i) k)
    (hpsi : HasDerivAt psi psi' k)
    (heig : ∀ q, (A q).mulVec (r q) = psi q • r q) :
    A'.mulVec (r k) + (A k).mulVec r' =
      psi' • r k + psi k • r' := by
  funext i
  have hsum := HasDerivAt.sum (u := Finset.univ) fun j _ =>
    (hA i j).mul (hr j)
  have hsumFunction :
      (∑ j : S, (fun q : ℝ => A q i j) * (fun q => r q j)) =
        fun q => (A q).mulVec (r q) i := by
    funext q
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [hsumFunction] at hsum
  have hleft : HasDerivAt
      (fun q => (A q).mulVec (r q) i)
      ((A'.mulVec (r k) + (A k).mulVec r') i) k := by
    simpa [Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using hsum
  have hright := hpsi.mul (hr i)
  have hsame :
      (fun q => (A q).mulVec (r q) i) =
        psi * fun q => r q i := by
    funext q
    have hi := congrFun (heig q) i
    simpa using hi
  rw [hsame] at hleft
  have hderiv := hleft.unique hright
  simpa using hderiv

/-- Local form of `differentiated_eigen_equation`: an eigen-equation holding
on a neighborhood of the differentiation point is sufficient. -/
theorem differentiated_eigen_equation_of_eventually
    (A : ℝ → Matrix S S ℝ) (r : ℝ → S → ℝ) (psi : ℝ → ℝ)
    (k : ℝ) (A' : Matrix S S ℝ) (r' : S → ℝ) (psi' : ℝ)
    (hA : ∀ i j, HasDerivAt (fun q => A q i j) (A' i j) k)
    (hr : ∀ i, HasDerivAt (fun q => r q i) (r' i) k)
    (hpsi : HasDerivAt psi psi' k)
    (heig : ∀ᶠ q in 𝓝 k,
      (A q).mulVec (r q) = psi q • r q) :
    A'.mulVec (r k) + (A k).mulVec r' =
      psi' • r k + psi k • r' := by
  funext i
  have hsum := HasDerivAt.sum (u := Finset.univ) fun j _ =>
    (hA i j).mul (hr j)
  have hsumFunction :
      (∑ j : S, (fun q : ℝ => A q i j) * (fun q => r q j)) =
        fun q => (A q).mulVec (r q) i := by
    funext q
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [hsumFunction] at hsum
  have hleft : HasDerivAt
      (fun q => (A q).mulVec (r q) i)
      ((A'.mulVec (r k) + (A k).mulVec r') i) k := by
    simpa [Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using hsum
  have hright := hpsi.mul (hr i)
  have hsame :
      (fun q => (A q).mulVec (r q) i) =ᶠ[𝓝 k]
        fun q => psi q * r q i := by
    filter_upwards [heig] with q hq
    have hi := congrFun hq i
    simpa using hi
  have hleft' := hleft.congr_of_eventuallyEq hsame.symm
  have hderiv := hleft'.unique hright
  simpa using hderiv

/-- Local-neighborhood version of the protected-tilt eigenvalue derivative
formula. -/
theorem tilted_eigenvalue_derivative_of_eventual_branch
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (r : ℝ → S → ℝ) (psi : ℝ → ℝ) (k : ℝ)
    (r' ell : S → ℝ) (psi' : ℝ)
    (hr : ∀ i, HasDerivAt (fun q => r q i) (r' i) k)
    (hpsi : HasDerivAt psi psi' k)
    (heig : ∀ᶠ q in 𝓝 k,
      (DrivenProcess.tilt L v g q).mulVec (r q) =
        psi q • r q)
    (hleft : (DrivenProcess.tilt L v g k).vecMul ell = psi k • ell)
    (hnorm : ell ⬝ᵥ r k = 1) :
    psi' = ell ⬝ᵥ (tiltDerivative L v g k).mulVec (r k) := by
  apply tilted_eigenvalue_derivative L v g k (r k) r' ell
    (psi k) psi' hleft hnorm
  exact differentiated_eigen_equation_of_eventually
    (fun q => DrivenProcess.tilt L v g q) r psi k
    (tiltDerivative L v g k) r' psi'
    (fun i j => hasDerivAt_tilt_entry L v g k i j)
    hr hpsi heig

/-- Full first-derivative formula for a differentiable eigenbranch of the
protected tilted generator. -/
theorem tilted_eigenvalue_derivative_of_branches
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (r : ℝ → S → ℝ) (psi : ℝ → ℝ) (k : ℝ)
    (r' ell : S → ℝ) (psi' : ℝ)
    (hr : ∀ i, HasDerivAt (fun q => r q i) (r' i) k)
    (hpsi : HasDerivAt psi psi' k)
    (heig : ∀ q, (DrivenProcess.tilt L v g q).mulVec (r q) =
      psi q • r q)
    (hleft : (DrivenProcess.tilt L v g k).vecMul ell = psi k • ell)
    (hnorm : ell ⬝ᵥ r k = 1) :
    psi' = ell ⬝ᵥ (tiltDerivative L v g k).mulVec (r k) := by
  apply tilted_eigenvalue_derivative L v g k (r k) r' ell
    (psi k) psi' hleft hnorm
  exact differentiated_eigen_equation
    (fun q => DrivenProcess.tilt L v g q) r psi k
    (tiltDerivative L v g k) r' psi'
    (fun i j => hasDerivAt_tilt_entry L v g k i j)
    hr hpsi heig

end NCG.PerronEigenvalueDerivative
