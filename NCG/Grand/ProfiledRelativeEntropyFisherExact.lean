/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MoorePenroseSchurExact
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Relative-entropy Fisher Hessians and exact nuisance profiling

This file isolates the two rigorous steps behind the profiled Fisher limit.
First, the second derivative of finite relative entropy along a normalized
full-support `C²` law path is the Fisher norm of its score tangent.  Second,
profiling that quadratic germ over nuisance directions is exactly the
Moore--Penrose Schur innovation.
-/

open ContinuousLinearMap Filter
open scoped RealInnerProductSpace InnerProduct

namespace NCG

/-! ## Finite relative-entropy second derivative -/

/-- Derivatives commute with a finite Fintype sum. -/
theorem hasDerivAt_finite_sum {ι : Type*} [Fintype ι]
    (A : ι → ℝ → ℝ) (A' : ι → ℝ) (x : ℝ)
    (h : ∀ i, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y => ∑ i, A i y) (∑ i, A' i) x := by
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ => h i)
  have hfun : (fun y => ∑ i, A i y) = ∑ i, A i := by
    funext y
    simp [Finset.sum_apply]
  rw [hfun]
  exact hs

/-- Finite relative entropy written in the log-difference form convenient for
differentiation.  For positive laws this is `∑ p log (p/q)`. -/
noncomputable def finiteRelativeEntropyPath {Ω : Type*} [Fintype Ω]
    (p : ℝ → Ω → ℝ) (q : Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ ω, p t ω * (Real.log (p t ω) - Real.log (q ω))

/-- The derivative formula for a finite relative-entropy path. -/
noncomputable def finiteRelativeEntropyPathDerivative
    {Ω : Type*} [Fintype Ω]
    (p p' : ℝ → Ω → ℝ) (q : Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ ω, p' t ω *
    (Real.log (p t ω) - Real.log (q ω) + 1)

/-- A full-support differentiable finite law path has the standard
relative-entropy derivative. -/
theorem hasDerivAt_finiteRelativeEntropyPath
    {Ω : Type*} [Fintype Ω]
    (p p' : ℝ → Ω → ℝ) (q : Ω → ℝ) (t : ℝ)
    (hp : ∀ ω, HasDerivAt (fun u => p u ω) (p' t ω) t)
    (hpos : ∀ ω, 0 < p t ω) :
    HasDerivAt (finiteRelativeEntropyPath p q)
      (finiteRelativeEntropyPathDerivative p p' q t) t := by
  unfold finiteRelativeEntropyPath finiteRelativeEntropyPathDerivative
  apply hasDerivAt_finite_sum
  intro ω
  have hlog := (hp ω).log (hpos ω).ne'
  have hterm := (hp ω).mul (hlog.sub_const (Real.log (q ω)))
  apply hterm.congr_deriv
  field_simp [(hpos ω).ne']

/-- At a normalized base law, relative entropy has zero first derivative and
Fisher second derivative `∑ (p')²/q`. -/
theorem finiteRelativeEntropyPath_secondDerivative_eq_fisher
    {Ω : Type*} [Fintype Ω]
    (p p' : ℝ → Ω → ℝ) (p'' q : Ω → ℝ)
    (hp : ∀ ω t, HasDerivAt (fun u => p u ω) (p' t ω) t)
    (hp' : ∀ ω, HasDerivAt (fun t => p' t ω) (p'' ω) 0)
    (hbase : ∀ ω, p 0 ω = q ω)
    (hq : ∀ ω, 0 < q ω)
    (hnorm' : ∑ ω, p' 0 ω = 0)
    (hnorm'' : ∑ ω, p'' ω = 0) :
    HasDerivAt (finiteRelativeEntropyPath p q) 0 0
    ∧ HasDerivAt (finiteRelativeEntropyPathDerivative p p' q)
        (∑ ω, (p' 0 ω) ^ 2 / q ω) 0 := by
  constructor
  · convert hasDerivAt_finiteRelativeEntropyPath p p' q 0
      (fun ω => hp ω 0) (fun ω => hbase ω ▸ hq ω) using 1
    unfold finiteRelativeEntropyPathDerivative
    rw [show (∑ ω, p' 0 ω *
        (Real.log (p 0 ω) - Real.log (q ω) + 1)) =
        ∑ ω, p' 0 ω by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [hbase ω]
      ring]
    exact hnorm'.symm
  · have hsum := hasDerivAt_finite_sum
      (fun ω t => p' t ω *
        (Real.log (p t ω) - Real.log (q ω) + 1))
      (fun ω => p'' ω *
          (Real.log (p 0 ω) - Real.log (q ω) + 1) +
        p' 0 ω * (p' 0 ω / p 0 ω)) 0
      (fun ω => by
        have hlog := ((hp ω 0).log
          (by rw [hbase ω]; exact (hq ω).ne')).sub_const
            (Real.log (q ω))
        have hlog1 := hlog.add_const 1
        exact (hp' ω).mul hlog1)
    have hraw :
        (∑ ω, (p'' ω *
            (Real.log (p 0 ω) - Real.log (q ω) + 1) +
          p' 0 ω * (p' 0 ω / p 0 ω))) =
        ∑ ω, (p'' ω + (p' 0 ω) ^ 2 / q ω) := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [hbase ω]
      ring
    have hderiv :
        (∑ ω, (p'' ω *
            (Real.log (p 0 ω) - Real.log (q ω) + 1) +
          p' 0 ω * (p' 0 ω / p 0 ω))) =
        ∑ ω, ((p' 0 ω) ^ 2 / q ω) := by
      rw [hraw, Finset.sum_add_distrib, hnorm'', zero_add]
    exact hsum.congr_deriv hderiv

/-- If the probability derivative is synthesized by nuisance and retained
score maps, the relative-entropy second derivative is their joint Euclidean
Fisher norm. -/
theorem finiteRelativeEntropyPath_secondDerivative_eq_scoreNorm
    {Ω E E' : Type*} [Fintype Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (p p' : ℝ → Ω → ℝ) (p'' q : Ω → ℝ)
    (N : E →L[ℝ] EuclideanSpace ℝ Ω)
    (S : E' →L[ℝ] EuclideanSpace ℝ Ω) (x : E) (y : E')
    (hp : ∀ ω t, HasDerivAt (fun u => p u ω) (p' t ω) t)
    (hp' : ∀ ω, HasDerivAt (fun t => p' t ω) (p'' ω) 0)
    (hbase : ∀ ω, p 0 ω = q ω)
    (hq : ∀ ω, 0 < q ω)
    (hnorm' : ∑ ω, p' 0 ω = 0)
    (hnorm'' : ∑ ω, p'' ω = 0)
    (hscore : ∀ ω, p' 0 ω =
      Real.sqrt (q ω) * (N x + S y) ω) :
    HasDerivAt (finiteRelativeEntropyPath p q) 0 0
    ∧ HasDerivAt (finiteRelativeEntropyPathDerivative p p' q)
        (‖N x + S y‖ ^ 2) 0 := by
  have hkl := finiteRelativeEntropyPath_secondDerivative_eq_fisher
    p p' p'' q hp hp' hbase hq hnorm' hnorm''
  refine ⟨hkl.1, hkl.2.congr_deriv ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [hscore ω]
  have hs : Real.sqrt (q ω) ^ 2 = q ω := Real.sq_sqrt (hq ω).le
  field_simp [(hq ω).ne']
  nlinarith

/-! ## Exact profiling of the Fisher quadratic germ -/

namespace ProfiledFisher

variable {E E' F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

/-- The joint nuisance/retained Fisher quadratic Taylor term. -/
noncomputable def jointQuadratic
    (N : E →L[ℝ] F) (S : E' →L[ℝ] F) (x : E) (y : E') : ℝ :=
  (1 / 2 : ℝ) * ‖N x + S y‖ ^ 2

/-- The profiled Fisher quadratic, expressed by the orthogonal residual. -/
noncomputable def profiledQuadratic
    (N : E →L[ℝ] F) (S : E' →L[ℝ] F) (y : E') : ℝ :=
  (1 / 2 : ℝ) * ‖MoorePenrose.residual N S y‖ ^ 2

/-- The canonical efficient Fisher Hessian after nuisance profiling. -/
noncomputable def efficientHessian
    (N : E →L[ℝ] F) (S : E' →L[ℝ] F) : E' →L[ℝ] E' :=
  S† ∘L MoorePenrose.residual N S

/-- Profiling the relative-entropy Fisher quadratic germ gives the exact
Moore--Penrose Schur action, with an attained nuisance minimum and a positive
efficient Hessian. -/
theorem profiled_relativeEntropy_fisher_germ
    (N : E →L[ℝ] F) (S : E' →L[ℝ] F) :
    (∀ y x, profiledQuadratic N S y ≤ jointQuadratic N S x y)
    ∧ (∀ y, ∃ x, jointQuadratic N S x y = profiledQuadratic N S y)
    ∧ efficientHessian N S =
      S† ∘L S - (MoorePenrose.crossGram N S)† ∘L
        MoorePenrose.gramPinv N ∘L MoorePenrose.crossGram N S
    ∧ (∀ y, ⟪y, efficientHessian N S y⟫ =
        ‖MoorePenrose.residual N S y‖ ^ 2)
    ∧ (efficientHessian N S).IsPositive := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y x
    have hnorm := (MoorePenrose.innovation_variational N S y).1 x
    have hsq := pow_le_pow_left₀
      (norm_nonneg (MoorePenrose.residual N S y)) hnorm 2
    unfold profiledQuadratic jointQuadratic
    nlinarith
  · intro y
    obtain ⟨x, hx⟩ := (MoorePenrose.innovation_variational N S y).2
    refine ⟨x, ?_⟩
    unfold jointQuadratic profiledQuadratic
    rw [hx]
  · exact (MoorePenrose.schur_innovation N S).symm
  · intro y
    exact MoorePenrose.inner_innovation N S y
  · exact MoorePenrose.innovation_isPositive N S

end ProfiledFisher

end NCG
