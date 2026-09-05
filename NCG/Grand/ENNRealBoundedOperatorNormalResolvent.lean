/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealBoundedOperatorEnergy
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Normal equations for bounded-operator resolvents

For a bounded operator `A`, the strong normal equation
`(A† A)x + λx = f` implies the weak graph-resolvent equation.  Combining this observation with
the one-shift theorem leaves model applications with ordinary operator equations only.
-/

open scoped ENNReal InnerProduct

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F] [CompleteSpace F]

/-- The bounded normal equation implies the weak graph-resolvent equation on the full domain. -/
theorem boundedOperatorGraph_resolventEquation_of_normalEquation
    (A : E →L[K] F) (lam : ℝ) (f x : E)
    (h : (A† ∘L A) x + ((lam : ℝ) : K) • x = f) :
    OperatorGraphResolventEquation (⊤ : Submodule K E)
      (boundedOperatorGraphMap A) lam f x := by
  refine ⟨Submodule.mem_top, ?_⟩
  intro z
  change RCLike.re (inner K (A x) (A z.1)) +
      lam * RCLike.re (inner K x z.1) =
    RCLike.re (inner K z.1 f)
  rw [← h, inner_add_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    inner_smul_right]
  rw [map_add, RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im,
    zero_mul, sub_zero, inner_re_symm (𝕜 := K) (A z.1) (A x),
    inner_re_symm (𝕜 := K) z.1 x]

namespace System

universe z

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {F₀ : Type z} [NormedAddCommGroup F₀] [InnerProductSpace K F₀]
  [CompleteSpace F₀]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]
  [∀ n, CompleteSpace (Fn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- For bounded operators, normal resolvent equations at every positive shift and strong
resolvent convergence at one shift imply Mosco convergence of the squared energies. -/
theorem ennrealBoundedOperatorEnergy_moscoConverges_of_oneStrongResolvent_of_normalEquation
    (An : ∀ n, Hn n →L[K] Fn n) (A : H →L[K] F₀)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : J.StrongOperatorConverges J (Tn lam0) (T lam0))
    (hstageNormal : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      ((An n)† ∘L (An n)) (Tn lam n f) +
          ((lam : ℝ) : K) • Tn lam n f = f)
    (hlimitNormal : ∀ lam, 0 < lam → ∀ f : H,
      (A† ∘L A) (T lam f) + ((lam : ℝ) : K) • T lam f = f) :
    J.MoscoConverges
      (fun n ↦ ennrealBoundedOperatorEnergy (An n))
      (ennrealBoundedOperatorEnergy A) := by
  apply ennrealBoundedOperatorEnergy_moscoConverges_of_oneStrongResolvent J
    An A Tn T hdense lam0 hlam0 hT0
  · intro lam hlam n f
    exact boundedOperatorGraph_resolventEquation_of_normalEquation
      (An n) lam f (Tn lam n f) (hstageNormal lam hlam n f)
  · intro lam hlam f
    exact boundedOperatorGraph_resolventEquation_of_normalEquation
      A lam f (T lam f) (hlimitNormal lam hlam f)

end System
end NCG.VaryingHilbert
