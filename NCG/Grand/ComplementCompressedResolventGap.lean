/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ConvergentSpectralGapCoercivity
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Spectral gaps from complement-compressed resolvents

After the kernel projection has stabilized, the first positive eigenvalue of a nonnegative
operator is read from the norm of its resolvent compressed to the kernel complement.  This file
formalizes the continuity part of that argument: operator-norm convergence of the resolvents and
kernel projections gives convergence of the compressed norms, and inversion converts those norms
to the shifted gap parameters.
-/

open Filter Topology

noncomputable section

namespace NCG.SpectralGap

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- Compress an operator to the algebraic complement selected by `1 - P`. -/
def complementCompression (T P : E →L[K] E) : E →L[K] E :=
  (1 - P) * T * (1 - P)

/-- Norm convergence of operators and projections passes to complement compressions. -/
theorem complementCompression_tendsto
    {I : Type*} {l : Filter I}
    (T P : I → E →L[K] E) (Tlim Plim : E →L[K] E)
    (hT : Tendsto T l (nhds Tlim)) (hP : Tendsto P l (nhds Plim)) :
    Tendsto (fun i ↦ complementCompression (T i) (P i)) l
      (nhds (complementCompression Tlim Plim)) := by
  have hcomp : Tendsto (fun i ↦ (1 : E →L[K] E) - P i) l
      (nhds ((1 : E →L[K] E) - Plim)) :=
    tendsto_const_nhds.sub hP
  exact (hcomp.mul hT).mul hcomp

/-- The norms of complement-compressed operators converge. -/
theorem norm_complementCompression_tendsto
    {I : Type*} {l : Filter I}
    (T P : I → E →L[K] E) (Tlim Plim : E →L[K] E)
    (hT : Tendsto T l (nhds Tlim)) (hP : Tendsto P l (nhds Plim)) :
    Tendsto (fun i ↦ ‖complementCompression (T i) (P i)‖) l
      (nhds ‖complementCompression Tlim Plim‖) :=
  (complementCompression_tendsto T P Tlim Plim hT hP).norm

/-- If the limiting compressed resolvent norm is nonzero, the shifted inverse-norm gap
parameters converge. -/
theorem inverseNormGap_tendsto
    {I : Type*} {l : Filter I}
    (T P : I → E →L[K] E) (Tlim Plim : E →L[K] E) (lam : ℝ)
    (hT : Tendsto T l (nhds Tlim)) (hP : Tendsto P l (nhds Plim))
    (hne : ‖complementCompression Tlim Plim‖ ≠ 0) :
    Tendsto
      (fun i ↦ ‖complementCompression (T i) (P i)‖⁻¹ - lam) l
      (nhds (‖complementCompression Tlim Plim‖⁻¹ - lam)) := by
  exact ((norm_complementCompression_tendsto T P Tlim Plim hT hP).inv₀ hne).sub
    tendsto_const_nhds

/-- Positive limiting inverse-norm gap supplies the same explicit eventual half-gap and
no-soft-mode consequences as an independently specified convergent gap sequence. -/
theorem eventually_uniform_coercivity_of_compressedResolvent_tendsto
    (T P : ℕ → E →L[K] E) (Tlim Plim : E →L[K] E) (lam : ℝ)
    (hT : Tendsto T atTop (nhds Tlim)) (hP : Tendsto P atTop (nhds Plim))
    (hne : ‖complementCompression Tlim Plim‖ ≠ 0)
    (energy residual : ℕ → E → ℝ)
    (hresidual : ∀ n x, 0 ≤ residual n x)
    (hcoercive : ∀ n x,
      (‖complementCompression (T n) (P n)‖⁻¹ - lam) * residual n x ≤ energy n x)
    (hgapPos : 0 < ‖complementCompression Tlim Plim‖⁻¹ - lam) :
    0 < (‖complementCompression Tlim Plim‖⁻¹ - lam) / 2 ∧
      ∀ᶠ n in atTop, ∀ x,
        (‖complementCompression Tlim Plim‖⁻¹ - lam) / 2 * residual n x ≤ energy n x := by
  exact eventually_uniform_coercivity_of_gap_tendsto
    energy residual
      (fun n ↦ ‖complementCompression (T n) (P n)‖⁻¹ - lam)
      (‖complementCompression Tlim Plim‖⁻¹ - lam)
      hresidual hcoercive (inverseNormGap_tendsto T P Tlim Plim lam hT hP hne) hgapPos

end NCG.SpectralGap
