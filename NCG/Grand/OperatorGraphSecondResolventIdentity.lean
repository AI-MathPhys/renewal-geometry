/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventKernel

/-!
# The second resolvent identity from weak graph equations

Positive-shift weak graph resolvents satisfy the source-transform and second resolvent
identities directly.  No convexity, closedness, or variational realification is needed: the
weak Euler equation transports between shifts, and uniqueness at the target shift finishes the
argument.
-/

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- Changing the shift and compensating the source leaves a weak graph-resolvent solution
unchanged. -/
theorem operatorGraphResolvent_sourceTransform
    (D : Submodule K E) (A : D →ₗ[K] F)
    (R : ℝ → E →L[K] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (f : E) :
    R a (f + (((a - b : ℝ) : K)) • R b f) = R b f := by
  have hbEquation := hequation b hb f
  have hshifted : OperatorGraphResolventEquation D A a
      (f + (((a - b : ℝ) : K)) • R b f) (R b f) := {
    mem := hbEquation.mem
    weakEuler z := by
      have h := hbEquation.weakEuler z
      rw [inner_add_right, inner_smul_right, map_add, RCLike.mul_re]
      simp only [RCLike.ofReal_re, RCLike.ofReal_im, zero_mul, sub_zero]
      rw [inner_re_symm (𝕜 := K) z.1 (R b f)]
      nlinarith
  }
  exact (hequation a ha _).eq_of_pos D A a ha _ _ _ hshifted

/-- Weak graph resolvents at positive shifts satisfy the second resolvent identity. -/
theorem operatorGraph_secondResolventIdentity
    (D : Submodule K E) (A : D →ₗ[K] F)
    (R : ℝ → E →L[K] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    R a - R b = (((b - a : ℝ) : K)) • ((R a).comp (R b)) := by
  apply ContinuousLinearMap.ext
  intro f
  have hsource := operatorGraphResolvent_sourceTransform
    D A R hequation a b ha hb f
  simp only [map_add, map_smul] at hsource
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply]
  calc
    R a f - R b f = -((((a - b : ℝ) : K)) • R a (R b f)) := by
      calc
        R a f - R b f = R a f -
            (R a f + (((a - b : ℝ) : K)) • R a (R b f)) :=
          congrArg (fun w ↦ R a f - w) hsource.symm
        _ = -((((a - b : ℝ) : K)) • R a (R b f)) := by abel
    _ = (((b - a : ℝ) : K)) • R a (R b f) := by
      rw [← neg_smul]
      congr 1
      push_cast
      ring

end NCG.VaryingHilbert
