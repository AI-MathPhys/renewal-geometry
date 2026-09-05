/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineTraceEntropyDerivativeExact

/-!
# Exact affine relative-entropy second derivative

This file upgrades the BKM first-variation calculation to the literal
relative-entropy function.  It supplies an explicit derivative field on a
faithful affine interval and proves that the derivative of that field at the
base point is the BKM quadratic form.
-/

open Matrix Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ d : Matrix n n ℂ}

/-- Relative entropy of an affine Hermitian path from its base. -/
noncomputable def affineRelativeEntropy
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (u : ℝ) : ℝ :=
  relEntropy (affineMatrix_isHermitian hσ hd u) hσ

/-- The exact derivative field of affine relative entropy. -/
noncomputable def affineRelativeEntropyDerivative
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (u : ℝ) : ℝ :=
  d.trace.re + affineRelativeEntropyFirstVariation hσ hd u

/-- The literal affine relative entropy has the advertised derivative at
every faithful point of the interval. -/
theorem affineRelativeEntropy_hasDerivAt
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {A B t : ℝ}
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • d).PosDef)
    (ht : t ∈ Set.Ioo A B) :
    HasDerivAt (affineRelativeEntropy hσ hd)
      (affineRelativeEntropyDerivative hσ hd t) t := by
  have hent := affineTraceEntropy_hasDerivAt hσ hd hpos ht
  let c0 : ℝ := (Matrix.trace (σ * matLog hσ)).re
  let c1 : ℝ := (Matrix.trace (d * matLog hσ)).re
  have hlinearRaw : HasDerivAt (fun u : ℝ => c0 + u * c1) c1 t := by
    have h := (hasDerivAt_const t c0).add
      ((hasDerivAt_id t).mul_const c1)
    exact h.congr_deriv (by ring)
  have hlinearFun :
      (fun u : ℝ => c0 + u * c1) =
      (fun u : ℝ =>
        (Matrix.trace ((σ + u • d) * matLog hσ)).re) := by
    funext u
    unfold c0 c1
    simp only [Matrix.add_mul, Matrix.trace_add, Complex.add_re,
      Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul]
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hlinear : HasDerivAt
      (fun u : ℝ =>
        (Matrix.trace ((σ + u • d) * matLog hσ)).re)
      c1 t := by
    rw [← hlinearFun]
    exact hlinearRaw
  have hsub := hent.sub hlinear
  have hfun :
      (fun u : ℝ => affineTraceEntropy hσ hd u -
        (Matrix.trace ((σ + u • d) * matLog hσ)).re) =
      affineRelativeEntropy hσ hd := by
    funext u
    unfold affineTraceEntropy affineRelativeEntropy relEntropy
    simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [← hfun]
  unfold affineRelativeEntropyDerivative
  apply hsub.congr_deriv
  unfold affineRelativeEntropyFirstVariation c1
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  ring

/-- On a faithful interval, `affineRelativeEntropyDerivative` is genuinely a
derivative field for the literal relative entropy. -/
theorem affineRelativeEntropy_hasDerivativeField
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {A B : ℝ}
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • d).PosDef) :
    ∀ t ∈ Set.Ioo A B,
      HasDerivAt (affineRelativeEntropy hσ hd)
        (affineRelativeEntropyDerivative hσ hd t) t := by
  intro t ht
  exact affineRelativeEntropy_hasDerivAt hσ hd hpos ht

/-- The derivative field itself has derivative equal to the affine BKM form at
every faithful point. -/
theorem affineRelativeEntropyDerivative_hasDerivAt
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {A B t : ℝ}
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • d).PosDef)
    (ht : t ∈ Set.Ioo A B) :
    HasDerivAt (affineRelativeEntropyDerivative hσ hd)
      (affineBkmForm hσ hd t) t := by
  have hfirst := affineRelativeEntropyFirstVariation_hasDerivAt
    hσ hd hpos ht
  have hconst : HasDerivAt (fun _ : ℝ => d.trace.re) 0 t :=
    hasDerivAt_const t _
  unfold affineRelativeEntropyDerivative
  exact (hconst.add hfirst).congr_deriv (zero_add _)

/-- The derivative of the literal relative-entropy derivative field at the
base point is exactly the BKM quadratic form. -/
theorem affineRelativeEntropyDerivative_hasDerivAt_zero
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ u ∈ Set.Ioo (-ε) ε, (σ + u • d).PosDef) :
    HasDerivAt (affineRelativeEntropyDerivative hσ hd)
      (bkmForm hσ d) 0 := by
  have hfirst := affineRelativeEntropyFirstVariation_hasDerivAt_zero
    hσ hd hε hpos
  have hconst : HasDerivAt (fun _ : ℝ => d.trace.re) 0 0 :=
    hasDerivAt_const 0 _
  unfold affineRelativeEntropyDerivative
  exact (hconst.add hfirst).congr_deriv (zero_add _)

/-- Literal second-derivative package for affine relative entropy: the first
component identifies the derivative throughout the faithful interval and the
second identifies its base derivative with the BKM metric. -/
theorem affineRelativeEntropy_hasBkmSecondDerivativeAt_zero
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ u ∈ Set.Ioo (-ε) ε, (σ + u • d).PosDef) :
    (∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt (affineRelativeEntropy hσ hd)
        (affineRelativeEntropyDerivative hσ hd t) t) ∧
    HasDerivAt (affineRelativeEntropyDerivative hσ hd)
      (bkmForm hσ d) 0 :=
  ⟨affineRelativeEntropy_hasDerivativeField hσ hd hpos,
    affineRelativeEntropyDerivative_hasDerivAt_zero hσ hd hε hpos⟩

end QRE
end NCG
