/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventBound
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Symmetry and dense range of weak graph resolvents

For a complex operator-graph energy, its weak positive-shift equation already contains the
standard Hilbert-space structure of the resolvent.  Testing the real weak equation at an
imaginary multiple recovers the missing imaginary part, hence symmetry.  If the graph domain is
dense, the resolvent is injective; symmetry then makes its range dense as well.

This supplies a canonical dense source family for Euler-resolvent and semigroup arguments without
adding a separate dense-range assumption.
-/

open Set

noncomputable section

namespace NCG.VaryingHilbert

universe v w

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A bounded operator satisfying the weak graph-resolvent equation is symmetric.  Although the
equation is stated using real parts, its value on `i • R f` shows that `⟨R f, f⟩` is real;
complex polarization then gives symmetry. -/
theorem operatorGraphResolvent_isSymmetric
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (lam : ℝ) (R : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    (R : E →ₗ[ℂ] E).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_inner_map_self_real]
  intro f
  apply Complex.conj_eq_iff_im.mpr
  let xD : D := ⟨R f, (hequation f).mem⟩
  have hI := (hequation f).weakEuler (Complex.I • xD)
  have hA : A (Complex.I • xD) = Complex.I • A xD := map_smul A _ _
  have hx : ((Complex.I • xD : D) : E) = Complex.I • (xD : E) := rfl
  rw [hA, hx] at hI
  rw [inner_smul_right, inner_smul_right, inner_smul_left] at hI
  change (Complex.I * inner ℂ (A xD) (A xD)).re +
      lam * (Complex.I * inner ℂ (xD : E) (xD : E)).re =
    ((starRingEnd ℂ) Complex.I * inner ℂ (xD : E) f).re at hI
  have hiA : RCLike.im (inner ℂ (A xD) (A xD)) = 0 :=
    inner_self_im (𝕜 := ℂ) (A xD)
  have hix : RCLike.im (inner ℂ (xD : E) (xD : E)) = 0 :=
    inner_self_im (𝕜 := ℂ) (xD : E)
  change (inner ℂ (A xD) (A xD)).im = 0 at hiA
  change (inner ℂ (xD : E) (xD : E)).im = 0 at hix
  rw [Complex.I_mul_re, hiA, neg_zero, Complex.I_mul_re, hix, neg_zero,
    mul_zero, zero_add, Complex.conj_I] at hI
  norm_num [Complex.mul_re] at hI
  simpa [xD] using hI.symm

/-- On a dense graph domain, a vector annihilated by a weak graph resolvent must vanish. -/
theorem eq_zero_of_operatorGraphResolvent_eq_zero
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (lam : ℝ) (R : E →L[ℂ] E)
    (hD : Dense (D : Set E))
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f))
    {f : E} (hf : R f = 0) :
    f = 0 := by
  apply hD.eq_zero_of_inner_right (𝕜 := ℂ)
  intro z hz
  let zD : D := ⟨z, hz⟩
  let xD : D := ⟨R f, (hequation f).mem⟩
  have hxD : xD = 0 := by
    apply Subtype.ext
    simpa [xD] using hf
  have hre := (hequation f).weakEuler zD
  have him := (hequation f).weakEuler (Complex.I • zD)
  change RCLike.re (inner ℂ (A xD) (A zD)) +
      lam * RCLike.re (inner ℂ (xD : E) (zD : E)) =
    RCLike.re (inner ℂ (zD : E) f) at hre
  rw [hxD] at hre
  simp only [map_zero, Submodule.coe_zero, inner_zero_left, zero_add] at hre
  have hAz : A (Complex.I • zD) = Complex.I • A zD := map_smul A _ _
  have hcoez : ((Complex.I • zD : D) : E) = Complex.I • (zD : E) := rfl
  change RCLike.re (inner ℂ (A xD) (A (Complex.I • zD))) +
      lam * RCLike.re (inner ℂ (xD : E) ((Complex.I • zD : D) : E)) =
    RCLike.re (inner ℂ (((Complex.I • zD : D) : E)) f) at him
  rw [hxD, hAz, hcoez] at him
  simp only [map_zero, Submodule.coe_zero, inner_zero_left, zero_add,
    inner_smul_left, Complex.conj_I] at him
  apply Complex.ext
  · simpa [zD] using hre.symm
  · change (inner ℂ z f).im = 0
    norm_num [Complex.mul_re] at him
    simpa [zD] using him.symm

/-- Weak graph resolvents on dense complex domains are injective. -/
theorem operatorGraphResolvent_injective
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (lam : ℝ) (R : E →L[ℂ] E)
    (hD : Dense (D : Set E))
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    Function.Injective R := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply eq_zero_of_operatorGraphResolvent_eq_zero D A lam R hD hequation
  rw [map_sub]
  exact sub_eq_zero.mpr hfg

/-- Weak graph resolvents on dense complex Hilbert-space domains have dense range. -/
theorem operatorGraphResolvent_denseRange
    [CompleteSpace E]
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (lam : ℝ) (R : E →L[ℂ] E)
    (hD : Dense (D : Set E))
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    DenseRange R := by
  have hsymm : (R : E →ₗ[ℂ] E).IsSymmetric :=
    operatorGraphResolvent_isSymmetric D A lam R hequation
  have hinj : Function.Injective R :=
    operatorGraphResolvent_injective D A lam R hD hequation
  have hker : LinearMap.ker (R : E →ₗ[ℂ] E) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hortho : (LinearMap.range (R : E →ₗ[ℂ] E))ᗮ = ⊥ := by
    rw [hsymm.orthogonal_range, hker]
  have hclosure : (LinearMap.range (R : E →ₗ[ℂ] E)).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,
      hortho, Submodule.bot_orthogonal_eq_top]
  change Dense ((LinearMap.range (R : E →ₗ[ℂ] E)) : Set E)
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hclosure

end NCG.VaryingHilbert
