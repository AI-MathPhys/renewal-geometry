/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.KuboBkmDualityExact
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Derivative of a faithful matrix resolvent along an affine path

This is the noncommutative differential-calculus input for the remaining
Daleckii--Krein layer of `cor:accepted-BKM-loss`.  It identifies the spectral
resolvent already used by the BKM form with the Banach-algebra inverse, then
applies Mathlib's Fréchet derivative of inversion.
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ v : Matrix n n ℂ}

/-- A positive shift of a faithful matrix is a unit. -/
theorem isUnit_shift_of_posDef (hσ : σ.PosDef) {s : ℝ} (hs : 0 < s) :
    IsUnit (σ + s • (1 : Matrix n n ℂ)) := by
  exact (posDef_add_smul_one hσ.posSemidef hs).isUnit

/-- A nonnegative shift of an already faithful matrix is still a unit. -/
theorem isUnit_shift_of_posDef_nonneg (hσ : σ.PosDef) {s : ℝ}
    (hs : 0 ≤ s) : IsUnit (σ + s • (1 : Matrix n n ℂ)) := by
  exact (hσ.add_posSemidef
    (posSemidef_smul_real hs Matrix.PosSemidef.one)).isUnit

/-- The spectral resolvent is a right inverse also at the zero endpoint for
a faithful base matrix. -/
theorem shift_mul_resolvent_nonneg (hσ : σ.PosDef) {s : ℝ}
    (hs : 0 ≤ s) :
    (σ + s • (1 : Matrix n n ℂ)) * resolvent hσ.1 s = 1 := by
  rw [shift_eq_matFun hσ.1 s]
  unfold resolvent
  rw [matFun_mul]
  have h1 : matFun hσ.1 (fun x => (x + s) * (x + s)⁻¹) =
      matFun hσ.1 (fun _ => 1) := by
    refine Petz.matFun_congr hσ.1 _ _ fun i => ?_
    have hpos : 0 < hσ.1.eigenvalues i + s :=
      add_pos_of_pos_of_nonneg (hσ.eigenvalues_pos i) hs
    exact mul_inv_cancel₀ hpos.ne'
  rw [h1, Petz.matFun_one]

/-- The Banach-algebra ring inverse agrees with the spectral resolvent for
every nonnegative shift of a faithful matrix. -/
theorem ringInverse_shift_eq_resolvent_nonneg (hσ : σ.PosDef) {s : ℝ}
    (hs : 0 ≤ s) :
    Ring.inverse (σ + s • (1 : Matrix n n ℂ)) = resolvent hσ.1 s := by
  let A : Matrix n n ℂ := σ + s • (1 : Matrix n n ℂ)
  have hA : IsUnit A := isUnit_shift_of_posDef_nonneg hσ hs
  have hAR : A * resolvent hσ.1 s = 1 :=
    shift_mul_resolvent_nonneg hσ hs
  calc
    Ring.inverse A = Ring.inverse A * (A * resolvent hσ.1 s) := by
      rw [hAR, Matrix.mul_one]
    _ = (Ring.inverse A * A) * resolvent hσ.1 s := by
      rw [Matrix.mul_assoc]
    _ = resolvent hσ.1 s := by
      rw [Ring.inverse_mul_cancel A hA, Matrix.one_mul]

/-- The Banach-algebra ring inverse of a faithful positive shift is exactly
the repository's spectral resolvent. -/
theorem ringInverse_shift_eq_resolvent (hσ : σ.PosDef) {s : ℝ}
    (hs : 0 < s) :
    Ring.inverse (σ + s • (1 : Matrix n n ℂ)) = resolvent hσ.1 s := by
  let A : Matrix n n ℂ := σ + s • (1 : Matrix n n ℂ)
  have hA : IsUnit A := isUnit_shift_of_posDef hσ hs
  have hAR : A * resolvent hσ.1 s = 1 := by
    exact shift_mul_resolvent hσ hs
  calc
    Ring.inverse A = Ring.inverse A * (A * resolvent hσ.1 s) := by
      rw [hAR, Matrix.mul_one]
    _ = (Ring.inverse A * A) * resolvent hσ.1 s := by
      rw [Matrix.mul_assoc]
    _ = resolvent hσ.1 s := by
      rw [Ring.inverse_mul_cancel A hA, Matrix.one_mul]

/-- **Resolvent derivative.**  Along `σ+t v`,
`d/dt (σ+t v+sI)⁻¹|₀ = -R_s v R_s`. -/
theorem resolvent_affine_hasDerivAt (hσ : σ.PosDef) (v : Matrix n n ℂ)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt
      (fun t : ℝ => Ring.inverse
        (σ + t • v + s • (1 : Matrix n n ℂ)))
      (-(resolvent hσ.1 s * v * resolvent hσ.1 s)) 0 := by
  let A : Matrix n n ℂ := σ + s • (1 : Matrix n n ℂ)
  have hA : IsUnit A := isUnit_shift_of_posDef hσ hs
  let u : (Matrix n n ℂ)ˣ := hA.unit
  have hu : (u : Matrix n n ℂ) = A := hA.unit_spec
  have hpath : HasDerivAt (fun t : ℝ => (u : Matrix n n ℂ) + t • v) v 0 := by
    have hlin : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    exact hlin.const_add (u : Matrix n n ℂ)
  have hinvBase : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)
        (↑u⁻¹ : Matrix n n ℂ) (↑u⁻¹ : Matrix n n ℂ))
      ((u : Matrix n n ℂ) + (0 : ℝ) • v) := by
    simpa using (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
  have hinv := hinvBase.comp_hasDerivAt 0 hpath
  have hfun : (fun t : ℝ => Ring.inverse
      (σ + t • v + s • (1 : Matrix n n ℂ))) =
      fun t : ℝ => Ring.inverse ((u : Matrix n n ℂ) + t • v) := by
    funext t
    congr 1
    rw [hu]
    dsimp [A]
    module
  rw [hfun]
  refine hinv.congr_deriv ?_
  have huinv : (↑u⁻¹ : Matrix n n ℂ) = resolvent hσ.1 s := by
    rw [← Ring.inverse_unit u, hu]
    exact ringInverse_shift_eq_resolvent hσ hs
  rw [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    huinv]

/-- The real trace pairing `X ↦ Re Tr(vX)` as a continuous real-linear map. -/
noncomputable def realTraceLeft (v : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (Matrix.trace (v * X)).re
      map_add' := fun X Y => by
        rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := fun r X => by
        rw [RingHom.id_apply, Matrix.mul_smul, Matrix.trace_smul]
        simp [Complex.real_smul] }

omit [DecidableEq n] in
@[simp]
theorem realTraceLeft_apply (v X : Matrix n n ℂ) :
    realTraceLeft v X = (Matrix.trace (v * X)).re := rfl

/-- Pairing the affine resolvent derivative with the tangent gives exactly the
negative BKM resolvent s-form. -/
theorem trace_resolvent_affine_hasDerivAt (hσ : σ.PosDef)
    (v : Matrix n n ℂ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt
      (fun t : ℝ => (Matrix.trace (v * Ring.inverse
        (σ + t • v + s • (1 : Matrix n n ℂ)))).re)
      (-sForm hσ.1 v s) 0 := by
  have hres := resolvent_affine_hasDerivAt hσ v hs
  have hcomp : HasDerivAt
      (fun t : ℝ => realTraceLeft v (Ring.inverse
        (σ + t • v + s • (1 : Matrix n n ℂ))))
      (realTraceLeft v
        (-(resolvent hσ.1 s * v * resolvent hσ.1 s))) 0 :=
    (realTraceLeft v).hasFDerivAt.comp_hasDerivAt 0 hres
  have hval : realTraceLeft v
      (-(resolvent hσ.1 s * v * resolvent hσ.1 s)) =
      -sForm hσ.1 v s := by
    unfold sForm
    simp only [realTraceLeft_apply, map_neg, Matrix.mul_assoc]
  simpa only [realTraceLeft_apply] using hcomp.congr_deriv hval

/-- The resolvent derivative at an arbitrary parameter value, assuming the
affine path is faithful there. -/
theorem resolvent_affine_hasDerivAt_at {t : ℝ}
    (ht : (σ + t • v).PosDef) {s : ℝ} (hs : 0 < s) :
    HasDerivAt
      (fun u : ℝ => Ring.inverse
        (σ + u • v + s • (1 : Matrix n n ℂ)))
      (-(resolvent ht.1 s * v * resolvent ht.1 s)) t := by
  have hbase := resolvent_affine_hasDerivAt ht v hs
  have hshift : HasDerivAt (fun u : ℝ => u - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have hcomp := hbase.scomp_of_eq t hshift (by ring)
  have hfun :
      (fun u : ℝ => Ring.inverse
        (σ + u • v + s • (1 : Matrix n n ℂ))) =
      fun u : ℝ => Ring.inverse
        ((σ + t • v) + (u - t) • v +
          s • (1 : Matrix n n ℂ)) := by
    funext u
    congr 1
    module
  rw [hfun]
  simpa [Function.comp_def] using hcomp

/-- The trace-paired resolvent derivative at an arbitrary faithful point of
the affine path. -/
theorem trace_resolvent_affine_hasDerivAt_at {t : ℝ}
    (ht : (σ + t • v).PosDef) {s : ℝ} (hs : 0 < s) :
    HasDerivAt
      (fun u : ℝ => (Matrix.trace (v * Ring.inverse
        (σ + u • v + s • (1 : Matrix n n ℂ)))).re)
      (-sForm ht.1 v s) t := by
  have hres := resolvent_affine_hasDerivAt_at ht hs
  have hcomp : HasDerivAt
      (fun u : ℝ => realTraceLeft v (Ring.inverse
        (σ + u • v + s • (1 : Matrix n n ℂ))))
      (realTraceLeft v
        (-(resolvent ht.1 s * v * resolvent ht.1 s))) t :=
    (realTraceLeft v).hasFDerivAt.comp_hasDerivAt t hres
  have hval : realTraceLeft v
      (-(resolvent ht.1 s * v * resolvent ht.1 s)) =
      -sForm ht.1 v s := by
    unfold sForm
    simp only [realTraceLeft_apply, map_neg, Matrix.mul_assoc]
  simpa only [realTraceLeft_apply] using hcomp.congr_deriv hval

end QRE
end NCG
