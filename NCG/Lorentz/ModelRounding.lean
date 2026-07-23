/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Isotropic Clifford rounding (finite cores)

**Theorem `thm:model-rounding`**: as the reset directions
equidistribute, the second-moment matrix converges to the isotropic
`(1/d)·I` and, with the engineering normalisation `κ = d`, the squared
symbol rounds to the identity — the standard Minkowski inverse metric
of signature `(1, d)`.  The finite cores proved here:

* `NCG.isotropic_trace_normalisation` — a rotation-invariant second
  moment `λ·I` with unit trace forces `λ = 1/d`;
* `NCG.rounding_kappa_sq` — with `κ = d`,
  `κ²·((1/d)·I)² = I` exactly.

The weak-* convergence of the direction measures and the Hausdorff
convergence of the null/order cones are the noted analytic steps.
-/

namespace NCG

/-- **Theorem `thm:model-rounding` (i), trace core**: an isotropic
second-moment matrix `λ·I` with unit trace has `λ = 1/d`. -/
theorem isotropic_trace_normalisation (d : ℕ) (hd : 0 < d) (l : ℝ)
    (h : Matrix.trace (l • (1 : Matrix (Fin d) (Fin d) ℝ)) = 1) :
    l = 1 / d := by
  rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
    Fintype.card_fin] at h
  have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  field_simp
  linarith

/-- **Theorem `thm:model-rounding` (i), rounding core**: with the
engineering normalisation `κ = d` the squared symbol of the isotropic
second moment is exactly the identity: `d²·((1/d)·I)² = I`. -/
theorem rounding_kappa_sq (d : ℕ) (hd : 0 < d) :
    ((d:ℝ) ^ 2) • (((1:ℝ) / d) • (1 : Matrix (Fin d) (Fin d) ℝ)) ^ 2
      = 1 := by
  have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [smul_pow, one_pow, smul_smul,
    show (d:ℝ) ^ 2 * ((1:ℝ) / d) ^ 2 = 1 from by field_simp,
    one_smul]

/-- **Theorem `thm:general-rounding` (spatial-block core)**: the
square of a positive-definite second moment is positive definite, so
the spatial block `−κ²M(ν)²` of the limiting inverse metric is
negative definite and the signature is `(1, d)` whatever the
direction measure. -/
theorem posDef_mul_self {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) : (M * M).PosDef := by
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (Matrix.isUnit_iff_isUnit_det M |>.mpr
        (isUnit_iff_ne_zero.mpr hM.det_pos.ne'))
  have h := Matrix.PosDef.conjTranspose_mul_self M hinj
  rwa [hM.isHermitian.eq] at h

end NCG
