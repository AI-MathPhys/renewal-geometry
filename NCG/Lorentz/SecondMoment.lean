/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.PrimitiveWeight

/-!
# Second-moment covariance derives isometric comparison

Covers `prop:second-moment-isometry` from
`manuscripts/lorentzian_emergence/lorentzian_emergence.tex`: if
the invertible record transport `T` intertwines the positive-definite
spatial second moments of neighbouring local record laws,
`T Mₓ Tᵀ = M_y`, and preserves the determinant orientation
(`det T > 0`), then the comparison in the orthonormal frames selected
by the two moments,

`U := M_y^{-1/2} T Mₓ^{1/2}`,

is special orthogonal: `U Uᵀ = 1` and `det U = 1`.  Isometric
comparison is thus a consequence of covariance of renewal second
moments rather than an independent metric postulate.

The positive square roots are built from the bare Hermitian
functional calculus of `NCG/Upstream/PrimitiveWeight.lean`
specialised to `𝕜 = ℝ` (real symmetric matrices).
-/

namespace NCG

open Matrix Unitary

variable {d : ℕ}

/-- Over `ℝ`, conjugate-transpose is transpose. -/
theorem real_conjTranspose_eq_transpose
    (A : Matrix (Fin d) (Fin d) ℝ) : Aᴴ = Aᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

/-- The positive square root `M^{1/2}` of a positive-definite real
symmetric matrix, via the functional calculus. -/
noncomputable def posSqrt {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) : Matrix (Fin d) (Fin d) ℝ :=
  hM.1.cfc Real.sqrt

/-- The inverse positive square root `M^{-1/2}`. -/
noncomputable def posInvSqrt {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) : Matrix (Fin d) (Fin d) ℝ :=
  hM.1.cfc fun x => (Real.sqrt x)⁻¹

theorem posSqrt_transpose {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) : (posSqrt hM)ᵀ = posSqrt hM := by
  rw [← real_conjTranspose_eq_transpose]
  exact Upstream.PrimitiveWeight.cfc_isHermitian hM.1 _

theorem posInvSqrt_transpose {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) : (posInvSqrt hM)ᵀ = posInvSqrt hM := by
  rw [← real_conjTranspose_eq_transpose]
  exact Upstream.PrimitiveWeight.cfc_isHermitian hM.1 _

theorem posSqrt_mul_self {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) : posSqrt hM * posSqrt hM = M := by
  unfold posSqrt
  rw [Upstream.PrimitiveWeight.cfc_mul]
  have h1 : hM.1.cfc (fun x => Real.sqrt x * Real.sqrt x)
      = hM.1.cfc id :=
    Upstream.PrimitiveWeight.cfc_congr hM.1 fun i =>
      Real.mul_self_sqrt (hM.posSemidef.eigenvalues_nonneg i)
  rw [h1, Upstream.PrimitiveWeight.cfc_id']

/-- `M^{-1/2} M M^{-1/2} = 1` for positive-definite `M`. -/
theorem posInvSqrt_conj {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) : posInvSqrt hM * M * posInvSqrt hM = 1 := by
  unfold posInvSqrt
  rw [Upstream.PrimitiveWeight.cfc_mul_self, Upstream.PrimitiveWeight.cfc_mul]
  have h1 : hM.1.cfc
      (fun x => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹)
      = hM.1.cfc fun _ => (1 : ℝ) := by
    refine Upstream.PrimitiveWeight.cfc_congr hM.1 fun i => ?_
    have hμ := hM.eigenvalues_pos i
    have hs : 0 < Real.sqrt (hM.1.eigenvalues i) :=
      Real.sqrt_pos.mpr hμ
    have hss := Real.mul_self_sqrt hμ.le
    field_simp
    linarith [hss]
  rw [h1, Upstream.PrimitiveWeight.cfc_const]
  simp

/-- Determinant of a functional-calculus element: the product of the
transformed eigenvalues. -/
theorem cfc_det {X : Matrix (Fin d) (Fin d) ℝ} (hX : X.IsHermitian)
    (f : ℝ → ℝ) :
    (hX.cfc f).det = ∏ i, f (hX.eigenvalues i) := by
  simp only [Matrix.IsHermitian.cfc, conjStarAlgAut_apply]
  rw [Matrix.det_mul, Matrix.det_mul]
  have hu : star (hX.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
      * (hX.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2
  have hdet1 :
      (hX.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).det
      * (star (hX.eigenvectorUnitary
          : Matrix (Fin d) (Fin d) ℝ)).det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, hu, Matrix.det_one]
  calc (hX.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).det
        * (diagonal (RCLike.ofReal ∘ f ∘ hX.eigenvalues)).det
        * (star (hX.eigenvectorUnitary
            : Matrix (Fin d) (Fin d) ℝ)).det
      = (diagonal (RCLike.ofReal ∘ f ∘ hX.eigenvalues)).det
        * ((hX.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).det
          * (star (hX.eigenvectorUnitary
              : Matrix (Fin d) (Fin d) ℝ)).det) := by ring
    _ = (diagonal (RCLike.ofReal ∘ f ∘ hX.eigenvalues)).det := by
        rw [hdet1, mul_one]
    _ = ∏ i, f (hX.eigenvalues i) := by
        rw [Matrix.det_diagonal]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp [Function.comp]

theorem posSqrt_det_pos {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) : 0 < (posSqrt hM).det := by
  unfold posSqrt
  rw [cfc_det]
  exact Finset.prod_pos fun i _ =>
    Real.sqrt_pos.mpr (hM.eigenvalues_pos i)

theorem posInvSqrt_det_pos {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) : 0 < (posInvSqrt hM).det := by
  unfold posInvSqrt
  rw [cfc_det]
  exact Finset.prod_pos fun i _ =>
    inv_pos.mpr (Real.sqrt_pos.mpr (hM.eigenvalues_pos i))

/-- **Proposition `prop:metric-comparison` (unconditional half)**:
covariance `T Mₓ Tᵀ = M_y` of positive second moments alone makes the
moment-normalised comparison `O_e = M_y^{-1/2} T Mₓ^{1/2}` orthogonal —
no orientation hypothesis needed for `O(d)` membership; preservation of
determinant orientation upgrades this to `SO(d)`
(`second_moment_isometry`). -/
theorem second_moment_orthogonal {Mx My T : Matrix (Fin d) (Fin d) ℝ}
    (hMx : Mx.PosDef) (hMy : My.PosDef)
    (hcov : T * Mx * Tᵀ = My) :
    (posInvSqrt hMy * T * posSqrt hMx)
      * (posInvSqrt hMy * T * posSqrt hMx)ᵀ = 1 := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    posSqrt_transpose, posInvSqrt_transpose]
  calc posInvSqrt hMy * T * posSqrt hMx
        * (posSqrt hMx * (Tᵀ * posInvSqrt hMy))
      = posInvSqrt hMy * (T * (posSqrt hMx * posSqrt hMx) * Tᵀ)
          * posInvSqrt hMy := by
        noncomm_ring
    _ = posInvSqrt hMy * My * posInvSqrt hMy := by
        rw [posSqrt_mul_self, hcov]
    _ = 1 := posInvSqrt_conj hMy

/-- **Proposition `prop:second-moment-isometry`**: covariance of the
transported second moments, `T Mₓ Tᵀ = M_y` with `Mₓ, M_y ≻ 0`,
together with preservation of the determinant orientation
(`det T > 0`), makes the moment-normalised comparison
`U = M_y^{-1/2} T Mₓ^{1/2}` special orthogonal: `U Uᵀ = 1` and
`det U = 1`. -/
theorem second_moment_isometry {Mx My T : Matrix (Fin d) (Fin d) ℝ}
    (hMx : Mx.PosDef) (hMy : My.PosDef)
    (hcov : T * Mx * Tᵀ = My) (hor : 0 < T.det) :
    (posInvSqrt hMy * T * posSqrt hMx)
      * (posInvSqrt hMy * T * posSqrt hMx)ᵀ = 1
    ∧ (posInvSqrt hMy * T * posSqrt hMx).det = 1 := by
  have horth : (posInvSqrt hMy * T * posSqrt hMx)
      * (posInvSqrt hMy * T * posSqrt hMx)ᵀ = 1 := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      posSqrt_transpose, posInvSqrt_transpose]
    calc posInvSqrt hMy * T * posSqrt hMx
          * (posSqrt hMx * (Tᵀ * posInvSqrt hMy))
        = posInvSqrt hMy * (T * (posSqrt hMx * posSqrt hMx) * Tᵀ)
            * posInvSqrt hMy := by
          noncomm_ring
      _ = posInvSqrt hMy * My * posInvSqrt hMy := by
          rw [posSqrt_mul_self, hcov]
      _ = 1 := posInvSqrt_conj hMy
  refine ⟨horth, ?_⟩
  have hdetU : 0 < (posInvSqrt hMy * T * posSqrt hMx).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_pos (mul_pos (posInvSqrt_det_pos hMy) hor)
      (posSqrt_det_pos hMx)
  have hsq : (posInvSqrt hMy * T * posSqrt hMx).det
      * (posInvSqrt hMy * T * posSqrt hMx).det = 1 := by
    have h1 := congrArg Matrix.det horth
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    exact h1
  have h2 : ((posInvSqrt hMy * T * posSqrt hMx).det - 1)
      * ((posInvSqrt hMy * T * posSqrt hMx).det + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · linarith

end NCG
