/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineDataProcessingSecondDerivativeExact

/-!
# Algebraic continuity machinery for the BKM form

This file begins the arbitrary-path reduction for the BKM Hessian by replacing
the proof-indexed spectral inverse with the ordinary nonsingular matrix inverse
at positive-definite matrices.  The latter is a rational matrix function and
is continuous throughout the invertible locus.
-/

open Matrix Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {N : Type*} [Fintype N] [DecidableEq N]
variable {P : Matrix N N ℂ}

/-- At a positive-definite matrix, the spectral inverse used by the BKM
development is the ordinary nonsingular matrix inverse. -/
theorem invMat_eq_nonsing_inv (hP : P.PosDef) :
    invMat hP.1 = P⁻¹ := by
  have hdet : IsUnit P.det :=
    (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  exact Matrix.right_inv_eq_right_inv
    (mul_invMat hP) (Matrix.mul_nonsing_inv P hdet)

/-- The ordinary nonsingular matrix inverse is continuous throughout the
invertible locus. -/
theorem continuousAt_nonsing_inv_of_isUnit (hP : IsUnit P) :
    ContinuousAt (fun A : Matrix N N ℂ => A⁻¹) P := by
  have hdet : P.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det P).mp hP).ne_zero
  change ContinuousAt
    (fun A : Matrix N N ℂ => Ring.inverse A.det • A.adjugate) P
  simp only [Ring.inverse_eq_inv]
  fun_prop

/-- Positive definiteness is a convenient sufficient condition for inverse
continuity. -/
theorem continuousAt_nonsing_inv (hP : P.PosDef) :
    ContinuousAt (fun A : Matrix N N ℂ => A⁻¹) P :=
  continuousAt_nonsing_inv_of_isUnit hP.isUnit

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Proof-independent algebraic version of the affine BKM integrand. -/
noncomputable def algebraicTQuad
    (σ v : Matrix n n ℂ) (t : ℝ) : ℝ :=
  (star (vecM v) ⬝ᵥ ((affineOp σ t)⁻¹ *ᵥ vecM v)).re

set_option linter.unusedFintypeInType false in
set_option linter.unusedSectionVars false in
/-- The affine modular operator depends continuously on its matrix and scalar
arguments. -/
theorem continuous_affineOp_uncurry :
    Continuous (Function.uncurry
      (affineOp : Matrix n n ℂ → ℝ → Matrix (n × n) (n × n) ℂ)) := by
  apply continuous_matrix
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Function.uncurry, affineOp, Matrix.add_apply,
    Matrix.smul_apply, Matrix.kronecker_apply, Matrix.transpose_apply]
  fun_prop

/-- On the positive cone, the algebraic integrand is the spectral `tQuad`. -/
theorem algebraicTQuad_eq_tQuad {σ v : Matrix n n ℂ}
    (hσ : σ.PosDef) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    algebraicTQuad σ v t = tQuad hσ.1 v t := by
  unfold algebraicTQuad tQuad
  rw [invMat_eq_nonsing_inv (affineOp_posDef hσ ht0 ht1)]

/-- The proof-independent affine BKM integrand is jointly continuous wherever
the affine modular operator is invertible. -/
theorem continuousAt_algebraicTQuad_uncurry_of_isUnit
    {σ v : Matrix n n ℂ} {t : ℝ} (hunit : IsUnit (affineOp σ t)) :
    ContinuousAt
      (Function.uncurry (fun p : Matrix n n ℂ × Matrix n n ℂ =>
        algebraicTQuad p.1 p.2)) ((σ, v), t) := by
  have hAff : ContinuousAt
      (fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
        affineOp q.1.1 q.2) ((σ, v), t) := by
    apply continuousAt_pi'
    rintro ⟨i₁, i₂⟩
    apply continuousAt_pi'
    rintro ⟨j₁, j₂⟩
    simp only [affineOp, Matrix.add_apply, Matrix.smul_apply,
      Matrix.kronecker_apply, Matrix.transpose_apply]
    fun_prop
  have hInv : ContinuousAt
      (fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
        (affineOp q.1.1 q.2)⁻¹) ((σ, v), t) :=
    ContinuousAt.comp'
      (f := fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
        affineOp q.1.1 q.2)
      (continuousAt_nonsing_inv_of_isUnit hunit) hAff
  have hVec : ContinuousAt
      (fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => vecM q.1.2)
      ((σ, v), t) := by
    apply continuousAt_pi'
    rintro ⟨i, j⟩
    unfold vecM
    fun_prop
  have hMulVec : ContinuousAt
      (fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
        (affineOp q.1.1 q.2)⁻¹ *ᵥ vecM q.1.2) ((σ, v), t) := by
    apply continuousAt_pi'
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply tendsto_finsetSum
    intro j _
    have hInvRow : ContinuousAt
        (fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
          (affineOp q.1.1 q.2)⁻¹ i) ((σ, v), t) :=
      ContinuousAt.comp'
        (f := fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
          (affineOp q.1.1 q.2)⁻¹) (continuousAt_apply i _) hInv
    have hInvEntry : ContinuousAt
        (fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
          (affineOp q.1.1 q.2)⁻¹ i j) ((σ, v), t) :=
      ContinuousAt.comp'
        (f := fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
          (affineOp q.1.1 q.2)⁻¹ i) (continuousAt_apply j _) hInvRow
    have hVecEntry : ContinuousAt
        (fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => vecM q.1.2 j)
        ((σ, v), t) :=
      ContinuousAt.comp'
        (f := fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => vecM q.1.2)
        (continuousAt_apply j _) hVec
    exact hInvEntry.mul hVecEntry
  unfold Function.uncurry algebraicTQuad
  apply Complex.continuous_re.continuousAt.comp'
  simp only [dotProduct]
  apply tendsto_finsetSum
  intro i _
  have hStarEntry : ContinuousAt
      (fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
        star (vecM q.1.2) i) ((σ, v), t) := by
    simp only [Pi.star_apply]
    exact continuous_star.continuousAt.comp'
      (ContinuousAt.comp'
        (f := fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => vecM q.1.2)
        (continuousAt_apply i _) hVec)
  have hMulEntry : ContinuousAt
      (fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
        ((affineOp q.1.1 q.2)⁻¹ *ᵥ vecM q.1.2) i) ((σ, v), t) :=
    ContinuousAt.comp'
      (f := fun q : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
        (affineOp q.1.1 q.2)⁻¹ *ᵥ vecM q.1.2)
      (continuousAt_apply i _) hMulVec
  exact hStarEntry.mul hMulEntry

/-- Faithfulness guarantees the invertibility required for joint continuity
at every interpolation coordinate in `[0,1]`. -/
theorem continuousAt_algebraicTQuad_uncurry
    {σ v : Matrix n n ℂ} (hσ : σ.PosDef) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ContinuousAt
      (Function.uncurry (fun p : Matrix n n ℂ × Matrix n n ℂ =>
        algebraicTQuad p.1 p.2)) ((σ, v), t) :=
  continuousAt_algebraicTQuad_uncurry_of_isUnit
    (affineOp_posDef hσ ht0 ht1).isUnit

/-- Proof-independent algebraic representative of the BKM quadratic form. -/
noncomputable def algebraicBkmForm
    (σ v : Matrix n n ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, algebraicTQuad σ v t

/-- The algebraic integral agrees exactly with the spectral BKM form at every
faithful base matrix. -/
theorem algebraicBkmForm_eq_bkmForm {σ v : Matrix n n ℂ}
    (hσ : σ.PosDef) :
    algebraicBkmForm σ v = bkmForm hσ.1 v := by
  rw [bkmForm_eq_integral hσ]
  unfold algebraicBkmForm
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  rw [algebraicTQuad_eq_tQuad hσ ht.1 ht.2,
    tQuad_eq_sum hσ v ht.1 ht.2]

/-- The proof-independent algebraic BKM form is jointly continuous at every
faithful base and arbitrary tangent. -/
theorem continuousAt_algebraicBkmForm
    {σ v : Matrix n n ℂ} (hσ : σ.PosDef) :
    ContinuousAt
      (fun p : Matrix n n ℂ × Matrix n n ℂ =>
        algebraicBkmForm p.1 p.2) (σ, v) := by
  let x0 : Matrix n n ℂ × Matrix n n ℂ := (σ, v)
  let F : (Matrix n n ℂ × Matrix n n ℂ) → ℝ → ℝ :=
    fun p t => algebraicTQuad p.1 p.2 t
  let W : Set ((Matrix n n ℂ × Matrix n n ℂ) × ℝ) :=
    {p | IsUnit (affineOp p.1.1 p.2)}
  have hOp : Continuous
      (fun p : (Matrix n n ℂ × Matrix n n ℂ) × ℝ =>
        affineOp p.1.1 p.2) := by
    exact continuous_affineOp_uncurry.comp'
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hWopen : IsOpen W := by
    exact Units.isOpen.preimage hOp
  have hstrip : ({x0} ×ˢ Set.Icc (0 : ℝ) 1) ⊆ W := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    have hp' : p = x0 := Set.mem_singleton_iff.mp hp
    subst p
    exact (affineOp_posDef hσ ht.1 ht.2).isUnit
  obtain ⟨U, V, hUopen, hVopen, hxU, hIV, hUV⟩ :=
    generalized_tube_lemma (X := Matrix n n ℂ × Matrix n n ℂ)
      (Y := ℝ) isCompact_singleton isCompact_Icc hWopen hstrip
  have hx0U : x0 ∈ U := hxU (Set.mem_singleton x0)
  obtain ⟨K, hKcompact, hx0int, hKU⟩ :=
    exists_compact_subset hUopen hx0U
  have hKnhds : K ∈ 𝓝 x0 :=
    mem_of_superset (isOpen_interior.mem_nhds hx0int) interior_subset
  have hcont : ContinuousOn (Function.uncurry F)
      (K ×ˢ Set.Icc (0 : ℝ) 1) := by
    rintro ⟨p, t⟩ ⟨hpK, ht⟩
    have hunit : IsUnit (affineOp p.1 t) :=
      hUV ⟨hKU hpK, hIV ht⟩
    exact (continuousAt_algebraicTQuad_uncurry_of_isUnit
      (v := p.2) hunit).continuousWithinAt
  obtain ⟨C, hC⟩ :=
    (hKcompact.prod isCompact_Icc).bddAbove_image hcont.norm
  apply intervalIntegral.continuousAt_of_dominated_interval
      (F := F) (bound := fun _ => C)
  · filter_upwards [hKnhds] with p hpK
    have hpcont : ContinuousOn (F p) (Set.uIcc (0 : ℝ) 1) := by
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have hw : (p, t) ∈ W := hUV ⟨hKU hpK, hIV htIcc⟩
      have hunit : IsUnit (affineOp p.1 t) := by
        exact hw
      have hjoint := continuousAt_algebraicTQuad_uncurry_of_isUnit
        (v := p.2) hunit
      have hpair : ContinuousAt
          (fun s : ℝ => (p, s)) t := by fun_prop
      exact (hjoint.comp' hpair).continuousWithinAt
    exact (hpcont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · filter_upwards [hKnhds] with p hpK
    filter_upwards with t
    intro ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        Set.uIoc_subset_uIcc ht
    have hmem : ‖F p t‖ ∈
        (fun z => ‖Function.uncurry F z‖) ''
          (K ×ˢ Set.Icc (0 : ℝ) 1) :=
      ⟨(p, t), ⟨hpK, htIcc⟩, rfl⟩
    exact hC hmem
  · exact intervalIntegrable_const
  · filter_upwards with t
    intro ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        Set.uIoc_subset_uIcc ht
    have hjoint := continuousAt_algebraicTQuad_uncurry
      (v := v) hσ htIcc.1 htIcc.2
    have hpair : ContinuousAt
        (fun p : Matrix n n ℂ × Matrix n n ℂ => (p, t)) x0 := by
      fun_prop
    exact ContinuousAt.comp'
      (f := fun p : Matrix n n ℂ × Matrix n n ℂ => (p, t))
      hjoint hpair

end QRE
end NCG
