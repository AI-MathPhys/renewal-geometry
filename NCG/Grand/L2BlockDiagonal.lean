import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Uniformly bounded block-diagonal operators on `ℓ²`

A uniformly bounded family of fibre operators acts coordinatewise on an
infinite `ℓ²` direct sum.  This file bundles that action as a continuous
linear map and proves the sharp uniform operator-norm bound.  It is the
functional-analytic carrier for matrix-valued Fourier multipliers.
-/

noncomputable section

open scoped lp

namespace NCG

variable {ι E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Coordinatewise action of a uniformly bounded family of fibre operators
on the underlying `ℓ²` vector space. -/
def l2BlockDiagonalLinearMap
    (M : ι → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i x, ‖M i x‖ ≤ C * ‖x‖) :
    ℓ²(ι, E) →ₗ[ℂ] ℓ²(ι, E) where
  toFun f :=
    ⟨fun i ↦ M i (f i), by
      have hg : Memℓp ((C : ℂ) • (f : ι → E)) 2 :=
        (lp.memℓp f).const_smul (C : ℂ)
      apply hg.mono'
      intro i
      simpa only [Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hC] using hM i (f i)⟩
  map_add' f g := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c f := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

@[simp]
theorem l2BlockDiagonalLinearMap_apply
    (M : ι → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i x, ‖M i x‖ ≤ C * ‖x‖)
    (f : ℓ²(ι, E)) (i : ι) :
    l2BlockDiagonalLinearMap M C hC hM f i = M i (f i) := rfl

theorem l2BlockDiagonalLinearMap_norm_apply_le
    (M : ι → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i x, ‖M i x‖ ≤ C * ‖x‖)
    (f : ℓ²(ι, E)) :
    ‖l2BlockDiagonalLinearMap M C hC hM f‖ ≤ C * ‖f‖ := by
  have hmono := lp.norm_mono (show (2 : ENNReal) ≠ 0 by norm_num)
    (x := l2BlockDiagonalLinearMap M C hC hM f)
    (y := (C : ℂ) • f) (fun i ↦ by
      simpa only [l2BlockDiagonalLinearMap_apply, lp.coeFn_smul, Pi.smul_apply,
        norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
        using hM i (f i))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hC] using hmono

/-- The uniformly bounded block-diagonal action as a continuous linear map. -/
def l2BlockDiagonal
    (M : ι → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i x, ‖M i x‖ ≤ C * ‖x‖) :
    ℓ²(ι, E) →L[ℂ] ℓ²(ι, E) :=
  (l2BlockDiagonalLinearMap M C hC hM).mkContinuous C hM'
where
  hM' := fun f ↦ l2BlockDiagonalLinearMap_norm_apply_le M C hC hM f

@[simp]
theorem l2BlockDiagonal_apply
    (M : ι → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i x, ‖M i x‖ ≤ C * ‖x‖)
    (f : ℓ²(ι, E)) (i : ι) :
    l2BlockDiagonal M C hC hM f i = M i (f i) := rfl

theorem l2BlockDiagonal_norm_apply_le
    (M : ι → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i x, ‖M i x‖ ≤ C * ‖x‖)
    (f : ℓ²(ι, E)) :
    ‖l2BlockDiagonal M C hC hM f‖ ≤ C * ‖f‖ :=
  l2BlockDiagonalLinearMap_norm_apply_le M C hC hM f

theorem l2BlockDiagonal_opNorm_le
    (M : ι → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i x, ‖M i x‖ ≤ C * ‖x‖) :
    ‖l2BlockDiagonal M C hC hM‖ ≤ C := by
  exact ContinuousLinearMap.opNorm_le_bound _ hC
    (l2BlockDiagonal_norm_apply_le M C hC hM)

end NCG
