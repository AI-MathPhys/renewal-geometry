import NCG.Grand.L2BlockDiagonal
import NCG.Grand.OperatorNormConvergenceFromEventualScreens

/-!
# Finite coordinate screens for block-diagonal `ℓ²` operators

This file provides the exact finite-screen calculus for block Fourier
multipliers.  Local block estimates control compressed operator norms, while
uniform estimates outside the finite coordinate set control the discarded
tail.
-/

noncomputable section

open Filter Topology
open scoped lp

namespace NCG

variable {ι E : Type*}
variable [DecidableEq ι]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An operator on an `ℓ²` direct sum is block diagonal with blocks `M`. -/
def IsL2BlockDiagonal (T : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E))
    (M : ι → E →L[ℂ] E) : Prop :=
  ∀ f i, T f i = M i (f i)

/-- The identity/zero block selecting one finite set of `ℓ²` coordinates. -/
def l2FinsetScreenBlock (s : Finset ι) (i : ι) : E →L[ℂ] E :=
  if i ∈ s then 1 else 0

theorem l2FinsetScreenBlock_norm_apply_le (s : Finset ι) (i : ι) (x : E) :
    ‖l2FinsetScreenBlock (E := E) s i x‖ ≤ 1 * ‖x‖ := by
  by_cases hi : i ∈ s <;> simp [l2FinsetScreenBlock, hi]

/-- Orthogonal coordinate projection onto a finite set in an `ℓ²` direct
sum. -/
def l2FinsetScreen (s : Finset ι) : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E) :=
  l2BlockDiagonal (l2FinsetScreenBlock (E := E) s) 1 zero_le_one
    (l2FinsetScreenBlock_norm_apply_le s)

@[simp]
theorem l2FinsetScreen_apply (s : Finset ι) (f : ℓ²(ι, E)) (i : ι) :
    l2FinsetScreen (E := E) s f i = if i ∈ s then f i else 0 := by
  change l2FinsetScreenBlock (E := E) s i (f i) =
    if i ∈ s then f i else 0
  by_cases hi : i ∈ s <;> simp [l2FinsetScreenBlock, hi]

theorem l2FinsetScreen_idempotent (s : Finset ι) :
    (l2FinsetScreen (E := E) s).comp (l2FinsetScreen (E := E) s) =
      l2FinsetScreen (E := E) s := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

theorem l2FinsetScreen_opNorm_le_one (s : Finset ι) :
    ‖l2FinsetScreen (E := E) s‖ ≤ 1 :=
  l2BlockDiagonal_opNorm_le _ 1 zero_le_one
    (l2FinsetScreenBlock_norm_apply_le s)

/-- Every block-diagonal operator commutes with each finite coordinate
screen. -/
theorem IsL2BlockDiagonal.commutes_l2FinsetScreen
    {T : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E)} {M : ι → E →L[ℂ] E}
    (hT : IsL2BlockDiagonal T M) (s : Finset ι) :
    (l2FinsetScreen (E := E) s).comp T =
      T.comp (l2FinsetScreen (E := E) s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  simp only [ContinuousLinearMap.comp_apply]
  rw [l2FinsetScreen_apply, hT f i, hT _ i, l2FinsetScreen_apply]
  by_cases hi : i ∈ s <;> simp [hi]

/-- A pointwise block bound outside the screen controls the full discarded
operator norm. -/
theorem IsL2BlockDiagonal.norm_sub_screenCompression_le_of_outside
    {T : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E)} {M : ι → E →L[ℂ] E}
    (hT : IsL2BlockDiagonal T M) (s : Finset ι)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (htail : ∀ i ∉ s, ∀ x, ‖M i x‖ ≤ δ * ‖x‖) :
    ‖T - screenCompression (l2FinsetScreen (E := E) s) T‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro f
  have hmono := lp.norm_mono (show (2 : ENNReal) ≠ 0 by norm_num)
    (x := (T - screenCompression (l2FinsetScreen (E := E) s) T) f)
    (y := (δ : ℂ) • f) (fun i ↦ by
      have hcoord :
          ((T - screenCompression (l2FinsetScreen (E := E) s) T) f) i =
            if i ∈ s then 0 else M i (f i) := by
        simp only [screenCompression, sub_apply, lp.coeFn_sub, Pi.sub_apply,
          ContinuousLinearMap.comp_apply]
        rw [hT f i, l2FinsetScreen_apply]
        by_cases hi : i ∈ s
        · rw [if_pos hi, hT _ i, l2FinsetScreen_apply]
          simp [hi]
        · simp [hi]
      rw [hcoord]
      by_cases hi : i ∈ s
      · simp [hi]
      · simpa only [screenCompression, sub_apply,
          ContinuousLinearMap.comp_apply, hi, if_false, lp.coeFn_smul, Pi.smul_apply,
          norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
          using htail i hi (f i))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hδ] using hmono

/-- Uniform block closeness on the finite screen controls the norm of the
difference of the two screened compressions. -/
theorem IsL2BlockDiagonal.norm_screenCompression_sub_le_of_inside
    {T U : ℓ²(ι, E) →L[ℂ] ℓ²(ι, E)}
    {M N : ι → E →L[ℂ] E}
    (hT : IsL2BlockDiagonal T M) (hU : IsL2BlockDiagonal U N)
    (s : Finset ι) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlocal : ∀ i ∈ s, ∀ x, ‖(M i - N i) x‖ ≤ δ * ‖x‖) :
    ‖screenCompression (l2FinsetScreen (E := E) s) T -
        screenCompression (l2FinsetScreen (E := E) s) U‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro f
  have hmono := lp.norm_mono (show (2 : ENNReal) ≠ 0 by norm_num)
    (x := (screenCompression (l2FinsetScreen (E := E) s) T -
      screenCompression (l2FinsetScreen (E := E) s) U) f)
    (y := (δ : ℂ) • f) (fun i ↦ by
      have hcoord :
          ((screenCompression (l2FinsetScreen (E := E) s) T -
            screenCompression (l2FinsetScreen (E := E) s) U) f) i =
            if i ∈ s then (M i - N i) (f i) else 0 := by
        simp only [screenCompression, sub_apply, lp.coeFn_sub, Pi.sub_apply,
          ContinuousLinearMap.comp_apply]
        calc
          l2FinsetScreen (E := E) s
                (T (l2FinsetScreen (E := E) s f)) i -
              l2FinsetScreen (E := E) s
                (U (l2FinsetScreen (E := E) s f)) i =
              (if i ∈ s then T (l2FinsetScreen (E := E) s f) i else 0) -
                (if i ∈ s then U (l2FinsetScreen (E := E) s f) i else 0) :=
            congrArg₂ (· - ·)
              (l2FinsetScreen_apply s (T (l2FinsetScreen s f)) i)
              (l2FinsetScreen_apply s (U (l2FinsetScreen s f)) i)
          _ = if i ∈ s then (M i - N i) (f i) else 0 := by
            by_cases hi : i ∈ s
            · simp only [if_pos hi]
              rw [hT _ i, hU _ i, l2FinsetScreen_apply]
              simp only [hi, if_true, sub_apply]
            · simp only [if_neg hi, sub_zero]
      rw [hcoord]
      by_cases hi : i ∈ s
      · simpa only [screenCompression, sub_apply,
          ContinuousLinearMap.comp_apply, hi, if_true, sub_apply,
          lp.coeFn_smul, Pi.smul_apply,
          norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
          using hlocal i hi (f i)
      · simp [hi])
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hδ] using hmono

end NCG
