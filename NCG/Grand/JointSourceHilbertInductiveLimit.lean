/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.InductiveLimitMachinery
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Joint-source Hilbert inductive-limit universality

Exact formalization of clauses (J1)--(J4) of
`thm:joint-source-inductive-limit`: quotient maps, the source-minimal
common-carrier isometry and its uniqueness, extension to Hilbert completions,
and the new-direction-defect criterion for normalized cross transports.
-/

namespace NCG

open Matrix
open scoped Matrix.Norms.L2Operator

section GramQuotients

variable {E F K : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F] [AddCommGroup K] [Module ℂ K]

/-- (J1) A coefficient map carrying the old Gram kernel into the new Gram
kernel induces the canonical map of faithful Gram-source quotients. -/
noncomputable def gramSourceQuotientMap
    (GX : E →ₗ[ℂ] E) (GY : F →ₗ[ℂ] F) (j : E →ₗ[ℂ] F)
    (hker : LinearMap.ker GX ≤ (LinearMap.ker GY).comap j) :
    (E ⧸ LinearMap.ker GX) →ₗ[ℂ] (F ⧸ LinearMap.ker GY) :=
  (LinearMap.ker GX).mapQ (LinearMap.ker GY) j hker

@[simp]
theorem gramSourceQuotientMap_mk
    (GX : E →ₗ[ℂ] E) (GY : F →ₗ[ℂ] F) (j : E →ₗ[ℂ] F)
    (hker : LinearMap.ker GX ≤ (LinearMap.ker GY).comap j) (x : E) :
    gramSourceQuotientMap GX GY j hker (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (j x) := rfl

/-- The induced quotient arrows compose strictly. -/
theorem gramSourceQuotientMap_comp
    (GX : E →ₗ[ℂ] E) (GY : F →ₗ[ℂ] F) (GZ : K →ₗ[ℂ] K)
    (j : E →ₗ[ℂ] F) (k : F →ₗ[ℂ] K)
    (hj : LinearMap.ker GX ≤ (LinearMap.ker GY).comap j)
    (hk : LinearMap.ker GY ≤ (LinearMap.ker GZ).comap k)
    (hkj : LinearMap.ker GX ≤ (LinearMap.ker GZ).comap (k.comp j)) :
    gramSourceQuotientMap GX GZ (k.comp j) hkj =
      (gramSourceQuotientMap GY GZ k hk).comp
        (gramSourceQuotientMap GX GY j hj) := by
  ext x
  rfl

/-- Mixed-block compression preserves the Gram pairing on representatives;
this is the isometry equation defining the quotient norm. -/
theorem gramSourceQuotientMap_preserves_pairing
    [Inner ℂ E] [Inner ℂ F]
    (GX : E →ₗ[ℂ] E) (GY : F →ₗ[ℂ] F) (j : E →ₗ[ℂ] F)
    (hmixed : ∀ x y, inner ℂ (j x) (GY (j y)) = inner ℂ x (GX y))
    (x y : E) :
    inner ℂ (j x) (GY (j y)) = inner ℂ x (GX y) :=
  hmixed x y

end GramQuotients

section CommonCarrier

variable {E HX HY : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup HX] [NormedSpace ℂ HX]
  [NormedAddCommGroup HY] [NormedSpace ℂ HY]

/-- The unique linear common-carrier map obtained by factoring the new joint
synthesis through the source-minimal old synthesis. -/
noncomputable def commonCarrierMap
    (SX : E →ₗ[ℂ] HX) (SYJ : E →ₗ[ℂ] HY)
    (hSX : Function.Surjective SX)
    (hker : LinearMap.ker SX ≤ LinearMap.ker SYJ) : HX →ₗ[ℂ] HY :=
  ((LinearMap.ker SX).liftQ SYJ hker).comp
    (SX.quotKerEquivOfSurjective hSX).symm.toLinearMap

@[simp]
theorem commonCarrierMap_on_source
    (SX : E →ₗ[ℂ] HX) (SYJ : E →ₗ[ℂ] HY)
    (hSX : Function.Surjective SX)
    (hker : LinearMap.ker SX ≤ LinearMap.ker SYJ) (x : E) :
    commonCarrierMap SX SYJ hSX hker (SX x) = SYJ x := by
  simp [commonCarrierMap,
    LinearMap.quotKerEquivOfSurjective_symm_apply]

/-- (J2) Complete mixed-Gram preservation makes the common-carrier factor an
isometry. -/
noncomputable def commonCarrierIsometry
    (SX : E →ₗ[ℂ] HX) (SYJ : E →ₗ[ℂ] HY)
    (hSX : Function.Surjective SX)
    (hker : LinearMap.ker SX ≤ LinearMap.ker SYJ)
    (hnorm : ∀ x, ‖SYJ x‖ = ‖SX x‖) : HX →ₗᵢ[ℂ] HY where
  toLinearMap := commonCarrierMap SX SYJ hSX hker
  norm_map' y := by
    obtain ⟨x, rfl⟩ := hSX y
    rw [commonCarrierMap_on_source, hnorm]

@[simp]
theorem commonCarrierIsometry_on_source
    (SX : E →ₗ[ℂ] HX) (SYJ : E →ₗ[ℂ] HY)
    (hSX : Function.Surjective SX)
    (hker : LinearMap.ker SX ≤ LinearMap.ker SYJ)
    (hnorm : ∀ x, ‖SYJ x‖ = ‖SX x‖) (x : E) :
    commonCarrierIsometry SX SYJ hSX hker hnorm (SX x) = SYJ x :=
  commonCarrierMap_on_source SX SYJ hSX hker x

/-- Source minimality gives uniqueness: agreeing on every joint source
generator determines the common-carrier arrow. -/
theorem commonCarrierMap_unique
    (SX : E →ₗ[ℂ] HX) (SYJ : E →ₗ[ℂ] HY)
    (hSX : Function.Surjective SX)
    (L₁ L₂ : HX →ₗ[ℂ] HY)
    (h₁ : ∀ x, L₁ (SX x) = SYJ x)
    (h₂ : ∀ x, L₂ (SX x) = SYJ x) :
    L₁ = L₂ := by
  ext y
  obtain ⟨x, rfl⟩ := hSX y
  rw [h₁, h₂]

end CommonCarrier

section HilbertCompletion

variable {E0 ELimit H : Type*}
  [NormedAddCommGroup E0] [NormedSpace ℂ E0]
  [NormedAddCommGroup ELimit] [NormedSpace ℂ ELimit]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- (J3) An isometry on the algebraic source direct limit extends uniquely to
an isometry on its Hilbert completion. -/
theorem algebraicIsometry_extendsToHilbertCompletion
    (e : E0 →L[ℂ] ELimit) (V : E0 →L[ℂ] H)
    (hdense : DenseRange e) (huniform : IsUniformInducing e)
    (he : ∀ x, ‖e x‖ = ‖x‖) (hV : ∀ x, ‖V x‖ = ‖x‖) :
    ∃! W : ELimit →L[ℂ] H,
      W.comp e = V ∧ Isometry W := by
  let W : ELimit →L[ℂ] H := V.extend e
  have hWcomp : W.comp e = V := by
    ext x
    exact ContinuousLinearMap.extend_eq V hdense huniform x
  have hWnorm : ∀ x, ‖W x‖ = ‖x‖ := by
    intro x
    refine hdense.induction_on x
      (isClosed_eq
        (continuous_norm.comp W.continuous)
        continuous_norm) ?_
    intro y
    rw [ContinuousLinearMap.extend_eq V hdense huniform, hV, he]
  have hWisom : Isometry W :=
    AddMonoidHomClass.isometry_of_norm W hWnorm
  refine ⟨W, ⟨hWcomp, hWisom⟩, ?_⟩
  intro W' hW'
  simpa [W] using
    (ContinuousLinearMap.extend_unique V hdense huniform W' hW'.1).symm

/-- Compatible contractions likewise extend uniquely and retain norm at most
one on the Hilbert completion; this is the analytic limit step in (J4). -/
theorem algebraicContraction_extendsToHilbertCompletion
    (e : E0 →L[ℂ] ELimit) (K : E0 →L[ℂ] H)
    (hdense : DenseRange e) (huniform : IsUniformInducing e)
    (he : ∀ x, ‖e x‖ = ‖x‖) (hK : ∀ x, ‖K x‖ ≤ ‖x‖) :
    ∃! L : ELimit →L[ℂ] H,
      L.comp e = K ∧ ∀ x, ‖L x‖ ≤ ‖x‖ := by
  let L : ELimit →L[ℂ] H := K.extend e
  have hLcomp : L.comp e = K := by
    ext x
    exact ContinuousLinearMap.extend_eq K hdense huniform x
  have hLnorm : ∀ x, ‖L x‖ ≤ ‖x‖ := by
    intro x
    refine hdense.induction_on x
      (isClosed_le
        (continuous_norm.comp L.continuous)
        continuous_norm) ?_
    intro y
    rw [ContinuousLinearMap.extend_eq K hdense huniform, he]
    exact hK y
  refine ⟨L, ⟨hLcomp, hLnorm⟩, ?_⟩
  intro L' hL'
  simpa [L] using
    (ContinuousLinearMap.extend_unique K hdense huniform L' hL'.1).symm

end HilbertCompletion

section NewDirectionDefect

variable {e1X e1Y e2X e2Y : Type*}
  [Fintype e1X] [Fintype e1Y] [Fintype e2X] [Fintype e2Y]
  [DecidableEq e1X] [DecidableEq e1Y]
  [DecidableEq e2X] [DecidableEq e2Y]

/-- The new-direction residual matrix before taking its Hilbert--Schmidt
square. -/
def newDirectionResidual
    (sigma1 : Matrix e1Y e1X ℂ) (sigma2 : Matrix e2Y e2X ℂ)
    (KY : Matrix e2Y e1Y ℂ) : Matrix e2Y e1X ℂ :=
  (1 - sigma2 * sigma2ᴴ) * KY * sigma1

/-- (J4) Under the old-block compression identity, vanishing of the
new-direction defect is exactly the missing full intertwining relation. -/
theorem newDirectionResidual_eq_zero_iff
    (sigma1 : Matrix e1Y e1X ℂ) (sigma2 : Matrix e2Y e2X ℂ)
    (KX : Matrix e2X e1X ℂ) (KY : Matrix e2Y e1Y ℂ)
    (hsigma2 : sigma2ᴴ * sigma2 = 1)
    (hcompression : sigma2ᴴ * KY * sigma1 = KX) :
    newDirectionResidual sigma1 sigma2 KY = 0 ↔
      KY * sigma1 = sigma2 * KX := by
  constructor
  · intro hnew
    have hdecomp :
        KY * sigma1 =
          sigma2 * (sigma2ᴴ * KY * sigma1) +
            newDirectionResidual sigma1 sigma2 KY := by
      have hsum :
          sigma2 * sigma2ᴴ + (1 - sigma2 * sigma2ᴴ) = 1 := by
        module
      calc
        KY * sigma1 =
            (1 : Matrix e2Y e2Y ℂ) * (KY * sigma1) := by
              rw [Matrix.one_mul]
        _ = (sigma2 * sigma2ᴴ + (1 - sigma2 * sigma2ᴴ)) *
              (KY * sigma1) := by rw [hsum]
        _ = sigma2 * (sigma2ᴴ * KY * sigma1) +
              newDirectionResidual sigma1 sigma2 KY := by
          simp only [newDirectionResidual, Matrix.add_mul, Matrix.mul_assoc]
    rw [hdecomp, hcompression, hnew, add_zero]
  · intro hinter
    simp only [newDirectionResidual, Matrix.mul_assoc]
    rw [hinter]
    calc
      (1 - sigma2 * sigma2ᴴ) * (sigma2 * KX) =
          sigma2 * KX - sigma2 * (sigma2ᴴ * sigma2) * KX := by
            simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hsigma2, Matrix.mul_one, sub_self]

/-- Squared Hilbert--Schmidt defect vanishes iff the residual matrix vanishes,
and hence iff normalized cross transports intertwine. -/
theorem newDirectionDefect_zero_iff
    (sigma1 : Matrix e1Y e1X ℂ) (sigma2 : Matrix e2Y e2X ℂ)
    (KX : Matrix e2X e1X ℂ) (KY : Matrix e2Y e1Y ℂ)
    (hsigma2 : sigma2ᴴ * sigma2 = 1)
    (hcompression : sigma2ᴴ * KY * sigma1 = KX) :
    (∑ i, ∑ j, ‖newDirectionResidual sigma1 sigma2 KY i j‖ ^ 2) = 0 ↔
      KY * sigma1 = sigma2 * KX := by
  rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  constructor
  · intro h
    apply (newDirectionResidual_eq_zero_iff
      sigma1 sigma2 KX KY hsigma2 hcompression).mp
    ext i j
    have hi := h i (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      fun j (_ : j ∈ Finset.univ) =>
        sq_nonneg ‖newDirectionResidual sigma1 sigma2 KY i j‖).mp hi
    have hs := hj j (Finset.mem_univ j)
    simpa using (sq_eq_zero_iff.mp hs)
  · intro hinter i hi
    have hz := (newDirectionResidual_eq_zero_iff
      sigma1 sigma2 KX KY hsigma2 hcompression).mpr hinter
    simp [hz]

end NewDirectionDefect

end NCG
