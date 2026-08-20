/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventBound
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Continuous graph-output maps for weak graph resolvents

A weak graph-resolvent equation places every resolvent vector in the graph
domain.  Testing the equation on that vector also bounds the graph component,
so the pointwise map `f ↦ (R f, A (R f))` is a continuous linear map.  This
is the model-facing object to which compact graph screens apply.
-/

open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- A weak graph-resolvent equation bounds its graph component.  The slightly
non-sharp constant `1 + 1 / lam` avoids introducing square roots and is uniform
on every family with fixed positive shift. -/
theorem OperatorGraphResolventEquation.graphComponent_norm_le
    {D : Submodule K E} {A : D →ₗ[K] F} {lam : ℝ} {f x : E}
    (h : OperatorGraphResolventEquation D A lam f x) (hlam : 0 < lam) :
    ‖A ⟨x, h.mem⟩‖ ≤ (1 + 1 / lam) * ‖f‖ := by
  have heuler := h.weakEuler ⟨x, h.mem⟩
  rw [← norm_sq_eq_re_inner (𝕜 := K) (A ⟨x, h.mem⟩),
    ← norm_sq_eq_re_inner (𝕜 := K) x] at heuler
  have hre : RCLike.re (inner K x f) ≤ ‖x‖ * ‖f‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm x f)
  have hx := h.norm_le_inv_mul hlam
  have hinv : 0 ≤ 1 / lam := by positivity
  have hAquad : ‖A ⟨x, h.mem⟩‖ ^ 2 ≤ (1 / lam) * ‖f‖ ^ 2 := by
    have hAx : ‖A ⟨x, h.mem⟩‖ ^ 2 ≤ ‖x‖ * ‖f‖ := by
      have hlamSq : 0 ≤ lam * ‖x‖ ^ 2 :=
        mul_nonneg hlam.le (sq_nonneg ‖x‖)
      nlinarith
    calc
      ‖A ⟨x, h.mem⟩‖ ^ 2 ≤ ‖x‖ * ‖f‖ := hAx
      _ ≤ ((1 / lam) * ‖f‖) * ‖f‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg f)
      _ = (1 / lam) * ‖f‖ ^ 2 := by ring
  have hcoeffSq : 1 / lam ≤ (1 + 1 / lam) ^ 2 := by
    nlinarith [sq_nonneg (1 - 1 / lam)]
  have htargetSq :
      ‖A ⟨x, h.mem⟩‖ ^ 2 ≤ ((1 + 1 / lam) * ‖f‖) ^ 2 := by
    calc
      ‖A ⟨x, h.mem⟩‖ ^ 2 ≤ (1 / lam) * ‖f‖ ^ 2 := hAquad
      _ ≤ (1 + 1 / lam) ^ 2 * ‖f‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeffSq (sq_nonneg ‖f‖)
      _ = ((1 + 1 / lam) * ‖f‖) ^ 2 := by ring
  have hcoeff : 0 ≤ 1 + 1 / lam := by linarith
  have hrhs : 0 ≤ (1 + 1 / lam) * ‖f‖ :=
    mul_nonneg hcoeff (norm_nonneg f)
  nlinarith [norm_nonneg (A ⟨x, h.mem⟩)]

/-- The algebraic lift of a graph resolvent into its operator domain. -/
def operatorGraphResolventRangeLinearMap
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    E →ₗ[K] D where
  toFun f := ⟨R f, (hR f).mem⟩
  map_add' f g := Subtype.ext (R.map_add f g)
  map_smul' c f := Subtype.ext (R.map_smul c f)

@[simp] theorem operatorGraphResolventRangeLinearMap_coe
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f))
    (f : E) :
    (operatorGraphResolventRangeLinearMap D A R lam hR f : E) = R f := rfl

/-- The algebraic graph-output map associated with a weak graph resolvent. -/
def operatorGraphResolventGraphLinearMap
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    E →ₗ[K] E × F where
  toFun f := (R f, A (operatorGraphResolventRangeLinearMap D A R lam hR f))
  map_add' f g := by simp
  map_smul' c f := by simp

/-- The canonical continuous graph-output map `f ↦ (R f, A(R f))`. -/
def operatorGraphResolventGraph
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    E →L[K] E × F :=
  (operatorGraphResolventGraphLinearMap D A R lam hR).mkContinuous
    (1 + 1 / lam) (by
      intro f
      rw [Prod.norm_def]
      apply max_le
      · exact (hR f).norm_le_inv_mul hlam |>.trans
          (mul_le_mul_of_nonneg_right (by linarith [show 0 ≤ 1 / lam by positivity])
            (norm_nonneg f))
      · exact (hR f).graphComponent_norm_le hlam)

@[simp] theorem operatorGraphResolventGraph_apply_fst
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f))
    (f : E) :
    (operatorGraphResolventGraph D A R lam hlam hR f).1 = R f := rfl

@[simp] theorem operatorGraphResolventGraph_apply_snd
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f))
    (f : E) :
    (operatorGraphResolventGraph D A R lam hlam hR f).2 =
      A ⟨R f, (hR f).mem⟩ := rfl

/-- First-coordinate projection recovers the original resolvent exactly. -/
theorem fst_comp_operatorGraphResolventGraph
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    (ContinuousLinearMap.fst K E F).comp
      (operatorGraphResolventGraph D A R lam hlam hR) = R := by
  ext f
  rfl

/-- The canonical graph-output map with the Hilbert direct-sum norm.  This is
the literal carrier for graph screens based on `‖u‖² + ‖Au‖²`. -/
def operatorGraphResolventHilbertGraph
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    E →L[K] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 K E F).symm.toContinuousLinearMap.comp
    (operatorGraphResolventGraph D A R lam hlam hR)

@[simp] theorem operatorGraphResolventHilbertGraph_apply_fst
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f))
    (f : E) :
    (operatorGraphResolventHilbertGraph D A R lam hlam hR f).fst = R f := rfl

@[simp] theorem operatorGraphResolventHilbertGraph_apply_snd
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f))
    (f : E) :
    (operatorGraphResolventHilbertGraph D A R lam hlam hR f).snd =
      A ⟨R f, (hR f).mem⟩ := rfl

/-- Hilbert-graph first-coordinate projection recovers the resolvent. -/
theorem fstL_comp_operatorGraphResolventHilbertGraph
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    (WithLp.fstL 2 K E F).comp
      (operatorGraphResolventHilbertGraph D A R lam hlam hR) = R := by
  ext f
  rfl

/-- Uniform pointwise bound for the canonical Hilbert graph-output map. -/
theorem norm_operatorGraphResolventHilbertGraph_le
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f))
    (f : E) :
    ‖operatorGraphResolventHilbertGraph D A R lam hlam hR f‖ ≤
      (2 * (1 + 1 / lam)) * ‖f‖ := by
  let q : ℝ := (1 + 1 / lam) * ‖f‖
  have hinv : 0 ≤ 1 / lam := by positivity
  have hcoeff : 0 ≤ 1 + 1 / lam := by linarith
  have hq : 0 ≤ q := mul_nonneg hcoeff (norm_nonneg f)
  have hx : ‖R f‖ ≤ q := by
    exact (hR f).norm_le_inv_mul hlam |>.trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg f))
  have hA : ‖A ⟨R f, (hR f).mem⟩‖ ≤ q := by
    exact (hR f).graphComponent_norm_le hlam
  have hxSq : ‖R f‖ ^ 2 ≤ q ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hq).2 hx
  have hASq : ‖A ⟨R f, (hR f).mem⟩‖ ^ 2 ≤ q ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hq).2 hA
  have hmain : ‖operatorGraphResolventHilbertGraph D A R lam hlam hR f‖ ≤ 2 * q := by
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) hq),
      WithLp.prod_norm_sq_eq_of_L2]
    simp only [operatorGraphResolventHilbertGraph_apply_fst,
      operatorGraphResolventHilbertGraph_apply_snd]
    nlinarith [sq_nonneg q]
  simpa only [q, mul_assoc] using hmain


/-- Operator-norm form of the uniform Hilbert graph-output estimate. -/
theorem norm_operatorGraphResolventHilbertGraph_le_bound
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    ‖operatorGraphResolventHilbertGraph D A R lam hlam hR‖ ≤
      2 * (1 + 1 / lam) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  exact norm_operatorGraphResolventHilbertGraph_le D A R lam hlam hR f
end NCG.VaryingHilbert

