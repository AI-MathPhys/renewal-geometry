import NCG.Grand.OperatorGraphResolventBound
import Mathlib.Analysis.InnerProductSpace.Adjoint

open Set

noncomputable section

namespace NCG.VaryingHilbert

universe v w

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem test_symm
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (lam : ℝ) (R : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    (R : E →ₗ[ℂ] E).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_inner_map_self_real]
  intro f
  apply Complex.conj_eq_iff_im.mpr
  have h := (hequation f).weakEuler
    (⟨R f, (hequation f).mem⟩ : D)
  have hI := (hequation f).weakEuler
    (Complex.I • (⟨R f, (hequation f).mem⟩ : D))
  simp only [map_smul, inner_smul_right, inner_smul_left,
    Complex.conj_I, Complex.I_mul_re, Complex.ofReal_re,
    inner_self_im, mul_zero, neg_zero, add_zero] at hI
  exact hI

end NCG.VaryingHilbert
