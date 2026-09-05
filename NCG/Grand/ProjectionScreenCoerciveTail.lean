import NCG.Grand.OperatorGraphCoerciveResolventBound
import NCG.Grand.OperatorNormConvergenceFromScreens

/-!
# Coercive estimates for complementary screen compressions

For an idempotent screen commuting with an operator, the error made by
compressing on both sides is precisely the compression to the complementary
screen.  Consequently a coercive graph estimate on that complementary piece
is already an operator-norm tail estimate in the form expected by the common
screen convergence compiler.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- The complementary screen associated with an endomorphism `S`. -/
def screenComplement (S : E →L[K] E) : E →L[K] E :=
  1 - S

/-- For a commuting idempotent screen, the two-sided compression error is
exactly the complementary compression. -/
theorem sub_screenCompression_eq_complementaryCompression
    (S T : E →L[K] E)
    (hidem : S.comp S = S)
    (hcomm : S.comp T = T.comp S) :
    T - screenCompression S T =
      (screenComplement S).comp (T.comp (screenComplement S)) := by
  ext x
  have hST (y : E) : S (T y) = T (S y) := by
    exact congrArg (fun U : E →L[K] E ↦ U y) hcomm
  have hSS (y : E) : S (S y) = S y := by
    exact congrArg (fun U : E →L[K] E ↦ U y) hidem
  simp only [screenCompression, screenComplement, sub_apply,
    ContinuousLinearMap.comp_apply, one_apply_eq_self]
  rw [map_sub, map_sub, hST, hST, hSS]
  abel

/-- Norm form of the complementary-compression identity. -/
theorem norm_sub_screenCompression_eq_complementaryCompression
    (S T : E →L[K] E)
    (hidem : S.comp S = S)
    (hcomm : S.comp T = T.comp S) :
    ‖T - screenCompression S T‖ =
      ‖(screenComplement S).comp (T.comp (screenComplement S))‖ := by
  rw [sub_screenCompression_eq_complementaryCompression S T hidem hcomm]

/-- A coercive graph realization of the complementary resolvent gives the
screen-tail estimate `1 / (λ + μ)`. -/
theorem norm_sub_screenCompression_le_inv_add_of_complementaryGraph
    (S T : E →L[K] E) (D : Submodule K E) (A : D →ₗ[K] F)
    (lam mu : ℝ)
    (hidem : S.comp S = S)
    (hcomm : S.comp T = T.comp S)
    (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoercive : ∀ y : D, mu * ‖(y : E)‖ ^ 2 ≤ ‖A y‖ ^ 2)
    (hgraph : ∀ f : E,
      VaryingHilbert.OperatorGraphResolventEquation D A lam f
        ((screenComplement S).comp (T.comp (screenComplement S)) f)) :
    ‖T - screenCompression S T‖ ≤ 1 / (lam + mu) := by
  rw [norm_sub_screenCompression_eq_complementaryCompression S T hidem hcomm]
  exact VaryingHilbert.operatorGraphResolvent_opNorm_le_inv_add
    D A ((screenComplement S).comp (T.comp (screenComplement S)))
      lam mu hlam hmu hcoercive hgraph

/-- The same coercive estimate in the orientation used for the limiting
operator's tail. -/
theorem norm_screenCompression_sub_le_inv_add_of_complementaryGraph
    (S T : E →L[K] E) (D : Submodule K E) (A : D →ₗ[K] F)
    (lam mu : ℝ)
    (hidem : S.comp S = S)
    (hcomm : S.comp T = T.comp S)
    (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoercive : ∀ y : D, mu * ‖(y : E)‖ ^ 2 ≤ ‖A y‖ ^ 2)
    (hgraph : ∀ f : E,
      VaryingHilbert.OperatorGraphResolventEquation D A lam f
        ((screenComplement S).comp (T.comp (screenComplement S)) f)) :
    ‖screenCompression S T - T‖ ≤ 1 / (lam + mu) := by
  rw [norm_sub_rev]
  exact norm_sub_screenCompression_le_inv_add_of_complementaryGraph
    S T D A lam mu hidem hcomm hlam hmu hcoercive hgraph

end NCG
