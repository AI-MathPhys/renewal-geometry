import NCG.Grand.BoundedOperatorNormalResolvent
import NCG.Grand.OperatorGraphCoerciveResolventBound
import NCG.Grand.CovariantSymbolFourierTail
import NCG.Grand.FiniteDirectionalOperatorStack
import NCG.Grand.CovariantFourierLaplacianSymbolConvergence

/-!
# Directional stacks for covariant Fourier symbols

For operator-valued connections, the directional covariant symbols are
stacked into one map.  Its normal operator is literally the summed positive
Laplacian symbol, and the phase-chord estimate becomes a coercivity estimate
for this stack outside a finite Fourier box.
-/

noncomputable section

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Nontrivial E]

/-- Stack of all finite-mesh directional covariant Fourier symbols. -/
def meshCovariantFourierOperatorStack
    (h : ℝ) (k : d → ℤ) (B : d → E →L[ℂ] E) :
    E →L[ℂ] PiLp 2 (fun _ : d ↦ E) :=
  finiteDirectionalOperatorStack fun j ↦
    meshCovariantFourierSymbol h (k j) (B j)

/-- Stack of all continuum directional covariant Fourier symbols. -/
def continuumCovariantFourierOperatorStack
    (k : d → ℤ) (B : d → E →L[ℂ] E) :
    E →L[ℂ] PiLp 2 (fun _ : d ↦ E) :=
  finiteDirectionalOperatorStack fun j ↦
    continuumCovariantFourierSymbol (k j) (B j)

@[simp]
theorem meshCovariantFourierOperatorStack_apply
    (h : ℝ) (k : d → ℤ) (B : d → E →L[ℂ] E) (v : E) (j : d) :
    meshCovariantFourierOperatorStack h k B v j =
      meshCovariantFourierSymbol h (k j) (B j) v := rfl

@[simp]
theorem continuumCovariantFourierOperatorStack_apply
    (k : d → ℤ) (B : d → E →L[ℂ] E) (v : E) (j : d) :
    continuumCovariantFourierOperatorStack k B v j =
      continuumCovariantFourierSymbol (k j) (B j) v := rfl

/-- The normal operator of the mesh stack is exactly the full positive mesh
Laplacian symbol. -/
theorem meshCovariantFourierOperatorStack_adjoint_comp
    (h : ℝ) (k : d → ℤ) (B : d → E →L[ℂ] E) :
    (meshCovariantFourierOperatorStack h k B).adjoint ∘L
        meshCovariantFourierOperatorStack h k B =
      meshCovariantLaplacianSymbol h k B := by
  rw [meshCovariantFourierOperatorStack,
    finiteDirectionalOperatorStack_adjoint_comp]
  unfold meshCovariantLaplacianSymbol meshCovariantPositiveSymbol
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-- The normal operator of the continuum stack is exactly the full positive
continuum Laplacian symbol. -/
theorem continuumCovariantFourierOperatorStack_adjoint_comp
    (k : d → ℤ) (B : d → E →L[ℂ] E) :
    (continuumCovariantFourierOperatorStack k B).adjoint ∘L
        continuumCovariantFourierOperatorStack k B =
      continuumCovariantLaplacianSymbol k B := by
  rw [continuumCovariantFourierOperatorStack,
    finiteDirectionalOperatorStack_adjoint_comp]
  unfold continuumCovariantLaplacianSymbol continuumCovariantPositiveSymbol
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-- Exact identification of the mesh stack energy with the explicit energy
used in the phase-chord lower bound. -/
theorem meshCovariantFourierOperatorStack_norm_sq_eq_totalEnergy
    (h : ℝ) (k : d → ℤ) (B : d → E →L[ℂ] E) (v : E)
    (hh : 0 < h)
    (hreal : ∀ (r : ℝ) (T : E →L[ℂ] E), r • T = (r : ℂ) • T) :
    ‖meshCovariantFourierOperatorStack h k B v‖ ^ 2 =
      covariantSymbolTotalEnergy h (fun j ↦ (k j : ℝ)) B v := by
  rw [meshCovariantFourierOperatorStack,
    finiteDirectionalOperatorStack_norm_sq]
  unfold covariantSymbolTotalEnergy
  apply Finset.sum_congr rfl
  intro j _
  rw [meshCovariantFourierSymbol_eq_explicit h (k j) (B j) hreal]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh]

/-- Outside a fixed Fourier box, the mesh directional stack has the canonical
coercivity floor `R²`. -/
theorem integerFourierCoercivityFloor_mul_norm_sq_le_meshStack
    (h : ℝ) (R : ℕ) (M : ℝ) (k : d → ℤ)
    (B : d → E →L[ℂ] E) (v : E)
    (hh : 0 < h) (hk : k ∉ integerFourierBox d R)
    (hNyquist : ∀ j, |2 * Real.pi * h * (k j : ℝ)| ≤ Real.pi)
    (hconnection : ∀ j,
      ‖B j‖ * Real.exp (h * ‖B j‖) ≤ M)
    (hthreshold : M ≤ 3 * (R : ℝ))
    (hreal : ∀ (r : ℝ) (T : E →L[ℂ] E), r • T = (r : ℂ) • T) :
    integerFourierCoercivityFloor R * ‖v‖ ^ 2 ≤
      ‖meshCovariantFourierOperatorStack h k B v‖ ^ 2 := by
  rw [meshCovariantFourierOperatorStack_norm_sq_eq_totalEnergy
    h k B v hh hreal]
  exact integerFourierCoercivityFloor_mul_norm_sq_le_totalEnergy
    h R M k B v hh hk hNyquist hconnection hthreshold

/-- The canonical positive-shift mesh-stack resolvent has an off-screen norm
bound `1 / (λ + R²)`. -/
theorem meshCovariantFourierOperatorStack_resolvent_opNorm_le
    (h : ℝ) (R : ℕ) (M : ℝ) (k : d → ℤ)
    (B : d → E →L[ℂ] E) (lam : ℝ)
    (hh : 0 < h) (hk : k ∉ integerFourierBox d R)
    (hlam : 0 < lam)
    (hNyquist : ∀ j, |2 * Real.pi * h * (k j : ℝ)| ≤ Real.pi)
    (hconnection : ∀ j,
      ‖B j‖ * Real.exp (h * ‖B j‖) ≤ M)
    (hthreshold : M ≤ 3 * (R : ℝ))
    (hreal : ∀ (r : ℝ) (T : E →L[ℂ] E), r • T = (r : ℂ) • T) :
    ‖VaryingHilbert.boundedOperatorNormalResolvent
        (meshCovariantFourierOperatorStack h k B) lam hlam‖ ≤
      1 / (lam + integerFourierCoercivityFloor R) := by
  apply VaryingHilbert.operatorGraphResolvent_opNorm_le_inv_add
    (⊤ : Submodule ℂ E)
    (VaryingHilbert.boundedOperatorGraphMap
      (meshCovariantFourierOperatorStack h k B))
    (VaryingHilbert.boundedOperatorNormalResolvent
      (meshCovariantFourierOperatorStack h k B) lam hlam)
    lam (integerFourierCoercivityFloor R) hlam
    (integerFourierCoercivityFloor_nonneg R)
  · intro v
    simpa only [VaryingHilbert.boundedOperatorGraphMap_apply] using
      integerFourierCoercivityFloor_mul_norm_sq_le_meshStack
        h R M k B (v : E) hh hk hNyquist hconnection hthreshold hreal
  · exact VaryingHilbert.boundedOperatorNormalResolvent_resolventEquation
      (meshCovariantFourierOperatorStack h k B) lam hlam

/-- Direct reverse-triangle lower bound for one continuum covariant Fourier
symbol. -/
theorem continuumCovariantFourierSymbol_apply_lower
    (k : ℤ) (B : E →L[ℂ] E) (v : E) :
    (2 * Real.pi * |(k : ℝ)| - ‖B‖) * ‖v‖ ≤
      ‖continuumCovariantFourierSymbol k B v‖ := by
  have hphase :
      ‖(covariantFourierPhaseGenerator
          (A := E →L[ℂ] E) k) v‖ =
        2 * Real.pi * |(k : ℝ)| * ‖v‖ := by
    unfold covariantFourierPhaseGenerator
    simp only [ContinuousLinearMap.smul_apply, one_apply_eq_self, norm_smul,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)), abs_of_pos Real.pi_pos]
  have hreverse := norm_sub_lower_of_phaseChord
    ((covariantFourierPhaseGenerator
      (A := E →L[ℂ] E) k) v) (-B v) 0
  have hBv : ‖B v‖ ≤ ‖B‖ * ‖v‖ :=
    ContinuousLinearMap.le_opNorm B v
  unfold continuumCovariantFourierSymbol
  simp only [add_apply, norm_neg, sub_zero, sub_neg_eq_add] at hreverse ⊢
  rw [hphase] at hreverse
  nlinarith

/-- Outside radius `R`, a connection bounded by `5R` leaves at least the
continuum coercivity floor `R²`. -/
theorem integerFourierCoercivityFloor_mul_norm_sq_le_continuumStack
    (R : ℕ) (M : ℝ) (k : d → ℤ)
    (B : d → E →L[ℂ] E) (v : E)
    (hk : k ∉ integerFourierBox d R)
    (hconnection : ∀ j, ‖B j‖ ≤ M)
    (hthreshold : M ≤ 5 * (R : ℝ)) :
    integerFourierCoercivityFloor R * ‖v‖ ^ 2 ≤
      ‖continuumCovariantFourierOperatorStack k B v‖ ^ 2 := by
  obtain ⟨j, hj⟩ :=
    exists_coordinate_natCast_lt_abs_intCast_of_not_mem_integerFourierBox hk
  have hpi : 6 < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hcoefficient :
      (R : ℝ) ≤ 2 * Real.pi * |(k j : ℝ)| - ‖B j‖ := by
    have hBj := hconnection j
    nlinarith
  have hjlower := continuumCovariantFourierSymbol_apply_lower
    (k j) (B j) v
  have hlinear :
      (R : ℝ) * ‖v‖ ≤
        ‖continuumCovariantFourierSymbol (k j) (B j) v‖ := by
    exact (mul_le_mul_of_nonneg_right hcoefficient (norm_nonneg v)).trans hjlower
  have hsquare :
      (R : ℝ) ^ 2 * ‖v‖ ^ 2 ≤
        ‖continuumCovariantFourierSymbol (k j) (B j) v‖ ^ 2 := by
    have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
    have hv : 0 ≤ ‖v‖ := norm_nonneg v
    have hrhs : 0 ≤ ‖continuumCovariantFourierSymbol (k j) (B j) v‖ :=
      norm_nonneg _
    have hleft : 0 ≤ (R : ℝ) * ‖v‖ := mul_nonneg hR hv
    have hs := (sq_le_sq₀ hleft hrhs).2 hlinear
    simpa only [mul_pow] using hs
  rw [continuumCovariantFourierOperatorStack,
    finiteDirectionalOperatorStack_norm_sq]
  exact hsquare.trans (Finset.single_le_sum
    (fun i _ ↦ sq_nonneg ‖continuumCovariantFourierSymbol (k i) (B i) v‖)
    (Finset.mem_univ j))

/-- The continuum positive-shift stack resolver has the same radius-squared
tail bound as the finite mesh resolvers. -/
theorem continuumCovariantFourierOperatorStack_resolvent_opNorm_le
    (R : ℕ) (M : ℝ) (k : d → ℤ)
    (B : d → E →L[ℂ] E) (lam : ℝ)
    (hk : k ∉ integerFourierBox d R) (hlam : 0 < lam)
    (hconnection : ∀ j, ‖B j‖ ≤ M)
    (hthreshold : M ≤ 5 * (R : ℝ)) :
    ‖VaryingHilbert.boundedOperatorNormalResolvent
        (continuumCovariantFourierOperatorStack k B) lam hlam‖ ≤
      1 / (lam + integerFourierCoercivityFloor R) := by
  apply VaryingHilbert.operatorGraphResolvent_opNorm_le_inv_add
    (⊤ : Submodule ℂ E)
    (VaryingHilbert.boundedOperatorGraphMap
      (continuumCovariantFourierOperatorStack k B))
    (VaryingHilbert.boundedOperatorNormalResolvent
      (continuumCovariantFourierOperatorStack k B) lam hlam)
    lam (integerFourierCoercivityFloor R) hlam
    (integerFourierCoercivityFloor_nonneg R)
  · intro v
    simpa only [VaryingHilbert.boundedOperatorGraphMap_apply] using
      integerFourierCoercivityFloor_mul_norm_sq_le_continuumStack
        R M k B (v : E) hk hconnection hthreshold
  · exact VaryingHilbert.boundedOperatorNormalResolvent_resolventEquation
      (continuumCovariantFourierOperatorStack k B) lam hlam

end NCG
