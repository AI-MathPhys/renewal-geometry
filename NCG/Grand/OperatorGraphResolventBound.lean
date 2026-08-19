/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealOperatorGraphResolventMinimizer

/-!
# Sharp bounds from weak operator-graph resolvent equations

Testing the weak Euler equation against the resolvent vector itself gives the energy identity.
Cauchy--Schwarz then proves the sharp bound `‖R_lam‖ ≤ 1 / lam`, so scaled positive-shift
resolvents are contractions without any extra analytic assumption.
-/

open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- A weak operator-graph resolvent equation gives the sharp pointwise resolvent bound. -/
theorem OperatorGraphResolventEquation.norm_le_inv_mul
    {D : Submodule K E} {A : D →ₗ[K] F} {lam : ℝ} {f x : E}
    (h : OperatorGraphResolventEquation D A lam f x) (hlam : 0 < lam) :
    ‖x‖ ≤ (1 / lam) * ‖f‖ := by
  have heuler := h.weakEuler ⟨x, h.mem⟩
  rw [← norm_sq_eq_re_inner (𝕜 := K) (A ⟨x, h.mem⟩),
    ← norm_sq_eq_re_inner (𝕜 := K) x] at heuler
  have hre : RCLike.re (inner K x f) ≤ ‖x‖ * ‖f‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm x f)
  have hquad : lam * ‖x‖ ^ 2 ≤ ‖x‖ * ‖f‖ := by
    nlinarith [sq_nonneg ‖A ⟨x, h.mem⟩‖]
  by_cases hx : ‖x‖ = 0
  · rw [hx]
    positivity
  have hxPos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
  have hlinear : lam * ‖x‖ ≤ ‖f‖ := by nlinarith
  calc
    ‖x‖ ≤ ‖f‖ / lam := (le_div_iff₀ hlam).2 (by simpa [mul_comm] using hlinear)
    _ = (1 / lam) * ‖f‖ := by ring

/-- A continuous linear solution operator for the weak graph equations has operator norm at most
the inverse positive shift. -/
theorem operatorGraphResolvent_opNorm_le_inv
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    ‖R‖ ≤ 1 / lam := by
  apply R.opNorm_le_bound
  · positivity
  intro f
  exact (hR f).norm_le_inv_mul hlam

/-- Multiplying a positive-shift graph resolvent by its shift produces a contraction. -/
theorem norm_smul_operatorGraphResolvent_le_one
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    ‖(lam : K) • R‖ ≤ 1 := by
  rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hlam]
  calc
    lam * ‖R‖ ≤ lam * (1 / lam) :=
      mul_le_mul_of_nonneg_left
        (operatorGraphResolvent_opNorm_le_inv D A R lam hlam hR) hlam.le
    _ = 1 := by field_simp

end NCG.VaryingHilbert
