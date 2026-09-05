/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Action-derived scalar current and the provenance discharge
  (the two unlabeled corollaries "Action-derived scalar
  current" and "Common-action provenance discharges the
  normal–endpoint comparison", Gran-Tensor manuscript)

* `scalar_current_antisymmetric`: the lapse pairing
  `ω(N,M)_{(x,y)} = N_xM_y - M_xN_y` of the scalar Poisson
  bracket is antisymmetric in the lapse pair and vanishes on the
  diagonal — the algebraic shape of
  `{H(N), H(M)} = D_sc(ω(N,M))`;
* `provenance_discharge`: the boxed comparison — with the split
  `R_x = (n_x - h_x)V + (h_xV - Va_x)`, the residual obeys
  `Σ‖R_x‖² ≤ 2Σ‖A_x‖² + 2Σ‖B_x‖²`, so zero provenance
  residuals identify the generator-native normal and the
  endpoint writer as restrictions of one Hamiltonian flow.

Rendering disclosed: the Hamiltonian computation producing the
boxed edge current `J_e^sc` (inverse kinetic metric cancelling
the transported metric) and the whitened-contractivity of
`V_aff` folding `‖(n-h)V‖ ≤ ‖n-h‖` into `Δ_act→nor` are the
manuscript's mechanics; the antisymmetric pairing and the exact
two-two comparison are proved here.
-/

namespace NCG

/-- The scalar-bracket lapse pairing is antisymmetric and
vanishes on the diagonal. -/
theorem scalar_current_antisymmetric {ι : Type*} (N M : ι → ℝ)
    (x y : ι) :
    N x * M y - M x * N y = -(M x * N y - N x * M y)
      ∧ N x * N y - N x * N y = 0 := by
  constructor <;> ring

/-- Boxed provenance comparison: the split residual obeys the
two-two bound `Σ‖R‖² ≤ 2Σ‖A‖² + 2Σ‖B‖²`. -/
theorem provenance_discharge {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] (R A B : ι → E)
    (hsplit : ∀ x, R x = A x + B x) :
    ∑ x, ‖R x‖ ^ 2
      ≤ 2 * ∑ x, ‖A x‖ ^ 2 + 2 * ∑ x, ‖B x‖ ^ 2 := by
  have hstep : ∀ x ∈ Finset.univ,
      ‖R x‖ ^ 2 ≤ 2 * ‖A x‖ ^ 2 + 2 * ‖B x‖ ^ 2 := by
    intro x _
    have htri : ‖R x‖ ≤ ‖A x‖ + ‖B x‖ := by
      rw [hsplit x]
      exact norm_add_le _ _
    have h2 : ‖R x‖ ^ 2 ≤ (‖A x‖ + ‖B x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [h2, sq_nonneg (‖A x‖ - ‖B x‖)]
  calc ∑ x, ‖R x‖ ^ 2
      ≤ ∑ x, (2 * ‖A x‖ ^ 2 + 2 * ‖B x‖ ^ 2) :=
        Finset.sum_le_sum hstep
    _ = 2 * ∑ x, ‖A x‖ ^ 2 + 2 * ∑ x, ‖B x‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum,
          Finset.mul_sum]

end NCG
