import NCG.Grand.GrandInterfaceEasy

/-!
# Exact EASY batch 29: the final block-resolvent bound

This is the norm estimate for the manuscript's Feshbach decomposition of the
full block resolvent.  Together with `interface_coercivity` it closes both
displayed clauses of `thm:interface-coercivity`.
-/

namespace NCG

/-- `thm:interface-coercivity`, second display.  If the full resolvent has the
Feshbach form `D⁻¹ + γ Λ⁻¹ γ̄*`, the direct interior, exterior inverse, and
solution-map bounds give the claimed network estimate. -/
theorem interface_block_resolvent_bound
    {𝔄 : Type*} [NormedRing 𝔄]
    (R Dinv γ Linv γbar : 𝔄) (MD MB δE : ℝ)
    (hMD : 0 ≤ MD) (hMB : 0 ≤ MB) (hδE : 0 < δE)
    (hR : R = Dinv + γ * Linv * γbar)
    (hD : ‖Dinv‖ ≤ MD) (hL : ‖Linv‖ ≤ 1 / δE)
    (hγ : ‖γ‖ * ‖γbar‖ ≤ 1 + MD ^ 2 * MB ^ 2) :
    ‖R‖ ≤ MD + (1 + MD ^ 2 * MB ^ 2) / δE := by
  have hden : 0 ≤ 1 / δE := by positivity
  have hfac : 0 ≤ 1 + MD ^ 2 * MB ^ 2 := by positivity
  have htriple : ‖γ * Linv * γbar‖
      ≤ (1 + MD ^ 2 * MB ^ 2) * (1 / δE) := by
    calc
      ‖γ * Linv * γbar‖ ≤ ‖γ * Linv‖ * ‖γbar‖ := norm_mul_le _ _
      _ ≤ (‖γ‖ * ‖Linv‖) * ‖γbar‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = (‖γ‖ * ‖γbar‖) * ‖Linv‖ := by ring
      _ ≤ (1 + MD ^ 2 * MB ^ 2) * (1 / δE) :=
        mul_le_mul hγ hL (norm_nonneg _) hfac
  rw [hR]
  calc
    ‖Dinv + γ * Linv * γbar‖ ≤ ‖Dinv‖ + ‖γ * Linv * γbar‖ :=
      norm_add_le _ _
    _ ≤ MD + (1 + MD ^ 2 * MB ^ 2) * (1 / δE) :=
      add_le_add hD htriple
    _ = MD + (1 + MD ^ 2 * MB ^ 2) / δE := by
      simp [div_eq_mul_inv]

end NCG
