import NCG.Grand.SpatiotemporalFeedback
import NCG.Grand.OperationalLightCone

/-! # exponential spatiotemporal weight removal -/

namespace NCG

/-- `thm:spatiotemporal-feedback`, graph-weight instantiation and the final
corner extraction.  A triangle distance makes `exp (μ d)`
submultiplicative, and a bound on the weighted row sum yields exactly the
displayed spatial-and-temporal corner decay. -/
theorem spatiotemporal_exponential_weights
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ι → ℝ) (hd : ∀ i j k, d i k ≤ d i j + d j k)
    (μ η q : ℝ) (hμ : 0 ≤ μ) (hq : q < 1)
    (W : ℕ → ι → ι → ℝ) (hW : ∀ m i j, 0 ≤ W m i j)
    (hrow : ∀ m i,
      ∑ j, Real.exp (μ * d i j) * W m i j
        ≤ Real.exp (-(η * m)) / (1 - q)) :
    (∀ i j k,
      Real.exp (μ * d i k)
        ≤ Real.exp (μ * d i j) * Real.exp (μ * d j k))
      ∧ (∀ m i j,
        W m i j ≤ Real.exp (-(μ * d i j))
          * Real.exp (-(η * m)) / (1 - q)) := by
  constructor
  · intro i j k
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hd i j k]
  · intro m i j
    have hterm : Real.exp (μ * d i j) * W m i j
        ≤ ∑ k, Real.exp (μ * d i k) * W m i k := by
      calc
        Real.exp (μ * d i j) * W m i j
            ≤ (∑ k ∈ (Finset.univ.erase j),
                Real.exp (μ * d i k) * W m i k)
              + Real.exp (μ * d i j) * W m i j := by
                exact le_add_of_nonneg_left
                  (Finset.sum_nonneg fun k _ =>
                    mul_nonneg (Real.exp_nonneg _) (hW m i k))
        _ = ∑ k, Real.exp (μ * d i k) * W m i k := by
              rw [Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    have hbound := hterm.trans (hrow m i)
    have hexp : 0 < Real.exp (μ * d i j) := Real.exp_pos _
    have heq : Real.exp (-(μ * d i j))
          * Real.exp (-(η * m)) / (1 - q)
        = (Real.exp (-(η * m)) / (1 - q)) /
            Real.exp (μ * d i j) := by
      rw [Real.exp_neg]
      field_simp
    rw [heq, le_div_iff₀ hexp]
    simpa [mul_comm] using hbound

end NCG
