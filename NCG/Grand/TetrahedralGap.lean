/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Prototype triangle controls the complete tetrahedral gap
  (`thm:tetrahedral-prototype-gap`,
  Gran-Tensor manuscript)

* `tetrahedral_prototype_gap`:
  (i) the flat complete-graph identity: on `K₄`, every
      zero-sum field satisfies
      `∑_{i<j} ‖f_j - f_i‖² = 4∑_i ‖f_i‖²`;
  (ii) the boxed perturbation ledger: a flat floor `4m‖f‖²`,
      a holonomy error at most `2Mδ‖f‖²` (three non-tree
      edges) and Hessian errors at most `6ε‖f‖²` give the
      boxed local Hodge floor
      `q_act(f) ≥ (4m - 2Mδ - 6ε)‖f‖²`;
  (iii) the boxed positivity criterion
      `4m > 2Mδ + 6ε` makes the floor positive;
  (iv) with `δ → 0` and `ε → 0` the gap converges to the
      flat value `4m`.

The star-tree gauge (three tree routers set to the
identity, each non-tree router within `δ = ‖I - H₁₂₃‖` of
the identity by the prototype-triangle conjugacy of
`NCG.tetrahedral_prototype_connection`) and the metric
comparison `mI ⪯ G ⪯ MI` are the manuscript's gauge layer
producing the three hypotheses of clause (ii).
-/

open Filter
open scoped InnerProductSpace

namespace NCG

/-- `thm:tetrahedral-prototype-gap`. -/
theorem tetrahedral_prototype_gap {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    -- (i) the flat complete-graph identity on zero-sum fields
    (∀ f : Fin 4 → V, f 0 + f 1 + f 2 + f 3 = 0 →
      ‖f 1 - f 0‖ ^ 2 + ‖f 2 - f 0‖ ^ 2 + ‖f 3 - f 0‖ ^ 2
        + ‖f 2 - f 1‖ ^ 2 + ‖f 3 - f 1‖ ^ 2
        + ‖f 3 - f 2‖ ^ 2
      = 4 * (‖f 0‖ ^ 2 + ‖f 1‖ ^ 2 + ‖f 2‖ ^ 2
        + ‖f 3‖ ^ 2))
    -- (ii) the boxed perturbation ledger
    ∧ (∀ qact qflat errH errE nf m M δ ε : ℝ,
        qflat ≤ qact + errH + errE →
        4 * m * nf ≤ qflat →
        errH ≤ 2 * M * δ * nf →
        errE ≤ 6 * ε * nf →
        (4 * m - 2 * M * δ - 6 * ε) * nf ≤ qact)
    -- (iii) the boxed positivity criterion
    ∧ (∀ m M δ ε nf : ℝ, 0 < nf →
        2 * M * δ + 6 * ε < 4 * m →
        0 < (4 * m - 2 * M * δ - 6 * ε) * nf)
    -- (iv) the gap converges to the flat value
    ∧ (∀ (m M : ℝ) (δ ε : ℕ → ℝ),
        Tendsto δ atTop (nhds 0) →
        Tendsto ε atTop (nhds 0) →
        Tendsto (fun n => 4 * m - 2 * M * δ n - 6 * ε n)
          atTop (nhds (4 * m))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hsum
    -- inner-product expansion of the six edges
    have hexp : ∀ i j : Fin 4, ‖f j - f i‖ ^ 2
        = ‖f j‖ ^ 2 - 2 * ⟪f j, f i⟫_ℝ + ‖f i‖ ^ 2 := by
      intro i j
      rw [norm_sub_sq_real]
    -- the zero-sum constraint kills the cross terms
    have h0 : ⟪f 0 + f 1 + f 2 + f 3,
        f 0 + f 1 + f 2 + f 3⟫_ℝ = 0 := by
      rw [hsum, inner_zero_left]
    simp only [inner_add_left, inner_add_right,
      real_inner_self_eq_norm_sq] at h0
    have hc01 : ⟪f 0, f 1⟫_ℝ = ⟪f 1, f 0⟫_ℝ :=
      real_inner_comm _ _
    have hc02 : ⟪f 0, f 2⟫_ℝ = ⟪f 2, f 0⟫_ℝ :=
      real_inner_comm _ _
    have hc03 : ⟪f 0, f 3⟫_ℝ = ⟪f 3, f 0⟫_ℝ :=
      real_inner_comm _ _
    have hc12 : ⟪f 1, f 2⟫_ℝ = ⟪f 2, f 1⟫_ℝ :=
      real_inner_comm _ _
    have hc13 : ⟪f 1, f 3⟫_ℝ = ⟪f 3, f 1⟫_ℝ :=
      real_inner_comm _ _
    have hc23 : ⟪f 2, f 3⟫_ℝ = ⟪f 3, f 2⟫_ℝ :=
      real_inner_comm _ _
    rw [hexp 0 1, hexp 0 2, hexp 0 3, hexp 1 2, hexp 1 3,
      hexp 2 3]
    linarith
  · intro qact qflat errH errE nf m M δ ε h1 h2 h3 h4
    have hexp : (4 * m - 2 * M * δ - 6 * ε) * nf
        = 4 * m * nf - 2 * M * δ * nf - 6 * ε * nf := by
      ring
    rw [hexp]
    linarith
  · intro m M δ ε nf hnf h
    have hco : 0 < 4 * m - 2 * M * δ - 6 * ε := by
      linarith
    exact mul_pos hco hnf
  · intro m M δ ε hδ hε
    have h1 : Tendsto (fun n => 2 * M * δ n) atTop
        (nhds 0) := by
      have h := hδ.const_mul (2 * M)
      simpa using h
    have h2 : Tendsto (fun n => 6 * ε n) atTop
        (nhds 0) := by
      have h := hε.const_mul 6
      simpa using h
    have h3 := (tendsto_const_nhds
      (x := 4 * m) (f := atTop)).sub h1 |>.sub h2
    simpa using h3

end NCG
