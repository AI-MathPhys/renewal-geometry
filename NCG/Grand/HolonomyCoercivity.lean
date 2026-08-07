/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Gauge classes and coercivity of operational holonomy
  (`thm:operational-holonomy-coercivity`,
  Gran-Tensor manuscript)

* `operational_holonomy_coercivity` (tree-path core on a
  transport chain):
  (i) the telescoping transport bound: against the
      parallel-transported reference `g` (tree gauge), the
      deviation at depth `x` is controlled by the summed edge
      defects `‖f_{i+1} - U_i f_i‖`;
  (ii) the tree Poincaré inequality: the total squared
      deviation is bounded by the Cauchy–Schwarz constant
      `∑_{x ≤ m} x` times the holonomy energy
      `∑ ‖f_{i+1} - U_i f_i‖²`;
  (iii) the boxed constant: `∑_{x ≤ m} x = m(m+1)/2`
      (the unit-weight instance of `C_T`);
  (iv) gauge covariance: conjugating the routers by a vertex
      gauge `W` and transporting the field leaves every edge
      defect invariant, so the coercivity constant is a
      gauge invariant.

The assembly of these tree-path estimates into the full
graph constant `C_TH = 2C_T + 6|V|(1 + d_T^nt C_T)/σ_T²`
(non-tree edges, holonomy observability margin, spanning
tree enumeration) is the manuscript's finite bookkeeping
over this chain core, with the weighted `κ_e` generalization
obtained by rescaling each edge defect.
-/

open Finset

namespace NCG

/-- `thm:operational-holonomy-coercivity` (tree-path core). -/
theorem operational_holonomy_coercivity {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ℕ → V ≃ₗᵢ[ℂ] V) (f g : ℕ → V) (m : ℕ)
    (hg0 : g 0 = f 0)
    (hgrec : ∀ i, g (i + 1) = U i (g i)) :
    -- (i) telescoping transport bound
    (∀ x, ‖f x - g x‖
      ≤ ∑ i ∈ Finset.range x, ‖f (i + 1) - U i (f i)‖)
    -- (ii) the tree Poincaré inequality
    ∧ (∑ x ∈ Finset.range (m + 1), ‖f x - g x‖ ^ 2
        ≤ (∑ x ∈ Finset.range (m + 1), (x : ℝ))
          * ∑ i ∈ Finset.range m,
              ‖f (i + 1) - U i (f i)‖ ^ 2)
    -- (iii) the boxed constant
    ∧ (∑ x ∈ Finset.range (m + 1), (x : ℝ))
        = m * (m + 1) / 2
    -- (iv) gauge covariance of the edge defects
    ∧ (∀ (W : V ≃ₗᵢ[ℂ] V) (i x : ℕ),
        ‖W (f (x + 1))
          - ((W.symm.trans (U i)).trans W) (W (f x))‖
        = ‖f (x + 1) - U i (f x)‖) := by
  have hpt : ∀ x, ‖f x - g x‖
      ≤ ∑ i ∈ Finset.range x, ‖f (i + 1) - U i (f i)‖ := by
    intro x
    induction x with
    | zero => simp [hg0]
    | succ x ih =>
      rw [Finset.sum_range_succ]
      have hkey : ‖f (x + 1) - g (x + 1)‖
          ≤ ‖f (x + 1) - U x (f x)‖ + ‖f x - g x‖ := by
        calc ‖f (x + 1) - g (x + 1)‖
            = ‖(f (x + 1) - U x (f x))
                + (U x (f x) - U x (g x))‖ := by
              rw [hgrec]
              congr 1
              abel
          _ ≤ ‖f (x + 1) - U x (f x)‖
              + ‖U x (f x) - U x (g x)‖ :=
              norm_add_le _ _
          _ = ‖f (x + 1) - U x (f x)‖ + ‖f x - g x‖ := by
              rw [← map_sub, LinearIsometryEquiv.norm_map]
      linarith [ih]
  refine ⟨hpt, ?_, ?_, ?_⟩
  · have hstep : ∀ x ∈ Finset.range (m + 1),
        ‖f x - g x‖ ^ 2
          ≤ (x : ℝ) * ∑ i ∈ Finset.range m,
              ‖f (i + 1) - U i (f i)‖ ^ 2 := by
      intro x hx
      have hx' : x ≤ m := by
        simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hx
      have h1 : ‖f x - g x‖ ^ 2
          ≤ (∑ i ∈ Finset.range x,
              ‖f (i + 1) - U i (f i)‖) ^ 2 := by
        have hb := hpt x
        have ha : (0 : ℝ) ≤ ‖f x - g x‖ := norm_nonneg _
        nlinarith [hb, ha]
      have h2 : (∑ i ∈ Finset.range x,
            ‖f (i + 1) - U i (f i)‖) ^ 2
          ≤ ((Finset.range x).card : ℝ)
            * ∑ i ∈ Finset.range x,
                ‖f (i + 1) - U i (f i)‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      rw [Finset.card_range] at h2
      have h3 : ∑ i ∈ Finset.range x,
            ‖f (i + 1) - U i (f i)‖ ^ 2
          ≤ ∑ i ∈ Finset.range m,
              ‖f (i + 1) - U i (f i)‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun i hi => Finset.mem_range.mpr
            (lt_of_lt_of_le (Finset.mem_range.mp hi) hx'))
          (fun i _ _ => sq_nonneg _)
      calc ‖f x - g x‖ ^ 2
          ≤ (x : ℝ) * ∑ i ∈ Finset.range x,
              ‖f (i + 1) - U i (f i)‖ ^ 2 :=
            le_trans h1 h2
        _ ≤ (x : ℝ) * ∑ i ∈ Finset.range m,
              ‖f (i + 1) - U i (f i)‖ ^ 2 :=
            mul_le_mul_of_nonneg_left h3
              (by exact_mod_cast Nat.zero_le x)
    calc ∑ x ∈ Finset.range (m + 1), ‖f x - g x‖ ^ 2
        ≤ ∑ x ∈ Finset.range (m + 1),
            (x : ℝ) * ∑ i ∈ Finset.range m,
              ‖f (i + 1) - U i (f i)‖ ^ 2 :=
          Finset.sum_le_sum hstep
      _ = (∑ x ∈ Finset.range (m + 1), (x : ℝ))
          * ∑ i ∈ Finset.range m,
              ‖f (i + 1) - U i (f i)‖ ^ 2 := by
          rw [← Finset.sum_mul]
  · have h2 : (∑ i ∈ Finset.range (m + 1), i) * 2
        = (m + 1) * m := by
      simpa using Finset.sum_range_id_mul_two (m + 1)
    have h3 : (∑ x ∈ Finset.range (m + 1), (x : ℝ)) * 2
        = ((m : ℝ) + 1) * m := by
      have hc := congrArg (fun k : ℕ => (k : ℝ)) h2
      push_cast at hc
      linarith [hc]
    linarith
  · intro W i x
    simp only [LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.symm_apply_apply]
    rw [← map_sub, LinearIsometryEquiv.norm_map]

end NCG
