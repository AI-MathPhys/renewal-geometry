/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Invariant axis and the second-moment counterexample
  (`thm:phase-invariant-axis`, `cth:second-moment-nontriviality`,
   Gran-Tensor manuscript)

* `phase_axis_norm_identity`: the boxed Pythagoras split — for
  `p(a,u) = (a, (1-a)u)` with `Σu = 1` and
  `J_n(a) = a - (1-a)/n`,
  `(n+1)‖p(a,u) - 1/(n+1)‖² = nJ_n(a)² + (n+1)(1-a)²‖u - 1/n‖²`;
* `phase_axis_split`: the boxed orthogonal decomposition — every
  centered vector splits uniquely as `t·ω_n ⊕ (0, w)` with
  `ω_n = (n,-1,…,-1)/√(n(n+1))` and `Σw = 0`;
* `ward_coordinate`: the boxed equivalences —
  `J_n(a) = 0 ↔ a = 1/(n+1)` and
  `|a - 1/(n+1)| = (n/(n+1))|J_n(a)|`;
* `second_moment_nontriviality`: the counterexample family —
  `μ_n = (1-1/n²)δ₀ + (1/2n²)(δ_n + δ_{-n})` is centered with
  unit second moment yet integrates every bounded observable to
  `f(0)` in the limit — a finite-stage variance floor does not
  pass through weak convergence.

Rendering disclosed: the `𝔖_n`-fixed-subspace clause is the
statement that the split is equivariant under permutations fixing
the head coordinate (immediate from the formulas); the weak-*
formulation of the counterexample is rendered on finite-support
integrals of bounded observables.
-/

open Filter

namespace NCG

/-- Boxed Pythagoras split for the concatenated law
`p(a,u) = (a, (1-a)u)`. -/
theorem phase_axis_norm_identity (n : ℕ) (hn : 1 ≤ n)
    (a : ℝ) (u : Fin n → ℝ) (hsum : ∑ i, u i = 1) :
    ((n : ℝ) + 1) * ((a - 1 / (n + 1)) ^ 2
        + ∑ i, ((1 - a) * u i - 1 / (n + 1)) ^ 2)
      = n * (a - (1 - a) / n) ^ 2
        + (n + 1) * (1 - a) ^ 2
          * ∑ i, (u i - 1 / n) ^ 2 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  set S2 : ℝ := ∑ i, u i ^ 2 with hS2
  have hexp1 : ∑ i, ((1 - a) * u i - 1 / (n + 1)) ^ 2
      = (1 - a) ^ 2 * S2 - 2 / (n + 1) * (1 - a)
        + n * (1 / (n + 1)) ^ 2 := by
    have h1 : ∀ i, ((1 - a) * u i - 1 / (n + 1)) ^ 2
        = (1 - a) ^ 2 * u i ^ 2
          - 2 / (n + 1) * (1 - a) * u i
          + (1 / (n + 1)) ^ 2 := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hexp2 : ∑ i, (u i - 1 / n) ^ 2
      = S2 - 2 / n + n * (1 / n) ^ 2 := by
    have h1 : ∀ i, (u i - 1 / n) ^ 2
        = u i ^ 2 - 2 / n * u i + (1 / n) ^ 2 := fun i => by
      ring
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hsum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hexp1, hexp2]
  field_simp
  ring

/-- Boxed orthogonal decomposition: a centered vector splits
uniquely into the invariant axis and the tail-centered fibre. -/
theorem phase_axis_split (n : ℕ) (hn : 1 ≤ n)
    (v : Fin (n + 1) → ℝ) (hv : ∑ j, v j = 0) :
    ∃! tw : ℝ × (Fin n → ℝ),
      (∑ i, tw.2 i = 0)
      ∧ v 0 = tw.1 * (n / Real.sqrt (n * (n + 1)))
      ∧ ∀ i : Fin n,
          v i.succ = tw.1 * (-1 / Real.sqrt (n * (n + 1)))
            + tw.2 i := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hsq : (0:ℝ) < Real.sqrt (n * (n + 1)) := by
    refine Real.sqrt_pos.mpr ?_
    positivity
  have hvsplit : v 0 + ∑ i : Fin n, v i.succ = 0 := by
    rw [← Fin.sum_univ_succ]
    exact hv
  refine ⟨⟨v 0 * Real.sqrt (n * (n + 1)) / n,
    fun i => v i.succ + v 0 / n⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : ∑ i : Fin n, v i.succ = -v 0 := by linarith
    rw [this]
    field_simp
    ring
  · field_simp
  · intro i
    have h1 : v 0 * Real.sqrt (n * (n + 1)) / n
        * (-1 / Real.sqrt (n * (n + 1))) = -v 0 / n := by
      field_simp
    rw [h1]
    ring
  · rintro ⟨t, w⟩ ⟨hw0, h0, hi⟩
    have ht : t = v 0 * Real.sqrt (n * (n + 1)) / n := by
      rw [h0]
      field_simp
    refine Prod.ext ht (funext fun i => ?_)
    change w i = v i.succ + v 0 / (n:ℝ)
    have hthis := hi i
    dsimp only at hthis
    rw [ht] at hthis
    have h1 : v 0 * Real.sqrt (n * (n + 1)) / n
        * (-1 / Real.sqrt (n * (n + 1)))
        = -(v 0 / (n:ℝ)) := by
      field_simp [hsq.ne', hnR.ne']
    rw [h1] at hthis
    linarith [hthis]

/-- Boxed Ward-coordinate equivalences:
`J_n(a) = 0 ↔ a = 1/(n+1)` and
`|a - 1/(n+1)| = (n/(n+1))|J_n(a)|`. -/
theorem ward_coordinate (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    (a - (1 - a) / n = 0 ↔ a = 1 / (n + 1))
    ∧ |a - 1 / (n + 1)|
      = n / (n + 1) * |a - (1 - a) / n| := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  constructor
  · constructor <;> intro h
    · have h' : a * ((n:ℝ) + 1) = 1 := by
        field_simp at h
        linarith
      rw [eq_div_iff (by positivity : ((n:ℝ) + 1) ≠ 0)]
      exact h'
    · rw [h]
      field_simp
      ring
  · have hkey : a - 1 / (n + 1)
        = n / (n + 1) * (a - (1 - a) / n) := by
      field_simp
      ring
    rw [hkey, abs_mul, abs_of_pos (by positivity :
      (0:ℝ) < n / (n + 1))]

/-- `cth:second-moment-nontriviality`: the explicit witness
family — centered, unit second moment, yet every bounded
observable integrates to `f(0)` in the limit. -/
theorem second_moment_nontriviality :
    (∀ n : ℕ, 1 ≤ n →
      (1 - 1 / (n:ℝ)^2) * 0 + 1 / (2 * n^2) * n
        + 1 / (2 * n^2) * (-(n:ℝ)) = 0
      ∧ (1 - 1 / (n:ℝ)^2) * 0^2 + 1 / (2 * n^2) * (n:ℝ)^2
        + 1 / (2 * n^2) * (-(n:ℝ))^2 = 1)
    ∧ ∀ (f : ℝ → ℝ) (M : ℝ), (∀ x, |f x| ≤ M) →
      Tendsto (fun n : ℕ => (1 - 1 / (n:ℝ)^2) * f 0
        + 1 / (2 * n^2) * f n + 1 / (2 * n^2) * f (-(n:ℝ)))
        atTop (nhds (f 0)) := by
  constructor
  · intro n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    constructor <;> field_simp <;> ring
  · intro f M hf
    have hM : 0 ≤ M := le_trans (abs_nonneg _) (hf 0)
    have hdecomp : ∀ n : ℕ,
        (1 - 1 / (n:ℝ)^2) * f 0 + 1 / (2 * n^2) * f n
          + 1 / (2 * n^2) * f (-(n:ℝ))
        = f 0 + (-(1 / (n:ℝ)^2) * f 0
          + 1 / (2 * n^2) * f n
          + 1 / (2 * n^2) * f (-(n:ℝ))) := fun n => by ring
    simp only [hdecomp]
    rw [show nhds (f 0) = nhds (f 0 + 0) by rw [add_zero]]
    refine Tendsto.const_add _ ?_
    refine squeeze_zero_norm
      (a := fun n : ℕ => 2 * M / (n:ℝ)^2) (fun n => ?_) ?_
    · have hbnd : ∀ (c : ℝ) (x : ℝ), 0 ≤ c →
          |c * f x| ≤ c * M := by
        intro c x hc
        rw [abs_mul, abs_of_nonneg hc]
        exact mul_le_mul_of_nonneg_left (hf x) hc
      calc ‖-(1 / (n:ℝ)^2) * f 0 + 1 / (2 * n^2) * f n
            + 1 / (2 * n^2) * f (-(n:ℝ))‖
          ≤ ‖-(1 / (n:ℝ)^2) * f 0 + 1 / (2 * n^2) * f n‖
            + ‖1 / (2 * (n:ℝ)^2) * f (-(n:ℝ))‖ :=
            norm_add_le _ _
        _ ≤ ‖-(1 / (n:ℝ)^2) * f 0‖
            + ‖1 / (2 * (n:ℝ)^2) * f n‖
            + ‖1 / (2 * (n:ℝ)^2) * f (-(n:ℝ))‖ := by
            have := norm_add_le (-(1 / (n:ℝ)^2) * f 0)
              (1 / (2 * n^2) * f n)
            linarith
        _ ≤ 1 / (n:ℝ)^2 * M + 1 / (2 * (n:ℝ)^2) * M
            + 1 / (2 * (n:ℝ)^2) * M := by
            have h1 : ‖-(1 / (n:ℝ)^2) * f 0‖
                ≤ 1 / (n:ℝ)^2 * M := by
              rw [Real.norm_eq_abs, neg_mul, abs_neg]
              exact hbnd _ _ (by positivity)
            have h2 : ‖1 / (2 * (n:ℝ)^2) * f n‖
                ≤ 1 / (2 * (n:ℝ)^2) * M := by
              rw [Real.norm_eq_abs]
              exact hbnd _ _ (by positivity)
            have h3 : ‖1 / (2 * (n:ℝ)^2) * f (-(n:ℝ))‖
                ≤ 1 / (2 * (n:ℝ)^2) * M := by
              rw [Real.norm_eq_abs]
              exact hbnd _ _ (by positivity)
            linarith
        _ = 2 * M / (n:ℝ)^2 := by ring
    · have h1 : Tendsto (fun n : ℕ => ((n:ℝ))^2) atTop
          atTop :=
        (tendsto_pow_atTop two_ne_zero).comp
          tendsto_natCast_atTop_atTop
      exact Tendsto.div_atTop tendsto_const_nhds h1

end NCG
