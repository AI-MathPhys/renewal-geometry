/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Conditional connected-uniformity bridge for affine
  primes (`thm:GT-affine-connected-bridge`,
  Gran-Tensor manuscript)

* `gt_affine_connected_bridge`: the manuscript's
  conditional bridge, with its hypotheses rendered as
  hypotheses: if the shorted decomposition writes the
  packet count as `P N = N^d·vol·β N + corr N` where
  (a) the fixed-coboundary bound gives
      `corr N ² ≤ a N · z N` (with `a = ‖A_{Ψ,N}‖²`,
      `z = ‖(Z^eff)* P^fix Z^eff‖`),
  (b) `a N = O_Ψ(N^d)` and the boxed `z N = o_Ψ(N^d)`,
  (c) the singular product converges, `β N → β∞`,
  then
  (i) the squared connected correction is `o(N^{2d})` —
      the manuscript's displayed intermediate bound;
  (ii) the boxed main term holds:
      `P N = N^d·vol·β∞ + o_Ψ(N^d)`, stated as
      `(P N - N^d·vol·β∞)/N^d → 0`.

The pipeline steps (A1)–(A3) producing the decomposition
(the proper-support shorts, the source-fusion and
occurrence audit of `thm:GT-source-fusion` /
`thm:GT-occurrence-Feshbach`, and the mean-ergodic
fixed-coboundary bound of `thm:GT-fixed-coboundary`) are
the cited theorems' layers — here they enter through the
decomposition-and-bound hypotheses, exactly as the
manuscript's conditional statement assumes them.
-/

open Filter

namespace NCG

/-- `thm:GT-affine-connected-bridge` (the conditional
bridge: `o(N^{2d})` correction and the boxed main
term). -/
theorem gt_affine_connected_bridge (d : ℕ)
    (P a z corr β : ℕ → ℝ) (vol βinf C : ℝ)
    -- the shorted decomposition
    (hdec : ∀ N, P N = (N : ℝ) ^ d * vol * β N + corr N)
    -- the fixed-coboundary bound
    (hcorr : ∀ N, (corr N) ^ 2 ≤ a N * z N)
    -- `‖A‖² = O(N^d)` with nonnegative data
    (ha : ∀ N, a N ≤ C * (N : ℝ) ^ d)
    (hz0 : ∀ N, 0 ≤ z N) (_hC : 0 ≤ C)
    -- the boxed `o(N^d)` hypothesis
    (hz : Tendsto (fun N : ℕ => z N / (N : ℝ) ^ d)
      atTop (nhds 0))
    -- singular-product convergence
    (hβ : Tendsto β atTop (nhds βinf)) :
    -- (i) the squared correction is `o(N^{2d})`
    Tendsto (fun N : ℕ =>
        (corr N) ^ 2 / (N : ℝ) ^ (2 * d))
      atTop (nhds 0)
    -- (ii) the boxed main term `P = N^d·vol·β∞ + o(N^d)`
    ∧ Tendsto (fun N : ℕ =>
        (P N - (N : ℝ) ^ d * vol * βinf) / (N : ℝ) ^ d)
      atTop (nhds 0) := by
  have hNpos : ∀ᶠ N : ℕ in atTop,
      (0 : ℝ) < (N : ℝ) ^ d := by
    filter_upwards [Filter.eventually_ge_atTop 1]
      with N hN
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  -- the squared-correction ratio is squeezed by `C·(z/N^d)`
  have hsq : Tendsto (fun N : ℕ =>
      (corr N) ^ 2 / (N : ℝ) ^ (2 * d))
      atTop (nhds 0) := by
    have hCz : Tendsto (fun N : ℕ =>
        C * (z N / (N : ℝ) ^ d)) atTop (nhds 0) := by
      have := hz.const_mul C
      simpa using this
    apply squeeze_zero' ?_ ?_ hCz
    · filter_upwards [hNpos] with N hN
      positivity
    · filter_upwards [hNpos] with N hN
      have h1 : (corr N) ^ 2 / (N : ℝ) ^ (2 * d)
          ≤ (a N * z N) / (N : ℝ) ^ (2 * d) := by
        gcongr
        exact hcorr N
      have h2 : (a N * z N) / (N : ℝ) ^ (2 * d)
          ≤ (C * (N : ℝ) ^ d * z N)
            / (N : ℝ) ^ (2 * d) := by
        gcongr ?_ / _
        exact mul_le_mul_of_nonneg_right (ha N) (hz0 N)
      have h3 : (C * (N : ℝ) ^ d * z N)
          / (N : ℝ) ^ (2 * d)
          = C * (z N / (N : ℝ) ^ d) := by
        rw [two_mul, pow_add]
        field_simp
      calc (corr N) ^ 2 / (N : ℝ) ^ (2 * d)
          ≤ (a N * z N) / (N : ℝ) ^ (2 * d) := h1
        _ ≤ (C * (N : ℝ) ^ d * z N)
            / (N : ℝ) ^ (2 * d) := h2
        _ = C * (z N / (N : ℝ) ^ d) := h3
  refine ⟨hsq, ?_⟩
  -- `corr/N^d → 0` via the square root of (i)
  have hcorrN : Tendsto (fun N : ℕ =>
      corr N / (N : ℝ) ^ d) atTop (nhds 0) := by
    have habs : Tendsto (fun N : ℕ =>
        |corr N / (N : ℝ) ^ d|) atTop (nhds 0) := by
      have hsqrt : Tendsto (fun N : ℕ =>
          Real.sqrt ((corr N) ^ 2 / (N : ℝ) ^ (2 * d)))
          atTop (nhds 0) := by
        have := (Real.continuous_sqrt.continuousAt
          (x := (0 : ℝ))).tendsto.comp hsq
        simpa only [Function.comp_def,
          Real.sqrt_zero] using this
      apply hsqrt.congr'
      filter_upwards [hNpos] with N hN
      rw [two_mul, pow_add, ← Real.sqrt_sq_eq_abs]
      congr 1
      field_simp
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simpa only [Real.norm_eq_abs] using habs
  -- assemble: `(P - N^d·vol·β∞)/N^d
  --   = vol·(β N - β∞) + corr N/N^d`
  have hfin : Tendsto (fun N : ℕ =>
      vol * (β N - βinf) + corr N / (N : ℝ) ^ d)
      atTop (nhds 0) := by
    have hb : Tendsto (fun N : ℕ =>
        vol * (β N - βinf)) atTop (nhds 0) := by
      have := (hβ.sub_const βinf).const_mul vol
      simpa using this
    have := hb.add hcorrN
    simpa using this
  apply hfin.congr'
  filter_upwards [hNpos] with N hN
  rw [hdec N]
  field_simp
  ring

end NCG
