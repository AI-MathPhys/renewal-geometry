/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Summable corrections of states, mixed Grams, and metric
  arrows
  (`thm:summable-state-correction`,
  `thm:summable-mixed-Gram-correction`, and
  `thm:summable-metric-correction`, Gran-Tensor manuscript)

* `summable_defect_limit` (master): a cutoff family with
  summable one-step defects has a canonical limit with the
  boxed defect-tail estimate `‖L - f m‖ ≤ Σ_{n≥m} δ_n`.

* The three records are the master applied to the
  restricted-state family `ω_n∘ι_{n/m}`, the compressed
  mixed-Gram family `J_{n/m}ᴴ𝔾_nJ_{n/m}`, and the
  transport-weighted metric family `Z_{n/m}ᴴG_nZ_{n/m}`
  (whose one-step defects are exactly the weighted errors
  `‖Z_{n/m}‖²·‖E_n‖`).  Preservation of closed convex
  constraints (positivity, normalization, complete
  positivity) and the exact-compatibility identities are the
  manuscript's closure bookkeeping over these limits.
-/

open Matrix
open scoped Norms.L2Operator

namespace NCG

/-- Master summable-correction limit with the boxed
defect-tail estimate. -/
theorem summable_defect_limit {V : Type*}
    [NormedAddCommGroup V] [CompleteSpace V]
    (f : ℕ → V) (d : ℕ → ℝ) (hd : Summable d)
    (hdef : ∀ n, ‖f (n + 1) - f n‖ ≤ d n) :
    ∃ L : V, Filter.Tendsto f Filter.atTop (nhds L)
      ∧ ∀ m : ℕ, ‖L - f m‖ ≤ ∑' n : ℕ, d (n + m) := by
  have hsum0 : Summable fun n : ℕ => f (n + 1) - f n :=
    Summable.of_norm_bounded hd hdef
  have hnormtail : ∀ m : ℕ,
      Summable fun n : ℕ => ‖f (n + m + 1) - f (n + m)‖ := by
    intro m
    apply Summable.of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => hdef (n + m))
    exact (summable_nat_add_iff m).mpr hd
  refine ⟨f 0 + ∑' n : ℕ, (f (n + 1) - f n), ?_, ?_⟩
  · have hpart : ∀ m : ℕ,
        f m = f 0 + ∑ n ∈ Finset.range m,
          (f (n + 1) - f n) := by
      intro m
      rw [Finset.sum_range_sub]
      abel
    have ht := Filter.Tendsto.const_add (f 0)
      hsum0.hasSum.tendsto_sum_nat
    exact ht.congr (fun m => (hpart m).symm)
  · intro m
    have hsplit := hsum0.sum_add_tsum_nat_add m
    have hpart : ∑ n ∈ Finset.range m,
        (f (n + 1) - f n) = f m - f 0 :=
      Finset.sum_range_sub _ _
    have htel : f 0 + (∑' n : ℕ, (f (n + 1) - f n)) - f m
        = ∑' n : ℕ, (f (n + m + 1) - f (n + m)) := by
      rw [← hsplit, hpart]
      abel
    rw [htel]
    calc ‖∑' n : ℕ, (f (n + m + 1) - f (n + m))‖
        ≤ ∑' n : ℕ, ‖f (n + m + 1) - f (n + m)‖ :=
          norm_tsum_le_tsum_norm (hnormtail m)
      _ ≤ ∑' n : ℕ, d (n + m) :=
          (hnormtail m).tsum_le_tsum
            (fun n => hdef (n + m))
            ((summable_nat_add_iff m).mpr hd)

/-- `thm:summable-state-correction` (canonical corrected
family from summable restriction defects). -/
theorem summable_state_correction {V : Type*}
    [NormedAddCommGroup V] [CompleteSpace V]
    (ω : ℕ → V) (δ : ℕ → ℝ) (hδ : Summable δ)
    (hdef : ∀ n, ‖ω (n + 1) - ω n‖ ≤ δ n) :
    ∃ ωhat : V,
      Filter.Tendsto ω Filter.atTop (nhds ωhat)
      ∧ ∀ m : ℕ, ‖ωhat - ω m‖ ≤ ∑' n : ℕ, δ (n + m) :=
  summable_defect_limit ω δ hδ hdef

/-- `thm:summable-mixed-Gram-correction` (the compressed
mixed-Gram family, in the matrix space). -/
theorem summable_mixed_gram_correction {E : Type*}
    [Fintype E] [DecidableEq E]
    (G : ℕ → Matrix E E ℂ) (δ : ℕ → ℝ) (hδ : Summable δ)
    (hdef : ∀ n, ‖G (n + 1) - G n‖ ≤ δ n) :
    ∃ Ghat : Matrix E E ℂ,
      Filter.Tendsto G Filter.atTop (nhds Ghat)
      ∧ ∀ m : ℕ, ‖Ghat - G m‖ ≤ ∑' n : ℕ, δ (n + m) :=
  summable_defect_limit G δ hδ hdef

/-- `thm:summable-metric-correction` (transport-weighted
metric arrows: the one-step defects carry the boxed weights
`‖Z_{n/m}‖²·‖E_n‖`). -/
theorem summable_metric_correction {E : Type*}
    [Fintype E] [DecidableEq E]
    (G : ℕ → Matrix E E ℂ) (w err : ℕ → ℝ)
    (hw : Summable fun n => w n * err n)
    (hdef : ∀ n, ‖G (n + 1) - G n‖ ≤ w n * err n) :
    ∃ Ghat : Matrix E E ℂ,
      Filter.Tendsto G Filter.atTop (nhds Ghat)
      ∧ ∀ m : ℕ,
          ‖Ghat - G m‖ ≤ ∑' n : ℕ, w (n + m) * err (n + m) :=
  summable_defect_limit G (fun n => w n * err n) hw hdef

end NCG
