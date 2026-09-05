/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Metric profile alternative
  (`thm:metric-profile-alternative`,
  Gran-Tensor manuscript)

* `metric_profile_alternative`: every nonnegative scale
  sequence admits a subsequence realizing exactly one of
  the branches (R1)–(R3): escape to infinity
  (`α_n → ∞`), collapse (`α_n → 0`, the collapsing-scale
  witness), or a stable positive limit — the scalar core of
  the cofinal-subnet classification.

The eigenvector/Grassmannian layers ((R3) collapsing
eigenvectors, (R4) source-direction loss/acquisition via
the source Pythagoras theorem, (R5) diamond witnesses via
`NCG.renormalization_cocycle` (iv), (R6) residual
Stiefel/affine moduli) attach the displayed witnesses to
each branch and are the manuscript's compactness
bookkeeping over finite Grassmannians; the scalar
trichotomy proved here drives the subnet extraction.
-/

open Filter

namespace NCG

/-- `thm:metric-profile-alternative` (scalar trichotomy). -/
theorem metric_profile_alternative (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (Tendsto (fun n => a (φ n)) atTop atTop
        ∨ Tendsto (fun n => a (φ n)) atTop (nhds 0)
        ∨ ∃ l > 0,
            Tendsto (fun n => a (φ n)) atTop (nhds l)) := by
  by_cases hb : ∃ M : ℝ, ∀ n, a n ≤ M
  · -- bounded: Bolzano–Weierstrass
    obtain ⟨M, hM⟩ := hb
    have hbdd : ∀ n, a n ∈ Set.Icc (0 : ℝ) M :=
      fun n => ⟨ha n, hM n⟩
    obtain ⟨l, _, φ, hφ, hlim⟩ :=
      tendsto_subseq_of_bounded
        (Metric.isBounded_Icc (0 : ℝ) M) hbdd
    have hl0 : 0 ≤ l :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        (Eventually.of_forall fun n => ha (φ n))
    rcases eq_or_lt_of_le hl0 with hl | hl
    · exact ⟨φ, hφ, Or.inr (Or.inl (hl ▸ hlim))⟩
    · exact ⟨φ, hφ, Or.inr (Or.inr ⟨l, hl, hlim⟩)⟩
  · -- unbounded: escape subsequence
    push Not at hb
    have hstep : ∀ (M : ℝ) (N : ℕ),
        ∃ n, N ≤ n ∧ M < a n := by
      intro M N
      by_contra hno
      push Not at hno
      obtain ⟨n, hn⟩ := hb (max M
        ((Finset.range (N + 1)).sup'
          (by simp) fun k => a k))
      rcases Nat.lt_or_ge n N with h | h
      · have hle : a n ≤ (Finset.range (N + 1)).sup'
            (by simp) (fun k => a k) :=
          Finset.le_sup' _
            (Finset.mem_range.mpr (by omega))
        have h2 := lt_of_le_of_lt (le_max_right M _) hn
        linarith
      · exact absurd (hno n h)
          (not_le.mpr
            (lt_of_le_of_lt (le_max_left _ _) hn))
    choose g hg1 hg2 using hstep
    let φ : ℕ → ℕ := fun k =>
      Nat.rec (g 0 0)
        (fun k ih => g ((k + 1 : ℕ) : ℝ) (ih + 1)) k
    have hφsucc : ∀ k,
        φ (k + 1) = g ((k + 1 : ℕ) : ℝ) (φ k + 1) :=
      fun k => rfl
    have hφmono : StrictMono φ := by
      apply strictMono_nat_of_lt_succ
      intro k
      have h := hg1 ((k + 1 : ℕ) : ℝ) (φ k + 1)
      rw [hφsucc k]
      omega
    have hval : ∀ k : ℕ, (k : ℝ) < a (φ k) := by
      intro k
      cases k with
      | zero =>
        have h0 : φ 0 = g 0 0 := rfl
        rw [h0]
        simpa using hg2 0 0
      | succ k =>
        have h := hg2 ((k + 1 : ℕ) : ℝ) (φ k + 1)
        rw [hφsucc k]
        exact_mod_cast h
    refine ⟨φ, hφmono, Or.inl ?_⟩
    exact tendsto_atTop_mono (fun k => (hval k).le)
      tendsto_natCast_atTop_atTop

end NCG
