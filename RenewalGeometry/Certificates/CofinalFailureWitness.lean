/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cofinal witnesses of failed sufficient certificates
  (failure branch of `thm:main-einstein-alternative`, `subsec:supp-failed-certificates`;
  emergent-spacetime manuscript)

The proof of the Einstein-limit-or-failed-certificate alternative extracts, from each failed
sufficient certificate, a *cofinal witness* along the realized sequence of records:

* a nonnegative residual which does not tend to zero has a subsequence bounded below by some
  `ε > 0` (`exists_subseq_residual_ge_of_not_tendsto`);
* an unbounded budget has a subsequence tending to infinity
  (`exists_subseq_tendsto_atTop_of_not_bddAbove`);
* a failed strictly positive lower margin has a subsequence tending to zero (below `1/(k+1)`)
  (`exists_subseq_margin_lt_of_not_eventually_ge`);
* failure of a uniform compactness tail (with individually tight, screen-antitone tails) supplies
  `ε > 0` and components of arbitrarily late records outside arbitrarily large screens
  (`exists_late_escape_of_not_uniformly_tight`);
* failure of a calibrated Cauchy comparison retains separated pairs of records along two
  increasing index sequences (`exists_separated_pairs_of_not_cauchy`).

`CertificateBank` packages finitely many certificates of each kind; `CertificateBank.alternative`
is the dichotomy: either every certificate passes, or one of them fails with its cofinal witness.
This is the quantifier content of the failure branch only; it does not encode the certification
procedure `(E1)–(E5)` on the actual records.
-/

open Filter Topology

namespace RenewalGeometry.CofinalWitness

/-- A residual that does not tend to zero stays above some `ε > 0` along a subsequence. -/
theorem exists_subseq_residual_ge_of_not_tendsto {r : ℕ → ℝ}
    (hr : ¬Tendsto r atTop (𝓝 0)) :
    ∃ ε > 0, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, ε ≤ |r (φ k)| := by
  rw [Metric.tendsto_atTop] at hr
  push Not at hr
  obtain ⟨ε, hε, hN⟩ := hr
  have hfreq : ∃ᶠ n in atTop, ε ≤ |r n| := by
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hn, hd⟩ := hN N
    exact ⟨n, hn, by simpa [Real.dist_eq] using hd⟩
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hfreq
  exact ⟨ε, hε, φ, hφ, hP⟩

/-- An unbounded budget tends to infinity along a subsequence. -/
theorem exists_subseq_tendsto_atTop_of_not_bddAbove {B : ℕ → ℝ}
    (hB : ¬BddAbove (Set.range B)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (B ∘ φ) atTop atTop := by
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop, (k : ℝ) ≤ B n := by
    intro k
    by_contra hcon
    rw [not_frequently, eventually_atTop] at hcon
    obtain ⟨N, hN⟩ := hcon
    apply hB
    refine ⟨max k (∑ i ∈ Finset.range N, |B i|), ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : N ≤ n
    · exact (le_of_lt (not_le.1 (hN n hn))).trans (le_max_left _ _)
    · refine le_trans (le_abs_self _) (le_trans ?_ (le_max_right _ _))
      exact Finset.single_le_sum (f := fun i => |B i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.2 (not_le.1 hn))
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_frequently hfreq
  exact ⟨φ, hφ, tendsto_atTop_mono hP tendsto_natCast_atTop_atTop⟩

/-- A failed strictly positive lower margin falls below `1/(k+1)` along a subsequence. -/
theorem exists_subseq_margin_lt_of_not_eventually_ge {μ : ℕ → ℝ}
    (hμ : ¬∃ c > 0, ∀ᶠ n in atTop, c ≤ μ n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, μ (φ k) < 1 / ((k : ℝ) + 1) := by
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop, μ n < 1 / ((k : ℝ) + 1) := by
    intro k
    by_contra hcon
    rw [not_frequently] at hcon
    exact hμ ⟨1 / ((k : ℝ) + 1), by positivity, hcon.mono fun n hn => not_lt.1 hn⟩
  exact extraction_forall_of_frequently hfreq

/-- Failure of a uniform compactness tail.  `τ n R` is the mass of record `n` outside the
declared screen of size `R`; each record is individually tight (`τ n R → 0` as `R → ∞`) and the
tails decrease as the screens grow.  If the tails are not uniformly small, then for some `ε > 0`
records arbitrarily late in the sequence have mass `> ε` outside arbitrarily large screens. -/
theorem exists_late_escape_of_not_uniformly_tight {τ : ℕ → ℕ → ℝ}
    (htight : ∀ n, Tendsto (τ n) atTop (𝓝 0)) (hanti : ∀ n, Antitone (τ n))
    (hfail : ¬∀ ε > 0, ∃ R, ∀ n, τ n R ≤ ε) :
    ∃ ε > 0, ∀ R N : ℕ, ∃ n ≥ N, ε < τ n R := by
  push Not at hfail
  obtain ⟨ε, hε, hR⟩ := hfail
  refine ⟨ε, hε, fun R N => ?_⟩
  -- a screen size beyond which the first `N` records are `ε`-tight
  have hfin : ∀ᶠ R' in atTop, ∀ m ∈ Finset.range N, τ m R' ≤ ε := by
    rw [Filter.eventually_all_finset]
    intro m _
    exact ((htight m).eventually (ge_mem_nhds hε)).mono fun _ h => h
  obtain ⟨R0, hR0⟩ := eventually_atTop.1 hfin
  obtain ⟨n, hn⟩ := hR (max R R0)
  refine ⟨n, ?_, lt_of_lt_of_le hn (hanti n (le_max_left _ _))⟩
  by_contra hlt
  push Not at hlt
  exact absurd (hR0 (max R R0) (le_max_right _ _) n (Finset.mem_range.2 hlt)) (not_le.2 hn)

/-- Failure of a calibrated Cauchy comparison retains separated pairs of records along two
increasing index sequences. -/
theorem exists_separated_pairs_of_not_cauchy {d : ℕ → ℕ → ℝ}
    (hd : ¬∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, d m n < ε) :
    ∃ ε > 0, ∃ φ ψ : ℕ → ℕ, StrictMono φ ∧ StrictMono ψ ∧ ∀ k, ε ≤ d (φ k) (ψ k) := by
  push Not at hd
  obtain ⟨ε, hε, hN⟩ := hd
  choose m hm n hn hmn using hN
  -- `g (k+1)` exceeds both indices chosen at stage `g k`
  let g : ℕ → ℕ := fun k => Nat.rec 0 (fun _ gk => max (m gk) (n gk) + 1) k
  have hg : ∀ k, g (k + 1) = max (m (g k)) (n (g k)) + 1 := fun k => rfl
  refine ⟨ε, hε, fun k => m (g k), fun k => n (g k), ?_, ?_, fun k => hmn (g k)⟩
  · refine strictMono_nat_of_lt_succ fun k => ?_
    have := hm (g (k + 1))
    rw [hg] at this ⊢
    omega
  · refine strictMono_nat_of_lt_succ fun k => ?_
    have := hn (g (k + 1))
    rw [hg] at this ⊢
    omega

/-- A finite bank of sufficient certificates of the five kinds of
`subsec:supp-failed-certificates`, indexed by finite types: residuals that must tend to zero,
budgets that must stay bounded, margins that must stay bounded below by a positive constant on a
cofinal tail, compactness tails that must be uniformly small, and calibrated comparisons that must
be Cauchy. -/
structure CertificateBank (ι₁ ι₂ ι₃ ι₄ ι₅ : Type*) where
  residual : ι₁ → ℕ → ℝ
  budget : ι₂ → ℕ → ℝ
  margin : ι₃ → ℕ → ℝ
  tail : ι₄ → ℕ → ℕ → ℝ
  tail_tight : ∀ i n, Tendsto (tail i n) atTop (𝓝 0)
  tail_antitone : ∀ i n, Antitone (tail i n)
  comparison : ι₅ → ℕ → ℕ → ℝ

namespace CertificateBank

variable {ι₁ ι₂ ι₃ ι₄ ι₅ : Type*}

/-- Every certificate of the bank passes. -/
def Passes (B : CertificateBank ι₁ ι₂ ι₃ ι₄ ι₅) : Prop :=
  (∀ i, Tendsto (B.residual i) atTop (𝓝 0)) ∧ (∀ i, BddAbove (Set.range (B.budget i))) ∧
    (∀ i, ∃ c > 0, ∀ᶠ n in atTop, c ≤ B.margin i n) ∧
    (∀ i, ∀ ε > 0, ∃ R, ∀ n, B.tail i n R ≤ ε) ∧
    (∀ i, ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, B.comparison i m n < ε)

/-- **Certificate alternative** (failure branch of `thm:main-einstein-alternative`): either every
certificate of the bank passes, or one certificate fails and carries its cofinal witness. -/
theorem alternative (B : CertificateBank ι₁ ι₂ ι₃ ι₄ ι₅) :
    B.Passes ∨
      (∃ i, ∃ ε > 0, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, ε ≤ |B.residual i (φ k)|) ∨
      (∃ i, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (B.budget i ∘ φ) atTop atTop) ∨
      (∃ i, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, B.margin i (φ k) < 1 / ((k : ℝ) + 1)) ∨
      (∃ i, ∃ ε > 0, ∀ R N : ℕ, ∃ n ≥ N, ε < B.tail i n R) ∨
      (∃ i, ∃ ε > 0, ∃ φ ψ : ℕ → ℕ, StrictMono φ ∧ StrictMono ψ ∧
        ∀ k, ε ≤ B.comparison i (φ k) (ψ k)) := by
  by_cases h1 : ∀ i, Tendsto (B.residual i) atTop (𝓝 0)
  · by_cases h2 : ∀ i, BddAbove (Set.range (B.budget i))
    · by_cases h3 : ∀ i, ∃ c > 0, ∀ᶠ n in atTop, c ≤ B.margin i n
      · by_cases h4 : ∀ i, ∀ ε > 0, ∃ R, ∀ n, B.tail i n R ≤ ε
        · by_cases h5 : ∀ i, ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, B.comparison i m n < ε
          · exact Or.inl ⟨h1, h2, h3, h4, h5⟩
          · push Not at h5
            obtain ⟨i, hi⟩ := h5
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, ?_⟩))))
            exact exists_separated_pairs_of_not_cauchy (by push Not; exact hi)
        · push Not at h4
          obtain ⟨i, hi⟩ := h4
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, ?_⟩))))
          exact exists_late_escape_of_not_uniformly_tight (B.tail_tight i) (B.tail_antitone i)
            (by push Not; exact hi)
      · push Not at h3
        obtain ⟨i, hi⟩ := h3
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨i, ?_⟩)))
        exact exists_subseq_margin_lt_of_not_eventually_ge (by push Not; exact hi)
    · push Not at h2
      obtain ⟨i, hi⟩ := h2
      exact Or.inr (Or.inr (Or.inl ⟨i, exists_subseq_tendsto_atTop_of_not_bddAbove hi⟩))
  · push Not at h1
    obtain ⟨i, hi⟩ := h1
    exact Or.inr (Or.inl ⟨i, exists_subseq_residual_ge_of_not_tendsto hi⟩)

end CertificateBank

end RenewalGeometry.CofinalWitness
