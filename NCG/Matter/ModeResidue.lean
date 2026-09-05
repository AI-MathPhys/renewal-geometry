/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Mode-resolved residue test and trace-singlet exclusion
  (`prop:mode-resolved-residue-test-sm`,
   `thm:trace-singlet-exclusion`, SM_emergence)

* `spectral_power` — for a semisimple spectral decomposition
  `L = Σ_k λ_k P_k` with orthogonal idempotent projectors,
  `Lⁿ = Σ_k λ_kⁿ P_k`;
* `mode_resolved_residue` — hence the contribution of the mode `j`
  to `u·Lⁿ·v` is exactly `λ_jⁿ·(u P_j v)`: an eigenvalue is not a
  physical channel prediction unless its left–right residue
  `u P_j v` is nonzero (Jordan blocks add the standard polynomial
  factors, declared);
* `trace_singlet_exclusion` — a centred source that vanishes
  pointwise by conservation (`Tr R = 𝔼(Tr R | context)`) has zero
  connected correlations, so its Green–Kubo susceptibility is
  `K₁ = 0`.
-/

namespace NCG

open Matrix

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

/-- Semisimple spectral calculus: if `L = Σ_k λ_k P_k` with
mutually orthogonal idempotent projectors, then
`Lⁿ = Σ_k λ_kⁿ P_k` for `n ≥ 1`. -/
theorem spectral_power (P : ι → Matrix d d ℂ)
    (lam : ι → ℂ)
    (hortho : ∀ k l, k ≠ l → P k * P l = 0)
    (hidem : ∀ k, P k * P k = P k) :
    ∀ n, 1 ≤ n →
      (∑ k, lam k • P k) ^ n = ∑ k, (lam k ^ n) • P k := by
  classical
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hn with h1 | h1
      · rw [← h1]
        simp
      · have hn' : 1 ≤ n := by omega
        rw [pow_succ, ih hn', Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_eq_single k]
        · rw [smul_mul_smul_comm, hidem k, ← pow_succ]
        · intro l _ hlk
          rw [smul_mul_smul_comm, hortho k l (Ne.symm hlk),
            smul_zero]
        · intro hk
          exact absurd (Finset.mem_univ k) hk

/-- `prop:mode-resolved-residue-test-sm`: the contribution of an
isolated semisimple mode to `u·Lⁿ·v` is `λ_jⁿ·(u P_j v)` — the
mode enters only through its left–right residue. -/
theorem mode_resolved_residue
    (P : ι → Matrix d d ℂ) (lam : ι → ℂ)
    (hortho : ∀ k l, k ≠ l → P k * P l = 0)
    (hidem : ∀ k, P k * P k = P k)
    (u v : d → ℂ) (n : ℕ) (hn : 1 ≤ n) :
    u ⬝ᵥ ((∑ k, lam k • P k) ^ n).mulVec v
      = ∑ k, lam k ^ n * (u ⬝ᵥ (P k).mulVec v) := by
  rw [spectral_power P lam hortho hidem n hn, Matrix.sum_mulVec,
    dotProduct_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- `thm:trace-singlet-exclusion`: a centred trace-singlet source
that vanishes pointwise by conservation has identically zero
connected correlations, so its Green–Kubo susceptibility is
`K₁ = 0` (stated for arbitrary time kernels `w`). -/
theorem trace_singlet_exclusion {Ω : Type*} [Fintype Ω]
    (trR ctxE : Ω → ℝ) (hcons : ∀ ω, trR ω = ctxE ω)
    (w : ℕ → Ω → Ω → ℝ) (N : ℕ) :
    ∑ t ∈ Finset.range N, ∑ ω, ∑ ω', w t ω ω'
        * (trR ω - ctxE ω) * (trR ω' - ctxE ω') = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro ω _
  apply Finset.sum_eq_zero
  intro ω' _
  rw [hcons ω, sub_self, mul_zero, zero_mul]

end NCG
