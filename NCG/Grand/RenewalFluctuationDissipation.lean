import NCG.Grand.FluctuationObservability

/-! # two-sided renewal fluctuation--dissipation -/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma psd_range_sum
    {A : ℕ → Matrix n n ℂ} (N : ℕ)
    (hA : ∀ k < N, (A k).PosSemidef) :
    (∑ k ∈ Finset.range N, A k).PosSemidef := by
  classical
  induction N with
  | zero => simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix n n ℂ).PosSemidef)
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact (ih fun k hk => hA k (Nat.lt.step hk)).add
        (hA N (Nat.lt_succ_self N))

/-- `thm:renewal-fluctuation-dissipation`, two-sided noncollapse clause at
every truncation.  The endpoint term tends to zero under the manuscript's
strict `H`-contraction, so these exact finite inequalities yield
`d₋ H ⪯ Σ ⪯ d₊ H` for the norm-convergent Lyapunov series. -/
theorem renewal_fluctuation_dissipation_two_sided
    (H K Q : Matrix n n ℂ) (dminus dplus : ℝ)
    (hH : H.PosSemidef)
    (hD : (H - Kᴴ * H * K).PosSemidef)
    (hminus : (Q - (dminus : ℂ) • (H - Kᴴ * H * K)).PosSemidef)
    (hplus : ((dplus : ℂ) • (H - Kᴴ * H * K) - Q).PosSemidef) :
    ∀ N : ℕ,
      ((∑ k ∈ Finset.range N, Kᴴ ^ k * Q * K ^ k)
          - (dminus : ℂ) • (H - Kᴴ ^ N * H * K ^ N)).PosSemidef
      ∧ ((dplus : ℂ) • (H - Kᴴ ^ N * H * K ^ N)
          - (∑ k ∈ Finset.range N, Kᴴ ^ k * Q * K ^ k)).PosSemidef := by
  intro N
  let D := H - Kᴴ * H * K
  have htel : (∑ k ∈ Finset.range N, Kᴴ ^ k * D * K ^ k)
      = H - Kᴴ ^ N * H * K ^ N := by
    have hcore := renewal_complete_observability K H (0 : Matrix n n ℂ)
      0 (by positivity) (by norm_num) hH (by simpa [D] using hD)
    simpa [D] using (hcore.2.2 N).1
  constructor
  · have hs := psd_range_sum N (A := fun k =>
        Kᴴ ^ k * (Q - (dminus : ℂ) • D) * K ^ k)
        (fun k _ => by
          simpa [Matrix.conjTranspose_pow, D] using
            hminus.conjTranspose_mul_mul_same (K ^ k))
    rw [← htel]
    convert hs using 1 <;>
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, Finset.sum_sub_distrib, Finset.smul_sum]
  · have hs := psd_range_sum N (A := fun k =>
        Kᴴ ^ k * ((dplus : ℂ) • D - Q) * K ^ k)
        (fun k _ => by
          simpa [Matrix.conjTranspose_pow, D] using
            hplus.conjTranspose_mul_mul_same (K ^ k))
    rw [← htel]
    convert hs using 1 <;>
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, Finset.sum_sub_distrib, Finset.smul_sum]

end NCG
