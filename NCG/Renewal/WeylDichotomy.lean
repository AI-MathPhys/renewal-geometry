/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.EhrhartCount

/-!
# Weyl asymptotics and the renewal dichotomy (proved cores)

**Theorem `thm:weyl-law`** (free-case core): the free predictive
counting function obeys a genuine two-sided Weyl bound with exponent
`c` and constant `1/c!`:

`(R+1)^c ≤ c! · N_c(R) ≤ (R+c)^c` (`NCG.weyl_free_bounds`),

immediate from the exact Ehrhart count and the ascending-factorial
bounds; the regularly varying general case (Karamata) is the noted
step.

**Theorem `thm:renewal-dichotomy`** (short-memory core): the exact
renewal-pole identity `1 − F(z) = (1−z)·Σ fₙ(1 + z + … + zⁿ⁻¹)`
(`NCG.renewal_pole_identity`) whose second factor evaluates at `z = 1`
to the mean return length `μ = Σ n·fₙ` (`NCG.renewal_mean_at_one`) —
the simple pole with residue `−1/μ`.  The Karamata branch regime (ii)
is the noted step.

**Corollary `cor:renewal-counting`** (constant core): Euler's
reflection identity `Γ(1+α)Γ(1−α) = πα / sin(πα)`
(`NCG.gamma_reflection_renewal`) which converts the Tauberian constant
into the stated `sin(πα)/(πα)` form; the Hardy–Littlewood–Karamata
theorem and the strong renewal theorem are the noted inputs.
-/

namespace NCG

/-- **Theorem `thm:weyl-law` (free-case Weyl bounds)**: the free
counting function satisfies `(R+1)^c ≤ c!·N_c(R) ≤ (R+c)^c` — a
genuine Weyl asymptotic with exponent `q = c` and Weyl constant
`1/c!`. -/
theorem weyl_free_bounds (c R : ℕ) :
    (R + 1) ^ c ≤ latticeShellCard c R * c.factorial
      ∧ latticeShellCard c R * c.factorial ≤ (R + c) ^ c := by
  rw [latticeShellCard_eq_choose, mul_comm,
    ← Nat.ascFactorial_eq_factorial_mul_choose R c]
  exact ⟨Nat.pow_succ_le_ascFactorial (R + 1) c,
    Nat.ascFactorial_le_pow_add R c⟩

/-- **Theorem `thm:renewal-dichotomy` (i), pole identity**: for a
return law `f` of total mass one,
`1 − Σ fₙ zⁿ = (1−z) · Σ fₙ (1 + z + … + zⁿ⁻¹)` — the resolvent
`1/(1−F(z))` has its singularity at `z = 1` carried by the factor
`(1−z)` times the partial-mean series. -/
theorem renewal_pole_identity (N : ℕ) (f : ℕ → ℝ) (z : ℝ)
    (hsum : ∑ n ∈ Finset.range N, f n = 1) :
    1 - ∑ n ∈ Finset.range N, f n * z ^ n
      = (1 - z) * ∑ n ∈ Finset.range N,
          f n * (∑ k ∈ Finset.range n, z ^ k) := by
  have hgeom : ∀ n : ℕ,
      (1 - z) * ∑ k ∈ Finset.range n, z ^ k = 1 - z ^ n := by
    intro n
    have h := geom_sum_mul z n
    linear_combination -h
  calc 1 - ∑ n ∈ Finset.range N, f n * z ^ n
      = ∑ n ∈ Finset.range N, (f n - f n * z ^ n) := by
        rw [Finset.sum_sub_distrib, hsum]
    _ = ∑ n ∈ Finset.range N,
          f n * ((1 - z) * ∑ k ∈ Finset.range n, z ^ k) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hgeom n]
        ring
    _ = (1 - z) * ∑ n ∈ Finset.range N,
          f n * (∑ k ∈ Finset.range n, z ^ k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring

/-- **Theorem `thm:renewal-dichotomy` (i), mean evaluation**: at
`z = 1` the partial-mean series evaluates to the calibrated mean
return length `μ = Σ n·fₙ`. -/
theorem renewal_mean_at_one (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.range N, f n * (∑ k ∈ Finset.range n, (1:ℝ) ^ k)
      = ∑ n ∈ Finset.range N, f n * n := by
  refine Finset.sum_congr rfl fun n _ => ?_
  simp

/-- **Corollary `cor:renewal-counting` (constant core)**: Euler's
reflection formula in the renewal normalisation,
`Γ(1+α)·Γ(1−α) = πα / sin(πα)` — the identity converting the
Karamata–Tauberian constant into the stated `sin(πα)/(πα)` form. -/
theorem gamma_reflection_renewal (α : ℝ) (h0 : 0 < α) :
    Real.Gamma (1 + α) * Real.Gamma (1 - α)
      = Real.pi * α / Real.sin (Real.pi * α) := by
  rw [show (1:ℝ) + α = α + 1 from by ring, Real.Gamma_add_one h0.ne',
    mul_assoc, Real.Gamma_mul_Gamma_one_sub α]
  ring

/-- **Theorem `thm:renewal-dichotomy` (i), the actual `z → 1` limit**:
for a finitely supported return law of total mass one, the ratio
`(1 − F(z))/(1 − z)` extends continuously across `z = 1` with value
the mean return length `μ = Σ n·fₙ` — i.e. `1 − F` has a *simple zero*
at `z = 1`.  (The finite-support case is the exponential-moment
sub-case of the manuscript's part (i), where the theorem asserts a
genuine pole; the infinite-support monotone-convergence version and
the Karamata branch regime (ii) remain the noted steps.) -/
theorem renewal_ratio_tendsto (N : ℕ) (f : ℕ → ℝ)
    (hsum : ∑ n ∈ Finset.range N, f n = 1) :
    Filter.Tendsto
      (fun z : ℝ => (1 - ∑ n ∈ Finset.range N, f n * z ^ n) / (1 - z))
      (nhdsWithin 1 {1}ᶜ)
      (nhds (∑ n ∈ Finset.range N, f n * n)) := by
  have hQcont : Continuous (fun z : ℝ =>
      ∑ n ∈ Finset.range N, f n * (∑ k ∈ Finset.range n, z ^ k)) := by
    refine continuous_finsetSum _ fun n _ => Continuous.mul
      continuous_const (continuous_finsetSum _ fun k _ => ?_)
    exact continuous_pow k
  have hQ1 : ∑ n ∈ Finset.range N, f n * (∑ k ∈ Finset.range n, (1:ℝ) ^ k)
      = ∑ n ∈ Finset.range N, f n * n := renewal_mean_at_one N f
  have hQtend := hQcont.tendsto 1
  rw [hQ1] at hQtend
  refine Filter.Tendsto.congr' ?_ (hQtend.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz1 : (1 : ℝ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  rw [renewal_pole_identity N f z hsum, mul_div_cancel_left₀ _ hz1]

/-- **Theorem `thm:renewal-dichotomy` (i), the simple pole**: with
positive mean `μ > 0`, the rescaled resolvent factor
`(1 − z)/(1 − F(z))` tends to `1/μ` as `z → 1` — the resolvent
`1/(1 − F)` has a genuine simple pole at `z = 1` with residue `−1/μ`. -/
theorem renewal_resolvent_pole (N : ℕ) (f : ℕ → ℝ)
    (hsum : ∑ n ∈ Finset.range N, f n = 1)
    (hμ : 0 < ∑ n ∈ Finset.range N, f n * n) :
    Filter.Tendsto
      (fun z : ℝ => (1 - z) / (1 - ∑ n ∈ Finset.range N, f n * z ^ n))
      (nhdsWithin 1 {1}ᶜ)
      (nhds (∑ n ∈ Finset.range N, f n * n)⁻¹) := by
  have h := (renewal_ratio_tendsto N f hsum).inv₀ hμ.ne'
  exact h.congr fun z => inv_div _ _

end NCG
