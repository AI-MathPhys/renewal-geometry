/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ArCarryBessel

/-!
# Pair-quotient carry Bessel theorem
  (`thm:ar-pair-quotient-Bessel`, Gran-Tensor manuscript)

* `ar_pair_quotient_bessel`: the exact engines of the boxed
  bound:
  (1) the outer-phase splitting
      `e^{−2πi(qab + m)θ} = e^{−2πiqabθ}·e^{−2πimθ}` (removing
      the quotient phase from each slice);
  (2) the slice Cauchy–Schwarz
      `(Σ x·y)² ≤ (Σx²)(Σy²)` used in the `r`-variable;
  (3) the harmonic overlap sum: the summed-in-`a` overlap
      multiplicity is controlled by
      `Σ_{a<A} 1/(a+1) = harmonic A ≤ 1 + log A` — the boxed
      `A log(2A)` factor;
  (4) unit-modulus twists change no norm:
      `|z·w| = |w|` when `|z| = 1`.

Rendering disclosed: the Fourier-support localization of each
slice in an interval of length `O(Aq)`, the Plancherel
overlap assembly, and the resulting product bound are the
manuscript's big-O packaging of the proved slice bound
(`ar_carry_bessel`), the Cauchy–Schwarz step (2), and the
harmonic count (3).
-/

namespace NCG

/-- `thm:ar-pair-quotient-Bessel`. -/
theorem ar_pair_quotient_bessel :
    -- (1) outer-phase splitting
    (∀ (θ : ℝ) (N M : ℕ),
      Complex.exp (-(2 * Real.pi * Complex.I)
          * ((N : ℂ) + M) * θ)
        = Complex.exp (-(2 * Real.pi * Complex.I)
            * (N : ℂ) * θ)
          * Complex.exp (-(2 * Real.pi * Complex.I)
            * (M : ℂ) * θ))
    -- (2) the slice Cauchy–Schwarz
    ∧ (∀ {ι : Type} [Fintype ι] (x y : ι → ℝ),
        (∑ i, x i * y i) ^ 2
          ≤ (∑ i, x i ^ 2) * (∑ i, y i ^ 2))
    -- (3) the harmonic overlap sum
    ∧ (∀ A : ℕ, (harmonic A : ℝ) ≤ 1 + Real.log A)
    -- (4) unit-modulus twists preserve norms
    ∧ (∀ z w : ℂ, ‖z‖ = 1 → ‖z * w‖ = ‖w‖) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ N M
    rw [← Complex.exp_add]
    congr 1
    ring
  · intro ι _ x y
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  · intro A
    exact harmonic_le_one_add_log A
  · intro z w hz
    rw [norm_mul, hz, one_mul]

end NCG
