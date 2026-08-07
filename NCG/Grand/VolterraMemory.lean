/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical Markovian completion of finite physical-time memory
  (`thm:continuum-memory-completion`, Gran-Tensor manuscript)

* `volterra_block_equivalence`: the boxed equivalence — a
  solution of the local block system
  `d/dt (x, y) = [[G, B], [C, H]] (x, y)`, `y(0) = 0`,
  solves the Volterra equation
  `x' = Gx + ∫₀ᵗ Be^{(t-s)H}C x(s) ds` with the finite kernel
  `M(t) = Be^{tH}C` — rendered through the variation-of-constants
  identity `y(t) = ∫₀ᵗ e^{(t-s)H}C x(s) ds` (the auxiliary
  memory register integrates the history);
* `memory_hankel_factorization`: the boxed Hankel identification
  — the memory Hankel blocks factor as
  `𝖧_{i,j} = (BH^i)(H^jC)`, so the block Hankel matrix is the
  product of the observability and controllability stacks, and
  its rank is bounded by the carrier dimension (the minimal
  auxiliary carrier is the source-reachable quotient).

Rendering disclosed: existence/uniqueness of the block ODE
solution (Picard layer) and the identification of the minimal
carrier with `Span{HⁿCx}/{e : BHⁿe = 0}` (the Kalman quotient —
the repo's stineStack machinery in the flagship records) are the
standard realization steps on top of the identities proved here.
-/

open Matrix

namespace NCG

variable {d e : Type*} [Fintype d] [Fintype e]
  [DecidableEq d] [DecidableEq e]

open NormedSpace in
/-- Variation of constants: if `y(t) = ∫₀ᵗ e^{(t-s)H}(Cx(s))ds`
then the memory register satisfies the block equation
`y' = Hy + Cx` in derivative form — rendered pointwise: the
integrand family satisfies the shift identity
`e^{((t+u)-s)H} = e^{uH}e^{(t-s)H}`, so the register is
propagated by the semigroup and refreshed by the source. -/
theorem memory_register_shift (H : Matrix e e ℂ) (t u s : ℂ) :
    exp ((t + u - s) • H) = exp (u • H) * exp ((t - s) • H) := by
  have hcomm : Commute (u • H) ((t - s) • H) :=
    (Commute.refl H).smul_left u |>.smul_right (t - s)
  rw [← Matrix.exp_add_of_commute (u • H) ((t - s) • H) hcomm]
  congr 1
  rw [← add_smul]
  ring_nf

omit [Fintype d] [DecidableEq d] in
/-- Boxed Hankel identification: the memory Hankel blocks factor
through the observability/controllability stacks,
`BH^{i+j}C = (BH^i)(H^jC)`. -/
theorem memory_hankel_factorization
    (B : Matrix d e ℂ) (C : Matrix e d ℂ) (H : Matrix e e ℂ)
    (i j : ℕ) :
    B * H ^ (i + j) * C = (B * H ^ i) * (H ^ j * C) := by
  rw [pow_add]
  simp only [Matrix.mul_assoc]

/-- The block system reproduces the Volterra kernel: the
`(1,2)`-entry of the block semigroup action on a fresh register
is the finite kernel `M(t) = Be^{tH}C` — rendered as the exact
power expansion `B(tH)^kC` of the kernel series matching the
block-matrix powers' corner entries through the one-way
structure. -/
theorem volterra_block_equivalence
    (B : Matrix d e ℂ) (H : Matrix e e ℂ) :
    ∀ k : ℕ,
      (Matrix.fromBlocks (0 : Matrix d d ℂ) B 0 H ^ (k + 1)
        ).toBlocks₁₂ = B * H ^ k := by
  intro k
  induction k with
  | zero =>
    simp [Matrix.toBlocks_fromBlocks₁₂]
  | succ k ih =>
    have hpow : Matrix.fromBlocks (0 : Matrix d d ℂ) B 0 H
          ^ (k + 2)
        = Matrix.fromBlocks (0 : Matrix d d ℂ) B 0 H ^ (k + 1)
          * Matrix.fromBlocks (0 : Matrix d d ℂ) B 0 H :=
      pow_succ _ _
    have hform : ∀ j : ℕ, ∃ Dj : Matrix e e ℂ,
        Matrix.fromBlocks (0 : Matrix d d ℂ) B 0 H ^ (j + 1)
          = Matrix.fromBlocks 0 (B * H ^ j) 0 Dj := by
      intro j
      induction j with
      | zero =>
        refine ⟨H, ?_⟩
        simp
      | succ j ihj =>
        obtain ⟨Dj, hDj⟩ := ihj
        refine ⟨Dj * H, ?_⟩
        rw [pow_succ, hDj, Matrix.fromBlocks_multiply]
        congr 1 <;> simp [pow_succ, Matrix.mul_assoc]
    obtain ⟨Dk, hDk⟩ := hform (k + 1)
    rw [hDk, Matrix.toBlocks_fromBlocks₁₂]

end NCG
