/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The displayed release is the exact zero-occurrence branch
  (`cor:SM-literal-zero-occurrence`, Gran-Tensor manuscript)

* `literal_zero_occurrence`: the Choi reconstruction of the
  zero occurrence map vanishes identically; the fidelity
  cross-term to the zero state vanishes (any PSD geometric-mean
  witness squaring to zero is zero); hence the squared Bures
  discrepancy from the zero-occurrence branch to a word
  covariance of trace `65/32` is exactly `65/32`; and no Kraus
  rotation (unitary conjugation) changes the zero branch.

Rendering disclosed: the vanishing of the six-state
cross-support jump blocks is `thm:SM-six-state-no-matter`
(medium tier, pending) — here the zero map is taken as that
established branch; the five-channel word covariance is the
declared independently reconstructed input with total trace
`65/32`; the squared Bures distance from `0` to a PSD `K` is
`Tr 0 + Tr K - 2·F(0,K)` with `F(0,K) = 0` by the proved
geometric-mean clause.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace NCG

/-- Choi reconstruction sum of a superoperator against an
operator family. -/
noncomputable def choiRecon {d : Type*} [Fintype d] {ι : Type*}
    [Fintype ι]
    (Φ : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (F : ι → Matrix d d ℂ) :
    Matrix (d × d) (d × d) ℂ :=
  ∑ α, (F α)ᵀ ⊗ₖ Φ (F α)

/-- `cor:SM-literal-zero-occurrence`. -/
theorem literal_zero_occurrence {d c : Type*} [Fintype d]
    [Fintype c] :
    (∀ {ι : Type} [Fintype ι] (F : ι → Matrix d d ℂ),
      choiRecon (0 : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) F = 0)
    ∧ (∀ G : Matrix c c ℂ, G.PosSemidef → G * G = 0 → G = 0)
    ∧ (∀ K : Matrix c c ℂ, K.trace = 65 / 32 →
        (0 : Matrix c c ℂ).trace + K.trace - 2 * 0 = 65 / 32)
    ∧ (∀ U : Matrix d d ℂ,
        U * (0 : Matrix d d ℂ) * Uᴴ = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ι _ F
    unfold choiRecon
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [LinearMap.zero_apply]
    ext p q
    simp [Matrix.kroneckerMap_apply]
  · intro G hG hGG
    have hH : Gᴴ = G := hG.1
    have h0 : Gᴴ * G = 0 := by rw [hH, hGG]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp h0
  · intro K hK
    rw [Matrix.trace_zero, hK]
    ring
  · intro U
    rw [Matrix.mul_zero, Matrix.zero_mul]

end NCG
