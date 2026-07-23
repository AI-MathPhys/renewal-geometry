/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Classical reduction of the anti-renewal dual

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `thm:classical-reverse` — on the diagonal algebra the KMS/Petz
  anti-renewal dual is the stationary reverse Markov kernel
  `p♯_{ij} = π_j p_{ji} / π_i`: row stochastic, `π`-preserving, and
  equal to `p` exactly at classical detailed balance;
* `thm:path-reversal-tautology` — the stationary forward path weight
  equals the reversed path weight under the reverse kernel,
  `π_{i₀} ∏ p_{i_{k-1} i_k} = π_{i_m} ∏ p♯_{i_k i_{k-1}}`, for
  every path — the canonical path-reversal identity.
-/

namespace NCG.Upstream

variable {n : ℕ} (p : Fin n → Fin n → ℝ) (π : Fin n → ℝ)

/-- **Theorem `thm:classical-reverse` (the reverse kernel)**:
`p♯_{ij} = π_j p_{ji} / π_i`. -/
noncomputable def reverseKernel : Fin n → Fin n → ℝ :=
  fun i j => π j * p j i / π i

/-- The Heisenberg action of a kernel on observables,
`(Φ_P f)_i = ∑_j p_{ij} f_j`. -/
def markovHeis (f : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, p i j * f j

/-- The commutative KMS/Petz dual: `Γ_π(f) = π f` pointwise, the
predual acts by `(μ P)_j = ∑_i μ_i p_{ij}`, and
`Φ♯ = Γ_π⁻¹ ∘ Φ_* ∘ Γ_π`. -/
noncomputable def classicalDual (f : Fin n → ℝ) : Fin n → ℝ :=
  fun j => (∑ i, (π i * f i) * p i j) / π j

/-- **Theorem `thm:classical-reverse` (identification)**: the
commutative KMS/Petz dual is exactly the reverse-kernel Markov
map. -/
theorem classicalDual_eq_reverse (f : Fin n → ℝ) :
    classicalDual p π f = markovHeis (reverseKernel p π) f := by
  funext j
  unfold classicalDual markovHeis reverseKernel
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Theorem `thm:classical-reverse` (row stochasticity)**: the
reverse kernel is row stochastic (using stationarity of `π`). -/
theorem reverseKernel_rowsum (hπ : ∀ i, 0 < π i)
    (hstat : ∀ j, ∑ i, π i * p i j = π j) (i : Fin n) :
    ∑ j, reverseKernel p π i j = 1 := by
  unfold reverseKernel
  rw [← Finset.sum_div]
  rw [show ∑ j, π j * p j i = π i from hstat i]
  exact div_self (hπ i).ne'

/-- **Theorem `thm:classical-reverse` (π-invariance)**: the reverse
kernel preserves the stationary law (using row stochasticity of
`p`). -/
theorem reverseKernel_stationary (hπ : ∀ i, 0 < π i)
    (hrow : ∀ i, ∑ j, p i j = 1) (j : Fin n) :
    ∑ i, π i * reverseKernel p π i j = π j := by
  unfold reverseKernel
  have hterm : ∀ i : Fin n, π i * (π j * p j i / π i) = π j * p j i :=
    fun i => by
      rw [mul_div_assoc']
      rw [mul_comm (π i) (π j * p j i), mul_div_assoc]
      rw [div_self (hπ i).ne', mul_one]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum,
    hrow j, mul_one]

/-- **Theorem `thm:classical-reverse` (detailed balance)**: the
kernel equals its reverse exactly at classical detailed balance
`π_i p_{ij} = π_j p_{ji}`. -/
theorem reverseKernel_eq_iff (hπ : ∀ i, 0 < π i) :
    (∀ i j, reverseKernel p π i j = p i j) ↔
      ∀ i j, π i * p i j = π j * p j i := by
  constructor
  · intro h i j
    rw [← h i j]
    unfold reverseKernel
    rw [mul_div_assoc', mul_comm (π i) (π j * p j i), mul_div_assoc,
      div_self (hπ i).ne', mul_one]
  · intro h i j
    unfold reverseKernel
    rw [← h i j, mul_div_cancel_left₀ _ (hπ i).ne']

/-- **Theorem `thm:path-reversal-tautology`**: for every path
`γ = (i₀, …, i_m)`, the stationary forward weight equals the
reversed weight under the canonical anti-renewal chain —
identically, whether or not `P` is detailed balanced. -/
theorem path_reversal_tautology (hπ : ∀ i, 0 < π i)
    (γ : ℕ → Fin n) (m : ℕ) :
    π (γ 0) * ∏ k ∈ Finset.range m, p (γ k) (γ (k + 1))
      = π (γ m)
        * ∏ k ∈ Finset.range m, reverseKernel p π (γ (k + 1)) (γ k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← mul_assoc,
      ih]
    have hstep : π (γ (m + 1)) * reverseKernel p π (γ (m + 1)) (γ m)
        = π (γ m) * p (γ m) (γ (m + 1)) := by
      unfold reverseKernel
      rw [mul_div_assoc']
      rw [mul_comm (π (γ (m + 1))) (π (γ m) * p (γ m) (γ (m + 1))),
        mul_div_assoc, div_self (hπ (γ (m + 1))).ne', mul_one]
    calc π (γ m)
          * (∏ k ∈ Finset.range m,
              reverseKernel p π (γ (k + 1)) (γ k))
          * p (γ m) (γ (m + 1))
        = (π (γ m) * p (γ m) (γ (m + 1)))
          * ∏ k ∈ Finset.range m,
              reverseKernel p π (γ (k + 1)) (γ k) := by ring
      _ = (π (γ (m + 1)) * reverseKernel p π (γ (m + 1)) (γ m))
          * ∏ k ∈ Finset.range m,
              reverseKernel p π (γ (k + 1)) (γ k) := by
          rw [hstep]
      _ = π (γ (m + 1))
          * ((∏ k ∈ Finset.range m,
              reverseKernel p π (γ (k + 1)) (γ k))
            * reverseKernel p π (γ (m + 1)) (γ m)) := by ring

end NCG.Upstream
