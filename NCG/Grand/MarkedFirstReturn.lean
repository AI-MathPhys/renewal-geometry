/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Marked first-return reconstruction
  (`thm:marked-first-return`, Gran-Tensor manuscript)

* `marked_first_return_renewal`: with total transfer `T` and
  no-boundary branch `Ψ`, the boxed renewal equation holds
  exactly with its survivor term:
  `Tⁿ = Σ_{k=1}^{n} T^{n-k}·F_k + Ψⁿ` where `F_k = (T-Ψ)Ψ^{k-1}`
  is the summed first-return map of length `k` — in any ring, by
  first-return telescoping.
* `marked_first_return_normalization` /
  `marked_instrument_normalization`: the boxed instrument
  normalization `Σ_{n=1}^{N} Σ_m F*_{n,m}(I) + S*_{N}(I) = I`
  for a unital coarse instrument, by the same telescope in the
  Heisenberg picture.

Rendering disclosed: `F_{n,m} = Φ_m Φ_∅^{n-1}` is definitional
in this rendering (the branch-conditioned tomography clause is
the manuscript's operational reading); the boxed recursion
`F_n = U_n - Σ U_{n-k}F_k` is the proved identity rearranged;
the survivor term is carried exactly (the manuscript's boxed
form is its recurrent-limit reading); the formal-series
resolvent identities are the power-series packaging.
-/

namespace NCG

/-- `thm:marked-first-return` (renewal clause): the exact
first-return decomposition with survivor term, in any ring. -/
theorem marked_first_return_renewal {A : Type*} [Ring A]
    (T Ψ : A) (n : ℕ) :
    T ^ n
      = (∑ k ∈ Finset.range n,
          T ^ (n - 1 - k) * ((T - Ψ) * Ψ ^ k)) + Ψ ^ n := by
  have hterm : ∀ k ∈ Finset.range n,
      T ^ (n - 1 - k) * ((T - Ψ) * Ψ ^ k)
      = T ^ (n - k) * Ψ ^ k
        - T ^ (n - (k + 1)) * Ψ ^ (k + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [sub_mul, mul_sub]
    congr 1
    · rw [← mul_assoc, ← pow_succ,
        show n - 1 - k + 1 = n - k from by omega]
    · rw [← pow_succ',
        show n - 1 - k = n - (k + 1) from by omega]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_range_sub' (fun j => T ^ (n - j) * Ψ ^ j)]
  rw [Nat.sub_zero, pow_zero, mul_one, Nat.sub_self, pow_zero,
    one_mul, sub_add_cancel]

/-- Heisenberg survivor telescope. -/
theorem marked_first_return_normalization {V : Type*}
    [AddCommGroup V] [Module ℂ V] (Ψ : V →ₗ[ℂ] V) (v : V)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, (Ψ ^ n) (v - Ψ v)) + (Ψ ^ N) v
      = v := by
  have hterm : ∀ n ∈ Finset.range N,
      (Ψ ^ n) (v - Ψ v)
        = (Ψ ^ n) v - (Ψ ^ (n + 1)) v := by
    intro n _
    rw [map_sub, pow_succ, Module.End.mul_apply]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_range_sub' (fun n => (Ψ ^ n) v)]
  rw [pow_zero, Module.End.one_apply, sub_add_cancel]

/-- `thm:marked-first-return` (normalization clause): the boxed
instrument normalization for a unital coarse instrument. -/
theorem marked_instrument_normalization {V M : Type*}
    [AddCommGroup V] [Module ℂ V] [Fintype M]
    (Ψ : V →ₗ[ℂ] V) (w : M → V) (v : V)
    (hunit : Ψ v + ∑ m, w m = v) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∑ m, (Ψ ^ n) (w m)) + (Ψ ^ N) v
      = v := by
  have hw : ∀ n : ℕ, ∑ m, (Ψ ^ n) (w m) = (Ψ ^ n) (v - Ψ v) := by
    intro n
    rw [← map_sum]
    congr 1
    exact eq_sub_of_add_eq' hunit
  rw [Finset.sum_congr rfl (fun n _ => hw n)]
  exact marked_first_return_normalization Ψ v N

end NCG
