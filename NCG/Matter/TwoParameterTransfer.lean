/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Classification of incidence-local covariant transfers
  (`thm:two-parameter-transfer`,
   `corollary:what-the-nonbacktracking-rule-fixes`, SM_emergence)

An operator on the oriented-edge space of `K₄` that is
incidence-local (output at `(i,j)` reads only edges leaving the
head `j`, all nonbacktracking continuations entering equally) and
`S₄`-equivariant is a unique two-parameter combination

`(T_{w,b} f)(i,j) = w·Σ_{k≠i,j} f(j,k) + b·f(j,i)`.

* `pair_two_transitive` — `S₄` is 2-transitive on ordered distinct
  pairs (kernel-checked);
* `two_parameter_transfer` — existence and uniqueness of `(w, b)`:
  the stabilizer of `(i,j)` fixes the reverse continuation and
  identifies the two forward continuations, and 2-transitivity
  transports the two coefficients to all ordered pairs.  The
  backtracking coefficient `b` is not forced to vanish by
  covariance: `b = 0` is the additional nonbacktracking support
  rule.
-/

namespace NCG

open Finset

/-- The delta cochain supported on the ordered pair `(p, q)`. -/
def pairDelta (p q : Fin 4) : Fin 4 → Fin 4 → ℂ :=
  fun a b => if a = p ∧ b = q then 1 else 0

/-- `S₄` acts 2-transitively on ordered distinct pairs. -/
theorem pair_two_transitive :
    ∀ i j i' j' : Fin 4, i ≠ j → i' ≠ j' →
      ∃ σ : Equiv.Perm (Fin 4), σ i = i' ∧ σ j = j' := by
  decide

/-- `thm:two-parameter-transfer`: an incidence-local,
uniform-continuation, `S₄`-equivariant transfer on the oriented
edges of `K₄` is `T_{w,b}` for a unique pair `(w, b)`. -/
theorem two_parameter_transfer
    (T : (Fin 4 → Fin 4 → ℂ) → (Fin 4 → Fin 4 → ℂ))
    (hker : ∃ w b : Fin 4 → Fin 4 → ℂ, ∀ f i j,
      T f i j = w i j * (∑ k ∈ Finset.univ.filter
          (fun k => k ≠ i ∧ k ≠ j), f j k)
        + b i j * f j i)
    (hequi : ∀ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Fin 4 → ℂ)
      (i j : Fin 4),
      T (fun a b => f (σ a) (σ b)) i j = T f (σ i) (σ j)) :
    ∃ w0 b0 : ℂ,
      (∀ f i j, i ≠ j →
        T f i j = w0 * (∑ k ∈ Finset.univ.filter
            (fun k => k ≠ i ∧ k ≠ j), f j k)
          + b0 * f j i)
      ∧ ∀ w1 b1 : ℂ,
        (∀ f i j, i ≠ j →
          T f i j = w1 * (∑ k ∈ Finset.univ.filter
              (fun k => k ≠ i ∧ k ≠ j), f j k)
            + b1 * f j i) → w1 = w0 ∧ b1 = b0 := by
  obtain ⟨w, b, hker⟩ := hker
  have hexk : ∀ i j : Fin 4, ∃ k, k ≠ i ∧ k ≠ j := by decide
  -- test evaluations extract the two coefficients
  have hsumδ : ∀ (i j k : Fin 4), k ≠ i → k ≠ j →
      (∑ k' ∈ Finset.univ.filter (fun k' => k' ≠ i ∧ k' ≠ j),
        pairDelta j k j k') = 1 := by
    intro i j k hki hkj
    have : ∀ k' : Fin 4, pairDelta j k j k'
        = if k' = k then 1 else 0 := by
      intro k'
      simp [pairDelta]
    simp only [this]
    rw [Finset.sum_ite_eq' _ k (fun _ => (1 : ℂ))]
    rw [if_pos (by simp [hki, hkj])]
  have htw : ∀ i j k, i ≠ j → k ≠ i → k ≠ j →
      T (pairDelta j k) i j = w i j := by
    intro i j k hij hki hkj
    rw [hker, hsumδ i j k hki hkj]
    rw [show pairDelta j k j i = 0 from by
      simp [pairDelta, Ne.symm hki]]
    ring
  have htb : ∀ i j, i ≠ j → T (pairDelta j i) i j = b i j := by
    intro i j hij
    rw [hker]
    rw [show (∑ k' ∈ Finset.univ.filter
        (fun k' => k' ≠ i ∧ k' ≠ j), pairDelta j i j k') = 0 from by
      apply Finset.sum_eq_zero
      intro k' hk'
      rw [Finset.mem_filter] at hk'
      simp [pairDelta, hk'.2.1]]
    rw [show pairDelta j i j i = 1 from by simp [pairDelta]]
    ring
  -- pullback of a delta cochain along a permutation
  have hcomp : ∀ (σ : Equiv.Perm (Fin 4)) (p q : Fin 4),
      (fun a b => pairDelta p q (σ a) (σ b))
        = pairDelta (σ.symm p) (σ.symm q) := by
    intro σ p q
    funext a c
    simp only [pairDelta]
    congr 1
    simp [Equiv.apply_eq_iff_eq_symm_apply]
  -- 2-transitivity transports the coefficients
  have hw : ∀ i j i' j' : Fin 4, i ≠ j → i' ≠ j' →
      w i j = w i' j' := by
    intro i j i' j' hij hij'
    obtain ⟨σ, hσi, hσj⟩ := pair_two_transitive i j i' j' hij hij'
    obtain ⟨k0, hk0i, hk0j⟩ := hexk i' j'
    have hsymj : σ.symm j' = j := by rw [← hσj]; simp
    have hσk1 : σ (σ.symm k0) = k0 := by simp
    have hk1i : σ.symm k0 ≠ i := by
      intro h
      apply hk0i
      rw [← hσi, ← h, hσk1]
    have hk1j : σ.symm k0 ≠ j := by
      intro h
      apply hk0j
      rw [← hσj, ← h, hσk1]
    calc w i j = T (pairDelta j (σ.symm k0)) i j :=
          (htw i j (σ.symm k0) hij hk1i hk1j).symm
    _ = T (fun a c => pairDelta j' k0 (σ a) (σ c)) i j := by
          rw [hcomp σ j' k0, hsymj]
    _ = T (pairDelta j' k0) (σ i) (σ j) := hequi σ _ i j
    _ = T (pairDelta j' k0) i' j' := by rw [hσi, hσj]
    _ = w i' j' := htw i' j' k0 hij' hk0i hk0j
  have hb : ∀ i j i' j' : Fin 4, i ≠ j → i' ≠ j' →
      b i j = b i' j' := by
    intro i j i' j' hij hij'
    obtain ⟨σ, hσi, hσj⟩ := pair_two_transitive i j i' j' hij hij'
    have hsymj : σ.symm j' = j := by rw [← hσj]; simp
    have hsymi : σ.symm i' = i := by rw [← hσi]; simp
    calc b i j = T (pairDelta j i) i j := (htb i j hij).symm
    _ = T (fun a c => pairDelta j' i' (σ a) (σ c)) i j := by
          rw [hcomp σ j' i', hsymj, hsymi]
    _ = T (pairDelta j' i') (σ i) (σ j) := hequi σ _ i j
    _ = T (pairDelta j' i') i' j' := by rw [hσi, hσj]
    _ = b i' j' := htb i' j' hij'
  refine ⟨w 0 1, b 0 1, ?_, ?_⟩
  · intro f i j hij
    rw [hker, hw i j 0 1 hij (by decide), hb i j 0 1 hij (by decide)]
  · intro w1 b1 hf
    constructor
    · have h1 := hf (pairDelta 1 2) 0 1 (by decide)
      have h2 := htw 0 1 2 (by decide) (by decide) (by decide)
      rw [hsumδ 0 1 2 (by decide) (by decide)] at h1
      rw [show pairDelta 1 2 1 0 = 0 from by simp [pairDelta]] at h1
      rw [h1] at h2
      linear_combination h2
    · have h1 := hf (pairDelta 1 0) 0 1 (by decide)
      have h2 := htb 0 1 (by decide)
      rw [show (∑ k' ∈ Finset.univ.filter
          (fun k' => k' ≠ (0 : Fin 4) ∧ k' ≠ 1),
          pairDelta 1 0 1 k') = 0 from by
        apply Finset.sum_eq_zero
        intro k' hk'
        rw [Finset.mem_filter] at hk'
        simp [pairDelta, hk'.2.1]] at h1
      rw [show pairDelta 1 0 1 0 = 1 from by simp [pairDelta]] at h1
      rw [h1] at h2
      linear_combination h2

end NCG
