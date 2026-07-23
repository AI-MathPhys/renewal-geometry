/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The exact scalar path law (`cor:predictive-reference-path-law`)

Given branch maps `E_i` along a resolved path satisfying the
reference-renewal identity `E_i ρ_{x_{i}} = w_i • ρ_{x_{i+1}}`
(the conclusion of `thm:predictive-reference-renewal`, taken here as
the hypothesis, exactly as the corollary depends on that theorem),
the accumulated branch map renews the terminal reference state with
the **product** of the one-edge weights:

`E_n ⋯ E_1 (ρ_{x_0}) = (∏ w_i) • ρ_{x_n}`.

In the matrix realization, taking traces gives the probability of the
resolved path as the product of its one-edge probabilities
(`reference_path_probability`).  The branch maps are taken on a
common ambient module (the direct-sum realization of the varying
target algebras); weights live in an arbitrary commutative ring.
-/

namespace NCG

variable {K : Type*} [CommRing K] {W : Type*} [AddCommGroup W]
  [Module K W]

/-- The accumulated branch map along a path, last edge outermost. -/
def pathComp : ∀ n, (Fin n → (W →ₗ[K] W)) → (W →ₗ[K] W)
  | 0, _ => LinearMap.id
  | n + 1, E => E (Fin.last n) ∘ₗ pathComp n fun i => E i.castSucc

@[simp]
theorem pathComp_zero (E : Fin 0 → (W →ₗ[K] W)) :
    pathComp 0 E = LinearMap.id := rfl

@[simp]
theorem pathComp_succ (n : ℕ) (E : Fin (n + 1) → (W →ₗ[K] W)) :
    pathComp (n + 1) E
      = E (Fin.last n) ∘ₗ pathComp n fun i => E i.castSucc := rfl

/-- **Corollary `cor:predictive-reference-path-law`**: branchwise
reference renewal telescopes to the exact scalar path law. -/
theorem reference_path_law :
    ∀ (n : ℕ) (ρ : Fin (n + 1) → W) (E : Fin n → (W →ₗ[K] W))
      (w : Fin n → K),
      (∀ i : Fin n, E i (ρ i.castSucc) = w i • ρ i.succ) →
      pathComp n E (ρ 0) = (∏ i, w i) • ρ (Fin.last n) := by
  intro n
  induction n with
  | zero =>
    intro ρ E w _
    simp [pathComp, Fin.last]
  | succ m ih =>
    intro ρ E w hren
    have h1 := ih (fun i => ρ i.castSucc) (fun i => E i.castSucc)
      (fun i => w i.castSucc) ?_
    · have h2 : pathComp (m + 1) E (ρ 0)
          = E (Fin.last m)
            (pathComp m (fun i => E i.castSucc) (ρ 0)) := rfl
      rw [h2]
      have h1' : pathComp m (fun i => E i.castSucc) (ρ 0)
          = (∏ i : Fin m, w i.castSucc) • ρ (Fin.last m).castSucc := by
        have hz : (fun i : Fin (m + 1) => ρ i.castSucc) 0 = ρ 0 := by
          simp
        rw [← hz]
        exact h1
      rw [h1', map_smul, hren (Fin.last m)]
      rw [smul_smul, Fin.prod_univ_castSucc]
      congr 1
    · intro i
      have h3 := hren i.castSucc
      rw [show (i.castSucc).succ = (i.succ).castSucc from
        (Fin.succ_castSucc i).symm] at h3
      exact h3

/-- The probability clause: on trace-one matrix reference states, the
accumulated branch weight is the product of the one-edge
probabilities. -/
theorem reference_path_probability {n d : ℕ}
    (ρ : Fin (n + 1) → Matrix (Fin d) (Fin d) ℂ)
    (E : Fin n → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ))
    (w : Fin n → ℂ)
    (hren : ∀ i : Fin n, E i (ρ i.castSucc) = w i • ρ i.succ)
    (htr : (ρ (Fin.last n)).trace = 1) :
    (pathComp n E (ρ 0)).trace = ∏ i, w i := by
  rw [reference_path_law n ρ E w hren, Matrix.trace_smul, htr,
    smul_eq_mul, mul_one]

end NCG
