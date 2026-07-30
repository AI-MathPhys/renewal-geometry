/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The connected-slot Möbius factorization (SM_emergence, Phase 2)

`thm:connected-slot-factorization-main`: the alternating
inclusion–exclusion of a multilinear chain functional over which
slots carry the physical (`ε`) versus baseline (`0`) insertion
telescopes into the fully connected product,

  `𝔠_n(ε) = Σ_{S⊆[n]} (-1)^{n-|S|} W(X^S) = L·ΔX₁·A₁·ΔX₂ ⋯ ΔX_n·R`,

with `ΔX = X(ε) - X(0)`; if each local defect is `O(ε)` the
connected coefficient is `O(ε^n)` — the record-order filtration of
the flavour hierarchy.

* `signedSum` — the alternating subset sum in recursive (on/off per
  slot) form;
* `deltaChain` — the connected product of slot defects;
* `connected_slot_factorization` — the boxed identity;
* `deltaChain_norm_bound` — the `O(ε^n)` bound: if every slot defect
  has norm `≤ d` and every coupler norm `≤ c`, then
  `‖ΔX₁A₁ ⋯ ΔX_nA_n‖ ≤ (d·c)^n`.
-/

namespace NCG

variable {M : Type*} [NormedRing M]

/-- The alternating inclusion–exclusion over slot insertions, in
recursive form: each slot contributes its physical insertion minus
its baseline insertion, so unfolding produces exactly
`Σ_{S⊆[n]} (-1)^{n-|S|} L·Y₁^S·A₁ ⋯ Y_n^S·A_n` with `Y^S = X(ε)` on
`S` and `X(0)` off `S`. -/
def signedSum (eps : ℝ) : M → List ((ℝ → M) × M) → M
  | L, [] => L
  | L, (X, A) :: rest =>
      signedSum eps (L * X eps * A) rest
        - signedSum eps (L * X 0 * A) rest

/-- The fully connected chain of slot defects
`ΔX₁·A₁·ΔX₂·A₂ ⋯ ΔX_n·A_n`. -/
def deltaChain (eps : ℝ) : List ((ℝ → M) × M) → M
  | [] => 1
  | (X, A) :: rest => (X eps - X 0) * A * deltaChain eps rest

/-- `thm:connected-slot-factorization-main`: the alternating subset
sum telescopes into the connected product of slot defects,
`𝔠_n(ε) = L·ΔX₁·A₁ ⋯ ΔX_n·A_n`. -/
theorem connected_slot_factorization (eps : ℝ) (L : M)
    (slots : List ((ℝ → M) × M)) :
    signedSum eps L slots = L * deltaChain eps slots := by
  induction slots generalizing L with
  | nil =>
    unfold signedSum deltaChain
    rw [mul_one]
  | cons slot rest ih =>
    obtain ⟨X, A⟩ := slot
    unfold signedSum deltaChain
    rw [ih, ih]
    rw [show L * ((X eps - X 0) * A * deltaChain eps rest)
        = (L * X eps * A) * deltaChain eps rest
          - (L * X 0 * A) * deltaChain eps rest by noncomm_ring]

/-- The `O(ε^n)` record-order bound: if every slot defect has norm
at most `d` and every coupler has norm at most `c`, the connected
chain has norm at most `(d·c)^n` — each additional connected slot
costs one full record order. -/
theorem deltaChain_norm_bound [NormOneClass M] (eps : ℝ)
    (slots : List ((ℝ → M) × M)) (d c : ℝ)
    (hd : ∀ s ∈ slots, ‖s.1 eps - s.1 0‖ ≤ d)
    (hc : ∀ s ∈ slots, ‖s.2‖ ≤ c)
    (hd0 : 0 ≤ d) (hc0 : 0 ≤ c) :
    ‖deltaChain eps slots‖ ≤ (d * c) ^ slots.length := by
  induction slots with
  | nil =>
    unfold deltaChain
    simp
  | cons slot rest ih =>
    obtain ⟨X, A⟩ := slot
    unfold deltaChain
    have h1 : ‖X eps - X 0‖ ≤ d := hd (X, A) List.mem_cons_self
    have h2 : ‖A‖ ≤ c := hc (X, A) List.mem_cons_self
    have h3 : ‖deltaChain eps rest‖ ≤ (d * c) ^ rest.length :=
      ih (fun s hs => hd s (List.mem_cons_of_mem _ hs))
        (fun s hs => hc s (List.mem_cons_of_mem _ hs))
    calc ‖(X eps - X 0) * A * deltaChain eps rest‖
        ≤ ‖(X eps - X 0) * A‖ * ‖deltaChain eps rest‖ :=
          norm_mul_le _ _
      _ ≤ (‖X eps - X 0‖ * ‖A‖) * ‖deltaChain eps rest‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _)
      _ ≤ (d * c) * (d * c) ^ rest.length := by
          apply mul_le_mul _ h3 (norm_nonneg _) (by positivity)
          exact mul_le_mul h1 h2 (norm_nonneg _) hd0
      _ = (d * c) ^ (rest.length + 1) := by
          rw [pow_succ]
          ring
      _ = (d * c) ^ (List.length ((X, A) :: rest)) := by
          rw [List.length_cons]

end NCG
