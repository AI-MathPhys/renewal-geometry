/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Krein.CoverModel
import NCG.Krein.SignedData

/-!
# The modular signed Dirac: deck-odd normal form and the forced weight

The manuscript characterises the unbounded part of the signed modular Dirac
operator `D₋ = J_χ e^{βN} + B` *intrinsically*
(`thm:modular-characterisation`): deck-oddness plus diagonality force the
factorization `D₀ = J_χ · g` with a sheet-independent magnitude `g`
(`lem:deck-odd-normal-form`), and the modular implementation property
`Ad(g)(S̃_e) = e^β S̃_e` forces `g = e^{βN}` up to scale along each
recurrent orbit (the recurrence route, Remark `rem:recurrence-route`).

This file proves both steps in the diagonal model:

* `NCG.deckOdd_eq_sign_mul`, `NCG.deckOdd_diagOp_eq` —
  **Lemma `lem:deck-odd-normal-form`**: a deck-odd diagonal symbol is the
  sheet sign times a sheet-independent symbol; at the operator level,
  `diagOp d = J ∘ (sheet-independent diagonal)`;
* `NCG.exchange_orbit_pow` and `NCG.modular_weight_on_orbit` — the
  **recurrence route of `thm:modular-characterisation`**: the exchange
  relation `g ∘ S̃ = c • (S̃ ∘ g)` propagates the diagonal symbol along
  shift orbits as `d(sⁿ i) = cⁿ · d(i)`; with `c = e^β` and a unit-increment
  clock this is exactly the exponential modular weight `e^{βN}` on each
  orbit, normalised by its value at the orbit's base point.
-/

namespace NCG

open Multigraph

/-! ### Deck-odd diagonal symbols -/

variable {V : Type*}

/-- A diagonal symbol on the signed cover is **deck-odd** when the deck
transformation `(x, η) ↦ (x, η+1)` reverses its sign
(`lem:deck-odd-normal-form`, hypothesis (M2) of the modular
characterisation). -/
def DeckOdd (d : V × ZMod 2 → ℂ) : Prop :=
  ∀ p : V × ZMod 2, d (p.1, p.2 + 1) = -d p

/-- **Deck-odd symbols are signed magnitudes**
(`lem:deck-odd-normal-form`): a deck-odd diagonal symbol is the sheet sign
times its sheet-independent restriction to the `0`-sheet. -/
theorem deckOdd_eq_sign_mul {d : V × ZMod 2 → ℂ} (hd : DeckOdd d)
    (p : V × ZMod 2) : d p = signValue p.2 * d (p.1, 0) := by
  obtain ⟨x, η⟩ := p
  have h2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h2 η with hη | hη
  · subst hη
    simp
  · subst hη
    have h := hd (x, 0)
    simp only [zero_add] at h
    simp [h]

/-- Diagonal operators compose to the diagonal operator of the pointwise
product of symbols. -/
theorem diagOp_comp_diagOp {ι : Type*} (d₁ d₂ : ι → ℂ) :
    diagOp d₁ ∘ₗ diagOp d₂ = diagOp fun i => d₁ i * d₂ i := by
  apply Finsupp.lhom_ext
  intro i c
  simp only [LinearMap.comp_apply, diagOp_single, mul_assoc]

/-- **Lemma `lem:deck-odd-normal-form`**, operator form: a deck-odd
diagonal operator on the signed cover factors as the fundamental symmetry
times a sheet-independent diagonal magnitude, `D₀ = J_χ · g`.  This
discharges the postulated factor `J_χ` in the modular signed Dirac
`D₋ = J_χ e^{βN} + B`. -/
theorem deckOdd_diagOp_eq {G : Multigraph} {d : G.V × ZMod 2 → ℂ}
    (hd : DeckOdd d) :
    diagOp d = kreinJ G ∘ₗ diagOp fun p => d (p.1, 0) := by
  calc diagOp d
      = diagOp fun p : G.V × ZMod 2 => signValue p.2 * d (p.1, 0) := by
        congr 1
        funext p
        exact deckOdd_eq_sign_mul hd p
    _ = diagOp (fun p : G.V × ZMod 2 => signValue p.2)
          ∘ₗ diagOp fun p => d (p.1, 0) :=
        (diagOp_comp_diagOp _ _).symm
    _ = kreinJ G ∘ₗ diagOp fun p => d (p.1, 0) := rfl

/-! ### The recurrence route: the modular weight is forced on orbits -/

/-- Iterating the modular scaling relation along a shift orbit: if the
diagonal symbol satisfies `d(s i) = c · d(i)`, then
`d(sⁿ i) = cⁿ · d(i)`.  This is the recurrence
`f(n+1) = e^β f(n) ⟹ f(n) = f(0) e^{βn}` of
Remark `rem:recurrence-route`. -/
theorem exchange_orbit_pow {ι : Type*} {d : ι → ℂ} {s : ι → ι} {c : ℂ}
    (h : ∀ i, d (s i) = c * d i) (i : ι) (n : ℕ) :
    d (s^[n] i) = c ^ n * d i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', h, ih, pow_succ]
      ring

/-- **The recurrence route of `thm:modular-characterisation`**: a diagonal
operator satisfying the modular exchange relation
`g ∘ S̃ = c • (S̃ ∘ g)` against a shift has its symbol propagated along
every shift orbit by `d(sⁿ i) = cⁿ · d(i)`.  With `c = e^β` this says the
magnitude of the modular signed Dirac is the exponential weight `e^{βN}`
on each recurrent orbit, up to the normalisation `d(i)` at the orbit's base
point — the manuscript's conclusion `g = e^{βN}` after base normalisation,
with connectivity supplying the passage from orbits to the whole recurrent
component. -/
theorem modular_weight_on_orbit {ι : Type*} {d : ι → ℂ} {s : ι → ι} {c : ℂ}
    (hex : diagOp d ∘ₗ shiftOp s = c • (shiftOp s ∘ₗ diagOp d))
    (i : ι) (n : ℕ) :
    d (s^[n] i) = c ^ n * d i :=
  exchange_orbit_pow ((diagOp_shiftOp_exchange_iff d s c).mp hex) i n

/-- Specialisation to the renewal clock: if the shift raises the clock `N`
by one and the symbol is the exponential weight `d = e^{βN}`, the exchange
constant is exactly `e^β` — the converse direction pairing with
`NCG.clock_scaling`, closing the characterisation loop of
`thm:modular-characterisation` in the diagonal model. -/
theorem exp_weight_orbit {ι : Type*} (N : ι → ℝ) (s : ι → ι)
    (hstep : ∀ i, N (s i) = N i + 1) (β : ℝ) (i : ι) (n : ℕ) :
    (Real.exp (β * N (s^[n] i)) : ℂ)
      = (Real.exp β : ℂ) ^ n * (Real.exp (β * N i) : ℂ) := by
  exact exchange_orbit_pow (d := fun j => (Real.exp (β * N j) : ℂ))
    (s := s) (c := (Real.exp β : ℂ))
    (fun j => by
      show (Real.exp (β * N (s j)) : ℂ)
        = (Real.exp β : ℂ) * (Real.exp (β * N j) : ℂ)
      have hexp : Real.exp (β * N (s j))
          = Real.exp β * Real.exp (β * N j) := by
        rw [hstep j, mul_add, mul_one, add_comm, Real.exp_add]
      rw [hexp]
      push_cast
      ring) i n

end NCG
