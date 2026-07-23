/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Deck symmetry and the first temporal-orientation no-go

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:deck-order-parameter` — the deck involution `τ`, deck-odd
  observables (`τ a τ⁻¹ = −a`), the sheet-sign observable `J`, and
  the order parameter `m_ϱ = ϱ(J)`;
* `thm:symmetric-state-cancellation-upstream` — a deck-invariant
  state annihilates every deck-odd observable; in particular
  `m_ϱ = 0`;
* `thm:no-finite-spontaneous-orientation` — a deck-covariant
  transfer with a unique stationary state (the uniqueness supplied
  by `thm:primitive-stationary-weight` for primitive finite
  transfers) has a deck-invariant stationary state, so
  `Tr(ρ_* J) = 0`: no finite primitive deck-symmetric renewal law
  spontaneously selects a temporal orientation;
* `cor:orientation-selection-routes` — contrapositive: a nonzero
  stationary deck-odd order parameter forces either explicit
  deck-symmetry breaking of the transfer or failure of
  stationary-state uniqueness (nonprimitivity / degeneracy /
  superselection or singular limits).
-/

namespace NCG.Upstream

variable {A : Type*} [Ring A] [Algebra ℂ A]

section Deck

variable (φ : A →ₗ[ℂ] ℂ) (τ τi : A)

/-- **Definition `def:deck-order-parameter` (deck-odd
observables)**: `τ a τ⁻¹ = −a`. -/
def DeckOdd (a : A) : Prop := τ * a * τi = -a

/-- **Definition `def:deck-order-parameter` (invariant states)**:
`ϱ ∘ Ad(τ) = ϱ`. -/
def DeckInvariantState : Prop := ∀ a : A, φ (τ * a * τi) = φ a

/-- **Theorem `thm:symmetric-state-cancellation-upstream`**: a
deck-invariant state has zero expectation on every deck-odd
observable — in particular the order parameter `m_ϱ = ϱ(J)`
vanishes. -/
theorem symmetric_state_cancellation
    (hinv : DeckInvariantState φ τ τi) {a : A}
    (hodd : DeckOdd τ τi a) : φ a = 0 := by
  have h1 : φ a = φ (τ * a * τi) := (hinv a).symm
  rw [hodd, map_neg] at h1
  have h2 : φ a + φ a = 0 := by
    nth_rewrite 1 [h1]
    ring
  exact add_self_eq_zero.mp h2

/-- **Theorem `thm:deck-observability` (deck-even agreement)**: the
deck companion `ω₋ = ω₊ ∘ Ad(τ)` of a state agrees with `ω₊` on every
deck-even observable, so a predictive quotient using only deck-even
future tests identifies the two orientations. -/
theorem deck_even_agreement {a : A} (heven : τ * a * τi = a) :
    φ (τ * a * τi) = φ a := by rw [heven]

/-- **Theorem `thm:deck-observability` (deck-odd sign flip)**: on a
deck-odd observable the deck companion flips sign,
`ω₋(a) = −ω₊(a)`. -/
theorem deck_odd_flip {a : A} (hodd : DeckOdd τ τi a) :
    φ (τ * a * τi) = -φ a := by rw [hodd, map_neg]

/-- **Theorem `thm:deck-observability` (predictive distinguishability)**:
an admissible deck-odd test with `ω₊(a) ≠ 0` separates the two
orientation phases: `ω₋(a) ≠ ω₊(a)`. -/
theorem deck_odd_distinguishes {a : A} (hodd : DeckOdd τ τi a)
    (hne : φ a ≠ 0) : φ (τ * a * τi) ≠ φ a := by
  rw [deck_odd_flip φ τ τi hodd]
  intro h
  have h2 : φ a + φ a = 0 := by linear_combination -h
  exact hne (add_self_eq_zero.mp h2)

end Deck

section Transfer

variable (τ τi : A) (T : A →ₗ[ℂ] A)
variable (tr : A →ₗ[ℂ] ℂ)

/-- The Schrödinger deck action on densities,
`Ad(τ)_* x = τ⁻¹ x τ` (the predual of `a ↦ τ a τ⁻¹` for a
trace pairing). -/
def deckAd (x : A) : A := τi * x * τ

/-- **Theorem `thm:no-finite-spontaneous-orientation` (invariant
stationary state)**: if the transfer is deck covariant and its
stationary density is unique, the stationary density is deck
invariant. -/
theorem stationary_deck_invariant (ρs : A)
    (hstat : T ρs = ρs)
    (hcov : ∀ x : A, T (deckAd τ τi x) = deckAd τ τi (T x))
    (huniq : ∀ x : A, T x = x → x = ρs)
    : deckAd τ τi ρs = ρs := by
  apply huniq
  rw [hcov, hstat]

/-- **Theorem `thm:no-finite-spontaneous-orientation`**: under deck
covariance and stationary-state uniqueness (supplied for primitive
finite transfers by `thm:primitive-stationary-weight`), the
stationary expectation of every deck-odd observable — in particular
of the sheet sign `J` — vanishes: no spontaneous orientation. -/
theorem no_finite_spontaneous_orientation (ρs : A)
    (hτi : τ * τi = 1) (hiτ : τi * τ = 1)
    (htr : ∀ x y : A, tr (x * y) = tr (y * x))
    (hstat : T ρs = ρs)
    (hcov : ∀ x : A, T (deckAd τ τi x) = deckAd τ τi (T x))
    (huniq : ∀ x : A, T x = x → x = ρs)
    {J : A} (hodd : DeckOdd τ τi J) :
    tr (ρs * J) = 0 := by
  have hinvρ : deckAd τ τi ρs = ρs :=
    stationary_deck_invariant τ τi T ρs hstat hcov huniq
  -- the state a ↦ tr(ρs a) is deck invariant
  have hstate : DeckInvariantState
      ((tr.comp (LinearMap.mulLeft ℂ ρs))) τ τi := by
    intro a
    show tr (ρs * (τ * a * τi)) = tr (ρs * a)
    calc tr (ρs * (τ * a * τi))
        = tr ((ρs * τ * a) * τi) := by congr 1; noncomm_ring
      _ = tr (τi * (ρs * τ * a)) := htr _ _
      _ = tr ((τi * ρs * τ) * a) := by congr 1; noncomm_ring
      _ = tr (deckAd τ τi ρs * a) := rfl
      _ = tr (ρs * a) := by rw [hinvρ]
  have := symmetric_state_cancellation
    (tr.comp (LinearMap.mulLeft ℂ ρs)) τ τi hstate hodd
  simpa using this

/-- **Corollary `cor:orientation-selection-routes`**: a nonzero
stationary deck-odd order parameter forces a departure from the
finite primitive symmetric phase — the transfer either fails deck
covariance (explicit breaking, route (i)) or fails stationary-state
uniqueness (nonprimitivity, degeneracy, superselection, or a
singular limit — routes (ii)–(iv)). -/
theorem orientation_selection_routes (ρs : A)
    (hτi : τ * τi = 1) (hiτ : τi * τ = 1)
    (htr : ∀ x y : A, tr (x * y) = tr (y * x))
    (hstat : T ρs = ρs)
    {J : A} (hodd : DeckOdd τ τi J)
    (hm : tr (ρs * J) ≠ 0) :
    ¬((∀ x : A, T (deckAd τ τi x) = deckAd τ τi (T x))
      ∧ ∀ x : A, T x = x → x = ρs) := by
  rintro ⟨hcov, huniq⟩
  exact hm (no_finite_spontaneous_orientation τ τi T tr ρs hτi hiτ
    htr hstat hcov huniq hodd)

end Transfer

end NCG.Upstream
