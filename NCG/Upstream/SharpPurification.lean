/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The sharp-purification package and its derivation from reduced
# reversible realisation

Definition `def:sharp-purification` and Proposition
`prop:reversible-realisation-sharp-purification` of
`manuscripts/renewal_emergence/renewal_emergence.tex`, as a faithful operational interface.

`OpTheory` is a minimal finite operational process-theory carrier:
systems with a trivial system and parallel composition, processes
with sequential and parallel composition, the right unitor, a
deterministic discard, scalars, and the operational purity and
reversibility predicates.  States are processes out of the trivial
system, effects are processes into it, and an effect is *certain* on
a state when their composite is the unit scalar.

* `SharpPurification` — the package (SP1)–(SP4): causality (unique
  deterministic effect), purity closure under sequential and
  parallel composition, pure sharpness (a pure effect certain on a
  normalized pure state), and purification with essential uniqueness
  up to a reversible transformation of the purifying system;
* `ReducedReversibleRealisation` — the operational content of clause
  (O2) of `ass:reconstruction-package`: unique discard, pure
  reversible dilation of states with essentially unique minimal
  environment, no-retained-record purity closure, and pure reverse
  effects for normalized pure preparations;
* `SharpPurification.ofRealisation` — **the proposition**: (O2)
  implies the sharp-purification package.
-/

namespace NCG.Upstream

/-- A minimal finite operational process-theory carrier. -/
structure OpTheory where
  /-- Systems. -/
  Sys : Type*
  /-- Processes between systems. -/
  Proc : Sys → Sys → Type*
  /-- The trivial system. -/
  unit : Sys
  /-- Sequential composition (diagrammatic order). -/
  seq : {A B C : Sys} → Proc A B → Proc B C → Proc A C
  /-- Parallel composition of systems. -/
  ten : Sys → Sys → Sys
  /-- Parallel composition of processes. -/
  par : {A B C D : Sys} → Proc A B → Proc C D → Proc (ten A C) (ten B D)
  /-- Identities. -/
  idp : (A : Sys) → Proc A A
  /-- The right unitor `A ⊗ I ≅ A`. -/
  runit : (A : Sys) → Proc (ten A unit) A
  /-- The deterministic discard. -/
  discard : (A : Sys) → Proc A unit
  /-- The unit scalar (certainty). -/
  scalarOne : Proc unit unit
  /-- Operational purity (non-refinability). -/
  Pure : {A B : Sys} → Proc A B → Prop
  /-- Operational reversibility. -/
  Reversible : {A B : Sys} → Proc A B → Prop

namespace OpTheory

variable (T : OpTheory)

/-- States of a system. -/
def State (A : T.Sys) := T.Proc T.unit A

/-- Effects on a system. -/
def Effect (A : T.Sys) := T.Proc A T.unit

/-- A state is normalized when the discard is certain on it. -/
def Normalized {A : T.Sys} (ρ : T.State A) : Prop :=
  T.seq ρ (T.discard A) = T.scalarOne

/-- An effect is certain on a state when their composite is the unit
scalar. -/
def CertainOn {A : T.Sys} (a : T.Effect A) (ρ : T.State A) : Prop :=
  T.seq ρ a = T.scalarOne

/-- The marginal of a bipartite state: discard the second factor. -/
def marginal {A E : T.Sys} (Ψ : T.State (T.ten A E)) : T.State A :=
  T.seq (T.seq Ψ (T.par (T.idp A) (T.discard E))) (T.runit A)

/-- `Ψ` purifies `ρ` on the purifying system `E`. -/
def Purifies {A E : T.Sys} (Ψ : T.State (T.ten A E)) (ρ : T.State A) :
    Prop :=
  T.Pure Ψ ∧ T.marginal Ψ = ρ

end OpTheory

/-- **Definition `def:sharp-purification`**: the sharp-purification
package (SP1)–(SP4). -/
structure SharpPurification (T : OpTheory) : Prop where
  /-- (SP1) causality: the deterministic effect is unique. -/
  causal : ∀ (A : T.Sys) (e : T.Effect A), e = T.discard A
  /-- (SP2) sequential composites of pure processes are pure. -/
  pure_seq : ∀ {A B C : T.Sys} (f : T.Proc A B) (g : T.Proc B C),
    T.Pure f → T.Pure g → T.Pure (T.seq f g)
  /-- (SP2) parallel composites of pure processes are pure. -/
  pure_par : ∀ {A B C D : T.Sys} (f : T.Proc A B) (g : T.Proc C D),
    T.Pure f → T.Pure g → T.Pure (T.par f g)
  /-- (SP3) pure sharpness: some pure effect is certain on some
  normalized pure state. -/
  sharp : ∀ A : T.Sys, ∃ (α : T.State A) (a : T.Effect A),
    T.Pure α ∧ T.Normalized α ∧ T.Pure a ∧ T.CertainOn a α
  /-- (SP4) existence of purifications. -/
  purify : ∀ {A : T.Sys} (ρ : T.State A), ∃ (E : T.Sys)
    (Ψ : T.State (T.ten A E)), T.Purifies Ψ ρ
  /-- (SP4) essential uniqueness: two purifications on the same
  purifying system differ by a reversible transformation of that
  system. -/
  purify_unique : ∀ {A E : T.Sys} (Ψ Ψ' : T.State (T.ten A E))
    (ρ : T.State A), T.Purifies Ψ ρ → T.Purifies Ψ' ρ →
    ∃ u : T.Proc E E, T.Reversible u
      ∧ T.seq Ψ (T.par (T.idp A) u) = Ψ'

/-- **Clause (O2) of `ass:reconstruction-package`**: reduced
sharp-reversible realisation — unique deterministic discard, pure
dilation with essentially unique environment, no-retained-record
purity closure, and pure reverse effects certain on normalized pure
preparations. -/
structure ReducedReversibleRealisation (T : OpTheory) : Prop where
  /-- Unique deterministic discard. -/
  unique_discard : ∀ (A : T.Sys) (e : T.Effect A), e = T.discard A
  /-- Every state admits a pure dilation with pure environment. -/
  dilate : ∀ {A : T.Sys} (ρ : T.State A), ∃ (E : T.Sys)
    (Ψ : T.State (T.ten A E)), T.Pure Ψ ∧ T.marginal Ψ = ρ
  /-- Essential uniqueness of dilations on a common minimal
  environment, up to a reversible environment change. -/
  dilate_unique : ∀ {A E : T.Sys} (Ψ Ψ' : T.State (T.ten A E)),
    T.Pure Ψ → T.Pure Ψ' → T.marginal Ψ = T.marginal Ψ' →
    ∃ u : T.Proc E E, T.Reversible u
      ∧ T.seq Ψ (T.par (T.idp A) u) = Ψ'
  /-- No-retained-record closure: sequential composites of pure
  processes are pure. -/
  pure_seq : ∀ {A B C : T.Sys} (f : T.Proc A B) (g : T.Proc B C),
    T.Pure f → T.Pure g → T.Pure (T.seq f g)
  /-- No-retained-record closure: parallel composites of pure
  processes are pure. -/
  pure_par : ∀ {A B C D : T.Sys} (f : T.Proc A B) (g : T.Proc C D),
    T.Pure f → T.Pure g → T.Pure (T.par f g)
  /-- Every system has a normalized pure preparation. -/
  pure_state : ∀ A : T.Sys, ∃ α : T.State A,
    T.Pure α ∧ T.Normalized α
  /-- Every normalized pure preparation has a normalized pure
  reverse effect certain on it. -/
  pure_reverse : ∀ {A : T.Sys} (α : T.State A), T.Pure α →
    T.Normalized α → ∃ a : T.Effect A, T.Pure a ∧ T.CertainOn a α

/-- **Proposition
`prop:reversible-realisation-sharp-purification`**: reduced
sharp-reversible realisation implies the sharp-purification
package. -/
theorem SharpPurification.ofRealisation {T : OpTheory}
    (h : ReducedReversibleRealisation T) : SharpPurification T where
  causal := h.unique_discard
  pure_seq := h.pure_seq
  pure_par := h.pure_par
  sharp := by
    intro A
    obtain ⟨α, hpure, hnorm⟩ := h.pure_state A
    obtain ⟨a, hapure, hacert⟩ := h.pure_reverse α hpure hnorm
    exact ⟨α, a, hpure, hnorm, hapure, hacert⟩
  purify := by
    intro A ρ
    obtain ⟨E, Ψ, hΨpure, hΨmarg⟩ := h.dilate ρ
    exact ⟨E, Ψ, hΨpure, hΨmarg⟩
  purify_unique := by
    intro A E Ψ Ψ' ρ hΨ hΨ'
    exact h.dilate_unique Ψ Ψ' hΨ.1 hΨ'.1 (hΨ.2.trans hΨ'.2.symm)

end NCG.Upstream
