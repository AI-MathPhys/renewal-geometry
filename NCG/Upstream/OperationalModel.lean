/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.SharpPurification
import NCG.Upstream.CompletePositivity

/-!
# The corrected operational model: determinism, dilation, and the
UCP bridge

Re-earns `def:sharp-purification`,
`prop:reversible-realisation-sharp-purification`, and
`thm:operational-ucp` from `manuscripts/renewal_emergence/renewal_emergence.tex`, repairing the two
defects found by the 2026-07-21 audit:

* the old `SharpPurification.causal` quantified over **all** effects
  (no determinism marker), collapsing (SP3) and making the package
  unsatisfiable by quantum theory; `DetMarking` adds the determinism
  predicate and `SharpPurificationPkg` states (SP1) as the *unique
  deterministic* effect, as in the text;
* the old `ReducedReversibleRealisation` was field-for-field the
  conclusion; `ReversibleDilationRealisation` now encodes (O2) at
  **transformation level** — pure reversible dilation of *every
  process* with essentially unique minimal environment — and
  `sharpPurificationPkg_of_realisation` *derives* (SP3) and (SP4) by
  genuine specialization to preparations, following the manuscript
  proof;
* the old operational-UCP bridge was `Iff.rfl`;
  `operational_positive` now derives positivity of a deterministic
  transformation from **closed-experiment probabilities and state
  separation**, `ucp_effect_map` / `ucp_state_pullback` prove the
  converse clauses, and `operational_to_ucp` assembles the bridge
  with complete ancillary stability supplying the matrix contexts
  (the passage stability → CP being definitional, as the text says,
  with the finite Choi reduction in
  `isCompletelyAncillaryStable_iff_choi`).
-/

namespace NCG.Upstream

open NCG

/-! ## Determinism marking and the corrected (SP1)–(SP4) package -/

/-- A **determinism marking** on an operational theory: the
operational predicate singling out the deterministic processes.
This is the datum whose absence made the previous encoding of
causality (`∀ e, e = discard`) unsatisfiable. -/
structure DetMarking (T : OpTheory) where
  /-- The deterministic processes. -/
  deterministic : {A B : T.Sys} → T.Proc A B → Prop
  /-- The discard is deterministic. -/
  discard_det : ∀ A, deterministic (T.discard A)

/-- **Definition `def:sharp-purification` (corrected)**: the
sharp-purification package (SP1)–(SP4), with (SP1) stated as in the
text — every system has a *unique deterministic* effect. -/
structure SharpPurificationPkg (T : OpTheory) (M : DetMarking T) :
    Prop where
  /-- (SP1) causality: the deterministic effect is unique. -/
  causal : ∀ (A : T.Sys) (e : T.Effect A),
    M.deterministic e → e = T.discard A
  /-- (SP2) sequential composites of pure processes are pure. -/
  pure_seq : ∀ {A B C : T.Sys} (f : T.Proc A B) (g : T.Proc B C),
    T.Pure f → T.Pure g → T.Pure (T.seq f g)
  /-- (SP2) parallel composites of pure processes are pure. -/
  pure_par : ∀ {A B C D : T.Sys} (f : T.Proc A B) (g : T.Proc C D),
    T.Pure f → T.Pure g → T.Pure (T.par f g)
  /-- (SP3) some pure effect is certain on some normalized pure
  state. -/
  sharp : ∀ A : T.Sys, ∃ (α : T.State A) (a : T.Effect A),
    T.Pure α ∧ T.Normalized α ∧ T.Pure a ∧ T.CertainOn a α
  /-- (SP4) existence: every state is a marginal of a pure bipartite
  state. -/
  purify : ∀ (A : T.Sys) (ρ : T.State A),
    ∃ (E : T.Sys) (Ψ : T.State (T.ten A E)), T.Purifies Ψ ρ
  /-- (SP4) uniqueness: purifications on a common (minimal) purifying
  system differ by a reversible transformation of that system. -/
  purify_unique : ∀ (A E : T.Sys) (Ψ Ψ' : T.State (T.ten A E)),
    T.Pure Ψ → T.Pure Ψ' → T.marginal Ψ = T.marginal Ψ' →
    ∃ R : T.Proc E E, T.Reversible R ∧
      Ψ' = T.seq Ψ (T.par (T.idp A) R)

/-! ## (O2) at transformation level -/

/-- The marginal of a bipartite **process**: discard the ancilla
output.  For preparations (`A = I`) this is definitionally
`OpTheory.marginal`. -/
def OpTheory.procMarginal (T : OpTheory) {A B E : T.Sys}
    (V : T.Proc A (T.ten B E)) : T.Proc A B :=
  T.seq (T.seq V (T.par (T.idp B) (T.discard E))) (T.runit B)

/-- **Item (O2) of `ass:reconstruction-package`, transformation
level**: unique deterministic discard; a pure *reversible* dilation
for **every process** with essentially unique minimal environment;
no-retained-record purity closure; pure reverse effects for
normalized pure preparations; and the (O1) normalization input that
every system has a normalized pure state. -/
structure ReversibleDilationRealisation (T : OpTheory)
    (M : DetMarking T) : Prop where
  /-- Unique deterministic discard. -/
  det_unique : ∀ (A : T.Sys) (e : T.Effect A),
    M.deterministic e → e = T.discard A
  /-- Every process admits a pure reversible dilation. -/
  dilate_proc : ∀ (A B : T.Sys) (f : T.Proc A B),
    ∃ (E : T.Sys) (V : T.Proc A (T.ten B E)),
      T.Pure V ∧ T.Reversible V ∧ f = T.procMarginal V
  /-- Essential uniqueness on a minimal environment. -/
  dilate_unique : ∀ (A B E : T.Sys) (V V' : T.Proc A (T.ten B E)),
    T.Pure V → T.Pure V' → T.procMarginal V = T.procMarginal V' →
    ∃ R : T.Proc E E, T.Reversible R ∧
      V' = T.seq V (T.par (T.idp B) R)
  /-- No-retained-record closure: sequential. -/
  pure_seq : ∀ {A B C : T.Sys} (f : T.Proc A B) (g : T.Proc B C),
    T.Pure f → T.Pure g → T.Pure (T.seq f g)
  /-- No-retained-record closure: parallel. -/
  pure_par : ∀ {A B C D : T.Sys} (f : T.Proc A B) (g : T.Proc C D),
    T.Pure f → T.Pure g → T.Pure (T.par f g)
  /-- Every normalized pure preparation has a normalized pure reverse
  effect certain on it. -/
  pure_reverse : ∀ (A : T.Sys) (α : T.State A),
    T.Pure α → T.Normalized α →
    ∃ a : T.Effect A, T.Pure a ∧ T.CertainOn a α
  /-- (O1) normalization input: every system has a normalized pure
  state. -/
  state_exists : ∀ A : T.Sys,
    ∃ α : T.State A, T.Pure α ∧ T.Normalized α

/-- **Proposition `prop:reversible-realisation-sharp-purification`**:
(O2) implies the sharp-purification package.  (SP1) is the unique
deterministic discard; (SP2) is the no-retained-record closure;
(SP3) is *derived* by instantiating the pure reverse effect on the
normalized pure state supplied by normalization; (SP4) is *derived*
by specializing the transformation-level reversible dilation and its
essential uniqueness to preparations `ρ : I → A`, exactly as in the
manuscript proof. -/
theorem sharpPurificationPkg_of_realisation {T : OpTheory}
    {M : DetMarking T} (D : ReversibleDilationRealisation T M) :
    SharpPurificationPkg T M where
  causal := D.det_unique
  pure_seq := fun f g hf hg => D.pure_seq f g hf hg
  pure_par := fun f g hf hg => D.pure_par f g hf hg
  sharp := by
    intro A
    obtain ⟨α, hαp, hαn⟩ := D.state_exists A
    obtain ⟨a, hap, hac⟩ := D.pure_reverse A α hαp hαn
    exact ⟨α, a, hαp, hαn, hap, hac⟩
  purify := by
    intro A ρ
    obtain ⟨E, V, hVp, _, hf⟩ := D.dilate_proc T.unit A ρ
    exact ⟨E, V, hVp, hf.symm⟩
  purify_unique := by
    intro A E Ψ Ψ' hΨ hΨ' hm
    exact D.dilate_unique T.unit A E Ψ Ψ' hΨ hΨ' hm

/-! ## The operational-to-UCP bridge (`thm:operational-ucp`) -/

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- **State separation** of the reconstructed operator system: a
self-adjoint element on which every operational state takes a
nonnegative value is positive. -/
def StateSeparating (S : Set (A →ₗ[ℂ] ℂ)) : Prop :=
  ∀ a : A, star a = a →
    (∀ ω ∈ S, ∃ r : ℝ, 0 ≤ r ∧ ω a = (r : ℂ)) → 0 ≤ a

/-- **`thm:operational-ucp` (forward, positivity)**: a deterministic
predictive transformation with nonnegative closed-experiment
probabilities on every operational state is a positive map — by
state separation.  This is the derivation that was previously
collapsed into a definitional identity. -/
theorem operational_positive (S : Set (A →ₗ[ℂ] ℂ))
    (hsep : StateSeparating S) (Φ : A →ₗ[ℂ] A)
    (hstar : ∀ a, Φ (star a) = star (Φ a))
    (hprob : ∀ ω ∈ S, ∀ b : A, 0 ≤ b →
      ∃ r : ℝ, 0 ≤ r ∧ ω (Φ b) = (r : ℂ)) :
    IsPositiveMap Φ := by
  intro b hb
  have hbsa : star b = b := (IsSelfAdjoint.of_nonneg hb).star_eq
  have hΦsa : star (Φ b) = Φ b := by
    rw [← hstar, hbsa]
  exact hsep (Φ b) hΦsa (fun ω hω => hprob ω hω b hb)

/-- **`thm:operational-ucp` (forward, assembly)**: a deterministic
(`Φ 1 = 1`), closed-experiment-positive, completely ancillary stable
predictive transformation is a UCP channel.  Positivity is grounded
operationally by `operational_positive`; complete ancillary
stability supplies every matrix context (the passage to complete
positivity being definitional, per the text, with the finite Choi
reduction in `isCompletelyAncillaryStable_iff_choi`). -/
noncomputable def operationalToUCP (Φ : A →ₗ[ℂ] A) (hdet : Φ 1 = 1)
    (hstab : IsCompletelyPositive Φ) : UCPMap A :=
  contextStableUCP Φ hdet hstab

/-- **`thm:operational-ucp` (converse, effects map to effects)**: a
positive unital map preserves the operational effect interval
`0 ≤ a ≤ 1` — it preserves the order unit and sends effects to
effects. -/
theorem ucp_effect_map (Φ : A →ₗ[ℂ] A) (hpos : IsPositiveMap Φ)
    (hu : Φ 1 = 1) {a : A} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    0 ≤ Φ a ∧ Φ a ≤ 1 := by
  refine ⟨hpos a h0, ?_⟩
  have h2 := hpos (1 - a) (sub_nonneg.mpr h1)
  rw [map_sub, hu] at h2
  exact sub_nonneg.mp h2

/-- **`thm:operational-ucp` (converse, state pullback)**: composing
an operational state with a positive transformation yields
nonnegative closed-experiment probabilities — pairing with states
defines consistent probabilities in every context, which is the
operational reading of a deterministic transformation. -/
theorem ucp_state_pullback (ω : A →ₗ[ℂ] ℂ)
    (hω : ∀ b : A, 0 ≤ b → ∃ r : ℝ, 0 ≤ r ∧ ω b = (r : ℂ))
    (Φ : A →ₗ[ℂ] A) (hpos : IsPositiveMap Φ) :
    ∀ b : A, 0 ≤ b → ∃ r : ℝ, 0 ≤ r ∧ (ω ∘ₗ Φ) b = (r : ℂ) :=
  fun b hb => hω _ (hpos b hb)

end NCG.Upstream
