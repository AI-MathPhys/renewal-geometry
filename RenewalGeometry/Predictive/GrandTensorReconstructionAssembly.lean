/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.TypedPredictiveCategoryExact
import RenewalGeometry.Predictive.TypedFinitePredictionExact
import RenewalGeometry.Predictive.DerivedPredictiveCarrierUniversalExact
import RenewalGeometry.Predictive.TypedHankelRealization
import RenewalGeometry.Predictive.HankelMinimality
import RenewalGeometry.Predictive.FiniteProcessCombTomography
import RenewalGeometry.Predictive.ContextualFutureNullIdeal
import RenewalGeometry.Predictive.ContextualEnvelope
import RenewalGeometry.Commutant.IntrinsicRegularTrace
import RenewalGeometry.Predictive.FlatWordPanelReconstruction
import RenewalGeometry.Predictive.RelationalCompletionProcessMorphismExact
import RenewalGeometry.Predictive.RelationalCompletion
import RenewalGeometry.Certificates.CertificateRecordBatch02

/-!
# Canonical predictive Grand-Tensor reconstruction: assembly
(`mt:grand-tensor`, emergent-spacetime manuscript)

The manuscript proves `mt:grand-tensor` clause by clause from the supplement theorems
(`thm:supp-right-congruence`, `thm:supp-minimal-record`, `thm:supp-persistence-derived`,
`thm:supp-hankel`, `thm:supp-comb-tomography`, `lem:supp-contextual-ideal`,
`thm:supp-word-flatness`, `cor:supp-future-operational-transfer`,
`prop:readable-relational-completion`).  Here each clause is stated as a proposition
(`GrandTensorReconstruction.clauseI`, …, `clauseVII`) whose content is the conjunction of the
universal properties of those theorems, instantiated on the typed carrier where one exists
(typed event grammars `FiniteTypedEventGrammar`, typed operational laws
`TypedPredictiveCategory.TypedOperationalLaw` and their category of reachable predictive
presentations), and `grand_tensor_reconstruction` proves all seven together.  The
finite-dimensionality hypothesis of the unbounded-horizon branch (a common finite-dimensional
sequential realization) is the finiteness of the matrix carriers of clauses (iii)–(v); on the
finite-horizon branch the predictive quotient is finite (`clauseI`).  Clause (vi)'s
"canonical without an independently supplied ledger, hidden state, …" is formalized as the
universal properties: every presentation and every future-operational compiler factors
uniquely through `Z^min`.
-/

open Matrix Filter
open scoped ComplexOrder

namespace RenewalGeometry

namespace GrandTensorReconstruction

open FiniteTypedEventGrammar TypedPredictiveCategory

/-- `mt:grand-tensor` (i): typed future equivalence is an equivalence and a right congruence on
every positive-probability branch; on the finite-horizon branch the predictive quotient is
finite at every cut type; and `Z^min` is the terminal (unique coarsest) reachable deterministic
predictive presentation of every typed operational law, onto which every presentation maps
surjectively. -/
def clauseI : Prop :=
  (∀ (G : FiniteTypedEventGrammar) (P : G.ConditionalLaw) (x : G.CutType),
      Equivalence (P.FutureEquivalent (x := x))) ∧
  (∀ (G : FiniteTypedEventGrammar) (P : G.ConditionalLaw) {x y : G.CutType}
      {h h' : G.History x} (hh : P.FutureEquivalent h h') (a : G.Letter x y)
      (hpos : 0 < P.prob h.word a),
      P.FutureEquivalent (h.snoc a (P.admissible_of_prob_pos hpos))
        (h'.snoc a (P.admissible_of_prob_pos (P.prob_eq_of_futureEquivalent hh a ▸ hpos)))) ∧
  (∀ (G : FiniteHorizonTypedEventGrammar) (P : G.toFiniteTypedEventGrammar.ConditionalLaw)
      (x : G.CutType), Finite (P.MinimalState x)) ∧
  (∀ L : TypedOperationalLaw, Nonempty (CategoryTheory.Limits.IsTerminal (minimal L)) ∧
      ∀ S : Presentation L, ∀ x, Function.Surjective ((toMinimal S).map x))

/-- `mt:grand-tensor` (ii): the successor maps are canonical, `T_a[h] = [h a]` on every
positive-probability branch, so the persistent event packet `(Z_n, A_{n+1}, Z_{n+1})` is a
function of the event process; in the untyped encoding, every word law is the product of the
successive branch laws along the derived state path and every realization maps uniquely onto
the derived carrier, intertwining branch functions and updates. -/
def clauseII : Prop :=
  (∀ (G : FiniteTypedEventGrammar) (P : G.ConditionalLaw) {x y : G.CutType} (a : G.Letter x y)
      (h : G.History x) (hpos : 0 < P.prob h.word a),
      P.transition a (P.project h) (by simpa using hpos)
        = P.project (h.snoc a (P.admissible_of_prob_pos hpos))) ∧
  (∀ {History Letter : Type} (P : DerivedPredictiveCarrierUniversal.PredictiveSystem History Letter)
      {State : Type} (R : P.Realization State),
      Equivalence P.FutureEquivalent ∧
      (∀ {h h' : History}, P.FutureEquivalent h h' → ∀ a : Letter, P.branch h a ≠ 0 →
        P.FutureEquivalent (P.step h a) (P.step h' a)) ∧
      (∀ (h : History) (w : List Letter), P.probability h w = P.pathWeight h w) ∧
      Function.Surjective
        (DerivedPredictiveCarrierUniversal.PredictiveSystem.Realization.toMinimal P R) ∧
      (∀ (s : State) (a : Letter), P.minimalBranch a
        (DerivedPredictiveCarrierUniversal.PredictiveSystem.Realization.toMinimal P R s)
          = R.rate s a) ∧
      (∀ (s : State) (a : Letter), R.rate s a ≠ 0 →
        DerivedPredictiveCarrierUniversal.PredictiveSystem.Realization.toMinimal P R (R.update s a)
          = P.minimalUpdate a
            (DerivedPredictiveCarrierUniversal.PredictiveSystem.Realization.toMinimal P R s)) ∧
      ∀ f : State → P.MinimalCarrier, (∀ h : History, f (R.stateOf h) = ⟦h⟧) →
        f = DerivedPredictiveCarrierUniversal.PredictiveSystem.Realization.toMinimal P R)

/-- `mt:grand-tensor` (iii): the state-conditioned Hankel quotient: the forward map of every
compatible re-indexing exists and is unique on the span of the Hankel columns, and every
finite-dimensional linear realization has a reachable-modulo-unobservable quotient isomorphic
to the Hankel core, so the Hankel quotient is the minimum linear predictor. -/
def clauseIII : Prop :=
  (∀ {P F P' F' : Type} (tbl : F → P → ℂ) (tbl' : F' → P' → ℂ) (ca : P → P') (fa : F' → F),
      (∀ (f' : F') (q : P), tbl' f' (ca q) = tbl (fa f') q) →
      ∃ A : (F → ℂ) →ₗ[ℂ] F' → ℂ,
        (∀ q : P, (A fun f => tbl f q) = fun f' => tbl' f' (ca q)) ∧
        (∀ (g : F → ℂ) (f' : F'), A g f' = g (fa f')) ∧
        ∀ A' : (F → ℂ) →ₗ[ℂ] F' → ℂ, (∀ q : P, (A' fun f => tbl f q) = fun f' => tbl' f' (ca q)) →
          ∀ m ∈ Submodule.span ℂ (Set.range fun q f => tbl f q), A' m = A m) ∧
  (∀ {P F N : Type} [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N] (tbl : F → P → ℂ)
      (nst : P → N) (ℓ : F → N →ₗ[ℂ] ℂ), (∀ (f : F) (q : P), ℓ f (nst q) = tbl f q) →
      Nonempty ((Submodule.span ℂ (Set.range nst) ⧸
          Submodule.comap (Submodule.span ℂ (Set.range nst)).subtype (⨅ f, LinearMap.ker (ℓ f)))
          ≃ₗ[ℂ] Submodule.span ℂ (Set.range fun q f => tbl f q)) ∧
        Module.finrank ℂ (Submodule.span ℂ (Set.range fun q f => tbl f q)) ≤ Module.finrank ℂ N)

/-- `mt:grand-tensor` (iv): the physical probability table reconstructs a unique Hermitian
Choi tensor independently of the tomographic frame; positive causal prefix combs exist exactly
under the causal trace recursion and are determined by their terminal comb; the canonical
square-root prefix memory has dimension `rank J`, and every other prefix-support-minimal
purification differs from it by a unique inner-product-preserving memory unitary. -/
def clauseIV : Prop :=
  (∀ {d : Type} [Fintype d] (F G : PhysicalChoiTomographyFrame d) (p : F.Probe → ℝ)
      (q : G.Probe → ℝ),
      (∀ M : Matrix d d ℂ, M.PosSemidef → M.trace.re ≤ 1 →
        (reconstructChoiTensor F p * M).trace = (reconstructChoiTensor G q * M).trace) →
      reconstructChoiTensor F p = reconstructChoiTensor G q) ∧
  (∀ {O I : Type} [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
      {R : CombPrefixFamily O I} {N : ℕ},
      Nonempty (FiniteDeterministicComb R N) ↔ IsDeterministicCombThrough R N) ∧
  (∀ {O I : Type} [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I] [Nonempty I]
      {R S : CombPrefixFamily O I} {N : ℕ}, IsDeterministicCombThrough R N →
      IsDeterministicCombThrough S N → R N = S N → ∀ k ≤ N, R k = S k) ∧
  (∀ {d h : Type} [Fintype d] [Fintype h] [DecidableEq d] (J : Matrix d d ℂ), J.PosSemidef →
      ∀ T : Matrix h d ℂ, T.conjTranspose * T = J →
        Module.finrank ℂ (CanonicalPrefixMemory J) = J.rank ∧
        ∃! U : CanonicalPrefixMemory J ≃ₗ[ℂ] LinearMap.range T.mulVecLin,
          (∀ u : d → ℂ, U ((canonicalPrefixFactor J).mulVecLin.rangeRestrict u)
            = T.mulVecLin.rangeRestrict u) ∧
          ∀ x y : CanonicalPrefixMemory J, star (x : d → ℂ) ⬝ᵥ (y : d → ℂ)
            = star ((U x : LinearMap.range T.mulVecLin) : h → ℂ) ⬝ᵥ
              ((U y : LinearMap.range T.mulVecLin) : h → ℂ))

/-- `mt:grand-tensor` (v): the contextual future-null set is a two-sided `*`-ideal and the
contextual quotient is the minimum context-preserving separated envelope; the normalized
regular trace is tracial, faithful, normalized and intrinsic; the word-Gram panels are
positive, become flat after a least finite depth at which the words span the represented
history algebra, and one further panel reconstructs the represented `*`-algebra. -/
def clauseV : Prop :=
  (∀ {A κ : Type} [Ring A] [StarRing A] (R : κ → A →+ ℂ),
      (contextualFutureNullIdeal R).IsTwoSided ∧
      ∀ q ∈ contextualFutureNullIdeal R, star q ∈ contextualFutureNullIdeal R) ∧
  (∀ {A B C ι : Type} [Ring A] [Ring B] [Ring C] (R : ι → A →+ ℂ) (π : A →+* B),
      Function.Surjective π → ∀ R' : ι → B →+ ℂ, (∀ (i : ι) (x : A), R i x = R' i (π x)) →
      (∀ x : A, π x = 0 → x ∈ contextualNull R) ∧
      (∀ θ : A →+* C, (∀ x ∈ contextualNull R, θ x = 0) → ∃ ψ : B →+* C, ∀ x : A, ψ (π x) = θ x) ∧
      ∀ θ : A →+* C, (∀ x : A, θ x = 0 ↔ x ∈ contextualNull R) →
        (∀ b : B, (∀ (i : ι) (u v : B), R' i (u * b * v) = 0) → b = 0) →
        ∀ ψ : B →+* C, (∀ x : A, ψ (π x) = θ x) → Function.Injective ψ) ∧
  (∀ {L : Type} [Fintype L] [Nonempty L] (nd : L → ℕ), (∀ l, 0 < nd l) →
      ((∀ a b : (l : L) → Matrix (Fin (nd l)) (Fin (nd l)) ℂ,
          ∑ l, (nd l : ℂ) * (a l * b l).trace = ∑ l, (nd l : ℂ) * (b l * a l).trace) ∧
        (∀ a : (l : L) → Matrix (Fin (nd l)) (Fin (nd l)) ℂ,
          ∑ l, (nd l : ℂ) * (star (a l) * a l).trace = 0 → a = 0) ∧
        Module.finrank ℂ ((l : L) → Matrix (Fin (nd l)) (Fin (nd l)) ℂ) = ∑ l, nd l ^ 2) ∧
      normalizedRegularTrace ((l : L) → Matrix (Fin (nd l)) (Fin (nd l)) ℂ) 1 = 1 ∧
      ∀ {B : Type} [Ring B] [Algebra ℂ B] [Module.Free ℂ B] [Module.Finite ℂ B]
        (e : ((l : L) → Matrix (Fin (nd l)) (Fin (nd l)) ℂ) ≃ₐ[ℂ] B)
        (a : (l : L) → Matrix (Fin (nd l)) (Fin (nd l)) ℂ),
        normalizedRegularTrace B (e a)
          = normalizedRegularTrace ((l : L) → Matrix (Fin (nd l)) (Fin (nd l)) ℂ) a) ∧
  (∀ {M Γ : Type} [Fintype M] [DecidableEq M] [Nonempty M] (gen : Γ → Matrix M M ℂ)
      [(r : ℕ) → Fintype (FiniteGrandTensor.Words Γ r)] (inv : Γ → Γ),
      (∀ γ, star (gen γ) = gen (inv γ)) →
      (∀ (r : ℕ) (c : FiniteGrandTensor.Words Γ r → ℂ),
        0 ≤ (∑ v, ∑ w, star (c v) * c w * FiniteGrandTensor.wordGramLevel gen r v w).re) ∧
      ∃ r : ℕ,
        ((gramPanel gen r).rank = (gramPanel gen (r + 1)).rank ∧
          ∀ r' < r, (gramPanel gen r').rank ≠ (gramPanel gen (r' + 1)).rank) ∧
        FiniteGrandTensor.historyWordSpan gen r =
          Subalgebra.toSubmodule (FiniteGrandTensor.historyAlgebra gen).toSubalgebra ∧
        (∀ s, r ≤ s → FiniteGrandTensor.historyWordSpan gen s
          = FiniteGrandTensor.historyWordSpan gen r) ∧
        ∀ (M' : Type) [Fintype M'] [DecidableEq M'] [Nonempty M'] (gen' : Γ → Matrix M' M' ℂ),
          (∀ γ, star (gen' γ) = gen' (inv γ)) → gramPanel gen (r + 1) = gramPanel gen' (r + 1) →
          ∃ ψ : FiniteGrandTensor.historyAlgebra gen ≃⋆ₐ[ℂ] FiniteGrandTensor.historyAlgebra gen',
            (∀ w : List Γ, ψ (wordElt gen w) = wordElt gen' w) ∧
            ∀ (Δ : Set Γ) (x : FiniteGrandTensor.historyAlgebra gen),
              (x : Matrix M M ℂ) ∈ coreAlgebra gen Δ ↔
                ((ψ x : FiniteGrandTensor.historyAlgebra gen') : Matrix M' M' ℂ) ∈ coreAlgebra gen' Δ)

/-- `mt:grand-tensor` (vi): every reachable deterministic predictive presentation factors
uniquely through `Z^min` (unique morphism, sending `s(h)` to `[h]`), and every
future-operational compiler (a readout constant on equal future signatures) factors uniquely
through the minimal predictive quotient. -/
def clauseVI : Prop :=
  (∀ (L : TypedOperationalLaw) (S : Presentation L),
      (∀ {x : L.grammar.CutType} (h : L.grammar.History x),
        (toMinimal S).map x (S.stateOf h) = L.law.project h) ∧
      ∀ f g : S ⟶ minimal L, f = g) ∧
  (∀ {State Sig V : Type} (σ : State → Sig) (D : State → V),
      (∀ s t : State, σ s = σ t → D s = D t) →
      ∃! Dbar : minimalPredictiveQuotient σ → V, D = Dbar ∘ minimalPredictiveProjection σ)

/-- `mt:grand-tensor` (vii): a finite same-history readable enrichment by normalized
conditional kernels is a surjective process quotient of the underlying operational process
(its forgetful image intertwines every branch word), and every word-record presentation has
the minimal faithful all-future quotient with its universal property. -/
def clauseVII : Prop :=
  (∀ {O Γ Ξ Z d : Type} [Fintype Γ] [Fintype Ξ] [Fintype Z] [DecidableEq Z] [Nonempty Z]
      (K : RelationalCompletion.Kernel O Γ Ξ Z) (Φ : O → Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ),
      Function.Surjective
        (RelationalCompletionProcessMorphism.canonicalProcessMorphism K Φ).forget ∧
      ∀ (word : List O) (ρ : Z → Matrix d d ℂ),
        (RelationalCompletionProcessMorphism.canonicalProcessMorphism K Φ).forget
          (RelationalCompletionProcessMorphism.FiniteWordProcessMorphism.run
            (RelationalCompletionProcessMorphism.canonicalProcessMorphism K Φ).newStep word ρ)
        = RelationalCompletionProcessMorphism.FiniteWordProcessMorphism.run
            (RelationalCompletionProcessMorphism.canonicalProcessMorphism K Φ).oldStep word
            ((RelationalCompletionProcessMorphism.canonicalProcessMorphism K Φ).forget ρ)) ∧
  (∀ {A R D V : Type} (M : WordRecordMachine A R D V),
    WordRecordMachine.MinimalRecordExact.{0, 0, 0, 0, 0} M)

/-- **`mt:grand-tensor`, canonical predictive Grand-Tensor reconstruction.**  All seven clauses
hold. -/
theorem grand_tensor_reconstruction :
    clauseI ∧ clauseII ∧ clauseIII ∧ clauseIV ∧ clauseV ∧ clauseVI ∧ clauseVII := by
  refine ⟨⟨fun G P x => P.futureEquivalent_equivalence x,
      fun G P _ _ _ _ hh a hpos => P.futureEquivalent_snoc hh a hpos,
      fun G P x => G.finite_minimalState P x,
      fun L => ⟨⟨minimal_isTerminal⟩, fun S x => (toMinimal_spec S).2.1 x⟩⟩,
    ⟨fun G P _ _ a h hpos => P.transition_project a h hpos,
      fun P _ R => P.derived_predictive_relation_carrier R⟩,
    ⟨fun tbl tbl' ca fa h => typed_hankel_realization tbl tbl' ca fa h,
      fun tbl nst ℓ h => hankel_minimality tbl nst ℓ h⟩,
    ⟨fun F G p q h => reconstructChoiTensor_frame_independent F G p q h,
      finiteDeterministicComb_iff,
      fun hR hS hN k hk => causalCombPrefixes_unique_from_terminal hR hS hN k hk,
      fun J hJ T hT => finiteCombPrefix_minimalPurification_unique J hJ T hT⟩,
    ⟨fun R => ⟨contextualFutureNullIdeal_isTwoSided R,
        fun _ hq => contextualFutureNullIdeal_star_mem R hq⟩,
      fun R π hπ R' hR => contextual_envelope_universal R π hπ R' hR,
      fun nd hnd => regular_trace_exact nd hnd,
      fun gen _ inv hinv => flat_word_reconstruction gen inv hinv⟩,
    ⟨fun L S => ⟨(toMinimal_spec S).1, (toMinimal_spec S).2.2⟩,
      fun σ D hD => upstream_compiler_transfer σ D hD⟩,
    ⟨fun K Φ => RelationalCompletionProcessMorphism.relational_completion_is_process_quotient K Φ,
      fun M => RelationalCompletion.future_minimality M⟩⟩

end GrandTensorReconstruction

end RenewalGeometry
