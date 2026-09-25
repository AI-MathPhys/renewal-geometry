/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.TypedEventGrammar
import RenewalGeometry.Predictive.FiniteProcessCombTomography

/-!
# Finite conditional operational renewal law
  (`def:supp-operational-datum`, `eq:supp-one-step-law`, `eq:supp-chain-law`;
  emergent-spacetime manuscript)

A finite conditional operational renewal law on a finite typed event grammar
`G` (`def:supp-event-grammar`, `FiniteTypedEventGrammar`) consists of:

* the one-step law `p_X(a | h) ∈ [0, 1]`, `∑_{a ∈ Σ_{X,h}} p_X(a | h) = 1` for
  every reachable history (`eq:supp-one-step-law`) — the inherited
  `FiniteTypedEventGrammar.ConditionalLaw`, whose chain law
  `ConditionalLaw.wordProb` is `eq:supp-chain-law`
  (`p_X(w | h) = ∏_j p_X(a_j | h a_1 ⋯ a_{j-1})`, `p_X(ε_x | h) = 1`);
* on every exposed operator port `p` an input leg `In p` and an output leg
  `Out p`, so that the exposed Hermitian Choi-coordinate space of the port is
  the Hermitian part of `Matrix (In p × Out p) (In p × Out p) ℂ`, and a
  finite physical CP frame on it (`PhysicalChoiTomographyFrame`: positive,
  trace-normalized probes with Hermitian duals) whose real span is the full
  Hermitian space (`frame_spans`), every probe of which is one of the
  grammar's physical intervention letters (`interventionLetter`);
* the induced multitime frame probabilities.  By `thm:supp-comb-tomography`
  (proved: `reconstructChoiTensor_pairing`, `finiteDeterministicComb_iff`)
  the multilinear intervention probabilities on a chronological sequence of
  ports are represented by a unique Hermitian tensor on the Kronecker product
  of the slot Choi spaces, and they are affine under randomization, additive
  under coarse graining, normalized on complete instruments, causal under
  deterministic discard, compatible on common prefixes and satisfy the finite
  positivity conditions exactly when that tensor family satisfies the process
  comb conditions `eq:supp-comb-conditions`
  `R^{(N)} ⪰ 0`, `Tr_{2k-1} R^{(k)} = I_{2k-2} ⊗ R^{(k-1)}`, `R^{(0)} = 1`.
  The datum therefore carries the tensor family `tensor ps` (indexed by the
  list of ports of the slots, newest slot first, as in `CombCarrier`) with
  the fields `tensor_posSemidef`, `tensor_causal` (partial trace over the
  newest output leg equals the identity on the newest input leg tensored with
  the prefix tensor) and `tensor_nil`; the multitime probability of a tuple
  of slot Choi matrices is the trace pairing `multitimeProb`
  (`multitimeProb_add`, `multitimeProb_smul`: additivity under coarse
  graining and affinity under randomization in the newest slot;
  `multitimeProb_nil`: the empty sequence has probability one);
* terminal Reads included as terminal event outcomes: a probability row
  `readProb h r` on the outcomes of every terminal Read after every history.

No state label, persistent relation object, metric, scheduler, connection or
spacetime semantic is assigned; the multitime layer is stated in the finite
matrix language of `FiniteProcessCombTomography`.
-/

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

namespace RenewalGeometry

/-! ## Kronecker slot carriers indexed by a list of ports -/

section Slots

variable {P : Type} (C : P → Type)

/-- The Kronecker index of a chronological list of slots (newest first):
`SlotIndex C [p₁, …, pₙ] = C p₁ × (C p₂ × (⋯ × Unit))`. -/
def SlotIndex : List P → Type
  | [] => Unit
  | p :: ps => C p × SlotIndex ps

instance slotIndexFintype [∀ p, Fintype (C p)] : ∀ ps : List P, Fintype (SlotIndex C ps)
  | [] => inferInstanceAs (Fintype Unit)
  | p :: ps => by
      letI := slotIndexFintype ps
      exact inferInstanceAs (Fintype (C p × SlotIndex C ps))

instance slotIndexDecidableEq [∀ p, DecidableEq (C p)] :
    ∀ ps : List P, DecidableEq (SlotIndex C ps)
  | [] => inferInstanceAs (DecidableEq Unit)
  | p :: ps => by
      letI := slotIndexDecidableEq ps
      exact inferInstanceAs (DecidableEq (C p × SlotIndex C ps))

/-- A tuple of slot Choi matrices, one on each port of the list. -/
def SlotTuple : List P → Type
  | [] => Unit
  | p :: ps => Matrix (C p) (C p) ℂ × SlotTuple ps

section

variable [∀ p, DecidableEq (C p)]

/-- The Kronecker product `C₁ ⊗ C₂ ⊗ ⋯ ⊗ Cₙ` of a slot tuple. -/
def slotKron : ∀ ps : List P, SlotTuple C ps → Matrix (SlotIndex C ps) (SlotIndex C ps) ℂ
  | [], _ => 1
  | _ :: ps, (M, Ms) => M ⊗ₖ slotKron ps Ms

@[simp] theorem slotKron_nil (u : SlotTuple C []) : slotKron C [] u = 1 := rfl

@[simp] theorem slotKron_cons (p : P) (ps : List P) (M : Matrix (C p) (C p) ℂ)
    (Ms : SlotTuple C ps) :
    slotKron C (p :: ps) (M, Ms) = M ⊗ₖ slotKron C ps Ms := rfl

end

/-- Real part of the trace pairing is additive in the second factor. -/
theorem trace_mul_add_re {n : Type} [Fintype n] (T X Y : Matrix n n ℂ) :
    ((T * (X + Y)).trace).re = ((T * X).trace).re + ((T * Y).trace).re := by
  simp [Matrix.mul_add]

/-- Real part of the trace pairing is real-homogeneous in the second factor. -/
theorem trace_mul_smul_re {n : Type} [Fintype n] (T X : Matrix n n ℂ) (r : ℝ) :
    ((T * ((r : ℂ) • X)).trace).re = r * ((T * X).trace).re := by
  simp [Matrix.mul_smul]

end Slots

/-! ## Newest-slot partial trace -/

section PartialTrace

variable {I O S : Type} [Fintype O]

/-- Partial trace over the newest output leg `O` of a tensor on
`(I × O) × S`: the Choi-tensor analogue of `combOutputTrace` with
port-dependent legs. -/
def newestOutputTrace (R : Matrix ((I × O) × S) ((I × O) × S) ℂ) :
    Matrix (I × S) (I × S) ℂ :=
  fun is js => ∑ o : O, R ((is.1, o), is.2) ((js.1, o), js.2)

end PartialTrace

/-! ## The datum -/

namespace FiniteTypedEventGrammar

variable (G : FiniteTypedEventGrammar)

/-- **`def:supp-operational-datum`.**  A finite conditional operational
renewal law on the typed event grammar `G`: the one-step law and chain law
(`toConditionalLaw`, `eq:supp-one-step-law`, `eq:supp-chain-law`); a spanning
finite physical CP frame of intervention letters on the exposed Hermitian
Choi space of every port; the multitime intervention probabilities carried
by a Hermitian tensor family satisfying the finite process-comb conditions
of `thm:supp-comb-tomography` (positivity, causal partial-trace recursion,
normalization); and the terminal-Read outcome rows. -/
structure FiniteConditionalOperationalRenewalLaw extends G.ConditionalLaw where
  /-- Input leg of the exposed port `p`. -/
  In : G.Port → Type
  /-- Output leg of the exposed port `p`. -/
  Out : G.Port → Type
  [inFintype : ∀ p, Fintype (In p)]
  [outFintype : ∀ p, Fintype (Out p)]
  [inDecidableEq : ∀ p, DecidableEq (In p)]
  [outDecidableEq : ∀ p, DecidableEq (Out p)]
  /-- The finite physical CP frame on the Hermitian Choi-coordinate space of
  the port `p`. -/
  frame : ∀ p : G.Port, PhysicalChoiTomographyFrame (In p × Out p)
  /-- The real span of the frame is the full Hermitian space. -/
  frame_spans : ∀ (p : G.Port) (H : Matrix (In p × Out p) (In p × Out p) ℂ), H.IsHermitian →
    H ∈ Submodule.span ℝ (Set.range (frame p).probe)
  /-- Every frame probe is one of the physical intervention letters. -/
  interventionLetter : ∀ p : G.Port, (frame p).Probe → G.InterventionOutcome
  /-- Distinct probes are distinct letters. -/
  interventionLetter_injective :
    Function.Injective (fun x : Σ p : G.Port, (frame p).Probe => interventionLetter x.1 x.2)
  /-- The Hermitian tensor `R^{(N)}` representing the multitime intervention
  probabilities on the chronological port sequence `ps` (newest first). -/
  tensor : ∀ ps : List G.Port,
    Matrix (SlotIndex (fun p => In p × Out p) ps) (SlotIndex (fun p => In p × Out p) ps) ℂ
  /-- `R^{(N)} ⪰ 0`: the finite positivity conditions. -/
  tensor_posSemidef : ∀ ps, (tensor ps).PosSemidef
  /-- `R^{(0)} = 1`: normalization. -/
  tensor_nil : tensor [] = 1
  /-- `Tr_{2k-1} R^{(k)} = I_{2k-2} ⊗ R^{(k-1)}`: causality under
  deterministic discard of the newest slot and compatibility on common
  prefixes. -/
  tensor_causal : ∀ (p : G.Port) (ps : List G.Port),
    newestOutputTrace (tensor (p :: ps)) = (1 : Matrix (In p) (In p) ℂ) ⊗ₖ tensor ps
  /-- Terminal Reads as terminal event outcomes: the outcome row of the Read
  `r` after the history `h`. -/
  readProb : ∀ {s x : G.CutType}, TypedWord G.Letter s x → ∀ r : G.TerminalRead,
    G.ReadOutcome r → ℝ
  readProb_nonneg : ∀ {s x : G.CutType} (h : TypedWord G.Letter s x) (r : G.TerminalRead)
    (o : G.ReadOutcome r), 0 ≤ readProb h r o
  sum_readProb : ∀ {s x : G.CutType} (h : TypedWord G.Letter s x), G.Reachable h →
    ∀ r : G.TerminalRead, ∑ o : G.ReadOutcome r, readProb h r o = 1

namespace FiniteConditionalOperationalRenewalLaw

variable {G}
variable (D : G.FiniteConditionalOperationalRenewalLaw)

attribute [instance] inFintype outFintype inDecidableEq outDecidableEq

/-- The exposed Choi index of the port `p`. -/
abbrev ChoiIndex (p : G.Port) : Type := D.In p × D.Out p

/-- The one-step probabilities lie in `[0, 1]` (`eq:supp-one-step-law`). -/
theorem prob_le_one {s x y : G.CutType} (h : TypedWord G.Letter s x) (hr : G.Reachable h)
    (a : G.Letter x y) : D.prob h a ≤ 1 := by
  have hsum := D.sum_prob h hr
  have hterm : D.prob h a ≤ ∑ y' : G.CutType, ∑ a' : G.Letter x y', D.prob h a' := by
    calc D.prob h a ≤ ∑ a' : G.Letter x y, D.prob h a' :=
          Finset.single_le_sum (fun a' _ => D.prob_nonneg h a') (Finset.mem_univ a)
      _ ≤ ∑ y' : G.CutType, ∑ a' : G.Letter x y', D.prob h a' :=
          Finset.single_le_sum (f := fun y' => ∑ a' : G.Letter x y', D.prob h a')
            (fun y' _ => Finset.sum_nonneg fun a' _ => D.prob_nonneg h a') (Finset.mem_univ y)
  linarith

/-- The multitime intervention probability of a tuple of slot Choi matrices
(newest slot first): the trace pairing `Re Tr(R^{(N)} (C₁ ⊗ ⋯ ⊗ Cₙ))`. -/
def multitimeProb (ps : List G.Port) (C : SlotTuple D.ChoiIndex ps) : ℝ :=
  ((D.tensor ps * slotKron D.ChoiIndex ps C).trace).re

/-- The slot tuple of Choi probes of a tuple of frame probes. -/
def probeTuple : ∀ ps : List G.Port, (∀ k : Fin ps.length, (D.frame (ps.get k)).Probe) →
    SlotTuple D.ChoiIndex ps
  | [], _ => ()
  | _ :: ps, a => ((D.frame _).probe (a ⟨0, Nat.succ_pos _⟩),
      probeTuple ps fun k => a k.succ)

/-- The multitime frame probability of a tuple of frame probes: the entries
of the finite probability table reconstructed by `thm:supp-comb-tomography`. -/
def frameProb (ps : List G.Port) (a : ∀ k : Fin ps.length, (D.frame (ps.get k)).Probe) : ℝ :=
  D.multitimeProb ps (D.probeTuple ps a)

/-- Normalization on the empty sequence: `R^{(0)} = 1` gives probability one. -/
theorem multitimeProb_nil (u : SlotTuple D.ChoiIndex []) : D.multitimeProb [] u = 1 := by
  have hcard : Fintype.card (SlotIndex D.ChoiIndex []) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨(), fun x => Subsingleton.elim (α := Unit) x ()⟩
  unfold multitimeProb
  rw [D.tensor_nil, slotKron_nil, one_mul, Matrix.trace_one, hcard]
  simp

/-- Additivity under coarse graining in the newest slot. -/
theorem multitimeProb_add (p : G.Port) (ps : List G.Port)
    (M M' : Matrix (D.ChoiIndex p) (D.ChoiIndex p) ℂ) (Ms : SlotTuple D.ChoiIndex ps) :
    D.multitimeProb (p :: ps) (M + M', Ms) =
      D.multitimeProb (p :: ps) (M, Ms) + D.multitimeProb (p :: ps) (M', Ms) := by
  unfold multitimeProb
  rw [slotKron_cons, slotKron_cons, slotKron_cons, Matrix.add_kronecker]
  exact trace_mul_add_re _ _ _

/-- Affinity under randomization in the newest slot: real scalings pass
through the probability. -/
theorem multitimeProb_smul (p : G.Port) (ps : List G.Port) (r : ℝ)
    (M : Matrix (D.ChoiIndex p) (D.ChoiIndex p) ℂ) (Ms : SlotTuple D.ChoiIndex ps) :
    D.multitimeProb (p :: ps) ((r : ℂ) • M, Ms) = r * D.multitimeProb (p :: ps) (M, Ms) := by
  unfold multitimeProb
  rw [slotKron_cons, slotKron_cons, Matrix.smul_kronecker]
  exact trace_mul_smul_re _ _ _

/-- Affinity under randomization: a convex mixture of two newest-slot
branches has the mixed probability. -/
theorem multitimeProb_convex (p : G.Port) (ps : List G.Port) (t : ℝ)
    (M M' : Matrix (D.ChoiIndex p) (D.ChoiIndex p) ℂ) (Ms : SlotTuple D.ChoiIndex ps) :
    D.multitimeProb (p :: ps) ((t : ℂ) • M + ((1 - t : ℝ) : ℂ) • M', Ms) =
      t * D.multitimeProb (p :: ps) (M, Ms) + (1 - t) * D.multitimeProb (p :: ps) (M', Ms) := by
  rw [multitimeProb_add, multitimeProb_smul, multitimeProb_smul]

end FiniteConditionalOperationalRenewalLaw

end FiniteTypedEventGrammar

end RenewalGeometry
