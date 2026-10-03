/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.OperationalRenewalLawDatum

/-!
# The finite conditional operational renewal law with induced frame probabilities
  (`def:supp-operational-datum`, emergent-spacetime manuscript)

`OperationalRenewalLawDatum.lean` encodes the conditional law and a family of
comb tensors side by side.  Here the multitime frame probabilities are
**induced by the conditional law**: intervention events are grammar letters,
and the frame probability of a chronological tuple of frame probes after a
history `h` is the chain-law probability `p_X(w | h)` (`eq:supp-chain-law`) of
the corresponding intervention word `w`.

* `OperationalFrameData G`: the conditional law `p_X(a | h)` on the grammar
  (`eq:supp-one-step-law`), input/output legs of every exposed port, a finite
  physical CP frame on every exposed Hermitian Choi space whose real span is the
  full Hermitian space (`frame_spans`), intervention letters `interventionLetter
  x p α : x → y` of the grammar realizing every frame probe at every cut type
  (injective), and terminal Read outcomes realized as terminal event letters
  (`readEvent`, injective, disjoint from interventions).
* `interventionWord`, `framePr`: the intervention word of a chronological probe
  tuple (newest slot first) and its chain-law probability — the induced
  multitime frame probabilities.  `readProb`: the Read rows, the law of the
  terminal event letters.
* `inducedTensor h ps = ∑_α p_X(w_α | h) D^{α₁} ⊗ ⋯ ⊗ D^{αₙ}`
  (`eq:supp-comb-tomography`) with `inducedTensor_pairing`
  (`Tr(R (F^{β₁} ⊗ ⋯ ⊗ F^{βₙ})) = p_X(w_β | h)`, the tensor represents the
  induced frame table), `inducedTensor_isHermitian`, `inducedTensor_nil`
  (`R^{(0)} = 1`), and the multilinear pairing `multitimeProb` (additive under
  coarse graining, affine under randomization: `multitimeProb_add`,
  `multitimeProb_smul`, `multitimeProb_convex`).
* `FiniteConditionalOperationalRenewalLawInduced G`: the datum together with the
  finite positivity / causal-recursion conditions of `thm:supp-comb-tomography`
  imposed on the INDUCED tensors after every reachable history
  (`comb_posSemidef`, `comb_causal`: normalization on complete instruments,
  causality under deterministic discard and prefix compatibility).
* `frameProb_eq_chain`, `readProb_eq_chain`: the frame/Read probabilities are the
  chain law of the corresponding event words.
* `qubitPreparationLaw`: non-vacuity — a one-port grammar with a qubit output
  leg, a minimal informationally complete four-outcome POVM as frame, terminal
  orientation Read letters, and the i.i.d. law of measuring `|0⟩⟨0|`; the induced
  tensors are `ρ^{⊗N}` and satisfy all comb conditions.
-/

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

namespace RenewalGeometry

namespace OperationalDatum

/-! ## Probe tuples -/

section ProbeTuple

variable {P : Type} (Pr : P → Type)

/-- A chronological tuple of probes on a list of ports (newest first). -/
def ProbeTuple : List P → Type
  | [] => Unit
  | p :: ps => Pr p × ProbeTuple ps

instance probeTupleFintype [∀ p, Fintype (Pr p)] : ∀ ps : List P, Fintype (ProbeTuple Pr ps)
  | [] => inferInstanceAs (Fintype Unit)
  | p :: ps => by
      letI := probeTupleFintype ps
      exact inferInstanceAs (Fintype (Pr p × ProbeTuple Pr ps))

instance probeTupleDecidableEq [∀ p, DecidableEq (Pr p)] :
    ∀ ps : List P, DecidableEq (ProbeTuple Pr ps)
  | [] => inferInstanceAs (DecidableEq Unit)
  | p :: ps => by
      letI := probeTupleDecidableEq ps
      exact inferInstanceAs (DecidableEq (Pr p × ProbeTuple Pr ps))

end ProbeTuple

/-! ## Kronecker products of frame elements -/

section Kron

variable {P : Type} (C : P → Type) [∀ p, Fintype (C p)] [∀ p, DecidableEq (C p)]
  (Pr : P → Type) [∀ p, Fintype (Pr p)] [∀ p, DecidableEq (Pr p)]

/-- `M_{α₁} ⊗ ⋯ ⊗ M_{αₙ}` for a family `M p : Pr p → Matrix (C p) (C p) ℂ`. -/
def tupleKron (M : ∀ p, Pr p → Matrix (C p) (C p) ℂ) :
    ∀ ps : List P, ProbeTuple Pr ps → Matrix (SlotIndex C ps) (SlotIndex C ps) ℂ
  | [], _ => 1
  | p :: ps, (α, a) => M p α ⊗ₖ tupleKron M ps a

/-- Kronecker products of mutually dual frames are mutually dual. -/
theorem trace_tupleKron_mul (D M : ∀ p, Pr p → Matrix (C p) (C p) ℂ)
    (hdual : ∀ p α β, (D p α * M p β).trace = if α = β then 1 else 0) :
    ∀ (ps : List P) (a b : ProbeTuple Pr ps),
      (tupleKron C Pr D ps a * tupleKron C Pr M ps b).trace = if a = b then 1 else 0
  | [], a, b => by
      have hcard : Fintype.card (SlotIndex C []) = 1 :=
        Fintype.card_eq_one_iff.mpr ⟨(), fun x => Subsingleton.elim (α := Unit) x ()⟩
      change ((1 : Matrix (SlotIndex C []) (SlotIndex C []) ℂ) * 1).trace = _
      rw [one_mul, Matrix.trace_one, hcard,
        if_pos (show a = b from Subsingleton.elim (α := Unit) a b)]
      simp
  | p :: ps, (α, a), (β, b) => by
      change ((D p α ⊗ₖ tupleKron C Pr D ps a) * (M p β ⊗ₖ tupleKron C Pr M ps b)).trace = _
      rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, hdual,
        trace_tupleKron_mul D M hdual ps a b]
      by_cases hαβ : α = β
      · subst hαβ
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl, if_pos rfl, mul_one]
          exact (if_pos rfl).symm
        · rw [if_pos rfl, if_neg hab, mul_zero]
          exact (if_neg (fun h => hab
            (Prod.mk.inj (h : ((α, a) : Pr p × ProbeTuple Pr ps) = (α, b))).2)).symm
      · rw [if_neg hαβ, zero_mul]
        exact (if_neg (fun h => hαβ
            (Prod.mk.inj (h : ((α, a) : Pr p × ProbeTuple Pr ps) = (β, b))).1)).symm

theorem tupleKron_isHermitian (M : ∀ p, Pr p → Matrix (C p) (C p) ℂ)
    (hM : ∀ p α, (M p α).IsHermitian) :
    ∀ (ps : List P) (a : ProbeTuple Pr ps), (tupleKron C Pr M ps a).IsHermitian
  | [], _ => Matrix.isHermitian_one
  | p :: ps, (α, a) => by
      change (M p α ⊗ₖ tupleKron C Pr M ps a).IsHermitian
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_kronecker, hM p α, tupleKron_isHermitian M hM ps a]

end Kron

/-! ## The datum -/

variable (G : FiniteTypedEventGrammar)

/-- **`def:supp-operational-datum`, data part.**  The conditional law on the
grammar `G`, a spanning finite physical CP frame on the exposed Hermitian Choi
space of every port, the realization of every frame probe by an intervention
letter of the grammar at every cut type, and the realization of terminal Read
outcomes by terminal event letters. -/
structure OperationalFrameData extends G.ConditionalLaw where
  /-- Input leg of the exposed port `p`. -/
  In : G.Port → Type
  /-- Output leg of the exposed port `p`. -/
  Out : G.Port → Type
  [inFintype : ∀ p, Fintype (In p)]
  [outFintype : ∀ p, Fintype (Out p)]
  [inDecidableEq : ∀ p, DecidableEq (In p)]
  [outDecidableEq : ∀ p, DecidableEq (Out p)]
  /-- The finite physical CP frame on the Hermitian Choi-coordinate space of `p`. -/
  frame : ∀ p : G.Port, PhysicalChoiTomographyFrame (In p × Out p)
  /-- Its real span is the full Hermitian space. -/
  frame_spans : ∀ (p : G.Port) (H : Matrix (In p × Out p) (In p × Out p) ℂ), H.IsHermitian →
    H ∈ Submodule.span ℝ (Set.range (frame p).probe)
  /-- Intervention-outcome labels of the probes. -/
  interventionLabel : ∀ p : G.Port, (frame p).Probe → G.InterventionOutcome
  interventionLabel_injective :
    Function.Injective (fun x : Σ p : G.Port, (frame p).Probe => interventionLabel x.1 x.2)
  /-- The intervention letter realizing the probe `α` at the port `p` after a
  history ending at the cut type `x`. -/
  interventionLetter : ∀ (x : G.CutType) (p : G.Port), (frame p).Probe → Σ y, G.Letter x y
  interventionLetter_injective : ∀ x : G.CutType,
    Function.Injective (fun q : Σ p : G.Port, (frame p).Probe => interventionLetter x q.1 q.2)
  /-- Terminal Read outcomes as terminal event letters. -/
  readEvent : ∀ (x : G.CutType) (r : G.TerminalRead), G.ReadOutcome r → Σ y, G.Letter x y
  readEvent_injective : ∀ x : G.CutType,
    Function.Injective (fun q : Σ r : G.TerminalRead, G.ReadOutcome r => readEvent x q.1 q.2)
  readEvent_ne_interventionLetter : ∀ (x : G.CutType) (r : G.TerminalRead)
    (o : G.ReadOutcome r) (p : G.Port) (α : (frame p).Probe),
    readEvent x r o ≠ interventionLetter x p α

namespace OperationalFrameData

variable {G}
variable (D : OperationalFrameData G)

attribute [instance] inFintype outFintype inDecidableEq outDecidableEq

/-- The exposed Choi index of the port `p`. -/
abbrev ChoiIndex (p : G.Port) : Type := D.In p × D.Out p

/-- The probe type of the port `p`. -/
abbrev Probe (p : G.Port) : Type := (D.frame p).Probe

/-- The intervention word of a chronological probe tuple (newest first)
starting at the cut type `x`: the oldest probe is applied first. -/
def interventionWord (x : G.CutType) :
    ∀ ps : List G.Port, ProbeTuple D.Probe ps → Σ z, TypedWord G.Letter x z
  | [], _ => ⟨x, TypedWord.nil x⟩
  | p :: ps, (α, a) =>
      let w := interventionWord x ps a
      ⟨(D.interventionLetter w.1 p α).1, w.2.snoc (D.interventionLetter w.1 p α).2⟩

/-- **Induced multitime frame probability**: the chain-law probability
`p_X(w | h)` of the intervention word of the probe tuple. -/
def framePr {s x : G.CutType} (h : TypedWord G.Letter s x) (ps : List G.Port)
    (a : ProbeTuple D.Probe ps) : ℝ :=
  D.wordProb h (D.interventionWord x ps a).2

/-- The Read rows: the law of the terminal event letters. -/
def readProb {s x : G.CutType} (h : TypedWord G.Letter s x) (r : G.TerminalRead)
    (o : G.ReadOutcome r) : ℝ :=
  D.prob h (D.readEvent x r o).2

theorem readProb_eq_chain {s x : G.CutType} (h : TypedWord G.Letter s x) (r : G.TerminalRead)
    (o : G.ReadOutcome r) :
    D.readProb h r o = D.wordProb h ((TypedWord.nil x).snoc (D.readEvent x r o).2) := by
  rw [D.toConditionalLaw.wordProb_single]
  rfl

theorem framePr_nil {s x : G.CutType} (h : TypedWord G.Letter s x) (a : ProbeTuple D.Probe []) :
    D.framePr h [] a = 1 := rfl

/-- Chain rule for the induced frame probabilities: appending the newest
probe multiplies by its one-step probability after the prefix word. -/
theorem framePr_cons {s x : G.CutType} (h : TypedWord G.Letter s x) (p : G.Port)
    (ps : List G.Port) (α : D.Probe p) (a : ProbeTuple D.Probe ps) :
    D.framePr h (p :: ps) (α, a) =
      D.framePr h ps a * D.prob (h.append (D.interventionWord x ps a).2)
        (D.interventionLetter (D.interventionWord x ps a).1 p α).2 := rfl

theorem framePr_nonneg {s x : G.CutType} (h : TypedWord G.Letter s x) :
    ∀ (ps : List G.Port) (a : ProbeTuple D.Probe ps), 0 ≤ D.framePr h ps a
  | [], _ => zero_le_one
  | p :: ps, (α, a) => by
      rw [framePr_cons]
      exact mul_nonneg (framePr_nonneg h ps a) (D.prob_nonneg _ _)

/-- The Kronecker product of frame probes. -/
abbrev probeKron (ps : List G.Port) (a : ProbeTuple D.Probe ps) :
    Matrix (SlotIndex D.ChoiIndex ps) (SlotIndex D.ChoiIndex ps) ℂ :=
  tupleKron D.ChoiIndex D.Probe (fun p => (D.frame p).probe) ps a

/-- The Kronecker product of dual frame elements. -/
abbrev dualKron (ps : List G.Port) (a : ProbeTuple D.Probe ps) :
    Matrix (SlotIndex D.ChoiIndex ps) (SlotIndex D.ChoiIndex ps) ℂ :=
  tupleKron D.ChoiIndex D.Probe (fun p => (D.frame p).dual) ps a

/-- **`eq:supp-comb-tomography` for the induced table**: the tensor
`R^{(N)}_h = ∑_α p_X(w_α | h) D^{α₁} ⊗ ⋯ ⊗ D^{αₙ}`. -/
def inducedTensor {s x : G.CutType} (h : TypedWord G.Letter s x) (ps : List G.Port) :
    Matrix (SlotIndex D.ChoiIndex ps) (SlotIndex D.ChoiIndex ps) ℂ :=
  ∑ a : ProbeTuple D.Probe ps, (D.framePr h ps a : ℂ) • D.dualKron ps a

theorem inducedTensor_isHermitian {s x : G.CutType} (h : TypedWord G.Letter s x)
    (ps : List G.Port) : (D.inducedTensor h ps).IsHermitian := by
  classical
  unfold inducedTensor
  refine Finset.sum_induction _ _ (fun A B hA hB => hA.add hB) Matrix.isHermitian_zero
    (fun a _ => ?_)
  exact (tupleKron_isHermitian _ _ _ (fun p α => (D.frame p).dualHermitian α) ps a).smul
    (by simp [IsSelfAdjoint])

/-- The induced tensor represents the induced frame table:
`Tr(R^{(N)}_h (F^{β₁} ⊗ ⋯ ⊗ F^{βₙ})) = p_X(w_β | h)`. -/
theorem inducedTensor_pairing {s x : G.CutType} (h : TypedWord G.Letter s x)
    (ps : List G.Port) (b : ProbeTuple D.Probe ps) :
    (D.inducedTensor h ps * D.probeKron ps b).trace = (D.framePr h ps b : ℂ) := by
  classical
  unfold inducedTensor
  rw [Finset.sum_mul, Matrix.trace_sum]
  simp_rw [Matrix.smul_mul, Matrix.trace_smul]
  rw [Finset.sum_eq_single b]
  · rw [trace_tupleKron_mul _ _ _ _ (fun p α β => (D.frame p).duality α β)]
    simp
  · intro a _ hab
    rw [trace_tupleKron_mul _ _ _ _ (fun p α β => (D.frame p).duality α β)]
    simp [hab]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

/-- `R^{(0)} = 1`. -/
theorem inducedTensor_nil {s x : G.CutType} (h : TypedWord G.Letter s x) :
    D.inducedTensor h [] = 1 := by
  unfold inducedTensor
  refine (Fintype.sum_eq_single (() : ProbeTuple D.Probe []) ?_).trans ?_
  · intro b hb
    exact absurd (Subsingleton.elim (α := Unit) b ()) hb
  · change ((1 : ℝ) : ℂ) • (1 : Matrix (SlotIndex D.ChoiIndex []) (SlotIndex D.ChoiIndex []) ℂ)
      = 1
    rw [Complex.ofReal_one, one_smul]

/-- The multitime probability of a tuple of slot Choi matrices (newest first):
the trace pairing with the induced tensor. -/
def multitimeProb {s x : G.CutType} (h : TypedWord G.Letter s x) (ps : List G.Port)
    (C : SlotTuple D.ChoiIndex ps) : ℝ :=
  ((D.inducedTensor h ps * slotKron D.ChoiIndex ps C).trace).re

/-- Additivity under coarse graining in the newest slot. -/
theorem multitimeProb_add {s x : G.CutType} (h : TypedWord G.Letter s x) (p : G.Port)
    (ps : List G.Port) (M M' : Matrix (D.ChoiIndex p) (D.ChoiIndex p) ℂ)
    (Ms : SlotTuple D.ChoiIndex ps) :
    D.multitimeProb h (p :: ps) (M + M', Ms) =
      D.multitimeProb h (p :: ps) (M, Ms) + D.multitimeProb h (p :: ps) (M', Ms) := by
  unfold multitimeProb
  rw [slotKron_cons, slotKron_cons, slotKron_cons, Matrix.add_kronecker]
  exact trace_mul_add_re _ _ _

/-- Real homogeneity in the newest slot. -/
theorem multitimeProb_smul {s x : G.CutType} (h : TypedWord G.Letter s x) (p : G.Port)
    (ps : List G.Port) (r : ℝ) (M : Matrix (D.ChoiIndex p) (D.ChoiIndex p) ℂ)
    (Ms : SlotTuple D.ChoiIndex ps) :
    D.multitimeProb h (p :: ps) ((r : ℂ) • M, Ms) = r * D.multitimeProb h (p :: ps) (M, Ms) := by
  unfold multitimeProb
  rw [slotKron_cons, slotKron_cons, Matrix.smul_kronecker]
  exact trace_mul_smul_re _ _ _

/-- Affinity under randomization in the newest slot. -/
theorem multitimeProb_convex {s x : G.CutType} (h : TypedWord G.Letter s x) (p : G.Port)
    (ps : List G.Port) (t : ℝ) (M M' : Matrix (D.ChoiIndex p) (D.ChoiIndex p) ℂ)
    (Ms : SlotTuple D.ChoiIndex ps) :
    D.multitimeProb h (p :: ps) ((t : ℂ) • M + ((1 - t : ℝ) : ℂ) • M', Ms) =
      t * D.multitimeProb h (p :: ps) (M, Ms) + (1 - t) * D.multitimeProb h (p :: ps) (M', Ms) := by
  rw [multitimeProb_add, multitimeProb_smul, multitimeProb_smul]

/-- Normalization on the empty sequence. -/
theorem multitimeProb_nil {s x : G.CutType} (h : TypedWord G.Letter s x)
    (u : SlotTuple D.ChoiIndex []) : D.multitimeProb h [] u = 1 := by
  have hcard : Fintype.card (SlotIndex D.ChoiIndex []) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨(), fun x => Subsingleton.elim (α := Unit) x ()⟩
  unfold multitimeProb
  rw [inducedTensor_nil, slotKron_nil, one_mul, Matrix.trace_one, hcard]
  simp

/-- The slot tuple of frame probes of a probe tuple. -/
def probeSlots : ∀ ps : List G.Port, ProbeTuple D.Probe ps → SlotTuple D.ChoiIndex ps
  | [], _ => ()
  | p :: ps, (α, a) => ((D.frame p).probe α, probeSlots ps a)

theorem slotKron_probeSlots : ∀ (ps : List G.Port) (a : ProbeTuple D.Probe ps),
    slotKron D.ChoiIndex ps (D.probeSlots ps a) = D.probeKron ps a
  | [], _ => rfl
  | p :: ps, (α, a) => by
      change (D.frame p).probe α ⊗ₖ slotKron D.ChoiIndex ps (D.probeSlots ps a) = _
      rw [slotKron_probeSlots ps a]
      rfl

/-- **The frame probabilities are induced by the conditional law**: the
multitime probability of a tuple of frame probes is the chain-law probability
of the corresponding intervention word. -/
theorem frameProb_eq_chain {s x : G.CutType} (h : TypedWord G.Letter s x) (ps : List G.Port)
    (a : ProbeTuple D.Probe ps) :
    D.multitimeProb h ps (D.probeSlots ps a) = D.wordProb h (D.interventionWord x ps a).2 := by
  unfold multitimeProb
  rw [slotKron_probeSlots, inducedTensor_pairing]
  rfl

end OperationalFrameData

/-- **`def:supp-operational-datum`.**  A finite conditional operational renewal
law: the data `OperationalFrameData` (conditional law, spanning physical CP
frames realized by intervention letters, terminal Read letters) whose INDUCED
multitime frame tables satisfy, after every reachable history, the finite
positivity and causal-recursion conditions of `thm:supp-comb-tomography`
(`R^{(N)} ⪰ 0`, `Tr_{newest out} R^{(k)} = I ⊗ R^{(k-1)}`; `R^{(0)} = 1` holds
automatically, `inducedTensor_nil`). -/
structure FiniteConditionalOperationalRenewalLawInduced where
  /-- The law and its frame/Read realization. -/
  data : OperationalFrameData G
  /-- Finite positivity conditions. -/
  comb_posSemidef : ∀ {s x : G.CutType} (h : TypedWord G.Letter s x), G.Reachable h →
    ∀ ps : List G.Port, (data.inducedTensor h ps).PosSemidef
  /-- Causality under deterministic discard of the newest slot / prefix
  compatibility / normalization on complete instruments. -/
  comb_causal : ∀ {s x : G.CutType} (h : TypedWord G.Letter s x), G.Reachable h →
    ∀ (p : G.Port) (ps : List G.Port),
      newestOutputTrace (data.inducedTensor h (p :: ps)) =
        (1 : Matrix (data.In p) (data.In p) ℂ) ⊗ₖ data.inducedTensor h ps

/-! ## Non-vacuity: an i.i.d. qubit measurement law -/

namespace QubitExample

open Complex

/-- The minimal informationally complete four-outcome POVM on a qubit. -/
def povm : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1/3, 0; 0, 0], !![1/6, 1/6; 1/6, 1/6], !![1/6, -I/6; I/6, 1/6],
    !![1/3, (-1 + I)/6; (-1 - I)/6, 2/3]]

/-- Its trace-dual Hermitian basis. -/
def povmDual : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![3, (-1 + I)/2; (-1 - I)/2, -2], !![0, (5 + I)/2; (5 - I)/2, 1],
    !![0, (-1 - 5 * I)/2; (-1 + 5 * I)/2, 1], !![0, (-1 + I)/2; (-1 - I)/2, 1]]

theorem povm_duality (a b : Fin 4) :
    (povmDual a * povm b).trace = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [povm, povmDual, Matrix.trace, Fin.sum_univ_two] <;>
    apply Complex.ext <;> simp <;> norm_num

theorem povmDual_isHermitian (a : Fin 4) : (povmDual a).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [povmDual, Matrix.conjTranspose_apply] <;> apply Complex.ext <;> simp

theorem povm_eq (a : Fin 4) : povm a =
    ![(((1:ℝ)/3 : ℝ) : ℂ) • vecMulVec ![1, 0] (star ![1, 0]),
      (((1:ℝ)/6 : ℝ) : ℂ) • vecMulVec ![1, 1] (star ![1, 1]),
      (((1:ℝ)/6 : ℝ) : ℂ) • vecMulVec ![1, I] (star ![1, I]),
      (((1:ℝ)/6 : ℝ) : ℂ) • (vecMulVec ![1, -1 - I] (star ![1, -1 - I]) +
        diagonal ![1, 2])] a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [povm, vecMulVec, diagonal] <;> apply Complex.ext <;> simp <;> norm_num


theorem povm_posSemidef (a : Fin 4) : (povm a).PosSemidef := by
  have h3 : (0 : ℂ) ≤ (((1:ℝ)/3 : ℝ) : ℂ) := Complex.zero_le_real.mpr (by norm_num)
  have h6 : (0 : ℂ) ≤ (((1:ℝ)/6 : ℝ) : ℂ) := Complex.zero_le_real.mpr (by norm_num)
  rw [povm_eq]
  fin_cases a
  · exact (posSemidef_vecMulVec_self_star _).smul h3
  · exact (posSemidef_vecMulVec_self_star _).smul h6
  · exact (posSemidef_vecMulVec_self_star _).smul h6
  · refine ((posSemidef_vecMulVec_self_star _).add ?_).smul h6
    rw [posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> simp

theorem povm_trace_le (a : Fin 4) : ((povm a).trace).re ≤ 1 := by
  fin_cases a <;> simp [povm, Matrix.trace, Fin.sum_univ_two] <;> norm_num

/-- Every Hermitian `2 × 2` matrix is a real combination of the POVM elements. -/
theorem povm_spans (K : Matrix (Fin 2) (Fin 2) ℂ) (hK : K.IsHermitian) :
    K ∈ Submodule.span ℝ (Set.range povm) := by
  have h00 : (K 0 0).im = 0 := by
    have := congrFun (congrFun hK 0) 0
    simp [Matrix.conjTranspose_apply] at this
    have := congrArg Complex.im this
    simp at this
    linarith
  have h11 : (K 1 1).im = 0 := by
    have := congrFun (congrFun hK 1) 1
    simp [Matrix.conjTranspose_apply] at this
    have := congrArg Complex.im this
    simp at this
    linarith
  have h10 : K 1 0 = star (K 0 1) := by
    have := congrFun (congrFun hK 1) 0
    simp [Matrix.conjTranspose_apply] at this
    rw [← this]; rfl
  set a := (K 0 0).re
  set dd := (K 1 1).re
  set b := (K 0 1).re
  set c := (K 0 1).im
  have hrepr : K = (3 * a - 2 * dd - b + c) • povm 0 + (dd + 5 * b + c) • povm 1
      + (dd - b - 5 * c) • povm 2 + (dd - b + c) • povm 3 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [povm, Matrix.add_apply] <;> apply Complex.ext <;>
      simp [h00, h11, h10, a, dd, b, c] <;> ring
  rw [hrepr]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The qubit output leg as the Choi index `Unit × Fin 2` of a port with
trivial input. -/
abbrev legEquiv : Unit × Fin 2 ≃ Fin 2 := Equiv.uniqueProd (Fin 2) Unit

theorem trace_submatrix_legEquiv (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (M.submatrix legEquiv legEquiv).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact legEquiv.sum_comp (fun i => M i i)

/-- The physical CP frame on the Choi space of the qubit port. -/
def qubitFrame : PhysicalChoiTomographyFrame (Unit × Fin 2) where
  Probe := Fin 4
  probeFintype := inferInstance
  probeDecidableEq := inferInstance
  probe a := (povm a).submatrix legEquiv legEquiv
  dual a := (povmDual a).submatrix legEquiv legEquiv
  probePositive a := (povm_posSemidef a).submatrix _
  probeNormalized a := by rw [trace_submatrix_legEquiv]; exact povm_trace_le a
  dualHermitian a := (povmDual_isHermitian a).submatrix _
  duality a b := by
    rw [Matrix.submatrix_mul_equiv, trace_submatrix_legEquiv]
    exact povm_duality a b

theorem qubitFrame_spans (H : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ) (hH : H.IsHermitian) :
    H ∈ Submodule.span ℝ (Set.range qubitFrame.probe) := by
  set K := H.submatrix legEquiv.symm legEquiv.symm with hKdef
  have hK : K.IsHermitian := hH.submatrix _
  have hHK : H = K.submatrix legEquiv legEquiv := by
    rw [hKdef, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
  let L : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ :=
    { toFun := fun M => M.submatrix legEquiv legEquiv
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmem := Submodule.mem_map_of_mem (f := L) (povm_spans K hK)
  rw [Submodule.map_span, ← Set.range_comp] at hmem
  rw [hHK]
  exact hmem

/-- The one-port grammar: a single cut type, the four POVM outcomes as
intervention letters and the binary orientation Read outcomes as terminal
event letters. -/
def grammar : FiniteTypedEventGrammar where
  CutType := Unit
  Letter _ _ := Fin 4 ⊕ ℤˣ
  Reachable _ := True
  reachable_nil _ := trivial
  reachable_of_snoc _ _ _ := trivial
  Preparation := Unit
  InterventionOutcome := Fin 4
  TerminalRead := Unit
  Port := Unit
  ReadOutcome _ := ℤˣ
  Verdict := ℤˣ
  readPolicy _ o := o
  orientationRead := ()
  orientationBinary := Equiv.refl _
  orientation_separated := by decide

/-- The outcome probabilities `Tr(ρ F_α)` for `ρ = |0⟩⟨0|`. -/
def outcomeProb : Fin 4 → ℝ := ![1/3, 1/6, 1/6, 1/3]

/-- The i.i.d. conditional law: every intervention outcome `α` has probability
`Tr(ρ F_α)` after every history; the orientation Read letters do not fire. -/
def law : grammar.ConditionalLaw where
  prob _ a := Sum.elim outcomeProb (fun _ => 0) a
  prob_nonneg _ a := by
    rcases a with a | a
    · fin_cases a <;> simp [outcomeProb]
    · simp
  prob_eq_zero_of_not_admissible _ _ h := absurd trivial h
  sum_prob _ _ := by
    change ∑ _y : Unit, ∑ a : Fin 4 ⊕ ℤˣ, Sum.elim outcomeProb (fun _ => (0 : ℝ)) a = 1
    simp [Fintype.sum_sum_type, outcomeProb, Fin.sum_univ_four]
    norm_num

/-- The frame data of the example. -/
def frameData : OperationalFrameData grammar where
  toConditionalLaw := law
  In _ := Unit
  Out _ := Fin 2
  frame _ := qubitFrame
  frame_spans _ H hH := qubitFrame_spans H hH
  interventionLabel _ α := α
  interventionLabel_injective := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    simp only at h
    subst h
    rfl
  interventionLetter _ _ α := ⟨(), Sum.inl α⟩
  interventionLetter_injective _ := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    have h2 := Sum.inl.inj (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    subst h2
    rfl
  readEvent _ _ o := ⟨(), Sum.inr o⟩
  readEvent_injective _ := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    have h2 := Sum.inr.inj (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    subst h2
    rfl
  readEvent_ne_interventionLetter _ _ _ _ _ := by
    intro h
    exact Sum.inr_ne_inl (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

/-- The prepared state `|0⟩⟨0|` on the Choi index of the port. -/
def rho : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ :=
  (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ).submatrix legEquiv legEquiv

theorem dual_reconstruction :
    ∑ α : Fin 4, ((outcomeProb α : ℝ) : ℂ) • (povmDual α).submatrix legEquiv legEquiv = rho := by
  have : ∑ α : Fin 4, ((outcomeProb α : ℝ) : ℂ) • povmDual α = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_four, outcomeProb, povmDual] <;> apply Complex.ext <;> simp <;> norm_num
  rw [rho, ← this]
  ext i j
  simp [Matrix.sum_apply]

/-- The tensor power `ρ^{⊗N}` on a port list. -/
def rhoPower : ∀ ps : List grammar.Port,
    Matrix (SlotIndex frameData.ChoiIndex ps) (SlotIndex frameData.ChoiIndex ps) ℂ
  | [] => 1
  | _ :: ps => rho ⊗ₖ rhoPower ps

theorem framePr_cons_eq {s x : grammar.CutType} (h : TypedWord grammar.Letter s x)
    (p : grammar.Port) (ps : List grammar.Port) (α : frameData.Probe p)
    (a : ProbeTuple frameData.Probe ps) :
    frameData.framePr h (p :: ps) (α, a) = outcomeProb α * frameData.framePr h ps a :=
  (OperationalFrameData.framePr_cons frameData h p ps α a).trans (mul_comm _ _)

theorem inducedTensor_eq {s x : grammar.CutType} (h : TypedWord grammar.Letter s x) :
    ∀ ps : List grammar.Port, frameData.inducedTensor h ps = rhoPower ps
  | [] => frameData.inducedTensor_nil h
  | p :: ps => by
      have ih := inducedTensor_eq h ps
      unfold OperationalFrameData.inducedTensor at ih ⊢
      change ∑ q : Fin 4 × ProbeTuple frameData.Probe ps,
          ((frameData.framePr h (p :: ps) q : ℝ) : ℂ) •
            ((povmDual q.1).submatrix legEquiv legEquiv ⊗ₖ frameData.dualKron ps q.2) =
        rho ⊗ₖ rhoPower ps
      rw [← ih, ← dual_reconstruction, Fintype.sum_prod_type]
      ext i j
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun α _ => ?_
      erw [framePr_cons_eq h p ps α a]
      push_cast
      ring

theorem rho_posSemidef : rho.PosSemidef := by
  have : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = vecMulVec ![1, 0] (star ![1, 0]) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec]
  rw [rho, this]
  exact (posSemidef_vecMulVec_self_star _).submatrix _

theorem rhoPower_posSemidef : ∀ ps, (rhoPower ps).PosSemidef
  | [] => Matrix.PosSemidef.one
  | _ :: ps => rho_posSemidef.kronecker (rhoPower_posSemidef ps)

theorem rhoPower_causal (p : grammar.Port) (ps : List grammar.Port) :
    newestOutputTrace (rhoPower (p :: ps)) =
      (1 : Matrix (frameData.In p) (frameData.In p) ℂ) ⊗ₖ rhoPower ps := by
  ext i j
  change ∑ o : Fin 2, rho (i.1, o) (j.1, o) * rhoPower ps i.2 j.2 = _
  have hij : i.1 = j.1 := Subsingleton.elim (α := Unit) _ _
  simp [rho, Fin.sum_univ_two, Matrix.kroneckerMap_apply, legEquiv]
  rw [hij, Matrix.one_apply_eq, one_mul]

/-- **Non-vacuity of `def:supp-operational-datum`**: the i.i.d. qubit
measurement law with a minimal informationally complete POVM frame is a finite
conditional operational renewal law; its induced tensors are `ρ^{⊗N}`. -/
def qubitPreparationLaw : FiniteConditionalOperationalRenewalLawInduced grammar where
  data := frameData
  comb_posSemidef h _ ps := by rw [inducedTensor_eq]; exact rhoPower_posSemidef ps
  comb_causal h _ p ps := by rw [inducedTensor_eq, inducedTensor_eq]; exact rhoPower_causal p ps

end QubitExample

end OperationalDatum

end RenewalGeometry
