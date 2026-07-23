# From Operational Prediction to Signed Renewal Memory

**A. Pélissier** — formal verification companion.

This folder contains the manuscript and its complete, machine-checked
statement inventory. Every named statement environment of the paper is
tracked in [`statements.json`](statements.json), which maps each label to the
Lean identifiers in [`NCG/`](../../NCG) that formalize it, together with an
honesty note describing exactly what was proved.

| File | Contents |
|---|---|
| [`renewal_emergence.tex`](renewal_emergence.tex) | The manuscript source |
| [`renewal_emergence.pdf`](renewal_emergence.pdf) | The compiled manuscript |
| [`statements.json`](statements.json) | The per-statement verification ledger (label → status → Lean anchors → note) |

## Verification summary

**123 tracked statements. 0 `sorry`. 0 conditional. 0 unformalized.**

Every claim-bearing statement of the paper (theorem / proposition / lemma /
corollary) is **proved in Lean**, with two declared exceptions (see below):

| Environment | Proved | Encoded interface | Total |
|---|---:|---:|---:|
| Theorems | 44 | 2 | 46 |
| Propositions | 28 | 0 | 28 |
| Corollaries | 14 | 0 | 14 |
| Lemmas | 6 | 0 | 6 |
| *Claim-bearing subtotal* | *92* | *2* | *94* |
| Definitions | 1 | 28 | 29 |
| **Total** | **93** | **30** | **123** |

What the two statuses mean:

- **Theorems / propositions / lemmas / corollaries** — `proved` means the
  statement's mathematical content is proved sorry-free in Lean; any scoped
  hypothesis is disclosed in the record's note *and* appears explicitly in the
  Lean signature. The two exceptions
  (`thm:operational-diagonalization`, `thm:operational-jordan`) are the
  paper's declared classical inputs: the Jordan–von Neumann–Wigner /
  operational-diagonalization classification, encoded as an interface
  (`NCG/Algebra/JordanFace.lean`) in exactly the form the text uses it.
- **Definitions** — a definition environment usually has nothing to *prove*;
  `statement_encoded` (28 records) means the object is faithfully transcribed
  as a Lean definition or structure. The one definition marked `proved`
  (`def:pressure-entropy-data`) is a definition that **carries claims** — the
  stationary edge flows are probability distributions and the entropy
  production is the relative entropy `D_KL(F‖F∘bar) ≥ 0` — and those claims
  are proved in Lean. So `proved` on a definition is *stronger* than
  `statement_encoded`, never weaker.

### Axioms

Every theorem depends only on Lean's three standard axioms — the identical
foundation used by Mathlib itself:

```
propext, Classical.choice, Quot.sound
```

No `sorryAx` (no `sorry` anywhere in the build), no `native_decide`, no
custom axioms. Reproduce for any theorem with, e.g.:

```lean
#print axioms NCG.Upstream.Ising.dlrState_unique
-- 'NCG.Upstream.Ising.dlrState_unique' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

### Reproducing the check

```bash
lake build                                            # kernel-checks the library
python scripts/check_statement_coverage.py --notes    # verifies this inventory
# Statement coverage passed (123 records): computer_certified=0,
#   conditional_interface=0, not_started=0, proved=93, statement_encoded=30
```

## Headline theorems

* **Phase coexistence — the paper's centerpiece**
(`thm:torsion-phase-coexistence`, `cor:torsion-selection`). One microscopic
detailed-balanced law admits both torsion-free and torsional stationary
phases, so plaquette closure (torsion freedom) is a genuine *selection
principle* — no theorem from locality, stationarity, detailed balance,
exchange covariance, bounded records, and nondegenerate second moments alone
can force it. All three clauses are formalized end to end on the 2d Ising
model, with **no scoped statistical-mechanics inputs remaining**:

- *Clause (ii), low temperature* — the Peierls argument in full: contour
  geometry (`NCG/Upstream/IsingContours.lean`), the planar circuit count
  `#{contours of length n} ≤ 4n·3^{n−1}` **proved** as a theorem
  (`NCG/Upstream/CircuitCount.lean`: a discrete Jordan theory via
  column-parity interiors, a no-proper-even-decomposition theorem, Euler
  circuits, and a `{1,2,3}`-turn walk coding; the one geometric hypothesis —
  upward escape of the volume's complement — is proved for all rectangles
  and disclosed as genuinely necessary in general), giving the uniform
  magnetization `⟨τ₀⟩ ≥ 203/216` (`box_magnetization`, zero hypotheses).
  The infinite-volume phases are genuine **states** with the **DLR
  property** (`NCG/Upstream/GibbsDLR.lean`: `gibbsPlus`, `gibbsMinus`,
  `gibbsPlus_dlr`), separated by the deck-odd spin test
  (`phases_distinct`: magnetizations `≥ 203/216` and `≤ −203/216`).
- *Clause (i), high temperature* — **Dobrushin uniqueness proved in full**
  (`NCG/Upstream/DobrushinUnique.lean`): the sharp single-site influence
  bound `tanh θ`, the oscillation-contraction descent against the harmonic
  series, and `dlrState_unique` — at `4·tanh θ < 1` any two DLR states
  coincide on all bounded local observables; the unique state is deck-flip
  invariant with zero magnetization (`gibbsPlus_spin_zero`), so the torsion
  defect vanishes.
- *Clause (iii)* — the symmetric mixture satisfies the same DLR law with
  zero defect (`gibbsMix_dlr`, `gibbsMix_spin`).

* **Complete positivity of the Lindblad semigroup**
(`thm:stable-pointer-selection` clause (ii)) — `e^{tℒ}` is completely
positive, proved from scratch: Kraus/conjugation splitting of the
dissipator, a Banach-algebra second-order exponential remainder bound
(absent from Mathlib), the full Euler–Trotter product limit with explicit
constants, and closedness of the ampliation-stable cone.
*Lean:* `NCG/Upstream/LindbladCP.lean`
(`NCG.Upstream.exp_dissipator_preservesPos`).

* **Predictive compression forces renewal memory**
(`thm:minimal-predictive-memory`, `thm:predictive-compression-stability`,
`cor:renewal-retract`) — minimality and uniqueness of predictive memory,
with quantitative stability of the compressed dynamics.
*Lean:* `NCG/Upstream/Retract.lean`, `LinearStability.lean`.

* **The complex predictive algebra** (`thm:complex-algebra`,
`thm:structural-reconstruction`, `thm:two-path-complex-face`) — the
operational state space embeds in a formally real Euclidean Jordan algebra;
two-path interference forces complex matrix faces; the finite predictive
algebra is reconstructed structurally.
*Lean:* `NCG/Algebra/JordanFace.lean`, `SpinFactor.lean`,
`NCG/Upstream/CommonOriginUCP.lean`.

* **Retrodiction and KMS structure** (`thm:petz-properties`,
`cor:common-petz-family`, `thm:predictive-reference-renewal`) — the
canonical Petz adjoint, the common KMS–Petz family, and the predictive
derivation of reference renewal with exact scalar path laws.
*Lean:* `NCG/Upstream/KMSDual.lean`, `PetzBranch.lean`, `PathLaw.lean`.

* **Signed covers from records** (`thm:determinant-cover`,
`thm:noisy-record-orientation`, `thm:record-parity-unique`) — the
determinant line induces the principal signed cover; determinant-regular
noisy records still orient it; resolved-record parity is unique.
*Lean:* `NCG/Graph/RecordOrientation.lean`, `NCG/Upstream/RecordParity.lean`.

* **Pressure and the modular clock** (`thm:pressure-root`,
`thm:entropy-affinity-depth`, `thm:exchange-pressure-stationarity`) — the
stationary pressure law selects a unique root; the entropy–affinity–depth
identity; zero exchange source is exactly the torsion-free stationary point.
*Lean:* `NCG/Upstream/CWPressure.lean`, `EntropyAffinity.lean`,
`ExchangePressure.lean`.

* **The common-origin phase** (`thm:common-origin-phase`,
`cor:full-phase-nonempty`) — the unified finite phase satisfying all the
paper's criteria simultaneously exists: resolved balance + primitivity +
Clifford factor + KMS, assembled and nonempty.
*Lean:* `NCG/Upstream/CommonOriginBalance.lean`, `CommonOriginKMS.lean`,
`CommonOriginFrame.lean`.

## How to review a single statement

1. Look up the label in [`statements.json`](statements.json) — e.g.
   `"thm:torsion-phase-coexistence"`. The record gives `status`, the list of
   Lean anchors (`lean`), and a `note` describing scope and proof route
   (the notes for the Ising suite narrate the entire formalization
   history, including the audits).
2. Open the cited file in `NCG/` and inspect the theorem statement — all
   hypotheses are explicit in the Lean signature.
3. `#print axioms <name>` confirms the axiom footprint;
   `lake build` re-checks everything from source.
