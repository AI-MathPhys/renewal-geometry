# Faithfulness audit — 2026-07-22

This audit checks if every tracked record correspond **exactly** to the statement as written in the
current manuscript text — no undisclosed narrowing, no extra assumptions, no
tautological anchors? This file is the current audit of all **333 records**:

- **210** in [`lorentzian_emergence/statements.json`](lorentzian_emergence/statements.json)
  against [`lorentzian_emergence/lorentzian_emergence.tex`](lorentzian_emergence/lorentzian_emergence.tex)
  (*Renewal Spectral Geometry and the Emergence of Lorentzian Spacetime*);
- **123** in [`renewal_emergence/statements.json`](renewal_emergence/statements.json)
  against [`renewal_emergence/renewal_emergence.tex`](renewal_emergence/renewal_emergence.tex)
  (*From Operational Prediction to Signed Renewal Memory*).

## Method

1. **Initial adversarial audit (2026-07-21).** Ten independent audit passes compared
   every record's Lean anchors against the manuscript text. Findings at that time:
   32 undisclosed gaps, 5 tautological anchors, 4 mismatches, 0 added assumptions.
2. **Remediation campaign (2026-07-21 → 2026-07-22).** Every finding was resolved by
   one of: (a) **re-proving the statement as written** in Lean (the large majority —
   see the resolution ledgers below); (b) **reclassifying** the record from `proved`
   to `statement_encoded` where the environment's role is definitional/interface;
   (c) **disclosing** the precise remaining gap in the record's note (tagged
   `AUDIT-2026-07-21` / `AUDIT-2026-07-22`), turning an undisclosed gap into a
   documented scoped one.
3. **Re-verification pass (this file, 2026-07-22).** Every finding of the initial
   audit was re-checked against the current ledgers: each flagged label now either
   cites new Lean anchors proving the statement as written, or carries an explicit
   audit note stating exactly what is and is not covered. Mechanical checks:
   both coverage checkers pass with **0 conditional records**, the build is
   **`sorry`-free**, and the headline theorems depend only on
   `propext, Classical.choice, Quot.sound` (verified with `#print axioms`).

## Verdict key

- **EXACT** — the Lean statement expresses the manuscript claim in its stated generality.
- **FAITHFUL-SCOPED** — a gap exists (specialization, hypothesis-form literature input,
  informal packaging) and the record note discloses it accurately.
- **UNDISCLOSED-GAP** — Lean is weaker/narrower than the manuscript and the note does
  not say so.
- **TAUTOLOGY** — the anchored "proved" content is definitional repackaging or a
  hypothesis restating the conclusion.
- **MISMATCH** — the anchors formalize a different statement than the current text.

## Current totals

| | EXACT / FAITHFUL-SCOPED | UNDISCLOSED-GAP | TAUTOLOGY | MISMATCH | ADDED-ASSUMPTION |
|---|---|---|---|---|---|
| lorentzian_emergence (210) | 210 | **0** | **0** | **0** | **0** |
| renewal_emergence (123) | 123 | **0** | **0** | **0** | **0** |
| **total (333)** | **333** | **0** | **0** | **0** | **0** |

Statuses: **286 `proved`** (193 + 93) and **47 `statement_encoded`** (17 + 30; all but
three are definition environments — see "Interface records" below). **0 conditional,
0 not started, 0 `sorry`.** Every remaining formalization gap is disclosed in the
record's note; 118 records carry explicit `AUDIT`-tagged annotations documenting
scope, corrections, or the re-proof that closed the original finding.

## Resolution ledger — the 12 HIGH findings

### renewal_emergence

| Label | 2026-07-21 finding | Resolution |
|---|---|---|
| `prop:reversible-realisation-sharp-purification` | TAUTOLOGY (field-for-field repackaging) | **Re-proved.** (O2) encoded at transformation level; `sharpPurificationPkg_of_realisation` derives SP1–SP4 (`NCG/Upstream/OperationalModel.lean`) |
| `def:sharp-purification` | undisclosed encoding defect (`causal` over all effects) | **Fixed & reclassified.** `DetMarking` adds the determinism marker; record is `statement_encoded` with the repair documented |
| `thm:universal-quotient` | MISMATCH (anchors proved a different theorem) | **Re-proved.** Symmetric monoidal structure on `CategoryTheory.Quotient` + universal property (`NCG/Upstream/MonoidalQuotient.lean`) |
| `thm:operational-ucp` | TAUTOLOGY (central iff was `Iff.rfl`) | **Re-proved.** Positivity derived from state separation, unitality from determinism (`operational_positive`, `operationalToUCP`) |
| `prop:branchwise-petz-reference-renewal` | MISMATCH (old instrument, wrong clause list) | **Re-proved.** All six clauses for a general CP trace-nonincreasing branch (`NCG/Upstream/PetzBranch.lean`) |
| `thm:canonical-record-algebra` | UNDISCLOSED-GAP (content half missing) | **Re-proved.** Generated-algebra half via the indicator-product separation argument (`NCG/Upstream/RecordAlgebra.lean`) |

### lorentzian_emergence

| Label | 2026-07-21 finding | Resolution |
|---|---|---|
| `cor:sharp-existence` | UNDISCLOSED-GAP (increment conjunct dropped) | **Re-proved.** Both conjuncts of the boxed iff, increment half via the commutator factorization `[D,S] = S·diag` (`NCG/Operator/FibreDichotomy.lean`) |
| `thm:classification` | UNDISCLOSED-GAP (reduction baked into the encoding) | **Re-proved.** Variable-rank derivation: rank forced to two, cone rigidity, `{1,S}` permutation cases, transition cochain (`NCG/Krein/EnrichmentMinimality.lean`) |
| `lem:complexity-gap` | TAUTOLOGY (anchor was `2^(m+3) = 4·2^(m+1)`) | **Re-proved.** `revisionAlgebra_finrank` computes the matrix dimension; `complexity_gap` derives the gap (`NCG/Dimension/PowerCounting.lean`) |
| `lem:realized-reversible-subgroup` | TAUTOLOGY (closure facts were structure fields) | **Re-proved.** Sheet-action additivity **derived** in the cover model (`NCG/Krein/SheetRealization.lean`) |
| `thm:rg-no-dimension-selection` | TAUTOLOGY (headline anchor `(d+1)−d = 1`) | **Re-proved.** Engineering-dimension calculus from the kinetic constraint (`NCG/Dimension/PowerCounting.lean`) |
| `thm:minimal-field` | TAUTOLOGY (conclusion assumed as hypothesis) | **Re-proved.** `minimal_field_degree_forcing` derives the degree; no `hdeg` hypothesis |

## Resolution ledger — the MEDIUM findings

All resolved; the ones with genuine mathematical content were re-proved:

- **Re-proved as stated**: `thm:deck-observability` (ω± even-agreement/odd-flip
  criterion, `NCG/Krein/DeckSymmetry.lean`); `thm:affinity-conductance` (boxed
  capacity factorization `c_e = √(q_e q_ē)` + uniqueness,
  `NCG/Upstream/CapacityFactorization.lean`); `prop:cancellation` (`Φ_sym`
  KMS-self-adjointness + uniqueness of the decomposition, `NCG/Upstream/Current.lean`);
  `cor:minimal-signed-enrichment` (all three clauses,
  `NCG/Krein/EnrichmentMinimality.lean`); `thm:pressure-path-clock` (graded path
  clock with the boxed identity, `NCG/Upstream/PathClock.lean`); `thm:affine-clock`
  (general edge depths `ℓ_e`, `NCG/Upstream/ModularSpectral.lean`);
  `prop:metric-comparison` (unconditional `O(d)` half stated separately,
  `NCG/Lorentz/SecondMoment.lean`); `thm:ehrhart-order` / `cor:ehrhart-free`
  (re-anchored to the interval count `NCG.card_interval`); `thm:full-operator`
  (stale anchor removed); `prop:fibres-automata` / `cor:automatic-triples` (graded
  automata, `NCG/Renewal/GradedAutomaton.lean`); `thm:complex-algebra` (Jordan stage
  derived via the Euclidean Jordan rank-two layer, `NCG/Algebra/JordanFace.lean`).
- **Reclassified to `statement_encoded`** (interface records, see below):
  `thm:operational-diagonalization`, `thm:operational-jordan`, `def:process-system`.
- **Disclosed** (gap now stated precisely in the note — FAITHFUL-SCOPED):
  `thm:temporal-row` (the general dressed-revision-operator clause),
  `thm:marked-torus-band-limit` / `thm:marked-torus-classification` /
  `thm:marked-torus-correspondence` (which displayed clauses the anchors cover),
  `thm:qmet-qalg` (strictness regimes), `thm:stability` (which of the enumerated
  conclusions are covered), `thm:metric-reconstruction` / `cor:symbol-reconstruction`
  (polarisation core vs. intertwiner content), `thm:macroscopic-domain` /
  `lem:constant-dirac-kernel` / `thm:constant-inner-characterization` (discrete
  surrogate scope), `thm:full-isotropy-interference` (d = 3 existence half),
  `prop:renewal-calibration` (the `2 ≤ |E|` case hypothesis),
  `prop:metric-collapse`, `cor:curved-stability`, `prop:fibres-monoid`,
  `prop:symmetric-alternating-independence`, `cor:canonical-hyperbolic-core`,
  `thm:intrinsic-graded-clifford-datum`.

## Former scoped inputs — now proved outright

The initial audit listed several "real projects" as the remaining scoped inputs.
All have since been **proved in full**, with no disclosed statistical-mechanics or
analytic inputs remaining:

| Former scoped input | Now proved |
|---|---|
| Planar circuit count `4n·3^{n−1}` | `NCG/Upstream/CircuitCount.lean` — discrete Jordan theory (column-parity interiors, no-proper-even-decomposition), Euler circuits, `{1,2,3}`-turn coding; `box_magnetization` with zero hypotheses |
| DLR/extremality packaging | `NCG/Upstream/GibbsDLR.lean` — infinite-volume states `gibbsPlus`/`gibbsMinus` with the DLR property; phase separation `±203/216` (`phases_distinct`) |
| Infinite-volume Dobrushin uniqueness | `NCG/Upstream/DobrushinUnique.lean` — sharp `tanh θ` influence bound, oscillation descent, `dlrState_unique`, zero magnetization at `4·tanh θ < 1` |
| Complete positivity of `e^{tℒ}` | `NCG/Upstream/LindbladCP.lean` — full Euler–Trotter proof (`exp_dissipator_preservesPos`) |
| Zeta abscissa of `thm:triple`(b) | `NCG/Renewal/ZetaAbscissa.lean` — both directions via dyadic Dirichlet estimates |
| Naturality riders of `thm:classification` | `NCG/Krein/EnrichmentNaturality.lean` |

The one caveat noted by the initial audit's adversarial pass that has been
**upgraded**: `phase_pair_of_uniform_bound` (number sequences, not states) is
superseded — the extremal-phase clause is now carried by genuine DLR states.
The one caveat that **remains, disclosed**: `pRad` equals the spectral radius
only under `HasDiagWitness` (stated in the relevant notes).

## Interface records (`statement_encoded`, 47)

44 are definition environments — objects with nothing to prove,
checked for faithful encoding. The three theorem-environment interface records are
the manuscripts' **declared external classical inputs**, encoded in exactly the form
the text uses them:

- `thm:sprinkling` (lorentzian_emergence) — the Poisson-sprinkling covariance
  interface; Poisson-process existence is the cited textbook input.
- `thm:operational-diagonalization`, `thm:operational-jordan` (renewal_emergence) —
  the Jordan–von Neumann–Wigner / operational-diagonalization classification
  interface (`NCG/Algebra/JordanFace.lean`).

## Mechanical verification

```bash
python scripts/check_statement_coverage.py
# Statement coverage passed (210 records): computer_certified=0,
#   conditional_interface=0, not_started=0, proved=193, statement_encoded=17
python scripts/check_statement_coverage.py --notes
# Statement coverage passed (123 records): computer_certified=0,
#   conditional_interface=0, not_started=0, proved=93, statement_encoded=30
lake build     # Build completed successfully — 0 sorry
```

```lean
#print axioms NCG.Upstream.Ising.dlrState_unique
-- [propext, Classical.choice, Quot.sound]
#print axioms NCG.Upstream.Ising.box_magnetization
-- [propext, Classical.choice, Quot.sound]
#print axioms NCG.Upstream.exp_dissipator_preservesPos
-- [propext, Classical.choice, Quot.sound]
```
