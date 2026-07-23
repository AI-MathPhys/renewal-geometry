# Faithfulness audit — 2026-07-22

This automated audit verifies if every tracked record correspond **exactly** to the statement as written in the current manuscript text, with no undisclosed narrowing, no extra assumptions and no tautological anchors. This file audits all **333 records**:

- **210** in [`lorentzian_emergence/statements.json`](lorentzian_emergence/statements.json)
  against [`lorentzian_emergence/lorentzian_emergence.tex`](lorentzian_emergence/lorentzian_emergence.tex)
  (*Renewal Spectral Geometry and the Emergence of Lorentzian Spacetime*);
- **123** in [`renewal_emergence/statements.json`](renewal_emergence/statements.json)
  against [`renewal_emergence/renewal_emergence.tex`](renewal_emergence/renewal_emergence.tex)
  (*From Operational Prediction to Signed Renewal Memory*).

## Method

Every record was compared against the manuscript text by multiple independent
adversarial passes over the full ledgers, on four axes:

1. **Generality** — the Lean statement quantifies over what the text
   quantifies over: no silent specialization to a concrete model, index type,
   or parameter value.
2. **Hypotheses** — the Lean theorem assumes nothing the text does not; where
   a classical literature input is taken in hypothesis form, the record note
   says so.
3. **Conclusion coverage** — every clause of the manuscript statement
   (including boxed identities and enumerated conclusions) is either proved by
   the cited anchors or explicitly listed in the note as not covered.
4. **Anchor content** — the cited anchors carry genuine mathematical content:
   no definitional repackaging, no hypothesis restating the conclusion, no
   stale identifiers.

Mechanical layer: both coverage checkers pass with **0 conditional records**
(the checkers also fail on stale or missing Lean identifiers), the build is
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

## Totals

| | EXACT / FAITHFUL-SCOPED | UNDISCLOSED-GAP | TAUTOLOGY | MISMATCH | ADDED-ASSUMPTION |
|---|---|---|---|---|---|
| lorentzian_emergence (210) | 210 | **0** | **0** | **0** | **0** |
| renewal_emergence (123) | 123 | **0** | **0** | **0** | **0** |
| **total (333)** | **333** | **0** | **0** | **0** | **0** |

Statuses: **286 `proved`** (193 + 93) and **47 `statement_encoded`** (17 + 30;
all but three are definition environments — see "Interface records" below).
**0 conditional, 0 not started, 0 `sorry`.** Every remaining formalization gap
is disclosed in the corresponding record's note, which is the authoritative
per-statement source.

## Records under closest scrutiny

All 333 records were audited on the four axes above; coverage is the totals
table, not this section. The records below are the subset that additionally
received a deep manual pass — reading the Lean proof terms against the
manuscript clause by clause — because their *shape* carries the highest risk
of a formalization silently under-delivering:

- **Tautology risk** — statements whose cheapest possible anchor would be
  technically true but empty (e.g. a complexity gap whose headline arithmetic
  is an identity: the record only has content if the algebra dimension itself
  is computed).
- **Structure-field risk** — packaged claims that could be "proved" by
  defining a structure whose fields are the conclusions; the check is that
  the conclusions are *derived*.
- **Missing-clause risk** — boxed multi-clause theorems, where proving most
  clauses looks complete; the check is clause-by-clause coverage.
- **Hidden-scoping risk** — the heaviest analytic and statistical-mechanics
  content, where a quiet specialization (a stronger hypothesis, a smaller
  model) would be tempting.
- **Claim-carrying definitions** — definition environments whose encoding
  choices silently strengthen or weaken every downstream theorem.

All verify **EXACT**; the "verified content" column states, for each record,
precisely the non-trivial content that the risk pattern above would have
omitted — i.e. what was checked to be actually present:

### renewal_emergence

| Label | Verified content |
|---|---|
| `prop:reversible-realisation-sharp-purification` | (O2) is encoded at the transformation level and `sharpPurificationPkg_of_realisation` **derives** SP1–SP4 from it (`NCG/Upstream/OperationalModel.lean`) — the package is a theorem, not a bundle of fields |
| `def:sharp-purification` | the determinism marker (`DetMarking`) makes `causal` quantify over exactly the effects the text intends; `statement_encoded` |
| `thm:universal-quotient` | symmetric monoidal structure on `CategoryTheory.Quotient` together with the universal property of the monoidal quotient (`NCG/Upstream/MonoidalQuotient.lean`) |
| `thm:operational-ucp` | positivity is derived from state separation and unitality from determinism (`operational_positive`, `operationalToUCP`) — the central iff is proved, not `Iff.rfl` |
| `prop:branchwise-petz-reference-renewal` | all six clauses for a general CP trace-nonincreasing branch (`NCG/Upstream/PetzBranch.lean`) |
| `thm:canonical-record-algebra` | both halves, including the generated-algebra half via the indicator-product separation argument (`NCG/Upstream/RecordAlgebra.lean`) |
| `thm:stable-pointer-selection` (CP clause) | complete positivity of `e^{tℒ}` by a full Euler–Trotter argument (`exp_dissipator_preservesPos`, `NCG/Upstream/LindbladCP.lean`) |
| torsion pair (`thm:torsion-phase-coexistence`, `cor:torsion-selection`) | genuine infinite-volume 2d Ising phase coexistence: Peierls with the **proved** planar circuit count `4n·3^{n−1}` (`NCG/Upstream/CircuitCount.lean`, `box_magnetization` with zero hypotheses), DLR states `gibbsPlus`/`gibbsMinus` with phase separation `±203/216` (`NCG/Upstream/GibbsDLR.lean`), and Dobrushin uniqueness at `4·tanh θ < 1` (`dlrState_unique`, `NCG/Upstream/DobrushinUnique.lean`) |
| `thm:deck-observability` | the ω± even-agreement / odd-flip criterion (`NCG/Upstream/DeckSymmetry.lean`) |
| `thm:affinity-conductance` | the boxed capacity factorization `c_e = √(q_e q_ē)` with uniqueness (`NCG/Upstream/CapacityFactorization.lean`) |
| `prop:cancellation` | `Φ_sym` KMS-self-adjointness and uniqueness of the sym/asym decomposition (`NCG/Upstream/Current.lean`) |
| `thm:affine-clock` | general edge depths `ℓ_e` (`NCG/Upstream/ModularSpectral.lean`) |
| `prop:metric-comparison` | the `O(d)` half holds unconditionally and is stated separately (`NCG/Lorentz/SecondMoment.lean`) |
| `thm:complex-algebra` | the Jordan stage is derived via a from-scratch Euclidean Jordan rank-two layer (`NCG/Algebra/SpinFactor.lean`, `NCG/Algebra/JordanFace.lean`) |

### lorentzian_emergence

| Label | Verified content |
|---|---|
| `cor:sharp-existence` | both conjuncts of the boxed iff; the increment half via the commutator factorization `[D,S] = S·diag` (`NCG/Operator/FibreDichotomy.lean`) |
| `thm:classification` | the variable-rank derivation: rank forced to two, cone rigidity, `{1,S}` permutation cases, transition cochain (`NCG/Krein/EnrichmentMinimality.lean`), with the naturality riders in `NCG/Krein/EnrichmentNaturality.lean` |
| `lem:complexity-gap` | `revisionAlgebra_finrank` computes the matrix-algebra dimension; `complexity_gap` derives the gap (`NCG/Dimension/PowerCounting.lean`) |
| `lem:realized-reversible-subgroup` | sheet-action additivity is **derived** in the cover model, not assumed as a structure field (`NCG/Krein/SheetRealization.lean`) |
| `thm:rg-no-dimension-selection`, `thm:minimal-field` | the engineering-dimension calculus is derived from the kinetic constraint, and `minimal_field_degree_forcing` derives the field degree with no degree hypothesis (`NCG/Dimension/PowerCounting.lean`) |
| `thm:pressure-selects-beta` | the pressure trichotomy on the Gelfand–Fekete growth rate, with the concluding Perron remark fully formalized: eigenvector existence/positivity/simplicity (`NCG/Lorentz/PerronExistence.lean`) and the identification of the growth rate with the Perron eigenvalue for irreducible kernels (`NCG/Lorentz/PerronPressure.lean`) |
| `thm:triple` (b) | the zeta-abscissa identity in both directions via dyadic Dirichlet estimates (`NCG/Renewal/ZetaAbscissa.lean`) |

## FAITHFUL-SCOPED register

Records whose notes disclose a precise scoped gap between the Lean anchors and
the full manuscript statement. The record note is authoritative in each case;
the principal entries are:

- `thm:temporal-row` — the general dressed-revision-operator clause.
- `thm:marked-torus-band-limit`, `thm:marked-torus-classification`,
  `thm:marked-torus-correspondence` — the notes state exactly which displayed
  clauses the anchors cover.
- `thm:qmet-qalg` — strictness regimes.
- `thm:stability` — which of the enumerated conclusions are covered.
- `thm:metric-reconstruction`, `cor:symbol-reconstruction` — polarisation-core
  versus intertwiner content.
- `thm:macroscopic-domain`, `lem:constant-dirac-kernel`,
  `thm:constant-inner-characterization` — discrete surrogate scope.
- `thm:full-isotropy-interference` — the `d = 3` existence half.
- `prop:renewal-calibration` — the `2 ≤ |E|` case hypothesis.
- `constr:pressure-law` — the Doob law includes the `r`-normalization, and the
  derivative identity `μ_ℓ = −P′(β)` is not formalized.
- `prop:metric-collapse`, `cor:curved-stability`, `prop:fibres-monoid`,
  `prop:symmetric-alternating-independence`, `cor:canonical-hyperbolic-core`,
  `thm:intrinsic-graded-clifford-datum` — scope stated in each note.

A global implementation choice, disclosed wherever it is used: the spectral
radius is implemented as the Gelfand–Fekete growth rate `pRad`; its
identification with the Perron eigenvalue is proved for irreducible kernels
(equivalently, under the diagonal-witness hypothesis the pressure theorems
carry explicitly).

## Interface records (`statement_encoded`, 47)

44 are definition environments — objects with nothing to prove, checked for
faithful encoding. The three theorem-environment interface records are the
manuscripts' **declared external classical inputs**, encoded in exactly the
form the text uses them:

- `thm:sprinkling` (lorentzian_emergence) — the Poisson-sprinkling covariance
  interface; Poisson-process existence is the cited textbook input.
- `thm:operational-diagonalization`, `thm:operational-jordan`
  (renewal_emergence) — the Jordan–von Neumann–Wigner /
  operational-diagonalization classification interface
  (`NCG/Algebra/JordanFace.lean`).

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
#print axioms Matrix.IsIrreducible.exists_pos_eigenvector
-- [propext, Classical.choice, Quot.sound]
```
