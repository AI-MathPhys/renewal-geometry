# Renewal Spectral Geometry and the Emergence of Lorentzian Spacetime

**A. Pélissier** — formal verification companion.

This folder contains the manuscript and its complete, machine-checked
statement inventory. Every named statement environment of the paper
(theorem / proposition / lemma / corollary / definition / construction) is
tracked in [`statements.json`](statements.json), which maps each label to the
Lean identifiers in [`NCG/`](../../NCG) that formalize it, together with an
honesty note describing exactly what was proved.

| File | Contents |
|---|---|
| [`lorentzian_emergence.tex`](lorentzian_emergence.tex) | The manuscript source |
| [`lorentzian_emergence.pdf`](lorentzian_emergence.pdf) | The compiled manuscript |
| [`statements.json`](statements.json) | The per-statement verification ledger (label → status → Lean anchors → note) |

## Verification summary

**210 tracked statements. 0 `sorry`. 0 conditional. 0 unformalized.**

Every claim-bearing statement of the paper (theorem / proposition / lemma /
corollary) is **proved in Lean**, with a single declared exception (see below):

| Environment | Proved | Encoded interface | Total |
|---|---:|---:|---:|
| Theorems | 77 | 1 | 78 |
| Propositions | 39 | 0 | 39 |
| Lemmas | 30 | 0 | 30 |
| Corollaries | 28 | 0 | 28 |
| *Claim-bearing subtotal* | *174* | *1* | *175* |
| Definitions | 19 | 16 | 35 |
| **Total** | **193** | **17** | **210** |

What the two statuses mean:

- **Theorems / propositions / lemmas / corollaries** — `proved` means the
  statement's mathematical content is proved sorry-free in Lean; any scoped
  hypothesis is disclosed in the record's note *and* appears explicitly in the
  Lean signature. The one exception, `thm:sprinkling`, is the paper's declared
  classical input: the Poisson-sprinkling covariance interface is encoded in
  exactly the form the text uses it, with textbook Poisson-process existence as
  the cited external result.
- **Definitions** — a definition environment usually has nothing to *prove*;
  `statement_encoded` (16 records) means the object is faithfully transcribed
  as a Lean definition or structure. A definition is marked `proved`
  (19 records) when the manuscript's definition **carries claims** — that a
  quantity is well-posed, that a minimum is attained, that a quotient or
  monoid structure is well-defined — and those embedded claims are proved in
  Lean (e.g. `def:qalg`, whose growth exponent requires the finite-shell
  theorem for well-posedness). So `proved` on a definition is *stronger* than
  `statement_encoded`, never weaker.

### Axioms

Every theorem in the library depends only on Lean's three standard axioms —
the identical foundation used by Mathlib itself:

```
propext, Classical.choice, Quot.sound
```

No `sorryAx` (no `sorry` anywhere in the build), no `native_decide`, no
custom axioms. This can be reproduced for any theorem with, e.g.:

```lean
#print axioms NCG.Upstream.exp_dissipator_preservesPos
-- 'NCG.Upstream.exp_dissipator_preservesPos' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

### Reproducing the check

```bash
lake build                        # kernel-checks the library
python scripts/check_statement_coverage.py lorentzian_emergence
# Statement coverage passed for lorentzian_emergence (210 records):
#   computer_certified=0, conditional_interface=0, not_started=0,
#   proved=193, statement_encoded=17
```

The checker parses every named statement out of the `.tex`, requires a
record for each, rejects stale records, and verifies that every cited Lean
identifier exists in the library. `--list proved` (etc.) enumerates a
category.

## Headline theorems

A guide to the main results and where to inspect them.
(Statement labels are the `\label`s in the manuscript)

* **The predictive spectral triple** (`thm:triple`) — the renewal data
assembles into a genuine spectral triple; the commutator formula
`[D, Ŝ] = (Λ(σw) − Λ(w))·shift` and the zeta-function abscissa
`abscissa(ζ_CP) = q_alg` are proved in both directions (dyadic Dirichlet
estimates in `ℝ≥0∞`).
*Lean:* `NCG.diagOp_comm_shiftOp_single`, `NCG/Renewal/ZetaAbscissa.lean`.

* **The signed sector is forced and classified** — positivity obstruction
(`cor:positivity-obstruction`, `thm:irreducible-positive-no-go`): a
nontrivial fundamental symmetry cannot live in a positive sector; minimal
enrichments are classified by `H¹(G, ℤ/2)` (`thm:classification`, with
naturality under graph isomorphisms and rank-minimality derived, not
assumed).
*Lean:* `NCG/Krein/EnrichmentClassification.lean`,
`EnrichmentNaturality.lean`, `EnrichmentMinimality.lean`.

* **The canonical signed modular Dirac** (`thm:signed-dirac`,
`thm:modular-characterisation`, `thm:canonical-temporal-row`) — deck-odd
normal form `D₀ = J·g`, the exponential weight `e^{βN}` forced on shift
orbits, and the cycle Krein exchange sign given by gauge-invariant holonomy.
*Lean:* `NCG/Krein/ModularDirac.lean`, `TemporalRow.lean`.

* **Levi–Civita is derived** (`thm:fundamental`, `thm:channel-torsion`) — the
discrete Cartan chapter: Koszul existence/uniqueness, the plaquette defect
exactly `h²T + O(h³)`, and two-scale closure forcing torsion `T = 0` while
curvature survives.
*Lean:* `NCG/Lorentz/DiscreteCartan.lean` (`NCG.cartan_uniqueness`,
`NCG.torsion_of_first_moment_closure`).

* **Lorentzian continuum limits** (`thm:operator-limit`,
`thm:band-norm-resolvent`, `thm:curved-limit`, `thm:self-averaging`,
`thm:frame-universality`, `thm:universality`) — operator-level Clifford
continuum limits: graph convergence of the full signed Dirac, band-limited
norm-resolvent convergence, curved Levi–Civita strong-resolvent limits,
self-averaging under nondegeneracy, and universality/inverse theorems for
the Lorentzian principal symbol.
*Lean:* `NCG/Lorentz/OperatorLimit.lean`, `FrameUniversality.lean`,
`CurvedHamiltonian.lean`, `SelfAveraging.lean`.

* **`3+1` selection** (`thm:minimal-nondegenerate-3plus1`,
`thm:interference-closure-selects-three`, `thm:access-efficiency-selection`,
`thm:real-even-division-selects-three`) — nondegenerate alternating forms
need even dimension (no `2+1`); oriented volume-dual interference closure
selects three spatial dimensions; the access efficiency `η(m) = m/2^m` is
uniquely maximised at `m = 3`; isotropy is dimension-blind (so it cannot do
the selecting).
*Lean:* `NCG/Dimension/EvenRank.lean`, `AccessSelection.lean`,
`NCG/Lorentz/InterferenceClosure.lean`.

* **Minkowski emergence and obstructions** (`thm:minkowski-2d`,
`thm:taxicab-limit`, `thm:obstruction`) — the two-generator causal order is
exactly the 2d Minkowski cone with `τ² = uv`; polyhedral Lorentzian continua
exist in general, but smooth higher-dimensional emergence is polyhedrally
obstructed.
*Lean:* `NCG/Lorentz/ProductOrder.lean`, `PolyhedralObstruction.lean`.

* **Dimension coincidence** (`thm:qmet-qalg-equality`,
`thm:dimension-coincidence`, `thm:weyl-law`) — metric and algebraic
predictive dimensions coincide; the renewal Weyl law with residue volume;
the crystal counting function's log–log dimension as an actual limit.
*Lean:* `NCG/Renewal/Dimensions.lean`, `CrystalCount.lean`,
`WeylDichotomy.lean`.

## How to review a single statement

1. Look up the label in [`statements.json`](statements.json) — e.g.
   `"thm:fundamental"`. The record gives `status`, the list of Lean anchors
   (`lean`), and a `note` describing scope and proof route.
2. Open the cited file in `NCG/` and inspect the theorem statement — all
   hypotheses are explicit in the Lean signature.
3. `#print axioms <name>` confirms the axiom footprint;
   `lake build` re-checks everything from source.
