# Renewal Geometry in Lean 4

A [Lean 4](https://lean-lang.org/) / [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of **Renewal Geometry**, the programme in which spacetime,
spectral (noncommutative) geometry and Standard-Model internal structure are
reconstructed as effective descriptions of a common finite predictive
structure, together with the generic **mathematical-physics machinery** the
proofs need and Mathlib does not yet contain.

The repository is the proof backend of four companion papers (see
[Papers](#papers)). Every named statement of every paper is tracked in a
machine-checked ledger that says exactly what is proved, what is merely
encoded, and what is still open.

## Papers

Each paper has a folder under [`papers/`](papers/) with the LaTeX source, the
PDF, a `paper.json` manifest, the ledger `statements.json` mapping **every**
theorem/proposition/lemma/corollary/definition environment to its status and
Lean declarations, and a generated README listing every record.

| Paper | Statements | Proved | Encoded | Open |
|---|---:|---:|---:|---:|
| [From Predictive Dynamics to Spectral Geometry](papers/predictive_spectral_geometry/) | 88 | 77 | 11 | 0 |
| [Renewal Geometry and the Emergence of Lorentzian Spacetime](papers/emergent_spacetime/) | 198 | 157 | 14 | 27 |
| [Variational Closure of Finite Einstein–Standard-Model Actions](papers/variational_closure_einstein_sm/) | 134 | 123 | 11 | 0 |
| [Action–Multiplicity Duality for Spacetime–Gauge Incidence](papers/action_multiplicity_duality/) | 119 | 107 | 12 | 0 |
| **Total** | **539** | **464** | **48** | **27** |

How to read the table:

- *Proved* means the Lean theorem proves the paper's claim as stated, in the
  generality stated; every scoped hypothesis or rendering choice (a
  finite-dimensional surrogate where the paper's object is a continuum one, a
  Fourier-mode representation where the paper works on the grid, a Sobolev
  order 6 where the paper says 11) is disclosed in the record's note.
  *Encoded* means the object is faithfully defined in Lean, with its defining
  conditions and a constructor from the paper's input data, and no proof
  content is claimed.
- *Open* records may point to Lean that proves a special case, one direction
  or some clauses; the note says exactly what is missing. Every open record
  carries a `difficulty` (easy: a day of assembly; medium: days of new finite
  lemmas; hard: infrastructure neither this library nor Mathlib has, or a
  reformulation) and a `plan` naming the missing piece and the files to build
  on.
- Corollaries whose Lean proof takes the conclusion of an unproved parent
  theorem as a hypothesis are kept *open* by policy: a proof of "theorem
  implies corollary" is not a proof of the corollary. The same rule applies to
  a single clause resting on an open statement.
- Every record marked proved has passed a faithfulness audit that reads the
  current manuscript statement and the cited Lean side by side, checking for
  tautologies (an object defined to be the claimed answer, a structure that
  stores the conclusion as a field, an "exactly when" that holds by
  definition), vacuous hypothesis packets, hidden assumptions of the
  conclusion, hypotheses stronger than the paper's named definitions, and
  missing clauses. Where a manuscript statement is ambiguous or false as
  literally written, the record proves the reading the paper's own proof uses
  and says so; these points are collected in the records' notes for the
  author.

Three of the four papers are completely formalized: every record of the
predictive-spectral-geometry paper, the action–multiplicity duality paper and
the variational-closure paper is proved or encoded. The
emergent-spacetime paper is formalized except for 27 hard records
that need input the manuscript does not yet give (the certified N = 3 event
with its triad, preparation equations and certificate matrices, the
graded-chart data behind the boundary sweeps, the c_H row identification of
the slow branch, the continuum consistency budget of the cofinal preparation,
and the same-cylinder Cartan reconstruction); its finite and discrete content,
the explicit phase-compatible finite action and the renewal-to-Einstein
certification chain are proved. Standing rendering choices (spatial sections
as 𝕋³, compact charts as coordinate boxes or balls, trivialised bundles,
χ = 1, Λ = 0, odd N, the symmetric square-root triad) are disclosed in the
records' notes, as are the few places where the Lean proof uses an amended
reading of the manuscript (an extra spatial L³ bound in the Palatini handoff,
a smooth time cut-off for the gauge-robust reader, shift-transported head rows
in the subsidiary system, an adapted Lorentz gauge for the frame bridge,
chart-local smoothness of the theory data).

## Two libraries

| Library | Role | Size |
|---|---|---|
| **`MathPhys`** | Generic mathematical physics, analysis, algebra and geometry with no reference to the programme: known theorems from the literature (Uhlenbeck's Coulomb gauge theorem, Kato's local existence, Perron–Frobenius, Mosco convergence, Lichnerowicz's conformal method, …) and the general infrastructure behind the papers (Sobolev spaces on domains, grids and tori, symmetric-hyperbolic energy estimates, the continuum Einstein–Standard-Model field equations, finite-dimensional operator algebras, lattice gauge theory). Depends on Mathlib only. | 1340 files, ~484k lines |
| **`RenewalGeometry`** | The programme itself, built on `MathPhys`: renewal memories and predictive quotients, the operational and statistical-mechanics upstream layer, Lorentzian emergence and dimension selection, the finite spectralization, commutant-duality and Standard-Model synthesis, the explicit finite actions, records, certificates and regulator sequences of the four papers. | 797 files, ~317k lines |

`MathPhys` never imports `RenewalGeometry`; this is enforced by
[`scripts/check_layering.py`](scripts/check_layering.py) in CI.

### Verification guarantees

- **Sorry-free.** `lake build` kernel-checks all 2137 files; there is no `sorry`.
- **Standard axioms only.** Every Lean declaration cited as *proved* in a
  paper ledger is audited with `#print axioms` by
  [`scripts/audit_axioms.py`](scripts/audit_axioms.py): only `propext`,
  `Classical.choice` and `Quot.sound` may appear (no `sorryAx`, no
  `native_decide`, no custom axioms).
- **Pinned toolchain.** Lean and Mathlib versions are fixed in
  [`lean-toolchain`](lean-toolchain) and
  [`lake-manifest.json`](lake-manifest.json); Mathlib is the only dependency.
- **Faithfulness over coverage.** A ledger record is *proved* only when the
  Lean theorem covers the paper's claim in the generality stated; any scoped
  hypothesis is spelled out in the record's note. Partial results stay *open*
  and say what is missing.

## Which machinery do the papers actually use?

Import closure says which files must *compile*; [`LIBRARY_USAGE.md`](LIBRARY_USAGE.md)
(generated by [`scripts/report_usage.py`](scripts/report_usage.py)) asks the
finer question by walking the proof terms of every ledger-cited declaration:

| | Modules |
|---|---:|
| Used by at least one cited declaration | 1448 |
| Never used, but imported by a used module (structurally required) | 329 |
| Never used and imported by nothing used (removable without loss) | 360 |
| **Total** | **2137** |

The unused part is kept because it is developed to the same standard and
available for future work; nothing in the four ledgers depends on it.

## Installation

```bash
git clone https://github.com/AI-MathPhys/renewal-geometry
cd renewal-geometry
lake exe cache get   # prebuilt Mathlib oleans
lake build           # kernel-checks MathPhys and RenewalGeometry
```

`lake` comes with the Lean toolchain manager
[`elan`](https://github.com/leanprover/elan); the pinned Lean version is
downloaded on first build. In VS Code, install the Lean 4 extension and open
this folder.

## Verifying the claims yourself

```bash
python scripts/check_layering.py               # MathPhys independent of RenewalGeometry; all modules registered
python scripts/check_statement_coverage.py     # every paper statement has a record; every cited Lean declaration exists
python scripts/check_statement_coverage.py emergent_spacetime --list proved
python scripts/audit_axioms.py                 # #print axioms on every proved declaration (needs a build)
python scripts/render_paper_readmes.py         # regenerate the per-paper READMEs from the ledgers
python scripts/report_usage.py > LIBRARY_USAGE.md   # which modules the cited declarations really use (needs a build)
```

The coverage checker fails on a missing or stale record, on a title/environment
mismatch with the manuscript, on a Lean reference that is not of the form
`<path>.lean:<declaration>`, or on a declaration that does not exist in the
cited file. CI runs all of the above on every push.

## Repository layout

```
MathPhys/               -- generic mathematical physics (library `MathPhys`, depends on Mathlib only)
├── NCG/            SpectralGeometry/  OperatorLimits/  OperatorAlgebras/  OperatorTheory/  Krein/
│                   Graph/  PerronFrobenius/  NoncommutativeGeometry/
├── FieldTheory/    Continuum/  Analysis/  Gravity/  GaugeTheory/  LorentzianGeometry/  GaugeGroups/
├── Lattice/        DiscreteAnalysis/  Variational/
├── Stochastics/    StatMech/  MarkovChains/  Probability/  QuantumInformation/  SystemsTheory/
└── Core/           Algebra/  Combinatorics/  Topology/
RenewalGeometry/        -- the programme (library `RenewalGeometry`, depends on MathPhys)
├── Renewal/  Predictive/  Operational/  Measurement/  StatMech/  Lorentz/  Dimension/
├── Spectralization/  Commutant/  StandardModel/  Action/  Gravity/  Continuum/
├── DiscreteAnalysis/  GaugeTheory/  Certificates/  OperatorLimits/  Krein/  Miscellany/  ...
papers/
├── predictive_spectral_geometry/   -- .tex, .pdf, paper.json, statements.json, README.md
├── emergent_spacetime/
├── variational_closure_einstein_sm/
└── action_multiplicity_duality/
scripts/
├── check_statement_coverage.py     -- ledger checker (--init, --list, --summary)
├── check_layering.py               -- import-layering and registration check
├── audit_axioms.py                 -- axiom audit of every proved declaration
├── report_usage.py                 -- proof-term usage report
└── render_paper_readmes.py         -- per-paper README generator
```

## Design principles

1. **A generic core.** Anything that makes sense without the programme lives
   in `MathPhys`, follows Mathlib naming and universe conventions, and is
   meant to be upstreamed.
2. **General definitions, concrete models.** Definitions are stated at the
   papers' level of generality; operator identities are proved first in
   concrete algebraic models where they are exact, then upgraded.
3. **Sorry-free, axiom-clean, honestly scoped.** Nothing is assumed silently:
   what is not formalized is recorded as open in the ledgers, and every
   scoped hypothesis is disclosed in the record note.
4. **Ledgers are the source of truth.** The per-paper READMEs are generated
   from the ledgers and the checker runs in CI, so the README numbers cannot
   drift from what the Lean tree actually contains.

## What is in `MathPhys`

Five thematic top-level folders, each organized by mathematical content; every
file is generic and could be upstreamed.

| Theme / folder | Files | Contents |
|---|---:|---|
| **`NCG/`** | **338** | *Noncommutative geometry and operator theory* |
| `NCG/OperatorLimits` | 167 | Convergence of operators on varying Hilbert spaces: Mosco convergence, strong and norm resolvent limits, the pseudo-resolvent theorem, collectively compact operators, Riesz projections, stable spin atlases, variable-coefficient Dirac operators on the torus |
| `NCG/OperatorAlgebras` | 65 | Finite-dimensional C*- and von Neumann algebra theory: bicommutants, Wedderburn and factor normal forms, Tannaka and Schur, Cauchy–Binet, Howe duality packets, commutant Gram certificates, Peirce decompositions |
| `NCG/SpectralGeometry` | 58 | Graph Connes distances, weighted graph Hodge–Dirac operators, the mesh-graph to Riemannian bridge, finite compact quantum metric spaces, Naimark dilation, operator-valued Stieltjes measures, flat and de Sitter comparisons on the A3 lattice |
| `NCG/Krein` | 20 | Krein spaces and fundamental symmetries, signed Dirac operators, cone positivity, enrichment classification |
| `NCG/OperatorTheory` | 13 | Diagonal operators and fibre dichotomy, Toeplitz operators and number-operator spectral triples, innovation decompositions |
| `NCG/Graph` | 11 | Directed multigraphs, sign cocycles, principal ℤ/2-covers, H¹(G, ℤ/2) and ℤ/4 cohomology, Betti numbers, condensation and decimation |
| `NCG/PerronFrobenius` | 2 | The Perron–Frobenius theorem for irreducible nonnegative matrices (existence, uniqueness, simplicity, Gelfand–Fekete spectral radius), stated against Mathlib's `Matrix.IsIrreducible` |
| `NCG/NoncommutativeGeometry` | 1 | Spectral triples `(𝒜, ℋ, D)` |
| **`FieldTheory/`** | **686** | *Continuum analysis, general relativity and gauge theory* |
| `FieldTheory/Continuum` | 281 | Continuum Einstein–Standard-Model field theory: field spaces and the variational framework, Noether identities, symmetric-hyperbolic L² and H^k energy estimates, Kato local existence by spectral Galerkin with midpoint schemes, the first-order actual-jet system with sector-wise constraint propagation (Dirac back-reaction included), the Lichnerowicz conformal method, Cauchy–Kovalevskaya, generated finite dynamics and their readouts, weak matter equations, torus Sobolev transfer and Aubin–Lions, critical quotient compactness with defect measures |
| `FieldTheory/Analysis` | 227 | Sobolev spaces on open sets, boxes, balls and tori with the critical embedding H¹ ↪ L⁴, Rellich and Kolmogorov–Riesz compactness, Vitali and de la Vallée-Poussin, mollifiers, L^p duality and weak-* compactness of measures, Gevrey and strip-holomorphic Fourier decay, the analytic implicit function theorem, Lyapunov–Perron, Hermite interpolation; Uhlenbeck's small-energy Coulomb gauge theorem on the 4-ball (divergence theorem and Gaffney inequality on balls, Neumann regularity up to the boundary, Sobolev algebras, implicit-function openness, closedness, continuity method) and the cube/torus reflection theory |
| `FieldTheory/Gravity` | 82 | Coordinate curvature, Christoffel and Bianchi jets, ADM decomposition, the harmonic-gauge Einstein writer on periodic grids with its continuum limit, Gowdy and de Sitter/flat vacuum solutions, Palatini–Holst variations, the actual-jet Einstein–SM system, contracted Bianchi identity and subsidiary constraint energies |
| `FieldTheory/GaugeTheory` | 42 | Lattice Coulomb gauge, Wilson transport and holonomy gauge covariance, literal-link compactness, determinant flux and Hodge normalization, the Standard-Model gauge structure used by Uhlenbeck's theorem |
| `FieldTheory/LorentzianGeometry` | 37 | Lorentz-group and bivector classification, Clifford rounding and signature facts, discrete Cartan calculus, covariant consistency |
| `FieldTheory/GaugeGroups` | 17 | The gauge group S(U(3)×U(2)) and its ℤ₆ quotient, anomaly-forced hypercharges, Yukawa descent blocks, the Minkowski coframe metric and the Einstein–Standard-Model coefficient bank |
| **`Lattice/`** | **96** | *Discrete analysis on grids and lattices* |
| `Lattice/DiscreteAnalysis` | 76 | Lattice Fourier symbols, uniform periodic-grid Sobolev, Poincaré and Loomis–Whitney inequalities, grid Hodge theory, plaquette expansions and finite-difference remainders, analysis on the A3 (FCC) lattice, the harmonic-writer scheme |
| `Lattice/Variational` | 20 | Discrete Euler consistency, finite variation complexes and Hodge projections, the analytic Legendre transform, Gibbs action gaps, Sobolev reader criteria |
| **`Stochastics/`** | **119** | *Probability, statistical mechanics, quantum information and systems theory* |
| `Stochastics/QuantumInformation` | 38 | Quantum relative entropy with Lieb, Petz and BKM, Lindblad generators, unital completely positive maps and channel monoids, purification, resets, quantum combs, Born weights |
| `Stochastics/SystemsTheory` | 33 | Descriptor/Weierstrass pencils, Hankel, Kalman and Pontryagin realizations, Moore–Penrose Schur shorts, comb tomography and dilation |
| `Stochastics/StatMech` | 27 | Curie–Weiss, Ising with Peierls and Dobrushin, Cramér–Chernoff, Birkhoff, BKM forms, Kullback–Leibler chain rules |
| `Stochastics/Probability` | 11 | Renewal and geometric random sums, calibration, face linearization, incidence zeta functions |
| `Stochastics/MarkovChains` | 10 | Metzler generators, Doob transforms, absorbing classes, affinity cohomology, entropy production |
| **`Core/`** | **101** | *Shared algebra, combinatorics and topology* |
| `Core/Algebra` | 69 | Matrix exponential and logarithm calculus, Pfaffians, free star algebras, completely positive maps and the Kraus/Stinespring layer, Jordan and Clifford algebra, certified weak pencils, canonical reductions |
| `Core/Combinatorics` | 23 | Graph cut–cycle decompositions and exterior ranks, tight frames, K₄ representation theory, finite Boolean circuits |
| `Core/Topology` | 9 | Brouwer and Sperner fixed points, finite inverse systems and their limits |

## What is in `RenewalGeometry`

| Folder | Files | Contents |
|---|---:|---|
| `Continuum` | 122 | Regulator sequences, compactness and reduced-topology certificates, strong packets and the main limit, the native lattice chain (records, sources, budgets, shadows, Wilson screens), the native-closure bridge |
| `Gravity` | 115 | Relational ADM branches, the renewal–Palatini handoff and Einstein certification chain, open-writer law families, exact-action Ward identities and cosine defect spectra |
| `StandardModel` | 99 | The programme's Standard-Model synthesis: internal assemblies, central descent selectors, generations and Yukawa descent, native generations |
| `Predictive` | 88 | Reconstructing a process from its futures: derived state machines, right congruences, minimal records, readable relations, memory cut-offs and the memory RG semigroup |
| `Action` | 87 | Finite action reconstruction: the explicit N = 3 phase-compatible action, stationarity and jets, K₄ selectors, determining kernels, native densities and Euler rows |
| `Commutant` | 57 | Commutant duality of the programme: grand interfaces, loaded Howe packets, source ideals, SMST assemblies, incidence duality |
| `Spectralization` | 48 | The finite spectralization functor and its essential image, the A3 twelve-root periodic graph chain, saturated Dirac generators, SMST graph regulators |
| `Operational` | 31 | Operational process systems, the UCP/channel bridge, sharp purification, Petz retrodiction and KMS duality, record algebras |
| `Renewal` | 30 | Renewal memories, the predictive quotient monoid and its length, predictive posets, Bowen-pressure calibration |
| `Dimension` | 23 | Selection of `3+1` dimensions: access efficiency, even rank, isotropy, power counting, cut–cycle dimension |
| `Lorentz` | 23 | Lorentzian emergence: Krein–Clifford signature selection, marked-torus classification, interference closure, pressure gauge |
| `DiscreteAnalysis` | 13 | Root-parity connectors, coframe renewal packets, positive-Higgs envelopes |
| `GaugeTheory` | 11 | Lattice Yang–Mills records of the programme: slab gaps, Wilson separators, Creutz ratios, regulated mass criteria, the gauge-robust reader |
| `StatMech` | 10 | Accepted-action information geometry and the programme's Gibbs selections |
| `Measurement` | 7 | Pointer records, Lüders/Kraus decompositions, apparent collapse, redundancy and objectivity |
| `Miscellany` | 6 | Batches of assorted finite records and conditional panels that span several of the topics above |
| `Certificates`, `Krein`, `Analysis`, `OperatorLimits`, `Numerics`, `Algebra`, `Arithmetic`, `Complexity`, `MarkovChains` | 27 | Small folders: The certificate and provenance calculus: typed compilation, executable statuses, cofinal failure witnesses; positive Krein distinctions and signed covers; threshold banks and Newton certificates; grand universal and marked renewal limits; numerical certificates; finite-dimensional algebra needing renewal inputs; arithmetic records; the P vs NP bridge; discrete clocks |

## License

Apache 2.0, following Mathlib.
