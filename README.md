# Renewal Geometry in Lean 4

A [Lean 4](https://lean-lang.org/) / [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of **Renewal Geometry**, the programme in which spacetime,
spectral (noncommutative) geometry and Standard-Model internal structure are
reconstructed as effective descriptions of a common finite predictive
structure, together with the generic **noncommutative-geometry** machinery
that Mathlib does not yet contain.

The repository is the proof backend of four companion papers (see
[Papers](#papers)). Every named statement of every paper is tracked in a
machine-checked ledger that says exactly what is proved, what is merely
encoded, and what is still open.

## Two libraries

| Library | Role | Size |
|---|---|---|
| **`NCG`** | Generic noncommutative geometry, stated with no reference to renewal processes: completely positive maps and channel monoids, Schwarz/Choi theory, Clifford and Jordan algebra, spectral triples, Krein spaces and signed sectors classified by `H¹(G, ℤ/2)`, graph cohomology and covers, and a complete Perron–Frobenius theorem. Candidate material for Mathlib. | 56 files, ~11k lines |
| **`RenewalGeometry`** | The programme itself, built on `NCG`: renewal memories and predictive quotients, the operational/statistical-mechanics upstream layer, Lorentzian emergence and dimension selection, and the finite spectralization, commutant-duality, action-reconstruction and Einstein-regulator results cited by the papers. | 1767 files, ~675k lines |

`NCG` never imports `RenewalGeometry`; this is enforced by
[`scripts/check_layering.py`](scripts/check_layering.py) in CI.

### Verification guarantees

- **Sorry-free.** `lake build` kernel-checks all 1823 files; there is no `sorry`.
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
  hypothesis is spelled out in the record's note. Partial results (a special
  case, one direction, a finite model) stay *open* and say what is missing.

## What is in `NCG`

| Folder | Contents |
|---|---|
| `NCG/Algebra` | Positive and completely positive maps, the unital channel monoid, Schwarz maps, Choi's multiplicative domain, projective defects and 2-cocycles, Clifford/Jordan generation, spin factors, Euclidean Jordan rank-two faces, radical–centre structure, symplectic forms |
| `NCG/SpectralTriple`, `NCG/Operator` | Spectral triples `(𝒜, ℋ, D)`, diagonal/length operators, clock scaling, fibre dichotomy |
| `NCG/Krein` | Fundamental symmetries, Krein forms and the positivity obstruction, the irreducible no-go, signed covers as Krein data, the canonical temporal row, the signed modular Dirac operator, enrichment classification via `H¹(G, ℤ/2)`, amplitude lifts |
| `NCG/Graph` | Directed multigraphs, sign cocycles, principal `ℤ/2`-covers with deck actions, `H¹(G, ℤ/2)` and `ℤ/4` cohomology, Betti numbers, record orientation, condensation and decimation |
| `NCG/PerronFrobenius` | The Perron–Frobenius theorem for irreducible nonnegative matrices, stated in the `Matrix` namespace against Mathlib's `Matrix.IsIrreducible` (see below) |

### Highlight: a Mathlib-ready Perron–Frobenius theorem

Mathlib defines irreducible nonnegative matrices but has no Perron–Frobenius
theorem. `NCG` proves the full package over an arbitrary finite index type:

- **Existence & positivity**
  ([`PerronExistence.lean`](NCG/PerronFrobenius/PerronExistence.lean)): every
  irreducible nonnegative real matrix has a strictly positive eigenvalue with
  an entrywise positive right (and left) eigenvector
  (`Matrix.IsIrreducible.exists_pos_eigenvector`), by the Collatz–Wielandt
  variational argument. Key stepping stone: `1 + A` is primitive.
- **Uniqueness & simplicity**: the Perron eigenvalue is the only eigenvalue
  with a positive eigenvector and its eigenspace is one-dimensional.
- **Spectral-radius characterization**
  ([`PerronPressure.lean`](NCG/PerronFrobenius/PerronPressure.lean)): the
  Perron eigenvalue equals the Gelfand–Fekete growth rate of the matrix
  powers, connecting eigenvector theory to the eigenvector-free pressure
  calculus used by the papers.

## What is in `RenewalGeometry`

Folders are organized by mathematical content. Only files reachable from a
paper ledger are included; the private development tree is larger.

| Folder | Files | Contents |
|---|---:|---|
| `Renewal` | 39 | Renewal memories, the predictive quotient monoid and its length, predictive posets, Bowen-pressure calibration, Dirichlet/zeta abscissas, renewal Weyl dichotomy, Ehrhart growth, spectral and metric dimensions, graded automata, renewal profiles and horizons |
| `Predictive` | 118 | Reconstructing a process from its futures: derived state machines, right congruences, minimal records, readable relational completion, comb and Hankel tomography, source identifiability, word modules, accepted-bit kernels, predictive carriers |
| `Operational` | 60 | Operational process systems, the UCP/channel bridge, sharp purification, Petz retrodiction and KMS duality, record algebras and pointer selection, complete positivity of the Lindblad semigroup, monoidal quotient categories, Uhlmann/Petz/BKM entropy programme |
| `Measurement` | 14 | Pointer records, Born weights, Lüders/Kraus decompositions, apparent collapse, redundancy and objectivity |
| `StatMech` | 35 | The 2d Ising phase-coexistence suite (Peierls with the proved planar circuit count, DLR Gibbs states, Dobrushin uniqueness), Curie–Weiss, large deviations, exponential tilts, SCGF/Legendre duals, Chernoff bounds, KL identities |
| `MarkovChains` | 10 | Finite Markov chains and CTMCs: Metzler generators, Doob transforms, lumpability, rewards, affinity classes, Birkhoff ergodic theorem |
| `Lorentz` | 60 | Lorentzian emergence: discrete Cartan calculus, Clifford rounding, Krein–Clifford signature, marked-torus classification, frame universality, pressure and modular-exponent selection, heat-bath convergence, Dobrushin mixing, interference closure, Lorentz-group invariants |
| `Dimension` | 41 | Selection of `3+1` dimensions: access efficiency, even rank, isotropy, tight frames, power counting, cut–cycle dimension counts |
| `Spectralization` | 104 | From predictive data to spectral geometry: the finite spectralization functor and its essential image, Hodge–Dirac packets and derivations, graph Hodge–Dirac spectral fibres, Connes distance, A₃ lattice metric convergence, Naimark dilation |
| `Commutant` | 114 | Commutant and double-centralizer theory: Wedderburn and factor normal forms, bicommutants, polar edges and holonomy, quiver commutants, typed multiplicity, Howe duality certificates, cofinal/coercive duality, commutant gaps |
| `StandardModel` | 109 | The gauge group `S(U(3)×U(2))`, hypercharge from anomaly cancellation, generations, Yukawa/Majorana sectors, Clifford matter, structural Standard-Model carriers, SM descent, determinant incidence and routers |
| `Action` | 59 | Finite action reconstruction: common action, stationarity and jets, K₄ selectors, determining kernels, reward pressure and Gibbs gaps, score control, exact finite actions, the finite common-action interface |
| `Gravity` | 151 | Relational ADM (lapse, shift, metric), de Sitter and flat vacuum branches, FLRW, the Einstein handoff, Palatini/Holst, curvature reconstruction, Einstein regulators |
| `OperatorLimits` | 170 | Convergence of operators on varying Hilbert spaces: Mosco convergence, strong/norm resolvent limits, collective compactness, compact screens, operator-graph energies, semigroups and Duhamel bounds, spectral convergence and Riesz projections |
| `DiscreteAnalysis` | 82 | Analysis on finite graphs and lattices: finite torus Fourier symbols, covariant symbols, plaquette expansions, coercive Hodge operators, A₃ periodic sampling, graph Poincaré/Weyl/Nash/Sobolev bounds, Loomis–Whitney, flows and cuts |
| `Continuum` | 33 | Continuum function-space analysis: Sobolev compactness, interpolation, Vitali and Gaussian kernel estimates, weak–strong pairings, Volterra/Mittag-Leffler |
| `Certificates` | 15 | The certificate and provenance calculus: typed compilation, provenance compilers, executable statuses, Toeplitz screen obstructions, orientation calibration residuals |
| `GaugeTheory` | 16 | Lattice Yang–Mills records: slab gaps, Wilson separators, Creutz ratios, regulated mass criteria |
| `Algebra`, `Krein` | 55 | Finite-dimensional algebra and Krein-space results that need renewal inputs: Kadison–Schwarz for channels, Choi criteria, Jordan faces, Loewner/PSD calculus, Schur block toolkits, cone positivity, enrichment minimality |
| `Topology`, `Analysis`, `Numerics`, `Complexity`, `Arithmetic` | 92 | Brouwer/Sperner fixed points, singular-value approximation and Gram least squares, rational certificates, finite Boolean circuits, arithmetic loading |
| `Miscellany` | 6 | Batches of assorted finite records and conditional panels that span several of the topics above |

## Papers

Each paper has a folder under [`papers/`](papers/) with the LaTeX source, the
PDF, a `paper.json` manifest, the ledger `statements.json` mapping **every**
theorem/proposition/lemma/corollary/definition environment to its status and
Lean declarations, and a generated README listing every record.

| Paper | Statements | Proved | Encoded | Open (partial Lean) | Open (none) | Easy | Medium | Hard |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| [From Predictive Dynamics to Spectral Geometry](papers/predictive_spectral_geometry/) | 88 | 77 | 11 | 0 | 0 | 0 | 0 | 0 |
| [Renewal Geometry and the Emergence of Lorentzian Spacetime](papers/emergent_spacetime/) | 198 | 157 | 14 | 25 | 2 | 0 | 0 | 27 |
| [Finite-Action Closure and Classical Einstein–Standard-Model Limits](papers/einstein_sm_action_closure/) | 134 | 111 | 11 | 12 | 0 | 0 | 0 | 12 |
| [Spacetime–Gauge Commutant Duality: Finite Rigidity and Cofinal Stability](papers/spacetime_gauge_duality/) | 119 | 107 | 12 | 0 | 0 | 0 | 0 | 0 |
| **Total** | **1823** | **452** | **48** | **37** | **2** | **0** | **0** | **39** |

How to read the table:

- *Proved* means the Lean theorem proves the paper's claim as stated, in the
  generality stated; every scoped hypothesis or rendering choice (a
  finite-dimensional surrogate where the paper's object is a continuum one, a
  Fourier-mode representation where the paper works on the grid, a Sobolev
  order 6 where the paper says 11) is disclosed in the record's note.
  *Encoded* means the object is faithfully defined in Lean, with its defining
  conditions and a constructor from the paper's input data, and no proof
  content is claimed.
- *Open (partial Lean)* records point to Lean that proves a special case, one
  direction or some clauses; the note says exactly what is missing. *Open
  (none)* records have no counterpart in the library yet. Every open record
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

Two papers are completely formalized: the predictive-spectral-geometry paper
and the spacetime–gauge duality paper (every record proved or encoded,
including the main duality for incidences of arbitrary operator-Schmidt rank,
the cofinal derived-kernel duality, the structural Standard-Model synthesis,
the finite Hodge–Dirac reconstruction and its essential images, and the
compact-spin norm-resolvent theorems on genuine Riemannian manifolds in
Mathlib's sense). Of the emergent-spacetime paper, the finite and discrete
content is proved (the ADM and grand-tensor reconstructions, the K₄ and A₃
selectors, the grid harmonic-gauge Einstein writer with its constructive
nonsymmetric 3+1 vacuum limit, the Gowdy regulator, the de Sitter and flat
vacuum regulators, the explicit operational family, the Hodge–temporal and
literal-link compactness theorems, and the renewal-to-Einstein certification
chain: connection stationarity of the Palatini–Holst action, the localized
renewal–Palatini handoff, the vacuum equation from certified variations, the
general certification theorem and the Einstein-or-failed-certificate
alternative). One disclosed amendment enters that chain: the first Bianchi
identity used to make the Holst variation inert does not follow at the
manuscript's L² connection regularity, so the handoff hypotheses carry an
additional uniform spatial L³ bound on the connection interpolants (supplied
by both concrete connection routes of the paper); the field is named
`spatialConnectionL3Bound` and flagged in every affected record. A full
re-audit against the 4 October revision (every proved and encoded record read
against the current statement and the cited Lean) kept 126 records, corrected
24 notes and reopened 9 records, all of which have since been re-proved (the
face-linearization stable branch under a disclosed, necessary continuity
hypothesis). The revision also wrote the explicit N = 3 phase-compatible finite
action into the appendix; it is now encoded literally (links, literal
curvatures, Palatini contraction, compensators, phase derivatives, connection
normal form), with the analytic stationary connection, the Legendre transform
and canonical Hamiltonian, the quadratic jet H₂, the initial-constraint map
and its prepared chart, the Ward orders and the harmonic q₄ = 0 law all proved
for the literal action (standing renderings: χ = 1, Λ = 0, the symmetric
square-root triad, odd N). The 27 hard open records need input the manuscript
still does not give: the certified N = 3 event (no triad fixed, no preparation
equations, no certificate matrix tabulated — the rank-24, (8,8,13) and
response operators are not computable from the text, though the generic rank,
pencil and dichotomy reductions are proved), the graded-chart data (C1)–(C4)
behind the boundary sweeps (the sweep contraction itself is proved), the c_H
row identification of the slow branch (three unwritten bookkeeping
identities; a Lean counterexample shows the uniform form of the Ward
hypothesis is false), the continuum consistency budget of the cofinal
preparation, and the same-cylinder Cartan reconstruction. The Einstein–Standard-Model closure paper is now formalized in
its analytic core as well: the reduced variational closure theorem, the
continuity and Lipschitz estimates of the complete first variation, the
compactness certificates and strong-packet limit, the defect-measure
identities and zero-defect characterization, the critical Coulomb/Kato
estimates, the whole native lattice chain (Coulomb normalization for
S(U(3)×U(2)), Wilson compactness, reconstruction identification, all-sector
consistency, the finite Wilson zero-defect closure and its determinant-resolved
form), the common-slab hyperbolic stability, Dirac stability, the actual-jet
writer with its coupled bootstrap, the a-posteriori shadows and the
constrained initial data. Its 12 open records fall into four groups: Uhlenbeck's
small-energy gauge theorem for the structure group S(U(3)×U(2)) (2 records,
isolated as one named proposition from which the rest is derived); the
analytic-germ (Cauchy–Kovalevskaya) existence behind the physical
identification (1); the bridge identifying the native Euler rows with the
field-equation residuals of the bootstrap model, on which the quantitative
closure theorem and its five corollaries rest (6, a general Euler–Lagrange ↔
Einstein-tensor calculus not yet in the library); the readout clauses of the
generated finite dynamics (2); and the gauge-robust reader certificate, whose
causal temporal gauge is not time-periodic although the paper applies a
periodic Fourier reader to it (1, an author query). Every rendering choice
(spatial sections rendered as 𝕋³, compact charts as coordinate boxes,
trivialised bundles) is disclosed in the records' notes.

The infrastructure built for these ledgers is general and absent from Mathlib,
among it: Sobolev spaces on open sets of ℝ^d by weak derivatives with cutoff,
reflection extension on boxes, local Rellich compactness and the critical
Sobolev embedding H¹ ↪ L⁴ in four dimensions; Fourier Sobolev spaces on 𝕋^d
with the C^r, L^p and Rellich embeddings and interpolation; Kolmogorov–Riesz
compactness on the torus and its charts; de la Vallée-Poussin/Vitali strong
convergence; weak-* compactness of bounded signed and tensor-valued measures;
uniform discrete Sobolev, Poincaré and Loomis–Whitney inequalities and Hodge
theory on periodic grids; the derivative of the matrix exponential and
logarithm; symmetric-hyperbolic L² and H^k energy estimates, Kato local
existence by spectral Galerkin with explicit CFL midpoint schemes, quasilinear
slab stability with the shifted energy multiplier; Whitney forms on simplicial
meshes; strip-holomorphic and Gevrey Fourier decay; and, from the earlier
papers, a Courant–Fischer min–max for compact self-adjoint operators; a real
Moore–Penrose inverse with the four Penrose equations; Davis–Kahan and Wedin
perturbation bounds; a pseudo-resolvent theorem producing a self-adjoint
operator from strongly convergent resolvents; transported Mosco convergence
with norm-resolvent and spectral-projection limits; a uniform discrete Sobolev
calculus on the periodic grid (Plancherel, product and commutator bounds,
Moser composition, sampling, Kuhn–Freudenthal interpolation); L^p duality and
weak compactness; a grid Aubin–Lions theorem; a Riemannian chain-metric bridge
identifying the optimal Lipschitz constant with the gradient supremum;
self-adjoint variable-coefficient Dirac operators on the torus built from
their lattice stages; Haar twirls over SU(2); a matrix Kraus/Stinespring layer;
free star algebras; spanning trees for multigraphs; Pfaffians; path-ordered
exponentials with a BCH bound; two-point Hermite interpolation; the
contracted Bianchi identity and harmonic-gauge constraint propagation at jet
level; and the Perron–Frobenius theorem of `NCG`.

## Which machinery do the papers actually use?

Import closure says which files must *compile*; [`LIBRARY_USAGE.md`](LIBRARY_USAGE.md)
(generated by [`scripts/report_usage.py`](scripts/report_usage.py)) asks the
finer question by walking the proof terms of every ledger-cited declaration:

| | Modules |
|---|---:|
| Used by at least one cited declaration | 1155 |
| Never used, but imported by a used module (structurally required) | 354 |
| Never used and imported by nothing used (removable without loss) | 314 |
| **Total** | **1823** |

The removable part is concentrated in the foundation of the *earlier* papers
of the programme rather than the four tracked here: `Lorentz` (51 of 60
modules), `Operational` (29), `Renewal` (25), `Dimension` (22), `StatMech`
(20), `NCG/Algebra` (19 of 24) and `NCG/Krein` (13 of 14). They are kept
deliberately: they are the generic noncommutative-geometry layer (Krein
classification, signed Dirac operators, Perron–Frobenius, the Lindblad and
Ising suites) that earlier stages of the programme were built on, verified to
the same standard, and available for future noncommutative-geometry work; but
nothing in the four current ledgers depends on them. Folders that the four
papers lean on almost entirely are `Commutant`, `StandardModel`,
`Spectralization`, `Gravity`, `Continuum`, `Analysis`, `DiscreteAnalysis` and
`Action`;
`OperatorLimits` is mostly structural (103 of 170 modules are imported but not
used by any cited proof).

## Installation

```bash
git clone https://github.com/AI-MathPhys/renewal-geometry
cd renewal-geometry
lake exe cache get   # prebuilt Mathlib oleans
lake build           # kernel-checks NCG and RenewalGeometry
```

`lake` comes with the Lean toolchain manager
[`elan`](https://github.com/leanprover/elan); the pinned Lean version is
downloaded on first build. In VS Code, install the Lean 4 extension and open
this folder.

## Verifying the claims yourself

```bash
python scripts/check_layering.py               # NCG independent of RenewalGeometry; all modules registered
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
NCG/                    -- generic noncommutative geometry (library `NCG`)
├── Algebra/  Graph/  Krein/  Operator/  PerronFrobenius/  SpectralTriple/  Basic.lean
RenewalGeometry/        -- the programme (library `RenewalGeometry`, depends on NCG)
├── Renewal/  Predictive/  Operational/  Measurement/  StatMech/  MarkovChains/
├── Lorentz/  Dimension/  Spectralization/  Commutant/  StandardModel/  Action/  Gravity/
├── OperatorLimits/  DiscreteAnalysis/  Continuum/  Certificates/  GaugeTheory/
├── Algebra/  Krein/  Topology/  Analysis/  Numerics/  Complexity/  Arithmetic/  Miscellany/
papers/
├── predictive_spectral_geometry/   -- .tex, .pdf, paper.json, statements.json, README.md
├── emergent_spacetime/
├── einstein_sm_action_closure/
└── spacetime_gauge_duality/
scripts/
├── check_statement_coverage.py     -- ledger checker (--init, --list, --summary)
├── check_layering.py               -- import-layering and registration check
├── audit_axioms.py                 -- axiom audit of every proved declaration
└── render_paper_readmes.py         -- per-paper README generator
```

## Design principles

1. **A generic core.** Anything that makes sense without renewal processes
   lives in `NCG`, follows Mathlib naming and universe conventions, and is
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

## License

Apache 2.0, following Mathlib.
