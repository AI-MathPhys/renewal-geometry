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
| **`NCG`** | Generic noncommutative geometry, stated with no reference to renewal processes: completely positive maps and channel monoids, Schwarz/Choi theory, Clifford and Jordan algebra, spectral triples, Krein spaces and signed sectors classified by `H¹(G, ℤ/2)`, graph cohomology and covers, and a complete Perron–Frobenius theorem. Candidate material for Mathlib. | 55 files, ~10k lines |
| **`RenewalGeometry`** | The programme itself, built on `NCG`: renewal memories and predictive quotients, the operational/statistical-mechanics upstream layer, Lorentzian emergence and dimension selection, and the finite spectralization, commutant-duality, action-reconstruction and Einstein-regulator results cited by the papers. | 1302 files, ~415k lines |

`NCG` never imports `RenewalGeometry`; this is enforced by
[`scripts/check_layering.py`](scripts/check_layering.py) in CI.

### Verification guarantees

- **Sorry-free.** `lake build` kernel-checks all 1357 files; there is no `sorry`.
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
| `Renewal` | 38 | Renewal memories, the predictive quotient monoid and its length, predictive posets, Bowen-pressure calibration, Dirichlet/zeta abscissas, renewal Weyl dichotomy, Ehrhart growth, spectral and metric dimensions, graded automata, renewal profiles and horizons |
| `Predictive` | 111 | Reconstructing a process from its futures: derived state machines, right congruences, minimal records, readable relational completion, comb and Hankel tomography, source identifiability, word modules, accepted-bit kernels, predictive carriers |
| `Operational` | 60 | Operational process systems, the UCP/channel bridge, sharp purification, Petz retrodiction and KMS duality, record algebras and pointer selection, complete positivity of the Lindblad semigroup, monoidal quotient categories, Uhlmann/Petz/BKM entropy programme |
| `Measurement` | 14 | Pointer records, Born weights, Lüders/Kraus decompositions, apparent collapse, redundancy and objectivity |
| `StatMech` | 34 | The 2d Ising phase-coexistence suite (Peierls with the proved planar circuit count, DLR Gibbs states, Dobrushin uniqueness), Curie–Weiss, large deviations, exponential tilts, SCGF/Legendre duals, Chernoff bounds, KL identities |
| `MarkovChains` | 10 | Finite Markov chains and CTMCs: Metzler generators, Doob transforms, lumpability, rewards, affinity classes, Birkhoff ergodic theorem |
| `Lorentz` | 60 | Lorentzian emergence: discrete Cartan calculus, Clifford rounding, Krein–Clifford signature, marked-torus classification, frame universality, pressure and modular-exponent selection, heat-bath convergence, Dobrushin mixing, interference closure, Lorentz-group invariants |
| `Dimension` | 39 | Selection of `3+1` dimensions: access efficiency, even rank, isotropy, tight frames, power counting, cut–cycle dimension counts |
| `Spectralization` | 89 | From predictive data to spectral geometry: the finite spectralization functor and its essential image, Hodge–Dirac packets and derivations, graph Hodge–Dirac spectral fibres, Connes distance, A₃ lattice metric convergence, Naimark dilation |
| `Commutant` | 106 | Commutant and double-centralizer theory: Wedderburn and factor normal forms, bicommutants, polar edges and holonomy, quiver commutants, typed multiplicity, Howe duality certificates, cofinal/coercive duality, commutant gaps |
| `StandardModel` | 103 | The gauge group `S(U(3)×U(2))`, hypercharge from anomaly cancellation, generations, Yukawa/Majorana sectors, Clifford matter, structural Standard-Model carriers, SM descent, determinant incidence and routers |
| `Action` | 55 | Finite action reconstruction: common action, stationarity and jets, K₄ selectors, determining kernels, reward pressure and Gibbs gaps, score control, exact finite actions, the finite common-action interface |
| `Gravity` | 140 | Relational ADM (lapse, shift, metric), de Sitter and flat vacuum branches, FLRW, the Einstein handoff, Palatini/Holst, curvature reconstruction, Einstein regulators |
| `OperatorLimits` | 157 | Convergence of operators on varying Hilbert spaces: Mosco convergence, strong/norm resolvent limits, collective compactness, compact screens, operator-graph energies, semigroups and Duhamel bounds, spectral convergence and Riesz projections |
| `DiscreteAnalysis` | 77 | Analysis on finite graphs and lattices: finite torus Fourier symbols, covariant symbols, plaquette expansions, coercive Hodge operators, A₃ periodic sampling, graph Poincaré/Weyl/Nash/Sobolev bounds, Loomis–Whitney, flows and cuts |
| `Continuum` | 30 | Continuum function-space analysis: Sobolev compactness, interpolation, Vitali and Gaussian kernel estimates, weak–strong pairings, Volterra/Mittag-Leffler |
| `Certificates` | 15 | The certificate and provenance calculus: typed compilation, provenance compilers, executable statuses, Toeplitz screen obstructions, orientation calibration residuals |
| `GaugeTheory` | 16 | Lattice Yang–Mills records: slab gaps, Wilson separators, Creutz ratios, regulated mass criteria |
| `Algebra`, `Krein` | 55 | Finite-dimensional algebra and Krein-space results that need renewal inputs: Kadison–Schwarz for channels, Choi criteria, Jordan faces, Loewner/PSD calculus, Schur block toolkits, cone positivity, enrichment minimality |
| `Topology`, `Analysis`, `Numerics`, `Complexity`, `Arithmetic` | 87 | Brouwer/Sperner fixed points, singular-value approximation and Gram least squares, rational certificates, finite Boolean circuits, arithmetic loading |
| `Miscellany` | 6 | Batches of assorted finite records and conditional panels that span several of the topics above |

## Papers

Each paper has a folder under [`papers/`](papers/) with the LaTeX source, the
PDF, a `paper.json` manifest, the ledger `statements.json` mapping **every**
theorem/proposition/lemma/corollary/definition environment to its status and
Lean declarations, and a generated README listing every record.

| Paper | Statements | Proved | Encoded | Open (partial Lean) | Open (none) | Easy | Medium | Hard |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| [From Predictive Dynamics to Spectral Geometry](papers/predictive_spectral_geometry/) | 88 | 55 | 9 | 24 | 0 | 5 | 12 | 7 |
| [Renewal Geometry and the Emergence of Lorentzian Spacetime](papers/emergent_spacetime/) | 197 | 114 | 13 | 53 | 17 | 16 | 11 | 43 |
| [Finite-Action Closure and Classical Einstein–Standard-Model Limits](papers/einstein_sm_action_closure/) | 134 | 27 | 4 | 21 | 82 | 3 | 2 | 98 |
| [Spacetime–Gauge Commutant Duality: Finite Rigidity and Cofinal Stability](papers/spacetime_gauge_duality/) | 119 | 92 | 11 | 16 | 0 | 11 | 5 | 0 |
| **Total** | **538** | **288** | **37** | **114** | **99** | **35** | **30** | **148** |

Three of the four manuscripts were revised on 30 September 2026 (new
theorems, refactored statements, relabelled records; the tracked statement
count grew from 369 to 518). Every record whose statement text changed was
re-verified against its cited Lean, and 12 previously proved records were
honestly downgraded because the theorems were strengthened (for instance the
main duality now asserts the commutant identity for arbitrary operator-Schmidt
rank, and the structural Standard-Model theorem gained new hypotheses and
conclusions). Every new record was triaged and, where open, rated.

Before that revision, six proving passes (September 2026) had taken the
ledgers from 75 to 240 proved statements and from 16 to 33 encoded
definitions: the first pass closed every record rated *easy*, three more
worked through the 115 records rated *medium*, and two further passes built
the missing infrastructure for the *hard* records of the duality paper and of
the predictive-spectral-geometry paper. The predictive-spectral-geometry
paper, unchanged in that revision, was then **completely formalized** (57 + 11
records, nothing open). The infrastructure those passes added is reusable and
absent from Mathlib: a Courant–Fischer min–max for compact self-adjoint
operators, rectangular Cauchy–Binet, Lebesgue-null zero sets of polynomials,
the intrinsic Wedderburn form of star-subalgebras of block matrix algebras, a
ghost superalgebra for BRST, lattice holonomy gauge covariance, the
L²(μ; H) completion and Naimark dilation of positive operator-valued measures
with Stieltjes injectivity and weak-* compactness, finite Pontryagin
realizations of rational Hermitian functions with pole–Hankel invariants and
Weierstrass descriptor forms, lattice-torus Plancherel with a variable-coefficient
Gårding estimate, an unbounded self-adjoint resolvent surrogate with
norm-resolvent convergence for compatible stable atlases, and mesh-graph
distance convergence on compact metric spaces. Where the paper's objects are
continuum ones Mathlib lacks (spin manifolds, spinor Sobolev spaces,
Riemannian distance), the record is proved for the disclosed abstract
surrogate that the paper's own proof uses.

The revision left 40 open records rated *easy* (assembly of existing lemmas
for the new wording). A seventh pass (30 September 2026) closed all of them:
32 are now proved, 6 definitions are encoded, and 2 corollaries stay open
(rated *medium*) because their parent theorem is not yet formalized. It added
37 files, among them a per-component anchor for the finite common action, the
S₄-equivariant isometry between W₄ and its twisted exterior square, a
periodic discrete Hodge identity on arbitrary finite grids, a
nonstationary action-gap bound for arbitrary couplings, a variance-sensitive
Thomson transfer bound, a Banach-fixed-point retraction onto the exact
initial constraints, and the translation Kato inequality. That left 54
records rated *medium* (new finite lemmas) and 181 rated *hard*.

An eighth pass (30 September 2026) worked through the 54 *medium* records.
43 are now proved, among them both main theorems of the duality paper: the
commutant identity for incidences of arbitrary operator-Schmidt rank, and the
cofinal derived-kernel duality. Nine were re-rated *hard*. Seven of them are
proved in Lean from the conclusion of an open hard theorem of the same paper
and close by instantiation once that theorem is formalized; two need Sobolev
composition bounds or an unbounded-limit spectral chain. Two stay *medium*.
The pass added 46 files, including a real Moore–Penrose inverse with the
four Penrose equations, unitary implementation of *-isomorphisms between
full matrix algebras, the explicit naturality spectra of the determinant
skeleton, and canonical chiral projectors. It also corrected two records.
One revised statement, the universal property in
`cor:reciprocal-wedderburn`, is false as literally written for algebras that
are not closed under adjoints; the record proves the C*-algebra version the
paper's proof uses and says so. And `prop:protected-kernel-locking`, proved in
an earlier pass, cited gap-convergence theorems whose hypotheses turned out
to be contradictory (a bounded limit with compact graph screens forces a
finite-dimensional carrier, while the theorems also assume an
infinite-dimensional one). The contradiction is now proved in Lean, those
theorems are no longer cited, and the record is open again. For consistency
the same rule was then applied to five records proved in earlier passes,
each of which had one clause resting on an open statement of its paper; they
are open again, with everything else they prove kept as partial Lean.

A hard pass (1 October 2026) then finished the duality paper. Its last open
records are proved in the paper's generality: the structural Standard-Model
synthesis (built on a genuine Haar twirl over SU(2)), the weak-copy census,
Davis–Kahan and Wedin perturbation bounds for the incidence-slice and
certified-support theorems, the compact spectral upgrade and protected kernel
locking with an unbounded limit and a general transported Mosco limit, and the
Schur envelope for arbitrary groups. At that point the spacetime–gauge duality
paper had no open record (107 proved, 12 encoded). The determinant split of
the Einstein–Standard-Model paper was re-rated *hard*: Lean now proves
det(exp X) = exp(tr X), but each of its three parents needs an open analytic
result.

A hard campaign on the emergent-spacetime paper (1 October 2026) built general
machinery and closed 51 of its 93 *hard* records, among them the
constructive nonsymmetric 3+1 vacuum limit (whole-sequence convergence of the
grid harmonic-gauge writer with rates, and G(g) = 0 by constraint propagation). The machinery includes a
uniform discrete Sobolev calculus on the periodic grid (Plancherel, product and
commutator bounds, Moser composition, sampling and interpolation); the grid
harmonic-gauge Einstein writer with its energy inequality, lifespan,
difference estimates, law family, time jets and local jets; the continuum limit
of the grid solutions with rates and uniqueness; L^p duality and weak
compactness; distributional curvature identification; a grid Aubin–Lions
theorem; cubical interface lifting with a proved jump formula; an analytic
implicit function theorem; Lyapunov growth bounds; two-point Hermite
interpolation; path-ordered exponentials with a BCH bound; characteristic
Strang splitting for the Gowdy scheme; and a faithful encoding of the explicit
operational family. About 25 of the remaining records concern the explicit
N = 3 exact finite action, which the paper describes only in words (external
formulas, irrational seed data, untabulated certificate matrices); they cannot
be closed from the paper as written. The campaign also found six places where
the manuscript needs a correction or clarification; each affected record states
the reading it proves.

The 42 emergent-spacetime records still open all need input the manuscript does
not give: 29 concern the explicit N = 3 exact action, 7 the original-action
Hamiltonian behind the initial constraint map, 4 a regularity amendment for the
first Bianchi identity in the Palatini handoff (a uniform spatial L^3 connection
bound, which both concrete routes supply), and 2 the same-cylinder Cartan
reconstruction.

The predictive-spectral-geometry manuscript was revised by the author on
1 October 2026 (88 statements, from 68: 26 new records, 28 reworded, 2
relabelled, 6 removed). Every reworded record was re-verified against its Lean
and nine were downgraded because the new wording claims more (for instance
meshes whose edge lengths may underestimate the metric, normalised Hodge
potentials, the compact inverse-limit fibre, HS-orthonormal commutant
coordinates, and a reconstruction category that keeps no generator germ).
Eight of the new records were matched to existing Lean, mostly the refactored
finite Hodge–Dirac packet and edge-relative modular identities; the other 18
were rated as 13 *easy*, 12 *medium* and 2 *hard*. A ninth pass (2 October
2026) then closed every easy and medium record: the commutant fibre for actual
matrix triples, the three reconstruction classes with their essential images
(strong line via spectral projection sequences, norm line equal to spectral
quasidiagonality, strictness by a Toeplitz triple), the operational
realization and recognition theorems on a new matrix Kraus/Stinespring layer,
the process-history representation on a free star algebra, the compact
inverse-fibre completion (inverse limits commute with compact-group
quotients), the Kuhn–Freudenthal A₃ interpolant with its compactness and
smoothing lemmas, and the normalised Hodge potentials. The paper now stands at
72 proved and 13 encoded, with 3 open records rated *hard*: the global metric
theorem needs the bridge from the library's chain-metric model to genuine
Riemannian manifolds, and the two spin records need a compatible stable atlas
for the flat torus.

A faithfulness audit (2 October 2026) then re-read every one of the 396 proved
or encoded records against the current manuscripts, with the cited Lean open
beside each statement, looking for tautologies, vacuous hypothesis packets,
hidden assumptions of the conclusion, and missing clauses. It moved 71 records
back to *open* (35 *easy*, 30 *medium*, 6 *hard*) and corrected the
renderings described in 29 notes. The recurring defects were: an algebra or set
defined to be the claimed answer instead of proved equal to it; a structure
that stores a theorem's conclusions as fields and is never constructed from
the input data; "exactly when" clauses that hold by definition; a bound with
"some positive constant" where the paper names an eigenvalue; hypotheses
stronger than the paper's named definition with no lemma deriving them; global
bounds where the paper works on a compact chart; a lemma proved for a fixed
small index set; and typeclass combinations that no nontrivial object
satisfies. The audit also found several places where the manuscripts need
correction, recorded in the affected records' notes. Every open record now
carries the audit's plan for closing it.

The remaining open records split into 35 *easy*, 30 *medium* and 148 *hard*, the latter
naming their missing infrastructure (Sobolev compactness, continuum PDE, a
uniform 4D discrete Sobolev inequality, ODE-flow composition,
unbounded-limit spectral convergence, or an open parent theorem). Corollaries
whose Lean proofs take an unproved parent theorem's
conclusion as a hypothesis are kept *open* by policy (a proof of "theorem
implies corollary" is not a proof of the corollary) and close when the parent
is formalized, as several did during the second pass. Every *proved* record
discloses its rendering choices in the note, for instance a finite-dimensional
model where the paper's statement is continuum, or a Fourier-mode
representation where the paper works on the grid.

How to read this table:

- *Proved* means the Lean theorem proves the paper's claim as stated
  (scoped hypotheses disclosed in the record note). *Encoded* means the
  object is faithfully defined in Lean with no proof content claimed.
- *Open (partial Lean)* records point to Lean that proves a special case, one
  direction or a finite model; the note says exactly what is missing. *Open
  (none)* records have no counterpart in the library yet.
- *Easy / Medium / Hard* estimate, for every unproved record, how far the
  existing machinery is from a proof: **easy** is at most a day of assembling
  existing lemmas or writing a direct definition; **medium** is several days
  of new lemmas inside the existing finite/algebraic framework; **hard** needs
  infrastructure that neither this library nor Mathlib has (function-space
  compactness, unbounded operators, continuum PDE) or a reformulation before
  the statement can be stated faithfully. Each record's `plan` field says what
  is missing and which files to build on; the per-paper READMEs list them.
- Coverage is strongest for the finite algebraic content: the finite
  spectralization functor and essential image, the graph and A₃ metric
  results, the commutant-duality and Howe-certificate theorems, the
  structural Standard-Model carrier and hypercharge, the K₄ selectors,
  determining kernels and common-action reconstruction. The analytic
  continuum results (Sobolev compactness, distributional Einstein–Yang–Mills
  limits, open `3+1` writers, law-space robustness) are largely open, and the
  Einstein–Standard-Model closure paper explicitly asserts no machine-checked
  formalization of its analytic theorems.

## Which machinery do the papers actually use?

Import closure says which files must *compile*; [`LIBRARY_USAGE.md`](LIBRARY_USAGE.md)
(generated by [`scripts/report_usage.py`](scripts/report_usage.py)) asks the
finer question by walking the proof terms of every ledger-cited declaration:

| | Modules |
|---|---:|
| Used by at least one cited declaration | 708 |
| Never used, but imported by a used module (structurally required) | 325 |
| Never used and imported by nothing used (removable without loss) | 324 |
| **Total** | **1357** |

The removable part is concentrated in the foundation of the *earlier* papers
of the programme rather than the four tracked here: `Lorentz` (50 of 60
modules), `Operational` (30), `Renewal` (25), `Dimension` (20), `StatMech`
(20), `NCG/Algebra` (19 of 24) and `NCG/Krein` (13 of 14). They are kept
deliberately: they are the generic noncommutative-geometry layer (Krein
classification, signed Dirac operators, Perron–Frobenius, the Lindblad and
Ising suites) that earlier stages of the programme were built on, verified to
the same standard, and available for future noncommutative-geometry work; but
nothing in the four current ledgers depends on them. Folders that the four papers lean on almost entirely are
`Commutant`, `StandardModel`, `Spectralization`, `Gravity`, `DiscreteAnalysis`
and `Action`; `OperatorLimits` is mostly structural (101 of 157 modules are
imported but not used by any cited proof).

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
