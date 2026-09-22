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
| **`RenewalGeometry`** | The programme itself, built on `NCG`: renewal memories and predictive quotients, the operational/statistical-mechanics upstream layer, Lorentzian emergence and dimension selection, and the finite spectralization, commutant-duality, action-reconstruction and Einstein-regulator results cited by the papers. | 785 files, ~198k lines |

`NCG` never imports `RenewalGeometry`; this is enforced by
[`scripts/check_layering.py`](scripts/check_layering.py) in CI.

### Verification guarantees

- **Sorry-free.** `lake build` kernel-checks all 840 files; there is no `sorry`.
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

| Folder | Contents |
|---|---|
| `Renewal` | Renewal memories, the predictive quotient monoid and its length, predictive posets, Bowen-pressure calibration, Dirichlet/zeta abscissas, renewal Weyl dichotomy, Ehrhart growth, crystal counting, spectral and metric dimensions, graded automata |
| `Upstream` | The operational process system and UCP bridge, sharp purification, Petz retrodiction and KMS duality, record algebras and pointer selection, complete positivity of the Lindblad semigroup, the symmetric monoidal quotient category, Curie–Weiss phases, and the 2d Ising phase-coexistence suite (Peierls with the proved planar circuit count, DLR Gibbs states, Dobrushin uniqueness) |
| `Lorentz`, `Dimension` | Discrete Cartan calculus, Clifford rounding, norm-resolvent and curved strong-resolvent continuum limits, frame universality, marked-torus classification, pressure and modular-exponent selection, heat-bath convergence, Dobrushin mixing, interference closure and `3+1` selection, access-efficiency and even-rank dimension theorems |
| `Algebra`, `Krein` | The parts of the algebra and Krein theory that need renewal inputs (Kadison–Schwarz for channels, Jordan faces of sharp purifications, ordered cones of atomic resets, cone positivity) |
| `Topology`, `Analysis`, `Numerics`, `Complexity`, `Wavefunction` | Brouwer/Sperner fixed points, singular-value approximation, rational certificates, finite Boolean circuits, pointer records and Born weights |
| `Grand`, `Flagship`, `Gravity`, `Matter`, `Arithmetic` | The finite spectralization functor and its essential image, graph Hodge–Dirac spectral fibres, A₃ Connes-distance convergence, commutant/double-centralizer duality, Howe certificates, the structural Standard-Model carrier, hypercharge from anomaly cancellation, K₄ selectors and determining kernels, common-action reconstruction and stationarity, relational ADM and de Sitter branches, Mosco/collective-compactness transport, and the finite common-action interface. Only the files reachable from a paper ledger are included; the private development tree is larger. |

## Papers

Each paper has a folder under [`papers/`](papers/) with the LaTeX source, the
PDF, a `paper.json` manifest, the ledger `statements.json` mapping **every**
theorem/proposition/lemma/corollary/definition environment to its status and
Lean declarations, and a generated README listing every record.

| Paper | Statements | Proved | Encoded | Open (partial Lean) | Open (none) |
|---|---:|---:|---:|---:|---:|
| [From Predictive Dynamics to Spectral Geometry](papers/predictive_spectral_geometry/) | 68 | 10 | 3 | 25 | 30 |
| [Renewal Geometry and the Emergence of Lorentzian Spacetime](papers/emergent_spacetime/) | 140 | 41 | 5 | 30 | 64 |
| [Finite-Action Closure and Classical Einstein–Standard-Model Limits](papers/einstein_sm_action_closure/) | 68 | 1 | 0 | 12 | 55 |
| [Spacetime–Gauge Commutant Duality: Finite Rigidity and Cofinal Stability](papers/spacetime_gauge_duality/) | 93 | 25 | 9 | 27 | 32 |
| **Total** | **369** | **77** | **17** | **94** | **181** |

How to read this table:

- *Proved* means the Lean theorem proves the paper's claim as stated
  (scoped hypotheses disclosed in the record note). *Encoded* means the
  object is faithfully defined in Lean with no proof content claimed.
- *Open (partial Lean)* records point to Lean that proves a special case, one
  direction or a finite model; the note says exactly what is missing. *Open
  (none)* records have no counterpart in the library yet.
- Coverage is strongest for the finite algebraic content: the finite
  spectralization functor and essential image, the graph and A₃ metric
  results, the commutant-duality and Howe-certificate theorems, the
  structural Standard-Model carrier and hypercharge, the K₄ selectors,
  determining kernels and common-action reconstruction. The analytic
  continuum results (Sobolev compactness, distributional Einstein–Yang–Mills
  limits, open `3+1` writers, law-space robustness) are largely open, and the
  Einstein–Standard-Model closure paper explicitly asserts no machine-checked
  formalization of its analytic theorems.

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
├── Renewal/  Upstream/  Lorentz/  Dimension/  Algebra/  Krein/  Topology/  Analysis/
├── Numerics/  Complexity/  Wavefunction/  Grand/  Flagship/  Gravity/  Matter/  Arithmetic/
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
