# Noncommutative & Renewal Geometry in Lean 4

A [Lean 4](https://lean-lang.org/) / [Mathlib](https://github.com/leanprover-community/mathlib4)
library formalizing **noncommutative geometry** (NCG) in Alain Connes'
spectral-triple formulation together with **renewal spectral geometry** — the
operational framework in which spacetime structure (Krein signature, Clifford
blocks, Lorentzian continuum limits, `3+1` dimension selection) *emerges* from
the predictive structure of renewal processes and completely positive channel
monoids.

Mathlib contains no formalization of noncommutative geometry — no spectral
triples, no Krein spaces, no completely positive map monoids. This library
builds that foundation from first principles and uses it to formalize, and
prove, the theorems of companions research manuscripts [companions research manuscript](# Related manuscripts).

**Verification guarantees.**

- **Sorry-free**: the library contains no `sorry`; `lake build` kernel-checks
  all ~52,000 lines across 194 files.
- **No additional axioms**: every theorem depends only on Lean's three
  standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — the same
  foundation as all of Mathlib. This is verified with `#print axioms` on the
  headline theorems; no `sorryAx`, no `native_decide`, no custom axioms.
- **Pinned toolchain**: the exact Lean and Mathlib versions are pinned in
  [`lean-toolchain`](lean-toolchain) and
  [`lake-manifest.json`](lake-manifest.json), so builds are reproducible.

## What is implemented

| Layer | Contents |
|---|---|
| **CP-map / channel algebra** (`NCG/Algebra`) | Positive and completely positive maps, the unital channel monoid, Schwarz maps, the Kadison–Schwarz inequality, Choi's multiplicative domain, projective defects and 2-cocycles, Clifford/Jordan generation, spin factors, Euclidean Jordan rank-two faces, radical–centre structure, symplectic forms |
| **Renewal structures** (`NCG/Renewal`) | Renewal memories, the predictive quotient monoid and its length, predictive posets, Bowen-pressure calibration, Dirichlet/zeta abscissas, renewal Weyl dichotomy, Ehrhart interval growth, crystal counting, spectral and metric dimensions, graded automata |
| **Graph cohomology & covers** (`NCG/Graph`) | Directed multigraphs, sign cocycles, principal `ℤ/2`-covers with deck actions, `H¹(G, ℤ/2)` and `ℤ/4` cohomology, Betti numbers, record orientation, condensation and decimation |
| **Krein geometry** (`NCG/Krein`) | Fundamental symmetries, Krein forms and the positivity obstruction, the irreducible no-go, signed covers as Krein data, the canonical temporal row, the signed modular Dirac operator, enrichment classification via `H¹(G, ℤ/2)` (with naturality and minimality), amplitude lifts |
| **Spectral triples** (`NCG/SpectralTriple`, `NCG/Operator`) | Spectral triples, diagonal/length operators, clock scaling, fibre dichotomy |
| **Lorentzian emergence** (`NCG/Lorentz`) | Discrete Cartan calculus (Levi–Civita derived, not assumed), Clifford rounding, operator-level and band-limited norm-resolvent continuum limits, curved strong-resolvent limits, frame universality, marked-torus classification, Perron pressure and modular-exponent selection, heat-bath convergence/primitivity, Dobrushin mixing, interference closure and `3+1` selection, polyhedral obstructions, 2d Minkowski emergence |
| **Dimension selection** (`NCG/Dimension`) | Access-efficiency selection of `3+1`, even-rank theorems, isotropy dimension-blindness, engineering power counting |
| **Operational / statistical-mechanics program** (`NCG/Upstream`) | The operational process system and UCP bridge, sharp purification, Petz retrodiction and KMS duality, record algebras and pointer selection, complete positivity of the Lindblad semigroup `e^{tℒ}` (full Euler–Trotter proof), the symmetric monoidal quotient category, Curie–Weiss phases, and the **2d Ising phase-coexistence suite**: Peierls bound with the *proved* planar circuit count `4n·3^{n−1}`, infinite-volume Gibbs states with the DLR property, phase separation `±203/216`, and Dobrushin uniqueness at high temperature |

## Related manuscripts

The library is the proof backend for two companion papers. Each has a
dedicated folder containing the LaTeX source, a machine-checked statement
inventory (`statements.json`) mapping every named statement of the paper to
the Lean identifiers that prove it, and a README with the
full verification summary.

### 1. Renewal Spectral Geometry and the Emergence of Lorentzian Spacetime

**→ [`manuscripts/lorentzian_emergence/`](manuscripts/lorentzian_emergence/)**

From a renewal process and its channel monoid to a predictive
spectral triple; the positivity obstruction forcing a *signed* (Krein) sector
classified by `H¹(G, ℤ/2)`; the canonical signed modular Dirac operator;
operator-level Lorentzian continuum limits (flat, curved, band-limited,
self-averaged); and the selection of `3+1` dimensions.
**210 tracked statements — 193 proved, 17 faithfully encoded definitions,
0 conditional, 0 sorry.**

### 2. From Operational Prediction to Signed Renewal Memory

**→ [`manuscripts/renewal_emergence/`](manuscripts/renewal_emergence/)**

The upstream operational paper: why predictive compression of an operational
process forces renewal memory, complex predictive algebras, retrodictive
(Petz/KMS) structure, signed orientation covers, stable pointer records — and
the statistical-mechanics endgame: torsion-free and torsional stationary
phases genuinely coexist (a full 2d Ising Peierls + DLR + Dobrushin
formalization), so torsion freedom is a *selection principle*, not a theorem.
**123 tracked statements — 93 proved, 30 faithfully encoded definitions,
0 conditional, 0 sorry.**

## Installation

Lean projects are built with **`lake`** (installed automatically with the
Lean toolchain via **`elan`**).

### 1. Install elan (the Lean toolchain manager)

**Windows (PowerShell):**

```powershell
Invoke-WebRequest https://elan.lean-lang.org/elan-init.ps1 -OutFile elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
```

**Linux / macOS:**

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Restart your shell so that `~/.elan/bin` is on your `PATH`. `elan` downloads
the exact Lean version pinned in `lean-toolchain` on first build.

### 2. Clone and build

```bash
git clone https://github.com/AI-MathPhys/renewal-geometry
cd renewal-geometry
lake exe cache get   # prebuilt Mathlib cache (avoids compiling Mathlib)
lake build           # build and kernel-check the whole library
```

A successful `lake build` means every definition and theorem in the library
has been checked by the Lean kernel.

### 3. Editor

Install the **Lean 4 extension** in VS Code and open this folder. Hover any
theorem to see its statement; `Ctrl+Click` jumps to Mathlib definitions.

## Verifying the manuscript coverage

Every named statement environment of each manuscript is tracked and checked:

```bash
python scripts/check_statement_coverage.py           # lorentzian_emergence
python scripts/check_statement_coverage.py --notes   # renewal_emergence
```

The checker fails if a manuscript statement has no status record, if a record
went stale, or if a cited Lean identifier disappears from `NCG/`. Use
`--list proved` (etc.) to enumerate a category. See the per-manuscript
READMEs for the axiom audit and the headline-theorem guide.

## Library structure

```
NCG/
├── Basic.lean          -- library overview
├── Algebra/            -- CP maps, Schwarz/Kadison–Schwarz, Choi, Clifford & Jordan algebra, projective defects
├── Renewal/            -- renewal memories, predictive quotients, pressure calibration, zeta/Weyl, dimensions
├── Graph/              -- multigraphs, sign cocycles, ℤ/2- and ℤ/4-cohomology, signed covers
├── Operator/           -- diagonal/length operators, rigidity, fibre dichotomy
├── Krein/              -- fundamental symmetries, signed Dirac, enrichment classification H¹(G,ℤ/2)
├── SpectralTriple/     -- spectral triples
├── Lorentz/            -- discrete Cartan, continuum limits, pressure selection, 3+1 interference closure
├── Dimension/          -- access-efficiency and even-rank dimension selection
└── Upstream/           -- operational program, Lindblad CP, monoidal quotients,
                        --   2d Ising: Peierls + circuit count + DLR + Dobrushin uniqueness
manuscripts/
├── lorentzian_emergence/   -- paper 1: source, statement inventory, verification README
├── renewal_emergence/      -- paper 2: source, statement inventory, verification README
├── ROADMAP.md              -- historical theorem-by-theorem plan
└── faithfulness_audit_2026-07-21.md  -- the adversarial statement-by-statement audit
scripts/
└── check_statement_coverage.py       -- the coverage checker
```

## Design principles

1. **General definitions, concrete models.** Definitions are stated at the
   manuscripts' level of generality (arbitrary channel monoids, arbitrary
   Hilbert spaces, `LinearPMap` Dirac operators). Operator identities are
   proved first in concrete algebraic models where they are exact, then
   upgraded analytically.
2. **Sorry-free, axiom-clean.** No `sorry` anywhere; no axioms beyond
   Mathlib's standard three. Anything not yet formalized is recorded as such
   in the statement inventories — never assumed silently.
3. **Faithfulness over coverage.** An adversarial audit
   ([`manuscripts/faithfulness_audit_2026-07-21.md`](manuscripts/faithfulness_audit_2026-07-21.md))
   compared every record against the manuscript text; every mismatch was
   either re-proved in full or honestly downgraded and disclosed in the
   record's note. Scoped hypotheses (e.g. the upward-escape hypothesis of the
   circuit count, satisfied by all boxes) are stated in the theorem and in
   the record note, never hidden.
4. **Mathlib conventions.** Naming, style, and universe polymorphism follow
   Mathlib so that mature parts (e.g. the symmetric monoidal quotient
   category, the Banach-algebra exponential remainder bound) can be
   upstreamed.

## License

Apache 2.0, following Mathlib.
