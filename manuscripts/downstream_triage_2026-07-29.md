# Downstream triage: GR_emergence, SM_emergence, wavefunction

*2026-07-29 — statement inventory, existing-library coverage, physlib assessment,
and a staged proof plan.*

All three papers now have curated `statements.json` ledgers validated by
`scripts/check_statement_coverage.py` (which was extended with the three
manuscripts, the `wave_function` basename, and their bespoke statement
environments). Every record carries a `TRIAGE` note with a difficulty class.

## 1. Inventory

| manuscript | records | already covered | easy | medium | hard | mathlib-scale | numeric cert. | encode-only | prose records |
|---|---|---|---|---|---|---|---|---|---|
| GR_emergence | 173 | 2 | 33 | 41 | 24 | 34 | 0 | 39 | 0 |
| SM_emergence | 273 | 31 | 63 | 68 | 13 | 1 | 2 | 62 | 33 |
| wavefunction | 17 | 0 | 1 | 3 | 2 | 0 | 0 | 10 | 1 |
| **total** | **463** | **33** | **97** | **112** | **39** | **35** | **2** | **111** | **34** |

Classes:

- **covered** — same content as a statement already proved/encoded in the
  lorentzian_emergence / renewal_emergence / flagship ledgers; Lean
  identifiers reused (status `proved` or `statement_encoded` now).
- **easy** (~0.5–1 day) — elementary algebra, explicit finite computation
  (often `decide`/`norm_num`-certifiable), or short arguments over existing
  NCG/Mathlib infrastructure.
- **medium** (~1–3 days) — self-contained development, no missing theory.
- **hard** (~1–3 weeks) — needs a new in-repo mini-library (like
  `PointwiseErgodic` or `SkolemNoether` were).
- **mathlib-scale** — blocked on theory absent from both Mathlib and physlib;
  encode the statement, treat the proof as a long-term project.
- **numeric-certificate** — exact finite construction whose decimal panel
  must be certified with rational/interval arithmetic (`computer_certified`
  target).
- **encode-only** — definitional/hypothesis/principle items;
  `statement_encoded` targets with no proof obligation.
- **record** — prose ledgers/warnings/computational records/status items.

## 2. What the existing library already proves

The SM paper's entire *upstream* layer (Sections on the predictive quotient,
signed covers, revision phase, Clifford dimension) restates theorems already
formalized for the earlier manuscripts, and the ledger reuses those
identifiers: predictive-unit theorem, positive spectral triple + residue
formula, irreducible positive-sector no-go, principal signed cover,
minimal signed enrichment + rank-two classification, modular magnitude
characterisation, signed modular Dirac, reversible revision theorem,
projective lift + commutator form, primitive revision factor
(M_{2^m} ≅ Cl, via flagship `externalFactorSplit`/`skolem_noether`),
revision twirl, sheet ergodicity, rank–Clifford bridge, 3+1 minimality,
Z₄ lift existence/minimality/conservativity — **31 SM records** in total.
On the GR side, `thm:imported-lorentzian` (the foundational operator-limit
endpoint) is covered by the flagship/curved-resolvent chain, and
`def:renewal-local-detailed-balance` by the renewal-affinity cohomology.

## 3. Physlib assessment

[leanprover-community/physlib](https://github.com/leanprover-community/physlib)
(HepLean → PhysLean lineage, with the QuantumInfo project merged) pins
**Lean v4.32.0 / Mathlib v4.32.0**, while this repo is on 4.33.0-rc1 — so it
cannot be taken as a Lake dependency today without toolchain alignment;
near-term use means *porting/replicating* its proofs (or waiting for its bump).
Its stub culture is explicit (`@[sorryful]`, `informal_definition`), so
presence ≠ proved; the items below were verified as actually proved.

**Genuinely useful overlaps**

- *SM anomaly cancellation* — full ACC framework: SM n-family anomaly
  equations, one-family gravitational anomaly automatic
  (`accGravSatisfied`), SM+RHN and B−L variants. Directly covers
  `corollary:explicit-anomaly-cancellation` and supports the hypercharge
  theorem.
- *Gauge group* — `GaugeGroupI = SU(3)×SU(2)×U(1)` with the ℤ₆ subgroup and
  quotient (matches `thm:gauge-group`).
- *CKM* — phase equivalence, Jarlskog invariants, standard parameterization
  (symbolic layer under `cert:canonical-ckm-main`).
- *Higgs potential* — minima/boundedness (background for the electroweak
  Hessian layer).
- *QuantumInfo* (finite-dim) — density matrices, trace distance, Choi's
  theorem/Kraus, CPTP maps, POVMs, **pinching maps** (=
  `thm:binary-colour-expectation-main`), von Neumann entropy with **strong
  subadditivity fully proved**, sandwiched-Rényi DPI, generalized quantum
  Stein's lemma. This is the missing entropy layer for the GR screen
  area-law cluster and the wavefunction paper's instrument statements.
- *Lorentz kinematics* — Lorentz group/algebra, tensors, causal characters
  and causal diamonds (flat only).

**Explicit gaps (nothing there):** curvature tensors, Levi-Civita connection,
Einstein equations, ADM/energy conditions (its `PseudoRiemannianMetric` stops
at musical isomorphisms; FLRW is a `sorry` type with the Friedmann equation
*defined*, not derived); no Born rule/Gleason/Naimark/Lüders/instruments; no
gauge QFT beyond Wick's theorem; no ergodic/renewal theory; no modular theory.

## 4. The five mathlib-scale theory gaps

All 35 mathlib-scale records reduce to five missing theories, essentially all
in the GR paper:

1. **Semiclassical/pseudodifferential calculus** (Weyl quantization,
   Calderón–Vaillancourt, WKB/van Vleck parametrix): `thm:matrix-wkb`,
   `thm:wkb`, the bare-remainder chain, `thm:proper-time`,
   `thm:causal-propagation`.
2. **Riemannian/Lorentzian curvature** (Riemann/Ricci in usable form, normal
   coordinates, Gray–Vanhecke, Raychaudhuri, space-form rigidity, Wald
   entropy): the Ricci-reconstruction cluster, de Sitter global rigidity,
   `thm:einstein` assembly.
3. **Tomita–Takesaki / Borchers–Wiesbrock modular theory**: the wedge/KMS
   cluster (`thm:quasifree-modular`, `thm:modular-calibration-equivalence`,
   `thm:local-calibration`, `prop:kms`).
4. **Hyperbolic PDE / small-data stability**: `thm:nohair` and horizon
   corollaries.
5. **Heat-kernel coefficients (Seeley–DeWitt)**: `prop:minimal-scalar-heat-kernel`,
   `thm:induced-factorization`, `cor:reduction`; plus the lattice continuum
   limit `thm:gauge-universality-app`.

Everything else in the three papers is provable with the repo's current
toolchain plus bounded new mini-libraries.

## 5. Staged plan

**Phase 0 — encode (~2–3 weeks of mechanical work).** Encode the 111
encode-only definitions/hypotheses as Lean structures (statement_encoded), so
every downstream theorem has a faithful statement to point at. Highest-value
first: the GR admissible-channel/diamond/effective-action definitions, the SM
finite-spectral-triple and Yukawa-slot definitions, the WF record-algebra
definitions.

**Phase 1 — the 97 easy statements (~2–3 months at flagship pace).**
Standouts with outsized payoff:
- GR: `thm:exact-renewal-band` + `prop:model-W2` (the massive band is the
  exact Perron eigenvalue — same Clifford-square pattern as
  `clifford_resolvent_identity`); the dark-energy algebra chain (`thm:lambda`
  → `thm:vacuum-trichotomy` → `thm:closed-source-free-deficiency-nogo` →
  `prop:deficiency-eos-identities` → `thm:comoving-matter-depletion` →
  `prop:local-clock-one-crossing` → `thm:crossing-entropy-floor`);
  `lem:null-reconstruction`; the K₄-screen normalization corollaries.
- SM: the K₄/oriented-edge finite linear algebra (`thm:k4-selection`,
  `thm:signed-k4-spectra-updated`, `thm:unique-antibalanced-updated`,
  `thm:exact-amplitude-carrier`, `thm:family-wide-carrier`, the Z₄ orbit
  enumerations — largely `decide`-certifiable); the anomaly/hypercharge
  arithmetic; the Feshbach/Schur block identities; the electroweak Hessian
  rank theorems (`thm:typed-rank-two-higgs`,
  `cor:one-light-doublet-consolidated`); `thm:binary-colour-expectation-main`
  + `thm:binary-renewal-semigroup-main`.
- WF: `prop:definiteness` (existing pointer/Lüders decls nearly close it).

**Phase 2 — the 112 medium statements (~4–6 months).** Clusters:
- GR diamond-moment tomography (`lem:canonical-diamond-moments` →
  `thm:diamond-linear-response` → `thm:u-tomography` → `thm:one-param`),
  Gallavotti–Cohen symmetry (`thm:renewal-gc-symmetry`, fits the pRad
  machinery), drift cancellation, growth-sign comparison (Gronwall),
  `thm:fractional-one-crossing` (self-contained Laplace monotonicity).
- SM representation layer (S₄ modules, stabilizer splits, transfer
  classification), predictive Dirichlet action + gauge normalisation, the
  flavour chronology theorems (mirror amplitudes, pair selector,
  path-ordered CKM composition), commutant rigidity, product-gauge
  factorization (Duhamel), `thm:linear-pressure-cancellation-nogo`
  (pressure + Birkhoff machinery).
- WF `prop:no-signalling`, `thm:pointer-born`, `prop:objectivity`.

**Phase 3 — the 39 hard items = five new mini-libraries (~6–12 months,
parallelizable).**
1. *Finite-dim quantum entropy* (port/replicate physlib QuantumInfo layer):
   unlocks the GR screen area-law cluster and strip entropy rates.
2. *Caputo/Mittag-Leffler fractional calculus*: unlocks the fractional
   dark-energy relaxation cluster (`prop:deficiency-subordination`,
   `thm:source-free-no-crossing`, `thm:irreversible-crossing-threshold`).
3. *Analytic Perron jet* (analytic perturbation of a simple eigenvalue via
   det + analytic IFT): unlocks `thm:matrix-renewal-dictionary` and the
   cumulant dictionary.
4. *Finite real C\*-algebra classification* (real Artin–Wedderburn):
   unlocks `thm:finite-algebra` and the Krajewski/Yukawa-slot enumeration.
5. *Exact-rational certification harness* for the CKM/PMNS panels and the
   two-loop threshold records (`computer_certified` targets).

**Phase 4 — mathlib-scale (long-term, outside-repo scale).** The five theory
gaps of §4. Recommended order by leverage: curvature tensors in coordinates
(unblocks ~15 GR records), then semiclassical calculus (~10), then modular
theory (~6). These are genuine Mathlib-contribution projects; until then the
records stay `conditional_interface` with encoded statements, exactly like
the pre-flagship operator-analytic layer did.

## 6. Bookkeeping

- Checker: `MANUSCRIPTS`, `TEX_BASENAMES`, `EXTRA_ENVS` extended; all six
  manuscripts pass (`python scripts/check_statement_coverage.py`).
- SM/GR/WF ledgers: every record has `TRIAGE <class>` in its note; covered
  records carry reused, checker-validated Lean identifiers.
- Physlib cannot be a Lake dependency until toolchains align
  (4.32.0 vs 4.33.0-rc1); plan assumes porting, not importing.
