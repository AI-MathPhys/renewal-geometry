# Faithfulness audit — 2026-07-21

Full audit of every tracked record against the **current** manuscript text: does the anchored
Lean correspond exactly to the statement as written, with no extra assumptions and no
tautological content? Ten independent audit passes: five over `manuscripts/lorentzian_emergence/lorentzian_emergence.tex`
(210 records, `manuscripts/lorentzian_emergence/statements.json`), four over `manuscripts/renewal_emergence/renewal_emergence.tex`
(123 records, `manuscripts/renewal_emergence/statements.json`), plus one adversarial pass over the scoped-interface
structures and key theorems.

Pre-check: the 2026-07-21 manuscript_2 update (1242 insertions) changed **no tracked
statement bodies** — all labeled environments are textually identical to the previous
git version; new material is prose/proofs/remarks. Mapping remains valid.

## Verdict key

- **EXACT** — Lean statement expresses the manuscript claim in its stated generality.
- **FAITHFUL-SCOPED** — a gap exists (specialization, hypothesis-form literature input,
  informal packaging) and the record note discloses it accurately.
- **UNDISCLOSED-GAP** — Lean is weaker/narrower than the manuscript and the note does not
  say so (or says the opposite).
- **TAUTOLOGY** — the anchored "proved" content is definitional repackaging, an arithmetic
  identity, or a hypothesis that restates the conclusion.
- **MISMATCH** — the anchors formalize a different statement than the current text.

## Totals

| | EXACT | FAITHFUL-SCOPED | UNDISCLOSED-GAP | TAUTOLOGY | MISMATCH |
|---|---|---|---|---|---|
| manuscript 1 (210) | 31 | 154 | 22 | 3 | 0 |
| manuscript 2 (123) | 45 | 62 | 10 | 2 | 4 |
| **total (333)** | **76** | **216** | **32** | **5** | **4** |

**ADDED-ASSUMPTION: 0 on both manuscripts** — no record was found where the Lean carries a
content-changing hypothesis absent from the text (typeclass plumbing only).

## Systemic findings

1. **The "matches on review of the new text" notes are the main defect source.** All four
   MISMATCH records and several UNDISCLOSED-GAPs stem from the manuscript_2 remapping
   session: records whose statements were *rewritten* in the text were re-registered with a
   note asserting the new text matches the old formalization, when it does not
   (`thm:universal-quotient`, `prop:branchwise-petz-reference-renewal`,
   `thm:deck-observability`, `thm:affinity-conductance`, `cor:minimal-signed-enrichment`,
   `thm:pressure-path-clock`, `thm:affine-clock`, `prop:cancellation`).
2. **Assembly-layer "proved" statuses overstate.** The analytic/combinatorial cores are real
   (see "Confirmed sound" below), but several bundle records route a manuscript clause
   through a vacuous or fragmentary anchor (e.g. `mixture_zero` = `(m + −m)/2 = 0` by
   `ring`; `phase_pair_of_uniform_bound` = Bolzano–Weierstrass on real numbers, not Gibbs
   states; `coherence_dim_two_selects_complex` = case-split on a definitional table).
3. **Discrete/algebraic surrogates anchoring continuum claims** (manuscript-1 operator
   chapters): discrete propagation lemmas anchor continuum domain-of-dependence theorems,
   symbol-level identities anchor operator-convergence theorems. Mostly disclosed, but the
   notes on ~10 records overstate which clause the surrogate covers.

## HIGH-severity findings (12)

### Manuscript 2

- **`prop:reversible-realisation-sharp-purification`** — TAUTOLOGY (confirmed by two
  independent passes). `ReducedReversibleRealisation` is field-for-field
  `SharpPurification` (`unique_discard` ≡ `causal`, `dilate` ≡ SP4 with `Purifies`
  unfolded, `sharp` = `pure_state ∧ pure_reverse`); `SharpPurification.ofRealisation` is
  record reshuffling. The manuscript's real step (transformation-level reversible dilation
  with minimal environments ⇒ state purification, via Chiribella–D'Ariano–Perinotti) lives
  on paper only. Status "proved" not earned → should be `statement_encoded`.
- **`def:sharp-purification`** — UNDISCLOSED encoding defect. `causal : ∀ e, e = discard`
  quantifies over **all** effects (no determinism marker in `OpTheory`), which collapses
  SP3 and makes the package unsatisfiable by finite quantum theory as encoded. Needs a
  `deterministic` predicate on effects.
- **`thm:universal-quotient`** — MISMATCH. Current text: symmetric-monoidal universal
  property of the process quotient `Q_pred`. Anchors: the rooted-history canonical
  realization (the old notes-track theorem, now part of `thm:minimal-predictive-memory`).
- **`thm:operational-ucp`** — TAUTOLOGY. `IsCompletelyOperationallyPositive` is defined
  verbatim as `IsCompletelyPositive`; the central iff is `Iff.rfl`. The theorem's actual
  content (positivity from state separation, unitality from determinism, converse) is
  unmodeled.
- **`prop:branchwise-petz-reference-renewal`** — MISMATCH. Current text: general CP
  trace-nonincreasing branch with involutivity/composition/iff clauses. Anchors: the old
  rank-one block-reset instrument with a different clause list.
- **`thm:canonical-record-algebra`** — UNDISCLOSED-GAP. `recordAlgebra` is *defined* as the
  class-constant functions, so the boxed identity's content-carrying half (generated-by-
  predictions = class-constant, via the indicator-product argument) is never proved; the
  anchored equalities are near-definitional quotient facts.

### Manuscript 1

- **`cor:sharp-existence`** — UNDISCLOSED-GAP. Note claims "triple exists iff fibres
  uniformly finite — both halves proved", dropping the bounded-Λ_min-increments conjunct of
  the manuscript's iff; the increment half has no Lean counterpart.
- **`thm:classification`** — UNDISCLOSED-GAP. `EnrichmentDatum := G.E → ZMod 2` bakes the
  rank-two/cochain reduction into the definition, making `classificationEquiv`
  essentially definitional; the manuscript step justifying the encoding is not derived.
  (The counting half, `card_H1_of_connected`, is genuine.)
- **`lem:complexity-gap`** — UNDISCLOSED tautological anchor. Sole anchor
  `revisionCost_step` proves `2^(m+3) = 4·2^(m+1)`; the lemma's content
  (`A_rev ≅ M_{2^{(m+1)/2}}(ℂ) ≅ Cl_{m+1}(ℂ)`) is not formalized; note empty.
- **`lem:realized-reversible-subgroup`** — TAUTOLOGY (disclosed in note, but status
  "proved"). The dynamical closure facts are structure fields; the "lemma" bundles them
  into an `AddSubgroup`.
- **`thm:rg-no-dimension-selection`** / **`thm:minimal-field`** — TAUTOLOGY (mitigated:
  notes are honest). Headline anchors are `(d+1) − d = 1` by `ring` and
  `3 ≤ d → d − 2 = 1 → d = 3` by `omega`; the deductive content sits in the hypothesis.

## MEDIUM-severity findings (selected, 20+)

Manuscript 2: `thm:deck-observability` (anchor proves deck-invariant-state cancellation,
not the ω± even-agreement/odd-flip criterion — both easy, absent);
`thm:affinity-conductance` (boxed capacity factorization `q_e = c_e e^{A/2}` + uniqueness
not formalized; anchors prove the H¹×H¹(ℤ/2) gauge classification instead);
`prop:cancellation` (missing: `Φ_sym` KMS-self-adjoint + uniqueness of decomposition —
easy consequences of proved involutivity); `cor:minimal-signed-enrichment` (minimality/
classification clauses have no Lean counterpart; anchors are ambient double-cover
machinery); `thm:temporal-row` (second display — the combined form on `K_full` — absent,
undisclosed); `thm:pressure-path-clock` / `thm:affine-clock` (finite spectral model with
unit depths `ℓ_e ≡ 1` anchors the general-depth path-clock construction);
`thm:operational-diagonalization` / `thm:operational-jordan` (no Lean statement links
`SharpPurification` to the models; normalization + transitivity clauses unencoded;
"order-embedded" claim has no order structure); `def:process-system` (finite generating
family and postprocessing closure unmodeled); `thm:complex-algebra` (no composite formal
statement of `A_pred ≅ ⊕ M_{n_r}(ℂ)`; step (c) anchored by an algebra-free calculus lemma).

Manuscript 1: `thm:ehrhart-order` / `cor:ehrhart-free` (anchors count the degree-shell
simplex `C(R+c,c)`, but the theorem counts order intervals/boxes `(τ+1)^c` — the right
lemma `NCG.card_interval` exists in `NCG/Lorentz/ProductOrder.lean` but is not cited);
`prop:metric-collapse` (anchors are number-theoretic stand-ins detached from the CP
example; covering bound proved for the wrong (one-parameter) set); `prop:fibres-monoid`
(constant-increment half missing, undisclosed); `thm:qmet-qalg` (strictness regimes (i),
(ii) unformalized, undisclosed); `prop:renewal-calibration` (stale AUDIT CORRECTION —
current text does case-split on |E|; residue clause uncovered); `cor:curved-stability`
(note still cites `central_difference_second_order`, disavowed as a tautology by sibling
records' own audit corrections); `thm:full-operator` (JSON inconsistency: note says
`NCG.marked_gap_sq` was removed from the anchors, but it is still listed);
`thm:stability` (six enumerated conclusions incl. finite-dimensional matrix items
unformalized; note names only Kato–Rellich); `thm:metric-reconstruction` /
`cor:symbol-reconstruction` (intertwiner→isometry content unformalized beyond
polarisation); `thm:macroscopic-domain` / `lem:constant-dirac-kernel` /
`thm:constant-inner-characterization` (discrete surrogates vs continuum claims, notes
overstate); marked-torus records (displayed convergence/classification clauses live
entirely in the noted step); `thm:full-isotropy-interference` (only the easy d = 3
existence witness proved); `prop:symmetric-alternating-independence` (complementarity
proved, inequivalence + Lichnerowicz clause not); `cor:canonical-hyperbolic-core`
(`rank2Form` free-standing, never identified with the restricted commutator form);
`thm:intrinsic-graded-clifford-datum` (clauses (a), (b), (e) absent, not named as missing);
`prop:branchwise` analogues in chunk-2 LOW list.

## Adversarial pass — confirmed sound

`ContourDatum` + `isingContourDatum` (nontrivially inhabited by the real 2d Ising model;
single scoped hypothesis is the 4n·3^{n−1} count); `peierls_magnetization`;
`circle_dimension_selection` + `two_path_face_complex` + SpinFactor/PauliJordan layer;
`TwoPathFaceDatum`; `RegularPerturbation`; `dissipator_exp_tendsto_stable`;
`pRad_attained_on_component`; `stationary_ae_in_one_closed_recurrent_class` (proves a
slightly *stronger* statement than the text). Caveats: `pRad` is the entry-sum growth rate,
equal to the spectral radius only under `HasDiagWitness` (disclosed, but the ρ-identity is
unformalized); `phase_pair_of_uniform_bound` constructs number sequences, not Gibbs
states — the extremal-state clause remains a scoped input everywhere it is cited.

## Recommended remediation (not yet applied)

1. **Status downgrades** (proved → statement_encoded): `prop:reversible-realisation-sharp-purification`,
   `thm:operational-ucp`, `lem:realized-reversible-subgroup`, `lem:complexity-gap`,
   `thm:universal-quotient`, `prop:branchwise-petz-reference-renewal` (unless re-proved, see 3).
2. **Note corrections** for every UNDISCLOSED-GAP and stale-note record above; remove
   `NCG.marked_gap_sq` from `thm:full-operator`; re-anchor `def:kms-pairing` to `kmsInner`;
   cite `NCG.card_interval` on the Ehrhart pair.
3. **Cheap Lean fixes** (hours, not sessions): general-depth `ℓ_e` in `upstream_affine_clock`;
   ω± even/odd criterion for `thm:deck-observability`; `Φ_sym` self-adjointness + uniqueness
   for `prop:cancellation`; the capacity factorization for `thm:affinity-conductance`;
   general-branch Petz clauses for `prop:branchwise-petz-reference-renewal`;
   unconditional-invertible half of `prop:metric-comparison`; generated-algebra half of
   `thm:canonical-record-algebra`; a `deterministic` marker in `OpTheory`.
4. **Real projects** (flagged, unchanged): planar circuit count; DLR/extremality packaging;
   CP of `e^{tℒ}`; JvNW/BLSS; transversality; continuum operator layers of manuscript 1.
