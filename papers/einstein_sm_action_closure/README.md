# Finite-Action Closure and Classical Einstein–Standard-Model Limits in Renewal Geometry

Source: [`einstein_sm_action_closure.tex`](einstein_sm_action_closure.tex) · PDF: [`einstein_sm_action_closure.pdf`](einstein_sm_action_closure.pdf) · Ledger: [`statements.json`](statements.json)

This file is generated from the ledger by `scripts/render_paper_readmes.py`; edit the ledger, not this file.

## Verification summary

| Status | Count | Meaning |
|---|---:|---|
| Proved | 1 | the statement's content is proved in Lean, sorry-free, standard axioms only (scoped hypotheses disclosed in the note) |
| Statement encoded | 0 | the object/statement is faithfully defined in Lean; no proof content claimed |
| Open, with partial Lean | 12 | a special case, one direction, or a finite model is proved; the note says what is missing |
| Open, no Lean counterpart | 55 | nothing in the library formalizes this statement yet |
| **Total tracked statements** | **68** | every theorem/proposition/lemma/corollary/definition environment of the paper |

Every cited declaration is checked to exist by `scripts/check_statement_coverage.py` and audited for axioms by `scripts/audit_axioms.py` (CI).

## Proved statements (1)

| Label | Env | Title | Lean | Note |
|---|---|---|---|---|
| `lem:screen` | lemma | Common compact screen | [`RenewalGeometry.SMSTChannel.screen_strong_convergence`](../../RenewalGeometry/Grand/SMSTPositiveScreenExact.lean)<br>[`RenewalGeometry.SMSTChannel.strong_convergence_transfer`](../../RenewalGeometry/Grand/SMSTPositiveScreenExact.lean) | screen_strong_convergence proves the first assertion on a complex Hilbert space for N-indexed sequences: bounded Z_n weakly convergent, \|\|S_{h,R} - S_R\|\| -> 0, uniform tail exhaustion, S_R Z -> Z, with compactness of S_R rendered as complete continuity (bounded weakly convergent inputs have strongly convergent images, equivalent for compact operators on Hilbert space) and the norm bound sup \|\|Z_n\|\| < infinity spelled out explicitly (automatic from weak convergence). The whitened clause is strong_convergence_transfer: uniformly bounded, strongly convergent B_n = A_h^{-1/2} applied to the strongly convergent whitened packet gives Y_h -> Y; the Loewner bounds mI <= A_h <= MI enter only through that uniform bound. |

## Open statements with partial Lean support (12)

| Label | Env | Title | Lean | Note |
|---|---|---|---|---|
| `def:finite-interface` | definition | Finite classical Einstein--Standard-Model interface | [`RenewalGeometry.RegulatedSMConfiguration`](../../RenewalGeometry/Grand/ExplicitRegulatedStandardModelActionExact.lean)<br>[`RenewalGeometry.explicitRegulatedStandardModelAction`](../../RenewalGeometry/Grand/ExplicitRegulatedStandardModelActionExact.lean)<br>[`RenewalGeometry.sm_group`](../../RenewalGeometry/Grand/SMGroup.lean) | Partial: RegulatedSMConfiguration/explicitRegulatedStandardModelAction encode a finite link/vertex Standard-Model configuration with the four-term (Euclidean) matter action of (I2)-(I4), and sm_group proves the quotient presentation S(U(3)xU(2)) = (SU(3)xSU(2)xU(1))/Z_6 of eq:gauge-group ; missing: the Lorentzian carrier and coframe variables (I1), the common gravity+matter action with its relative normalization (I4, gravity part), the positive source geometry (I5), and any single structure bundling (I1)-(I5). |
| `prop:renewal-interface` | proposition | Renewal realization of the finite interface | [`RenewalGeometry.finiteStandardModel_sourceNative_emergence`](../../RenewalGeometry/Grand/FiniteStandardModelSourceNativeEmergenceExact.lean) | Partial: the companion finite Standard-Model structural packet (gauge quotient, generation rank, weak doublet, finite Dirac incidence) is assembled as the typed certificate finiteStandardModel_sourceNative_emergence ; missing: a Lean finite-interface structure and a proof that the companion constructions instantiate (I1)-(I5), in particular the Lorentzian carrier and common-action normalization. |
| `prop:source-bound` | proposition | Scaled source control of physical stationarity | [`RenewalGeometry.gt_protected_riesz`](../../RenewalGeometry/Grand/GTProtectedRiesz.lean) | Partial: gt_protected_riesz proves the Gram Cauchy-Schwarz bound <Lu,v>^2 <= <u,Lu><v,Lv> for a range source e = Lu on a real inner-product space, i.e. \|a[w]\| <= \|\|a\|\|_{G^{-1}} \|\|w\|\|_G ; missing: the assembly eps_h(K) <= L_h sqrt(R_h) + e_h with the test-lift bound \|\|v_h(v)\|\|_G <= L_h \|\|v\|\| and the identification error e_h. |
| `thm:prefix-stationarity` | theorem | Alternative finite-prefix stationarity criterion | [`RenewalGeometry.BregmanStationarity.descent_upper`](../../RenewalGeometry/Grand/AcceptedBregmanStationarityExact.lean)<br>[`RenewalGeometry.BregmanStationarity.bregman_floor`](../../RenewalGeometry/Grand/AcceptedBregmanStationarityExact.lean) | Partial: descent_upper proves the Taylor descent inequality f(a+v) <= f(a) + <grad f(a),v> + (Lambda/2)\|\|v\|\|^2 used in eq:prefix-descent1, and bregman_floor the strong-convexity floor (m/2)\|\|v\|\|^2 <= D_Psi used for the potential Psi_h ; missing: the balance residual b_j, the telescoped prefix average eq:prefix-average with the h^{-2} Hessian-scale constants, and the selected-slope conclusion eq:prefix-selected (the legacy file instead treats a stationary law of an accepted kernel). |
| `prop:orlicz` | proposition | A local quartic compactness certificate | [`RenewalGeometry.GaussianKernelVitali.integral_norm_sub_tendsto_zero`](../../RenewalGeometry/Grand/GaussianKernelVitaliExact.lean) | Partial: integral_norm_sub_tendsto_zero proves the Vitali step (uniform integrability + convergence in measure implies L^1 convergence of the norm) on a finite reference cylinder ; missing: the superlinear-Phi (de la Vallee-Poussin) uniform integrability of \|H_h\|^4, Rellich compactness giving convergence in measure, and the L^4(K) conclusion. |
| `lem:products` | lemma | Local product and coefficient continuity | [`RenewalGeometry.StrongInterpolationConvergence.tendsto_diagonal_bilinear`](../../RenewalGeometry/Grand/StrongInterpolationConvergenceExact.lean)<br>[`RenewalGeometry.WeakStrongBilinearPairing.tendsto_of_strong_of_bounded_weak`](../../RenewalGeometry/Grand/WeakStrongBilinearPairingExact.lean) | Partial: continuity of bounded bilinear maps under strong (and strong x bounded-weak) convergence is proved on abstract normed spaces ; missing: the Holder instantiation L^p x L^q -> L^r, the explicit quadratic bound eq:quadratic-product, the algebraic coefficient convergence on the coframe chart, and the spin-connection convergence eq:spin-connection-convergence. |
| `thm:main-limit` | theorem | General subsequential Einstein--Standard-Model variational closure | [`RenewalGeometry.one_sequence_limit`](../../RenewalGeometry/Flagship/EinsteinHandoff.lean)<br>[`RenewalGeometry.einstein_extension`](../../RenewalGeometry/Flagship/EinsteinHandoff.lean)<br>[`RenewalGeometry.ConditionalLocalWeakEinsteinMatterHandoff.conditional_local_weak_Einstein_matter_handoff`](../../RenewalGeometry/Grand/ConditionalLocalWeakEinsteinMatterHandoffExact.lean) | Partial: one_sequence_limit/einstein_extension prove the abstract skeleton (sequence in a compact container, continuous residual bounded by vanishing defects, hence a subsequence converging to a zero-residual point), and conditional_local_weak_Einstein_matter_handoff derives the limiting scalar Euler and 2chi(G+Lambda g)=T identities from assumed sectorwise convergence of finite first variations plus vanishing defects (essentially uniqueness of limits) ; missing: compactness derived from the certificate, first-variation continuity in the strong-packet topology, the source-bound residual estimate eq:main-residual-bound, and the concrete Einstein-Standard-Model field equations. |
| `prop:cofinal-transport` | proposition | Summable cofinal transport | [`RenewalGeometry.TrineCofinalCompleteScreen.positive_outcomes_converge`](../../RenewalGeometry/Grand/TrineCofinalCompleteScreenExact.lean)<br>[`RenewalGeometry.ThreadCutoff.tendsto_of_summable_dist`](../../RenewalGeometry/Grand/ThreadCutoffCompactnessExact.lean)<br>[`RenewalGeometry.cofinal_transport_attribution`](../../RenewalGeometry/Grand/MediumProved00.lean) | Partial: summable adjacent distances give a Cauchy sequence and a limit in a complete normed space (positive_outcomes_converge, tendsto_of_summable_dist), and cofinal_transport_attribution adds uniqueness of the limit in a finite weighted norm ; missing: the componentwise d_K packet, identification of the curvature and covariant-derivative limits, and the two-route direct-comparison clause. |
| `prop:YM-defect` | proposition | Yang--Mills quadratic stress defect | [`RenewalGeometry.StrongInterpolationConvergence.tendsto_diagonal_bilinear`](../../RenewalGeometry/Grand/StrongInterpolationConvergenceExact.lean) | Partial: only the final clause (strong L^2 curvature convergence passes the quadratic stress through a bounded bilinear diagonal) has an abstract counterpart ; missing: the tensor-valued weak-star Radon defect measure S_YM and its extraction (Grand/NavierStokesDissipationDefectMeasureExact.lean handles only scalar positive measures). |
| `prop:homogeneous` | proposition | A nonvacuum Einstein--Higgs comparison family | [`RenewalGeometry.curved_einstein_00`](../../RenewalGeometry/Gravity/CurvedFLRW.lean) | Partial: curved_einstein_00 computes the FLRW Einstein component G_00 = 3((adot/a)^2 + k/a^2), the left side of the Friedmann constraint eq:Friedmann-initial at k=0 ; missing: the Einstein-Higgs ODE system eq:homogeneous-ODE, local existence with a>0, constraint propagation, and verification of the remaining Einstein/Higgs/gauge equations. |
| `prop:weak-palatini` | proposition | Weak-curvature Palatini passage | [`RenewalGeometry.FiniteMeasureL2L6Interpolation.lintegral_rpow_interpolate_two_six`](../../RenewalGeometry/Grand/FiniteMeasureL2L6InterpolationExact.lean)<br>[`RenewalGeometry.FiniteMeasureL2L6Interpolation.palatini_eLpNorm'_interpolation`](../../RenewalGeometry/Grand/FiniteMeasureL2L6InterpolationExact.lean)<br>[`RenewalGeometry.StrongInterpolationConvergence.tendsto_of_norm_interpolation`](../../RenewalGeometry/Grand/StrongInterpolationConvergenceExact.lean)<br>[`RenewalGeometry.PalatiniWeakStrongLimit.curvature_pairing_tendsto_of_coframe_interpolation`](../../RenewalGeometry/Grand/PalatiniWeakStrongLimitExact.lean)<br>[`RenewalGeometry.PalatiniWeakStrongLimit.palatini_and_holst_pairings_tendsto`](../../RenewalGeometry/Grand/PalatiniWeakStrongLimitExact.lean)<br>[`RenewalGeometry.PalatiniDeterminantVolume.determinantVolume_tendsto_of_coframe_interpolation`](../../RenewalGeometry/Grand/PalatiniDeterminantVolumeExact.lean) | Partial: the L^2-L^6 Holder interpolation to L^q for 2 < q < 6 (with the p > 3/2 exponent arithmetic) is proved concretely at eLpNorm level, and the passage strong coframe -> strong wedge product -> pairing with norm-bounded weakly convergent curvature, plus the four-linear volume-density limit, are proved on abstract normed spaces with the interpolation bound as hypothesis ; missing: the instantiation on L^p(K) fields (Holder boundedness of the wedge L^{2p'} x L^{2p'} -> L^{p'}, weak L^p as weak-space convergence), the coframe-variation clause, and the connection-Euler pairing caveat. |
| `lem:native-plaquette` | lemma | Regularity of the plaquette map | [`RenewalGeometry.CovariantPlaquette.norm_plaquette_sub_secondOrder_le`](../../RenewalGeometry/Grand/CovariantPlaquetteExpansion.lean)<br>[`RenewalGeometry.CovariantPlaquette.plaquette_sub_secondOrder_isBigO_right`](../../RenewalGeometry/Grand/CovariantPlaquetteExpansion.lean) | Partial: for the unshifted case a = b = 0 the four-exponential plaquette equals 1 + h^2 [X,Y] + O(h^3) in a Banach algebra, with an explicit cubic bound under contraction hypotheses ; missing: the shifted arguments a, b, the logarithm quotient Phi(h) = h^{-2} log(...), its analytic extension through h = 0 with Phi(0) = a - b + [X,Y], and uniform bounds on parameter derivatives. |

## Open statements without a Lean counterpart (55)

| Label | Env | Title |
|---|---|---|
| `def:tests` | definition | Physical variation space |
| `def:regulator` | definition | A finite-interface regulator sequence |
| `prop:native-consistency` | proposition | Growing-band consistency of the unchanged finite action |
| `thm:native-source` | theorem | Leakage-tolerant physical forcing estimate |
| `thm:native-closure` | theorem | Quantitative finite-action stability and Einstein--Standard-Model closure |
| `cor:native-rate` | corollary | An explicit cofinal rate |
| `thm:source-selection` | theorem | Same-record selection from the actual signed action drift |
| `prop:native-reader` | proposition | Exact native-energy to physical-tail certificate |
| `cor:native-reader-sobolev` | corollary | Sobolev positive-form reader criterion |
| `thm:native-selected-closure` | theorem | Same-source selected finite-action Einstein--Standard-Model closure |
| `cor:selected-polynomial` | corollary | An explicit polynomial selected-source regime |
| `cor:gauge-robust-reader` | corollary | Gauge-robust weak-sector reader entrance |
| `cor:prefix-table` | corollary | Finite-table certification for the prefix-balance entrance |
| `cor:generated-nonempty` | corollary | Nonemptiness of the controlled finite class |
| `prop:time-compactness` | proposition | From spatial screens to spacetime compactness |
| `prop:sobolev-bosonic` | proposition | A-priori Sobolev bounds imply bosonic strong compactness |
| `prop:dirac-stability` | proposition | Lorentzian Dirac stability produces spinor $H^1$ compactness |
| `def:compactness-certificate` | definition | Classical compactness certificate |
| `def:strong-packet` | definition | Classical strong packet |
| `thm:certificate-packet` | theorem | Finite certificates produce the classical strong packet |
| `prop:variation-continuity` | proposition | First-variation continuity from primitive fields |
| `cor:cofinal-unique` | corollary | Cofinal uniqueness and route independence |
| `thm:regular-branch` | theorem | Regularity criterion for variational closure |
| `prop:covariant-higgs-endpoint` | proposition | Covariant-gradient compactness closes the Higgs endpoint |
| `prop:weak-fermion` | proposition | Weak-$H^1$ continuity of the complete fermionic first variation |
| `def:reduced-certificate` | definition | Reduced compactness certificate |
| `thm:reduced-closure` | theorem | Reduced-certificate Einstein--Standard-Model closure |
| `cor:renewal-realization` | corollary | Renewal Geometry realization |
| `cor:exact-critical` | corollary | Exact finite critical branch |
| `cor:stress-topology` | corollary | Distributional and negative-Sobolev stress convergence |
| `cor:random-realization` | corollary | A realized random branch |
| `lem:critical-cubic` | lemma | Cubic Euler terms and quartic concentration |
| `thm:higgs-defect` | theorem | Critical Higgs stress-defect identity |
| `thm:joint-defect` | theorem | Joint matter-defect Einstein limit |
| `prop:monotonicity` | proposition | A sufficient Euclidean defect-removal mechanism |
| `thm:hyperbolic` | theorem | Common-slab metric stability |
| `prop:subsidiary` | proposition | Subsidiary equation and constraint stability |
| `prop:smooth-sampling` | proposition | Smooth sampling is a consistency realization |
| `prop:critical-shadowing` | proposition | Nondegenerate critical-point shadowing |
| `lem:Whitney` | lemma | Commuting reconstruction and positive comparison norm |
| `prop:mesh-consistency` | proposition | Smooth local action consistency |
| `prop:improvement` | proposition | An assembled strong--weak improvement criterion |
| `lem:half-ricci` | lemma | Twisted half-Ricci contraction |
| `prop:spinor-prolongation` | proposition | Residual-sensitive tangential spinor prolongation |
| `prop:actual-jet-writer` | proposition | Block-symmetric actual-jet equation |
| `prop:coupled-bootstrap` | theorem | Coupled actual-jet stability and first-exit closure |
| `thm:generated-dynamics` | theorem | Fully finite approximation branch |
| `prop:generated-initial` | proposition | Constructive constrained initial data |
| `lem:generated-physical-identification` | lemma | Physical identification of the symmetric extension |
| `lem:native-scaling` | lemma | Differential-order scaling |
| `lem:native-tail-transfer` | lemma | Finite-order tail bounds |
| `lem:log-source-upgrade` | lemma | Logarithmic derivative upgrade for a band-limited source |
| `prop:native-rounding` | proposition | A sufficient nodal-accuracy condition |
| `lem:native-firstjet-normal-form` | lemma | Shifted-first-jet normal form of the unchanged local action |
| `lem:native-action-Hessian` | lemma | Uniform upper Hessian scale of the local action |
