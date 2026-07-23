# Formalization roadmap

Target: formalize the manuscript *Renewal Spectral Geometry and the Emergence
of Lorentzian Spacetime* (A. Pélissier, `manuscripts/lorentzian_emergence/lorentzian_emergence.tex`, updated
version) on top of the `NCG` library, statement by statement. Manuscript
items are referenced by their LaTeX labels.

Status legend — ✅ proved (sorry-free in the library) · 🏗 definitions in
place, theorem pending · 🔜 planned, needs new infrastructure · 🧱 needs
substantial Mathlib-level analytic development first.

## Phase 0 — foundations (this repository, v0)

| Item | Manuscript | Lean | Status |
|---|---|---|---|
| Renewal memory | Def. `def:renewal-memory` | `NCG.RenewalMemory`, `NCG.CPRenewalMemory` | ✅ (CP maps via quadratic-form matrix positivity) |
| Accumulated channel `Φ_w` | Def. `def:renewal-memory` | `NCG.RenewalMemory.acc : FreeMonoid E →* M` | ✅ |
| Predictive equivalence + quotient `𝒲_CP` | Def. `def:predictive-quotient` | `predCon`, `PredictiveQuotient` (a monoid ≃* channel monoid) | ✅ |
| Shift congruence | Lem. `lem:shift-congruence` | `shift_congruence`, `shift` | ✅ |
| Quotient length `Λ_min` | Def. `def:predictive-quotient` | `quotLength` + basic lemmas | ✅ |
| Divisibility order, predictive poset | Def. `def:predictive-order`, Lem. `lem:poset` | `DivisibilityOrder`, `PredictivePoset` | ✅ |
| Sign cocycles, gauge, holonomy | Def. `def:sign-cocycle` | `gaugeAct`, `Walk.holonomy`, `holonomy_gauge_loop` | ✅ |
| Coboundary ⟺ trivial holonomy | Thm. `thm:cover` (triviality criterion) | `holonomy_eq_zero_of_isCoboundary`, `isCoboundary_of_holonomy_eq_zero` | ✅ |
| Signed cover, deck, monodromy | Constr. `constr:signed-cover`, Thm. `thm:cover` | `signedCover`, `deck`, `liftWalk`, `trivializeHom` | ✅ |
| Fundamental symmetry, Krein form | Def. `def:J-eps` | `IsFundamentalSymmetry`, `kreinForm` | ✅ |
| Positivity obstruction | Cor. `cor:positivity-obstruction` (absorbed the former label `cor:cp-positivity-boundary`) | `eq_one_of_krein_nonneg` | ✅ |
| Krein exchange relation | Prop. `prop:krein-datum` | `krein_exchange` (finsupp model) | ✅ |
| Length-Dirac commutator formula | Thm. `thm:triple` (core identity) | `diagOp_comm_shiftOp_single` | ✅ |
| Clock scaling `Ad(e^{βN})S = e^β S` | Lem. `lem:clock-scaling` | `clock_scaling` | ✅ |
| Positive averaging is Riemannian | Prop. `prop:positive-averaging` | `posSemidef_sum_outer` | ✅ |
| Spectral triple (abstract) | §2.1 background | `NCG.SpectralTriple` | 🏗 definition; instances pending |

## Phase 0b — new results of the updated manuscript

| Item | Manuscript | Lean | Status |
|---|---|---|---|
| Predictive channel monoid + unit group | Def. `def:predictive-channel-monoid` | `MonoidHom.mrange R.acc`, `(UCPMap A)ˣ` | ✅ (via Mathlib `Units`) |
| Predictive-unit theorem: sandwich equality | Thm. `thm:predictive-unit` (proof core) | `NCG.schwarz_sandwich_eq`, `NCG.UCPMap.unit_sandwich_eq` | ✅ (order-theoretic core) |
| CP ⟹ star-preserving | Thm. `thm:predictive-unit` (input) | `NCG.IsCompletelyPositive.map_star` | ✅ (via Gram-matrix amplification) |
| CP + unital ⟹ Schwarz inequality (**Kadison–Schwarz**) | Thm. `thm:predictive-unit` (input) | `NCG.IsCompletelyPositive.isSchwarzMap` | ✅ (purely order-algebraic, via `NCG.matrixQF_pair`) |
| Archimedean order property (the analytic input) | — | `NCG.IsArchimedeanStarOrder`, verified for `ℂ` (`isArchimedeanStarOrder_complex`) | ✅ (C⋆-algebra instance = future target) |
| Schwarz equality ⟹ multiplicative domain (**Choi**) | Thm. `thm:predictive-unit` (final step) | `NCG.multiplicative_of_schwarz_eq` | ✅ (complex-polarization proof, over an Archimedean order) |
| **Predictive-unit theorem, assembled** | Thm. `thm:predictive-unit` | `NCG.UCPMap.unit_map_star`, `NCG.UCPMap.unit_map_mul` | ✅ (units of `UCPMap A` are `*`-homomorphisms) |
| Irreducible positive-sector no-go | Ass. `ass:irreducible-positive-sector`, Thm. `thm:irreducible-positive-no-go` | `NCG.IsFundamentalSymmetry.eq_one_or_neg_one_of_mem_centralizer` | ✅ |
| Compatible fundamental symmetries are signed data | Thm. `thm:functorial-positive-obstruction` | `NCG.diagOp_shiftOp_exchange_iff`, `NCG.exchange_iff_step` | ✅ (diagonal model, both directions) |
| Automatic projective lift: central defects (Schur step) | Thm. `thm:spatial-multiplier-scalar-main` | `NCG.projDefect_mem_center_of_ad` | ✅ (group level) |
| Automatic projective lift: 2-cocycle identity | Thm. `thm:spatial-multiplier-scalar-main` | `NCG.projDefect_cocycle` | ✅ |
| Commutator pairing: exchange, defect ratio, biadditivity | Def. `def:revision-operators-main`, Lem. `lem:commutator-pm1` | `NCG.commutator_R_mul`, `NCG.commutator_R_eq_defect_ratio`, `NCG.commutator_R_add_left` | ✅ |
| Polar form is `{±1}`-valued over elementary-2 labels | Lem. `lem:commutator-pm1` | `NCG.commutator_R_sq_eq_one` | ✅ |
| Cycle Krein exchange / canonical temporal row | Lem. `lem:cycle-krein-exchange`, Thm. `thm:canonical-temporal-row` | `NCG.krein_exchange_path`, `NCG.pathShift`, `NCG.holonomy_eq_edge_sign_sum` | ✅ (operator form; sign = gauge-invariant holonomy) |
| Deck-odd normal form `D₀ = J·g` | Lem. `lem:deck-odd-normal-form` | `NCG.deckOdd_eq_sign_mul`, `NCG.deckOdd_diagOp_eq` | ✅ |
| Modular weight forced on orbits (recurrence route) | Thm. `thm:modular-characterisation`, Rem. `rem:recurrence-route` | `NCG.exchange_orbit_pow`, `NCG.modular_weight_on_orbit`, `NCG.exp_weight_orbit` | ✅ (orbit level; connected-component globalization pending `H¹` layer) |
| Access efficiency `η(m) = m/2^m` selection | Def. `def:access-efficiency`, Thm. `thm:access-efficiency-selection`, Rem. `rem:efficiency-honest` (a) | `NCG.accessEfficiency_le_three`, `_eq_three_iff`, `_succ_lt`, `_three_lt_one` | ✅ |
| Primitive complexity gap (×4 per odd step) | Lem. `lem:complexity-gap` | `NCG.revisionCost_step` | ✅ |
| Isotropy is dimension-blind (cross-polytope moment `(1/d)·I`) | Thm. `thm:isotropy-dimension-blind` | `NCG.crossPolytope_second_moment`, `NCG.sum_outer_single` | ✅ |
| **Even-rank theorem**: nondegenerate alternating ⟹ even dimension (any field, incl. `𝔽₂`) | Thm. `thm:minimal-nondegenerate-3plus1` (parity core) | `NCG.even_finrank_of_isAlt_nondegenerate` (hyperbolic-pair induction) | ✅ |
| **No `2+1`**: no nondegenerate alternating form on a 3-dim `𝔽₂`-space | Thm. `thm:minimal-nondegenerate-3plus1` (ii) | `NCG.no_two_plus_one`, `NCG.not_nondegenerate_of_isAlt_of_odd_finrank` | ✅ |
| **Odd spatial rank** `d_Cl = finrank − 1` | Thm. `thm:minimal-nondegenerate-3plus1` (i) | `NCG.odd_spatial_rank_of_isAlt_nondegenerate` | ✅ |
| `H¹(G, ℤ/2)` as a module; removability = vanishing class | Thm. `thm:cover`, Cor. `cor:removability` | `NCG.Multigraph.H1`, `H1.mk_eq_zero_iff` | ✅ |
| Loop holonomy descends to `H¹`; holonomy separates `H¹` on connected graphs | Thm. `thm:cover` (monodromy + injectivity) | `NCG.Multigraph.Walk.holonomy_congr`, `H1.mk_eq_zero_of_holonomy_eq_zero` | ✅ |
| `H¹(bouquet r) ≅ (ℤ/2)^r`, `dim = b₁ = r`, `#sectors = 2^{b₁}` | Cor. `cor:sector-count`, Prop. `prop:primitive-all-odd` (graph side) | `NCG.Multigraph.H1BouquetEquiv`, `finrank_H1_bouquet`, `card_H1_bouquet` | ✅ |
| **General Betti formula** `dim H¹ + \|V\| = \|E\| + 1`, `#sectors = 2^{b₁}` (every finite connected multigraph) | Thm. `thm:cover`, Cor. `cor:sector-count` (full) | `NCG.Multigraph.ker_coboundaryMap`, `finrank_H1_add_card_vertices`, `card_H1_of_connected` | ✅ (rank–nullity; kernel of `δ` = constants) |
| Access functional: AM–GM optimum, odd fixed points `{1,3}`, conditional `3+1` selection | Prop. `prop:additive-access-main`, Lem. `lem:odd-access-fixed-points`, Thm. `thm:conditional-access-3plus1` | `NCG/Dimension/AccessFixedPoint.lean` | ✅ |
| RG eigenvalue `b^{1−k}` and relevance trichotomy | Thm. `thm:rg-eigenvalue`, Cor. `cor:relevance` | `NCG/Dimension/RGEigenvalue.lean` | ✅ (continuum; lattice band error 🔜) |
| Oriented circulation and survival criterion (statistical core) | Def. `def:circulation`, Thm. `thm:survival-criterion` | `NCG/Dimension/Circulation.lean` | ✅ |
| ℤ/4 amplitude phases conservative over the real layer | Def. `def:amplitude-lift`, Cor. `cor:z4-conservative-real-layer` | `NCG.amplitudePhase_sq`, `_sq_eq_of_reduction_eq` | ✅ |
| Symmetric/alternating sector independence | Prop. `prop:symmetric-alternating-independence` | `NCG/Dimension/SectorIndependence.lean` | ✅ |
| Tight-frame bound: minimal isotropic access frame `N_min = 2d` | Lem. `lem:minimal-frame` | `NCG.tight_frame_card_lower_bound` | ✅ |
| Hodge-degree pair `⋀² ≅ ⋀^{d−2}`, degree one iff `d = 3` | Prop. `prop:volume-dual-degree` | `NCG/Dimension/HodgeDegree.lean` | ✅ |
| Spatial nondegeneracy + selection corollaries | Def. `def:spatially-nondegenerate`, Cors. `cor:first-order-symbol-selects-three`, `cor:dimension-final-status`, `cor:concordant-native-selection` | `NCG/Dimension/SelectionCorollaries.lean` | ✅ |
| `q_alg` with finite-shell well-posedness; `q_met` encoded | Def. `def:qalg`, `def:qmet` | `NCG/Renewal/Dimensions.lean` | ✅ / 🏗 |
| Radical–centre dictionary (group core) | Thm. `thm:radical-centre` | `NCG.radical_iff_central`, `radical_iff_pairing_trivial` | ✅ |
| Primitive reduction `H/rad ω` with nondegenerate descended form | Def. `def:primitive-reduction` | `NCG/Dimension/PrimitiveReduction.lean` | ✅ |
| Accessible modular rank: `b_eff` odd, 1-dim spatial radical, `rank = 1+b_eff` | Thm. `thm:accessible-modular-rank`, Def. `def:accessible-revision-block` | `NCG/Dimension/AccessibleRank.lean` | ✅ |
| Reset-difference multipliers: calibration + uniform bound | Def. `def:reset-differences` | `NCG/Lorentz/ResetDifference.lean` | ✅ |
| Displacement semigroupoid + bounded return completion | Def. `def:displacement-semigroupoid`, Thm. `thm:full-rank-returns` (core) | `NCG/Graph/Displacement.lean` | ✅ |
| Regular finite-fibre classes (A)–(D) | Props. `prop:fibres-automata`, `-cp`, `-quotient` (+ `prop:fibres-monoid` ✅) | `NCG/Renewal/FibreClasses.lean` | ✅ (core bounds) |
| Krein–Clifford datum, symbol square, signature dichotomy, Dirac matrices | Def. `def:krein-clifford`, Lem. `lem:symbol-square`, Thm. `thm:signature-krein`, Lem. `lem:alpha-selfadjoint`, Def. `def:dirac-symbol` | `NCG/Lorentz/KreinClifford.lean` | ✅ (algebra layer; Sobolev/operator layer 🧱) |
| Factor-block counting `⊕_ψ M_{2^m}` | Thm. `thm:factor-quotients-corrected` | `NCG/Algebra/FactorBlocks.lean` | ✅ (counting; Wedderburn 🔜) |
| Internal holonomy: dressed commutators, abelian no-go, gauge invariance | Def. `def:coherent-internal-holonomy`, Thms. `thm:nonabelian-holonomy-*`, Lem. `lem:spatial-omega-gauge-invariant` | `NCG/Krein/InternalHolonomy.lean` | ✅ ((iii) rep bound 🔜) |
| Revision cocycle: involutivity, full extension, quadratic refinement, projective law, kernel ⊆ radical, ℤ/4 squares | Thm. `thm:reversible-predictive-revision`, Prop. `prop:full-revision-cocycle-main`, Thms. `thm:revision-quadratic-refinement-main`, `-central-extension-main`, Prop. `prop:projective-revision`, Cor. `cor:revision-z4-square-root` | `NCG/Algebra/RevisionCocycle.lean` | ✅ (extraspecial order count 🔜) |
| Volume element: square identity + temporal anticommutation | Prop. `prop:renewal-volume-element` | `NCG/Lorentz/VolumeElement.lean` | ✅ (SO-invariance 🔜) |
| Discrete Cartan chapter: Koszul uniqueness, iso-metric, plaquette split, channel torsion | Thm. `thm:fundamental` (absorbed the former label `thm:discrete-cartan`), Prop. `prop:iso-metric`, Lem. `lem:plaquette-split`, Thm. `thm:channel-torsion` | `NCG/Lorentz/DiscreteCartan.lean` | ✅ (exact identities; `O(h²)` LC-convergence 🧱) |
| Cancellative commuting growth `q_alg = c` (free case bounds) | Thm. `thm:commuting` | `NCG/Renewal/CommutingGrowth.lean` | ✅ (affine reduction 🔜) |
| Interference closure: Lorentz-pair brackets, dimension dichotomy, `d = 3` Hodge/Clifford identities | Lem. `lem:interference-lorentz-pair`, Thms. `thm:interference-independence`, `-closure-selects-three`, Props. `prop:hodge-interference-closure`, `prop:clifford-internal-interference`, Def. `def:volume-dual-response` | `NCG/Lorentz/InterferenceClosure.lean` | ✅ |
| Chain-counting ≠ incidence zeta (multiplicity witness) | Prop. `prop:incidence-zeta` | `NCG/Renewal/IncidenceZeta.lean` | ✅ (resolvent series 🔜) |
| Signed modular Dirac: Krein-self-adjointness, twisted collapse, multiplier bound | Thm. `thm:signed-dirac`, Lem. `lem:bounded-twisted` | `NCG/Krein/SignedDirac.lean` | ✅ (compact resolvent/summability 🧱) |
| Atomic-diagonal rigidity + finite propagation | Lem. `lem:atom`, Def. `def:finite-propagation` | `NCG/Operator/DiagonalRigidity.lean` | ✅ (ℓ² phase packaging 🔜) |
| Kinematic assembly + regular Lorentzian + rescaling (library results; the assembly statements of earlier drafts) | Def. `def:rescaling` | `NCG/Lorentz/Assembly.lean` | ✅ |
| Net/separation sandwich (`q_met = q_alg` core) | Thm. `thm:metric-predictive-coincidence` | `NCG/Renewal/NetCounting.lean` | ✅ (limsup bookkeeping 🔜) |
| Anisotropy example + grade-blind power counting | Prop. `prop:isotropy-not-derived`, Thm. `thm:rg-no-dimension-selection`, Cor. `cor:dimension-status-rg-audit` | `NCG/Dimension/IsotropyNoGo.lean` | ✅ |
| Revision-sector summary assemblies | Thm. `thm:modular-characterisation` (forward fragment only), `thm:intrinsic-graded-clifford-datum`, Cors. `cor:graded-unconditional-minimality` (partial), `cor:primitive-not-input` | assemblies of proved pillars (see status notes) | ✅ (Wedderburn/SvN steps 🧱) |
| `thm:revision-structure-main`, `cor:full-access-revision-phase`, `cor:universality-clifford-main` (**repaired**) | the projective law is now DERIVED: `revisionFamilyOfDefect` constructs the family from central defects + cocycle identity, with only the scalar-centre input named | `NCG.revisionFamilyOfDefect`, `NCG.revisionFamilyOfDefect_hmul` (`NCG/Algebra/RevisionDerived.lean`) | ✅ (scalar-centre/Wedderburn input 🧱) |
| Taxicab reverse triangle (Mahler superadditivity) | Thm. `thm:taxicab-limit` | `NCG/Lorentz/TaxicabLimit.lean` | ✅ (GH convergence 🧱) |
| Metric-dimension chain: Moran root, `q_met ≤ q_alg`, equality under coding | Thms. `thm:fractal`, `thm:qmet-qalg`, `thm:qmet-qalg-equality` | `NCG/Renewal/Calibration.lean`, `NCG/Renewal/NetCounting.lean` | ✅ (limsup bookkeeping 🔜) |
| Primitive quotient has even nondegenerate rank | Thm. `thm:primitivity-canonical` | `NCG.even_finrank_primitiveQuotient` | ✅ (SvN 2^m rep 🧱) |
| Holonomy normal form, sheet ergodicity, continuum factorisation, enhanced package | Thms. `thm:internal-holonomy-normal-form`, `thm:sheet-ergodicity-main`, Cor. `cor:double-ergodicity-derived`, Lem. `lem:continuum-factorisation`, Def. `def:enhanced-package` | existing pillars + `NCG.EnhancedPackage` | ✅ / 🏗 |
| Twirl Ad-invariance + affine modular Hamiltonian | Thms. `thm:revision-twirl-main`, `thm:affine-modular` | `NCG/Algebra/RevisionTwirl.lean`, `NCG.affine_modular` | ✅ (Schur scalar step 🧱) |
| Reconstruction/universality at symbol level + 3+1 endpoint + marked classification | Thms. `thm:metric-reconstruction`, `thm:universality`, `thm:marked-torus-classification`, Cors. `cor:symbol-reconstruction`, `cor:31-endpoint`, Def. `def:strictly-marked-dirac-datum` | `NCG/Lorentz/Reconstruction.lean` | ✅ (operator limits / d_s 🧱) |
| `thm:frame-universality` (**repaired**) | dilation unitarity proved as a change-of-variables lintegral identity; chain-rule symbol conjugation proved | `NCG.dilation_lintegral_normSq`, `NCG.dilation_symbol_conjugation` (`NCG/Lorentz/FrameUniversality.lean`) | ✅ (closure extension 🧱) |
| `thm:dimension-coincidence`, `cor:full-dimension-chain` (**closed**) | exact lattice-ball count `(2R+1)^b`; crystal counting log-dimension `= 1+b_eff` as an actual limit; metric `δ→0⁺` squeeze: `upperBoxDimension = q` and `q_met = q_alg` as defined-limsup equalities | `NCG.crystal_log_dimension`, `NCG.upperBoxDimension_eq_of_poly_bounds`, `NCG.qmet_eq_qalg_of_poly_bounds` (`NCG/Renewal/CrystalCount.lean`, `DimensionTransfer.lean`) | ✅ (manuscript's five named assumptions = hypothesis interface) |
| **Primitive data in every odd rank** (standard symplectic form, every even dim) | Prop. `prop:primitive-all-odd` | `NCG.primitive_all_odd`, `NCG.stdSymplectic_nondegenerate` | ✅ (minimality-not-uniqueness now fully two-sided with the even-rank theorem) |
| Renewal measured causal set (rank time function, finite intervals, antichains) | Prop. `prop:measured-causet` | `NCG.productRank_strict_mono`, `NCG.eq_of_productRank_eq`, `NCG.card_interval` | ✅ |
| **Exact Ehrhart count + free spectral action** (stars and bars, Pascal shell) | Cor. `cor:ehrhart-free`, Thm. `thm:ehrhart-order` | `NCG.latticeShellCard_eq_choose`, `NCG.latticeShellCard_shell` (`NCG/Renewal/EhrhartCount.lean`) | ✅ (Tauberian repackaging 🧱) |
| Finite propagation is subadditive under composition | Prop. `prop:joint-finite-propagation` | `NCG.hasPropagation_comp` | ✅ (continuum energy estimates 🧱) |
| Optical-metric stability (**repaired**) | Lem. `lem:optical-distance-stability` | `‖u⁻²−v⁻²‖ ≤ 2c⁴‖v−u‖` proved in any normed ring — the manuscript's `2m₀⁻⁴` bound | `NCG.inv_sq_diff_bound` | ✅ (spectral input + distance convergence 🧱) |
| Marked-torus momentum gap + retention | Thms. `thm:marked-torus-band-limit`, `thm:marked-torus-correspondence` | `NCG.twisted_momentum_gap`, `NCG.marked_gap_sq`, `NCG.markedClass_injective` | ✅ (torus realization 🧱) |
| Canonical hyperbolic core (rank-2 alternating form) | Cor. `cor:canonical-hyperbolic-core` | `NCG.exists_pairing_one`, `NCG.rank2Form_nondegenerate` (`NCG/Lorentz/HyperbolicCore.lean`) | ✅ (Wedderburn `M₂(ℂ)` step 🧱) |
| Reset-field datum + sprinkling covariance (encodings) | Def. `def:reset-field`, Thm. `thm:sprinkling` | `NCG.ResetField`, `NCG.SprinklingCovariance` (`NCG/Lorentz/ResetField.lean`) | 🏗 (encoded) |
| **Reconstruction cluster** (basis bijection, shift/grading conjugation, complete invariant) | Thm. `thm:reconstruction`, Cor. `cor:iff` | `NCG.shift_conjugation`, `NCG.grading_conjugation`, `NCG.diagonal_commutant` | ✅ (deck-orbit descent 🔜) |
| Causal-cone kernel support + inner characterization | Lem. `lem:constant-dirac-kernel`, Thm. `thm:constant-inner-characterization` | `NCG.hasPropagation_pow`, `NCG.compressed_nonzero` | ✅ (Fourier wave kernel 🧱) |
| Curved core consistency (Hermiticity/square pillars only) | Prop. `prop:curved-core-consistency` (partial) | Krein multiplier pillars | ✅ (L² packaging 🧱) |
| Covariant central-difference cancellation (**repaired — derived**) | Lem. `lem:covariant-consistency` | transport×Taylor expansion computed through `Ω`'s linearity: difference exactly `2h(ψ'+Ωψ)+h³(Ωψ''+Ω²ψ')` | `NCG.covariant_central_difference` (`NCG/Lorentz/CovariantConsistency.lean`) | ✅ (L² packaging 🧱) |
| Cycle covariance full rank (PSD kernel core) | Prop. `prop:cycle-covariance-rank` | `NCG.psd_zero_diag_null`, `NCG.covariance_full_rank` | ✅ (Markov-additive CLT 🧱) |
| Isotropic rounding finite cores (`λ = 1/d`, `κ²M² = I`) | Thm. `thm:model-rounding` | `NCG.isotropic_trace_normalisation`, `NCG.rounding_kappa_sq` | ✅ (weak-*/Hausdorff limits 🧱) |
| Real-even division condition (ℍ vs `M₂(ℂ)`) | Thm. `thm:real-even-division-selects-three` | `NCG.quaternion_mul_eq_zero`, `NCG.matrix_two_zero_divisors` | ✅ (Wedderburn identifications 🧱) |
| **Free-case Weyl law + counting constant** | Thm. `thm:weyl-law`, Cor. `cor:renewal-counting` | `NCG.weyl_free_bounds`, `NCG.gamma_reflection_renewal` (`NCG/Renewal/WeylDichotomy.lean`) | ✅ (Karamata/Tauberian general case 🧱) |
| Renewal dichotomy (**repaired — actual limit**) | Thm. `thm:renewal-dichotomy` | `(1−F(z))/(1−z) → μ` and `(1−z)/(1−F(z)) → 1/μ` as `z→1` (finite-support case) | `NCG.renewal_ratio_tendsto`, `NCG.renewal_resolvent_pole` | ✅ (infinite support + Karamata (ii) 🧱) |
| Return-probability spectral dimension (log–log limit) | Cor. `cor:return-spectral-dimension` | `NCG.return_exponent_limit` (`NCG/Renewal/SpectralDimension.lean`) | ✅ (Delmotte bounds 🧱) |
| Empty resolvent via symbol factorisation | Prop. `prop:empty-resolvent` | `NCG.symbol_resolvent_factorisation`, `NCG.not_isUnit_of_symbol_null` | ✅ (L² multiplier packaging 🧱) |
| General rounding: `M ≻ 0 ⟹ M² ≻ 0`, signature measure-independent | Thm. `thm:general-rounding` | `NCG.posDef_mul_self` + Krein signature lemmas | ✅ (weak-*/Hausdorff 🧱) |
| Drift hull Minkowski-sum core + stencil moment consistency | Prop. `prop:drift-dispersion`, Lem. `lem:integer-stencil-decomposition` | `NCG.stepSum_eq_smul`, `NCG.stencil_moment_trace`, `NCG.stencil_moment_psd` | ✅ (density/perturbation existence 🧱) |
| Macroscopic domain (assembly) | Thm. `thm:macroscopic-domain` | propagation/kernel cores | ✅ (curved strong-resolvent limit 🧱) |
| Joint propagation (assembly, **re-established**) | Thm. `thm:joint-propagation` | all seven cited ingredient records now have genuine cores after the repairs | proved pillars per record | ✅ (curved packaging in ingredient records 🧱) |
| **Operator-limit chain**: `sin(hξ)/h → ξ`, uniform `h²Λ³/6` band error, full-operator assembly | Thms. `thm:operator-limit`, `thm:band-norm-resolvent`, `thm:full-operator` | `NCG.discrete_symbol_limit`, `NCG.band_symbol_bound` (`NCG/Lorentz/OperatorLimit.lean`) | ✅ (ℓ² strong-resolvent packaging 🧱) |
| Stability: squared-symbol shift + resolvent identity | Thm. `thm:stability`, Cor. `cor:curved-stability` | `NCG.perturbation_sq_bound`, `NCG.resolvent_identity` (`NCG/Lorentz/Stability.lean`) | ✅ (Kato–Rellich 🧱) |
| Frozen-symbol/cone convergence (quadratic-form Lipschitz) | Prop. `prop:joint-symbol-cone` | `NCG.quadratic_form_lipschitz` (`NCG/Lorentz/SymbolCone.lean`) | ✅ (Hausdorff cone limits 🧱) |
| Curved strong-resolvent limit (quantitative resolvent mechanism) | Thm. `thm:curved-limit` | `NCG.resolvent_diff_bound` + consistency/Hermiticity cores | ✅ (Trotter–Kato packaging 🧱) |
| Self-averaging (variance additivity, `1/N` rate) | Thm. `thm:self-averaging` | `NCG.variance_sum_uncorrelated` (`NCG/Lorentz/SelfAveraging.lean`) | ✅ (a.s. LLN packaging 🧱) |
| Worked reset-diffusion residue (exact formula + sup bound) | Prop. `prop:renewal-scalar-potential` | `NCG.ground_state_potential`, `NCG.potential_bound` (`NCG/Renewal/ScalarPotential.lean`) | ✅ (C²_b conjugation 🧱) |
| Controllability (open subgroup of connected group is everything) | Prop. `prop:interference-controllability` | `NCG.open_subgroup_eq_top` (`NCG/Dimension/Controllability.lean`) | ✅ (Lie closed-subgroup theorem 🧱) |
| Full-isotropy route (`d = 3` cross-product intertwiner) | Thm. `thm:full-isotropy-interference` | `NCG.cross_product_witness`, `NCG.cross_product_antisymm` (`NCG/Dimension/IsotropyInterference.lean`) | ✅ (SO(d) rep-theoretic vanishing 🧱) |
| Exact interval counting `∣[x,y]∣ = ∏(yᵢ−xᵢ+1)` (interval-growth dimension `= c`) | Prop. `prop:commuting-order` | `NCG.card_interval` | ✅ |
| **2d Minkowski emergence**: product order = Minkowski cone, `ΔuΔv = Δt²−Δξ²` | Thm. `thm:minkowski-2d` | `NCG.minkowski_causal_order`, `NCG.minkowski_proper_time` | ✅ (volume normalisation not formalised) |
| Flat holonomy sector is the commutative group algebra | Prop. `prop:flat-holonomy-obstruction` | `NCG.sheetShift_add`, `NCG.diagOp_comm` | ✅ |
| Flat sheet transport has trivial spatial block `ω∣_{H×H} = 0` | Prop. `prop:flat-spatial-block-zero` | `NCG.sheetShift_comm` | ✅ |
| Shell independence of the modular Gram data | Thm. `thm:exact-bicharacter-stabilisation` | `NCG.scalar_compression` | ✅ (scalar-compression form) |
| `ℤ/4` minimal square-root completion (order-4 theorem) | Thm. `thm:minimal-z4-amplitude-lift` | `NCG.orderOf_eq_four_of_sq_eq_neg_one` | ✅ |
| `ℤ/4 → ℤ/2` surjectivity (**repaired — actual graph cohomology**) | Lem. `lem:z4-lift-surjects` | `H1Z4 G` constructed; reduction surjective; `\|H¹(ℤ/4)\| = 4^{b₁}`; fibres exactly `2^{b₁}` | `NCG/Graph/CohomologyZ4.lean` | ✅ |
| **Graded Clifford exchange form + Gram matrix** (`Ω = Jₙ−Iₙ` invertible over `𝔽₂` iff `n` even) | Lem. `lem:graded-clifford-form`, Thm. `thm:intrinsic-graded-clifford-datum` (rank core) | `NCG.gen_mul_prod`, `NCG.prod_mul_prod_disjoint`, `NCG.gramMatrix_sq`, `NCG.gramMatrix_not_isUnit_of_odd` | ✅ (rank computation; full intrinsic-datum reconstruction 🔜) |
| **Renewal calibration**: unique pressure-zero root | Prop. `prop:renewal-calibration` | `NCG.pressure_eq_one_existsUnique` (IVT + strict antitonicity) | ✅ (residue/spectral-measure formula 🔜) |
| Cancellative fibres: descended shifts injective | Prop. `prop:fibres-monoid` | `NCG.RenewalMemory.shift_injective` | ✅ |
| **Polyhedral obstruction**: orthant ≇ round Lorentz cone (spatial dim ≥ 2) | Thm. `thm:obstruction`, Cor. `cor:lorentz-violation` | `NCG.polyhedral_obstruction` (+ `_complex` witness), extreme-ray calculus in `NCG/Lorentz/PolyhedralObstruction.lean` | ✅ |
| Cone-positive unitaries are permutations | Lem. `lem:cone-positive-permutation` | `NCG.conePositive_perm` | ✅ (rigidity input for `thm:classification`) |
| Rank-2 structure group `{I, S} ≅ ℤ/2` | Lem. `lem:minimal-rank-two` | `NCG.structure_group_rank_two` | ✅ |
| Two cochains, one class: `ε = c + δj`, coboundary gauge action | Lem. `lem:two-cochains-one-class` | `NCG.homogeneity_degree`, `NCG.gauge_transport`, `NCG.spow_add` | ✅ (model-fibre sign calculus) |
| Causal-order skeleton: locally finite graded poset | Prop. `prop:causal-skeleton` | `NCG.CausalSkeleton.interval_finite`, `saturated_chain_length_eq` | ✅ |
| `ℤ/4 → ℤ/2` amplitude lifts: surjective, `2^{b₁}` fibres | Lem. `lem:z4-lift-surjects` | `NCG.Multigraph.H1Z4.reduce_surjective`, `card_fibre_reduce` | ✅ |
| Reversible predictive revision theorem | Ass. `ass:signed-revision-phase`, Thm. `thm:reversible-predictive-revision` | assembles the above once `Aut(𝒜)`-innerness is formalized | 🔜 |
| Internal revision twirl (Schur averaging) | Thm. `thm:revision-twirl-main` | needs f.d. irreducibility + trace | 🧱 |
| Sheet ergodicity of the maximal cover / double ergodicity derived | Thm. `thm:sheet-ergodicity-main`, Cor. `cor:double-ergodicity-derived` | transitivity of deck action is `deck_transitive_on_fibre`; full statement needs `H¹` layer | 🔜 |

## Phase 1 — the positive predictive triple, analytically

| Item | Manuscript | Plan | Status |
|---|---|---|---|
| Finite fibres / bounded increments | Ass. `ass:fibres` | predicate on a `RenewalMemory`; classes (A)–(D) of Cor. `cor:automatic-triples` as instances | 🔜 |
| Shifts bounded on `ℓ²` iff finite fibres | Thm. `thm:fibre-dichotomy` (1),(2a) | `NCG/Operator/FibreDichotomy.lean` (dense core; `lp 2` completion 🔜) | ✅ |
| Bounded commutator dichotomy | Thm. `thm:fibre-dichotomy` (2b), Cor. `cor:sharp-existence` | via `diagOp_comm_shiftOp_single` + `lp` bounds | 🧱 |
| The predictive spectral triple | Thm. `thm:triple` | instance of `NCG.SpectralTriple` on `ℓ²(𝒲_CP)`; compact resolvent from finite length shells (Rem. `rem:compact-resolvent-finite-balls`) | 🧱 |
| Algebraic predictive dimension `q_alg` | Def. `def:qalg` | `limsup log N_CP(R) / log R` via `Filter.limsup` | 🔜 |
| Cancellative commuting regime `q_alg = r_mon` | Thm. `thm:commuting` | affine semigroups: Mathlib `AddMonoid` + `Submonoid.FG`; lattice-point counting | 🔜 |
| Ehrhart interval growth | Thm. `thm:ehrhart-order`, Cor. `cor:ehrhart-free` | exact stars-and-bars count `N_c(R) = C(R+c, c)` proved by coordinate peeling + hockey stick (`NCG/Renewal/EhrhartCount.lean`) | ✅ (general normal monoids 🧱) |
| Renewal Weyl law, Dixmier volume | Ass. `ass:regular-variation`, Thm. `thm:weyl-law` | Karamata/Tauberian layer; Dixmier traces do not yet exist in Mathlib | 🧱 (large; candidate Mathlib contribution) |
| Metric dimension `q_met`, Moran equation | Def. `def:qmet`, Thm. `thm:fractal` | box dimension exists in Mathlib (`Mathlib.Topology.MetricSpace.HausdorffDimension` etc.); cb-norm layer needed | 🧱 |
| `q_met ≤ q_alg` under Lipschitz coding | Thm. `thm:qmet-qalg`, `thm:qmet-qalg-equality` | covering/packing counting; mostly elementary once `N_cb` defined | 🔜 |
| Renewal calibration / pressure equation | Prop. `prop:renewal-calibration` | `NCG.pressure_eq_one_existsUnique` (`NCG/Renewal/Calibration.lean`) | ✅ |
| Causal-order skeleton | Ass. `ass:aperiodic`, Prop. `prop:causal-skeleton` | `NCG.CausalSkeleton.*` (`NCG/Renewal/CausalSkeleton.lean`) | ✅ |
| Chain-counting renewal resolvent | Prop. `prop:incidence-zeta` | incidence algebras: partial Mathlib support (`Mathlib.Combinatorics.Enumerative.IncidenceAlgebra`) | 🔜 |
| Renewal singularity dichotomy | Thm. `thm:renewal-dichotomy`, Cor. `cor:renewal-counting` | generating functions, Karamata Tauberian theorem | 🧱 |
| Functorial positivity no-go | Thm. `thm:functorial-positive-obstruction` | diagonal `J` ⟹ vertex sign ⟹ edge sign cocycle: combinatorial, buildable on `SignCocycle` | 🔜 (good next target) |

## Phase 2 — the signed Krein sector

| Item | Manuscript | Plan | Status |
|---|---|---|---|
| `H¹(G, ℤ/2) ≅ (ℤ/2)^{b₁}` | Thm. `thm:cover`, Cor. `cor:sector-count` | `NCG.Multigraph.finrank_H1_add_card_vertices`, `card_H1_of_connected` (`NCG/Graph/BettiNumber.lean`) | ✅ |
| Krein datum on the cover | Prop. `prop:krein-datum` | ✅ algebraic model (`krein_exchange`); `ℓ²`-version pending | 🏗 |
| Signed modular Dirac `D_χ = J e^{βN} + B` | Def. `def:signed-modular-twist`, Thm. `thm:signed-dirac` | twisted Krein spectral triple structure; summability | 🧱 |
| Bounded twisted commutators (checkable) | Ass. `ass:signed-bounded-geometry`, Lem. `lem:bounded-twisted`, Cor. `cor:checkable-signed-triple` | finite-propagation algebra on the cover; Schur test | 🧱 |
| Minimal-rank classification of enrichments | Lem. `lem:cone-positive-permutation`, Thm. `thm:classification` (with `def:fixed-enrichment`, `def:fixed-gauge`) | `NCG.Multigraph.EnrichmentDatum.classificationEquiv`, `card_enrichmentClasses` (`NCG/Krein/EnrichmentClassification.lean`) | ✅ (`π₀ ≅ H¹ ≅ (ℤ/2)^{b₁}`; naturality 🔜) |
| `ℤ/4` amplitude lifts | Thm. `thm:minimal-z4-amplitude-lift` | `NCG.orderOf_eq_four_of_sq_eq_neg_one` | ✅ |
| `ℤ/4 → ℤ/2` surjectivity | Lem. `lem:z4-lift-surjects` | graph-level `H1Z4` with surjective reduction | ✅ |
| Signed reconstruction | Lem. `lem:atom`, Thm. `thm:reconstruction`, Cor. `cor:iff` | atomic MASA rigidity; phase-permutation unitaries | 🧱 |
| Modular characterisation of `e^{βN}` | Lem. `lem:deck-odd-normal-form`, Lem. `lem:clock-scaling` ✅, Thm. `thm:modular-characterisation` | deck-odd diagonal normal form is elementary on the finsupp model | 🔜 (good next target) |
| Affine modular Hamiltonian | Ax. `ax:modular-homogeneity`, Thm. `thm:affine-modular` | commutant-scalar argument on connected cover | 🔜 |

## Phase 3 — Lorentzian continuum

| Item | Manuscript | Plan | Status |
|---|---|---|---|
| Kinematic assembly | Def. `def:rescaling` (assembly layer) | bookkeeping structure over Phases 1–2 | 🔜 |
| Measured causal set, rescaling | Def. `def:rescaling`, Prop. `prop:measured-causet` | product order on `ℕ^c`; interval = box counting | 🔜 |
| Polyhedral limit, reverse triangle inequality | Thm. `thm:taxicab-limit` | geometric-mean concavity (Mathlib `inner_le_nnorm...`/AM-GM); Lorentzian pre-length spaces need defining | 🧱 |
| 2d Minkowski emergence | Thm. `thm:minkowski-2d` | null-coordinate change of variables; elementary | 🔜 |
| Polyhedral obstruction (`c ≥ 3`) | Thm. `thm:obstruction`, Cor. `cor:lorentz-violation` | extreme rays of orthant vs. round cone: convex geometry in Mathlib | 🔜 (good target) |
| Symbol square / emergent metric | Lem. `lem:symbol-square`, Thm. `thm:signature-krein` | Clifford algebras exist in Mathlib (`CliffordAlgebra`); finite-dim representation calculus | 🧱 |
| Isotropic/general Clifford rounding | Thm. `thm:model-rounding`, `thm:general-rounding`, Ex. `ex:3plus1` | weak-* convergence of second moments (Mathlib measure theory) | 🧱 |
| Dirac Hamiltonian self-adjointness | Lem. `lem:alpha-selfadjoint` | Fourier multiplier calculus | 🧱 |
| Empty resolvent of hyperbolic Dirac | Prop. `prop:empty-resolvent` | multiplier norm estimates | 🧱 |
| Strong resolvent convergence | Thm. `thm:full-operator`, `thm:operator-limit` | Trotter–Kato exists partially in Mathlib? (needs survey) | 🧱 |
| Band-limited norm resolvent | Thm. `thm:band-norm-resolvent` | explicit `sin` estimates; more elementary than the strong-resolvent layer | 🧱 |
| Self-averaging (ergodic) | Thm. `thm:self-averaging` | Birkhoff ergodic theorem is in Mathlib | 🧱 |
| Frame universality | Thm. `thm:frame-universality` | change-of-variables unitary; mostly linear algebra + `L²` substitution | 🧱 |
| Discrete Cartan / Levi-Civita | Thm. `thm:fundamental`, `thm:channel-torsion` | finite-dimensional linear algebra (Koszul formula): feasible without heavy analysis | 🔜 |
| Curved strong-resolvent limit | Thm. `thm:curved-limit` | variable-coefficient operators | 🧱 |
| Stability estimates | Thm. `thm:stability`, Cor. `cor:curved-stability` | second resolvent identity + Duhamel; feasible after Hamiltonian layer | 🧱 |
| Marked torus correspondence | Thm. `thm:marked-torus-band-limit`, `thm:marked-torus-classification` | twisted momentum gap `≥ π` per marked direction, band separation `π²·\|ρ\|₀` proved (`NCG/Lorentz/MarkedTorus.lean`) | ✅ (norm-resolvent bookkeeping 🧱) |

## Phase 4 — dimension selection and 3+1

| Item | Manuscript | Plan | Status |
|---|---|---|---|
| Flat-holonomy obstruction | Prop. `prop:flat-holonomy-obstruction` | group algebra of `H¹` is commutative: easy once `H¹` defined | 🔜 |
| Temporal row forced | Lem. `lem:cycle-krein-exchange`, Thm. `thm:canonical-temporal-row` | iterate `krein_exchange` along walks (done for single edges) | 🔜 (good next target) |
| Scalarisation / revision algebra | Thm. `thm:spatial-multiplier-scalar-main`, `prop:full-revision-cocycle-main` | finite-dim rigidity (Schur); needs irreducibility infrastructure | 🧱 |
| Quadratic refinement, extraspecial extension | Thm. `thm:revision-quadratic-refinement-main`, `thm:revision-central-extension-main` | `ℤ/2`-bilinear algebra; finite group theory in Mathlib | 🔜 |
| Radical–centre dictionary | Thm. `thm:radical-centre` | twisted group algebras: build on Mathlib `MonoidAlgebra` with a 2-cocycle twist | 🔜 |
| Stone–von Neumann (finite) | Thm. `thm:primitivity-canonical`, `thm:factor-quotients-corrected` | finite Heisenberg groups; representation theory in Mathlib is adequate | 🧱 |
| Graded Clifford memory | Constr. `constr:graded-clifford-memory`, Lem. `lem:graded-clifford-form`, Thm. `thm:intrinsic-graded-clifford-datum` | exchange form + `𝔽₂` Gram rank done (`NCG/Dimension/GradedGram.lean`); intrinsic-datum reconstruction on Mathlib `CliffordAlgebra` 🔜 | 🏗 |
| Parity: `d_Cl` odd; no 2+1; minimal 3+1 | Thm. `thm:minimal-nondegenerate-3plus1` | nondegenerate alternating `𝔽₂`-forms have even rank — Mathlib `LinearAlgebra.Alternating`/`BilinearForm` | 🔜 (flagship target) |
| All odd ranks realized | Prop. `prop:primitive-all-odd` | explicit symplectic form; easy | 🔜 |
| Growth–cycle identity `q_alg = 1 + b₁^eff` | Thm. `thm:full-rank-returns` | bounded return completion; monoid geometry | 🧱 |
| Dimension coincidence | Thm. `thm:dimension-coincidence` | assembles Phases 1, 2, 4 | 🧱 |
| Volume-dual response / survival criterion | Thm. `thm:survival-criterion`, `thm:interference-closure-selects-three` | exterior algebra + Hodge star in Mathlib (`ExteriorAlgebra`); `⋀² ≅ ⋀^{d−2}` iff `d = 3` | 🔜 |
| Hodge/cross-product uniqueness (`d=3`), no `d=7` exception | Prop. `prop:hodge-interference-closure`, Rem. `rem:no-seven-dimensional-exception` | `SO(n)`-equivariant intertwiner spaces; representation theory | 🧱 |
| Access fixed points | Prop. `prop:additive-access-main`, Lem. `lem:odd-access-fixed-points`, Thm. `thm:conditional-access-3plus1` | discrete optimization over `ℕ`; elementary real analysis | 🔜 (easy target) |
| Access efficiency `η(m) = m/2^m` | Thm. `thm:access-efficiency-selection` | elementary; good warm-up | 🔜 (easy target) |
| Real-even division condition | Thm. `thm:real-even-division-selects-three` | real Clifford classification `Cl⁰₁ ≅ ℝ`, `Cl⁰₃ ≅ ℍ`; partially in Mathlib | 🧱 |
| Isotropy is dimension-blind | Thm. `thm:isotropy-dimension-blind` | cross-polytope second moment `= I/d`: elementary matrix computation | 🔜 (easy target) |
| Block-renewal RG eigenvalue | Thm. `thm:rg-eigenvalue`, Cor. `cor:relevance` | homogeneous symbol scaling; elementary once symbols defined | 🔜 |
| Canonicity theorem | Thm. `thm:canonicity` | assembly re-cited to its actual six ingredients (affine modular, derived projective lift, factor/radical counting, Cartan, block-RG) | ✅ (unbounded/Morita/O(h²) packaging 🧱) |

## Mathlib gaps this project will need to fill (candidate upstream contributions)

1. **Spectral triples & Krein spaces** — nothing exists; our `NCG.SpectralTriple`
   and `IsFundamentalSymmetry` are designed to be upstreamable.
2. **Unbounded self-adjoint operator theory** — Mathlib has `LinearPMap`
   adjoints and symmetric operators, but no spectral theorem for unbounded
   operators, no resolvent calculus, no Stone's theorem in full strength.
3. **Dixmier traces / weak trace ideals** (`ℒ^{1,∞}`, Connes trace theorem) —
   absent; needed for Thm. `thm:weyl-law` (iv).
4. **Karamata / Hardy–Littlewood Tauberian theorems** — absent; needed for the
   Weyl law and the renewal singularity dichotomy.
5. **Twisted group algebras with 2-cocycle** and finite Stone–von Neumann.
6. **Lorentzian pre-length spaces** — absent; needed for the continuum ladder.
7. **Graph cohomology `H¹(G, A)`** for multigraphs — we build this in
   `NCG.Graph` (cochains/coboundary quotient) with the spanning-tree rank
   formula.

## Suggested next steps (in order)

1. `H¹(G, ℤ/2)` as a `ZMod 2`-module with `b₁` rank formula
   (finishes Thm. `thm:cover` + Cor. `cor:sector-count`).
2. Functorial positivity no-go (Thm. `thm:functorial-positive-obstruction`) —
   purely combinatorial over what is already built.
3. Cycle Krein exchange + canonical temporal row
   (Lem. `lem:cycle-krein-exchange`, Thm. `thm:canonical-temporal-row`).
4. Deck-odd normal form + modular characterisation `D = J e^{βN} + B`
   (Thm. `thm:modular-characterisation`) on the finsupp model.
5. The easy Phase-4 items: access fixed points, access efficiency,
   isotropy-blindness, `ℤ/4` lifts, parity of nondegenerate alternating
   `𝔽₂`-forms (⟹ no `2+1`).
6. `lp 2` operator layer: bounded shifts under finite fibres — opens
   Thm. `thm:fibre-dichotomy` and the true Thm. `thm:triple`.
