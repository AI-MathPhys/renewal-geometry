/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.SupplementVacuumEquationInstantiated

/-!
# General renewal-to-Einstein certification
  (`thm:main-renewal-einstein`, `eq:main-einstein-variation`, `eq:main-vacuum-einstein`;
  emergent-spacetime manuscript)

This file assembles `thm:main-renewal-einstein` as one theorem whose hypothesis packet
`RenewalEinsteinCertification` is organised by the five certification conditions `(E1)`–`(E5)`
of the manuscript, and proves it by instantiating the localized renewal–Palatini handoff
`thm:supp-renewal-palatini` (`RenewalPalatiniHandoff.renewal_palatini_handoff`,
`renewal_palatini_handoff_literalLink`) and the corollary `cor:supp-renewal-einstein`
(`RenewalEinstein.renewal_vacuum_equation`, `renewal_vacuum_equation_literalLink`).

## The packet `RenewalEinsteinCertification`

The regulators are a cofinal sequence `X = n` of common-cylinder interpolants on an open cylinder
`Ω ⊆ ℝ⁴` (indexed from the start of the cofinal tail on which `(E1)`–`(E5)` hold): coframes
`e_X`, `so(1,3)` connections `ω_X`, curvature records `R_X`, represented torsion `T_X`, scores
`L_X` in the local gravitational class; limits `e`, `ω`; coefficients `(α, β, λ)`.  The
compact cylinder `K ⊆ Ω` carries the determining metric-test core `core ⊆ Test` (test fields
`kOf τ`), the physical lifts `H τ X` and the realized first variations `δA τ X` of the
reconstructed scalar common action.

* standing structure of the Lorentzian relational regulators (`mt:adm`): metric-compatible
  Lorentz connections, represented `L²_loc` torsion two-forms;
* `(E1)`: the realized first variations tend to zero on the core; bounded convergent physical
  lift coefficient tensors;
* `(E2)`: classified first-order score (`thm:main-gravitational-classification`: real Lorentz
  naturality etc.), and the physical first-variation remainder condition
  `eq:main-first-variation-reduction` on the same tests;
* `(E3)`: calibrated coefficient limits with `β ≠ 0`, spinless connection Euler residual tending
  to zero, uniformly nondegenerate Cartan map;
* `(E4)`: the output of the spatial-screen / common-cylinder compact-screen packet: a
  nondegenerate limit, `e_X → e` strongly in `L²_loc`, `sup_X ‖e_X‖_{L⁶(K)} < ∞` (oriented
  regulator coframes);
* `(E5)`: the output of the curvature propagation certificate (`sup_X ‖R_X‖_{L²(K)} < ∞`), and
  the connection/curvature handoff as an alternative of two routes:
  - `FullConnectionCertificate`: `ass:main-connection-compactness` after extraction
    (`ω_X → ω` strongly in `L²_loc`, first item of `eq:main-identified-curvature-hypotheses`),
    the two Cartan identification residuals `𝔠_X(K) → 0` (`eq:main-cartan-curvature-residual`)
    and `𝔍_X(Φ) → 0` (`eq:main-cartan-incidence`) for a finite Cartan writer `𝓡_X(ω_X)` (typed
    data `W`, a curvature-shaped field; the manuscript describes the writer only in words), and
    **the AMENDMENT `spatialConnectionL3Bound`** (uniform `L³_loc` bound on the spatial connection
    coefficients; not in the manuscript's list; supplied by the Hodge–temporal budget
    `eq:main-connection-hodge-budget` of the sufficient realization `thm:main-hodge-connection`);
  - `LiteralLinkCertificate`: the output of `thm:main-literal-link-compactness` on the cylinder
    (bounded, weakly `L²_loc`-convergent connection coefficients with strongly convergent spatial
    ones; curvature records weakly convergent to the full nonlinear curvature `dω + ω ∧ ω` of the
    limit), with `spatialConnectionL3Bound` (on this route `eq:supp-literal-integrability`).

## Main result

`renewal_einstein_certification` (**`thm:main-renewal-einstein`**): under `(E1)`–`(E5)` the
limiting torsion vanishes, `χ = β ≠ 0`, and on a compact neighbourhood `K'` of `K` there is an
identified limiting curvature `RL = dω + ω ∧ ω` with the limit connection metric compatible, the
limit coframe oriented, and `ω` the unique torsion-free metric-compatible (Levi-Civita)
connection; for every determining test the metric first variation converges to
`χ ∫_K √(-g) (G + Λ g) k` (`eq:main-einstein-variation`, `Λ = -λ/(2β)`), and
`G + Λ g = 0` holds distributionally on the determining test core and, under continuity in the
declared test topology, on its closure (`eq:main-vacuum-einstein`).  The whole cofinal sequence
converges (the paper's "a subsequence" is the selected sequence itself).

The conclusion also exports integrability on `K` of the Einstein insertion density of every core
test.  `renewal_einstein_certification_ae`: pointwise form (symmetrized `√(-g)(G + Λ g)` vanishes
a.e. on `int K`) when the core contains the constant symmetric unit tests and their smooth
localizations; non-vacuity `renewalEinsteinCertification_flat_ae`.

`renewalEinsteinCertification_flat`, `renewalEinsteinCertification_flat_literalLink`:
non-vacuity (flat Minkowski coframe, zero connection, Palatini score, constant tests,
zero Cartan writer), including the amendment.

Disclosed renderings: the operational reconstructions behind `(E1)` (determining kernel, scalar
common action), `(E4)` (`thm:main-spatial-screen`, `liminf I_X^eff > 0`, transported screens) and
`(E5)` (propagation budgets, `thm:main-curvature-propagation` / `thm:main-discrete-curvature`,
`thm:main-hodge-connection`, `thm:main-literal-link-compactness`) enter through their stated
outputs on the common-cylinder interpolants (the lattice records are proved in their periodic
settings; their transport to the cylinder interpolants is not formalised); the Cartan residuals
are tested on all smooth tests of `Ω` (the manuscript's banks exhaust a countable determining
smooth core); the connection-test part of `eq:main-first-variation-reduction` enters through the
`(E3)` Euler residual, as in the handoff.
-/

open MeasureTheory Filter Topology ENNReal TopologicalSpace Set
open scoped NNReal Distributions Matrix

noncomputable section

namespace RenewalGeometry.RenewalEinstein

open DistributionalTorsion DistributionalCurvature LimitEinsteinInsertion PalatiniEinsteinAlgebra
  RenewalPalatiniHandoff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ### `(E5)`: the two connection/curvature routes -/

/-- `(E5)`, full-connection branch: `ass:main-connection-compactness` (after extraction) with the
two Cartan identification residuals of `eq:main-identified-curvature-hypotheses`, for a finite
Cartan writer `W X = 𝓡_X(ω_X)`, plus the disclosed amendment `spatialConnectionL3Bound`. -/
structure FullConnectionCertificate (Ω : Opens (Fin 4 → ℝ))
    (ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (R W : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (t : Fin 4) : Prop where
  /-- (E5) "the connection satisfies the separate compactness certificate
  `ass:main-connection-compactness`": after extraction, `ω_X → ω` strongly in `L²_loc`
  (`eq:main-identified-curvature-hypotheses`). -/
  connection_L2 : L2LocTendsto Ω ω ωL
  /-- **AMENDMENT** (accepted manuscript correction): a uniform `L³_loc` bound on the spatial
  connection coefficients, supplied by `eq:main-connection-hodge-budget` of the sufficient
  Hodge–temporal realization `thm:main-hodge-connection`. -/
  spatialConnectionL3Bound : ∀ a, a ≠ t → ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (ω n a) 3 (volume.restrict C) ≤ M
  /-- (E5) "the two Cartan identification residuals in
  `eq:main-identified-curvature-hypotheses`", first residual `𝔠_X(K) → 0`
  (`eq:main-cartan-curvature-residual`): the actual curvature records against the Cartan writer. -/
  cartanCurvatureResidual : ∀ (φ : 𝓓(Ω, ℝ)) a b,
    Tendsto (fun n => (∫ x, φ x • R n a b x) - ∫ x, φ x • W n a b x) atTop (𝓝 0)
  /-- Second residual `𝔍_X(Φ) → 0` (`eq:main-cartan-incidence`): the Cartan writer against the
  distributional curvature `d_dist ω_X + ω_X ∧ ω_X`. -/
  cartanIncidenceResidual : ∀ (φ : 𝓓(Ω, ℝ)) a b,
    Tendsto (fun n => (∫ x, φ x • W n a b x) - curvaturePairing (ω n) φ a b) atTop (𝓝 0)

/-- `(E5)`, periodic literal-link branch: the output of `thm:main-literal-link-compactness` on the
common cylinder ("directly supplies strong spatial connection compactness and identifies the full
nonlinear curvature from the electric and magnetic records"), with `spatialConnectionL3Bound`
(on this route the bound `eq:supp-literal-integrability`). -/
structure LiteralLinkCertificate (Ω : Opens (Fin 4 → ℝ))
    (ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (t : Fin 4) : Prop where
  /-- The uniform spatial `L³_loc` bound (`eq:supp-literal-integrability` on this route). -/
  spatialConnectionL3Bound : ∀ a, a ≠ t → ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (ω n a) 3 (volume.restrict C) ≤ M
  connection_L2 : ∀ n a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (ω n a) 2 (volume.restrict C)
  connection_bound : ∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (ω n a) 2 (volume.restrict C) ≤ M
  connection_limit_L2 : ∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (ωL a) 2 (volume.restrict C)
  /-- `𝓘_h A_{0,h} ⇀ A_0` (and every coefficient) weakly in `L²_loc`
  (`eq:main-link-convergence`). -/
  connection_weak : ∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω → ∀ g : (Fin 4 → ℝ) → ℝ,
    MemLp g 2 (volume.restrict C) →
    Tendsto (fun n => ∫ x in C, g x • ω n a x) atTop (𝓝 (∫ x in C, g x • ωL a x))
  /-- `𝓘_h A_h → A` strongly in `L²_loc` (`eq:main-link-convergence`). -/
  spatial_strong : ∀ a, a ≠ t → ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    LpTendsto (volume.restrict C) 2 (fun n => ω n a) (ωL a)
  curvature_limit_L2 : ∀ a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (RL a b) 2 (volume.restrict C)
  /-- The literal electric and magnetic records converge weakly in `L²_loc`. -/
  curvature_weak : ∀ a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    ∀ g : (Fin 4 → ℝ) → ℝ, MemLp g 2 (volume.restrict C) →
    Tendsto (fun n => ∫ x in C, g x • R n a b x) atTop (𝓝 (∫ x in C, g x • RL a b x))
  /-- Their weak limits are the components of `R(ω) = dω + ω ∧ ω`
  (`eq:main-link-curvature-limit`). -/
  curvature_identified : IsDistributionalCurvature Ω ωL RL

/-! ### The certification packet `(E1)`–`(E5)` -/

/-- **The five certification conditions of `thm:main-renewal-einstein`** on the compact cylinder
`K ⊆ Ω` (see the module docstring for the data). -/
structure RenewalEinsteinCertification (Ω : Opens (Fin 4 → ℝ))
    (score : ℕ → GravitationalClassDensity)
    (e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (R W : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (α β lam : ℝ) (t : Fin 4)
    (K : Set (Fin 4 → ℝ)) {Test : Type*}
    (kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (core : Set Test)
    (H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (M : Test → ℝ)
    (δA : Test → ℕ → ℝ) : Prop where
  /-- Standing structure of the Lorentzian relational regulators (`mt:adm`): metric-compatible
  Lorentz connections. -/
  connection_lorentz : ∀ n, ∀ᵐ x, x ∈ Ω → ∀ a,
    (minkowski * ω n a x)ᵀ = -(minkowski * ω n a x)
  /-- Standing structure: the regulator torsion two-form `d e_X + ω_X ∧ e_X` is represented by
  `T_X` (the object of the `(E3)` Euler residual). -/
  torsion_rep : ∀ n (φ : 𝓓(Ω, ℝ)) a b,
    torsionPairing matAct (e n) (ω n) φ a b = ∫ x, φ x • T n a b x
  torsion_antisymm : ∀ n a b, ∀ᵐ x, x ∈ Ω → T n b a x = -T n a b x
  torsion_L2 : ∀ n a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (T n a b) 2 (volume.restrict C)
  /-- `K` is a compact spacetime cylinder of `Ω`. -/
  e1_compact : IsCompact K
  e1_subset : K ⊆ Ω
  /-- (E1) "Its actual first variations tend to zero on a fixed determining metric-test core." -/
  e1_firstVariation_vanish : ∀ τ ∈ core, Tendsto (δA τ) atTop (𝓝 0)
  /-- (E1) "The physical coframe lifts of these tests have uniformly bounded, convergent
  coefficient tensors in the curvature and volume insertions": measurability. -/
  e1_lift_measurable : ∀ τ ∈ core, ∀ n, AEStronglyMeasurable (H τ n) (volume.restrict K)
  /-- (E1) uniformly bounded lift coefficient tensors. -/
  e1_lift_bounded : ∀ τ ∈ core, ∀ n, ∀ᵐ x ∂(volume.restrict K), ‖H τ n x‖ ≤ M τ
  /-- (E1) convergent lift coefficient tensors (limit: the inverse-metric test lift `-½ k g`). -/
  e1_lift_tendsto : ∀ τ ∈ core, ∀ᵐ x ∂(volume.restrict K),
    Tendsto (fun n => H τ n x) atTop (𝓝 (metricTestGenerator minkowski (cfm eL x) (kOf τ x)))
  /-- (E2) "Complete resolved-memory subtraction and exact or summably stable binary face
  subdivision give the first-order score classified by
  `thm:main-gravitational-classification`": Lorentz-natural members of the gravitational class. -/
  e2_classified : ∀ n, (score n).IsLorentzNatural
  /-- (E2) "with the physical first-variation remainder condition
  `eq:main-first-variation-reduction` on the same metric and connection tests". -/
  e2_firstVariationRemainder : ∀ τ ∈ core, Tendsto (classifiedVariationRemainder (δA τ)
    (fun n => realizedHolst K (e n) (H τ n) (R n))
    (fun n => realizedPalatini K (e n) (H τ n) (R n))
    (fun n => realizedVolume K (e n) (H τ n))
    (fun n => holstCoeff (score n)) (fun n => palatiniCoeff (score n))
    (fun n => volumeCoeff (score n))) atTop (𝓝 0)
  /-- (E3) "the spacetime-constant coefficients converge, `(α_X, β_X, λ_X) → (α, β, λ)`". -/
  e3_holst_tendsto : Tendsto (fun n => holstCoeff (score n)) atTop (𝓝 α)
  e3_palatini_tendsto : Tendsto (fun n => palatiniCoeff (score n)) atTop (𝓝 β)
  e3_volume_tendsto : Tendsto (fun n => volumeCoeff (score n)) atTop (𝓝 lam)
  /-- (E3) "with `β ≠ 0` the coefficient of `L_Palatini`". -/
  e3_palatini_ne_zero : β ≠ 0
  /-- (E3) "The spinless connection Euler residual tends to zero". -/
  e3_euler_residual_tendsto : ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    Tendsto (fun n => eLpNorm (eulerResidualRep (holstCoeff (score n)) (palatiniCoeff (score n))
      (e n) (T n)) 2 (volume.restrict C)) atTop (𝓝 0)
  /-- (E3) "and the Cartan map is uniformly nondegenerate on the retained coframe chart". -/
  e3_cartan_floor : ∃ κ : ℝ, 0 < κ ∧ ∀ n, ∀ᵐ x, x ∈ Ω →
    ∀ v : Fin 4 → Fin 4 → Fin 4 → ℝ, (∀ I μ ν, v I μ ν = -v I ν μ) →
      κ * ‖v‖ ≤ ‖PalatiniTorsionModel.cartan (coframeArr (e n) x) v‖
  /-- (E4) "`e_X → e` strongly in local `L²`". -/
  e4_coframe_L2 : L2LocTendsto Ω e eL
  /-- (E4) "`sup_X ‖e_X‖_{L⁶(K)} < ∞`". -/
  e4_coframe_L6 : ∀ c (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (e n c) 6 (volume.restrict C) ≤ M
  /-- (E4) oriented regulator coframes (Lorentzian relational regulators). -/
  e4_coframe_oriented : ∀ n, ∀ᵐ x, x ∈ Ω → 0 < (cfm (e n) x).det
  /-- (E4) "gives a nondegenerate limit". -/
  e4_limit_nondegenerate : ∀ᵐ x, x ∈ Ω → (cfm eL x).det ≠ 0
  /-- (E5) "The actual curvature records satisfy either the continuous propagation certificate
  ... or the fully discrete certificate": their output, `L²` curvature records ... -/
  e5_curvature_L2 : ∀ n a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (R n a b) 2 (volume.restrict C)
  /-- ... with `sup_X ‖R_X‖_{L²(K)} < ∞` on every compact. -/
  e5_curvature_bound : ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ n a b, eLpNorm (R n a b) 2 (volume.restrict C) ≤ B
  /-- (E5) "For the connection/curvature handoff, either the connection satisfies the separate
  compactness certificate `ass:main-connection-compactness` ... and the two Cartan identification
  residuals ..., or the periodic literal-link branch satisfies
  `thm:main-literal-link-compactness`". -/
  e5_connection_route : FullConnectionCertificate Ω ω R W ωL t ∨
    ∃ RL, LiteralLinkCertificate Ω ω R ωL RL t

/-! ### The conclusion -/

/-- The conclusion of `thm:main-renewal-einstein` on the compact cylinder `K`: vanishing limiting
torsion, `χ = β ≠ 0`, and on a compact neighbourhood `K'` of `K` an identified limiting curvature
`RL = dω + ω ∧ ω` of the metric-compatible, oriented, Levi-Civita limit, such that the metric
first variations converge to `χ ⟨G + Λ g, k⟩_K` (`eq:main-einstein-variation`), the Einstein
insertion density of every core test is integrable on `K` (so the pairing is a genuine integral),
and
`G + Λ g = 0` on the determining core and, under continuity in the declared test topology, on its
closure (`eq:main-vacuum-einstein`). -/
def EinsteinCertificationConclusion (Ω : Opens (Fin 4 → ℝ))
    (eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (β lam : ℝ) (K : Set (Fin 4 → ℝ))
    {Test : Type*} [TopologicalSpace Test] (kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (core : Set Test) (δA : Test → ℕ → ℝ) : Prop :=
  IsTorsionFree matAct Ω eL ωL ∧ β ≠ 0 ∧
  ∃ K' : Set (Fin 4 → ℝ), IsCompact K' ∧ K ⊆ interior K' ∧ K' ⊆ Ω ∧
  ∃ RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ,
    (∀ a b, MemLp (RL a b) 2 (volume.restrict K')) ∧
    IsDistributionalCurvature (interiorOpens K') ωL RL ∧
    (∀ᵐ x ∂(volume.restrict K'), ∀ a, (minkowski * ωL a x)ᵀ = -(minkowski * ωL a x)) ∧
    (∀ᵐ x ∂(volume.restrict K'), 0 < (cfm eL x).det) ∧
    (∀ ω' : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ,
      (∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ interiorOpens K' →
        MemLp (ω' a) 2 (volume.restrict C)) →
      IsTorsionFree matAct (interiorOpens K') eL ω' →
      (∀ᵐ x, x ∈ interiorOpens K' → ∀ a, (minkowski * ω' a x)ᵀ = -(minkowski * ω' a x)) →
      ∀ᵐ x, x ∈ interiorOpens K' → ∀ a, ω' a x = ωL a x) ∧
    (∀ τ ∈ core, Integrable (fun x => einsteinInsertionDensity β lam (cfm eL x) (kOf τ x)
        (rcf RL x)) (volume.restrict K) ∧
      Integrable (fun x => einsteinCosmologicalDensity (cosmologicalConstant β lam) (cfm eL x)
        (kOf τ x) (rcf RL x)) (volume.restrict K)) ∧
    (∀ τ ∈ core, Tendsto (δA τ) atTop
      (𝓝 (β * einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ)))) ∧
    (∀ τ ∈ core, einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ) = 0) ∧
    (Continuous (fun τ => einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL
        (kOf τ)) →
      ∀ τ ∈ closure core,
        einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ) = 0)


/-! ### Assembly of the handoff packets from `(E1)`–`(E5)` -/

section Assembly

variable {Ω : Opens (Fin 4 → ℝ)} {score : ℕ → GravitationalClassDensity}
  {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {R W : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {α β lam : ℝ} {t : Fin 4}
  {K : Set (Fin 4 → ℝ)} {Test : Type*} {kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {core : Set Test} {H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {M : Test → ℝ}
  {δA : Test → ℕ → ℝ}

/-- The common hypotheses of the handoff from `(E2)`–`(E5)` and a spatial `L³_loc` bound. -/
theorem RenewalEinsteinCertification.toCommon
    (h : RenewalEinsteinCertification Ω score e ω R W T eL ωL α β lam t K kOf core H M δA)
    (hL3 : ∀ a, a ≠ t → ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
      ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (ω n a) 3 (volume.restrict C) ≤ M) :
    RenewalPalatiniCommon Ω score e ω R T eL α β lam t where
  natural := h.e2_classified
  holst_tendsto := h.e3_holst_tendsto
  palatini_tendsto := h.e3_palatini_tendsto
  volume_tendsto := h.e3_volume_tendsto
  palatini_ne_zero := h.e3_palatini_ne_zero
  coframe_L2 := h.e4_coframe_L2
  coframe_L6 := h.e4_coframe_L6
  coframe_oriented := h.e4_coframe_oriented
  limit_nondegenerate := h.e4_limit_nondegenerate
  connection_lorentz := h.connection_lorentz
  spatialConnectionL3Bound := hL3
  torsion_rep := h.torsion_rep
  torsion_antisymm := h.torsion_antisymm
  torsion_L2 := h.torsion_L2
  cartan_floor := h.e3_cartan_floor
  euler_residual_tendsto := h.e3_euler_residual_tendsto
  curvature_L2 := h.e5_curvature_L2
  curvature_bound := h.e5_curvature_bound

/-- The full-connection handoff packet: the two Cartan residuals combine into the distributional
curvature identification `eq:supp-curvature-identification`. -/
theorem RenewalEinsteinCertification.toHypotheses
    (h : RenewalEinsteinCertification Ω score e ω R W T eL ωL α β lam t K kOf core H M δA)
    (hF : FullConnectionCertificate Ω ω R W ωL t) :
    RenewalPalatiniHypotheses Ω score e ω R T eL ωL α β lam t :=
  { h.toCommon hF.spatialConnectionL3Bound with
    connection_L2 := hF.connection_L2
    curvature_identification := fun φ a b => by
      have hs := (hF.cartanCurvatureResidual φ a b).add (hF.cartanIncidenceResidual φ a b)
      rw [add_zero] at hs
      exact hs.congr fun n => sub_add_sub_cancel _ _ _ }

/-- The literal-link handoff packet. -/
theorem RenewalEinsteinCertification.toLiteralLinkHypotheses
    (h : RenewalEinsteinCertification Ω score e ω R W T eL ωL α β lam t K kOf core H M δA)
    {RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hL : LiteralLinkCertificate Ω ω R ωL RL t) :
    RenewalPalatiniLiteralLinkHypotheses Ω score e ω R T eL ωL RL α β lam t :=
  { h.toCommon hL.spatialConnectionL3Bound with
    connection_L2 := hL.connection_L2
    connection_bound := hL.connection_bound
    connection_limit_L2 := hL.connection_limit_L2
    connection_weak := hL.connection_weak
    spatial_strong := hL.spatial_strong
    curvature_limit_L2 := hL.curvature_limit_L2
    curvature_weak := hL.curvature_weak
    curvature_identified := hL.curvature_identified }

/-- The certified metric tests of `(E1)`–`(E2)`. -/
theorem RenewalEinsteinCertification.toCertifiedMetricTests
    (h : RenewalEinsteinCertification Ω score e ω R W T eL ωL α β lam t K kOf core H M δA) :
    CertifiedMetricTests K score e R eL kOf core H M δA :=
  ⟨h.e1_lift_measurable, h.e1_lift_bounded, h.e1_lift_tendsto, h.e2_firstVariationRemainder⟩

end Assembly

/-! ### `thm:main-renewal-einstein` -/

/-- **`thm:main-renewal-einstein` (general renewal-to-Einstein certification).**  If the
certification conditions `(E1)`–`(E5)` hold (`RenewalEinsteinCertification`, with either
connection route in `(E5)`; the full-connection route carries the disclosed amendment
`spatialConnectionL3Bound`), then the limiting torsion vanishes, `χ = β ≠ 0`, the limit connection
is the metric-compatible Levi-Civita connection of the oriented limit coframe with identified
curvature `RL = dω + ω ∧ ω`, for each determining test `k` the metric first variation converges to
`χ ∫_K √(-g) (G_{μν} + Λ g_{μν}) k^{μν}` (`eq:main-einstein-variation`, `Λ = -λ/(2β)`), and
`G_{μν} + Λ g_{μν} = 0` holds distributionally on the determining test core and on its closure in
the declared test topology (`eq:main-vacuum-einstein`). -/
theorem renewal_einstein_certification {Ω : Opens (Fin 4 → ℝ)}
    {score : ℕ → GravitationalClassDensity} {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R W : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {α β lam : ℝ} {t : Fin 4}
    {K : Set (Fin 4 → ℝ)} {Test : Type*} [TopologicalSpace Test]
    {kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {core : Set Test}
    {H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {M : Test → ℝ}
    {δA : Test → ℕ → ℝ}
    (h : RenewalEinsteinCertification Ω score e ω R W T eL ωL α β lam t K kOf core H M δA) :
    EinsteinCertificationConclusion Ω eL ωL β lam K kOf core δA := by
  have htests := h.toCertifiedMetricTests
  have hvan : ∀ τ ∈ core, Tendsto (fun n => δA τ (id n)) atTop (𝓝 0) :=
    fun τ hτ => h.e1_firstVariation_vanish τ hτ
  rcases h.e5_connection_route with hF | ⟨RL, hL⟩
  · -- full-connection route
    have P := h.toHypotheses hF
    obtain ⟨-, hTF, hloc⟩ := renewal_palatini_handoff P
    obtain ⟨K', hK', hKK', hK'Ω, RL, hRL, hid, hcompat, hdet, hLC, hvar⟩ :=
      hloc K h.e1_compact h.e1_subset
    have hUK' : ((interiorOpens K' : Opens (Fin 4 → ℝ)) : Set (Fin 4 → ℝ)) ⊆ Ω :=
      interior_subset.trans hK'Ω
    have hint : ∀ τ ∈ core, Integrable (fun x => einsteinInsertionDensity β lam (cfm eL x)
        (kOf τ x) (rcf RL x)) (volume.restrict K) ∧
        Integrable (fun x => einsteinCosmologicalDensity (cosmologicalConstant β lam) (cfm eL x)
          (kOf τ x) (rcf RL x)) (volume.restrict K) := fun τ hτ => by
      have hI := integrable_einsteinInsertionDensity h.e1_compact hK' hKK'
        (fun μ => P.coframe_L2.lpTendsto μ hK' hK'Ω) (fun μ => P.coframe_L6 μ K' hK' hK'Ω)
        (fun a => P.connection_L2.memLp_lim a K' hK' hK'Ω)
        (fun a _ => P.connection_L2.lpTendsto a hK' hK'Ω)
        (fun a ha => P.spatialConnectionL3Bound a ha K' hK' hK'Ω) (isTorsionFree_mono hUK' hTF)
        hcompat hdet hid hRL (htests.lift_measurable τ hτ) (htests.lift_bounded τ hτ)
        (htests.lift_tendsto τ hτ) (lam := lam) h.e3_palatini_ne_zero
      exact ⟨hI, integrable_einsteinCosmologicalDensity_of_insertion h.e3_palatini_ne_zero hI⟩
    have hlim : ∀ τ ∈ core, Tendsto (δA τ) atTop
        (𝓝 (β * einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ))) :=
      fun τ hτ => by
        rw [← integral_einsteinInsertionDensity_eq]
        exact hvar (kOf τ) (H τ) (M τ) (δA τ) (htests.lift_measurable τ hτ)
          (htests.lift_bounded τ hτ) (htests.lift_tendsto τ hτ)
          (htests.firstVariationRemainder τ hτ)
    have h0 := insertion_vanishes_on_core core δA _ h.e3_palatini_ne_zero hlim tendsto_id hvan
    exact ⟨hTF, h.e3_palatini_ne_zero, K', hK', hKK', hK'Ω, RL, hRL, hid, hcompat, hdet, hLC,
      hint, hlim, h0, fun hc => insertion_vanishes_on_closure core _ hc h0⟩
  · -- literal-link route
    have P := h.toLiteralLinkHypotheses hL
    obtain ⟨-, hTF, hloc⟩ := renewal_palatini_handoff_literalLink P
    obtain ⟨K', hK', hKK', hK'Ω, hcompat, hdet, hLC, hvar⟩ := hloc K h.e1_compact h.e1_subset
    have hUK' : ((interiorOpens K' : Opens (Fin 4 → ℝ)) : Set (Fin 4 → ℝ)) ⊆ Ω :=
      interior_subset.trans hK'Ω
    have hint : ∀ τ ∈ core, Integrable (fun x => einsteinInsertionDensity β lam (cfm eL x)
        (kOf τ x) (rcf RL x)) (volume.restrict K) ∧
        Integrable (fun x => einsteinCosmologicalDensity (cosmologicalConstant β lam) (cfm eL x)
          (kOf τ x) (rcf RL x)) (volume.restrict K) := fun τ hτ => by
      have hI := integrable_einsteinInsertionDensity h.e1_compact hK' hKK'
        (fun μ => P.coframe_L2.lpTendsto μ hK' hK'Ω) (fun μ => P.coframe_L6 μ K' hK' hK'Ω)
        (fun a => hL.connection_limit_L2 a K' hK' hK'Ω)
        (fun a ha => hL.spatial_strong a ha K' hK' hK'Ω)
        (fun a ha => hL.spatialConnectionL3Bound a ha K' hK' hK'Ω) (isTorsionFree_mono hUK' hTF)
        hcompat hdet (fun ψ a b => hL.curvature_identified (liftTest hUK' ψ) a b)
        (fun a b => hL.curvature_limit_L2 a b K' hK' hK'Ω) (htests.lift_measurable τ hτ)
        (htests.lift_bounded τ hτ) (htests.lift_tendsto τ hτ) (lam := lam) h.e3_palatini_ne_zero
      exact ⟨hI, integrable_einsteinCosmologicalDensity_of_insertion h.e3_palatini_ne_zero hI⟩
    have hlim : ∀ τ ∈ core, Tendsto (δA τ) atTop
        (𝓝 (β * einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ))) :=
      fun τ hτ => by
        rw [← integral_einsteinInsertionDensity_eq]
        exact hvar (kOf τ) (H τ) (M τ) (δA τ) (htests.lift_measurable τ hτ)
          (htests.lift_bounded τ hτ) (htests.lift_tendsto τ hτ)
          (htests.firstVariationRemainder τ hτ)
    have h0 := insertion_vanishes_on_core core δA _ h.e3_palatini_ne_zero hlim tendsto_id hvan
    exact ⟨hTF, h.e3_palatini_ne_zero, K', hK', hKK', hK'Ω, RL,
      fun a b => hL.curvature_limit_L2 a b K' hK' hK'Ω,
      fun ψ a b => hL.curvature_identified (liftTest hUK' ψ) a b, hcompat, hdet, hLC,
      hint, hlim, h0, fun hc => insertion_vanishes_on_closure core _ hc h0⟩

/-- **Pointwise form of `eq:main-vacuum-einstein` on a rich core**: if, in addition, the
determining core contains the constant symmetric unit tests `E_{ij} + E_{ji}` and their
localizations `φ (E_{ij} + E_{ji})`, `φ ∈ 𝓓(int K)`, then the symmetrized tensor density
`√(-g) ((G + Λ g)_{ij} + (G + Λ g)_{ji})` of the identified limit vanishes almost everywhere on
`int K` (from the exported integrability and core vanishing, by the fundamental lemma). -/
theorem renewal_einstein_certification_ae {Ω : Opens (Fin 4 → ℝ)}
    {score : ℕ → GravitationalClassDensity} {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R W : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {α β lam : ℝ} {t : Fin 4}
    {K : Set (Fin 4 → ℝ)} {Test : Type*} [TopologicalSpace Test]
    {kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {core : Set Test}
    {H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {M : Test → ℝ}
    {δA : Test → ℕ → ℝ}
    (h : RenewalEinsteinCertification Ω score e ω R W T eL ωL α β lam t K kOf core H M δA)
    (hconst : ∀ i j, ∃ τ ∈ core, kOf τ = fun _ => symmUnit i j)
    (hloc : ∀ (φ : 𝓓(interiorOpens K, ℝ)) (i j : Fin 4), ∃ τ ∈ core,
      kOf τ = fun x => φ x • symmUnit i j) :
    ∃ RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ,
      (∃ K' : Set (Fin 4 → ℝ), IsCompact K' ∧ K ⊆ interior K' ∧ K' ⊆ Ω ∧
        IsDistributionalCurvature (interiorOpens K') ωL RL) ∧
      ∀ᵐ x, x ∈ interior K → ∀ i j, einsteinCosmologicalDensity (cosmologicalConstant β lam)
        (cfm eL x) (symmUnit i j) (rcf RL x) = 0 := by
  obtain ⟨-, -, K', hK', hKK', hK'Ω, RL, -, hid, -, -, -, hint, -, h0, -⟩ :=
    renewal_einstein_certification (Test := Test) h
  exact ⟨RL, ⟨K', hK', hKK', hK'Ω, hid⟩, ae_einsteinCosmologicalDensity_symmUnit_eq_zero
    (fun τ hτ => (hint τ hτ).2) h0 hconst hloc⟩

/-! ### Non-vacuity -/

/-- **Non-vacuity of `(E1)`–`(E5)`, full-connection route (with the amendment)**: on `Ω = ℝ⁴` and
any compact `K`, the flat Minkowski coframe, the zero connection, curvature, torsion and Cartan
writer, the Palatini score (`α = 0`, `β = 1`, `λ = 0`), the constant inverse-metric tests
(test type `Matrix`, core = all of them) with lifts `-½ k η`, and zero realized variations. -/
theorem renewalEinsteinCertification_flat (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) :
    RenewalEinsteinCertification ⊤ (fun _ => RenewalGeometry.palatiniDensity)
      (fun _ μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun _ _ _ => 0) (fun _ _ _ _ => 0)
      (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (fun μ _ => (Pi.single μ 1 : Fin 4 → ℝ))
      (fun _ _ => 0) 0 1 0 0 K (Test := Matrix (Fin 4) (Fin 4) ℝ) (fun k _ => k) Set.univ
      (fun k _ _ => metricTestGenerator minkowski 1 k)
      (fun k => ‖metricTestGenerator minkowski 1 k‖) (fun _ _ => 0) := by
  have P := renewalPalatiniHypotheses_flat
  have C := certifiedMetricTests_flat K
  exact
    { connection_lorentz := P.connection_lorentz
      torsion_rep := P.torsion_rep
      torsion_antisymm := P.torsion_antisymm
      torsion_L2 := P.torsion_L2
      e1_compact := hK
      e1_subset := Set.subset_univ K
      e1_firstVariation_vanish := fun _ _ => tendsto_const_nhds
      e1_lift_measurable := C.lift_measurable
      e1_lift_bounded := C.lift_bounded
      e1_lift_tendsto := C.lift_tendsto
      e2_classified := P.natural
      e2_firstVariationRemainder := C.firstVariationRemainder
      e3_holst_tendsto := P.holst_tendsto
      e3_palatini_tendsto := P.palatini_tendsto
      e3_volume_tendsto := P.volume_tendsto
      e3_palatini_ne_zero := P.palatini_ne_zero
      e3_euler_residual_tendsto := P.euler_residual_tendsto
      e3_cartan_floor := P.cartan_floor
      e4_coframe_L2 := P.coframe_L2
      e4_coframe_L6 := P.coframe_L6
      e4_coframe_oriented := P.coframe_oriented
      e4_limit_nondegenerate := P.limit_nondegenerate
      e5_curvature_L2 := P.curvature_L2
      e5_curvature_bound := P.curvature_bound
      e5_connection_route := Or.inl
        { connection_L2 := P.connection_L2
          spatialConnectionL3Bound := P.spatialConnectionL3Bound
          cartanCurvatureResidual := fun _ _ _ => by simp
          cartanIncidenceResidual := fun φ a b => by simp [curvaturePairing] } }

/-- **Non-vacuity of `(E1)`–`(E5)`, literal-link route**: the same flat data with zero limiting
curvature. -/
theorem renewalEinsteinCertification_flat_literalLink (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) :
    RenewalEinsteinCertification ⊤ (fun _ => RenewalGeometry.palatiniDensity)
      (fun _ μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun _ _ _ => 0) (fun _ _ _ _ => 0)
      (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (fun μ _ => (Pi.single μ 1 : Fin 4 → ℝ))
      (fun _ _ => 0) 0 1 0 0 K (Test := Matrix (Fin 4) (Fin 4) ℝ) (fun k _ => k) Set.univ
      (fun k _ _ => metricTestGenerator minkowski 1 k)
      (fun k => ‖metricTestGenerator minkowski 1 k‖) (fun _ _ => 0) := by
  have L := renewalPalatiniLiteralLinkHypotheses_flat
  exact
    { renewalEinsteinCertification_flat K hK with
      e5_connection_route := Or.inr ⟨fun _ _ _ => 0,
        { spatialConnectionL3Bound := L.spatialConnectionL3Bound
          connection_L2 := L.connection_L2
          connection_bound := L.connection_bound
          connection_limit_L2 := L.connection_limit_L2
          connection_weak := L.connection_weak
          spatial_strong := L.spatial_strong
          curvature_limit_L2 := L.curvature_limit_L2
          curvature_weak := L.curvature_weak
          curvature_identified := L.curvature_identified }⟩ }

/-- The main theorem applies to the flat certification. -/
example (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) :=
  renewal_einstein_certification (Test := Matrix (Fin 4) (Fin 4) ℝ)
    (renewalEinsteinCertification_flat K hK)


/-! ### Non-vacuity of the pointwise form -/

theorem continuous_metricTestGenerator_one :
    Continuous fun k : Matrix (Fin 4) (Fin 4) ℝ => metricTestGenerator minkowski 1 k := by
  unfold metricTestGenerator
  have h : Continuous fun k : Matrix (Fin 4) (Fin 4) ℝ => k * coframeMetric minkowski 1 :=
    Continuous.matrix_mul (continuous_id (X := Matrix (Fin 4) (Fin 4) ℝ))
      (continuous_const (y := coframeMetric minkowski 1))
  exact h.const_smul (-(1 / 2 : ℝ))

/-- The rich flat test core: test fields `k` paired with a bound `C` on their lift
`-½ k η`, measurable on `K`. -/
def flatFieldCore (K : Set (Fin 4 → ℝ)) :
    Set (((Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) × ℝ) :=
  {τ | AEStronglyMeasurable τ.1 (volume.restrict K) ∧
    ∀ x, ‖metricTestGenerator minkowski 1 (τ.1 x)‖ ≤ τ.2}

/-- At the flat solution, every bounded measurable test field is certified. -/
theorem certifiedMetricTests_flatFields (K : Set (Fin 4 → ℝ)) :
    CertifiedMetricTests K (fun _ => RenewalGeometry.palatiniDensity)
      (fun _ μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun _ _ _ _ => 0)
      (fun μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) Prod.fst (flatFieldCore K)
      (fun τ _ x => metricTestGenerator minkowski 1 (τ.1 x)) Prod.snd (fun _ _ => 0) := by
  have hcfm : ∀ x : Fin 4 → ℝ, cfm (fun μ (_ : Fin 4 → ℝ) => (Pi.single μ 1 : Fin 4 → ℝ)) x = 1 :=
    fun x => coframeMatrix_basis
  refine ⟨fun τ hτ _ => continuous_metricTestGenerator_one.comp_aestronglyMeasurable hτ.1,
    fun τ hτ _ => Eventually.of_forall fun x => hτ.2 x,
    fun _ _ => Eventually.of_forall fun x => by rw [hcfm]; exact tendsto_const_nhds,
    fun τ _ => ?_⟩
  have hP : ∀ n : ℕ, realizedPalatini K (fun μ (_ : Fin 4 → ℝ) => (Pi.single μ 1 : Fin 4 → ℝ))
      (fun x => metricTestGenerator minkowski 1 (τ.1 x)) (fun _ _ _ => 0) = 0 := fun n => by
    unfold realizedPalatini
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    simp only [rcf_zero]
    simp [palatiniVariation, PalatiniEinsteinAlgebra.pal4]
  refine tendsto_const_nhds.congr fun n => ?_
  simp only [classifiedVariationRemainder, holstCoeff_palatiniDensity, palatiniCoeff_palatiniDensity,
    volumeCoeff_palatiniDensity, hP n]
  ring

/-- **Non-vacuity of `renewal_einstein_certification_ae`**: the flat certification with the rich
core `flatFieldCore K` (all bounded measurable test fields) satisfies `(E1)`–`(E5)` and the
richness hypotheses (constant symmetric units and their smooth localizations). -/
theorem renewalEinsteinCertification_flat_ae (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) :
    ∃ RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ,
      (∃ K' : Set (Fin 4 → ℝ), IsCompact K' ∧ K ⊆ interior K' ∧ K' ⊆ ⊤ ∧
        IsDistributionalCurvature (interiorOpens K') (fun _ _ => 0) RL) ∧
      ∀ᵐ x, x ∈ interior K → ∀ i j, einsteinCosmologicalDensity (cosmologicalConstant 1 0)
        (cfm (fun μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) x) (symmUnit i j) (rcf RL x) = 0 := by
  have F := renewalEinsteinCertification_flat K hK
  have C := certifiedMetricTests_flatFields K
  have h : RenewalEinsteinCertification ⊤ (fun _ => RenewalGeometry.palatiniDensity)
      (fun _ μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun _ _ _ => 0) (fun _ _ _ _ => 0)
      (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (fun μ _ => (Pi.single μ 1 : Fin 4 → ℝ))
      (fun _ _ => 0) 0 1 0 0 K Prod.fst (flatFieldCore K)
      (fun τ _ x => metricTestGenerator minkowski 1 (τ.1 x)) Prod.snd (fun _ _ => 0) :=
    { connection_lorentz := F.connection_lorentz
      torsion_rep := F.torsion_rep
      torsion_antisymm := F.torsion_antisymm
      torsion_L2 := F.torsion_L2
      e1_compact := hK
      e1_subset := Set.subset_univ K
      e2_classified := F.e2_classified
      e3_holst_tendsto := F.e3_holst_tendsto
      e3_palatini_tendsto := F.e3_palatini_tendsto
      e3_volume_tendsto := F.e3_volume_tendsto
      e3_palatini_ne_zero := F.e3_palatini_ne_zero
      e3_euler_residual_tendsto := F.e3_euler_residual_tendsto
      e3_cartan_floor := F.e3_cartan_floor
      e4_coframe_L2 := F.e4_coframe_L2
      e4_coframe_L6 := F.e4_coframe_L6
      e4_coframe_oriented := F.e4_coframe_oriented
      e4_limit_nondegenerate := F.e4_limit_nondegenerate
      e5_curvature_L2 := F.e5_curvature_L2
      e5_curvature_bound := F.e5_curvature_bound
      e5_connection_route := F.e5_connection_route
      e1_firstVariation_vanish := fun _ _ => tendsto_const_nhds
      e1_lift_measurable := C.lift_measurable
      e1_lift_bounded := C.lift_bounded
      e1_lift_tendsto := C.lift_tendsto
      e2_firstVariationRemainder := C.firstVariationRemainder }
  refine renewal_einstein_certification_ae h (fun i j => ?_) (fun φ i j => ?_)
  · refine ⟨((fun _ => symmUnit i j), ‖metricTestGenerator minkowski 1 (symmUnit i j)‖),
      ⟨aestronglyMeasurable_const, fun _ => le_rfl⟩, rfl⟩
  · set f : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ := fun x => φ x • symmUnit i j
    have hf : Continuous f := φ.continuous.smul continuous_const
    have : PseudoMetrizableSpace (Matrix (Fin 4) (Fin 4) ℝ) :=
      inferInstanceAs (PseudoMetrizableSpace (Fin 4 → Fin 4 → ℝ))
    have hfs : HasCompactSupport (fun x => metricTestGenerator minkowski 1 (f x)) :=
      (φ.hasCompactSupport.smul_right (f' := fun _ => symmUnit i j)).comp_left
        (g := fun k => metricTestGenerator minkowski 1 k) (by simp [metricTestGenerator])
    obtain ⟨B, hB⟩ := (continuous_metricTestGenerator_one.comp hf).bounded_above_of_compact_support
      hfs
    exact ⟨(f, B), ⟨hf.aestronglyMeasurable, hB⟩, rfl⟩

end RenewalGeometry.RenewalEinstein
