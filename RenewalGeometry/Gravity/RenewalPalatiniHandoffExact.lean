/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.PhysicalLiftVariationLimit
import RenewalGeometry.Gravity.MollifiedFirstBianchi
import RenewalGeometry.Gravity.VariationTransferExact
import RenewalGeometry.Gravity.PalatiniTorsionCoefficientModelExact
import RenewalGeometry.Lorentz.GravitationalClassDensity

/-!
# The localized renewal–Palatini handoff
  (`thm:supp-renewal-palatini`, `eq:supp-phv-classification`, `eq:supp-einstein-insertion`;
  emergent-spacetime manuscript, supplement)

This file assembles `thm:supp-renewal-palatini` as one theorem from the machinery of
`LorentzNaturalBivectorClassificationExact` / `GravitationalClassDensity` (classification),
`PalatiniTorsionCoefficientModelExact` (Cartan map, `P_{α,β}` and its inverse),
`DistributionalTorsionLimit` (torsion passage), `DistributionalCurvatureCompactness`
(`thm:supp-curvature-compactness`), `MollifiedFirstBianchi` (first Bianchi identity at limit
regularity and the integrated Einstein insertion), `LimitEinsteinInsertion` (Levi-Civita
uniqueness), `VariationTransferExact` (`lem:supp-variation-transfer`) and
`PhysicalLiftVariationLimit` (the `(E1)` passage of the realized metric-test variations).

## The hypothesis packets

`RenewalPalatiniCommon` collects the hypotheses common to both connection routes;
`RenewalPalatiniHypotheses` (full-connection route, `thm:supp-curvature-compactness`) and
`RenewalPalatiniLiteralLinkHypotheses` (literal-link route, `thm:main-literal-link-compactness`)
extend it.  On an open cylinder `Ω ⊆ ℝ⁴`, for a regulator sequence `X = n` of common-cylinder
interpolants:

* `natural`: the regulator scores are Lorentz-natural members of the local gravitational class
  (`def:main-gravitational-class`, real Lorentz naturality, scalar residual commutant,
  represented determinant volume — the `GravitationalClassDensity` model);
* `holst_tendsto`, `palatini_tendsto`, `volume_tendsto`, `palatini_ne_zero`: the calibrated
  coefficients converge, `(α_X, β_X, λ_X) → (α, β, λ)`, `β ≠ 0`;
* `coframe_L2`, `coframe_L6`: `eq:supp-coframe-l2-l6` on every compact;
  `coframe_oriented`: the regulator coframes are oriented (the class is defined on oriented
  coframes); `limit_nondegenerate`: nondegeneracy of the limiting coframe;
* `connection_lorentz`: the regulator connections are metric-compatible Lorentz connections;
  `connection_L2`: full-connection route, `ω_X → ω` strongly in `L²_loc`
  (`ass:main-connection-compactness` after extraction, `eq:main-identified-curvature-hypotheses`);
* **`spatialConnectionL3Bound` (AMENDMENT)**: a uniform `L³_loc` bound on the spatial connection
  interpolants (all coefficients except the temporal one `t`).  This is NOT in the manuscript's
  hypothesis list of `thm:supp-renewal-palatini`; it is needed for the first Bianchi identity
  `R ∧ e = 0` of the limit at the available regularity (`MollifiedFirstBianchi`), which the
  manuscript's one-line argument ("the first Bianchi identity removes the Holst coframe
  variation") uses without justification at `L²` connection regularity.  Both concrete
  realizations of `(E5)` in the manuscript supply it: the Hodge–temporal budget
  `eq:main-connection-hodge-budget` contains `‖A_h‖_{L⁴}²`, and the literal-link route has the
  `L^{10/3}` bound `eq:supp-literal-integrability`;
* `torsion_rep`, `torsion_antisymm`, `torsion_L2`: the regulator torsion two-form
  `T_X = d e_X + ω_X ∧ e_X` is represented by an `L²_loc` function;
  `cartan_floor`: the uniform Cartan inverse of `thm:supp-palatini-torsion` (a uniform lower
  singular-value bound `κ ‖v‖ ≤ ‖𝒦_{e_X} v‖` on antisymmetric torsion arrays);
  `euler_residual_tendsto`: the spinless connection Euler residual
  `D(P_{α_X,β_X} B_X) = P_{α_X,β_X} 𝒦_{e_X}(T_X)` tends to zero in `L²_loc`;
* `curvature_L2`, `curvature_bound`: the curvature certificate output
  `sup_X ‖R_X‖_{L²(K)} < ∞` (`thm:main-curvature-propagation`, `thm:main-discrete-curvature`);
  `curvature_identification` (full-connection route): `R_X - [d_dist ω_X + ω_X ∧ ω_X] → 0`
  in distributions (`eq:supp-curvature-identification`);
* literal-link route instead: the connection coefficients are bounded and converge weakly in
  `L²_loc`, the spatial ones strongly, and the curvature records converge weakly to a limit `RL`
  identified as `dω + ω ∧ ω` (the output of the literal-link identification from the electric
  and magnetic records).

The physical test lift `(E1)` of an inverse-metric test `k` on a compact `K` is given by
coefficient tensors `H_X` (`δe_X = e_X H_X`), uniformly bounded on `K` and converging almost
everywhere on `K` to the limit lift `metricTestGenerator η e k = -½ k g` of `(e, k)`.  The
physical first-variation remainder condition `eq:main-first-variation-reduction` is
`classifiedVariationRemainder δA δS_H δS_P δV α_X β_X λ_X → 0`, with the realized variations
`δS_H = ∫_K δ_{e_X H_X} L_H(e_X, R_X)`, `δS_P = ∫_K δ_{e_X H_X} L_P(e_X, R_X)`,
`δV = ∫_K det e_X · tr H_X`.

## Main results

* `RenewalPalatiniCommon.classified`: the regulator scores and their limit have the
  classified form `α L_H + β L_P + λ L_vol` (`eq:supp-phv-classification`);
* `RenewalPalatiniCommon.tendsto_eLpNorm_torsion`: the represented regulator torsion tends to
  zero in `L²_loc` (uniform Cartan inverse + vanishing Euler residual);
  `RenewalPalatiniHypotheses.isTorsionFree`, `RenewalPalatiniLiteralLinkHypotheses.isTorsionFree`:
  limiting torsion vanishes (strong, resp. weak temporal, connection convergence);
* `tendsto_firstVariation_einstein`: route-independent core — along an identified weak curvature
  limit, `(E1)` passage (`tendsto_liftVariations`), variation transfer
  (`tendsto_completeVariation_of_classified`) and the Einstein insertion at limit regularity
  (`integral_classifiedMetricVariation_of_metricCompatible`, using the amendment);
* `renewal_palatini_handoff`: **`thm:supp-renewal-palatini`** (full-connection route): the
  classification, vanishing limiting torsion, and for every compact `K ⊆ Ω` and every lifted
  metric test with the remainder condition, the convergence of the complete metric first
  variations to `β ∫_K √(-g) k^{γb} (G_{bγ} + Λ g_{bγ})`, `Λ = -λ/(2β)`, `χ = β ≠ 0`
  (`eq:supp-einstein-insertion`), where `G` is the Einstein tensor of the coordinate curvature of
  the limit connection, which is torsion-free, metric compatible and the unique such
  (Levi-Civita) connection of the limit coframe.  The whole sequence converges: the identified
  curvature is determined by the limit connection (`ae_eq_of_isDistributionalCurvature`), so
  every subsequence has a further subsequence with the same limit;
* `renewal_palatini_handoff_literalLink`: the same conclusions on the literal-link route;
* `renewalPalatiniHypotheses_flat`, `renewalPalatiniLiteralLinkHypotheses_flat`: non-vacuity
  (flat Minkowski coframe, zero connection, the Palatini score, including the amendment).

Disclosed renderings: regulators are represented by common-cylinder interpolant fields on `Ω`;
the physical lift is encoded by its coefficient tensor relative to the coframe
(`δe_X = e_X H_X`); the regulator Euler residual is the represented `P_{α,β} 𝒦_e(T)` (equal to
`D(P_{α,β} B)` for `C¹` fields, `PalatiniTorsionModel.eulerResidual_eq`); the curvature
certificates enter through their output (uniform `L²` bounds); `G` is the Einstein tensor of the
coordinate curvature of the identified limit curvature (agreement with the classical Riemann
tensor of `g` for `C²` coframes is the classical tetrad computation, not formalised).
-/

open MeasureTheory Filter Topology ENNReal TopologicalSpace Set
open scoped NNReal Distributions Matrix

noncomputable section

namespace RenewalGeometry.RenewalPalatiniHandoff

open DistributionalTorsion DistributionalCurvature DistributionalBianchi MollifiedBianchi
  LimitEinsteinInsertion PalatiniEinsteinAlgebra

set_option linter.unusedSectionVars false

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ### Classified coefficients of a regulator score -/

/-- The Holst coefficient of a member of the gravitational class (its `metricPairing` part). -/
def holstCoeff (D : GravitationalClassDensity) : ℝ := D.pairing (0, 0) (0, 0)

/-- The Palatini coefficient of a member of the gravitational class (its `epsilonPairing`
part). -/
def palatiniCoeff (D : GravitationalClassDensity) : ℝ := D.pairing (0, 0) (1, 0)

/-- The volume coefficient of a member of the gravitational class (`λ` in `λ det`). -/
def volumeCoeff (D : GravitationalClassDensity) : ℝ := D.volume (Pi.basisFun ℝ (Fin 4))

/-- **Classification with explicit coefficients** (`thm:main-gravitational-classification`):
a Lorentz-natural member of the class is `α L_H + β L_P + λ L_vol` with
`(α, β, λ) = (holstCoeff, palatiniCoeff, volumeCoeff)`. -/
theorem eq_ofCoefficients (D : GravitationalClassDensity) (hD : D.IsLorentzNatural) :
    D = GravitationalClassDensity.ofCoefficients (holstCoeff D) (palatiniCoeff D)
      (volumeCoeff D) := by
  obtain ⟨c, hc, -⟩ := D.classification hD
  have h1 : holstCoeff D = c.1 := by
    rw [holstCoeff, hc]; simp [metricPairing, epsilonPairing, BivectorRotationCommutant.scalarBlocks]
  have h2 : palatiniCoeff D = c.2.1 := by
    rw [palatiniCoeff, hc]; simp [metricPairing, epsilonPairing, BivectorRotationCommutant.scalarBlocks]
  have h3 : volumeCoeff D = c.2.2 := by
    rw [volumeCoeff, hc]
    simp only [GravitationalClassDensity.ofCoefficients_volume, AlternatingMap.smul_apply,
      Module.Basis.det_self, smul_eq_mul, mul_one]
  rw [h1, h2, h3]; exact hc

/-! ### Represented torsion and the connection Euler residual -/

/-- The internal coframe array `E^I_μ = e_μ(x)^I` (convention of
`PalatiniTorsionModel.cartan`). -/
def coframeArr (e : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun I μ => e μ x I

/-- The torsion array `T^I_{ab} = T_{ab}(x)^I` of a represented torsion two-form. -/
def torsionArr (T : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)) (x : Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun I a b => T a b x I

/-- The represented spinless connection Euler residual
`D(P_{α,β} B) = P_{α,β} 𝒦_e(T)` (`PalatiniTorsionModel.eulerResidual_eq` for `C¹` fields). -/
def eulerResidualRep (α β : ℝ) (e : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (T : Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)) (x : Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  PalatiniTorsionModel.palatiniApply α β
    (PalatiniTorsionModel.cartan (coframeArr e x) (torsionArr T x))

/-! ### The hypothesis packet -/

/-- The hypotheses of `thm:supp-renewal-palatini` common to both connection routes, with the
amendment `spatialConnectionL3Bound` (see the module docstring). -/
structure RenewalPalatiniCommon (Ω : Opens (Fin 4 → ℝ))
    (score : ℕ → GravitationalClassDensity)
    (e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)) (α β lam : ℝ) (t : Fin 4) : Prop where
  /-- Polynomial local class, real Lorentz naturality, scalar residual commutant, represented
  determinant volume. -/
  natural : ∀ n, (score n).IsLorentzNatural
  /-- Calibrated coefficient limits. -/
  holst_tendsto : Tendsto (fun n => holstCoeff (score n)) atTop (𝓝 α)
  palatini_tendsto : Tendsto (fun n => palatiniCoeff (score n)) atTop (𝓝 β)
  volume_tendsto : Tendsto (fun n => volumeCoeff (score n)) atTop (𝓝 lam)
  palatini_ne_zero : β ≠ 0
  /-- `eq:supp-coframe-l2-l6`. -/
  coframe_L2 : L2LocTendsto Ω e eL
  coframe_L6 : ∀ c (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (e n c) 6 (volume.restrict C) ≤ M
  /-- Oriented regulator coframes (the class is defined on oriented coframes). -/
  coframe_oriented : ∀ n, ∀ᵐ x, x ∈ Ω → 0 < (cfm (e n) x).det
  /-- Nondegeneracy of the limiting coframe. -/
  limit_nondegenerate : ∀ᵐ x, x ∈ Ω → (cfm eL x).det ≠ 0
  /-- Metric-compatible Lorentz connections. -/
  connection_lorentz : ∀ n, ∀ᵐ x, x ∈ Ω → ∀ a,
    (minkowski * ω n a x)ᵀ = -(minkowski * ω n a x)
  /-- **AMENDMENT** to the manuscript's hypothesis list: a uniform `L³_loc` bound on the spatial
  connection interpolants (supplied by `eq:main-connection-hodge-budget` and by
  `eq:supp-literal-integrability`). -/
  spatialConnectionL3Bound : ∀ a, a ≠ t → ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (ω n a) 3 (volume.restrict C) ≤ M
  /-- The regulator torsion two-form is represented by `T`. -/
  torsion_rep : ∀ n (φ : 𝓓(Ω, ℝ)) a b,
    torsionPairing matAct (e n) (ω n) φ a b = ∫ x, φ x • T n a b x
  torsion_antisymm : ∀ n a b, ∀ᵐ x, x ∈ Ω → T n b a x = -T n a b x
  torsion_L2 : ∀ n a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (T n a b) 2 (volume.restrict C)
  /-- Uniform Cartan inverse (`thm:supp-palatini-torsion`). -/
  cartan_floor : ∃ κ : ℝ, 0 < κ ∧ ∀ n, ∀ᵐ x, x ∈ Ω →
    ∀ v : Fin 4 → Fin 4 → Fin 4 → ℝ, (∀ I μ ν, v I μ ν = -v I ν μ) →
      κ * ‖v‖ ≤ ‖PalatiniTorsionModel.cartan (coframeArr (e n) x) v‖
  /-- The spinless connection Euler residual tends to zero. -/
  euler_residual_tendsto : ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    Tendsto (fun n => eLpNorm (eulerResidualRep (holstCoeff (score n)) (palatiniCoeff (score n))
      (e n) (T n)) 2 (volume.restrict C)) atTop (𝓝 0)
  /-- Curvature certificate output: uniform `L²` bounds on compacts. -/
  curvature_L2 : ∀ n a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (R n a b) 2 (volume.restrict C)
  curvature_bound : ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ n a b, eLpNorm (R n a b) 2 (volume.restrict C) ≤ B

/-- The hypotheses of `thm:supp-renewal-palatini` on the full-connection route
(`thm:supp-curvature-compactness`): the common packet (including the amendment
`spatialConnectionL3Bound`), strong `L²_loc` connection convergence and the distributional
curvature identification `eq:supp-curvature-identification`. -/
structure RenewalPalatiniHypotheses (Ω : Opens (Fin 4 → ℝ))
    (score : ℕ → GravitationalClassDensity)
    (e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (α β lam : ℝ) (t : Fin 4) : Prop
    extends RenewalPalatiniCommon Ω score e ω R T eL α β lam t where
  /-- Full-connection route: strong `L²_loc` connection convergence. -/
  connection_L2 : L2LocTendsto Ω ω ωL
  /-- `eq:supp-curvature-identification`. -/
  curvature_identification : ∀ (φ : 𝓓(Ω, ℝ)) a b,
    Tendsto (fun n => (∫ x, φ x • R n a b x) - curvaturePairing (ω n) φ a b) atTop (𝓝 0)

/-! ### Generic limit lemmas -/

section Generic

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A strong `L^p` limit (`1 ≤ p`) of almost-everywhere vanishing functions vanishes almost
everywhere. -/
theorem _root_.RenewalGeometry.LpTendsto.ae_eq_zero_of_ae_eq_zero {p : ℝ≥0∞} (hp : 1 ≤ p) {u : ℕ → X → E} {u' : X → E}
    (hu : LpTendsto ν p u u') (h0 : ∀ n, u n =ᵐ[ν] 0) : u' =ᵐ[ν] 0 := by
  have heq : ∀ n, eLpNorm u' p ν = eLpNorm (u n - u') p ν := fun n => by
    rw [eLpNorm_sub_comm]
    refine eLpNorm_congr_ae ?_
    filter_upwards [h0 n] with x hx
    simp [hx]
  have hlim : Tendsto (fun _ : ℕ => eLpNorm u' p ν) atTop (𝓝 0) := by
    simpa only [← heq] using hu.tendsto
  have hz : eLpNorm u' p ν = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  exact (eLpNorm_eq_zero_iff hu.memLp_lim.1 (by positivity)).1 hz

/-- Linear constraints holding almost everywhere pass to strong limits. -/
theorem _root_.RenewalGeometry.LpTendsto.ae_map_eq_zero {p : ℝ≥0∞} (hp : 1 ≤ p) (L : E →L[ℝ] F) {u : ℕ → X → E}
    {u' : X → E} (hu : LpTendsto ν p u u') (h0 : ∀ n, ∀ᵐ x ∂ν, L (u n x) = 0) :
    ∀ᵐ x ∂ν, L (u' x) = 0 :=
  (hu.clm_comp L).ae_eq_zero_of_ae_eq_zero hp fun n => h0 n

/-- Strong convergence is inherited by smaller measures. -/
theorem _root_.RenewalGeometry.LpTendsto.mono_measure' {p : ℝ≥0∞} {ν' : Measure X} (hle : ν' ≤ ν) {u : ℕ → X → E}
    {u' : X → E} (hu : LpTendsto ν p u u') : LpTendsto ν' p u u' :=
  ⟨fun n => (hu.memLp n).mono_measure hle, hu.memLp_lim.mono_measure hle,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu.tendsto (fun n => bot_le)
      fun n => eLpNorm_mono_measure _ hle⟩

/-- Strong convergence is preserved along sequences tending to infinity. -/
theorem _root_.RenewalGeometry.LpTendsto.comp_tendsto {p : ℝ≥0∞} {u : ℕ → X → E} {u' : X → E} (hu : LpTendsto ν p u u')
    {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) : LpTendsto ν p (fun n => u (ns n)) u' :=
  ⟨fun n => hu.memLp (ns n), hu.memLp_lim, hu.tendsto.comp hns⟩

end Generic

section GenericCurvature

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- **The identified curvature is determined by the connection**: two `L²_loc` curvature fields
both equal to `dω + ω ∧ ω` in distributions on `U` agree almost everywhere on `U`. -/
theorem ae_eq_of_isDistributionalCurvature {U : Opens (Fin 4 → ℝ)}
    {ω : Fin 4 → (Fin 4 → ℝ) → A} {R₁ R₂ : Fin 4 → Fin 4 → (Fin 4 → ℝ) → A}
    (h₁ : IsDistributionalCurvature U ω R₁) (h₂ : IsDistributionalCurvature U ω R₂)
    (hR₁ : ∀ a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ U → MemLp (R₁ a b) 2 (volume.restrict C))
    (hR₂ : ∀ a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ U → MemLp (R₂ a b) 2 (volume.restrict C))
    (a b : Fin 4) : ∀ᵐ x, x ∈ U → R₁ a b x = R₂ a b x := by
  have hint : ∀ (R : Fin 4 → Fin 4 → (Fin 4 → ℝ) → A),
      (∀ a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ U → MemLp (R a b) 2 (volume.restrict C)) →
      ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ U → IntegrableOn (R a b) C volume :=
    fun R hR C hC hCU => by
      have : IsFiniteMeasure (volume.restrict C) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
      exact (hR a b C hC hCU).integrable (by norm_num)
  have hloc : LocallyIntegrableOn (fun x => R₁ a b x - R₂ a b x) U := by
    rw [locallyIntegrableOn_iff U.isOpen.isLocallyClosed]
    intro C hCU hC
    exact (hint R₁ hR₁ C hC hCU).sub (hint R₂ hR₂ C hC hCU)
  have hz := U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgs => by
    set ψ : 𝓓(U, ℝ) := ⟨g, hg, hgc, hgs⟩
    have hzg : ∀ x, x ∉ tsupport g → g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
    have i₁ := integrable_smul_of_memLp_on hg.continuous hgc hzg (by norm_num) (hR₁ a b _ hgc hgs)
    have i₂ := integrable_smul_of_memLp_on hg.continuous hgc hzg (by norm_num) (hR₂ a b _ hgc hgs)
    have e₁ : ∫ x, g x • R₁ a b x = curvaturePairing ω g a b := h₁ ψ a b
    have e₂ : ∫ x, g x • R₂ a b x = curvaturePairing ω g a b := h₂ ψ a b
    simp only [smul_sub]
    rw [integral_sub i₁ i₂, e₁, e₂, sub_self]
  filter_upwards [hz] with x hx hxU
  exact sub_eq_zero.1 (hx hxU)

end GenericCurvature

/-! ### The torsion clause -/

section Torsion

variable {Ω : Opens (Fin 4 → ℝ)} {score : ℕ → GravitationalClassDensity}
  {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {α β lam : ℝ} {t : Fin 4}

open PalatiniTorsionModel in
/-- The internal Hodge star acting on three-form arrays, as a continuous linear map. -/
def starApplyCLM :
    (Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) →L[ℝ] (Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun C I J μ ν ρ => capply starC (fun A B => C A B μ ν ρ) I J
      map_add' := fun C D => by
        funext I J μ ν ρ
        simp only [capply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c C => by
        funext I J μ ν ρ
        simp only [capply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => by ring }

open PalatiniTorsionModel in
theorem inverseApplyCLM_eq (a b : ℝ) :
    inverseApplyCLM a b = (a ^ 2 + b ^ 2)⁻¹ • (a • ContinuousLinearMap.id ℝ _ - b • starApplyCLM) := by
  ext C I J μ ν ρ
  have h := congrFun (congrFun (capply_inverseC a b (fun A B => C A B μ ν ρ)) I) J
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  exact h

open PalatiniTorsionModel in
/-- **Torsion clause, quantitative form** (`thm:supp-palatini-torsion` finite estimate, passed to
the limit): under the uniform Cartan inverse, the represented regulator torsion tends to zero in
`L²_loc` when the connection Euler residual does and `β ≠ 0`. -/
theorem RenewalPalatiniCommon.tendsto_eLpNorm_torsion
    (h : RenewalPalatiniCommon Ω score e ω R T eL α β lam t) (a b : Fin 4)
    (C : Set (Fin 4 → ℝ)) (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
    Tendsto (fun n => eLpNorm (T n a b) 2 (volume.restrict C)) atTop (𝓝 0) := by
  obtain ⟨κ, hκ, hfl⟩ := h.cartan_floor
  set αs := fun n => holstCoeff (score n)
  set βs := fun n => palatiniCoeff (score n)
  have hs : α ^ 2 + β ^ 2 ≠ 0 := by
    have := h.palatini_ne_zero; positivity
  have hss : Tendsto (fun n => αs n ^ 2 + βs n ^ 2) atTop (𝓝 (α ^ 2 + β ^ 2)) :=
    (h.holst_tendsto.pow 2).add (h.palatini_tendsto.pow 2)
  have hev : ∀ᶠ n in atTop, αs n ^ 2 + βs n ^ 2 ≠ 0 := hss.eventually_ne hs
  have hinv : Tendsto (fun n => inverseApplyCLM (αs n) (βs n)) atTop
      (𝓝 (inverseApplyCLM α β)) := by
    simp only [inverseApplyCLM_eq]
    exact (hss.inv₀ hs).smul ((h.holst_tendsto.smul tendsto_const_nhds).sub
      (h.palatini_tendsto.smul tendsto_const_nhds))
  have hc : Tendsto (fun n => ENNReal.ofReal (κ⁻¹ * ‖inverseApplyCLM (αs n) (βs n)‖)) atTop
      (𝓝 (ENNReal.ofReal (κ⁻¹ * ‖inverseApplyCLM α β‖))) :=
    ENNReal.tendsto_ofReal (hinv.norm.const_mul _)
  have hmeas : MeasurableSet C := hC.isClosed.measurableSet
  -- pointwise estimate
  have hpt : ∀ᶠ n in atTop, ∀ᵐ x ∂(volume.restrict C), ‖T n a b x‖ ≤
      (κ⁻¹ * ‖inverseApplyCLM (αs n) (βs n)‖) *
        ‖eulerResidualRep (αs n) (βs n) (e n) (T n) x‖ := by
    filter_upwards [hev] with n hn
    have hanti : ∀ᵐ x, x ∈ Ω → ∀ a b, T n b a x = -T n a b x := by
      have : ∀ᵐ x, ∀ a b : Fin 4, x ∈ Ω → T n b a x = -T n a b x := by
        simp only [ae_all_iff]; exact h.torsion_antisymm n
      filter_upwards [this] with x hx hxΩ a b using hx a b hxΩ
    refine (ae_restrict_iff' hmeas).2 ?_
    filter_upwards [hfl n, hanti] with x hx hxa hxC
    have hxΩ := hCΩ hxC
    set tA := torsionArr (T n) x
    have htA : ∀ I μ ν, tA I μ ν = -tA I ν μ := fun I μ ν => by
      simp only [tA, torsionArr, hxa hxΩ μ ν, Pi.neg_apply, neg_neg]
    have hK : cartan (coframeArr (e n) x) tA =
        inverseApplyCLM (αs n) (βs n) (eulerResidualRep (αs n) (βs n) (e n) (T n) x) := by
      rw [eulerResidualRep]
      exact (inverseApply_palatiniApply_cartan hn _ _).symm
    have h1 := hx hxΩ tA htA
    rw [hK] at h1
    have h2 := (inverseApplyCLM (αs n) (βs n)).le_opNorm
      (eulerResidualRep (αs n) (βs n) (e n) (T n) x)
    have h3 : ‖T n a b x‖ ≤ ‖tA‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun I => ?_
      calc ‖T n a b x I‖ = ‖tA I a b‖ := rfl
        _ ≤ ‖tA I a‖ := norm_le_pi_norm (tA I a) b
        _ ≤ ‖tA I‖ := norm_le_pi_norm (tA I) a
        _ ≤ ‖tA‖ := norm_le_pi_norm tA I
    have h4 : ‖tA‖ ≤ κ⁻¹ * (‖inverseApplyCLM (αs n) (βs n)‖ *
        ‖eulerResidualRep (αs n) (βs n) (e n) (T n) x‖) := by
      rw [le_inv_mul_iff₀ hκ]; linarith
    calc ‖T n a b x‖ ≤ ‖tA‖ := h3
      _ ≤ _ := h4
      _ = _ := by ring
  have hle : ∀ᶠ n in atTop, eLpNorm (T n a b) 2 (volume.restrict C) ≤
      ENNReal.ofReal (κ⁻¹ * ‖inverseApplyCLM (αs n) (βs n)‖) *
        eLpNorm (eulerResidualRep (αs n) (βs n) (e n) (T n)) 2 (volume.restrict C) := by
    filter_upwards [hpt] with n hn
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hn 2
  have hprod := ENNReal.Tendsto.mul hc (Or.inr ENNReal.zero_ne_top)
    (h.euler_residual_tendsto C hC hCΩ) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hprod
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod
    (Eventually.of_forall fun n => bot_le) hle

/-- **Limiting torsion vanishes** (torsion clause of `thm:supp-renewal-palatini`, full-connection
route): the tested torsion residuals tend to zero, and the strong `L²_loc` limits pass through the
distributional torsion. -/
theorem RenewalPalatiniHypotheses.isTorsionFree
    (h : RenewalPalatiniHypotheses Ω score e ω R T eL ωL α β lam t) :
    IsTorsionFree matAct Ω eL ωL := by
  refine isTorsionFree_of_tendsto matAct h.coframe_L2 h.connection_L2 fun φ a b => ?_
  set C := tsupport (φ : (Fin 4 → ℝ) → ℝ)
  have hC : IsCompact C := φ.hasCompactSupport
  have hCΩ : C ⊆ Ω := φ.tsupport_subset
  have : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hz0 : ∀ x, x ∉ C → φ x = 0 := fun x hx => test_eq_zero_off φ hx
  obtain ⟨M0, hM0⟩ := exists_bound_of_eq_zero_off φ.continuous hC hz0
  have hT := tendsto_integral_smul_of_L2' (V := Fin 4 → ℝ) φ.continuous.aestronglyMeasurable hM0
    (fun n => h.torsion_L2 n a b C hC hCΩ) (MemLp.zero' (ε := Fin 4 → ℝ))
    ((h.toRenewalPalatiniCommon.tendsto_eLpNorm_torsion a b C hC hCΩ).congr fun n => by congr 1; funext x; simp)
  simp only [smul_zero, integral_zero] at hT
  refine hT.congr fun n => ?_
  rw [h.torsion_rep n φ a b, integral_test_eq_setIntegral hz0]

end Torsion

/-! ### The classification clause -/

/-- **`eq:supp-phv-classification`**: every regulator score is `α_X L_H + β_X L_P + λ_X L_vol`
with its classified coefficients, and the scores converge to the classified limit
`α L_H + β L_P + λ L_vol` (pairing and volume parts). -/
theorem RenewalPalatiniCommon.classified {Ω : Opens (Fin 4 → ℝ)}
    {score : ℕ → GravitationalClassDensity} {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {α β lam : ℝ} {t : Fin 4}
    (h : RenewalPalatiniCommon Ω score e ω R T eL α β lam t) :
    (∀ n, score n = GravitationalClassDensity.ofCoefficients (holstCoeff (score n))
      (palatiniCoeff (score n)) (volumeCoeff (score n))) ∧
    Tendsto (fun n => (score n).pairing) atTop
      (𝓝 (GravitationalClassDensity.ofCoefficients α β lam).pairing) ∧
    ∀ v : Fin 4 → Fin 4 → ℝ, Tendsto (fun n => (score n).volume v) atTop
      (𝓝 ((GravitationalClassDensity.ofCoefficients α β lam).volume v)) := by
  have hc := fun n => eq_ofCoefficients (score n) (h.natural n)
  refine ⟨hc, ?_, fun v => ?_⟩
  · have : (fun n => (score n).pairing) = fun n =>
        holstCoeff (score n) • metricPairing + palatiniCoeff (score n) • epsilonPairing := by
      funext n; conv_lhs => rw [hc n]
      rfl
    rw [this, GravitationalClassDensity.ofCoefficients_pairing]
    exact (h.holst_tendsto.smul tendsto_const_nhds).add (h.palatini_tendsto.smul tendsto_const_nhds)
  · have : (fun n => (score n).volume v) = fun n =>
        volumeCoeff (score n) * (Pi.basisFun ℝ (Fin 4)).det v := by
      funext n; conv_lhs => rw [hc n]
      rfl
    rw [this, GravitationalClassDensity.ofCoefficients_volume, AlternatingMap.smul_apply,
      smul_eq_mul]
    exact h.volume_tendsto.mul tendsto_const_nhds

/-! ### Metric compatibility and orientation of the limit -/

section LimitProperties

attribute [local instance] RenewalGeometry.fact_one_le_four RenewalGeometry.holderTriple_four_four_two

variable {Ω : Opens (Fin 4 → ℝ)} {score : ℕ → GravitationalClassDensity}
  {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {α β lam : ℝ} {t : Fin 4}

/-- The metric-compatibility defect `(η M)ᵀ + η M` as a continuous linear map. -/
def compatCLM : Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (minkowski * M)ᵀ + minkowski * M
      map_add' := fun M N => by
        simp only [Matrix.mul_add, Matrix.transpose_add]; abel
      map_smul' := fun c M => by
        simp only [Matrix.mul_smul, Matrix.transpose_smul, RingHom.id_apply, smul_add] }

theorem compatCLM_apply (M : Matrix (Fin 4) (Fin 4) ℝ) :
    compatCLM M = (minkowski * M)ᵀ + minkowski * M := rfl

theorem _root_.RenewalGeometry.DistributionalTorsion.L2LocTendsto.lpTendsto {E : Type*} [NormedAddCommGroup E] {U : Opens (Fin 4 → ℝ)}
    {u : ℕ → Fin 4 → (Fin 4 → ℝ) → E} {u' : Fin 4 → (Fin 4 → ℝ) → E} (h : L2LocTendsto U u u')
    (a : Fin 4) {C : Set (Fin 4 → ℝ)} (hC : IsCompact C) (hCU : C ⊆ U) :
    LpTendsto (volume.restrict C) 2 (fun n => u n a) (u' a) :=
  ⟨fun n => h.memLp n a C hC hCU, h.memLp_lim a C hC hCU, h.tendsto a C hC hCU⟩

/-- **The limit connection is metric compatible** (`so(1,3)`-valued) almost everywhere on every
compact of the cylinder: a linear constraint passes to strong `L²` limits. -/
theorem RenewalPalatiniHypotheses.ae_compat
    (h : RenewalPalatiniHypotheses Ω score e ω R T eL ωL α β lam t) (C : Set (Fin 4 → ℝ))
    (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
    ∀ᵐ x ∂(volume.restrict C), ∀ a, (minkowski * ωL a x)ᵀ = -(minkowski * ωL a x) := by
  have hmeas : MeasurableSet C := hC.isClosed.measurableSet
  have hone : ∀ a, ∀ᵐ x ∂(volume.restrict C), compatCLM (ωL a x) = 0 := fun a => by
    refine (h.connection_L2.lpTendsto a hC hCΩ).ae_map_eq_zero (by norm_num) compatCLM
      fun n => ?_
    refine (ae_restrict_iff' hmeas).2 ?_
    filter_upwards [h.connection_lorentz n] with x hx hxC
    show (minkowski * ω n a x)ᵀ + minkowski * ω n a x = 0
    rw [hx (hCΩ hxC) a, neg_add_cancel]
  have hall : ∀ᵐ x ∂(volume.restrict C), ∀ a, compatCLM (ωL a x) = 0 := ae_all_iff.2 hone
  filter_upwards [hall] with x hx a
  have h0 : (minkowski * ωL a x)ᵀ + minkowski * ωL a x = 0 := hx a
  exact eq_neg_of_add_eq_zero_left h0

/-- **The limit coframe is oriented** almost everywhere on every compact: the determinants converge
in `L¹` (`L⁴` coframe convergence from `eq:supp-coframe-l2-l6`), the regulator determinants are
positive, and the limit is nondegenerate. -/
theorem RenewalPalatiniCommon.ae_det_pos
    (h : RenewalPalatiniCommon Ω score e ω R T eL α β lam t) (C : Set (Fin 4 → ℝ))
    (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
    ∀ᵐ x ∂(volume.restrict C), 0 < (cfm eL x).det := by
  have : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hmeas : MeasurableSet C := hC.isClosed.measurableSet
  have hc4 : ∀ μ, LpTendsto (volume.restrict C) 4 (fun n => e n μ) (eL μ) := fun μ => by
    obtain ⟨M, hM, hb⟩ := h.coframe_L6 μ C hC hCΩ
    exact (lpTendsto_four_of_two_six (h.coframe_L2.lpTendsto μ hC hCΩ) hM hb).1
  have hE4 : LpTendsto (volume.restrict C) 4 (fun n => cfm (e n)) (cfm eL) := by
    have := LpTendsto.finset_sum Finset.univ fun μ _ => (hc4 μ).clm_comp (colEmbed μ)
    refine this.congr (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact (cfm_eq_sum (e n) x).symm
    · exact (cfm_eq_sum eL x).symm
  have hP := LpTendsto.bilin (r := 2) tens hE4 hE4
  have hQ := LpTendsto.bilin (r := 1) detTwo hP hP
  have hD : LpTendsto (volume.restrict C) 1 (fun n x => (cfm (e n) x).det)
      (fun x => (cfm eL x).det) :=
    hQ.congr (fun n => Eventually.of_forall fun x => (det_eq_detTwo _).symm)
      (Eventually.of_forall fun x => (det_eq_detTwo _).symm)
  have hm : TendstoInMeasure (volume.restrict C) (fun n x => (cfm (e n) x).det) atTop
      (fun x => (cfm eL x).det) :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun n => (hD.memLp n).1) hD.memLp_lim.1
      hD.tendsto
  obtain ⟨ns, -, hae⟩ := hm.exists_seq_tendsto_ae
  have hpos : ∀ᵐ x ∂(volume.restrict C), ∀ n, 0 < (cfm (e (ns n)) x).det := by
    refine ae_all_iff.2 fun n => (ae_restrict_iff' hmeas).2 ?_
    filter_upwards [h.coframe_oriented (ns n)] with x hx hxC using hx (hCΩ hxC)
  have hnd : ∀ᵐ x ∂(volume.restrict C), (cfm eL x).det ≠ 0 := by
    refine (ae_restrict_iff' hmeas).2 ?_
    filter_upwards [h.limit_nondegenerate] with x hx hxC using hx (hCΩ hxC)
  filter_upwards [hae, hpos, hnd] with x hx hp hn
  exact lt_of_le_of_ne (ge_of_tendsto' hx fun n => (hp n).le) (Ne.symm hn)

end LimitProperties

/-! ### Restriction of weak convergence and of test functions -/

/-- Weak `L²(K')` convergence tested against scalar functions restricts to `K ⊆ K'`. -/
theorem tendsto_setIntegral_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K K' : Set (Fin 4 → ℝ)} (hK : MeasurableSet K) (hKK' : K ⊆ K')
    {S : ℕ → (Fin 4 → ℝ) → E} {S' : (Fin 4 → ℝ) → E}
    (hw : ∀ g : (Fin 4 → ℝ) → ℝ, MemLp g 2 (volume.restrict K') →
      Tendsto (fun n => ∫ x in K', g x • S n x) atTop (𝓝 (∫ x in K', g x • S' x)))
    (g : (Fin 4 → ℝ) → ℝ) (hg : MemLp g 2 (volume.restrict K)) :
    Tendsto (fun n => ∫ x in K, g x • S n x) atTop (𝓝 (∫ x in K, g x • S' x)) := by
  have hrr : (volume.restrict K').restrict K = volume.restrict K := by
    rw [Measure.restrict_restrict hK, Set.inter_eq_left.2 hKK']
  have hg' : MemLp (K.indicator g) 2 (volume.restrict K') := by
    rw [memLp_indicator_iff_restrict hK, hrr]; exact hg
  have key : ∀ F : (Fin 4 → ℝ) → E,
      ∫ x in K', K.indicator g x • F x = ∫ x in K, g x • F x := fun F => by
    have : (fun x => K.indicator g x • F x) = K.indicator (fun x => g x • F x) := by
      funext x; by_cases hx : x ∈ K <;> simp [hx]
    rw [this, integral_indicator hK, hrr]
  have := hw _ hg'
  simp only [key] at this
  exact this

/-- A test function on a smaller open set is a test function on a larger one. -/
def liftTest {U Ω : Opens (Fin 4 → ℝ)} (hUΩ : (U : Set (Fin 4 → ℝ)) ⊆ Ω) (ψ : 𝓓(U, ℝ)) :
    𝓓(Ω, ℝ) :=
  ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset.trans hUΩ⟩

theorem liftTest_apply {U Ω : Opens (Fin 4 → ℝ)} (hUΩ : (U : Set (Fin 4 → ℝ)) ⊆ Ω)
    (ψ : 𝓓(U, ℝ)) (x : Fin 4 → ℝ) : liftTest hUΩ ψ x = ψ x := rfl

/-- Torsion-freeness restricts to smaller open sets. -/
theorem isTorsionFree_mono {U Ω : Opens (Fin 4 → ℝ)} (hUΩ : (U : Set (Fin 4 → ℝ)) ⊆ Ω)
    {e : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {ω : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (h : IsTorsionFree matAct Ω e ω) : IsTorsionFree matAct U e ω := fun ψ a b =>
  h (liftTest hUΩ ψ) a b

/-- The transpose form of metric compatibility gives the index form used by
`LimitEinsteinInsertion.ae_eq_of_isTorsionFree`. -/
theorem compat_index_of_transpose {M : Matrix (Fin 4) (Fin 4) ℝ}
    (h : (minkowski * M)ᵀ = -(minkowski * M)) (I J : Fin 4) :
    ∑ K, minkowski I K * M K J = -∑ K, minkowski J K * M K I := by
  have := congrFun (congrFun h J) I
  simpa [Matrix.transpose_apply, Matrix.mul_apply, Matrix.neg_apply] using this

/-- `MemLp` is inherited by smaller measures (stated for an arbitrary normed group, so that it
applies to matrix-valued fields with the `L^∞`-operator norm). -/
theorem memLp_mono_measure' {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ ν : Measure X} (hle : μ ≤ ν) {f : X → E} {p : ℝ≥0∞} (hf : MemLp f p ν) : MemLp f p μ :=
  hf.mono_measure hle

/-! ### The Einstein limit along an identified curvature subsequence -/

/-- The realized Holst variation `∫_K δ_{e_X H_X} L_H(e_X, R_X)`. -/
def realizedHolst (K : Set (Fin 4 → ℝ)) (e : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (H : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∫ x in K, holstVariation minkowski (cfm e x) (cfm e x * H x) (rcf R x)

/-- The realized Palatini variation `∫_K δ_{e_X H_X} L_P(e_X, R_X)`. -/
def realizedPalatini (K : Set (Fin 4 → ℝ)) (e : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (H : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∫ x in K, palatiniVariation (cfm e x) (cfm e x * H x) (rcf R x)

/-- The realized volume variation `∫_K det e_X · tr H_X`. -/
def realizedVolume (K : Set (Fin 4 → ℝ)) (e : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (H : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∫ x in K, (cfm e x).det * Matrix.trace (H x)

/-- **Einstein limit of the complete metric first variations along an identified curvature
limit** (route-independent core of `thm:supp-renewal-palatini`).  On compacts `K ⊆ int K'`,
assume `eq:supp-coframe-l2-l6` on `K'`, the spatial connection coefficients converge strongly in
`L²(K')` with a uniform `L³(K')` bound, the limit pair is torsion-free and metric compatible on
`int K'` with an oriented coframe, the curvature records are bounded in `L²(K')` and converge
weakly to `R'` with `R' = dω + ω ∧ ω` on `int K'`, the lift coefficient tensors are bounded and
converge a.e. on `K` to `-½ k g`, the coefficients converge with `β ≠ 0`, and the physical
first-variation remainder tends to zero.  Then the complete first variations converge to
`β ∫_K √(-g) k^{γb}(G_{bγ} + Λ g_{bγ})`, `Λ = -λ/(2β)`. -/
theorem tendsto_firstVariation_einstein {K K' : Set (Fin 4 → ℝ)} (hK : IsCompact K)
    (hK' : IsCompact K') (hKK' : K ⊆ interior K')
    {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R' : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {t : Fin 4}
    (he : ∀ μ, LpTendsto (volume.restrict K') 2 (fun n => e n μ) (eL μ)) {M6 : ℝ≥0∞}
    (hM6 : M6 ≠ ∞) (he6 : ∀ n μ, eLpNorm (e n μ) 6 (volume.restrict K') ≤ M6)
    (hωL : ∀ a, MemLp (ωL a) 2 (volume.restrict K'))
    (hωs : ∀ a, a ≠ t → LpTendsto (volume.restrict K') 2 (fun n => ω n a) (ωL a))
    {M3 : ℝ≥0∞} (hM3 : M3 ≠ ∞)
    (hω3 : ∀ a, a ≠ t → ∀ n, eLpNorm (ω n a) 3 (volume.restrict K') ≤ M3)
    (hT : IsTorsionFree matAct (interiorOpens K') eL ωL)
    (hcompat : ∀ᵐ x ∂(volume.restrict K'), ∀ a, (minkowski * ωL a x)ᵀ = -(minkowski * ωL a x))
    (hdet : ∀ᵐ x ∂(volume.restrict K'), 0 < (cfm eL x).det)
    (hCurv : IsDistributionalCurvature (interiorOpens K') ωL R')
    (hR : ∀ n a b, MemLp (R n a b) 2 (volume.restrict K'))
    (hR' : ∀ a b, MemLp (R' a b) 2 (volume.restrict K')) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hRb : ∀ n a b, eLpNorm (R n a b) 2 (volume.restrict K') ≤ B)
    (hRw : ∀ a b (g : (Fin 4 → ℝ) → ℝ), MemLp g 2 (volume.restrict K') →
      Tendsto (fun n => ∫ x in K', g x • R n a b x) atTop (𝓝 (∫ x in K', g x • R' a b x)))
    {k : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {H : ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hHm : ∀ n, AEStronglyMeasurable (H n) (volume.restrict K)) {M : ℝ}
    (hHb : ∀ n, ∀ᵐ x ∂(volume.restrict K), ‖H n x‖ ≤ M)
    (hHae : ∀ᵐ x ∂(volume.restrict K),
      Tendsto (fun n => H n x) atTop (𝓝 (metricTestGenerator minkowski (cfm eL x) (k x))))
    {αs βs lams : ℕ → ℝ} {α β lam : ℝ} (hα : Tendsto αs atTop (𝓝 α))
    (hβ : Tendsto βs atTop (𝓝 β)) (hlam : Tendsto lams atTop (𝓝 lam)) (hβ0 : β ≠ 0)
    {δA : ℕ → ℝ}
    (hrem : Tendsto (classifiedVariationRemainder δA (fun n => realizedHolst K (e n) (H n) (R n))
      (fun n => realizedPalatini K (e n) (H n) (R n)) (fun n => realizedVolume K (e n) (H n))
      αs βs lams) atTop (𝓝 0)) :
    Tendsto δA atTop
      (𝓝 (∫ x in K, einsteinInsertionDensity β lam (cfm eL x) (k x) (rcf R' x))) := by
  have hKK'' : K ⊆ K' := hKK'.trans interior_subset
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hK'm : MeasurableSet K' := hK'.isClosed.measurableSet
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have : IsFiniteMeasure (volume.restrict K') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK'.measure_lt_top⟩
  have hle : volume.restrict K ≤ volume.restrict K' := Measure.restrict_mono hKK'' le_rfl
  -- the `(E1)` passage on `K`
  obtain ⟨tH, tP, tV, iH, iP, iV⟩ := tendsto_liftVariations (ν := volume.restrict K) minkowski
    (fun μ => (he μ).mono_measure' hle) hM6
    (fun n μ => (eLpNorm_mono_measure _ hle).trans (he6 n μ)) hHm hHb hHae
    (fun n a b => memLp_mono_measure' hle (hR n a b)) (fun a b => memLp_mono_measure' hle (hR' a b)) hB
    (fun n a b => (eLpNorm_mono_measure _ hle).trans (hRb n a b))
    (fun a b g hg => tendsto_setIntegral_restrict hKm hKK'' (hRw a b) g hg)
  -- variation transfer (`lem:supp-variation-transfer`)
  have hA := tendsto_completeVariation_of_classified δA
    (fun n => realizedHolst K (e n) (H n) (R n)) (fun n => realizedPalatini K (e n) (H n) (R n))
    (fun n => realizedVolume K (e n) (H n)) αs βs lams hα hβ hlam tH tP tV hrem
  -- the limit is the integrated classified metric variation
  have hdetK : ∀ᵐ x ∂(volume.restrict K), 0 < (cfm eL x).det := ae_mono hle hdet
  have hcl : α * (∫ x in K, holstVariation minkowski (cfm eL x)
        (cfm eL x * metricTestGenerator minkowski (cfm eL x) (k x)) (rcf R' x)) +
      β * (∫ x in K, palatiniVariation (cfm eL x)
        (cfm eL x * metricTestGenerator minkowski (cfm eL x) (k x)) (rcf R' x)) +
      lam * (∫ x in K, (cfm eL x).det *
        Matrix.trace (metricTestGenerator minkowski (cfm eL x) (k x))) =
      ∫ x in K, classifiedMetricVariation α β lam minkowski (cfm eL x) (k x) (rcf R' x) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (iH.const_mul _) (iP.const_mul _)]
    rw [← integral_add (f := fun x => α * holstVariation minkowski (cfm eL x)
        (cfm eL x * metricTestGenerator minkowski (cfm eL x) (k x)) (rcf R' x) +
        β * palatiniVariation (cfm eL x)
        (cfm eL x * metricTestGenerator minkowski (cfm eL x) (k x)) (rcf R' x))
      (by exact (iH.const_mul _).add (iP.const_mul _)) (iV.const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [hdetK] with x hx
    simp only [classifiedMetricVariation, Pi.add_apply]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.2 hx.ne')]
  -- the anisotropic integrability packet on `int K'`
  have hsub : ∀ C : Set (Fin 4 → ℝ), C ⊆ interiorOpens K' →
      volume.restrict C ≤ volume.restrict K' := fun C hC =>
    Measure.restrict_mono (hC.trans interior_subset) le_rfl
  have hI : AnisotropicIntegrability (interiorOpens K') t eL ωL R' :=
    ⟨fun a b C _ hC => memLp_mono_measure' (hsub C hC) (hR' a b),
      fun c C _ hC => (lpTendsto_four_of_two_six (he c) hM6 (fun n => he6 n c)).2.mono_measure
        (hsub C hC),
      fun a C _ hC => memLp_mono_measure' (hsub C hC) (hωL a),
      fun a ha C _ hC => memLp_mono_measure' (hsub C hC)
        ((hωs a ha).memLp_of_bound two_ne_zero hM3 (hω3 a ha))⟩
  have hc : ∀ᵐ x, x ∈ interiorOpens K' → ∀ a,
      (minkowski * ωL a x)ᵀ = -(minkowski * ωL a x) := by
    filter_upwards [(ae_restrict_iff' hK'm).1 hcompat] with x hx hxU
    exact hx (interior_subset hxU)
  have hd : ∀ᵐ x, x ∈ interiorOpens K' → 0 < (coframeMatrix fun μ => eL μ x).det := by
    filter_upwards [(ae_restrict_iff' hK'm).1 hdet] with x hx hxU
    exact hx (interior_subset hxU)
  have hE := integral_classifiedMetricVariation_of_metricCompatible hT hCurv hI hc hd K hK hKK' k
    α β lam hβ0
  have hlim : α * (∫ x in K, holstVariation minkowski (cfm eL x)
        (cfm eL x * metricTestGenerator minkowski (cfm eL x) (k x)) (rcf R' x)) +
      β * (∫ x in K, palatiniVariation (cfm eL x)
        (cfm eL x * metricTestGenerator minkowski (cfm eL x) (k x)) (rcf R' x)) +
      lam * (∫ x in K, (cfm eL x).det *
        Matrix.trace (metricTestGenerator minkowski (cfm eL x) (k x))) =
      ∫ x in K, einsteinInsertionDensity β lam (cfm eL x) (k x) (rcf R' x) :=
    hcl.trans hE
  exact hA.mono_right (le_of_eq (congrArg 𝓝 hlim))

/-! ### The localized renewal–Palatini handoff -/

/-- **`thm:supp-renewal-palatini` (localized renewal–Palatini handoff), full-connection route,
with the amendment `spatialConnectionL3Bound`.**  Under `RenewalPalatiniHypotheses`:

1. (`eq:supp-phv-classification`) every regulator score is `α_X L_H + β_X L_P + λ_X L_vol` with
   its classified coefficients and the scores converge to `α L_H + β L_P + λ L_vol`;
2. limiting torsion vanishes: the limit connection is torsion-free for the limit coframe in
   distributions on `Ω`;
3. for every compact `K ⊆ Ω` there is a compact neighbourhood `K'` (`K ⊆ int K' ⊆ K' ⊆ Ω`) and
   a curvature field `R ∈ L²(K')` with `R = dω + ω ∧ ω` in distributions on `int K'` (the
   identified limiting curvature, determined by `ω`), such that the limit connection is metric
   compatible and the limit coframe oriented on `K'`, the limit connection is the unique
   torsion-free metric-compatible (Levi-Civita) `L²_loc` connection of the limit coframe on
   `int K'`, and **for every inverse-metric test `k` with bounded convergent physical lifts `H_X`
   (`(E1)`, `δe_X = e_X H_X`, `H_X → -½ k g` a.e. on `K`) and every sequence of complete first
   variations `δA_X` satisfying the physical first-variation remainder condition
   (`eq:main-first-variation-reduction`), the whole sequence `δA_X` converges to
   `β ∫_K √(-g) k^{γb} (G_{bγ} + Λ g_{bγ})`, `Λ = -λ/(2β)`** (`eq:supp-einstein-insertion`,
   `χ = β ≠ 0`; `G` is the Einstein tensor of the coordinate curvature of `R`, i.e. of the
   Levi-Civita connection of `g = eᵀ η e`). -/
theorem renewal_palatini_handoff {Ω : Opens (Fin 4 → ℝ)}
    {score : ℕ → GravitationalClassDensity} {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {α β lam : ℝ} {t : Fin 4}
    (h : RenewalPalatiniHypotheses Ω score e ω R T eL ωL α β lam t) :
    ((∀ n, score n = GravitationalClassDensity.ofCoefficients (holstCoeff (score n))
      (palatiniCoeff (score n)) (volumeCoeff (score n))) ∧
      Tendsto (fun n => (score n).pairing) atTop
        (𝓝 (GravitationalClassDensity.ofCoefficients α β lam).pairing) ∧
      ∀ v : Fin 4 → Fin 4 → ℝ, Tendsto (fun n => (score n).volume v) atTop
        (𝓝 ((GravitationalClassDensity.ofCoefficients α β lam).volume v))) ∧
    IsTorsionFree matAct Ω eL ωL ∧
    ∀ K : Set (Fin 4 → ℝ), IsCompact K → K ⊆ Ω →
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
        ∀ (k : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
          (H : ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (M : ℝ) (δA : ℕ → ℝ),
          (∀ n, AEStronglyMeasurable (H n) (volume.restrict K)) →
          (∀ n, ∀ᵐ x ∂(volume.restrict K), ‖H n x‖ ≤ M) →
          (∀ᵐ x ∂(volume.restrict K),
            Tendsto (fun n => H n x) atTop (𝓝 (metricTestGenerator minkowski (cfm eL x) (k x)))) →
          Tendsto (classifiedVariationRemainder δA
            (fun n => realizedHolst K (e n) (H n) (R n))
            (fun n => realizedPalatini K (e n) (H n) (R n))
            (fun n => realizedVolume K (e n) (H n))
            (fun n => holstCoeff (score n)) (fun n => palatiniCoeff (score n))
            (fun n => volumeCoeff (score n))) atTop (𝓝 0) →
          Tendsto δA atTop
            (𝓝 (∫ x in K, einsteinInsertionDensity β lam (cfm eL x) (k x) (rcf RL x))) := by
  refine ⟨h.toRenewalPalatiniCommon.classified, h.isTorsionFree, fun K hK hKΩ => ?_⟩
  obtain ⟨K', hK', hKK', hK'Ω⟩ := exists_compact_between hK Ω.isOpen hKΩ
  have : IsFiniteMeasure (volume.restrict K') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK'.measure_lt_top⟩
  have hUK' : ((interiorOpens K' : Opens (Fin 4 → ℝ)) : Set (Fin 4 → ℝ)) ⊆ Ω :=
    interior_subset.trans hK'Ω
  -- uniform bounds on `K'`
  choose M6 hM6 hb6 using fun μ => h.coframe_L6 μ K' hK' hK'Ω
  have hM6s : ∑ μ, M6 μ ≠ ∞ := ENNReal.sum_ne_top.2 fun μ _ => hM6 μ
  have hb6s : ∀ n μ, eLpNorm (e n μ) 6 (volume.restrict K') ≤ ∑ μ, M6 μ := fun n μ =>
    (hb6 μ n).trans (Finset.single_le_sum (f := M6) (fun _ _ => zero_le) (Finset.mem_univ μ))
  have hL3 : ∀ a, ∃ M : ℝ≥0∞, M ≠ ∞ ∧ (a ≠ t →
      ∀ n, eLpNorm (ω n a) 3 (volume.restrict K') ≤ M) := fun a => by
    by_cases ha : a = t
    · exact ⟨0, ENNReal.zero_ne_top, fun h' => absurd ha h'⟩
    · obtain ⟨M, hM, hb⟩ := h.spatialConnectionL3Bound a ha K' hK' hK'Ω
      exact ⟨M, hM, fun _ => hb⟩
  choose M3 hM3 hb3 using hL3
  have hM3s : ∑ a, M3 a ≠ ∞ := ENNReal.sum_ne_top.2 fun a _ => hM3 a
  have hb3s : ∀ a, a ≠ t → ∀ n, eLpNorm (ω n a) 3 (volume.restrict K') ≤ ∑ a, M3 a :=
    fun a ha n => (hb3 a ha n).trans
      (Finset.single_le_sum (f := M3) (fun _ _ => zero_le) (Finset.mem_univ a))
  obtain ⟨B, hB, hRb⟩ := h.curvature_bound K' hK' hK'Ω
  have hRmem : ∀ n a b, MemLp (R n a b) 2 (volume.restrict K') := fun n a b =>
    h.curvature_L2 n a b K' hK' hK'Ω
  -- curvature extraction along any subsequence
  have extract : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ,
        (∀ a b, MemLp (RL a b) 2 (volume.restrict K')) ∧
        (∀ a b (g : (Fin 4 → ℝ) → ℝ), MemLp g 2 (volume.restrict K') →
          Tendsto (fun n => ∫ x in K', g x • R (ns (φ n)) a b x) atTop
            (𝓝 (∫ x in K', g x • RL a b x))) ∧
        IsDistributionalCurvature (interiorOpens K') ωL RL := fun ns hns => by
    obtain ⟨φ, hφ, RL, hRL, hw, hid, -⟩ := curvature_weak_compactness (p := 2) (q := 2)
      (by norm_num) (by norm_num) hK' (fun n => R (ns n)) (fun n a b => hRmem (ns n) a b) hB
      (fun n a b => hRb (ns n) a b)
    refine ⟨φ, hφ, RL, hRL, hw, hid (fun n => ω (ns n)) ωL ?_ ?_⟩
    · exact ⟨fun n a C hC hCU => h.connection_L2.memLp (ns n) a C hC (hCU.trans hUK'),
        fun a C hC hCU => h.connection_L2.memLp_lim a C hC (hCU.trans hUK'),
        fun a C hC hCU => (h.connection_L2.tendsto a C hC (hCU.trans hUK')).comp hns⟩
    · intro ψ a b
      exact (h.curvature_identification (liftTest hUK' ψ) a b).comp hns
  obtain ⟨-, -, R0, hR0, -, hid0⟩ := extract id tendsto_id
  have hT' : IsTorsionFree matAct (interiorOpens K') eL ωL := isTorsionFree_mono hUK' h.isTorsionFree
  have hcompat := h.ae_compat K' hK' hK'Ω
  have hdet := h.toRenewalPalatiniCommon.ae_det_pos K' hK' hK'Ω
  have hK'm : MeasurableSet K' := hK'.isClosed.measurableSet
  have hsub : ∀ C : Set (Fin 4 → ℝ), C ⊆ interiorOpens K' →
      volume.restrict C ≤ volume.restrict K' := fun C hC =>
    Measure.restrict_mono (hC.trans interior_subset) le_rfl
  refine ⟨K', hK', hKK', hK'Ω, R0, hR0, hid0, hcompat, hdet, ?_, ?_⟩
  · -- Levi-Civita uniqueness
    intro ω' hω' hT'' hc'
    have hc : ∀ᵐ x, x ∈ interiorOpens K' → ∀ a I J,
        ∑ K, minkowski I K * ωL a x K J = -∑ K, minkowski J K * ωL a x K I := by
      filter_upwards [(ae_restrict_iff' hK'm).1 hcompat] with x hx hxU a I J
      exact compat_index_of_transpose (hx (interior_subset hxU) a) I J
    have hc'' : ∀ᵐ x, x ∈ interiorOpens K' → ∀ a I J,
        ∑ K, minkowski I K * ω' a x K J = -∑ K, minkowski J K * ω' a x K I := by
      filter_upwards [hc'] with x hx hxU a I J
      exact compat_index_of_transpose (hx hxU a) I J
    have hd : ∀ᵐ x, x ∈ interiorOpens K' → (coframeMatrix fun μ => eL μ x).det ≠ 0 := by
      filter_upwards [(ae_restrict_iff' hK'm).1 hdet] with x hx hxU
      exact (hx (interior_subset hxU)).ne'
    have := ae_eq_of_isTorsionFree (Ω := interiorOpens K')
      (fun c C hC hCU => h.coframe_L2.memLp_lim c C hC (hCU.trans hUK'))
      (fun a C hC hCU => h.connection_L2.memLp_lim a C hC (hCU.trans hUK')) hω' hT' hT'' hd hc
      hc''
    filter_upwards [this] with x hx hxU a
    exact (hx hxU a).symm
  · -- the Einstein limit of the complete first variations
    intro k H M δA hHm hHb hHae hrem
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨φ, hφ, RL, hRL, hw, hid⟩ := extract ns hns
    have hm : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
    refine ⟨φ, ?_⟩
    have core := tendsto_firstVariation_einstein (t := t) hK hK' hKK'
      (e := fun n => e (ns (φ n))) (ω := fun n => ω (ns (φ n))) (R := fun n => R (ns (φ n)))
      (H := fun n => H (ns (φ n))) (δA := fun n => δA (ns (φ n)))
      (fun μ => (h.coframe_L2.lpTendsto μ hK' hK'Ω).comp_tendsto hm) hM6s
      (fun n μ => hb6s (ns (φ n)) μ)
      (fun a => h.connection_L2.memLp_lim a K' hK' hK'Ω)
      (fun a _ => (h.connection_L2.lpTendsto a hK' hK'Ω).comp_tendsto hm) hM3s
      (fun a ha n => hb3s a ha (ns (φ n))) hT' hcompat hdet hid
      (fun n a b => hRmem (ns (φ n)) a b) hRL hB (fun n a b => hRb (ns (φ n)) a b) hw
      (fun n => hHm (ns (φ n))) (fun n => hHb (ns (φ n)))
      (by filter_upwards [hHae] with x hx using hx.comp hm)
      (h.holst_tendsto.comp hm) (h.palatini_tendsto.comp hm) (h.volume_tendsto.comp hm)
      h.palatini_ne_zero (hrem.comp hm)
    -- the identified curvature does not depend on the subsequence
    have hRR : ∀ a b, ∀ᵐ x, x ∈ interiorOpens K' → RL a b x = R0 a b x := fun a b =>
      ae_eq_of_isDistributionalCurvature hid hid0
        (fun a b C _ hC => memLp_mono_measure' (hsub C hC) (hRL a b))
        (fun a b C _ hC => memLp_mono_measure' (hsub C hC) (hR0 a b)) a b
    have hRR' : ∀ᵐ x, x ∈ interiorOpens K' → ∀ a b, RL a b x = R0 a b x := by
      have : ∀ᵐ x, ∀ a b : Fin 4, x ∈ interiorOpens K' → RL a b x = R0 a b x := by
        simp only [ae_all_iff]; exact hRR
      filter_upwards [this] with x hx hxU a b using hx a b hxU
    have heq : ∫ x in K, einsteinInsertionDensity β lam (cfm eL x) (k x) (rcf RL x) =
        ∫ x in K, einsteinInsertionDensity β lam (cfm eL x) (k x) (rcf R0 x) := by
      refine setIntegral_congr_ae hK.isClosed.measurableSet ?_
      filter_upwards [hRR'] with x hx hxK
      have : rcf RL x = rcf R0 x := by
        simp only [rcf]
        congr 1
        funext a b
        exact hx (hKK' hxK) a b
      rw [this]
    exact core.mono_right (le_of_eq (congrArg 𝓝 heq))

/-! ### The literal-link route -/

section LiteralLink

/-- Weak `L²` limits preserve almost-everywhere linear constraints: if `u_n ⇀ u` weakly in
`L²(ν)` (tested by scalar `L²` functions) and `L(u_n) = 0` almost everywhere, then `L(u) = 0`
almost everywhere (test with `g = L ∘ u`). -/
theorem ae_map_eq_zero_of_weak {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsFiniteMeasure ν] {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    (L : A →L[ℝ] ℝ) {u : ℕ → X → A} {u' : X → A} (hu : ∀ n, MemLp (u n) 2 ν)
    (hu' : MemLp u' 2 ν)
    (hw : ∀ g : X → ℝ, MemLp g 2 ν →
      Tendsto (fun n => ∫ x, g x • u n x ∂ν) atTop (𝓝 (∫ x, g x • u' x ∂ν)))
    (h0 : ∀ n, ∀ᵐ x ∂ν, L (u n x) = 0) : ∀ᵐ x ∂ν, L (u' x) = 0 := by
  set f : X → ℝ := fun x => L (u' x)
  have hf : MemLp f 2 ν := L.comp_memLp' hu'
  have hint : ∀ w : X → A, MemLp w 2 ν → Integrable (fun x => f x • w x) ν := fun w hw' =>
    (hw'.smul hf (r := 1)).integrable le_rfl
  have hL : ∀ w : X → A, MemLp w 2 ν → L (∫ x, f x • w x ∂ν) = ∫ x, f x * L (w x) ∂ν :=
    fun w hw' => by
      rw [← L.integral_comp_comm (hint w hw')]
      simp only [map_smul, smul_eq_mul]
  have hzero : ∀ n, L (∫ x, f x • u n x ∂ν) = 0 := fun n => by
    rw [hL _ (hu n)]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h0 n] with x hx
    simp [hx]
  have hlim : Tendsto (fun n => L (∫ x, f x • u n x ∂ν)) atTop (𝓝 (L (∫ x, f x • u' x ∂ν))) :=
    (L.continuous.tendsto _).comp (hw f hf)
  have h1 : L (∫ x, f x • u' x ∂ν) = 0 := by
    simp only [hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  rw [hL _ hu'] at h1
  have hsq : Integrable (fun x => f x * f x) ν := hf.integrable_mul hf
  have hz : (fun x => f x * f x) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (f x)) hsq).1 h1
  filter_upwards [hz] with x hx
  exact mul_self_eq_zero.1 hx

/-- Weak `L²_loc` convergence of connection coefficients (tested by scalar functions) gives the
coframe-tested weak convergence `WeakActTendsto1` used by the literal-link torsion passage. -/
theorem weakActTendsto1_of_weak {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [CompleteSpace A] (act : A →L[ℝ] (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) {Ω : Opens (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → A} {ωL : Fin 4 → (Fin 4 → ℝ) → A}
    (hmem : ∀ n a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
      MemLp (ω n a) 2 (volume.restrict C))
    (hmemL : ∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
      MemLp (ωL a) 2 (volume.restrict C))
    (hw : ∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω → ∀ g : (Fin 4 → ℝ) → ℝ,
      MemLp g 2 (volume.restrict C) →
      Tendsto (fun n => ∫ x in C, g x • ω n a x) atTop (𝓝 (∫ x in C, g x • ωL a x))) :
    WeakActTendsto1 act Ω ω ωL := by
  intro a C hC hCΩ g hg ψ hψ hz
  have : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  obtain ⟨M0, hM0⟩ := exists_bound_of_eq_zero_off hψ hC hz
  set gj : Fin 4 → (Fin 4 → ℝ) → ℝ := fun j x => ψ x * g x j
  have hgj : ∀ j, MemLp (gj j) 2 (volume.restrict C) := fun j => by
    have hcomp : MemLp (fun x => g x j) 2 (volume.restrict C) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) j).comp_memLp' hg
    refine MemLp.of_le_mul (c := M0) hcomp (hψ.aestronglyMeasurable.mul hcomp.1)
      (Eventually.of_forall fun x => ?_)
    show ‖ψ x * g x j‖ ≤ M0 * ‖g x j‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM0 x) (norm_nonneg _)
  set Lj : Fin 4 → A →L[ℝ] (Fin 4 → ℝ) := fun j => act.flip (Pi.single j 1)
  have hpt : ∀ (M : A) (x : Fin 4 → ℝ),
      ψ x • act M (g x) = ∑ j, Lj j (gj j x • M) := fun M x => by
    have hg' : g x = ∑ j, g x j • (Pi.single j 1 : Fin 4 → ℝ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hg']
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, Lj, gj,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply]
  have hexp : ∀ w : (Fin 4 → ℝ) → A, MemLp w 2 (volume.restrict C) →
      ∫ x, ψ x • act (w x) (g x) = ∑ j, Lj j (∫ x in C, gj j x • w x) := fun w hw' => by
    have hint : ∀ j, Integrable (fun x => gj j x • w x) (volume.restrict C) := fun j =>
      (hw'.smul (hgj j) (r := 1)).integrable le_rfl
    rw [integral_test_eq_setIntegral hz]
    simp only [hpt]
    rw [integral_finsetSum _ fun j _ => (Lj j).integrable_comp (hint j)]
    exact Finset.sum_congr rfl fun j _ => (Lj j).integral_comp_comm (hint j)
  simp only [hexp _ (hmem _ a C hC hCΩ), hexp _ (hmemL a C hC hCΩ)]
  exact tendsto_finsetSum _ fun j _ =>
    ((Lj j).continuous.tendsto _).comp (hw a C hC hCΩ (gj j) (hgj j))

/-- The `(I, J)` entry of a matrix, as a continuous linear functional. -/
def entryCLM (I J : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M I J
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem entryCLM_apply (I J : Fin 4) (M : Matrix (Fin 4) (Fin 4) ℝ) : entryCLM I J M = M I J :=
  rfl

/-- The hypotheses of `thm:supp-renewal-palatini` on the periodic literal-link route
(`thm:main-literal-link-compactness`): the common packet (with the amendment
`spatialConnectionL3Bound`, which on this route is the `L^{10/3}` bound
`eq:supp-literal-integrability`), connection coefficients bounded and weakly convergent in
`L²_loc` with the spatial ones (`a ≠ t`) strongly convergent, and the curvature records weakly
convergent to a limit `RL` identified as the full nonlinear curvature `dω + ω ∧ ω` of the limit
connection (the identification supplied by the electric and magnetic records on this route). -/
structure RenewalPalatiniLiteralLinkHypotheses (Ω : Opens (Fin 4 → ℝ))
    (score : ℕ → GravitationalClassDensity)
    (e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (α β lam : ℝ) (t : Fin 4) :
    Prop extends RenewalPalatiniCommon Ω score e ω R T eL α β lam t where
  connection_L2 : ∀ n a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (ω n a) 2 (volume.restrict C)
  connection_bound : ∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (ω n a) 2 (volume.restrict C) ≤ M
  connection_limit_L2 : ∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (ωL a) 2 (volume.restrict C)
  /-- Weak `L²_loc` convergence of every connection coefficient (the temporal one may converge
  only weakly). -/
  connection_weak : ∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω → ∀ g : (Fin 4 → ℝ) → ℝ,
    MemLp g 2 (volume.restrict C) →
    Tendsto (fun n => ∫ x in C, g x • ω n a x) atTop (𝓝 (∫ x in C, g x • ωL a x))
  /-- Strong `L²_loc` convergence of the spatial connection coefficients. -/
  spatial_strong : ∀ a, a ≠ t → ∀ (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    LpTendsto (volume.restrict C) 2 (fun n => ω n a) (ωL a)
  curvature_limit_L2 : ∀ a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    MemLp (RL a b) 2 (volume.restrict C)
  curvature_weak : ∀ a b (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
    ∀ g : (Fin 4 → ℝ) → ℝ, MemLp g 2 (volume.restrict C) →
    Tendsto (fun n => ∫ x in C, g x • R n a b x) atTop (𝓝 (∫ x in C, g x • RL a b x))
  curvature_identified : IsDistributionalCurvature Ω ωL RL

variable {Ω : Opens (Fin 4 → ℝ)} {score : ℕ → GravitationalClassDensity}
  {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
  {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
  {RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {α β lam : ℝ} {t : Fin 4}

/-- Tested torsion residuals tend to zero (common to both routes). -/
theorem RenewalPalatiniCommon.tendsto_torsionPairing
    (h : RenewalPalatiniCommon Ω score e ω R T eL α β lam t) (φ : 𝓓(Ω, ℝ)) (a b : Fin 4) :
    Tendsto (fun n => torsionPairing matAct (e n) (ω n) φ a b) atTop (𝓝 0) := by
  set C := tsupport (φ : (Fin 4 → ℝ) → ℝ)
  have hC : IsCompact C := φ.hasCompactSupport
  have hCΩ : C ⊆ Ω := φ.tsupport_subset
  have : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hz0 : ∀ x, x ∉ C → φ x = 0 := fun x hx => test_eq_zero_off φ hx
  obtain ⟨M0, hM0⟩ := exists_bound_of_eq_zero_off φ.continuous hC hz0
  have hT := tendsto_integral_smul_of_L2' (V := Fin 4 → ℝ) φ.continuous.aestronglyMeasurable hM0
    (fun n => h.torsion_L2 n a b C hC hCΩ) (MemLp.zero' (ε := Fin 4 → ℝ))
    ((h.tendsto_eLpNorm_torsion a b C hC hCΩ).congr fun n => by congr 1; funext x; simp)
  simp only [smul_zero, integral_zero] at hT
  refine hT.congr fun n => ?_
  rw [h.torsion_rep n φ a b, integral_test_eq_setIntegral hz0]

/-- Limiting torsion vanishes on the literal-link route (weak temporal coefficient). -/
theorem RenewalPalatiniLiteralLinkHypotheses.isTorsionFree
    (h : RenewalPalatiniLiteralLinkHypotheses Ω score e ω R T eL ωL RL α β lam t) :
    IsTorsionFree matAct Ω eL ωL :=
  isTorsionFree_of_tendsto_weak matAct h.coframe_L2 ⟨h.connection_L2, h.connection_bound⟩
    (weakActTendsto1_of_weak matAct h.connection_L2 h.connection_limit_L2 h.connection_weak)
    h.toRenewalPalatiniCommon.tendsto_torsionPairing

/-- The limit connection of the literal-link route is metric compatible on every compact. -/
theorem RenewalPalatiniLiteralLinkHypotheses.ae_compat
    (h : RenewalPalatiniLiteralLinkHypotheses Ω score e ω R T eL ωL RL α β lam t)
    (C : Set (Fin 4 → ℝ)) (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
    ∀ᵐ x ∂(volume.restrict C), ∀ a, (minkowski * ωL a x)ᵀ = -(minkowski * ωL a x) := by
  have : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hmeas : MeasurableSet C := hC.isClosed.measurableSet
  have hone : ∀ a I J, ∀ᵐ x ∂(volume.restrict C), (entryCLM I J).comp compatCLM (ωL a x) = 0 :=
    fun a I J => by
      refine ae_map_eq_zero_of_weak ((entryCLM I J).comp compatCLM)
        (fun n => h.connection_L2 n a C hC hCΩ) (h.connection_limit_L2 a C hC hCΩ)
        (h.connection_weak a C hC hCΩ) fun n => ?_
      refine (ae_restrict_iff' hmeas).2 ?_
      filter_upwards [h.connection_lorentz n] with x hx hxC
      show ((minkowski * ω n a x)ᵀ + minkowski * ω n a x) I J = 0
      rw [hx (hCΩ hxC) a, neg_add_cancel]; rfl
  have hall : ∀ᵐ x ∂(volume.restrict C), ∀ a I J,
      (entryCLM I J).comp compatCLM (ωL a x) = 0 := by
    simp only [ae_all_iff]; exact hone
  filter_upwards [hall] with x hx a
  have h0 : (minkowski * ωL a x)ᵀ + minkowski * ωL a x = 0 := by
    ext I J; exact hx a I J
  exact eq_neg_of_add_eq_zero_left h0

/-- **`thm:supp-renewal-palatini` (localized renewal–Palatini handoff), literal-link route,
with the amendment `spatialConnectionL3Bound`**: the classification, vanishing limiting
torsion, metric compatibility, orientation and Levi-Civita uniqueness of the limit, and for every
compact `K ⊆ Ω` and every lifted metric test with the physical first-variation remainder
condition, the convergence of the complete metric first variations to
`β ∫_K √(-g) k^{γb} (G_{bγ} + Λ g_{bγ})`, `Λ = -λ/(2β)` (`eq:supp-einstein-insertion`), `G` the
Einstein tensor of the identified limiting curvature `RL`. -/
theorem renewal_palatini_handoff_literalLink
    (h : RenewalPalatiniLiteralLinkHypotheses Ω score e ω R T eL ωL RL α β lam t) :
    ((∀ n, score n = GravitationalClassDensity.ofCoefficients (holstCoeff (score n))
      (palatiniCoeff (score n)) (volumeCoeff (score n))) ∧
      Tendsto (fun n => (score n).pairing) atTop
        (𝓝 (GravitationalClassDensity.ofCoefficients α β lam).pairing) ∧
      ∀ v : Fin 4 → Fin 4 → ℝ, Tendsto (fun n => (score n).volume v) atTop
        (𝓝 ((GravitationalClassDensity.ofCoefficients α β lam).volume v))) ∧
    IsTorsionFree matAct Ω eL ωL ∧
    ∀ K : Set (Fin 4 → ℝ), IsCompact K → K ⊆ Ω →
      ∃ K' : Set (Fin 4 → ℝ), IsCompact K' ∧ K ⊆ interior K' ∧ K' ⊆ Ω ∧
        (∀ᵐ x ∂(volume.restrict K'), ∀ a, (minkowski * ωL a x)ᵀ = -(minkowski * ωL a x)) ∧
        (∀ᵐ x ∂(volume.restrict K'), 0 < (cfm eL x).det) ∧
        (∀ ω' : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ,
          (∀ a (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ interiorOpens K' →
            MemLp (ω' a) 2 (volume.restrict C)) →
          IsTorsionFree matAct (interiorOpens K') eL ω' →
          (∀ᵐ x, x ∈ interiorOpens K' → ∀ a, (minkowski * ω' a x)ᵀ = -(minkowski * ω' a x)) →
          ∀ᵐ x, x ∈ interiorOpens K' → ∀ a, ω' a x = ωL a x) ∧
        ∀ (k : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
          (H : ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (M : ℝ) (δA : ℕ → ℝ),
          (∀ n, AEStronglyMeasurable (H n) (volume.restrict K)) →
          (∀ n, ∀ᵐ x ∂(volume.restrict K), ‖H n x‖ ≤ M) →
          (∀ᵐ x ∂(volume.restrict K),
            Tendsto (fun n => H n x) atTop (𝓝 (metricTestGenerator minkowski (cfm eL x) (k x)))) →
          Tendsto (classifiedVariationRemainder δA
            (fun n => realizedHolst K (e n) (H n) (R n))
            (fun n => realizedPalatini K (e n) (H n) (R n))
            (fun n => realizedVolume K (e n) (H n))
            (fun n => holstCoeff (score n)) (fun n => palatiniCoeff (score n))
            (fun n => volumeCoeff (score n))) atTop (𝓝 0) →
          Tendsto δA atTop
            (𝓝 (∫ x in K, einsteinInsertionDensity β lam (cfm eL x) (k x) (rcf RL x))) := by
  refine ⟨h.toRenewalPalatiniCommon.classified, h.isTorsionFree, fun K hK hKΩ => ?_⟩
  obtain ⟨K', hK', hKK', hK'Ω⟩ := exists_compact_between hK Ω.isOpen hKΩ
  have hUK' : ((interiorOpens K' : Opens (Fin 4 → ℝ)) : Set (Fin 4 → ℝ)) ⊆ Ω :=
    interior_subset.trans hK'Ω
  choose M6 hM6 hb6 using fun μ => h.coframe_L6 μ K' hK' hK'Ω
  have hM6s : ∑ μ, M6 μ ≠ ∞ := ENNReal.sum_ne_top.2 fun μ _ => hM6 μ
  have hb6s : ∀ n μ, eLpNorm (e n μ) 6 (volume.restrict K') ≤ ∑ μ, M6 μ := fun n μ =>
    (hb6 μ n).trans (Finset.single_le_sum (f := M6) (fun _ _ => zero_le) (Finset.mem_univ μ))
  have hL3 : ∀ a, ∃ M : ℝ≥0∞, M ≠ ∞ ∧ (a ≠ t →
      ∀ n, eLpNorm (ω n a) 3 (volume.restrict K') ≤ M) := fun a => by
    by_cases ha : a = t
    · exact ⟨0, ENNReal.zero_ne_top, fun h' => absurd ha h'⟩
    · obtain ⟨M, hM, hb⟩ := h.spatialConnectionL3Bound a ha K' hK' hK'Ω
      exact ⟨M, hM, fun _ => hb⟩
  choose M3 hM3 hb3 using hL3
  have hM3s : ∑ a, M3 a ≠ ∞ := ENNReal.sum_ne_top.2 fun a _ => hM3 a
  have hb3s : ∀ a, a ≠ t → ∀ n, eLpNorm (ω n a) 3 (volume.restrict K') ≤ ∑ a, M3 a :=
    fun a ha n => (hb3 a ha n).trans
      (Finset.single_le_sum (f := M3) (fun _ _ => zero_le) (Finset.mem_univ a))
  obtain ⟨B, hB, hRb⟩ := h.curvature_bound K' hK' hK'Ω
  have hT' : IsTorsionFree matAct (interiorOpens K') eL ωL := isTorsionFree_mono hUK' h.isTorsionFree
  have hcompat := h.ae_compat K' hK' hK'Ω
  have hdet := h.toRenewalPalatiniCommon.ae_det_pos K' hK' hK'Ω
  have hK'm : MeasurableSet K' := hK'.isClosed.measurableSet
  have hCurv : IsDistributionalCurvature (interiorOpens K') ωL RL := fun ψ a b =>
    h.curvature_identified (liftTest hUK' ψ) a b
  refine ⟨K', hK', hKK', hK'Ω, hcompat, hdet, ?_, ?_⟩
  · intro ω' hω' hT'' hc'
    have hc : ∀ᵐ x, x ∈ interiorOpens K' → ∀ a I J,
        ∑ K, minkowski I K * ωL a x K J = -∑ K, minkowski J K * ωL a x K I := by
      filter_upwards [(ae_restrict_iff' hK'm).1 hcompat] with x hx hxU a I J
      exact compat_index_of_transpose (hx (interior_subset hxU) a) I J
    have hc'' : ∀ᵐ x, x ∈ interiorOpens K' → ∀ a I J,
        ∑ K, minkowski I K * ω' a x K J = -∑ K, minkowski J K * ω' a x K I := by
      filter_upwards [hc'] with x hx hxU a I J
      exact compat_index_of_transpose (hx hxU a) I J
    have hd : ∀ᵐ x, x ∈ interiorOpens K' → (coframeMatrix fun μ => eL μ x).det ≠ 0 := by
      filter_upwards [(ae_restrict_iff' hK'm).1 hdet] with x hx hxU
      exact (hx (interior_subset hxU)).ne'
    have := ae_eq_of_isTorsionFree (Ω := interiorOpens K')
      (fun c C hC hCU => h.coframe_L2.memLp_lim c C hC (hCU.trans hUK'))
      (fun a C hC hCU => h.connection_limit_L2 a C hC (hCU.trans hUK')) hω' hT' hT'' hd hc hc''
    filter_upwards [this] with x hx hxU a
    exact (hx hxU a).symm
  · intro k H M δA hHm hHb hHae hrem
    exact tendsto_firstVariation_einstein (t := t) hK hK' hKK'
      (fun μ => h.coframe_L2.lpTendsto μ hK' hK'Ω) hM6s hb6s
      (fun a => h.connection_limit_L2 a K' hK' hK'Ω)
      (fun a ha => h.spatial_strong a ha K' hK' hK'Ω) hM3s hb3s hT' hcompat hdet hCurv
      (fun n a b => h.curvature_L2 n a b K' hK' hK'Ω)
      (fun a b => h.curvature_limit_L2 a b K' hK' hK'Ω) hB hRb
      (fun a b g hg => h.curvature_weak a b K' hK' hK'Ω g hg) hHm hHb hHae
      h.holst_tendsto h.palatini_tendsto h.volume_tendsto h.palatini_ne_zero hrem

end LiteralLink

/-! ### Non-vacuity of the hypothesis packet -/

section NonVacuity

open BivectorRotationCommutant

theorem det4_expand (Λ : Matrix (Fin 4) (Fin 4) ℝ) : Λ.det =
    Λ 0 0 * (Λ 1 1 * (Λ 2 2 * Λ 3 3 - Λ 2 3 * Λ 3 2) - Λ 1 2 * (Λ 2 1 * Λ 3 3 - Λ 2 3 * Λ 3 1)
      + Λ 1 3 * (Λ 2 1 * Λ 3 2 - Λ 2 2 * Λ 3 1))
    - Λ 0 1 * (Λ 1 0 * (Λ 2 2 * Λ 3 3 - Λ 2 3 * Λ 3 2) - Λ 1 2 * (Λ 2 0 * Λ 3 3 - Λ 2 3 * Λ 3 0)
      + Λ 1 3 * (Λ 2 0 * Λ 3 2 - Λ 2 2 * Λ 3 0))
    + Λ 0 2 * (Λ 1 0 * (Λ 2 1 * Λ 3 3 - Λ 2 3 * Λ 3 1) - Λ 1 1 * (Λ 2 0 * Λ 3 3 - Λ 2 3 * Λ 3 0)
      + Λ 1 3 * (Λ 2 0 * Λ 3 1 - Λ 2 1 * Λ 3 0))
    - Λ 0 3 * (Λ 1 0 * (Λ 2 1 * Λ 3 2 - Λ 2 2 * Λ 3 1) - Λ 1 1 * (Λ 2 0 * Λ 3 2 - Λ 2 2 * Λ 3 0)
      + Λ 1 2 * (Λ 2 0 * Λ 3 1 - Λ 2 1 * Λ 3 0)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [Fin.succAbove, Fin.lt_def]
  ring

/-- The `ε`-pairing of bivectors (the Palatini contraction) is invariant under the induced
action of every unimodular `4 × 4` matrix, in particular of every proper Lorentz matrix. -/
theorem epsilonPairing_invariant (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hdet : Λ.det = 1) :
    (inducedBivectorAction Λ)ᵀ * epsilonPairing * inducedBivectorAction Λ = epsilonPairing := by
  rw [det4_expand] at hdet
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j <;>
    simp [inducedBivectorAction, bivectorPair, epsilonPairing, scalarBlocks, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    first | ring1 | linear_combination hdet | linear_combination -hdet

/-- `L_Palatini` is Lorentz natural. -/
theorem palatiniDensity_isLorentzNatural : RenewalGeometry.palatiniDensity.IsLorentzNatural :=
  fun Λ hΛ => by
    rw [RenewalGeometry.palatiniDensity_pairing]
    exact epsilonPairing_invariant Λ hΛ.det

theorem holstCoeff_palatiniDensity : holstCoeff RenewalGeometry.palatiniDensity = 0 := by
  simp [holstCoeff, epsilonPairing, scalarBlocks]

theorem palatiniCoeff_palatiniDensity : palatiniCoeff RenewalGeometry.palatiniDensity = 1 := by
  simp [palatiniCoeff, epsilonPairing, scalarBlocks]

theorem volumeCoeff_palatiniDensity : volumeCoeff RenewalGeometry.palatiniDensity = 0 := by
  simp [volumeCoeff, RenewalGeometry.palatiniDensity, GravitationalClassDensity.ofCoefficients]

/-- The Cartan map at the basis coframe has a positive lower singular-value bound on
antisymmetric torsion arrays (finite-dimensional injectivity, `cartan_injective_of_isUnit_det`). -/
theorem cartan_floor_basis : ∃ κ : ℝ, 0 < κ ∧ ∀ v : Fin 4 → Fin 4 → Fin 4 → ℝ,
    (∀ I μ ν, v I μ ν = -v I ν μ) →
      κ * ‖v‖ ≤ ‖PalatiniTorsionModel.cartan (fun I μ => (Pi.single μ 1 : Fin 4 → ℝ) I) v‖ := by
  set E : Fin 4 → Fin 4 → ℝ := fun I μ => (Pi.single μ 1 : Fin 4 → ℝ) I
  have hE : (E : Matrix (Fin 4) (Fin 4) ℝ) = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext I μ; simp [E, Pi.single_apply, Matrix.one_apply]
  let S : Submodule ℝ (Fin 4 → Fin 4 → Fin 4 → ℝ) :=
    { carrier := {v | ∀ I μ ν, v I μ ν = -v I ν μ}
      add_mem' := fun {u v} hu hv I μ ν => by
        simp only [Pi.add_apply, hu I μ ν, hv I μ ν]; ring
      zero_mem' := fun I μ ν => by simp
      smul_mem' := fun c v hv I μ ν => by
        simp only [Pi.smul_apply, smul_eq_mul, hv I μ ν]; ring }
  let f : S →ₗ[ℝ] (Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :=
    { toFun := fun v => PalatiniTorsionModel.cartan E v
      map_add' := fun u v => by
        funext I J μ ν ρ
        simp only [PalatiniTorsionModel.cartan, Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun c v => by
        funext I J μ ν ρ
        simp only [PalatiniTorsionModel.cartan, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]; ring }
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    exact PalatiniTorsionModel.cartan_injective_of_isUnit_det E
      (by rw [hE, Matrix.det_one]; exact isUnit_one) v.2 hv
  obtain ⟨K, hK, hA⟩ := f.exists_antilipschitzWith hker
  refine ⟨(K : ℝ)⁻¹, by positivity, fun v hv => ?_⟩
  have h := ZeroHomClass.bound_of_antilipschitz f hA ⟨v, hv⟩
  have hn : ‖(⟨v, hv⟩ : S)‖ = ‖v‖ := rfl
  rw [hn] at h
  rw [inv_mul_le_iff₀ (by positivity)]
  exact h

theorem eulerResidualRep_zero (a b : ℝ) (e : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)) :
    eulerResidualRep a b e (fun _ _ _ => 0) = 0 := by
  funext x I J μ ν ρ
  simp [eulerResidualRep, PalatiniTorsionModel.palatiniApply, PalatiniTorsionModel.cartan,
    torsionArr, PalatiniTorsionModel.capply]

theorem memLp_zero_fun {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {p : ℝ≥0∞}
    {μ : Measure X} : MemLp (fun _ : X => (0 : E)) p μ := MemLp.zero'

theorem eLpNorm_zero_fun {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {p : ℝ≥0∞}
    {μ : Measure X} : eLpNorm (fun _ : X => (0 : E)) p μ = 0 := eLpNorm_zero'

theorem eLpNorm_zero_fun' {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {p : ℝ≥0∞}
    {μ : Measure X} : eLpNorm (0 : X → E) p μ = 0 := eLpNorm_zero

/-- **Non-vacuity of `RenewalPalatiniHypotheses`**: on `Ω = ℝ⁴`, the constant basis coframe
(flat Minkowski metric), the zero connection, curvature and torsion, and the Palatini score
`L_Palatini` (`α = 0`, `β = 1`, `λ = 0`) satisfy every hypothesis, including the amendment. -/
theorem renewalPalatiniHypotheses_flat :
    RenewalPalatiniHypotheses ⊤ (fun _ => RenewalGeometry.palatiniDensity)
      (fun _ μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun _ _ _ => 0) (fun _ _ _ _ => 0)
      (fun _ _ _ _ => 0) (fun μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun _ _ => 0) 0 1 0 0 := by
  have hfin : ∀ C : Set (Fin 4 → ℝ), IsCompact C → IsFiniteMeasure (volume.restrict C) :=
    fun C hC => ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hcfm : ∀ x : Fin 4 → ℝ, cfm (fun μ (_ : Fin 4 → ℝ) => (Pi.single μ 1 : Fin 4 → ℝ)) x = 1 :=
    fun x => coframeMatrix_basis
  obtain ⟨κ, hκ, hfl⟩ := cartan_floor_basis
  refine
    { natural := fun _ => palatiniDensity_isLorentzNatural
      holst_tendsto := by simp only [holstCoeff_palatiniDensity]; exact tendsto_const_nhds
      palatini_tendsto := by simp only [palatiniCoeff_palatiniDensity]; exact tendsto_const_nhds
      volume_tendsto := by simp only [volumeCoeff_palatiniDensity]; exact tendsto_const_nhds
      palatini_ne_zero := one_ne_zero
      coframe_L2 := ⟨fun _ _ C hC _ => by have := hfin C hC; exact memLp_const _,
        fun _ C hC _ => by have := hfin C hC; exact memLp_const _,
        fun _ _ _ _ => by simp⟩
      coframe_L6 := fun c C hC _ => by
        have := hfin C hC
        exact ⟨_, (memLp_const (Pi.single c 1 : Fin 4 → ℝ)).eLpNorm_ne_top (p := 6)
          (μ := volume.restrict C), fun _ => le_rfl⟩
      coframe_oriented := fun _ => Eventually.of_forall fun x _ => by simp [hcfm]
      limit_nondegenerate := Eventually.of_forall fun x _ => by simp [hcfm]
      connection_lorentz := fun _ => Eventually.of_forall fun _ _ _ => by simp
      connection_L2 := ⟨fun _ _ _ _ _ => memLp_zero_fun, fun _ _ _ _ => memLp_zero_fun,
        fun _ _ _ _ => by simp only [sub_self]; rw [eLpNorm_zero_fun']; exact tendsto_const_nhds⟩
      spatialConnectionL3Bound := fun _ _ _ _ _ => ⟨0, ENNReal.zero_ne_top, fun _ =>
        (eLpNorm_zero_fun).le⟩
      torsion_rep := fun _ φ a b => by
        unfold torsionPairing
        have h1 : ∀ v : Fin 4 → ℝ, ∫ x : Fin 4 → ℝ, (φ : (Fin 4 → ℝ) → ℝ) x •
            (matAct (0 : Matrix (Fin 4) (Fin 4) ℝ)) v = 0 := fun v => by simp
        erw [h1, h1]
        simp only [sub_zero, add_zero, smul_zero, integral_zero]
        rw [integral_smul_const, integral_smul_const, integral_pderiv_test, integral_pderiv_test]
        simp
      torsion_antisymm := fun _ _ _ => Eventually.of_forall fun _ _ => by simp
      torsion_L2 := fun _ _ _ _ _ _ => MemLp.zero'
      cartan_floor := ⟨κ, hκ, fun _ => Eventually.of_forall fun x _ v hv => hfl v hv⟩
      euler_residual_tendsto := fun C _ _ => by
        simp only [eulerResidualRep_zero, eLpNorm_zero]; exact tendsto_const_nhds
      curvature_L2 := fun _ _ _ _ _ _ => memLp_zero_fun
      curvature_bound := fun _ _ _ => ⟨0, ENNReal.zero_ne_top, fun _ _ _ =>
        (eLpNorm_zero_fun).le⟩
      curvature_identification := fun φ a b => by simp [curvaturePairing] }

/-- Non-vacuity of the test-level hypotheses of `renewal_palatini_handoff` at the flat
solution: the zero lift converges to the limit lift of the zero test. -/
example (K : Set (Fin 4 → ℝ)) : ∀ᵐ x ∂(volume.restrict K),
    Tendsto (fun _ : ℕ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) atTop
      (𝓝 (metricTestGenerator minkowski
        (cfm (fun μ (_ : Fin 4 → ℝ) => (Pi.single μ 1 : Fin 4 → ℝ)) x) 0)) :=
  Eventually.of_forall fun x => by simp [metricTestGenerator]

/-- **Non-vacuity of `RenewalPalatiniLiteralLinkHypotheses`**: the flat data of
`renewalPalatiniHypotheses_flat` with zero limiting curvature satisfy the literal-link packet. -/
theorem renewalPalatiniLiteralLinkHypotheses_flat :
    RenewalPalatiniLiteralLinkHypotheses ⊤ (fun _ => RenewalGeometry.palatiniDensity)
      (fun _ μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun _ _ _ => 0) (fun _ _ _ _ => 0)
      (fun _ _ _ _ => 0) (fun μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun _ _ => 0)
      (fun _ _ _ => 0) 0 1 0 0 :=
  { renewalPalatiniHypotheses_flat.toRenewalPalatiniCommon with
    connection_L2 := fun _ _ _ _ _ => memLp_zero_fun
    connection_bound := fun _ _ _ _ => ⟨0, ENNReal.zero_ne_top, fun _ => (eLpNorm_zero_fun).le⟩
    connection_limit_L2 := fun _ _ _ _ => memLp_zero_fun
    connection_weak := fun _ _ _ _ _ _ => by simp
    spatial_strong := fun _ _ _ _ _ => ⟨fun _ => memLp_zero_fun, memLp_zero_fun, by
      simp only [sub_self]; rw [eLpNorm_zero_fun']; exact tendsto_const_nhds⟩
    curvature_limit_L2 := fun _ _ _ _ _ => memLp_zero_fun
    curvature_weak := fun _ _ _ _ _ _ _ => by simp
    curvature_identified := fun φ a b => by simp [curvaturePairing] }

end NonVacuity

end RenewalGeometry.RenewalPalatiniHandoff
