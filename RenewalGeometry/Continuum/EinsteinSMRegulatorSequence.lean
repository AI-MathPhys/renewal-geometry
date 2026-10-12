/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.EinsteinSMFieldSpaces
import RenewalGeometry.StandardModel.FiniteInterfaceRepresentationTable
import MathPhys.FieldTheory.Gravity.CoordinateCurvature
import MathPhys.FieldTheory.Analysis.SobolevOpenSet
import MathPhys.FieldTheory.Continuum.EinsteinSMContinuumAction
open MathPhys

/-!
# The continuum Einstein–Standard-Model action and finite-interface regulator sequences
  (`def:regulator`, Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMFieldSpaces.lean` (cylinder `M = (0,T) × 𝕋³` lifted to `ℝ⁴`,
trivialised bundles, flat comparison data); `pd φ i x = Dφ(x) e_i` is the coordinate partial
derivative.

## The continuum action (`eq:SM-action`, `eq:dirac-density`, `eq:total-action`)

`def:regulator` compares the finite action with the *continuum* action `𝒮_{b,θ}` evaluated on
the reconstructed smooth fields.  The Lagrangian densities are written out literally in the
coordinates of the lift:

* gravity: `gravityDensity θ e = (Scal(g) - 2Λ)/(2κ) · √|det g|`, `g = eᵀ η e`, with the
  Christoffel symbols / Riemann / Ricci / scalar curvature of `Gravity/CoordinateCurvature.lean`
  (curvature convention `[∇_μ,∇_ν]v^ρ = R^ρ_{σμν}v^σ`, `Ric_{σν} = R^ρ_{σρν}`);
* Yang–Mills: `-¼ g^{μα}g^{νβ}⟨F_{μν},F_{αβ}⟩_𝔤`, `F = dA + A∧A` (`curvatureF`), with the
  invariant metric `lieMetric θ` having the three coefficients `g_j^{-2}` on the `𝔰𝔲(3)`,
  `𝔰𝔲(2)` and hypercharge parts (normalisation `-2 tr` on `𝔰𝔲(N)`, hypercharge
  `Y = diag(-⅓,-⅓,-⅓,½,½)`: these base normalisations are not fixed by the manuscript, which only
  names the coefficients `g_j^{-2}` — disclosed);
* Higgs: `-g^{μν} Re⟨D_μH, D_νH⟩ - λ_H(|H|²-v_H²)²`, `D_AH = dH + ρ_H(A)H` (`covDerivHiggs`);
* Dirac–Yukawa (`eq:dirac-density`):
  `Re{ (i/2)[Ψ̄ γ^μ ∇_μΨ - (∇_μΨ̄) γ^μ Ψ] - Ψ̄ 𝓜_Y(H) Ψ }` with Weyl-basis Clifford matrices
  `gammaW` for `η = diag(-1,1,1,1)` (`gammaW_clifford`, `gammaW_offDiag`), `γ^μ = E^μ_a γ^a`,
  the Levi-Civita spin
  connection `ω_μ^a_b = e^a_ν(∂_μE^ν_b + Γ^ν_{μλ}E^λ_b)` of `e` and `∇_μ = ∂_μ + ¼ω_{μab}γ^aγ^b
  + ρ_F(A_μ)`; all sectors multiplied by `dV_g = √|det g| d⁴x`.

The internal fermion data enter through `FermionCarrier`: a finite carrier index type, its
chirality labels, an `ℝ`-linear unitary (skew-Hermitian-valued) Lie-algebra action `ρ_F`
preserving chirality and brackets, and a real-affine Yukawa map `𝓜_Y(H)` (with constant
Majorana part allowed), infinitesimally gauge covariant.  The manuscript fixes these only
through the finite interface (`def:finite-interface`, `tab:SM-representations`) and states that
"the analytic arguments below use their finite rank, unitarity of the internal representations
and the affine Higgs dependence of the Yukawa map" — exactly the fields of `FermionCarrier`.

The complete metric variation along a test `v = (k, a, η_H, η_Ψ, η_Ψ̄)` uses the symmetric
coframe lift `ė^a_μ(k) = -½ e^a_α g_{μβ} k^{αβ}` (`eq:metric-lift`, `metricLift`), spinor
components held fixed in the spin-frame identification, and
`D𝒮_{b,θ}(z)[v] = d/dε|₀ ∫_M (𝓛_b(z + ε v̂) - 𝓛_b(z))` (`firstVariation`), the integral over
the fundamental domain `(0,T) × [0,1)³` of the lift; since `v` is compactly supported the
integrand vanishes off `supp v`, and the spin-connection variation is *not* dropped.

## `def:regulator`

`RegulatorSequence T FC` bundles: the fixed regulator order `r₀ ≥ 4`; a cofinal cutoff
sequence `h_n ↓ 0`; finite interfaces `𝔍_{h_n}` (the ledger encoding `TabulatedFiniteInterface`
of `def:finite-interface`) with a fixed identification of their Yukawa sectors; finite
configurations `z_h^d`; reconstruction maps `R_h` into smooth spatially periodic fields on `M`
(`SmoothFields`); a site-local decomposition of `𝒬_h` (positions of sites in `M`, projections
onto site degrees of freedom, compatible with the local coframe/Higgs readers) giving meaning to
"supported in a region"; a fixed enlargement `K ↦ K'` with `K ⊂ int K'`; and linear test lifts
`𝓘_h : 𝒱_K → T_{z_h^d}𝒬_h = 𝒬_h` supported in `K'`.  The defects of `eq:C1-consistency` and
`eq:stationarity` are `consistencyDefect` and `stationarityDefect`, suprema over the `C^{r₀}`
unit ball of `𝒱_K`, valued in `ℝ≥0∞` (no boundedness presupposed); the finite sector actions
are `𝒮_{g,h}` and `𝒮_{SM,h} = ν 𝒮_matter` of the library interface (so that
`𝒮_h = 𝒮_{g,h} + 𝒮_{SM,h}`), whose sectorwise differentiability at `z_h^d` is required.
`FirstVariationConsistent` (`c_h(K) → 0`) and `PhysicallyStationary` (`ε_h(K) → 0`) for every
`K`.  Non-vacuity: `trivialRegulator` (flat fields, zero action), which is physically
stationary (`trivialRegulator_stationary`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

namespace RenewalGeometry
namespace EinsteinSM
open MathPhys.EinsteinSM

open SobolevOpen (pd)

variable {Ysec : Type} [Fintype Ysec]

/-! ### Regulator sequences (`def:regulator`) -/

/-- Transport of a coefficient bank along an identification of Yukawa sectors. -/
def _root_.MathPhys.CoefficientBank.reindex {Y Y' : Type} (θ : CoefficientBank Y)
    (σ : Y ≃ Y') :
    CoefficientBank Y' :=
  { θ with yukawa := fun y => θ.yukawa (σ.symm y) }

/-- **`def:regulator`: a finite-interface regulator sequence.** -/
structure RegulatorSequence (T : ℝ) (FC : FermionCarrier Ysec) where
  /-- the fixed regulator order `r₀` -/
  r0 : ℕ
  four_le_r0 : 4 ≤ r0
  /-- the cofinal cutoffs `h ↓ 0` -/
  cutoff : ℕ → ℝ
  cutoff_pos : ∀ n, 0 < cutoff n
  cutoff_tendsto : Tendsto cutoff atTop (𝓝 0)
  /-- the structural interfaces `𝔍_h` of `def:finite-interface` -/
  iface : ∀ n, TabulatedFiniteInterface (cutoff n)
  /-- fixed identification of the Yukawa sectors (the bank `θ_h` is carried by `𝔍_h`) -/
  yukawaEquiv : ∀ n, (iface n).YukawaSector ≃ Ysec
  /-- the finite configurations `z_h^d ∈ 𝒬_h` -/
  config : ∀ n, (iface n).Config
  /-- the analytic reconstruction maps `R_h` into smooth local fields on `M` -/
  recon : ∀ n, (iface n).Config → SmoothFields T FC.left
  /-- the finite sector actions are differentiable at `z_h^d` -/
  gravity_differentiable : ∀ n, DifferentiableAt ℝ (iface n).gravityAction (config n)
  matter_differentiable : ∀ n, DifferentiableAt ℝ (iface n).matterAction (config n)
  /-- positions of the finite sites in `M` -/
  sitePos : ∀ n, (iface n).Site → ℝ × UnitAddTorus (Fin 3)
  /-- projections of `𝒬_h` onto the degrees of freedom of each site -/
  siteComp : ∀ n, (iface n).Site → (iface n).Config →ₗ[ℝ] (iface n).Config
  siteComp_sum : ∀ n q, ∑ x, siteComp n x q = q
  siteComp_idem : ∀ n x q, siteComp n x (siteComp n x q) = siteComp n x q
  siteComp_orth : ∀ n x y q, x ≠ y → siteComp n x (siteComp n y q) = 0
  /-- the local coframe and Higgs readers at a site only see that site's degrees of freedom -/
  coframe_local : ∀ n x q q', siteComp n x q = siteComp n x q' →
    (iface n).coframe q x = (iface n).coframe q' x
  higgs_local : ∀ n x q q', siteComp n x q = siteComp n x q' →
    (iface n).higgs q x = (iface n).higgs q' x
  /-- the fixed slightly larger region `K'` -/
  enlarge : CylRegion T → CylRegion T
  enlarge_sub : ∀ K, K.carrier ⊆ interior (enlarge K).carrier
  /-- the linear physical test lifts `𝓘_h : 𝒱_K → T_{z_h^d}𝒬_h` -/
  lift : ∀ n (K : CylRegion T), ↥(testSubmodule FC.left K) →ₗ[ℝ] (iface n).Config
  /-- `𝓘_h v` is supported in `K'` -/
  lift_support : ∀ n K v x, sitePos n x ∉ (enlarge K).carrier → siteComp n x (lift n K v) = 0

namespace RegulatorSequence

variable {T : ℝ} {FC : FermionCarrier Ysec} (reg : RegulatorSequence T FC)

/-- The coefficient bank `θ_h` carried by `𝔍_h`. -/
def bank (n : ℕ) : CoefficientBank Ysec :=
  ((reg.iface n).coefficients).reindex (reg.yukawaEquiv n)

/-- The reconstructed fields `z_h = R_h(z_h^d)`. -/
def fields (n : ℕ) : SmoothFields T FC.left := reg.recon n (reg.config n)

/-- The finite sector first variation `D𝒮_{b,h}(z_h^d)[w]` (`𝒮_{SM,h} = ν 𝒮_matter`). -/
def finiteSectorVariation (n : ℕ) : Sector → (reg.iface n).Config → ℝ
  | .gravity => fun w => fderiv ℝ (reg.iface n).gravityAction (reg.config n) w
  | .standardModel => fun w => fderiv ℝ (fun q => (reg.iface n).relativeNormalization *
      (reg.iface n).matterAction q) (reg.config n) w

/-- **First-variation consistency defect `c_h(K)`** (`eq:C1-consistency`):
`Σ_b sup_{v ∈ 𝒱_K, ‖v‖_{C^{r₀}} ≤ 1} |D𝒮_{b,h}(z_h^d)[𝓘_hv] - D𝒮_{b,θ_h}(z_h)[v]|`. -/
def consistencyDefect (n : ℕ) (K : CylRegion T) : ℝ≥0∞ :=
  ∑ b : Sector, ⨆ (v : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 v.1 ≤ 1),
    ENNReal.ofReal |reg.finiteSectorVariation n b (reg.lift n K v) -
      firstVariation T FC (reg.bank n) b (reg.fields n).z v.1|

/-- **Stationarity defect `ε_h(K)`** (`eq:stationarity`):
`sup_{v ∈ 𝒱_K, ‖v‖_{C^{r₀}} ≤ 1} |D𝒮_h(z_h^d)[𝓘_hv]|`. -/
def stationarityDefect (n : ℕ) (K : CylRegion T) : ℝ≥0∞ :=
  ⨆ (v : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 v.1 ≤ 1),
    ENNReal.ofReal |fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)|

/-- **First-variation consistency**: `c_h(K) → 0` for every `K ⋐ M`. -/
def FirstVariationConsistent : Prop :=
  ∀ K : CylRegion T, Tendsto (fun n => reg.consistencyDefect n K) atTop (𝓝 0)

/-- **Physical common-action stationarity**: `ε_h(K) → 0` for every `K ⋐ M`. -/
def PhysicallyStationary : Prop :=
  ∀ K : CylRegion T, Tendsto (fun n => reg.stationarityDefect n K) atTop (𝓝 0)

omit [Fintype Ysec] in
/-- The finite common action is the sum of the two sectors: `D𝒮_h = D𝒮_{g,h} + D𝒮_{SM,h}`. -/
theorem fderiv_action_eq_sum (n : ℕ) (w : (reg.iface n).Config) :
    fderiv ℝ (reg.iface n).action (reg.config n) w =
      reg.finiteSectorVariation n .gravity w + reg.finiteSectorVariation n .standardModel w := by
  have h1 := reg.gravity_differentiable n
  have h2 := (reg.matter_differentiable n).const_mul (reg.iface n).relativeNormalization
  have : (reg.iface n).action = fun q => (reg.iface n).gravityAction q +
      (reg.iface n).relativeNormalization * (reg.iface n).matterAction q := rfl
  rw [this, fderiv_fun_add h1 h2]
  rfl

end RegulatorSequence

/-! ### Non-vacuity -/

/-- **Non-vacuity of `def:regulator`**: flat constant reconstructions over the trivial
interfaces `𝔍_{1/(n+1)}`, zero test lifts. -/
def trivialRegulator (T : ℝ) : RegulatorSequence T (trivialCarrier Unit) where
  r0 := 4
  four_le_r0 := le_rfl
  cutoff n := 1 / ((n : ℝ) + 1)
  cutoff_pos n := by positivity
  cutoff_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
  iface n := TabulatedFiniteInterface.trivialGeometryInterface _ .minimal
  yukawaEquiv _ := Equiv.refl _
  config _ := (0 : ℝ)
  recon _ _ := constFields T _ 0 (fun _ => smLie.zero_mem) 0
  gravity_differentiable _ := differentiableAt_const _
  matter_differentiable _ := differentiableAt_const _
  sitePos _ _ := (0, 0)
  siteComp _ _ := LinearMap.id
  siteComp_sum _ q := by show ∑ _x : Unit, q = q; simp
  siteComp_idem _ _ _ := rfl
  siteComp_orth _ x y _ h := absurd (Subsingleton.elim (α := Unit) x y) h
  coframe_local _ _ q q' h := by simp only [LinearMap.id_apply] at h; rw [h]
  higgs_local _ _ q q' h := by simp only [LinearMap.id_apply] at h; rw [h]
  enlarge K := K.enlarge
  enlarge_sub K := K.subset_interior_enlarge
  lift _ _ := 0
  lift_support _ _ _ _ _ := by simp

/-- The trivial regulator is physically stationary (its finite action vanishes identically). -/
theorem trivialRegulator_stationary (T : ℝ) : (trivialRegulator T).PhysicallyStationary := by
  intro K
  have : ∀ n, (trivialRegulator T).stationarityDefect n K = 0 := by
    intro n
    simp only [RegulatorSequence.stationarityDefect]
    refine le_antisymm (iSup₂_le fun v _ => ?_) zero_le
    have h0 : (trivialRegulator T).lift n K v = 0 := by rfl
    rw [h0, map_zero, abs_zero, ENNReal.ofReal_zero]
  simp only [this]
  exact tendsto_const_nhds

end EinsteinSM
end RenewalGeometry
