/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMFieldSpaces
import RenewalGeometry.StandardModel.FiniteInterfaceRepresentationTable
import RenewalGeometry.Gravity.CoordinateCurvature
import RenewalGeometry.Analysis.SobolevOpenSet

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

open SobolevOpen (pd)

/-! ### Coframe geometry -/

/-- The open lifted slab `(0,T) × ℝ³`. -/
def cylSlab (T : ℝ) : Set E4 := {x | x 0 ∈ Ioo 0 T}

/-- The fundamental domain `(0,T) × [0,1)³` of `M` in the lift. -/
def cylFund (T : ℝ) : Set E4 := {x | x 0 ∈ Ioo 0 T ∧ ∀ i : Fin 3, x i.succ ∈ Ico 0 1}

/-- The metric `g_{μν} = η_{ab} e^a_μ e^b_ν` of a coframe value. -/
def metricAt (e : CoframeFibre) : Matrix (Fin 4) (Fin 4) ℝ := coframeMetric (Matrix.of e)

/-- The inverse metric `g^{μν}`. -/
def metricInv (e : CoframeFibre) : Matrix (Fin 4) (Fin 4) ℝ := (metricAt e)⁻¹

/-- The frame `E^μ_a`, inverse of the coframe. -/
def frameAt (e : CoframeFibre) : Matrix (Fin 4) (Fin 4) ℝ := (Matrix.of e)⁻¹

/-- The volume factor `√|det g|`. -/
def volFactor (e : CoframeFibre) : ℝ := Real.sqrt |(metricAt e).det|

/-- Metric jet `∂_i g_{μν}`. -/
def dMetric (e : E4 → CoframeFibre) (x : E4) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun i μ ν => pd (fun y => metricAt (e y) μ ν) i x

/-- Christoffel symbols `Γ^c_{ij}` of `g = eᵀηe`. -/
def christoffelF (e : E4 → CoframeFibre) (x : E4) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffel (metricInv (e x)) (dMetric e x)

/-- Connection jet `∂_c Γ^a_{db}`. -/
def dChristoffelF (e : E4 → CoframeFibre) (x : E4) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun c a d b => pd (fun y => christoffelF e y a d b) c x

/-- Scalar curvature `Scal(g)` of `g = eᵀηe`. -/
def scalarCurvF (e : E4 → CoframeFibre) (x : E4) : ℝ :=
  scalarCurv (metricInv (e x)) (christoffelF e x) (dChristoffelF e x)

/-! ### Gauge and Higgs sectors -/

/-- Curvature `F_{μν} = ∂_μA_ν - ∂_νA_μ + [A_μ, A_ν]` (`eq:curvature-higgs`). -/
def curvatureF (A : E4 → ConnFibre) (x : E4) (μ ν : Fin 4) : LieFibre :=
  pd (fun y => A y ν) μ x - pd (fun y => A y μ) ν x + comm (A x μ) (A x ν)

/-- Covariant Higgs derivative `K_μ = (D_AH)_μ = ∂_μH + ρ_H(A_μ)H` (`eq:curvature-higgs`). -/
def covDerivHiggs (A : E4 → ConnFibre) (H : E4 → HiggsFibre) (x : E4) (μ : Fin 4) :
    HiggsFibre :=
  pd H μ x + higgsAct (A x μ) (H x)

/-- The colour block `X₃` of `X ∈ smLie`. -/
def block3 (X : LieFibre) : Fin 3 → Fin 3 → ℂ := fun i j => X (Fin.castAdd 2 i) (Fin.castAdd 2 j)

/-- The weak block `X₂` of `X ∈ smLie`. -/
def block2 (X : LieFibre) : Fin 2 → Fin 2 → ℂ := fun i j => X (Fin.natAdd 3 i) (Fin.natAdd 3 j)

/-- Matrix trace. -/
def mtrace {n : ℕ} (X : Fin n → Fin n → ℂ) : ℂ := ∑ i, X i i

/-- Traceless part `X - (tr X / n) 1`. -/
def traceless {n : ℕ} (X : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun i j => X i j - if i = j then mtrace X / n else 0

/-- **The positive invariant metric on `𝔰(𝔲(3)⊕𝔲(2))` with the three coefficients `g_j^{-2}`**:
`g₃^{-2}(-2 Re tr X₃'Y₃') + g₂^{-2}(-2 Re tr X₂'Y₂') + g₁^{-2} b_X b_Y`, with `X_j'` the traceless
blocks and `b_X = Im tr X₂` the hypercharge coordinate. -/
def lieMetric {Y : Type} (θ : CoefficientBank Y) (X Z : LieFibre) : ℝ :=
  (θ.g3 ^ 2)⁻¹ * (-2 * (mtrace (mmul (traceless (block3 X)) (traceless (block3 Z)))).re) +
  (θ.g2 ^ 2)⁻¹ * (-2 * (mtrace (mmul (traceless (block2 X)) (traceless (block2 Z)))).re) +
  (θ.g1 ^ 2)⁻¹ * ((mtrace (block2 X)).im * (mtrace (block2 Z)).im)

/-- Yang–Mills density `-¼ g^{μα}g^{νβ}⟨F_{μν}, F_{αβ}⟩_𝔤`. -/
def ymDensity {Y : Type} (θ : CoefficientBank Y) (e : E4 → CoframeFibre) (A : E4 → ConnFibre)
    (x : E4) : ℝ :=
  -(1 / 4) * ∑ μ, ∑ ν, ∑ α, ∑ β, metricInv (e x) μ α * metricInv (e x) ν β *
    lieMetric θ (curvatureF A x μ ν) (curvatureF A x α β)

/-- Hermitian product on the Higgs fibre. -/
def hInner (u v : HiggsFibre) : ℂ := ∑ i, star (u i) * v i

/-- Higgs kinetic density `-g^{μν} Re⟨D_μH, D_νH⟩`. -/
def higgsKinetic (e : E4 → CoframeFibre) (A : E4 → ConnFibre) (H : E4 → HiggsFibre) (x : E4) :
    ℝ :=
  -∑ μ, ∑ ν, metricInv (e x) μ ν * (hInner (covDerivHiggs A H x μ) (covDerivHiggs A H x ν)).re

/-- Higgs potential `V(H) = λ_H(|H|² - v_H²)²`. -/
def higgsPotential {Y : Type} (θ : CoefficientBank Y) (v : HiggsFibre) : ℝ :=
  θ.lambdaH * (∑ i, Complex.normSq (v i) - θ.vH ^ 2) ^ 2

/-! ### Dirac sector -/

/-- Weyl-basis Clifford matrices for `η = diag(-1,1,1,1)`:
`γ⁰ = i[[0,1],[1,0]]`, `γ^k = i[[0,σ_k],[-σ_k,0]]`. -/
def gammaW : Fin 4 → Fin 4 → Fin 4 → ℂ :=
  ![![![0, 0, Complex.I, 0], ![0, 0, 0, Complex.I], ![Complex.I, 0, 0, 0],
      ![0, Complex.I, 0, 0]],
    ![![0, 0, 0, Complex.I], ![0, 0, Complex.I, 0], ![0, -Complex.I, 0, 0],
      ![-Complex.I, 0, 0, 0]],
    ![![0, 0, 0, 1], ![0, 0, -1, 0], ![0, -1, 0, 0], ![1, 0, 0, 0]],
    ![![0, 0, Complex.I, 0], ![0, 0, 0, -Complex.I], ![-Complex.I, 0, 0, 0],
      ![0, Complex.I, 0, 0]]]

/-- **Clifford relation** `γ^aγ^b + γ^bγ^a = 2η^{ab}` for `η = diag(-1,1,1,1)`. -/
theorem gammaW_clifford (a b : Fin 4) :
    mmul (gammaW a) (gammaW b) + mmul (gammaW b) (gammaW a) =
      fun i j => if i = j then (2 * minkowskiEta a b : ℂ) else 0 := by
  funext i j
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [mmul, gammaW, Fin.sum_univ_four, minkowskiEta, Matrix.diagonal] <;> ring_nf

/-- The Clifford matrices are block off-diagonal in the Weyl basis, i.e. they anticommute with
`γ₅ = diag(1,1,-1,-1)`: they exchange the chiral components used by `IsChiral`. -/
theorem gammaW_offDiag (a s s' : Fin 4) (h : ((s : ℕ) < 2) = ((s' : ℕ) < 2)) :
    gammaW a s s' = 0 := by
  fin_cases a <;> fin_cases s <;> fin_cases s' <;> simp_all [gammaW]

/-- Internal fermion data on the fixed carrier (finite rank, unitary internal representation,
affine Yukawa map): the part of the finite interface the continuum Dirac–Yukawa density uses. -/
structure FermionCarrier (Ysec : Type) where
  /-- carrier index (chiral rows × internal × generation) -/
  C : Type
  [fintype : Fintype C]
  /-- chirality of the carrier rows (`true` = left-handed) -/
  left : C → Bool
  /-- the retained gauge representation `ρ_F` on the carrier -/
  rho : LieFibre →ₗ[ℝ] (C → C → ℂ)
  /-- unitarity: `ρ_F(X)` is skew-Hermitian for `X ∈ smLie` -/
  rho_skew : ∀ X ∈ smLie, ∀ c c', rho X c' c = -star (rho X c c')
  /-- `ρ_F` is a Lie-algebra homomorphism -/
  rho_bracket : ∀ X ∈ smLie, ∀ Z ∈ smLie, rho (comm X Z) = comm (rho X) (rho Z)
  /-- `ρ_F` preserves chirality -/
  rho_chiral : ∀ X c c', left c ≠ left c' → rho X c c' = 0
  /-- the Dirac/Yukawa coupling `𝓜_Y(H)`, real-affine in the Higgs field -/
  yukawa : CoefficientBank Ysec → HiggsFibre →ᵃ[ℝ] (C → C → ℂ)
  /-- infinitesimal gauge covariance of `Ψ̄ 𝓜_Y(H) Ψ` -/
  yukawa_covariant : ∀ θ, ∀ X ∈ smLie, ∀ v,
    (yukawa θ).linear (higgsAct X v) = comm (rho X) (yukawa θ v)

attribute [instance] FermionCarrier.fintype

variable {Ysec : Type} [Fintype Ysec]

/-- Levi-Civita spin connection `ω_μ^a_b = e^a_ν(∂_μE^ν_b + Γ^ν_{μλ}E^λ_b)`. -/
def spinConn (e : E4 → CoframeFibre) (x : E4) (μ a b : Fin 4) : ℝ :=
  ∑ ν, e x a ν * (pd (fun y => frameAt (e y) ν b) μ x +
    ∑ l, christoffelF e x ν μ l * frameAt (e x) l b)

/-- Spinor connection `Ω_μ = ¼ ω_{μab} γ^a γ^b`, `ω_{μab} = η_{ac} ω_μ^c_b`. -/
def spinGen (e : E4 → CoframeFibre) (x : E4) (μ : Fin 4) : Fin 4 → Fin 4 → ℂ :=
  fun s s' => (1 / 4 : ℂ) * ∑ a, ∑ b,
    ((∑ c, minkowskiEta a c * spinConn e x μ c b : ℝ) : ℂ) * mmul (gammaW a) (gammaW b) s s'

/-- Curved Clifford matrices `γ^μ = E^μ_a γ^a`. -/
def curvedGamma (e : E4 → CoframeFibre) (x : E4) (μ : Fin 4) : Fin 4 → Fin 4 → ℂ :=
  fun s s' => ∑ a, (frameAt (e x) μ a : ℂ) * gammaW a s s'

/-- `∇^{e,A}_μ Ψ = ∂_μΨ + Ω_μΨ + ρ_F(A_μ)Ψ`. -/
def covDerivSpinor (FC : FermionCarrier Ysec) (e : E4 → CoframeFibre) (A : E4 → ConnFibre)
    (Ψ : E4 → SpinorFibre FC.C) (x : E4) (μ : Fin 4) : SpinorFibre FC.C :=
  fun s c => pd Ψ μ x s c + ∑ s', spinGen e x μ s s' * Ψ x s' c +
    ∑ c', FC.rho (A x μ) c c' * Ψ x s c'

/-- Dual covariant derivative `∇_μΨ̄ = ∂_μΨ̄ - Ψ̄Ω_μ - Ψ̄ρ_F(A_μ)`. -/
def covDerivCospinor (FC : FermionCarrier Ysec) (e : E4 → CoframeFibre) (A : E4 → ConnFibre)
    (Ψb : E4 → SpinorFibre FC.C) (x : E4) (μ : Fin 4) : SpinorFibre FC.C :=
  fun s c => pd Ψb μ x s c - ∑ s', Ψb x s' c * spinGen e x μ s' s -
    ∑ c', Ψb x s c' * FC.rho (A x μ) c' c

/-- **Dirac–Yukawa density** (`eq:dirac-density`):
`Re{ (i/2)[Ψ̄γ^μ∇_μΨ - (∇_μΨ̄)γ^μΨ] - Ψ̄𝓜_Y(H)Ψ }`. -/
def diracDensity (FC : FermionCarrier Ysec) (θ : CoefficientBank Ysec) (z : FieldTuple FC.C)
    (x : E4) : ℝ :=
  ((Complex.I / 2) * ∑ μ, ∑ s, ∑ s', ∑ c,
      (z.Ψb x s c * curvedGamma z.e x μ s s' * covDerivSpinor FC z.e z.A z.Ψ x μ s' c -
        covDerivCospinor FC z.e z.A z.Ψb x μ s c * curvedGamma z.e x μ s s' * z.Ψ x s' c) -
    ∑ s, ∑ c, ∑ c', z.Ψb x s c * FC.yukawa θ (z.H x) c c' * z.Ψ x s c').re

/-- Standard-Model density `𝓛_{SM,θ} dV_g` (`eq:SM-action`). -/
def smDensity (FC : FermionCarrier Ysec) (θ : CoefficientBank Ysec) (z : FieldTuple FC.C)
    (x : E4) : ℝ :=
  (ymDensity θ z.e z.A x + higgsKinetic z.e z.A z.H x - higgsPotential θ (z.H x) +
    diracDensity FC θ z x) * volFactor (z.e x)

/-- Gravitational density `(Scal(g) - 2Λ)/(2κ) dV_g` (`eq:total-action`). -/
def gravityDensity (θ : CoefficientBank Ysec) (e : E4 → CoframeFibre) (x : E4) : ℝ :=
  (scalarCurvF e x - 2 * θ.Lambda) / (2 * θ.kappa) * volFactor (e x)

/-- The two action sectors `b ∈ {g, SM}`. -/
inductive Sector
  | gravity
  | standardModel
  deriving DecidableEq

instance : Fintype Sector :=
  ⟨{.gravity, .standardModel}, by intro x; cases x <;> simp⟩

/-- The sector density `𝓛_{b,θ}`. -/
def sectorDensity (FC : FermionCarrier Ysec) (θ : CoefficientBank Ysec) :
    Sector → FieldTuple FC.C → E4 → ℝ
  | .gravity => fun z => gravityDensity θ z.e
  | .standardModel => fun z => smDensity FC θ z

/-- The symmetric coframe lift `ė^a_μ(k) = -½ e^a_α g_{μβ} k^{αβ}` (`eq:metric-lift`). -/
def metricLift (e k : E4 → CoframeFibre) : E4 → CoframeFibre :=
  fun x a μ => -(1 / 2) * ∑ α, ∑ β, e x a α * metricAt (e x) μ β * k x α β

/-- The complete field variation `v̂ = (ė(k), a, η_H, η_Ψ, η_Ψ̄)` of a test `v` at `z`. -/
def variationDirection {C : Type} (z v : FieldTuple C) : FieldTuple C :=
  FieldTuple.mk (metricLift z.e v.e) v.A v.H v.Ψ v.Ψb

/-- First variation `d/dε|₀ ∫_M (𝓛(z + εw) - 𝓛(z))` (integral over the fundamental domain). -/
def actionVariation {C : Type} (T : ℝ) (L : FieldTuple C → E4 → ℝ) (z w : FieldTuple C) : ℝ :=
  deriv (fun ε : ℝ => ∫ x in cylFund T, (L (z + ε • w) x - L z x)) 0

/-- **`D𝒮_{b,θ}(z)[v]`**: the complete first variation of the continuum sector action along
the physical test `v`. -/
def firstVariation (T : ℝ) (FC : FermionCarrier Ysec) (θ : CoefficientBank Ysec) (b : Sector)
    (z v : FieldTuple FC.C) : ℝ :=
  actionVariation T (sectorDensity FC θ b) z (variationDirection z v)

/-! ### Smooth reconstructed fields -/

/-- Smooth local fields `z = (e, A, H, Ψ, Ψ̄)` on `M = (0,T) × 𝕋³`: `C^∞` on the open slab,
spatially periodic, `A` valued in `smLie`, spinors in the chiral bundles. -/
structure SmoothFields (T : ℝ) {C : Type} [Fintype C] (left : C → Bool) where
  /-- the field tuple -/
  z : FieldTuple C
  smooth_e : ContDiffOn ℝ ∞ z.e (cylSlab T)
  smooth_A : ContDiffOn ℝ ∞ z.A (cylSlab T)
  smooth_H : ContDiffOn ℝ ∞ z.H (cylSlab T)
  smooth_Ψ : ContDiffOn ℝ ∞ z.Ψ (cylSlab T)
  smooth_Ψb : ContDiffOn ℝ ∞ z.Ψb (cylSlab T)
  periodic_e : ∀ n x, z.e (x + spatialShift n) = z.e x
  periodic_A : ∀ n x, z.A (x + spatialShift n) = z.A x
  periodic_H : ∀ n x, z.H (x + spatialShift n) = z.H x
  periodic_Ψ : ∀ n x, z.Ψ (x + spatialShift n) = z.Ψ x
  periodic_Ψb : ∀ n x, z.Ψb (x + spatialShift n) = z.Ψb x
  lie : ∀ x μ, z.A x μ ∈ smLie
  chiral : ∀ x, IsChiral left (z.Ψ x)
  cochiral : ∀ x, IsCoChiral left (z.Ψb x)

/-- The identity coframe `e^a_μ = δ^a_μ` (flat Minkowski metric). -/
def flatCoframe : CoframeFibre := fun a μ => if a = μ then 1 else 0

/-- Constant fields (identity coframe, constant `A ∈ smLie`, constant Higgs, zero spinors). -/
def constFields (T : ℝ) {C : Type} [Fintype C] (left : C → Bool) (A₀ : ConnFibre)
    (hA₀ : ∀ μ, A₀ μ ∈ smLie)
    (H₀ : HiggsFibre) : SmoothFields T left where
  z := FieldTuple.mk (fun _ => flatCoframe) (fun _ => A₀) (fun _ => H₀) 0 0
  smooth_e := contDiffOn_const
  smooth_A := contDiffOn_const
  smooth_H := contDiffOn_const
  smooth_Ψ := contDiffOn_const
  smooth_Ψb := contDiffOn_const
  periodic_e _ _ := rfl
  periodic_A _ _ := rfl
  periodic_H _ _ := rfl
  periodic_Ψ _ _ := rfl
  periodic_Ψb _ _ := rfl
  lie _ μ := hA₀ μ
  chiral _ _ _ _ := rfl
  cochiral _ _ _ _ := rfl

/-! ### Regulator sequences (`def:regulator`) -/

/-- Transport of a coefficient bank along an identification of Yukawa sectors. -/
def _root_.RenewalGeometry.CoefficientBank.reindex {Y Y' : Type} (θ : CoefficientBank Y)
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

/-- The trivial fermion carrier (one left-handed row, `ρ_F = 0`, `𝓜_Y = 0`). -/
def trivialCarrier (Ysec : Type) : FermionCarrier Ysec where
  C := Unit
  left _ := true
  rho := 0
  rho_skew _ _ _ _ := by simp
  rho_bracket _ _ _ _ := by funext i j; simp [comm, mmul]
  rho_chiral _ _ _ h := absurd rfl h
  yukawa _ := AffineMap.const ℝ _ 0
  yukawa_covariant _ _ _ _ := by funext i j; simp [comm, mmul]

/-- A compact enlargement `K ⊂ int K' ⋐ M` of a compact region. -/
theorem CylRegion.exists_enlarge {T : ℝ} (K : CylRegion T) :
    ∃ K' : CylRegion T, K.carrier ⊆ interior K'.carrier := by
  have hopen : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set (UnitAddTorus (Fin 3)))) :=
    isOpen_Ioo.prod isOpen_univ
  obtain ⟨δ, hδ, hsub⟩ := K.isCompact.exists_cthickening_subset_open hopen K.subset
  refine ⟨⟨Metric.cthickening δ K.carrier, K.isCompact.cthickening, hsub⟩, ?_⟩
  exact (Metric.self_subset_thickening hδ _).trans
    (interior_maximal (Metric.thickening_subset_cthickening _ _) Metric.isOpen_thickening)

/-- A choice of enlargement. -/
def CylRegion.enlarge {T : ℝ} (K : CylRegion T) : CylRegion T := K.exists_enlarge.choose

theorem CylRegion.subset_interior_enlarge {T : ℝ} (K : CylRegion T) :
    K.carrier ⊆ interior K.enlarge.carrier := K.exists_enlarge.choose_spec

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
