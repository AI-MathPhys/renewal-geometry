/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.StandardModel.SMGaugeQuotientExact

/-!
# Finite classical Einstein–Standard-Model interface
  (`def:finite-interface`, Einstein–Standard-Model action-closure manuscript)

The structural finite-interface record `𝔍_h` of `def:finite-interface`,
bundling the five data items:

* (I1) `FiniteInterface.Config`: a finite-dimensional configuration chart
  `𝒬_h` over a finite site set, with local coframe variables
  `coframe q x ∈ GL(4,ℝ)` whose reconstructed metric
  `eᵀ η e` is Lorentzian, oriented (`det e > 0`) and time-oriented
  (`e⁰₀ > 0`);
* (I2) the fixed finite-rank Standard-Model bundle type: the gauge group
  is `SMGaugeGroup = S(U(3)×U(2))` (with its `ℤ₆`-quotient presentation
  `smGaugeQuotientEquiv` of `eq:gauge-group`), one retained chiral
  fermion representation `fermionRep` of one generation with an
  equivariant chirality involution, the rank-three generation factor
  (spinor fields are `Site → Fin 3 → OneGeneration`), the Higgs doublet
  `Fin 2 → ℂ` carrying the weak `U(2)` action `higgsRep`, and an
  optional neutral/Majorana block type declared by the branch;
* (I3) the gauge-covariant finite Dirac/Yukawa incidence operator
  `dirac q` on spinor fields and the coefficient bank
  `CoefficientBank = (κ, Λ, g₁, g₂, g₃, λ_H, v_H, 𝐘)`;
* (I4) the differentiable common finite action
  `S_h = S_{g,h} + ν S_{SM,h}` with one relative normalization `ν` and
  finite local gauge invariance;
* (I5) a positive source geometry: a symmetric positive semidefinite Gram
  operator on `𝒬_h`, positive definite on the retained variation
  directions.

No reconstruction-to-continuum map, compactness, stationarity or field
equation is part of the record, exactly as in the paper.  Rendering
disclosed: the smooth comparison cylinder `M` and the continuum
reconstruction are not encoded (only the finite coframe reader is); the
gravitational and matter actions are abstract differentiable functionals
(the explicit lattice realisation
`explicitRegulatedStandardModelAction` is not enforced), and relabeling
covariance is not included.
-/

open Matrix
open scoped RealInnerProductSpace

namespace RenewalGeometry

/-- The Minkowski matrix `η = diag(-1,1,1,1)`. -/
def minkowskiEta : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![-1, 1, 1, 1]

/-- The reconstructed Lorentzian metric `g = eᵀ η e` of a coframe `e`. -/
def coframeMetric (e : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  eᵀ * minkowskiEta * e

/-- The weak `U(2)` action on the Higgs doublet `ℂ²`, restricted to
`S(U(3)×U(2))`. -/
noncomputable def higgsRep : Representation ℂ SMGaugeGroup (Fin 2 → ℂ) where
  toFun g := Matrix.toLin' ((g : SMGaugeU3 × SMGaugeU2).2 : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by
    simp only [OneMemClass.coe_one, Prod.snd_one, OneMemClass.coe_one, Matrix.toLin'_one]
    rfl
  map_mul' g g' := by
    simp only [Subgroup.coe_mul, Prod.snd_mul, Submonoid.coe_mul, Matrix.toLin'_mul]
    rfl

/-- The coefficient bank `θ_h = (κ_h, Λ_h, g_{1,h}, g_{2,h}, g_{3,h}, λ_{H,h},
v_{H,h}, 𝐘_h)` of (I3); the Yukawa matrices are `3 × 3` generation
matrices indexed by the declared Yukawa sectors. -/
structure CoefficientBank (YukawaSector : Type) where
  /-- gravitational coupling `κ` -/
  kappa : ℝ
  /-- cosmological constant `Λ` -/
  Lambda : ℝ
  /-- hypercharge coupling `g₁` -/
  g1 : ℝ
  /-- weak coupling `g₂` -/
  g2 : ℝ
  /-- strong coupling `g₃` -/
  g3 : ℝ
  /-- Higgs self-coupling `λ_H` -/
  lambdaH : ℝ
  /-- Higgs vacuum scale `v_H` -/
  vH : ℝ
  /-- Yukawa generation matrices `𝐘` -/
  yukawa : YukawaSector → Matrix (Fin 3) (Fin 3) ℂ

/-- **`def:finite-interface`**: a finite classical Einstein–Standard-Model
interface `𝔍_h` at cutoff `h`, bundling (I1)–(I5). -/
structure FiniteInterface (h : ℝ) where
  /-- (I1) the finite site set of the carrier -/
  Site : Type
  [siteFintype : Fintype Site]
  /-- (I1) the finite configuration chart `𝒬_h` -/
  Config : Type
  [configGroup : NormedAddCommGroup Config]
  [configInner : InnerProductSpace ℝ Config]
  [configFinite : FiniteDimensional ℝ Config]
  /-- (I1) local coframe variables `e^a_μ(x)` read from a configuration -/
  coframe : Config → Site → Matrix (Fin 4) (Fin 4) ℝ
  /-- (I1) oriented: `det e > 0` (the reconstructed metric `eᵀ η e` is
  then a nondegenerate Lorentzian metric) -/
  coframe_oriented : ∀ q x, 0 < (coframe q x).det
  /-- (I1) time-oriented: the temporal coframe component is future-directed -/
  coframe_timeOriented : ∀ q x, 0 < coframe q x 0 0
  /-- (I2) the retained chiral fermion representation of one generation -/
  OneGeneration : Type
  [oneGenerationGroup : AddCommGroup OneGeneration]
  [oneGenerationModule : Module ℂ OneGeneration]
  [oneGenerationFinite : FiniteDimensional ℂ OneGeneration]
  /-- (I2) the `S(U(3)×U(2))` representation on one generation -/
  fermionRep : Representation ℂ SMGaugeGroup OneGeneration
  /-- (I2) the chirality involution -/
  chirality : OneGeneration →ₗ[ℂ] OneGeneration
  chirality_involutive : chirality ∘ₗ chirality = LinearMap.id
  chirality_equivariant : ∀ g, chirality ∘ₗ fermionRep g = fermionRep g ∘ₗ chirality
  /-- (I2) optional neutral/Majorana blocks declared as part of the branch -/
  NeutralBlock : Type
  [neutralBlockFintype : Fintype NeutralBlock]
  /-- (I2) the Higgs doublet read from a configuration -/
  higgs : Config → Site → (Fin 2 → ℂ)
  /-- (I3) the declared Yukawa sectors -/
  YukawaSector : Type
  [yukawaSectorFintype : Fintype YukawaSector]
  /-- (I3) the coefficient bank `θ_h` -/
  coefficients : CoefficientBank YukawaSector
  /-- (I3) the finite Dirac/Yukawa incidence operator on spinor fields
  (one rank-three generation factor) -/
  dirac : Config → ((Site → Fin 3 → OneGeneration) →ₗ[ℂ] (Site → Fin 3 → OneGeneration))
  /-- (I4) finite local gauge transformations acting on the chart -/
  gaugeAct : (Site → SMGaugeGroup) → Config → Config
  /-- (I2)/(I4) the Higgs reader is gauge-covariant -/
  higgs_covariant : ∀ γ q x, higgs (gaugeAct γ q) x = higgsRep (γ x) (higgs q x)
  /-- (I3) the Dirac/Yukawa incidence operator is gauge-covariant -/
  dirac_covariant : ∀ γ q (ψ : Site → Fin 3 → OneGeneration) x n,
    dirac (gaugeAct γ q) (fun y m => fermionRep (γ y) (ψ y m)) x n
      = fermionRep (γ x) (dirac q ψ x n)
  /-- (I4) the gravitational finite action `S_{g,h}` -/
  gravityAction : Config → ℝ
  /-- (I4) the Standard-Model finite action `S_{SM,h}` -/
  matterAction : Config → ℝ
  /-- (I4) the physical relative normalization between gravity and matter -/
  relativeNormalization : ℝ
  relativeNormalization_pos : 0 < relativeNormalization
  /-- (I4) the common action is differentiable -/
  action_differentiable :
    Differentiable ℝ (fun q => gravityAction q + relativeNormalization * matterAction q)
  /-- (I4) finite gauge covariance of the common action on the declared branch -/
  action_gauge_invariant : ∀ γ q,
    gravityAction (gaugeAct γ q) + relativeNormalization * matterAction (gaugeAct γ q)
      = gravityAction q + relativeNormalization * matterAction q
  /-- (I5) the retained variation directions -/
  retained : Submodule ℝ Config
  /-- (I5) the source Gram operator -/
  gram : Config →ₗ[ℝ] Config
  gram_symmetric : ∀ u v, ⟪gram u, v⟫ = ⟪u, gram v⟫
  gram_nonneg : ∀ v, 0 ≤ ⟪v, gram v⟫
  /-- (I5) positivity on the retained variation directions -/
  gram_pos_retained : ∀ v ∈ retained, v ≠ 0 → 0 < ⟪v, gram v⟫

namespace FiniteInterface

variable {h : ℝ} (I : FiniteInterface h)

attribute [instance] siteFintype configGroup configInner configFinite
  oneGenerationGroup oneGenerationModule oneGenerationFinite neutralBlockFintype
  yukawaSectorFintype

/-- (I4) The common finite action `S_h = S_{g,h} + ν S_{SM,h}`. -/
def action (q : I.Config) : ℝ :=
  I.gravityAction q + I.relativeNormalization * I.matterAction q

theorem action_differentiable' : Differentiable ℝ I.action := I.action_differentiable

theorem action_gaugeAct (γ : I.Site → SMGaugeGroup) (q : I.Config) :
    I.action (I.gaugeAct γ q) = I.action q := I.action_gauge_invariant γ q

/-- (I1) The reconstructed metric at a site. -/
def metric (q : I.Config) (x : I.Site) : Matrix (Fin 4) (Fin 4) ℝ :=
  coframeMetric (I.coframe q x)

/-- (I1) The reconstructed metric is nondegenerate with Lorentzian
determinant sign `det g = -(det e)² < 0`. -/
theorem metric_det_neg (q : I.Config) (x : I.Site) : (I.metric q x).det < 0 := by
  unfold metric coframeMetric
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hη : minkowskiEta.det = -1 := by
    unfold minkowskiEta
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_four]
  rw [hη]
  have := I.coframe_oriented q x
  nlinarith

/-- (I2) The gauge group of the interface is `S(U(3)×U(2))`, isomorphic to
`(SU(3)×SU(2)×U(1))/ℤ₆` (`eq:gauge-group`). -/
noncomputable def gaugeGroupPresentation : SMGaugeCover ⧸ smGaugeHom.ker ≃* SMGaugeGroup :=
  smGaugeQuotientEquiv

end FiniteInterface

end RenewalGeometry
