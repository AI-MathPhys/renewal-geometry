/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeDensitiesExact
import RenewalGeometry.Algebra.SeriesLogChart

/-!
# Exact site-gauge invariance of the native local action, its packets and its covector norm
  (clauses (a)–(c) of `prop:rooted-gauge-certificate`, Einstein–SM action-closure manuscript)

The finite local common action `S_h^{loc}` of `eq:native-local-action` is
`NativeDensity.localAction`, built from the four densities of `eq:native-densities`.  Its gauge
links enter only through `U_μ(x) = e^{h A_μ(x)}` (and `U_μ(x)⁻¹ = e^{-h A_μ(x)}`).  This file

* rewrites the action **at link level** (`LinkConfig`, `linkAction`, `localAction_eq_linkAction`):
  every density is a function of the coframe, the links `U_μ(x)` (inverted by `Ring.inverse`),
  the Higgs field and the two spinor fields;
* adds the **standing covariance assumptions of the representation packet** as fields of a new
  structure `CovData` extending `NativeDensity.Data`: a gauge group `G ⊆ 𝔄ˣ` acting by
  norm-preserving conjugation, the `Ad`-invariance of the Lie inner product `⟨·,·⟩_𝐠`
  (`ipA_conj`), the `ρ_H(G)`-invariance of the Higgs form `Re⟨·,·⟩` (`hermH_inv`), the commutation
  of `ρ_S(g)` with the spin representation `σ` and the gamma matrices (`σ_comm`, `γ_comm`: the
  internal group acts on the internal factor, the spin transport and Clifford action on the
  spacetime factor), the covariance of the Yukawa blocks
  `𝓜_𝐘(ρ_H(g) H) = ρ_S(g) 𝓜_𝐘(H) ρ_S(g)⁻¹` (`yukawa_cov`) and the unitarity of `ρ_S` (`ρS_isom`).
  These are the manuscript's standing assumptions on the fixed representation packet:
  `tab:SM-representations` and `lem:SM-descent` (invariant contractions of the colour and weak
  indices, zero total hypercharge of each Yukawa monomial), "unitarity of the internal
  representations" and "Its covariance is part of the finite incidence interface" (Section
  "Fields, bundles and physical tests"), and the proof of `prop:rooted-gauge-certificate`
  ("the coframe-derived spin transport commutes with the internal group, and the covariant Yukawa
  blocks transform in their prescribed representations", "the invariant inner product");
* proves, for every site gauge `g : Grid → G` (in particular the normalizing gauge `g_x = q_x C_x`
  of the proved Coulomb clause, `RootedCoulomb.rooted_coulomb_normalization`), acting by
  `U_μ(x) ↦ g_x U_μ(x) g_{x+μ}⁻¹`, `H ↦ ρ_H(g) H`, `Ψ ↦ ρ_S(g) Ψ`, `Ψ̄ ↦ Ψ̄ ρ_S(g)⁻¹`:
  - **(a)** `gravSector_gauge`, `ymSector_gauge`, `higgsSector_gauge`, `diracSector_gauge`,
    `linkAction_gauge`, `localAction_gauge`: every sector of the finite common action is unchanged
    (on the admissible logarithm chart of the gauge plaquettes);
  - **(b)** `ipA_curv_gauge`, `hermH_hLink_gauge`, `norm_intLink_gauge`, `norm_intLinkBar_gauge`,
    `graphNormSq_gauge`, `wilsonSq_gauge`, `wilsonSqNeg_gauge`, `wilsonModulus_gauge`: the literal
    curvature and Higgs-gradient packets, the positive internal-link spinor graphs (spinor and
    dual spinor) and the Wilson moduli `eq:finite-Wilson-modulus` (open-link products
    `eq:open-finite-link`, both signs of `m`, any packet in a unitary representation, `Ad` for
    the curvature) are unchanged in norm;
  - **(c)** `linkCov_gauge`, `massSq_tangentAct`, `covNorm_gauge`: the complete action covector,
    taken in the physical link tangent `α_μ = h⁻¹ U̇_μ U_μ⁻¹` (curves `U_t = e^{t h α} U`) together
    with the coframe, Higgs and spinor tangents, transforms by the tangent map
    `α ↦ Ad_{g} α`, `η ↦ ρ_H(g) η`, `ψ ↦ ρ_S(g) ψ`, `ψ̄ ↦ ψ̄ ρ_S(g)⁻¹` (`tangentAct`), which
    preserves the positive physical mass metric (`massSq`); hence the dual norm of the covector is
    unchanged.  No derivative of the normalizing gauge appears.

Non-vacuity: the trivial packet (`𝔄 = ℝ`, trivial group, `trivialCovData`) and the `U(1)` packet
(`𝔄 = 𝓗 = 𝓢 = ℂ`, unitary units, `u1CovData`) satisfy all covariance fields; for the latter the
action is shown invariant under a constant phase rotation of the Higgs field and the spinors.
-/

open NormedSpace Finset Filter Topology

namespace RenewalGeometry
namespace NativeGauge

open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat omegaLink)
open NativeDensity

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]

/-! ### The covariant representation packet -/

/-- **The covariant native representation packet**: `NativeDensity.Data` together with a gauge
group `G ⊆ 𝔄ˣ` and the standing covariance assumptions of the representation packet
(`tab:SM-representations`, `lem:SM-descent`, the finite incidence interface). -/
structure CovData (𝔄 𝓗 𝓢 : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [NormedAddCommGroup 𝓗]
    [NormedSpace ℝ 𝓗] [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] extends NativeDensity.Data 𝔄 𝓗 𝓢 where
  /-- the gauge group, inside the units of the gauge algebra -/
  G : Subgroup 𝔄ˣ
  /-- the gauge group acts by norm-preserving conjugation (unitary group of a C*-algebra) -/
  norm_conj : ∀ g ∈ G, ∀ X : 𝔄, ‖(g : 𝔄) * X * ↑g⁻¹‖ = ‖X‖
  /-- `Ad`-invariance of the Lie inner product `⟨·,·⟩_𝐠` -/
  ipA_conj : ∀ g ∈ G, ∀ X Y : 𝔄, ipA ((g : 𝔄) * X * ↑g⁻¹) ((g : 𝔄) * Y * ↑g⁻¹) = ipA X Y
  /-- `ρ_H(G)`-invariance of the Higgs form `Re⟨·,·⟩` -/
  hermH_inv : ∀ g ∈ G, ∀ u v : 𝓗, hermH (ρH g u) (ρH g v) = hermH u v
  /-- the internal group commutes with the spin representation (spin transport) -/
  σ_comm : ∀ g ∈ G, ∀ m : Mat, Commute (ρS g) (σ m)
  /-- the internal group commutes with the Clifford action -/
  γ_comm : ∀ g ∈ G, ∀ a, Commute (ρS g) (γ a)
  /-- covariance of the Yukawa blocks -/
  yukawa_cov : ∀ g ∈ G, ∀ H : 𝓗, yukawa (ρH g H) = ρS g * yukawa H * ρS ↑g⁻¹
  /-- unitarity of the spinor representation -/
  ρS_isom : ∀ g ∈ G, ∀ v : 𝓢, ‖ρS g v‖ = ‖v‖

variable {n : ℕ} [NeZero n]

/-! ### Link configurations and the link-level action -/

/-- A link-level configuration: coframe, gauge links `U_μ(x)`, Higgs field, spinor and
co-spinor. -/
@[ext]
structure LinkConfig (n : ℕ) (𝔄 𝓗 𝓢 : Type*) [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] where
  e : Grid n → Mat
  U : Fin 4 → Grid n → 𝔄
  H : Grid n → 𝓗
  Ψ : Grid n → 𝓢
  Ψb : Grid n → CoSpinor 𝓢

/-- The link configuration of a record: `U_μ(x) = e^{h A_μ(x)}`. -/
def toLinks (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) : LinkConfig n 𝔄 𝓗 𝓢 where
  e := coframe y
  U μ x := exp (h • gauge y μ x)
  H := higgs y
  Ψ := psi y
  Ψb := psiBar y

/-- The gauge plaquette `U_μ(x) U_ν(x+μ) U_μ(x+ν)⁻¹ U_ν(x)⁻¹`. -/
def plaq (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ ν : Fin 4) : 𝔄 :=
  c.U μ x * c.U ν (x + unitVec n μ) * Ring.inverse (c.U μ (x + unitVec n ν)) *
    Ring.inverse (c.U ν x)

/-- The logarithmic field strength `F^h_{μν} = h⁻² log(plaquette)`. -/
def curv (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ ν : Fin 4) : 𝔄 :=
  (h ^ 2)⁻¹ • ShiftedPlaquette.logOneAdd (plaq c x μ ν - 1)

section Densities

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢)

/-- The Higgs link `K^h_μ = (ρ_H(U_μ) H(x+μ) - H(x))/h`. -/
def hLink (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : 𝓗 :=
  h⁻¹ • (D.ρH (c.U μ x) (c.H (x + unitVec n μ)) - c.H x)

/-- The spin link `V_μ = e^{hσ(ω_{μ,h})} ρ_S(U_μ)`. -/
def sLink (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : Spin 𝓢 :=
  exp (h • D.σ (omegaLink h c.e x μ)) * D.ρS (c.U μ x)

/-- The inverse spin link `V_μ⁻¹ = ρ_S(U_μ⁻¹) e^{-hσ(ω_{μ,h})}`. -/
def sLinkInv (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : Spin 𝓢 :=
  D.ρS (Ring.inverse (c.U μ x)) * exp (-(h • D.σ (omegaLink h c.e x μ)))

/-- The covariant Dirac difference `∇^h_μ Ψ`. -/
def dDiff (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : 𝓢 :=
  h⁻¹ • (sLink D h c x μ (c.Ψ (x + unitVec n μ)) - c.Ψ x)

/-- The transported co-spinor difference `∇^{h,∨}_μ Ψ̄`. -/
def dDiffBar (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : CoSpinor 𝓢 :=
  h⁻¹ • ((c.Ψb (x + unitVec n μ)).comp (sLinkInv D h c x μ) - c.Ψb x)

/-- The gravitational density at link level. -/
def gravD (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) : ℝ :=
  (∑ μ, ∑ ν, ∑ a, ∑ b, pal D.κ (c.e x) μ ν a b *
      opEntry (antisym (cartanCurvature h c.e x) μ ν) a b) - D.Λ / D.κ * volume (c.e x)

/-- The Yang–Mills density at link level. -/
def ymD (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) : ℝ :=
  -(4⁻¹ * volume (c.e x) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
    ginv (c.e x) μ ρ * ginv (c.e x) ν σ *
      D.ipA (antisym (curv h c x) μ ν) (antisym (curv h c x) ρ σ))

/-- The Higgs density at link level. -/
def higgsD (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) : ℝ :=
  -(volume (c.e x) * ∑ μ, ∑ ν, ginv (c.e x) μ ν *
      D.hermH (hLink D h c x μ) (hLink D h c x ν)) - volume (c.e x) * potential D (c.H x)

/-- The Dirac–Yukawa density at link level. -/
def diracD (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) : ℝ :=
  volume (c.e x) *
    (Complex.I / 2 * ∑ μ, (c.Ψb x (gammaMu D μ (c.e x) (dDiff D h c x μ)) -
        dDiffBar D h c x μ (gammaMu D μ (c.e x) (c.Ψ x))) -
      c.Ψb x (D.yukawa (c.H x) (c.Ψ x))).re

/-- The four sector actions `h⁴ Σ_x 𝓛_{•,h}` at link level. -/
def gravSector (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) : ℝ := h ^ 4 * ∑ x, gravD D h c x
def ymSector (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) : ℝ := h ^ 4 * ∑ x, ymD D h c x
def higgsSector (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) : ℝ := h ^ 4 * ∑ x, higgsD D h c x
def diracSector (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) : ℝ := h ^ 4 * ∑ x, diracD D h c x

/-- The finite local common action at link level. -/
def linkAction (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) : ℝ :=
  h ^ 4 * ∑ x, (gravD D h c x + ymD D h c x + higgsD D h c x + diracD D h c x)

theorem linkAction_eq_sectors (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) :
    linkAction D h c = gravSector D h c + ymSector D h c + higgsSector D h c +
      diracSector D h c := by
  simp only [linkAction, gravSector, ymSector, higgsSector, diracSector, Finset.sum_add_distrib]
  ring

/-! ### The link-level action is the native local action -/

theorem ring_inverse_exp (u : 𝔄) : Ring.inverse (exp u) = exp (-u) := by
  have hu : exp u * exp (-u) = 1 := exp_mul_exp_neg u
  have hu' : exp (-u) * exp u = 1 := exp_neg_mul_exp u
  have : Ring.inverse ((⟨exp u, exp (-u), hu, hu'⟩ : 𝔄ˣ) : 𝔄) = exp (-u) := by
    rw [Ring.inverse_unit]; rfl
  exact this

theorem gaugePlaquette_eq_plaq (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ ν : Fin 4) :
    NativeScaling.gaugePlaquette h (gauge y) x μ ν = plaq (toLinks h y) x μ ν := by
  simp only [NativeScaling.gaugePlaquette, plaq, toLinks, ring_inverse_exp]

theorem fieldStrength_eq_curv (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ ν : Fin 4) :
    NativeScaling.fieldStrength h (gauge y) x μ ν = curv h (toLinks h y) x μ ν := by
  simp only [NativeScaling.fieldStrength, curv, gaugePlaquette_eq_plaq]

theorem fieldStrength_eq_curv' (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    NativeScaling.fieldStrength h (gauge y) x = curv h (toLinks h y) x := by
  funext μ ν
  exact fieldStrength_eq_curv h y x μ ν

theorem higgsLink_eq_hLink (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    higgsLink D h y x μ = hLink D h (toLinks h y) x μ := rfl

theorem spinLink_eq_sLink (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    spinLink D h y x μ = sLink D h (toLinks h y) x μ := rfl

theorem spinLinkInv_eq_sLinkInv (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    spinLinkInv D h y x μ = sLinkInv D h (toLinks h y) x μ := by
  simp only [spinLinkInv, sLinkInv, toLinks, ring_inverse_exp]

theorem diracDiff_eq_dDiff (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    diracDiff D h y x μ = dDiff D h (toLinks h y) x μ := rfl

theorem diracDiffBar_eq_dDiffBar (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    diracDiffBar D h y x μ = dDiffBar D h (toLinks h y) x μ := by
  simp only [diracDiffBar, dDiffBar, spinLinkInv_eq_sLinkInv]
  rfl

theorem gravityDensity_eq (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    gravityDensity D h y x = gravD D h (toLinks h y) x := rfl

theorem ymDensity_eq (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    ymDensity D h y x = ymD D h (toLinks h y) x := by
  simp only [ymDensity, ymD, fieldStrength_eq_curv']
  rfl

theorem higgsDensity_eq (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    higgsDensity D h y x = higgsD D h (toLinks h y) x := rfl

theorem diracDensity_eq (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    diracDensity D h y x = diracD D h (toLinks h y) x := by
  simp only [diracDensity, diracD, diracDiff_eq_dDiff, diracDiffBar_eq_dDiffBar]
  rfl

/-- **The native local action is the link-level action** of its links `U = e^{hA}`. -/
theorem localAction_eq_linkAction (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) :
    localAction D h y = linkAction D h (toLinks h y) := by
  simp only [localAction, linkAction, nativeDensity, gravityDensity_eq, ymDensity_eq,
    higgsDensity_eq, diracDensity_eq]

end Densities
/-! ### The site-gauge action -/

section Gauge

variable (C : CovData 𝔄 𝓗 𝓢)

omit [CompleteSpace 𝔄] [NormOneClass 𝔄] in
/-- `Ring.inverse` of a two-sided unit conjugate. -/
theorem ring_inverse_conj (a b : 𝔄ˣ) (u : 𝔄) :
    Ring.inverse ((a : 𝔄) * u * ↑b⁻¹) = (b : 𝔄) * Ring.inverse u * ↑a⁻¹ := by
  by_cases hu : IsUnit u
  · obtain ⟨v, rfl⟩ := hu
    have e : (a : 𝔄) * v * ↑b⁻¹ = ((a * v * b⁻¹ : 𝔄ˣ) : 𝔄) := by simp
    rw [e, Ring.inverse_unit, Ring.inverse_unit]
    simp [mul_assoc]
  · have h2 : ¬ IsUnit ((a : 𝔄) * u * ↑b⁻¹) := by
      intro h'
      apply hu
      have e : u = ↑a⁻¹ * ((a : 𝔄) * u * ↑b⁻¹) * b := by simp [mul_assoc]
      rw [e]
      exact ((a⁻¹).isUnit.mul h').mul b.isUnit
    rw [Ring.inverse_non_unit _ hu, Ring.inverse_non_unit _ h2, mul_zero, zero_mul]

theorem algHom_inv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : 𝔄 →ₐ[ℝ] (F →L[ℝ] F)) (g : 𝔄ˣ) (v : F) : ρ ↑g⁻¹ (ρ g v) = v := by
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, Units.inv_mul, map_one,
    ContinuousLinearMap.one_apply]

theorem algHom_apply_inv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : 𝔄 →ₐ[ℝ] (F →L[ℝ] F)) (g : 𝔄ˣ) (v : F) : ρ g (ρ ↑g⁻¹ v) = v := by
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, Units.mul_inv, map_one,
    ContinuousLinearMap.one_apply]

/-- **The site-gauge action** `U_μ(x) ↦ g_x U_μ(x) g_{x+μ}⁻¹`, `H ↦ ρ_H(g) H`, `Ψ ↦ ρ_S(g) Ψ`,
`Ψ̄ ↦ Ψ̄ ρ_S(g)⁻¹`; the coframe is untouched. -/
def gaugeAct (g : Grid n → 𝔄ˣ) (c : LinkConfig n 𝔄 𝓗 𝓢) : LinkConfig n 𝔄 𝓗 𝓢 where
  e := c.e
  U μ x := (g x : 𝔄) * c.U μ x * ↑(g (x + unitVec n μ))⁻¹
  H x := C.ρH (g x) (c.H x)
  Ψ x := C.ρS (g x) (c.Ψ x)
  Ψb x := (c.Ψb x).comp (C.ρS ↑(g x)⁻¹)

/-- Plaquette endpoint cancellation: the gauge plaquette is conjugated at its base vertex. -/
theorem plaq_gauge (g : Grid n → 𝔄ˣ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ ν : Fin 4) :
    plaq (gaugeAct C g c) x μ ν = (g x : 𝔄) * plaq c x μ ν * ↑(g x)⁻¹ := by
  simp only [plaq, gaugeAct, ring_inverse_conj]
  rw [add_right_comm x (unitVec n ν) (unitVec n μ)]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

/-- Conjugation equivariance of the logarithmic field strength on the admissible chart. -/
theorem curv_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢)
    (x : Grid n) (μ ν : Fin 4) (hP : ‖plaq c x μ ν - 1‖ < 1) :
    curv h (gaugeAct C g c) x μ ν = (g x : 𝔄) * curv h c x μ ν * ↑(g x)⁻¹ := by
  have e : plaq (gaugeAct C g c) x μ ν - 1 = (g x : 𝔄) * (plaq c x μ ν - 1) * ↑(g x)⁻¹ := by
    rw [plaq_gauge, mul_sub, sub_mul, mul_one, Units.mul_inv]
  have hP' : ‖(g x : 𝔄) * (plaq c x μ ν - 1) * ↑(g x)⁻¹‖ < 1 := by
    rwa [C.norm_conj _ (hg x)]
  rw [curv, e, SeriesLogChart.logOneAdd_conj (g x) hP hP', curv, mul_smul_comm, smul_mul_assoc]

/-- The admissible logarithm chart of the gauge plaquettes. -/
def Chart (c : LinkConfig n 𝔄 𝓗 𝓢) : Prop := ∀ x (μ ν : Fin 4), μ < ν → ‖plaq c x μ ν - 1‖ < 1

theorem antisym_conj (u : 𝔄ˣ) (P : Fin 4 → Fin 4 → 𝔄) (μ ν : Fin 4) :
    antisym (fun μ ν => (u : 𝔄) * P μ ν * ↑u⁻¹) μ ν = (u : 𝔄) * antisym P μ ν * ↑u⁻¹ := by
  unfold antisym
  split_ifs <;> simp [neg_mul, mul_neg]

theorem antisym_curv_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    {c : LinkConfig n 𝔄 𝓗 𝓢} (hc : Chart c) (x : Grid n) (μ ν : Fin 4) :
    antisym (curv h (gaugeAct C g c) x) μ ν = (g x : 𝔄) * antisym (curv h c x) μ ν * ↑(g x)⁻¹ := by
  rw [← antisym_conj]
  unfold antisym
  split_ifs with h1 h2
  · exact curv_gauge C hg h c x μ ν (hc x μ ν h1)
  · rw [curv_gauge C hg h c x ν μ (hc x ν μ h2)]
  · rfl

/-- **(b), curvature packet**: the literal curvature packet is unchanged in the invariant metric
(every pair `⟨F_{μν}, F_{ρσ}⟩_𝐠`, in particular `|F_{μν}|²_𝐠`). -/
theorem ipA_curv_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    {c : LinkConfig n 𝔄 𝓗 𝓢} (hc : Chart c) (x : Grid n) (μ ν ρ σ : Fin 4) :
    C.ipA (antisym (curv h (gaugeAct C g c) x) μ ν) (antisym (curv h (gaugeAct C g c) x) ρ σ) =
      C.ipA (antisym (curv h c x) μ ν) (antisym (curv h c x) ρ σ) := by
  rw [antisym_curv_gauge C hg h hc, antisym_curv_gauge C hg h hc, C.ipA_conj _ (hg x)]

/-- The Higgs link transforms covariantly: `K^h(g·c) = ρ_H(g_x) K^h(c)`. -/
theorem hLink_gauge (g : Grid n → 𝔄ˣ) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n)
    (μ : Fin 4) :
    hLink C.toData h (gaugeAct C g c) x μ = C.ρH (g x) (hLink C.toData h c x μ) := by
  simp only [hLink, gaugeAct, map_mul, ContinuousLinearMap.mul_apply, algHom_inv_apply,
    map_smul, map_sub]

/-- **(b), Higgs-gradient packet**: `Re⟨K_μ, K_ν⟩` is unchanged. -/
theorem hermH_hLink_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ ν : Fin 4) :
    C.hermH (hLink C.toData h (gaugeAct C g c) x μ) (hLink C.toData h (gaugeAct C g c) x ν) =
      C.hermH (hLink C.toData h c x μ) (hLink C.toData h c x ν) := by
  rw [hLink_gauge, hLink_gauge, C.hermH_inv _ (hg x)]

theorem commute_exp_σ {g : 𝔄ˣ} (hg : g ∈ C.G) (t : ℝ) (m : Mat) :
    Commute (C.ρS g) (exp (t • C.σ m)) :=
  ((C.σ_comm g hg m).smul_right t).exp_right

theorem commute_exp_neg_σ {g : 𝔄ˣ} (hg : g ∈ C.G) (t : ℝ) (m : Mat) :
    Commute (C.ρS g) (exp (-(t • C.σ m))) :=
  (((C.σ_comm g hg m).smul_right t).neg_right).exp_right

/-- The spin link transforms by `V(g·c) = ρ_S(g_x) V(c) ρ_S(g_{x+μ})⁻¹` (the coframe-derived spin
transport commutes with the internal group). -/
theorem sLink_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢)
    (x : Grid n) (μ : Fin 4) :
    sLink C.toData h (gaugeAct C g c) x μ =
      C.ρS (g x) * sLink C.toData h c x μ * C.ρS ↑(g (x + unitVec n μ))⁻¹ := by
  simp only [sLink, gaugeAct, map_mul]
  rw [← mul_assoc, ← mul_assoc, ← (commute_exp_σ C (hg x) h _).eq]
  simp only [mul_assoc]

theorem sLinkInv_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    sLinkInv C.toData h (gaugeAct C g c) x μ =
      C.ρS (g (x + unitVec n μ)) * sLinkInv C.toData h c x μ * C.ρS ↑(g x)⁻¹ := by
  simp only [sLinkInv, gaugeAct, ring_inverse_conj, map_mul]
  rw [mul_assoc (C.ρS ↑(g (x + unitVec n μ)) * C.ρS (Ring.inverse (c.U μ x))),
    (commute_exp_neg_σ C (inv_mem (hg x)) h _).eq]
  simp only [mul_assoc]

/-- The covariant Dirac difference transforms covariantly: `∇^h(g·c) = ρ_S(g_x) ∇^h(c)`. -/
theorem dDiff_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢)
    (x : Grid n) (μ : Fin 4) :
    dDiff C.toData h (gaugeAct C g c) x μ = C.ρS (g x) (dDiff C.toData h c x μ) := by
  rw [dDiff, sLink_gauge C hg]
  simp only [dDiff, gaugeAct, ContinuousLinearMap.mul_apply, algHom_inv_apply, map_smul,
    map_sub]

/-- The transported co-spinor difference transforms contragrediently. -/
theorem dDiffBar_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    dDiffBar C.toData h (gaugeAct C g c) x μ =
      (dDiffBar C.toData h c x μ).comp (C.ρS ↑(g x)⁻¹) := by
  rw [dDiffBar, sLinkInv_gauge C hg]
  ext w
  simp only [dDiffBar, gaugeAct, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply, algHom_inv_apply]

theorem commute_gammaMu {g : 𝔄ˣ} (hg : g ∈ C.G) (μ : Fin 4) (e : Mat) :
    Commute (C.ρS g) (gammaMu C.toData μ e) :=
  Commute.sum_right _ _ _ fun a _ => (C.γ_comm g hg a).smul_right _

theorem gammaMu_ρS {g : 𝔄ˣ} (hg : g ∈ C.G) (μ : Fin 4) (e : Mat) (v : 𝓢) :
    gammaMu C.toData μ e (C.ρS g v) = C.ρS g (gammaMu C.toData μ e v) := by
  rw [← ContinuousLinearMap.mul_apply, ← (commute_gammaMu C hg μ e).eq,
    ContinuousLinearMap.mul_apply]

/-! #### (a): every sector is unchanged -/

theorem gravD_gauge (g : Grid n → 𝔄ˣ) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) :
    gravD C.toData h (gaugeAct C g c) x = gravD C.toData h c x := rfl

theorem ymD_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ) {c : LinkConfig n 𝔄 𝓗 𝓢}
    (hc : Chart c) (x : Grid n) :
    ymD C.toData h (gaugeAct C g c) x = ymD C.toData h c x := by
  simp only [ymD]
  congr 2
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [ipA_curv_gauge C hg h hc]
  rfl

theorem potential_gauge {g : 𝔄ˣ} (hg : g ∈ C.G) (H : 𝓗) :
    potential C.toData (C.ρH g H) = potential C.toData H := by
  simp only [potential, C.hermH_inv g hg]

theorem higgsD_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢)
    (x : Grid n) :
    higgsD C.toData h (gaugeAct C g c) x = higgsD C.toData h c x := by
  simp only [higgsD, hermH_hLink_gauge C hg]
  rw [show (gaugeAct C g c).H x = C.ρH (g x) (c.H x) from rfl, potential_gauge C (hg x)]
  rfl

theorem diracD_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢)
    (x : Grid n) :
    diracD C.toData h (gaugeAct C g c) x = diracD C.toData h c x := by
  simp only [diracD, dDiff_gauge C hg, dDiffBar_gauge C hg]
  have e1 : (gaugeAct C g c).e = c.e := rfl
  have e2 : (gaugeAct C g c).Ψ x = C.ρS (g x) (c.Ψ x) := rfl
  have e3 : (gaugeAct C g c).Ψb x = (c.Ψb x).comp (C.ρS ↑(g x)⁻¹) := rfl
  have e4 : (gaugeAct C g c).H x = C.ρH (g x) (c.H x) := rfl
  rw [e1, e2, e3, e4, C.yukawa_cov _ (hg x)]
  simp only [ContinuousLinearMap.comp_apply, gammaMu_ρS C (hg x), algHom_inv_apply,
    ContinuousLinearMap.mul_apply]

/-- **(a), gravity sector** (no internal link). -/
theorem gravSector_gauge (g : Grid n → 𝔄ˣ) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) :
    gravSector C.toData h (gaugeAct C g c) = gravSector C.toData h c := rfl

/-- **(a), Yang–Mills sector** (on the admissible logarithm chart). -/
theorem ymSector_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    {c : LinkConfig n 𝔄 𝓗 𝓢} (hc : Chart c) :
    ymSector C.toData h (gaugeAct C g c) = ymSector C.toData h c := by
  simp only [ymSector, ymD_gauge C hg h hc]

/-- **(a), Higgs sector**. -/
theorem higgsSector_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) :
    higgsSector C.toData h (gaugeAct C g c) = higgsSector C.toData h c := by
  simp only [higgsSector, higgsD_gauge C hg h c]

/-- **(a), Dirac–Yukawa sector**. -/
theorem diracSector_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) :
    diracSector C.toData h (gaugeAct C g c) = diracSector C.toData h c := by
  simp only [diracSector, diracD_gauge C hg h c]

/-- **(a)**: the complete finite common action is gauge invariant. -/
theorem linkAction_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    {c : LinkConfig n 𝔄 𝓗 𝓢} (hc : Chart c) :
    linkAction C.toData h (gaugeAct C g c) = linkAction C.toData h c := by
  rw [linkAction_eq_sectors, linkAction_eq_sectors, gravSector_gauge, ymSector_gauge C hg h hc,
    higgsSector_gauge C hg, diracSector_gauge C hg]

end Gauge

/-! ### Record-level invariance (clause (a) for `NativeDensity.localAction`) -/

section Records

variable (C : CovData 𝔄 𝓗 𝓢)

/-- `y'` is the gauge transform of the record `y` by the site gauge `g : Grid → G`: its links,
Higgs field and spinors are those of `gaugeAct g (toLinks h y)` and its coframe is that of `y`.
On the logarithm chart the transformed record exists (`toLinks_gaugeRecord`). -/
def IsGaugeTransform (h : ℝ) (g : Grid n → 𝔄ˣ) (y y' : Grid n → Field 𝔄 𝓗 𝓢) : Prop :=
  (∀ x, g x ∈ C.G) ∧ toLinks h y' = gaugeAct C g (toLinks h y)

/-- The gauge-transformed record with logarithmic coordinates
`A'_μ(x) = h⁻¹ log(g_x e^{hA_μ(x)} g_{x+μ}⁻¹)` (the normalized coordinates of the Coulomb clause). -/
def gaugeRecord (h : ℝ) (g : Grid n → 𝔄ˣ) (y : Grid n → Field 𝔄 𝓗 𝓢) :
    Grid n → Field 𝔄 𝓗 𝓢 := fun x =>
  (coframe y x, fun μ => h⁻¹ • SeriesLogChart.logChart ((gaugeAct C g (toLinks h y)).U μ x),
    C.ρH (g x) (higgs y x), C.ρS (g x) (psi y x), (psiBar y x).comp (C.ρS ↑(g x)⁻¹))

/-- On the logarithm chart `‖g_x e^{hA} g_{x+μ}⁻¹ - 1‖ < 1` the logarithmic record realizes the
gauge-transformed links exactly. -/
theorem toLinks_gaugeRecord {h : ℝ} (hh : h ≠ 0) (g : Grid n → 𝔄ˣ) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (hU : ∀ x μ, ‖(gaugeAct C g (toLinks h y)).U μ x - 1‖ < 1) :
    toLinks h (gaugeRecord C h g y) = gaugeAct C g (toLinks h y) := by
  have hU' : (fun μ x => exp (h • (h⁻¹ • SeriesLogChart.logChart
      ((gaugeAct C g (toLinks h y)).U μ x)))) = (gaugeAct C g (toLinks h y)).U := by
    funext μ x
    rw [smul_smul, mul_inv_cancel₀ hh, one_smul, SeriesLogChart.exp_logChart (hU x μ)]
  change LinkConfig.mk _ _ _ _ _ = _
  simp only [NativeDensity.gauge, gaugeRecord]
  rw [hU']
  rfl

/-- **Clause (a) for the native local action** `S_h^{loc}` (`eq:native-local-action`): under a site
gauge with values in `G`, on the admissible logarithm chart of the plaquettes, the finite common
action is unchanged. -/
theorem localAction_gauge {h : ℝ} {g : Grid n → 𝔄ˣ} {y y' : Grid n → Field 𝔄 𝓗 𝓢}
    (hy : IsGaugeTransform C h g y y') (hc : Chart (toLinks h y)) :
    localAction C.toData h y' = localAction C.toData h y := by
  rw [localAction_eq_linkAction, localAction_eq_linkAction, hy.2, linkAction_gauge C hy.1 h hc]

/-- Clause (a), sector by sector, for the native records. -/
theorem localSectors_gauge {h : ℝ} {g : Grid n → 𝔄ˣ} {y y' : Grid n → Field 𝔄 𝓗 𝓢}
    (hy : IsGaugeTransform C h g y y') (hc : Chart (toLinks h y)) :
    (h ^ 4 * ∑ x, gravityDensity C.toData h y' x = h ^ 4 * ∑ x, gravityDensity C.toData h y x) ∧
    (h ^ 4 * ∑ x, ymDensity C.toData h y' x = h ^ 4 * ∑ x, ymDensity C.toData h y x) ∧
    (h ^ 4 * ∑ x, higgsDensity C.toData h y' x = h ^ 4 * ∑ x, higgsDensity C.toData h y x) ∧
    (h ^ 4 * ∑ x, diracDensity C.toData h y' x = h ^ 4 * ∑ x, diracDensity C.toData h y x) := by
  simp only [gravityDensity_eq, ymDensity_eq, higgsDensity_eq, diracDensity_eq, hy.2]
  exact ⟨gravSector_gauge C g h _, ymSector_gauge C hy.1 h hc, higgsSector_gauge C hy.1 h _,
    diracSector_gauge C hy.1 h _⟩

end Records

/-! ### (b): positive internal-link spinor graphs and Wilson moduli -/

section Graphs

variable (C : CovData 𝔄 𝓗 𝓢)

/-- The internal-link spinor difference `𝒟^U_μ Ψ = (ρ_S(U_μ) Ψ(x+μ) - Ψ(x))/h`
(`eq:native-internal-graph`). -/
def intLink (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : 𝓢 :=
  h⁻¹ • (C.ρS (c.U μ x) (c.Ψ (x + unitVec n μ)) - c.Ψ x)

/-- The internal-link co-spinor difference `(Ψ̄(x+μ) ρ_S(U_μ)⁻¹ - Ψ̄(x))/h`. -/
def intLinkBar (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : CoSpinor 𝓢 :=
  h⁻¹ • ((c.Ψb (x + unitVec n μ)).comp (C.ρS (Ring.inverse (c.U μ x))) - c.Ψb x)

theorem intLink_gauge (g : Grid n → 𝔄ˣ) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n)
    (μ : Fin 4) :
    intLink C h (gaugeAct C g c) x μ = C.ρS (g x) (intLink C h c x μ) := by
  simp only [intLink, gaugeAct, map_mul, ContinuousLinearMap.mul_apply, algHom_inv_apply,
    map_smul, map_sub]

theorem intLinkBar_gauge (g : Grid n → 𝔄ˣ) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n)
    (μ : Fin 4) :
    intLinkBar C h (gaugeAct C g c) x μ = (intLinkBar C h c x μ).comp (C.ρS ↑(g x)⁻¹) := by
  ext w
  simp only [intLinkBar, gaugeAct, ring_inverse_conj, map_mul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply,
    algHom_inv_apply]

/-- The spinor representation of a gauge element is an isometry. -/
theorem norm_ρS_apply {g : 𝔄ˣ} (hg : g ∈ C.G) (v : 𝓢) : ‖C.ρS g v‖ = ‖v‖ := C.ρS_isom g hg v

/-- Composition with an isometric automorphism preserves the norm of a co-spinor. -/
theorem norm_comp_ρS_inv {g : 𝔄ˣ} (hg : g ∈ C.G) (f : CoSpinor 𝓢) :
    ‖f.comp (C.ρS ↑g⁻¹)‖ = ‖f‖ := by
  have hb : ∀ k : 𝔄ˣ, k ∈ C.G → ‖C.ρS k‖ ≤ 1 := fun k hk =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      rw [C.ρS_isom k hk, one_mul]
  refine le_antisymm ?_ ?_
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg _) (hb _ (inv_mem hg))
  · have e : f = (f.comp (C.ρS ↑g⁻¹)).comp (C.ρS g) := by
      ext v
      simp only [ContinuousLinearMap.comp_apply, algHom_inv_apply]
    calc ‖f‖ = ‖(f.comp (C.ρS ↑g⁻¹)).comp (C.ρS g)‖ := by rw [← e]
      _ ≤ ‖f.comp (C.ρS ↑g⁻¹)‖ * ‖C.ρS g‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖f.comp (C.ρS ↑g⁻¹)‖ := mul_le_of_le_one_right (norm_nonneg _) (hb _ hg)

/-- **(b), spinor graph**: the internal-link spinor differences are unchanged in norm. -/
theorem norm_intLink_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    ‖intLink C h (gaugeAct C g c) x μ‖ = ‖intLink C h c x μ‖ := by
  rw [intLink_gauge, C.ρS_isom _ (hg x)]

/-- **(b), dual-spinor graph**. -/
theorem norm_intLinkBar_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    ‖intLinkBar C h (gaugeAct C g c) x μ‖ = ‖intLinkBar C h c x μ‖ := by
  rw [intLinkBar_gauge, norm_comp_ρS_inv C (hg x)]

/-- The full spin–gauge covariant difference `∇^h_μ Ψ` is also unchanged in norm. -/
theorem norm_dDiff_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    ‖dDiff C.toData h (gaugeAct C g c) x μ‖ = ‖dDiff C.toData h c x μ‖ := by
  rw [dDiff_gauge C hg, C.ρS_isom _ (hg x)]

/-- The squared positive internal-link graph norms
`‖Ψ‖²_{2,h} + Σ_μ ‖𝒟^U_μ Ψ‖²_{2,h}` and its dual (`eq:native-spinor-graph`). -/
def graphNormSq (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) : ℝ :=
  h ^ 4 * ∑ x, (‖c.Ψ x‖ ^ 2 + ∑ μ, ‖intLink C h c x μ‖ ^ 2)

def graphNormSqBar (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) : ℝ :=
  h ^ 4 * ∑ x, (‖c.Ψb x‖ ^ 2 + ∑ μ, ‖intLinkBar C h c x μ‖ ^ 2)

/-- **(b)**: the positive internal-link spinor graphs are unchanged in norm. -/
theorem graphNormSq_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) :
    graphNormSq C h (gaugeAct C g c) = graphNormSq C h c ∧
      graphNormSqBar C h (gaugeAct C g c) = graphNormSqBar C h c := by
  constructor
  · simp only [graphNormSq, norm_intLink_gauge C hg]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (gaugeAct C g c).Ψ x = C.ρS (g x) (c.Ψ x) from rfl, C.ρS_isom _ (hg x)]
  · simp only [graphNormSqBar, norm_intLinkBar_gauge C hg]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (gaugeAct C g c).Ψb x = (c.Ψb x).comp (C.ρS ↑(g x)⁻¹) from rfl,
      norm_comp_ρS_inv C (hg x)]

/-! #### Wilson moduli (`eq:open-finite-link`, `eq:finite-Wilson-shift`,
`eq:finite-Wilson-modulus`) -/

/-- The open finite link `𝒰_{μ,m}(x) = U_μ(x) U_μ(x+e_μ) ⋯ U_μ(x+(m-1)e_μ)`. -/
def openLink (c : LinkConfig n 𝔄 𝓗 𝓢) (μ : Fin 4) : ℕ → Grid n → 𝔄
  | 0, _ => 1
  | m + 1, x => openLink c μ m x * c.U μ (x + m • unitVec n μ)

/-- Endpoint gauges telescope along the open link. -/
theorem openLink_gauge (g : Grid n → 𝔄ˣ) (c : LinkConfig n 𝔄 𝓗 𝓢) (μ : Fin 4) (m : ℕ)
    (x : Grid n) :
    openLink (gaugeAct C g c) μ m x =
      (g x : 𝔄) * openLink c μ m x * ↑(g (x + m • unitVec n μ))⁻¹ := by
  induction m with
  | zero => simp [openLink]
  | succ m ih =>
    rw [openLink, openLink, ih]
    change _ * ((g (x + m • unitVec n μ) : 𝔄) * c.U μ (x + m • unitVec n μ) *
      ↑(g (x + m • unitVec n μ + unitVec n μ))⁻¹) = _
    rw [show x + m • unitVec n μ + unitVec n μ = x + (m + 1) • unitVec n μ by
      rw [add_smul, one_smul, add_assoc]]
    simp only [mul_assoc, Units.inv_mul_cancel_left]

variable {F : Type*} [AddCommGroup F]

/-- The Wilson shift difference `W^U_{μ,m} Y(x) - Y(x) = act(𝒰_{μ,m}(x)) Y(x+m e_μ) - Y(x)` of a
packet `Y` in a representation `act` (positive `m`). -/
def wilsonDiff (act : 𝔄 → F → F) (c : LinkConfig n 𝔄 𝓗 𝓢) (Y : Grid n → F) (μ : Fin 4) (m : ℕ)
    (x : Grid n) : F :=
  act (openLink c μ m x) (Y (x + m • unitVec n μ)) - Y x

/-- The Wilson shift difference for negative displacement `-m`, with the inverse ordered
product `𝒰_{μ,m}(x - m e_μ)⁻¹`. -/
def wilsonDiffNeg (act : 𝔄 → F → F) (c : LinkConfig n 𝔄 𝓗 𝓢) (Y : Grid n → F) (μ : Fin 4)
    (m : ℕ) (x : Grid n) : F :=
  act (Ring.inverse (openLink c μ m (x - m • unitVec n μ))) (Y (x - m • unitVec n μ)) - Y x

/-- A representation on packets: covariance of the transported packet and additivity. -/
structure PacketRep (act : 𝔄 → F → F) : Prop where
  conj : ∀ (a b : 𝔄ˣ) (P : 𝔄) (v : F), act ((a : 𝔄) * P * ↑b⁻¹) (act b v) = act a (act P v)
  sub : ∀ (a : 𝔄) (v w : F), act a (v - w) = act a v - act a w

theorem wilsonDiff_gauge {act : 𝔄 → F → F} (hact : PacketRep act) (g : Grid n → 𝔄ˣ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) (Y : Grid n → F) (μ : Fin 4) (m : ℕ) (x : Grid n) :
    wilsonDiff act (gaugeAct C g c) (fun z => act (g z) (Y z)) μ m x =
      act (g x) (wilsonDiff act c Y μ m x) := by
  simp only [wilsonDiff, openLink_gauge, hact.conj, hact.sub]

theorem wilsonDiffNeg_gauge {act : 𝔄 → F → F} (hact : PacketRep act) (g : Grid n → 𝔄ˣ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) (Y : Grid n → F) (μ : Fin 4) (m : ℕ) (x : Grid n) :
    wilsonDiffNeg act (gaugeAct C g c) (fun z => act (g z) (Y z)) μ m x =
      act (g x) (wilsonDiffNeg act c Y μ m x) := by
  simp only [wilsonDiffNeg, openLink_gauge, sub_add_cancel, ring_inverse_conj, hact.conj,
    hact.sub]

/-- The squared Wilson difference sums `h⁴ Σ_x nrm(W^U_{μ,±m} Y - Y)`. -/
def wilsonSq (act : 𝔄 → F → F) (nrm : F → ℝ) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (Y : Grid n → F)
    (μ : Fin 4) (m : ℕ) : ℝ :=
  h ^ 4 * ∑ x, nrm (wilsonDiff act c Y μ m x)

def wilsonSqNeg (act : 𝔄 → F → F) (nrm : F → ℝ) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢)
    (Y : Grid n → F) (μ : Fin 4) (m : ℕ) : ℝ :=
  h ^ 4 * ∑ x, nrm (wilsonDiffNeg act c Y μ m x)

/-- **The Wilson modulus** `Ω_h(Y; ϱ) = max_μ max_{0 < |m| h ≤ ϱ} (h⁴ Σ_x |W^U_{μ,m}Y - Y|²)^{1/2}`
(`eq:finite-Wilson-modulus`, periodic box), with `|·|² = nrm`. -/
def wilsonModulus (act : 𝔄 → F → F) (nrm : F → ℝ) (h ϱ : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢)
    (Y : Grid n → F) : ℝ :=
  ⨆ (μ : Fin 4) (m : ℕ) (_ : 0 < m ∧ (m : ℝ) * h ≤ ϱ),
    max (Real.sqrt (wilsonSq act nrm h c Y μ m)) (Real.sqrt (wilsonSqNeg act nrm h c Y μ m))

/-- **(b), Wilson moduli**: for a packet in a representation whose norm is `G`-invariant, the
Wilson moduli of the transformed packet equal those of the original one. -/
theorem wilsonModulus_gauge {act : 𝔄 → F → F} (hact : PacketRep act) {nrm : F → ℝ}
    {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (hnrm : ∀ k ∈ C.G, ∀ v, nrm (act k v) = nrm v)
    (h ϱ : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (Y : Grid n → F) :
    wilsonModulus act nrm h ϱ (gaugeAct C g c) (fun z => act (g z) (Y z)) =
      wilsonModulus act nrm h ϱ c Y := by
  have e1 : ∀ μ m, wilsonSq act nrm h (gaugeAct C g c) (fun z => act (g z) (Y z)) μ m =
      wilsonSq act nrm h c Y μ m := fun μ m => by
    simp only [wilsonSq, wilsonDiff_gauge C hact, hnrm _ (hg _)]
  have e2 : ∀ μ m, wilsonSqNeg act nrm h (gaugeAct C g c) (fun z => act (g z) (Y z)) μ m =
      wilsonSqNeg act nrm h c Y μ m := fun μ m => by
    simp only [wilsonSqNeg, wilsonDiffNeg_gauge C hact, hnrm _ (hg _)]
  simp only [wilsonModulus, e1, e2]

/-- The spinor representation is a packet representation. -/
theorem packetRep_ρS : PacketRep (fun (P : 𝔄) (v : 𝓢) => C.ρS P v) where
  conj a b P v := by
    simp only [map_mul, ContinuousLinearMap.mul_apply, algHom_inv_apply]
  sub a v w := map_sub _ v w

/-- The Higgs representation is a packet representation. -/
theorem packetRep_ρH : PacketRep (fun (P : 𝔄) (v : 𝓗) => C.ρH P v) where
  conj a b P v := by
    simp only [map_mul, ContinuousLinearMap.mul_apply, algHom_inv_apply]
  sub a v w := map_sub _ v w

/-- The adjoint action `Ad_P X = P X P⁻¹` (curvature packets) is a packet representation. -/
theorem packetRep_Ad : PacketRep (fun (P X : 𝔄) => P * X * Ring.inverse P) where
  conj a b P v := by
    rw [ring_inverse_conj]
    simp only [Ring.inverse_unit, mul_assoc, Units.inv_mul_cancel_left]
  sub a v w := by rw [mul_sub, sub_mul]

/-- **(b), Wilson moduli of the spinor packet** (unitary `ρ_S`). -/
theorem wilsonModulus_spinor_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h ϱ : ℝ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) :
    wilsonModulus (fun (P : 𝔄) (v : 𝓢) => C.ρS P v) (fun v => ‖v‖ ^ 2) h ϱ (gaugeAct C g c)
        (gaugeAct C g c).Ψ =
      wilsonModulus (fun (P : 𝔄) (v : 𝓢) => C.ρS P v) (fun v => ‖v‖ ^ 2) h ϱ c c.Ψ :=
  wilsonModulus_gauge C (packetRep_ρS C) hg (fun k hk v => by simp only [C.ρS_isom k hk]) h ϱ c _

/-- **(b), Wilson moduli of the Higgs packet** (`Re⟨·,·⟩`-norm). -/
theorem wilsonModulus_higgs_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h ϱ : ℝ)
    (c : LinkConfig n 𝔄 𝓗 𝓢) :
    wilsonModulus (fun (P : 𝔄) (v : 𝓗) => C.ρH P v) (fun v => C.hermH v v) h ϱ (gaugeAct C g c)
        (gaugeAct C g c).H =
      wilsonModulus (fun (P : 𝔄) (v : 𝓗) => C.ρH P v) (fun v => C.hermH v v) h ϱ c c.H :=
  wilsonModulus_gauge C (packetRep_ρH C) hg (fun k hk v => C.hermH_inv k hk v v) h ϱ c _

/-- **(b), adjoint Wilson moduli of the curvature packet** (`Ad`, invariant metric). -/
theorem wilsonModulus_curv_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h ϱ : ℝ)
    {c : LinkConfig n 𝔄 𝓗 𝓢} (hc : Chart c) (μ ν : Fin 4) :
    wilsonModulus (fun (P X : 𝔄) => P * X * Ring.inverse P) (fun X => C.ipA X X) h ϱ
        (gaugeAct C g c) (fun x => antisym (curv h (gaugeAct C g c) x) μ ν) =
      wilsonModulus (fun (P X : 𝔄) => P * X * Ring.inverse P) (fun X => C.ipA X X) h ϱ c
        (fun x => antisym (curv h c x) μ ν) := by
  have e : (fun x => antisym (curv h (gaugeAct C g c) x) μ ν) =
      fun x => (g x : 𝔄) * antisym (curv h c x) μ ν * Ring.inverse (g x : 𝔄) := by
    funext x
    rw [antisym_curv_gauge C hg h hc, Ring.inverse_unit]
  rw [e]
  refine wilsonModulus_gauge C (packetRep_Ad) hg (fun k hk X => ?_) h ϱ c _
  rw [Ring.inverse_unit, C.ipA_conj k hk]

end Graphs

/-! ### (c): the covector norm in the positive physical mass metric -/

section Covector

variable (C : CovData 𝔄 𝓗 𝓢)

/-- A physical tangent: coframe tangent, link tangent `α_μ = h⁻¹ U̇_μ U_μ⁻¹`, Higgs, spinor and
co-spinor tangents. -/
structure Tangent (n : ℕ) (𝔄 𝓗 𝓢 : Type*) [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] where
  ε : Grid n → Mat
  α : Fin 4 → Grid n → 𝔄
  η : Grid n → 𝓗
  ψ : Grid n → 𝓢
  ψb : Grid n → CoSpinor 𝓢

/-- The curve realizing a physical tangent: `U_t = e^{t h α} U` (so `h⁻¹ U̇ U⁻¹ = α` at `t = 0`),
the other fields affine. -/
def curve (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (τ : Tangent n 𝔄 𝓗 𝓢) (t : ℝ) :
    LinkConfig n 𝔄 𝓗 𝓢 where
  e := c.e + t • τ.ε
  U μ x := exp ((t * h) • τ.α μ x) * c.U μ x
  H := c.H + t • τ.η
  Ψ := c.Ψ + t • τ.ψ
  Ψb := c.Ψb + t • τ.ψb

/-- **The complete action covector** in the physical link tangent. -/
def linkCov (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) (τ : Tangent n 𝔄 𝓗 𝓢) : ℝ :=
  deriv (fun t => linkAction C.toData h (curve h c τ t)) 0

/-- The covector of the native local action: along any curve of records realizing `τ`, the
derivative of `S_h^{loc}` is `linkCov`. -/
theorem deriv_localAction_eq_linkCov (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (τ : Tangent n 𝔄 𝓗 𝓢)
    (yt : ℝ → Grid n → Field 𝔄 𝓗 𝓢) (hyt : ∀ t, toLinks h (yt t) = curve h (toLinks h y) τ t) :
    deriv (fun t => localAction C.toData h (yt t)) 0 = linkCov C h (toLinks h y) τ := by
  simp only [linkCov, localAction_eq_linkAction, hyt]

/-- The tangent map of the site gauge: `α ↦ Ad_g α`, `η ↦ ρ_H(g) η`, `ψ ↦ ρ_S(g) ψ`,
`ψ̄ ↦ ψ̄ ρ_S(g)⁻¹`; the coframe tangent is untouched. -/
def tangentAct (g : Grid n → 𝔄ˣ) (τ : Tangent n 𝔄 𝓗 𝓢) : Tangent n 𝔄 𝓗 𝓢 where
  ε := τ.ε
  α μ x := (g x : 𝔄) * τ.α μ x * ↑(g x)⁻¹
  η x := C.ρH (g x) (τ.η x)
  ψ x := C.ρS (g x) (τ.ψ x)
  ψb x := (τ.ψb x).comp (C.ρS ↑(g x)⁻¹)

theorem exp_conj_units (u : 𝔄ˣ) (X : 𝔄) : exp ((u : 𝔄) * X * ↑u⁻¹) = u * exp X * ↑u⁻¹ := by
  let +nondep : NormedAlgebra ℚ 𝔄 := .restrictScalars ℚ ℝ 𝔄
  exact exp_units_conj u X

/-- The gauge action maps the curve of `τ` to the curve of the transformed tangent. -/
theorem gaugeAct_curve (g : Grid n → 𝔄ˣ) (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢)
    (τ : Tangent n 𝔄 𝓗 𝓢) (t : ℝ) :
    gaugeAct C g (curve h c τ t) = curve h (gaugeAct C g c) (tangentAct C g τ) t := by
  have hU : ∀ μ x, (g x : 𝔄) * (exp ((t * h) • τ.α μ x) * c.U μ x) * ↑(g (x + unitVec n μ))⁻¹ =
      exp ((t * h) • ((g x : 𝔄) * τ.α μ x * ↑(g x)⁻¹)) *
        ((g x : 𝔄) * c.U μ x * ↑(g (x + unitVec n μ))⁻¹) := by
    intro μ x
    rw [← smul_mul_assoc, ← mul_smul_comm, exp_conj_units]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  ext1
  · rfl
  · funext μ x
    exact hU μ x
  · funext x
    simp only [gaugeAct, curve, tangentAct, Pi.add_apply, Pi.smul_apply, map_add, map_smul]
  · funext x
    simp only [gaugeAct, curve, tangentAct, Pi.add_apply, Pi.smul_apply, map_add, map_smul]
  · funext x
    simp only [gaugeAct, curve, tangentAct, Pi.add_apply, Pi.smul_apply,
      ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp]

theorem ring_inverse_exp_mul (a : 𝔄) {u : 𝔄} (hu : IsUnit u) :
    Ring.inverse (exp a * u) = Ring.inverse u * exp (-a) := by
  obtain ⟨v, rfl⟩ := hu
  let w : 𝔄ˣ := ⟨exp a, exp (-a), exp_mul_exp_neg a, exp_neg_mul_exp a⟩
  have e : exp a * (v : 𝔄) = ((w * v : 𝔄ˣ) : 𝔄) := rfl
  rw [e, Ring.inverse_unit, Ring.inverse_unit]
  rfl

/-- The plaquette chart is open along the curve of a tangent. -/
theorem eventually_chart_curve (h : ℝ) {c : LinkConfig n 𝔄 𝓗 𝓢} (hu : ∀ μ x, IsUnit (c.U μ x))
    (hc : Chart c) (τ : Tangent n 𝔄 𝓗 𝓢) : ∀ᶠ t in 𝓝 (0 : ℝ), Chart (curve h c τ t) := by
  let +nondep : NormedAlgebra ℚ 𝔄 := .restrictScalars ℚ ℝ 𝔄
  have hcont : ∀ x μ ν, Continuous fun t : ℝ => plaq (curve h c τ t) x μ ν := by
    intro x μ ν
    have e : (fun t : ℝ => plaq (curve h c τ t) x μ ν) = fun t =>
        exp ((t * h) • τ.α μ x) * c.U μ x * (exp ((t * h) • τ.α ν (x + unitVec n μ)) *
          c.U ν (x + unitVec n μ)) * (Ring.inverse (c.U μ (x + unitVec n ν)) *
          exp (-((t * h) • τ.α μ (x + unitVec n ν)))) *
          (Ring.inverse (c.U ν x) * exp (-((t * h) • τ.α ν x))) := by
      funext t
      simp only [plaq, curve, ring_inverse_exp_mul _ (hu _ _)]
    rw [e]
    fun_prop
  have hev : ∀ x (μ ν : Fin 4), μ < ν →
      ∀ᶠ t in 𝓝 (0 : ℝ), ‖plaq (curve h c τ t) x μ ν - 1‖ < 1 := by
    intro x μ ν hμν
    have h0 : curve h c τ 0 = c := by
      ext1 <;> simp [curve] <;> funext x <;> ext v <;> simp
    have hlt : ‖plaq (curve h c τ 0) x μ ν - 1‖ < 1 := by rw [h0]; exact hc x μ ν hμν
    exact ((hcont x μ ν).sub continuous_const).norm.continuousAt.eventually_lt
      continuousAt_const hlt
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x (μ ν : Fin 4), μ < ν →
      ‖plaq (curve h c τ t) x μ ν - 1‖ < 1 := by
    simp only [Filter.eventually_all]
    intro x μ ν
    exact hev x μ ν
  exact hall

/-- **(c), covariance of the covector**: the covector at the transformed configuration, evaluated
on the transformed tangent, equals the original covector on the original tangent (no derivative
of the gauge appears). -/
theorem linkCov_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    {c : LinkConfig n 𝔄 𝓗 𝓢} (hu : ∀ μ x, IsUnit (c.U μ x)) (hc : Chart c)
    (τ : Tangent n 𝔄 𝓗 𝓢) :
    linkCov C h (gaugeAct C g c) (tangentAct C g τ) = linkCov C h c τ := by
  unfold linkCov
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_chart_curve h hu hc τ] with t ht
  rw [← gaugeAct_curve, linkAction_gauge C hg h ht]

/-- **The positive physical mass metric** on tangents:
`h⁴ Σ_x (|ε|² + Σ_μ ⟨α_μ, α_μ⟩_𝐠 + Re⟨η, η⟩ + |ψ|² + |ψ̄|²)`. -/
def massSq (h : ℝ) (τ : Tangent n 𝔄 𝓗 𝓢) : ℝ :=
  h ^ 4 * ∑ x, (‖τ.ε x‖ ^ 2 + ∑ μ, C.ipA (τ.α μ x) (τ.α μ x) + C.hermH (τ.η x) (τ.η x) +
    ‖τ.ψ x‖ ^ 2 + ‖τ.ψb x‖ ^ 2)

/-- **(c)**: the tangent map of a site gauge is an isometry of the physical mass metric. -/
theorem massSq_tangentAct {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    (τ : Tangent n 𝔄 𝓗 𝓢) : massSq C h (tangentAct C g τ) = massSq C h τ := by
  simp only [massSq, tangentAct]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [C.hermH_inv _ (hg x), C.ρS_isom _ (hg x), norm_comp_ρS_inv C (hg x)]
  simp only [C.ipA_conj _ (hg x)]

theorem tangentAct_inv (g : Grid n → 𝔄ˣ) (τ : Tangent n 𝔄 𝓗 𝓢) :
    tangentAct C g (tangentAct C (fun x => (g x)⁻¹) τ) = τ := by
  obtain ⟨ε, α, η, ψ, ψb⟩ := τ
  simp only [tangentAct, inv_inv]
  congr 1
  · funext μ x
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  · funext x
    exact algHom_apply_inv C.ρH (g x) (η x)
  · funext x
    exact algHom_apply_inv C.ρS (g x) (ψ x)
  · funext x
    ext v
    simp only [ContinuousLinearMap.comp_apply, algHom_apply_inv]

/-- The dual norm of the covector in the positive physical mass metric:
`sup { |DS[τ]| : massSq τ ≤ 1 }`. -/
def covNorm (h : ℝ) (c : LinkConfig n 𝔄 𝓗 𝓢) : ℝ :=
  sSup ((fun τ => |linkCov C h c τ|) '' {τ | massSq C h τ ≤ 1})

/-- **(c)**: the norm of the complete action covector is unchanged in the positive physical mass
metric whose link tangent is `α_μ = h⁻¹ U̇_μ U_μ⁻¹`. -/
theorem covNorm_gauge {g : Grid n → 𝔄ˣ} (hg : ∀ x, g x ∈ C.G) (h : ℝ)
    {c : LinkConfig n 𝔄 𝓗 𝓢} (hu : ∀ μ x, IsUnit (c.U μ x)) (hc : Chart c) :
    covNorm C h (gaugeAct C g c) = covNorm C h c := by
  have hset : (fun τ => |linkCov C h (gaugeAct C g c) τ|) '' {τ | massSq C h τ ≤ 1} =
      (fun τ => |linkCov C h c τ|) '' {τ | massSq C h τ ≤ 1} := by
    ext r
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨τ', hτ', rfl⟩
      refine ⟨tangentAct C (fun x => (g x)⁻¹) τ', ?_, ?_⟩
      · rwa [← massSq_tangentAct C hg h, tangentAct_inv]
      · rw [← linkCov_gauge C hg h hu hc, tangentAct_inv]
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨tangentAct C g τ, by rwa [massSq_tangentAct C hg h], by
        rw [linkCov_gauge C hg h hu hc τ]⟩
  unfold covNorm
  rw [hset]

/-- The links of a native record are units. -/
theorem isUnit_toLinks (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (μ : Fin 4) (x : Grid n) :
    IsUnit ((toLinks h y).U μ x) :=
  ⟨⟨exp (h • gauge y μ x), exp (-(h • gauge y μ x)), exp_mul_exp_neg _, exp_neg_mul_exp _⟩, rfl⟩

/-- **(c) for native records**: under a gauge transform on the chart, the dual norm of the covector
of the native local action is unchanged. -/
theorem covNorm_record_gauge {h : ℝ} {g : Grid n → 𝔄ˣ} {y y' : Grid n → Field 𝔄 𝓗 𝓢}
    (hy : IsGaugeTransform C h g y y') (hc : Chart (toLinks h y)) :
    covNorm C h (toLinks h y') = covNorm C h (toLinks h y) := by
  rw [hy.2]
  exact covNorm_gauge C hy.1 h (isUnit_toLinks h y) hc

end Covector

/-! ### The unitary gauge group of a C*-algebra -/

section UnitaryGroup

variable {𝔅 : Type*} [CStarAlgebra 𝔅]

/-- The unitary group of a C*-algebra as a subgroup of its units (the gauge group of the Coulomb
clause `RootedCoulomb.rooted_coulomb_normalization`, whose links and site gauges are unitary). -/
def unitaryUnits (𝔅 : Type*) [CStarAlgebra 𝔅] : Subgroup 𝔅ˣ := (Unitary.toUnits (R := 𝔅)).range

/-- Unitary conjugation is norm preserving: the field `CovData.norm_conj` holds for the unitary
gauge group of a C*-algebra. -/
theorem norm_conj_unitaryUnits {g : 𝔅ˣ} (hg : g ∈ unitaryUnits 𝔅) (X : 𝔅) :
    ‖(g : 𝔅) * X * ↑g⁻¹‖ = ‖X‖ := by
  obtain ⟨u, rfl⟩ := hg
  have h1 : ((Unitary.toUnits u : 𝔅ˣ) : 𝔅) = u := rfl
  have h2 : (((Unitary.toUnits u)⁻¹ : 𝔅ˣ) : 𝔅) = star (u : 𝔅) := rfl
  rw [h1, h2, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem u.2),
    CStarRing.norm_mem_unitary_mul _ u.2]

end UnitaryGroup

/-! ### Non-vacuity -/

section NonVacuity

/-- The trivial covariant packet over `𝔄 = 𝓗 = 𝓢 = ℝ` with trivial gauge group: all covariance
fields hold. -/
def trivialCovData : CovData ℝ ℝ ℝ where
  κ := 1
  Λ := 0
  lamH := 1
  vH := 1
  ipA := ContinuousLinearMap.mul ℝ ℝ
  hermH := ContinuousLinearMap.mul ℝ ℝ
  ρH := Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)
  ρH_cont := LinearMap.continuous_of_finiteDimensional (Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)).toLinearMap
  ρS := Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)
  ρS_cont := LinearMap.continuous_of_finiteDimensional (Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)).toLinearMap
  σ := 0
  γ := fun _ => 0
  yukawa := 0
  G := ⊥
  norm_conj g hg X := by rw [Subgroup.mem_bot] at hg; subst hg; simp
  ipA_conj g hg X Y := by rw [Subgroup.mem_bot] at hg; subst hg; simp
  hermH_inv g hg u v := by rw [Subgroup.mem_bot] at hg; subst hg; simp
  σ_comm g hg m := by simp
  γ_comm g hg a := by simp
  yukawa_cov g hg H := by simp
  ρS_isom g hg v := by rw [Subgroup.mem_bot] at hg; subst hg; simp

/-- Multiplication `ℂ → End_ℝ(ℂ)`, the defining representation of `U(1) ⊂ ℂˣ`. -/
def mulAlg : ℂ →ₐ[ℝ] (ℂ →L[ℝ] ℂ) where
  toFun z := ContinuousLinearMap.lsmul ℝ ℂ z
  map_one' := by ext; simp
  map_mul' z w := by ext v; simp [mul_assoc]
  map_zero' := by ext; simp
  map_add' z w := by ext; simp
  commutes' r := by ext; simp [Algebra.algebraMap_eq_smul_one]

theorem mulAlg_apply (z v : ℂ) : mulAlg z v = z * v := rfl

theorem norm_coe_of_mem_unitaryUnits {g : ℂˣ} (hg : g ∈ unitaryUnits ℂ) : ‖(g : ℂ)‖ = 1 := by
  obtain ⟨u, rfl⟩ := hg
  exact CStarRing.norm_of_mem_unitary u.2

theorem conj_units_complex (g : ℂˣ) (X : ℂ) : (g : ℂ) * X * ↑g⁻¹ = X := by
  rw [mul_comm (g : ℂ) X, mul_assoc, Units.mul_inv, mul_one]

/-- **A `U(1)` covariant packet** (`𝔄 = 𝓗 = 𝓢 = ℂ`, gauge group the unitary units of `ℂ`, Higgs
and spinor in the defining representation, real inner products as invariant forms): every
covariance field holds with a nontrivial gauge group. -/
def u1CovData : CovData ℂ ℂ ℂ where
  κ := 1
  Λ := 0
  lamH := 1
  vH := 1
  ipA := innerSL ℝ
  hermH := innerSL ℝ
  ρH := mulAlg
  ρH_cont := LinearMap.continuous_of_finiteDimensional mulAlg.toLinearMap
  ρS := mulAlg
  ρS_cont := LinearMap.continuous_of_finiteDimensional mulAlg.toLinearMap
  σ := 0
  γ := fun _ => 1
  yukawa := 0
  G := unitaryUnits ℂ
  norm_conj g _ X := by rw [conj_units_complex]
  ipA_conj g _ X Y := by rw [conj_units_complex, conj_units_complex]
  hermH_inv g hg u v := by
    have h1 := norm_coe_of_mem_unitaryUnits hg
    show inner ℝ ((g : ℂ) * u) ((g : ℂ) * v) = inner ℝ u v
    rw [Complex.inner, Complex.inner, map_mul,
      show (g : ℂ) * v * ((starRingEnd ℂ) (g : ℂ) * (starRingEnd ℂ) u) =
        ((g : ℂ) * (starRingEnd ℂ) (g : ℂ)) * (v * (starRingEnd ℂ) u) by ring,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    simp
  σ_comm g _ m := by simp
  γ_comm g _ a := by simp
  yukawa_cov g _ H := by simp
  ρS_isom g hg v := by rw [mulAlg_apply, norm_mul, norm_coe_of_mem_unitaryUnits hg, one_mul]

/-- A record with vanishing connection. -/
def flatGaugeRec {n : ℕ} (y : Grid n → Field ℂ ℂ ℂ) : Grid n → Field ℂ ℂ ℂ :=
  fun x => (coframe y x, 0, higgs y x, psi y x, psiBar y x)

/-- Its transform by a constant phase `u`: `H ↦ u H`, `Ψ ↦ u Ψ`, `Ψ̄ ↦ Ψ̄ u⁻¹`. -/
def rotRec {n : ℕ} (u : ℂˣ) (y : Grid n → Field ℂ ℂ ℂ) : Grid n → Field ℂ ℂ ℂ :=
  fun x => (coframe y x, 0, (u : ℂ) * higgs y x, (u : ℂ) * psi y x,
    (psiBar y x).comp (mulAlg ↑u⁻¹))

/-- **Non-vacuity of clause (a)** with a nontrivial gauge group: the native local action of the
`U(1)` packet is unchanged by a constant phase rotation of the Higgs field and the spinors. -/
example {n : ℕ} [NeZero n] (h : ℝ) (u : ℂˣ) (hu : u ∈ unitaryUnits ℂ)
    (y : Grid n → Field ℂ ℂ ℂ) :
    localAction u1CovData.toData h (rotRec u y) =
      localAction u1CovData.toData h (flatGaugeRec y) := by
  refine localAction_gauge u1CovData (g := fun _ => u) ⟨fun _ => hu, ?_⟩ ?_
  · ext1
    · rfl
    · funext μ x
      simp [toLinks, gaugeAct, rotRec, flatGaugeRec, NativeDensity.gauge, Units.ne_zero]
    · rfl
    · rfl
    · rfl
  · intro x μ ν _
    simp [plaq, toLinks, flatGaugeRec, NativeDensity.gauge]

end NonVacuity


end

end NativeGauge
end RenewalGeometry
