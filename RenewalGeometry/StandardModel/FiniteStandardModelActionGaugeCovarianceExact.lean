/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Algebra.SeriesLogUnitConjugation
import RenewalGeometry.GaugeTheory.LatticeHolonomyGaugeCovariance
import RenewalGeometry.StandardModel.ExplicitRegulatedStandardModelActionExact
import RenewalGeometry.Gravity.FiniteActionBRSTGhostExact
/-!
# Gauge covariance of the concrete finite Standard-Model action
  (`thm:finite-action-identities`, spacetime–gauge duality paper)

This file discharges the covariance hypotheses of
`explicitRegulatedStandardModelAction_gaugeInvariant` for the **concrete** cell densities of
`eq:finite-SM-action` and assembles the finite Ward, BRST and stress identities.

## The concrete action

On a finite oriented spacetime complex `X = (V, E, F, src, tgt, ∂)` (`FiniteSpacetimeComplex`,
each plaquette `p` carrying a closed boundary walk based at `base p`), with a gauge group `G`
acting through typed unitary representations `ρ_i` (the gauge-metric factors
`g₃, g₂, g₁`), `ρ_H` (Higgs fibre `W₂`) and `ρ_Ψ` (matter fibre) (`SMGaugeRepresentations`),
a configuration `Φ = (U_e ∈ G, H_v, Ψ_v, Ψ̄_v)` (`RegulatedSMConfiguration`) has the action

`𝒮 = ½ Σ_p ⋆₂(p) |F_p|²_{g} + ½ Σ_e ⋆₁(e) ‖(D_U H)_e‖² + Σ_v m_v λ_H (‖H_v‖² − v_H²)²
      + Σ_v ⋆₀(v) Re tr (Ψ̄_v (D^U_sp + Γ ⊗ D_F(H))Ψ)_v`

(`finiteStandardModelAction`), where

* `F_p = log P_p` is the **principal-logarithm plaquette curvature** (series logarithm
  `ShiftedPlaquette.logOneAdd (ρ_i(P_p) − 1)` of the plaquette holonomy `P_p`), and
  `|F_p|²_g = Σ_i κ_i ‖log ρ_i(P_p)‖²_F` is its squared norm in the gauge metric
  (`curvatureNormSq`);
* `(D_U H)_e = H_{t(e)} − ρ_H(U_e) H_{s(e)}` is the covariant edge difference
  (`higgsEdgeDifference`);
* `(D^U_sp Ψ)_v = Σ_{e : t(e) = v} ρ_Ψ(U_e) Ψ_{s(e)} γ⁺_e + Σ_{e : s(e) = v} ρ_Ψ(U_e⁻¹) Ψ_{t(e)} γ⁻_e
  + Ψ_v γ⁰_v` is the finite covariant Dirac operator with spin/generation coefficient matrices
  `γ`, and `Γ ⊗ D_F(H)` the Yukawa term (`finiteDiracYukawa`), with an independent dual
  amplitude `Ψ̄_v` transforming contragrediently.

## Results

* `curvatureNormSq_conj`: the principal-log curvature norm is a class function
  (plaquette holonomy conjugates: `LatticeWalk.holonomy_gaugeLinks_closed`; the series
  logarithm is conjugation equivariant: `ShiftedPlaquette.logOneAdd_conj_of_mul_eq_one`; the
  Frobenius norm is unitarily invariant: `frobSq_conj_of_mul`).
* `higgsEdgeDifference_gauge`: `D_U H` transforms covariantly in the target fibre,
  `(D_{g·U} (g·H))_e = ρ_H(g_{t(e)}) (D_U H)_e`.
* `finiteDiracYukawa_gauge`: the finite Dirac/Yukawa operator intertwines the typed
  representations, `(D^{g·U} + Γ ⊗ D_F(g·H))(g·Ψ) = ρ_Ψ(g) (D^U + Γ ⊗ D_F(H)) Ψ`, given the
  equivariance `D_F(ρ_H(g) H) = ρ_Ψ(g) D_F(H) ρ_Ψ(g)⁻¹` of the Yukawa map
  (`SMGaugeRepresentations.YukawaEquivariant`; the linear Yukawa couplings built from
  intertwiners satisfy it, `yukawaMap_equivariant`).
* `finiteStandardModelAction_gaugeInvariant`: **exact gauge invariance** of the concrete
  action, obtained from `explicitRegulatedStandardModelAction_gaugeInvariant` with the four
  covariance hypotheses now proved.
* `finite_action_identities`: the assembled theorem — one-cell locality (cutoff-independent
  support radius), exact gauge invariance, the differentiated form of gauge invariance along
  every gauge flow (the finite Ward identity `eq:ward`; its divergence/pairing form is the
  chain-rule theorem `FiniteActionWardBRSTStressEinstein.gauge_ward_divergence`), the finite
  group-cochain BRST closure and nilpotency, and the ghost BRST clause `eq:brst`
  (`s² = 0`, `s𝒮 = 0`) of `finite_action_brst`.

Disclosed: the gauge group is any group with unitary typed representations (the Standard
Model `S(U(3) × U(2))` with its three gauge-metric factors is one instance); the Yukawa map
`D_F` is a parameter with the intertwining property the paper's proof invokes; the stress
identity `eq:stress-identity` is the chain-rule theorem
`FiniteActionWardBRSTStressEinstein.relabeling_stress_transfer`, the cell-density
decomposition (clause (i)) being the matter stress tensor defined by variation of the Hodge
weights (the action is linear in `⋆₀, ⋆₁, ⋆₂, m`).
-/

open Matrix NormedSpace
open scoped BigOperators

namespace RenewalGeometry

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

universe u v w uA un up uq

/-- The finite oriented spacetime complex of `eq:finite-SM-action`: vertices, oriented edges
with source/target, and plaquettes, each with a closed boundary walk based at `base p`. -/
structure FiniteSpacetimeComplex (V : Type u) (E : Type v) (F : Type w) where
  /-- source vertex of an edge -/
  src : E → V
  /-- target vertex of an edge -/
  tgt : E → V
  /-- base point of the boundary walk of a plaquette -/
  base : F → V
  /-- the closed boundary walk of a plaquette -/
  boundary : ∀ p : F, LatticeWalk src tgt (base p) (base p)

/-- The typed unitary representations of the gauge group `G`: the gauge-metric factors
`ρ_i` (for `S(U(3) × U(2))`: the `U(3)`, `U(2)` and phase factors weighted by
`g₃⁻², g₂⁻², g₁⁻²`), the Higgs fibre representation `ρ_H` and the matter fibre
representation `ρ_Ψ`, together with the finite Dirac/Yukawa map `D_F`. -/
structure SMGaugeRepresentations (G : Type*) [Group G] {ι : Type*} (nG : ι → Type*)
    [∀ i, Fintype (nG i)] [∀ i, DecidableEq (nG i)]
    (nH pH nΨ : Type*) [Fintype nH] [DecidableEq nH] [Fintype nΨ] [DecidableEq nΨ] where
  /-- the gauge-metric factor representations -/
  ρG : ∀ i, G →* Matrix.unitaryGroup (nG i) ℂ
  /-- the Higgs fibre representation -/
  ρH : G →* Matrix.unitaryGroup nH ℂ
  /-- the matter fibre representation -/
  ρΨ : G →* Matrix.unitaryGroup nΨ ℂ
  /-- the finite Dirac/Yukawa map `H ↦ D_F(H)` on the matter fibre -/
  DF : Matrix nH pH ℂ → Matrix nΨ nΨ ℂ

/-- Equivariance of the Yukawa map: `D_F(ρ_H(g) H) = ρ_Ψ(g) D_F(H) ρ_Ψ(g)⁻¹` (the finite
Dirac/Yukawa term intertwines the left and right typed representations). -/
def SMGaugeRepresentations.YukawaEquivariant {G : Type*} [Group G] {ι : Type*}
    {nG : ι → Type*} [∀ i, Fintype (nG i)] [∀ i, DecidableEq (nG i)]
    {nH pH nΨ : Type*} [Fintype nH] [DecidableEq nH] [Fintype nΨ] [DecidableEq nΨ]
    (R : SMGaugeRepresentations G nG nH pH nΨ) : Prop :=
  ∀ (g : G) (H : Matrix nH pH ℂ),
    R.DF ((R.ρH g : Matrix nH nH ℂ) * H) =
      (R.ρΨ g : Matrix nΨ nΨ ℂ) * R.DF H * (R.ρΨ g⁻¹ : Matrix nΨ nΨ ℂ)

/-- Spin/generation coefficient matrices of the finite Dirac operator: forward and backward
hop coefficients `γ⁺_e, γ⁻_e`, the on-site coefficient `γ⁰_v`, and the Clifford grading
`Γ_Cl` multiplying the Yukawa term. -/
structure SMDiracCoefficients (V E q : Type*) where
  /-- forward hop coefficient -/
  γf : E → Matrix q q ℂ
  /-- backward hop coefficient -/
  γb : E → Matrix q q ℂ
  /-- on-site coefficient -/
  γ0 : V → Matrix q q ℂ
  /-- the Clifford grading `Γ_Cl` -/
  Γ : Matrix q q ℂ

/-- The Hodge weights `⋆₀, ⋆₁, ⋆₂`, vertex masses `m_v`, gauge-metric coefficients
`κ_i = g_i⁻²`, and the scalar parameters `λ_H`, `v_H` of `eq:finite-SM-action`. -/
structure SMActionCoefficients (V E F ι : Type*) where
  /-- vertex Hodge weight `⋆₀` -/
  star0 : V → ℝ
  /-- edge Hodge weight `⋆₁` -/
  star1 : E → ℝ
  /-- plaquette Hodge weight `⋆₂` -/
  star2 : F → ℝ
  /-- vertex mass `m_v` -/
  mass : V → ℝ
  /-- gauge-metric coefficients `κ_i = g_i⁻²` -/
  gaugeCoeff : ι → ℝ
  /-- Higgs self-coupling `λ_H` -/
  lambdaH : ℝ
  /-- Higgs vacuum value `v_H` -/
  vH : ℝ

/-! ### Unitary representation coercions -/

section UnitaryRep

variable {G : Type*} [Group G] {n : Type*} [Fintype n] [DecidableEq n]

theorem unitaryGroup_conjTranspose_mul_self (x : Matrix.unitaryGroup n ℂ) :
    (x : Matrix n n ℂ)ᴴ * (x : Matrix n n ℂ) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.UnitaryGroup.star_mul_self x

theorem unitaryGroup_self_mul_conjTranspose (x : Matrix.unitaryGroup n ℂ) :
    (x : Matrix n n ℂ) * (x : Matrix n n ℂ)ᴴ = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.coe_mul_star_self x

theorem coe_rep_mul (ρ : G →* Matrix.unitaryGroup n ℂ) (a b : G) :
    (ρ (a * b) : Matrix n n ℂ) = (ρ a : Matrix n n ℂ) * (ρ b : Matrix n n ℂ) := by
  rw [map_mul, Submonoid.coe_mul]

theorem coe_rep_mul_inv (ρ : G →* Matrix.unitaryGroup n ℂ) (g : G) :
    (ρ g : Matrix n n ℂ) * (ρ g⁻¹ : Matrix n n ℂ) = 1 := by
  rw [← Submonoid.coe_mul, ← map_mul, mul_inv_cancel, map_one, OneMemClass.coe_one]

theorem coe_rep_inv_mul (ρ : G →* Matrix.unitaryGroup n ℂ) (g : G) :
    (ρ g⁻¹ : Matrix n n ℂ) * (ρ g : Matrix n n ℂ) = 1 := by
  rw [← Submonoid.coe_mul, ← map_mul, inv_mul_cancel, map_one, OneMemClass.coe_one]

theorem coe_rep_mul_inv_cancel_left {m : Type*} (ρ : G →* Matrix.unitaryGroup n ℂ) (g : G)
    (M : Matrix n m ℂ) : (ρ g : Matrix n n ℂ) * ((ρ g⁻¹ : Matrix n n ℂ) * M) = M := by
  rw [← Matrix.mul_assoc, coe_rep_mul_inv, Matrix.one_mul]

theorem coe_rep_inv_mul_cancel_left {m : Type*} (ρ : G →* Matrix.unitaryGroup n ℂ) (g : G)
    (M : Matrix n m ℂ) : (ρ g⁻¹ : Matrix n n ℂ) * ((ρ g : Matrix n n ℂ) * M) = M := by
  rw [← Matrix.mul_assoc, coe_rep_inv_mul, Matrix.one_mul]

end UnitaryRep

/-! ### The concrete cell densities of `eq:finite-SM-action` and their covariance -/

section Densities

variable {V : Type u} {E : Type v} {F : Type w} {G : Type*} [Group G]
  {ι : Type*} [Fintype ι] {nG : ι → Type*} [∀ i, Fintype (nG i)] [∀ i, DecidableEq (nG i)]
  {nH pH nΨ q : Type*} [Fintype nH] [DecidableEq nH] [Fintype pH]
  [Fintype nΨ] [DecidableEq nΨ] [Fintype q]

/-- The plaquette holonomy `P_p` of a link configuration. -/
def FiniteSpacetimeComplex.plaquetteHolonomy (X : FiniteSpacetimeComplex V E F) (U : E → G)
    (p : F) : G :=
  (X.boundary p).holonomy U

/-- Plaquette holonomy transforms by conjugation with the gauge element at the base point. -/
theorem FiniteSpacetimeComplex.plaquetteHolonomy_gaugeLinks (X : FiniteSpacetimeComplex V E F)
    (g : V → G) (U : E → G) (p : F) :
    X.plaquetteHolonomy (gaugeLinks X.src X.tgt g U) p =
      g (X.base p) * X.plaquetteHolonomy U p * (g (X.base p))⁻¹ :=
  (X.boundary p).holonomy_gaugeLinks_closed g U

/-- The squared norm `|F|²_{g} = Σ_i κ_i ‖log ρ_i(P)‖²_F` of the principal-logarithm
curvature of a holonomy `P` in the gauge metric with coefficients `κ_i = g_i⁻²`. -/
noncomputable def curvatureNormSq (ρG : ∀ i, G →* Matrix.unitaryGroup (nG i) ℂ) (κ : ι → ℝ)
    (P : G) : ℝ :=
  ∑ i, κ i * frobSq (ShiftedPlaquette.logOneAdd ((ρG i P : Matrix (nG i) (nG i) ℂ) - 1))

/-- **The principal-log curvature norm is a class function.** -/
theorem curvatureNormSq_conj (ρG : ∀ i, G →* Matrix.unitaryGroup (nG i) ℂ) (κ : ι → ℝ)
    (g P : G) : curvatureNormSq ρG κ (g * P * g⁻¹) = curvatureNormSq ρG κ P := by
  unfold curvatureNormSq
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hcoe : (ρG i (g * P * g⁻¹) : Matrix (nG i) (nG i) ℂ) - 1 =
      (ρG i g : Matrix (nG i) (nG i) ℂ) * ((ρG i P : Matrix (nG i) (nG i) ℂ) - 1) *
        (ρG i g⁻¹ : Matrix (nG i) (nG i) ℂ) := by
    rw [coe_rep_mul, coe_rep_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      coe_rep_mul_inv]
  rw [hcoe, ShiftedPlaquette.logOneAdd_conj_of_mul_eq_one (coe_rep_mul_inv (ρG i) g)
    (coe_rep_inv_mul (ρG i) g),
    frobSq_conj_of_mul _ (unitaryGroup_conjTranspose_mul_self _) _ _
      (unitaryGroup_self_mul_conjTranspose _)]

/-- The Yang–Mills cell density `⋆₂(p) |F_p|²_g` of `eq:finite-SM-action`. -/
noncomputable def smFaceEnergy (X : FiniteSpacetimeComplex V E F)
    (ρG : ∀ i, G →* Matrix.unitaryGroup (nG i) ℂ) (κ : ι → ℝ) (star2 : F → ℝ)
    (p : F) (U : E → G) : ℝ :=
  star2 p * curvatureNormSq ρG κ (X.plaquetteHolonomy U p)

/-- Gauge invariance of the Yang–Mills cell density. -/
theorem smFaceEnergy_gaugeLinks (X : FiniteSpacetimeComplex V E F)
    (ρG : ∀ i, G →* Matrix.unitaryGroup (nG i) ℂ) (κ : ι → ℝ) (star2 : F → ℝ)
    (g : V → G) (p : F) (U : E → G) :
    smFaceEnergy X ρG κ star2 p (gaugeLinks X.src X.tgt g U) = smFaceEnergy X ρG κ star2 p U := by
  unfold smFaceEnergy
  rw [X.plaquetteHolonomy_gaugeLinks, curvatureNormSq_conj]

/-- The covariant Higgs edge difference `(D_U H)_e = H_{t(e)} − ρ_H(U_e) H_{s(e)}`. -/
def higgsEdgeDifference (X : FiniteSpacetimeComplex V E F)
    (ρH : G →* Matrix.unitaryGroup nH ℂ) (U : E → G) (H : V → Matrix nH pH ℂ) (e : E) :
    Matrix nH pH ℂ :=
  H (X.tgt e) - (ρH (U e) : Matrix nH nH ℂ) * H (X.src e)

omit [Fintype pH] in
/-- **The Higgs edge difference transforms covariantly in the target fibre.** -/
theorem higgsEdgeDifference_gauge (X : FiniteSpacetimeComplex V E F)
    (ρH : G →* Matrix.unitaryGroup nH ℂ) (g : V → G) (U : E → G) (H : V → Matrix nH pH ℂ)
    (e : E) :
    higgsEdgeDifference X ρH (gaugeLinks X.src X.tgt g U)
        (fun v => (ρH (g v) : Matrix nH nH ℂ) * H v) e =
      (ρH (g (X.tgt e)) : Matrix nH nH ℂ) * higgsEdgeDifference X ρH U H e := by
  simp only [higgsEdgeDifference, gaugeLinks_apply, coe_rep_mul, Matrix.mul_sub,
    Matrix.mul_assoc, coe_rep_inv_mul_cancel_left]

/-- The Higgs kinetic cell density `⋆₁(e) ‖(D_U H)_e‖²` of `eq:finite-SM-action`. -/
noncomputable def smEdgeEnergy (X : FiniteSpacetimeComplex V E F)
    (ρH : G →* Matrix.unitaryGroup nH ℂ) (star1 : E → ℝ) (e : E) (U : E → G)
    (H : V → Matrix nH pH ℂ) : ℝ :=
  star1 e * frobSq (higgsEdgeDifference X ρH U H e)

/-- Gauge invariance of the Higgs kinetic cell density. -/
theorem smEdgeEnergy_gauge (X : FiniteSpacetimeComplex V E F)
    (ρH : G →* Matrix.unitaryGroup nH ℂ) (star1 : E → ℝ) (g : V → G) (e : E) (U : E → G)
    (H : V → Matrix nH pH ℂ) :
    smEdgeEnergy X ρH star1 e (gaugeLinks X.src X.tgt g U)
        (fun v => (ρH (g v) : Matrix nH nH ℂ) * H v) =
      smEdgeEnergy X ρH star1 e U H := by
  unfold smEdgeEnergy
  rw [higgsEdgeDifference_gauge,
    frobSq_mul_left_of_conjTranspose_mul _ (unitaryGroup_conjTranspose_mul_self _)]

/-- Gauge invariance of the Higgs norm `‖H_v‖²`. -/
theorem frobSq_rep_mul (ρH : G →* Matrix.unitaryGroup nH ℂ) (g : G) (H : Matrix nH pH ℂ) :
    frobSq ((ρH g : Matrix nH nH ℂ) * H) = frobSq H :=
  frobSq_mul_left_of_conjTranspose_mul _ (unitaryGroup_conjTranspose_mul_self _) _

/-- The finite covariant Dirac/Yukawa operator `(D^U_sp + Γ_Cl ⊗ D_F(H)) Ψ` at a vertex:
forward hops `ρ_Ψ(U_e) Ψ_{s(e)} γ⁺_e` into `v = t(e)`, backward hops
`ρ_Ψ(U_e⁻¹) Ψ_{t(e)} γ⁻_e` into `v = s(e)`, the on-site term `Ψ_v γ⁰_v`, and the Yukawa
term `D_F(H_v) Ψ_v Γ_Cl`. -/
noncomputable def finiteDiracYukawa [Fintype E] [DecidableEq V]
    (X : FiniteSpacetimeComplex V E F) (ρΨ : G →* Matrix.unitaryGroup nΨ ℂ)
    (DF : Matrix nH pH ℂ → Matrix nΨ nΨ ℂ) (D : SMDiracCoefficients V E q)
    (U : E → G) (H : V → Matrix nH pH ℂ) (Ψ : V → Matrix nΨ q ℂ) (v : V) : Matrix nΨ q ℂ :=
  (∑ e, if X.tgt e = v then (ρΨ (U e) : Matrix nΨ nΨ ℂ) * Ψ (X.src e) * D.γf e else 0)
    + (∑ e, if X.src e = v then (ρΨ (U e)⁻¹ : Matrix nΨ nΨ ℂ) * Ψ (X.tgt e) * D.γb e else 0)
    + Ψ v * D.γ0 v + DF (H v) * Ψ v * D.Γ

omit [Fintype pH] in
/-- **The finite Dirac/Yukawa operator intertwines the typed representations**:
`(D^{g·U} + Γ ⊗ D_F(g·H)) (g·Ψ) = ρ_Ψ(g) (D^U + Γ ⊗ D_F(H)) Ψ`. -/
theorem finiteDiracYukawa_gauge [Fintype E] [DecidableEq V]
    (X : FiniteSpacetimeComplex V E F) (ρH : G →* Matrix.unitaryGroup nH ℂ)
    (ρΨ : G →* Matrix.unitaryGroup nΨ ℂ) (DF : Matrix nH pH ℂ → Matrix nΨ nΨ ℂ)
    (D : SMDiracCoefficients V E q)
    (hDF : ∀ (g : G) (H : Matrix nH pH ℂ), DF ((ρH g : Matrix nH nH ℂ) * H) =
      (ρΨ g : Matrix nΨ nΨ ℂ) * DF H * (ρΨ g⁻¹ : Matrix nΨ nΨ ℂ))
    (g : V → G) (U : E → G) (H : V → Matrix nH pH ℂ) (Ψ : V → Matrix nΨ q ℂ) (v : V) :
    finiteDiracYukawa X ρΨ DF D (gaugeLinks X.src X.tgt g U)
        (fun w => (ρH (g w) : Matrix nH nH ℂ) * H w)
        (fun w => (ρΨ (g w) : Matrix nΨ nΨ ℂ) * Ψ w) v =
      (ρΨ (g v) : Matrix nΨ nΨ ℂ) * finiteDiracYukawa X ρΨ DF D U H Ψ v := by
  have h1 : ∀ e, (if X.tgt e = v then
      (ρΨ (gaugeLinks X.src X.tgt g U e) : Matrix nΨ nΨ ℂ) *
        ((ρΨ (g (X.src e)) : Matrix nΨ nΨ ℂ) * Ψ (X.src e)) * D.γf e else 0) =
      (ρΨ (g v) : Matrix nΨ nΨ ℂ) *
        (if X.tgt e = v then (ρΨ (U e) : Matrix nΨ nΨ ℂ) * Ψ (X.src e) * D.γf e else 0) := by
    intro e
    split_ifs with h
    · subst h
      simp only [gaugeLinks_apply, coe_rep_mul, Matrix.mul_assoc, coe_rep_inv_mul_cancel_left]
    · rw [Matrix.mul_zero]
  have h2 : ∀ e, (if X.src e = v then
      (ρΨ (gaugeLinks X.src X.tgt g U e)⁻¹ : Matrix nΨ nΨ ℂ) *
        ((ρΨ (g (X.tgt e)) : Matrix nΨ nΨ ℂ) * Ψ (X.tgt e)) * D.γb e else 0) =
      (ρΨ (g v) : Matrix nΨ nΨ ℂ) *
        (if X.src e = v then (ρΨ (U e)⁻¹ : Matrix nΨ nΨ ℂ) * Ψ (X.tgt e) * D.γb e else 0) := by
    intro e
    split_ifs with h
    · subst h
      simp only [gaugeLinks_apply, _root_.mul_inv_rev, inv_inv, coe_rep_mul, Matrix.mul_assoc,
        coe_rep_inv_mul_cancel_left]
    · rw [Matrix.mul_zero]
  unfold finiteDiracYukawa
  simp only [h1, h2, Matrix.mul_add, Matrix.mul_sum]
  rw [hDF]
  simp only [Matrix.mul_assoc, coe_rep_inv_mul_cancel_left]

/-- The Dirac/Yukawa cell density `⋆₀(v) Re tr (Ψ̄_v ((D^U_sp + Γ ⊗ D_F(H)) Ψ)_v)` of
`eq:finite-SM-action`, with the independent dual amplitude `Ψ̄_v`. -/
noncomputable def smFermionEnergy [Fintype E] [DecidableEq V]
    (X : FiniteSpacetimeComplex V E F) (ρΨ : G →* Matrix.unitaryGroup nΨ ℂ)
    (DF : Matrix nH pH ℂ → Matrix nΨ nΨ ℂ) (D : SMDiracCoefficients V E q) (star0 : V → ℝ)
    (v : V) (U : E → G) (H : V → Matrix nH pH ℂ) (Ψ : V → Matrix nΨ q ℂ)
    (Ψb : V → Matrix q nΨ ℂ) : ℝ :=
  star0 v * (Ψb v * finiteDiracYukawa X ρΨ DF D U H Ψ v).trace.re

omit [Fintype pH] in
/-- Gauge invariance of the Dirac/Yukawa cell density, the dual amplitude transforming
contragrediently `Ψ̄_v ↦ Ψ̄_v ρ_Ψ(g_v)⁻¹`. -/
theorem smFermionEnergy_gauge [Fintype E] [DecidableEq V]
    (X : FiniteSpacetimeComplex V E F) (ρH : G →* Matrix.unitaryGroup nH ℂ)
    (ρΨ : G →* Matrix.unitaryGroup nΨ ℂ) (DF : Matrix nH pH ℂ → Matrix nΨ nΨ ℂ)
    (D : SMDiracCoefficients V E q) (star0 : V → ℝ)
    (hDF : ∀ (g : G) (H : Matrix nH pH ℂ), DF ((ρH g : Matrix nH nH ℂ) * H) =
      (ρΨ g : Matrix nΨ nΨ ℂ) * DF H * (ρΨ g⁻¹ : Matrix nΨ nΨ ℂ))
    (g : V → G) (v : V) (U : E → G) (H : V → Matrix nH pH ℂ) (Ψ : V → Matrix nΨ q ℂ)
    (Ψb : V → Matrix q nΨ ℂ) :
    smFermionEnergy X ρΨ DF D star0 v (gaugeLinks X.src X.tgt g U)
        (fun w => (ρH (g w) : Matrix nH nH ℂ) * H w)
        (fun w => (ρΨ (g w) : Matrix nΨ nΨ ℂ) * Ψ w)
        (fun w => Ψb w * (ρΨ (g w)⁻¹ : Matrix nΨ nΨ ℂ)) =
      smFermionEnergy X ρΨ DF D star0 v U H Ψ Ψb := by
  unfold smFermionEnergy
  rw [finiteDiracYukawa_gauge X ρH ρΨ DF D hDF g U H Ψ v]
  simp only [Matrix.mul_assoc, coe_rep_inv_mul_cancel_left]

/-- A linear Yukawa coupling `H ↦ A H B + (A H B)ᴴ` built from intertwiners
(`ρ_Ψ(g) A = A ρ_H(g)`, `B ρ_Ψ(g)⁻¹ = B`) is equivariant. -/
theorem yukawaMap_equivariant (ρH : G →* Matrix.unitaryGroup nH ℂ)
    (ρΨ : G →* Matrix.unitaryGroup nΨ ℂ) (A : Matrix nΨ nH ℂ) (B : Matrix pH nΨ ℂ)
    (hA : ∀ g : G, (ρΨ g : Matrix nΨ nΨ ℂ) * A = A * (ρH g : Matrix nH nH ℂ))
    (hB : ∀ g : G, B * (ρΨ g⁻¹ : Matrix nΨ nΨ ℂ) = B) (g : G) (H : Matrix nH pH ℂ) :
    (fun H : Matrix nH pH ℂ => A * H * B + (A * H * B)ᴴ) ((ρH g : Matrix nH nH ℂ) * H) =
      (ρΨ g : Matrix nΨ nΨ ℂ) * (fun H : Matrix nH pH ℂ => A * H * B + (A * H * B)ᴴ) H *
        (ρΨ g⁻¹ : Matrix nΨ nΨ ℂ) := by
  have hY : ∀ H : Matrix nH pH ℂ, A * ((ρH g : Matrix nH nH ℂ) * H) * B =
      (ρΨ g : Matrix nΨ nΨ ℂ) * (A * H * B) * (ρΨ g⁻¹ : Matrix nΨ nΨ ℂ) := by
    intro H
    rw [← Matrix.mul_assoc A, ← hA]
    simp only [Matrix.mul_assoc]
    rw [hB]
  have hinv : (ρΨ g⁻¹ : Matrix nΨ nΨ ℂ) = (ρΨ g : Matrix nΨ nΨ ℂ)ᴴ := by
    have h := coe_rep_inv_mul ρΨ g
    calc (ρΨ g⁻¹ : Matrix nΨ nΨ ℂ)
        = (ρΨ g⁻¹ : Matrix nΨ nΨ ℂ) * ((ρΨ g : Matrix nΨ nΨ ℂ) * (ρΨ g : Matrix nΨ nΨ ℂ)ᴴ) := by
          rw [unitaryGroup_self_mul_conjTranspose, Matrix.mul_one]
      _ = (ρΨ g : Matrix nΨ nΨ ℂ)ᴴ := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  show A * ((ρH g : Matrix nH nH ℂ) * H) * B + (A * ((ρH g : Matrix nH nH ℂ) * H) * B)ᴴ =
    (ρΨ g : Matrix nΨ nΨ ℂ) * (A * H * B + (A * H * B)ᴴ) * (ρΨ g⁻¹ : Matrix nΨ nΨ ℂ)
  rw [hY, Matrix.mul_add, Matrix.add_mul]
  congr 1
  simp only [Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

end Densities

/-! ### The gauge transformation, the concrete action, and its exact invariance -/

section Action

variable {V : Type u} {E : Type v} {F : Type w} {G : Type*} [Group G]
  {ι : Type*} [Fintype ι] {nG : ι → Type*} [∀ i, Fintype (nG i)] [∀ i, DecidableEq (nG i)]
  {nH pH nΨ q : Type*} [Fintype nH] [DecidableEq nH] [Fintype pH]
  [Fintype nΨ] [DecidableEq nΨ] [Fintype q]

/-- The local gauge transformation `U_e ↦ g_{t(e)} U_e g_{s(e)}⁻¹`, `H_v ↦ ρ_H(g_v) H_v`,
`Ψ_v ↦ ρ_Ψ(g_v) Ψ_v`, `Ψ̄_v ↦ Ψ̄_v ρ_Ψ(g_v)⁻¹` of a configuration. -/
def smGaugeTransform (X : FiniteSpacetimeComplex V E F) (ρH : G →* Matrix.unitaryGroup nH ℂ)
    (ρΨ : G →* Matrix.unitaryGroup nΨ ℂ) (g : V → G)
    (Φ : RegulatedSMConfiguration V E G (Matrix nH pH ℂ) (Matrix nΨ q ℂ) (Matrix q nΨ ℂ)) :
    RegulatedSMConfiguration V E G (Matrix nH pH ℂ) (Matrix nΨ q ℂ) (Matrix q nΨ ℂ) where
  gaugeLink := gaugeLinks X.src X.tgt g Φ.gaugeLink
  higgs := fun v => (ρH (g v) : Matrix nH nH ℂ) * Φ.higgs v
  spinor := fun v => (ρΨ (g v) : Matrix nΨ nΨ ℂ) * Φ.spinor v
  dualSpinor := fun v => Φ.dualSpinor v * (ρΨ (g v)⁻¹ : Matrix nΨ nΨ ℂ)

omit [Fintype pH] [Fintype q] in
/-- The gauge transformations form a group action. -/
theorem smGaugeTransform_mul (X : FiniteSpacetimeComplex V E F)
    (ρH : G →* Matrix.unitaryGroup nH ℂ) (ρΨ : G →* Matrix.unitaryGroup nΨ ℂ) (g h : V → G)
    (Φ : RegulatedSMConfiguration V E G (Matrix nH pH ℂ) (Matrix nΨ q ℂ) (Matrix q nΨ ℂ)) :
    smGaugeTransform X ρH ρΨ (g * h) Φ =
      smGaugeTransform X ρH ρΨ g (smGaugeTransform X ρH ρΨ h Φ) := by
  simp only [smGaugeTransform, gaugeLinks_mul, Pi.mul_apply, _root_.mul_inv_rev, coe_rep_mul,
    Matrix.mul_assoc]

/-- **The concrete finite Standard-Model action `eq:finite-SM-action`**: the four-term
`explicitRegulatedStandardModelAction` with the Yang–Mills density
`⋆₂(p) |log P_p|²_g`, the Higgs kinetic density `⋆₁(e) ‖(D_U H)_e‖²`, the Higgs potential
`m_v λ_H (‖H_v‖² − v_H²)²`, and the Dirac/Yukawa density
`⋆₀(v) Re tr (Ψ̄_v ((D^U_sp + Γ ⊗ D_F(H)) Ψ)_v)`. -/
noncomputable def finiteStandardModelAction [Fintype V] [Fintype E] [Fintype F] [DecidableEq V]
    (X : FiniteSpacetimeComplex V E F) (R : SMGaugeRepresentations G nG nH pH nΨ)
    (D : SMDiracCoefficients V E q) (C : SMActionCoefficients V E F ι)
    (Φ : RegulatedSMConfiguration V E G (Matrix nH pH ℂ) (Matrix nΨ q ℂ) (Matrix q nΨ ℂ)) :
    ℝ :=
  explicitRegulatedStandardModelAction (smFaceEnergy X R.ρG C.gaugeCoeff C.star2)
    (smEdgeEnergy X R.ρH C.star1) C.mass frobSq C.lambdaH (C.vH ^ 2)
    (smFermionEnergy X R.ρΨ R.DF D C.star0) Φ

/-- **Exact gauge invariance of the concrete action `eq:finite-SM-action`**
(first clause of `thm:finite-action-identities`): the four covariance hypotheses of
`explicitRegulatedStandardModelAction_gaugeInvariant` are discharged by
`smFaceEnergy_gaugeLinks`, `smEdgeEnergy_gauge`, `frobSq_rep_mul`, `smFermionEnergy_gauge`. -/
theorem finiteStandardModelAction_gaugeInvariant [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] (X : FiniteSpacetimeComplex V E F)
    (R : SMGaugeRepresentations G nG nH pH nΨ) (D : SMDiracCoefficients V E q)
    (C : SMActionCoefficients V E F ι) (hDF : R.YukawaEquivariant) :
    ∀ (g : V → G)
      (Φ : RegulatedSMConfiguration V E G (Matrix nH pH ℂ) (Matrix nΨ q ℂ) (Matrix q nΨ ℂ)),
      finiteStandardModelAction X R D C (smGaugeTransform X R.ρH R.ρΨ g Φ) =
        finiteStandardModelAction X R D C Φ :=
  explicitRegulatedStandardModelAction_gaugeInvariant (V → G) (smGaugeTransform X R.ρH R.ρΨ)
    (smFaceEnergy X R.ρG C.gaugeCoeff C.star2) (smEdgeEnergy X R.ρH C.star1) C.mass frobSq
    C.lambdaH (C.vH ^ 2) (smFermionEnergy X R.ρΨ R.DF D C.star0)
    (fun g p Φ => smFaceEnergy_gaugeLinks X R.ρG C.gaugeCoeff C.star2 g p Φ.gaugeLink)
    (fun g e Φ => smEdgeEnergy_gauge X R.ρH C.star1 g e Φ.gaugeLink Φ.higgs)
    (fun g v Φ => frobSq_rep_mul R.ρH (g v) (Φ.higgs v))
    (fun g v Φ => smFermionEnergy_gauge X R.ρH R.ρΨ R.DF D C.star0 hDF g v Φ.gaugeLink
      Φ.higgs Φ.spinor Φ.dualSpinor)

/-- **Finite Ward, BRST, and stress identities (`thm:finite-action-identities`)** for the
concrete action `eq:finite-SM-action`.

(i) One-cell locality (cutoff-independent support radius): the action is the sum of the
plaquette, edge and vertex densities.
(ii) Exact gauge invariance.
(iii) The finite Ward identity `eq:ward` in its differentiated form: the derivative of the
action along every gauge flow `t ↦ g(t)` vanishes (its divergence/pairing form
`d_U^* E_U + ℛ_H^* E_H + ℛ_Ψ^* E_Ψ + ℛ_Ψ̄^* E_Ψ̄ = 0` is the chain-rule theorem
`FiniteActionWardBRSTStressEinstein.gauge_ward_divergence`).
(iv) The finite group-cochain BRST closure and nilpotency of the action.
(v) The ghost BRST clause `eq:brst`: for the standard ghost extension `s c = −c²`,
`s U = c_t U − U c_s`, `s H = c H`, `s Ψ = c Ψ`, `s c̄ = B`, `s B = 0` on the same lattice,
`s² = 0` on the field–ghost algebra and `s 𝒮 = 0` for every infinitesimally gauge-invariant
element of the field algebra (`finite_action_brst`).
The stress identity `eq:stress-identity` is the chain-rule theorem
`FiniteActionWardBRSTStressEinstein.relabeling_stress_transfer`; the matter stress tensor
defined by Hodge-weight variation is the cell-density covector of clause (i). -/
theorem finite_action_identities [Fintype V] [Fintype E] [Fintype F] [DecidableEq V]
    (X : FiniteSpacetimeComplex V E F) (R : SMGaugeRepresentations G nG nH pH nΨ)
    (D : SMDiracCoefficients V E q) (C : SMActionCoefficients V E F ι)
    (hDF : R.YukawaEquivariant) :
    (∀ Φ : RegulatedSMConfiguration V E G (Matrix nH pH ℂ) (Matrix nΨ q ℂ) (Matrix q nΨ ℂ),
      finiteStandardModelAction X R D C Φ =
        (2 : ℝ)⁻¹ * ∑ p, C.star2 p *
            curvatureNormSq R.ρG C.gaugeCoeff (X.plaquetteHolonomy Φ.gaugeLink p)
        + (2 : ℝ)⁻¹ * ∑ e, C.star1 e *
            frobSq (higgsEdgeDifference X R.ρH Φ.gaugeLink Φ.higgs e)
        + ∑ v, C.mass v * C.lambdaH * (frobSq (Φ.higgs v) - C.vH ^ 2) ^ 2
        + ∑ v, C.star0 v * (Φ.dualSpinor v *
            finiteDiracYukawa X R.ρΨ R.DF D Φ.gaugeLink Φ.higgs Φ.spinor v).trace.re)
    ∧ (∀ (g : V → G)
        (Φ : RegulatedSMConfiguration V E G (Matrix nH pH ℂ) (Matrix nΨ q ℂ) (Matrix q nΨ ℂ)),
        finiteStandardModelAction X R D C (smGaugeTransform X R.ρH R.ρΨ g Φ) =
          finiteStandardModelAction X R D C Φ)
    ∧ (∀ (γ : ℝ → V → G)
        (Φ : RegulatedSMConfiguration V E G (Matrix nH pH ℂ) (Matrix nΨ q ℂ) (Matrix q nΨ ℂ))
        (t₀ : ℝ),
        HasDerivAt (fun t => finiteStandardModelAction X R D C
          (smGaugeTransform X R.ρH R.ρΨ (γ t) Φ)) 0 t₀)
    ∧ finiteBRST0 (smGaugeTransform X R.ρH R.ρΨ) (finiteStandardModelAction X R D C) = 0
    ∧ finiteBRST1 (smGaugeTransform X R.ρH R.ρΨ)
        (finiteBRST0 (smGaugeTransform X R.ρH R.ρΨ) (finiteStandardModelAction X R D C)) = 0
    ∧ (∀ {A : Type uA} [Ring A] [Algebra ℂ A] {P : ParityStructure A}
        (s : SuperDerivation P) {n : Type un} {p : Type up} {q' : Type uq}
        [Fintype n] [DecidableEq n]
        (c : V → Matrix n n A) (U : E → Matrix n n A) (H : V → Matrix n p A)
        (Ψ : V → Matrix n q' A) (Ψb : V → Matrix q' n A) (cb B : V → Matrix n n A)
        (_ : FiniteGhostBRST s X.src X.tgt c U H Ψ Ψb cb B) {d : ℕ}
        (T : Fin d → Matrix n n ℂ) (cs : V → Fin d → A)
        (_ : ∀ v, c v = ∑ a, cs v a • FiniteGhostBRST.liftGen (A := A) T a)
        (δ : V × Fin d → A →ₗ[ℂ] A)
        (_ : ∀ p x y, δ p (x * y) = x * δ p y + δ p x * y)
        (_ : ∀ v a e i j, δ (v, a) (U e i j) =
          (if v = X.tgt e then (FiniteGhostBRST.liftGen (A := A) T a * U e) i j else 0)
            - (if v = X.src e then (U e * FiniteGhostBRST.liftGen (A := A) T a) i j else 0))
        (_ : ∀ v a w i j, δ (v, a) (H w i j) =
          if v = w then (FiniteGhostBRST.liftGen (A := A) T a * H w) i j else 0)
        (_ : ∀ v a w i j, δ (v, a) (Ψ w i j) =
          if v = w then (FiniteGhostBRST.liftGen (A := A) T a * Ψ w) i j else 0)
        (_ : ∀ v a w i j, δ (v, a) (Ψb w i j) =
          if v = w then -(Ψb w * FiniteGhostBRST.liftGen (A := A) T a) i j else 0)
        (_ : ∀ x ∈ FiniteGhostBRST.fieldGenerators U H Ψ Ψb, ∀ v a,
          x * cs v a = cs v a * x),
        (∀ x ∈ Algebra.adjoin ℂ (FiniteGhostBRST.fieldGhostGenerators c U H Ψ Ψb cb B),
            s (s x) = 0)
        ∧ ∀ S ∈ Algebra.adjoin ℂ (FiniteGhostBRST.fieldGenerators U H Ψ Ψb),
            (∀ p, δ p S = 0) → s S = 0) := by
  have hinv := finiteStandardModelAction_gaugeInvariant X R D C hDF
  have hbrst := finiteGaugeAction_BRST (smGaugeTransform X R.ρH R.ρΨ)
    (smGaugeTransform_mul X R.ρH R.ρΨ) (finiteStandardModelAction X R D C) hinv
  refine ⟨fun Φ => rfl, hinv, ?_, hbrst.1, hbrst.2, ?_⟩
  · intro γ Φ t₀
    have hconst : (fun t => finiteStandardModelAction X R D C
        (smGaugeTransform X R.ρH R.ρΨ (γ t) Φ)) =
        fun _ => finiteStandardModelAction X R D C Φ :=
      funext fun t => hinv (γ t) Φ
    rw [hconst]
    exact hasDerivAt_const _ _
  · intro A _ _ P s n p q' _ _ c U H Ψ Ψb cb B R' d T cs hc δ hδ hδU hδH hδΨ hδΨb hcomm
    exact finite_action_brst s X.src X.tgt c U H Ψ Ψb cb B R' T cs hc δ hδ hδU hδH hδΨ hδΨb
      hcomm

end Action

end RenewalGeometry
