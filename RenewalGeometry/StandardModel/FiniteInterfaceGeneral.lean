/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.FiniteInterfaceRepresentationTable

/-!
# The finite Einstein–Standard-Model interface on an admissible chart, with a spinor fibre
  (`def:finite-interface`; Einstein–Standard-Model action-closure manuscript)

This file gives a second, more literal encoding of `def:finite-interface`.  The earlier encoding
`TabulatedFiniteInterface` (`FiniteInterfaceRepresentationTable.lean`) is kept unchanged (the
regulator sequence `RegulatorSequence` is built on it), but it has two features that no instance
built from the paper's own native local action can satisfy:

* its fermion carrier is `Site → Fin 3 → OneGeneration` with `OneGeneration ≃ ℂ^{table rows}`
  (`tableEquiv`), so there is **no spacetime-spinor index**, and the incidence operator of (I3)
  cannot be the Clifford/spin-link operator of the native Dirac density;
* its common action must be differentiable on the whole configuration vector space and gauge
  invariant for every configuration, whereas the paper's local action `S_h^{loc}` takes logarithms
  of plaquettes "on the declared admissible chart" (`subsec:local-action-conventions`) and is
  defined, differentiable and gauge invariant only there.

## The new encoding

`FiniteInterfaceChart h` (the structural record) and its refinement `SpinorFiniteInterface h`
(the record with the spinor/Clifford incidence of (I3)) encode the items of
`def:finite-interface` clause by clause:

* **(I1)** "A finite configuration space `𝒬_h` with a reconstructed oriented, time-oriented
  Lorentzian carrier and local coframe variables": a finite site set `Site`, a finite-dimensional
  real normed space `Config = 𝒬_h`, an **open nonempty admissible chart** `chart ⊆ 𝒬_h`, and local
  coframes `coframe q x ∈ M₄(ℝ)` which on the chart are oriented (`det e > 0`) and time-oriented
  (`e⁰₀ > 0`); the reconstructed metric `eᵀηe` is then Lorentzian (`metric_det_neg`).
  `SpinorFiniteInterface` adds the oriented incidence `next μ : Site ≃ Site` (the edge
  `x → x + e_μ` of the carrier) on which the finite Dirac incidence lives.
* **(I2)** "A fixed finite-rank Standard-Model bundle type with `G_SM = S(U(3)×U(2))`, the chiral
  fermion representations of `tab:SM-representations`, one rank-three generation factor, the Higgs
  doublet, and any optional neutral/Majorana blocks declared as part of the branch": the gauge
  group is `SMGaugeGroup` (with its `ℤ₆` presentation `gaugeGroupPresentation`); the declared
  branch `branch : NeutrinoBranch`; the fermion fibre is **`ℂ^{SpinIdx} ⊗ ℂ³_gen ⊗ ℂ^{TableRow}`**
  (index `FermionIdx SpinIdx branch = SpinIdx × (Fin 3 × TableRow branch)`), on which `G_SM` acts
  by `fibreRep = 1_spin ⊗ 1_gen ⊗ tableRep` (the rows `Q_L, L_L, u_R, d_R, e_R (, ν_R)` of the
  table); the Higgs doublet `higgs q x ∈ ℂ²` with the weak action `higgsRep`; the neutral rows of
  the branch `neutralRows branch`.  The spacetime chirality column is the chirality grading
  `γ₅ ⊗ 1 ⊗ tableChirality` (`chiralGrading`), whose `-1` eigenspace (`IsChiral`) is the chiral
  carrier (left spinors on the left rows, right spinors on the right rows).
* **(I3)** "A gauge-covariant finite Dirac/Yukawa incidence operator `D_{F,h}` on that fixed
  structural carrier and a coefficient bank `θ_h`": `dirac q`, a `ℂ`-linear operator on fermion
  fields `Site → FermionIdx → ℂ`, gauge covariant (`dirac_covariant`), and the bank
  `coefficients : CoefficientBank`.  In `SpinorFiniteInterface` the spinor fibre is a Clifford
  module (`gamma_clifford : γ^aγ^b + γ^bγ^a = 2η^{ab}`, chirality `γ₅` with `γ₅² = 1`,
  `γ₅γ^a = -γ^aγ₅`), and the operator **is** the finite Dirac incidence operator of the native
  Dirac density (`eq:native-spin-differences`, `eq:native-densities`):
  `D_q Ψ(x) = Σ_μ i γ^μ(e(x)) ∇^h_μ Ψ(x) - 𝓜_𝐘(H(x)) Ψ(x)`, with
  `γ^μ(e) = (e⁻¹)^μ_a γ^a ⊗ 1`, `∇^h_μ Ψ(x) = h⁻¹(V_μ(x) Ψ(x + e_μ) - Ψ(x))` for spin–gauge links
  `V_μ(x)` that transform as `V ↦ ρ(γ_x) V ρ(γ_{x+e_μ})⁻¹`, and the Yukawa block `1_spin ⊗ 𝓜_𝐘(H)`
  with `𝓜_𝐘` real-affine in the Higgs field and covariant as in `lem:SM-descent`
  (`dirac_eq`, `incidenceOp`; covariance of the operator is then a theorem,
  `incidenceOp_covariant`).
* **(I4)** "A differentiable common finite action `S_h = S_{g,h} + S_{SM,h}` with one physical
  relative normalization between gravity and matter and with the corresponding finite gauge
  covariance on the declared branch": `gravityAction`, `matterAction`, `relativeNormalization > 0`;
  site gauges `γ : Site → G_SM` act on `𝒬_h` (`gaugeAct`; in `SpinorFiniteInterface` a group
  action that leaves the coframe untouched); the chart is **gauge invariant**
  (`chart_gaugeAct`), the common action is **differentiable on the chart**
  (`action_differentiableOn`) and **exactly invariant on the chart** (`action_gauge_invariant`).
  The action is not required to be defined, differentiable or invariant off the chart.
* **(I5)** "A positive source geometry … equivalent positive Gram on the retained variation
  directions": a symmetric positive semidefinite bilinear Gram form on `𝒬_h`, positive definite on
  the retained directions.

No reconstruction map, compactness, stationarity or field equation is part of the record.
Disclosed (unchanged from the earlier encoding): relabeling covariance and the smooth comparison
cylinder of (I1) are not encoded; a Majorana block is antilinear and is not a block of the
`ℂ`-linear incidence operator (the neutral extension enters through its rows).

## Nothing is lost

`TabulatedFiniteInterface.toChart` embeds every interface of the earlier encoding into
`FiniteInterfaceChart` in the spinor-trivial case (`SpinIdx = Unit`, chart = the whole space,
Gram `⟨gram u, v⟩`), and `toChart_dirac` shows that the incidence operator is the old one
conjugated by the linear equivalence `fermionEquiv` of the two carriers.  A concrete
`SpinorFiniteInterface` built from the paper's native local action is
`RenewalNativeInterface.renewalSpinorInterface` (`RenewalInterfaceGeneral.lean`).
-/

open Matrix
open scoped Kronecker

namespace RenewalGeometry

open FiniteInterfaceTable

namespace FiniteInterfaceGeneral

/-! ### The fermion fibre `ℂ^{spin} ⊗ ℂ³_gen ⊗ ℂ^{table rows}` -/

/-- The generation × table-row index `ℂ³_gen ⊗ ℂ^{TableRow b}`. -/
abbrev InternalIdx (b : NeutrinoBranch) : Type := Fin 3 × TableRow b

/-- The fermion fibre index `spin × generation × table row`. -/
abbrev FermionIdx (S : Type) (b : NeutrinoBranch) : Type := S × InternalIdx b

/-- Fermion fields on a finite site set. -/
abbrev FermionField (Site S : Type) (b : NeutrinoBranch) : Type := Site → FermionIdx S b → ℂ

variable {S : Type} [Fintype S] [DecidableEq S] {b : NeutrinoBranch}

/-- An internal operator `1_spin ⊗ M` on the fermion fibre. -/
def internalOp (S : Type) [Fintype S] [DecidableEq S]
    (M : Matrix (InternalIdx b) (InternalIdx b) ℂ) :
    Matrix (FermionIdx S b) (FermionIdx S b) ℂ :=
  (1 : Matrix S S ℂ) ⊗ₖ M

/-- A spinor operator `A ⊗ 1_gen ⊗ 1_row` on the fermion fibre. -/
def spinOp (b : NeutrinoBranch) (A : Matrix S S ℂ) : Matrix (FermionIdx S b) (FermionIdx S b) ℂ :=
  A ⊗ₖ (1 : Matrix (InternalIdx b) (InternalIdx b) ℂ)

theorem internalOp_mul (M N : Matrix (InternalIdx b) (InternalIdx b) ℂ) :
    internalOp S M * internalOp S N = internalOp S (M * N) := by
  simp only [internalOp, ← mul_kronecker_mul, Matrix.one_mul]

theorem internalOp_one : internalOp S (1 : Matrix (InternalIdx b) (InternalIdx b) ℂ) = 1 := by
  simp [internalOp, one_kronecker_one]

theorem spinOp_mul (A B : Matrix S S ℂ) :
    spinOp b A * spinOp b B = spinOp b (A * B) := by
  simp only [spinOp, ← mul_kronecker_mul, Matrix.one_mul]

/-- Spinor and internal operators commute (they act on different tensor factors). -/
theorem spinOp_mul_internalOp (A : Matrix S S ℂ) (M : Matrix (InternalIdx b) (InternalIdx b) ℂ) :
    spinOp b A * internalOp S M = internalOp S M * spinOp b A := by
  simp only [spinOp, internalOp, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- `G_SM` on generation × table rows: `1_gen ⊗ tableRep`. -/
noncomputable def internalRep (b : NeutrinoBranch) :
    SMGaugeGroup →* Matrix (InternalIdx b) (InternalIdx b) ℂ where
  toFun y := (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ tableRep b y
  map_one' := by simp [one_kronecker_one]
  map_mul' y y' := by simp only [map_mul, ← mul_kronecker_mul, Matrix.one_mul]

/-- **`G_SM` on the fermion fibre**: `1_spin ⊗ 1_gen ⊗ tableRep` (`tab:SM-representations`). -/
noncomputable def fibreRep (S : Type) [Fintype S] [DecidableEq S] (b : NeutrinoBranch) :
    SMGaugeGroup →* Matrix (FermionIdx S b) (FermionIdx S b) ℂ where
  toFun y := internalOp S (internalRep b y)
  map_one' := by rw [map_one, internalOp_one]
  map_mul' y y' := by rw [map_mul, internalOp_mul]

theorem fibreRep_apply (y : SMGaugeGroup) :
    fibreRep S b y = internalOp S (internalRep b y) := rfl

theorem fibreRep_inv_mul (y : SMGaugeGroup) : fibreRep S b y⁻¹ * fibreRep S b y = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem fibreRep_mul_inv (y : SMGaugeGroup) : fibreRep S b y * fibreRep S b y⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

/-- The fibre representation acts row-wise by the table representation:
`(ρ(y) v)(s, g, r) = (tableRep(y) v(s, g, ·))(r)`. -/
theorem fibreRep_mulVec_apply (y : SMGaugeGroup) (v : FermionIdx S b → ℂ) (s : S) (g : Fin 3)
    (r : TableRow b) :
    (fibreRep S b y *ᵥ v) (s, g, r) = (tableRep b y *ᵥ fun r' => v (s, g, r')) r := by
  simp only [fibreRep_apply, internalOp, internalRep, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, kronecker_apply, Matrix.one_apply, ite_mul,
    one_mul, zero_mul]
  simp [Finset.sum_ite_irrel, Finset.sum_ite_eq]

/-! ### The finite Dirac incidence operator -/

/-- The Minkowski matrix as a complex number entry. -/
noncomputable def etaC (a c : Fin 4) : ℂ := (minkowskiEta a c : ℂ)

/-- `γ^μ(e) = Σ_a (e⁻¹)^μ_a γ^a` (frame-to-coordinate gamma matrices, `eq:native-densities`). -/
noncomputable def gammaMu (γ : Fin 4 → Matrix S S ℂ) (e : Matrix (Fin 4) (Fin 4) ℝ) (μ : Fin 4) :
    Matrix S S ℂ :=
  ∑ a, ((e⁻¹ μ a : ℝ) : ℂ) • γ a

variable {Site : Type}

/-- The kinetic coefficient `i h⁻¹ γ^μ(e) ⊗ 1` of the incidence operator. -/
noncomputable def kinCoeff (h : ℝ) (γ : Fin 4 → Matrix S S ℂ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (μ : Fin 4) : Matrix (FermionIdx S b) (FermionIdx S b) ℂ :=
  (Complex.I * (h : ℂ)⁻¹) • spinOp b (gammaMu γ e μ)

/-- **The finite Dirac/Yukawa incidence operator** at cutoff `h`
(`eq:native-spin-differences`, `eq:native-densities`):
`D Ψ(x) = Σ_μ i γ^μ(e(x)) h⁻¹(V_μ(x) Ψ(x + e_μ) - Ψ(x)) - (1_spin ⊗ 𝓜(x)) Ψ(x)`, with `x + e_μ`
the oriented incidence `next μ x`, `V_μ(x)` the spin–gauge link and `𝓜(x)` the Yukawa block. -/
noncomputable def incidenceOp (h : ℝ) (next : Fin 4 → Site ≃ Site) (γ : Fin 4 → Matrix S S ℂ)
    (e : Site → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Site → Fin 4 → Matrix (FermionIdx S b) (FermionIdx S b) ℂ)
    (M : Site → Matrix (InternalIdx b) (InternalIdx b) ℂ) :
    FermionField Site S b →ₗ[ℂ] FermionField Site S b where
  toFun ψ x := (∑ μ, kinCoeff h γ (e x) μ *ᵥ (V x μ *ᵥ ψ (next μ x) - ψ x)) -
    internalOp S (M x) *ᵥ ψ x
  map_add' ψ ψ' := by
    funext x
    simp only [Pi.add_apply, Matrix.mulVec_add, add_sub_add_comm, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext x
    simp only [Pi.smul_apply, Matrix.mulVec_smul, ← smul_sub, ← Finset.smul_sum, RingHom.id_apply]

theorem incidenceOp_apply (h : ℝ) (next : Fin 4 → Site ≃ Site) (γ : Fin 4 → Matrix S S ℂ)
    (e : Site → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Site → Fin 4 → Matrix (FermionIdx S b) (FermionIdx S b) ℂ)
    (M : Site → Matrix (InternalIdx b) (InternalIdx b) ℂ) (ψ : FermionField Site S b) (x : Site) :
    incidenceOp h next γ e V M ψ x = (∑ μ, kinCoeff h γ (e x) μ *ᵥ (V x μ *ᵥ ψ (next μ x) - ψ x)) -
      internalOp S (M x) *ᵥ ψ x := rfl

/-- **Gauge covariance of the incidence operator**: if the spin–gauge links transform as
`V ↦ ρ(γ_x) V ρ(γ_{x+e_μ})⁻¹`, the Yukawa blocks as `𝓜 ↦ ρ_int(γ_x) 𝓜 ρ_int(γ_x)⁻¹` and the
coframe is untouched, then `D'(ρ(γ) Ψ)(x) = ρ(γ_x) D Ψ(x)`. -/
theorem incidenceOp_covariant (h : ℝ) (next : Fin 4 → Site ≃ Site) (γ : Fin 4 → Matrix S S ℂ)
    (e : Site → Matrix (Fin 4) (Fin 4) ℝ)
    (V V' : Site → Fin 4 → Matrix (FermionIdx S b) (FermionIdx S b) ℂ)
    (M M' : Site → Matrix (InternalIdx b) (InternalIdx b) ℂ) (g : Site → SMGaugeGroup)
    (hV : ∀ x μ, V' x μ = fibreRep S b (g x) * V x μ * fibreRep S b (g (next μ x))⁻¹)
    (hM : ∀ x, M' x = internalRep b (g x) * M x * internalRep b (g x)⁻¹)
    (ψ : FermionField Site S b) (x : Site) :
    incidenceOp h next γ e V' M' (fun y => fibreRep S b (g y) *ᵥ ψ y) x =
      fibreRep S b (g x) *ᵥ incidenceOp h next γ e V M ψ x := by
  have hc : ∀ μ, kinCoeff h γ (e x) μ * fibreRep S b (g x) =
      fibreRep S b (g x) * kinCoeff (b := b) h γ (e x) μ := fun μ => by
    rw [kinCoeff, Matrix.smul_mul, Matrix.mul_smul, fibreRep_apply, spinOp_mul_internalOp]
  have hM' : internalOp S (M' x) * fibreRep S b (g x) =
      fibreRep S b (g x) * internalOp S (M x) := by
    rw [hM, fibreRep_apply]
    simp only [internalOp_mul]
    rw [Matrix.mul_assoc _ _ (internalRep b (g x)), ← map_mul, inv_mul_cancel, map_one,
      Matrix.mul_one]
  have hterm : ∀ μ, kinCoeff h γ (e x) μ *ᵥ (V' x μ *ᵥ (fibreRep S b (g (next μ x)) *ᵥ
      ψ (next μ x)) - fibreRep S b (g x) *ᵥ ψ x) =
      fibreRep S b (g x) *ᵥ (kinCoeff h γ (e x) μ *ᵥ (V x μ *ᵥ ψ (next μ x) - ψ x)) := by
    intro μ
    rw [hV, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, fibreRep_inv_mul,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, Matrix.mulVec_mulVec, hc,
      ← Matrix.mulVec_mulVec]
  have hB : internalOp S (M' x) *ᵥ (fibreRep S b (g x) *ᵥ ψ x) =
      fibreRep S b (g x) *ᵥ (internalOp S (M x) *ᵥ ψ x) := by
    rw [Matrix.mulVec_mulVec, hM', ← Matrix.mulVec_mulVec]
  rw [incidenceOp_apply, incidenceOp_apply, Finset.sum_congr rfl (fun μ _ => hterm μ), hB,
    ← Matrix.mulVec_sum, ← Matrix.mulVec_sub]

end FiniteInterfaceGeneral

open FiniteInterfaceGeneral

/-! ### The structural record on an admissible chart -/

/-- **`def:finite-interface` on an admissible chart** (structural record).  A finite classical
Einstein–Standard-Model interface at cutoff `h`: (I1) a finite carrier and configuration space with
an open nonempty admissible chart on which the local coframes are oriented and time-oriented;
(I2) the declared branch of `tab:SM-representations`, the Higgs doublet; (I3) the spinor index of
the fermion fibre `ℂ^{spin} ⊗ ℂ³_gen ⊗ ℂ^{table}`, a gauge-covariant `ℂ`-linear incidence operator
on fermion fields and the coefficient bank; (I4) a common action differentiable on the chart and
exactly invariant there under site gauges, which preserve the chart; (I5) a positive Gram form. -/
structure FiniteInterfaceChart (h : ℝ) where
  /-- (I1) the finite site set of the carrier -/
  Site : Type
  [siteFintype : Fintype Site]
  /-- (I1) the finite configuration space `𝒬_h` -/
  Config : Type
  [configGroup : NormedAddCommGroup Config]
  [configSpace : NormedSpace ℝ Config]
  [configFinite : FiniteDimensional ℝ Config]
  /-- (I1)/(I4) the admissible chart of `𝒬_h` -/
  chart : Set Config
  chart_isOpen : IsOpen chart
  chart_nonempty : chart.Nonempty
  /-- (I1) local coframe variables `e^a_μ(x)` -/
  coframe : Config → Site → Matrix (Fin 4) (Fin 4) ℝ
  /-- (I1) oriented on the chart -/
  coframe_oriented : ∀ q ∈ chart, ∀ x, 0 < (coframe q x).det
  /-- (I1) time-oriented on the chart -/
  coframe_timeOriented : ∀ q ∈ chart, ∀ x, 0 < coframe q x 0 0
  /-- (I2) the declared branch (minimal packet or neutrino extension) -/
  branch : NeutrinoBranch
  /-- (I2) the Higgs doublet -/
  higgs : Config → Site → (Fin 2 → ℂ)
  /-- (I3) the spinor index of the fermion fibre -/
  SpinIdx : Type
  [spinFintype : Fintype SpinIdx]
  [spinDecEq : DecidableEq SpinIdx]
  /-- (I3) the declared Yukawa sectors -/
  YukawaSector : Type
  [yukawaSectorFintype : Fintype YukawaSector]
  /-- (I3) the coefficient bank `θ_h` -/
  coefficients : CoefficientBank YukawaSector
  /-- (I3) the finite Dirac/Yukawa incidence operator on fermion fields -/
  dirac : Config → (FermionField Site SpinIdx branch →ₗ[ℂ] FermionField Site SpinIdx branch)
  /-- (I4) site gauges `Site → G_SM` acting on `𝒬_h` -/
  gaugeAct : (Site → SMGaugeGroup) → Config → Config
  /-- (I2) the Higgs reader is gauge covariant -/
  higgs_covariant : ∀ γ q x, higgs (gaugeAct γ q) x = higgsRep (γ x) (higgs q x)
  /-- (I3) the incidence operator is gauge covariant -/
  dirac_covariant : ∀ γ q (ψ : FermionField Site SpinIdx branch) x,
    dirac (gaugeAct γ q) (fun y => fibreRep SpinIdx branch (γ y) *ᵥ ψ y) x =
      fibreRep SpinIdx branch (γ x) *ᵥ dirac q ψ x
  /-- (I4) the gravitational finite action `S_{g,h}` -/
  gravityAction : Config → ℝ
  /-- (I4) the Standard-Model finite action `S_{SM,h}` -/
  matterAction : Config → ℝ
  /-- (I4) the physical relative normalization -/
  relativeNormalization : ℝ
  relativeNormalization_pos : 0 < relativeNormalization
  /-- (I4) the admissible chart is gauge invariant -/
  chart_gaugeAct : ∀ γ, ∀ q ∈ chart, gaugeAct γ q ∈ chart
  /-- (I4) the common action is differentiable on the chart -/
  action_differentiableOn :
    DifferentiableOn ℝ (fun q => gravityAction q + relativeNormalization * matterAction q) chart
  /-- (I4) exact finite gauge invariance on the chart -/
  action_gauge_invariant : ∀ γ, ∀ q ∈ chart,
    gravityAction (gaugeAct γ q) + relativeNormalization * matterAction (gaugeAct γ q) =
      gravityAction q + relativeNormalization * matterAction q
  /-- (I5) the retained variation directions -/
  retained : Submodule ℝ Config
  /-- (I5) the source Gram form -/
  gram : LinearMap.BilinForm ℝ Config
  gram_symm : ∀ u v, gram u v = gram v u
  gram_nonneg : ∀ v, 0 ≤ gram v v
  /-- (I5) positivity on the retained variation directions -/
  gram_pos_retained : ∀ v ∈ retained, v ≠ 0 → 0 < gram v v

namespace FiniteInterfaceChart

variable {h : ℝ} (I : FiniteInterfaceChart h)

attribute [instance] siteFintype configGroup configSpace configFinite spinFintype spinDecEq
  yukawaSectorFintype

/-- (I4) The common finite action `S_h = S_{g,h} + ν S_{SM,h}`. -/
def action (q : I.Config) : ℝ := I.gravityAction q + I.relativeNormalization * I.matterAction q

theorem action_differentiableOn' : DifferentiableOn ℝ I.action I.chart :=
  I.action_differentiableOn

theorem action_gaugeAct (γ : I.Site → SMGaugeGroup) {q : I.Config} (hq : q ∈ I.chart) :
    I.action (I.gaugeAct γ q) = I.action q := I.action_gauge_invariant γ q hq

/-- (I1) The reconstructed metric `eᵀηe`. -/
def metric (q : I.Config) (x : I.Site) : Matrix (Fin 4) (Fin 4) ℝ := coframeMetric (I.coframe q x)

/-- (I1) On the chart the reconstructed metric is Lorentzian: `det g = -(det e)² < 0`. -/
theorem metric_det_neg {q : I.Config} (hq : q ∈ I.chart) (x : I.Site) :
    (I.metric q x).det < 0 := by
  unfold metric coframeMetric
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hη : minkowskiEta.det = -1 := by
    unfold minkowskiEta
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_four]
  rw [hη]
  have := I.coframe_oriented q hq x
  nlinarith

/-- (I2) The neutral blocks declared on the branch (the neutral rows of the table). -/
def NeutralBlock : Type := neutralRows I.branch

/-- (I2) The gauge group is `S(U(3)×U(2)) ≅ (SU(3)×SU(2)×U(1))/ℤ₆` (`eq:gauge-group`). -/
noncomputable def gaugeGroupPresentation : SMGaugeCover ⧸ smGaugeHom.ker ≃* SMGaugeGroup :=
  smGaugeQuotientEquiv

/-- (I2) The fermion fibre has complex dimension `|spin| · 3 · |rows|`. -/
theorem card_fermionIdx :
    Fintype.card (FermionIdx I.SpinIdx I.branch) =
      Fintype.card I.SpinIdx * (3 * Fintype.card (TableRow I.branch)) := by
  simp [FermionIdx, InternalIdx, Fintype.card_prod]

end FiniteInterfaceChart

/-! ### The spinor (Clifford) refinement: the paper's incidence operator -/

/-- **`def:finite-interface`, with the spinor incidence of (I3).**  A `FiniteInterfaceChart` whose
fermion fibre carries a Clifford module structure (`γ^aγ^b + γ^bγ^a = 2η^{ab}`, a chirality `γ₅`),
whose site gauges form a group action leaving the coframe untouched, and whose incidence operator
is the finite Dirac incidence operator `Σ_μ i γ^μ(e) ∇^h_μ - 1_spin ⊗ 𝓜_𝐘(H)` of the native
Dirac density, built from covariant spin–gauge links on the oriented edges `x → next μ x` and a
covariant real-affine Yukawa map (`lem:SM-descent`). -/
structure SpinorFiniteInterface (h : ℝ) extends FiniteInterfaceChart h where
  /-- (I1)/(I3) the oriented incidence of the carrier: the edge `x → x + e_μ` -/
  next : Fin 4 → Site ≃ Site
  /-- (I3) the spinor fibre is nonempty -/
  spin_nonempty : Nonempty SpinIdx
  /-- (I3) the frame gamma matrices `γ^a` -/
  gamma : Fin 4 → Matrix SpinIdx SpinIdx ℂ
  /-- (I3) the Clifford relations `γ^aγ^b + γ^bγ^a = 2η^{ab}`, `η = diag(-1,1,1,1)` -/
  gamma_clifford : ∀ a c, gamma a * gamma c + gamma c * gamma a = (2 * etaC a c) • 1
  /-- (I2)/(I3) the spinor chirality `γ₅` -/
  gamma5 : Matrix SpinIdx SpinIdx ℂ
  gamma5_sq : gamma5 * gamma5 = 1
  gamma5_anticomm : ∀ a, gamma5 * gamma a = -(gamma a * gamma5)
  /-- (I4) site gauges form a group action -/
  gaugeAct_one : ∀ q, gaugeAct 1 q = q
  gaugeAct_mul : ∀ γ γ' q, gaugeAct (γ * γ') q = gaugeAct γ (gaugeAct γ' q)
  /-- (I4) internal gauges do not act on the coframe -/
  coframe_gaugeAct : ∀ γ q x, coframe (gaugeAct γ q) x = coframe q x
  /-- (I3) the spin–gauge link `V_μ(x)` transporting the fibre at `x + e_μ` to `x` -/
  spinLink : Config → Site → Fin 4 → Matrix (FermionIdx SpinIdx branch) (FermionIdx SpinIdx branch) ℂ
  /-- (I3) covariance of the spin–gauge links -/
  spinLink_covariant : ∀ γ q x μ, spinLink (gaugeAct γ q) x μ =
    fibreRep SpinIdx branch (γ x) * spinLink q x μ * fibreRep SpinIdx branch (γ (next μ x))⁻¹
  /-- (I3) the Yukawa map `H ↦ 𝓜_𝐘(H)` on generation × table rows, real-affine in `H` -/
  yukawaMap : (Fin 2 → ℂ) →ᵃ[ℝ] Matrix (InternalIdx branch) (InternalIdx branch) ℂ
  /-- (I3) covariance of the Yukawa map (`lem:SM-descent`) -/
  yukawaMap_covariant : ∀ y H, yukawaMap (higgsRep y H) =
    internalRep branch y * yukawaMap H * internalRep branch y⁻¹
  /-- (I3) the incidence operator is the finite Dirac incidence operator -/
  dirac_eq : ∀ q, dirac q = incidenceOp h next gamma (coframe q) (spinLink q)
    (fun x => yukawaMap (higgs q x))

namespace SpinorFiniteInterface

variable {h : ℝ} (I : SpinorFiniteInterface h)

/-- The chirality grading `γ₅ ⊗ 1_gen ⊗ tableChirality` of the fermion fibre. -/
def chiralGrading : Matrix (FermionIdx I.SpinIdx I.branch) (FermionIdx I.SpinIdx I.branch) ℂ :=
  I.gamma5 ⊗ₖ ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ tableChirality I.branch)

/-- The chiral carrier (spacetime chirality column of `tab:SM-representations`): the `-1`
eigenspace of the grading, i.e. spinors of chirality `γ₅ = -1` on the left rows and `γ₅ = +1` on
the right rows. -/
def IsChiral (v : FermionIdx I.SpinIdx I.branch → ℂ) : Prop := I.chiralGrading *ᵥ v = -v

theorem chiralGrading_mul_self : I.chiralGrading * I.chiralGrading = 1 := by
  simp only [chiralGrading, ← mul_kronecker_mul, I.gamma5_sq, Matrix.one_mul,
    tableChirality_mul_self, one_kronecker_one]

/-- The chirality grading commutes with the gauge action of the fibre. -/
theorem chiralGrading_commute (y : SMGaugeGroup) :
    I.chiralGrading * fibreRep I.SpinIdx I.branch y =
      fibreRep I.SpinIdx I.branch y * I.chiralGrading := by
  simp only [chiralGrading, fibreRep_apply, internalOp, internalRep, MonoidHom.coe_mk,
    OneHom.coe_mk, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, tableChirality_commute]

/-- With the Clifford relations a spinor fibre cannot be one dimensional (the gamma matrices
would commute, forcing `γ⁰γ¹ = 0`, while `(γ⁰)² = -1`, `(γ¹)² = 1`). -/
theorem card_spinIdx_ne_one : Fintype.card I.SpinIdx ≠ 1 := by
  intro hcard
  haveI : Subsingleton I.SpinIdx := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  have hcomm : ∀ A B : Matrix I.SpinIdx I.SpinIdx ℂ, A * B = B * A := by
    intro A B; ext i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [Matrix.mul_apply, Fintype.sum_subsingleton _ i, mul_comm]
  have h00 := I.gamma_clifford 0 0
  have h11 := I.gamma_clifford 1 1
  have h01 := I.gamma_clifford 0 1
  have e00 : etaC 0 0 = -1 := by simp [etaC, minkowskiEta]
  have e11 : etaC 1 1 = 1 := by simp [etaC, minkowskiEta]
  have e01 : etaC 0 1 = 0 := by simp [etaC, minkowskiEta]
  rw [e00] at h00; rw [e11] at h11; rw [e01] at h01
  rw [hcomm (I.gamma 1) (I.gamma 0)] at h01
  have hz : I.gamma 0 * I.gamma 1 = 0 := by
    have : (2 : ℂ) • (I.gamma 0 * I.gamma 1) = 0 := by rw [two_smul, h01]; simp
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  have hsq0 : I.gamma 0 * I.gamma 0 = -1 := by
    have : (2 : ℂ) • (I.gamma 0 * I.gamma 0) = (2 : ℂ) • (-1) := by
      rw [two_smul, h00, mul_smul, neg_one_smul]
    exact smul_right_injective _ two_ne_zero this
  have hsq1 : I.gamma 1 * I.gamma 1 = 1 := by
    have : (2 : ℂ) • (I.gamma 1 * I.gamma 1) = (2 : ℂ) • 1 := by
      rw [two_smul, h11, mul_one]
    exact smul_right_injective _ two_ne_zero this
  obtain ⟨i⟩ := I.spin_nonempty
  have : (I.gamma 0 * I.gamma 1) * (I.gamma 1 * I.gamma 0) = -1 := by
    calc _ = I.gamma 0 * (I.gamma 1 * I.gamma 1) * I.gamma 0 := by simp only [Matrix.mul_assoc]
      _ = -1 := by rw [hsq1, Matrix.mul_one, hsq0]
  rw [hz, Matrix.zero_mul] at this
  have := congrFun (congrFun this i) i
  simp at this

/-- **Gauge covariance of the Dirac incidence operator** follows from the covariance of its
spin–gauge links and Yukawa blocks. -/
theorem dirac_covariant' (γ : I.Site → SMGaugeGroup) (q : I.Config)
    (ψ : FermionField I.Site I.SpinIdx I.branch) (x : I.Site) :
    I.dirac (I.gaugeAct γ q) (fun y => fibreRep I.SpinIdx I.branch (γ y) *ᵥ ψ y) x =
      fibreRep I.SpinIdx I.branch (γ x) *ᵥ I.dirac q ψ x := by
  rw [I.dirac_eq, I.dirac_eq]
  have he : I.coframe (I.gaugeAct γ q) = I.coframe q := funext fun x => I.coframe_gaugeAct γ q x
  rw [he]
  exact incidenceOp_covariant h I.next I.gamma (I.coframe q) _ _ _ _ γ
    (fun x μ => I.spinLink_covariant γ q x μ)
    (fun x => by rw [I.higgs_covariant, I.yukawaMap_covariant]) ψ x

end SpinorFiniteInterface

/-! ### The earlier encoding embeds (spinor-trivial case) -/

namespace TabulatedFiniteInterface

variable {h : ℝ} (I : TabulatedFiniteInterface h)

/-- The linear equivalence between the earlier fermion carrier `Site → Fin 3 → OneGeneration` and
the spinor-trivial fermion fields `Site → Unit × Fin 3 × TableRow → ℂ`, through `tableEquiv`. -/
noncomputable def fermionEquiv :
    (I.Site → Fin 3 → I.OneGeneration) ≃ₗ[ℂ] FermionField I.Site Unit I.branch where
  toFun φ x p := I.tableEquiv (φ x p.2.1) p.2.2
  invFun ψ x g := I.tableEquiv.symm (fun r => ψ x ((), g, r))
  map_add' φ φ' := by funext x p; simp
  map_smul' c φ := by funext x p; simp
  left_inv φ := by funext x g; simp
  right_inv ψ := by funext x p; obtain ⟨⟨⟩, g, r⟩ := p; simp

theorem fermionEquiv_covariant (γ : I.Site → SMGaugeGroup) (φ : I.Site → Fin 3 → I.OneGeneration) :
    I.fermionEquiv (fun y m => I.fermionRep (γ y) (φ y m)) =
      fun y => fibreRep Unit I.branch (γ y) *ᵥ I.fermionEquiv φ y := by
  funext y p
  obtain ⟨⟨⟩, g, r⟩ := p
  rw [fibreRep_mulVec_apply]
  simp only [fermionEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [I.tableEquiv_fermionRep]

/-- **The earlier encoding embeds into the chart encoding** (spinor-trivial case): spin index
`Unit`, admissible chart = the whole configuration space, incidence operator conjugated by
`fermionEquiv`, Gram form `⟨gram u, v⟩`. -/
noncomputable def toChart : FiniteInterfaceChart h where
  Site := I.Site
  Config := I.Config
  chart := Set.univ
  chart_isOpen := isOpen_univ
  chart_nonempty := Set.univ_nonempty
  coframe := I.coframe
  coframe_oriented q _ x := I.coframe_oriented q x
  coframe_timeOriented q _ x := I.coframe_timeOriented q x
  branch := I.branch
  higgs := I.higgs
  SpinIdx := Unit
  YukawaSector := I.YukawaSector
  coefficients := I.coefficients
  dirac q := I.fermionEquiv.toLinearMap ∘ₗ I.dirac q ∘ₗ I.fermionEquiv.symm.toLinearMap
  gaugeAct := I.gaugeAct
  higgs_covariant := I.higgs_covariant
  dirac_covariant γ q ψ x := by
    obtain ⟨φ, rfl⟩ := I.fermionEquiv.surjective ψ
    have hd : I.dirac (I.gaugeAct γ q) (fun y m => I.fermionRep (γ y) (φ y m)) =
        fun y m => I.fermionRep (γ y) (I.dirac q φ y m) := by
      funext y m
      exact I.dirac_covariant γ q φ y m
    rw [← I.fermionEquiv_covariant γ φ]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    rw [hd, I.fermionEquiv_covariant γ (I.dirac q φ)]
  gravityAction := I.gravityAction
  matterAction := I.matterAction
  relativeNormalization := I.relativeNormalization
  relativeNormalization_pos := I.relativeNormalization_pos
  chart_gaugeAct _ _ _ := Set.mem_univ _
  action_differentiableOn := I.action_differentiable.differentiableOn
  action_gauge_invariant γ q _ := I.action_gauge_invariant γ q
  retained := I.retained
  gram := LinearMap.mk₂ ℝ (fun u v => inner ℝ (I.gram u) v)
    (fun u u' v => by rw [map_add, inner_add_left])
    (fun c u v => by rw [map_smul, real_inner_smul_left, smul_eq_mul])
    (fun u v v' => inner_add_right _ _ _)
    (fun c u v => by rw [real_inner_smul_right, smul_eq_mul])
  gram_symm u v := by
    simp only [LinearMap.mk₂_apply]
    rw [I.gram_symmetric, real_inner_comm]
  gram_nonneg v := by simpa [real_inner_comm] using I.gram_nonneg v
  gram_pos_retained v hv hv0 := by simpa [real_inner_comm] using I.gram_pos_retained v hv hv0

/-- **Nothing is lost**: the incidence operator of `toChart` is the earlier one conjugated by the
carrier equivalence. -/
theorem toChart_dirac (q : I.Config) :
    I.toChart.dirac q =
      I.fermionEquiv.toLinearMap ∘ₗ I.dirac q ∘ₗ I.fermionEquiv.symm.toLinearMap := rfl

theorem toChart_action (q : I.Config) : I.toChart.action q = I.action q := rfl

theorem toChart_gram (u v : I.Config) : I.toChart.gram u v = inner ℝ (I.gram u) v := rfl

theorem toChart_chart : I.toChart.chart = Set.univ := rfl

theorem toChart_coframe : I.toChart.coframe = I.coframe := rfl

theorem toChart_gaugeAct : I.toChart.gaugeAct = I.gaugeAct := rfl

theorem toChart_coefficients : I.toChart.coefficients = I.coefficients := rfl

end TabulatedFiniteInterface

end RenewalGeometry
