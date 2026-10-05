/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMVariationContinuity
import RenewalGeometry.Analysis.CardinalQuasiInterpolant
import RenewalGeometry.Analysis.TransportStencilVariation
import RenewalGeometry.Analysis.C11BoundsCalculus

/-!
# The smooth comparison regulator of `app:reconstruction`

Einstein–Standard-Model action-closure manuscript, `app:reconstruction` ("A finite smooth
comparison reconstruction", `eq:smooth-reconstruction`, `eq:lattice-comparison`,
`eq:spin-difference`) and `def:regulator` (`eq:C1-consistency`).  This file **encodes the
comparison regulator**; its first-variation consistency `eq:mesh-C1` is
`EinsteinSMMeshConsistency.lean`.

## Records and reconstruction

* Mesh `h = 1/N`; the comparison box is periodic with period `P ∈ ℕ` in time (`T ≤ P`, the
  slab `(0,T)` lies in one period: the "slightly larger region" of the manuscript, with an
  auxiliary temporal seam that is never seen by the tests) and period `1` in space (`𝕋³`).
* The configuration space `𝒬_h = records P N left` consists of nodal data
  `q : ℤ⁴ → (e, A, H, Ψ, Ψ̄)` that are periodic (`perVec`) and admissible (`A ∈ 𝔰(𝔲(3)⊕𝔲(2))`,
  chiral spinors); it is finite dimensional (`finiteDimensional_records`).
* The reconstruction `𝒥_h q = reconFields h q` is the smooth cardinal quasi-interpolant
  `Σ_j Φ(x/h - j) q(j)` of `Analysis/CardinalQuasiInterpolant` applied componentwise (the
  mollified multilinear interpolant), packaged as smooth fields on `M` (`reconSmooth`).
* The test lift `𝓘_h v = liftRec` samples the complete variation `v̂ = (ė(k), a, η_H, η_Ψ, η_Ψ̄)`
  (`variationDirection`, symmetric coframe lift at the reconstructed coframe) at the nodes of the
  fundamental box, periodically continued (`EinsteinSM.variationDirection`).

## The comparison action

* **Lattice comparison quantities** at a node `x` (`eq:lattice-comparison`, `eq:spin-difference`)
  of the reconstructed fields: the logarithmic plaquettes
  `F^h_{μν} = h⁻² log(U_μ(x)U_ν(x+he_μ)U_μ(x+he_ν)⁻¹U_ν(x)⁻¹)` of the backward parallel transports
  `U_μ` of the reconstructed connection in the defining representation (`fieldStrengthH`, `YMAlg`:
  `5 × 5` complex matrices with the operator norm), the Higgs links
  `K^h_μ = h⁻¹(U_μ(x)H(x+he_μ) - H(x))` (`higgsLinkH`, transports of `ρ_H(A)`), and the centred
  spin–gauge differences `∇^h_μΨ` of `eq:spin-difference` (`spinorDiffH`, transports of the
  spin–gauge connection `Ω_μ + ρ_F(A_μ)` built from the reconstructed coframe) and their duals
  (`cospinorDiffH`, transports of the dual connection).
* **The Standard-Model comparison action** `S_{SM,h}(q) = h⁴ Σ_{x ∈ box} 𝓛_{SM}(stencils)(x)`
  (`smAction`): the Standard-Model density `eq:SM-action`/`eq:dirac-density` with all
  coefficients (`√|g|`, `g^{μν}`, `γ^μ = E^μ_aγ^a`, Yukawa) computed from the reconstructed coframe
  and Higgs field at the node and the derivative packets replaced by the lattice quantities
  (`stencilJet`, evaluated by the library's jet density `smPt`).
* **The gravitational comparison action** `S_{g,h}(q) = ∫_{box} L₁(𝒥_h e, ∂𝒥_h e)` (`gravAction`):
  the integrated first-derivative representative of the Einstein–Hilbert density on the same
  reconstruction (exact integration).  The library's first-order representative is the metric
  `ΓΓ` form `gravPt` (`EinsteinSMGravityFirstOrder`); on the periodic box all first-order
  representatives of `√|g| R` differ by a divergence and have the same integral.
* `finiteVar S q w = d/dt S(q + t w)|₀` is the finite first variation, and
  `comparisonDefect` the defect `c_h(K)` of `eq:C1-consistency`.

Disclosed renderings: tensor-product (`Q1`) nodal basis and tensor mollifier instead of the
simplicial interpolant; periodic comparison box; the finite first variation is the directional
derivative along the lifted test (the only derivative `eq:C1-consistency` uses).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace EinsteinSM
namespace Comparison

open SobolevOpen (pd)
open CardinalQI TransportPlaquetteConsistency TransportStencilVariation

/-! ### The Yang–Mills transport algebra -/

/-- The transport algebra of the defining representation: real-linear operators on `ℂ⁵` with
the operator norm (a complete normed real algebra with `‖1‖ = 1`); a Lie-algebra element
`X ∈ 𝔰(𝔲(3)⊕𝔲(2))` acts by matrix multiplication (`toYM`). -/
abbrev YMAlg : Type := (Fin 5 → ℂ) →L[ℝ] (Fin 5 → ℂ)

/-- Matrix multiplication by `X` as an operator. -/
def ymOp (X : LieFibre) : YMAlg :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin (Matrix.of X)).restrictScalars ℝ)

theorem ymOp_apply (X : LieFibre) (v : Fin 5 → ℂ) (i : Fin 5) :
    ymOp X v i = ∑ k, X i k * v k := by
  simp [ymOp, Matrix.mulVec, dotProduct]

/-- `LieFibre → YMAlg`, `X ↦ (v ↦ X v)`, continuous real-linear. -/
def toYM : LieFibre →L[ℝ] YMAlg :=
  LinearMap.toContinuousLinearMap
    { toFun := ymOp
      map_add' := fun X Y => by
        ext v i; simp only [ContinuousLinearMap.add_apply, Pi.add_apply, ymOp_apply, add_mul,
          Finset.sum_add_distrib]
      map_smul' := fun r X => by
        ext v i
        simp only [ContinuousLinearMap.smul_apply, Pi.smul_apply, ymOp_apply, RingHom.id_apply,
          Finset.smul_sum, smul_mul_assoc] }

theorem toYM_apply (X : LieFibre) (v : Fin 5 → ℂ) (i : Fin 5) :
    toYM X v i = ∑ k, X i k * v k := ymOp_apply X v i

/-- `YMAlg → LieFibre`, the matrix of an operator, continuous real-linear. -/
def fromYM : YMAlg →L[ℝ] LieFibre :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T i j => T (Pi.single j 1) i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem fromYM_apply (T : YMAlg) (i j : Fin 5) : fromYM T i j = T (Pi.single j 1) i := rfl

@[simp] theorem fromYM_toYM (X : LieFibre) : fromYM (toYM X) = X := by
  funext i j
  rw [fromYM_apply, toYM_apply]
  simp [Pi.single_apply]

theorem toYM_mmul (X Y : LieFibre) : toYM (mmul X Y) = toYM X * toYM Y := by
  ext v i
  rw [ContinuousLinearMap.mul_apply, toYM_apply, toYM_apply]
  simp only [mmul, toYM_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem toYM_comm (X Y : LieFibre) : toYM (comm X Y) = toYM X * toYM Y - toYM Y * toYM X := by
  rw [comm, map_sub, toYM_mmul, toYM_mmul]

/-! ### Connection operators -/

/-- `ρ_H(X) = ` the `𝔲(2)` block action on the Higgs doublet, as a continuous linear map. -/
def higgsActL (X : LieFibre) : HiggsFibre →L[ℝ] HiggsFibre :=
  LinearMap.toContinuousLinearMap
    { toFun := higgsAct X
      map_add' := fun u v => by funext i; simp [higgsAct, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r u => by
        funext i; simp [higgsAct, Finset.mul_sum, Complex.real_smul]; ring_nf }

theorem higgsActL_apply (X : LieFibre) (v : HiggsFibre) : higgsActL X v = higgsAct X v := rfl

/-- `X ↦ ρ_H(X)` as a continuous linear map. -/
def higgsOpL : LieFibre →L[ℝ] (HiggsFibre →L[ℝ] HiggsFibre) :=
  LinearMap.toContinuousLinearMap
    { toFun := higgsActL
      map_add' := fun X Y => by
        ext v i; simp [higgsActL_apply, higgsAct, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r X => by
        ext v i; simp [higgsActL_apply, higgsAct, Finset.mul_sum, Complex.real_smul]; ring_nf }

/-- The Yang–Mills connection component `A_μ` in the transport algebra. -/
def ymConn (A : E4 → ConnFibre) (μ : Fin 4) : E4 → YMAlg := fun y => toYM (A y μ)

/-- The Higgs connection component `ρ_H(A_μ)`. -/
def higgsConn (A : E4 → ConnFibre) (μ : Fin 4) : E4 → HiggsFibre →L[ℝ] HiggsFibre :=
  fun y => higgsOpL (A y μ)

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-- The spin–gauge connection operator `Ψ ↦ S Ψ + M Ψ` (`S` acting on the Dirac index, `M` on the
carrier index). -/
def spinConnOp (S : Fin 4 → Fin 4 → ℂ) (M : FC.C → FC.C → ℂ) :
    SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ s c => ∑ s', S s s' * ψ s' c + ∑ c', M c c' * ψ s c'
      map_add' := fun u v => by
        funext s c; simp [mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun r u => by
        funext s c
        simp only [Pi.smul_apply, RingHom.id_apply, smul_add, Finset.smul_sum, mul_smul_comm] }

/-- The dual connection operator `Ψ̄ ↦ -(Ψ̄ S + Ψ̄ M)` (the dual transport of the manuscript). -/
def cospinConnOp (S : Fin 4 → Fin 4 → ℂ) (M : FC.C → FC.C → ℂ) :
    SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ s c => -(∑ s', ψ s' c * S s' s) - ∑ c', ψ s c' * M c' c
      map_add' := fun u v => by
        funext s c; simp [add_mul, Finset.sum_add_distrib]; ring
      map_smul' := fun r u => by
        funext s c
        simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, smul_neg, Finset.smul_sum,
          smul_mul_assoc] }

/-- The spin–gauge connection `Ω_μ + ρ_F(A_μ)` of fields `z` (Levi-Civita spin connection of the
coframe). -/
def spinConnection (z : FieldTuple FC.C) (μ : Fin 4) (y : E4) :
    SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C :=
  spinConnOp FC (spinGen z.e y μ) (FC.rho (z.A y μ))

/-- The dual spin–gauge connection. -/
def cospinConnection (z : FieldTuple FC.C) (μ : Fin 4) (y : E4) :
    SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C :=
  cospinConnOp FC (spinGen z.e y μ) (FC.rho (z.A y μ))

theorem covDerivSpinor_eq (z : FieldTuple FC.C) (x : E4) (μ : Fin 4) :
    covDerivSpinor FC z.e z.A z.Ψ x μ = pd z.Ψ μ x + spinConnection FC z μ x (z.Ψ x) := by
  funext s c
  simp [covDerivSpinor, spinConnection, spinConnOp, add_assoc]

theorem covDerivCospinor_eq (z : FieldTuple FC.C) (x : E4) (μ : Fin 4) :
    covDerivCospinor FC z.e z.A z.Ψb x μ = pd z.Ψb μ x + cospinConnection FC z μ x (z.Ψb x) := by
  funext s c
  simp [covDerivCospinor, cospinConnection, cospinConnOp]
  ring

theorem covDerivHiggs_eq (A : E4 → ConnFibre) (H : E4 → HiggsFibre) (x : E4) (μ : Fin 4) :
    covDerivHiggs A H x μ = pd H μ x + higgsConn A μ x (H x) := rfl

/-! ### The lattice comparison quantities (`eq:lattice-comparison`, `eq:spin-difference`) -/

/-- The coordinate unit vector `e_μ`. -/
def unitE (μ : Fin 4) : E4 := Pi.single μ 1

/-- The logarithmic plaquette `h⁻² log U_{μν}(x)` of the backward transports, `μ < ν`. -/
def logPlaq (h : ℝ) (A : E4 → ConnFibre) (x : E4) (μ ν : Fin 4) : LieFibre :=
  fromYM ((h ^ 2)⁻¹ • ShiftedPlaquette.logOneAdd
    (TransportGaugeVariation.linkPlaquette (ymConn A μ) (ymConn A ν) (unitE μ) (unitE ν) x h - 1))

/-- **The comparison field strength** `F^h_{μν}`: the logarithmic plaquette for `μ < ν`,
antisymmetrically extended. -/
def fieldStrengthH (h : ℝ) (A : E4 → ConnFibre) (x : E4) : Fin 4 → ConnFibre := fun μ ν =>
  if μ < ν then logPlaq h A x μ ν else if ν < μ then -logPlaq h A x ν μ else 0

/-- **The comparison Higgs links** `K^h_μ = h⁻¹(U_μ(x)H(x+he_μ) - H(x))`. -/
def higgsLinkH (h : ℝ) (A : E4 → ConnFibre) (H : E4 → HiggsFibre) (x : E4) :
    Fin 4 → HiggsFibre := fun μ => fwdDiff (higgsConn A μ) H (unitE μ) x h

/-- **The centred spin–gauge differences** of `eq:spin-difference`. -/
def spinorDiffH (h : ℝ) (z : FieldTuple FC.C) (x : E4) : Fin 4 → SpinorFibre FC.C :=
  fun μ => centredDiff (spinConnection FC z μ) z.Ψ (unitE μ) x h

/-- The dual-spinor differences (dual transport). -/
def cospinorDiffH (h : ℝ) (z : FieldTuple FC.C) (x : E4) : Fin 4 → SpinorFibre FC.C :=
  fun μ => centredDiff (cospinConnection FC z μ) z.Ψb (unitE μ) x h

/-- **The comparison stencil jet** at a node: coframe, Higgs and spinor values, the lattice
comparison field strength, Higgs links and spin–gauge differences (the derivative packets of the
Standard-Model density). -/
def stencilJet (h : ℝ) (z : FieldTuple FC.C) (x : E4) : RJet FC.C :=
  RJet.mk (z.e x) 0 0 (fieldStrengthH h z.A x) (z.H x) (higgsLinkH h z.A z.H x) (z.Ψ x)
    (spinorDiffH FC h z x) (z.Ψb x) (cospinorDiffH FC h z x)

/-- The continuum packet jet: the same slots filled with `F`, `D_AH`, `∇Ψ`, `∇Ψ̄`. -/
def contJet (z : FieldTuple FC.C) (x : E4) : RJet FC.C :=
  RJet.mk (z.e x) 0 0 (curvatureF z.A x) (z.H x) (covDerivHiggs z.A z.H x) (z.Ψ x)
    (covDerivSpinor FC z.e z.A z.Ψ x) (z.Ψb x) (covDerivCospinor FC z.e z.A z.Ψb x)

/-! ### Records, reconstruction and lift -/

/-- Field values `(e, A, H, Ψ, Ψ̄)` at a node. -/
abbrev FieldVal (C : Type) [Fintype C] : Type :=
  CoframeFibre × ConnFibre × HiggsFibre × SpinorFibre C × SpinorFibre C

/-- The lattice periods: `P N` nodes in time, `N` nodes in each spatial direction. -/
def perVec (P N : ℕ) (m : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => if i = 0 then (P * N : ℕ) * m i else (N : ℤ) * m i

/-- Admissible node values: `A_μ ∈ 𝔰(𝔲(3) ⊕ 𝔲(2))`, chiral spinors. -/
def admissible (left : FC.C → Bool) : Submodule ℝ (FieldVal FC.C) where
  carrier := {w | (∀ μ, w.2.1 μ ∈ smLie) ∧ IsChiral left w.2.2.2.1 ∧ IsCoChiral left w.2.2.2.2}
  add_mem' := by
    rintro a b ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun μ => smLie.add_mem (h1 μ) (k1 μ), fun s c hs => ?_, fun s c hs => ?_⟩
    · show a.2.2.2.1 s c + b.2.2.2.1 s c = 0; rw [h2 s c hs, k2 s c hs, add_zero]
    · show a.2.2.2.2 s c + b.2.2.2.2 s c = 0; rw [h3 s c hs, k3 s c hs, add_zero]
  zero_mem' := ⟨fun _ => smLie.zero_mem, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro r a ⟨h1, h2, h3⟩
    refine ⟨fun μ => smLie.smul_mem r (h1 μ), fun s c hs => ?_, fun s c hs => ?_⟩
    · show r • a.2.2.2.1 s c = 0; rw [h2 s c hs, smul_zero]
    · show r • a.2.2.2.2 s c = 0; rw [h3 s c hs, smul_zero]

/-- **The configuration space `𝒬_h`**: periodic admissible nodal records. -/
def records (P N : ℕ) (left : FC.C → Bool) : Submodule ℝ ((Fin 4 → ℤ) → FieldVal FC.C) where
  carrier := {q | (∀ j m, q (j + perVec P N m) = q j) ∧ ∀ j, q j ∈ admissible FC left}
  add_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨k1, k2⟩
    exact ⟨fun j m => by simp [h1 j m, k1 j m], fun j => (admissible FC left).add_mem (h2 j) (k2 j)⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ => (admissible FC left).zero_mem⟩
  smul_mem' := by
    rintro r a ⟨h1, h2⟩
    exact ⟨fun j m => by simp [h1 j m], fun j => (admissible FC left).smul_mem r (h2 j)⟩

/-- **The reconstruction `𝒥_h`** of nodal data, componentwise. -/
def reconFields (h : ℝ) (q : (Fin 4 → ℤ) → FieldVal FC.C) : FieldTuple FC.C :=
  FieldTuple.mk (recon h fun j => (q j).1) (recon h fun j => (q j).2.1)
    (recon h fun j => (q j).2.2.1) (recon h fun j => (q j).2.2.2.1) (recon h fun j => (q j).2.2.2.2)

/-- Nodal sampling of a field tuple. -/
def sampleRec (h : ℝ) (f : FieldTuple FC.C) : (Fin 4 → ℤ) → FieldVal FC.C :=
  fun j => (f.e (h • jc j), f.A (h • jc j), f.H (h • jc j), f.Ψ (h • jc j), f.Ψb (h • jc j))

/-- Reduction of the time index into `[0, P N)`. -/
def reduceIdx (P N : ℕ) (j : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => if i = 0 then j i % ((P * N : ℕ) : ℤ) else j i

/-- **The test lift `𝓘_h v`**: the samples of the complete variation
`v̂ = (ė(k), a, η_H, η_Ψ, η_Ψ̄)` at the reconstructed coframe, on the fundamental time period,
periodically continued. -/
def liftRec (P N : ℕ) (h : ℝ) (z v : FieldTuple FC.C) : (Fin 4 → ℤ) → FieldVal FC.C :=
  fun j => sampleRec FC h (variationDirection z v) (reduceIdx P N j)

/-- The node `k e₀ + j/N` of the comparison box (`k < P` the unit time cell, `j ∈ {0,…,N-1}⁴`):
the nodes `h ℤ⁴ ∩ [0,P) × [0,1)³`, `h = 1/N`. -/
def nodePt (N k : ℕ) (j : Fin 4 → Fin N) : E4 :=
  fun i => (if i = 0 then (k : ℝ) else 0) + (j i : ℝ) / N

/-- The comparison box `[0,P] × [0,1]³`. -/
def compBox (P : ℕ) : Set E4 := Set.Icc 0 (fun i => if i = 0 then (P : ℝ) else 1)

/-! ### The comparison action and its first variation -/

/-- **The Standard-Model comparison action** `S_{SM,h}(q) = h⁴ Σ_{x ∈ box} 𝓛_{SM}(x)`, `h = 1/N`. -/
def smAction (θ : CoefficientBank Ysec) (P N : ℕ) (q : (Fin 4 → ℤ) → FieldVal FC.C) : ℝ :=
  (1 / (N : ℝ)) ^ 4 * ∑ k : Fin P, ∑ j : Fin 4 → Fin N,
    smPt FC θ (stencilJet FC (1 / N) (reconFields FC (1 / N) q) (nodePt N k j))

/-- **The gravitational comparison action** `S_{g,h}(q) = ∫_{box} L₁(𝒥_h e, ∂𝒥_h e)`. -/
def gravAction (θ : CoefficientBank Ysec) (P N : ℕ) (q : (Fin 4 → ℤ) → FieldVal FC.C) : ℝ :=
  ∫ x in compBox P, gravPt (C := FC.C) θ (redJet (reconFields FC (1 / N) q) x)

/-- The comparison sector actions `S_{b,h}`. -/
def sectorAction (θ : CoefficientBank Ysec) (P N : ℕ) :
    Sector → ((Fin 4 → ℤ) → FieldVal FC.C) → ℝ
  | .gravity => gravAction FC θ P N
  | .standardModel => smAction FC θ P N

/-- The finite first variation `D S(q)[w] = d/dt S(q + t w)|₀`. -/
def finiteVar {X : Type*} [AddCommGroup X] [Module ℝ X] (S : X → ℝ) (q w : X) : ℝ :=
  deriv (fun t : ℝ => S (q + t • w)) 0

/-- **The first-variation consistency defect `c_h(K)`** (`eq:C1-consistency`) of the comparison
regulator at the records `q` (mesh `h = 1/N`): `Σ_b sup_{‖v‖_{C^{r₀}} ≤ 1}
|D S_{b,h}(q)[𝓘_h v] - D𝒮_{b,θ}(𝒥_h q)[v]|`. -/
def comparisonDefect (T : ℝ) (θ : CoefficientBank Ysec) (P N r₀ : ℕ) (K : CylRegion T)
    (q : (Fin 4 → ℤ) → FieldVal FC.C) : ℝ≥0∞ :=
  ∑ b : Sector, ⨆ (v : ↥(testSubmodule FC.left K)) (_ : testNorm r₀ v.1 ≤ 1),
    ENNReal.ofReal |finiteVar (sectorAction FC θ P N b) q
        (liftRec FC P N (1 / N) (reconFields FC (1 / N) q) v.1) -
      firstVariation T FC θ b (reconFields FC (1 / N) q) v.1|

end Comparison
end EinsteinSM
end RenewalGeometry
