/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeDiracCoefficients
import RenewalGeometry.Continuum.NativeSpinorCompactness

/-!
# The complete Dirac–Yukawa first variation of the native local action converges
  (`prop:native-spinor-variation`, second assertion; Einstein–SM action-closure manuscript)

Setting: unit-torus rendering of the periodic box (grid `(ℤ/N)⁴`, `h = 1/N`, raw reconstructions
`R_h^0 = pc`), spinor fibre a finite-dimensional real space `𝓢` (realified spinors in one fixed
frame), co-spinors `Ψ̄ = κ χ` read through a fixed linear frame `κ : W' → 𝓢^*` of the dual fibre,
gauge algebra and Higgs fibre finite dimensional.

## The algebraic shape of the first variation

At every node the first variation `dVar` of the finite Dirac–Yukawa action (`NativeDirac.dVar_eq`)
is the evaluation, on the **test jet** `J = (k, δ⁺k, a, η, ψ, δ⁺ψ, ψ̄, δ⁺ψ̄) ∈ Jet` of the lifted
tests, of two operator fields built from the **slot values** (`Slots`) of the record:

* `Gfun S J` — the part paired with values: link and Yukawa terms
  `Re(i/2 Ψ̄ δΞ[J] T_μΨ)`, `Re(i/2 T_μΨ̄ δΞ'[J] Ψ)`, `Re(Ψ̄ δM[J] Ψ)`, the co-spinor test against
  `Ξ T_μΨ`, `Γ' Ψ`, `Ξ' Ψ`, `MΨ` and the spinor test against `Ψ̄ Γ`, `Ψ̄ Ξ`, `T_μΨ̄ Ξ'`, `Ψ̄ M`;
* `Λfun S J u` — the part paired with the first differences `u = (δ⁺Ψ, δ⁺χ)`:
  `Re(i/2 Ψ̄ δΓ[J] δ⁺Ψ) - Re(i/2 (κδ⁺χ) δΓ[J] Ψ) + Re(i/2 (κψ̄) Γ δ⁺Ψ) - Re(i/2 (κδ⁺χ) Γ ψ)`.

The same functions evaluated at the **continuum slots** (`h = 0`, `T_μΨ = Ψ`, `W = B`, `W' = -B`,
`B_μ = σ(Ω_μ(e, ∂e)) + ρ_S(A_μ)`, `δW = σ(δω) + ρ_S(a)`) give the continuum Dirac–Yukawa covector.
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace
open scoped BigOperators ENNReal NNReal

namespace RenewalGeometry.NativeDiracLimit

open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat readerOmega omegaLink)
open NativeGravityFirstJet (M4 asM4 coframeM liftM liftL dqLift dqLiftL)
open NativeDensity NativeDirac NativeDiracConv

noncomputable section

set_option linter.unusedSectionVars false

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']

/-! ### Test jets -/

/-- The test jet `(k, δ⁺k, a, η, ψ, δ⁺ψ, ψ̄, δ⁺ψ̄)`. -/
abbrev Jet (𝔄 𝓗 𝓢 W' : Type*) [NormedRing 𝔄] [NormedAddCommGroup 𝓗] [NormedAddCommGroup 𝓢]
    [NormedAddCommGroup W'] :=
  M4 × (Fin 4 → M4) × (Fin 4 → 𝔄) × 𝓗 × 𝓢 × (Fin 4 → 𝓢) × W' × (Fin 4 → W')

/-- The first differences `(δ⁺Ψ, δ⁺χ)` paired with the kinetic part. -/
abbrev Dif (𝓢 W' : Type*) [NormedAddCommGroup 𝓢] [NormedAddCommGroup W'] :=
  (Fin 4 → 𝓢) × (Fin 4 → W')

section Proj

variable (𝔄 𝓗 𝓢 W')

def πk : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] M4 := ContinuousLinearMap.fst ℝ _ _
def πdk : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] (Fin 4 → M4) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
def πa : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] (Fin 4 → 𝔄) :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    (ContinuousLinearMap.snd ℝ _ _))
def πη : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] 𝓗 :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))
def πψ : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] 𝓢 :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      (ContinuousLinearMap.snd ℝ _ _))))
def πdψ : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] (Fin 4 → 𝓢) :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))))
def πψb : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] W' :=
  (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        (ContinuousLinearMap.snd ℝ _ _))))))
def πdψb : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] (Fin 4 → W') :=
  (ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        (ContinuousLinearMap.snd ℝ _ _))))))

end Proj

@[simp] theorem πk_apply (t : Jet 𝔄 𝓗 𝓢 W') : πk 𝔄 𝓗 𝓢 W' t = t.1 := rfl
@[simp] theorem πdk_apply (t : Jet 𝔄 𝓗 𝓢 W') : πdk 𝔄 𝓗 𝓢 W' t = t.2.1 := rfl
@[simp] theorem πa_apply (t : Jet 𝔄 𝓗 𝓢 W') : πa 𝔄 𝓗 𝓢 W' t = t.2.2.1 := rfl
@[simp] theorem πη_apply (t : Jet 𝔄 𝓗 𝓢 W') : πη 𝔄 𝓗 𝓢 W' t = t.2.2.2.1 := rfl
@[simp] theorem πψ_apply (t : Jet 𝔄 𝓗 𝓢 W') : πψ 𝔄 𝓗 𝓢 W' t = t.2.2.2.2.1 := rfl
@[simp] theorem πdψ_apply (t : Jet 𝔄 𝓗 𝓢 W') : πdψ 𝔄 𝓗 𝓢 W' t = t.2.2.2.2.2.1 := rfl
@[simp] theorem πψb_apply (t : Jet 𝔄 𝓗 𝓢 W') : πψb 𝔄 𝓗 𝓢 W' t = t.2.2.2.2.2.2.1 := rfl
@[simp] theorem πdψb_apply (t : Jet 𝔄 𝓗 𝓢 W') : πdψb 𝔄 𝓗 𝓢 W' t = t.2.2.2.2.2.2.2 := rfl

/-! ### Slot values and the two operator fields -/

/-- The slot values of the Dirac first variation at one point: mesh `h`, volume `v` and its
variation `dv[J]`, `γ^μ` and `dγ^μ[J]`, link quotients `W_μ`, `W'_μ` and their variations, the
Yukawa operator `𝓜_𝐘(H)`, spinor values and co-spinor values at the node and the shifted nodes. -/
structure Slots (𝔄 𝓗 𝓢 W' : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [NormedAddCommGroup 𝓗]
    [NormedSpace ℝ 𝓗] [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [NormedAddCommGroup W']
    [NormedSpace ℝ W'] where
  h : ℝ
  v : ℝ
  dv : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] ℝ
  γ : Fin 4 → Spin 𝓢
  dγ : Fin 4 → Jet 𝔄 𝓗 𝓢 W' →L[ℝ] Spin 𝓢
  Wl : Fin 4 → Spin 𝓢
  Wr : Fin 4 → Spin 𝓢
  dWl : Fin 4 → Jet 𝔄 𝓗 𝓢 W' →L[ℝ] Spin 𝓢
  dWr : Fin 4 → Jet 𝔄 𝓗 𝓢 W' →L[ℝ] Spin 𝓢
  YH : Spin 𝓢
  Ψ : 𝓢
  Ψp : Fin 4 → 𝓢
  Ψb : CoSpinor 𝓢
  Ψbp : Fin 4 → CoSpinor 𝓢

/-- `Re(i/2 Φ̄ w)`. -/
abbrev bI : CoSpinor 𝓢 →L[ℝ] 𝓢 →L[ℝ] ℝ := bForm (Complex.I / 2)

/-- `Re(Φ̄ w)`. -/
abbrev bR : CoSpinor 𝓢 →L[ℝ] 𝓢 →L[ℝ] ℝ := bForm 1

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

/-- The `μ`-summand of the value-paired part of the first variation (link terms, spinor and
co-spinor tests against undifferentiated fields), in applied form. -/
def Gμ (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) : ℝ :=
  S.dv t * bI S.Ψb (S.γ μ (S.Wl μ (S.Ψp μ))) + S.v * bI S.Ψb (S.dγ μ t (S.Wl μ (S.Ψp μ))) +
    S.v * bI S.Ψb (S.γ μ (S.dWl μ t (S.Ψp μ))) -
    S.dv t * bI (S.Ψbp μ) (S.Wr μ (S.γ μ S.Ψ)) - S.v * bI (S.Ψbp μ) (S.dWr μ t (S.γ μ S.Ψ)) -
    S.v * bI (S.Ψbp μ) (S.Wr μ (S.dγ μ t S.Ψ)) +
    S.v * bI (κ t.2.2.2.2.2.2.1) (S.γ μ (S.Wl μ (S.Ψp μ))) -
    S.v * bI (κ (t.2.2.2.2.2.2.2 μ)) (S.γ μ S.Ψ) -
    S.v * bI (κ t.2.2.2.2.2.2.1) (S.Wr μ (S.γ μ S.Ψ)) -
    S.h * S.v * bI (κ (t.2.2.2.2.2.2.2 μ)) (S.Wr μ (S.γ μ S.Ψ)) +
    S.v * bI S.Ψb (S.γ μ (t.2.2.2.2.2.1 μ)) +
    S.v * bI S.Ψb (S.γ μ (S.Wl μ t.2.2.2.2.1)) +
    S.h * S.v * bI S.Ψb (S.γ μ (S.Wl μ (t.2.2.2.2.2.1 μ))) -
    S.v * bI (S.Ψbp μ) (S.Wr μ (S.γ μ t.2.2.2.2.1))

/-- The Yukawa part of the value-paired first variation. -/
def G0 (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') : ℝ :=
  S.dv t * bR S.Ψb (S.YH S.Ψ) + S.v * bR S.Ψb (D.yukawa t.2.2.2.1 S.Ψ) +
    S.v * bR (κ t.2.2.2.2.2.2.1) (S.YH S.Ψ) + S.v * bR S.Ψb (S.YH t.2.2.2.2.1)

/-- The value-paired part of the first variation. -/
def Gfun (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') : ℝ :=
  (∑ μ, Gμ κ S t μ) - G0 D κ S t

/-- The `μ`-summand of the difference-paired (kinetic) part. -/
def Λμ (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') (u : Dif 𝓢 W') (μ : Fin 4) : ℝ :=
  S.dv t * bI S.Ψb (S.γ μ (u.1 μ)) + S.v * bI S.Ψb (S.dγ μ t (u.1 μ)) -
    S.dv t * bI (κ (u.2 μ)) (S.γ μ S.Ψ) - S.v * bI (κ (u.2 μ)) (S.dγ μ t S.Ψ) +
    S.v * bI (κ t.2.2.2.2.2.2.1) (S.γ μ (u.1 μ)) - S.v * bI (κ (u.2 μ)) (S.γ μ t.2.2.2.2.1)

/-- The difference-paired (kinetic) part of the first variation. -/
def Λfun (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') (u : Dif 𝓢 W') : ℝ := ∑ μ, Λμ κ S t u μ

section Linearity

variable {D κ}

theorem Gμ_add (S : Slots 𝔄 𝓗 𝓢 W') (t t' : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    Gμ κ S (t + t') μ = Gμ κ S t μ + Gμ κ S t' μ := by
  simp only [Gμ, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
  ring

theorem Gμ_smul (S : Slots 𝔄 𝓗 𝓢 W') (c : ℝ) (t : Jet 𝔄 𝓗 𝓢 W') (μ : Fin 4) :
    Gμ κ S (c • t) μ = c * Gμ κ S t μ := by
  simp only [Gμ, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem G0_add (S : Slots 𝔄 𝓗 𝓢 W') (t t' : Jet 𝔄 𝓗 𝓢 W') :
    G0 D κ S (t + t') = G0 D κ S t + G0 D κ S t' := by
  simp only [G0, Prod.fst_add, Prod.snd_add, map_add, ContinuousLinearMap.add_apply]
  ring

theorem G0_smul (S : Slots 𝔄 𝓗 𝓢 W') (c : ℝ) (t : Jet 𝔄 𝓗 𝓢 W') :
    G0 D κ S (c • t) = c * G0 D κ S t := by
  simp only [G0, Prod.smul_fst, Prod.smul_snd, map_smul, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

theorem Λμ_add_t (S : Slots 𝔄 𝓗 𝓢 W') (t t' : Jet 𝔄 𝓗 𝓢 W') (u : Dif 𝓢 W') (μ : Fin 4) :
    Λμ κ S (t + t') u μ = Λμ κ S t u μ + Λμ κ S t' u μ := by
  simp only [Λμ, Prod.fst_add, Prod.snd_add, map_add, ContinuousLinearMap.add_apply]
  ring

theorem Λμ_smul_t (S : Slots 𝔄 𝓗 𝓢 W') (c : ℝ) (t : Jet 𝔄 𝓗 𝓢 W') (u : Dif 𝓢 W') (μ : Fin 4) :
    Λμ κ S (c • t) u μ = c * Λμ κ S t u μ := by
  simp only [Λμ, Prod.smul_fst, Prod.smul_snd, map_smul, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

theorem Λμ_add_u (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') (u u' : Dif 𝓢 W') (μ : Fin 4) :
    Λμ κ S t (u + u') μ = Λμ κ S t u μ + Λμ κ S t u' μ := by
  simp only [Λμ, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
  ring

theorem Λμ_smul_u (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') (c : ℝ) (u : Dif 𝓢 W') (μ : Fin 4) :
    Λμ κ S t (c • u) μ = c * Λμ κ S t u μ := by
  simp only [Λμ, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end Linearity

/-- The value-paired part as a continuous linear functional of the test jet. -/
def Gop (S : Slots 𝔄 𝓗 𝓢 W') : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := Gfun D κ S
      map_add' := fun t t' => by
        simp only [Gfun, Gμ_add, G0_add, Finset.sum_add_distrib]; ring
      map_smul' := fun c t => by
        simp only [Gfun, Gμ_smul, G0_smul, ← Finset.mul_sum, smul_eq_mul, RingHom.id_apply]
        ring }

theorem Gop_apply (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') : Gop D κ S t = Gfun D κ S t := rfl

/-- The kinetic part as a continuous bilinear form of the test jet and the differences. -/
def Λop (S : Slots 𝔄 𝓗 𝓢 W') : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] Dif 𝓢 W' →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun t => LinearMap.toContinuousLinearMap
        { toFun := Λfun κ S t
          map_add' := fun u u' => by simp only [Λfun, Λμ_add_u, Finset.sum_add_distrib]
          map_smul' := fun c u => by
            simp only [Λfun, Λμ_smul_u, ← Finset.mul_sum, smul_eq_mul, RingHom.id_apply] }
      map_add' := fun t t' => ContinuousLinearMap.ext fun u => by
        change Λfun κ S (t + t') u = Λfun κ S t u + Λfun κ S t' u
        simp only [Λfun, Λμ_add_t, Finset.sum_add_distrib]
      map_smul' := fun c t => ContinuousLinearMap.ext fun u => by
        change Λfun κ S (c • t) u = c * Λfun κ S t u
        simp only [Λfun, Λμ_smul_t, ← Finset.mul_sum] }

theorem Λop_apply (S : Slots 𝔄 𝓗 𝓢 W') (t : Jet 𝔄 𝓗 𝓢 W') (u : Dif 𝓢 W') :
    Λop κ S t u = Λfun κ S t u := rfl
/-! ### The grid slots of a native record -/

section GridSlots

variable {N : ℕ} [NeZero N]

/-- The volume density on the sup-normed arrays. -/
def volM (M : M4) : ℝ := volume (M : Mat)

/-- `γ^μ(e)` on the sup-normed arrays. -/
def gammaM (μ : Fin 4) (M : M4) : Spin 𝓢 := gammaMu D μ (M : Mat)

/-- The lifted coframe test `ε = lift(e, k)` as a linear map of the jet. -/
def εL (e : M4) : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] M4 := (liftL e).comp (πk 𝔄 𝓗 𝓢 W')

/-- The lifted coframe-test differences `δ⁺_λ ε = lift(e(x+λ), δ⁺_λk) + dqLift(e, e(x+λ), δ⁺_λe, k)`. -/
def DεL (e : M4) (eP q : Fin 4 → M4) (lam : Fin 4) : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] M4 :=
  (liftL (eP lam)).comp ((ContinuousLinearMap.proj lam).comp (πdk 𝔄 𝓗 𝓢 W')) +
    (dqLiftL e (eP lam) (q lam)).comp (πk 𝔄 𝓗 𝓢 W')

/-- **The metric variation of the coframe-derived connection** as a linear map of the jet:
`δω_μ = Σ_{λij} (δ⁺_λ ε)_{ij} G_{μλij}(e) + q_{λij} DG_{μλij}(e)[ε]`. -/
def δωL (e : M4) (eP q : Fin 4 → M4) (μ : Fin 4) : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] M4 :=
  ∑ lam, ∑ i, ∑ j, (((CoHyp.entryL i j).comp (DεL e eP q lam)).smulRight
    (omegaCoef μ lam i j e) + (q lam i j) • (fderiv ℝ (omegaCoef μ lam i j) e).comp (εL e))

/-- Left multiplication `M ↦ E M`. -/
def mulLeft (E : Spin 𝓢) : Spin 𝓢 →L[ℝ] Spin 𝓢 := ContinuousLinearMap.mul ℝ (Spin 𝓢) E

@[simp] theorem mulLeft_apply (E M : Spin 𝓢) : mulLeft E M = E * M := rfl

/-- The variation of the link quotient `W_μ` as a linear map of the jet:
`δW = D exp(hσω)[σ(δω)] ρ_S(U) + e^{hσω} ρ_S(D exp(hA)[a])`. -/
def δWL (h : ℝ) (ω : M4) (A : 𝔄) (dω : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] M4) (μ : Fin 4) :
    Jet 𝔄 𝓗 𝓢 W' →L[ℝ] Spin 𝓢 :=
  (mulRight (exp (h • D.ρSL A))).comp ((fderiv ℝ exp (h • σL D ω)).comp ((σL D).comp dω)) +
    (mulLeft (exp (h • σL D ω))).comp (D.ρSL.comp ((fderiv ℝ exp (h • A)).comp
      ((ContinuousLinearMap.proj μ).comp (πa 𝔄 𝓗 𝓢 W'))))

/-- The variation of the inverse link quotient `W'_μ` as a linear map of the jet. -/
def δWRL (h : ℝ) (ω : M4) (A : 𝔄) (dω : Jet 𝔄 𝓗 𝓢 W' →L[ℝ] M4) (μ : Fin 4) :
    Jet 𝔄 𝓗 𝓢 W' →L[ℝ] Spin 𝓢 :=
  (mulRight (exp (-(h • σL D ω)))).comp (D.ρSL.comp ((fderiv ℝ exp (-(h • A))).comp
      (-((ContinuousLinearMap.proj μ).comp (πa 𝔄 𝓗 𝓢 W'))))) +
    (mulLeft (D.ρS (exp (-(h • A))))).comp ((fderiv ℝ exp (-(h • σL D ω))).comp
      (-((σL D).comp dω)))

/-- **The grid slots** of a native record at a node (`h = 1/N`). -/
def gridSlots (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) : Slots 𝔄 𝓗 𝓢 W' where
  h := (N : ℝ)⁻¹
  v := volM (coframeM y x)
  dv := (fderiv ℝ volM (coframeM y x)).comp (εL (coframeM y x))
  γ μ := gammaM D μ (coframeM y x)
  dγ μ := (fderiv ℝ (gammaM D μ) (coframeM y x)).comp (εL (coframeM y x))
  Wl μ := wL D (N : ℝ)⁻¹ y x μ
  Wr μ := wR D (N : ℝ)⁻¹ y x μ
  dWl μ := δWL D (N : ℝ)⁻¹ (ωM y μ x) (gauge y μ x)
    (δωL (coframeM y x) (fun lam => coframeM y (x + unitVec N lam)) (fun lam => qM y lam x) μ) μ
  dWr μ := δWRL D (N : ℝ)⁻¹ (ωM y μ x) (gauge y μ x)
    (δωL (coframeM y x) (fun lam => coframeM y (x + unitVec N lam)) (fun lam => qM y lam x) μ) μ
  YH := D.yukawa (higgs y x)
  Ψ := psi y x
  Ψp μ := psi y (x + unitVec N μ)
  Ψb := psiBar y x
  Ψbp μ := psiBar y (x + unitVec N μ)

end GridSlots

/-! ### Identification of the exact variation coefficients with the slot operators -/

section Identify

variable {N : ℕ} [NeZero N]

theorem hasDerivAt_omegaCoef_line (μ lam i j : Fin 4) {e : M4}
    (he : Matrix.det (show Mat from e) ≠ 0) (ε : M4) :
    HasDerivAt (fun t : ℝ => omegaCoef μ lam i j (e + t • ε))
      (fderiv ℝ (omegaCoef μ lam i j) e ε) 0 :=
  hasDerivAt_comp_line ((contDiffAt_omegaCoef μ lam i j he).differentiableAt (by simp)) ε

/-- **The metric variation of the coframe-derived connection, decomposed**: along a coframe
direction `ε`, `δω_μ = Σ_{λij} (δ⁺_λ ε)_{ij} G_{μλij}(e) + (δ⁺_λ e)_{ij} DG_{μλij}(e)[ε]`. -/
theorem omegaVar_eq_sum (h : ℝ) (y δy : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    asM4 (omegaVar h y δy x μ) =
      ∑ lam, ∑ i, ∑ j, (fwdDiff h lam (coframe δy) x i j • omegaCoef μ lam i j (coframeM y x) +
        fwdDiff h lam (coframe y) x i j •
          fderiv ℝ (omegaCoef μ lam i j) (coframeM y x) (coframeM δy x)) := by
  have H1 : HasDerivAt (fun t : ℝ => asM4 (omegaLink h (coframe (y + t • δy)) x μ))
      (asM4 (omegaVar h y δy x μ)) 0 := hasDerivAt_omegaLink h y δy x μ hx
  have H2 : HasDerivAt (fun t : ℝ => ∑ lam, ∑ i, ∑ j,
      (fwdDiff h lam (coframe y) x i j + t * fwdDiff h lam (coframe δy) x i j) •
        omegaCoef μ lam i j (coframeM y x + t • coframeM δy x))
      (∑ lam, ∑ i, ∑ j, (fwdDiff h lam (coframe δy) x i j • omegaCoef μ lam i j (coframeM y x) +
        fwdDiff h lam (coframe y) x i j •
          fderiv ℝ (omegaCoef μ lam i j) (coframeM y x) (coframeM δy x))) 0 := by
    refine HasDerivAt.fun_sum fun lam _ => HasDerivAt.fun_sum fun i _ =>
      HasDerivAt.fun_sum fun j _ => ?_
    have h1 : HasDerivAt (fun t : ℝ => fwdDiff h lam (coframe y) x i j +
        t * fwdDiff h lam (coframe δy) x i j) (fwdDiff h lam (coframe δy) x i j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (fwdDiff h lam (coframe δy) x i j)).const_add
        (fwdDiff h lam (coframe y) x i j)
    have h2 := hasDerivAt_omegaCoef_line μ lam i j (e := coframeM y x) hx (coframeM δy x)
    have := h1.smul h2
    simp only [zero_mul, add_zero, zero_smul] at this
    refine this.congr_deriv ?_
    abel
  have heq : (fun t : ℝ => asM4 (omegaLink h (coframe (y + t • δy)) x μ)) = fun t : ℝ =>
      ∑ lam, ∑ i, ∑ j, (fwdDiff h lam (coframe y) x i j + t * fwdDiff h lam (coframe δy) x i j) •
        omegaCoef μ lam i j (coframeM y x + t • coframeM δy x) := by
    funext t
    rw [omegaLink, readerOmega_expand]
    refine Finset.sum_congr rfl fun lam _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    rw [coframe_add_smul, fwdDiff_add_smul]
    rfl
  rw [heq] at H1
  exact H1.unique H2

end Identify

/-! ### Tests, the sampled test jet, and the nodal test record -/

section Tests

open TorusC2Tests

/-- **A Dirac-sector test**: inverse-metric, gauge, Higgs, spinor and co-spinor tests, all `C²`
on `𝕋⁴` (bounded sets of `C^r` tests, `r ≥ 2`, are bounded in this norm). -/
structure DTest (𝔄 𝓗 𝓢 W' : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [NormedAddCommGroup 𝓗]
    [NormedSpace ℝ 𝓗] [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [NormedAddCommGroup W']
    [NormedSpace ℝ W'] where
  k : C2Test M4
  a : C2Test (Fin 4 → 𝔄)
  η : C2Test 𝓗
  ψ : C2Test 𝓢
  ψb : C2Test W'

/-- The `C²` norm of a Dirac-sector test. -/
def DTest.norm (τ : DTest 𝔄 𝓗 𝓢 W') : ℝ := τ.k.norm + τ.a.norm + τ.η.norm + τ.ψ.norm + τ.ψb.norm

theorem DTest.norm_nonneg (τ : DTest 𝔄 𝓗 𝓢 W') : 0 ≤ τ.norm := by
  unfold DTest.norm
  have := τ.k.norm_nonneg; have := τ.a.norm_nonneg; have := τ.η.norm_nonneg
  have := τ.ψ.norm_nonneg; have := τ.ψb.norm_nonneg
  positivity

variable {N : ℕ} [NeZero N]

/-- Nodal samples `f(x/N)`. -/
def samp {F : Type*} [NormedAddCommGroup F] (N : ℕ) (f : C(UnitAddTorus (Fin 4), F)) :
    Grid N → F := fun x => f (TorusCellEmbedding.samplePt x)

/-- **The sampled test jet** `J_h(x) = (k, δ⁺k, a, η, ψ, δ⁺ψ, ψ̄, δ⁺ψ̄)(x)`. -/
def sampleJet (N : ℕ) [NeZero N] (τ : DTest 𝔄 𝓗 𝓢 W') (x : Grid N) : Jet 𝔄 𝓗 𝓢 W' :=
  (samp N τ.k.f x, fun lam => fwdDiff (N : ℝ)⁻¹ lam (samp N τ.k.f) x, samp N τ.a.f x,
    samp N τ.η.f x, samp N τ.ψ.f x, fun lam => fwdDiff (N : ℝ)⁻¹ lam (samp N τ.ψ.f) x,
    samp N τ.ψb.f x, fun lam => fwdDiff (N : ℝ)⁻¹ lam (samp N τ.ψb.f) x)

/-- **The nodal test record** `𝓘_h v`: the symmetric coframe lift of the inverse-metric test and
the nodal samples of the other tests (the co-spinor test read through the frame `κ`). -/
def testRec (N : ℕ) [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W') :
    Grid N → Field 𝔄 𝓗 𝓢 := fun x =>
  ((NativeGravityFirstJet.liftM (coframe y x) (τ.k.f (TorusCellEmbedding.samplePt x)) : Mat),
    samp N τ.a.f x, samp N τ.η.f x,
    samp N τ.ψ.f x, κ (samp N τ.ψb.f x))

/-- The first differences `(δ⁺Ψ, δ⁺χ)` of a record with co-spinor frame field `χ`. -/
def difs (y : Grid N → Field 𝔄 𝓗 𝓢) (χ : Grid N → W') (x : Grid N) : Dif 𝓢 W' :=
  (fun μ => fwdDiff (N : ℝ)⁻¹ μ (psi y) x, fun μ => fwdDiff (N : ℝ)⁻¹ μ χ x)

end Tests

/-! ### The nodal identity -/

section NodalIdentity

variable {N : ℕ} [NeZero N]

theorem hN_ne : (N : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne N))

theorem shift_eq_add_fwdDiff {V : Type*} [AddCommGroup V] [Module ℝ V] (u : Grid N → V)
    (x : Grid N) (μ : Fin 4) :
    u (x + unitVec N μ) = u x + (N : ℝ)⁻¹ • fwdDiff (N : ℝ)⁻¹ μ u x := by
  simp only [ShiftedJetAction.fwdDiff, smul_smul, mul_inv_cancel₀ (hN_ne (N := N)), one_smul,
    add_sub_cancel]

theorem fwdDiff_clm {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (L : V →L[ℝ] V') (h : ℝ) (u : Grid N → V)
    (x : Grid N) (μ : Fin 4) : fwdDiff h μ (fun z => L (u z)) x = L (fwdDiff h μ u x) := by
  simp only [ShiftedJetAction.fwdDiff, map_smul, map_sub]

theorem volVar_eq (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W') (x : Grid N) :
    volVar y (testRec κ N y τ) x = (gridSlots D y x).dv (sampleJet N τ x) := rfl

theorem gammaVar_eq (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W') (x : Grid N) (μ : Fin 4) :
    gammaVar D y (testRec κ N y τ) x μ = (gridSlots (W' := W') D y x).dγ μ (sampleJet N τ x) :=
  rfl

end NodalIdentity

section NodalIdentity2

variable {N : ℕ} [NeZero N]

theorem δωL_apply (e : M4) (eP q : Fin 4 → M4) (μ : Fin 4) (t : Jet 𝔄 𝓗 𝓢 W') :
    δωL e eP q μ t = ∑ lam, ∑ i, ∑ j, (DεL e eP q lam t i j • omegaCoef μ lam i j e +
      q lam i j • fderiv ℝ (omegaCoef μ lam i j) e (εL e t)) := by
  simp only [δωL, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  rfl

theorem DεL_sampleJet (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W') (x : Grid N)
    (lam : Fin 4) :
    DεL (coframeM y x) (fun lam => coframeM y (x + unitVec N lam)) (fun lam => qM y lam x) lam
      (sampleJet N τ x) = fwdDiff (N : ℝ)⁻¹ lam (coframe (testRec κ N y τ)) x := by
  have h := NativeGravityFirstJet.fwdDiff_lift (hN_ne (N := N)) (coframe y)
    (fun z => (τ.k.f (TorusCellEmbedding.samplePt z) : Mat)) lam x
  simp only [DεL, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, NativeGravityFirstJet.liftL_apply, NativeGravityFirstJet.dqLiftL_apply,
    πdk_apply, πk_apply, ContinuousLinearMap.proj_apply]
  exact h.symm

theorem εL_sampleJet (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W') (x : Grid N) :
    εL (coframeM y x) (sampleJet N τ x) = coframeM (testRec κ N y τ) x := rfl

/-- The variation of the coframe-derived connection along the nodal test record is the slot
operator `δωL` applied to the sampled jet. -/
theorem omegaVar_eq_δωL (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W') (x : Grid N)
    (μ : Fin 4) (hx : (coframe y x).det ≠ 0) :
    asM4 (omegaVar (N : ℝ)⁻¹ y (testRec κ N y τ) x μ) =
      δωL (coframeM y x) (fun lam => coframeM y (x + unitVec N lam)) (fun lam => qM y lam x) μ
        (sampleJet N τ x) := by
  rw [omegaVar_eq_sum _ _ _ x μ hx, δωL_apply]
  refine Finset.sum_congr rfl fun lam _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  rw [DεL_sampleJet κ y τ x lam, εL_sampleJet κ y τ x]
  rfl

theorem wLVar_eq (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W') (x : Grid N) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    wLVar D (N : ℝ)⁻¹ y (testRec κ N y τ) x μ =
      (gridSlots D y x).dWl μ (sampleJet N τ x) := by
  have hω : D.σ (omegaVar (N : ℝ)⁻¹ y (testRec κ N y τ) x μ) =
      σL D (δωL (coframeM y x) (fun lam => coframeM y (x + unitVec N lam))
        (fun lam => qM y lam x) μ (sampleJet N τ x)) := by
    rw [← omegaVar_eq_δωL κ y τ x μ hx]
    rfl
  simp only [wLVar, spinLinkVar, gridSlots, δWL, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, mulRight_apply, mulLeft_apply,
    ContinuousLinearMap.proj_apply, πa_apply, hω, map_smul, ρS_exp_smul]
  simp only [smul_add, mul_smul_comm, smul_mul_assoc, smul_smul,
    inv_mul_cancel₀ (hN_ne (N := N)), one_smul]
  rfl

theorem wRVar_eq (y : Grid N → Field 𝔄 𝓗 𝓢) (τ : DTest 𝔄 𝓗 𝓢 W') (x : Grid N) (μ : Fin 4)
    (hx : (coframe y x).det ≠ 0) :
    wRVar D (N : ℝ)⁻¹ y (testRec κ N y τ) x μ =
      (gridSlots D y x).dWr μ (sampleJet N τ x) := by
  have hω : D.σ (omegaVar (N : ℝ)⁻¹ y (testRec κ N y τ) x μ) =
      σL D (δωL (coframeM y x) (fun lam => coframeM y (x + unitVec N lam))
        (fun lam => qM y lam x) μ (sampleJet N τ x)) := by
    rw [← omegaVar_eq_δωL κ y τ x μ hx]
    rfl
  simp only [wRVar, spinLinkInvVar, gridSlots, δWRL, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, mulRight_apply, mulLeft_apply,
    ContinuousLinearMap.proj_apply, πa_apply, hω, ContinuousLinearMap.neg_apply, map_neg,
    map_smul, ← smul_neg]
  simp only [smul_add, mul_smul_comm, smul_mul_assoc, smul_smul,
    inv_mul_cancel₀ (hN_ne (N := N)), one_smul, neg_mul, mul_neg]
  rfl

end NodalIdentity2

section NodalIdentity3

variable {N : ℕ} [NeZero N]

theorem spin_mul_apply (A B : Spin 𝓢) (w : 𝓢) : (A * B) w = A (B w) := rfl

theorem sum3_aux (a b c : Fin 4 → ℝ) (m1 m2 m3 : ℝ) :
    ((∑ μ, a μ) - m1) + ((∑ μ, b μ) - m2) + ((∑ μ, c μ) - m3) =
      (∑ μ, (a μ + b μ + c μ)) - (m1 + m2 + m3) := by
  simp only [Finset.sum_add_distrib]; ring

theorem sum2_aux (a b : Fin 4 → ℝ) (m : ℝ) :
    ((∑ μ, a μ) - m) + ∑ μ, b μ = (∑ μ, (a μ + b μ)) - m := by
  simp only [Finset.sum_add_distrib]; ring

/-- **The nodal identity**: at every node, the three parts of the exact finite first variation
along the nodal test record equal the value-paired field `G` at the sampled test jet plus the
difference-paired field `Λ` at the sampled jet and the field differences. -/
theorem nodal_identity (y : Grid N → Field 𝔄 𝓗 𝓢) (χ : Grid N → W')
    (hχ : psiBar y = fun z => κ (χ z)) (τ : DTest 𝔄 𝓗 𝓢 W') (x : Grid N)
    (hx : (coframe y x).det ≠ 0) :
    formDens (N : ℝ)⁻¹ (varCoef D (N : ℝ)⁻¹ y (testRec κ N y τ)) (psiBar y) (psi y) x +
        formDens (N : ℝ)⁻¹ (origCoef D (N : ℝ)⁻¹ y) (psiBar (testRec κ N y τ)) (psi y) x +
        formDens (N : ℝ)⁻¹ (origCoef D (N : ℝ)⁻¹ y) (psiBar y) (psi (testRec κ N y τ)) x =
      Gfun D κ (gridSlots D y x) (sampleJet N τ x) +
        Λfun κ (gridSlots D y x) (sampleJet N τ x) (difs y χ x) := by
  set S : Slots 𝔄 𝓗 𝓢 W' := gridSlots D y x with hS
  set t : Jet 𝔄 𝓗 𝓢 W' := sampleJet N τ x with ht
  set u : Dif 𝓢 W' := difs y χ x with hu
  have eW : ∀ μ, wLVar D (N : ℝ)⁻¹ y (testRec κ N y τ) x μ = S.dWl μ t :=
    fun μ => wLVar_eq D κ y τ x μ hx
  have eW' : ∀ μ, wRVar D (N : ℝ)⁻¹ y (testRec κ N y τ) x μ = S.dWr μ t :=
    fun μ => wRVar_eq D κ y τ x μ hx
  have eγv : ∀ μ, gammaVar D y (testRec κ N y τ) x μ = S.dγ μ t := fun μ => rfl
  have evv : volVar y (testRec κ N y τ) x = S.dv t := rfl
  have ev : volume (coframe y x) = S.v := rfl
  have eγ : ∀ μ, gammaMu D μ (coframe y x) = S.γ μ := fun μ => rfl
  have eWl : ∀ μ, wL D (N : ℝ)⁻¹ y x μ = S.Wl μ := fun μ => rfl
  have eWr : ∀ μ, wR D (N : ℝ)⁻¹ y x μ = S.Wr μ := fun μ => rfl
  have eY : D.yukawa (higgs y x) = S.YH := rfl
  have eYt : higgs (testRec κ N y τ) x = t.2.2.2.1 := rfl
  have eΨ : psi y x = S.Ψ := rfl
  have eΨp : ∀ μ, psi y (x + unitVec N μ) = S.Ψp μ := fun μ => rfl
  have eΨb : psiBar y x = S.Ψb := rfl
  have eΨbp : ∀ μ, psiBar y (x + unitVec N μ) = S.Ψbp μ := fun μ => rfl
  have eDΨ : ∀ μ, fwdDiff (N : ℝ)⁻¹ μ (psi y) x = u.1 μ := fun μ => rfl
  have eDΨb : ∀ μ, fwdDiff (N : ℝ)⁻¹ μ (psiBar y) x = κ (u.2 μ) := fun μ => by
    rw [hχ]; exact fwdDiff_clm κ _ χ x μ
  have eψ : psi (testRec κ N y τ) x = t.2.2.2.2.1 := rfl
  have eDψ : ∀ μ, fwdDiff (N : ℝ)⁻¹ μ (psi (testRec κ N y τ)) x = t.2.2.2.2.2.1 μ :=
    fun μ => rfl
  have eψp : ∀ μ, psi (testRec κ N y τ) (x + unitVec N μ) =
      t.2.2.2.2.1 + (N : ℝ)⁻¹ • t.2.2.2.2.2.1 μ := fun μ =>
    shift_eq_add_fwdDiff (psi (testRec κ N y τ)) x μ
  have eψb : psiBar (testRec κ N y τ) x = κ t.2.2.2.2.2.2.1 := rfl
  have eDψb : ∀ μ, fwdDiff (N : ℝ)⁻¹ μ (psiBar (testRec κ N y τ)) x =
      κ (t.2.2.2.2.2.2.2 μ) := fun μ => fwdDiff_clm κ _ (samp N τ.ψb.f) x μ
  have eψbp : ∀ μ, psiBar (testRec κ N y τ) (x + unitVec N μ) =
      κ t.2.2.2.2.2.2.1 + (N : ℝ)⁻¹ • κ (t.2.2.2.2.2.2.2 μ) := fun μ => by
    rw [shift_eq_add_fwdDiff (psiBar (testRec κ N y τ)) x μ, eDψb μ]; rfl
  have eh : (N : ℝ)⁻¹ = S.h := rfl
  simp only [formDens, Gfun, Λfun]
  rw [sum3_aux, sum2_aux]
  congr 1
  · refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [varCoef, origCoef, eW, eW', eγv, evv, ev, eγ, eWl, eWr, eΨ, eΨp, eΨb, eΨbp, eDΨ,
      eDΨb, eψ, eDψ, eψp, eψb, eDψb, eψbp]
    simp only [eh, Gμ, Λμ, bI, map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,
      spin_mul_apply, smul_eq_mul]
    ring
  · simp only [varCoef, origCoef, evv, ev, eΨ, eΨb, eψ, eψb, eY, eYt]
    simp only [G0, bR, map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]

end NodalIdentity3


end

end RenewalGeometry.NativeDiracLimit
