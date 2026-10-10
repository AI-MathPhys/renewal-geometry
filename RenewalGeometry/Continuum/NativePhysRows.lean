/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeFieldScaling
import RenewalGeometry.Continuum.NativeTailTransferBounds

/-!
# The physical (gauge-Lie) Euler rows of the native action

Einstein–Standard-Model action-closure manuscript, `thm:native-source`, `thm:native-closure` and
their dependents: the gauge potential of the native field and its **test directions live in the
gauge Lie algebra `𝔤`**, not in the ambient associative algebra `𝔄` that carries the lattice links
`e^{hA}` and the representations.  The native field space `Field = Mat × (Fin 4 → 𝔄) × 𝓗 × 𝓢 × 𝓢̄`
keeps `𝔄` as the ambient value space; the **physical** Euler rows are the native Euler covector
restricted to the physical directions.  Given any continuous linear map `P_𝔤 : 𝔄 → 𝔄` (for a slab
model: the `⟨·,·⟩_𝐠`-orthogonal projection onto `𝔤`, `SlabData.SlabModel.πg`):

* `gaugeProjB P_𝔤` — `(δe, δA, δH) ↦ (δe, P_𝔤 ∘ δA, δH)` on bosonic directions;
* `physF P_𝔤` — `(δe, δA, δH, δΨ, δΨ̄) ↦ (δe, P_𝔤 ∘ δA, δH, δΨ, δΨ̄)` on all directions;
* **`RBP D P_𝔤 Y = 𝓡_B(Y) ∘ gaugeProjB P_𝔤`** — the physical bosonic residual map (Einstein and
  Higgs rows unchanged, Yang–Mills rows tested only along `range P_𝔤`); the Dirac residual map
  `𝓡_D` is unchanged (`RD_eq_phys`).

For a projection `P_𝔤` onto `𝔤` a covector `ρ` vanishes on the physical directions iff
`ρ ∘ physF P_𝔤 = 0`, and `‖ρ ∘ physF P_𝔤‖` is equivalent to the norm of the restriction of `ρ` to
the physical directions; so the budgets built from `ρ ∘ physF P_𝔤` are the manuscript's budgets
(gauge rows in `𝔤` only).  This corrects the earlier encoding, in which the Euler rows were
imposed in every direction of `𝔄 ≅ gl(m)`, including the unit, whose row `-2v g^{σν}⟨H, ∂_νH⟩` is
absent from the manuscript (`CalibrationBackreacting.unit_gauge_row`).

Results: `RBP_eq` / `RD_eq_phys` (both rows factor through `𝓔₀ ∘ physF`), `contDiff_RBP`,
`isPeriodic_RBP`, `RBP_dilate` (behaviour under the dilation of slab coordinates), `RBP_id`
(`P_𝔤 = id` gives back `𝓡_B`).
-/

open Finset
open scoped ContDiff

namespace RenewalGeometry.NativeTail

open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity IsPeriodic)
open NativeScaling (Mat)
open NativeDensity FieldScaling
open ContEulerBounds (NCLM JS preL)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- The gauge projection acting on the four gauge slots, `X ↦ (μ ↦ P_𝔤 X_μ)`. -/
def gaugeSlots (Pg : 𝔄 →L[ℝ] 𝔄) : NCLM (Fin 4 → 𝔄) (Fin 4 → 𝔄) :=
  ContinuousLinearMap.pi fun μ => Pg.comp (ContinuousLinearMap.proj μ)

theorem gaugeSlots_apply (Pg : 𝔄 →L[ℝ] 𝔄) (X : Fin 4 → 𝔄) (μ : Fin 4) :
    gaugeSlots Pg X μ = Pg (X μ) := rfl

/-- **The physical bosonic directions**: `(δe, δA, δH) ↦ (δe, P_𝔤 ∘ δA, δH)`. -/
def gaugeProjB (Pg : 𝔄 →L[ℝ] 𝔄) : NCLM (Mat × (Fin 4 → 𝔄) × 𝓗) (Mat × (Fin 4 → 𝔄) × 𝓗) :=
  (ContinuousLinearMap.id ℝ Mat).prodMap
    ((gaugeSlots Pg).prodMap (ContinuousLinearMap.id ℝ 𝓗))

theorem gaugeProjB_apply (Pg : 𝔄 →L[ℝ] 𝔄) (v : Mat × (Fin 4 → 𝔄) × 𝓗) :
    gaugeProjB Pg v = (v.1, gaugeSlots Pg v.2.1, v.2.2) := rfl

/-- **The physical field directions**: `(δe, δA, δH, δΨ, δΨ̄) ↦ (δe, P_𝔤 ∘ δA, δH, δΨ, δΨ̄)`. -/
def physF (Pg : 𝔄 →L[ℝ] 𝔄) : NCLM (Field 𝔄 𝓗 𝓢) (Field 𝔄 𝓗 𝓢) :=
  (ContinuousLinearMap.id ℝ Mat).prodMap
    ((gaugeSlots Pg).prodMap (ContinuousLinearMap.id ℝ (𝓗 × 𝓢 × CoSpinor 𝓢)))

theorem physF_apply (Pg : 𝔄 →L[ℝ] 𝔄) (w : Field 𝔄 𝓗 𝓢) :
    physF Pg w = (w.1, gaugeSlots Pg w.2.1, w.2.2) := rfl

theorem physF_ιB_apply (Pg : 𝔄 →L[ℝ] 𝔄) (v : Mat × (Fin 4 → 𝔄) × 𝓗) :
    physF (𝓢 := 𝓢) Pg (ιB v) = ιB (gaugeProjB Pg v) := rfl

theorem physF_ιS_apply (Pg : 𝔄 →L[ℝ] 𝔄) (v : 𝓢 × CoSpinor 𝓢) :
    physF (𝓗 := 𝓗) Pg (ιS v) = ιS v := by
  rw [physF_apply, ιS_apply]
  have h0 : gaugeSlots Pg (0 : Fin 4 → 𝔄) = 0 := map_zero _
  simp only [h0]

theorem gaugeSlots_single (Pg : 𝔄 →L[ℝ] 𝔄) (ν : Fin 4) (y : 𝔄) :
    gaugeSlots Pg (Pi.single ν y) = Pi.single ν (Pg y) := by
  funext μ
  rw [gaugeSlots_apply]
  by_cases h : μ = ν
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem gaugeProjB_coframe (Pg : 𝔄 →L[ℝ] 𝔄) (k : Mat) :
    gaugeProjB (𝓗 := 𝓗) Pg (k, 0, 0) = (k, 0, 0) := by
  rw [gaugeProjB_apply]
  have h0 : gaugeSlots Pg (0 : Fin 4 → 𝔄) = 0 := map_zero _
  simp only [h0]

theorem gaugeProjB_higgs (Pg : 𝔄 →L[ℝ] 𝔄) (η : 𝓗) :
    gaugeProjB Pg ((0 : Mat), (0 : Fin 4 → 𝔄), η) = (0, 0, η) := by
  rw [gaugeProjB_apply]
  have h0 : gaugeSlots Pg (0 : Fin 4 → 𝔄) = 0 := map_zero _
  simp only [h0]

theorem gaugeProjB_gauge (Pg : 𝔄 →L[ℝ] 𝔄) (X : Fin 4 → 𝔄) :
    gaugeProjB (𝓗 := 𝓗) Pg ((0 : Mat), X, 0) = (0, gaugeSlots Pg X, 0) := rfl

/-- **The physical bosonic residual map** `𝓡_B^𝔤(Y) = 𝓡_B(Y) ∘ gaugeProjB P_𝔤`: Einstein and Higgs
rows, Yang–Mills rows tested along `P_𝔤`. -/
def RBP (Pg : 𝔄 →L[ℝ] 𝔄) (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) :
    NCLM (Mat × (Fin 4 → 𝔄) × 𝓗) ℝ :=
  (RB D Y x).comp (gaugeProjB Pg)

theorem RBP_apply (Pg : 𝔄 →L[ℝ] 𝔄) (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4)
    (v : Mat × (Fin 4 → 𝔄) × 𝓗) : RBP D Pg Y x v = RB D Y x (gaugeProjB Pg v) := rfl

theorem RBP_fun (Pg : 𝔄 →L[ℝ] 𝔄) (Y : R4 → Field 𝔄 𝓗 𝓢) :
    RBP D Pg Y = fun x => preL (gaugeProjB Pg) (RB D Y x) := rfl

/-- The physical bosonic rows factor through the physical Euler covector `𝓔₀ ∘ physF`. -/
theorem RBP_eq (Pg : 𝔄 →L[ℝ] 𝔄) (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) :
    RBP D Pg Y x = ((Rfull D Y x).comp (physF Pg)).comp ιB :=
  ContinuousLinearMap.ext fun _ => rfl

/-- The Dirac rows factor through the physical Euler covector `𝓔₀ ∘ physF`. -/
theorem RD_eq_phys (Pg : 𝔄 →L[ℝ] 𝔄) (Y : R4 → Field 𝔄 𝓗 𝓢) (x : R4) :
    RD D Y x = ((Rfull D Y x).comp (physF Pg)).comp ιS := by
  refine ContinuousLinearMap.ext fun v => ?_
  show Rfull D Y x (ιS v) = Rfull D Y x (physF Pg (ιS v))
  rw [physF_ιS_apply]

theorem RBP_id (Y : R4 → Field 𝔄 𝓗 𝓢) :
    RBP D (ContinuousLinearMap.id ℝ 𝔄) Y = RB D Y := by
  funext x
  exact ContinuousLinearMap.ext fun _ => rfl

theorem physF_id : physF (𝓗 := 𝓗) (𝓢 := 𝓢) (ContinuousLinearMap.id ℝ 𝔄) =
    ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext fun _ => rfl

/-- The physical rows of a vanishing Euler covector vanish. -/
theorem RBP_eq_zero_of {Pg : 𝔄 →L[ℝ] 𝔄} {Y : R4 → Field 𝔄 𝓗 𝓢} {x : R4}
    (h : (Rfull D Y x).comp (physF Pg) = 0) : RBP D Pg Y x = 0 := by
  rw [RBP_eq, h, ContinuousLinearMap.zero_comp]

theorem RD_eq_zero_of {Pg : 𝔄 →L[ℝ] 𝔄} {Y : R4 → Field 𝔄 𝓗 𝓢} {x : R4}
    (h : (Rfull D Y x).comp (physF Pg) = 0) : RD D Y x = 0 := by
  rw [RD_eq_phys D Pg, h, ContinuousLinearMap.zero_comp]

theorem contDiff_RBP (Pg : 𝔄 →L[ℝ] 𝔄) {K : ℝ} (hK : 0 < K) {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hY : ContDiff ℝ ∞ Y) (hch : ∀ ξ, ((K⁻¹, jet1 (resc K Y) ξ) : ℝ × JS (Field 𝔄 𝓗 𝓢)) ∈ chartU) :
    ContDiff ℝ ∞ (RBP D Pg Y) := by
  exact (contDiff_RB D hK hY hch).clm_comp contDiff_const

theorem isPeriodic_RBP (Pg : 𝔄 →L[ℝ] 𝔄) {L : ℝ} {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hRB : IsPeriodic L (RB D Y)) : IsPeriodic L (RBP D Pg Y) := fun z μ => by
  rw [RBP_fun]
  simp only [hRB z μ]

theorem gaugeProjB_bosScaleInv (Pg : 𝔄 →L[ℝ] 𝔄) (lam : ℝ) (v : Mat × (Fin 4 → 𝔄) × 𝓗) :
    bosScaleInv lam (gaugeProjB Pg v) = gaugeProjB Pg (bosScaleInv lam v) := by
  rw [bosScaleInv_apply, gaugeProjB_apply, gaugeProjB_apply, bosScaleInv_apply, map_smul]

/-- **The physical bosonic residual map under the dilation**:
`𝓡_B^𝔤(Ỹ)(x) = λ⁴ 𝓡_B^𝔤(Y)(λx + c) ∘ Φ_{B,λ}⁻¹`. -/
theorem RBP_dilate (Pg : 𝔄 →L[ℝ] 𝔄) {lam : ℝ} (hlam : lam ≠ 0) (hlam0 : 0 < lam) (c : R4)
    {Y : R4 → Field 𝔄 𝓗 𝓢} (hdet : ∀ z, 0 < (Y z).1.det) (x : R4) :
    RBP D Pg (dilateF (fieldScale hlam) lam c Y) x =
      lam ^ 4 • (RBP D Pg Y (lam • x + c)).comp (bosScaleInv lam) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h := gaugeProjB_bosScaleInv Pg lam v
  have hR := congrArg (fun T : NCLM (Mat × (Fin 4 → 𝔄) × 𝓗) ℝ => T (gaugeProjB Pg v))
    (RB_dilate D hlam hlam0 c hdet x)
  refine hR.trans ?_
  change lam ^ 4 • RB D Y (lam • x + c) (bosScaleInv lam (gaugeProjB Pg v)) =
    lam ^ 4 • RB D Y (lam • x + c) (gaugeProjB Pg (bosScaleInv lam v))
  rw [h]

end

end RenewalGeometry.NativeTail
