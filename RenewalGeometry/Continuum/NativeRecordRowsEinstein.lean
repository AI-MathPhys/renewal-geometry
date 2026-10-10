/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeRecordRowsGauge

/-!
# The Einstein residual of the actual tuple of a native field

Einstein–Standard-Model action-closure manuscript, `thm:native-closure`, bridge step P2
(gravitational row).  For a native field satisfying `RecordTuple.TupleHyp`:

* `ricci_symm`, `einstein_symm` (generic) — the Ricci and Einstein tensors of a metric 2-jet with
  symmetric jets are symmetric;
* `lower_raise` — lowering the raised indices with the metric of a coframe is the identity;
* **`Tact_toTuple`** — the complete off-shell stress of the tuple (slab theory data
  `SlabData.toSMData`) is the lowered symmetric part of the native stress
  `NativeStressEuler.smStressUp`;
* **`Etr_toTuple`** — the trace-reversed Einstein residual of the tuple is
  `traceRev(g, g⁻¹, lower(sym 𝓔))` with the native Einstein residual
  `𝓔^{ab} = NativeStressEuler.einsteinRes` (`G^{ab} + Λg^{ab} - κT_{SM}^{ab}`), and
  `sym 𝓔^{cd} = -(κ/v) 𝓔₀(Y)[(S_{cd}e, 0)]` with the metric directions `S_{cd}` of
  `NativeStressEuler.metricS` (`einsteinRes_sym_row`).
-/

open Finset
open scoped Matrix

namespace RenewalGeometry.RecordTuple

open SobolevOpen (pd)
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open NativeScaling (Mat eta metric readerOmega readerG)
open NativeDensity NativeModel NativeFrameBridge NativeBosonicEuler NativeDiracEuler PalatiniEuler
open ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetFrame SlabData SpinorProlongation
open HarmonicDefect

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Symmetry of the Ricci tensor of a metric 2-jet -/

section RicciSymm

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {gi : n → n → ℝ} {dg : n → n → n → ℝ} {ddg : n → n → n → n → ℝ}

/-- Reversal of four nested finite sums. -/
theorem sum4_rev (F : n → n → n → n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ b, ∑ d, ∑ c, F a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, F a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ c, ∑ b, F a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ c, ∑ b, F a b c d := Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ a, ∑ b, F a b c d := Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem chr_symm' (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (l μ ν : n) :
    chr gi dg l μ ν = chr gi dg l ν μ := by
  unfold chr
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hdg σ μ ν]; ring

theorem dchr_symm' (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (hddg : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ) (α l μ ν : n) :
    dchr gi dg ddg α l μ ν = dchr gi dg ddg α l ν μ := by
  unfold dchr dchr1 dchr2
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hdg σ μ ν]; ring
  · congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hddg α σ μ ν]; ring

theorem dginv_symm' (hgi : ∀ a b, gi a b = gi b a) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (α l σ : n) : dginv gi dg α l σ = dginv gi dg α σ l := by
  unfold dginv
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hgi l b, hgi a σ, hdg α b a]; ring

/-- `Σ_α ∂_νΓ^α_{μα}` is symmetric in `μ, ν` for symmetric jets (`Γ^α_{μα} = ½∂_μ log|g|`). -/
theorem sum_dchr_trace_symm (hgi : ∀ a b, gi a b = gi b a) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (hddg1 : ∀ α β μ ν, ddg α β μ ν = ddg β α μ ν) (hddg2 : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ)
    (μ ν : n) : ∑ α, dchr gi dg ddg ν α μ α = ∑ α, dchr gi dg ddg μ α ν α := by
  -- reduce both sides to the trace forms
  have key : ∀ μ ν, ∑ α, dchr gi dg ddg ν α μ α =
      (1 / 2) * ∑ α, ∑ σ, dginv gi dg ν α σ * dg μ σ α +
        (1 / 2) * ∑ α, ∑ σ, gi α σ * ddg ν μ σ α := by
    intro μ ν
    have h1 : ∑ α, ∑ σ, dginv gi dg ν α σ * (dg μ σ α + dg α σ μ - dg σ μ α) =
        ∑ α, ∑ σ, dginv gi dg ν α σ * dg μ σ α := by
      have h0 : ∑ α, ∑ σ, dginv gi dg ν α σ * (dg α σ μ - dg σ α μ) = 0 := by
        have hs : ∑ α, ∑ σ, dginv gi dg ν α σ * dg α σ μ =
            ∑ α, ∑ σ, dginv gi dg ν α σ * dg σ α μ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [dginv_symm' hgi hdg]
        simp only [mul_sub, Finset.sum_sub_distrib, hs, sub_self]
      have h2 : ∀ α σ, dg σ μ α = dg σ α μ := fun α σ => hdg σ μ α
      calc ∑ α, ∑ σ, dginv gi dg ν α σ * (dg μ σ α + dg α σ μ - dg σ μ α)
          = ∑ α, ∑ σ, dginv gi dg ν α σ * dg μ σ α +
              ∑ α, ∑ σ, dginv gi dg ν α σ * (dg α σ μ - dg σ α μ) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun α _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [h2]; ring
        _ = _ := by rw [h0, add_zero]
    have h3 : ∑ α, ∑ σ, gi α σ * (ddg ν μ σ α + ddg ν α σ μ - ddg ν σ μ α) =
        ∑ α, ∑ σ, gi α σ * ddg ν μ σ α := by
      have h0 : ∑ α, ∑ σ, gi α σ * (ddg ν α σ μ - ddg ν σ α μ) = 0 := by
        have hs : ∑ α, ∑ σ, gi α σ * ddg ν α σ μ = ∑ α, ∑ σ, gi α σ * ddg ν σ α μ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [hgi a b]
        simp only [mul_sub, Finset.sum_sub_distrib, hs, sub_self]
      calc ∑ α, ∑ σ, gi α σ * (ddg ν μ σ α + ddg ν α σ μ - ddg ν σ μ α)
          = ∑ α, ∑ σ, gi α σ * ddg ν μ σ α +
              ∑ α, ∑ σ, gi α σ * (ddg ν α σ μ - ddg ν σ α μ) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun α _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [hddg2 ν σ μ α]; ring
        _ = _ := by rw [h0, add_zero]
    unfold dchr dchr1 dchr2
    rw [Finset.sum_add_distrib]
    simp only [← Finset.mul_sum]
    rw [h1, h3]
  rw [key μ ν, key ν μ]
  congr 1
  · congr 1
    -- `Σ dginv_ν g' dg_μ = -tr(g⁻¹∂_νg g⁻¹∂_μg)` is symmetric
    unfold dginv
    simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
    congr 1
    -- both sides are the same quadruple sum after relabelling
    rw [sum4_rev]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun α _ => ?_
    ring
  · congr 1
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [hddg1 ν μ σ α]

/-- **The Ricci tensor of a metric 2-jet with symmetric jets is symmetric.** -/
theorem ricci_symm (hgi : ∀ a b, gi a b = gi b a) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (hddg1 : ∀ α β μ ν, ddg α β μ ν = ddg β α μ ν) (hddg2 : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ)
    (μ ν : n) : ricci gi dg ddg μ ν = ricci gi dg ddg ν μ := by
  unfold ricci ricciJ
  have h1 : ∑ α, dchr gi dg ddg α α μ ν = ∑ α, dchr gi dg ddg α α ν μ :=
    Finset.sum_congr rfl fun α _ => dchr_symm' hdg hddg2 α α μ ν
  have h2 := sum_dchr_trace_symm hgi hdg hddg1 hddg2 μ ν
  have h3 : ∑ α, ∑ l, chr gi dg α α l * chr gi dg l μ ν =
      ∑ α, ∑ l, chr gi dg α α l * chr gi dg l ν μ :=
    Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun l _ => by rw [chr_symm' hdg l μ ν]
  have h4 : ∑ α, ∑ l, chr gi dg α ν l * chr gi dg l μ α =
      ∑ α, ∑ l, chr gi dg α μ l * chr gi dg l ν α := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [h1, h2, h3, h4]

/-- **The Einstein tensor of a metric 2-jet with symmetric jets is symmetric.** -/
theorem einstein_symm {g : n → n → ℝ} (hg : ∀ a b, g a b = g b a) (hgi : ∀ a b, gi a b = gi b a)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (hddg1 : ∀ α β μ ν, ddg α β μ ν = ddg β α μ ν)
    (hddg2 : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ) (μ ν : n) :
    einstein g gi dg ddg μ ν = einstein g gi dg ddg ν μ := by
  unfold einstein
  rw [ricci_symm hgi hdg hddg1 hddg2 μ ν, hg μ ν]

end RicciSymm

/-! ### Lowering indices with the metric of a coframe -/

/-- Lowered indices `T_{ab} = g_{ac}g_{bd}T^{cd}`, `g = eᵀηe`. -/
def lowerE (E : Mat) (T : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) : ℝ :=
  ∑ c, ∑ d, metric E a c * metric E b d * T c d

theorem lowerE_add (E : Mat) (T T' : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    lowerE E (fun c d => T c d + T' c d) a b = lowerE E T a b + lowerE E T' a b := by
  unfold lowerE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

theorem lowerE_smul (E : Mat) (r : ℝ) (T : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    lowerE E (fun c d => r * T c d) a b = r * lowerE E T a b := by
  unfold lowerE
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

theorem lowerE_symm (E : Mat) (T : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    lowerE E (fun c d => T d c) a b = lowerE E T b a := by
  unfold lowerE
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

/-- **Lowering the raised indices is the identity.** -/
theorem lowerE_raise {E : Mat} (hE : E.det ≠ 0) (T : Fin 4 → Fin 4 → ℝ) :
    lowerE E (NativeStressEuler.raise E T) = T := by
  funext a b
  unfold lowerE NativeStressEuler.raise
  have hδ := NativeStressEuler.sum_metric_ginv hE
  calc ∑ c, ∑ d, metric E a c * metric E b d * ∑ μ, ∑ ν, ginv E c μ * ginv E d ν * T μ ν
      = ∑ μ, ∑ ν, (∑ c, metric E a c * ginv E c μ) * (∑ d, metric E b d * ginv E d ν) * T μ ν := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [NativeStressEuler.sum4_swap]
        refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        ring
    _ = T a b := by simp [hδ]

end

end RenewalGeometry.RecordTuple
