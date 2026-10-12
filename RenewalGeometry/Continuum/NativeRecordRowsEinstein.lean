/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeRecordRowsGauge
import MathPhys.FieldTheory.Continuum.RicciJetSymmetry
open MathPhys

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
open MathPhys.RecordTuple

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
