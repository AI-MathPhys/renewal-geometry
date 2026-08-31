/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.PairLocalityIndependentExact

/-!
# Route-locality leakage Grams

The positive split leakage Gram is represented by its quadratic form. This
is the exact data needed for positivity, the almost-everywhere zero
criterion, and path-bound control, while avoiding a basis choice in the
finite source space.
-/

open Filter MeasureTheory Set
open scoped Interval
open Matrix

noncomputable section

namespace NCG
namespace RouteLocalityGram

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Quadratic form of the split leakage Gram. The split synthesis S already
contains the outside-collar projection and source synthesis. -/
def splitLeakageEnergy (S : ℝ → E →L[ℂ] F) (t : ℝ) (x : E) : ℝ :=
  ∫ s in (0 : ℝ)..t, ‖S s x‖ ^ 2

/-- Every split leakage Gram is positive. -/
theorem splitLeakageEnergy_nonneg
    (S : ℝ → E →L[ℂ] F) (t : ℝ) (x : E) (ht : 0 ≤ t) :
    0 ≤ splitLeakageEnergy S t x := by
  unfold splitLeakageEnergy
  exact intervalIntegral.integral_nonneg ht fun _ _ => sq_nonneg _

/-- Vanishing of a positive split Gram in one source direction is equivalent
to almost-everywhere vanishing of the corresponding split synthesis. -/
theorem splitLeakageEnergy_eq_zero_iff
    (S : ℝ → E →L[ℂ] F) (t : ℝ) (x : E) (ht : 0 ≤ t)
    (hInt : IntervalIntegrable (fun s => ‖S s x‖ ^ 2) volume 0 t) :
    splitLeakageEnergy S t x = 0 ↔
      (fun s => S s x) =ᵐ[volume.restrict (Ioc 0 t)] 0 := by
  unfold splitLeakageEnergy
  rw [intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae ht
    (Eventually.of_forall fun _ => sq_nonneg _) hInt]
  constructor
  · intro h
    filter_upwards [h] with s hs
    simpa using hs
  · intro h
    filter_upwards [h] with s hs
    simp [hs]

/-- Basis-free zero criterion for the entire split leakage quadratic form. -/
theorem splitLeakageForm_eq_zero_iff
    (S : ℝ → E →L[ℂ] F) (t : ℝ) (ht : 0 ≤ t)
    (hInt : ∀ x, IntervalIntegrable (fun s => ‖S s x‖ ^ 2) volume 0 t) :
    (∀ x, splitLeakageEnergy S t x = 0) ↔
      (∀ x, (fun s => S s x) =ᵐ[volume.restrict (Ioc 0 t)] 0) := by
  constructor <;> intro h x
  · exact (splitLeakageEnergy_eq_zero_iff S t x ht (hInt x)).mp (h x)
  · exact (splitLeakageEnergy_eq_zero_iff S t x ht (hInt x)).mpr (h x)

/-- The split Gram quadratic form is bounded by the integral of the square
of any pointwise operator-norm route bound. -/
theorem splitLeakageEnergy_le_pathIntegral
    (S : ℝ → E →L[ℂ] F) (B : ℝ → ℝ) (t : ℝ) (x : E)
    (ht : 0 ≤ t)
    (hSInt : IntervalIntegrable (fun s => ‖S s x‖ ^ 2) volume 0 t)
    (hBInt : IntervalIntegrable (fun s => B s ^ 2) volume 0 t)
    (hB : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ B s ∧ ‖S s‖ ≤ B s) :
    splitLeakageEnergy S t x
      ≤ ‖x‖ ^ 2 * ∫ s in (0 : ℝ)..t, B s ^ 2 := by
  unfold splitLeakageEnergy
  have hscaled : IntervalIntegrable
      (fun s => ‖x‖ ^ 2 * B s ^ 2) volume 0 t :=
    hBInt.const_mul (‖x‖ ^ 2)
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) ht hSInt hscaled (fun s hs => by
      have happly : ‖S s x‖ ≤ B s * ‖x‖ :=
        (ContinuousLinearMap.le_opNorm _ x).trans
          (mul_le_mul_of_nonneg_right (hB s hs).2 (norm_nonneg x))
      calc
        ‖S s x‖ ^ 2 ≤ (B s * ‖x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) happly 2
        _ = ‖x‖ ^ 2 * B s ^ 2 := by ring)
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

/-- Unit-source form of the route-bound estimate, i.e. the operator-norm
bound for the represented positive Gram. -/
theorem splitLeakageEnergy_unit_le_pathIntegral
    (S : ℝ → E →L[ℂ] F) (B : ℝ → ℝ) (t : ℝ) (x : E)
    (ht : 0 ≤ t) (hx : ‖x‖ ≤ 1)
    (hSInt : IntervalIntegrable (fun s => ‖S s x‖ ^ 2) volume 0 t)
    (hBInt : IntervalIntegrable (fun s => B s ^ 2) volume 0 t)
    (hB : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ B s ∧ ‖S s‖ ≤ B s) :
    splitLeakageEnergy S t x
      ≤ ∫ s in (0 : ℝ)..t, B s ^ 2 := by
  have h := splitLeakageEnergy_le_pathIntegral
    S B t x ht hSInt hBInt hB
  calc
    splitLeakageEnergy S t x
        ≤ ‖x‖ ^ 2 * ∫ s in (0 : ℝ)..t, B s ^ 2 := h
    _ ≤ 1 * ∫ s in (0 : ℝ)..t, B s ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_one₀ (norm_nonneg _) hx)
        (intervalIntegral.integral_nonneg ht fun s hs => sq_nonneg (B s))
    _ = ∫ s in (0 : ℝ)..t, B s ^ 2 := one_mul _

/-- The explicit two-site long-hop packet shows that zero endpoint/first
data do not force route locality. -/
theorem endpoint_zero_does_not_imply_route_zero (N : ℕ) (hN : 0 < N) :
    (∀ t : ℝ,
      star (Pi.single (0 : Fin 2) (1 : ℂ))
        ⬝ᵥ (duhamelFirst 0 longHop t *ᵥ Pi.single 0 1) = 0) ∧
    star (Pi.single (0 : Fin 2) (1 : ℂ))
        ⬝ᵥ (duhamelPair 0 longHop longHop 1 *ᵥ Pi.single 0 1) = 1 ∧
    longHop *ᵥ Pi.single (0 : Fin 2) (1 : ℂ) = Pi.single 1 1 ∧
    PairLocalityIndependent.twoSiteDistance N 0 1 = N ∧
    0 < PairLocalityIndependent.twoSiteDistance N 0 1 :=
  PairLocalityIndependent.pair_locality_is_independent N hN

end RouteLocalityGram
end NCG
