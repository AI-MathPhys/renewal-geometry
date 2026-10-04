/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMSlabRegularity
import RenewalGeometry.Analysis.SobolevBoxCrEmbedding

/-!
# The slab Sobolev class `C_tH^s ∩ C¹_tH^{s-1} ∩ C²_tH^{s-2}` (`cor:strong-solution-upgrade`,
  Einstein–Standard-Model action-closure manuscript)

Rendering: `M = (0,T) × 𝕋³` lifted to `ℝ⁴` (coordinate `0` = time) with spatially periodic fields,
`H^m(𝕋³)` the Fourier Sobolev space of `Analysis/TorusSobolevEmbedding.lean`
(`sobNorm m F = (Σ_n (1 + 4π²|n|²)^m |F̂(n)|²)^{1/2}`), time slices `slice u t = u(t, ·)`.

* `CtH T m u` (`u ∈ C((0,T); H^m(𝕋³))`, with continuous slices), `HasTimeDerivH T m u u'`
  (`∂_t u = u'` in `H^m`: the difference quotients of the slices converge in `H^m`),
  `SlabC2 T s u` (`u ∈ C_tH^s ∩ C¹_tH^{s-1} ∩ C²_tH^{s-2}`), `SlabC1 T s u`
  (`u ∈ C_tH^s ∩ C¹_tH^{s-1}`); vector-valued fields belong to a class when all their real-linear
  scalar components do (`VecSlabC2`, `VecSlabC1`).
* `sD α u`: the spatial derivatives `∂_y^α u(t, y)` computed slice-wise (`fourierDeriv`); joint
  continuity (`continuousOn_sD`), spatial line derivatives (`hasDerivAt_sD_space`), time
  derivatives (`hasDerivAt_sD_time`), `sD 0 u = u` (`sD_zero`).
* **`contDiffOn_two_of_slabC2`** (`s ≥ 5`, in fact `s > 7/2` suffices): `SlabC2 T s u ⇒ u ∈ C²` on
  the open slab; **`contDiffOn_one_of_slabC1`** (`s ≥ 4`): `SlabC1 T s u ⇒ u ∈ C¹`; through
  `PartialC1.contDiffOn_two_of_partials` / `contDiffOn_one_of_partials`.
* `SobolevSlab T s z`: the manuscript's hypothesis of `cor:strong-solution-upgrade`:
  `(e, A, H) ∈ C_tH^s ∩ C¹_tH^{s-1} ∩ C²_tH^{s-2}`, `(Ψ, Ψ̄) ∈ C_tH^{s-1} ∩ C¹_tH^{s-2}`, `s ≥ 5`,
  nondegenerate coframe; **`classicalSlab_of_sobolevSlab`**: it implies `ClassicalSlab`.
* **`strong_solution_upgrade_sobolev`** (`cor:strong-solution-upgrade`): under the hypotheses of
  `thm:reduced-closure`, every subsequence has a further subsequence with a limit such that, if
  the limit lies in the Sobolev class, its distributional Euler identities are strong (pointwise)
  field equations: all second-order bosonic and first-order spinor rows vanish at every point of
  `(0,T) × (0,1)³`; the limit packets are the classical derivatives.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ContDiff ENNReal NNReal Real

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace SlabSob

open SobolevOpen (pd)
open TorusSobolev SlabReg

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The 3-torus. -/
abbrev T3 := UnitAddTorus (Fin 3)

/-! ### Linear combinations of Sobolev functions on `𝕋³` -/

section Lin

theorem integrable_cont (F : C(T3, ℂ)) (n : Fin 3 → ℤ) :
    Integrable fun t => mFourier (-n) t • F t :=
  ((mFourier (-n)).continuous.smul F.continuous).continuousOn.integrableOn_compact isCompact_univ
    |> integrableOn_univ.mp

/-- Fourier coefficients of `c(F - G) - H`. -/
theorem mFourierCoeff_comb (F G H : C(T3, ℂ)) (c : ℂ) (n : Fin 3 → ℤ) :
    mFourierCoeff (fun t => c * (F t - G t) - H t) n =
      c * (mFourierCoeff F n - mFourierCoeff G n) - mFourierCoeff H n := by
  unfold mFourierCoeff
  have e : ∀ t, mFourier (-n) t • (c * (F t - G t) - H t) =
      c * (mFourier (-n) t • F t) - c * (mFourier (-n) t • G t) - mFourier (-n) t • H t := by
    intro t; simp only [smul_eq_mul]; ring
  simp_rw [e]
  have i1 : Integrable (fun t => c * (mFourier (-n) t • F t)) := (integrable_cont F n).const_mul c
  have i2 : Integrable (fun t => c * (mFourier (-n) t • G t)) := (integrable_cont G n).const_mul c
  have i3 : Integrable (fun t => c * (mFourier (-n) t • F t) - c * (mFourier (-n) t • G t)) :=
    i1.sub i2
  rw [integral_sub i3 (integrable_cont H n), integral_sub i1 i2, integral_const_mul,
    integral_const_mul]
  ring

theorem sq_add3_le (X Y Z : ℝ) : (X + Y + Z) ^ 2 ≤ 3 * X ^ 2 + 3 * Y ^ 2 + 3 * Z ^ 2 := by
  nlinarith [sq_nonneg (X - Y), sq_nonneg (Y - Z), sq_nonneg (X - Z)]

theorem norm_comb_le (c a b d : ℂ) : ‖c * (a - b) - d‖ ≤ ‖c‖ * ‖a‖ + ‖c‖ * ‖b‖ + ‖d‖ := by
  have h1 : ‖c * (a - b)‖ ≤ ‖c‖ * ‖a‖ + ‖c‖ * ‖b‖ := by
    rw [norm_mul, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_sub_le a b) (norm_nonneg c)
  linarith [norm_sub_le (c * (a - b)) d]

theorem coeffMemH_comb {m : ℝ} {a b d : (Fin 3 → ℤ) → ℂ} (ha : CoeffMemH m a)
    (hb : CoeffMemH m b) (hd : CoeffMemH m d) (c : ℂ) :
    CoeffMemH m (fun n => c * (a n - b n) - d n) := by
  unfold CoeffMemH at *
  have hle : ∀ n, sobWeight n ^ m * ‖c * (a n - b n) - d n‖ ^ 2 ≤
      (3 * ‖c‖ ^ 2) * (sobWeight n ^ m * ‖a n‖ ^ 2) + (3 * ‖c‖ ^ 2) * (sobWeight n ^ m * ‖b n‖ ^ 2) +
        3 * (sobWeight n ^ m * ‖d n‖ ^ 2) := by
    intro n
    have hw := sobWeight_rpow_nonneg n m
    have h2 : ‖c * (a n - b n) - d n‖ ^ 2 ≤
        3 * (‖c‖ * ‖a n‖) ^ 2 + 3 * (‖c‖ * ‖b n‖) ^ 2 + 3 * ‖d n‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) (norm_comb_le c (a n) (b n) (d n)) 2).trans
        (sq_add3_le _ _ _)
    calc sobWeight n ^ m * ‖c * (a n - b n) - d n‖ ^ 2
        ≤ sobWeight n ^ m * (3 * (‖c‖ * ‖a n‖) ^ 2 + 3 * (‖c‖ * ‖b n‖) ^ 2 + 3 * ‖d n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hw
      _ = _ := by ring
  exact Summable.of_nonneg_of_le (coeffSobSq_term_nonneg _ _) hle
    (((ha.mul_left _).add (hb.mul_left _)).add (hd.mul_left _))

theorem memH_comb {m : ℝ} {F G H : C(T3, ℂ)} (hF : MemH m F) (hG : MemH m G) (hH : MemH m H)
    (c : ℂ) : MemH m (fun t => c * (F t - G t) - H t) := by
  unfold MemH
  have : mFourierCoeff (fun t => c * (F t - G t) - H t) =
      fun n => c * (mFourierCoeff F n - mFourierCoeff G n) - mFourierCoeff H n :=
    funext (mFourierCoeff_comb F G H c)
  rw [this]
  exact coeffMemH_comb hF hG hH c

theorem summable_norm_derivCoeff {m : ℝ} {α : Fin 3 → ℕ}
    (hm : (Fintype.card (Fin 3) : ℝ) / 2 + mOrder α < m) {F : T3 → ℂ} (hF : MemH m F) :
    Summable fun n => ‖derivCoeff α (mFourierCoeff F) n‖ :=
  (summable_norm_of_coeffMemH (by linarith) (coeffMemH_derivCoeff hF α).1).1

/-- **`∂^α` is linear on `H^m`, `m > 3/2 + |α|`.** -/
theorem fourierDeriv_comb {m : ℝ} {α : Fin 3 → ℕ}
    (hm : (Fintype.card (Fin 3) : ℝ) / 2 + mOrder α < m) {F G H : C(T3, ℂ)} (hF : MemH m F)
    (hG : MemH m G) (hH : MemH m H) (c : ℂ) :
    fourierDeriv α (fun t => c * (F t - G t) - H t) =
      c • (fourierDeriv α F - fourierDeriv α G) - fourierDeriv α H := by
  unfold fourierDeriv
  have hc : derivCoeff α (mFourierCoeff fun t => c * (F t - G t) - H t) = fun n =>
      c * (derivCoeff α (mFourierCoeff F) n - derivCoeff α (mFourierCoeff G) n) -
        derivCoeff α (mFourierCoeff H) n := by
    funext n; simp only [derivCoeff, mFourierCoeff_comb]; ring
  rw [hc]
  have hsF := summable_norm_derivCoeff hm hF
  have hsG := summable_norm_derivCoeff hm hG
  have hsH := summable_norm_derivCoeff hm hH
  have h1 := ((hasSum_fourierSum hsF).sub (hasSum_fourierSum hsG)).const_smul c |>.sub
    (hasSum_fourierSum hsH)
  have hs : Summable fun n => ‖c * (derivCoeff α (mFourierCoeff F) n -
      derivCoeff α (mFourierCoeff G) n) - derivCoeff α (mFourierCoeff H) n‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (((hsF.add hsG).mul_left ‖c‖).add hsH)
    refine (norm_comb_le _ _ _ _).trans (le_of_eq ?_)
    ring
  have h2 : HasSum (fun n => (c * (derivCoeff α (mFourierCoeff F) n -
      derivCoeff α (mFourierCoeff G) n) - derivCoeff α (mFourierCoeff H) n) • mFourier n)
      (c • (fourierSum (derivCoeff α (mFourierCoeff ⇑F)) -
        fourierSum (derivCoeff α (mFourierCoeff ⇑G))) -
        fourierSum (derivCoeff α (mFourierCoeff ⇑H))) :=
    h1.congr_fun fun n => by simp only [sub_smul, mul_smul, smul_sub]
  exact (hasSum_fourierSum hs).unique h2

end Lin

/-! ### Time slices and the slab classes -/

section Classes

variable {T : ℝ}

/-- The point `(t, y)` of `ℝ⁴`. -/
abbrev pt (t : ℝ) (y : Fin 3 → ℝ) : E4 := Fin.cons t y

theorem pt_add_shift (t : ℝ) (y : Fin 3 → ℝ) (n : Fin 3 → ℤ) :
    pt t (y + fun i => (n i : ℝ)) = pt t y + spatialShift n := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pt]
  · simp [pt]

/-- The time slice `y ↦ u(t, y)` as a function on `𝕋³`. -/
def slice (u : E4 → ℂ) (t : ℝ) : T3 → ℂ := SobolevBoxCr.descendFun fun y => u (pt t y)

theorem isPeriodic_slice {u : E4 → ℂ} (hper : ∀ (n : Fin 3 → ℤ) x, u (x + spatialShift n) = u x)
    (t : ℝ) : SobolevBoxCr.IsPeriodic fun y : Fin 3 → ℝ => u (pt t y) := fun n y => by
  show u (pt t (y + fun i => (n i : ℝ))) = u (pt t y)
  rw [pt_add_shift, hper]

/-- **`u ∈ C((0,T); H^m(𝕋³))`** (spatially periodic, continuous slices). -/
structure CtH (T m : ℝ) (u : E4 → ℂ) : Prop where
  periodic : ∀ (n : Fin 3 → ℤ) (x : E4), u (x + spatialShift n) = u x
  slice_cont : ∀ t ∈ Ioo 0 T, Continuous fun y : Fin 3 → ℝ => u (pt t y)
  mem : ∀ t ∈ Ioo 0 T, MemH m (slice u t)
  cont : ∀ t₀ ∈ Ioo 0 T,
    Tendsto (fun t => sobNorm m fun y => slice u t y - slice u t₀ y) (𝓝[Ioo 0 T] t₀) (𝓝 0)

/-- **`∂_t u = u'` in `H^m`**: the difference quotients of the slices converge in `H^m`. -/
def HasTimeDerivH (T m : ℝ) (u u' : E4 → ℂ) : Prop :=
  ∀ t₀ ∈ Ioo 0 T, Tendsto (fun t => sobNorm m fun y =>
    (((t - t₀)⁻¹ : ℝ) : ℂ) * (slice u t y - slice u t₀ y) - slice u' t₀ y) (𝓝[≠] t₀) (𝓝 0)

/-- **`u ∈ C_tH^s ∩ C¹_tH^{s-1} ∩ C²_tH^{s-2}`** on `(0,T)`. -/
def SlabC2 (T s : ℝ) (u : E4 → ℂ) : Prop :=
  ∃ u₁ u₂ : E4 → ℂ, CtH T s u ∧ CtH T (s - 1) u₁ ∧ CtH T (s - 2) u₂ ∧
    HasTimeDerivH T (s - 1) u u₁ ∧ HasTimeDerivH T (s - 2) u₁ u₂

/-- **`u ∈ C_tH^s ∩ C¹_tH^{s-1}`** on `(0,T)`. -/
def SlabC1 (T s : ℝ) (u : E4 → ℂ) : Prop :=
  ∃ u₁ : E4 → ℂ, CtH T s u ∧ CtH T (s - 1) u₁ ∧ HasTimeDerivH T (s - 1) u u₁

/-- The slice as a continuous function. -/
def sliceC {m : ℝ} {u : E4 → ℂ} (hu : CtH T m u) {t : ℝ} (ht : t ∈ Ioo 0 T) : C(T3, ℂ) :=
  ⟨slice u t, SobolevBoxCr.continuous_descendFun (hu.slice_cont t ht) (isPeriodic_slice hu.periodic t)⟩

/-- The slice-wise spatial derivative `∂_y^α u(t, y)`. -/
def sD (α : Fin 3 → ℕ) (u : E4 → ℂ) (x : E4) : ℂ :=
  fourierDeriv α (slice u (x 0)) (SobolevBoxCr.torusMk (Fin.tail x))

theorem slice_pt {u : E4 → ℂ} (hper : ∀ (n : Fin 3 → ℤ) x, u (x + spatialShift n) = u x)
    (t : ℝ) (y : Fin 3 → ℝ) : slice u t (SobolevBoxCr.torusMk y) = u (pt t y) :=
  SobolevBoxCr.descendFun_mk (isPeriodic_slice hper t) y

theorem card_fin3 : (Fintype.card (Fin 3) : ℝ) = 3 := by simp

/-- `sD 0 u = u` on the slab. -/
theorem sD_zero {m : ℝ} {u : E4 → ℂ} (hu : CtH T m u) (hm : 3 / 2 < m) {x : E4}
    (hx : x ∈ cylSlab T) : sD 0 u x = u x := by
  have hF := fourierDeriv_zero (m := m) (by rw [card_fin3]; linarith) (sliceC hu hx) (hu.mem _ hx)
  unfold sD
  rw [show slice u (x 0) = ⇑(sliceC hu hx) from rfl, hF]
  change slice u (x 0) (SobolevBoxCr.torusMk (Fin.tail x)) = u x
  rw [slice_pt hu.periodic]
  simp [pt]

end Classes

end SlabSob
end EinsteinSM
end RenewalGeometry
