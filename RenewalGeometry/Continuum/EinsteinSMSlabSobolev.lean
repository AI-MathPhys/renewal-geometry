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


/-! ### Slice-wise derivatives: continuity, spatial and time derivatives -/

section Deriv

variable {T : ℝ}

theorem memH_zero_fun (m : ℝ) : MemH m (fun _ : T3 => (0 : ℂ)) := by
  have : mFourierCoeff (fun _ : T3 => (0 : ℂ)) = fun _ => 0 := by
    funext n; simp [mFourierCoeff]
  unfold MemH CoeffMemH
  rw [this]
  simpa using (summable_zero : Summable fun _ : Fin 3 → ℤ => (0 : ℝ))

theorem fourierDeriv_sub {m : ℝ} {α : Fin 3 → ℕ}
    (hm : (Fintype.card (Fin 3) : ℝ) / 2 + mOrder α < m) {F G : C(T3, ℂ)} (hF : MemH m F)
    (hG : MemH m G) :
    fourierDeriv α (fun t => F t - G t) = fourierDeriv α F - fourierDeriv α G := by
  have h := fourierDeriv_comb hm hF hG (H := 0) (show MemH m ⇑(0 : C(T3, ℂ)) from memH_zero_fun m) 1
  have e1 : (fun t => (1 : ℂ) * (F t - G t) - (0 : C(T3, ℂ)) t) = fun t => F t - G t := by
    funext t; simp
  have e2 : fourierDeriv α ⇑(0 : C(T3, ℂ)) = 0 := by
    unfold fourierDeriv
    have : derivCoeff α (mFourierCoeff ⇑(0 : C(T3, ℂ))) = 0 := by
      funext n; simp [derivCoeff, mFourierCoeff]
    rw [this]
    unfold fourierSum
    simp
  rw [e1, e2, one_smul, sub_zero] at h
  exact h

theorem memH_sub {m : ℝ} {F G : C(T3, ℂ)} (hF : MemH m F) (hG : MemH m G) :
    MemH m (fun t => F t - G t) := by
  have h := memH_comb hF hG (H := 0) (show MemH m ⇑(0 : C(T3, ℂ)) from memH_zero_fun m) 1
  have e1 : (fun t => (1 : ℂ) * (F t - G t) - (0 : C(T3, ℂ)) t) = fun t => F t - G t := by
    funext t; simp
  rwa [e1] at h

/-- The slice-wise derivative at time `t` as a continuous function. -/
theorem sD_eq_apply (α : Fin 3 → ℕ) (u : E4 → ℂ) (x : E4) :
    sD α u x = fourierDeriv α (slice u (x 0)) (SobolevBoxCr.torusMk (Fin.tail x)) := rfl

/-- **Continuity in time of `∂^α u(t, ·)` in the sup norm.** -/
theorem tendsto_fourierDeriv_slice {m : ℝ} {α : Fin 3 → ℕ} (hm : 3 / 2 + mOrder α < m)
    {u : E4 → ℂ} (hu : CtH T m u) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) :
    Tendsto (fun t => fourierDeriv α (slice u t)) (𝓝[Ioo 0 T] t₀)
      (𝓝 (fourierDeriv α (slice u t₀))) := by
  have hm' : (Fintype.card (Fin 3) : ℝ) / 2 + mOrder α < m := by rw [card_fin3]; linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ᶠ t in 𝓝[Ioo 0 T] t₀, ‖fourierDeriv α (slice u t) - fourierDeriv α (slice u t₀)‖ ≤
      embConst (Fin 3) (m - mOrder α) * sobNorm m (fun y => slice u t y - slice u t₀ y) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have e := fourierDeriv_sub hm' (F := sliceC hu ht) (G := sliceC hu ht₀) (hu.mem t ht)
      (hu.mem t₀ ht₀)
    change ‖fourierDeriv α ⇑(sliceC hu ht) - fourierDeriv α ⇑(sliceC hu ht₀)‖ ≤ _
    rw [← e]
    exact norm_fourierDeriv_le hm' (memH_sub (F := sliceC hu ht) (G := sliceC hu ht₀)
      (hu.mem t ht) (hu.mem t₀ ht₀))
  have hlim : Tendsto (fun t => embConst (Fin 3) (m - mOrder α) *
      sobNorm m (fun y => slice u t y - slice u t₀ y)) (𝓝[Ioo 0 T] t₀) (𝓝 0) := by
    simpa using (hu.cont t₀ ht₀).const_mul (embConst (Fin 3) (m - mOrder α))
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb hlim

/-- **`∂^α u` is jointly continuous on the slab** for `u ∈ C_tH^m`, `m > 3/2 + |α|`. -/
theorem continuousOn_sD {m : ℝ} {α : Fin 3 → ℕ} (hm : 3 / 2 + mOrder α < m) {u : E4 → ℂ}
    (hu : CtH T m u) : ContinuousOn (sD α u) (cylSlab T) := by
  intro x hx
  have hΦ : ContinuousWithinAt (fun x : E4 => fourierDeriv α (slice u (x 0))) (cylSlab T) x :=
    (tendsto_fourierDeriv_slice hm hu hx).comp
      (tendsto_nhdsWithin_iff.mpr ⟨((continuous_apply 0).tendsto x).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun y hy => hy⟩)
  have hy : ContinuousWithinAt (fun x : E4 => SobolevBoxCr.torusMk (Fin.tail x)) (cylSlab T) x :=
    (SobolevBoxCr.continuous_torusMk.comp (continuous_pi fun i => continuous_apply i.succ)
      ).continuousWithinAt
  exact (continuous_eval.continuousAt.comp_continuousWithinAt (hΦ.prodMk hy) :)

theorem tail_add_single_succ (x : E4) (j : Fin 3) (r : ℝ) :
    Fin.tail (x + r • Pi.single j.succ 1) = Fin.tail x + r • (Pi.single j 1 : Fin 3 → ℝ) := by
  funext k
  simp only [Fin.tail, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : k = j
  · subst h; simp
  · simp [h, Pi.single_apply, Fin.succ_inj]

/-- **Spatial derivatives of `∂^α u`.** -/
theorem hasDerivAt_sD_space {m : ℝ} {α : Fin 3 → ℕ} (hm : 3 / 2 + mOrder α + 1 < m)
    {u : E4 → ℂ} (hu : CtH T m u) {x : E4} (hx : x ∈ cylSlab T) (j : Fin 3) :
    HasDerivAt (fun r : ℝ => sD α u (x + r • Pi.single j.succ 1))
      (sD (α + Pi.single j 1) u x) 0 := by
  have hm' : (Fintype.card (Fin 3) : ℝ) / 2 + mOrder α + 1 < m := by rw [card_fin3]; linarith
  have hL := isLineDeriv_fourierDeriv hm' (hu.mem _ hx) j (SobolevBoxCr.torusMk (Fin.tail x))
  have e : (fun r : ℝ => sD α u (x + r • Pi.single j.succ 1)) = fun r =>
      fourierDeriv α (slice u (x 0)) (SobolevBoxCr.torusMk (Fin.tail x) + lineShift j r) := by
    funext r
    have h0 : (x + r • (Pi.single j.succ 1 : E4)) 0 = x 0 := by
      simp
    rw [sD_eq_apply, h0, tail_add_single_succ, SobolevBoxCr.torusMk_add,
      SobolevBoxCr.lineShift_eq_torusMk]
  rw [e]
  exact hL

/-- **Time derivatives of `∂^α u`**: `∂_t ∂^α u = ∂^α u'` when `∂_t u = u'` in `H^{m'}`,
`m' > 3/2 + |α|`. -/
theorem hasDerivAt_sD_time {m m' : ℝ} {α : Fin 3 → ℕ} (hm' : 3 / 2 + mOrder α < m')
    (hmm : m' ≤ m) {u u' : E4 → ℂ} (hu : CtH T m u) (hu' : CtH T m' u')
    (hd : HasTimeDerivH T m' u u') {x : E4} (hx : x ∈ cylSlab T) :
    HasDerivAt (fun r : ℝ => sD α u (x + r • Pi.single 0 1)) (sD α u' x) 0 := by
  have hm'' : (Fintype.card (Fin 3) : ℝ) / 2 + mOrder α < m' := by rw [card_fin3]; linarith
  set t₀ := x 0
  set y := SobolevBoxCr.torusMk (Fin.tail x)
  have ht₀ : t₀ ∈ Ioo 0 T := hx
  have htail : ∀ r : ℝ, Fin.tail (x + r • (Pi.single 0 1 : E4)) = Fin.tail x := fun r => by
    funext k; simp [Fin.tail, Pi.single_apply, Fin.succ_ne_zero k]
  have hzero : ∀ r : ℝ, (x + r • (Pi.single 0 1 : E4)) 0 = t₀ + r := fun r => by simp [t₀]
  rw [hasDerivAt_iff_tendsto_slope_zero]
  -- the quotient as `∂^α` of the `H^{m'}` difference quotient
  have hq : ∀ r : ℝ, t₀ + r ∈ Ioo 0 T →
      ‖r⁻¹ • (sD α u (x + (0 + r) • Pi.single 0 1) - sD α u (x + (0 : ℝ) • Pi.single 0 1)) -
        sD α u' x‖ ≤ embConst (Fin 3) (m' - mOrder α) * sobNorm m' (fun z =>
          ((((t₀ + r) - t₀)⁻¹ : ℝ) : ℂ) * (slice u (t₀ + r) z - slice u t₀ z) - slice u' t₀ z) := by
    intro r hr
    have hFm := (hu.mem _ hr).mono hmm
    have hGm := (hu.mem _ ht₀).mono hmm
    have hHm := hu'.mem _ ht₀
    have hcomb := fourierDeriv_comb hm'' (F := sliceC hu hr) (G := sliceC hu ht₀)
      (H := sliceC hu' ht₀) hFm hGm hHm ((((t₀ + r) - t₀)⁻¹ : ℝ) : ℂ)
    have hmem := memH_comb (F := sliceC hu hr) (G := sliceC hu ht₀) (H := sliceC hu' ht₀) hFm hGm
      hHm ((((t₀ + r) - t₀)⁻¹ : ℝ) : ℂ)
    have hb := norm_fourierDeriv_le hm'' hmem
    rw [hcomb] at hb
    refine le_trans (le_of_eq ?_) ((ContinuousMap.norm_coe_le_norm _ y).trans hb)
    simp only [sD_eq_apply, zero_add, zero_smul, add_zero, hzero, htail, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, add_sub_cancel_left, Complex.real_smul, smul_eq_mul]
    rfl
  have hlim : Tendsto (fun r : ℝ => embConst (Fin 3) (m' - mOrder α) * sobNorm m' (fun z =>
      ((((t₀ + r) - t₀)⁻¹ : ℝ) : ℂ) * (slice u (t₀ + r) z - slice u t₀ z) - slice u' t₀ z))
      (𝓝[≠] 0) (𝓝 0) := by
    have h1 := hd t₀ ht₀
    have hmap : Tendsto (fun r : ℝ => t₀ + r) (𝓝[≠] 0) (𝓝[≠] t₀) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Tendsto (fun r : ℝ => t₀ + r) (𝓝 0) (𝓝 (t₀ + 0)) :=
          tendsto_const_nhds.add tendsto_id
        rw [add_zero] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    simpa using (h1.comp hmap).const_mul (embConst (Fin 3) (m' - mOrder α))
  have hev : ∀ᶠ r in 𝓝[≠] (0 : ℝ), t₀ + r ∈ Ioo 0 T := by
    have : Tendsto (fun r : ℝ => t₀ + r) (𝓝 0) (𝓝 t₀) := by
      have hc : Tendsto (fun r : ℝ => t₀ + r) (𝓝 0) (𝓝 (t₀ + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rwa [add_zero] at hc
    exact nhdsWithin_le_nhds (this.eventually (isOpen_Ioo.mem_nhds ht₀))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hev.mono fun r hr => hq r hr) hlim

end Deriv


/-! ### From the slab classes to classical regularity -/

section Regularity

variable {T : ℝ}

theorem mOrder_zero3 : mOrder (0 : Fin 3 → ℕ) = 0 := by simp [mOrder]

theorem mOrder_single3 (j : Fin 3) : mOrder (Pi.single j 1 : Fin 3 → ℕ) = 1 := by
  have := mOrder_add_single (0 : Fin 3 → ℕ) j
  rwa [zero_add, mOrder_zero3] at this

theorem mOrder_single3_add (j k : Fin 3) :
    mOrder (Pi.single j 1 + Pi.single k 1 : Fin 3 → ℕ) = 2 := by
  rw [mOrder_add_single, mOrder_single3]

/-- The candidate partial derivatives `(∂_t v = v', ∂_{y_j} v)` of `v` on the slab. -/
def gPart (β : Fin 3 → ℕ) (v v' : E4 → ℂ) (i : Fin 4) : E4 → ℂ :=
  Fin.cases (sD β v') (fun j => sD (β + Pi.single j 1) v) i

/-- **The partial derivatives of `∂^β v`** for `v ∈ C_tH^m`, `∂_t v = v'` in `H^{m-1}`,
`m > 5/2 + |β|`. -/
theorem hasDerivAt_sD_partials {m : ℝ} {β : Fin 3 → ℕ} (hm : 5 / 2 + mOrder β < m)
    {v v' : E4 → ℂ} (hv : CtH T m v) (hv' : CtH T (m - 1) v') (hd : HasTimeDerivH T (m - 1) v v')
    (i : Fin 4) {x : E4} (hx : x ∈ cylSlab T) :
    HasDerivAt (fun r : ℝ => sD β v (x + r • Pi.single i 1)) (gPart β v v' i x) 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hasDerivAt_sD_time (by linarith) (by linarith) hv hv' hd hx
  · exact hasDerivAt_sD_space (by linarith) hv hx j

theorem continuousOn_gPart {m : ℝ} {β : Fin 3 → ℕ} (hm : 5 / 2 + mOrder β < m)
    {v v' : E4 → ℂ} (hv : CtH T m v) (hv' : CtH T (m - 1) v') (i : Fin 4) :
    ContinuousOn (gPart β v v' i) (cylSlab T) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuousOn_sD (by linarith) hv'
  · have : mOrder (β + Pi.single j 1) = mOrder β + 1 := mOrder_add_single β j
    exact continuousOn_sD (by rw [this]; push_cast; linarith) hv

theorem eventually_mem_slab {x : E4} (hx : x ∈ cylSlab T) (i : Fin 4) :
    ∀ᶠ r : ℝ in 𝓝 0, x + r • (Pi.single i 1 : E4) ∈ cylSlab T := by
  have hc : Tendsto (fun r : ℝ => x + r • (Pi.single i 1 : E4)) (𝓝 0) (𝓝 x) := by
    have h1 : Continuous fun r : ℝ => x + r • (Pi.single i 1 : E4) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h2 := h1.tendsto 0
    rwa [zero_smul, add_zero] at h2
  exact hc.eventually ((isOpen_cylSlab T).mem_nhds hx)

/-- **`C_tH^m ∩ C¹_tH^{m-1} ⊂ C¹` on the slab**, `m > 5/2` (`H^m(𝕋³) ⊂ C¹`). -/
theorem contDiffOn_one_of_slabC1 {s : ℝ} (hs : 5 / 2 < s) {u : E4 → ℂ} (hu : SlabC1 T s u) :
    ContDiffOn ℝ 1 u (cylSlab T) := by
  obtain ⟨u₁, h1, h2, hd⟩ := hu
  have hm : 5 / 2 + (mOrder (0 : Fin 3 → ℕ) : ℝ) < s := by rw [mOrder_zero3]; simpa using hs
  refine PartialC1.contDiffOn_one_of_partials (isOpen_cylSlab T)
    (g := gPart 0 u u₁) (continuousOn_gPart hm h1 h2) fun i x hx => ?_
  refine (hasDerivAt_sD_partials hm h1 h2 hd i hx).congr_of_eventuallyEq ?_
  filter_upwards [eventually_mem_slab hx i] with r hr
  exact (sD_zero h1 (by linarith) hr).symm

/-- **`C_tH^s ∩ C¹_tH^{s-1} ∩ C²_tH^{s-2} ⊂ C²` on the slab**, `s > 7/2` (`H^{s-2} ⊂ C⁰`,
`H^{s-1} ⊂ C¹`, `H^s ⊂ C²`). -/
theorem contDiffOn_two_of_slabC2 {s : ℝ} (hs : 7 / 2 < s) {u : E4 → ℂ} (hu : SlabC2 T s u) :
    ContDiffOn ℝ 2 u (cylSlab T) := by
  obtain ⟨u₁, u₂, h1, h2, h3, hd1, hd2⟩ := hu
  have h3' : CtH T (s - 1 - 1) u₂ := by rw [show s - 1 - 1 = s - 2 by ring]; exact h3
  have hd2' : HasTimeDerivH T (s - 1 - 1) u₁ u₂ := by
    rw [show s - 1 - 1 = s - 2 by ring]; exact hd2
  have hm0 : 5 / 2 + (mOrder (0 : Fin 3 → ℕ) : ℝ) < s := by rw [mOrder_zero3]; push_cast; linarith
  have hm0' : 5 / 2 + (mOrder (0 : Fin 3 → ℕ) : ℝ) < s - 1 := by
    rw [mOrder_zero3]; push_cast; linarith
  refine PartialC1.contDiffOn_two_of_partials (isOpen_cylSlab T) (g := gPart 0 u u₁)
    (fun i => ?_) fun i x hx => ?_
  · refine Fin.cases ?_ (fun j => ?_) i
    · -- `∂_t u = u₁`: its partials are `(u₂, ∂_y u₁)`
      exact PartialC1.contDiffOn_one_of_partials (isOpen_cylSlab T) (g := gPart 0 u₁ u₂)
        (continuousOn_gPart hm0' h2 h3') fun i x hx => hasDerivAt_sD_partials hm0' h2 h3' hd2' i hx
    · -- `∂_{y_j} u`: its partials are `(∂_{y_j} u₁, ∂_{y_k}∂_{y_j} u)`
      have hmj : 5 / 2 + (mOrder (0 + Pi.single j 1 : Fin 3 → ℕ) : ℝ) < s := by
        rw [zero_add, mOrder_single3]; push_cast; linarith
      exact PartialC1.contDiffOn_one_of_partials (isOpen_cylSlab T)
        (g := gPart (0 + Pi.single j 1) u u₁) (continuousOn_gPart hmj h1 h2)
        fun i x hx => hasDerivAt_sD_partials hmj h1 h2 hd1 i hx
  · refine (hasDerivAt_sD_partials hm0 h1 h2 hd1 i hx).congr_of_eventuallyEq ?_
    filter_upwards [eventually_mem_slab hx i] with r hr
    exact (sD_zero h1 (by linarith) hr).symm

/-! ### Finite-dimensional fields -/

/-- `f ∈ C_tH^s ∩ C¹_tH^{s-1} ∩ C²_tH^{s-2}`: all real-linear scalar components are. -/
def VecSlabC2 (T s : ℝ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E4 → F) :
    Prop :=
  ∀ ℓ : F →L[ℝ] ℂ, SlabC2 T s fun x => ℓ (f x)

/-- `f ∈ C_tH^s ∩ C¹_tH^{s-1}`: all real-linear scalar components are. -/
def VecSlabC1 (T s : ℝ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E4 → F) :
    Prop :=
  ∀ ℓ : F →L[ℝ] ℂ, SlabC1 T s fun x => ℓ (f x)

theorem eq_sum_coordC {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (y : F) :
    y = ∑ k, (SobolevBoxCr.coordC (Module.finBasis ℝ F) k y).re • (Module.finBasis ℝ F) k := by
  conv_lhs => rw [← (Module.finBasis ℝ F).sum_repr y]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [SobolevBoxCr.coordC, Module.Basis.coord_apply]

theorem contDiffOn_of_components {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : E4 → F} {n : WithTop ℕ∞} {U : Set E4}
    (h : ∀ ℓ : F →L[ℝ] ℂ, ContDiffOn ℝ n (fun x => ℓ (f x)) U) : ContDiffOn ℝ n f U := by
  have e : f = fun x => ∑ k, (SobolevBoxCr.coordC (Module.finBasis ℝ F) k (f x)).re •
      (Module.finBasis ℝ F) k := funext fun x => eq_sum_coordC (f x)
  rw [e]
  refine ContDiffOn.sum fun k _ => ?_
  have h1 : ContDiffOn ℝ n (fun x => (SobolevBoxCr.coordC (Module.finBasis ℝ F) k (f x)).re) U :=
    Complex.reCLM.contDiff.comp_contDiffOn (h (SobolevBoxCr.coordC (Module.finBasis ℝ F) k))
  exact h1.smul contDiffOn_const

theorem eq_of_components {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {y y' : F} (h : ∀ ℓ : F →L[ℝ] ℂ, ℓ y = ℓ y') : y = y' := by
  rw [eq_sum_coordC y, eq_sum_coordC y']
  simp only [h]

theorem VecSlabC2.contDiffOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : E4 → F} {s : ℝ} (hs : 7 / 2 < s) (h : VecSlabC2 T s f) :
    ContDiffOn ℝ 2 f (cylSlab T) :=
  contDiffOn_of_components fun ℓ => contDiffOn_two_of_slabC2 hs (h ℓ)

theorem VecSlabC1.contDiffOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : E4 → F} {s : ℝ} (hs : 5 / 2 < s) (h : VecSlabC1 T s f) :
    ContDiffOn ℝ 1 f (cylSlab T) :=
  contDiffOn_of_components fun ℓ => contDiffOn_one_of_slabC1 hs (h ℓ)

theorem VecSlabC2.periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : E4 → F} {s : ℝ} (h : VecSlabC2 T s f) (n : Fin 3 → ℤ) (x : E4) :
    f (x + spatialShift n) = f x :=
  eq_of_components fun ℓ => by
    obtain ⟨_, _, h1, -⟩ := h ℓ
    exact h1.periodic n x

theorem VecSlabC1.periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : E4 → F} {s : ℝ} (h : VecSlabC1 T s f) (n : Fin 3 → ℤ) (x : E4) :
    f (x + spatialShift n) = f x :=
  eq_of_components fun ℓ => by
    obtain ⟨_, h1, -⟩ := h ℓ
    exact h1.periodic n x

/-- **The hypothesis of `cor:strong-solution-upgrade`** on fields `z = (e, A, H, Ψ, Ψ̄)` on the slab
`(0,T) × 𝕋³` (fixed gauges): `(e, A, H) ∈ C_tH^s ∩ C¹_tH^{s-1} ∩ C²_tH^{s-2}`,
`(Ψ, Ψ̄) ∈ C_tH^{s-1} ∩ C¹_tH^{s-2}`, `s ≥ 5`, with a common nondegenerate coframe chart. -/
structure SobolevSlab (T s : ℝ) {C : Type} [Fintype C] (z : FieldTuple C) : Prop where
  five_le : 5 ≤ s
  e : VecSlabC2 T s z.e
  A : VecSlabC2 T s z.A
  H : VecSlabC2 T s z.H
  Ψ : VecSlabC1 T (s - 1) z.Ψ
  Ψb : VecSlabC1 T (s - 1) z.Ψb
  gl : ∀ x ∈ cylSlab T, z.e x ∈ coframeGL

/-- **The Sobolev class gives classical fields**: bosons `C²`, spinors `C¹` on the open slab. -/
theorem classicalSlab_of_sobolevSlab {C : Type} [Fintype C] {z : FieldTuple C} {s : ℝ}
    (hz : SobolevSlab T s z) : ClassicalSlab T z := by
  have h72 : 7 / 2 < s := by linarith [hz.five_le]
  have h52 : 5 / 2 < s - 1 := by linarith [hz.five_le]
  exact ⟨hz.e.contDiffOn h72, hz.A.contDiffOn h72, hz.H.contDiffOn h72, hz.Ψ.contDiffOn h52,
    hz.Ψb.contDiffOn h52, hz.gl, hz.e.periodic, hz.A.periodic, hz.H.periodic, hz.Ψ.periodic,
    hz.Ψb.periodic⟩

end Regularity


/-! ### `cor:strong-solution-upgrade` -/

section Corollary

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **`cor:strong-solution-upgrade` (regularity upgrade on a common slab).**  Under the hypotheses
of `thm:reduced-closure`, every cutoff subsequence has a further subsequence with a limit
`(L, θ₀)` in the reduced topology such that, if the limit fields additionally satisfy (in the
fixed gauges on `(0,T) × 𝕋³`) `(e, A, H) ∈ C_tH^s ∩ C¹_tH^{s-1} ∩ C²_tH^{s-2}`,
`(Ψ, Ψ̄) ∈ C_tH^{s-1} ∩ C¹_tH^{s-2}`, `s ≥ 5`, with a common nondegenerate coframe chart
(`SobolevSlab`), then its distributional Euler identities are strong field equations: the packets
of the limit are its classical derivatives, and every Euler row of the classical first-variation
covector field — the second-order bosonic rows (Einstein in first-order form, Yang–Mills, Higgs)
and the first-order spinor rows — vanishes at every point of `(0,T) × (0,1)³` in every admissible
direction. -/
theorem strong_solution_upgrade_sobolev (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesReducedCertificate Q)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      (∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (ns (ψ k)))
          (fun k => reg.bank (ns (ψ k))) L θ₀) ∧
      ∀ s : ℝ, SobolevSlab T s (limitTuple L) →
        (∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
          ∀ᵐ x, x ∈ (slabChart t₀ t₁ h0 h01 h1 (T := T)).set →
            limitJet L x = redJet (limitTuple L) x) ∧
        ∀ x₀ : E4, x₀ 0 ∈ Ioo 0 T → (∀ i : Fin 3, x₀ i.succ ∈ Ioo 0 1) →
          ∀ w : FieldVal FC.C, IsAdmissible FC.left w →
            eulerRowW (classicalCov FC θ₀ (limitTuple L)) x₀ w = 0 := by
  obtain ⟨ψ, hψ, L, θ₀, hRC, hcl⟩ :=
    strong_solution_upgrade_classical hT reg hcert hcons hstat hyuk ns hns
  exact ⟨ψ, hψ, L, θ₀, hRC, fun s hs => hcl (classicalSlab_of_sobolevSlab hs)⟩

end Corollary

/-! ### Non-vacuity -/

section NonVacuity

variable {T : ℝ}

theorem mFourierCoeff_zero_fun : mFourierCoeff (fun _ : T3 => (0 : ℂ)) = fun _ => 0 := by
  funext n; simp [mFourierCoeff]

theorem sobNorm_zero_fun (m : ℝ) : sobNorm m (fun _ : T3 => (0 : ℂ)) = 0 := by
  simp [sobNorm, sobSq, coeffSobSq, mFourierCoeff_zero_fun]

theorem memH_const (m : ℝ) (c : ℂ) : MemH m (fun _ : T3 => c) := by
  have h := memH_comb (memH_mFourier (d := Fin 3) m 0)
    (show MemH m ⇑(0 : C(T3, ℂ)) from memH_zero_fun m)
    (show MemH m ⇑(0 : C(T3, ℂ)) from memH_zero_fun m) c
  have e : (fun t => c * (mFourier (0 : Fin 3 → ℤ) t - (0 : C(T3, ℂ)) t) - (0 : C(T3, ℂ)) t) =
      fun _ : T3 => c := by
    funext t; simp [mFourier]
  rwa [e] at h

theorem slice_const (c : ℂ) (t : ℝ) : slice (fun _ : E4 => c) t = fun _ => c := rfl

theorem ctH_const (m : ℝ) (c : ℂ) : CtH T m (fun _ : E4 => c) where
  periodic _ _ := rfl
  slice_cont _ _ := continuous_const
  mem _ _ := by rw [slice_const]; exact memH_const m c
  cont _ _ := by simp only [slice_const, sub_self, sobNorm_zero_fun]; exact tendsto_const_nhds

theorem hasTimeDerivH_const (m : ℝ) (c : ℂ) :
    HasTimeDerivH T m (fun _ : E4 => c) (fun _ => 0) := fun _ _ => by
  simp only [slice_const, sub_self, mul_zero, sobNorm_zero_fun]
  exact tendsto_const_nhds

theorem vecSlabC2_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (s : ℝ) (v : F) :
    VecSlabC2 T s (fun _ : E4 => v) := fun ℓ =>
  ⟨fun _ => 0, fun _ => 0, ctH_const s (ℓ v), ctH_const (s - 1) 0, ctH_const (s - 2) 0,
    hasTimeDerivH_const (s - 1) (ℓ v), hasTimeDerivH_const (s - 2) 0⟩

theorem vecSlabC1_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (s : ℝ) (v : F) :
    VecSlabC1 T s (fun _ : E4 => v) := fun ℓ =>
  ⟨fun _ => 0, ctH_const s (ℓ v), ctH_const (s - 1) 0, hasTimeDerivH_const (s - 1) (ℓ v)⟩

/-- **Non-vacuity of the Sobolev class**: the flat limit fields lie in it (`s = 5`). -/
theorem flatLimit_sobolevSlab :
    SobolevSlab T 5 (limitTuple (C := (trivialCarrier Unit).C) flatLimitT) :=
  ⟨le_rfl, vecSlabC2_const 5 flatCoframe, vecSlabC2_const 5 (0 : ConnFibre),
    vecSlabC2_const 5 (0 : HiggsFibre), vecSlabC1_const (5 - 1) (0 : SpinorFibre Unit),
    vecSlabC1_const (5 - 1) (0 : SpinorFibre Unit),
    fun _ _ => coframeChart_subset_GL flatCoframe_mem_chart⟩

/-- **Non-vacuity of `cor:strong-solution-upgrade`**: the flat regulator satisfies every
hypothesis of `strong_solution_upgrade_sobolev`. -/
example (hT : 0 < T) :=
  strong_solution_upgrade_sobolev hT (flatRegulator T) (fun Q => flatRegulator_reducedCertificate T Q)
    (flatRegulator_consistent hT) flatRegulator_stationary (trivialCarrier_yukawaContinuous Unit)
    id strictMono_id

end NonVacuity

end SlabSob
end EinsteinSM
end RenewalGeometry
