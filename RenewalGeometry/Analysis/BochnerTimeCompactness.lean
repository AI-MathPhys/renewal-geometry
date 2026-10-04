/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TotallyBoundedApproximation

/-!
# From spatial screens to spacetime compactness in `L²(0,T;H)`

This file proves `prop:time-compactness` of the Einstein–SM action-closure manuscript
(`papers/einstein_sm_action_closure`): a family `Y_h` bounded in the Bochner space
`L²(0,T;𝓗)`, with uniformly small spatial tails `‖(I - P_R) Y_h‖_{L²_t 𝓗}` for finite-rank
projections `P_R`, and with `P_R Y_h` bounded in `H¹(0,T;P_R 𝓗)` for each fixed `R`, is
precompact in `L²(0,T;𝓗)`.

## Encoding

* `L²(0,T;𝓗)` is Mathlib's Bochner space `Lp H 2 (volume.restrict (Ioc 0 T))`.
* `H¹(0,T;E)` is encoded through the absolutely continuous representative: a function `u`
  lies in `H¹(0,T;E)` with `‖∂_t u‖_{L²} ≤ C` when `u(t) = v₀ + ∫_0^t g` for a.e. `t ∈ (0,T)`,
  with `g ∈ L²(0,T;E)` and `‖g‖_{L²} ≤ C` (every `H¹(0,T)` class has such a representative;
  `g` is its weak derivative).  The `L²` part of the `H¹` norm of `P_R Y_h` is bounded by
  `‖P_R‖ sup_h ‖Y_h‖`.
* The finite-rank projections are arbitrary bounded idempotent operators with
  finite-dimensional range; orthogonality, smoothness of the ranges and `P_R → I` are not
  needed (the tail hypothesis is what is used).  The tail hypothesis is used in the form
  "for every `ε > 0` there is `R` with `sup_h ‖(I - P_R) Y_h‖ ≤ ε`", which is implied by
  `lim_{R→∞} sup_h ‖(I - P_R)Y_h‖ = 0`.

## Main results

* `norm_intervalIntegral_le_sqrt_mul_eLpNorm`: the one-dimensional Hölder-`1/2` bound
  `‖∫_a^b g‖ ≤ √(b - a) ‖g‖_{L²(0,T)}` (`0 ≤ a ≤ b ≤ T`).
* `totallyBounded_of_h1_bounded`: one-dimensional Rellich: an `H¹(0,T;V)`-bounded family with
  values in a finite-dimensional subspace `V` is totally bounded in `L²(0,T;H)` (sampling on a
  uniform partition; the Hölder bound gives uniform closeness to step functions with values in
  a compact ball of `V`).
* `timeCompactness_totallyBounded`, `timeCompactness_isCompact_closure`:
  **`prop:time-compactness`** (main assertion).
* `timeCompactness_of_tested_derivative_bound`: the final assertion of the proposition: the
  `H¹(0,T;P_R𝓗)` bound follows from a bound on the tested time derivatives
  `|∂_t ⟪e, Y_h⟫| ≤ ‖e‖_V D_h(t)` with `‖D_h‖_{L²(0,T)} ≤ C` (a bound on `∂_t Y_h` in
  `L²(0,T;V^*)`, e.g. `V = H^m(Σ;E)`), when `P_R x = Σ_j ⟪e_{R,j}, x⟫ e_{R,j}` with `e_{R,j} ∈ V`.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace RenewalGeometry
namespace BochnerTimeCompactness

noncomputable section

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-! ### The one-dimensional Hölder bound -/

/-- `‖∫_a^b g‖ ≤ √(b-a) ‖g‖_{L²(0,T)}` for `0 ≤ a ≤ b ≤ T` and `g ∈ L²(0,T)`. -/
theorem norm_intervalIntegral_le_sqrt_mul_eLpNorm {T : ℝ} {g : ℝ → H}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 T))) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ T) :
    ‖∫ s in a..b, g s‖ ≤ Real.sqrt (b - a) * (eLpNorm g 2 (volume.restrict (Ioc 0 T))).toReal := by
  have hsub : Ioc a b ⊆ Ioc 0 T := Ioc_subset_Ioc ha hb
  have hgab : MemLp g 2 (volume.restrict (Ioc a b)) := hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  rw [intervalIntegral.integral_of_le hab]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [integral_norm_eq_lintegral_enorm hgab.1]
  have h1 : eLpNorm g 1 (volume.restrict (Ioc a b)) ≤
      eLpNorm g 2 (volume.restrict (Ioc a b)) * (volume.restrict (Ioc a b)) univ ^
        (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hgab.1
  rw [eLpNorm_one_eq_lintegral_enorm] at h1
  have h2 : eLpNorm g 2 (volume.restrict (Ioc a b)) ≤ eLpNorm g 2 (volume.restrict (Ioc 0 T)) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)
  have hvol : (volume.restrict (Ioc a b)) univ = ENNReal.ofReal (b - a) := by
    simp [Real.volume_Ioc]
  rw [hvol] at h1
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [hexp] at h1
  have hfin : eLpNorm g 2 (volume.restrict (Ioc 0 T)) ≠ ∞ := hg.eLpNorm_ne_top
  have h3 : ∫⁻ x in Ioc a b, ‖g x‖ₑ ≤
      eLpNorm g 2 (volume.restrict (Ioc 0 T)) * ENNReal.ofReal (b - a) ^ (1 / 2 : ℝ) :=
    h1.trans (mul_le_mul_left h2 _)
  have hne : eLpNorm g 2 (volume.restrict (Ioc 0 T)) * ENNReal.ofReal (b - a) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top hfin (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  refine (ENNReal.toReal_mono hne h3).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by linarith),
    Real.sqrt_eq_rpow, mul_comm]

/-- Interval integrability on `[0, t]`, `t ≤ T`, of an `L²(0,T)` function. -/
theorem intervalIntegrable_of_memLp {T : ℝ} {g : ℝ → H}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 T))) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ T) : IntervalIntegrable g volume a b := by
  have hi : IntegrableOn g (Ioc 0 T) volume := hg.integrable (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact hi.mono_set (Ioc_subset_Ioc ha hb)

/-! ### Uniform partition of `(0, T]` -/

/-- The index `k ∈ {0, …, N}` of the subinterval `(kT/(N+1), (k+1)T/(N+1)]` containing `t`
(clamped outside `(0, T]`). -/
def idx (N : ℕ) (T t : ℝ) : Fin (N + 1) :=
  ⟨min (⌈((N : ℝ) + 1) * t / T⌉ - 1).toNat N, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The left endpoint `kT/(N+1)` of the `k`-th subinterval. -/
def node (N : ℕ) (T : ℝ) (k : Fin (N + 1)) : ℝ := T * (k : ℕ) / ((N : ℝ) + 1)

theorem measurable_idx (N : ℕ) (T : ℝ) : Measurable (idx N T) := by
  have h1 : Measurable fun t : ℝ => ⌈((N : ℝ) + 1) * t / T⌉ :=
    Int.measurable_ceil.comp (by fun_prop)
  exact (measurable_of_countable (fun z : ℤ =>
    (⟨min (z - 1).toNat N, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (N + 1)))).comp h1

theorem node_spec {N : ℕ} {T t : ℝ} (hT : 0 < T) (ht : t ∈ Ioc 0 T) :
    0 ≤ node N T (idx N T t) ∧ node N T (idx N T t) ≤ t ∧
      t - node N T (idx N T t) ≤ T / ((N : ℝ) + 1) := by
  obtain ⟨ht0, htT⟩ := ht
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set x := ((N : ℝ) + 1) * t / T with hx
  set c := ⌈x⌉ with hc
  have hx0 : 0 < x := by positivity
  have hxN : x ≤ (N : ℝ) + 1 := by
    rw [hx, div_le_iff₀ hT]; nlinarith
  have hc1 : 1 ≤ c := by rw [hc, Int.one_le_ceil_iff]; exact hx0
  have hcN : c ≤ (N : ℤ) + 1 := by
    rw [hc, Int.ceil_le]; push_cast; exact hxN
  have htoNat : ((c - 1).toNat : ℤ) = c - 1 := Int.toNat_of_nonneg (by omega)
  have hmin : min (c - 1).toNat N = (c - 1).toNat := min_eq_left (by omega)
  have hval : ((idx N T t : ℕ) : ℝ) = (c : ℝ) - 1 := by
    simp only [idx, ← hx, ← hc, hmin]
    have := congrArg (fun z : ℤ => (z : ℝ)) htoNat
    push_cast at this ⊢
    exact this
  have hlo : (c : ℝ) - 1 < x := by have := Int.ceil_lt_add_one x; rw [← hc] at this; linarith
  have hhi : x ≤ (c : ℝ) := Int.le_ceil x
  have hc1' : (1 : ℝ) ≤ c := by exact_mod_cast hc1
  simp only [node, hval]
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ hN]
    have : (c - 1) * T < x * T := mul_lt_mul_of_pos_right hlo hT
    rw [hx, div_mul_cancel₀ _ hT.ne'] at this
    nlinarith
  · have h2 : x * T ≤ c * T := mul_le_mul_of_nonneg_right hhi hT.le
    rw [hx, div_mul_cancel₀ _ hT.ne'] at h2
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN]
    nlinarith

/-! ### Step functions on the uniform partition -/

/-- The step function with value `c k` on the `k`-th subinterval. -/
def stepFn {N : ℕ} {T : ℝ} (c : Fin (N + 1) → H) : ℝ → H := fun t => c (idx N T t)

theorem stronglyMeasurable_stepFn {N : ℕ} {T : ℝ} (c : Fin (N + 1) → H) :
    StronglyMeasurable (stepFn (T := T) c) :=
  (StronglyMeasurable.of_discrete (f := c)).comp_measurable (measurable_idx N T)

theorem memLp_stepFn {N : ℕ} {T : ℝ} (c : Fin (N + 1) → H) :
    MemLp (stepFn (T := T) c) 2 (volume.restrict (Ioc 0 T)) := by
  refine MemLp.of_bound (stronglyMeasurable_stepFn c).aestronglyMeasurable
    (∑ k, ‖c k‖) (Eventually.of_forall fun t => ?_)
  exact Finset.single_le_sum (f := fun k => ‖c k‖) (fun k _ => norm_nonneg _)
    (Finset.mem_univ (idx N T t))

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 H]

/-- The step-function map `c ↦ Σ_k c_k 1_{(t_k, t_{k+1}]}` from `V^{N+1}` into `L²(0,T;H)`. -/
def stepLp (N : ℕ) (T : ℝ) (V : Submodule 𝕜 H) :
    (Fin (N + 1) → V) →ₗ[𝕜] Lp H 2 (volume.restrict (Ioc 0 T)) where
  toFun c := (memLp_stepFn (T := T) (fun k => (c k : H))).toLp _
  map_add' c c' := by
    rw [← MemLp.toLp_add (memLp_stepFn _) (memLp_stepFn _)]
    rfl
  map_smul' a c := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul a (memLp_stepFn _)]
    rfl

theorem coeFn_stepLp (N : ℕ) (T : ℝ) (V : Submodule 𝕜 H) (c : Fin (N + 1) → V) :
    stepLp N T V c =ᵐ[volume.restrict (Ioc 0 T)] stepFn (T := T) (fun k => (c k : H)) :=
  MemLp.coeFn_toLp (memLp_stepFn _)

/-- The absolutely continuous representative `v₀ + ∫_0^t g` is Hölder-`1/2` on `[0,T]`. -/
theorem norm_sub_primitive_le {T : ℝ} {g : ℝ → H}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 T))) (v₀ : H) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ T) :
    ‖(v₀ + ∫ r in (0)..t, g r) - (v₀ + ∫ r in (0)..s, g r)‖ ≤
      Real.sqrt (t - s) * (eLpNorm g 2 (volume.restrict (Ioc 0 T))).toReal := by
  rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_of_memLp hg le_rfl (hs.trans hst) ht)
    (intervalIntegrable_of_memLp hg le_rfl hs (hst.trans ht))]
  exact norm_intervalIntegral_le_sqrt_mul_eLpNorm hg hs hst ht

/-- **One-dimensional Rellich compactness in `L²(0,T;H)`.**  Let `P` be a bounded idempotent
operator with finite-dimensional range and `Y_i` a family bounded in `L²(0,T;H)` such that each
`P Y_i` has an `H¹(0,T)` representative `v₀ + ∫_0^t g_i` with `‖g_i‖_{L²(0,T)} ≤ C`.  Then
`{P Y_i}` is totally bounded in `L²(0,T;H)`. -/
theorem totallyBounded_of_h1_bounded {ι : Type*} {T : ℝ} (hT : 0 < T) (P : H →L[𝕜] H)
    [FiniteDimensional 𝕜 (LinearMap.range (P : H →ₗ[𝕜] H))] (hP : ∀ x, P (P x) = P x)
    (Y : ι → Lp H 2 (volume.restrict (Ioc 0 T))) {B C : ℝ} (hB : ∀ i, ‖Y i‖ ≤ B)
    (hH1 : ∀ i, ∃ (v₀ : H) (g : ℝ → H), MemLp g 2 (volume.restrict (Ioc 0 T)) ∧
      (eLpNorm g 2 (volume.restrict (Ioc 0 T))).toReal ≤ C ∧
      ∀ᵐ t ∂(volume.restrict (Ioc 0 T)), P (Y i t) = v₀ + ∫ s in (0)..t, g s) :
    TotallyBounded (range fun i => P.compLp (Y i)) := by
  set V : Submodule 𝕜 H := LinearMap.range (P : H →ₗ[𝕜] H) with hV
  apply totallyBounded_of_forall_approx
  intro ε hε
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set A : ℝ := T * ‖P‖ * C' with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((A / ε) ^ 2)
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set b : ℝ := ‖P‖ * (Real.sqrt (T / ((N : ℝ) + 1)) * C') with hb
  have hb0 : 0 ≤ b := by positivity
  have hsmall : Real.sqrt T * b < ε := by
    have h1 : Real.sqrt T * b = A / Real.sqrt ((N : ℝ) + 1) := by
      have hTT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
      rw [hb, hA, Real.sqrt_div hT.le]
      calc Real.sqrt T * (‖P‖ * (Real.sqrt T / Real.sqrt ((N : ℝ) + 1) * C'))
          = (Real.sqrt T * Real.sqrt T) * ‖P‖ * C' / Real.sqrt ((N : ℝ) + 1) := by ring
        _ = T * ‖P‖ * C' / Real.sqrt ((N : ℝ) + 1) := by rw [hTT]
    rw [h1, div_lt_iff₀ (Real.sqrt_pos.mpr hN1)]
    have h2 : A / ε < Real.sqrt ((N : ℝ) + 1) := by
      rw [Real.lt_sqrt (by positivity)]; linarith
    rw [div_lt_iff₀ hε] at h2
    linarith
  refine ⟨(LinearMap.range (stepLp N T V) : Set _) ∩ closedBall 0 (‖P‖ * B + ε),
    totallyBounded_inter_closedBall_of_finiteDimensional _ _, ?_⟩
  rintro x ⟨i, rfl⟩
  obtain ⟨v₀, g, hg, hgC, hrep⟩ := hH1 i
  set u : ℝ → H := fun t => v₀ + ∫ s in (0)..t, g s with hu
  let c : Fin (N + 1) → V := fun k => ⟨P (u (node N T k)), LinearMap.mem_range_self _ _⟩
  have hdist : dist (P.compLp (Y i)) (stepLp N T V c) < ε := by
    rw [Lp.dist_def]
    have hae : (⇑(P.compLp (Y i)) - ⇑(stepLp N T V c)) =ᵐ[volume.restrict (Ioc 0 T)]
        fun t => P (Y i t) - P (u (node N T (idx N T t))) := by
      filter_upwards [P.coeFn_compLp' (Y i), coeFn_stepLp N T V c] with t h1 h2
      simp only [Pi.sub_apply, h1, h2, stepFn]
      rfl
    rw [eLpNorm_congr_ae hae]
    have hbound : ∀ᵐ t ∂(volume.restrict (Ioc 0 T)), ‖P (Y i t) - P (u (node N T (idx N T t)))‖ ≤ b := by
      filter_upwards [hrep, ae_restrict_mem measurableSet_Ioc] with t hrt ht
      obtain ⟨h0, h1, h2⟩ := node_spec (N := N) hT ht
      have hPY : P (Y i t) = P (u t) := by
        change P (Y i t) = P (v₀ + ∫ s in (0)..t, g s); rw [← hrt, hP]
      rw [hPY, ← map_sub]
      refine (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      refine (norm_sub_primitive_le hg v₀ h0 h1 ht.2).trans ?_
      have hG0 : 0 ≤ (eLpNorm g 2 (volume.restrict (Ioc 0 T))).toReal := ENNReal.toReal_nonneg
      exact mul_le_mul (Real.sqrt_le_sqrt h2) (hgC.trans (le_max_left _ _)) hG0
        (Real.sqrt_nonneg _)
    have hle := eLpNorm_le_of_ae_bound (p := 2) hbound
    have hμuniv : (volume.restrict (Ioc 0 T)) univ = ENNReal.ofReal T := by
      simp [Real.volume_Ioc]
    rw [hμuniv] at hle
    have hne : ENNReal.ofReal T ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal b ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top
    refine lt_of_le_of_lt (ENNReal.toReal_mono hne hle) ?_
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hT.le,
      ENNReal.toReal_ofReal hb0]
    have : (2 : ℝ≥0∞).toReal⁻¹ = (1 / 2 : ℝ) := by norm_num
    rw [this, ← Real.sqrt_eq_rpow]
    exact hsmall
  refine ⟨stepLp N T V c, ⟨LinearMap.mem_range_self _ _, ?_⟩, hdist⟩
  rw [mem_closedBall, dist_zero_right]
  have h1 : ‖P.compLp (Y i)‖ ≤ ‖P‖ * B :=
    (P.norm_compLp_le _).trans (mul_le_mul_of_nonneg_left (hB i) (norm_nonneg _))
  have h2 := norm_le_norm_add_norm_sub' (stepLp N T V c) (P.compLp (Y i))
  rw [← dist_eq_norm, dist_comm] at h2
  linarith


/-! ### `prop:time-compactness` -/

/-- **`prop:time-compactness` (from spatial screens to spacetime compactness).**  Let `Y_h` be
bounded in `L²(0,T;H)`, let `P_R` be bounded idempotent operators with finite-dimensional range
such that `sup_h ‖(I - P_R)Y_h‖_{L²_t H}` becomes arbitrarily small for large `R`, and suppose
that, for each `R`, `P_R Y_h` is bounded in `H¹(0,T;P_R H)`, i.e. has a representative
`v₀ + ∫_0^t g` with `‖g‖_{L²(0,T)} ≤ C_R` uniformly in `h`.  Then `{Y_h}` is totally bounded in
`L²(0,T;H)`. -/
theorem timeCompactness_totallyBounded {ι : Type*} {T : ℝ} (hT : 0 < T)
    (Y : ι → Lp H 2 (volume.restrict (Ioc 0 T))) (P : ℕ → H →L[𝕜] H)
    (hPfin : ∀ R, FiniteDimensional 𝕜 (LinearMap.range (P R : H →ₗ[𝕜] H)))
    (hPidem : ∀ R x, P R (P R x) = P R x) (hbdd : ∃ B, ∀ i, ‖Y i‖ ≤ B)
    (htail : ∀ ε > 0, ∃ R, ∀ i, ‖Y i - (P R).compLp (Y i)‖ ≤ ε)
    (hH1 : ∀ R, ∃ C, ∀ i, ∃ (v₀ : H) (g : ℝ → H), MemLp g 2 (volume.restrict (Ioc 0 T)) ∧
      (eLpNorm g 2 (volume.restrict (Ioc 0 T))).toReal ≤ C ∧
      ∀ᵐ t ∂(volume.restrict (Ioc 0 T)), P R (Y i t) = v₀ + ∫ s in (0)..t, g s) :
    TotallyBounded (range Y) := by
  obtain ⟨B, hB⟩ := hbdd
  apply totallyBounded_of_forall_approx
  intro ε hε
  obtain ⟨R, hR⟩ := htail (ε / 2) (by positivity)
  obtain ⟨C, hC⟩ := hH1 R
  haveI := hPfin R
  refine ⟨range fun i => (P R).compLp (Y i),
    totallyBounded_of_h1_bounded hT (P R) (hPidem R) Y hB hC, ?_⟩
  rintro x ⟨i, rfl⟩
  refine ⟨(P R).compLp (Y i), ⟨i, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  linarith [hR i]

/-- `prop:time-compactness`, compactness form: with `H` complete, the closure of `{Y_h}` is
compact in `L²(0,T;H)`. -/
theorem timeCompactness_isCompact_closure [CompleteSpace H] {ι : Type*} {T : ℝ} (hT : 0 < T)
    (Y : ι → Lp H 2 (volume.restrict (Ioc 0 T))) (P : ℕ → H →L[𝕜] H)
    (hPfin : ∀ R, FiniteDimensional 𝕜 (LinearMap.range (P R : H →ₗ[𝕜] H)))
    (hPidem : ∀ R x, P R (P R x) = P R x) (hbdd : ∃ B, ∀ i, ‖Y i‖ ≤ B)
    (htail : ∀ ε > 0, ∃ R, ∀ i, ‖Y i - (P R).compLp (Y i)‖ ≤ ε)
    (hH1 : ∀ R, ∃ C, ∀ i, ∃ (v₀ : H) (g : ℝ → H), MemLp g 2 (volume.restrict (Ioc 0 T)) ∧
      (eLpNorm g 2 (volume.restrict (Ioc 0 T))).toReal ≤ C ∧
      ∀ᵐ t ∂(volume.restrict (Ioc 0 T)), P R (Y i t) = v₀ + ∫ s in (0)..t, g s) :
    IsCompact (closure (range Y)) :=
  isCompact_iff_totallyBounded_isComplete.2
    ⟨(timeCompactness_totallyBounded hT Y P hPfin hPidem hbdd htail hH1).closure,
      isClosed_closure.isComplete⟩

/-- `prop:time-compactness`, sequential form: every sequence `Y_{h_n}` has a subsequence
converging in `L²(0,T;H)`. -/
theorem timeCompactness_exists_tendsto_subseq [CompleteSpace H] {ι : Type*} {T : ℝ}
    (hT : 0 < T) (Y : ι → Lp H 2 (volume.restrict (Ioc 0 T))) (P : ℕ → H →L[𝕜] H)
    (hPfin : ∀ R, FiniteDimensional 𝕜 (LinearMap.range (P R : H →ₗ[𝕜] H)))
    (hPidem : ∀ R x, P R (P R x) = P R x) (hbdd : ∃ B, ∀ i, ‖Y i‖ ≤ B)
    (htail : ∀ ε > 0, ∃ R, ∀ i, ‖Y i - (P R).compLp (Y i)‖ ≤ ε)
    (hH1 : ∀ R, ∃ C, ∀ i, ∃ (v₀ : H) (g : ℝ → H), MemLp g 2 (volume.restrict (Ioc 0 T)) ∧
      (eLpNorm g 2 (volume.restrict (Ioc 0 T))).toReal ≤ C ∧
      ∀ᵐ t ∂(volume.restrict (Ioc 0 T)), P R (Y i t) = v₀ + ∫ s in (0)..t, g s)
    (h : ℕ → ι) :
    ∃ (φ : ℕ → ℕ) (Ylim : Lp H 2 (volume.restrict (Ioc 0 T))), StrictMono φ ∧
      Tendsto (fun n => Y (h (φ n))) atTop (𝓝 Ylim) := by
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (timeCompactness_isCompact_closure hT Y P hPfin hPidem hbdd htail hH1).tendsto_subseq
      (x := fun n => Y (h n)) (fun n => subset_closure ⟨h n, rfl⟩)
  exact ⟨φ, a, hφ, hlim⟩

/-! ### The final assertion: tested time-derivative bounds -/

/-- A scalar `L²` function times a fixed vector is in `L²`. -/
theorem memLp_smul_const {w : ℝ → 𝕜} {μ : Measure ℝ} (hw : MemLp w 2 μ) (e : H) :
    MemLp (fun s => w s • e) 2 μ :=
  ((ContinuousLinearMap.id 𝕜 𝕜).smulRight e).comp_memLp' hw

/-- **Final assertion of `prop:time-compactness`.**  Suppose `P_R` has the form
`P_R x = Σ_j φ_{R,j}(x) e_{R,j}` (e.g. `φ_{R,j} = ⟪e_{R,j}, ·⟫` for an orthonormal basis of the
smooth range) and that the time derivative of `Y_h` is bounded in `L²(0,T;V^*)` in the tested
sense: every coefficient `φ_{R,j}(Y_h(t))` has an absolutely continuous representative
`a + ∫_0^t w` with `|w(s)| ≤ ν_{R,j} D_h(s)`, where `ν_{R,j}` is the `V`-norm of the test vector
(e.g. `V = H^m(Σ;E)`) and `‖D_h‖_{L²(0,T)} ≤ C₀` (`D_h(s) = ‖∂_t Y_h(s)‖_{V^*}`).  Then `P_R Y_h`
is bounded in `H¹(0,T;P_R H)`, which is the `H¹` hypothesis of `timeCompactness_totallyBounded`. -/
theorem h1_bound_of_tested_derivative_bound [CompleteSpace H] {ι : Type*} {T : ℝ}
    (Y : ι → Lp H 2 (volume.restrict (Ioc 0 T))) {J : Type*} [Fintype J] (P : H →L[𝕜] H)
    (φ : J → H →L[𝕜] 𝕜) (e : J → H) (hPform : ∀ x, P x = ∑ j, φ j x • e j) (ν : J → ℝ)
    (D : ι → ℝ → ℝ) (hD : ∀ i, MemLp (D i) 2 (volume.restrict (Ioc 0 T))) {C₀ : ℝ}
    (hDC : ∀ i, (eLpNorm (D i) 2 (volume.restrict (Ioc 0 T))).toReal ≤ C₀)
    (htest : ∀ i j, ∃ (a : 𝕜) (w : ℝ → 𝕜), MemLp w 2 (volume.restrict (Ioc 0 T)) ∧
      (∀ᵐ s ∂(volume.restrict (Ioc 0 T)), ‖w s‖ ≤ ν j * D i s) ∧
      ∀ᵐ t ∂(volume.restrict (Ioc 0 T)), φ j (Y i t) = a + ∫ s in (0)..t, w s) :
    ∃ C, ∀ i, ∃ (v₀ : H) (g : ℝ → H), MemLp g 2 (volume.restrict (Ioc 0 T)) ∧
      (eLpNorm g 2 (volume.restrict (Ioc 0 T))).toReal ≤ C ∧
      ∀ᵐ t ∂(volume.restrict (Ioc 0 T)), P (Y i t) = v₀ + ∫ s in (0)..t, g s := by
  classical
  refine ⟨∑ j, ‖e j‖ * (|ν j| * max C₀ 0), fun i => ?_⟩
  choose a w hw hwb hrep using htest i
  refine ⟨∑ j, a j • e j, fun s => ∑ j, w j s • e j, ?_, ?_, ?_⟩
  · exact memLp_finsetSum _ fun j _ => memLp_smul_const (hw j) (e j)
  · have hle : eLpNorm (fun s => ∑ j, w j s • e j) 2 (volume.restrict (Ioc 0 T)) ≤
        ∑ j, ENNReal.ofReal (‖e j‖ * (|ν j| * max C₀ 0)) := by
      have hsum : (fun s => ∑ j, w j s • e j) = ∑ j, fun s => w j s • e j := by
        funext s; simp
      rw [hsum]
      refine (eLpNorm_sum_le (fun j _ => (memLp_smul_const (hw j) (e j)).1) (by norm_num)).trans ?_
      refine Finset.sum_le_sum fun j _ => ?_
      have h1 : eLpNorm (fun s => w j s • e j) 2 (volume.restrict (Ioc 0 T)) ≤
          ENNReal.ofReal (‖e j‖ * |ν j|) * eLpNorm (D i) 2 (volume.restrict (Ioc 0 T)) := by
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ 2
        filter_upwards [hwb j] with s hs
        rw [norm_smul, Real.norm_eq_abs]
        calc ‖w j s‖ * ‖e j‖ ≤ (|ν j| * |D i s|) * ‖e j‖ := by
              refine mul_le_mul_of_nonneg_right (hs.trans ?_) (norm_nonneg _)
              rw [← abs_mul]; exact le_abs_self _
          _ = ‖e j‖ * |ν j| * |D i s| := by ring
      refine h1.trans ?_
      have hDle : eLpNorm (D i) 2 (volume.restrict (Ioc 0 T)) ≤ ENNReal.ofReal (max C₀ 0) := by
        rw [← ENNReal.ofReal_toReal (hD i).eLpNorm_ne_top]
        exact ENNReal.ofReal_le_ofReal ((hDC i).trans (le_max_left _ _))
      calc ENNReal.ofReal (‖e j‖ * |ν j|) * eLpNorm (D i) 2 (volume.restrict (Ioc 0 T))
          ≤ ENNReal.ofReal (‖e j‖ * |ν j|) * ENNReal.ofReal (max C₀ 0) := by gcongr
        _ = ENNReal.ofReal (‖e j‖ * (|ν j| * max C₀ 0)) := by
            rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]
    have hne : ∑ j, ENNReal.ofReal (‖e j‖ * (|ν j| * max C₀ 0)) ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun j _ => ENNReal.ofReal_ne_top
    refine (ENNReal.toReal_mono hne hle).trans (le_of_eq ?_)
    rw [ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)]
    exact Finset.sum_congr rfl fun j _ => ENNReal.toReal_ofReal (by positivity)
  · have hall : ∀ᵐ t ∂(volume.restrict (Ioc 0 T)),
        ∀ j, φ j (Y i t) = a j + ∫ s in (0)..t, w j s := ae_all_iff.2 hrep
    filter_upwards [hall, ae_restrict_mem measurableSet_Ioc] with t ht htI
    rw [hPform]
    have hint : ∀ j, IntervalIntegrable (fun s => w j s • e j) volume 0 t := fun j =>
      intervalIntegrable_of_memLp (memLp_smul_const (hw j) (e j)) le_rfl htI.1.le htI.2
    rw [intervalIntegral.integral_finsetSum fun j _ => hint j, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ht j, intervalIntegral.integral_smul_const, add_smul]

end

end BochnerTimeCompactness
end RenewalGeometry

/-! ### Non-vacuity -/

namespace RenewalGeometry.BochnerTimeCompactness

open MeasureTheory Set

/-- The ramp `t ↦ t` is in `L²(0,1)`. -/
theorem memLp_ramp : MemLp (fun t : ℝ => t) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  refine MemLp.of_bound (by fun_prop) 1 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [ht.1, ht.2]

theorem compLp_id_eq {μ : Measure ℝ} (f : Lp ℝ 2 μ) : (ContinuousLinearMap.id ℝ ℝ).compLp f = f :=
  Lp.ext <| by
    filter_upwards [(ContinuousLinearMap.id ℝ ℝ).coeFn_compLp' f] with a ha
    simpa using ha

/-- Non-vacuity of `timeCompactness_totallyBounded`: the family `Y_i(t) = sin(i) t` in
`L²(0,1;ℝ)` with the rank-one projections `P_R = I` satisfies all hypotheses. -/
example : TotallyBounded (range fun i : ℕ =>
    Real.sin i • (memLp_ramp.toLp (fun t : ℝ => t))) := by
  refine timeCompactness_totallyBounded (𝕜 := ℝ) zero_lt_one _ (fun _ => ContinuousLinearMap.id ℝ ℝ)
    (fun _ => inferInstance) (fun _ _ => rfl) ⟨‖memLp_ramp.toLp (fun t : ℝ => t)‖, fun i => ?_⟩
    (fun ε hε => ⟨0, fun i => by rw [compLp_id_eq, sub_self, norm_zero]; exact hε.le⟩) (fun _ => ⟨1, fun i => ?_⟩)
  · rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  · refine ⟨0, fun _ => Real.sin i, memLp_const _, ?_, ?_⟩
    · have := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (f := fun _ : ℝ => Real.sin (i : ℝ)) (C := 1)
        (Eventually.of_forall fun _ => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
      have hu : (volume.restrict (Ioc (0 : ℝ) 1)) univ = 1 := by simp [Real.volume_Ioc]
      rw [hu] at this
      simp only [ENNReal.one_rpow, one_mul, ENNReal.ofReal_one] at this
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    · filter_upwards [Lp.coeFn_smul (Real.sin (i : ℝ)) (memLp_ramp.toLp (fun t : ℝ => t)),
        memLp_ramp.coeFn_toLp] with t h1 h2
      simp [h1, h2, intervalIntegral.integral_const, mul_comm]

end RenewalGeometry.BochnerTimeCompactness
