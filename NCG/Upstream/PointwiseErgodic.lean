/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The pointwise (Birkhoff) ergodic theorem for bounded observables

The stationary-ergodic ingredient of `cor:self-averaged-flat`
(flagship), proved from scratch since Mathlib currently provides only
the von Neumann mean ergodic theorem:

* `maxSum` — the running maximum `Mₙ = max₀≤k≤n Sₖ` of the Birkhoff
  sums, with `M₀ = S₀ = 0`;
* `maximal_ergodic` — **Garsia's maximal ergodic lemma**: for an
  integrable observable, `0 ≤ ∫_E f` on the set
  `E = {x | ∃ n, 0 < Mₙ(x)}` where some Birkhoff sum is positive;
* `birkhoff_ergodic_ae` — the **pointwise ergodic theorem** for a
  bounded measurable observable under an ergodic measure-preserving
  map on a probability space: almost surely the Birkhoff averages
  converge to the space mean `∫ f`.

The bounded case suffices for the flagship application: renewal
direction records are unit vectors, so the second-moment observables
`θᵢθⱼ` are bounded by one.  The proof follows the classical route:
Garsia's inequality `Mₙ ≤ f + Mₙ∘T` on `{Mₙ > 0}` gives the maximal
lemma; the limsup of the averages is an exactly `T`-invariant bounded
measurable function, hence a.e. constant by ergodicity; and the
maximal lemma applied to `f − β` and `α − f` pins both the limsup and
liminf constants at `∫ f`.
-/

namespace NCG

open Filter MeasureTheory Set

variable {Ω : Type*} {T : Ω → Ω} {f : Ω → ℝ}

/-! ## The running maximum of Birkhoff sums -/

/-- The running maximum `Mₙ = max_{0 ≤ k ≤ n} Sₖ` of Birkhoff sums,
with `M₀ = S₀ = 0`. -/
noncomputable def maxSum (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max (birkhoffSum T f (n + 1) x) (maxSum T f n x)

@[simp] theorem maxSum_zero (x : Ω) : maxSum T f 0 x = 0 := rfl

theorem maxSum_succ (n : ℕ) (x : Ω) :
    maxSum T f (n + 1) x
      = max (birkhoffSum T f (n + 1) x) (maxSum T f n x) := rfl

theorem maxSum_nonneg (n : ℕ) (x : Ω) : 0 ≤ maxSum T f n x := by
  induction n with
  | zero => simp
  | succ k ih => exact le_trans ih (le_max_right _ _)

theorem maxSum_mono (x : Ω) : Monotone fun n => maxSum T f n x := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [maxSum_succ]
  exact le_max_right _ _

theorem birkhoffSum_le_maxSum {k n : ℕ} (hk : k ≤ n) (x : Ω) :
    birkhoffSum T f k x ≤ maxSum T f n x := by
  induction n with
  | zero =>
    interval_cases k
    simp [birkhoffSum_zero]
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hk' | hk'
    · exact le_trans (ih (Nat.lt_succ_iff.mp hk'))
        (maxSum_mono x (Nat.le_succ m))
    · have hkeq : k = m + 1 := le_antisymm hk hk'
      subst hkeq
      rw [maxSum_succ]
      exact le_max_left _ _

theorem maxSum_measurable [MeasurableSpace Ω]
    (hT : Measurable T) (hf : Measurable f)
    (n : ℕ) : Measurable (maxSum T f n) := by
  induction n with
  | zero => simp only [maxSum]; exact measurable_const
  | succ k ih =>
    have hS : Measurable (birkhoffSum T f (k + 1)) := by
      unfold birkhoffSum
      exact Finset.measurable_sum _ fun j _ =>
        hf.comp (hT.iterate j)
    exact hS.max ih

theorem abs_birkhoffSum_le {C : ℝ} (hb : ∀ x, |f x| ≤ C)
    (n : ℕ) (x : Ω) : |birkhoffSum T f n x| ≤ n * C := by
  unfold birkhoffSum
  calc |∑ k ∈ Finset.range n, f (T^[k] x)|
      ≤ ∑ k ∈ Finset.range n, |f (T^[k] x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, C :=
        Finset.sum_le_sum fun k _ => hb _
    _ = n * C := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem maxSum_le {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C)
    (n : ℕ) (x : Ω) : maxSum T f n x ≤ n * C := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [maxSum_succ]
    refine max_le ?_ ?_
    · exact le_trans (le_abs_self _)
        (abs_birkhoffSum_le hb (k + 1) x)
    · refine le_trans ih ?_
      push_cast
      nlinarith

/-- The running maximum is attained at some index. -/
theorem maxSum_exists_index (n : ℕ) (x : Ω) :
    ∃ k ≤ n, maxSum T f n x = birkhoffSum T f k x := by
  induction n with
  | zero => exact ⟨0, le_rfl, by simp [birkhoffSum_zero]⟩
  | succ m ih =>
    obtain ⟨k, hk, hkeq⟩ := ih
    rw [maxSum_succ]
    rcases max_cases (birkhoffSum T f (m + 1) x) (maxSum T f m x)
      with ⟨heq, _⟩ | ⟨heq, _⟩
    · exact ⟨m + 1, le_rfl, heq⟩
    · exact ⟨k, le_trans hk (Nat.le_succ m), heq.trans hkeq⟩

/-- **Garsia's inequality**: away from `0`, the running maximum obeys
`Mₙ(x) ≤ f(x) + Mₙ(T x)`. -/
theorem maxSum_le_add_comp {n : ℕ} {x : Ω}
    (hpos : 0 < maxSum T f n x) :
    maxSum T f n x ≤ f x + maxSum T f n (T x) := by
  obtain ⟨k, hk, hkeq⟩ := maxSum_exists_index (T := T) (f := f) n x
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hkeq, birkhoffSum_zero] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  rw [hkeq, birkhoffSum_succ' T f j x]
  have hj : j ≤ n := le_trans (Nat.le_succ j) hk
  exact add_le_add le_rfl
    (birkhoffSum_le_maxSum (T := T) (f := f) hj (T x))

/-! ## The maximal ergodic lemma -/

section Maximal

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem integrable_of_bounded {C : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ C) : Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  refine MeasureTheory.HasFiniteIntegral.of_bounded (C := C) ?_
  exact MeasureTheory.ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hb x

theorem integrable_maxSum {C : ℝ} (hT : Measurable T)
    (hf : Measurable f) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C)
    (n : ℕ) : Integrable (maxSum T f n) μ := by
  refine integrable_of_bounded (maxSum_measurable hT hf n)
    (C := n * C) fun x => ?_
  rw [abs_of_nonneg (maxSum_nonneg n x)]
  exact maxSum_le hC hb n x

/-- **Garsia's maximal ergodic lemma** (`lem:app-*` input for the
stationary-ergodic self-averaging): the integral of a bounded
observable over the set where some Birkhoff sum is positive is
nonnegative. -/
theorem maximal_ergodic {C : ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Measurable f)
    (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    0 ≤ ∫ x in {x | ∃ n, 0 < maxSum T f n x}, f x ∂μ := by
  have hmT : Measurable T := hT.measurable
  have hintf : Integrable f μ := integrable_of_bounded hf hb
  have hintM : ∀ n, Integrable (maxSum T f n) μ :=
    integrable_maxSum hmT hf hC hb
  have hintMT : ∀ n, Integrable (fun x => maxSum T f n (T x)) μ := by
    intro n
    have h := hintM n
    rw [← hT.map_eq] at h
    exact MeasureTheory.Integrable.comp_measurable h hmT
  set En : ℕ → Set Ω := fun n => {x | 0 < maxSum T f n x}
    with hEn
  have hEnm : ∀ n, MeasurableSet (En n) := fun n =>
    measurableSet_lt measurable_const (maxSum_measurable hmT hf n)
  -- the per-`n` maximal inequality
  have hstep : ∀ n, 0 ≤ ∫ x in En n, f x ∂μ := by
    intro n
    have hkey : ∀ x ∈ En n,
        maxSum T f n x - maxSum T f n (T x) ≤ f x := by
      intro x hx
      have := maxSum_le_add_comp (T := T) (f := f) hx
      linarith
    have h1 : (∫ x in En n,
          (maxSum T f n x - maxSum T f n (T x)) ∂μ)
        ≤ ∫ x in En n, f x ∂μ := by
      refine setIntegral_mono_on
        (((hintM n).sub (hintMT n)).integrableOn)
        hintf.integrableOn (hEnm n) hkey
    have h2 : (∫ x in En n, maxSum T f n x ∂μ)
        = ∫ x, maxSum T f n x ∂μ := by
      rw [← MeasureTheory.integral_add_compl (hEnm n) (hintM n)]
      have hzero : (∫ x in (En n)ᶜ, maxSum T f n x ∂μ) = 0 := by
        refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
          fun x hx => ?_
        have hnotpos : ¬ 0 < maxSum T f n x := hx
        exact le_antisymm (not_lt.mp hnotpos) (maxSum_nonneg n x)
      rw [hzero, add_zero]
    have h3 : (∫ x in En n, maxSum T f n (T x) ∂μ)
        ≤ ∫ x, maxSum T f n (T x) ∂μ := by
      refine MeasureTheory.setIntegral_le_integral (hintMT n) ?_
      exact MeasureTheory.ae_of_all _ fun x => maxSum_nonneg n (T x)
    have h4 : (∫ x, maxSum T f n (T x) ∂μ)
        = ∫ x, maxSum T f n x ∂μ := by
      conv_rhs => rw [← hT.map_eq]
      rw [integral_map hmT.aemeasurable
        ((maxSum_measurable hmT hf n).aestronglyMeasurable.mono_ac
          (by rw [hT.map_eq]))]
    have h5 : (∫ x in En n,
          (maxSum T f n x - maxSum T f n (T x)) ∂μ)
        = (∫ x in En n, maxSum T f n x ∂μ)
          - ∫ x in En n, maxSum T f n (T x) ∂μ :=
      MeasureTheory.integral_sub (hintM n).integrableOn
        (hintMT n).integrableOn
    have h6 : 0 ≤ (∫ x in En n,
        (maxSum T f n x - maxSum T f n (T x)) ∂μ) := by
      rw [h5, h2]
      have := le_trans h3 (le_of_eq h4)
      linarith
    linarith
  -- pass to the union
  have hunion : {x | ∃ n, 0 < maxSum T f n x} = ⋃ n, En n := by
    ext x
    simp [hEn]
  have hmono : Monotone En := by
    intro a b hab x hx
    exact lt_of_lt_of_le hx (maxSum_mono x hab)
  have htend := MeasureTheory.tendsto_setIntegral_of_monotone
    hEnm hmono hintf.integrableOn
  rw [hunion]
  exact ge_of_tendsto htend
    (Filter.Eventually.of_forall hstep)

end Maximal

/-! ## Limsup and liminf congruence for bounded sequences -/

theorem bddAbove_of_abs_le {u : ℕ → ℝ} {D : ℝ} (hu : ∀ n, |u n| ≤ D) :
    Filter.IsBoundedUnder (· ≤ ·) atTop u :=
  Filter.isBoundedUnder_of ⟨D, fun n =>
    le_trans (le_abs_self _) (hu n)⟩

theorem bddBelow_of_abs_le {u : ℕ → ℝ} {D : ℝ} (hu : ∀ n, |u n| ≤ D) :
    Filter.IsBoundedUnder (· ≥ ·) atTop u :=
  Filter.isBoundedUnder_of ⟨-D, fun n => by
    have := abs_le.mp (hu n)
    linarith [this.1]⟩

theorem limsup_le_limsup_of_tendsto_sub {u v : ℕ → ℝ} {D : ℝ}
    (h : Tendsto (fun n => u n - v n) atTop (nhds 0))
    (hu : ∀ n, |u n| ≤ D) (hv : ∀ n, |v n| ≤ D) :
    limsup u atTop ≤ limsup v atTop := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev1 : ∀ᶠ n in atTop, v n < limsup v atTop + ε / 2 :=
    eventually_lt_of_limsup_lt (by linarith) (bddAbove_of_abs_le hv)
  have hev2 : ∀ᶠ n in atTop, ‖u n - v n‖ < ε / 2 :=
    NormedAddGroup.tendsto_nhds_zero.mp h (ε / 2)
      (by positivity)
  refine limsup_le_of_le
    ((bddBelow_of_abs_le hu).isCoboundedUnder_le) ?_
  filter_upwards [hev1, hev2] with n h1 h2
  rw [Real.norm_eq_abs] at h2
  have h3 : u n - v n < ε / 2 := lt_of_le_of_lt (le_abs_self _) h2
  linarith

theorem limsup_eq_of_tendsto_sub {u v : ℕ → ℝ} {D : ℝ}
    (h : Tendsto (fun n => u n - v n) atTop (nhds 0))
    (hu : ∀ n, |u n| ≤ D) (hv : ∀ n, |v n| ≤ D) :
    limsup u atTop = limsup v atTop := by
  refine le_antisymm (limsup_le_limsup_of_tendsto_sub h hu hv) ?_
  refine limsup_le_limsup_of_tendsto_sub ?_ hv hu
  have := h.neg
  simpa [neg_sub] using this

theorem liminf_le_liminf_of_tendsto_sub {u v : ℕ → ℝ} {D : ℝ}
    (h : Tendsto (fun n => u n - v n) atTop (nhds 0))
    (hu : ∀ n, |u n| ≤ D) (hv : ∀ n, |v n| ≤ D) :
    liminf v atTop ≤ liminf u atTop := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlow : liminf v atTop - ε ≤ liminf u atTop := by
    have hev1 : ∀ᶠ n in atTop, liminf v atTop - ε / 2 < v n :=
      eventually_lt_of_lt_liminf (by linarith)
        (bddBelow_of_abs_le hv)
    have hev2 : ∀ᶠ n in atTop, ‖u n - v n‖ < ε / 2 :=
      NormedAddGroup.tendsto_nhds_zero.mp h (ε / 2)
        (by positivity)
    refine le_liminf_of_le
      ((bddAbove_of_abs_le hu).isCoboundedUnder_ge) ?_
    filter_upwards [hev1, hev2] with n h1 h2
    rw [Real.norm_eq_abs] at h2
    have h4 : -(ε / 2) < u n - v n := (abs_lt.mp h2).1
    linarith
  linarith

theorem liminf_eq_of_tendsto_sub {u v : ℕ → ℝ} {D : ℝ}
    (h : Tendsto (fun n => u n - v n) atTop (nhds 0))
    (hu : ∀ n, |u n| ≤ D) (hv : ∀ n, |v n| ≤ D) :
    liminf u atTop = liminf v atTop := by
  refine le_antisymm ?_ (liminf_le_liminf_of_tendsto_sub h hu hv)
  have h2 : Tendsto (fun n => v n - u n) atTop (nhds 0) := by
    have := h.neg
    simpa [neg_sub] using this
  exact liminf_le_liminf_of_tendsto_sub h2 hv hu

/-! ## The pointwise ergodic theorem -/

section Birkhoff

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem birkhoffSum_measurable
    (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffSum T f n) := by
  unfold birkhoffSum
  exact Finset.measurable_sum _ fun j _ => hf.comp (hT.iterate j)

omit [MeasurableSpace Ω] in
theorem abs_birkhoffAverage_le {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ C) (n : ℕ) (x : Ω) :
    |birkhoffAverage ℝ T f n x| ≤ C := by
  change |(n : ℝ)⁻¹ • birkhoffSum T f n x| ≤ C
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hC]
  · have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    rw [smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hn0)]
    calc (n:ℝ)⁻¹ * |birkhoffSum T f n x|
        ≤ (n:ℝ)⁻¹ * (n * C) :=
          mul_le_mul_of_nonneg_left (abs_birkhoffSum_le hb n x)
            (inv_pos.mpr hn0).le
      _ = C := by field_simp

omit [MeasurableSpace Ω] in
theorem birkhoffSum_const_shift (β : ℝ) (n : ℕ) (x : Ω) :
    birkhoffSum T (fun y => f y - β) n x
      = birkhoffSum T f n x - n * β := by
  unfold birkhoffSum
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

/-- **The pointwise (Birkhoff) ergodic theorem** for bounded
observables (`cor:self-averaged-flat`, stationary-ergodic phase):
under an ergodic measure-preserving map on a probability space, the
Birkhoff averages of a bounded measurable observable converge almost
surely to the space mean. -/
theorem birkhoff_ergodic_ae {C : ℝ} (hT : Ergodic T μ)
    (hf : Measurable f) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x)
      atTop (nhds (∫ x, f x ∂μ)) := by
  have hmT : Measurable T := hT.toMeasurePreserving.measurable
  have hAmeas : ∀ n, Measurable (birkhoffAverage ℝ T f n) := by
    intro n
    change Measurable fun x => (n : ℝ)⁻¹ • birkhoffSum T f n x
    exact (birkhoffSum_measurable hmT hf n).const_smul ((n : ℝ)⁻¹)
  have hAbnd : ∀ (x : Ω) (n : ℕ),
      |birkhoffAverage ℝ T f n x| ≤ C :=
    fun x n => abs_birkhoffAverage_le hC hb n x
  have hrange : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨C, by rintro y ⟨x, rfl⟩; rw [Real.norm_eq_abs]; exact hb x⟩
  have hdiff : ∀ x, Tendsto (fun n =>
      birkhoffAverage ℝ T f n (T x) - birkhoffAverage ℝ T f n x)
      atTop (nhds 0) :=
    fun x => tendsto_birkhoffAverage_apply_sub_birkhoffAverage'
      (𝕜 := ℝ) hrange T x
  set LS : Ω → ℝ := fun x =>
    limsup (fun n => birkhoffAverage ℝ T f n x) atTop with hLS
  set LI : Ω → ℝ := fun x =>
    liminf (fun n => birkhoffAverage ℝ T f n x) atTop with hLI
  have hLSmeas : Measurable LS := Measurable.limsup hAmeas
  have hLImeas : Measurable LI := Measurable.liminf hAmeas
  have hLSinv : ∀ x, LS (T x) = LS x := fun x =>
    limsup_eq_of_tendsto_sub (hdiff x) (fun n => hAbnd (T x) n)
      (fun n => hAbnd x n)
  have hLIinv : ∀ x, LI (T x) = LI x := fun x =>
    liminf_eq_of_tendsto_sub (hdiff x) (fun n => hAbnd (T x) n)
      (fun n => hAbnd x n)
  obtain ⟨cs, hcs⟩ := hT.ae_eq_const_of_ae_eq_comp₀
    hLSmeas.nullMeasurable
    (Filter.Eventually.of_forall hLSinv)
  obtain ⟨ci, hci⟩ := hT.ae_eq_const_of_ae_eq_comp₀
    hLImeas.nullMeasurable
    (Filter.Eventually.of_forall hLIinv)
  -- `β < cs → β ≤ ∫ f` via the maximal lemma on `f − β`
  have hupper : ∀ β, β < cs → β ≤ ∫ x, f x ∂μ := by
    intro β hβ
    have hgmeas : Measurable fun y => f y - β :=
      hf.sub measurable_const
    have hgb : ∀ y, |f y - β| ≤ C + |β| := fun y =>
      le_trans (abs_sub _ _) (by gcongr; exact hb y)
    have hae : ∀ᵐ x ∂μ,
        x ∈ {x | ∃ n, 0 < maxSum T (fun y => f y - β) n x} := by
      filter_upwards [hcs] with x hx
      have hfreq : ∃ᶠ n in atTop,
          β < birkhoffAverage ℝ T f n x := by
        refine frequently_lt_of_lt_limsup
          ((bddBelow_of_abs_le fun n =>
            hAbnd x n).isCoboundedUnder_le) ?_
        rw [show limsup (fun n => birkhoffAverage ℝ T f n x) atTop
            = LS x from rfl, hx]
        exact hβ
      obtain ⟨n, hn1, hnlt⟩ := Filter.frequently_atTop.mp hfreq 1
      have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
      have hS : (n:ℝ) * β < birkhoffSum T f n x := by
        have h1 : β < (n:ℝ)⁻¹ * birkhoffSum T f n x := by
          have h2 := hnlt
          rw [show birkhoffAverage ℝ T f n x
              = (n : ℝ)⁻¹ • birkhoffSum T f n x from rfl,
            smul_eq_mul] at h2
          exact h2
        exact (lt_inv_mul_iff₀ hn0).mp h1
      refine ⟨n, lt_of_lt_of_le ?_
        (birkhoffSum_le_maxSum le_rfl x)⟩
      rw [birkhoffSum_const_shift]
      linarith
    have hmax := maximal_ergodic (μ := μ) hT.toMeasurePreserving
      hgmeas (C := C + |β|) (by positivity) hgb
    have hEm : MeasurableSet
        {x | ∃ n, 0 < maxSum T (fun y => f y - β) n x} := by
      rw [Set.setOf_exists]
      exact MeasurableSet.iUnion fun n =>
        measurableSet_lt measurable_const
          (maxSum_measurable hmT hgmeas n)
    have hcompl : μ {x | ∃ n,
        0 < maxSum T (fun y => f y - β) n x}ᶜ = 0 := by
      rw [Set.compl_def]
      exact MeasureTheory.ae_iff.mp hae
    have hfull : (∫ x in
          {x | ∃ n, 0 < maxSum T (fun y => f y - β) n x},
          (f x - β) ∂μ) = ∫ x, (f x - β) ∂μ := by
      conv_rhs => rw [← MeasureTheory.integral_add_compl hEm
        (integrable_of_bounded hgmeas hgb)]
      rw [MeasureTheory.setIntegral_measure_zero _ hcompl, add_zero]
    have hint : (∫ x, (f x - β) ∂μ) = (∫ x, f x ∂μ) - β := by
      rw [MeasureTheory.integral_sub
        (integrable_of_bounded hf hb) (integrable_const β)]
      simp
    rw [hfull, hint] at hmax
    linarith
  -- `ci < α → ∫ f ≤ α` via the maximal lemma on `α − f`
  have hlower : ∀ α, ci < α → (∫ x, f x ∂μ) ≤ α := by
    intro α hα
    have hgmeas : Measurable fun y => α - f y :=
      measurable_const.sub hf
    have hgb : ∀ y, |α - f y| ≤ C + |α| := fun y =>
      le_trans (abs_sub _ _) (by
        rw [add_comm]
        gcongr
        exact hb y)
    have hae : ∀ᵐ x ∂μ,
        x ∈ {x | ∃ n, 0 < maxSum T (fun y => α - f y) n x} := by
      filter_upwards [hci] with x hx
      have hfreq : ∃ᶠ n in atTop,
          birkhoffAverage ℝ T f n x < α := by
        refine frequently_lt_of_liminf_lt
          ((bddAbove_of_abs_le fun n =>
            hAbnd x n).isCoboundedUnder_ge) ?_
        rw [show liminf (fun n => birkhoffAverage ℝ T f n x) atTop
            = LI x from rfl, hx]
        exact hα
      obtain ⟨n, hn1, hnlt⟩ := Filter.frequently_atTop.mp hfreq 1
      have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
      have hS : birkhoffSum T f n x < (n:ℝ) * α := by
        have h1 : (n:ℝ)⁻¹ * birkhoffSum T f n x < α := by
          have h2 := hnlt
          rw [show birkhoffAverage ℝ T f n x
              = (n : ℝ)⁻¹ • birkhoffSum T f n x from rfl,
            smul_eq_mul] at h2
          exact h2
        exact (inv_mul_lt_iff₀ hn0).mp h1
      refine ⟨n, lt_of_lt_of_le ?_
        (birkhoffSum_le_maxSum le_rfl x)⟩
      have hsum : birkhoffSum T (fun y => α - f y) n x
          = (n:ℝ) * α - birkhoffSum T f n x := by
        unfold birkhoffSum
        rw [Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
      rw [hsum]
      linarith
    have hmax := maximal_ergodic (μ := μ) hT.toMeasurePreserving
      hgmeas (C := C + |α|) (by positivity) hgb
    have hEm : MeasurableSet
        {x | ∃ n, 0 < maxSum T (fun y => α - f y) n x} := by
      rw [Set.setOf_exists]
      exact MeasurableSet.iUnion fun n =>
        measurableSet_lt measurable_const
          (maxSum_measurable hmT hgmeas n)
    have hcompl : μ {x | ∃ n,
        0 < maxSum T (fun y => α - f y) n x}ᶜ = 0 := by
      rw [Set.compl_def]
      exact MeasureTheory.ae_iff.mp hae
    have hfull : (∫ x in
          {x | ∃ n, 0 < maxSum T (fun y => α - f y) n x},
          (α - f x) ∂μ) = ∫ x, (α - f x) ∂μ := by
      conv_rhs => rw [← MeasureTheory.integral_add_compl hEm
        (integrable_of_bounded hgmeas hgb)]
      rw [MeasureTheory.setIntegral_measure_zero _ hcompl, add_zero]
    have hint : (∫ x, (α - f x) ∂μ) = α - ∫ x, f x ∂μ := by
      rw [MeasureTheory.integral_sub (integrable_const α)
        (integrable_of_bounded hf hb)]
      simp
    rw [hfull, hint] at hmax
    linarith
  -- combine: `∫f ≤ ci ≤ cs ≤ ∫f`
  have hcile : ci ≤ cs := by
    obtain ⟨x, hx, hx2⟩ := (hcs.and hci).exists
    have hx3 : LS x = cs := hx
    have hx4 : LI x = ci := hx2
    rw [← hx3, ← hx4]
    exact liminf_le_limsup (bddAbove_of_abs_le fun n => hAbnd x n)
      (bddBelow_of_abs_le fun n => hAbnd x n)
  have hcint : cs ≤ ∫ x, f x ∂μ := by
    by_contra hcon
    push Not at hcon
    have := hupper (((∫ x, f x ∂μ) + cs) / 2) (by linarith)
    linarith
  have hciint : (∫ x, f x ∂μ) ≤ ci := by
    by_contra hcon
    push Not at hcon
    have := hlower ((ci + ∫ x, f x ∂μ) / 2) (by linarith)
    linarith
  have hcseq : cs = ∫ x, f x ∂μ := le_antisymm hcint
    (le_trans hciint hcile)
  have hcieq : ci = ∫ x, f x ∂μ := le_antisymm
    (le_trans hcile hcint) hciint
  filter_upwards [hcs, hci] with x hx hx2
  refine tendsto_of_liminf_eq_limsup ?_ ?_
    (bddAbove_of_abs_le fun n => hAbnd x n)
    (bddBelow_of_abs_le fun n => hAbnd x n)
  · have hx4 : LI x = ci := hx2
    rw [show liminf (fun n => birkhoffAverage ℝ T f n x) atTop
        = LI x from rfl, hx4, hcieq]
  · have hx3 : LS x = cs := hx
    rw [show limsup (fun n => birkhoffAverage ℝ T f n x) atTop
        = LS x from rfl, hx3, hcseq]

/-- **Stationary-ergodic self-averaging**
(`cor:self-averaged-flat`, ergodic phase): for an ergodic
measure-preserving renewal shift and bounded measurable direction
records, almost surely every entry of the empirical second moment
converges to the entry of the limit moment `∫ θθᵀ`. -/
theorem ergodic_second_moment (hT : Ergodic T μ)
    {θ : Ω → Fin 3 → ℝ} (hθ : Measurable θ)
    (hθb : ∀ ω i, |θ ω i| ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ i j : Fin 3,
      Tendsto (fun n =>
          birkhoffAverage ℝ T (fun ω => θ ω i * θ ω j) n ω)
        atTop (nhds (∫ ω, θ ω i * θ ω j ∂μ)) := by
  rw [MeasureTheory.ae_all_iff]
  intro i
  rw [MeasureTheory.ae_all_iff]
  intro j
  refine birkhoff_ergodic_ae hT
    (((measurable_pi_apply i).comp hθ).mul
      ((measurable_pi_apply j).comp hθ)) zero_le_one fun ω => ?_
  rw [abs_mul]
  calc |θ ω i| * |θ ω j| ≤ 1 * 1 :=
      mul_le_mul (hθb ω i) (hθb ω j) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end Birkhoff

end NCG
