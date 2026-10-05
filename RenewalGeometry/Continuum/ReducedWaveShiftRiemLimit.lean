/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveShiftCurvature
import RenewalGeometry.Continuum.ReducedWaveShiftLimit

/-!
# `thm:hyperbolic`, curvature clause: the limit of `Riem(g_h)` is `Riem(g)`

(Einstein–Standard-Model action-closure manuscript, "Common-slab metric stability".)  The limit
metric `g` of `common_slab_limit_sh` lies in `C_tH^{s-1} ∩ C¹_tH^{s-2}`: it is `C¹` on the slab,
but its second time derivative exists only in `L¹_tH^{s-3}`.  Its curvature is the distributional
Riemann tensor of a `C¹` metric,

`⟨Riem(g)^a_{bcd}, φ⟩ = ∫∫ (-Γ^a_{db}∂_cφ + Γ^a_{cb}∂_dφ + (Γ^a_{ce}Γ^e_{db} - Γ^a_{de}Γ^e_{cb})φ)`,

`Γ = Γ(g)` the Christoffel symbols of `g` (`riemDist`), tested on smooth functions on the
cylinder `(0, T) × 𝕋³` (`IsCylTest`: spatially periodic, compact time support).

* `slabInt`, `slabInt_pd_mul` — integration by parts on `(0, T) × 𝕋³`;
* `slabInt_riemF` — for smooth metrics the pairing of `RiemF` is `riemDist` (no `∂²g`);
* `UConv`, `tendsto_riemDist` — `C⁰` convergence of the Christoffel symbols gives convergence of
  the distributional curvature;
* `exists_L1_limit` — `L¹_t`-Cauchy families of continuous `E`-valued curves converge in
  `L¹((0, T); E)`;
* `weak_deriv_of_L2_limit` — `L²` limits of slice derivatives are the weak derivatives of the limit
  (the `C_tH^m` limits of `common_slab_limit_sh` are Sobolev functions with those derivatives);
* **`riem_limit_sh`** — under the hypotheses of `thm:hyperbolic` (`MetricHypSh`), the limit metric
  `g` is `C¹` on the open slab with inverse `g⁻¹` (`g_h → g`, `∂g_h → ∂g`, `g_h⁻¹ → g⁻¹` uniformly),
  every word derivative `∂^w Riem(g_h)`, `|w| ≤ s - 3`, converges in `L¹((0, T); L²(𝕋³))`, the
  limits are the weak spatial derivatives of the `w = ∅` limit `R`, and `R = Riem(g)` in the sense
  of distributions on `(0, T) × 𝕋³`: `Riem(g_h) → Riem(g)` in `L¹_tH^{s-3}`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Interval

noncomputable section

namespace RenewalGeometry.ReducedWaveShift

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg ReducedWaveStab SlabWaveShift

set_option linter.unusedSectionVars false

/-! ### Slab integrals and integration by parts on `(0, T) × 𝕋³` -/

/-- `∫₀ᵀ ∫_{[0,1]³} f(t, y) dy dt`. -/
def slabInt (T : ℝ) (f : X → ℝ) : ℝ :=
  ∫ t in (0)..T, ∫ y in Icc (0 : Fin 3 → ℝ) 1, f (Fin.cons t y)

theorem mem_slab_of_uIoc {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Ι 0 T) : t ∈ Icc 0 T := by
  rw [uIoc_of_le hT] at ht; exact ⟨ht.1.le, ht.2⟩

theorem intervalIntegrable_slice {T : ℝ} (hT : 0 ≤ T) {f : X → ℝ}
    (hf : ContinuousOn f (slab 0 T)) :
    IntervalIntegrable (fun t => ∫ y in Icc (0 : Fin 3 → ℝ) 1, f (Fin.cons t y)) volume 0 T :=
  (continuousOn_sliceIntegral hT hf).intervalIntegrable_of_Icc hT

theorem slabInt_add {T : ℝ} (hT : 0 ≤ T) {f g : X → ℝ} (hf : ContinuousOn f (slab 0 T))
    (hg : ContinuousOn g (slab 0 T)) :
    slabInt T (fun x => f x + g x) = slabInt T f + slabInt T g := by
  unfold slabInt
  rw [← intervalIntegral.integral_add (intervalIntegrable_slice hT hf)
    (intervalIntegrable_slice hT hg)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hT] at ht
  exact integral_add (integrableOn_cube_slice hf ht) (integrableOn_cube_slice hg ht)

theorem slabInt_sub {T : ℝ} (hT : 0 ≤ T) {f g : X → ℝ} (hf : ContinuousOn f (slab 0 T))
    (hg : ContinuousOn g (slab 0 T)) :
    slabInt T (fun x => f x - g x) = slabInt T f - slabInt T g := by
  unfold slabInt
  rw [← intervalIntegral.integral_sub (intervalIntegrable_slice hT hf)
    (intervalIntegrable_slice hT hg)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hT] at ht
  exact integral_sub (integrableOn_cube_slice hf ht) (integrableOn_cube_slice hg ht)

theorem slabInt_neg (T : ℝ) (f : X → ℝ) : slabInt T (fun x => -f x) = -slabInt T f := by
  unfold slabInt
  simp only [integral_neg, intervalIntegral.integral_neg]

theorem slabInt_congr {T : ℝ} (hT : 0 ≤ T) {f g : X → ℝ}
    (h : ∀ x : X, x 0 ∈ Icc 0 T → f x = g x) : slabInt T f = slabInt T g := by
  unfold slabInt
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hT] at ht
  exact setIntegral_congr_fun measurableSet_Icc fun y _ => h _ (by simpa using ht)

theorem volume_cube3 : (volume : Measure (Fin 3 → ℝ)).real (Icc 0 1) = 1 := by
  rw [measureReal_def, Real.volume_Icc_pi]
  simp

/-- `|∫₀ᵀ∫ f| ≤ T C` when `|f| ≤ C` on the slab. -/
theorem abs_slabInt_le {T : ℝ} (hT : 0 ≤ T) {f : X → ℝ} {C : ℝ}
    (hC : ∀ x : X, x 0 ∈ Icc 0 T → |f x| ≤ C) : |slabInt T f| ≤ T * C := by
  unfold slabInt
  have h1 : ∀ t ∈ Ι (0 : ℝ) T, ‖∫ y in Icc (0 : Fin 3 → ℝ) 1, f (Fin.cons t y)‖ ≤ C := by
    intro t ht
    have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Fin 3 → ℝ)))
      (s := Icc 0 1) (f := fun y => f (Fin.cons t y)) (C := C) (by simp [Real.volume_Icc_pi])
      (fun y _ => by
        rw [Real.norm_eq_abs]; exact hC _ (by simpa using mem_slab_of_uIoc hT ht))
    rwa [volume_cube3, mul_one] at this
  have := intervalIntegral.norm_integral_le_of_norm_le_const h1
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at this
  linarith

/-- **Test functions on the cylinder `(0, T) × 𝕋³`**: smooth, spatially `ℤ³`-periodic, vanishing
outside `[a, b] × ℝ³` for some `0 < a ≤ b < T`. -/
structure IsCylTest (T : ℝ) (φ : X → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  per : IsSPeriodic φ
  supp : ∃ a b, 0 < a ∧ b < T ∧ ∀ x : X, x 0 ∉ Icc a b → φ x = 0

/-- The time derivative of a slice integral. -/
theorem hasDerivAt_sliceInt {P : X → ℝ} (hP : ContDiff ℝ ∞ P) (t : ℝ) :
    HasDerivAt (fun s => ∫ y in Icc (0 : Fin 3 → ℝ) 1, P (Fin.cons s y))
      (∫ y in Icc (0 : Fin 3 → ℝ) 1, pd P 0 (Fin.cons t y)) t := by
  have hcT : Continuous (pd P 0) := (contDiff_pd_top hP 0).continuous
  set K : Set X := (fun p : ℝ × (Fin 3 → ℝ) => (Fin.cons p.1 p.2 : X)) ''
    (Icc (t - 1) (t + 1) ×ˢ Icc 0 1)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image continuous_cons2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcT.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc (0 : Fin 3 → ℝ) 1))
    (F := fun s y => P (Fin.cons s y)) (F' := fun s y => pd P 0 (Fin.cons s y))
    (x₀ := t) (bound := fun _ => C) (s := Ioo (t - 1) (t + 1))
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    (Eventually.of_forall fun s => (hP.continuous.comp (continuous_cons s)).aestronglyMeasurable)
    (integrableOn_slice hP.continuous t)
    ((hcT.comp (continuous_cons t)).aestronglyMeasurable)
    (by
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall fun y hy s hs => ?_
      exact hC _ ⟨(s, y), ⟨Ioo_subset_Icc_self hs, hy⟩, rfl⟩)
    (integrable_const C)
    (Eventually.of_forall fun y s _ => hasDerivAt_time y ((hP.differentiable (by simp)) _))
  exact key.2

/-- **Integration by parts on the cylinder**: for a smooth periodic `F` and a cylinder test
function `φ`, `∫₀ᵀ∫ ∂_μF φ = -∫₀ᵀ∫ F ∂_μφ`. -/
theorem slabInt_pd_mul {T : ℝ} (hT : 0 ≤ T) {F φ : X → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFp : IsSPeriodic F) (hφ : IsCylTest T φ) (μ : Fin 4) :
    slabInt T (fun x => pd F μ x * φ x) = -slabInt T (fun x => F x * pd φ μ x) := by
  set P : X → ℝ := fun x => F x * φ x
  have hP : ContDiff ℝ ∞ P := hF.mul hφ.smooth
  have hPp : IsSPeriodic P := fun k x => by simp only [P, hFp k x, hφ.per k x]
  have hpd : ∀ x, pd P μ x = pd F μ x * φ x + F x * pd φ μ x := fun x =>
    SobolevOpen.pd_mul (hF.of_le (by norm_cast)) (hφ.smooth.of_le (by norm_cast)) μ x
  have hzero : slabInt T (pd P μ) = 0 := by
    induction μ using Fin.cases with
    | succ i =>
      unfold slabInt
      have : ∀ t, ∫ y in Icc (0 : Fin 3 → ℝ) 1, pd P i.succ (Fin.cons t y) = 0 := fun t =>
        integral_slice_pd_eq_zero (hP.of_le (by norm_cast)) hPp t i
      simp [this]
    | zero =>
      unfold slabInt
      obtain ⟨a, b, ha, hb, hsupp⟩ := hφ.supp
      have hI : ∀ s, ∫ y in Icc (0 : Fin 3 → ℝ) 1, P (Fin.cons s y) =
          ∫ y in Icc (0 : Fin 3 → ℝ) 1, P (Fin.cons s y) := fun _ => rfl
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s => ∫ y in Icc (0 : Fin 3 → ℝ) 1, P (Fin.cons s y))
        (fun t _ => hasDerivAt_sliceInt hP t)
        ((continuous_sliceInt (contDiff_pd_top hP 0).continuous).intervalIntegrable _ _)]
      have h0 : ∀ s, s ∉ Icc a b → ∫ y in Icc (0 : Fin 3 → ℝ) 1, P (Fin.cons s y) = 0 := by
        intro s hs
        have : ∀ y, P (Fin.cons s y) = 0 := fun y => by
          simp only [P]; rw [hsupp _ (by simpa using hs), mul_zero]
        simp [this]
      rw [h0 T (fun h => by linarith [h.2]), h0 0 (fun h => by linarith [h.1]), sub_zero]
  have hc1 : ContinuousOn (fun x => pd F μ x * φ x) (slab 0 T) :=
    ((contDiff_pd_top hF μ).continuous.mul hφ.smooth.continuous).continuousOn
  have hc2 : ContinuousOn (fun x => F x * pd φ μ x) (slab 0 T) :=
    (hF.continuous.mul (contDiff_pd_top hφ.smooth μ).continuous).continuousOn
  have := slabInt_add hT hc1 hc2
  rw [show slabInt T (fun x => pd F μ x * φ x + F x * pd φ μ x) = slabInt T (pd P μ) from
    slabInt_congr hT fun x _ => (hpd x).symm, hzero] at this
  linarith

/-! ### The distributional curvature of a `C¹` metric -/

/-- **The distributional Riemann tensor** of a metric with continuous Christoffel symbols `Γ`
(`Γ c i j = Γ^c_{ij}`), tested on `φ`:
`∫₀ᵀ∫ (-Γ^a_{db}∂_cφ + Γ^a_{cb}∂_dφ + (Σₑ Γ^a_{ce}Γ^e_{db} - Σₑ Γ^a_{de}Γ^e_{cb})φ)`. -/
def riemDist (T : ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → X → ℝ) (a b c d : Fin 4) (φ : X → ℝ) : ℝ :=
  slabInt T (fun x => -(Γ a d b x * pd φ c x) + Γ a c b x * pd φ d x +
    (∑ e, Γ a c e x * Γ e d b x - ∑ e, Γ a d e x * Γ e c b x) * φ x)

/-- **For smooth metrics the pairing of the classical curvature is the distributional one.** -/
theorem slabInt_riemF {T : ℝ} (hT : 0 ≤ T) {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    (sg : ∀ c, ContDiff ℝ ∞ (g c)) (sgi : ∀ a b, ContDiff ℝ ∞ (gi a b))
    (pg : ∀ c, IsSPeriodic (g c)) (pgi : ∀ a b, IsSPeriodic (gi a b)) {φ : X → ℝ}
    (hφ : IsCylTest T φ) (a b c d : Fin 4) :
    slabInt T (fun x => RiemF g gi a b c d x * φ x) = riemDist T (GamF g gi) a b c d φ := by
  have sΓ := contDiff_GamF sg sgi
  have pΓ := isSPeriodic_GamF pg pgi
  have cφ := hφ.smooth.continuous
  have cdφ := fun μ => (contDiff_pd_top hφ.smooth μ).continuous
  have cΓ := fun c i j => (sΓ c i j).continuous
  have cdΓ := fun c i j μ => (contDiff_pd_top (sΓ c i j) μ).continuous
  set Q : X → ℝ := fun x => (∑ e, GamF g gi a c e x * GamF g gi e d b x -
    ∑ e, GamF g gi a d e x * GamF g gi e c b x) * φ x
  have cQ : Continuous Q := by simp only [Q]; fun_prop
  have k1 : ContinuousOn (fun x => pd (GamF g gi a d b) c x * φ x) (slab 0 T) :=
    ((cdΓ a d b c).mul cφ).continuousOn
  have k2 : ContinuousOn (fun x => pd (GamF g gi a c b) d x * φ x) (slab 0 T) :=
    ((cdΓ a c b d).mul cφ).continuousOn
  have k12 : ContinuousOn (fun x => pd (GamF g gi a d b) c x * φ x -
      pd (GamF g gi a c b) d x * φ x) (slab 0 T) := k1.sub k2
  have e1 : slabInt T (fun x => RiemF g gi a b c d x * φ x) =
      slabInt T (fun x => pd (GamF g gi a d b) c x * φ x) -
        slabInt T (fun x => pd (GamF g gi a c b) d x * φ x) + slabInt T Q := by
    rw [← slabInt_sub hT k1 k2, ← slabInt_add hT k12 cQ.continuousOn]
    refine slabInt_congr hT fun x _ => ?_
    simp only [RiemF, riemann, Q]
    ring
  have e2 : riemDist T (GamF g gi) a b c d φ =
      -slabInt T (fun x => GamF g gi a d b x * pd φ c x) +
        slabInt T (fun x => GamF g gi a c b x * pd φ d x) + slabInt T Q := by
    have m1 : ContinuousOn (fun x => -(GamF g gi a d b x * pd φ c x)) (slab 0 T) :=
      ((cΓ a d b).mul (cdφ c)).neg.continuousOn
    have m2 : ContinuousOn (fun x => GamF g gi a c b x * pd φ d x) (slab 0 T) :=
      ((cΓ a c b).mul (cdφ d)).continuousOn
    have m12 : ContinuousOn (fun x => -(GamF g gi a d b x * pd φ c x) +
        GamF g gi a c b x * pd φ d x) (slab 0 T) := m1.add m2
    unfold riemDist
    rw [← slabInt_neg, ← slabInt_add hT m1 m2, ← slabInt_add hT m12 cQ.continuousOn]
  rw [e1, e2, slabInt_pd_mul hT (sΓ a d b) (pΓ a d b) hφ c,
    slabInt_pd_mul hT (sΓ a c b) (pΓ a c b) hφ d]
  ring

/-! ### Uniform convergence on the slab -/

/-- Uniform convergence on the slab `[0, T] × ℝ³`. -/
def UConv (T : ℝ) (u : ℕ → X → ℝ) (v : X → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n, N ≤ n → ∀ x : X, x 0 ∈ Icc 0 T → |u n x - v x| ≤ ε

namespace UConv

variable {T : ℝ} {u u' : ℕ → X → ℝ} {v v' : X → ℝ}

theorem add (h : UConv T u v) (h' : UConv T u' v') :
    UConv T (fun n x => u n x + u' n x) (fun x => v x + v' x) := fun ε hε => by
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  obtain ⟨N', hN'⟩ := h' (ε / 2) (by positivity)
  refine ⟨max N N', fun n hn x hx => ?_⟩
  have := hN n (le_of_max_le_left hn) x hx
  have := hN' n (le_of_max_le_right hn) x hx
  calc |u n x + u' n x - (v x + v' x)| = |(u n x - v x) + (u' n x - v' x)| := by ring_nf
    _ ≤ |u n x - v x| + |u' n x - v' x| := abs_add_le _ _
    _ ≤ ε := by linarith

theorem neg (h : UConv T u v) : UConv T (fun n x => -u n x) (fun x => -v x) := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn x hx => by
    rw [show -u n x - -v x = -(u n x - v x) by ring, abs_neg]; exact hN n hn x hx⟩

theorem sub (h : UConv T u v) (h' : UConv T u' v') :
    UConv T (fun n x => u n x - u' n x) (fun x => v x - v' x) := by
  have := h.add h'.neg
  simpa [sub_eq_add_neg] using this

theorem const (f : X → ℝ) : UConv T (fun _ => f) f := fun ε hε => ⟨0, fun n _ x _ => by simpa using hε.le⟩

/-- Products, with a uniform bound on the limits. -/
theorem mul {B B' : ℝ} (h : UConv T u v) (h' : UConv T u' v')
    (hv : ∀ x : X, x 0 ∈ Icc 0 T → |v x| ≤ B) (hv' : ∀ x : X, x 0 ∈ Icc 0 T → |v' x| ≤ B') :
    UConv T (fun n x => u n x * u' n x) (fun x => v x * v' x) := fun ε hε => by
  have hB : 0 ≤ |B| := abs_nonneg _
  have hB' : 0 ≤ |B'| := abs_nonneg _
  set δ := min 1 (ε / (|B| + |B'| + 1))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (|B| + |B'| + 1) ≤ ε := by
    have := min_le_right 1 (ε / (|B| + |B'| + 1))
    rwa [le_div_iff₀ (by positivity)] at this
  obtain ⟨N, hN⟩ := h δ hδ
  obtain ⟨N', hN'⟩ := h' δ hδ
  refine ⟨max N N', fun n hn x hx => ?_⟩
  have e1 := hN n (le_of_max_le_left hn) x hx
  have e2 := hN' n (le_of_max_le_right hn) x hx
  have b1 := (hv x hx).trans (le_abs_self B)
  have b2 := (hv' x hx).trans (le_abs_self B')
  have hu' : |u' n x| ≤ |B'| + δ := by
    have := abs_sub_abs_le_abs_sub (u' n x) (v' x); linarith
  calc |u n x * u' n x - v x * v' x| = |(u n x - v x) * u' n x + v x * (u' n x - v' x)| := by
        ring_nf
    _ ≤ |u n x - v x| * |u' n x| + |v x| * |u' n x - v' x| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ δ * (|B'| + δ) + |B| * δ := by gcongr
    _ ≤ δ * (|B| + |B'| + 1) := by nlinarith
    _ ≤ ε := hδε

theorem sum {ι : Type*} (s : Finset ι) {u : ι → ℕ → X → ℝ} {v : ι → X → ℝ}
    (h : ∀ i ∈ s, UConv T (u i) (v i)) :
    UConv T (fun n x => ∑ i ∈ s, u i n x) (fun x => ∑ i ∈ s, v i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UConv.const (T := T) (fun _ => (0 : ℝ))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Uniform convergence of the slab integrals. -/
theorem tendsto_slabInt (hT : 0 ≤ T) (h : UConv T u v) (hu : ∀ n, ContinuousOn (u n) (slab 0 T))
    (hv : ContinuousOn v (slab 0 T)) :
    Tendsto (fun n => slabInt T (u n)) atTop (𝓝 (slabInt T v)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / (2 * (T + 1))) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, ← slabInt_sub hT (hu n) hv]
  refine (abs_slabInt_le hT (fun x hx => hN n hn x hx)).trans_lt ?_
  rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
  nlinarith

theorem continuousOn (h : UConv T u v) (hu : ∀ n, Continuous (u n)) :
    ContinuousOn v (slab 0 T) := by
  refine TendstoUniformlyOn.continuousOn (F := u) (p := atTop) ?_
    (Frequently.of_forall fun n => (hu n).continuousOn)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  refine Filter.eventually_atTop.2 ⟨N, fun n hn x hx => ?_⟩
  rw [dist_comm, Real.dist_eq]
  exact (hN n hn x hx).trans_lt (by linarith)

theorem tendsto (h : UConv T u v) {x : X} (hx : x 0 ∈ Icc 0 T) :
    Tendsto (fun n => u n x) atTop (𝓝 (v x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact (hN n hn x hx).trans_lt (by linarith)⟩

theorem bound {B : ℝ} (h : UConv T u v) (hb : ∀ n, ∀ x : X, x 0 ∈ Icc 0 T → |u n x| ≤ B) :
    ∀ x : X, x 0 ∈ Icc 0 T → |v x| ≤ B := fun x hx =>
  le_of_tendsto (continuous_abs.tendsto _ |>.comp (h.tendsto hx))
    (Eventually.of_forall fun n => hb n x hx)

end UConv

/-- A cylinder test function and its derivatives are bounded on the slab. -/
theorem IsCylTest.exists_bound {T : ℝ} (hT : 0 ≤ T) {φ : X → ℝ} (hφ : IsCylTest T φ)
    (f : X → ℝ) (hf : ContDiff ℝ ∞ f) (hfp : IsSPeriodic f) :
    ∃ B, ∀ x : X, x 0 ∈ Icc 0 T → |f x| ≤ B := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuous_Q 2 hf).continuousOn
    (s := Icc (0 : ℝ) T)
  exact ⟨Real.sqrt (CS * |K|), fun x hx => abs_le_of_Q hCS hsup hf hfp
    (fun t ht => ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hK t ht))).trans
      (le_abs_self K)) hx⟩

/-- **Convergence of the distributional curvature** under uniform convergence of the Christoffel
symbols (with a uniform bound). -/
theorem tendsto_riemDist {T : ℝ} (hT : 0 ≤ T) {Γn : ℕ → Fin 4 → Fin 4 → Fin 4 → X → ℝ}
    {Γ : Fin 4 → Fin 4 → Fin 4 → X → ℝ} (hc : ∀ n c i j, Continuous (Γn n c i j))
    (hu : ∀ c i j, UConv T (fun n => Γn n c i j) (Γ c i j)) {BΓ : ℝ}
    (hb : ∀ c i j, ∀ x : X, x 0 ∈ Icc 0 T → |Γ c i j x| ≤ BΓ) {φ : X → ℝ} (hφ : IsCylTest T φ)
    (a b c d : Fin 4) :
    Tendsto (fun n => riemDist T (Γn n) a b c d φ) atTop (𝓝 (riemDist T Γ a b c d φ)) := by
  obtain ⟨B0, hB0⟩ := hφ.exists_bound hT φ hφ.smooth hφ.per
  have hBd : ∀ μ, ∃ B, ∀ x : X, x 0 ∈ Icc 0 T → |pd φ μ x| ≤ B := fun μ =>
    hφ.exists_bound hT _ (contDiff_pd_top hφ.smooth μ) (isSPeriodic_pd hφ.per μ)
  choose Bd hBd using hBd
  have hΓc : ∀ c i j, ContinuousOn (Γ c i j) (slab 0 T) := fun c i j =>
    (hu c i j).continuousOn (hc · c i j)
  have hφc := hφ.smooth.continuous
  have hdφc := fun μ => (contDiff_pd_top hφ.smooth μ).continuous
  have hpp : ∀ (c₁ i₁ j₁ c₂ i₂ j₂ : Fin 4), UConv T (fun n x => Γn n c₁ i₁ j₁ x * Γn n c₂ i₂ j₂ x)
      (fun x => Γ c₁ i₁ j₁ x * Γ c₂ i₂ j₂ x) := fun c₁ i₁ j₁ c₂ i₂ j₂ =>
    (hu c₁ i₁ j₁).mul (hu c₂ i₂ j₂) (hb c₁ i₁ j₁) (hb c₂ i₂ j₂)
  have hU : UConv T (fun n x => -(Γn n a d b x * pd φ c x) + Γn n a c b x * pd φ d x +
      (∑ e, Γn n a c e x * Γn n e d b x - ∑ e, Γn n a d e x * Γn n e c b x) * φ x)
      (fun x => -(Γ a d b x * pd φ c x) + Γ a c b x * pd φ d x +
      (∑ e, Γ a c e x * Γ e d b x - ∑ e, Γ a d e x * Γ e c b x) * φ x) := by
    refine ((((hu a d b).mul (UConv.const _) (hb a d b) (hBd c)).neg).add
      ((hu a c b).mul (UConv.const _) (hb a c b) (hBd d))).add ?_
    refine ((UConv.sum Finset.univ fun e _ => hpp a c e e d b).sub
      (UConv.sum Finset.univ fun e _ => hpp a d e e c b)).mul (UConv.const _) (B := 8 * BΓ ^ 2)
      (fun x hx => ?_) hB0
    have h1 : ∀ e, |Γ a c e x * Γ e d b x| ≤ BΓ ^ 2 := fun e => by
      rw [abs_mul, sq]; exact mul_le_mul (hb _ _ _ x hx) (hb _ _ _ x hx) (abs_nonneg _)
        ((abs_nonneg _).trans (hb a c e x hx))
    have h2 : ∀ e, |Γ a d e x * Γ e c b x| ≤ BΓ ^ 2 := fun e => by
      rw [abs_mul, sq]; exact mul_le_mul (hb _ _ _ x hx) (hb _ _ _ x hx) (abs_nonneg _)
        ((abs_nonneg _).trans (hb a d e x hx))
    have s1 : |∑ e, Γ a c e x * Γ e d b x| ≤ 4 * BΓ ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ e, |Γ a c e x * Γ e d b x| ≤ ∑ _e : Fin 4, BΓ ^ 2 := Finset.sum_le_sum fun e _ => h1 e
        _ = 4 * BΓ ^ 2 := by simp
    have s2 : |∑ e, Γ a d e x * Γ e c b x| ≤ 4 * BΓ ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ e, |Γ a d e x * Γ e c b x| ≤ ∑ _e : Fin 4, BΓ ^ 2 := Finset.sum_le_sum fun e _ => h2 e
        _ = 4 * BΓ ^ 2 := by simp
    refine (abs_sub _ _).trans ?_
    linarith
  refine hU.tendsto_slabInt hT (fun n => ?_) ?_
  · have := fun c i j => hc n c i j
    exact Continuous.continuousOn (by fun_prop)
  · have hsum1 : ContinuousOn (fun x => ∑ e, Γ a c e x * Γ e d b x) (slab 0 T) :=
      continuousOn_finsetSum _ fun e _ => (hΓc a c e).mul (hΓc e d b)
    have hsum2 : ContinuousOn (fun x => ∑ e, Γ a d e x * Γ e c b x) (slab 0 T) :=
      continuousOn_finsetSum _ fun e _ => (hΓc a d e).mul (hΓc e c b)
    exact (((hΓc a d b).mul (hdφc c).continuousOn).neg.add ((hΓc a c b).mul
      (hdφc d).continuousOn)).add ((hsum1.sub hsum2).mul hφc.continuousOn)


/-! ### `L²` pairings and `L¹((0, T); L²)` limits -/

theorem inner_toL2 {f ψ : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) (hψ : Continuous ψ) :
    inner ℝ (toL2 f) (toL2 ψ) = ∫ y in Icc (0 : Fin 3 → ℝ) 1, f y * ψ y := by
  rw [toL2_eq hf, toL2_eq hψ, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_of_continuous hf).coeFn_toLp, (memLp_of_continuous hψ).coeFn_toLp]
    with a ha hb
  rw [ha, hb, RCLike.inner_apply, conj_trivial, mul_comm]

/-- The pairing `⟨R, φ⟩ = ∫₀ᵀ ⟨R(t), φ(t, ·)⟩_{L²([0,1]³)} dt` of a curve `R : ℝ → L²` with a
space-time function. -/
def Pair (T : ℝ) (R : ℝ → Lp ℝ 2 μc) (φ : X → ℝ) : ℝ :=
  ∫ t in (0)..T, inner ℝ (R t) (toL2 (fun y => φ (Fin.cons t y)))

/-- The pairing of the slice curve of a continuous function is its slab integral against `φ`. -/
theorem Pair_slice {T : ℝ} {F φ : X → ℝ} (hF : Continuous F) (hφ : Continuous φ) :
    Pair T (fun t => toL2 (fun y => F (Fin.cons t y))) φ = slabInt T (fun x => F x * φ x) := by
  unfold Pair slabInt
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact inner_toL2 (hF.comp (continuous_cons t)) (hφ.comp (continuous_cons t))

theorem L1_norm_sub_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ}
    {f : ℝ → E} (hf : Integrable f μ) (L : ℝ →₁[μ] E) :
    ‖hf.toL1 f - L‖ = ∫ t, ‖f t - L t‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (hf.toL1 f) L, hf.coeFn_toL1] with t h1 h2
  rw [h1, Pi.sub_apply, h2]

/-- **`L¹_t`-Cauchy families of continuous curves converge in `L¹((0, T); E)`.** -/
theorem exists_L1_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} (hT : 0 ≤ T) {F : ℕ → ℝ → E} (hF : ∀ n, Continuous (F n))
    (hc : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → ∫ t in (0)..T, ‖F m t - F n t‖ ≤ ε) :
    ∃ G : ℝ → E, Integrable G (volume.restrict (Ioc 0 T)) ∧
      Tendsto (fun n => ∫ t in (0)..T, ‖F n t - G t‖) atTop (𝓝 0) := by
  set μ : Measure ℝ := volume.restrict (Ioc 0 T)
  have hi : ∀ n, Integrable (F n) μ := fun n =>
    ((hF n).continuousOn.integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self
  set u : ℕ → ℝ →₁[μ] E := fun n => (hi n).toL1 (F n)
  have hd : ∀ m n, dist (u m) (u n) = ∫ t in (0)..T, ‖F m t - F n t‖ := by
    intro m n
    rw [dist_eq_norm, intervalIntegral.integral_of_le hT, L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (u m) (u n), (hi m).coeFn_toL1, (hi n).coeFn_toL1]
      with t h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hcs : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (by positivity)
    exact ⟨N, fun n hn => by rw [hd]; exact (hN n N hn le_rfl).trans_lt (by linarith)⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨L, L1.integrable_coeFn L, ?_⟩
  have e : ∀ n, ∫ t in (0)..T, ‖F n t - L t‖ = ‖u n - L‖ := fun n => by
    rw [intervalIntegral.integral_of_le hT, L1_norm_sub_eq (hi n) L]
  simp_rw [e]
  have := (tendsto_iff_norm_sub_tendsto_zero.mp hL)
  exact this

theorem norm_toL2_slice_le {T : ℝ} {φ : X → ℝ} (hφ : Continuous φ) :
    ∃ B, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, ‖toL2 (fun y => φ (Fin.cons t y))‖ ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_toL2_slice hφ).continuousOn (s := Icc (0 : ℝ) T)
  exact ⟨|B|, abs_nonneg _, fun t ht => (hB t ht).trans (le_abs_self _)⟩

/-- **Continuity of the pairing** under `L¹((0, T); L²)` convergence. -/
theorem tendsto_Pair {T : ℝ} (hT : 0 ≤ T) {Fn : ℕ → ℝ → Lp ℝ 2 μc} {R : ℝ → Lp ℝ 2 μc}
    (hFn : ∀ n, Continuous (Fn n)) (hR : Integrable R (volume.restrict (Ioc 0 T)))
    (hconv : Tendsto (fun n => ∫ t in (0)..T, ‖Fn n t - R t‖) atTop (𝓝 0)) {φ : X → ℝ}
    (hφ : Continuous φ) : Tendsto (fun n => Pair T (Fn n) φ) atTop (𝓝 (Pair T R φ)) := by
  set Φ : ℝ → Lp ℝ 2 μc := fun t => toL2 (fun y => φ (Fin.cons t y))
  have hΦ : Continuous Φ := continuous_toL2_slice hφ
  obtain ⟨B, hB0, hB⟩ := norm_toL2_slice_le (T := T) hφ
  set μ : Measure ℝ := volume.restrict (Ioc 0 T)
  have h2 : Integrable (fun t => inner ℝ (R t) (Φ t)) μ := by
    refine Integrable.mono' (hR.norm.mul_const B)
      (hR.aestronglyMeasurable.inner hΦ.aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (hB t ⟨ht.1.le, ht.2⟩) (norm_nonneg _))
  have hdiff : ∀ n, |Pair T (Fn n) φ - Pair T R φ| ≤ B * ∫ t in (0)..T, ‖Fn n t - R t‖ := by
    intro n
    have hi1 : Integrable (fun t => ‖Fn n t - R t‖) μ :=
      (((((hFn n).continuousOn.integrableOn_Icc (a := 0) (b := T)).mono_set
        Ioc_subset_Icc_self)).sub hR).norm
    unfold Pair
    rw [← intervalIntegral.integral_sub, intervalIntegral.integral_of_le hT,
      intervalIntegral.integral_of_le hT, ← integral_const_mul]
    · refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
        (Eventually.of_forall fun t => abs_nonneg _) (hi1.const_mul B) ?_)
      rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun t ht => ?_
      rw [← inner_sub_left]
      exact (abs_real_inner_le_norm _ _).trans (by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hB t ⟨ht.1.le, ht.2⟩) (norm_nonneg _))
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
        ((((hFn n).inner hΦ).continuousOn.integrableOn_Icc (a := 0) (b := T)).mono_set
          Ioc_subset_Icc_self)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (ε / (B + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero] at h1
  rw [Real.dist_eq]
  have h0 : 0 ≤ ∫ t in (0)..T, ‖Fn n t - R t‖ :=
    intervalIntegral.integral_nonneg hT fun t _ => norm_nonneg _
  rw [abs_of_nonneg h0] at h1
  calc |Pair T (Fn n) φ - Pair T R φ| ≤ B * ∫ t in (0)..T, ‖Fn n t - R t‖ := hdiff n
    _ < (B + 1) * (ε / (B + 1)) := by
        have := div_pos hε (by linarith : (0 : ℝ) < B + 1)
        nlinarith
    _ = ε := by field_simp

/-! ### Weak derivatives of `L²` limits of slice derivatives -/

/-- Integration by parts on the cube for periodic functions. -/
theorem integral_pd_mul_cube {f ψ : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (pf : IsZPeriodic f)
    (hψ : ContDiff ℝ ∞ ψ) (pψ : IsZPeriodic ψ) (i : Fin 3) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, pd f i y * ψ y = -∫ y in Icc (0 : Fin 3 → ℝ) 1, f y * pd ψ i y := by
  have hP : ContDiff ℝ 1 (fun y => f y * ψ y) := (hf.mul hψ).of_le (by norm_cast)
  have hPp : IsZPeriodic (fun y => f y * ψ y) := fun k y => by simp only [pf k y, pψ k y]
  have h0 := integral_pd_eq_zero hP hPp i
  have e : ∀ y, pd (fun y => f y * ψ y) i y = pd f i y * ψ y + f y * pd ψ i y := fun y =>
    SobolevOpen.pd_mul (hf.of_le (by norm_cast)) (hψ.of_le (by norm_cast)) i y
  simp_rw [e] at h0
  rw [integral_add (f := fun y => pd f i y * ψ y) (g := fun y => f y * pd ψ i y)
    (integrableOn_cube_of_continuousOn
    (((contDiff_pd_top hf i).continuous.mul hψ.continuous).continuousOn))
    (integrableOn_cube_of_continuousOn
      ((hf.continuous.mul (contDiff_pd_top hψ i).continuous).continuousOn))] at h0
  linarith

/-- **`L²` limits of slice derivatives are the weak derivatives of the limit**: if the slices
`∂^w F_n(t, ·)` and `∂^{w i} F_n(t, ·)` of smooth periodic fields converge in `L²([0,1]³)` to `G`
and `G'`, then `⟨G', ψ⟩ = -⟨G, ∂ᵢψ⟩` for every smooth `ℤ³`-periodic `ψ`: `G' = ∂ᵢG` weakly on
`𝕋³`. -/
theorem weak_deriv_of_L2_limit {F : ℕ → X → ℝ} (sF : ∀ n, ContDiff ℝ ∞ (F n))
    (pF : ∀ n, IsSPeriodic (F n)) (t : ℝ) (w : List (Fin 3)) (i : Fin 3) {G G' : Lp ℝ 2 μc}
    (hG : Tendsto (fun n => toL2 (fun y => sd w (F n) (Fin.cons t y))) atTop (𝓝 G))
    (hG' : Tendsto (fun n => toL2 (fun y => sd (w ++ [i]) (F n) (Fin.cons t y))) atTop (𝓝 G'))
    {ψ : (Fin 3 → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (pψ : IsZPeriodic ψ) :
    inner ℝ G' (toL2 ψ) = -inner ℝ G (toL2 (pd ψ i)) := by
  have hdψ : Continuous (pd ψ i) := (contDiff_pd_top hψ i).continuous
  have key : ∀ n, inner ℝ (toL2 (fun y => sd (w ++ [i]) (F n) (Fin.cons t y))) (toL2 ψ) =
      -inner ℝ (toL2 (fun y => sd w (F n) (Fin.cons t y))) (toL2 (pd ψ i)) := by
    intro n
    have sw := contDiff_sd w (sF n)
    have hsl : ContDiff ℝ ∞ (fun y : Fin 3 → ℝ => sd w (F n) (Fin.cons t y)) :=
      sw.comp (contDiff_cons t)
    have psl : IsZPeriodic (fun y : Fin 3 → ℝ => sd w (F n) (Fin.cons t y)) :=
      (isSPeriodic_sd w (pF n)).slice t
    have e : (fun y => sd (w ++ [i]) (F n) (Fin.cons t y)) =
        pd (fun y => sd w (F n) (Fin.cons t y)) i := by
      funext y
      rw [sd_append_single, pd_slice i ((sw.differentiable (by simp)) _)]
    rw [e, inner_toL2 (contDiff_pd_top hsl i).continuous hψ.continuous,
      inner_toL2 hsl.continuous hdψ, integral_pd_mul_cube hsl psl hψ pψ i]
  have h1 := (hG'.inner (𝕜 := ℝ) (tendsto_const_nhds (x := toL2 ψ)))
  have h2 := (hG.inner (𝕜 := ℝ) (tendsto_const_nhds (x := toL2 (pd ψ i)))).neg
  simp_rw [key] at h1
  exact tendsto_nhds_unique h1 h2

/-- A cylinder test function's partial derivatives are cylinder test functions. -/
theorem IsCylTest.pd {T : ℝ} {φ : X → ℝ} (hφ : IsCylTest T φ) (μ : Fin 4) :
    IsCylTest T (pd φ μ) := by
  obtain ⟨a, b, ha, hb, hs⟩ := hφ.supp
  refine ⟨contDiff_pd_top hφ.smooth μ, isSPeriodic_pd hφ.per μ, a, b, ha, hb, fun x hx => ?_⟩
  have hopen : IsOpen {y : X | y 0 ∉ Icc a b} :=
    (isClosed_Icc.preimage (continuous_apply 0)).isOpen_compl
  have hev : φ =ᶠ[𝓝 x] fun _ => 0 :=
    Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => hs y hy
  show fderiv ℝ φ x (Pi.single μ 1) = 0
  rw [hev.fderiv_eq]
  simp


/-! ### `C¹` limits -/

theorem norm_clm_le_sum (A : (Fin 4 → ℝ) →L[ℝ] ℝ) : ‖A‖ ≤ ∑ μ, |A (Pi.single μ 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    fun v => ?_
  have hv : v = ∑ μ, v μ • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) := by
    ext j; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun μ _ => ?_
  rw [map_smul, smul_eq_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm v μ))
    (abs_nonneg _)

/-- The linear map with the given partial derivatives. -/
def jetCLM (D : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ∑ μ, D μ • ContinuousLinearMap.proj μ

theorem jetCLM_single (D : Fin 4 → ℝ) (μ : Fin 4) : jetCLM D (Pi.single μ 1) = D μ := by
  simp [jetCLM, Pi.single_apply]

/-- **Uniform `C¹` limits are `C¹`**: if `F_n → F` and `∂_μF_n → D_μ` uniformly on the slab, then
`F` is differentiable on the open slab with `∂_μF = D_μ`. -/
theorem hasFDerivAt_of_UConv {T : ℝ} {F : ℕ → X → ℝ} {Fl : X → ℝ} {D : Fin 4 → X → ℝ}
    (sF : ∀ n, ContDiff ℝ ∞ (F n)) (hF : UConv T F Fl)
    (hD : ∀ μ, UConv T (fun n => pd (F n) μ) (D μ)) {x : X} (hx : x 0 ∈ Ioo 0 T) :
    HasFDerivAt Fl (jetCLM fun μ => D μ x) x := by
  set s : Set X := {y | y 0 ∈ Ioo 0 T}
  have hs : IsOpen s := isOpen_Ioo.preimage (continuous_apply 0)
  refine hasFDerivAt_of_tendstoUniformlyOn (f := F) (f' := fun n y => fderiv ℝ (F n) y)
    (g' := fun y => jetCLM fun μ => D μ y) (l := atTop) hs ?_
    (fun n y _ => ((sF n).differentiable (by simp) y).hasFDerivAt)
    (fun y hy => hF.tendsto (Ioo_subset_Icc_self hy)) hx
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hμ : ∀ μ, ∃ N, ∀ n, N ≤ n → ∀ y : X, y 0 ∈ Icc 0 T → |pd (F n) μ y - D μ y| ≤ ε / 8 :=
    fun μ => hD μ (ε / 8) (by positivity)
  choose N hN using hμ
  refine Filter.eventually_atTop.2 ⟨∑ μ, N μ, fun n hn y hy => ?_⟩
  rw [dist_eq_norm]
  refine (norm_clm_le_sum _).trans_lt ?_
  have h1 : ∀ μ, |(jetCLM (fun μ => D μ y) - fderiv ℝ (F n) y) (Pi.single μ 1)| ≤ ε / 8 := by
    intro μ
    rw [sub_apply, jetCLM_single, abs_sub_comm]
    exact hN μ n (le_trans (Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ μ)) hn) y (Ioo_subset_Icc_self hy)
  calc ∑ μ, |(jetCLM (fun μ => D μ y) - fderiv ℝ (F n) y) (Pi.single μ 1)| ≤
      ∑ _μ : Fin 4, ε / 8 := Finset.sum_le_sum fun μ _ => h1 μ
    _ < ε := by simp; linarith

/-- The Christoffel symbols of a metric given by its inverse and its first derivatives. -/
def GamL (gil : Fin 4 → Fin 4 → X → ℝ) (dgl : Idx → Fin 4 → X → ℝ) (c i j : Fin 4) (x : X) :
    ℝ :=
  christoffel (fun a b => gil a b x) (fun i j k => dgl (j, k) i x) c i j

theorem UConv.const_mul {T : ℝ} {u : ℕ → X → ℝ} {v : X → ℝ} (h : UConv T u v) (a : ℝ) :
    UConv T (fun n x => a * u n x) (fun x => a * v x) := fun ε hε => by
  obtain ⟨N, hN⟩ := h (ε / (|a| + 1)) (by positivity)
  refine ⟨N, fun n hn x hx => ?_⟩
  rw [← mul_sub, abs_mul]
  calc |a| * |u n x - v x| ≤ |a| * (ε / (|a| + 1)) :=
        mul_le_mul_of_nonneg_left (hN n hn x hx) (abs_nonneg _)
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg a]

theorem contDiff_RiemF {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    (sg : ∀ c, ContDiff ℝ ∞ (g c)) (sgi : ∀ a b, ContDiff ℝ ∞ (gi a b)) (a b c d : Fin 4) :
    ContDiff ℝ ∞ (RiemF g gi a b c d) := by
  have sΓ := contDiff_GamF sg sgi
  have : RiemF g gi a b c d = fun x => pd (GamF g gi a d b) c x - pd (GamF g gi a c b) d x +
      (∑ e, GamF g gi a c e x * GamF g gi e d b x - ∑ e, GamF g gi a d e x * GamF g gi e c b x) :=
    funext fun x => by simp only [RiemF, riemann]; ring
  rw [this]
  exact ((contDiff_pd_top (sΓ a d b) c).sub (contDiff_pd_top (sΓ a c b) d)).add
    ((ContDiff.sum fun e _ => (sΓ a c e).mul (sΓ e d b)).sub
      (ContDiff.sum fun e _ => (sΓ a d e).mul (sΓ e c b)))

theorem isSPeriodic_RiemF {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    (pg : ∀ c, IsSPeriodic (g c)) (pgi : ∀ a b, IsSPeriodic (gi a b)) (a b c d : Fin 4) :
    IsSPeriodic (RiemF g gi a b c d) := fun k x => by
  have pΓ := isSPeriodic_GamF pg pgi
  simp only [RiemF, riemann, fun c i j => pΓ c i j k x,
    fun c i j μ => isSPeriodic_pd (pΓ c i j) μ k x]

/-! ### The curvature limit -/

/-- **`thm:hyperbolic`, curvature clause: `Riem(g_h) → Riem(g)` in `L¹_tH^{s-3}`** under the
paper's hypotheses (`MetricHypSh`: uniform hyperbolicity with a common time function, any bounded
shift; `Σ = 𝕋³`, `s ≥ 5`; Cauchy initial data in `H^{s-1} × H^{s-2}`, Cauchy sources in
`L¹_tH^{s-2}`).  There are a limit metric `g`, its first derivatives `∂g` and its inverse
`g⁻¹` such that
1. `g_h → g`, `∂_μg_h → ∂_μg`, `g_h⁻¹ → g⁻¹` uniformly on `[0, T] × ℝ³`;
2. `g` is differentiable on the open slab with partial derivatives `∂g`, and `g g⁻¹ = 1`;
3. for every curvature component `q` and word `|w| ≤ s - 3`, `∂^w Riem(g_h)` converges in
   `L¹((0, T); L²([0,1]³))` to `R_{q,w}` (an integrable curve);
4. `R_{q,wi} = ∂ᵢR_{q,w}` weakly on `(0, T) × 𝕋³` (so `R_q = R_{q,∅} ∈ L¹_tH^{s-3}` with weak
   derivatives `R_{q,w}`);
5. `R_q = Riem(g)_q` in the sense of distributions on `(0, T) × 𝕋³`: `⟨R_q, φ⟩ = riemDist` of
   the Christoffel symbols `Γ(g) = GamL g⁻¹ ∂g` (the distributional curvature of the `C¹` metric
   `g`) for every cylinder test function `φ`. -/
theorem riem_limit_sh {κ : Type} [Fintype κ] {Np : Idx → MvPolynomial (NV κ) ℝ}
    {θ : κ → X → ℝ} {T a0 lamS Λ K0 : ℝ} {s : ℕ} (hs : 5 ≤ s) (hT : 0 < T) (ha : 0 < a0)
    (hlamS : 0 < lamS) {g : ℕ → Idx → X → ℝ} {gi : ℕ → Fin 4 → Fin 4 → X → ℝ}
    {S : ℕ → Idx → X → ℝ}
    (hg : ∀ h, MetricHypSh Np θ s T a0 lamS Λ K0 (g h) (gi h) (S h))
    (hinit : Tendsto (fun p : ℕ × ℕ => ∑ c, (Q (s - 1) (fun x => g p.1 c x - g p.2 c x) 0 +
      Q (s - 2) (fun x => pd (g p.1 c) 0 x - pd (g p.2 c) 0 x) 0)) atTop (𝓝 0))
    (hsrc : Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T,
      Real.sqrt (∑ c, Q (s - 2) (fun x => S p.1 c x - S p.2 c x) t)) atTop (𝓝 0)) :
    ∃ (gl : Idx → X → ℝ) (dgl : Idx → Fin 4 → X → ℝ) (gil : Fin 4 → Fin 4 → X → ℝ)
      (R : Fin 4 × Fin 4 × Fin 4 × Fin 4 → List (Fin 3) → ℝ → Lp ℝ 2 μc),
      (∀ c, UConv T (fun h => g h c) (gl c)) ∧
      (∀ c μ, UConv T (fun h => pd (g h c) μ) (dgl c μ)) ∧
      (∀ a b, UConv T (fun h => gi h a b) (gil a b)) ∧
      (∀ c (x : X), x 0 ∈ Ioo 0 T → DifferentiableAt ℝ (gl c) x ∧
        ∀ μ, pd (gl c) μ x = dgl c μ x) ∧
      (∀ x : X, x 0 ∈ Icc 0 T → ∀ a b, ∑ e, gl (a, e) x * gil e b x = if a = b then 1 else 0) ∧
      (∀ q w, w.length ≤ s - 3 → Integrable (R q w) (volume.restrict (Ioc 0 T)) ∧
        Tendsto (fun h => ∫ t in (0)..T, ‖toL2 (fun y => sd w
          (RiemF (g h) (gi h) q.1 q.2.1 q.2.2.1 q.2.2.2) (Fin.cons t y)) - R q w t‖) atTop
          (𝓝 0)) ∧
      (∀ q w (i : Fin 3), (w ++ [i]).length ≤ s - 3 → ∀ φ, IsCylTest T φ →
        Pair T (R q (w ++ [i])) φ = -Pair T (R q w) (pd φ i.succ)) ∧
      (∀ q φ, IsCylTest T φ →
        Pair T (R q []) φ = riemDist T (GamL gil dgl) q.1 q.2.1 q.2.2.1 q.2.2.2 φ) := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  have hT0 := hT.le
  have hgM := fun h => (hg h).toMetricHyp
  have hgM2 : ∀ h, MetricHyp Np θ (s - 2 + 2) T a0 (-(3 * Λ)) Λ K0 (g h) (gi h) (S h) :=
    fun h => by rw [Nat.sub_add_cancel (by omega : 2 ≤ s)]; exact hgM h
  have hΛ : 0 ≤ Λ := le_trans ha.le ((hgM 0).Λ_pos ha hT0)
  have hcau := common_slab_cauchy_sh hs hT ha hlamS hg hinit hsrc
  have hN := cauchy_N (P := fun i j ε => ∀ t ∈ Icc 0 T, ∑ c, (Q (s - 1)
    (fun x => g i c x - g j c x) t + Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t) ≤ ε)
    hcau
  have hterm : ∀ i j t c, Q (s - 1) (fun x => g i c x - g j c x) t +
      Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t ≤ ∑ c, (Q (s - 1)
        (fun x => g i c x - g j c x) t + Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t) :=
    fun i j t c => Finset.single_le_sum (f := fun c => Q (s - 1) (fun x => g i c x - g j c x) t +
      Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t)
      (fun c _ => add_nonneg (Q_nonneg _ _ _) (Q_nonneg _ _ _)) (Finset.mem_univ c)
  have hc1 : ∀ c, ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ t ∈ Icc 0 T,
      Q (s - 1) (fun x => g i c x - g j c x) t ≤ ε := by
    intro c ε hε
    obtain ⟨N, hN'⟩ := hN ε hε
    refine ⟨N, fun i j hi hj t ht => ?_⟩
    have h1 := hterm i j t c
    have h2 := hN' i j hi hj t ht
    have h3 := Q_nonneg (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t
    linarith
  have hcd : ∀ c (ν : Fin 4), ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ t ∈ Icc 0 T,
      Q (s - 2) (fun x => pd (g i c) ν x - pd (g j c) ν x) t ≤ ε := by
    intro c ν ε hε
    obtain ⟨N, hN'⟩ := hN ε hε
    refine ⟨N, fun i j hi hj t ht => ?_⟩
    have h1 := hterm i j t c
    have h2 := hN' i j hi hj t ht
    induction ν using Fin.cases with
    | zero =>
      have h3 := Q_nonneg (s - 1) (fun x => g i c x - g j c x) t
      linarith
    | succ k =>
      have e : (fun x => pd (g i c) k.succ x - pd (g j c) k.succ x) =
          pd (fun x => g i c x - g j c x) k.succ := by
        have := pd_lincomb ((hg i).sg c) ((hg j).sg c) 1 (-1) k.succ
        simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at this
        exact this.symm
      rw [e]
      have h4 := Q_pd_le (k := s - 2) k (fun x => g i c x - g j c x) t
      rw [show s - 2 + 1 = s - 1 by omega] at h4
      have h3 := Q_nonneg (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t
      linarith
  -- uniform Cauchy and limits
  have ug : ∀ c, ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x ∈ {x : X | x 0 ∈ Icc 0 T},
      ‖g i c x - g j c x‖ ≤ ε := fun c ε hε => by
    obtain ⟨N, hN'⟩ := uniformCauchy_of_Q hCS hsup (m := s - 1) (by omega) (fun i => (hg i).sg c)
      (fun i => (hg i).pg c) (hc1 c) ε hε
    exact ⟨N, fun i j hi hj x hx => by rw [Real.norm_eq_abs]; exact hN' i j hi hj x hx⟩
  have udg : ∀ c ν, ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x ∈ {x : X | x 0 ∈ Icc 0 T},
      ‖pd (g i c) ν x - pd (g j c) ν x‖ ≤ ε := fun c ν ε hε => by
    obtain ⟨N, hN'⟩ := uniformCauchy_of_Q hCS hsup (m := s - 2) (by omega)
      (fun i => contDiff_pd_top ((hg i).sg c) ν) (fun i => isSPeriodic_pd ((hg i).pg c) ν)
      (hcd c ν) ε hε
    exact ⟨N, fun i j hi hj x hx => by rw [Real.norm_eq_abs]; exact hN' i j hi hj x hx⟩
  have toU : ∀ {u : ℕ → X → ℝ} {v : X → ℝ}, (∀ ε > 0, ∃ N, ∀ i, N ≤ i →
      ∀ x ∈ {x : X | x 0 ∈ Icc 0 T}, ‖u i x - v x‖ ≤ ε) → UConv T u v := fun h ε hε => by
    obtain ⟨N, hN'⟩ := h ε hε
    exact ⟨N, fun n hn x hx => by have := hN' n hn x hx; rwa [Real.norm_eq_abs] at this⟩
  choose gl hgl using fun c => exists_uniform_limit (fun i x => g i c x) _ (ug c)
  choose dgl hdgl using fun c ν => exists_uniform_limit (fun i x => pd (g i c) ν x) _ (udg c ν)
  have Ugl : ∀ c, UConv T (fun h => g h c) (gl c) := fun c => toU (hgl c)
  have Udgl : ∀ c μ, UConv T (fun h => pd (g h c) μ) (dgl c μ) := fun c μ => toU (hdgl c μ)
  -- the inverse metrics
  have ugi : ∀ a b, ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x ∈ {x : X | x 0 ∈ Icc 0 T},
      ‖gi i a b x - gi j a b x‖ ≤ ε := by
    intro a b ε hε
    choose Nc hNc using fun c => ug c (ε / (16 * (Λ ^ 2 + 1))) (by positivity)
    refine ⟨∑ c, Nc c, fun i j hi hj x hx => ?_⟩
    rw [Real.norm_eq_abs, gi_sub_eq (hgM2 i) (hgM2 j) hx]
    have hd : ∀ c, |g j c x - g i c x| ≤ ε / (16 * (Λ ^ 2 + 1)) := fun c => by
      have hle := Finset.single_le_sum (f := Nc) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      rw [abs_sub_comm]
      have := hNc c i j (by omega) (by omega) x hx
      rwa [Real.norm_eq_abs] at this
    have hterm2 : ∀ c e, |gi i a c x * (g j (c, e) x - g i (c, e) x) * gi j e b x| ≤
        Λ ^ 2 * (ε / (16 * (Λ ^ 2 + 1))) := by
      intro c e
      rw [abs_mul, abs_mul]
      have h1 := (hg i).bnd x hx a c
      have h2 := (hg j).bnd x hx e b
      have h3 := hd (c, e)
      calc |gi i a c x| * |g j (c, e) x - g i (c, e) x| * |gi j e b x| ≤
          Λ * (ε / (16 * (Λ ^ 2 + 1))) * Λ := by gcongr
        _ = _ := by ring
    calc |∑ c, ∑ e, gi i a c x * (g j (c, e) x - g i (c, e) x) * gi j e b x| ≤
        ∑ _c : Fin 4, ∑ _e : Fin 4, Λ ^ 2 * (ε / (16 * (Λ ^ 2 + 1))) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => hterm2 c e))
      _ = 16 * Λ ^ 2 * (ε / (16 * (Λ ^ 2 + 1))) := by simp; ring
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg Λ]
  choose gil hgil using fun a b => exists_uniform_limit (fun i x => gi i a b x) _ (ugi a b)
  have Ugil : ∀ a b, UConv T (fun h => gi h a b) (gil a b) := fun a b => toU (hgil a b)
  -- bounds
  set BD := Real.sqrt (CS * K0)
  have hBD : 0 ≤ BD := Real.sqrt_nonneg _
  have bdg : ∀ h c ν (x : X), x 0 ∈ Icc 0 T → |pd (g h c) ν x| ≤ BD := by
    intro h c ν x hx
    refine abs_le_of_Q_bound hCS hsup (m := s - 1) (by omega) (contDiff_pd_top ((hg h).sg c) ν)
      (isSPeriodic_pd ((hg h).pg c) ν) (fun t ht => ?_) hx
    induction ν using Fin.cases with
    | zero => exact (hg h).hst t ht c
    | succ k =>
      have := Q_pd_le (k := s - 1) k (g h c) t
      rw [show s - 1 + 1 = s by omega] at this
      exact this.trans ((hg h).hsg t ht c)
  have bgil : ∀ a b (x : X), x 0 ∈ Icc 0 T → |gil a b x| ≤ Λ := fun a b =>
    (Ugil a b).bound fun h x hx => (hg h).bnd x hx a b
  have bdgl : ∀ c ν (x : X), x 0 ∈ Icc 0 T → |dgl c ν x| ≤ BD := fun c ν =>
    (Udgl c ν).bound fun h x hx => bdg h c ν x hx
  -- the Christoffel symbols
  have UΓ : ∀ c i j, UConv T (fun h => GamF (g h) (gi h) c i j) (GamL gil dgl c i j) := by
    intro c i j
    have hY : ∀ e, UConv T (fun h x => pd (g h (e, j)) i x + pd (g h (e, i)) j x -
        pd (g h (i, j)) e x) (fun x => dgl (e, j) i x + dgl (e, i) j x - dgl (i, j) e x) :=
      fun e => ((Udgl _ i).add (Udgl _ j)).sub (Udgl _ e)
    have hbY : ∀ e (x : X), x 0 ∈ Icc 0 T →
        |dgl (e, j) i x + dgl (e, i) j x - dgl (i, j) e x| ≤ 3 * BD := fun e x hx => by
      have h1 := bdgl (e, j) i x hx; have h2 := bdgl (e, i) j x hx; have h3 := bdgl (i, j) e x hx
      have h4 := abs_sub (dgl (e, j) i x + dgl (e, i) j x) (dgl (i, j) e x)
      have h5 := abs_add_le (dgl (e, j) i x) (dgl (e, i) j x)
      linarith
    have hsum := UConv.sum Finset.univ fun e _ => (Ugil c e).mul (hY e) (bgil c e) (hbY e)
    have h12 := hsum.const_mul (1 / 2)
    intro ε hε
    obtain ⟨N, hN'⟩ := h12 ε hε
    exact ⟨N, fun n hn x hx => by
      have := hN' n hn x hx
      simpa only [GamF, GamL, christoffel] using this⟩
  have bΓh : ∀ h c i j (x : X), x 0 ∈ Icc 0 T → |GamF (g h) (gi h) c i j x| ≤ 6 * Λ * BD := by
    intro h c i j x hx
    have hb : ∀ e, |gi h c e x * (pd (g h (e, j)) i x + pd (g h (e, i)) j x -
        pd (g h (i, j)) e x)| ≤ Λ * (3 * BD) := fun e => by
      rw [abs_mul]
      refine mul_le_mul ((hg h).bnd x hx c e) ?_ (abs_nonneg _) hΛ
      have h1 := bdg h (e, j) i x hx; have h2 := bdg h (e, i) j x hx
      have h3 := bdg h (i, j) e x hx
      have h4 := abs_sub (pd (g h (e, j)) i x + pd (g h (e, i)) j x) (pd (g h (i, j)) e x)
      have h5 := abs_add_le (pd (g h (e, j)) i x) (pd (g h (e, i)) j x)
      linarith
    simp only [GamF, christoffel]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := (Finset.abs_sum_le_sum_abs (fun e => gi h c e x * (pd (g h (e, j)) i x +
      pd (g h (e, i)) j x - pd (g h (i, j)) e x)) Finset.univ).trans
      (Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) => hb e)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    linarith
  have bΓ : ∀ c i j (x : X), x 0 ∈ Icc 0 T → |GamL gil dgl c i j x| ≤ 6 * Λ * BD :=
    fun c i j => (UΓ c i j).bound fun h x hx => bΓh h c i j x hx
  -- `C¹` and the inverse
  have hC1 : ∀ c (x : X), x 0 ∈ Ioo 0 T → DifferentiableAt ℝ (gl c) x ∧
      ∀ μ, pd (gl c) μ x = dgl c μ x := fun c x hx => by
    have hF := hasFDerivAt_of_UConv (fun n => (hg n).sg c) (Ugl c) (Udgl c) hx
    refine ⟨hF.differentiableAt, fun μ => ?_⟩
    show fderiv ℝ (gl c) x (Pi.single μ 1) = _
    rw [hF.fderiv, jetCLM_single]
  have hinv : ∀ x : X, x 0 ∈ Icc 0 T → ∀ a b,
      ∑ e, gl (a, e) x * gil e b x = if a = b then 1 else 0 := fun x hx a b => by
    have h1 : Tendsto (fun h => ∑ e, g h (a, e) x * gi h e b x) atTop
        (𝓝 (∑ e, gl (a, e) x * gil e b x)) :=
      tendsto_finsetSum _ fun e _ => ((Ugl _).tendsto hx).mul ((Ugil e b).tendsto hx)
    have h2 : (fun h => ∑ e, g h (a, e) x * gi h e b x) = fun _ => if a = b then 1 else 0 :=
      funext fun h => (hg h).inv x hx a b
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- the curvature curves
  set Rf : ℕ → Fin 4 × Fin 4 × Fin 4 × Fin 4 → X → ℝ :=
    fun h q => RiemF (g h) (gi h) q.1 q.2.1 q.2.2.1 q.2.2.2
  have sR : ∀ h q, ContDiff ℝ ∞ (Rf h q) := fun h q => contDiff_RiemF (hg h).sg (hg h).sgi _ _ _ _
  have pR : ∀ h q, IsSPeriodic (Rf h q) := fun h q =>
    isSPeriodic_RiemF (hg h).pg (hg h).pgi _ _ _ _
  have hRc := riem_cauchy_sh hs hT ha hlamS hg hinit hsrc
  have hRc' : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → ∫ t in (0)..T, Real.sqrt
      (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4, Q (s - 3) (fun x => Rf m q x - Rf n q x) t) ≤ ε :=
    cauchy_N (P := fun m n ε => ∫ t in (0)..T, Real.sqrt
      (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4, Q (s - 3) (fun x => Rf m q x - Rf n q x) t) ≤ ε)
      fun ε hε => (hRc.eventually (Iio_mem_nhds hε)).mono fun p hp => le_of_lt hp
  have hcurve : ∀ h q (w : List (Fin 3)),
      Continuous fun t => toL2 (fun y => sd w (Rf h q) (Fin.cons t y)) := fun h q w =>
    continuous_toL2_slice (contDiff_sd w (sR h q)).continuous
  have hRex : ∀ q (w : List (Fin 3)), ∃ G : ℝ → Lp ℝ 2 μc, w.length ≤ s - 3 →
      Integrable G (volume.restrict (Ioc 0 T)) ∧
      Tendsto (fun h => ∫ t in (0)..T, ‖toL2 (fun y => sd w (Rf h q) (Fin.cons t y)) - G t‖)
        atTop (𝓝 0) := by
    intro q w
    by_cases hw : w.length ≤ s - 3
    · have hpt : ∀ m n, ∀ t ∈ Icc 0 T, ‖toL2 (fun y => sd w (Rf m q) (Fin.cons t y)) -
          toL2 (fun y => sd w (Rf n q) (Fin.cons t y))‖ ≤ Real.sqrt
            (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4, Q (s - 3) (fun x => Rf m q x - Rf n q x) t) := by
        intro m n t _
        have hs0 : 0 ≤ ∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
            Q (s - 3) (fun x => Rf m q x - Rf n q x) t :=
          Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
        refine norm_toL2_sub_le (F := fun y => sd w (Rf m q) (Fin.cons t y))
          (F' := fun y => sd w (Rf n q) (Fin.cons t y))
          ((contDiff_sd w (sR m q)).continuous.comp (continuous_cons t))
          ((contDiff_sd w (sR n q)).continuous.comp (continuous_cons t)) ?_ (Real.sqrt_nonneg _)
        rw [Real.sq_sqrt hs0]
        have e : ∀ y, sd w (Rf m q) (Fin.cons t y) - sd w (Rf n q) (Fin.cons t y) =
            sd w (fun x => Rf m q x - Rf n q x) (Fin.cons t y) := fun y => by
          rw [sd_sub w (sR m q) (sR n q)]
        simp_rw [e]
        exact (term_le_Q hw _ t).trans (Finset.single_le_sum
          (f := fun q => Q (s - 3) (fun x => Rf m q x - Rf n q x) t)
          (fun _ _ => Q_nonneg _ _ _) (Finset.mem_univ q))
      have hc : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → ∫ t in (0)..T,
          ‖toL2 (fun y => sd w (Rf m q) (Fin.cons t y)) -
            toL2 (fun y => sd w (Rf n q) (Fin.cons t y))‖ ≤ ε := by
        intro ε hε
        obtain ⟨N, hN'⟩ := hRc' ε hε
        refine ⟨N, fun m n hm hn => le_trans ?_ (hN' m n hm hn)⟩
        refine intervalIntegral.integral_mono_on hT0
          (((hcurve m q w).sub (hcurve n q w)).norm.intervalIntegrable _ _)
          ((continuous_finsetSum _ fun q _ => continuous_Q _ ((sR m q).sub (sR n q))).sqrt
            |>.intervalIntegrable _ _) (hpt m n)
      obtain ⟨G, hG1, hG2⟩ := exists_L1_limit hT0 (fun n => hcurve n q w) hc
      exact ⟨G, fun _ => ⟨hG1, hG2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hw⟩
  choose R hR using hRex
  refine ⟨gl, dgl, gil, R, Ugl, Udgl, Ugil, hC1, hinv, fun q w hw => hR q w hw, ?_, ?_⟩
  · -- weak spatial derivatives
    intro q w i hwi φ hφ
    have hw : w.length ≤ s - 3 := by simp at hwi; omega
    have hφc := hφ.smooth.continuous
    have hdφc := (contDiff_pd_top hφ.smooth i.succ).continuous
    have key : ∀ n, Pair T (fun t => toL2 (fun y => sd (w ++ [i]) (Rf n q) (Fin.cons t y))) φ =
        -Pair T (fun t => toL2 (fun y => sd w (Rf n q) (Fin.cons t y))) (pd φ i.succ) := by
      intro n
      rw [Pair_slice (contDiff_sd _ (sR n q)).continuous hφc,
        Pair_slice (contDiff_sd _ (sR n q)).continuous hdφc]
      simp only [sd_append_single]
      exact slabInt_pd_mul hT0 (contDiff_sd w (sR n q)) (isSPeriodic_sd w (pR n q)) hφ i.succ
    have h1 := tendsto_Pair hT0 (fun n => hcurve n q (w ++ [i])) (hR q (w ++ [i]) hwi).1
      (hR q (w ++ [i]) hwi).2 hφc
    have h2 := (tendsto_Pair hT0 (fun n => hcurve n q w) (hR q w hw).1 (hR q w hw).2 hdφc).neg
    simp_rw [key] at h1
    exact tendsto_nhds_unique h1 h2
  · -- identification
    intro q φ hφ
    have hφc := hφ.smooth.continuous
    have h0 : ([] : List (Fin 3)).length ≤ s - 3 := by simp
    have h1 := tendsto_Pair hT0 (fun n => hcurve n q []) (hR q [] h0).1 (hR q [] h0).2 hφc
    have key : ∀ n, Pair T (fun t => toL2 (fun y => sd [] (Rf n q) (Fin.cons t y))) φ =
        riemDist T (GamF (g n) (gi n)) q.1 q.2.1 q.2.2.1 q.2.2.2 φ := by
      intro n
      rw [Pair_slice (contDiff_sd _ (sR n q)).continuous hφc]
      exact slabInt_riemF hT0 (hg n).sg (hg n).sgi (hg n).pg (hg n).pgi hφ _ _ _ _
    simp_rw [key] at h1
    have h2 := tendsto_riemDist hT0 (fun n c i j => (contDiff_GamF (hg n).sg (hg n).sgi c i j).continuous)
      UΓ bΓ hφ q.1 q.2.1 q.2.2.1 q.2.2.2
    exact tendsto_nhds_unique h1 h2


/-! ### The `C_tH^m` limits of the metric are Sobolev functions -/

theorem tendsto_of_uniform_word {F : ℕ → ℝ → Lp ℝ 2 μc} {G : ℝ → Lp ℝ 2 μc} {T t : ℝ}
    (ht : t ∈ Icc 0 T) (h : ∀ ε > 0, ∃ N, ∀ n, N ≤ n → ∀ t ∈ Icc 0 T, ‖F n t - G t‖ ≤ ε) :
    Tendsto (fun n => F n t) atTop (𝓝 (G t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact (hN n hn t ht).trans_lt (by linarith)⟩

/-- **`thm:hyperbolic`, the first two limits with the weak-derivative identification**: the
`C_tH^{s-1}` and `C_tH^{s-2}` limits `G_w(t)`, `G'_w(t)` of `common_slab_limit_sh` are the weak
spatial derivatives of `G_∅(t) = g(t, ·)`, `G'_∅(t) = ∂ₜg(t, ·)` on `𝕋³`:
`⟨G_{wi}(t), ψ⟩ = -⟨G_w(t), ∂ᵢψ⟩` for smooth `ℤ³`-periodic `ψ` (so `g(t) ∈ H^{s-1}(𝕋³)`,
`∂ₜg(t) ∈ H^{s-2}(𝕋³)` with these derivatives). -/
theorem common_slab_limit_weak_sh {κ : Type} [Fintype κ] {Np : Idx → MvPolynomial (NV κ) ℝ}
    {θ : κ → X → ℝ} {T a0 lamS Λ K0 : ℝ} {s : ℕ} (hs : 5 ≤ s) (hT : 0 < T) (ha : 0 < a0)
    (hlamS : 0 < lamS) {g : ℕ → Idx → X → ℝ} {gi : ℕ → Fin 4 → Fin 4 → X → ℝ}
    {S : ℕ → Idx → X → ℝ}
    (hg : ∀ h, MetricHypSh Np θ s T a0 lamS Λ K0 (g h) (gi h) (S h))
    (hinit : Tendsto (fun p : ℕ × ℕ => ∑ c, (Q (s - 1) (fun x => g p.1 c x - g p.2 c x) 0 +
      Q (s - 2) (fun x => pd (g p.1 c) 0 x - pd (g p.2 c) 0 x) 0)) atTop (𝓝 0))
    (hsrc : Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T,
      Real.sqrt (∑ c, Q (s - 2) (fun x => S p.1 c x - S p.2 c x) t)) atTop (𝓝 0)) :
    ∃ (gl gt : Idx → X → ℝ) (G G' : Idx → List (Fin 3) → ℝ → Lp ℝ 2 μc),
      (∀ ε > 0, ∃ N, ∀ h, N ≤ h → ∀ x : X, x 0 ∈ Icc 0 T → ∀ c,
        |g h c x - gl c x| ≤ ε ∧ |pd (g h c) 0 x - gt c x| ≤ ε) ∧
      (∀ c (x : X), x 0 ∈ Icc 0 T → gl c x = gl c (Fin.cons 0 (Fin.tail x)) +
        ∫ σ in (0)..(x 0), gt c (Fin.cons σ (Fin.tail x))) ∧
      (∀ ε > 0, ∃ N, ∀ h, N ≤ h → ∀ t ∈ Icc 0 T, ∀ c (w : List (Fin 3)), w.length ≤ s - 1 →
        ‖toL2 (fun y => sd w (g h c) (Fin.cons t y)) - G c w t‖ ≤ ε) ∧
      (∀ ε > 0, ∃ N, ∀ h, N ≤ h → ∀ t ∈ Icc 0 T, ∀ c (w : List (Fin 3)), w.length ≤ s - 2 →
        ‖toL2 (fun y => sd w (pd (g h c) 0) (Fin.cons t y)) - G' c w t‖ ≤ ε) ∧
      (∀ c, ∀ t ∈ Icc 0 T, G c [] t = toL2 (fun y => gl c (Fin.cons t y)) ∧
        G' c [] t = toL2 (fun y => gt c (Fin.cons t y))) ∧
      (∀ c (w : List (Fin 3)) (i : Fin 3), (w ++ [i]).length ≤ s - 1 → ∀ t ∈ Icc 0 T,
        ∀ ψ : (Fin 3 → ℝ) → ℝ, ContDiff ℝ ∞ ψ → IsZPeriodic ψ →
          inner ℝ (G c (w ++ [i]) t) (toL2 ψ) = -inner ℝ (G c w t) (toL2 (pd ψ i))) ∧
      (∀ c (w : List (Fin 3)) (i : Fin 3), (w ++ [i]).length ≤ s - 2 → ∀ t ∈ Icc 0 T,
        ∀ ψ : (Fin 3 → ℝ) → ℝ, ContDiff ℝ ∞ ψ → IsZPeriodic ψ →
          inner ℝ (G' c (w ++ [i]) t) (toL2 ψ) = -inner ℝ (G' c w t) (toL2 (pd ψ i))) := by
  obtain ⟨gl, gt, G, G', h1, _, h3, h4, h5, _, h7⟩ :=
    common_slab_limit_sh hs hT ha hlamS hg hinit hsrc
  refine ⟨gl, gt, G, G', h1, h3, h4, h5, h7, ?_, ?_⟩
  · intro c w i hwi t ht ψ hψ pψ
    have hw : w.length ≤ s - 1 := by simp at hwi; omega
    have conv : ∀ v : List (Fin 3), v.length ≤ s - 1 →
        Tendsto (fun n => toL2 (fun y => sd v (g n c) (Fin.cons t y))) atTop (𝓝 (G c v t)) :=
      fun v hv => tendsto_of_uniform_word (F := fun n t => toL2 (fun y => sd v (g n c)
        (Fin.cons t y))) ht fun ε hε => by
          obtain ⟨N, hN⟩ := h4 ε hε
          exact ⟨N, fun n hn t ht => hN n hn t ht c v hv⟩
    exact weak_deriv_of_L2_limit (fun n => (hg n).sg c) (fun n => (hg n).pg c) t w i
      (conv w hw) (conv _ hwi) hψ pψ
  · intro c w i hwi t ht ψ hψ pψ
    have hw : w.length ≤ s - 2 := by simp at hwi; omega
    have conv : ∀ v : List (Fin 3), v.length ≤ s - 2 →
        Tendsto (fun n => toL2 (fun y => sd v (pd (g n c) 0) (Fin.cons t y))) atTop
          (𝓝 (G' c v t)) :=
      fun v hv => tendsto_of_uniform_word (F := fun n t => toL2 (fun y => sd v (pd (g n c) 0)
        (Fin.cons t y))) ht fun ε hε => by
          obtain ⟨N, hN⟩ := h5 ε hε
          exact ⟨N, fun n hn t ht => hN n hn t ht c v hv⟩
    exact weak_deriv_of_L2_limit (fun n => contDiff_pd_top ((hg n).sg c) 0)
      (fun n => isSPeriodic_pd ((hg n).pg c) 0) t w i (conv w hw) (conv _ hwi) hψ pψ

/-! ### Non-vacuity -/

/-- Non-vacuity of `riem_limit_sh` (the constant shifted metric of `shifted_metricHypSh`, `∂ₜ`
spacelike). -/
example (T : ℝ) (hT : 0 < T) :=
  riem_limit_sh (κ := Empty) (s := 5) (by norm_num) hT one_pos one_pos
    (g := fun _ => gShift) (gi := fun _ => giShift) (S := fun _ _ _ => 0)
    (fun _ => shifted_metricHypSh 5 T) (by simp [Q_const]) (by simp [Q_const])

/-- Non-vacuity of `common_slab_limit_weak_sh`. -/
example (T : ℝ) (hT : 0 < T) :=
  common_slab_limit_weak_sh (κ := Empty) (s := 5) (by norm_num) hT one_pos one_pos
    (g := fun _ => gShift) (gi := fun _ => giShift) (S := fun _ _ _ => 0)
    (fun _ => shifted_metricHypSh 5 T) (by simp [Q_const]) (by simp [Q_const])

/-- A cylinder test function exists for every `T > 0` (non-vacuity of `IsCylTest`): a smooth
time bump supported in `[T/4, 3T/4]`, constant in space. -/
theorem exists_cylTest {T : ℝ} (hT : 0 < T) : ∃ φ : X → ℝ, IsCylTest T φ ∧ φ ≠ 0 := by
  obtain ⟨f, hf, hsupp, hpos⟩ : ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧
      (∀ t, t ∉ Icc (T / 4) (3 * T / 4) → f t = 0) ∧ f (T / 2) ≠ 0 := by
    let b : ContDiffBump (T / 2) := ⟨T / 8, T / 4, by positivity, by linarith⟩
    refine ⟨b, b.contDiff, fun t ht => ?_, ?_⟩
    · refine b.zero_of_le_dist ?_
      have hr : b.rOut = T / 4 := rfl
      rw [Real.dist_eq, hr]
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    · rw [b.one_of_mem_closedBall (by simp; positivity)]; norm_num
  refine ⟨fun x => f (x 0), ⟨hf.comp (contDiff_apply ℝ ℝ (0 : Fin 4)), fun k x => ?_,
    T / 4, 3 * T / 4, by positivity, by linarith, fun x hx => hsupp _ hx⟩, ?_⟩
  · simp [sshift]
  · intro h
    have := congrFun h (Fin.cons (T / 2) 0)
    simp at this
    exact hpos this

end RenewalGeometry.ReducedWaveShift
