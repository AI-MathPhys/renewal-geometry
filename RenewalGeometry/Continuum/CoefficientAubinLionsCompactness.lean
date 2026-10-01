/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Aubin–Lions–Simon compactness in Fourier-coefficient form
  (infrastructure for `thm:main-hodge-connection` and `thm:main-literal-link-compactness`;
  emergent-spacetime manuscript, supplement)

The finite-mode temporal compactness mechanism of the manuscript (`SimonCompact`): a family of
fields whose spatial Fourier coefficients `c_k(t)` are uniformly bounded in `L²_t H¹_x`
(`Σ_k w(k) ∫₀ᵀ |c_k|² ≤ B`, `w(k) = 1 + |k|²`) and whose time derivatives are bounded in
any negative norm `L²_t H^{-s}_x` (per mode, `∫₀ᵀ |∂ₜ c_k|² ≤ B₁(k)`) is relatively compact in
`L²_t L²_x` (`L²_t ℓ²_k`).

* `IsW12Rep`: the `W^{1,2}(0,T)` representation `c(t) = c(0) + ∫₀ᵗ g`, `g ∈ L²(0,T)` (weak time
  derivative); `IsW12Rep.norm_sub_le_abs` (the `½`-Hölder bound
  `|c(t) - c(s)| ≤ |t - s|^{1/2} ‖g‖_{L²}`), `IsW12Rep.continuousOn`, `IsW12Rep.norm_le`
  (uniform bound from `L²` bounds);
* `exists_subseq_tendstoUniformlyOn`: simultaneous Arzelà–Ascoli extraction over countably many
  modes (compactness of countable products of compact metrizable sets);
* `aubinLions_coefficients`: the Aubin–Lions–Simon theorem in coefficient form — a subsequence
  converges strongly in `L²_t ℓ²_k`, i.e. (by Parseval) the corresponding trigonometric fields
  converge strongly in `L²((0,T) × 𝕋³)`; the tail is controlled uniformly by `B / R` on modes with
  `w(k) > R`.
-/

open MeasureTheory Filter Topology Set
open scoped BoundedContinuousFunction

noncomputable section

namespace RenewalGeometry.CoefficientAubinLions

/-! ### One-dimensional `W^{1,2}(0,T)` estimates -/

section OneDim

/-- `c` is represented on `[0,T]` as `c(t) = c(0) + ∫₀ᵗ g` with `g ∈ L²(0,T)`: the weak time
derivative of `c` is `g` (the `W^{1,2}(0,T)` characterization). -/
structure IsW12Rep (T : ℝ) (c g : ℝ → ℂ) : Prop where
  memLp : MemLp g 2 (volume.restrict (Ioc 0 T))
  rep : ∀ t ∈ Icc 0 T, c t = c 0 + ∫ u in (0 : ℝ)..t, g u

theorem integral_norm_le_sqrt_mul_sqrt {s t : ℝ} (hst : s ≤ t) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioc s t))) :
    ∫ u in Ioc s t, ‖g u‖ ≤ Real.sqrt (t - s) * Real.sqrt (∫ u in Ioc s t, ‖g u‖ ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict (Ioc s t)) := by
    have : IsFiniteMeasure (volume.restrict (Ioc s t)) := by
      constructor; simp
    exact memLp_const 1
  have h2 : MemLp (fun u => ‖g u‖) (ENNReal.ofReal 2) (volume.restrict (Ioc s t)) := by
    rw [ENNReal.ofReal_ofNat]; exact hg.norm
  have := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ fun _ => zero_le_one)
    (ae_of_all _ fun _ => norm_nonneg _) h1 h2
  simp only [one_mul, Real.one_rpow, integral_const, MeasurableSet.univ, measureReal_restrict_apply,
    univ_inter, Real.volume_real_Ioc_of_le hst, smul_eq_mul, mul_one] at this
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert this using 3
  norm_num

theorem IsW12Rep.norm_sub_le {T : ℝ} {c g : ℝ → ℂ} (h : IsW12Rep T c g) {s t : ℝ}
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    ‖c t - c s‖ ≤ Real.sqrt (t - s) * Real.sqrt (∫ u in Ioc 0 T, ‖g u‖ ^ 2) := by
  have hint : IntegrableOn g (Ioc 0 T) := by
    have : IsFiniteMeasure (volume.restrict (Ioc 0 T)) := by constructor; simp
    exact h.memLp.integrable (by norm_num)
  have hii : ∀ r ∈ Icc 0 T, IntervalIntegrable g volume 0 r := fun r hr =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1).2
      (hint.mono_set (Ioc_subset_Ioc le_rfl hr.2))
  rw [h.rep t ht, h.rep s hs, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hii t ht) (hii s hs),
    intervalIntegral.integral_of_le hst]
  have hsub : Ioc s t ⊆ Ioc 0 T := Ioc_subset_Ioc hs.1 ht.2
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_norm_le_sqrt_mul_sqrt hst (h.memLp.restrict (Ioc s t) |>.mono_measure
    (by rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_self_of_subset_left hsub]))).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (setIntegral_mono_set
    (h.memLp.norm.integrable_sq) (ae_of_all _ fun _ => by positivity)
    (Eventually.of_forall hsub))) (Real.sqrt_nonneg _)

end OneDim


section OneDimMore

theorem IsW12Rep.norm_sub_le_abs {T : ℝ} {c g : ℝ → ℂ} (h : IsW12Rep T c g) {s t : ℝ}
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    ‖c t - c s‖ ≤ Real.sqrt |t - s| * Real.sqrt (∫ u in Ioc 0 T, ‖g u‖ ^ 2) := by
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.2 hst)]; exact h.norm_sub_le hs ht hst
  · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hts)]
    exact h.norm_sub_le ht hs hts

theorem IsW12Rep.continuousOn {T : ℝ} {c g : ℝ → ℂ} (h : IsW12Rep T c g) :
    ContinuousOn c (Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  set L := Real.sqrt (∫ u in Ioc 0 T, ‖g u‖ ^ 2)
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  refine ⟨(ε / (L + 1)) ^ 2, by positivity, fun a ha hab => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (h.norm_sub_le_abs hb ha) ?_
  rw [Real.dist_eq] at hab
  have h1 : Real.sqrt |a - b| < ε / (L + 1) := by
    rw [show ε / (L + 1) = Real.sqrt ((ε / (L + 1)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt (abs_nonneg _) hab
  calc Real.sqrt |a - b| * L ≤ ε / (L + 1) * L := by gcongr
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

/-- Uniform bound from the `L²` bound and the `W^{1,2}` representation. -/
theorem IsW12Rep.norm_le {T : ℝ} (hT : 0 < T) {c g : ℝ → ℂ} (h : IsW12Rep T c g) {B0 B1 : ℝ}
    (h0 : ∫ u in Ioc 0 T, ‖c u‖ ^ 2 ≤ B0) (h1 : ∫ u in Ioc 0 T, ‖g u‖ ^ 2 ≤ B1) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ‖c t‖ ≤ Real.sqrt (B0 / T) + Real.sqrt T * Real.sqrt B1 := by
  have hcont := h.continuousOn
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT.le)
    ((hcont.norm).pow 2)
  have hint : IntegrableOn (fun u => ‖c u‖ ^ 2) (Ioc 0 T) :=
    (((hcont.norm).pow 2).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hT0 : T * ‖c t0‖ ^ 2 ≤ B0 := by
    have : ∫ _ in Ioc 0 T, ‖c t0‖ ^ 2 ≤ ∫ u in Ioc 0 T, ‖c u‖ ^ 2 :=
      setIntegral_mono_on (integrableOn_const (by simp)) hint measurableSet_Ioc
        fun u hu => hmin (Ioc_subset_Icc_self hu)
    simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
      Real.volume_real_Ioc_of_le hT.le, sub_zero, smul_eq_mul] at this
    linarith
  have hc0 : ‖c t0‖ ≤ Real.sqrt (B0 / T) := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hT]; linarith
  have hd := h.norm_sub_le_abs ht0 ht
  have habs : |t - t0| ≤ T := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, ht0.1, ht0.2]
  calc ‖c t‖ ≤ ‖c t0‖ + ‖c t - c t0‖ := by
        have := norm_add_le (c t0) (c t - c t0); simpa using this
    _ ≤ Real.sqrt (B0 / T) + Real.sqrt T * Real.sqrt B1 := by
        gcongr
        refine hd.trans ?_
        gcongr

end OneDimMore

/-! ### Simultaneous uniform extraction over countably many modes (Arzelà–Ascoli) -/

section Extraction

variable {T : ℝ}

/-- The restriction of a `W^{1,2}` time function to `[0,T]`, as a bounded continuous function. -/
def toBCF {c g : ℝ → ℂ} (h : IsW12Rep T c g) : Icc (0 : ℝ) T →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact ⟨(Icc 0 T).restrict c, h.continuousOn.restrict⟩

theorem toBCF_apply {c g : ℝ → ℂ} (h : IsW12Rep T c g) (t : Icc (0 : ℝ) T) :
    toBCF h t = c t := rfl

/-- **Simultaneous Arzelà–Ascoli extraction.**  For countably many modes `k`, if every
`c m k` is `W^{1,2}(0,T)` with `∫|c m k|² ≤ B₀ k` and `∫|∂ₜ c m k|² ≤ B₁ k` uniformly in `m`, a
single subsequence converges uniformly on `[0,T]` in every mode. -/
theorem exists_subseq_tendstoUniformlyOn {ι : Type*} [Countable ι] (hT : 0 < T)
    (c g : ℕ → ι → ℝ → ℂ) (hW : ∀ m k, IsW12Rep T (c m k) (g m k)) (B0 B1 : ι → ℝ)
    (h0 : ∀ m k, ∫ u in Ioc 0 T, ‖c m k u‖ ^ 2 ≤ B0 k)
    (h1 : ∀ m k, ∫ u in Ioc 0 T, ‖g m k u‖ ^ 2 ≤ B1 k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c' : ι → ℝ → ℂ, ∀ k, ContinuousOn (c' k) (Icc 0 T) ∧
      TendstoUniformlyOn (fun m => c (φ m) k) (c' k) atTop (Icc 0 T) := by
  classical
  let F : ℕ → ι → (Icc (0 : ℝ) T →ᵇ ℂ) := fun m k => toBCF (hW m k)
  have hcpt : ∀ k, IsCompact (closure (range fun m => F m k)) := by
    intro k
    apply BoundedContinuousFunction.arzela_ascoli
      (Metric.closedBall 0 (Real.sqrt (B0 k / T) + Real.sqrt T * Real.sqrt (B1 k)))
      (isCompact_closedBall _ _)
    · rintro f t ⟨m, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hW m k).norm_le hT (h0 m k) (h1 m k) t.2
    · intro x₀
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      set L := Real.sqrt (B1 k)
      refine ⟨(ε / (L + 1)) ^ 2, by positivity, fun x hx f => ?_⟩
      obtain ⟨m, hm⟩ := f.2
      have e : ∀ y, (f : Icc (0 : ℝ) T →ᵇ ℂ) y = c m k y := fun y => by rw [← hm]; rfl
      change dist ((f : Icc (0 : ℝ) T →ᵇ ℂ) x₀) ((f : Icc (0 : ℝ) T →ᵇ ℂ) x) < ε
      rw [e, e, dist_eq_norm, norm_sub_rev]
      refine lt_of_le_of_lt ((hW m k).norm_sub_le_abs x₀.2 x.2) ?_
      have hL : Real.sqrt (∫ u in Ioc 0 T, ‖g m k u‖ ^ 2) ≤ L := Real.sqrt_le_sqrt (h1 m k)
      have hx' : |(x : ℝ) - x₀| < (ε / (L + 1)) ^ 2 := by
        rw [Subtype.dist_eq, Real.dist_eq] at hx; exact hx
      have h1' : Real.sqrt |(x : ℝ) - x₀| < ε / (L + 1) := by
        rw [show ε / (L + 1) = Real.sqrt ((ε / (L + 1)) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
        exact Real.sqrt_lt_sqrt (abs_nonneg _) hx'
      have hL0 : 0 ≤ L := Real.sqrt_nonneg _
      calc Real.sqrt |(x : ℝ) - x₀| * Real.sqrt (∫ u in Ioc 0 T, ‖g m k u‖ ^ 2)
          ≤ ε / (L + 1) * L := mul_le_mul h1'.le hL (Real.sqrt_nonneg _) (by positivity)
        _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  have hS : IsCompact (Set.pi univ fun k => closure (range fun m => F m k)) :=
    isCompact_univ_pi hcpt
  obtain ⟨a, -, φ, hφ, hlim⟩ := hS.tendsto_subseq (x := fun m k => F m k)
    fun m => fun k _ => subset_closure ⟨m, rfl⟩
  refine ⟨φ, hφ, fun k t => if ht : t ∈ Icc 0 T then a k ⟨t, ht⟩ else 0, fun k => ?_⟩
  have hk : Tendsto (fun m => F (φ m) k) atTop (𝓝 (a k)) :=
    ((continuous_apply k).tendsto a).comp hlim
  have hres : ∀ t : Icc (0 : ℝ) T,
      (fun t => if ht : t ∈ Icc 0 T then a k ⟨t, ht⟩ else 0) (t : ℝ) = a k t := fun t =>
    dif_pos t.2
  constructor
  · refine continuousOn_iff_continuous_restrict.2 ?_
    convert (a k).continuous using 1
    funext t
    exact hres t
  · rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 hk
    have e : (fun t => if ht : t ∈ Icc 0 T then a k ⟨t, ht⟩ else 0) ∘ Subtype.val = ⇑(a k) :=
      funext hres
    rw [e]
    exact hu

end Extraction


/-! ### The Aubin–Lions–Simon theorem in coefficient form -/

section AubinLions

theorem norm_sub_sq_le_two (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have h0 := norm_nonneg (x - y)
  nlinarith [mul_self_le_mul_self h0 h, sq_nonneg (‖x‖ - ‖y‖)]

theorem setIntegral_sq_le_of_norm_le {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℂ} {ε : ℝ}
    (h : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ ε) : ∫ u in Ioc 0 T, ‖f u‖ ^ 2 ≤ ε ^ 2 * T := by
  have hb : ∀ t ∈ Ioc 0 T, ‖‖f t‖ ^ 2‖ ≤ ε ^ 2 := fun t ht => by
    rw [Real.norm_of_nonneg (by positivity)]
    have := h t (Ioc_subset_Icc_self ht)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 T)
    (by simp) hb
  rw [Real.volume_real_Ioc_of_le hT, sub_zero] at this
  exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact this)

/-- **Aubin–Lions–Simon compactness in coefficient form.**  Let `c m k` (`m ∈ ℕ`, modes `k` in a
countable set `ι`) be `W^{1,2}(0,T)` time coefficients with weak time derivatives `g m k`, and let
`w ≥ 1` be weights with finite sublevel sets (e.g. `w(k) = 1 + |k|²` on `ℤ³`).  Assume the
uniform spatial `H¹` bound `Σ_k w(k) ∫₀ᵀ |c m k|² ≤ B` and a per-mode time-derivative bound
`∫₀ᵀ |g m k|² ≤ B₁(k)` uniform in `m` — implied by any negative-norm bound, e.g.
`Σ_k w(k)⁻¹ ∫₀ᵀ |g m k|² ≤ B` (`∂ₜ ∈ L²_t H⁻¹_x`, `B₁ = B w`) or
`Σ_k w(k)⁻² ∫₀ᵀ |g m k|² ≤ B` (`∂ₜ ∈ L²_t H⁻²_x`, `B₁ = B w²`).
Then a subsequence converges strongly in `L²_t ℓ²_k`:
`Σ_k ∫₀ᵀ |c (φ m) k - c' k|² → 0`.  By Parseval this is strong `L²((0,T) × 𝕋³)` convergence of
the corresponding trigonometric fields. -/
theorem aubinLions_coefficients {ι : Type*} [Countable ι] {T : ℝ} (hT : 0 < T) (w : ι → ℝ)
    (hw1 : ∀ k, 1 ≤ w k) (hwfin : ∀ R, {k | w k ≤ R}.Finite)
    (c g : ℕ → ι → ℝ → ℂ) (hW : ∀ m k, IsW12Rep T (c m k) (g m k)) {B : ℝ}
    (h0s : ∀ m, Summable fun k => w k * ∫ u in Ioc 0 T, ‖c m k u‖ ^ 2)
    (h0 : ∀ m, ∑' k, w k * ∫ u in Ioc 0 T, ‖c m k u‖ ^ 2 ≤ B)
    (B1 : ι → ℝ) (h1 : ∀ m k, ∫ u in Ioc 0 T, ‖g m k u‖ ^ 2 ≤ B1 k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c' : ι → ℝ → ℂ,
      (∀ m, Summable fun k => ∫ u in Ioc 0 T, ‖c (φ m) k u - c' k u‖ ^ 2) ∧
      Tendsto (fun m => ∑' k, ∫ u in Ioc 0 T, ‖c (φ m) k u - c' k u‖ ^ 2) atTop (𝓝 0) := by
  classical
  set a : ℕ → ι → ℝ := fun m k => ∫ u in Ioc 0 T, ‖c m k u‖ ^ 2 with ha_def
  have ha0 : ∀ m k, 0 ≤ a m k := fun m k => integral_nonneg fun _ => by positivity
  have hw0 : ∀ k, 0 < w k := fun k => lt_of_lt_of_le one_pos (hw1 k)
  have hwa : ∀ m k, w k * a m k ≤ B := fun m k =>
    ((h0s m).le_tsum k fun j _ => mul_nonneg (hw0 j).le (ha0 m j)).trans (h0 m)
  have hB : 0 ≤ B := (tsum_nonneg fun k => mul_nonneg (hw0 k).le (ha0 0 k)).trans (h0 0)
  have haB : ∀ m k, a m k ≤ B := fun m k => by
    have := hwa m k
    nlinarith [hw1 k, ha0 m k]
  obtain ⟨φ, hφ, c', hc'⟩ := exists_subseq_tendstoUniformlyOn hT c g hW (fun _ => B)
    B1 haB h1
  refine ⟨φ, hφ, c', ?_⟩
  -- integrability
  have hcont : ∀ m k, ContinuousOn (c m k) (Icc 0 T) := fun m k => (hW m k).continuousOn
  have hintsq : ∀ f : ℝ → ℂ, ContinuousOn f (Icc 0 T) →
      IntegrableOn (fun u => ‖f u‖ ^ 2) (Ioc 0 T) := fun f hf =>
    ((hf.norm.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  set d : ℕ → ι → ℝ := fun m k => ∫ u in Ioc 0 T, ‖c (φ m) k u - c' k u‖ ^ 2 with hd_def
  set A : ι → ℝ := fun k => ∫ u in Ioc 0 T, ‖c' k u‖ ^ 2 with hA_def
  have hd0 : ∀ m k, 0 ≤ d m k := fun m k => integral_nonneg fun _ => by positivity
  have hA0 : ∀ k, 0 ≤ A k := fun k => integral_nonneg fun _ => by positivity
  have hdiffcont : ∀ m k, ContinuousOn (fun u => c (φ m) k u - c' k u) (Icc 0 T) :=
    fun m k => (hcont _ k).sub (hc' k).1
  have hd_le : ∀ m k, d m k ≤ 2 * a (φ m) k + 2 * A k := by
    intro m k
    have := integral_mono (μ := volume.restrict (Ioc 0 T)) (hintsq _ (hdiffcont m k))
      (((hintsq _ (hcont (φ m) k)).const_mul 2).add ((hintsq _ (hc' k).1).const_mul 2))
      fun u => norm_sub_sq_le_two (c (φ m) k u) (c' k u)
    simp only [Pi.add_apply] at this
    rw [integral_add ((hintsq _ (hcont (φ m) k)).const_mul 2)
      ((hintsq _ (hc' k).1).const_mul 2), integral_const_mul, integral_const_mul] at this
    exact this
  have hA_le : ∀ m k, A k ≤ 2 * a (φ m) k + 2 * d m k := by
    intro m k
    have := integral_mono (μ := volume.restrict (Ioc 0 T)) (hintsq _ (hc' k).1)
      (((hintsq _ (hcont (φ m) k)).const_mul 2).add ((hintsq _ (hdiffcont m k)).const_mul 2))
      fun u => by
        have := norm_sub_sq_le_two (c (φ m) k u) (c (φ m) k u - c' k u)
        simpa using this
    simp only [Pi.add_apply] at this
    rw [integral_add ((hintsq _ (hcont (φ m) k)).const_mul 2)
      ((hintsq _ (hdiffcont m k)).const_mul 2), integral_const_mul, integral_const_mul] at this
    exact this
  -- per-mode convergence
  have hd_tend : ∀ k, Tendsto (fun m => d m k) atTop (𝓝 0) := by
    intro k
    rw [Metric.tendsto_atTop]
    intro ε hε
    set δ := Real.sqrt (ε / (2 * T))
    have hδ : 0 < δ := Real.sqrt_pos.2 (by positivity)
    obtain ⟨M, hM⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 (hc' k).2) δ hδ)
    refine ⟨M, fun m hm => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd0 m k)]
    have hb : ∀ t ∈ Icc 0 T, ‖c (φ m) k t - c' k t‖ ≤ δ := fun t ht => by
      have := hM m hm t ht
      rw [dist_eq_norm, norm_sub_rev] at this
      exact this.le
    refine lt_of_le_of_lt (setIntegral_sq_le_of_norm_le hT.le hb) ?_
    rw [Real.sq_sqrt (by positivity)]
    rw [div_mul_eq_mul_div, mul_comm, ← div_mul_eq_mul_div, div_mul_eq_mul_div]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  -- the limit energy is summable
  have hAsum_fin : ∀ F : Finset ι, ∑ k ∈ F, w k * A k ≤ 2 * B := by
    intro F
    have hlim : Tendsto (fun m => 2 * B + 2 * ∑ k ∈ F, w k * d m k) atTop (𝓝 (2 * B)) := by
      have := (tendsto_finsetSum F fun k _ => (hd_tend k).const_mul (w k)).const_mul 2
      simpa using this.const_add (2 * B)
    refine ge_of_tendsto' hlim fun m => ?_
    calc ∑ k ∈ F, w k * A k ≤ ∑ k ∈ F, (2 * (w k * a (φ m) k) + 2 * (w k * d m k)) :=
          Finset.sum_le_sum fun k _ => by
            have := mul_le_mul_of_nonneg_left (hA_le m k) (hw0 k).le; linarith
      _ = 2 * ∑ k ∈ F, w k * a (φ m) k + 2 * ∑ k ∈ F, w k * d m k := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * B + 2 * ∑ k ∈ F, w k * d m k := by
          gcongr
          exact ((h0s (φ m)).sum_le_tsum F fun j _ => mul_nonneg (hw0 j).le (ha0 _ j)).trans
            (h0 (φ m))
  have hwA0 : 0 ≤ fun k => w k * A k := fun k => mul_nonneg (hw0 k).le (hA0 k)
  have hAsum : Summable fun k => w k * A k := summable_of_sum_le hwA0 hAsum_fin
  have hAtsum : ∑' k, w k * A k ≤ 2 * B := Real.tsum_le_of_sum_le hwA0 hAsum_fin
  -- summability of the errors
  have hdom : ∀ m k, d m k ≤ 2 * (w k * a (φ m) k) + 2 * (w k * A k) := fun m k => by
    have := hd_le m k
    have h1' : a (φ m) k ≤ w k * a (φ m) k := le_mul_of_one_le_left (ha0 _ k) (hw1 k)
    have h2' : A k ≤ w k * A k := le_mul_of_one_le_left (hA0 k) (hw1 k)
    linarith
  have hsum2 : ∀ m, Summable fun k => 2 * (w k * a (φ m) k) + 2 * (w k * A k) := fun m =>
    ((h0s (φ m)).mul_left 2).add (hAsum.mul_left 2)
  have hdsum : ∀ m, Summable fun k => d m k := fun m =>
    Summable.of_nonneg_of_le (hd0 m) (hdom m) (hsum2 m)
  refine ⟨hdsum, ?_⟩
  -- tail argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R := 12 * B / ε + 1 with hR
  have hRpos : 0 < R := by positivity
  set Fs := (hwfin R).toFinset
  have hfin := tendsto_finsetSum Fs fun k _ => hd_tend k
  simp only [Finset.sum_const_zero] at hfin
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hfin (ε / 2) (by positivity)
  refine ⟨M, fun m hm => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg (hd0 m))]
  have hhead := hM m hm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun k _ => hd0 m k)] at hhead
  have htail : ∑' k : ↑((Fs : Set ι)ᶜ), d m k ≤ 6 * B / R := by
    have hle : ∀ k : ↑((Fs : Set ι)ᶜ), d m k ≤
        (2 / R) * (w k * a (φ m) k + w k * A k) := by
      rintro ⟨k, hk⟩
      have hwk : R < w k := by
        simp only [Fs, Set.mem_compl_iff, Finset.mem_coe,
          Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hk
        exact hk
      have e1 : a (φ m) k ≤ (w k * a (φ m) k) / R := by
        rw [le_div_iff₀ hRpos]; nlinarith [ha0 (φ m) k]
      have e2 : A k ≤ (w k * A k) / R := by
        rw [le_div_iff₀ hRpos]; nlinarith [hA0 k]
      have := hd_le m k
      calc d m k ≤ 2 * a (φ m) k + 2 * A k := this
        _ ≤ 2 * ((w k * a (φ m) k) / R) + 2 * ((w k * A k) / R) := by linarith
        _ = (2 / R) * (w k * a (φ m) k + w k * A k) := by ring
    have hS : Summable fun k => (2 / R) * (w k * a (φ m) k + w k * A k) :=
      ((h0s (φ m)).add hAsum).mul_left _
    calc ∑' k : ↑((Fs : Set ι)ᶜ), d m k
        ≤ ∑' k : ↑((Fs : Set ι)ᶜ), (2 / R) * (w k * a (φ m) k + w k * A k) :=
          Summable.tsum_le_tsum hle ((hdsum m).subtype _) (hS.subtype _)
      _ ≤ ∑' k, (2 / R) * (w k * a (φ m) k + w k * A k) := by
          rw [← hS.sum_add_tsum_compl (s := Fs)]
          have : 0 ≤ ∑ k ∈ Fs, (2 / R) * (w k * a (φ m) k + w k * A k) :=
            Finset.sum_nonneg fun k _ => by
              have := mul_nonneg (hw0 k).le (ha0 (φ m) k)
              have := mul_nonneg (hw0 k).le (hA0 k)
              positivity
          linarith
      _ = (2 / R) * (∑' k, w k * a (φ m) k + ∑' k, w k * A k) := by
          rw [tsum_mul_left, (h0s (φ m)).tsum_add hAsum]
      _ ≤ (2 / R) * (B + 2 * B) := by gcongr; exact h0 (φ m)
      _ = 6 * B / R := by ring
  have hsplit := (hdsum m).sum_add_tsum_compl (s := Fs)
  have hRB : 6 * B / R ≤ ε / 2 := by
    rw [div_le_iff₀ hRpos, hR]
    field_simp
    nlinarith
  rw [← hsplit]
  linarith

/-- Non-vacuity of `aubinLions_coefficients`: the zero family on modes `ℕ` with weights
`w(k) = 1 + k` satisfies all hypotheses. -/
example : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c' : ℕ → ℝ → ℂ,
    (∀ _m : ℕ, Summable fun k => ∫ u in Ioc 0 1, ‖(0 : ℂ) - c' k u‖ ^ 2) ∧
    Tendsto (fun _m : ℕ => ∑' k, ∫ u in Ioc 0 1, ‖(0 : ℂ) - c' k u‖ ^ 2) atTop (𝓝 0) := by
  have hW : ∀ (m k : ℕ), IsW12Rep 1 (fun _ => (0 : ℂ)) (fun _ => 0) := fun _ _ =>
    ⟨MemLp.zero', fun t _ => by simp⟩
  obtain ⟨φ, hφ, c', h1, h2⟩ := aubinLions_coefficients (ι := ℕ) one_pos (fun k => 1 + k)
    (fun k => by simp) (fun R => (Set.finite_Iio (⌈R⌉₊ + 1)).subset fun k hk => by
      simp only [Set.mem_setOf_eq] at hk
      simp only [Set.mem_Iio]
      have := Nat.le_ceil R
      exact_mod_cast (show (k : ℝ) < ⌈R⌉₊ + 1 by linarith))
    (fun _ _ _ => 0) (fun _ _ _ => 0) hW (B := 0) (fun _ => by simp) (fun _ => by simp)
    (fun _ => 0) (fun _ _ => by simp)
  exact ⟨φ, hφ, c', h1, h2⟩

end AubinLions

end RenewalGeometry.CoefficientAubinLions
