/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMRegularFields

/-!
# The regular branch, spinor part: the Dirac coefficient model gives the hypotheses of
  `prop:dirac-stability` (`thm:regular-branch`, lemma L4)

`thm:regular-branch` assumes that "the reconstructed spinors and dual spinors obey the Lorentzian
systems of `prop:dirac-stability`" and proves that "the stronger bounds `eq:regular-bosonic-bound`
also give uniform coefficient convergence and the bounds required by `prop:dirac-stability`".  In
fixed local gauges and spin frames the reconstructed Dirac–Yukawa operator has principal
coefficients `A^μ = 𝒜^μ(e)` (the `γ`-matrices contracted with the frame) and zeroth-order
coefficient `B = ℬ(e, ∂e, A, H, θ)` (spin connection, gauge connection, Yukawa term, couplings).
`DiracModel` records such coefficient maps: `𝒜^μ` of class `C¹` and Hermitian, `ℬ` continuous.

* `UCauchyOn.extend_slab`, `mem_of_ae_box`, `bounded_on_slab` — from the open chart box
  `(t₀, t₁) × (0,1)³` to the closed slab `[t₀, t₁] × ℝ³` (continuity and spatial periodicity).
* **`diracStabilityHyp_of_model`** (L4) — `C¹`-Cauchy bosonic fields on the box, the coframe chart
  condition, convergent banks in a compact physical set, the Dirac model with uniformly positive
  `𝒜⁰`, the `L^∞_tH²_x` bound, Cauchy initial data and residuals tending to zero in `L²_tL²_x` give
  `DiracStabilityHyp` (coefficients bounded, `𝒜^μ ∘ e_h` Lipschitz on the slab, all coefficients
  uniformly Cauchy).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal BigOperators

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace RegularBranch

open SobolevOpen (pd box IsTest MemW12)

set_option linter.unusedSectionVars false

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-! ### From the open box to the closed slab -/

theorem closure_slabChart {t₀ t₁ : ℝ} {h0 : 0 < t₀} {h01 : t₀ < t₁} {h1 : t₁ < T} :
    closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set =
      univ.pi fun i => Icc ((slabChart t₀ t₁ h0 h01 h1 (T := T)).a i)
        ((slabChart t₀ t₁ h0 h01 h1 (T := T)).b i) := by
  show closure (Set.pi univ fun i => Ioo _ _) = _
  rw [closure_pi_set]
  refine Set.pi_congr rfl fun i _ => closure_Ioo ((slabChart t₀ t₁ h0 h01 h1).lt i).ne

/-- The periodic reduction of a slab point into the closed fundamental box. -/
theorem exists_shift_mem_closure {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {x : E4}
    (hx : x ∈ slab t₀ t₁) : ∃ k : Fin 3 → ℤ, x + spatialShift k ∈
      closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set := by
  refine ⟨fun i => -⌊x i.succ⌋, ?_⟩
  rw [closure_slabChart]
  intro i _
  induction i using Fin.cases with
  | zero =>
    simp only [slabChart, Pi.add_apply, spatialShift_zero, add_zero, Fin.cons_zero]
    exact hx
  | succ j =>
    simp only [slabChart, Pi.add_apply, spatialShift_succ, Fin.cons_succ, Pi.zero_apply,
      Pi.one_apply, Int.cast_neg]
    have h1 := Int.floor_le (x j.succ)
    have h2 := Int.lt_floor_add_one (x j.succ)
    constructor <;> linarith

theorem mem_cylSlab_of_slab {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h1 : t₁ < T) {x : E4}
    (hx : x ∈ slab t₀ t₁) : x ∈ cylSlab T :=
  ⟨lt_of_lt_of_le h0 hx.1, lt_of_le_of_lt hx.2 h1⟩

theorem mem_slab_of_closure {t₀ t₁ : ℝ} {h0 : 0 < t₀} {h01 : t₀ < t₁} {h1 : t₁ < T} {x : E4}
    (hx : x ∈ closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set) : x ∈ slab t₀ t₁ := by
  rw [closure_slabChart] at hx
  have := hx 0 (mem_univ _)
  simp only [slabChart, Fin.cons_zero] at this
  exact this

/-- **Uniform Cauchy property extends from the box to the closed slab** (continuity and spatial
periodicity). -/
theorem UCauchyOn.extend_slab {F : Type*} [NormedAddCommGroup F] {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {u : ℕ → E4 → F} (hc : ∀ n, ContinuousOn (u n) (cylSlab T))
    (hp : ∀ n k x, u n (x + spatialShift k) = u n x)
    (h : UCauchyOn (slabChart t₀ t₁ h0 h01 h1 (T := T)).set u) : UCauchyOn (slab t₀ t₁) u := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun m n hm hn x hx => ?_⟩
  obtain ⟨k, hk⟩ := exists_shift_mem_closure h0 h01 h1 hx
  rw [← hp m k x, ← hp n k x]
  have hxs := mem_cylSlab_of_slab h0 h1 (mem_slab_of_closure hk)
  have hca : ∀ j, ContinuousAt (u j) (x + spatialShift k) := fun j =>
    (hc j).continuousAt ((isOpen_cylSlab T).mem_nhds hxs)
  exact ContinuousWithinAt.closure_le hk
    (((hca m).sub (hca n)).norm.continuousWithinAt) continuousWithinAt_const
    (fun y hy => hN m n hm hn y hy)

/-- Continuous periodic fields are bounded on the closed slab. -/
theorem bounded_on_slab {F : Type*} [NormedAddCommGroup F] {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {f : E4 → F} (hc : ContinuousOn f (cylSlab T))
    (hp : ∀ k x, f (x + spatialShift k) = f x) : ∃ B, ∀ x ∈ slab t₀ t₁, ‖f x‖ ≤ B := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  obtain ⟨B, hB⟩ := Q.isCompact_closure.exists_bound_of_continuousOn
    (hc.mono Q.closure_subset_cylSlab)
  refine ⟨B, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := exists_shift_mem_closure h0 h01 h1 hx
  rw [← hp k x]; exact hB _ hk

/-- **Values a.e. in a closed set on the box lie in it on the whole closed slab.** -/
theorem mem_of_ae_box {F : Type*} [NormedAddCommGroup F] {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {f : E4 → F} (hc : ContinuousOn f (cylSlab T))
    (hp : ∀ k x, f (x + spatialShift k) = f x) {K : Set F} (hK : IsClosed K)
    (hae : ∀ᵐ x ∂(slabChart t₀ t₁ h0 h01 h1 (T := T)).μ, f x ∈ K) :
    ∀ x ∈ slab t₀ t₁, f x ∈ K := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  intro x hx
  obtain ⟨k, hk⟩ := exists_shift_mem_closure h0 h01 h1 hx
  rw [← hp k x]
  set y := x + spatialShift k
  by_contra hy
  have hys := mem_cylSlab_of_slab h0 h1 (mem_slab_of_closure hk)
  have hca : ContinuousAt f y := hc.continuousAt ((isOpen_cylSlab T).mem_nhds hys)
  obtain ⟨V, hVsub, hVo, hyV⟩ := mem_nhds_iff.mp (hca.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hy))
  have hne : (V ∩ Q.set).Nonempty := mem_closure_iff.mp hk V hVo hyV
  have hpos : 0 < volume (V ∩ Q.set) := (hVo.inter Q.isOpen).measure_pos volume hne
  have h0' : volume (V ∩ Q.set) = 0 := by
    have h2 := (ae_restrict_iff' Q.isOpen.measurableSet).mp hae
    rw [ae_iff] at h2
    refine measure_mono_null (fun z hz => ?_) h2
    exact fun h => hVsub hz.1 (h hz.2)
  exact absurd h0' hpos.ne'

/-! ### Products and compositions of uniformly Cauchy sequences -/

theorem UCauchyOn.prod {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G] {S : Set E4}
    {u : ℕ → E4 → F} {v : ℕ → E4 → G} (hu : UCauchyOn S u) (hv : UCauchyOn S v) :
    UCauchyOn S (fun n x => (u n x, v n x)) := fun ε hε => by
  obtain ⟨N, hN⟩ := hu ε hε
  obtain ⟨N', hN'⟩ := hv ε hε
  exact ⟨max N N', fun m n hm hn x hx => by
    rw [Prod.norm_def]
    exact max_le (hN m n (le_of_max_le_left hm) (le_of_max_le_left hn) x hx)
      (hN' m n (le_of_max_le_right hm) (le_of_max_le_right hn) x hx)⟩

theorem UCauchyOn.const_x {F : Type*} [NormedAddCommGroup F] {S : Set E4} {c : ℕ → F}
    (hc : CauchySeq c) : UCauchyOn S (fun n _ => c n) := fun ε hε => by
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc ε hε
  exact ⟨N, fun m n hm hn x _ => by rw [← dist_eq_norm]; exact (hN m hm n hn).le⟩

/-- Compositions with a continuous map, values in a compact set: uniformly Cauchy and bounded. -/
theorem UCauchyOn.comp_compact {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {S : Set E4} {u : ℕ → E4 → F} {K : Set F} (hK : IsCompact K) {Φ : F → G}
    (hΦ : Continuous Φ) (hval : ∀ n, ∀ x ∈ S, u n x ∈ K) (h : UCauchyOn S u) :
    UCauchyOn S (fun n x => Φ (u n x)) ∧ ∃ B, ∀ n, ∀ x ∈ S, ‖Φ (u n x)‖ ≤ B := by
  refine ⟨h.comp_uniformContinuousOn (hK.uniformContinuousOn_of_continuous hΦ.continuousOn) hval,
    ?_⟩
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  exact ⟨B, fun n x hx => hB _ (hval n x hx)⟩

/-! ### The Dirac coefficient model -/

/-- The bank coordinates as a vector. -/
def bankVec (θ : CoefficientBank Ysec) : (Fin 7 → ℝ) × (Ysec → Fin 3 → Fin 3 → ℂ) :=
  ((bankCoords θ).1, fun y => (bankCoords θ).2 y)

theorem continuous_bankVec_of_coords :
    Continuous (fun p : (Fin 7 → ℝ) × (Ysec → Matrix (Fin 3) (Fin 3) ℂ) =>
      ((p.1, fun y => p.2 y) : (Fin 7 → ℝ) × (Ysec → Fin 3 → Fin 3 → ℂ))) :=
  continuous_fst.prodMk (continuous_pi fun y => continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply y).comp continuous_snd)))

/-- The arguments of the zeroth-order coefficient: `(e, ∂e, A, H, θ)`. -/
abbrev BArg (Ysec : Type) := CoframeFibre × ((Fin 4 → CoframeFibre) × (ConnFibre × (HiggsFibre ×
  ((Fin 7 → ℝ) × (Ysec → Fin 3 → Fin 3 → ℂ)))))

/-- **The Dirac coefficient model** (fixed local gauges and spin frames): principal coefficients
`A^μ = 𝒜^μ(e)` — `C¹` and Hermitian (the `γ`-matrices contracted with the frame) — and the
zeroth-order coefficient `B = ℬ(e, ∂e, A, H, θ)` continuous (spin connection, gauge connection,
Yukawa coupling). -/
structure DiracModel (N : Type) [Fintype N] (Ysec : Type) where
  A : Fin 4 → CoframeFibre → N → N → ℂ
  B : BArg Ysec → N → N → ℂ
  smooth_A : ∀ μ, ContDiff ℝ 1 (A μ)
  cont_B : Continuous B
  herm : ∀ μ e i j, A μ e j i = star (A μ e i j)

/-- The coefficient fields of a model along fields `w` and bank `θ`. -/
def DiracModel.Acoef {N : Type} [Fintype N] (D : DiracModel N Ysec) (w : SmoothFields T left)
    (μ : Fin 4) (x : E4) : N → N → ℂ :=
  D.A μ (w.z.e x)

/-- The argument tuple of `ℬ`. -/
def bArg (w : SmoothFields T left) (θ : CoefficientBank Ysec) (x : E4) : BArg Ysec :=
  (w.z.e x, fun μ => pd w.z.e μ x, w.z.A x, w.z.H x, bankVec θ)

def DiracModel.Bcoef {N : Type} [Fintype N] (D : DiracModel N Ysec) (w : SmoothFields T left)
    (θ : CoefficientBank Ysec) (x : E4) : N → N → ℂ :=
  D.B (bArg w θ x)

/-- The residual of the Dirac system `Σ_μ A^μ ∂_μψ + Bψ`. -/
def residual {N : Type} [Fintype N] (Acoef : Fin 4 → E4 → N → N → ℂ) (Bcoef : E4 → N → N → ℂ)
    (ψ : E4 → N → ℂ) (x : E4) : N → ℂ :=
  ∑ μ, mvec (Acoef μ x) (pd ψ μ x) + mvec (Bcoef x) (ψ x)


/-! ### Lipschitz bounds -/

theorem norm_clm_le_sum' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E4 →L[ℝ] F) : ‖A‖ ≤ ∑ μ, ‖A (Pi.single μ 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun v => ?_
  have hv : v = ∑ μ, v μ • (Pi.single μ (1 : ℝ) : E4) := by
    ext j; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun μ _ => ?_
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm ▸ (norm_le_pi_norm v μ))
    (norm_nonneg _)

/-- A `C¹` map is Lipschitz on a closed ball (finite-dimensional source). -/
theorem exists_lipschitzOnWith_closedBall {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : F → G}
    (hf : ContDiff ℝ 1 f) (R : ℝ) : ∃ K : ℝ≥0, LipschitzOnWith K f (Metric.closedBall 0 R) := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : F) R).exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨⟨max K 0, le_max_right _ _⟩, Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (hf.differentiable one_ne_zero) x) (fun x hx => ?_) (convex_closedBall 0 R)⟩
  show ‖fderiv ℝ f x‖ ≤ max K 0
  exact (hK x hx).trans (le_max_left _ _)

/-! ### L4: the hypotheses of `prop:dirac-stability` from the model -/

theorem cauchySeq_bankVec {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (h : BankTendsto θ θ₀) : CauchySeq (fun n => bankVec (θ n)) :=
  ((continuous_bankVec_of_coords.tendsto _).comp h).cauchySeq

set_option maxHeartbeats 1600000 in
/-- **L4: the Dirac coefficient model gives `DiracStabilityHyp`.**  Let the bosonic fields be
`C¹`-Cauchy on the chart box `Q = (t₀, t₁) × (0,1)³` with coframe values in a compact subset of the
nondegenerate chart, the banks converge in a compact physical set, and let the spinor fields
`ψ_h` obey the systems `Σ_μ 𝒜^μ(e_h)∂_μψ_h + ℬ(e_h, ∂e_h, A_h, H_h, θ_h)ψ_h = r_h` of a
`DiracModel` with uniformly positive `𝒜⁰(e_h)`, uniformly bounded `L^∞_tH²_x` norms, Cauchy
initial data in `L²(Σ)` and residuals `r_h → 0` in `L²(I × Σ)`.  Then the hypotheses
`DiracStabilityHyp t₀ t₁ ψ` of `prop:dirac-stability` hold: the coefficients are bounded,
`𝒜^μ(e_h)` uniformly Lipschitz on the slab (`e_h` uniformly `C¹`), and all coefficients are
uniformly Cauchy. -/
theorem diracStabilityHyp_of_model {N : Type} [Fintype N] {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {w : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec}
    (hC1 : BosonicC1Cauchy (slabChart t₀ t₁ h0 h01 h1 (T := T)) w)
    (hch : CoframeChartCondition (slabChart t₀ t₁ h0 h01 h1 (T := T)) w)
    (hbank : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P) {θ₀ : CoefficientBank Ysec}
    (hθ : BankTendsto θ θ₀) (D : DiracModel N Ysec) {ψ : ℕ → E4 → N → ℂ}
    (hψ : ∀ n, ContDiffOn ℝ ∞ (ψ n) (cylSlab T))
    (hpos : ∃ c > (0 : ℝ), ∀ n, ∀ x ∈ slab t₀ t₁, ∀ ξ : N → ℂ,
      c * ∑ i, ‖ξ i‖ ^ 2 ≤ (∑ i, ∑ j, star (ξ i) * D.A 0 ((w n).z.e x) i j * ξ j).re)
    (hH2 : ∃ Cb : ℝ≥0, ∀ n, ∀ t ∈ Icc t₀ t₁, spatialH2 (ψ n) t ≤ Cb)
    (hinit : ∀ ε > (0 : ℝ), ∃ N₀, ∀ m ≥ N₀, ∀ n ≥ N₀,
      eLpNorm (fun y : Fin 3 → ℝ => ψ m (Fin.cons t₀ y) - ψ n (Fin.cons t₀ y)) 2
        (volume.restrict cube3) ≤ ENNReal.ofReal ε)
    (hres : Tendsto (fun n => eLpNorm (residual (fun μ => D.Acoef (w n) μ) (D.Bcoef (w n) (θ n))
      (ψ n)) 2 (volume.restrict (slabFund t₀ t₁))) atTop (𝓝 0)) :
    DiracStabilityHyp t₀ t₁ ψ := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  set S := slab t₀ t₁
  have hSm : MeasurableSet S := (measurable_pi_apply 0) measurableSet_Icc
  have hFm : MeasurableSet (slabFund t₀ t₁) := by
    have e : slabFund t₀ t₁ = (fun x : E4 => x 0) ⁻¹' Icc t₀ t₁ ∩
        ⋂ i : Fin 3, (fun x : E4 => x i.succ) ⁻¹' Ico 0 1 := by
      ext x; simp [slabFund]
    rw [e]
    exact ((measurable_pi_apply 0) measurableSet_Icc).inter
      (MeasurableSet.iInter fun i => (measurable_pi_apply _) measurableSet_Ico)
  obtain ⟨Ke, hKe, hKn⟩ := hch
  obtain ⟨P, hP, hθP⟩ := hbank
  have hsl : ∀ x ∈ S, x ∈ cylSlab T := fun x hx => mem_cylSlab_of_slab h0 h1 hx
  -- periodicity
  have pe := fun n => (w n).periodic_e
  have pA := fun n => (w n).periodic_A
  have pH := fun n => (w n).periodic_H
  have pde : ∀ n k x, (fun μ => pd (w n).z.e μ (x + spatialShift k)) = fun μ => pd (w n).z.e μ x :=
    fun n k x => funext fun μ => DiracStab.pd_periodic' (pe n) μ k x
  -- continuity
  have ce := fun n => (w n).smooth_e.continuousOn
  have cA := fun n => (w n).smooth_A.continuousOn
  have cH := fun n => (w n).smooth_H.continuousOn
  have cde : ∀ n, ContinuousOn (fun x => fun μ => pd (w n).z.e μ x) (cylSlab T) := fun n =>
    continuousOn_pi.mpr fun μ => continuousOn_pd_slab (w n).smooth_e μ
  -- the slab Cauchy properties
  have Ue : UCauchyOn S (fun n => (w n).z.e) :=
    UCauchyOn.extend_slab h0 h01 h1 ce (fun n => pe n) hC1.1
  have Ude : UCauchyOn S (fun n x => fun μ => pd (w n).z.e μ x) := by
    refine UCauchyOn.pi fun μ => ?_
    exact UCauchyOn.extend_slab h0 h01 h1 (fun n => continuousOn_pd_slab (w n).smooth_e μ)
      (fun n => DiracStab.pd_periodic' (pe n) μ) (hC1.2.1 μ)
  have UA : UCauchyOn S (fun n => (w n).z.A) :=
    UCauchyOn.extend_slab h0 h01 h1 cA (fun n => pA n) hC1.2.2.1
  have UH : UCauchyOn S (fun n => (w n).z.H) :=
    UCauchyOn.extend_slab h0 h01 h1 cH (fun n => pH n) hC1.2.2.2.2.1
  have Uθ : UCauchyOn S (fun n (_ : E4) => bankVec (θ n)) := UCauchyOn.const_x (cauchySeq_bankVec hθ)
  -- values
  have vKe : ∀ n, ∀ x ∈ S, (w n).z.e x ∈ Ke := fun n =>
    mem_of_ae_box h0 h01 h1 (ce n) (pe n) hKe.1.isClosed (hKn n)
  have bnd : ∀ {F : Type} [NormedAddCommGroup F] {u : ℕ → E4 → F}, UCauchyOn S u →
      (∀ n, ContinuousOn (u n) (cylSlab T)) → (∀ n k x, u n (x + spatialShift k) = u n x) →
      ∃ B, ∀ n, ∀ x ∈ S, ‖u n x‖ ≤ B := fun h hc hp =>
    h.bounded fun n => bounded_on_slab h0 h01 h1 (hc n) (hp n)
  obtain ⟨Cde, hCde⟩ := bnd Ude cde (fun n k x => pde n k x)
  obtain ⟨CA, hCA⟩ := bnd UA cA pA
  obtain ⟨CH, hCH⟩ := bnd UH cH pH
  set KB : Set (BArg Ysec) := Ke ×ˢ (Metric.closedBall 0 Cde ×ˢ (Metric.closedBall 0 CA ×ˢ
    (Metric.closedBall 0 CH ×ˢ ((fun p : (Fin 7 → ℝ) × (Ysec → Matrix (Fin 3) (Fin 3) ℂ) =>
      ((p.1, fun y => p.2 y) : (Fin 7 → ℝ) × (Ysec → Fin 3 → Fin 3 → ℂ))) '' (bankCoords '' P)))))
  have hKB : IsCompact KB := hKe.1.prod ((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
      (hP.1.image continuous_bankVec_of_coords))))
  have vKB : ∀ n, ∀ x ∈ S, bArg (w n) (θ n) x ∈ KB := fun n x hx =>
    ⟨vKe n x hx, mem_closedBall_zero_iff.mpr (hCde n x hx), mem_closedBall_zero_iff.mpr
      (hCA n x hx), mem_closedBall_zero_iff.mpr (hCH n x hx),
      ⟨bankCoords (θ n), ⟨θ n, hθP n, rfl⟩, rfl⟩⟩
  have UArg : UCauchyOn S (fun n x => bArg (w n) (θ n) x) :=
    Ue.prod (Ude.prod (UA.prod (UH.prod Uθ)))
  obtain ⟨UB, CB, hCB⟩ := UArg.comp_compact hKB D.cont_B vKB
  -- the principal coefficients
  have UAc : UCauchyOn S (fun n x => fun μ => D.A μ ((w n).z.e x)) :=
    UCauchyOn.pi fun μ => (Ue.comp_compact hKe.1 (D.smooth_A μ).continuous vKe).1
  obtain ⟨CAc, hCAc⟩ : ∃ C, ∀ μ, ∀ e ∈ Ke, ‖D.A μ e‖ ≤ C := by
    choose Cμ hCμ using fun μ => hKe.1.exists_bound_of_continuousOn (D.smooth_A μ).continuous.continuousOn
    exact ⟨∑ μ, |Cμ μ|, fun μ e he => (hCμ μ e he).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun μ => |Cμ μ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ μ)))⟩
  -- Lipschitz constants
  obtain ⟨R, hR⟩ := hKe.1.isBounded.subset_closedBall 0
  choose LA hLA using fun μ => exists_lipschitzOnWith_closedBall (D.smooth_A μ) R
  have hCde0 : 0 ≤ Cde := le_trans (norm_nonneg _) (hCde 0 _ (show (Fin.cons t₀ 0 : E4) ∈ S by
    simp [S, slab, h01.le]))
  set Le : ℝ≥0 := ⟨4 * Cde, by positivity⟩
  have Lip_e : ∀ n, LipschitzOnWith Le (w n).z.e S := by
    intro n
    refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x hx => differentiableAt_of_contDiffOn_slab (w n).smooth_e (hsl x hx))
      (fun x hx => ?_) ?_
    · show ‖fderiv ℝ (w n).z.e x‖ ≤ 4 * Cde
      refine (norm_clm_le_sum' _).trans ?_
      calc ∑ μ, ‖fderiv ℝ (w n).z.e x (Pi.single μ 1)‖ ≤ ∑ _μ : Fin 4, Cde :=
            Finset.sum_le_sum fun μ _ => (norm_le_pi_norm (fun μ => pd (w n).z.e μ x) μ).trans
              (hCde n x hx)
        _ = 4 * Cde := by simp
    · exact (convex_Icc t₀ t₁).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0)
  -- the constant
  obtain ⟨CH2, hCH2⟩ := hH2
  set Cb : ℝ≥0 := ⟨max (max (max |CAc| |CB|) (∑ μ, (LA μ * Le : ℝ))) CH2, by positivity⟩
  obtain ⟨c, hc, hcpos⟩ := hpos
  refine ⟨fun n μ x => D.A μ ((w n).z.e x), fun n x => D.B (bArg (w n) (θ n) x),
    fun n μ k x => by simp only [pe n k x], fun n k x => by
      simp only [bArg, pe n k x, pA n k x, pH n k x, pde n k x],
    fun n => ?_, fun n μ x i j => D.herm μ _ i j, ⟨c, hc, hcpos⟩, ⟨Cb, fun n => ⟨fun μ => ⟨?_, ?_⟩,
      ?_, fun t ht => (hCH2 n t ht).trans (by
        have : (CH2 : ℝ) ≤ Cb := le_max_right _ _
        exact_mod_cast this)⟩⟩, ?_, hinit, ?_⟩
  · -- measurability
    have hcont : ContinuousOn (fun x => D.B (bArg (w n) (θ n) x)) S := by
      refine D.cont_B.comp_continuousOn ?_
      exact ((ce n).mono hsl).prodMk (((cde n).mono hsl).prodMk (((cA n).mono hsl).prodMk
        (((cH n).mono hsl).prodMk continuousOn_const)))
    exact hcont.aestronglyMeasurable hSm
  · intro x hx
    have := hCAc μ _ (vKe n x hx)
    have h2 : |CAc| ≤ (Cb : ℝ) := le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
      (le_max_left _ _))
    exact this.trans ((le_abs_self _).trans h2)
  · have h1' := (hLA μ).comp (Lip_e n) (fun x hx => hR (vKe n x hx))
    refine h1'.weaken ?_
    have : (LA μ * Le : ℝ) ≤ ∑ μ, (LA μ * Le : ℝ) := Finset.single_le_sum
      (f := fun μ => (LA μ * Le : ℝ)) (fun _ _ => by positivity) (Finset.mem_univ μ)
    have h3 : (∑ μ, (LA μ * Le : ℝ)) ≤ Cb := le_trans (le_max_right _ _) (le_max_left _ _)
    exact_mod_cast this.trans h3
  · refine (ae_restrict_iff' hSm).mpr (Eventually.of_forall fun x hx => ?_)
    have h2 : |CB| ≤ (Cb : ℝ) := le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
      (le_max_left _ _))
    exact (hCB n x hx).trans ((le_abs_self _).trans h2)
  · -- coefficients Cauchy
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := UAc ε hε
    obtain ⟨N₂, hN₂⟩ := UB ε hε
    refine ⟨max N₁ N₂, fun m hm n hn => ⟨fun μ x hx => ?_, ?_⟩⟩
    · exact (norm_le_pi_norm (fun μ => D.A μ ((w m).z.e x) - D.A μ ((w n).z.e x)) μ).trans
        (hN₁ m n (le_of_max_le_left hm) (le_of_max_le_left hn) x hx)
    · refine (ae_restrict_iff' hSm).mpr (Eventually.of_forall fun x hx => ?_)
      exact hN₂ m n (le_of_max_le_right hm) (le_of_max_le_right hn) x hx
  · -- residuals Cauchy
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := (ENNReal.tendsto_atTop_zero.mp hres) (ENNReal.ofReal (ε / 2))
      (by simpa using hε)
    refine ⟨N₀, fun m hm n hn => ?_⟩
    have hmeas : ∀ j, AEStronglyMeasurable (residual (fun μ => D.Acoef (w j) μ)
        (D.Bcoef (w j) (θ j)) (ψ j)) (volume.restrict (slabFund t₀ t₁)) := by
      intro j
      have hsub : slabFund t₀ t₁ ⊆ cylSlab T := fun x hx => hsl x hx.1
      have hc1 : ContinuousOn (fun x => D.B (bArg (w j) (θ j) x)) (cylSlab T) :=
        D.cont_B.comp_continuousOn ((ce j).prodMk ((cde j).prodMk ((cA j).prodMk
          ((cH j).prodMk continuousOn_const))))
      have hc2 : ∀ μ, ContinuousOn (fun x => D.A μ ((w j).z.e x)) (cylSlab T) := fun μ =>
        (D.smooth_A μ).continuous.comp_continuousOn (ce j)
      have hc3 : ∀ μ, ContinuousOn (pd (ψ j) μ) (cylSlab T) := fun μ =>
        continuousOn_pd_slab (hψ j) μ
      have hc4 : ContinuousOn (ψ j) (cylSlab T) := (hψ j).continuousOn
      have hcont : ContinuousOn (residual (fun μ => D.Acoef (w j) μ) (D.Bcoef (w j) (θ j)) (ψ j))
          (cylSlab T) := by
        refine continuousOn_pi.mpr fun i => ?_
        have e : ∀ y, residual (fun μ => D.Acoef (w j) μ) (D.Bcoef (w j) (θ j)) (ψ j) y i =
            ∑ μ, ∑ k, D.A μ ((w j).z.e y) i k * pd (ψ j) μ y k +
              ∑ k, D.B (bArg (w j) (θ j) y) i k * ψ j y k := fun y => by
          simp [residual, mvec, Finset.sum_apply, DiracModel.Acoef, DiracModel.Bcoef]
        refine ContinuousOn.congr ?_ fun y _ => e y
        refine (continuousOn_finsetSum _ fun μ _ => ?_).add ?_
        · refine continuousOn_finsetSum _ fun k _ => ?_
          have := hc2 μ; have := hc3 μ
          fun_prop
        · refine continuousOn_finsetSum _ fun k _ => ?_
          fun_prop
      exact (hcont.mono hsub).aestronglyMeasurable hFm
    calc eLpNorm (residual (fun μ => D.Acoef (w m) μ) (D.Bcoef (w m) (θ m)) (ψ m) -
          residual (fun μ => D.Acoef (w n) μ) (D.Bcoef (w n) (θ n)) (ψ n)) 2
          (volume.restrict (slabFund t₀ t₁)) ≤
        eLpNorm (residual (fun μ => D.Acoef (w m) μ) (D.Bcoef (w m) (θ m)) (ψ m)) 2
          (volume.restrict (slabFund t₀ t₁)) +
        eLpNorm (residual (fun μ => D.Acoef (w n) μ) (D.Bcoef (w n) (θ n)) (ψ n)) 2
          (volume.restrict (slabFund t₀ t₁)) := eLpNorm_sub_le (hmeas m) (hmeas n) (by norm_num)
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add (hN₀ m hm) (hN₀ n hn)
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end RegularBranch
end EinsteinSM
end RenewalGeometry
