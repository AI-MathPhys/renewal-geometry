/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed

/-!
# Vector-valued Vitali transport for Gaussian kernels

The reusable analytic core of `thm:SMQG-kernel-Vitali`.  A uniformly
integrable scalar majorant transfers uniform integrability to a Banach-valued
kernel family.  On a finite reference cylinder, convergence in measure then
upgrades to convergence of the integral of the norm by Mathlib's
vector-valued Vitali theorem.
-/

open Filter Set Topology
open scoped ENNReal MeasureTheory

namespace NCG
namespace GaussianKernelVitali

open MeasureTheory

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E]
  {μ : Measure Ω}

/-- Scalar domination transfers probability-theory uniform integrability to
a Banach-valued family. -/
theorem uniformIntegrable_of_norm_le
    {F : ℕ → Ω → E} {g : ℕ → Ω → ℝ}
    (hFmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hg : UniformIntegrable g 1 μ)
    (hdom : ∀ n, ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ ‖g n ω‖) :
    UniformIntegrable F 1 μ := by
  refine ⟨hFmeas, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hgδ⟩ := hg.unifIntegrable hε
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    apply (eLpNorm_mono_ae ?_).trans (hgδ n s hs hμs)
    filter_upwards [hdom n] with ω hω
    by_cases hωs : ω ∈ s
    · simpa [Set.indicator, hωs, Real.norm_eq_abs] using hω
    · simp [Set.indicator, hωs]
  · obtain ⟨C, hC⟩ := hg.2.2
    exact ⟨C, fun n => (eLpNorm_mono_ae (hdom n)).trans (hC n)⟩

/-- **Vector-valued finite-cylinder Vitali theorem (QG.83 core).**
Uniform integrability and convergence in measure imply convergence of the
integral norm, exactly in the real-valued form used by the manuscript. -/
theorem integral_norm_sub_tendsto_zero
    [IsFiniteMeasure μ]
    {F : ℕ → Ω → E} {G : Ω → E}
    (hUI : UniformIntegrable F 1 μ)
    (hconv : TendstoInMeasure μ F atTop G) :
    Tendsto (fun n => ∫ ω, ‖F n ω - G ω‖ ∂μ) atTop (𝓝 0) := by
  have hG : MemLp G 1 μ :=
    hUI.memLp_of_tendstoInMeasure hconv
  have hLp : Tendsto (fun n => eLpNorm (F n - G) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl (by simp)
      (fun n => (hUI.memLp n).aestronglyMeasurable)
      hG hUI.unifIntegrable hconv
  have hreal : Tendsto (fun n => (eLpNorm (F n - G) 1 μ).toReal)
      atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hLp
  have hdiff : ∀ n, AEStronglyMeasurable (F n - G) μ := fun n =>
    (hUI.memLp n).aestronglyMeasurable.sub hG.aestronglyMeasurable
  have heq : (fun n => ∫ ω, ‖F n ω - G ω‖ ∂μ) =
      fun n => (eLpNorm (F n - G) 1 μ).toReal := by
    funext n
    rw [MeasureTheory.toReal_eLpNorm (hdiff n),
      MeasureTheory.lpNorm_one_eq_integral_norm (hdiff n)]
    rfl
  rw [heq]
  exact hreal

/-- QG.83 with the manuscript's scalar majorant hypothesis exposed directly. -/
theorem dominated_kernel_Vitali
    [IsFiniteMeasure μ]
    {F : ℕ → Ω → E} {G : Ω → E} {majorant : ℕ → Ω → ℝ}
    (hFmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hmajorant : UniformIntegrable majorant 1 μ)
    (hdom : ∀ n, ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ ‖majorant n ω‖)
    (hconv : TendstoInMeasure μ F atTop G) :
    Tendsto (fun n => ∫ ω, ‖F n ω - G ω‖ ∂μ) atTop (𝓝 0) :=
  integral_norm_sub_tendsto_zero
    (uniformIntegrable_of_norm_le hFmeas hmajorant hdom) hconv

/-- The matrix/vector-valued measures with densities `F n` converge to the
measure with density `G` in total variation.  The displayed quantity is the
total variation of their difference on the whole reference cylinder. -/
theorem totalVariation_withDensity_tendsto_zero
    [IsFiniteMeasure μ] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℕ → Ω → E} {G : Ω → E}
    (hUI : UniformIntegrable F 1 μ)
    (hconv : TendstoInMeasure μ F atTop G) :
    Tendsto (fun n =>
      ((μ.withDensityᵥ (F n) - μ.withDensityᵥ G).variation Set.univ).toReal)
      atTop (𝓝 0) := by
  have hG : Integrable G μ :=
    (hUI.integrable_of_tendstoInMeasure hconv)
  have hFn : ∀ n, Integrable (F n) μ := fun n =>
    memLp_one_iff_integrable.mp (hUI.memLp n)
  have hL1 := integral_norm_sub_tendsto_zero hUI hconv
  have heq : (fun n =>
      ((μ.withDensityᵥ (F n) - μ.withDensityᵥ G).variation Set.univ).toReal) =
      (fun n => ∫ ω, ‖F n ω - G ω‖ ∂μ) := by
    funext n
    rw [← MeasureTheory.withDensityᵥ_sub (hFn n) hG]
    rw [MeasureTheory.Measure.variation_withDensityᵥ ((hFn n).sub hG)]
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm ((hFn n).sub hG)]
    rw [ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
    simp only [Pi.sub_apply]
  rw [heq]
  exact hL1

/-- Failure of uniform absolute continuity can be witnessed beyond every
finite initial segment.  This is the key step that makes the concentration
indices a genuine subsequence. -/
theorem bad_set_above_of_not_unifIntegrable
    {F : ℕ → Ω → E}
    (hLp : ∀ n, MemLp (F n) 1 μ)
    (hfail : ¬ UnifIntegrable F 1 μ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∀ δ : ℝ, 0 < δ →
      ∃ n : ℕ, N ≤ n ∧ ∃ A : Set Ω, MeasurableSet A ∧
        μ A ≤ ENNReal.ofReal δ ∧
        ENNReal.ofReal ε < eLpNorm (A.indicator (F n)) 1 μ := by
  rw [UnifIntegrable] at hfail
  classical
  obtain ⟨ε, hεbad⟩ := Classical.not_forall.mp hfail
  have hε : 0 < ε := by
    by_contra hε
    apply hεbad
    intro hε'
    exact False.elim (hε hε')
  have hbad : ∀ δ : ℝ, 0 < δ → ∃ n A, MeasurableSet A ∧
      μ A ≤ ENNReal.ofReal δ ∧
      ¬ eLpNorm (A.indicator (F n)) 1 μ ≤ ENNReal.ofReal ε := by
    intro δ hδ
    have hno : ¬ ∀ n A, MeasurableSet A → μ A ≤ ENNReal.ofReal δ →
        eLpNorm (A.indicator (F n)) 1 μ ≤ ENNReal.ofReal ε := by
      intro hall
      apply hεbad
      intro _
      exact ⟨δ, hδ, hall⟩
    obtain ⟨n, hn⟩ := Classical.not_forall.mp hno
    obtain ⟨A, hAall⟩ := Classical.not_forall.mp hn
    have hA : MeasurableSet A := by
      by_contra hA
      apply hAall
      intro hA'
      exact False.elim (hA hA')
    have hμA : μ A ≤ ENNReal.ofReal δ := by
      by_contra hμA
      apply hAall
      intro _ hμA'
      exact False.elim (hμA hμA')
    have hnorm : ¬ eLpNorm (A.indicator (F n)) 1 μ ≤ ENNReal.ofReal ε := by
      intro hnorm
      exact hAall (fun _ _ => hnorm)
    exact ⟨n, A, hA, hμA, hnorm⟩
  refine ⟨ε, hε, fun N δ hδ => ?_⟩
  have hfinite : UnifIntegrable (fun i : Fin N => F i) 1 μ :=
    unifIntegrable_fin le_rfl (by simp) fun i => hLp i
  obtain ⟨δ₀, hδ₀, hprefix⟩ := hfinite hε
  obtain ⟨n, A, hA, hμA, hnorm⟩ := hbad (min δ δ₀) (lt_min hδ hδ₀)
  have hμδ : μ A ≤ ENNReal.ofReal δ :=
    hμA.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hn : N ≤ n := by
    by_contra hn
    have hn' : n < N := Nat.lt_of_not_ge hn
    have hμδ₀ : μ A ≤ ENNReal.ofReal δ₀ :=
      hμA.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    exact hnorm (hprefix ⟨n, hn'⟩ A hA hμδ₀)
  exact ⟨n, hn, A, hA, hμδ, lt_of_not_ge hnorm⟩

/-- **Concentration alternative (QG.83 converse clause).**  If uniform
absolute continuity fails, a strictly increasing subsequence carries a fixed
amount of `L¹` mass on measurable sets whose measure tends to zero. -/
theorem concentration_subsequence_of_not_unifIntegrable
    {F : ℕ → Ω → E}
    (hLp : ∀ n, MemLp (F n) 1 μ)
    (hfail : ¬ UnifIntegrable F 1 μ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ A : ℕ → Set Ω,
        (∀ j, MeasurableSet (A j)) ∧
        Tendsto (fun j => μ (A j)) atTop (𝓝 0) ∧
        ∀ j, ε < ∫ ω in A j, ‖F (ns j) ω‖ ∂μ := by
  obtain ⟨ε, hε, hbad⟩ :=
    bad_set_above_of_not_unifIntegrable hLp hfail
  classical
  let Good (N j : ℕ) (p : ℕ × Set Ω) : Prop :=
    N ≤ p.1 ∧ MeasurableSet p.2 ∧
      μ p.2 ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) ∧
      ENNReal.ofReal ε < eLpNorm (p.2.indicator (F p.1)) 1 μ
  have hGood : ∀ N j, ∃ p : ℕ × Set Ω, Good N j p := by
    intro N j
    obtain ⟨n, hn, A, hA, hμA, hnorm⟩ :=
      hbad N (1 / ((j : ℝ) + 1)) (by positivity)
    exact ⟨(n, A), hn, hA, hμA, hnorm⟩
  let pick (N j : ℕ) : ℕ × Set Ω := Classical.choose (hGood N j)
  have hpick (N j : ℕ) : Good N j (pick N j) :=
    Classical.choose_spec (hGood N j)
  let pair : ℕ → ℕ × Set Ω := fun j =>
    Nat.rec (pick 0 0) (fun k previous => pick (previous.1 + 1) (k + 1)) j
  let ns : ℕ → ℕ := fun j => (pair j).1
  let A : ℕ → Set Ω := fun j => (pair j).2
  have hpair : ∀ j, MeasurableSet (A j) ∧
      μ (A j) ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) ∧
      ENNReal.ofReal ε < eLpNorm ((A j).indicator (F (ns j))) 1 μ := by
    intro j
    induction j with
    | zero =>
        simpa [pair, ns, A, Good] using (hpick 0 0)
    | succ j ih =>
        simpa [pair, ns, A, Good] using
          (hpick ((pair j).1 + 1) (j + 1)).2
  have hns : StrictMono ns := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hle := (hpick ((pair j).1 + 1) (j + 1)).1
    exact lt_of_lt_of_le (Nat.lt_succ_self (ns j)) (by
      simpa [pair, ns] using hle)
  have hmeasure : Tendsto (fun j => μ (A j)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hupper : Tendsto
        (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1)))
        atTop (𝓝 0) := by
      convert ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal using 1 <;>
        simp [Function.comp_def]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => bot_le) (fun j => (hpair j).2.1)
  refine ⟨ε, hε, ns, hns, A, (fun j => (hpair j).1), hmeasure, fun j => ?_⟩
  have hmem : MemLp ((A j).indicator (F (ns j))) 1 μ :=
    (hLp (ns j)).indicator (hpair j).1
  have htoReal : ε <
      (eLpNorm ((A j).indicator (F (ns j))) 1 μ).toReal := by
    rw [← ENNReal.toReal_ofReal hε.le]
    exact (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hmem.eLpNorm_ne_top).2
      (hpair j).2.2
  rw [MeasureTheory.toReal_eLpNorm hmem.aestronglyMeasurable,
    MeasureTheory.lpNorm_one_eq_integral_norm hmem.aestronglyMeasurable] at htoReal
  have hindicator :
      (fun x => ‖(A j).indicator (F (ns j)) x‖) =
        (A j).indicator (fun x => ‖F (ns j) x‖) := by
    funext x
    by_cases hx : x ∈ A j <;> simp [Set.indicator, hx]
  rw [hindicator, MeasureTheory.integral_indicator (hpair j).1] at htoReal
  exact htoReal

open scoped ComplexOrder Matrix in
/-- Positive-semidefinite complex matrices form a closed cone in finite
dimension.  This complex version is the closure fact needed for Gaussian
matrix kernels. -/
theorem isClosed_complex_posSemidef {n : Type*} [Finite n] :
    IsClosed {M : Matrix n n ℂ | M.PosSemidef} := by
  cases nonempty_fintype n
  have h : {M : Matrix n n ℂ | M.PosSemidef} =
      {M | Mᴴ = M} ∩ ⋂ v : n → ℂ, {M | 0 ≤ star v ⬝ᵥ (M *ᵥ v)} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun hM => ⟨hM.1, hM.dotProduct_mulVec_nonneg⟩,
      fun hM => Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM.1 hM.2⟩
  rw [h]
  refine (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter ?_
  exact isClosed_iInter fun v =>
    isClosed_Ici.preimage
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

open scoped ComplexOrder Matrix.Norms.Frobenius in
/-- A convergence-in-measure limit of almost-everywhere positive-semidefinite
finite complex matrix kernels is itself positive semidefinite almost
everywhere. -/
theorem ae_posSemidef_limit_of_tendstoInMeasure
    {n : Type*} [Fintype n]
    {K : ℕ → Ω → Matrix n n ℂ} {L : Ω → Matrix n n ℂ}
    (hpos : ∀ k, ∀ᵐ ω ∂μ, (K k ω).PosSemidef)
    (hconv : TendstoInMeasure μ K atTop L) :
    ∀ᵐ ω ∂μ, (L ω).PosSemidef := by
  obtain ⟨ns, -, hsub⟩ := hconv.exists_seq_tendsto_ae
  have hposSub : ∀ᵐ ω ∂μ, ∀ k, (K (ns k) ω).PosSemidef :=
    ae_all_iff.2 fun k => hpos (ns k)
  filter_upwards [hsub, hposSub] with ω hlim hω
  exact isClosed_complex_posSemidef.mem_of_tendsto hlim
    (Eventually.of_forall hω)

open scoped ComplexOrder Matrix.Norms.Frobenius in
/-- **Positive matrix-kernel Vitali theorem (QG.83).**  A uniformly
integrable scalar majorant and convergence in measure give `L¹` convergence,
total-variation convergence of the associated matrix-valued measures, and
positivity of the limiting kernel. -/
theorem positive_matrix_kernel_Vitali
    [IsFiniteMeasure μ]
    {n : Type*} [Fintype n]
    {K : ℕ → Ω → Matrix n n ℂ} {L : Ω → Matrix n n ℂ}
    {majorant : ℕ → Ω → ℝ}
    (hKmeas : ∀ k, AEStronglyMeasurable (K k) μ)
    (hmajorant : UniformIntegrable majorant 1 μ)
    (hdom : ∀ k, ∀ᵐ ω ∂μ, ‖K k ω‖ ≤ ‖majorant k ω‖)
    (hconv : TendstoInMeasure μ K atTop L)
    (hpos : ∀ k, ∀ᵐ ω ∂μ, (K k ω).PosSemidef) :
    Tendsto (fun k => ∫ ω, ‖K k ω - L ω‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun k =>
        ((μ.withDensityᵥ (K k) - μ.withDensityᵥ L).variation Set.univ).toReal)
        atTop (𝓝 0) ∧
      ∀ᵐ ω ∂μ, (L ω).PosSemidef := by
  have hUI : UniformIntegrable K 1 μ :=
    uniformIntegrable_of_norm_le hKmeas hmajorant hdom
  exact ⟨integral_norm_sub_tendsto_zero hUI hconv,
    totalVariation_withDensity_tendsto_zero hUI hconv,
    ae_posSemidef_limit_of_tendstoInMeasure hpos hconv⟩

end GaussianKernelVitali
end NCG
