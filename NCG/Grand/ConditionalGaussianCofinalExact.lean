/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GaussianKernelVitaliExact
import NCG.Grand.SummableCorrections
import NCG.Grand.ExteriorSecondQuantizationNormBoundsExact
import NCG.Grand.ExteriorReflectionPositivityCriterionExact
import NCG.Grand.DataProcessingExact

/-!
# Cofinal conditional-Gaussian kernels

This file supplies the convergence compiler used by `thm:SMQG-cofinal`.
Summable adjacent defects are converted into an actual pointwise limit on the
transported reference cylinder.  A continuous finite-dimensional assembly map
then converges in measure; the target-relative uniform-integrability row upgrades
this to `L¹` and total-variation convergence.  Positivity and fixed physical word
relations pass to the limit rather than being assumed there.

The last section instantiates the compiler with one dressed exterior grade
`q Wᴴ (⋀^r P) W` and proves directly both the manuscript's polynomial majorant
and positivity from `q ≥ 0` and `P ⪰ 0`.
-/

open Filter Set Topology Matrix
open scoped ENNReal MeasureTheory ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace NCG
namespace ConditionalGaussianCofinal

open MeasureTheory
open GaussianKernelVitali
open FiniteCompoundMatrixExteriorPower
open ExteriorSecondQuantizationNormBounds
open ExteriorPowerOperatorNormBounds

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [CompleteSpace E]
  {μ : Measure Ω}

/-- The canonical limit selected by the summable-adjacent-defect theorem. -/
noncomputable def summableLimit
    (x : ℕ → Ω → E) (δ : ℕ → ℝ) (hδ : Summable δ)
    (hstep : ∀ n ω, ‖x (n + 1) ω - x n ω‖ ≤ δ n) : Ω → E :=
  fun ω => Classical.choose
    (summable_defect_limit (fun n => x n ω) δ hδ (fun n => hstep n ω))

/-- Summable compatibility produces genuine pointwise convergence, with no
limit-convergence premise hidden in the interface. -/
theorem tendsto_summableLimit
    (x : ℕ → Ω → E) (δ : ℕ → ℝ) (hδ : Summable δ)
    (hstep : ∀ n ω, ‖x (n + 1) ω - x n ω‖ ≤ δ n) (ω : Ω) :
    Tendsto (fun n => x n ω) atTop
      (𝓝 (summableLimit x δ hδ hstep ω)) :=
  (Classical.choose_spec
    (summable_defect_limit (fun n => x n ω) δ hδ (fun n => hstep n ω))).1

/-- The canonical pointwise limit retains the quantitative defect-tail bound. -/
theorem summableLimit_sub_norm_le_tail
    (x : ℕ → Ω → E) (δ : ℕ → ℝ) (hδ : Summable δ)
    (hstep : ∀ n ω, ‖x (n + 1) ω - x n ω‖ ≤ δ n)
    (m : ℕ) (ω : Ω) :
    ‖summableLimit x δ hδ hstep ω - x m ω‖ ≤
      ∑' n : ℕ, δ (n + m) :=
  (Classical.choose_spec
    (summable_defect_limit (fun n => x n ω) δ hδ (fun n => hstep n ω))).2 m

/-- A fixed continuous relation is closed under the canonical cofinal limit. -/
theorem relation_closed_under_summable_limit
    {F G : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ F] [NormedSpace ℂ G]
    (x : ℕ → Ω → E) (δ : ℕ → ℝ) (hδ : Summable δ)
    (hstep : ∀ n ω, ‖x (n + 1) ω - x n ω‖ ≤ δ n)
    (assemble : E → F) (hassemble : Continuous assemble)
    (R : F →L[ℂ] G)
    (hR : ∀ n ω, R (assemble (x n ω)) = 0) (ω : Ω) :
    R (assemble (summableLimit x δ hδ hstep ω)) = 0 := by
  have hlim : Tendsto (fun n => R (assemble (x n ω))) atTop
      (𝓝 (R (assemble (summableLimit x δ hδ hstep ω)))) :=
    R.continuous.continuousAt.tendsto.comp
      (hassemble.continuousAt.tendsto.comp
        (tendsto_summableLimit x δ hδ hstep ω))
  have hzero : Tendsto (fun _ : ℕ => (0 : G)) atTop (𝓝 0) :=
    tendsto_const_nhds
  have heq : (fun n => R (assemble (x n ω))) = fun _ : ℕ => (0 : G) := by
    funext n
    exact hR n ω
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim hzero

/-- If the physical relation maps themselves converge, relations holding at
every cutoff descend through the limiting relation as well. -/
theorem varying_relation_closed_under_summable_limit
    {F G : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ F] [NormedSpace ℂ G]
    (x : ℕ → Ω → E) (δ : ℕ → ℝ) (hδ : Summable δ)
    (hstep : ∀ n ω, ‖x (n + 1) ω - x n ω‖ ≤ δ n)
    (assemble : E → F) (hassemble : Continuous assemble)
    (R : ℕ → F →L[ℂ] G) (Rlim : F →L[ℂ] G)
    (hRtendsto : Tendsto R atTop (𝓝 Rlim))
    (hR : ∀ n ω, R n (assemble (x n ω)) = 0) (ω : Ω) :
    Rlim (assemble (summableLimit x δ hδ hstep ω)) = 0 := by
  have hxlim : Tendsto (fun n => assemble (x n ω)) atTop
      (𝓝 (assemble (summableLimit x δ hδ hstep ω))) :=
    hassemble.continuousAt.tendsto.comp
      (tendsto_summableLimit x δ hδ hstep ω)
  have hlim : Tendsto (fun n => R n (assemble (x n ω))) atTop
      (𝓝 (Rlim (assemble (summableLimit x δ hδ hstep ω)))) :=
    (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (hRtendsto.prodMk_nhds hxlim)
  have hzero : Tendsto (fun _ : ℕ => (0 : G)) atTop (𝓝 0) :=
    tendsto_const_nhds
  have heq : (fun n => R n (assemble (x n ω))) = fun _ : ℕ => (0 : G) := by
    funext n
    exact hR n ω
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim hzero

/-- A vanishing held-out Gaussian occurrence residual identifies the direct
higher-word limit with the exterior prediction.  Thus C5 is a genuine closed
falsification test, not an equality assumed at the limit. -/
theorem heldOut_occurrence_limit
    {F : Type*} [NormedAddCommGroup F]
    (direct predicted : ℕ → F) (directLimit predictedLimit : F)
    (hdirect : Tendsto direct atTop (𝓝 directLimit))
    (hpredicted : Tendsto predicted atTop (𝓝 predictedLimit))
    (hresidual : Tendsto (fun n => direct n - predicted n) atTop (𝓝 0)) :
    directLimit = predictedLimit := by
  have hsub : Tendsto (fun n => direct n - predicted n) atTop
      (𝓝 (directLimit - predictedLimit)) := hdirect.sub hpredicted
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub hresidual)

/-- Positive-semidefinite matrices are closed also for the Euclidean operator
norm topology used by the exterior-power estimates. -/
theorem isClosed_l2_posSemidef {n : Type*} [Finite n] :
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

/-- Positivity survives convergence in measure for operator-norm matrix
kernels. -/
theorem ae_posSemidef_limit_l2
    {n : Type*} [Fintype n] [DecidableEq n]
    {K : ℕ → Ω → Matrix n n ℂ} {L : Ω → Matrix n n ℂ}
    (hpos : ∀ k, ∀ᵐ ω ∂μ, (K k ω).PosSemidef)
    (hconv : TendstoInMeasure μ K atTop L) :
    ∀ᵐ ω ∂μ, (L ω).PosSemidef := by
  obtain ⟨ns, -, hsub⟩ := hconv.exists_seq_tendsto_ae
  have hposSub : ∀ᵐ ω ∂μ, ∀ k, (K (ns k) ω).PosSemidef :=
    ae_all_iff.2 fun k => hpos (ns k)
  filter_upwards [hsub, hposSub] with ω hlim hω
  exact isClosed_l2_posSemidef.mem_of_tendsto hlim (Eventually.of_forall hω)

/-- Operator-norm form of the positive matrix-kernel Vitali theorem. -/
theorem positive_matrix_kernel_Vitali_l2
    [IsFiniteMeasure μ]
    {n : Type*} [Fintype n] [DecidableEq n]
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
    ae_posSemidef_limit_l2 hpos hconv⟩

set_option maxHeartbeats 800000 in
/-- **Cofinal positive-kernel compiler.**  Summable transported data, continuous
finite assembly, and the manuscript's UI domination row imply `L¹` and total
variation convergence.  Positivity and every fixed continuous word relation
survive in the limit.  The larger heartbeat budget is needed to elaborate the
dependent matrix-valued measure statement. -/
theorem cofinal_positive_kernel
    [IsFiniteMeasure μ]
    {f g : Type*} [Fintype f] [DecidableEq f]
    [Fintype g] [DecidableEq g]
    (x : ℕ → Ω → E) (δ : ℕ → ℝ) (hδ : Summable δ)
    (hstep : ∀ n ω, ‖x (n + 1) ω - x n ω‖ ≤ δ n)
    (hxmeas : ∀ n, AEStronglyMeasurable (x n) μ)
    (assemble : E → Matrix f f ℂ) (hassemble : Continuous assemble)
    (majorant : ℕ → Ω → ℝ)
    (hmajorant : UniformIntegrable majorant 1 μ)
    (hdom : ∀ n, ∀ᵐ ω ∂μ,
      ‖assemble (x n ω)‖ ≤ ‖majorant n ω‖)
    (hpos : ∀ n, ∀ᵐ ω ∂μ, (assemble (x n ω)).PosSemidef)
    (R : Matrix f f ℂ →L[ℂ] Matrix g g ℂ)
    (hR : ∀ n ω, R (assemble (x n ω)) = 0) :
    let L := fun ω => assemble (summableLimit x δ hδ hstep ω)
    Tendsto (fun n => ∫ ω, ‖assemble (x n ω) - L ω‖ ∂μ)
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        ((μ.withDensityᵥ (assemble ∘ x n) - μ.withDensityᵥ L).variation
          Set.univ).toReal) atTop (𝓝 0) ∧
      (∀ᵐ ω ∂μ, (L ω).PosSemidef) ∧
      ∀ ω, R (L ω) = 0 := by
  dsimp only
  let L := fun ω => assemble (summableLimit x δ hδ hstep ω)
  have hKmeas : ∀ n, AEStronglyMeasurable (assemble ∘ x n) μ := fun n =>
    hassemble.comp_aestronglyMeasurable (hxmeas n)
  have hpoint : ∀ᵐ ω ∂μ,
      Tendsto (fun n => (assemble ∘ x n) ω) atTop (𝓝 (L ω)) :=
    Filter.Eventually.of_forall fun ω =>
      hassemble.continuousAt.tendsto.comp
        (tendsto_summableLimit x δ hδ hstep ω)
  have hconv : TendstoInMeasure μ (fun n => assemble ∘ x n) atTop L :=
    tendstoInMeasure_of_tendsto_ae hKmeas hpoint
  obtain ⟨hL1, hTV, hLpos⟩ :=
    positive_matrix_kernel_Vitali_l2 hKmeas hmajorant hdom hconv hpos
  refine ⟨?_, hTV, hLpos, fun ω => ?_⟩
  · simpa only [Function.comp_apply] using hL1
  · exact relation_closed_under_summable_limit x δ hδ hstep assemble
      hassemble R hR ω

/-! ## The exterior-Gaussian assembly map -/

variable {d : ℕ} {f : Type*} [Fintype f] [DecidableEq f]

/-- One transported conditional-Gaussian grade consists of its scalar line
weight, one-particle covariance, and one-sided word synthesis. -/
abbrev GradePacket (d : ℕ) (r : Fin (d + 1)) (f : Type*) :=
  ℝ × (Matrix (Fin d) (Fin d) ℂ × Matrix (GradeIdx r.1 d) f ℂ)

/-- The exact dressed grade kernel `q Wᴴ (⋀^r P) W`. -/
noncomputable def gradeKernelAssembly (r : Fin (d + 1)) :
    GradePacket d r f → Matrix f f ℂ := fun z =>
  ((z.1 : ℂ) • (z.2.2ᴴ * cmpd r.1 z.2.1 * z.2.2))

/-- Every fixed compound-matrix construction is continuous. -/
@[continuity, fun_prop] theorem continuous_cmpd (r : ℕ) :
    Continuous (cmpd r : Matrix (Fin d) (Fin d) ℂ →
      Matrix (GradeIdx r d) (GradeIdx r d) ℂ) := by
  apply continuous_matrix
  intro S T
  exact (continuous_id.matrix_submatrix (sel S) (sel T)).matrix_det

/-- The dressed exterior-grade assembly is continuous in all transported
finite-dimensional data. -/
@[continuity, fun_prop] theorem continuous_gradeKernelAssembly (r : Fin (d + 1)) :
    Continuous (gradeKernelAssembly (d := d) (f := f) r) := by
  unfold gradeKernelAssembly
  fun_prop

/-- The exact scalar majorant appearing in the Gaussian-kernel UI row. -/
def gradeMajorant (r : Fin (d + 1)) (z : GradePacket d r f) : ℝ :=
  |z.1| * ‖z.2.2‖ ^ 2 * (1 + ‖z.2.1‖) ^ d

/-- The manuscript's polynomial envelope dominates the dressed grade kernel. -/
theorem norm_gradeKernelAssembly_le_majorant (r : Fin (d + 1))
    (z : GradePacket d r f) :
    ‖gradeKernelAssembly (d := d) (f := f) r z‖ ≤ gradeMajorant r z := by
  rcases z with ⟨q, P, W⟩
  have hcmpd : ‖cmpd r.1 P‖ ≤ (1 + ‖P‖) ^ d :=
    (cmpd_norm_le_pow P r.1).trans
      ((pow_le_max_one_pow_top ‖P‖ (norm_nonneg P)
        (Nat.le_of_lt_succ r.2)).trans (max_one_pow_le_one_add_pow P))
  have hmul : ‖Wᴴ * cmpd r.1 P * W‖ ≤
      ‖W‖ ^ 2 * (1 + ‖P‖) ^ d := by
    calc
      ‖Wᴴ * cmpd r.1 P * W‖
          ≤ ‖Wᴴ * cmpd r.1 P‖ * ‖W‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Wᴴ‖ * ‖cmpd r.1 P‖) * ‖W‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg W)
      _ ≤ (‖W‖ * (1 + ‖P‖) ^ d) * ‖W‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
      _ = ‖W‖ ^ 2 * (1 + ‖P‖) ^ d := by ring
  rw [gradeKernelAssembly, gradeMajorant, norm_smul]
  simpa [Real.norm_eq_abs, mul_assoc] using
    (mul_le_mul_of_nonneg_left hmul (abs_nonneg q))

/-- Nonnegative line weight and positive one-particle covariance imply
positivity of the dressed exterior grade. -/
theorem gradeKernelAssembly_posSemidef (r : Fin (d + 1))
    (z : GradePacket d r f) (hq : 0 ≤ z.1) (hP : z.2.1.PosSemidef) :
    (gradeKernelAssembly (d := d) (f := f) r z).PosSemidef := by
  exact QRE.posSemidef_smul_real hq
    ((cmpd_posSemidef hP).conjTranspose_mul_mul_same z.2.2)

/-! ## Complete finite represented-word bank -/

/-- One common scalar/covariance packet together with a word synthesis for
every represented exterior grade. -/
abbrev CompletePacket (d : ℕ) (f : Type*) :=
  ℝ × (Matrix (Fin d) (Fin d) ℂ ×
    (∀ r : Fin (d + 1), Matrix (GradeIdx r.1 d) f ℂ))

/-- The complete selected mixed-word kernel is the finite sum of its dressed
homogeneous exterior grades. -/
noncomputable def completeKernelAssembly :
    CompletePacket d f → Matrix f f ℂ := fun z =>
  ∑ r : Fin (d + 1),
    gradeKernelAssembly r (z.1, z.2.1, z.2.2 r)

/-- The full finite-word assembly is continuous. -/
@[continuity, fun_prop] theorem continuous_completeKernelAssembly :
    Continuous (completeKernelAssembly (d := d) (f := f)) := by
  unfold completeKernelAssembly
  apply continuous_finsetSum
  intro r _
  exact (continuous_gradeKernelAssembly r).comp (by fun_prop)

/-- QG.82 for the complete represented bank.  The word-map norm is written as
the finite sum of squared homogeneous synthesis norms. -/
def completeMajorant (z : CompletePacket d f) : ℝ :=
  |z.1| * (∑ r : Fin (d + 1), ‖z.2.2 r‖ ^ 2) *
    (1 + ‖z.2.1‖) ^ d

/-- The complete selected kernel is dominated by the exact finite-grade UI
envelope. -/
theorem norm_completeKernelAssembly_le_majorant (z : CompletePacket d f) :
    ‖completeKernelAssembly (d := d) (f := f) z‖ ≤ completeMajorant z := by
  rcases z with ⟨q, P, W⟩
  unfold completeKernelAssembly completeMajorant
  calc
    ‖∑ r : Fin (d + 1), gradeKernelAssembly r (q, P, W r)‖
        ≤ ∑ r : Fin (d + 1), ‖gradeKernelAssembly r (q, P, W r)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r : Fin (d + 1),
        |q| * ‖W r‖ ^ 2 * (1 + ‖P‖) ^ d := by
      exact Finset.sum_le_sum fun r _ =>
        norm_gradeKernelAssembly_le_majorant r (q, P, W r)
    _ = |q| * (∑ r : Fin (d + 1), ‖W r‖ ^ 2) *
        (1 + ‖P‖) ^ d := by
      rw [Finset.mul_sum, Finset.sum_mul]

/-- Positivity of the scalar line and one-particle covariance makes the whole
represented word bank positive. -/
theorem completeKernelAssembly_posSemidef (z : CompletePacket d f)
    (hq : 0 ≤ z.1) (hP : z.2.1.PosSemidef) :
    (completeKernelAssembly (d := d) (f := f) z).PosSemidef := by
  apply Petz.sum_posSemidef
  intro r
  exact gradeKernelAssembly_posSemidef r (z.1, z.2.1, z.2.2 r) hq hP

/-- **Complete-kernel clause of `thm:SMQG-cofinal`.**  Summable compatibility
of the transported line/covariance/all-grade word packet plus the literal
QG.82 uniform-integrability condition gives total-variation convergence of
the complete selected mixed-word kernel, positivity of its limit, and exact
descent through every fixed limiting word relation. -/
theorem cofinal_complete_conditional_gaussian_kernel
    [IsFiniteMeasure μ]
    {g : Type*} [Fintype g] [DecidableEq g]
    (x : ℕ → Ω → CompletePacket d f) (δ : ℕ → ℝ) (hδ : Summable δ)
    (hstep : ∀ n ω, ‖x (n + 1) ω - x n ω‖ ≤ δ n)
    (hxmeas : ∀ n, AEStronglyMeasurable (x n) μ)
    (hUI : UniformIntegrable (fun n ω => completeMajorant (x n ω)) 1 μ)
    (hq : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ (x n ω).1)
    (hP : ∀ n, ∀ᵐ ω ∂μ, ((x n ω).2.1).PosSemidef)
    (R : Matrix f f ℂ →L[ℂ] Matrix g g ℂ)
    (hR : ∀ n ω, R (completeKernelAssembly (x n ω)) = 0) :
    let L := fun ω =>
      completeKernelAssembly (summableLimit x δ hδ hstep ω)
    Tendsto (fun n => ∫ ω,
        ‖completeKernelAssembly (x n ω) - L ω‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        ((μ.withDensityᵥ (completeKernelAssembly ∘ x n) -
          μ.withDensityᵥ L).variation Set.univ).toReal) atTop (𝓝 0) ∧
      (∀ᵐ ω ∂μ, (L ω).PosSemidef) ∧
      ∀ ω, R (L ω) = 0 := by
  apply cofinal_positive_kernel x δ hδ hstep hxmeas
    completeKernelAssembly continuous_completeKernelAssembly
    (fun n ω => completeMajorant (x n ω)) hUI
  · intro n
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact norm_completeKernelAssembly_le_majorant (x n ω)
      · unfold completeMajorant
        positivity
  · intro n
    filter_upwards [hq n, hP n] with ω hqω hPω
    exact completeKernelAssembly_posSemidef (x n ω) hqω hPω
  · exact hR

/-- **Fixed-grade clause of `thm:SMQG-cofinal`.**  The one-particle/line/word
packet is transported with summable adjacent defects.  The exact QG.82
majorant supplies UI.  Consequently the dressed grade converges in `L¹` and
total variation, stays positive, and descends through every fixed represented
word relation. -/
theorem cofinal_conditional_gaussian_grade
    [IsFiniteMeasure μ]
    {g : Type*} [Fintype g] [DecidableEq g]
    (r : Fin (d + 1))
    (x : ℕ → Ω → GradePacket d r f) (δ : ℕ → ℝ) (hδ : Summable δ)
    (hstep : ∀ n ω, ‖x (n + 1) ω - x n ω‖ ≤ δ n)
    (hxmeas : ∀ n, AEStronglyMeasurable (x n) μ)
    (hUI : UniformIntegrable (fun n ω => gradeMajorant r (x n ω)) 1 μ)
    (hq : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ (x n ω).1)
    (hP : ∀ n, ∀ᵐ ω ∂μ, ((x n ω).2.1).PosSemidef)
    (R : Matrix f f ℂ →L[ℂ] Matrix g g ℂ)
    (hR : ∀ n ω, R (gradeKernelAssembly r (x n ω)) = 0) :
    let L := fun ω => gradeKernelAssembly r (summableLimit x δ hδ hstep ω)
    Tendsto (fun n => ∫ ω, ‖gradeKernelAssembly r (x n ω) - L ω‖ ∂μ)
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        ((μ.withDensityᵥ (gradeKernelAssembly r ∘ x n) -
          μ.withDensityᵥ L).variation Set.univ).toReal) atTop (𝓝 0) ∧
      (∀ᵐ ω ∂μ, (L ω).PosSemidef) ∧
      ∀ ω, R (L ω) = 0 := by
  apply cofinal_positive_kernel x δ hδ hstep hxmeas
    (gradeKernelAssembly r) (continuous_gradeKernelAssembly r)
    (fun n ω => gradeMajorant r (x n ω)) hUI
  · intro n
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact norm_gradeKernelAssembly_le_majorant r (x n ω)
      · unfold gradeMajorant
        positivity
  · intro n
    filter_upwards [hq n, hP n] with ω hqω hPω
    exact gradeKernelAssembly_posSemidef r (x n ω) hqω hPω
  · exact hR

end ConditionalGaussianCofinal
end NCG
