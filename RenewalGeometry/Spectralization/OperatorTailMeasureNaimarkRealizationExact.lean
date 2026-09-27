/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.OperatorMeasureL2Completion
import RenewalGeometry.Spectralization.OperatorTailMeasureDynamicJetsExact
/-!
# The canonical minimal Stieltjes dilation and the operator-measure realization theorem

This file covers, for `papers/predictive_spectral_geometry`,

* `con:supp-Naimark-tail` (Canonical minimal Stieltjes dilation): for a positive operator-valued
  tail measure `μ` (`def:supp-POVM`) the Hilbert space `K_μ = L²(μ; H)` (`kSpace`, built in
  `Analysis/OperatorMeasureL2Completion` as the completion of the bounded measurable `H`-valued
  functions modulo the null space of `⟨f, g⟩_μ = ∫ ⟨f, dμ g⟩`), the projection-valued measure
  `P_μ(E) = ` multiplication by `1_E` (`spectralProj`), the embedding `V_μ ξ = [1 ξ]` (`embedV`)
  and `B_μ = V_μ^*` (`compressB`).  The operator `C_μ = ∫ λ dP_μ` is unbounded when the support is
  unbounded; Mathlib has no spectral theorem for unbounded self-adjoint operators, so `C_μ` is
  represented through its bounded functional calculus: the resolvents
  `(C_μ - z)⁻¹ = ` multiplication by `(λ - z)⁻¹` (`resolventOp`, `z ∉ [0, ∞)`) and the semigroup
  `e^{-tC_μ} = ` multiplication by `e^{-tλ}` (`heatOp`, `t ≥ 0`) — these multipliers are taken
  to vanish on `(-∞, 0]`, a `μ`-null set, so that they are bounded.
* `thm:supp-Naimark-realization`:
  - `eq:supp-Naimark-realization` `Σ_μ(z) = B_μ (C_μ - z)⁻¹ B_μ^*` (`stieltjesSelfEnergy_eq_compress`)
    together with the dilation form `K_μ(t) = B_μ e^{-tC_μ} B_μ^*` of `eq:supp-Euclidean-memory`
    (`euclideanMemoryKernel_eq_compress`) and `μ(E) = B_μ P_μ(E) B_μ^*` (`toVectorMeasure_eq_compress`);
  - `eq:supp-Naimark-minimal` `K_μ = closure span {P_μ(E) B_μ^* ξ}` (`minimal`);
  - the converse: for a spectral measure `P` on a Hilbert space `K` supported in `(0, ∞)`
    (`IsSpectralMeasure`, the spectral measure `E_C` of a nonnegative self-adjoint `C`) and
    `B = V^*`, `μ(E) = B P(E) B^*` is a positive tail measure (`ofSpectralMeasure`) whose
    self-energy is `B (C - z)⁻¹ B^*`, where `(C - z)⁻¹` is any operator `R` acting as the
    spectral integral of `(λ - z)⁻¹` against `P` on the source vectors
    (`stieltjesSelfEnergy_ofSpectralMeasure`).
  The uniqueness of the intertwining unitary between two minimal realizations
  (`eq:supp-Naimark-unitary`) is not formalised here.
-/

open MeasureTheory Filter Topology Set
open scoped ComplexOrder ENNReal Matrix InnerProductSpace

namespace RenewalGeometry
namespace OperatorTailMeasure

variable {H : Type*} [Fintype H] [DecidableEq H]

open OperatorMeasureL2

namespace PositiveTailMeasure

variable (μ : PositiveTailMeasure H)

instance : IsFiniteMeasure μ.toPosOperatorMeasure.toVectorMeasure.variation :=
  inferInstanceAs (IsFiniteMeasure μ.toVectorMeasure.variation)

/-! ## `con:supp-Naimark-tail`: the canonical objects -/

/-- **`K_μ = L²(μ; H)`**: the completion of the bounded measurable `H`-valued functions modulo the
null space of `⟨f, g⟩_μ` (`con:supp-Naimark-tail`). -/
abbrev kSpace : Type _ := L2 μ.toPosOperatorMeasure

/-- **The projection-valued measure `P_μ(E)`** (multiplication by `1_E`). -/
noncomputable def spectralProj (s : Set ℝ) (hs : MeasurableSet s) : kSpace μ →L[ℂ] kSpace μ :=
  L2.proj μ.toPosOperatorMeasure s hs

/-- **The embedding `V_μ ξ = [1_{(0,∞)} ξ]`** of `H` into `K_μ`. -/
noncomputable def embedV : EuclideanSpace ℂ H →L[ℂ] kSpace μ := L2.embed μ.toPosOperatorMeasure

/-- **`B_μ = V_μ^*`**. -/
noncomputable def compressB : kSpace μ →L[ℂ] EuclideanSpace ℂ H :=
  ContinuousLinearMap.adjoint (embedV μ)

theorem adjoint_compressB : ContinuousLinearMap.adjoint (compressB μ) = embedV μ :=
  ContinuousLinearMap.adjoint_adjoint _

/-- Distance from `z ∉ [0,∞)` to the half-line. -/
noncomputable def resolventGap (z : ℂ) : ℝ := if z.im = 0 then -z.re else |z.im|

theorem resolventGap_pos {z : ℂ} (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) : 0 < resolventGap z := by
  unfold resolventGap
  split_ifs with h
  · have : ¬ 0 ≤ z.re := fun h' => hz ⟨h, h'⟩
    linarith [not_le.mp this]
  · exact abs_pos.mpr h

theorem resolventGap_le_norm_sub {z : ℂ} (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) {lam : ℝ}
    (hlam : 0 ≤ lam) : resolventGap z ≤ ‖(lam : ℂ) - z‖ := by
  unfold resolventGap
  split_ifs with h
  · have hre : z.re < 0 := not_le.mp fun h' => hz ⟨h, h'⟩
    have e1 : |((lam : ℂ) - z).re| = lam - z.re := by
      rw [Complex.sub_re, Complex.ofReal_re, abs_of_nonneg (by linarith)]
    have e2 := Complex.abs_re_le_norm ((lam : ℂ) - z)
    rw [e1] at e2
    linarith
  · have e1 : |((lam : ℂ) - z).im| = |z.im| := by
      rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg]
    have e2 := Complex.abs_im_le_norm ((lam : ℂ) - z)
    rw [e1] at e2
    exact e2

/-- The bounded resolvent kernel `λ ↦ (λ - z)⁻¹` on `(0, ∞)` (and `0` on `(-∞, 0]`). -/
noncomputable def resolventScalar (z : ℂ) (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) : BddScalar ℝ where
  toFun lam := if 0 < lam then ((lam : ℂ) - z)⁻¹ else 0
  measurable := Measurable.ite measurableSet_Ioi
    (Complex.measurable_ofReal.sub measurable_const).inv measurable_const
  bound := (resolventGap z)⁻¹
  bound_nonneg := (inv_pos.mpr (resolventGap_pos hz)).le
  norm_le lam := by
    split_ifs with h
    · rw [norm_inv]
      exact inv_anti₀ (resolventGap_pos hz) (resolventGap_le_norm_sub hz h.le)
    · simp only [norm_zero]
      exact (inv_pos.mpr (resolventGap_pos hz)).le

/-- **The resolvent `(C_μ - z)⁻¹`** of the self-adjoint operator `C_μ = ∫ λ dP_μ`: multiplication
by `(λ - z)⁻¹`. -/
noncomputable def resolventOp (z : ℂ) (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) : kSpace μ →L[ℂ] kSpace μ :=
  L2.mul μ.toPosOperatorMeasure (resolventScalar z hz)

/-- The bounded heat kernel `λ ↦ e^{-tλ}` on `(0, ∞)`. -/
noncomputable def heatScalar (t : ℝ) (ht : 0 ≤ t) : BddScalar ℝ where
  toFun lam := if 0 < lam then ((Real.exp (-t * lam) : ℝ) : ℂ) else 0
  measurable := Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
  bound := 1
  bound_nonneg := zero_le_one
  norm_le lam := by
    split_ifs with h
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by nlinarith)
    · simp

/-- **The semigroup `e^{-tC_μ}`**: multiplication by `e^{-tλ}`. -/
noncomputable def heatOp (t : ℝ) (ht : 0 ≤ t) : kSpace μ →L[ℂ] kSpace μ :=
  L2.mul μ.toPosOperatorMeasure (heatScalar t ht)

/-! ## The compression identity for multipliers -/

/-- **Compression of a multiplier**: `⟨V ξ, g V η⟩ = ⟨ξ, (∫ g dμ) η⟩`. -/
theorem inner_embedV_mul_embedV (g : BddScalar ℝ) (ξ η : EuclideanSpace ℂ H) :
    ⟪embedV μ ξ, L2.mul μ.toPosOperatorMeasure g (embedV μ η)⟫_ℂ =
      ⟪ξ, Matrix.toEuclideanLin (Matrix.of (VectorMeasure.integral μ.toVectorMeasure g.toFun
        (ContinuousLinearMap.lsmul ℝ ℂ))) η⟫_ℂ := by
  have hg : Integrable g.toFun μ.toVectorMeasure.variation :=
    Integrable.mono' (integrable_const g.bound) g.measurable.aestronglyMeasurable
      (ae_of_all _ g.norm_le)
  unfold embedV
  rw [L2.embed_apply, L2.embed_apply, L2.mul_mk, L2.inner_mk_mk]
  -- the left-hand side is a pairing integral of `g • (ξ^* ⊗ η)`
  set A₀ : H → H → ℂ := fun i j => star (WithLp.ofLp ξ i) * WithLp.ofLp η j with hA₀
  have hL : μ.toPosOperatorMeasure.form (PreL2.ofFun μ.toPosOperatorMeasure (fun _ => WithLp.ofLp ξ)
        (const_mem_bddMeasurable _)).toFun
      (L2.mulPre μ.toPosOperatorMeasure g (PreL2.ofFun μ.toPosOperatorMeasure (fun _ => WithLp.ofLp η)
        (const_mem_bddMeasurable _))).toFun =
      VectorMeasure.integral μ.toVectorMeasure
        (fun x => ((ContinuousLinearMap.lsmul ℝ ℂ).flip A₀ : ℂ →L[ℝ] (H → H → ℂ)) (g.toFun x))
        pairCLM := by
    unfold PosOperatorMeasure.form
    congr 1
    funext x i j
    simp [innerIntegrand_apply, hA₀, mul_left_comm]
  rw [hL, VectorMeasure.integral_continuousLinearMap_comp hg]
  -- the right-hand side through the sesquilinear functional
  have hR : ⟪ξ, Matrix.toEuclideanLin (Matrix.of (VectorMeasure.integral μ.toVectorMeasure g.toFun
      (ContinuousLinearMap.lsmul ℝ ℂ))) η⟫_ℂ =
      sesqCLM (WithLp.ofLp ξ) (WithLp.ofLp η) (VectorMeasure.integral μ.toVectorMeasure g.toFun
        (ContinuousLinearMap.lsmul ℝ ℂ)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply, sesqCLM_apply,
      sesqForm, dotProduct_comm]
  rw [hR, VectorMeasure.continuousLinearMap_apply_integral hg]
  have hB : (pairCLM ∘L ((ContinuousLinearMap.lsmul ℝ ℂ).flip A₀ : ℂ →L[ℝ] (H → H → ℂ))) =
      (ContinuousLinearMap.compL ℝ (H → H → ℂ) (H → H → ℂ) ℂ (sesqCLM (WithLp.ofLp ξ) (WithLp.ofLp η))) ∘L
        ContinuousLinearMap.lsmul ℝ ℂ := by
    refine ContinuousLinearMap.ext fun c => ContinuousLinearMap.ext fun M => ?_
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lsmul_apply, pairCLM_apply, ContinuousLinearMap.compL_apply, sesqCLM_apply,
      sesqForm, hA₀, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hB]

/-- The compression `B (mul g) B^*` as an operator on `H`. -/
theorem compressB_mul_embedV (g : BddScalar ℝ) (η : EuclideanSpace ℂ H) :
    compressB μ (L2.mul μ.toPosOperatorMeasure g (embedV μ η)) =
      Matrix.toEuclideanLin (Matrix.of (VectorMeasure.integral μ.toVectorMeasure g.toFun
        (ContinuousLinearMap.lsmul ℝ ℂ))) η := by
  refine ext_inner_left ℂ fun ξ => ?_
  rw [compressB, ContinuousLinearMap.adjoint_inner_right]
  exact μ.inner_embedV_mul_embedV g ξ η

/-! ## `thm:supp-Naimark-realization` for the canonical realization -/

/-- **`eq:supp-Naimark-realization`**: `Σ_μ(z) = B_μ (C_μ - z)⁻¹ B_μ^*` for `z ∉ [0, ∞)`. -/
theorem stieltjesSelfEnergy_eq_compress {z : ℂ} (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re))
    (η : EuclideanSpace ℂ H) :
    Matrix.toEuclideanLin (μ.stieltjesSelfEnergy z) η =
      compressB μ (resolventOp μ z hz (embedV μ η)) := by
  rw [resolventOp, compressB_mul_embedV]
  unfold stieltjesSelfEnergy
  congr 3
  refine VectorMeasure.integral_congr_ae ?_
  filter_upwards [μ.ae_pos_variation] with lam hlam
  simp [resolventScalar, hlam]

/-- **`eq:supp-Euclidean-memory`, dilation form**: `K_μ(t) = B_μ e^{-tC_μ} B_μ^*` for `t ≥ 0`. -/
theorem euclideanMemoryKernel_eq_compress {t : ℝ} (ht : 0 ≤ t) (η : EuclideanSpace ℂ H) :
    Matrix.toEuclideanLin (μ.euclideanMemoryKernel t) η =
      compressB μ (heatOp μ t ht (embedV μ η)) := by
  rw [heatOp, compressB_mul_embedV]
  unfold euclideanMemoryKernel
  congr 3
  refine VectorMeasure.integral_congr_ae ?_
  filter_upwards [μ.ae_pos_variation] with lam hlam
  simp [heatScalar, hlam]

/-- `μ(E) = B_μ P_μ(E) B_μ^*`. -/
theorem toVectorMeasure_eq_compress (s : Set ℝ) (hs : MeasurableSet s) (η : EuclideanSpace ℂ H) :
    Matrix.toEuclideanLin (Matrix.of (μ.toVectorMeasure s)) η =
      compressB μ (spectralProj μ s hs (embedV μ η)) := by
  refine ext_inner_left ℂ fun ξ => ?_
  rw [compressB, ContinuousLinearMap.adjoint_inner_right]
  exact (L2.inner_embed_proj_embed μ.toPosOperatorMeasure s hs ξ η).symm

/-- `P_μ` is supported in `(0, ∞)`: `P_μ((-∞, 0]) = 0`, i.e. `C_μ ≥ 0`. -/
theorem spectralProj_Iic : spectralProj μ (Iic 0) measurableSet_Iic = 0 :=
  L2.proj_eq_zero_of_forall_subset _ measurableSet_Iic fun t ht hts =>
    μ.eq_zero_of_subset_Iic t ht hts

/-- **`eq:supp-Naimark-minimal`**: `K_μ` is the closed span of the source vectors
`P_μ(E) B_μ^* ξ`. -/
theorem minimal :
    (Submodule.span ℂ {y : kSpace μ | ∃ (s : Set ℝ) (hs : MeasurableSet s) (ξ : EuclideanSpace ℂ H),
      y = spectralProj μ s hs (ContinuousLinearMap.adjoint (compressB μ) ξ)}).topologicalClosure =
      ⊤ := by
  rw [adjoint_compressB]
  exact L2.topologicalClosure_sourceSpan μ.toPosOperatorMeasure

end PositiveTailMeasure

/-! ## Abstract spectral measures and the converse -/

/-- A **spectral measure supported in `(0, ∞)`** on a Hilbert space `K`: a projection-valued,
multiplicative, normalised, strongly σ-additive set function vanishing on `(-∞, 0]` — the spectral
measure `E_C` of a nonnegative self-adjoint operator `C`. -/
structure IsSpectralMeasure {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (P : ∀ s : Set ℝ, MeasurableSet s → K →L[ℂ] K) : Prop where
  isSelfAdjoint : ∀ s hs, IsSelfAdjoint (P s hs)
  inter : ∀ s t (hs : MeasurableSet s) (ht : MeasurableSet t), P (s ∩ t) (hs.inter ht) = P s hs ∘L P t ht
  univ : P univ MeasurableSet.univ = ContinuousLinearMap.id ℂ K
  hasSum : ∀ (E : ℕ → Set ℝ) (hE : ∀ n, MeasurableSet (E n)),
    (Pairwise fun m n => Disjoint (E m) (E n)) → ∀ x,
      HasSum (fun n => P (E n) (hE n) x) (P (⋃ n, E n) (MeasurableSet.iUnion hE) x)
  Iic_eq_zero : P (Set.Iic 0) measurableSet_Iic = 0

/-- The canonical `P_μ` is a spectral measure supported in `(0,∞)`. -/
theorem PositiveTailMeasure.isSpectralMeasure_spectralProj (μ : PositiveTailMeasure H) :
    IsSpectralMeasure (spectralProj μ) where
  isSelfAdjoint s hs := L2.isSelfAdjoint_proj _ s hs
  inter s t hs ht := L2.proj_inter _ s t hs ht
  univ := L2.proj_univ _
  hasSum E hE hdisj x := L2.hasSum_proj _ hE hdisj x
  Iic_eq_zero := μ.spectralProj_Iic

namespace IsSpectralMeasure

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {P : ∀ s : Set ℝ, MeasurableSet s → K →L[ℂ] K} (hP : IsSpectralMeasure P)

include hP

theorem eq_zero_of_subset_Iic {s : Set ℝ} (hs : MeasurableSet s) (hsub : s ⊆ Set.Iic 0) :
    P s hs = 0 := by
  have h := hP.inter s (Set.Iic 0) hs measurableSet_Iic
  rw [hP.Iic_eq_zero, ContinuousLinearMap.comp_zero] at h
  have : s ∩ Set.Iic 0 = s := Set.inter_eq_left.mpr hsub
  simp only [this] at h
  exact h

theorem empty : P ∅ MeasurableSet.empty = 0 :=
  hP.eq_zero_of_subset_Iic MeasurableSet.empty (Set.empty_subset _)

omit hP in
open scoped Classical in
variable (P) in
/-- The compression `E ↦ ⟨V e_i, P(E) V e_j⟩` as a set function. -/
noncomputable def compressFun (V : EuclideanSpace ℂ H →L[ℂ] K) (s : Set ℝ) : H → H → ℂ :=
  if hs : MeasurableSet s then
    fun i j => ⟪V (EuclideanSpace.single i 1), P s hs (V (EuclideanSpace.single j 1))⟫_ℂ
  else 0

omit hP in
variable (P) in
theorem compressFun_apply (V : EuclideanSpace ℂ H →L[ℂ] K) {s : Set ℝ} (hs : MeasurableSet s)
    (i j : H) : compressFun P V s i j =
      ⟪V (EuclideanSpace.single i 1), P s hs (V (EuclideanSpace.single j 1))⟫_ℂ := by
  simp [compressFun, hs]

omit hP in
/-- Basis expansion in `EuclideanSpace ℂ H`. -/
theorem euclideanSpace_eq_sum (ξ : EuclideanSpace ℂ H) :
    ξ = ∑ i, WithLp.ofLp ξ i • EuclideanSpace.single i (1 : ℂ) := by
  ext j
  simp [EuclideanSpace.single_apply, Pi.single_apply]

omit hP in
variable (P) in
/-- The compressed set function, on measurable sets, is `⟨V ξ, P(s) V η⟩`. -/
theorem inner_eq_sesqForm_compressFun (V : EuclideanSpace ℂ H →L[ℂ] K) {s : Set ℝ}
    (hs : MeasurableSet s) (ξ η : EuclideanSpace ℂ H) :
    ⟪V ξ, P s hs (V η)⟫_ℂ = sesqForm (WithLp.ofLp ξ) (WithLp.ofLp η) (Matrix.of (compressFun P V s)) := by
  conv_lhs => rw [euclideanSpace_eq_sum ξ, euclideanSpace_eq_sum η]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, sesqForm,
    dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [compressFun_apply P V hs, Complex.star_def]
  ring

/-- **The converse construction**: `μ(E) = B P(E) B^*` with `B = V^*` is a positive tail measure
(`thm:supp-Naimark-realization`). -/
noncomputable def ofSpectralMeasure (V : EuclideanSpace ℂ H →L[ℂ] K) : PositiveTailMeasure H where
  toVectorMeasure :=
    { measureOf' := compressFun P V
      empty' := by
        rw [compressFun, dif_pos MeasurableSet.empty]
        funext i j
        simp [hP.empty]
      not_measurable' := fun s hs => by
        rw [compressFun, dif_neg hs]
      m_iUnion' := fun E hE hdisj => by
        have hdisj' : Pairwise fun m n => Disjoint (E m) (E n) :=
          fun m n hmn => (hdisj hmn : Disjoint (E m) (E n))
        rw [Pi.hasSum]
        intro i
        rw [Pi.hasSum]
        intro j
        have h1 : ∀ n, compressFun P V (E n) i j =
            ⟪V (EuclideanSpace.single i 1), P (E n) (hE n) (V (EuclideanSpace.single j 1))⟫_ℂ :=
          fun n => compressFun_apply P V (hE n) i j
        simp only [h1, compressFun_apply P V (MeasurableSet.iUnion hE)]
        exact (innerSL ℂ (V (EuclideanSpace.single i 1))).hasSum
          (hP.hasSum E hE hdisj' (V (EuclideanSpace.single j 1))) }
  posSemidef s hs := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · refine Matrix.IsHermitian.ext fun i j => ?_
      change star (compressFun P V s j i) = compressFun P V s i j
      rw [compressFun_apply P V hs, compressFun_apply P V hs]
      have hadj : ContinuousLinearMap.adjoint (P s hs) = P s hs := by
        rw [← ContinuousLinearMap.star_eq_adjoint]
        exact (hP.isSelfAdjoint s hs).star_eq
      have key : ∀ a b : K, ⟪P s hs a, b⟫_ℂ = ⟪a, P s hs b⟫_ℂ := fun a b => by
        conv_rhs => rw [← hadj]
        exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      rw [Complex.star_def, inner_conj_symm, key]
    · intro ξ
      change 0 ≤ sesqForm ξ ξ (Matrix.of (compressFun P V s))
      have h := inner_eq_sesqForm_compressFun P V hs (WithLp.toLp 2 ξ) (WithLp.toLp 2 ξ)
      simp only [WithLp.ofLp_toLp] at h
      rw [← h]
      -- `⟨V ξ, P V ξ⟩ = ⟨P V ξ, P V ξ⟩ ≥ 0`
      have hidem : P s hs ∘L P s hs = P s hs := by
        have := hP.inter s s hs hs
        simp only [Set.inter_self] at this
        exact this.symm
      have hadj : ContinuousLinearMap.adjoint (P s hs) = P s hs := by
        rw [← ContinuousLinearMap.star_eq_adjoint]
        exact (hP.isSelfAdjoint s hs).star_eq
      conv_rhs => rw [← hidem]
      rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left, hadj,
        Complex.nonneg_iff]
      refine ⟨?_, ?_⟩
      · rw [← RCLike.re_to_complex]
        exact inner_self_nonneg
      · rw [← RCLike.im_to_complex]
        exact (inner_self_im _).symm
  eq_zero_of_subset_Iic s hs hsub := by
    change compressFun P V s = 0
    rw [compressFun, dif_pos hs, hP.eq_zero_of_subset_Iic hs hsub]
    funext i j
    simp

theorem ofSpectralMeasure_apply (V : EuclideanSpace ℂ H →L[ℂ] K) (s : Set ℝ) :
    (ofSpectralMeasure hP V).toVectorMeasure s = compressFun P V s := rfl

/-- The converse realization identity `⟨V ξ, P(E) V η⟩ = ⟨ξ, μ(E) η⟩` for `μ = B P B^*`. -/
theorem inner_ofSpectralMeasure (V : EuclideanSpace ℂ H →L[ℂ] K) {s : Set ℝ}
    (hs : MeasurableSet s) (ξ η : EuclideanSpace ℂ H) :
    ⟪V ξ, P s hs (V η)⟫_ℂ =
      ⟪ξ, Matrix.toEuclideanLin (Matrix.of ((ofSpectralMeasure hP V).toVectorMeasure s)) η⟫_ℂ := by
  rw [inner_eq_sesqForm_compressFun P V hs, ofSpectralMeasure_apply,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply, sesqForm, dotProduct_comm]

/-- The scalar spectral measures `E ↦ ⟨V ξ, P(E) V η⟩` of the converse construction. -/
theorem sesqMeasure_ofSpectralMeasure (V : EuclideanSpace ℂ H →L[ℂ] K) (ξ η : EuclideanSpace ℂ H)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (ofSpectralMeasure hP V).sesqMeasure (WithLp.ofLp ξ) (WithLp.ofLp η) s = ⟪V ξ, P s hs (V η)⟫_ℂ := by
  rw [PositiveTailMeasure.sesqMeasure_apply, sesqCLM_apply, ofSpectralMeasure_apply,
    inner_eq_sesqForm_compressFun P V hs]

/-- **The converse self-energy identity.**  If `R` acts on the source vectors as the spectral
integral of `(λ - z)⁻¹` against `P` (this is what `(C - z)⁻¹ = ∫ (λ - z)⁻¹ dE_C(λ)` means), then
the self-energy of `μ = B P B^*` is `B R B^*`. -/
theorem stieltjesSelfEnergy_ofSpectralMeasure (V : EuclideanSpace ℂ H →L[ℂ] K) {z : ℂ}
    (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) (R : K →L[ℂ] K)
    (hR : ∀ ξ η : EuclideanSpace ℂ H, ⟪V ξ, R (V η)⟫_ℂ =
      VectorMeasure.integral ((ofSpectralMeasure hP V).sesqMeasure (WithLp.ofLp ξ) (WithLp.ofLp η))
        (fun lam : ℝ => ((lam : ℂ) - z)⁻¹) (ContinuousLinearMap.lsmul ℝ ℂ))
    (η : EuclideanSpace ℂ H) :
    Matrix.toEuclideanLin ((ofSpectralMeasure hP V).stieltjesSelfEnergy z) η =
      ContinuousLinearMap.adjoint V (R (V η)) := by
  refine ext_inner_left ℂ fun ξ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, hR, ← PositiveTailMeasure.sesqCLM_integral _ _ _
    ((ofSpectralMeasure hP V).integrable_resolvent hz)]
  unfold PositiveTailMeasure.stieltjesSelfEnergy
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply, sesqCLM_apply, sesqForm,
    dotProduct_comm]

end IsSpectralMeasure

/-- **`thm:supp-Naimark-realization` (Operator-measure realization and minimality), packaged.**
For every positive operator-valued tail measure `μ`: `Σ_μ(z) = B_μ (C_μ - z)⁻¹ B_μ^*`,
`K_μ` is the closed span of `P_μ(E) B_μ^* ξ`, `P_μ` is a spectral measure supported in `(0,∞)`
with `μ(E) = B_μ P_μ(E) B_μ^*`; conversely, for a spectral measure `P` supported in `(0,∞)` on a
Hilbert space `K` and `B = V^*`, `μ = B P B^*` is a positive tail measure with self-energy
`B (C - z)⁻¹ B^*` whenever `(C - z)⁻¹` acts as the spectral integral of `(λ - z)⁻¹` on the source
vectors. -/
theorem naimark_realization (μ : PositiveTailMeasure H) :
    (∀ (z : ℂ) (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) (η : EuclideanSpace ℂ H),
      Matrix.toEuclideanLin (μ.stieltjesSelfEnergy z) η =
        μ.compressB (μ.resolventOp z hz (μ.embedV η))) ∧
    (Submodule.span ℂ {y : μ.kSpace | ∃ (s : Set ℝ) (hs : MeasurableSet s) (ξ : EuclideanSpace ℂ H),
      y = μ.spectralProj s hs (ContinuousLinearMap.adjoint μ.compressB ξ)}).topologicalClosure = ⊤ ∧
    IsSpectralMeasure μ.spectralProj ∧
    (∀ (s : Set ℝ) (hs : MeasurableSet s) (η : EuclideanSpace ℂ H),
      Matrix.toEuclideanLin (Matrix.of (μ.toVectorMeasure s)) η =
        μ.compressB (μ.spectralProj s hs (μ.embedV η))) ∧
    (∀ {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      {P : ∀ s : Set ℝ, MeasurableSet s → K →L[ℂ] K} (hP : IsSpectralMeasure P)
      (V : EuclideanSpace ℂ H →L[ℂ] K),
      (∀ (s : Set ℝ) (hs : MeasurableSet s) (ξ η : EuclideanSpace ℂ H),
        ⟪V ξ, P s hs (V η)⟫_ℂ = ⟪ξ, Matrix.toEuclideanLin
          (Matrix.of ((IsSpectralMeasure.ofSpectralMeasure hP V).toVectorMeasure s)) η⟫_ℂ) ∧
      ∀ (z : ℂ) (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) (R : K →L[ℂ] K),
        (∀ ξ η : EuclideanSpace ℂ H, ⟪V ξ, R (V η)⟫_ℂ =
          VectorMeasure.integral ((IsSpectralMeasure.ofSpectralMeasure hP V).sesqMeasure
            (WithLp.ofLp ξ) (WithLp.ofLp η)) (fun lam : ℝ => ((lam : ℂ) - z)⁻¹)
            (ContinuousLinearMap.lsmul ℝ ℂ)) →
        ∀ η : EuclideanSpace ℂ H,
          Matrix.toEuclideanLin ((IsSpectralMeasure.ofSpectralMeasure hP V).stieltjesSelfEnergy z) η =
            ContinuousLinearMap.adjoint V (R (V η))) :=
  ⟨fun _ hz η => μ.stieltjesSelfEnergy_eq_compress hz η, μ.minimal,
    μ.isSpectralMeasure_spectralProj, fun s hs η => μ.toVectorMeasure_eq_compress s hs η,
    fun hP V => ⟨fun s hs ξ η => IsSpectralMeasure.inner_ofSpectralMeasure hP V hs ξ η,
      fun _ hz R hR η => IsSpectralMeasure.stieltjesSelfEnergy_ofSpectralMeasure hP V hz R hR η⟩⟩

end OperatorTailMeasure
end RenewalGeometry
