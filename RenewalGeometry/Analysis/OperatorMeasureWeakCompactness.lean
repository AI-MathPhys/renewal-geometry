/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.OperatorMeasureL2Completion
import RenewalGeometry.Spectralization.OperatorTailMeasureScalarizationExact
/-!
# Weak-* sequential compactness of bounded positive operator-valued measures

Infrastructure for `thm:supp-contact-escape` of `papers/predictive_spectral_geometry`: on a compact
metrizable space `X`, a sequence of positive operator-valued measures `ν n : PosOperatorMeasure X H`
with uniformly bounded trace mass has a subsequence converging weakly (against bounded continuous
functions) to a positive operator-valued measure `ν∞`.

* `exists_subseq_tendsto_family`: sequential compactness for finite families of finite measures
  with bounded mass (Prokhorov on a compact space, through the normalisation to probability measures
  and Mathlib's Lévy–Prokhorov metrisability).
* `PosOperatorMeasure.formMeasure ν ξ`: the scalar finite measure `E ↦ Re ⟨ξ, ν(E) ξ⟩`.
* `polarize`: reconstruction of a matrix-valued measure from the quadratic-form measures of the
  polarisation vectors `e_i + I^k e_j` (`polarize_formMeasure`).
* `exists_subseq_tendsto_integral`: the extraction, with weak convergence of the operator integrals
  `∫ g dν_{φ n} → ∫ g dν∞` for every bounded continuous `g`.
* `exists_subseq_tendsto_posOperatorMeasure`: the limit is a positive operator-valued measure
  (positivity of the limit through Jordan decomposition and Mathlib's uniqueness of finite Borel
  measures by integrals of bounded continuous functions), and every quadratic-form measure converges
  weakly.
-/

open MeasureTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal ComplexOrder InnerProductSpace

namespace RenewalGeometry
namespace OperatorMeasureL2

open OperatorTailMeasure

/-! ## Operator integrals against pushed-forward vector measures -/

/-- The push-forward of a vector measure along a continuous linear map, evaluated. -/
theorem mapRange_clm_apply' {X F F' : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] (ν : VectorMeasure X F)
    (L : F →L[ℝ] F') (s : Set X) :
    ν.mapRange L.toLinearMap.toAddMonoidHom L.continuous s = L (ν s) := rfl

theorem variation_mapRange_le' {X F F' : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] (ν : VectorMeasure X F)
    (L : F →L[ℝ] F') :
    (ν.mapRange L.toLinearMap.toAddMonoidHom L.continuous).variation ≤ ‖L‖₊ • ν.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le (fun s _ => ?_)
  rw [mapRange_clm_apply']
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  calc ‖L (ν s)‖ₑ ≤ ‖L‖ₑ * ‖ν s‖ₑ := L.le_opENorm _
    _ ≤ ‖L‖ₑ * ν.variation s := by
        gcongr
        exact VectorMeasure.enorm_measure_le_variation ν s
    _ = ↑‖L‖₊ * ν.variation s := by rw [enorm_eq_nnnorm]

theorem integrable_mapRange' {X F F' : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] (ν : VectorMeasure X F)
    (L : F →L[ℝ] F') {f : X → ℝ} (hf : Integrable f ν.variation) :
    Integrable f (ν.mapRange L.toLinearMap.toAddMonoidHom L.continuous).variation := by
  have h1 : Integrable f (‖L‖₊ • ν.variation) := hf.smul_measure_nnreal
  exact h1.mono_measure (variation_mapRange_le' ν L)

instance isFiniteMeasure_variation_mapRange {X F F' : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (ν : VectorMeasure X F) [IsFiniteMeasure ν.variation] (L : F →L[ℝ] F') :
    IsFiniteMeasure (ν.mapRange L.toLinearMap.toAddMonoidHom L.continuous).variation :=
  MeasureTheory.isFiniteMeasure_of_le _ (variation_mapRange_le' ν L)

/-- The real-scalar operator integral against a pushed-forward vector measure is the push-forward
of the operator integral. -/
theorem integral_mapRange_lsmul {X F F' : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
    (ν : VectorMeasure X F) (L : F →L[ℝ] F') {f : X → ℝ} (hf : Integrable f ν.variation) :
    VectorMeasure.integral (ν.mapRange L.toLinearMap.toAddMonoidHom L.continuous) f
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F' →L[ℝ] F') =
      L (VectorMeasure.integral ν f (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)) := by
  rw [VectorMeasure.continuousLinearMap_apply_integral hf,
    VectorMeasure.integral_eq_setToFun_transpose (integrable_mapRange' ν L hf),
    VectorMeasure.integral_eq_setToFun_transpose hf]
  have hT : (ν.mapRange L.toLinearMap.toAddMonoidHom L.continuous).transpose
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F' →L[ℝ] F') =
      ν.transpose ((ContinuousLinearMap.compL ℝ F F F' L) ∘L
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)) := by
    refine VectorMeasure.ext fun s hs => ?_
    refine ContinuousLinearMap.ext fun c => ?_
    change c • L (ν s) = L (c • ν s)
    rw [map_smul]
  simp only [hT]

/-- `∫ f d(μ.toSignedMeasure) = ∫ f dμ` for the real-scalar pairing. -/
theorem integral_toSignedMeasure_lsmul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (f : X → ℝ) :
    VectorMeasure.integral μ.toSignedMeasure f (ContinuousLinearMap.lsmul ℝ ℝ) = ∫ x, f x ∂μ := by
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) =
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip := by
    ext; simp
  rw [hflip]
  exact VectorMeasure.integral_toSignedMeasure

/-! ## Sequential compactness of bounded families of finite measures on a compact space -/

section Compact

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [TopologicalSpace.SeparableSpace X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-- **Sequential weak compactness** of finitely many uniformly bounded sequences of finite measures
on a compact metrizable space: one common subsequence converges weakly in every coordinate. -/
theorem exists_subseq_tendsto_family {ι : Type*} [Fintype ι] (m : ℕ → ι → FiniteMeasure X)
    {M : ℝ≥0} (hM : ∀ n i, (m n i).mass ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ mlim : ι → FiniteMeasure X,
      ∀ i, Tendsto (fun n => m (φ n) i) atTop (𝓝 (mlim i)) := by
  let p : ℕ → (ι → ProbabilityMeasure X) × (ι → ℝ≥0) :=
    fun n => (fun i => (m n i).normalize, fun i => (m n i).mass)
  have hS : IsCompact ((univ : Set (ι → ProbabilityMeasure X)) ×ˢ
      (Set.pi univ fun _ : ι => Icc (0 : ℝ≥0) M)) :=
    isCompact_univ.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨⟨P, c⟩, -, φ, hφ, hlim⟩ :=
    hS.tendsto_subseq (x := p) (fun n => ⟨mem_univ _, fun i _ => ⟨bot_le, hM n i⟩⟩)
  rw [Prod.tendsto_iff] at hlim
  obtain ⟨hP, hc⟩ := hlim
  refine ⟨φ, hφ, fun i => c i • (P i).toFiniteMeasure, fun i => ?_⟩
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have hPi : Tendsto (fun n => (p (φ n)).1 i) atTop (𝓝 (P i)) := tendsto_pi_nhds.mp hP i
  have hci : Tendsto (fun n => (p (φ n)).2 i) atTop (𝓝 (c i)) := tendsto_pi_nhds.mp hc i
  have hg := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hPi g
  have key : ∀ n, ∫ x, g x ∂(m n i : Measure X) =
      ((m n i).mass : ℝ) * ∫ x, g x ∂((m n i).normalize : Measure X) := by
    intro n
    conv_lhs => rw [FiniteMeasure.self_eq_mass_smul_normalize (m n i)]
    rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
    rfl
  simp only [key]
  have hlimit : ∫ x, g x ∂((c i • (P i).toFiniteMeasure : FiniteMeasure X) : Measure X) =
      (c i : ℝ) * ∫ x, g x ∂(P i : Measure X) := by
    rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
    rfl
  rw [hlimit]
  exact ((NNReal.continuous_coe.tendsto _).comp hci).mul hg

end Compact

/-! ## Scalarisation of positive operator-valued measures on a general space -/

variable {X : Type*} [MeasurableSpace X] {H : Type*} [Fintype H] [DecidableEq H]

namespace PosOperatorMeasure

variable (ν : PosOperatorMeasure X H)

/-- The scalarised signed measure `E ↦ Re ⟨ξ, ν(E) ξ⟩`. -/
noncomputable def signedForm (ξ : H → ℂ) : SignedMeasure X :=
  ν.toVectorMeasure.mapRange (quadFormCLM ξ).toLinearMap.toAddMonoidHom (quadFormCLM ξ).continuous

@[simp]
theorem signedForm_apply (ξ : H → ℂ) (s : Set X) :
    ν.signedForm ξ s = quadFormCLM ξ (ν.toVectorMeasure s) := rfl

theorem signedForm_nonneg (ξ : H → ℂ) (s : Set X) : 0 ≤ ν.signedForm ξ s := by
  rw [signedForm_apply, quadFormCLM_apply]
  exact posSemidef_re_quadForm_nonneg (ν.posSemidef_apply s) ξ

theorem zero_le_signedForm (ξ : H → ℂ) : 0 ≤ ν.signedForm ξ :=
  VectorMeasure.le_iff.mpr fun s _ => by simpa using ν.signedForm_nonneg ξ s

theorem zero_le_restrict_signedForm (ξ : H → ℂ) : 0 ≤[Set.univ] ν.signedForm ξ :=
  (VectorMeasure.le_restrict_univ_iff_le _ _).2 (ν.zero_le_signedForm ξ)

/-- The scalarised finite positive measure `E ↦ Re ⟨ξ, ν(E) ξ⟩`. -/
noncomputable def formMeasure (ξ : H → ℂ) : Measure X :=
  (ν.signedForm ξ).toMeasureOfZeroLE Set.univ MeasurableSet.univ (ν.zero_le_restrict_signedForm ξ)

instance (ξ : H → ℂ) : IsFiniteMeasure (ν.formMeasure ξ) :=
  SignedMeasure.toMeasureOfZeroLE_finite _ _ _

theorem formMeasure_real_apply (ξ : H → ℂ) {s : Set X} (hs : MeasurableSet s) :
    (ν.formMeasure ξ).real s = quadFormCLM ξ (ν.toVectorMeasure s) := by
  rw [formMeasure, SignedMeasure.toMeasureOfZeroLE_real_apply _ _ _ hs, Set.univ_inter,
    signedForm_apply]

theorem formMeasure_apply (ξ : H → ℂ) {s : Set X} (hs : MeasurableSet s) :
    ν.formMeasure ξ s = ENNReal.ofReal (quadFormCLM ξ (ν.toVectorMeasure s)) := by
  rw [← formMeasure_real_apply ν ξ hs, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem toSignedMeasure_formMeasure (ξ : H → ℂ) :
    (ν.formMeasure ξ).toSignedMeasure = ν.signedForm ξ :=
  SignedMeasure.toMeasureOfZeroLE_toSignedMeasure _ _

/-- The scalarised measure as a `FiniteMeasure`. -/
noncomputable def formFiniteMeasure (ξ : H → ℂ) : FiniteMeasure X := ⟨ν.formMeasure ξ, inferInstance⟩

@[simp]
theorem coe_formFiniteMeasure (ξ : H → ℂ) : (ν.formFiniteMeasure ξ : Measure X) = ν.formMeasure ξ := rfl

/-- The trace-mass bound on the scalarised masses. -/
theorem mass_formFiniteMeasure_le (ξ : H → ℂ) {C : ℝ}
    (hC : (Matrix.of (ν.toVectorMeasure univ)).trace.re ≤ C) :
    (ν.formFiniteMeasure ξ).mass ≤ Real.toNNReal ((∑ i, ‖ξ i‖) ^ 2 * C) := by
  change ((ν.formFiniteMeasure ξ : Measure X) univ).toNNReal ≤ _
  rw [coe_formFiniteMeasure, ν.formMeasure_apply ξ MeasurableSet.univ, ENNReal.ofReal,
    ENNReal.toNNReal_coe]
  refine Real.toNNReal_le_toNNReal ?_
  rw [quadFormCLM_apply]
  have h2 := posSemidef_norm_quadForm_le (ν.posSemidef_apply univ) ξ
  have h3 : (quadForm ξ (Matrix.of (ν.toVectorMeasure univ))).re ≤
      ‖quadForm ξ (Matrix.of (ν.toVectorMeasure univ))‖ := Complex.re_le_norm _
  have h4 : 0 ≤ (∑ i, ‖ξ i‖) ^ 2 := sq_nonneg _
  calc (quadForm ξ (Matrix.of (ν.toVectorMeasure univ))).re
      ≤ (∑ i, ‖ξ i‖) ^ 2 * (Matrix.of (ν.toVectorMeasure univ)).trace.re := h3.trans h2
    _ ≤ (∑ i, ‖ξ i‖) ^ 2 * C := by gcongr

end PosOperatorMeasure

/-! ## Polarisation of matrix-valued measures -/

/-- The polarisation vectors `e_i + I^k e_j`. -/
noncomputable def polVec (i j : H) (k : Fin 4) : H → ℂ :=
  (1 : ℂ) • Pi.single i 1 + (Complex.I ^ (k : ℕ)) • Pi.single j 1

/-- The polarisation coefficients `(1/4) conj(I^k)`. -/
noncomputable def polCoeff (k : Fin 4) : ℂ := (1 / 4 : ℂ) * (starRingEnd ℂ) (Complex.I ^ (k : ℕ))

/-- **Polarisation**: `M i j = (1/4) ∑_k conj(I^k) ⟨e_i + I^k e_j, M (e_i + I^k e_j)⟩`. -/
theorem polarization (M : Matrix H H ℂ) (i j : H) :
    ∑ k : Fin 4, polCoeff k * quadForm (polVec i j k) M = M i j := by
  simp only [polVec, polCoeff, quadForm_smul_single_add_smul_single, Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl, pow_zero,
    pow_succ, Complex.I_mul_I, star_one, one_mul, mul_one]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Polarisation through the real parts of the quadratic forms, for a positive semidefinite matrix. -/
theorem polarization_re {M : Matrix H H ℂ} (hM : M.PosSemidef) (i j : H) :
    ∑ k : Fin 4, polCoeff k * ((quadForm (polVec i j k) M).re : ℂ) = M i j := by
  rw [← polarization M i j]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  apply Complex.ext
  · simp
  · simp [posSemidef_im_quadForm_eq_zero hM]

/-- The `ℓ¹`-size of a polarisation vector is at most `2`. -/
theorem sum_norm_polVec_le (i j : H) (k : Fin 4) : ∑ a, ‖polVec i j k a‖ ≤ 2 := by
  have e1 : ∀ x : H, ‖(if x = i then (1 : ℂ) else 0)‖ = if x = i then 1 else 0 := fun x => by
    split_ifs <;> simp
  have e2 : ∀ x : H, ‖(if x = j then Complex.I ^ (k : ℕ) else 0)‖ = if x = j then 1 else 0 :=
    fun x => by split_ifs <;> simp [norm_pow]
  have h1 : ∑ a, ‖((1 : ℂ) • Pi.single i (1 : ℂ) : H → ℂ) a‖ = 1 := by
    simp [Pi.single_apply, e1, Finset.sum_ite_eq']
  have h2 : ∑ a, ‖((Complex.I ^ (k : ℕ)) • Pi.single j (1 : ℂ) : H → ℂ) a‖ = 1 := by
    simp [Pi.single_apply, e2, Finset.sum_ite_eq']
  calc ∑ a, ‖polVec i j k a‖
      ≤ ∑ a, (‖((1 : ℂ) • Pi.single i (1 : ℂ) : H → ℂ) a‖ +
          ‖((Complex.I ^ (k : ℕ)) • Pi.single j (1 : ℂ) : H → ℂ) a‖) :=
        Finset.sum_le_sum fun a _ => norm_add_le _ _
    _ = 2 := by rw [Finset.sum_add_distrib, h1, h2]; norm_num

/-- `r ↦ r • (c E_{ij})`: the rank-one matrix unit as a real continuous linear map. -/
noncomputable def unitCLM (i j : H) (c : ℂ) : ℝ →L[ℝ] (H → H → ℂ) :=
  ContinuousLinearMap.toSpanSingleton ℝ (fun a b => if a = i ∧ b = j then c else 0)

theorem unitCLM_apply (i j : H) (c : ℂ) (r : ℝ) (a b : H) :
    unitCLM i j c r a b = if a = i ∧ b = j then (r : ℂ) * c else 0 := by
  simp only [unitCLM, ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

/-- **Reconstruction of a matrix-valued measure from scalar measures by polarisation.** -/
noncomputable def polarize (m : H → H → Fin 4 → Measure X) [∀ i j k, IsFiniteMeasure (m i j k)] :
    VectorMeasure X (H → H → ℂ) :=
  ∑ k : Fin 4, ∑ i : H, ∑ j : H, (m i j k).toSignedMeasure.mapRange
    (unitCLM i j (polCoeff k)).toLinearMap.toAddMonoidHom (unitCLM i j (polCoeff k)).continuous

theorem polarize_apply (m : H → H → Fin 4 → Measure X) [∀ i j k, IsFiniteMeasure (m i j k)]
    {s : Set X} (hs : MeasurableSet s) (a b : H) :
    polarize m s a b = ∑ k : Fin 4, polCoeff k * ((m a b k).real s : ℂ) := by
  simp only [polarize, VectorMeasure.coe_finsetSum, Finset.sum_apply, mapRange_clm_apply',
    Measure.toSignedMeasure_apply_measurable hs, unitCLM_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero fun x1 _ => by simp [Ne.symm hx])
    (by simp)]
  rw [Finset.sum_eq_single b (fun x1 _ hx1 => by simp [Ne.symm hx1]) (by simp)]
  simp only [and_self, if_true]
  ring

/-- Every positive operator-valued measure is the polarisation of its quadratic-form measures. -/
theorem polarize_formMeasure (ν : PosOperatorMeasure X H) :
    polarize (fun i j k => ν.formMeasure (polVec i j k)) = ν.toVectorMeasure := by
  refine VectorMeasure.ext fun s hs => ?_
  funext a b
  rw [polarize_apply _ hs]
  simp only [PosOperatorMeasure.formMeasure_real_apply _ _ hs, quadFormCLM_apply]
  exact polarization_re (ν.posSemidef_apply s) a b

theorem integrable_toSignedMeasure_variation [TopologicalSpace X] [OpensMeasurableSpace X]
    {μ : Measure X}
    [IsFiniteMeasure μ] (g : X →ᵇ ℝ) :
    Integrable g μ.toSignedMeasure.variation := by
  rw [Measure.variation_toSignedMeasure]
  exact g.integrable _

theorem integrable_polarize [TopologicalSpace X] [OpensMeasurableSpace X]
    (m : H → H → Fin 4 → Measure X)
    [∀ i j k, IsFiniteMeasure (m i j k)] (g : X →ᵇ ℝ) : (polarize m).Integrable g := by
  refine VectorMeasure.Integrable.finsetSum_vectorMeasure fun k _ =>
    VectorMeasure.Integrable.finsetSum_vectorMeasure fun i _ =>
    VectorMeasure.Integrable.finsetSum_vectorMeasure fun j _ => ?_
  exact integrable_mapRange' _ _ (integrable_toSignedMeasure_variation g)

/-- The operator integral against a polarised measure. -/
theorem integral_polarize [TopologicalSpace X] [OpensMeasurableSpace X]
    (m : H → H → Fin 4 → Measure X)
    [∀ i j k, IsFiniteMeasure (m i j k)] (g : X →ᵇ ℝ) :
    VectorMeasure.integral (polarize m) g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)) =
      fun a b => ∑ k : Fin 4, polCoeff k * ((∫ x, g x ∂(m a b k) : ℝ) : ℂ) := by
  have hint : ∀ (i j : H) (k : Fin 4), ((m i j k).toSignedMeasure.mapRange
      (unitCLM i j (polCoeff k)).toLinearMap.toAddMonoidHom
      (unitCLM i j (polCoeff k)).continuous).Integrable g :=
    fun i j k => integrable_mapRange' _ _ (integrable_toSignedMeasure_variation g)
  unfold polarize
  rw [VectorMeasure.integral_finsetSum_vectorMeasure fun k _ =>
    VectorMeasure.Integrable.finsetSum_vectorMeasure fun i _ =>
    VectorMeasure.Integrable.finsetSum_vectorMeasure fun j _ => hint i j k]
  funext a b
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [VectorMeasure.integral_finsetSum_vectorMeasure fun i _ =>
    VectorMeasure.Integrable.finsetSum_vectorMeasure fun j _ => hint i j k]
  have h2 : ∀ i, VectorMeasure.integral (∑ j, (m i j k).toSignedMeasure.mapRange
      (unitCLM i j (polCoeff k)).toLinearMap.toAddMonoidHom (unitCLM i j (polCoeff k)).continuous) g
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)) =
      ∑ j, VectorMeasure.integral ((m i j k).toSignedMeasure.mapRange
      (unitCLM i j (polCoeff k)).toLinearMap.toAddMonoidHom (unitCLM i j (polCoeff k)).continuous) g
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)) :=
    fun i => VectorMeasure.integral_finsetSum_vectorMeasure fun j _ => hint i j k
  simp only [h2, Finset.sum_apply]
  simp only [integral_mapRange_lsmul _ _ (integrable_toSignedMeasure_variation g),
    integral_toSignedMeasure_lsmul, unitCLM_apply]
  rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero fun x1 _ => by simp [Ne.symm hx])
    (by simp)]
  rw [Finset.sum_eq_single b (fun x1 _ hx1 => by simp [Ne.symm hx1]) (by simp)]
  simp only [and_self, if_true]
  ring

/-! ## The extraction with weak convergence of the operator integrals -/

section Extraction

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [TopologicalSpace.SeparableSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X]

/-- **Weak-* sequential compactness (integral form).**  A sequence of positive operator-valued
measures with uniformly bounded trace mass has a subsequence along which all polarisation-vector
scalar measures converge weakly, and hence the operator integrals of every bounded continuous
function converge to the integrals against the polarised limit. -/
theorem exists_subseq_tendsto_integral (ν : ℕ → PosOperatorMeasure X H) {C : ℝ}
    (hC : ∀ n, (Matrix.of ((ν n).toVectorMeasure univ)).trace.re ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ mlim : H → H → Fin 4 → FiniteMeasure X,
      (∀ i j k, Tendsto (fun n => (ν (φ n)).formFiniteMeasure (polVec i j k)) atTop
        (𝓝 (mlim i j k))) ∧
      ∀ g : X →ᵇ ℝ, Tendsto (fun n => VectorMeasure.integral (ν (φ n)).toVectorMeasure g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))) atTop
        (𝓝 (VectorMeasure.integral (polarize fun i j k => (mlim i j k : Measure X)) g
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))) := by
  have hC0 : 0 ≤ C := (posSemidef_re_trace_nonneg ((ν 0).posSemidef_apply univ)).trans (hC 0)
  have hbound : ∀ n (p : H × H × Fin 4),
      ((ν n).formFiniteMeasure (polVec p.1 p.2.1 p.2.2)).mass ≤ Real.toNNReal (4 * C) := by
    intro n p
    refine ((ν n).mass_formFiniteMeasure_le _ (hC n)).trans (Real.toNNReal_le_toNNReal ?_)
    have h := sum_norm_polVec_le p.1 p.2.1 p.2.2
    have h0 : 0 ≤ ∑ a, ‖polVec p.1 p.2.1 p.2.2 a‖ := Finset.sum_nonneg fun a _ => norm_nonneg _
    have h2 : (∑ a, ‖polVec p.1 p.2.1 p.2.2 a‖) ^ 2 ≤ 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right h2 hC0
  obtain ⟨φ, hφ, mlim', hconv⟩ := exists_subseq_tendsto_family (X := X)
    (fun n (p : H × H × Fin 4) => (ν n).formFiniteMeasure (polVec p.1 p.2.1 p.2.2)) hbound
  refine ⟨φ, hφ, fun i j k => mlim' (i, j, k), fun i j k => hconv (i, j, k), fun g => ?_⟩
  have hrepr : ∀ n, VectorMeasure.integral (ν n).toVectorMeasure g
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)) =
      fun a b => ∑ k : Fin 4, polCoeff k *
        ((∫ x, g x ∂((ν n).formMeasure (polVec a b k)) : ℝ) : ℂ) := fun n => by
    rw [← polarize_formMeasure (ν n), integral_polarize]
  simp only [hrepr, integral_polarize]
  rw [tendsto_pi_nhds]
  intro a
  rw [tendsto_pi_nhds]
  intro b
  refine tendsto_finsetSum _ fun k _ => tendsto_const_nhds.mul ?_
  refine (Complex.continuous_ofReal.tendsto _).comp ?_
  have := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp (hconv (a, b, k)) g
  simpa only [PosOperatorMeasure.coe_formFiniteMeasure] using this

end Extraction

/-! ## Positivity of the limit -/

/-- `Im q_ξ` as a real continuous linear functional on `H → H → ℂ`. -/
noncomputable def quadFormImCLM (ξ : H → ℂ) : (H → H → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (quadForm ξ (Matrix.of M)).im
      map_add' := fun M N => by
        change (quadForm ξ (Matrix.of M + Matrix.of N)).im = _
        rw [quadForm_add, Complex.add_im]
      map_smul' := fun c M => by
        change (quadForm ξ (Matrix.of (c • M))).im = c * (quadForm ξ (Matrix.of M)).im
        have : Matrix.of (c • M) = (c : ℂ) • Matrix.of M := by
          ext i j
          simp [Complex.real_smul]
        rw [this, quadForm_smul, Complex.im_ofReal_mul] }

@[simp]
theorem quadFormImCLM_apply (ξ : H → ℂ) (M : H → H → ℂ) :
    quadFormImCLM ξ M = (quadForm ξ (Matrix.of M)).im := rfl

/-- The real-part quadratic-form signed measure of a matrix-valued vector measure. -/
noncomputable def reForm (V : VectorMeasure X (H → H → ℂ)) (ξ : H → ℂ) : SignedMeasure X :=
  V.mapRange (quadFormCLM ξ).toLinearMap.toAddMonoidHom (quadFormCLM ξ).continuous

/-- The imaginary-part quadratic-form signed measure of a matrix-valued vector measure. -/
noncomputable def imForm (V : VectorMeasure X (H → H → ℂ)) (ξ : H → ℂ) : SignedMeasure X :=
  V.mapRange (quadFormImCLM ξ).toLinearMap.toAddMonoidHom (quadFormImCLM ξ).continuous

theorem reForm_apply (V : VectorMeasure X (H → H → ℂ)) (ξ : H → ℂ) (s : Set X) :
    reForm V ξ s = (quadForm ξ (Matrix.of (V s))).re := rfl

theorem imForm_apply (V : VectorMeasure X (H → H → ℂ)) (ξ : H → ℂ) (s : Set X) :
    imForm V ξ s = (quadForm ξ (Matrix.of (V s))).im := rfl

theorem reForm_posOperatorMeasure (ν : PosOperatorMeasure X H) (ξ : H → ℂ) :
    reForm ν.toVectorMeasure ξ = ν.signedForm ξ := rfl

/-- The imaginary quadratic forms of a positive operator-valued measure vanish. -/
theorem imForm_posOperatorMeasure (ν : PosOperatorMeasure X H) (ξ : H → ℂ) :
    imForm ν.toVectorMeasure ξ = 0 := by
  refine VectorMeasure.ext fun s hs => ?_
  rw [imForm_apply, posSemidef_im_quadForm_eq_zero (ν.posSemidef s hs), VectorMeasure.zero_apply]

/-- A matrix whose quadratic forms are all real and nonnegative is positive semidefinite. -/
theorem posSemidef_of_quadForm (M : Matrix H H ℂ)
    (h : ∀ ξ : H → ℂ, 0 ≤ (quadForm ξ M).re ∧ (quadForm ξ M).im = 0) : M.PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
    intro v
    have key : ⟪Matrix.toEuclideanLin M v, v⟫_ℂ = (starRingEnd ℂ) (quadForm (WithLp.ofLp v) M) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
      simp only [dotProduct, quadForm, Matrix.mulVec, map_sum, map_mul, Pi.star_apply,
        Complex.star_def, Complex.conj_conj]
    rw [key, Complex.conj_conj, Complex.conj_eq_iff_im.mpr (h _).2]
  · exact Complex.nonneg_iff.mpr ⟨(h x).1, (h x).2.symm⟩

section Jordan

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Jordan-decomposition uniqueness**: a finite signed measure whose integrals of bounded
continuous functions are those of a finite positive measure `ρ` is `ρ` itself. -/
theorem signedMeasure_eq_toSignedMeasure_of_forall_integral_eq {σ : SignedMeasure X}
    {ρ : Measure X} [IsFiniteMeasure ρ]
    (h : ∀ g : X →ᵇ ℝ, VectorMeasure.integral σ g (ContinuousLinearMap.lsmul ℝ ℝ) =
      ∫ x, g x ∂ρ) :
    σ = ρ.toSignedMeasure := by
  set J := σ.toJordanDecomposition
  have hσ : σ = J.posPart.toSignedMeasure - J.negPart.toSignedMeasure :=
    (σ.toSignedMeasure_toJordanDecomposition).symm
  have key : J.posPart = J.negPart + ρ := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
    have h1 := h g
    rw [hσ, VectorMeasure.integral_sub_vectorMeasure (integrable_toSignedMeasure_variation g)
      (integrable_toSignedMeasure_variation g), integral_toSignedMeasure_lsmul,
      integral_toSignedMeasure_lsmul] at h1
    rw [integral_add_measure (g.integrable _) (g.integrable _)]
    linarith
  refine VectorMeasure.ext fun s hs => ?_
  rw [hσ, VectorMeasure.sub_apply, Measure.toSignedMeasure_apply_measurable hs,
    Measure.toSignedMeasure_apply_measurable hs, Measure.toSignedMeasure_apply_measurable hs]
  have h1 : J.posPart.real s = (J.negPart + ρ).real s := congrArg (fun μ : Measure X => μ.real s) key
  have h2 : (J.negPart + ρ).real s = J.negPart.real s + ρ.real s := by
    simp only [measureReal_def, Measure.add_apply]
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  linarith

end Jordan

section Limit

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [TopologicalSpace.SeparableSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X]

/-- **Weak-* sequential compactness of bounded positive operator-valued measures.**  On a compact
metrizable space, a sequence of positive operator-valued measures with uniformly bounded trace mass
has a subsequence converging weakly to a positive operator-valued measure `νlim`: every
quadratic-form measure `E ↦ Re ⟨ξ, ν(E) ξ⟩` converges weakly, and the operator integrals of every
bounded continuous function converge. -/
theorem exists_subseq_tendsto_posOperatorMeasure (ν : ℕ → PosOperatorMeasure X H) {C : ℝ}
    (hC : ∀ n, (Matrix.of ((ν n).toVectorMeasure univ)).trace.re ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νlim : PosOperatorMeasure X H,
      (∀ ξ : H → ℂ, Tendsto (fun n => (ν (φ n)).formFiniteMeasure ξ) atTop
        (𝓝 (νlim.formFiniteMeasure ξ))) ∧
      ∀ g : X →ᵇ ℝ, Tendsto (fun n => VectorMeasure.integral (ν (φ n)).toVectorMeasure g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))) atTop
        (𝓝 (VectorMeasure.integral νlim.toVectorMeasure g
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))) := by
  obtain ⟨φ, hφ, mlim, -, hint⟩ := exists_subseq_tendsto_integral ν hC
  set V : VectorMeasure X (H → H → ℂ) := polarize fun i j k => (mlim i j k : Measure X) with hV
  have hintν : ∀ n (g : X →ᵇ ℝ), (ν n).toVectorMeasure.Integrable g := fun n g => by
    rw [← polarize_formMeasure (ν n)]
    exact integrable_polarize _ g
  have hintV : ∀ g : X →ᵇ ℝ, V.Integrable g := fun g => integrable_polarize _ g
  -- the real quadratic forms converge
  have hre : ∀ (ξ : H → ℂ) (g : X →ᵇ ℝ),
      Tendsto (fun n => ∫ x, g x ∂((ν (φ n)).formMeasure ξ)) atTop
        (𝓝 (VectorMeasure.integral (reForm V ξ) g (ContinuousLinearMap.lsmul ℝ ℝ))) := by
    intro ξ g
    have h := ((quadFormCLM ξ).continuous.tendsto _).comp (hint g)
    have e1 : ∀ n, quadFormCLM ξ (VectorMeasure.integral (ν n).toVectorMeasure g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))) =
        ∫ x, g x ∂((ν n).formMeasure ξ) := fun n => by
      rw [← integral_mapRange_lsmul _ _ (hintν n g)]
      change VectorMeasure.integral (reForm (ν n).toVectorMeasure ξ) g _ = _
      rw [reForm_posOperatorMeasure, ← PosOperatorMeasure.toSignedMeasure_formMeasure,
        integral_toSignedMeasure_lsmul]
    have e2 : quadFormCLM ξ (VectorMeasure.integral V g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))) =
        VectorMeasure.integral (reForm V ξ) g (ContinuousLinearMap.lsmul ℝ ℝ) := by
      rw [← integral_mapRange_lsmul _ _ (hintV g)]
      rfl
    rw [← e2]
    refine h.congr fun n => ?_
    exact e1 (φ n)
  -- the imaginary quadratic forms vanish in the limit
  have him : ∀ (ξ : H → ℂ) (g : X →ᵇ ℝ),
      VectorMeasure.integral (imForm V ξ) g (ContinuousLinearMap.lsmul ℝ ℝ) = 0 := by
    intro ξ g
    have h := ((quadFormImCLM ξ).continuous.tendsto _).comp (hint g)
    have e1 : ∀ n, quadFormImCLM ξ (VectorMeasure.integral (ν n).toVectorMeasure g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))) = 0 := fun n => by
      rw [← integral_mapRange_lsmul _ _ (hintν n g)]
      change VectorMeasure.integral (imForm (ν n).toVectorMeasure ξ) g _ = _
      rw [imForm_posOperatorMeasure, VectorMeasure.integral_zero_vectorMeasure]
    have e2 : quadFormImCLM ξ (VectorMeasure.integral V g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ))) =
        VectorMeasure.integral (imForm V ξ) g (ContinuousLinearMap.lsmul ℝ ℝ) := by
      rw [← integral_mapRange_lsmul _ _ (hintV g)]
      rfl
    rw [← e2]
    have h' : Tendsto (fun n => quadFormImCLM ξ (VectorMeasure.integral (ν (φ n)).toVectorMeasure g
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (H → H → ℂ) →L[ℝ] (H → H → ℂ)))) atTop (𝓝 0) := by
      simp only [e1]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h h'
  -- the real quadratic-form measures of the limit are positive measures
  have hpos : ∀ ξ : H → ℂ, ∃ ρ : Measure X, ∃ _ : IsFiniteMeasure ρ, reForm V ξ = ρ.toSignedMeasure := by
    intro ξ
    have hbound : ∀ n (_ : Unit), ((ν (φ n)).formFiniteMeasure ξ).mass ≤
        Real.toNNReal ((∑ i, ‖ξ i‖) ^ 2 * C) :=
      fun n _ => (ν (φ n)).mass_formFiniteMeasure_le ξ (hC (φ n))
    obtain ⟨ψ, hψ, ρ', hρ'⟩ := exists_subseq_tendsto_family (X := X)
      (fun n (_ : Unit) => (ν (φ n)).formFiniteMeasure ξ) hbound
    refine ⟨(ρ' () : Measure X), inferInstance, ?_⟩
    refine signedMeasure_eq_toSignedMeasure_of_forall_integral_eq fun g => ?_
    have h1 := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp (hρ' ()) g
    have h2 := (hre ξ g).comp hψ.tendsto_atTop
    exact (tendsto_nhds_unique h1 h2).symm
  have himzero : ∀ ξ : H → ℂ, imForm V ξ = 0 := by
    intro ξ
    have := signedMeasure_eq_toSignedMeasure_of_forall_integral_eq (σ := imForm V ξ)
      (ρ := (0 : Measure X)) fun g => by rw [him ξ g, integral_zero_measure]
    rw [this, Measure.toSignedMeasure_zero]
  -- the limit is a positive operator-valued measure
  let νlim : PosOperatorMeasure X H :=
    { toVectorMeasure := V
      posSemidef := fun s hs => by
        refine posSemidef_of_quadForm _ fun ξ => ⟨?_, ?_⟩
        · obtain ⟨ρ, _, hρ⟩ := hpos ξ
          have : reForm V ξ s = ρ.real s := by
            rw [hρ, Measure.toSignedMeasure_apply_measurable hs]
          rw [← reForm_apply, this]
          exact measureReal_nonneg
        · rw [← imForm_apply, himzero ξ, VectorMeasure.zero_apply] }
  refine ⟨φ, hφ, νlim, fun ξ => ?_, hint⟩
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have e : ∫ x, g x ∂((νlim.formFiniteMeasure ξ : FiniteMeasure X) : Measure X) =
      VectorMeasure.integral (reForm V ξ) g (ContinuousLinearMap.lsmul ℝ ℝ) := by
    rw [PosOperatorMeasure.coe_formFiniteMeasure, ← integral_toSignedMeasure_lsmul,
      PosOperatorMeasure.toSignedMeasure_formMeasure]
    rfl
  rw [e]
  simpa only [PosOperatorMeasure.coe_formFiniteMeasure] using hre ξ g

end Limit

end OperatorMeasureL2
end RenewalGeometry
