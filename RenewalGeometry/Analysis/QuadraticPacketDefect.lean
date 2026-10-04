/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SignedMeasureWeakCompactness
import RenewalGeometry.Continuum.MonotoneDefectRemovalExact

/-!
# Quadratic defect measures of weakly convergent `L²` packets with variable coefficients

Generic measure theory (no renewal notions) for the quadratic stress defects of the
Einstein–Standard-Model action-closure manuscript (`prop:YM-defect`, `thm:higgs-defect`,
`thm:zero-defect-characterization`); it generalizes the covariance-measure calculus of
`PositivePacketDefectExact.lean` (`lem:positive-packet-defect`) to an arbitrary finite index set,
to function-level packets, and to positivity on a pointwise admissible set of directions (used
for two-form packets, whose stress is coercive only on antisymmetric tensors).

Setting: a compact metric space `K` (a compact chart including its boundary, or `𝕋^d`) with a
finite Borel measure `V₀` (the positive reference volume).  A *packet* is a finite family
`Y i : K → ℝ`, `i : ι`, of real `L²(V₀)` functions (the realified components of a field in a fixed
orthonormal frame).  Coefficient fields are continuous matrix fields `P : C(K, ι → ι → ℝ)`, and the
quadratic density is `qf (P x) (Y x) = Σ_{ij} P_{ij}(x) Y_i(x) Y_j(x)`.  As in
`PositivePacketDefectExact.lean`, matrix-valued Radon measures are continuous linear functionals on
`C(K, ι → ι → ℝ)` (Riesz identification), and scalar ones are functionals on `C(K, ℝ)`.

* `WeakL2`, `StrongL2`: weak and strong `L²` convergence of packets (componentwise).
* `WeakL2.bounded`: weakly convergent packets are bounded (Banach–Steinhaus in `L²`).
* `quadCLM Y`: the matrix measure `Y ⊗ Y dV₀`, `P ↦ ∫ qf (P x) (Y x) dV₀`.
* `exists_isDefect`: after extraction, `Y_h ⊗ Y_h dV₀ ⇀* Y ⊗ Y dV₀ + 𝖰` (`IsDefect`).
* `IsDefect.tendsto_sub`: `𝖰(P) = lim ∫ qf (P x) (Y_h x - Y x) dV₀` (cross terms vanish weakly).
* `IsDefect.tendsto_coef`: for coefficient fields `P_h → P` uniformly,
  `∫ qf (P_h) (Y_h) dV₀ → ∫ qf (P) (Y) dV₀ + 𝖰(P)`.
* `IsDefect.le_of_qf_le`, `IsDefect.nonneg`: if `qf (P x) z ≤ qf (P' x) z` for every admissible
  direction `z ∈ S x` and the differences `Y_h - Y` are a.e. admissible, then `𝖰(P) ≤ 𝖰(P')`.
* `traceMeasure`, `IsDefect.tendsto_trace`, `IsDefect.traceMeasure_nonneg`:
  `|Y_h|² dV₀ ⇀* |Y|² dV₀ + μ_Y`, `μ_Y = tr 𝖰 ≥ 0`.
* `IsDefect.eq_zero_iff_strongL2`, `IsDefect.traceMeasure_eq_zero_iff_strongL2`:
  `𝖰 = 0 ↔ μ_Y = 0 ↔ Y_h → Y` in `L²`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace RenewalGeometry

namespace QuadraticPacketDefect

/-! ## Pointwise quadratic forms -/

section Pointwise

variable {ι : Type*} [Fintype ι]

/-- The quadratic form `qf b z = Σ_{ij} b_{ij} z_i z_j`. -/
def qf (b : ι → ι → ℝ) (z : ι → ℝ) : ℝ := ∑ i, ∑ j, b i j * (z i * z j)

theorem qf_add_left (b b' : ι → ι → ℝ) (z : ι → ℝ) : qf (b + b') z = qf b z + qf b' z := by
  simp only [qf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem qf_smul_left (c : ℝ) (b : ι → ι → ℝ) (z : ι → ℝ) : qf (c • b) z = c * qf b z := by
  simp only [qf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem qf_sub_left (b b' : ι → ι → ℝ) (z : ι → ℝ) : qf (b - b') z = qf b z - qf b' z := by
  simp only [qf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem qf_zero_left (z : ι → ℝ) : qf (0 : ι → ι → ℝ) z = 0 := by simp [qf]

/-- Expansion `qf b (w + z) = qf b w + Σ b_{ij} z_i w_j + Σ b_{ij} w_i z_j + qf b z`. -/
theorem qf_add_right (b : ι → ι → ℝ) (w z : ι → ℝ) :
    qf b (w + z) = qf b w + ∑ i, ∑ j, b i j * (z i * w j) + ∑ i, ∑ j, b i j * (w i * z j) +
      qf b z := by
  simp only [qf, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `|qf b z| ≤ ‖b‖ · card ι · Σ zᵢ²`. -/
theorem abs_qf_le (b : ι → ι → ℝ) (z : ι → ℝ) :
    |qf b z| ≤ ‖b‖ * (Fintype.card ι * ∑ i, z i ^ 2) := by
  have hb : ∀ i j, |b i j| ≤ ‖b‖ := fun i j =>
    (Real.norm_eq_abs (b i j) ▸ (norm_le_pi_norm (b i) j)).trans (norm_le_pi_norm b i)
  have key : ∑ i, ∑ j, (z i ^ 2 + z j ^ 2) / 2 = Fintype.card ι * ∑ i, z i ^ 2 := by
    simp only [add_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.sum_div]
    ring
  calc |qf b z| ≤ ∑ i, ∑ j, |b i j * (z i * z j)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, ‖b‖ * ((z i ^ 2 + z j ^ 2) / 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        refine mul_le_mul (hb i j) ?_ (abs_nonneg _) (norm_nonneg _)
        rw [abs_mul]
        nlinarith [sq_nonneg (|z i| - |z j|), sq_abs (z i), sq_abs (z j)]
    _ = ‖b‖ * (Fintype.card ι * ∑ i, z i ^ 2) := by
        rw [← key, Finset.mul_sum]
        simp only [Finset.mul_sum]

/-- The identity coefficient `δ_{ij}`. -/
def idCoef [DecidableEq ι] : ι → ι → ℝ := fun i j => if i = j then 1 else 0

theorem qf_idCoef [DecidableEq ι] (z : ι → ℝ) : qf idCoef z = ∑ i, z i ^ 2 := by
  simp only [qf, idCoef, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  exact Finset.sum_congr rfl fun i _ => (sq (z i)).symm

end Pointwise


/-! ## Packets, energies and the matrix measure `Y ⊗ Y dV₀` -/

section Packets

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable (V₀ : Measure K) [IsFiniteMeasure V₀]
variable {ι : Type*} [Fintype ι]

/-- The `L²` energy `Σ_i ∫ Y_i² dV₀` of a packet. -/
noncomputable def energy (Y : ι → K → ℝ) : ℝ := ∑ i, ∫ x, Y i x ^ 2 ∂V₀

/-- Weak `L²(V₀)` convergence `Y_h ⇀ Y₀` of packets (componentwise, tested on `L²`). -/
structure WeakL2 (Y : ℕ → ι → K → ℝ) (Y₀ : ι → K → ℝ) : Prop where
  memLp : ∀ h i, MemLp (Y h i) 2 V₀
  memLp_lim : ∀ i, MemLp (Y₀ i) 2 V₀
  tendsto : ∀ i (v : K → ℝ), MemLp v 2 V₀ →
    Tendsto (fun h => ∫ x, v x * Y h i x ∂V₀) atTop (𝓝 (∫ x, v x * Y₀ i x ∂V₀))

/-- Strong `L²(V₀)` convergence `Y_h → Y₀` of packets: `∫ (Y_{h,i} - Y_i)² dV₀ → 0`. -/
def StrongL2 (Y : ℕ → ι → K → ℝ) (Y₀ : ι → K → ℝ) : Prop :=
  ∀ i, Tendsto (fun h => ∫ x, (Y h i x - Y₀ i x) ^ 2 ∂V₀) atTop (𝓝 0)

variable {V₀}

omit [CompactSpace K] [IsFiniteMeasure V₀] in
theorem energy_nonneg (Y : ι → K → ℝ) : 0 ≤ energy V₀ Y :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

omit [CompactSpace K] [IsFiniteMeasure V₀] in
theorem aestronglyMeasurable_qf (P : C(K, ι → ι → ℝ)) {Y : ι → K → ℝ}
    (hY : ∀ i, AEStronglyMeasurable (Y i) V₀) :
    AEStronglyMeasurable (fun x => qf (P x) (fun i => Y i x)) V₀ := by
  unfold qf
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp P.continuous)).aestronglyMeasurable.mul
    ((hY i).mul (hY j))

omit [IsFiniteMeasure V₀] in
theorem abs_qf_apply_le (P : C(K, ι → ι → ℝ)) (z : ι → ℝ) (x : K) :
    |qf (P x) z| ≤ ‖P‖ * (Fintype.card ι * ∑ i, z i ^ 2) := by
  refine (abs_qf_le (P x) z).trans ?_
  exact mul_le_mul_of_nonneg_right (P.norm_coe_le_norm x) (by positivity)

omit [CompactSpace K] [IsFiniteMeasure V₀] in
theorem integrable_sum_sq {Y : ι → K → ℝ} (hY : ∀ i, MemLp (Y i) 2 V₀) :
    Integrable (fun x => ∑ i, Y i x ^ 2) V₀ :=
  integrable_finsetSum _ fun i _ => (hY i).integrable_sq

omit [CompactSpace K] [IsFiniteMeasure V₀] in
theorem integral_sum_sq {Y : ι → K → ℝ} (hY : ∀ i, MemLp (Y i) 2 V₀) :
    ∫ x, ∑ i, Y i x ^ 2 ∂V₀ = energy V₀ Y :=
  integral_finsetSum _ fun i _ => (hY i).integrable_sq

omit [IsFiniteMeasure V₀] in
theorem integrable_qf (P : C(K, ι → ι → ℝ)) {Y : ι → K → ℝ} (hY : ∀ i, MemLp (Y i) 2 V₀) :
    Integrable (fun x => qf (P x) (fun i => Y i x)) V₀ := by
  refine Integrable.mono' (((integrable_sum_sq hY).const_mul (Fintype.card ι)).const_mul ‖P‖)
    (aestronglyMeasurable_qf P fun i => (hY i).1) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_qf_apply_le P _ x

omit [IsFiniteMeasure V₀] in
theorem abs_integral_qf_le (P : C(K, ι → ι → ℝ)) {Y : ι → K → ℝ} (hY : ∀ i, MemLp (Y i) 2 V₀) :
    |∫ x, qf (P x) (fun i => Y i x) ∂V₀| ≤ ‖P‖ * (Fintype.card ι * energy V₀ Y) := by
  rw [← integral_sum_sq hY, ← integral_const_mul, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le
    (((integrable_sum_sq hY).const_mul (Fintype.card ι)).const_mul ‖P‖)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_qf_apply_le P _ x

variable (V₀) in
/-- The matrix-valued measure `Y ⊗ Y dV₀`, as the functional `P ↦ ∫ qf (P x) (Y x) dV₀` on
`C(K, ι → ι → ℝ)` (zero if `Y` is not an `L²` packet). -/
noncomputable def quadCLM (Y : ι → K → ℝ) : StrongDual ℝ C(K, ι → ι → ℝ) := by
  classical
  exact if hY : ∀ i, MemLp (Y i) 2 V₀ then
    LinearMap.mkContinuous
      { toFun := fun P => ∫ x, qf (P x) (fun i => Y i x) ∂V₀
        map_add' := fun P P' => by
          simp only [ContinuousMap.add_apply, qf_add_left]
          exact integral_add (integrable_qf P hY) (integrable_qf P' hY)
        map_smul' := fun c P => by
          simp only [ContinuousMap.smul_apply, qf_smul_left, RingHom.id_apply, smul_eq_mul]
          exact integral_const_mul c _ }
      (Fintype.card ι * energy V₀ Y) fun P => by
        rw [Real.norm_eq_abs, mul_comm]
        exact abs_integral_qf_le P hY
  else 0

omit [IsFiniteMeasure V₀] in
theorem quadCLM_apply {Y : ι → K → ℝ} (hY : ∀ i, MemLp (Y i) 2 V₀) (P : C(K, ι → ι → ℝ)) :
    quadCLM V₀ Y P = ∫ x, qf (P x) (fun i => Y i x) ∂V₀ := by
  simp [quadCLM, hY]

omit [IsFiniteMeasure V₀] in
theorem abs_quadCLM_le {Y : ι → K → ℝ} (hY : ∀ i, MemLp (Y i) 2 V₀) (P : C(K, ι → ι → ℝ)) :
    |quadCLM V₀ Y P| ≤ ‖P‖ * (Fintype.card ι * energy V₀ Y) := by
  rw [quadCLM_apply hY]
  exact abs_integral_qf_le P hY

omit [IsFiniteMeasure V₀] in
theorem norm_quadCLM_le {Y : ι → K → ℝ} (hY : ∀ i, MemLp (Y i) 2 V₀) :
    ‖quadCLM V₀ Y‖ ≤ Fintype.card ι * energy V₀ Y :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) (energy_nonneg Y))
    fun P => by
      rw [Real.norm_eq_abs, mul_comm]
      exact abs_quadCLM_le hY P

/-! ### Weakly convergent packets -/

variable {Y : ℕ → ι → K → ℝ} {Y₀ : ι → K → ℝ}

omit [CompactSpace K] [IsFiniteMeasure V₀] in
/-- Weakly convergent packets are bounded in `L²` (uniform boundedness in the Hilbert space
`L²(V₀)`, through the Riesz representation of its dual). -/
theorem WeakL2.bounded (hY : WeakL2 V₀ Y Y₀) : ∃ C, ∀ h, energy V₀ (Y h) ≤ C := by
  have hcomp : ∀ i, ∃ C : ℝ, ∀ h, ∫ x, Y h i x ^ 2 ∂V₀ ≤ C := by
    intro i
    let y : ℕ → Lp ℝ 2 V₀ := fun h => (hY.memLp h i).toLp (Y h i)
    let y₀ : Lp ℝ 2 V₀ := (hY.memLp_lim i).toLp (Y₀ i)
    have hinner : ∀ (w f : Lp ℝ 2 V₀), inner ℝ w f = ∫ x, w x * f x ∂V₀ := by
      intro w f
      rw [L2.inner_def]
      simp only [RCLike.inner_apply, conj_trivial]
      exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    have hweak : ∀ φ : StrongDual ℝ (Lp ℝ 2 V₀), Tendsto (fun h => φ (y h)) atTop (𝓝 (φ y₀)) := by
      intro φ
      set w := (InnerProductSpace.toDual ℝ (Lp ℝ 2 V₀)).symm φ
      have e : ∀ f : Lp ℝ 2 V₀, φ f = ∫ x, w x * f x ∂V₀ := by
        intro f
        rw [← hinner, InnerProductSpace.toDual_symm_apply]
      simp only [e]
      have h1 := hY.tendsto i w (Lp.memLp w)
      have ey : ∀ h, ∫ x, w x * y h x ∂V₀ = ∫ x, w x * Y h i x ∂V₀ := fun h =>
        integral_congr_ae ((hY.memLp h i).coeFn_toLp.mono fun x hx => by simp only [y, hx])
      have ey₀ : ∫ x, w x * y₀ x ∂V₀ = ∫ x, w x * Y₀ i x ∂V₀ :=
        integral_congr_ae ((hY.memLp_lim i).coeFn_toLp.mono fun x hx => by simp only [y₀, hx])
      simp only [ey, ey₀]
      exact h1
    obtain ⟨C, hC⟩ := MonotoneDefectRemoval.norm_bounded_of_weak_tendsto y y₀ hweak
    refine ⟨C ^ 2, fun h => ?_⟩
    have e1 : ∫ x, Y h i x ^ 2 ∂V₀ = ‖y h‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hinner]
      exact (integral_congr_ae ((hY.memLp h i).coeFn_toLp.mono fun x hx => by
        simp only [y, hx, sq])).symm
    rw [e1]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC h) 2
  choose C hC using hcomp
  exact ⟨∑ i, C i, fun h => Finset.sum_le_sum fun i _ => hC i h⟩

omit [CompactSpace K] [IsFiniteMeasure V₀] in
theorem WeakL2.comp (hY : WeakL2 V₀ Y Y₀) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    WeakL2 V₀ (fun h => Y (σ h)) Y₀ :=
  ⟨fun h => hY.memLp (σ h), hY.memLp_lim, fun i v hv => (hY.tendsto i v hv).comp hσ.tendsto_atTop⟩

omit [IsFiniteMeasure V₀] in
/-- Cross terms against a fixed `L²` function and a continuous coefficient tend to their weak
limit: `∫ c W Y_{h,i} → ∫ c W Y_i`. -/
theorem WeakL2.tendsto_cross (hY : WeakL2 V₀ Y Y₀) (c : C(K, ℝ)) {W : K → ℝ}
    (hW : MemLp W 2 V₀) (i : ι) :
    Tendsto (fun h => ∫ x, c x * W x * Y h i x ∂V₀) atTop (𝓝 (∫ x, c x * W x * Y₀ i x ∂V₀)) := by
  have hv : MemLp (fun x => c x * W x) 2 V₀ := by
    refine (hW.const_mul ‖c‖).of_le
      (c.continuous.aestronglyMeasurable.mul hW.1) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (norm_nonneg c)]
    exact mul_le_mul_of_nonneg_right (c.norm_coe_le_norm x) (norm_nonneg _)
  exact hY.tendsto i _ hv

/-- The defect relation `Y_h ⊗ Y_h dV₀ ⇀* Y ⊗ Y dV₀ + 𝖰`, tested against every continuous
coefficient field. -/
def IsDefect (V₀ : Measure K) (Y : ℕ → ι → K → ℝ) (Y₀ : ι → K → ℝ)
    (Q : StrongDual ℝ C(K, ι → ι → ℝ)) : Prop :=
  ∀ P, Tendsto (fun h => quadCLM V₀ (Y h) P) atTop (𝓝 (quadCLM V₀ Y₀ P + Q P))

/-- **Extraction of the matrix defect measure**: a weakly convergent packet has a subsequence and
a matrix-valued measure `𝖰` with `Y_{σ h} ⊗ Y_{σ h} dV₀ ⇀* Y ⊗ Y dV₀ + 𝖰` (sequential
Banach–Alaoglu in the dual of the separable space `C(K, ι → ι → ℝ)`). -/
theorem exists_isDefect (hY : WeakL2 V₀ Y Y₀) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ Q : StrongDual ℝ C(K, ι → ι → ℝ),
      IsDefect V₀ (fun h => Y (σ h)) Y₀ Q := by
  obtain ⟨C, hC⟩ := hY.bounded
  obtain ⟨σ, hσ, L, hL⟩ := SignedMeasureWeakCompactness.exists_subseq_weakStar_tendsto
    (fun h => quadCLM V₀ (Y h)) (C := Fintype.card ι * C) fun h =>
      (norm_quadCLM_le (hY.memLp h)).trans
        (mul_le_mul_of_nonneg_left (hC h) (Nat.cast_nonneg _))
  refine ⟨σ, hσ, L - quadCLM V₀ Y₀, fun P => ?_⟩
  rw [sub_apply, add_sub_cancel]
  exact hL P

variable {Q : StrongDual ℝ C(K, ι → ι → ℝ)}

omit [IsFiniteMeasure V₀] in
theorem integrable_coef_mul (c : C(K, ℝ)) {a b : K → ℝ} (ha : MemLp a 2 V₀) (hb : MemLp b 2 V₀) :
    Integrable (fun x => c x * (a x * b x)) V₀ :=
  (ha.integrable_mul hb).bdd_mul c.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => c.norm_coe_le_norm x)

/-- The entry `P_{ij}` of a coefficient field, as a continuous function. -/
def entry (P : C(K, ι → ι → ℝ)) (i j : ι) : C(K, ℝ) :=
  ⟨fun x => P x i j, (continuous_apply j).comp ((continuous_apply i).comp P.continuous)⟩

theorem entry_apply (P : C(K, ι → ι → ℝ)) (i j : ι) (x : K) :
    entry P i j x = P x i j := rfl

omit [IsFiniteMeasure V₀] in
/-- A single cross term `∫ P_{ij} (Y_{h,i} - Y_i) W` tends to zero for `W ∈ L²`. -/
theorem WeakL2.tendsto_cross_zero (hY : WeakL2 V₀ Y Y₀) (c : C(K, ℝ)) {W : K → ℝ}
    (hW : MemLp W 2 V₀) (i : ι) :
    Tendsto (fun h => ∫ x, c x * ((Y h i x - Y₀ i x) * W x) ∂V₀) atTop (𝓝 0) := by
  have h1 := hY.tendsto_cross c hW i
  have hlim := h1.sub_const (∫ x, c x * W x * Y₀ i x ∂V₀)
  rw [sub_self] at hlim
  refine hlim.congr fun h => ?_
  have hi1 : Integrable (fun x => c x * W x * Y h i x) V₀ := by
    simpa only [mul_assoc] using integrable_coef_mul c hW (hY.memLp h i)
  have hi2 : Integrable (fun x => c x * W x * Y₀ i x) V₀ := by
    simpa only [mul_assoc] using integrable_coef_mul c hW (hY.memLp_lim i)
  rw [← integral_sub hi1 hi2]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

/-- `𝖰(P) = lim ∫ qf (P x) (Y_h x - Y x) dV₀`: the defect is carried by the differences
(the cross terms vanish by weak convergence). -/
theorem IsDefect.tendsto_sub (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    (P : C(K, ι → ι → ℝ)) :
    Tendsto (fun h => ∫ x, qf (P x) (fun i => Y h i x - Y₀ i x) ∂V₀) atTop (𝓝 (Q P)) := by
  have hc1 : ∀ i j, Tendsto (fun h => ∫ x, P x i j * ((Y h i x - Y₀ i x) * Y₀ j x) ∂V₀) atTop
      (𝓝 0) := fun i j => hY.tendsto_cross_zero (entry P i j) (hY.memLp_lim j) i
  have hc2 : ∀ i j, Tendsto (fun h => ∫ x, P x i j * (Y₀ i x * (Y h j x - Y₀ j x)) ∂V₀) atTop
      (𝓝 0) := by
    intro i j
    refine (hY.tendsto_cross_zero (entry P i j) (hY.memLp_lim i) j).congr fun h => ?_
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [entry_apply]; ring)
  have hd : ∀ h i, MemLp (fun x => Y h i x - Y₀ i x) 2 V₀ := fun h i =>
    (hY.memLp h i).sub (hY.memLp_lim i)
  have hexp : ∀ h, ∫ x, qf (P x) (fun i => Y h i x - Y₀ i x) ∂V₀ =
      quadCLM V₀ (Y h) P - quadCLM V₀ Y₀ P -
        ∑ i, ∑ j, ∫ x, P x i j * ((Y h i x - Y₀ i x) * Y₀ j x) ∂V₀ -
        ∑ i, ∑ j, ∫ x, P x i j * (Y₀ i x * (Y h j x - Y₀ j x)) ∂V₀ := by
    intro h
    have hpt : ∀ x, qf (P x) (fun i => Y h i x - Y₀ i x) =
        qf (P x) (fun i => Y h i x) - qf (P x) (fun i => Y₀ i x) -
          ∑ i, ∑ j, P x i j * ((Y h i x - Y₀ i x) * Y₀ j x) -
          ∑ i, ∑ j, P x i j * (Y₀ i x * (Y h j x - Y₀ j x)) := by
      intro x
      have := qf_add_right (P x) (fun i => Y₀ i x) (fun i => Y h i x - Y₀ i x)
      have e : ((fun i => Y₀ i x) + fun i => Y h i x - Y₀ i x) = fun i => Y h i x := by
        funext i; simp
      rw [e] at this
      linarith
    have hint1 : ∀ i j, Integrable (fun x => P x i j * ((Y h i x - Y₀ i x) * Y₀ j x)) V₀ :=
      fun i j => integrable_coef_mul (entry P i j) (hd h i) (hY.memLp_lim j)
    have hint2 : ∀ i j, Integrable (fun x => P x i j * (Y₀ i x * (Y h j x - Y₀ j x))) V₀ :=
      fun i j => integrable_coef_mul (entry P i j) (hY.memLp_lim i) (hd h j)
    have hs1 : Integrable (fun x => ∑ i, ∑ j, P x i j * ((Y h i x - Y₀ i x) * Y₀ j x)) V₀ :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint1 i j
    have hs2 : Integrable (fun x => ∑ i, ∑ j, P x i j * (Y₀ i x * (Y h j x - Y₀ j x))) V₀ :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint2 i j
    simp_rw [hpt]
    have iq := integrable_qf P (hY.memLp h)
    have iq0 := integrable_qf P hY.memLp_lim
    have e3 := integral_sub ((iq.sub iq0).sub hs1) hs2
    have e2 := integral_sub (iq.sub iq0) hs1
    have e1 := integral_sub iq iq0
    simp only [Pi.sub_apply] at e1 e2 e3
    rw [e3, e2, e1,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint1 i j,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint2 i j,
      quadCLM_apply (hY.memLp h), quadCLM_apply hY.memLp_lim]
    simp only [integral_finsetSum _ fun j _ => hint1 _ j,
      integral_finsetSum _ fun j _ => hint2 _ j]
  simp_rw [hexp]
  have hs1 : Tendsto (fun h => ∑ i, ∑ j, ∫ x, P x i j * ((Y h i x - Y₀ i x) * Y₀ j x) ∂V₀)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => hc1 i j
  have hs2 : Tendsto (fun h => ∑ i, ∑ j, ∫ x, P x i j * (Y₀ i x * (Y h j x - Y₀ j x)) ∂V₀)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => hc2 i j
  have := (((hQ P).sub_const (quadCLM V₀ Y₀ P)).sub hs1).sub hs2
  simpa using this


/-- **Coefficient replacement**: for coefficient fields `P_h → P` uniformly,
`∫ qf (P_h) (Y_h) dV₀ → ∫ qf (P) (Y) dV₀ + 𝖰(P)`. -/
theorem IsDefect.tendsto_coef (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    {P : ℕ → C(K, ι → ι → ℝ)} {P₀ : C(K, ι → ι → ℝ)} (hP : Tendsto P atTop (𝓝 P₀)) :
    Tendsto (fun h => quadCLM V₀ (Y h) (P h)) atTop (𝓝 (quadCLM V₀ Y₀ P₀ + Q P₀)) := by
  obtain ⟨C, hC⟩ := hY.bounded
  have hsmall : Tendsto (fun h => quadCLM V₀ (Y h) (P h - P₀)) atTop (𝓝 0) := by
    have hd : Tendsto (fun h => ‖P h - P₀‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hP
    refine squeeze_zero_norm (fun h => ?_) (by simpa using hd.mul_const (Fintype.card ι * C))
    rw [Real.norm_eq_abs]
    refine (abs_quadCLM_le (hY.memLp h) _).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC h) (Nat.cast_nonneg _))
      (norm_nonneg _)
  have hsum := hsmall.add (hQ P₀)
  rw [zero_add] at hsum
  refine hsum.congr fun h => ?_
  rw [← map_add, sub_add_cancel]

/-- **Comparison on admissible directions**: if the differences `Y_h - Y` take values a.e. in the
admissible sets `S x` and `qf (P x) z ≤ qf (P' x) z` on `S x`, then `𝖰(P) ≤ 𝖰(P')`. -/
theorem IsDefect.le_of_qf_le (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    {S : K → Set (ι → ℝ)} (hS : ∀ h, ∀ᵐ x ∂V₀, (fun i => Y h i x - Y₀ i x) ∈ S x)
    {P P' : C(K, ι → ι → ℝ)} (hPP : ∀ x, ∀ z ∈ S x, qf (P x) z ≤ qf (P' x) z) :
    Q P ≤ Q P' := by
  have hd : ∀ h i, MemLp (fun x => Y h i x - Y₀ i x) 2 V₀ := fun h i =>
    (hY.memLp h i).sub (hY.memLp_lim i)
  refine le_of_tendsto_of_tendsto' (hQ.tendsto_sub hY P) (hQ.tendsto_sub hY P') fun h => ?_
  refine integral_mono_ae (integrable_qf P (hd h)) (integrable_qf P' (hd h)) ?_
  filter_upwards [hS h] with x hx
  exact hPP x _ hx

/-- Positivity on admissible directions: `qf (P x) ≥ 0` on `S x` gives `𝖰(P) ≥ 0`. -/
theorem IsDefect.nonneg (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    {S : K → Set (ι → ℝ)} (hS : ∀ h, ∀ᵐ x ∂V₀, (fun i => Y h i x - Y₀ i x) ∈ S x)
    {P : C(K, ι → ι → ℝ)} (hP : ∀ x, ∀ z ∈ S x, 0 ≤ qf (P x) z) : 0 ≤ Q P := by
  have := hQ.le_of_qf_le hY hS (P := 0) (P' := P) fun x z hz => by
    simpa [qf_zero_left] using hP x z hz
  simpa using this

/-! ### Contractions with coefficient fields and the trace measure -/

/-- The coefficient field `x ↦ φ(x) B(x)`. -/
def smulCoef (φ : C(K, ℝ)) (B : C(K, ι → ι → ℝ)) : C(K, ι → ι → ℝ) :=
  ⟨fun x => φ x • B x, φ.continuous.smul B.continuous⟩

theorem smulCoef_apply (φ : C(K, ℝ)) (B : C(K, ι → ι → ℝ)) (x : K) :
    smulCoef φ B x = φ x • B x := rfl

theorem norm_smulCoef_le (φ : C(K, ℝ)) (B : C(K, ι → ι → ℝ)) :
    ‖smulCoef φ B‖ ≤ ‖φ‖ * ‖B‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  rw [smulCoef_apply, norm_smul]
  exact mul_le_mul (φ.norm_coe_le_norm x) (B.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)

/-- `φ ↦ φ B` as a continuous linear map. -/
noncomputable def smulCoefCLM (B : C(K, ι → ι → ℝ)) : C(K, ℝ) →L[ℝ] C(K, ι → ι → ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun φ => smulCoef φ B
      map_add' := fun φ ψ => by ext x i j; simp [smulCoef_apply, add_mul]
      map_smul' := fun c φ => by ext x i j; simp [smulCoef_apply, mul_assoc] }
    ‖B‖ fun φ => by rw [mul_comm]; exact norm_smulCoef_le φ B

theorem smulCoefCLM_apply (B : C(K, ι → ι → ℝ)) (φ : C(K, ℝ)) :
    smulCoefCLM B φ = smulCoef φ B := rfl

/-- The scalar measure `B : 𝖰`, `φ ↦ 𝖰(φ B)` (contraction of a matrix measure with a continuous
coefficient field). -/
noncomputable def contract (Q : StrongDual ℝ C(K, ι → ι → ℝ)) (B : C(K, ι → ι → ℝ)) :
    StrongDual ℝ C(K, ℝ) :=
  Q.comp (smulCoefCLM B)

theorem contract_apply (Q : StrongDual ℝ C(K, ι → ι → ℝ)) (B : C(K, ι → ι → ℝ)) (φ : C(K, ℝ)) :
    contract Q B φ = Q (smulCoef φ B) := rfl

theorem quadCLM_smulCoef {Y : ι → K → ℝ} (hY : ∀ i, MemLp (Y i) 2 V₀) (φ : C(K, ℝ))
    (B : C(K, ι → ι → ℝ)) :
    quadCLM V₀ Y (smulCoef φ B) = ∫ x, φ x * qf (B x) (fun i => Y i x) ∂V₀ := by
  rw [quadCLM_apply hY]
  simp only [smulCoef_apply, qf_smul_left]

theorem tendsto_smulCoef (φ : C(K, ℝ)) {B : ℕ → C(K, ι → ι → ℝ)} {B₀ : C(K, ι → ι → ℝ)}
    (hB : Tendsto B atTop (𝓝 B₀)) :
    Tendsto (fun h => smulCoef φ (B h)) atTop (𝓝 (smulCoef φ B₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hB ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun h => ?_) (by simpa using hB.const_mul ‖φ‖)
  have e : smulCoef φ (B h) - smulCoef φ B₀ = smulCoef φ (B h - B₀) := by
    ext x i j; simp [smulCoef_apply, mul_sub]
  rw [e]
  exact norm_smulCoef_le φ _

/-- **Contracted defect, `eq:defect-contraction`**: for coefficient fields `B_h → B` uniformly,
`qf (B_h) (Y_h) dV₀ ⇀* qf (B) (Y) dV₀ + B : 𝖰`. -/
theorem IsDefect.tendsto_contract (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    {B : ℕ → C(K, ι → ι → ℝ)} {B₀ : C(K, ι → ι → ℝ)} (hB : Tendsto B atTop (𝓝 B₀))
    (φ : C(K, ℝ)) :
    Tendsto (fun h => ∫ x, φ x * qf (B h x) (fun i => Y h i x) ∂V₀) atTop
      (𝓝 (∫ x, φ x * qf (B₀ x) (fun i => Y₀ i x) ∂V₀ + contract Q B₀ φ)) := by
  have := hQ.tendsto_coef hY (tendsto_smulCoef φ hB)
  rw [quadCLM_smulCoef hY.memLp_lim] at this
  refine this.congr fun h => ?_
  rw [quadCLM_smulCoef (hY.memLp h)]

variable [DecidableEq ι]

/-- The constant identity coefficient field. -/
def idField : C(K, ι → ι → ℝ) := ContinuousMap.const K idCoef

/-- The trace measure `μ = tr 𝖰 : φ ↦ 𝖰(φ I)`. -/
noncomputable def traceMeasure (Q : StrongDual ℝ C(K, ι → ι → ℝ)) : StrongDual ℝ C(K, ℝ) :=
  contract Q idField

/-- `|Y_h|² dV₀ ⇀* |Y|² dV₀ + μ_Y` with `μ_Y = tr 𝖰`. -/
theorem IsDefect.tendsto_trace (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q) (φ : C(K, ℝ)) :
    Tendsto (fun h => ∫ x, φ x * ∑ i, Y h i x ^ 2 ∂V₀) atTop
      (𝓝 (∫ x, φ x * ∑ i, Y₀ i x ^ 2 ∂V₀ + traceMeasure Q φ)) := by
  have := hQ.tendsto_contract hY (tendsto_const_nhds (x := (idField : C(K, ι → ι → ℝ)))) φ
  simpa only [traceMeasure, idField, ContinuousMap.const_apply, qf_idCoef] using this

/-- `μ_Y = lim ∫ φ |Y_h - Y|² dV₀`. -/
theorem IsDefect.tendsto_trace_sub (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    (φ : C(K, ℝ)) :
    Tendsto (fun h => ∫ x, φ x * ∑ i, (Y h i x - Y₀ i x) ^ 2 ∂V₀) atTop
      (𝓝 (traceMeasure Q φ)) := by
  have := hQ.tendsto_sub hY (smulCoef φ idField)
  simpa only [traceMeasure, contract_apply, smulCoef_apply, qf_smul_left, idField,
    ContinuousMap.const_apply, qf_idCoef] using this

/-- `μ_Y = tr 𝖰_Y ≥ 0`. -/
theorem IsDefect.traceMeasure_nonneg (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    {φ : C(K, ℝ)} (hφ : ∀ x, 0 ≤ φ x) : 0 ≤ traceMeasure Q φ := by
  refine hQ.nonneg hY (S := fun _ => univ) (fun h => Eventually.of_forall fun x => mem_univ _)
    fun x z _ => ?_
  change 0 ≤ qf (smulCoef φ idField x) z
  rw [smulCoef_apply, qf_smul_left, idField, ContinuousMap.const_apply, qf_idCoef]
  exact mul_nonneg (hφ x) (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- Domination `|B : 𝖰| ≤ ‖B‖ · card ι · μ_Y` on nonnegative test functions. -/
theorem IsDefect.abs_contract_le (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    (B : C(K, ι → ι → ℝ)) {φ : C(K, ℝ)} (hφ : ∀ x, 0 ≤ φ x) :
    |contract Q B φ| ≤ ‖B‖ * Fintype.card ι * traceMeasure Q φ := by
  set c := ‖B‖ * (Fintype.card ι : ℝ)
  have hpt : ∀ (x : K) (z : ι → ℝ), |qf (B x) z| ≤ c * ∑ i, z i ^ 2 := by
    intro x z; rw [mul_assoc]; exact abs_qf_apply_le B z x
  have hT : traceMeasure Q φ * c = Q (smulCoef φ (c • idField)) := by
    rw [traceMeasure, contract_apply, mul_comm, ← smul_eq_mul, ← map_smul]
    congr 1
    ext x i j
    simp [smulCoef_apply, idField]
    ring
  have hqT : ∀ (x : K) (z : ι → ℝ), qf (smulCoef φ (c • idField) x) z = φ x * (c * ∑ i, z i ^ 2) := by
    intro x z
    rw [smulCoef_apply, qf_smul_left, ContinuousMap.smul_apply, qf_smul_left, idField,
      ContinuousMap.const_apply, qf_idCoef]
  have hqB : ∀ (x : K) (z : ι → ℝ), qf (smulCoef φ B x) z = φ x * qf (B x) z := by
    intro x z; rw [smulCoef_apply, qf_smul_left]
  have h1 := hQ.nonneg hY (S := fun _ => univ) (fun h => Eventually.of_forall fun x =>
    mem_univ _) (P := smulCoef φ (c • idField) - smulCoef φ B) fun x z _ => by
      rw [ContinuousMap.sub_apply, qf_sub_left, hqT, hqB]
      have := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hpt x z)) (hφ x)
      linarith
  have h2 := hQ.nonneg hY (S := fun _ => univ) (fun h => Eventually.of_forall fun x =>
    mem_univ _) (P := smulCoef φ (c • idField) + smulCoef φ B) fun x z _ => by
      rw [ContinuousMap.add_apply, qf_add_left, hqT, hqB]
      have := mul_le_mul_of_nonneg_left ((neg_le_abs (qf (B x) z)).trans (hpt x z)) (hφ x)
      linarith
  rw [map_sub] at h1
  rw [map_add] at h2
  rw [contract_apply, abs_le]
  constructor <;> linarith

/-- Strong convergence of the packet kills the defect. -/
theorem IsDefect.eq_zero_of_strongL2 (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    (hs : StrongL2 V₀ Y Y₀) : Q = 0 := by
  have hd : ∀ h i, MemLp (fun x => Y h i x - Y₀ i x) 2 V₀ := fun h i =>
    (hY.memLp h i).sub (hY.memLp_lim i)
  ext P
  have hE : Tendsto (fun h => energy V₀ (fun i x => Y h i x - Y₀ i x)) atTop (𝓝 0) := by
    simpa [energy] using tendsto_finsetSum _ fun i _ => hs i
  have hlim := hQ.tendsto_sub hY P
  have h0 : Tendsto (fun h => ∫ x, qf (P x) (fun i => Y h i x - Y₀ i x) ∂V₀) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun h => ?_) (by simpa using hE.const_mul (‖P‖ * Fintype.card ι))
    rw [Real.norm_eq_abs, mul_assoc]
    exact abs_integral_qf_le P (hd h)
  simpa using tendsto_nhds_unique hlim h0

/-- A vanishing trace measure forces strong convergence. -/
theorem IsDefect.strongL2_of_traceMeasure (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    (h0 : traceMeasure Q 1 = 0) : StrongL2 V₀ Y Y₀ := by
  have hd : ∀ h i, MemLp (fun x => Y h i x - Y₀ i x) 2 V₀ := fun h i =>
    (hY.memLp h i).sub (hY.memLp_lim i)
  have hlim := hQ.tendsto_trace_sub hY 1
  rw [h0] at hlim
  simp only [ContinuousMap.one_apply, one_mul] at hlim
  have hE : Tendsto (fun h => ∑ i, ∫ x, (Y h i x - Y₀ i x) ^ 2 ∂V₀) atTop (𝓝 0) := by
    refine hlim.congr fun h => ?_
    exact integral_finsetSum _ fun i _ => (hd h i).integrable_sq
  intro i
  refine squeeze_zero (fun h => integral_nonneg fun x => sq_nonneg _) (fun h => ?_) hE
  exact Finset.single_le_sum (f := fun i => ∫ x, (Y h i x - Y₀ i x) ^ 2 ∂V₀)
    (fun j _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ i)

/-- `eq:positive-defect-equivalence`: `𝖰 = 0 ↔ Y_h → Y` in `L²`. -/
theorem IsDefect.eq_zero_iff_strongL2 (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q) :
    Q = 0 ↔ StrongL2 V₀ Y Y₀ :=
  ⟨fun h0 => hQ.strongL2_of_traceMeasure hY (by rw [traceMeasure, contract_apply, h0]; rfl),
    hQ.eq_zero_of_strongL2 hY⟩

/-- `eq:positive-defect-equivalence`: `μ_Y = 0 ↔ Y_h → Y` in `L²`. -/
theorem IsDefect.traceMeasure_eq_zero_iff_strongL2 (hY : WeakL2 V₀ Y Y₀)
    (hQ : IsDefect V₀ Y Y₀ Q) : traceMeasure Q = 0 ↔ StrongL2 V₀ Y Y₀ :=
  ⟨fun h0 => hQ.strongL2_of_traceMeasure hY (by rw [h0]; rfl), fun hs => by
    rw [hQ.eq_zero_of_strongL2 hY hs]; rfl⟩
end Packets
end QuadraticPacketDefect

end RenewalGeometry
