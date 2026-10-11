/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.QuadraticPacketDefect
import RenewalGeometry.Analysis.LpDualityWeakCompactness
import RenewalGeometry.Continuum.EinsteinSMCertificatePacket

/-!
# `L¹` densities of quadratic defect measures under uniform integrability

Generic measure theory for the `L¹`-density clause of `thm:critical-quotient-defect`
("if, in addition, `|D_{A_h}H_h|²` and `|H_h|⁴` are uniformly integrable, then the complete bosonic
defect is an `L¹` tensor density").

**`exists_density_of_truncation`**: on a compact space `K` with a finite measure `μ`, let a packet
`Y_n : ι → K → ℝ` be bounded in `L²` and *uniformly truncatable* in `L²`
(`sup_n ‖Y_{n,i} - T_m Y_{n,i}‖_2 → 0` as `m → ∞`, `T_m` the clamp at level `m`; this is the
uniform integrability of `|Y_n|²`).  If the matrix measures `Y_n ⊗ Y_n dμ` converge weak-* to a
functional `Λ` on `C(K, ℝ^{ι×ι})`, then `Λ` has an `L¹` density: `Λ(P) = ∫ Σ P_{ij} ρ_{ij} dμ`.
Proof (Dunford–Pettis by truncation): the truncated products `T_m Y_i · T_m Y_j` are bounded,
hence weakly compact in `L²` (`LpDuality.exists_subseq_tendsto_weak_family`); a diagonal
extraction over `m` gives limits `ρ^m`; uniform truncatability makes `ρ^m` Cauchy in `L¹`
(tested against the sign of `ρ^m - ρ^{m'}`) and `|Λ(P) - ∫ P : ρ^m| ≤ C ‖P‖ ε_m`; the `L¹` limit
`ρ` represents `Λ`.

**`uniformTruncation_of_unifIntegrable`**: Mathlib's `UnifIntegrable … 2` plus an `L²` bound
gives the uniform truncation.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.CriticalQuotientDensity

open QuadraticPacketDefect

set_option linter.unusedSectionVars false

/-! ### The clamp -/

/-- The clamp `T_m t = max (-m) (min m t)`. -/
def clampR (m t : ℝ) : ℝ := max (-m) (min m t)

theorem continuous_clampR (m : ℝ) : Continuous (clampR m) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_clampR_le {m : ℝ} (hm : 0 ≤ m) (t : ℝ) : |clampR m t| ≤ m := by
  unfold clampR
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem abs_clampR_le_abs {m : ℝ} (hm : 0 ≤ m) (t : ℝ) : |clampR m t| ≤ |t| := by
  unfold clampR
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_le]
    constructor
    · exact (neg_nonpos.2 ht).trans (by
        rw [le_max_iff]; right; exact le_min hm ht) |>.trans' (by linarith)
    · exact max_le (by linarith) (min_le_right _ _)
  · rw [abs_of_nonpos ht, abs_le]
    constructor
    · rw [neg_neg]; exact le_max_of_le_right (le_min (by linarith) le_rfl)
    · exact max_le (by linarith) ((min_le_right _ _).trans (by linarith))

theorem abs_sub_clampR_mono {m m' : ℝ} (hm : 0 ≤ m) (hmm : m ≤ m') (t : ℝ) :
    |t - clampR m' t| ≤ |t - clampR m t| := by
  unfold clampR
  rcases le_total t (-m') with h1 | h1
  · rw [max_eq_left (by rw [min_le_iff]; right; exact h1),
      max_eq_left (by rw [min_le_iff]; right; linarith)]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  rcases le_total t m' with h2 | h2
  · rw [min_eq_right h2, max_eq_right h1, sub_self, abs_zero]
    exact abs_nonneg _
  · rw [min_eq_left h2, max_eq_right (by linarith), min_eq_left (by linarith),
      max_eq_right (by linarith)]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

theorem abs_sub_clampR_le_abs {m : ℝ} (hm : 0 ≤ m) (t : ℝ) : |t - clampR m t| ≤ |t| := by
  have := abs_sub_clampR_mono (le_refl (0 : ℝ)) hm t
  simpa [clampR] using this

/-! ### `L²` products -/

section Products

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integral_abs_mul_le {a b : α → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun x => a x * b x) μ ∧
      ∫ x, |a x * b x| ∂μ ≤ (eLpNorm a 2 μ).toReal * (eLpNorm b 2 μ).toReal := by
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have h1 : MemLp (a • b) 1 μ := hb.smul ha
  have hi : Integrable (fun x => a x * b x) μ := memLp_one_iff_integrable.1 h1
  refine ⟨hi, ?_⟩
  calc ∫ x, |a x * b x| ∂μ = ∫ x, ‖(a • b) x‖ ∂μ := rfl
    _ = (eLpNorm (a • b) 1 μ).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm h1.1]
    _ ≤ (eLpNorm a 2 μ * eLpNorm b 2 μ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ha.eLpNorm_ne_top hb.eLpNorm_ne_top)
          (eLpNorm_smul_le_mul_eLpNorm hb.1 ha.1)
    _ = _ := ENNReal.toReal_mul

/-- `‖a b - a' b'‖₁ ≤ ‖a - a'‖₂ ‖b‖₂ + ‖a'‖₂ ‖b - b'‖₂`. -/
theorem integral_abs_mul_sub_le {a b a' b' : α → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (ha' : MemLp a' 2 μ) (hb' : MemLp b' 2 μ) :
    ∫ x, |a x * b x - a' x * b' x| ∂μ ≤
      (eLpNorm (a - a') 2 μ).toReal * (eLpNorm b 2 μ).toReal +
        (eLpNorm a' 2 μ).toReal * (eLpNorm (b - b') 2 μ).toReal := by
  obtain ⟨i1, e1⟩ := integral_abs_mul_le (ha.sub ha') hb
  obtain ⟨i2, e2⟩ := integral_abs_mul_le ha' (hb.sub hb')
  calc ∫ x, |a x * b x - a' x * b' x| ∂μ ≤
        ∫ x, (|(a - a') x * b x| + |a' x * (b - b') x|) ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
          (i1.abs.add i2.abs) (Eventually.of_forall fun x => ?_)
        simp only [Pi.sub_apply]
        calc |a x * b x - a' x * b' x| = |(a x - a' x) * b x + a' x * (b x - b' x)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
    _ = ∫ x, |(a - a') x * b x| ∂μ + ∫ x, |a' x * (b - b') x| ∂μ := integral_add i1.abs i2.abs
    _ ≤ _ := add_le_add e1 e2

end Products


/-! ### Truncated products and their diagonal weak limits -/

section Truncation

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
variable {ι : Type*} [Fintype ι]

/-- The truncated product `T_m Y_i · T_m Y_j`. -/
def trProd (Y : ι → α → ℝ) (m : ℕ) (k : ι × ι) (x : α) : ℝ :=
  clampR m (Y k.1 x) * clampR m (Y k.2 x)

theorem aesm_clamp {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (m : ℝ) :
    AEStronglyMeasurable (fun x => clampR m (f x)) μ :=
  (continuous_clampR m).comp_aestronglyMeasurable hf

theorem memLp_clamp {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (m : ℕ) (p : ℝ≥0∞) :
    MemLp (fun x => clampR m (f x)) p μ :=
  MemLp.of_bound (aesm_clamp hf m) m (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact abs_clampR_le (Nat.cast_nonneg m) _)

theorem eLpNorm_clamp_le {f : α → ℝ} (m : ℕ) (p : ℝ≥0∞) :
    eLpNorm (fun x => clampR m (f x)) p μ ≤ eLpNorm f p μ :=
  eLpNorm_mono fun x => by
    simp only [Real.norm_eq_abs]; exact abs_clampR_le_abs (Nat.cast_nonneg m) _

theorem memLp_trProd {Y : ι → α → ℝ} (hY : ∀ i, AEStronglyMeasurable (Y i) μ) (m : ℕ)
    (k : ι × ι) : MemLp (trProd Y m k) 2 μ ∧
      eLpNorm (trProd Y m k) 2 μ ≤ μ univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (m * m) := by
  have hm : AEStronglyMeasurable (trProd Y m k) μ :=
    (aesm_clamp (hY k.1) m).mul (aesm_clamp (hY k.2) m)
  have hb : ∀ x, ‖trProd Y m k x‖ ≤ m * m := fun x => by
    rw [Real.norm_eq_abs, trProd, abs_mul]
    exact mul_le_mul (abs_clampR_le (Nat.cast_nonneg m) _) (abs_clampR_le (Nat.cast_nonneg m) _)
      (abs_nonneg _) (Nat.cast_nonneg m)
  exact ⟨MemLp.of_bound hm _ (Eventually.of_forall hb),
    eLpNorm_le_of_ae_bound (Eventually.of_forall hb)⟩

end Truncation

section Diagonal

variable {α : Type*} [MeasurableSpace α] [MeasurableSpace.CountablyGenerated α] {μ : Measure α}
  [IsFiniteMeasure μ]
variable {ι : Type*} [Fintype ι]

/-- **Diagonal weak extraction of all truncated products.** -/
theorem exists_diag_trProd (Y : ℕ → ι → α → ℝ) (hY : ∀ n i, AEStronglyMeasurable (Y n i) μ) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ ∃ g : ℕ → ι × ι → α → ℝ, ∀ m k, MemLp (g m k) 2 μ ∧
      ∀ h : α → ℝ, MemLp h 2 μ → Tendsto (fun n => ∫ x, h x * trProd (Y (D n)) m k x ∂μ)
        atTop (𝓝 (∫ x, h x * g m k x ∂μ)) := by
  set WP : ℕ → (ℕ → ℕ) → Prop := fun m s => ∃ g : ι × ι → α → ℝ, ∀ k, MemLp (g k) 2 μ ∧
    ∀ h : α → ℝ, MemLp h 2 μ → Tendsto (fun n => ∫ x, h x * trProd (Y (s n)) m k x ∂μ)
      atTop (𝓝 (∫ x, h x * g k x ∂μ))
  have hex : ∀ m (s : ℕ → ℕ), StrictMono s → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ WP m (s ∘ ψ) := by
    intro m s _
    obtain ⟨φ, hφ, g, hg⟩ := LpDuality.exists_subseq_tendsto_weak_family (μ := μ) (p := 2)
      (q := 2) (by norm_num) (by norm_num) (fun k n => trProd (Y (s n)) m k)
      (fun k n => (memLp_trProd (hY (s n)) m k).1)
      (B := μ univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (m * m))
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _))
        ENNReal.ofReal_ne_top)
      (fun k n => (memLp_trProd (hY (s n)) m k).2)
    exact ⟨φ, hφ, g, hg⟩
  have hcomp : ∀ m (s ψ : ℕ → ℕ), StrictMono ψ → WP m s → WP m (s ∘ ψ) := by
    intro m s ψ hψ h
    obtain ⟨g, hg⟩ := h
    exact ⟨g, fun k => ⟨(hg k).1, fun h hh => ((hg k).2 h hh).comp hψ.tendsto_atTop⟩⟩
  have htail : ∀ m (s : ℕ → ℕ) (k : ℕ), StrictMono s → WP m (fun j => s (j + k)) → WP m s := by
    intro m s k _ h
    obtain ⟨g, hg⟩ := h
    exact ⟨g, fun k' => ⟨(hg k').1, fun h hh => (tendsto_add_atTop_iff_nat k).1 ((hg k').2 h hh)⟩⟩
  obtain ⟨D, hD, hall⟩ := EinsteinSM.exists_diagonal_subseq WP hex hcomp htail
  choose g hg using hall
  exact ⟨D, hD, g, hg⟩

end Diagonal


/-! ### Uniform truncatability and the truncation estimates -/

section Estimates

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
variable {ι : Type*} [Fintype ι]

/-- **Uniform `L²` truncatability** of a packet: `sup_{n,i} ‖Y_{n,i} - T_m Y_{n,i}‖_2 → 0`
(uniform integrability of `|Y_n|²`). -/
def UnifTrunc (μ : Measure α) (Y : ℕ → ι → α → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ n i,
    eLpNorm (fun x => Y n i x - clampR m (Y n i x)) 2 μ ≤ ENNReal.ofReal ε

theorem UnifTrunc.mono {Y : ℕ → ι → α → ℝ} (h : UnifTrunc μ Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ n i,
      eLpNorm (fun x => Y n i x - clampR m (Y n i x)) 2 μ ≤ ENNReal.ofReal ε := by
  obtain ⟨m₀, hm₀⟩ := h ε hε
  exact ⟨m₀, fun m hm n i => (eLpNorm_mono fun x => by
    simp only [Real.norm_eq_abs]
    exact abs_sub_clampR_mono (Nat.cast_nonneg _) (Nat.cast_le.2 hm) _).trans (hm₀ n i)⟩

/-- `‖Y_i Y_j - T_m Y_i T_m Y_j‖₁ ≤ 2 C ε`. -/
theorem integral_abs_sub_trProd_le {Y : ι → α → ℝ} (hY : ∀ i, MemLp (Y i) 2 μ) {Cb ε : ℝ}
    (hCb : 0 ≤ Cb) (hε0 : 0 ≤ ε) (hC : ∀ i, eLpNorm (Y i) 2 μ ≤ ENNReal.ofReal Cb) {m : ℕ}
    (hε : ∀ i, eLpNorm (fun x => Y i x - clampR m (Y i x)) 2 μ ≤ ENNReal.ofReal ε)
    (k : ι × ι) :
    ∫ x, |Y k.1 x * Y k.2 x - trProd Y m k x| ∂μ ≤ 2 * Cb * ε := by
  have hc : ∀ i, MemLp (fun x => clampR m (Y i x)) 2 μ := fun i => memLp_clamp (hY i).1 m 2
  have h := integral_abs_mul_sub_le (hY k.1) (hY k.2) (hc k.1) (hc k.2)
  have t1 : (eLpNorm (Y k.1 - fun x => clampR m (Y k.1 x)) 2 μ).toReal ≤ ε :=
    ENNReal.toReal_le_of_le_ofReal hε0 (hε k.1)
  have t2 : (eLpNorm (Y k.2 - fun x => clampR m (Y k.2 x)) 2 μ).toReal ≤ ε :=
    ENNReal.toReal_le_of_le_ofReal hε0 (hε k.2)
  have t3 : (eLpNorm (Y k.2) 2 μ).toReal ≤ Cb := ENNReal.toReal_le_of_le_ofReal hCb (hC k.2)
  have t4 : (eLpNorm (fun x => clampR m (Y k.1 x)) 2 μ).toReal ≤ Cb :=
    ENNReal.toReal_le_of_le_ofReal hCb ((eLpNorm_clamp_le m 2).trans (hC k.1))
  calc _ ≤ _ := h
    _ ≤ ε * Cb + Cb * ε := add_le_add
        (mul_le_mul t1 t3 ENNReal.toReal_nonneg hε0)
        (mul_le_mul t4 t2 ENNReal.toReal_nonneg hCb)
    _ = 2 * Cb * ε := by ring

/-- `|∫ t f| ≤ B ∫ |f|` for `|t| ≤ B`. -/
theorem abs_integral_bdd_mul_le {t f : α → ℝ} (ht : AEStronglyMeasurable t μ) {B : ℝ}
    (hB : ∀ x, |t x| ≤ B) (hf : Integrable f μ) :
    |∫ x, t x * f x ∂μ| ≤ B * ∫ x, |f x| ∂μ := by
  have hi : Integrable (fun x => t x * f x) μ :=
    hf.bdd_mul ht (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  calc |∫ x, t x * f x ∂μ| ≤ ∫ x, |t x * f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, B * |f x| ∂μ := integral_mono hi.abs (hf.abs.const_mul B) fun x => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
    _ = B * ∫ x, |f x| ∂μ := integral_const_mul _ _

end Estimates

/-! ### The density representation -/

section Representation

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] [MeasurableSpace.CountablyGenerated K] {μ : Measure K}
  [IsFiniteMeasure μ]
variable {ι : Type*} [Fintype ι]

theorem abs_entry_le (P : C(K, ι → ι → ℝ)) (x : K) (i j : ι) : |P x i j| ≤ ‖P‖ := by
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm (P x i) j).trans ((norm_le_pi_norm (P x) i).trans (P.norm_coe_le_norm x))

theorem aesm_entry (P : C(K, ι → ι → ℝ)) (i j : ι) :
    AEStronglyMeasurable (fun x => P x i j) μ :=
  ((continuous_apply j).comp ((continuous_apply i).comp P.continuous)).aestronglyMeasurable

theorem memLp_entry (P : C(K, ι → ι → ℝ)) (i j : ι) (p : ℝ≥0∞) :
    MemLp (fun x => P x i j) p μ :=
  MemLp.of_bound (aesm_entry P i j) ‖P‖ (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact abs_entry_le P x i j)

/-- **`L¹` limit of an `L¹`-Cauchy sequence.** -/
theorem exists_L1_limit {g : ℕ → K → ℝ} (hg : ∀ m, Integrable (g m) μ)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ m' ≥ m₀, ∫ x, |g m x - g m' x| ∂μ ≤ ε) :
    ∃ ρ : K → ℝ, Integrable ρ μ ∧
      Tendsto (fun m => ∫ x, |g m x - ρ x| ∂μ) atTop (𝓝 0) := by
  set G : ℕ → Lp ℝ 1 μ := fun m => (memLp_one_iff_integrable.2 (hg m)).toLp (g m)
  have hdist : ∀ m m', dist (G m) (G m') = ∫ x, |g m x - g m' x| ∂μ := by
    intro m m'
    rw [dist_eq_norm, L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (G m) (G m'), (memLp_one_iff_integrable.2 (hg m)).coeFn_toLp,
      (memLp_one_iff_integrable.2 (hg m')).coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Real.norm_eq_abs]
  have hcs : CauchySeq G := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨m₀, hm₀⟩ := hc (ε / 2) (by positivity)
    refine ⟨m₀, fun m hm => ?_⟩
    rw [hdist]
    exact (hm₀ m hm m₀ le_rfl).trans_lt (by linarith)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨L, L1.integrable_coeFn L, ?_⟩
  have hn := (tendsto_iff_norm_sub_tendsto_zero.1 hL)
  refine hn.congr fun m => ?_
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (G m) L, (memLp_one_iff_integrable.2 (hg m)).coeFn_toLp]
    with x h1 h2
  rw [h1, Pi.sub_apply, h2, Real.norm_eq_abs]

end Representation


/-! ### The `L¹` density theorem -/

section DensityTheorem

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] [MeasurableSpace.CountablyGenerated K] {μ : Measure K}
  [IsFiniteMeasure μ]
variable {ι : Type*} [Fintype ι]

/-- The quadratic pairing as a double sum of integrals. -/
theorem integral_qf_eq_sum {Y : ι → K → ℝ} (hY : ∀ i, MemLp (Y i) 2 μ) (P : C(K, ι → ι → ℝ)) :
    ∫ x, qf (P x) (fun i => Y i x) ∂μ = ∑ i, ∑ j, ∫ x, P x i j * (Y i x * Y j x) ∂μ := by
  have hi : ∀ i j, Integrable (fun x => P x i j * (Y i x * Y j x)) μ := fun i j =>
    (integral_abs_mul_le (hY i) (hY j)).1.bdd_mul (aesm_entry P i j)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_entry_le P x i j)
  simp only [qf]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hi i j]
  exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ fun j _ => hi i j

/-- **Approximation of the limit functional by the truncated limits.** -/
theorem abs_sub_trunc_le {Y : ℕ → ι → K → ℝ} (hYm : ∀ n i, MemLp (Y n i) 2 μ) {Cb : ℝ}
    (hCb : 0 ≤ Cb) (hC : ∀ n i, eLpNorm (Y n i) 2 μ ≤ ENNReal.ofReal Cb)
    {Λ : StrongDual ℝ C(K, ι → ι → ℝ)} {D : ℕ → ℕ} (hD : StrictMono D)
    (hΛ : ∀ P, Tendsto (fun n => ∫ x, qf (P x) (fun i => Y n i x) ∂μ) atTop (𝓝 (Λ P)))
    {m : ℕ} {g : ι × ι → K → ℝ}
    (hg : ∀ k (h : K → ℝ), MemLp h 2 μ → Tendsto (fun n => ∫ x, h x * trProd (Y (D n)) m k x ∂μ)
      atTop (𝓝 (∫ x, h x * g k x ∂μ)))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ n i, eLpNorm (fun x => Y n i x - clampR m (Y n i x)) 2 μ ≤ ENNReal.ofReal ε)
    (P : C(K, ι → ι → ℝ)) :
    |Λ P - ∑ i, ∑ j, ∫ x, P x i j * g (i, j) x ∂μ| ≤
      Fintype.card ι * Fintype.card ι * (‖P‖ * (2 * Cb * ε)) := by
  have ha := (hΛ P).comp hD.tendsto_atTop
  have hb : Tendsto (fun n => ∑ i, ∑ j, ∫ x, P x i j * trProd (Y (D n)) m (i, j) x ∂μ) atTop
      (𝓝 (∑ i, ∑ j, ∫ x, P x i j * g (i, j) x ∂μ)) :=
    tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
      hg (i, j) _ (memLp_entry P i j 2)
  refine le_of_tendsto ((ha.sub hb).abs) (Eventually.of_forall fun n => ?_)
  simp only [Function.comp_apply]
  rw [integral_qf_eq_sum (hYm (D n)) P, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hrow : ∀ i, |∑ j, ∫ x, P x i j * (Y (D n) i x * Y (D n) j x) ∂μ -
      ∑ j, ∫ x, P x i j * trProd (Y (D n)) m (i, j) x ∂μ| ≤
        Fintype.card ι * (‖P‖ * (2 * Cb * ε)) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j, |∫ x, P x i j * (Y (D n) i x * Y (D n) j x) ∂μ -
        ∫ x, P x i j * trProd (Y (D n)) m (i, j) x ∂μ| ≤ ‖P‖ * (2 * Cb * ε) := by
      intro j
      have i1 : Integrable (fun x => Y (D n) i x * Y (D n) j x - trProd (Y (D n)) m (i, j) x) μ :=
        (integral_abs_mul_le (hYm (D n) i) (hYm (D n) j)).1.sub
          ((memLp_trProd (fun i => (hYm (D n) i).1) m (i, j)).1.integrable one_le_two)
      have i2 : Integrable (fun x => Y (D n) i x * Y (D n) j x) μ :=
        (integral_abs_mul_le (hYm (D n) i) (hYm (D n) j)).1
      have i3 : Integrable (fun x => trProd (Y (D n)) m (i, j) x) μ :=
        (memLp_trProd (fun i => (hYm (D n) i).1) m (i, j)).1.integrable one_le_two
      rw [← integral_sub (i2.bdd_mul (aesm_entry P i j) (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact abs_entry_le P x i j))
        (i3.bdd_mul (aesm_entry P i j) (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact abs_entry_le P x i j))]
      have e : (fun x => P x i j * (Y (D n) i x * Y (D n) j x) -
          P x i j * trProd (Y (D n)) m (i, j) x) = fun x => P x i j *
            (Y (D n) i x * Y (D n) j x - trProd (Y (D n)) m (i, j) x) := by
        funext x; ring
      rw [e]
      refine (abs_integral_bdd_mul_le (aesm_entry P i j) (abs_entry_le P · i j) i1).trans ?_
      exact mul_le_mul_of_nonneg_left (integral_abs_sub_trProd_le (hYm (D n)) hCb hε0
        (hC (D n)) (hε (D n)) (i, j)) (norm_nonneg _)
    calc ∑ j, _ ≤ ∑ _j : ι, ‖P‖ * (2 * Cb * ε) := Finset.sum_le_sum fun j _ => hterm j
      _ = _ := by simp
  calc ∑ i, _ ≤ ∑ _i : ι, (Fintype.card ι : ℝ) * (‖P‖ * (2 * Cb * ε)) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp [mul_assoc]

/-- **`L¹` Cauchy estimate of the truncated limits.** -/
theorem integral_abs_sub_trunc_le {Y : ℕ → ι → K → ℝ} (hYm : ∀ n i, MemLp (Y n i) 2 μ) {Cb : ℝ}
    (hCb : 0 ≤ Cb) (hC : ∀ n i, eLpNorm (Y n i) 2 μ ≤ ENNReal.ofReal Cb) {D : ℕ → ℕ}
    {m m' : ℕ} {g g' : K → ℝ} {k : ι × ι} (hgm : MemLp g 2 μ) (hgm' : MemLp g' 2 μ)
    (hg : ∀ h : K → ℝ, MemLp h 2 μ → Tendsto (fun n => ∫ x, h x * trProd (Y (D n)) m k x ∂μ)
      atTop (𝓝 (∫ x, h x * g x ∂μ)))
    (hg' : ∀ h : K → ℝ, MemLp h 2 μ → Tendsto (fun n => ∫ x, h x * trProd (Y (D n)) m' k x ∂μ)
      atTop (𝓝 (∫ x, h x * g' x ∂μ)))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ n i, eLpNorm (fun x => Y n i x - clampR m (Y n i x)) 2 μ ≤ ENNReal.ofReal ε)
    (hε' : ∀ n i, eLpNorm (fun x => Y n i x - clampR m' (Y n i x)) 2 μ ≤ ENNReal.ofReal ε) :
    ∫ x, |g x - g' x| ∂μ ≤ 4 * Cb * ε := by
  have hd : MemLp (fun x => g x - g' x) 2 μ := hgm.sub hgm'
  set d' := hd.1.mk _
  have hdd : (fun x => g x - g' x) =ᵐ[μ] d' := hd.1.ae_eq_mk
  have hd'm : StronglyMeasurable d' := hd.1.stronglyMeasurable_mk
  set t : K → ℝ := fun x => if 0 ≤ d' x then 1 else -1
  have htm : Measurable t := Measurable.ite (measurableSet_le measurable_const hd'm.measurable)
    measurable_const measurable_const
  have htb : ∀ x, |t x| ≤ 1 := fun x => by simp only [t]; split_ifs <;> simp
  have ht2 : MemLp t 2 μ := MemLp.of_bound htm.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact htb x)
  have e1 : ∫ x, |g x - g' x| ∂μ = ∫ x, t x * g x ∂μ - ∫ x, t x * g' x ∂μ := by
    have ig : ∀ f : K → ℝ, MemLp f 2 μ → Integrable (fun x => t x * f x) μ := fun f hf =>
      (hf.integrable one_le_two).bdd_mul htm.aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact htb x)
    rw [← integral_sub (ig g hgm) (ig g' hgm')]
    refine integral_congr_ae (hdd.mono fun x hx => ?_)
    simp only at hx
    simp only [t, ← mul_sub, hx]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.1 h)]; ring
  rw [e1]
  have hlim := (hg t ht2).sub (hg' t ht2)
  refine le_of_tendsto' hlim fun n => ?_
  have iY : Integrable (fun x => Y (D n) k.1 x * Y (D n) k.2 x) μ :=
    (integral_abs_mul_le (hYm (D n) k.1) (hYm (D n) k.2)).1
  have iT : ∀ m'' : ℕ, Integrable (trProd (Y (D n)) m'' k) μ := fun m'' =>
    (memLp_trProd (fun i => (hYm (D n) i).1) m'' k).1.integrable one_le_two
  have igt : ∀ m'' : ℕ, Integrable (fun x => t x * trProd (Y (D n)) m'' k x) μ := fun m'' =>
    (iT m'').bdd_mul htm.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact htb x)
  rw [← integral_sub (igt m) (igt m')]
  have e2 : (fun x => t x * trProd (Y (D n)) m k x - t x * trProd (Y (D n)) m' k x) =
      fun x => t x * (trProd (Y (D n)) m k x - trProd (Y (D n)) m' k x) := by
    funext x; ring
  rw [e2]
  refine (le_abs_self _).trans ((abs_integral_bdd_mul_le htm.aestronglyMeasurable htb
    ((iT m).sub (iT m'))).trans ?_)
  rw [one_mul]
  calc ∫ x, |trProd (Y (D n)) m k x - trProd (Y (D n)) m' k x| ∂μ ≤
        ∫ x, (|Y (D n) k.1 x * Y (D n) k.2 x - trProd (Y (D n)) m k x| +
          |Y (D n) k.1 x * Y (D n) k.2 x - trProd (Y (D n)) m' k x|) ∂μ := by
        refine integral_mono ((iT m).sub (iT m')).abs ((iY.sub (iT m)).abs.add (iY.sub (iT m')).abs)
          fun x => ?_
        exact (abs_sub_le (trProd (Y (D n)) m k x) (Y (D n) k.1 x * Y (D n) k.2 x)
          (trProd (Y (D n)) m' k x)).trans_eq (by
            rw [abs_sub_comm (trProd (Y (D n)) m k x) (Y (D n) k.1 x * Y (D n) k.2 x)])
    _ = ∫ x, |Y (D n) k.1 x * Y (D n) k.2 x - trProd (Y (D n)) m k x| ∂μ +
          ∫ x, |Y (D n) k.1 x * Y (D n) k.2 x - trProd (Y (D n)) m' k x| ∂μ :=
        integral_add (iY.sub (iT m)).abs (iY.sub (iT m')).abs
    _ ≤ 2 * Cb * ε + 2 * Cb * ε := add_le_add
        (integral_abs_sub_trProd_le (hYm (D n)) hCb hε0 (hC (D n)) (hε (D n)) k)
        (integral_abs_sub_trProd_le (hYm (D n)) hCb hε0 (hC (D n)) (hε' (D n)) k)
    _ = 4 * Cb * ε := by ring

end DensityTheorem


section DensityMain

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] [MeasurableSpace.CountablyGenerated K] {μ : Measure K}
  [IsFiniteMeasure μ]
variable {ι : Type*} [Fintype ι]

/-- **`L¹` density of a weak-* limit of quadratic packets under uniform truncatability**
(Dunford–Pettis by truncation): if `Y_n` is bounded and uniformly truncatable in `L²` and
`Y_n ⊗ Y_n dμ ⇀* Λ`, then `Λ(P) = ∫ Σ P_{ij} ρ_{ij} dμ` for integrable `ρ_{ij}`. -/
theorem exists_density_of_truncation {Y : ℕ → ι → K → ℝ} (hYm : ∀ n i, MemLp (Y n i) 2 μ)
    {Cb : ℝ} (hCb : 0 ≤ Cb) (hC : ∀ n i, eLpNorm (Y n i) 2 μ ≤ ENNReal.ofReal Cb)
    (hT : UnifTrunc μ Y) {Λ : StrongDual ℝ C(K, ι → ι → ℝ)}
    (hΛ : ∀ P, Tendsto (fun n => ∫ x, qf (P x) (fun i => Y n i x) ∂μ) atTop (𝓝 (Λ P))) :
    ∃ ρ : ι → ι → K → ℝ, (∀ i j, Integrable (ρ i j) μ) ∧
      ∀ P, Λ P = ∫ x, ∑ i, ∑ j, P x i j * ρ i j x ∂μ := by
  obtain ⟨D, hD, g, hg⟩ := exists_diag_trProd Y (fun n i => (hYm n i).1)
  have hcau : ∀ k, ∀ ε : ℝ, 0 < ε → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ m' ≥ m₀,
      ∫ x, |g m k x - g m' k x| ∂μ ≤ ε := by
    intro k ε hε
    obtain ⟨m₀, hm₀⟩ := hT.mono (show 0 < ε / (4 * Cb + 1) by positivity)
    refine ⟨m₀, fun m hm m' hm' => ?_⟩
    refine (integral_abs_sub_trunc_le hYm hCb hC (D := D) (hg m k).1 (hg m' k).1 (hg m k).2
      (hg m' k).2 (by positivity) (hm₀ m hm) (hm₀ m' hm')).trans ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  choose ρ hρi hρt using fun k =>
    exists_L1_limit (fun m => (hg m k).1.integrable one_le_two) (hcau k)
  refine ⟨fun i j => ρ (i, j), fun i j => hρi _, fun P => ?_⟩
  set c : ℕ → ℝ := fun m => ∑ i, ∑ j, ∫ x, P x i j * g m (i, j) x ∂μ
  have hbd : ∀ i j, ∀ᵐ x ∂μ, ‖P x i j‖ ≤ ‖P‖ := fun i j =>
    Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_entry_le P x i j
  have h1 : Tendsto c atTop (𝓝 (∑ i, ∑ j, ∫ x, P x i j * ρ (i, j) x ∂μ)) := by
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim := (hρt (i, j)).const_mul ‖P‖
    rw [mul_zero] at hlim
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hlim
    have i1 := ((hg m (i, j)).1.integrable one_le_two).bdd_mul (aesm_entry P i j) (hbd i j)
    have i2 := (hρi (i, j)).bdd_mul (aesm_entry P i j) (hbd i j)
    rw [← integral_sub i1 i2, Real.norm_eq_abs]
    have e : (fun x => P x i j * g m (i, j) x - P x i j * ρ (i, j) x) =
        fun x => P x i j * (g m (i, j) x - ρ (i, j) x) := by funext x; ring
    rw [e]
    exact abs_integral_bdd_mul_le (aesm_entry P i j) (abs_entry_le P · i j)
      (((hg m (i, j)).1.integrable one_le_two).sub (hρi (i, j)))
  have h2 : Tendsto c atTop (𝓝 (Λ P)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set X : ℝ := (Fintype.card ι : ℝ) * Fintype.card ι * ‖P‖ * (2 * Cb)
    have hX : 0 ≤ X := by positivity
    obtain ⟨m₀, hm₀⟩ := hT.mono (show 0 < ε / (2 * (X + 1)) by positivity)
    refine ⟨m₀, fun m hm => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    have := abs_sub_trunc_le hYm hCb hC hD hΛ (fun k => (hg m k).2) (by positivity)
      (hm₀ m hm) P
    refine this.trans_lt ?_
    have e : (Fintype.card ι : ℝ) * Fintype.card ι * (‖P‖ * (2 * Cb * (ε / (2 * (X + 1))))) =
        X * ε / (2 * (X + 1)) := by simp only [X]; ring
    rw [e, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [tendsto_nhds_unique h2 h1]
  have hi : ∀ i j, Integrable (fun x => P x i j * ρ (i, j) x) μ := fun i j =>
    (hρi (i, j)).bdd_mul (aesm_entry P i j) (hbd i j)
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hi i j]
  exact Finset.sum_congr rfl fun i _ => (integral_finset_sum _ fun j _ => hi i j).symm

end DensityMain

/-! ### Uniform truncatability from uniform integrability -/

section FromUI

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
variable {ι : Type*} [Fintype ι]

/-- **Uniform integrability of `|Y_n|²` (Mathlib's `UnifIntegrable … 2`) with an `L²` bound gives
uniform truncatability.** -/
theorem unifTrunc_of_unifIntegrable {Y : ℕ → ι → α → ℝ}
    (hm : ∀ n i, AEStronglyMeasurable (Y n i) μ) (hUI : ∀ i, UnifIntegrable (fun n => Y n i) 2 μ)
    {Cb : ℝ} (hC : ∀ n i, eLpNorm (Y n i) 2 μ ≤ ENNReal.ofReal Cb) : UnifTrunc μ Y := by
  intro ε hε
  have hU : ∀ i, UniformIntegrable (fun n => Y n i) 2 μ := fun i =>
    ⟨fun n => hm n i, hUI i, ⟨Cb.toNNReal, fun n => by
      rw [ENNReal.ofReal] at hC; exact hC n i⟩⟩
  choose C hC' using fun i => (hU i).spec two_ne_zero ENNReal.ofNat_ne_top hε
  obtain ⟨m, hmC⟩ : ∃ m : ℕ, ∀ i, (C i : ℝ) ≤ m := by
    obtain ⟨m, hm⟩ := exists_nat_ge (∑ i, (C i : ℝ))
    exact ⟨m, fun i => (Finset.single_le_sum (f := fun i => (C i : ℝ)) (fun _ _ => NNReal.coe_nonneg _)
      (Finset.mem_univ i)).trans hm⟩
  refine ⟨m, fun n i => (eLpNorm_mono fun x => ?_).trans (hC' i n)⟩
  simp only [Real.norm_eq_abs]
  by_cases hx : C i ≤ ‖Y n i x‖₊
  · rw [indicator_of_mem (show x ∈ {x | C i ≤ ‖Y n i x‖₊} from hx)]
    exact abs_sub_clampR_le_abs (Nat.cast_nonneg m) _
  · rw [indicator_of_notMem (show x ∉ {x | C i ≤ ‖Y n i x‖₊} from hx), abs_zero]
    have hlt : |Y n i x| < m := by
      have : ‖Y n i x‖₊ < C i := not_le.1 hx
      have h' : (‖Y n i x‖₊ : ℝ) < C i := by exact_mod_cast this
      rw [coe_nnnorm, Real.norm_eq_abs] at h'
      exact h'.trans_le (hmC i)
    have hcl : clampR m (Y n i x) = Y n i x := by
      unfold clampR
      rw [abs_lt] at hlt
      rw [min_eq_right hlt.2.le, max_eq_right hlt.1.le]
    rw [hcl, sub_self, abs_zero]

end FromUI

end RenewalGeometry.CriticalQuotientDensity
