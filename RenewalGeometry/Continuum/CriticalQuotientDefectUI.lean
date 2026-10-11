/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientDefectClosed
import RenewalGeometry.Continuum.CriticalQuotientDensity

/-!
# `thm:critical-quotient-defect`: the `L¹`-density and quartic clauses

"If, in addition, `|D_{A_h}H_h|²` and `|H_h|⁴` are uniformly integrable, then the complete bosonic
defect is an `L¹` tensor density and the quartic concentration measure vanishes."

* `isDefect_density`: a covariance measure of a uniformly truncatable packet has an `L¹` density.
* `unifIntegrable_of_dom`, `unifIntegrable_comp_val`, `unifIntegrable_curv`: uniform integrability
  passes to dominated families, to the closed cube, and follows from `def:critical-curvature-ui`.
* `quartic_defect_eq_zero`: uniform `L⁴`-integrability of the Higgs field (Vitali) makes the
  quartic packet converge strongly, so its covariance measure (the quartic concentration
  measure) vanishes.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.CriticalQuotientRows

open SobolevOpen CriticalGauge CriticalQuotient CriticalQuotientClosure
  BallAnalysis.SMGaugeStructure SMGaugeLie EinsteinSM SMGaugeJet FirstVariationCalculus
  QuadraticPacketDefect BosonicStressDefectBox CurvatureCovariance CriticalQuotientDensity

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ### Uniform integrability: domination, reindexing, transfer -/

section UI

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Domination**: a family dominated pointwise by `c Σ_k |f_{n,k}|` with `f` uniformly integrable
is uniformly integrable. -/
theorem unifIntegrable_of_dom {κ : Type*} [Fintype κ] {F G : Type*} [NormedAddCommGroup F]
    [NormedAddCommGroup G] {f : ℕ × κ → X → F} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : UnifIntegrable f p μ) (hfm : ∀ q, AEStronglyMeasurable (f q) μ) {g : ℕ → X → G}
    {c : ℝ} (hc : 0 ≤ c) (hdom : ∀ n, ∀ᵐ x ∂μ, ‖g n x‖ ≤ c * ∑ k, ‖f (n, k) x‖) :
    UnifIntegrable g p μ := by
  intro ε hε
  set ε' := ε / ((c + 1) * (Fintype.card κ + 1))
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ, hδ, h⟩ := hf hε'
  refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
  have hpt : ∀ᵐ x ∂μ, ‖s.indicator (g n) x‖ ≤ c * ‖∑ k, ‖s.indicator (f (n, k)) x‖‖ := by
    filter_upwards [hdom n] with x hx
    by_cases hxs : x ∈ s
    · simp only [indicator_of_mem hxs]
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
      exact hx
    · simp only [indicator_of_notMem hxs, norm_zero, Finset.sum_const_zero, mul_zero, le_refl]
  calc eLpNorm (s.indicator (g n)) p μ ≤
        ENNReal.ofReal c * eLpNorm (fun x => ∑ k, ‖s.indicator (f (n, k)) x‖) p μ :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt p
    _ = ENNReal.ofReal c * eLpNorm (∑ k, fun x => ‖s.indicator (f (n, k)) x‖) p μ := by
        congr 2; funext x; simp
    _ ≤ ENNReal.ofReal c * ∑ k, eLpNorm (fun x => ‖s.indicator (f (n, k)) x‖) p μ := by
        gcongr
        exact eLpNorm_sum_le (fun k _ => ((hfm (n, k)).indicator hs).norm) hp
    _ = ENNReal.ofReal c * ∑ k, eLpNorm (s.indicator (f (n, k))) p μ := by
        simp only [eLpNorm_norm]
    _ ≤ ENNReal.ofReal c * ∑ _k : κ, ENNReal.ofReal ε' := by
        gcongr with k
        exact h (n, k) s hs hμs
    _ = ENNReal.ofReal (c * (Fintype.card κ * ε')) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hc]
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hk : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
        have e : c * (Fintype.card κ * ε') = ε * (c * Fintype.card κ) /
            ((c + 1) * (Fintype.card κ + 1)) := by
          simp only [ε']; ring
        rw [e, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hc hk, hε.le]

/-- Reindexing a uniformly integrable family along a map of indices. -/
theorem unifIntegrable_reindex {ι ι' F : Type*} [NormedAddCommGroup F] {f : ι → X → F}
    {p : ℝ≥0∞} (hf : UnifIntegrable f p μ) (e : ι' → ι) :
    UnifIntegrable (fun i => f (e i)) p μ := fun ε hε =>
  let ⟨δ, hδ, h⟩ := hf hε
  ⟨δ, hδ, fun i => h (e i)⟩

end UI

section Transfer

variable {lo hi : E4}

/-- Uniform integrability on the open box transfers to the closed cube with `V0`. -/
theorem unifIntegrable_comp_val {F : Type*} [NormedAddCommGroup F] {g : ℕ → E4 → F}
    {p : ℝ≥0∞} (hg : UnifIntegrable g p (volume.restrict (box lo hi))) :
    UnifIntegrable (fun n => g n ∘ Subtype.val) p (V0 lo hi) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hg hε
  refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
  have himg : MeasurableSet (Subtype.val '' s : Set E4) := (emb lo hi).measurableSet_image.2 hs
  have hV : V0 lo hi s = (volume.restrict (box lo hi)) (Subtype.val '' s) :=
    (emb lo hi).comap_apply _ s
  have hind : s.indicator (g n ∘ Subtype.val) = ((Subtype.val '' s).indicator (g n)) ∘
      Subtype.val := by
    funext y
    by_cases hy : y ∈ s
    · rw [indicator_of_mem hy]
      show g n y.val = (Subtype.val '' s).indicator (g n) y.val
      rw [indicator_of_mem (mem_image_of_mem _ hy)]
    · rw [indicator_of_notMem hy]
      show (0 : F) = (Subtype.val '' s).indicator (g n) y.val
      rw [indicator_of_notMem]
      exact fun ⟨y', hy', he⟩ => hy (Subtype.val_injective he ▸ hy')
  rw [hind, eLpNorm_comp (emb lo hi) (map_V0 lo hi)]
  exact h n _ himg (hV ▸ hμs)

end Transfer

section CurvUI

variable {a b : E4}

/-- **`def:critical-curvature-ui` gives uniform `L²`-integrability of `|F_{A_h}|`.** -/
theorem unifIntegrable_curv {A : ℕ → MConn 5}
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x)) :
    UnifIntegrable (fun h x => ‖curvVec (A h) x‖) 2 (volume.restrict (box a b)) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := (criticalCurvatureUI_iff _ _ _).1 hUI (ENNReal.ofReal (ε ^ 2))
    (ENNReal.ofReal_pos.2 (by positivity))
  refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
  have hQm : MeasurableSet (box a b) := (isOpen_box a b).measurableSet
  rw [Measure.restrict_apply hs] at hμs
  have hE := h n (s ∩ box a b) (hs.inter hQm) inter_subset_right hμs
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs, Measure.restrict_restrict hs,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [enorm_norm, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc (∫⁻ x in s ∩ box a b, ‖curvVec (A n) x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
        (ENNReal.ofReal (ε ^ 2)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hE (by norm_num)
    _ = ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hε.le]

end CurvUI

/-! ### `L¹` density of a covariance measure -/

section Density

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace.CountablyGenerated K] {V₀ : Measure K} [IsFiniteMeasure V₀]
variable {ι : Type*} [Fintype ι]

/-- A weakly convergent packet is bounded in `L²`. -/
theorem weakL2_exists_eLpNorm_le {Y : ℕ → ι → K → ℝ} {Y₀ : ι → K → ℝ} (hY : WeakL2 V₀ Y Y₀) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ n i, eLpNorm (Y n i) 2 V₀ ≤ ENNReal.ofReal Cb := by
  obtain ⟨C, hC⟩ := hY.bounded
  refine ⟨Real.sqrt (max C 0), Real.sqrt_nonneg _, fun n i => ?_⟩
  rw [(hY.memLp n i).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [ENNReal.toReal_ofNat]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  refine Real.sqrt_le_sqrt ?_
  have hi : ∫ x, ‖Y n i x‖ ^ (2 : ℝ) ∂V₀ = ∫ x, Y n i x ^ 2 ∂V₀ := by
    congr 1; funext x; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hi]
  calc ∫ x, Y n i x ^ 2 ∂V₀ ≤ energy V₀ (Y n) :=
        Finset.single_le_sum (f := fun i => ∫ x, Y n i x ^ 2 ∂V₀)
          (fun j _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ i)
    _ ≤ C := hC n
    _ ≤ max C 0 := le_max_left _ _

/-- **`L¹` density of a covariance measure** of a uniformly truncatable weakly convergent packet:
`𝖰(P) = ∫ Σ P_{ij} ρ_{ij} dV₀` with integrable `ρ_{ij}`. -/
theorem isDefect_density {Y : ℕ → ι → K → ℝ} {Y₀ : ι → K → ℝ}
    {Q : StrongDual ℝ C(K, ι → ι → ℝ)} (hY : WeakL2 V₀ Y Y₀) (hQ : IsDefect V₀ Y Y₀ Q)
    (hT : UnifTrunc V₀ Y) :
    ∃ ρ : ι → ι → K → ℝ, (∀ i j, Integrable (ρ i j) V₀) ∧
      ∀ P, Q P = ∫ x, ∑ i, ∑ j, P x i j * ρ i j x ∂V₀ := by
  obtain ⟨Cb, hCb, hC⟩ := weakL2_exists_eLpNorm_le hY
  obtain ⟨ρ', hρ'i, hρ'⟩ := exists_density_of_truncation (μ := V₀) (hY.memLp) hCb hC hT
    (Λ := quadCLM V₀ Y₀ + Q) fun P => by
      have := hQ P
      simp only [quadCLM_apply (hY.memLp _)] at this
      simpa using this
  have hYY : ∀ i j, Integrable (fun x => Y₀ i x * Y₀ j x) V₀ := fun i j =>
    (integral_abs_mul_le (hY.memLp_lim i) (hY.memLp_lim j)).1
  refine ⟨fun i j x => ρ' i j x - Y₀ i x * Y₀ j x, fun i j => (hρ'i i j).sub (hYY i j),
    fun P => ?_⟩
  have hb : ∀ i j, ∀ᵐ x ∂V₀, ‖P x i j‖ ≤ ‖P‖ := fun i j =>
    Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_entry_le P x i j
  have i1 : Integrable (fun x => ∑ i, ∑ j, P x i j * ρ' i j x) V₀ :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      (hρ'i i j).bdd_mul (aesm_entry P i j) (hb i j)
  have i2 : Integrable (fun x => ∑ i, ∑ j, P x i j * (Y₀ i x * Y₀ j x)) V₀ :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      (hYY i j).bdd_mul (aesm_entry P i j) (hb i j)
  have hΛ := hρ' P
  rw [ContinuousLinearMap.add_apply, quadCLM_apply hY.memLp_lim] at hΛ
  have e : ∫ x, ∑ i, ∑ j, P x i j * (ρ' i j x - Y₀ i x * Y₀ j x) ∂V₀ =
      ∫ x, ∑ i, ∑ j, P x i j * ρ' i j x ∂V₀ -
        ∫ x, ∑ i, ∑ j, P x i j * (Y₀ i x * Y₀ j x) ∂V₀ := by
    rw [← integral_sub i1 i2]
    congr 1; funext x
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [e, ← hΛ]
  simp only [qf]
  ring

end Density


/-! ### The packets on a Coulomb cube under uniform integrability -/

section CubeUI

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Domination by a single uniformly integrable family. -/
theorem unifIntegrable_of_dom_single {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {f : ℕ → X → F} {p : ℝ≥0∞} (hf : UnifIntegrable f p μ) {g : ℕ → X → G} {c : ℝ}
    (hc : 0 ≤ c) (hdom : ∀ n, ∀ᵐ x ∂μ, ‖g n x‖ ≤ c * ‖f n x‖) : UnifIntegrable g p μ := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf (show 0 < ε / (c + 1) by positivity)
  refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
  have hpt : ∀ᵐ x ∂μ, ‖s.indicator (g n) x‖ ≤ c * ‖s.indicator (f n) x‖ := by
    filter_upwards [hdom n] with x hx
    by_cases hxs : x ∈ s
    · simp only [indicator_of_mem hxs]; exact hx
    · simp only [indicator_of_notMem hxs, norm_zero, mul_zero, le_refl]
  calc eLpNorm (s.indicator (g n)) p μ ≤ ENNReal.ofReal c * eLpNorm (s.indicator (f n)) p μ :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt p
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (ε / (c + 1)) := by gcongr; exact h n s hs hμs
    _ = ENNReal.ofReal (c * (ε / (c + 1))) := (ENNReal.ofReal_mul hc).symm
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

variable {lo hi : E4}

/-- Pointwise bound of the transported curvature by the gauge-invariant `|F|`. -/
theorem norm_redJet_F_le {R : E4 → M5} {z : FieldTuple (Fin 5)} {x : E4} (hR : GaugeAt R x)
    (hA : DifferentiableAt ℝ z.A x) :
    ‖(redJet (gaugeTuple R z) x).F‖ ≤ ‖curvVec (connM z.A) x‖ := by
  rw [← norm_curvVec_gaugeConn hR.unitary hR.c2 (mdiffAt_connM hA)]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ν =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun e => ?_
  rw [redJet_gaugeTuple_F hR hA μ ν c e]
  have := PiLp.norm_apply_le (curvVec (gaugeConn R (connM z.A)) x) (μ, ν, c, e)
  simpa [curvVec] using this

/-- Pointwise bound of the transported covariant Higgs gradient. -/
theorem norm_redJet_K_le {R : E4 → M5} {z : FieldTuple (Fin 5)} {x : E4} (hR : GaugeAt R x)
    (hz : DiffAt z x) (hlie : ∀ μ, z.A x μ ∈ smLie) :
    ‖(redJet (gaugeTuple R z) x).K‖ ≤
      ∑ k : Fin 4 × Fin 5, ‖covDerV (connM z.A) (matterSec z none) k.1 x k.2‖ := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun μ =>
    (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun i => ?_
  have hK2 : (redJet (gaugeTuple R z) x).K μ = higgsG (R x) (covDerivHiggs z.A z.H x μ) :=
    covDerivHiggs_gaugeTuple hR hz.H μ
  have hproj : covDerivHiggs z.A z.H x μ = projH (covDerV (connM z.A) (matterSec z none) μ x) := by
    rw [covDerV_matterSec_higgs hlie hz.H, projH_embH]
  rw [hK2, hproj]
  refine (norm_higgsG_apply_le hR.unitary.self_of_nhds _ i).trans ?_
  simp only [projH]
  calc ∑ j : Fin 2, ‖covDerV (connM z.A) (matterSec z none) μ x (Fin.natAdd 3 j)‖ ≤
        ∑ e, ‖covDerV (connM z.A) (matterSec z none) μ x e‖ := by
        rw [sum_fin5 (fun e => ‖covDerV (connM z.A) (matterSec z none) μ x e‖)]
        exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ ≤ ∑ k : Fin 4 × Fin 5, ‖covDerV (connM z.A) (matterSec z none) k.1 x k.2‖ := by
        rw [Fintype.sum_prod_type]
        exact Finset.single_le_sum (f := fun μ' => ∑ e,
          ‖covDerV (connM z.A) (matterSec z none) μ' x e‖) (fun _ _ =>
            Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ μ)

/-- **Uniform integrability of the curvature packet on the closed cube.** -/
theorem unifIntegrable_F_packet {z : ℕ → FieldTuple (Fin 5)} {R : ℕ → E4 → M5}
    (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x) (hzA : ∀ n x, DifferentiableAt ℝ (z n).A x)
    (hUI : UnifIntegrable (fun n x => ‖curvVec (connM (z n).A) x‖) 2
      (volume.restrict (box lo hi))) (i : PIdx (Fin 4 → ConnFibre)) :
    UnifIntegrable (fun n => pk lo hi (fun x => (redJet (gaugeTuple (R n) (z n)) x).F) i) 2
      (V0 lo hi) := by
  have hQm : MeasurableSet (box lo hi) := (isOpen_box lo hi).measurableSet
  refine unifIntegrable_comp_val (g := fun n x => coordL i ((redJet (gaugeTuple (R n) (z n)) x).F))
    (unifIntegrable_of_dom_single hUI (norm_nonneg (coordL i)) fun n => ?_)
  refine (ae_restrict_iff' hQm).2 (Eventually.of_forall fun x hx => ?_)
  refine ((coordL i).le_opNorm _).trans ?_
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left (norm_redJet_F_le (hR n x hx) (hzA n x)) (norm_nonneg _)

/-- **Uniform integrability of the covariant-Higgs-gradient packet on the closed cube.** -/
theorem unifIntegrable_K_packet {z : ℕ → FieldTuple (Fin 5)} {R : ℕ → E4 → M5}
    (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x) (hz : ∀ n x, DiffAt (z n) x)
    (hlie : ∀ n x μ, (z n).A x μ ∈ smLie)
    (hm : ∀ n (k : Fin 4 × Fin 5), AEStronglyMeasurable
      (fun y => covDerV (connM (z n).A) (matterSec (z n) none) k.1 y k.2)
      (volume.restrict (box lo hi)))
    (hUI : UnifIntegrable (fun p : ℕ × (Fin 4 × Fin 5) => fun y =>
      covDerV (connM (z p.1).A) (matterSec (z p.1) none) p.2.1 y p.2.2) 2
      (volume.restrict (box lo hi))) (i : PIdx (Fin 4 → HiggsFibre)) :
    UnifIntegrable (fun n => pk lo hi (fun x => (redJet (gaugeTuple (R n) (z n)) x).K) i) 2
      (V0 lo hi) := by
  have hQm : MeasurableSet (box lo hi) := (isOpen_box lo hi).measurableSet
  refine unifIntegrable_comp_val (g := fun n x => coordL i ((redJet (gaugeTuple (R n) (z n)) x).K))
    (unifIntegrable_of_dom (κ := Fin 4 × Fin 5) one_le_two hUI (fun q => hm q.1 q.2)
      (norm_nonneg (coordL i)) fun n => ?_)
  refine (ae_restrict_iff' hQm).2 (Eventually.of_forall fun x hx => ?_)
  refine ((coordL i).le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_redJet_K_le (hR n x hx) (hz n x) (hlie n x))
    (norm_nonneg _)

end CubeUI


/-! ### Vanishing of the quartic concentration measure -/

section Quartic

variable {lo hi : E4}

theorem tendsto_integral_sq_of_lpTendsto {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : ℕ → X → ℝ} {f₀ : X → ℝ} (h : RenewalGeometry.LpTendsto ν 2 f f₀) :
    Tendsto (fun n => ∫ x, (f n x - f₀ x) ^ 2 ∂ν) atTop (𝓝 0) := by
  have e : ∀ n, ∫ x, (f n x - f₀ x) ^ 2 ∂ν = ((eLpNorm (f n - f₀) 2 ν).toReal) ^ 2 := by
    intro n
    rw [((h.memLp n).sub h.memLp_lim).eLpNorm_eq_integral_rpow_norm two_ne_zero
      ENNReal.ofNat_ne_top, ENNReal.toReal_ofReal (by positivity)]
    simp only [ENNReal.toReal_ofNat]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sq_sqrt
      (integral_nonneg fun x => by positivity)]
    congr 1; funext x
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs, Pi.sub_apply]
  simp only [e]
  have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h.tendsto).pow 2
  simpa using this

set_option maxHeartbeats 1000000 in
/-- **The quartic concentration measure vanishes** when the Higgs fields are uniformly
`L⁴`-integrable (`|H_h|⁴` uniformly integrable): Vitali upgrades the transported Higgs fields to
strong `L⁴` convergence, the quartic packet `|H_h|² - v_h²` converges strongly in `L²`, and its
covariance measure is zero (`eq:positive-defect-equivalence`). -/
theorem quartic_defect_eq_zero (hlh : ∀ i, lo i < hi i) {z : ℕ → FieldTuple (Fin 5)}
    {R : ℕ → E4 → M5} (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x)
    (hzH : ∀ n, ContDiff ℝ ∞ (z n).H)
    (hWu : ∀ n s c, MemW12 (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c))
    {uinf : MIdx → Fin 5 → E4 → ℂ} {Gu : MIdx → Fin 5 → Fin 4 → E4 → ℂ}
    (q5 : ∀ s c, MemW12 (box lo hi) (uinf s c) (Gu s c))
    (q6 : ∀ s c, Tendsto (fun n => eLpNorm (transp (R n) (matterSec (z n) s) c - uinf s c) 2
      (volume.restrict (box lo hi))) atTop (𝓝 0))
    (hUIH : UnifIntegrable (fun p : ℕ × Fin 5 => fun y => matterSec (z p.1) none y p.2) 4
      (volume.restrict (box lo hi)))
    {Ysec : Type} {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hv : Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH))
    {L : LimitFields (Fin 5)} (hLH : ∀ x i, (limitJet L x).H i = uinf none (Fin.natAdd 3 i) x)
    {QY : StrongDual ℝ C(Icc lo hi, PIdx ℝ → PIdx ℝ → ℝ)}
    (w3 : WeakL2 (V0 lo hi)
      (fun n => pk lo hi (fun x => quartY (θ n) (redJet (gaugeTuple (R n) (z n)) x)))
      (pk lo hi (fun x => quartY θ₀ (limitJet L x))))
    (dY : IsDefect (V0 lo hi)
      (fun n => pk lo hi (fun x => quartY (θ n) (redJet (gaugeTuple (R n) (z n)) x)))
      (pk lo hi (fun x => quartY θ₀ (limitJet L x))) QY) : QY = 0 := by
  set μQ := volume.restrict (box lo hi)
  have : IsFiniteMeasure μQ := isFiniteMeasure_restrict.mpr (volume_box_ne_top lo hi)
  have hQm : MeasurableSet (box lo hi) := (isOpen_box lo hi).measurableSet
  -- Vitali: strong `L⁴` convergence of the transported Higgs components
  have hmeas : ∀ n e, AEStronglyMeasurable (fun y => matterSec (z n) none y e) μQ := fun n e =>
    ((continuous_apply e).comp ((embHL.contDiff.comp (hzH n)).continuous)).aestronglyMeasurable
  have hT4 : ∀ c, RenewalGeometry.LpTendsto μQ 4 (fun n => transp (R n) (matterSec (z n) none) c)
      (uinf none c) := fun c =>
    ⟨fun n => memLp_four_of_memW12_box hlh (hWu n none c), memLp_four_of_memW12_box hlh (q5 none c),
      tendsto_L4_of_L2_of_unifIntegrable hlh (fun n => (hWu n none c).memLp.1) (q5 none c)
        (q6 none c) (unifIntegrable_transp hQm (fun n y hy => (hR n y hy).unitary.self_of_nhds)
          hmeas hUIH c)⟩
  have hH4 : RenewalGeometry.LpTendsto μQ 4 (fun n x => (redJet (gaugeTuple (R n) (z n)) x).H)
      (fun x => (limitJet L x).H) := by
    refine lpTendsto_pi (by norm_num) fun i => ?_
    refine (hT4 (Fin.natAdd 3 i)).congr (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (hLH x i).symm)
    show transp (R n) (matterSec (z n) none) (Fin.natAdd 3 i) x = (gaugeTuple (R n) (z n)).H x i
    rw [gaugeTuple_H_eq]; rfl
  haveI : ENNReal.HolderTriple 4 4 2 := FirstVariationCalculus.holderTriple_four_four_two
  have hq := RenewalGeometry.LpTendsto.bilin (p := 4) (q := 4) (r := 2)
    (hInnerReL : HiggsFibre →L[ℝ] HiggsFibre →L[ℝ] ℝ) hH4 hH4
  have hc := FirstVariationCalculus.LpTendsto.const_seq (μ := μQ) (p := 2) (hv.pow 2)
  have hY : RenewalGeometry.LpTendsto μQ 2
      (fun n x => quartY (θ n) (redJet (gaugeTuple (R n) (z n)) x))
      (fun x => quartY θ₀ (limitJet L x)) := (hq.sub hc).congr
    (fun n => Eventually.of_forall fun x => rfl) (Eventually.of_forall fun x => rfl)
  refine dY.eq_zero_of_strongL2 w3 ?_
  refine (strongL2_comp_iff (emb lo hi) (map_V0 lo hi)
    (Y := fun n i x => coordL i (quartY (θ n) (redJet (gaugeTuple (R n) (z n)) x)))
    (Y₀ := fun i x => coordL i (quartY θ₀ (limitJet L x)))).2 fun i => ?_
  exact tendsto_integral_sq_of_lpTendsto (FirstVariationCalculus.LpTendsto.clm_comp
    (by norm_num) (coordL i) hY)

end Quartic


/-! ### The cube conclusions with the `L¹`-density and quartic clauses -/

section CubeAllUI

variable {lo hi a b : E4}

set_option maxHeartbeats 2000000 in
/-- **All conclusions on one Coulomb cube, with the `L¹`-density clause**: in addition to
`cube_all`, the curvature covariance measure has an `L¹` density (uniform integrability of
`|F|²`, `def:critical-curvature-ui`); under uniform integrability of `|D_AH|²` the Higgs-kinetic
covariance measure has an `L¹` density; under uniform `L⁴`-integrability of `H` the quartic
concentration measure vanishes. -/
theorem cube_all_UI {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    (hlh : ∀ i, lo i < hi i) (hQK : box lo hi ⊆ box a b) {z : ℕ → FieldTuple (Fin 5)}
    {R : ℕ → E4 → M5}
    (hzA : ∀ n, ContDiff ℝ ∞ (z n).A) (hzH : ∀ n, ContDiff ℝ ∞ (z n).H)
    (hze : ∀ n, ContDiff ℝ ∞ (z n).e) (hz : ∀ n x, DiffAt (z n) x)
    (hlie : ∀ n x μ, (z n).A x μ ∈ smLie) (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x)
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL)
    (heK : ∀ n, ∀ x ∈ box a b, (z n).e x ∈ Ke)
    {e₀ : E4 → CoframeFibre} {de₀ : Fin 4 → Fin 4 → Fin 4 → E4 → ℝ}
    (he₀ : ∀ i ν, MemLp (fun y => e₀ y i ν) ⊤ (volume.restrict (box a b)))
    (hde₀ : ∀ i ν μ, MemLp (de₀ i ν μ) 2 (volume.restrict (box a b)))
    (hLinf : ∀ i ν, Tendsto (fun k => eLpNorm (fun y => (z k).e y i ν - e₀ y i ν) ⊤
      (volume.restrict (box a b))) atTop (𝓝 0))
    (hL2 : ∀ i ν, Tendsto (fun k => eLpNorm (fun y => (z k).e y i ν - e₀ y i ν) 2
      (volume.restrict (box a b))) atTop (𝓝 0))
    (hd : ∀ i ν μ, Tendsto (fun k => eLpNorm (fun y => pd (fun y => (z k).e y i ν) μ y -
      de₀ i ν μ y) 2 (volume.restrict (box a b))) atTop (𝓝 0))
    (hWA : ∀ n ν c e, MemW12 (box lo hi) (entries (gaugeConn (R n) (connM (z n).A)) ν c e)
      (entryGrad (gaugeConn (R n) (connM (z n).A)) ν c e))
    (hWu : ∀ n s c, MemW12 (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c))
    {Bu : ℝ≥0∞} (hBu : Bu ≠ ⊤)
    (hBu' : ∀ n s c, w12Norm (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c) ≤ Bu)
    {Ainf : Fin 4 → Fin 5 → Fin 5 → E4 → ℂ} {GA : Fin 4 → Fin 5 → Fin 5 → Fin 4 → E4 → ℂ}
    {uinf : MIdx → Fin 5 → E4 → ℂ} {Gu : MIdx → Fin 5 → Fin 4 → E4 → ℂ}
    (q1 : ∀ ν c e, MemW12 (box lo hi) (Ainf ν c e) (GA ν c e))
    (q2 : ∀ ν c e (q : ℝ≥0∞), 1 ≤ q → q < 4 → Tendsto (fun n => eLpNorm
      (entries (gaugeConn (R n) (connM (z n).A)) ν c e - Ainf ν c e) q
      (volume.restrict (box lo hi))) atTop (𝓝 0))
    (q4 : ∀ μ ν c e (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • curvatureW (entries (gaugeConn (R n) (connM (z n).A)))
        (entryGrad (gaugeConn (R n) (connM (z n).A))) μ ν c e x ∂(volume.restrict (box lo hi)))
        atTop (𝓝 (∫ x, w x • curvatureW Ainf GA μ ν c e x ∂(volume.restrict (box lo hi)))))
    (q5 : ∀ s c, MemW12 (box lo hi) (uinf s c) (Gu s c))
    (q6 : ∀ s c (q : ℝ≥0∞), 1 ≤ q → q < 4 → Tendsto (fun n => eLpNorm
      (transp (R n) (matterSec (z n) s) c - uinf s c) q (volume.restrict (box lo hi))) atTop
      (𝓝 0))
    (q7 : ∀ s c μ (w : E4 → ℝ), MemLp w 2 (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • tgrad (R n) (matterSec (z n) s) c μ x
        ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • Gu s c μ x ∂(volume.restrict (box lo hi)))))
    (q8 : ∀ s c μ (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • (tgrad (R n) (matterSec (z n) s) c μ x +
          ∑ e, entries (gaugeConn (R n) (connM (z n).A)) μ c e x *
            transp (R n) (matterSec (z n) s) e x) ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • (Gu s c μ x + ∑ e, Ainf μ c e x * uinf s e x)
          ∂(volume.restrict (box lo hi)))))
    {MF : ℝ≥0∞} (hMF : MF ≠ ⊤)
    (hE : ∀ n, curvEnergy (gaugeConn (R n) (connM (z n).A)) (box lo hi) ≤ MF)
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hQ3c : ∀ n, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM (z n).A) (matterSec (z n) none) μ y e)
      2 (volume.restrict (box lo hi)) ≤ B)
    {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hs : ∀ j, Tendsto (fun n => gaugeScalars (θ n) j) atTop (𝓝 (gaugeScalars θ₀ j)))
    (hl : Tendsto (fun n => (θ n).lambdaH) atTop (𝓝 θ₀.lambdaH))
    (hv : Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH))
    (hk : Tendsto (fun n => (2 * (θ n).kappa)⁻¹) atTop (𝓝 (2 * θ₀.kappa)⁻¹))
    (hΛ : Tendsto (fun n => -(2 * (θ n).Lambda)) atTop (𝓝 (-(2 * θ₀.Lambda))))
    (hm : Tendsto (fun n => mY (θ n)) atTop (𝓝 (mY θ₀)))
    (hzero : ∀ v, IsSetTest (box lo hi) v → Tendsto (fun n => ∫ x in box lo hi,
      fullCov mY (θ n) (redJet (gaugeTuple (R n) (z n)) x) (testJet v x)) atTop (𝓝 0))
    {QF : StrongDual ℝ C(Icc lo hi, PIdx (Fin 4 → ConnFibre) → PIdx (Fin 4 → ConnFibre) → ℝ)}
    {QK : StrongDual ℝ C(Icc lo hi, PIdx (Fin 4 → HiggsFibre) → PIdx (Fin 4 → HiggsFibre) → ℝ)}
    {QY : StrongDual ℝ C(Icc lo hi, PIdx ℝ → PIdx ℝ → ℝ)}
    (dF : IsDefect (V0 lo hi) (fun n => pk lo hi (fun x => (redJet (gaugeTuple (R n) (z n)) x).F))
      (pk lo hi (fun x => (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x).F)) QF)
    (dK : IsDefect (V0 lo hi) (fun n => pk lo hi (fun x => (redJet (gaugeTuple (R n) (z n)) x).K))
      (pk lo hi (fun x => (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x).K)) QK)
    (dY : IsDefect (V0 lo hi)
      (fun n => pk lo hi (fun x => quartY (θ n) (redJet (gaugeTuple (R n) (z n)) x)))
      (pk lo hi (fun x => quartY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x))) QY)
    (hUIF : UnifIntegrable (fun n x => ‖curvVec (connM (z n).A) x‖) 2
      (volume.restrict (box lo hi))) :

    (CubeConv lo hi (fun n x => redJet (gaugeTuple (R n) (z n)) x)
         (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu)) ∧
       (∀ v, IsSetTest (box lo hi) v → v.e = 0 →
         ∫ x in box lo hi, fullCov mY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x)
           (testJet v x) = 0) ∧
       (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QF P) ∧
       (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QK P) ∧
       (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QY P) ∧
       ∃ (ec : C(Icc lo hi, CoframeFibre)) (hec : ∀ y, ec y ∈ Ke),
         (∀ᵐ y ∂(V0 lo hi), ec y = e₀ y.val) ∧
         ∀ v, IsSetTest (box lo hi) v → ∀ hc : Continuous (testJet v),
           (∫ x in box lo hi, fullCov mY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x)
               (testJet v x)) +
             smDefect QF QK QY θ₀ ec (fun y => hKeGL (hec y))
               ⟨fun y => testJet v y.val, hc.comp continuous_subtype_val⟩ = 0) ∧
      (∃ ρF : PIdx (Fin 4 → ConnFibre) → PIdx (Fin 4 → ConnFibre) → Icc lo hi → ℝ,
        (∀ i j, Integrable (ρF i j) (V0 lo hi)) ∧
        ∀ P, QF P = ∫ x, ∑ i, ∑ j, P x i j * ρF i j x ∂(V0 lo hi)) ∧
      (UnifIntegrable (fun p : ℕ × (Fin 4 × Fin 5) => fun y =>
          covDerV (connM (z p.1).A) (matterSec (z p.1) none) p.2.1 y p.2.2) 2
          (volume.restrict (box lo hi)) →
        ∃ ρK : PIdx (Fin 4 → HiggsFibre) → PIdx (Fin 4 → HiggsFibre) → Icc lo hi → ℝ,
          (∀ i j, Integrable (ρK i j) (V0 lo hi)) ∧
          ∀ P, QK P = ∫ x, ∑ i, ∑ j, P x i j * ρK i j x ∂(V0 lo hi)) ∧
      (UnifIntegrable (fun p : ℕ × Fin 5 => fun y => matterSec (z p.1) none y p.2) 4
          (volume.restrict (box lo hi)) → QY = 0) := by
  have q2' := fun ν c e => q2 ν c e 2 one_le_two (by norm_num)
  have q6' := fun s c => q6 s c 2 one_le_two (by norm_num)
  obtain ⟨w1, w2, w3⟩ := cube_packets_weakL2 hlh hzA hzH hz hlie hR e₀ de₀ hWA hWu hBu hBu' q1 q2'
    q4 q5 q6' q8 hMF hE hB hQ3c hv
  have hbase := cube_all mY hlh hQK hzA hzH hze hz hlie hR hKe hKeGL heK he₀ hde₀ hLinf hL2 hd hWA
    hWu hBu hBu' q1 q2 q4 q5 q6 q7 q8 hMF hE hB hQ3c hs hl hv hk hΛ hm hzero dF dK dY
  refine ⟨hbase, ?_, fun hUIK => ?_, fun hUIH => ?_⟩
  · obtain ⟨Cb, -, hC⟩ := weakL2_exists_eLpNorm_le w1
    exact isDefect_density w1 dF (unifTrunc_of_unifIntegrable (fun n i => (w1.memLp n i).1)
      (fun i => unifIntegrable_F_packet hR (fun n x => (hz n x).A) hUIF i) hC)
  · obtain ⟨Cb, -, hC⟩ := weakL2_exists_eLpNorm_le w2
    have hmK : ∀ n (k : Fin 4 × Fin 5), AEStronglyMeasurable
        (fun y => covDerV (connM (z n).A) (matterSec (z n) none) k.1 y k.2)
        (volume.restrict (box lo hi)) := fun n k =>
      (continuous_covDerV_entry (fun μ c e =>
          ((continuous_apply e).comp ((continuous_apply c).comp ((continuous_apply μ).comp
            (hzA n).continuous))))
        (embHL.contDiff.comp (hzH n)) k.1 k.2).aestronglyMeasurable
    exact isDefect_density w2 dK (unifTrunc_of_unifIntegrable (fun n i => (w2.memLp n i).1)
      (fun i => unifIntegrable_K_packet hR hz hlie hmK hUIK i) hC)
  · exact quartic_defect_eq_zero hlh hR hzH hWu q5 q6' hUIH hv (fun x i => rfl) w3 dY

end CubeAllUI

/-! ### Uniform integrability along a subsequence on a cube -/

section UICube

theorem ui_cube_F {z : ℕ → FieldTuple (Fin 5)} (Φ : ℕ → ℕ) {Q K : Set E4} (hQ : MeasurableSet Q)
    (hQK : Q ⊆ K) (h : UnifIntegrable (fun n x => ‖curvVec (connM (z n).A) x‖) 2
      (volume.restrict K)) :
    UnifIntegrable (fun n x => ‖curvVec (connM (z (Φ n)).A) x‖) 2 (volume.restrict Q) :=
  unifIntegrable_restrict_subset hQ hQK (unifIntegrable_reindex h Φ)

theorem ui_cube_K {z : ℕ → FieldTuple (Fin 5)} (Φ : ℕ → ℕ) {Q K : Set E4} (hQ : MeasurableSet Q)
    (hQK : Q ⊆ K) (h : UnifIntegrable (fun p : ℕ × (Fin 4 × Fin 5) => fun y =>
      covDerV (connM (z p.1).A) (matterSec (z p.1) none) p.2.1 y p.2.2) 2 (volume.restrict K)) :
    UnifIntegrable (fun p : ℕ × (Fin 4 × Fin 5) => fun y =>
      covDerV (connM (z (Φ p.1)).A) (matterSec (z (Φ p.1)) none) p.2.1 y p.2.2) 2
      (volume.restrict Q) := by
  refine unifIntegrable_restrict_subset (f := fun p : ℕ × (Fin 4 × Fin 5) => fun y =>
      covDerV (connM (z (Φ p.1)).A) (matterSec (z (Φ p.1)) none) p.2.1 y p.2.2) hQ hQK ?_
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := h hε
  exact ⟨δ, hδ, fun p => hd (Φ p.1, p.2)⟩

theorem ui_cube_H {z : ℕ → FieldTuple (Fin 5)} (Φ : ℕ → ℕ) {Q K : Set E4} (hQ : MeasurableSet Q)
    (hQK : Q ⊆ K) (h : UnifIntegrable (fun p : ℕ × Fin 5 => fun y => matterSec (z p.1) none y p.2)
      4 (volume.restrict K)) :
    UnifIntegrable (fun p : ℕ × Fin 5 => fun y => matterSec (z (Φ p.1)) none y p.2) 4
      (volume.restrict Q) := by
  refine unifIntegrable_restrict_subset (f := fun p : ℕ × Fin 5 => fun y =>
      matterSec (z (Φ p.1)) none y p.2) hQ hQK ?_
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := h hε
  exact ⟨δ, hδ, fun p => hd (Φ p.1, p.2)⟩

end UICube

/-! ### The complete theorem -/

set_option maxHeartbeats 20000000 in
/-- **`thm:critical-quotient-defect`** (complete; Standard-Model structure group, box rendering of the chart
`K = box a b`, defining-carrier matter).  Hypotheses (Q1)–(Q5): smooth reconstructed fields
`z_h = (e_h, A_h, H_h, Ψ_h, Ψ̄_h)` with `𝔰(𝔲(3) ⊕ 𝔲(2))`-valued connections and coefficient banks
`θ_h` in a compact physical set; coframes with values in a compact subset of the nondegenerate
chart and precompact in `L^∞ ∩ H¹`; bounded and uniformly integrable curvature energy;
gauge-invariant `L²` bounds of the matter sections and of their covariant derivatives; equivariant
consistency and stationarity budgets `c_h + ε_h → 0` with the covariant test size.  Conclusion:
for every compact `K' ⊂ K`, Coulomb cubes covering `K'` with smooth `G_SM`-valued gauges
(`𝔰(𝔲(3) ⊕ 𝔲(2))`-valued Coulomb connections, small `L⁴` norm), one subsequence `Φ` and a limit
bank `θ₀` such that on every cube: the critical convergences (`CubeConv`); the Yang–Mills, Higgs,
Dirac and dual-Dirac equations in distributions; positive semidefinite covariance measures
`𝖰_F, 𝖰_K, 𝖰_Y` of the curvature, covariant Higgs gradient and quartic packets; a continuous
representative `ec` of the limit coframe on the closed cube; and the **metric equation**
`∫_Q Cov_{θ₀}(j L)(j¹ v) + 𝔖(j¹ v) = 0` for every smooth test `v` supported in the cube
(`eq:critical-quotient-einstein` in the first-variation normalisation, `𝔖 = 𝔖_YM + 𝔖_H`).
**`L¹`-density clause**: the curvature covariance measure is an `L¹` density (uniform
integrability of `|F|²` is (Q2)); if `|D_{A_h}H_h|²` is uniformly integrable the Higgs-kinetic
covariance measure is an `L¹` density, so the complete bosonic defect `𝔖` is an `L¹` tensor density
once also the quartic part vanishes, which holds if `|H_h|⁴` is uniformly integrable. -/
theorem critical_quotient_defect_SM {Ysec : Type} [Fintype Ysec] (mY : CoefficientBank Ysec → ℂ)
    (hmY : ∃ f : (Fin 7 → ℝ) × (Ysec → Matrix (Fin 3) (Fin 3) ℂ) → ℂ, Continuous f ∧
      ∀ θ, mY θ = f (bankCoords θ))
    {a b : E4} (z : ℕ → FieldTuple (Fin 5))
    (hze : ∀ h, ContDiff ℝ ∞ (z h).e) (hzA : ∀ h, ContDiff ℝ ∞ (z h).A)
    (hzH : ∀ h, ContDiff ℝ ∞ (z h).H) (hzΨ : ∀ h, ContDiff ℝ ∞ (z h).Ψ)
    (hzΨb : ∀ h, ContDiff ℝ ∞ (z h).Ψb) (hlie : ∀ h y μ, (z h).A y μ ∈ smLie)
    (θ : ℕ → CoefficientBank Ysec)
    (hP : ∃ P, IsCompactBankSet P ∧ ∀ h, θ h ∈ P)
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL)
    (heK : ∀ h, ∀ x ∈ box a b, (z h).e x ∈ Ke)
    (hQ1 : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      CoframeLimitH1 (box a b) (fun h => (z h).e) (φ ∘ ψ))
    (hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (connM (z h).A) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (connM (z h).A) x))
    (hQ3 : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h s,
      ∑ e, eLpNorm (fun y => matterSec (z h) s y e) 2 (volume.restrict (box a b)) +
        ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM (z h).A) (matterSec (z h) s) μ y e) 2
          (volume.restrict (box a b)) ≤ B)
    (Dfin : ℕ → FieldTuple (Fin 5) → ℝ) (c ε : ℕ → ℝ)
    (hcons : ∀ h v, IsSetTest (box a b) v →
      |Dfin h v - boxVariation mY (θ h) (box a b) (z h) v| ≤
        c h * (nSize (volume.restrict (box a b)) (z h).A v).toReal)
    (hstat : ∀ h v, IsSetTest (box a b) v →
      |Dfin h v| ≤ ε h * (nSize (volume.restrict (box a b)) (z h).A v).toReal)
    (hce : Tendsto (fun h => c h + ε h) atTop (𝓝 0))
    {K' : Set E4} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → E4) (r : ℝ), 0 < r ∧ (∀ j, eBall (ctr j) r ⊆ box a b) ∧
      (∀ j, innerCube (ctr j) r ⊆ eBall (ctr j) r) ∧ K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → E4 → M5,
        (∀ h j, ∀ y ∈ eBall (ctr j) r, R h j y ∈ GSM) ∧
        (∀ h j c e, ContDiffOn ℝ ∞ (fun y => R h j y c e) (eBall (ctr j) r)) ∧
        (∀ h j, ∀ y ∈ eBall (ctr j) r, ∀ μ,
          Matrix.of.symm (gaugeConn (R h j) (connM (z h).A) μ y) ∈ smLie) ∧
        (∀ h j, ∀ x ∈ innerCube (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (connM (z h).A)) μ c e μ x = 0) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (connM (z h).A)) ν c e) 4
          (volume.restrict (innerCube (ctr j) r)) ≤ η) ∧
        ∃ Φ : ℕ → ℕ, StrictMono Φ ∧ ∃ θ₀ : CoefficientBank Ysec,
          BankTendsto (fun n => θ (Φ n)) θ₀ ∧ ∀ j, ∃ L : LimitFields (Fin 5),
            CubeConv (cubeLo (ctr j) r) (cubeHi (ctr j) r)
              (fun n x => redJet (gaugeTuple (R (Φ n) j) (z (Φ n))) x) (limitJet L) ∧
            (∀ v, IsSetTest (innerCube (ctr j) r) v → v.e = 0 →
              ∫ x in innerCube (ctr j) r, fullCov mY θ₀ (limitJet L x) (testJet v x) = 0) ∧
            ∃ (QF : StrongDual ℝ C(Icc (cubeLo (ctr j) r) (cubeHi (ctr j) r),
                  PIdx (Fin 4 → ConnFibre) → PIdx (Fin 4 → ConnFibre) → ℝ))
              (QK : StrongDual ℝ C(Icc (cubeLo (ctr j) r) (cubeHi (ctr j) r),
                  PIdx (Fin 4 → HiggsFibre) → PIdx (Fin 4 → HiggsFibre) → ℝ))
              (QY : StrongDual ℝ C(Icc (cubeLo (ctr j) r) (cubeHi (ctr j) r),
                  PIdx ℝ → PIdx ℝ → ℝ)),
              IsDefect (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
                (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
                  (fun x => (redJet (gaugeTuple (R (Φ n) j) (z (Φ n))) x).F))
                (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r) (fun x => (limitJet L x).F)) QF ∧
              IsDefect (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
                (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
                  (fun x => (redJet (gaugeTuple (R (Φ n) j) (z (Φ n))) x).K))
                (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r) (fun x => (limitJet L x).K)) QK ∧
              IsDefect (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
                (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
                  (fun x => quartY (θ (Φ n)) (redJet (gaugeTuple (R (Φ n) j) (z (Φ n))) x)))
                (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r) (fun x => quartY θ₀ (limitJet L x)))
                QY ∧
              (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QF P) ∧
              (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QK P) ∧
              (∀ P, (∀ x w, 0 ≤ qf (P x) w) → 0 ≤ QY P) ∧
              (∃ ρF : PIdx (Fin 4 → ConnFibre) → PIdx (Fin 4 → ConnFibre) →
                  Icc (cubeLo (ctr j) r) (cubeHi (ctr j) r) → ℝ,
                (∀ i j', Integrable (ρF i j') (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))) ∧
                ∀ P, QF P = ∫ x, ∑ i, ∑ j', P x i j' * ρF i j' x
                  ∂(V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))) ∧
              (UnifIntegrable (fun p : ℕ × (Fin 4 × Fin 5) => fun y =>
                  covDerV (connM (z p.1).A) (matterSec (z p.1) none) p.2.1 y p.2.2) 2
                  (volume.restrict (box a b)) →
                ∃ ρK : PIdx (Fin 4 → HiggsFibre) → PIdx (Fin 4 → HiggsFibre) →
                    Icc (cubeLo (ctr j) r) (cubeHi (ctr j) r) → ℝ,
                  (∀ i j', Integrable (ρK i j') (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))) ∧
                  ∀ P, QK P = ∫ x, ∑ i, ∑ j', P x i j' * ρK i j' x
                    ∂(V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))) ∧
              (UnifIntegrable (fun p : ℕ × Fin 5 => fun y => matterSec (z p.1) none y p.2) 4
                  (volume.restrict (box a b)) → QY = 0) ∧
              ∃ (ec : C(Icc (cubeLo (ctr j) r) (cubeHi (ctr j) r), CoframeFibre))
                (hec : ∀ y, ec y ∈ Ke),
                (∀ᵐ y ∂(V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r)), ec y = L.e y.val) ∧
                ∀ v, IsSetTest (innerCube (ctr j) r) v → ∀ hc : Continuous (testJet v),
                  (∫ x in innerCube (ctr j) r, fullCov mY θ₀ (limitJet L x) (testJet v x)) +
                    smDefect QF QK QY θ₀ ec (fun y => hKeGL (hec y))
                      ⟨fun y => testJet v y.val, hc.comp continuous_subtype_val⟩ = 0 := by
  set A : ℕ → MConn 5 := fun h => connM (z h).A
  have hA : ∀ h, IsSmoothUnitaryConn (A h) := fun h => isSmoothUnitaryConn_connM (hzA h) (hlie h)
  have hsm : ∀ h μ y, Matrix.of.symm (A h μ y) ∈ smLie := fun h μ y => hlie h y μ
  have hu : ∀ h s, ContDiff ℝ ∞ (matterSec (z h) s) := fun h s =>
    contDiff_matterSec (hzH h) (hzΨ h) (hzΨb h) s
  obtain ⟨N, ctr, r, hr, hball, hQB, hcover, R, hRG, hRs, hlieC, hdiv, hA4, ⟨BA, hBAt, hAW⟩,
    ⟨Bu, hBut, hUW⟩, φ, hφ, hcf, hQL⟩ :=
    critical_quotient_chart_SM A hA hsm hUI (fun h => matterSec (z h)) hu hQ3
      (fun h => (z h).e) hQ1 (∅ : Set MIdx) (by simp) hK' hK'Q hη
  obtain ⟨P, hPc, hθP⟩ := hP
  obtain ⟨ψ, hψ, θ₀, -, hbank⟩ := bank_extract hPc hθP φ
  obtain ⟨hs, hl, hv, hk, hΛ, hm⟩ := bank_tendsto_all mY hmY ⟨P, hPc, fun n => hθP (φ (ψ n))⟩
    hbank
  obtain ⟨e₀, de₀, he₀, hde₀, hcfl⟩ := hcf.comp hψ
  obtain ⟨M, hM⟩ := hbd
  obtain ⟨B, hBt, hB⟩ := hQ3
  have hz : ∀ n x, DiffAt (z n) x := fun n x =>
    ⟨((hze n).differentiable (by simp)) x, ((hzA n).differentiable (by simp)) x,
      ((hzH n).differentiable (by simp)) x, ((hzΨ n).differentiable (by simp)) x,
      ((hzΨb n).differentiable (by simp)) x⟩
  choose Ainf GA uinf Gu hq using fun j =>
    QuotientLimit.comp (QuotientLimitL4.quotientLimit (hQL j)) hψ
  have hlhj : ∀ j, ∀ i, cubeLo (ctr j) r i < cubeHi (ctr j) r i := fun j i => by
    simp only [cubeLo, cubeHi]; linarith
  have hQKj : ∀ j, box (cubeLo (ctr j) r) (cubeHi (ctr j) r) ⊆ box a b := fun j =>
    (hQB j).trans (hball j)
  have hRj : ∀ j k, ∀ x ∈ box (cubeLo (ctr j) r) (cubeHi (ctr j) r), GaugeAt (R k j) x :=
    fun j k x hx => gaugeAt_of_ball (isOpen_eBall _ _) (hRs _ j) (hRG _ j) (hQB j hx)
  have hEj : ∀ j k, curvEnergy (gaugeConn (R k j) (connM (z k).A))
      (box (cubeLo (ctr j) r) (cubeHi (ctr j) r)) ≤ (M : ℝ≥0∞) := by
    intro j k
    have hopen := isOpen_box (cubeLo (ctr j) r) (cubeHi (ctr j) r)
    rw [curvEnergy_gaugeConn hopen (fun y hy => (hRG _ j y (hQB j hy)).1)
      (fun c e => ((hRs _ j c e).mono (hQB j)).of_le (WithTop.coe_le_coe.mpr le_top)) (hA _)]
    exact (lintegral_mono_set (hQKj j)).trans (hM _)
  have hQ3j : ∀ j k, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM (z k).A)
      (matterSec (z k) none) μ y e) 2
      (volume.restrict (box (cubeLo (ctr j) r) (cubeHi (ctr j) r))) ≤ B :=
    fun j k => (Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun μ _ =>
      eLpNorm_restrict_mono_set (hQKj j)).trans (le_add_left le_rfl |>.trans (hB _ none))
  -- weak packets along `φ ∘ ψ` on every cube
  have hWL : ∀ j, WeakL2 (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
        (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x).F))
        (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x).F)) ∧
      WeakL2 (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
        (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x).K))
        (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x).K)) ∧
      WeakL2 (V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
        (fun n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => quartY (θ (φ (ψ n))) (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x)))
        (pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
          (fun x => quartY θ₀ (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x))) := by
    intro j
    obtain ⟨q1, q2, -, q4, q5, q6, -, q8⟩ := hq j
    exact cube_packets_weakL2 (z := fun n => z (φ (ψ n))) (R := fun n => R (φ (ψ n)) j)
      (θ := fun n => θ (φ (ψ n))) (hlhj j) (fun n => hzA _) (fun n => hzH _) (fun n => hz _)
      (fun n => hlie _) (fun n => hRj j _) e₀ de₀ (fun n => (hAW _ j · · · |>.1))
      (fun n => (hUW _ j · · |>.1)) hBut (fun n s c => (hUW _ j s c).2) q1
      (fun ν c e => q2 ν c e 2 one_le_two (by norm_num)) q4 q5
      (fun s c => q6 s c 2 one_le_two (by norm_num)) q8 (by simp) (fun n => hEj j _) hBt
      (fun n => hQ3j j _) hv
  -- common extraction of the covariance measures on all cubes
  obtain ⟨σ, hσ, hdef⟩ := exists_common_defects
    (fun j => V0 (cubeLo (ctr j) r) (cubeHi (ctr j) r))
    (fun j n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x).F))
    (fun j => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x).F))
    (fun j n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x).K))
    (fun j => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x).K))
    (fun j n => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => quartY (θ (φ (ψ n))) (redJet (gaugeTuple (R (φ (ψ n)) j) (z (φ (ψ n)))) x)))
    (fun j => pk (cubeLo (ctr j) r) (cubeHi (ctr j) r)
      (fun x => quartY θ₀ (limitJet (limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j)) x)))
    hWL
  have hΦ : StrictMono (fun n => φ (ψ (σ n))) := hφ.comp (hψ.comp hσ)
  have ht := hσ.tendsto_atTop
  refine ⟨N, ctr, r, hr, hball, hQB, hcover, R, hRG, hRs, hlieC, hdiv, hA4,
    fun n => φ (ψ (σ n)), hΦ, θ₀, hbank.comp ht, fun j => ?_⟩
  obtain ⟨q1, q2, -, q4, q5, q6, q7, q8⟩ := hq j
  obtain ⟨QF, QK, QY, dF, dK, dY⟩ := hdef j
  have hWA : ∀ n ν c e, MemW12 (box (cubeLo (ctr j) r) (cubeHi (ctr j) r))
      (entries (gaugeConn (R (φ (ψ (σ n))) j) (connM (z (φ (ψ (σ n)))).A)) ν c e)
      (entryGrad (gaugeConn (R (φ (ψ (σ n))) j) (connM (z (φ (ψ (σ n)))).A)) ν c e) :=
    fun n ν c e => (hAW _ j ν c e).1
  have hWu : ∀ n s c, MemW12 (box (cubeLo (ctr j) r) (cubeHi (ctr j) r))
      (transp (R (φ (ψ (σ n))) j) (matterSec (z (φ (ψ (σ n)))) s) c)
      (tgrad (R (φ (ψ (σ n))) j) (matterSec (z (φ (ψ (σ n)))) s) c) :=
    fun n s c => (hUW _ j s c).1
  have hzero : ∀ v, IsSetTest (box (cubeLo (ctr j) r) (cubeHi (ctr j) r)) v →
      Tendsto (fun n => ∫ x in box (cubeLo (ctr j) r) (cubeHi (ctr j) r),
        fullCov mY (θ (φ (ψ (σ n)))) (redJet (gaugeTuple (R (φ (ψ (σ n))) j)
          (z (φ (ψ (σ n))))) x) (testJet v x)) atTop (𝓝 0) := fun v hv' =>
    budget_pullback_tendsto mY (S := box a b) (B := eBall (ctr j) r) (z := z) (θ := θ)
      (Φ := fun n => φ (ψ (σ n))) (hlhj j) (isOpen_box a b).measurableSet (isOpen_eBall _ _)
      (hQB j) (hQKj j) hz (fun n x hx => hKeGL (heK n x hx)) hΦ
      (R := fun n => R (φ (ψ (σ n))) j) (fun n => hRs _ j) (fun n => hRG _ j) hWA hBAt
      (fun n ν c e => (hAW _ j ν c e).2) Dfin c ε hcons hstat hce hv'
  have hcm : MeasurableSet (box (cubeLo (ctr j) r) (cubeHi (ctr j) r)) :=
    (isOpen_box _ _).measurableSet
  obtain ⟨⟨hc1, hc2, hc3, hc4, hc5, hc6⟩, hρF, hρK, hQY⟩ := cube_all_UI mY
    (z := fun n => z (φ (ψ (σ n))))
    (R := fun n => R (φ (ψ (σ n))) j) (θ := fun n => θ (φ (ψ (σ n)))) (hlhj j) (hQKj j)
    (fun n => hzA _) (fun n => hzH _) (fun n => hze _) (fun n => hz _) (fun n => hlie _)
    (fun n => hRj j _) hKe hKeGL (fun n => heK _) he₀ hde₀
    (fun i ν => ((hcfl i ν).1).comp ht) (fun i ν => ((hcfl i ν).2.1).comp ht)
    (fun i ν μ => ((hcfl i ν).2.2 μ).comp ht) hWA hWu hBut (fun n s c => (hUW _ j s c).2) q1
    (fun ν c e q h1 h4 => (q2 ν c e q h1 h4).comp ht)
    (fun μ ν c e w hw => (q4 μ ν c e w hw).comp ht) q5
    (fun s c q h1 h4 => (q6 s c q h1 h4).comp ht) (fun s c μ w hw => (q7 s c μ w hw).comp ht)
    (fun s c μ w hw => (q8 s c μ w hw).comp ht) (by simp) (fun n => hEj j _) hBt
    (fun n => hQ3j j _) (fun j' => (hs j').comp ht) (hl.comp ht) (hv.comp ht) (hk.comp ht)
    (hΛ.comp ht) (hm.comp ht) hzero dF dK dY
    (ui_cube_F (fun n => φ (ψ (σ n))) hcm (hQKj j) (unifIntegrable_curv hUI))
  exact ⟨limitOf e₀ de₀ (Ainf j) (GA j) (uinf j) (Gu j), hc1, hc2, QF, QK, QY, dF, dK, dY, hc3, hc4,
    hc5, hρF, fun hK => hρK (ui_cube_K (fun n => φ (ψ (σ n))) hcm (hQKj j) hK),
    fun hH => hQY (ui_cube_H (fun n => φ (ψ (σ n))) hcm (hQKj j) hH), hc6⟩

end RenewalGeometry.CriticalQuotientRows
