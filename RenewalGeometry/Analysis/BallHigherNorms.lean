/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallUhlenbeckPackage

/-!
# Seminorm toolkit for the higher a-priori bounds of Coulomb gauges
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `mN_le_norm` — `‖X‖_{L^p}` (entrywise) is bounded by the Sobolev algebra norm (`H^s ⊂ L^∞`);
* `mN_le_mN` — `L^q ⊂ L^p` on the ball for `p ≤ q`;
* `mN_mul_le_44`, `mN_mul_le_inf2`, `mN_mul_le_2inf`, `mN_mul_le_inf4`, `mN_mul_le_4inf`,
  `mN_mul_le_infinf`, `mN_mul3_le` — Hölder for matrix products;
* `mN_four_le` — **critical Sobolev** `‖X‖_{L⁴} ≤ C_S (‖X‖_{L²} + Σ_ν ‖∂_νX‖_{L²})` for matrix
  fields;
* `mN_top_le_of_unitary` — unitary fields have `L^∞` entries `≤ 1`;
* `hM_mono`, `norm_le_hM`, `hM_le_norm` — the jet seminorms against the algebra norms.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.HigherNorms

open SobolevOpen BallReg BallAlg SobAlg

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-! ### Lebesgue seminorms against the algebra norm -/

theorem sN_le_norm {s : ℕ} [Fact (3 ≤ s)] (p : ℝ≥0∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : SobAlg c r s, sN p F ≤ C * ‖F‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_eLpNorm_fn_le (c := c) (r := r) (s := s) p
  exact ⟨C, hC0, fun F => ENNReal.toReal_le_of_le_ofReal (by positivity) (hC F)⟩

theorem mN_le_norm {s : ℕ} [Fact (3 ≤ s)] (p : ℝ≥0∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : MatSob c r s m, mN p X ≤ C * ‖X‖ := by
  obtain ⟨C, hC0, hC⟩ := sN_le_norm (c := c) (r := r) (s := s) p
  refine ⟨(m : ℝ) ^ 2 * C, by positivity, fun X => ?_⟩
  unfold mN
  calc ∑ i, ∑ j, (sN p (X i j).re + sN p (X i j).im)
      ≤ ∑ _i : Fin m, ∑ _j : Fin m, C * ‖X‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        calc sN p (X i j).re + sN p (X i j).im ≤ C * ‖(X i j).re‖ + C * ‖(X i j).im‖ :=
              add_le_add (hC _) (hC _)
          _ = C * ‖X i j‖ := by rw [Cx.norm_def, mul_add]
          _ ≤ C * ‖X‖ := by gcongr; exact norm_entry_le_linfty X i j
    _ = (m : ℝ) ^ 2 * C * ‖X‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### Comparison of Lebesgue exponents -/

theorem sN_le_sN {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℕ} [Fact (3 ≤ s)] (F : SobAlg c r s), sN p F ≤ C * sN q F := by
  have hfin := isFiniteMeasure_restrict_euclBall c hr.out.le
  set V := (volume.restrict (euclBall c r)) Set.univ ^ (1 / p.toReal - 1 / q.toReal)
  have hexp : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
    rcases eq_or_ne q ⊤ with rfl | hq
    · rw [ENNReal.toReal_top, div_zero, sub_zero]; positivity
    · have hpt : p ≠ ⊤ := ne_top_of_le_ne_top hq hpq
      have h2 : 0 < p.toReal := ENNReal.toReal_pos (by positivity) hpt
      have := one_div_le_one_div_of_le h2 (ENNReal.toReal_mono hq hpq)
      linarith
  have hV : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top _ _)
  refine ⟨V.toReal, ENNReal.toReal_nonneg, fun {s} _ F => ?_⟩
  unfold sN
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (euclBall c r)) hpq
    (memLp_fn F).aestronglyMeasurable
  calc (eLpNorm (fn F) p (volume.restrict (euclBall c r))).toReal
      ≤ (eLpNorm (fn F) q (volume.restrict (euclBall c r)) * V).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (eLpNorm_fn_ne_top q F) hV) h
    _ = V.toReal * (eLpNorm (fn F) q (volume.restrict (euclBall c r))).toReal := by
        rw [ENNReal.toReal_mul, mul_comm]

theorem mN_le_mN {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℕ} [Fact (3 ≤ s)] (X : MatSob c r s m), mN p X ≤ C * mN q X := by
  obtain ⟨C, hC0, hC⟩ := sN_le_sN (c := c) (r := r) hp hpq
  refine ⟨C, hC0, fun {s} _ X => ?_⟩
  unfold mN
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_add]
  exact add_le_add (hC _) (hC _)

/-! ### Hölder for matrix products -/

section Holder

variable {s : ℕ} [Fact (3 ≤ s)]

theorem mN_mul_le_44 (X Y : MatSob c r s m) : mN 2 (X * Y) ≤ mN 4 X * mN 4 Y :=
  mN_mul_le 4 4 2 (by norm_num) X Y

theorem mN_mul_le_inf2 (X Y : MatSob c r s m) : mN 2 (X * Y) ≤ mN ⊤ X * mN 2 Y :=
  mN_mul_le ⊤ 2 2 (by norm_num) X Y

theorem mN_mul_le_2inf (X Y : MatSob c r s m) : mN 2 (X * Y) ≤ mN 2 X * mN ⊤ Y :=
  mN_mul_le 2 ⊤ 2 (by norm_num) X Y

theorem mN_mul_le_inf4 (X Y : MatSob c r s m) : mN 4 (X * Y) ≤ mN ⊤ X * mN 4 Y :=
  mN_mul_le ⊤ 4 4 (by norm_num) X Y

theorem mN_mul_le_4inf (X Y : MatSob c r s m) : mN 4 (X * Y) ≤ mN 4 X * mN ⊤ Y :=
  mN_mul_le 4 ⊤ 4 (by norm_num) X Y

theorem mN_mul_le_infinf (X Y : MatSob c r s m) : mN ⊤ (X * Y) ≤ mN ⊤ X * mN ⊤ Y :=
  mN_mul_le ⊤ ⊤ ⊤ (by norm_num) X Y

/-- `‖X Y Z‖_{L²} ≤ ‖X‖_{L⁴} ‖Y‖_{L^∞} ‖Z‖_{L⁴}`. -/
theorem mN_mul3_le (X Y Z : MatSob c r s m) : mN 2 (X * Y * Z) ≤ mN 4 X * mN ⊤ Y * mN 4 Z :=
  (mN_mul_le_44 (X * Y) Z).trans (mul_le_mul_of_nonneg_right (mN_mul_le_4inf X Y)
    (mN_nonneg _ _))

end Holder

/-! ### Critical Sobolev for matrix fields -/

/-- **Critical Sobolev inequality for matrix fields.** -/
theorem mN_four_le :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ {s : ℕ} [Fact (3 ≤ s)] (X : MatSob c r (s + 1) m),
      mN 4 X ≤ CS * (mN 2 X + ∑ ν, mN 2 (derM ν X)) := by
  obtain ⟨CS, hCS0, hCS⟩ := exists_sN_four_le (c := c) (r := r)
  refine ⟨CS, hCS0, fun {s} _ X => ?_⟩
  unfold mN
  have e : ∑ ν, ∑ i, ∑ j, (sN 2 ((derM ν X) i j).re + sN 2 ((derM ν X) i j).im) =
      ∑ i, ∑ j, ((∑ ν, sN 2 (derS ν (X i j).re)) + ∑ ν, sN 2 (derS ν (X i j).im)) := by
    simp only [derM_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_add_distrib]
  rw [e, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := hCS (X i j).re
  have h2 := hCS (X i j).im
  nlinarith

/-! ### Unitary fields are bounded -/

theorem sN_top_le_one {s : ℕ} [Fact (3 ≤ s)] {F : SobAlg c r s}
    (h : ∀ᵐ x ∂(volume.restrict (euclBall c r)), |fn F x| ≤ 1) : sN ⊤ F ≤ 1 := by
  unfold sN
  have : eLpNorm (fn F) ⊤ (volume.restrict (euclBall c r)) ≤ ENNReal.ofReal 1 := by
    refine eLpNorm_le_of_ae_bound (C := 1) ?_ |>.trans ?_
    · filter_upwards [h] with x hx
      rwa [Real.norm_eq_abs]
    · simp
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one this

theorem re_evM {s : ℕ} [Fact (3 ≤ s)] (X : MatSob c r s m) (x : Fin 4 → ℝ) (i j : Fin m) :
    (evM X x i j).re = fn (X i j).re x := by
  simp [evM_apply, evC]

theorem im_evM {s : ℕ} [Fact (3 ≤ s)] (X : MatSob c r s m) (x : Fin 4 → ℝ) (i j : Fin m) :
    (evM X x i j).im = fn (X i j).im x := by
  simp [evM_apply, evC]

/-- **Unitary fields are bounded**: `X X^* = 1` gives `‖X‖_{L^∞}` (entrywise) `≤ 2m²`. -/
theorem mN_top_le_of_unitary {s : ℕ} [Fact (3 ≤ s)] {X : MatSob c r s m} (hX : X * star X = 1) :
    mN ⊤ X ≤ 2 * (m : ℝ) ^ 2 := by
  have hU : ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM X x * star (evM X x) = 1 := by
    filter_upwards [evM_mul X (star X), evM_star X, evM_one (c := c) (r := r) (s := s) (m := m)]
      with x h1 h2 h3
    rw [← h2, ← h1, hX, h3]
  have hent : ∀ i j, ∀ᵐ x ∂(volume.restrict (euclBall c r)), ‖evM X x i j‖ ≤ 1 := by
    intro i j
    filter_upwards [hU] with x hx
    have hii := congrFun (congrFun hx i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hii
    have hsum : ∑ k, ‖evM X x i k‖ ^ 2 = 1 := by
      have : ∑ k, evM X x i k * star (evM X x i k) = ∑ k, ((‖evM X x i k‖ ^ 2 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [this, ← Complex.ofReal_sum] at hii
      exact_mod_cast hii
    have h1 : ‖evM X x i j‖ ^ 2 ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun k => ‖evM X x i k‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    nlinarith [norm_nonneg (evM X x i j)]
  unfold mN
  calc ∑ i, ∑ j, (sN ⊤ (X i j).re + sN ⊤ (X i j).im) ≤ ∑ _i : Fin m, ∑ _j : Fin m, (1 + 1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => add_le_add ?_ ?_
        · refine sN_top_le_one ?_
          filter_upwards [hent i j] with x hx
          have : |(evM X x i j).re| ≤ ‖evM X x i j‖ := Complex.abs_re_le_norm _
          rw [re_evM] at this
          linarith
        · refine sN_top_le_one ?_
          filter_upwards [hent i j] with x hx
          have : |(evM X x i j).im| ≤ ‖evM X x i j‖ := Complex.abs_im_le_norm _
          rw [im_evM] at this
          linarith
    _ = 2 * (m : ℝ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### Jet seminorms against algebra norms -/

section Jet

variable {s : ℕ} [Fact (3 ≤ s)]

theorem hS_mono (K : ℕ) (hK : K + 1 ≤ s) (F : SobAlg c r s) :
    hS K (by omega) F ≤ hS (K + 1) hK F := by
  unfold hS
  simp only [restrL_apply']
  set g : ↥(wordsUpTo 4 K) → ↥(wordsUpTo 4 (K + 1)) := fun w =>
    ⟨w.1, mem_wordsUpTo_mono (Nat.le_succ K) w.2⟩
  have hg : Function.Injective g := fun a b hab => Subtype.ext (by
    have := congrArg Subtype.val hab
    simpa [g] using this)
  calc ∑ w : ↥(wordsUpTo 4 K), ‖((jet F : HsB c r s) : JetAmb c r s) ⟨w.1, _⟩‖
      = ∑ w ∈ (Finset.univ : Finset ↥(wordsUpTo 4 K)).map ⟨g, hg⟩,
          ‖((jet F : HsB c r s) : JetAmb c r s) ⟨w.1, mem_wordsUpTo_mono hK w.2⟩‖ := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ w : ↥(wordsUpTo 4 (K + 1)), ‖((jet F : HsB c r s) : JetAmb c r s)
          ⟨w.1, mem_wordsUpTo_mono hK w.2⟩‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => norm_nonneg _

theorem hM_mono (K : ℕ) (hK : K + 1 ≤ s) (X : MatSob c r s m) :
    hM K (by omega) X ≤ hM (K + 1) hK X :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    add_le_add (hS_mono K hK _) (hS_mono K hK _)

theorem norm_le_hS (F : SobAlg c r s) : ‖F‖ ≤ Kal c r s * hS s le_rfl F := by
  rw [norm_def]
  exact mul_le_mul_of_nonneg_left ((le_of_eq rfl).trans (norm_restrL_le_hS s le_rfl F))
    (Kal_pos c r s).le

theorem hS_le_norm (K : ℕ) (hK : K ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : SobAlg c r s, hS K hK F ≤ C * ‖F‖ := by
  set N : ℝ := ((Fintype.card ↥(wordsUpTo 4 K) : ℕ) : ℝ)
  refine ⟨N * (Kal c r s)⁻¹, by have := (Kal_pos c r s).le; positivity, fun F => ?_⟩
  calc hS K hK F ≤ N * ‖restrL c r hK (jet F)‖ := hS_le_card_mul _ _ _
    _ ≤ N * ‖jet F‖ := by
        gcongr
        exact ((restrL c r hK).le_of_opNorm_le
          (LinearMap.mkContinuous_norm_le _ zero_le_one _) (jet F)).trans (by rw [one_mul])
    _ ≤ N * ((Kal c r s)⁻¹ * ‖F‖) := by gcongr; exact norm_jet_le F
    _ = N * (Kal c r s)⁻¹ * ‖F‖ := by ring

/-- **The matrix algebra norm is controlled by the top jet seminorm.** -/
theorem norm_le_hM (X : MatSob c r s m) : ‖X‖ ≤ (m : ℝ) * Kal c r s * hM s le_rfl X := by
  have hrow : ∀ i, ∑ j, ‖X i j‖ ≤ Kal c r s * ∑ j, (hS s le_rfl (X i j).re +
      hS s le_rfl (X i j).im) := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Cx.norm_def, mul_add]
    exact add_le_add (norm_le_hS _) (norm_le_hS _)
  have hK := (Kal_pos c r s).le
  calc ‖X‖ ≤ ∑ i, ∑ j, ‖X i j‖ := by
        have h : ‖X‖₊ ≤ ∑ i, ∑ j, ‖X i j‖₊ := by
          rw [Matrix.linfty_opNNNorm_def]
          exact Finset.sup_le fun i _ => Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖₊)
            (fun _ _ => zero_le) (Finset.mem_univ i)
        have h' := NNReal.coe_le_coe.mpr h
        push_cast at h'
        exact h'
    _ ≤ ∑ _i : Fin m, Kal c r s * hM s le_rfl X := by
        refine Finset.sum_le_sum fun i _ => (hrow i).trans ?_
        gcongr
        exact Finset.single_le_sum (f := fun i => ∑ j, (hS s le_rfl (X i j).re +
          hS s le_rfl (X i j).im)) (fun i _ => Finset.sum_nonneg fun j _ =>
            add_nonneg (hS_nonneg _ _ _) (hS_nonneg _ _ _)) (Finset.mem_univ i)
    _ = (m : ℝ) * Kal c r s * hM s le_rfl X := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem hM_le_norm (K : ℕ) (hK : K ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : MatSob c r s m, hM K hK X ≤ C * ‖X‖ := by
  obtain ⟨C, hC0, hC⟩ := hS_le_norm (c := c) (r := r) K hK
  refine ⟨(m : ℝ) ^ 2 * C, by positivity, fun X => ?_⟩
  unfold hM
  calc ∑ i, ∑ j, (hS K hK (X i j).re + hS K hK (X i j).im)
      ≤ ∑ _i : Fin m, ∑ _j : Fin m, C * ‖X‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        calc hS K hK (X i j).re + hS K hK (X i j).im ≤ C * ‖(X i j).re‖ + C * ‖(X i j).im‖ :=
              add_le_add (hC _) (hC _)
          _ = C * ‖X i j‖ := by rw [Cx.norm_def, mul_add]
          _ ≤ C * ‖X‖ := by gcongr; exact norm_entry_le_linfty X i j
    _ = (m : ℝ) ^ 2 * C * ‖X‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Jet

end RenewalGeometry.BallAnalysis.HigherNorms
