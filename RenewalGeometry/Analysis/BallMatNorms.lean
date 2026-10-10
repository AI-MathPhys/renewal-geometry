/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallStateRegularity

/-!
# Lebesgue seminorms of Sobolev matrix fields: Hölder, Sobolev and unitarity bounds
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript: the tools for the critical (non-algebra)
levels of the a-priori estimates of Coulomb gauges.

* `sN p F = ‖F‖_{L^p(B)}` for `F ∈ H^s(B)` (always finite, `H^s ⊂ L^∞`);
  `mN p X = Σ_{ij} (‖Re X_{ij}‖_{L^p} + ‖Im X_{ij}‖_{L^p})` for matrix fields;
* `sN_mul_le`, `mN_mul_le` — **Hölder** for products (any Hölder triple `1/r = 1/p + 1/q`);
* `mN_add_le`, `mN_sub_le`, `mN_sum_le`, `mN_smul`, `mN_restrM`, `mN_star` — seminorm calculus;
* `sN_four_le` — **critical Sobolev** `‖F‖_{L⁴(B)} ≤ C_S (‖F‖_{L²} + Σ_i ‖∂_iF‖_{L²})` for
  `F ∈ H^{s+1}(B)` (smooth approximation and lower semicontinuity), and the matrix version
  `mN_four_le`;
* `mN_top_le_of_unitary` — unitary fields have `‖·‖_{L^∞}` entries `≤ 1`.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

instance holderTriple_four : ENNReal.HolderTriple 4 4 2 where
  inv_add_inv_eq_inv := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (Or.inl (by norm_num))
      (Or.inl (by norm_num)), ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num)
      (by norm_num), one_mul]

instance holderTriple_eight : ENNReal.HolderTriple 8 8 4 where
  inv_add_inv_eq_inv := by
    rw [show (8 : ℝ≥0∞) = 2 * 4 by norm_num, ENNReal.mul_inv (Or.inl (by norm_num))
      (Or.inl (by norm_num)), ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num)
      (by norm_num), one_mul]

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-! ### Scalar seminorms -/

section Scalar

variable {s : ℕ} [Fact (3 ≤ s)]

/-- `‖F‖_{L^p(B)}`. -/
def sN (p : ℝ≥0∞) (F : SobAlg c r s) : ℝ :=
  (eLpNorm (fn F) p (volume.restrict (euclBall c r))).toReal

theorem eLpNorm_fn_ne_top (p : ℝ≥0∞) (F : SobAlg c r s) :
    eLpNorm (fn F) p (volume.restrict (euclBall c r)) ≠ ⊤ := by
  obtain ⟨C, -, hC⟩ := exists_eLpNorm_fn_le (c := c) (r := r) (s := s) p
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC F)

theorem sN_nonneg (p : ℝ≥0∞) (F : SobAlg c r s) : 0 ≤ sN p F := ENNReal.toReal_nonneg

theorem ofReal_sN (p : ℝ≥0∞) (F : SobAlg c r s) :
    ENNReal.ofReal (sN p F) = eLpNorm (fn F) p (volume.restrict (euclBall c r)) :=
  ENNReal.ofReal_toReal (eLpNorm_fn_ne_top p F)

theorem sN_congr {p : ℝ≥0∞} {F G : SobAlg c r s}
    (h : fn F =ᵐ[volume.restrict (euclBall c r)] fn G) : sN p F = sN p G := by
  unfold sN; rw [eLpNorm_congr_ae h]

theorem sN_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (F G : SobAlg c r s) : sN p (F + G) ≤ sN p F + sN p G := by
  unfold sN
  rw [eLpNorm_congr_ae (fn_add F G), ← ENNReal.toReal_add (eLpNorm_fn_ne_top p F)
    (eLpNorm_fn_ne_top p G)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨eLpNorm_fn_ne_top p F, eLpNorm_fn_ne_top p G⟩)
    (eLpNorm_add_le (memLp_fn F).aestronglyMeasurable (memLp_fn G).aestronglyMeasurable hp)

theorem sN_neg (p : ℝ≥0∞) (F : SobAlg c r s) : sN p (-F) = sN p F := by
  unfold sN
  rw [eLpNorm_congr_ae (fn_neg F)]
  congr 1
  exact eLpNorm_neg (fn F) p _

theorem sN_sub_le {p : ℝ≥0∞} (hp : 1 ≤ p) (F G : SobAlg c r s) : sN p (F - G) ≤ sN p F + sN p G := by
  rw [sub_eq_add_neg]
  exact (sN_add_le hp F (-G)).trans (by rw [sN_neg])

theorem sN_smul (p : ℝ≥0∞) (t : ℝ) (F : SobAlg c r s) : sN p (t • F) = |t| * sN p F := by
  unfold sN
  rw [eLpNorm_congr_ae (fn_smul t F)]
  rw [show (fun x => t * fn F x) = t • fn F by funext x; simp, eLpNorm_const_smul,
    ENNReal.toReal_mul]
  simp

theorem sN_sum_le {p : ℝ≥0∞} (hp : 1 ≤ p) {ι : Type*} (t : Finset ι) (F : ι → SobAlg c r s) :
    sN p (∑ i ∈ t, F i) ≤ ∑ i ∈ t, sN p (F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [sN, eLpNorm_congr_ae (fn_zero (c := c) (r := r) (s := s))]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sN_add_le hp _ _).trans (by linarith)

/-- **Hölder for products in `H^s(B)`.** -/
theorem sN_mul_le (p q r' : ℝ≥0∞) [ENNReal.HolderTriple p q r'] (F G : SobAlg c r s) :
    sN r' (F * G) ≤ sN p F * sN q G := by
  unfold sN
  rw [eLpNorm_congr_ae (fn_mul F G), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (eLpNorm_fn_ne_top p F) (eLpNorm_fn_ne_top q G)) ?_
  have := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := p) (q := q) (r := r')
    (μ := volume.restrict (euclBall c r)) (memLp_fn F).aestronglyMeasurable
    (memLp_fn G).aestronglyMeasurable (fun a b : ℝ => a * b) 1
    (Eventually.of_forall fun x => by simp [norm_mul])
  simpa using this

theorem sN_restrS {s' : ℕ} [Fact (3 ≤ s')] (h : s' ≤ s) (p : ℝ≥0∞) (F : SobAlg c r s) :
    sN p (restrS h F) = sN p F := rfl

end Scalar

theorem tendsto_eLpNorm_of_sub {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (hg : AEStronglyMeasurable g μ) (hgt : eLpNorm g p μ ≠ ⊤) (hp : 1 ≤ p)
    (h : Tendsto (fun k => eLpNorm (f k - g) p μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) p μ) atTop (𝓝 (eLpNorm g p μ)) := by
  rw [ENNReal.tendsto_nhds hgt]
  intro ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp h) ε hε] with k hk
  constructor
  · refine tsub_le_iff_right.mpr ?_
    have := eLpNorm_add_le (hf k) (hg.sub (hf k)) hp
    rw [show f k + (g - f k) = g by abel, eLpNorm_sub_comm] at this
    exact this.trans (add_le_add le_rfl hk)
  · have := eLpNorm_add_le hg ((hf k).sub hg) hp
    rw [show g + (f k - g) = f k by abel] at this
    exact this.trans (add_le_add le_rfl hk)

/-! ### Critical Sobolev for `H^s(B)` -/

/-- **Critical Sobolev inequality on `H^{s+1}(B)`**: `‖F‖_{L⁴} ≤ C_S (‖F‖_{L²} + Σ_i ‖∂_iF‖_{L²})`. -/
theorem exists_sN_four_le :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ {s : ℕ} [Fact (3 ≤ s)] (F : SobAlg c r (s + 1)),
      sN 4 F ≤ CS * (sN 2 F + ∑ i, sN 2 (derS i F)) := by
  obtain ⟨C, hC⟩ := sobolev_ball_real (n := 4) (by norm_num) (p' := 4) (by norm_num)
  set K : ℝ := (C : ℝ) * max 1 r⁻¹
  refine ⟨K, by positivity, fun {s} _ F => ?_⟩
  set μB := volume.restrict (euclBall c r)
  obtain ⟨φ, hφ, hlim⟩ := exists_tendsto_ofSmooth F
  -- convergence of the function and the derivatives in `L²`
  have hcomp : ∀ (G : SobAlg c r (s + 1)) (ψ : ℕ → SobAlg c r (s + 1)),
      Tendsto ψ atTop (𝓝 G) → Tendsto (fun k => eLpNorm (fn (ψ k) - fn G) 2 μB) atTop (𝓝 0) := by
    intro G ψ h
    have h1 := (fnL (c := c) (r := r) (s := s + 1)).continuous.tendsto G |>.comp h
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h1
    exact h1
  have hder : ∀ i, Tendsto (fun k => eLpNorm (fn (derS i (ofSmooth (c := c) (r := r)
      (s := s + 1) (φ k) (hφ k))) - fn (derS i F)) 2 μB) atTop (𝓝 0) := by
    intro i
    have h1 := (fnL (c := c) (r := r) (s := s)).continuous.tendsto (derS i F) |>.comp
      ((derS i).continuous.tendsto F |>.comp hlim)
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h1
    exact h1
  have h0 := hcomp F _ hlim
  -- the smooth inequality
  have hk : ∀ k, eLpNorm (φ k) 4 μB ≤ ENNReal.ofReal K *
      (eLpNorm (φ k) 2 μB + ∑ i, eLpNorm (pd (φ k) i) 2 μB) := by
    intro k
    have h1 := hC c r hr.out (φ k) ((hφ k).of_le (by simp))
    refine h1.trans ?_
    calc (C : ℝ≥0∞) * (∑ i, eLpNorm (pd (φ k) i) 2 μB + ENNReal.ofReal r⁻¹ * eLpNorm (φ k) 2 μB)
        ≤ (C : ℝ≥0∞) * (ENNReal.ofReal (max 1 r⁻¹) * (eLpNorm (φ k) 2 μB +
            ∑ i, eLpNorm (pd (φ k) i) 2 μB)) := by
          gcongr
          rw [mul_add, add_comm]
          gcongr
          · exact le_max_right _ _
          · calc ∑ i, eLpNorm (pd (φ k) i) 2 μB = 1 * ∑ i, eLpNorm (pd (φ k) i) 2 μB := (one_mul _).symm
              _ ≤ ENNReal.ofReal (max 1 r⁻¹) * ∑ i, eLpNorm (pd (φ k) i) 2 μB := by
                  gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
      _ = ENNReal.ofReal K * (eLpNorm (φ k) 2 μB + ∑ i, eLpNorm (pd (φ k) i) 2 μB) := by
          rw [← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
  -- identify the smooth quantities with `fn` of the smooth elements
  have hfnk : ∀ k, fn (ofSmooth (c := c) (r := r) (s := s + 1) (φ k) (hφ k)) =ᵐ[μB] φ k :=
    fun k => fn_ofSmooth _
  have hdk : ∀ k i, fn (derS i (ofSmooth (c := c) (r := r) (s := s + 1) (φ k) (hφ k))) =ᵐ[μB]
      pd (φ k) i := fun k i => by rw [derS_ofSmooth]; exact fn_ofSmooth _
  -- the limit of the right side
  set R := ENNReal.ofReal K * (eLpNorm (fn F) 2 μB + ∑ i, eLpNorm (fn (derS i F)) 2 μB)
  have hR : Tendsto (fun k => ENNReal.ofReal K * (eLpNorm (φ k) 2 μB +
      ∑ i, eLpNorm (pd (φ k) i) 2 μB)) atTop (𝓝 R) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
    refine Tendsto.add ?_ (tendsto_finsetSum _ fun i _ => ?_)
    · have := tendsto_eLpNorm_of_sub (fun k => (memLp_fn _).aestronglyMeasurable)
        (memLp_fn F).aestronglyMeasurable (eLpNorm_fn_ne_top 2 F) (by norm_num) h0
      refine (this.congr fun k => ?_)
      exact eLpNorm_congr_ae (hfnk k)
    · have := tendsto_eLpNorm_of_sub (fun k => (memLp_fn _).aestronglyMeasurable)
        (memLp_fn _).aestronglyMeasurable (eLpNorm_fn_ne_top 2 _) (by norm_num) (hder i)
      refine (this.congr fun k => ?_)
      exact eLpNorm_congr_ae (hdk k i)
  -- lower semicontinuity of the `L⁴` norm
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    (fun k => (memLp_fn _).aestronglyMeasurable) (memLp_fn F).aestronglyMeasurable
    h0).exists_seq_tendsto_ae
  have hlsc := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 4)
    (fun k => (memLp_fn (ofSmooth (c := c) (r := r) (s := s + 1) (φ (ns k)) (hφ (ns k)))).aestronglyMeasurable)
    (fn F) hae
  have hle : eLpNorm (fn F) 4 μB ≤ R := by
    refine hlsc.trans ?_
    calc atTop.liminf (fun k => eLpNorm (fn (ofSmooth (c := c) (r := r) (s := s + 1) (φ (ns k))
          (hφ (ns k)))) 4 μB)
        ≤ atTop.liminf (fun k => ENNReal.ofReal K * (eLpNorm (φ (ns k)) 2 μB +
            ∑ i, eLpNorm (pd (φ (ns k)) i) 2 μB)) :=
          liminf_le_liminf (Eventually.of_forall fun k => by
            rw [eLpNorm_congr_ae (hfnk (ns k))]; exact hk (ns k))
      _ = R := (hR.comp hns.tendsto_atTop).liminf_eq
  -- conclude in real numbers
  unfold sN
  have hfin : R ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
    ⟨eLpNorm_fn_ne_top 2 F, ENNReal.sum_ne_top.mpr fun i _ => eLpNorm_fn_ne_top 2 _⟩)
  refine (ENNReal.toReal_mono hfin hle).trans (le_of_eq ?_)
  simp only [R]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_add
    (eLpNorm_fn_ne_top 2 F) (ENNReal.sum_ne_top.mpr fun i _ => eLpNorm_fn_ne_top 2 _),
    ENNReal.toReal_sum fun i _ => eLpNorm_fn_ne_top 2 _]

end RenewalGeometry.BallAnalysis.BallAlg
