/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.CoulombHodgeAbsorption
import RenewalGeometry.Analysis.LpDualityWeakCompactness
import RenewalGeometry.Analysis.MollifierLpConvergence

/-!
# Weak `W^{1,2}` compactness on a box, subcritical strong convergence, and weak curvature limits

Generic infrastructure (no renewal notions) for the compactness step of
`prop:critical-uhlenbeck` (Einstein–Standard-Model action-closure manuscript): once local Coulomb
gauges with uniform `W^{1,2}` bounds are available, the gauged connections are compact.

* `tendsto_Lq_of_L2_of_L4_bound`: on a finite measure space, `L²` convergence plus a uniform `L⁴`
  bound give `L^q` convergence for every `1 ≤ q < 4` (Vitali with `Φ(t) = t^{4/q}`);
* `w12_compactness_box` (**weak `W^{1,2}` compactness + Rellich on a box**, four dimensions):
  a finite family of sequences bounded in `W^{1,2}(Q)` has a common subsequence converging
  strongly in every `L^q(Q)`, `1 ≤ q < 4`, to `W^{1,2}(Q)` limits whose weak gradients are the weak
  `L²(Q)` limits of the gradients;
* `tendsto_integral_bdd_mul_mul`: products of two `L²`-convergent sequences pair convergently
  with bounded weights;
* `tendsto_integral_curvatureW` (**weak curvature limit**): if `A_k → A` strongly in `L²(Q)` and
  `∂A_k ⇀ ∂A` weakly in `L²(Q)`, then `F_{A_k} = dA_k + [A_k ∧ A_k] → F_A` against every bounded
  measurable weight.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.SobolevOpen

set_option linter.unusedSectionVars false

/-! ### Subcritical strong convergence -/

/-- **`L^q` convergence below the critical exponent**: on a finite measure space, if `f_k → g`
in `L²` and `‖f_k‖_{L⁴} ≤ B`, then `f_k → g` in `L^q` for every `1 ≤ q < 4`. -/
theorem tendsto_Lq_of_L2_of_L4_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {f : ℕ → X → ℂ} {g : X → ℂ} (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (hg : AEStronglyMeasurable g μ)
    (hL2 : Tendsto (fun k => eLpNorm (f k - g) 2 μ) atTop (𝓝 0)) {B : ℝ≥0}
    (hB : ∀ k, eLpNorm (f k) 4 μ ≤ B) {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hq4 : q < 4) :
    Tendsto (fun k => eLpNorm (f k - g) q μ) atTop (𝓝 0) := by
  have hqt : q ≠ ⊤ := ne_top_of_lt hq4
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos (by positivity) hqt
  have hq4' : q.toReal < 4 := by
    have := ENNReal.toReal_strict_mono (by norm_num) hq4
    simpa using this
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hf hg hL2
  set r : ℝ := 4 / q.toReal
  have hr1 : 1 < r := by rw [lt_div_iff₀ hq0]; linarith
  have hΦ : Tendsto (fun t : ℝ => t ^ r / t) atTop atTop := by
    refine (tendsto_rpow_atTop (by linarith : 0 < r - 1)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.rpow_sub ht, Real.rpow_one]
  refine (SuperlinearVitali.tendsto_Lp_of_tendstoInMeasure_of_superlinear hq1 hqt hf hmeas hΦ
    (M := (B : ℝ) ^ (4 : ℝ)) fun k => ?_).2
  have e : ∀ x, ENNReal.ofReal ((‖f k x‖ ^ q.toReal) ^ r) = ‖f k x‖ₑ ^ (4 : ℝ) := by
    intro x
    rw [← Real.rpow_mul (norm_nonneg _), show q.toReal * r = 4 by
      simp only [r]; field_simp, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
      (by norm_num)]
  simp_rw [e]
  have h4 := eLpNorm_nnreal_pow_eq_lintegral (f := f k) (μ := μ) (p := 4) (by norm_num)
  have e4 : ((4 : ℝ≥0) : ℝ≥0∞) = 4 := by norm_num
  rw [e4] at h4
  push_cast at h4
  rw [← h4, ← ENNReal.ofReal_rpow_of_nonneg B.coe_nonneg (by norm_num), ENNReal.ofReal_coe_nnreal]
  exact ENNReal.rpow_le_rpow (hB k) (by norm_num)

/-! ### Weak `W^{1,2}` compactness on a box -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Weak `W^{1,2}` compactness and Rellich on a box (four dimensions).**  A finite family
`(u_k^p)_{p ∈ P}` bounded in `W^{1,2}(Q)` has a common subsequence and limits `v^p ∈ W^{1,2}(Q)`
(weak gradients `G^p`) such that `u_k^p → v^p` strongly in `L^q(Q)` for every `1 ≤ q < 4`, and
`∂_μ u_k^p ⇀ G^p_μ` weakly in `L²(Q)`. -/
theorem w12_compactness_box (hd : Fintype.card ι = 4) {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    {P : Type*} [Fintype P] (u : ℕ → P → (ι → ℝ) → ℂ) (g : ℕ → P → ι → (ι → ℝ) → ℂ)
    (hW : ∀ k p, MemW12 (box a b) (u k p) (g k p)) {B : ℝ≥0∞} (hBt : B ≠ ⊤)
    (hB : ∀ k p, w12Norm (box a b) (u k p) (g k p) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (v : P → (ι → ℝ) → ℂ) (G : P → ι → (ι → ℝ) → ℂ),
      (∀ p, MemW12 (box a b) (v p) (G p)) ∧
      (∀ p (q : ℝ≥0∞), 1 ≤ q → q < 4 →
        Tendsto (fun k => eLpNorm (u (φ k) p - v p) q (volume.restrict (box a b))) atTop
          (𝓝 0)) ∧
      (∀ p μ (h : (ι → ℝ) → ℝ), MemLp h 2 (volume.restrict (box a b)) →
        Tendsto (fun k => ∫ x, h x • g (φ k) p μ x ∂(volume.restrict (box a b))) atTop
          (𝓝 (∫ x, h x • G p μ x ∂(volume.restrict (box a b))))) := by
  classical
  set ρ := volume.restrict (box a b)
  have : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr (volume_box_ne_top a b)
  set Q := box a b
  have hQo : IsOpen Q := isOpen_box a b
  -- Rellich for the finite family
  set e := Fintype.equivFin P
  obtain ⟨φ1, v', hφ1, hv', hlim'⟩ := rellich_box_family hab (fun k c => u k (e.symm c))
    (fun k c => g k (e.symm c)) (fun k c => hW k _) hBt (fun k c => hB k _)
  set v : P → (ι → ℝ) → ℂ := fun p => v' (e p)
  have hlimv : ∀ p, Tendsto (fun k => eLpNorm (u (φ1 k) p - v p) 2 ρ) atTop (𝓝 0) := by
    intro p
    have := hlim' (e p)
    simpa [v] using this
  -- weak limits of the gradients
  have hgB : ∀ k p μ, eLpNorm (g k p μ) 2 ρ ≤ B := fun k p μ =>
    (Finset.single_le_sum (f := fun μ => eLpNorm (g k p μ) 2 ρ) (fun _ _ => zero_le)
      (Finset.mem_univ μ)).trans (le_add_self.trans (hB k p))
  obtain ⟨ψ, hψ, G', hG'⟩ := LpDuality.exists_subseq_tendsto_weak_family_vec (μ := ρ)
    (p := 2) (q := 2) (V := ℂ) (by norm_num) (by norm_num)
    (fun (pm : P × ι) n => g (φ1 n) pm.1 pm.2) (fun pm n => (hW _ pm.1).memLp_grad pm.2) hBt
    (fun pm n => hgB _ _ _)
  set φ := φ1 ∘ ψ
  set G : P → ι → (ι → ℝ) → ℂ := fun p μ => G' (p, μ)
  have hweak : ∀ p μ (h : (ι → ℝ) → ℝ), MemLp h 2 ρ →
      Tendsto (fun k => ∫ x, h x • g (φ k) p μ x ∂ρ) atTop (𝓝 (∫ x, h x • G p μ x ∂ρ)) :=
    fun p μ h hh => (hG' (p, μ)).2 h hh
  have hlim : ∀ p, Tendsto (fun k => eLpNorm (u (φ k) p - v p) 2 ρ) atTop (𝓝 0) :=
    fun p => (hlimv p).comp hψ.tendsto_atTop
  -- the limits lie in `W^{1,2}(Q)`
  have hvL2 : ∀ p, MemLp (v p) 2 ρ := fun p => (hv' (e p)).restrict Q
  have hmem : ∀ p, MemW12 Q (v p) (G p) := by
    intro p
    refine ⟨hvL2 p, fun μ => (hG' (p, μ)).1, fun μ φt hφt => ?_⟩
    have h0 : ∀ x, x ∉ Q → φt x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hφt.subset h)
    have h1 := tendsto_integral_test_of_L2 hQo.measurableSet (volume_box_ne_top a b)
      (hφt.pd μ) (fun k => (hW (φ k) p).memLp) (hvL2 p) (hlim p)
    have hφL2 : MemLp φt 2 ρ := by
      obtain ⟨M, hM⟩ := hφt.exists_bound
      exact MemLp.of_bound hφt.continuous.aestronglyMeasurable M
        (Eventually.of_forall fun x => hM x)
    have h2 := (hweak p μ φt hφL2).neg
    have hset : ∀ w : (ι → ℝ) → ℂ, ∫ x, φt x • w x ∂ρ = ∫ x, ((φt x : ℝ) : ℂ) * w x := by
      intro w
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [h0 x hx]]
      simp only [Complex.real_smul]
    simp only [hset] at h2
    have h3 : Tendsto (fun k => ∫ x, ((pd φt μ x : ℝ) : ℂ) * u (φ k) p x) atTop
        (𝓝 (-∫ x, ((φt x : ℝ) : ℂ) * G p μ x)) :=
      h2.congr fun k => ((hW (φ k) p).weak μ φt hφt).symm
    exact tendsto_nhds_unique h1 h3
  -- subcritical strong convergence
  obtain ⟨CS, hCS⟩ := exists_sobolev_L4_box hd hab
  refine ⟨φ, hφ1.comp hψ, v, G, hmem, fun p q hq1 hq4 => ?_, hweak⟩
  refine tendsto_Lq_of_L2_of_L4_bound (fun k => (hW (φ k) p).memLp.1) (hvL2 p).1 (hlim p)
    (B := CS * B.toNNReal) (fun k => ?_) hq1 hq4
  refine (hCS _ _ (hW (φ k) p)).trans ?_
  push_cast
  rw [ENNReal.coe_toNNReal hBt]
  exact mul_le_mul_right (hB _ _) _

/-! ### Weak curvature limits -/

section Curvature

variable {X : Type*} [MeasurableSpace X] {ρ : Measure X} [IsFiniteMeasure ρ]

/-- Products of two `L²`-convergent sequences pair convergently with a bounded weight. -/
theorem tendsto_integral_bdd_mul_mul {f g : ℕ → X → ℂ} {f₀ g₀ : X → ℂ}
    (hf : LpTendsto ρ 2 f f₀) (hg : LpTendsto ρ 2 g g₀) {h : X → ℝ} (hh : MemLp h ⊤ ρ) :
    Tendsto (fun k => ∫ x, h x • (f k x * g k x) ∂ρ) atTop
      (𝓝 (∫ x, h x • (f₀ x * g₀ x) ∂ρ)) := by
  have h1 : LpTendsto ρ 1 (fun k x => ContinuousLinearMap.mul ℝ ℂ (f k x) (g k x))
      (fun x => ContinuousLinearMap.mul ℝ ℂ (f₀ x) (g₀ x)) :=
    LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.mul ℝ ℂ) hf hg
  have h2 := LpTendsto.bilin (p := ⊤) (q := 1) (r := 1)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) (LpTendsto.const hh) h1
  simpa using h2.tendsto_integral

theorem integrable_smul_of_memLp_two {h : X → ℝ} (hh : MemLp h ⊤ ρ) {F : X → ℂ}
    (hF : MemLp F 2 ρ) : Integrable (fun x => h x • F x) ρ :=
  ((hF.smul hh : MemLp (h • F) 2 ρ).integrable one_le_two)

theorem integrable_smul_of_memLp_one {h : X → ℝ} (hh : MemLp h ⊤ ρ) {F : X → ℂ}
    (hF : MemLp F 1 ρ) : Integrable (fun x => h x • F x) ρ :=
  memLp_one_iff_integrable.mp (hF.smul hh : MemLp (h • F) 1 ρ)

end Curvature

/-- **Weak curvature limit.**  Let `A_k → A₀` strongly in `L²(ρ)` (entrywise) with gradients
`∂A_k ∈ L²(ρ)` converging weakly to `∂A₀` (against `L²` weights).  Then for every bounded
measurable weight `h`, `∫ h F_{A_k} → ∫ h F_{A₀}` (`F = dA + [A ∧ A]`, `curvatureW`); together
with a uniform `L²` bound on `F_{A_k}` this is weak `L²` convergence `F_{A_k} ⇀ F_{A₀}`. -/
theorem tendsto_integral_curvatureW {m : ℕ} {ρ : Measure (ι → ℝ)} [IsFiniteMeasure ρ]
    {A : ℕ → ι → Fin m → Fin m → (ι → ℝ) → ℂ} {dA : ℕ → ι → Fin m → Fin m → ι → (ι → ℝ) → ℂ}
    {A₀ : ι → Fin m → Fin m → (ι → ℝ) → ℂ} {dA₀ : ι → Fin m → Fin m → ι → (ι → ℝ) → ℂ}
    (hA : ∀ ν c e, LpTendsto ρ 2 (fun k => A k ν c e) (A₀ ν c e))
    (hdAm : ∀ k ν c e μ, MemLp (dA k ν c e μ) 2 ρ) (hdA₀m : ∀ ν c e μ, MemLp (dA₀ ν c e μ) 2 ρ)
    (hdA : ∀ ν c e μ (h : (ι → ℝ) → ℝ), MemLp h 2 ρ →
      Tendsto (fun k => ∫ x, h x • dA k ν c e μ x ∂ρ) atTop (𝓝 (∫ x, h x • dA₀ ν c e μ x ∂ρ)))
    {h : (ι → ℝ) → ℝ} (hh : MemLp h ⊤ ρ) (μ ν : ι) (c e : Fin m) :
    Tendsto (fun k => ∫ x, h x • curvatureW (A k) (dA k) μ ν c e x ∂ρ) atTop
      (𝓝 (∫ x, h x • curvatureW A₀ dA₀ μ ν c e x ∂ρ)) := by
  have hh2 : MemLp h 2 ρ := hh.mono_exponent le_top
  -- splitting of the integral
  have hprod : ∀ (B : ι → Fin m → Fin m → (ι → ℝ) → ℂ), (∀ ν c e, MemLp (B ν c e) 2 ρ) →
      ∀ μ ν c e j, Integrable (fun x => h x • (B μ c j x * B ν j e x)) ρ := by
    intro B hB μ ν c e j
    refine integrable_smul_of_memLp_one hh ?_
    have := (hB ν j e).smul (p := 2) (q := 2) (r := 1) (hB μ c j)
    exact this
  have hsplit : ∀ (B : ι → Fin m → Fin m → (ι → ℝ) → ℂ)
      (dB : ι → Fin m → Fin m → ι → (ι → ℝ) → ℂ), (∀ ν c e, MemLp (B ν c e) 2 ρ) →
      (∀ ν c e μ, MemLp (dB ν c e μ) 2 ρ) →
      ∫ x, h x • curvatureW B dB μ ν c e x ∂ρ =
        (∫ x, h x • dB ν c e μ x ∂ρ) - (∫ x, h x • dB μ c e ν x ∂ρ) +
          ∑ j, ((∫ x, h x • (B μ c j x * B ν j e x) ∂ρ) -
            ∫ x, h x • (B ν c j x * B μ j e x) ∂ρ) := by
    intro B dB hB hdB
    have i1 := integrable_smul_of_memLp_two hh (hdB ν c e μ)
    have i2 := integrable_smul_of_memLp_two hh (hdB μ c e ν)
    have i3 := hprod B hB μ ν c e
    have i4 := hprod B hB ν μ c e
    have e1 : (fun x => h x • curvatureW B dB μ ν c e x) = fun x =>
        (h x • dB ν c e μ x - h x • dB μ c e ν x) +
          ∑ j, (h x • (B μ c j x * B ν j e x) - h x • (B ν c j x * B μ j e x)) := by
      funext x
      simp only [curvatureW, smul_add, smul_sub, Finset.smul_sum]
    rw [e1]
    have j1 : ∫ x, (h x • dB ν c e μ x - h x • dB μ c e ν x) +
        ∑ j, (h x • (B μ c j x * B ν j e x) - h x • (B ν c j x * B μ j e x)) ∂ρ =
        (∫ x, h x • dB ν c e μ x - h x • dB μ c e ν x ∂ρ) +
          ∫ x, ∑ j, (h x • (B μ c j x * B ν j e x) - h x • (B ν c j x * B μ j e x)) ∂ρ :=
      integral_add (i1.sub i2) (integrable_finset_sum _ fun j _ => (i3 j).sub (i4 j))
    have j2 : ∫ x, h x • dB ν c e μ x - h x • dB μ c e ν x ∂ρ =
        (∫ x, h x • dB ν c e μ x ∂ρ) - ∫ x, h x • dB μ c e ν x ∂ρ := integral_sub i1 i2
    have j3 : ∫ x, ∑ j, (h x • (B μ c j x * B ν j e x) - h x • (B ν c j x * B μ j e x)) ∂ρ =
        ∑ j, ∫ x, (h x • (B μ c j x * B ν j e x) - h x • (B ν c j x * B μ j e x)) ∂ρ :=
      integral_finset_sum _ fun j _ => (i3 j).sub (i4 j)
    rw [j1, j2, j3]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => integral_sub (i3 j) (i4 j))
  have hAm : ∀ k ν c e, MemLp (A k ν c e) 2 ρ := fun k ν c e => (hA ν c e).memLp k
  have hA₀m : ∀ ν c e, MemLp (A₀ ν c e) 2 ρ := fun ν c e => (hA ν c e).memLp_lim
  simp only [hsplit _ _ (hAm _) (hdAm _), hsplit _ _ hA₀m hdA₀m]
  refine ((hdA ν c e μ h hh2).sub (hdA μ c e ν h hh2)).add (tendsto_finset_sum _ fun j _ => ?_)
  exact (tendsto_integral_bdd_mul_mul (hA μ c j) (hA ν j e) hh).sub
    (tendsto_integral_bdd_mul_mul (hA ν c j) (hA μ j e) hh)

end RenewalGeometry.SobolevOpen
