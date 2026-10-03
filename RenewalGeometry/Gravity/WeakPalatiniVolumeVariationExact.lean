/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.WeakPalatiniPassageExact
import RenewalGeometry.Continuum.WeakStrongPalatiniLebesgueExact

/-!
# Volume (cosmological-term) first variation in the weak-curvature Palatini passage
  (`prop:weak-palatini`, Einstein–SM action closure)

`WeakPalatiniPassageExact` proves the Palatini-pairing, volume-density and Palatini-variation
clauses of `prop:weak-palatini`.  This file adds the remaining part of "their coframe first
variations also converge": the variation of the volume (cosmological) term, a bounded
four-linear density with one slot filled by the coframe variation `k` and three by the coframe
`e`, `vol(k_h, e_h, e_h, e_h) → vol(k, e, e, e)` in `L¹` (the full volume variation is the
sum of the four slot positions, each of which is of this form for a permuted `vol`).

* `norm_multilinear_four_sub_le` — pointwise telescoping bound
  `‖vol(a) - vol(b)‖ ≤ 4 ‖vol‖ (Σ_j ‖a_j - b_j‖) (Σ_j (‖a_j‖ + ‖b_j‖))³`;
* `eLpNorm_multilinear_four_tendsto_zero` — the general four-factor `L⁴ × L⁴ × L⁴ × L⁴ → L¹`
  passage: if each slot converges in `L⁴` with uniform `L⁴` bounds, the four-linear densities
  converge in `L¹` (four-factor Hölder estimate `eLpNorm_fourFactor_le`);
* `eLpNorm_volume_variation_tendsto_zero` — the volume-variation clause under
  `eq:Palatini-hypotheses` (coframes and variations converge in `L²`, bounded in `L⁶`, on a
  finite measure space; `L⁴` convergence by `L²`–`L⁶` interpolation);
* `weak_palatini_passage_with_volume_variation` — `weak_palatini_passage` together with the
  volume-variation clause (all conclusions of the proposition with formal content);
* `weak_palatini_passage_lp` — the same conclusions from the literal hypotheses
  `eq:Palatini-hypotheses` for cutoff sequences: `R_h ⇀ R` weakly in `L^p` (every continuous
  linear functional on `Lp`), with the uniform `L^p` bound (Banach–Steinhaus), the pairing
  convergence and the limit `L⁶` bounds (Fatou) derived rather than assumed.
-/

open MeasureTheory ENNReal Filter Topology

namespace RenewalGeometry.WeakPalatiniPassage

variable {α E Biv Curv : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Biv] [NormedSpace ℝ Biv]
  [NormedAddCommGroup Curv] [NormedSpace ℝ Curv]

/-- Pointwise telescoping bound for a bounded four-linear map:
`‖vol(a) - vol(b)‖ ≤ 4‖vol‖ (Σ_j ‖a_j - b_j‖) (Σ_j (‖a_j‖ + ‖b_j‖))³`. -/
theorem norm_multilinear_four_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (vol : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) V) (a b : Fin 4 → E) :
    ‖vol a - vol b‖ ≤ (4 * ‖vol‖) * (∑ j, ‖a j - b j‖) * (∑ j, (‖a j‖ + ‖b j‖)) *
      (∑ j, (‖a j‖ + ‖b j‖)) * (∑ j, (‖a j‖ + ‖b j‖)) := by
  have h := vol.norm_image_sub_le a b
  simp only [Fintype.card_fin, Nat.cast_ofNat, Nat.add_one_sub_one] at h
  set S : ℝ := ∑ j, (‖a j‖ + ‖b j‖) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by positivity
  have hsingle : ∀ j, ‖a j‖ + ‖b j‖ ≤ S := fun j =>
    Finset.single_le_sum (f := fun j => ‖a j‖ + ‖b j‖) (fun j _ => by positivity)
      (Finset.mem_univ j)
  have ha : ‖a‖ ≤ S := (pi_norm_le_iff_of_nonneg hS0).2 fun j =>
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hsingle j)
  have hb : ‖b‖ ≤ S := (pi_norm_le_iff_of_nonneg hS0).2 fun j =>
    (le_add_of_nonneg_left (norm_nonneg _)).trans (hsingle j)
  have hmax : max ‖a‖ ‖b‖ ≤ S := max_le ha hb
  have hD0 : 0 ≤ ∑ j, ‖a j - b j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hdiff : ‖a - b‖ ≤ ∑ j, ‖a j - b j‖ := (pi_norm_le_iff_of_nonneg hD0).2 fun j =>
    Finset.single_le_sum (f := fun j => ‖a j - b j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ j)
  refine h.trans ?_
  calc ‖vol‖ * 4 * max ‖a‖ ‖b‖ ^ 3 * ‖a - b‖
      ≤ ‖vol‖ * 4 * S ^ 3 * (∑ j, ‖a j - b j‖) := by gcongr
    _ = (4 * ‖vol‖) * (∑ j, ‖a j - b j‖) * S * S * S := by ring

/-- `L⁴` Minkowski bound for a four-term sum of real functions. -/
theorem eLpNorm'_four_sum_le (u : Fin 4 → α → ℝ) (hu : ∀ j, AEStronglyMeasurable (u j) μ) :
    eLpNorm' (fun x => ∑ j, u j x) 4 μ ≤ ∑ j, eLpNorm' (u j) 4 μ := by
  simp only [Fin.sum_univ_four]
  have h4 : (1 : ℝ) ≤ 4 := by norm_num
  have e1 := eLpNorm'_add_le ((hu 0).add (hu 1) |>.add (hu 2)) (hu 3) h4
  have e2 := eLpNorm'_add_le ((hu 0).add (hu 1)) (hu 2) h4
  have e3 := eLpNorm'_add_le (hu 0) (hu 1) h4
  calc eLpNorm' (fun x => u 0 x + u 1 x + u 2 x + u 3 x) 4 μ
      = eLpNorm' (u 0 + u 1 + u 2 + u 3) 4 μ := rfl
    _ ≤ eLpNorm' (u 0 + u 1 + u 2) 4 μ + eLpNorm' (u 3) 4 μ := e1
    _ ≤ eLpNorm' (u 0 + u 1) 4 μ + eLpNorm' (u 2) 4 μ + eLpNorm' (u 3) 4 μ := by gcongr
    _ ≤ eLpNorm' (u 0) 4 μ + eLpNorm' (u 1) 4 μ + eLpNorm' (u 2) 4 μ + eLpNorm' (u 3) 4 μ := by
        gcongr

/-- **Four-factor passage `L⁴ × L⁴ × L⁴ × L⁴ → L¹`.**  If each of the four slots converges in
`L⁴` (`‖f_j(i) - f_j‖₄ → 0`) with uniform `L⁴` bounds `‖f_j(i)‖₄, ‖f_j‖₄ ≤ M`, then for every
bounded four-linear `vol`, `vol(f_0(i), …, f_3(i)) → vol(f_0, …, f_3)` in `L¹`. -/
theorem eLpNorm_multilinear_four_tendsto_zero {ι : Type*} {l : Filter ι}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (vol : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) V)
    (f : Fin 4 → ι → α → E) (f₀ : Fin 4 → α → E)
    (hf : ∀ j i, AEStronglyMeasurable (f j i) μ) (hf₀ : ∀ j, AEStronglyMeasurable (f₀ j) μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (hb : ∀ j i, eLpNorm' (f j i) 4 μ ≤ M)
    (hb₀ : ∀ j, eLpNorm' (f₀ j) 4 μ ≤ M)
    (hconv : ∀ j, Tendsto (fun i => eLpNorm' (f j i - f₀ j) 4 μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (fun x => vol (fun j => f j i x) - vol (fun j => f₀ j x)) 1 μ) l
      (𝓝 0) := by
  set Dn : ι → α → ℝ := fun i x => ∑ j, ‖f j i x - f₀ j x‖ with hDn
  set Sn : ι → α → ℝ := fun i x => ∑ j, (‖f j i x‖ + ‖f₀ j x‖) with hSn
  have hDm : ∀ i, AEStronglyMeasurable (Dn i) μ := fun i => by
    have : Dn i = ∑ j, fun x => ‖f j i x - f₀ j x‖ := by
      funext x; simp [hDn, Finset.sum_apply]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun j _ => ((hf j i).sub (hf₀ j)).norm
  have hSm : ∀ i, AEStronglyMeasurable (Sn i) μ := fun i => by
    have : Sn i = ∑ j, fun x => ‖f j i x‖ + ‖f₀ j x‖ := by
      funext x; simp [hSn, Finset.sum_apply]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun j _ => (hf j i).norm.add (hf₀ j).norm
  -- L⁴ bounds of the majorants
  have hD4 : ∀ i, eLpNorm' (Dn i) 4 μ ≤ ∑ j, eLpNorm' (f j i - f₀ j) 4 μ := fun i => by
    refine (eLpNorm'_four_sum_le (fun j x => ‖f j i x - f₀ j x‖)
      (fun j => ((hf j i).sub (hf₀ j)).norm)).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    exact eLpNorm'_norm (f := f j i - f₀ j)
  have hS4 : ∀ i, eLpNorm' (Sn i) 4 μ ≤ ∑ _j : Fin 4, (M + M) := fun i => by
    refine (eLpNorm'_four_sum_le (fun j x => ‖f j i x‖ + ‖f₀ j x‖)
      (fun j => (hf j i).norm.add (hf₀ j).norm)).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    have := eLpNorm'_add_le (hf j i).norm (hf₀ j).norm (by norm_num : (1 : ℝ) ≤ 4)
    rw [eLpNorm'_norm, eLpNorm'_norm] at this
    exact this.trans (add_le_add (hb j i) (hb₀ j))
  set S : ℝ≥0∞ := ∑ _j : Fin 4, (M + M) with hS
  have hSne : S ≠ ∞ := by
    rw [hS]
    exact ENNReal.sum_ne_top.2 fun j _ => ENNReal.add_ne_top.2 ⟨hM, hM⟩
  set D : ℝ≥0∞ := ((4 * ‖vol‖₊ : NNReal) : ℝ≥0∞) * S * S * S with hD
  have hDne : D ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hSne) hSne) hSne
  have hest : ∀ i, eLpNorm (fun x => vol (fun j => f j i x) - vol (fun j => f₀ j x)) 1 μ ≤
      D * ∑ j, eLpNorm' (f j i - f₀ j) 4 μ := fun i => by
    have h := eLpNorm_fourFactor_le (fun x => vol (fun j => f j i x) - vol (fun j => f₀ j x))
      (Dn i) (Sn i) (Sn i) (Sn i) (hDm i) (hSm i) (hSm i) (hSm i) (4 * ‖vol‖₊)
      (fun x => by
        have := norm_multilinear_four_sub_le vol (fun j => f j i x) (fun j => f₀ j x)
        have hD0 : 0 ≤ Dn i x := Finset.sum_nonneg fun j _ => norm_nonneg _
        have hS0 : 0 ≤ Sn i x := Finset.sum_nonneg fun j _ => by positivity
        rw [Real.norm_of_nonneg hD0, Real.norm_of_nonneg hS0]
        simpa [hDn, hSn, NNReal.coe_mul] using this)
    refine h.trans ?_
    calc ((4 * ‖vol‖₊ : NNReal) : ℝ≥0∞) * eLpNorm' (Dn i) 4 μ * eLpNorm' (Sn i) 4 μ *
          eLpNorm' (Sn i) 4 μ * eLpNorm' (Sn i) 4 μ
        ≤ ((4 * ‖vol‖₊ : NNReal) : ℝ≥0∞) * (∑ j, eLpNorm' (f j i - f₀ j) 4 μ) * S * S * S := by
          gcongr
          · exact hD4 i
          all_goals exact hS4 i
      _ = D * ∑ j, eLpNorm' (f j i - f₀ j) 4 μ := by rw [hD]; ring
  have hsum : Tendsto (fun i => ∑ j, eLpNorm' (f j i - f₀ j) 4 μ) l (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun j _ => hconv j
    simpa using this
  have hmajor : Tendsto (fun i => D * ∑ j, eLpNorm' (f j i - f₀ j) 4 μ) l (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hsum (Or.inr hDne)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor (fun _ => zero_le) hest

/-- `L⁴` bound from an `L⁶` bound on a finite measure space. -/
theorem eLpNorm'_four_le_of_six [IsFiniteMeasure μ] (f : α → E) (hf : AEStronglyMeasurable f μ)
    (M : ℝ≥0∞) (h6 : eLpNorm' f 6 μ ≤ M) :
    eLpNorm' f 4 μ ≤ M * μ Set.univ ^ (1 / (4 : ℝ) - 1 / 6) :=
  (eLpNorm'_four_le f hf).trans (by gcongr)

/-- **`prop:weak-palatini`, volume (cosmological-term) variation clause.**  Under
`eq:Palatini-hypotheses` on a finite measure space — coframes `e_h → e` and represented coframe
variations `k_h → k` in `L²`, all bounded in `L⁶` by `M` — the volume-variation densities
converge in `L¹`: `vol(k_h, e_h, e_h, e_h) → vol(k, e, e, e)` for every bounded four-linear
`vol`.  (The full volume variation `Σ_slot vol(…, k, …)` is a sum of four such terms with
permuted `vol`.) -/
theorem eLpNorm_volume_variation_tendsto_zero {ι : Type*} {l : Filter ι} [IsFiniteMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (vol : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) V)
    (e : ι → α → E) (e₀ : α → E) (k : ι → α → E) (k₀ : α → E)
    (he : ∀ i, AEStronglyMeasurable (e i) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (hk : ∀ i, AEStronglyMeasurable (k i) μ) (hk₀ : AEStronglyMeasurable k₀ μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (h6 : ∀ i, eLpNorm' (e i) 6 μ ≤ M) (h6₀ : eLpNorm' e₀ 6 μ ≤ M)
    (hk6 : ∀ i, eLpNorm' (k i) 6 μ ≤ M) (hk6₀ : eLpNorm' k₀ 6 μ ≤ M)
    (h2 : Tendsto (fun i => eLpNorm' (e i - e₀) 2 μ) l (𝓝 0))
    (hk2 : Tendsto (fun i => eLpNorm' (k i - k₀) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (fun x => vol ![k i x, e i x, e i x, e i x] -
        vol ![k₀ x, e₀ x, e₀ x, e₀ x]) 1 μ) l (𝓝 0) := by
  set f : Fin 4 → ι → α → E := fun j i => if j = 0 then k i else e i with hf
  set f₀ : Fin 4 → α → E := fun j => if j = 0 then k₀ else e₀ with hf₀
  have hvec : ∀ i x, (fun j => f j i x) = ![k i x, e i x, e i x, e i x] := fun i x => by
    funext j; fin_cases j <;> simp [hf]
  have hvec₀ : ∀ x, (fun j => f₀ j x) = ![k₀ x, e₀ x, e₀ x, e₀ x] := fun x => by
    funext j; fin_cases j <;> simp [hf₀]
  set V₄ : ℝ≥0∞ := μ Set.univ ^ (1 / (4 : ℝ) - 1 / 6) with hV₄
  have hV₄ne : V₄ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ _)
  have hmain := eLpNorm_multilinear_four_tendsto_zero (μ := μ) (l := l) vol f f₀
    (fun j i => by by_cases hj : j = 0 <;> simp [hf, hj, he, hk])
    (fun j => by by_cases hj : j = 0 <;> simp [hf₀, hj, he₀, hk₀])
    (M * V₄) (ENNReal.mul_ne_top hM hV₄ne)
    (fun j i => by
      by_cases hj : j = 0
      · simp only [hf, hj, ite_true]; exact eLpNorm'_four_le_of_six _ (hk i) M (hk6 i)
      · simp only [hf, hj, ite_false]; exact eLpNorm'_four_le_of_six _ (he i) M (h6 i))
    (fun j => by
      by_cases hj : j = 0
      · simp only [hf₀, hj, ite_true]; exact eLpNorm'_four_le_of_six _ hk₀ M hk6₀
      · simp only [hf₀, hj, ite_false]; exact eLpNorm'_four_le_of_six _ he₀ M h6₀)
    (fun j => by
      by_cases hj : j = 0
      · simp only [hf, hf₀, hj, ite_true]
        exact eLpNorm'_four_tendsto_zero k k₀ hk hk₀ M hM hk6 hk6₀ hk2
      · simp only [hf, hf₀, hj, ite_false]
        exact eLpNorm'_four_tendsto_zero e e₀ he he₀ M hM h6 h6₀ h2)
  refine hmain.congr fun i => ?_
  congr 1
  funext x
  rw [hvec i x, hvec₀ x]

/-- **`prop:weak-palatini`** (bundled, all clauses with formal content).  On a finite measure
space under `eq:Palatini-hypotheses`: (1) `B(e_h) → B(e)` in `L^{p'}`; (2) the Palatini
pairings converge; (3) the volume densities converge in `L¹`; (4) for represented coframe
variations `k_h → k` in `L²`, bounded in `L⁶`, the Palatini first-variation pairings converge
and (5) the volume first-variation densities `vol(k_h, e_h, e_h, e_h) → vol(k, e, e, e)` in
`L¹`. -/
theorem weak_palatini_passage_with_volume_variation {ι : Type*} {l : Filter ι}
    [IsFiniteMeasure μ] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : E →L[ℝ] E →L[ℝ] Biv) (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ)
    (vol : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) V) (p : ℝ) (hp : 3 / 2 < p)
    (e : ι → α → E) (e₀ : α → E)
    (he : ∀ i, AEStronglyMeasurable (e i) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (h6 : ∀ i, eLpNorm' (e i) 6 μ ≤ M) (h6₀ : eLpNorm' e₀ 6 μ ≤ M)
    (h2 : Tendsto (fun i => eLpNorm' (e i - e₀) 2 μ) l (𝓝 0))
    (R : ι → α → Curv) (R₀ : α → Curv) (hR : ∀ i, AEStronglyMeasurable (R i) μ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hRb : ∀ i, eLpNorm (R i) (ENNReal.ofReal p) μ ≤ C)
    (hweak : ∀ φ : α → Biv, MemLp φ (ENNReal.ofReal (p / (p - 1))) μ →
      Tendsto (fun i => ∫ x, pr (φ x) (R i x) ∂μ) l (𝓝 (∫ x, pr (φ x) (R₀ x) ∂μ))) :
    Tendsto (fun i => eLpNorm (fun x => w (e i x) (e i x) - w (e₀ x) (e₀ x))
        (ENNReal.ofReal (p / (p - 1))) μ) l (𝓝 0) ∧
    Tendsto (fun i => ∫ x, pr (w (e i x) (e i x)) (R i x) ∂μ) l
      (𝓝 (∫ x, pr (w (e₀ x) (e₀ x)) (R₀ x) ∂μ)) ∧
    Tendsto (fun i => eLpNorm (fun x => vol (fun _ => e i x) - vol (fun _ => e₀ x)) 1 μ) l
      (𝓝 0) ∧
    (∀ (k : ι → α → E) (k₀ : α → E), (∀ i, AEStronglyMeasurable (k i) μ) →
      AEStronglyMeasurable k₀ μ → (∀ i, eLpNorm' (k i) 6 μ ≤ M) → eLpNorm' k₀ 6 μ ≤ M →
      Tendsto (fun i => eLpNorm' (k i - k₀) 2 μ) l (𝓝 0) →
      Tendsto (fun i => ∫ x, pr (w (e i x) (k i x)) (R i x) ∂μ) l
        (𝓝 (∫ x, pr (w (e₀ x) (k₀ x)) (R₀ x) ∂μ)) ∧
      Tendsto (fun i => eLpNorm (fun x => vol ![k i x, e i x, e i x, e i x] -
        vol ![k₀ x, e₀ x, e₀ x, e₀ x]) 1 μ) l (𝓝 0)) := by
  obtain ⟨h1, h2', h3, h4⟩ := weak_palatini_passage w pr vol p hp e e₀ he he₀ M hM h6 h6₀ h2
    R R₀ hR C hC hRb hweak
  refine ⟨h1, h2', h3, fun k k₀ hk hk₀ hk6 hk6₀ hk2 => ⟨h4 k k₀ hk hk₀ hk6 hk6₀ hk2, ?_⟩⟩
  exact eLpNorm_volume_variation_tendsto_zero vol e e₀ k k₀ he he₀ hk hk₀ M hM h6 h6₀ hk6 hk6₀
    h2 hk2

/-- **`prop:weak-palatini`, literal hypotheses** (`eq:Palatini-hypotheses` on a finite measure
space, cutoff sequences indexed by `ℕ`): `e_h → e` in `L²`, `sup_h ‖e_h‖₆ ≤ M`, `p > 3/2` and
`R_h ⇀ R` weakly in `L^p` (every continuous linear functional on `L^p` converges).  The limit
bound `‖e‖₆ ≤ M` (Fatou), the uniform bound `sup_h ‖R_h‖_p < ∞` (Banach–Steinhaus) and the
convergence of all `L^{p'}` pairings are derived.  Conclusions: (1) `B(e_h) → B(e)` in `L^{p'}`;
(2) the Palatini pairings converge; (3) the volume densities converge in `L¹`; and for
represented coframe variations `k_h → k` in `L²` with `sup_h ‖k_h‖₆ ≤ M`: (4) the Palatini
first-variation pairings converge and (5) the volume first-variation densities converge in
`L¹`. -/
theorem weak_palatini_passage_lp [IsFiniteMeasure μ] {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (w : E →L[ℝ] E →L[ℝ] Biv) (pr : Biv →L[ℝ] Curv →L[ℝ] ℝ)
    (vol : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) V) (p : ℝ) (hp : 3 / 2 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (e : ℕ → α → E) (e₀ : α → E)
    (he : ∀ i, AEStronglyMeasurable (e i) μ) (he₀ : AEStronglyMeasurable e₀ μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (h6 : ∀ i, eLpNorm' (e i) 6 μ ≤ M)
    (h2 : Tendsto (fun i => eLpNorm' (e i - e₀) 2 μ) atTop (𝓝 0))
    (R : ℕ → Lp Curv (ENNReal.ofReal p) μ) (R₀ : Lp Curv (ENNReal.ofReal p) μ)
    (hR : WeakStrongPalatiniLebesgue.LpWeakTendsto R R₀) :
    Tendsto (fun i => eLpNorm (fun x => w (e i x) (e i x) - w (e₀ x) (e₀ x))
        (ENNReal.ofReal (p / (p - 1))) μ) atTop (𝓝 0) ∧
    Tendsto (fun i => ∫ x, pr (w (e i x) (e i x)) (R i x) ∂μ) atTop
      (𝓝 (∫ x, pr (w (e₀ x) (e₀ x)) (R₀ x) ∂μ)) ∧
    Tendsto (fun i => eLpNorm (fun x => vol (fun _ => e i x) - vol (fun _ => e₀ x)) 1 μ) atTop
      (𝓝 0) ∧
    (∀ (k : ℕ → α → E) (k₀ : α → E), (∀ i, AEStronglyMeasurable (k i) μ) →
      AEStronglyMeasurable k₀ μ → (∀ i, eLpNorm' (k i) 6 μ ≤ M) →
      Tendsto (fun i => eLpNorm' (k i - k₀) 2 μ) atTop (𝓝 0) →
      Tendsto (fun i => ∫ x, pr (w (e i x) (k i x)) (R i x) ∂μ) atTop
        (𝓝 (∫ x, pr (w (e₀ x) (k₀ x)) (R₀ x) ∂μ)) ∧
      Tendsto (fun i => eLpNorm (fun x => vol ![k i x, e i x, e i x, e i x] -
        vol ![k₀ x, e₀ x, e₀ x, e₀ x]) 1 μ) atTop (𝓝 0)) := by
  have hp1 : 1 < p := by linarith
  have h6₀ : eLpNorm' e₀ 6 μ ≤ M :=
    CoframeInterpolation.eLpNorm'_limit_le_of_tendsto_L2 e e₀ he he₀ h2 h6
  obtain ⟨C, hC, hRb⟩ := WeakStrongPalatiniLebesgue.lp_norm_bounded_of_weakTendsto hR
  have hweak := WeakStrongPalatiniLebesgue.tendsto_integral_pairing_of_weakTendsto pr p hp1 hR
  obtain ⟨h1, h2', h3, h4⟩ := weak_palatini_passage_with_volume_variation w pr vol p hp e e₀ he
    he₀ M hM h6 h6₀ h2 (fun i => (R i : α → Curv)) (R₀ : α → Curv)
    (fun i => Lp.aestronglyMeasurable (R i)) C hC hRb hweak
  refine ⟨h1, h2', h3, fun k k₀ hk hk₀ hk6 hk2 => ?_⟩
  exact h4 k k₀ hk hk₀ hk6
    (CoframeInterpolation.eLpNorm'_limit_le_of_tendsto_L2 k k₀ hk hk₀ hk2 hk6) hk2

/-- Non-vacuity: the hypothesis packet of `eLpNorm_volume_variation_tendsto_zero` is satisfied
by the constant coframes and variations `e_h = e = k_h = k = 1` on the unit interval with
Lebesgue measure, `vol` the four-fold product. -/
example : Tendsto (fun _ : ℕ => eLpNorm (fun x : Set.Icc (0 : ℝ) 1 =>
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ) ![(fun _ => (1 : ℝ)) x, 1, 1, 1] -
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ) ![(fun _ => (1 : ℝ)) x, 1, 1, 1]) 1
      volume) atTop (𝓝 0) := by
  have hfin : eLpNorm' (fun _ : Set.Icc (0 : ℝ) 1 => (1 : ℝ)) 6 volume ≠ ∞ := by
    have h := (memLp_const (μ := (volume : Measure (Set.Icc (0 : ℝ) 1))) (p := 6) (1 : ℝ)).2
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)] at h
    simpa using h.ne
  have h0 : Tendsto (fun _ : ℕ => eLpNorm' ((fun _ : Set.Icc (0 : ℝ) 1 => (1 : ℝ)) -
      fun _ => (1 : ℝ)) 2 volume) atTop (𝓝 0) := by
    simp [eLpNorm'_zero (by norm_num : (0 : ℝ) < 2)]
  exact eLpNorm_volume_variation_tendsto_zero (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ)
    (fun _ _ => 1) (fun _ => 1) (fun _ _ => 1) (fun _ => 1)
    (fun _ => aestronglyMeasurable_const) aestronglyMeasurable_const
    (fun _ => aestronglyMeasurable_const) aestronglyMeasurable_const
    _ hfin (fun _ => le_rfl) le_rfl (fun _ => le_rfl) le_rfl h0 h0

end RenewalGeometry.WeakPalatiniPassage
