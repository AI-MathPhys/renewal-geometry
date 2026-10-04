/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.FlatHodgeWeitzenbock
import RenewalGeometry.Analysis.SobolevCriticalEmbedding
import RenewalGeometry.Analysis.KatoInequalitySobolev

/-!
# Interior Hodge–Sobolev estimates and critical Coulomb absorption

Generic infrastructure (no renewal notions) for `lem:critical-Coulomb-Hodge` of the
Einstein–Standard-Model action-closure manuscript, on a coordinate box `Q ⊂ ℝ⁴` (the rendering of
the small-energy Coulomb ball `B`).

Connections are matrix-valued one-forms `A ν c e : ℝ^ι → ℂ` (`ν` the form index, `c, e` matrix
indices) with weak gradients `dA ν c e μ = ∂_μ A_{ν,ce}` on `Q`.  Their curvature is
`F_{μν} = ∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν]` (`curvatureW`), and they are **co-closed** when
`d^*A = -Σ_μ ∂_μ A_μ = 0` a.e. on `Q`.

* `eLpNorm_eq_restrict_of_vanish`: `Lᵖ` norms of functions vanishing off `Q`;
* `cutoffGrad`, `memW12_cutoff`: the cut-off form `χ u` and its weak gradient
  `χ ∂u + ∂χ u` on `ℝ^ι`;
* `eLpNorm_cutoff_le_hodge` (**interior Hodge–Sobolev estimate**): for `χ ∈ C_c^∞(Q)` and a one-form
  `u ∈ W^{1,2}(Q)`,
  `‖χ u_ν‖_{L⁴(Q)} ≤ C_d Σ_μ (Σ_{μ'ν'} ‖d(χu)_{μ'ν'}‖_{L²(Q)} + ‖d^*(χu)‖_{L²(Q)})`
  with the dimensional Gagliardo–Nirenberg–Sobolev constant `C_d` (independent of `Q` and `χ`):
  critical Sobolev `H¹_c ↪ L⁴` (`eLpNorm_le_sum_grad_of_ball`) plus the flat Weitzenböck identity
  (`eLpNorm_grad_le_d_dstar`);
* `eLpNorm_div_cutoff_le`: for co-closed `u`, `d^*(χu) = -Σ_μ ∂_μχ u_μ` is of order zero;
* `critical_coulomb_hodge` (**`lem:critical-Coulomb-Hodge` on a box**): there is a threshold
  `δ₀ > 0` depending only on the dimension and the matrix size such that, if `A_h, A` are
  co-closed `W^{1,2}(Q)` connections with `L⁴(Q)` entries of norm `≤ δ ≤ δ₀`, `A_h → A` in
  `L²(Q)` and `F_{A_h} → F_A` in `L²(Q)`, then `A_h → A` in `L⁴(K)` for every compact `K ⊂ Q`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.SobolevOpen

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Generic helpers -/

/-- `Lᵖ` norm of a function vanishing off a measurable set `Ω`. -/
theorem eLpNorm_eq_restrict_of_vanish {E : Type*} [NormedAddCommGroup E] {Ω : Set (ι → ℝ)}
    (hΩ : MeasurableSet Ω) {f : (ι → ℝ) → E} (h0 : ∀ x, x ∉ Ω → f x = 0) (p : ℝ≥0∞) :
    eLpNorm f p volume = eLpNorm f p (volume.restrict Ω) := by
  have : f = Ω.indicator f := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · simp [hx, h0 x hx]
  conv_lhs => rw [this]
  exact eLpNorm_indicator_eq_eLpNorm_restrict hΩ

/-- **Absorption.**  If `T < ∞` and `T ≤ X + q T` with `q ≤ 1/2`, then `T ≤ 2 X`. -/
theorem le_two_mul_of_le_add_mul {T X q : ℝ≥0∞} (hT : T ≠ ⊤) (hq : q ≤ 2⁻¹)
    (h : T ≤ X + q * T) : T ≤ 2 * X := by
  have h1 : T ≤ X + 2⁻¹ * T := h.trans (add_le_add le_rfl (mul_le_mul_left hq T))
  have h2 : 2⁻¹ * T + 2⁻¹ * T ≤ X + 2⁻¹ * T := by
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]; exact h1
  have h3 : 2⁻¹ * T ≤ X :=
    (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by simp) hT)).mp h2
  calc T = 2 * (2⁻¹ * T) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * X := mul_le_mul_right h3 2

/-! ### Cut-off one-forms -/

/-- The weak gradient `∂_μ (χ u) = χ ∂_μ u + ∂_μ χ u` of a cut-off function. -/
def cutoffGrad (χ : (ι → ℝ) → ℝ) (u : (ι → ℝ) → ℂ) (g : ι → (ι → ℝ) → ℂ) :
    ι → (ι → ℝ) → ℂ :=
  fun μ x => ((χ x : ℝ) : ℂ) * g μ x + ((pd χ μ x : ℝ) : ℂ) * u x

theorem IsTest.eq_zero_of_notMem {Ω : Set (ι → ℝ)} {χ : (ι → ℝ) → ℝ} (hχ : IsTest Ω χ)
    {x : ι → ℝ} (hx : x ∉ Ω) : χ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hχ.subset h)

theorem isTest_pd_eq_zero_of_notMem {Ω : Set (ι → ℝ)} {χ : (ι → ℝ) → ℝ} (hχ : IsTest Ω χ)
    (μ : ι) {x : ι → ℝ} (hx : x ∉ Ω) : pd χ μ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hχ.subset (tsupport_pd_subset χ μ h))

theorem cutoffGrad_eq_zero_of_notMem {Ω : Set (ι → ℝ)} {χ : (ι → ℝ) → ℝ} (hχ : IsTest Ω χ)
    (u : (ι → ℝ) → ℂ) (g : ι → (ι → ℝ) → ℂ) (μ : ι) {x : ι → ℝ} (hx : x ∉ Ω) :
    cutoffGrad χ u g μ x = 0 := by
  simp [cutoffGrad, hχ.eq_zero_of_notMem hx, isTest_pd_eq_zero_of_notMem hχ μ hx]

/-- **Interior Hodge–Sobolev estimate.**  Let `Q` be a box in `ℝ⁴`, `χ ∈ C_c^∞(Q)` and `u` a
one-form with components in `W^{1,2}(Q)`.  With `G = cutoffGrad χ u_ν (du ν)` the weak gradient of
`χ u_ν`, for every `ν`
`‖χ u_ν‖_{L⁴(Q)} ≤ C_d Σ_μ (Σ_{μ'ν'} ‖G_{ν'μ'} - G_{μ'ν'}‖_{L²(Q)} + ‖Σ_{μ'} G_{μ'μ'}‖_{L²(Q)})`,
where `C_d` is Mathlib's Gagliardo–Nirenberg–Sobolev constant (independent of `Q` and `χ`). -/
theorem eLpNorm_cutoff_le_hodge (hd : Fintype.card ι = 4) {a b : ι → ℝ} {χ : (ι → ℝ) → ℝ}
    (hχ : IsTest (box a b) χ) {u : ι → (ι → ℝ) → ℂ} {du : ι → ι → (ι → ℝ) → ℂ}
    (hW : ∀ ν, MemW12 (box a b) (u ν) (du ν)) (ν : ι) :
    eLpNorm (fun x => ((χ x : ℝ) : ℂ) * u ν x) 4 (volume.restrict (box a b)) ≤
      SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 *
        ∑ _μ : ι, (∑ μ', ∑ ν', eLpNorm (fun x => cutoffGrad χ (u ν') (du ν') μ' x -
            cutoffGrad χ (u μ') (du μ') ν' x) 2 (volume.restrict (box a b)) +
          eLpNorm (fun x => ∑ μ', cutoffGrad χ (u μ') (du μ') μ' x) 2
            (volume.restrict (box a b))) := by
  obtain ⟨R, _C, hR, hχ0, hpd0, hcut⟩ := cutoff_ball (isOpen_box a b) hχ
  have hQ : MeasurableSet (box a b) := (isOpen_box a b).measurableSet
  have hWc : ∀ ν, MemW12 univ (fun x => ((χ x : ℝ) : ℂ) * u ν x) (cutoffGrad χ (u ν) (du ν)) :=
    fun ν => (hcut (u ν) (du ν) (hW ν)).1
  have hw0 : ∀ ν x, R < ‖x‖ → ((χ x : ℝ) : ℂ) * u ν x = 0 := fun ν x hx => by
    simp [hχ0 x hx]
  have hg0 : ∀ ν μ x, R < ‖x‖ → cutoffGrad χ (u ν) (du ν) μ x = 0 := fun ν μ x hx => by
    simp [cutoffGrad, hχ0 x hx, hpd0 μ x hx]
  have hS := eLpNorm_le_sum_grad_of_ball (hWc ν) (hw0 ν) (by rw [hd]; norm_num) (p' := 4)
    (by rw [hd]; norm_num)
  have hH := fun μ => eLpNorm_grad_le_d_dstar hR hWc hw0 hg0 ν μ
  rw [← eLpNorm_eq_restrict_of_vanish hQ (fun x hx => by simp [hχ.eq_zero_of_notMem hx])]
  have e4 : ((4 : ℝ≥0) : ℝ≥0∞) = 4 := by norm_num
  rw [e4] at hS
  refine hS.trans (mul_le_mul_right (Finset.sum_le_sum fun μ _ => (hH μ).trans ?_) _)
  refine add_le_add (Finset.sum_le_sum fun μ' _ => Finset.sum_le_sum fun ν' _ => le_of_eq ?_)
    (le_of_eq ?_)
  · exact eLpNorm_eq_restrict_of_vanish hQ (fun x hx => by
      simp [cutoffGrad_eq_zero_of_notMem hχ _ _ _ hx]) 2
  · exact eLpNorm_eq_restrict_of_vanish hQ (fun x hx => by
      simp [cutoffGrad_eq_zero_of_notMem hχ _ _ _ hx]) 2

/-- **Order-zero codifferential of a cut-off co-closed form.**  If `Σ_μ ∂_μ u_μ = 0` a.e. on `Q`
and `|∂_μ χ| ≤ M'`, then `‖Σ_μ ∂_μ(χ u_μ)‖_{L²(Q)} ≤ M' Σ_μ ‖u_μ‖_{L²(Q)}`. -/
theorem eLpNorm_div_cutoff_le {a b : ι → ℝ} {χ : (ι → ℝ) → ℝ} (hχ : IsTest (box a b) χ)
    {u : ι → (ι → ℝ) → ℂ} {du : ι → ι → (ι → ℝ) → ℂ}
    (hum : ∀ μ, AEStronglyMeasurable (u μ) (volume.restrict (box a b)))
    (hdiv : ∀ᵐ x ∂(volume.restrict (box a b)), ∑ μ, du μ μ x = 0) {M' : ℝ≥0}
    (hM' : ∀ μ x, ‖pd χ μ x‖ ≤ M') :
    eLpNorm (fun x => ∑ μ, cutoffGrad χ (u μ) (du μ) μ x) 2 (volume.restrict (box a b)) ≤
      M' * ∑ μ, eLpNorm (u μ) 2 (volume.restrict (box a b)) := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.smooth.of_le (by simp)
  have e : (fun x => ∑ μ, cutoffGrad χ (u μ) (du μ) μ x) =ᵐ[volume.restrict (box a b)]
      fun x => ∑ μ, ((pd χ μ x : ℝ) : ℂ) * u μ x := by
    filter_upwards [hdiv] with x hx
    simp only [cutoffGrad, Finset.sum_add_distrib, ← Finset.mul_sum, hx, mul_zero, zero_add]
  rw [eLpNorm_congr_ae e, Finset.mul_sum]
  have hm : ∀ μ, AEStronglyMeasurable (fun x => ((pd χ μ x : ℝ) : ℂ) * u μ x)
      (volume.restrict (box a b)) := fun μ =>
    (Complex.continuous_ofReal.comp (continuous_pd hχ1 μ)).aestronglyMeasurable.mul (hum μ)
  refine (eLpNorm_le_sum_of_le hm (fun x => norm_sum_le _ _) (by norm_num)).trans ?_
  exact Finset.sum_le_sum fun μ _ => eLpNorm_mul_le_of_bound (fun x => by
    rw [Complex.norm_real]; exact hM' μ x)

/-! ### Matrix-valued connections: curvature and the curl of a cut-off difference -/

/-- The curvature `F_{μν} = ∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν]` (matrix entry `(c,e)`) of a
matrix-valued connection with weak gradients `dA ν c e μ = ∂_μ A_{ν,ce}`. -/
def curvatureW {m : ℕ} (A : ι → Fin m → Fin m → (ι → ℝ) → ℂ)
    (dA : ι → Fin m → Fin m → ι → (ι → ℝ) → ℂ) (μ ν : ι) (c e : Fin m) (x : ι → ℝ) : ℂ :=
  dA ν c e μ x - dA μ c e ν x + ∑ k, (A μ c k x * A ν k e x - A ν c k x * A μ k e x)

theorem aestronglyMeasurable_curvatureW {m : ℕ} {ρ : Measure (ι → ℝ)}
    {A : ι → Fin m → Fin m → (ι → ℝ) → ℂ} {dA : ι → Fin m → Fin m → ι → (ι → ℝ) → ℂ}
    (hA : ∀ ν c e, AEStronglyMeasurable (A ν c e) ρ)
    (hdA : ∀ ν c e μ, AEStronglyMeasurable (dA ν c e μ) ρ) (μ ν : ι) (c e : Fin m) :
    AEStronglyMeasurable (curvatureW A dA μ ν c e) ρ := by
  have hs : AEStronglyMeasurable
      (∑ k, fun x => A μ c k x * A ν k e x - A ν c k x * A μ k e x) ρ :=
    Finset.aestronglyMeasurable_sum _ fun k _ =>
      ((hA μ c k).mul (hA ν k e)).sub ((hA ν c k).mul (hA μ k e))
  have := ((hdA ν c e μ).sub (hdA μ c e ν)).add hs
  convert this using 1
  funext x; simp [curvatureW, Finset.sum_apply]

/-- **The curl of a cut-off difference of connections.**  With `a = A - B` and `w = χ a`,
`d(χ a)_{μ'ν'} = χ (F_A - F_B)_{μ'ν'} - ([w_{μ'}, A_{ν'}] + [B_{μ'}, w_{ν'}]) + ∂_{μ'}χ a_{ν'}
- ∂_{ν'}χ a_{μ'}` (entrywise, every point). -/
theorem curl_cutoff_eq {m : ℕ} (χ : (ι → ℝ) → ℝ) (A B : ι → Fin m → Fin m → (ι → ℝ) → ℂ)
    (dA dB : ι → Fin m → Fin m → ι → (ι → ℝ) → ℂ) (μ' ν' : ι) (c e : Fin m) (x : ι → ℝ) :
    cutoffGrad χ (fun x => A ν' c e x - B ν' c e x) (fun i x => dA ν' c e i x - dB ν' c e i x)
      μ' x -
        cutoffGrad χ (fun x => A μ' c e x - B μ' c e x)
          (fun i x => dA μ' c e i x - dB μ' c e i x) ν' x =
      ((χ x : ℝ) : ℂ) * (curvatureW A dA μ' ν' c e x - curvatureW B dB μ' ν' c e x) -
        ∑ k, (((χ x : ℝ) : ℂ) * (A μ' c k x - B μ' c k x) * A ν' k e x +
          B μ' c k x * (((χ x : ℝ) : ℂ) * (A ν' k e x - B ν' k e x)) -
          ((χ x : ℝ) : ℂ) * (A ν' c k x - B ν' c k x) * A μ' k e x -
          B ν' c k x * (((χ x : ℝ) : ℂ) * (A μ' k e x - B μ' k e x))) +
        ((pd χ μ' x : ℝ) : ℂ) * (A ν' c e x - B ν' c e x) -
        ((pd χ ν' x : ℝ) : ℂ) * (A μ' c e x - B μ' c e x) := by
  have hs : ∑ k, (((χ x : ℝ) : ℂ) * (A μ' c k x - B μ' c k x) * A ν' k e x +
          B μ' c k x * (((χ x : ℝ) : ℂ) * (A ν' k e x - B ν' k e x)) -
          ((χ x : ℝ) : ℂ) * (A ν' c k x - B ν' c k x) * A μ' k e x -
          B ν' c k x * (((χ x : ℝ) : ℂ) * (A μ' k e x - B μ' k e x))) =
      ((χ x : ℝ) : ℂ) * (∑ k, (A μ' c k x * A ν' k e x - A ν' c k x * A μ' k e x) -
        ∑ k, (B μ' c k x * B ν' k e x - B ν' c k x * B μ' k e x)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hs]
  simp only [cutoffGrad, curvatureW]
  ring

/-- **`L²` bound for the curl of a cut-off difference of connections**: with `T` a bound for the
`L⁴(Q)` norms of the entries of `χ (A - B)` and `δ` one for those of `A`, `B`,
`‖d(χ a)_{μ'ν'}‖_{L²(Q)} ≤ ‖F_A - F_B‖_{L²(Q)} + M' (‖a_{ν'}‖_{L²(Q)} + ‖a_{μ'}‖_{L²(Q)})
+ Σ_k 4 T δ`. -/
theorem eLpNorm_curl_cutoff_le {m : ℕ} {a b : ι → ℝ} {χ : (ι → ℝ) → ℝ}
    (hχ : IsTest (box a b) χ) (hχ1 : ∀ x, ‖χ x‖ ≤ 1) {M' : ℝ≥0}
    (hM' : ∀ μ x, ‖pd χ μ x‖ ≤ M') {A B : ι → Fin m → Fin m → (ι → ℝ) → ℂ}
    {dA dB : ι → Fin m → Fin m → ι → (ι → ℝ) → ℂ}
    (hWA : ∀ ν c e, MemW12 (box a b) (A ν c e) (dA ν c e))
    (hWB : ∀ ν c e, MemW12 (box a b) (B ν c e) (dB ν c e)) {δ T : ℝ≥0∞}
    (hAδ : ∀ ν c e, eLpNorm (A ν c e) 4 (volume.restrict (box a b)) ≤ δ)
    (hBδ : ∀ ν c e, eLpNorm (B ν c e) 4 (volume.restrict (box a b)) ≤ δ)
    (hwT : ∀ ν c e, eLpNorm (fun x => ((χ x : ℝ) : ℂ) * (A ν c e x - B ν c e x)) 4
      (volume.restrict (box a b)) ≤ T) (μ' ν' : ι) (c e : Fin m) :
    eLpNorm (fun x => cutoffGrad χ (fun x => A ν' c e x - B ν' c e x)
        (fun i x => dA ν' c e i x - dB ν' c e i x) μ' x -
      cutoffGrad χ (fun x => A μ' c e x - B μ' c e x)
        (fun i x => dA μ' c e i x - dB μ' c e i x) ν' x) 2 (volume.restrict (box a b)) ≤
      eLpNorm (fun x => curvatureW A dA μ' ν' c e x - curvatureW B dB μ' ν' c e x) 2
          (volume.restrict (box a b)) +
        M' * eLpNorm (fun x => A ν' c e x - B ν' c e x) 2 (volume.restrict (box a b)) +
        M' * eLpNorm (fun x => A μ' c e x - B μ' c e x) 2 (volume.restrict (box a b)) +
        ∑ _k : Fin m, (T * δ + δ * T + T * δ + δ * T) := by
  set ρ := volume.restrict (box a b)
  have hχ1' : ContDiff ℝ 1 χ := hχ.smooth.of_le (by simp)
  have hχm : AEStronglyMeasurable (fun x => ((χ x : ℝ) : ℂ)) ρ :=
    (Complex.continuous_ofReal.comp hχ1'.continuous).aestronglyMeasurable
  have hpdm : ∀ μ, AEStronglyMeasurable (fun x => ((pd χ μ x : ℝ) : ℂ)) ρ := fun μ =>
    (Complex.continuous_ofReal.comp (continuous_pd hχ1' μ)).aestronglyMeasurable
  have hAm : ∀ ν c e, AEStronglyMeasurable (A ν c e) ρ := fun ν c e => (hWA ν c e).memLp.1
  have hBm : ∀ ν c e, AEStronglyMeasurable (B ν c e) ρ := fun ν c e => (hWB ν c e).memLp.1
  have hdAm : ∀ ν c e μ, AEStronglyMeasurable (dA ν c e μ) ρ := fun ν c e μ =>
    ((hWA ν c e).memLp_grad μ).1
  have hdBm : ∀ ν c e μ, AEStronglyMeasurable (dB ν c e μ) ρ := fun ν c e μ =>
    ((hWB ν c e).memLp_grad μ).1
  set w : ι → Fin m → Fin m → (ι → ℝ) → ℂ := fun ν c e x =>
    ((χ x : ℝ) : ℂ) * (A ν c e x - B ν c e x) with hw
  have hwm : ∀ ν c e, AEStronglyMeasurable (w ν c e) ρ := fun ν c e =>
    hχm.mul ((hAm ν c e).sub (hBm ν c e))
  -- the family of terms
  set g0 : (ι → ℝ) → ℂ := fun x => ((χ x : ℝ) : ℂ) *
    (curvatureW A dA μ' ν' c e x - curvatureW B dB μ' ν' c e x)
  set g1 : (ι → ℝ) → ℂ := fun x => ((pd χ μ' x : ℝ) : ℂ) * (A ν' c e x - B ν' c e x)
  set g2 : (ι → ℝ) → ℂ := fun x => ((pd χ ν' x : ℝ) : ℂ) * (A μ' c e x - B μ' c e x)
  set t1 : Fin m → (ι → ℝ) → ℂ := fun k x => w μ' c k x * A ν' k e x
  set t2 : Fin m → (ι → ℝ) → ℂ := fun k x => B μ' c k x * w ν' k e x
  set t3 : Fin m → (ι → ℝ) → ℂ := fun k x => w ν' c k x * A μ' k e x
  set t4 : Fin m → (ι → ℝ) → ℂ := fun k x => B ν' c k x * w μ' k e x
  set G : Fin 3 ⊕ (Fin m × Fin 4) → (ι → ℝ) → ℂ :=
    Sum.elim (fun i => ![g0, g1, g2] i) (fun p => ![t1 p.1, t2 p.1, t3 p.1, t4 p.1] p.2)
  have hGm : ∀ j, AEStronglyMeasurable (G j) ρ := by
    rintro (i | ⟨k, t⟩)
    · fin_cases i
      · exact hχm.mul ((aestronglyMeasurable_curvatureW hAm hdAm μ' ν' c e).sub
          (aestronglyMeasurable_curvatureW hBm hdBm μ' ν' c e))
      · exact (hpdm μ').mul ((hAm ν' c e).sub (hBm ν' c e))
      · exact (hpdm ν').mul ((hAm μ' c e).sub (hBm μ' c e))
    · fin_cases t
      · exact (hwm μ' c k).mul (hAm ν' k e)
      · exact (hBm μ' c k).mul (hwm ν' k e)
      · exact (hwm ν' c k).mul (hAm μ' k e)
      · exact (hBm ν' c k).mul (hwm μ' k e)
  have hsplit : ∀ (φ : ((ι → ℝ) → ℂ) → ℝ≥0∞), ∑ j, φ (G j) =
      φ g0 + φ g1 + φ g2 + ∑ k, (φ (t1 k) + φ (t2 k) + φ (t3 k) + φ (t4 k)) := by
    intro φ
    simp only [G, Fintype.sum_sum_type, Fin.sum_univ_three, Fintype.sum_prod_type,
      Fin.sum_univ_four, Sum.elim_inl, Sum.elim_inr]
    simp [add_assoc]
  have hpt : ∀ x, ‖cutoffGrad χ (fun x => A ν' c e x - B ν' c e x)
        (fun i x => dA ν' c e i x - dB ν' c e i x) μ' x -
      cutoffGrad χ (fun x => A μ' c e x - B μ' c e x)
        (fun i x => dA μ' c e i x - dB μ' c e i x) ν' x‖ ≤ ∑ j, ‖G j x‖ := by
    intro x
    have hs := hsplit (fun f => (‖f x‖₊ : ℝ≥0∞))
    have hs' : ∑ j, ‖G j x‖ = ‖g0 x‖ + ‖g1 x‖ + ‖g2 x‖ +
        ∑ k, (‖t1 k x‖ + ‖t2 k x‖ + ‖t3 k x‖ + ‖t4 k x‖) := by
      have := congrArg ENNReal.toReal hs
      simpa [ENNReal.toReal_add, ENNReal.toReal_sum] using this
    rw [hs', curl_cutoff_eq]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add_left (norm_add_le _ _) _).trans ?_
    refine (add_le_add_left (add_le_add_left (norm_sub_le _ _) _) _).trans ?_
    have hsum : ‖∑ k, (((χ x : ℝ) : ℂ) * (A μ' c k x - B μ' c k x) * A ν' k e x +
          B μ' c k x * (((χ x : ℝ) : ℂ) * (A ν' k e x - B ν' k e x)) -
          ((χ x : ℝ) : ℂ) * (A ν' c k x - B ν' c k x) * A μ' k e x -
          B ν' c k x * (((χ x : ℝ) : ℂ) * (A μ' k e x - B μ' k e x)))‖ ≤
        ∑ k, (‖t1 k x‖ + ‖t2 k x‖ + ‖t3 k x‖ + ‖t4 k x‖) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl) |>.trans (le_of_eq ?_)
      simp only [t1, t2, t3, t4, hw]
    have h0 : ‖((χ x : ℝ) : ℂ) * (curvatureW A dA μ' ν' c e x - curvatureW B dB μ' ν' c e x) -
        ∑ k, (((χ x : ℝ) : ℂ) * (A μ' c k x - B μ' c k x) * A ν' k e x +
          B μ' c k x * (((χ x : ℝ) : ℂ) * (A ν' k e x - B ν' k e x)) -
          ((χ x : ℝ) : ℂ) * (A ν' c k x - B ν' c k x) * A μ' k e x -
          B ν' c k x * (((χ x : ℝ) : ℂ) * (A μ' k e x - B μ' k e x)))‖ ≤
        ‖g0 x‖ + ∑ k, (‖t1 k x‖ + ‖t2 k x‖ + ‖t3 k x‖ + ‖t4 k x‖) :=
      (norm_sub_le _ _).trans (add_le_add le_rfl hsum)
    simp only [g1, g2] at *
    linarith [h0]
  refine (eLpNorm_le_sum_of_le hGm hpt (by norm_num)).trans ?_
  rw [hsplit (fun f => eLpNorm f 2 ρ)]
  gcongr with k
  · exact (eLpNorm_mul_le_of_bound (G := 1) (by simpa using hχ1)).trans (by simp)
  · exact eLpNorm_mul_le_of_bound (by simpa using hM' μ')
  · exact eLpNorm_mul_le_of_bound (by simpa using hM' ν')
  · exact (eLpNorm_mul_le_L4 (hwm μ' c k) (hAm ν' k e)).trans
      (mul_le_mul' (hwT μ' c k) (hAδ ν' k e))
  · exact (eLpNorm_mul_le_L4 (hBm μ' c k) (hwm ν' k e)).trans
      (mul_le_mul' (hBδ μ' c k) (hwT ν' k e))
  · exact (eLpNorm_mul_le_L4 (hwm ν' c k) (hAm μ' k e)).trans
      (mul_le_mul' (hwT ν' c k) (hAδ μ' k e))
  · exact (eLpNorm_mul_le_L4 (hBm ν' c k) (hwm μ' k e)).trans
      (mul_le_mul' (hBδ ν' c k) (hwT μ' k e))

/-! ### Absorption and the critical Coulomb–Hodge lemma -/

/-- The absorption constant `κ_{d,m} = 4 d⁴ m³ C_d` (`C_d` the Gagliardo–Nirenberg–Sobolev
constant): the small-energy threshold is any `δ` with `κ δ ≤ 1/2`.  It depends only on the
dimension and the matrix size, not on the box or the cutoff. -/
def coulombKappa (ι : Type*) [Fintype ι] (m : ℕ) : ℝ≥0 :=
  (Fintype.card ι : ℝ≥0) * (m * (m * (SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 *
    ((Fintype.card ι : ℝ≥0) * ((Fintype.card ι : ℝ≥0) * ((Fintype.card ι : ℝ≥0) * (m * 4)))))))

theorem le_sum_three {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ≥0∞) (i : α) (j : β) (k : γ) : f i j k ≤ ∑ i, ∑ j, ∑ k, f i j k :=
  (Finset.single_le_sum (f := fun k => f i j k) (fun _ _ => zero_le) (Finset.mem_univ k)).trans
    ((Finset.single_le_sum (f := fun j => ∑ k, f i j k) (fun _ _ => zero_le)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ∑ k, f i j k) (fun _ _ => zero_le)
        (Finset.mem_univ i)))

/-- **One absorption step.**  For co-closed `W^{1,2}(Q)` connections `A, B` with `L⁴(Q)` entries
of norm `≤ δ`, `κ δ ≤ 1/2`, and a cutoff `χ ∈ C_c^∞(Q)` with `|χ| ≤ 1`, `|∂χ| ≤ M'`, the total
`L⁴(Q)` norm `T = Σ_{νce} ‖χ (A - B)_{νce}‖_{L⁴(Q)}` satisfies
`T ≤ 2 d m² C_d (d (d² (S_F + 2 M' S_a)) + M' S_a)`, where `S_F` sums
`‖F_A - F_B‖_{L²(Q)}` and `S_a` sums `‖A - B‖_{L²(Q)}` over all entries. -/
theorem coulomb_hodge_step (hd : Fintype.card ι = 4) {a b : ι → ℝ} {χ : (ι → ℝ) → ℝ}
    (hχ : IsTest (box a b) χ) (hχ1 : ∀ x, ‖χ x‖ ≤ 1) {M' : ℝ≥0}
    (hM' : ∀ μ x, ‖pd χ μ x‖ ≤ M') {m : ℕ} {A B : ι → Fin m → Fin m → (ι → ℝ) → ℂ}
    {dA dB : ι → Fin m → Fin m → ι → (ι → ℝ) → ℂ}
    (hWA : ∀ ν c e, MemW12 (box a b) (A ν c e) (dA ν c e))
    (hWB : ∀ ν c e, MemW12 (box a b) (B ν c e) (dB ν c e))
    (hdivA : ∀ c e, ∀ᵐ x ∂(volume.restrict (box a b)), ∑ μ, dA μ c e μ x = 0)
    (hdivB : ∀ c e, ∀ᵐ x ∂(volume.restrict (box a b)), ∑ μ, dB μ c e μ x = 0)
    (hA4 : ∀ ν c e, MemLp (A ν c e) 4 (volume.restrict (box a b)))
    (hB4 : ∀ ν c e, MemLp (B ν c e) 4 (volume.restrict (box a b))) {δ : ℝ≥0∞}
    (hAδ : ∀ ν c e, eLpNorm (A ν c e) 4 (volume.restrict (box a b)) ≤ δ)
    (hBδ : ∀ ν c e, eLpNorm (B ν c e) 4 (volume.restrict (box a b)) ≤ δ)
    (hsmall : (coulombKappa ι m : ℝ≥0∞) * δ ≤ 2⁻¹) :
    ∑ ν, ∑ c, ∑ e, eLpNorm (fun x => ((χ x : ℝ) : ℂ) * (A ν c e x - B ν c e x)) 4
        (volume.restrict (box a b)) ≤
      2 * ((Fintype.card ι : ℝ≥0∞) * (m * (m *
        (SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 *
          ((Fintype.card ι : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) *
            ((∑ μ, ∑ ν, ∑ c, ∑ e, eLpNorm (fun x => curvatureW A dA μ ν c e x -
              curvatureW B dB μ ν c e x) 2 (volume.restrict (box a b))) +
            M' * (∑ ν, ∑ c, ∑ e, eLpNorm (fun x => A ν c e x - B ν c e x) 2
              (volume.restrict (box a b))) +
            M' * (∑ ν, ∑ c, ∑ e, eLpNorm (fun x => A ν c e x - B ν c e x) 2
              (volume.restrict (box a b)))))) +
          (Fintype.card ι : ℝ≥0∞) * (M' * (∑ ν, ∑ c, ∑ e, eLpNorm (fun x => A ν c e x - B ν c e x) 2
            (volume.restrict (box a b))))))))) := by
  set ρ := volume.restrict (box a b)
  set T := ∑ ν, ∑ c, ∑ e, eLpNorm (fun x => ((χ x : ℝ) : ℂ) * (A ν c e x - B ν c e x)) 4 ρ
  set SF := ∑ μ, ∑ ν, ∑ c, ∑ e, eLpNorm (fun x => curvatureW A dA μ ν c e x -
    curvatureW B dB μ ν c e x) 2 ρ
  set Sa := ∑ ν, ∑ c, ∑ e, eLpNorm (fun x => A ν c e x - B ν c e x) 2 ρ
  have hχ1' : ContDiff ℝ 1 χ := hχ.smooth.of_le (by simp)
  have hwT : ∀ ν c e, eLpNorm (fun x => ((χ x : ℝ) : ℂ) * (A ν c e x - B ν c e x)) 4 ρ ≤ T :=
    fun ν c e => le_sum_three (fun ν c e => eLpNorm (fun x => ((χ x : ℝ) : ℂ) *
      (A ν c e x - B ν c e x)) 4 ρ) ν c e
  have haT : ∀ ν c e, eLpNorm (fun x => A ν c e x - B ν c e x) 2 ρ ≤ Sa :=
    fun ν c e => le_sum_three (fun ν c e => eLpNorm (fun x => A ν c e x - B ν c e x) 2 ρ) ν c e
  have hFT : ∀ μ ν c e, eLpNorm (fun x => curvatureW A dA μ ν c e x -
      curvatureW B dB μ ν c e x) 2 ρ ≤ SF := by
    intro μ ν c e
    refine (le_sum_three (fun ν c e => eLpNorm (fun x => curvatureW A dA μ ν c e x -
      curvatureW B dB μ ν c e x) 2 ρ) ν c e).trans ?_
    exact Finset.single_le_sum (f := fun μ => ∑ ν, ∑ c, ∑ e, eLpNorm (fun x =>
      curvatureW A dA μ ν c e x - curvatureW B dB μ ν c e x) 2 ρ) (fun _ _ => zero_le)
      (Finset.mem_univ μ)
  have hTfin : T ≠ ⊤ := by
    refine ENNReal.sum_ne_top.mpr fun ν _ => ENNReal.sum_ne_top.mpr fun c _ =>
      ENNReal.sum_ne_top.mpr fun e _ => ?_
    have hm : MemLp (fun x => ((χ x : ℝ) : ℂ) * (A ν c e x - B ν c e x)) 4 ρ := by
      refine ((hA4 ν c e).sub (hB4 ν c e)).of_le ((Complex.continuous_ofReal.comp
        hχ1'.continuous).aestronglyMeasurable.mul ((hA4 ν c e).1.sub (hB4 ν c e).1))
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Complex.norm_real]
      simpa using mul_le_mul_of_nonneg_right (hχ1 x) (norm_nonneg (A ν c e x - B ν c e x))
    exact hm.eLpNorm_ne_top
  -- the curl and divergence bounds
  set Y : ℝ≥0∞ := SF + M' * Sa + M' * Sa + ∑ _k : Fin m, (T * δ + δ * T + T * δ + δ * T)
    with hYd
  have hcurl : ∀ μ' ν' c e, eLpNorm (fun x => cutoffGrad χ (fun x => A ν' c e x - B ν' c e x)
        (fun i x => dA ν' c e i x - dB ν' c e i x) μ' x -
      cutoffGrad χ (fun x => A μ' c e x - B μ' c e x)
        (fun i x => dA μ' c e i x - dB μ' c e i x) ν' x) 2 ρ ≤ Y := by
    intro μ' ν' c e
    refine (eLpNorm_curl_cutoff_le hχ hχ1 hM' hWA hWB hAδ hBδ hwT μ' ν' c e).trans ?_
    rw [hYd]
    gcongr
    · exact hFT μ' ν' c e
    · exact haT ν' c e
    · exact haT μ' c e
  have hdiv : ∀ c e, eLpNorm (fun x => ∑ μ, cutoffGrad χ (fun x => A μ c e x - B μ c e x)
      (fun i x => dA μ c e i x - dB μ c e i x) μ x) 2 ρ ≤ M' * Sa := by
    intro c e
    have hd0 : ∀ᵐ x ∂ρ, ∑ μ, (fun i x => dA μ c e i x - dB μ c e i x) μ x = 0 := by
      filter_upwards [hdivA c e, hdivB c e] with x h1 h2
      simp only [Finset.sum_sub_distrib, h1, h2, sub_zero]
    refine (eLpNorm_div_cutoff_le hχ (u := fun μ x => A μ c e x - B μ c e x)
      (fun μ => (hWA μ c e).memLp.1.sub (hWB μ c e).memLp.1) hd0 hM').trans ?_
    refine mul_le_mul_right ?_ _
    exact Finset.sum_le_sum fun μ _ =>
      (Finset.single_le_sum (f := fun e => eLpNorm (fun x => A μ c e x - B μ c e x) 2 ρ)
        (fun _ _ => zero_le) (Finset.mem_univ e)).trans
        (Finset.single_le_sum (f := fun c => ∑ e, eLpNorm (fun x =>
          A μ c e x - B μ c e x) 2 ρ) (fun _ _ => zero_le) (Finset.mem_univ c))
  -- per-entry Sobolev–Hodge bound
  have hentry : ∀ ν c e, eLpNorm (fun x => ((χ x : ℝ) : ℂ) * (A ν c e x - B ν c e x)) 4 ρ ≤
      SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 *
        ((Fintype.card ι : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) * Y)) +
          (Fintype.card ι : ℝ≥0∞) * (M' * Sa)) := by
    intro ν c e
    refine (eLpNorm_cutoff_le_hodge hd hχ (u := fun ν x => A ν c e x - B ν c e x)
      (du := fun ν i x => dA ν c e i x - dB ν c e i x)
      (fun ν => (hWA ν c e).sub (hWB ν c e)) ν).trans ?_
    refine mul_le_mul_right ?_ _
    calc ∑ _μ : ι, (∑ μ', ∑ ν', eLpNorm (fun x =>
            cutoffGrad χ (fun x => A ν' c e x - B ν' c e x)
              (fun i x => dA ν' c e i x - dB ν' c e i x) μ' x -
            cutoffGrad χ (fun x => A μ' c e x - B μ' c e x)
              (fun i x => dA μ' c e i x - dB μ' c e i x) ν' x) 2 ρ +
          eLpNorm (fun x => ∑ μ', cutoffGrad χ (fun x => A μ' c e x - B μ' c e x)
            (fun i x => dA μ' c e i x - dB μ' c e i x) μ' x) 2 ρ)
        ≤ ∑ _μ : ι, (∑ _μ' : ι, ∑ _ν' : ι, Y + M' * Sa) :=
          Finset.sum_le_sum fun _ _ => add_le_add (Finset.sum_le_sum fun μ' _ =>
            Finset.sum_le_sum fun ν' _ => hcurl μ' ν' c e) (hdiv c e)
      _ = (Fintype.card ι : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) * Y)) +
          (Fintype.card ι : ℝ≥0∞) * (M' * Sa) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  -- sum over entries and absorb
  have hT : T ≤ (Fintype.card ι : ℝ≥0∞) * (m * (m *
      (SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 *
        ((Fintype.card ι : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) * Y)) +
          (Fintype.card ι : ℝ≥0∞) * (M' * Sa))))) := by
    refine (Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun c _ =>
      Finset.sum_le_sum fun e _ => hentry ν c e).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine le_two_mul_of_le_add_mul hTfin hsmall (hT.trans (le_of_eq ?_))
  simp only [hYd, coulombKappa, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring





/-- `C f → 0` for `f → 0` and a finite constant `C`. -/
theorem tendsto_const_mul_zero' {α : Type*} {l : Filter α} {f : α → ℝ≥0∞} (C : ℝ≥0∞)
    (hC : C ≠ ⊤) (hf : Tendsto f l (𝓝 0)) : Tendsto (fun x => C * f x) l (𝓝 0) := by
  simpa using ENNReal.Tendsto.const_mul hf (Or.inr hC)

/-- The small-energy threshold `δ₀ = (2κ + 1)⁻¹` satisfies `κ δ ≤ 1/2` for `δ ≤ δ₀`. -/
theorem coulombKappa_mul_le {κ δ : ℝ≥0} (hδ : δ ≤ (2 * κ + 1)⁻¹) :
    (κ : ℝ≥0∞) * δ ≤ 2⁻¹ := by
  have h1 : κ * δ ≤ 2⁻¹ := by
    refine (mul_le_mul_right hδ κ).trans ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith [κ.2]
  have h2 : ((κ * δ : ℝ≥0) : ℝ≥0∞) ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr h1
  rw [ENNReal.coe_mul, ENNReal.coe_inv two_ne_zero] at h2
  simpa using h2

/-- **Critical Coulomb–Hodge absorption** (`lem:critical-Coulomb-Hodge`, rendered on a
coordinate box `Q = box a b ⊂ ℝ⁴` in place of the small-energy Coulomb ball `B`).  There is a
threshold `δ₀ > 0`, depending only on the dimension and the matrix size `m`, such that: if
`A_h`, `A` are `m × m`-matrix-valued connections with components in `W^{1,2}(Q)`, **co-closed**
(`Σ_μ ∂_μ A_μ = 0` a.e. on `Q`), with all `L⁴(Q)` entry norms `≤ δ ≤ δ₀`, `A_h → A` in `L²(Q)` and
`F_{A_h} → F_A` in `L²(Q)` (`F = dA + [A ∧ A]`, `curvatureW`), then `A_h → A` strongly in
`L⁴(K)` for every compact `K ⊂ Q` (the rendering of `B' ⋐ B`). -/
theorem critical_coulomb_hodge (hd : Fintype.card ι = 4) (a b : ι → ℝ) (m : ℕ) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ (A : ℕ → ι → Fin m → Fin m → (ι → ℝ) → ℂ)
      (dA : ℕ → ι → Fin m → Fin m → ι → (ι → ℝ) → ℂ) (A₀ : ι → Fin m → Fin m → (ι → ℝ) → ℂ)
      (dA₀ : ι → Fin m → Fin m → ι → (ι → ℝ) → ℂ) (δ : ℝ≥0), δ ≤ δ₀ →
      (∀ h ν c e, MemW12 (box a b) (A h ν c e) (dA h ν c e)) →
      (∀ ν c e, MemW12 (box a b) (A₀ ν c e) (dA₀ ν c e)) →
      (∀ h c e, ∀ᵐ x ∂(volume.restrict (box a b)), ∑ μ, dA h μ c e μ x = 0) →
      (∀ c e, ∀ᵐ x ∂(volume.restrict (box a b)), ∑ μ, dA₀ μ c e μ x = 0) →
      (∀ h ν c e, eLpNorm (A h ν c e) 4 (volume.restrict (box a b)) ≤ δ) →
      (∀ ν c e, eLpNorm (A₀ ν c e) 4 (volume.restrict (box a b)) ≤ δ) →
      (∀ ν c e, Tendsto (fun h => eLpNorm (fun x => A h ν c e x - A₀ ν c e x) 2
        (volume.restrict (box a b))) atTop (𝓝 0)) →
      (∀ μ ν c e, Tendsto (fun h => eLpNorm (fun x => curvatureW (A h) (dA h) μ ν c e x -
        curvatureW A₀ dA₀ μ ν c e x) 2 (volume.restrict (box a b))) atTop (𝓝 0)) →
      ∀ K : Set (ι → ℝ), IsCompact K → K ⊆ box a b → ∀ ν c e,
        Tendsto (fun h => eLpNorm (fun x => A h ν c e x - A₀ ν c e x) 4 (volume.restrict K))
          atTop (𝓝 0) := by
  refine ⟨(2 * coulombKappa ι m + 1)⁻¹, by positivity, fun A dA A₀ dA₀ δ hδ hWA hWA₀ hdivA
    hdivA₀ hAδ hA₀δ hL2 hF K hK hKQ ν c e => ?_⟩
  have hA4 : ∀ h ν c e, MemLp (A h ν c e) 4 (volume.restrict (box a b)) := fun h ν c e =>
    ⟨(hWA h ν c e).memLp.1, lt_of_le_of_lt (hAδ h ν c e) ENNReal.coe_lt_top⟩
  have hA₀4 : ∀ ν c e, MemLp (A₀ ν c e) 4 (volume.restrict (box a b)) := fun ν c e =>
    ⟨(hWA₀ ν c e).memLp.1, lt_of_le_of_lt (hA₀δ ν c e) ENNReal.coe_lt_top⟩
  have hsmall := coulombKappa_mul_le hδ
  obtain ⟨χ, hχ, hχK, hχ01⟩ := exists_cutoff (isOpen_box a b) hK hKQ
  have hχ1 : ∀ x, ‖χ x‖ ≤ 1 := fun x => by
    rw [Real.norm_of_nonneg (hχ01 x).1]; exact (hχ01 x).2
  obtain ⟨M', hM'⟩ := hχ.exists_bound_pd
  set ρ := volume.restrict (box a b)
  set SF : ℕ → ℝ≥0∞ := fun h => ∑ μ, ∑ ν, ∑ c, ∑ e, eLpNorm (fun x =>
    curvatureW (A h) (dA h) μ ν c e x - curvatureW A₀ dA₀ μ ν c e x) 2 ρ with hSFd
  set Sa : ℕ → ℝ≥0∞ := fun h => ∑ ν, ∑ c, ∑ e, eLpNorm (fun x => A h ν c e x - A₀ ν c e x) 2 ρ
    with hSad
  have hSF : Tendsto SF atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset ι) fun μ _ =>
      tendsto_finset_sum (Finset.univ : Finset ι) fun ν _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun c _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun e _ => hF μ ν c e
    simpa [hSFd] using this
  have hSa : Tendsto Sa atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset ι) fun ν _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun c _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun e _ => hL2 ν c e
    simpa [hSad] using this
  have hdt : (Fintype.card ι : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmt : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h1 : Tendsto (fun h => SF h + M' * Sa h + M' * Sa h) atTop (𝓝 0) := by
    have := (hSF.add (tendsto_const_mul_zero' (M' : ℝ≥0∞) ENNReal.coe_ne_top hSa)).add
      (tendsto_const_mul_zero' (M' : ℝ≥0∞) ENNReal.coe_ne_top hSa)
    simpa using this
  have h2 : Tendsto (fun h => (Fintype.card ι : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) *
      ((Fintype.card ι : ℝ≥0∞) * (SF h + M' * Sa h + M' * Sa h))) +
      (Fintype.card ι : ℝ≥0∞) * (M' * Sa h)) atTop (𝓝 0) := by
    have := (tendsto_const_mul_zero' _ hdt (tendsto_const_mul_zero' _ hdt
      (tendsto_const_mul_zero' _ hdt h1))).add
      (tendsto_const_mul_zero' _ hdt (tendsto_const_mul_zero' (M' : ℝ≥0∞) ENNReal.coe_ne_top hSa))
    simpa using this
  have h3 : Tendsto (fun h => 2 * ((Fintype.card ι : ℝ≥0∞) * (m * (m *
      (SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 *
        ((Fintype.card ι : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) *
          ((Fintype.card ι : ℝ≥0∞) * (SF h + M' * Sa h + M' * Sa h))) +
        (Fintype.card ι : ℝ≥0∞) * (M' * Sa h))))))) atTop (𝓝 0) :=
    tendsto_const_mul_zero' _ (by norm_num) (tendsto_const_mul_zero' _ hdt
      (tendsto_const_mul_zero' _ hmt (tendsto_const_mul_zero' _ hmt
        (tendsto_const_mul_zero' (SNormLESNormFDerivOfEqConst ℂ (volume : Measure (ι → ℝ)) 2 : ℝ≥0∞)
          ENNReal.coe_ne_top h2))))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun h => zero_le)
    (fun h => ?_)
  have hstep := coulomb_hodge_step hd hχ hχ1 hM' (hWA h) hWA₀ (hdivA h) hdivA₀ (hA4 h) hA₀4
    (hAδ h) hA₀δ hsmall
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hKeq : eLpNorm (fun x => A h ν c e x - A₀ ν c e x) 4 (volume.restrict K) =
      eLpNorm (fun x => ((χ x : ℝ) : ℂ) * (A h ν c e x - A₀ ν c e x)) 4 (volume.restrict K) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' hKm).mpr (Eventually.of_forall fun x hx => ?_))
    simp [hχK.self_of_nhdsSet x hx]
  rw [hKeq]
  refine (eLpNorm_mono_measure _ (Measure.restrict_mono hKQ le_rfl)).trans ?_
  refine (le_sum_three (fun ν c e => eLpNorm (fun x => ((χ x : ℝ) : ℂ) *
    (A h ν c e x - A₀ ν c e x)) 4 ρ) ν c e).trans ?_
  exact hstep

end RenewalGeometry.SobolevOpen
