/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoRegularityPersistence
import RenewalGeometry.Analysis.TorusSobolevEmbedding

/-!
# Smoothness of Kato solutions with smooth data

Generic infrastructure (no renewal notions) for `lem:generated-physical-identification`
(Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics`): a classical
solution of a quasilinear symmetric hyperbolic system on `(-T, T) × 𝕋^d` which is bounded in every
`H^{q'}` (Fourier side, `KatoPersist.kato_two_sided_allOrders`) is `C^∞` on the open slab.

## Method

* `contDiffOn_succ_of_partials`, **`contDiffOn_top_of_closed`** — a class of functions on an open
  set which are continuous and closed under all coordinate partial derivatives consists of `C^∞`
  functions (generic, any dimension);
* `wq` lower bound and the summability of `wq_s(k)^{-1/2}` for `s > d` (`summable_inv_sqrt_wq`);
* `ser L f` — the termwise-differentiated `cas` series `Σ_k c_k(f, t) ∂^L cas_k` of a field whose
  coefficients decay in every order uniformly in `t` (`AllOrd`): it represents `f`
  (`ser_nil_eq`), its spatial line derivatives are the series of the longer words (`hasDerivAt_ser_space`),
  it is continuous, and its time derivative is the series of `g` whenever `∂_t c_k(f) = c_k(g)`
  (`hasDerivAt_ser_time`);
* jets `jet M U = (∂^L U_b)_{|L| ≤ M}` and jet functions `Ψ(jet M U)`; their partial derivatives are
  again jet functions (chain rule, the equation for the time direction);
* **`twoSided_contDiffOn`** — a two-sided classical solution bounded in every `H^{q'}` is `C^∞` on
  `(-T, T) × 𝕋^d`.
-/

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ContDiff Real

noncomputable section

namespace RenewalGeometry.KatoSmooth

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin

set_option linter.unusedSectionVars false

/-! ### `C^∞` from a class closed under partial derivatives -/

section Partials

variable {N : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Partial derivatives of class `C^k` give `C^{k+1}`.** -/
theorem contDiffOn_succ_of_partials {U : Set (Fin N → ℝ)} (hU : IsOpen U) {f : (Fin N → ℝ) → F}
    {g : Fin N → (Fin N → ℝ) → F} {k : ℕ} (hg : ∀ i, ContDiffOn ℝ k (g i) U)
    (hd : ∀ i, ∀ x ∈ U, HasDerivAt (fun t : ℝ => f (x + t • Pi.single i 1)) (g i x) 0) :
    ContDiffOn ℝ (k + 1 : ℕ) f U := by
  have hf := fun x (hx : x ∈ U) =>
    PartialC1.hasFDerivAt_of_partials hU (fun i => (hg i).continuousOn) hd hx
  rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl,
    contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  have hc : ContDiffOn ℝ k (fun x => PartialC1.partialCLM fun i => g i x) U := by
    unfold PartialC1.partialCLM
    refine ContDiffOn.sum fun i _ => ?_
    exact (ContinuousLinearMap.smulRightL ℝ (Fin N → ℝ) F
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i)).contDiff.comp_contDiffOn
      (hg i)
  exact hc.congr fun x hx => (hf x hx).fderiv

/-- **`C^∞` from closure under partial derivatives**: if every member of a class of functions is
continuous on the open set `U` and has, along every coordinate line, a derivative which is again a
member of the class, then every member is `C^∞` on `U`. -/
theorem contDiffOn_top_of_closed {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (𝒞 : ((Fin N → ℝ) → F) → Prop) (hcont : ∀ f, 𝒞 f → ContinuousOn f U)
    (hpart : ∀ f, 𝒞 f → ∀ i, ∃ g, 𝒞 g ∧
      ∀ x ∈ U, HasDerivAt (fun t : ℝ => f (x + t • Pi.single i 1)) (g x) 0) :
    ∀ f, 𝒞 f → ContDiffOn ℝ ∞ f U := by
  have key : ∀ k : ℕ, ∀ f, 𝒞 f → ContDiffOn ℝ k f U := by
    intro k
    induction k with
    | zero => intro f hf; exact contDiffOn_zero.2 (hcont f hf)
    | succ k ih =>
      intro f hf
      choose g hg hgd using hpart f hf
      exact contDiffOn_succ_of_partials hU (fun i => ih _ (hg i)) hgd
  intro f hf
  exact contDiffOn_infty.2 fun k => key k f hf

end Partials

/-! ### Lower bounds of the Sobolev weights and summability -/

section Summability

variable {d : ℕ}

theorem mem_wordsLE_replicate (s : ℕ) (i : Fin d) : List.replicate s i ∈ wordsLE d s :=
  mem_wordsLE.2 (by simp)

/-- `1 + Σ_i ((2πk_i)²)^s ≤ wq_s(k)` (the empty word and the constant words). -/
theorem one_add_sum_pow_le_wq (s : ℕ) (hs : 1 ≤ s) (k : Fin d → ℤ) :
    1 + ∑ i, ((2 * π * (k i : ℝ)) ^ 2) ^ s ≤ wq s k := by
  classical
  have hinj : Set.InjOn (fun i : Fin d => List.replicate s i) (Finset.univ : Finset (Fin d)) := by
    intro i _ j _ h
    have h1 := congrArg List.head? h
    simp only at h1
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    simpa [List.replicate_succ] using h1
  have hnot : [] ∉ (Finset.univ : Finset (Fin d)).image fun i => List.replicate s i := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i h
    have := congrArg List.length h
    simp at this
    omega
  have hsub : insert [] ((Finset.univ : Finset (Fin d)).image fun i => List.replicate s i) ⊆
      wordsLE d s := by
    intro L hL
    rw [Finset.mem_insert, Finset.mem_image] at hL
    rcases hL with rfl | ⟨i, -, rfl⟩
    · exact mem_wordsLE.2 (by simp)
    · exact mem_wordsLE_replicate s i
  calc 1 + ∑ i, ((2 * π * (k i : ℝ)) ^ 2) ^ s
      = ∑ L ∈ insert [] ((Finset.univ : Finset (Fin d)).image fun i => List.replicate s i),
          muL L k := by
        rw [Finset.sum_insert hnot, Finset.sum_image hinj, muL_nil]
        simp only [muL_replicate]
    _ ≤ wq s k := Finset.sum_le_sum_of_subset_of_nonneg hsub fun L _ _ => muL_nonneg L k

/-- **`⟨k⟩^{2s} ≤ (d+1)^s wq_s(k)`** (`⟨k⟩² = sobWeight k = 1 + 4π²|k|²`). -/
theorem sobWeight_pow_le_wq (s : ℕ) (k : Fin d → ℤ) :
    TorusSobolev.sobWeight k ^ s ≤ ((d : ℝ) + 1) ^ s * wq s k := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp only [pow_zero, one_mul]; exact one_le_wq 0 k
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  set x : Option (Fin d) → ℝ := fun o => Option.elim o 1 fun i => (2 * π * (k i : ℝ)) ^ 2 with hx
  have hx0 : ∀ o ∈ (Finset.univ : Finset (Option (Fin d))), 0 ≤ x o := by
    intro o _; cases o <;> simp [hx, sq_nonneg]
  have h1 := pow_sum_div_card_le_sum_pow hx0 s'
  have hsum : ∑ o, x o = TorusSobolev.sobWeight k := by
    rw [Fintype.sum_option]
    simp only [hx, Option.elim, TorusSobolev.sobWeight, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  have hsum2 : ∑ o, x o ^ (s' + 1) = 1 + ∑ i, ((2 * π * (k i : ℝ)) ^ 2) ^ (s' + 1) := by
    rw [Fintype.sum_option]; simp [hx]
  have hcard : ((Finset.univ : Finset (Option (Fin d))).card : ℝ) = d + 1 := by
    simp [Finset.card_univ, Fintype.card_option]
  rw [hsum, hsum2, hcard] at h1
  have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h2 := one_add_sum_pow_le_wq (s' + 1) (by omega) k
  rw [div_le_iff₀ (pow_pos hd _)] at h1
  calc TorusSobolev.sobWeight k ^ (s' + 1)
      ≤ (1 + ∑ i, ((2 * π * (k i : ℝ)) ^ 2) ^ (s' + 1)) * ((d : ℝ) + 1) ^ s' := h1
    _ ≤ wq (s' + 1) k * ((d : ℝ) + 1) ^ (s' + 1) := by
        refine mul_le_mul h2 (pow_le_pow_right₀ (by linarith) (by omega)) (by positivity)
          (wq_nonneg _ k)
    _ = ((d : ℝ) + 1) ^ (s' + 1) * wq (s' + 1) k := by ring

/-- **`Σ_k wq_s(k)^{-1/2} < ∞` for `s > d`.** -/
theorem summable_inv_sqrt_wq {s : ℕ} (hs : d < s) :
    Summable fun k : Fin d → ℤ => 1 / Real.sqrt (wq s k) := by
  have hsum := TorusSobolev.summable_sobWeight_rpow_neg (d := Fin d) (s := (s : ℝ) / 2)
    (by simp; exact_mod_cast (by linarith [(Nat.cast_lt (α := ℝ)).2 hs] : (d : ℝ) / 2 < s / 2))
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hsum.mul_left (Real.sqrt (((d : ℝ) + 1) ^ s)))
  have hw := sobWeight_pow_le_wq s k
  have hW : 0 < TorusSobolev.sobWeight k := by
    unfold TorusSobolev.sobWeight; positivity
  have hwq := wq_pos s k
  have hd : (0 : ℝ) < ((d : ℝ) + 1) ^ s := by positivity
  -- `1/√wq ≤ √((d+1)^s) ⟨k⟩^{-s}`
  have hroot : Real.sqrt (TorusSobolev.sobWeight k ^ s) = TorusSobolev.sobWeight k ^ ((s : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    congr 1; ring
  have h1 : Real.sqrt (TorusSobolev.sobWeight k ^ s) ≤
      Real.sqrt (((d : ℝ) + 1) ^ s) * Real.sqrt (wq s k) := by
    rw [← Real.sqrt_mul hd.le]; exact Real.sqrt_le_sqrt hw
  rw [hroot] at h1
  have hpos : 0 < TorusSobolev.sobWeight k ^ ((s : ℝ) / 2) := Real.rpow_pos_of_pos hW _
  rw [Real.rpow_neg hW.le, div_le_iff₀ (Real.sqrt_pos.2 hwq)]
  calc (1 : ℝ) = (TorusSobolev.sobWeight k ^ ((s : ℝ) / 2))⁻¹ *
        TorusSobolev.sobWeight k ^ ((s : ℝ) / 2) := by field_simp
    _ ≤ (TorusSobolev.sobWeight k ^ ((s : ℝ) / 2))⁻¹ *
        (Real.sqrt (((d : ℝ) + 1) ^ s) * Real.sqrt (wq s k)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hpos.le)
    _ = Real.sqrt (((d : ℝ) + 1) ^ s) * (TorusSobolev.sobWeight k ^ ((s : ℝ) / 2))⁻¹ *
        Real.sqrt (wq s k) := by ring

/-- `μ_L(k) wq_s(k) ≤ wq_{|L|+s}(k)` (prefixing words). -/
theorem muL_mul_wq_le (L : List (Fin d)) (s : ℕ) (k : Fin d → ℤ) :
    muL L k * wq s k ≤ wq (L.length + s) k := by
  have hinj : Set.InjOn (fun v : List (Fin d) => L ++ v) (wordsLE d s : Set (List (Fin d))) :=
    fun v _ v' _ hv => List.append_cancel_left hv
  have hsub : (wordsLE d s).image (fun v => L ++ v) ⊆ wordsLE d (L.length + s) := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [mem_wordsLE] at hv ⊢
    simp; omega
  calc muL L k * wq s k = ∑ v ∈ wordsLE d s, muL (L ++ v) k := by
        rw [wq, Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => (muL_append L v k).symm
    _ = ∑ w ∈ (wordsLE d s).image (fun v => L ++ v), muL w k :=
        (Finset.sum_image (f := fun w => muL w k) hinj).symm
    _ ≤ wq (L.length + s) k := Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ =>
        muL_nonneg w k

end Summability

/-! ### Word derivatives of the `cas` modes -/

section Modes

variable {d : ℕ}

theorem sd_cons_casS (i : Fin d) (L : List (Fin d)) (k : Fin d → ℤ) :
    sd (i :: L) (casS k) = fun x => 2 * π * (k i : ℝ) * sd L (casS (-k)) x := by
  rw [sd_cons, pd_casS_succ, sd_const_mul L (contDiff_casS (-k))]

/-- `|∂^L cas_k| ≤ 2 √μ_L(k)`. -/
theorem abs_sd_casS_le : ∀ (L : List (Fin d)) (k : Fin d → ℤ) (x : ST d),
    |sd L (casS k) x| ≤ 2 * Real.sqrt (muL L k)
  | [], k, x => by simpa [muL_nil] using abs_casS_le k x
  | i :: L, k, x => by
    rw [sd_cons_casS, abs_mul, muL_cons, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    have h := abs_sd_casS_le L (-k) x
    rw [muL_neg] at h
    calc |2 * π * (k i : ℝ)| * |sd L (casS (-k)) x|
        ≤ |2 * π * (k i : ℝ)| * (2 * Real.sqrt (muL L k)) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = 2 * (|2 * π * (k i : ℝ)| * Real.sqrt (muL L k)) := by ring

theorem casS_add_time (k : Fin d → ℤ) (x : ST d) (s : ℝ) :
    casS k (x + s • ev 0) = casS k x := by
  unfold casS
  rw [map_add, map_smul, phL_single_zero, smul_zero, add_zero]

/-- The word derivatives of a mode do not depend on time. -/
theorem sd_casS_add_time : ∀ (L : List (Fin d)) (k : Fin d → ℤ) (x : ST d) (s : ℝ),
    sd L (casS k) (x + s • ev 0) = sd L (casS k) x
  | [], k, x, s => casS_add_time k x s
  | i :: L, k, x, s => by
    rw [sd_cons_casS]
    simp only
    rw [sd_casS_add_time L (-k) x s]

/-- The derivative of `s ↦ φ(x + s e_μ)` at any `s₀` for a smooth `φ`. -/
theorem hasDerivAt_line_at {φ : ST d → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : ST d) (μ : Fin (d + 1))
    (s₀ : ℝ) : HasDerivAt (fun s : ℝ => φ (x + s • ev μ)) (pd φ μ (x + s₀ • ev μ)) s₀ := by
  have hφd : DifferentiableAt ℝ φ (x + s₀ • ev μ) := hφ.differentiable (by simp) _
  have hline : HasDerivAt (fun s : ℝ => x + s • ev μ) (ev μ) s₀ := by
    simpa using ((hasDerivAt_id s₀).smul_const (ev μ : ST d)).const_add x
  have := hφd.hasFDerivAt.comp_hasDerivAt s₀ hline
  exact this

/-- The spatial line derivative of a word derivative of a mode is the longer word derivative. -/
theorem hasDerivAt_sd_casS_space (L : List (Fin d)) (k : Fin d → ℤ) (x : ST d) (i : Fin d)
    (s₀ : ℝ) : HasDerivAt (fun s : ℝ => sd L (casS k) (x + s • ev i.succ))
      (sd (L ++ [i]) (casS k) (x + s₀ • ev i.succ)) s₀ := by
  rw [sd_append_single]
  exact hasDerivAt_line_at (contDiff_sd L (contDiff_casS k)) x i.succ s₀

theorem line_zero_succ' (x : ST d) (i : Fin d) (s : ℝ) : (x + s • ev i.succ) 0 = x 0 := by
  simp [Fin.succ_ne_zero]

theorem line_zero_zero (x : ST d) (s : ℝ) : (x + s • ev (0 : Fin (d + 1))) 0 = x 0 + s := by
  simp

end Modes

/-! ### Fields with coefficients decaying in every order -/

section Series

variable {d : ℕ}

/-- **Coefficient decay in every order, uniformly on a time set `I`**: the field is bounded in
every `H^r` on the slices `t ∈ I` (Fourier side). -/
def AllOrd (f : ST d → ℝ) (I : Set ℝ) : Prop :=
  ∀ r : ℕ, ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ I, ∀ S : Finset (Fin d → ℤ), ∑ k ∈ S, wq r k * coef f t k ^ 2 ≤ R ^ 2

theorem AllOrd.coef_le {f : ST d → ℝ} {I : Set ℝ} (h : AllOrd f I) (r : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ I, ∀ k, |coef f t k| ≤ R / Real.sqrt (wq r k) := by
  obtain ⟨R, hR, hb⟩ := h r
  refine ⟨R, hR, fun t ht k => ?_⟩
  have h1 := hb t ht {k}
  rw [Finset.sum_singleton] at h1
  have hw := wq_pos r k
  rw [le_div_iff₀ (Real.sqrt_pos.2 hw)]
  have h2 : (|coef f t k| * Real.sqrt (wq r k)) ^ 2 ≤ R ^ 2 := by
    rw [mul_pow, sq_abs, Real.sq_sqrt hw.le, mul_comm]; exact h1
  exact (abs_le_of_sq_le_sq' h2 hR).2

/-- **A uniform summable (nonnegative) majorant of the word-differentiated series.** -/
theorem AllOrd.majorant' {f : ST d → ℝ} {I : Set ℝ} (h : AllOrd f I) (L : List (Fin d)) :
    ∃ u : (Fin d → ℤ) → ℝ, Summable u ∧ (∀ t ∈ I, ∀ k x, |coef f t k * sd L (casS k) x| ≤ u k) ∧
      ∀ k, 0 ≤ u k := by
  obtain ⟨R, hR, hb⟩ := h.coef_le (L.length + (d + 1))
  refine ⟨fun k => 2 * R * (1 / Real.sqrt (wq (d + 1) k)),
    (summable_inv_sqrt_wq (by omega)).mul_left (2 * R), fun t ht k x => ?_,
    fun k => by positivity⟩
  rw [abs_mul]
  have h1 := hb t ht k
  have h2 := abs_sd_casS_le L k x
  have hw := wq_pos (d + 1) k
  have hwr := wq_pos (L.length + (d + 1)) k
  have h3 : Real.sqrt (muL L k) * Real.sqrt (wq (d + 1) k) ≤
      Real.sqrt (wq (L.length + (d + 1)) k) := by
    rw [← Real.sqrt_mul (muL_nonneg L k)]
    exact Real.sqrt_le_sqrt (muL_mul_wq_le L (d + 1) k)
  have h4 : Real.sqrt (muL L k) / Real.sqrt (wq (L.length + (d + 1)) k) ≤
      1 / Real.sqrt (wq (d + 1) k) := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 hwr) (Real.sqrt_pos.2 hw), one_mul]; exact h3
  calc |coef f t k| * |sd L (casS k) x|
      ≤ R / Real.sqrt (wq (L.length + (d + 1)) k) * (2 * Real.sqrt (muL L k)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 2 * R * (Real.sqrt (muL L k) / Real.sqrt (wq (L.length + (d + 1)) k)) := by ring
    _ ≤ 2 * R * (1 / Real.sqrt (wq (d + 1) k)) := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- **A uniform summable majorant of the word-differentiated series.** -/
theorem AllOrd.majorant {f : ST d → ℝ} {I : Set ℝ} (h : AllOrd f I) (L : List (Fin d)) :
    ∃ u : (Fin d → ℤ) → ℝ, Summable u ∧ ∀ t ∈ I, ∀ k x, |coef f t k * sd L (casS k) x| ≤ u k := by
  obtain ⟨u, hu, hb, -⟩ := h.majorant' L
  exact ⟨u, hu, hb⟩

/-- **The word-differentiated `cas` series** `Σ_k c_k(f, t) ∂^L cas_k(x)` (`t = x₀`). -/
def ser (L : List (Fin d)) (f : ST d → ℝ) (x : ST d) : ℝ :=
  ∑' k : Fin d → ℤ, coef f (x 0) k * sd L (casS k) x

/-- The series is continuous on `{x₀ ∈ I}`. -/
theorem continuousOn_ser {f : ST d → ℝ} (hf : Continuous f) {I : Set ℝ} (h : AllOrd f I)
    (L : List (Fin d)) : ContinuousOn (ser L f) {x | x 0 ∈ I} := by
  obtain ⟨u, hu, hb⟩ := h.majorant L
  refine continuousOn_tsum (fun k => ?_) hu fun k x hx => ?_
  · exact (((continuous_coef hf k).comp (continuous_apply 0)).mul
      (contDiff_sd L (contDiff_casS k)).continuous).continuousOn
  · rw [Real.norm_eq_abs]; exact hb (x 0) hx k x

/-- **Spatial line derivatives of the series**: `∂_i ser_L f = ser_{L i} f`. -/
theorem hasDerivAt_ser_space {f : ST d → ℝ} {I : Set ℝ} (h : AllOrd f I) (L : List (Fin d))
    {x : ST d} (hx : x 0 ∈ I) (i : Fin d) :
    HasDerivAt (fun s : ℝ => ser L f (x + s • ev i.succ)) (ser (L ++ [i]) f x) 0 := by
  obtain ⟨u, hu, hb⟩ := h.majorant L
  obtain ⟨u', hu', hb'⟩ := h.majorant (L ++ [i])
  have e : (fun s : ℝ => ser L f (x + s • ev i.succ)) =
      fun s => ∑' k, coef f (x 0) k * sd L (casS k) (x + s • ev i.succ) := by
    funext s; unfold ser; rw [line_zero_succ']
  rw [e]
  have hd := hasDerivAt_tsum (u := u') (g := fun k s => coef f (x 0) k * sd L (casS k)
      (x + s • ev i.succ)) (g' := fun k s => coef f (x 0) k * sd (L ++ [i]) (casS k)
      (x + s • ev i.succ)) (y₀ := (0 : ℝ)) hu'
    (fun k s => (hasDerivAt_sd_casS_space L k x i s).const_mul _)
    (fun k s => by rw [Real.norm_eq_abs]; exact hb' (x 0) hx k _)
    (Summable.of_norm_bounded hu fun k => by rw [Real.norm_eq_abs]; exact hb (x 0) hx k _) 0
  simpa [ser] using hd

/-- **Time derivative of the series**: if `∂_t c_k(f) = c_k(g)` on the open interval `I` and `g`
has coefficients decaying in every order, then `∂_t ser_L f = ser_L g` on `{x₀ ∈ I}`. -/
theorem hasDerivAt_ser_time {f g : ST d → ℝ} {a b : ℝ} (hf : AllOrd f (Ioo a b))
    (hg : AllOrd g (Ioo a b))
    (hdt : ∀ k, ∀ t ∈ Ioo a b, HasDerivAt (fun s => coef f s k) (coef g t k) t)
    (L : List (Fin d)) {x : ST d} (hx : x 0 ∈ Ioo a b) :
    HasDerivAt (fun s : ℝ => ser L f (x + s • ev 0)) (ser L g x) 0 := by
  obtain ⟨u, hu, hb⟩ := hf.majorant L
  obtain ⟨u', hu', hb'⟩ := hg.majorant L
  set J : Set ℝ := Ioo (a - x 0) (b - x 0) with hJ
  have hJmem : ∀ s ∈ J, x 0 + s ∈ Ioo a b := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have e : (fun s : ℝ => ser L f (x + s • ev 0)) =
      fun s => ∑' k, coef f (x 0 + s) k * sd L (casS k) x := by
    funext s; unfold ser; rw [line_zero_zero]
    exact tsum_congr fun k => by rw [sd_casS_add_time]
  rw [e]
  have h0J : (0 : ℝ) ∈ J := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hd := hasDerivAt_tsum_of_isPreconnected (u := u')
    (g := fun k s => coef f (x 0 + s) k * sd L (casS k) x)
    (g' := fun k s => coef g (x 0 + s) k * sd L (casS k) x) (t := J) (y₀ := 0) (y := 0) hu'
    isOpen_Ioo isPreconnected_Ioo
    (fun k s hs => by
      have h1 := (hdt k (x 0 + s) (hJmem s hs)).comp s ((hasDerivAt_id s).const_add (x 0))
      simpa using h1.mul_const (sd L (casS k) x))
    (fun k s hs => by rw [Real.norm_eq_abs]; exact hb' _ (hJmem s hs) k x) h0J
    (Summable.of_norm_bounded hu fun k => by
      rw [Real.norm_eq_abs]; exact hb _ (hJmem 0 h0J) k x) h0J
  simpa [ser] using hd

/-- The coefficients of a uniformly convergent `cas` series. -/
theorem coef_tsum_casS {c : (Fin d → ℤ) → ℝ} {u : (Fin d → ℤ) → ℝ} (hu : Summable u)
    (hb : ∀ k x, |c k * casS k x| ≤ u k) (t : ℝ) (l : Fin d → ℤ) :
    coef (fun x => ∑' k, c k * casS k x) t l = c l := by
  unfold coef sint
  have hint : ∀ k, Integrable (fun y : Fin d → ℝ => casS l (Fin.cons t y) *
      (c k * casS k (Fin.cons t y))) (volume.restrict (Icc (0 : Fin d → ℝ) 1)) := fun k =>
    ((((contDiff_casS l).continuous.comp (continuous_cons t)).mul (continuous_const.mul
      ((contDiff_casS k).continuous.comp (continuous_cons t))))).integrableOn_Icc
  have hnorm : Summable fun k => ∫ y in Icc (0 : Fin d → ℝ) 1,
      ‖casS l (Fin.cons t y) * (c k * casS k (Fin.cons t y))‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
      (fun k => ?_) (hu.mul_left 2)
    have hv : (volume (Icc (0 : Fin d → ℝ) 1)).toReal = 1 := by
      rw [PeriodicCube.volume_cube]; simp
    calc ∫ y in Icc (0 : Fin d → ℝ) 1, ‖casS l (Fin.cons t y) * (c k * casS k (Fin.cons t y))‖
        ≤ ∫ y in Icc (0 : Fin d → ℝ) 1, 2 * u k := by
          refine setIntegral_mono_on (hint k).norm (continuous_const.integrableOn_Icc)
            measurableSet_Icc fun y _ => ?_
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul (abs_casS_le l _) (hb k _) (abs_nonneg _) (by norm_num)
      _ = 2 * u k := by rw [setIntegral_const, measureReal_def, hv, one_smul]
  have h1 := integral_tsum_of_summable_integral_norm hint hnorm
  have e : (fun y : Fin d → ℝ => casS l (Fin.cons t y) *
      ∑' k, c k * casS k (Fin.cons t y)) =
      fun y => ∑' k, casS l (Fin.cons t y) * (c k * casS k (Fin.cons t y)) := by
    funext y; rw [tsum_mul_left]
  rw [e, ← h1]
  have h2 : ∀ k, ∫ y in Icc (0 : Fin d → ℝ) 1, casS l (Fin.cons t y) *
      (c k * casS k (Fin.cons t y)) = if k = l then c k else 0 := by
    intro k
    have := sint_casS_mul_casS l k t
    unfold sint at this
    have e2 : (fun y : Fin d → ℝ => casS l (Fin.cons t y) * (c k * casS k (Fin.cons t y))) =
        fun y => c k * (casS l (Fin.cons t y) * casS k (Fin.cons t y)) := by
      funext y; ring
    rw [e2, integral_const_mul, this]
    by_cases hk : k = l
    · subst hk; simp
    · simp [hk, Ne.symm hk]
  simp_rw [h2]
  rw [tsum_ite_eq]

/-- **The series represents the field**: for a continuous periodic field with coefficients
decaying in every order on `I`, `f(x) = Σ_k c_k(f, x₀) cas_k(x)` for `x₀ ∈ I`. -/
theorem ser_nil_eq {f : ST d → ℝ} (hf : Continuous f) (hfp : IsSPeriodic f) {I : Set ℝ}
    (h : AllOrd f I) {x : ST d} (hx : x 0 ∈ I) : ser [] f x = f x := by
  obtain ⟨u, hu, hb⟩ := h.majorant []
  set t := x 0 with ht
  set g : ST d → ℝ := fun z => ∑' k, coef f t k * casS k z with hg
  have hbt : ∀ k z, |coef f t k * casS k z| ≤ u k := fun k z => by
    simpa using hb t hx k z
  have hgc : Continuous g :=
    continuous_tsum (fun k => continuous_const.mul (contDiff_casS k).continuous) hu
      fun k z => by rw [Real.norm_eq_abs]; exact hbt k z
  set h' : ST d → ℝ := fun z => f (Fin.cons t (Fin.tail z)) - g z with hh'
  have hcons : Continuous fun z : ST d => (Fin.cons t (Fin.tail z) : ST d) :=
    (continuous_cons t).comp (continuous_pi fun i => continuous_apply i.succ)
  have hh'c : Continuous h' := (hf.comp hcons).sub hgc
  have hh'p : IsSPeriodic h' := by
    intro m z
    simp only [hh', hg]
    congr 1
    · have : (Fin.tail (z + sshift m) : Fin d → ℝ) = Fin.tail z + zvec m := by
        funext i; simp [Fin.tail, sshift, zvec]
      rw [this]
      exact hfp.slice t m (Fin.tail z)
    · exact tsum_congr fun k => by rw [isSPeriodic_casS k m z]
  have hcoef : ∀ s k, coef h' s k = 0 := by
    intro s k
    have h1 : coef (fun z => f (Fin.cons t (Fin.tail z))) s k = coef f t k :=
      KatoPersist.coef_congr_slice (fun y => by simp) k
    have e : h' = fun z => (fun z => f (Fin.cons t (Fin.tail z))) z - g z := rfl
    have hc1 : Continuous fun z : ST d => f (Fin.cons t (Fin.tail z)) := hf.comp hcons
    rw [e, coef_sub hc1 hgc, h1, coef_tsum_casS hu hbt s k, sub_self]
  have h0 := eq_zero_of_coef_eq_zero hh'c hh'p t (hcoef t) (Fin.tail x)
  have hx' : (Fin.cons t (Fin.tail x) : ST d) = x := by rw [ht]; exact Fin.cons_self_tail x
  simp only [hh', hx'] at h0
  unfold ser
  have : g x = ∑' k, coef f (x 0) k * sd [] (casS k) x := rfl
  rw [← this]
  linarith

end Series

/-! ### Jets of a field family and jet functions -/

section Jets

variable {d n : ℕ}

/-- The jet coordinates of order `M`: a component and a word of length `≤ M`. -/
abbrev JI (d n M : ℕ) := Fin n × (wordsLE d M)

theorem mem_wordsLE_of_le {M K : ℕ} (h : M ≤ K) {L : List (Fin d)} (hL : L ∈ wordsLE d M) :
    L ∈ wordsLE d K :=
  mem_wordsLE.2 ((mem_wordsLE.1 hL).trans h)

theorem mem_wordsLE_append {M : ℕ} {L : List (Fin d)} (hL : L ∈ wordsLE d M) (i : Fin d) :
    L ++ [i] ∈ wordsLE d (M + 1) :=
  mem_wordsLE.2 (by simp [mem_wordsLE.1 hL])

/-- Restriction of jets to a lower order. -/
def resLE {M K : ℕ} (h : M ≤ K) : (JI d n K → ℝ) →L[ℝ] (JI d n M → ℝ) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj
    ((p.1, ⟨p.2.1, mem_wordsLE_of_le h p.2.2⟩) : JI d n K)

theorem resLE_apply {M K : ℕ} (h : M ≤ K) (w : JI d n K → ℝ) (p : JI d n M) :
    resLE h w p = w (p.1, ⟨p.2.1, mem_wordsLE_of_le h p.2.2⟩) := rfl

/-- The jet coordinates of the spatial derivative `∂_i`. -/
def shiftL {M : ℕ} (i : Fin d) : (JI d n (M + 1) → ℝ) →L[ℝ] (JI d n M → ℝ) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj
    ((p.1, ⟨p.2.1 ++ [i], mem_wordsLE_append p.2.2 i⟩) : JI d n (M + 1))

theorem shiftL_apply {M : ℕ} (i : Fin d) (w : JI d n (M + 1) → ℝ) (p : JI d n M) :
    shiftL i w p = w (p.1, ⟨p.2.1 ++ [i], mem_wordsLE_append p.2.2 i⟩) := rfl

/-- **The total spatial derivative** of a jet function: `D_iΨ(w) = DΨ(w|_M)(∂_i w)`. -/
def DS {M : ℕ} (i : Fin d) (Ψ : (JI d n M → ℝ) → ℝ) : (JI d n (M + 1) → ℝ) → ℝ :=
  fun w => fderiv ℝ Ψ (resLE (Nat.le_succ M) w) (shiftL i w)

theorem contDiff_DS {M : ℕ} (i : Fin d) {Ψ : (JI d n M → ℝ) → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (DS i Ψ) := by
  unfold DS
  exact ((hΨ.fderiv_right (m := ∞) (by simp)).comp (resLE (Nat.le_succ M)).contDiff).clm_apply
    (shiftL i).contDiff

/-- The jet of order `M` of a field family: the word-differentiated series of its components. -/
def jet (U : Fin n → ST d → ℝ) (M : ℕ) (x : ST d) : JI d n M → ℝ :=
  fun p => ser p.2.1 (U p.1) x

theorem resLE_jet (U : Fin n → ST d → ℝ) {M K : ℕ} (h : M ≤ K) (x : ST d) :
    resLE h (jet U K x) = jet U M x := rfl

variable {U : Fin n → ST d → ℝ} {I : Set ℝ}

theorem continuousOn_jet (hU : ∀ b, Continuous (U b)) (h : ∀ b, AllOrd (U b) I) (M : ℕ) :
    ContinuousOn (jet U M) {x | x 0 ∈ I} :=
  continuousOn_pi.2 fun p => continuousOn_ser (hU p.1) (h p.1) p.2.1

/-- The jets are uniformly bounded on `{x₀ ∈ I}`. -/
theorem exists_jet_bound (h : ∀ b, AllOrd (U b) I) (M : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ST d, x 0 ∈ I → ‖jet U M x‖ ≤ B := by
  have hp : ∀ p : JI d n M, ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ST d, x 0 ∈ I → |ser p.2.1 (U p.1) x| ≤ B := by
    intro p
    obtain ⟨u, hu, hb, hu0⟩ := (h p.1).majorant' p.2.1
    refine ⟨∑' k, u k, tsum_nonneg hu0, fun x hx => ?_⟩
    · unfold ser
      have hs : Summable fun k => coef (U p.1) (x 0) k * sd p.2.1 (casS k) x :=
        Summable.of_norm_bounded hu fun k => by rw [Real.norm_eq_abs]; exact hb _ hx k x
      calc |∑' k, coef (U p.1) (x 0) k * sd p.2.1 (casS k) x|
          ≤ ∑' k, |coef (U p.1) (x 0) k * sd p.2.1 (casS k) x| := by
            have := norm_tsum_le_tsum_norm hs.norm
            simpa [Real.norm_eq_abs] using this
        _ ≤ ∑' k, u k := hs.abs.tsum_le_tsum (fun k => hb _ hx k x) hu
  choose B hB0 hB using hp
  refine ⟨∑ p, B p, Finset.sum_nonneg fun p _ => hB0 p, fun x hx => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun p _ => hB0 p)).2 fun p => ?_
  rw [Real.norm_eq_abs]
  exact (hB p x hx).trans (Finset.single_le_sum (fun p _ => hB0 p) (Finset.mem_univ p))

end Jets

/-! ### Jet functions: chain rules, frozen slices and coefficient decay -/

section JetFunctions

variable {d n : ℕ} {U : Fin n → ST d → ℝ} {a b : ℝ}

theorem cons_tail_line_succ (t : ℝ) (z : ST d) (i : Fin d) (s : ℝ) :
    (Fin.cons t (Fin.tail (z + s • ev i.succ)) : ST d) = Fin.cons t (Fin.tail z) + s • ev i.succ := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [Fin.succ_ne_zero]
  | succ j => simp [Fin.tail, Pi.single_apply]

theorem cons_tail_line_zero (t : ℝ) (z : ST d) (s : ℝ) :
    (Fin.cons t (Fin.tail (z + s • ev (0 : Fin (d + 1)))) : ST d) = Fin.cons t (Fin.tail z) := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.tail, Fin.succ_ne_zero]

/-- **The spatial chain rule for jet functions**: `∂_i Ψ(jet_M U) = (D_iΨ)(jet_{M+1} U)`. -/
theorem hasDerivAt_jetFun_space (hall : ∀ c, AllOrd (U c) (Ioo a b)) {M : ℕ}
    {Ψ : (JI d n M → ℝ) → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) {x : ST d} (hx : x 0 ∈ Ioo a b) (i : Fin d) :
    HasDerivAt (fun s : ℝ => Ψ (jet U M (x + s • ev i.succ))) (DS i Ψ (jet U (M + 1) x)) 0 := by
  have hj : HasDerivAt (fun s : ℝ => jet U M (x + s • ev i.succ))
      (shiftL i (jet U (M + 1) x)) 0 :=
    hasDerivAt_pi.2 fun p => hasDerivAt_ser_space (hall p.1) p.2.1 hx i
  have hx0 : jet U M (x + (0 : ℝ) • ev i.succ) = jet U M x := by simp
  have hd : HasFDerivAt Ψ (fderiv ℝ Ψ (jet U M (x + (0 : ℝ) • ev i.succ)))
      (jet U M (x + (0 : ℝ) • ev i.succ)) :=
    (hΨ.differentiable (by simp) _).hasFDerivAt
  have := hd.comp_hasDerivAt (0 : ℝ) hj
  rw [hx0] at this
  unfold DS
  rw [resLE_jet]
  exact this

/-- The time-frozen lift `z ↦ Ψ(jet_M U(t, z_space))` of a jet function. -/
def frz (U : Fin n → ST d → ℝ) (t : ℝ) (M : ℕ) (Ψ : (JI d n M → ℝ) → ℝ) (z : ST d) : ℝ :=
  Ψ (jet U M (Fin.cons t (Fin.tail z)))

theorem isSPeriodic_ser (L : List (Fin d)) (f : ST d → ℝ) : IsSPeriodic (ser L f) := by
  intro m x
  unfold ser
  have h0 : (x + sshift m) 0 = x 0 := by simp [sshift]
  rw [h0]
  exact tsum_congr fun k => by rw [isSPeriodic_sd L (isSPeriodic_casS k) m x]

theorem isSPeriodic_frz (t : ℝ) (M : ℕ) (Ψ : (JI d n M → ℝ) → ℝ) :
    IsSPeriodic (frz U t M Ψ) := by
  intro m z
  unfold frz
  have : (Fin.cons t (Fin.tail (z + sshift m)) : ST d) = Fin.cons t (Fin.tail z) + sshift m := by
    funext μ
    induction μ using Fin.cases with
    | zero => simp [sshift]
    | succ j => simp [Fin.tail, sshift]
  rw [this]
  congr 1
  funext p
  exact isSPeriodic_ser p.2.1 (U p.1) m _

theorem continuous_frz (hU : ∀ c, Continuous (U c)) (hall : ∀ c, AllOrd (U c) (Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo a b) {M : ℕ} {Ψ : (JI d n M → ℝ) → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) :
    Continuous (frz U t M Ψ) := by
  have hcons : Continuous fun z : ST d => (Fin.cons t (Fin.tail z) : ST d) :=
    (continuous_cons t).comp (continuous_pi fun i => continuous_apply i.succ)
  have hj : Continuous fun z : ST d => jet U M (Fin.cons t (Fin.tail z)) :=
    (continuousOn_jet hU hall M).comp_continuous hcons fun z => by simpa using ht
  exact hΨ.continuous.comp hj

theorem hasDerivAt_frz_space (hall : ∀ c, AllOrd (U c) (Ioo a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    {M : ℕ} {Ψ : (JI d n M → ℝ) → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (z : ST d) (i : Fin d) :
    HasDerivAt (fun s : ℝ => frz U t M Ψ (z + s • ev i.succ)) (frz U t (M + 1) (DS i Ψ) z) 0 := by
  unfold frz
  simp only [cons_tail_line_succ]
  exact hasDerivAt_jetFun_space hall hΨ (by simpa using ht) i

/-- **The frozen lifts are smooth.** -/
theorem contDiff_frz (hU : ∀ c, Continuous (U c)) (hall : ∀ c, AllOrd (U c) (Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo a b) {M : ℕ} {Ψ : (JI d n M → ℝ) → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (frz U t M Ψ) := by
  set 𝒞 : (ST d → ℝ) → Prop := fun g =>
    ∃ (M : ℕ) (Ψ : (JI d n M → ℝ) → ℝ), ContDiff ℝ ∞ Ψ ∧ g = frz U t M Ψ with h𝒞
  have key := contDiffOn_top_of_closed (N := d + 1) isOpen_univ 𝒞
    (fun g ⟨M, Ψ, hΨ, hg⟩ => by rw [hg]; exact (continuous_frz hU hall ht hΨ).continuousOn)
    (fun g ⟨M, Ψ, hΨ, hg⟩ μ => by
      subst hg
      induction μ using Fin.cases with
      | zero =>
        refine ⟨fun _ => 0, ⟨0, fun _ => 0, contDiff_const, rfl⟩, fun z _ => ?_⟩
        have : (fun s : ℝ => frz U t M Ψ (z + s • Pi.single (0 : Fin (d + 1)) 1)) =
            fun _ => frz U t M Ψ z := by
          funext s; unfold frz; rw [show (Pi.single (0 : Fin (d + 1)) (1 : ℝ) : ST d) = ev 0 from rfl,
            cons_tail_line_zero]
        rw [this]; exact hasDerivAt_const _ _
      | succ i =>
        exact ⟨frz U t (M + 1) (DS i Ψ), ⟨M + 1, DS i Ψ, contDiff_DS i hΨ, rfl⟩,
          fun z _ => hasDerivAt_frz_space hall ht hΨ z i⟩)
  exact contDiffOn_univ.1 (key _ ⟨M, Ψ, hΨ, rfl⟩)

/-- The word derivatives of the frozen lifts are bounded uniformly in `t ∈ I`. -/
theorem sd_frz_bound (hU : ∀ c, Continuous (U c)) (hall : ∀ c, AllOrd (U c) (Ioo a b)) :
    ∀ (L : List (Fin d)) (M : ℕ) (Ψ : (JI d n M → ℝ) → ℝ), ContDiff ℝ ∞ Ψ →
      ∃ C : ℝ, ∀ t ∈ Ioo a b, ∀ z, |sd L (frz U t M Ψ) z| ≤ C
  | [], M, Ψ, hΨ => by
    obtain ⟨B, hB0, hB⟩ := exists_jet_bound (U := U) hall M
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : JI d n M → ℝ) B).exists_bound_of_continuousOn
      hΨ.continuous.continuousOn
    refine ⟨C, fun t ht z => ?_⟩
    have hm : jet U M (Fin.cons t (Fin.tail z)) ∈ Metric.closedBall (0 : JI d n M → ℝ) B := by
      rw [mem_closedBall_zero_iff]; exact hB _ (by simpa using ht)
    have := hC _ hm
    simpa [frz, Real.norm_eq_abs] using this
  | i :: L, M, Ψ, hΨ => by
    obtain ⟨C, hC⟩ := sd_frz_bound hU hall L (M + 1) (DS i Ψ) (contDiff_DS i hΨ)
    refine ⟨C, fun t ht z => ?_⟩
    have e : pd (frz U t M Ψ) i.succ = frz U t (M + 1) (DS i Ψ) := by
      funext z
      exact (hasDerivAt_line0 (contDiff_frz hU hall ht hΨ) z i.succ).unique
        (hasDerivAt_frz_space hall ht hΨ z i)
    rw [sd_cons, e]
    exact hC t ht z

/-- **Jet functions have coefficients decaying in every order.** -/
theorem allOrd_of_jetFun (hU : ∀ c, Continuous (U c)) (hall : ∀ c, AllOrd (U c) (Ioo a b))
    {f : ST d → ℝ} {M : ℕ} {Ψ : (JI d n M → ℝ) → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hf : ∀ x : ST d, x 0 ∈ Ioo a b → f x = Ψ (jet U M x)) : AllOrd f (Ioo a b) := by
  intro r
  have hC : ∀ L : List (Fin d), ∃ C : ℝ, ∀ t ∈ Ioo a b, ∀ z, |sd L (frz U t M Ψ) z| ≤ C :=
    fun L => sd_frz_bound hU hall L M Ψ hΨ
  choose C hC using hC
  refine ⟨Real.sqrt (∑ L ∈ wordsLE d r, C L ^ 2), Real.sqrt_nonneg _, fun t ht S => ?_⟩
  rw [Real.sq_sqrt (Finset.sum_nonneg fun L _ => sq_nonneg _)]
  have hcoef : ∀ k, coef f t k = coef (frz U t M Ψ) 0 k := fun k =>
    KatoPersist.coef_congr_slice (fun y => by
      rw [hf _ (by simpa using ht)]; simp [frz]) k
  simp only [hcoef]
  refine (bessel_Hq r S (contDiff_frz hU hall ht hΨ) (isSPeriodic_frz t M Ψ) 0).trans ?_
  unfold Q
  refine Finset.sum_le_sum fun L _ => ?_
  have hv : (volume (Icc (0 : Fin d → ℝ) 1)).toReal = 1 := by
    rw [PeriodicCube.volume_cube]; simp
  calc ∫ y in Icc (0 : Fin d → ℝ) 1, sd L (frz U t M Ψ) (Fin.cons 0 y) ^ 2
      ≤ ∫ y in Icc (0 : Fin d → ℝ) 1, C L ^ 2 := by
        refine setIntegral_mono_on ?_ continuous_const.integrableOn_Icc measurableSet_Icc
          fun y _ => ?_
        · exact (((contDiff_sd L (contDiff_frz hU hall ht hΨ)).continuous.comp
            (continuous_cons 0)).pow 2).integrableOn_Icc
        · have := hC L t ht (Fin.cons 0 y)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = C L ^ 2 := by rw [setIntegral_const, measureReal_def, hv, one_smul]

end JetFunctions

/-! ### Smoothness of solutions bounded in every order -/

section Main

variable {d n : ℕ} {U : Fin n → ST d → ℝ} {a b : ℝ}

/-- `x ↦ Ψ(jet_M U(x))` on the open slab. -/
def IsJetFun (U : Fin n → ST d → ℝ) (a b : ℝ) (f : ST d → ℝ) : Prop :=
  ∃ (M : ℕ) (Ψ : (JI d n M → ℝ) → ℝ), ContDiff ℝ ∞ Ψ ∧ ∀ x : ST d, x 0 ∈ Ioo a b → f x = Ψ (jet U M x)

theorem isJetFun_comp (hall : ∀ c, AllOrd (U c) (Ioo a b)) :
    ∀ (L : List (Fin d)) {f : ST d → ℝ}, Continuous f → IsSPeriodic f → AllOrd f (Ioo a b) →
      IsJetFun U a b f → IsJetFun U a b (ser L f) := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro f hf hfp hfa ⟨M, Ψ, hΨ, hfΨ⟩
    exact ⟨M, Ψ, hΨ, fun x hx => by rw [ser_nil_eq hf hfp hfa hx, hfΨ x hx]⟩
  | append_singleton L i ih =>
    intro f hf hfp hfa hJ
    obtain ⟨M, Θ, hΘ, hfΘ⟩ := ih hf hfp hfa hJ
    refine ⟨M + 1, DS i Θ, contDiff_DS i hΘ, fun x hx => ?_⟩
    have h1 := hasDerivAt_ser_space hfa L hx i
    have h2 := hasDerivAt_jetFun_space hall hΘ hx i
    have e : (fun s : ℝ => ser L f (x + s • ev i.succ)) =
        fun s => Θ (jet U M (x + s • ev i.succ)) := by
      funext s
      exact hfΘ _ (by rw [line_zero_succ']; exact hx)
    rw [e] at h1
    exact h1.unique h2

/-- **Coefficient derivative of a classical solution**: if `∂_t U = G` pointwise on `(a, b)` with
`G` continuous, then `∂_t c_k(U(t)) = c_k(G(t))`. -/
theorem hasDerivAt_coef_of_time {f G : ST d → ℝ} (hf : Continuous f) (hG : Continuous G)
    (htime : ∀ t ∈ Ioo a b, ∀ y, HasDerivAt (fun s => f (Fin.cons s y)) (G (Fin.cons t y)) t)
    (k : Fin d → ℤ) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => coef f s k) (coef G t k) t := by
  obtain ⟨δ, hδ, hδI⟩ : ∃ δ > 0, Icc (t - δ) (t + δ) ⊆ Ioo a b := by
    refine ⟨min (t - a) (b - t) / 2, by have := ht.1; have := ht.2; positivity, fun s hs => ?_⟩
    have h1 := min_le_left (t - a) (b - t)
    have h2 := min_le_right (t - a) (b - t)
    have hpos : 0 < min (t - a) (b - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  set K : Set (ℝ × (Fin d → ℝ)) := Icc (t - δ) (t + δ) ×ˢ Icc (0 : Fin d → ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hGc : Continuous fun p : ℝ × (Fin d → ℝ) => G (Fin.cons p.1 p.2) :=
    hG.comp (continuous_cons2.comp (continuous_fst.prodMk continuous_snd))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hGc.continuousOn
  unfold coef sint
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (fun y : Fin d → ℝ => casS k (Fin.cons s y) *
      f (Fin.cons s y)) (volume.restrict (Icc (0 : Fin d → ℝ) 1)) := fun s =>
    (((contDiff_casS k).continuous.comp (continuous_cons s)).mul
      (hf.comp (continuous_cons s))).aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict
      (Icc (0 : Fin d → ℝ) 1)) (bound := fun _ => 2 * C) (x₀ := t)
    (F := fun s y => casS k (Fin.cons s y) * f (Fin.cons s y))
    (F' := fun s y => casS k (Fin.cons s y) * G (Fin.cons s y))
    (Icc_mem_nhds (show t - δ < t by linarith) (show t < t + δ by linarith))
    (Eventually.of_forall hmeas)
    ((((contDiff_casS k).continuous.comp (continuous_cons t)).mul
      (hf.comp (continuous_cons t)))).integrableOn_Icc
    ((((contDiff_casS k).continuous.comp (continuous_cons t)).mul
      (hG.comp (continuous_cons t)))).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Icc fun y hy s hs => by
      rw [norm_mul, Real.norm_eq_abs]
      have := hC (s, y) ⟨hs, hy⟩
      exact mul_le_mul (abs_casS_le k _) this (norm_nonneg _) (by norm_num))
    (continuous_const.integrableOn_Icc)
    (Eventually.of_forall fun y s hs => by
      have e : (fun s' => casS k (Fin.cons s' y : ST d) * f (Fin.cons s' y)) =
          fun s' => casS k (Fin.cons t y : ST d) * f (Fin.cons s' y) := by
        funext s'; rw [casS_cons, casS_cons]
      have := (htime s (hδI hs) y).const_mul (casS k (Fin.cons t y))
      show HasDerivAt (fun s' => casS k (Fin.cons s' y : ST d) * f (Fin.cons s' y)) _ s
      rw [e, casS_cons k s y, ← casS_cons k t y]
      exact this)
  exact h.2

/-- **A classical solution bounded in every Sobolev order is `C^∞`** (`Σ = 𝕋^d`): let `U` be a
continuous spatially periodic field with continuous periodic spatial derivatives `P`, solving
`∂_tU = F(U) - Σ_i A^i(U)P_i` on `(a, b) × 𝕋^d` (smooth `A`, `F`), with coefficients decaying in
every order uniformly on `(a, b)`.  Then every component is `C^∞` on the open slab. -/
theorem contDiffOn_of_allOrd {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {P : Fin n → Fin d → ST d → ℝ}
    (hU : ∀ c, Continuous (U c)) (hUp : ∀ c, IsSPeriodic (U c))
    (hP : ∀ c i, Continuous (P c i)) (hPp : ∀ c i, IsSPeriodic (P c i))
    (hspace : ∀ c (i : Fin d) x, HasDerivAt (fun s : ℝ => U c (x + s • ev i.succ)) (P c i x) 0)
    (htime : ∀ c, ∀ t ∈ Ioo a b, ∀ y, HasDerivAt (fun s => U c (Fin.cons s y))
      (genP A F U P c (Fin.cons t y)) t)
    (hall : ∀ c, AllOrd (U c) (Ioo a b)) : ∀ c, ContDiffOn ℝ ∞ (U c) (openSlab a b) := by
  -- the spatial derivatives are the series of the words of length one
  have hPser : ∀ c (i : Fin d) (x : ST d), x 0 ∈ Ioo a b → P c i x = ser [i] (U c) x := by
    intro c i x hx
    have h1 := hasDerivAt_ser_space (hall c) [] hx i
    have e : (fun s : ℝ => ser [] (U c) (x + s • ev i.succ)) = fun s => U c (x + s • ev i.succ) := by
      funext s; exact ser_nil_eq (hU c) (hUp c) (hall c) (by rw [line_zero_succ']; exact hx)
    rw [e] at h1
    exact (hspace c i x).unique h1
  -- the generator is a jet function of order one
  set G : Fin n → ST d → ℝ := fun c => genP A F U P c with hGdef
  have hnil : ∀ (M : ℕ), ([] : List (Fin d)) ∈ wordsLE d M := fun M => mem_wordsLE.2 (by simp)
  have hone : ∀ i : Fin d, [i] ∈ wordsLE d 1 := fun i => mem_wordsLE.2 (by simp)
  set Φ : Fin n → (JI d n 1 → ℝ) → ℝ := fun c w =>
    F c (fun c' => w (c', ⟨[], hnil 1⟩)) -
      ∑ i, ∑ c', A i c c' (fun c'' => w (c'', ⟨[], hnil 1⟩)) * w (c', ⟨[i], hone i⟩) with hΦ
  have hΦs : ∀ c, ContDiff ℝ ∞ (Φ c) := by
    intro c
    have hv : ContDiff ℝ ∞ fun w : JI d n 1 → ℝ => fun c' => w (c', ⟨[], hnil 1⟩) :=
      contDiff_pi.2 fun c' => contDiff_apply ℝ ℝ _
    exact ((hF c).comp hv).sub (ContDiff.sum fun i _ => ContDiff.sum fun c' _ =>
      ((hA i c c').comp hv).mul (contDiff_apply ℝ ℝ _))
  have hGJ : ∀ c, ∀ x : ST d, x 0 ∈ Ioo a b → G c x = Φ c (jet U 1 x) := by
    intro c x hx
    simp only [hGdef, hΦ, genP, jet]
    congr 1
    · congr 1; funext c'; exact (ser_nil_eq (hU c') (hUp c') (hall c') hx).symm
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c' _ => ?_
      congr 1
      · congr 1; funext c''; exact (ser_nil_eq (hU c'') (hUp c'') (hall c'') hx).symm
      · exact hPser c' i x hx
  have hGc : ∀ c, Continuous (G c) := fun c =>
    ((hF c).continuous.comp (continuous_pi hU)).sub (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun c' _ => ((hA i c c').continuous.comp
        (continuous_pi hU)).mul (hP c' i))
  have hGp : ∀ c, IsSPeriodic (G c) := by
    intro c m x
    simp only [hGdef, genP, hUp _ m x, hPp _ _ m x]
  have hGall : ∀ c, AllOrd (G c) (Ioo a b) := fun c => allOrd_of_jetFun hU hall (hΦs c) (hGJ c)
  have hGser : ∀ c (L : List (Fin d)), IsJetFun U a b (ser L (G c)) := fun c L =>
    isJetFun_comp hall L (hGc c) (hGp c) (hGall c) ⟨1, Φ c, hΦs c, hGJ c⟩
  have hcoefd : ∀ c k, ∀ t ∈ Ioo a b, HasDerivAt (fun s => coef (U c) s k) (coef (G c) t k) t :=
    fun c k t ht => hasDerivAt_coef_of_time (hU c) (hGc c) (htime c) k ht
  -- the class of jet functions is closed under partial derivatives
  have hcl : ∀ f, IsJetFun U a b f → ∀ μ : Fin (d + 1), ∃ g, IsJetFun U a b g ∧
      ∀ x ∈ openSlab (d := d) a b, HasDerivAt (fun s : ℝ => f (x + s • Pi.single μ 1)) (g x) 0 := by
    intro f ⟨M, Ψ, hΨ, hfΨ⟩ μ
    induction μ using Fin.cases with
    | zero =>
      have hp : ∀ p : JI d n M, IsJetFun U a b (ser p.2.1 (G p.1)) := fun p => hGser p.1 p.2.1
      choose Mp Θ hΘ hΘeq using hp
      set K := M + ∑ p, Mp p with hKdef
      have hMK : M ≤ K := Nat.le_add_right _ _
      have hpK : ∀ p, Mp p ≤ K := fun p => le_add_left (Finset.single_le_sum
        (f := Mp) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p))
      refine ⟨fun x => fderiv ℝ Ψ (jet U M x) (fun p => ser p.2.1 (G p.1) x),
        ⟨K, fun w => fderiv ℝ Ψ (resLE hMK w) (fun p => Θ p (resLE (hpK p) w)), ?_, ?_⟩, ?_⟩
      · exact ((hΨ.fderiv_right (m := ∞) (by simp)).comp (resLE hMK).contDiff).clm_apply
          (contDiff_pi.2 fun p => (hΘ p).comp (resLE (hpK p)).contDiff)
      · intro x hx
        simp only [resLE_jet]
        congr 1
        funext p
        exact hΘeq p x hx
      · intro x hx
        have hj : HasDerivAt (fun s : ℝ => jet U M (x + s • ev 0))
            (fun p => ser p.2.1 (G p.1) x) 0 :=
          hasDerivAt_pi.2 fun p => hasDerivAt_ser_time (hall p.1) (hGall p.1)
            (hcoefd p.1) p.2.1 hx
        have hd : HasFDerivAt Ψ (fderiv ℝ Ψ (jet U M (x + (0 : ℝ) • ev 0)))
            (jet U M (x + (0 : ℝ) • ev 0)) := (hΨ.differentiable (by simp) _).hasFDerivAt
        have h2 := hd.comp_hasDerivAt (0 : ℝ) hj
        simp only [zero_smul, add_zero] at h2
        refine h2.congr_of_eventuallyEq ?_
        have hO := (isOpen_openSlab (d := d) a b).mem_nhds hx
        have hline : Continuous fun s : ℝ => x + s • (ev 0 : ST d) :=
          continuous_const.add (continuous_id.smul continuous_const)
        have hO' : openSlab (d := d) a b ∈ 𝓝 (x + (0 : ℝ) • (ev 0 : ST d)) := by
          rw [zero_smul, add_zero]; exact hO
        have hev := hline.continuousAt.preimage_mem_nhds hO'
        filter_upwards [hev] with s hs
        exact hfΨ _ hs
    | succ i =>
      refine ⟨fun x => DS i Ψ (jet U (M + 1) x), ⟨M + 1, DS i Ψ, contDiff_DS i hΨ,
        fun x _ => rfl⟩, fun x hx => ?_⟩
      have h2 := hasDerivAt_jetFun_space hall hΨ hx i
      have hev : (Pi.single i.succ (1 : ℝ) : ST d) = ev i.succ := rfl
      have e : (fun s : ℝ => f (x + s • Pi.single i.succ 1)) =
          fun s => Ψ (jet U M (x + s • ev i.succ)) := by
        funext s
        rw [hev]
        exact hfΨ _ (by rw [line_zero_succ']; exact hx)
      rw [e]; exact h2
  have hcont : ∀ f, IsJetFun U a b f → ContinuousOn f (openSlab (d := d) a b) := by
    intro f ⟨M, Ψ, hΨ, hfΨ⟩
    exact (hΨ.continuous.comp_continuousOn (continuousOn_jet hU hall M)).congr fun x hx => hfΨ x hx
  have key := contDiffOn_top_of_closed (N := d + 1) (isOpen_openSlab a b) (IsJetFun U a b)
    hcont hcl
  intro c
  refine key (U c) ⟨0, fun w => w (c, ⟨[], hnil 0⟩), contDiff_apply ℝ ℝ _, fun x hx => ?_⟩
  exact (ser_nil_eq (hU c) (hUp c) (hall c) hx).symm

end Main

/-! ### Kato's theorem with smooth solutions -/

section Kato

variable {d n : ℕ}

theorem allOrd_of_bounds {U : Fin n → ST d → ℝ} {I : Set ℝ} {q : ℕ}
    (h : ∀ j : ℕ, ∃ Rj : ℝ, 0 ≤ Rj ∧ ∀ t ∈ I, ∀ S : Finset (Fin d → ℤ),
      ∑ b, ∑ k ∈ S, wq (q + j) k * coef (U b) t k ^ 2 ≤ Rj ^ 2) (c : Fin n) :
    AllOrd (U c) I := by
  intro r
  obtain ⟨R, hR, hb⟩ := h (r - q)
  refine ⟨R, hR, fun t ht S => ?_⟩
  calc ∑ k ∈ S, wq r k * coef (U c) t k ^ 2 ≤ ∑ k ∈ S, wq (q + (r - q)) k * coef (U c) t k ^ 2 :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (wq_mono (by omega) k)
          (sq_nonneg _)
    _ ≤ ∑ b, ∑ k ∈ S, wq (q + (r - q)) k * coef (U b) t k ^ 2 :=
        Finset.single_le_sum (f := fun b => ∑ k ∈ S, wq (q + (r - q)) k * coef (U b) t k ^ 2)
          (fun b _ => Finset.sum_nonneg fun k _ => mul_nonneg (wq_nonneg _ k) (sq_nonneg _))
          (Finset.mem_univ c)
    _ ≤ R ^ 2 := hb t ht S

/-- **Kato's theorem with smooth solutions** (`Σ = 𝕋^d`, persistence of regularity): for
`m > d/2`, `q ≥ 2m + 1`, smooth real symmetric `A^i`, smooth `F` and every radius `R₀` there is
`T > 0` such that every smooth periodic datum with `‖U₀‖_{H^q} ≤ R₀` has a classical solution on
`(-T, T) × 𝕋^d` (`TwoSidedSol`) which is `C^∞` on the open slab `(-T, T) × ℝ^d`. -/
theorem kato_two_sided_smooth {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m + 1 ≤ q)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
      energyQ q U₀ 0 ≤ R₀ ^ 2 →
      ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ), TwoSidedSol A F U₀ T U P ∧
        ∀ b, ContDiffOn ℝ ∞ (U b) (openSlab (-T) T) := by
  obtain ⟨T, hT, h⟩ := KatoPersist.kato_two_sided_allOrders (A := A) (F := F) hm hq hA hsym hF hR₀
  refine ⟨T, hT, fun U₀ hU hUp hE => ?_⟩
  obtain ⟨U, P, hsol, hb⟩ := h U₀ hU hUp hE
  exact ⟨U, P, hsol, contDiffOn_of_allOrd hA hF hsol.contU hsol.perU hsol.contP hsol.perP
    hsol.space hsol.time (allOrd_of_bounds hb)⟩

end Kato

end RenewalGeometry.KatoSmooth
