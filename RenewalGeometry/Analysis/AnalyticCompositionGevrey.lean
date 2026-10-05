/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Gevrey bounds for compositions with real-analytic maps

Generic infrastructure (no renewal notions) for the strip-analyticity step of `thm:native-source`
of the Einstein–Standard-Model action-closure manuscript ("by Bernstein estimates the
low-frequency field changes by at most a fixed constant times `K|Im x|` in a complex spatial
strip … the bosonic and Dirac source amplitudes in this strip are bounded by `CK²` and `CK`").
We prove the real-variable form of that statement: a real-analytic coefficient map composed with
a curve whose derivatives grow geometrically (as the Bernstein bounds give for a band-limited
field) has derivatives of **analytic (Gevrey-1) growth** `n! C Rⁿ`, with `C`, `R` uniform on a
compact set of values.  This is exactly the input of the Fourier-decay step of
`lem:log-source-upgrade` (`GevreyFourierDecay`).

## Main results

* `norm_cmm_one_dim`: a continuous multilinear map on `ℝⁿ` (one-dimensional factors) has norm
  `‖f(1,…,1)‖`.
* `norm_changeOrigin_le_of_geom`: coefficients of a change of origin by `‖x‖ ≤ δ/4` of a series
  with `‖pₙ‖ ≤ C δ⁻ⁿ` satisfy `‖(p.changeOrigin x)ₖ‖ ≤ 2C (2/δ)ᵏ`.
* **`exists_uniform_series`**: a map analytic at every point of a compact set `S` has power
  series at every point of `S` with a **common** radius `r` and common geometric coefficient
  bound `‖qₖ‖ ≤ C r⁻ᵏ`.
* `norm_comp_coeff_le`: `‖(q ∘ P)ₙ‖ ≤ C (2 c max(1, B/r))ⁿ` when `‖qₖ‖ ≤ C r⁻ᵏ` and
  `‖Pₘ‖ ≤ B cᵐ` (`m ≥ 1`) — the sum over the `2ⁿ⁻¹` compositions of `n`.
* **`norm_iteratedDeriv_comp_le`**: for `γ : ℝ → E` analytic at `s₀` with
  `‖γ⁽ᵐ⁾(s₀)‖ ≤ B cᵐ` (`m ≥ 1`), `‖(Φ ∘ γ)⁽ⁿ⁾(s₀)‖ ≤ n! C (2 c max(1, B/r))ⁿ`.
* **`exists_gevrey_comp`**: the uniform statement on a compact set of values.
* `iteratedDeriv_line`: `dⁿ/dsⁿ f(x + s v) = Dⁿf(x + s v)(v, …, v)` for smooth `f`.
-/

open scoped ENNReal NNReal Nat ContDiff
open Set Filter Topology

namespace RenewalGeometry.AnalyticGevrey

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### One-dimensional multilinear maps -/

/-- A continuous multilinear map with one-dimensional factors has norm `‖f(1, …, 1)‖`. -/
theorem norm_cmm_one_dim {n : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) F) :
    ‖f‖ = ‖f (fun _ => 1)‖ := by
  conv_lhs => rw [← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self f]
  exact ContinuousMultilinearMap.norm_mkPiRing _

/-! ### Change of origin with geometric coefficients -/

theorem card_fiber_le (k l : ℕ) :
    Fintype.card {s : Finset (Fin (k + l)) // s.card = l} ≤ 2 ^ (k + l) := by
  calc Fintype.card {s : Finset (Fin (k + l)) // s.card = l}
      ≤ Fintype.card (Finset (Fin (k + l))) := Fintype.card_subtype_le _
    _ = 2 ^ (k + l) := by simp

/-- **Coefficients of a change of origin**: if `‖pₙ‖ ≤ C δ⁻ⁿ` and `‖x‖ ≤ δ/4` then
`‖(p.changeOrigin x)ₖ‖ ≤ 2C (2/δ)ᵏ`. -/
theorem norm_changeOrigin_le_of_geom (p : FormalMultilinearSeries ℝ E F) {C δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ n, ‖p n‖ ≤ C * δ⁻¹ ^ n) {x : E} (hx : ‖x‖ ≤ δ / 4) (k : ℕ) :
    ‖p.changeOrigin x k‖ ≤ 2 * C * (2 / δ) ^ k := by
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hp 0)
    simpa using this
  -- the radius is at least `δ`
  have hrad : ((δ.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    refine p.le_radius_of_bound C fun n => ?_
    have h := hp n
    rw [Real.coe_toNNReal _ hδ.le]
    calc ‖p n‖ * (δ : ℝ) ^ n ≤ C * δ⁻¹ ^ n * δ ^ n := by gcongr
      _ = C := by rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hδ.ne', one_pow, mul_one]
  have hxr : (‖x‖₊ : ℝ≥0∞) < p.radius := by
    refine lt_of_lt_of_le ?_ hrad
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
    simp only [coe_nnnorm, Real.coe_toNNReal _ hδ.le]
    linarith
  have h := p.nnnorm_changeOrigin_le k hxr
  -- bound the series by finite sums
  set g : (Σ l : ℕ, {s : Finset (Fin (k + l)) // s.card = l}) → ℝ≥0 :=
    fun s => ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1
  have hg : ∀ s, (g s : ℝ) ≤ C * δ⁻¹ ^ k * (1 / 4 : ℝ) ^ s.1 := by
    intro s
    simp only [g, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm]
    calc ‖p (k + s.1)‖ * ‖x‖ ^ s.1 ≤ C * δ⁻¹ ^ (k + s.1) * (δ / 4) ^ s.1 := by
          gcongr
          exact hp _
      _ = C * δ⁻¹ ^ k * (1 / 4 : ℝ) ^ s.1 := by
          rw [pow_add, div_eq_mul_inv δ 4, mul_pow]
          have : δ⁻¹ ^ s.1 * δ ^ s.1 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hδ.ne', one_pow]
          calc C * (δ⁻¹ ^ k * δ⁻¹ ^ s.1) * (δ ^ s.1 * 4⁻¹ ^ s.1)
              = C * δ⁻¹ ^ k * (δ⁻¹ ^ s.1 * δ ^ s.1) * 4⁻¹ ^ s.1 := by ring
            _ = C * δ⁻¹ ^ k * (1 / 4 : ℝ) ^ s.1 := by rw [this]; norm_num
  have hsum : ∀ t : Finset (Σ l : ℕ, {s : Finset (Fin (k + l)) // s.card = l}),
      ∑ i ∈ t, g i ≤ (2 * C * (2 / δ) ^ k).toNNReal := by
    intro t
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, Real.coe_toNNReal _ (by positivity)]
    set I : Finset ℕ := t.image Sigma.fst
    have hsub : t ⊆ I.sigma fun _ => Finset.univ := by
      intro i hi
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_image_of_mem _ hi, Finset.mem_univ _⟩
    have h1 : ∑ i ∈ t, (g i : ℝ) ≤ ∑ i ∈ I.sigma (fun _ => Finset.univ), (g i : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => NNReal.coe_nonneg _
    refine h1.trans ?_
    rw [Finset.sum_sigma]
    have h2 : ∀ l ∈ I, ∑ s ∈ (Finset.univ : Finset {s : Finset (Fin (k + l)) // s.card = l}),
        (g ⟨l, s⟩ : ℝ) ≤ C * (2 / δ) ^ k * (1 / 2 : ℝ) ^ l := by
      intro l _
      calc ∑ s ∈ (Finset.univ : Finset {s : Finset (Fin (k + l)) // s.card = l}), (g ⟨l, s⟩ : ℝ)
          ≤ ∑ _s ∈ (Finset.univ : Finset {s : Finset (Fin (k + l)) // s.card = l}),
              C * δ⁻¹ ^ k * (1 / 4 : ℝ) ^ l := Finset.sum_le_sum fun s _ => hg ⟨l, s⟩
        _ = (Fintype.card {s : Finset (Fin (k + l)) // s.card = l} : ℝ) *
              (C * δ⁻¹ ^ k * (1 / 4 : ℝ) ^ l) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ (k + l) * (C * δ⁻¹ ^ k * (1 / 4 : ℝ) ^ l) := by
            gcongr
            exact_mod_cast card_fiber_le k l
        _ = C * (2 / δ) ^ k * (1 / 2 : ℝ) ^ l := by
            rw [div_eq_mul_inv 2 δ, mul_pow, pow_add]
            have : (2 : ℝ) ^ l * (1 / 4) ^ l = (1 / 2) ^ l := by
              rw [← mul_pow]; norm_num
            calc 2 ^ k * 2 ^ l * (C * δ⁻¹ ^ k * (1 / 4 : ℝ) ^ l)
                = C * (2 ^ k * δ⁻¹ ^ k) * (2 ^ l * (1 / 4) ^ l) := by ring
              _ = C * (2 ^ k * δ⁻¹ ^ k) * (1 / 2 : ℝ) ^ l := by rw [this]
    refine (Finset.sum_le_sum h2).trans ?_
    rw [← Finset.mul_sum]
    have hgeom : ∑ l ∈ I, (1 / 2 : ℝ) ^ l ≤ 2 := by
      have hs : Summable fun l : ℕ => (1 / 2 : ℝ) ^ l :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      calc ∑ l ∈ I, (1 / 2 : ℝ) ^ l ≤ ∑' l : ℕ, (1 / 2 : ℝ) ^ l :=
            hs.sum_le_tsum I fun _ _ => by positivity
        _ = 2 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
    have : 0 ≤ C * (2 / δ) ^ k := by positivity
    nlinarith
  have h4 : ‖p.changeOrigin x k‖₊ ≤ (2 * C * (2 / δ) ^ k).toNNReal :=
    h.trans (tsum_le_of_sum_le' (by positivity) hsum)
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity), coe_nnnorm] at h4
  exact h4

/-! ### Uniform power series on a compact set -/

/-- **Uniform power series on a compact set**: a map analytic at every point of a compact set `S`
has, at every point of `S`, a power series with a common radius `r` and coefficients bounded by
`C r⁻ᵏ`. -/
theorem exists_uniform_series [CompleteSpace F] {Φ : E → F} {S : Set E} (hS : IsCompact S)
    (hΦ : ∀ y ∈ S, AnalyticAt ℝ Φ y) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ y ∈ S, ∃ q : FormalMultilinearSeries ℝ E F,
      HasFPowerSeriesOnBall Φ q y (ENNReal.ofReal r) ∧ ∀ k, ‖q k‖ ≤ C * r⁻¹ ^ k := by
  -- local data at each point of `S`
  have hloc : ∀ y ∈ S, ∃ p : FormalMultilinearSeries ℝ E F, ∃ R : ℝ≥0∞, ∃ δ : ℝ, ∃ Cy : ℝ,
      HasFPowerSeriesOnBall Φ p y R ∧ 0 < δ ∧ ENNReal.ofReal δ < R ∧ 0 ≤ Cy ∧
        ∀ n, ‖p n‖ ≤ Cy * δ⁻¹ ^ n := by
    intro y hy
    obtain ⟨p, R, hpR⟩ := hΦ y hy
    obtain ⟨δ, hδ0, hδR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpR.r_pos
    have hδrad : (δ : ℝ≥0∞) < p.radius := lt_of_lt_of_le hδR hpR.r_le
    obtain ⟨Cy, hCy, hb⟩ := p.norm_mul_pow_le_of_lt_radius hδrad
    have hδpos : (0 : ℝ) < δ := by exact_mod_cast hδ0
    refine ⟨p, R, δ, Cy, hpR, hδpos, ?_, hCy.le, fun n => ?_⟩
    · rwa [ENNReal.ofReal_coe_nnreal]
    · have h := hb n
      have hδn : (0 : ℝ) < (δ : ℝ) ^ n := pow_pos hδpos n
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hδn]
      exact h
  choose p R δ Cy hpR hδ hδR hCy hpb using hloc
  -- finite subcover by the balls `B(y, δ_y/4)`
  obtain ⟨t, ht⟩ := hS.elim_nhds_subcover' (fun y hy => Metric.ball y (δ y hy / 4))
    (fun y hy => Metric.ball_mem_nhds y (by have := hδ y hy; positivity))
  by_cases htne : t.Nonempty
  swap
  · refine ⟨0, 1, le_rfl, one_pos, fun y hy => ?_⟩
    have := ht hy
    rw [Finset.not_nonempty_iff_eq_empty.mp htne] at this
    simp at this
  set r : ℝ := t.inf' htne fun i => δ i.1 i.2 / 2 with hr
  have hrpos : 0 < r := by
    rw [hr, Finset.lt_inf'_iff]
    intro i _
    have := hδ i.1 i.2
    positivity
  have hrle : ∀ i ∈ t, r ≤ δ i.1 i.2 / 2 := fun i hi => Finset.inf'_le _ hi
  set C : ℝ := ∑ i ∈ t, 2 * Cy i.1 i.2 with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => by have := hCy i.1 i.2; positivity
  refine ⟨C, r, hC0, hrpos, fun y hy => ?_⟩
  obtain ⟨i, hit, hyi⟩ : ∃ i ∈ t, y ∈ Metric.ball i.1 (δ i.1 i.2 / 4) := by
    have := ht hy
    simp only [mem_iUnion] at this
    obtain ⟨i, hi, hyi⟩ := this
    exact ⟨i, hi, hyi⟩
  set c := i.1
  set hc := i.2
  have hδi := hδ c hc
  set x : E := y - c
  have hx : ‖x‖ < δ c hc / 4 := by rw [← dist_eq_norm]; exact hyi
  have hxR : (‖x‖₊ : ℝ≥0∞) < R c hc := by
    refine lt_of_le_of_lt ?_ (hδR c hc)
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hch := (hpR c hc).changeOrigin hxR
  rw [show c + x = y by simp [x]] at hch
  refine ⟨(p c hc).changeOrigin x, hch.mono (by simpa using hrpos) ?_, fun k => ?_⟩
  · -- `r ≤ R - ‖x‖`
    have h1 : ENNReal.ofReal r + ‖x‖₊ ≤ R c hc := by
      refine le_trans ?_ (hδR c hc).le
      rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ← ENNReal.ofReal_add hrpos.le (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hrle i hit
      linarith
    exact ENNReal.le_sub_of_add_le_right ENNReal.coe_ne_top h1
  · have hb := norm_changeOrigin_le_of_geom (p c hc) hδi (hpb c hc) hx.le k
    refine hb.trans ?_
    have h2 : 2 / δ c hc ≤ r⁻¹ := by
      rw [div_le_iff₀ hδi, inv_mul_eq_div, le_div_iff₀ hrpos]
      have := hrle i hit
      linarith
    have hCi : 2 * Cy c hc ≤ C :=
      Finset.single_le_sum (f := fun i : S => 2 * Cy i.1 i.2)
        (fun i _ => by have := hCy i.1 i.2; positivity) hit
    have h2' : 0 ≤ 2 / δ c hc := by positivity
    calc 2 * Cy c hc * (2 / δ c hc) ^ k ≤ C * r⁻¹ ^ k := by
          gcongr

/-! ### Coefficients of a composition -/

/-- **Coefficients of a composition of series**: if `‖qₖ‖ ≤ C r⁻ᵏ` and `‖Pₘ‖ ≤ B cᵐ` for `m ≥ 1`,
then `‖(q.comp P)ₙ‖ ≤ C (2 c max(1, B/r))ⁿ` (sum over the `2ⁿ⁻¹` compositions of `n`). -/
theorem norm_comp_coeff_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {q : FormalMultilinearSeries ℝ F G} {P : FormalMultilinearSeries ℝ E F}
    {C r B c : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hq : ∀ k, ‖q k‖ ≤ C * r⁻¹ ^ k) (hP : ∀ m, 1 ≤ m → ‖P m‖ ≤ B * c ^ m) (n : ℕ) :
    ‖q.comp P n‖ ≤ C * (2 * c * max 1 (B / r)) ^ n := by
  set M : ℝ := max 1 (B / r)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hBr : B / r ≤ M := le_max_right _ _
  have hterm : ∀ cmp : Composition n, ‖q.compAlongComposition P cmp‖ ≤ C * M ^ n * c ^ n := by
    intro cmp
    refine (q.compAlongComposition_norm P cmp).trans ?_
    have hprod : ∏ i, ‖P (cmp.blocksFun i)‖ ≤ ∏ i, (B * c ^ cmp.blocksFun i) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hP _ (cmp.one_le_blocksFun i)
    have hprod' : ∏ i, (B * c ^ cmp.blocksFun i) = B ^ cmp.length * c ^ n := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Finset.prod_pow_eq_pow_sum, cmp.sum_blocksFun]
    calc ‖q cmp.length‖ * ∏ i, ‖P (cmp.blocksFun i)‖
        ≤ C * r⁻¹ ^ cmp.length * (B ^ cmp.length * c ^ n) := by
          rw [← hprod']
          exact mul_le_mul (hq _) hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
            (by positivity)
      _ = C * (B / r) ^ cmp.length * c ^ n := by
          rw [div_eq_mul_inv, mul_pow]; ring
      _ ≤ C * M ^ cmp.length * c ^ n := by gcongr
      _ ≤ C * M ^ n * c ^ n := by
          have := pow_le_pow_right₀ hM1 cmp.length_le
          gcongr
  unfold FormalMultilinearSeries.comp
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun cmp _ => hterm cmp).trans ?_
  rw [Finset.sum_const, Finset.card_univ, composition_card, nsmul_eq_mul]
  have h2 : ((2 ^ (n - 1) : ℕ) : ℝ) ≤ 2 ^ n := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
  calc ((2 ^ (n - 1) : ℕ) : ℝ) * (C * M ^ n * c ^ n) ≤ 2 ^ n * (C * M ^ n * c ^ n) := by
        gcongr
    _ = C * (2 * c * M) ^ n := by rw [mul_pow, mul_pow]; ring

/-! ### Gevrey bound for a composition along a curve -/

/-- **Analytic growth of the derivatives of `Φ ∘ γ`**: if `Φ` has a power series at `γ(s₀)` with
radius `r` and `‖qₖ‖ ≤ C r⁻ᵏ`, and `γ : ℝ → E` is analytic at `s₀` with
`‖γ⁽ᵐ⁾(s₀)‖ ≤ B cᵐ` for `m ≥ 1`, then `‖(Φ ∘ γ)⁽ⁿ⁾(s₀)‖ ≤ n! C (2 c max(1, B/r))ⁿ`. -/
theorem norm_iteratedDeriv_comp_le [CompleteSpace E] [CompleteSpace F] {Φ : E → F}
    {q : FormalMultilinearSeries ℝ E F} {y : E} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (hq : HasFPowerSeriesOnBall Φ q y (ENNReal.ofReal r)) (hqC : ∀ k, ‖q k‖ ≤ C * r⁻¹ ^ k)
    {γ : ℝ → E} {s₀ : ℝ} (hγ : AnalyticAt ℝ γ s₀) (hγy : γ s₀ = y) {B c : ℝ} (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hγB : ∀ m, 1 ≤ m → ‖iteratedDeriv m γ s₀‖ ≤ B * c ^ m) (n : ℕ) :
    ‖iteratedDeriv n (Φ ∘ γ) s₀‖ ≤ n ! * (C * (2 * c * max 1 (B / r)) ^ n) := by
  obtain ⟨P, R, hPR⟩ := hγ
  -- the coefficients of `γ`
  have hP : ∀ m, 1 ≤ m → ‖P m‖ ≤ B * c ^ m := by
    intro m hm
    have h1 := hPR.factorial_smul 1 m
    rw [norm_cmm_one_dim]
    have h2 : ‖iteratedDeriv m γ s₀‖ = (m ! : ℝ) * ‖P m (fun _ => 1)‖ := by
      rw [iteratedDeriv_eq_iteratedFDeriv, ← h1, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
        Real.norm_natCast]
    have hfac : (1 : ℝ) ≤ m ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
    have h3 := hγB m hm
    rw [h2] at h3
    have h4 : 0 ≤ ‖P m (fun _ => 1)‖ := norm_nonneg _
    nlinarith
  have hq' : HasFPowerSeriesAt Φ q (γ s₀) := by rw [hγy]; exact hq.hasFPowerSeriesAt
  obtain ⟨R', hcomp⟩ := hq'.comp ⟨R, hPR⟩
  have h1 := hcomp.factorial_smul 1 n
  rw [iteratedDeriv_eq_iteratedFDeriv, ← h1, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
    Real.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (((q.comp P) n).le_opNorm _).trans ?_
  simp only [norm_one, Finset.prod_const_one, mul_one]
  exact norm_comp_coeff_le hC hr hB hc hqC hP n

/-- **Uniform Gevrey bound on a compact set of values**: if `Φ` is analytic at every point of a
compact `S`, there are `C ≥ 0`, `r > 0` such that for every curve `γ` analytic at `s₀` with
`γ(s₀) ∈ S` and `‖γ⁽ᵐ⁾(s₀)‖ ≤ B cᵐ` (`m ≥ 1`), `‖(Φ ∘ γ)⁽ⁿ⁾(s₀)‖ ≤ n! C (2 c max(1, B/r))ⁿ`. -/
theorem exists_gevrey_comp [CompleteSpace E] [CompleteSpace F] {Φ : E → F} {S : Set E}
    (hS : IsCompact S) (hΦ : ∀ y ∈ S, AnalyticAt ℝ Φ y) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ (γ : ℝ → E) (s₀ : ℝ), AnalyticAt ℝ γ s₀ → γ s₀ ∈ S →
      ∀ B c : ℝ, 0 ≤ B → 0 ≤ c → (∀ m, 1 ≤ m → ‖iteratedDeriv m γ s₀‖ ≤ B * c ^ m) →
        ∀ n, ‖iteratedDeriv n (Φ ∘ γ) s₀‖ ≤ n ! * (C * (2 * c * max 1 (B / r)) ^ n) := by
  obtain ⟨C, r, hC, hr, hser⟩ := exists_uniform_series hS hΦ
  refine ⟨C, r, hC, hr, fun γ s₀ hγ hγS B c hB hc hγB n => ?_⟩
  obtain ⟨q, hq, hqC⟩ := hser (γ s₀) hγS
  exact norm_iteratedDeriv_comp_le hC hr hq hqC hγ rfl hB hc hγB n

/-! ### Derivatives along lines -/

/-- `dⁿ/dsⁿ f(x + s v) = Dⁿ f(x + s v)(v, …, v)` for a smooth `f`. -/
theorem iteratedDeriv_line {f : E → F} (hf : ContDiff ℝ ∞ f) (x v : E) (n : ℕ) (s : ℝ) :
    iteratedDeriv n (fun t : ℝ => f (x + t • v)) s = iteratedFDeriv ℝ n f (x + s • v) (fun _ => v) := by
  set L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ v
  have hfun : (fun t : ℝ => f (x + t • v)) = (fun z => f (x + z)) ∘ L := by
    funext t; simp [L, ContinuousLinearMap.toSpanSingleton_apply]
  have hg : ContDiff ℝ ∞ (fun z => f (x + z)) := hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv, hfun,
    L.iteratedFDeriv_comp_right hg s (by exact_mod_cast le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp [L, ContinuousLinearMap.toSpanSingleton_apply]

/-- A line through an analytic point is analytic. -/
theorem analyticAt_line {f : E → F} {x v : E} {s : ℝ} (hf : AnalyticAt ℝ f (x + s • v)) :
    AnalyticAt ℝ (fun t : ℝ => f (x + t • v)) s := by
  have hl : AnalyticAt ℝ (fun t : ℝ => x + t • v) s := by
    have : AnalyticAt ℝ (fun t : ℝ => t • v) s :=
      (ContinuousLinearMap.toSpanSingleton ℝ v).analyticAt s |>.congr
        (Filter.Eventually.of_forall fun t => by simp [ContinuousLinearMap.toSpanSingleton_apply])
    exact analyticAt_const.add this
  exact AnalyticAt.comp (g := f) (f := fun t : ℝ => x + t • v) hf hl

end

end RenewalGeometry.AnalyticGevrey
