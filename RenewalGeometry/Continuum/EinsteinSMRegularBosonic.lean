/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMLocalClosure
import RenewalGeometry.Continuum.EinsteinSMDiracStability
import RenewalGeometry.Analysis.TorusC1Rellich
import RenewalGeometry.Analysis.TorusBoxRestriction

/-!
# The regular Sobolev branch: `C¹` compactness of the bosonic fields and automatic screens
  (towards `thm:regular-branch`, Einstein–Standard-Model action-closure manuscript)

Generic tools for `thm:regular-branch` ("No compact-screen hypothesis and no a-priori spinor
first-jet compactness is required on this regular branch"):

* **`commonCompactScreen_of_cauchy`** — a Cauchy sequence in a complex Hilbert space has a common
  compact screen (`S_R` = orthogonal projection onto the span of `Y₀, …, Y_R`, a finite-rank hence
  compact operator); `hasCommonCompactScreen_of_cauchy` — packets Cauchy in `L²(Q)` have a common
  compact screen in `L²(Q)`.  So on the regular branch the screens of `def:compactness-certificate`
  are consequences, not hypotheses.
* `UCauchyOn`, `eLpNorm_sub_le_of_unif`, `lpCauchy_of_UCauchyOn` — uniform Cauchy sequences on a
  chart box are Cauchy in every `L^p(Q)`.
* `TorusRep` — the restriction-space rendering of an `H^s(Q)` bound (as in
  `TorusBoxRestriction.lean` / `BoxBosonicCompactness.lean`): on the box the field agrees with
  `U ∘ chart` for a continuous `U` on the torus of period `L` bounded in `H^s(𝕋⁴)`.
* `hasDerivAt_chart`, `pd_eq_of_torusRep` — chart transfer: `∂ᵢ(U ∘ chart) = L⁻¹ (∂ᵢU) ∘ chart`.
* **`exists_subseq_C1_cauchy`** — a sequence of fields smooth on the box with `TorusRep` bounds of
  order `s > 3` (`= d/2 + 1`, `d = 4`) has a subsequence along which the fields and all their
  first partial derivatives are uniformly Cauchy on the box (`rellich_C1`, the compact embedding
  `H^{3+σ}(𝕋⁴) ⊂ C¹`).
* `exists_subseq_forall` — common extraction for finitely many subsequence properties.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ContDiff ENNReal NNReal BigOperators

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace RegularBranch

open SobolevOpen (pd box IsTest MemW12)
open SobolevOpen.TorusChart TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-! ### Screens from Cauchy sequences -/

section Screen

variable {𝒴 : Type} [NormedAddCommGroup 𝒴] [InnerProductSpace ℂ 𝒴] [CompleteSpace 𝒴]

/-- The span of the first `R + 1` terms. -/
def spanUpTo (Y : ℕ → 𝒴) (R : ℕ) : Submodule ℂ 𝒴 :=
  Submodule.span ℂ (Set.range fun i : Fin (R + 1) => Y i)

instance (Y : ℕ → 𝒴) (R : ℕ) : FiniteDimensional ℂ (spanUpTo Y R) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

instance (Y : ℕ → 𝒴) (R : ℕ) : (spanUpTo Y R).HasOrthogonalProjection := inferInstance

theorem mem_spanUpTo (Y : ℕ → 𝒴) {i R : ℕ} (h : i ≤ R) : Y i ∈ spanUpTo Y R :=
  Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩

theorem norm_sub_starProjection_le (V : Submodule ℂ 𝒴) [V.HasOrthogonalProjection] (y : 𝒴)
    {v : 𝒴} (hv : v ∈ V) : ‖y - V.starProjection y‖ ≤ ‖y - v‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ (⟨v, hv⟩ : V)

theorem isCompactOperator_starProjection (V : Submodule ℂ 𝒴) [FiniteDimensional ℂ V]
    [V.HasOrthogonalProjection] : IsCompactOperator V.starProjection := by
  have : ProperSpace V := FiniteDimensional.proper_rclike ℂ V
  exact (isCompactOperator_of_locallyCompactSpace_dom V.orthogonalProjectionOnto).clm_comp
    V.subtypeL

/-- **A Cauchy sequence in a Hilbert space has a common compact screen** (the hypotheses of
`lem:screen`): `S_{h,R} = S_R` the orthogonal projection onto `span{Y₀, …, Y_R}`. -/
theorem commonCompactScreen_of_cauchy {Y : ℕ → 𝒴} (hY : CauchySeq Y) : CommonCompactScreen Y := by
  obtain ⟨Yinf, hYinf⟩ := cauchySeq_tendsto_of_complete hY
  set S : ℕ → 𝒴 →L[ℂ] 𝒴 := fun R => (spanUpTo Y R).starProjection
  refine ⟨fun _ R => S R, S, fun R => isCompactOperator_starProjection _, fun R => by simp,
    fun ε hε => ?_, fun φ hφ Ylim hw => ?_⟩
  · obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hY ε hε
    refine ⟨N, fun R hR h => ?_⟩
    by_cases hh : h ≤ R
    · have := (Submodule.starProjection_eq_self_iff (K := spanUpTo Y R)).mpr (mem_spanUpTo Y hh)
      simp only [S, this, sub_self, norm_zero, hε.le]
    · refine (norm_sub_starProjection_le _ (Y h) (mem_spanUpTo Y hR)).trans ?_
      have := hN h (by omega)
      rw [dist_eq_norm] at this
      exact this.le
  · -- the weak limit is the strong limit
    have hstrong : Tendsto (Y ∘ φ) atTop (𝓝 Yinf) := hYinf.comp hφ.tendsto_atTop
    have hYl : Ylim = Yinf := by
      refine ext_inner_left ℂ fun v => ?_
      exact tendsto_nhds_unique (hw v) ((tendsto_const_nhds.inner hstrong :
        Tendsto (fun n => inner ℂ v ((Y ∘ φ) n)) atTop (𝓝 (inner ℂ v Yinf))))
    subst hYl
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun R => ‖Ylim - Y R‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.mp hYinf)
      simpa [norm_sub_rev] using this
    refine squeeze_zero (fun R => norm_nonneg _) (fun R => ?_) h0
    rw [norm_sub_rev]
    exact norm_sub_starProjection_le _ Ylim (mem_spanUpTo Y le_rfl)

end Screen

variable {T : ℝ} {ι' : Type} [Fintype ι']

/-- **Packets Cauchy in `L²(Q)` have a common compact screen in `L²(Q)`.** -/
theorem hasCommonCompactScreen_of_cauchy (Q : ChartBox T) {P : ℕ → E4 → ι' → ℂ}
    (hmem : ∀ n, MemLp (P n) 2 Q.μ)
    (hc : ∀ ε > (0 : ℝ), ∃ N, ∀ m ≥ N, ∀ n ≥ N, eLpNorm (P m - P n) 2 Q.μ ≤ ENNReal.ofReal ε) :
    HasCommonCompactScreen Q P := by
  set c : ℝ≥0 := ((Fintype.card ι' : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal : ℝ≥0)
  have hE : ∀ n, MemLp (fun x => WithLp.toLp 2 (P n x)) 2 Q.μ := fun n =>
    ((PiLp.lipschitzWith_toLp 2 (fun _ : ι' => ℂ)).continuous.comp_aestronglyMeasurable
      (hmem n).1 |> fun h => (hmem n).of_le_mul h (Eventually.of_forall fun x =>
        norm_toLp_le_card (P n x)))
  set Y : ℕ → L2Hilbert Q ι' := fun n => (hE n).toLp _
  refine ⟨Y, fun n => (hE n).coeFn_toLp, commonCompactScreen_of_cauchy ?_⟩
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε / (c + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
  have hle : eLpNorm ((fun x => WithLp.toLp 2 (P n x)) - fun x => WithLp.toLp 2 (P N x)) 2 Q.μ ≤
      c * eLpNorm (P n - P N) 2 Q.μ := by
    refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2
    simp only [Pi.sub_apply]
    rw [← WithLp.toLp_sub]
    exact norm_toLp_le_card _
  have h2 := hN n hn N le_rfl
  have h3 : eLpNorm ((fun x => WithLp.toLp 2 (P n x)) - fun x => WithLp.toLp 2 (P N x)) 2 Q.μ ≤
      ENNReal.ofReal (c * (ε / (c + 1))) := by
    refine hle.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
    gcongr
  have h4 : c * (ε / (c + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [c.coe_nonneg]
  calc (eLpNorm ((fun x => WithLp.toLp 2 (P n x)) - fun x => WithLp.toLp 2 (P N x)) 2 Q.μ).toReal
      ≤ c * (ε / (c + 1)) := ENNReal.toReal_le_of_le_ofReal (by positivity) h3
    _ < ε := h4

/-! ### Uniform Cauchy sequences on a set -/

/-- Uniformly Cauchy on `S`. -/
def UCauchyOn {F : Type*} [NormedAddCommGroup F] (S : Set E4) (u : ℕ → E4 → F) : Prop :=
  ∀ ε > (0 : ℝ), ∃ N, ∀ m n, N ≤ m → N ≤ n → ∀ x ∈ S, ‖u m x - u n x‖ ≤ ε

namespace UCauchyOn

variable {F : Type*} [NormedAddCommGroup F] {S : Set E4} {u v : ℕ → E4 → F}

theorem comp (h : UCauchyOn S u) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    UCauchyOn S (fun k => u (φ k)) := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun m n hm hn x hx => hN _ _ (hm.trans (hφ.id_le m)) (hn.trans (hφ.id_le n)) x hx⟩

theorem of_tail {k : ℕ} (h : UCauchyOn S (fun j => u (j + k))) : UCauchyOn S u := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N + k, fun m n hm hn x hx => ?_⟩
  have := hN (m - k) (n - k) (by omega) (by omega) x hx
  simp only [Nat.sub_add_cancel (show k ≤ m by omega), Nat.sub_add_cancel (show k ≤ n by omega)]
    at this
  exact this

theorem mono {S' : Set E4} (h : UCauchyOn S u) (hS : S' ⊆ S) : UCauchyOn S' u := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun m n hm hn x hx => hN m n hm hn x (hS hx)⟩

theorem add (hu : UCauchyOn S u) (hv : UCauchyOn S v) : UCauchyOn S (fun n x => u n x + v n x) :=
  fun ε hε => by
  obtain ⟨N, hN⟩ := hu (ε / 2) (by positivity)
  obtain ⟨N', hN'⟩ := hv (ε / 2) (by positivity)
  refine ⟨max N N', fun m n hm hn x hx => ?_⟩
  have h1 := hN m n (le_of_max_le_left hm) (le_of_max_le_left hn) x hx
  have h2 := hN' m n (le_of_max_le_right hm) (le_of_max_le_right hn) x hx
  calc ‖u m x + v m x - (u n x + v n x)‖ = ‖(u m x - u n x) + (v m x - v n x)‖ := by abel_nf
    _ ≤ ‖u m x - u n x‖ + ‖v m x - v n x‖ := norm_add_le _ _
    _ ≤ ε := by linarith

theorem sub (hu : UCauchyOn S u) (hv : UCauchyOn S v) : UCauchyOn S (fun n x => u n x - v n x) :=
  fun ε hε => by
  obtain ⟨N, hN⟩ := hu (ε / 2) (by positivity)
  obtain ⟨N', hN'⟩ := hv (ε / 2) (by positivity)
  refine ⟨max N N', fun m n hm hn x hx => ?_⟩
  have h1 := hN m n (le_of_max_le_left hm) (le_of_max_le_left hn) x hx
  have h2 := hN' m n (le_of_max_le_right hm) (le_of_max_le_right hn) x hx
  calc ‖u m x - v m x - (u n x - v n x)‖ = ‖(u m x - u n x) - (v m x - v n x)‖ := by abel_nf
    _ ≤ ‖u m x - u n x‖ + ‖v m x - v n x‖ := norm_sub_le _ _
    _ ≤ ε := by linarith

/-- Images under a uniformly continuous map on a set containing all values. -/
theorem comp_uniformContinuousOn {G : Type*} [NormedAddCommGroup G] {K : Set F} {Φ : F → G}
    (hΦ : UniformContinuousOn Φ K) (hK : ∀ n, ∀ x ∈ S, u n x ∈ K) (h : UCauchyOn S u) :
    UCauchyOn S (fun n x => Φ (u n x)) := fun ε hε => by
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp hΦ ε hε
  obtain ⟨N, hN⟩ := h (δ / 2) (by positivity)
  refine ⟨N, fun m n hm hn x hx => ?_⟩
  have := hδf _ (hK m x hx) _ (hK n x hx)
    (by rw [dist_eq_norm]; exact (hN m n hm hn x hx).trans_lt (by linarith))
  rw [dist_eq_norm] at this
  exact this.le

/-- Pi-valued sequences are uniformly Cauchy iff their components are. -/
theorem pi {κ : Type*} [Fintype κ] {G : κ → Type*} [∀ k, NormedAddCommGroup (G k)]
    {w : ℕ → E4 → ∀ k, G k} (h : ∀ k, UCauchyOn S (fun n x => w n x k)) : UCauchyOn S w :=
  fun ε hε => by
  choose N hN using fun k => h k ε hε
  refine ⟨∑ k, N k, fun m n hm hn x hx => (pi_norm_le_iff_of_nonneg hε.le).2 fun k => ?_⟩
  have hle := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  exact hN k m n (by omega) (by omega) x hx

theorem component {κ : Type*} [Fintype κ] {G : κ → Type*} [∀ k, NormedAddCommGroup (G k)]
    {w : ℕ → E4 → ∀ k, G k} (h : UCauchyOn S w) (k : κ) : UCauchyOn S (fun n x => w n x k) :=
  fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun m n hm hn x hx => (norm_le_pi_norm (w m x - w n x) k).trans (hN m n hm hn x hx)⟩

/-- A uniformly Cauchy sequence of functions bounded on `S` is uniformly bounded on `S`. -/
theorem bounded (h : UCauchyOn S u) (hb : ∀ n, ∃ C, ∀ x ∈ S, ‖u n x‖ ≤ C) :
    ∃ C, ∀ n, ∀ x ∈ S, ‖u n x‖ ≤ C := by
  obtain ⟨N, hN⟩ := h 1 one_pos
  choose C hC using hb
  refine ⟨(∑ i ∈ Finset.range (N + 1), |C i|) + 1, fun n x hx => ?_⟩
  have hs : ∀ i ∈ Finset.range (N + 1), 0 ≤ |C i| := fun i _ => abs_nonneg _
  by_cases hn : n ≤ N
  · have := Finset.single_le_sum hs (Finset.mem_range.mpr (by omega : n < N + 1))
    have := hC n x hx
    have := le_abs_self (C n)
    linarith
  · have h1 := hN n N (by omega) le_rfl x hx
    have h2 := hC N x hx
    have h3 := Finset.single_le_sum hs (Finset.mem_range.mpr (by omega : N < N + 1))
    have h4 := le_abs_self (C N)
    calc ‖u n x‖ = ‖(u n x - u N x) + u N x‖ := by abel_nf
      _ ≤ ‖u n x - u N x‖ + ‖u N x‖ := norm_add_le _ _
      _ ≤ _ := by linarith

/-- Products of uniformly Cauchy, uniformly bounded sequences (any continuous bilinear map). -/
theorem bilin {F₁ F₂ G : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂]
    [NormedSpace ℝ F₂] [NormedAddCommGroup G] [NormedSpace ℝ G] (B : F₁ →L[ℝ] F₂ →L[ℝ] G)
    {u : ℕ → E4 → F₁} {v : ℕ → E4 → F₂} (hu : UCauchyOn S u) (hv : UCauchyOn S v)
    {Cu Cv : ℝ} (hCu : ∀ n, ∀ x ∈ S, ‖u n x‖ ≤ Cu) (hCv : ∀ n, ∀ x ∈ S, ‖v n x‖ ≤ Cv) :
    UCauchyOn S (fun n x => B (u n x) (v n x)) := fun ε hε => by
  set K := ‖B‖ * (|Cu| + |Cv| + 1)
  have hK : 0 ≤ K := by positivity
  obtain ⟨N, hN⟩ := hu (ε / (2 * (K + 1))) (by positivity)
  obtain ⟨N', hN'⟩ := hv (ε / (2 * (K + 1))) (by positivity)
  refine ⟨max N N', fun m n hm hn x hx => ?_⟩
  have h1 := hN m n (le_of_max_le_left hm) (le_of_max_le_left hn) x hx
  have h2 := hN' m n (le_of_max_le_right hm) (le_of_max_le_right hn) x hx
  have e : B (u m x) (v m x) - B (u n x) (v n x) =
      B (u m x - u n x) (v m x) + B (u n x) (v m x - v n x) := by
    simp only [map_sub, sub_apply]; abel
  rw [e]
  have b1 : ‖B (u m x - u n x) (v m x)‖ ≤ ‖B‖ * ‖u m x - u n x‖ * |Cv| :=
    (B.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_left ((hCv m x hx).trans (le_abs_self _))
      (by positivity))
  have b2 : ‖B (u n x) (v m x - v n x)‖ ≤ ‖B‖ * |Cu| * ‖v m x - v n x‖ :=
    (B.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      ((hCu n x hx).trans (le_abs_self _)) (norm_nonneg B)) (norm_nonneg _))
  have hB := norm_nonneg B
  have hd : 0 < 2 * (K + 1) := by positivity
  have t1 : ‖B‖ * ‖u m x - u n x‖ * |Cv| ≤ K * (ε / (2 * (K + 1))) := by
    have : ‖B‖ * |Cv| ≤ K := by
      simp only [K]; nlinarith [abs_nonneg Cu, abs_nonneg Cv]
    nlinarith [norm_nonneg (u m x - u n x), abs_nonneg Cv]
  have t2 : ‖B‖ * |Cu| * ‖v m x - v n x‖ ≤ K * (ε / (2 * (K + 1))) := by
    have : ‖B‖ * |Cu| ≤ K := by
      simp only [K]; nlinarith [abs_nonneg Cu, abs_nonneg Cv]
    nlinarith [norm_nonneg (v m x - v n x), abs_nonneg Cu]
  have t3 : K * (ε / (2 * (K + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ hd (by norm_num)]
    nlinarith
  calc _ ≤ ‖B (u m x - u n x) (v m x)‖ + ‖B (u n x) (v m x - v n x)‖ := norm_add_le _ _
    _ ≤ ε := by linarith

end UCauchyOn

/-- The `L^p(Q)` norm of a function bounded by `ε` on `Q`. -/
theorem eLpNorm_le_of_unif {F : Type*} [NormedAddCommGroup F] (Q : ChartBox T) {f : E4 → F}
    {ε : ℝ} (hf : ∀ x ∈ Q.set, ‖f x‖ ≤ ε) (p : ℝ≥0∞) :
    eLpNorm f p Q.μ ≤ Q.μ univ ^ p.toReal⁻¹ * ENNReal.ofReal ε :=
  eLpNorm_le_of_ae_bound ((ae_restrict_iff' Q.isOpen.measurableSet).mpr
    (Eventually.of_forall fun x hx => hf x hx))

/-- **Uniformly Cauchy sequences on the box are Cauchy in `L^p(Q)`.** -/
theorem lpCauchy_of_UCauchyOn {F : Type*} [NormedAddCommGroup F] (Q : ChartBox T)
    {u : ℕ → E4 → F} (h : UCauchyOn Q.set u) (p : ℝ≥0∞) :
    ∀ ε > (0 : ℝ), ∃ N, ∀ m ≥ N, ∀ n ≥ N, eLpNorm (u m - u n) p Q.μ ≤ ENNReal.ofReal ε := by
  intro ε hε
  set c : ℝ≥0∞ := Q.μ univ ^ p.toReal⁻¹
  have hc : c ≠ ⊤ := by
    have : Q.μ univ ≠ ⊤ := measure_ne_top _ _
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) this
  set c' : ℝ := c.toReal
  obtain ⟨N, hN⟩ := h (ε / (c' + 1)) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  refine (eLpNorm_le_of_unif Q (f := u m - u n) (fun x hx => hN m n hm hn x hx) p).trans ?_
  have hc' : c = ENNReal.ofReal c' := (ENNReal.ofReal_toReal hc).symm
  rw [show Q.μ univ ^ p.toReal⁻¹ = ENNReal.ofReal c' from hc', ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [ENNReal.toReal_nonneg (a := c)]

/-! ### Torus representatives and the chart transfer -/

/-- **The restriction-space rendering of an `H^s(Q)` bound**: on the set `Ω` the field `u`
agrees with `U ∘ chart a L` for a continuous `U` on `𝕋⁴` with `‖U‖²_{H^s} ≤ B`. -/
def TorusRep (a : E4) (L s B : ℝ) (Ω : Set E4) (u : E4 → ℂ) : Prop :=
  ∃ U : C(UnitAddTorus (Fin 4), ℂ), MemH s ⇑U ∧ sobSq s ⇑U ≤ B ∧ ∀ x ∈ Ω, u x = U (chart a L x)

theorem chart_add_single (a : E4) {L : ℝ} (hL : L ≠ 0) (x : E4) (i : Fin 4) (s : ℝ) :
    chart a L (x + s • Pi.single i 1) = chart a L x + lineShift i (s / L) := by
  funext j
  simp only [chart, lineShift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = i
  · subst hj
    simp only [Pi.single_eq_same, mul_one]
    rw [← AddCircle.coe_add]
    congr 1
    field_simp
    ring
  · simp only [Pi.single_eq_of_ne hj, mul_zero, add_zero]

/-- **Chart transfer**: `∂ᵢ(U ∘ chart a L) = L⁻¹ (∂ᵢU) ∘ chart a L` along lines. -/
theorem hasDerivAt_chart (a : E4) {L : ℝ} (hL : L ≠ 0) {U U' : UnitAddTorus (Fin 4) → ℂ}
    (i : Fin 4) (hU : IsLineDeriv i U U') (x : E4) :
    HasDerivAt (fun s : ℝ => U (chart a L (x + s • Pi.single i 1)))
      (((L⁻¹ : ℝ) : ℂ) * U' (chart a L x)) 0 := by
  have h1 := hU (chart a L x)
  have h2 : HasDerivAt (fun s : ℝ => s / L) (L⁻¹) 0 := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id (0 : ℝ)).mul_const L⁻¹
  have h3 := h1.scomp_of_eq (0 : ℝ) h2 (by simp)
  have e : (fun s : ℝ => U (chart a L (x + s • Pi.single i 1))) =
      (fun t => U (chart a L x + lineShift i t)) ∘ fun s => s / L := by
    funext s; rw [Function.comp_apply, chart_add_single a hL x i s]
  rw [e]
  exact h3.congr_deriv (Complex.real_smul)

/-- **The classical partial derivatives of a field with a torus representative** on an open set. -/
theorem pd_eq_of_rep (a : E4) {L : ℝ} (hL : L ≠ 0) {Ω : Set E4} (hΩ : IsOpen Ω) {u : E4 → ℂ}
    {U U' : UnitAddTorus (Fin 4) → ℂ} (hrep : ∀ x ∈ Ω, u x = U (chart a L x)) (i : Fin 4)
    (hU : IsLineDeriv i U U') {x : E4} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ u x) :
    pd u i x = ((L⁻¹ : ℝ) : ℂ) * U' (chart a L x) := by
  have h1 := PeriodicCube.hasDerivAt_line (f := u) (x := x) i (s := 0) (by simpa using hd)
  simp only [zero_smul, add_zero] at h1
  have hev : (fun s : ℝ => u (x + s • Pi.single i 1)) =ᶠ[𝓝 0]
      fun s => U (chart a L (x + s • Pi.single i 1)) := by
    have hc : Continuous fun s : ℝ => x + s • (Pi.single i 1 : E4) := by fun_prop
    have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • (Pi.single i 1 : E4) ∈ Ω :=
      hc.continuousAt.preimage_mem_nhds (by simpa using hΩ.mem_nhds hx)
    exact hmem.mono fun s hs => hrep _ hs
  exact h1.unique ((hasDerivAt_chart a hL i hU x).congr_of_eventuallyEq hev)

/-- **`C¹` compactness from `H^s` torus representatives** (`s > 3`): fields differentiable on the
open set `Ω` with `TorusRep` bounds have a subsequence along which the fields and all their first
partial derivatives are uniformly Cauchy on `Ω`. -/
theorem exists_subseq_C1_cauchy (a : E4) {L : ℝ} (hL : 0 < L) {s B : ℝ} (hs : 3 < s)
    {Ω : Set E4} (hΩ : IsOpen Ω) {u : ℕ → E4 → ℂ} (hrep : ∀ n, TorusRep a L s B Ω (u n))
    (hd : ∀ n, ∀ x ∈ Ω, DifferentiableAt ℝ (u n) x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ UCauchyOn Ω (fun k => u (φ k)) ∧
      ∀ i, UCauchyOn Ω (fun k => pd (u (φ k)) i) := by
  choose U hUm hUB hUrep using hrep
  have hcard : ((Fintype.card (Fin 4) : ℕ) : ℝ) / 2 + 1 < s := by simp; linarith
  obtain ⟨φ, G, hφ, -, -, hG, hder⟩ := rellich_C1 hcard U hUm hUB
  refine ⟨φ, hφ, fun ε hε => ?_, fun i => ?_⟩
  · obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hG (ε / 2) (by positivity)
    refine ⟨N, fun m n hm hn x hx => ?_⟩
    show ‖u (φ m) x - u (φ n) x‖ ≤ ε
    rw [hUrep _ x hx, hUrep _ x hx]
    have h1 := hN m hm; have h2 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1 h2
    calc ‖U (φ m) (chart a L x) - U (φ n) (chart a L x)‖ =
        ‖(U (φ m) - G) (chart a L x) - (U (φ n) - G) (chart a L x)‖ := by simp
      _ ≤ ‖(U (φ m) - G) (chart a L x)‖ + ‖(U (φ n) - G) (chart a L x)‖ := norm_sub_le _ _
      _ ≤ ‖U (φ m) - G‖ + ‖U (φ n) - G‖ :=
          add_le_add (ContinuousMap.norm_coe_le_norm _ _) (ContinuousMap.norm_coe_le_norm _ _)
      _ ≤ ε := by linarith
  · obtain ⟨G', F', -, hF', hconv⟩ := hder i
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (L * (ε / 2)) (by positivity)
    refine ⟨N, fun m n hm hn x hx => ?_⟩
    show ‖pd (u (φ m)) i x - pd (u (φ n)) i x‖ ≤ ε
    rw [pd_eq_of_rep a hL.ne' hΩ (hUrep (φ m)) i (hF' m) hx (hd _ x hx),
      pd_eq_of_rep a hL.ne' hΩ (hUrep (φ n)) i (hF' n) hx (hd _ x hx), ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    have h1 := hN m hm; have h2 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1 h2
    have h3 : ‖F' m (chart a L x) - F' n (chart a L x)‖ ≤ L * ε := by
      calc ‖F' m (chart a L x) - F' n (chart a L x)‖ =
          ‖(F' m - G') (chart a L x) - (F' n - G') (chart a L x)‖ := by simp
        _ ≤ ‖(F' m - G') (chart a L x)‖ + ‖(F' n - G') (chart a L x)‖ := norm_sub_le _ _
        _ ≤ ‖F' m - G'‖ + ‖F' n - G'‖ :=
            add_le_add (ContinuousMap.norm_coe_le_norm _ _) (ContinuousMap.norm_coe_le_norm _ _)
        _ ≤ L * ε := by linarith
    calc L⁻¹ * ‖F' m (chart a L x) - F' n (chart a L x)‖ ≤ L⁻¹ * (L * ε) :=
          mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hL.le)
      _ = ε := by field_simp

end RegularBranch
end EinsteinSM
end RenewalGeometry
