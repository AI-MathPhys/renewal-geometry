/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.SMSTPositiveScreenExact

/-!
# Compact positive-screen upgrade (`prop:supp-compact-upgrade`, emergent-spacetime manuscript)

Let `𝒴` be a complex Hilbert space, `Y_X ⇀ Y` weakly, and positive operators `𝔸_X` with
`m I ⪯ 𝔸_X` (Loewner order of `𝒴 →L 𝒴`, `m > 0`).  The square roots are Mathlib's continuous
functional calculus square roots `𝔸_X^{1/2} = CFC.sqrt 𝔸_X`, and `𝔸_X^{-1/2}` is the two-sided
inverse of `𝔸_X^{1/2}`; the limit `𝔸^{-1/2}` is the two-sided inverse of `CFC.sqrt 𝔸` for a
positive `𝔸`, and `𝔸_X^{-1/2} → 𝔸^{-1/2}` strongly.  Put `Z_X = 𝔸_X^{1/2} Y_X` and suppose
`Z_X ⇀ Z`.  If for every `R` there are screens `S_{X,R} → S_R` in operator norm with `S_R`
compact (`IsCompactOperator`) and the two tail conditions hold, then:

* `Y_X → Y` strongly, and `Y = 𝔸^{-1/2} Z` (`compact_positive_screen_upgrade`);
* every bounded quadratic insertion converges: for a bounded real-bilinear `B : 𝒴 × 𝒴 → W`,
  `‖B(Y_X, Y_X) - B(Y, Y)‖ ≤ ‖B‖ ‖Y_X - Y‖ (‖Y_X‖ + ‖Y‖) → 0`
  (`norm_bilinear_diag_sub_le`, `tendsto_bilinear_diag`);
* on the cylinder space (`𝒴` realised in `L²(K; E)` by a bounded map `ι`, e.g. the identity),
  every pointwise bounded quadratic density converges in `L¹(K)`: `‖b(Y_X, Y_X) - b(Y, Y)‖_{L¹} ≤ ‖b‖ ‖Y_X - Y‖₂ (‖Y_X‖₂ + ‖Y‖₂) → 0`
  (`eLpNorm_quadratic_insertion_le`, `compact_positive_screen_upgrade_L2`).

Derived rather than assumed (the gaps of the earlier `SMSTPositiveScreenExact` rendering):

* `sup_X ‖Z_X‖ < ∞` from weak convergence (Banach–Steinhaus, `norm_bounded_of_weakTendsto`);
* compactness of `S_R` is the genuine `IsCompactOperator`; complete continuity (bounded weakly
  convergent sequences are mapped to norm-convergent ones) is proved
  (`tendsto_of_isCompactOperator`: compact closure of the image of a ball, subsequence
  extraction, identification of the limit through the adjoint);
* `‖𝔸_X^{-1/2}‖ ≤ m^{-1/2}` from `m I ⪯ 𝔸_X` (`norm_inv_sqrt_le`);
* `Y_X = 𝔸_X^{-1/2} Z_X` and `Y = 𝔸^{-1/2} Z` (uniqueness of weak limits).

The screen radii `R` are indexed by `ℕ` and the cutoffs `X` by a sequence.  The upper bound
`𝔸_X ⪯ M I` and the finite rank of `S_{X,R}` are not needed by the argument and are omitted
(the theorem is stated without them, i.e. more generally).
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RenewalGeometry.CompactPositiveScreen

open SMSTChannel

variable {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- **Banach–Steinhaus for weak convergence**: a weakly convergent sequence in a Hilbert space
is norm bounded. -/
theorem norm_bounded_of_weakTendsto {Z : ℕ → Y} {Zlim : Y} (hZ : WeakTendsto Z Zlim) :
    ∃ C : ℝ, ∀ n, ‖Z n‖ ≤ C := by
  have hpt : ∀ y : Y, ∃ C, ∀ n, ‖innerSL ℂ (Z n) y‖ ≤ C := by
    intro y
    obtain ⟨C, hC⟩ := (hZ y).norm.bddAbove_range
    refine ⟨C, fun n => ?_⟩
    rw [innerSL_apply_apply, ← norm_inner_symm]
    exact hC ⟨n, rfl⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpt
  exact ⟨C, fun n => by rw [← innerSL_apply_norm ℂ (Z n)]; exact hC n⟩

/-- Strong convergence implies weak convergence. -/
theorem weakTendsto_of_tendsto {Z : ℕ → Y} {Zlim : Y} (hZ : Tendsto Z atTop (𝓝 Zlim)) :
    WeakTendsto Z Zlim :=
  fun y => ((innerSL ℂ y).continuous.tendsto Zlim).comp hZ

/-- Weak limits are unique. -/
theorem weakTendsto_unique {Z : ℕ → Y} {a b : Y} (ha : WeakTendsto Z a) (hb : WeakTendsto Z b) :
    a = b :=
  ext_inner_left ℂ fun y => tendsto_nhds_unique (ha y) (hb y)

/-- A bounded linear operator is weakly continuous: `W_n ⇀ W` implies `S W_n ⇀ S W`. -/
theorem weakTendsto_map {W : ℕ → Y} {Wlim : Y} (hW : WeakTendsto W Wlim) (S : Y →L[ℂ] Y) :
    WeakTendsto (fun n => S (W n)) (S Wlim) := by
  intro y
  simpa only [ContinuousLinearMap.adjoint_inner_left] using hW (ContinuousLinearMap.adjoint S y)

/-- **Compact operators are completely continuous**: a compact operator maps a bounded weakly
convergent sequence to a norm-convergent one. -/
theorem tendsto_of_isCompactOperator (S : Y →L[ℂ] Y) (hS : IsCompactOperator S)
    {W : ℕ → Y} {Wlim : Y} (C : ℝ) (hb : ∀ n, ‖W n‖ ≤ C) (hW : WeakTendsto W Wlim) :
    Tendsto (fun n => S (W n)) atTop (𝓝 (S Wlim)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hK := hS.isCompact_closure_image_closedBall (f := (S : Y →ₗ[ℂ] Y)) C
  have hmem : ∀ k, S (W (ns k)) ∈ closure ((S : Y →ₗ[ℂ] Y) '' Metric.closedBall 0 C) :=
    fun k => subset_closure ⟨W (ns k), by simpa using hb (ns k), rfl⟩
  obtain ⟨a, -, φ, hφ, ha⟩ := hK.tendsto_subseq hmem
  refine ⟨φ, ?_⟩
  have hweak : WeakTendsto (fun k => S (W (ns (φ k)))) (S Wlim) :=
    fun y => (weakTendsto_map hW S y).comp (hns.comp hφ.tendsto_atTop)
  have hstrong : WeakTendsto (fun k => S (W (ns (φ k)))) a := weakTendsto_of_tendsto ha
  rw [weakTendsto_unique hweak hstrong]
  exact ha

/-- Coercivity `m I ⪯ 𝔸` in the Loewner order gives `m ‖v‖² ≤ Re ⟪𝔸 v, v⟫`. -/
theorem re_inner_ge_of_le (A : Y →L[ℂ] Y) (m : ℝ) (h : (m : ℂ) • (1 : Y →L[ℂ] Y) ≤ A) (v : Y) :
    m * ‖v‖ ^ 2 ≤ RCLike.re ⟪A v, v⟫_ℂ := by
  rw [ContinuousLinearMap.le_def] at h
  have h1 := h.re_inner_nonneg_left v
  have h2 : RCLike.re ⟪((m : ℂ) • (1 : Y →L[ℂ] Y)) v, v⟫_ℂ = m * ‖v‖ ^ 2 := by
    simp [inner_self_eq_norm_sq_to_K] <;>
      first | (left; rw [← Complex.ofReal_pow, Complex.ofReal_re]) | exact Or.inl (by ring)
  rw [sub_apply, inner_sub_left, map_sub, h2] at h1
  linarith

/-- `m I ⪯ 𝔸` with `m > 0` makes `𝔸` positive. -/
theorem nonneg_of_le (A : Y →L[ℂ] Y) (m : ℝ) (hm : 0 < m) (h : (m : ℂ) • (1 : Y →L[ℂ] Y) ≤ A) :
    0 ≤ A := by
  refine le_trans ?_ h
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  have : (m : ℂ) • (1 : Y →L[ℂ] Y) = ((m : ℝ) : ℂ) • ContinuousLinearMap.id ℂ Y := rfl
  rw [this]
  exact (ContinuousLinearMap.isPositive_id).smul_of_nonneg (by exact_mod_cast hm.le)

/-- `‖𝔸^{1/2} v‖² = Re ⟪𝔸 v, v⟫` for a positive `𝔸`. -/
theorem norm_sqrt_apply_sq (A : Y →L[ℂ] Y) (hA : 0 ≤ A) (v : Y) :
    ‖CFC.sqrt A v‖ ^ 2 = RCLike.re ⟪A v, v⟫_ℂ := by
  have hsa : IsSelfAdjoint (CFC.sqrt A) := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hmul : CFC.sqrt A (CFC.sqrt A v) = A v := by
    rw [← ContinuousLinearMap.mul_apply, CFC.sqrt_mul_sqrt_self A hA]
  have hsym := hsa.isSymmetric (CFC.sqrt A v) v
  simp only [ContinuousLinearMap.coe_coe] at hsym
  rw [← hmul, hsym, inner_self_eq_norm_sq]

/-- **`‖𝔸^{-1/2}‖ ≤ m^{-1/2}`** from `m I ⪯ 𝔸`, for the two-sided inverse `T` of `𝔸^{1/2}`. -/
theorem norm_inv_sqrt_le (A : Y →L[ℂ] Y) (m : ℝ) (hm : 0 < m)
    (h : (m : ℂ) • (1 : Y →L[ℂ] Y) ≤ A) (T : Y →L[ℂ] Y) (hT : CFC.sqrt A * T = 1) :
    ‖T‖ ≤ (Real.sqrt m)⁻¹ := by
  have hA := nonneg_of_le A m hm h
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hw : CFC.sqrt A (T w) = w := by
    rw [← ContinuousLinearMap.mul_apply, hT, ContinuousLinearMap.one_apply]
  have hsq : m * ‖T w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    have h1 := norm_sqrt_apply_sq A hA (T w)
    rw [hw] at h1
    rw [h1]
    exact re_inner_ge_of_le A m h (T w)
  have hsq' : (Real.sqrt m * ‖T w‖) ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hm.le]; exact hsq
  have hle : Real.sqrt m * ‖T w‖ ≤ ‖w‖ :=
    (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg w) two_ne_zero).1 hsq'
  rw [inv_mul_eq_div, le_div_iff₀ hsm]
  linarith

/-! ### The upgrade -/

/-- **`prop:supp-compact-upgrade`, strong convergence.**  Let `Y_X ⇀ Y` in the Hilbert space
`𝒴`, let `𝔸_X` satisfy `m I ⪯ 𝔸_X` (`m > 0`), let `𝔸_X^{-1/2}` be the two-sided inverse of
`𝔸_X^{1/2} = CFC.sqrt 𝔸_X` and `𝔸_X^{-1/2} → T` strongly (`T = 𝔸^{-1/2}`).  Put
`Z_X = 𝔸_X^{1/2} Y_X` and suppose `Z_X ⇀ Z`.  If the screens satisfy `S_{X,R} → S_R` in operator
norm with `S_R` compact, `lim_R sup_X ‖(I - S_{X,R}) Z_X‖ = 0` and `lim_R ‖(I - S_R) Z‖ = 0`, then
`Z_X → Z` and `Y_X → Y` strongly, and `Y = T Z`.  (`sup_X ‖Z_X‖ < ∞`, complete continuity of
`S_R` and `‖𝔸_X^{-1/2}‖ ≤ m^{-1/2}` are derived.) -/
theorem compact_positive_screen_upgrade
    (Yseq : ℕ → Y) (Ylim : Y) (hY : WeakTendsto Yseq Ylim)
    (A : ℕ → Y →L[ℂ] Y) (m : ℝ) (hm : 0 < m)
    (hcoer : ∀ n, (m : ℂ) • (1 : Y →L[ℂ] Y) ≤ A n)
    (Ainv : ℕ → Y →L[ℂ] Y)
    (hAinv : ∀ n, Ainv n * CFC.sqrt (A n) = 1 ∧ CFC.sqrt (A n) * Ainv n = 1)
    (T : Y →L[ℂ] Y) (hT : ∀ v, Tendsto (fun n => Ainv n v) atTop (𝓝 (T v)))
    (Zlim : Y) (hZ : WeakTendsto (fun n => CFC.sqrt (A n) (Yseq n)) Zlim)
    (SR : ℕ → Y →L[ℂ] Y) (Sh : ℕ → ℕ → Y →L[ℂ] Y)
    (hSconv : ∀ R, Tendsto (fun n => ‖Sh R n - SR R‖) atTop (𝓝 0))
    (hScpt : ∀ R, IsCompactOperator (SR R))
    (htail : ∀ ε > (0 : ℝ), ∃ R₀, ∀ R ≥ R₀, ∀ n,
      ‖CFC.sqrt (A n) (Yseq n) - Sh R n (CFC.sqrt (A n) (Yseq n))‖ ≤ ε)
    (htailZ : ∀ ε > (0 : ℝ), ∃ R₀, ∀ R ≥ R₀, ‖Zlim - SR R Zlim‖ ≤ ε) :
    Tendsto (fun n => CFC.sqrt (A n) (Yseq n)) atTop (𝓝 Zlim) ∧
    Tendsto Yseq atTop (𝓝 Ylim) ∧ Ylim = T Zlim := by
  set Z : ℕ → Y := fun n => CFC.sqrt (A n) (Yseq n) with hZdef
  obtain ⟨Cb, hCb⟩ := norm_bounded_of_weakTendsto hZ
  have hZs : Tendsto Z atTop (𝓝 Zlim) :=
    screen_strong_convergence Z Zlim Cb hCb hZ SR Sh hSconv
      (fun R W Wlim Cw hb hw => tendsto_of_isCompactOperator (SR R) (hScpt R) Cw hb hw)
      htail htailZ
  have hYZ : ∀ n, Yseq n = Ainv n (Z n) := fun n => by
    simp only [hZdef]
    rw [← ContinuousLinearMap.mul_apply, (hAinv n).1, ContinuousLinearMap.one_apply]
  have hbd : ∀ n, ‖Ainv n‖ ≤ (Real.sqrt m)⁻¹ := fun n =>
    norm_inv_sqrt_le (A n) m hm (hcoer n) (Ainv n) (hAinv n).2
  have htr := strong_convergence_transfer Ainv T (Real.sqrt m)⁻¹ hbd hT Z Zlim hZs
  have hYs : Tendsto Yseq atTop (𝓝 (T Zlim)) := htr.congr fun n => (hYZ n).symm
  have hid : Ylim = T Zlim := weakTendsto_unique hY (weakTendsto_of_tendsto hYs)
  exact ⟨hZs, hid ▸ hYs, hid⟩

/-- A bounded real-bilinear quadratic insertion is Lipschitz on bounded sets:
`‖B(u,u) - B(v,v)‖ ≤ ‖B‖ ‖u - v‖ (‖u‖ + ‖v‖)`. -/
theorem norm_bilinear_diag_sub_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : Y →L[ℝ] Y →L[ℝ] W) (u v : Y) :
    ‖B u u - B v v‖ ≤ ‖B‖ * ‖u - v‖ * (‖u‖ + ‖v‖) := by
  have hsplit : B u u - B v v = B (u - v) u + B v (u - v) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]; abel
  rw [hsplit]
  calc ‖B (u - v) u + B v (u - v)‖ ≤ ‖B (u - v) u‖ + ‖B v (u - v)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖u - v‖ * ‖u‖ + ‖B‖ * ‖v‖ * ‖u - v‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ = ‖B‖ * ‖u - v‖ * (‖u‖ + ‖v‖) := by ring

/-- Bounded quadratic insertions pass to strong limits. -/
theorem tendsto_bilinear_diag {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : Y →L[ℝ] Y →L[ℝ] W) {u : ℕ → Y} {v : Y} (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => B (u n) (u n)) atTop (𝓝 (B v v)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hd : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hu
  have hmaj : Tendsto (fun n => ‖B‖ * ‖u n - v‖ * (‖u n‖ + ‖v‖)) atTop (𝓝 0) := by
    have := ((hd.const_mul ‖B‖).mul ((hu.norm).add_const ‖v‖))
    simpa using this
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_bilinear_diag_sub_le B (u n) v) hmaj

/-! ### The cylinder space `L²(K; E)`: quadratic insertions converge in `L¹` -/

section Cylinder

open MeasureTheory ENNReal

variable {α : Type} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

instance holderTriple_two_two_one : HolderTriple (2 : ℝ≥0∞) 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

/-- **Quadratic `L¹` estimate**: for a pointwise bounded real-bilinear density `b`,
`‖b(f,f) - b(g,g)‖_{L¹} ≤ ‖b‖ ‖f - g‖_{L²} (‖f‖_{L²} + ‖g‖_{L²})`. -/
theorem eLpNorm_quadratic_insertion_le (b : E →L[ℝ] E →L[ℝ] G) (f g : α → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => b (f x) (f x) - b (g x) (g x)) 1 μ ≤
      ‖b‖₊ * eLpNorm (f - g) 2 μ * (eLpNorm f 2 μ + eLpNorm g 2 μ) := by
  have hsplit : (fun x => b (f x) (f x) - b (g x) (g x)) =
      (fun x => b ((f - g) x) (f x)) + fun x => b (g x) ((f - g) x) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, map_sub, ContinuousLinearMap.sub_apply]
    abel
  have h1 : eLpNorm (fun x => b ((f - g) x) (f x)) 1 μ ≤
      ‖b‖₊ * eLpNorm (f - g) 2 μ * eLpNorm f 2 μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (hf.sub hg) hf (fun x y => b x y) ‖b‖₊
      (Eventually.of_forall fun x => by rw [coe_nnnorm]; exact b.le_opNorm₂ _ _)
  have h2 : eLpNorm (fun x => b (g x) ((f - g) x)) 1 μ ≤
      ‖b‖₊ * eLpNorm g 2 μ * eLpNorm (f - g) 2 μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hg (hf.sub hg) (fun x y => b x y) ‖b‖₊
      (Eventually.of_forall fun x => by rw [coe_nnnorm]; exact b.le_opNorm₂ _ _)
  rw [hsplit]
  refine (eLpNorm_add_le (b.aestronglyMeasurable_comp₂ (hf.sub hg) hf)
    (b.aestronglyMeasurable_comp₂ hg (hf.sub hg)) le_rfl).trans ?_
  calc eLpNorm (fun x => b ((f - g) x) (f x)) 1 μ + eLpNorm (fun x => b (g x) ((f - g) x)) 1 μ
      ≤ ‖b‖₊ * eLpNorm (f - g) 2 μ * eLpNorm f 2 μ +
          ‖b‖₊ * eLpNorm g 2 μ * eLpNorm (f - g) 2 μ := add_le_add h1 h2
    _ = ‖b‖₊ * eLpNorm (f - g) 2 μ * (eLpNorm f 2 μ + eLpNorm g 2 μ) := by ring

/-- Strong convergence in `L²(K; E)` makes every pointwise bounded quadratic density converge in
`L¹(K)`. -/
theorem tendsto_quadratic_insertion_L1 (b : E →L[ℝ] E →L[ℝ] G) {u : ℕ → Lp E 2 μ}
    {v : Lp E 2 μ} (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => eLpNorm (fun x => b (u n x) (u n x) - b (v x) (v x)) 1 μ) atTop (𝓝 0) := by
  have hd : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hu
  have hnorm : ∀ w : Lp E 2 μ, eLpNorm (w : α → E) 2 μ = ENNReal.ofReal ‖w‖ := fun w => by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top w)]
  have hdiff : ∀ n, eLpNorm ((u n : α → E) - (v : α → E)) 2 μ = ENNReal.ofReal ‖u n - v‖ := fun n => by
    rw [← hnorm]
    exact eLpNorm_congr_ae (Lp.coeFn_sub (u n) v).symm
  have hest : ∀ n, eLpNorm (fun x => b (u n x) (u n x) - b (v x) (v x)) 1 μ ≤
      ‖b‖₊ * ENNReal.ofReal ‖u n - v‖ * (ENNReal.ofReal ‖u n‖ + ENNReal.ofReal ‖v‖) :=
    fun n => by
      have := eLpNorm_quadratic_insertion_le (μ := μ) b (u n) v (Lp.aestronglyMeasurable _)
        (Lp.aestronglyMeasurable _)
      rwa [hdiff, hnorm, hnorm] at this
  have hmaj : Tendsto (fun n => (‖b‖₊ : ℝ≥0∞) * ENNReal.ofReal ‖u n - v‖ *
      (ENNReal.ofReal ‖u n‖ + ENNReal.ofReal ‖v‖)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => ENNReal.ofReal ‖u n - v‖) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp hd
      rwa [ENNReal.ofReal_zero] at this
    have h1 : Tendsto (fun n => ENNReal.ofReal ‖u n‖ + ENNReal.ofReal ‖v‖) atTop
        (𝓝 (ENNReal.ofReal ‖v‖ + ENNReal.ofReal ‖v‖)) :=
      ((ENNReal.continuous_ofReal.tendsto _).comp hu.norm).add tendsto_const_nhds
    have h2 := ENNReal.Tendsto.mul (ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.coe_ne_top (r := ‖b‖₊))))
      (Or.inr (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)) h1
      (Or.inr (by simp))
    simpa using h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj (fun _ => zero_le) hest

/-- **`prop:supp-compact-upgrade`** with the quadratic clause on the cylinder.  The Hilbert space
`𝒴` is realised in the cylinder space `L²(K; E)` by a bounded real-linear map
`ι : 𝒴 →L L²(K; E)` (e.g. the identity of `L²(K; E)` or the inclusion of a closed subspace of
packets).  Under the hypotheses of `compact_positive_screen_upgrade`, `Z_X → Z` and `Y_X → Y`
strongly, `Y = T Z`, and **every bounded quadratic insertion in `Y_X` converges in `L¹(K)`**: for
each pointwise bounded real-bilinear density `b`, `b(Y_X, Y_X) → b(Y, Y)` in `L¹(K)`, with
`‖b(Y_X,Y_X) - b(Y,Y)‖_{L¹} ≤ ‖b‖ ‖Y_X - Y‖₂ (‖Y_X‖₂ + ‖Y‖₂)`. -/
theorem compact_positive_screen_upgrade_L2 (ι : Y →L[ℝ] Lp E 2 μ)
    (Yseq : ℕ → Y) (Ylim : Y) (hY : WeakTendsto Yseq Ylim)
    (A : ℕ → Y →L[ℂ] Y) (m : ℝ) (hm : 0 < m)
    (hcoer : ∀ n, (m : ℂ) • (1 : Y →L[ℂ] Y) ≤ A n)
    (Ainv : ℕ → Y →L[ℂ] Y)
    (hAinv : ∀ n, Ainv n * CFC.sqrt (A n) = 1 ∧ CFC.sqrt (A n) * Ainv n = 1)
    (T : Y →L[ℂ] Y) (hT : ∀ v, Tendsto (fun n => Ainv n v) atTop (𝓝 (T v)))
    (Zlim : Y) (hZ : WeakTendsto (fun n => CFC.sqrt (A n) (Yseq n)) Zlim)
    (SR : ℕ → Y →L[ℂ] Y) (Sh : ℕ → ℕ → Y →L[ℂ] Y)
    (hSconv : ∀ R, Tendsto (fun n => ‖Sh R n - SR R‖) atTop (𝓝 0))
    (hScpt : ∀ R, IsCompactOperator (SR R))
    (htail : ∀ ε > (0 : ℝ), ∃ R₀, ∀ R ≥ R₀, ∀ n,
      ‖CFC.sqrt (A n) (Yseq n) - Sh R n (CFC.sqrt (A n) (Yseq n))‖ ≤ ε)
    (htailZ : ∀ ε > (0 : ℝ), ∃ R₀, ∀ R ≥ R₀, ‖Zlim - SR R Zlim‖ ≤ ε) :
    Tendsto (fun n => CFC.sqrt (A n) (Yseq n)) atTop (𝓝 Zlim) ∧
    Tendsto Yseq atTop (𝓝 Ylim) ∧ Ylim = T Zlim ∧
    ∀ b : E →L[ℝ] E →L[ℝ] G,
      Tendsto (fun n => eLpNorm (fun x => b (ι (Yseq n) x) (ι (Yseq n) x) -
        b (ι Ylim x) (ι Ylim x)) 1 μ) atTop (𝓝 0) := by
  obtain ⟨h1, h2, h3⟩ := compact_positive_screen_upgrade Yseq Ylim hY A m hm hcoer Ainv hAinv T hT
    Zlim hZ SR Sh hSconv hScpt htail htailZ
  exact ⟨h1, h2, h3, fun b => tendsto_quadratic_insertion_L1 b ((ι.continuous.tendsto Ylim).comp h2)⟩

end Cylinder

/-- Non-vacuity of the hypothesis packet of `compact_positive_screen_upgrade` with a nonzero
packet: `𝒴 = ℂ`, `𝔸_X = 1` (`m = 1`), `Y_X = 1`, screens `S_{X,R} = S_R = 1` (compact on the
finite-dimensional space `ℂ`). -/
example : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := by
  have hc : IsCompactOperator ((1 : ℂ →L[ℂ] ℂ) : ℂ → ℂ) := by
    have := (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ) (E := ℂ)).2 inferInstance
    simpa using this
  have h := compact_positive_screen_upgrade (Y := ℂ) (fun _ => 1) 1
    (fun y => tendsto_const_nhds) (fun _ => 1) 1 one_pos (fun _ => by simp)
    (fun _ => 1) (fun _ => by simp [CFC.sqrt_one]) 1 (fun v => tendsto_const_nhds) 1
    (fun y => by simp [CFC.sqrt_one]) (fun _ => 1) (fun _ _ => 1) (fun R => by simp)
    (fun R => hc) (fun ε hε => ⟨0, fun R _ n => by simp [CFC.sqrt_one]; exact hε.le⟩)
    (fun ε hε => ⟨0, fun R _ => by simp; exact hε.le⟩)
  exact h.2.1

end RenewalGeometry.CompactPositiveScreen
