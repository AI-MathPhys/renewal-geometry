/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallRotationInvariance
import RenewalGeometry.Analysis.SobolevCriticalEmbedding

/-!
# Interior `H²` regularity for the weak Laplace equation
  (stage C4b, step 2, of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.  Real-valued functions on `ℝⁿ = Fin n → ℝ`.

* `HasWeakPartialR Ω i u g` — real weak partial derivatives (`hasWeakPartialR_iff`: the same as
  the complex `SobolevOpen.HasWeakPartial` of the complexifications);
* `integral_sum_sq_hessian` — **the `C_c^∞` Hessian identity**
  `Σ_{k,l} ∫ (∂_l∂_k v)² = ∫ (Δv)²` (two integrations by parts);
* `whole_space_H2` — **whole-space `H²` regularity**: a compactly supported `w ∈ H¹(ℝⁿ)` whose
  weak Laplacian is `F ∈ L²` has weak second derivatives `∂_l∂_k w ∈ L²` with
  `Σ_{k,l} ‖∂_l∂_k w‖² ≤ ‖F‖²` (mollification: the mollified Hessians are Cauchy in `L²` by the
  Hessian identity, and weak derivatives pass to `L²` limits);
* `interior_H2` — **local version**: if `u ∈ H¹(Ω)` solves `Δu = f ∈ L²(Ω)` weakly and `χ` is a
  test function on `Ω`, the gradient of `u` has weak derivatives in `L²` on the interior of
  `{χ = 1}`, with a bound by `‖Δ(χu)‖`, `Δ(χu) = χ f + 2∇χ·∇u + (Δχ) u`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Convolution

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ### Real weak partial derivatives -/

/-- `g` is the **real weak `i`-th partial derivative** of `u` on `Ω`:
`∫ ∂_iφ · u = -∫ φ · g` for every `φ ∈ C_c^∞(Ω)`. -/
def HasWeakPartialR (Ω : Set (Fin n → ℝ)) (i : Fin n) (u g : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ φ : (Fin n → ℝ) → ℝ, IsTest Ω φ → ∫ x, pd φ i x * u x = -∫ x, φ x * g x

theorem hasWeakPartialR_iff {Ω : Set (Fin n → ℝ)} {i : Fin n} {u g : (Fin n → ℝ) → ℝ} :
    HasWeakPartialR Ω i u g ↔
      HasWeakPartial Ω i (fun x => ((u x : ℝ) : ℂ)) (fun x => ((g x : ℝ) : ℂ)) := by
  have e : ∀ φ : (Fin n → ℝ) → ℝ, (∫ x, ((pd φ i x : ℝ) : ℂ) * ((u x : ℝ) : ℂ)) =
      ((∫ x, pd φ i x * u x : ℝ) : ℂ) ∧ (∫ x, ((φ x : ℝ) : ℂ) * ((g x : ℝ) : ℂ)) =
      ((∫ x, φ x * g x : ℝ) : ℂ) := fun φ => by
    constructor
    · rw [← integral_complex_ofReal]; congr 1; funext x; push_cast; ring
    · rw [← integral_complex_ofReal]; congr 1; funext x; push_cast; ring
  constructor
  · intro h φ hφ
    rw [(e φ).1, (e φ).2, h φ hφ]; push_cast; ring
  · intro h φ hφ
    have := h φ hφ
    rw [(e φ).1, (e φ).2] at this
    exact_mod_cast this

/-- Restriction to a smaller set, and replacement of `u` by a function agreeing with it there. -/
theorem HasWeakPartialR.congr_left {Ω Ω' : Set (Fin n → ℝ)} {i : Fin n} {u u' g : (Fin n → ℝ) → ℝ}
    (h : HasWeakPartialR Ω i u g) (hΩ : Ω' ⊆ Ω) (heq : ∀ x ∈ Ω', u x = u' x) :
    HasWeakPartialR Ω' i u' g := by
  intro φ hφ
  rw [← h φ (hφ.mono hΩ)]
  congr 1; funext x
  by_cases hx : x ∈ Ω'
  · rw [heq x hx]
  · rw [image_eq_zero_of_notMem_tsupport (fun h' => hx (hφ.subset (tsupport_pd_subset φ i h'))),
      zero_mul, zero_mul]

theorem HasWeakPartialR.congr_right {Ω : Set (Fin n → ℝ)} {i : Fin n} {u g g' : (Fin n → ℝ) → ℝ}
    (h : HasWeakPartialR Ω i u g) (heq : ∀ x ∈ Ω, g x = g' x) : HasWeakPartialR Ω i u g' := by
  intro φ hφ
  rw [h φ hφ]
  congr 2; funext x
  by_cases hx : x ∈ Ω
  · rw [heq x hx]
  · rw [image_eq_zero_of_notMem_tsupport (fun h' => hx (hφ.subset h')), zero_mul, zero_mul]

/-- Classical derivatives are weak derivatives. -/
theorem hasWeakPartialR_of_contDiff (Ω : Set (Fin n → ℝ)) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (i : Fin n) : HasWeakPartialR Ω i u (pd u i) :=
  fun φ hφ => integral_pd_mul_eq_neg_real hu hφ.smooth hφ.compact i

/-! ### `L²` norms as integrals -/

theorem norm_sq_toLp_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x h1
  rw [h1]
  simp [sq]

theorem norm_sq_Lp_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, (f : α → ℝ) x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [sq]

/-! ### Mollification of real functions -/

/-- **Derivatives of mollifications** (real version): if `g` is the weak `i`-th partial of `u` on
`ℝⁿ` and `ρ ∈ C_c^∞`, then `∂_i(ρ ⋆ u) = ρ ⋆ g`. -/
theorem pd_convolution_eq_R {ρ : (Fin n → ℝ) → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) {i : Fin n} {u g : (Fin n → ℝ) → ℝ}
    (hw : HasWeakPartialR univ i u g) (hu : LocallyIntegrable u volume) (x : Fin n → ℝ) :
    pd (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) i x =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  unfold pd
  rw [Mollifier.fderiv_convolution_apply hρ1 hρc hu x (Pi.single i 1), convolution_def]
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : (Fin n → ℝ) → ℝ, ψ = fun y => ρ (x - y) := ⟨_, rfl⟩
  have hψs : ContDiff ℝ ∞ ψ := by rw [hψdef]; exact hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := by rw [hψdef]; exact hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hψ : IsTest univ ψ := ⟨hψs, hψc, subset_univ _⟩
  have hpdψ : ∀ y, pd ψ i y = -(fderiv ℝ ρ (x - y) (Pi.single i 1)) := by
    intro y
    unfold pd
    have h1 : HasFDerivAt (fun y : Fin n → ℝ => x - y) (-ContinuousLinearMap.id ℝ (Fin n → ℝ)) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 := ((hρ1.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y h1
    rw [hψdef, show (fun y => ρ (x - y)) = ρ ∘ fun y => x - y from rfl, h2.fderiv]
    simp
  have key := hw ψ hψ
  simp only [hpdψ, neg_mul, integral_neg] at key
  have e1 : ∫ t, fderiv ℝ ρ t (Pi.single i 1) • u (x - t) =
      ∫ y, fderiv ℝ ρ (x - y) (Pi.single i 1) • u y := by
    rw [← integral_sub_left_eq_self (fun t => fderiv ℝ ρ t (Pi.single i 1) • u (x - t)) volume x]
    simp only [sub_sub_cancel]
  have e2 : ∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (g (x - t)) =
      ∫ y, ρ (x - y) * g y := by
    rw [← integral_sub_left_eq_self (fun t => (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (g (x - t)))
      volume x]
    simp only [sub_sub_cancel, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [e1, e2]
  simp only [smul_eq_mul]
  rw [hψdef] at key
  exact neg_inj.mp key

/-! ### The Hessian identity for `C_c^∞` functions -/

theorem contDiff_pd_inf {v : (Fin n → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v) (k : Fin n) :
    ContDiff ℝ ∞ (pd v k) := contDiff_pd hv k

theorem hasCompactSupport_pd_pd {v : (Fin n → ℝ) → ℝ} (hv : HasCompactSupport v) (k l : Fin n) :
    HasCompactSupport (pd (pd v k) l) :=
  hasCompactSupport_pd (hasCompactSupport_pd hv k) l

/-- `∂_l∂_l∂_k v = ∂_k∂_l∂_l v` for `C³` functions. -/
theorem pd3_symm {v : (Fin n → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v) (k l : Fin n) :
    pd (pd (pd v k) l) l = pd (pd (pd v l) l) k := by
  have h1 : pd (pd v k) l = pd (pd v l) k :=
    funext fun x => (pd_pd_symm (hv.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) l k x)
  rw [h1]
  funext x
  exact pd_pd_symm ((contDiff_pd hv l).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) l k x

/-- **The Hessian identity**: `Σ_{k,l} ∫ (∂_l∂_k v)² = ∫ (Σ_k ∂_k∂_k v)²` for `v ∈ C_c^∞(ℝⁿ)`. -/
theorem integral_sum_sq_hessian {v : (Fin n → ℝ) → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) :
    ∑ k, ∑ l, ∫ x, pd (pd v k) l x ^ 2 = ∫ x, (∑ k, pd (pd v k) k x) ^ 2 := by
  have hs : ∀ k, ContDiff ℝ ∞ (pd v k) := fun k => contDiff_pd hv k
  have hs2 : ∀ k l, ContDiff ℝ ∞ (pd (pd v k) l) := fun k l => contDiff_pd (hs k) l
  have hc : ∀ k, HasCompactSupport (pd v k) := fun k => hasCompactSupport_pd hvc k
  have hc2 : ∀ k l, HasCompactSupport (pd (pd v k) l) := fun k l => hasCompactSupport_pd (hc k) l
  -- term by term
  have hterm : ∀ k l, ∫ x, pd (pd v k) l x ^ 2 = ∫ x, pd (pd v k) k x * pd (pd v l) l x := by
    intro k l
    -- first integration by parts in the direction `l`
    have i1 := integral_pd_mul_eq_neg_real ((hs2 k l).of_le (by simp)) (hs k) (hc k) l
    -- `∫ ∂_l∂_k v · ∂_l∂_k v = -∫ ∂_k v · ∂_l∂_l∂_k v`
    have e1 : ∫ x, pd (pd v k) l x ^ 2 = -∫ x, pd v k x * pd (pd (pd v k) l) l x := by
      rw [← i1]; congr 1; funext x; ring
    rw [e1, pd3_symm hv k l]
    -- second integration by parts in the direction `k`
    have i2 := integral_pd_mul_eq_neg_real ((hs k).of_le (by simp)) (hs2 l l) (hc2 l l) k
    have e2 : ∫ x, pd v k x * pd (pd (pd v l) l) k x = ∫ x, pd (pd (pd v l) l) k x * pd v k x := by
      congr 1; funext x; ring
    rw [e2, i2, neg_neg]
    congr 1; funext x; ring
  simp only [hterm]
  have hint : ∀ k l, Integrable fun x => pd (pd v k) k x * pd (pd v l) l x := fun k l =>
    ((hs2 k k).continuous.mul (hs2 l l).continuous).integrable_of_hasCompactSupport
      (hc2 k k).mul_right
  have e1 : ∀ k, ∑ l, ∫ x, pd (pd v k) k x * pd (pd v l) l x =
      ∫ x, ∑ l, pd (pd v k) k x * pd (pd v l) l x := fun k =>
    (integral_finset_sum _ fun l _ => hint k l).symm
  simp only [e1]
  rw [← integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => hint k l]
  congr 1; funext x
  rw [sq, Finset.sum_mul_sum]

/-! ### Mollifiers -/

/-- The standard mollifier bumps, outer radius `2/(m+2) → 0`. -/
def bumpSeq (m : ℕ) : ContDiffBump (0 : Fin n → ℝ) :=
  ⟨1 / ((m : ℝ) + 2), 2 / ((m : ℝ) + 2), by positivity,
    by apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩

/-- The normalized mollifier `ρ_m`. -/
def molli (m : ℕ) : (Fin n → ℝ) → ℝ := (bumpSeq m).normed volume

/-- Mollification `ρ_m ⋆ f`. -/
def mconv (m : ℕ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  molli m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem molli_smooth (m : ℕ) : ContDiff ℝ ∞ (molli (n := n) m) := (bumpSeq m).contDiff_normed

theorem molli_compact (m : ℕ) : HasCompactSupport (molli (n := n) m) :=
  (bumpSeq m).hasCompactSupport_normed

theorem tendsto_bumpSeq_rOut : Tendsto (fun m => (bumpSeq (n := n) m).rOut) atTop (𝓝 0) := by
  show Tendsto (fun m : ℕ => 2 / ((m : ℝ) + 2)) atTop (𝓝 0)
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
  rw [mul_zero] at h
  refine squeeze_zero (fun m => by positivity) (fun m => ?_) h
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

theorem contDiff_mconv (m : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ ∞ (mconv m f) :=
  (molli_compact m).contDiff_convolution_left _ (molli_smooth m) hf

theorem hasCompactSupport_mconv (m : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (mconv m f) :=
  (molli_compact m).convolution _ hf

theorem eLpNorm_mconv_le (m : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume) :
    eLpNorm (mconv m f) 2 volume ≤ eLpNorm f 2 volume :=
  Mollifier.eLpNorm_convolution_le (bumpSeq m).continuous_normed.measurable
    (fun x => (bumpSeq m).nonneg_normed x) (bumpSeq m).integral_normed hf.aestronglyMeasurable
    (by norm_num) (by norm_num)

theorem memLp_mconv (m : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume) :
    MemLp (mconv m f) 2 volume :=
  ⟨(contDiff_mconv m (hf.locallyIntegrable (by norm_num))).continuous.aestronglyMeasurable,
    (eLpNorm_mconv_le m hf).trans_lt hf.eLpNorm_lt_top⟩

theorem tendsto_mconv {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun m => eLpNorm (mconv m f - f) 2 volume) atTop (𝓝 0) :=
  Mollifier.tendsto_eLpNorm_normed_bump_convolution_sub tendsto_bumpSeq_rOut (by norm_num)
    (by norm_num) hf

theorem mconv_sub (m : ℕ) {f g : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) : mconv m (f - g) = mconv m f - mconv m g := by
  funext x
  exact Mollifier.convolution_sub_apply
    ((molli_compact m).convolutionExists_left _ (molli_smooth m).continuous hf x)
    ((molli_compact m).convolutionExists_left _ (molli_smooth m).continuous hg x)

/-- `toLp` convergence from `eLpNorm` convergence. -/
theorem tendsto_toLp_of_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {f₀ : α → ℝ} (hf : ∀ m, MemLp (f m) 2 μ) (hf₀ : MemLp f₀ 2 μ)
    (h : Tendsto (fun m => eLpNorm (f m - f₀) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => (hf m).toLp (f m)) atTop (𝓝 (hf₀.toLp f₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ m, ‖(hf m).toLp (f m) - hf₀.toLp f₀‖ = (eLpNorm (f m - f₀) 2 μ).toReal := by
    intro m
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
  simp only [e]
  rw [← ENNReal.toReal_zero]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

/-- A sequence dominated (in distances) by a convergent sequence is Cauchy. -/
theorem cauchySeq_of_dist_le {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {x : ℕ → E} {y : ℕ → F} (hy : CauchySeq y) (h : ∀ m p, dist (x m) (x p) ≤ dist (y m) (y p)) :
    CauchySeq x := by
  rw [Metric.cauchySeq_iff] at hy ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hy ε hε
  exact ⟨N, fun m hm p hp => (h m p).trans_lt (hN m hm p hp)⟩

/-- **The Laplacian of a mollification**: if `Δw = F` weakly on `ℝⁿ` (with weak gradient `g`),
then `Δ(ρ_m ⋆ w) = ρ_m ⋆ F` pointwise. -/
theorem lap_mconv (m : ℕ) {w F : (Fin n → ℝ) → ℝ} {g : Fin n → (Fin n → ℝ) → ℝ}
    (hwl : LocallyIntegrable w volume) (hgl : ∀ k, LocallyIntegrable (g k) volume)
    (hwk : ∀ k, HasWeakPartialR univ k w (g k))
    (hΔ : ∀ φ, IsTest univ φ → ∑ k, ∫ x, pd φ k x * g k x = -∫ x, φ x * F x) (x : Fin n → ℝ) :
    ∑ k, pd (pd (mconv m w) k) k x = mconv m F x := by
  have hρ1 : ContDiff ℝ 1 (molli (n := n) m) := (molli_smooth m).of_le (by simp)
  have e1 : ∀ k, pd (mconv m w) k = mconv m (g k) := fun k =>
    funext fun y => pd_convolution_eq_R (molli_smooth m) (molli_compact m) (hwk k) hwl y
  simp only [e1]
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : (Fin n → ℝ) → ℝ, ψ = fun y => molli m (x - y) := ⟨_, rfl⟩
  have hψs : ContDiff ℝ ∞ ψ := by
    rw [hψdef]; exact (molli_smooth m).comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := by
    rw [hψdef]; exact (molli_compact m).comp_homeomorph (Homeomorph.subLeft x)
  have hpdψ : ∀ k y, pd ψ k y = -(fderiv ℝ (molli m) (x - y) (Pi.single k 1)) := by
    intro k y
    unfold pd
    have h1 : HasFDerivAt (fun y : Fin n → ℝ => x - y) (-ContinuousLinearMap.id ℝ (Fin n → ℝ)) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 := ((hρ1.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y h1
    rw [hψdef, show (fun y => molli m (x - y)) = molli m ∘ fun y => x - y from rfl, h2.fderiv]
    simp
  have key := hΔ ψ ⟨hψs, hψc, subset_univ _⟩
  have e2 : ∀ k, pd (mconv m (g k)) k x = -∫ y, pd ψ k y * g k y := by
    intro k
    simp only [hpdψ, neg_mul, integral_neg, neg_neg]
    show fderiv ℝ (molli m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g k) x (Pi.single k 1) = _
    rw [Mollifier.fderiv_convolution_apply hρ1 (molli_compact m) (hgl k) x (Pi.single k 1)]
    rw [← integral_sub_left_eq_self (fun t => fderiv ℝ (molli m) t (Pi.single k 1) • g k (x - t))
      volume x]
    simp only [sub_sub_cancel, smul_eq_mul]
  simp only [e2]
  rw [Finset.sum_neg_distrib, key, neg_neg, hψdef]
  unfold mconv
  rw [convolution_def, ← integral_sub_left_eq_self
    (fun t => (ContinuousLinearMap.lsmul ℝ ℝ) (molli m t) (F (x - t))) volume x]
  simp only [sub_sub_cancel, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-! ### Whole-space `H²` regularity -/

/-- **Whole-space `H²` regularity** (generic): let `w ∈ L²(ℝⁿ)` have compact support, weak
gradient `g ∈ L²`, and weak Laplacian `F ∈ L²` (`Σ_k ∫ ∂_kφ g_k = -∫ φ F` for all test `φ`).
Then each `g_k` has weak derivatives `G_{kl} ∈ L²(ℝⁿ)` and `Σ_{k,l} ∫ G_{kl}² ≤ ∫ F²`. -/
theorem whole_space_H2 {w F : (Fin n → ℝ) → ℝ} {g : Fin n → (Fin n → ℝ) → ℝ}
    (hwc : HasCompactSupport w) (hw : MemLp w 2 volume) (hg : ∀ k, MemLp (g k) 2 volume)
    (hF : MemLp F 2 volume) (hwk : ∀ k, HasWeakPartialR univ k w (g k))
    (hΔ : ∀ φ, IsTest univ φ → ∑ k, ∫ x, pd φ k x * g k x = -∫ x, φ x * F x) :
    ∃ G : Fin n → Fin n → (Fin n → ℝ) → ℝ, (∀ k l, MemLp (G k l) 2 volume) ∧
      (∀ k l, HasWeakPartialR univ l (g k) (G k l)) ∧
      ∑ k, ∑ l, ∫ x, G k l x ^ 2 ≤ ∫ x, F x ^ 2 := by
  have hwl : LocallyIntegrable w volume := hw.locallyIntegrable (by norm_num)
  have hgl : ∀ k, LocallyIntegrable (g k) volume := fun k => (hg k).locallyIntegrable (by norm_num)
  set u : ℕ → (Fin n → ℝ) → ℝ := fun m => mconv m w
  have hus : ∀ m, ContDiff ℝ ∞ (u m) := fun m => contDiff_mconv m hwl
  have huc : ∀ m, HasCompactSupport (u m) := fun m => hasCompactSupport_mconv m hwc
  have hpu : ∀ m k, pd (u m) k = mconv m (g k) := fun m k =>
    funext fun y => pd_convolution_eq_R (molli_smooth m) (molli_compact m) (hwk k) hwl y
  set H : ℕ → Fin n → Fin n → (Fin n → ℝ) → ℝ := fun m k l => pd (pd (u m) k) l
  have hHs : ∀ m k l, ContDiff ℝ ∞ (H m k l) := fun m k l => contDiff_pd (contDiff_pd (hus m) k) l
  have hHc : ∀ m k l, HasCompactSupport (H m k l) := fun m k l =>
    hasCompactSupport_pd (hasCompactSupport_pd (huc m) k) l
  have hHL : ∀ m k l, MemLp (H m k l) 2 volume := fun m k l =>
    (hHs m k l).continuous.memLp_of_hasCompactSupport (hHc m k l)
  have hFm : ∀ m, MemLp (mconv m F) 2 volume := fun m => memLp_mconv m hF
  -- the Hessian identity on differences
  have hdiff : ∀ m p k l, ∫ x, (H m k l x - H p k l x) ^ 2 ≤
      ∫ x, (mconv m F x - mconv p F x) ^ 2 := by
    intro m p k l
    set v := fun x => u m x - u p x
    have hv : ContDiff ℝ ∞ v := (hus m).sub (hus p)
    have hvc : HasCompactSupport v := (huc m).sub (huc p)
    have hd1 : ∀ k, pd v k = fun x => pd (u m) k x - pd (u p) k x := fun k => funext fun x =>
      pd_sub_real ((hus m).differentiable (by simp) x) ((hus p).differentiable (by simp) x) k
    have hd2 : ∀ k l, pd (pd v k) l = fun x => H m k l x - H p k l x := by
      intro k l; rw [hd1 k]; funext x
      exact pd_sub_real ((contDiff_pd (hus m) k).differentiable (by simp) x)
        ((contDiff_pd (hus p) k).differentiable (by simp) x) l
    have hid := integral_sum_sq_hessian hv hvc
    simp only [hd2] at hid
    have hlap : ∀ x, ∑ k, (H m k k x - H p k k x) = mconv m F x - mconv p F x := by
      intro x
      rw [Finset.sum_sub_distrib]
      simp only [H]
      rw [lap_mconv m hwl hgl hwk hΔ x, lap_mconv p hwl hgl hwk hΔ x]
    simp only [hlap] at hid
    rw [← hid]
    have hnn : ∀ k l, 0 ≤ ∫ x, (H m k l x - H p k l x) ^ 2 := fun k l =>
      integral_nonneg fun x => sq_nonneg _
    calc ∫ x, (H m k l x - H p k l x) ^ 2 ≤ ∑ l', ∫ x, (H m k l' x - H p k l' x) ^ 2 :=
          Finset.single_le_sum (f := fun l' => ∫ x, (H m k l' x - H p k l' x) ^ 2)
            (fun l' _ => hnn k l') (Finset.mem_univ l)
      _ ≤ ∑ k', ∑ l', ∫ x, (H m k' l' x - H p k' l' x) ^ 2 :=
          Finset.single_le_sum (f := fun k' => ∑ l', ∫ x, (H m k' l' x - H p k' l' x) ^ 2)
            (fun k' _ => Finset.sum_nonneg fun l' _ => hnn k' l') (Finset.mem_univ k)
  -- Cauchy sequences in `L²`
  have hFconv : Tendsto (fun m => (hFm m).toLp (mconv m F)) atTop (𝓝 (hF.toLp F)) :=
    tendsto_toLp_of_eLpNorm hFm hF (tendsto_mconv hF)
  have hcauchy : ∀ k l, CauchySeq fun m => (hHL m k l).toLp (H m k l) := by
    intro k l
    refine cauchySeq_of_dist_le hFconv.cauchySeq fun m p => ?_
    rw [dist_eq_norm, dist_eq_norm, ← MemLp.toLp_sub, ← MemLp.toLp_sub]
    have h1 := norm_sq_toLp_eq ((hHL m k l).sub (hHL p k l))
    have h2 := norm_sq_toLp_eq ((hFm m).sub (hFm p))
    simp only [Pi.sub_apply] at h1 h2
    have := hdiff m p k l
    rw [← h1, ← h2] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  choose Gl hGl using fun k l => cauchySeq_tendsto_of_complete (hcauchy k l)
  refine ⟨fun k l => (Gl k l : (Fin n → ℝ) → ℝ), fun k l => Lp.memLp _, ?_, ?_⟩
  · -- weak derivatives pass to the limit
    intro k l φ hφ
    have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
    have hpφ : MemLp (pd φ l) 2 volume :=
      (continuous_pd hφ1 l).memLp_of_hasCompactSupport (hasCompactSupport_pd hφ.compact l)
    have hφL : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφ.compact
    have hcl : ∀ m, ∫ x, pd φ l x * mconv m (g k) x = -∫ x, φ x * H m k l x := by
      intro m
      rw [← hpu m k]
      exact hasWeakPartialR_of_contDiff univ ((contDiff_pd (hus m) k).of_le (by simp)) l φ hφ
    -- left side
    have hL : Tendsto (fun m => ∫ x, pd φ l x * mconv m (g k) x) atTop
        (𝓝 (∫ x, pd φ l x * g k x)) := by
      refine tendsto_integral_of_le_mul_L2 (fun m => ?_) ((continuous_pd hφ1 l).aestronglyMeasurable.mul
        (hg k).aestronglyMeasurable) hpφ (fun m => ((memLp_mconv m (hg k)).sub (hg k)).aestronglyMeasurable)
        (tendsto_mconv (hg k)) fun m => Eventually.of_forall fun x => ?_
      · exact ((continuous_pd hφ1 l).mul (contDiff_mconv m (hgl k)).continuous).integrable_of_hasCompactSupport
          (hasCompactSupport_pd hφ.compact l).mul_right
      · rw [Pi.sub_apply, ← mul_sub, norm_mul]
    -- right side
    have hR : Tendsto (fun m => ∫ x, φ x * H m k l x) atTop
        (𝓝 (∫ x, φ x * (Gl k l : (Fin n → ℝ) → ℝ) x)) := by
      have hconv : Tendsto (fun m => eLpNorm (H m k l - (Gl k l : (Fin n → ℝ) → ℝ)) 2 volume)
          atTop (𝓝 0) := by
        have := hGl k l
        rw [tendsto_iff_norm_sub_tendsto_zero] at this
        have e : ∀ m, eLpNorm (H m k l - (Gl k l : (Fin n → ℝ) → ℝ)) 2 volume =
            ENNReal.ofReal ‖(hHL m k l).toLp (H m k l) - Gl k l‖ := by
          intro m
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
          refine eLpNorm_congr_ae ?_
          filter_upwards [Lp.coeFn_sub ((hHL m k l).toLp (H m k l)) (Gl k l),
            (hHL m k l).coeFn_toLp] with x h1 h2
          rw [h1, Pi.sub_apply, Pi.sub_apply, h2]
        simp only [e]
        rw [← ENNReal.ofReal_zero]
        exact ENNReal.tendsto_ofReal this
      refine tendsto_integral_of_le_mul_L2 (fun m => ?_) (hφ.continuous.aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable _)) hφL (fun m => ((hHL m k l).sub (Lp.memLp _)).aestronglyMeasurable)
        hconv fun m => Eventually.of_forall fun x => ?_
      · exact (hφ.continuous.mul (hHs m k l).continuous).integrable_of_hasCompactSupport
          hφ.compact.mul_right
      · rw [Pi.sub_apply, ← mul_sub, norm_mul]
    exact tendsto_nhds_unique (hL.congr fun m => hcl m) hR.neg
  · -- the bound
    have hbd : ∀ m, ∑ k, ∑ l, ‖(hHL m k l).toLp (H m k l)‖ ^ 2 ≤ ‖hF.toLp F‖ ^ 2 := by
      intro m
      simp only [norm_sq_toLp_eq]
      rw [integral_sum_sq_hessian (hus m) (huc m)]
      have e : ∀ x, ∑ k, pd (pd (u m) k) k x = mconv m F x := fun x =>
        lap_mconv m hwl hgl hwk hΔ x
      simp only [e]
      rw [← norm_sq_toLp_eq (hFm m), ← norm_sq_toLp_eq hF, Lp.norm_toLp, Lp.norm_toLp]
      exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hF.eLpNorm_ne_top
        (eLpNorm_mconv_le m hF)) 2
    have hlim : Tendsto (fun m => ∑ k, ∑ l, ‖(hHL m k l).toLp (H m k l)‖ ^ 2) atTop
        (𝓝 (∑ k, ∑ l, ‖Gl k l‖ ^ 2)) :=
      tendsto_finset_sum _ fun k _ => tendsto_finset_sum _ fun l _ =>
        ((continuous_norm.pow 2).tendsto _).comp (hGl k l)
    have := le_of_tendsto' hlim hbd
    rw [norm_sq_toLp_eq hF] at this
    simp only [norm_sq_Lp_eq] at this
    exact this

/-! ### Local (interior) `H²` regularity -/

/-- A continuous compactly supported function with support in `Ω`, times an `L²(Ω)` function, is
integrable. -/
theorem integrable_mul_of_memLp_restrict {Ω : Set (Fin n → ℝ)} {ψ v : (Fin n → ℝ) → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω)
    (hv : MemLp v 2 (volume.restrict Ω)) : Integrable (fun x => ψ x * v x) volume := by
  have h1 : MemLp v 2 (volume.restrict (tsupport ψ)) := hv.mono_measure (Measure.restrict_mono hψs le_rfl)
  have : IsFiniteMeasure (volume.restrict (tsupport ψ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hψc.measure_lt_top⟩
  have h2 : IntegrableOn v (tsupport ψ) := h1.integrable (by norm_num)
  have h3 : IntegrableOn (fun x => ψ x * v x) (tsupport ψ) := h2.continuousOn_mul hψ.continuousOn hψc
  refine h3.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- A bounded continuous multiplier vanishing off `Ω` maps `L²(Ω)` into `L²(ℝⁿ)`. -/
theorem memLp_mul_of_vanish_R {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) {ψ v : (Fin n → ℝ) → ℝ}
    (hψ : Continuous ψ) (h0 : ∀ x, x ∉ Ω → ψ x = 0) {M : ℝ} (hM : ∀ x, |ψ x| ≤ M)
    (hv : MemLp v 2 (volume.restrict Ω)) : MemLp (fun x => ψ x * v x) 2 volume := by
  have hind : (fun x => ψ x * v x) = Ω.indicator (fun x => ψ x * v x) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · simp [hx, h0 x hx]
  rw [hind, memLp_indicator_iff_restrict hΩ]
  exact hv.of_le_mul (c := M) (hψ.aestronglyMeasurable.mul hv.1) (Eventually.of_forall fun x => by
    rw [norm_mul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))

/-- `∫ (ψ v)² ≤ M² ∫_Ω v²` for `|ψ| ≤ M` vanishing off `Ω`. -/
theorem integral_sq_mul_le {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) {ψ v : (Fin n → ℝ) → ℝ}
    (h0 : ∀ x, x ∉ Ω → ψ x = 0) {M : ℝ} (hM : ∀ x, |ψ x| ≤ M)
    (hv : MemLp v 2 (volume.restrict Ω)) :
    ∫ x, (ψ x * v x) ^ 2 ≤ M ^ 2 * ∫ x in Ω, v x ^ 2 := by
  have hind : (fun x => (ψ x * v x) ^ 2) = Ω.indicator (fun x => (ψ x * v x) ^ 2) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · simp [hx, h0 x hx]
  rw [hind, integral_indicator hΩ, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) ?_
    (Eventually.of_forall fun x => ?_)
  · exact (hv.integrable_sq).const_mul _
  · show (ψ x * v x) ^ 2 ≤ M ^ 2 * v x ^ 2
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by
      have := hM x
      nlinarith [abs_nonneg (ψ x), sq_abs (ψ x)]) (sq_nonneg _)

theorem isTest_pd {Ω : Set (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ} (hφ : IsTest Ω φ) (i : Fin n) :
    IsTest Ω (pd φ i) :=
  ⟨contDiff_pd hφ.smooth i, hasCompactSupport_pd hφ.compact i,
    (tsupport_pd_subset φ i).trans hφ.subset⟩

theorem isTest_vanish {Ω : Set (Fin n → ℝ)} {χ : (Fin n → ℝ) → ℝ} (hχ : IsTest Ω χ) :
    ∀ x, x ∉ Ω → χ x = 0 := fun x hx =>
  image_eq_zero_of_notMem_tsupport (fun h => hx (hχ.subset h))

theorem exists_abs_bound_of_test {Ω : Set (Fin n → ℝ)} {χ : (Fin n → ℝ) → ℝ} (hχ : IsTest Ω χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |χ x| ≤ M := by
  obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hχ.compact
  exact ⟨max C 0, le_max_right _ _, fun x => (by simpa [Real.norm_eq_abs] using hC x : |χ x| ≤ C).trans
    (le_max_left _ _)⟩

/-- Real version of the cutoff product rule. -/
theorem HasWeakPartialR.mul_test {Ω : Set (Fin n → ℝ)} {i : Fin n} {u g : (Fin n → ℝ) → ℝ}
    (h : HasWeakPartialR Ω i u g) (hu : MemLp u 2 (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω)) {χ : (Fin n → ℝ) → ℝ} (hχ : IsTest Ω χ) :
    HasWeakPartialR univ i (fun x => χ x * u x) (fun x => χ x * g x + pd χ i x * u x) := by
  rw [hasWeakPartialR_iff] at h ⊢
  have hu' : LocallyIntegrableOn (fun x => ((u x : ℝ) : ℂ)) Ω :=
    locallyIntegrableOn_of_memLp hu.ofReal
  have hg' : LocallyIntegrableOn (fun x => ((g x : ℝ) : ℂ)) Ω :=
    locallyIntegrableOn_of_memLp hg.ofReal
  have := h.mul_test hu' hg' hχ
  convert this using 2 <;> push_cast <;> ring

theorem integral_sub_add_sub {a b c d : (Fin n → ℝ) → ℝ} (ha : Integrable a) (hb : Integrable b)
    (hc : Integrable c) (hd : Integrable d) :
    ∫ x, (a x - b x + (c x - d x)) = (∫ x, a x) - (∫ x, b x) + ((∫ x, c x) - ∫ x, d x) := by
  rw [integral_add (f := fun x => a x - b x) (g := fun x => c x - d x) (ha.sub hb) (hc.sub hd),
    integral_sub ha hb, integral_sub hc hd]

theorem integral_add_two_mul_add {a : (Fin n → ℝ) → ℝ} {b c : Fin n → (Fin n → ℝ) → ℝ}
    (ha : Integrable a) (hb : ∀ k, Integrable (b k)) (hc : ∀ k, Integrable (c k)) :
    ∫ x, (a x + 2 * ∑ k, b k x + ∑ k, c k x) =
      (∫ x, a x) + 2 * ∑ k, (∫ x, b k x) + ∑ k, ∫ x, c k x := by
  have hB : Integrable (fun x => ∑ k, b k x) := integrable_finset_sum _ fun k _ => hb k
  have hC : Integrable (fun x => ∑ k, c k x) := integrable_finset_sum _ fun k _ => hc k
  rw [integral_add (f := fun x => a x + 2 * ∑ k, b k x) (g := fun x => ∑ k, c k x)
      (ha.add (hB.const_mul 2)) hC,
    integral_add (f := a) (g := fun x => 2 * ∑ k, b k x) ha (hB.const_mul 2), integral_const_mul,
    integral_finset_sum _ fun k _ => hb k, integral_finset_sum _ fun k _ => hc k]

/-- **Interior `H²` regularity** (generic): let `u ∈ L²(Ω)` with weak gradient `g ∈ L²(Ω)` solve
`Δu = f ∈ L²(Ω)` weakly (`Σ_k ∫ ∂_kφ g_k = -∫ φ f` for `φ ∈ C_c^∞(Ω)`), and let `χ ∈ C_c^∞(Ω)` be
`1` on an open set `V`.  Then the `g_k` have weak derivatives `G_{kl} ∈ L²` on `V`, with
`Σ_{k,l} ∫ G_{kl}² ≤ ∫ (χ f + 2 ∇χ·g + (Δχ) u)²`. -/
theorem interior_H2 {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {u f : (Fin n → ℝ) → ℝ}
    {g : Fin n → (Fin n → ℝ) → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (hg : ∀ k, MemLp (g k) 2 (volume.restrict Ω)) (hf : MemLp f 2 (volume.restrict Ω))
    (hweak : ∀ k, HasWeakPartialR Ω k u (g k))
    (heq : ∀ φ, IsTest Ω φ → ∑ k, ∫ x, pd φ k x * g k x = -∫ x, φ x * f x)
    {χ : (Fin n → ℝ) → ℝ} (hχ : IsTest Ω χ) {V : Set (Fin n → ℝ)} (hV : IsOpen V)
    (hχV : ∀ x ∈ V, χ x = 1) :
    ∃ G : Fin n → Fin n → (Fin n → ℝ) → ℝ, (∀ k l, MemLp (G k l) 2 volume) ∧
      (∀ k l, HasWeakPartialR V l (g k) (G k l)) ∧
      ∑ k, ∑ l, ∫ x, G k l x ^ 2 ≤
        ∫ x, (χ x * f x + 2 * ∑ k, pd χ k x * g k x + ∑ k, pd (pd χ k) k x * u x) ^ 2 := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.smooth.of_le (by simp)
  have hΩm := hΩ.measurableSet
  have hVΩ : V ⊆ Ω := fun x hx =>
    hχ.subset (subset_tsupport χ (Function.mem_support.mpr (by rw [hχV x hx]; norm_num)))
  -- bounds for the cutoff and its derivatives
  have hpdT : ∀ k, IsTest Ω (pd χ k) := fun k => isTest_pd hχ k
  have hpdpdT : ∀ k, IsTest Ω (pd (pd χ k) k) := fun k => isTest_pd (isTest_pd hχ k) k
  obtain ⟨M0, -, hM0⟩ := exists_abs_bound_of_test hχ
  choose M1 _ hM1 using fun k => exists_abs_bound_of_test (hpdT k)
  choose M2 _ hM2 using fun k => exists_abs_bound_of_test (hpdpdT k)
  -- the cut function and its data
  set w : (Fin n → ℝ) → ℝ := fun x => χ x * u x
  set gw : Fin n → (Fin n → ℝ) → ℝ := fun k x => χ x * g k x + pd χ k x * u x
  set Fw : (Fin n → ℝ) → ℝ := fun x =>
    χ x * f x + 2 * ∑ k, pd χ k x * g k x + ∑ k, pd (pd χ k) k x * u x
  have hwc : HasCompactSupport w := hχ.compact.mul_right
  have hwL : MemLp w 2 volume := memLp_mul_of_vanish_R hΩm hχ.continuous (isTest_vanish hχ) hM0 hu
  have hgwL : ∀ k, MemLp (gw k) 2 volume := fun k =>
    (memLp_mul_of_vanish_R hΩm hχ.continuous (isTest_vanish hχ) hM0 (hg k)).add
      (memLp_mul_of_vanish_R hΩm (hpdT k).continuous (isTest_vanish (hpdT k)) (hM1 k) hu)
  have hFwL : MemLp Fw 2 volume :=
    ((memLp_mul_of_vanish_R hΩm hχ.continuous (isTest_vanish hχ) hM0 hf).add
      ((memLp_finset_sum _ fun k _ => memLp_mul_of_vanish_R hΩm (hpdT k).continuous
        (isTest_vanish (hpdT k)) (hM1 k) (hg k)).const_mul 2)).add
      (memLp_finset_sum _ fun k _ => memLp_mul_of_vanish_R hΩm (hpdpdT k).continuous
        (isTest_vanish (hpdpdT k)) (hM2 k) hu)
  have hwk : ∀ k, HasWeakPartialR univ k w (gw k) := fun k =>
    (hweak k).mul_test hu (hg k) hχ
  -- the weak Laplacian of the cut function
  have hΔ : ∀ φ, IsTest univ φ → ∑ k, ∫ x, pd φ k x * gw k x = -∫ x, φ x * Fw x := by
    intro φ hφ
    have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
    have hT1 : IsTest Ω (fun x => χ x * φ x) := hχ.mul_smooth hφ.smooth
    have hT2 : ∀ k, IsTest Ω (fun x => pd χ k x * φ x) := fun k => (hpdT k).mul_smooth hφ.smooth
    have hT3 : ∀ k, IsTest Ω (fun x => pd (pd χ k) k x * φ x) := fun k =>
      (hpdpdT k).mul_smooth hφ.smooth
    have iT := fun (ψ : (Fin n → ℝ) → ℝ) (hψ : IsTest Ω ψ) (v : (Fin n → ℝ) → ℝ)
      (hv : MemLp v 2 (volume.restrict Ω)) =>
      integrable_mul_of_memLp_restrict hψ.continuous hψ.compact hψ.subset hv
    -- the per-direction identity
    have hk : ∀ k, ∫ x, pd φ k x * gw k x =
        (∫ x, pd (fun y => χ y * φ y) k x * g k x) -
          2 * (∫ x, (pd χ k x * φ x) * g k x) - ∫ x, (pd (pd χ k) k x * φ x) * u x := by
      intro k
      have hpt : ∀ x, pd φ k x * gw k x =
          pd (fun y => χ y * φ y) k x * g k x - (pd χ k x * φ x) * g k x +
            (pd (fun y => pd χ k y * φ y) k x * u x - (pd (pd χ k) k x * φ x) * u x) := by
        intro x
        rw [pd_mul hχ1 hφ1, pd_mul ((hpdT k).smooth.of_le (by simp)) hφ1]
        simp only [gw]; ring
      simp only [hpt]
      rw [integral_sub_add_sub (iT _ (isTest_pd hT1 k) _ (hg k)) (iT _ (hT2 k) _ (hg k))
        (iT _ (isTest_pd (hT2 k) k) _ hu) (iT _ (hT3 k) _ hu), hweak k _ (hT2 k)]
      ring
    simp only [hk]
    simp only [Finset.sum_sub_distrib]
    rw [heq _ hT1]
    -- the right-hand side
    have hpt2 : ∀ x, φ x * Fw x = (χ x * φ x) * f x + 2 * ∑ k, (pd χ k x * φ x) * g k x +
        ∑ k, (pd (pd χ k) k x * φ x) * u x := by
      intro x
      have s1 : ∑ k, (pd χ k x * φ x) * g k x = φ x * ∑ k, pd χ k x * g k x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      have s2 : ∑ k, (pd (pd χ k) k x * φ x) * u x = φ x * ∑ k, pd (pd χ k) k x * u x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [s1, s2]
      simp only [Fw]
      ring
    simp only [hpt2]
    rw [integral_add_two_mul_add (iT _ hT1 _ hf) (fun k => iT _ (hT2 k) _ (hg k))
      (fun k => iT _ (hT3 k) _ hu)]
    rw [← Finset.mul_sum]
    ring
  obtain ⟨G, hGL, hGw, hGb⟩ := whole_space_H2 hwc hwL hgwL hFwL hwk hΔ
  refine ⟨G, hGL, fun k l => ?_, hGb⟩
  -- on `V` the cut gradient is the gradient
  refine (hGw k l).congr_left (subset_univ _) fun x hx => ?_
  have hloc : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := Filter.eventually_of_mem (hV.mem_nhds hx) hχV
  have hpd0 : pd χ k x = 0 := by
    unfold pd; rw [hloc.fderiv_eq]; simp
  simp only [gw, hχV x hx, hpd0, one_mul, zero_mul, add_zero]

end RenewalGeometry.BallAnalysis.BallReg
