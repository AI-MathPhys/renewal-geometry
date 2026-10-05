/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoGalerkinLimit

/-!
# Kato's local existence theorem for quasilinear symmetric hyperbolic systems on `𝕋^d`

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` and
`lem:generated-physical-identification` (Einstein–Standard-Model action-closure manuscript,
`app:generated-dynamics`): the continuum limit of the spectral Galerkin scheme.

Setting: `∂_tU + Σ_i A^i(U)∂_iU = F(U)` for `U = (u_b)_{b < n}` on `[0, T] × 𝕋^d`
(`ℤ^d`-periodic fields on `ℝ^d`), smooth real symmetric `A^i(v)`, smooth `F(v)`; smooth periodic
data `U₀` with `‖U₀‖_{H^q} ≤ R₀`, `m > d/2`, `q ≥ 2m`, `q ≥ m + 2` (`d = 3`: `m = 2`, `q ≥ 4`).

* `galerkinField γ N`: the Galerkin field `U_N(t, y)` (frozen outside `[0, T]`), `galerkinDeriv`:
  its spatial derivatives; both converge uniformly on space-time (`tendstoUniformly_galerkin`).
* **`kato_local_existence`** (Kato's local existence theorem, classical form): there are `T > 0`
  and `R`, depending only on `R₀` (and `A, F, q, m, d, n`), such that every such datum has a
  solution `U` on `[0, T] × 𝕋^d` with continuous spatial derivatives `P_i = ∂_iU`, which is a
  classical solution in time, `∂_tU = F(U) - Σ_i A^i(U)∂_iU` on `[0, T]`, takes the datum at
  `t = 0`, satisfies the integral equation `U(t) = U₀ + ∫₀ᵗ G(U)`, the uniform `H^q` bound
  `Σ_k wq q k |⟨U(t), cas_k⟩|² ≤ R²` (`U ∈ L^∞_tH^q`, Fourier side), and is the uniform limit of
  the spectral Galerkin solutions of `KatoGalerkinODE.galerkin_uniform` (with their first
  derivatives), with the `L²` rate `‖U_N(t) - U(t)‖²_{L²} ≤ C (2π(N+1))^{-q}`.

Disclosed: `Σ = 𝕋^d`; smooth data (`H^q` data enter through the Fourier truncations); the
coefficients are smooth on all of `ℝ^n`; the limit is identified as a `C¹` (in `t`, and in `y`)
solution with the `H^q` bound on the Fourier side; continuity of `t ↦ U(t)` in `H^q` (strong) is
not claimed.
-/

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.KatoGalerkin

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### Uniform limits -/

/-- A uniformly Cauchy sequence of real functions converges uniformly to its pointwise limit. -/
theorem tendstoUniformly_limUnder {X : Type*} {f : ℕ → X → ℝ}
    (h : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N M, N₀ ≤ N → N₀ ≤ M → ∀ x, |f N x - f M x| ≤ ε) :
    TendstoUniformly f (fun x => limUnder atTop fun N => f N x) atTop := by
  have hconv : ∀ x, Tendsto (fun N => f N x) atTop (𝓝 (limUnder atTop fun N => f N x)) := by
    intro x
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := h (ε / 2) (by positivity)
    refine ⟨N₀, fun N hN => ?_⟩
    rw [Real.dist_eq]
    exact (hN₀ N N₀ hN le_rfl x).trans_lt (by linarith)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := h (ε / 2) (by positivity)
  refine eventually_atTop.2 ⟨N₀, fun N hN x => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  have hle : |f N x - limUnder atTop (fun N => f N x)| ≤ ε / 2 := by
    have ht : Tendsto (fun M => |f N x - f M x|) atTop
        (𝓝 |f N x - limUnder atTop fun N => f N x|) :=
      ((continuous_abs.comp (continuous_const.sub continuous_id)).tendsto _).comp (hconv x)
    exact le_of_tendsto ht (eventually_atTop.2 ⟨N₀, fun M hM => hN₀ N M hN hM x⟩)
  linarith

/-! ### Clamped Galerkin fields -/

/-- The clamp `t ↦ min(max(t, 0), T)` onto `[0, T]`. -/
def clampT {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : ℝ := (Set.projIcc 0 T hT t : ℝ)

theorem clampT_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampT hT t ∈ Set.Icc 0 T :=
  (Set.projIcc 0 T hT t).2

theorem clampT_of_mem {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) : clampT hT t = t := by
  simp [clampT, Set.projIcc_of_mem hT ht]

theorem continuous_clampT {T : ℝ} (hT : 0 ≤ T) : Continuous (clampT hT) :=
  continuous_subtype_val.comp continuous_projIcc

theorem fld_cons_eq (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) (s s' : ℝ) (y : Fin d → ℝ) :
    fld q a b (Fin.cons s y) = fld q a b (Fin.cons s' y) := by
  simp only [fld_eq, casS_cons]

theorem pd_fld_cons_eq (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) (i : Fin d) (s s' : ℝ)
    (y : Fin d → ℝ) :
    pd (fld q a b) i.succ (Fin.cons s y) = pd (fld q a b) i.succ (Fin.cons s' y) := by
  simp only [pd_fld_eq, casS_cons]

theorem continuous_fld_joint (q : ℕ) {N : ℕ} (b : Fin n) :
    Continuous fun p : GS d n N × ST d => fld q p.1 b p.2 := by
  have e : (fun p : GS d n N × ST d => fld q p.1 b p.2) = fun p =>
      ∑ k : box (d := d) N, p.1 (b, k) / Real.sqrt (wq q k.1) * casS k.1 p.2 := by
    funext p; rw [fld_eq]
  rw [e]
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((((EuclideanSpace.proj (𝕜 := ℝ) (b, k)).continuous.comp continuous_fst).div_const _)).mul
    ((contDiff_casS k.1).continuous.comp continuous_snd)

theorem continuous_pd_fld_joint (q : ℕ) {N : ℕ} (b : Fin n) (i : Fin d) :
    Continuous fun p : GS d n N × ST d => pd (fld q p.1 b) i.succ p.2 := by
  have e : (fun p : GS d n N × ST d => pd (fld q p.1 b) i.succ p.2) = fun p =>
      ∑ k : box (d := d) N, p.1 (b, k) / Real.sqrt (wq q k.1) *
        (2 * π * (k.1 i : ℝ) * casS (-k.1) p.2) := by
    funext p; rw [pd_fld_eq]
  rw [e]
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((((EuclideanSpace.proj (𝕜 := ℝ) (b, k)).continuous.comp continuous_fst).div_const _)).mul
    (continuous_const.mul ((contDiff_casS _).continuous.comp continuous_snd))

variable (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (γ : (N : ℕ) → ℝ → GS d n N)

/-- The Galerkin field `U_N(t, y)` on space-time, frozen outside `[0, T]`. -/
def galerkinField (N : ℕ) (b : Fin n) (x : ST d) : ℝ := fld q (γ N (clampT hT (x 0))) b x

/-- The spatial derivatives `∂_iU_N(t, y)` of the Galerkin field. -/
def galerkinDeriv (N : ℕ) (b : Fin n) (i : Fin d) (x : ST d) : ℝ :=
  pd (fld q (γ N (clampT hT (x 0))) b) i.succ x

/-- The limit field `U = lim U_N`. -/
def limField (b : Fin n) (x : ST d) : ℝ := limUnder atTop fun N => galerkinField q hT γ N b x

/-- The limit spatial derivatives `P_i = lim ∂_iU_N`. -/
def limDeriv (b : Fin n) (i : Fin d) (x : ST d) : ℝ :=
  limUnder atTop fun N => galerkinDeriv q hT γ N b i x

variable {q hT γ}

theorem continuous_galerkinField (hγc : ∀ N, ContinuousOn (γ N) (Set.Icc 0 T)) (N : ℕ)
    (b : Fin n) : Continuous (galerkinField q hT γ N b) := by
  have hc : Continuous fun x : ST d => γ N (clampT hT (x 0)) :=
    (hγc N).comp_continuous ((continuous_clampT hT).comp (continuous_apply 0))
      fun x => clampT_mem hT _
  exact (continuous_fld_joint q b).comp (hc.prodMk continuous_id)

theorem continuous_galerkinDeriv (hγc : ∀ N, ContinuousOn (γ N) (Set.Icc 0 T)) (N : ℕ)
    (b : Fin n) (i : Fin d) : Continuous (galerkinDeriv q hT γ N b i) := by
  have hc : Continuous fun x : ST d => γ N (clampT hT (x 0)) :=
    (hγc N).comp_continuous ((continuous_clampT hT).comp (continuous_apply 0))
      fun x => clampT_mem hT _
  exact (continuous_pd_fld_joint q b i).comp (hc.prodMk continuous_id)

theorem sshift_zero (k : Fin d → ℤ) (x : ST d) : (x + sshift k) 0 = x 0 := by
  simp [sshift]

theorem isSPeriodic_galerkinField (N : ℕ) (b : Fin n) :
    IsSPeriodic (galerkinField q hT γ N b) := fun k x => by
  simp only [galerkinField, sshift_zero]
  exact isSPeriodic_fld q _ b k x

theorem isSPeriodic_galerkinDeriv (N : ℕ) (b : Fin n) (i : Fin d) :
    IsSPeriodic (galerkinDeriv q hT γ N b i) := fun k x => by
  simp only [galerkinDeriv, sshift_zero]
  exact isSPeriodic_pd (isSPeriodic_fld q _ b) _ k x

theorem galerkinField_cons {t : ℝ} (ht : t ∈ Set.Icc 0 T) (N : ℕ) (b : Fin n) (y : Fin d → ℝ) :
    galerkinField q hT γ N b (Fin.cons t y) = fld q (γ N t) b (Fin.cons t y) := by
  simp [galerkinField, clampT_of_mem hT ht]

theorem galerkinDeriv_cons {t : ℝ} (ht : t ∈ Set.Icc 0 T) (N : ℕ) (b : Fin n) (i : Fin d)
    (y : Fin d → ℝ) :
    galerkinDeriv q hT γ N b i (Fin.cons t y) = pd (fld q (γ N t) b) i.succ (Fin.cons t y) := by
  simp [galerkinDeriv, clampT_of_mem hT ht]

/-! ### Convergence of the Galerkin fields -/

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- The hypotheses on a family of spectral Galerkin solutions on `[0, T]`: data `P_N U₀`, the
Galerkin ODE, and the uniform bound `R`. -/
structure GalerkinHyp (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (F : Fin n → (Fin n → ℝ) → ℝ) (q : ℕ) (U₀ : Fin n → ST d → ℝ) (T R : ℝ)
    (γ : (N : ℕ) → ℝ → GS d n N) : Prop where
  init : ∀ N, γ N 0 = P0 q N U₀
  deriv : ∀ N, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (γ N) (GN A F q (γ N t)) (Set.Icc 0 T) t
  bound : ∀ N, ∀ t ∈ Set.Icc 0 T, ‖γ N t‖ ≤ R

theorem GalerkinHyp.continuousOn {U₀ : Fin n → ST d → ℝ} {R : ℝ}
    (hG : GalerkinHyp A F q U₀ T R γ) (N : ℕ) : ContinuousOn (γ N) (Set.Icc 0 T) :=
  fun t ht => (hG.deriv N t ht).continuousWithinAt

section Convergence

variable {m : ℕ} (hm : (d : ℝ) / 2 < m) (hq2 : m + 2 ≤ q)
  (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
  (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ R : ℝ} (hR₀ : 0 ≤ R₀) (hR : 0 ≤ R)
  {U₀ : Fin n → ST d → ℝ} (hU : ∀ b, ContDiff ℝ ∞ (U₀ b)) (hUp : ∀ b, IsSPeriodic (U₀ b))
  (hE : energyQ q U₀ 0 ≤ R₀ ^ 2) (hG : GalerkinHyp A F q U₀ T R γ)

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
/-- Uniform Cauchy bounds on all of space-time for the clamped fields and derivatives. -/
theorem unif_cauchy_all :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N M, N₀ ≤ N → N₀ ≤ M → ∀ b x,
      |galerkinField q hT γ N b x - galerkinField q hT γ M b x| ≤ ε ∧
      ∀ i : Fin d, |galerkinDeriv q hT γ N b i x - galerkinDeriv q hT γ M b i x| ≤ ε := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := galerkin_unif_cauchy hm hq2 hA hsym hF hR₀ hR hT U₀ hU hUp hE γ hG.init
    hG.deriv hG.bound ε hε
  refine ⟨N₀, fun N M hN hM b x => ?_⟩
  rcases le_total N M with h | h
  · exact hN₀ N M hN h _ (clampT_mem hT _) b x
  · obtain ⟨h1, h2⟩ := hN₀ M N hM h _ (clampT_mem hT _) b x
    refine ⟨?_, fun i => ?_⟩
    · rw [abs_sub_comm]; exact h1
    · rw [abs_sub_comm]; exact h2 i

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
theorem tendstoUniformly_galerkinField (b : Fin n) :
    TendstoUniformly (fun N => galerkinField q hT γ N b) (limField q hT γ b) atTop :=
  tendstoUniformly_limUnder fun ε hε => by
    obtain ⟨N₀, h⟩ := unif_cauchy_all hm hq2 hA hsym hF hR₀ hR hU hUp hE hG ε hε
    exact ⟨N₀, fun N M hN hM x => (h N M hN hM b x).1⟩

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
theorem tendstoUniformly_galerkinDeriv (b : Fin n) (i : Fin d) :
    TendstoUniformly (fun N => galerkinDeriv q hT γ N b i) (limDeriv q hT γ b i) atTop :=
  tendstoUniformly_limUnder fun ε hε => by
    obtain ⟨N₀, h⟩ := unif_cauchy_all hm hq2 hA hsym hF hR₀ hR hU hUp hE hG ε hε
    exact ⟨N₀, fun N M hN hM x => (h N M hN hM b x).2 i⟩

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
theorem continuous_limField (b : Fin n) : Continuous (limField q hT γ b) :=
  (tendstoUniformly_galerkinField hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b).continuous
    (Frequently.of_forall fun N => continuous_galerkinField hG.continuousOn N b)

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
theorem continuous_limDeriv (b : Fin n) (i : Fin d) : Continuous (limDeriv q hT γ b i) :=
  (tendstoUniformly_galerkinDeriv hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b i).continuous
    (Frequently.of_forall fun N => continuous_galerkinDeriv hG.continuousOn N b i)

theorem isSPeriodic_limField (b : Fin n) : IsSPeriodic (limField q hT γ b) := fun k x => by
  simp only [limField, isSPeriodic_galerkinField _ b k x]

theorem isSPeriodic_limDeriv (b : Fin n) (i : Fin d) : IsSPeriodic (limDeriv q hT γ b i) :=
  fun k x => by simp only [limDeriv, isSPeriodic_galerkinDeriv _ b i k x]

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
/-- **The limit is spatially differentiable, with derivatives the limits of the Galerkin
derivatives**: `∂_i U(x) = P_i(x)` along every spatial line. -/
theorem hasDerivAt_limField (b : Fin n) (i : Fin d) (x : ST d) :
    HasDerivAt (fun s : ℝ => limField q hT γ b (x + s • ev i.succ)) (limDeriv q hT γ b i x) 0 := by
  have hline : ∀ s : ℝ, (x + s • ev i.succ) 0 = x 0 := fun s => by
    simp [Pi.single_apply, Fin.succ_ne_zero]
  have h := hasDerivAt_of_tendstoUniformly (l := atTop)
    (f := fun N (s : ℝ) => galerkinField q hT γ N b (x + s • ev i.succ))
    (f' := fun N (s : ℝ) => galerkinDeriv q hT γ N b i (x + s • ev i.succ))
    (g := fun (s : ℝ) => limField q hT γ b (x + s • ev i.succ))
    (g' := fun (s : ℝ) => limDeriv q hT γ b i (x + s • ev i.succ))
    ((tendstoUniformly_galerkinDeriv hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b i).comp
      fun s => x + s • ev i.succ)
    (Eventually.of_forall fun N s => by
      simp only [galerkinField, galerkinDeriv, hline]
      exact hasDerivAt_line i.succ ((contDiff_fld q _ b).differentiable (by simp) _))
    (fun s => (tendstoUniformly_galerkinField hm hq2 hA hsym hF hR₀ hR hU hUp hE hG
      b).tendsto_at _) 0
  simpa using h

end Convergence

/-! ### Generic facts on coefficients and integrals -/

/-- Coefficients are `2`-Lipschitz for the sup norm. -/
theorem abs_coef_sub_le {f g : ST d → ℝ} (hf : Continuous f) (hg : Continuous g) {η : ℝ}
    (h : ∀ x, |f x - g x| ≤ η) (t : ℝ) (k : Fin d → ℤ) : |coef f t k - coef g t k| ≤ 2 * η := by
  rw [← coef_sub hf hg]
  unfold coef
  refine abs_sint_le (fun x => ?_) t
  rw [abs_mul]
  have h0 : 0 ≤ η := (abs_nonneg _).trans (h x)
  exact mul_le_mul (abs_casS_le k x) (h x) (abs_nonneg _) (by norm_num)

theorem continuous_coef {f : ST d → ℝ} (hf : Continuous f) (k : Fin d → ℤ) :
    Continuous fun t => coef f t k :=
  continuous_sliceInt (f := fun x => casS k x * f x) ((contDiff_casS k).continuous.mul hf)

/-- Coefficients of uniformly convergent sequences converge, uniformly in time. -/
theorem tendsto_coef_unif {f : ℕ → ST d → ℝ} {g : ST d → ℝ} (hf : ∀ N, Continuous (f N))
    (hg : Continuous g) (h : TendstoUniformly f g atTop) (k : Fin d → ℤ) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ t, |coef (f N) t k - coef g t k| ≤ ε := by
  intro ε hε
  rw [Metric.tendstoUniformly_iff] at h
  filter_upwards [h (ε / 2) (by positivity)] with N hN t
  refine (abs_coef_sub_le (hf N) hg (η := ε / 2) (fun x => ?_) t k).trans (by linarith)
  have := (hN x).le
  rwa [Real.dist_eq, abs_sub_comm] at this

/-- **Fubini on `[0, t] × [0,1]^d`** for a continuous integrand. -/
theorem integral_cube_intervalIntegral_swap {g : ℝ × (Fin d → ℝ) → ℝ} (hg : Continuous g)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, ∫ s in (0)..t, g (s, y) =
      ∫ s in (0)..t, ∫ y in Icc (0 : Fin d → ℝ) 1, g (s, y) := by
  simp only [intervalIntegral.integral_of_le ht]
  have hint : Integrable (Function.uncurry fun (y : Fin d → ℝ) (s : ℝ) => g (s, y))
      ((volume.restrict (Icc (0 : Fin d → ℝ) 1)).prod (volume.restrict (Ioc 0 t))) := by
    rw [Measure.prod_restrict]
    have hc : Continuous (Function.uncurry fun (y : Fin d → ℝ) (s : ℝ) => g (s, y)) :=
      hg.comp (continuous_snd.prodMk continuous_fst)
    have h1 : IntegrableOn (Function.uncurry fun (y : Fin d → ℝ) (s : ℝ) => g (s, y))
        (Icc (0 : Fin d → ℝ) 1 ×ˢ Icc 0 t) (volume.prod volume) :=
      hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact h1.mono_set (Set.prod_mono le_rfl Ioc_subset_Icc_self)
  exact integral_integral_swap hint

/-- **Completeness, spatial form**: a continuous `ℤ^d`-periodic `w` on `ℝ^d` whose `cas`
coefficients vanish is zero. -/
theorem eq_zero_of_coef_eq_zero' {w : (Fin d → ℝ) → ℝ} (hw : Continuous w)
    (hp : ∀ k y, w (y + zvec k) = w y)
    (h : ∀ k : Fin d → ℤ, ∫ y in Icc (0 : Fin d → ℝ) 1, casS k (Fin.cons 0 y) * w y = 0)
    (y : Fin d → ℝ) : w y = 0 := by
  set f : ST d → ℝ := fun x => w (Fin.tail x) with hf
  have hfc : Continuous f := hw.comp (continuous_pi fun i => continuous_apply _)
  have hfp : IsSPeriodic f := fun k x => by
    simp only [hf]
    have : Fin.tail (x + sshift k) = Fin.tail x + zvec k := by
      funext i; simp [Fin.tail, sshift]
    rw [this, hp]
  have := eq_zero_of_coef_eq_zero hfc hfp 0 (fun k => by
    unfold coef sint; simpa [hf] using h k) y
  simpa [hf] using this

theorem exists_mem_box (k : Fin d → ℤ) : ∃ N : ℕ, k ∈ box N := by
  refine ⟨∑ i, (k i).natAbs, mem_box.2 fun i => ?_⟩
  have h1 : (k i).natAbs ≤ ∑ i, (k i).natAbs :=
    Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2 : |k i| = ((k i).natAbs : ℤ) := Int.abs_eq_natAbs (k i)
  rw [h2]; exact_mod_cast h1

theorem genG_fld_cons_eq (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) (s s' : ℝ)
    (y : Fin d → ℝ) :
    genG A F (fld q a) b (Fin.cons s y) = genG A F (fld q a) b (Fin.cons s' y) := by
  simp only [genG, compF, fld_cons_eq q a _ s s' y, pd_fld_cons_eq q a _ _ s s' y]

/-! ### The limit equation -/

variable (A F q hT γ) in
/-- The generator `G(U) = F(U) - Σ_i A^i(U) P_i` of the limit field. -/
def limGen (b : Fin n) (x : ST d) : ℝ :=
  F b (fun c => limField q hT γ c x) -
    ∑ i, ∑ b', A i b b' (fun c => limField q hT γ c x) * limDeriv q hT γ b' i x

variable (A F q hT γ) in
/-- The generator evaluated on the clamped Galerkin field. -/
def galGen (N : ℕ) (b : Fin n) (x : ST d) : ℝ :=
  F b (fun c => galerkinField q hT γ N c x) -
    ∑ i, ∑ b', A i b b' (fun c => galerkinField q hT γ N c x) * galerkinDeriv q hT γ N b' i x

theorem galGen_cons {t : ℝ} (ht : t ∈ Set.Icc 0 T) (N : ℕ) (b : Fin n) (y : Fin d → ℝ) :
    galGen (A := A) (F := F) q hT γ N b (Fin.cons t y) = genG A F (fld q (γ N t)) b (Fin.cons t y) := by
  simp only [galGen, genG, compF, galerkinField_cons ht, galerkinDeriv_cons ht]

section Limit

variable {m : ℕ} (hm : (d : ℝ) / 2 < m) (hq2 : m + 2 ≤ q)
  (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
  (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ R : ℝ} (hR₀ : 0 ≤ R₀) (hR : 0 ≤ R)
  {U₀ : Fin n → ST d → ℝ} (hU : ∀ b, ContDiff ℝ ∞ (U₀ b)) (hUp : ∀ b, IsSPeriodic (U₀ b))
  (hE : energyQ q U₀ 0 ≤ R₀ ^ 2) (hG : GalerkinHyp A F q U₀ T R γ)

include hm hq2 hR hG in
/-- Uniform bounds for the Galerkin fields, their derivatives and the limits. -/
theorem exists_unif_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N b x, |galerkinField q hT γ N b x| ≤ B ∧
      ∀ i : Fin d, |galerkinDeriv q hT γ N b i x| ≤ B := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  refine ⟨Real.sqrt CS * R, by positivity, fun N b x => ?_⟩
  have hn := hG.bound N _ (clampT_mem hT (x 0))
  have h := abs_fld_le (by omega : m + 1 ≤ q) hCS hsup (γ N (clampT hT (x 0))) b x
  refine ⟨h.1.trans (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)), fun i =>
    (h.2 i).trans (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))⟩

theorem abs_le_of_tendsto_abs {u : ℕ → ℝ} {l B : ℝ} (h : Tendsto u atTop (𝓝 l))
    (hb : ∀ N, |u N| ≤ B) : |l| ≤ B :=
  le_of_tendsto ((continuous_abs.tendsto _).comp h) (Eventually.of_forall hb)

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
theorem continuous_galGen (N : ℕ) (b : Fin n) : Continuous (galGen (A := A) (F := F) q hT γ N b) := by
  have hc : ∀ c, Continuous (galerkinField q hT γ N c) := fun c =>
    continuous_galerkinField hG.continuousOn N c
  unfold galGen
  exact ((hF b).continuous.comp (continuous_pi hc)).sub (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun b' _ => ((hA i b b').continuous.comp (continuous_pi hc)).mul
      (continuous_galerkinDeriv hG.continuousOn N b' i))

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
theorem continuous_limGen (b : Fin n) : Continuous (limGen (A := A) (F := F) q hT γ b) := by
  have hc : ∀ c, Continuous (limField q hT γ c) := fun c =>
    continuous_limField (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG c
  unfold limGen
  exact ((hF b).continuous.comp (continuous_pi hc)).sub (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun b' _ => ((hA i b b').continuous.comp (continuous_pi hc)).mul
      (continuous_limDeriv hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b' i))

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
/-- **The generator converges uniformly**: `G(U_N) → G(U)` on space-time. -/
theorem tendstoUniformly_galGen (b : Fin n) :
    TendstoUniformly (fun N => galGen (A := A) (F := F) q hT γ N b) (limGen (A := A) (F := F) q hT γ b) atTop := by
  obtain ⟨B, hB0, hB⟩ := exists_unif_bound (hT := hT) hm hq2 hR hG
  have hU1 := tendstoUniformly_galerkinField (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG
  have hP1 := tendstoUniformly_galerkinDeriv (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG
  have hlimB : ∀ c x, |limField q hT γ c x| ≤ B := fun c x =>
    abs_le_of_tendsto_abs ((hU1 c).tendsto_at x) fun N => (hB N c x).1
  have hlimP : ∀ c i x, |limDeriv q hT γ c i x| ≤ B := fun c i x =>
    abs_le_of_tendsto_abs ((hP1 c i).tendsto_at x) fun N => (hB N c x).2 i
  set Φ : (Fin n ⊕ (Fin d × Fin n × Fin n)) → (Fin n → ℝ) → ℝ :=
    fun k => Sum.elim (fun a => F a) (fun p => A p.1 p.2.1 p.2.2) k with hΦ
  have hΦs : ∀ k, ContDiff ℝ ∞ (Φ k) := by
    intro k; cases k with
    | inl a => exact hF a
    | inr p => exact hA p.1 p.2.1 p.2.2
  obtain ⟨M, hM0, hM⟩ := exists_coeff_bounds hΦs B
  set Kc := M + d * n * (M + M * B) + 1 with hKc
  have hKc0 : 0 < Kc := by positivity
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  set η := ε / (2 * Kc) with hη
  have hη0 : 0 < η := by positivity
  have hev : ∀ᶠ N in atTop, ∀ c x, |galerkinField q hT γ N c x - limField q hT γ c x| ≤ η ∧
      ∀ i, |galerkinDeriv q hT γ N c i x - limDeriv q hT γ c i x| ≤ η := by
    have h1 : ∀ c, ∀ᶠ N in atTop, ∀ x, |galerkinField q hT γ N c x - limField q hT γ c x| ≤ η :=
      fun c => (Metric.tendstoUniformly_iff.1 (hU1 c) η hη0).mono fun N hN x => by
        have := (hN x).le; rwa [Real.dist_eq, abs_sub_comm] at this
    have h2 : ∀ c i, ∀ᶠ N in atTop, ∀ x,
        |galerkinDeriv q hT γ N c i x - limDeriv q hT γ c i x| ≤ η :=
      fun c i => (Metric.tendstoUniformly_iff.1 (hP1 c i) η hη0).mono fun N hN x => by
        have := (hN x).le; rwa [Real.dist_eq, abs_sub_comm] at this
    have h1' := Filter.eventually_all.2 h1
    have h2' := Filter.eventually_all.2 fun c => Filter.eventually_all.2 (h2 c)
    filter_upwards [h1', h2'] with N hN1 hN2 c x
    exact ⟨hN1 c x, fun i => hN2 c i x⟩
  filter_upwards [hev] with N hN x
  rw [Real.dist_eq, abs_sub_comm]
  have hux : ‖(fun c => galerkinField q hT γ N c x)‖ ≤ B :=
    norm_le_of_abs_le hB0 fun c => (hB N c x).1
  have hvx : ‖(fun c => limField q hT γ c x)‖ ≤ B := norm_le_of_abs_le hB0 fun c => hlimB c x
  have hdiff : ‖(fun c => galerkinField q hT γ N c x) - (fun c => limField q hT γ c x)‖ ≤ η :=
    norm_le_of_abs_le hη0.le fun c => (hN c x).1
  unfold galGen limGen
  have e : ∀ (a1 a2 : ℝ) (s1 s2 : ℝ), (a1 - s1) - (a2 - s2) = (a1 - a2) - (s1 - s2) :=
    fun _ _ _ _ => by ring
  rw [e, ← Finset.sum_sub_distrib]
  refine lt_of_le_of_lt (abs_sub _ _) ?_
  have hF' : |F b (fun c => galerkinField q hT γ N c x) - F b (fun c => limField q hT γ c x)|
      ≤ M * η :=
    ((hM (Sum.inl b) _ _ hux hvx).2.2).trans (mul_le_mul_of_nonneg_left hdiff hM0)
  have hS : |∑ i, ((∑ b', A i b b' (fun c => galerkinField q hT γ N c x) *
      galerkinDeriv q hT γ N b' i x) - ∑ b', A i b b' (fun c => limField q hT γ c x) *
        limDeriv q hT γ b' i x)| ≤ d * n * (M + M * B) * η := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |(∑ b', A i b b' (fun c => galerkinField q hT γ N c x) *
          galerkinDeriv q hT γ N b' i x) - ∑ b', A i b b' (fun c => limField q hT γ c x) *
            limDeriv q hT γ b' i x|
        ≤ ∑ _i : Fin d, n * ((M + M * B) * η) := Finset.sum_le_sum fun i _ => by
          rw [← Finset.sum_sub_distrib]
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ b', |A i b b' (fun c => galerkinField q hT γ N c x) *
                galerkinDeriv q hT γ N b' i x - A i b b' (fun c => limField q hT γ c x) *
                  limDeriv q hT γ b' i x|
              ≤ ∑ _b' : Fin n, (M + M * B) * η := Finset.sum_le_sum fun b' _ => by
                have e2 : A i b b' (fun c => galerkinField q hT γ N c x) *
                    galerkinDeriv q hT γ N b' i x - A i b b' (fun c => limField q hT γ c x) *
                      limDeriv q hT γ b' i x =
                    A i b b' (fun c => galerkinField q hT γ N c x) *
                      (galerkinDeriv q hT γ N b' i x - limDeriv q hT γ b' i x) +
                    (A i b b' (fun c => galerkinField q hT γ N c x) -
                      A i b b' (fun c => limField q hT γ c x)) * limDeriv q hT γ b' i x := by
                  ring
                rw [e2]
                refine (abs_add_le _ _).trans ?_
                rw [abs_mul, abs_mul]
                have a1 : |A i b b' (fun c => galerkinField q hT γ N c x)| ≤ M :=
                  (hM (Sum.inr (i, b, b')) _ _ hux hvx).1
                have a2 : |A i b b' (fun c => galerkinField q hT γ N c x) -
                    A i b b' (fun c => limField q hT γ c x)| ≤ M * ‖(fun c => galerkinField q hT γ N c x) -
                      (fun c => limField q hT γ c x)‖ :=
                  (hM (Sum.inr (i, b, b')) _ _ hux hvx).2.2
                have a3 : |A i b b' (fun c => galerkinField q hT γ N c x) -
                    A i b b' (fun c => limField q hT γ c x)| ≤ M * η :=
                  a2.trans (mul_le_mul_of_nonneg_left hdiff hM0)
                have t1 := mul_le_mul a1 ((hN b' x).2 i) (abs_nonneg _) hM0
                have t2 := mul_le_mul a3 (hlimP b' i x) (abs_nonneg _) (by positivity)
                nlinarith
            _ = n * ((M + M * B) * η) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = d * n * (M + M * B) * η := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hfin : M * η + d * n * (M + M * B) * η < ε := by
    have : M * η + d * n * (M + M * B) * η = (Kc - 1) * η := by rw [hKc]; ring
    rw [this, hη]
    rw [show (Kc - 1) * (ε / (2 * Kc)) = ε * (Kc - 1) / (2 * Kc) by ring,
      div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
/-- **The Fourier form of the limit equation**: for `t ∈ [0, T]` and every mode,
`⟨U(t), cas_k⟩ = ⟨U₀, cas_k⟩ + ∫₀ᵗ ⟨G(U)(s), cas_k⟩ ds`. -/
theorem coef_limField_eq {t : ℝ} (ht : t ∈ Set.Icc 0 T) (b : Fin n) (k : Fin d → ℤ) :
    coef (limField q hT γ b) t k =
      coef (U₀ b) 0 k + ∫ s in (0)..t, coef (limGen (A := A) (F := F) q hT γ b) s k := by
  obtain ⟨N₀, hN₀⟩ := exists_mem_box k
  have hU1 := tendstoUniformly_galerkinField (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b
  have hG1 := tendstoUniformly_galGen (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b
  have hcU := continuous_limField (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b
  have hcG := continuous_limGen (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b
  have hcVN : ∀ N, Continuous (galerkinField q hT γ N b) := fun N =>
    continuous_galerkinField hG.continuousOn N b
  have hcGN : ∀ N, Continuous (galGen (A := A) (F := F) q hT γ N b) := fun N =>
    continuous_galGen (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG N b
  -- the Galerkin identity
  have hid : ∀ N, N₀ ≤ N → coef (galerkinField q hT γ N b) t k =
      coef (U₀ b) 0 k + ∫ s in (0)..t, coef (galGen (A := A) (F := F) q hT γ N b) s k := by
    intro N hN
    have hk : k ∈ box N := box_mono hN hN₀
    have e1 : coef (galerkinField q hT γ N b) t k = cf q (γ N t) b k := by
      have : coef (galerkinField q hT γ N b) t k = coef (fld q (γ N t) b) t k := by
        unfold coef sint
        exact integral_congr_ae (Eventually.of_forall fun y => by
          simp only [galerkinField_cons ht])
      rw [this, fld, coef_tfs_of_mem _ _ hk]
    have e0 : cf q (γ N 0) b k = coef (U₀ b) 0 k := by
      rw [hG.init N, cf_P0, if_pos hk]
    have hcf' : ContinuousOn (fun s => coef (genG A F (fld q (γ N s)) b) 0 k) (Set.Icc 0 T) := by
      have e : (fun s => coef (genG A F (fld q (γ N s)) b) 0 k) = fun s =>
          (EuclideanSpace.proj (𝕜 := ℝ) ((b, ⟨k, hk⟩) : Fin n × box (d := d) N))
            (GN A F q (γ N s)) / Real.sqrt (wq q k) := by
        funext s
        show _ = GN A F q (γ N s) (b, ⟨k, hk⟩) / Real.sqrt (wq q k)
        rw [GN_apply]; field_simp [sqrt_wq_ne q k]
      rw [e]
      exact ((((EuclideanSpace.proj _).continuous.comp
        (contDiff_GN hA hF q N).continuous).comp_continuousOn (hG.continuousOn N)).div_const _)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (f := fun s => cf q (γ N s) b k) (f' := fun s => coef (genG A F (fld q (γ N s)) b) 0 k)
      (fun s hs => ((hasDerivWithinAt_cf (hG.deriv N s ⟨hs.1, hs.2.trans ht.2⟩) b
        hk).continuousWithinAt).mono (Icc_subset_Icc le_rfl ht.2))
      (fun s hs => ((hasDerivWithinAt_cf (hG.deriv N s ⟨hs.1.le, hs.2.le.trans ht.2⟩) b
        hk).hasDerivAt (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))).hasDerivWithinAt)
      ((hcf'.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
    have hcongr : ∫ s in (0)..t, coef (genG A F (fld q (γ N s)) b) 0 k =
        ∫ s in (0)..t, coef (galGen (A := A) (F := F) q hT γ N b) s k := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le ht.1] at hs
      have hs' : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
      unfold coef sint
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [galGen_cons hs', casS_cons, genG_fld_cons_eq q (γ N s) b 0 s y]
    rw [e1, ← hcongr, hftc, e0]; ring
  -- pass to the limit
  have hlimL : Tendsto (fun N => coef (galerkinField q hT γ N b) t k) atTop
      (𝓝 (coef (limField q hT γ b) t k)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (tendsto_coef_unif hcVN hcU hU1 k (ε / 2)
      (by positivity))
    exact ⟨N₁, fun N hN => by rw [Real.dist_eq]; exact (hN₁ N hN t).trans_lt (by linarith)⟩
  have hlimR : Tendsto (fun N => coef (U₀ b) 0 k + ∫ s in (0)..t, coef (galGen (A := A) (F := F) q hT γ N b) s k)
      atTop (𝓝 (coef (U₀ b) 0 k + ∫ s in (0)..t, coef (limGen (A := A) (F := F) q hT γ b) s k)) := by
    refine tendsto_const_nhds.add ?_
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (tendsto_coef_unif hcGN hcG hG1 k (ε / (2 * (t + 1)))
      (by have := ht.1; positivity))
    refine ⟨N₁, fun N hN => ?_⟩
    rw [Real.dist_eq, ← intervalIntegral.integral_sub
      ((continuous_coef (hcGN N) k).intervalIntegrable _ _)
      ((continuous_coef hcG k).intervalIntegrable _ _)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (f := fun s => coef (galGen (A := A) (F := F) q hT γ N b) s k - coef (limGen (A := A) (F := F) q hT γ b) s k)
      (C := ε / (2 * (t + 1))) fun s _ => by rw [Real.norm_eq_abs]; exact hN₁ N hN s
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hb
    refine hb.trans_lt ?_
    have ht0 := ht.1
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  exact tendsto_nhds_unique hlimL (by
    refine hlimR.congr' (eventually_atTop.2 ⟨N₀, fun N hN => (hid N hN).symm⟩))

theorem cons_zvec (s : ℝ) (y : Fin d → ℝ) (k : Fin d → ℤ) :
    (Fin.cons s (y + zvec k) : ST d) = Fin.cons s y + sshift k := by
  rw [sshift, cons_add_cons, add_zero]

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
/-- **The limit takes the initial datum.** -/
theorem limField_zero (b : Fin n) (y : Fin d → ℝ) :
    limField q hT γ b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y) := by
  have hcU := continuous_limField (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b
  have h := eq_zero_of_coef_eq_zero' (w := fun y => limField q hT γ b (Fin.cons 0 y) -
      U₀ b (Fin.cons 0 y))
    ((hcU.comp (continuous_cons 0)).sub ((hU b).continuous.comp (continuous_cons 0)))
    (fun k y => by
      beta_reduce
      rw [cons_zvec, isSPeriodic_limField b k, hUp b k])
    (fun k => by
      have h0 := coef_limField_eq (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG
        ⟨le_rfl, hT⟩ b k
      simp only [intervalIntegral.integral_same, add_zero] at h0
      have e : ∫ y in Icc (0 : Fin d → ℝ) 1, casS k (Fin.cons 0 y) *
          (limField q hT γ b (Fin.cons 0 y) - U₀ b (Fin.cons 0 y)) =
          coef (limField q hT γ b) 0 k - coef (U₀ b) 0 k := by
        have := coef_sub (hcU) (hU b).continuous 0 k
        unfold coef sint at this ⊢
        rw [← this]
      rw [e, h0, sub_self]) y
  exact sub_eq_zero.1 h

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
/-- **The limit solves the integral equation** `U(t) = U₀ + ∫₀ᵗ G(U)(s) ds` on `[0, T]`. -/
theorem limField_integral_eq {t : ℝ} (ht : t ∈ Set.Icc 0 T) (b : Fin n) (y : Fin d → ℝ) :
    limField q hT γ b (Fin.cons t y) =
      U₀ b (Fin.cons 0 y) + ∫ s in (0)..t, limGen (A := A) (F := F) q hT γ b (Fin.cons s y) := by
  have hcU := continuous_limField (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b
  have hcG := continuous_limGen (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b
  have hcGy : Continuous fun p : ℝ × (Fin d → ℝ) =>
      limGen (A := A) (F := F) q hT γ b (Fin.cons p.1 p.2) := hcG.comp continuous_cons2
  have hint : Continuous fun y : Fin d → ℝ =>
      ∫ s in (0)..t, limGen (A := A) (F := F) q hT γ b (Fin.cons s y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y s => limGen (A := A) (F := F) q hT γ b (Fin.cons s y))
      (hcG.comp (continuous_cons2.comp (continuous_snd.prodMk continuous_fst))) 0 t
  have h := eq_zero_of_coef_eq_zero' (w := fun y => limField q hT γ b (Fin.cons t y) -
      U₀ b (Fin.cons 0 y) - ∫ s in (0)..t, limGen (A := A) (F := F) q hT γ b (Fin.cons s y))
    (((hcU.comp (continuous_cons t)).sub ((hU b).continuous.comp (continuous_cons 0))).sub hint)
    (fun k y => by
      beta_reduce
      rw [cons_zvec, isSPeriodic_limField b k, cons_zvec, hUp b k]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [cons_zvec]
      have hp : IsSPeriodic (limGen (A := A) (F := F) q hT γ b) := fun k x => by
        simp only [limGen, isSPeriodic_limField _ k x, isSPeriodic_limDeriv _ _ k x]
      exact hp k _)
    (fun k => by
      have h0 := coef_limField_eq (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG ht b k
      have hcas : ∀ s y, casS k (Fin.cons s y : ST d) = casS k (Fin.cons 0 y) := fun s y => by
        rw [casS_cons, casS_cons]
      have i1 : IntegrableOn (fun y : Fin d → ℝ => casS k (Fin.cons 0 y) *
          limField q hT γ b (Fin.cons t y)) (Icc 0 1) :=
        integrableOn_cube_of_continuousOn
          (((contDiff_casS k).continuous.comp (continuous_cons 0)).mul
            (hcU.comp (continuous_cons t))).continuousOn
      have i2 : IntegrableOn (fun y : Fin d → ℝ => casS k (Fin.cons 0 y) *
          U₀ b (Fin.cons 0 y)) (Icc 0 1) :=
        integrableOn_cube_of_continuousOn
          (((contDiff_casS k).continuous.comp (continuous_cons 0)).mul
            ((hU b).continuous.comp (continuous_cons 0))).continuousOn
      have i3 : IntegrableOn (fun y : Fin d → ℝ => casS k (Fin.cons 0 y) *
          ∫ s in (0)..t, limGen (A := A) (F := F) q hT γ b (Fin.cons s y)) (Icc 0 1) :=
        integrableOn_cube_of_continuousOn
          (((contDiff_casS k).continuous.comp (continuous_cons 0)).mul hint).continuousOn
      have e1 : (fun y : Fin d → ℝ => casS k (Fin.cons 0 y) *
          (limField q hT γ b (Fin.cons t y) - U₀ b (Fin.cons 0 y) -
            ∫ s in (0)..t, limGen (A := A) (F := F) q hT γ b (Fin.cons s y))) =
          fun y => casS k (Fin.cons 0 y) * limField q hT γ b (Fin.cons t y) -
            casS k (Fin.cons 0 y) * U₀ b (Fin.cons 0 y) -
            casS k (Fin.cons 0 y) * ∫ s in (0)..t,
              limGen (A := A) (F := F) q hT γ b (Fin.cons s y) := by
        funext y; ring
      have i12 : IntegrableOn (fun y : Fin d → ℝ => casS k (Fin.cons 0 y) *
          limField q hT γ b (Fin.cons t y) - casS k (Fin.cons 0 y) * U₀ b (Fin.cons 0 y))
          (Icc 0 1) := i1.sub i2
      rw [e1, integral_sub i12 i3, integral_sub i1 i2]
      have c1 : ∫ y in Icc (0 : Fin d → ℝ) 1, casS k (Fin.cons 0 y) *
          limField q hT γ b (Fin.cons t y) = coef (limField q hT γ b) t k := by
        unfold coef sint
        exact integral_congr_ae (Eventually.of_forall fun y => by simp only [hcas])
      have c2 : ∫ y in Icc (0 : Fin d → ℝ) 1, casS k (Fin.cons 0 y) * U₀ b (Fin.cons 0 y) =
          coef (U₀ b) 0 k := rfl
      have c3 : ∫ y in Icc (0 : Fin d → ℝ) 1, casS k (Fin.cons 0 y) *
          ∫ s in (0)..t, limGen (A := A) (F := F) q hT γ b (Fin.cons s y) =
          ∫ s in (0)..t, coef (limGen (A := A) (F := F) q hT γ b) s k := by
        have e : ∀ y : Fin d → ℝ, casS k (Fin.cons 0 y) *
            ∫ s in (0)..t, limGen (A := A) (F := F) q hT γ b (Fin.cons s y) =
            ∫ s in (0)..t, casS k (Fin.cons s y) *
              limGen (A := A) (F := F) q hT γ b (Fin.cons s y) := by
          intro y
          rw [← intervalIntegral.integral_const_mul]
          exact intervalIntegral.integral_congr fun s _ => by simp only [hcas]
        simp_rw [e]
        rw [integral_cube_intervalIntegral_swap (g := fun p : ℝ × (Fin d → ℝ) =>
          casS k (Fin.cons p.1 p.2) * limGen (A := A) (F := F) q hT γ b (Fin.cons p.1 p.2))
          (((contDiff_casS k).continuous.comp continuous_cons2).mul hcGy) ht.1]
        rfl
      rw [c1, c2, c3, h0]; ring) y
  have := sub_eq_zero.1 h
  linarith

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
/-- **The limit is a classical solution in time**: on `[0, T]`,
`∂_tU = G(U) = F(U) - Σ_i A^i(U) ∂_iU`. -/
theorem hasDerivWithinAt_limField {t : ℝ} (ht : t ∈ Set.Icc 0 T) (b : Fin n)
    (y : Fin d → ℝ) :
    HasDerivWithinAt (fun s => limField q hT γ b (Fin.cons s y))
      (limGen (A := A) (F := F) q hT γ b (Fin.cons t y)) (Set.Icc 0 T) t := by
  have hcG := continuous_limGen (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b
  have hcs : Continuous fun s : ℝ => limGen (A := A) (F := F) q hT γ b (Fin.cons s y) :=
    hcG.comp (continuous_cons2.comp (continuous_id.prodMk continuous_const))
  have hd := (hcs.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hd' := (hd.const_add (U₀ b (Fin.cons 0 y))).hasDerivWithinAt (s := Set.Icc 0 T)
  refine hd'.congr (fun s hs => ?_) ?_
  · exact limField_integral_eq (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG hs b y
  · exact limField_integral_eq (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG ht b y

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
/-- **The uniform `H^q` bound of the limit** (Fatou, Fourier side): for `t ∈ [0, T]` and every
finite mode set `S`, `Σ_b Σ_{k ∈ S} wq q k ⟨U_b(t), cas_k⟩² ≤ R²`. -/
theorem limField_Hq_bound {t : ℝ} (ht : t ∈ Set.Icc 0 T) (S : Finset (Fin d → ℤ)) :
    ∑ b, ∑ k ∈ S, wq q k * coef (limField q hT γ b) t k ^ 2 ≤ R ^ 2 := by
  have hev : ∀ᶠ N in atTop, ∀ k ∈ S, k ∈ box N :=
    (Filter.eventually_all_finset S).2 fun k _ => by
      obtain ⟨N₀, hN₀⟩ := exists_mem_box k
      exact eventually_atTop.2 ⟨N₀, fun N hN => box_mono hN hN₀⟩
  have hcoef : ∀ N b k, k ∈ box N →
      coef (galerkinField q hT γ N b) t k = cf q (γ N t) b k := by
    intro N b k hk
    have : coef (galerkinField q hT γ N b) t k = coef (fld q (γ N t) b) t k := by
      unfold coef sint
      exact integral_congr_ae (Eventually.of_forall fun y => by
        simp only [galerkinField_cons ht])
    rw [this, fld, coef_tfs_of_mem _ _ hk]
  have hlim : Tendsto (fun N => ∑ b, ∑ k ∈ S, wq q k * coef (galerkinField q hT γ N b) t k ^ 2)
      atTop (𝓝 (∑ b, ∑ k ∈ S, wq q k * coef (limField q hT γ b) t k ^ 2)) := by
    refine tendsto_finset_sum _ fun b _ => tendsto_finset_sum _ fun k _ =>
      (Tendsto.pow ?_ 2).const_mul _
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (tendsto_coef_unif
      (fun N => continuous_galerkinField hG.continuousOn N b)
      (continuous_limField (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b)
      (tendstoUniformly_galerkinField (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b) k
      (ε / 2) (by positivity))
    exact ⟨N₁, fun N hN => by rw [Real.dist_eq]; exact (hN₁ N hN t).trans_lt (by linarith)⟩
  refine le_of_tendsto hlim ?_
  filter_upwards [hev] with N hN
  calc ∑ b, ∑ k ∈ S, wq q k * coef (galerkinField q hT γ N b) t k ^ 2
      = ∑ b, ∑ k ∈ S, wq q k * cf q (γ N t) b k ^ 2 := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k hk => ?_
        rw [hcoef N b k (hN k hk)]
    _ ≤ ∑ b, ∑ k ∈ box N, wq q k * cf q (γ N t) b k ^ 2 :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum_of_subset_of_nonneg
          (fun k hk => hN k hk) fun k _ _ => mul_nonneg (wq_nonneg q k) (sq_nonneg _)
    _ = ‖γ N t‖ ^ 2 := by
        rw [← energyQ_fld q (γ N t) 0, energyQ]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [fld, Q_tfs]
    _ ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hG.bound N t ht) 2

include hm hq2 hA hsym hF hR₀ hR hU hUp hE hG in
/-- **The `L²` rate of the Galerkin approximation**: a Cauchy bound
`‖U_N(t) - U_M(t)‖²_{L²} ≤ C (2π(N+1))^{-q}` (`N ≤ M`) passes to the limit:
`‖U_N(t) - U(t)‖²_{L²} ≤ C (2π(N+1))^{-q}`. -/
theorem limField_L2_rate {C : ℝ}
    (hC : ∀ N M, N ≤ M → ∀ t ∈ Set.Icc 0 T,
      ∑ b, ∑ k ∈ box M, (cf q (γ N t) b k - cf q (γ M t) b k) ^ 2 ≤
        C / (2 * π * ((N : ℝ) + 1)) ^ q)
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ∑ b, sint (fun x => (galerkinField q hT γ N b x - limField q hT γ b x) ^ 2) t ≤
      C / (2 * π * ((N : ℝ) + 1)) ^ q := by
  obtain ⟨B, hB0, hB⟩ := exists_unif_bound (hT := hT) hm hq2 hR hG
  have hU1 := tendstoUniformly_galerkinField (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG
  have hlimB : ∀ c x, |limField q hT γ c x| ≤ B := fun c x =>
    abs_le_of_tendsto_abs ((hU1 c).tendsto_at x) fun N => (hB N c x).1
  have hcV : ∀ M b, Continuous (galerkinField q hT γ M b) := fun M b =>
    continuous_galerkinField hG.continuousOn M b
  have hcU : ∀ b, Continuous (limField q hT γ b) := fun b =>
    continuous_limField (hT := hT) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b
  have hseq : ∀ M, N ≤ M → ∑ b, sint (fun x => (galerkinField q hT γ N b x -
      galerkinField q hT γ M b x) ^ 2) t ≤ C / (2 * π * ((N : ℝ) + 1)) ^ q := by
    intro M hM
    refine le_trans (le_of_eq ?_) (hC N M hM t ht)
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sint_fld_sub_sq hM (γ N t) (γ M t) b t]
    unfold sint
    exact integral_congr_ae (Eventually.of_forall fun y => by
      simp only [galerkinField_cons ht])
  have hlim : Tendsto (fun M => ∑ b, sint (fun x => (galerkinField q hT γ N b x -
      galerkinField q hT γ M b x) ^ 2) t) atTop
      (𝓝 (∑ b, sint (fun x => (galerkinField q hT γ N b x - limField q hT γ b x) ^ 2) t)) := by
    refine tendsto_finset_sum _ fun b _ => ?_
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 (hU1 b)
      (ε / (8 * B + 1)) (by positivity))
    refine ⟨M₀, fun M hM => ?_⟩
    rw [Real.dist_eq, ← sint_sub
      (f := fun x => (galerkinField q hT γ N b x - galerkinField q hT γ M b x) ^ 2)
      (g := fun x => (galerkinField q hT γ N b x - limField q hT γ b x) ^ 2)
      ((hcV N b).sub (hcV M b) |>.pow 2) ((hcV N b).sub (hcU b) |>.pow 2)]
    refine (abs_sint_le (C := ε / (8 * B + 1) * (4 * B)) (fun x => ?_) t).trans_lt ?_
    · have h1 := (hM₀ M hM x).le
      rw [Real.dist_eq] at h1
      have e : (galerkinField q hT γ N b x - galerkinField q hT γ M b x) ^ 2 -
          (galerkinField q hT γ N b x - limField q hT γ b x) ^ 2 =
          (limField q hT γ b x - galerkinField q hT γ M b x) *
            (2 * galerkinField q hT γ N b x - galerkinField q hT γ M b x -
              limField q hT γ b x) := by ring
      rw [e, abs_mul]
      have h2 : |2 * galerkinField q hT γ N b x - galerkinField q hT γ M b x -
          limField q hT γ b x| ≤ 4 * B := by
        have := (hB N b x).1; have := (hB M b x).1; have := hlimB b x
        calc _ ≤ |2 * galerkinField q hT γ N b x| + |galerkinField q hT γ M b x| +
              |limField q hT γ b x| := by
              refine (abs_sub _ _).trans ?_
              exact add_le_add_left (abs_sub _ _) _ |>.trans_eq (by ring) |>.trans le_rfl
          _ ≤ 4 * B := by rw [abs_mul, abs_two]; linarith
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    · rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun M hM => hseq M hM⟩)

end Limit

/-! ### Kato's local existence theorem -/

/-- **Kato's local existence theorem for quasilinear symmetric hyperbolic systems on `𝕋^d`,
through the spectral Galerkin limit** (`thm:generated-dynamics`, `eq:generated-Galerkin` and
`lem:generated-physical-identification`, "common local Sobolev solution").  Let `m > d/2`,
`q ≥ 2m`, `q ≥ m + 2`, `A^i(v)` smooth real symmetric, `F(v)` smooth.  For every data radius `R₀`
there are `T > 0`, `R ≥ 0` and `C ≥ 0` (depending only on `R₀` and `A, F, q, m, d, n`) such that
every smooth `ℤ^d`-periodic datum `U₀` with `‖U₀‖²_{H^q} ≤ R₀²` has a solution `U` on
`[0, T] × 𝕋^d` with continuous spatial derivatives `P_i = ∂_iU`:
* `U` and `P` are continuous and periodic, `U(0) = U₀`, `∂_iU = P_i` along every spatial line;
* `∂_tU = F(U) - Σ_i A^i(U) P_i` on `[0, T]` (classical solution), and the integral equation
  `U(t) = U₀ + ∫₀ᵗ (F(U) - Σ_i A^i(U)P_i)` holds;
* `U ∈ L^∞_tH^q`: `Σ_b Σ_{k ∈ S} wq q k ⟨U_b(t), cas_k⟩² ≤ R²` for every finite mode set `S`;
* `U` is the limit of the spectral Galerkin solutions `U_N` (`GalerkinHyp`: data `P_N U₀`, the
  Galerkin ODE `U̇_N = P_N G(U_N)`, `‖U_N‖_{H^q} ≤ R` on `[0, T]` for every `N`): `U_N → U` and
  `∂_iU_N → P_i` uniformly on `[0, T] × ℝ^d`, with the `L²` rate
  `‖U_N(t) - U(t)‖²_{L²} ≤ C (2π(N+1))^{-q}`. -/
theorem kato_local_existence {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    (hq2 : m + 2 ≤ q) {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∃ R ≥ 0, ∃ C ≥ 0, ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) →
      (∀ b, IsSPeriodic (U₀ b)) → energyQ q U₀ 0 ≤ R₀ ^ 2 →
      ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ),
        (∀ b, Continuous (U b)) ∧ (∀ b i, Continuous (P b i)) ∧
        (∀ b, IsSPeriodic (U b)) ∧ (∀ b i, IsSPeriodic (P b i)) ∧
        (∀ b y, U b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
        (∀ b (i : Fin d) x, HasDerivAt (fun s : ℝ => U b (x + s • ev i.succ)) (P b i x) 0) ∧
        (∀ b, ∀ t ∈ Set.Icc 0 T, ∀ y, HasDerivWithinAt (fun s => U b (Fin.cons s y))
          (F b (fun c => U c (Fin.cons t y)) -
            ∑ i, ∑ b', A i b b' (fun c => U c (Fin.cons t y)) * P b' i (Fin.cons t y))
          (Set.Icc 0 T) t) ∧
        (∀ b, ∀ t ∈ Set.Icc 0 T, ∀ y, U b (Fin.cons t y) = U₀ b (Fin.cons 0 y) +
          ∫ s in (0)..t, (F b (fun c => U c (Fin.cons s y)) -
            ∑ i, ∑ b', A i b b' (fun c => U c (Fin.cons s y)) * P b' i (Fin.cons s y))) ∧
        (∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin d → ℤ),
          ∑ b, ∑ k ∈ S, wq q k * coef (U b) t k ^ 2 ≤ R ^ 2) ∧
        ∃ γ : (N : ℕ) → ℝ → GS d n N, GalerkinHyp A F q U₀ T R γ ∧
          (∀ b, ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Set.Icc 0 T, ∀ y,
            |fld q (γ N t) b (Fin.cons t y) - U b (Fin.cons t y)| ≤ ε ∧
            ∀ i : Fin d, |pd (fld q (γ N t) b) i.succ (Fin.cons t y) - P b i (Fin.cons t y)| ≤ ε) ∧
          (∀ N, ∀ t ∈ Set.Icc 0 T,
            ∑ b, sint (fun x => (fld q (γ N t) b x - U b x) ^ 2) t ≤
              C / (2 * π * ((N : ℝ) + 1)) ^ q) := by
  obtain ⟨T, hT, K, hK, hgal⟩ := galerkin_uniform (d := d) (n := n) hm hq hA hsym hF hR₀
  set R := 2 * R₀ + 1 with hRdef
  have hR : 0 ≤ R := by linarith
  obtain ⟨C, hC0, hC⟩ := galerkin_L2_cauchy (A := A) (F := F) hm (by omega : m + 1 ≤ q) hA hsym
    hF hR₀ hR hT.le
  refine ⟨T, hT, R, hR, C, hC0, fun U₀ hU hUp hE => ?_⟩
  have hex := fun N => hgal N U₀ hU hUp hE
  choose γ hγ0 hγ using hex
  have hG : GalerkinHyp A F q U₀ T R γ :=
    ⟨hγ0, fun N t ht => (hγ N t ht).1, fun N t ht => (hγ N t ht).2.1⟩
  have hT0 := hT.le
  refine ⟨limField q hT0 γ, limDeriv q hT0 γ,
    fun b => continuous_limField (hT := hT0) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b,
    fun b i => continuous_limDeriv (hT := hT0) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b i,
    fun b => isSPeriodic_limField b, fun b i => isSPeriodic_limDeriv b i,
    fun b y => limField_zero (hT := hT0) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b y,
    fun b i x => hasDerivAt_limField (hT := hT0) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b i x,
    fun b t ht y => hasDerivWithinAt_limField (hT := hT0) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG
      ht b y,
    fun b t ht y => limField_integral_eq (hT := hT0) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG ht b y,
    fun t ht S => limField_Hq_bound (hT := hT0) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG ht S,
    γ, hG, fun b ε hε => ?_, fun N t ht => ?_⟩
  · have h1 := Metric.tendstoUniformly_iff.1
      (tendstoUniformly_galerkinField (hT := hT0) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b) ε hε
    have h2 := fun i => Metric.tendstoUniformly_iff.1
      (tendstoUniformly_galerkinDeriv (hT := hT0) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG b i) ε hε
    filter_upwards [h1, Filter.eventually_all.2 h2] with N hN1 hN2 t ht y
    refine ⟨?_, fun i => ?_⟩
    · have := (hN1 (Fin.cons t y)).le
      rw [Real.dist_eq, abs_sub_comm, galerkinField_cons ht] at this
      exact this
    · have := (hN2 i (Fin.cons t y)).le
      rw [Real.dist_eq, abs_sub_comm, galerkinDeriv_cons ht] at this
      exact this
  · have h := limField_L2_rate (hT := hT0) hm hq2 hA hsym hF hR₀ hR hU hUp hE hG
      (hC U₀ hU hUp hE γ hG.init hG.deriv hG.bound) N ht
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold sint
    exact integral_congr_ae (Eventually.of_forall fun y => by
      simp only [galerkinField_cons ht])

/-! ### Non-vacuity -/

theorem sd_zero_fun (w : List (Fin d)) : sd w (fun _ : ST d => (0 : ℝ)) = fun _ => 0 := by
  rcases w with _ | ⟨i, w⟩
  · rfl
  · exact sd_const_nonempty _ (List.cons_ne_nil i w) 0

theorem energyQ_zero (k : ℕ) (t : ℝ) :
    energyQ (d := d) (n := n) k (fun _ _ => (0 : ℝ)) t = (0 : ℝ) := by
  simp [energyQ, Q, sd_zero_fun (d := d)]

/-- The coefficient matrix `A^1 = σ₁` (`A^2 = A^3 = 0`) of a `2 × 2` symmetric hyperbolic system
on `𝕋³`. -/
def exampleA : Fin 3 → Fin 2 → Fin 2 → (Fin 2 → ℝ) → ℝ :=
  fun i a b _ => if i = 0 ∧ a ≠ b then 1 else 0

/-- **Non-vacuity of `kato_local_existence`**: its hypotheses hold for the symmetric hyperbolic
system `∂_tU + σ₁∂_1U = -U` on `𝕋³` (`m = 2`, `q = 4`), and the theorem applies to the zero
datum. -/
example : ∃ (U : Fin 2 → ST 3 → ℝ) (P : Fin 2 → Fin 3 → ST 3 → ℝ),
    ∀ b y, U b (Fin.cons 0 y) = 0 := by
  obtain ⟨T, -, R, -, C, -, h⟩ := kato_local_existence (d := 3) (n := 2) (m := 2) (q := 4)
    (by norm_num) le_rfl le_rfl (A := exampleA) (F := fun a v => -v a)
    (fun _ _ _ => by unfold exampleA; exact contDiff_const)
    (fun i a b v => by
      unfold exampleA
      by_cases h : a = b
      · subst h; rfl
      · simp [h, Ne.symm h])
    (fun a => (contDiff_apply ℝ ℝ a).neg) zero_le_one
  obtain ⟨U, P, -, -, -, -, h0, -⟩ := h (fun _ _ => 0) (fun _ => contDiff_const)
    (fun _ _ _ => rfl) (by rw [energyQ_zero]; norm_num)
  exact ⟨U, P, fun b y => h0 b y⟩

end RenewalGeometry.KatoGalerkin
