/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMCertificatePacket
import RenewalGeometry.Action.ScaledSourceStationarity

/-!
# Strong-packet refinement of variational closure (`thm:main-limit`, `cor:exact-critical`,
  Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMCompactnessCertificates.lean` and `EinsteinSMReducedClosure.lean`
(cylinder `(0,T) × 𝕋³` lifted to `ℝ⁴`, trivialised bundles, chart boxes; the conclusions about the
first variation are stated on every slab chart `(t₀,t₁) × (0,1)³` whose open time interval contains
the time support of the test region `K`, which carries the whole first variation of a test in
`𝒱_K`; dual norms of `𝒱_K^{r₀}` rendered as uniform estimates `|ℓ_h(v) - ℓ(v)| ≤ ε ‖v‖`).

## Contents

* `H1Tendsto.toWeak`, `StrongPacketOn.toReduced`: a strong-packet convergence on a chart box, with
  the coframe chart condition and compact banks, is a reduced convergence there (so that the proved
  first-variation continuity `actionVariation_dual_tendsto` applies to strong-packet limits);
* `SourceBounds`: the hypotheses of `prop:source-bound` for the regulator (`a_h`, `G_h`, `v_h`,
  `R_h`, `L_h`, `e_h`); `stationarityDefect_le_of_source`, `physicallyStationary_of_source`
  (`ε_h(K) ≤ L_h√R_h + e_h`, through the proved `source_bound_pointwise`);
* `FirstVariationsConverge`, `IsDistributionalSolution`, `SatisfiesEinsteinSM`: the conclusions;
* `closure_along`: along any subsequence with reduced convergence on every slab chart,
  consistency and stationarity give convergence of the first variations, the Euler identities and
  `eq:Einstein-SM`;
* `main_residual_bound`: the residual bound `eq:main-residual-bound` in triangle form;
* `accumulation_point_solution`: every strong-packet accumulation point is a classical
  Einstein–Standard-Model solution (unconditional);
* **`main_limit_of_spinorStrong`**, **`main_limit_screen`** (route (C4a), unconditional),
  **`main_limit`** (the certificate as stated; route (C4b) conditional on `prop:dirac-stability`);
* **`exact_critical`** (`cor:exact-critical`);
* non-vacuity for the flat regulator.

**Residual bound (disclosed).**  `eq:main-residual-bound` reads
`‖D𝒮_θ(z)‖ ≤ L_h√R_h + e_h + c_h(K) + C_K d_K(z_h, z)`, its last term coming from the Lipschitz
estimate of `prop:variation-continuity` (open).  `main_residual_bound` proves the same triangle
inequality with `C_K d_K(z_h, z)` replaced by the first-variation continuity defect
`|D𝒮_{θ_h}(z_h)[v] - D𝒮_θ(z)[v]|`, which tends to zero uniformly on the unit ball along the
subsequence by the proved continuity theorem (`actionVariation_dual_tendsto`); all conclusions of
`thm:main-limit` follow from it.  Since the theorem proves `D𝒮_θ(z) = 0`, the displayed inequality
with any nonnegative `C_K d_K` also holds; the Lipschitz *estimate* itself is not used.

**Coframe chart (disclosed).**  As in `EinsteinSMCertificatePacket.lean`, the coframes are assumed
to take values a.e. in one fixed compact subset of the oriented time-oriented chart
(`CoframeChartCondition`, item (R1) of the reduced certificate).  The carrier's Yukawa map is
assumed to depend continuously on the bank (`FermionCarrier.YukawaContinuous`, as in
`reduced_closure`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Strong-packet convergence is reduced convergence -/

section StrongToReduced

variable {T : ℝ} {ι' : Type} [Fintype ι']

/-- Strong `H¹(Q)` convergence implies weak `H¹(Q)` convergence. -/
theorem H1Tendsto.toWeak {Q : ChartBox T} {u : ℕ → E4 → ι' → ℂ}
    {g : ℕ → E4 → Fin 4 → ι' → ℂ} {u₀ : E4 → ι' → ℂ} {g₀ : E4 → Fin 4 → ι' → ℂ}
    (hmem : ∀ n, MemH1 Q (u n) (g n)) (hmem₀ : MemH1 Q u₀ g₀) (h : H1Tendsto Q u g u₀ g₀) :
    WeakH1Tendsto Q u g u₀ g₀ := by
  have hu : ∀ n, MemLp (u n) 2 Q.μ := fun n => memLp_pi_iff.mpr fun c => (hmem n c).memLp
  have hg : ∀ n, MemLp (g n) 2 Q.μ := fun n =>
    memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun c => (hmem n c).memLp_grad i
  have hu₀ : MemLp u₀ 2 Q.μ := memLp_pi_iff.mpr fun c => (hmem₀ c).memLp
  have hg₀ : MemLp g₀ 2 Q.μ :=
    memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun c => (hmem₀ c).memLp_grad i
  have htu : Tendsto (fun n => eLpNorm (u n - u₀) 2 Q.μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le)
      fun n => le_self_add
  have htg : Tendsto (fun n => eLpNorm (g n - g₀) 2 Q.μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le)
      fun n => le_add_self
  obtain ⟨B₁, hB₁, hB₁n⟩ := exists_eLpNorm_bound (by norm_num) hu hu₀ htu
  obtain ⟨B₂, hB₂, hB₂n⟩ := exists_eLpNorm_bound (by norm_num) hg hg₀ htg
  refine ⟨hmem, hmem₀, ⟨B₁ + B₂, ENNReal.add_ne_top.mpr ⟨hB₁, hB₂⟩, fun n =>
    add_le_add (hB₁n n) (hB₂n n)⟩, fun χ hχ c => ?_, fun χ hχ i c => ?_⟩
  · exact SobolevOpen.tendsto_integral_test_of_L2 Q.isOpen.measurableSet Q.volume_ne_top hχ
      (fun n => (hmem n c).memLp) (hmem₀ c).memLp (tendsto_eLpNorm_apply htu c)
  · exact SobolevOpen.tendsto_integral_test_of_L2 Q.isOpen.measurableSet Q.volume_ne_top hχ
      (fun n => (hmem n c).memLp_grad i) ((hmem₀ c).memLp_grad i)
      (tendsto_eLpNorm_apply (u := fun n x => g n x i) (tendsto_eLpNorm_apply htg i) c)

variable {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- **A strong-packet convergence on a chart box is a reduced convergence there**, given the
coframe chart condition and banks in a compact physical set. -/
theorem StrongPacketOn.toReduced {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C} {θ₀ : CoefficientBank Ysec}
    (h : StrongPacketOn Q z L) (hch : CoframeChartCondition Q z)
    (hbank : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P) (hθ : BankTendsto θ θ₀) :
    ReducedConvergence Q z θ L θ₀ := by
  obtain ⟨Ke, hKe, hKn⟩ := hch
  have hcl := Q.isCompact_closure
  have hsub := Q.closure_subset_cylSlab
  have hcf : ∀ n, MemH1 Q (coframeC (z n).z.e) (coframeGrad (z n).z.e) := fun n =>
    memH1_coframe_of_smooth Q hcl hsub (z n).smooth_e
  have hmeas := coframe_tendstoInMeasure hcf h.coframe_mem h.coframe_H1
  have hKL : ∀ᵐ x ∂Q.μ, L.e x ∈ Ke := by
    obtain ⟨σ, -, hae⟩ := hmeas.exists_seq_tendsto_ae
    have hall : ∀ᵐ x ∂Q.μ, ∀ k, (z (σ k)).z.e x ∈ Ke := ae_all_iff.mpr fun k => hKn _
    filter_upwards [hae, hall] with x hx hxK
    exact hKe.1.isClosed.mem_of_tendsto hx (Eventually.of_forall hxK)
  have hH4 : RenewalGeometry.LpTendsto Q.μ 4 (fun n => (z n).z.H) L.H :=
    ⟨fun n => memLp_of_continuousOn_closure Q.isOpen hcl ((z n).smooth_H.continuousOn.mono hsub)
      4, h.higgs_mem, h.higgs_tendsto⟩
  have hH2 := hH4.mono (p := 2) (by norm_num) (by norm_num)
  exact
    { coframe_chart := ⟨Ke, hKe, hKn, hKL⟩
      coframe_mem := h.coframe_mem
      coframe_tendsto := h.coframe_H1
      conn_lie := h.conn_lie
      conn_mem := h.conn_mem
      conn_tendsto := h.conn_tendsto
      curv_mem := h.curv_mem
      curv_weak := h.curv_weak
      curv_tendsto := h.curv_tendsto
      higgs_mem := hH2.memLp_lim
      higgs_tendsto := hH2.tendsto
      covgrad_mem := h.covgrad_mem
      covgrad_weak := h.covgrad_weak
      covgrad_tendsto := h.covgrad_tendsto
      spinor_weak := H1Tendsto.toWeak (fun n => memH1_spinor_of_smooth Q (z n).smooth_Ψ)
        h.spinor_mem h.spinor_tendsto
      cospinor_weak := H1Tendsto.toWeak (fun n => memH1_spinor_of_smooth Q (z n).smooth_Ψb)
        h.cospinor_mem h.cospinor_tendsto
      bank_compact := hbank
      bank_tendsto := hθ }

end StrongToReduced

/-! ### `prop:source-bound` for the regulator -/

section Source

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **The hypotheses of `prop:source-bound` for a regulator sequence**: for every cutoff `n` a
positive source space `W n` (a real inner-product space, its norm the `G_h` norm), a finite action
covector `a_h : W n →L ℝ` (operator norm = `‖a_h‖_{G_h^{-1}}`) with `‖a_h‖² ≤ R_h`, source lifts
`v_h : 𝒱_K → W n` with `‖v_h(v)‖ ≤ L_h‖v‖_{C^{r₀}}`, and the identification error
`|D𝒮_h(z_h^d)[𝓘_hv] - a_h[v_h(v)]| ≤ e_h(K)‖v‖_{C^{r₀}}`. -/
def SourceBounds (reg : RegulatorSequence T FC) (W : ℕ → Type) [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)] (a : ∀ n, W n →L[ℝ] ℝ) (R Lc : ℕ → ℝ)
    (e : CylRegion T → ℕ → ℝ) (vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n) :
    Prop :=
  (∀ n, ‖a n‖ ^ 2 ≤ R n) ∧ (∀ n K v, ‖vh n K v‖ ≤ Lc n * ‖v‖) ∧
    ∀ n K (v : CrTest FC.left reg.r0 K),
      |fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v) - a n (vh n K v)| ≤
        e K n * ‖v‖

theorem ofReal_mul_le_ofReal {c t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal (c * t) ≤ ENNReal.ofReal c := by
  rcases le_or_gt 0 c with hc | hc
  · exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hc ht1)
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hc.le ht0)]
    exact zero_le

variable {reg : RegulatorSequence T FC} {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)]
  [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ} {R Lc : ℕ → ℝ}
  {e : CylRegion T → ℕ → ℝ} {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}

/-- `|D𝒮_h(z_h^d)[𝓘_hv]| ≤ (L_h√R_h + e_h)‖v‖` (`source_bound_pointwise`). -/
theorem finite_variation_le_of_source (hsrc : SourceBounds reg W a R Lc e vh) (n : ℕ)
    (K : CylRegion T) (v : CrTest FC.left reg.r0 K) :
    |fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)| ≤
      (Lc n * Real.sqrt (R n) + e K n) * ‖v‖ :=
  source_bound_pointwise (a n) (vh n K)
    (fun v : CrTest FC.left reg.r0 K => fderiv ℝ (reg.iface n).action (reg.config n)
      (reg.lift n K v)) (R n) (Lc n) (e K n) (hsrc.1 n) (hsrc.2.1 n K) (hsrc.2.2 n K) v

/-- **`prop:source-bound` for the regulator**: `ε_h(K) ≤ L_h√R_h + e_h(K)`. -/
theorem stationarityDefect_le_of_source (hsrc : SourceBounds reg W a R Lc e vh) (n : ℕ)
    (K : CylRegion T) :
    reg.stationarityDefect n K ≤ ENNReal.ofReal (Lc n * Real.sqrt (R n) + e K n) := by
  refine iSup₂_le fun w hw => ?_
  set v : CrTest FC.left reg.r0 K := w
  have hv : ‖v‖ ≤ 1 := hw
  exact (ENNReal.ofReal_le_ofReal (finite_variation_le_of_source hsrc n K v)).trans
    (ofReal_mul_le_ofReal (norm_nonneg v) hv)

/-- **Scaled stationarity from the source bound**: `L_h√R_h + e_h(K) → 0` for every `K` gives
physical common-action stationarity `ε_h(K) → 0`. -/
theorem physicallyStationary_of_source (hsrc : SourceBounds reg W a R Lc e vh)
    (hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (R n) + e K n) atTop (𝓝 0)) :
    reg.PhysicallyStationary := by
  intro K
  have h := ENNReal.tendsto_ofReal (hvan K)
  rw [ENNReal.ofReal_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le)
    fun n => stationarityDefect_le_of_source hsrc n K

end Source

/-! ### The closure conclusions -/

section Conclusions

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-- **Convergence of the first variations** along `σ`: on every slab chart containing the time
support of `K`, `D𝒮_{θ_h}(z_h) → D𝒮_θ(z)` in the dual norm of `𝒱_K^{r}` (gravitational
first-order representative + complete Standard-Model first variation of the limit). -/
def FirstVariationsConverge (r : ℕ) (fields : ℕ → SmoothFields T FC.left)
    (bank : ℕ → CoefficientBank Ysec) (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec) : Prop :=
  ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
    (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ ε > (0 : ℝ), ∀ᶠ k in atTop,
      ∀ v : CrTest FC.left r K,
        |(firstVariation T FC (bank k) .gravity (fields k).z v.val +
            firstVariation T FC (bank k) .standardModel (fields k).z v.val) -
          (gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
            smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v)| ≤ ε * ‖v‖

/-- **`eq:main-stationary`**: `D𝒮_θ(z)[v] = 0` for every test `v ∈ 𝒱_K` of every region `K`
(all Euler rows: metric, Yang–Mills, Higgs, Dirac–Yukawa). -/
def IsDistributionalSolution (r : ℕ) (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec) :
    Prop :=
  ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
    (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest FC.left r K,
      gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
        smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v = 0

/-- **`eq:Einstein-SM`**: `(Ein(g) + Λg) dV_g = κ T^SM dV_g` as distributions on metric tests. -/
def SatisfiesEinsteinSM (r : ℕ) (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec) : Prop :=
  ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
    (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest FC.left r K,
      einsteinDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v =
        θ₀.kappa * stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v

variable {FC}

/-- The Euler identities give `eq:Einstein-SM` on metric tests. -/
theorem IsDistributionalSolution.einstein {r : ℕ} {L : LimitFields FC.C}
    {θ₀ : CoefficientBank Ysec} (h : IsDistributionalSolution (T := T) FC r L θ₀) :
    SatisfiesEinsteinSM (T := T) FC r L θ₀ := by
  intro K t₀ t₁ h0 h01 h1 hK v
  have h' := h K t₀ t₁ h0 h01 h1 hK (metricTest FC v)
  simp only [einsteinDistribution, stressDistribution]
  rw [show gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L (metricTest FC v) =
    -smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L (metricTest FC v) by linarith]
  ring

/-- **Closure along a subsequence.**  If along `σ → ∞` the reconstructed fields converge in the
reduced topology on every slab chart, the regulator is first-variation consistent and physically
stationary, and the Yukawa map is continuous in the bank, then the first variations converge, the
limit solves all Euler equations and `eq:Einstein-SM` holds. -/
theorem closure_along (reg : RegulatorSequence T FC) {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop)
    {L : LimitFields FC.C} {θ₀ : CoefficientBank Ysec}
    (hRC : ∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (σ k))
        (fun k => reg.bank (σ k)) L θ₀)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) :
    FirstVariationsConverge FC reg.r0 (fun k => reg.fields (σ k)) (fun k => reg.bank (σ k)) L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ := by
  have hr : 1 ≤ reg.r0 := le_trans (by norm_num) reg.four_le_r0
  have hdual : FirstVariationsConverge FC reg.r0 (fun k => reg.fields (σ k))
      (fun k => reg.bank (σ k)) L θ₀ := by
    intro K t₀ t₁ h0 h01 h1 hK ε hε
    obtain ⟨hyL, hy0⟩ := hyuk _ _ (hRC t₀ t₁ h0 h01 h1).bank_tendsto
    exact actionVariation_dual_tendsto FC h0 h01 h1 hK hr (hRC t₀ t₁ h0 h01 h1) hyL hy0 hε
  have heuler : IsDistributionalSolution (T := T) FC reg.r0 L θ₀ := by
    intro K t₀ t₁ h0 h01 h1 hK
    refine eq_zero_of_unit_of_homogeneous FC (fun v => gravLimitVariation FC θ₀
      (slabChart t₀ t₁ h0 h01 h1) L v + smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v)
      (fun c v => by
        simp only [gravLimitVariation_smul, smLimitVariation_smul]; ring) ?_
    intro v hv
    exact limit_eq_zero_of_defects reg hσ K hcons hstat _ (hdual K t₀ t₁ h0 h01 h1 hK) v hv
  exact ⟨hdual, heuler, heuler.einstein⟩

end Conclusions

/-! ### `thm:main-limit` -/

section MainLimit

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **`eq:main-residual-bound` (triangle form).**  Under the source bounds, for every cutoff `n`,
every test region `K`, every limit `(z, θ)` and every test `v` with `‖v‖_{C^{r₀}} ≤ 1`:
`|D𝒮_θ(z)[v]| ≤ (L_h√R_h + e_h) + c_h(K) + |D𝒮_{θ_h}(z_h)[v] - D𝒮_θ(z)[v]|`. -/
theorem main_residual_bound {reg : RegulatorSequence T FC} {W : ℕ → Type}
    [∀ n, NormedAddCommGroup (W n)] [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ}
    {R Lc : ℕ → ℝ} {e : CylRegion T → ℕ → ℝ}
    {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBounds reg W a R Lc e vh) (n : ℕ) (K : CylRegion T)
    (ℓ : CrTest FC.left reg.r0 K → ℝ) (v : CrTest FC.left reg.r0 K) (hv : ‖v‖ ≤ 1) :
    ENNReal.ofReal |ℓ v| ≤ ENNReal.ofReal (Lc n * Real.sqrt (R n) + e K n) +
      reg.consistencyDefect n K +
      ENNReal.ofReal |(firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.val +
        firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.val) - ℓ v| := by
  obtain ⟨b1, -⟩ := reg.defect_bounds n K v hv
  have b2 : ENNReal.ofReal |fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)| ≤
      ENNReal.ofReal (Lc n * Real.sqrt (R n) + e K n) :=
    (ENNReal.ofReal_le_ofReal (finite_variation_le_of_source hsrc n K v)).trans
      (ofReal_mul_le_ofReal (norm_nonneg v) hv)
  set D := firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.val +
    firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.val
  set Φ := fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)
  have htri : |ℓ v| ≤ |Φ| + |D - Φ| + |D - ℓ v| := by
    have := abs_sub_le (ℓ v) D 0
    have h2 := abs_sub_le D Φ 0
    rw [abs_sub_comm (ℓ v) D] at this
    simp only [sub_zero] at this h2
    linarith [abs_nonneg (D - Φ)]
  calc ENNReal.ofReal |ℓ v| ≤ ENNReal.ofReal (|Φ| + |D - Φ| + |D - ℓ v|) :=
        ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal |Φ| + ENNReal.ofReal |D - Φ| + ENNReal.ofReal |D - ℓ v| := by
        rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    _ ≤ _ := add_le_add (add_le_add b2 b1) le_rfl

/-- **Every strong-packet accumulation point is a classical Einstein–Standard-Model solution**
(the identification part of `thm:main-limit`): if along a subsequence `σ` the reconstructed fields
converge to `(z, θ)` in the classical strong packet, the coframe chart condition holds and the
banks stay in a compact physical set, then consistency and stationarity make the first variations
converge to `D𝒮_θ(z)`, `D𝒮_θ(z) = 0` and `eq:Einstein-SM` holds. -/
theorem accumulation_point_solution (reg : RegulatorSequence T FC)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hbank : ∃ P, IsCompactBankSet P ∧ ∀ n, reg.bank n ∈ P)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) {σ : ℕ → ℕ} (hσ : StrictMono σ) {L : LimitFields FC.C}
    {θ₀ : CoefficientBank Ysec}
    (hSP : StrongPacket (fun k => reg.fields (σ k)) (fun k => reg.bank (σ k)) L θ₀) :
    FirstVariationsConverge FC reg.r0 (fun k => reg.fields (σ k)) (fun k => reg.bank (σ k)) L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ := by
  obtain ⟨P, hP, hθP⟩ := hbank
  refine closure_along reg hσ.tendsto_atTop (fun t₀ t₁ h0 h01 h1 => ?_) hcons hstat hyuk
  obtain ⟨Ke, hKe, hKn⟩ := hch (slabChart t₀ t₁ h0 h01 h1)
  exact (hSP.local_conv _).toReduced ⟨Ke, hKe, fun k => hKn _⟩ ⟨P, hP, fun k => hθP _⟩
    hSP.bank_tendsto

/-- **`thm:main-limit`, core form** (spinor strong data on every chart box).  Under the
compactness certificate on every chart box (with the coframe chart condition and strong spinor
data), first-variation consistency, the source bounds of `prop:source-bound` with
`L_h√R_h + e_h(K) → 0`, and continuity of the Yukawa map, every cutoff subsequence `ns` has a
further subsequence `ns ∘ ψ` and `(z, θ)` with: `θ` physical; `z_h → z` in the classical strong
packet (`StrongPacket`, every chart box); `D𝒮_{θ_h}(z_h) → D𝒮_θ(z)` in the dual norms;
`D𝒮_θ(z) = 0` (`eq:main-stationary`, all Euler rows); `eq:Einstein-SM`; and the residual bound
`main_residual_bound` along the subsequence. -/
theorem main_limit_of_spinorStrong (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hsp : ∀ Q : ChartBox T, SpinorStrongRoute Q reg.fields)
    (hcons : reg.FirstVariationConsistent) {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ} {R Lc : ℕ → ℝ}
    {e : CylRegion T → ℕ → ℝ} {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBounds reg W a R Lc e vh)
    (hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (R n) + e K n) atTop (𝓝 0))
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      θ₀ ∈ physicalBanks ∧
      StrongPacket (fun k => reg.fields (ns (ψ k))) (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      FirstVariationsConverge FC reg.r0 (fun k => reg.fields (ns (ψ k)))
        (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ ∧
      ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) (k : ℕ)
        (v : CrTest FC.left reg.r0 K), ‖v‖ ≤ 1 →
        ENNReal.ofReal |gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
            smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v| ≤
          ENNReal.ofReal (Lc (ns (ψ k)) * Real.sqrt (R (ns (ψ k))) + e K (ns (ψ k))) +
          reg.consistencyDefect (ns (ψ k)) K +
          ENNReal.ofReal |(firstVariation T FC (reg.bank (ns (ψ k))) .gravity
              (reg.fields (ns (ψ k))).z v.val +
            firstVariation T FC (reg.bank (ns (ψ k))) .standardModel
              (reg.fields (ns (ψ k))).z v.val) -
            (gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
              smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v)| := by
  have hstat := physicallyStationary_of_source hsrc hvan
  obtain ⟨ψ, hψ, L, θ₀, hSP, hRC⟩ := certificate_packet_of_spinorStrong hT hcert hch hsp ns hns
  have hcl := closure_along reg (hns.comp hψ).tendsto_atTop
    (fun t₀ t₁ h0 h01 h1 => hRC (slabChart t₀ t₁ h0 h01 h1)) hcons hstat hyuk
  exact ⟨ψ, hψ, L, θ₀, hSP.limit_bank_physical, hSP, hcl.1, hcl.2.1, hcl.2.2,
    fun K t₀ t₁ h0 h01 h1 k v hv => main_residual_bound hsrc (ns (ψ k)) K
      (fun v => gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
        smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v) v hv⟩

/-- **`thm:main-limit`, route (C4a)** (unconditional): the compactness certificate with the spinor
screen route on every chart box. -/
theorem main_limit_screen (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hroute : ∀ Q : ChartBox T, SpinorScreenRoute Q reg.fields)
    (hcons : reg.FirstVariationConsistent) {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ} {R Lc : ℕ → ℝ}
    {e : CylRegion T → ℕ → ℝ} {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBounds reg W a R Lc e vh)
    (hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (R n) + e K n) atTop (𝓝 0))
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      θ₀ ∈ physicalBanks ∧
      StrongPacket (fun k => reg.fields (ns (ψ k))) (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      FirstVariationsConverge FC reg.r0 (fun k => reg.fields (ns (ψ k)))
        (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ := by
  obtain ⟨ψ, hψ, L, θ₀, h1, h2, h3, h4, h5, -⟩ := main_limit_of_spinorStrong hT reg hcert hch
    (fun Q => (hroute Q).spinorStrongRoute) hcons hsrc hvan hyuk ns hns
  exact ⟨ψ, hψ, L, θ₀, h1, h2, h3, h4, h5⟩

/-- **`thm:main-limit`, the certificate as stated** (route (C4a) or (C4b) on each chart box),
**conditional on `prop:dirac-stability` for route (C4b)** (hypothesis `hdirac`: its conclusion,
`H¹`-Cauchy spinors, on the chart boxes using route (C4b)). -/
theorem main_limit (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hdirac : ∀ Q : ChartBox T, DiracStabilityRoute Q reg.fields → SpinorH1Cauchy Q reg.fields)
    (hcons : reg.FirstVariationConsistent) {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ} {R Lc : ℕ → ℝ}
    {e : CylRegion T → ℕ → ℝ} {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBounds reg W a R Lc e vh)
    (hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (R n) + e K n) atTop (𝓝 0))
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      θ₀ ∈ physicalBanks ∧
      StrongPacket (fun k => reg.fields (ns (ψ k))) (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      FirstVariationsConverge FC reg.r0 (fun k => reg.fields (ns (ψ k)))
        (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ := by
  have hsp : ∀ Q : ChartBox T, SpinorStrongRoute Q reg.fields := fun Q =>
    (hcert Q).spinor_route.elim (fun h => h.spinorStrongRoute)
      (fun h => (hdirac Q h).spinorStrongRoute)
  obtain ⟨ψ, hψ, L, θ₀, h1, h2, h3, h4, h5, -⟩ := main_limit_of_spinorStrong hT reg hcert hch
    hsp hcons hsrc hvan hyuk ns hns
  exact ⟨ψ, hψ, L, θ₀, h1, h2, h3, h4, h5⟩

end MainLimit

/-! ### `cor:exact-critical` -/

section ExactCritical

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- Exact finite critical points have vanishing stationarity defect: `ε_h(K) = 0`. -/
theorem stationarityDefect_eq_zero_of_critical (reg : RegulatorSequence T FC)
    (hcrit : ∀ n (K : CylRegion T) (v : CrTest FC.left reg.r0 K),
      fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v) = 0) (n : ℕ)
    (K : CylRegion T) : reg.stationarityDefect n K = 0 := by
  refine le_antisymm (iSup₂_le fun w _ => ?_) zero_le
  have h := hcrit n K w
  rw [h, abs_zero, ENNReal.ofReal_zero]

/-- **`cor:exact-critical`.**  Under the compactness and consistency hypotheses of
`thm:main-limit` (compactness certificate and coframe chart condition on every chart box,
`c_h(K) → 0`, continuity of the Yukawa map), if the finite configurations are exact critical
points in all lifted physical directions, `D𝒮_h(z_h^d)[𝓘_hv] = 0`, then every strong-packet
accumulation point `(z, θ)` satisfies all classical Euler equations and `eq:Einstein-SM`, without a
separate source-residual hypothesis (exact criticality gives `ε_h(K) = 0`). -/
theorem exact_critical (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hcons : reg.FirstVariationConsistent) (hyuk : FC.YukawaContinuous)
    (hcrit : ∀ n (K : CylRegion T) (v : CrTest FC.left reg.r0 K),
      fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v) = 0)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {L : LimitFields FC.C} {θ₀ : CoefficientBank Ysec}
    (hSP : StrongPacket (fun k => reg.fields (σ k)) (fun k => reg.bank (σ k)) L θ₀) :
    IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ := by
  have hstat : reg.PhysicallyStationary := fun K => by
    simp only [stationarityDefect_eq_zero_of_critical reg hcrit _ K]
    exact tendsto_const_nhds
  obtain ⟨P, hP, hθP⟩ := (hcert (midChart hT)).bank_compact
  exact (accumulation_point_solution reg hch ⟨P, hP, hθP⟩ hcons hstat hyuk hσ hSP).2
end ExactCritical

/-! ### Non-vacuity: the flat regulator -/

section FlatNonVacuity

variable {T : ℝ}

/-- The flat regulator satisfies the source bounds with `a_h = 0`, `R_h = L_h = e_h = 0`. -/
theorem flatRegulator_sourceBounds :
    SourceBounds (flatRegulator T) (fun _ => ℝ) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun _ _ => 0) (fun _ _ _ => 0) := by
  refine ⟨fun n => by simp, fun n K v => by simp, fun n K v => ?_⟩
  have h0 : (flatRegulator T).lift n K v = 0 := rfl
  rw [h0]
  simp

/-- The flat regulator's spinors are (trivially) Cauchy in `H¹` on every chart box. -/
theorem flatRegulator_spinorH1Cauchy (Q : ChartBox T) : SpinorH1Cauchy Q (flatRegulator T).fields :=
  ⟨fun ε _ => ⟨0, fun m _ n _ => by simp [h1Norm, flat_Ψ, spinorC_zero, spinorGrad_zero]⟩,
    fun ε _ => ⟨0, fun m _ n _ => by simp [h1Norm, flat_Ψb, spinorC_zero, spinorGrad_zero]⟩⟩

/-- The flat regulator consists of exact finite critical points (zero test lifts). -/
theorem flatRegulator_critical (n : ℕ) (K : CylRegion T)
    (v : CrTest (trivialCarrier Unit).left (flatRegulator T).r0 K) :
    fderiv ℝ ((flatRegulator T).iface n).action ((flatRegulator T).config n)
      ((flatRegulator T).lift n K v) = 0 := by
  have h0 : (flatRegulator T).lift n K v = 0 := rfl
  rw [h0, map_zero]

/-- **Non-vacuity of `thm:main-limit`** (route (C4a)): the flat regulator satisfies every
hypothesis of `main_limit_screen`. -/
example (hT : 0 < T) :=
  main_limit_screen hT (flatRegulator T) (fun Q => flatRegulator_compactnessCertificate T Q)
    (flatRegulator_coframeChart T) (flatRegulator_spinorScreenRoute T)
    (flatRegulator_consistent hT) flatRegulator_sourceBounds (fun K => by simp)
    (trivialCarrier_yukawaContinuous Unit) id strictMono_id

/-- **Non-vacuity of `main_limit`** (with the route-(C4b) hypothesis). -/
example (hT : 0 < T) :=
  main_limit hT (flatRegulator T) (fun Q => flatRegulator_compactnessCertificate T Q)
    (flatRegulator_coframeChart T) (fun Q _ => flatRegulator_spinorH1Cauchy Q)
    (flatRegulator_consistent hT) flatRegulator_sourceBounds (fun K => by simp)
    (trivialCarrier_yukawaContinuous Unit) id strictMono_id

/-- **Non-vacuity of `cor:exact-critical`**: the flat regulator satisfies every hypothesis and has
a strong-packet accumulation point. -/
example (hT : 0 < T) : ∃ (L : LimitFields Unit) (θ₀ : CoefficientBank Unit),
    IsDistributionalSolution (T := T) (trivialCarrier Unit) (flatRegulator T).r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) (trivialCarrier Unit) (flatRegulator T).r0 L θ₀ := by
  obtain ⟨ψ, hψ, L, θ₀, hSP⟩ := flatRegulator_certificatePacket_hyps hT
  exact ⟨L, θ₀, exact_critical hT (flatRegulator T)
    (fun Q => flatRegulator_compactnessCertificate T Q) (flatRegulator_coframeChart T)
    (flatRegulator_consistent hT) (trivialCarrier_yukawaContinuous Unit) flatRegulator_critical
    hψ hSP⟩

end FlatNonVacuity

end EinsteinSM
end RenewalGeometry
