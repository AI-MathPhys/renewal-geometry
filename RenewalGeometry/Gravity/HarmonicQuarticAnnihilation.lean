/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ConstantShiftWardOrders
import RenewalGeometry.Analysis.AnalyticCauchyProductCoefficients
import RenewalGeometry.Gravity.ExactSlowRankTwoExact

/-!
# Base-uniform harmonic quartic annihilation from the constant-shift Ward packet
  (`thm:supp-exact-harmonic-q4-zero`, `eq:supp-exact-harmonic-q4-zero`,
  `eq:supp-exact-fixed-target-residual`, `eq:supp-exact-pure-harmonic-ray`,
  `eq:supp-exact-ward-mass-order`, `eq:supp-exact-harmonic-mass-column`,
  `lem:supp-exact-ward-orders`; emergent-spacetime manuscript)

For one literal constant-shift row `c` of the Hamiltonian `H_h(X, λ)` put
`P_c = ∂_λH_h[H_c c]`, `P'_c = D_X P_c` (`rowX`), the mass column `𝓜_c = D_λP_c = 𝓜[c, ·]`
(`massCol`), `ℬ_c = P'_c F^can` (`WardOrders.wardRow`), and the constant-shift row of the
fixed-target residual `𝓕_a(Q) = ℬ(Q) + 𝓜(Q) a r_*(a)` (`eq:supp-exact-fixed-target-residual`),
`ℬ_c(Q) + 𝓜_c(Q)[a r_*]` (`residualRow`).  Its directional residual along a tangent
`δQ = (δX, δλ)` is `Dℬ_c(Q)[δQ] + D𝓜_c(Q)[δQ][a r_*]` (`dirResidualRow`,
`dirResidualRow_eq_fderiv`).

General infrastructure:
* `coeff_eq_zero_of_isBigO`: an analytic `q : ℝ → F` with `q = O(aᵏ)` as `a ↓ 0` has vanishing
  Taylor coefficients of order `< k`;
* `fderiv_inr_eq_zero_of_slice`, `norm_le_of_slice`: a map vanishing on the slice `X = 0` has
  vanishing `λ`-derivative there, and a slice-vanishing map whose `X`-derivative is
  `O(‖X‖ᵏ)` is `O(‖X‖ᵏ⁺¹)` near `(0, e)` (mean value along `X`-segments);
* `massCol_inr_bound`: the uniform mass order `𝓜(X, λ) = O(‖X‖²)` (`eq:supp-exact-ward-mass-order`,
  encoded on the slice as `𝓜_c(0, λ) = 0`, `D_X𝓜_c(0, λ) = 0` for `λ` near `e`) gives
  `‖D_λ𝓜_c(X, λ)‖ = O(‖X‖²)` (symmetry of second derivatives), and `massRow_eq_zero_of_mass`
  derives the Ward hypothesis `D_X𝓜(0, e)[c, ·] = 0` of `WardOrders.ward_orders` from it.

Main results:
* **`dirResidualRow_isBigO_five`**: under the constant-shift Ward packet (`F^can(0,e) = 0`,
  `P_{c,1} = 0`, vanishing linear first-Poisson coefficient `𝕂₁(Y)c = 0`, the quadratic
  mass-column identity `𝓜₂(X, e)c = 0` and the vanishing quadratic bracket of commuting phase
  translations for `ν = H_c c`), the uniform mass order, along every base family
  `Q_a = (0, e) + O(a)` and every pure-harmonic ray tangent `δX = O(a⁵)`,
  `δλ = a²H_c c + O(a³)` (`eq:supp-exact-pure-harmonic-ray`) with bounded rate `r_*`, the
  constant-shift row of the directional residual is `O(a⁵)`.  This is the order count of the
  paper's proof (canonical part `O(a)O(a⁵)`, leading harmonic multiplier part `O(a³)O(a²)`,
  nonharmonic multiplier corrections `O(a²)O(a³)`, mass part `O(a²)O(a²)O(a)`).
* **`harmonic_q4_zero`** (`eq:supp-exact-harmonic-q4-zero`): if that row is analytic in `a`, its
  Taylor coefficients of order `≤ 4` vanish, in particular `q₄ = 0`; `q4_fderiv_eq_zero`: a
  quartic coefficient vanishing at every base near `ξ₀` has zero base derivative.
* **`harmonicAnnihilation_of_quartic`**, **`harmonicAnnihilation_of_ward`**: if, at every
  second-record base `Ξ(q)` near `0` on the elimination graph, the rows of the harmonic
  derivative `D𝔠_H(Ξ(q))[J_H c]` are the quartic coefficients `q₄(Ξ(q); J_H c)` of the
  constant-shift rows (the identification of the harmonic compatibility row with the rescaled
  constant-shift row of the graded chart), then `ExactSlowRankTwo.HarmonicAnnihilation` holds;
  `slopeCan_rank_two_factorization_of_ward` and `harmonic_slope_entrance_of_ward`
  (`D𝔠_H(0)J_H = 0`) instantiate the slope chain with the Ward packet in place of the
  annihilation hypothesis.

Status of the inputs.  The Ward packet, the mass order and the ray orders are the finite
coefficient identities the manuscript displays (`eq:supp-exact-ward-mass-order`,
`eq:supp-exact-harmonic-mass-column`, `eq:supp-exact-pure-harmonic-ray`) for its explicit finite
action; they are hypotheses here.  They are Taylor-coefficient identities of `H_h` at the flat
point `(0, e)` (up to third order in `X`, second in `λ`) and of the graded chart; they do not
involve the certified event `Y_*` or `ω = 3√3`.
-/

open Filter Set Asymptotics Finset
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace HarmonicQuartic

open WardOrders

/-! ### Taylor coefficients of a function that is `O(aᵏ)` -/

section Coeff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An analytic `q : ℝ → F` with `q = O(aᵏ)` as `a ↓ 0` has vanishing Taylor coefficients of
every order `j < k`. -/
theorem coeff_eq_zero_of_isBigO {q : ℝ → F} {pq : FormalMultilinearSeries ℝ ℝ F}
    (hq : HasFPowerSeriesAt q pq 0) {k : ℕ} (hO : q =O[𝓝[>] 0] fun a => a ^ k) :
    ∀ j < k, pq.coeff j = 0 := by
  have h1 : (fun a : ℝ => q a - ∑ m ∈ range k, a ^ m • pq.coeff m) =O[𝓝[>] 0]
      fun a => a ^ k := by
    have := (AnalyticCauchy.isBigO_sub_sum hq k).mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    refine this.trans (isBigO_of_le' (c := 1) _ fun a => ?_)
    simp [norm_pow]
  have h2 : (fun a : ℝ => ∑ m ∈ range k, a ^ m • pq.coeff m) =O[𝓝[>] 0] fun a => a ^ k := by
    have := hO.sub h1
    simpa using this
  obtain ⟨C, hC⟩ := h2.bound
  refine AnalyticCauchy.poly_coeff_eq_zero_of_eventually k (fun m => pq.coeff m) C ?_
  filter_upwards [hC, self_mem_nhdsWithin] with a ha hpos
  rwa [Real.norm_eq_abs, abs_of_pos (pow_pos hpos k)] at ha

end Coeff

/-! ### Slice lemmas -/

section Slice

variable {X L F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A map vanishing on the slice `X = 0` near `λ₀` has vanishing `λ`-derivative at `(0, λ₀)`. -/
theorem fderiv_inr_eq_zero_of_slice (Φ : X × L → F) {lam₀ : L}
    (hz : ∀ᶠ lam in 𝓝 lam₀, Φ (0, lam) = 0) (hd : DifferentiableAt ℝ Φ (0, lam₀)) :
    (fderiv ℝ Φ (0, lam₀)).comp (ContinuousLinearMap.inr ℝ X L) = 0 := by
  have h1 : HasFDerivAt (fun lam => Φ (0, lam)) ((fderiv ℝ Φ (0, lam₀)).comp
      (ContinuousLinearMap.inr ℝ X L)) lam₀ :=
    hd.hasFDerivAt.comp lam₀ (hasFDerivAt_prodMk_right (0 : X) lam₀)
  have h2 : HasFDerivAt (fun lam => Φ (0, lam)) (0 : L →L[ℝ] F) lam₀ :=
    (hasFDerivAt_const (0 : F) lam₀).congr_of_eventuallyEq (hz.mono fun lam hlam => hlam)
  exact h1.unique h2

/-- **Slice mean-value lemma.**  If `G` is differentiable near `(0, e)`, its `X`-derivative
satisfies `‖D_X G(X, λ)‖ ≤ C‖X‖ᵏ` near `(0, e)`, and `G(0, λ) = 0` for `λ` near `e`, then
`‖G(X, λ)‖ ≤ C‖X‖ᵏ⁺¹` near `(0, e)`. -/
theorem norm_le_of_slice {G : X × L → F} {e : L} {k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ᶠ z in 𝓝 ((0 : X), e), DifferentiableAt ℝ G z)
    (hbound : ∀ᶠ z in 𝓝 ((0 : X), e),
      ‖(fderiv ℝ G z).comp (ContinuousLinearMap.inl ℝ X L)‖ ≤ C * ‖z.1‖ ^ k)
    (hslice : ∀ᶠ lam in 𝓝 e, G (0, lam) = 0) :
    ∀ᶠ z in 𝓝 ((0 : X), e), ‖G z‖ ≤ C * ‖z.1‖ ^ (k + 1) := by
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.eventually_nhds_iff_ball.mp (hd.and hbound)
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.eventually_nhds_iff_ball.mp hslice
  filter_upwards [Metric.ball_mem_nhds _ (lt_min hr₁ hr₂)] with z hz
  obtain ⟨Xz, lamz⟩ := z
  have hdist : dist ((Xz, lamz) : X × L) (0, e) = max ‖Xz‖ (dist lamz e) := by
    rw [Prod.dist_eq, dist_zero_right]
  rw [Metric.mem_ball, hdist] at hz
  have hlam : dist lamz e < r₂ := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hz (min_le_right _ _))
  have hmem : ∀ Y ∈ Metric.closedBall (0 : X) ‖Xz‖, ((Y, lamz) : X × L) ∈ Metric.ball (0, e) r₁ := by
    intro Y hY
    rw [Metric.mem_closedBall, dist_zero_right] at hY
    rw [Metric.mem_ball, Prod.dist_eq, dist_zero_right]
    exact lt_of_le_of_lt (max_le_max hY le_rfl) (lt_of_lt_of_le hz (min_le_left _ _))
  set g : X → F := fun Y => G (Y, lamz)
  have hgd : ∀ Y ∈ Metric.closedBall (0 : X) ‖Xz‖,
      HasFDerivAt g ((fderiv ℝ G (Y, lamz)).comp (ContinuousLinearMap.inl ℝ X L)) Y := fun Y hY =>
    ((h₁ _ (hmem Y hY)).1).hasFDerivAt.comp Y (hasFDerivAt_prodMk_left Y lamz)
  have hgb : ∀ Y ∈ Metric.closedBall (0 : X) ‖Xz‖,
      ‖(fderiv ℝ G (Y, lamz)).comp (ContinuousLinearMap.inl ℝ X L)‖ ≤ C * ‖Xz‖ ^ k := by
    intro Y hY
    have hb := (h₁ _ (hmem Y hY)).2
    have hY' : ‖Y‖ ≤ ‖Xz‖ := by rwa [Metric.mem_closedBall, dist_zero_right] at hY
    exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hY' k) hC)
  have hconv : Convex ℝ (Metric.closedBall (0 : X) ‖Xz‖) := convex_closedBall _ _
  have hmv := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun Y hY => (hgd Y hY).hasFDerivWithinAt) hgb
    (Metric.mem_closedBall_self (norm_nonneg _))
    (show Xz ∈ Metric.closedBall (0 : X) ‖Xz‖ by simp)
  have hg0 : g 0 = 0 := h₂ lamz hlam
  rw [hg0, sub_zero, sub_zero] at hmv
  simp only [g] at hmv
  rw [pow_succ, ← mul_assoc]
  exact hmv

end Slice

/-! ### The constant-shift row of the directional residual -/

section Row

variable {X L : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup L]
  [NormedSpace ℝ L]

/-- `P'_c = D_X P_c`. -/
def rowX (P : X × L → ℝ) (z : X × L) : X →L[ℝ] ℝ :=
  (fderiv ℝ P z).comp (ContinuousLinearMap.inl ℝ X L)

/-- The mass column `𝓜_c = D_λ P_c = 𝓜[c, ·]` (`𝓜 = H_λλ`, `eq:supp-exact-ward-objects`). -/
def massCol (P : X × L → ℝ) (z : X × L) : L →L[ℝ] ℝ :=
  (fderiv ℝ P z).comp (ContinuousLinearMap.inr ℝ X L)

/-- The constant-shift row `ℬ_c(Q) + 𝓜_c(Q)[μ]` of the fixed-target residual
`𝓕_a(Q) = ℬ(Q) + 𝓜(Q) a r_*(a)` (`eq:supp-exact-fixed-target-residual`, `μ = a r_*(a)`). -/
def residualRow (P : X × L → ℝ) (F : X × L → X) (z : X × L) (μ : L) : ℝ :=
  wardRow (rowX P) F z + massCol P z μ

/-- The constant-shift row of the directional residual along `δQ`:
`Dℬ_c(Q)[δQ] + D𝓜_c(Q)[δQ][μ]`. -/
def dirResidualRow (P : X × L → ℝ) (F : X × L → X) (z δ : X × L) (μ : L) : ℝ :=
  fderiv ℝ (wardRow (rowX P) F) z δ + fderiv ℝ (massCol P) z δ μ

/-- `dirResidualRow` is the directional derivative in `Q` of the residual row at fixed target
rate `μ`. -/
theorem dirResidualRow_eq_fderiv (P : X × L → ℝ) (F : X × L → X) {z : X × L} (δ : X × L)
    (μ : L) (hB : DifferentiableAt ℝ (wardRow (rowX P) F) z)
    (hM : DifferentiableAt ℝ (massCol P) z) :
    fderiv ℝ (fun w => residualRow P F w μ) z δ = dirResidualRow P F z δ μ := by
  have h : HasFDerivAt (fun w => residualRow P F w μ)
      (fderiv ℝ (wardRow (rowX P) F) z +
        (ContinuousLinearMap.apply ℝ ℝ μ).comp (fderiv ℝ (massCol P) z)) z :=
    hB.hasFDerivAt.add ((ContinuousLinearMap.apply ℝ ℝ μ).hasFDerivAt.comp z hM.hasFDerivAt)
  rw [h.fderiv]
  rfl

/-- Derivative of `z ↦ (Φ z).comp K` for a fixed `K`. -/
theorem fderiv_comp_const_apply {E G H K' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K'] [NormedSpace ℝ K'] {Φ : E → G →L[ℝ] H} {z : E}
    (hΦ : DifferentiableAt ℝ Φ z) (K : K' →L[ℝ] G) (v : E) :
    fderiv ℝ (fun w => (Φ w).comp K) z v = (fderiv ℝ Φ z v).comp K := by
  have h := hΦ.hasFDerivAt.clm_comp (hasFDerivAt_const K z)
  rw [h.fderiv]
  ext x
  simp

end Row

/-! ### The mass order -/

section Mass

variable {X L : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup L]
  [NormedSpace ℝ L]

/-- **Second-order slice lemma.**  If `G` is `C²` near `(0, e)` and both `G(0, λ)` and
`D_X G(0, λ)` vanish for `λ` near `e`, then `‖G(X, λ)‖ ≤ C‖X‖²` near `(0, e)`. -/
theorem norm_le_sq_of_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : X × L → F} {e : L} (hG : ContDiffAt ℝ 2 G (0, e))
    (h0 : ∀ᶠ lam in 𝓝 e, G (0, lam) = 0)
    (h1 : ∀ᶠ lam in 𝓝 e, (fderiv ℝ G (0, lam)).comp (ContinuousLinearMap.inl ℝ X L) = 0) :
    ∃ C, ∀ᶠ z in 𝓝 ((0 : X), e), ‖G z‖ ≤ C * ‖z.1‖ ^ 2 := by
  set p : X × L := (0, e)
  set Φ : X × L → X →L[ℝ] F := fun z => (fderiv ℝ G z).comp (ContinuousLinearMap.inl ℝ X L)
  have hΦc : ContDiffAt ℝ 1 Φ p :=
    (hG.fderiv_right (m := 1) (by norm_num)).clm_comp contDiffAt_const
  have hGd : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ G z :=
    (hG.eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp)
  have hΦd : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ Φ z :=
    (hΦc.eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp)
  have hDΦc := (hΦc.fderiv_right (m := 0) le_rfl).continuousAt
  set C₀ := ‖fderiv ℝ Φ p‖ + 1
  have hb0 : ∀ᶠ z in 𝓝 p,
      ‖(fderiv ℝ Φ z).comp (ContinuousLinearMap.inl ℝ X L)‖ ≤ C₀ * ‖z.1‖ ^ 0 := by
    have hlt : ∀ᶠ z in 𝓝 p, ‖fderiv ℝ Φ z‖ < C₀ :=
      hDΦc.norm.eventually (gt_mem_nhds (lt_add_one _))
    filter_upwards [hlt] with z hz
    rw [pow_zero, mul_one]
    calc ‖(fderiv ℝ Φ z).comp (ContinuousLinearMap.inl ℝ X L)‖
        ≤ ‖fderiv ℝ Φ z‖ * ‖ContinuousLinearMap.inl ℝ X L‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ Φ z‖ * 1 := by
          gcongr; exact ContinuousLinearMap.norm_inl_le_one ℝ X L
      _ ≤ C₀ := by rw [mul_one]; exact hz.le
  have hC₀ : 0 ≤ C₀ := by positivity
  have hΦb : ∀ᶠ z in 𝓝 p, ‖Φ z‖ ≤ C₀ * ‖z.1‖ ^ (0 + 1) := norm_le_of_slice hC₀ hΦd hb0 h1
  have hGb : ∀ᶠ z in 𝓝 p, ‖G z‖ ≤ C₀ * ‖z.1‖ ^ (1 + 1) :=
    norm_le_of_slice hC₀ hGd (by simpa using hΦb) h0
  exact ⟨C₀, hGb⟩

/-- From the uniform mass order on the slice (`𝓜_c(0, λ) = 0`, `D_X𝓜_c(0, λ) = 0` for `λ`
near `e`): `‖D_λ𝓜_c(X, λ)‖ ≤ C‖X‖²` near `(0, e)`. -/
theorem massCol_inr_bound (P : X × L → ℝ) (e : L) (hP : ContDiffAt ℝ 5 P (0, e))
    (hmass0 : ∀ᶠ lam in 𝓝 e, massCol P (0, lam) = 0)
    (hmass1 : ∀ᶠ lam in 𝓝 e,
      (fderiv ℝ (massCol P) (0, lam)).comp (ContinuousLinearMap.inl ℝ X L) = 0) :
    ∃ C, ∀ᶠ z in 𝓝 ((0 : X), e),
      ‖(fderiv ℝ (massCol P) z).comp (ContinuousLinearMap.inr ℝ X L)‖ ≤ C * ‖z.1‖ ^ 2 := by
  set p : X × L := (0, e)
  set Mc := massCol P
  have hMc : ContDiffAt ℝ 4 Mc p :=
    (hP.fderiv_right (m := 4) (by norm_num)).clm_comp contDiffAt_const
  have hMcev : ∀ᶠ z in 𝓝 p, ContDiffAt ℝ 4 Mc z := hMc.eventually (by simp)
  have hsl : Tendsto (fun lam : L => ((0 : X), lam)) (𝓝 e) (𝓝 p) :=
    (continuous_const.prodMk continuous_id).tendsto' e p rfl
  have hMclam : ∀ᶠ lam in 𝓝 e, ContDiffAt ℝ 4 Mc (0, lam) := hsl.eventually hMcev
  have hGc : ContDiffAt ℝ 2 (fun z => (fderiv ℝ Mc z).comp (ContinuousLinearMap.inr ℝ X L)) p :=
    (hMc.fderiv_right (m := 2) (by norm_num)).clm_comp contDiffAt_const
  refine norm_le_sq_of_slice hGc ?_ ?_
  · filter_upwards [hmass0.eventually_nhds, hMclam] with lam hlam hc
    exact fderiv_inr_eq_zero_of_slice Mc hlam (hc.differentiableAt (by simp))
  · filter_upwards [hmass1.eventually_nhds, hMclam] with lam hlam hc
    have hd1 : DifferentiableAt ℝ (fderiv ℝ Mc) (0, lam) :=
      (hc.fderiv_right (m := 3) (by norm_num)).differentiableAt (by simp)
    have hsymm : IsSymmSndFDerivAt ℝ Mc (0, lam) := hc.isSymmSndFDerivAt (by simp; norm_num)
    have hH1 := fderiv_inr_eq_zero_of_slice
      (fun z => (fderiv ℝ Mc z).comp (ContinuousLinearMap.inl ℝ X L)) hlam
      (hd1.clm_comp (differentiableAt_const _))
    refine ContinuousLinearMap.ext fun w => ContinuousLinearMap.ext fun ν => ?_
    have e1 : fderiv ℝ (fun z => (fderiv ℝ Mc z).comp (ContinuousLinearMap.inr ℝ X L)) (0, lam)
        (ContinuousLinearMap.inl ℝ X L w) ν =
        fderiv ℝ (fderiv ℝ Mc) (0, lam) (ContinuousLinearMap.inl ℝ X L w)
          (ContinuousLinearMap.inr ℝ X L ν) := by
      rw [fderiv_comp_const_apply hd1]
      rfl
    have e2 : fderiv ℝ (fderiv ℝ Mc) (0, lam) (ContinuousLinearMap.inr ℝ X L ν)
        (ContinuousLinearMap.inl ℝ X L w) =
        fderiv ℝ (fun z => (fderiv ℝ Mc z).comp (ContinuousLinearMap.inl ℝ X L)) (0, lam)
          (ContinuousLinearMap.inr ℝ X L ν) w := by
      rw [fderiv_comp_const_apply hd1]
      rfl
    have e3 : fderiv ℝ (fun z => (fderiv ℝ Mc z).comp (ContinuousLinearMap.inl ℝ X L)) (0, lam)
        (ContinuousLinearMap.inr ℝ X L ν) = 0 := by
      have := congrArg (fun T => T ν) hH1
      simpa using this
    show fderiv ℝ (fun z => (fderiv ℝ Mc z).comp (ContinuousLinearMap.inr ℝ X L)) (0, lam)
        (ContinuousLinearMap.inl ℝ X L w) ν = 0
    rw [e1, hsymm, e2, e3]
    rfl

/-- The Ward hypothesis `D_X𝓜(0, e)[c, ·] = 0` (`massRow` of `WardOrders.ward_orders`) follows from
the mass order on the slice at `λ = e` (symmetry of `D²P_c`). -/
theorem massRow_eq_zero_of_mass (P : X × L → ℝ) (e : L) (hP : ContDiffAt ℝ 5 P (0, e))
    (hmass1 : (fderiv ℝ (massCol P) (0, e)).comp (ContinuousLinearMap.inl ℝ X L) = 0) :
    massRow (rowX P) (0, e) = 0 := by
  have hd1 : DifferentiableAt ℝ (fderiv ℝ P) (0, e) :=
    (hP.fderiv_right (m := 4) (by norm_num)).differentiableAt (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ P (0, e) := hP.isSymmSndFDerivAt (by simp; norm_num)
  ext ν w
  have h1 : massRow (rowX P) (0, e) ν w =
      fderiv ℝ (fderiv ℝ P) (0, e) (ContinuousLinearMap.inr ℝ X L ν)
        (ContinuousLinearMap.inl ℝ X L w) := by
    simp only [massRow, ContinuousLinearMap.comp_apply]
    rw [show rowX P = fun w => (fderiv ℝ P w).comp (ContinuousLinearMap.inl ℝ X L) from rfl,
      fderiv_comp_const_apply hd1]
    rfl
  have h2 : ((fderiv ℝ (massCol P) (0, e)).comp (ContinuousLinearMap.inl ℝ X L)) w ν =
      fderiv ℝ (fderiv ℝ P) (0, e) (ContinuousLinearMap.inl ℝ X L w)
        (ContinuousLinearMap.inr ℝ X L ν) := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [show massCol P = fun w => (fderiv ℝ P w).comp (ContinuousLinearMap.inr ℝ X L) from rfl,
      fderiv_comp_const_apply hd1]
    rfl
  rw [h1, hsymm, ← h2, hmass1]
  rfl

end Mass

/-! ### The order count -/

section Orders

variable {X L : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]

/-- Along a family `z_a → p` with `‖z_a - p‖ = O(a)` (filter `l`), a map vanishing to order `k`
at `p` is `O(aᵏ)`. -/
theorem _root_.RenewalGeometry.WardOrders.VanishesToOrder.comp_family' {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] {f : E → G} {p : E} {k : ℕ} (hf : VanishesToOrder f p k)
    {l : Filter ℝ} (z : ℝ → E) (hz : (fun a => z a - p) =O[l] fun a => a)
    (hl : Tendsto (fun a : ℝ => a) l (𝓝 0)) :
    (fun a => f (z a)) =O[l] fun a => a ^ k := by
  have ht : Tendsto z l (𝓝 p) := by
    have h2 := (hz.trans_tendsto hl).add_const p
    simpa using h2
  exact (hf.comp_tendsto ht).trans (hz.norm_left.pow k)

/-- Product estimate for operator evaluation along a filter. -/
theorem isBigO_clm_apply {α E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {l : Filter α} {A : α → E →L[ℝ] G} {v : α → E} {f g : α → ℝ}
    (hA : A =O[l] f) (hv : v =O[l] g) : (fun a => A a (v a)) =O[l] fun a => f a * g a := by
  have h1 : (fun a => A a (v a)) =O[l] fun a => ‖A a‖ * ‖v a‖ :=
    IsBigO.of_bound 1 (Eventually.of_forall fun a => by
      rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (A a).le_opNorm (v a))
  exact h1.trans (hA.norm_left.mul hv.norm_left)

/-- **The order count of `thm:supp-exact-harmonic-q4-zero`.**  Let `P = P_c` be a literal
constant-shift row (`C⁵` near `p = (0, e)`) and `F = F^can` (`C⁴`), satisfying the constant-shift
Ward packet `F(p) = 0`, `P_{c,1} = 0`, `𝕂₁(Y)c = 0` (`hK1`), and for the harmonic multiplier
direction `ν = H_c c` the quadratic mass-column identity (`hM2`) and the vanishing quadratic
bracket (`hQ`); let the mass be of order `‖X‖²` uniformly in `λ` (`hmass0`, `hmass1`).  Then along
every base family `Q_a = p + O(a)` (`a ↓ 0`), every exact-constrained tangent with
`δX = O(a⁵)`, `δλ = a²ν + O(a³)` (`eq:supp-exact-pure-harmonic-ray`) and every bounded rate
`r_*`, the constant-shift row of the directional residual
`Dℬ_c(Q_a)[δQ_a] + D𝓜_c(Q_a)[δQ_a][a r_*(a)]` is `O(a⁵)`. -/
theorem dirResidualRow_isBigO_five (P : X × L → ℝ) (F : X × L → X) (e ν : L)
    (hP : ContDiffAt ℝ 5 P (0, e)) (hF : ContDiffAt ℝ 4 F (0, e))
    (hF0 : F (0, e) = 0) (hP0 : rowX P (0, e) = 0)
    (hK1 : ∀ w, (fderiv ℝ (rowX P) (0, e) w).comp
      ((fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L)) = 0)
    (hM2 : fderiv ℝ (fun z => massRow (rowX P) z ν) (0, e) = 0)
    (hQ : fderiv ℝ (fderiv ℝ (fun z => bracketRow (rowX P) F z ν)) (0, e) = 0)
    (hmass0 : ∀ᶠ lam in 𝓝 e, massCol P (0, lam) = 0)
    (hmass1 : ∀ᶠ lam in 𝓝 e,
      (fderiv ℝ (massCol P) (0, lam)).comp (ContinuousLinearMap.inl ℝ X L) = 0)
    (z : ℝ → X × L) (hz : (fun a => z a - (0, e)) =O[𝓝[>] 0] fun a => a)
    (δX : ℝ → X) (δlam : ℝ → L) (hδX : δX =O[𝓝[>] 0] fun a => a ^ 5)
    (hδlam : (fun a => δlam a - a ^ 2 • ν) =O[𝓝[>] 0] fun a => a ^ 3)
    (r : ℝ → L) (hr : r =O[𝓝[>] 0] fun _ => (1 : ℝ)) :
    (fun a => dirResidualRow P F (z a) (δX a, δlam a) (a • r a)) =O[𝓝[>] 0] fun a => a ^ 5 := by
  set p : X × L := (0, e)
  have hl : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl)
  have hzt : Tendsto z (𝓝[>] 0) (𝓝 p) := by
    have h2 := (hz.trans_tendsto hl).add_const p
    simpa using h2
  -- Ward orders
  have hP' : ContDiffAt ℝ 4 (rowX P) p :=
    (hP.fderiv_right (m := 4) (by norm_num)).clm_comp contDiffAt_const
  have hM : massRow (rowX P) p = 0 := massRow_eq_zero_of_mass P e hP hmass1.self_of_nhds
  obtain ⟨o1, o2, o3⟩ := ward_orders (rowX P) F e hP' hF hF0 hP0 hM hK1
  set B := wardRow (rowX P) F
  have a1 : (fun a => fderiv ℝ B (z a)) =O[𝓝[>] 0] fun a => a ^ 1 := o1.comp_family' z hz hl
  have a2 : (fun a => (fderiv ℝ B (z a)).comp (ContinuousLinearMap.inr ℝ X L)) =O[𝓝[>] 0]
      fun a => a ^ 2 := o2.comp_family' z hz hl
  have a3 : (fun a => (fderiv ℝ B (z a)).comp (ContinuousLinearMap.inr ℝ X L) ν) =O[𝓝[>] 0]
      fun a => a ^ 3 := (o3 ν hM2 hQ).comp_family' z hz hl
  -- mass orders
  obtain ⟨Cm, hCm⟩ := massCol_inr_bound P e hP hmass0 hmass1
  have hMc : ContDiffAt ℝ 4 (massCol P) p :=
    (hP.fderiv_right (m := 4) (by norm_num)).clm_comp contDiffAt_const
  have hDMc :=
    (hMc.fderiv_right (m := 3) (by norm_num)).continuousAt
  have m0 : (fun a => fderiv ℝ (massCol P) (z a)) =O[𝓝[>] 0] fun _ => (1 : ℝ) := by
    have := (vanishesToOrder_zero_of_continuousAt hDMc).comp_family' z hz hl
    simpa using this
  have hX : (fun a => (z a).1) =O[𝓝[>] 0] fun a => a := by
    refine (isBigO_of_le' (c := 1) _ fun a => ?_).trans hz
    rw [one_mul]
    have : (z a).1 = (z a - p).1 := by simp [p]
    rw [this]
    exact norm_fst_le _
  have m2 : (fun a => (fderiv ℝ (massCol P) (z a)).comp (ContinuousLinearMap.inr ℝ X L))
      =O[𝓝[>] 0] fun a => a ^ 2 := by
    have h1 : (fun a => (fderiv ℝ (massCol P) (z a)).comp (ContinuousLinearMap.inr ℝ X L))
        =O[𝓝[>] 0] fun a => ‖(z a).1‖ ^ 2 :=
      IsBigO.of_bound Cm ((hzt.eventually hCm).mono fun a ha => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact ha)
    exact h1.trans (hX.norm_left.pow 2)
  -- the tangent pieces
  have hν2 : (fun a : ℝ => a ^ 2 • ν) =O[𝓝[>] 0] fun a => a ^ 2 :=
    isBigO_of_le' (c := ‖ν‖) _ fun a => by rw [norm_smul, mul_comm]
  have hδlam2 : δlam =O[𝓝[>] 0] fun a => a ^ 2 := by
    have h3 : (fun a : ℝ => a ^ 3) =O[𝓝[>] 0] fun a => a ^ 2 := by
      have hb : (fun a : ℝ => a) =O[𝓝[>] 0] (fun _ => (1 : ℝ)) := hl.isBigO_one ℝ
      have := (isBigO_refl (fun a : ℝ => a ^ 2) (𝓝[>] 0)).mul hb
      simpa [pow_succ] using this
    have := (hδlam.trans h3).add hν2
    simpa using this
  have hμ : (fun a => a • r a) =O[𝓝[>] 0] fun a => a := by
    have := (isBigO_refl (fun a : ℝ => a) (𝓝[>] 0)).smul hr
    simpa using this
  -- the five terms
  have t1 : (fun a => fderiv ℝ B (z a) (ContinuousLinearMap.inl ℝ X L (δX a))) =O[𝓝[>] 0]
      fun a => a ^ 1 * a ^ 5 := by
    have hδ : (fun a => ContinuousLinearMap.inl ℝ X L (δX a)) =O[𝓝[>] 0] fun a => a ^ 5 :=
      ((ContinuousLinearMap.inl ℝ X L).isBigO_comp _ _).trans hδX
    exact isBigO_clm_apply a1 hδ
  have t2 : (fun a => (fderiv ℝ B (z a)).comp (ContinuousLinearMap.inr ℝ X L) (a ^ 2 • ν))
      =O[𝓝[>] 0] fun a => a ^ 2 * a ^ 3 := by
    have : (fun a => (fderiv ℝ B (z a)).comp (ContinuousLinearMap.inr ℝ X L) (a ^ 2 • ν)) =
        fun a => a ^ 2 • (fderiv ℝ B (z a)).comp (ContinuousLinearMap.inr ℝ X L) ν := by
      ext a; rw [map_smul]
    rw [this]
    exact (isBigO_refl (fun a : ℝ => a ^ 2) _).smul a3
  have t3 : (fun a => (fderiv ℝ B (z a)).comp (ContinuousLinearMap.inr ℝ X L)
      (δlam a - a ^ 2 • ν)) =O[𝓝[>] 0] fun a => a ^ 2 * a ^ 3 := isBigO_clm_apply a2 hδlam
  have t4 : (fun a => fderiv ℝ (massCol P) (z a) (ContinuousLinearMap.inl ℝ X L (δX a))
      (a • r a)) =O[𝓝[>] 0] fun a => (1 : ℝ) * a ^ 5 * a := by
    have hδ : (fun a => ContinuousLinearMap.inl ℝ X L (δX a)) =O[𝓝[>] 0] fun a => a ^ 5 :=
      ((ContinuousLinearMap.inl ℝ X L).isBigO_comp _ _).trans hδX
    exact isBigO_clm_apply (isBigO_clm_apply m0 hδ) hμ
  have t5 : (fun a => (fderiv ℝ (massCol P) (z a)).comp (ContinuousLinearMap.inr ℝ X L) (δlam a)
      (a • r a)) =O[𝓝[>] 0] fun a => a ^ 2 * a ^ 2 * a :=
    isBigO_clm_apply (isBigO_clm_apply m2 hδlam2) hμ
  -- reassemble
  have hsplit : ∀ a, dirResidualRow P F (z a) (δX a, δlam a) (a • r a) =
      fderiv ℝ B (z a) (ContinuousLinearMap.inl ℝ X L (δX a)) +
      (fderiv ℝ B (z a)).comp (ContinuousLinearMap.inr ℝ X L) (a ^ 2 • ν) +
      (fderiv ℝ B (z a)).comp (ContinuousLinearMap.inr ℝ X L) (δlam a - a ^ 2 • ν) +
      fderiv ℝ (massCol P) (z a) (ContinuousLinearMap.inl ℝ X L (δX a)) (a • r a) +
      (fderiv ℝ (massCol P) (z a)).comp (ContinuousLinearMap.inr ℝ X L) (δlam a) (a • r a) := by
    intro a
    have hδ : ((δX a, δlam a) : X × L) = ContinuousLinearMap.inl ℝ X L (δX a) +
        ContinuousLinearMap.inr ℝ X L (δlam a) := by simp
    simp only [dirResidualRow, ContinuousLinearMap.comp_apply, map_sub, hδ, map_add,
      add_apply, B]
    abel
  -- every comparison function is `O(a⁵)` as `a ↓ 0`
  have hb1 : (fun a : ℝ => a) =O[𝓝[>] 0] (fun _ => (1 : ℝ)) := hl.isBigO_one ℝ
  have e1 : (fun a : ℝ => a ^ 1 * a ^ 5) =O[𝓝[>] 0] fun a => a ^ 5 := by
    have := hb1.mul (isBigO_refl (fun a : ℝ => a ^ 5) (𝓝[>] 0))
    simpa using this
  have e2 : (fun a : ℝ => a ^ 2 * a ^ 3) =O[𝓝[>] 0] fun a => a ^ 5 :=
    (isBigO_refl _ _).congr_left fun a => by ring
  have e4 : (fun a : ℝ => (1 : ℝ) * a ^ 5 * a) =O[𝓝[>] 0] fun a => a ^ 5 := by
    have := (isBigO_refl (fun a : ℝ => a ^ 5) (𝓝[>] 0)).mul hb1
    simpa using this
  have e5 : (fun a : ℝ => a ^ 2 * a ^ 2 * a) =O[𝓝[>] 0] fun a => a ^ 5 :=
    (isBigO_refl _ _).congr_left fun a => by ring
  have hsum := ((((t1.trans e1).add (t2.trans e2)).add (t3.trans e2)).add (t4.trans e4)).add
    (t5.trans e5)
  exact hsum.congr_left fun a => (hsplit a).symm

/-- **`thm:supp-exact-harmonic-q4-zero`, single base.**  Under the hypotheses of
`dirResidualRow_isBigO_five`, if the constant-shift row of the directional residual is analytic
in the amplitude (power series `pq` at `0`), then its Taylor coefficients of order `≤ 4` vanish;
in particular the quartic coefficient `q₄(ξ; J_H c) = pq.coeff 4` is zero. -/
theorem harmonic_q4_zero (P : X × L → ℝ) (F : X × L → X) (e ν : L)
    (hP : ContDiffAt ℝ 5 P (0, e)) (hF : ContDiffAt ℝ 4 F (0, e))
    (hF0 : F (0, e) = 0) (hP0 : rowX P (0, e) = 0)
    (hK1 : ∀ w, (fderiv ℝ (rowX P) (0, e) w).comp
      ((fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L)) = 0)
    (hM2 : fderiv ℝ (fun z => massRow (rowX P) z ν) (0, e) = 0)
    (hQ : fderiv ℝ (fderiv ℝ (fun z => bracketRow (rowX P) F z ν)) (0, e) = 0)
    (hmass0 : ∀ᶠ lam in 𝓝 e, massCol P (0, lam) = 0)
    (hmass1 : ∀ᶠ lam in 𝓝 e,
      (fderiv ℝ (massCol P) (0, lam)).comp (ContinuousLinearMap.inl ℝ X L) = 0)
    (z : ℝ → X × L) (hz : (fun a => z a - (0, e)) =O[𝓝[>] 0] fun a => a)
    (δX : ℝ → X) (δlam : ℝ → L) (hδX : δX =O[𝓝[>] 0] fun a => a ^ 5)
    (hδlam : (fun a => δlam a - a ^ 2 • ν) =O[𝓝[>] 0] fun a => a ^ 3)
    (r : ℝ → L) (hr : r =O[𝓝[>] 0] fun _ => (1 : ℝ)) {pq : FormalMultilinearSeries ℝ ℝ ℝ}
    (hq : HasFPowerSeriesAt (fun a => dirResidualRow P F (z a) (δX a, δlam a) (a • r a)) pq 0) :
    (∀ j ≤ 4, pq.coeff j = 0) ∧ pq.coeff 4 = 0 := by
  have h := coeff_eq_zero_of_isBigO hq (dirResidualRow_isBigO_five P F e ν hP hF hF0 hP0 hK1 hM2
    hQ hmass0 hmass1 z hz δX δlam hδX hδlam r hr)
  exact ⟨fun j hj => h j (by omega), h 4 (by norm_num)⟩

/-- **`lem:supp-exact-ward-orders` with the mass order.**  `WardOrders.ward_orders` for
`P'_c = D_X P_c` of a `C⁵` constant-shift row `P_c`, with the hypothesis `D_X𝓜(0, e)[c, ·] = 0`
replaced by the displayed mass order `𝓜 = O(‖X‖²)` (`eq:supp-exact-ward-mass-order`, used here
only at `λ = e`: `D_X𝓜_c(0, e) = 0`), via `massRow_eq_zero_of_mass`. -/
theorem ward_orders_of_mass (P : X × L → ℝ) (F : X × L → X) (e : L)
    (hP : ContDiffAt ℝ 5 P (0, e)) (hF : ContDiffAt ℝ 4 F (0, e))
    (hF0 : F (0, e) = 0) (hP0 : rowX P (0, e) = 0)
    (hmass1 : (fderiv ℝ (massCol P) (0, e)).comp (ContinuousLinearMap.inl ℝ X L) = 0)
    (hK1 : ∀ w, (fderiv ℝ (rowX P) (0, e) w).comp
      ((fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L)) = 0) :
    VanishesToOrder (fderiv ℝ (wardRow (rowX P) F)) (0, e) 1 ∧
      VanishesToOrder (fun z => (fderiv ℝ (wardRow (rowX P) F) z).comp
        (ContinuousLinearMap.inr ℝ X L)) (0, e) 2 ∧
      ∀ ν : L, fderiv ℝ (fun z => massRow (rowX P) z ν) (0, e) = 0 →
        fderiv ℝ (fderiv ℝ (fun z => bracketRow (rowX P) F z ν)) (0, e) = 0 →
        VanishesToOrder (fun z => (fderiv ℝ (wardRow (rowX P) F) z).comp
          (ContinuousLinearMap.inr ℝ X L) ν) (0, e) 3 :=
  ward_orders (rowX P) F e ((hP.fderiv_right (m := 4) (by norm_num)).clm_comp contDiffAt_const)
    hF hF0 hP0 (massRow_eq_zero_of_mass P e hP hmass1) hK1

/-- Non-vacuity of the hypothesis packet of `dirResidualRow_isBigO_five` (trivial branch
`P_c = 0`, `F = 0` on `ℝ × ℝ`, with an arbitrary base family, ray tangent and rate). -/
example : (fun a : ℝ => dirResidualRow (fun _ : ℝ × ℝ => (0 : ℝ)) (fun _ => (0 : ℝ))
    ((a, 1 + a) : ℝ × ℝ) (a ^ 5, a ^ 2 * 2) (a • (1 : ℝ))) =O[𝓝[>] 0] fun a => a ^ 5 := by
  have hr : rowX (fun _ : ℝ × ℝ => (0 : ℝ)) = fun _ => 0 := by
    funext z; ext; simp [rowX]
  have hm : massCol (fun _ : ℝ × ℝ => (0 : ℝ)) = fun _ => 0 := by
    funext z; ext; simp [massCol]
  refine dirResidualRow_isBigO_five (fun _ : ℝ × ℝ => (0 : ℝ)) (fun _ => (0 : ℝ)) 1 2
    contDiffAt_const contDiffAt_const rfl (by rw [hr]) (fun w => by simp [hr])
    (by simp [massRow, hr]) (by simp [bracketRow, hr])
    (Eventually.of_forall fun _ => by rw [hm]) (Eventually.of_forall fun _ => by simp [hm])
    (fun a => (a, 1 + a)) ?_ (fun a => a ^ 5) (fun a => a ^ 2 * 2) (isBigO_refl _ _) ?_
    (fun _ => 1) (isBigO_refl _ _)
  · refine isBigO_of_le' (c := 1) _ fun a => ?_
    simp [Prod.norm_def]
  · simp only [smul_eq_mul, mul_comm, sub_self]
    exact isBigO_zero _ _

end Orders

/-- "Consequently its derivative with respect to any admissible second-record base direction also
vanishes": a quantity vanishing at every base near `ξ₀` has zero base derivative. -/
theorem q4_fderiv_eq_zero {Ξs G : Type*} [NormedAddCommGroup Ξs] [NormedSpace ℝ Ξs]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (q4 : Ξs → G) {ξ₀ : Ξs}
    (h : ∀ᶠ ξ in 𝓝 ξ₀, q4 ξ = 0) : fderiv ℝ q4 ξ₀ = 0 := by
  have : HasFDerivAt q4 (0 : Ξs →L[ℝ] G) ξ₀ :=
    (hasFDerivAt_const (0 : G) ξ₀).congr_of_eventuallyEq h
  exact this.fderiv

/-! ### Bridge to the slope chain -/

section Bridge

open ExactSlowBranch ExactSlowRankTwo

variable {R Y Zg V Xs Ho : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Zg] [NormedSpace ℝ Zg]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Xs] [NormedSpace ℝ Xs]
  [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]

/-- If at every second-record base `Ξ(q)` near `0` and for every harmonic slope `c` each row
`ℓ_i` of the harmonic derivative `D𝔠_H(Ξ(q))[J_H c]` is the quartic Taylor coefficient of an
analytic function that is `O(a⁵)` (the identification of the harmonic compatibility row with the
rescaled constant-shift row of the directional residual), and the rows separate `Ho`, then
`HarmonicAnnihilation` holds. -/
theorem harmonicAnnihilation_of_quartic {ι : Type*} (ℓ : ι → Ho →L[ℝ] ℝ)
    (hsep : ∀ y : Ho, (∀ i, ℓ i y = 0) → y = 0)
    (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cH : V → Ho)
    (hq4 : ∀ c : Y, ∀ᶠ q in 𝓝 (0 : R × Y), ∀ i, ∃ (f : ℝ → ℝ)
      (pf : FormalMultilinearSeries ℝ ℝ ℝ), HasFPowerSeriesAt f pf 0 ∧
        f =O[𝓝[>] 0] (fun a => a ^ 5) ∧
        ℓ i (fderiv ℝ cH (reducedChart E Jg JH γ q) (JH c)) = pf.coeff 4) :
    HarmonicAnnihilation E Jg JH γ cH := by
  intro c
  filter_upwards [hq4 c] with q hq
  refine hsep _ fun i => ?_
  obtain ⟨f, pf, hf, hO, hid⟩ := hq i
  rw [hid]
  exact coeff_eq_zero_of_isBigO hf hO 4 (by norm_num)

variable {X L : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]

/-- The constant-shift Ward packet for a family of literal constant-shift rows `P i`
(`i ∈ ι`, the rows `H_cᵀ`) and the harmonic multiplier directions `νH c = H_c c`. -/
structure WardPacket {ι : Type*} (P : ι → X × L → ℝ) (F : X × L → X) (e : L) (νH : Y → L) :
    Prop where
  hP : ∀ i, ContDiffAt ℝ 5 (P i) (0, e)
  hF : ContDiffAt ℝ 4 F (0, e)
  hF0 : F (0, e) = 0
  hP0 : ∀ i, rowX (P i) (0, e) = 0
  hK1 : ∀ i w, (fderiv ℝ (rowX (P i)) (0, e) w).comp
    ((fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L)) = 0
  hM2 : ∀ i c, fderiv ℝ (fun z => massRow (rowX (P i)) z (νH c)) (0, e) = 0
  hQ : ∀ i c, fderiv ℝ (fderiv ℝ (fun z => bracketRow (rowX (P i)) F z (νH c))) (0, e) = 0
  hmass0 : ∀ i, ∀ᶠ lam in 𝓝 e, massCol (P i) (0, lam) = 0
  hmass1 : ∀ i, ∀ᶠ lam in 𝓝 e,
    (fderiv ℝ (massCol (P i)) (0, lam)).comp (ContinuousLinearMap.inl ℝ X L) = 0

/-- **`thm:supp-exact-harmonic-q4-zero` ⇒ harmonic annihilation.**  Given the Ward packet, and at
every second-record base `Ξ(q)` near `0` and every `c` a base family `Q_a = (0,e) + O(a)`, a
pure-harmonic ray tangent (`δX = O(a⁵)`, `δλ = a²H_c c + O(a³)`) and a bounded rate such that the
constant-shift rows of the directional residual are analytic in `a` and their quartic
coefficients are the rows `ℓ_i` of `D𝔠_H(Ξ(q))[J_H c]`, the encoded conclusion
`HarmonicAnnihilation` of `thm:supp-exact-harmonic-q4-zero` holds. -/
theorem harmonicAnnihilation_of_ward {ι : Type*} (ℓ : ι → Ho →L[ℝ] ℝ)
    (hsep : ∀ y : Ho, (∀ i, ℓ i y = 0) → y = 0)
    (P : ι → X × L → ℝ) (F : X × L → X) (e : L) (νH : Y → L) (hW : WardPacket P F e νH)
    (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cH : V → Ho)
    (hray : ∀ c : Y, ∀ᶠ q in 𝓝 (0 : R × Y), ∃ (z : ℝ → X × L) (δX : ℝ → X) (δlam : ℝ → L)
      (r : ℝ → L), (fun a => z a - (0, e)) =O[𝓝[>] 0] (fun a => a) ∧
        δX =O[𝓝[>] 0] (fun a => a ^ 5) ∧
        (fun a => δlam a - a ^ 2 • νH c) =O[𝓝[>] 0] (fun a => a ^ 3) ∧
        r =O[𝓝[>] 0] (fun _ => (1 : ℝ)) ∧
        ∀ i, ∃ pq : FormalMultilinearSeries ℝ ℝ ℝ,
          HasFPowerSeriesAt (fun a => dirResidualRow (P i) F (z a) (δX a, δlam a) (a • r a)) pq 0 ∧
          ℓ i (fderiv ℝ cH (reducedChart E Jg JH γ q) (JH c)) = pq.coeff 4) :
    HarmonicAnnihilation E Jg JH γ cH := by
  refine harmonicAnnihilation_of_quartic ℓ hsep E Jg JH γ cH fun c => ?_
  filter_upwards [hray c] with q hq
  obtain ⟨z, δX, δlam, r, hz, hδX, hδlam, hr, hrow⟩ := hq
  intro i
  obtain ⟨pq, hpq, hid⟩ := hrow i
  exact ⟨_, pq, hpq, dirResidualRow_isBigO_five (P i) F e (νH c) (hW.hP i) hW.hF hW.hF0
    (hW.hP0 i) (hW.hK1 i) (hW.hM2 i c) (hW.hQ i c) (hW.hmass0 i) (hW.hmass1 i) z hz δX δlam hδX
    hδlam r hr, hid⟩

/-- The harmonic slope-entrance identity `D𝔠_H(0)J_H = 0` of `eq:supp-exact-slope-entrance`
from the annihilation at the base `0` (`Ξ(0) = 0`). -/
theorem harmonic_slope_entrance (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V)
    (γ : R × Y → Zg) (cH : V → Ho) (hγ0 : γ 0 = 0) (hW : HarmonicAnnihilation E Jg JH γ cH)
    (c : Y) : fderiv ℝ cH 0 (JH c) = 0 := by
  have h := (hW c).self_of_nhds
  simpa [reducedChart, hγ0] using h

/-- **`thm:supp-exact-rank-two-factorization` from the Ward packet**: the factorization
`𝒬_can(c) = q_{0,can} - 𝒞ℛ(c)` with `HarmonicAnnihilation` discharged by
`harmonicAnnihilation_of_ward`. -/
theorem slopeCan_rank_two_factorization_of_ward {ι : Type*} (ℓ : ι → Ho →L[ℝ] ℝ)
    (hsep : ∀ y : Ho, (∀ i, ℓ i y = 0) → y = 0)
    (P : ι → X × L → ℝ) (F : X × L → X) (e : L) (νH : Y → L) (hWd : WardPacket P F e νH)
    (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cg : V → Zg)
    (cH : V → Ho) (f : V → Xs) (LX : Xs →L[ℝ] R) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z)
    (hray : ∀ c : Y, ∀ᶠ q in 𝓝 (0 : R × Y), ∃ (z : ℝ → X × L) (δX : ℝ → X) (δlam : ℝ → L)
      (r : ℝ → L), (fun a => z a - (0, e)) =O[𝓝[>] 0] (fun a => a) ∧
        δX =O[𝓝[>] 0] (fun a => a ^ 5) ∧
        (fun a => δlam a - a ^ 2 • νH c) =O[𝓝[>] 0] (fun a => a ^ 3) ∧
        r =O[𝓝[>] 0] (fun _ => (1 : ℝ)) ∧
        ∀ i, ∃ pq : FormalMultilinearSeries ℝ ℝ ℝ,
          HasFPowerSeriesAt (fun a => dirResidualRow (P i) F (z a) (δX a, δlam a) (a • r a)) pq 0 ∧
          ℓ i (fderiv ℝ cH (reducedChart E Jg JH γ q) (JH c)) = pq.coeff 4)
    (v : R) (c : Y) :
    slopeCan E Jg JH γ cH f LX v c
      = slopeCan E Jg JH γ cH f LX v 0
        - scriptC ((fderiv ℝ cH 0).comp Jg) AgInv
            (scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v) c) :=
  slopeCan_rank_two_factorization E Jg JH γ cg cH f LX AgInv hγ hγ0 hcg hcH hf himp hJH hAg
    (harmonicAnnihilation_of_ward ℓ hsep P F e νH hWd E Jg JH γ cH hray) v c

end Bridge

end HarmonicQuartic
end RenewalGeometry

end
