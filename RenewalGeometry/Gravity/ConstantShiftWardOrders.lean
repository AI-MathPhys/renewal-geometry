/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Vanishing orders and the constant-shift Ward orders
  (`lem:supp-exact-ward-orders`, `eq:supp-exact-ward-orders`, `eq:supp-exact-ward-objects`,
  `eq:supp-exact-ward-mass-order`, `eq:supp-exact-harmonic-mass-column`;
  emergent-spacetime manuscript)

## Vanishing-order calculus (general)
`VanishesToOrder f p k` means `‖f z‖ = O(‖z - p‖ᵏ)` as `z → p`.
* `vanishesToOrder_zero_of_continuousAt`, `vanishesToOrder_one_of_differentiableAt`;
* `VanishesToOrder.succ_of_fderiv` (mean-value step: `f p = 0` and `Df` of order `k` give
  order `k + 1`), and its iterates `vanishesToOrder_two`, `vanishesToOrder_three`;
* product rules `VanishesToOrder.clm_apply`, `VanishesToOrder.clm_comp`,
  `VanishesToOrder.clm_flip_apply`, linear post-composition, sums;
* `VanishesToOrder.comp_curve`: along a curve `z_a = p + O(a)`, `f(z_a) = O(aᵏ)`.

## The constant-shift Ward orders
For the canonical vector field `F = F^can` and the `X`-derivative `P'_c = D_X P_c` of a
constant-shift constraint row, on `E = 𝒳 × Λ` near `p = (0, e)`, put
`ℬ_c(z) = P'_c(z) F(z)` (`eq:supp-exact-ward-objects`).  Then
`D ℬ_c = P'_c ∘ DF + (DP'_c)ᵀ F`, so `D_λ ℬ_c[ν] = P'_c D_λF[ν] + D_λ P'_c[ν] F`, i.e.
`{P_c, P_ν} + D_X 𝓜[c, ν] F^can` as in the paper's proof.  `ward_orders` proves, under the
finite coefficient identities that the paper's proof uses, written at the level of
derivatives at `p`:
* `F(p) = 0` (`F^can(0, e) = 0`);
* `P'_c(p) = 0` (`P_{c,1} = 0`);
* `D_λ P'_c(p) = 0` (`D_X 𝓜(0, e)[c, ·] = 0`, from `𝓜 = O(‖X‖²)`);
* `DP'_c(p)[w] ∘ D_λF(p) = 0` for all `w` (the linear first-Poisson coefficient of
  `{P_c, P_ν}` vanishes: `𝕂₁(Y) c = 0`, together with `D_λ P'_c(p) = 0`);
* for the third clause, with `ν = H_c d`: `D(D_λ P'_c[ν])(p) = 0` (`𝓜₂(X, e) c = 0` for all
  `X`) and `D²{P_c, P_ν}(p) = 0` (the quadratic bracket of two commuting phase translations
  `⟨p, δ_c U⟩`, `⟨p, δ_d U⟩` vanishes, `[δ_c, δ_d] = 0`; see
  `ExactThreeSite.phaseDeriv_comb_comm` for the three-site commutation),
the estimates `‖D ℬ_c‖ = O(‖z - p‖)` (hence `‖D_X ℬ_c‖ = O(a)`),
`‖D_λ ℬ_c‖ = O(‖z - p‖²)` and `D_λ ℬ_c[H_c d] = O(‖z - p‖³)` on a neighbourhood of `p`
(uniform), hence `O(a), O(a²), O(a³)` along every family `X_a = aY + O(a²)`,
`λ_a = e + O(a)` (`ward_orders_along`).

Status: the coefficient identities are taken as hypotheses on abstract `C⁴` maps; the
paper asserts them for its explicit finite action, which is not written in the paper and is
not encoded in Lean.
-/

open Filter Topology Asymptotics Metric

namespace RenewalGeometry
namespace WardOrders

section Vanishing

variable {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- `f` vanishes to order `k` at `p`: `‖f z‖ = O(‖z - p‖ᵏ)` as `z → p`. -/
def VanishesToOrder (f : E → G) (p : E) (k : ℕ) : Prop :=
  f =O[𝓝 p] fun z => ‖z - p‖ ^ k

theorem vanishesToOrder_zero_of_continuousAt {f : E → G} {p : E} (hf : ContinuousAt f p) :
    VanishesToOrder f p 0 := by
  unfold VanishesToOrder
  simp only [pow_zero]
  exact hf.tendsto.isBigO_one ℝ

theorem vanishesToOrder_one_of_differentiableAt {f : E → G} {p : E}
    (hf : DifferentiableAt ℝ f p) (h0 : f p = 0) : VanishesToOrder f p 1 := by
  unfold VanishesToOrder
  have h := hf.hasFDerivAt.isBigO_sub
  simp only [h0, sub_zero] at h
  simpa using h.norm_right

/-- **Mean-value step.** If `f` is differentiable near `p`, `f p = 0`, and `Df` vanishes to
order `k`, then `f` vanishes to order `k + 1`. -/
theorem VanishesToOrder.succ_of_fderiv {f : E → G} {p : E} {k : ℕ}
    (hdiff : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ f z) (h0 : f p = 0)
    (hD : VanishesToOrder (fderiv ℝ f) p k) : VanishesToOrder f p (k + 1) := by
  obtain ⟨C, hCpos, hC⟩ := hD.exists_pos
  rw [IsBigOWith] at hC
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hdiff.and hC)
  unfold VanishesToOrder
  refine IsBigO.of_bound C ?_
  filter_upwards [Metric.ball_mem_nhds p hr] with z hz
  set s := closedBall p ‖z - p‖ ∩ ball p r
  have hs : Convex ℝ s := (convex_closedBall _ _).inter (convex_ball _ _)
  have hps : p ∈ s := ⟨mem_closedBall_self (norm_nonneg _), mem_ball_self hr⟩
  have hzs : z ∈ s := ⟨by rw [mem_closedBall, dist_eq_norm], hz⟩
  have hbound : ∀ w ∈ s, ‖fderiv ℝ f w‖ ≤ C * ‖z - p‖ ^ k := by
    intro w hw
    have h1 := (hball w hw.2).2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCpos.le)
    have : ‖w - p‖ ≤ ‖z - p‖ := by
      have := hw.1
      rwa [mem_closedBall, dist_eq_norm] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this k
  have hmv := hs.norm_image_sub_le_of_norm_fderiv_le (fun w hw => (hball w hw.2).1) hbound
    hps hzs
  rw [h0, sub_zero] at hmv
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_succ, ← mul_assoc]
  exact hmv

/-- Order two from a vanishing value and derivative. -/
theorem vanishesToOrder_two {f : E → G} {p : E}
    (hdiff : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ f z) (hD : DifferentiableAt ℝ (fderiv ℝ f) p)
    (h0 : f p = 0) (h1 : fderiv ℝ f p = 0) : VanishesToOrder f p 2 :=
  VanishesToOrder.succ_of_fderiv hdiff h0 (vanishesToOrder_one_of_differentiableAt hD h1)

/-- Order three from vanishing value, first and second derivatives. -/
theorem vanishesToOrder_three {f : E → G} {p : E}
    (hdiff : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ f z)
    (hdiff1 : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ (fderiv ℝ f) z)
    (hD2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) p)
    (h0 : f p = 0) (h1 : fderiv ℝ f p = 0) (h2 : fderiv ℝ (fderiv ℝ f) p = 0) :
    VanishesToOrder f p 3 :=
  VanishesToOrder.succ_of_fderiv hdiff h0 (vanishesToOrder_two hdiff1 hD2 h1 h2)

theorem VanishesToOrder.of_norm_le {f : E → G} {g : E → H} {p : E} {k : ℕ} (C : ℝ)
    (hf : VanishesToOrder f p k) (hle : ∀ᶠ z in 𝓝 p, ‖g z‖ ≤ C * ‖f z‖) :
    VanishesToOrder g p k :=
  (IsBigO.of_bound C hle).trans hf

theorem VanishesToOrder.add {f g : E → G} {p : E} {k : ℕ} (hf : VanishesToOrder f p k)
    (hg : VanishesToOrder g p k) : VanishesToOrder (f + g) p k :=
  IsBigO.add hf hg

/-- Product rule for evaluation: orders add. -/
theorem VanishesToOrder.clm_apply {A : E → G →L[ℝ] H} {v : E → G} {p : E} {m n : ℕ}
    (hA : VanishesToOrder A p m) (hv : VanishesToOrder v p n) :
    VanishesToOrder (fun z => A z (v z)) p (m + n) := by
  have h1 : (fun z => A z (v z)) =O[𝓝 p] fun z => ‖A z‖ * ‖v z‖ :=
    IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (A z).le_opNorm (v z))
  have h2 : (fun z => ‖A z‖ * ‖v z‖) =O[𝓝 p] fun z => ‖z - p‖ ^ m * ‖z - p‖ ^ n :=
    hA.norm_left.mul hv.norm_left
  unfold VanishesToOrder
  simpa [pow_add] using h1.trans h2

/-- Product rule for composition: orders add. -/
theorem VanishesToOrder.clm_comp {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {A : E → G →L[ℝ] H} {B : E → G' →L[ℝ] G} {p : E} {m n : ℕ}
    (hA : VanishesToOrder A p m) (hB : VanishesToOrder B p n) :
    VanishesToOrder (fun z => (A z).comp (B z)) p (m + n) := by
  have h1 : (fun z => (A z).comp (B z)) =O[𝓝 p] fun z => ‖A z‖ * ‖B z‖ :=
    IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (A z).opNorm_comp_le (B z))
  have h2 : (fun z => ‖A z‖ * ‖B z‖) =O[𝓝 p] fun z => ‖z - p‖ ^ m * ‖z - p‖ ^ n :=
    hA.norm_left.mul hB.norm_left
  unfold VanishesToOrder
  simpa [pow_add] using h1.trans h2

/-- Product rule for a flipped bilinear evaluation: orders add. -/
theorem VanishesToOrder.clm_flip_apply {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {L : E → G' →L[ℝ] G →L[ℝ] H} {v : E → G} {p : E} {m n : ℕ}
    (hL : VanishesToOrder L p m) (hv : VanishesToOrder v p n) :
    VanishesToOrder (fun z => (L z).flip (v z)) p (m + n) := by
  have hL' : VanishesToOrder (fun z => (L z).flip) p m :=
    hL.of_norm_le 1 (Eventually.of_forall fun z => by
      rw [ContinuousLinearMap.opNorm_flip, one_mul])
  exact hL'.clm_apply hv

/-- Post-composition with a fixed continuous linear map preserves the order. -/
theorem VanishesToOrder.map {f : E → G} {p : E} {k : ℕ} (T : G →L[ℝ] H)
    (hf : VanishesToOrder f p k) : VanishesToOrder (fun z => T (f z)) p k :=
  (T.isBigO_comp f (𝓝 p)).trans hf

/-- **Along curves.** If `f` vanishes to order `k` at `p` and `z_a - p = O(a)` as `a → 0`, then
`f(z_a) = O(aᵏ)`. -/
theorem VanishesToOrder.comp_curve {f : E → G} {p : E} {k : ℕ} (hf : VanishesToOrder f p k)
    (z : ℝ → E) (hz : (fun a => z a - p) =O[𝓝 0] fun a => a) :
    (fun a => f (z a)) =O[𝓝 0] fun a => a ^ k := by
  have ht : Tendsto z (𝓝 0) (𝓝 p) := by
    have h0 : Tendsto (fun a : ℝ => a) (𝓝 0) (𝓝 0) := tendsto_id
    have := hz.trans_tendsto h0
    have h2 := this.add_const p
    simpa using h2
  have h1 : (fun a => f (z a)) =O[𝓝 0] fun a => ‖z a - p‖ ^ k := hf.comp_tendsto ht
  have h2 : (fun a => ‖z a - p‖ ^ k) =O[𝓝 0] fun a => a ^ k :=
    hz.norm_left.pow k
  exact h1.trans h2

end Vanishing

/-! ## The constant-shift Ward orders -/

section Ward

variable {X L : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- `ℬ_c(z) = D_X P_c(z) F^can(z)` (`eq:supp-exact-ward-objects`), with `Pc' = D_X P_c`. -/
def wardRow (Pc' : X × L → X →L[ℝ] ℝ) (F : X × L → X) (z : X × L) : ℝ := Pc' z (F z)

/-- The derivative of `ℬ_c`: `Dℬ_c = P'_c ∘ DF + (DP'_c)ᵀ F`. -/
theorem wardRow_hasFDerivAt {Pc' : X × L → X →L[ℝ] ℝ} {F : X × L → X} {z : X × L}
    (hP : DifferentiableAt ℝ Pc' z) (hF : DifferentiableAt ℝ F z) :
    HasFDerivAt (wardRow Pc' F)
      ((Pc' z).comp (fderiv ℝ F z) + (fderiv ℝ Pc' z).flip (F z)) z :=
  hP.hasFDerivAt.clm_apply hF.hasFDerivAt

/-- The first Poisson bracket row `{P_c, P_ν}(z) = P'_c(z) ∘ D_λ F(z)` as a function of `ν`. -/
noncomputable def bracketRow (Pc' : X × L → X →L[ℝ] ℝ) (F : X × L → X) (z : X × L) : L →L[ℝ] ℝ :=
  (Pc' z).comp ((fderiv ℝ F z).comp (ContinuousLinearMap.inr ℝ X L))

/-- The mass row `D_X 𝓜[c, ·]`, i.e. `D_λ P'_c(z) : L → (X →L ℝ)`. -/
noncomputable def massRow (Pc' : X × L → X →L[ℝ] ℝ) (z : X × L) : L →L[ℝ] X →L[ℝ] ℝ :=
  (fderiv ℝ Pc' z).comp (ContinuousLinearMap.inr ℝ X L)

theorem wardRow_fderiv_inr {Pc' : X × L → X →L[ℝ] ℝ} {F : X × L → X} {z : X × L}
    (hP : DifferentiableAt ℝ Pc' z) (hF : DifferentiableAt ℝ F z) :
    (fderiv ℝ (wardRow Pc' F) z).comp (ContinuousLinearMap.inr ℝ X L)
      = bracketRow Pc' F z + (massRow Pc' z).flip (F z) := by
  rw [(wardRow_hasFDerivAt hP hF).fderiv]
  ext ν
  simp [bracketRow, massRow]

variable [CompleteSpace X] [CompleteSpace L]

/-- **`lem:supp-exact-ward-orders` (neighbourhood form).**  Let `F` (canonical vector field)
and `P'_c = D_X P_c` be `C⁴` near `p = (0, e)` and assume the finite coefficient identities
`F(p) = 0`, `P'_c(p) = 0` (`P_{c,1} = 0`), `D_λ P'_c(p) = 0` (`D_X 𝓜(0, e)[c, ·] = 0`), and
`DP'_c(p)[w] ∘ D_λF(p) = 0` for every `w` (vanishing linear first-Poisson coefficient).  Then
on a neighbourhood of `p`:
1. `‖Dℬ_c(z)‖ = O(‖z - p‖)` (in particular `‖D_Xℬ_c‖`);
2. `‖D_λℬ_c(z)‖ = O(‖z - p‖²)`;
3. if moreover, for the constant shift `ν = H_c d`, `D(D_λP'_c[ν])(p) = 0`
   (`𝓜₂(X, e) c = 0`) and `D²{P_c, P_ν}(p) = 0` (commuting phase translations), then
   `D_λℬ_c(z)[ν] = O(‖z - p‖³)`. -/
theorem ward_orders (Pc' : X × L → X →L[ℝ] ℝ) (F : X × L → X) (e : L)
    (hP : ContDiffAt ℝ 4 Pc' (0, e)) (hF : ContDiffAt ℝ 4 F (0, e))
    (hF0 : F (0, e) = 0) (hP0 : Pc' (0, e) = 0) (hM : massRow Pc' (0, e) = 0)
    (hK1 : ∀ w, (fderiv ℝ Pc' (0, e) w).comp
      ((fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L)) = 0) :
    VanishesToOrder (fderiv ℝ (wardRow Pc' F)) (0, e) 1 ∧
      VanishesToOrder (fun z => (fderiv ℝ (wardRow Pc' F) z).comp
        (ContinuousLinearMap.inr ℝ X L)) (0, e) 2 ∧
      ∀ ν : L, fderiv ℝ (fun z => massRow Pc' z ν) (0, e) = 0 →
        fderiv ℝ (fderiv ℝ (fun z => bracketRow Pc' F z ν)) (0, e) = 0 →
        VanishesToOrder (fun z => (fderiv ℝ (wardRow Pc' F) z).comp
          (ContinuousLinearMap.inr ℝ X L) ν) (0, e) 3 := by
  set p : X × L := (0, e)
  -- regularity near `p`
  have hPev := hP.eventually (by simp)
  have hFev := hF.eventually (by simp)
  have hPd : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ Pc' z :=
    hPev.mono fun z hz => hz.differentiableAt (by simp)
  have hFd : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ F z :=
    hFev.mono fun z hz => hz.differentiableAt (by simp)
  -- derivatives are `C³` resp. `C²` near `p`
  have hDP : ContDiffAt ℝ 3 (fderiv ℝ Pc') p := hP.fderiv_right (by norm_num)
  have hDF : ContDiffAt ℝ 3 (fderiv ℝ F) p := hF.fderiv_right (by norm_num)
  have hDPev := hDP.eventually (by simp)
  have hDFev := hDF.eventually (by simp)
  -- basic orders
  have oF1 : VanishesToOrder F p 1 :=
    vanishesToOrder_one_of_differentiableAt (hF.differentiableAt (by simp)) hF0
  have oP1 : VanishesToOrder Pc' p 1 :=
    vanishesToOrder_one_of_differentiableAt (hP.differentiableAt (by simp)) hP0
  have oDF0 : VanishesToOrder (fderiv ℝ F) p 0 :=
    vanishesToOrder_zero_of_continuousAt hDF.continuousAt
  have oDP0 : VanishesToOrder (fderiv ℝ Pc') p 0 :=
    vanishesToOrder_zero_of_continuousAt hDP.continuousAt
  -- the derivative formula holds near `p`
  have hformula : ∀ᶠ z in 𝓝 p, fderiv ℝ (wardRow Pc' F) z
      = (Pc' z).comp (fderiv ℝ F z) + (fderiv ℝ Pc' z).flip (F z) := by
    filter_upwards [hPd, hFd] with z h1 h2
    exact (wardRow_hasFDerivAt h1 h2).fderiv
  have hformula' : ∀ᶠ z in 𝓝 p, (fderiv ℝ (wardRow Pc' F) z).comp
      (ContinuousLinearMap.inr ℝ X L) = bracketRow Pc' F z + (massRow Pc' z).flip (F z) := by
    filter_upwards [hPd, hFd] with z h1 h2
    exact wardRow_fderiv_inr h1 h2
  refine ⟨?_, ?_, ?_⟩
  · -- clause 1
    have h1 : VanishesToOrder (fun z => (Pc' z).comp (fderiv ℝ F z)) p 1 := by
      simpa using oP1.clm_comp oDF0
    have h2 : VanishesToOrder (fun z => (fderiv ℝ Pc' z).flip (F z)) p 1 := by
      simpa using oDP0.clm_flip_apply oF1
    exact (h1.add h2).congr' (hformula.mono fun z hz => hz.symm) EventuallyEq.rfl
  · -- clause 2: the bracket row vanishes to order two, the mass row to order one
    have hbr_d : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ (bracketRow Pc' F) z := by
      filter_upwards [hPev, hDFev] with z h1 h2
      exact (h1.differentiableAt (by simp)).clm_comp
        ((h2.differentiableAt (by simp)).clm_comp (differentiableAt_const _))
    have hbr_fd : HasFDerivAt (bracketRow Pc' F) (0 : X × L →L[ℝ] L →L[ℝ] ℝ) p := by
      have h := (hP.differentiableAt (by simp)).hasFDerivAt.clm_comp
        ((hDF.differentiableAt (by simp)).hasFDerivAt.clm_comp
          (hasFDerivAt_const (ContinuousLinearMap.inr ℝ X L) p))
      refine h.congr_fderiv ?_
      refine ContinuousLinearMap.ext fun w => ContinuousLinearMap.ext fun ν => ?_
      have := congrArg (fun T => T ν) (hK1 w)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
      simp [hP0]
      simpa using this
    have hbr_D : DifferentiableAt ℝ (fderiv ℝ (bracketRow Pc' F)) p := by
      have hc : ContDiffAt ℝ 2 (bracketRow Pc' F) p := by
        have h1 : ContDiffAt ℝ 2 Pc' p := hP.of_le (by norm_num)
        have h2 : ContDiffAt ℝ 2 (fderiv ℝ F) p := hDF.of_le (by norm_num)
        exact h1.clm_comp (h2.clm_comp contDiffAt_const)
      exact (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    have obr : VanishesToOrder (bracketRow Pc' F) p 2 :=
      vanishesToOrder_two hbr_d hbr_D (by simp [bracketRow, p, hP0]) hbr_fd.fderiv
    have omass : VanishesToOrder (massRow Pc') p 1 := by
      have hd : DifferentiableAt ℝ (massRow Pc') p := by
        show DifferentiableAt ℝ (fun z => (fderiv ℝ Pc' z).comp (ContinuousLinearMap.inr ℝ X L)) p
        exact (hDP.differentiableAt (by simp)).clm_comp
          (differentiableAt_const (ContinuousLinearMap.inr ℝ X L))
      exact vanishesToOrder_one_of_differentiableAt hd hM
    have h2 : VanishesToOrder (fun z => (massRow Pc' z).flip (F z)) p 2 :=
      omass.clm_flip_apply oF1
    exact (obr.add h2).congr' (hformula'.mono fun z hz => hz.symm) EventuallyEq.rfl
  · -- clause 3
    intro ν hM2 hQ
    have hformula'' : ∀ᶠ z in 𝓝 p, (fderiv ℝ (wardRow Pc' F) z).comp
        (ContinuousLinearMap.inr ℝ X L) ν = bracketRow Pc' F z ν + massRow Pc' z ν (F z) := by
      filter_upwards [hformula'] with z hz
      rw [hz]
      rfl
    -- the bracket row at `ν` vanishes to order three
    set b : X × L → ℝ := fun z => bracketRow Pc' F z ν
    have hb3 : ContDiffAt ℝ 3 b p := by
      have h1 : ContDiffAt ℝ 3 Pc' p := hP.of_le (by norm_num)
      exact (h1.clm_comp (hDF.clm_comp contDiffAt_const)).clm_apply contDiffAt_const
    have hbev := hb3.eventually (by simp)
    have hbd : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ b z :=
      hbev.mono fun z hz => hz.differentiableAt (by simp)
    have hbd1 : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ (fderiv ℝ b) z :=
      hbev.mono fun z hz => (hz.fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp)
    have hbd2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ b)) p := by
      have : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ b)) p :=
        (hb3.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
      exact this.differentiableAt (by simp)
    have hb1 : fderiv ℝ b p = 0 := by
      have h := (hP.differentiableAt (by simp)).hasFDerivAt.clm_comp
        ((hDF.differentiableAt (by simp)).hasFDerivAt.clm_comp
          (hasFDerivAt_const (ContinuousLinearMap.inr ℝ X L) p))
      have h' : HasFDerivAt b _ p := h.clm_apply (hasFDerivAt_const ν p)
      rw [h'.fderiv]
      refine ContinuousLinearMap.ext fun w => ?_
      have := congrArg (fun T => T ν) (hK1 w)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.zero_apply]
      simp [hP0]
      simpa using this
    have ob : VanishesToOrder b p 3 :=
      vanishesToOrder_three hbd hbd1 hbd2 (by simp [b, bracketRow, p, hP0]) hb1 hQ
    -- the mass row at `ν` vanishes to order two
    set mν : X × L → X →L[ℝ] ℝ := fun z => massRow Pc' z ν
    have hm2 : ContDiffAt ℝ 3 mν p :=
      (hDP.clm_comp contDiffAt_const).clm_apply contDiffAt_const
    have hmev := hm2.eventually (by simp)
    have om : VanishesToOrder mν p 2 :=
      vanishesToOrder_two (hmev.mono fun z hz => hz.differentiableAt (by simp))
        ((hm2.fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp))
        (by simp [mν, hM]) hM2
    have h2 : VanishesToOrder (fun z => mν z (F z)) p 3 := om.clm_apply oF1
    exact (ob.add h2).congr' (hformula''.mono fun z hz => hz.symm) EventuallyEq.rfl

/-- **`eq:supp-exact-ward-orders` along the amplitude family.**  For every family
`z_a = (X_a, λ_a)` with `z_a - (0, e) = O(a)` (e.g. `X_a = aY + O(a²)`, `λ_a = e + O(a)`):
`‖D_Xℬ_c‖ = O(a)`, `‖D_λℬ_c‖ = O(a²)`, and, under the two second-order identities of
`ward_orders`, `D_λℬ_c[H_c d] = O(a³)`. -/
theorem ward_orders_along (Pc' : X × L → X →L[ℝ] ℝ) (F : X × L → X) (e : L)
    (hP : ContDiffAt ℝ 4 Pc' (0, e)) (hF : ContDiffAt ℝ 4 F (0, e))
    (hF0 : F (0, e) = 0) (hP0 : Pc' (0, e) = 0) (hM : massRow Pc' (0, e) = 0)
    (hK1 : ∀ w, (fderiv ℝ Pc' (0, e) w).comp
      ((fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L)) = 0)
    (z : ℝ → X × L) (hz : (fun a => z a - (0, e)) =O[𝓝 0] fun a => a) :
    (fun a => (fderiv ℝ (wardRow Pc' F) (z a)).comp (ContinuousLinearMap.inl ℝ X L))
        =O[𝓝 0] (fun a => a) ∧
      (fun a => (fderiv ℝ (wardRow Pc' F) (z a)).comp (ContinuousLinearMap.inr ℝ X L))
        =O[𝓝 0] (fun a => a ^ 2) ∧
      ∀ ν : L, fderiv ℝ (fun z => massRow Pc' z ν) (0, e) = 0 →
        fderiv ℝ (fderiv ℝ (fun z => bracketRow Pc' F z ν)) (0, e) = 0 →
        (fun a => (fderiv ℝ (wardRow Pc' F) (z a)).comp
          (ContinuousLinearMap.inr ℝ X L) ν) =O[𝓝 0] (fun a => a ^ 3) := by
  obtain ⟨o1, o2, o3⟩ := ward_orders Pc' F e hP hF hF0 hP0 hM hK1
  refine ⟨?_, ?_, fun ν h1 h2 => (o3 ν h1 h2).comp_curve z hz⟩
  · have := ((o1.map ((ContinuousLinearMap.compL ℝ X (X × L) ℝ).flip
      (ContinuousLinearMap.inl ℝ X L))).comp_curve z hz)
    simpa using this
  · exact o2.comp_curve z hz

/-- Non-vacuity: the hypothesis packet of `ward_orders` is satisfiable (here by the trivial
branch `F = 0`, `P'_c = 0` on `ℝ × ℝ`). -/
example : VanishesToOrder (fderiv ℝ (wardRow (fun _ : ℝ × ℝ => (0 : ℝ →L[ℝ] ℝ))
    (fun _ => (0 : ℝ)))) ((0 : ℝ), (1 : ℝ)) 1 :=
  (ward_orders (fun _ : ℝ × ℝ => (0 : ℝ →L[ℝ] ℝ)) (fun _ => (0 : ℝ)) 1 contDiffAt_const
    contDiffAt_const rfl rfl (by ext; simp [massRow]) (fun w => by simp)).1

end Ward

end WardOrders
end RenewalGeometry
