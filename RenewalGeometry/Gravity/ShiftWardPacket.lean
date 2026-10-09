/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.HarmonicQuarticAnnihilation

/-!
# The constant-shift Ward packet from a quadratic-plus-cubic shift structure
  (`lem:supp-exact-ward-orders`, `eq:supp-exact-ward-orders`, `eq:supp-exact-ward-mass-order`,
  `eq:supp-exact-harmonic-mass-column`, `thm:supp-exact-harmonic-q4-zero`; emergent-spacetime
  manuscript)

General machinery (abstract finite-dimensional `X`, `L`, analytic Hamiltonian `H : X × L → ℝ`,
`F = 𝕁∇_X H` through a fixed linear map `J`, constant-shift directions `ν c`, rows
`P_c = ∂_λH[ν c]`):

* `cubic_point`: an analytic function that is `O(‖z - p‖³)` has vanishing value, first and second
  derivative at `p` (power series + polarization).
* `slice_cubic`: if `‖Q(X, λ)‖ ≤ C‖X‖³` near `(0, e)`, then for every `λ` near `e`: `Q(0, λ) = 0`,
  `D_XQ(0, λ) = 0`, `D_X²Q(0, λ) = 0`.
* **`ShiftStructure`** (hypothesis packet): `P_c(X, λ) = q_c(X) + O(‖X‖³)` uniformly in `λ`, with a
  quadratic form `q_c(X) = B_c(X, X)` whose gradients Poisson-commute, `{q_c, q_d} = 0`, and
  `F(0, e) = 0`.  From it, **`wardPacket_of_shift`** derives every field of the constant-shift
  Ward packet except the linear first-Poisson coefficient: `P_{c,1} = 0`, `𝓜₂(X, e)c = 0`, the
  vanishing quadratic bracket, the uniform mass order `𝓜 = O(‖X‖²)` on the slice, and
  `D_λF(0, e)[ν c] = 0`; **`K1_eq`**: the linear first-Poisson coefficient at a first field `Y` is
  `(B_c Y + B_cᵀY)(J D_X D_λH(0, e)[·, μ])`.

The Ward orders along the first-field ray (`ward_orders_ray`) and the quartic count
(`dirResidualRow_isBigO_five_ray`, `harmonic_q4_zero_ray`) use the linear first-Poisson
coefficient **only at the first field `Y`** of the base family `X_a = aY + O(a²)`, as the
manuscript's displayed identity `𝕂₁(Y)c = 0` does; the uniform version used by
`HarmonicQuartic.WardPacket` (`∀ w`) is not satisfied by the literal Hamiltonian (see
`Gravity/ExactWardPacketLiteral.lean`).
-/

open Filter Set Asymptotics Finset Metric
open scoped Topology ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace ShiftWardPacket

open WardOrders HarmonicQuartic

/-! ### Cubic vanishing of analytic functions -/

section Cubic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **An analytic function that is `O(‖z - p‖³)` has vanishing `0`-, `1`- and `2`-jets at `p`.** -/
theorem cubic_point {f : E → ℝ} {p : E} (hf : AnalyticAt ℝ f p) (h3 : VanishesToOrder f p 3) :
    f p = 0 ∧ fderiv ℝ f p = 0 ∧ fderiv ℝ (fderiv ℝ f) p = 0 := by
  obtain ⟨pf, r, hp⟩ := hf
  -- the partial sum of order three is `O(‖y‖³)`
  have hps : (fun y : E => pf.partialSum 3 y) =O[𝓝 0] fun y => ‖y‖ ^ 3 := by
    have h1 := hp.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 3
    have h2 : (fun y : E => f (p + y)) =O[𝓝 0] fun y => ‖y‖ ^ 3 := by
      have ht : Tendsto (fun y : E => p + y) (𝓝 0) (𝓝 p) := by
        have hc : Continuous (fun y : E => p + y) := by fun_prop
        simpa using hc.tendsto 0
      refine (h3.comp_tendsto ht).trans (IsBigO.of_bound 1 (Eventually.of_forall fun y => ?_))
      simp
    have := h2.sub h1
    simpa using this
  -- along every ray the homogeneous terms vanish
  have hcoef : ∀ v : E, ∀ m < 3, pf m (fun _ => v) = 0 := by
    intro v
    have hray : (fun t : ℝ => pf.partialSum 3 (t • v)) =O[𝓝 0] fun t => ‖t • v‖ ^ 3 := by
      have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
        have hc : Continuous (fun t : ℝ => t • v) := by fun_prop
        simpa using hc.tendsto 0
      exact hps.comp_tendsto ht
    have hpoly : ∀ t : ℝ, pf.partialSum 3 (t • v) = ∑ m ∈ range 3, t ^ m • pf m (fun _ => v) := by
      intro t
      simp only [FormalMultilinearSeries.partialSum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show (fun _ : Fin m => t • v) = fun i : Fin m => (fun _ => t) i • (fun _ => v) i from rfl,
        ContinuousMultilinearMap.map_smul_univ]
      simp [Finset.prod_const]
    obtain ⟨C, hC⟩ := hray.bound
    refine AnalyticCauchy.poly_coeff_eq_zero_of_eventually 3 (fun m => pf m (fun _ => v))
      (C * ‖v‖ ^ 3) ?_
    filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with t ht htpos
    rw [← hpoly]
    calc ‖pf.partialSum 3 (t • v)‖ ≤ C * ‖‖t • v‖ ^ 3‖ := ht
      _ = C * ‖v‖ ^ 3 * t ^ 3 := by
          rw [Real.norm_of_nonneg (by positivity), norm_smul, Real.norm_eq_abs,
            abs_of_pos (Set.mem_Ioi.1 htpos)]
          ring
  have h0 : f p = 0 := by
    have := hp.coeff_zero (fun _ => (0 : E))
    rw [← this]; exact hcoef 0 0 (by norm_num)
  have hd1 : ∀ v, fderiv ℝ f p v = 0 := by
    intro v
    have := hp.factorial_smul v 1
    rw [hcoef v 1 (by norm_num), smul_zero, iteratedFDeriv_one_apply] at this
    exact this.symm
  have hd2 : ∀ v, fderiv ℝ (fderiv ℝ f) p v v = 0 := by
    intro v
    have := hp.factorial_smul v 2
    rw [hcoef v 2 (by norm_num), smul_zero, iteratedFDeriv_two_apply] at this
    exact this.symm
  refine ⟨h0, ContinuousLinearMap.ext hd1, ?_⟩
  have hsymm : IsSymmSndFDerivAt ℝ f p :=
    (AnalyticAt.contDiffAt (n := ω) ⟨pf, r, hp⟩).isSymmSndFDerivAt_of_omega
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  have h := hd2 (v + w)
  simp only [map_add, ContinuousLinearMap.add_apply, hd2 v, hd2 w, zero_add, add_zero] at h
  rw [hsymm w v] at h
  simp only [ContinuousLinearMap.zero_apply]
  linarith

end Cubic

/-! ### Cubic vanishing on the slice `X = 0` -/

section Slice

variable {X L : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup L]
  [NormedSpace ℝ L]

theorem rowX_analyticAt {Q : X × L → ℝ} {z : X × L} (hQ : AnalyticAt ℝ Q z) :
    AnalyticAt ℝ (rowX Q) z := by
  have : rowX Q = fun w => ((ContinuousLinearMap.compL ℝ X (X × L) ℝ).flip
      (ContinuousLinearMap.inl ℝ X L)) (fderiv ℝ Q w) := by
    funext w; rfl
  rw [this]
  exact (ContinuousLinearMap.analyticAt _ _).comp hQ.fderiv

/-- The `X`-partial derivative of a map on `X × L` along the slice `λ = lam`. -/
theorem hasFDerivAt_slice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {Q : X × L → G}
    {x : X} {lam : L} (hQ : DifferentiableAt ℝ Q (x, lam)) :
    HasFDerivAt (fun y : X => Q (y, lam)) ((fderiv ℝ Q (x, lam)).comp
      (ContinuousLinearMap.inl ℝ X L)) x :=
  hQ.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x lam)

/-- **Cubic slice vanishing.**  If `Q` is analytic at `(0, e)` and `‖Q(X, λ)‖ ≤ C‖X‖³` near
`(0, e)`, then for every `λ` near `e`: `Q(0, λ) = 0`, `D_XQ(0, λ) = 0` and `D_X²Q(0, λ) = 0`. -/
theorem slice_cubic {Q : X × L → ℝ} {e : L} (hQ : AnalyticAt ℝ Q (0, e)) {C : ℝ}
    (hC : ∀ᶠ z in 𝓝 ((0 : X), e), ‖Q z‖ ≤ C * ‖z.1‖ ^ 3) :
    ∀ᶠ lam in 𝓝 e, Q (0, lam) = 0 ∧ rowX Q (0, lam) = 0 ∧
      (fderiv ℝ (rowX Q) (0, lam)).comp (ContinuousLinearMap.inl ℝ X L) = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hQ.eventually_analyticAt.and hC)
  filter_upwards [ball_mem_nhds e hε] with lam hlam
  have hmem : ∀ x ∈ ball (0 : X) ε, ((x, lam) : X × L) ∈ ball ((0 : X), e) ε := by
    intro x hx
    rw [mem_ball, Prod.dist_eq] at *
    exact max_lt hx hlam
  set g : X → ℝ := fun x => Q (x, lam) with hg
  have han0 : AnalyticAt ℝ Q (0, lam) := (hball _ (hmem 0 (mem_ball_self hε))).1
  have hg_an : AnalyticAt ℝ g 0 :=
    AnalyticAt.comp (g := Q) (f := fun x : X => ((x, lam) : X × L)) han0
      (analyticAt_id.prod analyticAt_const)
  have hg3 : VanishesToOrder g 0 3 := by
    refine IsBigO.of_bound C ?_
    filter_upwards [ball_mem_nhds (0 : X) hε] with x hx
    have := (hball _ (hmem x hx)).2
    simpa [g] using this
  obtain ⟨h0, h1, h2⟩ := cubic_point hg_an hg3
  have hfd : ∀ x ∈ ball (0 : X) ε, fderiv ℝ g x = rowX Q (x, lam) := fun x hx =>
    (hasFDerivAt_slice (hball _ (hmem x hx)).1.differentiableAt).fderiv
  refine ⟨h0, ?_, ?_⟩
  · rw [← hfd 0 (mem_ball_self hε)]; exact h1
  · have hev : fderiv ℝ g =ᶠ[𝓝 0] fun x => rowX Q (x, lam) := by
      filter_upwards [ball_mem_nhds (0 : X) hε] with x hx using hfd x hx
    have hd := hasFDerivAt_slice (rowX_analyticAt han0).differentiableAt
    rw [← hd.fderiv, ← hev.fderiv_eq]
    exact h2

end Slice

/-! ### Second-derivative bookkeeping -/

section Second

variable {X L : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup L]
  [NormedSpace ℝ L]

/-- The row `P_ν = ∂_λH[ν]`. -/
def rowP (H : X × L → ℝ) (ν : L) (z : X × L) : ℝ := fderiv ℝ H z (ContinuousLinearMap.inr ℝ X L ν)

/-- The canonical vector field `F = J(D_X H)`. -/
def canF (H : X × L → ℝ) (J : (X →L[ℝ] ℝ) →L[ℝ] X) (z : X × L) : X := J (rowX H z)

/-- The gradient `Dq(x) = B x + Bᵀ x` of the quadratic form `q(x) = B(x, x)`. -/
def gradQ (B : X →L[ℝ] X →L[ℝ] ℝ) (x : X) : X →L[ℝ] ℝ := B x + B.flip x

theorem rowP_analyticAt {H : X × L → ℝ} {z : X × L} (hH : AnalyticAt ℝ H z) (ν : L) :
    AnalyticAt ℝ (rowP H ν) z := by
  have : rowP H ν = fun w => (ContinuousLinearMap.apply ℝ ℝ (ContinuousLinearMap.inr ℝ X L ν))
      (fderiv ℝ H w) := by funext w; rfl
  rw [this]
  exact (ContinuousLinearMap.analyticAt _ _).comp hH.fderiv

theorem fderiv_rowX_apply {H : X × L → ℝ} {z : X × L} (hd : DifferentiableAt ℝ (fderiv ℝ H) z)
    (v : X × L) (w : X) :
    fderiv ℝ (rowX H) z v w = fderiv ℝ (fderiv ℝ H) z v (ContinuousLinearMap.inl ℝ X L w) := by
  rw [show rowX H = fun z => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ X L) from rfl,
    fderiv_comp_const_apply hd]
  rfl

theorem fderiv_rowP_apply {H : X × L → ℝ} {z : X × L} (hd : DifferentiableAt ℝ (fderiv ℝ H) z)
    (ν : L) (v : X × L) :
    fderiv ℝ (rowP H ν) z v = fderiv ℝ (fderiv ℝ H) z v (ContinuousLinearMap.inr ℝ X L ν) := by
  rw [show rowP H ν = fun z => fderiv ℝ H z (ContinuousLinearMap.inr ℝ X L ν) from rfl,
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- `D_λ(D_XH)[ν] = D_X(∂_λH[ν])` (symmetry of the second derivative). -/
theorem fderiv_rowX_inr {H : X × L → ℝ} {z : X × L} (hH : AnalyticAt ℝ H z) (ν : L) :
    fderiv ℝ (rowX H) z (ContinuousLinearMap.inr ℝ X L ν) = rowX (rowP H ν) z := by
  have hd := hH.fderiv.differentiableAt
  have hsymm : IsSymmSndFDerivAt ℝ H z := (hH.contDiffAt (n := ω)).isSymmSndFDerivAt_of_omega
  ext w
  rw [fderiv_rowX_apply hd, hsymm]
  simp only [rowX, ContinuousLinearMap.comp_apply]
  rw [fderiv_rowP_apply hd]

/-- `(D(massCol P)(z)(w, 0))ν = (D(rowX P)(z)(0, ν))w` (symmetry). -/
theorem fderiv_massCol_inl {P : X × L → ℝ} {z : X × L} (hP : AnalyticAt ℝ P z) (w : X) (ν : L) :
    fderiv ℝ (massCol P) z (ContinuousLinearMap.inl ℝ X L w) ν =
      fderiv ℝ (rowX P) z (ContinuousLinearMap.inr ℝ X L ν) w := by
  have hd := hP.fderiv.differentiableAt
  have hsymm : IsSymmSndFDerivAt ℝ P z := (hP.contDiffAt (n := ω)).isSymmSndFDerivAt_of_omega
  rw [fderiv_rowX_apply hd, show massCol P = fun z => (fderiv ℝ P z).comp
    (ContinuousLinearMap.inr ℝ X L) from rfl, fderiv_comp_const_apply hd]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hsymm]

end Second

/-! ### The shift structure and the Ward packet -/

section Packet

variable {X L Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- **The constant-shift structure** of a Hamiltonian at `(0, e)`: analytic, `D_XH(0, e) = 0`,
each constant-shift row is a quadratic form `B_c(X, X)` up to `O(‖X‖³)` uniformly in `λ`, and the
quadratic forms Poisson-commute through `J`. -/
structure ShiftStructure (H : X × L → ℝ) (J : (X →L[ℝ] ℝ) →L[ℝ] X) (e : L) (ν : Y → L)
    (B : Y → X →L[ℝ] X →L[ℝ] ℝ) : Prop where
  analytic : AnalyticAt ℝ H (0, e)
  F0 : rowX H (0, e) = 0
  cubic : ∀ c, ∃ C, ∀ᶠ z in 𝓝 ((0 : X), e), ‖rowP H (ν c) z - B c z.1 z.1‖ ≤ C * ‖z.1‖ ^ 3
  comm : ∀ c d x, gradQ (B c) x (J (gradQ (B d) x)) = 0

/-- The quadratic function `z ↦ B(z.1, z.1)`. -/
def qfun (B : X →L[ℝ] X →L[ℝ] ℝ) (z : X × L) : ℝ := B z.1 z.1

theorem qfun_analyticAt (B : X →L[ℝ] X →L[ℝ] ℝ) (z : X × L) : AnalyticAt ℝ (qfun B) z := by
  have : qfun (L := L) B = (fun x : X × X => B x.1 x.2) ∘ fun z : X × L => (z.1, z.1) := rfl
  rw [this]
  exact AnalyticAt.comp (B.analyticAt_bilinear _) (analyticAt_fst.prod analyticAt_fst)

theorem rowX_qfun (B : X →L[ℝ] X →L[ℝ] ℝ) (z : X × L) : rowX (qfun B) z = gradQ B z.1 := by
  have h1 : HasFDerivAt (fun z : X × L => z.1) (ContinuousLinearMap.fst ℝ X L) z := hasFDerivAt_fst
  have h : HasFDerivAt (qfun (L := L) B)
      ((B z.1).comp (ContinuousLinearMap.fst ℝ X L) + (B.flip z.1).comp
        (ContinuousLinearMap.fst ℝ X L)) z := by
    have := B.hasFDerivAt_of_bilinear h1 h1
    refine this.congr_fderiv ?_
    ext v <;> simp [add_comm]
  ext w
  simp [rowX, h.fderiv, gradQ]

/-- `rowX (qfun B)` is the linear map `z ↦ (B + Bᵀ) z.1`. -/
theorem rowX_qfun_eq (B : X →L[ℝ] X →L[ℝ] ℝ) :
    rowX (qfun (L := L) B) = fun z => (B + B.flip) z.1 := by
  funext z; rw [rowX_qfun]; rfl

theorem fderiv_rowX_qfun (B : X →L[ℝ] X →L[ℝ] ℝ) (z : X × L) :
    fderiv ℝ (rowX (qfun (L := L) B)) z = (B + B.flip).comp (ContinuousLinearMap.fst ℝ X L) := by
  rw [rowX_qfun_eq]
  exact ((B + B.flip).hasFDerivAt.comp z hasFDerivAt_fst).fderiv

theorem clm_eq_zero_of_inl_inr {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {T : X × L →L[ℝ] G} (h1 : T.comp (ContinuousLinearMap.inl ℝ X L) = 0)
    (h2 : T.comp (ContinuousLinearMap.inr ℝ X L) = 0) : T = 0 := by
  ext v
  · exact congrArg (fun S => S v) h1
  · exact congrArg (fun S => S v) h2

variable {H : X × L → ℝ} {J : (X →L[ℝ] ℝ) →L[ℝ] X} {e : L} {ν : Y → L}
  {B : Y → X →L[ℝ] X →L[ℝ] ℝ}

/-- The cubic part `Q_c = P_c - q_c`. -/
def cubicPart (H : X × L → ℝ) (ν : L) (B : X →L[ℝ] X →L[ℝ] ℝ) (z : X × L) : ℝ :=
  rowP H ν z - qfun B z

theorem cubicPart_analyticAt (hH : AnalyticAt ℝ H (0, e)) (μ : L) (B0 : X →L[ℝ] X →L[ℝ] ℝ) :
    AnalyticAt ℝ (cubicPart H μ B0) (0, e) :=
  (rowP_analyticAt hH μ).sub (qfun_analyticAt B0 _)

/-- The slice identities of the cubic part: `Q_c(0, λ) = 0`, `D_XQ_c(0, λ) = 0`, `DD_XQ_c(0, λ) = 0`
for `λ` near `e`. -/
theorem cubicPart_slice (S : ShiftStructure H J e ν B) (c : Y) :
    ∀ᶠ lam in 𝓝 e, cubicPart H (ν c) (B c) (0, lam) = 0 ∧
      rowX (cubicPart H (ν c) (B c)) (0, lam) = 0 ∧
      fderiv ℝ (rowX (cubicPart H (ν c) (B c))) (0, lam) = 0 := by
  obtain ⟨C, hC⟩ := S.cubic c
  have han := cubicPart_analyticAt S.analytic (ν c) (B c)
  have hsl := slice_cubic han (C := C) (by
    filter_upwards [hC] with z hz
    simpa [cubicPart, qfun] using hz)
  have hanev : ∀ᶠ lam in 𝓝 e, AnalyticAt ℝ (cubicPart H (ν c) (B c)) (0, lam) := by
    have ht : Tendsto (fun lam : L => ((0 : X), lam)) (𝓝 e) (𝓝 ((0 : X), e)) :=
      (continuous_const.prodMk continuous_id).tendsto' e _ rfl
    exact ht.eventually han.eventually_analyticAt
  filter_upwards [hsl, hsl.eventually_nhds, hanev] with lam h hnear han'
  refine ⟨h.1, h.2.1, clm_eq_zero_of_inl_inr h.2.2 ?_⟩
  refine HarmonicQuartic.fderiv_inr_eq_zero_of_slice (rowX (cubicPart H (ν c) (B c)))
    (hnear.mono fun l hl => hl.2.1) (rowX_analyticAt han').differentiableAt

theorem vanishesToOrder_mono {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] {f : E → G} {p : E} {k : ℕ} (h : VanishesToOrder f p (k + 1)) :
    VanishesToOrder f p k := by
  unfold VanishesToOrder at *
  refine h.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [ball_mem_nhds p one_pos] with z hz
  rw [mem_ball, dist_eq_norm] at hz
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul, pow_succ]
  exact mul_le_of_le_one_right (by positivity) hz.le

variable (S : ShiftStructure H J e ν B)
include S

theorem rowP_eq (c : Y) : rowP H (ν c) = qfun (B c) + cubicPart H (ν c) (B c) := by
  funext z; simp [cubicPart]

theorem rowX_rowP_eq (c : Y) : ∀ᶠ z in 𝓝 ((0 : X), e),
    rowX (rowP H (ν c)) z = gradQ (B c) z.1 + rowX (cubicPart H (ν c) (B c)) z := by
  filter_upwards [(cubicPart_analyticAt S.analytic (ν c) (B c)).eventually_analyticAt] with z hz
  rw [rowP_eq S, ← rowX_qfun (L := L)]
  simp only [rowX]
  rw [fderiv_add (qfun_analyticAt _ z).differentiableAt hz.differentiableAt]
  rfl

theorem rowX_rowP_eq_fun (c : Y) : rowX (rowP H (ν c)) =ᶠ[𝓝 ((0 : X), e)]
    rowX (qfun (B c)) + rowX (cubicPart H (ν c) (B c)) := by
  filter_upwards [rowX_rowP_eq S c] with z hz
  rw [hz]; simp only [Pi.add_apply, rowX_qfun]

/-- `P_{c,1} = 0`. -/
theorem ward_hP0 (c : Y) : rowX (rowP H (ν c)) (0, e) = 0 := by
  rw [(rowX_rowP_eq S c).self_of_nhds, ((cubicPart_slice S c).self_of_nhds).2.1]
  simp [gradQ]

/-- The row vanishes on the slice. -/
theorem rowP_slice (c : Y) : ∀ᶠ lam in 𝓝 e, rowP H (ν c) (0, lam) = 0 := by
  filter_upwards [cubicPart_slice S c] with lam h
  rw [rowP_eq S]
  simp [qfun, h.1]

theorem rowX_rowP_slice (c : Y) : ∀ᶠ lam in 𝓝 e, rowX (rowP H (ν c)) (0, lam) = 0 := by
  have ht : Tendsto (fun lam : L => ((0 : X), lam)) (𝓝 e) (𝓝 ((0 : X), e)) :=
    (continuous_const.prodMk continuous_id).tendsto' e _ rfl
  filter_upwards [cubicPart_slice S c, ht.eventually (rowX_rowP_eq S c)] with lam h h'
  rw [h', h.2.1]
  simp [gradQ]

theorem rowP_analyticAt_near (c : Y) : ∀ᶠ lam in 𝓝 e, AnalyticAt ℝ (rowP H (ν c)) (0, lam) := by
  have ht : Tendsto (fun lam : L => ((0 : X), lam)) (𝓝 e) (𝓝 ((0 : X), e)) :=
    (continuous_const.prodMk continuous_id).tendsto' e _ rfl
  exact ht.eventually (rowP_analyticAt S.analytic (ν c)).eventually_analyticAt

/-- **The mass order on the slice**, value: `𝓜_c(0, λ) = 0`. -/
theorem ward_hmass0 (c : Y) : ∀ᶠ lam in 𝓝 e, massCol (rowP H (ν c)) (0, lam) = 0 := by
  filter_upwards [(rowP_slice S c).eventually_nhds, rowP_analyticAt_near S c] with lam h han
  exact HarmonicQuartic.fderiv_inr_eq_zero_of_slice _ h han.differentiableAt

/-- **The mass order on the slice**, first `X`-derivative: `D_X𝓜_c(0, λ) = 0`. -/
theorem ward_hmass1 (c : Y) : ∀ᶠ lam in 𝓝 e,
    (fderiv ℝ (massCol (rowP H (ν c))) (0, lam)).comp (ContinuousLinearMap.inl ℝ X L) = 0 := by
  filter_upwards [(rowX_rowP_slice S c).eventually_nhds, rowP_analyticAt_near S c] with lam h han
  have h0 := HarmonicQuartic.fderiv_inr_eq_zero_of_slice _ h
    (rowX_analyticAt han).differentiableAt
  ext w μ
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  rw [fderiv_massCol_inl han]
  have := congrArg (fun T => T μ w) h0
  simpa using this

/-- **`𝓜₂(X, e)c = 0`**: the first derivative of the mass row vanishes at `(0, e)`. -/
theorem ward_hM2 (c : Y) (μ : L) :
    fderiv ℝ (fun z => massRow (rowX (rowP H (ν c))) z μ) (0, e) = 0 := by
  set Qc := cubicPart H (ν c) (B c)
  have hQan := cubicPart_analyticAt S.analytic (ν c) (B c)
  have hRan := rowX_analyticAt hQan
  -- near `p`, the mass row is the `λ`-derivative of `D_XQ_c`
  have hev : (fun z => massRow (rowX (rowP H (ν c))) z μ) =ᶠ[𝓝 ((0 : X), e)]
      fun z => fderiv ℝ (rowX Qc) z (ContinuousLinearMap.inr ℝ X L μ) := by
    filter_upwards [(rowX_rowP_eq_fun S c).eventually_nhds, hQan.eventually_analyticAt] with z hz han
    simp only [massRow, ContinuousLinearMap.comp_apply]
    rw [show fderiv ℝ (rowX (rowP H (ν c))) z = fderiv ℝ (rowX (qfun (B c)) +
        rowX (cubicPart H (ν c) (B c))) z from Filter.EventuallyEq.fderiv_eq hz, fderiv_add (by
        rw [rowX_qfun_eq]; exact ((B c + (B c).flip).differentiableAt.comp z differentiableAt_fst))
      (rowX_analyticAt han).differentiableAt, fderiv_rowX_qfun]
    simp
    rfl
  rw [hev.fderiv_eq]
  -- the `λ`-derivative of `D(D_XQ_c)` vanishes since `D(D_XQ_c)` vanishes on the slice
  have hslice : ∀ᶠ lam in 𝓝 e, fderiv ℝ (rowX Qc) (0, lam) = 0 :=
    (cubicPart_slice S c).mono fun lam h => h.2.2
  have hD : DifferentiableAt ℝ (fderiv ℝ (rowX Qc)) (0, e) := hRan.fderiv.differentiableAt
  have h1 := HarmonicQuartic.fderiv_inr_eq_zero_of_slice (X := X) (L := L)
    (fderiv ℝ (rowX Qc)) hslice hD
  have hsymm : IsSymmSndFDerivAt ℝ (rowX Qc) (0, e) :=
    (hRan.contDiffAt (n := ω)).isSymmSndFDerivAt_of_omega
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  rw [fderiv_clm_apply hD (differentiableAt_const _)]
  simp
  rw [hsymm]
  have := congrArg (fun T => T μ v w) h1
  simpa using this

theorem canF_analyticAt : AnalyticAt ℝ (canF H J) (0, e) := by
  have : canF H J = fun z => J (rowX H z) := rfl
  rw [this]
  exact (J.analyticAt _).comp (rowX_analyticAt S.analytic)

/-- `D_λF(z)[μ] = J(D_X P_μ(z))` near `(0, e)`. -/
theorem fderiv_canF_inr : ∀ᶠ z in 𝓝 ((0 : X), e), ∀ μ : L,
    fderiv ℝ (canF H J) z (ContinuousLinearMap.inr ℝ X L μ) = J (rowX (rowP H μ) z) := by
  filter_upwards [S.analytic.eventually_analyticAt] with z hz μ
  have h : HasFDerivAt (canF H J) (J.comp (fderiv ℝ (rowX H) z)) z :=
    J.hasFDerivAt.comp z (rowX_analyticAt hz).differentiableAt.hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply, fderiv_rowX_inr hz]

/-- `F(0, e) = 0`. -/
theorem ward_hF0 : canF H J (0, e) = 0 := by
  simp [canF, S.F0]

/-- `D_λF(0, e)[ν d] = 0`: a constant shift has no linear constraint row. -/
theorem ward_hFν (d : Y) :
    (fderiv ℝ (canF H J) (0, e)).comp (ContinuousLinearMap.inr ℝ X L) (ν d) = 0 := by
  rw [ContinuousLinearMap.comp_apply, (fderiv_canF_inr S).self_of_nhds, ward_hP0 S d, map_zero]

theorem vanishes_gradQ (B0 : X →L[ℝ] X →L[ℝ] ℝ) :
    VanishesToOrder (fun z : X × L => gradQ B0 z.1) ((0 : X), e) 1 := by
  have h : (fun z : X × L => gradQ B0 z.1) = fun z => (B0 + B0.flip) z.1 := rfl
  rw [h]
  exact vanishesToOrder_one_of_differentiableAt
    ((B0 + B0.flip).differentiableAt.comp _ differentiableAt_fst) (by simp)

theorem vanishes_rowX_cubic (c : Y) :
    VanishesToOrder (rowX (cubicPart H (ν c) (B c))) ((0 : X), e) 2 := by
  have han := cubicPart_analyticAt S.analytic (ν c) (B c)
  have hR := rowX_analyticAt han
  have hsl := (cubicPart_slice S c).self_of_nhds
  exact vanishesToOrder_two (hR.eventually_analyticAt.mono fun z hz => hz.differentiableAt)
    hR.fderiv.differentiableAt hsl.2.1 hsl.2.2

/-- **The quadratic bracket of two commuting constant shifts vanishes**:
`D²{P_c, P_{ν d}}(0, e) = 0`. -/
theorem ward_hQ (c d : Y) :
    fderiv ℝ (fderiv ℝ (fun z => bracketRow (rowX (rowP H (ν c))) (canF H J) z (ν d))) (0, e)
      = 0 := by
  set br := fun z => bracketRow (rowX (rowP H (ν c))) (canF H J) z (ν d)
  have hPc := rowP_analyticAt S.analytic (ν c)
  have hFa := canF_analyticAt S
  have hbr_an : AnalyticAt ℝ br (0, e) := by
    have : br = fun z => (rowX (rowP H (ν c)) z)
        ((fderiv ℝ (canF H J) z) (ContinuousLinearMap.inr ℝ X L (ν d))) := rfl
    rw [this]
    have h1 := rowX_analyticAt hPc
    have h2 : AnalyticAt ℝ (fun z => (fderiv ℝ (canF H J) z)
        (ContinuousLinearMap.inr ℝ X L (ν d))) (0, e) :=
      (ContinuousLinearMap.analyticAt (ContinuousLinearMap.apply ℝ X
        (ContinuousLinearMap.inr ℝ X L (ν d))) _).comp hFa.fderiv
    exact ((ContinuousLinearMap.apply ℝ ℝ).flip.analyticAt_bilinear _).comp (h1.prod h2) |>.congr
      (Eventually.of_forall fun z => by simp)
  -- the bracket near `(0, e)`
  set gc := fun z : X × L => gradQ (B c) z.1
  set gd := fun z : X × L => gradQ (B d) z.1
  set rc := rowX (cubicPart H (ν c) (B c))
  set rd := rowX (cubicPart H (ν d) (B d))
  have hev : br =ᶠ[𝓝 ((0 : X), e)] fun z => gc z (J (rd z)) + rc z (J (gd z + rd z)) := by
    filter_upwards [fderiv_canF_inr S, rowX_rowP_eq S c, rowX_rowP_eq S d] with z h1 h2 h3
    simp only [br, bracketRow, ContinuousLinearMap.comp_apply, h1, h2, h3]
    have hcomm := S.comm c d z.1
    simp only [gc, gd, rc, rd, map_add, ContinuousLinearMap.add_apply] at hcomm ⊢
    linarith
  have o1 : VanishesToOrder (fun z => gc z (J (rd z))) ((0 : X), e) (1 + 2) :=
    (vanishes_gradQ S (B c)).clm_apply ((vanishes_rowX_cubic S d).map J)
  have o2 : VanishesToOrder (fun z => rc z (J (gd z + rd z))) ((0 : X), e) (2 + 1) := by
    have hgr : VanishesToOrder (fun z => gd z + rd z) ((0 : X), e) 1 :=
      (vanishes_gradQ S (B d)).add (vanishesToOrder_mono (vanishes_rowX_cubic S d))
    exact (vanishes_rowX_cubic S c).clm_apply (hgr.map J)
  have o3 : VanishesToOrder br ((0 : X), e) 3 :=
    (o1.add o2).congr' (hev.mono fun z hz => hz.symm) EventuallyEq.rfl
  exact (cubic_point hbr_an o3).2.2

/-- **The linear first-Poisson coefficient**: `D(D_XP_c)(0, e)[(Y, 0)] ∘ D_λF(0, e) =
(B_c Y + B_cᵀ Y) ∘ J ∘ D_λD_XH(0, e)`. -/
theorem ward_K1_eq (c : Y) (Y0 : X) :
    (fderiv ℝ (rowX (rowP H (ν c))) (0, e) (Y0, 0)).comp
        ((fderiv ℝ (canF H J) (0, e)).comp (ContinuousLinearMap.inr ℝ X L)) =
      (gradQ (B c) Y0).comp (J.comp ((fderiv ℝ (rowX H) (0, e)).comp
        (ContinuousLinearMap.inr ℝ X L))) := by
  have han := cubicPart_analyticAt S.analytic (ν c) (B c)
  have hfd : fderiv ℝ (rowX (rowP H (ν c))) (0, e) =
      fderiv ℝ (rowX (qfun (B c))) (0, e) + fderiv ℝ (rowX (cubicPart H (ν c) (B c))) (0, e) := by
    have hq : DifferentiableAt ℝ (rowX (qfun (L := L) (B c))) (0, e) := by
      rw [rowX_qfun_eq]
      exact (B c + (B c).flip).differentiableAt.comp _ differentiableAt_fst
    rw [(rowX_rowP_eq_fun S c).fderiv_eq]
    exact fderiv_add hq (rowX_analyticAt han).differentiableAt
  have hFd : fderiv ℝ (canF H J) (0, e) = J.comp (fderiv ℝ (rowX H) (0, e)) :=
    (J.hasFDerivAt.comp _ (rowX_analyticAt S.analytic).differentiableAt.hasFDerivAt).fderiv
  rw [hfd, ((cubicPart_slice S c).self_of_nhds).2.2, fderiv_rowX_qfun, hFd]
  ext μ
  simp [gradQ]

end Packet

/-! ### Ward orders along the first-field ray -/

section Ray

variable {X L : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]

/-- **`lem:supp-exact-ward-orders` along the first-field ray.**  For `P'_c = D_XP_c` and
`F = F^can` (`C⁴` at `p = (0, e)`) with `F(p) = 0`, `P'_c(p) = 0`, `D_λP'_c(p) = 0` and the linear
first-Poisson coefficient vanishing **at the first field** `Y` only
(`D P'_c(p)[(Y, 0)] ∘ D_λF(p) = 0`, the manuscript's `𝕂₁(Y)c = 0`):
1. `‖Dℬ_c(z)‖ = O(‖z - p‖)` on a neighbourhood of `p`;
2. along every family `X_a = aY + O(a²)`, `λ_a = e + O(a)` (`a ↓ 0`): `‖D_λℬ_c‖ = O(a²)`;
3. for every `ν` with `D_λF(p)ν = 0` (a constant shift), `D(D_λP'_c[ν])(p) = 0` and
   `D²{P_c, P_ν}(p) = 0`: `D_λℬ_c[ν] = O(‖z - p‖³)` on a neighbourhood of `p`. -/
theorem ward_orders_ray (Pc' : X × L → X →L[ℝ] ℝ) (F : X × L → X) (e : L)
    (hP : ContDiffAt ℝ 4 Pc' (0, e)) (hF : ContDiffAt ℝ 4 F (0, e))
    (hF0 : F (0, e) = 0) (hP0 : Pc' (0, e) = 0) (hM : massRow Pc' (0, e) = 0) (Y0 : X)
    (hK1 : (fderiv ℝ Pc' (0, e) (Y0, 0)).comp
      ((fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L)) = 0) :
    VanishesToOrder (fderiv ℝ (wardRow Pc' F)) (0, e) 1 ∧
      (∀ z : ℝ → X × L, (fun a => (z a).1 - a • Y0) =O[𝓝[>] 0] (fun a => a ^ 2) →
        (fun a => (z a).2 - e) =O[𝓝[>] 0] (fun a => a) →
        (fun a => (fderiv ℝ (wardRow Pc' F) (z a)).comp (ContinuousLinearMap.inr ℝ X L))
          =O[𝓝[>] 0] fun a => a ^ 2) ∧
      ∀ ν : L, (fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L) ν = 0 →
        fderiv ℝ (fun z => massRow Pc' z ν) (0, e) = 0 →
        fderiv ℝ (fderiv ℝ (fun z => bracketRow Pc' F z ν)) (0, e) = 0 →
        VanishesToOrder (fun z => (fderiv ℝ (wardRow Pc' F) z).comp
          (ContinuousLinearMap.inr ℝ X L) ν) (0, e) 3 := by
  set p : X × L := (0, e)
  have hPev := hP.eventually (by simp)
  have hFev := hF.eventually (by simp)
  have hPd : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ Pc' z :=
    hPev.mono fun z hz => hz.differentiableAt (by simp)
  have hFd : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ F z :=
    hFev.mono fun z hz => hz.differentiableAt (by simp)
  have hDP : ContDiffAt ℝ 3 (fderiv ℝ Pc') p := hP.fderiv_right (by norm_num)
  have hDF : ContDiffAt ℝ 3 (fderiv ℝ F) p := hF.fderiv_right (by norm_num)
  have hDFev := hDF.eventually (by simp)
  have oF1 : VanishesToOrder F p 1 :=
    vanishesToOrder_one_of_differentiableAt (hF.differentiableAt (by simp)) hF0
  have oP1 : VanishesToOrder Pc' p 1 :=
    vanishesToOrder_one_of_differentiableAt (hP.differentiableAt (by simp)) hP0
  have oDF0 : VanishesToOrder (fderiv ℝ F) p 0 :=
    vanishesToOrder_zero_of_continuousAt hDF.continuousAt
  have oDP0 : VanishesToOrder (fderiv ℝ Pc') p 0 :=
    vanishesToOrder_zero_of_continuousAt hDP.continuousAt
  have hformula : ∀ᶠ z in 𝓝 p, fderiv ℝ (wardRow Pc' F) z
      = (Pc' z).comp (fderiv ℝ F z) + (fderiv ℝ Pc' z).flip (F z) := by
    filter_upwards [hPd, hFd] with z h1 h2
    exact (wardRow_hasFDerivAt h1 h2).fderiv
  have hformula' : ∀ᶠ z in 𝓝 p, (fderiv ℝ (wardRow Pc' F) z).comp
      (ContinuousLinearMap.inr ℝ X L) = bracketRow Pc' F z + (massRow Pc' z).flip (F z) := by
    filter_upwards [hPd, hFd] with z h1 h2
    exact wardRow_fderiv_inr h1 h2
  have omass : VanishesToOrder (massRow Pc') p 1 := by
    have hd : DifferentiableAt ℝ (massRow Pc') p := by
      show DifferentiableAt ℝ (fun z => (fderiv ℝ Pc' z).comp (ContinuousLinearMap.inr ℝ X L)) p
      exact (hDP.differentiableAt (by simp)).clm_comp
        (differentiableAt_const (ContinuousLinearMap.inr ℝ X L))
    exact vanishesToOrder_one_of_differentiableAt hd hM
  -- the derivative of the bracket row at `p`
  have hbrH : HasFDerivAt (bracketRow Pc' F)
      ((ContinuousLinearMap.compL ℝ L X ℝ).flip ((fderiv ℝ F p).comp
        (ContinuousLinearMap.inr ℝ X L)) |>.comp (fderiv ℝ Pc' p)) p := by
    have h := (hP.differentiableAt (by simp)).hasFDerivAt.clm_comp
      ((hDF.differentiableAt (by simp)).hasFDerivAt.clm_comp
        (hasFDerivAt_const (ContinuousLinearMap.inr ℝ X L) p))
    refine h.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun w => ContinuousLinearMap.ext fun ν => ?_
    simp [hP0]
  refine ⟨?_, ?_, ?_⟩
  · -- clause 1
    have h1 : VanishesToOrder (fun z => (Pc' z).comp (fderiv ℝ F z)) p 1 := by
      simpa using oP1.clm_comp oDF0
    have h2 : VanishesToOrder (fun z => (fderiv ℝ Pc' z).flip (F z)) p 1 := by
      simpa using oDP0.clm_flip_apply oF1
    exact (h1.add h2).congr' (hformula.mono fun z hz => hz.symm) EventuallyEq.rfl
  · -- clause 2 along the ray
    intro z hz1 hz2
    have hl : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl)
    have hb1 : (fun a : ℝ => a) =O[𝓝[>] 0] (fun _ => (1 : ℝ)) := hl.isBigO_one ℝ
    have ha2 : (fun a : ℝ => a ^ 2) =O[𝓝[>] 0] fun a => a := by
      have := (isBigO_refl (fun a : ℝ => a) (𝓝[>] 0)).mul hb1
      simpa [pow_two] using this
    have hX : (fun a => (z a).1) =O[𝓝[>] 0] fun a => a := by
      have h1 : (fun a : ℝ => a • Y0) =O[𝓝[>] 0] fun a => a :=
        IsBigO.of_bound ‖Y0‖ (Eventually.of_forall fun a => by
          rw [norm_smul, Real.norm_eq_abs, mul_comm])
      have := (hz1.trans ha2).add h1
      simpa using this
    have hzp : (fun a => z a - p) =O[𝓝[>] 0] fun a => a := by
      have : (fun a => z a - p) = fun a => ((z a).1, (z a).2 - e) := by
        funext a; ext <;> simp [p]
      rw [this]
      exact hX.prod_left hz2
    -- the mass part
    have hmassF : VanishesToOrder (fun z => (massRow Pc' z).flip (F z)) p 2 :=
      omass.clm_flip_apply oF1
    have tm := hmassF.comp_family' z hzp hl
    -- the bracket part: first-order Taylor remainder
    set G := bracketRow Pc' F
    set DG := (ContinuousLinearMap.compL ℝ L X ℝ).flip ((fderiv ℝ F p).comp
        (ContinuousLinearMap.inr ℝ X L)) |>.comp (fderiv ℝ Pc' p)
    have hG2 : ContDiffAt ℝ 2 G p := by
      have h1 : ContDiffAt ℝ 2 Pc' p := hP.of_le (by norm_num)
      have h2 : ContDiffAt ℝ 2 (fderiv ℝ F) p := hDF.of_le (by norm_num)
      exact h1.clm_comp (h2.clm_comp contDiffAt_const)
    set φ := fun w => G w - DG (w - p)
    have hφd : ∀ᶠ w in 𝓝 p, DifferentiableAt ℝ φ w := by
      filter_upwards [hG2.eventually (by simp)] with w hw
      exact (hw.differentiableAt (by simp)).sub
        (DG.differentiableAt.comp w ((differentiableAt_id).sub_const p))
    have hφhas : ∀ w, DifferentiableAt ℝ G w →
        HasFDerivAt φ (fderiv ℝ G w - DG) w := by
      intro w hw
      have h := hw.hasFDerivAt.sub (DG.hasFDerivAt.comp w ((hasFDerivAt_id w).sub_const p))
      exact h.congr_fderiv (by rw [ContinuousLinearMap.comp_id])
    have hφfd : HasFDerivAt φ (DG - DG) p := by
      have := hφhas p hbrH.differentiableAt
      rwa [hbrH.fderiv] at this
    have hφD : DifferentiableAt ℝ (fderiv ℝ φ) p := by
      have hG1 : ContDiffAt ℝ 1 (fderiv ℝ G) p := hG2.fderiv_right (by norm_num)
      have hev : fderiv ℝ φ =ᶠ[𝓝 p] fun w => fderiv ℝ G w - DG := by
        filter_upwards [hG2.eventually (by simp)] with w hw
        exact (hφhas w (hw.differentiableAt (by simp))).fderiv
      exact ((hG1.differentiableAt (by simp)).sub_const DG).congr_of_eventuallyEq hev
    have oφ : VanishesToOrder φ p 2 :=
      vanishesToOrder_two hφd hφD (by simp [φ, G, bracketRow, p, hP0]) (by
        rw [hφfd.fderiv]; simp)
    have tφ := oφ.comp_family' z hzp hl
    -- the linear part `DG(z_a - p) = DG((X_a - aY, 0))`
    have hDG : ∀ a, DG (z a - p) = DG (((z a).1 - a • Y0, 0)) := by
      intro a
      have hsplit : z a - p = ((z a).1 - a • Y0, 0) + a • (Y0, 0) + (0, (z a).2 - e) := by
        ext <;> simp [p]
      rw [hsplit, map_add, map_add, map_smul]
      have h1 : DG (Y0, 0) = 0 := by
        simp only [DG, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.compL_apply]
        exact hK1
      have h2 : DG (0, (z a).2 - e) = 0 := by
        simp only [DG, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.compL_apply]
        have hm : fderiv ℝ Pc' p (0, (z a).2 - e) = massRow Pc' p ((z a).2 - e) := rfl
        rw [hm, hM]
        simp
      rw [h1, h2, smul_zero, add_zero, add_zero]
    have tlin : (fun a => DG (z a - p)) =O[𝓝[>] 0] fun a => a ^ 2 := by
      simp only [hDG]
      have : (fun a => (((z a).1 - a • Y0, (0 : L)) : X × L)) =O[𝓝[>] 0] fun a => a ^ 2 :=
        hz1.prod_left (isBigO_zero _ _)
      exact (DG.isBigO_comp _ _).trans this
    have tbr : (fun a => G (z a)) =O[𝓝[>] 0] fun a => a ^ 2 := by
      have := tφ.add tlin
      refine this.congr_left fun a => ?_
      simp [φ]
    have := tbr.add tm
    refine this.congr' ?_ EventuallyEq.rfl
    have ht : Tendsto z (𝓝[>] 0) (𝓝 p) := by
      have h2 := (hzp.trans_tendsto hl).add_const p
      simpa using h2
    filter_upwards [ht.eventually hformula'] with a ha
    rw [ha]
  · -- clause 3
    intro ν hFν hM2 hQ
    have hformula'' : ∀ᶠ z in 𝓝 p, (fderiv ℝ (wardRow Pc' F) z).comp
        (ContinuousLinearMap.inr ℝ X L) ν = bracketRow Pc' F z ν + massRow Pc' z ν (F z) := by
      filter_upwards [hformula'] with z hz
      rw [hz]
      rfl
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
      have h' : HasFDerivAt b _ p := hbrH.clm_apply (hasFDerivAt_const ν p)
      rw [h'.fderiv]
      refine ContinuousLinearMap.ext fun w => ?_
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, fderiv_const,
        Pi.zero_apply, ContinuousLinearMap.zero_apply]
      have hFν' : (fderiv ℝ F p) ((0 : X), ν) = 0 := hFν
      simp [hFν', bracketRow, hP0]
    have ob : VanishesToOrder b p 3 :=
      vanishesToOrder_three hbd hbd1 hbd2 (by simp [b, bracketRow, p, hP0]) hb1 hQ
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

/-- **The order count of `thm:supp-exact-harmonic-q4-zero` along the first-field ray.**  As
`HarmonicQuartic.dirResidualRow_isBigO_five`, but the base family is `X_a = aY + O(a²)`,
`λ_a = e + O(a)` and the linear first-Poisson coefficient is required only at `Y`
(`𝕂₁(Y)c = 0`); the harmonic direction `ν` is a constant shift (`D_λF(0, e)ν = 0`).  Then the
constant-shift row of the directional residual along every pure-harmonic ray tangent is
`O(a⁵)`. -/
theorem dirResidualRow_isBigO_five_ray (P : X × L → ℝ) (F : X × L → X) (e ν : L)
    (hP : ContDiffAt ℝ 5 P (0, e)) (hF : ContDiffAt ℝ 4 F (0, e))
    (hF0 : F (0, e) = 0) (hP0 : rowX P (0, e) = 0)
    (Y0 : X) (hK1 : (fderiv ℝ (rowX P) (0, e) (Y0, 0)).comp
      ((fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L)) = 0)
    (hFν : (fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L) ν = 0)
    (hM2 : fderiv ℝ (fun z => massRow (rowX P) z ν) (0, e) = 0)
    (hQ : fderiv ℝ (fderiv ℝ (fun z => bracketRow (rowX P) F z ν)) (0, e) = 0)
    (hmass0 : ∀ᶠ lam in 𝓝 e, massCol P (0, lam) = 0)
    (hmass1 : ∀ᶠ lam in 𝓝 e,
      (fderiv ℝ (massCol P) (0, lam)).comp (ContinuousLinearMap.inl ℝ X L) = 0)
    (z : ℝ → X × L) (hz1 : (fun a => (z a).1 - a • Y0) =O[𝓝[>] 0] fun a => a ^ 2)
    (hz2 : (fun a => (z a).2 - e) =O[𝓝[>] 0] fun a => a)
    (δX : ℝ → X) (δlam : ℝ → L) (hδX : δX =O[𝓝[>] 0] fun a => a ^ 5)
    (hδlam : (fun a => δlam a - a ^ 2 • ν) =O[𝓝[>] 0] fun a => a ^ 3)
    (r : ℝ → L) (hr : r =O[𝓝[>] 0] fun _ => (1 : ℝ)) :
    (fun a => dirResidualRow P F (z a) (δX a, δlam a) (a • r a)) =O[𝓝[>] 0] fun a => a ^ 5 := by
  set p : X × L := (0, e)
  have hl : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl)
  have hz : (fun a => z a - p) =O[𝓝[>] 0] fun a => a := by
    have hb1 : (fun a : ℝ => a) =O[𝓝[>] 0] (fun _ => (1 : ℝ)) := hl.isBigO_one ℝ
    have ha2 : (fun a : ℝ => a ^ 2) =O[𝓝[>] 0] fun a => a := by
      have := (isBigO_refl (fun a : ℝ => a) (𝓝[>] 0)).mul hb1
      simpa [pow_two] using this
    have hX : (fun a => (z a).1) =O[𝓝[>] 0] fun a => a := by
      have h1 : (fun a : ℝ => a • Y0) =O[𝓝[>] 0] fun a => a :=
        IsBigO.of_bound ‖Y0‖ (Eventually.of_forall fun a => by
          rw [norm_smul, Real.norm_eq_abs, mul_comm])
      have := (hz1.trans ha2).add h1
      simpa using this
    have : (fun a => z a - p) = fun a => ((z a).1, (z a).2 - e) := by
      funext a; ext <;> simp [p]
    rw [this]
    exact hX.prod_left hz2
  have hzt : Tendsto z (𝓝[>] 0) (𝓝 p) := by
    have h2 := (hz.trans_tendsto hl).add_const p
    simpa using h2
  -- Ward orders
  have hP' : ContDiffAt ℝ 4 (rowX P) p :=
    (hP.fderiv_right (m := 4) (by norm_num)).clm_comp contDiffAt_const
  have hM : massRow (rowX P) p = 0 := massRow_eq_zero_of_mass P e hP hmass1.self_of_nhds
  obtain ⟨o1, o2, o3⟩ := ward_orders_ray (rowX P) F e hP' hF hF0 hP0 hM Y0 hK1
  set B := wardRow (rowX P) F
  have a1 : (fun a => fderiv ℝ B (z a)) =O[𝓝[>] 0] fun a => a ^ 1 := o1.comp_family' z hz hl
  have a2 : (fun a => (fderiv ℝ B (z a)).comp (ContinuousLinearMap.inr ℝ X L)) =O[𝓝[>] 0]
      fun a => a ^ 2 := o2 z hz1 hz2
  have a3 : (fun a => (fderiv ℝ B (z a)).comp (ContinuousLinearMap.inr ℝ X L) ν) =O[𝓝[>] 0]
      fun a => a ^ 3 := (o3 ν hFν hM2 hQ).comp_family' z hz hl
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


/-- **`thm:supp-exact-harmonic-q4-zero` along the first-field ray**: the Taylor coefficients of
order `≤ 4` (in particular `q₄`) of the analytic constant-shift row of the directional residual
vanish. -/
theorem harmonic_q4_zero_ray (P : X × L → ℝ) (F : X × L → X) (e ν : L)
    (hP : ContDiffAt ℝ 5 P (0, e)) (hF : ContDiffAt ℝ 4 F (0, e))
    (hF0 : F (0, e) = 0) (hP0 : rowX P (0, e) = 0)
    (Y0 : X) (hK1 : (fderiv ℝ (rowX P) (0, e) (Y0, 0)).comp
      ((fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L)) = 0)
    (hFν : (fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L) ν = 0)
    (hM2 : fderiv ℝ (fun z => massRow (rowX P) z ν) (0, e) = 0)
    (hQ : fderiv ℝ (fderiv ℝ (fun z => bracketRow (rowX P) F z ν)) (0, e) = 0)
    (hmass0 : ∀ᶠ lam in 𝓝 e, massCol P (0, lam) = 0)
    (hmass1 : ∀ᶠ lam in 𝓝 e,
      (fderiv ℝ (massCol P) (0, lam)).comp (ContinuousLinearMap.inl ℝ X L) = 0)
    (z : ℝ → X × L) (hz1 : (fun a => (z a).1 - a • Y0) =O[𝓝[>] 0] fun a => a ^ 2)
    (hz2 : (fun a => (z a).2 - e) =O[𝓝[>] 0] fun a => a)
    (δX : ℝ → X) (δlam : ℝ → L) (hδX : δX =O[𝓝[>] 0] fun a => a ^ 5)
    (hδlam : (fun a => δlam a - a ^ 2 • ν) =O[𝓝[>] 0] fun a => a ^ 3)
    (r : ℝ → L) (hr : r =O[𝓝[>] 0] fun _ => (1 : ℝ)) {pq : FormalMultilinearSeries ℝ ℝ ℝ}
    (hq : HasFPowerSeriesAt (fun a => dirResidualRow P F (z a) (δX a, δlam a) (a • r a)) pq 0) :
    (∀ j ≤ 4, pq.coeff j = 0) ∧ pq.coeff 4 = 0 := by
  have h := coeff_eq_zero_of_isBigO hq (dirResidualRow_isBigO_five_ray P F e ν hP hF hF0 hP0 Y0
    hK1 hFν hM2 hQ hmass0 hmass1 z hz1 hz2 δX δlam hδX hδlam r hr)
  exact ⟨fun j hj => h j (by omega), h 4 (by norm_num)⟩

end Ray

/-! ### The ray Ward packet and the bridge to the slope chain -/

section RayPacket

variable {X L Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]

/-- **The constant-shift Ward packet along the first field `Y0`** (`eq:supp-exact-ward-mass-order`,
`eq:supp-exact-harmonic-mass-column`): `F^can(0, e) = 0`, `P_{c,1} = 0`, `𝕂₁(Y0)c = 0`,
`D_λF(0, e)[H_c d] = 0`, `𝓜₂(X, e)c = 0`, the vanishing quadratic bracket and the mass order on
the slice.  It differs from `HarmonicQuartic.WardPacket` only in `hK1` (at `Y0`, not for every
`w`) and the explicit field `hFν`. -/
structure WardPacketRay {ι : Type*} (P : ι → X × L → ℝ) (F : X × L → X) (e : L) (νH : Y → L)
    (Y0 : X) : Prop where
  hP : ∀ i, ContDiffAt ℝ 5 (P i) (0, e)
  hF : ContDiffAt ℝ 4 F (0, e)
  hF0 : F (0, e) = 0
  hP0 : ∀ i, rowX (P i) (0, e) = 0
  hK1 : ∀ i, (fderiv ℝ (rowX (P i)) (0, e) (Y0, 0)).comp
    ((fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L)) = 0
  hFν : ∀ c, (fderiv ℝ F (0, e)).comp (ContinuousLinearMap.inr ℝ X L) (νH c) = 0
  hM2 : ∀ i c, fderiv ℝ (fun z => massRow (rowX (P i)) z (νH c)) (0, e) = 0
  hQ : ∀ i c, fderiv ℝ (fderiv ℝ (fun z => bracketRow (rowX (P i)) F z (νH c))) (0, e) = 0
  hmass0 : ∀ i, ∀ᶠ lam in 𝓝 e, massCol (P i) (0, lam) = 0
  hmass1 : ∀ i, ∀ᶠ lam in 𝓝 e,
    (fderiv ℝ (massCol (P i)) (0, lam)).comp (ContinuousLinearMap.inl ℝ X L) = 0

variable {H : X × L → ℝ} {J : (X →L[ℝ] ℝ) →L[ℝ] X} {e : L} {ν : Y → L}
  {B : Y → X →L[ℝ] X →L[ℝ] ℝ}

/-- **The Ward packet from the shift structure.**  Every field is derived; the linear
first-Poisson coefficient at `Y0` is computed by `ward_K1_eq` and its vanishing is the hypothesis
`hK1`. -/
theorem wardPacketRay_of_shift {ι : Type*} (σ : ι → Y) (S : ShiftStructure H J e ν B) (Y0 : X)
    (hK1 : ∀ i, (gradQ (B (σ i)) Y0).comp (J.comp ((fderiv ℝ (rowX H) (0, e)).comp
      (ContinuousLinearMap.inr ℝ X L))) = 0) :
    WardPacketRay (fun i => rowP H (ν (σ i))) (canF H J) e ν Y0 where
  hP i := (rowP_analyticAt S.analytic _).contDiffAt
  hF := (canF_analyticAt S).contDiffAt
  hF0 := ward_hF0 S
  hP0 i := ward_hP0 S (σ i)
  hK1 i := by rw [ward_K1_eq S (σ i) Y0]; exact hK1 i
  hFν c := ward_hFν S c
  hM2 i c := ward_hM2 S (σ i) (ν c)
  hQ i c := ward_hQ S (σ i) c
  hmass0 i := ward_hmass0 S (σ i)
  hmass1 i := ward_hmass1 S (σ i)

open ExactSlowBranch ExactSlowRankTwo

variable {R Yh Zg V Xs Ho : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup Yh] [NormedSpace ℝ Yh] [NormedAddCommGroup Zg] [NormedSpace ℝ Zg]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Xs] [NormedSpace ℝ Xs]
  [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]

/-- **`thm:supp-exact-harmonic-q4-zero` ⇒ harmonic annihilation, along the first-field ray.**
As `HarmonicQuartic.harmonicAnnihilation_of_ward`, with the ray Ward packet and base families
`X_a = aY0 + O(a²)`, `λ_a = e + O(a)`. -/
theorem harmonicAnnihilation_of_ward_ray {ι : Type*} (ℓ : ι → Ho →L[ℝ] ℝ)
    (hsep : ∀ y : Ho, (∀ i, ℓ i y = 0) → y = 0)
    (P : ι → X × L → ℝ) (F : X × L → X) (e : L) (νH : Yh → L) (Y0 : X)
    (hW : WardPacketRay P F e νH Y0)
    (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Yh →L[ℝ] V) (γ : R × Yh → Zg) (cH : V → Ho)
    (hray : ∀ c : Yh, ∀ᶠ q in 𝓝 (0 : R × Yh), ∃ (z : ℝ → X × L) (δX : ℝ → X) (δlam : ℝ → L)
      (r : ℝ → L), (fun a => (z a).1 - a • Y0) =O[𝓝[>] 0] (fun a => a ^ 2) ∧
        (fun a => (z a).2 - e) =O[𝓝[>] 0] (fun a => a) ∧
        δX =O[𝓝[>] 0] (fun a => a ^ 5) ∧
        (fun a => δlam a - a ^ 2 • νH c) =O[𝓝[>] 0] (fun a => a ^ 3) ∧
        r =O[𝓝[>] 0] (fun _ => (1 : ℝ)) ∧
        ∀ i, ∃ pq : FormalMultilinearSeries ℝ ℝ ℝ,
          HasFPowerSeriesAt (fun a => dirResidualRow (P i) F (z a) (δX a, δlam a) (a • r a)) pq 0 ∧
          ℓ i (fderiv ℝ cH (reducedChart E Jg JH γ q) (JH c)) = pq.coeff 4) :
    HarmonicAnnihilation E Jg JH γ cH := by
  refine harmonicAnnihilation_of_quartic ℓ hsep E Jg JH γ cH fun c => ?_
  filter_upwards [hray c] with q hq
  obtain ⟨z, δX, δlam, r, hz1, hz2, hδX, hδlam, hr, hrow⟩ := hq
  intro i
  obtain ⟨pq, hpq, hid⟩ := hrow i
  exact ⟨_, pq, hpq, dirResidualRow_isBigO_five_ray (P i) F e (νH c) (hW.hP i) hW.hF hW.hF0
    (hW.hP0 i) Y0 (hW.hK1 i) (hW.hFν c) (hW.hM2 i c) (hW.hQ i c) (hW.hmass0 i) (hW.hmass1 i) z
    hz1 hz2 δX δlam hδX hδlam r hr, hid⟩

end RayPacket

end ShiftWardPacket
end RenewalGeometry
