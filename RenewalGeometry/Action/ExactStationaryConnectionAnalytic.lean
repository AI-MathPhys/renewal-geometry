/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactStationaryConnection
import RenewalGeometry.Analysis.PlaquetteBCHExpansion

/-!
# Analytic dependence of the stationary connection
  (`thm:supp-exact-action-provenance` (ii), `eq:supp-exact-stationary-connection`;
  emergent-spacetime manuscript)

Clause (ii) asserts that the stationary row has "a unique analytic solution
`A = 𝒜_h(e, ∂_t e)` on the declared chart".  Existence and uniqueness are
`stationary_connection_gradient_exists_unique`; this file proves the analytic dependence.

The coframe and the `Π`-velocity are parametrised by plain coordinates
`CoP N = (Site N → Fin 4 → Fin 4 → ℝ) × (Fin 3 → Site N → Fin 4 → Fin 4 → ℝ)` (`ofCo`), so that
all derivative spaces are standard `Π`-types.

* `analyticAt_phiCo`: the Lagrangian `Φ(q, A) = L°((ofCo q), A)` is jointly analytic on the
  open retained branch (`isOpen_branchCo`).
* **`analyticAt_statRow`**: `(q, A) ↦ γ°_h` (the `⟨·,·⟩_{b,h}`-gradient of `L°` in `A`) is
  jointly analytic on the retained branch; it is a fixed continuous linear function
  (`rowOfDerivCLM`) of `D Φ`.
* `plaqBranch_toA_of_norm_le`: small connections lie on the retained branch.
* **`analyticOnNhd_stationaryConnection`**: on any open set `U` of data obeying the chart
  hypotheses (coframe bound, Cartan least singular value `c_*`, strict load bound
  `‖f°_h‖ < c_* R/4`), the stationary connection (the unique zero of the stationary row in the
  closed `R`-ball) depends analytically on the data, for `hR` below an `N`-independent
  threshold.  The partial derivative `C(e) + D_A N_h` is invertible because
  `‖D_A N_h‖ ≤ c_*/2` (converse mean-value inequality on the ball).
  `analyticOnNhd_statConnCo`: the same for the selected solution `statConnCo`.
* Non-vacuity: `fPh_const_zero` (a constant coframe with zero `Π`-velocity has zero load);
  `exists_open_chartCo`: the chart hypotheses are open conditions (continuity of `C(e)` in
  operator norm and of `f°_h`), so every datum satisfying them strictly has an open
  neighbourhood on which the analytic dependence applies; `flat_statConnCo_nonvacuous`: given
  the flat least singular value `c₀ > 0`, an open neighbourhood of the flat datum carries an
  analytic stationary connection vanishing at the flat datum.
-/

open Finset NormedSpace Metric Filter Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open LogBCH LocalSumGradient

variable {N : ℕ} [NeZero N]

/-! ### Coordinates for the coframe data -/

/-- Plain coordinates for a coframe field and a `Π`-velocity field. -/
abbrev CoP (N : ℕ) := (Site N → Fin 4 → Fin 4 → ℝ) × (Fin 3 → Site N → Fin 4 → Fin 4 → ℝ)

/-- The coframe field and `Π`-velocity field with coordinates `q`. -/
def ofCo (q : CoP N) : (Site N → M4) × (Fin 3 → Site N → M4) :=
  (fun x => Matrix.of (q.1 x), fun i x => Matrix.of (q.2 i x))

/-- The phase-compatible Lagrangian as a function of coordinates and connection. -/
def phiCo (χ Λ : ℝ) (z : CoP N × Conn N) : ℝ :=
  phaseLagr χ Λ (ofCo z.1).1 (ofCo z.1).2 z.2

/-- The stationary row as a function of coordinates and connection. -/
def rowCo (χ Λ : ℝ) (z : CoP N × Conn N) : Conn N :=
  statRow χ Λ (ofCo z.1).1 (ofCo z.1).2 z.2

/-- The retained-branch set in coordinates. -/
def branchCo (N : ℕ) [NeZero N] : Set (CoP N × Conn N) := {z | PlaqBranch (hN N) (toA z.2)}

/-- The coframe entries are analytic in the coordinates. -/
theorem analyticAt_ofCo_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E}
    {g : E → CoP N} (hg : AnalyticAt ℝ g p) (x : Site N) :
    AnalyticAt ℝ (fun z => (ofCo (g z)).1 x) p :=
  analyticAt_of_entries fun a b =>
    analyticAt_pi_apply (analyticAt_pi_apply (analyticAt_pi_apply (analyticAt_fst.comp hg) x) a) b

/-- The `Π`-velocity entries are analytic in the coordinates. -/
theorem analyticAt_ofCo_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E}
    {g : E → CoP N} (hg : AnalyticAt ℝ g p) (i : Fin 3) (x : Site N) :
    AnalyticAt ℝ (fun z => (ofCo (g z)).2 i x) p :=
  analyticAt_of_entries fun a b => analyticAt_pi_apply (analyticAt_pi_apply
    (analyticAt_pi_apply (analyticAt_pi_apply (analyticAt_snd.comp hg) i) x) a) b

/-- **Joint analyticity of the Lagrangian in coordinates** on the retained branch. -/
theorem analyticAt_phiCo (χ Λ : ℝ) (z : CoP N × Conn N) (hz : z ∈ branchCo N) :
    AnalyticAt ℝ (phiCo χ Λ) z := by
  have h3 : AnalyticAt ℝ (fun z : CoP N × Conn N => z.2) z := analyticAt_snd
  have hc : ∀ x μ k, AnalyticAt ℝ (fun z : CoP N × Conn N => z.2 x μ k) z :=
    fun x μ k => analyticAt_pi_apply (analyticAt_pi_apply (analyticAt_pi_apply h3 x) μ) k
  unfold phiCo phaseLagr
  exact analyticAt_gridPair_comp _ fun x => analyticAt_nfDensityPh_comp χ Λ (hN N)
    (analyticAt_ofCo_fst analyticAt_fst) (analyticAt_ofCo_snd analyticAt_fst)
    (fun x => analyticAt_iota_comp fun k => hc x 0 k)
    (fun i x => analyticAt_iota_comp fun k => hc x i.succ k) hz x

/-- The spatial connection matrices are continuous in `(q, A)`. -/
theorem continuous_toA_co : Continuous fun z : CoP N × Conn N => toA z.2 := by
  refine continuous_pi fun i => continuous_pi fun x => continuous_iff_continuousAt.2 fun z => ?_
  have h3 : AnalyticAt ℝ (fun z : CoP N × Conn N => z.2) z := analyticAt_snd
  exact (analyticAt_iota_comp fun k =>
    analyticAt_pi_apply (analyticAt_pi_apply (analyticAt_pi_apply h3 x) i.succ) k).continuousAt

/-- The retained-branch set is open. -/
theorem isOpen_branchCo : IsOpen (branchCo N) :=
  (isOpen_plaqBranch (hN N)).preimage continuous_toA_co

/-- The Lagrangian is analytic on the open retained-branch set. -/
theorem analyticOnNhd_phiCo (χ Λ : ℝ) : AnalyticOnNhd ℝ (phiCo χ Λ) (branchCo N) :=
  fun z hz => analyticAt_phiCo χ Λ z hz

/-! ### The stationary row as a linear function of `DΦ` -/

/-- The gradient field read off a derivative of `Φ`:
`ℓ ↦ (y ↦ (h³)⁻¹ rieszInv(ℓ ∘ inr ∘ single y))`. -/
def rowOfDeriv (ℓ : (CoP N × Conn N) →L[ℝ] ℝ) : Conn N :=
  fun y => (hN N ^ 3)⁻¹ • rieszInv ((ℓ.comp (ContinuousLinearMap.inr ℝ (CoP N) (Conn N))).comp
    (ContinuousLinearMap.single ℝ (fun _ : Site N => LocVal) y))

/-- `rowOfDeriv` as a linear map. -/
def rowOfDerivLin : ((CoP N × Conn N) →L[ℝ] ℝ) →ₗ[ℝ] Conn N where
  toFun := rowOfDeriv
  map_add' ℓ ℓ' := by
    funext y
    simp [rowOfDeriv, ContinuousLinearMap.add_comp, smul_add]
  map_smul' c ℓ := by
    funext y
    simp [rowOfDeriv, ContinuousLinearMap.smul_comp, smul_comm c]

/-- `rowOfDeriv` as a continuous linear map (finite dimension). -/
def rowOfDerivCLM : ((CoP N × Conn N) →L[ℝ] ℝ) →L[ℝ] Conn N :=
  LinearMap.toContinuousLinearMap rowOfDerivLin

/-- On the retained branch, the stationary row is `rowOfDeriv (DΦ)`:
`D_A L°(e, ∂_tΠ; A) = DΦ(q, A) ∘ inr`. -/
theorem rowCo_eq (χ Λ : ℝ) {z : CoP N × Conn N} (hz : z ∈ branchCo N) :
    rowCo χ Λ z = rowOfDerivCLM (fderiv ℝ (phiCo χ Λ) z) := by
  obtain ⟨p, A⟩ := z
  have hd : DifferentiableAt ℝ (phiCo χ Λ) (p, A) := (analyticAt_phiCo χ Λ _ hz).differentiableAt
  have hcomp : HasFDerivAt (fun B => phiCo χ Λ (p, B))
      ((fderiv ℝ (phiCo χ Λ) (p, A)).comp (ContinuousLinearMap.inr ℝ (CoP N) (Conn N))) A :=
    hd.hasFDerivAt.comp A (hasFDerivAt_prodMk_right p A)
  have hf : fderiv ℝ (phaseLagr χ Λ (ofCo p).1 (ofCo p).2) A =
      (fderiv ℝ (phiCo χ Λ) (p, A)).comp (ContinuousLinearMap.inr ℝ (CoP N) (Conn N)) :=
    hcomp.fderiv
  funext y
  simp only [rowCo, statRow, siteGrad, hf]
  rfl

/-- **Joint analyticity of the stationary row** (`eq:supp-exact-stationary-connection`): the map
`(q, A) ↦ γ°_h(ofCo q, A)` is analytic at every point of the retained branch. -/
theorem analyticAt_statRow (χ Λ : ℝ) {z : CoP N × Conn N} (hz : z ∈ branchCo N) :
    AnalyticAt ℝ (fun z : CoP N × Conn N => statRow χ Λ (ofCo z.1).1 (ofCo z.1).2 z.2) z := by
  have h1 : AnalyticAt ℝ (fun z => rowOfDerivCLM (fderiv ℝ (phiCo χ Λ) z)) z :=
    ((rowOfDerivCLM (N := N)).analyticAt _).comp ((analyticOnNhd_phiCo χ Λ).fderiv z hz)
  refine h1.congr ?_
  filter_upwards [isOpen_branchCo.mem_nhds hz] with w hw
  exact (rowCo_eq χ Λ hw).symm

/-- `rowCo` is analytic on the retained branch. -/
theorem analyticOnNhd_rowCo (χ Λ : ℝ) : AnalyticOnNhd ℝ (rowCo χ Λ) (branchCo N) :=
  fun _ hz => analyticAt_statRow χ Λ hz

/-! ### Small connections lie on the retained branch -/

/-- If `‖ι c‖ ≤ C‖c‖` and `h C ‖A‖ ≤ 1/16`, every plaquette of `A` lies in the principal chart. -/
theorem plaqBranch_toA_of_norm_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ c, ‖iota c‖ ≤ C * ‖c‖)
    (A : Conn N) (hA : hN N * C * ‖A‖ ≤ 1 / 16) : PlaqBranch (hN N) (toA A) := by
  intro i j x
  refine PlaquetteBCH.norm_expProd_sub_one_lt _ ?_
  have hb : ∀ (y : Site N) (k : Fin 3), ‖toA A k y‖ ≤ C * ‖A‖ := fun y k =>
    (hC _).trans (mul_le_mul_of_nonneg_left
      ((norm_le_pi_norm (A y) k.succ).trans (norm_le_pi_norm A y)) hC0)
  have hh := hN_pos (N := N)
  have b1 := mul_le_mul_of_nonneg_left (hb x i) hh.le
  have b2 := mul_le_mul_of_nonneg_left (hb (x + unitVec i) j) hh.le
  have b3 := mul_le_mul_of_nonneg_left (hb (x + unitVec j) i) hh.le
  have b4 := mul_le_mul_of_nonneg_left (hb x j) hh.le
  simp only [plaqList, normSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  nlinarith

/-! ### Analytic dependence of the stationary connection -/

/-- **Clause (ii) of `thm:supp-exact-action-provenance`, analytic dependence.**  Fix `χ, Λ`, a
coframe bound `E_max` and a least singular value `c_* > 0`.  There is a threshold `ε > 0`,
independent of the cutoff `N`, such that: if `hR ≤ ε` (`h = 1/N`), `U` is an open set of
coframe/`Π`-velocity data on which `‖e(x)‖ ≤ E_max`, `c_*‖A‖ ≤ ‖C(e)A‖` and the strict load bound
`‖f°_h‖ < c_* R/4` hold, and `s q` is a zero of the stationary row in the closed `R`-ball for every
`q ∈ U` (it is then the unique one), then `q ↦ s q` is analytic on `U`. -/
theorem analyticOnNhd_stationaryConnection (χ Λ Emax c : ℝ) (hc : 0 < c) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ) (U : Set (CoP N)) (s : CoP N → Conn N),
      0 ≤ R → hN N * R ≤ ε → IsOpen U →
      (∀ q ∈ U, ∀ x, ‖(ofCo q).1 x‖ ≤ Emax) →
      (∀ q ∈ U, ∀ A : Conn N, c * ‖A‖ ≤ ‖cartanOp χ (ofCo q).1 A‖) →
      (∀ q ∈ U, ‖fPh χ (ofCo q).1 (ofCo q).2‖ < c * R / 4) →
      (∀ q ∈ U, s q ∈ closedBall (0 : Conn N) R ∧
        statRow χ Λ (ofCo q).1 (ofCo q).2 (s q) = 0) →
      AnalyticOnNhd ℝ s U := by
  obtain ⟨ε₁, hε₁, hstat⟩ := stationary_connection_gradient_exists_unique χ Λ Emax c hc
  obtain ⟨ε₀, hε₀, κ, hκ, hlip⟩ := exists_Nh_lipschitz
  obtain ⟨Cι, hCι1, hCι⟩ := exists_iota_bound
  set M := κ * (|χ| * Emax ^ 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hCι0 : 0 < Cι := by linarith
  refine ⟨min (min ε₁ ε₀) (min (c / (2 * (M + 1))) (1 / (16 * Cι))), by positivity, ?_⟩
  intro N _ R U s hR hhR hU he hC hf hs
  have hh := hN_pos (N := N)
  have hhR1 : hN N * R ≤ ε₁ := hhR.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhR0 : hN N * R ≤ ε₀ := hhR.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhR2 : hN N * R ≤ c / (2 * (M + 1)) :=
    hhR.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhR3 : hN N * R ≤ 1 / (16 * Cι) := hhR.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hhpos : 0 ≤ hN N * R := mul_nonneg hh.le hR
  have hML : M * (hN N * R) ≤ c / 2 := by
    have h1 : M * (hN N * R) ≤ M * (c / (2 * (M + 1))) := by gcongr
    have h2 : M * (c / (2 * (M + 1))) ≤ c / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact h1.trans h2
  have hbr : ∀ A : Conn N, ‖A‖ ≤ R → (q : CoP N) → (q, A) ∈ branchCo N := by
    intro A hA q
    refine plaqBranch_toA_of_norm_le hCι0.le hCι A ?_
    calc hN N * Cι * ‖A‖ ≤ hN N * Cι * R := by gcongr
      _ = (hN N * R) * Cι := by ring
      _ ≤ 1 / (16 * Cι) * Cι := by gcongr
      _ = 1 / 16 := by field_simp
  -- data at each point of `U`
  have hdata : ∀ q ∈ U, s q ∈ ball (0 : Conn N) R ∧
      (∀ a ∈ closedBall (0 : Conn N) R, rowCo χ Λ (q, a) = 0 → a = s q) ∧
      ∀ a ∈ closedBall (0 : Conn N) R, statRow χ Λ (ofCo q).1 (ofCo q).2 a =
        statRowExplicit χ (ofCo q).1 (ofCo q).2 a := by
    intro q hq
    obtain ⟨hex, hbd, hball⟩ :=
      hstat N R (ofCo q).1 (ofCo q).2 hR hhR1 (he q hq) (hC q hq) (hf q hq).le
    refine ⟨?_, fun a ha hFa => hex.unique ⟨ha, hFa⟩ (hs q hq), hball⟩
    have hb := hbd (s q) (hs q hq).1 (hs q hq).2
    have hfq := hf q hq
    have hR0 : 0 < R := by
      by_contra hR0
      rw [not_lt] at hR0
      have : c * R / 4 ≤ 0 := by
        have : c * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le hR0
        linarith
      linarith [norm_nonneg (fPh χ (ofCo q).1 (ofCo q).2)]
    rw [mem_ball_zero_iff]
    calc ‖s q‖ ≤ 2 * c⁻¹ * ‖fPh χ (ofCo q).1 (ofCo q).2‖ := hb
      _ < 2 * c⁻¹ * (c * R / 4) := by gcongr
      _ = R / 2 := by field_simp; ring
      _ < R := by linarith
  refine StationaryContraction.analyticOnNhd_of_unique_zero_closedBall (F := rowCo χ Λ) hU
    (R := R) (fun q hq => analyticOnNhd_rowCo χ Λ _ (hbr _
      (mem_closedBall_zero_iff.1 (hs q hq).1) q))
    (fun q hq => (hdata q hq).1) (fun q hq => (hs q hq).2) (fun q hq => (hdata q hq).2.1) ?_
  -- invertibility of the partial derivative `C(e) + D_A N_h`
  intro q hq
  set e := (ofCo q).1 with he_def
  set P := (ofCo q).2 with hP_def
  set A := s q with hA_def
  obtain ⟨hAball, -, hball⟩ := hdata q hq
  set T := (fderiv ℝ (rowCo χ Λ) (q, A)).comp (ContinuousLinearMap.inr ℝ (CoP N) (Conn N))
    with hT_def
  have hdiff : DifferentiableAt ℝ (rowCo χ Λ) (q, A) :=
    (analyticOnNhd_rowCo χ Λ _ (hbr _ (mem_closedBall_zero_iff.1 (hs q hq).1) q)).differentiableAt
  have hTd : HasFDerivAt (fun a => rowCo χ Λ (q, a)) T A :=
    hdiff.hasFDerivAt.comp A (hasFDerivAt_prodMk_right q A)
  have hG : HasFDerivAt (fun a => rowCo χ Λ (q, a) - cartanCLM χ e a - fPh χ e P)
      (T - cartanCLM χ e) A :=
    (hTd.sub (cartanCLM χ e).hasFDerivAt).sub_const _
  have hGN : ∀ a ∈ closedBall (0 : Conn N) R,
      rowCo χ Λ (q, a) - cartanCLM χ e a - fPh χ e P = Nh χ e a := by
    intro a ha
    change statRow χ Λ e P a - cartanCLM χ e a - fPh χ e P = Nh χ e a
    rw [hball a ha, statRowExplicit, cartanCLM_apply]
    abel
  have hLip : LipschitzOnWith (Real.toNNReal (M * (hN N * R)))
      (fun a => rowCo χ Λ (q, a) - cartanCLM χ e a - fPh χ e P) (closedBall (0 : Conn N) R) := by
    refine LipschitzOnWith.of_dist_le' fun a ha b hb => ?_
    simp only [dist_eq_norm]
    rw [hGN a ha, hGN b hb]
    exact hlip N χ Emax R e hR hhR0 (he q hq) a b (mem_closedBall_zero_iff.1 ha)
      (mem_closedBall_zero_iff.1 hb)
  have hnhds : closedBall (0 : Conn N) R ∈ 𝓝 A :=
    mem_of_superset (isOpen_ball.mem_nhds hAball) ball_subset_closedBall
  have hnorm : ‖T - cartanCLM χ e‖ ≤ M * (hN N * R) := by
    have := norm_fderiv_le_of_lipschitzOn ℝ hnhds hLip
    rwa [hG.fderiv, Real.coe_toNNReal _ (by positivity)] at this
  have hlow : ∀ δ : Conn N, c / 2 * ‖δ‖ ≤ ‖T δ‖ := by
    intro δ
    have h1 : c * ‖δ‖ ≤ ‖cartanCLM χ e δ‖ := hC q hq δ
    have h2 : ‖(T - cartanCLM χ e) δ‖ ≤ c / 2 * ‖δ‖ :=
      ((T - cartanCLM χ e).le_opNorm δ).trans
        (mul_le_mul_of_nonneg_right (hnorm.trans hML) (norm_nonneg _))
    have h3 : cartanCLM χ e δ = T δ - (T - cartanCLM χ e) δ := by
      simp
    have h4 := norm_sub_le (T δ) ((T - cartanCLM χ e) δ)
    rw [← h3] at h4
    linarith
  obtain ⟨Tinv, h1, h2, -⟩ :=
    StationaryContraction.exists_inverse_of_lower_bound (by positivity : 0 < c / 2) hlow
  exact ⟨ContinuousLinearEquiv.equivOfInverse T Tinv h1 h2, rfl⟩

/-! ### The selected stationary connection -/

/-- The selected stationary connection `𝒜_h(q)`: a zero of the stationary row in the closed
`R`-ball (chosen), or `0` if there is none. -/
def statConnCo (χ Λ R : ℝ) (q : CoP N) : Conn N :=
  open Classical in
  if h : ∃ A : Conn N, A ∈ closedBall (0 : Conn N) R ∧ statRow χ Λ (ofCo q).1 (ofCo q).2 A = 0
  then h.choose else 0

/-- The selected connection is a zero in the closed ball whenever one exists. -/
theorem statConnCo_spec {χ Λ R : ℝ} {q : CoP N}
    (h : ∃ A : Conn N, A ∈ closedBall (0 : Conn N) R ∧ statRow χ Λ (ofCo q).1 (ofCo q).2 A = 0) :
    statConnCo χ Λ R q ∈ closedBall (0 : Conn N) R ∧
      statRow χ Λ (ofCo q).1 (ofCo q).2 (statConnCo χ Λ R q) = 0 := by
  unfold statConnCo
  split_ifs
  exact h.choose_spec

/-- **Clause (ii), selected-solution form**: under the chart hypotheses on an open set `U` (strict
load bound) and for `hR` below an `N`-independent threshold, the selected stationary connection
`𝒜_h = statConnCo` is the unique zero of the stationary row in the closed `R`-ball, it obeys
`‖𝒜_h‖ ≤ 2c_*⁻¹‖f°_h‖` (so it vanishes for zero load), and it is analytic on `U`. -/
theorem analyticOnNhd_statConnCo (χ Λ Emax c : ℝ) (hc : 0 < c) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ) (U : Set (CoP N)),
      0 ≤ R → hN N * R ≤ ε → IsOpen U →
      (∀ q ∈ U, ∀ x, ‖(ofCo q).1 x‖ ≤ Emax) →
      (∀ q ∈ U, ∀ A : Conn N, c * ‖A‖ ≤ ‖cartanOp χ (ofCo q).1 A‖) →
      (∀ q ∈ U, ‖fPh χ (ofCo q).1 (ofCo q).2‖ < c * R / 4) →
      (∀ q ∈ U, (∀ A : Conn N, A ∈ closedBall (0 : Conn N) R →
          (statRow χ Λ (ofCo q).1 (ofCo q).2 A = 0 ↔ A = statConnCo χ Λ R q)) ∧
        ‖statConnCo χ Λ R q‖ ≤ 2 * c⁻¹ * ‖fPh χ (ofCo q).1 (ofCo q).2‖) ∧
      AnalyticOnNhd ℝ (statConnCo χ Λ R) U := by
  obtain ⟨ε₁, hε₁, hstat⟩ := stationary_connection_gradient_exists_unique χ Λ Emax c hc
  obtain ⟨ε₂, hε₂, han⟩ := analyticOnNhd_stationaryConnection χ Λ Emax c hc
  refine ⟨min ε₁ ε₂, by positivity, ?_⟩
  intro N _ R U hR hhR hU he hC hf
  have hspec : ∀ q ∈ U, statConnCo χ Λ R q ∈ closedBall (0 : Conn N) R ∧
      statRow χ Λ (ofCo q).1 (ofCo q).2 (statConnCo χ Λ R q) = 0 ∧
      (∀ A : Conn N, A ∈ closedBall (0 : Conn N) R →
        statRow χ Λ (ofCo q).1 (ofCo q).2 A = 0 → A = statConnCo χ Λ R q) ∧
      ‖statConnCo χ Λ R q‖ ≤ 2 * c⁻¹ * ‖fPh χ (ofCo q).1 (ofCo q).2‖ := by
    intro q hq
    obtain ⟨hex, hbd, -⟩ := hstat N R (ofCo q).1 (ofCo q).2 hR (hhR.trans (min_le_left _ _))
      (he q hq) (hC q hq) (hf q hq).le
    have hs := statConnCo_spec (χ := χ) (Λ := Λ) hex.exists
    exact ⟨hs.1, hs.2, fun A hA hz => hex.unique ⟨hA, hz⟩ hs, hbd _ hs.1 hs.2⟩
  refine ⟨fun q hq => ⟨fun A hA => ⟨(hspec q hq).2.2.1 A hA, fun h => h ▸ (hspec q hq).2.1⟩,
    (hspec q hq).2.2.2⟩, ?_⟩
  exact han N R U (statConnCo χ Λ R) hR (hhR.trans (min_le_right _ _)) hU he hC hf
    fun q hq => ⟨(hspec q hq).1, (hspec q hq).2.1⟩

/-! ### Non-vacuity: zero load at constant coframes, openness of the chart -/

open OddPhaseDerivativeReal in
/-- A constant coframe with zero `Π`-velocity has zero phase-compatible load. -/
theorem fPh_const_zero (χ : ℝ) (E : M4) :
    fPh χ (fun _ : Site N => E) (0 : Fin 3 → Site N → M4) = 0 := by
  have h0 : ∀ x : Site N, load0Ph χ (fun _ => E) x = 0 := by
    intro x; simp [load0Ph, pd_const]
  have h1 : ∀ (i : Fin 3) (x : Site N), loadSpPh χ (fun _ => E) i x = 0 := by
    intro i x; simp [loadSpPh, pd_const]
  have hc : coord (0 : M4) = 0 := by
    funext k; simp [coord, pairing]
  funext x μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp [fPh, h0, hc]
  · simp [fPh, h1, hc]

/-- `coord` of an analytic matrix-valued map is analytic. -/
theorem analyticAt_coord_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E}
    {f : E → M4} (hf : AnalyticAt ℝ f p) (k : Fin 6) :
    AnalyticAt ℝ (fun q => coord (f q) k) p := by
  unfold coord
  exact (analyticAt_pairing_comp analyticAt_const hf).div_const

/-- The Cartan operator applied to a fixed connection is continuous in the coframe coordinates. -/
theorem continuous_cartanOp_co (χ : ℝ) (A : Conn N) :
    Continuous fun q : CoP N => cartanOp χ (ofCo q).1 A := by
  refine continuous_pi fun x => continuous_pi fun μ => continuous_pi fun k =>
    continuous_iff_continuousAt.2 fun q => ?_
  have he : ∀ y, AnalyticAt ℝ (fun q : CoP N => (ofCo q).1 y) q :=
    fun y => analyticAt_ofCo_fst (g := fun q : CoP N => q) analyticAt_id y
  refine AnalyticAt.continuousAt (𝕜 := ℝ) ?_
  cases μ using Fin.cases with
  | zero =>
    simp only [cartanOp, Fin.cases_zero]
    refine analyticAt_coord_comp ?_ k
    unfold cart0
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      analyticAt_bracket_comp analyticAt_const (analyticAt_piArr_comp χ i (he x))
  | succ i =>
    simp only [cartanOp, Fin.cases_succ]
    refine analyticAt_coord_comp ?_ k
    unfold cartSp
    exact (analyticAt_bracket_comp (analyticAt_piArr_comp χ i (he x)) analyticAt_const).add
      (Finset.analyticAt_fun_sum _ fun j _ =>
        analyticAt_bracket_comp analyticAt_const (analyticAt_sigmaArr_comp χ i j (he x)))

/-- The Cartan operator is continuous in the coframe coordinates (operator norm). -/
theorem continuous_cartanCLM_co (χ : ℝ) :
    Continuous fun q : CoP N => cartanCLM χ (ofCo q).1 :=
  continuous_clm_apply.2 fun A => by
    simpa only [cartanCLM_apply] using continuous_cartanOp_co χ A

/-- The phase-compatible load is continuous in the coordinates. -/
theorem continuous_fPh_co (χ : ℝ) :
    Continuous fun q : CoP N => fPh χ (ofCo q).1 (ofCo q).2 := by
  refine continuous_pi fun x => continuous_pi fun μ => continuous_pi fun k =>
    continuous_iff_continuousAt.2 fun q => ?_
  have he : ∀ y, AnalyticAt ℝ (fun q : CoP N => (ofCo q).1 y) q :=
    fun y => analyticAt_ofCo_fst (g := fun q : CoP N => q) analyticAt_id y
  refine AnalyticAt.continuousAt (𝕜 := ℝ) ?_
  cases μ using Fin.cases with
  | zero =>
    simp only [fPh, Fin.cases_zero]
    exact analyticAt_coord_comp (analyticAt_load0Ph_comp χ he x) k
  | succ i =>
    simp only [fPh, Fin.cases_succ]
    exact analyticAt_coord_comp
      ((analyticAt_ofCo_snd (g := fun q : CoP N => q) analyticAt_id i x).neg.add
      (analyticAt_loadSpPh_comp χ he i x)) k

/-- The coframe at a site is continuous in the coordinates. -/
theorem continuous_ofCo_fst (x : Site N) : Continuous fun q : CoP N => (ofCo q).1 x :=
  continuous_iff_continuousAt.2 fun _ =>
    (analyticAt_ofCo_fst (g := fun q : CoP N => q) analyticAt_id x).continuousAt

/-- **The chart hypotheses are open conditions.**  If a datum `q₀` satisfies them strictly
(`‖e₀(x)‖ < E_max`, least singular value `c₀`, `‖f°_h(q₀)‖ < c₀R/8`), then there is an open
neighbourhood `U ∋ q₀` on which they hold with `c_* = c₀/2`. -/
theorem exists_open_chartCo (χ Emax c₀ R : ℝ) (hc₀ : 0 < c₀) (q₀ : CoP N)
    (he : ∀ x, ‖(ofCo q₀).1 x‖ < Emax)
    (hC : ∀ A : Conn N, c₀ * ‖A‖ ≤ ‖cartanOp χ (ofCo q₀).1 A‖)
    (hf : ‖fPh χ (ofCo q₀).1 (ofCo q₀).2‖ < c₀ * R / 8) :
    ∃ U : Set (CoP N), IsOpen U ∧ q₀ ∈ U ∧
      (∀ q ∈ U, ∀ x, ‖(ofCo q).1 x‖ ≤ Emax) ∧
      (∀ q ∈ U, ∀ A : Conn N, c₀ / 2 * ‖A‖ ≤ ‖cartanOp χ (ofCo q).1 A‖) ∧
      (∀ q ∈ U, ‖fPh χ (ofCo q).1 (ofCo q).2‖ < c₀ / 2 * R / 4) := by
  set U : Set (CoP N) := (⋂ x : Site N, {q | ‖(ofCo q).1 x‖ < Emax}) ∩
    ({q | ‖cartanCLM χ (ofCo q).1 - cartanCLM χ (ofCo q₀).1‖ < c₀ / 2} ∩
      {q | ‖fPh χ (ofCo q).1 (ofCo q).2‖ < c₀ * R / 8}) with hU
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · refine (isOpen_iInter_of_finite fun x =>
      isOpen_lt (continuous_norm.comp (continuous_ofCo_fst x)) continuous_const).inter
      ((isOpen_lt (continuous_norm.comp ((continuous_cartanCLM_co χ).sub continuous_const))
        continuous_const).inter
      (isOpen_lt (continuous_norm.comp (continuous_fPh_co χ)) continuous_const))
  · refine ⟨Set.mem_iInter.2 fun x => he x, ?_, hf⟩
    change ‖cartanCLM χ (ofCo q₀).1 - cartanCLM χ (ofCo q₀).1‖ < c₀ / 2
    rw [sub_self, norm_zero]; positivity
  · intro q hq x
    exact (Set.mem_iInter.1 hq.1 x).le
  · intro q hq A
    have h1 := hC A
    have hq2 : ‖cartanCLM χ (ofCo q).1 - cartanCLM χ (ofCo q₀).1‖ < c₀ / 2 := hq.2.1
    have h2 : ‖(cartanCLM χ (ofCo q).1 - cartanCLM χ (ofCo q₀).1) A‖ ≤ c₀ / 2 * ‖A‖ :=
      (ContinuousLinearMap.le_opNorm _ A).trans
        (mul_le_mul_of_nonneg_right hq2.le (norm_nonneg _))
    have h3 : cartanOp χ (ofCo q₀).1 A = cartanCLM χ (ofCo q).1 A -
        (cartanCLM χ (ofCo q).1 - cartanCLM χ (ofCo q₀).1) A := by simp
    have h4 := norm_sub_le (cartanCLM χ (ofCo q).1 A)
      ((cartanCLM χ (ofCo q).1 - cartanCLM χ (ofCo q₀).1) A)
    rw [← h3, cartanCLM_apply] at h4
    linarith
  · intro q hq
    have : ‖fPh χ (ofCo q).1 (ofCo q).2‖ < c₀ * R / 8 := hq.2.2
    linarith

/-- The flat coordinates: unit coframe, zero `Π`-velocity. -/
def flatCo (N : ℕ) [NeZero N] : CoP N := (fun _ a b => (1 : M4) a b, 0)

/-- The flat coordinates describe the unit coframe and zero `Π`-velocity. -/
theorem ofCo_flatCo : ofCo (flatCo N) = ((fun _ => (1 : M4)), (0 : Fin 3 → Site N → M4)) := by
  simp only [ofCo, flatCo]
  congr 1

/-- **Non-vacuity at flat data.**  Assume the flat Cartan operator has least singular value
`c₀ > 0` (for `χ ≠ 0` this holds with `c₀ = 2|χ|/3`, proved separately).  Then there is an
`N`-independent threshold `ε > 0` such that for every regulator and every `R > 0` with `hR ≤ ε`
there is an open neighbourhood `U` of the flat datum on which the selected stationary connection
is analytic, and it vanishes at the flat datum. -/
theorem flat_statConnCo_nonvacuous (χ Λ c₀ : ℝ) (hc₀ : 0 < c₀)
    (hflat : ∀ (N : ℕ) [NeZero N] (A : Conn N),
      c₀ * ‖A‖ ≤ ‖cartanOp χ (fun _ : Site N => (1 : M4)) A‖) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ), 0 < R → hN N * R ≤ ε →
      ∃ U : Set (CoP N), IsOpen U ∧ flatCo N ∈ U ∧ AnalyticOnNhd ℝ (statConnCo χ Λ R) U ∧
        statConnCo χ Λ R (flatCo N) = 0 := by
  obtain ⟨ε, hε, h⟩ := analyticOnNhd_statConnCo χ Λ 2 (c₀ / 2) (by positivity)
  refine ⟨ε, hε, fun N _ R hR hhR => ?_⟩
  have hf0 : fPh χ (ofCo (flatCo N)).1 (ofCo (flatCo N)).2 = 0 := by
    rw [ofCo_flatCo]; exact fPh_const_zero χ 1
  obtain ⟨U, hUo, hq₀, he, hC, hf⟩ := exists_open_chartCo (N := N) χ 2 c₀ R hc₀ (flatCo N)
    (fun x => by rw [ofCo_flatCo]; simp)
    (fun A => by rw [ofCo_flatCo]; exact hflat N A)
    (by rw [hf0, norm_zero]; positivity)
  obtain ⟨hspec, han⟩ := h N R U hR.le hhR hUo he hC hf
  refine ⟨U, hUo, hq₀, han, ?_⟩
  have := (hspec _ hq₀).2
  rw [hf0, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

end RenewalGeometry.ExactPhaseAction
