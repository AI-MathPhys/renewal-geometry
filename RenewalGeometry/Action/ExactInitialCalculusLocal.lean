/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactStationaryConnection
import RenewalGeometry.Analysis.AnalyticCoordinateDivision

/-!
# The link remainder of the explicit action as a spacing-analytic local operator
  (infrastructure for `lem:supp-initial-calculus`: "the full link remainder starts at cubic order in
  the flat connection", uniformly in the lattice spacing; emergent-spacetime manuscript)

The local link remainder `r_h(e, A)(x)` of the explicit phase-compatible action contains the
rescaled remainders `ρ^E_h(p) = h⁻² adRem(h p)` and `ρ^B_h(Y) = h⁻² plaqRem(h Y)`.

* `exists_GE`, `exists_GB`, `GE`, `GB`: by the coordinate-division theorem
  (`AnalyticDivision.exists_scaled_cubic`) and the cubic bounds `norm_adRem_le`, `norm_plaqRem_le`,
  there are maps `G^E, G^B`, **jointly analytic in `(s, p)` at `(0, 0)`**, with
  `G^E(h, p) = ρ^E_h(p)` and `G^B(h, Y) = ρ^B_h(Y)` for `0 < h < δ`, `‖p‖, ‖Y‖ < δ`
  (`GE_eq_rhoE`, `GB_eq_rhoB`, one `N`-independent `δ`).
* `remLocJ χ (s, E, w)`: the local remainder density with `G^E, G^B` in place of `ρ^E_h, ρ^B_h`,
  analytic at every `(0, E, 0)` (`analyticAt_remLocJ`) and equal to `remLocal χ h e x w` for small
  `h`, `w` (`remLocal_eq_remLocJ`).
* `remLocJw`: its derivative in the local configuration; `analyticAt_remLocJw`.
* **`Nh_eq_NhLoc`**: for `hN N < δ` and `‖A‖ < δ` (sup norm; `δ` independent of `N`), the remainder
  gradient is the local formula
  `N_h(e, A)(x) = Σ_ℓ rieszInv(D_w r(h, e(x - o_ℓ), (A(x - o_ℓ + o_ν))_ν) ∘ ι_ℓ)`,
  i.e. a finite sum of shifted pointwise maps whose coefficients are analytic in `h` through
  `h = 0` (`analyticAt_NhLoc`).
-/

open Filter Finset Metric
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.InitialCalculus

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open LinkRemainder AnalyticDivision LocalSumGradient

/-! ### The jointly analytic rescaled remainders -/

theorem exists_GE : ∃ G : ℝ × (M4 × M4) → M4, AnalyticAt ℝ G (0, 0) ∧
    ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : M4 × M4)), z.1 ^ 2 • G z = adRem (z.1 • z.2) := by
  refine exists_scaled_cubic (analyticAt_adRem 0) (C := 16) ?_
  have hb : Metric.ball (0 : M4 × M4) 1 ∈ 𝓝 (0 : M4 × M4) := Metric.ball_mem_nhds _ one_pos
  filter_upwards [hb] with v hv
  exact norm_adRem_le v (by simpa using (mem_ball_zero_iff.mp hv).le)

theorem exists_GB : ∃ G : ℝ × (Fin 4 → M4) → M4, AnalyticAt ℝ G (0, 0) ∧
    ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : Fin 4 → M4)), z.1 ^ 2 • G z = plaqRem (z.1 • z.2) := by
  refine exists_scaled_cubic (analyticOnNhd_plaqRem 0 (mem_ball_self (by norm_num))) (C := 384) ?_
  have hb : Metric.ball (0 : Fin 4 → M4) (1 / 16) ∈ 𝓝 (0 : Fin 4 → M4) :=
    Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [hb] with v hv
  exact norm_plaqRem_le v (mem_ball_zero_iff.mp hv).le

/-- The jointly analytic Ad-link remainder `G^E(s, p)` (`= s⁻² adRem(s p)` for small `s ≠ 0`). -/
def GE : ℝ × (M4 × M4) → M4 := Classical.choose exists_GE

/-- The jointly analytic plaquette remainder `G^B(s, Y)` (`= s⁻² plaqRem(s Y)` for small
`s ≠ 0`). -/
def GB : ℝ × (Fin 4 → M4) → M4 := Classical.choose exists_GB

theorem analyticAt_GE : AnalyticAt ℝ GE (0, 0) := (Classical.choose_spec exists_GE).1

theorem analyticAt_GB : AnalyticAt ℝ GB (0, 0) := (Classical.choose_spec exists_GB).1

/-- A common `N`-independent radius on which both rescaled remainders are the lattice ones. -/
theorem exists_radius_G : ∃ δ > 0, ∀ (s : ℝ), 0 < s → s < δ →
    (∀ p : M4 × M4, ‖p‖ < δ → GE (s, p) = rhoE s p) ∧
    (∀ Y : Fin 4 → M4, ‖Y‖ < δ → GB (s, Y) = rhoB s Y) := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.eventually_nhds_iff.mp (Classical.choose_spec exists_GE).2
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.eventually_nhds_iff.mp (Classical.choose_spec exists_GB).2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs hsδ => ⟨fun p hp => ?_, fun Y hY => ?_⟩⟩
  · have hd : dist ((s, p) : ℝ × (M4 × M4)) (0, 0) < δ₁ := by
      rw [Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs, abs_of_pos hs]
      exact max_lt (hsδ.trans_le (min_le_left _ _)) (hp.trans_le (min_le_left _ _))
    have h := h₁ hd
    change s ^ 2 • GE (s, p) = adRem (s • p) at h
    rw [rhoE, ← h, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hs.ne'), one_smul]
  · have hd : dist ((s, Y) : ℝ × (Fin 4 → M4)) (0, 0) < δ₂ := by
      rw [Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs, abs_of_pos hs]
      exact max_lt (hsδ.trans_le (min_le_right _ _)) (hY.trans_le (min_le_right _ _))
    have h := h₂ hd
    change s ^ 2 • GB (s, Y) = plaqRem (s • Y) at h
    rw [rhoB, ← h, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hs.ne'), one_smul]

/-! ### The jointly analytic local remainder -/

/-- Local configuration space of the remainder: `w ℓ = A(x + o_ℓ)`. -/
abbrev Cfg := Fin 4 → LocVal

/-- **The local remainder density with jointly analytic rescaled remainders**, as a function of
`(s, E, w)` (spacing, coframe value, local configuration). -/
def remLocJ (χ : ℝ) (q : ℝ × M4 × Cfg) : ℝ :=
  ∑ i : Fin 3, pairingLeft (-piArr χ q.2.1 i) (GE (q.1, projE i q.2.2)) +
    (pairingLeft (sigmaArr χ q.2.1 0 1) (GB (q.1, projB 0 1 q.2.2)) +
      pairingLeft (sigmaArr χ q.2.1 0 2) (GB (q.1, projB 0 2 q.2.2)) +
      pairingLeft (sigmaArr χ q.2.1 1 2) (GB (q.1, projB 1 2 q.2.2)))

theorem analyticAt_pairingLeft_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E}
    {f g : E → M4} (hf : AnalyticAt ℝ f p) (hg : AnalyticAt ℝ g p) :
    AnalyticAt ℝ (fun q => pairingLeft (f q) (g q)) p := by
  have : (fun q => pairingLeft (f q) (g q)) = fun q => pairing (f q) (g q) := rfl
  rw [this]
  exact analyticAt_pairing_comp hf hg

theorem analyticAt_projE_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E}
    {w : E → Cfg} (hw : AnalyticAt ℝ w p) (i : Fin 3) :
    AnalyticAt ℝ (fun q => projE i (w q)) p :=
  ((LinearMap.toContinuousLinearMap (projE i)).analyticAt _).comp hw

theorem analyticAt_projB_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E}
    {w : E → Cfg} (hw : AnalyticAt ℝ w p) (i j : Fin 3) :
    AnalyticAt ℝ (fun q => projB i j (w q)) p :=
  ((LinearMap.toContinuousLinearMap (projB i j)).analyticAt _).comp hw

/-- The local remainder density is analytic at every `(0, E, 0)`. -/
theorem analyticAt_remLocJ (χ : ℝ) (E : M4) : AnalyticAt ℝ (remLocJ χ) (0, E, 0) := by
  have hs : AnalyticAt ℝ (fun q : ℝ × M4 × Cfg => q.1) (0, E, 0) := analyticAt_fst
  have hE : AnalyticAt ℝ (fun q : ℝ × M4 × Cfg => q.2.1) (0, E, 0) :=
    analyticAt_fst.comp analyticAt_snd
  have hw : AnalyticAt ℝ (fun q : ℝ × M4 × Cfg => q.2.2) (0, E, 0) :=
    analyticAt_snd.comp analyticAt_snd
  have hGE : ∀ i : Fin 3, AnalyticAt ℝ (fun q : ℝ × M4 × Cfg => GE (q.1, projE i q.2.2)) (0, E, 0) :=
    fun i => analyticAt_GE.comp_of_eq (hs.prod (analyticAt_projE_comp hw i)) (by simp)
  have hGB : ∀ i j : Fin 3, AnalyticAt ℝ (fun q : ℝ × M4 × Cfg => GB (q.1, projB i j q.2.2))
      (0, E, 0) :=
    fun i j => analyticAt_GB.comp_of_eq (hs.prod (analyticAt_projB_comp hw i j)) (by simp)
  have hpi : ∀ i : Fin 3, AnalyticAt ℝ (fun q : ℝ × M4 × Cfg => -piArr χ q.2.1 i) (0, E, 0) :=
    fun i => (analyticAt_piArr_comp χ i hE).neg
  have hsig : ∀ i j : Fin 3, AnalyticAt ℝ (fun q : ℝ × M4 × Cfg => sigmaArr χ q.2.1 i j) (0, E, 0) :=
    fun i j => analyticAt_sigmaArr_comp χ i j hE
  unfold remLocJ
  refine AnalyticAt.add ?_ ?_
  · exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_pairingLeft_comp (hpi i) (hGE i)
  · exact ((analyticAt_pairingLeft_comp (hsig 0 1) (hGB 0 1)).add
      (analyticAt_pairingLeft_comp (hsig 0 2) (hGB 0 2))).add
      (analyticAt_pairingLeft_comp (hsig 1 2) (hGB 1 2))

variable {N : ℕ} [NeZero N]

/-- **The local remainder is the jointly analytic one for small spacing and configuration**
(one `N`-independent radius). -/
theorem exists_remLocal_eq_remLocJ : ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (χ h : ℝ) (e : Site N → M4)
    (x : Site N) (w : Cfg), 0 < h → h < δ → ‖w‖ < δ → remLocal χ h e x w = remLocJ χ (h, e x, w) := by
  obtain ⟨δG, hδG, hG⟩ := exists_radius_G
  obtain ⟨C, hC1, hC⟩ := exists_iota_bound
  have hC0 : 0 ≤ C := by linarith
  refine ⟨δG / C, by positivity, fun N _ χ h e x w hh hhδ hw => ?_⟩
  have hCw : C * ‖w‖ < δG := by
    rw [lt_div_iff₀ (by positivity)] at hw; linarith
  have hδC : δG / C ≤ δG := div_le_self hδG.le hC1
  obtain ⟨hE, hB⟩ := hG h hh (hhδ.trans_le hδC)
  have hpE : ∀ i, GE (h, projE i w) = rhoE h (projE i w) := fun i =>
    hE _ ((norm_projE_le hC0 hC i w).trans_lt hCw)
  have hpB : ∀ i j, GB (h, projB i j w) = rhoB h (projB i j w) := fun i j =>
    hB _ ((norm_projB_le hC0 hC i j w).trans_lt hCw)
  rw [remLocal_eq_sum hh.ne', Fin.sum_univ_six]
  simp [remLocJ, remTerm, Fin.sum_univ_three, hpE, hpB]
  ring

/-- The configuration derivative of the jointly analytic local remainder. -/
def remLocJw (χ : ℝ) (q : ℝ × M4 × Cfg) : Cfg →L[ℝ] ℝ :=
  fderiv ℝ (fun w => remLocJ χ (q.1, q.2.1, w)) q.2.2

/-- The injection of the configuration slot. -/
def inCfg : Cfg →L[ℝ] (ℝ × M4 × Cfg) :=
  (ContinuousLinearMap.inr ℝ ℝ (M4 × Cfg)).comp (ContinuousLinearMap.inr ℝ M4 Cfg)

theorem remLocJw_eq_of_analyticAt {χ : ℝ} {q : ℝ × M4 × Cfg} (hq : AnalyticAt ℝ (remLocJ χ) q) :
    remLocJw χ q = (fderiv ℝ (remLocJ χ) q).comp inCfg := by
  have hin : HasFDerivAt (fun w : Cfg => ((q.1, q.2.1, w) : ℝ × M4 × Cfg)) inCfg q.2.2 := by
    have h0 := (inCfg.hasFDerivAt (x := q.2.2)).const_add ((q.1, q.2.1, 0) : ℝ × M4 × Cfg)
    have e : (fun w : Cfg => ((q.1, q.2.1, w) : ℝ × M4 × Cfg)) =
        fun x => (q.1, q.2.1, 0) + inCfg x := by
      funext w; simp [inCfg]
    rw [e]; exact h0
  have h := hq.differentiableAt.hasFDerivAt.comp q.2.2 hin
  exact h.fderiv

/-- **The configuration derivative is analytic** at every `(0, E, 0)`. -/
theorem analyticAt_remLocJw (χ : ℝ) (E : M4) : AnalyticAt ℝ (remLocJw χ) (0, E, 0) := by
  have han := analyticAt_remLocJ χ E
  have hev : ∀ᶠ q in 𝓝 ((0 : ℝ), E, (0 : Cfg)), remLocJw χ q = (fderiv ℝ (remLocJ χ) q).comp inCfg := by
    filter_upwards [han.eventually_analyticAt] with q hq
    exact remLocJw_eq_of_analyticAt hq
  have h2 : AnalyticAt ℝ (fun q => (fderiv ℝ (remLocJ χ) q).comp inCfg) ((0 : ℝ), E, (0 : Cfg)) :=
    ((ContinuousLinearMap.compL ℝ Cfg (ℝ × M4 × Cfg) ℝ).flip inCfg).analyticAt _ |>.comp han.fderiv
  exact h2.congr (hev.mono fun q hq => hq.symm)

/-- **The local remainder gradient formula**: the coefficient function of `N_h` at a site. -/
def NhLoc (χ : ℝ) (q : ℝ × (Fin 4 → M4) × (Fin 4 → Cfg)) : LocVal :=
  ∑ ℓ : Fin 4, rieszInv ((remLocJw χ (q.1, q.2.1 ℓ, q.2.2 ℓ)).comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => LocVal) ℓ))

/-- `NhLoc` is analytic at every `(0, E, 0)`. -/
theorem analyticAt_NhLoc (χ : ℝ) (E : Fin 4 → M4) : AnalyticAt ℝ (NhLoc χ) (0, E, 0) := by
  unfold NhLoc
  refine Finset.analyticAt_fun_sum _ fun ℓ _ => ?_
  have h1 : AnalyticAt ℝ (fun q : ℝ × (Fin 4 → M4) × (Fin 4 → Cfg) => ((q.1, q.2.1 ℓ, q.2.2 ℓ) :
      ℝ × M4 × Cfg)) (0, E, 0) :=
    analyticAt_fst.prod (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => M4) ℓ).analyticAt
      _).comp (analyticAt_fst.comp analyticAt_snd) |>.prod
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Cfg) ℓ).analyticAt _).comp
        (analyticAt_snd.comp analyticAt_snd)))
  have h2 := (analyticAt_remLocJw χ (E ℓ)).comp_of_eq h1 (by simp)
  have h3 := ((ContinuousLinearMap.compL ℝ LocVal Cfg ℝ).flip
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => LocVal) ℓ)).analyticAt _ |>.comp h2
  exact (rieszInv.analyticAt _).comp h3

/-- **`N_h` as a local operator** (sup norm, `N`-independent radius): for `hN N < δ`, `‖A‖ < δ`,
`N_h(e, A)(x) = NhLoc(h, (e(x - o_ℓ))_ℓ, (A(x - o_ℓ + o_ν))_{ℓ,ν})`. -/
theorem exists_Nh_eq_NhLoc : ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (χ : ℝ) (e : Site N → M4) (A : Conn N),
    hN N < δ → ‖A‖ < δ → ∀ x : Site N,
      Nh χ e A x = NhLoc χ (hN N, fun ℓ => e (x - offs ℓ), fun ℓ => loc offs (x - offs ℓ) A) := by
  obtain ⟨δ₁, hδ₁, heq⟩ := exists_remLocal_eq_remLocJ
  obtain ⟨ε₀, hε₀, κ, hκ, hlip⟩ := exists_remLocal_lipschitz
  refine ⟨min (min δ₁ ε₀) 1, by positivity, fun N _ χ e A hh hA x => ?_⟩
  have hh1 : hN N < δ₁ := hh.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hA1 : ‖A‖ < δ₁ := hA.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hpos := hN_pos (N := N)
  have hhA : hN N * ‖A‖ ≤ ε₀ := by
    have h1 : hN N ≤ 1 := hh.le.trans (min_le_right _ _)
    have h2 : ‖A‖ ≤ ε₀ := hA.le.trans ((min_le_left _ _).trans (min_le_right _ _))
    nlinarith [norm_nonneg A]
  have hd : ∀ y, DifferentiableAt ℝ (remLocal χ (hN N) e y) (loc offs y A) := fun y =>
    (hlip N χ ‖e y‖ (hN N) ‖A‖ e y hpos (norm_nonneg _) hhA le_rfl).1 _ (norm_loc_apply_le offs y A)
  have hfd : ∀ y, fderiv ℝ (remLocal χ (hN N) e y) (loc offs y A) =
      remLocJw χ (hN N, e y, loc offs y A) := by
    intro y
    have hball : Metric.ball (0 : Cfg) δ₁ ∈ 𝓝 (loc offs y A) :=
      Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ((norm_loc_apply_le offs y A).trans_lt hA1))
    have hev : remLocal χ (hN N) e y =ᶠ[𝓝 (loc offs y A)] fun w => remLocJ χ (hN N, e y, w) := by
      filter_upwards [hball] with w hw
      exact heq N χ (hN N) e y w hpos hh1 (mem_ball_zero_iff.mp hw)
    rw [hev.fderiv_eq]
    rfl
  unfold Nh
  simp only [siteGrad, inv_one, one_smul]
  rw [fderiv_localSum_comp_single offs _ A hd x, map_sum]
  unfold NhLoc
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [hfd]

end RenewalGeometry.ExactPhaseAction.InitialCalculus
