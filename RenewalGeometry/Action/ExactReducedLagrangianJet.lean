/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactFlatLinearization
import RenewalGeometry.Action.ExactLegendreSecondOrder
import RenewalGeometry.Action.ExactStationaryConnectionAnalytic

/-!
# The reduced Lagrangian of the actual action and its second-order jet at flat data
  (`eq:supp-exact-stationary-connection`, `eq:supp-exact-legendre`;
  `thm:supp-exact-action-provenance` (iii)–(iv), emergent-spacetime manuscript)

The Legendre file `ExactLegendreHamiltonian.lean` builds `𝓛°_h` and `𝓗_h` from two parameters,
the triad map and the stationary-connection map.  Here both are instantiated:

* the triad is the symmetric square root `sqrtTriad` (`ExactSqrtTriad.lean`, disclosed rendering
  of "the canonical ADM coframe");
* the stationary connection is the selected zero `statConnCo χ 0 R` of the stationary row of the
  phase-compatible action (`ExactStationaryConnectionAnalytic.lean`), `statAst χ R`.

So `redLagr χ 0 sqrtTriad (statAst χ R)` is the reduced Lagrangian of the actual action
(`Λ = 0`).  At the flat datum `zFlat` (`γ = I`, `N = 1`, `β = 0`, `V = 0`):

* `flat_chart`: for `hR` below an `N`-independent threshold the stationary connection is
  analytic near the flat coordinates and vanishes there (the flat Cartan block has least
  singular value `2|χ|/3`, `cartanOp_flat_lower_bound_explicit`, so the chart hypothesis holds).
* **`redLagr_jet_flat`** (the Schur complement / stationary elimination at second order):
  `𝓛°_h` is analytic at flat data, `𝓛°_h = 0`, `D𝓛°_h = 0`, and
  `D²𝓛°_h(v, w) = -h³ Σ_x ⟨F₁ w (x), χ⁻¹ C₀⁻¹ F₁ v (x)⟩_b`, where
  `F₁ = D(f°_h ∘ data)` is the linearized phase-compatible load and `C₀⁻¹ = cartFlatInv`
  (the inverse of the flat Cartan block).  The link remainder `N_h` does not contribute
  (`‖N_h(e, A)‖ ≤ C‖A‖²`), nor does the coframe dependence of `C(e)`.
-/

open Filter Finset Metric
open scoped Topology ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction.QuadJet

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open LogBCH LocalSumGradient

/-! ### Generic calculus helpers -/

section Generic

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Second derivatives as derivatives of evaluated first derivatives. -/
theorem fderiv_fderiv_apply_eq {f : X → ℝ} {x : X} (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (v w : X) : fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  rw [fderiv_clm_apply hf (differentiableAt_const w)]
  simp

/-- The first partial derivative of a function on a product. -/
theorem fderiv_apply_inl {g : X × Y → F} {x : X} {y : Y} (hg : DifferentiableAt ℝ g (x, y))
    (v : X) : fderiv ℝ g (x, y) (v, 0) = fderiv ℝ (fun x' => g (x', y)) x v := by
  have h : HasFDerivAt (fun x' => g (x', y)) (fderiv ℝ g (x, y) ∘L ContinuousLinearMap.inl ℝ X Y)
      x := hg.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
  rw [h.fderiv]
  simp

/-- The second partial derivative of a function on a product. -/
theorem fderiv_apply_inr {g : X × Y → F} {x : X} {y : Y} (hg : DifferentiableAt ℝ g (x, y))
    (v : Y) : fderiv ℝ g (x, y) (0, v) = fderiv ℝ (fun y' => g (x, y')) y v := by
  have h : HasFDerivAt (fun y' => g (x, y')) (fderiv ℝ g (x, y) ∘L ContinuousLinearMap.inr ℝ X Y)
      y := hg.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
  rw [h.fderiv]
  simp

/-- Derivative of `x ↦ T(x)(s(x))` with `T` merely continuous, when `s(x₀) = 0`. -/
theorem hasFDerivAt_apply_of_continuousAt {T : X → E →L[ℝ] F} {s : X → E} {s' : X →L[ℝ] E}
    {x₀ : X} (hT : ContinuousAt T x₀) (hs : HasFDerivAt s s' x₀) (hs0 : s x₀ = 0) :
    HasFDerivAt (fun x => T x (s x)) ((T x₀).comp s') x₀ := by
  rw [hasFDerivAt_iff_isLittleO]
  have hsplit : (fun x => T x (s x) - T x₀ (s x₀) - (T x₀).comp s' (x - x₀)) =
      fun x => (T x - T x₀) (s x) + T x₀ (s x - s x₀ - s' (x - x₀)) := by
    funext x
    simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub, hs0, map_zero, sub_zero]
    abel
  rw [hsplit]
  refine Asymptotics.IsLittleO.add ?_ ?_
  · have hTo : (fun x => ‖T x - T x₀‖) =o[𝓝 x₀] (fun _ => (1 : ℝ)) :=
      (Asymptotics.isLittleO_one_iff ℝ).2 (tendsto_iff_norm_sub_tendsto_zero.1 hT.tendsto)
    have hsO : (fun x => ‖s x‖) =O[𝓝 x₀] (fun x => ‖x - x₀‖) := by
      have h1 := hs.isBigO_sub
      simp only [hs0, sub_zero] at h1
      exact h1.norm_left.norm_right
    have hprod := hTo.mul_isBigO hsO
    simp only [one_mul] at hprod
    refine Asymptotics.isLittleO_norm_right.1 (Asymptotics.IsBigO.trans_isLittleO ?_ hprod)
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (T x - T x₀).le_opNorm _
  · exact ((T x₀).isBigO_comp _ _).trans_isLittleO hs.isLittleO

/-- A map that is quadratically small in a differentiable map vanishing at `x₀` has zero
derivative at `x₀`. -/
theorem hasFDerivAt_zero_of_sq_le {f : X → F} {s : X → E} {s' : X →L[ℝ] E} {x₀ : X} {K : ℝ}
    (hs : HasFDerivAt s s' x₀) (hs0 : s x₀ = 0) (hf : ∀ᶠ x in 𝓝 x₀, ‖f x‖ ≤ K * ‖s x‖ ^ 2) :
    HasFDerivAt f (0 : X →L[ℝ] F) x₀ := by
  have hf0 : f x₀ = 0 := by
    have := hf.self_of_nhds
    rw [hs0, norm_zero] at this
    exact norm_le_zero_iff.1 (by simpa using this)
  rw [hasFDerivAt_iff_isLittleO]
  simp only [hf0, sub_zero, zero_apply]
  have hsO : (fun x => ‖s x‖) =O[𝓝 x₀] (fun x => ‖x - x₀‖) := by
    have h1 := hs.isBigO_sub
    simp only [hs0, sub_zero] at h1
    exact h1.norm_left.norm_right
  have hso : (fun x => ‖s x‖) =o[𝓝 x₀] (fun _ => (1 : ℝ)) := by
    refine (Asymptotics.isLittleO_one_iff ℝ).2 ?_
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hs.continuousAt.tendsto)
    simp only [hs0, sub_zero] at this
    exact this
  have hsq : (fun x => ‖s x‖ ^ 2) =o[𝓝 x₀] (fun x => ‖x - x₀‖) := by
    have := hso.mul_isBigO hsO
    simp only [one_mul] at this
    refine (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)).trans_isLittleO
      this
    simp [sq]
  have hfO : f =O[𝓝 x₀] (fun x => ‖s x‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [hf] with x hx
    rw [Real.norm_eq_abs (‖s x‖ ^ 2), abs_of_nonneg (by positivity)]
    exact hx
  exact Asymptotics.isLittleO_norm_right.1 (hfO.trans_isLittleO hsq)

end Generic

/-! ### Flat data and the instantiated reduced Lagrangian -/

variable {N : ℕ} [NeZero N]

/-- `Sym₃` coordinates of the flat metric `I` (order `(11, 22, 33, 12, 13, 23)`). -/
def flatSym : Fin 6 → ℝ := ![1, 1, 1, 0, 0, 0]

theorem symMat_flatSym : symMat flatSym = one3 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [symMat, flatSym, InitialConstraintLinearRange.sym6, one3_apply]

/-- The flat metric field. -/
def flatMet (N : ℕ) : MetF N := fun _ => flatSym

/-- The flat datum `((γ, N, β), V) = ((I, 1, 0), 0)`: the base point of the Legendre chart. -/
def zFlat (N : ℕ) [NeZero N] : ParF N × MetF N := (refMult (flatMet N), 0)

/-- Matrix fields as plain coordinates. -/
def toCo (p : (Site N → M4) × (Fin 3 → Site N → M4)) : CoP N :=
  (fun x a b => p.1 x a b, fun i x a b => p.2 i x a b)

theorem ofCo_toCo (p : (Site N → M4) × (Fin 3 → Site N → M4)) : ofCo (toCo p) = p := rfl

/-- **The stationary-connection map of the actual action** (`Λ = 0`): the selected zero
`statConnCo` of the stationary row in the closed `R`-ball, as a function of `(e, ∂_tΠ)`. -/
def statAst (χ R : ℝ) : (Site N → M4) × (Fin 3 → Site N → M4) → Conn N :=
  fun p => statConnCo χ 0 R (toCo p)

/-- The coframe / `Π`-velocity data of a configuration `((γ, N, β), V)`. -/
def dataMap (χ : ℝ) (z : ParF N × MetF N) : (Site N → M4) × (Fin 3 → Site N → M4) :=
  (coframeField sqrtTriad z.1, piDot χ sqrtTriad z.1.1 z.2)

theorem coframeField_flat : coframeField sqrtTriad (zFlat N).1 = fun _ => (1 : M4) := by
  funext x
  simp only [coframeField, zFlat, refMult, flatMet, symMat_flatSym, sqrtTriad_one]
  exact admCoframe_flat

theorem dataMap_flat (χ : ℝ) : dataMap χ (zFlat N) = ((fun _ => (1 : M4)), 0) := by
  refine Prod.ext coframeField_flat ?_
  funext i x
  ext K L
  simp [dataMap, piDot, zFlat]

theorem toCo_dataMap_flat (χ : ℝ) : toCo (dataMap χ (zFlat N)) = flatCo N := by
  rw [dataMap_flat]
  rfl

/-- The triad is analytic at the flat metric of every site. -/
theorem analyticAt_sqrtTriad_flat (x : Site N) :
    AnalyticAt ℝ sqrtTriad (symMat ((zFlat N).1.1 x)) := by
  simp only [zFlat, refMult, flatMet, symMat_flatSym]
  exact analyticAt_sqrtTriad

/-- **The data map is analytic at flat data.** -/
theorem analyticAt_dataMap (χ : ℝ) : AnalyticAt ℝ (dataMap χ) (zFlat N) := by
  set z₀ := zFlat N
  have htr := analyticAt_sqrtTriad_flat (N := N)
  have hγ : ∀ x, AnalyticAt ℝ (fun z : ParF N × MetF N => z.1.1 x) z₀ := fun x =>
    analyticAt_pi_apply (analyticAt_fst.comp analyticAt_fst) x
  have hn : ∀ x, AnalyticAt ℝ (fun z : ParF N × MetF N => z.1.2.1 x) z₀ := fun x =>
    analyticAt_pi_apply (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)) x
  have hβ : ∀ x, AnalyticAt ℝ (fun z : ParF N × MetF N => z.1.2.2 x) z₀ := fun x =>
    analyticAt_pi_apply (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)) x
  have hV : ∀ x, AnalyticAt ℝ (fun z : ParF N × MetF N => z.2 x) z₀ := fun x =>
    analyticAt_pi_apply analyticAt_snd x
  have he : ∀ x, AnalyticAt ℝ (fun z : ParF N × MetF N => coframeField sqrtTriad z.1 x) z₀ :=
    fun x => analyticAt_admCoframe_comp
      ((htr x).comp_of_eq (analyticAt_symMat_comp (hγ x)) rfl) (hn x) (hβ x)
  have hPd : ∀ i x, AnalyticAt ℝ (fun z : ParF N × MetF N => piDot χ sqrtTriad z.1.1 z.2 i x)
      z₀ := by
    intro i x
    refine analyticAt_of_entries fun K L => ?_
    have hf : AnalyticAt ℝ (fun z : ParF N × MetF N =>
        fderiv ℝ (piEntry χ sqrtTriad i K L) (z.1.1 x)) z₀ :=
      ((analyticAt_piEntry χ (htr x) i K L).fderiv).comp_of_eq (hγ x) rfl
    exact ((ContinuousLinearMap.id ℝ ((Fin 6 → ℝ) →L[ℝ] ℝ)).analyticAt_bilinear _).comp
      (hf.prod (hV x))
  exact (AnalyticAt.pi he).prod (AnalyticAt.pi fun i => AnalyticAt.pi fun x => hPd i x)

/-- The coordinates of the data are analytic at flat data. -/
theorem analyticAt_toCo_dataMap (χ : ℝ) :
    AnalyticAt ℝ (fun z : ParF N × MetF N => toCo (dataMap χ z)) (zFlat N) := by
  have h := analyticAt_dataMap (N := N) χ
  have h1 : ∀ x, AnalyticAt ℝ (fun z : ParF N × MetF N => (dataMap χ z).1 x) (zFlat N) :=
    fun x => analyticAt_pi_apply (analyticAt_fst.comp h) x
  have h2 : ∀ i x, AnalyticAt ℝ (fun z : ParF N × MetF N => (dataMap χ z).2 i x) (zFlat N) :=
    fun i x => analyticAt_pi_apply (analyticAt_pi_apply (analyticAt_snd.comp h) i) x
  refine AnalyticAt.prod (AnalyticAt.pi fun x => AnalyticAt.pi fun a => AnalyticAt.pi fun b =>
    analyticAt_entry_comp (h1 x) a b) (AnalyticAt.pi fun i => AnalyticAt.pi fun x =>
      AnalyticAt.pi fun a => AnalyticAt.pi fun b => analyticAt_entry_comp (h2 i x) a b)

/-- The phase-compatible Lagrangian as a function of a configuration and a connection
(`Λ = 0`). -/
def PhiL (χ : ℝ) (p : (ParF N × MetF N) × Conn N) : ℝ :=
  phaseLagr χ 0 (dataMap χ p.1).1 (dataMap χ p.1).2 p.2

/-- The configuration-and-connection map `p ↦ (e, ∂_tΠ, A)`. -/
def phiArg (χ : ℝ) (p : (ParF N × MetF N) × Conn N) :
    (Site N → M4) × (Fin 3 → Site N → M4) × Conn N :=
  ((dataMap χ p.1).1, (dataMap χ p.1).2, p.2)

theorem PhiL_eq (χ : ℝ) : PhiL (N := N) χ =
    (fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N => phaseLagr χ 0 q.1 q.2.1 q.2.2) ∘
      phiArg χ := rfl

theorem analyticAt_phiArg (χ : ℝ) : AnalyticAt ℝ (phiArg (N := N) χ) (zFlat N, (0 : Conn N)) := by
  have hd : AnalyticAt ℝ (fun p : (ParF N × MetF N) × Conn N => dataMap χ p.1)
      (zFlat N, (0 : Conn N)) :=
    AnalyticAt.comp_of_eq (g := dataMap χ) (f := fun p : (ParF N × MetF N) × Conn N => p.1)
      (analyticAt_dataMap (N := N) χ) analyticAt_fst rfl
  exact (analyticAt_fst.comp hd).prod ((analyticAt_snd.comp hd).prod analyticAt_snd)

/-- **The phase Lagrangian is analytic at `(flat data, A = 0)`.** -/
theorem analyticAt_PhiL (χ : ℝ) : AnalyticAt ℝ (PhiL χ) (zFlat N, (0 : Conn N)) := by
  have hbr : PlaqBranch (hN N) (toA (phiArg χ (zFlat N, (0 : Conn N))).2.2) := by
    show PlaqBranch (hN N) (toA (0 : Conn N))
    rw [toA_zero]; exact plaqBranch_zero _
  rw [PhiL_eq]
  exact (analyticAt_phaseLagr χ 0 _ hbr).comp (analyticAt_phiArg χ)

/-- The phase Lagrangian vanishes at the zero connection when `Λ = 0`. -/
theorem phaseLagr_zero_conn (χ : ℝ) (e : Site N → M4) (P : Fin 3 → Site N → M4) :
    phaseLagr χ 0 e P 0 = 0 := by
  have h0 : toA0 (0 : Conn N) = 0 := by funext x; simp [toA0, ← iota_zero]
  have hrem : ∀ x, remDensity χ (hN N) e 0 0 x = 0 := by
    intro x
    simp [remDensity, remE, remB, plaquette, plaqList, plaqX, commTerm, bracket, sumLt_eq,
      pairing]
  have hq : ∀ x, qc χ e 0 0 x = 0 := by
    intro x; simp [qc, bracket, sumLt_eq, pairing]
  unfold phaseLagr gridPair nfDensityPh
  rw [h0, toA_zero]
  simp [hrem, hq, pairing_zero_right]

theorem PhiL_zero (χ : ℝ) (z : ParF N × MetF N) : PhiL χ (z, 0) = 0 := phaseLagr_zero_conn χ _ _

/-! ### The flat chart of the stationary connection -/

/-- The chart hypotheses of `analyticOnNhd_statConnCo` around the flat coordinates, with the
selected stationary connection vanishing at flat data. -/
structure FlatChart (χ R : ℝ) (U : Set (CoP N)) : Prop where
  isOpen : IsOpen U
  mem : flatCo N ∈ U
  analytic : AnalyticOnNhd ℝ (statConnCo χ 0 R) U
  spec : ∀ q ∈ U, statConnCo χ 0 R q ∈ closedBall (0 : Conn N) R ∧
    statRow χ 0 (ofCo q).1 (ofCo q).2 (statConnCo χ 0 R q) = 0
  zero : statConnCo χ 0 R (flatCo N) = 0

/-- **The flat chart** (clause (ii) at flat data, chart hypothesis discharged): for `χ ≠ 0` there
is an `N`-independent threshold `ε` such that for `0 < R`, `hR ≤ ε`, the selected stationary
connection is analytic on an open neighbourhood of the flat coordinates, is there the unique
stationary connection in the `R`-ball, and vanishes at flat data.  The least singular value is
the explicit flat one, `2|χ|/3`. -/
theorem flat_chart (χ : ℝ) (hχ : χ ≠ 0) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ), 0 < R → hN N * R ≤ ε →
      ∃ U : Set (CoP N), FlatChart χ R U := by
  set c₀ := 2 * |χ| / 3 with hc₀def
  have hc₀ : 0 < c₀ := by have := abs_pos.2 hχ; positivity
  obtain ⟨ε, hε, h⟩ := analyticOnNhd_statConnCo χ 0 2 (c₀ / 2) (by positivity)
  refine ⟨ε, hε, fun N _ R hR hhR => ?_⟩
  have hf0 : fPh χ (ofCo (flatCo N)).1 (ofCo (flatCo N)).2 = 0 := by
    rw [ofCo_flatCo]; exact fPh_const_zero χ 1
  obtain ⟨U, hUo, hq₀, he, hC, hf⟩ := exists_open_chartCo (N := N) χ 2 c₀ R hc₀ (flatCo N)
    (fun x => by rw [ofCo_flatCo]; simp)
    (fun A => by rw [ofCo_flatCo]; exact cartanOp_flat_lower_bound_explicit χ hχ A)
    (by rw [hf0, norm_zero]; positivity)
  obtain ⟨hspec, han⟩ := h N R U hR.le hhR hUo he hC hf
  have hball : ∀ q ∈ U, statConnCo χ 0 R q ∈ closedBall (0 : Conn N) R := by
    intro q hq
    rw [mem_closedBall_zero_iff]
    have h1 := (hspec q hq).2
    have h2 := (hf q hq).le
    calc ‖statConnCo χ 0 R q‖ ≤ 2 * (c₀ / 2)⁻¹ * ‖fPh χ (ofCo q).1 (ofCo q).2‖ := h1
      _ ≤ 2 * (c₀ / 2)⁻¹ * (c₀ / 2 * R / 4) := by gcongr
      _ = R / 2 := by field_simp; ring
      _ ≤ R := by linarith
  refine ⟨U, hUo, hq₀, han, fun q hq => ⟨hball q hq, ((hspec q hq).1 _ (hball q hq)).2 rfl⟩, ?_⟩
  have := (hspec _ hq₀).2
  rw [hf0, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-! ### The stationary connection along configurations -/

/-- The stationary connection of the configuration `z`. -/
def Sfun (χ R : ℝ) (z : ParF N × MetF N) : Conn N := statAst χ R (dataMap χ z)

/-- The reduced Lagrangian is the phase Lagrangian at the stationary connection. -/
theorem redLagr_eq_PhiL (χ R : ℝ) :
    redLagr χ 0 sqrtTriad (statAst (N := N) χ R) = fun z => PhiL χ (z, Sfun χ R z) := rfl

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U)
include hU

theorem Sfun_flat : Sfun χ R (zFlat N) = 0 := by
  simp only [Sfun, statAst, toCo_dataMap_flat, hU.zero]

theorem eventually_toCo_mem : ∀ᶠ z in 𝓝 (zFlat N), toCo (dataMap χ z) ∈ U := by
  have hc := (analyticAt_toCo_dataMap (N := N) χ).continuousAt
  have hmem : U ∈ 𝓝 (toCo (dataMap χ (zFlat N))) := by
    rw [toCo_dataMap_flat]; exact hU.isOpen.mem_nhds hU.mem
  exact hc.eventually hmem

theorem analyticAt_Sfun : AnalyticAt ℝ (Sfun χ R) (zFlat N) := by
  have h1 := hU.analytic _ hU.mem
  rw [← toCo_dataMap_flat (N := N) χ] at h1
  exact AnalyticAt.comp (f := fun z => toCo (dataMap χ z)) h1 (analyticAt_toCo_dataMap (N := N) χ)

theorem eventually_stationary : ∀ᶠ z in 𝓝 (zFlat N),
    statRow χ 0 (dataMap χ z).1 (dataMap χ z).2 (Sfun χ R z) = 0 ∧
      Sfun χ R z ∈ closedBall (0 : Conn N) R := by
  filter_upwards [eventually_toCo_mem hU] with z hz
  exact ⟨(hU.spec _ hz).2, (hU.spec _ hz).1⟩

end Chart

/-- The `⟨·,·⟩_{b,h}`-pairing with a fixed connection, as a continuous linear functional. -/
def pairA (a : Conn N) : Conn N →L[ℝ] ℝ :=
  hN N ^ 3 • ∑ x, (bdotCLM (a x)).comp (ContinuousLinearMap.proj x)

theorem pairA_apply (a u : Conn N) : pairA a u = hN N ^ 3 * ∑ x, bdot (a x) (u x) := by
  simp [pairA]

theorem bdot_comm (u v : LocVal) : bdot u v = bdot v u := by
  unfold bdot
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The connection partial derivative of the phase Lagrangian is the pairing with the
stationary row. -/
theorem fderiv_phaseLagr_conn (χ : ℝ) (e : Site N → M4) (P : Fin 3 → Site N → M4)
    (A a : Conn N) :
    fderiv ℝ (phaseLagr χ 0 e P) A a = pairA a (statRow χ 0 e P A) := by
  rw [fderiv_eq_sum_siteGrad rieszInv (pow_ne_zero 3 (hN_ne_zero (N := N))) bdotCLM rieszInv_spec _ A a,
    pairA_apply]
  simp only [bdotCLM_apply, statRow]
  congr 1
  exact Finset.sum_congr rfl fun y _ => bdot_comm _ _

/-- At the zero connection the stationary row is the load. -/
theorem statRow_zero_conn (χ : ℝ) (e : Site N → M4) (P : Fin 3 → Site N → M4) :
    statRow χ 0 e P 0 = fPh χ e P := by
  obtain ⟨ε₀, hε₀, hrow⟩ := exists_statRow_eq
  rw [hrow N χ 0 e P 0 (by simp; exact hε₀.le)]
  have hC : cartanOp χ e 0 = 0 := by simpa using cartanOp_smul χ e 0 0
  simp [statRowExplicit, hC, Nh_zero]

/-- The load of the configuration `z`. -/
def loadF (χ : ℝ) (z : ParF N × MetF N) : Conn N := fPh χ (dataMap χ z).1 (dataMap χ z).2

theorem analyticAt_loadF (χ : ℝ) : AnalyticAt ℝ (loadF (N := N) χ) (zFlat N) := by
  have hd := analyticAt_dataMap (N := N) χ
  have he : ∀ y, AnalyticAt ℝ (fun z : ParF N × MetF N => (dataMap χ z).1 y) (zFlat N) :=
    fun y => analyticAt_pi_apply (analyticAt_fst.comp hd) y
  have hP : ∀ i y, AnalyticAt ℝ (fun z : ParF N × MetF N => (dataMap χ z).2 i y) (zFlat N) :=
    fun i y => analyticAt_pi_apply (analyticAt_pi_apply (analyticAt_snd.comp hd) i) y
  refine AnalyticAt.pi fun x => AnalyticAt.pi fun μ => AnalyticAt.pi fun k => ?_
  cases μ using Fin.cases with
  | zero =>
    simp only [loadF, fPh, Fin.cases_zero]
    exact analyticAt_coord_comp (analyticAt_load0Ph_comp χ he x) k
  | succ i =>
    simp only [loadF, fPh, Fin.cases_succ]
    exact analyticAt_coord_comp ((hP i x).neg.add (analyticAt_loadSpPh_comp χ he i x)) k

/-- **The linearized phase-compatible load** `F₁ = D(f°_h ∘ data)` at flat data. -/
def loadDer (χ : ℝ) : (ParF N × MetF N) →L[ℝ] Conn N := fderiv ℝ (loadF χ) (zFlat N)

/-- `D²Φ(flat, 0)((v, 0), (w, 0)) = 0`: the phase Lagrangian vanishes identically at `A = 0`. -/
theorem snd_PhiL_inl_inl (χ : ℝ) (v w : ParF N × MetF N) :
    fderiv ℝ (fderiv ℝ (PhiL χ)) (zFlat N, (0 : Conn N)) (v, 0) (w, 0) = 0 := by
  have han := analyticAt_PhiL (N := N) χ
  rw [fderiv_fderiv_apply_eq han.fderiv.differentiableAt]
  have hg : DifferentiableAt ℝ (fun p => fderiv ℝ (PhiL χ) p (w, (0 : Conn N)))
      (zFlat N, (0 : Conn N)) :=
    han.fderiv.differentiableAt.clm_apply (differentiableAt_const _)
  rw [fderiv_apply_inl hg]
  have hev : (fun z : ParF N × MetF N => fderiv ℝ (PhiL χ) (z, 0) (w, 0)) =ᶠ[𝓝 (zFlat N)]
      fun _ => (0 : ℝ) := by
    have hcont : ContinuousAt (fun z : ParF N × MetF N => ((z, 0) : (ParF N × MetF N) × Conn N))
        (zFlat N) := continuousAt_id.prodMk continuousAt_const
    filter_upwards [hcont.eventually han.eventually_analyticAt] with z hz
    rw [fderiv_apply_inl hz.differentiableAt]
    have : (fun z' => PhiL χ (z', (0 : Conn N))) = fun _ => 0 := funext fun z' => PhiL_zero χ z'
    rw [this]; simp
  rw [hev.fderiv_eq]
  simp

/-- `D²Φ(flat, 0)((w, 0), (0, a)) = ⟨a, F₁ w⟩_{b,h}`: the mixed block is the linearized load. -/
theorem snd_PhiL_inl_inr (χ : ℝ) (w : ParF N × MetF N) (a : Conn N) :
    fderiv ℝ (fderiv ℝ (PhiL χ)) (zFlat N, (0 : Conn N)) (w, 0) (0, a) =
      pairA a (loadDer χ w) := by
  have han := analyticAt_PhiL (N := N) χ
  rw [fderiv_fderiv_apply_eq han.fderiv.differentiableAt]
  have hg : DifferentiableAt ℝ (fun p => fderiv ℝ (PhiL χ) p ((0 : ParF N × MetF N), a))
      (zFlat N, (0 : Conn N)) :=
    han.fderiv.differentiableAt.clm_apply (differentiableAt_const _)
  rw [fderiv_apply_inl hg]
  have hev : (fun z : ParF N × MetF N => fderiv ℝ (PhiL χ) (z, 0) (0, a)) =ᶠ[𝓝 (zFlat N)]
      fun z => pairA a (loadF χ z) := by
    have hcont : ContinuousAt (fun z : ParF N × MetF N => ((z, 0) : (ParF N × MetF N) × Conn N))
        (zFlat N) := continuousAt_id.prodMk continuousAt_const
    filter_upwards [hcont.eventually han.eventually_analyticAt] with z hz
    rw [fderiv_apply_inr hz.differentiableAt]
    change fderiv ℝ (phaseLagr χ 0 (dataMap χ z).1 (dataMap χ z).2) 0 a = _
    rw [fderiv_phaseLagr_conn, statRow_zero_conn]
    rfl
  rw [hev.fderiv_eq]
  have hd : HasFDerivAt (fun z => pairA a (loadF χ z)) ((pairA a).comp (loadDer χ)) (zFlat N) :=
    (pairA a).hasFDerivAt.comp (zFlat N) (analyticAt_loadF χ).differentiableAt.hasFDerivAt
  rw [hd.fderiv]
  rfl

/-! ### Stationary elimination at second order -/

theorem cartFlatInv_smul (c : ℝ) (y : Fin 4 → Fin 6 → ℝ) : cartFlatInv (c • y) = c • cartFlatInv y := by
  funext μ k
  fin_cases μ <;> fin_cases k <;> simp [cartFlatInv] <;> ring

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U)
include hU

/-- The configuration-and-stationary-connection map is analytic, with value `(flat, 0)`. -/
theorem pair_Sfun_flat : (fun z : ParF N × MetF N => (z, Sfun χ R z)) (zFlat N) =
    (zFlat N, (0 : Conn N)) := by
  simp [Sfun_flat hU]

/-- **Envelope identity**: near flat data, `D𝓛°_h(z) w = DΦ(z, 𝒜_h(z))(w, 0)` (the connection
derivative of `Φ` vanishes at the stationary connection). -/
theorem eventually_fderiv_redLagr : ∀ᶠ z in 𝓝 (zFlat N), ∀ w,
    fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R)) z w =
      fderiv ℝ (PhiL χ) (z, Sfun χ R z) (w, 0) := by
  have hS := analyticAt_Sfun hU
  have hpair : ContinuousAt (fun z : ParF N × MetF N => (z, Sfun χ R z)) (zFlat N) :=
    continuousAt_id.prodMk hS.continuousAt
  have hPev := (analyticAt_PhiL (N := N) χ).eventually_analyticAt
  rw [← pair_Sfun_flat hU] at hPev
  filter_upwards [hpair.eventually hPev, hS.eventually_analyticAt, eventually_stationary hU]
    with z hP hSz hst w
  have hd : HasFDerivAt (fun z => PhiL χ (z, Sfun χ R z))
      (fderiv ℝ (PhiL χ) (z, Sfun χ R z) ∘L
        (ContinuousLinearMap.id ℝ (ParF N × MetF N)).prod (fderiv ℝ (Sfun χ R) z)) z :=
    HasFDerivAt.comp (g := PhiL χ) (f := fun z : ParF N × MetF N => (z, Sfun χ R z)) z
      hP.differentiableAt.hasFDerivAt ((hasFDerivAt_id z).prodMk hSz.differentiableAt.hasFDerivAt)
  rw [redLagr_eq_PhiL, hd.fderiv]
  have hsplit : ((w, fderiv ℝ (Sfun χ R) z w) : (ParF N × MetF N) × Conn N) =
      (w, 0) + (0, fderiv ℝ (Sfun χ R) z w) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  rw [hsplit, map_add, fderiv_apply_inr hP.differentiableAt]
  change _ + fderiv ℝ (phaseLagr χ 0 (dataMap χ z).1 (dataMap χ z).2) (Sfun χ R z) _ = _
  rw [fderiv_phaseLagr_conn, hst.1, map_zero, add_zero]

/-- **The linearized stationary connection**: `D𝒜_h(flat) v = -χ⁻¹ C₀⁻¹ F₁ v` (the flat Cartan
block inverts the linearized load; neither the link remainder nor the coframe dependence of
`C(e)` contributes at first order). -/
theorem fderiv_Sfun_flat (hχ : χ ≠ 0) (v : ParF N × MetF N) (x : Site N) :
    fderiv ℝ (Sfun χ R) (zFlat N) v x = -(χ⁻¹ • cartFlatInv (loadDer χ v x)) := by
  obtain ⟨ε₀, hε₀, κ, hκ, hlip⟩ := exists_Nh_lipschitz
  obtain ⟨ε₁, hε₁, hrow⟩ := exists_statRow_eq
  have hS := analyticAt_Sfun hU
  have hS0 := Sfun_flat hU
  have hSd : HasFDerivAt (Sfun χ R) (fderiv ℝ (Sfun χ R) (zFlat N)) (zFlat N) :=
    hS.differentiableAt.hasFDerivAt
  have hh := hN_pos (N := N)
  -- smallness of the stationary connection near flat data
  have hsmall : ∀ᶠ z in 𝓝 (zFlat N), hN N * ‖Sfun χ R z‖ < min ε₀ ε₁ := by
    have hc : ContinuousAt (fun z => hN N * ‖Sfun χ R z‖) (zFlat N) :=
      continuousAt_const.mul (continuous_norm.continuousAt.comp hS.continuousAt)
    have h0 : (fun z => hN N * ‖Sfun χ R z‖) (zFlat N) < min ε₀ ε₁ := by
      simp only [hS0, norm_zero, mul_zero]; exact lt_min hε₀ hε₁
    exact hc.eventually (gt_mem_nhds h0)
  -- the coframe stays bounded near flat data
  have hbound : ∀ᶠ z in 𝓝 (zFlat N), ∀ x, ‖(dataMap χ z).1 x‖ ≤ 2 := by
    rw [Filter.eventually_all]
    intro x
    have hc : ContinuousAt (fun z : ParF N × MetF N => ‖(dataMap χ z).1 x‖) (zFlat N) :=
      continuous_norm.continuousAt.comp
        (analyticAt_pi_apply (analyticAt_fst.comp (analyticAt_dataMap (N := N) χ)) x).continuousAt
    have h0 : (fun z : ParF N × MetF N => ‖(dataMap χ z).1 x‖) (zFlat N) < 2 := by
      simp only [dataMap_flat]; simp
    filter_upwards [hc.eventually (gt_mem_nhds h0)] with z hz
    exact hz.le
  -- the explicit stationary row vanishes near flat data
  have hexp : ∀ᶠ z in 𝓝 (zFlat N), loadF χ z + cartanCLM χ (dataMap χ z).1 (Sfun χ R z) +
      Nh χ (dataMap χ z).1 (Sfun χ R z) = 0 := by
    filter_upwards [eventually_stationary hU, hsmall] with z hst hz
    have h1 := hrow N χ 0 (dataMap χ z).1 (dataMap χ z).2 (Sfun χ R z)
      (hz.le.trans (min_le_right _ _))
    rw [hst.1] at h1
    rw [cartanCLM_apply]
    exact h1.symm
  have hF : HasFDerivAt (loadF χ) (loadDer χ) (zFlat N) :=
    (analyticAt_loadF χ).differentiableAt.hasFDerivAt
  have hT : ContinuousAt (fun z : ParF N × MetF N => cartanCLM χ (dataMap χ z).1) (zFlat N) :=
    ContinuousAt.comp (f := fun z : ParF N × MetF N => toCo (dataMap χ z))
      (g := fun q : CoP N => cartanCLM χ (ofCo q).1)
      (continuous_cartanCLM_co χ).continuousAt (analyticAt_toCo_dataMap χ).continuousAt
  have hC : HasFDerivAt (fun z => cartanCLM χ (dataMap χ z).1 (Sfun χ R z))
      ((cartanCLM χ (dataMap χ (zFlat N)).1).comp (fderiv ℝ (Sfun χ R) (zFlat N))) (zFlat N) :=
    hasFDerivAt_apply_of_continuousAt hT hSd hS0
  have hNd : HasFDerivAt (fun z => Nh χ (dataMap χ z).1 (Sfun χ R z))
      (0 : (ParF N × MetF N) →L[ℝ] Conn N) (zFlat N) := by
    refine hasFDerivAt_zero_of_sq_le (K := κ * (|χ| * 2 ^ 2) * hN N) hSd hS0 ?_
    filter_upwards [hsmall, hbound] with z hz hb
    have h1 := hlip N χ 2 ‖Sfun χ R z‖ (dataMap χ z).1 (norm_nonneg _)
      (hz.le.trans (min_le_left _ _)) hb (Sfun χ R z) 0 le_rfl (by simp)
    rw [Nh_zero, sub_zero, sub_zero] at h1
    calc ‖Nh χ (dataMap χ z).1 (Sfun χ R z)‖
        ≤ κ * (|χ| * 2 ^ 2) * (hN N * ‖Sfun χ R z‖) * ‖Sfun χ R z‖ := h1
      _ = κ * (|χ| * 2 ^ 2) * hN N * ‖Sfun χ R z‖ ^ 2 := by ring
  have hsum := (hF.add hC).add hNd
  have hzero : HasFDerivAt (fun z => loadF χ z + cartanCLM χ (dataMap χ z).1 (Sfun χ R z) +
      Nh χ (dataMap χ z).1 (Sfun χ R z)) (0 : (ParF N × MetF N) →L[ℝ] Conn N) (zFlat N) :=
    (hasFDerivAt_const (0 : Conn N) (zFlat N)).congr_of_eventuallyEq hexp
  have heq := hsum.unique hzero
  have hvx := congrArg (fun T : (ParF N × MetF N) →L[ℝ] Conn N => T v x) heq
  simp only [add_apply, ContinuousLinearMap.comp_apply, cartanCLM_apply,
    zero_apply, add_zero, Pi.add_apply, Pi.zero_apply, dataMap_flat] at hvx
  rw [cartanOp_flat] at hvx
  have hc : χ • cartFlat (fderiv ℝ (Sfun χ R) (zFlat N) v x) = -loadDer χ v x :=
    eq_neg_of_add_eq_zero_right hvx
  have := congrArg (fun y => cartFlatInv (χ⁻¹ • y)) hc
  simp only [smul_smul, inv_mul_cancel₀ hχ, one_smul, cartFlatInv_cartFlat] at this
  rw [this, cartFlatInv_smul, show -loadDer χ v x = (-1 : ℝ) • loadDer χ v x by simp,
    cartFlatInv_smul]
  simp

/-- **Stationary elimination at second order** (`thm:supp-exact-action-provenance` (iv), the
Schur-complement step): at flat data the reduced Lagrangian of the actual action is analytic, it
vanishes together with its first derivative, and its Hessian is
`D²𝓛°_h(v, w) = -h³ Σ_x ⟨χ⁻¹ C₀⁻¹ F₁ v (x), F₁ w (x)⟩_b`. -/
theorem redLagr_jet_flat (hχ : χ ≠ 0) :
    AnalyticAt ℝ (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) ∧
      redLagr χ 0 sqrtTriad (statAst χ R) (zFlat N) = 0 ∧
      fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) = 0 ∧
      ∀ v w, fderiv ℝ (fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R))) (zFlat N) v w =
        -(hN N ^ 3 * ∑ x, bdot (χ⁻¹ • cartFlatInv (loadDer χ v x)) (loadDer χ w x)) := by
  have hS := analyticAt_Sfun hU
  have hPhi := analyticAt_PhiL (N := N) χ
  have hpairA : AnalyticAt ℝ (fun z : ParF N × MetF N => (z, Sfun χ R z)) (zFlat N) :=
    analyticAt_id.prod hS
  have hL : AnalyticAt ℝ (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) := by
    rw [redLagr_eq_PhiL]
    exact AnalyticAt.comp_of_eq (g := PhiL χ) (f := fun z => (z, Sfun χ R z)) hPhi hpairA
      (pair_Sfun_flat hU)
  have hfd := eventually_fderiv_redLagr hU
  -- the first derivative vanishes
  have hD1 : ∀ w, fderiv ℝ (PhiL χ) (zFlat N, (0 : Conn N)) (w, 0) = 0 := by
    intro w
    rw [fderiv_apply_inl hPhi.differentiableAt]
    have : (fun z' => PhiL χ (z', (0 : Conn N))) = fun _ => 0 := funext fun z' => PhiL_zero χ z'
    rw [this]; simp
  refine ⟨hL, ?_, ?_, fun v w => ?_⟩
  · rw [redLagr_eq_PhiL]
    simp only [Sfun_flat hU]
    exact PhiL_zero χ _
  · refine ContinuousLinearMap.ext fun w => ?_
    rw [hfd.self_of_nhds w, Sfun_flat hU, hD1 w]
    rfl
  · rw [fderiv_fderiv_apply_eq hL.fderiv.differentiableAt]
    have hev : (fun z => fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R)) z w) =ᶠ[𝓝 (zFlat N)]
        fun z => fderiv ℝ (PhiL χ) (z, Sfun χ R z) (w, 0) := by
      filter_upwards [hfd] with z hz
      exact hz w
    rw [hev.fderiv_eq]
    -- chain rule for `z ↦ DΦ(z, 𝒜(z))(w, 0)`
    set g : (ParF N × MetF N) × Conn N → ℝ := fun p => fderiv ℝ (PhiL χ) p (w, 0) with hgdef
    have hgd : DifferentiableAt ℝ g (zFlat N, (0 : Conn N)) :=
      hPhi.fderiv.differentiableAt.clm_apply (differentiableAt_const _)
    have hgD : ∀ q, fderiv ℝ g (zFlat N, (0 : Conn N)) q =
        fderiv ℝ (fderiv ℝ (PhiL χ)) (zFlat N, (0 : Conn N)) q (w, 0) := by
      intro q
      rw [hgdef, fderiv_clm_apply hPhi.fderiv.differentiableAt (differentiableAt_const _)]
      simp
    have hg' : HasFDerivAt g (fderiv ℝ g (zFlat N, (0 : Conn N)))
        ((fun z : ParF N × MetF N => (z, Sfun χ R z)) (zFlat N)) := by
      rw [pair_Sfun_flat hU]; exact hgd.hasFDerivAt
    have hcomp := HasFDerivAt.comp (g := g) (f := fun z : ParF N × MetF N => (z, Sfun χ R z))
      (zFlat N) hg' ((hasFDerivAt_id (zFlat N)).prodMk hS.differentiableAt.hasFDerivAt)
    have hfun : (fun z => fderiv ℝ (PhiL χ) (z, Sfun χ R z) (w, 0)) =
        g ∘ fun z : ParF N × MetF N => (z, Sfun χ R z) := rfl
    rw [hfun, hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, hgD]
    have hsplit : ((v, fderiv ℝ (Sfun χ R) (zFlat N) v) : (ParF N × MetF N) × Conn N) =
        (v, 0) + (0, fderiv ℝ (Sfun χ R) (zFlat N) v) := by simp
    rw [hsplit, map_add, add_apply, snd_PhiL_inl_inl, zero_add]
    have hsymm := (hPhi.contDiffAt (n := ω)).isSymmSndFDerivAt_of_omega
    rw [hsymm, snd_PhiL_inl_inr, pairA_apply]
    simp only [fderiv_Sfun_flat hU hχ]
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show -(χ⁻¹ • cartFlatInv (loadDer χ v x)) = (-1 : ℝ) • (χ⁻¹ • cartFlatInv (loadDer χ v x))
      by simp]
    unfold bdot
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Chart

end RenewalGeometry.ExactPhaseAction.QuadJet
