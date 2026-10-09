/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactActionProvenance
import RenewalGeometry.Gravity.SupplementInitialBalancePhase

/-!
# Exact lapse homogeneity of the phase-compatible action and of its canonical Hamiltonian;
  the lapse component of the quadratic mean jet
  (`lem:supp-initial-balance`, first component of `eq:supp-initial-quadratic-mean`;
  emergent-spacetime manuscript)

For the canonical ADM coframe with a spatially constant lapse `s` and zero shift,
`e_s(x) = admCoframe(E(x), s, 0)`, only the temporal column scales: `e⁰₀ = s`, `eᵃ₀ = 0`.

* `sigmaArr_admCoframe_lapse`: `Σ_ij(e_s) = s Σ_ij(e_1)` (the plaquette coefficient arrays are
  linear in the temporal column), while `Π_i(e_s) = Π_i(e_1)` (`piArr_admCoframe`).
* `scaleConn s A`: the connection with temporal component multiplied by `s`;
  `phaseLagr_lapse_scale` (**exact**, every connection, every regulator, `Λ = 0`):
  `L°(e_s, s ∂_tΠ; scale_s A) = s L°(e_1, ∂_tΠ; A)`.
* `statRow_eq_zero_iff_fderiv`, `statRow_lapse_scale_iff`: the stationary rows correspond,
  `γ°(e_s, s∂_tΠ)(scale_s A) = 0 ↔ γ°(e_1, ∂_tΠ)(A) = 0` (`s ≠ 0`, retained branch).
* `exists_uniq_chart`: an `N`-independent threshold and an open chart around flat data on which the
  selected stationary connection is the unique zero in the closed `R`-ball.
* `eventually_redLagr_lapse`: near flat data, `𝓛°_h(γ, V, s, 0) = s 𝓛°_h(γ, s⁻¹V, 1, 0)` for the
  actual reduced Lagrangian (stationary connection `statAst`, symmetric-square-root triad).
* `eventually_canonicalHamiltonian_lapse`: near flat data, `𝓗_h(γ, π, s, 0) = s 𝓗_h(γ, π, 1, 0)`
  (local uniqueness of the analytic Legendre inverse).
* `meanLapse_eq`, `eventually_meanLapse`: the spatial mean `P₀ = h³Σ_x` of the lapse row of the
  original initial constraint map `Cmap` is `-D𝓗_h(q)[δN ≡ 1]`, hence equals `-𝓗_h(I + u, p, 1, 0)`
  near `X = 0`; `meanLapse_second_jet`: `D²(P₀ 𝒞_h^{lapse})(0)[X, X] = -2H₂(X)` (`χ = 1`).
* Seed: `uSeed`, `pSeedF` (`eq:supp-initial-seed` in `Sym₃` coordinates on `(ℤ/N)³`) and `H2_seed`:
  `H₂(u_*, p(ϑ)) = -(⅔κ² - ½Σb_i² - ⅜ω_h²)`.
* **`lapse_mean_jet_seed`**: the lapse component of the quadratic mean jet of the actual action on
  the seed is exactly the first component of `Q_h(ϑ)` (odd `N ≥ 3`, `N`-independent threshold on
  `hR`).

The shift components (`-½ω_h b_i`) and the assembled `Q_h` are in
`ExactInitialBalanceMeanJet.lean`.
-/

open Filter Finset Metric
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction.LapseHomogeneity

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open PalatiniEinsteinAlgebra OddPhaseDerivativeReal

variable {N : ℕ} [NeZero N]

/-! ### The coefficient arrays at a scaled lapse -/

set_option maxRecDepth 100000 in
theorem eps4_succ_succ_succ_succ : ∀ a b c d : Fin 3, eps4 a.succ b.succ c.succ d.succ = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem eps4_zero_zero : ∀ c d : Fin 4, eps4 0 0 c d = 0 := by decide

/-- The temporal column of the canonical coframe at lapse `s`, zero shift. -/
theorem admCoframe_col_zero_lapse (E : Fin 3 → Fin 3 → ℝ) (s : ℝ) (I : Fin 4) :
    admCoframe E s 0 I 0 = s * admCoframe E 1 0 I 0 := by
  cases I using Fin.cases with
  | zero => simp
  | succ a => simp

theorem half_mul_eq {a b s : ℝ} (h : a = s * b) : 1 / 2 * a = s * (1 / 2 * b) := by
  rw [h]; ring

/-- **`Σ_ij` is linear in the lapse** (zero shift). -/
theorem palCoeff_admCoframe_lapse (E : Fin 3 → Fin 3 → ℝ) (s : ℝ) (i j : Fin 3) :
    palCoeff (admCoframe E s 0) i.succ j.succ = s • palCoeff (admCoframe E 1 0) i.succ j.succ := by
  ext K L
  simp only [palCoeff, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
  cases μ using Fin.cases with
  | zero =>
    cases ν using Fin.cases with
    | zero => simp [epsR, eps4_zero_zero]
    | succ ν =>
      rw [admCoframe_col_zero_lapse E s I, admCoframe_col_succ, admCoframe_col_succ]
      ring
  | succ μ =>
    cases ν using Fin.cases with
    | zero =>
      rw [admCoframe_col_zero_lapse E s J, admCoframe_col_succ, admCoframe_col_succ]
      ring
    | succ ν => simp [epsR, eps4_succ_succ_succ_succ]

theorem sigmaArr_admCoframe_lapse (χ : ℝ) (E : Fin 3 → Fin 3 → ℝ) (s : ℝ) (i j : Fin 3) :
    sigmaArr χ (admCoframe E s 0) i j = s • sigmaArr χ (admCoframe E 1 0) i j := by
  rw [sigmaArr, sigmaArr, palCoeff_admCoframe_lapse, smul_comm]
  congr 1
  simp [dualCoeff, Matrix.transpose_smul]

/-! ### Scaling of the phase-compatible Lagrangian -/

/-- The coframe field at constant lapse `s` and zero shift, `e_s(x) = admCoframe(E(x), s, 0)`. -/
def eLapse (E : Site N → Fin 3 → Fin 3 → ℝ) (s : ℝ) : Site N → M4 :=
  fun x => admCoframe (E x) s 0

/-- The connection with its temporal component multiplied by `s`. -/
def scaleConn (s : ℝ) (A : Conn N) : Conn N := fun x μ => if μ = 0 then s • A x μ else A x μ

theorem iota_smul (s : ℝ) (c : Fin 6 → ℝ) : iota (s • c) = s • iota c := by
  simp [iota, Finset.smul_sum, smul_smul]

theorem toA0_scaleConn (s : ℝ) (A : Conn N) : toA0 (scaleConn s A) = s • toA0 A := by
  funext x
  simp [toA0, scaleConn, iota_smul]

theorem toA_scaleConn (s : ℝ) (A : Conn N) : toA (scaleConn s A) = toA A := by
  funext i x
  simp [toA, scaleConn, Fin.succ_ne_zero]

theorem bracket_smul_left (s : ℝ) (a b : M4) : bracket (s • a) b = s • bracket a b := by
  simp [bracket, smul_sub]

theorem bracket_smul_right (s : ℝ) (a b : M4) : bracket a (s • b) = s • bracket a b := by
  simp [bracket, smul_sub]

theorem remE_smul (h s : ℝ) (a b : M4) : remE h a (s • b) = s • remE h a b := by
  simp only [remE, bracket_smul_right, smul_mul_assoc, mul_smul_comm, smul_sub, smul_comm h s,
    smul_comm h⁻¹ s]

theorem piArr_eLapse (χ : ℝ) (E : Site N → Fin 3 → Fin 3 → ℝ) (s : ℝ) (x : Site N) (i : Fin 3) :
    piArr χ (eLapse E s x) i = piArr χ (eLapse E 1 x) i :=
  piArr_admCoframe χ (E x) s 0 i

theorem sigmaArr_eLapse (χ : ℝ) (E : Site N → Fin 3 → Fin 3 → ℝ) (s : ℝ) (x : Site N)
    (i j : Fin 3) : sigmaArr χ (eLapse E s x) i j = s • sigmaArr χ (eLapse E 1 x) i j :=
  sigmaArr_admCoframe_lapse χ (E x) s i j

theorem load0Ph_eLapse (χ : ℝ) (E : Site N → Fin 3 → Fin 3 → ℝ) (s : ℝ) :
    load0Ph χ (eLapse E s) = load0Ph χ (eLapse E 1) := by
  funext x
  simp only [load0Ph, piArr_eLapse]

theorem loadSpPh_eLapse (χ : ℝ) (E : Site N → Fin 3 → Fin 3 → ℝ) (s : ℝ) (i : Fin 3)
    (x : Site N) : loadSpPh χ (eLapse E s) i x = s • loadSpPh χ (eLapse E 1) i x := by
  simp only [loadSpPh, sigmaArr_eLapse χ E s, smul_neg, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (fun y => s • sigmaArr χ (eLapse E 1 y) j i) = s • fun y => sigmaArr χ (eLapse E 1 y) j i :=
    rfl
  rw [e, map_smul]
  rfl

theorem sumLt_mul (s : ℝ) (f : Fin 3 → Fin 3 → ℝ) : sumLt (fun i j => s * f i j) = s * sumLt f := by
  simp only [sumLt_eq]; ring

/-- Pointwise lapse scaling of the phase-compatible normal-form density (`Λ = 0`). -/
theorem nfDensityPh_lapse_scale (χ h : ℝ) (E : Site N → Fin 3 → Fin 3 → ℝ) (s : ℝ)
    (P : Fin 3 → Site N → M4) (A : Conn N) (x : Site N) :
    nfDensityPh χ 0 h (eLapse E s) (s • P) (toA0 (scaleConn s A)) (toA (scaleConn s A)) x =
      s * nfDensityPh χ 0 h (eLapse E 1) P (toA0 A) (toA A) x := by
  rw [toA0_scaleConn, toA_scaleConn]
  have hq : qc χ (eLapse E s) (s • toA0 A) (toA A) x = s * qc χ (eLapse E 1) (toA0 A) (toA A) x := by
    simp only [qc, Pi.smul_apply, bracket_smul_left, pairing_smul_right, piArr_eLapse χ E s,
      sigmaArr_eLapse χ E s, pairing_smul_left]
    rw [← Finset.mul_sum, sumLt_mul]
    ring
  have hr : remDensity χ h (eLapse E s) (s • toA0 A) (toA A) x =
      s * remDensity χ h (eLapse E 1) (toA0 A) (toA A) x := by
    simp only [remDensity, Pi.smul_apply, remE_smul, pairing_smul_right, piArr_eLapse χ E s,
      sigmaArr_eLapse χ E s, pairing_smul_left]
    rw [← Finset.mul_sum, sumLt_mul]
    ring
  simp only [nfDensityPh, hq, hr, load0Ph_eLapse χ E s, loadSpPh_eLapse χ E s, Pi.smul_apply,
    pairing_smul_right]
  have hl : ∀ i, pairing (-(s • P i x) + s • loadSpPh χ (eLapse E 1) i x) (toA A i x) =
      s * pairing (-P i x + loadSpPh χ (eLapse E 1) i x) (toA A i x) := by
    intro i
    rw [← smul_neg, ← smul_add, pairing_smul_left]
  simp only [hl, ← Finset.mul_sum]
  ring

/-- **Exact lapse homogeneity of the phase-compatible Lagrangian** (`Λ = 0`):
`L°(e_s, s ∂_tΠ; scale_s A) = s L°(e_1, ∂_tΠ; A)` for every connection `A`. -/
theorem phaseLagr_lapse_scale (χ : ℝ) (E : Site N → Fin 3 → Fin 3 → ℝ) (s : ℝ)
    (P : Fin 3 → Site N → M4) (A : Conn N) :
    phaseLagr χ 0 (eLapse E s) (s • P) (scaleConn s A) = s * phaseLagr χ 0 (eLapse E 1) P A := by
  simp only [phaseLagr, gridPair, nfDensityPh_lapse_scale, ← Finset.mul_sum]
  ring

/-! ### The stationary rows correspond -/

open QuadJet

/-- The stationary row vanishes iff the connection derivative of the Lagrangian vanishes. -/
theorem statRow_eq_zero_iff_fderiv (χ : ℝ) (e : Site N → M4) (P : Fin 3 → Site N → M4)
    (A : Conn N) : statRow χ 0 e P A = 0 ↔ fderiv ℝ (phaseLagr χ 0 e P) A = 0 := by
  constructor
  · intro h
    ext a
    rw [fderiv_phaseLagr_conn, h, pairA_apply]
    simp [bdot]
  · intro h
    funext y
    simp [statRow, LocalSumGradient.siteGrad, h]

/-- `scaleConn` as a linear map. -/
def scaleLin (s : ℝ) : Conn N →ₗ[ℝ] Conn N where
  toFun := scaleConn s
  map_add' A B := by
    funext x μ
    simp only [scaleConn, Pi.add_apply]
    split_ifs <;> simp [smul_add]
  map_smul' c A := by
    funext x μ
    simp only [scaleConn, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [smul_comm c s]

/-- `scaleConn` as a continuous linear map. -/
def scaleCLM (s : ℝ) : Conn N →L[ℝ] Conn N := LinearMap.toContinuousLinearMap (scaleLin s)

@[simp] theorem scaleCLM_apply (s : ℝ) (A : Conn N) : scaleCLM s A = scaleConn s A := rfl

theorem scaleConn_scaleConn {s t : ℝ} (A : Conn N) :
    scaleConn s (scaleConn t A) = scaleConn (s * t) A := by
  funext x μ
  simp only [scaleConn]
  split_ifs <;> simp [smul_smul]

theorem scaleConn_one (A : Conn N) : scaleConn 1 A = A := by
  funext x μ; simp [scaleConn]

theorem scaleConn_inv_cancel {s : ℝ} (hs : s ≠ 0) (A : Conn N) :
    scaleConn s (scaleConn s⁻¹ A) = A := by
  rw [scaleConn_scaleConn, mul_inv_cancel₀ hs, scaleConn_one]

theorem norm_scaleConn_le (s : ℝ) (A : Conn N) : ‖scaleConn s A‖ ≤ max |s| 1 * ‖A‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun x => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_
  have hA : ‖A x μ‖ ≤ ‖A‖ := (norm_le_pi_norm (A x) μ).trans (norm_le_pi_norm A x)
  simp only [scaleConn]
  split_ifs
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (le_max_left _ _) hA (norm_nonneg _) (by positivity)
  · calc ‖A x μ‖ ≤ ‖A‖ := hA
      _ = 1 * ‖A‖ := (one_mul _).symm
      _ ≤ max |s| 1 * ‖A‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- The phase Lagrangian is differentiable in the connection on the retained plaquette branch. -/
theorem differentiableAt_phaseLagr_conn (χ : ℝ) (e : Site N → M4) (P : Fin 3 → Site N → M4)
    {A : Conn N} (hbr : PlaqBranch (hN N) (toA A)) :
    DifferentiableAt ℝ (phaseLagr χ 0 e P) A := by
  have h := analyticAt_phaseLagr χ 0 (e, P, A) hbr
  have hc : AnalyticAt ℝ (fun B : Conn N => ((e, P, B) :
      (Site N → M4) × (Fin 3 → Site N → M4) × Conn N)) A :=
    analyticAt_const.prod (analyticAt_const.prod analyticAt_id)
  exact (AnalyticAt.comp (f := fun B : Conn N => ((e, P, B) :
      (Site N → M4) × (Fin 3 → Site N → M4) × Conn N)) h hc).differentiableAt

/-- **The stationary rows correspond under lapse scaling**: for `s ≠ 0` and `A` on the retained
branch, `scale_s A` is stationary for `(e_s, s ∂_tΠ)` iff `A` is stationary for `(e_1, ∂_tΠ)`. -/
theorem statRow_lapse_scale_iff (χ : ℝ) (E : Site N → Fin 3 → Fin 3 → ℝ) {s : ℝ} (hs : s ≠ 0)
    (P : Fin 3 → Site N → M4) {A : Conn N} (hbr : PlaqBranch (hN N) (toA A)) :
    statRow χ 0 (eLapse E s) (s • P) (scaleConn s A) = 0 ↔ statRow χ 0 (eLapse E 1) P A = 0 := by
  rw [statRow_eq_zero_iff_fderiv, statRow_eq_zero_iff_fderiv]
  set f := phaseLagr χ 0 (eLapse E 1) P
  set g := phaseLagr χ 0 (eLapse E s) (s • P)
  have hg : g = fun B => s * f (scaleConn s⁻¹ B) := by
    funext B
    have := phaseLagr_lapse_scale χ E s P (scaleConn s⁻¹ B)
    rwa [scaleConn_inv_cancel hs] at this
  have hf : HasFDerivAt f (fderiv ℝ f A) (scaleConn s⁻¹ (scaleConn s A)) := by
    rw [scaleConn_scaleConn, inv_mul_cancel₀ hs, scaleConn_one]
    exact (differentiableAt_phaseLagr_conn χ _ P hbr).hasFDerivAt
  have hgd : HasFDerivAt g (s • (fderiv ℝ f A ∘L scaleCLM s⁻¹)) (scaleConn s A) := by
    rw [hg]
    have h1 := hf.comp (scaleConn s A) (scaleCLM (N := N) s⁻¹).hasFDerivAt
    exact h1.const_smul s
  rw [hgd.fderiv]
  constructor
  · intro h
    have h1 : fderiv ℝ f A ∘L scaleCLM s⁻¹ = 0 := by
      have := congrArg (fun L => s⁻¹ • L) h
      simpa [smul_smul, inv_mul_cancel₀ hs] using this
    ext B
    have := congrArg (fun L => L (scaleConn s B)) h1
    simpa [scaleConn_scaleConn, inv_mul_cancel₀ hs, scaleConn_one] using this
  · intro h
    rw [h]; simp

/-! ### A uniqueness chart around flat data -/

/-- **Uniqueness chart.**  For `χ ≠ 0` there is an `N`-independent threshold `ε` such that for
`0 < R`, `hR ≤ ε`, the selected stationary connection is, on an open neighbourhood `U` of the
flat coordinates, analytic, zero at flat data, and the **unique** zero of the stationary row in
the closed `R`-ball. -/
theorem exists_uniq_chart (χ : ℝ) (hχ : χ ≠ 0) :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N] (R : ℝ), 0 < R → hN N * R ≤ ε →
      ∃ U : Set (CoP N), IsOpen U ∧ flatCo N ∈ U ∧ AnalyticOnNhd ℝ (statConnCo χ 0 R) U ∧
        statConnCo χ 0 R (flatCo N) = 0 ∧
        ∀ q ∈ U, ∀ A : Conn N, A ∈ closedBall (0 : Conn N) R →
          (statRow χ 0 (ofCo q).1 (ofCo q).2 A = 0 ↔ A = statConnCo χ 0 R q) := by
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
  refine ⟨U, hUo, hq₀, han, ?_, fun q hq A hA => (hspec q hq).1 A hA⟩
  have := (hspec _ hq₀).2
  rw [hf0, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-! ### Lapse scaling of the reduced Lagrangian -/

/-- The configuration `((γ, s, 0), V)` (constant lapse `s`, zero shift). -/
def zLapse (γ : MetF N) (s : ℝ) (V : MetF N) : ParF N × MetF N := ((γ, fun _ => s, 0), V)

theorem piDot_smul (χ : ℝ) (triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ) (γ V : MetF N)
    (c : ℝ) : piDot χ triad γ (c • V) = c • piDot χ triad γ V := by
  funext i x
  ext K L
  simp [piDot, map_smul]

theorem dataMap_zLapse (χ : ℝ) (γ : MetF N) (s : ℝ) (V : MetF N) :
    dataMap χ (zLapse γ s V) =
      (eLapse (fun x => sqrtTriad (symMat (γ x))) s, piDot χ sqrtTriad γ V) := rfl

theorem continuous_zLapse :
    Continuous fun w : (MetF N × MetF N) × ℝ => zLapse w.1.1 w.2 w.1.2 := by
  unfold zLapse
  fun_prop

theorem zLapse_flat : zLapse (flatMet N) 1 0 = zFlat N := by
  simp [zLapse, zFlat, refMult]
  rfl

/-- **Exact lapse homogeneity of the reduced Lagrangian near flat data**:
`𝓛°_h(γ, V, s, 0) = s 𝓛°_h(γ, s⁻¹ V, 1, 0)`. -/
theorem eventually_redLagr_lapse {χ R : ℝ} {U : Set (CoP N)} (hUo : IsOpen U)
    (hq₀ : flatCo N ∈ U) (han : AnalyticOnNhd ℝ (statConnCo χ 0 R) U)
    (hz : statConnCo χ 0 R (flatCo N) = 0)
    (huniq : ∀ q ∈ U, ∀ A : Conn N, A ∈ closedBall (0 : Conn N) R →
      (statRow χ 0 (ofCo q).1 (ofCo q).2 A = 0 ↔ A = statConnCo χ 0 R q)) (hR : 0 < R) :
    ∀ᶠ w in 𝓝 (((flatMet N, (0 : MetF N)), (1 : ℝ)) : (MetF N × MetF N) × ℝ),
      redLagr χ 0 sqrtTriad (statAst χ R) (zLapse w.1.1 w.2 w.1.2) =
        w.2 * redLagr χ 0 sqrtTriad (statAst χ R) (zLapse w.1.1 1 (w.2⁻¹ • w.1.2)) := by
  set w₀ : (MetF N × MetF N) × ℝ := ((flatMet N, (0 : MetF N)), (1 : ℝ)) with hw₀
  have hcd := (analyticAt_toCo_dataMap (N := N) χ).continuousAt
  have hz1 : Tendsto (fun w : (MetF N × MetF N) × ℝ => zLapse w.1.1 w.2 w.1.2) (𝓝 w₀)
      (𝓝 (zFlat N)) := by
    have := (continuous_zLapse (N := N)).tendsto w₀
    rwa [hw₀, zLapse_flat] at this
  have hz2 : Tendsto (fun w : (MetF N × MetF N) × ℝ => zLapse w.1.1 1 (w.2⁻¹ • w.1.2)) (𝓝 w₀)
      (𝓝 (zFlat N)) := by
    have h1 : ContinuousAt (fun w : (MetF N × MetF N) × ℝ =>
        (((w.1.1, w.2⁻¹ • w.1.2), (1 : ℝ)) : (MetF N × MetF N) × ℝ)) w₀ := by
      refine ContinuousAt.prodMk (ContinuousAt.prodMk (by fun_prop) ?_) continuousAt_const
      exact ContinuousAt.smul (continuousAt_snd.inv₀ (by simp [hw₀])) (by fun_prop)
    have hc := ((continuous_zLapse (N := N)).continuousAt).comp h1
    have := hc.tendsto
    simp only [Function.comp_def] at this
    have e : zLapse w₀.1.1 1 (w₀.2⁻¹ • w₀.1.2) = zFlat N := by
      rw [hw₀]; simpa using (zLapse_flat (N := N))
    rwa [e] at this
  have hU : U ∈ 𝓝 (toCo (dataMap χ (zFlat N))) := by
    rw [toCo_dataMap_flat]; exact hUo.mem_nhds hq₀
  have hmem1 := (hcd.tendsto.comp hz1).eventually hU
  have hmem2 := (hcd.tendsto.comp hz2).eventually hU
  have hA2 : Tendsto (fun w : (MetF N × MetF N) × ℝ =>
      statConnCo χ 0 R (toCo (dataMap χ (zLapse w.1.1 1 (w.2⁻¹ • w.1.2))))) (𝓝 w₀) (𝓝 0) := by
    have hc := (han _ hq₀).continuousAt
    rw [← hz]
    have := hcd.tendsto.comp hz2
    rw [toCo_dataMap_flat] at this
    exact hc.tendsto.comp this
  obtain ⟨Cι, hCι1, hCι⟩ := exists_iota_bound
  set r : ℝ := min (R / 2) (1 / (16 * (hN N * Cι))) with hr
  have hr0 : 0 < r := lt_min (by positivity) (by have := hN_pos (N := N); positivity)
  have hsmall := hA2.eventually (Metric.ball_mem_nhds (0 : Conn N) hr0)
  have hs : ∀ᶠ w in 𝓝 w₀, (1 / 2 : ℝ) < w.2 ∧ w.2 < 2 := by
    have h1 : Tendsto (fun w : (MetF N × MetF N) × ℝ => w.2) (𝓝 w₀) (𝓝 1) := continuousAt_snd
    exact (h1.eventually (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2))).mono fun w hw => ⟨hw.1, hw.2⟩
  filter_upwards [hmem1, hmem2, hsmall, hs] with w h1 h2 h3 h4
  obtain ⟨⟨γ, V⟩, s⟩ := w
  simp only [Function.comp_apply] at h1 h2 h3 h4 ⊢
  have hs0 : s ≠ 0 := by linarith [h4.1]
  set E : Site N → Fin 3 → Fin 3 → ℝ := fun x => sqrtTriad (symMat (γ x)) with hE
  set P' := piDot χ sqrtTriad γ (s⁻¹ • V) with hP'
  set A₁ := statConnCo χ 0 R (toCo (dataMap χ (zLapse γ 1 (s⁻¹ • V)))) with hA₁def
  have hA₁ : ‖A₁‖ < r := by simpa using h3
  have hA₁R : ‖A₁‖ ≤ R / 2 := hA₁.le.trans (min_le_left _ _)
  have hbr : PlaqBranch (hN N) (toA A₁) := by
    refine plaqBranch_toA_of_norm_le (by linarith) hCι A₁ ?_
    have h5 : ‖A₁‖ ≤ 1 / (16 * (hN N * Cι)) := hA₁.le.trans (min_le_right _ _)
    have hpos : 0 < hN N * Cι := mul_pos hN_pos (by linarith)
    rw [le_div_iff₀ (by positivity)] at h5
    nlinarith
  have hP : piDot χ sqrtTriad γ V = s • P' := by
    rw [hP', piDot_smul, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  have hscale : statConnCo χ 0 R (toCo (dataMap χ (zLapse γ s V))) = scaleConn s A₁ := by
    symm
    refine (huniq _ h1 (scaleConn s A₁) ?_).1 ?_
    · rw [mem_closedBall_zero_iff]
      refine (norm_scaleConn_le s A₁).trans ?_
      have hm : max |s| 1 ≤ 2 :=
        max_le (by rw [abs_of_pos (by linarith [h4.1])]; linarith [h4.2]) (by norm_num)
      nlinarith [norm_nonneg A₁]
    · have hq2 : statRow χ 0 (ofCo (toCo (dataMap χ (zLapse γ 1 (s⁻¹ • V))))).1
          (ofCo (toCo (dataMap χ (zLapse γ 1 (s⁻¹ • V))))).2 A₁ = 0 := by
        refine (huniq _ h2 A₁ ?_).2 rfl
        rw [mem_closedBall_zero_iff]; linarith [norm_nonneg A₁]
      rw [ofCo_toCo, dataMap_zLapse] at hq2 ⊢
      rw [hP]
      exact (statRow_lapse_scale_iff χ E hs0 P' hbr).2 hq2
  show phaseLagr χ 0 (dataMap χ (zLapse γ s V)).1 (dataMap χ (zLapse γ s V)).2
      (statAst χ R (dataMap χ (zLapse γ s V))) =
    s * phaseLagr χ 0 (dataMap χ (zLapse γ 1 (s⁻¹ • V))).1
      (dataMap χ (zLapse γ 1 (s⁻¹ • V))).2 (statAst χ R (dataMap χ (zLapse γ 1 (s⁻¹ • V))))
  have e1 : statAst χ R (dataMap χ (zLapse γ s V)) =
      statConnCo χ 0 R (toCo (dataMap χ (zLapse γ s V))) := rfl
  have e2 : statAst χ R (dataMap χ (zLapse γ 1 (s⁻¹ • V))) = A₁ := rfl
  rw [e1, e2, hscale, dataMap_zLapse, dataMap_zLapse, hP]
  exact phaseLagr_lapse_scale χ E s P' A₁

/-! ### Lapse homogeneity of the canonical Hamiltonian -/

/-- The parameters `(γ, s, 0)` (constant lapse `s`, zero shift). -/
def pLapse (γ : MetF N) (s : ℝ) : ParF N := (γ, fun _ => s, 0)

theorem pLapse_one (γ : MetF N) : pLapse γ 1 = refMult γ := rfl

theorem zLapse_eq (γ : MetF N) (s : ℝ) (V : MetF N) : zLapse γ s V = (pLapse γ s, V) := rfl

/-- **Exact lapse homogeneity of the canonical Hamiltonian near flat data**:
`𝓗_h(γ, π, s, 0) = s 𝓗_h(γ, π, 1, 0)`. -/
theorem eventually_canonicalHamiltonian_lapse {χ R : ℝ} (hχ : χ ≠ 0) {U V : Set (CoP N)}
    (hU : FlatChart χ R U) (hVo : IsOpen V)
    (hq₀ : flatCo N ∈ V) (han : AnalyticOnNhd ℝ (statConnCo χ 0 R) V)
    (hz : statConnCo χ 0 R (flatCo N) = 0)
    (huniq : ∀ q ∈ V, ∀ A : Conn N, A ∈ closedBall (0 : Conn N) R →
      (statRow χ 0 (ofCo q).1 (ofCo q).2 A = 0 ↔ A = statConnCo χ 0 R q)) (hR : 0 < R) :
    ∀ᶠ w in 𝓝 (((flatMet N, (0 : MetF N)), (1 : ℝ)) : (MetF N × MetF N) × ℝ),
      canonicalHamiltonian χ 0 sqrtTriad (statAst χ R) (zFlat N) (pLapse w.1.1 w.2) w.1.2 =
        w.2 * canonicalHamiltonian χ 0 sqrtTriad (statAst χ R) (zFlat N) (pLapse w.1.1 1) w.1.2 := by
  set L := redLagr χ 0 sqrtTriad (statAst (N := N) χ R) with hLdef
  set w₀ : (MetF N × MetF N) × ℝ := ((flatMet N, (0 : MetF N)), (1 : ℝ)) with hw₀
  have hc : LegendreChart L (zFlat N) := legendreChart_flat hU hχ
  have hπ₀ : pairCov (0 : MetF N) = velMom L (zFlat N) := by
    rw [velMom_flat hU hχ, map_zero]
  obtain ⟨hV0, hVan, hsol, huniqL, -⟩ := canonical_legendre χ 0 hc hπ₀
  have hLan : AnalyticAt ℝ L (zFlat N) := hc.1
  have hz0 : (zFlat N).1 = pLapse (flatMet N) 1 := rfl
  have hzV : (zFlat N).2 = 0 := rfl
  -- convergence of the parameter points
  have hp : ∀ᶠ w in 𝓝 w₀, True := Filter.Eventually.of_forall fun _ => trivial
  have hcont_q1 : Tendsto (fun w : (MetF N × MetF N) × ℝ => ((pLapse w.1.1 1, w.1.2) :
      ParF N × MetF N)) (𝓝 w₀) (𝓝 ((zFlat N).1, (0 : MetF N))) := by
    have hc1 : Continuous (fun w : (MetF N × MetF N) × ℝ => ((pLapse w.1.1 1, w.1.2) :
        ParF N × MetF N)) := by unfold pLapse; fun_prop
    have := hc1.tendsto w₀
    simpa [hw₀, hz0] using this
  have hcont_qs : Tendsto (fun w : (MetF N × MetF N) × ℝ => ((pLapse w.1.1 w.2, w.1.2) :
      ParF N × MetF N)) (𝓝 w₀) (𝓝 ((zFlat N).1, (0 : MetF N))) := by
    have hc1 : Continuous (fun w : (MetF N × MetF N) × ℝ => ((pLapse w.1.1 w.2, w.1.2) :
        ParF N × MetF N)) := by unfold pLapse; fun_prop
    have := hc1.tendsto w₀
    simpa [hw₀, hz0] using this
  -- the unit-lapse Legendre velocity
  set V₁ : (MetF N × MetF N) × ℝ → MetF N := fun w =>
    legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) (pLapse w.1.1 1) w.1.2 with hV₁
  have hV₁t : Tendsto V₁ (𝓝 w₀) (𝓝 0) := by
    have := hVan.continuousAt.tendsto.comp hcont_q1
    rw [hV0, hzV] at this
    exact this
  -- the scaled candidate
  have hs1 : Tendsto (fun w : (MetF N × MetF N) × ℝ => w.2) (𝓝 w₀) (𝓝 1) := continuousAt_snd
  have hsV : Tendsto (fun w => w.2 • V₁ w) (𝓝 w₀) (𝓝 (0 : MetF N)) := by
    have := hs1.smul hV₁t
    simpa using this
  -- the lapse identity holds in a neighbourhood of the candidate
  have hL6 := (eventually_redLagr_lapse hVo hq₀ han hz huniq hR).eventually_nhds
  have hcand : Tendsto (fun w : (MetF N × MetF N) × ℝ =>
      (((w.1.1, w.2 • V₁ w), w.2) : (MetF N × MetF N) × ℝ)) (𝓝 w₀) (𝓝 w₀) := by
    have h1 : Tendsto (fun w : (MetF N × MetF N) × ℝ => w.1.1) (𝓝 w₀) (𝓝 (flatMet N)) :=
      (continuous_fst.comp continuous_fst).tendsto w₀
    have := (h1.prodMk_nhds hsV).prodMk_nhds hs1
    simpa [hw₀] using this
  have hnbhd := hcand.eventually hL6
  -- analyticity of `L` at the relevant points
  have hLev : ∀ᶠ z in 𝓝 (zFlat N), AnalyticAt ℝ L z := hLan.eventually_analyticAt
  have hzq1 : Tendsto (fun w : (MetF N × MetF N) × ℝ => ((pLapse w.1.1 1, V₁ w) :
      ParF N × MetF N)) (𝓝 w₀) (𝓝 (zFlat N)) := by
    have h1 : Tendsto (fun w : (MetF N × MetF N) × ℝ => pLapse w.1.1 1) (𝓝 w₀)
        (𝓝 (zFlat N).1) := by
      have := (continuous_fst.tendsto _).comp hcont_q1
      exact this
    have := h1.prodMk_nhds hV₁t
    exact this
  have hzqs : Tendsto (fun w : (MetF N × MetF N) × ℝ => ((pLapse w.1.1 w.2, w.2 • V₁ w) :
      ParF N × MetF N)) (𝓝 w₀) (𝓝 (zFlat N)) := by
    have h1 : Tendsto (fun w : (MetF N × MetF N) × ℝ => pLapse w.1.1 w.2) (𝓝 w₀)
        (𝓝 (zFlat N).1) := by
      have := (continuous_fst.tendsto _).comp hcont_qs
      exact this
    have := h1.prodMk_nhds hsV
    exact this
  have han1 := hzq1.eventually hLev
  have hans := hzqs.eventually hLev
  have hsol1 := hcont_q1.eventually hsol
  -- local uniqueness of the Legendre inverse at the scaled point
  have hwq : Tendsto (fun w : (MetF N × MetF N) × ℝ =>
      ((((pLapse w.1.1 w.2, w.1.2), w.2 • V₁ w)) : (ParF N × MetF N) × MetF N)) (𝓝 w₀)
      (𝓝 (((zFlat N).1, (0 : MetF N)), (zFlat N).2)) := by
    have := hcont_qs.prodMk_nhds hsV
    simpa [hzV] using this
  have huniq' := hwq.eventually huniqL
  have hpos : ∀ᶠ w in 𝓝 w₀, (1 / 2 : ℝ) < w.2 :=
    hs1.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hnbhd, han1, hans, hsol1, huniq', hpos] with w hw6 hw1 hws hwsol hwu hwp
  obtain ⟨⟨γ, π⟩, s⟩ := w
  simp only at hw6 hw1 hws hwsol hwu hwp ⊢
  have hs0 : s ≠ 0 := by linarith
  set v := V₁ ((γ, π), s) with hv
  -- the identity `L(p_s, V') = s L(p_1, s⁻¹ V')` near `V' = s v`
  have hloc : (fun V' : MetF N => L (pLapse γ s, V')) =ᶠ[𝓝 (s • v)]
      fun V' => s * L (pLapse γ 1, s⁻¹ • V') := by
    have hc2 : Tendsto (fun V' : MetF N => (((γ, V'), s) : (MetF N × MetF N) × ℝ)) (𝓝 (s • v))
        (𝓝 ((γ, s • v), s)) := by
      have : Continuous (fun V' : MetF N => (((γ, V'), s) : (MetF N × MetF N) × ℝ)) := by
        fun_prop
      exact this.tendsto _
    filter_upwards [hc2.eventually hw6] with V' hV'
    exact hV'
  -- velocity momenta agree
  have hmom : velMom L (pLapse γ s, s • v) = velMom L (pLapse γ 1, v) := by
    have hd1 : DifferentiableAt ℝ L (pLapse γ 1, v) := hw1.differentiableAt
    have hds : DifferentiableAt ℝ L (pLapse γ s, s • v) := hws.differentiableAt
    ext W
    simp only [velMom, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [fderiv_apply_inr hds, fderiv_apply_inr hd1, hloc.fderiv_eq]
    have hF : HasFDerivAt (fun V' : MetF N => L (pLapse γ 1, V'))
        (fderiv ℝ (fun V' => L (pLapse γ 1, V')) v) (s⁻¹ • (s • v)) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      have : DifferentiableAt ℝ (fun V' : MetF N => L (pLapse γ 1, V')) v :=
        hd1.comp v ((differentiableAt_const _).prodMk differentiableAt_id)
      exact this.hasFDerivAt
    have hG : HasFDerivAt (fun V' : MetF N => s * L (pLapse γ 1, s⁻¹ • V'))
        (s • ((fderiv ℝ (fun V' => L (pLapse γ 1, V')) v).comp
          (s⁻¹ • ContinuousLinearMap.id ℝ (MetF N)))) (s • v) := by
      have h1 := hF.comp (s • v) ((s⁻¹ • ContinuousLinearMap.id ℝ (MetF N)).hasFDerivAt)
      exact h1.const_mul s
    rw [hG.fderiv]
    simp [smul_smul, mul_inv_cancel₀ hs0]
  -- the Legendre velocity scales
  have hVs : legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) (pLapse γ s) π = s • v := by
    refine hwu.1 fun W => ?_
    rw [hmom]
    exact hwsol W
  rw [canonicalHamiltonian_eq, canonicalHamiltonian_eq, hVs]
  have hLs : L (pLapse γ s, s • v) = s * L (pLapse γ 1, v) := by
    have := hloc.self_of_nhds
    simp only at this
    rw [this, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  change pairH π (s • v) - L (pLapse γ s, s • v) = s * (pairH π v - L (pLapse γ 1, v))
  rw [hLs, show pairH π (s • v) = s * pairH π v from by
    rw [← pairCov_apply, map_smul, ← pairCov_apply]; rfl]
  ring

/-! ### The mean lapse row of the initial constraint map -/

/-- The constant lapse direction `δN ≡ 1`. -/
def dirLapse : ParF N × MetF N := ((0, fun _ => 1, 0), 0)

theorem sum_lapseDir : ∑ x : Site N, lapseDir x = (dirLapse : ParF N × MetF N) := by
  simp only [lapseDir, dirLapse]
  ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

/-- The spatial mean `P₀` of the lapse row of `𝒞_h` (`P₀ f = h³ Σ_x f(x)`). -/
def meanLapse (χ R : ℝ) (X : MetF N × MetF N) : ℝ := hN N ^ 3 * ∑ x, (Cmap χ R X).1 x

/-- The mean lapse row is minus the derivative of `𝓗_h` along the constant lapse. -/
theorem meanLapse_eq (χ R : ℝ) (X : MetF N × MetF N) :
    meanLapse χ R X = -fderiv ℝ (canonH χ R) (qFlat N + iotaX X) dirLapse := by
  rw [meanLapse, Cmap_eq]
  simp only
  have hh : hN N ^ 3 ≠ 0 := pow_ne_zero 3 hN_ne_zero
  rw [← sum_lapseDir, map_sum]
  simp only [neg_mul_eq_neg_mul, ← Finset.mul_sum]
  rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hh]
  ring

theorem qFlat_add_iotaX_add_dirLapse (X : MetF N × MetF N) (t : ℝ) :
    qFlat N + iotaX X + t • (dirLapse : ParF N × MetF N) =
      (pLapse (flatMet N + X.1) (1 + t), X.2) := by
  ext <;> simp [qFlat, zFlat, refMult, iotaX_apply, dirLapse, pLapse, add_comm]

theorem qFlat_add_iotaX (X : MetF N × MetF N) :
    qFlat N + iotaX X = (pLapse (flatMet N + X.1) 1, X.2) := by
  ext <;> simp [qFlat, zFlat, refMult, iotaX_apply, pLapse]

/-- **The mean lapse row is minus the unit-lapse Hamiltonian** near flat data:
`P₀ 𝒞_h^{lapse}(X) = -𝓗_h(I + u, p, 1, 0)` (exact lapse homogeneity). -/
theorem eventually_meanLapse {χ R : ℝ} (hχ : χ ≠ 0) {U V : Set (CoP N)}
    (hU : FlatChart χ R U) (hVo : IsOpen V)
    (hq₀ : flatCo N ∈ V) (han : AnalyticOnNhd ℝ (statConnCo χ 0 R) V)
    (hz : statConnCo χ 0 R (flatCo N) = 0)
    (huniq : ∀ q ∈ V, ∀ A : Conn N, A ∈ closedBall (0 : Conn N) R →
      (statRow χ 0 (ofCo q).1 (ofCo q).2 A = 0 ↔ A = statConnCo χ 0 R q)) (hR : 0 < R) :
    ∀ᶠ X in 𝓝 (0 : MetF N × MetF N), meanLapse χ R X = -canonHres χ R X := by
  have hL7 := eventually_canonicalHamiltonian_lapse hχ hU hVo hq₀ han hz huniq hR
  -- pull back to `(X, t)` near `(0, 0)`
  set Φ : (MetF N × MetF N) × ℝ → (MetF N × MetF N) × ℝ :=
    fun p => ((flatMet N + p.1.1, p.1.2), 1 + p.2) with hΦ
  have hΦc : Tendsto Φ (𝓝 ((0 : MetF N × MetF N), (0 : ℝ)))
      (𝓝 ((flatMet N, (0 : MetF N)), (1 : ℝ))) := by
    have : Continuous Φ := by rw [hΦ]; fun_prop
    have h := this.tendsto ((0 : MetF N × MetF N), (0 : ℝ))
    simpa [hΦ] using h
  have h2 := hΦc.eventually hL7
  rw [nhds_prod_eq] at h2
  have h3 := h2.curry
  -- differentiability of `𝓗_h` near the base
  have hH := analyticAt_canonH hU hχ
  have hq : Tendsto (fun X : MetF N × MetF N => qFlat N + iotaX X) (𝓝 0) (𝓝 (qFlat N)) := by
    have : Continuous (fun X : MetF N × MetF N => qFlat N + iotaX X) := by fun_prop
    have h := this.tendsto 0
    rwa [map_zero, add_zero] at h
  have hdiff := hq.eventually hH.eventually_analyticAt
  filter_upwards [h3, hdiff] with X hX hXd
  rw [meanLapse_eq, canonHres_eq]
  simp only [neg_inj]
  -- the curve `t ↦ 𝓗_h(q_X + t δN)` equals `(1 + t) 𝓗_h(q_X)` near `t = 0`
  have hcurve : HasDerivAt (fun t : ℝ => canonH χ R (qFlat N + iotaX X + t • dirLapse))
      (fderiv ℝ (canonH χ R) (qFlat N + iotaX X) dirLapse) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => qFlat N + iotaX X + t • (dirLapse : ParF N × MetF N))
        dirLapse 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (dirLapse : ParF N × MetF N)).const_add
        (qFlat N + iotaX X)
    have h2 : HasFDerivAt (canonH χ R) (fderiv ℝ (canonH χ R) (qFlat N + iotaX X))
        (qFlat N + iotaX X + (0 : ℝ) • (dirLapse : ParF N × MetF N)) := by
      rw [zero_smul, add_zero]; exact hXd.differentiableAt.hasFDerivAt
    exact h2.comp_hasDerivAt 0 h1
  have hlin : HasDerivAt (fun t : ℝ => canonH χ R (qFlat N + iotaX X + t • dirLapse))
      (canonH χ R (qFlat N + iotaX X)) 0 := by
    have hev : (fun t : ℝ => canonH χ R (qFlat N + iotaX X + t • dirLapse)) =ᶠ[𝓝 0]
        fun t => (1 + t) * canonH χ R (qFlat N + iotaX X) := by
      filter_upwards [hX] with t ht
      simp only [hΦ] at ht
      rw [qFlat_add_iotaX_add_dirLapse, qFlat_add_iotaX]
      exact ht
    have h1 : HasDerivAt (fun t : ℝ => (1 + t) * canonH χ R (qFlat N + iotaX X))
        (canonH χ R (qFlat N + iotaX X)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const (canonH χ R (qFlat N + iotaX X))
    exact h1.congr_of_eventuallyEq hev
  exact hcurve.unique hlin

/-- **The quadratic jet of the mean lapse row** (`χ = 1`): `D²(P₀ 𝒞_h^{lapse})(0)[X, X] =
-2 H₂(X)`, i.e. the lapse component of the quadratic mean jet is `-H₂`. -/
theorem meanLapse_second_jet {R : ℝ} {U V : Set (CoP N)}
    (hU : FlatChart 1 R U) (hVo : IsOpen V)
    (hq₀ : flatCo N ∈ V) (han : AnalyticOnNhd ℝ (statConnCo 1 0 R) V)
    (hz : statConnCo 1 0 R (flatCo N) = 0)
    (huniq : ∀ q ∈ V, ∀ A : Conn N, A ∈ closedBall (0 : Conn N) R →
      (statRow 1 0 (ofCo q).1 (ofCo q).2 A = 0 ↔ A = statConnCo 1 0 R q)) (hR : 0 < R)
    (u p : MetF N) :
    meanLapse 1 R (0 : MetF N × MetF N) = 0 ∧
      fderiv ℝ (fderiv ℝ (meanLapse (N := N) 1 R)) 0 (u, p) (u, p) = -(2 * H2 u p) := by
  have hev : meanLapse (N := N) 1 R =ᶠ[𝓝 0] fun X => -canonHres 1 R X :=
    eventually_meanLapse one_ne_zero hU hVo hq₀ han hz huniq hR
  obtain ⟨h0, -, h2⟩ := canonicalHamiltonian_restricted_quadratic hU
  refine ⟨by rw [hev.self_of_nhds]; simp only [h0, neg_zero], ?_⟩
  have hd : fderiv ℝ (meanLapse (N := N) 1 R) =ᶠ[𝓝 0] fderiv ℝ (fun X => -canonHres 1 R X) :=
    hev.fderiv
  rw [hd.fderiv_eq]
  have e1 : fderiv ℝ (fun X : MetF N × MetF N => -canonHres 1 R X) =
      fun X => -fderiv ℝ (canonHres 1 R) X := by
    funext X; exact fderiv_neg
  rw [e1]
  have e2 : fderiv ℝ (fun X : MetF N × MetF N => -fderiv ℝ (canonHres 1 R) X) 0 =
      -fderiv ℝ (fderiv ℝ (canonHres (N := N) 1 R)) 0 := fderiv_neg
  rw [e2, neg_apply, neg_apply, h2]

/-! ### The balancing seed in `Sym₃` coordinates and `H₂` on the seed -/

section Seed

open InitialBalancePhase

/-- `Sym₃` coordinates `(11, 22, 33, 12, 13, 23)` of a `3 × 3` matrix. -/
def matToSymLin : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun M := ![M 0 0, M 1 1, M 2 2, M 0 1, M 0 2, M 1 2]
  map_add' A B := by funext c; fin_cases c <;> rfl
  map_smul' r A := by funext c; fin_cases c <;> rfl

/-- Symmetric `3 × 3` matrices. -/
def IsSym3 (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop := ∀ i j, A i j = A j i

theorem symMat_matToSym {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsSym3 A) :
    symMat (matToSymLin A) = A := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [symMat, matToSymLin, InitialConstraintLinearRange.sym6, hA 1 0, hA 2 0, hA 2 1]

theorem isSym3_T (i : Fin 3) : IsSym3 (InitialBalance.T i) := by
  intro a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [InitialBalance.T]

theorem isSym3_one : IsSym3 (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  intro a b; simp [Matrix.one_apply, eq_comm]

theorem IsSym3.add {A B : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsSym3 A) (hB : IsSym3 B) :
    IsSym3 (A + B) := fun i j => by simp [hA i j, hB i j]

theorem IsSym3.smul {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsSym3 A) (c : ℝ) : IsSym3 (c • A) :=
  fun i j => by simp [hA i j]

theorem IsSym3.sum {ι : Type*} (s : Finset ι) {A : ι → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ i, IsSym3 (A i)) : IsSym3 (∑ i ∈ s, A i) := fun a b => by
  simp only [Matrix.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hA i a b

theorem isSym3_uStar (x : InitialBalance.Grid N) : IsSym3 (InitialBalance.uStar N x) :=
  IsSym3.sum _ fun i => (isSym3_T i).smul _

theorem isSym3_pSeed (κ : ℝ) (b : Fin 3 → ℝ) (x : InitialBalance.Grid N) :
    IsSym3 (InitialBalance.pSeed N κ b x) :=
  (isSym3_one.smul _).add (IsSym3.sum _ fun i => (isSym3_T i).smul _)

theorem frob_matToSym {A B : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsSym3 A) (hB : IsSym3 B) :
    QuadJet.frob (matToSymLin A) (matToSymLin B) = InitialBalance.frob A B := by
  simp only [QuadJet.frob, symMat_matToSym hA, symMat_matToSym hB, InitialBalance.frob]

theorem trS_matToSym (A : Matrix (Fin 3) (Fin 3) ℝ) : trS (matToSymLin A) = A.trace := by
  simp [trS, symMat, matToSymLin, InitialConstraintLinearRange.sym6, Matrix.trace,
    Fin.sum_univ_three]

/-- The configuration seed `u_* = Σ_i T_i cos(2πx_i)` as a metric perturbation field. -/
def uSeed (N : ℕ) [NeZero N] : MetF N := fun z => matToSymLin (InitialBalance.uStar N (toF z))

/-- The momentum seed `p(ϑ) = -(2/3)κ I + Σ_i b_i T_i sin(2πx_i)` as a momentum field. -/
def pSeedF (N : ℕ) [NeZero N] (κ : ℝ) (b : Fin 3 → ℝ) : MetF N :=
  fun z => matToSymLin (InitialBalance.pSeed N κ b (toF z))

/-- `toF` as an equivalence of grids. -/
def toFEquiv : Site N ≃ InitialBalance.Grid N :=
  Equiv.piCongrRight fun _ => (ZMod.finEquiv N).symm

theorem sum_toF {M : Type*} [AddCommMonoid M] (f : InitialBalance.Grid N → M) :
    ∑ z : Site N, f (toF z) = ∑ x, f x :=
  Fintype.sum_equiv toFEquiv _ _ fun _ => rfl

theorem toZ_toF (z : Site N) : InitialBalancePhase.toZ (toF z) = z := by
  funext j; simp [InitialBalancePhase.toZ, toF]

theorem pd_uSeed (i : Fin 3) (z : Site N) :
    pd i (uSeed N) z = matToSymLin (phaseDerivFin i (InitialBalance.uStar N) (toF z)) := by
  have h := pd_map (N := N) i matToSymLin (fun z => InitialBalance.uStar N (toF z))
  have e : uSeed N = fun z => matToSymLin (InitialBalance.uStar N (toF z)) := rfl
  rw [e, h]
  simp only [phaseDerivFin, toZ_toF]

theorem T_diag_row (i j : Fin 3) : InitialBalance.T i i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp [InitialBalance.T]

/-- The Fierz–Pauli potential density on transverse trace-free jets `a_i = c_i T_i`. -/
theorem potJ_T (c : Fin 3 → ℝ) :
    QuadJet.potJ (fun i => matToSymLin (c i • InitialBalance.T i)) =
      1 / 4 * ∑ i, InitialBalance.frob (c i • InitialBalance.T i) (c i • InitialBalance.T i) := by
  have hs : ∀ i, IsSym3 (c i • InitialBalance.T i) := fun i => (isSym3_T i).smul _
  have h1 : ∀ i j, symMat (matToSymLin (c i • InitialBalance.T i)) i j = 0 := by
    intro i j
    rw [symMat_matToSym (hs i)]
    simp [T_diag_row]
  have h2 : ∀ j, trS (matToSymLin (c j • InitialBalance.T j)) = 0 := by
    intro j
    rw [trS_matToSym, Matrix.trace_smul, InitialBalance.trace_T, smul_zero]
  simp only [QuadJet.potJ, h1, h2, frob_matToSym (hs _) (hs _)]
  simp

/-- **`H₂` on the balancing seed** (odd `N ≥ 3`): `H₂(u_*, p(ϑ))` is minus the lapse component
of `Q_h(ϑ)`, i.e. `-(⅔κ² - ½Σb_i² - ⅜ω_h²)`. -/
theorem H2_seed (hNo : Odd N) (h3 : 3 ≤ N) (κ : ℝ) (b : Fin 3 → ℝ) :
    H2 (uSeed N) (pSeedF N κ b) =
      -(2 / 3 * κ ^ 2 - 1 / 2 * ∑ i, b i ^ 2 - 3 / 8 * omega N ^ 2) := by
  have hmj := meanJet_seed_phase hNo h3 κ b
  have hmj1 := congrArg Prod.fst hmj
  simp only [InitialBalance.meanJet] at hmj1
  rw [← hmj1, neg_neg, H2_eq]
  have hh : hN N = ((N : ℝ))⁻¹ := rfl
  have hkin : kinH (pSeedF N κ b) = InitialBalance.gridNormSq N (InitialBalance.pSeed N κ b) -
      1 / 2 * InitialBalance.scalarNormSq N (fun x => (InitialBalance.pSeed N κ b x).trace) := by
    simp only [kinH, pSeedF, InitialBalance.gridNormSq, InitialBalance.gridInner,
      InitialBalance.scalarNormSq, hh, frob_matToSym (isSym3_pSeed κ b _) (isSym3_pSeed κ b _),
      trS_matToSym]
    rw [sum_toF (fun x => InitialBalance.frob (InitialBalance.pSeed N κ b x)
      (InitialBalance.pSeed N κ b x)), sum_toF (fun x => (InitialBalance.pSeed N κ b x).trace ^ 2)]
  have hpot : potH (uSeed N) =
      1 / 4 * ∑ i, InitialBalance.gridNormSq N (phaseDerivFin i (InitialBalance.uStar N)) := by
    simp only [potH, pd_uSeed, phaseDerivFin_uStar hNo h3, potJ_T, InitialBalance.gridNormSq,
      InitialBalance.gridInner, hh]
    rw [sum_toF (fun x => 1 / 4 * ∑ i, InitialBalance.frob
      ((-(omega N * InitialBalance.sinMode N i x)) • InitialBalance.T i)
      ((-(omega N * InitialBalance.sinMode N i x)) • InitialBalance.T i))]
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hkin, hpot]

end Seed

/-! ### Assembly: the lapse component of `eq:supp-initial-quadratic-mean` -/

/-- **The lapse component of the quadratic mean jet of the actual action on the seed**
(`lem:supp-initial-balance`, first component of `eq:supp-initial-quadratic-mean`; `χ = 1`, `Λ = 0`,
symmetric-square-root triad, odd `N ≥ 3`).  There is an `N`-independent threshold `ε` such that
for `0 < R`, `hR ≤ ε`, the spatial mean `P₀ = h³Σ_x` of the lapse row of the original initial
constraint map `𝒞_h = Cmap 1 R` vanishes at flat data and its quadratic Taylor coefficient on the
seed `Z(ϑ) = (u_*, p(ϑ))` is exactly `⅔κ² - ½Σ_i b_i² - ⅜ω_h²`, the first component of
`Q_h(ϑ)` (`ω_h = 2h⁻¹ sin(πh)`).  Proof: exact lapse homogeneity of the discrete action
(`phaseLagr_lapse_scale`) transported through the stationary connection and the Legendre
transform, so that `P₀𝒞_h^{lapse} = -𝓗_h(·, 1, 0)`, whose Hessian is `2H₂`. -/
theorem lapse_mean_jet_seed :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N], Odd N → 3 ≤ N → ∀ R : ℝ, 0 < R → hN N * R ≤ ε →
      ∀ (κ : ℝ) (b : Fin 3 → ℝ),
        meanLapse (N := N) 1 R 0 = 0 ∧
        1 / 2 * fderiv ℝ (fderiv ℝ (meanLapse (N := N) 1 R)) 0 (uSeed N, pSeedF N κ b)
          (uSeed N, pSeedF N κ b) = (InitialBalance.Qh (omega N) (κ, b)).1 := by
  obtain ⟨ε₁, hε₁, h₁⟩ := flat_chart 1 one_ne_zero
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_uniq_chart 1 one_ne_zero
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun N _ hNo h3 R hR hhR κ b => ?_⟩
  obtain ⟨U, hU⟩ := h₁ N R hR (hhR.trans (min_le_left _ _))
  obtain ⟨V, hVo, hq₀, han, hz, huniq⟩ := h₂ N R hR (hhR.trans (min_le_right _ _))
  obtain ⟨h0, h2⟩ := meanLapse_second_jet hU hVo hq₀ han hz huniq hR (uSeed N) (pSeedF N κ b)
  refine ⟨h0, ?_⟩
  rw [h2, H2_seed hNo h3 κ b]
  simp only [InitialBalance.Qh]
  ring

/-- Non-vacuity: the flat datum is a zero of the original initial constraint map, so the mean
jet statement is about an actual nonempty chart (and `Q_h` has the root `ϑ_h^*`). -/
example : InitialBalance.Qh (omega 3) (3 * omega 3 / 4, 0) = 0 := InitialBalance.Qh_root _

end LapseHomogeneity

end RenewalGeometry.ExactPhaseAction
