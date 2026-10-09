/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialCalculusLocal
import RenewalGeometry.Action.ExactReducedLagrangianJet

/-!
# Site-wise formulas for the stationary row and the Legendre row of the explicit action
  (infrastructure for `lem:supp-initial-calculus`; emergent-spacetime manuscript)

All objects are those of the explicit phase-compatible action (`ExactStationaryConnection.lean`,
`ExactLegendreHamiltonian.lean`) with the symmetric-square-root triad.  We write each row at a
site `x` as an analytic function of finitely many local values, so that the uniform
derivative bounds of `PeriodicGridLocalAnalytic.lean` apply.

* `eG v n b = admCoframe(E(I + v), n, b)` (`E` = symmetric square root), `eU v = eG v 1 0`,
  `analyticAt_eG`, `eU_zero`.
* `cartLoc χ E a`: the Cartan operator at one site; `cartanOp_apply` (definitional).
* `fLoc`: the phase-compatible load at one site in terms of the phase derivatives of the entries of
  `Π_i(e)`, `Σ_ji(e)` and of `∂_tΠ`; `fPh_apply`.
* `PdLoc v V i = D_γ Π_i(I + v)[V]` (`piDot` at one site), `analyticAt_PdLoc`.
* **`exists_statRowExplicit_eq_local`**: for `hN N`, `‖A‖` below an `N`-independent radius,
  `γ°_h(e, ∂_tΠ; A)(x) = fLoc(…)(x) + cartLoc(e(x), A(x)) + NhLoc(h, (e(x - o_ℓ)), (A(x - o_ℓ + o_ν)))`.
-/

open Filter Finset Metric
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.InitialCalculus

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open LocalSumGradient OddPhaseDerivativeReal QuadJet

/-! ### The coframe of a metric perturbation -/

/-- The canonical ADM coframe of the metric `I + v` (symmetric-square-root triad), lapse `n`,
shift `b`. -/
def eG (v : Fin 6 → ℝ) (n : ℝ) (b : Fin 3 → ℝ) : M4 :=
  admCoframe (sqrtTriad (symMat (flatSym + v))) n b

/-- Unit lapse, zero shift. -/
def eU (v : Fin 6 → ℝ) : M4 := eG v 1 0

theorem eU_zero : eU 0 = 1 := by
  rw [eU, eG, add_zero, symMat_flatSym, sqrtTriad_one]
  exact admCoframe_flat

theorem analyticAt_eG : AnalyticAt ℝ (fun p : (Fin 6 → ℝ) × ℝ × (Fin 3 → ℝ) => eG p.1 p.2.1 p.2.2)
    (0, 1, 0) := by
  have hv : AnalyticAt ℝ (fun p : (Fin 6 → ℝ) × ℝ × (Fin 3 → ℝ) => flatSym + p.1) (0, 1, 0) :=
    analyticAt_const.add analyticAt_fst
  have htr : AnalyticAt ℝ (fun p : (Fin 6 → ℝ) × ℝ × (Fin 3 → ℝ) => sqrtTriad (symMat (flatSym + p.1)))
      (0, 1, 0) := by
    refine analyticAt_sqrtTriad.comp_of_eq (analyticAt_symMat_comp hv) ?_
    simp [symMat_flatSym]
  exact analyticAt_admCoframe_comp htr (analyticAt_fst.comp analyticAt_snd)
    (analyticAt_snd.comp analyticAt_snd)

theorem analyticAt_eU : AnalyticAt ℝ eU 0 := by
  have h : AnalyticAt ℝ (fun v : Fin 6 → ℝ => ((v, 1, 0) : (Fin 6 → ℝ) × ℝ × (Fin 3 → ℝ))) 0 :=
    analyticAt_id.prod analyticAt_const
  exact analyticAt_eG.comp_of_eq h rfl

theorem analyticAt_eU_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E}
    {f : E → Fin 6 → ℝ} (hf : AnalyticAt ℝ f p) (h0 : f p = 0) :
    AnalyticAt ℝ (fun q => eU (f q)) p :=
  analyticAt_eU.comp_of_eq hf h0

/-! ### The Cartan operator at one site -/

/-- The Cartan operator at one site, in Lorentz coordinates. -/
def cartLoc (χ : ℝ) (E : M4) (a : LocVal) : LocVal :=
  fun μ => Fin.cases (coord (∑ i, bracket (iota (a i.succ)) (piArr χ E i)))
    (fun i => coord (bracket (piArr χ E i) (iota (a 0)) +
      ∑ j, bracket (iota (a j.succ)) (sigmaArr χ E i j))) μ

variable {N : ℕ} [NeZero N]

theorem cartanOp_apply (χ : ℝ) (e : Site N → M4) (A : Conn N) (x : Site N) :
    cartanOp χ e A x = cartLoc χ (e x) (A x) := rfl

theorem analyticAt_coordM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E}
    {f : E → M4} (hf : AnalyticAt ℝ f p) (k : Fin 6) : AnalyticAt ℝ (fun q => coord (f q) k) p :=
  analyticAt_coord_comp hf k

theorem analyticAt_iota_comp' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E}
    {c : E → Fin 6 → ℝ} (hc : AnalyticAt ℝ c p) : AnalyticAt ℝ (fun q => iota (c q)) p :=
  analyticAt_iota_comp fun k => analyticAt_pi_apply hc k

theorem analyticAt_cartLoc_comp (χ : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : E} {e : E → M4} {a : E → LocVal} (he : AnalyticAt ℝ e p) (ha : AnalyticAt ℝ a p)
    (μ : Fin 4) (k : Fin 6) : AnalyticAt ℝ (fun q => cartLoc χ (e q) (a q) μ k) p := by
  have hai : ∀ ν, AnalyticAt ℝ (fun q => iota (a q ν)) p := fun ν =>
    analyticAt_iota_comp' (analyticAt_pi_apply ha ν)
  cases μ using Fin.cases with
  | zero =>
    simp only [cartLoc, Fin.cases_zero]
    exact analyticAt_coordM (Finset.analyticAt_fun_sum _ fun i _ =>
      analyticAt_bracket_comp (hai i.succ) (analyticAt_piArr_comp χ i he)) k
  | succ i =>
    simp only [cartLoc, Fin.cases_succ]
    exact analyticAt_coordM ((analyticAt_bracket_comp (analyticAt_piArr_comp χ i he) (hai 0)).add
      (Finset.analyticAt_fun_sum _ fun j _ =>
        analyticAt_bracket_comp (hai j.succ) (analyticAt_sigmaArr_comp χ i j he))) k

/-! ### The load at one site -/

/-- The phase-compatible load at one site from the phase derivatives `dP i K L = δ_i(Π_i)_{KL}`,
`dS j i K L = δ_j(Σ_ji)_{KL}` and the `Π`-velocities `P i`. -/
def fLoc (dP : Fin 3 → Fin 4 → Fin 4 → ℝ) (dS : Fin 3 → Fin 3 → Fin 4 → Fin 4 → ℝ)
    (P : Fin 3 → M4) : LocVal :=
  fun μ => Fin.cases (coord (∑ i, Matrix.of (dP i)))
    (fun i => coord (-P i + -∑ j, Matrix.of (dS j i))) μ

theorem fPh_apply (χ : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4) (x : Site N) :
    fPh χ e Pidot x = fLoc (fun i K L => pd i (fun y => piArr χ (e y) i K L) x)
      (fun j i K L => pd j (fun y => sigmaArr χ (e y) j i K L) x) (fun i => Pidot i x) := by
  funext μ
  have h0 : load0Ph χ e x = ∑ i, Matrix.of (fun K L => pd i (fun y => piArr χ (e y) i K L) x) := by
    unfold load0Ph
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Matrix.ext fun K L => pd_matrix_apply i _ x K L
  have h1 : ∀ i, loadSpPh χ e i x =
      -∑ j, Matrix.of (fun K L => pd j (fun y => sigmaArr χ (e y) j i K L) x) := by
    intro i
    unfold loadSpPh
    refine congrArg Neg.neg (Finset.sum_congr rfl fun j _ => ?_)
    exact Matrix.ext fun K L => pd_matrix_apply j _ x K L
  cases μ using Fin.cases with
  | zero =>
    change coord (load0Ph χ e x) = coord (∑ i, Matrix.of (fun K L =>
      pd i (fun y => piArr χ (e y) i K L) x))
    rw [h0]
  | succ i =>
    change coord (-Pidot i x + loadSpPh χ e i x) = coord (-Pidot i x + -∑ j, Matrix.of
      (fun K L => pd j (fun y => sigmaArr χ (e y) j i K L) x))
    rw [h1]

/-! ### The `Π`-velocity at one site -/

/-- `∂_tΠ_i` at one site: `D_γ Π_i(I + v)[V]`. -/
def PdLoc (χ : ℝ) (v V : Fin 6 → ℝ) (i : Fin 3) : M4 :=
  Matrix.of fun K L => fderiv ℝ (piEntry χ sqrtTriad i K L) (flatSym + v) V

theorem piDot_apply (χ : ℝ) (u V : MetF N) (i : Fin 3) (x : Site N) :
    piDot χ sqrtTriad (flatMet N + u) V i x = PdLoc χ (u x) (V x) i := rfl

theorem analyticAt_PdLoc (χ : ℝ) (i : Fin 3) (K L : Fin 4) :
    AnalyticAt ℝ (fun p : (Fin 6 → ℝ) × (Fin 6 → ℝ) => PdLoc χ p.1 p.2 i K L) (0, 0) := by
  have htr : ∀ g : Fin 6 → ℝ, symMat g = one3 → AnalyticAt ℝ sqrtTriad (symMat g) := by
    intro g hg; rw [hg]; exact analyticAt_sqrtTriad
  have hE : AnalyticAt ℝ (piEntry χ sqrtTriad i K L) (flatSym + 0) :=
    analyticAt_piEntry χ (htr _ (by simp [symMat_flatSym])) i K L
  have hf : AnalyticAt ℝ (fun p : (Fin 6 → ℝ) × (Fin 6 → ℝ) =>
      fderiv ℝ (piEntry χ sqrtTriad i K L) (flatSym + p.1)) (0, 0) :=
    hE.fderiv.comp_of_eq (analyticAt_const.add analyticAt_fst) rfl
  exact ((ContinuousLinearMap.id ℝ ((Fin 6 → ℝ) →L[ℝ] ℝ)).analyticAt_bilinear _).comp
    (hf.prod analyticAt_snd)

theorem PdLoc_zero_right (χ : ℝ) (v : Fin 6 → ℝ) (i : Fin 3) : PdLoc χ v 0 i = 0 := by
  ext K L; simp [PdLoc]

/-! ### The explicit stationary row as a local formula -/

/-- **The explicit stationary row at one site** (`eq:supp-exact-stationary-connection`): for
`hN N` and the sup norm of the connection below an `N`-independent radius,
`γ°_h(x) = f°_h(x) + C(e(x))A(x) + N_h(e, A)(x)` with every term given by a local formula. -/
theorem exists_statRowExplicit_eq_local : ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (χ : ℝ) (e : Site N → M4)
    (Pidot : Fin 3 → Site N → M4) (A : Conn N), hN N < δ → ‖A‖ < δ → ∀ x : Site N,
      statRowExplicit χ e Pidot A x =
        fLoc (fun i K L => pd i (fun y => piArr χ (e y) i K L) x)
          (fun j i K L => pd j (fun y => sigmaArr χ (e y) j i K L) x) (fun i => Pidot i x) +
        cartLoc χ (e x) (A x) +
        NhLoc χ (hN N, fun ℓ => e (x - offs ℓ), fun ℓ => loc offs (x - offs ℓ) A) := by
  obtain ⟨δ, hδ, h⟩ := exists_Nh_eq_NhLoc
  refine ⟨δ, hδ, fun N _ χ e Pidot A hh hA x => ?_⟩
  simp only [statRowExplicit, Pi.add_apply, fPh_apply, cartanOp_apply, h N χ e A hh hA x]

end RenewalGeometry.ExactPhaseAction.InitialCalculus
