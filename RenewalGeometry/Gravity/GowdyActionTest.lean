/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdyActionTestJetBounds
import RenewalGeometry.Gravity.GowdyHigherOrderStateError

/-!
# The independent action test of the Gowdy regulator
  (`eq:supp-gowdy-action-test`, `eq:supp-gowdy-kappa`, first clause of (G4) of
  `thm:main-gowdy-regulator`; emergent-spacetime supplement)

The independent midpoint/centered discretization of the unreduced ADM density
(`GowdyActionTestDensity.lean`: `discreteAction`, all six fields `(R, λ, P, Q, N, β)` independent,
`-2NR''` replaced by `2N'R'`) is evaluated at the recorded areal-gauge fields of a numerical
history of the Gowdy split scheme (`arealRecord`: `R = t_n`, `λ, P, Q` from the records, `N = 1`,
`β = 0`), and its first variation `δS_h` is tested against a fixed smooth local test `φ` of all
six fields (lapse and shift varied before the areal-gauge restriction), sampled on the grid
(`testSample`).

* `actionKappa`: `κ_h = ε₀ + h² + √𝓕_h` (`eq:supp-gowdy-kappa`) in the `C¹_h` norm (`r = 1`).
* `action_test` (**`eq:supp-gowdy-action-test`**, with an `O(h)` quadrature term): for a smooth
  reference, every smooth test supported in `[t_a, t_b] × 𝕋¹ ⊂ (t₀, t₁) × 𝕋¹` (`2π`-periodic in
  `θ`) and every chart/envelope radius there are `C, ℓ₀` such that for `h = ℓ = 2π/N ≤ ℓ₀`,
  every time window `[τ₀, τ₀ + n₀ h] ⊆ [t₀, t₁]` whose interior contains `[t_a, t_b]` and every
  history realized by split steps in the enforced `C¹_h` envelope with `κ_h ≤ 1`,
  `|δS_h - δS_*| ≤ C (κ_h + h)`, where `δS_* = 0` is the continuum first variation of the
  areal lift (`continuumFirstVariation_arealLift_eq_zero`).
* `action_test_pathwise` (**first clause of (G4)**: the first-variation residual tends to zero):
  on the histories of (G3) (offset cap `charDist(X_{n+1}, B_n) ≤ c₀ h⁴`, initial `C¹_h` error
  `≤ c₁ h²`, `C¹_h` envelope) `|δS_h| ≤ C h` (`actionKappa_le_of_offset_cap`: `κ_h = O(h)` there).
* `successful_histories_inherit` (**inheritance clause of `prop:main-safe-access`**): on the
  deterministic admissible support (offset/solver cap, `C¹_h` envelope, initial error `O(h²)`)
  every history has both the pathwise curvature estimate `eq:main-gowdy-full-curvature`
  (`readout_full_curvature_of_envelope`) and the action-test bound `|δS_h| ≤ C h`.
* `exists_nonzero_local_test`: non-vacuity of the test hypotheses (a smooth bump in `t`).

The manuscript states `|δS_h - δS_*| ≤ C κ_h`; the proof here uses first-order (Lipschitz) cell
quadrature, which contributes the additional `O(h)` term.  Both versions tend to zero, which is
what (G4) asserts.
-/

open Set Finset
open scoped BigOperators ContDiff

namespace RenewalGeometry.GowdyStaggered.ActionTest

noncomputable section

open HermiteReadout CharStability PeriodicGridResidual

variable {t₀ t₁ : ℝ} {N : ℕ}

/-! ### Error arrays: componentwise bounds -/

theorem norm_le_crNorm_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NeZero N]
    (ℓ : ℝ) (v : ZMod N → E) : ‖v‖ ≤ crNorm 1 ℓ v := by
  have := Finset.le_sup' (fun k => ‖(PeriodicGridResidual.fwdDiff ℓ)^[k] v‖) (mem_range.2 (by norm_num : 0 < 1 + 1))
  exact this

theorem norm_fwdDiff_le_crNorm_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NeZero N] (ℓ : ℝ) (v : ZMod N → E) : ‖PeriodicGridResidual.fwdDiff ℓ v‖ ≤ crNorm 1 ℓ v := by
  have := Finset.le_sup' (fun k => ‖(PeriodicGridResidual.fwdDiff ℓ)^[k] v‖) (mem_range.2 (by norm_num : 1 < 1 + 1))
  exact this

/-- **Componentwise bounds from the `C¹_ℓ` error norm**: the `λ`, `P`, `Q` errors and their
forward space differences are bounded by `‖errArr X Y‖_{1,∞,ℓ}`. -/
theorem errArr_component_bounds [NeZero N] (X Y : GridState N) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (j : ZMod N) :
    |X.lam j - Y.lam j| ≤ crNorm 1 ℓ (errArr X Y) ∧
    |(X.site j).P - (Y.site j).P| ≤ crNorm 1 ℓ (errArr X Y) ∧
    |(X.site j).Q - (Y.site j).Q| ≤ crNorm 1 ℓ (errArr X Y) ∧
    |(X.lam (j + 1) - Y.lam (j + 1)) - (X.lam j - Y.lam j)| / ℓ ≤ crNorm 1 ℓ (errArr X Y) ∧
    |((X.site (j + 1)).P - (Y.site (j + 1)).P) - ((X.site j).P - (Y.site j).P)| / ℓ ≤
      crNorm 1 ℓ (errArr X Y) ∧
    |((X.site (j + 1)).Q - (Y.site (j + 1)).Q) - ((X.site j).Q - (Y.site j).Q)| / ℓ ≤
      crNorm 1 ℓ (errArr X Y) := by
  have h0 := (norm_le_pi_norm (errArr X Y) j).trans (norm_le_crNorm_one ℓ (errArr X Y))
  have h1 := (norm_le_pi_norm (PeriodicGridResidual.fwdDiff ℓ (errArr X Y)) j).trans
    (norm_fwdDiff_le_crNorm_one ℓ (errArr X Y))
  set v := errArr X Y j with hv
  set w := PeriodicGridResidual.fwdDiff ℓ (errArr X Y) j with hw
  have hvl : |X.lam j - Y.lam j| ≤ ‖v‖ := by
    have := norm_snd_le v; rwa [Real.norm_eq_abs] at this
  have hvP : |(X.site j).P - (Y.site j).P| ≤ ‖v‖ := (abs_P_le v.1).trans (norm_fst_le v)
  have hvQ : |(X.site j).Q - (Y.site j).Q| ≤ ‖v‖ := (abs_Q_le v.1).trans (norm_fst_le v)
  have hw2 : w.2 = ℓ⁻¹ * ((X.lam (j + 1) - Y.lam (j + 1)) - (X.lam j - Y.lam j)) := by
    simp [hw, PeriodicGridResidual.fwdDiff, errArr]
  have hw1P : w.1.2.1 = ℓ⁻¹ * (((X.site (j + 1)).P - (Y.site (j + 1)).P) -
      ((X.site j).P - (Y.site j).P)) := by
    simp [hw, PeriodicGridResidual.fwdDiff, errArr, LocalState.toVec]
  have hw1Q : w.1.2.2.1 = ℓ⁻¹ * (((X.site (j + 1)).Q - (Y.site (j + 1)).Q) -
      ((X.site j).Q - (Y.site j).Q)) := by
    simp [hw, PeriodicGridResidual.fwdDiff, errArr, LocalState.toVec]
  have hwl : |w.2| ≤ ‖w‖ := by have := norm_snd_le w; rwa [Real.norm_eq_abs] at this
  have hwP : |w.1.2.1| ≤ ‖w‖ := (abs_P_le w.1).trans (norm_fst_le w)
  have hwQ : |w.1.2.2.1| ≤ ‖w‖ := (abs_Q_le w.1).trans (norm_fst_le w)
  have hdiv : ∀ x : ℝ, |ℓ⁻¹ * x| = |x| / ℓ := fun x => by
    rw [abs_mul, abs_inv, abs_of_pos hℓ]; ring
  refine ⟨hvl.trans h0, hvP.trans h0, hvQ.trans h0, ?_, ?_, ?_⟩
  · rw [← hdiv, ← hw2]; exact hwl.trans h1
  · rw [← hdiv, ← hw1P]; exact hwP.trans h1
  · rw [← hdiv, ← hw1Q]; exact hwQ.trans h1

/-! ### Residual budgets -/

theorem residualFlux_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NeZero N]
    (r : ℕ) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) (res : ℕ → ZMod N → E) {n n₀ : ℕ}
    (hn : n ≤ n₀) : residualFlux r ℓ h res n ≤ residualFlux r ℓ h res n₀ := by
  unfold residualFlux residualEnergy
  gcongr

theorem residualFlux_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NeZero N]
    (r : ℕ) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) (res : ℕ → ZMod N → E) (n : ℕ) :
    0 ≤ residualFlux r ℓ h res n := by
  unfold residualFlux residualEnergy
  exact div_nonneg (Finset.sum_nonneg fun i _ => by positivity) (by positivity)

/-- **A single residual is controlled by the normalized flux**: for `h = ℓ ∈ (0, 2]` and
`n < n₀`, `‖r_n‖_∞ ≤ 2 ℓ √𝓕_h` with `𝓕_h = ℓ^{-3} ∑_{k<n₀} ‖r_k‖²_{2,ℓ}/(2ℓ)` (`r = 1`). -/
theorem norm_le_two_mul_sqrt_residualFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NeZero N] {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ 2) (res : ℕ → ZMod N → E) {n n₀ : ℕ}
    (hn : n < n₀) : ‖res n‖ ≤ 2 * ℓ * Real.sqrt (residualFlux 1 ℓ ℓ res n₀) := by
  set F := residualFlux 1 ℓ ℓ res n₀
  set l := l2Norm ℓ (res n)
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hF0 : 0 ≤ F := residualFlux_nonneg 1 hℓ hℓ res n₀
  have hl2 : l ^ 2 ≤ 2 * ℓ ^ 4 * F := by
    have hsingle : l ^ 2 / (2 * ℓ) ≤ residualEnergy ℓ ℓ res n₀ :=
      Finset.single_le_sum (f := fun k => l2Norm ℓ (res k) ^ 2 / (2 * ℓ))
        (fun k _ => by positivity) (mem_range.2 hn)
    have hF : F = residualEnergy ℓ ℓ res n₀ / ℓ ^ 3 := by simp [F, residualFlux]
    rw [hF]
    rw [div_le_iff₀ (by positivity)] at hsingle
    have : 2 * ℓ ^ 4 * (residualEnergy ℓ ℓ res n₀ / ℓ ^ 3) =
        residualEnergy ℓ ℓ res n₀ * (2 * ℓ) := by field_simp
    rw [this]; exact hsingle
  have hsq : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ.le
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  refine (norm_le_l2Norm hℓ (res n)).trans ?_
  rw [div_le_iff₀ hs]
  -- `l ≤ 2 ℓ √F √ℓ` from `l² ≤ 2ℓ⁴F ≤ 4ℓ³F`
  have hrhs : 0 ≤ 2 * ℓ * Real.sqrt F * Real.sqrt ℓ := by positivity
  refine (pow_le_pow_iff_left₀ hl0 hrhs (by norm_num : (2 : ℕ) ≠ 0)).1 ?_
  have hkey : 0 ≤ 2 * ℓ ^ 3 * F * (2 - ℓ) :=
    mul_nonneg (by positivity) (by linarith)
  calc l ^ 2 ≤ 2 * ℓ ^ 4 * F := hl2
    _ ≤ 4 * ℓ ^ 2 * F * ℓ := by nlinarith
    _ = (2 * ℓ * Real.sqrt F * Real.sqrt ℓ) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hF0, hsq]; ring

/-! ### The tested objects -/

/-- The grid sampling `φ_k(τ₀ + n h, θ_j)` of a test of the six fields. -/
def testSample (φ : Fin 6 → ℝ × ℝ → ℝ) (τ₀ h : ℝ) (N : ℕ) : ℕ → ZMod N → Fin 6 → ℝ :=
  fun n j k => φ k (τ₀ + n * h, sampleAngle N j)

/-- **`κ_h = ε₀ + h² + √𝓕_h`** (`eq:supp-gowdy-kappa`) of a history `X` with split stages `B`,
in the `C¹_h` norm: `ε₀ = ‖X₀ - 𝖲_hX_*(τ₀)‖_{1,∞,h}`, `𝓕_h = h^{-3} ∑_{k<n₀} ‖r_k‖²_{2,h}/(2h)`
with residuals `r_k = X_{k+1} - B_k`. -/
def actionKappa [NeZero N] {t₀ t₁ : ℝ} (sol : GowdyFrameSolution t₀ t₁) (τ₀ : ℝ) (n₀ : ℕ)
    (X B : ℕ → GridState N) : ℝ :=
  crNorm 1 (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) + (2 * Real.pi / N) ^ 2 +
    Real.sqrt (residualFlux 1 (2 * Real.pi / N) (2 * Real.pi / N)
      (fun k => errArr (X (k + 1)) (B k)) n₀)

/-- The error of the recorded `λ` against the sampled reference. -/
def errLam (sol : GowdySmoothReference t₀ t₁) (τ₀ h : ℝ) (X : ℕ → GridState N) :
    ℕ → ZMod N → ℝ :=
  fun n j => (X n).lam j - sol.lam (τ₀ + n * h, sampleAngle N j)

/-- The error of the recorded `P`. -/
def errP (sol : GowdySmoothReference t₀ t₁) (τ₀ h : ℝ) (X : ℕ → GridState N) :
    ℕ → ZMod N → ℝ :=
  fun n j => ((X n).site j).P - sol.P (τ₀ + n * h, sampleAngle N j)

/-- The error of the recorded `Q`. -/
def errQ (sol : GowdySmoothReference t₀ t₁) (τ₀ h : ℝ) (X : ℕ → GridState N) :
    ℕ → ZMod N → ℝ :=
  fun n j => ((X n).site j).Q - sol.Q (τ₀ + n * h, sampleAngle N j)

theorem recLam_eq (sol : GowdySmoothReference t₀ t₁) (τ₀ h : ℝ) (X : ℕ → GridState N) :
    recLam X = fun n j => sampleField sol.lam τ₀ h N n j + errLam sol τ₀ h X n j := by
  funext n j; simp [recLam, sampleField, errLam]

theorem recP_eq (sol : GowdySmoothReference t₀ t₁) (τ₀ h : ℝ) (X : ℕ → GridState N) :
    recP X = fun n j => sampleField sol.P τ₀ h N n j + errP sol τ₀ h X n j := by
  funext n j; simp [recP, sampleField, errP]

theorem recQ_eq (sol : GowdySmoothReference t₀ t₁) (τ₀ h : ℝ) (X : ℕ → GridState N) :
    recQ X = fun n j => sampleField sol.Q τ₀ h N n j + errQ sol τ₀ h X n j := by
  funext n j; simp [recQ, sampleField, errQ]

/-- The first-variation density at an areal-gauge jet as a function of the eight solution-jet
entries `(t, λ_t, λ_θ, P, P_t, P_θ, Q_t, Q_θ)` and of the test jet. -/
def liftVar (z : (Fin 8 → ℝ) × FieldJet) : ℝ :=
  liftVariation (z.1 0) (z.1 1) (z.1 2) (z.1 3) (z.1 4) (z.1 5) (z.1 6) (z.1 7) z.2

theorem contDiff_liftVar : ContDiff ℝ 1 liftVar := by
  unfold liftVar liftVariation
  fun_prop

/-- The continuum solution-jet entries of the areal lift at `p`. -/
def contEntries (sol : GowdySmoothReference t₀ t₁) (p : ℝ × ℝ) : Fin 8 → ℝ :=
  ![p.1, dT sol.lam p, dΘ sol.lam p, sol.P p, dT sol.P p, dΘ sol.P p, dT sol.Q p, dΘ sol.Q p]

/-- The discrete solution-jet entries of the recorded areal-gauge fields on the cell `(n, j)`. -/
def gridEntries (τ₀ h ℓ : ℝ) (X : ℕ → GridState N) (n : ℕ) (j : ZMod N) : Fin 8 → ℝ :=
  ![τ₀ + n * h + h / 2, gridDt h (recLam X) n j, gridDθ ℓ (recLam X) n j, gridAvg (recP X) n j,
    gridDt h (recP X) n j, gridDθ ℓ (recP X) n j, gridDt h (recQ X) n j, gridDθ ℓ (recQ X) n j]

theorem discreteFirstVariation_eq_liftVar [NeZero N] {h : ℝ} (hh : h ≠ 0) (ℓ τ₀ : ℝ) (n₀ : ℕ)
    (X : ℕ → GridState N) (φ : ℕ → ZMod N → Fin 6 → ℝ) :
    discreteFirstVariation h ℓ n₀ (arealRecord τ₀ h X) φ =
      ∑ n ∈ range n₀, ∑ j : ZMod N, h * ℓ *
        liftVar (gridEntries τ₀ h ℓ X n j, gridJet h ℓ φ n j) := by
  rw [discreteFirstVariation_arealRecord hh]
  rfl

theorem continuumFirstVariation_eq_liftVar (sol : GowdySmoothReference t₀ t₁)
    {φ : Fin 6 → ℝ × ℝ → ℝ} (hφ : ∀ k, Differentiable ℝ (φ k)) (α β : ℝ) :
    continuumFirstVariation (arealLift sol) φ α β =
      ∫ t in α..β, ∫ θ in (0 : ℝ)..2 * Real.pi,
        liftVar (contEntries sol (t, θ), contJet φ (t, θ)) := by
  rw [continuumFirstVariation_eq α β
    (fun k => (contDiff_arealLift sol k).differentiable (by simp)) hφ
    (fun p => by simp [arealLift])]
  simp only [contJet_arealLift, admVariation_liftJet]
  rfl

theorem continuous_dT {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) : Continuous fun p => dT F p :=
  (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_dΘ {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) : Continuous fun p => dΘ F p :=
  (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_contEntries_contJet (sol : GowdySmoothReference t₀ t₁)
    {φ : Fin 6 → ℝ × ℝ → ℝ} (hφ : ∀ k, ContDiff ℝ 1 (φ k)) :
    Continuous fun p => (contEntries sol p, contJet φ p) := by
  have hl : ContDiff ℝ 1 sol.lam := sol.smoothInf_lam.of_le (by exact_mod_cast le_top)
  have hP : ContDiff ℝ 1 sol.P := sol.smoothInf_P.of_le (by exact_mod_cast le_top)
  have hQ : ContDiff ℝ 1 sol.Q := sol.smoothInf_Q.of_le (by exact_mod_cast le_top)
  refine Continuous.prodMk (continuous_pi fun i => ?_) (Continuous.prodMk
    (continuous_pi fun k => (hφ k).continuous) (Continuous.prodMk
      (continuous_pi fun k => continuous_dT (hφ k)) (continuous_pi fun k => continuous_dΘ (hφ k))))
  fin_cases i
  · exact continuous_fst
  · exact continuous_dT hl
  · exact continuous_dΘ hl
  · exact hP.continuous
  · exact continuous_dT hP
  · exact continuous_dΘ hP
  · exact continuous_dT hQ
  · exact continuous_dΘ hQ

theorem exists_bound_contEntries_contJet (sol : GowdySmoothReference t₀ t₁)
    {φ : Fin 6 → ℝ × ℝ → ℝ} (hφ : ∀ k, ContDiff ℝ 1 (φ k))
    (hper : ∀ k (p : ℝ × ℝ), φ k (p.1, p.2 + 2 * Real.pi) = φ k p) :
    ∃ B, 0 ≤ B ∧ ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ‖(contEntries sol p, contJet φ p)‖ ≤ B :=
  exists_bound_of_periodic _ (continuous_contEntries_contJet sol hφ) (fun p => by
    simp only [contEntries, contJet, dT_periodic sol.periodic_lam, dΘ_periodic sol.periodic_lam,
      sol.periodic_P, dT_periodic sol.periodic_P, dΘ_periodic sol.periodic_P,
      dT_periodic sol.periodic_Q, dΘ_periodic sol.periodic_Q, hper, dT_periodic (hper _),
      dΘ_periodic (hper _)]) t₀ t₁

/-- `liftVar` is Lipschitz on every closed ball. -/
theorem exists_lipschitz_liftVar (ρ : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ z ∈ Metric.closedBall (0 : (Fin 8 → ℝ) × FieldJet) ρ,
      ∀ z' ∈ Metric.closedBall (0 : (Fin 8 → ℝ) × FieldJet) ρ,
        |liftVar z - liftVar z'| ≤ K * ‖z - z'‖ := by
  obtain ⟨K, hK⟩ := contDiff_liftVar.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ⟨K, K.2, fun z hz z' hz' => ?_⟩
  have := hK.dist_le_mul z hz z' hz'
  rwa [Real.dist_eq, dist_eq_norm] at this

/-! ### Error bounds along a history in the `C¹_h` envelope -/

/-- **Jet errors of the recorded fields.**  For a smooth reference, a chart radius `R` and an
enforced `C¹_h` envelope radius, there are `C_s, C_t, ℓ₁` such that every history realised by split
steps in the envelope has, with `κ = actionKappa`: value and forward-space-difference errors of
`λ, P, Q` at most `C_s κ`, and time-difference errors at most `C_t κ` (state error
`eq:supp-gowdy-state-error` for `r = 1` together with the nodal time differences). -/
theorem exists_history_error_bounds (sol : GowdySmoothReference t₀ t₁) (h0 : 0 < t₀) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) (Renv : ℝ) :
    ∃ Cs Ct ℓ₁ : ℝ, 0 ≤ Cs ∧ 0 ≤ Ct ∧ 0 < ℓ₁ ∧ ℓ₁ ≤ 2 ∧
      ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₁ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ), t₀ ≤ τ₀ → τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁ →
      ∀ X A B : ℕ → GridState N,
        (∀ n < n₀, CharStability.IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
          GowdyEnvR 1 t₀ R Renv (2 * Real.pi / N) (X n) (A n) (B n)) →
        (∀ n ≤ n₀, ∀ j : ZMod N,
          |errLam sol τ₀ (2 * Real.pi / N) X n j| ≤ Cs * actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B ∧
          |errP sol τ₀ (2 * Real.pi / N) X n j| ≤ Cs * actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B ∧
          |errQ sol τ₀ (2 * Real.pi / N) X n j| ≤ Cs * actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B ∧
          |errLam sol τ₀ (2 * Real.pi / N) X n (j + 1) - errLam sol τ₀ (2 * Real.pi / N) X n j| /
            (2 * Real.pi / N) ≤ Cs * actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B ∧
          |errP sol τ₀ (2 * Real.pi / N) X n (j + 1) - errP sol τ₀ (2 * Real.pi / N) X n j| /
            (2 * Real.pi / N) ≤ Cs * actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B ∧
          |errQ sol τ₀ (2 * Real.pi / N) X n (j + 1) - errQ sol τ₀ (2 * Real.pi / N) X n j| /
            (2 * Real.pi / N) ≤ Cs * actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B) ∧
        (∀ n < n₀, ∀ j : ZMod N,
          |errLam sol τ₀ (2 * Real.pi / N) X (n + 1) j - errLam sol τ₀ (2 * Real.pi / N) X n j| /
            (2 * Real.pi / N) ≤ Ct * actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B ∧
          |errP sol τ₀ (2 * Real.pi / N) X (n + 1) j - errP sol τ₀ (2 * Real.pi / N) X n j| /
            (2 * Real.pi / N) ≤ Ct * actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B ∧
          |errQ sol τ₀ (2 * Real.pi / N) X (n + 1) j - errQ sol τ₀ (2 * Real.pi / N) X n j| /
            (2 * Real.pi / N) ≤ Ct * actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B) := by
  obtain ⟨Cs, ℓs, hCs, hℓs, hst⟩ :=
    sol.toGowdyFrameSolution.state_error_crNorm_flux sol.isSmooth h0 1 hR Renv
  have hR0 : 0 ≤ R := by linarith [(sol.toGowdyFrameSolution.chartRadius_spec h0).1]
  set Kt := 15 * gowdyLipschitz (t₀ / 2) R + 32 * R with hKt
  have hKt0 : 0 ≤ Kt := by
    have := gowdyLipschitz_nonneg (by linarith : 0 < t₀ / 2) hR0
    positivity
  set Cc := sol.toGowdyFrameSolution.charConsConst h0
  have hCc : 0 ≤ Cc := sol.toGowdyFrameSolution.charConsConst_nonneg h0
  refine ⟨Cs, Kt * Cs + 2 + Cc, min ℓs (min (sol.toGowdyFrameSolution.charStabStep h0 R) 2),
    hCs, by positivity, lt_min hℓs (lt_min (sol.toGowdyFrameSolution.charStabStep_pos h0 hR0)
      two_pos), (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro N _ hN τ₀ n₀ hτ₀ hn₀ X A B hstep
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hℓ2 : ℓ ≤ 2 := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  set κ := actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B with hκ
  set F := residualFlux 1 ℓ ℓ (fun k => errArr (X (k + 1)) (B k)) n₀ with hF
  have hF0 : 0 ≤ F := residualFlux_nonneg 1 hℓpos hℓpos _ n₀
  have he0 : 0 ≤ crNorm 1 ℓ (errArr (X 0) (sol.sample N τ₀)) := crNorm_nonneg _ _ _
  have hκF : Real.sqrt F ≤ κ := by
    simp only [hκ, actionKappa]; nlinarith [sq_nonneg ℓ]
  have hκℓ : ℓ ^ 2 ≤ κ := by
    simp only [hκ, actionKappa]; nlinarith [Real.sqrt_nonneg F]
  -- the `C¹_h` state error
  have hcr : ∀ n ≤ n₀, crNorm 1 ℓ (errArr (X n) (sol.sample N (τ₀ + n * ℓ))) ≤ Cs * κ := by
    intro n hn
    refine (hst N (hN.trans (min_le_left _ _)) τ₀ n₀ hτ₀ hn₀ X A B hstep n hn).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCs
    have := Real.sqrt_le_sqrt (residualFlux_mono 1 hℓpos hℓpos
      (fun k => errArr (X (k + 1)) (B k)) hn)
    simp only [hκ, actionKappa]
    linarith
  refine ⟨fun n hn j => ?_, fun n hn j => ?_⟩
  · obtain ⟨b1, b2, b3, b4, b5, b6⟩ :=
      errArr_component_bounds (X n) (sol.sample N (τ₀ + n * ℓ)) hℓpos j
    have hc := hcr n hn
    exact ⟨b1.trans hc, b2.trans hc, b3.trans hc, b4.trans hc, b5.trans hc, b6.trans hc⟩
  · -- the nodal time differences
    have henv : ∀ n < n₀, SplitEnvelope (t₀ / 2) R ℓ (X n) (A n) (B n) := by
      intro n hn j
      obtain ⟨h1, h2, h3⟩ := (hstep n hn).2.1 j
      refine ⟨chartK_subset_gowdyChart h1, h2.1, ?_⟩
      have e : ((transport ℓ (A n)).site j).toVec =
          (gowdyData.transport ℓ (toCG (A n))).site j := by
        rw [← toCG_transport]; rfl
      have := chartK_subset_gowdyChart h3
      rw [e]
      exact this
    have hE : ∀ n ≤ n₀, charDist (X n) (sol.sample N (τ₀ + n * ℓ)) ≤ Cs * κ := fun n hn =>
      (charDist_le_norm_errArr _ _).trans ((norm_le_crNorm_one ℓ _).trans (hcr n hn))
    have hρ : ∀ n < n₀, charDist (X (n + 1)) (B n) ≤ 2 * ℓ * Real.sqrt F := fun n hn =>
      (charDist_le_norm_errArr _ _).trans
        (norm_le_two_mul_sqrt_residualFlux hℓpos hℓ2 (fun k => errArr (X (k + 1)) (B k)) hn)
    obtain ⟨t1, t2⟩ := sol.toGowdyFrameSolution.nodal_time_difference h0 hR N
      (hN.trans ((min_le_right _ _).trans (min_le_left _ _))) τ₀ n₀ hτ₀ hn₀ X A B
      (fun n hn => ⟨(hstep n hn).1, henv n hn⟩) hE hρ n hn j
    have hρℓ : 2 * ℓ * Real.sqrt F / ℓ = 2 * Real.sqrt F := by field_simp
    rw [hρℓ] at t1 t2
    have hbound : Kt * (Cs * κ) + 2 * Real.sqrt F + Cc * ℓ ^ 2 ≤ (Kt * Cs + 2 + Cc) * κ := by
      nlinarith [mul_le_mul_of_nonneg_left hκℓ hCc]
    set Δ := ((X (n + 1)).site j).toVec -
          ((sol.sample N (τ₀ + (n + 1 : ℕ) * ℓ)).site j).toVec -
          (((X n).site j).toVec - ((sol.sample N (τ₀ + n * ℓ)).site j).toVec) with hΔ
    have hPΔ : |errP sol τ₀ ℓ X (n + 1) j - errP sol τ₀ ℓ X n j| ≤ ‖projZero Δ‖ := by
      have e : (projZero Δ).2.1 = errP sol τ₀ ℓ X (n + 1) j - errP sol τ₀ ℓ X n j := by
        rw [projZero_apply]
        simp [hΔ, errP, LocalState.toVec, GowdyFrameSolution.sample, LocalState.ofVec,
          GowdyFrameSolution.Z]
      rw [← e]; exact abs_P_le _
    have hQΔ : |errQ sol τ₀ ℓ X (n + 1) j - errQ sol τ₀ ℓ X n j| ≤ ‖projZero Δ‖ := by
      have e : (projZero Δ).2.2.1 = errQ sol τ₀ ℓ X (n + 1) j - errQ sol τ₀ ℓ X n j := by
        rw [projZero_apply]
        simp [hΔ, errQ, LocalState.toVec, GowdyFrameSolution.sample, LocalState.ofVec,
          GowdyFrameSolution.Z]
      rw [← e]; exact abs_Q_le _
    refine ⟨?_, ?_, ?_⟩
    · exact (le_of_eq (by rfl)).trans (t2.trans hbound)
    · exact (div_le_div_of_nonneg_right hPΔ hℓpos.le).trans (t1.trans hbound)
    · exact (div_le_div_of_nonneg_right hQΔ hℓpos.le).trans (t1.trans hbound)

/-! ### Jet comparisons on a cell -/

/-- **Test jets**: the discrete jets of the sampled test are within `M (h + ℓ)` of its continuum
jets on the whole cell. -/
theorem exists_testJet_error {φ : Fin 6 → ℝ × ℝ → ℝ} (hφ : ∀ k, ContDiff ℝ 2 (φ k))
    (hper : ∀ k (p : ℝ × ℝ), φ k (p.1, p.2 + 2 * Real.pi) = φ k p) (t₀ t₁ : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ (N : ℕ) [NeZero N] (τ₀ h : ℝ) (n : ℕ), 0 < h → t₀ ≤ τ₀ + n * h →
      τ₀ + n * h + h ≤ t₁ → ∀ (j : ZMod N), ∀ t ∈ Icc (τ₀ + n * h) (τ₀ + n * h + h),
      ∀ ϑ ∈ Icc (sampleAngle N j) (sampleAngle N j + 2 * Real.pi / N),
        ‖gridJet h (2 * Real.pi / N) (testSample φ τ₀ h N) n j - contJet φ (t, ϑ)‖ ≤
          M * (h + 2 * Real.pi / N) := by
  have hex := fun k => exists_sampleField_jet_error (hφ k) (hper k) t₀ t₁
  choose M hM hbd using hex
  refine ⟨∑ k, M k, Finset.sum_nonneg fun k _ => hM k, ?_⟩
  intro N _ τ₀ h n hh hτ hτh j t ht ϑ hϑ
  have hℓ : 0 < 2 * Real.pi / N := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hMk : ∀ k, M k * (h + 2 * Real.pi / N) ≤ (∑ k, M k) * (h + 2 * Real.pi / N) :=
    fun k => mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := M) (fun k _ => hM k) (mem_univ k)) (by positivity)
  have hnn : 0 ≤ (∑ k, M k) * (h + 2 * Real.pi / N) :=
    mul_nonneg (Finset.sum_nonneg fun k _ => hM k) (by positivity)
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · refine (pi_norm_le_iff_of_nonneg hnn).2 fun k => ?_
    rw [Real.norm_eq_abs]
    exact (hbd k N τ₀ h n hh hτ hτh j t ht ϑ hϑ).1.trans (hMk k)
  · refine (pi_norm_le_iff_of_nonneg hnn).2 fun k => ?_
    rw [Real.norm_eq_abs]
    exact (hbd k N τ₀ h n hh hτ hτh j t ht ϑ hϑ).2.1.trans (hMk k)
  · refine (pi_norm_le_iff_of_nonneg hnn).2 fun k => ?_
    rw [Real.norm_eq_abs]
    exact (hbd k N τ₀ h n hh hτ hτh j t ht ϑ hϑ).2.2.trans (hMk k)

theorem abs_add_sub_le (a b c : ℝ) : |a + b - c| ≤ |a - c| + |b| := by
  rw [show a + b - c = (a - c) + b by ring]; exact abs_add_le _ _

/-- **Solution jets**: on a cell, the discrete solution-jet entries of the recorded areal-gauge
fields differ from the continuum ones by at most `M + E₁ + T + h`, where `M` bounds the jet
errors of the sampled reference, `E₁` the value and forward-space-difference errors of the
records and `T` their time-difference errors. -/
theorem norm_gridEntries_sub_contEntries_le [NeZero N] (sol : GowdySmoothReference t₀ t₁)
    {τ₀ h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (X : ℕ → GridState N) (n : ℕ) (j : ZMod N)
    {t ϑ : ℝ} (ht : t ∈ Icc (τ₀ + n * h) (τ₀ + n * h + h)) {M E₁ T : ℝ}
    (hS1 : |gridDt h (sampleField sol.lam τ₀ h N) n j - dT sol.lam (t, ϑ)| ≤ M)
    (hS2 : |gridDθ ℓ (sampleField sol.lam τ₀ h N) n j - dΘ sol.lam (t, ϑ)| ≤ M)
    (hS3 : |gridAvg (sampleField sol.P τ₀ h N) n j - sol.P (t, ϑ)| ≤ M)
    (hS4 : |gridDt h (sampleField sol.P τ₀ h N) n j - dT sol.P (t, ϑ)| ≤ M)
    (hS5 : |gridDθ ℓ (sampleField sol.P τ₀ h N) n j - dΘ sol.P (t, ϑ)| ≤ M)
    (hS6 : |gridDt h (sampleField sol.Q τ₀ h N) n j - dT sol.Q (t, ϑ)| ≤ M)
    (hS7 : |gridDθ ℓ (sampleField sol.Q τ₀ h N) n j - dΘ sol.Q (t, ϑ)| ≤ M)
    (hEv : |errP sol τ₀ h X n j| ≤ E₁ ∧ |errP sol τ₀ h X (n + 1) j| ≤ E₁)
    (hEs : ∀ m ∈ ({n, n + 1} : Finset ℕ), ∀ k : ZMod N,
      |errLam sol τ₀ h X m (k + 1) - errLam sol τ₀ h X m k| / ℓ ≤ E₁ ∧
      |errP sol τ₀ h X m (k + 1) - errP sol τ₀ h X m k| / ℓ ≤ E₁ ∧
      |errQ sol τ₀ h X m (k + 1) - errQ sol τ₀ h X m k| / ℓ ≤ E₁)
    (hEt : |errLam sol τ₀ h X (n + 1) j - errLam sol τ₀ h X n j| / h ≤ T ∧
      |errP sol τ₀ h X (n + 1) j - errP sol τ₀ h X n j| / h ≤ T ∧
      |errQ sol τ₀ h X (n + 1) j - errQ sol τ₀ h X n j| / h ≤ T) :
    ‖gridEntries τ₀ h ℓ X n j - contEntries sol (t, ϑ)‖ ≤ M + E₁ + T + h := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hS1
  have hE : 0 ≤ E₁ := (abs_nonneg _).trans hEv.1
  have hT : 0 ≤ T := (div_nonneg (abs_nonneg _) hh.le).trans hEt.1
  have dLt := abs_gridDt_le (e := errLam sol τ₀ h X) hh hEt.1
  have dPt := abs_gridDt_le (e := errP sol τ₀ h X) hh hEt.2.1
  have dQt := abs_gridDt_le (e := errQ sol τ₀ h X) hh hEt.2.2
  have dLs := abs_gridDθ_le (e := errLam sol τ₀ h X) (j := j) hℓ fun m hm k => (hEs m hm k).1
  have dPs := abs_gridDθ_le (e := errP sol τ₀ h X) (j := j) hℓ fun m hm k => (hEs m hm k).2.1
  have dQs := abs_gridDθ_le (e := errQ sol τ₀ h X) (j := j) hℓ fun m hm k => (hEs m hm k).2.2
  have dPv := abs_gridAvg_le (e := errP sol τ₀ h X) hEv.1 hEv.2
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i
  · simp only [gridEntries, contEntries, Pi.sub_apply]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  · simp only [gridEntries, contEntries, Pi.sub_apply]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [recLam_eq sol τ₀ h X, gridDt_add]
    linarith [abs_add_sub_le (gridDt h (sampleField sol.lam τ₀ h N) n j)
      (gridDt h (errLam sol τ₀ h X) n j) (dT sol.lam (t, ϑ))]
  · simp [gridEntries, contEntries]
    rw [recLam_eq sol τ₀ h X, gridDθ_add]
    linarith [abs_add_sub_le (gridDθ ℓ (sampleField sol.lam τ₀ h N) n j)
      (gridDθ ℓ (errLam sol τ₀ h X) n j) (dΘ sol.lam (t, ϑ))]
  · simp [gridEntries, contEntries]
    rw [recP_eq sol τ₀ h X, gridAvg_add]
    linarith [abs_add_sub_le (gridAvg (sampleField sol.P τ₀ h N) n j)
      (gridAvg (errP sol τ₀ h X) n j) (sol.P (t, ϑ))]
  · simp [gridEntries, contEntries]
    rw [recP_eq sol τ₀ h X, gridDt_add]
    linarith [abs_add_sub_le (gridDt h (sampleField sol.P τ₀ h N) n j)
      (gridDt h (errP sol τ₀ h X) n j) (dT sol.P (t, ϑ))]
  · simp [gridEntries, contEntries]
    rw [recP_eq sol τ₀ h X, gridDθ_add]
    linarith [abs_add_sub_le (gridDθ ℓ (sampleField sol.P τ₀ h N) n j)
      (gridDθ ℓ (errP sol τ₀ h X) n j) (dΘ sol.P (t, ϑ))]
  · simp [gridEntries, contEntries]
    rw [recQ_eq sol τ₀ h X, gridDt_add]
    linarith [abs_add_sub_le (gridDt h (sampleField sol.Q τ₀ h N) n j)
      (gridDt h (errQ sol τ₀ h X) n j) (dT sol.Q (t, ϑ))]
  · simp [gridEntries, contEntries]
    rw [recQ_eq sol τ₀ h X, gridDθ_add]
    linarith [abs_add_sub_le (gridDθ ℓ (sampleField sol.Q τ₀ h N) n j)
      (gridDθ ℓ (errQ sol τ₀ h X) n j) (dΘ sol.Q (t, ϑ))]

/-! ### Sums over the periodic grid -/

theorem sum_zmod_eq_sum_range [NeZero N] (g : ZMod N → ℝ) :
    ∑ j : ZMod N, g j = ∑ j ∈ range N, g (j : ZMod N) := by
  refine Finset.sum_nbij' (fun j => j.val) (fun j => (j : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro j _; simp [ZMod.val_lt]
  · intro j _; simp
  · intro j _; simp
  · intro j hj; rw [Finset.mem_range] at hj; simp [ZMod.val_cast_of_lt hj]
  · intro j _; simp

theorem sampleAngle_natCast [NeZero N] {j : ℕ} (hj : j < N) :
    sampleAngle N (j : ZMod N) = j * (2 * Real.pi / N) := by
  simp [sampleAngle, ZMod.val_cast_of_lt hj]

/-! ### The action test -/

/-- **The independent action test `eq:supp-gowdy-action-test`** (first clause of (G4) of
`thm:main-gowdy-regulator`, with an `O(h)` quadrature term).

Let `X_*` be a smooth reference (`GowdySmoothReference`, `t₀ > 0`), `R ≥ chartRadius` a chart
radius and `R_env` an enforced `C¹_h` envelope radius, and let `φ` be a smooth test of all six
fields `(δR, δλ, δP, δQ, δN, δβ)` — lapse and shift varied independently — `2π`-periodic in `θ`
and supported in `[t_a, t_b] × 𝕋¹` with `t₀ < t_a ≤ t_b < t₁`.  Then the continuum first
variation of the unreduced action at the areal lift vanishes, `δS_* = 0`, and there are `C ≥ 0`,
`ℓ₀ > 0` such that for every grid `h = ℓ = 2π/N ≤ ℓ₀`, every time window
`[τ₀, τ₀ + n₀ h] ⊆ [t₀, t₁]` with `τ₀ < t_a`, `t_b < τ₀ + n₀ h`, and every numerical history
`X_n` realised by Gowdy split steps in the envelope with `κ_h ≤ 1`, the first variation of the
independent midpoint/centered discrete action at the recorded areal-gauge fields, in the
direction of the sampled test, satisfies `|δS_h - δS_*| ≤ C (κ_h + h)`. -/
theorem action_test (sol : GowdySmoothReference t₀ t₁) (h0 : 0 < t₀) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) (Renv : ℝ) {φ : Fin 6 → ℝ × ℝ → ℝ}
    (hφ : ∀ k, ContDiff ℝ ∞ (φ k))
    (hper : ∀ k (p : ℝ × ℝ), φ k (p.1, p.2 + 2 * Real.pi) = φ k p)
    {ta tb : ℝ} (hta : t₀ < ta) (hab : ta ≤ tb) (htb : tb < t₁)
    (hsupp : ∀ k (p : ℝ × ℝ), p.1 ∉ Icc ta tb → φ k p = 0) :
    continuumFirstVariation (arealLift sol) φ t₀ t₁ = 0 ∧
    ∃ C ℓ₀ : ℝ, 0 ≤ C ∧ 0 < ℓ₀ ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ), t₀ ≤ τ₀ → τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁ → τ₀ < ta →
        tb < τ₀ + n₀ * (2 * Real.pi / N) →
      ∀ X A B : ℕ → GridState N,
        (∀ n < n₀, CharStability.IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
          GowdyEnvR 1 t₀ R Renv (2 * Real.pi / N) (X n) (A n) (B n)) →
        actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B ≤ 1 →
        |discreteFirstVariation (2 * Real.pi / N) (2 * Real.pi / N) n₀
            (arealRecord τ₀ (2 * Real.pi / N) X) (testSample φ τ₀ (2 * Real.pi / N) N) -
          continuumFirstVariation (arealLift sol) φ t₀ t₁| ≤
          C * (actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B + 2 * Real.pi / N) := by
  have hφ2 : ∀ k, ContDiff ℝ 2 (φ k) := fun k => (hφ k).of_le (by norm_cast)
  have hφ1 : ∀ k, ContDiff ℝ 1 (φ k) := fun k => (hφ k).of_le (by exact_mod_cast le_top)
  have hφd : ∀ k, Differentiable ℝ (φ k) := fun k => (hφ1 k).differentiable one_ne_zero
  have hzero : ∀ α β : ℝ, t₀ ≤ α → α ≤ β → β ≤ t₁ → α ∉ Icc ta tb → β ∉ Icc ta tb →
      continuumFirstVariation (arealLift sol) φ α β = 0 := fun α β hα hαβ hβ hαs hβs =>
    continuumFirstVariation_arealLift_eq_zero sol h0 hφ1 hper hαβ hα hβ
      (fun k θ => hsupp k (α, θ) hαs) (fun k θ => hsupp k (β, θ) hβs)
  have hS0 : continuumFirstVariation (arealLift sol) φ t₀ t₁ = 0 :=
    hzero t₀ t₁ le_rfl (by linarith) le_rfl (fun h => by linarith [h.1])
      (fun h => by linarith [h.2])
  refine ⟨hS0, ?_⟩
  -- constants
  obtain ⟨Cs, Ct, ℓ₁, hCs, hCt, hℓ₁, hℓ₁2, hhist⟩ := exists_history_error_bounds sol h0 hR Renv
  have hl2 : ContDiff ℝ 2 sol.lam := sol.smoothInf_lam.of_le (by norm_cast)
  have hP2 : ContDiff ℝ 2 sol.P := sol.smoothInf_P.of_le (by norm_cast)
  have hQ2 : ContDiff ℝ 2 sol.Q := sol.smoothInf_Q.of_le (by norm_cast)
  obtain ⟨Ml, hMl, hjl⟩ := exists_sampleField_jet_error hl2 sol.periodic_lam t₀ t₁
  obtain ⟨MP, hMP, hjP⟩ := exists_sampleField_jet_error hP2 sol.periodic_P t₀ t₁
  obtain ⟨MQ, hMQ, hjQ⟩ := exists_sampleField_jet_error hQ2 sol.periodic_Q t₀ t₁
  obtain ⟨Mφ, hMφ, hjφ⟩ := exists_testJet_error hφ2 hper t₀ t₁
  obtain ⟨Bd, hBd0, hBd⟩ := exists_bound_contEntries_contJet sol hφ1 hper
  set Ms := Ml + MP + MQ with hMs
  have hMs0 : 0 ≤ Ms := by positivity
  set c1 := 2 * (Ms + Mφ) + 1 + Cs + Ct with hc1
  have hc10 : 0 ≤ c1 := by positivity
  obtain ⟨K, hK0, hK⟩ := exists_lipschitz_liftVar (Bd + 3 * c1)
  set T := max (t₁ - t₀) 0 with hT
  have hT0 : 0 ≤ T := le_max_right _ _
  refine ⟨K * c1 * T * (2 * Real.pi), ℓ₁, by positivity, hℓ₁, ?_⟩
  intro N _ hN τ₀ n₀ hτ₀ hn₀ hτa htb' X A B hstep hκ1
  set ℓ := 2 * Real.pi / N with hℓ
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hℓpos : 0 < ℓ := by positivity
  have hℓ2 : ℓ ≤ 2 := hN.trans hℓ₁2
  have hNℓ : (N : ℝ) * ℓ = 2 * Real.pi := by rw [hℓ]; field_simp
  set κ := actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B with hκ
  have hκ0 : 0 ≤ κ := by
    simp only [hκ, actionKappa]
    have := crNorm_nonneg 1 ℓ (errArr (X 0) (sol.sample N τ₀))
    positivity
  obtain ⟨hE, hTd⟩ := hhist N hN τ₀ n₀ hτ₀ hn₀ X A B hstep
  rw [hS0, sub_zero, discreteFirstVariation_eq_liftVar hℓpos.ne' ℓ τ₀ n₀ X]
  -- the window integral vanishes
  have hwin := hzero τ₀ (τ₀ + n₀ * ℓ) hτ₀ (by linarith) hn₀ (fun h => by linarith [h.1])
    (fun h => by linarith [h.2])
  rw [continuumFirstVariation_eq_liftVar sol hφd] at hwin
  -- cell comparison
  have hFc : Continuous fun p : ℝ × ℝ => liftVar (contEntries sol p, contJet φ p) :=
    contDiff_liftVar.continuous.comp (continuous_contEntries_contJet sol hφ1)
  have hcell : ∀ n < n₀, ∀ j < N, ∀ t ∈ Icc (τ₀ + n * ℓ) (τ₀ + n * ℓ + ℓ),
      ∀ θ ∈ Icc (j * ℓ : ℝ) (j * ℓ + ℓ),
      |liftVar (contEntries sol (t, θ), contJet φ (t, θ)) -
        liftVar (gridEntries τ₀ ℓ ℓ X n (j : ZMod N),
          gridJet ℓ ℓ (testSample φ τ₀ ℓ N) n (j : ZMod N))| ≤ K * (c1 * (κ + ℓ)) := by
    intro n hn j hj t ht θ hθ
    have hθ' : θ ∈ Icc (sampleAngle N (j : ZMod N)) (sampleAngle N (j : ZMod N) + ℓ) := by
      rw [sampleAngle_natCast hj]; exact hθ
    have hn1 : ((n + 1 : ℕ) : ℝ) ≤ n₀ := by exact_mod_cast hn
    have hτn : t₀ ≤ τ₀ + n * ℓ := by
      have : 0 ≤ (n : ℝ) * ℓ := by positivity
      linarith
    have hτnh : τ₀ + n * ℓ + ℓ ≤ t₁ := by
      have : ((n + 1 : ℕ) : ℝ) * ℓ ≤ n₀ * ℓ := mul_le_mul_of_nonneg_right hn1 hℓpos.le
      push_cast at this
      linarith
    have htslab : t ∈ Icc t₀ t₁ := ⟨hτn.trans ht.1, ht.2.trans hτnh⟩
    obtain ⟨l1, l2, l3⟩ := hjl N τ₀ ℓ n hℓpos hτn hτnh (j : ZMod N) t ht θ hθ'
    obtain ⟨p1, p2, p3⟩ := hjP N τ₀ ℓ n hℓpos hτn hτnh (j : ZMod N) t ht θ hθ'
    obtain ⟨q1, q2, q3⟩ := hjQ N τ₀ ℓ n hℓpos hτn hτnh (j : ZMod N) t ht θ hθ'
    have hMs' : ∀ M' : ℝ, M' ≤ Ms → M' * (ℓ + ℓ) ≤ Ms * (ℓ + ℓ) := fun M' h =>
      mul_le_mul_of_nonneg_right h (by positivity)
    have hlMs : Ml ≤ Ms := by rw [hMs]; linarith
    have hPMs : MP ≤ Ms := by rw [hMs]; linarith
    have hQMs : MQ ≤ Ms := by rw [hMs]; linarith
    have hE0 := hE n (Nat.le_of_lt hn) (j : ZMod N)
    have hE1 := hE (n + 1) hn (j : ZMod N)
    have hx := norm_gridEntries_sub_contEntries_le sol hℓpos hℓpos X n (j : ZMod N) ht
      (M := Ms * (ℓ + ℓ)) (E₁ := Cs * κ) (T := Ct * κ)
      (l2.trans (hMs' Ml hlMs)) (l3.trans (hMs' Ml hlMs))
      (p1.trans (hMs' MP hPMs)) (p2.trans (hMs' MP hPMs)) (p3.trans (hMs' MP hPMs))
      (q2.trans (hMs' MQ hQMs)) (q3.trans (hMs' MQ hQMs))
      ⟨hE0.2.1, hE1.2.1⟩
      (fun m hm k => by
        have hm' : m ≤ n₀ := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl <;> omega
        have := hE m hm' k
        exact ⟨this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩)
      (hTd n hn (j : ZMod N))
    have hy := hjφ N τ₀ ℓ n hℓpos hτn hτnh (j : ZMod N) t ht θ hθ'
    set D := c1 * (κ + ℓ) with hDdef
    have hxD : Ms * (ℓ + ℓ) + Cs * κ + Ct * κ + ℓ ≤ D := by
      rw [hDdef, hc1, ← sub_nonneg]
      have e : (2 * (Ms + Mφ) + 1 + Cs + Ct) * (κ + ℓ) - (Ms * (ℓ + ℓ) + Cs * κ + Ct * κ + ℓ) =
          2 * Ms * κ + 2 * Mφ * κ + 2 * Mφ * ℓ + κ + Cs * ℓ + Ct * ℓ := by ring
      rw [e]; positivity
    have hyD : Mφ * (ℓ + ℓ) ≤ D := by
      rw [hDdef, hc1, ← sub_nonneg]
      have e : (2 * (Ms + Mφ) + 1 + Cs + Ct) * (κ + ℓ) - Mφ * (ℓ + ℓ) =
          2 * Ms * κ + 2 * Ms * ℓ + 2 * Mφ * κ + κ + ℓ + Cs * κ + Cs * ℓ + Ct * κ + Ct * ℓ := by
        ring
      rw [e]; positivity
    have hdiff : ‖(gridEntries τ₀ ℓ ℓ X n (j : ZMod N),
        gridJet ℓ ℓ (testSample φ τ₀ ℓ N) n (j : ZMod N)) -
        (contEntries sol (t, θ), contJet φ (t, θ))‖ ≤ D :=
      norm_prod_le_iff.2 ⟨hx.trans hxD, hy.trans hyD⟩
    have hD3 : D ≤ 3 * c1 := by
      rw [hDdef, mul_comm 3 c1]
      exact mul_le_mul_of_nonneg_left (by linarith) hc10
    have hc : (contEntries sol (t, θ), contJet φ (t, θ)) ∈
        Metric.closedBall (0 : (Fin 8 → ℝ) × FieldJet) (Bd + 3 * c1) := by
      rw [mem_closedBall_zero_iff]; linarith [hBd (t, θ) htslab]
    have hd : (gridEntries τ₀ ℓ ℓ X n (j : ZMod N),
        gridJet ℓ ℓ (testSample φ τ₀ ℓ N) n (j : ZMod N)) ∈
        Metric.closedBall (0 : (Fin 8 → ℝ) × FieldJet) (Bd + 3 * c1) := by
      rw [mem_closedBall_zero_iff]
      have := norm_le_insert' (gridEntries τ₀ ℓ ℓ X n (j : ZMod N),
        gridJet ℓ ℓ (testSample φ τ₀ ℓ N) n (j : ZMod N))
        (contEntries sol (t, θ), contJet φ (t, θ))
      linarith [hBd (t, θ) htslab, hdiff, hD3]
    have := hK _ hc _ hd
    rw [norm_sub_rev] at this
    exact this.trans (mul_le_mul_of_nonneg_left hdiff hK0)
  have hcells := RectangleIntegrationByParts.abs_sum_cells_sub_integral2_le hFc hℓpos hℓpos n₀ N
    (fun n j => liftVar (gridEntries τ₀ ℓ ℓ X n (j : ZMod N),
      gridJet ℓ ℓ (testSample φ τ₀ ℓ N) n (j : ZMod N))) (a := τ₀) (η := K * (c1 * (κ + ℓ)))
    hcell
  rw [hNℓ, hwin, sub_zero] at hcells
  have hsum : ∑ n ∈ range n₀, ∑ j : ZMod N, ℓ * ℓ *
        liftVar (gridEntries τ₀ ℓ ℓ X n j, gridJet ℓ ℓ (testSample φ τ₀ ℓ N) n j) =
      ∑ n ∈ range n₀, ∑ j ∈ range N, ℓ * ℓ *
        liftVar (gridEntries τ₀ ℓ ℓ X n (j : ZMod N),
          gridJet ℓ ℓ (testSample φ τ₀ ℓ N) n (j : ZMod N)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    exact sum_zmod_eq_sum_range _
  rw [hsum]
  refine hcells.trans ?_
  have hnT : (n₀ : ℝ) * ℓ ≤ T := (by linarith : (n₀ : ℝ) * ℓ ≤ t₁ - t₀).trans (le_max_left _ _)
  have hKc : 0 ≤ K * (c1 * (κ + ℓ)) := by positivity
  calc K * (c1 * (κ + ℓ)) * (n₀ * ℓ) * (2 * Real.pi)
      ≤ K * (c1 * (κ + ℓ)) * T * (2 * Real.pi) := by gcongr
    _ = K * c1 * T * (2 * Real.pi) * (κ + ℓ) := by ring

/-! ### The (G3) histories: the first-variation residual tends to zero -/

theorem l2Norm_le_sqrt_mul_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NeZero N]
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (v : ZMod N → E) :
    l2Norm ℓ v ≤ Real.sqrt (N * ℓ) * ‖v‖ := by
  unfold l2Norm
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  calc ℓ * ∑ j, ‖v j‖ ^ 2 ≤ ℓ * ∑ _j : ZMod N, ‖v‖ ^ 2 := by
        gcongr with j; exact norm_le_pi_norm v j
    _ = N * ℓ * ‖v‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring

/-- **`κ_h = O(h)` on the (G3) histories**: with the offset cap
`charDist(X_{n+1}, B_n) ≤ c₀ h⁴` (`eq:supp-gowdy-offset-cap`) and initial `C¹_h` error
`≤ c₁ h²`, for `h ≤ 1` and `n₀ h ≤ T`: `κ_h ≤ (c₁ + 1 + 3 c₀ √(π T)) h`. -/
theorem actionKappa_le_of_offset_cap [NeZero N] (sol : GowdyFrameSolution t₀ t₁)
    {c₀ c₁ T : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hT : 0 ≤ T) (hℓ1 : 2 * Real.pi / N ≤ 1)
    (τ₀ : ℝ) (n₀ : ℕ) (hn : n₀ * (2 * Real.pi / N) ≤ T) (X B : ℕ → GridState N)
    (hoff : ∀ n < n₀, charDist (X (n + 1)) (B n) ≤ c₀ * (2 * Real.pi / N) ^ 4)
    (hinit : crNorm 1 (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) ≤
      c₁ * (2 * Real.pi / N) ^ 2) :
    actionKappa sol τ₀ n₀ X B ≤ (c₁ + 1 + 3 * c₀ * Real.sqrt (Real.pi * T)) * (2 * Real.pi / N) := by
  set ℓ := 2 * Real.pi / N with hℓ
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hℓpos : 0 < ℓ := by positivity
  have hNℓ : (N : ℝ) * ℓ = 2 * Real.pi := by rw [hℓ]; field_simp
  set F := residualFlux 1 ℓ ℓ (fun k => errArr (X (k + 1)) (B k)) n₀ with hF
  -- each residual in `L²`
  have hl2 : ∀ k < n₀, l2Norm ℓ (errArr (X (k + 1)) (B k)) ^ 2 ≤
      2 * Real.pi * (3 * c₀ * ℓ ^ 4) ^ 2 := by
    intro k hk
    have h1 := l2Norm_le_sqrt_mul_norm hℓpos.le (errArr (X (k + 1)) (B k))
    have h2 := (norm_errArr_le_charDist (X (k + 1)) (B k)).trans
      (mul_le_mul_of_nonneg_left (hoff k hk) (by norm_num : (0 : ℝ) ≤ 3))
    rw [hNℓ] at h1
    have h0 : 0 ≤ l2Norm ℓ (errArr (X (k + 1)) (B k)) := Real.sqrt_nonneg _
    calc l2Norm ℓ (errArr (X (k + 1)) (B k)) ^ 2
        ≤ (Real.sqrt (2 * Real.pi) * (3 * (c₀ * ℓ ^ 4))) ^ 2 := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
      _ = 2 * Real.pi * (3 * c₀ * ℓ ^ 4) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hFle : F ≤ 9 * Real.pi * c₀ ^ 2 * T * ℓ ^ 2 := by
    have hE : residualEnergy ℓ ℓ (fun k => errArr (X (k + 1)) (B k)) n₀ ≤
        n₀ * (2 * Real.pi * (3 * c₀ * ℓ ^ 4) ^ 2 / (2 * ℓ)) := by
      unfold residualEnergy
      calc ∑ k ∈ range n₀, l2Norm ℓ (errArr (X (k + 1)) (B k)) ^ 2 / (2 * ℓ)
          ≤ ∑ _k ∈ range n₀, 2 * Real.pi * (3 * c₀ * ℓ ^ 4) ^ 2 / (2 * ℓ) :=
            Finset.sum_le_sum fun k hk => by gcongr; exact hl2 k (mem_range.1 hk)
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e : n₀ * (2 * Real.pi * (3 * c₀ * ℓ ^ 4) ^ 2 / (2 * ℓ)) / ℓ ^ (2 * 1 + 1) =
        9 * Real.pi * c₀ ^ 2 * (n₀ * ℓ) * ℓ ^ 3 := by field_simp; ring
    have hℓ3 : ℓ ^ 3 ≤ ℓ ^ 2 := pow_le_pow_of_le_one hℓpos.le hℓ1 (by norm_num)
    calc F = residualEnergy ℓ ℓ (fun k => errArr (X (k + 1)) (B k)) n₀ / ℓ ^ (2 * 1 + 1) := rfl
      _ ≤ n₀ * (2 * Real.pi * (3 * c₀ * ℓ ^ 4) ^ 2 / (2 * ℓ)) / ℓ ^ (2 * 1 + 1) := by gcongr
      _ = 9 * Real.pi * c₀ ^ 2 * (n₀ * ℓ) * ℓ ^ 3 := e
      _ ≤ 9 * Real.pi * c₀ ^ 2 * T * ℓ ^ 2 := by gcongr
  have hsF : Real.sqrt F ≤ 3 * c₀ * Real.sqrt (Real.pi * T) * ℓ := by
    calc Real.sqrt F ≤ Real.sqrt (9 * Real.pi * c₀ ^ 2 * T * ℓ ^ 2) := Real.sqrt_le_sqrt hFle
      _ = 3 * c₀ * Real.sqrt (Real.pi * T) * ℓ := by
        rw [show 9 * Real.pi * c₀ ^ 2 * T * ℓ ^ 2 = (3 * c₀ * ℓ) ^ 2 * (Real.pi * T) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        ring
  have hℓ2 : ℓ ^ 2 ≤ ℓ := by nlinarith
  have hc1ℓ : c₁ * ℓ ^ 2 ≤ c₁ * ℓ := mul_le_mul_of_nonneg_left hℓ2 hc₁
  simp only [actionKappa]
  rw [← hℓ, ← hF]
  nlinarith

/-- **First clause of (G4) of `thm:main-gowdy-regulator` on the (G3) histories: the
first-variation residual tends to zero.**  For a smooth reference, every smooth local test of the
six fields (lapse and shift varied independently, support in `[t_a, t_b] × 𝕋¹ ⊂ (t₀, t₁) × 𝕋¹`),
every chart/envelope radius, offset cap `c₀` and initial-error constant `c₁`, there are `C, ℓ₀`
such that for `h = ℓ = 2π/N ≤ ℓ₀` and every history realized by split steps in the `C¹_h`
envelope with `charDist(X_{n+1}, B_n) ≤ c₀ h⁴` and initial `C¹_h` error `≤ c₁ h²`, the first
variation of the independent discrete action at the recorded areal-gauge fields obeys
`|δS_h| ≤ C h` (and `δS_* = 0`), on every time window covering the support of the test. -/
theorem action_test_pathwise (sol : GowdySmoothReference t₀ t₁) (h0 : 0 < t₀) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) (Renv : ℝ) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    {φ : Fin 6 → ℝ × ℝ → ℝ} (hφ : ∀ k, ContDiff ℝ ∞ (φ k))
    (hper : ∀ k (p : ℝ × ℝ), φ k (p.1, p.2 + 2 * Real.pi) = φ k p)
    {ta tb : ℝ} (hta : t₀ < ta) (hab : ta ≤ tb) (htb : tb < t₁)
    (hsupp : ∀ k (p : ℝ × ℝ), p.1 ∉ Icc ta tb → φ k p = 0) :
    continuumFirstVariation (arealLift sol) φ t₀ t₁ = 0 ∧
    ∃ C ℓ₀ : ℝ, 0 ≤ C ∧ 0 < ℓ₀ ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ), t₀ ≤ τ₀ → τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁ → τ₀ < ta →
        tb < τ₀ + n₀ * (2 * Real.pi / N) →
      ∀ X A B : ℕ → GridState N,
        (∀ n < n₀, CharStability.IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
          GowdyEnvR 1 t₀ R Renv (2 * Real.pi / N) (X n) (A n) (B n)) →
        (∀ n < n₀, charDist (X (n + 1)) (B n) ≤ c₀ * (2 * Real.pi / N) ^ 4) →
        crNorm 1 (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) ≤
          c₁ * (2 * Real.pi / N) ^ 2 →
        |discreteFirstVariation (2 * Real.pi / N) (2 * Real.pi / N) n₀
            (arealRecord τ₀ (2 * Real.pi / N) X) (testSample φ τ₀ (2 * Real.pi / N) N)| ≤
          C * (2 * Real.pi / N) := by
  obtain ⟨hS0, C, ℓ₀, hC, hℓ₀, hmain⟩ :=
    action_test sol h0 hR Renv hφ hper hta hab htb hsupp
  refine ⟨hS0, ?_⟩
  set T := max (t₁ - t₀) 0 with hT
  have hT0 : 0 ≤ T := le_max_right _ _
  set Cκ := c₁ + 1 + 3 * c₀ * Real.sqrt (Real.pi * T) with hCκ
  have hCκ1 : 1 ≤ Cκ := by
    have : 0 ≤ 3 * c₀ * Real.sqrt (Real.pi * T) := by positivity
    linarith
  refine ⟨C * (Cκ + 1), min ℓ₀ (min 1 (1 / Cκ)), by positivity,
    lt_min hℓ₀ (lt_min one_pos (by positivity)), ?_⟩
  intro N _ hN τ₀ n₀ hτ₀ hn₀ hτa htb' X A B hstep hoff hinit
  set ℓ := 2 * Real.pi / N with hℓ
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hℓpos : 0 < ℓ := by positivity
  have hℓ1 : ℓ ≤ 1 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hℓC : ℓ ≤ 1 / Cκ := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hnT : (n₀ : ℝ) * ℓ ≤ T := (by linarith : (n₀ : ℝ) * ℓ ≤ t₁ - t₀).trans (le_max_left _ _)
  have hκ := actionKappa_le_of_offset_cap sol.toGowdyFrameSolution hc₀ hc₁ hT0 hℓ1 τ₀ n₀ hnT X B
    hoff hinit
  have hκ1 : actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B ≤ 1 := by
    refine hκ.trans ?_
    rw [le_div_iff₀ (by positivity)] at hℓC
    linarith [mul_comm Cκ ℓ]
  have := hmain N (hN.trans (min_le_left _ _)) τ₀ n₀ hτ₀ hn₀ hτa htb' X A B hstep hκ1
  rw [hS0, sub_zero] at this
  refine this.trans ?_
  calc C * (actionKappa sol.toGowdyFrameSolution τ₀ n₀ X B + ℓ) ≤ C * (Cκ * ℓ + ℓ) := by gcongr
    _ = C * (Cκ + 1) * ℓ := by ring

/-! ### Non-vacuity of the test hypotheses -/

/-- A nonzero smooth local test satisfying the hypotheses of `action_test`: the same bump
`s(t - t_a) s(t_b - t)` (`s = Real.smoothTransition`) in all six directions, constant in `θ`. -/
theorem exists_nonzero_local_test {ta tb : ℝ} (hab : ta < tb) :
    ∃ φ : Fin 6 → ℝ × ℝ → ℝ, (∀ k, ContDiff ℝ ∞ (φ k)) ∧
      (∀ k (p : ℝ × ℝ), φ k (p.1, p.2 + 2 * Real.pi) = φ k p) ∧
      (∀ k (p : ℝ × ℝ), p.1 ∉ Icc ta tb → φ k p = 0) ∧ ∀ k, φ k ((ta + tb) / 2, 0) ≠ 0 := by
  refine ⟨fun _ p => Real.smoothTransition (p.1 - ta) * Real.smoothTransition (tb - p.1),
    fun k => ?_, fun k p => rfl, fun k p hp => ?_, fun k => ?_⟩
  · exact ((Real.smoothTransition.contDiff.comp (contDiff_fst.sub contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_fst)))
  · simp only [Set.mem_Icc, not_and_or, not_le] at hp
    show Real.smoothTransition (p.1 - ta) * Real.smoothTransition (tb - p.1) = 0
    rcases hp with h | h
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : tb - p.1 ≤ 0), mul_zero]
  · show Real.smoothTransition ((ta + tb) / 2 - ta) *
      Real.smoothTransition (tb - (ta + tb) / 2) ≠ 0
    exact mul_ne_zero (Real.smoothTransition.pos_of_pos (by linarith)).ne'
      (Real.smoothTransition.pos_of_pos (by linarith)).ne'

/-! ### Successful histories inherit the deterministic estimates -/

open CoordinateCurvatureJet in
/-- **Inheritance of the deterministic estimates by the successful histories**
(`prop:main-safe-access`, with (G3) and (G4) of `thm:main-gowdy-regulator`).  The pathwise
curvature estimate `eq:main-gowdy-full-curvature` and the independent action test are uniform over
every history whose accepted proposals satisfy the offset/solver cap (`charDist(X_{n+1}, B_n) ≤
c₀ h⁴`) in the `C¹_h` envelope with initial `C¹_h` error `≤ c₁ h²` — the deterministic admissible
support shared by all successful histories, whatever the proposal weights: there are `C, ℓ₀` such
that every such history has, on every cell, the readout estimates (metric `O(h²)` in `W^{1,∞}`,
`O(h)` in second derivatives and Riemann tensor, bounded Riemann tensor, Ricci tensor `O(h)`), and
the first variation of the independent discrete action against the fixed smooth local test `φ`
satisfies `|δS_h| ≤ C h` (with `δS_* = 0`). -/
theorem successful_histories_inherit (sol : GowdySmoothReference t₀ t₁) (h0 : 0 < t₀) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) (Renv : ℝ) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    {φ : Fin 6 → ℝ × ℝ → ℝ} (hφ : ∀ k, ContDiff ℝ ∞ (φ k))
    (hper : ∀ k (p : ℝ × ℝ), φ k (p.1, p.2 + 2 * Real.pi) = φ k p)
    {ta tb : ℝ} (hta : t₀ < ta) (hab : ta ≤ tb) (htb : tb < t₁)
    (hsupp : ∀ k (p : ℝ × ℝ), p.1 ∉ Icc ta tb → φ k p = 0) :
    continuumFirstVariation (arealLift sol) φ t₀ t₁ = 0 ∧
    ∃ C ℓ₀ : ℝ, 0 ≤ C ∧ 0 < ℓ₀ ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ) (X A B : ℕ → GridState N), t₀ ≤ τ₀ →
        τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁ →
        (∀ n < n₀, CharStability.IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
          GowdyEnvR 1 t₀ R Renv (2 * Real.pi / N) (X n) (A n) (B n)) →
        (∀ n < n₀, charDist (X (n + 1)) (B n) ≤ c₀ * (2 * Real.pi / N) ^ 4) →
        crNorm 1 (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) ≤
          c₁ * (2 * Real.pi / N) ^ 2 →
        (∀ n < n₀, ∀ (j : ZMod N),
          ∀ x ∈ Icc (τ₀ + n * (2 * Real.pi / N)) (τ₀ + n * (2 * Real.pi / N) + 2 * Real.pi / N),
          ∀ y ∈ Icc (sampleAngle N j) (sampleAngle N j + 2 * Real.pi / N),
            ‖gowdyMetric (stateMap (cellReadout X τ₀ n j) (x, y)) -
                gowdyMetric (stateMap sol.fld (x, y))‖ ≤ C * (2 * Real.pi / N) ^ 2 ∧
            ‖fderiv ℝ (fun z => gowdyMetric (stateMap (cellReadout X τ₀ n j) z)) (x, y) -
                fderiv ℝ (fun z => gowdyMetric (stateMap sol.fld z)) (x, y)‖ ≤
              C * (2 * Real.pi / N) ^ 2 ∧
            ‖fderiv ℝ (fderiv ℝ (fun z => gowdyMetric (stateMap (cellReadout X τ₀ n j) z)))
                  (x, y) -
                fderiv ℝ (fderiv ℝ (fun z => gowdyMetric (stateMap sol.fld z))) (x, y)‖ ≤
              C * (2 * Real.pi / N) ∧
            ‖riemJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y)) -
                riemJet (gowdyJet (stateMap sol.fld) (x, y))‖ ≤ C * (2 * Real.pi / N) ∧
            ‖riemJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y))‖ ≤ C ∧
            ricciJet (gowdyJet (stateMap sol.fld) (x, y)) = 0 ∧
            ‖ricciJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y))‖ ≤
              C * (2 * Real.pi / N)) ∧
        (τ₀ < ta → tb < τ₀ + n₀ * (2 * Real.pi / N) →
          |discreteFirstVariation (2 * Real.pi / N) (2 * Real.pi / N) n₀
              (arealRecord τ₀ (2 * Real.pi / N) X) (testSample φ τ₀ (2 * Real.pi / N) N)| ≤
            C * (2 * Real.pi / N)) := by
  obtain ⟨C₁, ℓ₁, hC₁, hℓ₁, hcurv⟩ := sol.readout_full_curvature_of_envelope h0 hR Renv hc₀ hc₁
  obtain ⟨hS0, C₂, ℓ₂, hC₂, hℓ₂, hact⟩ :=
    action_test_pathwise sol h0 hR Renv hc₀ hc₁ hφ hper hta hab htb hsupp
  refine ⟨hS0, max C₁ C₂, min ℓ₁ ℓ₂, le_max_of_le_left hC₁, lt_min hℓ₁ hℓ₂, ?_⟩
  intro N _ hN τ₀ n₀ X A B hτ₀ hn₀ hstep hoff hinit
  have hℓpos : 0 < 2 * Real.pi / N := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hc := hcurv N (hN.trans (min_le_left _ _)) τ₀ n₀ X A B hτ₀ hn₀ hstep hoff hinit
  have hCC : C₁ ≤ max C₁ C₂ := le_max_left _ _
  refine ⟨fun n hn j x hx y hy => ?_, fun hτa htb' => ?_⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc n hn j x hx y hy
    exact ⟨e1.trans (by gcongr), e2.trans (by gcongr), e3.trans (by gcongr),
      e4.trans (by gcongr), e5.trans hCC, e6, e7.trans (by gcongr)⟩
  · exact (hact N (hN.trans (min_le_right _ _)) τ₀ n₀ hτ₀ hn₀ hτa htb' X A B hstep hoff
      hinit).trans (by gcongr; exact le_max_right _ _)

end

end RenewalGeometry.GowdyStaggered.ActionTest
