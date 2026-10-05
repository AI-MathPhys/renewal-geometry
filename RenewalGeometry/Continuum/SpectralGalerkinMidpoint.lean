/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.ODEAprioriContinuation
import RenewalGeometry.DiscreteAnalysis.CubicHermiteStability

/-!
# Spectral Galerkin and implicit-midpoint discretization of energy-stable evolutions

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` of the
Einstein–Standard-Model action-closure manuscript (`app:generated-dynamics`).  The state space is
a real inner product space `E` (the spectral Galerkin space `Ran P_N ⊂ H^q` with the `H^q` inner
product); the semidiscrete field `G_N = P_N G` is abstract, and the **symmetric `H^q` energy
estimate** of the hyperbolic system enters only through the one-sided bounds
`⟪G w, w⟫ ≤ K (1 + ‖w‖²)` (energy) and `⟪G a - G b, a - b⟫ ≤ K ‖a - b‖²` (difference energy),
with `K` independent of the cutoff, while the bound `M` and Lipschitz constant `L` of `G_N` may
grow with `N` (inverse inequality) and are controlled by the CFL condition.

* `inner_proj_eq`: **the orthogonal projection disappears from the energy pairing**:
  `⟪P g, v⟫ = ⟪g, v⟫` for `v ∈ Ran P`, so the energy hypothesis for `G` gives the one for
  `P G` with the same `K`.
* `midpoint_step_exists_unique`: **existence and uniqueness of the implicit-midpoint step**
  `V = U + τ G((U + V)/2)` by Banach contraction under `τ L < 2` (CFL), in the ball
  `‖V - U‖ ≤ τ M`; `midpoint_step_cfl` is the CFL form `τ (N + 1) ≤ c_*`, `L = C_R (N + 1)`.
* `midpoint_energy_identity`: the **exact discrete energy identity**
  `‖V‖² - ‖U‖² = 2 τ ⟪G(m), m⟫`, `m = (U + V)/2`; `midpoint_energy_step`: with the energy
  hypothesis, `1 + ‖V‖² ≤ e^{4τK} (1 + ‖U‖²)` (`τK ≤ 1/2`).
* `midpoint_recursion`: **the fully discrete recursion exists on `[0, T]`** with
  `1 + ‖U^j‖² ≤ e^{4Kjτ}(1 + ‖U^0‖²)` and `‖U^j‖ ≤ R`, the radius `R` depending only on
  `K`, `T` and the data (not on `M`, `L`, hence not on the cutoff): `eq:generated-uniform`.
* `midpoint_causal`: the **discrete stability estimate** `eq:generated-causal`
  `‖U^n - V^n‖ ≤ e^{2Knτ} (‖U^0 - V^0‖ + 2τ Σ_{j<n} ‖r_j‖)` for two midpoint trajectories with
  forcing difference `r_j`; `midpoint_convergence`: with residuals `‖r_j‖ ≤ Cτ²`, the
  `O(τ²)` rate of `eq:generated-time-rate`.
* Taylor bounds in a normed space (`taylor1_le`, `taylor2_le`) and **`midpoint_consistency`**:
  for a `C³` trajectory, `‖(z(t) + z(t+τ))/2 - z(t+τ/2)‖ ≤ 3M₂τ²/8` and
  `‖z(t+τ) - z(t) - τ z'(t+τ/2)‖ ≤ 7M₃τ³/24` (the local truncation residual is `O(τ²)`).
* The semidiscrete (Galerkin) evolution: `galerkin_energy` (energy estimate along a solution),
  **`galerkin_exists`** (existence on `[0, T]` for a `C¹` field on a finite-dimensional space,
  with `T` depending only on `K`, `R` and the data — the first-exit argument through
  `ODEContinuation.exists_solution_of_apriori`), **`galerkin_compare`** (Galerkin versus exact
  evolution: `‖U_N - P U‖² ≤ gronwallBound(‖U_N(0) - P U(0)‖², 2K + 1, δ², t)` with `δ` the
  projection defect of the field — the mechanism of `eq:generated-Galerkin-rate`).
* Cubic Hermite readout in time (`hermite`, `hermiteD`, `hermiteDD` on the basis of
  `CubicHermiteStability`): nodal values and slopes (`hermite_zero`, `hermiteD_one`, …), the
  readout is `C¹` in time (`hasDerivAt_hermite`, `hasDerivAt_hermiteD`), **stability**
  (`hermite_stability`), **exact-data accuracy** (`hermite_accuracy`: `2M₂τ²`, `2M₃τ²`, `4M₃τ`)
  and the combined **error** `hermite_error` (the mechanism of `eq:generated-Hermite`).
-/

open Set Filter Topology Metric
open scoped RealInnerProductSpace

namespace RenewalGeometry.SpectralGalerkin

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Orthogonal projections and the energy pairing -/

/-- **The orthogonal projection disappears from the energy pairing**: for a symmetric `P` and
`v ∈ Ran P` (`P v = v`), `⟪P g, v⟫ = ⟪g, v⟫`. -/
theorem inner_proj_eq (P : E →L[ℝ] E) (hP : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫) {v : E} (hv : P v = v)
    (g : E) : ⟪P g, v⟫ = ⟪g, v⟫ := by
  rw [hP, hv]

/-- The energy hypothesis transfers from `G` to `P G` on `Ran P` with the same constant. -/
theorem energy_proj (P : E →L[ℝ] E) (hP : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫) {G : E → E} {K : ℝ}
    {v : E} (hv : P v = v) (h : ⟪G v, v⟫ ≤ K * (1 + ‖v‖ ^ 2)) :
    ⟪P (G v), v⟫ ≤ K * (1 + ‖v‖ ^ 2) := by
  rwa [inner_proj_eq P hP hv]

/-! ### Elementary inequalities -/

theorem one_add_le_exp_mul_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    1 + x ≤ Real.exp (4 * x) * (1 - x) := by
  have h1 := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 4 * x)
  have h2 : 0 ≤ 1 - x := by linarith
  have h3 : (1 + 4 * x + (4 * x) ^ 2 / 2) * (1 - x) ≤ Real.exp (4 * x) * (1 - x) :=
    mul_le_mul_of_nonneg_right h1 h2
  nlinarith

theorem norm_midpoint_sq_le (U V : E) :
    ‖(1 / 2 : ℝ) • (U + V)‖ ^ 2 ≤ (‖U‖ ^ 2 + ‖V‖ ^ 2) / 2 := by
  have h1 : ‖(1 / 2 : ℝ) • (U + V)‖ ≤ (‖U‖ + ‖V‖) / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := norm_add_le U V
    linarith
  have h0 := norm_nonneg ((1 / 2 : ℝ) • (U + V))
  have : ‖(1 / 2 : ℝ) • (U + V)‖ ^ 2 ≤ ((‖U‖ + ‖V‖) / 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
  nlinarith [sq_nonneg (‖U‖ - ‖V‖)]

/-! ### Banach contraction on a closed ball -/

omit [InnerProductSpace ℝ E] in
/-- Banach contraction on the closed ball `‖x - c‖ ≤ ρ`. -/
theorem exists_unique_fixedPoint_closedBall [CompleteSpace E] {T : E → E} {c : E} {ρ κ : ℝ}
    (hρ : 0 ≤ ρ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hmaps : ∀ x, ‖x - c‖ ≤ ρ → ‖T x - c‖ ≤ ρ)
    (hlip : ∀ x y, ‖x - c‖ ≤ ρ → ‖y - c‖ ≤ ρ → ‖T x - T y‖ ≤ κ * ‖x - y‖) :
    ∃ x, ‖x - c‖ ≤ ρ ∧ T x = x ∧ ∀ y, ‖y - c‖ ≤ ρ → T y = y → y = x := by
  set s := closedBall c ρ with hsdef
  have hs : ∀ x, x ∈ s ↔ ‖x - c‖ ≤ ρ := fun x => by simp [hsdef, dist_eq_norm]
  have hmaps' : Set.MapsTo T s s := fun x hx => (hs _).2 (hmaps x ((hs x).1 hx))
  have : CompleteSpace s := isClosed_closedBall.completeSpace_coe
  have : Nonempty s := ⟨⟨c, (hs c).2 (by simpa using hρ)⟩⟩
  have hc : ContractingWith ⟨κ, hκ0⟩ (hmaps'.restrict T s s) := by
    refine ⟨by exact_mod_cast hκ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hlip _ _ ((hs _).1 x.2) ((hs _).1 y.2)
  have hfix := ContractingWith.fixedPoint_isFixedPt (f := hmaps'.restrict T s s) hc
  refine ⟨(ContractingWith.fixedPoint _ hc).1, (hs _).1 (ContractingWith.fixedPoint _ hc).2,
    congrArg Subtype.val hfix, fun y hy hTy => ?_⟩
  have := ContractingWith.fixedPoint_unique (f := hmaps'.restrict T s s) hc
    (x := ⟨y, (hs _).2 hy⟩) (Subtype.ext hTy)
  exact congrArg Subtype.val this

/-! ### The implicit midpoint step -/

/-- The midpoint of `U` and `V`. -/
def mid (U V : E) : E := (1 / 2 : ℝ) • (U + V)

/-- **Existence and uniqueness of the implicit-midpoint step** `V = U + τ G((U + V)/2)`: if `G`
is bounded by `M` and `L`-Lipschitz on the ball `‖w‖ ≤ ρ ⊇ {‖w‖ ≤ ‖U‖ + τM}` and `τ L < 2`, the
step map is a contraction of the ball `‖V - U‖ ≤ τ M` and has exactly one fixed point there. -/
theorem midpoint_step_exists_unique [CompleteSpace E] {G : E → E} {τ M L ρ : ℝ} (hτ : 0 ≤ τ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) {U : E}
    (hbound : ∀ w, ‖w‖ ≤ ρ → ‖G w‖ ≤ M)
    (hlip : ∀ w w', ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ → ‖G w - G w'‖ ≤ L * ‖w - w'‖)
    (hρ : ‖U‖ + τ * M ≤ ρ) (hcfl : τ * L < 2) :
    ∃ V, ‖V - U‖ ≤ τ * M ∧ V = U + τ • G (mid U V) ∧
      ∀ V', ‖V' - U‖ ≤ τ * M → V' = U + τ • G (mid U V') → V' = V := by
  have hmid : ∀ V, ‖V - U‖ ≤ τ * M → ‖mid U V‖ ≤ ρ := by
    intro V hV
    have e : mid U V = U + (1 / 2 : ℝ) • (V - U) := by
      unfold mid; rw [smul_add, smul_sub]; module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := mul_nonneg hτ hM
    linarith
  have hmaps : ∀ V, ‖V - U‖ ≤ τ * M → ‖(U + τ • G (mid U V)) - U‖ ≤ τ * M := by
    intro V hV
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
    exact mul_le_mul_of_nonneg_left (hbound _ (hmid V hV)) hτ
  have hlip' : ∀ V V', ‖V - U‖ ≤ τ * M → ‖V' - U‖ ≤ τ * M →
      ‖(U + τ • G (mid U V)) - (U + τ • G (mid U V'))‖ ≤ (τ * L / 2) * ‖V - V'‖ := by
    intro V V' hV hV'
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
    have h1 := hlip _ _ (hmid V hV) (hmid V' hV')
    have e : mid U V - mid U V' = (1 / 2 : ℝ) • (V - V') := by
      unfold mid; rw [← smul_sub]; congr 1; abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1
    calc τ * ‖G (mid U V) - G (mid U V')‖ ≤ τ * (L * (1 / 2 * ‖V - V'‖)) :=
          mul_le_mul_of_nonneg_left h1 hτ
      _ = (τ * L / 2) * ‖V - V'‖ := by ring
  obtain ⟨V, hV, hfix, huniq⟩ := exists_unique_fixedPoint_closedBall
    (T := fun V => U + τ • G (mid U V)) (c := U) (mul_nonneg hτ hM)
    (by positivity) (by linarith) hmaps hlip'
  exact ⟨V, hV, hfix.symm, fun V' hV' h => huniq V' hV' h.symm⟩

/-- The CFL form: `G` is `C_R (N + 1)`-Lipschitz (inverse inequality on `Ran P_N`) and
`τ (N + 1) ≤ c_*` with `c_* C_R < 2`. -/
theorem midpoint_step_cfl [CompleteSpace E] {G : E → E} {τ M CR ρ cstar : ℝ} {N : ℕ}
    (hτ : 0 ≤ τ) (hM : 0 ≤ M) (hCR : 0 ≤ CR) {U : E}
    (hbound : ∀ w, ‖w‖ ≤ ρ → ‖G w‖ ≤ M)
    (hlip : ∀ w w', ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ → ‖G w - G w'‖ ≤ CR * (N + 1) * ‖w - w'‖)
    (hρ : ‖U‖ + τ * M ≤ ρ) (hcfl : τ * (N + 1) ≤ cstar) (hc : cstar * CR < 2) :
    ∃ V, ‖V - U‖ ≤ τ * M ∧ V = U + τ • G (mid U V) ∧
      ∀ V', ‖V' - U‖ ≤ τ * M → V' = U + τ • G (mid U V') → V' = V := by
  refine midpoint_step_exists_unique hτ hM (by positivity) hbound hlip hρ ?_
  calc τ * (CR * (N + 1)) = CR * (τ * (N + 1)) := by ring
    _ ≤ CR * cstar := mul_le_mul_of_nonneg_left hcfl hCR
    _ < 2 := by linarith

/-- **The exact discrete energy identity of the midpoint rule**:
if `V = U + τ G(m)`, `m = (U + V)/2`, then `‖V‖² - ‖U‖² = 2 τ ⟪G(m), m⟫`. -/
theorem midpoint_energy_identity {G : E → E} {τ : ℝ} {U V : E}
    (h : V = U + τ • G (mid U V)) : ‖V‖ ^ 2 - ‖U‖ ^ 2 = 2 * τ * ⟪G (mid U V), mid U V⟫ := by
  have hVU : V - U = τ • G (mid U V) := sub_eq_iff_eq_add'.mpr h
  have e1 : ‖V‖ ^ 2 - ‖U‖ ^ 2 = ⟪V - U, V + U⟫ := by
    rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, real_inner_comm U V]
    ring
  have e2 : V + U = (2 : ℝ) • mid U V := by
    unfold mid; rw [smul_smul]; norm_num; abel
  rw [e1, hVU, e2, inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  ring

/-- **Energy step**: under `⟪G w, w⟫ ≤ K (1 + ‖w‖²)` at the midpoint, `0 ≤ τ`, `0 ≤ K`,
`τ K ≤ 1/2`: `1 + ‖V‖² ≤ e^{4τK} (1 + ‖U‖²)`. -/
theorem midpoint_energy_step {G : E → E} {τ K : ℝ} (hτ : 0 ≤ τ) (hK : 0 ≤ K)
    (hτK : τ * K ≤ 1 / 2) {U V : E} (h : V = U + τ • G (mid U V))
    (hE : ⟪G (mid U V), mid U V⟫ ≤ K * (1 + ‖mid U V‖ ^ 2)) :
    1 + ‖V‖ ^ 2 ≤ Real.exp (4 * (τ * K)) * (1 + ‖U‖ ^ 2) := by
  have hid := midpoint_energy_identity h
  have hm := norm_midpoint_sq_le U V
  set x := τ * K with hx
  have hx0 : 0 ≤ x := mul_nonneg hτ hK
  have h1 : ‖V‖ ^ 2 - ‖U‖ ^ 2 ≤ 2 * τ * (K * (1 + (‖U‖ ^ 2 + ‖V‖ ^ 2) / 2)) := by
    rw [hid]
    have : K * (1 + ‖mid U V‖ ^ 2) ≤ K * (1 + (‖U‖ ^ 2 + ‖V‖ ^ 2) / 2) := by
      unfold mid at hm ⊢; gcongr
    have h2τ : 0 ≤ 2 * τ := by linarith
    exact mul_le_mul_of_nonneg_left (hE.trans this) h2τ
  -- `(1 + ‖V‖²)(1 - x) ≤ (1 + ‖U‖²)(1 + x)`
  have h2 : (1 + ‖V‖ ^ 2) * (1 - x) ≤ (1 + ‖U‖ ^ 2) * (1 + x) := by
    rw [hx]; nlinarith
  have h3 := one_add_le_exp_mul_one_sub hx0 hτK
  have hU := sq_nonneg ‖U‖
  have hV := sq_nonneg ‖V‖
  have h1x : 0 < 1 - x := by linarith
  have h4 : (1 + ‖U‖ ^ 2) * (1 + x) ≤ (1 + ‖U‖ ^ 2) * (Real.exp (4 * x) * (1 - x)) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : (1 + ‖V‖ ^ 2) * (1 - x) ≤ (Real.exp (4 * x) * (1 + ‖U‖ ^ 2)) * (1 - x) := by
    nlinarith
  exact le_of_mul_le_mul_right h5 h1x

/-! ### The fully discrete recursion on a common interval -/

/-- **The midpoint recursion exists on `[0, T]` with a cutoff-uniform bound**
(`eq:generated-uniform`).  On the ball `‖w‖ ≤ 2R` let `G` be bounded by `M`, `L`-Lipschitz, and
satisfy the energy inequality `⟪G w, w⟫ ≤ K (1 + ‖w‖²)`; let `τ M ≤ R`, `τ L < 2` (CFL),
`τ K ≤ 1/2` and `e^{4KT} (1 + ‖U⁰‖²) ≤ 1 + R²`.  Then the recursion
`U^{j+1} = U^j + τ G((U^j + U^{j+1})/2)` (with `U^{j+1}` the unique solution in
`‖U^{j+1} - U^j‖ ≤ τ M`) exists for all `jτ ≤ T`, with `‖U^j‖ ≤ R` and
`1 + ‖U^j‖² ≤ e^{4Kjτ} (1 + ‖U⁰‖²)`.  `R` depends only on `K`, `T` and the data. -/
theorem midpoint_recursion [CompleteSpace E] {G : E → E} {τ M L K R T : ℝ} (hτ : 0 ≤ τ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hbound : ∀ w, ‖w‖ ≤ 2 * R → ‖G w‖ ≤ M)
    (hlip : ∀ w w', ‖w‖ ≤ 2 * R → ‖w'‖ ≤ 2 * R → ‖G w - G w'‖ ≤ L * ‖w - w'‖)
    (henergy : ∀ w, ‖w‖ ≤ 2 * R → ⟪G w, w⟫ ≤ K * (1 + ‖w‖ ^ 2))
    (hτM : τ * M ≤ R) (hcfl : τ * L < 2) (hτK : τ * K ≤ 1 / 2) {U₀ : E}
    (h0 : Real.exp (4 * K * T) * (1 + ‖U₀‖ ^ 2) ≤ 1 + R ^ 2) :
    ∃ U : ℕ → E, U 0 = U₀ ∧ ∀ j : ℕ, (j : ℝ) * τ ≤ T →
      ‖U j‖ ≤ R ∧ 1 + ‖U j‖ ^ 2 ≤ Real.exp (4 * K * (j * τ)) * (1 + ‖U₀‖ ^ 2) ∧
      (((j : ℝ) + 1) * τ ≤ T → U (j + 1) = U j + τ • G (mid (U j) (U (j + 1))) ∧
        ‖U (j + 1) - U j‖ ≤ τ * M ∧
        ∀ V, ‖V - U j‖ ≤ τ * M → V = U j + τ • G (mid (U j) V) → V = U (j + 1)) := by
  classical
  have hstep : ∀ U : E, ‖U‖ ≤ R → ∃ V, ‖V - U‖ ≤ τ * M ∧ V = U + τ • G (mid U V) ∧
      ∀ V', ‖V' - U‖ ≤ τ * M → V' = U + τ • G (mid U V') → V' = V := fun U hU =>
    midpoint_step_exists_unique hτ hM hL hbound hlip (by linarith) hcfl
  set step : E → E := fun U => if h : ‖U‖ ≤ R then (hstep U h).choose else U with hstepdef
  have hstep_spec : ∀ U (h : ‖U‖ ≤ R), ‖step U - U‖ ≤ τ * M ∧
      step U = U + τ • G (mid U (step U)) ∧
      ∀ V', ‖V' - U‖ ≤ τ * M → V' = U + τ • G (mid U V') → V' = step U := by
    intro U h
    have e : step U = (hstep U h).choose := by simp [hstepdef, h]
    rw [e]; exact (hstep U h).choose_spec
  set U : ℕ → E := fun j => step^[j] U₀ with hUdef
  have hUsucc : ∀ j, U (j + 1) = step (U j) := fun j => by
    simp only [hUdef]; rw [Function.iterate_succ_apply']
  have hmid_ball : ∀ U V : E, ‖U‖ ≤ R → ‖V - U‖ ≤ τ * M → ‖mid U V‖ ≤ 2 * R := by
    intro U V hU hV
    have e : mid U V = U + (1 / 2 : ℝ) • (V - U) := by
      unfold mid; rw [smul_add, smul_sub]; module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hexp1 : 1 ≤ 1 + ‖U₀‖ ^ 2 := by have := sq_nonneg ‖U₀‖; linarith
  have key : ∀ j : ℕ, (j : ℝ) * τ ≤ T →
      ‖U j‖ ≤ R ∧ 1 + ‖U j‖ ^ 2 ≤ Real.exp (4 * K * (j * τ)) * (1 + ‖U₀‖ ^ 2) := by
    intro j
    induction j with
    | zero =>
      intro hz
      have hT0 : 0 ≤ T := by simpa using hz
      simp only [hUdef, Function.iterate_zero, id, Nat.cast_zero, zero_mul, mul_zero,
        Real.exp_zero, one_mul, le_refl, and_true]
      have h1 : Real.exp 0 ≤ Real.exp (4 * K * T) := Real.exp_le_exp.mpr (by positivity)
      rw [Real.exp_zero] at h1
      have : 1 + ‖U₀‖ ^ 2 ≤ 1 + R ^ 2 := by nlinarith
      nlinarith [norm_nonneg U₀]
    | succ j ih =>
      intro hj
      have hjT : (j : ℝ) * τ ≤ T := by push_cast at hj; nlinarith
      obtain ⟨hUj, hEj⟩ := ih hjT
      obtain ⟨hd, hfix, -⟩ := hstep_spec (U j) hUj
      rw [← hUsucc] at hd hfix
      have hE := midpoint_energy_step hτ hK (by linarith) hfix
        (henergy _ (hmid_ball _ _ hUj hd))
      have hEj1 : 1 + ‖U (j + 1)‖ ^ 2 ≤ Real.exp (4 * K * (((j + 1 : ℕ) : ℝ) * τ)) *
          (1 + ‖U₀‖ ^ 2) := by
        refine hE.trans ?_
        calc Real.exp (4 * (τ * K)) * (1 + ‖U j‖ ^ 2)
            ≤ Real.exp (4 * (τ * K)) * (Real.exp (4 * K * (j * τ)) * (1 + ‖U₀‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left hEj (Real.exp_pos _).le
          _ = Real.exp (4 * K * (((j + 1 : ℕ) : ℝ) * τ)) * (1 + ‖U₀‖ ^ 2) := by
              rw [← mul_assoc, ← Real.exp_add]; push_cast; ring_nf
      refine ⟨?_, hEj1⟩
      have h2 : Real.exp (4 * K * (((j + 1 : ℕ) : ℝ) * τ)) ≤ Real.exp (4 * K * T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hj (by positivity))
      have h3 : 1 + ‖U (j + 1)‖ ^ 2 ≤ 1 + R ^ 2 := hEj1.trans
        ((mul_le_mul_of_nonneg_right h2 (by linarith)).trans h0)
      have : ‖U (j + 1)‖ ^ 2 ≤ R ^ 2 := by linarith
      nlinarith [norm_nonneg (U (j + 1))]
  refine ⟨U, rfl, fun j hj => ⟨(key j hj).1, (key j hj).2, fun hj1 => ?_⟩⟩
  obtain ⟨hd, hfix, huniq⟩ := hstep_spec (U j) (key j hj).1
  rw [← hUsucc] at hd hfix huniq
  exact ⟨hfix, hd, huniq⟩

/-! ### Discrete stability (`eq:generated-causal`) -/

/-- One step of the discrete stability estimate. -/
theorem midpoint_causal_step {G : E → E} {τ K : ℝ} (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hτK : τ * K ≤ 1)
    {U U' V V' r : E} (hU : U' = U + τ • G (mid U U'))
    (hV : V' = V + τ • (G (mid V V') + r))
    (hmono : ⟪G (mid U U') - G (mid V V'), mid U U' - mid V V'⟫ ≤
      K * ‖mid U U' - mid V V'‖ ^ 2) :
    ‖U' - V'‖ ≤ Real.exp (2 * (τ * K)) * ‖U - V‖ + 2 * τ * ‖r‖ := by
  set a := ‖U - V‖
  set b := ‖U' - V'‖
  set g := G (mid U U') - G (mid V V') - r with hg
  have he : U' - V' = (U - V) + τ • g := by
    rw [hg, smul_sub, smul_sub]
    conv_lhs => rw [hU, hV]
    rw [smul_add]; abel
  have hme : mid U U' - mid V V' = mid (U - V) (U' - V') := by
    unfold mid; rw [← smul_sub]; congr 1; abel
  have hid := midpoint_energy_identity (G := fun _ => g) (τ := τ) (U := U - V) (V := U' - V')
    (by simpa using he)
  rw [← hme] at hid
  -- `⟪g, mₑ⟫ ≤ K ‖mₑ‖² + ‖r‖ ‖mₑ‖`
  have hgm : ⟪g, mid U U' - mid V V'⟫ ≤
      K * ‖mid U U' - mid V V'‖ ^ 2 + ‖r‖ * ‖mid U U' - mid V V'‖ := by
    rw [hg, inner_sub_left]
    have := real_inner_le_norm r (mid U U' - mid V V')
    have h2 : -⟪r, mid U U' - mid V V'⟫ ≤ ‖r‖ * ‖mid U U' - mid V V'‖ := by
      have := abs_real_inner_le_norm r (mid U U' - mid V V')
      linarith [neg_abs_le ⟪r, mid U U' - mid V V'⟫]
    linarith
  have hmn : ‖mid U U' - mid V V'‖ ≤ (a + b) / 2 := by
    rw [hme]; unfold mid
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := norm_add_le (U - V) (U' - V'); linarith
  have ha := norm_nonneg (U - V)
  have hb := norm_nonneg (U' - V')
  have hr := norm_nonneg r
  have hm0 := norm_nonneg (mid U U' - mid V V')
  -- `b² - a² ≤ 2τ(K ((a+b)/2)² + ‖r‖ (a+b)/2)`
  have hsq : b ^ 2 - a ^ 2 ≤ 2 * τ * (K * ((a + b) / 2) ^ 2 + ‖r‖ * ((a + b) / 2)) := by
    rw [hid]
    have h1 : K * ‖mid U U' - mid V V'‖ ^ 2 ≤ K * ((a + b) / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 hmn 2) hK
    have h2 : ‖r‖ * ‖mid U U' - mid V V'‖ ≤ ‖r‖ * ((a + b) / 2) :=
      mul_le_mul_of_nonneg_left hmn hr
    exact mul_le_mul_of_nonneg_left (hgm.trans (add_le_add h1 h2)) (by linarith)
  set x := τ * K / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by linarith
  -- `b (1 - x) ≤ a (1 + x) + τ ‖r‖`
  have hlin : b * (1 - x) ≤ a * (1 + x) + τ * ‖r‖ := by
    rcases (add_nonneg ha hb).lt_or_eq with hpos | hzero
    · have : (b - a) * (a + b) ≤ (x * (a + b) + τ * ‖r‖) * (a + b) := by
        have : (b - a) * (a + b) = b ^ 2 - a ^ 2 := by ring
        rw [this]
        refine hsq.trans (le_of_eq ?_)
        rw [hx]; ring
      have := le_of_mul_le_mul_right this hpos
      nlinarith
    · have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      rw [ha0, hb0]; simp only [zero_mul, zero_add]; exact mul_nonneg hτ hr
  have h3 := one_add_le_exp_mul_one_sub hx0 hx1
  have h1x : 0 < 1 - x := by linarith
  have e4 : Real.exp (4 * x) = Real.exp (2 * (τ * K)) := by rw [hx]; ring_nf
  rw [e4] at h3
  have hexp := Real.exp_pos (2 * (τ * K))
  -- conclude
  have h5 : b * (1 - x) ≤ (Real.exp (2 * (τ * K)) * a + 2 * τ * ‖r‖) * (1 - x) := by
    have h6 : a * (1 + x) ≤ a * (Real.exp (2 * (τ * K)) * (1 - x)) :=
      mul_le_mul_of_nonneg_left h3 ha
    have h7 : τ * ‖r‖ ≤ 2 * τ * ‖r‖ * (1 - x) := by
      have : 0 ≤ τ * ‖r‖ := mul_nonneg hτ hr
      nlinarith
    nlinarith
  exact le_of_mul_le_mul_right h5 h1x

/-- **Discrete stability of the midpoint recursion** (`eq:generated-causal`): for two midpoint
trajectories `U^{j+1} = U^j + τ G(m_U^j)`, `V^{j+1} = V^j + τ (G(m_V^j) + r_j)` whose midpoints
satisfy the difference energy inequality `⟪G a - G b, a - b⟫ ≤ K ‖a - b‖²`,
`‖U^n - V^n‖ ≤ e^{2Knτ} (‖U^0 - V^0‖ + 2τ Σ_{j<n} ‖r_j‖)` (`τ K ≤ 1`). -/
theorem midpoint_causal {G : E → E} {τ K : ℝ} (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hτK : τ * K ≤ 1)
    {U V r : ℕ → E} (n : ℕ)
    (hU : ∀ j < n, U (j + 1) = U j + τ • G (mid (U j) (U (j + 1))))
    (hV : ∀ j < n, V (j + 1) = V j + τ • (G (mid (V j) (V (j + 1))) + r j))
    (hmono : ∀ j < n, ⟪G (mid (U j) (U (j + 1))) - G (mid (V j) (V (j + 1))),
      mid (U j) (U (j + 1)) - mid (V j) (V (j + 1))⟫ ≤
        K * ‖mid (U j) (U (j + 1)) - mid (V j) (V (j + 1))‖ ^ 2) :
    ‖U n - V n‖ ≤ Real.exp (2 * K * (n * τ)) *
      (‖U 0 - V 0‖ + 2 * τ * ∑ j ∈ Finset.range n, ‖r j‖) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hU j (by omega)) (fun j hj => hV j (by omega))
      (fun j hj => hmono j (by omega))
    have hs := midpoint_causal_step hτ hK hτK (hU n (by omega)) (hV n (by omega))
      (hmono n (by omega))
    have hS : 0 ≤ ∑ j ∈ Finset.range n, ‖r j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hr := norm_nonneg (r n)
    have he1 : 1 ≤ Real.exp (2 * K * (((n + 1 : ℕ) : ℝ) * τ)) :=
      Real.one_le_exp (by positivity)
    rw [Finset.sum_range_succ]
    calc ‖U (n + 1) - V (n + 1)‖ ≤ Real.exp (2 * (τ * K)) * ‖U n - V n‖ + 2 * τ * ‖r n‖ := hs
      _ ≤ Real.exp (2 * (τ * K)) * (Real.exp (2 * K * (n * τ)) *
            (‖U 0 - V 0‖ + 2 * τ * ∑ j ∈ Finset.range n, ‖r j‖)) + 2 * τ * ‖r n‖ := by
          gcongr
      _ = Real.exp (2 * K * (((n + 1 : ℕ) : ℝ) * τ)) *
            (‖U 0 - V 0‖ + 2 * τ * ∑ j ∈ Finset.range n, ‖r j‖) + 2 * τ * ‖r n‖ := by
          rw [← mul_assoc, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (2 * K * (((n + 1 : ℕ) : ℝ) * τ)) *
            (‖U 0 - V 0‖ + 2 * τ * ∑ j ∈ Finset.range n, ‖r j‖) +
            Real.exp (2 * K * (((n + 1 : ℕ) : ℝ) * τ)) * (2 * τ * ‖r n‖) := by
          have : 2 * τ * ‖r n‖ ≤ Real.exp (2 * K * (((n + 1 : ℕ) : ℝ) * τ)) * (2 * τ * ‖r n‖) :=
            le_mul_of_one_le_left (by positivity) he1
          linarith
      _ = _ := by ring

/-- **Convergence of the midpoint recursion** (first half of `eq:generated-time-rate`): if a
reference trajectory `V^j` satisfies the midpoint relation up to residuals `‖r_j‖ ≤ C τ²` and the
difference energy inequality holds at the midpoints, then
`‖U^n - V^n‖ ≤ e^{2Knτ} (‖U^0 - V^0‖ + 2 C (nτ) τ²)`. -/
theorem midpoint_convergence {G : E → E} {τ K C : ℝ} (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hτK : τ * K ≤ 1)
    {U V r : ℕ → E} (n : ℕ)
    (hU : ∀ j < n, U (j + 1) = U j + τ • G (mid (U j) (U (j + 1))))
    (hV : ∀ j < n, V (j + 1) = V j + τ • (G (mid (V j) (V (j + 1))) + r j))
    (hmono : ∀ j < n, ⟪G (mid (U j) (U (j + 1))) - G (mid (V j) (V (j + 1))),
      mid (U j) (U (j + 1)) - mid (V j) (V (j + 1))⟫ ≤
        K * ‖mid (U j) (U (j + 1)) - mid (V j) (V (j + 1))‖ ^ 2)
    (hr : ∀ j < n, ‖r j‖ ≤ C * τ ^ 2) :
    ‖U n - V n‖ ≤ Real.exp (2 * K * (n * τ)) * (‖U 0 - V 0‖ + 2 * C * (n * τ) * τ ^ 2) := by
  refine (midpoint_causal hτ hK hτK n hU hV hmono).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hs : ∑ j ∈ Finset.range n, ‖r j‖ ≤ n * (C * τ ^ 2) := by
    have := Finset.sum_le_sum fun j (hj : j ∈ Finset.range n) => hr j (Finset.mem_range.mp hj)
    simpa using this
  have : 2 * τ * ∑ j ∈ Finset.range n, ‖r j‖ ≤ 2 * τ * (n * (C * τ ^ 2)) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  nlinarith

end

/-! ### Taylor estimates in a normed space and the midpoint consistency -/

section Taylor

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_shift {z z' : ℝ → F} {a b t s : ℝ} (hz : ∀ x ∈ Icc a b, HasDerivAt z (z' x) x)
    (hts : t + s ∈ Icc a b) : HasDerivAt (fun s => z (t + s)) (z' (t + s)) s :=
  HasDerivAt.comp_const_add t s (hz (t + s) hts)

/-- **First-order Taylor bound**: `‖z(t+h) - z(t) - h z'(t)‖ ≤ M₂ h² / 2` when `‖z''‖ ≤ M₂`
on `[a, b] ∋ t, t + h`, `h ≥ 0`. -/
theorem taylor1_le {z z' z'' : ℝ → F} {a b M₂ : ℝ} (hz : ∀ x ∈ Icc a b, HasDerivAt z (z' x) x)
    (hz' : ∀ x ∈ Icc a b, HasDerivAt z' (z'' x) x) (hM : ∀ x ∈ Icc a b, ‖z'' x‖ ≤ M₂)
    {t h : ℝ} (ht : a ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ b) :
    ‖z (t + h) - z t - h • z' t‖ ≤ M₂ * h ^ 2 / 2 := by
  have hmem : ∀ s ∈ Icc (0 : ℝ) h, t + s ∈ Icc a b := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- `‖z'(t+s) - z'(t)‖ ≤ M₂ s`
  have hd : ∀ s ∈ Icc (0 : ℝ) h, ‖z' (t + s) - z' t‖ ≤ M₂ * s := by
    intro s hs
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := z') (f' := z'') (a := t) (b := t + s)
      (C := M₂) (fun x hx => (hz' x ⟨by linarith [hx.1], by linarith [hx.2, hs.2]⟩).hasDerivWithinAt)
      (fun x hx => hM x ⟨by linarith [hx.1], by linarith [hx.2, hs.2]⟩) (t + s)
      ⟨by linarith [hs.1], le_rfl⟩
    simpa using this
  set f : ℝ → F := fun s => z (t + s) - z t - s • z' t with hf
  have hfd : ∀ s ∈ Icc (0 : ℝ) h, HasDerivAt f (z' (t + s) - z' t) s := by
    intro s hs
    have h1 := hasDerivAt_shift hz (hmem s hs)
    have h2 := (hasDerivAt_id s).smul_const (z' t)
    simp only [id, one_smul] at h2
    exact (h1.sub_const (z t)).sub h2
  have hB : ∀ x, HasDerivAt (fun s => M₂ * s ^ 2 / 2) (M₂ * x) x := by
    intro x
    have h := ((hasDerivAt_pow 2 x).const_mul M₂).div_const 2
    have e : M₂ * ((2 : ℕ) * x ^ (2 - 1)) / 2 = M₂ * x := by
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring
    rw [e] at h; exact h
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := f) (a := 0) (b := h)
    (fun s hs => (hfd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hfd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by simp [hf]) hB (fun s hs => hd s (Ico_subset_Icc_self hs)) ⟨hh, le_rfl⟩
  simpa [hf] using key

/-- **Second-order Taylor bound**: `‖z(t+h) - z(t) - h z'(t) - (h²/2) z''(t)‖ ≤ M₃ h³ / 6`. -/
theorem taylor2_le {z z' z'' z''' : ℝ → F} {a b M₃ : ℝ}
    (hz : ∀ x ∈ Icc a b, HasDerivAt z (z' x) x) (hz' : ∀ x ∈ Icc a b, HasDerivAt z' (z'' x) x)
    (hz'' : ∀ x ∈ Icc a b, HasDerivAt z'' (z''' x) x) (hM : ∀ x ∈ Icc a b, ‖z''' x‖ ≤ M₃)
    {t h : ℝ} (ht : a ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ b) :
    ‖z (t + h) - z t - h • z' t - (h ^ 2 / 2) • z'' t‖ ≤ M₃ * h ^ 3 / 6 := by
  have hmem : ∀ s ∈ Icc (0 : ℝ) h, t + s ∈ Icc a b := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hd : ∀ s ∈ Icc (0 : ℝ) h, ‖z' (t + s) - z' t - s • z'' t‖ ≤ M₃ * s ^ 2 / 2 :=
    fun s hs => taylor1_le hz' hz'' hM ht hs.1 (by linarith [hs.2])
  set f : ℝ → F := fun s => z (t + s) - z t - s • z' t - (s ^ 2 / 2) • z'' t with hf
  have hfd : ∀ s ∈ Icc (0 : ℝ) h, HasDerivAt f (z' (t + s) - z' t - s • z'' t) s := by
    intro s hs
    have h1 := hasDerivAt_shift hz (hmem s hs)
    have h2 := (hasDerivAt_id s).smul_const (z' t)
    simp only [id, one_smul] at h2
    have h3 := ((hasDerivAt_pow 2 s).div_const 2).smul_const (z'' t)
    have e : ((2 : ℕ) * s ^ (2 - 1) / 2 : ℝ) = s := by norm_num
    rw [e] at h3
    exact ((h1.sub_const (z t)).sub h2).sub h3
  have hB : ∀ x, HasDerivAt (fun s => M₃ * s ^ 3 / 6) (M₃ * x ^ 2 / 2) x := by
    intro x
    have h := ((hasDerivAt_pow 3 x).const_mul M₃).div_const 6
    have e : M₃ * ((3 : ℕ) * x ^ (3 - 1)) / 6 = M₃ * x ^ 2 / 2 := by
      rw [show (3 : ℕ) - 1 = 2 from rfl]; push_cast; ring
    rw [e] at h; exact h
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := f) (a := 0) (b := h)
    (fun s hs => (hfd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hfd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by simp [hf]) hB (fun s hs => hd s (Ico_subset_Icc_self hs)) ⟨hh, le_rfl⟩
  simpa [hf] using key

/-- **Consistency of the midpoint rule** for a `C³` trajectory on `[a, b] ∋ t, t + τ`:
* `‖(z(t) + z(t+τ))/2 - z(t + τ/2)‖ ≤ 3 M₂ τ² / 8`;
* `‖z(t+τ) - z(t) - τ z'(t + τ/2)‖ ≤ 7 M₃ τ³ / 24`. -/
theorem midpoint_consistency {z z' z'' z''' : ℝ → F} {a b M₂ M₃ : ℝ}
    (hz : ∀ x ∈ Icc a b, HasDerivAt z (z' x) x) (hz' : ∀ x ∈ Icc a b, HasDerivAt z' (z'' x) x)
    (hz'' : ∀ x ∈ Icc a b, HasDerivAt z'' (z''' x) x) (hM₂ : ∀ x ∈ Icc a b, ‖z'' x‖ ≤ M₂)
    (hM₃ : ∀ x ∈ Icc a b, ‖z''' x‖ ≤ M₃) {t τ : ℝ} (ht : a ≤ t) (hτ : 0 ≤ τ) (htτ : t + τ ≤ b) :
    ‖(1 / 2 : ℝ) • (z t + z (t + τ)) - z (t + τ / 2)‖ ≤ 3 * M₂ * τ ^ 2 / 8 ∧
      ‖z (t + τ) - z t - τ • z' (t + τ / 2)‖ ≤ 7 * M₃ * τ ^ 3 / 24 := by
  constructor
  · have h1 := taylor1_le hz hz' hM₂ ht hτ htτ
    have h2 := taylor1_le hz hz' hM₂ ht (by linarith : 0 ≤ τ / 2) (by linarith)
    have e : (1 / 2 : ℝ) • (z t + z (t + τ)) - z (t + τ / 2) =
        (1 / 2 : ℝ) • (z (t + τ) - z t - τ • z' t) - (z (t + τ / 2) - z t - (τ / 2) • z' t) := by
      rw [smul_sub, smul_sub, smul_add, smul_smul]; module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith
  · have h1 := taylor2_le hz hz' hz'' hM₃ ht hτ htτ
    have h2 := taylor1_le hz' hz'' hM₃ ht (by linarith : 0 ≤ τ / 2) (by linarith)
    have e : z (t + τ) - z t - τ • z' (t + τ / 2) =
        (z (t + τ) - z t - τ • z' t - (τ ^ 2 / 2) • z'' t) -
          τ • (z' (t + τ / 2) - z' t - (τ / 2) • z'' t) := by
      rw [smul_sub, smul_sub, smul_smul]; module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
    have : τ * ‖z' (t + τ / 2) - z' t - (τ / 2) • z'' t‖ ≤ τ * (M₃ * (τ / 2) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left h2 hτ
    nlinarith

end Taylor

/-! ### The semidiscrete (Galerkin) evolution -/

section Galerkin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scalar Grönwall on `[0, T]` from one-sided derivatives. -/
theorem le_gronwall_scalar {f f' : ℝ → ℝ} {K ε T : ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hf' : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (hb : ∀ t ∈ Ico 0 T, f' t ≤ K * f t + ε) :
    ∀ t ∈ Icc 0 T, f t ≤ gronwallBound (f 0) K ε t := by
  intro t ht
  have := le_gronwallBound_of_liminf_deriv_right_le hf
    (fun x hx r hr => ((hf' x hx).liminf_right_slope_le hr).mono fun z hz => by
      simpa [slope, smul_eq_mul, vsub_eq_sub] using hz) le_rfl hb t ht
  simpa using this

/-- **Energy estimate for the semidiscrete system** `γ' = G(γ)` on `[0, T]`: under the energy
inequality `⟪G γ, γ⟫ ≤ K (1 + ‖γ‖²)` along the solution,
`1 + ‖γ(t)‖² ≤ e^{2Kt} (1 + ‖γ(0)‖²)`. -/
theorem galerkin_energy {G : E → E} {K T : ℝ} {γ : ℝ → E}
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (G (γ t)) (Icc 0 T) t)
    (hE : ∀ t ∈ Icc 0 T, ⟪G (γ t), γ t⟫ ≤ K * (1 + ‖γ t‖ ^ 2)) :
    ∀ t ∈ Icc 0 T, 1 + ‖γ t‖ ^ 2 ≤ Real.exp (2 * K * t) * (1 + ‖γ 0‖ ^ 2) := by
  have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => 1 + ‖γ s‖ ^ 2)
      (2 * ⟪γ t, G (γ t)⟫) (Icc 0 T) t := fun t ht => ((hγ t ht).norm_sq).const_add 1
  have hc : ContinuousOn (fun s => 1 + ‖γ s‖ ^ 2) (Icc 0 T) :=
    fun t ht => (hd t ht).continuousWithinAt
  have key := le_gronwall_scalar (f := fun s => 1 + ‖γ s‖ ^ 2) (K := 2 * K) (ε := 0) hc
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => by
      have := hE t (Ico_subset_Icc_self ht)
      rw [real_inner_comm]; linarith)
  intro t ht
  have := key t ht
  rw [gronwallBound_ε0] at this
  simpa [mul_comm] using this

/-- **Existence of the semidiscrete (Galerkin) solution on a cutoff-uniform interval.**  Let `E`
be finite dimensional (the range of `P_N`), `G : E → E` of class `C¹` (the projected field
`P_N G`), satisfying the energy inequality `⟪G w, w⟫ ≤ K (1 + ‖w‖²)` on the ball `‖w‖ < 2R`, and
let `e^{2KT} (1 + ‖U₀‖²) ≤ 1 + R²`, `R > 0`.  Then the ODE `γ' = G(γ)`, `γ(0) = U₀` has a solution
on `[0, T]` with `‖γ(t)‖ ≤ R` and `1 + ‖γ(t)‖² ≤ e^{2Kt}(1 + ‖U₀‖²)`.  The interval depends only
on `K`, `R` and the data, not on the `C¹` size of `G` (first-exit argument). -/
theorem galerkin_exists [FiniteDimensional ℝ E] {G : E → E} (hG : ContDiff ℝ 1 G)
    {K R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (henergy : ∀ w, ‖w‖ < 2 * R → ⟪G w, w⟫ ≤ K * (1 + ‖w‖ ^ 2)) {U₀ : E}
    (h0 : Real.exp (2 * K * T) * (1 + ‖U₀‖ ^ 2) ≤ 1 + R ^ 2) (hK : 0 ≤ K) :
    ∃ γ : ℝ → E, γ 0 = U₀ ∧ ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (G (γ t)) (Icc 0 T) t ∧
      ‖γ t‖ ≤ R ∧ 1 + ‖γ t‖ ^ 2 ≤ Real.exp (2 * K * t) * (1 + ‖U₀‖ ^ 2) := by
  set O : Set (ℝ × E) := univ ×ˢ ball (0 : E) (2 * R) with hO
  set Kc : Set (ℝ × E) := Icc 0 T ×ˢ closedBall (0 : E) R with hKc
  have hOopen : IsOpen O := isOpen_univ.prod isOpen_ball
  have hKcomp : IsCompact Kc := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKO : Kc ⊆ O := by
    rintro ⟨t, x⟩ ⟨-, hx⟩
    refine ⟨mem_univ _, ?_⟩
    simp only [mem_closedBall, dist_zero_right] at hx
    simp only [mem_ball, dist_zero_right]; linarith
  have hf : ContDiffOn ℝ 1 (Function.uncurry fun (_ : ℝ) (x : E) => G x) O :=
    (hG.comp contDiff_snd).contDiffOn
  have hU0 : ‖U₀‖ ≤ R := by
    have h1 : 1 ≤ Real.exp (2 * K * T) := Real.one_le_exp (by positivity)
    have : 1 + ‖U₀‖ ^ 2 ≤ 1 + R ^ 2 := by
      have := sq_nonneg ‖U₀‖; nlinarith
    nlinarith [norm_nonneg U₀]
  have hx0 : ((0 : ℝ), U₀) ∈ Kc := ⟨⟨le_rfl, hT⟩, by simpa using hU0⟩
  have hap : ∀ T' ∈ Icc 0 T, ∀ γ : ℝ → E, γ 0 = U₀ → (∀ t ∈ Icc 0 T', (t, γ t) ∈ O) →
      (∀ t ∈ Icc 0 T', HasDerivWithinAt γ (G (γ t)) (Icc 0 T') t) →
      ∀ t ∈ Icc 0 T', (t, γ t) ∈ Kc := by
    intro T' hT' γ hγ0 hγO hγ t ht
    have hE : ∀ s ∈ Icc 0 T', ⟪G (γ s), γ s⟫ ≤ K * (1 + ‖γ s‖ ^ 2) := by
      intro s hs
      have := (hγO s hs).2
      simp only [mem_ball, dist_zero_right] at this
      exact henergy _ this
    have hb := galerkin_energy hγ hE t ht
    rw [hγ0] at hb
    refine ⟨⟨ht.1, ht.2.trans hT'.2⟩, ?_⟩
    simp only [mem_closedBall, dist_zero_right]
    have h2 : Real.exp (2 * K * t) ≤ Real.exp (2 * K * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (ht.2.trans hT'.2) (by positivity))
    have h3 : 1 + ‖γ t‖ ^ 2 ≤ 1 + R ^ 2 := hb.trans
      ((mul_le_mul_of_nonneg_right h2 (by positivity)).trans h0)
    nlinarith [norm_nonneg (γ t)]
  obtain ⟨γ, hγ0, hγ⟩ := ODEContinuation.exists_solution_of_apriori hOopen hf hKcomp hKO hx0 hT hap
  refine ⟨γ, hγ0, fun t ht => ⟨(hγ t ht).1, ?_, ?_⟩⟩
  · have := (hγ t ht).2.2
    simpa using this
  · have hE : ∀ s ∈ Icc 0 T, ⟪G (γ s), γ s⟫ ≤ K * (1 + ‖γ s‖ ^ 2) := by
      intro s hs
      have := (hγ s hs).2.2
      simp only [mem_closedBall, dist_zero_right] at this
      exact henergy _ (by linarith)
    have := galerkin_energy (fun s hs => (hγ s hs).1) hE t ht
    rwa [hγ0] at this

/-- **Galerkin versus exact evolution** (the mechanism of `eq:generated-Galerkin-rate`): let
`U' = G(U)` (exact) and `U_N' = P G(U_N)` with `U_N ∈ Ran P`, `P` symmetric.  If
`⟪G(U_N) - G(P U), U_N - P U⟫ ≤ K ‖U_N - P U‖²` (difference energy) and
`‖G(P U) - G(U)‖ ≤ δ` (projection defect), then
`‖U_N(t) - P U(t)‖² ≤ gronwallBound (‖U_N(0) - P U(0)‖²) (2K + 1) δ² t`. -/
theorem galerkin_compare (P : E →L[ℝ] E) (hP : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫) {G : E → E}
    {K δ T : ℝ} {U UN : ℝ → E}
    (hU : ∀ t ∈ Icc 0 T, HasDerivWithinAt U (G (U t)) (Icc 0 T) t)
    (hUN : ∀ t ∈ Icc 0 T, HasDerivWithinAt UN (P (G (UN t))) (Icc 0 T) t)
    (hran : ∀ t ∈ Icc 0 T, P (UN t) = UN t) (hPP : ∀ x, P (P x) = P x)
    (hmono : ∀ t ∈ Icc 0 T, ⟪G (UN t) - G (P (U t)), UN t - P (U t)⟫ ≤ K * ‖UN t - P (U t)‖ ^ 2)
    (hdef : ∀ t ∈ Icc 0 T, ‖G (P (U t)) - G (U t)‖ ≤ δ) :
    ∀ t ∈ Icc 0 T, ‖UN t - P (U t)‖ ^ 2 ≤
      gronwallBound (‖UN 0 - P (U 0)‖ ^ 2) (2 * K + 1) (δ ^ 2) t := by
  set e : ℝ → E := fun t => UN t - P (U t) with he
  have hed : ∀ t ∈ Icc 0 T, HasDerivWithinAt e (P (G (UN t)) - P (G (U t))) (Icc 0 T) t :=
    fun t ht => (hUN t ht).sub (P.hasFDerivAt.comp_hasDerivWithinAt t (hU t ht))
  have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => ‖e s‖ ^ 2)
      (2 * ⟪e t, P (G (UN t)) - P (G (U t))⟫) (Icc 0 T) t := fun t ht => (hed t ht).norm_sq
  have hc : ContinuousOn (fun s => ‖e s‖ ^ 2) (Icc 0 T) :=
    fun t ht => (hd t ht).continuousWithinAt
  have hPe : ∀ t ∈ Icc 0 T, P (e t) = e t := by
    intro t ht; simp only [he, map_sub, hran t ht, hPP]
  have key := le_gronwall_scalar (f := fun s => ‖e s‖ ^ 2) (K := 2 * K + 1) (ε := δ ^ 2) hc
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      have e1 : ⟪e t, P (G (UN t)) - P (G (U t))⟫ = ⟪G (UN t) - G (U t), e t⟫ := by
        rw [← map_sub, real_inner_comm, inner_proj_eq P hP (hPe t ht')]
      have e2 : G (UN t) - G (U t) = (G (UN t) - G (P (U t))) + (G (P (U t)) - G (U t)) := by
        abel
      rw [e1, e2, inner_add_left]
      have h1 := hmono t ht'
      have h2 : ⟪G (P (U t)) - G (U t), e t⟫ ≤ δ * ‖e t‖ :=
        (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hdef t ht') (norm_nonneg _))
      have h3 : 2 * (δ * ‖e t‖) ≤ ‖e t‖ ^ 2 + δ ^ 2 := by nlinarith [sq_nonneg (‖e t‖ - δ)]
      simp only [he] at h1 h2 h3 ⊢
      nlinarith)
  intro t ht
  exact key t ht

end Galerkin

/-! ### Cubic Hermite reconstruction in time -/

section Hermite

open CubicHermite

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The cubic Hermite interpolant on a time cell of length `τ`, in the cell coordinate
`θ = (t - t_j)/τ ∈ [0, 1]`, from nodal values `U₀, U₁` and nodal slopes `V₀, V₁`. -/
noncomputable def hermite (τ : ℝ) (U₀ U₁ V₀ V₁ : F) (θ : ℝ) : F :=
  basisH 0 θ • U₀ + basisH 1 θ • U₁ + (τ * basisG 0 θ) • V₀ + (τ * basisG 1 θ) • V₁

/-- Its time derivative (`∂_t = τ⁻¹ ∂_θ`). -/
noncomputable def hermiteD (τ : ℝ) (U₀ U₁ V₀ V₁ : F) (θ : ℝ) : F :=
  τ⁻¹ • (basisHD 0 θ • U₀ + basisHD 1 θ • U₁) + basisGD 0 θ • V₀ + basisGD 1 θ • V₁

/-- Its second time derivative. -/
noncomputable def hermiteDD (τ : ℝ) (U₀ U₁ V₀ V₁ : F) (θ : ℝ) : F :=
  (τ⁻¹ ^ 2) • (basisHDD 0 θ • U₀ + basisHDD 1 θ • U₁) +
    τ⁻¹ • (basisGDD 0 θ • V₀ + basisGDD 1 θ • V₁)

theorem hermite_zero (τ : ℝ) (U₀ U₁ V₀ V₁ : F) : hermite τ U₀ U₁ V₀ V₁ 0 = U₀ := by
  obtain ⟨h1, -, h3, -, h5, -, h7, -⟩ := basis_nodal
  simp [hermite, h1, h3, h5, h7]

theorem hermite_one (τ : ℝ) (U₀ U₁ V₀ V₁ : F) : hermite τ U₀ U₁ V₀ V₁ 1 = U₁ := by
  obtain ⟨-, h2, -, h4, -, h6, -, h8, -⟩ := basis_nodal
  simp [hermite, h2, h4, h6, h8]

theorem hermiteD_zero (τ : ℝ) (U₀ U₁ V₀ V₁ : F) : hermiteD τ U₀ U₁ V₀ V₁ 0 = V₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -, h11, -, h13, -, h15, -⟩ := basis_nodal
  simp [hermiteD, h9, h11, h13, h15]

theorem hermiteD_one (τ : ℝ) (U₀ U₁ V₀ V₁ : F) : hermiteD τ U₀ U₁ V₀ V₁ 1 = V₁ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -, h12, -, h14, -, h16⟩ := basis_nodal
  simp [hermiteD, h10, h12, h14, h16]

/-- **The Hermite readout is `C¹` in time** (and `C²` inside each cell):
`∂_t hermite(…, (t - t₀)/τ) = hermiteD(…, (t - t₀)/τ)`, and similarly for the second
derivative. -/
theorem hasDerivAt_hermite {τ : ℝ} (hτ : τ ≠ 0) (t₀ : ℝ) (U₀ U₁ V₀ V₁ : F) (t : ℝ) :
    HasDerivAt (fun t => hermite τ U₀ U₁ V₀ V₁ ((t - t₀) / τ))
      (hermiteD τ U₀ U₁ V₀ V₁ ((t - t₀) / τ)) t := by
  have hθ : HasDerivAt (fun t : ℝ => (t - t₀) / τ) τ⁻¹ t := by
    simpa [div_eq_mul_inv] using ((hasDerivAt_id t).sub_const t₀).mul_const τ⁻¹
  set θ := (t - t₀) / τ
  have hH : ∀ a : Fin 2, HasDerivAt (fun t : ℝ => basisH a ((t - t₀) / τ))
      (basisHD a θ * τ⁻¹) t := fun a =>
    (hasDerivAt_cubic (hCoef a) θ).comp t hθ
  have hG : ∀ a : Fin 2, HasDerivAt (fun t : ℝ => τ * basisG a ((t - t₀) / τ))
      (τ * (basisGD a θ * τ⁻¹)) t := fun a =>
    ((hasDerivAt_cubic (gCoef a) θ).comp t hθ).const_mul τ
  have h := ((((hH 0).smul_const U₀).fun_add ((hH 1).smul_const U₁)).fun_add
    ((hG 0).smul_const V₀)).fun_add ((hG 1).smul_const V₁)
  unfold hermite hermiteD
  refine h.congr_deriv ?_
  have k : ∀ g : ℝ, τ * (g * τ⁻¹) = g := fun g => by field_simp
  rw [k, k, smul_add, smul_smul, smul_smul, mul_comm τ⁻¹ (basisHD 0 θ),
    mul_comm τ⁻¹ (basisHD 1 θ)]

theorem hasDerivAt_hermiteD (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : F) (t : ℝ) :
    HasDerivAt (fun t => hermiteD τ U₀ U₁ V₀ V₁ ((t - t₀) / τ))
      (hermiteDD τ U₀ U₁ V₀ V₁ ((t - t₀) / τ)) t := by
  have hθ : HasDerivAt (fun t : ℝ => (t - t₀) / τ) τ⁻¹ t := by
    simpa [div_eq_mul_inv] using ((hasDerivAt_id t).sub_const t₀).mul_const τ⁻¹
  set θ := (t - t₀) / τ
  have hH : ∀ a : Fin 2, HasDerivAt (fun t : ℝ => basisHD a ((t - t₀) / τ))
      (basisHDD a θ * τ⁻¹) t := fun a =>
    (hasDerivAt_cubicD (hCoef a) θ).comp t hθ
  have hG : ∀ a : Fin 2, HasDerivAt (fun t : ℝ => basisGD a ((t - t₀) / τ))
      (basisGDD a θ * τ⁻¹) t := fun a =>
    (hasDerivAt_cubicD (gCoef a) θ).comp t hθ
  have h := ((((hH 0).smul_const U₀).fun_add ((hH 1).smul_const U₁)).fun_const_smul τ⁻¹).fun_add
    (((hG 0).smul_const V₀).fun_add ((hG 1).smul_const V₁))
  unfold hermiteD hermiteDD
  have e1 : (fun t => τ⁻¹ • (basisHD 0 ((t - t₀) / τ) • U₀ + basisHD 1 ((t - t₀) / τ) • U₁) +
      basisGD 0 ((t - t₀) / τ) • V₀ + basisGD 1 ((t - t₀) / τ) • V₁) =
      fun t => τ⁻¹ • (basisHD 0 ((t - t₀) / τ) • U₀ + basisHD 1 ((t - t₀) / τ) • U₁) +
      (basisGD 0 ((t - t₀) / τ) • V₀ + basisGD 1 ((t - t₀) / τ) • V₁) := by
    funext t; abel
  rw [e1]
  refine h.congr_deriv ?_
  module

/-- Pointwise bound for a combination with coefficients bounded by `1`. -/
theorem norm_comb_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (x y : F) :
    ‖a • x + b • y‖ ≤ ‖x‖ + ‖y‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have := norm_nonneg x; have := norm_nonneg y
  nlinarith [abs_nonneg a, abs_nonneg b]

theorem hermite_sub (τ : ℝ) (U₀ U₁ V₀ V₁ U₀' U₁' V₀' V₁' : F) (θ : ℝ) :
    hermite τ U₀ U₁ V₀ V₁ θ - hermite τ U₀' U₁' V₀' V₁' θ =
      hermite τ (U₀ - U₀') (U₁ - U₁') (V₀ - V₀') (V₁ - V₁') θ := by
  simp only [hermite, smul_sub]; abel

theorem hermiteD_sub (τ : ℝ) (U₀ U₁ V₀ V₁ U₀' U₁' V₀' V₁' : F) (θ : ℝ) :
    hermiteD τ U₀ U₁ V₀ V₁ θ - hermiteD τ U₀' U₁' V₀' V₁' θ =
      hermiteD τ (U₀ - U₀') (U₁ - U₁') (V₀ - V₀') (V₁ - V₁') θ := by
  simp only [hermiteD, smul_sub, smul_add]; abel

theorem hermiteDD_sub (τ : ℝ) (U₀ U₁ V₀ V₁ U₀' U₁' V₀' V₁' : F) (θ : ℝ) :
    hermiteDD τ U₀ U₁ V₀ V₁ θ - hermiteDD τ U₀' U₁' V₀' V₁' θ =
      hermiteDD τ (U₀ - U₀') (U₁ - U₁') (V₀ - V₀') (V₁ - V₁') θ := by
  simp only [hermiteDD, smul_sub, smul_add]; abel

/-- **Stability of the Hermite readout** with respect to nodal data (`θ ∈ [0, 1]`, `τ > 0`):
values `‖·‖ ≤ ‖δU₀‖ + ‖δU₁‖ + τ (‖δV₀‖ + ‖δV₁‖)`, first derivative
`≤ (3/2) τ⁻¹ ‖δU₁ - δU₀‖ + ‖δV₀‖ + ‖δV₁‖`, second derivative
`≤ 6 τ⁻² ‖δU₁ - δU₀‖ + 4 τ⁻¹ (‖δV₀‖ + ‖δV₁‖)` (the identities `H₀' + H₁' = 0`,
`H₀'' + H₁'' = 0` make only the nodal increment of the value errors enter the derivatives). -/
theorem hermite_stability {τ θ : ℝ} (hτ : 0 < τ) (hθ : θ ∈ Icc (0 : ℝ) 1) (U₀ U₁ V₀ V₁ : F) :
    ‖hermite τ U₀ U₁ V₀ V₁ θ‖ ≤ ‖U₀‖ + ‖U₁‖ + τ * (‖V₀‖ + ‖V₁‖) ∧
      ‖hermiteD τ U₀ U₁ V₀ V₁ θ‖ ≤ 3 / 2 * τ⁻¹ * ‖U₁ - U₀‖ + (‖V₀‖ + ‖V₁‖) ∧
      ‖hermiteDD τ U₀ U₁ V₀ V₁ θ‖ ≤ 6 * τ⁻¹ ^ 2 * ‖U₁ - U₀‖ + 4 * τ⁻¹ * (‖V₀‖ + ‖V₁‖) := by
  have hH := abs_basisH_le hθ
  have hG := abs_basisG_le hθ
  have hHD := abs_basisHD_le hθ
  have hGD := abs_basisGD_le hθ
  have hHDD := abs_basisHDD_le hθ
  have hGDD := abs_basisGDD_le hθ
  have hHDs := basisHD_sum θ
  have hHDDs := basisHDD_sum θ
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  refine ⟨?_, ?_, ?_⟩
  · unfold hermite
    have h1 := norm_comb_le (hH 0) (hH 1) U₀ U₁
    have h2 : ‖(τ * basisG 0 θ) • V₀ + (τ * basisG 1 θ) • V₁‖ ≤ τ * (‖V₀‖ + ‖V₁‖) := by
      have e : (τ * basisG 0 θ) • V₀ + (τ * basisG 1 θ) • V₁ =
          τ • (basisG 0 θ • V₀ + basisG 1 θ • V₁) := by
        rw [smul_add, smul_smul, smul_smul]
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
      exact mul_le_mul_of_nonneg_left (norm_comb_le (hG 0) (hG 1) V₀ V₁) hτ.le
    rw [add_assoc]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  · unfold hermiteD
    have e : basisHD 0 θ • U₀ + basisHD 1 θ • U₁ = basisHD 1 θ • (U₁ - U₀) := by
      rw [smul_sub, show basisHD 0 θ = -basisHD 1 θ by linarith, neg_smul]; abel
    rw [e, add_assoc]
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_comb_le (hGD 0) (hGD 1) V₀ V₁))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hτi]
    have := norm_nonneg (U₁ - U₀)
    calc τ⁻¹ * (|basisHD 1 θ| * ‖U₁ - U₀‖) ≤ τ⁻¹ * (3 / 2 * ‖U₁ - U₀‖) := by
          gcongr; exact hHD 1
      _ = _ := by ring
  · unfold hermiteDD
    have e : basisHDD 0 θ • U₀ + basisHDD 1 θ • U₁ = basisHDD 1 θ • (U₁ - U₀) := by
      rw [smul_sub, show basisHDD 0 θ = -basisHDD 1 θ by linarith, neg_smul]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have := norm_nonneg (U₁ - U₀)
      calc τ⁻¹ ^ 2 * (|basisHDD 1 θ| * ‖U₁ - U₀‖) ≤ τ⁻¹ ^ 2 * (6 * ‖U₁ - U₀‖) := by
            gcongr; exact hHDD 1
        _ = _ := by ring
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτi]
      have h4 : ‖basisGDD 0 θ • V₀ + basisGDD 1 θ • V₁‖ ≤ 4 * (‖V₀‖ + ‖V₁‖) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        have := norm_nonneg V₀; have := norm_nonneg V₁
        nlinarith [hGDD 0, hGDD 1, abs_nonneg (basisGDD 0 θ), abs_nonneg (basisGDD 1 θ)]
      calc τ⁻¹ * ‖basisGDD 0 θ • V₀ + basisGDD 1 θ • V₁‖ ≤ τ⁻¹ * (4 * (‖V₀‖ + ‖V₁‖)) :=
            mul_le_mul_of_nonneg_left h4 hτi.le
        _ = _ := by ring

/-- **Accuracy of the Hermite readout on exact data**: for a `C³` trajectory on
`[t₀, t₀ + τ]` with `‖z''‖ ≤ M₂`, `‖z'''‖ ≤ M₃`, the Hermite interpolant of the exact nodal values
and slopes satisfies (`θ ∈ [0, 1]`)
`‖hermite - z‖ ≤ 2 M₂ τ²`, `‖hermiteD - z'‖ ≤ 2 M₃ τ²`, `‖hermiteDD - z''‖ ≤ 4 M₃ τ`. -/
theorem hermite_accuracy {z z' z'' z''' : ℝ → F} {t₀ τ M₂ M₃ θ : ℝ} (hτ : 0 < τ)
    (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hz : ∀ x ∈ Icc t₀ (t₀ + τ), HasDerivAt z (z' x) x)
    (hz' : ∀ x ∈ Icc t₀ (t₀ + τ), HasDerivAt z' (z'' x) x)
    (hz'' : ∀ x ∈ Icc t₀ (t₀ + τ), HasDerivAt z'' (z''' x) x)
    (hM₂ : ∀ x ∈ Icc t₀ (t₀ + τ), ‖z'' x‖ ≤ M₂) (hM₃ : ∀ x ∈ Icc t₀ (t₀ + τ), ‖z''' x‖ ≤ M₃) :
    ‖hermite τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z (t₀ + θ * τ)‖ ≤ 2 * M₂ * τ ^ 2 ∧
      ‖hermiteD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z' (t₀ + θ * τ)‖ ≤
        2 * M₃ * τ ^ 2 ∧
      ‖hermiteDD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z'' (t₀ + θ * τ)‖ ≤
        4 * M₃ * τ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hθτ0 : 0 ≤ θ * τ := mul_nonneg hθ0 hτ.le
  have hθτ1 : t₀ + θ * τ ≤ t₀ + τ := by nlinarith
  have hH := abs_basisH_le ⟨hθ0, hθ1⟩
  have hG := abs_basisG_le ⟨hθ0, hθ1⟩
  have hHD := abs_basisHD_le ⟨hθ0, hθ1⟩
  have hGD := abs_basisGD_le ⟨hθ0, hθ1⟩
  have hHDD := abs_basisHDD_le ⟨hθ0, hθ1⟩
  have hGDD := abs_basisGDD_le ⟨hθ0, hθ1⟩
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ t₀ ⟨le_rfl, by linarith⟩)
  have hM₃0 : 0 ≤ M₃ := (norm_nonneg _).trans (hM₃ t₀ ⟨le_rfl, by linarith⟩)
  have hτi : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ.ne'
  -- basis identities
  have i1 : basisH 0 θ + basisH 1 θ = 1 := basisH_sum θ
  have i2 : basisH 1 θ + basisG 0 θ + basisG 1 θ = θ := by
    rw [basisH_one, basisG_zero, basisG_one]; ring
  have i3 : basisHD 0 θ + basisHD 1 θ = 0 := basisHD_sum θ
  have i4 : basisHD 1 θ + basisGD 0 θ + basisGD 1 θ = 1 := by
    rw [basisHD_one, basisGD_zero, basisGD_one]; ring
  have i5 : basisHD 1 θ / 2 + basisGD 1 θ = θ := by
    rw [basisHD_one, basisGD_one]; ring
  have i6 : basisHDD 0 θ + basisHDD 1 θ = 0 := basisHDD_sum θ
  have i7 : basisHDD 1 θ + basisGDD 0 θ + basisGDD 1 θ = 0 := by
    rw [basisHDD_one, basisGDD_zero, basisGDD_one]; ring
  have i8 : basisHDD 1 θ / 2 + basisGDD 1 θ = 1 := by
    rw [basisHDD_one, basisGDD_one]; ring
  refine ⟨?_, ?_, ?_⟩
  · -- values
    set R1 := z (t₀ + τ) - z t₀ - τ • z' t₀
    set R2 := z' (t₀ + τ) - z' t₀
    set R3 := z (t₀ + θ * τ) - z t₀ - (θ * τ) • z' t₀
    have b1 : ‖R1‖ ≤ M₂ * τ ^ 2 / 2 := taylor1_le hz hz' hM₂ le_rfl hτ.le le_rfl
    have b3 : ‖R3‖ ≤ M₂ * (θ * τ) ^ 2 / 2 := taylor1_le hz hz' hM₂ le_rfl hθτ0 hθτ1
    have b2 : ‖R2‖ ≤ M₂ * τ := by
      have := norm_image_sub_le_of_norm_deriv_le_segment' (f := z') (f' := z'') (a := t₀)
        (b := t₀ + τ) (C := M₂) (fun x hx => (hz' x hx).hasDerivWithinAt)
        (fun x hx => hM₂ x (Ico_subset_Icc_self hx)) (t₀ + τ) ⟨by linarith, le_rfl⟩
      simpa using this
    have e : hermite τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z (t₀ + θ * τ) =
        basisH 1 θ • R1 + (τ * basisG 1 θ) • R2 - R3 := by
      have hz1 : z (t₀ + τ) = z t₀ + τ • z' t₀ + R1 := by simp only [R1]; abel
      have hz1' : z' (t₀ + τ) = z' t₀ + R2 := by simp only [R2]; abel
      have hzθ : z (t₀ + θ * τ) = z t₀ + (θ * τ) • z' t₀ + R3 := by simp only [R3]; abel
      unfold hermite
      rw [hz1, hz1', hzθ]
      have h0 : basisH 0 θ = 1 - basisH 1 θ := by linarith
      have hG0 : basisG 0 θ = θ - basisH 1 θ - basisG 1 θ := by linarith
      rw [h0, hG0]
      simp only [smul_add, add_smul, sub_smul, smul_smul, one_smul]
      module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hτ]
    have := norm_nonneg R1; have := norm_nonneg R2
    have hθ2 : (θ * τ) ^ 2 ≤ τ ^ 2 := by
      have : θ * τ ≤ τ := by nlinarith
      exact pow_le_pow_left₀ hθτ0 this 2
    calc |basisH 1 θ| * ‖R1‖ + τ * |basisG 1 θ| * ‖R2‖ + ‖R3‖
        ≤ 1 * (M₂ * τ ^ 2 / 2) + τ * 1 * (M₂ * τ) + M₂ * (θ * τ) ^ 2 / 2 := by
          gcongr
          · exact hH 1
          · exact hG 1
      _ ≤ 1 * (M₂ * τ ^ 2 / 2) + τ * 1 * (M₂ * τ) + M₂ * τ ^ 2 / 2 := by gcongr
      _ = 2 * M₂ * τ ^ 2 := by ring
  · -- first derivatives
    set R1 := z (t₀ + τ) - z t₀ - τ • z' t₀ - (τ ^ 2 / 2) • z'' t₀
    set R2 := z' (t₀ + τ) - z' t₀ - τ • z'' t₀
    set R3 := z' (t₀ + θ * τ) - z' t₀ - (θ * τ) • z'' t₀
    have b1 : ‖R1‖ ≤ M₃ * τ ^ 3 / 6 := taylor2_le hz hz' hz'' hM₃ le_rfl hτ.le le_rfl
    have b2 : ‖R2‖ ≤ M₃ * τ ^ 2 / 2 := taylor1_le hz' hz'' hM₃ le_rfl hτ.le le_rfl
    have b3 : ‖R3‖ ≤ M₃ * (θ * τ) ^ 2 / 2 := taylor1_le hz' hz'' hM₃ le_rfl hθτ0 hθτ1
    have e : hermiteD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z' (t₀ + θ * τ) =
        (τ⁻¹ * basisHD 1 θ) • R1 + basisGD 1 θ • R2 - R3 := by
      have hz1 : z (t₀ + τ) = z t₀ + τ • z' t₀ + (τ ^ 2 / 2) • z'' t₀ + R1 := by
        simp only [R1]; abel
      have hz1' : z' (t₀ + τ) = z' t₀ + τ • z'' t₀ + R2 := by simp only [R2]; abel
      have hzθ : z' (t₀ + θ * τ) = z' t₀ + (θ * τ) • z'' t₀ + R3 := by simp only [R3]; abel
      unfold hermiteD
      rw [hz1, hz1', hzθ]
      have h0 : basisHD 0 θ = -basisHD 1 θ := by linarith
      have hG0 : basisGD 0 θ = 1 - basisHD 1 θ - basisGD 1 θ := by linarith
      have hG1 : basisGD 1 θ = θ - basisHD 1 θ / 2 := by linarith
      rw [h0, hG0]
      simp only [smul_add, add_smul, sub_smul, smul_smul, one_smul, neg_smul, smul_neg]
      have k1 : τ⁻¹ * (basisHD 1 θ * τ) = basisHD 1 θ := by
        rw [mul_comm, mul_assoc, mul_comm τ, hτi, mul_one]
      have k2 : τ⁻¹ * (basisHD 1 θ * (τ ^ 2 / 2)) = (basisHD 1 θ / 2) * τ := by
        field_simp
      rw [k1, k2]
      conv_lhs => rw [show basisGD 1 θ * τ = (θ - basisHD 1 θ / 2) * τ by rw [hG1]]
      simp only [sub_smul, mul_smul]
      module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (inv_pos.mpr hτ)]
    have := norm_nonneg R1; have := norm_nonneg R2
    have hθ2 : (θ * τ) ^ 2 ≤ τ ^ 2 := by
      have : θ * τ ≤ τ := by nlinarith
      exact pow_le_pow_left₀ hθτ0 this 2
    calc τ⁻¹ * |basisHD 1 θ| * ‖R1‖ + |basisGD 1 θ| * ‖R2‖ + ‖R3‖
        ≤ τ⁻¹ * (3 / 2) * (M₃ * τ ^ 3 / 6) + 1 * (M₃ * τ ^ 2 / 2) + M₃ * (θ * τ) ^ 2 / 2 := by
          gcongr
          · exact hHD 1
          · exact hGD 1
      _ ≤ τ⁻¹ * (3 / 2) * (M₃ * τ ^ 3 / 6) + 1 * (M₃ * τ ^ 2 / 2) + M₃ * τ ^ 2 / 2 := by gcongr
      _ = (τ⁻¹ * τ) * (M₃ * τ ^ 2 / 4) + M₃ * τ ^ 2 := by ring
      _ ≤ 2 * M₃ * τ ^ 2 := by rw [hτi]; nlinarith [sq_nonneg τ]
  · -- second derivatives
    set R1 := z (t₀ + τ) - z t₀ - τ • z' t₀ - (τ ^ 2 / 2) • z'' t₀
    set R2 := z' (t₀ + τ) - z' t₀ - τ • z'' t₀
    set R3 := z'' (t₀ + θ * τ) - z'' t₀
    have b1 : ‖R1‖ ≤ M₃ * τ ^ 3 / 6 := taylor2_le hz hz' hz'' hM₃ le_rfl hτ.le le_rfl
    have b2 : ‖R2‖ ≤ M₃ * τ ^ 2 / 2 := taylor1_le hz' hz'' hM₃ le_rfl hτ.le le_rfl
    have b3 : ‖R3‖ ≤ M₃ * (θ * τ) := by
      have := norm_image_sub_le_of_norm_deriv_le_segment' (f := z'') (f' := z''') (a := t₀)
        (b := t₀ + θ * τ) (C := M₃)
        (fun x hx => (hz'' x ⟨hx.1, hx.2.trans hθτ1⟩).hasDerivWithinAt)
        (fun x hx => hM₃ x ⟨hx.1, hx.2.le.trans hθτ1⟩) (t₀ + θ * τ) ⟨by linarith, le_rfl⟩
      simpa using this
    have e : hermiteDD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z'' (t₀ + θ * τ) =
        (τ⁻¹ ^ 2 * basisHDD 1 θ) • R1 + (τ⁻¹ * basisGDD 1 θ) • R2 - R3 := by
      have hz1 : z (t₀ + τ) = z t₀ + τ • z' t₀ + (τ ^ 2 / 2) • z'' t₀ + R1 := by
        simp only [R1]; abel
      have hz1' : z' (t₀ + τ) = z' t₀ + τ • z'' t₀ + R2 := by simp only [R2]; abel
      have hzθ : z'' (t₀ + θ * τ) = z'' t₀ + R3 := by simp only [R3]; abel
      unfold hermiteDD
      rw [hz1, hz1', hzθ]
      have h0 : basisHDD 0 θ = -basisHDD 1 θ := by linarith
      have hG0 : basisGDD 0 θ = -basisHDD 1 θ - basisGDD 1 θ := by linarith
      have hG1 : basisGDD 1 θ = 1 - basisHDD 1 θ / 2 := by linarith
      rw [h0, hG0]
      simp only [smul_add, add_smul, sub_smul, smul_smul, one_smul, neg_smul, smul_neg]
      have k1 : τ⁻¹ ^ 2 * (basisHDD 1 θ * τ) = τ⁻¹ * basisHDD 1 θ := by
        field_simp
      have k2 : τ⁻¹ ^ 2 * (basisHDD 1 θ * (τ ^ 2 / 2)) = basisHDD 1 θ / 2 := by
        field_simp
      have k3 : τ⁻¹ * (basisGDD 1 θ * τ) = basisGDD 1 θ := by
        field_simp
      rw [k1, k2, k3, hG1]
      simp only [sub_smul, neg_sub, smul_sub, one_smul, neg_smul]
      module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < τ⁻¹ ^ 2), abs_of_pos (inv_pos.mpr hτ)]
    have := norm_nonneg R1; have := norm_nonneg R2
    have hθ1' : θ * τ ≤ τ := by nlinarith
    calc τ⁻¹ ^ 2 * |basisHDD 1 θ| * ‖R1‖ + τ⁻¹ * |basisGDD 1 θ| * ‖R2‖ + ‖R3‖
        ≤ τ⁻¹ ^ 2 * 6 * (M₃ * τ ^ 3 / 6) + τ⁻¹ * 4 * (M₃ * τ ^ 2 / 2) + M₃ * (θ * τ) := by
          gcongr
          · exact hHDD 1
          · exact hGDD 1
      _ ≤ τ⁻¹ ^ 2 * 6 * (M₃ * τ ^ 3 / 6) + τ⁻¹ * 4 * (M₃ * τ ^ 2 / 2) + M₃ * τ := by gcongr
      _ = (τ⁻¹ * τ) ^ 2 * (M₃ * τ) + (τ⁻¹ * τ) * (2 * M₃ * τ) + M₃ * τ := by ring
      _ = 4 * M₃ * τ := by rw [hτi]; ring

/-- **Error of the Hermite readout** (`eq:generated-Hermite` mechanism): nodal value errors
`δU_a = U_a - z(t_a)`, nodal slope errors `δV_a = V_a - z'(t_a)` and the exact-data accuracy add up:
values `≤ ‖δU₀‖ + ‖δU₁‖ + τ(‖δV₀‖ + ‖δV₁‖) + 2M₂τ²`, first derivatives
`≤ (3/2)τ⁻¹‖δU₁ - δU₀‖ + ‖δV₀‖ + ‖δV₁‖ + 2M₃τ²`, second derivatives
`≤ 6τ⁻²‖δU₁ - δU₀‖ + 4τ⁻¹(‖δV₀‖ + ‖δV₁‖) + 4M₃τ`. -/
theorem hermite_error {z z' z'' z''' : ℝ → F} {t₀ τ M₂ M₃ θ : ℝ} (hτ : 0 < τ)
    (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hz : ∀ x ∈ Icc t₀ (t₀ + τ), HasDerivAt z (z' x) x)
    (hz' : ∀ x ∈ Icc t₀ (t₀ + τ), HasDerivAt z' (z'' x) x)
    (hz'' : ∀ x ∈ Icc t₀ (t₀ + τ), HasDerivAt z'' (z''' x) x)
    (hM₂ : ∀ x ∈ Icc t₀ (t₀ + τ), ‖z'' x‖ ≤ M₂) (hM₃ : ∀ x ∈ Icc t₀ (t₀ + τ), ‖z''' x‖ ≤ M₃)
    (U₀ U₁ V₀ V₁ : F) :
    ‖hermite τ U₀ U₁ V₀ V₁ θ - z (t₀ + θ * τ)‖ ≤
        ‖U₀ - z t₀‖ + ‖U₁ - z (t₀ + τ)‖ + τ * (‖V₀ - z' t₀‖ + ‖V₁ - z' (t₀ + τ)‖) +
          2 * M₂ * τ ^ 2 ∧
      ‖hermiteD τ U₀ U₁ V₀ V₁ θ - z' (t₀ + θ * τ)‖ ≤
        3 / 2 * τ⁻¹ * ‖(U₁ - z (t₀ + τ)) - (U₀ - z t₀)‖ +
          (‖V₀ - z' t₀‖ + ‖V₁ - z' (t₀ + τ)‖) + 2 * M₃ * τ ^ 2 ∧
      ‖hermiteDD τ U₀ U₁ V₀ V₁ θ - z'' (t₀ + θ * τ)‖ ≤
        6 * τ⁻¹ ^ 2 * ‖(U₁ - z (t₀ + τ)) - (U₀ - z t₀)‖ +
          4 * τ⁻¹ * (‖V₀ - z' t₀‖ + ‖V₁ - z' (t₀ + τ)‖) + 4 * M₃ * τ := by
  obtain ⟨a1, a2, a3⟩ := hermite_accuracy (θ := θ) hτ hθ hz hz' hz'' hM₂ hM₃
  obtain ⟨s1, s2, s3⟩ := hermite_stability hτ hθ (U₀ - z t₀) (U₁ - z (t₀ + τ)) (V₀ - z' t₀)
    (V₁ - z' (t₀ + τ))
  refine ⟨?_, ?_, ?_⟩
  · have e : hermite τ U₀ U₁ V₀ V₁ θ - z (t₀ + θ * τ) =
        (hermite τ U₀ U₁ V₀ V₁ θ - hermite τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ) +
          (hermite τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z (t₀ + θ * τ)) := by abel
    rw [e, hermite_sub]
    exact (norm_add_le _ _).trans (add_le_add s1 a1)
  · have e : hermiteD τ U₀ U₁ V₀ V₁ θ - z' (t₀ + θ * τ) =
        (hermiteD τ U₀ U₁ V₀ V₁ θ - hermiteD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ) +
          (hermiteD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z' (t₀ + θ * τ)) := by abel
    rw [e, hermiteD_sub]
    exact (norm_add_le _ _).trans (add_le_add s2 a2)
  · have e : hermiteDD τ U₀ U₁ V₀ V₁ θ - z'' (t₀ + θ * τ) =
        (hermiteDD τ U₀ U₁ V₀ V₁ θ - hermiteDD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ) +
          (hermiteDD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z'' (t₀ + θ * τ)) := by
      abel
    rw [e, hermiteDD_sub]
    exact (norm_add_le _ _).trans (add_le_add s3 a3)

end Hermite

end RenewalGeometry.SpectralGalerkin
