/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialPreparedInverse

/-!
# `thm:supp-action-prepared-chart`: exact finite preparation from free initial records
  (emergent-spacetime manuscript)

Assembly of the four-mean contraction (`NormalizedMeanRoot.prepared_record_exact_zero`) for the
actual constraint map `C_h = CHmap` (`χ = 1`, `Λ = 0`, symmetric-square-root triad, odd `N`,
`h < h₀`), with every constant independent of the cutoff:

* `exists_rangeData_chart`: the range-reduction packet of `lem:supp-initial-range`, now with the
  order-three bounds of `lem:supp-initial-calculus` (`K = 1`) for `𝒞_h` and `𝒩_h = 𝒞_h - L_h`, the
  bound `‖L_h‖ ≤ M_k`, and the identification `𝒞_h = encY ∘ Cmap ∘ decX` near `0`.
* `jacE`: the uniformly invertible derivative `DQ_h(ϑ_h^*) = diag(ω_h, -ω_h/2, -ω_h/2, -ω_h/2)` as
  a continuous linear equivalence `ℝ × ℝ³ ≃ ℝ⁴`, `‖(DQ_h)⁻¹‖ ≤ 1`.
* **`supp_action_prepared_chart`**: the first assertions of `thm:supp-action-prepared-chart`.
-/

open Filter Finset Metric Set
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.PreparedChart

set_option linter.unusedSectionVars false

open QuadJet PeriodicGridSobolev GridLocalOps InitialCalculus InitialRange PreparedSeed
open LyapunovSchmidt HessianRay IteratedDerivBounds UniformDerivBounds LapseHomogeneity
open InitialMeanJet OddPhaseDerivativeReal

/-! ### The range packet with order-three bounds -/

theorem norm_P0L_le {N : ℕ} [NeZero N] (r : ℕ) : ‖P0L (N := N) r‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun c => ?_
  rw [P0L_apply, Real.norm_eq_abs]
  exact (abs_meanG_le (y c)).trans (norm_le_pi_norm y c)

/-- **The range packet of the actual constraint map with order-three bounds.** -/
theorem exists_rangeData_chart (r : ℕ) (hr : 2 ≤ r) :
    ∃ M ρ' ρ C a σ δ Mk h₀ ε : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 < a ∧ 0 < δ ∧ radiiOK a 2 C ρ σ δ ∧
      0 ≤ Mk ∧ 0 < h₀ ∧ 0 < ε ∧
      ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
        ∃ D : RD N r, (∀ X, D.L X = LHfun r X) ∧
          (∀ X, D.full X = CHmap hNo 1 r M (aBlock one_ne_zero) ρ' X) ∧
          D.R = RH r ∧ D.P = PL r ∧ D.P0 = P0L r ∧ D.a = a ∧ D.p = 2 ∧ D.C = C ∧ D.ρ = ρ ∧
          ‖D.L‖ ≤ Mk ∧ DerivBound D.N (ball 0 ρ) 3 (Mk + Mk * max 1 ρ) ∧
          DerivBound D.full (ball 0 ρ) 3 Mk ∧
          (∀ x ∈ ball (0 : XH N r) ρ, AnalyticAt ℝ D.N x) ∧
          (∀ R : ℝ, 0 < R → hN N * R ≤ ε →
            ∀ᶠ X in 𝓝 (0 : XH N r), D.full X = encY r (Cmap 1 R (decX X))) := by
  obtain ⟨M, ρ', ρ, C, h₀, ε, Mk, hρ, hC, hh₀, hε, hall⟩ :=
    supp_initial_calculus (χ := 1) one_ne_zero r hr 1
  obtain ⟨a, ha, hRa⟩ := exists_norm_RH_le r
  obtain ⟨σ, δ, hδ, hrad⟩ := LyapunovSchmidt.exists_radiiOK ha.le (by norm_num : (0 : ℝ) ≤ 2) hC hρ
  have hMk : 0 ≤ Mk := by
    obtain ⟨N₀, _, hNo₀, hh₀'⟩ := exists_odd_hN_lt hh₀
    exact (hall N₀ hNo₀ hh₀').2.2.2.2.1.nonneg (mem_ball_self hρ)
  refine ⟨M, ρ', ρ, C, a, σ, δ, Mk, h₀, ε, hρ, hC, ha, hδ, hrad, hMk, hh₀, hε,
    fun N _ hNo hh => ?_⟩
  obtain ⟨hAn, hCH0, hDCH, hTay, hDB, hEq⟩ := hall N hNo hh
  set CH := CHmap hNo 1 r M (aBlock one_ne_zero) ρ'
  set L := fderiv ℝ CH 0
  have hLX : ∀ X, L X = LHfun r X := fun X => (hDCH X).trans rfl
  have hmeanL : ∀ X c, meanG (L X c) = 0 := fun X c => by rw [hLX]; exact meanG_LHfun hNo r X c
  let D : RD N r :=
    { L := L
      R := RH r
      P := PL r
      P0 := P0L r
      N := fun X => CH X - L X
      DN := fun X => fderiv ℝ CH X - L
      ρ := ρ
      C := C
      a := a
      p := 2
      hPP := fun w => by
        funext c
        rw [PL_apply (y := PL r w), meanG_PL, constArr_zero, sub_zero]
      hPL := fun x => by
        funext c
        rw [PL_apply, hmeanL, constArr_zero, sub_zero]
      hLR := fun y hy => by rw [hLX]; exact LHfun_RH hNo r hy
      hP0L := fun x => by funext c; exact hmeanL x c
      hsplit := fun w hP hP0 => by
        funext c
        have h1 := congrFun hP c
        have h2 : meanG (w c) = 0 := congrFun hP0 c
        rw [PL_apply, h2, constArr_zero, sub_zero] at h1
        exact h1
      hN := fun x hx => (hAn x hx).differentiableAt.hasFDerivAt.sub L.hasFDerivAt
      hDN := fun x hx => (hTay x hx).2
      hN0 := by simp [hCH0]
      hC := hC
      ha := hRa N
      hp := norm_PL_le r }
  have hfull : ∀ X, D.full X = CH X := fun X => by
    show L X + (CH X - L X) = CH X
    abel
  have hDB3 : DerivBound CH (ball 0 ρ) 3 Mk := hDB
  have hLn : ‖L‖ ≤ Mk := hDB3.norm_fderiv_le (by norm_num) (mem_ball_self hρ)
  have hLb : DerivBound (fun X => L X) (ball (0 : XH N r) ρ) 3 (‖L‖ * max 1 ρ) :=
    DerivBound.clm L hρ.le ball_subset_closedBall 3
  have hNb : DerivBound D.N (ball 0 ρ) 3 (Mk + Mk * max 1 ρ) :=
    (hDB3.sub hLb isOpen_ball).mono le_rfl
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hLn (by positivity)))
  have hFb : DerivBound D.full (ball 0 ρ) 3 Mk := hDB3.congr fun X => (hfull X).symm
  refine ⟨D, hLX, hfull, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hLn, hNb, hFb,
    fun x hx => (hAn x hx).sub (L.analyticAt x), fun R hR hRε => ?_⟩
  filter_upwards [hEq R hR hRε] with X hX
  rw [hfull, hX]

/-! ### The uniformly invertible jacobian `DQ_h(ϑ_h^*)` -/

/-- `DQ_h(ϑ_h^*) = diag(ω, -ω/2, -ω/2, -ω/2)` as a map `ℝ × ℝ³ → ℝ⁴`. -/
def jacF (ω : ℝ) : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ϑ => eQ (ω * ϑ.1, fun i => -(ω / 2) * ϑ.2 i)
      map_add' := fun ϑ ϑ' => by
        funext c; cases c using Fin.cases <;> simp [eQ] <;> ring
      map_smul' := fun t ϑ => by
        funext c; cases c using Fin.cases <;> simp [eQ] <;> ring }

/-- Its inverse. -/
def jacG (ω : ℝ) : (Fin 4 → ℝ) →L[ℝ] (ℝ × (Fin 3 → ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (w 0 / ω, fun i => -(2 / ω) * w i.succ)
      map_add' := fun w w' => by
        refine Prod.ext ?_ (funext fun i => ?_) <;> simp <;> ring
      map_smul' := fun t w => by
        refine Prod.ext ?_ (funext fun i => ?_) <;> simp <;> ring }

theorem jacF_apply (ω : ℝ) (ϑ : ℝ × (Fin 3 → ℝ)) :
    jacF ω ϑ = eQ (ω * ϑ.1, fun i => -(ω / 2) * ϑ.2 i) := rfl

theorem jacG_apply (ω : ℝ) (w : Fin 4 → ℝ) :
    jacG ω w = (w 0 / ω, fun i => -(2 / ω) * w i.succ) := rfl

/-- The jacobian as a continuous linear equivalence (`ω ≠ 0`). -/
def jacE (ω : ℝ) (hω : ω ≠ 0) : (ℝ × (Fin 3 → ℝ)) ≃L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (jacF ω) (jacG ω)
    (fun ϑ => by
      refine Prod.ext ?_ (funext fun i => ?_)
      · simp [jacF_apply, jacG_apply, eQ]; field_simp
      · simp [jacF_apply, jacG_apply, eQ]; field_simp)
    (fun w => by
      funext c
      cases c using Fin.cases
      · simp [jacF_apply, jacG_apply, eQ]; field_simp
      · simp [jacF_apply, jacG_apply, eQ]; field_simp)

theorem jacE_apply (ω : ℝ) (hω : ω ≠ 0) (ϑ : ℝ × (Fin 3 → ℝ)) :
    jacE ω hω ϑ = eQ (ω * ϑ.1, fun i => -(ω / 2) * ϑ.2 i) := rfl

/-- `‖(DQ_h)⁻¹‖ ≤ 1` (`ω_h ≥ 4`). -/
theorem norm_jacE_symm_le {ω : ℝ} (hω : 4 ≤ ω) :
    ‖((jacE ω (by linarith)).symm : (Fin 4 → ℝ) →L[ℝ] (ℝ × (Fin 3 → ℝ)))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul]
  have hω0 : 0 < ω := by linarith
  show ‖jacG ω w‖ ≤ ‖w‖
  rw [jacG_apply]
  refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hω0]
    have := norm_le_pi_norm w 0
    rw [Real.norm_eq_abs] at this
    rw [div_le_iff₀ hω0]
    nlinarith [abs_nonneg (w 0), norm_nonneg w]
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    have := norm_le_pi_norm w i.succ
    rw [Real.norm_eq_abs] at this ⊢
    rw [abs_mul, abs_neg, abs_div, abs_of_pos hω0]
    have h2 : |(2 : ℝ)| / ω ≤ 1 := by
      rw [abs_two, div_le_iff₀ hω0]; linarith
    calc |(2 : ℝ)| / ω * |w i.succ| ≤ 1 * ‖w‖ :=
          mul_le_mul h2 this (abs_nonneg _) zero_le_one
      _ = ‖w‖ := one_mul _

theorem omega_le (N : ℕ) [NeZero N] : omega N ≤ 2 * Real.pi := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold omega
  have := Real.sin_le (x := Real.pi / N) (by positivity)
  calc 2 * (N : ℝ) * Real.sin (Real.pi / N) ≤ 2 * N * (Real.pi / N) := by gcongr
    _ = 2 * Real.pi := by field_simp

theorem norm_root_le (N : ℕ) [NeZero N] :
    ‖((3 * omega N / 4, 0) : ℝ × (Fin 3 → ℝ))‖ ≤ 5 := by
  refine norm_prod_le_iff.mpr ⟨?_, by simp⟩
  have h1 := omega_le N
  have h2 : 0 ≤ omega N := by
    unfold omega
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have : 0 ≤ Real.sin (Real.pi / N) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (div_le_self Real.pi_pos.le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)))
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [Real.pi_lt_d2]

/-! ### Cutoff-uniform constants of the reduced mean map -/

/-- The order-three constant of `RangeUniform.C3` without the factor `‖P₀‖`. -/
def C3core {N r : ℕ} [NeZero N] (D : RD N r) (MN σ δ : ℝ) : ℝ :=
  Nat.factorial 3 * MN * max 1 ((1 + D.a) * (max 1 (RangeUniform.delta0 D MN σ δ) +
    UniformImplicit.impC 1 (RangeUniform.Mf D MN) 1 (RangeUniform.rhoP D))) ^ 3

theorem C3_eq {N r : ℕ} [NeZero N] (D : RD N r) (MN σ δ : ℝ) :
    RangeUniform.C3 D MN σ δ = ‖D.P0‖ * C3core D MN σ δ := rfl

theorem delta0_congr {N N' r : ℕ} [NeZero N] [NeZero N'] (D : RD N r) (D' : RD N' r)
    (ha : D.a = D'.a) (hp : D.p = D'.p) (hρ : D.ρ = D'.ρ) (MN σ δ : ℝ) :
    RangeUniform.delta0 D MN σ δ = RangeUniform.delta0 D' MN σ δ := by
  simp only [RangeUniform.delta0, RangeUniform.Mf, RangeUniform.rhoP, ha, hp, hρ]

theorem C3core_congr {N N' r : ℕ} [NeZero N] [NeZero N'] (D : RD N r) (D' : RD N' r)
    (ha : D.a = D'.a) (hp : D.p = D'.p) (hρ : D.ρ = D'.ρ) (MN σ δ : ℝ) :
    C3core D MN σ δ = C3core D' MN σ δ := by
  simp only [C3core, delta0_congr D D' ha hp hρ, RangeUniform.Mf, RangeUniform.rhoP, ha, hp, hρ]

/-- Polarization of a symmetric bilinear map. -/
theorem polar {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] {B : X →L[ℝ] X →L[ℝ] W} (hB : ∀ u v, B u v = B v u) (u v : X) :
    B u v = (1 / 4 : ℝ) • (B (u + v) (u + v) - B (u - v) (u - v)) := by
  simp only [map_add, map_sub, add_apply, sub_apply]
  rw [hB v u]
  module

theorem P_sol {N r : ℕ} [NeZero N] (D : RD N r) (σ δ : ℝ) (z : XH N r) :
    D.P (D.sol σ δ z) = D.sol σ δ z := by
  unfold LyapunovSchmidt.RangeData.sol
  split_ifs with h
  · exact (D.exists_unique_solution h.1 h.2.1 h.2.2).exists.choose_spec.1.1
  · exact map_zero _

theorem chartOK_mono {K b ζ M m ρ r ρW t0 t1 : ℝ} (hK : 0 ≤ K) (hζ : 0 ≤ ζ) (hM : 0 ≤ M)
    (hm : 0 ≤ m) (h : NormalizedMeanRoot.chartOK K b ζ M m ρ r ρW t0) (ht1 : 0 < t1)
    (h10 : t1 ≤ t0) : NormalizedMeanRoot.chartOK K b ζ M m ρ r ρW t1 := by
  obtain ⟨hr, hρW, ht0, h4, h5, h6⟩ := h
  have hξ : 0 ≤ ζ * (1 + m + r) + ρW := by positivity
  refine ⟨hr, hρW, ht1, (mul_le_mul_of_nonneg_right h10 hξ).trans_lt h4, h5.trans' ?_,
    h6.trans' ?_⟩
  · gcongr
  · gcongr

/-- A real inequality for the bordered bound with `β = C C_r |t|`, `p = M = 2`. -/
theorem inv_bound_aux {a ζ CC P0n u v t : ℝ} (ha : 0 ≤ a) (hζ : 0 ≤ ζ) (hCC : 0 ≤ CC)
    (hP0 : P0n ≤ 1) (hP00 : 0 ≤ P0n) (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 < |t|) (ht1 : |t| ≤ 1) :
    a * (2 * (u + 2 * (CC * |t|) * ζ * (2 * 2 / |t|) * v)) +
        ζ * (2 * 2 / |t| * (v + P0n * (CC * |t|) * a *
          (2 * (u + 2 * (CC * |t|) * ζ * (2 * 2 / |t|) * v)))) ≤
      ((2 * a + 8 * ζ * CC * a) * (1 + 8 * CC * ζ) + 4 * ζ) * (u + |t|⁻¹ * v) := by
  have e : 2 * (CC * |t|) * ζ * (2 * 2 / |t|) = 8 * CC * ζ := by field_simp; ring
  rw [e]
  set X := u + 8 * CC * ζ * v with hX
  have hs : 1 ≤ |t|⁻¹ := one_le_inv₀ ht |>.mpr ht1
  have e2 : ζ * (2 * 2 / |t| * (v + P0n * (CC * |t|) * a * (2 * X))) =
      4 * ζ * |t|⁻¹ * v + 8 * ζ * P0n * CC * a * X := by
    field_simp; ring
  rw [e2]
  have hX0 : 0 ≤ X := by positivity
  have hXb : X ≤ (1 + 8 * CC * ζ) * (u + |t|⁻¹ * v) := by
    have : v ≤ |t|⁻¹ * v := le_mul_of_one_le_left hv hs
    have h8 : 0 ≤ 8 * CC * ζ := by positivity
    nlinarith [mul_nonneg h8 hu, mul_le_mul_of_nonneg_left this h8]
  have hP : 8 * ζ * P0n * CC * a * X ≤ 8 * ζ * CC * a * X := by
    have : 0 ≤ 8 * ζ * CC * a * X := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hP0 this]
  have hsv : 0 ≤ |t|⁻¹ * v := by positivity
  calc a * (2 * X) + (4 * ζ * |t|⁻¹ * v + 8 * ζ * P0n * CC * a * X)
      ≤ (2 * a + 8 * ζ * CC * a) * X + 4 * ζ * (|t|⁻¹ * v) := by nlinarith
    _ ≤ (2 * a + 8 * ζ * CC * a) * ((1 + 8 * CC * ζ) * (u + |t|⁻¹ * v)) +
          4 * ζ * (u + |t|⁻¹ * v) :=
        add_le_add (mul_le_mul_of_nonneg_left hXb (by positivity))
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    _ = ((2 * a + 8 * ζ * CC * a) * (1 + 8 * CC * ζ) + 4 * ζ) * (u + |t|⁻¹ * v) := by ring

theorem finrank_GridH {N : ℕ} [NeZero N] (s : ℕ) : Module.finrank ℝ (GridH N s) = N ^ 3 := by
  rw [LinearEquiv.finrank_eq (GridH.toFunLin (N := N) (r := s)),
    Module.finrank_fintype_fun_eq_card]
  simp [PeriodicGridSobolev.Grid, ZMod.card]

/-- `dim 𝒫^r_h = 12 N³` (the canonical phase). -/
theorem finrank_XH {N : ℕ} [NeZero N] (r : ℕ) : Module.finrank ℝ (XH N r) = 12 * N ^ 3 := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp only [finrank_GridH, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- `dim 𝒴^r_h = 4 N³` (the four constraint rows). -/
theorem finrank_YH {N : ℕ} [NeZero N] (r : ℕ) : Module.finrank ℝ (YH N r) = 4 * N ^ 3 := by
  rw [Module.finrank_pi_fintype]
  simp only [finrank_GridH, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The prepared record `𝔍 = t(Z(ϑ) + W) + R y(t(Z(ϑ) + W))`
(`eq:supp-initial-prepared-record`). -/
def prec {N r : ℕ} [NeZero N] (D : RD N r) (σ δ t : ℝ) (ϑ : ℝ × (Fin 3 → ℝ)) (W : XH N r) :
    XH N r :=
  t • (Zs0 r + ZsL r ϑ + W) + D.R (D.sol σ δ (t • (Zs0 r + ZsL r ϑ + W)))

/-! ### `thm:supp-action-prepared-chart` -/

set_option maxHeartbeats 1000000 in
/-- **`thm:supp-action-prepared-chart` (exact finite preparation from free initial records).**
For the actual action (`χ = 1`, `Λ = 0`, symmetric-square-root triad) and `r ≥ 2` there are
constants `t₀, ρ_W, r_ϑ, C_r, C_inv, h₀ > 0` independent of the cutoff such that for every odd
`N` with `h < h₀` the range packet `D` of `lem:supp-initial-range` (`D.full = C_h = CHmap`,
`D.L = L_h`, `D.R = R_h`, `D.P = P_⊥`, `D.P₀ = P₀`) satisfies, with `dim 𝒫^r_h = 12N³` and
`dim 𝒴^r_h = 4N³`: for every `0 < |t| ≤ t₀` and every free record `W ∈ ker L_h`, `‖W‖ ≤ ρ_W`,
there is `ϑ ∈ B̄(ϑ_h^*, r_ϑ)` (`ϑ_h^* = (3ω_h/4, 0, 0, 0)`) such that the prepared record
`𝔍 = prec t ϑ W = t(Z_h(ϑ) + W) + R_h y_h(t(Z_h(ϑ) + W))` (`eq:supp-initial-prepared-record`):
* is an exact zero, `C_h(𝔍) = 0`, with `‖𝔍‖ ≤ C_r|t|` (`eq:supp-initial-exact-zero`), and the
  reduced (hence normalized, `eq:supp-initial-normalized-mean`) mean vanishes;
* `ϑ` is the only balancing parameter in `B̄(ϑ_h^*, r_ϑ)` with an exact zero;
* `DC_h(𝔍)` has a bounded linear right inverse `S` with
  `‖S f‖ ≤ C_inv (‖P_⊥ f‖ + |t|⁻¹ |P₀ f|)` (`eq:supp-initial-full-inverse`); hence `DC_h(𝔍)` is
  onto, its kernel has dimension `8N³`, and by the implicit function theorem `C_h` is the first
  component of a local homeomorphism `𝒫^r_h ⊇ U ≅ 𝒴^r_h × ker DC_h(𝔍)` near `𝔍`, so the zero set
  is, near `𝔍`, a topological submanifold of codimension `4N³` in the `12N³`-dimensional phase;
* (relative openness) if `‖W‖ < ρ_W`, every exact zero of `C_h` in a neighbourhood of `𝔍` is the
  prepared record `prec t ϑ W'` of some free record `W' ∈ ker L_h`, `‖W'‖ ≤ ρ_W`, with the same
  balancing parameter `ϑ` (unique for `W'`).
The free record `W` is an arbitrary small element of `ker L_h` (no symmetry, CMC,
conformal-flatness or frequency-support restriction). -/
theorem supp_action_prepared_chart (r : ℕ) (hr : 2 ≤ r) :
    ∃ M ρ' σ δ t0 ρW rθ Cr Cinv h₀ : ℝ, 0 < t0 ∧ 0 < ρW ∧ 0 < rθ ∧ 0 ≤ Cr ∧ 0 ≤ Cinv ∧ 0 < h₀ ∧
      ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
        ∃ D : RD N r, (∀ X, D.full X = CHmap hNo 1 r M (aBlock one_ne_zero) ρ' X) ∧
          (∀ X, D.L X = LHfun r X) ∧ D.R = RH r ∧ D.P = PL r ∧ D.P0 = P0L r ∧
          Module.finrank ℝ (XH N r) = 12 * N ^ 3 ∧ Module.finrank ℝ (YH N r) = 4 * N ^ 3 ∧
          ∀ t : ℝ, t ≠ 0 → |t| ≤ t0 → ∀ W : XH N r, LHfun r W = 0 → ‖W‖ ≤ ρW →
            ∃ ϑ ∈ closedBall ((3 * omega N / 4, 0) : ℝ × (Fin 3 → ℝ)) rθ,
              D.full (prec D σ δ t ϑ W) = 0 ∧ ‖prec D σ δ t ϑ W‖ ≤ Cr * |t| ∧
              D.meanMap σ δ (t • (Zs0 r + ZsL r ϑ + W)) = 0 ∧
              (∀ ϑ' ∈ closedBall ((3 * omega N / 4, 0) : ℝ × (Fin 3 → ℝ)) rθ,
                D.full (prec D σ δ t ϑ' W) = 0 → ϑ' = ϑ) ∧
              (∃ S : YH N r →L[ℝ] XH N r,
                (∀ f, fderiv ℝ D.full (prec D σ δ t ϑ W) (S f) = f) ∧
                ∀ f, ‖S f‖ ≤ Cinv * (‖PL r f‖ + |t|⁻¹ * ‖P0L r f‖)) ∧
              (fderiv ℝ D.full (prec D σ δ t ϑ W)).range = ⊤ ∧
              Module.finrank ℝ (fderiv ℝ D.full (prec D σ δ t ϑ W)).ker = 8 * N ^ 3 ∧
              (∃ e : OpenPartialHomeomorph (XH N r)
                  (YH N r × (fderiv ℝ D.full (prec D σ δ t ϑ W)).ker),
                prec D σ δ t ϑ W ∈ e.source ∧ ∀ X, (e X).1 = D.full X) ∧
              (‖W‖ < ρW → ∃ U ∈ 𝓝 (prec D σ δ t ϑ W), ∀ Y ∈ U, D.full Y = 0 →
                ∃ W' : XH N r, LHfun r W' = 0 ∧ ‖W'‖ ≤ ρW ∧ Y = prec D σ δ t ϑ W' ∧
                  ∀ ϑ' ∈ closedBall ((3 * omega N / 4, 0) : ℝ × (Fin 3 → ℝ)) rθ,
                    D.full (prec D σ δ t ϑ' W') = 0 → ϑ' = ϑ) := by
  obtain ⟨M, ρ', ρ, C, a, σ, δ, Mk, h₁, ε, hρ, hC, ha, hδ, hrad, hMk, hh₁, hε, hall⟩ :=
    exists_rangeData_chart r hr
  obtain ⟨εJ, hεJ, hJ⟩ := quadratic_mean_jet_seed
  set MN := Mk + Mk * max 1 ρ with hMNdef
  set cι := (1 + a * Mk)⁻¹ with hcιdef
  have hc1 : 0 < 1 + a * Mk := by positivity
  have hcpos : 0 < cι := inv_pos.mpr hc1
  have hσ : 0 < σ := hrad.1
  -- a reference packet fixes the cutoff-independent radius and order-three constant
  obtain ⟨N₀, _, hNo₀, hh₀⟩ := exists_odd_hN_lt hh₁
  obtain ⟨D₀, -, -, -, -, -, ha₀, hp₀, hC₀, hρ₀, -, hNb₀, -, -, -⟩ := hall N₀ hNo₀ hh₀
  set δ0 := RangeUniform.delta0 D₀ MN σ δ with hδ0def
  set Kc := C3core D₀ MN σ δ with hKcdef
  have hMN : 0 ≤ MN := by positivity
  have hKc : 0 ≤ Kc := by rw [hKcdef, C3core]; positivity
  have hrad₀ : radiiOK D₀.a D₀.p D₀.C D₀.ρ σ δ := by rw [ha₀, hp₀, hC₀, hρ₀]; exact hrad
  have hNb₀' : DerivBound D₀.N (ball 0 D₀.ρ) 3 MN := by rw [hρ₀]; exact hNb₀
  have hδ0 : 0 < δ0 := delta0_pos D₀ (hρ₀ ▸ hρ) hNb₀' hrad₀ hδ
  have hδ0δ : δ0 ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  -- the seed bound, the radii of the contraction, and the time scale
  set ζ := cι⁻¹ * zetaS r with hζdef
  have hζ : 0 ≤ ζ := mul_nonneg (inv_pos.mpr hcpos).le (zetaS_nonneg r)
  obtain ⟨rθ, ρW, t0, hc⟩ := NormalizedMeanRoot.exists_chartOK (K := Kc) (b := Kc) (ζ := ζ)
    (M := 4) (m := 5) (ρ := δ0) hKc hKc hζ (by norm_num) (by norm_num) hδ0
  obtain ⟨hrθ, hρW, ht0, hρc, hηc, -⟩ := id hc
  set ξ := ζ * (1 + 5 + rθ) + ρW with hξdef
  have hξ : 0 ≤ ξ := by positivity
  set η := ζ * (Kc * t0 * ξ ^ 2 + Kc * (ζ * rθ + ρW)) with hηdef
  set Cr := (1 + 2 * a * 2 * C * δ) * (ζ * (1 + 5 + rθ) + ρW) with hCrdef
  have hCr : 0 ≤ Cr := by positivity
  set CC := C * Cr with hCCdef
  have hCC : 0 ≤ CC := by positivity
  obtain ⟨τ1, hτ1, hτ11, hτ1c⟩ := NormalizedMeanRoot.exists_small
    (c := 2 * a * CC + 8 * a * ζ * CC ^ 2) (ε := 1 / 2) (by positivity) (by norm_num)
  obtain ⟨τ2, hτ2, hτ21, hτ2c⟩ := NormalizedMeanRoot.exists_small
    (c := 4 * a * ζ * CC ^ 2) (ε := 1 / 8) (by positivity) (by norm_num)
  obtain ⟨τ3, hτ3, hτ31, hτ3c⟩ := NormalizedMeanRoot.exists_small
    (c := 4 * C * ξ ^ 2) (ε := σ / 2) (by positivity) (by positivity)
  set t1 := min t0 (min τ1 (min τ2 τ3)) with ht1def
  have ht1 : 0 < t1 := lt_min ht0 (lt_min hτ1 (lt_min hτ2 hτ3))
  have ht10 : t1 ≤ t0 := min_le_left _ _
  have ht1τ1 : t1 ≤ τ1 := (min_le_right _ _).trans (min_le_left _ _)
  have ht1τ2 : t1 ≤ τ2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht1τ3 : t1 ≤ τ3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have ht11 : t1 ≤ 1 := ht1τ1.trans hτ11
  have hc1' : NormalizedMeanRoot.chartOK Kc Kc ζ 4 5 δ0 rθ ρW t1 :=
    chartOK_mono hKc hζ (by norm_num) (by norm_num) hc ht1 ht10
  set Cinv := (2 * a + 8 * ζ * CC * a) * (1 + 8 * CC * ζ) + 4 * ζ with hCinvdef
  have hCinv : 0 ≤ Cinv := by positivity
  refine ⟨M, ρ', σ, δ, t1, cι * ρW, rθ, Cr, Cinv, min h₁ (1 / 2), ht1, by positivity, hrθ, hCr,
    hCinv, lt_min hh₁ (by norm_num), fun N _ hNo hh => ?_⟩
  obtain ⟨D, hDL, hfullCH, hR, hP, hP0, ha', hp', hC', hρ', hLn, hNb, hFb, hNa, hEq⟩ :=
    hall N hNo (hh.trans_le (min_le_left _ _))
  -- `N ≥ 3`
  have h3 : 3 ≤ N := by
    have h2 : hN N < 1 / 2 := hh.trans_le (min_le_right _ _)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have : (2 : ℝ) < N := by
      rw [show hN N = ((N : ℝ))⁻¹ from rfl, inv_lt_comm₀ hN0 (by norm_num)] at h2
      linarith
    have : 2 < N := by exact_mod_cast this
    obtain ⟨k, hk⟩ := hNo
    omega
  -- the identification with the original rows at a cutoff-admissible `R`
  have hhN : 0 < hN N := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact inv_pos.mpr hN0
  set R := min ε εJ / hN N with hRdef
  have hR0 : 0 < R := div_pos (lt_min hε hεJ) hhN
  have hRN : hN N * R = min ε εJ := by rw [hRdef]; field_simp
  have hjet := hJ N hNo h3 R hR0 (by rw [hRN]; exact min_le_right _ _)
  have hjet' : ∀ (κ : ℝ) (b : Fin 3 → ℝ),
      (1 / 2 * fderiv ℝ (fderiv ℝ (meanLapse (N := N) 1 R)) 0 (uSeed N, pSeedF N κ b)
          (uSeed N, pSeedF N κ b) = (InitialBalance.Qh (omega N) (κ, b)).1) ∧
        ∀ a : Fin 3, 1 / 2 * fderiv ℝ (fderiv ℝ (meanShift (N := N) 1 R a)) 0
          (uSeed N, pSeedF N κ b) (uSeed N, pSeedF N κ b) =
            (InitialBalance.Qh (omega N) (κ, b)).2 a :=
    fun κ b => ⟨(hjet κ b).1.2, fun a => ((hjet κ b).2 a).2⟩
  have hfullR := hEq R hR0 (by rw [hRN]; exact min_le_left _ _)
  -- the packet in the form of the abstract theorems
  have hrD : radiiOK D.a D.p D.C D.ρ σ δ := by rw [ha', hp', hC', hρ']; exact hrad
  have hρD : 0 < D.ρ := hρ' ▸ hρ
  have hNbD : DerivBound D.N (ball 0 D.ρ) 3 MN := by rw [hρ']; exact hNb
  have hFbD : DerivBound D.full (ball 0 D.ρ) 3 Mk := by rw [hρ']; exact hFb
  have hNaD : ∀ x ∈ ball (0 : XH N r) D.ρ, AnalyticAt ℝ D.N x := by rw [hρ']; exact hNa
  have hι : ∀ z, ‖iotaC D cι z‖ ≤ ‖z‖ := by
    have := norm_iotaC_le D hMk hLn
    rw [ha'] at this
    exact this
  have hP0n : ‖D.P0‖ ≤ 1 := hP0 ▸ norm_P0L_le r
  have hδ0eq : RangeUniform.delta0 D MN σ δ = δ0 :=
    delta0_congr D D₀ (ha'.trans ha₀.symm) (hp'.trans hp₀.symm) (hρ'.trans hρ₀.symm) MN σ δ
  have hC3 : RangeUniform.C3 D MN σ δ ≤ Kc := by
    rw [C3_eq, C3core_congr D D₀ (ha'.trans ha₀.symm) (hp'.trans hp₀.symm)
      (hρ'.trans hρ₀.symm) MN σ δ]
    exact mul_le_of_le_one_left hKc hP0n
  have hTb : DerivBound (ThX D σ δ cι) (ball 0 δ0) 3 Kc := by
    have := derivBound_ThX D hρD hNbD hrD hι
    rw [hδ0eq] at this
    exact this.mono le_rfl hC3
  obtain ⟨hΘ, hDΘ, hL, hsymm, hb⟩ := taylor_of_derivBound hTb
  have hd0 : fderiv ℝ (ThX D σ δ cι) 0 = 0 := (hasFDerivAt_ThX_zero D hrD hδ cι).fderiv
  -- the affine seed `Z'(ϑ) = c_ι⁻¹ Z(ϑ)` on the ambient space
  set Z0 : XH N r := cι⁻¹ • Zs0 r with hZ0def
  set Zl : (ℝ × (Fin 3 → ℝ)) →L[ℝ] XH N r := cι⁻¹ • ZsL r with hZldef
  have hseed : ∀ ϑ, Z0 + Zl ϑ = cι⁻¹ • (Zs0 r + ZsL r ϑ) := fun ϑ => by
    rw [smul_add]; rfl
  have hcinv : 0 ≤ cι⁻¹ := (inv_pos.mpr hcpos).le
  have hZ0 : ‖Z0‖ ≤ ζ := by
    rw [hZ0def, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcinv]
    exact mul_le_mul_of_nonneg_left (norm_Zs0_le h3 r) hcinv
  have hZl : ‖Zl‖ ≤ ζ := by
    refine (norm_smul_le (cι⁻¹ : ℝ) (ZsL (N := N) r)).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg hcinv]
    exact mul_le_mul_of_nonneg_left (norm_ZsL_le h3 r) hcinv
  set B := fderiv ℝ (fderiv ℝ (ThX D σ δ cι)) 0 with hBdef
  have hH : ∀ ϑ, B (Z0 + Zl ϑ) (Z0 + Zl ϑ) = (2 : ℝ) • eQ (InitialBalance.Qh (omega N) ϑ) := by
    intro ϑ
    have h := hessian_ThX_seed D hrD hδ hρD hDL hP0 hNbD hFbD hι hcpos.ne' hfullR hjet' ϑ
    rw [hseed, ← h, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
  set θs : ℝ × (Fin 3 → ℝ) := (3 * omega N / 4, 0) with hθsdef
  have hθs : ‖θs‖ ≤ 5 := norm_root_le N
  have hω := four_le_omega h3
  have hroot : B (Z0 + Zl θs) (Z0 + Zl θs) = 0 := by
    rw [hH, InitialBalance.Qh_root]
    funext c
    cases c using Fin.cases <;> simp [eQ]
  have hω0 : omega N ≠ 0 := by linarith
  set A := jacE (omega N) hω0 with hAdef
  have hA : (A : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (Fin 4 → ℝ)) = (B (Z0 + Zl θs)).comp Zl := by
    refine ContinuousLinearMap.ext fun ϑ => ?_
    rw [ContinuousLinearMap.comp_apply, polar (hsymm hδ0),
      show Z0 + Zl θs + Zl ϑ = Z0 + Zl (θs + ϑ) by rw [map_add, add_assoc],
      show Z0 + Zl θs - Zl ϑ = Z0 + Zl (θs - ϑ) by rw [map_sub]; abel, hH, hH]
    show jacE (omega N) hω0 ϑ = _
    rw [jacE_apply]
    funext c
    cases c using Fin.cases with
    | zero =>
      simp only [eQ, InitialBalance.Qh, hθsdef, Pi.smul_apply, Pi.sub_apply, Fin.cons_zero,
        Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub, Pi.add_apply, smul_eq_mul]
      have : ∑ x, ((0 : Fin 3 → ℝ) x - ϑ.2 x) ^ 2 = ∑ x, ((0 : Fin 3 → ℝ) x + ϑ.2 x) ^ 2 :=
        Finset.sum_congr rfl fun i _ => by simp
      rw [this]
      ring
    | succ i =>
      simp only [eQ, InitialBalance.Qh, hθsdef, Pi.smul_apply, Pi.sub_apply, Fin.cons_succ,
        Prod.snd_add, Prod.snd_sub, Pi.add_apply, smul_eq_mul, Pi.zero_apply]
      ring
  have hM1 : ‖(A.symm : (Fin 4 → ℝ) →L[ℝ] (ℝ × (Fin 3 → ℝ)))‖ ≤ 1 := norm_jacE_symm_le hω
  have hM4 : ‖(A.symm : (Fin 4 → ℝ) →L[ℝ] (ℝ × (Fin 3 → ℝ)))‖ ≤ 4 := hM1.trans (by norm_num)
  have hM2 : ‖(A.symm : (Fin 4 → ℝ) →L[ℝ] (ℝ × (Fin 3 → ℝ)))‖ ≤ 2 := hM1.trans (by norm_num)
  -- the kernel projection fixes the prepared free points
  have hPKrec : ∀ (t : ℝ) (ϑ : ℝ × (Fin 3 → ℝ)) (W : XH N r), D.L W = 0 →
      PK D (prec D σ δ t ϑ W) = t • (Zs0 r + ZsL r ϑ + W) ∧
        D.L (prec D σ δ t ϑ W) = D.sol σ δ (t • (Zs0 r + ZsL r ϑ + W)) := by
    intro t ϑ W hLW
    have hL0' : D.L (Zs0 r + ZsL r ϑ + W) = 0 := by
      rw [map_add, hDL, LHfun_seed, hLW, add_zero]
    have hL0 : D.L (t • (Zs0 r + ZsL r ϑ + W)) = 0 := by rw [map_smul, hL0', smul_zero]
    have hLI : D.L (prec D σ δ t ϑ W) = D.sol σ δ (t • (Zs0 r + ZsL r ϑ + W)) := by
      rw [prec, map_add, hL0, zero_add, D.hLR _ (P_sol D σ δ _)]
    refine ⟨?_, hLI⟩
    rw [PK_apply, hLI, prec, add_sub_cancel_right]
  have key : ∀ t : ℝ, t ≠ 0 → |t| ≤ t1 → ∀ W : XH N r, LHfun r W = 0 → ‖W‖ ≤ cι * ρW →
      ∃ ϑ ∈ closedBall θs rθ, D.full (prec D σ δ t ϑ W) = 0 ∧
        ‖prec D σ δ t ϑ W‖ ≤ Cr * |t| ∧ D.meanMap σ δ (t • (Zs0 r + ZsL r ϑ + W)) = 0 ∧
        (∀ ϑ' ∈ closedBall θs rθ, D.full (prec D σ δ t ϑ' W) = 0 → ϑ' = ϑ) ∧
        (∃ S : YH N r →L[ℝ] XH N r,
          (∀ f, D.L (S f) + D.DN (prec D σ δ t ϑ W) (S f) = f) ∧
          ∀ f, ‖S f‖ ≤ Cinv * (‖PL r f‖ + |t|⁻¹ * ‖P0L r f‖)) ∧
        ‖t • (Zs0 r + ZsL r ϑ + W)‖ < δ ∧ ‖D.sol σ δ (t • (Zs0 r + ZsL r ϑ + W))‖ < σ := by
    intro t ht htt W hW hWn
    have hat : 0 < |t| := abs_pos.mpr ht
    have hLW : D.L W = 0 := by rw [hDL]; exact hW
    set w : XH N r := cι⁻¹ • W with hwdef
    have hw : ‖w‖ ≤ ρW := by
      rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcinv]
      calc cι⁻¹ * ‖W‖ ≤ cι⁻¹ * (cι * ρW) := mul_le_mul_of_nonneg_left hWn hcinv
        _ = ρW := by field_simp
    have hrec : ∀ ϑ, iotaC D cι (t • (Z0 + Zl ϑ + w)) = t • (Zs0 r + ZsL r ϑ + W) := by
      intro ϑ
      have hL0 : D.L (Zs0 r + ZsL r ϑ + W) = 0 := by
        rw [map_add, hDL, LHfun_seed, hLW, add_zero]
      rw [hseed, hwdef, ← smul_add, iotaC_apply, map_smul, map_smul, PK_of_ker D hL0]
      simp only [smul_smul]
      congr 1
      field_simp
    obtain ⟨θ, hθ, hzero, hnorm, huniq⟩ := NormalizedMeanRoot.prepared_record_exact_zero D hrD
      (iotaC D cι) (L_iotaC D cι) hι (DΘ := fderiv ℝ (ThX D σ δ cι)) (D2 := fun x =>
        fderiv ℝ (fderiv ℝ (ThX D σ δ cι)) x) hδ0δ hΘ hDΘ hL hKc hd0 (hsymm hδ0) (hb hδ0)
      Z0 Zl hZ0 hZl hθs hroot A hA hM4 hc1' ht htt hw
    rw [hrec] at hzero hnorm
    -- sizes
    set X := Z0 + Zl θ + w with hXdef
    have hXn : ‖X‖ ≤ ξ := NormalizedMeanRoot.norm_seed_le hZ0 hZl hθs hθ hw
    have htX : |t| * ‖X‖ < δ0 := by
      calc |t| * ‖X‖ ≤ t0 * ξ := mul_le_mul (htt.trans ht10) hXn (norm_nonneg _) ht0.le
        _ < δ0 := hρc
    have hxball : t • X ∈ ball (0 : XH N r) δ0 := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs]; exact htX
    have hx' : ‖iotaC D cι (t • X)‖ < δ :=
      ((hι _).trans_lt (mem_ball_zero_iff.mp hxball)).trans_le hδ0δ
    have hxt : ‖t • (Zs0 r + ZsL r θ + W)‖ ≤ t1 * ξ := by
      rw [← hrec]
      refine (hι _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul htt hXn (norm_nonneg _) ht1.le
    have hxδ : ‖t • (Zs0 r + ZsL r θ + W)‖ < δ := by rw [← hrec]; exact hx'
    have hLx : D.L (t • (Zs0 r + ZsL r θ + W)) = 0 := by rw [← hrec]; exact L_iotaC D cι _
    have hsolS := D.sol_spec hrD hLx hxδ.le
    have hIball : prec D σ δ t θ W ∈ ball (0 : XH N r) D.ρ :=
      mem_ball_zero_iff.mpr ((D.norm_arg_le hxδ.le hsolS.1).trans_lt hrD.2.2.1)
    have hnorm' : ‖prec D σ δ t θ W‖ ≤ Cr * |t| := by
      refine hnorm.trans (le_of_eq ?_)
      rw [ha', hp', hC', hCrdef]
      ring
    -- the range solution is strictly inside its ball
    have hyσ : ‖D.sol σ δ (t • (Zs0 r + ZsL r θ + W))‖ < σ := by
      have h := D.norm_sol_le hrD hLx hxδ.le
      rw [hp', hC'] at h
      have hx2 : ‖t • (Zs0 r + ZsL r θ + W)‖ ^ 2 ≤ t1 * ξ ^ 2 := by
        have h0 := norm_nonneg (t • (Zs0 r + ZsL r θ + W))
        calc ‖t • (Zs0 r + ZsL r θ + W)‖ ^ 2 ≤ (t1 * ξ) ^ 2 := pow_le_pow_left₀ h0 hxt 2
          _ = t1 ^ 2 * ξ ^ 2 := by ring
          _ ≤ t1 * ξ ^ 2 := by
              have : t1 ^ 2 ≤ t1 := by rw [sq]; exact mul_le_of_le_one_left ht1.le ht11
              exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      calc ‖D.sol σ δ (t • (Zs0 r + ZsL r θ + W))‖
          ≤ 2 * 2 * C * ‖t • (Zs0 r + ZsL r θ + W)‖ ^ 2 := h
        _ ≤ 2 * 2 * C * (t1 * ξ ^ 2) := mul_le_mul_of_nonneg_left hx2 (by positivity)
        _ = 4 * C * ξ ^ 2 * t1 := by ring
        _ ≤ 4 * C * ξ ^ 2 * τ3 := mul_le_mul_of_nonneg_left ht1τ3 (by positivity)
        _ ≤ σ / 2 := hτ3c
        _ < σ := half_lt_self hσ
    -- the mean block along the balancing directions
    have hβ : ‖D.DN (iotaC D cι (t • X) + D.R (D.sol σ δ (iotaC D cι (t • X))))‖ ≤
        CC * |t| := by
      rw [hrec]
      refine (D.hDN _ hIball).trans ?_
      rw [hC', hCCdef, mul_assoc]
      exact mul_le_mul_of_nonneg_left hnorm' hC
    have hblock : ‖fderiv ℝ (ThX D σ δ cι) (t • X) ∘L Zl -
        t • (A : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (Fin 4 → ℝ))‖ ≤ η * |t| := by
      have hray := (NormalizedMeanRoot.normalized_ray_bounds hΘ hDΘ hL hKc (ThX_zero D hrD cι)
        hd0 (hsymm hδ0) ht htX).2
      have h1 : ‖fderiv ℝ (ThX D σ δ cι) (t • X) - t • B X‖ ≤ Kc * |t| ^ 2 * ‖X‖ ^ 2 := by
        have e : fderiv ℝ (ThX D σ δ cι) (t • X) - t • B X =
            t • (t⁻¹ • fderiv ℝ (ThX D σ δ cι) (t • X) - B X) := by
          rw [smul_sub, smul_smul, mul_inv_cancel₀ ht, one_smul]
        rw [e, norm_smul, Real.norm_eq_abs]
        calc |t| * ‖t⁻¹ • fderiv ℝ (ThX D σ δ cι) (t • X) - B X‖ ≤
            |t| * (Kc * |t| * ‖X‖ ^ 2) := mul_le_mul_of_nonneg_left hray hat.le
          _ = Kc * |t| ^ 2 * ‖X‖ ^ 2 := by ring
      have hXs : X = (Z0 + Zl θs) + (Zl (θ - θs) + w) := by
        rw [hXdef, map_sub]; abel
      have h2 : (B X).comp Zl - (A : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (Fin 4 → ℝ)) =
          (B (Zl (θ - θs) + w)).comp Zl := by
        rw [hA, hXs, map_add, ContinuousLinearMap.add_comp, add_sub_cancel_left]
      have hv : ‖Zl (θ - θs) + w‖ ≤ ζ * rθ + ρW := by
        have hd : ‖θ - θs‖ ≤ rθ := by
          have := mem_closedBall.mp hθ; rwa [dist_eq_norm] at this
        calc ‖Zl (θ - θs) + w‖ ≤ ‖Zl‖ * ‖θ - θs‖ + ‖w‖ :=
              (norm_add_le _ _).trans (add_le_add (Zl.le_opNorm _) le_rfl)
          _ ≤ ζ * rθ + ρW := add_le_add (mul_le_mul hZl hd (norm_nonneg _) hζ) hw
      have h3 : ‖(B (Zl (θ - θs) + w)).comp Zl‖ ≤ Kc * (ζ * rθ + ρW) * ζ := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        refine mul_le_mul ?_ hZl (norm_nonneg _) (by positivity)
        exact (B.le_opNorm _).trans (mul_le_mul (hb hδ0) hv (norm_nonneg _) hKc)
      have e : fderiv ℝ (ThX D σ δ cι) (t • X) ∘L Zl -
          t • (A : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (Fin 4 → ℝ)) =
          (fderiv ℝ (ThX D σ δ cι) (t • X) - t • B X) ∘L Zl +
            t • ((B X).comp Zl - (A : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (Fin 4 → ℝ))) := by
        rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.smul_comp, smul_sub]; abel
      rw [e, h2]
      have hX2 : |t| ^ 2 * ‖X‖ ^ 2 ≤ |t| * (t0 * ξ ^ 2) := by
        have h0 : ‖X‖ ^ 2 ≤ ξ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hXn 2
        have h0' : |t| ≤ t0 := htt.trans ht10
        calc |t| ^ 2 * ‖X‖ ^ 2 = |t| * (|t| * ‖X‖ ^ 2) := by ring
          _ ≤ |t| * (t0 * ξ ^ 2) := mul_le_mul_of_nonneg_left
              (mul_le_mul h0' h0 (sq_nonneg _) ht0.le) hat.le
      calc ‖(fderiv ℝ (ThX D σ δ cι) (t • X) - t • B X) ∘L Zl +
            t • (B (Zl (θ - θs) + w)).comp Zl‖
          ≤ ‖fderiv ℝ (ThX D σ δ cι) (t • X) - t • B X‖ * ‖Zl‖ +
              |t| * ‖(B (Zl (θ - θs) + w)).comp Zl‖ := by
            refine (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
              (le_of_eq ?_))
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ (Kc * |t| ^ 2 * ‖X‖ ^ 2) * ζ + |t| * (Kc * (ζ * rθ + ρW) * ζ) :=
            add_le_add (mul_le_mul h1 hZl (norm_nonneg _) (by positivity))
              (mul_le_mul_of_nonneg_left h3 hat.le)
        _ ≤ (Kc * (|t| * (t0 * ξ ^ 2))) * ζ + |t| * (Kc * (ζ * rθ + ρW) * ζ) := by
            have : Kc * |t| ^ 2 * ‖X‖ ^ 2 ≤ Kc * (|t| * (t0 * ξ ^ 2)) := by
              calc Kc * |t| ^ 2 * ‖X‖ ^ 2 = Kc * (|t| ^ 2 * ‖X‖ ^ 2) := by ring
                _ ≤ Kc * (|t| * (t0 * ξ ^ 2)) := mul_le_mul_of_nonneg_left hX2 hKc
            exact add_le_add (mul_le_mul_of_nonneg_right this hζ) le_rfl
        _ = η * |t| := by rw [hηdef]; ring
    -- the full right inverse
    have hβ0 : 0 ≤ CC * |t| := by positivity
    have hη8 : η ≤ 1 / 8 := by linarith only [hηc]
    have hsmall : D.p * (CC * |t|) * D.a ≤ 1 / 2 := by
      rw [hp', ha']
      have h1 : |t| ≤ τ1 := htt.trans ht1τ1
      have h6 : 2 * (CC * |t|) * a ≤ (2 * a * CC + 8 * a * ζ * CC ^ 2) * τ1 := by
        have h7 : 0 ≤ 8 * a * ζ * CC ^ 2 * τ1 := by positivity
        have h8 : 2 * a * CC * |t| ≤ 2 * a * CC * τ1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        calc 2 * (CC * |t|) * a = 2 * a * CC * |t| := by ring
          _ ≤ 2 * a * CC * τ1 := h8
          _ ≤ (2 * a * CC + 8 * a * ζ * CC ^ 2) * τ1 := by linarith only [h7]
      linarith only [h6, hτ1c]
    have hMε : 2 * (η + ‖D.P0‖ * (CC * |t|) * D.a * (2 * D.p * (CC * |t|)) * ζ / |t|) ≤
        1 / 2 := by
      rw [hp', ha']
      have e : ‖D.P0‖ * (CC * |t|) * a * (2 * 2 * (CC * |t|)) * ζ / |t| =
          ‖D.P0‖ * (4 * a * ζ * CC ^ 2) * |t| := by field_simp; ring
      rw [e]
      have h1 : |t| ≤ τ2 := htt.trans ht1τ2
      have h4 : 0 ≤ 4 * a * ζ * CC ^ 2 := by positivity
      have h2 : ‖D.P0‖ * (4 * a * ζ * CC ^ 2) * |t| ≤ 4 * a * ζ * CC ^ 2 * τ2 := by
        calc ‖D.P0‖ * (4 * a * ζ * CC ^ 2) * |t| ≤ 1 * (4 * a * ζ * CC ^ 2) * τ2 :=
              mul_le_mul (mul_le_mul_of_nonneg_right hP0n h4) h1 hat.le (by positivity)
          _ = 4 * a * ζ * CC ^ 2 * τ2 := by ring
      linarith only [hη8, h2, hτ2c]
    have hq : D.p * (CC * |t|) * D.a + D.p * (CC * |t|) * ζ * (2 * 2 / |t|) *
        (‖D.P0‖ * (CC * |t|) * D.a) ≤ 1 / 2 := by
      rw [hp', ha']
      have e : 2 * (CC * |t|) * a + 2 * (CC * |t|) * ζ * (2 * 2 / |t|) *
          (‖D.P0‖ * (CC * |t|) * a) = (2 * a * CC + 8 * a * ζ * CC ^ 2 * ‖D.P0‖) * |t| := by
        field_simp; ring
      rw [e]
      have h1 : |t| ≤ τ1 := htt.trans ht1τ1
      have h9 : 0 ≤ 8 * a * ζ * CC ^ 2 := by positivity
      have h5 : 8 * a * ζ * CC ^ 2 * ‖D.P0‖ ≤ 8 * a * ζ * CC ^ 2 :=
        mul_le_of_le_one_right h9 hP0n
      calc (2 * a * CC + 8 * a * ζ * CC ^ 2 * ‖D.P0‖) * |t|
          ≤ (2 * a * CC + 8 * a * ζ * CC ^ 2) * τ1 :=
            mul_le_mul (by linarith only [h5]) h1 hat.le (by positivity)
        _ ≤ 1 / 2 := hτ1c
    have hP0P : ∀ f, D.P0 (D.P f) = 0 := fun f => by
      rw [hP0, hP]; funext c; exact meanG_PL r f c
    obtain ⟨S, hS, hSb⟩ := full_inverse_at D hrD hNaD hP0P hι hx'
      (hΘ _ hxball) Zl hZl hβ A hM2 ht hblock hsmall hMε hq
    rw [hrec] at hS
    refine ⟨θ, hθ, hzero, hnorm', ?_, fun θ' hθ' h' => huniq θ' hθ' (by rw [hrec]; exact h'),
      ⟨S, hS, fun f => ?_⟩, hxδ, hyσ⟩
    · rw [LyapunovSchmidt.RangeData.meanMap]
      exact (congrArg D.P0 hzero).trans (map_zero _)
    · have h := hSb f
      rw [hp', ha', hP, hP0] at h
      exact h.trans (inv_bound_aux ha.le hζ hCC (norm_P0L_le r) (norm_nonneg _) (norm_nonneg _)
        (norm_nonneg _) hat (htt.trans ht11))
  refine ⟨D, hfullCH, hDL, hR, hP, hP0, finrank_XH r, finrank_YH r,
    fun t ht htt W hW hWn => ?_⟩
  obtain ⟨θ, hθ, hzero, hnorm, hmean, huniq, ⟨S, hS, hSb⟩, hxδ, hyσ⟩ := key t ht htt W hW hWn
  have hLW : D.L W = 0 := by rw [hDL]; exact hW
  have hLx : D.L (t • (Zs0 r + ZsL r θ + W)) = 0 := by
    rw [map_smul, map_add, hDL (Zs0 r + ZsL r θ), LHfun_seed, hLW, add_zero, smul_zero]
  have hsolS := D.sol_spec hrD hLx hxδ.le
  have hIball : prec D σ δ t θ W ∈ ball (0 : XH N r) D.ρ :=
    mem_ball_zero_iff.mpr ((D.norm_arg_le hxδ.le hsolS.1).trans_lt hrD.2.2.1)
  have hderiv : HasFDerivAt D.full (D.L + D.DN (prec D σ δ t θ W)) (prec D σ δ t θ W) :=
    D.L.hasFDerivAt.add (D.hN _ hIball)
  have hfd : fderiv ℝ D.full (prec D σ δ t θ W) = D.L + D.DN (prec D σ δ t θ W) :=
    hderiv.fderiv
  have hS' : ∀ f, fderiv ℝ D.full (prec D σ δ t θ W) (S f) = f := by
    intro f; rw [hfd]; exact hS f
  have hrange : (fderiv ℝ D.full (prec D σ δ t θ W)).range = ⊤ :=
    LinearMap.range_eq_top.mpr fun f => ⟨S f, hS' f⟩
  have hker : Module.finrank ℝ (fderiv ℝ D.full (prec D σ δ t θ W)).ker = 8 * N ^ 3 := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (fderiv ℝ D.full (prec D σ δ t θ W) : XH N r →ₗ[ℝ] YH N r)
    have h2 : LinearMap.range (fderiv ℝ D.full (prec D σ δ t θ W) : XH N r →ₗ[ℝ] YH N r) = ⊤ :=
      hrange
    rw [h2, finrank_top, finrank_YH, finrank_XH] at h
    have h3 : Module.finrank ℝ (fderiv ℝ D.full (prec D σ δ t θ W)).ker =
        Module.finrank ℝ
          (LinearMap.ker (fderiv ℝ D.full (prec D σ δ t θ W) : XH N r →ₗ[ℝ] YH N r)) := rfl
    rw [h3]
    omega
  have hstrict : HasStrictFDerivAt D.full (fderiv ℝ D.full (prec D σ δ t θ W))
      (prec D σ δ t θ W) :=
    (hFbD.contDiffAt isOpen_ball hIball).hasStrictFDerivAt (by simp)
  refine ⟨θ, hθ, hzero, hnorm, hmean, huniq, ⟨S, hS', hSb⟩, hrange, hker,
    ⟨hstrict.implicitToOpenPartialHomeomorph D.full _ hrange,
      hstrict.mem_implicitToOpenPartialHomeomorph_source hrange,
      fun X => hstrict.implicitToOpenPartialHomeomorph_fst hrange X⟩, fun hWlt => ?_⟩
  -- relative openness in the zero set
  obtain ⟨hPKI, hLI⟩ := hPKrec t θ W hLW
  set Zθ : XH N r := Zs0 r + ZsL r θ with hZθ
  have hcont1 : Continuous fun Y : XH N r => t⁻¹ • PK D Y - Zθ :=
    (((PK D).continuous.const_smul t⁻¹).sub (continuous_const (y := Zθ)) :)
  set U : Set (XH N r) := {Y | ‖t⁻¹ • PK D Y - Zθ‖ < cι * ρW} ∩ {Y | ‖D.L Y‖ < σ} ∩
    {Y | ‖PK D Y‖ < δ} with hUdef
  have hUo : IsOpen U :=
    ((isOpen_lt (continuous_norm.comp hcont1) continuous_const).inter
      (isOpen_lt (continuous_norm.comp D.L.continuous) continuous_const)).inter
      (isOpen_lt (continuous_norm.comp (PK D).continuous) continuous_const)
  have hIU : prec D σ δ t θ W ∈ U := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show ‖t⁻¹ • PK D (prec D σ δ t θ W) - Zθ‖ < cι * ρW
      rw [hPKI, smul_smul, inv_mul_cancel₀ ht, one_smul, hZθ, add_sub_cancel_left]
      exact hWlt
    · show ‖D.L (prec D σ δ t θ W)‖ < σ
      rw [hLI]; exact hyσ
    · show ‖PK D (prec D σ δ t θ W)‖ < δ
      rw [hPKI]; exact hxδ
  refine ⟨U, hUo.mem_nhds hIU, fun Y hY hYz => ?_⟩
  obtain ⟨⟨hY1, hY2⟩, hY3⟩ := hY
  set z := PK D Y with hzdef
  set W' := t⁻¹ • z - Zθ with hW'def
  have hLz : D.L z = 0 := L_PK D Y
  have hLW' : D.L W' = 0 := by
    rw [hW'def, map_sub, map_smul, hLz, smul_zero, zero_sub, neg_eq_zero, hZθ, hDL]
    exact LHfun_seed r θ
  have hW'r : LHfun r W' = 0 := by rw [← hDL]; exact hLW'
  have hz : t • (Zs0 r + ZsL r θ + W') = z := by
    rw [hW'def, ← hZθ, add_sub_cancel, smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hY' : Y = z + D.R (D.L Y) := by rw [hzdef, PK_apply, sub_add_cancel]
  have hyS : D.L Y ∈ D.S σ := ⟨D.hPL Y, hY2.le⟩
  have hyeq : D.P (D.full (z + D.R (D.L Y))) = 0 := by rw [← hY', hYz, map_zero]
  have hsol : D.L Y = D.sol σ δ z := D.eq_sol hrD hLz hY3.le hyS hyeq
  have hYrec : Y = prec D σ δ t θ W' := by
    rw [prec, hz, ← hsol]; exact hY'
  have hW'n : ‖W'‖ ≤ cι * ρW := hY1.le
  refine ⟨W', hW'r, hW'n, hYrec, fun ϑ' hϑ' h' => ?_⟩
  obtain ⟨θ', -, -, -, -, huniq', -⟩ := key t ht htt W' hW'r hW'n
  have h1 := huniq' θ hθ (by rw [← hYrec]; exact hYz)
  rw [huniq' ϑ' hϑ' h', h1]

end RenewalGeometry.ExactPhaseAction.PreparedChart

namespace RenewalGeometry.ExactPhaseAction.PreparedChart

open InitialCalculus InitialRange

/-- Non-vacuity of `supp_action_prepared_chart`: some admissible cutoff carries an exact prepared
zero (with the free record `W = 0` and `t = t₀`). -/
example : ∃ (N : ℕ) (_ : NeZero N) (D : RD N 2) (σ δ t : ℝ) (ϑ : ℝ × (Fin 3 → ℝ)),
    t ≠ 0 ∧ D.full (prec D σ δ t ϑ 0) = 0 ∧
      (fderiv ℝ D.full (prec D σ δ t ϑ 0)).range = ⊤ := by
  obtain ⟨M, ρ', σ, δ, t0, ρW, rθ, Cr, Cinv, h₀, ht0, hρW, -, -, -, hh₀, hall⟩ :=
    supp_action_prepared_chart 2 le_rfl
  obtain ⟨N, _, hNo, hN⟩ := exists_odd_hN_lt hh₀
  obtain ⟨D, -, hDL, -, -, -, -, -, hmain⟩ := hall N hNo hN
  have h0 : LHfun 2 (0 : XH N 2) = 0 := (hDL 0).symm.trans (map_zero _)
  obtain ⟨ϑ, -, hz, -, -, -, -, hr, -⟩ := hmain t0 ht0.ne' (by rw [abs_of_pos ht0]) 0 h0
    (by rw [norm_zero]; exact hρW.le)
  exact ⟨N, inferInstance, D, σ, δ, t0, ϑ, ht0.ne', hz, hr⟩

end RenewalGeometry.ExactPhaseAction.PreparedChart
