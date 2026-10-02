/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.GridFaaDiBrunoHigherOrder
import RenewalGeometry.Gravity.GowdySplitCharacteristicStability
import RenewalGeometry.Gravity.GowdyReferenceVacuum

/-!
# The `C^r_ℓ` state error of the Gowdy split scheme for every `r`
  (`prop:supp-gowdy-residual-control`, `eq:supp-gowdy-state-error`; `eq:supp-gowdy-pathwise-c1`;
  `thm:main-gowdy-regulator` (G2), (G3); emergent-spacetime supplement)

The concrete Gowdy symmetric splitting (`Gravity/GowdyStaggeredMomentumExact.lean`: implicit-
midpoint source half-steps of `eq:supp-gowdy-source-flow`, the characteristic transport
`eq:supp-gowdy-transport`, synchronized `h = ℓ = 2π/N`) is an instance of the abstract smooth
characteristic setup of `DiscreteAnalysis/GridFaaDiBrunoHigherOrder.lean`
(`exists_gowdySmoothSetup`): the source field is `C^∞` on `{t > 0}` with bounded derivatives on
bounded subsets of `{t > t₀/4}`, the densities `g± = |w±|²` are polynomials depending only on
`Π±U`, and a smooth solution of `eq:supp-gowdy-frame-system` gives a smooth periodic reference
`X_* = (√t(a,b,c,d), P, Q, t; λ)` in characteristic form.

* `GowdyFrameSolution.state_error_crNorm` (**`eq:supp-gowdy-state-error` for every `r`**): for a
  smooth solution, every chart radius `R ≥ chartRadius` and every enforced `C^r_ℓ` envelope radius
  `R_env`, there are `C, ℓ₀ > 0` such that for `h = ℓ = 2π/N ≤ ℓ₀` and every numerical history
  `X_{n+1} = Φ_h(X_n) + r_n` realised by split steps in the envelope,
  `‖X_n - 𝖲_ℓX_*(t_n)‖_{r,∞,ℓ} ≤ C (‖X₀ - 𝖲_ℓX_*(t₀)‖_{r,∞,ℓ} + Σ_{k<n} ‖r_k‖_{r,∞,ℓ} + h²)`.
* `GowdyFrameSolution.state_error_crNorm_flux`: the manuscript's form
  `max_n ‖X_n - 𝖲_ℓX_*(t_n)‖_{r,∞,ℓ} ≤ C (ε₀ + h² + √𝓕_h)` with
  `𝓕_h = ℓ^{-(2r+1)} Σ_k ‖r_k‖²_{2,ℓ}/(2h)` (`eq:supp-gowdy-residual-energy`).
* `GowdyFrameSolution.pathwise_c1` (**`eq:supp-gowdy-pathwise-c1`**): with the offset cap
  `charDist(X_{n+1}, B_n) ≤ c₀h⁴` (`eq:supp-gowdy-offset-cap`) and initial `C¹_h` error `≤ c₁h²`,
  `max_n ‖X_n - 𝖲_hX_*(t_n)‖_{1,∞,h} ≤ C h²`.
* `GowdySmoothReference.readout_full_curvature_of_envelope` (**(G3) for the scheme's histories**):
  composing `pathwise_c1` with `readout_full_curvature_vacuum`, every history in the `C¹`
  envelope with the offset cap and initial `C¹_h` error `O(h²)` has
  `eq:main-gowdy-full-curvature` and `Ric(g_h) = O(h)` cellwise.

The envelope is the manuscript's "enforced offset envelope": the stage midpoints and the
transported inputs lie in the chart `{‖v‖ ≤ R, t ≥ t₀/2}` and their forward differences of order
`1, …, r` are bounded by `R_env` (`GowdyEnvR`).
-/

open Set Finset
open scoped BigOperators ContDiff

set_option linter.unusedSectionVars false

namespace RenewalGeometry.GowdyStaggered

noncomputable section

open GridFaaDiBruno IteratedDerivBounds CharStability

/-! ### Smoothness of the Gowdy data -/

theorem contDiff_regClock_infty (t₀ : ℝ) : ContDiff ℝ ∞ (regClock t₀) := by
  unfold regClock
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (hs.comp ((contDiff_id.sub contDiff_const).div_const _)))

theorem contDiff_regField_infty {t₀ : ℝ} (h0 : 0 < t₀) : ContDiff ℝ ∞ (regField t₀) := by
  have hT : ContDiff ℝ ∞ (fun v : StateVec => regClock t₀ v.2.2.2) :=
    (contDiff_regClock_infty t₀).comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
  have hTne : ∀ v : StateVec, regClock t₀ v.2.2.2 ≠ 0 := fun v => (regClock_pos h0 _).ne'
  have hS : ContDiff ℝ ∞ (fun v : StateVec => Real.sqrt (regClock t₀ v.2.2.2)) :=
    hT.sqrt hTne
  have hSne : ∀ v : StateVec, Real.sqrt (regClock t₀ v.2.2.2) ≠ 0 :=
    fun v => (Real.sqrt_pos.mpr (regClock_pos h0 _)).ne'
  have h2T : ContDiff ℝ ∞ (fun v : StateVec => 2 * regClock t₀ v.2.2.2) := contDiff_const.mul hT
  have h2Tne : ∀ v : StateVec, 2 * regClock t₀ v.2.2.2 ≠ 0 :=
    fun v => mul_ne_zero two_ne_zero (hTne v)
  have hu : ∀ i : Fin 4, ContDiff ℝ ∞ (fun v : StateVec => v.1 i) :=
    fun i => (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hP : ContDiff ℝ ∞ (fun v : StateVec => v.2.1) := contDiff_fst.comp contDiff_snd
  unfold regField
  refine ContDiff.prodMk ?_ (ContDiff.prodMk ?_ (ContDiff.prodMk ?_ contDiff_const))
  · refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · simp only [sourceField, Fin.zero_eta, Matrix.cons_val_zero]
      exact (((hu 0).neg).div h2T h2Tne).add
        ((((hu 2).pow 2).sub ((hu 3).pow 2)).div hS hSne)
    · simp only [sourceField, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact (hu 1).div h2T h2Tne
    · simp only [sourceField]
      simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      exact (((hu 2).neg).div h2T h2Tne).add
        (((((hu 0).neg).mul (hu 2)).add ((hu 1).mul (hu 3))).div hS hSne)
    · simp only [sourceField]
      simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      exact ((hu 3).div h2T h2Tne).add
        ((((hu 0).mul (hu 3)).sub ((hu 1).mul (hu 2))).div hS hSne)
  · exact (hu 0).div hS hSne
  · exact ((Real.contDiff_exp.comp hP.neg).mul (hu 2)).div hS hSne

theorem contDiff_densPlus : ContDiff ℝ ∞ densPlus := by
  have hu : ∀ i : Fin 4, ContDiff ℝ ∞ (fun v : StateVec => v.1 i) :=
    fun i => (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have e : densPlus = fun v : StateVec => ((v.1 0 + v.1 1) ^ 2 + (v.1 2 + v.1 3) ^ 2) / 2 := by
    funext v; exact gPlus_eq v.1
  rw [e]
  exact ((((hu 0).add (hu 1)).pow 2).add (((hu 2).add (hu 3)).pow 2)).div_const _

theorem contDiff_densMinus : ContDiff ℝ ∞ densMinus := by
  have hu : ∀ i : Fin 4, ContDiff ℝ ∞ (fun v : StateVec => v.1 i) :=
    fun i => (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have e : densMinus = fun v : StateVec => ((v.1 0 - v.1 1) ^ 2 + (v.1 2 - v.1 3) ^ 2) / 2 := by
    funext v; exact gMinus_eq v.1
  rw [e]
  exact ((((hu 0).sub (hu 1)).pow 2).add (((hu 2).sub (hu 3)).pow 2)).div_const _

theorem densPlus_projPlus (v : StateVec) : densPlus (projPlus v) = densPlus v := by
  simp only [densPlus, gPlus_eq, projPlus_apply]
  simp

theorem densMinus_projMinus (v : StateVec) : densMinus (projMinus v) = densMinus v := by
  simp only [densMinus, gMinus_eq, projMinus_apply]
  simp

/-- Uniform derivative bounds on a bounded open set for a map agreeing with a globally `C^∞`
map on an open neighbourhood. -/
theorem exists_derivBound_of_eqOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F}
    (hg : ContDiff ℝ ∞ g) {O U : Set E} (hO : IsOpen O) (hUO : U ⊆ O) (hfg : EqOn f g O)
    {r : ℝ} (hUr : U ⊆ Metric.closedBall 0 r) (m : ℕ) : ∃ M, 0 ≤ M ∧ DerivBound f U m M := by
  have hcont : Continuous fun x => ∑ k ∈ range (m + 1), ‖iteratedFDeriv ℝ k g x‖ :=
    continuous_finset_sum _ fun k _ =>
      (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) r).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, ⟨(hg.contDiffOn).congr fun x hx => hfg (hUO hx),
    fun x hx k hk => ?_⟩⟩
  have heq : iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k g x :=
    (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ)
      (Filter.eventually_of_mem (hO.mem_nhds (hUO hx)) fun y hy => hfg hy) k).eq_of_nhds
  rw [heq]
  have h1 := hC x (hUr hx)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)] at h1
  have h2 : ‖iteratedFDeriv ℝ k g x‖ ≤ ∑ k ∈ range (m + 1), ‖iteratedFDeriv ℝ k g x‖ :=
    Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k g x‖) (fun k _ => norm_nonneg _)
      (mem_range.2 (Nat.lt_succ_of_le hk))
  exact h2.trans (h1.trans (le_max_left _ _))

/-! ### The Gowdy characteristic data -/

/-- The Gowdy characteristic data: projections onto `w⁺`, `w⁻`, `(P, Q, t)`, the source field
`eq:supp-gowdy-source-flow` and the densities `g± = |w±|²`. -/
def gowdyData : CharData StateVec :=
  ⟨projPlus, projMinus, projZero, localFieldVec, densPlus, densMinus⟩

theorem gowdyData_proj : gowdyData.Proj :=
  ⟨proj_sum, norm_projPlus_le, norm_projMinus_le, norm_projZero_le, projPlus_projPlus,
    projPlus_projMinus, projPlus_projZero, projMinus_projPlus, projMinus_projMinus,
    projMinus_projZero, projZero_projPlus, projZero_projMinus, projZero_projZero⟩

/-- A Gowdy grid state as an abstract grid state. -/
def toCG {N : ℕ} (X : GridState N) : CGrid StateVec N := ⟨fun j => (X.site j).toVec, X.lam⟩

theorem toCG_isSrc {N : ℕ} {σ : ℝ} {X Y : GridState N} (h : IsSourceStep σ X Y) :
    gowdyData.IsSrc σ (toCG X) (toCG Y) :=
  ⟨fun j => (isMidpointStep_iff_toVec _ _ _).1 (h.1 j), h.2⟩

theorem toCG_transport {N : ℕ} [NeZero N] (ℓ : ℝ) (X : GridState N) :
    toCG (transport ℓ X) = gowdyData.transport ℓ (toCG X) :=
  CGrid.ext (funext fun j => transport_site_toVec ℓ X j) (funext fun j => transport_lam_apply ℓ X j)

theorem toCG_isSplit {N : ℕ} [NeZero N] {ℓ : ℝ} {X A B : GridState N}
    (h : CharStability.IsSplitStep ℓ X A B) : gowdyData.IsSplit ℓ (toCG X) (toCG A) (toCG B) := by
  refine ⟨toCG_isSrc h.1, ?_⟩
  rw [← toCG_transport]
  exact toCG_isSrc h.2

theorem errA_toCG {N : ℕ} (X Y : GridState N) : CharData.errA (toCG X) (toCG Y) = errArr X Y :=
  rfl

/-- **The `C^r_ℓ` envelope of a Gowdy split step** `X → A → B`: the stage-one midpoints
`(X_j + A_j)/2`, the transported inputs `A_j` and the stage-three midpoints
`((TA)_j + B_j)/2` lie in the chart `{‖v‖ ≤ R, t ≥ t₀/2}`, and their forward differences
`D₊ⁱ`, `1 ≤ i ≤ r`, have sup norm at most `R_env` (the enforced offset envelope of
`prop:supp-gowdy-residual-control`). -/
def GowdyEnvR {N : ℕ} [NeZero N] (r : ℕ) (t₀ R Renv ℓ : ℝ) (X A B : GridState N) : Prop :=
  gowdyData.EnvK r (chartK t₀ R) Renv ℓ (toCG X) (toCG A) (toCG B)

/-! ### The Gowdy smooth setup -/

namespace GowdyFrameSolution

variable {t₀ t₁ : ℝ} (sol : GowdyFrameSolution t₀ t₁)

/-- The frame fields and the potentials of a solution are `C^∞` (the "smooth solution" of
`thm:main-gowdy-regulator`). -/
structure IsSmooth : Prop where
  a : ContDiff ℝ ∞ sol.a
  b : ContDiff ℝ ∞ sol.b
  c : ContDiff ℝ ∞ sol.c
  d : ContDiff ℝ ∞ sol.d
  P : ContDiff ℝ ∞ sol.P
  Q : ContDiff ℝ ∞ sol.Q
  lam : ContDiff ℝ ∞ sol.lam

theorem IsSmooth.Z {sol : GowdyFrameSolution t₀ t₁} (hs : sol.IsSmooth) (h0 : 0 < t₀) :
    ContDiff ℝ ∞ sol.Z := by
  have hsq : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.sqrt (regClock t₀ p.1)) :=
    ((contDiff_regClock_infty t₀).comp contDiff_fst).sqrt fun p => (regClock_pos h0 _).ne'
  have hfr : ∀ i, ContDiff ℝ ∞ (sol.fr i) := by
    intro i; fin_cases i
    exacts [hs.a, hs.b, hs.c, hs.d]
  exact ContDiff.prodMk (contDiff_pi.2 fun i => hsq.mul (hfr i))
    (hs.P.prodMk (hs.Q.prodMk contDiff_fst))

/-- **The Gowdy scheme is a smooth characteristic setup** of every order `m`, with chart
`chartK t₀ R` (`R ≥ chartRadius`), tube radius `min 1 (t₀/2)` and any envelope radius at least
`R_env`. -/
theorem exists_gowdySmoothSetup (hs : sol.IsSmooth) (h0 : 0 < t₀) (m : ℕ) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) (Renv : ℝ) :
    ∃ (p : Params) (S : SmoothSetup StateVec p), p.t₀ = t₀ ∧ p.t₁ = t₁ ∧ p.m = m ∧
      Renv ≤ p.R ∧ S.c = gowdyData ∧ S.K = chartK t₀ R ∧ S.Z = sol.Z ∧ S.lam = sol.lam := by
  have hR0 : 0 ≤ R := by linarith [(sol.chartRadius_spec h0).1]
  have hZ := hs.Z h0
  -- the sets
  set UF : Set StateVec := {v | t₀ / 4 < v.2.2.2} ∩ Metric.ball 0 (R + 1) with hUF
  set Ug : Set StateVec := Metric.ball 0 (R + 1) with hUg
  have hcont_t : Continuous fun v : StateVec => v.2.2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hUFo : IsOpen UF := (isOpen_lt continuous_const hcont_t).inter Metric.isOpen_ball
  have hUFc : Convex ℝ UF := by
    refine Convex.inter ?_ (convex_ball _ _)
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hx hy ⊢
    rcases eq_or_lt_of_le ha with h | h
    · subst h; simp only [zero_add] at hab; subst hab; simpa using hy
    · nlinarith [mul_pos h (sub_pos.2 hx), mul_nonneg hb (sub_pos.2 hy).le]
  have hUFb : UF ⊆ Metric.closedBall 0 (R + 1) := fun v hv => Metric.ball_subset_closedBall hv.2
  have hUgb : Ug ⊆ Metric.closedBall 0 (R + 1) := Metric.ball_subset_closedBall
  -- derivative bounds of the field and densities
  obtain ⟨MF, hMF, hF⟩ := exists_derivBound_of_eqOn (f := localFieldVec)
    (contDiff_regField_infty (t₀ := t₀ / 2) (by linarith)) (isOpen_lt continuous_const hcont_t)
    (fun v hv => hv.1) (fun v hv => (regField_eq (by linarith) (by
      have : t₀ / 4 < v.2.2.2 := hv
      show t₀ / 2 / 2 ≤ v.2.2.2; linarith)).symm) hUFb m
  obtain ⟨Mp, hMp, hgp⟩ := exists_derivBound_of_eqOn (f := densPlus) contDiff_densPlus isOpen_univ
    (subset_univ Ug) (fun _ _ => rfl) hUgb m
  obtain ⟨Mm, hMm, hgm⟩ := exists_derivBound_of_eqOn (f := densMinus) contDiff_densMinus
    isOpen_univ (subset_univ Ug) (fun _ _ => rfl) hUgb m
  set M := max MF (max Mp Mm)
  -- reference bounds
  have hcontD : Continuous fun q : ℝ × ℝ => ∑ k ∈ range (m + 1),
      (‖iteratedFDeriv ℝ k sol.Z q‖ + ‖iteratedFDeriv ℝ k sol.lam q‖) :=
    continuous_finset_sum _ fun k _ =>
      (hZ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.add
        ((hs.lam.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm)
  obtain ⟨D, hD0, hD⟩ := exists_bound_of_periodic _ hcontD (fun q => by
    simp only [iteratedFDeriv_periodic sol.Z sol.periodic_Z,
      iteratedFDeriv_periodic sol.lam sol.periodic_lam]) t₀ t₁
  have hDk : ∀ q : ℝ × ℝ, q.1 ∈ Icc t₀ t₁ → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k sol.Z q‖ ≤ D ∧ ‖iteratedFDeriv ℝ k sol.lam q‖ ≤ D := by
    intro q hq k hk
    have h1 := hD q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => by positivity)] at h1
    have h2 := Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k sol.Z q‖ +
      ‖iteratedFDeriv ℝ k sol.lam q‖) (fun k _ => by positivity) (mem_range.2 (Nat.lt_succ_of_le hk))
    constructor <;> linarith [norm_nonneg (iteratedFDeriv ℝ k sol.Z q),
      norm_nonneg (iteratedFDeriv ℝ k sol.lam q)]
  set p : Params := ⟨t₀, t₁, min 1 (t₀ / 2), M, D, max Renv (D + 1), m⟩
  have hgood : p.Good := ⟨lt_min one_pos (by linarith), min_le_left _ _,
    le_max_of_le_left hMF, hD0, le_max_right _ _⟩
  have hKUF : chartK t₀ R ⊆ UF := fun v hv => ⟨by have := hv.2; show t₀ / 4 < v.2.2.2; linarith,
    mem_ball_zero_iff.2 (by linarith [hv.1])⟩
  have hKUg : chartK t₀ R ⊆ Ug := fun v hv => mem_ball_zero_iff.2 (by linarith [hv.1])
  refine ⟨p, {
    c := gowdyData
    K := chartK t₀ R
    UF := UF
    Ug := Ug
    Z := sol.Z
    lam := sol.lam
    proj := gowdyData_proj
    gp_proj := densPlus_projPlus
    gm_proj := densMinus_projMinus
    UF_open := hUFo
    UF_convex := hUFc
    Ug_open := Metric.isOpen_ball
    Ug_convex := convex_ball _ _
    K_convex := convex_chartK t₀ R
    K_UF := hKUF
    K_Ug := hKUg
    Pp_K := fun v hv => mem_ball_zero_iff.2 ((norm_projPlus_le v).trans_lt (by linarith [hv.1]))
    Pm_K := fun v hv => mem_ball_zero_iff.2 ((norm_projMinus_le v).trans_lt (by linarith [hv.1]))
    F_bd := hF.mono le_rfl (le_max_left _ _)
    gp_bd := hgp.mono le_rfl ((le_max_left _ _).trans (le_max_right _ _))
    gm_bd := hgm.mono le_rfl ((le_max_right _ _).trans (le_max_right _ _))
    Z_smooth := hZ
    lam_smooth := hs.lam
    Z_per := sol.periodic_Z
    lam_per := sol.periodic_lam
    Z_bd := fun q hq i _ hi => (hDk q hq i hi).1
    lam_bd := fun q hq i _ hi => (hDk q hq i hi).2
    char_plus := fun q hq => sol.char_plus h0 hq
    char_minus := fun q hq => sol.char_minus h0 hq
    char_zero := fun q hq => sol.char_zero h0 hq
    char_lam := fun q hq => sol.char_lam h0 hq
    tube := fun q hq v hv => by
      have hRq := (sol.chartRadius_spec h0).2 q hq
      have hδ1 : ‖v - sol.Z q‖ ≤ 1 := hv.trans (min_le_left _ _)
      have hδ2 : ‖v - sol.Z q‖ ≤ t₀ / 2 := hv.trans (min_le_right _ _)
      refine ⟨?_, ?_⟩
      · calc ‖v‖ = ‖(v - sol.Z q) + sol.Z q‖ := by rw [sub_add_cancel]
          _ ≤ ‖v - sol.Z q‖ + ‖sol.Z q‖ := norm_add_le _ _
          _ ≤ R := by linarith
      · have ht := abs_t_le (v - sol.Z q)
        have hZt : (sol.Z q).2.2.2 = q.1 := rfl
        simp only [Prod.snd_sub, hZt] at ht
        have := (abs_le.1 (ht.trans hδ2)).1
        linarith [hq.1]
    good := hgood }, rfl, rfl, rfl, le_max_left _ _, rfl, rfl, rfl, rfl⟩

/-! ### The `C^r_ℓ` state error -/

theorem sample_toCG (N : ℕ) (τ : ℝ) :
    toCG (sol.sample N τ) = sampleGrid sol.Z sol.lam N τ :=
  CGrid.ext (funext fun j => by simp [toCG, sample, sampleGrid]) rfl

/-- **`eq:supp-gowdy-state-error` for every `r`, residual-sum form.**  For a smooth solution of
the frame system on `[t₀, t₁] × 𝕋¹` (`t₀ > 0`), a chart radius `R ≥ chartRadius` and an enforced
`C^r_ℓ` envelope radius `R_env`, there are `C ≥ 0` and `ℓ₀ > 0` such that for `h = ℓ = 2π/N ≤ ℓ₀`,
`[τ₀, τ₀ + n₀ℓ] ⊆ [t₀, t₁]`, and every numerical history `X_n` realised by Gowdy split steps
`X_n → A_n → B_n` in the envelope (`GowdyEnvR r`), with arbitrary next states `X_{n+1}`
(residual arrays `r_n = X_{n+1} - B_n`):
`‖X_n - 𝖲_ℓX_*(τ₀+nℓ)‖_{r,∞,ℓ} ≤ C (‖X₀ - 𝖲_ℓX_*(τ₀)‖_{r,∞,ℓ} + Σ_{k<n} ‖r_k‖_{r,∞,ℓ} + h²)`. -/
theorem state_error_crNorm (hs : sol.IsSmooth) (h0 : 0 < t₀) (r : ℕ) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) (Renv : ℝ) :
    ∃ C ℓ₀ : ℝ, 0 ≤ C ∧ 0 < ℓ₀ ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ), t₀ ≤ τ₀ → τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁ →
      ∀ X A B : ℕ → GridState N,
        (∀ n < n₀, CharStability.IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
          GowdyEnvR r t₀ R Renv (2 * Real.pi / N) (X n) (A n) (B n)) →
        ∀ n ≤ n₀, PeriodicGridResidual.crNorm r (2 * Real.pi / N)
            (errArr (X n) (sol.sample N (τ₀ + n * (2 * Real.pi / N)))) ≤
          C * (PeriodicGridResidual.crNorm r (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) +
            ∑ i ∈ range n, PeriodicGridResidual.crNorm r (2 * Real.pi / N)
              (errArr (X (i + 1)) (B i)) + (2 * Real.pi / N) ^ 2) := by
  obtain ⟨p, S, hp0, hp1, hpm, hpR, hc, hK, hZ, hl⟩ :=
    sol.exists_gowdySmoothSetup hs h0 (3 + r) hR Renv
  set T := max (t₁ - t₀) 0
  have hgood := S.good
  have hK0 : 0 ≤ SmoothSetup.rateR r p :=
    Finset.sum_nonneg fun k _ => Params.rate_nonneg hgood k
  have hC0 : 0 ≤ SmoothSetup.consR r p :=
    Finset.sum_nonneg fun k _ => Params.cons_nonneg hgood k
  have hT0' : 0 ≤ T := le_max_right _ _
  refine ⟨3 * (1 + SmoothSetup.consR r p * T) * Real.exp (SmoothSetup.rateR r p * T),
    Params.step r p, mul_nonneg (mul_nonneg (by norm_num) (add_nonneg zero_le_one
      (mul_nonneg hC0 hT0'))) (Real.exp_pos _).le, Params.step_pos hgood r, ?_⟩
  intro N _ hN τ₀ n₀ hτ₀ hn₀ X A B hstep n hn
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hstep' : ∀ n < n₀, S.c.IsSplit ℓ (toCG (X n)) (toCG (A n)) (toCG (B n)) ∧
      S.c.EnvK r S.K p.R ℓ (toCG (X n)) (toCG (A n)) (toCG (B n)) := by
    intro n hn
    rw [hc, hK]
    refine ⟨toCG_isSplit (hstep n hn).1, ?_⟩
    obtain ⟨h0', hd⟩ := (hstep n hn).2
    exact ⟨h0', fun i h1 h2 => ⟨((hd i h1 h2).1).trans hpR, ((hd i h1 h2).2.1).trans hpR,
      ((hd i h1 h2).2.2).trans hpR⟩⟩
  have h := S.global_error_crNorm r (by omega) hN τ₀ n₀ (by rw [hp0]; exact hτ₀)
    (by rw [hp1]; exact hn₀) (fun n => toCG (X n)) (fun n => toCG (A n)) (fun n => toCG (B n))
    hstep' n hn
  rw [hZ, hl, ← sol.sample_toCG, ← sol.sample_toCG, errA_toCG, errA_toCG, hp1, hp0] at h
  simp only [errA_toCG] at h
  refine h.trans ?_
  set e0 := PeriodicGridResidual.crNorm r ℓ (errArr (X 0) (sol.sample N τ₀))
  set sr := ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errArr (X (i + 1)) (B i))
  have he0 : 0 ≤ e0 := PeriodicGridResidual.crNorm_nonneg _ _ _
  have hsr : 0 ≤ sr := Finset.sum_nonneg fun i _ => PeriodicGridResidual.crNorm_nonneg _ _ _
  have hT : t₁ - t₀ ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := le_max_right _ _
  have hexp : Real.exp (SmoothSetup.rateR r p * (t₁ - t₀)) ≤
      Real.exp (SmoothSetup.rateR r p * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hK0)
  have hin : e0 + sr + SmoothSetup.consR r p * (t₁ - t₀) * ℓ ^ 2 ≤
      (1 + SmoothSetup.consR r p * T) * (e0 + sr + ℓ ^ 2) := by
    have h1 : SmoothSetup.consR r p * (t₁ - t₀) * ℓ ^ 2 ≤ SmoothSetup.consR r p * T * ℓ ^ 2 := by
      gcongr
    have h2 : 0 ≤ SmoothSetup.consR r p * T := by positivity
    nlinarith [sq_nonneg ℓ, mul_nonneg h2 he0, mul_nonneg h2 hsr]
  have hb0 : 0 ≤ (1 + SmoothSetup.consR r p * T) * (e0 + sr + ℓ ^ 2) :=
    mul_nonneg (add_nonneg zero_le_one (mul_nonneg hC0 hT0))
      (add_nonneg (add_nonneg he0 hsr) (sq_nonneg _))
  calc 3 * ((e0 + sr + SmoothSetup.consR r p * (t₁ - t₀) * ℓ ^ 2) *
        Real.exp (SmoothSetup.rateR r p * (t₁ - t₀)))
      ≤ 3 * (((1 + SmoothSetup.consR r p * T) * (e0 + sr + ℓ ^ 2)) *
        Real.exp (SmoothSetup.rateR r p * T)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hin hexp (Real.exp_pos _).le hb0) (by norm_num)
    _ = _ := by ring

/-- **`eq:supp-gowdy-state-error` for every `r`** in the manuscript's form: there are `C` and
`ℓ₀ > 0` such that `max_{n ≤ n₀} ‖X_n - 𝖲_ℓX_*(t_n)‖_{r,∞,ℓ} ≤ C (ε₀ + h² + √𝓕_h)`, where
`ε₀ = ‖X₀ - 𝖲_ℓX_*(t₀)‖_{r,∞,ℓ}` and `𝓕_h = ℓ^{-(2r+1)} Σ_{k<n} ‖r_k‖²_{2,ℓ}/(2h)`
(`eq:supp-gowdy-residual-energy`), for every history in the enforced `C^r_ℓ` envelope. -/
theorem state_error_crNorm_flux (hs : sol.IsSmooth) (h0 : 0 < t₀) (r : ℕ) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) (Renv : ℝ) :
    ∃ C ℓ₀ : ℝ, 0 ≤ C ∧ 0 < ℓ₀ ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ), t₀ ≤ τ₀ → τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁ →
      ∀ X A B : ℕ → GridState N,
        (∀ n < n₀, CharStability.IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
          GowdyEnvR r t₀ R Renv (2 * Real.pi / N) (X n) (A n) (B n)) →
        ∀ n ≤ n₀, PeriodicGridResidual.crNorm r (2 * Real.pi / N)
            (errArr (X n) (sol.sample N (τ₀ + n * (2 * Real.pi / N)))) ≤
          C * (PeriodicGridResidual.crNorm r (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) +
            (2 * Real.pi / N) ^ 2 +
            Real.sqrt (PeriodicGridResidual.residualFlux r (2 * Real.pi / N) (2 * Real.pi / N)
              (fun k => errArr (X (k + 1)) (B k)) n)) := by
  obtain ⟨C, ℓ₀, hC, hℓ₀, h⟩ := sol.state_error_crNorm hs h0 r hR Renv
  set T := max (t₁ - t₀) 0
  refine ⟨C * (1 + 2 ^ r * Real.sqrt (2 * T)), min ℓ₀ 2, by positivity, lt_min hℓ₀ two_pos, ?_⟩
  intro N _ hN τ₀ n₀ hτ₀ hn₀ X A B hstep n hn
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have h1 := h N (hN.trans (min_le_left _ _)) τ₀ n₀ hτ₀ hn₀ X A B hstep n hn
  have hbud := PeriodicGridResidual.sum_crNorm_le_sqrt_residualFlux hℓpos
    (hN.trans (min_le_right _ _)) r (fun k => errArr (X (k + 1)) (B k)) n
  have hnl : (n : ℝ) * ℓ ≤ T := by
    have : (n : ℝ) ≤ n₀ := by exact_mod_cast hn
    have : (n : ℝ) * ℓ ≤ n₀ * ℓ := mul_le_mul_of_nonneg_right this hℓpos.le
    exact (by linarith : (n : ℝ) * ℓ ≤ t₁ - t₀).trans (le_max_left _ _)
  have hs2 : Real.sqrt (2 * n * ℓ) ≤ Real.sqrt (2 * T) := Real.sqrt_le_sqrt (by nlinarith)
  set e0 := PeriodicGridResidual.crNorm r ℓ (errArr (X 0) (sol.sample N τ₀))
  set F := PeriodicGridResidual.residualFlux r ℓ ℓ (fun k => errArr (X (k + 1)) (B k)) n
  have he0 : 0 ≤ e0 := PeriodicGridResidual.crNorm_nonneg _ _ _
  have hsF : 0 ≤ Real.sqrt F := Real.sqrt_nonneg _
  have hsum : ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errArr (X (i + 1)) (B i)) ≤
      2 ^ r * Real.sqrt (2 * T) * Real.sqrt F := by
    refine hbud.trans ?_
    have := mul_le_mul_of_nonneg_left hs2 (by positivity : (0 : ℝ) ≤ 2 ^ r)
    exact mul_le_mul_of_nonneg_right this hsF
  refine h1.trans ?_
  have h2r : 0 ≤ 2 ^ r * Real.sqrt (2 * T) := by positivity
  set Kr := 2 ^ r * Real.sqrt (2 * T)
  have key : e0 + ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errArr (X (i + 1)) (B i)) +
      ℓ ^ 2 ≤ (1 + Kr) * (e0 + ℓ ^ 2 + Real.sqrt F) := by
    nlinarith [mul_nonneg h2r he0, mul_nonneg h2r (sq_nonneg ℓ)]
  calc C * (e0 + ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errArr (X (i + 1)) (B i)) +
        ℓ ^ 2) ≤ C * ((1 + Kr) * (e0 + ℓ ^ 2 + Real.sqrt F)) := mul_le_mul_of_nonneg_left key hC
    _ = C * (1 + Kr) * (e0 + ℓ ^ 2 + Real.sqrt F) := by ring

/-- **The pathwise `C¹_h` estimate `eq:supp-gowdy-pathwise-c1`.**  For a smooth solution, a
chart radius `R ≥ chartRadius`, an enforced `C¹_h` envelope radius `R_env`, an offset cap `c₀`
(`charDist(X_{n+1}, B_n) ≤ c₀ h⁴`, `eq:supp-gowdy-offset-cap`, accepted offset plus solver error)
and an initial `C¹_h` error `≤ c₁ h²`, there are `C` and `ℓ₀ > 0` with
`max_n ‖X_n - 𝖲_hX_*(t_n)‖_{1,∞,h} ≤ C h²` for every history in the envelope. -/
theorem pathwise_c1 (hs : sol.IsSmooth) (h0 : 0 < t₀) {R : ℝ} (hR : sol.chartRadius h0 ≤ R)
    (Renv c₀ c₁ : ℝ) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) :
    ∃ C ℓ₀ : ℝ, 0 ≤ C ∧ 0 < ℓ₀ ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ), t₀ ≤ τ₀ → τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁ →
      ∀ X A B : ℕ → GridState N,
        (∀ n < n₀, CharStability.IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
          GowdyEnvR 1 t₀ R Renv (2 * Real.pi / N) (X n) (A n) (B n)) →
        (∀ n < n₀, charDist (X (n + 1)) (B n) ≤ c₀ * (2 * Real.pi / N) ^ 4) →
        PeriodicGridResidual.crNorm 1 (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) ≤
          c₁ * (2 * Real.pi / N) ^ 2 →
        ∀ n ≤ n₀, PeriodicGridResidual.crNorm 1 (2 * Real.pi / N)
            (errArr (X n) (sol.sample N (τ₀ + n * (2 * Real.pi / N)))) ≤
          C * (2 * Real.pi / N) ^ 2 := by
  obtain ⟨C, ℓ₀, hC, hℓ₀, h⟩ := sol.state_error_crNorm hs h0 1 hR Renv
  set T := max (t₁ - t₀) 0
  refine ⟨C * (c₁ + 6 * c₀ * T + 1), min ℓ₀ 2, by positivity, lt_min hℓ₀ two_pos, ?_⟩
  intro N _ hN τ₀ n₀ hτ₀ hn₀ X A B hstep hoff hinit n hn
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hℓ2 : ℓ ≤ 2 := hN.trans (min_le_right _ _)
  have h1 := h N (hN.trans (min_le_left _ _)) τ₀ n₀ hτ₀ hn₀ X A B hstep n hn
  have hres : ∀ i < n, PeriodicGridResidual.crNorm 1 ℓ (errArr (X (i + 1)) (B i)) ≤
      6 * c₀ * ℓ ^ 3 := by
    intro i hi
    have hi' : i < n₀ := lt_of_lt_of_le hi hn
    refine (PeriodicGridResidual.crNorm_le_sup hℓpos hℓ2 1 _).trans ?_
    have := (norm_errArr_le_charDist (X (i + 1)) (B i)).trans
      (mul_le_mul_of_nonneg_left (hoff i hi') (by norm_num : (0 : ℝ) ≤ 3))
    rw [pow_one]
    calc 2 / ℓ * ‖errArr (X (i + 1)) (B i)‖ ≤ 2 / ℓ * (3 * (c₀ * ℓ ^ 4)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 6 * c₀ * ℓ ^ 3 := by field_simp; ring
  have hnl : (n : ℝ) * ℓ ≤ T := by
    have : (n : ℝ) ≤ n₀ := by exact_mod_cast hn
    have : (n : ℝ) * ℓ ≤ n₀ * ℓ := mul_le_mul_of_nonneg_right this hℓpos.le
    exact (by linarith : (n : ℝ) * ℓ ≤ t₁ - t₀).trans (le_max_left _ _)
  have hsum : ∑ i ∈ range n, PeriodicGridResidual.crNorm 1 ℓ (errArr (X (i + 1)) (B i)) ≤
      6 * c₀ * T * ℓ ^ 2 := by
    calc _ ≤ ∑ _i ∈ range n, 6 * c₀ * ℓ ^ 3 :=
          Finset.sum_le_sum fun i hi => hres i (mem_range.1 hi)
      _ = 6 * c₀ * ℓ ^ 2 * (n * ℓ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ 6 * c₀ * ℓ ^ 2 * T := mul_le_mul_of_nonneg_left hnl (by positivity)
      _ = 6 * c₀ * T * ℓ ^ 2 := by ring
  refine h1.trans ?_
  calc C * (PeriodicGridResidual.crNorm 1 ℓ (errArr (X 0) (sol.sample N τ₀)) +
        ∑ i ∈ range n, PeriodicGridResidual.crNorm 1 ℓ (errArr (X (i + 1)) (B i)) + ℓ ^ 2)
      ≤ C * (c₁ * ℓ ^ 2 + 6 * c₀ * T * ℓ ^ 2 + ℓ ^ 2) := by gcongr
    _ = C * (c₁ + 6 * c₀ * T + 1) * ℓ ^ 2 := by ring

end GowdyFrameSolution

/-! ### (G3) for the scheme's histories -/

namespace HermiteReadout.GowdySmoothReference

variable {t₀ t₁ : ℝ} (sol : HermiteReadout.GowdySmoothReference t₀ t₁)

theorem isSmooth : sol.toGowdyFrameSolution.IsSmooth :=
  ⟨sol.smoothInf_a, sol.smoothInf_b, sol.smoothInf_c, sol.smoothInf_d, sol.smoothInf_P,
    sol.smoothInf_Q, sol.smoothInf_lam⟩

open HermiteReadout CoordinateCurvatureJet in
/-- **(G3) of `thm:main-gowdy-regulator` for the scheme's histories.**  For a smooth reference
satisfying the coordinate constraints, a chart radius `R ≥ chartRadius`, an enforced `C¹_h`
envelope radius `R_env`, an offset cap `c₀` (`eq:supp-gowdy-offset-cap`) and an initial `C¹_h`
error `≤ c₁h²`, there are `C` and `ℓ₀ > 0` such that every history realised by split steps in
the envelope has, on every space-time cell, the shared cubic Hermite readout estimates
`eq:main-gowdy-full-curvature`: metric `O(h²)` in `W^{1,∞}`, `O(h)` in second derivatives and
Riemann tensor, uniformly bounded Riemann tensor, and Ricci tensor `O(h)` (the reference being
Ricci flat).  (The pathwise `C¹_h` hypothesis of `readout_full_curvature_vacuum` is supplied by
`GowdyFrameSolution.pathwise_c1`.) -/
theorem readout_full_curvature_of_envelope (h0 : 0 < t₀) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) (Renv : ℝ) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) :
    ∃ C ℓ₀ : ℝ, 0 ≤ C ∧ 0 < ℓ₀ ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ) (X A B : ℕ → GridState N), t₀ ≤ τ₀ →
        τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁ →
        (∀ n < n₀, CharStability.IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
          GowdyEnvR 1 t₀ R Renv (2 * Real.pi / N) (X n) (A n) (B n)) →
        (∀ n < n₀, charDist (X (n + 1)) (B n) ≤ c₀ * (2 * Real.pi / N) ^ 4) →
        PeriodicGridResidual.crNorm 1 (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) ≤
          c₁ * (2 * Real.pi / N) ^ 2 →
        ∀ n < n₀, ∀ (j : ZMod N),
        ∀ x ∈ Icc (τ₀ + n * (2 * Real.pi / N)) (τ₀ + n * (2 * Real.pi / N) + 2 * Real.pi / N),
        ∀ y ∈ Icc (sampleAngle N j) (sampleAngle N j + 2 * Real.pi / N),
          ‖gowdyMetric (stateMap (cellReadout X τ₀ n j) (x, y)) -
              gowdyMetric (stateMap sol.fld (x, y))‖ ≤ C * (2 * Real.pi / N) ^ 2 ∧
          ‖fderiv ℝ (fun z => gowdyMetric (stateMap (cellReadout X τ₀ n j) z)) (x, y) -
              fderiv ℝ (fun z => gowdyMetric (stateMap sol.fld z)) (x, y)‖ ≤
            C * (2 * Real.pi / N) ^ 2 ∧
          ‖fderiv ℝ (fderiv ℝ (fun z => gowdyMetric (stateMap (cellReadout X τ₀ n j) z))) (x, y) -
              fderiv ℝ (fderiv ℝ (fun z => gowdyMetric (stateMap sol.fld z))) (x, y)‖ ≤
            C * (2 * Real.pi / N) ∧
          ‖riemJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y)) -
              riemJet (gowdyJet (stateMap sol.fld) (x, y))‖ ≤ C * (2 * Real.pi / N) ∧
          ‖riemJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y))‖ ≤ C ∧
          ricciJet (gowdyJet (stateMap sol.fld) (x, y)) = 0 ∧
          ‖ricciJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y))‖ ≤
            C * (2 * Real.pi / N) := by
  obtain ⟨C₁, ℓ₁, hC₁, hℓ₁, hpw⟩ :=
    sol.toGowdyFrameSolution.pathwise_c1 sol.isSmooth h0 hR Renv c₀ c₁ hc₀ hc₁
  obtain ⟨C, ℓ₂, hC, hℓ₂, hcurv⟩ := sol.readout_full_curvature_vacuum h0 hR hc₀ hC₁
  refine ⟨C, min ℓ₁ ℓ₂, hC, lt_min hℓ₁ hℓ₂, ?_⟩
  intro N _ hN τ₀ n₀ X A B hτ₀ hn₀ hstep hoff hinit
  have hc1 := hpw N (hN.trans (min_le_left _ _)) τ₀ n₀ hτ₀ hn₀ X A B hstep hoff hinit
  have henv : ∀ n < n₀, SplitEnvelope (t₀ / 2) R (2 * Real.pi / N) (X n) (A n) (B n) := by
    intro n hn j
    obtain ⟨h1, h2, h3⟩ := (hstep n hn).2.1 j
    refine ⟨chartK_subset_gowdyChart h1, h2.1, ?_⟩
    have e : ((transport (2 * Real.pi / N) (A n)).site j).toVec =
        (gowdyData.transport (2 * Real.pi / N) (toCG (A n))).site j := by
      rw [← toCG_transport]; rfl
    have := chartK_subset_gowdyChart h3
    rw [e]
    exact this
  exact hcurv N (hN.trans (min_le_right _ _)) τ₀ n₀ X A B
    ⟨hτ₀, hn₀, fun n hn => ⟨(hstep n hn).1, henv n hn⟩, hoff, hc1⟩

end HermiteReadout.GowdySmoothReference

/-! ### Non-vacuity of the hypotheses -/

section NonVacuity

/-- The trivial solution `a = b = c = d = P = Q = λ = 0` of the frame system. -/
def zeroFrameSolution (t₀ t₁ : ℝ) : GowdyFrameSolution t₀ t₁ where
  a := 0
  b := 0
  c := 0
  d := 0
  P := 0
  Q := 0
  lam := 0
  smooth_a := contDiff_const
  smooth_b := contDiff_const
  smooth_c := contDiff_const
  smooth_d := contDiff_const
  smooth_P := contDiff_const
  smooth_Q := contDiff_const
  smooth_lam := contDiff_const
  periodic_a _ := rfl
  periodic_b _ := rfl
  periodic_c _ := rfl
  periodic_d _ := rfl
  periodic_P _ := rfl
  periodic_Q _ := rfl
  periodic_lam _ := rfl
  eq_a _ _ := by simp [dT, dΘ]
  eq_b _ _ := by simp [dT, dΘ]
  eq_c _ _ := by simp [dT, dΘ]
  eq_d _ _ := by simp [dT, dΘ]
  eq_P _ _ := by simp [dT]
  eq_Q _ _ := by simp [dT]
  eq_lam _ _ := by simp [dT]

/-- Non-vacuity: the trivial solution is smooth. -/
theorem zeroFrameSolution_isSmooth (t₀ t₁ : ℝ) : (zeroFrameSolution t₀ t₁).IsSmooth :=
  ⟨contDiff_const, contDiff_const, contDiff_const, contDiff_const, contDiff_const,
    contDiff_const, contDiff_const⟩

/-- The spatially constant grid state with frame `0`, `P = Q = λ = 0` and clock `t`. -/
def constGrid (N : ℕ) (t : ℝ) : GridState N := ⟨fun _ => ⟨0, 0, 0, t⟩, fun _ => 0⟩

theorem localFieldVec_zero_frame (s : ℝ) :
    localFieldVec ((0 : Fin 4 → ℝ), (0 : ℝ), (0 : ℝ), s) = (0, 0, 0, 1) := by
  rw [localFieldVec_eq]
  refine Prod.ext ?_ (by simp)
  funext i; fin_cases i <;> simp [sourceField]

theorem constGrid_sourceStep (N : ℕ) (t σ : ℝ) :
    IsSourceStep σ (constGrid N t) (constGrid N (t + σ)) := by
  refine ⟨fun j => ?_, rfl⟩
  rw [isMidpointStep_iff_toVec]
  have e : (1 / 2 : ℝ) • ((LocalState.toVec ⟨0, 0, 0, t⟩) + LocalState.toVec ⟨0, 0, 0, t + σ⟩) =
      ((0 : Fin 4 → ℝ), (0 : ℝ), (0 : ℝ), (1 / 2 : ℝ) * (t + (t + σ))) := by
    simp [LocalState.toVec]
  show LocalState.toVec ⟨0, 0, 0, t + σ⟩ = LocalState.toVec ⟨0, 0, 0, t⟩ + σ •
    localFieldVec ((1 / 2 : ℝ) • (LocalState.toVec ⟨0, 0, 0, t⟩ + LocalState.toVec ⟨0, 0, 0, t + σ⟩))
  rw [e, localFieldVec_zero_frame]
  simp [LocalState.toVec]

theorem transport_constGrid (N : ℕ) (ℓ t : ℝ) : transport ℓ (constGrid N t) = constGrid N t := by
  have h0 : recombine (wPlus (0 : Fin 4 → ℝ)) (wMinus 0) = 0 := by
    funext i; fin_cases i <;> simp [recombine, wPlus, wMinus]
  simp only [transport, constGrid, h0]
  congr 1
  funext j
  simp [gPlus, gMinus, wPlus, wMinus]

theorem fwdDiff_const {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : ℝ)
    (v : E) : PeriodicGridResidual.fwdDiff ℓ (fun _ : ZMod N => v) = 0 := by
  funext j; simp [PeriodicGridResidual.fwdDiff]

theorem iterate_fwdDiff_const {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : ℝ) (v : E) {i : ℕ} (hi : 1 ≤ i) :
    (PeriodicGridResidual.fwdDiff ℓ)^[i] (fun _ : ZMod N => v) = 0 := by
  have hz : ∀ k : ℕ, (PeriodicGridResidual.fwdDiff ℓ)^[k] (0 : ZMod N → E) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      exact fwdDiff_const ℓ (0 : E)
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Function.iterate_succ_apply, fwdDiff_const]
  exact hz k

theorem norm_zero_frame (s : ℝ) : ‖((0 : Fin 4 → ℝ), (0 : ℝ), (0 : ℝ), s)‖ = |s| := by
  simp [Prod.norm_def]

/-- **Non-vacuity of the step and envelope hypotheses** of `state_error_crNorm`,
`state_error_crNorm_flux`, `pathwise_c1` and `readout_full_curvature_of_envelope`: for every
`r`, every chart radius `R ≥ |t₁| + 1` and every envelope radius `R_env ≥ 0`, the spatially
constant history `X_n = (U = 0, P = Q = λ = 0, t = τ₀ + nℓ)` with its split steps satisfies the
split-step and `C^r_ℓ` envelope hypotheses (and has zero residuals). -/
theorem constGrid_history_envelope (r : ℕ) {t₀ t₁ R Renv : ℝ} (h0 : 0 < t₀)
    (hR : |t₁| + 1 ≤ R) (hRenv : 0 ≤ Renv) (N : ℕ) [NeZero N] (τ₀ : ℝ) (n₀ : ℕ)
    (hτ₀ : t₀ ≤ τ₀) (hn₀ : τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁) :
    ∀ n < n₀, CharStability.IsSplitStep (2 * Real.pi / N)
        (constGrid N (τ₀ + n * (2 * Real.pi / N)))
        (constGrid N (τ₀ + n * (2 * Real.pi / N) + 2 * Real.pi / N / 2))
        (constGrid N (τ₀ + n * (2 * Real.pi / N) + 2 * Real.pi / N / 2 + 2 * Real.pi / N / 2)) ∧
      GowdyEnvR r t₀ R Renv (2 * Real.pi / N) (constGrid N (τ₀ + n * (2 * Real.pi / N)))
        (constGrid N (τ₀ + n * (2 * Real.pi / N) + 2 * Real.pi / N / 2))
        (constGrid N (τ₀ + n * (2 * Real.pi / N) + 2 * Real.pi / N / 2 + 2 * Real.pi / N / 2)) := by
  intro n hn
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  set τ := τ₀ + n * ℓ
  have hτ : t₀ ≤ τ := by have : 0 ≤ (n : ℝ) * ℓ := by positivity
                         linarith
  have hτℓ : τ + ℓ ≤ t₁ := by
    have : ((n + 1 : ℕ) : ℝ) * ℓ ≤ n₀ * ℓ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hℓpos.le
    push_cast at this
    linarith
  have htr := transport_constGrid N ℓ (τ + ℓ / 2)
  refine ⟨⟨constGrid_sourceStep N τ (ℓ / 2), by rw [htr]; exact constGrid_sourceStep N _ _⟩, ?_⟩
  have hmem : ∀ s : ℝ, τ ≤ s → s ≤ τ + ℓ →
      ((0 : Fin 4 → ℝ), (0 : ℝ), (0 : ℝ), s) ∈ chartK t₀ R := by
    intro s h1 h2
    refine ⟨?_, by show t₀ / 2 ≤ s; linarith⟩
    rw [norm_zero_frame, abs_le]
    constructor <;> linarith [le_abs_self t₁, neg_abs_le t₁]
  have htrCG : gowdyData.transport ℓ (toCG (constGrid N (τ + ℓ / 2))) =
      toCG (constGrid N (τ + ℓ / 2)) := by rw [← toCG_transport, htr]
  refine ⟨fun j => ⟨?_, ?_, ?_⟩, fun i hi1 _ => ⟨?_, ?_, ?_⟩⟩
  · have e : (1 / 2 : ℝ) • ((toCG (constGrid N τ)).site j + (toCG (constGrid N (τ + ℓ / 2))).site j) =
        ((0 : Fin 4 → ℝ), (0 : ℝ), (0 : ℝ), (1 / 2 : ℝ) * (τ + (τ + ℓ / 2))) := by
      simp [toCG, constGrid, LocalState.toVec]
    rw [e]; exact hmem _ (by linarith) (by linarith)
  · show ((0 : Fin 4 → ℝ), (0 : ℝ), (0 : ℝ), τ + ℓ / 2) ∈ chartK t₀ R
    exact hmem _ (by linarith) (by linarith)
  · rw [htrCG]
    have e : (1 / 2 : ℝ) • ((toCG (constGrid N (τ + ℓ / 2))).site j +
        (toCG (constGrid N (τ + ℓ / 2 + ℓ / 2))).site j) =
        ((0 : Fin 4 → ℝ), (0 : ℝ), (0 : ℝ), (1 / 2 : ℝ) * (τ + ℓ / 2 + (τ + ℓ / 2 + ℓ / 2))) := by
      simp [toCG, constGrid, LocalState.toVec]
    rw [e]; exact hmem _ (by linarith) (by linarith)
  · show ‖(PeriodicGridResidual.fwdDiff ℓ)^[i]
      (CharData.midA (toCG (constGrid N τ)) (toCG (constGrid N (τ + ℓ / 2))))‖ ≤ Renv
    have e : CharData.midA (toCG (constGrid N τ)) (toCG (constGrid N (τ + ℓ / 2))) =
        fun _ => ((0 : Fin 4 → ℝ), (0 : ℝ), (0 : ℝ), (1 / 2 : ℝ) * (τ + (τ + ℓ / 2))) := by
      funext j; simp [CharData.midA, toCG, constGrid, LocalState.toVec]
    rw [e, iterate_fwdDiff_const ℓ _ hi1, norm_zero]; exact hRenv
  · show ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] (toCG (constGrid N (τ + ℓ / 2))).site‖ ≤ Renv
    have e : (toCG (constGrid N (τ + ℓ / 2))).site =
        fun _ => ((0 : Fin 4 → ℝ), (0 : ℝ), (0 : ℝ), τ + ℓ / 2) := rfl
    rw [e, iterate_fwdDiff_const ℓ _ hi1, norm_zero]; exact hRenv
  · show ‖(PeriodicGridResidual.fwdDiff ℓ)^[i]
      (CharData.midA (gowdyData.transport ℓ (toCG (constGrid N (τ + ℓ / 2))))
        (toCG (constGrid N (τ + ℓ / 2 + ℓ / 2))))‖ ≤ Renv
    rw [htrCG]
    have e : CharData.midA (toCG (constGrid N (τ + ℓ / 2))) (toCG (constGrid N (τ + ℓ / 2 + ℓ / 2)))
        = fun _ => ((0 : Fin 4 → ℝ), (0 : ℝ), (0 : ℝ),
          (1 / 2 : ℝ) * (τ + ℓ / 2 + (τ + ℓ / 2 + ℓ / 2))) := by
      funext j; simp [CharData.midA, toCG, constGrid, LocalState.toVec]
    rw [e, iterate_fwdDiff_const ℓ _ hi1, norm_zero]; exact hRenv

end NonVacuity

end

end RenewalGeometry.GowdyStaggered
