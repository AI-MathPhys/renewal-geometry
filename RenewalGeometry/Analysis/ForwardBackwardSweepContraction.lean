/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.ForwardBackwardGreenCalculus

/-!
# The forward–backward sweep contraction

Generic content of the boundary construction of the emergent-spacetime manuscript
(`eq:supp-exact-dichotomy`, `eq:supp-exact-green`, `eq:supp-exact-nonlinear-sweeps`,
`thm:supp-exact-boundary`, `prop:supp-exact-sweep-accuracy`).

Let `D` be a bounded operator on a Banach space `E` with an exponential dichotomy
(`FBSweep.Dichotomy`: projections `Π₊ + Π₋ = 1` commuting with `D`,
`‖e^{tD}Π₋‖ ≤ M`, `‖e^{-tD}Π₊‖ ≤ M e^{-κt}` for `t ≥ 0`), and let `𝒢_S` be the forward–backward
Green operator on `[0, S]`.  For a source `f` and a nonlinearity `N(s, e)` with `N(s,0) = 0`,
`L`-Lipschitz in `e` on the ball `‖e‖ ≤ R`, the sweep map `e ↦ 𝒢_S(f + N(·, e))` acts on the closed
ball of radius `R` of `C([0,S], E)`.  Under the two smallness conditions of the manuscript's proof,
`q = M S L ≤ 1/4` and `M S sup‖f‖ ≤ R/2` (the paper's `‖𝒢_S f_a‖ ≤ C₀a²`, `K = 2C₀`):

* `FBSweep.sweepMap_contracting`: the sweep map is a contraction (`ContractingWith q`);
* `FBSweep.exists_unique_fixedPoint`: it has a unique fixed point in the ball;
* `FBSweep.dist_iterate_le`: the sweep iterates from `e^{[0]} = 0` satisfy
  `‖e^{[m]} - e_*‖ ≤ q^m R ≤ 4^{-m} R`;
* `FBSweep.sweepMap_hasDerivAt`, `FBSweep.fixedPoint_ode`: every sweep image solves
  `e' = D e + f + N(·, e_prev)` inside `(0, S)`, and the fixed point solves
  `e' = De + f + N(·,e)` with `Π₋ e(0) = 0`, `Π₊ e(S) = 0`;
* `FBSweep.eq_fixedPoint_of_ode`: conversely every solution of that boundary-value problem in the
  ball is the fixed point (the integral equation is equivalent to the differential equation with
  the two boundary conditions);
* `FBSweep.deriv_iterate_sub_le`: the first-derivative jet of the sweep error,
  `‖δ_m'‖ ≤ ‖D‖ ‖δ_m‖ + L ‖δ_{m-1}‖`.
-/

open Filter Set MeasureTheory Metric
open scoped Topology NNReal

namespace RenewalGeometry
namespace FBSweep

open FBVariation FBGreen

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Exponential dichotomy** `eq:supp-exact-dichotomy`: commuting complementary projections
`Π₊ + Π₋ = 1` and constants `M, κ > 0` with `‖e^{tD}Π₋‖ ≤ M`, `‖e^{-tD}Π₊‖ ≤ M e^{-κ t}`
for `t ≥ 0`. -/
structure Dichotomy (D Pp Pm : E →L[ℝ] E) (M κ : ℝ) : Prop where
  sum : Pp + Pm = 1
  comm_p : Commute D Pp
  comm_m : Commute D Pm
  idem_p : Pp * Pp = Pp
  idem_m : Pm * Pm = Pm
  kappa_pos : 0 < κ
  bound_m : ∀ t, 0 ≤ t → ‖prop D t * Pm‖ ≤ M
  bound_p : ∀ t, 0 ≤ t → ‖prop D (-t) * Pp‖ ≤ M * Real.exp (-(κ * t))

namespace Dichotomy

variable {D Pp Pm : E →L[ℝ] E} {M κ : ℝ}

theorem M_nonneg (h : Dichotomy D Pp Pm M κ) : 0 ≤ M :=
  (norm_nonneg _).trans (h.bound_m 0 le_rfl)

/-- The decaying unstable bound implies the plain bound used by the Green estimate. -/
theorem bound_p' (h : Dichotomy D Pp Pm M κ) : ∀ t, 0 ≤ t → ‖prop D (-t) * Pp‖ ≤ M :=
  fun t ht => (h.bound_p t ht).trans (mul_le_of_le_one_right h.M_nonneg
    (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg h.kappa_pos.le ht))))

end Dichotomy

variable (D Pp Pm : E →L[ℝ] E) {S : ℝ}

/-- The Green operator `𝒢_S` acting on `C([0,S], E)`. -/
noncomputable def greenC (hsum : Pp + Pm = 1) (hS : 0 ≤ S) (u : C(Icc (0 : ℝ) S, E)) :
    C(Icc (0 : ℝ) S, E) where
  toFun s := green D Pp Pm S (IccExtend hS u) s
  continuous_toFun :=
    (continuous_green D Pp Pm hsum S u.continuous.Icc_extend').comp continuous_subtype_val

theorem greenC_apply (hsum : Pp + Pm = 1) (hS : 0 ≤ S) (u : C(Icc (0 : ℝ) S, E))
    (s : Icc (0 : ℝ) S) : greenC D Pp Pm hsum hS u s = green D Pp Pm S (IccExtend hS u) s :=
  rfl

theorem greenC_sub (hsum : Pp + Pm = 1) (hS : 0 ≤ S) (u v : C(Icc (0 : ℝ) S, E)) :
    greenC D Pp Pm hsum hS u - greenC D Pp Pm hsum hS v = greenC D Pp Pm hsum hS (u - v) := by
  ext s
  simp only [ContinuousMap.sub_apply, greenC_apply]
  rw [green_sub_of_continuous D Pp Pm S u.continuous.Icc_extend' v.continuous.Icc_extend']
  congr 1

theorem norm_greenC_apply_le {M : ℝ} (hsum : Pp + Pm = 1) (hS : 0 ≤ S)
    (hm : ∀ t, 0 ≤ t → ‖prop D t * Pm‖ ≤ M) (hp : ∀ t, 0 ≤ t → ‖prop D (-t) * Pp‖ ≤ M)
    {u : C(Icc (0 : ℝ) S, E)} {K : ℝ} (hu : ∀ s, ‖u s‖ ≤ K) (s : Icc (0 : ℝ) S) :
    ‖greenC D Pp Pm hsum hS u s‖ ≤ M * S * K := by
  rw [greenC_apply]
  refine norm_green_le D Pp Pm hm hp (fun r hr => ?_) s.2
  rw [IccExtend_of_mem hS u hr]
  exact hu _

/-- Data and smallness conditions of the sweep contraction (proof of `thm:supp-exact-boundary`):
dichotomy, continuity, `N(s,0) = 0`, `L`-Lipschitz on the ball of radius `R`, `‖f‖ ≤ K_f`,
`q = M S L ≤ 1/4` and `M S K_f ≤ R/2`. -/
structure SweepData (D Pp Pm : E →L[ℝ] E) (M κ S R L Kf : ℝ) (f : ℝ → E) (N : ℝ → E → E) :
    Prop where
  dich : Dichotomy D Pp Pm M κ
  S_nonneg : 0 ≤ S
  f_cont : ContinuousOn f (Icc 0 S)
  N_cont : ContinuousOn (Function.uncurry N) (Icc 0 S ×ˢ closedBall (0 : E) R)
  N_zero : ∀ s ∈ Icc 0 S, N s 0 = 0
  L_nonneg : 0 ≤ L
  N_lip : ∀ s ∈ Icc 0 S, ∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R,
    ‖N s x - N s y‖ ≤ L * ‖x - y‖
  f_bound : ∀ s ∈ Icc 0 S, ‖f s‖ ≤ Kf
  q_le : M * S * L ≤ 1 / 4
  source_le : M * S * Kf ≤ R / 2

variable {D Pp Pm} {M κ R L Kf : ℝ} {f : ℝ → E} {N : ℝ → E → E}

namespace SweepData

theorem Kf_nonneg (hd : SweepData D Pp Pm M κ S R L Kf f N) : 0 ≤ Kf :=
  (norm_nonneg _).trans (hd.f_bound 0 ⟨le_rfl, hd.S_nonneg⟩)

theorem R_nonneg (hd : SweepData D Pp Pm M κ S R L Kf f N) : 0 ≤ R := by
  have := mul_nonneg (mul_nonneg hd.dich.M_nonneg hd.S_nonneg) hd.Kf_nonneg
  linarith [hd.source_le]

theorem q_nonneg (hd : SweepData D Pp Pm M κ S R L Kf f N) : 0 ≤ M * S * L :=
  mul_nonneg (mul_nonneg hd.dich.M_nonneg hd.S_nonneg) hd.L_nonneg

end SweepData

/-- Ball of radius `R` in `C([0,S], E)` (the paper's `‖e‖_∞ ≤ K a²`). -/
abbrev Ball (S R : ℝ) (E : Type*) [NormedAddCommGroup E] := closedBall (0 : C(Icc (0 : ℝ) S, E)) R

instance (S R : ℝ) : CompleteSpace (Ball S R E) := isClosed_closedBall.completeSpace_coe

theorem Ball.norm_apply_le {R : ℝ} (u : Ball S R E) (s : Icc (0 : ℝ) S) : ‖u.1 s‖ ≤ R :=
  (u.1.norm_coe_le_norm s).trans (mem_closedBall_zero_iff.1 u.2)

/-- The nonlinear source `s ↦ f(s) + N(s, u(s))` of a history in the ball. -/
noncomputable def source (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E) :
    C(Icc (0 : ℝ) S, E) where
  toFun s := f s + N s (u.1 s)
  continuous_toFun :=
    (hd.f_cont.comp_continuous continuous_subtype_val fun s => s.2).add
      (hd.N_cont.comp_continuous (continuous_subtype_val.prodMk u.1.continuous)
        fun s => ⟨s.2, mem_closedBall_zero_iff.2 (Ball.norm_apply_le u s)⟩)

theorem source_apply (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E)
    (s : Icc (0 : ℝ) S) : source hd u s = f s + N s (u.1 s) := rfl

theorem norm_N_le (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E)
    (s : Icc (0 : ℝ) S) : ‖N s (u.1 s)‖ ≤ L * R := by
  have h := hd.N_lip s s.2 (u.1 s) (mem_closedBall_zero_iff.2 (Ball.norm_apply_le u s)) 0
    (mem_closedBall_self hd.R_nonneg)
  rw [hd.N_zero s s.2, sub_zero, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Ball.norm_apply_le u s) hd.L_nonneg)

theorem greenC_source_mem (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E) :
    greenC D Pp Pm hd.dich.sum hd.S_nonneg (source hd u) ∈ closedBall (0 : C(Icc (0 : ℝ) S, E)) R
    := by
  rw [mem_closedBall_zero_iff, ContinuousMap.norm_le _ hd.R_nonneg]
  intro s
  have hb : ∀ r, ‖source hd u r‖ ≤ Kf + L * R := fun r =>
    (norm_add_le _ _).trans (add_le_add (hd.f_bound r r.2) (norm_N_le hd u r))
  refine (norm_greenC_apply_le D Pp Pm hd.dich.sum hd.S_nonneg hd.dich.bound_m hd.dich.bound_p'
    hb s).trans ?_
  have h1 := hd.source_le
  have h2 : M * S * L * R ≤ 1 / 4 * R := mul_le_mul_of_nonneg_right hd.q_le hd.R_nonneg
  nlinarith [hd.R_nonneg]

/-- **The sweep map** `e ↦ 𝒢_S{f + N(·, e)}` of `eq:supp-exact-nonlinear-sweeps` on the ball. -/
noncomputable def sweepMap (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E) :
    Ball S R E :=
  ⟨greenC D Pp Pm hd.dich.sum hd.S_nonneg (source hd u), greenC_source_mem hd u⟩

theorem dist_sweepMap_le (hd : SweepData D Pp Pm M κ S R L Kf f N) (u v : Ball S R E) :
    dist (sweepMap hd u) (sweepMap hd v) ≤ M * S * L * dist u v := by
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  show ‖greenC D Pp Pm hd.dich.sum hd.S_nonneg (source hd u)
    - greenC D Pp Pm hd.dich.sum hd.S_nonneg (source hd v)‖ ≤ _
  rw [greenC_sub]
  have hK : 0 ≤ M * S * (L * ‖u.1 - v.1‖) :=
    mul_nonneg (mul_nonneg hd.dich.M_nonneg hd.S_nonneg) (mul_nonneg hd.L_nonneg (norm_nonneg _))
  refine ((ContinuousMap.norm_le _ hK).2 fun s => ?_).trans (le_of_eq (by ring))
  have hb : ∀ r, ‖(source hd u - source hd v) r‖ ≤ L * ‖u.1 - v.1‖ := by
    intro r
    rw [ContinuousMap.sub_apply, source_apply, source_apply, add_sub_add_left_eq_sub]
    refine (hd.N_lip r r.2 _ (mem_closedBall_zero_iff.2 (Ball.norm_apply_le u r)) _
      (mem_closedBall_zero_iff.2 (Ball.norm_apply_le v r))).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hd.L_nonneg
    rw [← ContinuousMap.sub_apply]
    exact ContinuousMap.norm_coe_le_norm _ _
  exact norm_greenC_apply_le D Pp Pm hd.dich.sum hd.S_nonneg hd.dich.bound_m
    hd.dich.bound_p' hb s

/-- **The sweep map is a contraction** with ratio `q = M S L ≤ 1/4`. -/
theorem sweepMap_contracting (hd : SweepData D Pp Pm M κ S R L Kf f N) :
    ContractingWith (M * S * L).toNNReal (sweepMap hd) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  · rw [Real.toNNReal_lt_one]; linarith [hd.q_le]
  · rw [Real.coe_toNNReal _ hd.q_nonneg]; exact dist_sweepMap_le hd u v

theorem ball_nonempty (hd : SweepData D Pp Pm M κ S R L Kf f N) : Nonempty (Ball S R E) :=
  ⟨⟨0, mem_closedBall_self hd.R_nonneg⟩⟩

/-- **Existence and uniqueness of the sweep fixed point** in the ball (Banach). -/
theorem exists_unique_fixedPoint (hd : SweepData D Pp Pm M κ S R L Kf f N) :
    ∃! u : Ball S R E, sweepMap hd u = u := by
  have := ball_nonempty hd
  refine ⟨ContractingWith.fixedPoint _ (sweepMap_contracting hd),
    ContractingWith.fixedPoint_isFixedPt (sweepMap_contracting hd), fun v hv => ?_⟩
  exact ContractingWith.fixedPoint_unique (sweepMap_contracting hd) hv

/-- The zero history, start of the sweep iteration `e^{[0]} = 0`. -/
def zeroBall (hd : SweepData D Pp Pm M κ S R L Kf f N) : Ball S R E :=
  ⟨0, mem_closedBall_self hd.R_nonneg⟩

/-- **Geometric convergence of the sweeps**: `‖e^{[m]} - e_*‖ ≤ q^m R`, `q = M S L`. -/
theorem dist_iterate_le (hd : SweepData D Pp Pm M κ S R L Kf f N) {u : Ball S R E}
    (hu : sweepMap hd u = u) (m : ℕ) :
    dist ((sweepMap hd)^[m] (zeroBall hd)) u ≤ (M * S * L) ^ m * R := by
  have hlip := ((sweepMap_contracting hd).2.iterate m).dist_le_mul (zeroBall hd) u
  rw [Function.iterate_fixed hu, NNReal.coe_pow, Real.coe_toNNReal _ hd.q_nonneg] at hlip
  refine hlip.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hd.q_nonneg _))
  rw [Subtype.dist_eq, dist_comm]
  show dist u.1 0 ≤ R
  rw [dist_zero_right]
  exact mem_closedBall_zero_iff.1 u.2

/-- With `q ≤ 1/4`: `‖e^{[m]} - e_*‖ ≤ 4^{-m} R` (the paper's `C a² 4^{-m}`). -/
theorem dist_iterate_le_quarter (hd : SweepData D Pp Pm M κ S R L Kf f N) {u : Ball S R E}
    (hu : sweepMap hd u = u) (m : ℕ) :
    dist ((sweepMap hd)^[m] (zeroBall hd)) u ≤ (1 / 4) ^ m * R :=
  (dist_iterate_le hd hu m).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hd.q_nonneg hd.q_le m) hd.R_nonneg)

/-- Pointwise form of the sweep error. -/
theorem norm_iterate_sub_le (hd : SweepData D Pp Pm M κ S R L Kf f N) {u : Ball S R E}
    (hu : sweepMap hd u = u) (m : ℕ) (s : Icc (0 : ℝ) S) :
    ‖((sweepMap hd)^[m] (zeroBall hd)).1 s - u.1 s‖ ≤ (1 / 4) ^ m * R := by
  have h := dist_iterate_le_quarter hd hu m
  rw [Subtype.dist_eq, dist_eq_norm] at h
  rw [← ContinuousMap.sub_apply]
  exact (ContinuousMap.norm_coe_le_norm _ _).trans h

/-- The extension of a history in the ball to `ℝ` (constant outside `[0, S]`). -/
noncomputable def ext (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E) : ℝ → E :=
  IccExtend hd.S_nonneg u.1

theorem ext_of_mem (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E) {s : ℝ}
    (hs : s ∈ Icc 0 S) : ext hd u s = u.1 ⟨s, hs⟩ :=
  IccExtend_of_mem hd.S_nonneg u.1 hs

theorem continuous_ext (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E) :
    Continuous (ext hd u) :=
  u.1.continuous.Icc_extend'

theorem norm_ext_le (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E) {s : ℝ}
    (hs : s ∈ Icc 0 S) : ‖ext hd u s‖ ≤ R := by
  rw [ext_of_mem hd u hs]; exact Ball.norm_apply_le u _

/-- On `[0, S]` the image of the sweep map is the Green integral of the source. -/
theorem ext_sweepMap (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E) {s : ℝ}
    (hs : s ∈ Icc 0 S) :
    ext hd (sweepMap hd u) s = green D Pp Pm S (IccExtend hd.S_nonneg (source hd u)) s := by
  rw [ext_of_mem hd _ hs]; rfl

theorem IccExtend_source (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E) {s : ℝ}
    (hs : s ∈ Icc 0 S) :
    IccExtend hd.S_nonneg (source hd u) s = f s + N s (ext hd u s) := by
  rw [IccExtend_of_mem hd.S_nonneg _ hs, source_apply, ext_of_mem hd u hs]

/-- **Every sweep image solves the linearised equation** `e_{new}' = D e_{new} + f + N(·, e)`
inside `(0, S)`. -/
theorem sweepMap_hasDerivAt (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E) {s : ℝ}
    (hs : s ∈ Ioo 0 S) :
    HasDerivAt (ext hd (sweepMap hd u))
      (D (ext hd (sweepMap hd u) s) + (f s + N s (ext hd u s))) s := by
  have hg := (source hd u).continuous.Icc_extend' (h := hd.S_nonneg)
  have hd' := hasDerivAt_green D Pp Pm hd.dich.sum S hg s
  have hev : ext hd (sweepMap hd u) =ᶠ[𝓝 s] green D Pp Pm S (IccExtend hd.S_nonneg (source hd u))
      := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    exact ext_sweepMap hd u (Ioo_subset_Icc_self hr)
  have hsI := Ioo_subset_Icc_self hs
  rw [ext_sweepMap hd u hsI, ← IccExtend_source hd u hsI]
  exact hd'.congr_of_eventuallyEq hev

/-- Boundary conditions of every sweep image: `Π₋ e(0) = 0`, `Π₊ e(S) = 0`. -/
theorem sweepMap_boundary (hd : SweepData D Pp Pm M κ S R L Kf f N) (u : Ball S R E) :
    Pm (ext hd (sweepMap hd u) 0) = 0 ∧ Pp (ext hd (sweepMap hd u) S) = 0 := by
  have hg := (source hd u).continuous.Icc_extend' (h := hd.S_nonneg)
  refine ⟨?_, ?_⟩
  · rw [ext_sweepMap hd u ⟨le_rfl, hd.S_nonneg⟩]
    exact green_boundary_zero D Pp Pm hd.dich.sum hd.dich.comm_m hd.dich.idem_m S hg
  · rw [ext_sweepMap hd u ⟨hd.S_nonneg, le_rfl⟩]
    exact green_boundary_end D Pp Pm hd.dich.sum hd.dich.comm_p hd.dich.idem_p S hg

/-- **The fixed point solves the boundary-value problem**: `e_*' = D e_* + f + N(·, e_*)` inside
`(0,S)`, `Π₋ e_*(0) = 0`, `Π₊ e_*(S) = 0`, and `‖e_*‖ ≤ R` (`eq:supp-exact-boundary-estimate`,
first line, in error form `e = w - w_ref`). -/
theorem fixedPoint_ode (hd : SweepData D Pp Pm M κ S R L Kf f N) {u : Ball S R E}
    (hu : sweepMap hd u = u) :
    (∀ s ∈ Ioo 0 S, HasDerivAt (ext hd u) (D (ext hd u s) + (f s + N s (ext hd u s))) s) ∧
      Pm (ext hd u 0) = 0 ∧ Pp (ext hd u S) = 0 ∧ ∀ s ∈ Icc 0 S, ‖ext hd u s‖ ≤ R := by
  refine ⟨fun s hs => ?_, ?_, ?_, fun s hs => norm_ext_le hd u hs⟩
  · have := sweepMap_hasDerivAt hd u hs
    rwa [hu] at this
  · have := (sweepMap_boundary hd u).1; rwa [hu] at this
  · have := (sweepMap_boundary hd u).2; rwa [hu] at this

/-- **Converse**: a solution of the boundary-value problem lying in the ball is the sweep fixed
point (the integral equation is equivalent to the differential and boundary conditions). -/
theorem eq_fixedPoint_of_ode (hd : SweepData D Pp Pm M κ S R L Kf f N) {u : Ball S R E}
    (hu : sweepMap hd u = u) {e : ℝ → E} (hcont : ContinuousOn e (Icc 0 S))
    (hde : ∀ s ∈ Ioo 0 S, HasDerivAt e (D (e s) + (f s + N s (e s))) s)
    (h0 : Pm (e 0) = 0) (hS : Pp (e S) = 0) (hR : ∀ s ∈ Icc 0 S, ‖e s‖ ≤ R) :
    ∀ s ∈ Icc 0 S, e s = ext hd u s := by
  let ue : C(Icc (0 : ℝ) S, E) := ⟨fun s => e s, hcont.restrict⟩
  have hue : ue ∈ closedBall (0 : C(Icc (0 : ℝ) S, E)) R := by
    rw [mem_closedBall_zero_iff, ContinuousMap.norm_le _ hd.R_nonneg]
    exact fun s => hR s s.2
  let v : Ball S R E := ⟨ue, hue⟩
  have hext : ∀ s ∈ Icc 0 S, ext hd v s = e s := fun s hs => by
    rw [ext_of_mem hd v hs]; rfl
  have hF : ContinuousOn (fun r => f r + N r (e r)) (Icc 0 S) := by
    refine hd.f_cont.add ?_
    have : ContinuousOn (fun r => ((r, e r) : ℝ × E)) (Icc 0 S) :=
      continuousOn_id.prodMk hcont
    exact hd.N_cont.comp this fun r hr => ⟨hr, mem_closedBall_zero_iff.2 (hR r hr)⟩
  have hfix : sweepMap hd v = v := by
    apply Subtype.ext
    ext ⟨s, hs⟩
    show green D Pp Pm S (IccExtend hd.S_nonneg (source hd v)) s = e s
    have hvoc := variation_of_constants D Pp Pm hd.dich.sum hd.dich.comm_p hd.dich.comm_m hcont hF
      hde hs
    rw [h0, hS, map_zero, map_zero, zero_add, zero_add] at hvoc
    rw [hvoc]
    refine green_congr D Pp Pm (fun r hr => ?_) hs
    rw [IccExtend_source hd v hr, hext r hr]
  have huniq := (exists_unique_fixedPoint hd).unique hfix hu
  intro s hs
  rw [← hext s hs, huniq]

/-- **First-derivative jet of the sweep error** (`prop:supp-exact-sweep-accuracy`, `j = 1`):
`δ_m' = D δ_m + N(·, e^{[m-1]}) - N(·, e_*)`, so
`‖δ_m'‖ ≤ ‖D‖ ‖δ_m‖ + L ‖δ_{m-1}‖` inside `(0, S)`. -/
theorem deriv_iterate_sub_le (hd : SweepData D Pp Pm M κ S R L Kf f N) {u : Ball S R E}
    (hu : sweepMap hd u = u) (m : ℕ) {s : ℝ} (hs : s ∈ Ioo 0 S) :
    ∃ δ' : E, HasDerivAt (fun r => ext hd ((sweepMap hd)^[m + 1] (zeroBall hd)) r - ext hd u r)
        δ' s ∧
      ‖δ'‖ ≤ ‖D‖ * ((1 / 4) ^ (m + 1) * R) + L * ((1 / 4) ^ m * R) := by
  set v := (sweepMap hd)^[m] (zeroBall hd)
  have hv : (sweepMap hd)^[m + 1] (zeroBall hd) = sweepMap hd v :=
    Function.iterate_succ_apply' _ _ _
  have h1 := sweepMap_hasDerivAt hd v hs
  have h2 := (fixedPoint_ode hd hu).1 s hs
  rw [hv]
  refine ⟨_, h1.sub h2, ?_⟩
  have hsI := Ioo_subset_Icc_self hs
  have e1 : ‖ext hd (sweepMap hd v) s - ext hd u s‖ ≤ (1 / 4) ^ (m + 1) * R := by
    rw [ext_of_mem hd _ hsI, ext_of_mem hd _ hsI, ← hv]
    exact norm_iterate_sub_le hd hu (m + 1) ⟨s, hsI⟩
  have e0 : ‖ext hd v s - ext hd u s‖ ≤ (1 / 4) ^ m * R := by
    rw [ext_of_mem hd _ hsI, ext_of_mem hd _ hsI]
    exact norm_iterate_sub_le hd hu m ⟨s, hsI⟩
  have hN := hd.N_lip s hsI _ (mem_closedBall_zero_iff.2 (norm_ext_le hd v hsI)) _
    (mem_closedBall_zero_iff.2 (norm_ext_le hd u hsI))
  have hrw : D (ext hd (sweepMap hd v) s) + (f s + N s (ext hd v s))
      - (D (ext hd u s) + (f s + N s (ext hd u s)))
      = D (ext hd (sweepMap hd v) s - ext hd u s) + (N s (ext hd v s) - N s (ext hd u s)) := by
    rw [map_sub]; abel
  rw [hrw]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left e1 (norm_nonneg _))
  · exact hN.trans (mul_le_mul_of_nonneg_left e0 hd.L_nonneg)

end FBSweep
end RenewalGeometry
