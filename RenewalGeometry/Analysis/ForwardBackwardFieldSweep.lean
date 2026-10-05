/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.ForwardBackwardSweepContraction

/-!
# Boundary histories of a vector field near a linear dichotomy

Vector-field form of the sweep contraction (emergent-spacetime manuscript, subsection
`subsec:supp-exact-boundary`: `eq:supp-exact-reference`, `eq:supp-exact-nonlinear-sweeps`,
`thm:supp-exact-boundary`, `prop:supp-exact-boundary-residual`).

Let `H : E → E` be a vector field, differentiable on the tube `‖w‖ ≤ ρ` with
`‖DH(w) - D‖ ≤ ε` there, where `D` has an exponential dichotomy.  Take the affine reference
`w_ref(s) = s ω`, its residual `f(s) = H(sω) - ω` and the nonlinearity
`N(s, e) = H(sω + e) - H(sω) - De` (exactly the manuscript's `f_a`, `N_a`).
If `q = M S ε ≤ 1/4`, `M S sup‖f‖ ≤ R/2` and the reference plus the ball of radius `R` stays in
the tube, then:

* `FBField.exists_unique_boundary_history`: there is a unique history `w` with
  `w' = H(w)` on `(0, S)`, `Π₋(w(0) - w_ref(0)) = 0`, `Π₊(w(S) - w_ref(S)) = 0` and
  `‖w - w_ref‖ ≤ R` (`eq:supp-exact-boundary-estimate`, first two lines);
* `FBField.norm_velocity_error_le`: if moreover `DH` is continuous and `C₂`-Lipschitz on the tube and
  `‖DH(sω) ω‖ ≤ K_f'` (the paper's `‖f_a'‖`), then the velocity error
  `(w - w_ref)' = H(w) - ω` satisfies
  `‖(w - w_ref)'‖ ≤ (2M(K_f + εR) + M S (K_f' + C₂ R ‖ω‖)) / (1 - M S ε)`
  (the derivative estimate of `thm:supp-exact-boundary`, by the paper's argument: the velocity error
  solves the differentiated equation, its boundary data are `Π₋F_e(0)`, `Π₊F_e(S)`, and the
  `q`-term is absorbed);
* `FBField.residual_bound`: an approximate history `w̃` in the tube with residual
  `r = w̃' - H(w̃)` satisfies `sup‖w̃ - w‖ ≤ (M(|d₋| + |d₊|) + M S sup‖r‖)/(1 - q)`,
  `d₋ = Π₋(w̃(0) - w_ref(0))`, `d₊ = Π₊(w̃(S) - w_ref(S))` (`eq:supp-exact-residual-bound`).
-/

open Filter Set MeasureTheory Metric
open scoped Topology NNReal

namespace RenewalGeometry
namespace FBField

open FBVariation FBGreen FBSweep

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The reference residual `f(s) = H(sω) - ω` of `w_ref(s) = sω` (`eq:supp-exact-reference`). -/
def src (H : E → E) (ω : E) (s : ℝ) : E := H (s • ω) - ω

/-- The nonlinearity `N(s, e) = H(sω + e) - H(sω) - D e`. -/
def nonlin (D : E →L[ℝ] E) (H : E → E) (ω : E) (s : ℝ) (e : E) : E :=
  H (s • ω + e) - H (s • ω) - D e

/-- Hypotheses of the field form of the boundary contraction. -/
structure FieldData (D Pp Pm : E →L[ℝ] E) (M κ : ℝ) (H : E → E) (H' : E → E →L[ℝ] E) (ω : E)
    (ρ ε S R Kf : ℝ) : Prop where
  dich : Dichotomy D Pp Pm M κ
  S_nonneg : 0 ≤ S
  deriv : ∀ w ∈ closedBall (0 : E) ρ, HasFDerivAt H (H' w) w
  deriv_close : ∀ w ∈ closedBall (0 : E) ρ, ‖H' w - D‖ ≤ ε
  tube : ∀ s ∈ Icc 0 S, ‖s • ω‖ + R ≤ ρ
  src_bound : ∀ s ∈ Icc 0 S, ‖H (s • ω) - ω‖ ≤ Kf
  q_le : M * S * ε ≤ 1 / 4
  source_le : M * S * Kf ≤ R / 2

variable {D Pp Pm : E →L[ℝ] E} {M κ : ℝ} {H : E → E} {H' : E → E →L[ℝ] E} {ω : E}
  {ρ ε S R Kf : ℝ}

namespace FieldData

theorem Kf_nonneg (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) : 0 ≤ Kf :=
  (norm_nonneg _).trans (hF.src_bound 0 ⟨le_rfl, hF.S_nonneg⟩)

theorem R_nonneg (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) : 0 ≤ R := by
  have := mul_nonneg (mul_nonneg hF.dich.M_nonneg hF.S_nonneg) hF.Kf_nonneg
  linarith [hF.source_le]

theorem mem_tube (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) {s : ℝ} (hs : s ∈ Icc 0 S)
    {e : E} (he : ‖e‖ ≤ R) : s • ω + e ∈ closedBall (0 : E) ρ := by
  rw [mem_closedBall_zero_iff]
  exact (norm_add_le _ _).trans ((add_le_add le_rfl he).trans (hF.tube s hs))

theorem mem_tube' (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) {s : ℝ} (hs : s ∈ Icc 0 S) :
    s • ω ∈ closedBall (0 : E) ρ := by
  simpa using hF.mem_tube hs (e := 0) (by simpa using hF.R_nonneg)

theorem rho_nonneg (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) : 0 ≤ ρ :=
  (norm_nonneg _).trans (mem_closedBall_zero_iff.1 (hF.mem_tube' ⟨le_rfl, hF.S_nonneg⟩))

theorem eps_nonneg (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) : 0 ≤ ε :=
  (norm_nonneg _).trans (hF.deriv_close 0 (mem_closedBall_self hF.rho_nonneg))

theorem H_contOn (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) :
    ContinuousOn H (closedBall (0 : E) ρ) :=
  fun w hw => (hF.deriv w hw).continuousAt.continuousWithinAt

/-- Mean-value estimate: `N(s, ·)` is `ε`-Lipschitz on the ball of radius `R`. -/
theorem nonlin_lip (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) {s : ℝ} (hs : s ∈ Icc 0 S)
    {x y : E} (hx : x ∈ closedBall (0 : E) R) (hy : y ∈ closedBall (0 : E) R) :
    ‖nonlin D H ω s x - nonlin D H ω s y‖ ≤ ε * ‖x - y‖ := by
  have hder : ∀ z ∈ closedBall (0 : E) R,
      HasFDerivWithinAt (fun z => H (s • ω + z) - D z) (H' (s • ω + z) - D)
        (closedBall (0 : E) R) z := by
    intro z hz
    have h1 : HasFDerivAt (fun z => H (s • ω + z)) (H' (s • ω + z)) z := by
      have h2 := (hF.deriv _ (hF.mem_tube hs (mem_closedBall_zero_iff.1 hz))).comp z
        ((hasFDerivAt_id z).const_add (s • ω))
      rw [ContinuousLinearMap.comp_id] at h2
      exact h2
    exact (h1.sub D.hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ z ∈ closedBall (0 : E) R, ‖H' (s • ω + z) - D‖ ≤ ε := fun z hz =>
    hF.deriv_close _ (hF.mem_tube hs (mem_closedBall_zero_iff.1 hz))
  have := (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hb hy hx
  have hrw : nonlin D H ω s x - nonlin D H ω s y
      = (H (s • ω + x) - D x) - (H (s • ω + y) - D y) := by
    simp only [nonlin]; abel
  rw [hrw]
  exact this

/-- The field hypotheses produce the abstract sweep data with `L = ε`. -/
theorem toSweepData (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) :
    SweepData D Pp Pm M κ S R ε Kf (src H ω) (nonlin D H ω) where
  dich := hF.dich
  S_nonneg := hF.S_nonneg
  f_cont := by
    refine (hF.H_contOn.comp (continuous_id.smul continuous_const).continuousOn
      fun s hs => hF.mem_tube' hs).sub continuousOn_const
  N_cont := by
    have hc1 : ContinuousOn (fun p : ℝ × E => H (p.1 • ω + p.2)) (Icc 0 S ×ˢ closedBall 0 R) :=
      hF.H_contOn.comp ((continuous_fst.smul continuous_const).add continuous_snd).continuousOn
        fun p hp => hF.mem_tube hp.1 (mem_closedBall_zero_iff.1 hp.2)
    have hc2 : ContinuousOn (fun p : ℝ × E => H (p.1 • ω)) (Icc 0 S ×ˢ closedBall 0 R) :=
      hF.H_contOn.comp (continuous_fst.smul continuous_const).continuousOn
        fun p hp => hF.mem_tube' hp.1
    exact (hc1.sub hc2).sub (D.continuous.comp continuous_snd).continuousOn
  N_zero := fun s _ => by simp [nonlin]
  L_nonneg := hF.eps_nonneg
  N_lip := fun s hs x hx y hy => hF.nonlin_lip hs hx hy
  f_bound := hF.src_bound
  q_le := hF.q_le
  source_le := hF.source_le

end FieldData

/-- The error equation: along `w = sω + e`, `w' = H(w)` is `e' = De + f + N(e)`. -/
theorem field_eq_error (D : E →L[ℝ] E) (H : E → E) (ω : E) (s : ℝ) (e : E) :
    H (s • ω + e) - ω = D e + (src H ω s + nonlin D H ω s e) := by
  simp only [src, nonlin]; abel

/-- A boundary history of the field: `w' = H(w)` on `(0,S)`, the two projected boundary
conditions relative to `w_ref(s) = sω`, and the tube bound `‖w - w_ref‖ ≤ R`. -/
def IsBoundaryHistory (D Pp Pm : E →L[ℝ] E) (H : E → E) (ω : E) (S R : ℝ) (w : ℝ → E) :
    Prop :=
  ContinuousOn w (Icc 0 S) ∧ (∀ s ∈ Ioo 0 S, HasDerivAt w (H (w s)) s) ∧
    Pm (w 0 - (0 : ℝ) • ω) = 0 ∧ Pp (w S - S • ω) = 0 ∧ ∀ s ∈ Icc 0 S, ‖w s - s • ω‖ ≤ R

theorem error_of_history {w : ℝ → E} (hw : IsBoundaryHistory D Pp Pm H ω S R w) :
    ContinuousOn (fun s => w s - s • ω) (Icc 0 S) ∧
      (∀ s ∈ Ioo 0 S, HasDerivAt (fun r => w r - r • ω)
        (D (w s - s • ω) + (src H ω s + nonlin D H ω s (w s - s • ω))) s) ∧
      Pm (w 0 - (0 : ℝ) • ω) = 0 ∧ Pp (w S - S • ω) = 0 ∧ ∀ s ∈ Icc 0 S, ‖w s - s • ω‖ ≤ R := by
  refine ⟨hw.1.sub (continuous_id.smul continuous_const).continuousOn, fun s hs => ?_, hw.2.2⟩
  have h := (hw.2.1 s hs).sub ((hasDerivAt_id s).smul_const ω)
  rw [← field_eq_error]
  simp only [one_smul, add_sub_cancel] at h ⊢
  exact h

/-- **Unique boundary history** (`thm:supp-exact-boundary`, existence/uniqueness and the first
two lines of `eq:supp-exact-boundary-estimate`, generic form). -/
theorem exists_unique_boundary_history (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) :
    ∃ w : ℝ → E, IsBoundaryHistory D Pp Pm H ω S R w ∧
      ∀ w' : ℝ → E, IsBoundaryHistory D Pp Pm H ω S R w' → ∀ s ∈ Icc 0 S, w' s = w s := by
  have hd := hF.toSweepData
  obtain ⟨u, hu, -⟩ := exists_unique_fixedPoint hd
  obtain ⟨hode, h0, hS, hR⟩ := fixedPoint_ode hd hu
  refine ⟨fun s => s • ω + ext hd u s, ⟨?_, fun s hs => ?_, ?_, ?_, fun s hs => ?_⟩, ?_⟩
  · exact ((continuous_id.smul continuous_const).add (continuous_ext hd u)).continuousOn
  · have h := ((hasDerivAt_id s).smul_const ω).add (hode s hs)
    have heq : (1 : ℝ) • ω + (D (ext hd u s) + (src H ω s + nonlin D H ω s (ext hd u s)))
        = H (s • ω + ext hd u s) := by
      rw [← field_eq_error]; simp
    rw [heq] at h
    exact h
  · simpa using h0
  · simpa using hS
  · simpa using hR s hs
  · intro w' hw' s hs
    obtain ⟨hc, hd', h0', hS', hR'⟩ := error_of_history hw'
    have := eq_fixedPoint_of_ode hd hu hc hd' (by simpa using h0') hS' hR' s hs
    show w' s = s • ω + ext hd u s
    rw [← this]; abel

/-- **A posteriori residual estimate** `eq:supp-exact-residual-bound` (generic form): an
approximate history `w̃` in the tube with residual `r = w̃' - H(w̃)` satisfies
`‖w̃ - w‖ ≤ (M(|d₋| + |d₊|) + M S sup‖r‖)/(1 - q)`, `q = M S ε ≤ 1/4`. -/
theorem residual_bound (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) {w : ℝ → E}
    (hw : IsBoundaryHistory D Pp Pm H ω S R w) {wt res : ℝ → E} {Kr : ℝ}
    (hwt : ContinuousOn wt (Icc 0 S)) (htube : ∀ s ∈ Icc 0 S, ‖wt s - s • ω‖ ≤ R)
    (hres : ContinuousOn res (Icc 0 S))
    (hde : ∀ s ∈ Ioo 0 S, HasDerivAt wt (H (wt s) + res s) s)
    (hr : ∀ s ∈ Icc 0 S, ‖res s‖ ≤ Kr) :
    ∀ s ∈ Icc 0 S, ‖wt s - w s‖
      ≤ (M * (‖Pm (wt 0 - (0 : ℝ) • ω)‖ + ‖Pp (wt S - S • ω)‖) + M * S * Kr)
          / (1 - M * S * ε) := by
  have hd := hF.toSweepData
  obtain ⟨hcs, hdes, h0s, hSs, hRs⟩ := error_of_history hw
  set es := fun s => w s - s • ω
  set et := fun s => wt s - s • ω
  have hNcont : ∀ {g : ℝ → E}, ContinuousOn g (Icc 0 S) → (∀ s ∈ Icc 0 S, ‖g s‖ ≤ R) →
      ContinuousOn (fun s => src H ω s + nonlin D H ω s (g s)) (Icc 0 S) := by
    intro g hg hgR
    refine hd.f_cont.add ?_
    exact hd.N_cont.comp (continuousOn_id.prodMk hg)
      fun r hr => ⟨hr, mem_closedBall_zero_iff.2 (hgR r hr)⟩
  have hct : ContinuousOn et (Icc 0 S) :=
    hwt.sub (continuous_id.smul continuous_const).continuousOn
  have hFs := hNcont hcs hRs
  have hFt := (hNcont hct htube).add hres
  -- the exact error is a Green fixed point
  have hfix : ∀ s ∈ Icc 0 S, es s = green D Pp Pm S
      (fun r => src H ω r + nonlin D H ω r (es r)) s := by
    intro s hs
    have := variation_of_constants D Pp Pm hd.dich.sum hd.dich.comm_p hd.dich.comm_m hcs hFs
      hdes hs
    rw [this]
    have e0 : Pm (es 0) = 0 := h0s
    have eS : Pp (es S) = 0 := hSs
    rw [e0, eS, map_zero, map_zero, zero_add, zero_add]
  have hdet : ∀ s ∈ Ioo 0 S, HasDerivAt et
      (D (et s) + (src H ω s + nonlin D H ω s (et s) + res s)) s := by
    intro s hs
    have h := (hde s hs).sub ((hasDerivAt_id s).smul_const ω)
    have heq : H (wt s) + res s - (1 : ℝ) • ω
        = D (et s) + (src H ω s + nonlin D H ω s (et s) + res s) := by
      have := field_eq_error D H ω s (wt s - s • ω)
      rw [add_sub_cancel] at this
      simp only [et, one_smul]
      rw [add_sub_right_comm, this]; abel
    rw [heq] at h
    exact h
  have hNL : ∀ s ∈ Icc 0 S, ‖nonlin D H ω s (et s) - nonlin D H ω s (es s)‖
      ≤ ε * ‖et s - es s‖ := fun s hs =>
    hF.nonlin_lip hs (mem_closedBall_zero_iff.2 (htube s hs))
      (mem_closedBall_zero_iff.2 (hRs s hs))
  have h0 : ∀ s ∈ Icc 0 S, ‖et s - es s‖ ≤ R + R := fun s hs =>
    (norm_sub_le _ _).trans (add_le_add (htube s hs) (hRs s hs))
  have hq : M * S * ε < 1 := by linarith [hF.q_le]
  have key := boundary_residual_bound D Pp Pm hd.dich.sum hd.dich.comm_p hd.dich.comm_m
    hd.dich.idem_p hd.dich.idem_m hd.S_nonneg hd.dich.bound_m hd.dich.bound_p' hF.eps_nonneg hq
    hfix hct hFt hdet hNL hr hFs h0
  intro s hs
  have hk := key s hs
  have : et s - es s = wt s - w s := by simp only [et, es]; abel
  rw [this] at hk
  exact hk

/-- The source of the error equation at a point of a history is bounded by `K_f + ε R`. -/
theorem norm_source_le (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) {s : ℝ} (hs : s ∈ Icc 0 S)
    {e : E} (he : ‖e‖ ≤ R) : ‖src H ω s + nonlin D H ω s e‖ ≤ Kf + ε * R := by
  have h := hF.nonlin_lip hs (mem_closedBall_zero_iff.2 he) (mem_closedBall_self hF.R_nonneg)
  have h0 : nonlin D H ω s 0 = 0 := by simp [nonlin]
  rw [h0, sub_zero, sub_zero] at h
  exact (norm_add_le _ _).trans (add_le_add (hF.src_bound s hs)
    (h.trans (mul_le_mul_of_nonneg_left he hF.eps_nonneg)))

/-- **Derivative estimate of the boundary history** (`thm:supp-exact-boundary`, last estimate of
`eq:supp-exact-boundary-estimate`, generic form).  The velocity error
`(w - w_ref)' = H(w) - ω` solves the differentiated equation `u' = Du + (DH(w) - D)u + DH(w)ω`;
its projected boundary data are those of `F_e = f + N(e)` because `Π₋ e(0) = 0`, `Π₊ e(S) = 0`;
splitting `DH(w)ω = DH(w_ref)ω + (DH(w) - DH(w_ref))ω` and absorbing the `q`-term gives
`‖(w - w_ref)'‖ ≤ (2M(K_f + εR) + M S (K_f' + C₂ R ‖ω‖)) / (1 - M S ε)`. -/
theorem norm_velocity_error_le (hF : FieldData D Pp Pm M κ H H' ω ρ ε S R Kf) {C₂ Kf' : ℝ}
    (hC₂ : 0 ≤ C₂)
    (hH'c : ContinuousOn H' (closedBall (0 : E) ρ))
    (hH'lip : ∀ x ∈ closedBall (0 : E) ρ, ∀ y ∈ closedBall (0 : E) ρ,
      ‖H' x - H' y‖ ≤ C₂ * ‖x - y‖)
    (hfd : ∀ s ∈ Icc 0 S, ‖H' (s • ω) ω‖ ≤ Kf') {w : ℝ → E}
    (hw : IsBoundaryHistory D Pp Pm H ω S R w) :
    ∀ s ∈ Icc 0 S, ‖H (w s) - ω‖
      ≤ (M * (2 * (Kf + ε * R)) + M * S * (Kf' + C₂ * R * ‖ω‖)) / (1 - M * S * ε) := by
  have hd := hF.toSweepData
  obtain ⟨hwc, hwd, h0, hS, hR⟩ := hw
  have hwrite : ∀ s, s • ω + (w s - s • ω) = w s := fun s => add_sub_cancel _ _
  have hwt : ∀ s ∈ Icc 0 S, w s ∈ closedBall (0 : E) ρ := fun s hs => by
    have := hF.mem_tube hs (hR s hs); rwa [hwrite] at this
  set u : ℝ → E := fun s => H (w s) - ω with hu_def
  set G : ℝ → E := fun s => (H' (w s) - D) (u s) + H' (w s) ω with hG_def
  have hu_cont : ContinuousOn u (Icc 0 S) := (hF.H_contOn.comp hwc hwt).sub continuousOn_const
  have hH'w : ContinuousOn (fun s => H' (w s)) (Icc 0 S) := hH'c.comp hwc hwt
  have hG_cont : ContinuousOn G (Icc 0 S) :=
    ((hH'w.sub continuousOn_const).clm_apply hu_cont).add (hH'w.clm_apply continuousOn_const)
  have hu_der : ∀ s ∈ Ioo 0 S, HasDerivAt u (D (u s) + G s) s := by
    intro s hs
    have h1 := ((hF.deriv _ (hwt s (Ioo_subset_Icc_self hs))).comp_hasDerivAt s (hwd s hs)).sub_const ω
    have heq : D (u s) + G s = H' (w s) (H (w s)) := by
      simp only [hG_def, hu_def, ContinuousLinearMap.sub_apply, map_sub]
      abel
    rw [heq]
    exact h1
  -- boundary data: `Π₋ u(0) = Π₋ F_e(0)`, `Π₊ u(S) = Π₊ F_e(S)`
  have hcomm : ∀ (P : E →L[ℝ] E), Commute D P → ∀ x, P (D x) = D (P x) := fun P hP x => by
    rw [← ContinuousLinearMap.mul_apply, ← hP.eq, ContinuousLinearMap.mul_apply]
  have hu_split : ∀ s, u s = D (w s - s • ω) + (src H ω s + nonlin D H ω s (w s - s • ω)) :=
    fun s => by rw [← field_eq_error, hwrite]
  have hb0 : Pm (u 0) = Pm (src H ω 0 + nonlin D H ω 0 (w 0 - (0 : ℝ) • ω)) := by
    rw [hu_split, map_add, hcomm Pm hd.dich.comm_m, h0, map_zero, zero_add]
  have hbS : Pp (u S) = Pp (src H ω S + nonlin D H ω S (w S - S • ω)) := by
    rw [hu_split, map_add, hcomm Pp hd.dich.comm_p, hS, map_zero, zero_add]
  have hS0 : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hF.S_nonneg⟩
  have hSS : S ∈ Icc 0 S := ⟨hF.S_nonneg, le_rfl⟩
  have hF0 := norm_source_le hF hS0 (hR 0 hS0)
  have hFS := norm_source_le hF hSS (hR S hSS)
  obtain ⟨Δ₀, hΔ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hu_cont
  have hq0 : 0 ≤ M * S * ε := mul_nonneg (mul_nonneg hF.dich.M_nonneg hF.S_nonneg) hF.eps_nonneg
  have hq1 : M * S * ε < 1 := by linarith [hF.q_le]
  refine aposteriori_sup_bound (Δ := fun s => ‖u s‖) hq0 hq1 hΔ₀ ?_
  intro c hc s hs
  have hvoc := variation_of_constants D Pp Pm hd.dich.sum hd.dich.comm_p hd.dich.comm_m hu_cont
    hG_cont hu_der hs
  rw [hb0, hbS] at hvoc
  have hGb : ∀ r ∈ Icc 0 S, ‖G r‖ ≤ ε * c + (Kf' + C₂ * R * ‖ω‖) := by
    intro r hr
    have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc r hr)
    have t1 : ‖(H' (w r) - D) (u r)‖ ≤ ε * c :=
      ((H' (w r) - D).le_opNorm _).trans (mul_le_mul (hF.deriv_close _ (hwt r hr)) (hc r hr)
        (norm_nonneg _) hF.eps_nonneg)
    have t2 : ‖H' (w r) ω‖ ≤ Kf' + C₂ * R * ‖ω‖ := by
      have hsplit : H' (w r) ω = H' (r • ω) ω + (H' (w r) - H' (r • ω)) ω := by
        rw [ContinuousLinearMap.sub_apply]; abel
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add (hfd r hr) ?_)
      refine ((H' (w r) - H' (r • ω)).le_opNorm ω).trans (mul_le_mul_of_nonneg_right ?_
        (norm_nonneg _))
      have hC := hH'lip _ (hwt r hr) _ (hF.mem_tube' hr)
      exact hC.trans (mul_le_mul_of_nonneg_left (hR r hr) hC₂)
    exact (norm_add_le _ _).trans (add_le_add t1 t2)
  have hgreen := norm_green_le D Pp Pm hd.dich.bound_m hd.dich.bound_p' hGb hs
  have hbd := norm_boundary_le D Pp Pm hd.dich.bound_m hd.dich.bound_p'
    (src H ω 0 + nonlin D H ω 0 (w 0 - (0 : ℝ) • ω)) (src H ω S + nonlin D H ω S (w S - S • ω)) hs
  have hM := hF.dich.M_nonneg
  show ‖u s‖ ≤ _
  rw [hvoc]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ M * ((Kf + ε * R) + (Kf + ε * R)) + M * S * (ε * c + (Kf' + C₂ * R * ‖ω‖)) :=
        add_le_add (hbd.trans (mul_le_mul_of_nonneg_left (add_le_add hF0 hFS) hM)) hgreen
    _ = _ := by ring

end FBField
end RenewalGeometry
