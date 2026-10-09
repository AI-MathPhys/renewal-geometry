/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialCalculusIdent

/-!
# `lem:supp-initial-calculus`: the uniform original-action constraint calculus
  (emergent-spacetime manuscript)

* `analyticAt_imp_of_analyticAt` (generic): under `UniformImplicit.Hyp`, the implicit function is
  analytic at every point of its ball where `F` is analytic (analytic implicit function theorem +
  local uniqueness).
* `exists_analyticAt_FH`, `exists_analyticAt_CrowH`: the joint residual and the constraint rows are
  analytic on fixed (`N`-independent) balls.
* **`supp_initial_calculus`**: for `χ ≠ 0` and `r ≥ 2` there are constants independent of the
  cutoff and one ball `B(0, ρ) ⊂ P^r_h = (H^{r+2}_h)^6 × (H^{r+1}_h)^6` on which, for every odd `N`
  with `h < h₀`, the constraint map `C_h = CHmap` (the four original lapse–shift rows
  `(-∇_N 𝓗_h, ∇_β 𝓗_h)|_{N=1,β=0}` of the canonical Hamiltonian, values in `(H^r_h)^4`):
  - is analytic on `B(0, ρ)`;
  - vanishes at `0`, and `DC_h(0)(u, π) = (χ R₁(u), -2δ_jπ^{ij})` (`= L_h` for `χ = 1`);
  - satisfies `‖C_h(X) - DC_h(0)X‖ ≤ C‖X‖²`, `‖DC_h(X) - DC_h(0)‖ ≤ C‖X‖`
    (`eq:supp-initial-nonlinear-bounds`) and has uniform derivative bounds of order `K + 2`;
  - coincides near `0` with the constraint map `QuadJet.Cmap χ R` of the actual canonical
    Hamiltonian (analytic Legendre inverse at flat data), for every `R > 0` with `hR ≤ ε`; hence
    it is the analytic continuation of that germ to the common ball.
  No lapse or shift time derivative and no metric acceleration appears (by its type: `C_h` is a
  function of `X = (u, π)` only).
-/

open Filter Finset Metric Set
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.InitialCalculus

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open QuadJet PeriodicGridSobolev GridLocalOps IteratedDerivBounds UniformDerivBounds
open UniformImplicit

variable {N : ℕ} [NeZero N]

/-! ### Analytic implicit functions under the uniform hypotheses -/

section Generic

variable {E Z Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- **Analyticity of the uniform implicit function**: if `F` is analytic at `(x, z(x))`, then `z`
is analytic at `x` (analytic implicit function theorem and local uniqueness). -/
theorem analyticAt_imp_of_analyticAt {F : E × Z → Y} {T : Z ≃L[ℝ] Y} {K : ℕ} {M a ρ : ℝ}
    (h : Hyp F T K M a ρ) {x : E} (hx : ‖x‖ < del M a ρ)
    (hF : AnalyticAt ℝ F (x, imp F M a ρ x)) : AnalyticAt ℝ (imp F M a ρ) x := by
  set u : E × Z := (x, imp F M a ρ x)
  have hs := h.imp_spec hx
  have hu : u ∈ ball (0 : E × Z) (2 * sig M a ρ) := by
    rw [mem_ball_zero_iff, Prod.norm_def]
    have h1 : ‖x‖ ≤ sig M a ρ := hx.le.trans h.del_le_sig
    have := h.sig_pos
    exact lt_of_le_of_lt (max_le h1 hs.1) (by linarith)
  have hS := h.mapsTo_Sfun hu
  rw [mem_ball, dist_eq_norm] at hS
  obtain ⟨v, hv⟩ := exists_unit_of_norm_sub_one_lt (S := Hyp.Sfun T F u) (by linarith)
  have hinv : (fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ E Z).IsInvertible := by
    refine ⟨(ContinuousLinearEquiv.unitsEquiv ℝ Z v).trans T, ?_⟩
    ext z
    show T ((v : Z →L[ℝ] Z) z) = _
    rw [hv]
    simp [Hyp.Sfun]
  obtain ⟨ψ, hψ0, hψa, -, huniq, -⟩ := AnalyticImplicit.analytic_implicit_function hF hinv
  have hc : ContinuousAt (fun x' : E => ((x', imp F M a ρ x') : E × Z)) x :=
    continuousAt_id.prodMk (h.continuousAt_imp hx)
  have hball : ∀ᶠ x' in 𝓝 x, ‖x'‖ < del M a ρ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx)] with x' hx'
    simpa using hx'
  have hev : imp F M a ρ =ᶠ[𝓝 x] ψ := by
    filter_upwards [hc.eventually huniq, hball] with x' h1 h2
    have hF0 : F (x', imp F M a ρ x') = F u := by
      rw [(h.imp_spec h2).2, hs.2]
    exact ((h1.mp hF0)).symm
  exact hψa.congr hev.symm

end Generic

/-- A common analyticity ball for finitely many maps analytic at one point. -/
theorem exists_common_ball {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : ι → E → F} {x : E}
    (h : ∀ i, AnalyticAt ℝ (f i) x) : ∃ R > 0, ∀ i, ∀ y ∈ ball x R, AnalyticAt ℝ (f i) y := by
  have hev : ∀ᶠ y in 𝓝 x, ∀ i, AnalyticAt ℝ (f i) y :=
    Filter.eventually_all.mpr fun i => (h i).eventually_analyticAt
  obtain ⟨R, hR, hall⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨R, hR, fun i y hy => hall hy i⟩

/-! ### Analyticity of the residual and of the rows on fixed balls -/

theorem norm_fst_fst_apply_le (r : ℕ) (q : XH N r × ZH N r) : ‖q.1.1‖ ≤ ‖q‖ :=
  (norm_fst_le q.1).trans (norm_fst_le q)

theorem exists_analyticAt_FH (χ : ℝ) (r : ℕ) (hr : 2 ≤ r) :
    ∃ ρ > 0, ∃ h₀ > 0, ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
      ∀ q ∈ ball (0 : XH N r × ZH N r) ρ, AnalyticAt ℝ (FH hNo χ r) q := by
  obtain ⟨Rp, hRp, hp⟩ := exists_common_ball (f := pfun χ) (x := 0) (analyticAt_pfun χ)
  obtain ⟨RG, hRG, hG⟩ := exists_common_ball (f := Gst χ) (x := ((0 : ℝ), (0 : KF → ℝ)))
    (analyticAt_Gst χ)
  set K := Real.sqrt PeriodicGridSobolev.Kprod
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  refine ⟨min Rp RG / (K + 1), by positivity, RG, hRG, fun N _ hNo hh q hq => ?_⟩
  have hq' : ‖q‖ < min Rp RG / (K + 1) := by simpa using hq
  have hKq : K * ‖q‖ < min Rp RG := by
    rw [lt_div_iff₀ (by positivity)] at hq'
    nlinarith [norm_nonneg q]
  have h1 : AnalyticAt ℝ (fun q : XH N r × ZH N r => PW χ r q.1.1) q := by
    refine AnalyticAt.pi fun p => ?_
    have hpw : AnalyticAt ℝ (GridH.pointwise (N := N) (r := r + 2) (pfun χ p) 0) q.1.1 :=
      analyticAt_pointwise (by omega) (fun y hy => hp p y hy)
        (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_fst_fst_apply_le r q) hK)
          (hKq.trans_le (min_le_left _ _)))
    exact AnalyticAt.comp (g := GridH.pointwise (N := N) (r := r + 2) (pfun χ p) 0)
      (f := fun q : XH N r × ZH N r => q.1.1) hpw (analyticAt_fst.comp analyticAt_fst)
  have h2 : AnalyticAt ℝ (fun q : XH N r × ZH N r => fun m =>
      localOp (r + 1) (Gst χ m) 0 (hN N) jF (oF N) (packL r q)) q := by
    refine AnalyticAt.pi fun m => ?_
    have hpk : ‖packL r q‖ ≤ ‖q‖ := ((packL r).le_opNorm q).trans (by
      have := norm_packL_le (N := N) r; nlinarith [norm_nonneg q])
    have hloc : AnalyticAt ℝ (localOp (N := N) (r + 1) (Gst χ m) 0 (hN N) jF (oF N)) (packL r q) :=
      analyticAt_localOp (by omega) (fun y hy => hG m y hy)
        (by rw [abs_of_pos hN_pos]; exact hh)
        jF (oF N) (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpk hK) (hKq.trans_le (min_le_right _ _)))
    exact hloc.comp ((packL r).analyticAt q)
  have hT : AnalyticAt ℝ ((applyLinH (N := N) (r + 1) Lcoord).comp (pdAll hNo r))
      (PW χ r q.1.1) := ContinuousLinearMap.analyticAt _ _
  have h3 := AnalyticAt.comp (f := fun q : XH N r × ZH N r => PW χ r q.1.1) (x := q) hT h1
  have h4 := h3.add h2
  have e : (fun q : XH N r × ZH N r => (⇑((applyLinH (N := N) (r + 1) Lcoord).comp (pdAll hNo r)) ∘
      fun q : XH N r × ZH N r => PW χ r q.1.1) q + (fun m =>
        localOp (r + 1) (Gst χ m) 0 (hN N) jF (oF N) (packL r q))) = FH hNo χ r := by
    funext q'
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rfl
  rw [← e]
  exact h4


theorem exists_analyticAt_CrowH (χ : ℝ) (r : ℕ) (hr : 2 ≤ r) :
    ∃ ρ > 0, ∃ h₀ > 0, ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
      ∀ q ∈ ball (0 : XH N r × ZH N r) ρ, AnalyticAt ℝ (CrowH hNo χ r) q := by
  obtain ⟨RG, hRG, hG⟩ := exists_common_ball (f := Gcon χ) (x := ((0 : ℝ), (0 : KC → ℝ)))
    (analyticAt_Gcon χ)
  set K := Real.sqrt PeriodicGridSobolev.Kprod
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  refine ⟨RG / (K + 1), by positivity, RG, hRG, fun N _ hNo hh q hq => ?_⟩
  have hq' : ‖q‖ < RG / (K + 1) := by simpa using hq
  have hKq : K * ‖q‖ < RG := by
    rw [lt_div_iff₀ (by positivity)] at hq'
    nlinarith [norm_nonneg q]
  refine AnalyticAt.pi fun row => ?_
  have hpk : ‖packC hNo r q‖ ≤ ‖q‖ := ((packC hNo r).le_opNorm q).trans (by
    have := norm_packC_le hNo r; nlinarith [norm_nonneg q])
  have hloc : AnalyticAt ℝ (localOp (N := N) r (Gcon χ row) 0 (hN N) jC (oC N)) (packC hNo r q) :=
    analyticAt_localOp hr (fun y hy => hG row y hy) (by rw [abs_of_pos hN_pos]; exact hh)
      jC (oC N) (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpk hK) hKq)
  exact hloc.comp ((packC hNo r).analyticAt q)

/-! ### Odd cutoffs below any spacing threshold -/

/-- Every spacing threshold is met by some odd cutoff (non-vacuity of `hN N < h₀`). -/
theorem exists_odd_hN_lt {c : ℝ} (hc : 0 < c) : ∃ N : ℕ, ∃ _ : NeZero N, Odd N ∧ hN N < c := by
  obtain ⟨m, hm⟩ := exists_nat_gt c⁻¹
  refine ⟨2 * m + 1, ⟨by omega⟩, ⟨m, rfl⟩, ?_⟩
  unfold hN
  have hpos : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  rw [inv_lt_comm₀ hpos hc]
  calc c⁻¹ < m := hm
    _ ≤ ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-! ### `lem:supp-initial-calculus` -/

/-- **`lem:supp-initial-calculus` (uniform original-action constraint calculus).**  Let `χ ≠ 0`,
`r ≥ 2`, `K ∈ ℕ`.  There are constants, independent of the cutoff, such that for every odd `N`
with `h = 1/N < h₀`, the original-action constraint map `C_h = CHmap` on
`P^r_h = (H^{r+2}_h)^6 × (H^{r+1}_h)^6` with values in `(H^r_h)^4`:
1. is analytic on the common ball `B(0, ρ)`;
2. vanishes at `0`;
3. has `DC_h(0)(u, π) = (χ R₁(u), -2δ_jπ^{ij})` (`eq:supp-initial-linear-map`; `L_h` for `χ = 1`);
4. obeys `‖C_h(X) - DC_h(0)X‖ ≤ C‖X‖²`, `‖DC_h(X) - DC_h(0)‖ ≤ C‖X‖` on `B(0, ρ)`
   (`eq:supp-initial-nonlinear-bounds`), with all derivatives of order `≤ K + 2` bounded by `Mk`;
5. coincides near `0` with the initial constraint map `QuadJet.Cmap χ R` of the canonical
   Hamiltonian `𝓗_h` of `eq:main-action-hamiltonian` (analytic Legendre inverse at flat data,
   actual stationary connection selected in the `R`-ball), for every `R > 0` with `hR ≤ ε`. -/
theorem supp_initial_calculus {χ : ℝ} (hχ : χ ≠ 0) (r : ℕ) (hr : 2 ≤ r) (K : ℕ) :
    ∃ M ρ' ρ C h₀ ε Mk : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 < h₀ ∧ 0 < ε ∧
      ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
        AnalyticOnNhd ℝ (CHmap hNo χ r M (aBlock hχ) ρ') (ball 0 ρ) ∧
        CHmap hNo χ r M (aBlock hχ) ρ' 0 = 0 ∧
        (∀ X : XH N r, fderiv ℝ (CHmap hNo χ r M (aBlock hχ) ρ') 0 X =
          encY r (fun x => χ * R1F (metOf X.1) x, divF (metOf X.2))) ∧
        (∀ X ∈ ball (0 : XH N r) ρ,
          ‖CHmap hNo χ r M (aBlock hχ) ρ' X - fderiv ℝ (CHmap hNo χ r M (aBlock hχ) ρ') 0 X‖ ≤
              C * ‖X‖ ^ 2 ∧
          ‖fderiv ℝ (CHmap hNo χ r M (aBlock hχ) ρ') X -
              fderiv ℝ (CHmap hNo χ r M (aBlock hχ) ρ') 0‖ ≤ C * ‖X‖) ∧
        DerivBound (CHmap hNo χ r M (aBlock hχ) ρ') (ball 0 ρ) (K + 2) Mk ∧
        (∀ R : ℝ, 0 < R → hN N * R ≤ ε →
          ∀ᶠ X in 𝓝 (0 : XH N r), CHmap hNo χ r M (aBlock hχ) ρ' X = encY r (Cmap χ R (decX X))) := by
  obtain ⟨M, ρF, h₁, hh₁, hyp⟩ := exists_uniform_solve hχ r hr K
  obtain ⟨ρC, hρC, MC, hMC, h₂, hh₂, hC⟩ := exists_derivBound_CrowH χ r hr (K + 2)
  obtain ⟨ρAF, hρAF, h₃, hh₃, hAF⟩ := exists_analyticAt_FH χ r hr
  obtain ⟨ρAC, hρAC, h₄, hh₄, hAC⟩ := exists_analyticAt_CrowH χ r hr
  obtain ⟨δI, hδI, hident⟩ := exists_eventually_CHmap_eq_Cmap
  obtain ⟨ε, hε, hflat⟩ := flat_chart χ hχ
  -- positivity of the radius of the uniform solve
  obtain ⟨N₁, hN₁, hNo₁, hh₁'⟩ := exists_odd_hN_lt hh₁
  have hρF : 0 < ρF := (hyp N₁ hNo₁ hh₁').hρ
  set a := aBlock hχ
  set ρ' := min ρF (min ρC (min ρAF ρAC))
  have hρ' : 0 < ρ' := lt_min hρF (lt_min hρC (lt_min hρAF hρAC))
  set h₀ := min h₁ (min h₂ (min h₃ (min h₄ (min δI ε))))
  have hh₀ : 0 < h₀ := lt_min hh₁ (lt_min hh₂ (lt_min hh₃ (lt_min hh₄ (lt_min hδI hε))))
  have hyp' : ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
      Hyp (FH hNo χ r) (TH (N := N) hχ r) K M a ρ' := fun N _ hNo hh =>
    hyp_mono_rho (hyp N hNo (hh.trans_le (min_le_left _ _))) hρ' (min_le_left _ _)
  obtain ⟨N₀, hN₀, hNo₀, hh₀'⟩ := exists_odd_hN_lt hh₀
  have hρ : 0 < del M a ρ' := (hyp' N₀ hNo₀ hh₀').del_pos
  set ρ := del M a ρ'
  set Mf := max 1 ρ + impC K M a ρ'
  set Mk := (Nat.factorial (K + 2) : ℝ) * MC * max 1 Mf ^ (K + 2)
  have hMk : 0 ≤ Mk := by positivity
  refine ⟨M, ρ', ρ, Mk, h₀, ε, Mk, hρ, hMk, hh₀, hε, fun N _ hNo hh => ?_⟩
  have hh2 : hN N < h₂ := hh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hh3 : hN N < h₃ := hh.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hh4 : hN N < h₄ := hh.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hhI : hN N < δI := hh.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hhε : hN N < ε := hh.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have h := hyp' N hNo hh
  set CH := CHmap hNo χ r M a ρ'
  -- the pair `X ↦ (X, z_h(X))` stays in the balls of the residual and of the rows
  have hpair : ∀ X ∈ ball (0 : XH N r) ρ, ‖((X, imp (FH hNo χ r) M a ρ' X) : XH N r × ZH N r)‖ < ρ' := by
    intro X hX
    have hX' : ‖X‖ < ρ := by simpa using hX
    have hs := (h.imp_spec hX').1
    rw [Prod.norm_def]
    exact lt_of_le_of_lt (max_le (hX'.le.trans h.del_le_sig) hs) h.sig_lt
  -- derivative bounds of every order `≤ K + 2`
  have hD : DerivBound CH (ball 0 ρ) (K + 2) Mk := by
    have himp := h.derivBound_imp
    have hgraph := derivBound_graph himp isOpen_ball hρ.le ball_subset_closedBall
      (himp.nonneg (mem_ball_self hρ))
    have hmaps : MapsTo (fun X : XH N r => (X, imp (FH hNo χ r) M a ρ' X))
        (ball (0 : XH N r) ρ) (ball (0 : XH N r × ZH N r) ρC) := fun X hX => by
      rw [mem_ball_zero_iff]
      exact (hpair X hX).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hc := derivBound_comp (g := CrowH hNo χ r) (hC N hNo hh2) isOpen_ball hgraph isOpen_ball
      hmaps
    exact hc.congr fun X => rfl
  -- identification with `Cmap` and the linearization
  have hU1 := hflat N 1 one_pos (by rw [mul_one]; exact hhε.le)
  obtain ⟨U, hU⟩ := hU1
  have hev := hident N hNo hU hχ r K h hhI
  have hCm := fderiv_initialConstraint_flat (N := N) hU hχ
  have hdC : HasFDerivAt (fun X : XH N r => encYL r (Cmap χ 1 (decXL r X)))
      ((encYL r).comp ((fderiv ℝ (Cmap χ 1) 0).comp (decXL r))) 0 := by
    have h1 : HasFDerivAt (Cmap χ (1 : ℝ)) (fderiv ℝ (Cmap χ 1) 0) (decXL (N := N) r 0) := by
      rw [map_zero]; exact hCm.2.1.differentiableAt.hasFDerivAt
    exact (encYL r).hasFDerivAt.comp (0 : XH N r) (h1.comp (0 : XH N r) (decXL r).hasFDerivAt)
  have hev' : CH =ᶠ[𝓝 0] fun X : XH N r => encYL r (Cmap χ 1 (decXL r X)) := hev
  have hD0 : HasFDerivAt CH ((encYL r).comp ((fderiv ℝ (Cmap χ 1) 0).comp (decXL r))) 0 :=
    hdC.congr_of_eventuallyEq hev'
  have hCH0 : CH 0 = 0 := by
    have h0 : CH 0 = encY r (Cmap χ 1 (decX (0 : XH N r))) := hev.self_of_nhds
    have hd0 : decX (0 : XH N r) = 0 := rfl
    rw [h0, hd0, hCm.1]
    funext row
    cases row using Fin.cases <;> exact GridH.ext fun x => rfl
  -- Taylor bounds
  have hdiff : ∀ X ∈ ball (0 : XH N r) ρ, HasFDerivAt CH (fderiv ℝ CH X) X :=
    fun X hX => ((hD.contDiffAt isOpen_ball hX).differentiableAt (by simp)).hasFDerivAt
  have hL : ∀ X ∈ ball (0 : XH N r) ρ, ‖fderiv ℝ CH X - fderiv ℝ CH 0‖ ≤ Mk * ‖X‖ := by
    intro X hX
    have := norm_fderiv_sub_le_of_derivBound (K := K) hD isOpen_ball (convex_ball 0 _) hX
      (mem_ball_self hρ)
    simpa using this
  have hT := LyapunovSchmidt.taylor_remainder_bounds (Φ := CH) (DΦ := fun X => fderiv ℝ CH X)
    (ρ := ρ) hdiff hL hMk hCH0
  refine ⟨fun X hX => ?_, hCH0, fun X => ?_, fun X hX => ⟨hT.2 X hX, hL X hX⟩, hD,
    fun R hR hhR => ?_⟩
  · -- analyticity
    have hq := hpair X hX
    have hX' : ‖X‖ < ρ := by simpa using hX
    have hFa : AnalyticAt ℝ (FH hNo χ r) (X, imp (FH hNo χ r) M a ρ' X) :=
      hAF N hNo hh3 _ (mem_ball_zero_iff.mpr (hq.trans_le ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))
    have hza := analyticAt_imp_of_analyticAt h hX' hFa
    have hCa : AnalyticAt ℝ (CrowH hNo χ r) (X, imp (FH hNo χ r) M a ρ' X) :=
      hAC N hNo hh4 _ (mem_ball_zero_iff.mpr (hq.trans_le ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))))
    exact AnalyticAt.comp (g := CrowH hNo χ r)
      (f := fun X : XH N r => ((X, imp (FH hNo χ r) M a ρ' X) : XH N r × ZH N r)) hCa
      (analyticAt_id.prod hza)
  · -- the linearization
    rw [hD0.fderiv]
    simp only [ContinuousLinearMap.comp_apply, encYL_apply, decXL_apply]
    have := hCm.2.2 (metOf X.1) (metOf X.2)
    rw [show decX X = (metOf X.1, metOf X.2) from rfl, this]
  · obtain ⟨U', hU'⟩ := hflat N R hR hhR
    exact hident N hNo hU' hχ r K h hhI

/-- Non-vacuity: the hypotheses of `supp_initial_calculus` are met (`χ = 1`, `r = 2`), and every
spacing threshold is met by an odd cutoff (`exists_odd_hN_lt`). -/
example : ∃ N : ℕ, ∃ _ : NeZero N, Odd N ∧ hN N < 1 / 100 := exists_odd_hN_lt (by norm_num)

example := supp_initial_calculus (χ := 1) one_ne_zero 2 le_rfl 0

end RenewalGeometry.ExactPhaseAction.InitialCalculus
