/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialCalculusSolve
import RenewalGeometry.Action.ExactInitialCalculusPartials

/-!
# The four original lapse–shift rows on the grid Sobolev spaces, with mesh-uniform bounds
  (`lem:supp-initial-calculus`, `eq:main-action-initial-constraints`: "in a lapse or shift derivative,
  every spatial load has one phase derivative; exact skew-adjointness transfers it to the stationary
  connection, so the output loses at most the declared Sobolev orders"; emergent-spacetime
  manuscript)

At a site `x`, the lapse row is `conLoc(Σ(e(x)), A)(x)` and the shift rows are
`-conLoc(e_a,j Π_i - e_a,i Π_j, A)(x)` (`ExactInitialCalculusPartials.lean`): pairings of the
coefficient arrays with the phase derivatives `δ_j A_i(x)` and with the magnetic remainder
`[A_i, A_j] + ρ^B_ij(x)`.  On `H^r_h` these are ONE spacing-dependent local analytic operator
(`CrowH`) applied to `(u, A, δA)` with `δ : H^{r+1}_h → H^r_h`:

* `Gcon`, `analyticAt_Gcon`: the coefficient functions (with the jointly analytic plaquette
  remainder `G^B`), analytic at `(0, 0)`;
* **`exists_derivBound_CrowH`**: mesh-uniform derivative bounds of every order on a fixed ball;
* **`exists_CrowH_val`**: for `h` and the sup norm of `A` below an `N`-independent radius the rows
  of `CrowH` are exactly the lapse and shift rows `conLoc`.
-/

open Filter Finset Metric Set
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.InitialCalculus

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open QuadJet PeriodicGridSobolev GridLocalOps IteratedDerivBounds UniformDerivBounds
open LocalSumGradient OddPhaseDerivativeReal

variable {N : ℕ} [NeZero N]

/-! ### Site-wise constraint rows with the jointly analytic plaquette remainder -/

/-- The magnetic remainder `[A_i, A_j] + G^B(s, (A_i, A_j(+e_i), -A_i(+e_j), -A_j))` at a site, from
the connection values `aS ℓ = A(x + o_ℓ)`. -/
def magLoc (s : ℝ) (aS : Fin 4 → LocVal) (i j : Fin 3) : M4 :=
  bracket (iota (aS 0 i.succ)) (iota (aS 0 j.succ)) +
    GB (s, ![iota (aS 0 i.succ), iota (aS i.succ j.succ), -iota (aS j.succ i.succ),
      -iota (aS 0 j.succ)])

/-- The site-wise row of a coefficient array `σ` (`dA j = δ_jA(x)`). -/
def conLocJ (s : ℝ) (σ : Fin 3 → Fin 3 → M4) (dA : Fin 3 → LocVal) (aS : Fin 4 → LocVal) : ℝ :=
  (∑ i, ∑ j, pairing (σ j i) (iota (dA j i.succ))) + sumLt fun i j => pairing (σ i j) (magLoc s aS i j)

/-- The shift coefficient array `e_a,j Π_i - e_a,i Π_j`. -/
def sigS (χ : ℝ) (E : M4) (a : Fin 3) : Fin 3 → Fin 3 → M4 :=
  fun i j => (Pi.single a (1 : ℝ) : Fin 3 → ℝ) j • piArr χ E i -
    (Pi.single a (1 : ℝ) : Fin 3 → ℝ) i • piArr χ E j

/-! ### The stencil of the constraint rows -/

/-- Field index: metric, unknowns, phase derivatives of the connection. -/
abbrev FC := Fin 6 ⊕ J30 ⊕ (Fin 3 × (Fin 4 × Fin 6))

/-- The components of the packing at level `r`. -/
def packCComp (hNo : Odd N) (r : ℕ) : FC → (XH N r × ZH N r →L[ℝ] GridH N r) :=
  Sum.elim (fun c => (GridH.incl (N := N) (r := r) (r' := r + 2) (by omega)).comp
      ((ContinuousLinearMap.proj c).comp ((ContinuousLinearMap.fst ℝ _ _).comp
        (ContinuousLinearMap.fst ℝ _ _))))
    (Sum.elim (fun m => (GridH.incl (N := N) (r := r) (r' := r + 1) (by omega)).comp
        ((ContinuousLinearMap.proj m).comp (ContinuousLinearMap.snd ℝ _ _)))
      (fun jm => (PhaseDerivSobolev.GridH.pdL hNo r jm.1).comp
        ((ContinuousLinearMap.proj (Sum.inl jm.2)).comp (ContinuousLinearMap.snd ℝ _ _))))

/-- The packing `(X, z) ↦ (u, z, δA)` at level `r`. -/
def packC (hNo : Odd N) (r : ℕ) : XH N r × ZH N r →L[ℝ] (FC → GridH N r) :=
  ContinuousLinearMap.pi (packCComp hNo r)

theorem norm_packCComp_le (hNo : Odd N) (r : ℕ) (i : FC) : ‖packCComp hNo r i‖ ≤ 1 := by
  have hp : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (c : ι),
      ‖(ContinuousLinearMap.proj c : (ι → GridH N s) →L[ℝ] GridH N s)‖ ≤ 1 := fun c =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      rw [one_mul]; exact norm_le_pi_norm v c
  have hc : ∀ {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
      [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (g : F →L[ℝ] G) (f : E →L[ℝ] F),
      ‖g‖ ≤ 1 → ‖f‖ ≤ 1 → ‖g.comp f‖ ≤ 1 := fun g f hg hf =>
    (ContinuousLinearMap.opNorm_comp_le g f).trans (by nlinarith [norm_nonneg g, norm_nonneg f])
  rcases i with c | m | jm
  · exact hc _ _ (GridH.norm_incl_le _) (hc _ _ (hp c) (hc _ _
      (ContinuousLinearMap.norm_fst_le _ _ _) (ContinuousLinearMap.norm_fst_le _ _ _)))
  · exact hc _ _ (GridH.norm_incl_le _) (hc _ _ (hp m) (ContinuousLinearMap.norm_snd_le _ _ _))
  · exact hc _ _ (PhaseDerivSobolev.GridH.norm_pdL_le hNo _ _) (hc _ _ (hp _)
      (ContinuousLinearMap.norm_snd_le _ _ _))

theorem norm_packC_le (hNo : Odd N) (r : ℕ) : ‖packC hNo r‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  calc ‖packCComp hNo r i q‖ ≤ ‖packCComp hNo r i‖ * ‖q‖ := (packCComp hNo r i).le_opNorm q
    _ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right (norm_packCComp_le hNo r i) (norm_nonneg _)

/-- The stencil: metric at `x`, connection at `x + o_ℓ`, phase derivatives at `x`. -/
abbrev KC := Fin 6 ⊕ (Fin 4 × (Fin 4 × Fin 6)) ⊕ (Fin 3 × (Fin 4 × Fin 6))

/-- Input slots. -/
def jC : KC → FC
  | Sum.inl c => Sum.inl c
  | Sum.inr (Sum.inl (_, m)) => Sum.inr (Sum.inl (Sum.inl m))
  | Sum.inr (Sum.inr jm) => Sum.inr (Sum.inr jm)

/-- Offsets. -/
def oC (N : ℕ) [NeZero N] : KC → Grid N
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (ℓ, _)) => (offs ℓ : Site N)
  | Sum.inr (Sum.inr _) => 0

/-- Metric value in the stencil. -/
def uC (ξ : KC → ℝ) : Fin 6 → ℝ := fun c => ξ (Sum.inl c)
/-- Connection values in the stencil. -/
def aC (ξ : KC → ℝ) (ℓ : Fin 4) : LocVal := fun μ k => ξ (Sum.inr (Sum.inl (ℓ, (μ, k))))
/-- Phase-derivative values in the stencil. -/
def dC (ξ : KC → ℝ) (j : Fin 3) : LocVal := fun μ k => ξ (Sum.inr (Sum.inr (j, (μ, k))))

/-- **The coefficient functions of the four constraint rows** (row `0`: lapse; row `a + 1`: shift
`a`, with the sign of `eq:main-action-initial-constraints`). -/
def Gcon (χ : ℝ) (row : Fin 4) (q : ℝ × (KC → ℝ)) : ℝ :=
  Fin.cases (conLocJ q.1 (sigmaArr χ (eU (uC q.2))) (dC q.2) (aC q.2))
    (fun a => -conLocJ q.1 (sigS χ (eU (uC q.2)) a) (dC q.2) (aC q.2)) row

/-- The four constraint rows on `H^r_h`. -/
def CrowH (hNo : Odd N) (χ : ℝ) (r : ℕ) (q : XH N r × ZH N r) : Fin 4 → GridH N r :=
  fun row => localOp r (Gcon χ row) 0 (hN N) jC (oC N) (packC hNo r q)

/-! ### Analyticity -/

theorem analyticAt_uC_comp : AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => uC q.2) (0, 0) :=
  AnalyticAt.pi fun c => analyticAt_eval_comp analyticAt_snd _

theorem analyticAt_aC_comp (ℓ : Fin 4) : AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => aC q.2 ℓ) (0, 0) :=
  AnalyticAt.pi fun μ => AnalyticAt.pi fun k => analyticAt_eval_comp analyticAt_snd _

theorem analyticAt_dC_comp (j : Fin 3) : AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => dC q.2 j) (0, 0) :=
  AnalyticAt.pi fun μ => AnalyticAt.pi fun k => analyticAt_eval_comp analyticAt_snd _

theorem analyticAt_magLoc_comp (i j : Fin 3) :
    AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => magLoc q.1 (aC q.2) i j) (0, 0) := by
  have hi : ∀ ℓ ν, AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => iota (aC q.2 ℓ ν)) (0, 0) := fun ℓ ν =>
    analyticAt_iota_comp' (analyticAt_pi_apply (analyticAt_aC_comp ℓ) ν)
  have hY : AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => (![iota (aC q.2 0 i.succ),
      iota (aC q.2 i.succ j.succ), -iota (aC q.2 j.succ i.succ), -iota (aC q.2 0 j.succ)] :
        Fin 4 → M4)) (0, 0) := by
    refine AnalyticAt.pi fun ℓ => ?_
    fin_cases ℓ
    · exact hi 0 i.succ
    · exact hi i.succ j.succ
    · exact (hi j.succ i.succ).neg
    · exact (hi 0 j.succ).neg
  have hG : AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => GB (q.1, ![iota (aC q.2 0 i.succ),
      iota (aC q.2 i.succ j.succ), -iota (aC q.2 j.succ i.succ), -iota (aC q.2 0 j.succ)])) (0, 0) := by
    refine analyticAt_GB.comp_of_eq (analyticAt_fst.prod hY) ?_
    have h0 : ∀ ℓ ν, aC (0 : KC → ℝ) ℓ ν = 0 := fun _ _ => rfl
    simp only [h0, iota_zero', neg_zero]
    congr 1
    funext ℓ; fin_cases ℓ <;> rfl
  exact (analyticAt_bracket_comp (hi 0 i.succ) (hi 0 j.succ)).add hG

theorem analyticAt_conLocJ_comp {σ : ℝ × (KC → ℝ) → Fin 3 → Fin 3 → M4}
    (hσ : ∀ i j, AnalyticAt ℝ (fun q => σ q i j) (0, 0)) :
    AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => conLocJ q.1 (σ q) (dC q.2) (aC q.2)) (0, 0) := by
  unfold conLocJ
  refine AnalyticAt.add (Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _
    fun j _ => analyticAt_pairing_comp (hσ j i) (analyticAt_iota_comp' (analyticAt_pi_apply
      (analyticAt_dC_comp j) i.succ))) ?_
  exact analyticAt_sumLt fun i j => analyticAt_pairing_comp (hσ i j) (analyticAt_magLoc_comp i j)

/-- **The constraint-row coefficient functions are analytic at `(0, 0)`.** -/
theorem analyticAt_Gcon (χ : ℝ) (row : Fin 4) : AnalyticAt ℝ (Gcon χ row) (0, 0) := by
  have he : AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => eU (uC q.2)) (0, 0) :=
    analyticAt_eU_comp analyticAt_uC_comp rfl
  cases row using Fin.cases with
  | zero =>
    show AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => conLocJ q.1 (sigmaArr χ (eU (uC q.2))) (dC q.2)
      (aC q.2)) (0, 0)
    exact analyticAt_conLocJ_comp fun i j => analyticAt_sigmaArr_comp χ i j he
  | succ a =>
    show AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => -conLocJ q.1 (sigS χ (eU (uC q.2)) a) (dC q.2)
      (aC q.2)) (0, 0)
    refine (analyticAt_conLocJ_comp fun i j => ?_).neg
    show AnalyticAt ℝ (fun q : ℝ × (KC → ℝ) => (Pi.single a (1 : ℝ) : Fin 3 → ℝ) j •
      piArr χ (eU (uC q.2)) i - (Pi.single a (1 : ℝ) : Fin 3 → ℝ) i • piArr χ (eU (uC q.2)) j) (0, 0)
    have h1 : AnalyticAt ℝ (fun _ : ℝ × (KC → ℝ) => (Pi.single a (1 : ℝ) : Fin 3 → ℝ) j) (0, 0) :=
      analyticAt_const
    have h2 : AnalyticAt ℝ (fun _ : ℝ × (KC → ℝ) => (Pi.single a (1 : ℝ) : Fin 3 → ℝ) i) (0, 0) :=
      analyticAt_const
    exact (h1.smul (analyticAt_piArr_comp χ i he)).sub (h2.smul (analyticAt_piArr_comp χ j he))

/-! ### Mesh-uniform derivative bounds -/

/-- **Mesh-uniform derivative bounds for the four constraint rows.** -/
theorem exists_derivBound_CrowH (χ : ℝ) (r : ℕ) (hr : 2 ≤ r) (K : ℕ) :
    ∃ ρ > 0, ∃ M ≥ 0, ∃ h₀ > 0, ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
      DerivBound (CrowH hNo χ r) (ball 0 ρ) K M := by
  obtain ⟨δL, hδL, CL, hCL, hLoc⟩ := localOp_derivBound_pi (r := r) (ι := FC) hr
    (c := (0 : KC → ℝ)) (fun row => analyticAt_Gcon χ row) K
  refine ⟨δL, hδL, CL, hCL, δL, hδL, fun N _ hNo hh => ?_⟩
  have habs : |hN N| < δL := by rw [abs_of_pos hN_pos]; exact hh
  have h2a := (hLoc N (hN N) habs jC (oC N)).comp_clm isOpen_ball (packC hNo r)
    (U := ball (0 : XH N r × ZH N r) δL) fun q hq => by
      rw [mem_ball_zero_iff] at hq ⊢
      calc ‖packC hNo r q‖ ≤ ‖packC hNo r‖ * ‖q‖ := (packC hNo r).le_opNorm q
        _ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right (norm_packC_le hNo r) (norm_nonneg _)
        _ < δL := by rw [one_mul]; exact hq
  have hP1 : max 1 ‖packC hNo r‖ = 1 := max_eq_left (norm_packC_le hNo r)
  rw [hP1, one_pow, mul_one] at h2a
  exact h2a

/-! ### Values of the constraint rows -/

theorem pd_toA (A : Conn N) (i j : Fin 3) (x : Site N) :
    pd j (toA A i) x = iota (fun k => pd j (fun y => A y i.succ k) x) := by
  have h := congrFun (pd_map j iotaLin (fun y => A y i.succ)) x
  change pd j (fun y => iotaLin (A y i.succ)) x = _
  rw [h]
  change iota (pd j (fun y => A y i.succ) x) = _
  congr 1
  funext k
  exact pd_pi_apply j _ x k

/-- **The rows of `CrowH` are the lapse and shift rows**, for `h` and the sup norm of the connection
below an `N`-independent radius. -/
theorem exists_CrowH_val : ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (hNo : Odd N) (χ : ℝ) (r : ℕ)
    (q : XH N r × ZH N r), hN N < δ → ‖connOfZ q.2‖ < δ → ∀ x : Grid N,
      GridH.val (CrowH hNo χ r q 0) x =
        conLoc (hN N) (sigmaArr χ (eU (metOf q.1.1 x))) (connOfZ q.2) x ∧
      ∀ a : Fin 3, GridH.val (CrowH hNo χ r q a.succ) x =
        -conLoc (hN N) (sigS χ (eU (metOf q.1.1 x)) a) (connOfZ q.2) x := by
  obtain ⟨δG, hδG, hG⟩ := exists_radius_G
  obtain ⟨C, hC1, hC⟩ := exists_iota_bound
  have hC0 : 0 ≤ C := by linarith
  refine ⟨δG / C, by positivity, fun N _ hNo χ r q hh hA x => ?_⟩
  set A := connOfZ q.2
  have hδC : δG / C ≤ δG := div_le_self hδG.le hC1
  have hAC : C * ‖A‖ < δG := by rw [lt_div_iff₀ (by positivity)] at hA; linarith
  -- the stencil values
  have hξ : (0 + fun k : KC => GridH.val (packC hNo r q (jC k)) (x + oC N k)) =
      fun k => match k with
        | Sum.inl c => metOf q.1.1 x c
        | Sum.inr (Sum.inl (ℓ, (μ, k))) => A (x + offs ℓ) μ k
        | Sum.inr (Sum.inr (j, (μ, k))) => pd j (fun y => A y μ k) x := by
    funext k
    rw [zero_add]
    rcases k with c | ⟨ℓ, μ, k⟩ | ⟨j, μ, k⟩
    · simp only [jC, oC, packC, ContinuousLinearMap.pi_apply, packCComp, Sum.elim_inl,
        ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.coe_fst', val_incl_eq, metOf, add_zero]
    · simp only [jC, oC, packC, ContinuousLinearMap.pi_apply, packCComp, Sum.elim_inr,
        Sum.elim_inl, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_snd', val_incl_eq]
      rfl
    · simp only [jC, oC, packC, ContinuousLinearMap.pi_apply, packCComp, Sum.elim_inr,
        ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.coe_snd', PhaseDerivSobolev.GridH.pdL_val, add_zero]
      rfl
  set ξ : KC → ℝ := fun k => match k with
    | Sum.inl c => metOf q.1.1 x c
    | Sum.inr (Sum.inl (ℓ, (μ, k))) => A (x + offs ℓ) μ k
    | Sum.inr (Sum.inr (j, (μ, k))) => pd j (fun y => A y μ k) x
  have hval : ∀ row, GridH.val (CrowH hNo χ r q row) x = Gcon χ row (hN N, ξ) := by
    intro row
    simp only [CrowH, localOp, GridH.val_mk]
    rw [hξ]
  have hu : uC ξ = metOf q.1.1 x := rfl
  have hd : ∀ j i, iota (dC ξ j i.succ) = pd j (toA A i) x := by
    intro j i; rw [pd_toA]; rfl
  have hm : ∀ i j, magLoc (hN N) (aC ξ) i j = magRem (hN N) A i j x := by
    intro i j
    have hpos := hN_pos (N := N)
    have hY : ‖(![iota (A x i.succ), iota (A (x + unitVec i) j.succ),
        -iota (A (x + unitVec j) i.succ), -iota (A x j.succ)] : Fin 4 → M4)‖ < δG := by
      have hb : ∀ y μ, ‖iota (A y μ)‖ ≤ C * ‖A‖ := fun y μ =>
        (hC _).trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm (A y) μ).trans
          (norm_le_pi_norm A y)) hC0)
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).mpr fun ℓ => ?_) hAC
      fin_cases ℓ <;> simp [hb, norm_neg]
    have hGB := (hG (hN N) hpos (hh.trans_le hδC)).2 _ hY
    have ha0 : aC ξ 0 = A x := by funext μ k; simp [aC, ξ]
    have has : ∀ i : Fin 3, aC ξ i.succ = A (x + unitVec i) := by
      intro i; funext μ k; simp [aC, ξ]
    unfold magLoc magRem
    rw [remB_eq_rhoB hN_ne_zero, ha0, has, has, hGB]
    rfl
  refine ⟨?_, fun a => ?_⟩
  · rw [hval]
    show conLocJ (hN N) (sigmaArr χ (eU (uC ξ))) (dC ξ) (aC ξ) = _
    unfold conLocJ conLoc
    simp only [hu, hd, hm]
  · rw [hval]
    show -conLocJ (hN N) (sigS χ (eU (uC ξ)) a) (dC ξ) (aC ξ) = _
    unfold conLocJ conLoc
    simp only [hu, hd, hm]

end RenewalGeometry.ExactPhaseAction.InitialCalculus
