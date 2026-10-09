/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridSobolevSpace

/-!
# Uniform derivative bounds for spacing-dependent local analytic operators on `H^r_h`
  (infrastructure for `lem:supp-initial-calculus`: the stationary row, the Legendre row and the
  four constraint rows are finite sums of shifted pointwise analytic maps whose coefficients
  depend analytically on the lattice spacing; emergent-spacetime manuscript)

On the periodic grid `(ℤ/N)³` with the grid Sobolev spaces `H^r_h` (`GridH N r`, `r ≥ 2`):

* `GridH.transL a` (`u ↦ u(· + a)`, any `a ∈ (ℤ/N)³`): an isometry, `‖transL a‖ ≤ 1`
  (`sobSq_translate`: the grid Sobolev norm is translation invariant).
* `GridH.constArr c`: the constant array, `‖constArr c‖_{r,h} = |c|`.
* `DerivBound.comp_affine`: right composition with an affine map `u ↦ b + L u`.
* **`localOp_derivBound`**: let `G : ℝ × (κ → ℝ) → ℝ` be analytic at `(0, c)` (the first variable
  is the lattice spacing).  For every `K` there are `δ > 0` and `C ≥ 0`, **independent of the
  mesh**, such that for every `N`, every spacing parameter `|s| < δ`, every choice of input
  slots `j : κ → ι` and offsets `o : κ → (ℤ/N)³`, the local operator
  `u ↦ (x ↦ G(s, c + (u_{j k}(x + o k))_k))` on `(H^r_h)^ι` satisfies
  `DerivBound _ (B(0, δ)) K C`.  `localOp_derivBound_pi` is the version for finitely many
  output components (values in `(H^r_h)^μ`).
-/

open Finset Filter Topology Set
open scoped BigOperators ContDiff

namespace RenewalGeometry.GridLocalOps

open LatticeTorusPlancherel IteratedDerivBounds PeriodicGridSobolev

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### Translations -/

theorem S_pow_apply (i : Fin 3) (n : ℕ) (u : Grid N → ℂ) (x : Grid N) :
    (S i ^ n) u x = u (x + (n : ZMod N) • unit i) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, S_apply, ih]
    congr 1
    push_cast
    rw [add_smul, one_smul]
    abel

theorem Sα_apply (δ : Fin 3 → ℕ) (u : Grid N → ℂ) (x : Grid N) :
    Sα δ u x = u (x + fun i => ((δ i : ℕ) : ZMod N)) := by
  simp only [Sα, Module.End.mul_apply, S_pow_apply]
  congr 1
  funext i
  fin_cases i <;> simp [PeriodicGridSobolev.unit, Pi.single_apply]

theorem eq_val_sum (a : Grid N) : (fun i => (((a i).val : ℕ) : ZMod N)) = a := by
  funext i; simp

/-- The grid Sobolev norm is invariant under every lattice translation. -/
theorem sobSq_translate (r : ℕ) (a : Grid N) (u : Grid N → ℂ) :
    sobSq r (fun x => u (x + a)) = sobSq r u := by
  have h : (fun x => u (x + a)) = Sα (fun i => (a i).val) u := by
    funext x
    rw [Sα_apply, eq_val_sum]
  rw [h, sobSq_Sα]

namespace GridH

variable {r : ℕ}

/-- The translation `u ↦ u(· + a)` on `H^r_h`. -/
def transL (r : ℕ) (a : Grid N) : PeriodicGridSobolev.GridH N r →L[ℝ] PeriodicGridSobolev.GridH N r :=
  PeriodicGridSobolev.GridH.ofBound (LinearMap.funLeft ℝ ℝ (fun x : Grid N => x + a)) 1
    fun u => by
      rw [PeriodicGridSobolev.GridH.norm_def, PeriodicGridSobolev.GridH.norm_def, one_mul]
      unfold sobNorm
      have e : PeriodicGridSobolev.GridH.cxv (PeriodicGridSobolev.GridH.mk (r := r)
          (LinearMap.funLeft ℝ ℝ (fun x : Grid N => x + a) (PeriodicGridSobolev.GridH.val u))) =
          fun x => PeriodicGridSobolev.GridH.cxv u (x + a) := rfl
      rw [e, sobSq_translate]

@[simp] theorem transL_val (a : Grid N) (u : PeriodicGridSobolev.GridH N r) (x : Grid N) :
    PeriodicGridSobolev.GridH.val (transL r a u) x = PeriodicGridSobolev.GridH.val u (x + a) := rfl

theorem norm_transL_le (a : Grid N) : ‖transL (N := N) r a‖ ≤ 1 :=
  PeriodicGridSobolev.GridH.norm_ofBound_le _ zero_le_one _

/-- The constant array. -/
def constArr (r : ℕ) (c : ℝ) : PeriodicGridSobolev.GridH N r :=
  PeriodicGridSobolev.GridH.mk fun _ => c

@[simp] theorem constArr_val (c : ℝ) (x : Grid N) :
    PeriodicGridSobolev.GridH.val (constArr (N := N) r c) x = c := rfl

theorem norm_constArr (c : ℝ) : ‖constArr (N := N) r c‖ = |c| := by
  rw [PeriodicGridSobolev.GridH.norm_def]
  have : PeriodicGridSobolev.GridH.cxv (constArr (N := N) r c) = fun _ => ((c : ℝ) : ℂ) := rfl
  rw [this, PeriodicGridSobolev.sobNorm_const, Complex.norm_real, Real.norm_eq_abs]

end GridH

/-! ### Affine right composition -/

section Affine

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem derivBound_translate {g : F → G} {V : Set F} {K : ℕ} {M : ℝ} (hg : DerivBound g V K M)
    (_hV : IsOpen V) (b : F) :
    DerivBound (fun v => g (b + v)) ((fun v => b + v) ⁻¹' V) K M := by
  refine ⟨hg.contDiffOn.comp (contDiffOn_const.add contDiffOn_id) fun v hv => hv,
    fun v hv k hk => ?_⟩
  rw [iteratedFDeriv_comp_add_left]
  exact hg.bound _ hv k hk

/-- Right composition with an affine map `u ↦ b + L u`. -/
theorem derivBound_comp_affine {g : F → G} {V : Set F} {K : ℕ} {M : ℝ} (hg : DerivBound g V K M)
    (hV : IsOpen V) (b : F) (L : E →L[ℝ] F) {U : Set E} (hmaps : ∀ u ∈ U, b + L u ∈ V) :
    DerivBound (fun u => g (b + L u)) U K (M * max 1 ‖L‖ ^ K) := by
  have h1 := derivBound_translate hg hV b
  have hV' : IsOpen ((fun v => b + v) ⁻¹' V) := hV.preimage (continuous_const.add continuous_id)
  exact h1.comp_clm hV' L fun u hu => hmaps u hu

end Affine

/-! ### Local analytic operators -/

section LocalOp

variable {r : ℕ} {ι κ μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ]

/-- The local operator `u ↦ (x ↦ G(s, c + (u_{j k}(x + o k))_k))`. -/
def localOp (r : ℕ) (G : ℝ × (κ → ℝ) → ℝ) (c : κ → ℝ) (s : ℝ) (j : κ → ι) (o : κ → Grid N)
    (u : ι → PeriodicGridSobolev.GridH N r) : PeriodicGridSobolev.GridH N r :=
  PeriodicGridSobolev.GridH.mk fun x =>
    G (s, c + fun k => PeriodicGridSobolev.GridH.val (u (j k)) (x + o k))

/-- The affine slot map `u ↦ (none ↦ s, some k ↦ u_{j k}(· + o k))`. -/
def slotLin (r : ℕ) (j : κ → ι) (o : κ → Grid N) :
    (ι → PeriodicGridSobolev.GridH N r) →L[ℝ] (Option κ → PeriodicGridSobolev.GridH N r) :=
  ContinuousLinearMap.pi fun t => Option.casesOn (motive := fun t =>
      (ι → PeriodicGridSobolev.GridH N r) →L[ℝ] PeriodicGridSobolev.GridH N r) t 0
    fun k => (GridH.transL r (o k)).comp (ContinuousLinearMap.proj (j k))

theorem norm_slotLin_le (j : κ → ι) (o : κ → Grid N) : ‖slotLin (N := N) r j o‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun t => ?_
  cases t with
  | none => simp [slotLin]
  | some k =>
    simp only [slotLin, ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, one_mul]
    refine ((GridH.transL r (o k)).le_opNorm _).trans ?_
    calc ‖GridH.transL r (o k)‖ * ‖u (j k)‖ ≤ 1 * ‖u‖ :=
          mul_le_mul (GridH.norm_transL_le _) (norm_le_pi_norm u (j k)) (norm_nonneg _) zero_le_one
      _ = ‖u‖ := one_mul _

/-- The constant part `none ↦ s`. -/
def slotConst (r : ℕ) (s : ℝ) : Option κ → PeriodicGridSobolev.GridH N r :=
  fun t => Option.casesOn t (GridH.constArr r s) fun _ => 0

theorem norm_slotConst (s : ℝ) : ‖(slotConst (N := N) (κ := κ) r s)‖ ≤ |s| := by
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg s)).mpr fun t => ?_
  cases t with
  | none => simp [slotConst, GridH.norm_constArr]
  | some k => simp [slotConst]

/-- The scalar function of the `Option κ` coordinates. -/
def optFun (G : ℝ × (κ → ℝ) → ℝ) : (Option κ → ℝ) → ℝ := fun v => G (v none, fun k => v (some k))

/-- The base point `(0, c)` in `Option κ` coordinates. -/
def optPt (c : κ → ℝ) : Option κ → ℝ := fun t => Option.casesOn t 0 c

theorem localOp_eq (G : ℝ × (κ → ℝ) → ℝ) (c : κ → ℝ) (s : ℝ) (j : κ → ι) (o : κ → Grid N)
    (u : ι → PeriodicGridSobolev.GridH N r) :
    localOp r G c s j o u = PeriodicGridSobolev.GridH.pointwise (optFun G) (optPt c)
      (slotConst r s + slotLin r j o u) := by
  refine PeriodicGridSobolev.GridH.ext fun x => ?_
  simp only [localOp, PeriodicGridSobolev.GridH.pointwise, PeriodicGridSobolev.GridH.val_mk, optFun]
  refine congrArg G (Prod.ext ?_ ?_)
  · simp [optPt, slotConst, slotLin]
  · funext k
    simp [optPt, slotConst, slotLin]

theorem analyticAt_optFun {G : ℝ × (κ → ℝ) → ℝ} {c : κ → ℝ} (hG : AnalyticAt ℝ G (0, c)) :
    AnalyticAt ℝ (optFun G) (optPt c) := by
  have h1 : AnalyticAt ℝ (fun v : Option κ → ℝ => (v none, fun k => v (some k))) (optPt c) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Option κ => ℝ) none).analyticAt _).prod
      (AnalyticAt.pi fun k =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Option κ => ℝ) (some k)).analyticAt _)
  exact hG.comp_of_eq h1 (by simp [optPt])

/-- **Uniform derivative bounds for spacing-dependent local analytic operators.** -/
theorem localOp_derivBound (hr : 2 ≤ r) {G : ℝ × (κ → ℝ) → ℝ} {c : κ → ℝ}
    (hG : AnalyticAt ℝ G (0, c)) (K : ℕ) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (s : ℝ), |s| < δ → ∀ (j : κ → ι) (o : κ → Grid N),
      DerivBound (localOp (N := N) r G c s j o) (Metric.ball 0 δ) K C := by
  obtain ⟨δ, hδ, C, hC, h⟩ := PeriodicGridSobolev.GridH.pointwise_derivBound (r := r) hr
    (analyticAt_optFun hG) K
  refine ⟨δ, hδ, C, hC, fun N _ s hs j o => ?_⟩
  have hb := derivBound_comp_affine (h N) Metric.isOpen_ball (slotConst r s) (slotLin r j o)
    (U := Metric.ball (0 : ι → PeriodicGridSobolev.GridH N r) δ) fun u hu => by
      rw [Metric.mem_ball, dist_zero_right] at hu ⊢
      have h2 : ‖slotLin r j o u‖ ≤ ‖u‖ := by
        refine ((slotLin r j o).le_opNorm u).trans ?_
        have := norm_slotLin_le (N := N) (r := r) j o
        nlinarith [norm_nonneg u]
      have hsum : ‖slotConst (N := N) (κ := κ) r s + slotLin r j o u‖ ≤ max |s| ‖u‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun t => ?_
        cases t with
        | none =>
          simp only [Pi.add_apply, slotConst, slotLin, ContinuousLinearMap.pi_apply,
            ContinuousLinearMap.zero_apply, add_zero, GridH.norm_constArr]
          exact le_max_left _ _
        | some k =>
          have := norm_le_pi_norm (slotLin r j o u) (some k)
          simp only [Pi.add_apply, slotConst, zero_add]
          exact (this.trans h2).trans (le_max_right _ _)
      exact lt_of_le_of_lt hsum (max_lt hs hu)
  have hL1 : max 1 ‖slotLin (N := N) r j o‖ = 1 := max_eq_left (norm_slotLin_le j o)
  rw [hL1, one_pow, mul_one] at hb
  exact hb.congr fun u => (localOp_eq G c s j o u).symm

/-- Vector-valued version: finitely many output components `G m`, one common ball and constant. -/
theorem localOp_derivBound_pi (hr : 2 ≤ r) {G : μ → ℝ × (κ → ℝ) → ℝ} {c : κ → ℝ}
    (hG : ∀ m, AnalyticAt ℝ (G m) (0, c)) (K : ℕ) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (s : ℝ), |s| < δ → ∀ (j : κ → ι) (o : κ → Grid N),
      DerivBound (fun u m => localOp (N := N) r (G m) c s j o u) (Metric.ball 0 δ) K C := by
  obtain ⟨δ, hδ, C, hC, h⟩ := PeriodicGridSobolev.GridH.uniformize'
    (fun m δ C => ∀ (N : ℕ) [NeZero N] (s : ℝ), |s| < δ → ∀ (j : κ → ι) (o : κ → Grid N),
      DerivBound (localOp (N := N) r (G m) c s j o) (Metric.ball 0 δ) K C)
    (fun m δ δ' C C' _ hδ' hCC' hP N _ s hs j o =>
      ((hP N s (lt_of_lt_of_le hs hδ') j o).subset (Metric.ball_subset_ball hδ')).mono le_rfl hCC')
    (fun m => localOp_derivBound hr (hG m) K)
  exact ⟨δ, hδ, C, hC, fun N _ s hs j o =>
    DerivBound.pi (fun m => h m N s hs j o) Metric.isOpen_ball hC⟩

end LocalOp

/-! ### Analyticity of local operators on a fixed ball -/

section AnalyticLocal

variable {r : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The stencil evaluation at a site, as a continuous linear map. -/
def stencilL (r : ℕ) (j : κ → ι) (o : κ → Grid N) (x : Grid N) :
    (ι → PeriodicGridSobolev.GridH N r) →L[ℝ] (κ → ℝ) :=
  ContinuousLinearMap.pi fun k => (ContinuousLinearMap.proj (x + o k)).comp
    ((PeriodicGridSobolev.GridH.toFunL (N := N) (r := r) :
      PeriodicGridSobolev.GridH N r →L[ℝ] (Grid N → ℝ)).comp (ContinuousLinearMap.proj (j k)))

theorem norm_stencilL_apply_le (hr : 2 ≤ r) (j : κ → ι) (o : κ → Grid N) (x : Grid N)
    (u : ι → PeriodicGridSobolev.GridH N r) :
    ‖stencilL r j o x u‖ ≤ Real.sqrt PeriodicGridSobolev.Kprod * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  have h := PeriodicGridSobolev.GridH.abs_apply_le hr (u (j k)) (x + o k)
  rw [Real.norm_eq_abs]
  exact h.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm u (j k)) (Real.sqrt_nonneg _))

/-- **Local operators are analytic on a fixed ball** (radius independent of the mesh). -/
theorem analyticAt_localOp (hr : 2 ≤ r) {G : ℝ × (κ → ℝ) → ℝ} {c : κ → ℝ} {R : ℝ}
    (hG : ∀ y ∈ Metric.ball ((0 : ℝ), c) R, AnalyticAt ℝ G y) {s : ℝ} (hs : |s| < R)
    (j : κ → ι) (o : κ → Grid N) {u : ι → PeriodicGridSobolev.GridH N r}
    (hu : Real.sqrt PeriodicGridSobolev.Kprod * ‖u‖ < R) :
    AnalyticAt ℝ (localOp (N := N) r G c s j o) u := by
  have e : localOp (N := N) r G c s j o = fun u => (PeriodicGridSobolev.GridH.toFunL (N := N)
      (r := r)).symm (fun x => G (s, c + stencilL r j o x u)) := rfl
  rw [e]
  refine ((PeriodicGridSobolev.GridH.toFunL (N := N) (r := r)).symm.analyticAt _).comp
    (AnalyticAt.pi fun x => ?_)
  have hmem : ((s, c + stencilL r j o x u) : ℝ × (κ → ℝ)) ∈ Metric.ball ((0 : ℝ), c) R := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, dist_eq_norm, add_sub_cancel_left]
    exact max_lt hs ((norm_stencilL_apply_le hr j o x u).trans_lt hu)
  have hlin : AnalyticAt ℝ (fun w : ι → PeriodicGridSobolev.GridH N r =>
      ((s, c + stencilL r j o x w) : ℝ × (κ → ℝ))) u :=
    analyticAt_const.prod (analyticAt_const.add ((stencilL r j o x).analyticAt u))
  exact AnalyticAt.comp (g := G) (f := fun w : ι → PeriodicGridSobolev.GridH N r =>
    ((s, c + stencilL r j o x w) : ℝ × (κ → ℝ))) (hG _ hmem) hlin

/-- **Pointwise compositions are analytic on a fixed ball.** -/
theorem analyticAt_pointwise (hr : 2 ≤ r) {A : (ι → ℝ) → ℝ} {c : ι → ℝ} {R : ℝ}
    (hA : ∀ y ∈ Metric.ball c R, AnalyticAt ℝ A y) {u : ι → PeriodicGridSobolev.GridH N r}
    (hu : Real.sqrt PeriodicGridSobolev.Kprod * ‖u‖ < R) :
    AnalyticAt ℝ (PeriodicGridSobolev.GridH.pointwise (N := N) (r := r) A c) u := by
  rw [PeriodicGridSobolev.GridH.pointwise_eq]
  refine ((PeriodicGridSobolev.GridH.toFunL (N := N) (r := r)).symm.analyticAt _).comp
    (AnalyticAt.pi fun x => ?_)
  have hmem : c + PeriodicGridSobolev.GridH.evalAt x u ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (PeriodicGridSobolev.GridH.norm_evalAt_le hr x u).trans_lt hu
  have hlin : AnalyticAt ℝ (fun w : ι → PeriodicGridSobolev.GridH N r =>
      c + PeriodicGridSobolev.GridH.evalAt x w) u :=
    analyticAt_const.add ((PeriodicGridSobolev.GridH.evalAt (N := N) (r := r) (ι := ι) x).analyticAt u)
  exact AnalyticAt.comp (g := A) (f := fun w : ι → PeriodicGridSobolev.GridH N r =>
    c + PeriodicGridSobolev.GridH.evalAt x w) (hA _ hmem) hlin

end AnalyticLocal

/-! ### Site-wise constant linear maps -/

section SiteLin

variable {r : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The coefficient bound `Σ_m Σ_n |L(e_n)_m|` of a linear map of coordinate vectors. -/
def coefNorm (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) : ℝ := ∑ m, ∑ n, |L (Pi.single n 1) m|

theorem coefNorm_nonneg (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) : 0 ≤ coefNorm L :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The site-wise application of a fixed linear map `L : ℝ^ι → ℝ^κ` to arrays in `H^r_h`. -/
def applyLinH (r : ℕ) (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    (ι → PeriodicGridSobolev.GridH N r) →L[ℝ] (κ → PeriodicGridSobolev.GridH N r) :=
  ∑ m, ∑ n, (L (Pi.single n 1) m) • ((ContinuousLinearMap.single ℝ
    (fun _ : κ => PeriodicGridSobolev.GridH N r) m).comp (ContinuousLinearMap.proj n))

theorem applyLinH_apply (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (v : ι → PeriodicGridSobolev.GridH N r)
    (m : κ) : applyLinH r L v m = ∑ n, (L (Pi.single n 1) m) • v n := by
  classical
  simp only [applyLinH, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.single_apply]
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
  · simp

/-- Site-wise values: `(L v)(x) = L(v(x))`. -/
theorem applyLinH_val (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (v : ι → PeriodicGridSobolev.GridH N r)
    (m : κ) (x : Grid N) :
    PeriodicGridSobolev.GridH.val (applyLinH r L v m) x =
      L (fun n => PeriodicGridSobolev.GridH.val (v n) x) m := by
  rw [applyLinH_apply, PeriodicGridSobolev.GridH.val_sum]
  have hv : (fun n => PeriodicGridSobolev.GridH.val (v n) x) =
      ∑ n, PeriodicGridSobolev.GridH.val (v n) x • (Pi.single n 1 : ι → ℝ) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul,
    PeriodicGridSobolev.GridH.val_smul]
  exact Finset.sum_congr rfl fun n _ => mul_comm _ _

theorem norm_applyLinH_le (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    ‖applyLinH (N := N) r L‖ ≤ coefNorm L := by
  refine ContinuousLinearMap.opNorm_le_bound _ (coefNorm_nonneg L) fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by have := coefNorm_nonneg L; positivity)).mpr fun m => ?_
  rw [applyLinH_apply]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ n, ‖(L (Pi.single n 1) m) • v n‖ ≤ |L (Pi.single n 1) m| * ‖v‖ := fun n => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v n) (abs_nonneg _)
  refine (Finset.sum_le_sum fun n _ => h1 n).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact Finset.single_le_sum (f := fun m => ∑ n, |L (Pi.single n 1) m|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ m)

theorem applyLinH_comp {μ : Type*} [Fintype μ] [DecidableEq μ] (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (L' : (κ → ℝ) →ₗ[ℝ] (μ → ℝ)) (v : ι → PeriodicGridSobolev.GridH N r) :
    applyLinH r L' (applyLinH r L v) = applyLinH r (L' ∘ₗ L) v := by
  funext m
  refine PeriodicGridSobolev.GridH.ext fun x => ?_
  rw [applyLinH_val, applyLinH_val, LinearMap.comp_apply]
  have : (fun n => PeriodicGridSobolev.GridH.val (applyLinH r L v n) x) =
      L (fun n => PeriodicGridSobolev.GridH.val (v n) x) := by
    funext n; rw [applyLinH_val]
  rw [this]

theorem applyLinH_id (v : ι → PeriodicGridSobolev.GridH N r) :
    applyLinH r (LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) v = v := by
  funext m
  refine PeriodicGridSobolev.GridH.ext fun x => ?_
  rw [applyLinH_val]; rfl

/-- **A site-wise linear isomorphism** as a continuous linear equivalence of the array spaces. -/
def applyEquivH (r : ℕ) (L : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) :
    (ι → PeriodicGridSobolev.GridH N r) ≃L[ℝ] (ι → PeriodicGridSobolev.GridH N r) :=
  ContinuousLinearEquiv.equivOfInverse (applyLinH r L.toLinearMap) (applyLinH r L.symm.toLinearMap)
    (fun v => by
      rw [applyLinH_comp]
      have : (L.symm.toLinearMap ∘ₗ L.toLinearMap) = LinearMap.id := by ext; simp
      rw [this, applyLinH_id])
    (fun v => by
      rw [applyLinH_comp]
      have : (L.toLinearMap ∘ₗ L.symm.toLinearMap) = LinearMap.id := by ext; simp
      rw [this, applyLinH_id])

theorem applyEquivH_apply (L : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → PeriodicGridSobolev.GridH N r) :
    applyEquivH r L v = applyLinH r L.toLinearMap v := rfl

/-- **The inverse of a site-wise isomorphism is bounded independently of the mesh.** -/
theorem norm_applyEquivH_symm_le (L : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) :
    ‖((applyEquivH (N := N) r L).symm : (ι → PeriodicGridSobolev.GridH N r) →L[ℝ]
      (ι → PeriodicGridSobolev.GridH N r))‖ ≤
      coefNorm L.symm.toLinearMap :=
  norm_applyLinH_le _

end SiteLin

end

end RenewalGeometry.GridLocalOps
