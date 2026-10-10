/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallPoincareWirtinger

/-!
# `H¹(B)` and the weak Neumann problem on a Euclidean ball
  (stage C4, existence and uniqueness, of the ball rendering of Uhlenbeck's theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `H1B c r` (**`H¹(B)`**): the closure of the graphs `(u, ∂_1u, …, ∂_nu)` of real `C¹` functions
  in the Hilbert space `L²(B)^{1+n}` (`H1Amb`, a `PiLp 2` over `Option (Fin n)`); complete.
  `H1B_induction`: closed properties pass from graphs to `H¹(B)`.  Elements are `W^{1,2}(B)`
  functions with their weak gradients (`weak_H1B`, `memW12_of_H1B`).
* `poincare_H1B` (**Poincaré–Wirtinger on `H¹(B)`**, from `poincare_wirtinger_ball'` by
  continuity).
* `H1B0` (mean-zero elements, closed), the Dirichlet form `dirForm` (`a(x,y) = Σ_i ⟨x_i, y_i⟩`)
  and its **coercivity** `dirForm_coercive`.
* `exists_neumann_H1B0`, `neumann_H1B0_unique` (**Lax–Milgram**, Mathlib's
  `IsCoercive.continuousLinearEquivOfBilin` + Riesz).
* `neumann_weak_ball` (**the weak Neumann problem on a ball**): for `f ∈ L²(B)` with `∫_B f = 0`
  there is a mean-zero `ξ ∈ H¹(B)` with `Σ_i ∫_B ∂_iξ ∂_iφ = -∫_B f φ` for every `C¹` function
  `φ` (the weak form of `Δξ = f`, `∂_νξ = 0`; the Neumann condition is natural) and
  `‖∇ξ‖²_{L²(B)} ≤ 2^{n+1} r² ‖f‖²_{L²(B)}`; unique among mean-zero `H¹(B)` elements.

Boundary regularity (`H^{k+2}` up to the sphere for `f ∈ H^k`) is **not** proved here; see the
plan in the ledger note (rotation fields, radial equation, interior regularity).
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ} [NeZero n]

/-! ### `H¹(B)` as the closure of `C¹` graphs in `L²(B)^{1+n}` -/

section H1

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- `L²(B_r(c))` (real-valued). -/
abbrev L2B := Lp ℝ 2 (volume.restrict (euclBall c r))

/-- The ambient Hilbert space `L²(B) × L²(B)ⁿ` (`none` ↦ the function, `some i` ↦ `∂_i`). -/
abbrev H1Amb := PiLp 2 (fun _ : Option (Fin n) => L2B c r)

instance : IsFiniteMeasure (volume.restrict (euclBall c r)) :=
  isFiniteMeasure_restrict_euclBall c hr.out.le

/-- The real `C¹` functions on `ℝⁿ`, as a submodule. -/
def C1fun : Submodule ℝ ((Fin n → ℝ) → ℝ) where
  carrier := {u | ContDiff ℝ 1 u}
  add_mem' := by
    intro a b ha hb
    exact (show ContDiff ℝ 1 a from ha).add hb
  zero_mem' := by
    show ContDiff ℝ 1 (fun _ : Fin n → ℝ => (0 : ℝ))
    exact contDiff_const
  smul_mem' := by
    intro a x hx
    exact (show ContDiff ℝ 1 x from hx).const_smul a

theorem memLp_ball_of_C1 {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) :
    MemLp u 2 (volume.restrict (euclBall c r)) :=
  memLp_euclBall_of_continuous c hr.out.le hu.continuous 2

theorem memLp_ball_pd_of_C1 {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (i : Fin n) :
    MemLp (pd u i) 2 (volume.restrict (euclBall c r)) :=
  memLp_euclBall_of_continuous c hr.out.le (continuous_pd hu i) 2

/-- The graph `(u, ∂_1 u, …, ∂_n u)` of a `C¹` function, in `L²(B)^{1+n}`. -/
def graphC1 (u : C1fun (n := n)) : H1Amb c r :=
  WithLp.toLp 2 fun k => match k with
    | none => (memLp_ball_of_C1 c r u.2).toLp u
    | some i => (memLp_ball_pd_of_C1 c r u.2 i).toLp (pd u i)

theorem graphC1_none (u : C1fun (n := n)) :
    graphC1 c r u none = (memLp_ball_of_C1 c r u.2).toLp u := rfl

theorem graphC1_some (u : C1fun (n := n)) (i : Fin n) :
    graphC1 c r u (some i) = (memLp_ball_pd_of_C1 c r u.2 i).toLp (pd u i) := rfl

theorem pd_add_fun {u v : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (i : Fin n) : pd (u + v) i = pd u i + pd v i := by
  funext x
  exact pd_add_real ((hu.differentiable (by norm_num)) x) ((hv.differentiable (by norm_num)) x) i

theorem pd_smul_fun {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (a : ℝ) (i : Fin n) :
    pd (a • u) i = a • pd u i := by
  funext x
  unfold pd
  rw [show a • u = fun y => a * u y from rfl,
    ((hu.differentiable (by norm_num)) x).hasFDerivAt.const_mul a |>.fderiv]
  simp

/-- The graph map is linear. -/
def graphLin : C1fun (n := n) →ₗ[ℝ] H1Amb c r where
  toFun := graphC1 c r
  map_add' u v := by
    ext k : 1
    cases k with
    | none =>
      show (memLp_ball_of_C1 c r (u + v).2).toLp ((u + v : C1fun (n := n)) : (Fin n → ℝ) → ℝ) =
        (memLp_ball_of_C1 c r u.2).toLp (u : (Fin n → ℝ) → ℝ) +
          (memLp_ball_of_C1 c r v.2).toLp (v : (Fin n → ℝ) → ℝ)
      exact MemLp.toLp_add (memLp_ball_of_C1 c r u.2) (memLp_ball_of_C1 c r v.2)
    | some i =>
      show (memLp_ball_pd_of_C1 c r (u + v).2 i).toLp
          (pd ((u + v : C1fun (n := n)) : (Fin n → ℝ) → ℝ) i) =
        (memLp_ball_pd_of_C1 c r u.2 i).toLp (pd (u : (Fin n → ℝ) → ℝ) i) +
          (memLp_ball_pd_of_C1 c r v.2 i).toLp (pd (v : (Fin n → ℝ) → ℝ) i)
      rw [← MemLp.toLp_add (memLp_ball_pd_of_C1 c r u.2 i) (memLp_ball_pd_of_C1 c r v.2 i)]
      congr 1
      exact pd_add_fun u.2 v.2 i
  map_smul' a u := by
    ext k : 1
    cases k with
    | none =>
      show (memLp_ball_of_C1 c r (a • u).2).toLp ((a • u : C1fun (n := n)) : (Fin n → ℝ) → ℝ) =
        a • (memLp_ball_of_C1 c r u.2).toLp (u : (Fin n → ℝ) → ℝ)
      exact MemLp.toLp_const_smul a (memLp_ball_of_C1 c r u.2)
    | some i =>
      show (memLp_ball_pd_of_C1 c r (a • u).2 i).toLp
          (pd ((a • u : C1fun (n := n)) : (Fin n → ℝ) → ℝ) i) =
        a • (memLp_ball_pd_of_C1 c r u.2 i).toLp (pd (u : (Fin n → ℝ) → ℝ) i)
      rw [← MemLp.toLp_const_smul a (memLp_ball_pd_of_C1 c r u.2 i)]
      congr 1
      exact pd_smul_fun u.2 a i

/-- **`H¹(B)`**: the closure of the `C¹` graphs in `L²(B)^{1+n}` (the strong `W^{1,2}`
closure; complete). -/
def H1B : Submodule ℝ (H1Amb c r) := (LinearMap.range (graphLin c r)).topologicalClosure

instance : CompleteSpace (H1B c r) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem graphC1_mem (u : C1fun (n := n)) : graphC1 c r u ∈ H1B c r :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (graphLin c r) u)

/-- A closed property of the ambient space that holds on all `C¹` graphs holds on `H¹(B)`. -/
theorem H1B_induction {P : H1Amb c r → Prop} (hP : IsClosed {x | P x})
    (hgraph : ∀ u : C1fun (n := n), P (graphC1 c r u)) : ∀ x ∈ H1B c r, P x := by
  intro x hx
  have hsub : ((LinearMap.range (graphLin c r) : Submodule ℝ (H1Amb c r)) : Set (H1Amb c r)) ⊆
      {x | P x} := by
    rintro _ ⟨u, rfl⟩
    exact hgraph u
  have hx' : x ∈ closure ((LinearMap.range (graphLin c r) : Submodule ℝ (H1Amb c r)) :
      Set (H1Amb c r)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hx
  exact closure_minimal hsub hP hx'

/-! #### Inner products of `toLp` elements -/

theorem inner_toLp_toLp {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict (euclBall c r)))
    (hg : MemLp g 2 (volume.restrict (euclBall c r))) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x in euclBall c r, f x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem inner_toLp_left {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict (euclBall c r)))
    (g : L2B c r) : ⟪hf.toLp f, g⟫ = ∫ x in euclBall c r, f x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x h1
  rw [h1]
  simp [mul_comm]

theorem norm_sq_toLp {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict (euclBall c r))) :
    ‖hf.toLp f‖ ^ 2 = ∫ x in euclBall c r, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_toLp]
  simp [sq]

end H1


section Neumann

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- The constant function `1` in `L²(B)`. -/
def oneB : L2B c r := (memLp_const (1 : ℝ)).toLp fun _ => (1 : ℝ)

/-- `∫_B` of the function component, as a continuous linear functional on `L²(B)^{1+n}`. -/
def meanCLM : H1Amb c r →L[ℝ] ℝ :=
  (innerSL ℝ (oneB c r)).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none)

theorem meanCLM_apply (x : H1Amb c r) : meanCLM c r x = ⟪oneB c r, x none⟫ := rfl

theorem inner_oneB (g : L2B c r) : ⟪oneB c r, g⟫ = ∫ x in euclBall c r, g x := by
  rw [oneB, inner_toLp_left]; simp

theorem meanCLM_graph (u : C1fun (n := n)) :
    meanCLM c r (graphC1 c r u) = ∫ x in euclBall c r, (u : (Fin n → ℝ) → ℝ) x := by
  rw [meanCLM_apply, graphC1_none, oneB, inner_toLp_toLp]; simp

/-- The norm of the ambient space: `‖x‖² = ‖x₀‖² + Σ_i ‖x_i‖²`. -/
theorem norm_sq_H1Amb (x : H1Amb c r) :
    ‖x‖ ^ 2 = ‖x none‖ ^ 2 + ∑ i, ‖x (some i)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_option]

/-- The volume of the ball (as a real number). -/
def volB : ℝ := (volume (euclBall c r)).toReal

/-- **Poincaré–Wirtinger on `H¹(B)`**: `‖x₀ - |B|⁻¹(∫x₀)·1‖² ≤ 2^{n+1} r² Σ_i ‖x_i‖²`. -/
theorem poincare_H1B : ∀ x ∈ H1B c r,
    ‖x none - ((volB c r)⁻¹ * meanCLM c r x) • oneB c r‖ ^ 2 ≤
      2 ^ (n + 1) * r ^ 2 * ∑ i, ‖x (some i)‖ ^ 2 := by
  refine H1B_induction c r ?_ fun u => ?_
  · refine isClosed_le ?_ ?_
    · exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none).continuous.sub
        ((continuous_const.mul (meanCLM c r).continuous).smul continuous_const)).norm.pow 2
    · exact continuous_const.mul (continuous_finset_sum _ fun i _ =>
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) (some i)).continuous).norm.pow 2)
  · set k := (volB c r)⁻¹ * ∫ x in euclBall c r, (u : (Fin n → ℝ) → ℝ) x
    have hu := u.2
    have e1 : graphC1 c r u none - ((volB c r)⁻¹ * meanCLM c r (graphC1 c r u)) • oneB c r =
        ((memLp_ball_of_C1 c r hu).sub (memLp_const k)).toLp
          (fun x => (u : (Fin n → ℝ) → ℝ) x - k) := by
      rw [meanCLM_graph, graphC1_none, oneB, ← MemLp.toLp_const_smul, ← MemLp.toLp_sub]
      congr 1
      funext x; simp [k]
    rw [e1, norm_sq_toLp]
    have e2 : ∑ i, ‖graphC1 c r u (some i)‖ ^ 2 =
        ∫ x in euclBall c r, gradSqF (u : (Fin n → ℝ) → ℝ) x := by
      simp only [graphC1_some, norm_sq_toLp]
      rw [← integral_finset_sum (f := fun i x => pd (u : (Fin n → ℝ) → ℝ) i x ^ 2) _
        fun i _ => integrableOn_euclBall hr.out.le ((continuous_pd hu i).pow 2)]
      rfl
    rw [e2]
    exact poincare_wirtinger_ball' c hr.out hu

/-- **Weak derivatives on `H¹(B)`**: for every test function `φ ∈ C_c^∞(B)`,
`⟨∂_i φ, x₀⟩ = -⟨φ, x_i⟩`. -/
theorem weak_H1B {φ : (Fin n → ℝ) → ℝ} (hφ : IsTest (euclBall c r) φ) (i : Fin n) :
    ∀ x ∈ H1B c r,
      ⟪(memLp_ball_pd_of_C1 c r (hφ.smooth.of_le (by simp)) i).toLp (pd φ i), x none⟫ =
        -⟪(memLp_ball_of_C1 c r (hφ.smooth.of_le (by simp))).toLp φ, x (some i)⟫ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  refine H1B_induction c r ?_ fun u => ?_
  · exact isClosed_eq ((innerSL ℝ _).continuous.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none).continuous)
      ((innerSL ℝ _).continuous.comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) (some i)).continuous).neg
  · rw [graphC1_none, graphC1_some, inner_toLp_toLp, inner_toLp_toLp]
    have hu := u.2
    have hB := measurableSet_euclBall c r
    have e1 : ∫ x in euclBall c r, pd φ i x * (u : (Fin n → ℝ) → ℝ) x =
        ∫ x, pd φ i x * (u : (Fin n → ℝ) → ℝ) x := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.subset (tsupport_pd_subset φ i h))),
        zero_mul]
    have e2 : ∫ x in euclBall c r, φ x * pd (u : (Fin n → ℝ) → ℝ) i x =
        ∫ x, φ x * pd (u : (Fin n → ℝ) → ℝ) i x := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.subset h)), zero_mul]
    rw [e1, e2]
    exact integral_pd_mul_eq_neg_real hu hφ.smooth hφ.compact i

/-! #### The mean-zero subspace and the Dirichlet form -/

/-- Mean-zero elements of `H¹(B)`. -/
def H1B0 : Submodule ℝ (H1Amb c r) := H1B c r ⊓ LinearMap.ker (meanCLM c r : H1Amb c r →ₗ[ℝ] ℝ)

theorem isClosed_H1B0 : IsClosed (H1B0 c r : Set (H1Amb c r)) :=
  (Submodule.isClosed_topologicalClosure _).inter (ContinuousLinearMap.isClosed_ker (meanCLM c r))

instance : CompleteSpace (H1B0 c r) := (isClosed_H1B0 c r).completeSpace_coe

/-- The `i`-th gradient component on `H¹₀(B)`. -/
def gradComp (i : Fin n) : H1B0 c r →L[ℝ] L2B c r :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) (some i)).comp (H1B0 c r).subtypeL

/-- The Dirichlet form `a(x, y) = Σ_i ⟨x_i, y_i⟩`. -/
def dirForm : H1B0 c r →L[ℝ] H1B0 c r →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (E := L2B c r)).bilinearComp (gradComp c r i) (gradComp c r i)

theorem dirForm_apply (x y : H1B0 c r) :
    dirForm c r x y = ∑ i, ⟪(x : H1Amb c r) (some i), (y : H1Amb c r) (some i)⟫ := by
  simp [dirForm, gradComp, ContinuousLinearMap.sum_apply]

theorem volB_pos : 0 < volB c r := by
  refine ENNReal.toReal_pos ?_ (volume_euclBall_lt_top c hr.out.le).ne
  have hc : c ∈ euclBall c r := by
    show sqDist c c < r ^ 2; simp [sqDist]; exact pow_pos hr.out 2
  exact ((isOpen_euclBall c r).measure_pos volume ⟨c, hc⟩).ne'

/-- **Coercivity of the Dirichlet form on mean-zero `H¹(B)`** (Poincaré–Wirtinger). -/
theorem dirForm_coercive : IsCoercive (dirForm c r) := by
  set K : ℝ := 2 ^ (n + 1) * r ^ 2
  have hK : 0 ≤ K := by positivity
  refine ⟨(1 + K)⁻¹, by positivity, fun x => ?_⟩
  have hx0 : meanCLM c r (x : H1Amb c r) = 0 := x.2.2
  have hPW := poincare_H1B c r (x : H1Amb c r) x.2.1
  rw [hx0, mul_zero, zero_smul, sub_zero] at hPW
  have hnorm : ‖x‖ ^ 2 = ‖(x : H1Amb c r) none‖ ^ 2 + ∑ i, ‖(x : H1Amb c r) (some i)‖ ^ 2 := by
    rw [← norm_sq_H1Amb]; rfl
  have happ : dirForm c r x x = ∑ i, ‖(x : H1Amb c r) (some i)‖ ^ 2 := by
    rw [dirForm_apply]
    exact Finset.sum_congr rfl fun i _ => real_inner_self_eq_norm_sq _
  rw [happ]
  have h1 : ‖x‖ * ‖x‖ ≤ (1 + K) * ∑ i, ‖(x : H1Amb c r) (some i)‖ ^ 2 := by
    rw [← sq, hnorm]; linarith
  calc (1 + K)⁻¹ * ‖x‖ * ‖x‖ = (1 + K)⁻¹ * (‖x‖ * ‖x‖) := by ring
    _ ≤ (1 + K)⁻¹ * ((1 + K) * ∑ i, ‖(x : H1Amb c r) (some i)‖ ^ 2) := by gcongr
    _ = _ := by field_simp

end Neumann


section Solve

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- The graph of the constant function `1` is `(1, 0, …, 0)`. -/
theorem graphC1_one :
    graphC1 c r ⟨fun _ => (1 : ℝ), (contDiff_const : ContDiff ℝ 1 fun _ : Fin n → ℝ => (1 : ℝ))⟩ =
      WithLp.toLp 2 fun k => match k with
        | none => oneB c r
        | some _ => 0 := by
  ext k : 1
  cases k with
  | none => rfl
  | some i =>
    show (memLp_ball_pd_of_C1 c r (contDiff_const : ContDiff ℝ 1 fun _ : Fin n → ℝ => (1 : ℝ))
      i).toLp (pd (fun _ : Fin n → ℝ => (1 : ℝ)) i) = 0
    have : pd (fun _ : Fin n → ℝ => (1 : ℝ)) i = fun _ => 0 := by funext x; simp [pd]
    simp only [this]
    exact MemLp.toLp_zero _

/-- The element `(1, 0, …, 0)` of `H¹(B)`. -/
def oneH : H1Amb c r := WithLp.toLp 2 fun k => match k with
  | none => oneB c r
  | some _ => 0

theorem oneH_mem : oneH c r ∈ H1B c r := by
  rw [oneH, ← graphC1_one]; exact graphC1_mem c r _

theorem meanCLM_oneH : meanCLM c r (oneH c r) = volB c r := by
  rw [meanCLM_apply, inner_oneB]
  show ∫ x in euclBall c r, (oneB c r : (Fin n → ℝ) → ℝ) x = volB c r
  rw [← inner_oneB, oneB, inner_toLp_toLp]
  simp [volB, measureReal_def]

/-- The load functional `y ↦ -⟨f, y₀⟩`. -/
def loadCLM (F : L2B c r) : H1B0 c r →L[ℝ] ℝ :=
  -((innerSL ℝ F).comp ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none).comp
    (H1B0 c r).subtypeL))

/-- **Lax–Milgram for the Neumann problem on a ball** (abstract form): for every `F ∈ L²(B)` there
is a unique mean-zero `ξ ∈ H¹(B)` with `Σ_i ⟨ξ_i, y_i⟩ = -⟨F, y₀⟩` for all mean-zero `y ∈ H¹(B)`. -/
theorem exists_neumann_H1B0 (F : L2B c r) :
    ∃ ξ : H1B0 c r, ∀ y : H1B0 c r, dirForm c r ξ y = loadCLM c r F y := by
  have coer := dirForm_coercive c r
  refine ⟨coer.continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual ℝ (H1B0 c r)).symm (loadCLM c r F)), fun y => ?_⟩
  rw [← IsCoercive.continuousLinearEquivOfBilin_apply coer, ContinuousLinearEquiv.apply_symm_apply,
    InnerProductSpace.toDual_symm_apply]

theorem neumann_H1B0_unique {F : L2B c r} {ξ ξ' : H1B0 c r}
    (h : ∀ y : H1B0 c r, dirForm c r ξ y = loadCLM c r F y)
    (h' : ∀ y : H1B0 c r, dirForm c r ξ' y = loadCLM c r F y) : ξ = ξ' := by
  obtain ⟨C, hC, hcoer⟩ := dirForm_coercive c r
  have h0 : dirForm c r (ξ - ξ') (ξ - ξ') = 0 := by
    rw [map_sub (dirForm c r) ξ ξ', ContinuousLinearMap.sub_apply, h, h', sub_self]
  have := hcoer (ξ - ξ')
  rw [h0] at this
  have hn : ‖ξ - ξ'‖ = 0 := by
    by_contra hne
    have : 0 < C * ‖ξ - ξ'‖ * ‖ξ - ξ'‖ := by positivity
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- **The weak Neumann problem on a ball** (`Δξ = f` in `B_r(c)`, `∂_νξ = 0` on the sphere, weak
form): for `f ∈ L²(B)` with `∫_B f = 0` there is `ξ ∈ H¹(B)` (closure of `C¹` graphs, so
`ξ₀ ∈ L²(B)` with weak gradient `ξ_i ∈ L²(B)`, `weak_H1B`), of mean zero, with
`Σ_i ∫_B ξ_i ∂_i φ = -∫_B f φ` for **every** `C¹` function `φ` (no boundary condition on `φ`:
the Neumann condition is natural), and the energy bound
`Σ_i ‖ξ_i‖²_{L²(B)} ≤ 2^{n+1} r² ‖f‖²_{L²(B)}`.  The solution is unique among mean-zero
elements of `H¹(B)` (`neumann_H1B0_unique`). -/
theorem neumann_weak_ball {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict (euclBall c r)))
    (hf0 : ∫ x in euclBall c r, f x = 0) :
    ∃ x ∈ H1B c r, meanCLM c r x = 0 ∧
      (∀ φ : (Fin n → ℝ) → ℝ, ∀ hφ : ContDiff ℝ 1 φ,
        ∑ i, ∫ y in euclBall c r, (x (some i) : (Fin n → ℝ) → ℝ) y * pd φ i y =
          -∫ y in euclBall c r, f y * φ y) ∧
      ∑ i, ‖x (some i)‖ ^ 2 ≤ 2 ^ (n + 1) * r ^ 2 * ‖hf.toLp f‖ ^ 2 := by
  obtain ⟨ξ, hξ⟩ := exists_neumann_H1B0 c r (hf.toLp f)
  have hF1 : ⟪hf.toLp f, oneB c r⟫ = 0 := by
    rw [real_inner_comm, inner_oneB]
    rw [← hf0]
    exact integral_congr_ae (hf.coeFn_toLp.mono fun x hx => hx)
  -- the identity holds for all `y ∈ H¹(B)`
  have hall : ∀ y ∈ H1B c r, ∑ i, ⟪(ξ : H1Amb c r) (some i), y (some i)⟫ =
      -⟪hf.toLp f, y none⟫ := by
    intro y hy
    set t := (volB c r)⁻¹ * meanCLM c r y
    have hy0 : y - t • oneH c r ∈ H1B0 c r := by
      refine ⟨(H1B c r).sub_mem hy ((H1B c r).smul_mem t (oneH_mem c r)), ?_⟩
      show meanCLM c r (y - t • oneH c r) = 0
      rw [map_sub, map_smul, meanCLM_oneH, smul_eq_mul, mul_comm t, show t = (volB c r)⁻¹ *
        meanCLM c r y from rfl, ← mul_assoc, mul_inv_cancel₀ (volB_pos c r).ne', one_mul, sub_self]
    have := hξ ⟨_, hy0⟩
    rw [dirForm_apply] at this
    simp only [loadCLM, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, Submodule.subtypeL_apply, PiLp.proj_apply] at this
    have e1 : ∀ i, (y - t • oneH c r) (some i) = y (some i) := fun i => by
      simp [oneH]
    have e2 : (y - t • oneH c r) none = y none - t • oneB c r := by
      simp [oneH]
    simp only [e1, e2, inner_sub_right, inner_smul_right, hF1, mul_zero, sub_zero] at this
    exact this
  refine ⟨(ξ : H1Amb c r), ξ.2.1, ξ.2.2, fun φ hφ => ?_, ?_⟩
  · have := hall _ (graphC1_mem c r ⟨φ, show φ ∈ C1fun from hφ⟩)
    simp only [graphC1_some, graphC1_none] at this
    rw [inner_toLp_toLp] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, inner_toLp_left]
    exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  · -- energy estimate
    obtain hcoer := dirForm_coercive c r
    have hE : dirForm c r ξ ξ = -⟪hf.toLp f, (ξ : H1Amb c r) none⟫ := by
      rw [hξ ξ]; simp [loadCLM]
    have hEn : dirForm c r ξ ξ = ∑ i, ‖(ξ : H1Amb c r) (some i)‖ ^ 2 := by
      rw [dirForm_apply]
      exact Finset.sum_congr rfl fun i _ => real_inner_self_eq_norm_sq _
    have hPW := poincare_H1B c r (ξ : H1Amb c r) ξ.2.1
    rw [show meanCLM c r (ξ : H1Amb c r) = 0 from ξ.2.2, mul_zero, zero_smul, sub_zero] at hPW
    set S := ∑ i, ‖(ξ : H1Amb c r) (some i)‖ ^ 2
    set K : ℝ := 2 ^ (n + 1) * r ^ 2
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hK0 : 0 ≤ K := by positivity
    have h1 : S ≤ ‖hf.toLp f‖ * ‖(ξ : H1Amb c r) none‖ := by
      rw [← hEn, hE]
      exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
    -- `S² ≤ ‖hf.toLp f‖² ‖ξ₀‖² ≤ ‖hf.toLp f‖² K S`
    have h2 : S ^ 2 ≤ ‖hf.toLp f‖ ^ 2 * (K * S) := by
      calc S ^ 2 ≤ (‖hf.toLp f‖ * ‖(ξ : H1Amb c r) none‖) ^ 2 := pow_le_pow_left₀ hS0 h1 2
        _ = ‖hf.toLp f‖ ^ 2 * ‖(ξ : H1Amb c r) none‖ ^ 2 := by ring
        _ ≤ ‖hf.toLp f‖ ^ 2 * (K * S) := by gcongr
    rcases eq_or_lt_of_le hS0 with h | h
    · rw [← h]; positivity
    · have : S ≤ ‖hf.toLp f‖ ^ 2 * K := by
        have h3 : S * S ≤ (‖hf.toLp f‖ ^ 2 * K) * S := by nlinarith
        exact le_of_mul_le_mul_right h3 h
      linarith

end Solve


section W12

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- Elements of `H¹(B)` are `W^{1,2}(B)` functions in the library's sense (complexified). -/
theorem memW12_of_H1B {x : H1Amb c r} (hx : x ∈ H1B c r) :
    MemW12 (euclBall c r) (fun y => (((x none : L2B c r) : (Fin n → ℝ) → ℝ) y : ℂ))
      (fun i y => (((x (some i) : L2B c r) : (Fin n → ℝ) → ℝ) y : ℂ)) := by
  refine ⟨(Lp.memLp _).ofReal, fun i => (Lp.memLp _).ofReal, fun i φ hφ => ?_⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have hw := weak_H1B c r hφ i x hx
  rw [inner_toLp_left, inner_toLp_left] at hw
  have e1 : ∫ y, pd φ i y * ((x none : L2B c r) : (Fin n → ℝ) → ℝ) y =
      ∫ y in euclBall c r, pd φ i y * ((x none : L2B c r) : (Fin n → ℝ) → ℝ) y := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφ.subset (tsupport_pd_subset φ i h))),
      zero_mul]
  have e2 : ∫ y, φ y * ((x (some i) : L2B c r) : (Fin n → ℝ) → ℝ) y =
      ∫ y in euclBall c r, φ y * ((x (some i) : L2B c r) : (Fin n → ℝ) → ℝ) y := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφ.subset h)), zero_mul]
  have c1 : (fun y => ((pd φ i y : ℝ) : ℂ) * (((x none : L2B c r) : (Fin n → ℝ) → ℝ) y : ℂ)) =
      fun y => (((pd φ i y * ((x none : L2B c r) : (Fin n → ℝ) → ℝ) y) : ℝ) : ℂ) := by
    funext y; push_cast; ring
  have c2 : (fun y => ((φ y : ℝ) : ℂ) * (((x (some i) : L2B c r) : (Fin n → ℝ) → ℝ) y : ℂ)) =
      fun y => (((φ y * ((x (some i) : L2B c r) : (Fin n → ℝ) → ℝ) y) : ℝ) : ℂ) := by
    funext y; push_cast; ring
  rw [c1, c2, integral_complex_ofReal, integral_complex_ofReal, e1, e2, hw]
  push_cast; ring

end W12


/-- Non-vacuity: the hypotheses of `neumann_weak_ball` are satisfied by `f = 0`. -/
example (c : Fin 4 → ℝ) : ∃ x ∈ H1B (r := 1) c, meanCLM (r := 1) c x = 0 := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  obtain ⟨x, hx, h0, -⟩ := neumann_weak_ball (r := 1) c (f := fun _ => 0)
    (memLp_const 0) (by simp)
  exact ⟨x, hx, h0⟩

end RenewalGeometry.BallAnalysis
