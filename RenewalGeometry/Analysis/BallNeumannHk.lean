/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallRadialDecomposition
import RenewalGeometry.Analysis.BallSobolevHk

/-!
# The `H²` estimate for the Neumann problem on a ball (closed graph theorem)
  (stage C4b, step 4, of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `weakR_iff_inner`, `isClosed_weakR`, `weakR_unique` — real weak partial derivatives on the ball
  for `L²(B)` elements, as a closed linear condition with unique solutions;
* `gradCLM c r j : L²(B) →L L²(B)`, `F ↦ ∂_j(solCLM F)`;
* `hessOp c r j k` — the linear map `F ↦ ∂_k∂_j(solCLM F)` (well defined by `neumann_H2_ball` and
  uniqueness), `hessCLM` — **continuous by the closed graph theorem**;
* `neumann_H2_bound` (**the `H²` estimate**): there is `C = C(n, r)` with
  `‖∂_k∂_j ξ‖_{L²(B)} ≤ C ‖F‖_{L²(B)}` for `ξ = solCLM F`, for all `j, k`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ} [NeZero n]

section WeakL2

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- Real weak derivatives of `L²(B)` elements, in inner-product form. -/
theorem weakR_iff_inner (k : Fin n) (U G : L2B c r) :
    HasWeakPartialR (euclBall c r) k (U : (Fin n → ℝ) → ℝ) (G : (Fin n → ℝ) → ℝ) ↔
      ∀ φ (hφ : IsTest (euclBall c r) φ),
        ⟪(memLp_ball_pd_of_C1 c r (hφ.smooth.of_le (by simp)) k).toLp (pd φ k), U⟫ =
          -⟪(memLp_ball_of_C1 c r (hφ.smooth.of_le (by simp))).toLp φ, G⟫ := by
  have e : ∀ φ (hφ : IsTest (euclBall c r) φ),
      ⟪(memLp_ball_pd_of_C1 c r (hφ.smooth.of_le (by simp)) k).toLp (pd φ k), U⟫ =
        ∫ x, pd φ k x * U x ∧
      ⟪(memLp_ball_of_C1 c r (hφ.smooth.of_le (by simp))).toLp φ, G⟫ = ∫ x, φ x * G x := by
    intro φ hφ
    rw [inner_toLp_left, inner_toLp_left, integral_test_eq_setIntegral c r (isTest_pd hφ k),
      integral_test_eq_setIntegral c r hφ]
    exact ⟨rfl, rfl⟩
  constructor
  · intro h φ hφ; rw [(e φ hφ).1, (e φ hφ).2]; exact h φ hφ
  · intro h φ hφ; rw [← (e φ hφ).1, ← (e φ hφ).2]; exact h φ hφ

/-- Weak derivatives are a closed condition in `L²(B) × L²(B)`. -/
theorem isClosed_weakR (k : Fin n) :
    IsClosed {p : L2B c r × L2B c r |
      HasWeakPartialR (euclBall c r) k (p.1 : (Fin n → ℝ) → ℝ) (p.2 : (Fin n → ℝ) → ℝ)} := by
  simp only [weakR_iff_inner]
  simp only [setOf_forall]
  refine isClosed_iInter fun φ => isClosed_iInter fun hφ => ?_
  exact isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd).neg

/-- Uniqueness of weak derivatives as elements of `L²(B)`. -/
theorem weakR_unique (k : Fin n) {U G G' : L2B c r}
    (h : HasWeakPartialR (euclBall c r) k (U : (Fin n → ℝ) → ℝ) (G : (Fin n → ℝ) → ℝ))
    (h' : HasWeakPartialR (euclBall c r) k (U : (Fin n → ℝ) → ℝ) (G' : (Fin n → ℝ) → ℝ)) :
    G = G' := by
  have := h.ae_eq (isOpen_euclBall c r) h' (Lp.memLp G) (Lp.memLp G')
  refine Lp.ext ?_
  rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]
  exact this

/-- Weak derivatives only depend on the `L²(B)` classes. -/
theorem HasWeakPartialR.congr_ae {k : Fin n} {u u' g g' : (Fin n → ℝ) → ℝ}
    (h : HasWeakPartialR (euclBall c r) k u g)
    (hu : u =ᵐ[volume.restrict (euclBall c r)] u') (hg : g =ᵐ[volume.restrict (euclBall c r)] g') :
    HasWeakPartialR (euclBall c r) k u' g' := by
  intro φ hφ
  rw [integral_test_eq_setIntegral c r (isTest_pd hφ k), integral_test_eq_setIntegral c r hφ]
  have h1 := h φ hφ
  rw [integral_test_eq_setIntegral c r (isTest_pd hφ k), integral_test_eq_setIntegral c r hφ] at h1
  have e1 : ∫ x in euclBall c r, pd φ k x * u x = ∫ x in euclBall c r, pd φ k x * u' x :=
    integral_congr_ae (hu.mono fun x hx => by simp only [hx])
  have e2 : ∫ x in euclBall c r, φ x * g x = ∫ x in euclBall c r, φ x * g' x :=
    integral_congr_ae (hg.mono fun x hx => by simp only [hx])
  rw [← e1, ← e2]
  exact h1

/-- Sums of weak derivatives (for `L²(B)` elements). -/
theorem HasWeakPartialR.add_L2B {k : Fin n} {U V G H : L2B c r}
    (h1 : HasWeakPartialR (euclBall c r) k (U : (Fin n → ℝ) → ℝ) (G : (Fin n → ℝ) → ℝ))
    (h2 : HasWeakPartialR (euclBall c r) k (V : (Fin n → ℝ) → ℝ) (H : (Fin n → ℝ) → ℝ)) :
    HasWeakPartialR (euclBall c r) k ((U + V : L2B c r) : (Fin n → ℝ) → ℝ)
      ((G + H : L2B c r) : (Fin n → ℝ) → ℝ) := by
  rw [weakR_iff_inner] at h1 h2 ⊢
  intro φ hφ
  rw [inner_add_right, inner_add_right, h1 φ hφ, h2 φ hφ]; ring

theorem HasWeakPartialR.smul_L2B {k : Fin n} {U G : L2B c r} (a : ℝ)
    (h1 : HasWeakPartialR (euclBall c r) k (U : (Fin n → ℝ) → ℝ) (G : (Fin n → ℝ) → ℝ)) :
    HasWeakPartialR (euclBall c r) k ((a • U : L2B c r) : (Fin n → ℝ) → ℝ)
      ((a • G : L2B c r) : (Fin n → ℝ) → ℝ) := by
  rw [weakR_iff_inner] at h1 ⊢
  intro φ hφ
  rw [inner_smul_right, inner_smul_right, h1 φ hφ]; ring

end WeakL2

section H2Op

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- `F ↦ ∂_j(solCLM F)` as a continuous linear map of `L²(B)`. -/
def gradCLM (j : Fin n) : L2B c r →L[ℝ] L2B c r :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) (some j)).comp
    ((H1B0 c r).subtypeL.comp (solCLM c r))

theorem gradCLM_apply (j : Fin n) (F : L2B c r) :
    gradCLM c r j F = ((solCLM c r F : H1B0 c r) : H1Amb c r) (some j) := rfl

/-- The second derivative `∂_k∂_j(solCLM F)` as an element of `L²(B)` (chosen; unique). -/
def hessFn (F : L2B c r) (j k : Fin n) : L2B c r :=
  (neumann_H2_ball c r F j k).choose_spec.1.toLp _

theorem hessFn_weak (F : L2B c r) (j k : Fin n) :
    HasWeakPartialR (euclBall c r) k (gradCLM c r j F : (Fin n → ℝ) → ℝ)
      (hessFn c r F j k : (Fin n → ℝ) → ℝ) :=
  (neumann_H2_ball c r F j k).choose_spec.2.congr_ae c r (Filter.EventuallyEq.refl _ _)
    (neumann_H2_ball c r F j k).choose_spec.1.coeFn_toLp.symm

/-- `hessFn` is characterized by the weak-derivative property. -/
theorem hessFn_eq {F : L2B c r} {j k : Fin n} {Y : L2B c r}
    (h : HasWeakPartialR (euclBall c r) k (gradCLM c r j F : (Fin n → ℝ) → ℝ)
      (Y : (Fin n → ℝ) → ℝ)) : hessFn c r F j k = Y :=
  weakR_unique c r k (hessFn_weak c r F j k) h

/-- The Hessian operator of the Neumann problem, as a linear map. -/
def hessOp (j k : Fin n) : L2B c r →ₗ[ℝ] L2B c r where
  toFun F := hessFn c r F j k
  map_add' F G := by
    refine hessFn_eq c r ?_
    rw [map_add]
    exact (hessFn_weak c r F j k).add_L2B c r (hessFn_weak c r G j k)
  map_smul' a F := by
    refine hessFn_eq c r ?_
    rw [map_smul]
    exact (hessFn_weak c r F j k).smul_L2B c r a

/-- **The Hessian operator is bounded** (closed graph theorem). -/
theorem continuous_hessOp (j k : Fin n) : Continuous (hessOp c r j k) := by
  refine (hessOp c r j k).continuous_of_seq_closed_graph fun u x y hu hy => ?_
  have hg : Tendsto (fun m => gradCLM c r j (u m)) atTop (𝓝 (gradCLM c r j x)) :=
    ((gradCLM c r j).continuous.tendsto x).comp hu
  have hpair : Tendsto (fun m => (gradCLM c r j (u m), hessOp c r j k (u m))) atTop
      (𝓝 (gradCLM c r j x, y)) := hg.prodMk_nhds hy
  have hmem := (isClosed_weakR c r k).mem_of_tendsto hpair
    (Eventually.of_forall fun m => hessFn_weak c r (u m) j k)
  exact (hessFn_eq c r hmem).symm

/-- The Hessian operator as a continuous linear map. -/
def hessCLM (j k : Fin n) : L2B c r →L[ℝ] L2B c r :=
  ⟨hessOp c r j k, continuous_hessOp c r j k⟩

theorem hessCLM_weak (F : L2B c r) (j k : Fin n) :
    HasWeakPartialR (euclBall c r) k (gradCLM c r j F : (Fin n → ℝ) → ℝ)
      (hessCLM c r j k F : (Fin n → ℝ) → ℝ) := hessFn_weak c r F j k

/-- **The `H²` estimate for the weak Neumann problem on a ball**: there is `C` such that for all
`F ∈ L²(B)`, the second weak derivatives of `ξ = solCLM F` satisfy
`‖∂_k∂_j ξ‖_{L²(B)} ≤ C ‖F‖_{L²(B)}` (and `∂_k∂_j ξ` exists on the whole ball,
`neumann_H2_ball`). -/
theorem neumann_H2_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : L2B c r) (j k : Fin n) (Y : L2B c r),
    HasWeakPartialR (euclBall c r) k (gradCLM c r j F : (Fin n → ℝ) → ℝ)
      (Y : (Fin n → ℝ) → ℝ) → ‖Y‖ ≤ C * ‖F‖ := by
  refine ⟨∑ j, ∑ k, ‖hessCLM c r j k‖, by positivity, fun F j k Y hY => ?_⟩
  rw [← hessFn_eq c r hY]
  calc ‖hessFn c r F j k‖ = ‖hessCLM c r j k F‖ := rfl
    _ ≤ ‖hessCLM c r j k‖ * ‖F‖ := (hessCLM c r j k).le_opNorm F
    _ ≤ (∑ j, ∑ k, ‖hessCLM c r j k‖) * ‖F‖ := by
        gcongr
        exact (Finset.single_le_sum (f := fun k => ‖hessCLM c r j k‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ k)).trans (Finset.single_le_sum (f := fun j => ∑ k, ‖hessCLM c r j k‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j))

end H2Op

/-! ### Higher regularity: interior, gluing, the radial factor -/

section HigherBall

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

theorem isBounded_euclBall' (ρ : ℝ) : Bornology.IsBounded (euclBall c ρ) := by
  refine (isBounded_closedBall (x := c) (r := |ρ|)).subset fun x hx => ?_
  exact mem_closedBall_of_sqDist_le (abs_nonneg ρ) (by rw [sq_abs]; exact le_of_lt hx)

theorem isBounded_annB : Bornology.IsBounded (annB c r) :=
  (isBounded_euclBall' c r).subset (annB_subset c r)

/-- **Interior `H^{k+2}` regularity of the Neumann solution** on `B_{r/2}(c)`. -/
theorem neumann_interior_Hk (k : ℕ) (F : L2B c r)
    (hF : MemHk (euclBall c r) k (solRhs c r F))
    (hξ : MemHk (euclBall c r) (k + 1) (solFn c r F)) :
    MemHk (euclBall c (r / 2)) (k + 2) (solFn c r F) := by
  have hr0 := hr.out
  set B := euclBall c r
  obtain ⟨χ, hχ, U, -, hKU, hU⟩ := exists_cutoff_ball c (ρ := r / 2) (R := r) (by positivity)
    (by linarith)
  have hχV : ∀ x ∈ euclBall c (r / 2), χ x = 1 := fun x hx =>
    hU x (hKU (show sqDist c x ≤ (r / 2) ^ 2 from le_of_lt hx))
  set ξ := solFn c r F
  set g := solGrad c r F
  have hg : ∀ j, MemHk B k (g j) := fun j =>
    hξ.deriv (isOpen_euclBall c r) (solGrad_weak c r F j) (memLp_solGrad c r F j)
  have hwk : ∀ j, HasWeakPartialR univ j (fun x => χ x * ξ x)
      (fun x => χ x * g j x + pd χ j x * ξ x) := fun j =>
    (solGrad_weak c r F j).mul_test (memLp_solFn c r F) (memLp_solGrad c r F j) hχ
  have hgw : ∀ j, MemHk univ k (fun x => χ x * g j x + pd χ j x * ξ x) := fun j =>
    ((hg j).mul_test_univ (isOpen_euclBall c r) hχ).add
      ((hξ.mono (Nat.le_succ k)).mul_test_univ (isOpen_euclBall c r) (isTest_pd hχ j))
  have hFw : MemHk univ k (fun x => χ x * solRhs c r F x + 2 * ∑ j, pd χ j x * g j x +
      ∑ j, pd (pd χ j) j x * ξ x) := by
    refine ((hF.mul_test_univ (isOpen_euclBall c r) hχ).add ?_).add ?_
    · exact (MemHk.sum' _ fun j _ =>
        (hg j).mul_test_univ (isOpen_euclBall c r) (isTest_pd hχ j)).const_mul 2
    · exact MemHk.sum' _ fun j _ => (hξ.mono (Nat.le_succ k)).mul_test_univ
        (isOpen_euclBall c r) (isTest_pd (isTest_pd hχ j) j)
  have hΔ := weak_laplacian_cutoff (memLp_solFn c r F) (memLp_solGrad c r F)
    (memLp_solRhs c r F) (solGrad_weak c r F) (fun φ hφ => solCLM_weak_test c r F hφ) hχ
  have hw := whole_space_Hk k hχ.compact.mul_right (hξ.mul_test_univ (isOpen_euclBall c r) hχ)
    hwk hgw hFw hΔ
  refine (hw.restrict (subset_univ _)).congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c (r / 2))]
  exact Eventually.of_forall fun x hx => by simp [hχV x hx]

/-- The glued function `V.piecewise gV gA` is square integrable on the ball. -/
theorem memLp_glue {gV gA : (Fin n → ℝ) → ℝ}
    (hgV : MemLp gV 2 (volume.restrict (euclBall c (r / 2))))
    (hgA : MemLp gA 2 (volume.restrict (annB c r))) :
    MemLp ((euclBall c (r / 2)).piecewise gV gA) 2 (volume.restrict (euclBall c r)) := by
  have hr0 := hr.out
  have hVcB : (euclBall c (r / 2))ᶜ ∩ euclBall c r ⊆ annB c r := fun x hx => ⟨hx.2, by
    have : ¬ sqDist c x < (r / 2) ^ 2 := hx.1
    push_neg at this; nlinarith⟩
  refine MemLp.piecewise (measurableSet_euclBall c (r / 2)) ?_ ?_
  · rw [Measure.restrict_restrict (measurableSet_euclBall c (r / 2))]
    exact hgV.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  · rw [Measure.restrict_restrict (measurableSet_euclBall c (r / 2)).compl]
    exact hgA.mono_measure (Measure.restrict_mono hVcB le_rfl)

/-- **Gluing weak derivatives** from `B_{r/2}(c)` and the annulus `r/4 < |x - c| < r`. -/
theorem weak_glue_ball {u gV gA : (Fin n → ℝ) → ℝ} {i : Fin n}
    (huB : MemLp u 2 (volume.restrict (euclBall c r)))
    (hV : HasWeakPartialR (euclBall c (r / 2)) i u gV)
    (hA : HasWeakPartialR (annB c r) i u gA)
    (hgV : MemLp gV 2 (volume.restrict (euclBall c (r / 2))))
    (hgA : MemLp gA 2 (volume.restrict (annB c r))) :
    HasWeakPartialR (euclBall c r) i u ((euclBall c (r / 2)).piecewise gV gA) := by
  have hr0 := hr.out
  set V := euclBall c (r / 2)
  set A := annB c r
  set H := V.piecewise gV gA
  have hVB : V ⊆ euclBall c r := fun x (hx : sqDist c x < (r / 2) ^ 2) => by
    show sqDist c x < r ^ 2; nlinarith
  have hHL : MemLp H 2 (volume.restrict (euclBall c r)) := memLp_glue c r hgV hgA
  intro φ hφ
  obtain ⟨χ0, hχ0, U, hUo, hKU, hU⟩ := exists_cutoff_ball c (ρ := r / 3) (R := r / 2)
    (by positivity) (by linarith)
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  set φ1 : (Fin n → ℝ) → ℝ := fun x => χ0 x * φ x
  set φ2 : (Fin n → ℝ) → ℝ := fun x => (1 - χ0 x) * φ x
  have hT1 : IsTest V φ1 := hχ0.mul_smooth hφ.smooth
  have hT2 : IsTest A φ2 := by
    refine ⟨(contDiff_const.sub hχ0.smooth).mul hφ.smooth, hφ.compact.mul_left, ?_⟩
    intro x hx
    have hx1 : x ∈ tsupport φ := tsupport_mul_subset_right hx
    have hx2 : x ∈ tsupport (fun x => 1 - χ0 x) := tsupport_mul_subset_left hx
    have hx3 : x ∈ Uᶜ := by
      refine closure_minimal (fun y hy => ?_) hUo.isClosed_compl hx2
      intro hyU; apply hy; simp [hU y hyU]
    refine ⟨hφ.subset hx1, ?_⟩
    by_contra hle
    push_neg at hle
    exact hx3 (hKU (le_trans hle (by nlinarith)))
  have hsplit : ∀ x, pd φ i x = pd φ1 i x + pd φ2 i x := by
    intro x
    have e : φ = fun x => φ1 x + φ2 x := by funext y; simp only [φ1, φ2]; ring
    have h1 : ContDiff ℝ 1 φ1 := hT1.smooth.of_le (by simp)
    have h2 : ContDiff ℝ 1 φ2 := hT2.smooth.of_le (by simp)
    rw [e]
    exact pd_add_real (h1.differentiable one_ne_zero x) (h2.differentiable one_ne_zero x) i
  have i1 : Integrable fun x => pd φ1 i x * u x :=
    integrable_mul_of_memLp_restrict (isTest_pd (hT1.mono hVB) i).continuous
      (isTest_pd (hT1.mono hVB) i).compact (isTest_pd (hT1.mono hVB) i).subset huB
  have i2 : Integrable fun x => pd φ2 i x * u x :=
    integrable_mul_of_memLp_restrict (isTest_pd (hT2.mono (annB_subset c r)) i).continuous
      (isTest_pd (hT2.mono (annB_subset c r)) i).compact
      (isTest_pd (hT2.mono (annB_subset c r)) i).subset huB
  have e1 : ∫ x, pd φ i x * u x = (∫ x, pd φ1 i x * u x) + ∫ x, pd φ2 i x * u x := by
    rw [← integral_add i1 i2]; congr 1; funext x; rw [hsplit]; ring
  rw [e1, hV φ1 hT1, hA φ2 hT2]
  have hEq1 : ∫ x, φ1 x * gV x = ∫ x, φ1 x * H x := by
    congr 1; funext x
    by_cases hx : x ∈ V
    · simp [H, hx]
    · rw [isTest_vanish hT1 x hx, zero_mul, zero_mul]
  have huniq : ∀ᵐ x, x ∈ A ∩ V → gV x = gA x := by
    have hAV : IsOpen (A ∩ V) := (isOpen_annB c r).inter (isOpen_euclBall c (r / 2))
    exact weakR_ae_eq hAV (hV.mono_set inter_subset_right) (hA.mono_set inter_subset_left)
      (hgV.mono_measure (Measure.restrict_mono inter_subset_right le_rfl))
      (hgA.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
  have hEq2 : ∫ x, φ2 x * gA x = ∫ x, φ2 x * H x := by
    refine integral_congr_ae ?_
    filter_upwards [huniq] with x hx
    by_cases hxV : x ∈ V
    · by_cases h0 : φ2 x = 0
      · rw [h0, zero_mul, zero_mul]
      · have hxA : x ∈ A := hT2.subset (subset_tsupport φ2 h0)
        simp [H, hxV, hx ⟨hxA, hxV⟩]
    · simp [H, hxV]
  have i3 : Integrable fun x => φ1 x * H x :=
    integrable_mul_of_memLp_restrict (hT1.mono hVB).continuous (hT1.mono hVB).compact
      (hT1.mono hVB).subset hHL
  have i4 : Integrable fun x => φ2 x * H x :=
    integrable_mul_of_memLp_restrict (hT2.mono (annB_subset c r)).continuous
      (hT2.mono (annB_subset c r)).compact (hT2.mono (annB_subset c r)).subset hHL
  rw [hEq1, hEq2, ← neg_add, ← integral_add i3 i4]
  congr 2; funext x; simp only [φ1, φ2]; ring

/-- **Gluing `H^m`** from `B_{r/2}(c)` and the annulus. -/
theorem memHk_glue_ball (m : ℕ) : ∀ {u : (Fin n → ℝ) → ℝ},
    MemHk (euclBall c (r / 2)) m u → MemHk (annB c r) m u → MemHk (euclBall c r) m u := by
  induction m with
  | zero =>
    intro u hV hA
    have := memLp_glue c r hV hA
    show MemLp u 2 (volume.restrict (euclBall c r))
    simpa using this
  | succ m ih =>
    intro u hV hA
    have huB : MemLp u 2 (volume.restrict (euclBall c r)) := by
      simpa using memLp_glue c r hV.1 hA.1
    refine ⟨huB, fun i => ?_⟩
    obtain ⟨gV, hgV, hgVm⟩ := hV.2 i
    obtain ⟨gA, hgA, hgAm⟩ := hA.2 i
    refine ⟨_, weak_glue_ball c r huB hgV hgA hgVm.memLp hgAm.memLp, ih ?_ ?_⟩
    · refine hgVm.congr_ae ?_
      rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c (r / 2))]
      exact Eventually.of_forall fun x hx => by simp [hx]
    · have huniq : ∀ᵐ x, x ∈ annB c r ∩ euclBall c (r / 2) → gV x = gA x :=
        weakR_ae_eq ((isOpen_annB c r).inter (isOpen_euclBall c (r / 2)))
          (hgV.mono_set inter_subset_right) (hgA.mono_set inter_subset_left)
          (hgVm.memLp.mono_measure (Measure.restrict_mono inter_subset_right le_rfl))
          (hgAm.memLp.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
      refine hgAm.congr_ae ?_
      rw [EventuallyEq, ae_restrict_iff' (isOpen_annB c r).measurableSet]
      filter_upwards [huniq] with x hx hxA
      by_cases hxV : x ∈ euclBall c (r / 2)
      · simp [hxV, hx ⟨hxA, hxV⟩]
      · simp [hxV]

/-- A smooth function equal to `1/|x - c|²` on `|x - c| ≥ r/4`. -/
def invS (x : Fin n → ℝ) : ℝ :=
  (sqDist c x + (r / 4) ^ 2 * (1 - Real.smoothTransition (16 * sqDist c x / r ^ 2)))⁻¹

theorem invS_den_pos (x : Fin n → ℝ) :
    0 < sqDist c x + (r / 4) ^ 2 * (1 - Real.smoothTransition (16 * sqDist c x / r ^ 2)) := by
  have hr0 := hr.out
  have hs := sqDist_nonneg c x
  rcases lt_or_ge (16 * sqDist c x / r ^ 2) 1 with h | h
  · have := Real.smoothTransition.lt_one_of_lt_one h
    have : 0 < (r / 4) ^ 2 * (1 - Real.smoothTransition (16 * sqDist c x / r ^ 2)) := by
      apply mul_pos (by positivity); linarith
    linarith
  · have h1 : (r / 4) ^ 2 ≤ sqDist c x := by
      rw [le_div_iff₀ (by positivity)] at h; nlinarith
    have := Real.smoothTransition.le_one (16 * sqDist c x / r ^ 2)
    have : 0 ≤ (r / 4) ^ 2 * (1 - Real.smoothTransition (16 * sqDist c x / r ^ 2)) := by
      apply mul_nonneg (by positivity); linarith
    have : 0 < sqDist c x := lt_of_lt_of_le (by positivity) h1
    linarith

theorem contDiff_invS : ContDiff ℝ ∞ (invS c r) := by
  unfold invS
  refine ContDiff.inv ?_ fun x => (invS_den_pos c r x).ne'
  exact (contDiff_sqDist c).add (contDiff_const.mul (contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul (contDiff_sqDist c)).div_const _))))

theorem invS_eq {x : Fin n → ℝ} (hx : (r / 4) ^ 2 ≤ sqDist c x) : invS c r x = (sqDist c x)⁻¹ := by
  have hr0 := hr.out
  unfold invS
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by positivity)]; nlinarith)]
  simp

end HigherBall

/-! ### The `H^{k+2}` induction -/

section Induction

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

theorem norm_toLp_sub_eq {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict (euclBall c r)))
    (F : L2B c r) :
    ‖hf.toLp f - F‖ = (eLpNorm (f - (F : (Fin n → ℝ) → ℝ)) 2
      (volume.restrict (euclBall c r))).toReal := by
  rw [Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (hf.toLp f) F, hf.coeFn_toLp] with x h1 h2
  rw [h1, Pi.sub_apply, h2, Pi.sub_apply]

theorem tendsto_toLp_of_conv0 {ψ : ℕ → (Fin n → ℝ) → ℝ}
    (hψ : ∀ m, MemLp (ψ m) 2 (volume.restrict (euclBall c r))) {F : L2B c r}
    (h : Tendsto (fun m => eLpNorm (ψ m - (F : (Fin n → ℝ) → ℝ)) 2
      (volume.restrict (euclBall c r))) atTop (𝓝 0)) :
    Tendsto (fun m => (hψ m).toLp (ψ m)) atTop (𝓝 F) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [norm_toLp_sub_eq c r]
  rw [← ENNReal.toReal_zero]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

/-- `H¹`-convergent smooth data define an element of `H¹(B)` (closure of `C¹` graphs) with the
prescribed function component. -/
theorem exists_H1B_of_conv {φ : ℕ → (Fin n → ℝ) → ℝ} (hφ : ∀ m, ContDiff ℝ ∞ (φ m))
    {F : L2B c r} (h : ConvHk (euclBall c r) 1 φ (F : (Fin n → ℝ) → ℝ)) :
    ∃ Fh ∈ H1B c r, Fh none = F ∧ ∀ i,
      ConvHk (euclBall c r) 0 (fun m => pd (φ m) i) ((Fh (some i) : L2B c r) : (Fin n → ℝ) → ℝ) := by
  have hφ1 : ∀ m, ContDiff ℝ 1 (φ m) := fun m => (hφ m).of_le (by simp)
  choose g hg using h.2
  set Fh : H1Amb c r := WithLp.toLp 2 fun k => match k with
    | none => F
    | some i => (hg i).1.toLp (g i)
  have hlim : Tendsto (fun m => graphC1 c r ⟨φ m, show φ m ∈ C1fun from hφ1 m⟩) atTop (𝓝 Fh) := by
    have he := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin n) => L2B c r)).symm.continuous
    have : Tendsto (fun m => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin n) => L2B c r))
        (graphC1 c r ⟨φ m, show φ m ∈ C1fun from hφ1 m⟩)) atTop
        (𝓝 ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin n) => L2B c r)) Fh)) := by
      rw [tendsto_pi_nhds]
      intro k
      cases k with
      | none =>
        exact tendsto_toLp_of_conv0 c r (fun m => memLp_ball_of_C1 c r (hφ1 m)) h.1.2
      | some i =>
        have h2 := tendsto_toLp_of_conv0 c r (fun m => memLp_ball_pd_of_C1 c r (hφ1 m) i)
          (F := (hg i).1.toLp (g i)) ?_
        · exact h2
        · refine (hg i).2.congr fun m => ?_
          refine eLpNorm_congr_ae ?_
          filter_upwards [(hg i).1.coeFn_toLp] with x hx
          simp [hx]
    have := (he.tendsto _).comp this
    refine (this.congr fun m => ?_).trans (le_of_eq ?_)
    · simp
    · simp
  have hmem : Fh ∈ H1B c r := (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    (Eventually.of_forall fun m => graphC1_mem c r _)
  refine ⟨Fh, hmem, rfl, fun i => ⟨Lp.memLp _, ?_⟩⟩
  refine (hg i).2.congr fun m => ?_
  refine eLpNorm_congr_ae ?_
  filter_upwards [(hg i).1.coeFn_toLp] with x hx
  show (pd (φ m) i - g i) x = (pd (φ m) i - ((hg i).1.toLp (g i) : (Fin n → ℝ) → ℝ)) x
  simp [hx]

/-- **Commutation of the solution operator with the rotation fields** on `H¹(B)` data:
`Sol(R_ij F) = R_ij Sol(F)` (function components). -/
theorem sol_rotDer_none {i j : Fin n} (h : i ≠ j) :
    ∀ Fh ∈ H1B c r, ((solCLM c r (rotDerOp c r i j Fh) : H1B0 c r) : H1Amb c r) none =
      rotDerOp c r i j (solCLM c r (Fh none)) := by
  have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none).continuous
  refine H1B_induction c r ?_ fun u => ?_
  · exact isClosed_eq ((hp.comp continuous_subtype_val).comp ((solCLM c r).continuous.comp
      (rotDerOp c r i j).continuous)) ((rotDerOp c r i j).continuous.comp
        (continuous_subtype_val.comp ((solCLM c r).continuous.comp hp)))
  · rw [rotDerOp_graphC1, graphC1_none]
    exact (tangential_smooth c r h u.2).1

/-- Uniqueness of `L²` limits. -/
theorem conv0_unique {Ω : Set (Fin n → ℝ)} {ψ : ℕ → (Fin n → ℝ) → ℝ} {g g' : (Fin n → ℝ) → ℝ}
    (hψ : ∀ m, AEStronglyMeasurable (ψ m) (volume.restrict Ω))
    (h : ConvHk Ω 0 ψ g) (h' : ConvHk Ω 0 ψ g') : g =ᵐ[volume.restrict Ω] g' := by
  have hle : ∀ m, eLpNorm (g - g') 2 (volume.restrict Ω) ≤
      eLpNorm (ψ m - g) 2 (volume.restrict Ω) + eLpNorm (ψ m - g') 2 (volume.restrict Ω) := by
    intro m
    have e : g - g' = -(ψ m - g) + (ψ m - g') := by abel
    rw [e]
    refine (eLpNorm_add_le ((hψ m).sub h.1.1).neg ((hψ m).sub h'.1.1) (by norm_num)).trans ?_
    rw [eLpNorm_neg]
  have hlim := h.2.add h'.2
  rw [add_zero] at hlim
  have h0 : eLpNorm (g - g') 2 (volume.restrict Ω) = 0 :=
    le_antisymm (ge_of_tendsto' hlim hle) zero_le
  have := (eLpNorm_eq_zero_iff (h.1.1.sub h'.1.1) (by norm_num)).mp h0
  filter_upwards [this] with x hx
  simpa [sub_eq_zero] using hx

theorem ConvHk.congr_lim {Ω : Set (Fin n → ℝ)} {k : ℕ} {φ : ℕ → (Fin n → ℝ) → ℝ}
    {u u' : (Fin n → ℝ) → ℝ} (h : ConvHk Ω k φ u) (hu : u =ᵐ[volume.restrict Ω] u') :
    ConvHk Ω k φ u' := by
  have hb : MemLp u' 2 (volume.restrict Ω) ∧
      Tendsto (fun m => eLpNorm (φ m - u') 2 (volume.restrict Ω)) atTop (𝓝 0) :=
    ⟨(memLp_congr_ae hu).mp h.base.1, h.base.2.congr fun m => eLpNorm_congr_ae
      (hu.mono fun x hx => by simp [hx])⟩
  cases k with
  | zero => exact hb
  | succ k => exact ⟨hb, h.2⟩

theorem contDiff_rotDer {i j : Fin n} {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (rotDer c i j u) := by
  have h1 : rotDer c i j u = fun y => yc c i y * pd u j y - yc c j y * pd u i y := rfl
  rw [h1]
  exact ((contDiff_yc c i).mul (contDiff_pd hu j)).sub ((contDiff_yc c j).mul (contDiff_pd hu i))

/-- **The rotation field preserves the approximation classes**: `R_ij φ_m → R_ij F` in `H^k`. -/
theorem conv_rotDer {k : ℕ} {i j : Fin n} {φ : ℕ → (Fin n → ℝ) → ℝ}
    (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) {F : L2B c r}
    (hk : ConvHk (euclBall c r) (k + 1) φ (F : (Fin n → ℝ) → ℝ)) {Fh : H1Amb c r}
    (hFh : ∀ l, ConvHk (euclBall c r) 0 (fun m => pd (φ m) l)
      ((Fh (some l) : L2B c r) : (Fin n → ℝ) → ℝ)) :
    ConvHk (euclBall c r) k (fun m => rotDer c i j (φ m))
      (rotDerOp c r i j Fh : (Fin n → ℝ) → ℝ) := by
  have hB := isBounded_euclBall' c r
  have hBm := measurableSet_euclBall c r
  obtain ⟨gi, hgi⟩ := hk.2 i
  obtain ⟨gj, hgj⟩ := hk.2 j
  have hpd : ∀ l, ∀ m, ContDiff ℝ ∞ (pd (φ m) l) := fun l m => contDiff_pd (hφ m) l
  have hc := (hgj.mul_smooth hB hBm (contDiff_yc c i) (hpd j)).sub
    (fun m => (contDiff_yc c i).mul (hpd j m)) (fun m => (contDiff_yc c j).mul (hpd i m))
    (hgi.mul_smooth hB hBm (contDiff_yc c j) (hpd i))
  have hφpd : ∀ l, ∀ m, AEStronglyMeasurable (pd (φ m) l) (volume.restrict (euclBall c r)) :=
    fun l m => (continuous_pd ((hφ m).of_le (by simp)) l).aestronglyMeasurable
  have hai : gi =ᵐ[volume.restrict (euclBall c r)] ((Fh (some i) : L2B c r) : (Fin n → ℝ) → ℝ) :=
    conv0_unique (hφpd i) hgi.base (hFh i)
  have haj : gj =ᵐ[volume.restrict (euclBall c r)] ((Fh (some j) : L2B c r) : (Fin n → ℝ) → ℝ) :=
    conv0_unique (hφpd j) hgj.base (hFh j)
  refine hc.congr_lim ?_
  filter_upwards [hai, haj, coeFn_rotDerOp c r i j Fh] with x h1 h2 h3
  rw [h3, ← h1, ← h2]; rfl

/-- **`H^{k+2}` regularity of the weak Neumann problem on a ball** (stage C4b): if the data
`F ∈ L²(B)` is the `H^k(B)` limit of smooth functions, then the mean-zero weak solution
`ξ = solCLM F` of `Δξ = F - avg F`, `∂_νξ = 0` lies in `H^{k+2}(B)` (weak derivatives up to order
`k + 2` in `L²(B)`, on the whole open ball). -/
theorem neumann_Hk (k : ℕ) : ∀ (F : L2B c r) (φ : ℕ → (Fin n → ℝ) → ℝ),
    (∀ m, ContDiff ℝ ∞ (φ m)) → ConvHk (euclBall c r) k φ (F : (Fin n → ℝ) → ℝ) →
    MemHk (euclBall c r) (k + 2) (solFn c r F) := by
  have hB := isBounded_euclBall' c r
  have hBm := measurableSet_euclBall c r
  have hBf : volume (euclBall c r) ≠ ⊤ := (volume_euclBall_lt_top c hr.out.le).ne
  induction k with
  | zero =>
    intro F φ hφ hk
    refine ⟨memLp_solFn c r F, fun j => ⟨solGrad c r F j, solGrad_weak c r F j,
      memLp_solGrad c r F j, fun l => ?_⟩⟩
    obtain ⟨H, hHL, hH⟩ := neumann_H2_ball c r F j l
    exact ⟨H, hH, hHL⟩
  | succ k ih =>
    intro F φ hφ hk
    set ξ := solFn c r F
    have hξ : MemHk (euclBall c r) (k + 2) ξ := ih F φ hφ (hk.mono (Nat.le_succ k))
    have hFk : MemHk (euclBall c r) (k + 1) (F : (Fin n → ℝ) → ℝ) := hk.memHk hB hBm hφ
    have hRhs : MemHk (euclBall c r) (k + 1) (solRhs c r F) := hFk.sub (memHk_const hBf _)
    have hgrad : ∀ j, MemHk (euclBall c r) (k + 1) (solGrad c r F j) := fun j =>
      hξ.deriv (isOpen_euclBall c r) (solGrad_weak c r F j) (memLp_solGrad c r F j)
    obtain ⟨Fh, hFhB, hFh0, hFhg⟩ := exists_H1B_of_conv c r hφ (hk.mono (by omega))
    -- the tangential derivatives are `H^{k+2}`
    have hZ : ∀ i j, i ≠ j → MemHk (euclBall c r) (k + 2) (solFn c r (rotDerOp c r i j Fh)) :=
      fun i j _ => ih _ _ (fun m => contDiff_rotDer c (hφ m)) (conv_rotDer c r hφ hk hFhg)
    have htan : ∀ i j l, MemHk (euclBall c r) (k + 1) (tanM c r F i j l) := by
      intro i j l
      by_cases hij : i = j
      · have : tanM c r F i j l = fun _ => 0 := by funext x; simp [tanM, hij]
        rw [this]; exact memHk_zero_fn _
      · have hgradZ : ((tanZ c r F i j : H1B0 c r) : H1Amb c r) (some l) =
            ((solCLM c r (rotDerOp c r i j Fh) : H1B0 c r) : H1Amb c r) (some l) := by
          have h1 := hasWeakPartialR_of_H1B c r (tanZ c r F i j).2.1 l
          have h2 := hasWeakPartialR_of_H1B c r (solCLM c r (rotDerOp c r i j Fh)).2.1 l
          have e : ((solCLM c r (rotDerOp c r i j Fh) : H1B0 c r) : H1Amb c r) none =
              ((tanZ c r F i j : H1B0 c r) : H1Amb c r) none := by
            rw [sol_rotDer_none c r hij Fh hFhB, tanZ_none c r F hij, hFh0]
          rw [e] at h2
          exact weakR_unique c r l h1 h2
        have hZl : MemHk (euclBall c r) (k + 1)
            ((((tanZ c r F i j : H1B0 c r) : H1Amb c r) (some l) : L2B c r) :
              (Fin n → ℝ) → ℝ) := by
          rw [hgradZ]
          exact (hZ i j hij).deriv (isOpen_euclBall c r) (solGrad_weak c r _ l)
            (memLp_solGrad c r _ l)
        have e : tanM c r F i j l = fun x =>
            ((((tanZ c r F i j : H1B0 c r) : H1Amb c r) (some l) : L2B c r) :
              (Fin n → ℝ) → ℝ) x - (if i = l then solGrad c r F j x else 0) +
                (if j = l then solGrad c r F i x else 0) := by
          funext x; simp [tanM, hij]
        rw [e]
        have hif : ∀ (p q : Fin n), MemHk (euclBall c r) (k + 1)
            (fun x => if p = l then solGrad c r F q x else 0) := by
          intro p q
          by_cases hp : p = l
          · simp only [hp, if_true]; exact hgrad q
          · simp only [hp, if_false]; exact memHk_zero_fn _
        exact (hZl.sub (hif i j)).add (hif j i)
    have hradN : ∀ j l, MemHk (euclBall c r) (k + 1) (radN c r F j l) := by
      intro j l
      unfold radN
      refine (MemHk.sum' _ fun i _ => (htan i j l).mul_smooth hB hBm (contDiff_yc c i)).add ?_
      refine MemHk.mul_smooth hB hBm (contDiff_yc c j) ?_
      exact (hRhs.mul_smooth hB hBm (contDiff_yc c l)).sub (MemHk.sum' _ fun i _ => htan l i i)
    -- regularity of each gradient component by gluing
    have hgradK : ∀ j, MemHk (euclBall c r) (k + 2) (solGrad c r F j) := by
      intro j
      refine memHk_glue_ball c r (k + 2) ?_ ?_
      · have hV := neumann_interior_Hk c r (k + 1) F hRhs hξ
        refine hV.deriv (isOpen_euclBall c (r / 2)) ((solGrad_weak c r F j).mono_set ?_)
          ((memLp_solGrad c r F j).mono_measure (Measure.restrict_mono ?_ le_rfl))
        · intro x (hx : sqDist c x < (r / 2) ^ 2)
          show sqDist c x < r ^ 2; have := hr.out; nlinarith
        · intro x (hx : sqDist c x < (r / 2) ^ 2)
          show sqDist c x < r ^ 2; have := hr.out; nlinarith
      · refine ⟨(memLp_solGrad c r F j).mono_measure (Measure.restrict_mono (annB_subset c r)
          le_rfl), fun l => ⟨radH c r F j l, radH_weak c r F j l, ?_⟩⟩
        have h1 := ((hradN j l).restrict (annB_subset c r)).mul_smooth (isBounded_annB c r)
          (isOpen_annB c r).measurableSet (contDiff_invS c r)
        refine h1.congr_ae ?_
        rw [EventuallyEq, ae_restrict_iff' (isOpen_annB c r).measurableSet]
        refine Eventually.of_forall fun x hx => ?_
        rw [invS_eq c r (le_of_lt hx.2), radH, div_eq_inv_mul]
    exact ⟨memLp_solFn c r F, fun j => ⟨solGrad c r F j, solGrad_weak c r F j, hgradK j⟩⟩

end Induction

end RenewalGeometry.BallAnalysis.BallReg
