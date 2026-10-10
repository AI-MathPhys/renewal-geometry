/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallInteriorRegularity
import RenewalGeometry.Analysis.BallTangentialRegularity

/-!
# The radial decomposition of the Hessian and `H²` regularity of the Neumann problem on a ball
  (stage C4b, step 3, of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

With `y = x - c`, `R_ij = y_i ∂_j - y_j ∂_i` and `M_ijk = ∂_k(R_ij ξ) - δ_ki ∂_jξ + δ_kj ∂_iξ`
(`= y_i ∂_k∂_jξ - y_j ∂_k∂_iξ` for smooth `ξ`), the Hessian of a solution of `Δξ = f` is recovered
from the tangential derivatives and the equation away from the centre:

  `|y|² ∂_k∂_jξ = Σ_i y_i M_ijk + y_j (y_k f - Σ_i M_kii)`.

* `radial_hessian` (**generic, distributional**): on an open `A ⊆ Ω` not containing `c`, if `u`
  has weak gradient `g` on `Ω`, `Σ_k ∫ ∂_kχ g_k = -∫ χ f` (weak `Δu = f`), and the pairings
  `T_jk(χ) = -∫ ∂_kχ g_j` satisfy `T_jk(y_iχ) - T_ik(y_jχ) = ∫ χ M_ijk`, then
  `∂_k g_j = (Σ_i y_i M_ijk + y_j (y_k f - Σ_i M_kii)) / |y|²` weakly on `A`.  Proof by testing
  against `φ = |y|² ψ` and the symmetry/trace identities of the pairings.
* `neumann_H2_ball` (**`H²` regularity of the weak Neumann problem on a ball**): for every
  `F ∈ L²(B)`, the gradient components of `ξ = solCLM F` have weak derivatives in `L²(B)` on the
  whole ball: interior regularity (`interior_H2`) on `B_{r/2}(c)`, the radial formula with the
  tangential regularity (`tangential_regularity`) on `r/4 < |x - c| < r`, glued by a partition of
  unity and uniqueness of weak derivatives.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ### Coordinates and the distributional pairings -/

section Algebra

variable (c : Fin n → ℝ)

/-- The centred coordinate `y_i = x_i - c_i`. -/
def yc (i : Fin n) (x : Fin n → ℝ) : ℝ := x i - c i

theorem contDiff_yc (i : Fin n) : ContDiff ℝ ∞ (yc c i) :=
  (contDiff_apply ℝ ℝ i).sub contDiff_const

theorem pd_yc (i k : Fin n) (x : Fin n → ℝ) : pd (yc c i) k x = if i = k then 1 else 0 :=
  pd_coord_sub c i k x

theorem isTest_yc_mul {Ω : Set (Fin n → ℝ)} {χ : (Fin n → ℝ) → ℝ} (hχ : IsTest Ω χ) (i : Fin n) :
    IsTest Ω (fun x => yc c i x * χ x) := by
  have := hχ.mul_smooth (contDiff_yc c i)
  convert this using 1; funext x; ring

theorem pd_yc_mul {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ 1 χ) (i k : Fin n) (x : Fin n → ℝ) :
    pd (fun x => yc c i x * χ x) k x = (if i = k then χ x else 0) + yc c i x * pd χ k x := by
  rw [pd_mul ((contDiff_yc c i).of_le (by simp)) hχ, pd_yc]
  split_ifs <;> ring

theorem sqDist_eq_sum_yc (x : Fin n → ℝ) : sqDist c x = ∑ i, yc c i x * yc c i x := by
  simp [sqDist, yc, sq]

theorem eq_of_sqDist_eq_zero {x : Fin n → ℝ} (h : sqDist c x = 0) : x = c := by
  funext i
  have := sq_le_sqDist c x i
  rw [h] at this
  have : (x i - c i) ^ 2 = 0 := le_antisymm this (sq_nonneg _)
  linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp this]

/-- The distributional pairing `T_jk(χ) = -∫ ∂_kχ g_j` (`= ⟨∂_k∂_j u, χ⟩` for `g = ∇u`). -/
def distT (g : Fin n → (Fin n → ℝ) → ℝ) (j k : Fin n) (χ : (Fin n → ℝ) → ℝ) : ℝ :=
  -∫ x, pd χ k x * g j x

variable {Ω : Set (Fin n → ℝ)} {u f : (Fin n → ℝ) → ℝ} {g : Fin n → (Fin n → ℝ) → ℝ}

/-- Symmetry of the pairings (`∂_k∂_j = ∂_j∂_k`). -/
theorem distT_symm (h1 : ∀ j, HasWeakPartialR Ω j u (g j)) {χ : (Fin n → ℝ) → ℝ}
    (hχ : IsTest Ω χ) (i k : Fin n) : distT g i k χ = distT g k i χ := by
  unfold distT
  have e1 := h1 i (pd χ k) (isTest_pd hχ k)
  have e2 := h1 k (pd χ i) (isTest_pd hχ i)
  have hs : pd (pd χ k) i = pd (pd χ i) k := funext fun x =>
    pd_pd_symm (hχ.smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) i k x
  rw [hs] at e1
  rw [e1] at e2
  linarith

/-- The trace of the pairings is the equation: `Σ_i T_ii(χ) = ∫ χ f`. -/
theorem sum_distT_diag (h2 : ∀ χ, IsTest Ω χ → ∑ k, ∫ x, pd χ k x * g k x = -∫ x, χ x * f x)
    {χ : (Fin n → ℝ) → ℝ} (hχ : IsTest Ω χ) : ∑ i, distT g i i χ = ∫ x, χ x * f x := by
  unfold distT
  rw [Finset.sum_neg_distrib, h2 χ hχ, neg_neg]

/-- Linearity of the pairings on finite sums of test functions. -/
theorem distT_sum (hg : ∀ j, MemLp (g j) 2 (volume.restrict Ω)) {χ : Fin n → (Fin n → ℝ) → ℝ}
    (hχ : ∀ i, IsTest Ω (χ i)) (j k : Fin n) :
    distT g j k (fun x => ∑ i, χ i x) = ∑ i, distT g j k (χ i) := by
  unfold distT
  have hpd : ∀ x, pd (fun x => ∑ i, χ i x) k x = ∑ i, pd (χ i) k x := fun x =>
    pd_sum_real (fun i _ => ((hχ i).smooth.differentiable (by simp)) x) k
  simp only [hpd, Finset.sum_mul]
  rw [integral_finset_sum _ fun i _ => integrable_mul_of_memLp_restrict (isTest_pd (hχ i) k).continuous
    (isTest_pd (hχ i) k).compact (isTest_pd (hχ i) k).subset (hg j), Finset.sum_neg_distrib]

theorem integrable_test_mul {χ v : (Fin n → ℝ) → ℝ} (hχ : IsTest Ω χ)
    (hv : MemLp v 2 (volume.restrict Ω)) : Integrable (fun x => χ x * v x) :=
  integrable_mul_of_memLp_restrict hχ.continuous hχ.compact hχ.subset hv

/-- **The radial formula for the Hessian** (generic, distributional form): away from the centre,
`∂_k g_j = (Σ_i y_i M_ijk + y_j (y_k f - Σ_i M_kii)) / |y|²` weakly. -/
theorem radial_hessian {A : Set (Fin n → ℝ)} (hAΩ : A ⊆ Ω) (hcA : c ∉ A)
    {M : Fin n → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    (hg : ∀ j, MemLp (g j) 2 (volume.restrict Ω)) (hf : MemLp f 2 (volume.restrict Ω))
    (hM : ∀ i j k, MemLp (M i j k) 2 (volume.restrict Ω))
    (h1 : ∀ j, HasWeakPartialR Ω j u (g j))
    (h2 : ∀ χ, IsTest Ω χ → ∑ k, ∫ x, pd χ k x * g k x = -∫ x, χ x * f x)
    (h3 : ∀ i j k χ, IsTest Ω χ → distT g j k (fun x => yc c i x * χ x) -
      distT g i k (fun x => yc c j x * χ x) = ∫ x, χ x * M i j k x)
    (j k : Fin n) :
    HasWeakPartialR A k (g j) (fun x => (∑ i, yc c i x * M i j k x +
      yc c j x * (yc c k x * f x - ∑ i, M k i i x)) / sqDist c x) := by
  intro φ hφ
  have hφΩ : IsTest Ω φ := hφ.mono hAΩ
  have hcφ : c ∉ tsupport φ := fun h => hcA (hφ.subset h)
  -- `ψ = φ / |y|²`
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : (Fin n → ℝ) → ℝ, ψ = fun x => φ x / sqDist c x := ⟨_, rfl⟩
  have hψs : ContDiff ℝ ∞ ψ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hne : sqDist c x ≠ 0 := fun h0 => hcφ (eq_of_sqDist_eq_zero c h0 ▸ hx)
      rw [hψdef]
      exact hφ.smooth.contDiffAt.div (contDiff_sqDist c).contDiffAt hne
    · have hev : φ =ᶠ[𝓝 x] fun _ => 0 := (notMem_tsupport_iff_eventuallyEq).mp hx
      have : ψ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [hev] with y hy
        rw [hψdef]; simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq this
  have hψsupp : tsupport ψ ⊆ tsupport φ := by
    refine closure_mono fun x hx => ?_
    intro h0; apply hx; rw [hψdef]; simp [h0]
  have hψ : IsTest A ψ := ⟨hψs, hφ.compact.mono' (subset_tsupport ψ |>.trans hψsupp),
    hψsupp.trans hφ.subset⟩
  have hψΩ : IsTest Ω ψ := hψ.mono hAΩ
  have hφeq : ∀ x, φ x = ∑ i, yc c i x * (yc c i x * ψ x) := by
    intro x
    have e : ∑ i, yc c i x * (yc c i x * ψ x) = sqDist c x * ψ x := by
      rw [sqDist_eq_sum_yc, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    by_cases h0 : sqDist c x = 0
    · have hxc := eq_of_sqDist_eq_zero c h0
      have : φ x = 0 := image_eq_zero_of_notMem_tsupport (hxc ▸ hcφ)
      rw [this, h0, zero_mul]
    · rw [hψdef]; field_simp
  -- test functions
  have tY : ∀ i (χ : (Fin n → ℝ) → ℝ), IsTest Ω χ → IsTest Ω (fun x => yc c i x * χ x) :=
    fun i χ hχ => isTest_yc_mul c hχ i
  have tYψ : ∀ i, IsTest Ω (fun x => yc c i x * ψ x) := fun i => tY i ψ hψΩ
  have tYYψ : ∀ i l, IsTest Ω (fun x => yc c i x * (yc c l x * ψ x)) := fun i l =>
    tY i _ (tYψ l)
  -- the left-hand side through the pairings
  have hL : ∫ x, pd φ k x * g j x = -distT g j k φ := by unfold distT; ring
  have hφfun : φ = fun x => ∑ i, yc c i x * (yc c i x * ψ x) := funext hφeq
  have step1 : distT g j k φ = ∑ i, distT g j k (fun x => yc c i x * (yc c i x * ψ x)) := by
    rw [hφfun]; exact distT_sum hg (fun i => tYYψ i i) j k
  have step2 : ∀ i, distT g j k (fun x => yc c i x * (yc c i x * ψ x)) =
      distT g i k (fun x => yc c j x * (yc c i x * ψ x)) +
        ∫ x, (yc c i x * ψ x) * M i j k x := by
    intro i
    have := h3 i j k _ (tYψ i)
    linarith
  have step3 : ∀ i, distT g i k (fun x => yc c j x * (yc c i x * ψ x)) =
      distT g i i (fun x => yc c k x * (yc c j x * ψ x)) -
        ∫ x, (yc c j x * ψ x) * M k i i x := by
    intro i
    have e : (fun x => yc c j x * (yc c i x * ψ x)) = fun x => yc c i x * (yc c j x * ψ x) := by
      funext x; ring
    rw [e, distT_symm h1 (tYYψ i j) i k]
    have := h3 k i i _ (tYψ j)
    linarith
  have step4 : ∑ i, distT g i i (fun x => yc c k x * (yc c j x * ψ x)) =
      ∫ x, (yc c k x * (yc c j x * ψ x)) * f x := sum_distT_diag h2 (tYYψ k j)
  have hT : distT g j k φ = (∫ x, (yc c k x * (yc c j x * ψ x)) * f x) -
      ∑ i, (∫ x, (yc c j x * ψ x) * M k i i x) + ∑ i, ∫ x, (yc c i x * ψ x) * M i j k x := by
    rw [step1]
    simp only [step2, step3]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, step4]
  -- the right-hand side
  have hR : ∫ x, φ x * ((∑ i, yc c i x * M i j k x +
      yc c j x * (yc c k x * f x - ∑ i, M k i i x)) / sqDist c x) =
      ∑ i, (∫ x, (yc c i x * ψ x) * M i j k x) +
        ((∫ x, (yc c k x * (yc c j x * ψ x)) * f x) - ∑ i, ∫ x, (yc c j x * ψ x) * M k i i x) := by
    have hpt : ∀ x, φ x * ((∑ i, yc c i x * M i j k x +
        yc c j x * (yc c k x * f x - ∑ i, M k i i x)) / sqDist c x) =
        ∑ i, (yc c i x * ψ x) * M i j k x +
          ((yc c k x * (yc c j x * ψ x)) * f x - ∑ i, (yc c j x * ψ x) * M k i i x) := by
      intro x
      have hψx : ψ x = φ x / sqDist c x := by rw [hψdef]
      rw [hψx]
      have a1 : ∑ i, yc c i x * (φ x / sqDist c x) * M i j k x =
          (φ x / sqDist c x) * ∑ i, yc c i x * M i j k x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      have a2 : ∑ i, yc c j x * (φ x / sqDist c x) * M k i i x =
          (φ x / sqDist c x) * yc c j x * ∑ i, M k i i x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [a1, a2]
      ring
    simp only [hpt]
    have i1 : ∀ i, Integrable fun x => (yc c i x * ψ x) * M i j k x := fun i =>
      integrable_test_mul (tYψ i) (hM i j k)
    have i2 : Integrable fun x => (yc c k x * (yc c j x * ψ x)) * f x :=
      integrable_test_mul (tYYψ k j) hf
    have i3 : ∀ i, Integrable fun x => (yc c j x * ψ x) * M k i i x := fun i =>
      integrable_test_mul (tYψ j) (hM k i i)
    have i3' : Integrable fun x => ∑ i, (yc c j x * ψ x) * M k i i x :=
      integrable_finset_sum _ fun i _ => i3 i
    have i1' : Integrable fun x => ∑ i, (yc c i x * ψ x) * M i j k x :=
      integrable_finset_sum _ fun i _ => i1 i
    rw [integral_add (f := fun x => ∑ i, (yc c i x * ψ x) * M i j k x)
        (g := fun x => (yc c k x * (yc c j x * ψ x)) * f x - ∑ i, (yc c j x * ψ x) * M k i i x)
        i1' (i2.sub i3'),
      integral_sub (f := fun x => (yc c k x * (yc c j x * ψ x)) * f x)
        (g := fun x => ∑ i, (yc c j x * ψ x) * M k i i x) i2 i3',
      integral_finset_sum _ fun i _ => i1 i, integral_finset_sum _ fun i _ => i3 i]
  rw [hL, hT, hR]
  ring

end Algebra

/-! ### The Neumann solution: weak data -/

section BallData

variable [NeZero n] (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- The function component of `Sol F`. -/
def solFn (F : L2B c r) : (Fin n → ℝ) → ℝ :=
  (((solCLM c r F : H1B0 c r) : H1Amb c r) none : (Fin n → ℝ) → ℝ)

/-- The gradient components of `Sol F`. -/
def solGrad (F : L2B c r) (k : Fin n) : (Fin n → ℝ) → ℝ :=
  (((solCLM c r F : H1B0 c r) : H1Amb c r) (some k) : (Fin n → ℝ) → ℝ)

/-- The right-hand side `F - avg F` of the Neumann problem solved by `Sol F`. -/
def solRhs (F : L2B c r) (x : Fin n → ℝ) : ℝ := F x - avgB c r F

theorem memLp_solFn (F : L2B c r) : MemLp (solFn c r F) 2 (volume.restrict (euclBall c r)) :=
  Lp.memLp _

theorem memLp_solGrad (F : L2B c r) (k : Fin n) :
    MemLp (solGrad c r F k) 2 (volume.restrict (euclBall c r)) := Lp.memLp _

theorem memLp_solRhs (F : L2B c r) : MemLp (solRhs c r F) 2 (volume.restrict (euclBall c r)) :=
  (Lp.memLp F).sub (memLp_const _)

/-- Real weak partials of elements of `H¹(B)`. -/
theorem hasWeakPartialR_of_H1B {x : H1Amb c r} (hx : x ∈ H1B c r) (k : Fin n) :
    HasWeakPartialR (euclBall c r) k ((x none : L2B c r) : (Fin n → ℝ) → ℝ)
      ((x (some k) : L2B c r) : (Fin n → ℝ) → ℝ) :=
  hasWeakPartialR_iff.mpr ((memW12_of_H1B c r hx).weak k)

theorem solGrad_weak (F : L2B c r) (k : Fin n) :
    HasWeakPartialR (euclBall c r) k (solFn c r F) (solGrad c r F k) :=
  hasWeakPartialR_of_H1B c r (solCLM c r F).2.1 k

/-- Whole-space integrals of test-function products are integrals over the ball. -/
theorem integral_test_eq_setIntegral {φ v : (Fin n → ℝ) → ℝ} (hφ : IsTest (euclBall c r) φ) :
    ∫ x, φ x * v x = ∫ x in euclBall c r, φ x * v x := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  rw [isTest_vanish hφ x hx, zero_mul]

/-- **The weak equation** `Δ(Sol F) = F - avg F` tested against `C_c^∞(B)`. -/
theorem solCLM_weak_test (F : L2B c r) {φ : (Fin n → ℝ) → ℝ} (hφ : IsTest (euclBall c r) φ) :
    ∑ k, ∫ x, pd φ k x * solGrad c r F k x = -∫ x, φ x * solRhs c r F x := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have h := solCLM_weak c r F (graphC1_mem c r ⟨φ, show φ ∈ C1fun from hφ1⟩)
  simp only [graphC1_some, graphC1_none, meanCLM_graph] at h
  have e1 : ∀ k, ⟪((solCLM c r F : H1B0 c r) : H1Amb c r) (some k),
      (memLp_ball_pd_of_C1 c r hφ1 k).toLp (pd φ k)⟫ = ∫ x, pd φ k x * solGrad c r F k x := by
    intro k
    rw [real_inner_comm, inner_toLp_left, ← integral_test_eq_setIntegral c r (isTest_pd hφ k)]
    rfl
  have e2 : ⟪F, (memLp_ball_of_C1 c r hφ1).toLp φ⟫ = ∫ x in euclBall c r, φ x * F x := by
    rw [real_inner_comm, inner_toLp_left]
  simp only [e1, e2] at h
  rw [h, integral_test_eq_setIntegral c r hφ]
  have hiF : IntegrableOn (fun x => φ x * F x) (euclBall c r) :=
    (integrable_test_mul hφ (Lp.memLp F)).integrableOn
  have hi1 : IntegrableOn φ (euclBall c r) :=
    integrableOn_euclBall hr.out.le hφ.continuous
  simp only [solRhs, mul_sub]
  rw [integral_sub hiF (hi1.mul_const _), integral_mul_const]
  ring

/-- The tangential derivatives of `Sol F` (from `tangential_regularity`), as an `H¹₀(B)` element
for each pair `i ≠ j` (and `0` for `i = j`). -/
def tanZ (F : L2B c r) (i j : Fin n) : H1B0 c r :=
  if h : i = j then 0 else (tangential_regularity c r h F).choose

theorem tanZ_none (F : L2B c r) {i j : Fin n} (h : i ≠ j) :
    ((tanZ c r F i j : H1B0 c r) : H1Amb c r) none = rotDerOp c r i j (solCLM c r F) := by
  simp only [tanZ, h, dif_neg, not_false_eq_true]
  exact (tangential_regularity c r h F).choose_spec.1

/-- The tensor `M_ijk = ∂_k(R_ij ξ) - δ_ki ∂_jξ + δ_kj ∂_iξ`. -/
def tanM (F : L2B c r) (i j k : Fin n) (x : Fin n → ℝ) : ℝ :=
  if i = j then 0 else
    (((tanZ c r F i j : H1B0 c r) : H1Amb c r) (some k) : (Fin n → ℝ) → ℝ) x -
      (if i = k then solGrad c r F j x else 0) + (if j = k then solGrad c r F i x else 0)

theorem memLp_tanM (F : L2B c r) (i j k : Fin n) :
    MemLp (tanM c r F i j k) 2 (volume.restrict (euclBall c r)) := by
  unfold tanM
  by_cases hij : i = j
  · simp only [hij, if_true]; exact memLp_const 0
  · simp only [hij, if_false]
    have h1 : MemLp (fun x => if i = k then solGrad c r F j x else 0) 2
        (volume.restrict (euclBall c r)) := by
      by_cases hk : i = k
      · simp only [hk, if_true]; exact memLp_solGrad c r F j
      · simp only [hk, if_false]; exact memLp_const 0
    have h2 : MemLp (fun x => if j = k then solGrad c r F i x else 0) 2
        (volume.restrict (euclBall c r)) := by
      by_cases hk : j = k
      · simp only [hk, if_true]; exact memLp_solGrad c r F i
      · simp only [hk, if_false]; exact memLp_const 0
    exact ((Lp.memLp (((tanZ c r F i j : H1B0 c r) : H1Amb c r) (some k))).sub h1).add h2

/-- **The commutator identity** `T_jk(y_iχ) - T_ik(y_jχ) = ∫ χ M_ijk` for the Neumann solution. -/
theorem distT_commutator (F : L2B c r) (i j k : Fin n) {χ : (Fin n → ℝ) → ℝ}
    (hχ : IsTest (euclBall c r) χ) :
    distT (solGrad c r F) j k (fun x => yc c i x * χ x) -
      distT (solGrad c r F) i k (fun x => yc c j x * χ x) = ∫ x, χ x * tanM c r F i j k x := by
  by_cases hij : i = j
  · subst hij; simp [tanM]
  have hχ1 : ContDiff ℝ 1 χ := hχ.smooth.of_le (by simp)
  set g := solGrad c r F
  have hZw := hasWeakPartialR_of_H1B c r (tanZ c r F i j).2.1 k χ hχ
  -- the function component of `Z` is `y_i g_j - y_j g_i` on the ball
  have hZ0 : ∀ᵐ x ∂(volume.restrict (euclBall c r)),
      ((((tanZ c r F i j : H1B0 c r) : H1Amb c r) none : L2B c r) : (Fin n → ℝ) → ℝ) x =
        yc c i x * g j x - yc c j x * g i x := by
    rw [tanZ_none c r F hij]
    filter_upwards [coeFn_rotDerOp c r i j (solCLM c r F)] with x hx
    rw [hx]; rfl
  have hZ0' : ∫ x, pd χ k x * ((((tanZ c r F i j : H1B0 c r) : H1Amb c r) none : L2B c r) : (Fin n → ℝ) → ℝ) x =
      ∫ x, pd χ k x * (yc c i x * g j x - yc c j x * g i x) := by
    rw [integral_test_eq_setIntegral c r (isTest_pd hχ k),
      integral_test_eq_setIntegral c r (isTest_pd hχ k)]
    refine integral_congr_ae ?_
    filter_upwards [hZ0] with x hx
    rw [hx]
  rw [hZ0'] at hZw
  have hgL : ∀ l, MemLp (g l) 2 (volume.restrict (euclBall c r)) := memLp_solGrad c r F
  have tY : ∀ l, IsTest (euclBall c r) (fun x => yc c l x * pd χ k x) := fun l =>
    isTest_yc_mul c (isTest_pd hχ k) l
  have e : ∀ (a b : Fin n), distT g b k (fun x => yc c a x * χ x) =
      -(if a = k then ∫ x, χ x * g b x else 0) - ∫ x, (yc c a x * pd χ k x) * g b x := by
    intro a b
    unfold distT
    simp only [pd_yc_mul c hχ1]
    have hsplit : ∀ x, ((if a = k then χ x else 0) + yc c a x * pd χ k x) * g b x =
        (if a = k then χ x * g b x else 0) + (yc c a x * pd χ k x) * g b x := by
      intro x; split_ifs <;> ring
    simp only [hsplit]
    by_cases hak : a = k
    · simp only [hak, if_true]
      rw [integral_add (f := fun x => χ x * g b x) (g := fun x => (yc c k x * pd χ k x) * g b x)
        (integrable_test_mul hχ (hgL b)) (integrable_test_mul (tY k) (hgL b))]
      ring
    · simp only [hak, if_false, zero_add]
      ring
  rw [e i j, e j i]
  have hcomb : ∫ x, pd χ k x * (yc c i x * g j x - yc c j x * g i x) =
      (∫ x, (yc c i x * pd χ k x) * g j x) - ∫ x, (yc c j x * pd χ k x) * g i x := by
    rw [← integral_sub (integrable_test_mul (tY i) (hgL j)) (integrable_test_mul (tY j) (hgL i))]
    congr 1; funext x; ring
  rw [hcomb] at hZw
  -- the right-hand side
  have hM : ∀ x, χ x * tanM c r F i j k x =
      χ x * ((((tanZ c r F i j : H1B0 c r) : H1Amb c r) (some k) : L2B c r) : (Fin n → ℝ) → ℝ) x -
        (if i = k then χ x * g j x else 0) + (if j = k then χ x * g i x else 0) := by
    intro x
    simp only [tanM, hij, if_false]
    split_ifs <;> ring
  simp only [hM]
  have iZ := integrable_test_mul hχ (Lp.memLp ((((tanZ c r F i j : H1B0 c r) : H1Amb c r) (some k) : L2B c r)))
  have iA : Integrable fun x => if i = k then χ x * g j x else 0 := by
    split_ifs
    · exact integrable_test_mul hχ (hgL j)
    · exact integrable_zero _ _ _
  have iB : Integrable fun x => if j = k then χ x * g i x else 0 := by
    split_ifs
    · exact integrable_test_mul hχ (hgL i)
    · exact integrable_zero _ _ _
  rw [integral_add (f := fun x => χ x * ((((tanZ c r F i j : H1B0 c r) : H1Amb c r) (some k) :
      L2B c r) : (Fin n → ℝ) → ℝ) x - (if i = k then χ x * g j x else 0))
      (g := fun x => if j = k then χ x * g i x else 0) (iZ.sub iA) iB,
    integral_sub (f := fun x => χ x * ((((tanZ c r F i j : H1B0 c r) : H1Amb c r) (some k) :
      L2B c r) : (Fin n → ℝ) → ℝ) x) (g := fun x => if i = k then χ x * g j x else 0) iZ iA]
  have e1 : ∫ x, (if i = k then χ x * g j x else 0) = if i = k then ∫ x, χ x * g j x else 0 := by
    split_ifs <;> simp
  have e2 : ∫ x, (if j = k then χ x * g i x else 0) = if j = k then ∫ x, χ x * g i x else 0 := by
    split_ifs <;> simp
  rw [e1, e2]
  linarith

end BallData

/-! ### `H²` regularity on the whole ball -/

section H2Ball

variable [NeZero n] (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- The annulus `r/4 < |x - c| < r`. -/
def annB : Set (Fin n → ℝ) := {x | x ∈ euclBall c r ∧ (r / 4) ^ 2 < sqDist c x}

theorem isOpen_annB : IsOpen (annB c r) :=
  (isOpen_euclBall c r).inter (isOpen_lt continuous_const (continuous_sqDist c))

theorem annB_subset : annB c r ⊆ euclBall c r := fun _ hx => hx.1

theorem center_notMem_annB : c ∉ annB c r := fun h => by
  have h2 := h.2
  simp [sqDist] at h2
  nlinarith [sq_nonneg (r / 4)]

theorem memLp_yc_mul {h : (Fin n → ℝ) → ℝ} (hh : MemLp h 2 (volume.restrict (euclBall c r)))
    (i : Fin n) : MemLp (fun x => yc c i x * h x) 2 (volume.restrict (euclBall c r)) :=
  hh.of_le_mul (c := r) (((contDiff_yc c i).continuous.aestronglyMeasurable).mul hh.1)
    ((ae_restrict_mem (measurableSet_euclBall c r)).mono fun x hx => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_coord_sub_le c r i x hx) (norm_nonneg _))

/-- The numerator `Σ_i y_i M_ijk + y_j (y_k f - Σ_i M_kii)` of the radial formula. -/
def radN (F : L2B c r) (j k : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, yc c i x * tanM c r F i j k x +
    yc c j x * (yc c k x * solRhs c r F x - ∑ i, tanM c r F k i i x)

/-- The radial Hessian `radN / |y|²`. -/
def radH (F : L2B c r) (j k : Fin n) (x : Fin n → ℝ) : ℝ := radN c r F j k x / sqDist c x

theorem memLp_radN (F : L2B c r) (j k : Fin n) :
    MemLp (radN c r F j k) 2 (volume.restrict (euclBall c r)) := by
  unfold radN
  refine (memLp_finset_sum _ fun i _ => memLp_yc_mul c r (memLp_tanM c r F i j k) i).add ?_
  refine memLp_yc_mul c r ((memLp_yc_mul c r (memLp_solRhs c r F) k).sub ?_) j
  exact memLp_finset_sum _ fun i _ => memLp_tanM c r F k i i

/-- The radial Hessian is square integrable on the annulus. -/
theorem memLp_radH (F : L2B c r) (j k : Fin n) :
    MemLp (radH c r F j k) 2 (volume.restrict (annB c r)) := by
  have hN : MemLp (radN c r F j k) 2 (volume.restrict (annB c r)) :=
    (memLp_radN c r F j k).mono_measure (Measure.restrict_mono (annB_subset c r) le_rfl)
  have hr0 := hr.out
  refine hN.of_le_mul (c := ((r / 4) ^ 2)⁻¹) ?_ ?_
  · exact (hN.1.aemeasurable.div (continuous_sqDist c).measurable.aemeasurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (isOpen_annB c r).measurableSet] with x hx
    have hs : (r / 4) ^ 2 < sqDist c x := hx.2
    have hs0 : 0 < sqDist c x := lt_trans (by positivity) hs
    rw [radH, norm_div, Real.norm_of_nonneg hs0.le, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) hs.le) (norm_nonneg _)

/-- **The radial formula on the annulus**: `∂_k ∂_j ξ = radH` weakly on `r/4 < |x - c| < r`. -/
theorem radH_weak (F : L2B c r) (j k : Fin n) :
    HasWeakPartialR (annB c r) k (solGrad c r F j) (radH c r F j k) :=
  radial_hessian c (annB_subset c r) (center_notMem_annB c r) (memLp_solGrad c r F)
    (memLp_solRhs c r F) (memLp_tanM c r F) (solGrad_weak c r F)
    (fun χ hχ => solCLM_weak_test c r F hχ) (fun i j k χ hχ => distT_commutator c r F i j k hχ) j k

/-- A cutoff on a ball equal to `1` near a smaller closed ball. -/
theorem exists_cutoff_ball {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    ∃ χ : (Fin n → ℝ) → ℝ, IsTest (euclBall c R) χ ∧ ∃ U : Set (Fin n → ℝ), IsOpen U ∧
      {x | sqDist c x ≤ ρ ^ 2} ⊆ U ∧ ∀ x ∈ U, χ x = 1 := by
  have hK : IsCompact {x : Fin n → ℝ | sqDist c x ≤ ρ ^ 2} :=
    (isCompact_closedBall c ρ).of_isClosed_subset (isClosed_le (continuous_sqDist c)
      continuous_const) fun x hx => mem_closedBall_of_sqDist_le hρ hx
  have hKB : {x : Fin n → ℝ | sqDist c x ≤ ρ ^ 2} ⊆ euclBall c R := fun x hx => by
    show sqDist c x < R ^ 2
    have : ρ ^ 2 < R ^ 2 := by nlinarith
    exact lt_of_le_of_lt hx this
  obtain ⟨χ, hχ, hev, -⟩ := exists_cutoff (isOpen_euclBall c R) hK hKB
  obtain ⟨U, ⟨hUo, hKU⟩, hU⟩ := (hasBasis_nhdsSet _).eventually_iff.mp hev
  exact ⟨χ, hχ, U, hUo, hKU, hU⟩

/-- Uniqueness of real weak derivatives on an open set. -/
theorem HasWeakPartialR.ae_eq {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {i : Fin n}
    {u g g' : (Fin n → ℝ) → ℝ} (h : HasWeakPartialR Ω i u g) (h' : HasWeakPartialR Ω i u g')
    (hg : MemLp g 2 (volume.restrict Ω)) (hg' : MemLp g' 2 (volume.restrict Ω)) :
    ∀ᵐ x, x ∈ Ω → g x = g' x := by
  have := (hasWeakPartialR_iff.mp h).ae_eq hΩ (hasWeakPartialR_iff.mp h')
    (locallyIntegrableOn_of_memLp hg.ofReal) (locallyIntegrableOn_of_memLp hg'.ofReal)
  filter_upwards [this] with x hx hxΩ
  exact_mod_cast hx hxΩ

/-- **`H²` regularity of the weak Neumann problem on a ball** (stage C4b): for every `F ∈ L²(B)`,
each gradient component `∂_jξ` of `ξ = solCLM F` has a weak partial derivative `∂_k∂_jξ ∈ L²(B)`
on the whole open ball `B = B_r(c)`. -/
theorem neumann_H2_ball (F : L2B c r) (j k : Fin n) :
    ∃ H : (Fin n → ℝ) → ℝ, MemLp H 2 (volume.restrict (euclBall c r)) ∧
      HasWeakPartialR (euclBall c r) k (solGrad c r F j) H := by
  have hr0 := hr.out
  set B := euclBall c r
  set V := euclBall c (r / 2)
  set A := annB c r
  -- interior regularity on `V`
  obtain ⟨χ, hχ, U1, -, hKU1, hU1⟩ := exists_cutoff_ball c (ρ := r / 2) (R := r) (by positivity)
    (by linarith)
  have hχV : ∀ x ∈ V, χ x = 1 := fun x hx =>
    hU1 x (hKU1 (show sqDist c x ≤ (r / 2) ^ 2 from le_of_lt hx))
  obtain ⟨G, hGL, hGw, -⟩ := interior_H2 (isOpen_euclBall c r) (memLp_solFn c r F)
    (memLp_solGrad c r F) (memLp_solRhs c r F) (solGrad_weak c r F)
    (fun φ hφ => solCLM_weak_test c r F hφ) hχ (isOpen_euclBall c (r / 2)) hχV
  -- the glued Hessian
  set H : (Fin n → ℝ) → ℝ := V.piecewise (G j k) (radH c r F j k)
  have hVB : V ⊆ B := fun x (hx : sqDist c x < (r / 2) ^ 2) => by
    show sqDist c x < r ^ 2; nlinarith
  have hVcB : Vᶜ ∩ B ⊆ A := fun x hx => ⟨hx.2, by
    have : ¬ sqDist c x < (r / 2) ^ 2 := hx.1
    push_neg at this; nlinarith⟩
  have hHL : MemLp H 2 (volume.restrict B) := by
    refine MemLp.piecewise (measurableSet_euclBall c (r / 2)) ?_ ?_
    · exact ((hGL j k).restrict B).restrict V
    · rw [Measure.restrict_restrict (measurableSet_euclBall c (r / 2)).compl]
      exact (memLp_radH c r F j k).mono_measure (Measure.restrict_mono hVcB le_rfl)
  refine ⟨H, hHL, fun φ hφ => ?_⟩
  -- partition of unity
  obtain ⟨χ0, hχ0, U, hUo, hKU, hU⟩ := exists_cutoff_ball c (ρ := r / 3) (R := r / 2)
    (by positivity) (by linarith)
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have hχ01 : ContDiff ℝ 1 χ0 := hχ0.smooth.of_le (by simp)
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
  have hsplit : ∀ x, pd φ k x = pd φ1 k x + pd φ2 k x := by
    intro x
    have e : φ = fun x => φ1 x + φ2 x := by funext y; simp only [φ1, φ2]; ring
    have h1 : ContDiff ℝ 1 φ1 := hT1.smooth.of_le (by simp)
    have h2 : ContDiff ℝ 1 φ2 := hT2.smooth.of_le (by simp)
    rw [e]
    exact pd_add_real (h1.differentiable one_ne_zero x) (h2.differentiable one_ne_zero x) k
  have hgL := memLp_solGrad c r F j
  have i1 : Integrable fun x => pd φ1 k x * solGrad c r F j x :=
    integrable_test_mul (isTest_pd (hT1.mono hVB) k) hgL
  have i2 : Integrable fun x => pd φ2 k x * solGrad c r F j x :=
    integrable_test_mul (isTest_pd (hT2.mono (annB_subset c r)) k) hgL
  have e1 : ∫ x, pd φ k x * solGrad c r F j x =
      (∫ x, pd φ1 k x * solGrad c r F j x) + ∫ x, pd φ2 k x * solGrad c r F j x := by
    rw [← integral_add i1 i2]; congr 1; funext x; rw [hsplit]; ring
  rw [e1, hGw j k φ1 hT1, radH_weak c r F j k φ2 hT2]
  -- identification of the glued Hessian
  have hEq1 : ∫ x, φ1 x * G j k x = ∫ x, φ1 x * H x := by
    congr 1; funext x
    by_cases hx : x ∈ V
    · simp [H, hx]
    · rw [isTest_vanish hT1 x hx, zero_mul, zero_mul]
  have huniq : ∀ᵐ x, x ∈ A ∩ V → G j k x = radH c r F j k x := by
    have hAV : IsOpen (A ∩ V) := (isOpen_annB c r).inter (isOpen_euclBall c (r / 2))
    have w1 : HasWeakPartialR (A ∩ V) k (solGrad c r F j) (G j k) :=
      (hGw j k).congr_left inter_subset_right fun _ _ => rfl
    have w2 : HasWeakPartialR (A ∩ V) k (solGrad c r F j) (radH c r F j k) :=
      (radH_weak c r F j k).congr_left inter_subset_left fun _ _ => rfl
    exact w1.ae_eq hAV w2 ((hGL j k).restrict _)
      ((memLp_radH c r F j k).mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
  have hEq2 : ∫ x, φ2 x * radH c r F j k x = ∫ x, φ2 x * H x := by
    refine integral_congr_ae ?_
    filter_upwards [huniq] with x hx
    by_cases hxV : x ∈ V
    · by_cases h0 : φ2 x = 0
      · rw [h0, zero_mul, zero_mul]
      · have hxA : x ∈ A := hT2.subset (subset_tsupport φ2 h0)
        simp [H, hxV, hx ⟨hxA, hxV⟩]
    · simp [H, hxV]
  have i3 : Integrable fun x => φ1 x * H x := integrable_test_mul (hT1.mono hVB) hHL
  have i4 : Integrable fun x => φ2 x * H x :=
    integrable_test_mul (hT2.mono (annB_subset c r)) hHL
  rw [hEq1, hEq2, ← neg_add, ← integral_add i3 i4]
  congr 2; funext x; simp only [φ1, φ2]; ring

end H2Ball

end RenewalGeometry.BallAnalysis.BallReg
