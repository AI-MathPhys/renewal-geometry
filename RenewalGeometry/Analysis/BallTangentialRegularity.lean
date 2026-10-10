/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallRotationInvariance

/-!
# Tangential regularity of the weak Neumann problem on a ball (rotation fields)
  (stage C4b, step 1, of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

For `i ≠ j` let `R_ij u = (x_i - c_i) ∂_j u - (x_j - c_j) ∂_i u` be the rotation vector field in
the `(i, j)`-plane about the centre `c` of the ball `B = B_r(c)`; it is tangent to the spheres,
divergence free, and generates the plane rotations `ρ_t = rotAff c (rotM i j t)`.

* `rotM i j t = 1 + (cos t - 1) P + sin t J` (`P = E_ii + E_jj`, `J = E_ji - E_ij`):
  `isOrth_rotM`, `hasDerivAt_rotM_mulVec` (`d/dt O_t v = J O_t v`), `hasDerivAt_comp_flow`
  (`d/dt u(ρ_t x) = (R_ij u)(ρ_t x)`);
* `mulOp` (multiplication by a bounded continuous function on `L²(B)`), `rotDerOp c r i j`
  (`R_ij` on `L²(B)^{1+n}`, `w ↦ (x_i - c_i) w_j - (x_j - c_j) w_i`), `norm_rotDerOp_le`;
* `C¹` estimates: `norm_flow_sub_le` (`‖u ∘ ρ_t - u‖ ≤ t ‖R_ij u‖`) and
  `tendsto_flow_quotient` (`(u ∘ ρ_t - u)/t → R_ij u` in `L²(B)`); their closures on `H¹(B)`:
  `norm_flowB_sub_le_H1B`, `tendsto_flowB_quotient_H1B`;
* `rotDer_antisymm` (**`R_ij` is antisymmetric on `H¹(B)`**: `⟨R y, z₀⟩ = -⟨y₀, R z⟩`, the boundary
  term vanishes because the field is tangent to the sphere);
* `tangential_regularity` (**main result**): for every `F ∈ L²(B)` and `ξ = solCLM F`, the function
  `R_ij ξ` is the function component of a mean-zero `Z ∈ H¹(B)` with
  `Σ_k ‖∂_k Z‖²_{L²(B)} ≤ 4 r² ‖F‖²_{L²(B)}`.  Proof: difference quotients along `ρ_t` and the
  rotation equivariance `solCLM_compB` for smooth data, antisymmetry for the bound, density of
  smooth data.
-/

open MeasureTheory Set Metric Filter Topology Matrix
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

/-! ### Plane rotations -/

section PlaneRot

variable {n : ℕ}

/-- The generator `J = E_ji - E_ij` of rotations in the `(i, j)`-plane (`(J v)_j = v_i`,
`(J v)_i = -v_j`). -/
def genJ (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ := single j i 1 - single i j 1

/-- The orthogonal projection `P = E_ii + E_jj` onto the `(i, j)`-plane. -/
def projP (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ := single i i 1 + single j j 1

/-- The rotation by the angle `t` in the `(i, j)`-plane, `O_t = 1 + (cos t - 1) P + sin t J`. -/
def rotM (i j : Fin n) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + (Real.cos t - 1) • projP i j + Real.sin t • genJ i j

theorem single_mul_single_ne {a b : Fin n} (h : a ≠ b) (x y : Fin n) :
    single x a (1 : ℝ) * single b y 1 = 0 := single_mul_single_of_ne (c := (1 : ℝ)) x a b h 1

theorem genJ_mul_genJ {i j : Fin n} (h : i ≠ j) : genJ i j * genJ i j = -projP i j := by
  simp [genJ, projP, sub_mul, mul_sub, single_mul_single_ne h, single_mul_single_ne h.symm]
  abel

theorem projP_mul_genJ {i j : Fin n} (h : i ≠ j) : projP i j * genJ i j = genJ i j := by
  simp [genJ, projP, add_mul, mul_sub, single_mul_single_ne h, single_mul_single_ne h.symm]

theorem genJ_mul_projP {i j : Fin n} (h : i ≠ j) : genJ i j * projP i j = genJ i j := by
  simp [genJ, projP, mul_add, sub_mul, single_mul_single_ne h, single_mul_single_ne h.symm]
  abel

theorem projP_mul_projP {i j : Fin n} (h : i ≠ j) : projP i j * projP i j = projP i j := by
  simp [projP, add_mul, mul_add, single_mul_single_ne h, single_mul_single_ne h.symm]

theorem genJ_transpose (i j : Fin n) : (genJ i j)ᵀ = -genJ i j := by
  simp [genJ, transpose_sub, transpose_single]

theorem projP_transpose (i j : Fin n) : (projP i j)ᵀ = projP i j := by
  simp [projP, transpose_single]

theorem rotM_mul_transpose {i j : Fin n} (h : i ≠ j) (t : ℝ) :
    rotM i j t * (rotM i j t)ᵀ = 1 := by
  have hs := Real.sin_sq_add_cos_sq t
  simp only [rotM, transpose_add, transpose_one, transpose_smul, genJ_transpose, projP_transpose,
    add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_neg, mul_neg,
    genJ_mul_genJ h, projP_mul_genJ h, genJ_mul_projP h, projP_mul_projP h]
  have : ((Real.cos t - 1) + (Real.cos t - 1) + (Real.cos t - 1) * (Real.cos t - 1) +
      Real.sin t * Real.sin t) = 0 := by nlinarith
  calc _ = (1 : Matrix (Fin n) (Fin n) ℝ) + ((Real.cos t - 1) + (Real.cos t - 1) +
      (Real.cos t - 1) * (Real.cos t - 1) + Real.sin t * Real.sin t) • projP i j := by module
    _ = 1 := by rw [this, zero_smul, add_zero]

/-- Plane rotations are orthogonal. -/
theorem isOrth_rotM {i j : Fin n} (h : i ≠ j) (t : ℝ) : IsOrth (rotM i j t) :=
  ⟨rotM_mul_transpose h t, mul_eq_one_comm.mp (rotM_mul_transpose h t)⟩

theorem rotM_zero (i j : Fin n) : rotM i j 0 = 1 := by simp [rotM]

theorem genJ_mul_rotM {i j : Fin n} (h : i ≠ j) (t : ℝ) :
    genJ i j * rotM i j t = Real.cos t • genJ i j - Real.sin t • projP i j := by
  simp only [rotM, mul_add, mul_one, mul_smul_comm, genJ_mul_projP h, genJ_mul_genJ h, smul_neg]
  module

theorem rotM_mulVec (i j : Fin n) (t : ℝ) (v : Fin n → ℝ) :
    rotM i j t *ᵥ v = v + (Real.cos t - 1) • (projP i j *ᵥ v) + Real.sin t • (genJ i j *ᵥ v) := by
  simp [rotM, add_mulVec, smul_mulVec]

/-- `d/dt (O_t v) = J (O_t v)`. -/
theorem hasDerivAt_rotM_mulVec {i j : Fin n} (h : i ≠ j) (v : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s => rotM i j s *ᵥ v) (genJ i j *ᵥ (rotM i j t *ᵥ v)) t := by
  have e : (fun s => rotM i j s *ᵥ v) =
      fun s => v + (Real.cos s - 1) • (projP i j *ᵥ v) + Real.sin s • (genJ i j *ᵥ v) := by
    funext s; exact rotM_mulVec i j s v
  rw [e, mulVec_mulVec, genJ_mul_rotM h, sub_mulVec, smul_mulVec, smul_mulVec]
  have h1 := (((Real.hasDerivAt_cos t).sub_const 1).smul_const (projP i j *ᵥ v)).const_add v
  have h2 := (Real.hasDerivAt_sin t).smul_const (genJ i j *ᵥ v)
  refine (h1.add h2).congr_deriv ?_
  rw [neg_smul]; abel

/-- `(J v)_k = δ_{kj} v_i - δ_{ki} v_j`. -/
theorem genJ_mulVec (i j : Fin n) (v : Fin n → ℝ) :
    genJ i j *ᵥ v = Pi.single j (v i) - Pi.single i (v j) := by
  simp [genJ, sub_mulVec, single_mulVec, Pi.single]

theorem sum_genJ_mulVec_mul (i j : Fin n) (v a : Fin n → ℝ) :
    ∑ k, (genJ i j *ᵥ v) k * a k = v i * a j - v j * a i := by
  rw [genJ_mulVec]
  simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply]

end PlaneRot

variable {n : ℕ} [NeZero n]

/-! ### The rotation flow and the rotation field -/

section Flow

variable (c : Fin n → ℝ) (i j : Fin n)

/-- The rotation flow `ρ_t(x) = c + O_t (x - c)` in the `(i, j)`-plane about `c`. -/
def flow (t : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := rotAff c (rotM i j t) x

/-- The rotation field `R_ij u = (x_i - c_i) ∂_j u - (x_j - c_j) ∂_i u`. -/
def rotDer (u : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : ℝ :=
  (y i - c i) * pd u j y - (y j - c j) * pd u i y

theorem flow_zero (x : Fin n → ℝ) : flow c i j 0 x = x := by
  simp [flow, rotAff, rotM_zero]

theorem hasDerivAt_flow {i j : Fin n} (h : i ≠ j) (t : ℝ) (x : Fin n → ℝ) :
    HasDerivAt (fun s => flow c i j s x) (genJ i j *ᵥ (flow c i j t x - c)) t := by
  have e : flow c i j t x - c = rotM i j t *ᵥ (x - c) := by simp [flow, rotAff]
  rw [e]
  exact (hasDerivAt_rotM_mulVec h (x - c) t).const_add c

theorem continuous_flow_uncurry {i j : Fin n} :
    Continuous fun p : ℝ × (Fin n → ℝ) => flow c i j p.1 p.2 := by
  have : (fun p : ℝ × (Fin n → ℝ) => flow c i j p.1 p.2) = fun p =>
      c + (p.2 - c + (Real.cos p.1 - 1) • (projP i j *ᵥ (p.2 - c)) +
        Real.sin p.1 • (genJ i j *ᵥ (p.2 - c))) := by
    funext p; simp only [flow, rotAff, rotM_mulVec]
  rw [this]
  have hP : Continuous fun v : Fin n → ℝ => projP i j *ᵥ v :=
    (Matrix.toLin' (projP i j)).continuous_of_finiteDimensional
  have hJ : Continuous fun v : Fin n → ℝ => genJ i j *ᵥ v :=
    (Matrix.toLin' (genJ i j)).continuous_of_finiteDimensional
  fun_prop

/-- Continuity of `x ↦ ρ_{f(x)}(g(x))` (without unification through compositions). -/
theorem continuous_flow_comp {X : Type*} [TopologicalSpace X] {f : X → ℝ} {g : X → Fin n → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => flow c i j (f x) (g x) := by
  have : (fun x => flow c i j (f x) (g x)) = fun x =>
      c + (g x - c + (Real.cos (f x) - 1) • (projP i j *ᵥ (g x - c)) +
        Real.sin (f x) • (genJ i j *ᵥ (g x - c))) := by
    funext x; simp only [flow, rotAff, rotM_mulVec]
  rw [this]
  have hP : Continuous fun v : Fin n → ℝ => projP i j *ᵥ v :=
    (Matrix.toLin' (projP i j)).continuous_of_finiteDimensional
  have hJ : Continuous fun v : Fin n → ℝ => genJ i j *ᵥ v :=
    (Matrix.toLin' (genJ i j)).continuous_of_finiteDimensional
  have h1 : Continuous fun x => g x - c := hg.sub continuous_const
  exact continuous_const.add ((h1.add (((Real.continuous_cos.comp hf).sub continuous_const).smul
    (hP.comp h1))).add ((Real.continuous_sin.comp hf).smul (hJ.comp h1)))

/-- **The derivative along the rotation flow**: `d/dt u(ρ_t x) = (R_ij u)(ρ_t x)`. -/
theorem hasDerivAt_comp_flow {i j : Fin n} (h : i ≠ j) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (t : ℝ) (x : Fin n → ℝ) :
    HasDerivAt (fun s => u (flow c i j s x)) (rotDer c i j u (flow c i j t x)) t := by
  have hd := ((hu.differentiable one_ne_zero) (flow c i j t x)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_flow c h t x)
  refine hd.congr_deriv ?_
  rw [fderiv_apply_eq_sum_pd, rotDer]
  rw [sum_genJ_mulVec_mul]
  simp only [Pi.sub_apply]

theorem continuous_rotDer {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (rotDer c i j u) := by
  unfold rotDer
  have h1 := continuous_pd hu i
  have h2 := continuous_pd hu j
  fun_prop

theorem sqDist_flow {i j : Fin n} (h : i ≠ j) (t : ℝ) (x : Fin n → ℝ) :
    sqDist c (flow c i j t x) = sqDist c x := sqDist_rotAff c (isOrth_rotM h t) x

end Flow

/-! ### Multiplication operators and the rotation field on `L²(B)^{1+n}` -/

section MulOp

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

theorem memLp_mul_bdd {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x ∈ euclBall c r, |g x| ≤ M) (f : L2B c r) :
    MemLp (fun x => g x * f x) 2 (volume.restrict (euclBall c r)) :=
  (Lp.memLp f).of_le_mul (c := M) (hg.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    ((ae_restrict_mem (measurableSet_euclBall c r)).mono fun x hx => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _))

/-- Multiplication by a continuous function bounded on the ball, as a linear map of `L²(B)`. -/
def mulLinB {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x ∈ euclBall c r, |g x| ≤ M) : L2B c r →ₗ[ℝ] L2B c r where
  toFun f := (memLp_mul_bdd c r hg hM f).toLp _
  map_add' f₁ f₂ := by
    rw [← MemLp.toLp_add]
    refine (MemLp.toLp_eq_toLp_iff _ _).mpr ?_
    filter_upwards [Lp.coeFn_add f₁ f₂] with x hx
    simp only [hx, Pi.add_apply]; ring
  map_smul' a f := by
    rw [← MemLp.toLp_const_smul]
    refine (MemLp.toLp_eq_toLp_iff _ _).mpr ?_
    filter_upwards [Lp.coeFn_smul a f] with x hx
    simp only [hx, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem norm_mulLinB_le {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x ∈ euclBall c r, |g x| ≤ M) (f : L2B c r) :
    ‖mulLinB c r hg hM f‖ ≤ M * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [(memLp_mul_bdd c r hg hM f).coeFn_toLp,
    ae_restrict_mem (measurableSet_euclBall c r)] with x h1 hx
  show ‖((memLp_mul_bdd c r hg hM f).toLp _ : (Fin n → ℝ) → ℝ) x‖ ≤ M * ‖f x‖
  rw [h1, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)

/-- Multiplication by a bounded continuous function, as a continuous linear map of `L²(B)`. -/
def mulOp {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x ∈ euclBall c r, |g x| ≤ M) : L2B c r →L[ℝ] L2B c r :=
  (mulLinB c r hg hM).mkContinuous M (norm_mulLinB_le c r hg hM)

theorem coeFn_mulOp {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x ∈ euclBall c r, |g x| ≤ M) (f : L2B c r) :
    (mulOp c r hg hM f : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      fun x => g x * f x :=
  (memLp_mul_bdd c r hg hM f).coeFn_toLp

theorem norm_mulOp_le {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x ∈ euclBall c r, |g x| ≤ M) (f : L2B c r) : ‖mulOp c r hg hM f‖ ≤ M * ‖f‖ :=
  norm_mulLinB_le c r hg hM f

theorem continuous_coord_sub (k : Fin n) : Continuous fun y : Fin n → ℝ => y k - c k :=
  (continuous_apply k).sub continuous_const

theorem abs_coord_sub_le (k : Fin n) : ∀ y ∈ euclBall c r, |y k - c k| ≤ r := by
  intro y hy
  have h1 := sq_le_sqDist c y k
  have h2 : sqDist c y < r ^ 2 := hy
  exact abs_le_of_sq_le_sq' (by nlinarith) hr.out.le |> fun h => abs_le.mpr h

/-- **The rotation field on `L²(B)^{1+n}`**: `R_ij w = (x_i - c_i) w_j - (x_j - c_j) w_i`. -/
def rotDerOp (i j : Fin n) : H1Amb c r →L[ℝ] L2B c r :=
  (mulOp c r (continuous_coord_sub c i) (abs_coord_sub_le c r i)).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) (some j)) -
    (mulOp c r (continuous_coord_sub c j) (abs_coord_sub_le c r j)).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) (some i))

theorem coeFn_rotDerOp (i j : Fin n) (w : H1Amb c r) :
    (rotDerOp c r i j w : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      fun y => (y i - c i) * (w (some j) : (Fin n → ℝ) → ℝ) y -
        (y j - c j) * (w (some i) : (Fin n → ℝ) → ℝ) y := by
  have h := Lp.coeFn_sub
    ((mulOp c r (continuous_coord_sub c i) (abs_coord_sub_le c r i)) (w (some j)))
    ((mulOp c r (continuous_coord_sub c j) (abs_coord_sub_le c r j)) (w (some i)))
  filter_upwards [h, coeFn_mulOp c r (continuous_coord_sub c i) (abs_coord_sub_le c r i)
    (w (some j)), coeFn_mulOp c r (continuous_coord_sub c j) (abs_coord_sub_le c r j)
    (w (some i))] with y h1 h2 h3
  show ((rotDerOp c r i j w : L2B c r) : (Fin n → ℝ) → ℝ) y = _
  have : rotDerOp c r i j w =
      (mulOp c r (continuous_coord_sub c i) (abs_coord_sub_le c r i)) (w (some j)) -
      (mulOp c r (continuous_coord_sub c j) (abs_coord_sub_le c r j)) (w (some i)) := rfl
  rw [this, h1, Pi.sub_apply, h2, h3]

theorem norm_rotDerOp_le (i j : Fin n) (w : H1Amb c r) :
    ‖rotDerOp c r i j w‖ ≤ r * (‖w (some i)‖ + ‖w (some j)‖) := by
  have : rotDerOp c r i j w =
      (mulOp c r (continuous_coord_sub c i) (abs_coord_sub_le c r i)) (w (some j)) -
      (mulOp c r (continuous_coord_sub c j) (abs_coord_sub_le c r j)) (w (some i)) := rfl
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_mulOp_le c r (continuous_coord_sub c i) (abs_coord_sub_le c r i) (w (some j))
  have h2 := norm_mulOp_le c r (continuous_coord_sub c j) (abs_coord_sub_le c r j) (w (some i))
  linarith

theorem norm_rotDerOp_le' (i j : Fin n) (w : H1Amb c r) :
    ‖rotDerOp c r i j w‖ ≤ 2 * r * ‖w‖ := by
  refine (norm_rotDerOp_le c r i j w).trans ?_
  have h1 := PiLp.norm_apply_le w (some i)
  have h2 := PiLp.norm_apply_le w (some j)
  have := hr.out
  nlinarith

/-- On `C¹` graphs, `rotDerOp` is the classical rotation field. -/
theorem rotDerOp_graphC1 (i j : Fin n) (u : C1fun (n := n)) :
    rotDerOp c r i j (graphC1 c r u) =
      (memLp_euclBall_of_continuous c hr.out.le (continuous_rotDer c i j u.2) 2).toLp
        (rotDer c i j u) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_rotDerOp c r i j (graphC1 c r u),
    (memLp_euclBall_of_continuous c hr.out.le (continuous_rotDer c i j u.2) 2).coeFn_toLp,
    (memLp_ball_pd_of_C1 c r u.2 i).coeFn_toLp, (memLp_ball_pd_of_C1 c r u.2 j).coeFn_toLp]
    with y h1 h2 h3 h4
  rw [h1, h2, graphC1_some, graphC1_some, h3, h4]
  rfl

end MulOp

/-! ### `C¹` estimates along the rotation flow -/

section C1Est

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

theorem measurableEmbedding_rotAff {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) :
    MeasurableEmbedding (rotAff c O) :=
  (Homeomorph.mk ⟨rotAff c O, rotAff c Oᵀ, rotAff_rotAff_transpose c hO,
    rotAff_transpose_rotAff c hO⟩ (continuous_rotAff c O)
    (continuous_rotAff c Oᵀ)).measurableEmbedding

/-- Rotation invariance of integrals over the ball. -/
theorem setIntegral_comp_rotAff {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O)
    (g : (Fin n → ℝ) → ℝ) :
    ∫ x in euclBall c r, g (rotAff c O x) = ∫ x in euclBall c r, g x :=
  (measurePreserving_rotAff_ball c r hO).integral_comp (measurableEmbedding_rotAff c hO) g

theorem continuous_rotDer_flow {i j : Fin n} {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous fun p : ℝ × (Fin n → ℝ) => rotDer c i j u (flow c i j p.1 p.2) :=
  (continuous_rotDer c i j hu).comp (continuous_flow_comp c i j continuous_fst continuous_snd)

theorem continuous_rotDer_flow_comp {i j : Fin n} {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} {g : X → Fin n → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => rotDer c i j u (flow c i j (f x) (g x)) :=
  (continuous_rotDer c i j hu).comp (continuous_flow_comp c i j hf hg)

theorem continuous_comp_flow {i j : Fin n} {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (t : ℝ) :
    Continuous fun x => u (flow c i j t x) :=
  hu.continuous.comp (continuous_rotAff c (rotM i j t))

/-- **Fundamental theorem of calculus along the flow**:
`u(ρ_t x) - u(x) = ∫₀¹ t (R_ij u)(ρ_{tσ} x) dσ`. -/
theorem comp_flow_sub_eq {i j : Fin n} (h : i ≠ j) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (t : ℝ) (x : Fin n → ℝ) :
    u (flow c i j t x) - u x =
      ∫ σ in (0 : ℝ)..1, t * rotDer c i j u (flow c i j (t * σ) x) := by
  have hd : ∀ σ : ℝ, HasDerivAt (fun σ => u (flow c i j (t * σ) x))
      (t * rotDer c i j u (flow c i j (t * σ) x)) σ := by
    intro σ
    have := (hasDerivAt_comp_flow c h hu (t * σ) x).comp σ ((hasDerivAt_id σ).const_mul t)
    refine this.congr_deriv ?_
    simp [mul_comm]
  have hcont : Continuous fun σ : ℝ => t * rotDer c i j u (flow c i j (t * σ) x) :=
    continuous_const.mul (continuous_rotDer_flow_comp c hu (continuous_const.mul continuous_id)
      continuous_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hd σ)
    (hcont.intervalIntegrable 0 1)]
  simp [flow_zero]

set_option maxHeartbeats 1000000 in
/-- **The `C¹` difference estimate**: `∫_B (u(ρ_t x) - u(x))² ≤ t² ∫_B (R_ij u)²`. -/
theorem integral_sq_flow_sub_le {i j : Fin n} (h : i ≠ j) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (t : ℝ) :
    ∫ x in euclBall c r, (u (flow c i j t x) - u x) ^ 2 ≤
      t ^ 2 * ∫ x in euclBall c r, rotDer c i j u x ^ 2 := by
  obtain ⟨G, hG⟩ : ∃ G : ℝ → (Fin n → ℝ) → ℝ,
      G = fun σ x => rotDer c i j u (flow c i j (t * σ) x) ^ 2 := ⟨_, rfl⟩
  have hGc : Continuous (Function.uncurry G) := by
    rw [hG]
    exact (continuous_rotDer_flow_comp c hu (continuous_const.mul continuous_fst)
      continuous_snd).pow 2
  have hpt : ∀ x, (u (flow c i j t x) - u x) ^ 2 ≤ t ^ 2 * ∫ σ in (0 : ℝ)..1, G σ x := by
    intro x
    rw [comp_flow_sub_eq c h hu t x]
    have hc : Continuous fun σ : ℝ => t * rotDer c i j u (flow c i j (t * σ) x) :=
      continuous_const.mul (continuous_rotDer_flow_comp c hu (continuous_const.mul continuous_id)
        continuous_const)
    refine (sq_integral_le_integral_sq hc).trans (le_of_eq ?_)
    rw [← intervalIntegral.integral_const_mul, hG]
    congr 1; funext σ; ring
  have hinner : ∀ σ, ∫ x in euclBall c r, G σ x = ∫ x in euclBall c r, rotDer c i j u x ^ 2 := by
    intro σ
    rw [hG]
    exact setIntegral_comp_rotAff c r (isOrth_rotM h (t * σ)) (fun y => rotDer c i j u y ^ 2)
  have hcx : Continuous fun x => ∫ σ in (0 : ℝ)..1, G σ x :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x σ => G σ x) (hGc.comp continuous_swap) 0 1
  have hr0 := hr.out
  have hswap : ∫ x in euclBall c r, ∫ σ in (0 : ℝ)..1, G σ x =
      ∫ σ in Icc (0 : ℝ) 1, ∫ x in euclBall c r, G σ x := by
    simp only [intervalIntegral_eq_Icc]
    exact integral_swap_of_continuous (measurableSet_euclBall c r) measurableSet_Icc
      (volume_euclBall_lt_top c hr0.le) (by simp) (isCompact_closedBall c r) isCompact_Icc
      (euclBall_subset_closedBall c hr0.le) subset_rfl (F := fun x σ => G σ x)
      (hGc.comp continuous_swap)
  have hmono : ∫ x in euclBall c r, (u (flow c i j t x) - u x) ^ 2 ≤
      ∫ x in euclBall c r, t ^ 2 * ∫ σ in (0 : ℝ)..1, G σ x := by
    refine setIntegral_mono_on ?_ ?_ (measurableSet_euclBall c r) fun x _ => hpt x
    · exact integrableOn_euclBall hr0.le (((continuous_comp_flow c hu t).sub hu.continuous).pow 2)
    · exact integrableOn_euclBall hr0.le (continuous_const.mul hcx)
  rw [integral_const_mul, hswap] at hmono
  refine hmono.trans (le_of_eq ?_)
  congr 1
  rw [setIntegral_congr_fun measurableSet_Icc (fun σ _ => hinner σ), setIntegral_const]
  simp

/-- The rotated function as an element of `L²(B)`. -/
theorem memLp_comp_flow {i j : Fin n} {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (t : ℝ) :
    MemLp (fun x => u (flow c i j t x)) 2 (volume.restrict (euclBall c r)) :=
  memLp_euclBall_of_continuous c hr.out.le (continuous_comp_flow c hu t) 2

theorem memLp_rotDer {i j : Fin n} {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) :
    MemLp (rotDer c i j u) 2 (volume.restrict (euclBall c r)) :=
  memLp_euclBall_of_continuous c hr.out.le (continuous_rotDer c i j hu) 2

/-- `L²` form of the difference estimate: `‖u ∘ ρ_t - u‖ ≤ |t| ‖R_ij u‖`. -/
theorem norm_flow_sub_le {i j : Fin n} (h : i ≠ j) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (t : ℝ) :
    ‖(memLp_comp_flow c r hu t (i := i) (j := j)).toLp _ - (memLp_ball_of_C1 c r hu).toLp u‖ ≤
      |t| * ‖(memLp_rotDer c r hu (i := i) (j := j)).toLp (rotDer c i j u)‖ := by
  rw [← MemLp.toLp_sub]
  have h1 := norm_sq_toLp c r ((memLp_comp_flow c r hu t (i := i) (j := j)).sub
    (memLp_ball_of_C1 c r hu))
  have h2 := norm_sq_toLp c r (memLp_rotDer c r hu (i := i) (j := j))
  have h3 := integral_sq_flow_sub_le c r h hu t
  simp only [Pi.sub_apply] at h1
  rw [← h1, ← h2] at h3
  have h4 : ‖((memLp_comp_flow c r hu t (i := i) (j := j)).sub
      (memLp_ball_of_C1 c r hu)).toLp _‖ ^ 2 ≤
      (|t| * ‖(memLp_rotDer c r hu (i := i) (j := j)).toLp (rotDer c i j u)‖) ^ 2 := by
    rw [mul_pow, sq_abs]; exact h3
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4

/-- The sequence of times `t_m = 1/(m+1) → 0⁺`. -/
def tseq (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

theorem tseq_pos (m : ℕ) : 0 < tseq m := by unfold tseq; positivity

theorem tseq_le_one (m : ℕ) : tseq m ≤ 1 := by
  unfold tseq
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem tendsto_tseq : Tendsto tseq atTop (𝓝 0) := by
  unfold tseq
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Convergence of the difference quotients for `C¹` functions**:
`(u ∘ ρ_t - u)/t → R_ij u` in `L²(B)` as `t = t_m → 0⁺`. -/
theorem tendsto_flow_quotient {i j : Fin n} (h : i ≠ j) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) :
    Tendsto (fun m => ‖(tseq m)⁻¹ • ((memLp_comp_flow c r hu (tseq m) (i := i) (j := j)).toLp _ -
        (memLp_ball_of_C1 c r hu).toLp u) -
        (memLp_rotDer c r hu (i := i) (j := j)).toLp (rotDer c i j u)‖) atTop (𝓝 0) := by
  have hr0 := hr.out
  set Gf : ℝ × (Fin n → ℝ) → ℝ := fun p => rotDer c i j u (flow c i j p.1 p.2)
  have hGc : Continuous Gf := continuous_rotDer_flow c hu
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall c r) :=
    isCompact_Icc.prod (isCompact_closedBall c r)
  have huc := hK.uniformContinuousOn_of_continuous hGc.continuousOn
  rw [Metric.tendsto_atTop]
  intro ε hε
  set V := volB c r
  have hV : 0 < V := volB_pos c r
  set ε' := ε / (2 * (Real.sqrt V + 1))
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.mp huc ε' hε'
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp tendsto_tseq) δ hδ
  refine ⟨M, fun m hm => ?_⟩
  set t := tseq m
  have ht0 : 0 < t := tseq_pos m
  have htδ : t < δ := by
    have := hM m hm; rw [Real.dist_eq, sub_zero, abs_of_pos ht0] at this; exact this
  have ht1 : t ≤ 1 := tseq_le_one m
  -- pointwise bound
  have hpt : ∀ x ∈ euclBall c r,
      |t⁻¹ * (u (flow c i j t x) - u x) - rotDer c i j u x| ≤ ε' := by
    intro x hx
    have hxK : x ∈ closedBall c r := euclBall_subset_closedBall c hr0.le hx
    rw [comp_flow_sub_eq c h hu t x, ← intervalIntegral.integral_const_mul]
    have e : ∫ σ in (0 : ℝ)..1, t⁻¹ * (t * rotDer c i j u (flow c i j (t * σ) x)) =
        ∫ σ in (0 : ℝ)..1, Gf (t * σ, x) := by
      congr 1; funext σ; simp only [Gf]; field_simp
    have e2 : rotDer c i j u x = ∫ σ in (0 : ℝ)..1, Gf (0, x) := by
      simp [Gf, flow_zero]
    rw [e, e2, ← intervalIntegral.integral_sub]
    · have hb : ∀ σ ∈ Set.uIoc (0 : ℝ) 1, ‖Gf (t * σ, x) - Gf (0, x)‖ ≤ ε' := by
        intro σ hσ
        rw [uIoc_of_le zero_le_one] at hσ
        have hσ' : σ ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hσ
        have hmem1 : (t * σ, x) ∈ Icc (0 : ℝ) 1 ×ˢ closedBall c r :=
          ⟨⟨by nlinarith [hσ'.1], by nlinarith [hσ'.2]⟩, hxK⟩
        have hmem2 : ((0 : ℝ), x) ∈ Icc (0 : ℝ) 1 ×ˢ closedBall c r :=
          ⟨⟨le_rfl, zero_le_one⟩, hxK⟩
        have hd : dist (t * σ, x) ((0 : ℝ), x) < δ := by
          rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
          rw [max_eq_left (abs_nonneg _), abs_of_nonneg (by nlinarith [hσ'.1])]
          nlinarith [hσ'.2]
        have := hδε _ hmem1 _ hmem2 hd
        rw [Real.dist_eq] at this
        rw [Real.norm_eq_abs]; exact this.le
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb
      simpa using this
    · exact ((continuous_rotDer_flow_comp c hu (continuous_const.mul continuous_id)
        continuous_const)).intervalIntegrable 0 1
    · exact intervalIntegrable_const
  -- integrate
  have hmem := (((memLp_comp_flow c r hu t (i := i) (j := j)).sub
    (memLp_ball_of_C1 c r hu)).const_smul t⁻¹).sub (memLp_rotDer c r hu (i := i) (j := j))
  have heq : t⁻¹ • ((memLp_comp_flow c r hu t (i := i) (j := j)).toLp _ -
      (memLp_ball_of_C1 c r hu).toLp u) -
      (memLp_rotDer c r hu (i := i) (j := j)).toLp (rotDer c i j u) = hmem.toLp _ := by
    rw [← MemLp.toLp_sub, ← MemLp.toLp_const_smul, ← MemLp.toLp_sub]
  rw [dist_zero_right, norm_norm, heq]
  have hsq := norm_sq_toLp c r hmem
  have hint : ∫ x in euclBall c r, (((t⁻¹ • ((fun x => u (flow c i j t x)) - u)) -
      rotDer c i j u) x) ^ 2 ≤ ∫ x in euclBall c r, ε' ^ 2 := by
    refine setIntegral_mono_on ?_ (integrableOn_const (volume_euclBall_lt_top c hr0.le).ne)
      (measurableSet_euclBall c r) fun x hx => ?_
    · exact integrableOn_euclBall hr0.le
        (((continuous_const.smul ((continuous_comp_flow c hu t).sub hu.continuous)).sub
          (continuous_rotDer c i j hu)).pow 2)
    · have := hpt x hx
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have h2 := abs_le.mp this
      nlinarith [h2.1, h2.2]
  rw [setIntegral_const, smul_eq_mul] at hint
  have hVr : volume.real (euclBall c r) = V := by
    simp [V, volB, measureReal_def]
  rw [hVr, ← hsq] at hint
  have hnn := norm_nonneg (hmem.toLp _)
  have h1 : ‖hmem.toLp _‖ ≤ ε' * Real.sqrt V := by
    rw [← Real.sqrt_sq hnn, ← Real.sqrt_sq hε'.le, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith)
  calc ‖hmem.toLp _‖ ≤ ε' * Real.sqrt V := h1
    _ < ε := by
        have hs := Real.sqrt_nonneg V
        rw [show ε' = ε / (2 * (Real.sqrt V + 1)) from rfl, div_mul_eq_mul_div,
          div_lt_iff₀ (by positivity)]
        nlinarith

end C1Est

/-! ### Closure on `H¹(B)` and antisymmetry -/

section H1Ext

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- The rotation flow acting on `L²(B)`. -/
def flowB {i j : Fin n} (h : i ≠ j) (t : ℝ) : L2B c r →L[ℝ] L2B c r :=
  compB c r (isOrth_rotM h t)

theorem flowB_toLp {i j : Fin n} (h : i ≠ j) (t : ℝ) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) :
    flowB c r h t ((memLp_ball_of_C1 c r hu).toLp u) =
      (memLp_comp_flow c r hu t (i := i) (j := j)).toLp _ := rfl

/-- The difference estimate on `H¹(B)`: `‖w₀ ∘ ρ_t - w₀‖ ≤ t ‖R_ij w‖` for `t ≥ 0`. -/
theorem norm_flowB_sub_le_H1B {i j : Fin n} (h : i ≠ j) {t : ℝ} (ht : 0 ≤ t) :
    ∀ w ∈ H1B c r, ‖flowB c r h t (w none) - w none‖ ≤ t * ‖rotDerOp c r i j w‖ := by
  refine H1B_induction c r ?_ fun u => ?_
  · have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none).continuous
    exact isClosed_le (((flowB c r h t).continuous.comp hp).sub hp).norm
      (continuous_const.mul (rotDerOp c r i j).continuous.norm)
  · rw [graphC1_none, flowB_toLp c r h t u.2, rotDerOp_graphC1]
    have := norm_flow_sub_le c r h u.2 t
    rwa [abs_of_nonneg ht] at this

/-- The difference-quotient defect `Q_t x = (x₀ ∘ ρ_t - x₀)/t - R_ij x`. -/
def quotDefect {i j : Fin n} (h : i ≠ j) (t : ℝ) : H1Amb c r →L[ℝ] L2B c r :=
  t⁻¹ • ((flowB c r h t).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none) -
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none) - rotDerOp c r i j

theorem quotDefect_apply {i j : Fin n} (h : i ≠ j) (t : ℝ) (x : H1Amb c r) :
    quotDefect c r h t x = t⁻¹ • (flowB c r h t (x none) - x none) - rotDerOp c r i j x := rfl

theorem norm_quotDefect_le {i j : Fin n} (h : i ≠ j) {t : ℝ} (ht : 0 < t) {x : H1Amb c r}
    (hx : x ∈ H1B c r) : ‖quotDefect c r h t x‖ ≤ 4 * r * ‖x‖ := by
  rw [quotDefect_apply]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
  have h1 := norm_flowB_sub_le_H1B c r h ht.le x hx
  have h2 := norm_rotDerOp_le' c r i j x
  have h3 : t⁻¹ * ‖flowB c r h t (x none) - x none‖ ≤ ‖rotDerOp c r i j x‖ := by
    rw [inv_mul_le_iff₀ ht]; exact h1
  linarith

/-- **Convergence of the difference quotients on `H¹(B)`**:
`(w₀ ∘ ρ_t - w₀)/t → R_ij w` in `L²(B)` for every `w ∈ H¹(B)` (`t = t_m → 0⁺`). -/
theorem tendsto_flowB_quotient_H1B {i j : Fin n} (h : i ≠ j) {w : H1Amb c r}
    (hw : w ∈ H1B c r) :
    Tendsto (fun m => (tseq m)⁻¹ • (flowB c r h (tseq m) (w none) - w none)) atTop
      (𝓝 (rotDerOp c r i j w)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  have hr0 := hr.out
  have hw' : w ∈ closure ((LinearMap.range (graphLin c r) : Submodule ℝ (H1Amb c r)) :
      Set (H1Amb c r)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hw
  obtain ⟨b, ⟨u, rfl⟩, hb⟩ := Metric.mem_closure_iff.mp hw' (ε / (8 * r + 1)) (by positivity)
  have hg := tendsto_flow_quotient c r h u.2
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hg) (ε / 2) (by positivity)
  refine ⟨M, fun m hm => ?_⟩
  rw [dist_zero_right, norm_norm]
  have hgm := hM m hm
  rw [dist_zero_right, norm_norm] at hgm
  have hgraph : quotDefect c r h (tseq m) (graphLin c r u) =
      (tseq m)⁻¹ • ((memLp_comp_flow c r u.2 (tseq m) (i := i) (j := j)).toLp _ -
        (memLp_ball_of_C1 c r u.2).toLp u) -
        (memLp_rotDer c r u.2 (i := i) (j := j)).toLp (rotDer c i j u) := by
    rw [quotDefect_apply]
    show (tseq m)⁻¹ • (flowB c r h (tseq m) (graphC1 c r u none) - graphC1 c r u none) -
      rotDerOp c r i j (graphC1 c r u) = _
    rw [graphC1_none, flowB_toLp c r h (tseq m) u.2, rotDerOp_graphC1]
  have hsplit : (tseq m)⁻¹ • (flowB c r h (tseq m) (w none) - w none) - rotDerOp c r i j w =
      quotDefect c r h (tseq m) (w - graphLin c r u) + quotDefect c r h (tseq m) (graphLin c r u) := by
    rw [← map_add, sub_add_cancel, quotDefect_apply]
  rw [hsplit]
  have hmem : w - graphLin c r u ∈ H1B c r := (H1B c r).sub_mem hw (graphC1_mem c r u)
  have h1 := norm_quotDefect_le c r h (tseq_pos m) hmem
  have h2 : ‖w - graphLin c r u‖ < ε / (8 * r + 1) := by rw [← dist_eq_norm]; exact hb
  rw [hgraph] at *
  calc ‖quotDefect c r h (tseq m) (w - graphLin c r u) + _‖
      ≤ ‖quotDefect c r h (tseq m) (w - graphLin c r u)‖ + ‖(tseq m)⁻¹ •
          ((memLp_comp_flow c r u.2 (tseq m) (i := i) (j := j)).toLp _ -
          (memLp_ball_of_C1 c r u.2).toLp u) -
          (memLp_rotDer c r u.2 (i := i) (j := j)).toLp (rotDer c i j u)‖ := norm_add_le _ _
    _ < 4 * r * (ε / (8 * r + 1)) + ε / 2 := by
        refine add_lt_add_of_le_of_lt (h1.trans ?_) hgm
        exact mul_le_mul_of_nonneg_left h2.le (by positivity)
    _ ≤ ε := by
        have : 4 * r * (ε / (8 * r + 1)) ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

/-- **Antisymmetry of the rotation field for `C¹` functions** (no boundary term: the field is
tangent to the sphere). -/
theorem integral_rotDer_mul_add {i j : Fin n} (h : i ≠ j) {u v : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    (∫ y in euclBall c r, rotDer c i j u y * v y) +
      ∫ y in euclBall c r, u y * rotDer c i j v y = 0 := by
  have hr0 := hr.out
  have huv : ContDiff ℝ 1 (fun y => u y * v y) := hu.mul hv
  have hci : ContDiff ℝ 1 (fun y : Fin n → ℝ => y i - c i) :=
    ((contDiff_apply ℝ ℝ i).sub contDiff_const)
  have hcj : ContDiff ℝ 1 (fun y : Fin n → ℝ => y j - c j) :=
    ((contDiff_apply ℝ ℝ j).sub contDiff_const)
  have hpt : ∀ y, rotDer c i j u y * v y + u y * rotDer c i j v y =
      (y i - c i) * pd (fun y => u y * v y) j y - (y j - c j) * pd (fun y => u y * v y) i y := by
    intro y
    rw [pd_mul_real ((hu.differentiable one_ne_zero) y) ((hv.differentiable one_ne_zero) y),
      pd_mul_real ((hu.differentiable one_ne_zero) y) ((hv.differentiable one_ne_zero) y)]
    simp only [rotDer]; ring
  have hint := fun (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) =>
    integrableOn_euclBall (c := c) hr0.le hg
  have i1 : IntegrableOn (fun y => rotDer c i j u y * v y) (euclBall c r) :=
    hint _ ((continuous_rotDer c i j hu).mul hv.continuous)
  have i2 : IntegrableOn (fun y => u y * rotDer c i j v y) (euclBall c r) :=
    hint _ (hu.continuous.mul (continuous_rotDer c i j hv))
  have i3 : IntegrableOn (fun y => (y i - c i) * pd (fun y => u y * v y) j y) (euclBall c r) :=
    hint _ (hci.continuous.mul (continuous_pd huv j))
  have i4 : IntegrableOn (fun y => (y j - c j) * pd (fun y => u y * v y) i y) (euclBall c r) :=
    hint _ (hcj.continuous.mul (continuous_pd huv i))
  rw [← integral_add i1 i2]
  simp only [hpt]
  rw [integral_sub i3 i4]
  rw [integral_mul_pd_ball c hr0 hci huv j, integral_mul_pd_ball c hr0 hcj huv i]
  have e1 : ∀ y, pd (fun y : Fin n → ℝ => y i - c i) j y = 0 := fun y => by
    rw [pd_coord_sub]; simp [h]
  have e2 : ∀ y, pd (fun y : Fin n → ℝ => y j - c j) i y = 0 := fun y => by
    rw [pd_coord_sub]; simp [h.symm]
  simp only [e1, e2, zero_mul, integral_zero, sub_zero]
  have e3 : ∀ w : Fin n → ℝ, ((c + r • w) i - c i) * (u (c + r • w) * v (c + r • w)) * w j =
      ((c + r • w) j - c j) * (u (c + r • w) * v (c + r • w)) * w i := fun w => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]; ring
  simp only [e3, sub_self]

/-- **Antisymmetry of `R_ij` on `H¹(B)`**: `⟨R_ij y, z₀⟩ = -⟨y₀, R_ij z⟩`. -/
theorem rotDerOp_antisymm {i j : Fin n} (h : i ≠ j) :
    ∀ y ∈ H1B c r, ∀ z ∈ H1B c r,
      ⟪rotDerOp c r i j y, z none⟫ = -⟪y none, rotDerOp c r i j z⟫ := by
  have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none).continuous
  have hR := (rotDerOp c r i j).continuous
  -- first for `z` a graph
  have hgraph : ∀ v : C1fun (n := n), ∀ y ∈ H1B c r,
      ⟪rotDerOp c r i j y, graphC1 c r v none⟫ = -⟪y none, rotDerOp c r i j (graphC1 c r v)⟫ := by
    intro v
    refine H1B_induction c r ?_ fun u => ?_
    · exact isClosed_eq (hR.inner continuous_const) (hp.inner continuous_const).neg
    · rw [rotDerOp_graphC1, rotDerOp_graphC1, graphC1_none, graphC1_none, inner_toLp_toLp,
        inner_toLp_toLp]
      have := integral_rotDer_mul_add c r h u.2 v.2
      linarith
  intro y hy
  refine H1B_induction c r ?_ fun v => hgraph v y hy
  exact isClosed_eq (continuous_const.inner hp) (continuous_const.inner hR).neg

end H1Ext

/-! ### Tangential regularity of the Neumann solution -/

section Main

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- The Dirichlet energy of an element of `H¹₀(B)`. -/
theorem dirForm_self (x : H1B0 c r) :
    dirForm c r x x = ∑ k, ‖(x : H1Amb c r) (some k)‖ ^ 2 := by
  rw [dirForm_apply]
  exact Finset.sum_congr rfl fun k _ => real_inner_self_eq_norm_sq _

/-- The full norm of a mean-zero element of `H¹(B)` is controlled by its energy (Poincaré). -/
theorem norm_sq_H1B0_le (x : H1B0 c r) :
    ‖x‖ ^ 2 ≤ (2 ^ (n + 1) * r ^ 2 + 1) * ∑ k, ‖(x : H1Amb c r) (some k)‖ ^ 2 := by
  have hPW := poincare_H1B c r (x : H1Amb c r) x.2.1
  rw [show meanCLM c r (x : H1Amb c r) = 0 from x.2.2, mul_zero, zero_smul, sub_zero] at hPW
  have hn : ‖x‖ ^ 2 = ‖(x : H1Amb c r) none‖ ^ 2 + ∑ k, ‖(x : H1Amb c r) (some k)‖ ^ 2 := by
    rw [← norm_sq_H1Amb]; rfl
  rw [hn]; linarith

theorem loadCLM_apply (F : L2B c r) (y : H1B0 c r) :
    loadCLM c r F y = -⟪F, (y : H1Amb c r) none⟫ := rfl

/-- `S ≤ K (a + b)` with `a², b² ≤ S` forces `S ≤ 4 K²`. -/
theorem energy_le_of_le_mul_sum {S K a b : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haS : a ^ 2 ≤ S) (hbS : b ^ 2 ≤ S) (h : S ≤ K * (a + b)) : S ≤ 4 * K ^ 2 := by
  have hS : 0 ≤ S := (sq_nonneg a).trans haS
  have hab : (a + b) ^ 2 ≤ 4 * S := by nlinarith [sq_nonneg (a - b)]
  have h2 : S ^ 2 ≤ K ^ 2 * (4 * S) := by
    calc S ^ 2 ≤ (K * (a + b)) ^ 2 := pow_le_pow_left₀ hS h 2
      _ = K ^ 2 * (a + b) ^ 2 := by ring
      _ ≤ K ^ 2 * (4 * S) := by gcongr
  rcases eq_or_lt_of_le hS with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

/-- **Tangential regularity for smooth data**: for `φ ∈ C¹` and `ξ = Sol(φ)`, the rotation
derivative `R_ij ξ` is the function component of `Z = Sol(R_ij φ) ∈ H¹₀(B)`, and
`Σ_k ‖∂_k Z‖² ≤ 4 r² ‖φ‖²_{L²(B)}`. -/
theorem tangential_smooth {i j : Fin n} (h : i ≠ j) {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    ((solCLM c r ((memLp_rotDer c r hφ (i := i) (j := j)).toLp (rotDer c i j φ)) : H1B0 c r) :
        H1Amb c r) none =
      rotDerOp c r i j (solCLM c r ((memLp_ball_of_C1 c r hφ).toLp φ)) ∧
    ∑ k, ‖((solCLM c r ((memLp_rotDer c r hφ (i := i) (j := j)).toLp (rotDer c i j φ)) :
        H1B0 c r) : H1Amb c r) (some k)‖ ^ 2 ≤
      4 * r ^ 2 * ‖(memLp_ball_of_C1 c r hφ).toLp φ‖ ^ 2 := by
  have hr0 := hr.out
  set F : L2B c r := (memLp_ball_of_C1 c r hφ).toLp φ with hFdef
  set G : L2B c r := (memLp_rotDer c r hφ (i := i) (j := j)).toLp (rotDer c i j φ) with hGdef
  set Z : H1B0 c r := solCLM c r G with hZdef
  have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none).continuous
  -- difference quotients of the data
  have hFq : Tendsto (fun m => (tseq m)⁻¹ • (flowB c r h (tseq m) F - F)) atTop (𝓝 G) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact tendsto_flow_quotient c r h hφ
  have hS : Tendsto (fun m => ((solCLM c r ((tseq m)⁻¹ • (flowB c r h (tseq m) F - F)) :
      H1B0 c r) : H1Amb c r) none) atTop (𝓝 ((Z : H1Amb c r) none)) :=
    ((hp.comp (continuous_subtype_val.comp (solCLM c r).continuous)).tendsto G).comp hFq
  have heq : ∀ m, ((solCLM c r ((tseq m)⁻¹ • (flowB c r h (tseq m) F - F)) :
      H1B0 c r) : H1Amb c r) none = (tseq m)⁻¹ • (flowB c r h (tseq m)
        (((solCLM c r F : H1B0 c r) : H1Amb c r) none) - ((solCLM c r F : H1B0 c r) :
          H1Amb c r) none) := by
    intro m
    rw [map_smul, map_sub, Submodule.coe_smul, Submodule.coe_sub, flowB,
      solCLM_compB c r (isOrth_rotM h (tseq m)), PiLp.smul_apply, PiLp.sub_apply, rotOp_none]
  have hR := tendsto_flowB_quotient_H1B c r h (solCLM c r F).2.1
  have hZ0 : (Z : H1Amb c r) none = rotDerOp c r i j (solCLM c r F) :=
    tendsto_nhds_unique (hS.congr heq) hR
  refine ⟨hZ0, ?_⟩
  -- the energy bound
  have hE := solCLM_spec c r G Z
  rw [dirForm_self, loadCLM_apply] at hE
  have hG : G = rotDerOp c r i j (graphC1 c r ⟨φ, show φ ∈ C1fun from hφ⟩) := by
    rw [rotDerOp_graphC1]
  have hanti := rotDerOp_antisymm c r h (graphC1 c r ⟨φ, show φ ∈ C1fun from hφ⟩)
    (graphC1_mem c r _) (Z : H1Amb c r) Z.2.1
  rw [← hG, graphC1_none] at hanti
  rw [hanti, neg_neg] at hE
  set S := ∑ k, ‖(Z : H1Amb c r) (some k)‖ ^ 2
  have hle : S ≤ ‖F‖ * r * (‖(Z : H1Amb c r) (some i)‖ + ‖(Z : H1Amb c r) (some j)‖) := by
    rw [hE]
    refine (real_inner_le_norm _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_rotDerOp_le c r i j _) (norm_nonneg _)
  have hsing : ∀ k, ‖(Z : H1Amb c r) (some k)‖ ^ 2 ≤ S := fun k =>
    Finset.single_le_sum (f := fun k => ‖(Z : H1Amb c r) (some k)‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  have := energy_le_of_le_mul_sum (by positivity) (norm_nonneg _) (norm_nonneg _) (hsing i)
    (hsing j) hle
  calc S ≤ 4 * (‖F‖ * r) ^ 2 := this
    _ = 4 * r ^ 2 * ‖F‖ ^ 2 := by ring

theorem rotDer_sub {i j : Fin n} {φ ψ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hψ : ContDiff ℝ 1 ψ) : rotDer c i j (φ - ψ) = rotDer c i j φ - rotDer c i j ψ := by
  funext y
  have hd1 := (hφ.differentiable one_ne_zero) y
  have hd2 := (hψ.differentiable one_ne_zero) y
  simp only [rotDer, Pi.sub_apply]
  rw [show φ - ψ = fun y => φ y - ψ y from rfl, pd_sub_real hd1 hd2, pd_sub_real hd1 hd2]
  ring

/-- **Tangential regularity of the weak Neumann problem on a ball** (stage C4b, step 1): for every
`F ∈ L²(B)` and `ξ = solCLM F` (the mean-zero weak solution of `Δξ = F - avg F`, `∂_νξ = 0`), and
every rotation field `R_ij = (x_i - c_i)∂_j - (x_j - c_j)∂_i` (`i ≠ j`), the function `R_ij ξ` is
the function component of a mean-zero `Z ∈ H¹(B)`, with `Σ_k ‖∂_k Z‖²_{L²(B)} ≤ 4 r² ‖F‖²`. -/
theorem tangential_regularity {i j : Fin n} (h : i ≠ j) (F : L2B c r) :
    ∃ Z : H1B0 c r, (Z : H1Amb c r) none = rotDerOp c r i j (solCLM c r F) ∧
      ∑ k, ‖(Z : H1Amb c r) (some k)‖ ^ 2 ≤ 4 * r ^ 2 * ‖F‖ ^ 2 := by
  have hr0 := hr.out
  -- smooth approximations of the data
  have happrox : ∀ m : ℕ, ∃ φ : (Fin n → ℝ) → ℝ, HasCompactSupport φ ∧ ContDiff ℝ ∞ φ ∧
      eLpNorm ((F : (Fin n → ℝ) → ℝ) - φ) 2 (volume.restrict (euclBall c r)) ≤
        ENNReal.ofReal (1 / ((m : ℝ) + 1)) := fun m =>
    (Lp.memLp F).exist_eLpNorm_sub_le (by norm_num) (by norm_num) (by positivity)
  choose φ _ hφs hφe using happrox
  have hφ1 : ∀ m, ContDiff ℝ 1 (φ m) := fun m => (hφs m).of_le (by simp)
  set Fm : ℕ → L2B c r := fun m => (memLp_ball_of_C1 c r (hφ1 m)).toLp (φ m)
  have hFm : Tendsto Fm atTop (𝓝 F) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_sub_rev, Lp.norm_def]
    have : eLpNorm ((F - Fm m : L2B c r) : (Fin n → ℝ) → ℝ) 2 (volume.restrict (euclBall c r)) =
        eLpNorm ((F : (Fin n → ℝ) → ℝ) - φ m) 2 (volume.restrict (euclBall c r)) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub F (Fm m), (memLp_ball_of_C1 c r (hφ1 m)).coeFn_toLp] with x h1 h2
      rw [h1, Pi.sub_apply, Pi.sub_apply]
      show F x - ((memLp_ball_of_C1 c r (hφ1 m)).toLp (φ m) : (Fin n → ℝ) → ℝ) x = F x - φ m x
      rw [h2]
    rw [this]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hφe m)
  set Zm : ℕ → H1B0 c r := fun m =>
    solCLM c r ((memLp_rotDer c r (hφ1 m) (i := i) (j := j)).toLp (rotDer c i j (φ m)))
  have hsm := fun m => tangential_smooth c r h (hφ1 m)
  -- Lipschitz control of the differences
  set L : ℝ := Real.sqrt ((2 ^ (n + 1) * r ^ 2 + 1) * (4 * r ^ 2))
  have hdiff : ∀ m k, ‖Zm m - Zm k‖ ≤ L * ‖Fm m - Fm k‖ := by
    intro m k
    have hsub : ContDiff ℝ 1 (φ m - φ k) := (hφ1 m).sub (hφ1 k)
    have e1 : Zm m - Zm k = solCLM c r ((memLp_rotDer c r hsub (i := i) (j := j)).toLp
        (rotDer c i j (φ m - φ k))) := by
      simp only [Zm]
      rw [← map_sub, ← MemLp.toLp_sub]
      congr 2
      exact (rotDer_sub c (hφ1 m) (hφ1 k)).symm
    have e2 : Fm m - Fm k = (memLp_ball_of_C1 c r hsub).toLp (φ m - φ k) := by
      simp only [Fm]; rw [← MemLp.toLp_sub]
    have hb := (tangential_smooth c r h hsub (i := i) (j := j)).2
    rw [← e1, ← e2] at hb
    have hn := norm_sq_H1B0_le c r (Zm m - Zm k)
    have hsq : ‖Zm m - Zm k‖ ^ 2 ≤ (L * ‖Fm m - Fm k‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      calc ‖Zm m - Zm k‖ ^ 2 ≤ (2 ^ (n + 1) * r ^ 2 + 1) *
            ∑ k', ‖((Zm m - Zm k : H1B0 c r) : H1Amb c r) (some k')‖ ^ 2 := hn
        _ ≤ (2 ^ (n + 1) * r ^ 2 + 1) * (4 * r ^ 2 * ‖Fm m - Fm k‖ ^ 2) := by gcongr
        _ = _ := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hcauchy : CauchySeq Zm := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hFm.cauchySeq (ε / (L + 1)) (by positivity)
    refine ⟨N, fun m hm k hk => ?_⟩
    rw [dist_eq_norm]
    have h1 := hN m hm k hk
    rw [dist_eq_norm] at h1
    have hL : 0 ≤ L := Real.sqrt_nonneg _
    calc ‖Zm m - Zm k‖ ≤ L * ‖Fm m - Fm k‖ := hdiff m k
      _ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left h1.le hL
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  obtain ⟨Z, hZ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none).continuous
  refine ⟨Z, ?_, ?_⟩
  · have h1 : Tendsto (fun m => ((Zm m : H1B0 c r) : H1Amb c r) none) atTop
        (𝓝 ((Z : H1Amb c r) none)) :=
      ((hp.comp continuous_subtype_val).tendsto Z).comp hZ
    have h2 : Tendsto (fun m => rotDerOp c r i j (solCLM c r (Fm m))) atTop
        (𝓝 (rotDerOp c r i j (solCLM c r F))) :=
      (((rotDerOp c r i j).continuous.comp (continuous_subtype_val.comp
        (solCLM c r).continuous)).tendsto F).comp hFm
    exact tendsto_nhds_unique (h1.congr fun m => (hsm m).1) h2
  · have hcont : Continuous fun x : H1B0 c r => ∑ k, ‖(x : H1Amb c r) (some k)‖ ^ 2 :=
      continuous_finset_sum _ fun k _ => (((PiLp.proj (𝕜 := ℝ) 2
        (fun _ : Option (Fin n) => L2B c r) (some k)).continuous.comp
          continuous_subtype_val).norm.pow 2)
    have h1 := (hcont.tendsto Z).comp hZ
    have h2 : Tendsto (fun m => 4 * r ^ 2 * ‖Fm m‖ ^ 2) atTop (𝓝 (4 * r ^ 2 * ‖F‖ ^ 2)) :=
      ((continuous_const.mul (continuous_norm.pow 2)).tendsto F).comp hFm
    exact le_of_tendsto_of_tendsto' h1 h2 fun m => (hsm m).2

end Main

end RenewalGeometry.BallAnalysis.BallReg
