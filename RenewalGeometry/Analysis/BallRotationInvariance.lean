/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallNeumannLaplacian

/-!
# Rotation invariance of `H¹(B)` and of the weak Neumann problem on a ball
  (stage C4b, step 0, of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.  Boundary regularity of the Neumann problem on
a ball is proved with the rotation vector fields `x_i ∂_j - x_j ∂_i`, which are tangent to the
spheres; this file provides the group-level input.

* `solCLM c r : L²(B) →L H¹₀(B)` — **the Neumann solution operator** (Lax–Milgram for the coercive
  Dirichlet form on mean-zero `H¹(B)`), `solCLM_spec`, and `solCLM_weak`: for every `y ∈ H¹(B)`,
  `Σ_i ⟨ξ_i, y_i⟩ = -⟨F, y₀⟩ + avg(F) ∫_B y₀` (`ξ = solCLM F` solves `Δξ = F - avg F`,
  `∂_νξ = 0` weakly);
* `IsOrth O` (orthogonal matrices), `rotAff c O x = c + O (x - c)` (rotation about the centre):
  `sqDist_rotAff`, `measurePreserving_rotAff` (Lebesgue measure), `measurePreserving_rotAff_ball`
  (restricted to the ball);
* `compB c r O : L²(B) →L L²(B)`, `g ↦ g ∘ ρ` (a linear isometry), and
  `rotOp c r O : L²(B)^{1+n} →L L²(B)^{1+n}`, `(w₀, w_i) ↦ (w₀ ∘ ρ, Σ_k O_{ki} w_k ∘ ρ)`
  (the chain rule for `u ∘ ρ`): `rotOp_graphC1` (graphs go to graphs), `rotOp_mem_H1B`
  (**`H¹(B)` is rotation invariant**), `rotOp_rotOp_transpose` (inverse), `dirSum_rotOp`
  (**the Dirichlet form is invariant**), `meanCLM_rotOp`;
* `solCLM_compB` (**equivariance of the Neumann problem**): `Sol(F ∘ ρ) = rotOp (Sol F)`.
-/

open MeasureTheory Set Metric Filter Topology Matrix
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ} [NeZero n]

/-! ### The Neumann solution operator -/

section Sol

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- A chosen solution of the abstract Neumann problem (`exists_neumann_H1B0`). -/
def solFun (F : L2B c r) : H1B0 c r := (exists_neumann_H1B0 c r F).choose

theorem solFun_spec (F : L2B c r) :
    ∀ y : H1B0 c r, dirForm c r (solFun c r F) y = loadCLM c r F y :=
  (exists_neumann_H1B0 c r F).choose_spec

theorem loadCLM_add (F G : L2B c r) : loadCLM c r (F + G) = loadCLM c r F + loadCLM c r G := by
  ext y
  simp [loadCLM, inner_add_left]
  ring

theorem loadCLM_smul (a : ℝ) (F : L2B c r) : loadCLM c r (a • F) = a • loadCLM c r F := by
  ext y
  simp [loadCLM, inner_smul_left]

/-- The solution map is linear (uniqueness of the Lax–Milgram solution). -/
def solLin : L2B c r →ₗ[ℝ] H1B0 c r where
  toFun := solFun c r
  map_add' F G := by
    refine neumann_H1B0_unique c r (solFun_spec c r (F + G)) fun y => ?_
    rw [map_add, ContinuousLinearMap.add_apply, solFun_spec, solFun_spec, loadCLM_add,
      ContinuousLinearMap.add_apply]
  map_smul' a F := by
    refine neumann_H1B0_unique c r (solFun_spec c r (a • F)) fun y => ?_
    rw [map_smul, ContinuousLinearMap.smul_apply, solFun_spec, loadCLM_smul,
      ContinuousLinearMap.smul_apply, RingHom.id_apply]

/-- The coercivity constant of the Dirichlet form (chosen). -/
def coerC : ℝ := (dirForm_coercive c r).choose

theorem coerC_pos : 0 < coerC c r := (dirForm_coercive c r).choose_spec.1

theorem coerC_spec (x : H1B0 c r) : coerC c r * ‖x‖ * ‖x‖ ≤ dirForm c r x x :=
  (dirForm_coercive c r).choose_spec.2 x

theorem norm_solFun_le (F : L2B c r) : ‖solFun c r F‖ ≤ (coerC c r)⁻¹ * ‖F‖ := by
  set ξ := solFun c r F
  have h1 := coerC_spec c r ξ
  rw [solFun_spec] at h1
  have h2 : loadCLM c r F ξ ≤ ‖F‖ * ‖ξ‖ := by
    simp only [loadCLM, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, Submodule.subtypeL_apply, PiLp.proj_apply]
    refine (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans ?_)
    gcongr
    exact PiLp.norm_apply_le (ξ : H1Amb c r) none
  have hC := coerC_pos c r
  rcases eq_or_lt_of_le (norm_nonneg ξ) with h | h
  · rw [← h]; positivity
  · rw [le_inv_mul_iff₀ hC]
    have : coerC c r * ‖ξ‖ * ‖ξ‖ ≤ ‖F‖ * ‖ξ‖ := h1.trans h2
    nlinarith

/-- **The Neumann solution operator** `L²(B) → H¹₀(B)`: `solCLM F` is the unique mean-zero
`ξ ∈ H¹(B)` with `Σ_i ⟨ξ_i, y_i⟩ = -⟨F, y₀⟩` for all mean-zero `y ∈ H¹(B)` (the weak form of
`Δξ = F - avg F`, `∂_νξ = 0`). -/
def solCLM : L2B c r →L[ℝ] H1B0 c r :=
  (solLin c r).mkContinuous (coerC c r)⁻¹ (norm_solFun_le c r)

theorem solCLM_apply (F : L2B c r) : solCLM c r F = solFun c r F := rfl

theorem solCLM_spec (F : L2B c r) :
    ∀ y : H1B0 c r, dirForm c r (solCLM c r F) y = loadCLM c r F y :=
  solFun_spec c r F

theorem norm_solCLM_le (F : L2B c r) : ‖solCLM c r F‖ ≤ (coerC c r)⁻¹ * ‖F‖ :=
  norm_solFun_le c r F

/-- The average `|B|⁻¹ ∫_B F`. -/
def avgB (F : L2B c r) : ℝ := (volB c r)⁻¹ * ⟪oneB c r, F⟫

/-- **The weak Neumann equation against all of `H¹(B)`**: for `ξ = solCLM F` and `y ∈ H¹(B)`,
`Σ_i ⟨ξ_i, y_i⟩ = -⟨F, y₀⟩ + avg(F) · ∫_B y₀`. -/
theorem solCLM_weak (F : L2B c r) {y : H1Amb c r} (hy : y ∈ H1B c r) :
    ∑ i, ⟪((solCLM c r F : H1B0 c r) : H1Amb c r) (some i), y (some i)⟫ =
      -⟪F, y none⟫ + avgB c r F * meanCLM c r y := by
  set ξ := solCLM c r F
  set t := (volB c r)⁻¹ * meanCLM c r y
  have hy0 : y - t • oneH c r ∈ H1B0 c r := by
    refine ⟨(H1B c r).sub_mem hy ((H1B c r).smul_mem t (oneH_mem c r)), ?_⟩
    show meanCLM c r (y - t • oneH c r) = 0
    rw [map_sub, map_smul, meanCLM_oneH, smul_eq_mul, mul_comm t, show t = (volB c r)⁻¹ *
      meanCLM c r y from rfl, ← mul_assoc, mul_inv_cancel₀ (volB_pos c r).ne', one_mul, sub_self]
  have := solCLM_spec c r F ⟨_, hy0⟩
  rw [dirForm_apply] at this
  simp only [loadCLM, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Submodule.subtypeL_apply, PiLp.proj_apply] at this
  have e1 : ∀ i, (y - t • oneH c r) (some i) = y (some i) := fun i => by
    simp [oneH]
  have e2 : (y - t • oneH c r) none = y none - t • oneB c r := by
    simp [oneH]
  simp only [e1, e2, inner_sub_right, inner_smul_right] at this
  rw [this, avgB, real_inner_comm (oneB c r) F]
  simp only [t]
  ring

end Sol

/-! ### Orthogonal matrices and rotations about the centre -/

/-- An orthogonal matrix: `O Oᵀ = 1 = Oᵀ O`. -/
structure IsOrth (O : Matrix (Fin n) (Fin n) ℝ) : Prop where
  mul_tr : O * Oᵀ = 1
  tr_mul : Oᵀ * O = 1

theorem IsOrth.transpose {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) : IsOrth Oᵀ :=
  ⟨by rw [transpose_transpose]; exact hO.tr_mul, by rw [transpose_transpose]; exact hO.mul_tr⟩

theorem IsOrth.sum_mul_row {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (k l : Fin n) :
    ∑ i, O k i * O l i = if k = l then 1 else 0 := by
  have := congrFun (congrFun hO.mul_tr k) l
  simp only [mul_apply, transpose_apply, one_apply] at this
  exact this

theorem IsOrth.sum_mul_col {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (k l : Fin n) :
    ∑ i, O i k * O i l = if k = l then 1 else 0 := by
  have := congrFun (congrFun hO.tr_mul k) l
  simp only [mul_apply, transpose_apply, one_apply] at this
  exact this

theorem IsOrth.det_sq {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) : O.det ^ 2 = 1 := by
  have := congrArg det hO.mul_tr
  rw [det_mul, det_transpose, det_one] at this
  rw [sq]; exact this

theorem IsOrth.abs_det {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) : |O.det| = 1 := by
  have h := hO.det_sq
  have : |O.det| ^ 2 = 1 := by rw [sq_abs]; exact h
  nlinarith [abs_nonneg O.det, sq_nonneg (|O.det| - 1)]

/-- `Σ_k ((O v)_k)² = Σ_k v_k²` for orthogonal `O`. -/
theorem IsOrth.sum_sq_mulVec {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (v : Fin n → ℝ) :
    ∑ k, (O *ᵥ v) k ^ 2 = ∑ k, v k ^ 2 := by
  have h1 : ∑ k, (O *ᵥ v) k ^ 2 = (O *ᵥ v) ⬝ᵥ (O *ᵥ v) := by
    simp [dotProduct, sq]
  have h2 : ∑ k, v k ^ 2 = v ⬝ᵥ v := by simp [dotProduct, sq]
  rw [h1, h2, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hO.tr_mul, one_mulVec,
    dotProduct_comm]

/-- The rotation `ρ(x) = c + O (x - c)` about the centre `c`. -/
def rotAff (c : Fin n → ℝ) (O : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  c + O *ᵥ (x - c)

theorem rotAff_apply (c : Fin n → ℝ) (O : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (k : Fin n) :
    rotAff c O x k = c k + ∑ l, O k l * (x l - c l) := by
  simp [rotAff, mulVec, dotProduct]

theorem sqDist_rotAff (c : Fin n → ℝ) {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O)
    (x : Fin n → ℝ) : sqDist c (rotAff c O x) = sqDist c x := by
  unfold sqDist rotAff
  have := hO.sum_sq_mulVec (x - c)
  simpa using this

theorem rotAff_rotAff_transpose (c : Fin n → ℝ) {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O)
    (x : Fin n → ℝ) : rotAff c Oᵀ (rotAff c O x) = x := by
  simp only [rotAff, add_sub_cancel_left, mulVec_mulVec, hO.tr_mul, one_mulVec]
  abel

theorem rotAff_transpose_rotAff (c : Fin n → ℝ) {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O)
    (x : Fin n → ℝ) : rotAff c O (rotAff c Oᵀ x) = x := by
  simp only [rotAff, add_sub_cancel_left, mulVec_mulVec, hO.mul_tr, one_mulVec]
  abel

theorem continuous_rotAff (c : Fin n → ℝ) (O : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (rotAff c O) := by
  unfold rotAff
  exact continuous_const.add ((Matrix.toLin' O).continuous_of_finiteDimensional.comp
    (continuous_id.sub continuous_const))

/-- **Rotations preserve Lebesgue measure.** -/
theorem measurePreserving_rotAff (c : Fin n → ℝ) {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) :
    MeasurePreserving (rotAff c O) volume volume := by
  have hdet : O.det ≠ 0 := by
    intro h; have := hO.abs_det; rw [h, abs_zero] at this; exact zero_ne_one this
  have hL : MeasurePreserving (Matrix.toLin' O) volume volume := by
    refine ⟨(Matrix.toLin' O).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, abs_inv, hO.abs_det, inv_one,
      ENNReal.ofReal_one, one_smul]
  have h1 : MeasurePreserving (fun x : Fin n → ℝ => x - c) volume volume :=
    measurePreserving_sub_right volume c
  have h2 : MeasurePreserving (fun x : Fin n → ℝ => c + x) volume volume :=
    measurePreserving_add_left volume c
  have := h2.comp (hL.comp h1)
  convert this using 1
  funext x
  simp [rotAff, Matrix.toLin'_apply]

theorem preimage_rotAff_ball (c : Fin n → ℝ) (r : ℝ) {O : Matrix (Fin n) (Fin n) ℝ}
    (hO : IsOrth O) : rotAff c O ⁻¹' euclBall c r = euclBall c r := by
  ext x
  simp only [mem_preimage, euclBall, mem_setOf_eq, sqDist_rotAff c hO]

/-- Rotations about the centre preserve the restricted measure on the ball. -/
theorem measurePreserving_rotAff_ball (c : Fin n → ℝ) (r : ℝ) {O : Matrix (Fin n) (Fin n) ℝ}
    (hO : IsOrth O) :
    MeasurePreserving (rotAff c O) (volume.restrict (euclBall c r))
      (volume.restrict (euclBall c r)) := by
  have := (measurePreserving_rotAff c hO).restrict_preimage (measurableSet_euclBall c r)
  rwa [preimage_rotAff_ball c r hO] at this

/-! ### Composition operators -/

section Comp

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- `g ↦ g ∘ ρ` on `L²(B)` (a linear isometry). -/
def compB {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) : L2B c r →L[ℝ] L2B c r :=
  (Lp.compMeasurePreservingₗᵢ ℝ (rotAff c O)
    (measurePreserving_rotAff_ball c r hO)).toContinuousLinearMap

theorem compB_apply {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (g : L2B c r) :
    compB c r hO g = Lp.compMeasurePreserving (rotAff c O) (measurePreserving_rotAff_ball c r hO) g :=
  rfl

theorem coeFn_compB {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (g : L2B c r) :
    (compB c r hO g : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)] g ∘ rotAff c O :=
  Lp.coeFn_compMeasurePreserving g _

theorem compB_toLp {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) {f : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 (volume.restrict (euclBall c r))) :
    compB c r hO (hf.toLp f) =
      (hf.comp_measurePreserving (measurePreserving_rotAff_ball c r hO)).toLp (f ∘ rotAff c O) :=
  rfl

theorem inner_compB {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (g h : L2B c r) :
    ⟪compB c r hO g, compB c r hO h⟫ = ⟪g, h⟫ :=
  LinearIsometry.inner_map_map _ g h

theorem norm_compB {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (g : L2B c r) :
    ‖compB c r hO g‖ = ‖g‖ :=
  LinearIsometry.norm_map _ g

theorem compB_compB_transpose {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (g : L2B c r) :
    compB c r hO (compB c r hO.transpose g) = g := by
  refine Lp.ext ?_
  have h1 := coeFn_compB c r hO (compB c r hO.transpose g)
  have h2 := coeFn_compB c r hO.transpose g
  have h2' : (compB c r hO.transpose g : (Fin n → ℝ) → ℝ) ∘ rotAff c O =ᵐ[volume.restrict
      (euclBall c r)] ((g : (Fin n → ℝ) → ℝ) ∘ rotAff c Oᵀ) ∘ rotAff c O :=
    (measurePreserving_rotAff_ball c r hO).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h2'] with x hx1 hx2
  rw [hx1, hx2]
  simp [Function.comp, rotAff_rotAff_transpose c hO]

theorem compB_oneB {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) :
    compB c r hO (oneB c r) = oneB c r := by
  rw [oneB, compB_toLp]
  rfl

/-- `L²(B)`-valued sums: the coefficient function of a finite sum. -/
theorem coeFn_finset_sum {ι : Type*} (s : Finset ι) (f : ι → L2B c r) :
    ((∑ k ∈ s, f k : L2B c r) : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      fun x => ∑ k ∈ s, (f k : (Fin n → ℝ) → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ k ∈ s, f k), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2]

/-- The rotation acting on `L²(B)^{1+n}` by the chain rule:
`(w₀, w_i) ↦ (w₀ ∘ ρ, Σ_k O_{ki} w_k ∘ ρ)`. -/
def rotComp {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) :
    (k : Option (Fin n)) → (H1Amb c r →L[ℝ] L2B c r)
  | none => (compB c r hO).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) none)
  | some i => ∑ k, O k i • (compB c r hO).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin n) => L2B c r) (some k))

/-- **The rotation operator** on `L²(B)^{1+n}`. -/
def rotOp {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) : H1Amb c r →L[ℝ] H1Amb c r :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin n) => L2B c r)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (rotComp c r hO))

theorem rotOp_none {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (x : H1Amb c r) :
    rotOp c r hO x none = compB c r hO (x none) := rfl

theorem rotOp_some {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (x : H1Amb c r) (i : Fin n) :
    rotOp c r hO x (some i) = ∑ k, O k i • compB c r hO (x (some k)) := by
  show rotComp c r hO (some i) x = _
  simp [rotComp, ContinuousLinearMap.sum_apply]

/-- Chain rule for `u ∘ ρ`. -/
theorem pd_comp_rotAff {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (O : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    pd (u ∘ rotAff c O) i x = ∑ k, O k i * pd u k (rotAff c O x) := by
  set L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := (Matrix.toLin' O).toContinuousLinearMap
  have hρeq : rotAff c O = fun y => c + L (y - c) := by
    funext y; simp [rotAff, L, Matrix.toLin'_apply]
  have hρ : HasFDerivAt (rotAff c O) L x := by
    have h1 : HasFDerivAt (fun y : Fin n → ℝ => y - c) (ContinuousLinearMap.id ℝ _) x :=
      (hasFDerivAt_id x).sub_const c
    have h3 := (L.hasFDerivAt.comp x h1).const_add c
    rw [hρeq]
    simpa using h3
  have hd := ((hu.differentiable one_ne_zero) (rotAff c O x)).hasFDerivAt.comp x hρ
  unfold pd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_apply_eq_sum_pd]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hL : L (Pi.single i 1) k = O k i := by
    simp only [L, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, mulVec_single_one]
    rfl
  rw [hL]
  rfl

theorem contDiff_comp_rotAff {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (O : Matrix (Fin n) (Fin n) ℝ) : ContDiff ℝ 1 (u ∘ rotAff c O) := by
  refine hu.comp ?_
  unfold rotAff
  exact contDiff_const.add ((Matrix.toLin' O).toContinuousLinearMap.contDiff.comp
    (contDiff_id.sub contDiff_const))

/-- **Rotations map `C¹` graphs to `C¹` graphs**: `rotOp (graph u) = graph (u ∘ ρ)`. -/
theorem rotOp_graphC1 {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (u : C1fun (n := n)) :
    rotOp c r hO (graphC1 c r u) =
      graphC1 c r ⟨(u : (Fin n → ℝ) → ℝ) ∘ rotAff c O,
        show ContDiff ℝ 1 _ from contDiff_comp_rotAff c u.2 O⟩ := by
  ext k : 1
  cases k with
  | none =>
    rw [rotOp_none, graphC1_none, graphC1_none, compB_toLp]
  | some i =>
    rw [rotOp_some, graphC1_some]
    refine Lp.ext ?_
    have hsum := coeFn_finset_sum c r Finset.univ
      (fun k => O k i • compB c r hO (graphC1 c r u (some k)))
    filter_upwards [hsum, (memLp_ball_pd_of_C1 c r (contDiff_comp_rotAff c u.2 O) i).coeFn_toLp,
      ae_all_iff.mpr fun k => Lp.coeFn_smul (O k i) (compB c r hO (graphC1 c r u (some k))),
      ae_all_iff.mpr fun k => coeFn_compB c r hO (graphC1 c r u (some k)),
      ae_all_iff.mpr fun k => (measurePreserving_rotAff_ball c r hO).quasiMeasurePreserving.ae_eq_comp
        (memLp_ball_pd_of_C1 c r u.2 k).coeFn_toLp] with x h1 h2 h3 h4 h5
    rw [h1, h2, pd_comp_rotAff c u.2 O i x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h3 k, Pi.smul_apply, h4 k, graphC1_some]
    simp only [Function.comp_apply, smul_eq_mul] at h5 ⊢
    rw [h5 k]

/-- **`H¹(B)` is rotation invariant.** -/
theorem rotOp_mem_H1B {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) :
    ∀ x ∈ H1B c r, rotOp c r hO x ∈ H1B c r := by
  refine H1B_induction c r ?_ fun u => ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage (rotOp c r hO).continuous
  · rw [rotOp_graphC1]; exact graphC1_mem c r _

theorem rotOp_rotOp_transpose {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (x : H1Amb c r) :
    rotOp c r hO (rotOp c r hO.transpose x) = x := by
  ext k : 1
  cases k with
  | none => rw [rotOp_none, rotOp_none, compB_compB_transpose]
  | some i =>
    rw [rotOp_some]
    simp only [rotOp_some, map_sum, map_smul, compB_compB_transpose, Finset.smul_sum, smul_smul,
      transpose_apply]
    rw [Finset.sum_comm]
    have : ∀ l, ∑ k, (O k i * O k l) • x (some l) = (if i = l then 1 else 0 : ℝ) • x (some l) :=
      fun l => by rw [← Finset.sum_smul, hO.sum_mul_col]
    simp only [this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- `⟨Σ_k a_k A_k, Σ_l b_l B_l⟩ = Σ_k Σ_l a_k b_l ⟨A_k, B_l⟩`. -/
theorem inner_sum_smul_sum_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : Fin n → ℝ) (A B : Fin n → E) :
    ⟪∑ k, a k • A k, ∑ l, b l • B l⟫ = ∑ k, ∑ l, a k * b l * ⟪A k, B l⟫ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

/-- **Invariance of the Dirichlet form** under rotations. -/
theorem dirSum_rotOp {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (x y : H1Amb c r) :
    ∑ i, ⟪rotOp c r hO x (some i), rotOp c r hO y (some i)⟫ = ∑ i, ⟪x (some i), y (some i)⟫ := by
  simp only [rotOp_some]
  simp only [inner_sum_smul_sum_smul (fun k => O k _) (fun l => O l _), inner_compB]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have : ∀ l, ∑ i, O k i * O l i * ⟪x (some k), y (some l)⟫ =
      (if k = l then 1 else 0) * ⟪x (some k), y (some l)⟫ := fun l => by
    rw [← Finset.sum_mul, hO.sum_mul_row]
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem meanCLM_rotOp {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (x : H1Amb c r) :
    meanCLM c r (rotOp c r hO x) = meanCLM c r x := by
  rw [meanCLM_apply, meanCLM_apply, rotOp_none]
  conv_lhs => rw [← compB_oneB c r hO]
  rw [inner_compB]

theorem rotOp_mem_H1B0 {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) {x : H1Amb c r}
    (hx : x ∈ H1B0 c r) : rotOp c r hO x ∈ H1B0 c r :=
  ⟨rotOp_mem_H1B c r hO x hx.1, by
    show meanCLM c r (rotOp c r hO x) = 0
    rw [meanCLM_rotOp]; exact hx.2⟩

/-- **Equivariance of the Neumann problem**: `Sol(F ∘ ρ) = rotOp (Sol F)`. -/
theorem solCLM_compB {O : Matrix (Fin n) (Fin n) ℝ} (hO : IsOrth O) (F : L2B c r) :
    ((solCLM c r (compB c r hO F) : H1B0 c r) : H1Amb c r) =
      rotOp c r hO ((solCLM c r F : H1B0 c r) : H1Amb c r) := by
  set ξ := solCLM c r F
  have hmem : rotOp c r hO (ξ : H1Amb c r) ∈ H1B0 c r := rotOp_mem_H1B0 c r hO ξ.2
  have key : ∀ y : H1B0 c r, dirForm c r ⟨_, hmem⟩ y = loadCLM c r (compB c r hO F) y := by
    intro y
    have hy' : rotOp c r hO.transpose (y : H1Amb c r) ∈ H1B0 c r :=
      rotOp_mem_H1B0 c r hO.transpose y.2
    have h1 := solCLM_spec c r F ⟨_, hy'⟩
    rw [dirForm_apply] at h1 ⊢
    simp only [loadCLM, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, Submodule.subtypeL_apply, PiLp.proj_apply] at h1 ⊢
    have e : (y : H1Amb c r) = rotOp c r hO (rotOp c r hO.transpose (y : H1Amb c r)) :=
      (rotOp_rotOp_transpose c r hO _).symm
    rw [show (∑ i, ⟪rotOp c r hO (ξ : H1Amb c r) (some i), (y : H1Amb c r) (some i)⟫) =
        ∑ i, ⟪rotOp c r hO (ξ : H1Amb c r) (some i),
          rotOp c r hO (rotOp c r hO.transpose (y : H1Amb c r)) (some i)⟫ by rw [← e],
      dirSum_rotOp, h1]
    rw [rotOp_none, ← inner_compB c r hO, compB_compB_transpose]
  have := neumann_H1B0_unique c r (solCLM_spec c r (compB c r hO F)) key
  rw [this]

end Comp

end RenewalGeometry.BallAnalysis.BallReg
