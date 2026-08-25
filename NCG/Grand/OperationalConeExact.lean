/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Operational marginal cone and future-visible neutral carrier

Machinery for `thm:SM-operational-cone`.  On a finite-dimensional coefficient space `E`, the
homogeneous equality writers are assembled into `R : E →ₗ[ℝ] F` with `E₀ = ker R`, and the
matrix-order writers `𝓛_j : E →ₗ[ℝ] Matrix (n j) (n j) ℝ` cut out the cone
`𝒦 = {x ∈ E₀ : 𝓛_j x ⪰ 0 ∀ j}` (RG.3b).

* (RG.3c) `𝒦 ∩ (-𝒦) = E₀ ∩ ker 𝓛` (`cone_inter_neg`);
* (RG.3d) for positive definite calibration matrices `W_j`, `ν(x) = ∑ⱼ Tr(W_j 𝓛_j x)` is
  nonnegative on `𝒦` and strictly positive on every `x ∈ 𝒦` outside `ker 𝓛`, i.e. on every
  nonzero ray of the pointed quotient cone (`calib_nonneg`, `calib_pos`); this rests on
  `Tr(W M) > 0` for `W ≻ 0`, `M ⪰ 0`, `M ≠ 0` (`trace_mul_pos`);
* (RG.3e) the base `ℬ = {x ∈ 𝒦 : ν(x) = 1}` is convex (`base_convex`) and, once the lineality
  `E₀ ∩ ker 𝓛` has been quotiented (pointedness), compact (`base_isCompact`).
-/

open Matrix
open scoped MatrixOrder

namespace NCG
namespace OperationalCone

/-! ### Trace pairings of positive matrices -/

section Trace

variable {n : Type*} [Fintype n]

omit [Fintype n] in
/-- A matrix that is both positive semidefinite and negative semidefinite vanishes. -/
theorem eq_zero_of_posSemidef_of_neg_posSemidef [Finite n] {M : Matrix n n ℝ}
    (hM : M.PosSemidef) (hN : (-M).PosSemidef) : M = 0 := by
  classical
  cases nonempty_fintype n
  have hv : ∀ v, M *ᵥ v = 0 := by
    intro v
    have h1 := hM.dotProduct_mulVec_nonneg v
    have h2 := hN.dotProduct_mulVec_nonneg v
    rw [neg_mulVec, dotProduct_neg] at h2
    have h0 : star v ⬝ᵥ (M *ᵥ v) = 0 := le_antisymm (by linarith) h1
    exact (hM.dotProduct_mulVec_zero_iff v).mp h0
  ext a b
  have := congrFun (hv (Pi.single b 1)) a
  rw [mulVec_single_one] at this
  exact this

/-- `Tr(W M) ≥ 0` for `W, M ⪰ 0`. -/
theorem trace_mul_nonneg {W M : Matrix n n ℝ} (hW : W.PosSemidef) (hM : M.PosSemidef) :
    0 ≤ (W * M).trace := by
  classical
  have hW0 : 0 ≤ W := hW.nonneg
  have hsH : (CFC.sqrt W)ᴴ = CFC.sqrt W := (CFC.sqrt_nonneg W).posSemidef.isHermitian
  have h1 : (W * M).trace = ((CFC.sqrt W)ᴴ * M * CFC.sqrt W).trace := by
    conv_lhs => rw [← CFC.sqrt_mul_sqrt_self W hW0]
    rw [hsH, mul_assoc, trace_mul_comm]
  rw [h1]
  exact (hM.conjTranspose_mul_mul_same _).trace_nonneg

/-- `Tr(W M) > 0` for `W ≻ 0`, `M ⪰ 0`, `M ≠ 0`. -/
theorem trace_mul_pos {W M : Matrix n n ℝ} (hW : W.PosDef) (hM : M.PosSemidef) (hM0 : M ≠ 0) :
    0 < (W * M).trace := by
  classical
  rcases (trace_mul_nonneg hW.posSemidef hM).lt_or_eq with h | h
  · exact h
  exfalso
  have hW0 : 0 ≤ W := hW.posSemidef.nonneg
  have hM0' : 0 ≤ M := hM.nonneg
  set S := CFC.sqrt W with hS
  set T := CFC.sqrt M with hT
  have hSH : Sᴴ = S := (CFC.sqrt_nonneg W).posSemidef.isHermitian
  have hTH : Tᴴ = T := (CFC.sqrt_nonneg M).posSemidef.isHermitian
  have h2 : (W * M).trace = ((T * S)ᴴ * (T * S)).trace := by
    rw [conjTranspose_mul, hSH, hTH]
    conv_lhs => rw [← CFC.sqrt_mul_sqrt_self W hW0, ← CFC.sqrt_mul_sqrt_self M hM0']
    have e1 : S * S * (T * T) = S * (S * T * T) := by simp only [mul_assoc]
    have e2 : S * T * (T * S) = S * T * T * S := by simp only [mul_assoc]
    rw [e1, e2, trace_mul_comm]
  have h3 : (T * S)ᴴ * (T * S) = 0 :=
    (posSemidef_conjTranspose_mul_self (T * S)).trace_eq_zero_iff.mp (h2 ▸ h.symm)
  have h4 : T * S = 0 := conjTranspose_mul_self_eq_zero.mp h3
  have hSunit : IsUnit S :=
    (CFC.isUnit_sqrt_iff W hW0).mpr ((isUnit_iff_isUnit_det W).mpr hW.det_pos.ne'.isUnit)
  have h5 : T = 0 := (hSunit.mul_left_eq_zero).mp h4
  have h6 : M = 0 := by
    rw [← CFC.sqrt_mul_sqrt_self M hM0', ← hT, h5, mul_zero]
  exact hM0 h6

omit [Fintype n] in
/-- The positive semidefinite matrices form a closed set. -/
theorem isClosed_posSemidef [Finite n] : IsClosed {M : Matrix n n ℝ | M.PosSemidef} := by
  cases nonempty_fintype n
  have h : {M : Matrix n n ℝ | M.PosSemidef}
      = {M | Mᴴ = M} ∩ ⋂ v : n → ℝ, {M | 0 ≤ star v ⬝ᵥ (M *ᵥ v)} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun hM => ⟨hM.1, hM.dotProduct_mulVec_nonneg⟩,
      fun hM => PosSemidef.of_dotProduct_mulVec_nonneg hM.1 hM.2⟩
  rw [h]
  refine (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter ?_
  exact isClosed_iInter fun v =>
    isClosed_le continuous_const (continuous_const.dotProduct (continuous_id.matrix_mulVec
      continuous_const))

end Trace

/-! ### The operational cone -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {ι : Type*} [Fintype ι] {n : ι → Type*} [∀ j, Fintype (n j)]

variable (R : E →ₗ[ℝ] F) (L : ∀ j, E →ₗ[ℝ] Matrix (n j) (n j) ℝ)

/-- (RG.3b) the operational cone `𝒦 = {x ∈ ker R : 𝓛_j x ⪰ 0 ∀ j}`. -/
def cone : Set E := {x | x ∈ LinearMap.ker R ∧ ∀ j, (L j x).PosSemidef}

/-- The writer kernel `E₀ ∩ ker 𝓛` (the lineality space). -/
def writerKer : Set E := {x | x ∈ LinearMap.ker R ∧ ∀ j, L j x = 0}

omit [FiniteDimensional ℝ E] [Fintype ι] [∀ j, Fintype (n j)] in
theorem writerKer_subset_cone : writerKer R L ⊆ cone R L := fun x ⟨hx, hL⟩ =>
  ⟨hx, fun j => by rw [hL j]; exact PosSemidef.zero⟩

omit [FiniteDimensional ℝ E] [Fintype ι] [∀ j, Fintype (n j)] in
theorem cone_smul {x : E} (hx : x ∈ cone R L) {c : ℝ} (hc : 0 ≤ c) : c • x ∈ cone R L :=
  ⟨(LinearMap.ker R).smul_mem c hx.1, fun j => by rw [map_smul]; exact (hx.2 j).smul hc⟩

omit [FiniteDimensional ℝ E] [Fintype ι] [∀ j, Fintype (n j)] in
theorem cone_add {x y : E} (hx : x ∈ cone R L) (hy : y ∈ cone R L) : x + y ∈ cone R L :=
  ⟨(LinearMap.ker R).add_mem hx.1 hy.1, fun j => by rw [map_add]; exact (hx.2 j).add (hy.2 j)⟩

omit [FiniteDimensional ℝ E] [Fintype ι] [∀ j, Fintype (n j)] in
theorem zero_mem_cone : (0 : E) ∈ cone R L :=
  ⟨(LinearMap.ker R).zero_mem, fun j => by rw [map_zero]; exact PosSemidef.zero⟩

omit [FiniteDimensional ℝ E] [Fintype ι] [∀ j, Fintype (n j)] in
/-- **(RG.3c)**: `𝒦 ∩ (-𝒦) = E₀ ∩ ker 𝓛`. -/
theorem cone_inter_neg [∀ j, Finite (n j)] : cone R L ∩ -cone R L = writerKer R L := by
  classical
  ext x
  constructor
  · rintro ⟨⟨hx, hpos⟩, ⟨_, hneg⟩⟩
    refine ⟨hx, fun j => ?_⟩
    have hN : (-(L j x)).PosSemidef := by
      have := hneg j
      rwa [map_neg] at this
    exact eq_zero_of_posSemidef_of_neg_posSemidef (hpos j) hN
  · intro hx
    refine ⟨writerKer_subset_cone R L hx, ?_⟩
    change -x ∈ cone R L
    exact ⟨(LinearMap.ker R).neg_mem hx.1, fun j => by
      rw [map_neg, hx.2 j, neg_zero]; exact PosSemidef.zero⟩

omit [FiniteDimensional ℝ E] [Fintype ι] [∀ j, Fintype (n j)] in
theorem convex_cone : Convex ℝ (cone R L) := by
  intro x hx y hy a b ha hb _
  exact cone_add R L (cone_smul R L hx ha) (cone_smul R L hy hb)

omit [Fintype ι] [∀ j, Fintype (n j)] in
theorem isClosed_cone [∀ j, Finite (n j)] : IsClosed (cone R L) := by
  have h : cone R L = (LinearMap.ker R : Set E) ∩ ⋂ j, L j ⁻¹' {M | M.PosSemidef} := by
    ext x
    simp [cone, Set.mem_iInter]
  rw [h]
  refine (LinearMap.ker R).closed_of_finiteDimensional.inter (isClosed_iInter fun j => ?_)
  exact isClosed_posSemidef.preimage (L j).continuous_of_finiteDimensional

/-! ### (RG.3d): the calibration functional -/

variable (W : ∀ j, Matrix (n j) (n j) ℝ)

/-- (RG.3d) `ν(x) = ∑ⱼ Tr(W_j 𝓛_j x)`. -/
noncomputable def calib (x : E) : ℝ := ∑ j, (W j * L j x).trace

omit [FiniteDimensional ℝ E] in
theorem calib_smul (c : ℝ) (x : E) : calib L W (c • x) = c * calib L W x := by
  simp only [calib, map_smul, Matrix.mul_smul, trace_smul, smul_eq_mul, Finset.mul_sum]

omit [FiniteDimensional ℝ E] in
theorem calib_add (x y : E) : calib L W (x + y) = calib L W x + calib L W y := by
  simp only [calib, map_add, Matrix.mul_add, trace_add, Finset.sum_add_distrib]

theorem continuous_calib : Continuous (calib L W) :=
  continuous_finsetSum _ fun j _ =>
    (continuous_const.matrix_mul (L j).continuous_of_finiteDimensional).matrix_trace

omit [FiniteDimensional ℝ E] in
theorem calib_nonneg (hW : ∀ j, (W j).PosDef) {x : E} (hx : x ∈ cone R L) :
    0 ≤ calib L W x := by
  classical
  exact Finset.sum_nonneg fun j _ => trace_mul_nonneg (hW j).posSemidef (hx.2 j)

omit [FiniteDimensional ℝ E] in
/-- **(RG.3d)**: `ν` is strictly positive on every cone point outside the writer kernel, i.e.
on every nonzero ray of the pointed quotient cone. -/
theorem calib_pos (hW : ∀ j, (W j).PosDef) {x : E} (hx : x ∈ cone R L)
    (hx' : ¬ ∀ j, L j x = 0) : 0 < calib L W x := by
  classical
  rw [not_forall] at hx'
  obtain ⟨j, hj⟩ := hx'
  refine Finset.sum_pos' (fun k _ => trace_mul_nonneg (hW k).posSemidef (hx.2 k)) ?_
  exact ⟨j, Finset.mem_univ j, trace_mul_pos (hW j) (hx.2 j) hj⟩

/-! ### (RG.3e): the compact convex base -/

/-- (RG.3e) the base `ℬ = {x ∈ 𝒦 : ν(x) = 1}`. -/
def base : Set E := {x | x ∈ cone R L ∧ calib L W x = 1}

omit [FiniteDimensional ℝ E] in
theorem base_convex : Convex ℝ (base R L W) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_cone R L hx.1 hy.1 ha hb hab, ?_⟩
  rw [calib_add, calib_smul, calib_smul, hx.2, hy.2, mul_one, mul_one, hab]

theorem isClosed_base : IsClosed (base R L W) :=
  (isClosed_cone R L).inter (isClosed_eq (continuous_calib L W) continuous_const)

/-- On a pointed cone the calibration dominates the norm: `c ‖x‖ ≤ ν(x)` on `𝒦` for some
`c > 0`. -/
theorem exists_calib_ge_norm (hW : ∀ j, (W j).PosDef)
    (hpointed : ∀ x ∈ LinearMap.ker R, (∀ j, L j x = 0) → x = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ cone R L, c * ‖x‖ ≤ calib L W x := by
  set S : Set E := Metric.sphere (0 : E) 1 ∩ cone R L with hS
  have hScompact : IsCompact S := (isCompact_sphere (0 : E) 1).inter_right (isClosed_cone R L)
  by_cases hne : S.Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hScompact.exists_isMinOn hne (continuous_calib L W).continuousOn
    have hx₀ne : x₀ ≠ 0 := by
      intro h0
      have := hx₀.1
      rw [mem_sphere_iff_norm, sub_zero, h0, norm_zero] at this
      exact zero_ne_one this
    have hc : 0 < calib L W x₀ := by
      refine calib_pos R L W hW hx₀.2 fun hL => hx₀ne ?_
      exact hpointed x₀ hx₀.2.1 hL
    refine ⟨calib L W x₀, hc, fun x hx => ?_⟩
    by_cases hx0 : x = 0
    · rw [hx0, norm_zero, mul_zero]
      exact calib_nonneg R L W hW (zero_mem_cone R L)
    · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hy : ‖x‖⁻¹ • x ∈ S := by
        refine ⟨?_, cone_smul R L hx (inv_nonneg.mpr hnorm.le)⟩
        rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hnorm.ne']
      have h1 : calib L W x₀ ≤ calib L W (‖x‖⁻¹ • x) := hmin hy
      rw [calib_smul] at h1
      have h2 : calib L W x₀ * ‖x‖ ≤ ‖x‖⁻¹ * calib L W x * ‖x‖ :=
        mul_le_mul_of_nonneg_right h1 hnorm.le
      rwa [inv_mul_eq_div, div_mul_cancel₀ _ hnorm.ne'] at h2
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    by_cases hx0 : x = 0
    · rw [hx0, norm_zero, mul_zero]
      exact calib_nonneg R L W hW (zero_mem_cone R L)
    · exfalso
      have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      refine hne ⟨‖x‖⁻¹ • x, ?_, cone_smul R L hx (inv_nonneg.mpr hnorm.le)⟩
      rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hnorm.ne']

/-- **(RG.3e)**: on the pointed quotient the base is compact. -/
theorem base_isCompact (hW : ∀ j, (W j).PosDef)
    (hpointed : ∀ x ∈ LinearMap.ker R, (∀ j, L j x = 0) → x = 0) :
    IsCompact (base R L W) := by
  obtain ⟨c, hc, hdom⟩ := exists_calib_ge_norm R L W hW hpointed
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_base R L W) ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨c⁻¹, fun x hx => ?_⟩
  have h := hdom x hx.1
  rw [hx.2] at h
  rw [← one_div, le_div_iff₀ hc, mul_comm]
  exact h

/-- **`thm:SM-operational-cone`**: (RG.3c) `𝒦 ∩ (-𝒦) = E₀ ∩ ker 𝓛`; (RG.3d) for positive definite
calibrations the functional `ν` is nonnegative on `𝒦` and strictly positive off the writer
kernel; (RG.3e) the base is convex and, on the pointed quotient, compact. -/
theorem sm_operational_cone (hW : ∀ j, (W j).PosDef) :
    cone R L ∩ -cone R L = writerKer R L ∧
      (∀ x ∈ cone R L, 0 ≤ calib L W x) ∧
      (∀ x ∈ cone R L, (¬ ∀ j, L j x = 0) → 0 < calib L W x) ∧
      Convex ℝ (base R L W) ∧
      ((∀ x ∈ LinearMap.ker R, (∀ j, L j x = 0) → x = 0) → IsCompact (base R L W)) :=
  ⟨cone_inter_neg R L, fun _ hx => calib_nonneg R L W hW hx,
    fun _ hx hx' => calib_pos R L W hW hx hx', base_convex R L W,
    fun hpointed => base_isCompact R L W hW hpointed⟩

end OperationalCone
end NCG
