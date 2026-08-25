/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Physical recurrent-flow minimax

Machinery for `thm:GT-physical-circulation-minimax`.  On a recurrent component with edge set
`E`, vertex set `V`, oriented incidence `∂ : Matrix V E ℝ` and assembled current vectors
`q e ∈ ℝ^d`, the normalized circulation polytope is
`𝒵 = {z ≥ 0 : ∂ z = 0, ∑ z = 1}` (GW.2) and `Q z = ∑ₑ zₑ q e`.  For a compact convex physical
coefficient set `Λ ∋ 0` the payoff `λᵀ Q z` is bilinear, so Sion's minimax theorem
(`Sion.exists_isSaddlePointOn`) yields a saddle point `(z*, λ*)` whose value `m = λ*ᵀ Q z*` is
the physical recurrent margin `max_λ min_z λᵀ Q z` (GW.3).

* (R1) if `m > 0`, the loaded current `λ*` has strictly positive mean on every circulation;
* (R2) if `m = 0`, the circulation `z*` satisfies `λᵀ Q z* ≤ 0` for every `λ ∈ Λ` (GW.4); if `Λ`
  is centrally symmetric and contains a neighbourhood of `0` in a represented span containing
  `Q z*`, then `Q z* = 0`.
-/

open Matrix Finset

namespace NCG
namespace CirculationMinimax

variable {V E : Type*} [Fintype V] [Fintype E] {d : ℕ}

/-- (GW.2) the normalized circulation polytope `{z ≥ 0 : ∂ z = 0, ∑ z = 1}`. -/
def circulations (inc : Matrix V E ℝ) : Set (E → ℝ) :=
  {z | (∀ e, 0 ≤ z e) ∧ inc *ᵥ z = 0 ∧ ∑ e, z e = 1}

/-- The assembled current of a circulation, `Q z = ∑ₑ zₑ q e`. -/
def assembled (q : E → Fin d → ℝ) (z : E → ℝ) : Fin d → ℝ :=
  (Matrix.of fun i e => q e i) *ᵥ z

/-- The payoff `λᵀ Q z`. -/
def payoff (q : E → Fin d → ℝ) (z : E → ℝ) (lam : Fin d → ℝ) : ℝ :=
  lam ⬝ᵥ assembled q z

theorem assembled_apply (q : E → Fin d → ℝ) (z : E → ℝ) (i : Fin d) :
    assembled q z i = ∑ e, z e * q e i := by
  simp [assembled, mulVec, dotProduct, mul_comm]

omit [Fintype V] in
theorem payoff_eq_sum (q : E → Fin d → ℝ) (z : E → ℝ) (lam : Fin d → ℝ) :
    payoff q z lam = ∑ e, z e * (lam ⬝ᵥ q e) := by
  simp only [payoff, dotProduct, assembled_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### Structure of the circulation polytope -/

omit [Fintype V] in
theorem convex_circulations (inc : Matrix V E ℝ) : Convex ℝ (circulations inc) := by
  intro z hz w hw a b ha hb hab
  refine ⟨fun e => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hz.1 e)) (mul_nonneg hb (hw.1 e))
  · rw [mulVec_add, mulVec_smul, mulVec_smul, hz.2.1, hw.2.1, smul_zero, smul_zero, add_zero]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hz.2.2, hw.2.2, mul_one, hab]

omit [Fintype V] in
theorem isClosed_circulations (inc : Matrix V E ℝ) : IsClosed (circulations inc) := by
  have h : circulations inc = (⋂ e, {z : E → ℝ | 0 ≤ z e}) ∩ {z | inc *ᵥ z = 0} ∩
      {z | ∑ e, z e = 1} := by
    ext z
    simp [circulations, Set.mem_iInter, and_assoc]
  rw [h]
  refine ((isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)).inter
    (isClosed_eq (continuous_const.matrix_mulVec continuous_id) continuous_const)).inter
    (isClosed_eq (continuous_finsetSum _ fun e _ => continuous_apply e) continuous_const)

omit [Fintype V] in
theorem norm_le_one_of_mem_circulations (inc : Matrix V E ℝ) {z : E → ℝ}
    (hz : z ∈ circulations inc) : ‖z‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro e
  rw [Real.norm_eq_abs, abs_of_nonneg (hz.1 e)]
  calc z e = ∑ e' ∈ {e}, z e' := by simp
    _ ≤ ∑ e', z e' := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun e' _ _ => hz.1 e'
    _ = 1 := hz.2.2

omit [Fintype V] in
theorem isCompact_circulations (inc : Matrix V E ℝ) : IsCompact (circulations inc) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_circulations inc)
    (isBounded_iff_forall_norm_le.mpr ⟨1, fun _ hz => norm_le_one_of_mem_circulations inc hz⟩)

/-! ### Bilinearity of the payoff -/

omit [Fintype V] in
/-- The payoff as a linear map in the circulation. -/
def payoffLinZ (q : E → Fin d → ℝ) (lam : Fin d → ℝ) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun z := payoff q z lam
  map_add' z w := by simp [payoff, assembled, mulVec_add, dotProduct_add]
  map_smul' c z := by simp [payoff, assembled, mulVec_smul, dotProduct_smul]

omit [Fintype V] in
/-- The payoff as a linear map in the coefficient. -/
def payoffLinLam (q : E → Fin d → ℝ) (z : E → ℝ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun lam := payoff q z lam
  map_add' lam mu := by simp [payoff, add_dotProduct]
  map_smul' c lam := by simp [payoff, smul_dotProduct]

omit [Fintype V] in
theorem continuous_payoff_z (q : E → Fin d → ℝ) (lam : Fin d → ℝ) :
    Continuous fun z : E → ℝ => payoff q z lam :=
  continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)

omit [Fintype V] in
theorem continuous_payoff_lam (q : E → Fin d → ℝ) (z : E → ℝ) :
    Continuous fun lam : Fin d → ℝ => payoff q z lam :=
  continuous_id.dotProduct continuous_const

/-! ### The minimax alternative -/

variable (inc : Matrix V E ℝ) (q : E → Fin d → ℝ) (Λ : Set (Fin d → ℝ))

omit [Fintype V] in
/-- **(GW.3) via Sion**: the bilinear payoff on the compact convex polytopes `𝒵` and `Λ` has a
saddle point `(z*, λ*)`: `λᵀ Q z* ≤ λ*ᵀ Q z* ≤ λ*ᵀ Q z` for all `λ ∈ Λ`, `z ∈ 𝒵`.  Its value is
the physical recurrent margin `max_λ min_z λᵀ Q z`. -/
theorem exists_saddle (hZ : (circulations inc).Nonempty) (hΛc : Convex ℝ Λ) (hΛk : IsCompact Λ)
    (hΛne : Λ.Nonempty) :
    ∃ zs ∈ circulations inc, ∃ ls ∈ Λ,
      ∀ z ∈ circulations inc, ∀ lam ∈ Λ, payoff q zs lam ≤ payoff q z ls := by
  have h := Sion.exists_isSaddlePointOn (f := fun z lam => payoff q z lam) hZ
    (convex_circulations inc) (isCompact_circulations inc)
    (fun lam _ => (continuous_payoff_z q lam).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun lam _ => ((payoffLinZ q lam).convexOn (convex_circulations inc)).quasiconvexOn)
    hΛc hΛne hΛk
    (fun z _ => (continuous_payoff_lam q z).upperSemicontinuous.upperSemicontinuousOn _)
    (fun z _ => ((payoffLinLam q z).concaveOn hΛc).quasiconcaveOn)
  obtain ⟨zs, hzs, ls, hls, hsaddle⟩ := h
  exact ⟨zs, hzs, ls, hls, fun z hz lam hlam => hsaddle z hz lam hlam⟩

omit [Fintype V] in
/-- The saddle value is `max_λ min_z`: `λ*` maximizes the minimum (attained at `z*`) and every
`λ` has minimum at most `m`. -/
theorem saddle_is_max_min {zs : E → ℝ} {ls : Fin d → ℝ} (hzs : zs ∈ circulations inc)
    (hls : ls ∈ Λ)
    (hsaddle : ∀ z ∈ circulations inc, ∀ lam ∈ Λ, payoff q zs lam ≤ payoff q z ls) :
    (∀ z ∈ circulations inc, payoff q zs ls ≤ payoff q z ls) ∧
      ∀ lam ∈ Λ, ∃ z ∈ circulations inc, payoff q z lam ≤ payoff q zs ls :=
  ⟨fun z hz => hsaddle z hz ls hls, fun lam hlam => ⟨zs, hzs, hsaddle zs hzs lam hlam⟩⟩

omit [Fintype V] in
/-- **(R1)**: a positive margin is witnessed by one loaded current with strictly positive mean on
every recurrent circulation. -/
theorem positive_branch {zs : E → ℝ} {ls : Fin d → ℝ} (hls : ls ∈ Λ)
    (hsaddle : ∀ z ∈ circulations inc, ∀ lam ∈ Λ, payoff q zs lam ≤ payoff q z ls)
    (hm : 0 < payoff q zs ls) : ∀ z ∈ circulations inc, 0 < payoff q z ls :=
  fun z hz => lt_of_lt_of_le hm (hsaddle z hz ls hls)

omit [Fintype V] in
/-- **(R2), (GW.4)**: a zero margin is witnessed by one circulation `z*` with
`λᵀ Q z* ≤ 0` for every physical coefficient. -/
theorem zero_branch {zs : E → ℝ} {ls : Fin d → ℝ} (hzs : zs ∈ circulations inc)
    (hsaddle : ∀ z ∈ circulations inc, ∀ lam ∈ Λ, payoff q zs lam ≤ payoff q z ls)
    (hm : payoff q zs ls = 0) : ∀ lam ∈ Λ, payoff q zs lam ≤ 0 :=
  fun lam hlam => (hsaddle zs hzs lam hlam).trans_eq hm

omit [Fintype V] in
/-- The zero-branch support function vanishes at the admitted zero coefficient:
`max_λ λᵀ Q z* = 0`. -/
theorem zero_branch_sup {zs : E → ℝ} {ls : Fin d → ℝ} (hzs : zs ∈ circulations inc)
    (hsaddle : ∀ z ∈ circulations inc, ∀ lam ∈ Λ, payoff q zs lam ≤ payoff q z ls)
    (hm : payoff q zs ls = 0) :
    (∀ lam ∈ Λ, payoff q zs lam ≤ 0) ∧ payoff q zs 0 = 0 :=
  ⟨zero_branch inc q Λ hzs hsaddle hm, by simp [payoff]⟩

omit [Fintype V] in
/-- **(R2), symmetric case**: if `Λ` contains a neighbourhood of `0` in a represented span
`W ∋ Q z*` (as it does when it is centrally symmetric around such a neighbourhood), then
`Q z* = 0`. -/
theorem assembled_eq_zero_of_symmetric {zs : E → ℝ}
    (W : Submodule ℝ (Fin d → ℝ)) (hW : assembled q zs ∈ W)
    (hball : ∃ ε > 0, ∀ w ∈ W, ‖w‖ < ε → w ∈ Λ)
    (hle : ∀ lam ∈ Λ, payoff q zs lam ≤ 0) : assembled q zs = 0 := by
  obtain ⟨ε, hε, hball⟩ := hball
  by_contra hne
  have hnorm : 0 < ‖assembled q zs‖ := norm_pos_iff.mpr hne
  set t : ℝ := ε / (2 * ‖assembled q zs‖) with ht
  have htpos : 0 < t := div_pos hε (by positivity)
  have hmem : t • assembled q zs ∈ Λ := by
    refine hball _ (W.smul_mem t hW) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht, div_mul_eq_mul_div,
      div_lt_iff₀ (by positivity)]
    nlinarith
  have h1 := hle _ hmem
  have hpay : payoff q zs (t • assembled q zs) = t * (assembled q zs ⬝ᵥ assembled q zs) := by
    rw [payoff, smul_dotProduct, smul_eq_mul]
  have hself : 0 < assembled q zs ⬝ᵥ assembled q zs := by
    have hnn : 0 ≤ assembled q zs ⬝ᵥ assembled q zs :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg (assembled q zs i)
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hne
  rw [hpay] at h1
  have : 0 < t * (assembled q zs ⬝ᵥ assembled q zs) := mul_pos htpos hself
  linarith

omit [Fintype V] in
/-- **`thm:GT-physical-circulation-minimax`**: for a nonempty circulation polytope and a compact
convex physical coefficient set containing `0`, there is a saddle point `(z*, λ*)` whose value
`m = λ*ᵀ Q z*` is the recurrent margin `max_λ min_z λᵀ Q z`, and (R1) if `m > 0` the current
`λ*` has strictly positive mean on every circulation, (R2) if `m = 0` then `λᵀ Q z* ≤ 0` for
every `λ ∈ Λ` (GW.4) with support value `0`, and under central symmetry plus a represented
neighbourhood of `0` containing `Q z*` one has `Q z* = 0`. -/
theorem physical_circulation_minimax (hZ : (circulations inc).Nonempty) (hΛc : Convex ℝ Λ)
    (hΛk : IsCompact Λ) (h0 : (0 : Fin d → ℝ) ∈ Λ) :
    ∃ zs ∈ circulations inc, ∃ ls ∈ Λ,
      (∀ z ∈ circulations inc, ∀ lam ∈ Λ, payoff q zs lam ≤ payoff q z ls) ∧
      (∀ z ∈ circulations inc, payoff q zs ls ≤ payoff q z ls) ∧
      (∀ lam ∈ Λ, ∃ z ∈ circulations inc, payoff q z lam ≤ payoff q zs ls) ∧
      (0 < payoff q zs ls → ∀ z ∈ circulations inc, 0 < payoff q z ls) ∧
      (payoff q zs ls = 0 → (∀ lam ∈ Λ, payoff q zs lam ≤ 0) ∧ payoff q zs 0 = 0 ∧
        ((∀ lam ∈ Λ, -lam ∈ Λ) → ∀ W : Submodule ℝ (Fin d → ℝ), assembled q zs ∈ W →
          (∃ ε > 0, ∀ w ∈ W, ‖w‖ < ε → w ∈ Λ) → assembled q zs = 0)) := by
  obtain ⟨zs, hzs, ls, hls, hsaddle⟩ := exists_saddle inc q Λ hZ hΛc hΛk ⟨0, h0⟩
  refine ⟨zs, hzs, ls, hls, hsaddle, fun z hz => hsaddle z hz ls hls,
    fun lam hlam => ⟨zs, hzs, hsaddle zs hzs lam hlam⟩,
    fun hm => positive_branch inc q Λ hls hsaddle hm, fun hm => ?_⟩
  refine ⟨zero_branch inc q Λ hzs hsaddle hm, by simp [payoff], fun _ W hW hball => ?_⟩
  exact assembled_eq_zero_of_symmetric q Λ W hW hball (zero_branch inc q Λ hzs hsaddle hm)

end CirculationMinimax
end NCG
