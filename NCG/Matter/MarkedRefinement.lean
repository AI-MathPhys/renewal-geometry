/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Rank-one marked-refinement rigidity
  (`thm:rank-one-marked-refinement-main`, SM_emergence)

A marked instrument refining a rank-one channel is a scalar
splitting of it:

* `rank_one_sum_vector_rigidity` — positive rank-one decompositions
  are collinear: `Σ_m w_m w_m† = v v†` forces every `w_m ∈ ℂ·v`;
* `rank_one_kraus_rigidity` — if `Σ_m R_m ρ R_m† = R ρ R†` for all
  `ρ` with `R ≠ 0`, then `R_m = c_m R` with `Σ|c_m|² = 1`;
* `marked_refinement_effect` — hence `Σ_m R_m†R_m = R†R`: mark
  resolution cannot change any eigenvalue ratio of the source
  effect.
-/

namespace NCG

open Matrix Complex

variable {d : Type*} [Fintype d]
variable {ι : Type*} [Fintype ι]

/-- The sesquilinear pairing `⟨a, u⟩ = Σ conj(a i)·u i`. -/
noncomputable def cip (a u : d → ℂ) : ℂ := star a ⬝ᵥ u

private theorem star_mul_self_normSq (z : ℂ) :
    star z * z = (Complex.normSq z : ℂ) := by
  rw [show (star z : ℂ) = (starRingEnd ℂ) z from rfl,
    mul_comm ((starRingEnd ℂ) z) z]
  exact Complex.mul_conj z

/-- Quadratic evaluation of a rank-one operator. -/
theorem rank_one_quadratic (a u : d → ℂ) :
    star u ⬝ᵥ (Matrix.vecMulVec a (star a)).mulVec u
      = (Complex.normSq (cip a u) : ℂ) := by
  have h1 : (Matrix.vecMulVec a (star a)).mulVec u
      = (cip a u) • a := by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
      cip, Pi.smul_apply, smul_eq_mul, Pi.star_apply]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, dotProduct_smul]
  have h2 : star u ⬝ᵥ a = starRingEnd ℂ (cip a u) := by
    simp only [dotProduct, cip, Pi.star_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [mul_comm]
  rw [smul_eq_mul, h2]
  exact Complex.mul_conj _

/-- Sums of complex `normSq` casts vanish only termwise. -/
theorem sum_normSq_cast_eq_zero {z : ι → ℂ}
    (h : (∑ m, (Complex.normSq (z m) : ℂ)) = 0) : ∀ m, z m = 0 := by
  have hreal : (∑ m, Complex.normSq (z m)) = 0 := by
    exact_mod_cast h
  intro m
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Complex.normSq_nonneg (z i))).mp hreal m
    (Finset.mem_univ m)
  exact Complex.normSq_eq_zero.mp hterm

omit [Fintype d] in
/-- Positive rank-one decompositions are collinear. -/
theorem rank_one_sum_vector_rigidity [Finite d]
    (w : ι → (d → ℂ)) (v : d → ℂ)
    (h : (∑ m, Matrix.vecMulVec (w m) (star (w m)))
      = Matrix.vecMulVec v (star v)) :
    ∀ m, ∃ c : ℂ, w m = c • v := by
  cases nonempty_fintype d
  classical
  -- the quadratic identity
  have hquad : ∀ u : d → ℂ,
      (∑ m, (Complex.normSq (cip (w m) u) : ℂ))
        = (Complex.normSq (cip v u) : ℂ) := by
    intro u
    have := congrArg (fun M : Matrix d d ℂ =>
      star u ⬝ᵥ M.mulVec u) h
    rw [rank_one_quadratic] at this
    rw [← this]
    rw [show (∑ m, Matrix.vecMulVec (w m) (star (w m))).mulVec u
      = ∑ m, (Matrix.vecMulVec (w m) (star (w m))).mulVec u from by
        rw [Matrix.sum_mulVec]]
    rw [dotProduct_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [rank_one_quadratic]
  -- orthogonality transfer
  have horth : ∀ u : d → ℂ, cip v u = 0 → ∀ m, cip (w m) u = 0 := by
    intro u hu m
    have := hquad u
    rw [hu] at this
    simp only [Complex.normSq_zero, Complex.ofReal_zero] at this
    exact sum_normSq_cast_eq_zero this m
  by_cases hv : v = 0
  · -- degenerate: everything vanishes
    intro m
    refine ⟨0, ?_⟩
    have hzero : (∑ m, Matrix.vecMulVec (w m) (star (w m))) = 0 := by
      rw [h, hv]
      ext i j
      simp [Matrix.vecMulVec_apply]
    have hdiag := congrArg (fun M : Matrix d d ℂ =>
      star (w m) ⬝ᵥ M.mulVec (w m)) hzero
    simp only [Matrix.zero_mulVec, dotProduct_zero] at hdiag
    rw [show star (w m) ⬝ᵥ (∑ k, Matrix.vecMulVec (w k)
        (star (w k))).mulVec (w m)
      = ∑ k, (Complex.normSq (cip (w k) (w m)) : ℂ) from by
        rw [Matrix.sum_mulVec, dotProduct_sum]
        exact Finset.sum_congr rfl fun k _ =>
          rank_one_quadratic (w k) (w m)] at hdiag
    have hall := sum_normSq_cast_eq_zero hdiag m
    -- ⟨w_m, w_m⟩ = 0 forces w_m = 0
    have : (∑ i, Complex.normSq (w m i)) = 0 := by
      have hcip : cip (w m) (w m)
          = ∑ i, (Complex.normSq (w m i) : ℂ) := by
        simp only [cip, dotProduct, Pi.star_apply]
        apply Finset.sum_congr rfl
        intro i _
        exact star_mul_self_normSq _
      rw [hcip] at hall
      exact_mod_cast hall
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Complex.normSq_nonneg (w m i))).mp this i
      (Finset.mem_univ i)
    simpa using Complex.normSq_eq_zero.mp this
  · -- nondegenerate: project onto `v`
    intro m
    have hvv : cip v v ≠ 0 := by
      intro h0
      apply hv
      have hcip : cip v v = ∑ i, (Complex.normSq (v i) : ℂ) := by
        simp only [cip, dotProduct, Pi.star_apply]
        apply Finset.sum_congr rfl
        intro i _
        exact star_mul_self_normSq _
      rw [hcip] at h0
      have : (∑ i, Complex.normSq (v i)) = 0 := by
        exact_mod_cast h0
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Complex.normSq_nonneg (v i))).mp this i
        (Finset.mem_univ i)
      simpa using Complex.normSq_eq_zero.mp this
    set c : ℂ := cip v (w m) / cip v v with hc
    refine ⟨c, ?_⟩
    set u0 : d → ℂ := w m - c • v with hu0
    have hvu0 : cip v u0 = 0 := by
      have hexp : cip v u0 = cip v (w m) - c * cip v v := by
        rw [hu0]
        simp only [cip, dotProduct, Pi.sub_apply, Pi.smul_apply,
          Pi.star_apply, smul_eq_mul]
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hexp, hc]
      field_simp
      ring
    have hwu0 := horth u0 hvu0 m
    -- ⟨u₀, u₀⟩ = ⟨w_m, u₀⟩ - conj c·⟨v, u₀⟩ = 0
    have hself : cip u0 u0 = 0 := by
      have hexp : ∀ x : d → ℂ,
          cip u0 x = cip (w m) x - star c * cip v x := by
        intro x
        rw [hu0]
        simp only [cip, dotProduct, Pi.sub_apply, Pi.smul_apply,
          Pi.star_apply, smul_eq_mul, star_sub, star_mul']
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hexp u0, hwu0, hvu0, mul_zero, sub_zero]
    -- hence `u₀ = 0`
    have hu0zero : u0 = 0 := by
      have hcip : cip u0 u0 = ∑ i, (Complex.normSq (u0 i) : ℂ) := by
        simp only [cip, dotProduct, Pi.star_apply]
        apply Finset.sum_congr rfl
        intro i _
        exact star_mul_self_normSq _
      rw [hcip] at hself
      have : (∑ i, Complex.normSq (u0 i)) = 0 := by
        exact_mod_cast hself
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Complex.normSq_nonneg (u0 i))).mp this i
        (Finset.mem_univ i)
      simpa using Complex.normSq_eq_zero.mp this
    have := hu0
    rw [hu0zero] at this
    linear_combination (norm := module) -this

private theorem mul_star_self_normSq (z : ℂ) :
    z * star z = (Complex.normSq z : ℂ) := by
  rw [mul_comm]
  exact star_mul_self_normSq z

/-- Conjugating a dyad `u·w†` by matrices transports the vectors. -/
private theorem conj_pair (A : Matrix d d ℂ) (u w : d → ℂ) :
    A * Matrix.vecMulVec u (star w) * Aᴴ
      = Matrix.vecMulVec (A.mulVec u) (star (A.mulVec w)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.star_mulVec]

/-- `thm:rank-one-marked-refinement-main` (rigidity): a Kraus family
refining a rank-one channel is a scalar splitting of it. -/
theorem rank_one_kraus_rigidity
    (Rm : ι → Matrix d d ℂ) (R : Matrix d d ℂ) (hR : R ≠ 0)
    (h : ∀ ρ : Matrix d d ℂ,
      ∑ m, Rm m * ρ * (Rm m)ᴴ = R * ρ * Rᴴ) :
    ∃ c : ι → ℂ, (∀ m, Rm m = c m • R)
      ∧ ∑ m, Complex.normSq (c m) = 1 := by
  classical
  have hsingle : ∀ (A : Matrix d d ℂ) (j : d),
      A.mulVec (Pi.single j 1) = fun i => A i j := by
    intro A j
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply,
      Finset.sum_ite_eq']
  -- Choi-matrix equality on the doubled index space
  have hchoi : (∑ m, Matrix.vecMulVec
        (fun p : d × d => Rm m p.1 p.2)
        (star fun p : d × d => Rm m p.1 p.2))
      = Matrix.vecMulVec (fun p : d × d => R p.1 p.2)
        (star fun p : d × d => R p.1 p.2) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    have h1 := h (Matrix.vecMulVec (Pi.single j 1)
      (star (Pi.single l (1 : ℂ))))
    simp only [conj_pair, hsingle] at h1
    have h2 := congrArg (fun M : Matrix d d ℂ => M i k) h1
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply,
      Pi.star_apply] at h2
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply,
      Pi.star_apply] using h2
  obtain ⟨c, hc⟩ := Classical.axiomOfChoice
    (rank_one_sum_vector_rigidity
      (fun m => fun p : d × d => Rm m p.1 p.2)
      (fun p : d × d => R p.1 p.2) hchoi)
  have hRm : ∀ m, Rm m = c m • R := by
    intro m
    ext i j
    have := congrFun (hc m) (i, j)
    simpa [Matrix.smul_apply] using this
  refine ⟨c, hRm, ?_⟩
  -- normalization from a nonvanishing entry of `R`
  obtain ⟨i0, j0, hij⟩ : ∃ i j, R i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hR (by ext i j; simpa using hcon i j)
  have hentry := congrArg
    (fun M : Matrix (d × d) (d × d) ℂ => M (i0, j0) (i0, j0)) hchoi
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply,
    Pi.star_apply] at hentry
  have hmm : ∀ m, Rm m i0 j0 = c m * R i0 j0 := by
    intro m
    rw [hRm m]
    simp [Matrix.smul_apply]
  simp only [hmm, mul_star_self_normSq, Complex.normSq_mul]
    at hentry
  have hre : (∑ m, Complex.normSq (c m)
      * Complex.normSq (R i0 j0)) = Complex.normSq (R i0 j0) := by
    exact_mod_cast hentry
  have hz : Complex.normSq (R i0 j0) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hij
  rw [← Finset.sum_mul] at hre
  exact mul_right_cancel₀ hz (hre.trans (one_mul _).symm)

/-- `thm:rank-one-marked-refinement-main` (effect identity): the
refined instrument reproduces the source effect,
`Σ_m R_m†R_m = R†R`. -/
theorem marked_refinement_effect
    (Rm : ι → Matrix d d ℂ) (R : Matrix d d ℂ) (hR : R ≠ 0)
    (h : ∀ ρ : Matrix d d ℂ,
      ∑ m, Rm m * ρ * (Rm m)ᴴ = R * ρ * Rᴴ) :
    ∑ m, (Rm m)ᴴ * Rm m = Rᴴ * R := by
  obtain ⟨c, hc, hnorm⟩ := rank_one_kraus_rigidity Rm R hR h
  calc ∑ m, (Rm m)ᴴ * Rm m
      = ∑ m, (Complex.normSq (c m) : ℂ) • (Rᴴ * R) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [hc m, Matrix.conjTranspose_smul, Matrix.smul_mul,
          Matrix.mul_smul, smul_smul]
        congr 1
        exact star_mul_self_normSq _
  _ = ((∑ m, Complex.normSq (c m) : ℝ) : ℂ) • (Rᴴ * R) := by
        rw [← Finset.sum_smul]
        norm_cast
  _ = Rᴴ * R := by
        rw [hnorm]
        norm_num

end NCG
