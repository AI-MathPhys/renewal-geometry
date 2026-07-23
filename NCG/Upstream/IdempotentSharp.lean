/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# The sharp self-adjoint idempotentization bound

Covers `cor:selfadjoint-idempotentization` from `manuscripts/renewal_emergence/renewal_emergence.tex`:
for a symmetric operator `T` on a finite-dimensional inner product
space with `‖T² − T‖ ≤ δ < 1/4`, the spectral threshold projection
`P = 1_{[1/2,∞)}(T)` is a symmetric idempotent commuting with `T`
with the sharp Hilbert-space bound

`‖P − T‖ ≤ α_H(δ) = (1 − √(1 − 4δ))/2`,

and the constant is attained by the scalar operator with spectrum at
the endpoint of the forbidden interval around `1/2`.
-/

namespace NCG.Upstream

open Finset

section Scalar

/-- The scalar threshold distance bound: a real number whose
quadratic defect is at most `δ < 1/4` lies within
`α_H(δ) = (1 − √(1−4δ))/2` of `{0, 1}`, on the side selected by the
`1/2` threshold. -/
theorem threshold_bound {μ δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 4)
    (hμ : |μ ^ 2 - μ| ≤ δ) :
    |(if (1 : ℝ) / 2 ≤ μ then (1 : ℝ) else 0) - μ|
      ≤ (1 - Real.sqrt (1 - 4 * δ)) / 2 := by
  set s : ℝ := Real.sqrt (1 - 4 * δ) with hs_def
  have hw : (0 : ℝ) < 1 - 4 * δ := by linarith
  have hs2 : s ^ 2 = 1 - 4 * δ := Real.sq_sqrt hw.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hw
  have hs1 : s ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show 1 - 4 * δ ≤ 1 by linarith)
    rwa [Real.sqrt_one] at h
  have hup : μ ^ 2 - μ ≤ δ := (abs_le.mp hμ).2
  have hlo : -δ ≤ μ ^ 2 - μ := (abs_le.mp hμ).1
  by_cases hthr : (1 : ℝ) / 2 ≤ μ
  · rw [if_pos hthr]
    rw [abs_le]
    constructor
    · -- −α ≤ 1 − μ: via s' = √(1+4δ) and s + s' ≤ 2
      set s' : ℝ := Real.sqrt (1 + 4 * δ) with hs'_def
      have hs'2 : s' ^ 2 = 1 + 4 * δ :=
        Real.sq_sqrt (by linarith)
      have hs'0 : 0 ≤ s' := Real.sqrt_nonneg _
      have hss' : s * s' ≤ 1 := by
        have h4 : s * s' = Real.sqrt ((1 - 4 * δ) * (1 + 4 * δ)) :=
          (Real.sqrt_mul hw.le _).symm
        have h4b := Real.sqrt_le_sqrt
          (show (1 - 4 * δ) * (1 + 4 * δ) ≤ 1 by nlinarith)
        rw [Real.sqrt_one] at h4b
        rw [h4]
        exact h4b
      have hsum : s + s' ≤ 2 := by
        have h5 : (s + s') ^ 2 ≤ 4 := by nlinarith
        nlinarith [hs0.le, hs'0]
      have h6 : (2 * μ - 1) ^ 2 ≤ s' ^ 2 := by
        rw [hs'2]
        nlinarith
      have h7 : 2 * μ - 1 ≤ s' := by
        by_contra hc
        push_neg at hc
        nlinarith
      linarith
    · -- 1 − μ ≤ α: from (2μ−1)² ≥ s² and 2μ−1 ≥ 0
      have h1 : (2 * μ - 1) ^ 2 ≥ s ^ 2 := by
        rw [hs2]
        nlinarith
      have h2 : 0 ≤ 2 * μ - 1 := by linarith
      have h3 : s ≤ 2 * μ - 1 := by
        by_contra hc
        push_neg at hc
        nlinarith
      linarith
  · rw [if_neg hthr]
    push_neg at hthr
    rw [abs_le]
    constructor
    · -- −α ≤ −μ, i.e. μ ≤ α: from (1−2μ)² ≥ s², 1−2μ > 0
      have h1 : (1 - 2 * μ) ^ 2 ≥ s ^ 2 := by
        rw [hs2]
        nlinarith
      have h2 : 0 < 1 - 2 * μ := by linarith
      have h3 : s ≤ 1 - 2 * μ := by
        by_contra hc
        push_neg at hc
        nlinarith
      linarith
    · -- 0 − μ ≤ α, i.e. −μ ≤ α: only needs work for μ < 0
      rcases le_or_gt 0 μ with hpos | hneg
      · linarith [hs1]
      · set t : ℝ := -μ with ht_def
        have ht0 : 0 < t := by rw [ht_def]; linarith
        have htq : t ^ 2 + t ≤ δ := by
          have : μ ^ 2 - μ = t ^ 2 + t := by rw [ht_def]; ring
          linarith
        set α : ℝ := (1 - s) / 2 with hα_def
        have hα0 : 0 ≤ α := by
          rw [hα_def]
          linarith
        have hαδ : α * (1 - α) = δ := by
          rw [hα_def]
          nlinarith [hs2]
        have h8 : t ≤ α := by
          by_contra hc
          push_neg at hc
          nlinarith
        rw [ht_def] at h8
        rw [hα_def] at h8
        linarith
end Scalar

section Sharpness

/-- **Corollary `cor:selfadjoint-idempotentization` (sharpness)**:
the constant `α_H(δ)` is attained by the scalar with spectrum at the
lower endpoint of the forbidden interval. -/
theorem threshold_sharp {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 4) :
    ∃ μ : ℝ, |μ ^ 2 - μ| ≤ δ
      ∧ |(if (1 : ℝ) / 2 ≤ μ then (1 : ℝ) else 0) - μ|
        = (1 - Real.sqrt (1 - 4 * δ)) / 2 := by
  set s : ℝ := Real.sqrt (1 - 4 * δ) with hs_def
  have hw : (0 : ℝ) < 1 - 4 * δ := by linarith
  have hs2 : s ^ 2 = 1 - 4 * δ := Real.sq_sqrt hw.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hw
  have hs1 : s ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show 1 - 4 * δ ≤ 1 by linarith)
    rwa [Real.sqrt_one] at h
  set t : ℝ := (1 - s) / 2 with ht_def
  have ht0 : 0 ≤ t := by rw [ht_def]; linarith
  have ht_half : t < 1 / 2 := by
    rw [ht_def]
    linarith
  have htδ : t * (1 - t) = δ := by
    rw [ht_def]
    nlinarith [hs2]
  refine ⟨t, ?_, ?_⟩
  · have h1 : t ^ 2 - t = -δ := by nlinarith [htδ]
    rw [h1, abs_neg, abs_of_nonneg hδ0]
  · rw [if_neg (by linarith), abs_sub_comm, sub_zero,
      abs_of_nonneg ht0, ht_def]

end Sharpness

/-! ## The operator corollary -/

section Operator

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 V)

/-- The operator that acts diagonally in the orthonormal basis `b`
with coefficients `c`. -/
noncomputable def diagOp (c : Fin n → 𝕜) : V →ₗ[𝕜] V where
  toFun x := ∑ i, (c i * ⟪b i, x⟫) • b i
  map_add' x y := by
    simp only [inner_add_right, mul_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [inner_smul_right, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    ring

theorem diagOp_apply (c : Fin n → 𝕜) (x : V) :
    diagOp b c x = ∑ i, (c i * ⟪b i, x⟫) • b i := rfl

theorem inner_basis_sum (a : Fin n → 𝕜) (i : Fin n) :
    ⟪b i, ∑ j, a j • b j⟫ = a i := by
  rw [inner_sum]
  rw [Finset.sum_eq_single i]
  · rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
      if_pos rfl, mul_one]
  · intro j _ hj
    rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
      if_neg (Ne.symm hj), mul_zero]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

theorem diagOp_comp (c d : Fin n → 𝕜) :
    diagOp b c ∘ₗ diagOp b d = diagOp b fun i => c i * d i := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, diagOp_apply, diagOp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_basis_sum]
  congr 1
  ring

theorem diagOp_isSymmetric (c : Fin n → 𝕜)
    (hc : ∀ i, (starRingEnd 𝕜) (c i) = c i) :
    (diagOp b c).IsSymmetric := by
  intro x y
  rw [diagOp_apply, diagOp_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_smul_right]
  rw [map_mul, hc i, ← inner_conj_symm x (b i)]
  ring

/-- Parseval-type computation: the squared norm of an orthonormal
expansion. -/
theorem norm_sq_sum_smul (a : Fin n → 𝕜) :
    ‖∑ i, a i • b i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  have h1 : (⟪∑ i, a i • b i, ∑ j, a j • b j⟫ : 𝕜)
      = ∑ i, (starRingEnd 𝕜) (a i) * a i := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, inner_basis_sum]
  have h2 := congrArg RCLike.re h1
  rw [inner_self_eq_norm_sq] at h2
  rw [h2, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.conj_mul]
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]

theorem parseval (x : V) : ∑ i, ‖(⟪b i, x⟫ : 𝕜)‖ ^ 2 = ‖x‖ ^ 2 := by
  have h1 := norm_sq_sum_smul b fun i => (⟪b i, x⟫ : 𝕜)
  rw [b.sum_repr'] at h1
  exact h1.symm

/-- The diagonal operator bound by the largest coefficient. -/
theorem diagOp_norm_le (c : Fin n → 𝕜) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, ‖c i‖ ≤ M) (x : V) :
    ‖diagOp b c x‖ ≤ M * ‖x‖ := by
  have h1 : ‖diagOp b c x‖ ^ 2 = ∑ i, ‖c i * ⟪b i, x⟫‖ ^ 2 := by
    rw [diagOp_apply]
    exact norm_sq_sum_smul b _
  have h2 : ∑ i, ‖c i * (⟪b i, x⟫ : 𝕜)‖ ^ 2
      ≤ M ^ 2 * ∑ i, ‖(⟪b i, x⟫ : 𝕜)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, mul_pow]
    have h3 : ‖c i‖ ^ 2 ≤ M ^ 2 := by
      have := hM i
      nlinarith [norm_nonneg (c i)]
    nlinarith [sq_nonneg ‖(⟪b i, x⟫ : 𝕜)‖]
  rw [parseval] at h2
  have h4 : ‖diagOp b c x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [h1, mul_pow]
    exact h2
  have h5 : 0 ≤ M * ‖x‖ := mul_nonneg hM0 (norm_nonneg _)
  nlinarith [norm_nonneg (diagOp b c x), h4, h5]

variable {T : V →ₗ[𝕜] V}

/-- The spectral theorem in diagonal form. -/
theorem isSymmetric_eq_diagOp (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 V = n) :
    T = diagOp (hT.eigenvectorBasis hn)
      fun i => ((hT.eigenvalues hn i : ℝ) : 𝕜) := by
  apply LinearMap.ext
  intro x
  conv_lhs => rw [← (hT.eigenvectorBasis hn).sum_repr' x]
  rw [map_sum, diagOp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, hT.apply_eigenvectorBasis hn i,
    smul_smul]
  congr 1
  ring

/-- **Corollary `cor:selfadjoint-idempotentization`**: for a
symmetric operator with quadratic defect at most `δ < 1/4`, the
spectral threshold projection at `1/2` is a symmetric idempotent
commuting with `T`, at distance at most
`α_H(δ) = (1 − √(1−4δ))/2` — the sharp constant. -/
theorem selfadjoint_idempotentization (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 V = n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 1 / 4)
    (hnorm : ∀ x : V, ‖(T ∘ₗ T - T) x‖ ≤ δ * ‖x‖) :
    ∃ P : V →ₗ[𝕜] V, P ∘ₗ P = P ∧ P ∘ₗ T = T ∘ₗ P
      ∧ P.IsSymmetric
      ∧ ∀ x : V, ‖(P - T) x‖
        ≤ (1 - Real.sqrt (1 - 4 * δ)) / 2 * ‖x‖ := by
  set bb := hT.eigenvectorBasis hn with hbb
  set μ := hT.eigenvalues hn with hμ
  -- eigenvalue defect bound
  have hev : ∀ i, |μ i ^ 2 - μ i| ≤ δ := by
    intro i
    have h1 : (T ∘ₗ T - T) (bb i)
        = ((((μ i : ℝ) ^ 2 - μ i : ℝ)) : 𝕜) • bb i := by
      rw [LinearMap.sub_apply, LinearMap.comp_apply,
        hT.apply_eigenvectorBasis hn i, LinearMap.map_smul,
        hT.apply_eigenvectorBasis hn i, smul_smul]
      rw [show ((((μ i : ℝ) ^ 2 - μ i : ℝ)) : 𝕜)
          = ((μ i : ℝ) : 𝕜) * ((μ i : ℝ) : 𝕜)
            - ((μ i : ℝ) : 𝕜) from by push_cast; ring]
      rw [sub_smul]
    have h2 := hnorm (bb i)
    rw [h1, norm_smul, RCLike.norm_ofReal,
      bb.orthonormal.1 i] at h2
    simpa using h2
  -- the threshold coefficients
  set χ : Fin n → 𝕜 := fun i =>
    if (1 : ℝ) / 2 ≤ μ i then (1 : 𝕜) else 0 with hχ
  refine ⟨diagOp bb χ, ?_, ?_, ?_, ?_⟩
  · rw [diagOp_comp]
    congr 1
    funext i
    simp only [hχ]
    split <;> simp
  · rw [isSymmetric_eq_diagOp hT hn, ← hbb, ← hμ, diagOp_comp,
      diagOp_comp]
    congr 1
    funext i
    ring
  · refine diagOp_isSymmetric bb χ fun i => ?_
    simp only [hχ]
    split <;> simp
  · intro x
    have hPT : diagOp bb χ - T
        = diagOp bb fun i => χ i - ((μ i : ℝ) : 𝕜) := by
      rw [isSymmetric_eq_diagOp hT hn, ← hbb, ← hμ]
      apply LinearMap.ext
      intro y
      rw [LinearMap.sub_apply, diagOp_apply, diagOp_apply,
        diagOp_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, ← sub_mul]
    rw [hPT]
    refine diagOp_norm_le bb _ ?_ (fun i => ?_) x
    · have h5 : Real.sqrt (1 - 4 * δ) ≤ 1 := by
        have h := Real.sqrt_le_sqrt
          (show 1 - 4 * δ ≤ 1 by linarith)
        rwa [Real.sqrt_one] at h
      linarith
    · have h6 : χ i - ((μ i : ℝ) : 𝕜)
          = (((if (1 : ℝ) / 2 ≤ μ i then (1 : ℝ) else 0)
            - μ i : ℝ) : 𝕜) := by
        simp only [hχ]
        split <;> push_cast <;> ring
      rw [h6, RCLike.norm_ofReal]
      exact threshold_bound hδ0 hδ (hev i)

end Operator

end NCG.Upstream
