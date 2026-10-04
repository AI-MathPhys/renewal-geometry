/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Structural reductions for the finite rational detuning
  (`lem:supp-exact-rational-detuning`, `eq:supp-exact-cosine-defect`,
  `eq:supp-exact-diagonal-source`, `eq:supp-exact-diagonal-margin`;
  emergent-spacetime manuscript, Appendix `supp:exact-action-audit`)

The lemma asserts: for every sufficiently fine odd cutoff `N = 1/h` there is a rational
`θ ∈ (1, 1 + h)` such that, with `α = (1, θ, 1)`, the diagonal lapse source
`𝒟_{h,α} n = ((α₂D₂ − α₃D₃)n, (α₃D₃ − α₁D₁)n, (α₁D₁ − α₂D₂)n)` satisfies
`‖𝒟 n‖ ≥ c h⁶ ‖n‖` on mean-zero `n`, where `D_i` is the one-dimensional cosine product-defect
operator `D_h u = δ(fu) − f δu − (δf) u`, `f = cos 2πx`, acting along axis `i`.  The paper's
proof has three steps; this file proves the two structural ones in general and isolates the
remaining quantitative spectral input.

* **Tensor-eigenbasis step** (`tensor_margin`, `tensor_margin_hermitian`): for any real symmetric
  `D` whose kernel is the constants, if the eigenvalues satisfy the separation
  `|λ_a − θ λ_b| ≥ ε` whenever `(λ_a, λ_b) ≠ (0,0)`, then
  `ε² ‖n‖² ≤ ‖(θD₂ − D₃)n‖² + ‖(D₃ − D₁)n‖² + ‖(D₁ − θD₂)n‖²` for every `n` on the
  three-dimensional grid with zero sum.  (Proof: Kronecker conjugation by the orthogonal
  eigenvector matrix diagonalizes the three components simultaneously.)
* **Ratio-set step** (`exists_rat_separated`): if `Σ_a Σ_{b : λ_b ≠ 0} 4ε/|λ_b| < h` and
  `|λ| ≥ ε` for every nonzero eigenvalue, then some rational `θ ∈ (1, 1+h)` has the separation
  (measure of the bad ratio set, then a rational sufficiently close to a good point).
* **Assembly** (`detuning_margin_of_reciprocal_sum`): if `ker D = constants` and
  `Σ_{λ_a ≠ 0} 1/|λ_a| ≤ C h⁻³`, `N h = 1`, `4 C h < 1`, `C h³ ≤ 1`, then there is a rational
  `θ ∈ (1, 1 + h)` with `‖𝒟_{(1,θ,1)} n‖² ≥ (h⁶)² ‖n‖²` on zero-sum `n`.
* `cosineDefect N` is the paper's operator `D_h` (`eq:supp-exact-cosine-defect`) with the odd-grid
  phase derivative `δ` of `eq:supp-exact-phase-derivative` (`phaseDeriv`); `cosineDefect_symm`
  shows it is symmetric.

**Not proved (the remaining spectral lemma):** for all sufficiently large odd `N`,
`ker D_h = constants` and `Σ_{λ ≠ 0} 1/|λ| = O(h⁻³)` for the eigenvalues of `cosineDefect N`
(`CosineDefectSpectralInput`).  With it, `rational_detuning_of_spectralInput` gives the lemma.
-/

namespace RenewalGeometry
namespace RationalDetuning

open Matrix Finset MeasureTheory
open scoped Kronecker

noncomputable section

/-! ## The tensor-eigenbasis step -/

section Tensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `D` acting along the first axis of `(ι × ι) × ι`. -/
def axis₁ (D : Matrix ι ι ℝ) : Matrix ((ι × ι) × ι) ((ι × ι) × ι) ℝ := (D ⊗ₖ 1) ⊗ₖ 1
/-- `D` acting along the second axis. -/
def axis₂ (D : Matrix ι ι ℝ) : Matrix ((ι × ι) × ι) ((ι × ι) × ι) ℝ := (1 ⊗ₖ D) ⊗ₖ 1
/-- `D` acting along the third axis. -/
def axis₃ (D : Matrix ι ι ℝ) : Matrix ((ι × ι) × ι) ((ι × ι) × ι) ℝ := (1 ⊗ₖ 1) ⊗ₖ D

/-- The squared norm of `𝒟_{(1,θ,1)} n` (`eq:supp-exact-diagonal-source` with `α = (1,θ,1)`). -/
def sourceNormSq (D : Matrix ι ι ℝ) (θ : ℝ) (n : (ι × ι) × ι → ℝ) : ℝ :=
  let v₁ := (θ • axis₂ D - axis₃ D) *ᵥ n
  let v₂ := (axis₃ D - axis₁ D) *ᵥ n
  let v₃ := (axis₁ D - θ • axis₂ D) *ᵥ n
  v₁ ⬝ᵥ v₁ + v₂ ⬝ᵥ v₂ + v₃ ⬝ᵥ v₃

omit [Fintype ι] [DecidableEq ι] in
/-- An orthogonal matrix preserves the dot-product square. -/
theorem dotProduct_mulVec_self_of_orth {κ : Type*} [Fintype κ] [DecidableEq κ]
    {K : Matrix κ κ ℝ} (hK : Kᵀ * K = 1) (y : κ → ℝ) : (K *ᵥ y) ⬝ᵥ (K *ᵥ y) = y ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hK, one_mulVec]

omit [Fintype ι] [DecidableEq ι] in
/-- If `Kᵀ M K = diag w` with `K` orthogonal, then `‖M n‖² = Σ w² (Kᵀn)²`. -/
theorem normSq_of_conj_diag {κ : Type*} [Fintype κ] [DecidableEq κ] {K M : Matrix κ κ ℝ}
    (hK : Kᵀ * K = 1) (hK' : K * Kᵀ = 1) (w : κ → ℝ) (hM : Kᵀ * M * K = diagonal w)
    (n : κ → ℝ) :
    (M *ᵥ n) ⬝ᵥ (M *ᵥ n) = ∑ i, w i ^ 2 * (Kᵀ *ᵥ n) i ^ 2 := by
  have hMeq : M = K * diagonal w * Kᵀ := by
    rw [← hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hK', Matrix.one_mul, Matrix.mul_assoc,
      hK', Matrix.mul_one]
  have : M *ᵥ n = K *ᵥ (diagonal w *ᵥ (Kᵀ *ᵥ n)) := by
    rw [hMeq, mulVec_mulVec, mulVec_mulVec]
  rw [this, dotProduct_mulVec_self_of_orth hK]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

variable (U : Matrix ι ι ℝ) (lam : ι → ℝ)

/-- The Kronecker cube `K = U ⊗ U ⊗ U`. -/
def kron3 : Matrix ((ι × ι) × ι) ((ι × ι) × ι) ℝ := (U ⊗ₖ U) ⊗ₖ U

variable {U}

theorem kron3_orth (hU : Uᵀ * U = 1) : (kron3 U)ᵀ * kron3 U = 1 := by
  simp only [kron3, ← kroneckerMap_transpose, ← mul_kronecker_mul, hU, one_kronecker_one]

theorem kron3_orth' (hU : U * Uᵀ = 1) : kron3 U * (kron3 U)ᵀ = 1 := by
  simp only [kron3, ← kroneckerMap_transpose, ← mul_kronecker_mul, hU, one_kronecker_one]

variable {D : Matrix ι ι ℝ}

theorem conj_diag (hU : Uᵀ * U = 1) (hDU : D * U = U * diagonal lam) :
    Uᵀ * D * U = diagonal lam := by
  rw [Matrix.mul_assoc, hDU, ← Matrix.mul_assoc, hU, Matrix.one_mul]

omit [DecidableEq ι] in
theorem kron3_conj (A B C : Matrix ι ι ℝ) :
    (kron3 U)ᵀ * ((A ⊗ₖ B) ⊗ₖ C) * kron3 U
      = ((Uᵀ * A * U) ⊗ₖ (Uᵀ * B * U)) ⊗ₖ (Uᵀ * C * U) := by
  rw [kron3, ← kroneckerMap_transpose, ← kroneckerMap_transpose, ← mul_kronecker_mul,
    ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]

theorem conj_one (hU : Uᵀ * U = 1) : Uᵀ * (1 : Matrix ι ι ℝ) * U = diagonal fun _ => 1 := by
  rw [Matrix.mul_one, hU, diagonal_one]

theorem kron3_conj_axis₁ (hU : Uᵀ * U = 1) (hDU : D * U = U * diagonal lam) :
    (kron3 U)ᵀ * axis₁ D * kron3 U = diagonal fun p => lam p.1.1 := by
  rw [axis₁, kron3_conj, conj_diag lam hU hDU, conj_one hU, diagonal_kronecker_diagonal,
    diagonal_kronecker_diagonal]
  congr 1; funext p; ring

theorem kron3_conj_axis₂ (hU : Uᵀ * U = 1) (hDU : D * U = U * diagonal lam) :
    (kron3 U)ᵀ * axis₂ D * kron3 U = diagonal fun p => lam p.1.2 := by
  rw [axis₂, kron3_conj, conj_diag lam hU hDU, conj_one hU, diagonal_kronecker_diagonal,
    diagonal_kronecker_diagonal]
  congr 1; funext p; ring

theorem kron3_conj_axis₃ (hU : Uᵀ * U = 1) (hDU : D * U = U * diagonal lam) :
    (kron3 U)ᵀ * axis₃ D * kron3 U = diagonal fun p => lam p.2 := by
  rw [axis₃, kron3_conj, conj_diag lam hU hDU, conj_one hU, diagonal_kronecker_diagonal,
    diagonal_kronecker_diagonal]
  congr 1; funext p; ring

/-- **Tensor-eigenbasis step** (abstract form).  Let `D U = U diag λ` with `U` orthogonal and
`ker D = constants`.  If `|λ_a − θ λ_b| ≥ ε` whenever `(λ_a, λ_b) ≠ (0,0)`, then on zero-sum `n`,
`ε² ‖n‖² ≤ ‖𝒟_{(1,θ,1)} n‖²`. -/
theorem tensor_margin (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hDU : D * U = U * diagonal lam)
    (hker : ∀ v : ι → ℝ, D *ᵥ v = 0 → ∃ c, v = fun _ => c) {θ ε : ℝ} (hε : 0 ≤ ε)
    (hsep : ∀ a b, (lam a ≠ 0 ∨ lam b ≠ 0) → ε ≤ |lam a - θ * lam b|)
    (n : (ι × ι) × ι → ℝ) (hn : ∑ p, n p = 0) :
    ε ^ 2 * (n ⬝ᵥ n) ≤ sourceNormSq D θ n := by
  set K := kron3 U
  have hK := kron3_orth hU
  have hK' := kron3_orth' hU'
  have h1 := kron3_conj_axis₁ lam hU hDU
  have h2 := kron3_conj_axis₂ lam hU hDU
  have h3 := kron3_conj_axis₃ lam hU hDU
  have hc : ∀ (M₁ M₂ : Matrix ((ι × ι) × ι) ((ι × ι) × ι) ℝ) (c : ℝ),
      Kᵀ * (c • M₁ - M₂) * K = c • (Kᵀ * M₁ * K) - Kᵀ * M₂ * K := by
    intro M₁ M₂ c
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e1 : Kᵀ * (θ • axis₂ D - axis₃ D) * K
      = diagonal fun p => θ * lam p.1.2 - lam p.2 := by
    rw [hc, h2, h3, ← diagonal_smul, diagonal_sub]; rfl
  have e2 : Kᵀ * (axis₃ D - axis₁ D) * K = diagonal fun p => lam p.2 - lam p.1.1 := by
    have := hc (axis₃ D) (axis₁ D) 1
    rw [one_smul, one_smul] at this
    rw [this, h3, h1, diagonal_sub]
  have e3 : Kᵀ * (axis₁ D - θ • axis₂ D) * K
      = diagonal fun p => lam p.1.1 - θ * lam p.1.2 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h1, h2,
      ← diagonal_smul, diagonal_sub]; rfl
  unfold sourceNormSq
  simp only
  rw [normSq_of_conj_diag hK hK' _ e1, normSq_of_conj_diag hK hK' _ e2,
    normSq_of_conj_diag hK hK' _ e3]
  rw [← dotProduct_mulVec_self_of_orth (K := Kᵀ) (by rw [transpose_transpose]; exact hK') n]
  -- now everything is in the coefficients `m = Kᵀ n`
  set m := Kᵀ *ᵥ n with hm
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  obtain ⟨⟨a, b⟩, c⟩ := p
  simp only
  by_cases hab : lam a ≠ 0 ∨ lam b ≠ 0
  · have hs := hsep a b hab
    have : ε ^ 2 ≤ (lam a - θ * lam b) ^ 2 :=
      calc ε ^ 2 ≤ |lam a - θ * lam b| ^ 2 := pow_le_pow_left₀ hε hs 2
        _ = _ := sq_abs _
    linarith [mul_le_mul_of_nonneg_right this (sq_nonneg (m ((a, b), c))),
      mul_nonneg (sq_nonneg (θ * lam b - lam c)) (sq_nonneg (m ((a, b), c))),
      mul_nonneg (sq_nonneg (lam c - lam a)) (sq_nonneg (m ((a, b), c)))]
  · push Not at hab
    obtain ⟨ha, hb⟩ := hab
    by_cases hcz : lam c = 0
    · -- all three eigenvalues vanish: the coefficient is `0` by the zero-sum condition
      have hcol : ∀ d, lam d = 0 → ∃ k, (fun x => U x d) = fun _ => k := by
        intro d hd
        apply hker
        funext x
        have := congrFun (congrFun hDU x) d
        simp only [Matrix.mul_apply, diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true] at this
        simp only [mulVec, dotProduct, Pi.zero_apply]
        rw [this, hd, mul_zero]
      obtain ⟨ka, hka⟩ := hcol a ha
      obtain ⟨kb, hkb⟩ := hcol b hb
      obtain ⟨kc, hkc⟩ := hcol c hcz
      have hm0 : m ((a, b), c) = 0 := by
        rw [hm]
        simp only [mulVec, dotProduct, transpose_apply, K, kron3, kroneckerMap_apply]
        have : ∀ q : (ι × ι) × ι, U q.1.1 a * U q.1.2 b * U q.2 c * n q = ka * kb * kc * n q := by
          intro q
          rw [show U q.1.1 a = ka from congrFun hka q.1.1, show U q.1.2 b = kb from
            congrFun hkb q.1.2, show U q.2 c = kc from congrFun hkc q.2]
        rw [Finset.sum_congr rfl fun q _ => this q, ← Finset.mul_sum, hn, mul_zero]
      rw [hm0]; simp
    · have hs := hsep c b (Or.inl hcz)
      rw [hb, mul_zero, sub_zero] at hs
      have : ε ^ 2 ≤ lam c ^ 2 :=
        calc ε ^ 2 ≤ |lam c| ^ 2 := pow_le_pow_left₀ hε hs 2
          _ = _ := sq_abs _
      rw [ha, hb]
      linarith [mul_le_mul_of_nonneg_right this (sq_nonneg (m ((a, b), c))),
        mul_nonneg (sq_nonneg (θ * 0 - lam c)) (sq_nonneg (m ((a, b), c))),
        mul_nonneg (sq_nonneg ((0 : ℝ) - θ * 0)) (sq_nonneg (m ((a, b), c)))]

/-- **Tensor-eigenbasis step** for a real symmetric matrix, with its spectral decomposition. -/
theorem tensor_margin_hermitian (hD : D.IsHermitian)
    (hker : ∀ v : ι → ℝ, D *ᵥ v = 0 → ∃ c, v = fun _ => c) {θ ε : ℝ} (hε : 0 ≤ ε)
    (hsep : ∀ a b, (hD.eigenvalues a ≠ 0 ∨ hD.eigenvalues b ≠ 0) →
      ε ≤ |hD.eigenvalues a - θ * hD.eigenvalues b|)
    (n : (ι × ι) × ι → ℝ) (hn : ∑ p, n p = 0) :
    ε ^ 2 * (n ⬝ᵥ n) ≤ sourceNormSq D θ n := by
  set U : Matrix ι ι ℝ := (hD.eigenvectorUnitary : Matrix ι ι ℝ)
  have hmem := hD.eigenvectorUnitary.2
  have hU' : U * Uᵀ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).1 hmem
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hU : Uᵀ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').1 hmem
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hDU : D * U = U * diagonal hD.eigenvalues := by
    ext x a
    have := congrFun (hD.mulVec_eigenvectorBasis a) x
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [U, IsHermitian.eigenvectorUnitary_apply]
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    ring
  exact tensor_margin hD.eigenvalues hU hU' hDU hker hε hsep n hn

end Tensor

/-! ## The ratio-set step -/

section Ratio

variable {ι : Type*} [Fintype ι]

/-- **Ratio-set step.**  If `Σ_a Σ_{b : λ_b ≠ 0} 4ε/|λ_b| < h` and every nonzero eigenvalue has
`|λ| ≥ ε`, then there is a rational `θ ∈ (1, 1 + h)` with `|λ_a − θ λ_b| ≥ ε` whenever
`(λ_a, λ_b) ≠ (0,0)`. -/
theorem exists_rat_separated (lam : ι → ℝ) {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h)
    (hsum : ∑ _a : ι, ∑ b, (if lam b = 0 then 0 else 4 * ε / |lam b|) < h)
    (hmin : ∀ a, lam a ≠ 0 → ε ≤ |lam a|) :
    ∃ θ : ℚ, 1 < (θ : ℝ) ∧ (θ : ℝ) < 1 + h ∧
      ∀ a b, (lam a ≠ 0 ∨ lam b ≠ 0) → ε ≤ |lam a - θ * lam b| := by
  classical
  -- the bad ratio set
  set bad : Set ℝ := ⋃ a, ⋃ b ∈ Finset.univ.filter (fun b => lam b ≠ 0),
    Metric.ball (lam a / lam b) (2 * ε / |lam b|) with hbad
  have hvol : volume bad < volume (Set.Ioo (1 : ℝ) (1 + h)) := by
    rw [Real.volume_Ioo, show 1 + h - 1 = h by ring]
    calc volume bad
        ≤ ∑ a, volume (⋃ b ∈ Finset.univ.filter (fun b => lam b ≠ 0),
            Metric.ball (lam a / lam b) (2 * ε / |lam b|)) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ a, ∑ b ∈ Finset.univ.filter (fun b => lam b ≠ 0),
            volume (Metric.ball (lam a / lam b) (2 * ε / |lam b|)) :=
          Finset.sum_le_sum fun a _ => measure_biUnion_finset_le _ _
      _ = ENNReal.ofReal (∑ a, ∑ b, (if lam b = 0 then 0 else 4 * ε / |lam b|)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => by
            split_ifs <;> positivity)]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => by split_ifs <;> positivity),
            Finset.sum_filter]
          refine Finset.sum_congr rfl fun b _ => ?_
          by_cases hb : lam b = 0
          · simp [hb]
          · simp only [hb, ne_eq, not_false_eq_true, ite_true, ite_false]
            rw [Real.volume_ball]; congr 1; ring
      _ < ENNReal.ofReal h := (ENNReal.ofReal_lt_ofReal_iff hh).2 hsum
  obtain ⟨θs, hθs, hθbad⟩ : (Set.Ioo (1 : ℝ) (1 + h) \ bad).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
    exact absurd (measure_mono hemp) (not_le.2 hvol)
  -- `θs` is `2ε`-separated
  have hsep2 : ∀ a b, lam b ≠ 0 → 2 * ε ≤ |lam a - θs * lam b| := by
    intro a b hb
    have hnot : θs ∉ Metric.ball (lam a / lam b) (2 * ε / |lam b|) := by
      intro hin
      exact hθbad (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion₂.2 ⟨b, by simp [hb], hin⟩⟩)
    rw [Metric.mem_ball, not_lt, Real.dist_eq] at hnot
    have hbpos : 0 < |lam b| := abs_pos.2 hb
    have : lam a - θs * lam b = -(lam b) * (θs - lam a / lam b) := by field_simp; ring
    rw [this, abs_mul, abs_neg]
    rw [div_le_iff₀ hbpos] at hnot
    linarith
  -- a nearby rational
  set Mb := ∑ b, |lam b| + 1 with hMb
  have hMb0 : 0 < Mb := by
    have := Finset.sum_nonneg fun b (_ : b ∈ Finset.univ) => abs_nonneg (lam b); linarith
  have hle : ∀ b, |lam b| ≤ Mb := fun b => by
    have := Finset.single_le_sum (f := fun b => |lam b|) (fun b _ => abs_nonneg _)
      (Finset.mem_univ b)
    linarith
  set η := min (ε / Mb) (min (θs - 1) (1 + h - θs)) with hη
  have hη0 : 0 < η := lt_min (div_pos hε hMb0) (lt_min (by linarith [hθs.1]) (by linarith [hθs.2]))
  obtain ⟨θ, hθ1, hθ2⟩ := exists_rat_btwn (show θs - η < θs + η by linarith)
  have hdist : |(θ : ℝ) - θs| ≤ η := abs_le.2 ⟨by linarith, by linarith⟩
  refine ⟨θ, ?_, ?_, fun a b hab => ?_⟩
  · have := min_le_right (ε / Mb) (min (θs - 1) (1 + h - θs))
    have := min_le_left (θs - 1) (1 + h - θs)
    linarith
  · have := min_le_right (ε / Mb) (min (θs - 1) (1 + h - θs))
    have := min_le_right (θs - 1) (1 + h - θs)
    linarith
  · by_cases hb : lam b = 0
    · rw [hb, mul_zero, sub_zero]
      exact hmin a (hab.resolve_right (not_not.2 hb))
    · have h2 := hsep2 a b hb
      have hη' : η * Mb ≤ ε := by
        have := min_le_left (ε / Mb) (min (θs - 1) (1 + h - θs))
        rw [le_div_iff₀ hMb0] at this; linarith
      have hdiff : |((θ : ℝ) - θs) * lam b| ≤ ε := by
        rw [abs_mul]
        calc |(θ : ℝ) - θs| * |lam b| ≤ η * Mb :=
              mul_le_mul hdist (hle b) (abs_nonneg _) hη0.le
          _ ≤ ε := hη'
      have : lam a - θ * lam b = (lam a - θs * lam b) - ((θ : ℝ) - θs) * lam b := by ring
      rw [this]
      have := abs_sub_abs_le_abs_sub (lam a - θs * lam b) (((θ : ℝ) - θs) * lam b)
      linarith

end Ratio

/-! ## Assembly -/

section Assembly

variable {N : ℕ}

/-- **Assembly of `lem:supp-exact-rational-detuning` from the spectral input.**  Let `D` be a real
symmetric `N × N` matrix with `ker D = constants` and reciprocal-eigenvalue sum
`Σ_{λ_a ≠ 0} 1/|λ_a| ≤ C h⁻³`, where `N h = 1`, `4 C h < 1` and `C h³ ≤ 1`.  Then there is a
rational `θ ∈ (1, 1 + h)` such that, for `α = (1, θ, 1)`, every zero-sum `n` on the grid satisfies
`‖𝒟_{h,α} n‖² ≥ (h⁶)² ‖n‖²` (`eq:supp-exact-diagonal-margin` with `c = 1`). -/
theorem detuning_margin_of_reciprocal_sum (D : Matrix (Fin N) (Fin N) ℝ) (hD : D.IsHermitian)
    (hker : ∀ v : Fin N → ℝ, D *ᵥ v = 0 → ∃ c, v = fun _ => c) {C h : ℝ} (hh : 0 < h)
    (hNh : (N : ℝ) * h = 1)
    (hrec : ∑ a, (if hD.eigenvalues a = 0 then 0 else 1 / |hD.eigenvalues a|) ≤ C / h ^ 3)
    (hC1 : 4 * C * h < 1) (hC2 : C * h ^ 3 ≤ 1) :
    ∃ θ : ℚ, 1 < (θ : ℝ) ∧ (θ : ℝ) < 1 + h ∧
      ∀ n : (Fin N × Fin N) × Fin N → ℝ, ∑ p, n p = 0 →
        (h ^ 6) ^ 2 * (n ⬝ᵥ n) ≤ sourceNormSq D θ n := by
  set lam := hD.eigenvalues
  have hε : 0 < h ^ 6 := by positivity
  have hrec0 : ∀ a, lam a ≠ 0 → 1 / |lam a| ≤ C / h ^ 3 := by
    intro a ha
    refine le_trans ?_ hrec
    have := Finset.single_le_sum (f := fun a => if lam a = 0 then 0 else 1 / |lam a|)
      (fun a _ => by split_ifs <;> positivity) (Finset.mem_univ a)
    simpa [ha] using this
  have hmin : ∀ a, lam a ≠ 0 → h ^ 6 ≤ |lam a| := by
    intro a ha
    have hpos : 0 < |lam a| := abs_pos.2 ha
    have h1 := hrec0 a ha
    have hC : 0 < C := by
      have : 0 < 1 / |lam a| := by positivity
      have := this.trans_le h1
      exact (div_pos_iff_of_pos_right (by positivity)).1 this
    -- `|λ| ≥ h³ / C ≥ h⁶`
    rw [div_le_div_iff₀ hpos (by positivity), one_mul] at h1
    have e1 := mul_le_mul_of_nonneg_left h1 (pow_pos hh 3).le
    have e2 := mul_le_mul_of_nonneg_right hC2 hpos.le
    have e3 : h ^ 6 = h ^ 3 * (1 * h ^ 3) := by ring
    have e4 : h ^ 3 * (C * |lam a|) = C * h ^ 3 * |lam a| := by ring
    linarith
  have hsum : ∑ _a : Fin N, ∑ b, (if lam b = 0 then 0 else 4 * h ^ 6 / |lam b|) < h := by
    have hinner : ∀ a : Fin N, ∑ b, (if lam b = 0 then 0 else 4 * h ^ 6 / |lam b|)
        = 4 * h ^ 6 * ∑ b, (if lam b = 0 then 0 else 1 / |lam b|) := by
      intro a
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun a _ => hinner a), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hS0 : 0 ≤ ∑ b, (if lam b = 0 then 0 else 1 / |lam b|) :=
      Finset.sum_nonneg fun b _ => by split_ifs <;> positivity
    have hN : (N : ℝ) = 1 / h := by field_simp; linarith
    calc (N : ℝ) * (4 * h ^ 6 * ∑ b, (if lam b = 0 then 0 else 1 / |lam b|))
        ≤ (1 / h) * (4 * h ^ 6 * (C / h ^ 3)) := by
          rw [hN]; gcongr
      _ = 4 * C * h * h := by field_simp
      _ < 1 * h := mul_lt_mul_of_pos_right hC1 hh
      _ = h := one_mul h
  obtain ⟨θ, hθ1, hθ2, hsep⟩ := exists_rat_separated lam hε hh hsum hmin
  exact ⟨θ, hθ1, hθ2, fun n hn => tensor_margin_hermitian hD hker hε.le hsep n hn⟩

end Assembly

/-! ## The cosine product-defect operator -/

section Cosine

/-- The odd-grid phase derivative `δ` (`eq:supp-exact-phase-derivative`,
`(δu)^(k) = iκ(k) û(k)`, `κ(k) = 2h⁻¹ sin(πhk)`, `|k| ≤ m`, `N = 2m + 1`) in real space:
`δ_{xy} = −4 Σ_{k=1}^{m} sin(πk/N) sin(2πk(x−y)/N)`. -/
def phaseDeriv (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := fun x y =>
  -4 * ∑ k ∈ Finset.Icc 1 ((N - 1) / 2),
    Real.sin (Real.pi * k / N) * Real.sin (2 * Real.pi * k * ((x : ℝ) - y) / N)

/-- The grid cosine `f(x_j) = cos(2π j/N)`. -/
def gridCos (N : ℕ) : Fin N → ℝ := fun x => Real.cos (2 * Real.pi * x / N)

/-- The cosine product-defect operator `D_h u = δ(fu) − f δu − (δf) u`
(`eq:supp-exact-cosine-defect`). -/
def cosineDefect (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  phaseDeriv N * diagonal (gridCos N) - diagonal (gridCos N) * phaseDeriv N
    - diagonal (phaseDeriv N *ᵥ gridCos N)

theorem phaseDeriv_transpose (N : ℕ) : (phaseDeriv N)ᵀ = -phaseDeriv N := by
  ext x y
  simp only [transpose_apply, phaseDeriv, Matrix.neg_apply]
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show 2 * Real.pi * k * ((y : ℝ) - x) / N = -(2 * Real.pi * k * ((x : ℝ) - y) / N) by ring,
    Real.sin_neg]
  ring

/-- `D_h` is symmetric. -/
theorem cosineDefect_symm (N : ℕ) : (cosineDefect N).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  simp only [cosineDefect, transpose_sub, transpose_mul, diagonal_transpose,
    phaseDeriv_transpose, Matrix.neg_mul, Matrix.mul_neg]
  abel

/-- **The remaining spectral lemma** for `lem:supp-exact-rational-detuning` at cutoff `N`
(`h = 1/N`), with constant `C`: the kernel of `D_h` is the constants and
`Σ_{λ ≠ 0} 1/|λ| ≤ C h⁻³` over the eigenvalues of `D_h` (with multiplicity). -/
def CosineDefectSpectralInput (N : ℕ) (C : ℝ) : Prop :=
  (∀ v : Fin N → ℝ, cosineDefect N *ᵥ v = 0 → ∃ c, v = fun _ => c) ∧
  ∑ a, (if (cosineDefect_symm N).eigenvalues a = 0 then 0
    else 1 / |(cosineDefect_symm N).eigenvalues a|) ≤ C * (N : ℝ) ^ 3

/-- **`lem:supp-exact-rational-detuning` from the spectral input.**  If the spectral input holds
with a constant `C` at every sufficiently fine odd cutoff, then at every odd cutoff with
`4 C < N` and `C ≤ N³` there is a rational `θ_h ∈ (1, 1 + h)` such that for `α_h = (1, θ_h, 1)`
the diagonal lapse source of `eq:supp-exact-diagonal-source` (with `D_i = D_h` along axis `i`)
satisfies `‖𝒟_{h,α_h} n‖² ≥ (h⁶)² ‖n‖²` for all mean-zero `n`. -/
theorem rational_detuning_of_spectralInput {N : ℕ} {C : ℝ} (hN : 0 < N)
    (hspec : CosineDefectSpectralInput N C) (hC1 : 4 * C < N) (hC2 : C ≤ (N : ℝ) ^ 3) :
    ∃ θ : ℚ, 1 < (θ : ℝ) ∧ (θ : ℝ) < 1 + 1 / N ∧
      ∀ n : (Fin N × Fin N) × Fin N → ℝ, ∑ p, n p = 0 →
        ((1 / (N : ℝ)) ^ 6) ^ 2 * (n ⬝ᵥ n) ≤ sourceNormSq (cosineDefect N) θ n := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  refine detuning_margin_of_reciprocal_sum (cosineDefect N) (cosineDefect_symm N) hspec.1
    (C := C) (by positivity) (by field_simp) ?_ ?_ ?_
  · have := hspec.2
    rw [div_pow, one_pow, div_div_eq_mul_div, div_one]
    exact this
  · rw [mul_one_div, div_lt_one hNpos]; linarith
  · rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]; exact hC2

theorem cosineDefect_one : cosineDefect 1 = 0 := by
  have h0 : phaseDeriv 1 = 0 := by
    ext x y; simp [phaseDeriv]
  simp [cosineDefect, h0]

/-- Non-vacuity of the spectral-input packet (degenerate cutoff `N = 1`, where `D_h = 0`); the
assembly theorem `rational_detuning_of_spectralInput` then applies with `C = 0`. -/
example : CosineDefectSpectralInput 1 0 := by
  have hz : ∀ a, (cosineDefect_symm 1).eigenvalues a = 0 := by
    have := (cosineDefect_symm 1).eigenvalues_eq_zero_iff.2 cosineDefect_one
    exact fun a => congrFun this a
  refine ⟨fun v _ => ⟨v 0, funext fun x => by rw [Subsingleton.elim x 0]⟩, ?_⟩
  simp [hz]

example : ∃ θ : ℚ, 1 < (θ : ℝ) ∧ (θ : ℝ) < 1 + 1 / (1 : ℕ) ∧
    ∀ n : (Fin 1 × Fin 1) × Fin 1 → ℝ, ∑ p, n p = 0 →
      ((1 / ((1 : ℕ) : ℝ)) ^ 6) ^ 2 * (n ⬝ᵥ n) ≤ sourceNormSq (cosineDefect 1) θ n := by
  have hz : ∀ a, (cosineDefect_symm 1).eigenvalues a = 0 := by
    have := (cosineDefect_symm 1).eigenvalues_eq_zero_iff.2 cosineDefect_one
    exact fun a => congrFun this a
  exact rational_detuning_of_spectralInput (C := 0) Nat.one_pos
    ⟨fun v _ => ⟨v 0, funext fun x => by rw [Subsingleton.elim x 0]⟩, by simp [hz]⟩
    (by norm_num) (by norm_num)

end Cosine

end

end RationalDetuning
end RenewalGeometry
