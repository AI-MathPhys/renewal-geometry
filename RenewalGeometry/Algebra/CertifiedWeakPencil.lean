/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Certificate reductions for the weak first-Poisson block and the weak pencil
  (`thm:supp-certified-weak-rank`, `eq:supp-certified-K24`, `eq:supp-certified-pencil-factor`,
  `thm:supp-certified-rapid-spectrum`; emergent-spacetime manuscript, subsection
  `subsec:supp-exact-certified-rapid`)

The rank and spectral statements at the certified `N = 3` event are numerical certificates on
matrices obtained by differentiating the canonical Hamiltonian.  This file proves, in general,
the exact linear algebra that turns such certificates into the stated conclusions, so that only
the certificate data remain.

* **Row-sum (Neumann) certificate** (`det_ne_zero_of_rowsum`): if `Σ_j |(I − R K)_{ij}| ≤ q < 1`
  for every row `i` (i.e. `‖I − R K‖_∞ < 1`), then `K` is invertible.  This is the lower-bound
  certificate `‖I − R₂₄ K₂₄‖_∞ < 8.80·10⁻¹⁴` of `eq:supp-certified-K24`.
* **Rank from certificates** (`le_rank_of_principal`, `rank_le_sub_two`,
  `rank_eq_of_certificates`): an invertible `k × k` submatrix gives `rank K ≥ k`; two linearly
  independent kernel vectors give `rank K ≤ n − 2`; together, for an `(k+2) × (k+2)` matrix,
  `rank K = k` (the paper: `k = 24`, `n = 26`, rows/columns `2, 24` deleted).
* **Pencil factorization** (`pencil_det`, `eq:supp-certified-pencil-factor`): for
  `K_WW = diag(0_ℋ, K_g)` and `D_W = [[D_ℋℋ, D_ℋ𝒢], [D_𝒢ℋ, D_𝒢𝒢]]` with `D_ℋℋ` invertible,
  `det(K_WW + λ D_W) = λ^{dim ℋ} det D_ℋℋ det(K_g + λ D₂₆)`,
  `D₂₆ = D_𝒢𝒢 − D_𝒢ℋ D_ℋℋ⁻¹ D_ℋ𝒢` (Schur complement).
* **Spectral reduction** (`charDet_weak_generator`): with `B_W = −D_W⁻¹ K_WW` and
  `A_g = −D₂₆⁻¹ K_g`, `det(λ − B_W) = λ^{dim ℋ} det(λ − A_g)` for every `λ`: the spectrum of
  the full weak generator is that of `A_g` together with `dim ℋ` exact zeros (the constant
  shifts), with algebraic multiplicities.  Hence the counts `(8, 8, 10)` of `A_g` in the open
  right/left half-planes and on the imaginary axis give the algebraic counts `(8, 8, 13)` of
  `B_W` (`eq:supp-certified-8813`).

Not proved here: the numerical certificates themselves (the matrices `K_g`, `R₂₄`, `D_W` are
neither tabulated in the manuscript nor computable in Lean from it), and the semigroup bounds of
`eq:supp-certified-semigroup` (which additionally need semisimplicity of the central spectrum).
-/

namespace RenewalGeometry
namespace CertifiedWeakPencil

open Matrix

/-! ## Row-sum certificate and rank -/

section Rank

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Neumann row-sum certificate.**  If `‖I − R K‖_∞ ≤ q < 1` (every absolute row sum of
`I − R K` is at most `q`), then `det K ≠ 0`. -/
theorem det_ne_zero_of_rowsum (K R : Matrix n n ℝ) {q : ℝ} (hq : q < 1)
    (hrow : ∀ i, ∑ j, |(1 - R * K) i j| ≤ q) : K.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hKv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hfix : (1 - R * K) *ᵥ v = v := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hKv, mulVec_zero, sub_zero]
  have hne : (Finset.univ : Finset n).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at h
    exact hv0 (funext fun i => (h.false i).elim)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) hne
  have hle : |v i| ≤ q * |v i| := by
    calc |v i| = |((1 - R * K) *ᵥ v) i| := by rw [hfix]
      _ = |∑ j, (1 - R * K) i j * v j| := rfl
      _ ≤ ∑ j, |(1 - R * K) i j| * |v j| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun j _ => abs_mul _ _
      _ ≤ ∑ j, |(1 - R * K) i j| * |v i| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j))
            (abs_nonneg _)
      _ = (∑ j, |(1 - R * K) i j|) * |v i| := by rw [Finset.sum_mul]
      _ ≤ q * |v i| := mul_le_mul_of_nonneg_right (hrow i) (abs_nonneg _)
  have hvi : |v i| = 0 := by
    have h0 := abs_nonneg (v i)
    nlinarith
  apply hv0
  funext j
  have := hi j (Finset.mem_univ j)
  rw [hvi] at this
  exact abs_nonpos_iff.1 this

/-- An invertible `k × k` submatrix gives `rank K ≥ k`. -/
theorem le_rank_of_principal {m : Type*} [Fintype m] {k : ℕ} (K : Matrix m n ℝ)
    (r : Fin k → m) (c : Fin k → n) (h : (K.submatrix r c).det ≠ 0) : k ≤ K.rank := by
  have hu : IsUnit (K.submatrix r c) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have := Matrix.rank_of_isUnit _ hu
  rw [Fintype.card_fin] at this
  rw [← this]
  exact Matrix.rank_submatrix_le K r c

/-- Two linearly independent kernel vectors give `rank K ≤ card n − 2`. -/
theorem rank_le_sub_two (K : Matrix n n ℝ) (u w : n → ℝ) (hu : K *ᵥ u = 0) (hw : K *ᵥ w = 0)
    (hind : LinearIndependent ℝ ![u, w]) : K.rank ≤ Fintype.card n - 2 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker K.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hker : 2 ≤ Module.finrank ℝ (LinearMap.ker K.mulVecLin) := by
    have hsub : Submodule.span ℝ (Set.range ![u, w]) ≤ LinearMap.ker K.mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hu
      · exact hw
    have := Submodule.finrank_mono hsub
    rw [finrank_span_eq_card hind, Fintype.card_fin] at this
    exact this
  rw [Matrix.rank]
  omega

/-- **Rank from the two certificates**: for a `(k+2) × (k+2)` matrix, an invertible `k × k`
submatrix (e.g. certified by `det_ne_zero_of_rowsum`) and two independent kernel vectors give
`rank K = k`. -/
theorem rank_eq_of_certificates {k : ℕ} (K : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)
    (r c : Fin k → Fin (k + 2)) (R : Matrix (Fin k) (Fin k) ℝ) {q : ℝ} (hq : q < 1)
    (hrow : ∀ i, ∑ j, |(1 - R * K.submatrix r c) i j| ≤ q)
    (u w : Fin (k + 2) → ℝ) (hu : K *ᵥ u = 0) (hw : K *ᵥ w = 0)
    (hind : LinearIndependent ℝ ![u, w]) : K.rank = k := by
  have h1 := le_rank_of_principal K r c (det_ne_zero_of_rowsum _ R hq hrow)
  have h2 := rank_le_sub_two K u w hu hw hind
  rw [Fintype.card_fin] at h2
  omega

/-- Non-vacuity of the certificate packet: `diag(1, 0, 0)` has rank `1`, certified by the
`1 × 1` block `(1)` with `R = (1)` and the kernel vectors `e₁`, `e₂`. -/
example : (Matrix.diagonal ![(1 : ℝ), 0, 0]).rank = 1 := by
  refine rank_eq_of_certificates (k := 1) _ (fun _ => 0) (fun _ => 0) 1 (q := 0) (by norm_num)
    (fun i => by fin_cases i; simp [Matrix.submatrix, Matrix.one_apply]) ![0, 1, 0] ![0, 0, 1] ?_ ?_ ?_
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrFun hst 1
    have h2 := congrFun hst 2
    simp at h1 h2
    exact ⟨h1, h2⟩

end Rank

/-! ## The weak pencil -/

section Pencil

variable {h g : Type*} [Fintype h] [Fintype g] [DecidableEq h] [DecidableEq g]

/-- The Schur complement `D₂₆ = D_𝒢𝒢 − D_𝒢ℋ D_ℋℋ⁻¹ D_ℋ𝒢`. -/
noncomputable def schur (DHH : Matrix h h ℝ) (DHG : Matrix h g ℝ) (DGH : Matrix g h ℝ)
    (DGG : Matrix g g ℝ) : Matrix g g ℝ :=
  DGG - DGH * DHH⁻¹ * DHG

/-- **Pencil factorization** (`eq:supp-certified-pencil-factor`):
`det(diag(0, K_g) + λ D_W) = λ^{dim ℋ} det D_ℋℋ det(K_g + λ D₂₆)`. -/
theorem pencil_det (Kg : Matrix g g ℝ) (DHH : Matrix h h ℝ) (DHG : Matrix h g ℝ)
    (DGH : Matrix g h ℝ) (DGG : Matrix g g ℝ) (hD : DHH.det ≠ 0) (lam : ℝ) :
    (fromBlocks 0 0 0 Kg + lam • fromBlocks DHH DHG DGH DGG).det
      = lam ^ Fintype.card h * DHH.det * (Kg + lam • schur DHH DHG DGH DGG).det := by
  rw [fromBlocks_smul, fromBlocks_add, zero_add, zero_add, zero_add]
  by_cases hl : lam = 0
  · subst hl
    simp only [zero_smul, add_zero]
    rw [det_fromBlocks_zero₁₂]
    rcases isEmpty_or_nonempty h with hh | hh
    · simp [Fintype.card_eq_zero]
    · rw [det_zero, zero_pow Fintype.card_ne_zero]; ring
  · have hdet : (lam • DHH).det ≠ 0 := by
      rw [det_smul]; exact mul_ne_zero (pow_ne_zero _ hl) hD
    let _ : Invertible (lam • DHH) := (lam • DHH).invertibleOfIsUnitDet
      (isUnit_iff_ne_zero.2 hdet)
    have hinv : (lam • DHH)⁻¹ = lam⁻¹ • DHH⁻¹ := by
      have := Matrix.inv_smul' (Units.mk0 lam hl) (A := DHH) (isUnit_iff_ne_zero.2 hD)
      rw [Units.smul_def, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0] at this
      exact this
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, det_smul, hinv]
    unfold schur
    have e : lam • DGH * lam⁻¹ • DHH⁻¹ * lam • DHG = lam • (DGH * DHH⁻¹ * DHG) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      field_simp
    rw [e, smul_sub, add_sub_assoc]

/-- **Spectral reduction to `A_g`.**  With `D_W` the weak mass (`D_ℋℋ` and the Schur complement
`D₂₆` invertible), `B_W = −D_W⁻¹ diag(0, K_g)` and `A_g = −D₂₆⁻¹ K_g`:
`det(λ − B_W) = λ^{dim ℋ} det(λ − A_g)` for every `λ`. -/
theorem charDet_weak_generator (Kg : Matrix g g ℝ) (DHH : Matrix h h ℝ) (DHG : Matrix h g ℝ)
    (DGH : Matrix g h ℝ) (DGG : Matrix g g ℝ) (hD : DHH.det ≠ 0)
    (hS : (schur DHH DHG DGH DGG).det ≠ 0) (lam : ℝ) :
    (scalar (h ⊕ g) lam - -((fromBlocks DHH DHG DGH DGG)⁻¹ * fromBlocks 0 0 0 Kg)).det
      = lam ^ Fintype.card h *
        (scalar g lam - -((schur DHH DHG DGH DGG)⁻¹ * Kg)).det := by
  set DW := fromBlocks DHH DHG DGH DGG
  set S := schur DHH DHG DGH DGG
  have hDW : DW.det = DHH.det * S.det := by
    let _ : Invertible DHH := DHH.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hD)
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]; rfl
  have hDW0 : DW.det ≠ 0 := by rw [hDW]; exact mul_ne_zero hD hS
  have hW : DW⁻¹ * DW = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hDW0)
  have hSS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hS)
  have e1 : scalar (h ⊕ g) lam - -(DW⁻¹ * fromBlocks 0 0 0 Kg)
      = DW⁻¹ * (fromBlocks 0 0 0 Kg + lam • DW) := by
    rw [Matrix.mul_add, Matrix.mul_smul, hW, sub_neg_eq_add, add_comm, scalar_apply,
      smul_one_eq_diagonal]
  have e2 : scalar g lam - -(S⁻¹ * Kg) = S⁻¹ * (Kg + lam • S) := by
    rw [Matrix.mul_add, Matrix.mul_smul, hSS, sub_neg_eq_add, add_comm, scalar_apply,
      smul_one_eq_diagonal]
  rw [e1, e2, det_mul, det_mul, pencil_det Kg DHH DHG DGH DGG hD lam, det_nonsing_inv,
    det_nonsing_inv, hDW]
  rw [show schur DHH DHG DGH DGG = S from rfl]
  simp only [Ring.inverse_eq_inv']
  field_simp

/-- **Characteristic polynomials**: `χ_{B_W} = X^{dim ℋ} χ_{A_g}`; the full weak generator has the
spectrum of `A_g` plus `dim ℋ` exact zeros, with algebraic multiplicities. -/
theorem charpoly_weak_generator (Kg : Matrix g g ℝ) (DHH : Matrix h h ℝ) (DHG : Matrix h g ℝ)
    (DGH : Matrix g h ℝ) (DGG : Matrix g g ℝ) (hD : DHH.det ≠ 0)
    (hS : (schur DHH DHG DGH DGG).det ≠ 0) :
    (-((fromBlocks DHH DHG DGH DGG)⁻¹ * fromBlocks 0 0 0 Kg)).charpoly
      = Polynomial.X ^ Fintype.card h * (-((schur DHH DHG DGH DGG)⁻¹ * Kg)).charpoly := by
  apply Polynomial.funext
  intro lam
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, eval_charpoly, eval_charpoly,
    charDet_weak_generator Kg DHH DHG DGH DGG hD hS lam]

end Pencil

end CertifiedWeakPencil
end RenewalGeometry
