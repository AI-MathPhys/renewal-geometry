/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.StoreFrequencyPencil

/-!
# Exact loaded-frequency count and source reconstruction
  (`cor:store-frequency-count-master`, flagship manuscript)

For the Hankel shells `ℍ_r = [m_{a+b}]_{a,b=0}^{r}` of the loaded
Store moment sequence:

* the boxed rank formula `rank ℍ_r = min(r+1, s)`
  (`store_hankel_rank`): the square shells below the loaded count
  are positive definite by the rectangular Vandermonde
  factorization (`hankelShell_posDef`), while beyond it the rank
  is pinched between the factorization bound and the embedded
  `H₀` — the first vanishing shell determines `s` without knowing
  it in advance;
* the boxed source reconstruction `z_j = p_j(𝒦)Z` for the
  Lagrange polynomials `p_j` of the reconstructed values
  (`store_source_reconstruction`): the spectral component is a
  finite polynomial in the Store jet applied to the pointer;
* the future-separation criterion: for admitted functionals `f_i`
  and `R_{ij} = f_i(z_j)`, the quadratic identity
  `cᵀRᵀRc = Σ_i f_i(Σ_j c_j z_j)²` holds, so `RᵀR ≻ 0` exactly
  when the functionals separate the loaded span
  (`store_future_separation`).

The operator interface is as in `StoreAutocorrelation`: an
operator `K` with `Kz_j = λ_jz_j` on the loaded components
(instantiated by `𝒦 = -¼δ²` via `store_frequency_moments`'s
eigenvalue lemma); real scalars throughout (disclosed).
-/

open Matrix Polynomial Finset

namespace NCG

variable {s : ℕ} (w lam : Fin s → ℝ)

/-- The `(r+1) × (r+1)` Hankel shell `ℍ_r`. -/
noncomputable def hankelShell (r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  Matrix.of fun a b => storeMoment w lam ((a : ℕ) + b)

/-- The rectangular Vandermonde factor. -/
noncomputable def vandShell (r : ℕ) : Matrix (Fin (r + 1)) (Fin s) ℝ :=
  Matrix.of fun a j => lam j ^ (a : ℕ)

/-- Rectangular Vandermonde factorization of the shell. -/
lemma hankelShell_factor (r : ℕ) :
    hankelShell w lam r
      = vandShell lam r * Matrix.diagonal w * (vandShell lam r)ᵀ := by
  rw [Matrix.mul_assoc]
  ext a b
  rw [Matrix.mul_apply, hankelShell, Matrix.of_apply, storeMoment]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diagonal_mul, Matrix.transpose_apply, vandShell,
    Matrix.of_apply, Matrix.of_apply, pow_add]
  ring

/-- The shell quadratic form is a weighted sum of squares. -/
lemma hankelShell_quadratic (r : ℕ) (x : Fin (r + 1) → ℝ) :
    x ⬝ᵥ (hankelShell w lam r *ᵥ x)
      = ∑ j, w j * ((vandShell lam r)ᵀ *ᵥ x) j ^ 2 := by
  rw [hankelShell_factor, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    ← Matrix.mulVec_mulVec]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_diagonal]
  ring

/-- Shells below the loaded count are positive definite. -/
theorem hankelShell_posDef (hw : ∀ j, 0 < w j)
    (hinj : Function.Injective lam) (r : ℕ) (hr : r + 1 ≤ s) :
    (hankelShell w lam r).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rw [Matrix.IsHermitian]
    ext a b
    simp only [Matrix.conjTranspose_apply, hankelShell,
      Matrix.of_apply, star_trivial]
    rw [Nat.add_comm]
  · intro x hx
    rw [star_trivial, hankelShell_quadratic]
    have hp : (vandShell lam r)ᵀ *ᵥ x ≠ 0 := by
      intro h0
      apply hx
      have hsq : Matrix.vandermonde (lam ∘ Fin.castLE hr) *ᵥ x = 0 := by
        funext i
        have h1 := congrFun h0 (Fin.castLE hr i)
        simpa [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
          vandShell, Matrix.transpose_apply] using h1
      exact vandermonde_mulVec_eq_zero _
        (hinj.comp (Fin.castLE_injective hr)) hsq
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hp
    refine Finset.sum_pos'
      (fun j _ => mul_nonneg (hw j).le (sq_nonneg _))
      ⟨j0, mem_univ j0, ?_⟩
    exact mul_pos (hw j0)
      ((sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hj0)))

/-- `cor:store-frequency-count-master`, boxed rank formula:
`rank ℍ_r = min(r+1, s)`. -/
theorem store_hankel_rank (hw : ∀ j, 0 < w j)
    (hinj : Function.Injective lam) (r : ℕ) :
    (hankelShell w lam r).rank = min (r + 1) s := by
  by_cases hr : r + 1 ≤ s
  · rw [min_eq_left hr]
    have hPD := hankelShell_posDef w lam hw hinj r hr
    have h := Matrix.rank_of_isUnit (hankelShell w lam r)
      ((Matrix.isUnit_iff_isUnit_det _).mpr hPD.det_pos.ne'.isUnit)
    simpa using h
  · have hs : s ≤ r + 1 := (Nat.lt_of_not_le hr).le
    rw [min_eq_right hs]
    refine le_antisymm ?_ ?_
    · rw [hankelShell_factor]
      calc (vandShell lam r * Matrix.diagonal w
            * (vandShell lam r)ᵀ).rank
          ≤ (vandShell lam r * Matrix.diagonal w).rank :=
            Matrix.rank_mul_le_left _ _
        _ ≤ (vandShell lam r).rank := Matrix.rank_mul_le_left _ _
        _ ≤ Fintype.card (Fin s) := Matrix.rank_le_card_width _
        _ = s := by simp
    · have hsub : storeH0 w lam
          = (hankelShell w lam r).submatrix
            (Fin.castLE hs) (Fin.castLE hs) := by
        ext a b
        simp [storeH0, hankelShell, Matrix.submatrix_apply]
      have h1 : (storeH0 w lam).rank = s := by
        have h := Matrix.rank_of_isUnit (storeH0 w lam)
          ((Matrix.isUnit_iff_isUnit_det _).mpr
            (storeH0_posDef w lam hw hinj).det_pos.ne'.isUnit)
        simpa using h
      calc s = (storeH0 w lam).rank := h1.symm
        _ = ((hankelShell w lam r).submatrix
            (Fin.castLE hs) (Fin.castLE hs)).rank := by rw [hsub]
        _ ≤ (hankelShell w lam r).rank :=
            Matrix.rank_submatrix_le _ _ _

/-! ### Lagrange source reconstruction -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Operator powers on an eigenvector. -/
lemma pow_apply_eigenvec (K : E →L[ℝ] E) (v : E) (c : ℝ)
    (hv : K v = c • v) (n : ℕ) : (K ^ n) v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    have happ : (K * K ^ m) v = K ((K ^ m) v) := rfl
    rw [happ, ih, map_smul, hv, smul_smul, ← pow_succ]

/-- Polynomials of an operator on an eigenvector. -/
lemma aeval_apply_eigenvec (K : E →L[ℝ] E) (v : E) (c : ℝ)
    (hv : K v = c • v) (p : Polynomial ℝ) :
    (Polynomial.aeval K p) v = p.eval c • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    have happ : (Polynomial.aeval K p + Polynomial.aeval K q) v
        = (Polynomial.aeval K p) v + (Polynomial.aeval K q) v := rfl
    rw [happ, hp, hq, eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, eval_monomial]
    have happ : (algebraMap ℝ (E →L[ℝ] E) a * K ^ n) v
        = a • ((K ^ n) v) := by
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      rfl
    rw [happ, pow_apply_eigenvec K v c hv n, smul_smul]

/-- `cor:store-frequency-count-master`, boxed reconstruction:
`z_j = p_j(𝒦)Z` for the Lagrange polynomial of the reconstructed
values. -/
theorem store_source_reconstruction (hinj : Function.Injective lam)
    (K : E →L[ℝ] E) (z : Fin s → E)
    (hK : ∀ j, K (z j) = lam j • z j) (j : Fin s) :
    (Polynomial.aeval K (Lagrange.basis Finset.univ lam j))
      (∑ i, z i) = z j := by
  rw [map_sum]
  rw [Finset.sum_congr rfl fun i _ =>
    aeval_apply_eigenvec K (z i) (lam i) (hK i) _]
  rw [Finset.sum_eq_single j
    (fun i _ hij => by
      rw [Lagrange.eval_basis_of_ne (Ne.symm hij) (mem_univ i),
        zero_smul])
    (fun h => absurd (mem_univ j) h)]
  rw [Lagrange.eval_basis_self hinj.injOn (mem_univ j), one_smul]

/-! ### Future separation -/

/-- The boxed separation identity `cᵀRᵀRc = Σ_i f_i(Σ_j c_jz_j)²`
and the resulting criterion: `RᵀR ≻ 0` exactly when the admitted
functionals separate the loaded span. -/
theorem store_future_separation {m : ℕ} (z : Fin s → E)
    (f : Fin m → E →ₗ[ℝ] ℝ) :
    (∀ c : Fin s → ℝ,
      c ⬝ᵥ (((Matrix.of fun i j => f i (z j))ᵀ
          * (Matrix.of fun i j => f i (z j))) *ᵥ c)
        = ∑ i, (f i (∑ j, c j • z j)) ^ 2)
    ∧ ((∀ c : Fin s → ℝ, c ≠ 0 →
        0 < c ⬝ᵥ (((Matrix.of fun i j => f i (z j))ᵀ
          * (Matrix.of fun i j => f i (z j))) *ᵥ c))
      ↔ ∀ c : Fin s → ℝ, c ≠ 0 →
          ∃ i, f i (∑ j, c j • z j) ≠ 0) := by
  have hval : ∀ (c : Fin s → ℝ) (i : Fin m),
      ((Matrix.of fun i j => f i (z j)) *ᵥ c) i
        = f i (∑ j, c j • z j) := by
    intro c i
    rw [map_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_smul,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hquad : ∀ c : Fin s → ℝ,
      c ⬝ᵥ (((Matrix.of fun i j => f i (z j))ᵀ
          * (Matrix.of fun i j => f i (z j))) *ᵥ c)
        = ∑ i, (f i (∑ j, c j • z j)) ^ 2 := by
    intro c
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, Matrix.transpose_transpose]
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hval c i]
    ring
  refine ⟨hquad, ?_, ?_⟩
  · intro hpos c hc
    have h := hpos c hc
    rw [hquad] at h
    by_contra hcon
    rw [not_exists] at hcon
    have hzero : ∀ i ∈ Finset.univ, (f i (∑ j, c j • z j)) ^ 2 = 0 :=
      fun i _ => by
        rw [not_not.mp (fun hne => hcon i hne)]
        ring
    rw [Finset.sum_eq_zero hzero] at h
    exact lt_irrefl 0 h
  · intro hsep c hc
    obtain ⟨i0, hi0⟩ := hsep c hc
    rw [hquad c]
    refine Finset.sum_pos' (fun i _ => sq_nonneg _)
      ⟨i0, mem_univ i0, ?_⟩
    exact (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hi0))

end NCG
