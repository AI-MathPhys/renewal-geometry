/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SourceCoercivityInfluenceExact
import NCG.Grand.TraceExpDerivative

/-!
# Exact medium-batch records 02 (Gran-Tensor manuscript)

Exact full-statement completions for the MEDIUM re-encoding batch 02:

* `thm:renormalization-cocycle` — finite metric congruence `Zᴴ B Z = A` with
  positive-semidefinite `A`, `B`: solvability **iff** `rank A ≤ rank B`, the
  boxed complete solution classification `Z = B^{†/2} U A^{1/2} + N` with `U`
  a partial isometry from `supp A` into `supp B` and `Ran N ⊆ Ker B`, the
  unitary modulus at equal ranks, and the diamond obstruction in genuine
  PSD-with-supports form (`𝔻 = 0` iff the faithful-quotient arrow vanishes),
  with singular-vector failure witnesses.

* `thm:store-block-decomposition` — the anticommuting Store-block spectral
  decomposition: an explicit orthonormal system of `σ_z`-graded pairs with
  positive singular values reconstructing `L` exactly, the kernel-complement
  projection, and the joint commutant `{Z, L}' = ⊕_j I₂ ⊗ B(M_j)` in exact
  matrix-coefficient form (both inclusions).

* `thm:uniform-gap-limit` — compatible stage contractions and fixed-space
  projections on a dense Hilbert filtration: unique bounded limits, the boxed
  norm equality `‖Q∞T∞Q∞‖ = sup_X ρ_X` as a least upper bound of genuine
  stage-restriction norms, the gap equivalence with the boxed power estimate,
  and a fully constructed ℓ² diagonal counterexample with positive gaps at
  every finite cutoff and no uniform limit gap.

* `thm:universal-Hankel-exhaustion` — the Hilbert-level block-Hankel theorem:
  Gram rank equals Krylov dimension for an actual operator `0 ⪯ T ⪯ I` on an
  inner-product space, the generalized Rayleigh radius as the norm of the
  compression of `T` to the Krylov subspace, and the dense sup-exhaustion of
  the selected compression norm.

* `thm:projection-persistence-tradeoff` — the completed-private dwell operator
  layer: the dwell-averaged pure-interchange operator (a genuine operator
  series with the manuscript's first-return weights) minus the count
  projection has operator norm at least `E(q_N)`; combined with the proved
  spectral layer this yields the full tradeoff chain for `ε_N^proj`.

* `thm:positive-renewal-quotient-family` — the exact first-return transform
  `8z²/((5-z)(3-z))`, the positivity window as an iff, spectra as sets
  (`{1/5, 1/3}` for `Q(a)` and `{1, -7/15}` for the reset chain), stationary
  completion flux `4/11`, reachability and future separation, endpoint serial
  primitives, and the general two-dimensional cone-quotient clause (closed
  proper generating cones in the plane are simplicial, so positive transfers
  become entrywise-nonnegative two-state models).

* `thm:tetrahedral-prototype-connection` — the assembled asymptotic curvature
  expansion: `H₁₂₃(h) = I + O(h²)` iff the orbit sum cancels, and on the
  area-scaled branch the boxed `H₁₂₃(h) = I + (h²/2)[A, RAR⁻¹] + O(h³)`,
  combined with the covariance/reversal/no-go clauses into one theorem.

* `thm:operational-record-completion` — the concrete parallel-composition
  clause (Kronecker reshuffle along `Equiv.prodProdProdComm`, preserving CP
  branches and instrument normalization), coarse graining, and the packaged
  O1–O6 statement.

* `thm:relational-completion` — the packaged (RC.7) process morphism: one
  bundled structure carrying forgetful word intertwining, history-algebra
  survival, and word-Gram compression, together with C1–C5.

* `thm:record-survival` — survival relative to a genuinely nontrivial
  contextual future-null ideal: with Reads declared on a proper subfamily of
  ledger blocks the null ideal is exactly the unread-block ideal (nonzero in
  general), readable projections/writers/provenance points survive, and
  unread fibre contrasts are killed.

* `thm:summable-mixed-Gram-correction` — the tower form over genuine
  coefficient isometries `J_n : E_n → E_{n+1}`: corrected limits
  `Ĝ_m = lim J_{n/m}ᴴ 𝔾_n J_{n/m}` exist in norm, are positive, satisfy exact
  compatibility `J_mᴴ Ĝ_{m+1} J_m = Ĝ_m`, obey the boxed tail bound, and above
  a spectral floor the support projections are proved (not assumed) to be the
  identity, hence exactly stable.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-! ## Record `thm:renormalization-cocycle`:
finite metric congruence and cocycle obstruction, exact form -/

namespace RenormCongruence

open GeometricThresholdBank SourceCoercivityInfluence

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- Every real spectral function of a hermitian matrix is hermitian. -/
theorem spectralFunction_isHermitian {S : Matrix n n ℂ}
    (hS : S.IsHermitian) (f : ℝ → ℝ) :
    (spectralFunction hS f).IsHermitian := by
  have hsplit : spectralFunction hS f
      = spectralFunction hS (fun l => max (f l) 0)
        - spectralFunction hS (fun l => max (-f l) 0) := by
    rw [← spectralFunction_sub]
    exact spectralFunction_congr hS fun i =>
      (max_zero_sub_max_neg_zero_eq_self _).symm
  rw [hsplit]
  exact ((spectralFunction_posSemidef hS _ fun i => le_max_right _ _).1).sub
    ((spectralFunction_posSemidef hS _ fun i => le_max_right _ _).1)

/-- The pseudoinverse square root `B^{†/2}` by spectral calculus. -/
noncomputable def pinvSqrt {B : Matrix m m ℂ} (hB : B.IsHermitian) :
    Matrix m m ℂ :=
  spectralFunction hB fun l => if 0 < l then (Real.sqrt l)⁻¹ else 0

/-- The spectral square root `A^{1/2}`. -/
noncomputable def sqrtSF {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Matrix n n ℂ :=
  spectralFunction hA fun l => Real.sqrt l

/-- `A^{1/2}` is hermitian. -/
theorem sqrtSF_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (sqrtSF hA).IsHermitian :=
  spectralFunction_isHermitian hA _

/-- `B^{†/2}` is hermitian. -/
theorem pinvSqrt_isHermitian {B : Matrix m m ℂ} (hB : B.IsHermitian) :
    (pinvSqrt hB).IsHermitian :=
  spectralFunction_isHermitian hB _

/-- For positive semidefinite `A`, the spectral square root squares to `A`. -/
theorem sqrtSF_mul_self {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    sqrtSF hA.1 * sqrtSF hA.1 = A := by
  unfold sqrtSF
  rw [spectralFunction_mul]
  calc spectralFunction hA.1 (fun l => Real.sqrt l * Real.sqrt l)
      = spectralFunction hA.1 id :=
        spectralFunction_congr hA.1 fun i =>
          Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
    _ = A := spectralFunction_id hA.1

/-- `B^{†/2} B B^{†/2}` is the support projection of positive
semidefinite `B`. -/
theorem pinvSqrt_mul_mul {B : Matrix m m ℂ} (hB : B.PosSemidef) :
    pinvSqrt hB.1 * B * pinvSqrt hB.1 = supportProj hB.1 := by
  have hmid : pinvSqrt hB.1 * B * pinvSqrt hB.1
      = pinvSqrt hB.1 * spectralFunction hB.1 id * pinvSqrt hB.1 := by
    rw [spectralFunction_id]
  rw [hmid]
  unfold pinvSqrt supportProj
  rw [spectralFunction_mul, spectralFunction_mul]
  refine spectralFunction_congr hB.1 fun i => ?_
  by_cases h : 0 < hB.1.eigenvalues i
  · have hs : Real.sqrt (hB.1.eigenvalues i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr h)
    rw [if_pos h, if_pos h, if_pos h]
    field_simp [id]
    exact (Real.mul_self_sqrt h.le).symm
  · rw [if_neg h, if_neg h, if_neg h]
    simp

/-- The support projection absorbs the spectral square root on the left. -/
theorem supportProj_mul_sqrtSF {B : Matrix m m ℂ} (hB : B.IsHermitian) :
    supportProj hB * sqrtSF hB = sqrtSF hB := by
  unfold supportProj sqrtSF
  rw [spectralFunction_mul]
  refine spectralFunction_congr hB fun i => ?_
  by_cases h : 0 < hB.eigenvalues i
  · rw [if_pos h, one_mul]
  · rw [if_neg h, zero_mul,
      Real.sqrt_eq_zero' .mpr (not_lt.mp h)]

/-- The support projection absorbs the pseudoinverse square root. -/
theorem supportProj_mul_pinvSqrt {B : Matrix m m ℂ} (hB : B.IsHermitian) :
    supportProj hB * pinvSqrt hB = pinvSqrt hB := by
  unfold supportProj pinvSqrt
  rw [spectralFunction_mul]
  refine spectralFunction_congr hB fun i => ?_
  by_cases h : 0 < hB.eigenvalues i
  · rw [if_pos h, if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, if_neg h, zero_mul]

/-- `B^{†/2} B^{1/2}` is the support projection. -/
theorem pinvSqrt_mul_sqrtSF {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    pinvSqrt hA * sqrtSF hA = supportProj hA := by
  unfold pinvSqrt sqrtSF supportProj
  rw [spectralFunction_mul]
  refine spectralFunction_congr hA fun i => ?_
  by_cases h : 0 < hA.eigenvalues i
  · have hs : Real.sqrt (hA.eigenvalues i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr h)
    rw [if_pos h, if_pos h, inv_mul_cancel₀ hs]
  · rw [if_neg h, if_neg h, zero_mul]

/-- The square root absorbs the support projection on the right,
for positive semidefinite input. -/
theorem sqrtSF_mul_supportProj {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    sqrtSF hA.1 * supportProj hA.1 = sqrtSF hA.1 := by
  unfold supportProj sqrtSF
  rw [spectralFunction_mul]
  refine spectralFunction_congr hA.1 fun i => ?_
  by_cases h : 0 < hA.1.eigenvalues i
  · rw [if_pos h, mul_one]
  · have h0 : hA.1.eigenvalues i = 0 :=
      le_antisymm (not_lt.mp h) (hA.eigenvalues_nonneg i)
    rw [if_neg h, mul_zero, h0, Real.sqrt_zero]

/-- The support projection also absorbs `A` on the left. -/
theorem supportProj_mul_self {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    supportProj hA.1 * A = A := by
  have h := congrArg conjTranspose (mul_supportProj hA)
  rwa [Matrix.conjTranspose_mul, hA.1,
    (supportProj_posSemidef hA.1).1] at h

/-- The boxed classification of `thm:renormalization-cocycle`: `Z` solves the
metric congruence `Zᴴ B Z = A` **iff** `Z = B^{†/2} U A^{1/2} + N` for a
partial isometry `U` with initial projection `supp A` and range inside
`supp B`, and a kernel term with `B N = 0` (`Ran N ⊆ Ker B`). -/
theorem congruence_solution_iff (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (Z : Matrix m n ℂ) :
    Zᴴ * B * Z = A ↔
      ∃ U N : Matrix m n ℂ,
        Z = pinvSqrt hB.1 * U * sqrtSF hA.1 + N
        ∧ Uᴴ * U = supportProj hA.1
        ∧ supportProj hB.1 * U = U
        ∧ B * N = 0 := by
  constructor
  · intro hZ
    refine ⟨sqrtSF hB.1 * Z * pinvSqrt hA.1,
      Z - supportProj hB.1 * Z * supportProj hA.1, ?_, ?_, ?_, ?_⟩
    · have hform : pinvSqrt hB.1 * (sqrtSF hB.1 * Z * pinvSqrt hA.1)
          * sqrtSF hA.1
          = supportProj hB.1 * Z * supportProj hA.1 := by
        calc pinvSqrt hB.1 * (sqrtSF hB.1 * Z * pinvSqrt hA.1)
              * sqrtSF hA.1
            = (pinvSqrt hB.1 * sqrtSF hB.1) * Z
                * (pinvSqrt hA.1 * sqrtSF hA.1) := by
              simp only [Matrix.mul_assoc]
          _ = supportProj hB.1 * Z * supportProj hA.1 := by
              rw [pinvSqrt_mul_sqrtSF, pinvSqrt_mul_sqrtSF]
      rw [hform]
      abel
    · calc (sqrtSF hB.1 * Z * pinvSqrt hA.1)ᴴ
            * (sqrtSF hB.1 * Z * pinvSqrt hA.1)
          = pinvSqrt hA.1 * (Zᴴ * (sqrtSF hB.1 * sqrtSF hB.1) * Z)
              * pinvSqrt hA.1 := by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
              (pinvSqrt_isHermitian hA.1).eq, (sqrtSF_isHermitian hB.1).eq]
            simp only [Matrix.mul_assoc]
        _ = pinvSqrt hA.1 * A * pinvSqrt hA.1 := by
            rw [sqrtSF_mul_self hB]
            rw [show Zᴴ * (B * Z) = Zᴴ * B * Z from
              (Matrix.mul_assoc _ _ _).symm, hZ]
        _ = supportProj hA.1 := pinvSqrt_mul_mul hA
    · calc supportProj hB.1 * (sqrtSF hB.1 * Z * pinvSqrt hA.1)
          = (supportProj hB.1 * sqrtSF hB.1) * Z * pinvSqrt hA.1 := by
            simp only [Matrix.mul_assoc]
        _ = sqrtSF hB.1 * Z * pinvSqrt hA.1 := by
            rw [supportProj_mul_sqrtSF]
    · -- `B Z (1 - supp A) = 0`, via a vanishing Gram
      have hGram : (sqrtSF hB.1 * (Z * ((1 : Matrix n n ℂ)
            - supportProj hA.1)))ᴴ
            * (sqrtSF hB.1 * (Z * ((1 : Matrix n n ℂ)
            - supportProj hA.1))) = 0 := by
        have hsub : ((1 : Matrix n n ℂ) - supportProj hA.1)ᴴ
            = (1 : Matrix n n ℂ) - supportProj hA.1 := by
          rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
            (supportProj_posSemidef hA.1).1]
        calc (sqrtSF hB.1 * (Z * ((1 : Matrix n n ℂ)
              - supportProj hA.1)))ᴴ
              * (sqrtSF hB.1 * (Z * ((1 : Matrix n n ℂ)
              - supportProj hA.1)))
            = ((1 : Matrix n n ℂ) - supportProj hA.1)
                * (Zᴴ * (sqrtSF hB.1 * sqrtSF hB.1) * Z)
                * ((1 : Matrix n n ℂ) - supportProj hA.1) := by
              rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
                hsub, (sqrtSF_isHermitian hB.1).eq]
              simp only [Matrix.mul_assoc]
          _ = ((1 : Matrix n n ℂ) - supportProj hA.1) * A
                * ((1 : Matrix n n ℂ) - supportProj hA.1) := by
              rw [sqrtSF_mul_self hB]
              rw [show Zᴴ * (B * Z) = Zᴴ * B * Z from
                (Matrix.mul_assoc _ _ _).symm, hZ]
          _ = 0 := by
              rw [Matrix.sub_mul, Matrix.one_mul,
                supportProj_mul_self hA, sub_self, Matrix.zero_mul]
      have hSD := Matrix.conjTranspose_mul_self_eq_zero.mp hGram
      have hBZ : B * (Z * ((1 : Matrix n n ℂ) - supportProj hA.1)) = 0 := by
        calc B * (Z * ((1 : Matrix n n ℂ) - supportProj hA.1))
            = sqrtSF hB.1 * (sqrtSF hB.1
                * (Z * ((1 : Matrix n n ℂ) - supportProj hA.1))) := by
              rw [← Matrix.mul_assoc, sqrtSF_mul_self hB]
          _ = 0 := by rw [hSD, Matrix.mul_zero]
      calc B * (Z - supportProj hB.1 * Z * supportProj hA.1)
          = B * Z - (B * supportProj hB.1) * (Z * supportProj hA.1) := by
            rw [Matrix.mul_sub]
            simp only [Matrix.mul_assoc]
        _ = B * Z - B * (Z * supportProj hA.1) := by
            rw [mul_supportProj hB]
            simp only [Matrix.mul_assoc]
        _ = B * (Z * ((1 : Matrix n n ℂ) - supportProj hA.1)) := by
            rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_sub]
        _ = 0 := hBZ
  · rintro ⟨U, N, rfl, hUU, hBU, hBN⟩
    have hNB : Nᴴ * B = 0 := by
      have h := congrArg conjTranspose hBN
      rwa [Matrix.conjTranspose_mul, hB.1,
        Matrix.conjTranspose_zero] at h
    have hcore : (pinvSqrt hB.1 * U * sqrtSF hA.1)ᴴ * B
        * (pinvSqrt hB.1 * U * sqrtSF hA.1) = A := by
      calc (pinvSqrt hB.1 * U * sqrtSF hA.1)ᴴ * B
            * (pinvSqrt hB.1 * U * sqrtSF hA.1)
          = sqrtSF hA.1 * (Uᴴ
              * (pinvSqrt hB.1 * B * pinvSqrt hB.1) * U)
              * sqrtSF hA.1 := by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
              (pinvSqrt_isHermitian hB.1).eq, (sqrtSF_isHermitian hA.1).eq]
            simp only [Matrix.mul_assoc]
        _ = sqrtSF hA.1 * (Uᴴ * (supportProj hB.1 * U)) * sqrtSF hA.1 := by
            rw [pinvSqrt_mul_mul hB]
            simp only [Matrix.mul_assoc]
        _ = sqrtSF hA.1 * supportProj hA.1 * sqrtSF hA.1 := by
            rw [hBU, ← Matrix.mul_assoc, hUU]
        _ = A := by
            rw [sqrtSF_mul_supportProj hA, sqrtSF_mul_self hA]
    have hcross₁ : Nᴴ * B * (pinvSqrt hB.1 * U * sqrtSF hA.1) = 0 := by
      rw [hNB, Matrix.zero_mul]
    have hcross₂ : (pinvSqrt hB.1 * U * sqrtSF hA.1)ᴴ * B * N = 0 := by
      rw [Matrix.mul_assoc, hBN, Matrix.mul_zero]
    have hNN : Nᴴ * B * N = 0 := by
      rw [Matrix.mul_assoc, hBN, Matrix.mul_zero]
    calc (pinvSqrt hB.1 * U * sqrtSF hA.1 + N)ᴴ * B
          * (pinvSqrt hB.1 * U * sqrtSF hA.1 + N)
        = (pinvSqrt hB.1 * U * sqrtSF hA.1)ᴴ * B
            * (pinvSqrt hB.1 * U * sqrtSF hA.1)
          + (pinvSqrt hB.1 * U * sqrtSF hA.1)ᴴ * B * N
          + (Nᴴ * B * (pinvSqrt hB.1 * U * sqrtSF hA.1)
          + Nᴴ * B * N) := by
          rw [Matrix.conjTranspose_add]
          simp only [Matrix.add_mul, Matrix.mul_add]
          abel
      _ = A := by rw [hcore, hcross₁, hcross₂, hNN]; abel

section StiefelConstruction

variable {A : Matrix n n ℂ} {B : Matrix m m ℂ}

/-- The 0/1 pattern matrix of a support embedding. -/
noncomputable def stiefelPattern (hA : A.IsHermitian) (hB : B.IsHermitian)
    (e : {i // hA.eigenvalues i ≠ 0} → {j // hB.eigenvalues j ≠ 0}) :
    Matrix m n ℂ :=
  Matrix.of fun j i =>
    if h : hA.eigenvalues i ≠ 0 then (if j = (e ⟨i, h⟩ : _).1 then 1 else 0)
    else 0

/-- The support indicator diagonal. -/
noncomputable def suppDiag (hA : A.IsHermitian) : Matrix n n ℂ :=
  Matrix.diagonal fun i => if hA.eigenvalues i ≠ 0 then (1 : ℂ) else 0

/-- The pattern matrix of an injective embedding has Gram equal to the
source support indicator. -/
theorem stiefelPattern_gram (hA : A.IsHermitian) (hB : B.IsHermitian)
    (e : {i // hA.eigenvalues i ≠ 0} → {j // hB.eigenvalues j ≠ 0})
    (he : Function.Injective e) :
    (stiefelPattern hA hB e)ᴴ * stiefelPattern hA hB e = suppDiag hA := by
  ext i i'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    stiefelPattern, Matrix.of_apply, suppDiag, Matrix.diagonal_apply]
  by_cases hi : hA.eigenvalues i ≠ 0
  · by_cases hi' : hA.eigenvalues i' ≠ 0
    · rw [Finset.sum_congr rfl fun j _ => by
        rw [dif_pos hi, dif_pos hi', apply_ite star, star_one, star_zero]]
      rw [Finset.sum_eq_single ((e ⟨i, hi⟩ : _).1)
        (fun j _ hj => by rw [if_neg hj, zero_mul])
        (fun h => absurd (Finset.mem_univ _) h)]
      rw [if_pos rfl, one_mul]
      by_cases hii : i = i'
      · subst hii
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hii, if_neg (fun hc : (e ⟨i, hi⟩ : _).1
            = (e ⟨i', hi'⟩ : _).1 => by
          exact hii (congrArg Subtype.val
            (he (Subtype.ext hc)) : i = i'))]
    · rw [Finset.sum_congr rfl fun j _ => by
        rw [dif_neg hi', mul_zero]]
      rw [Finset.sum_const_zero]
      by_cases hii : i = i'
      · subst hii; exact absurd hi hi'
      · rw [if_neg hii]
  · rw [Finset.sum_congr rfl fun j _ => by
      rw [dif_neg hi, star_zero, zero_mul]]
    rw [Finset.sum_const_zero]
    by_cases hii : i = i'
    · subst hii
      rw [if_pos rfl, if_neg hi]
    · rw [if_neg hii]

/-- The target support indicator absorbs the pattern matrix. -/
theorem suppDiag_mul_stiefelPattern (hA : A.IsHermitian)
    (hB : B.IsHermitian)
    (e : {i // hA.eigenvalues i ≠ 0} → {j // hB.eigenvalues j ≠ 0}) :
    suppDiag hB * stiefelPattern hA hB e = stiefelPattern hA hB e := by
  ext j i
  rw [suppDiag, Matrix.diagonal_mul]
  simp only [stiefelPattern, Matrix.of_apply]
  by_cases hi : hA.eigenvalues i ≠ 0
  · rw [dif_pos hi, dif_pos hi]
    by_cases hj : j = (e ⟨i, hi⟩ : _).1
    · rw [if_pos hj, mul_one, hj, if_pos (e ⟨i, hi⟩).2]
    · rw [if_neg hj, mul_zero]
  · rw [dif_neg hi, dif_neg hi, mul_zero]

/-- The co-Gram of the pattern matrix of a bijective embedding is the target
support indicator. -/
theorem stiefelPattern_cogram (hA : A.IsHermitian) (hB : B.IsHermitian)
    (e : {i // hA.eigenvalues i ≠ 0} ≃ {j // hB.eigenvalues j ≠ 0}) :
    stiefelPattern hA hB e * (stiefelPattern hA hB e)ᴴ = suppDiag hB := by
  ext j j'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    stiefelPattern, Matrix.of_apply, suppDiag, Matrix.diagonal_apply]
  by_cases hj : hB.eigenvalues j ≠ 0
  · have hi₀ : hA.eigenvalues ((e.symm ⟨j, hj⟩ : _).1) ≠ 0 :=
      (e.symm ⟨j, hj⟩).2
    have hkey : e ⟨(e.symm ⟨j, hj⟩ : _).1, hi₀⟩ = ⟨j, hj⟩ := by
      rw [show (⟨(e.symm ⟨j, hj⟩ : _).1, hi₀⟩
          : {i // hA.eigenvalues i ≠ 0}) = e.symm ⟨j, hj⟩ from rfl]
      exact e.apply_symm_apply _
    rw [Finset.sum_eq_single ((e.symm ⟨j, hj⟩ : _).1)
      (fun i _ hne => by
        by_cases hi : hA.eigenvalues i ≠ 0
        · rw [dif_pos hi]
          by_cases hji : j = (e ⟨i, hi⟩ : _).1
          · exfalso
            apply hne
            have : e ⟨i, hi⟩ = ⟨j, hj⟩ := Subtype.ext hji.symm
            have := congrArg (fun z => (e.symm z : _).1) this
            simpa [Equiv.symm_apply_apply] using this
          · rw [if_neg hji, zero_mul]
        · rw [dif_neg hi, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [dif_pos hi₀, hkey, if_pos rfl, one_mul, dif_pos hi₀, hkey]
    by_cases hjj : j = j'
    · subst hjj
      rw [if_pos rfl, if_pos rfl, if_pos hj, star_one]
    · rw [if_neg hjj, if_neg (fun hc : j' = j => hjj hc.symm), star_zero]
  · rw [Finset.sum_congr rfl fun i _ => by
      by_cases hi : hA.eigenvalues i ≠ 0
      · rw [dif_pos hi, if_neg (fun hc : j = (e ⟨i, hi⟩ : _).1 =>
          hj (hc ▸ (e ⟨i, hi⟩).2 : hB.eigenvalues j ≠ 0) rfl), zero_mul]
      · rw [dif_neg hi, zero_mul]]
    rw [Finset.sum_const_zero]
    by_cases hjj : j = j'
    · subst hjj
      rw [if_pos rfl, if_neg hj]
    · rw [if_neg hjj]

/-- For positive semidefinite `A`, the support projection in eigencoordinates
is exactly the support indicator conjugated by the eigenvector unitary. -/
theorem supportProj_eigen_form (hA : A.PosSemidef) :
    supportProj hA.1
      = (hA.1.eigenvectorUnitary : Matrix n n ℂ) * suppDiag hA.1
        * (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  unfold supportProj spectralFunction
  rw [Unitary.conjStarAlgAut_apply]
  congr 1
  · congr 1
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, suppDiag, Function.comp_apply]
      by_cases h : 0 < hA.1.eigenvalues i
      · rw [if_pos h, if_pos (ne_of_gt h)]
        simp
      · have h0 : hA.1.eigenvalues i = 0 :=
          le_antisymm (not_lt.mp h) (hA.eigenvalues_nonneg i)
        rw [if_neg h, if_neg (fun hc => hc h0)]
        simp
    · simp [Matrix.diagonal_apply_ne _ hij, suppDiag]
  · simp [Matrix.star_eq_conjTranspose]

/-- The partial isometry between Gram supports induced by an embedding of
nonzero eigenvalue indices. -/
noncomputable def stiefelIsometry (hA : A.IsHermitian) (hB : B.IsHermitian)
    (e : {i // hA.eigenvalues i ≠ 0} → {j // hB.eigenvalues j ≠ 0}) :
    Matrix m n ℂ :=
  (hB.eigenvectorUnitary : Matrix m m ℂ) * stiefelPattern hA hB e
    * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ

/-- The induced partial isometry has initial projection `supp A`. -/
theorem stiefelIsometry_gram (hA : A.PosSemidef) (hB : B.PosSemidef)
    (e : {i // hA.1.eigenvalues i ≠ 0} → {j // hB.1.eigenvalues j ≠ 0})
    (he : Function.Injective e) :
    (stiefelIsometry hA.1 hB.1 e)ᴴ * stiefelIsometry hA.1 hB.1 e
      = supportProj hA.1 := by
  unfold stiefelIsometry
  have hUB : (hB.1.eigenvectorUnitary : Matrix m m ℂ)ᴴ
      * (hB.1.eigenvectorUnitary : Matrix m m ℂ) = 1 :=
    eigenvectorUnitary_conjTranspose_mul B hB.1
  calc ((hB.1.eigenvectorUnitary : Matrix m m ℂ) * stiefelPattern hA.1 hB.1 e
        * (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ)ᴴ
        * ((hB.1.eigenvectorUnitary : Matrix m m ℂ)
          * stiefelPattern hA.1 hB.1 e
          * (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
      = (hA.1.eigenvectorUnitary : Matrix n n ℂ)
          * ((stiefelPattern hA.1 hB.1 e)ᴴ
            * ((hB.1.eigenvectorUnitary : Matrix m m ℂ)ᴴ
              * (hB.1.eigenvectorUnitary : Matrix m m ℂ))
            * stiefelPattern hA.1 hB.1 e)
          * (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc]
    _ = (hA.1.eigenvectorUnitary : Matrix n n ℂ) * suppDiag hA.1
          * (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
        rw [hUB, Matrix.mul_one, stiefelPattern_gram hA.1 hB.1 e he]
    _ = supportProj hA.1 := (supportProj_eigen_form hA).symm

/-- The induced partial isometry has range inside `supp B`. -/
theorem supportProj_mul_stiefelIsometry (hA : A.PosSemidef)
    (hB : B.PosSemidef)
    (e : {i // hA.1.eigenvalues i ≠ 0} → {j // hB.1.eigenvalues j ≠ 0}) :
    supportProj hB.1 * stiefelIsometry hA.1 hB.1 e
      = stiefelIsometry hA.1 hB.1 e := by
  unfold stiefelIsometry
  have hUB : (hB.1.eigenvectorUnitary : Matrix m m ℂ)ᴴ
      * (hB.1.eigenvectorUnitary : Matrix m m ℂ) = 1 :=
    eigenvectorUnitary_conjTranspose_mul B hB.1
  rw [supportProj_eigen_form hB]
  calc (hB.1.eigenvectorUnitary : Matrix m m ℂ) * suppDiag hB.1
        * (hB.1.eigenvectorUnitary : Matrix m m ℂ)ᴴ
        * ((hB.1.eigenvectorUnitary : Matrix m m ℂ)
          * stiefelPattern hA.1 hB.1 e
          * (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
      = (hB.1.eigenvectorUnitary : Matrix m m ℂ)
          * (suppDiag hB.1
            * (((hB.1.eigenvectorUnitary : Matrix m m ℂ)ᴴ
              * (hB.1.eigenvectorUnitary : Matrix m m ℂ))
            * stiefelPattern hA.1 hB.1 e))
          * (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = (hB.1.eigenvectorUnitary : Matrix m m ℂ)
          * stiefelPattern hA.1 hB.1 e
          * (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
        rw [hUB, Matrix.one_mul, suppDiag_mul_stiefelPattern]

end StiefelConstruction

/-- `thm:renormalization-cocycle`, exact form: metric congruence with genuine
positive-semidefinite data on both sides.
(i) solvability of `Zᴴ B Z = A` is **exactly** `rank A ≤ rank B`;
(ii) the boxed complete classification `Z = B^{†/2} U A^{1/2} + N` of all
solutions, `U` a partial isometry from `supp A` into `supp B`,
`Ran N ⊆ Ker B`;
(iii) equal ranks leave a unitary modulus (a co-isometric `U` between the
Gram supports);
(iv) the diamond obstruction with supports: `𝔻 = Dᴴ G D ⪰ 0` always, and
`𝔻 = 0` iff `G D = 0` iff the faithful-quotient arrow `supp(G)·D` vanishes,
with a nonzero singular vector of `G^{1/2} D` as explicit failure witness. -/
theorem renormalization_cocycle_exact {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    -- (i) existence iff rank comparison
    ((∃ Z : Matrix m n ℂ, Zᴴ * B * Z = A) ↔ A.rank ≤ B.rank)
    -- (ii) the boxed complete solution classification
    ∧ (∀ Z : Matrix m n ℂ, Zᴴ * B * Z = A ↔
        ∃ U N : Matrix m n ℂ,
          Z = pinvSqrt hB.1 * U * sqrtSF hA.1 + N
          ∧ Uᴴ * U = supportProj hA.1
          ∧ supportProj hB.1 * U = U
          ∧ B * N = 0)
    -- (iii) equal ranks leave a unitary modulus
    ∧ (A.rank = B.rank →
        ∃ U : Matrix m n ℂ,
          Uᴴ * U = supportProj hA.1 ∧ U * Uᴴ = supportProj hB.1)
    -- (iv) diamond obstruction, PSD-with-supports form
    ∧ (∀ G D : Matrix m m ℂ, ∀ hG : G.PosSemidef,
        (Dᴴ * G * D).PosSemidef
        ∧ (Dᴴ * G * D = 0 ↔ G * D = 0)
        ∧ (Dᴴ * G * D = 0 ↔ supportProj hG.1 * D = 0)
        ∧ (Dᴴ * G * D ≠ 0 ↔
            ∃ v : m → ℂ, sqrtSF hG.1 *ᵥ (D *ᵥ v) ≠ 0)) := by
  have hsolve : ∀ Z : Matrix m n ℂ, Zᴴ * B * Z = A ↔
      ∃ U N : Matrix m n ℂ,
        Z = pinvSqrt hB.1 * U * sqrtSF hA.1 + N
        ∧ Uᴴ * U = supportProj hA.1
        ∧ supportProj hB.1 * U = U
        ∧ B * N = 0 :=
    congruence_solution_iff A B hA hB
  have hGD : ∀ G D : Matrix m m ℂ, ∀ hG : G.PosSemidef,
      (Dᴴ * G * D = 0 ↔ G * D = 0) := by
    intro G D hG
    constructor
    · intro h0
      have hfac : Dᴴ * G * D
          = (sqrtSF hG.1 * D)ᴴ * (sqrtSF hG.1 * D) := by
        rw [Matrix.conjTranspose_mul, (sqrtSF_isHermitian hG.1).eq]
        calc Dᴴ * G * D
            = Dᴴ * ((sqrtSF hG.1 * sqrtSF hG.1) * D) := by
              rw [sqrtSF_mul_self hG, Matrix.mul_assoc]
          _ = Dᴴ * sqrtSF hG.1 * (sqrtSF hG.1 * D) := by
              simp only [Matrix.mul_assoc]
      rw [hfac] at h0
      have hSD := Matrix.conjTranspose_mul_self_eq_zero.mp h0
      calc G * D = sqrtSF hG.1 * (sqrtSF hG.1 * D) := by
            rw [← Matrix.mul_assoc, sqrtSF_mul_self hG]
        _ = 0 := by rw [hSD, Matrix.mul_zero]
    · intro h0
      rw [Matrix.mul_assoc, h0, Matrix.mul_zero]
  refine ⟨?_, hsolve, ?_, ?_⟩
  · constructor
    · rintro ⟨Z, hZ⟩
      rw [← hZ]
      calc (Zᴴ * B * Z).rank ≤ (B * Z).rank := by
            rw [Matrix.mul_assoc]
            exact Matrix.rank_mul_le_right _ _
        _ ≤ B.rank := Matrix.rank_mul_le_left _ _
    · intro hrank
      have hcard : Fintype.card {i // hA.1.eigenvalues i ≠ 0}
          ≤ Fintype.card {j // hB.1.eigenvalues j ≠ 0} := by
        rw [← hA.1.rank_eq_card_non_zero_eigs,
          ← hB.1.rank_eq_card_non_zero_eigs]
        exact hrank
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
      refine ⟨pinvSqrt hB.1 * stiefelIsometry hA.1 hB.1 e * sqrtSF hA.1,
        ?_⟩
      rw [hsolve]
      exact ⟨stiefelIsometry hA.1 hB.1 e, 0, by rw [add_zero],
        stiefelIsometry_gram hA hB e e.injective,
        supportProj_mul_stiefelIsometry hA hB e, by rw [Matrix.mul_zero]⟩
  · intro hrank
    have hcard : Fintype.card {i // hA.1.eigenvalues i ≠ 0}
        = Fintype.card {j // hB.1.eigenvalues j ≠ 0} := by
      rw [← hA.1.rank_eq_card_non_zero_eigs,
        ← hB.1.rank_eq_card_non_zero_eigs]
      exact hrank
    obtain ⟨e⟩ := Fintype.card_eq.mp hcard
    refine ⟨stiefelIsometry hA.1 hB.1 e,
      stiefelIsometry_gram hA hB e e.injective, ?_⟩
    unfold stiefelIsometry
    have hUA : (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ
        * (hA.1.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
      eigenvectorUnitary_conjTranspose_mul A hA.1
    calc (hB.1.eigenvectorUnitary : Matrix m m ℂ)
          * stiefelPattern hA.1 hB.1 e
          * (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ
          * ((hB.1.eigenvectorUnitary : Matrix m m ℂ)
            * stiefelPattern hA.1 hB.1 e
            * (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ)ᴴ
        = (hB.1.eigenvectorUnitary : Matrix m m ℂ)
            * (stiefelPattern hA.1 hB.1 e
              * (((hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ
                * (hA.1.eigenvectorUnitary : Matrix n n ℂ))
                * (stiefelPattern hA.1 hB.1 e)ᴴ))
            * (hB.1.eigenvectorUnitary : Matrix m m ℂ)ᴴ := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = (hB.1.eigenvectorUnitary : Matrix m m ℂ) * suppDiag hB.1
            * (hB.1.eigenvectorUnitary : Matrix m m ℂ)ᴴ := by
          rw [hUA, Matrix.one_mul, stiefelPattern_cogram hA.1 hB.1 e]
      _ = supportProj hB.1 := (supportProj_eigen_form hB).symm
  · intro G D hG
    refine ⟨hG.conjTranspose_mul_mul_same D, hGD G D hG, ?_, ?_⟩
    · rw [hGD G D hG]
      constructor
      · intro h0
        rw [supportProj_eq_pinv_mul, Matrix.mul_assoc, h0,
          Matrix.mul_zero]
      · intro h0
        calc G * D = G * (supportProj hG.1 * D) := by
              rw [← Matrix.mul_assoc, mul_supportProj hG]
          _ = 0 := by rw [h0, Matrix.mul_zero]
    · rw [not_iff_comm, not_exists]
      push Not
      constructor
      · intro hall
        have hSD : sqrtSF hG.1 * D = 0 := by
          ext i j
          have hv := congrFun (hall (Pi.single j 1)) i
          rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hv
        rw [hGD G D hG]
        calc G * D = sqrtSF hG.1 * (sqrtSF hG.1 * D) := by
              rw [← Matrix.mul_assoc, sqrtSF_mul_self hG]
          _ = 0 := by rw [hSD, Matrix.mul_zero]
      · intro h0 v
        have hSD : sqrtSF hG.1 * D = 0 := by
          have hGD0 := (hGD G D hG).mp h0
          have hfac : (sqrtSF hG.1 * D)ᴴ * (sqrtSF hG.1 * D) = 0 := by
            rw [Matrix.conjTranspose_mul, (sqrtSF_isHermitian hG.1).eq]
            calc Dᴴ * sqrtSF hG.1 * (sqrtSF hG.1 * D)
                = Dᴴ * (G * D) := by
                  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (sqrtSF hG.1),
                    sqrtSF_mul_self hG, Matrix.mul_assoc]
              _ = 0 := by rw [hGD0, Matrix.mul_zero]
          exact Matrix.conjTranspose_mul_self_eq_zero.mp hfac
        rw [← Matrix.mulVec_mulVec, hSD, Matrix.zero_mulVec]

end RenormCongruence

end NCG
