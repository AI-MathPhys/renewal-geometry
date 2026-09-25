/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Determinantal nullity filtration (`cor:howe-nullity`)

`cor:howe-nullity` of the spacetime–gauge duality manuscript.  In the Howe-discriminant
setting the stacked commutator map `D(θ) X = ([c_1(θ), X], …, [c_s(θ), X])` is written in an
orthonormal basis of `𝒦 = M^⊥` (`dim 𝒦 = r`) as a matrix `D(θ)` with `r` columns; the commutant
`C*(c(θ))'` is `M ⊕ ker D(θ)`, so the number of *additional* commutant dimensions at `θ` is
the nullity `dim ker D(θ) = r - rank D(θ)` (`matrixNullity`,
`finrank_ker_eq_matrixNullity_toMatrix` for the basis bridge).

* `rank_le_iff_minors_eq_zero`: the rank-via-minors lemma
  `rank A ≤ q ↔ every (q+1)×(q+1) minor of A vanishes` (field coefficients);
* `howe_nullity_filtration`: **`cor:howe-nullity`, first clause** — for `1 ≤ k ≤ r` the locus
  `{θ : nullity D(θ) ≥ k}` is the common zero set of all `(r-k+1)×(r-k+1)` minors of `D(θ)`;
* `isClosed_nullity_ge`, `upperSemicontinuous_matrixNullity`: **`cor:howe-nullity`, second
  clause** — for a continuous family `θ ↦ D(θ)` every superlevel set `{nullity ≥ k}` is closed,
  i.e. the additional commutant dimension is upper semicontinuous.
-/

open Matrix Module

namespace RenewalGeometry

section Minors

variable {K : Type*} [Field K] {m k : Type*} [Fintype m] [Fintype k]

/-- If `q ≤ rank A`, some `q` distinct columns of `A` are linearly independent. -/
theorem exists_linearIndependent_cols (A : Matrix m k K) {q : ℕ} (hq : q ≤ A.rank) :
    ∃ g : Fin q → k, Function.Injective g ∧ LinearIndependent K (fun j => A.col (g j)) := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
  have : Finite κ := hli.finite
  let _ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = A.rank := by
    rw [rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hli]
  obtain ⟨e⟩ : Nonempty (Fin q ↪ κ) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, hcard]; exact hq)
  exact ⟨a ∘ e, ha.comp e.injective, hli.comp e e.injective⟩

/-- If `q ≤ rank A`, some `q × q` minor of `A` is nonzero. -/
theorem exists_minor_ne_zero (A : Matrix m k K) {q : ℕ} (hq : q ≤ A.rank) :
    ∃ (f : Fin q → m) (g : Fin q → k),
      Function.Injective f ∧ Function.Injective g ∧ (A.submatrix f g).det ≠ 0 := by
  obtain ⟨g, hg, hli⟩ := exists_linearIndependent_cols A hq
  set B := A.submatrix id g with hB
  have hBcol : B.col = fun j => A.col (g j) := by
    funext j i
    rfl
  have hrankB : B.rank = q := by
    rw [rank_eq_finrank_span_cols, hBcol, finrank_span_eq_card hli, Fintype.card_fin]
  have hrankBT : q ≤ Bᵀ.rank := by
    rw [rank_transpose, hrankB]
  obtain ⟨f, hf, hli'⟩ := exists_linearIndependent_cols Bᵀ hrankBT
  refine ⟨f, g, hf, hg, ?_⟩
  have hrows : (A.submatrix f g).row = fun i => Bᵀ.col (f i) := by
    funext i j
    rfl
  have hunit : IsUnit (A.submatrix f g) := by
    rw [← linearIndependent_rows_iff_isUnit, hrows]
    exact hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

/-- **Rank via minors**: `rank A ≤ q` exactly when every `(q+1) × (q+1)` minor of `A` vanishes
(minors indexed by arbitrary row/column selections; non-injective selections vanish trivially). -/
theorem rank_le_iff_minors_eq_zero (A : Matrix m k K) (q : ℕ) :
    A.rank ≤ q ↔
      ∀ (f : Fin (q + 1) → m) (g : Fin (q + 1) → k), (A.submatrix f g).det = 0 := by
  constructor
  · intro h f g
    by_contra hdet
    have hunit : IsUnit (A.submatrix f g) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have h1 := rank_of_isUnit _ hunit
    have h2 := rank_submatrix_le A f g
    rw [h1, Fintype.card_fin] at h2
    omega
  · intro h
    by_contra hlt
    obtain ⟨f, g, -, -, hdet⟩ := exists_minor_ne_zero A (q := q + 1) (not_le.mp hlt)
    exact hdet (h f g)

/-- The nullity `dim ker A` of a matrix: in the Howe setting, the number of additional commutant
dimensions carried by the kernel of the stacked commutator map. -/
noncomputable def matrixNullity (A : Matrix m k K) : ℕ :=
  finrank K (LinearMap.ker A.mulVecLin)

omit [Fintype m] in
/-- Rank–nullity: `nullity A + rank A = number of columns`. -/
theorem matrixNullity_add_rank (A : Matrix m k K) :
    matrixNullity A + A.rank = Fintype.card k := by
  unfold matrixNullity Matrix.rank
  rw [add_comm, LinearMap.finrank_range_add_finrank_ker, Module.finrank_pi]

/-- Basis bridge: the nullity of the matrix of a linear map `T : V → W` in bases of `V` and `W`
is `dim ker T`.  (For `T = D(θ)` on `𝒦 = M^⊥` this is the additional commutant dimension.) -/
theorem finrank_ker_eq_matrixNullity_toMatrix [DecidableEq k]
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (bV : Basis k K V) (bW : Basis m K W) (T : V →ₗ[K] W) :
    finrank K (LinearMap.ker T) = matrixNullity (LinearMap.toMatrix bV bW T) := by
  have : FiniteDimensional K V := Module.Finite.of_basis bV
  have h1 := matrixNullity_add_rank (LinearMap.toMatrix bV bW T)
  have h2 := LinearMap.finrank_range_add_finrank_ker T
  rw [rank_eq_finrank_range_toLin _ bW bV, Matrix.toLin_toMatrix] at h1
  rw [Module.finrank_eq_card_basis bV] at h2
  omega

end Minors

section Filtration

variable {K : Type*} [Field K] {m : Type*} [Fintype m]

/-- **`cor:howe-nullity`, first clause (determinantal nullity filtration).**  For a family
`θ ↦ D(θ)` of matrices with `r` columns and `1 ≤ k ≤ r`, the locus on which the kernel of
`D(θ)` — the additional commutant dimension of the Howe setting — has dimension at least `k` is
the common zero set of all `(r-k+1) × (r-k+1)` minors of `D(θ)`. -/
theorem howe_nullity_filtration {Θ : Type*} {r : ℕ} (D : Θ → Matrix m (Fin r) K)
    (k : ℕ) (_hk1 : 1 ≤ k) (hkr : k ≤ r) :
    {θ | k ≤ matrixNullity (D θ)} =
      {θ | ∀ (f : Fin (r - k + 1) → m) (g : Fin (r - k + 1) → Fin r),
        ((D θ).submatrix f g).det = 0} := by
  ext θ
  simp only [Set.mem_ofPred_eq]
  rw [← rank_le_iff_minors_eq_zero]
  have := matrixNullity_add_rank (D θ)
  rw [Fintype.card_fin] at this
  omega

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

/-- **`cor:howe-nullity`, second clause**: in a continuous family every superlevel set
`{θ : nullity D(θ) ≥ k}` is closed (the common zero set of finitely many continuous minors). -/
theorem isClosed_nullity_ge {Θ : Type*} [TopologicalSpace Θ] {r : ℕ}
    (D : Θ → Matrix m (Fin r) K) (hD : Continuous D) (k : ℕ) :
    IsClosed {θ | k ≤ matrixNullity (D θ)} := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases le_or_gt k r with hkr | hkr
  · rw [howe_nullity_filtration D k hk hkr]
    have hset : {θ | ∀ (f : Fin (r - k + 1) → m) (g : Fin (r - k + 1) → Fin r),
          ((D θ).submatrix f g).det = 0}
        = ⋂ (f : Fin (r - k + 1) → m) (g : Fin (r - k + 1) → Fin r),
          {θ | ((D θ).submatrix f g).det = 0} := by
      ext θ
      simp
    rw [hset]
    exact isClosed_iInter fun f => isClosed_iInter fun g =>
      isClosed_eq ((hD.matrix_submatrix f g).matrix_det) continuous_const
  · have hempty : {θ | k ≤ matrixNullity (D θ)} = ∅ := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have := matrixNullity_add_rank (D θ)
      rw [Fintype.card_fin] at this
      omega
    rw [hempty]
    exact isClosed_empty

/-- **`cor:howe-nullity`, second clause**: the additional commutant dimension
`θ ↦ dim ker D(θ)` is upper semicontinuous in every continuous family. -/
theorem upperSemicontinuous_matrixNullity {Θ : Type*} [TopologicalSpace Θ] {r : ℕ}
    (D : Θ → Matrix m (Fin r) K) (hD : Continuous D) :
    UpperSemicontinuous fun θ => matrixNullity (D θ) :=
  upperSemicontinuous_iff_isClosed_preimage.mpr fun k => isClosed_nullity_ge D hD k

end Filtration

end RenewalGeometry
