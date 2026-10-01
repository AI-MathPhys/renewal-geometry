/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Certificates.ProvenanceInnovationRank

/-!
# Same-source coefficient formula
  (`cor:endpoint-allocation-compiler`, spacetime–gauge duality manuscript)

The endpoint allocation residual of `thm:endpoint-allocation`
(`eq:endpoint-allocation-short`) is, for a typed synthesis `S_f : E_f → N_f` and an
endpoint subsource `T_f : G_gen → N_f`,

`𝔸_{f|G} = G_f − C_f* A_f⁻¹ C_f`,  `G_f = S_f* S_f`, `A_f = T_f* T_f`, `C_f = T_f* S_f`.

When the endpoint subsource is specified through a coefficient map `J : G_gen → E_f`
with `T_f = S_f J`, the residual is the same-source expression

`𝔸_{f|G} = G_f − G_f J (J* G_f J)⁻¹ J* G_f`   (`eq:endpoint-allocation-compiler`),

so the residual, its trace and its rank are functions of the typed source Gram `G_f`
and the compiler `J` alone.

* `allocationResidual S T` — `eq:endpoint-allocation-short`;
* `sameSourceResidual G J` — the right-hand side of `eq:endpoint-allocation-compiler`;
* `allocationResidual_eq_sameSource` — the boxed identity;
* `allocationResidual_trace_eq`, `allocationResidual_rank_eq` — the trace and the
  rank are determined by `(G_f, J)`.

The parent theorem `thm:endpoint-allocation` (matrix content) is proved in the second
section: with `A_f = T* T ≻ 0` and `P_fG = T A_f⁻¹ T*` (`eq:endpoint-subsource-projector`),

* `allocationResidual_eq_orthogonal`, `allocationResidual_posSemidef`,
  `allocationResidual_trace_hs` — `𝔸_{f|G} = S*(I − P_fG)S ⪰ 0`,
  `a_{f|G} = Tr 𝔸_{f|G} = ‖(I − P_fG)S‖²_HS` (`eq:endpoint-allocation-positive`);
* `rank_eq_card_add_rank_allocationResidual` — for a specified endpoint subsource
  `T = S J` (`Ran T ⊆ Ran S`), `n_f = rank G_f = dim G_gen + rank 𝔸_{f|G}`
  (`eq:endpoint-generation-excess`, with `dim G_gen = 3` in the paper);
* `allocationResidual_zero_iff` — `a_{f|G} = 0 ⟺ 𝔸_{f|G} = 0 ⟺ (I − P_fG)S = 0 ⟺
  n_f = dim G_gen` (`eq:endpoint-allocation-zero`; `(I − P_fG)S = 0` is `Ran S ⊆ Ran T`,
  i.e. `Ran T = Ran S = N_f` for a complete synthesis).

Rendering disclosed: the identity is an algebraic rewriting valid for every `J`
(Mathlib's `Matrix.inv` is total); the hypothesis `J* G_f J ≻ 0` of the paper is only
needed to interpret `(J* G_f J)⁻¹` as a genuine inverse, and is recorded in
`allocationResidual_eq_sameSource_of_posDef` for the record.  The "word native at a
flat historical depth" sentence is interpretive (it refers to
`thm:inserted-word-moments`) and is not formalised.
-/

open Matrix
open scoped ComplexOrder

namespace RenewalGeometry
namespace EndpointAllocationCompiler

variable {N E G : Type*} [Fintype N] [Fintype E] [Fintype G] [DecidableEq G]

/-- The endpoint allocation residual `𝔸_{f|G} = G_f − C_f* A_f⁻¹ C_f` of
`eq:endpoint-allocation-short`, with `G_f = S* S`, `A_f = T* T`, `C_f = T* S`. -/
noncomputable def allocationResidual (S : Matrix N E ℂ) (T : Matrix N G ℂ) :
    Matrix E E ℂ :=
  Sᴴ * S - (Tᴴ * S)ᴴ * (Tᴴ * T)⁻¹ * (Tᴴ * S)

/-- The same-source residual `G − G J (J* G J)⁻¹ J* G` of
`eq:endpoint-allocation-compiler`, a function of the typed Gram `G` and the compiler
`J` alone. -/
noncomputable def sameSourceResidual (Gf : Matrix E E ℂ) (J : Matrix E G ℂ) :
    Matrix E E ℂ :=
  Gf - Gf * J * (Jᴴ * Gf * J)⁻¹ * Jᴴ * Gf

/-- **`cor:endpoint-allocation-compiler`** (`eq:endpoint-allocation-compiler`): for
`T_f = S_f J`, the allocation residual equals the same-source residual built from
`G_f = S_f* S_f` and `J`. -/
theorem allocationResidual_eq_sameSource (S : Matrix N E ℂ) (J : Matrix E G ℂ) :
    allocationResidual S (S * J) = sameSourceResidual (Sᴴ * S) J := by
  simp only [allocationResidual, sameSourceResidual, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The same identity under the paper's hypothesis `J* G_f J ≻ 0`. -/
theorem allocationResidual_eq_sameSource_of_posDef (S : Matrix N E ℂ) (J : Matrix E G ℂ)
    (_hpos : (Jᴴ * (Sᴴ * S) * J).PosDef) :
    allocationResidual S (S * J) = sameSourceResidual (Sᴴ * S) J :=
  allocationResidual_eq_sameSource S J

/-- The allocation trace `a_{f|G}` is determined by `(G_f, J)`. -/
theorem allocationResidual_trace_eq (S : Matrix N E ℂ) (J : Matrix E G ℂ) :
    (allocationResidual S (S * J)).trace = (sameSourceResidual (Sᴴ * S) J).trace := by
  rw [allocationResidual_eq_sameSource]

/-- The excess rank `rank 𝔸_{f|G}` is determined by `(G_f, J)`. -/
theorem allocationResidual_rank_eq (S : Matrix N E ℂ) (J : Matrix E G ℂ) :
    (allocationResidual S (S * J)).rank = (sameSourceResidual (Sᴴ * S) J).rank := by
  rw [allocationResidual_eq_sameSource]

/-- Two typed syntheses with the same typed Gram and the same compiler have the same
allocation residual: no independent mixed Gram is required. -/
theorem allocationResidual_congr_gram {N' : Type*} [Fintype N']
    (S : Matrix N E ℂ) (S' : Matrix N' E ℂ) (hG : Sᴴ * S = S'ᴴ * S')
    (J : Matrix E G ℂ) :
    allocationResidual S (S * J) = allocationResidual S' (S' * J) := by
  rw [allocationResidual_eq_sameSource, allocationResidual_eq_sameSource, hG]

/-! ## The parent theorem `thm:endpoint-allocation` -/

section Parent

variable [DecidableEq N] [DecidableEq E]

/-- The squared Hilbert–Schmidt norm `‖A‖²_HS = ∑ |A i j|²`. -/
noncomputable def hsNormSq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- The endpoint subsource projector `P_fG = T A_f⁻¹ T*`
(`eq:endpoint-subsource-projector`). -/
noncomputable def subsourceProjector (T : Matrix N G ℂ) : Matrix N N ℂ :=
  T * (Tᴴ * T)⁻¹ * Tᴴ

omit [DecidableEq N] [DecidableEq E] in
theorem subsourceProjector_mul_self {T : Matrix N G ℂ} (hA : (Tᴴ * T).PosDef) :
    subsourceProjector T * subsourceProjector T = subsourceProjector T := by
  have hu : IsUnit (Tᴴ * T).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  simp only [subsourceProjector, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Tᴴ T, ← Matrix.mul_assoc (Tᴴ * T)⁻¹, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]

omit [DecidableEq N] [DecidableEq E] in
theorem subsourceProjector_conjTranspose {T : Matrix N G ℂ} (hA : (Tᴴ * T).PosDef) :
    (subsourceProjector T)ᴴ = subsourceProjector T := by
  simp only [subsourceProjector, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_nonsing_inv, hA.isHermitian.eq, Matrix.mul_assoc]

omit [DecidableEq N] [DecidableEq E] in
theorem subsourceProjector_mul {T : Matrix N G ℂ} (hA : (Tᴴ * T).PosDef) :
    subsourceProjector T * T = T := by
  have hu : IsUnit (Tᴴ * T).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  simp only [subsourceProjector, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

omit [DecidableEq N] [DecidableEq E] in
theorem subsourceProjector_rank {T : Matrix N G ℂ} (hA : (Tᴴ * T).PosDef) :
    (subsourceProjector T).rank = T.rank := by
  apply le_antisymm
  · simp only [subsourceProjector, Matrix.mul_assoc]
    exact Matrix.rank_mul_le_left T _
  · have h := Matrix.rank_mul_le_left (subsourceProjector T) T
    rwa [subsourceProjector_mul hA] at h

omit [DecidableEq N] [DecidableEq E] in
/-- `rank T_f = dim G_gen` when `A_f = T_f* T_f ≻ 0`. -/
theorem rank_eq_card_of_posDef {T : Matrix N G ℂ} (hA : (Tᴴ * T).PosDef) :
    T.rank = Fintype.card G := by
  rw [← Matrix.rank_conjTranspose_mul_self, Matrix.rank_of_isUnit _ hA.isUnit]

omit [Fintype E] [DecidableEq E] in
/-- **`eq:endpoint-allocation-positive`, identity**: `𝔸_{f|G} = S*(I − P_fG)S`. -/
theorem allocationResidual_eq_orthogonal (S : Matrix N E ℂ) (T : Matrix N G ℂ) :
    allocationResidual S T = Sᴴ * (1 - subsourceProjector T) * S := by
  simp only [allocationResidual, subsourceProjector, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_assoc]

omit [Fintype E] [DecidableEq E] in
/-- `𝔸_{f|G} = V* V` with `V = (I − P_fG) S`. -/
theorem allocationResidual_eq_gram (S : Matrix N E ℂ) {T : Matrix N G ℂ}
    (hA : (Tᴴ * T).PosDef) :
    allocationResidual S T
      = ((1 - subsourceProjector T) * S)ᴴ * ((1 - subsourceProjector T) * S) := by
  have hQH : (1 - subsourceProjector T)ᴴ = 1 - subsourceProjector T := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, subsourceProjector_conjTranspose hA]
  have hQ2 : (1 - subsourceProjector T) * (1 - subsourceProjector T)
      = 1 - subsourceProjector T := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      subsourceProjector_mul_self hA]
    abel
  rw [allocationResidual_eq_orthogonal, Matrix.conjTranspose_mul, hQH]
  calc Sᴴ * (1 - subsourceProjector T) * S
      = Sᴴ * ((1 - subsourceProjector T) * (1 - subsourceProjector T)) * S := by rw [hQ2]
    _ = Sᴴ * (1 - subsourceProjector T) * ((1 - subsourceProjector T) * S) := by
        simp only [Matrix.mul_assoc]

omit [DecidableEq E] in
/-- **`eq:endpoint-allocation-positive`, positivity**: `𝔸_{f|G} ⪰ 0`. -/
theorem allocationResidual_posSemidef (S : Matrix N E ℂ) {T : Matrix N G ℂ}
    (hA : (Tᴴ * T).PosDef) : (allocationResidual S T).PosSemidef := by
  rw [allocationResidual_eq_gram S hA]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq E] in
/-- **`eq:endpoint-allocation-positive`, trace**: `a_{f|G} = ‖(I − P_fG) S‖²_HS`. -/
theorem allocationResidual_trace_hs (S : Matrix N E ℂ) {T : Matrix N G ℂ}
    (hA : (Tᴴ * T).PosDef) :
    (allocationResidual S T).trace = (hsNormSq ((1 - subsourceProjector T) * S) : ℂ) := by
  rw [allocationResidual_eq_gram S hA]
  set V := (1 - subsourceProjector T) * S
  have hentry : ∀ j, (Vᴴ * V) j j = ∑ i, ((Complex.normSq (V i j) : ℝ) : ℂ) := by
    intro j
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  simp only [Matrix.trace, Matrix.diag, hentry, hsNormSq]
  push_cast
  rw [Finset.sum_comm]

omit [Fintype N] [DecidableEq G] [DecidableEq N] in
/-- Adjoining columns inside the range does not change the rank:
`rank [S J | S] = rank S`. -/
theorem rank_fromCols_mul_self (S : Matrix N E ℂ) (J : Matrix E G ℂ) :
    (Matrix.fromCols (S * J) S).rank = S.rank := by
  apply le_antisymm
  · have h := Matrix.mul_fromCols S J (1 : Matrix E E ℂ)
    rw [Matrix.mul_one] at h
    rw [← h]
    exact Matrix.rank_mul_le_left S _
  · have h := Matrix.fromCols_mul_fromRows (S * J) S (0 : Matrix G E ℂ) (1 : Matrix E E ℂ)
    rw [Matrix.mul_zero, Matrix.mul_one, zero_add] at h
    have hle := Matrix.rank_mul_le_left (Matrix.fromCols (S * J) S)
      (Matrix.fromRows (0 : Matrix G E ℂ) (1 : Matrix E E ℂ))
    rwa [h] at hle

omit [Fintype N] [DecidableEq N] [DecidableEq E] in
/-- The first block is dominated by the stacked matrix: `rank T ≤ rank [T | S]`. -/
theorem rank_le_rank_fromCols (T : Matrix N G ℂ) (S : Matrix N E ℂ) :
    T.rank ≤ (Matrix.fromCols T S).rank := by
  have h := Matrix.fromCols_mul_fromRows T S (1 : Matrix G G ℂ) (0 : Matrix E G ℂ)
  rw [Matrix.mul_zero, Matrix.mul_one, add_zero] at h
  have hle := Matrix.rank_mul_le_left (Matrix.fromCols T S)
    (Matrix.fromRows (1 : Matrix G G ℂ) (0 : Matrix E G ℂ))
  rwa [h] at hle

/-- **`eq:endpoint-generation-excess`**: for a specified endpoint subsource `T = S J`
with `T* T ≻ 0`, `n_f = rank G_f = rank S = dim G_gen + rank 𝔸_{f|G}`. -/
theorem rank_eq_card_add_rank_allocationResidual (S : Matrix N E ℂ) (J : Matrix E G ℂ)
    (hA : ((S * J)ᴴ * (S * J)).PosDef) :
    (Sᴴ * S).rank = Fintype.card G + (allocationResidual S (S * J)).rank := by
  set T := S * J with hT
  set P := subsourceProjector T
  have hstack := stacked_rank_innovation Tᵀ Sᵀ Pᵀ
    (by rw [← Matrix.transpose_mul, subsourceProjector_mul_self hA])
    (by rw [← Matrix.transpose_mul, subsourceProjector_mul hA])
    (by rw [Matrix.rank_transpose, Matrix.rank_transpose, subsourceProjector_rank hA])
  have hrows : (Matrix.fromRows Tᵀ Sᵀ).rank = S.rank := by
    rw [← Matrix.transpose_fromCols, Matrix.rank_transpose, hT, rank_fromCols_mul_self]
  have hres : (Sᵀ * (1 - Pᵀ)).rank = (allocationResidual S T).rank := by
    rw [allocationResidual_eq_gram S hA, Matrix.rank_conjTranspose_mul_self,
      ← Matrix.rank_transpose ((1 - P) * S), Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one]
  have hTrank : Tᵀ.rank = Fintype.card G := by
    rw [Matrix.rank_transpose, rank_eq_card_of_posDef hA]
  have hle : Tᵀ.rank ≤ (Matrix.fromRows Tᵀ Sᵀ).rank := by
    rw [Matrix.rank_transpose, ← Matrix.transpose_fromCols, Matrix.rank_transpose]
    exact rank_le_rank_fromCols T S
  rw [hrows, hres, hTrank] at hstack
  rw [hTrank] at hle
  rw [Matrix.rank_conjTranspose_mul_self]
  omega

/-- A matrix of rank zero is zero. -/
theorem eq_zero_of_rank_eq_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n ℂ} (h : A.rank = 0) : A = 0 := by
  have hrange : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
  have hlin : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hrange
  rw [← Matrix.toLin'_apply'] at hlin
  exact (LinearEquiv.map_eq_zero_iff _).mp hlin

/-- **`eq:endpoint-allocation-zero`**: `a_{f|G} = 0 ⟺ 𝔸_{f|G} = 0 ⟺ (I − P_fG) S = 0
⟺ n_f = dim G_gen`, for a specified endpoint subsource `T = S J` with `T* T ≻ 0`. -/
theorem allocationResidual_zero_iff (S : Matrix N E ℂ) (J : Matrix E G ℂ)
    (hA : ((S * J)ᴴ * (S * J)).PosDef) :
    ((allocationResidual S (S * J)).trace = 0 ↔ allocationResidual S (S * J) = 0)
    ∧ (allocationResidual S (S * J) = 0 ↔ (1 - subsourceProjector (S * J)) * S = 0)
    ∧ (allocationResidual S (S * J) = 0 ↔ (Sᴴ * S).rank = Fintype.card G) := by
  have hgram := allocationResidual_eq_gram S hA
  refine ⟨?_, ?_, ?_⟩
  · rw [hgram, Matrix.trace_conjTranspose_mul_self_eq_zero_iff,
      Matrix.conjTranspose_mul_self_eq_zero]
  · rw [hgram, Matrix.conjTranspose_mul_self_eq_zero]
  · rw [rank_eq_card_add_rank_allocationResidual S J hA]
    constructor
    · intro h
      rw [h, Matrix.rank_zero, add_zero]
    · intro h
      exact eq_zero_of_rank_eq_zero (by omega)

end Parent

end EndpointAllocationCompiler
end RenewalGeometry

