/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.FiniteProcessCombTomography
import RenewalGeometry.Algebra.MatrixKrausExistence

/-!
# Sequential isometric realization of finite process combs

Papers `emergent_spacetime` (`thm:supp-comb-tomography`) and
`predictive_spectral_geometry` (`thm:ncg-comb-tomography`).

This file builds the finite comb-realization theory from an *independent*
definition of a sequential quantum process and proves the comb conditions from
it, instead of storing them.

* `SequentialComb.SequentialIsometricComb`: memories `A_k` (`A_0` a point) and
  link isometries `V_k : H^in ⊗ A_k → H^out ⊗ A_{k+1}` (`V_kᴴ V_k = 1`).  Its
  cumulative isometry `W_k` (`cumulative`) is the sequential link of the `V_j`,
  and its Choi tensors are `R^(k) = W_k W_kᴴ` (`realizedChoi`): link followed by
  the final memory discard.
* `realizedChoi_isDeterministic`: **necessity** — the Choi tensors of every
  sequential isometric comb are positive, normalized and obey the nested
  output-trace recursion.
* `canonicalComb`: **sufficiency** — from a positive causal prefix family a
  sequential isometric comb with memories `Fin (rank R^(k))` is constructed;
  its link isometries are obtained by Gram matching of consecutive prefix
  factors (`exists_isometry_of_gram_eq`).  It realizes every prefix
  (`canonicalComb_realizedChoi`) and is prefix-support minimal.
* `exists_sequentialIsometricComb_iff`, `exists_realizing_comb_iff_terminal`,
  `exists_sequentialIsometricComb_iff_conditions`: the exact characterization
  "deterministic finite quantum process exactly when `R^(N) ⪰ 0`, causal trace
  recursion, `R^(0) = 1`", with *process* meaning the independent
  sequential-isometric notion (`isDeterministicCombThrough_iff_terminal`: the
  literal conditions force positivity of every prefix).
* `SequentialIsometricComb.memory_equiv_support`: `A_k ≅ supp R^(k)` for
  prefix-support-minimal realizations.
* `realizedChoi_rank_le_card`, `isPrefixSupportMinimal_iff_card_eq_rank`:
  memory dimension is at least `rank R^(k)`, with equality exactly for
  prefix-support-minimal realizations.
* `sequentialComb_unitary_covariance`: two prefix-support-minimal realizations
  of the same terminal tensor are related by memory unitaries `U_k` (`U_0 = I`)
  with `V'_k = (I ⊗ U_{k+1}) V_k (I ⊗ U_k)ᴴ` (`eq:supp-comb-unitary`,
  `eq:ncg-minimal-unitary-covariance`), `W'_k = (I ⊗ U_k) W_k`, and the unitary
  family is unique.
* `reducedKraus_covariant`: retained named operators (reduced Kraus operators of
  fixed external interventions) are transported by the same unitaries.
* Multi-slot tomography: `combProd` (product interventions), `combPairing R`
  (the multilinear intervention functional represented by `R`),
  `combPairing_injective` (uniqueness), `combDualTensor`/`combFrameTensor`
  (dual-frame reconstruction `eq:supp-comb-tomography`) with
  `combPairing_combFrameTensor` (it represents **all** multilinear intervention
  probabilities), `combFrameTensor_frame_independent` (frame independence, derived,
  not assumed), and `multilinear_eq_of_physical` (probabilities on physical
  trace-normalized positive probes already determine the functional).

Conventions: the slot spaces `O = H^out`, `I = H^in` are the same finite types at
every slot (as in `CombCarrier`); the newest slot is the outermost factor.
-/

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix
open scoped ComplexOrder Kronecker

namespace RenewalGeometry
namespace SequentialComb

universe u

/-! ## Gram matching -/

section GramMatch

variable {E F ι : Type*} [Fintype E] [Fintype F] [Fintype ι] [DecidableEq F] [DecidableEq ι]

/-- **Gram matching.**  If two families of vectors (the columns of `P` and `Q`)
have the same Gram matrix and the second family spans (`Q` has a right inverse
`L`), then `P L` is an isometry carrying the second family onto the first. -/
theorem exists_isometry_of_gram_eq (P : Matrix E ι ℂ) (Q : Matrix F ι ℂ)
    (hG : Pᴴ * P = Qᴴ * Q) (L : Matrix ι F ℂ) (hL : Q * L = 1) :
    (P * L)ᴴ * (P * L) = 1 ∧ P * L * Q = P := by
  have hQ : Q * (1 - L * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hL, Matrix.one_mul, sub_self]
  have hX : P * (1 - L * Q) = 0 := by
    rw [← Matrix.conjTranspose_mul_self_eq_zero]
    calc (P * (1 - L * Q))ᴴ * (P * (1 - L * Q))
        = (1 - L * Q)ᴴ * (Pᴴ * P) * (1 - L * Q) := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (Q * (1 - L * Q))ᴴ * (Q * (1 - L * Q)) := by
          rw [hG, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQ]; simp
  refine ⟨?_, ?_⟩
  · calc (P * L)ᴴ * (P * L) = Lᴴ * (Pᴴ * P) * L := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (Q * L)ᴴ * (Q * L) := by
          rw [hG, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hL]; simp
  · have h := hX
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    rw [Matrix.mul_assoc]
    exact h.symm

/-- Cancellation against a spanning family: `V Q = V' Q` with `Q L = 1` forces
`V = V'`. -/
theorem eq_of_mul_eq_of_rightInverse {G : Type*} [Fintype G] (V V' : Matrix G F ℂ)
    (Q : Matrix F ι ℂ) (L : Matrix ι F ℂ) (hL : Q * L = 1) (h : V * Q = V' * Q) :
    V = V' := by
  calc V = V * Q * L := by rw [Matrix.mul_assoc, hL, Matrix.mul_one]
    _ = V' * Q * L := by rw [h]
    _ = V' := by rw [Matrix.mul_assoc, hL, Matrix.mul_one]

end GramMatch

/-! ## Sequential isometric combs -/

variable {O I : Type u} [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]

/-- A **finite sequential isometric quantum process** (coherent comb) through
horizon `N`: memories `A_k` with `A_0` a single point (`A_0 = ℂ`) and link
isometries `V_k : H^in ⊗ A_k → H^out ⊗ A_{k+1}` for `k < N`. -/
structure SequentialIsometricComb (O I : Type u) [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (N : ℕ) where
  /-- The memory spaces `A_k = ℂ^{Mem k}`. -/
  Mem : ℕ → Type
  [memFintype : ∀ k, Fintype (Mem k)]
  [memDecidableEq : ∀ k, DecidableEq (Mem k)]
  [memZero : Unique (Mem 0)]
  /-- The link maps `V_k`. -/
  link : ∀ k, Matrix (O × Mem (k + 1)) (I × Mem k) ℂ
  /-- Each link is an isometry, `V_kᴴ V_k = 1`. -/
  isometry : ∀ k, k < N → (link k)ᴴ * link k = 1

attribute [instance] SequentialIsometricComb.memFintype SequentialIsometricComb.memDecidableEq
  SequentialIsometricComb.memZero

instance combCarrierZeroUnique : Unique (CombCarrier O I 0) :=
  inferInstanceAs (Unique PUnit)

namespace SequentialIsometricComb

variable {N : ℕ} (C : SequentialIsometricComb O I N)

/-- The cumulative isometry `W_k : I_k → O_k ⊗ A_k` through cut `k`, written as
the amplitude array `W_k (x, a)` with `x` the interleaved output/input index:
`W_{k+1} = (I ⊗ V_k)(W_k ⊗ I)`. -/
def cumulative : ∀ k, Matrix (CombCarrier O I k) (C.Mem k) ℂ
  | 0 => fun _ _ => 1
  | k + 1 => fun x a => ∑ b, C.link k (x.1, a) (x.2.1, b) * cumulative k x.2.2 b

/-- The Choi tensors realized by the comb: sequential link followed by the
final memory discard, `R^(k) = W_k W_kᴴ`. -/
def realizedChoi : CombPrefixFamily O I := fun k => C.cumulative k * (C.cumulative k)ᴴ

end SequentialIsometricComb

/-! ### Unfolding the newest slot -/

/-- The newest-slot unfolding of a prefix amplitude array: the vectors
`(o,a) ↦ W((o,i,x),a)` indexed by `(i,x)`. -/
def combUnfoldOut {k : ℕ} {A : Type*} (W : Matrix (CombCarrier O I (k + 1)) A ℂ) :
    Matrix (O × A) (I × CombCarrier O I k) ℂ :=
  fun oa ix => W (oa.1, ix) oa.2

/-- The input-extended prefix vectors `(j,b) ↦ δ_{ij} W(x,b)` indexed by `(i,x)`. -/
def combUnfoldIn {k : ℕ} {A : Type*} (W : Matrix (CombCarrier O I k) A ℂ) :
    Matrix (I × A) (I × CombCarrier O I k) ℂ :=
  fun jb ix => if jb.1 = ix.1 then W ix.2 jb.2 else 0

/-- Right inverse of `combUnfoldIn W` built from a left inverse of `W`. -/
def combUnfoldInv {k : ℕ} {A : Type*} (L : Matrix A (CombCarrier O I k) ℂ) :
    Matrix (I × CombCarrier O I k) (I × A) ℂ :=
  fun ix jb => if ix.1 = jb.1 then L jb.2 ix.2 else 0

theorem combOutputTrace_mul_conjTranspose {k : ℕ} {A : Type*} [Fintype A]
    (W : Matrix (CombCarrier O I (k + 1)) A ℂ) :
    combOutputTrace (W * Wᴴ) = ((combUnfoldOut W)ᴴ * combUnfoldOut W)ᵀ := by
  ext ix jy
  simp only [combOutputTrace, combUnfoldOut, Matrix.mul_apply, conjTranspose_apply,
    transpose_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]
  rfl

theorem combIdentityExtension_mul_conjTranspose {k : ℕ} {A : Type*} [Fintype A]
    (W : Matrix (CombCarrier O I k) A ℂ) :
    combIdentityExtension (W * Wᴴ) = ((combUnfoldIn W)ᴴ * combUnfoldIn W)ᵀ := by
  ext ix jy
  simp only [combIdentityExtension, combUnfoldIn, Matrix.mul_apply, conjTranspose_apply,
    transpose_apply, Fintype.sum_prod_type, apply_ite star, star_zero, ite_mul, mul_ite,
    zero_mul, mul_zero]
  rw [Finset.sum_comm]
  by_cases h : ix.1 = jy.1
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos h]
    ring
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_neg h]

theorem combUnfoldOut_injective {k : ℕ} {A : Type*} :
    Function.Injective (combUnfoldOut (O := O) (I := I) (k := k) (A := A)) := by
  intro W W' h
  funext x a
  exact congrFun (congrFun h (x.1, a)) x.2

theorem combUnfoldIn_eq_kronecker {k : ℕ} {A : Type*} (W : Matrix (CombCarrier O I k) A ℂ) :
    combUnfoldIn W = (1 : Matrix I I ℂ) ⊗ₖ Wᵀ := by
  ext jb ix
  simp only [combUnfoldIn, kroneckerMap_apply, one_apply, transpose_apply, ite_mul, one_mul,
    zero_mul]

theorem combUnfoldInv_eq_kronecker {k : ℕ} {A : Type*} (L : Matrix A (CombCarrier O I k) ℂ) :
    combUnfoldInv L = (1 : Matrix I I ℂ) ⊗ₖ Lᵀ := by
  ext ix jb
  simp only [combUnfoldInv, kroneckerMap_apply, one_apply, transpose_apply, ite_mul, one_mul,
    zero_mul]

theorem combUnfoldIn_mul_combUnfoldInv {k : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (W : Matrix (CombCarrier O I k) A ℂ) (L : Matrix A (CombCarrier O I k) ℂ)
    (hL : L * W = 1) : combUnfoldIn W * combUnfoldInv L = 1 := by
  rw [combUnfoldIn_eq_kronecker, combUnfoldInv_eq_kronecker, ← mul_kronecker_mul,
    Matrix.one_mul, ← transpose_mul, hL, transpose_one, one_kronecker_one]

namespace SequentialIsometricComb

variable {N : ℕ} (C : SequentialIsometricComb O I N)

theorem combUnfoldOut_cumulative_succ (k : ℕ) :
    combUnfoldOut (C.cumulative (k + 1)) = C.link k * combUnfoldIn (C.cumulative k) := by
  ext oa ix
  simp only [combUnfoldOut, combUnfoldIn, cumulative, Matrix.mul_apply, Fintype.sum_prod_type,
    mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

theorem realizedChoi_zero : C.realizedChoi 0 = 1 := by
  ext x y
  have hxy : x = y := Subsingleton.elim _ _
  subst hxy
  show (C.cumulative 0 * (C.cumulative 0)ᴴ) x x = (1 : Matrix (CombCarrier O I 0) _ ℂ) x x
  rw [Matrix.mul_apply, Matrix.one_apply_eq]
  simp only [conjTranspose_apply]
  simp [cumulative]

/-- **Necessity.**  The Choi tensors of every sequential isometric comb are
positive, normalized (`R^(0) = 1`) and obey the nested output-trace recursion
`Tr_out R^(k+1) = I ⊗ R^(k)` (complete positivity and causal normalization). -/
theorem realizedChoi_isDeterministic : IsDeterministicCombThrough C.realizedChoi N := by
  refine ⟨C.realizedChoi_zero, fun k _ => posSemidef_self_mul_conjTranspose _, ?_⟩
  intro k hk
  change combOutputTrace (C.cumulative (k + 1) * (C.cumulative (k + 1))ᴴ) =
    combIdentityExtension (C.cumulative k * (C.cumulative k)ᴴ)
  rw [combOutputTrace_mul_conjTranspose, combIdentityExtension_mul_conjTranspose,
    combUnfoldOut_cumulative_succ, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (C.link k)ᴴ, C.isometry k hk, Matrix.one_mul]

end SequentialIsometricComb

/-! ## Support-minimal factors -/

section Factor

variable {d A : Type*} [Fintype d] [Fintype A]

/-- **Prefix support minimality** (`eq:ncg-prefix-minimality`): the vectors
`(⟨η| ⊗ I) W ξ`, i.e. the rows `W x` of the amplitude array, span the memory. -/
def IsPrefixSupportMinimal (W : Matrix d A ℂ) : Prop :=
  Submodule.span ℂ (Set.range W) = ⊤

theorem isPrefixSupportMinimal_iff_exists_leftInverse [DecidableEq A] (W : Matrix d A ℂ) :
    IsPrefixSupportMinimal W ↔ ∃ L : Matrix A d ℂ, L * W = 1 := by
  have hrange : LinearMap.range Wᵀ.mulVecLin = Submodule.span ℂ (Set.range W) := by
    rw [Matrix.range_mulVecLin]
    rfl
  constructor
  · intro h
    have hsurj : ∀ v : A → ℂ, ∃ u : d → ℂ, Wᵀ *ᵥ u = v := by
      intro v
      have hv : v ∈ LinearMap.range Wᵀ.mulVecLin := by
        rw [hrange, h]; exact Submodule.mem_top
      obtain ⟨u, hu⟩ := hv
      exact ⟨u, hu⟩
    choose g hg using fun b : A => hsurj (Pi.single b 1)
    refine ⟨(Matrix.of fun x b => g b x)ᵀ, ?_⟩
    apply transpose_injective
    rw [transpose_mul, transpose_transpose, transpose_one]
    ext a b
    have h1 := congrFun (hg b) a
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [mulVec, dotProduct, Matrix.of_apply] at h1 ⊢
    rw [h1, Pi.single_apply]
  · rintro ⟨L, hL⟩
    unfold IsPrefixSupportMinimal
    rw [← hrange, LinearMap.range_eq_top]
    intro v
    refine ⟨Lᵀ *ᵥ v, ?_⟩
    change Wᵀ *ᵥ (Lᵀ *ᵥ v) = v
    rw [mulVec_mulVec, ← transpose_mul, hL, transpose_one, one_mulVec]

theorem isPrefixSupportMinimal_iff_rank [DecidableEq A] (W : Matrix d A ℂ) :
    IsPrefixSupportMinimal W ↔ W.rank = Fintype.card A := by
  rw [isPrefixSupportMinimal_iff_exists_leftInverse]
  constructor
  · rintro ⟨L, hL⟩
    refine le_antisymm (rank_le_card_width W) ?_
    calc Fintype.card A = (1 : Matrix A A ℂ).rank := (rank_one).symm
      _ = (L * W).rank := by rw [hL]
      _ ≤ W.rank := rank_mul_le_right L W
  · intro h
    have hker : LinearMap.ker W.mulVecLin = ⊥ := by
      have hsum := LinearMap.finrank_range_add_finrank_ker W.mulVecLin
      have hr : Module.finrank ℂ (LinearMap.range W.mulVecLin) = Fintype.card A := h
      rw [hr, Module.finrank_fintype_fun_eq_card] at hsum
      exact Submodule.finrank_eq_zero.mp (by omega)
    have hker' : LinearMap.ker (Wᴴ * W).mulVecLin = ⊥ := by
      rw [ker_mulVecLin_conjTranspose_mul_self, hker]
    have hinj : Function.Injective (Wᴴ * W).mulVec := LinearMap.ker_eq_bot.mp hker'
    have hunit : IsUnit (Wᴴ * W) := mulVec_injective_iff_isUnit.mp hinj
    refine ⟨(Wᴴ * W)⁻¹ * Wᴴ, ?_⟩
    rw [Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hunit)]

theorem rank_mul_conjTranspose_le_card (W : Matrix d A ℂ) :
    (W * Wᴴ).rank ≤ Fintype.card A := by
  rw [rank_self_mul_conjTranspose]
  exact rank_le_card_width W

/-- Every positive matrix factors as `F Fᴴ` through a memory of dimension
exactly its rank. -/
theorem exists_rank_factor [DecidableEq d] (J : Matrix d d ℂ) (hJ : J.PosSemidef) :
    ∃ F : Matrix d (Fin J.rank) ℂ, F * Fᴴ = J := by
  classical
  set hH := hJ.1 with hHdef
  set U : Matrix d d ℂ := (hH.eigenvectorUnitary : Matrix d d ℂ) with hUdef
  set ev := hH.eigenvalues with hev
  have hspec : J = U * diagonal (fun i => (ev i : ℂ)) * Uᴴ := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rfl
  have hcard : Fintype.card {i // ev i ≠ 0} = J.rank := (hH.rank_eq_card_non_zero_eigs).symm
  let e : {i // ev i ≠ 0} ≃ Fin J.rank := Fintype.equivFinOfCardEq hcard
  refine ⟨Matrix.of fun x a => U x (e.symm a) * ((Real.sqrt (ev (e.symm a)) : ℝ) : ℂ), ?_⟩
  ext x y
  rw [Matrix.mul_apply]
  simp only [conjTranspose_apply, Matrix.of_apply]
  have hterm : ∀ s : {i // ev i ≠ 0},
      U x s * ((Real.sqrt (ev s) : ℝ) : ℂ) * star (U y s * ((Real.sqrt (ev s) : ℝ) : ℂ)) =
        U x s * (ev s : ℂ) * star (U y s) := by
    intro s
    have hnn : 0 ≤ ev s := hJ.eigenvalues_nonneg s
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
    have : ((Real.sqrt (ev s) : ℝ) : ℂ) * ((Real.sqrt (ev s) : ℝ) : ℂ) = (ev s : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hnn]
    calc U x s * ((Real.sqrt (ev s) : ℝ) : ℂ) * (star (U y s) * ((Real.sqrt (ev s) : ℝ) : ℂ))
        = U x s * (((Real.sqrt (ev s) : ℝ) : ℂ) * ((Real.sqrt (ev s) : ℝ) : ℂ)) *
            star (U y s) := by ring
      _ = _ := by rw [this]; rfl
  calc ∑ a : Fin J.rank, U x (e.symm a) * ((Real.sqrt (ev (e.symm a)) : ℝ) : ℂ) *
        star (U y (e.symm a) * ((Real.sqrt (ev (e.symm a)) : ℝ) : ℂ))
      = ∑ s : {i // ev i ≠ 0}, U x s * (ev s : ℂ) * star (U y s) :=
        Fintype.sum_equiv e.symm _ _ (fun a => hterm (e.symm a))
    _ = ∑ i, U x i * (ev i : ℂ) * star (U y i) := by
        rw [← Fintype.sum_subtype_add_sum_subtype (fun i => ev i ≠ 0)
          (fun i => U x i * (ev i : ℂ) * star (U y i))]
        have hz : ∑ i : {i // ¬ ev i ≠ 0}, U x i * (ev i : ℂ) * star (U y i) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          have : ev i = 0 := not_not.mp i.2
          simp [this]
        rw [hz, add_zero]
    _ = J x y := by
        rw [hspec, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_diagonal, conjTranspose_apply]

end Factor

/-! ## Sufficiency: the canonical sequential realization -/

section Canonical

/-- Memory dimension of a sequential realization is at least the rank of the
realized prefix tensor. -/
theorem SequentialIsometricComb.realizedChoi_rank_le_card {N : ℕ}
    (C : SequentialIsometricComb O I N) (k : ℕ) :
    (C.realizedChoi k).rank ≤ Fintype.card (C.Mem k) :=
  rank_mul_conjTranspose_le_card _

/-- Equality of memory dimension and prefix rank holds exactly for
prefix-support-minimal realizations. -/
theorem SequentialIsometricComb.isPrefixSupportMinimal_iff_card_eq_rank {N : ℕ}
    (C : SequentialIsometricComb O I N) (k : ℕ) :
    IsPrefixSupportMinimal (C.cumulative k) ↔
      Fintype.card (C.Mem k) = (C.realizedChoi k).rank := by
  rw [isPrefixSupportMinimal_iff_rank, SequentialIsometricComb.realizedChoi,
    rank_self_mul_conjTranspose, eq_comm]

/-- The canonical memories `A_0 = ℂ`, `A_{k+1} = ℂ^{rank R^(k+1)}`. -/
def canonicalMem (R : CombPrefixFamily O I) : ℕ → Type
  | 0 => PUnit
  | k + 1 => Fin (R (k + 1)).rank

instance canonicalMemFintype (R : CombPrefixFamily O I) : ∀ k, Fintype (canonicalMem R k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k + 1 => inferInstanceAs (Fintype (Fin (R (k + 1)).rank))

instance canonicalMemDecidableEq (R : CombPrefixFamily O I) :
    ∀ k, DecidableEq (canonicalMem R k)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | k + 1 => inferInstanceAs (DecidableEq (Fin (R (k + 1)).rank))

instance canonicalMemZeroUnique (R : CombPrefixFamily O I) : Unique (canonicalMem R 0) :=
  inferInstanceAs (Unique PUnit)

/-- The canonical rank factors `F_k` of the prefixes, `F_k F_kᴴ = R^(k)`. -/
def canonicalFactor (R : CombPrefixFamily O I) :
    ∀ k, Matrix (CombCarrier O I k) (canonicalMem R k) ℂ
  | 0 => fun _ _ => 1
  | k + 1 => by
      classical
      exact if h : (R (k + 1)).PosSemidef then
        Classical.choose (exists_rank_factor (R (k + 1)) h) else 0

theorem unitPrefix_mul_conjTranspose {A : Type*} [Fintype A] [Unique A]
    (W : Matrix (CombCarrier O I 0) A ℂ) (hW : ∀ x a, W x a = 1) : W * Wᴴ = 1 := by
  ext x y
  have hxy : x = y := Subsingleton.elim _ _
  subst hxy
  rw [Matrix.mul_apply, Matrix.one_apply_eq]
  simp only [conjTranspose_apply, hW]
  simp

variable {R : CombPrefixFamily O I} {N : ℕ}

theorem canonicalFactor_gram (hR : IsDeterministicCombThrough R N) (k : ℕ) (hk : k ≤ N) :
    canonicalFactor R k * (canonicalFactor R k)ᴴ = R k := by
  cases k with
  | zero =>
      rw [hR.1]
      exact unitPrefix_mul_conjTranspose _ fun _ _ => rfl
  | succ k =>
      simp only [canonicalFactor, dif_pos (hR.2.1 (k + 1) hk)]
      exact Classical.choose_spec (exists_rank_factor (R (k + 1)) (hR.2.1 (k + 1) hk))

theorem card_canonicalMem (hR : IsDeterministicCombThrough R N) (k : ℕ) (hk : k ≤ N) :
    Fintype.card (canonicalMem R k) = (R k).rank := by
  cases k with
  | zero =>
      rw [hR.1, rank_one]
      rfl
  | succ k => exact Fintype.card_fin _

theorem canonicalFactor_minimal (hR : IsDeterministicCombThrough R N) (k : ℕ) (hk : k ≤ N) :
    IsPrefixSupportMinimal (canonicalFactor R k) := by
  rw [isPrefixSupportMinimal_iff_rank, ← rank_self_mul_conjTranspose,
    canonicalFactor_gram hR k hk, card_canonicalMem hR k hk]

/-- The link isometry between consecutive canonical prefix factors (Schmidt /
minimal-purification step of the proof). -/
theorem exists_canonicalLink (hR : IsDeterministicCombThrough R N) (k : ℕ) (hk : k < N) :
    ∃ V : Matrix (O × canonicalMem R (k + 1)) (I × canonicalMem R k) ℂ,
      Vᴴ * V = 1 ∧ V * combUnfoldIn (canonicalFactor R k) =
        combUnfoldOut (canonicalFactor R (k + 1)) := by
  obtain ⟨L, hL⟩ := (isPrefixSupportMinimal_iff_exists_leftInverse _).1
    (canonicalFactor_minimal hR k hk.le)
  have hG : (combUnfoldOut (canonicalFactor R (k + 1)))ᴴ *
        combUnfoldOut (canonicalFactor R (k + 1)) =
      (combUnfoldIn (canonicalFactor R k))ᴴ * combUnfoldIn (canonicalFactor R k) := by
    apply transpose_injective
    rw [← combOutputTrace_mul_conjTranspose, ← combIdentityExtension_mul_conjTranspose,
      canonicalFactor_gram hR (k + 1) hk, canonicalFactor_gram hR k hk.le]
    exact hR.2.2 k hk
  obtain ⟨h1, h2⟩ := exists_isometry_of_gram_eq _ _ hG _ (combUnfoldIn_mul_combUnfoldInv _ L hL)
  exact ⟨_, h1, h2⟩

/-- **The canonical support-minimal sequential realization** of a positive
causal prefix family. -/
def canonicalComb (R : CombPrefixFamily O I) (N : ℕ) (hR : IsDeterministicCombThrough R N) :
    SequentialIsometricComb O I N where
  Mem := canonicalMem R
  link k := if hk : k < N then Classical.choose (exists_canonicalLink hR k hk) else 0
  isometry k hk := by
    simp only [dif_pos hk]
    exact (Classical.choose_spec (exists_canonicalLink hR k hk)).1

theorem canonicalComb_cumulative (hR : IsDeterministicCombThrough R N) :
    ∀ k, k ≤ N → (canonicalComb R N hR).cumulative k = canonicalFactor R k
  | 0, _ => rfl
  | k + 1, hk => by
      apply combUnfoldOut_injective
      rw [SequentialIsometricComb.combUnfoldOut_cumulative_succ,
        canonicalComb_cumulative hR k (by omega)]
      change (if hk' : k < N then Classical.choose (exists_canonicalLink hR k hk') else 0) *
        combUnfoldIn (canonicalFactor R k) = _
      rw [dif_pos (by omega)]
      exact (Classical.choose_spec (exists_canonicalLink hR k (by omega))).2

/-- The canonical comb realizes every prefix tensor. -/
theorem canonicalComb_realizedChoi (hR : IsDeterministicCombThrough R N) (k : ℕ) (hk : k ≤ N) :
    (canonicalComb R N hR).realizedChoi k = R k := by
  change (canonicalComb R N hR).cumulative k * ((canonicalComb R N hR).cumulative k)ᴴ = R k
  rw [canonicalComb_cumulative hR k hk]
  exact canonicalFactor_gram hR k hk

/-- The canonical comb is prefix-support minimal at every cut. -/
theorem canonicalComb_minimal (hR : IsDeterministicCombThrough R N) (k : ℕ) (hk : k ≤ N) :
    IsPrefixSupportMinimal ((canonicalComb R N hR).cumulative k) := by
  rw [canonicalComb_cumulative hR k hk]
  exact canonicalFactor_minimal hR k hk

/-- The canonical memory dimensions are `dim A_k = rank R^(k)`. -/
theorem canonicalComb_card (hR : IsDeterministicCombThrough R N) (k : ℕ) (hk : k ≤ N) :
    Fintype.card ((canonicalComb R N hR).Mem k) = (R k).rank :=
  card_canonicalMem hR k hk

end Canonical

/-! ## The exact characterization -/

/-- **Deterministic finite quantum process exactly when.**  A prefix family is
realized (at every cut through `N`) by a finite sequential isometric quantum
process if and only if it is positive, normalized and obeys the nested
output-trace recursion (`eq:supp-comb-conditions`, `eq:ncg-comb-causality`).
The process notion on the left is the independent sequential-isometric one. -/
theorem exists_sequentialIsometricComb_iff (R : CombPrefixFamily O I) (N : ℕ) :
    (∃ C : SequentialIsometricComb O I N, ∀ k, k ≤ N → C.realizedChoi k = R k) ↔
      IsDeterministicCombThrough R N := by
  constructor
  · rintro ⟨C, hC⟩
    have hD := C.realizedChoi_isDeterministic
    refine ⟨?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [← hC 0 (Nat.zero_le _)]; exact hD.1
    · rw [← hC k hk]; exact hD.2.1 k hk
    · rw [← hC (k + 1) hk, ← hC k hk.le]; exact hD.2.2 k hk
  · intro hR
    exact ⟨canonicalComb R N hR, fun k hk => canonicalComb_realizedChoi hR k hk⟩

/-- Terminal form: an `N`-slot tensor is the Choi tensor of a finite sequential
isometric quantum process exactly when it is the terminal member of a positive,
normalized, causal prefix family. -/
theorem exists_realizing_comb_iff_terminal (N : ℕ)
    (T : Matrix (CombCarrier O I N) (CombCarrier O I N) ℂ) :
    (∃ C : SequentialIsometricComb O I N, C.realizedChoi N = T) ↔
      IsDeterministicTerminalComb N T := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C.realizedChoi, hC, C.realizedChoi_isDeterministic⟩
  · rintro ⟨R, hRT, hR⟩
    exact ⟨canonicalComb R N hR, (canonicalComb_realizedChoi hR N le_rfl).trans hRT⟩

/-- **`A_k ≅ supp R^(k)`**: for a prefix-support-minimal realization the
cumulative isometry identifies the memory `A_k` linearly with the support (range)
of the realized prefix tensor `R^(k) = W_k W_kᴴ`. -/
theorem SequentialIsometricComb.memory_equiv_support {N : ℕ} (C : SequentialIsometricComb O I N)
    (k : ℕ) (hmin : IsPrefixSupportMinimal (C.cumulative k)) :
    ∃ e : (C.Mem k → ℂ) ≃ₗ[ℂ] LinearMap.range (C.realizedChoi k).mulVecLin,
      ∀ v, (e v : CombCarrier O I k → ℂ) = C.cumulative k *ᵥ v := by
  obtain ⟨L, hL⟩ := (isPrefixSupportMinimal_iff_exists_leftInverse _).1 hmin
  set W := C.cumulative k
  have hinj : Function.Injective W.mulVecLin := by
    intro v w hvw
    have := congrArg (fun u => L *ᵥ u) hvw
    simpa [Matrix.mulVecLin_apply, mulVec_mulVec, hL] using this
  have hle : LinearMap.range (W * Wᴴ).mulVecLin ≤ LinearMap.range W.mulVecLin := by
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have heq : LinearMap.range (W * Wᴴ).mulVecLin = LinearMap.range W.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      change (W * Wᴴ).rank = W.rank
      exact rank_self_mul_conjTranspose W)
  refine ⟨(LinearEquiv.ofInjective W.mulVecLin hinj).trans (LinearEquiv.ofEq _ _ heq.symm),
    fun v => rfl⟩

/-! ## Sequential uniqueness: memory-unitary covariance -/

section Covariance

theorem transpose_conjTranspose_mul_transpose {d A : Type*} [Fintype A]
    (W : Matrix d A ℂ) : (Wᵀ)ᴴ * Wᵀ = (W * Wᴴ)ᵀ := by
  ext x y
  simp only [Matrix.mul_apply, conjTranspose_apply, transpose_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem combUnfoldIn_mul_transpose {k : ℕ} {A A' : Type*} [Fintype A]
    (W : Matrix (CombCarrier O I k) A ℂ) (U : Matrix A' A ℂ) :
    combUnfoldIn (W * Uᵀ) = ((1 : Matrix I I ℂ) ⊗ₖ U) * combUnfoldIn W := by
  rw [combUnfoldIn_eq_kronecker, combUnfoldIn_eq_kronecker, transpose_mul, transpose_transpose,
    ← mul_kronecker_mul, Matrix.one_mul]

theorem combUnfoldOut_mul_transpose {k : ℕ} {A A' : Type*} [Fintype A]
    (W : Matrix (CombCarrier O I (k + 1)) A ℂ) (U : Matrix A' A ℂ) :
    combUnfoldOut (W * Uᵀ) = ((1 : Matrix O O ℂ) ⊗ₖ U) * combUnfoldOut W := by
  ext oa ix
  change ∑ a, W (oa.1, ix) a * Uᵀ a oa.2 =
    ∑ j, ((1 : Matrix O O ℂ) ⊗ₖ U) oa j * combUnfoldOut W j ix
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [combUnfoldOut, kroneckerMap_apply, Matrix.one_apply, transpose_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem one_kronecker_isometry {X A A' : Type*} [Fintype X] [DecidableEq X] [Fintype A']
    [Fintype A] [DecidableEq A] (U : Matrix A' A ℂ) (h : Uᴴ * U = 1) :
    ((1 : Matrix X X ℂ) ⊗ₖ U)ᴴ * ((1 : Matrix X X ℂ) ⊗ₖ U) = 1 := by
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, h,
    one_kronecker_one]

/-- Minimal-purification uniqueness at one cut: two prefix-support-minimal factors
of the same prefix tensor differ by a unique memory unitary, `W' = (I ⊗ U) W`. -/
theorem exists_memory_unitary {d A A' : Type*} [Fintype d] [DecidableEq d] [Fintype A]
    [Fintype A'] [DecidableEq A] [DecidableEq A'] (W : Matrix d A ℂ) (W' : Matrix d A' ℂ)
    (hmin : IsPrefixSupportMinimal W) (hmin' : IsPrefixSupportMinimal W')
    (hG : W * Wᴴ = W' * W'ᴴ) :
    ∃ U : Matrix A' A ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ W' = W * Uᵀ := by
  obtain ⟨L, hL⟩ := (isPrefixSupportMinimal_iff_exists_leftInverse W).1 hmin
  obtain ⟨L', hL'⟩ := (isPrefixSupportMinimal_iff_exists_leftInverse W').1 hmin'
  have hQ : Wᵀ * Lᵀ = 1 := by rw [← transpose_mul, hL, transpose_one]
  have hQ' : W'ᵀ * L'ᵀ = 1 := by rw [← transpose_mul, hL', transpose_one]
  have hG1 : (W'ᵀ)ᴴ * W'ᵀ = (Wᵀ)ᴴ * Wᵀ := by
    rw [transpose_conjTranspose_mul_transpose, transpose_conjTranspose_mul_transpose, hG]
  obtain ⟨hU1, hU2⟩ := exists_isometry_of_gram_eq W'ᵀ Wᵀ hG1 Lᵀ hQ
  obtain ⟨-, hV2⟩ := exists_isometry_of_gram_eq Wᵀ W'ᵀ hG1.symm L'ᵀ hQ'
  set U := W'ᵀ * Lᵀ
  set V := Wᵀ * L'ᵀ
  have hVU : V * U = 1 := by
    apply eq_of_mul_eq_of_rightInverse _ _ Wᵀ Lᵀ hQ
    rw [Matrix.mul_assoc, hU2, hV2, Matrix.one_mul]
  have hUV : U * V = 1 := by
    apply eq_of_mul_eq_of_rightInverse _ _ W'ᵀ L'ᵀ hQ'
    rw [Matrix.mul_assoc, hV2, hU2, Matrix.one_mul]
  have hstar : Uᴴ = V := by
    calc Uᴴ = Uᴴ * (U * V) := by rw [hUV, Matrix.mul_one]
      _ = (Uᴴ * U) * V := (Matrix.mul_assoc _ _ _).symm
      _ = V := by rw [hU1, Matrix.one_mul]
  refine ⟨U, hU1, by rw [hstar, hUV], ?_⟩
  apply transpose_injective
  rw [transpose_mul, transpose_transpose, hU2]

variable {N : ℕ}

/-- Prefix tensors of two sequential realizations with the same terminal tensor
coincide (the prefixes are derived from the terminal comb). -/
theorem SequentialIsometricComb.realizedChoi_eq_of_terminal [Nonempty I]
    (C C' : SequentialIsometricComb O I N) (hT : C.realizedChoi N = C'.realizedChoi N) :
    ∀ k, k ≤ N → C.realizedChoi k = C'.realizedChoi k :=
  causalCombPrefixes_unique_from_terminal C.realizedChoi_isDeterministic
    C'.realizedChoi_isDeterministic hT

/-- The cumulative isometries of a sequential comb with dressed links: if
`V'_k = (I ⊗ U_{k+1}) V_k (I ⊗ U_k)ᴴ` for isometries `U_k` with `U_0 = I`, then
`W'_k = (I ⊗ U_k) W_k`. -/
theorem SequentialIsometricComb.cumulative_eq_of_covariant (C C' : SequentialIsometricComb O I N)
    (U : ∀ k, Matrix (C'.Mem k) (C.Mem k) ℂ) (hU : ∀ k, k ≤ N → (U k)ᴴ * U k = 1)
    (hU0 : ∀ a b, U 0 a b = 1)
    (hcov : ∀ k, k < N → C'.link k =
      ((1 : Matrix O O ℂ) ⊗ₖ U (k + 1)) * C.link k * ((1 : Matrix I I ℂ) ⊗ₖ U k)ᴴ) :
    ∀ k, k ≤ N → C'.cumulative k = C.cumulative k * (U k)ᵀ
  | 0, _ => by
      ext x a'
      rw [Matrix.mul_apply]
      simp [SequentialIsometricComb.cumulative, hU0]
  | k + 1, hk => by
      apply combUnfoldOut_injective
      rw [SequentialIsometricComb.combUnfoldOut_cumulative_succ,
        SequentialIsometricComb.cumulative_eq_of_covariant C C' U hU hU0 hcov k (by omega),
        combUnfoldIn_mul_transpose,
        hcov k (by omega), combUnfoldOut_mul_transpose,
        SequentialIsometricComb.combUnfoldOut_cumulative_succ]
      calc ((1 : Matrix O O ℂ) ⊗ₖ U (k + 1)) * C.link k * ((1 : Matrix I I ℂ) ⊗ₖ U k)ᴴ *
            (((1 : Matrix I I ℂ) ⊗ₖ U k) * combUnfoldIn (C.cumulative k))
          = ((1 : Matrix O O ℂ) ⊗ₖ U (k + 1)) * C.link k *
            ((((1 : Matrix I I ℂ) ⊗ₖ U k)ᴴ * ((1 : Matrix I I ℂ) ⊗ₖ U k)) *
              combUnfoldIn (C.cumulative k)) := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [one_kronecker_isometry _ (hU k (by omega)), Matrix.one_mul, Matrix.mul_assoc]

/-- **Sequential uniqueness** (`eq:supp-comb-unitary`,
`eq:ncg-minimal-unitary-covariance`).  Two prefix-support-minimal sequential
isometric realizations of the same terminal Choi tensor are related by memory
unitaries `U_k` with `U_0 = I`: `W'_k = (I ⊗ U_k) W_k` at every cut and
`V'_k = (I ⊗ U_{k+1}) V_k (I ⊗ U_k)ᴴ` for every link; the unitary family is
unique among isometric families with `U_0 = I` satisfying the link relation. -/
theorem sequentialComb_unitary_covariance [Nonempty I] (C C' : SequentialIsometricComb O I N)
    (hmin : ∀ k, k ≤ N → IsPrefixSupportMinimal (C.cumulative k))
    (hmin' : ∀ k, k ≤ N → IsPrefixSupportMinimal (C'.cumulative k))
    (hT : C.realizedChoi N = C'.realizedChoi N) :
    ∃ U : ∀ k, Matrix (C'.Mem k) (C.Mem k) ℂ,
      (∀ k, k ≤ N → (U k)ᴴ * U k = 1 ∧ U k * (U k)ᴴ = 1) ∧
      (∀ a b, U 0 a b = 1) ∧
      (∀ k, k ≤ N → C'.cumulative k = C.cumulative k * (U k)ᵀ) ∧
      (∀ k, k < N → C'.link k =
        ((1 : Matrix O O ℂ) ⊗ₖ U (k + 1)) * C.link k * ((1 : Matrix I I ℂ) ⊗ₖ U k)ᴴ) ∧
      ∀ U' : ∀ k, Matrix (C'.Mem k) (C.Mem k) ℂ,
        (∀ k, k ≤ N → (U' k)ᴴ * U' k = 1) → (∀ a b, U' 0 a b = 1) →
        (∀ k, k < N → C'.link k =
          ((1 : Matrix O O ℂ) ⊗ₖ U' (k + 1)) * C.link k * ((1 : Matrix I I ℂ) ⊗ₖ U' k)ᴴ) →
        ∀ k, k ≤ N → U' k = U k := by
  have hpre := C.realizedChoi_eq_of_terminal C' hT
  have hex : ∀ k, k ≤ N → ∃ U : Matrix (C'.Mem k) (C.Mem k) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ C'.cumulative k = C.cumulative k * Uᵀ :=
    fun k hk => exists_memory_unitary _ _ (hmin k hk) (hmin' k hk) (hpre k hk)
  choose! U hU using hex
  have hU0 : ∀ a b, U 0 a b = 1 := by
    intro a b
    have h := congrFun (congrFun (hU 0 (Nat.zero_le _)).2.2 default) a
    rw [Matrix.mul_apply] at h
    have hb : b = default := Subsingleton.elim _ _
    subst hb
    simpa [SequentialIsometricComb.cumulative] using h.symm
  -- cancellation against the spanning input-extended prefix vectors
  have hcancel : ∀ k, k ≤ N → ∀ X Y : Matrix (O × C'.Mem (k + 1)) (I × C'.Mem k) ℂ,
      X * combUnfoldIn (C'.cumulative k) = Y * combUnfoldIn (C'.cumulative k) → X = Y := by
    intro k hk X Y h
    obtain ⟨L, hL⟩ := (isPrefixSupportMinimal_iff_exists_leftInverse _).1 (hmin' k hk)
    exact eq_of_mul_eq_of_rightInverse X Y _ _ (combUnfoldIn_mul_combUnfoldInv _ L hL) h
  have hcov : ∀ k, k < N → C'.link k =
      ((1 : Matrix O O ℂ) ⊗ₖ U (k + 1)) * C.link k * ((1 : Matrix I I ℂ) ⊗ₖ U k)ᴴ := by
    intro k hk
    apply hcancel k hk.le
    rw [← SequentialIsometricComb.combUnfoldOut_cumulative_succ, (hU (k + 1) hk).2.2,
      combUnfoldOut_mul_transpose, (hU k hk.le).2.2, combUnfoldIn_mul_transpose,
      SequentialIsometricComb.combUnfoldOut_cumulative_succ]
    calc ((1 : Matrix O O ℂ) ⊗ₖ U (k + 1)) * (C.link k * combUnfoldIn (C.cumulative k))
        = ((1 : Matrix O O ℂ) ⊗ₖ U (k + 1)) * C.link k *
            ((((1 : Matrix I I ℂ) ⊗ₖ U k)ᴴ * ((1 : Matrix I I ℂ) ⊗ₖ U k)) *
              combUnfoldIn (C.cumulative k)) := by
          rw [one_kronecker_isometry _ (hU k hk.le).1, Matrix.one_mul, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨U, fun k hk => ⟨(hU k hk).1, (hU k hk).2.1⟩, hU0, fun k hk => (hU k hk).2.2, hcov, ?_⟩
  intro U' hU' hU'0 hcov' k hk
  have hW := C.cumulative_eq_of_covariant C' U' hU' hU'0 hcov' k hk
  obtain ⟨L, hL⟩ := (isPrefixSupportMinimal_iff_exists_leftInverse _).1 (hmin k hk)
  have hQ : (C.cumulative k)ᵀ * Lᵀ = 1 := by rw [← transpose_mul, hL, transpose_one]
  apply eq_of_mul_eq_of_rightInverse _ _ _ _ hQ
  rw [← transpose_transpose (U' k * _), transpose_mul, transpose_transpose, ← hW,
    ← transpose_transpose (U k * _), transpose_mul, transpose_transpose, ← (hU k hk).2.2]

end Covariance

/-! ## Transport of retained operators: reduced Kraus operators -/

section Reduced

variable {A A' B B' : Type*} [Fintype A] [Fintype A'] [Fintype B] [Fintype B']

/-- The `(o, i)` block `a' a ↦ V (o, a') (i, a)` of a link map. -/
def linkBlock (V : Matrix (O × A') (I × A) ℂ) (o : O) (i : I) : Matrix A' A ℂ :=
  Matrix.of fun a' a => V (o, a') (i, a)

/-- The reduced Kraus operator `A_k → A_{k+1}` obtained by contracting a link with a
fixed external intervention vector `m` on `H^out ⊗ H^in`:
`K_m = ∑_{o,i} conj(m(o,i)) ⟨o| V |i⟩`. -/
def reducedKraus (V : Matrix (O × A') (I × A) ℂ) (m : O × I → ℂ) : Matrix A' A ℂ :=
  ∑ o, ∑ i, star (m (o, i)) • linkBlock V o i

theorem linkBlock_kronecker_mul (V : Matrix (O × A') (I × A) ℂ) (Ua : Matrix B' A' ℂ)
    (o : O) (i : I) :
    linkBlock (((1 : Matrix O O ℂ) ⊗ₖ Ua) * V) o i = Ua * linkBlock V o i := by
  ext b' a
  simp only [linkBlock, Matrix.of_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

theorem linkBlock_mul_kronecker (V : Matrix (O × A') (I × A) ℂ) (Ub : Matrix B A ℂ)
    (o : O) (i : I) :
    linkBlock (V * ((1 : Matrix I I ℂ) ⊗ₖ Ub)ᴴ) o i = linkBlock V o i * Ubᴴ := by
  ext a' b
  simp only [linkBlock, Matrix.of_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [conjTranspose_apply, kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul,
    zero_mul, star_mul', apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

theorem linkBlock_covariant (V : Matrix (O × A') (I × A) ℂ)
    (Ua : Matrix B' A' ℂ) (Ub : Matrix B A ℂ) (o : O) (i : I) :
    linkBlock (((1 : Matrix O O ℂ) ⊗ₖ Ua) * V * ((1 : Matrix I I ℂ) ⊗ₖ Ub)ᴴ) o i =
      Ua * linkBlock V o i * Ubᴴ := by
  rw [linkBlock_mul_kronecker, linkBlock_kronecker_mul]

/-- **Retained operators are transported by the memory unitaries**: dressing a
link by `V' = (I ⊗ U_a) V (I ⊗ U_b)ᴴ` dresses every reduced Kraus operator,
`K'_m = U_a K_m U_bᴴ`. -/
theorem reducedKraus_covariant (V : Matrix (O × A') (I × A) ℂ)
    (Ua : Matrix B' A' ℂ) (Ub : Matrix B A ℂ) (m : O × I → ℂ) :
    reducedKraus (((1 : Matrix O O ℂ) ⊗ₖ Ua) * V * ((1 : Matrix I I ℂ) ⊗ₖ Ub)ᴴ) m =
      Ua * reducedKraus V m * Ubᴴ := by
  simp only [reducedKraus, linkBlock_covariant, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul]

end Reduced

/-! ## Multi-slot tomography -/

section Tomography

/-- Slot coordinates of a chronologically nested carrier index: slot `j` carries
the output/input pair of the `(j+1)`-st intervention. -/
def combSlot : ∀ {n : ℕ}, CombCarrier O I n → Fin n → O × I
  | 0, _ => Fin.elim0
  | _ + 1, x => Fin.snoc (α := fun _ => O × I) (combSlot x.2.2) (x.1, x.2.1)

/-- Inverse of `combSlot`. -/
def combUnslot : ∀ {n : ℕ}, (Fin n → O × I) → CombCarrier O I n
  | 0, _ => PUnit.unit
  | n + 1, f => (((f (Fin.last n)).1, ((f (Fin.last n)).2, combUnslot (Fin.init f))) :
      O × (I × CombCarrier O I n))

theorem combUnslot_combSlot : ∀ {n : ℕ} (x : CombCarrier O I n), combUnslot (combSlot x) = x
  | 0, _ => Subsingleton.elim _ _
  | n + 1, x => by
      change (((combSlot x (Fin.last n)).1, ((combSlot x (Fin.last n)).2,
        combUnslot (Fin.init (combSlot x)))) : O × (I × CombCarrier O I n)) = x
      have h1 : combSlot x (Fin.last n) = (x.1, x.2.1) := by
        simp [combSlot]
      have h2 : Fin.init (combSlot x) = combSlot x.2.2 := by
        simp [combSlot]
      rw [h1, h2, combUnslot_combSlot]
      rfl

theorem combSlot_combUnslot : ∀ {n : ℕ} (f : Fin n → O × I), combSlot (combUnslot f) = f
  | 0, f => funext fun j => Fin.elim0 j
  | n + 1, f => by
      change Fin.snoc (α := fun _ => O × I) (combSlot (combUnslot (Fin.init f)))
        ((f (Fin.last n)).1, (f (Fin.last n)).2) = f
      rw [combSlot_combUnslot]
      exact Fin.snoc_init_self f

/-- The slot-coordinate equivalence `CombCarrier O I n ≃ (Fin n → O × I)`. -/
def combSlotEquiv (n : ℕ) : CombCarrier O I n ≃ (Fin n → O × I) where
  toFun := combSlot
  invFun := combUnslot
  left_inv := combUnslot_combSlot
  right_inv := combSlot_combUnslot

theorem combSlot_injective {n : ℕ} : Function.Injective (combSlot (O := O) (I := I) (n := n)) :=
  (combSlotEquiv n).injective

/-- The product intervention `M_n ⊗ ⋯ ⊗ M_1` on the nested carrier. -/
def combProd {n : ℕ} (M : Fin n → Matrix (O × I) (O × I) ℂ) :
    Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ :=
  Matrix.of fun x y => ∏ j, M j (combSlot x j) (combSlot y j)

/-- Pairings of product tensors factor slotwise. -/
theorem trace_combProd_mul {n : ℕ} (A B : Fin n → Matrix (O × I) (O × I) ℂ) :
    (combProd A * combProd B).trace = ∏ j, (A j * B j).trace := by
  classical
  have hL : (combProd A * combProd B).trace =
      ∑ x : CombCarrier O I n, ∑ y : CombCarrier O I n,
        ∏ j, (A j (combSlot x j) (combSlot y j) * B j (combSlot y j) (combSlot x j)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, combProd, Matrix.of_apply,
      Finset.prod_mul_distrib]
  have hR : ∏ j, (A j * B j).trace =
      ∏ j, ∑ q : (O × I) × (O × I), A j q.1 q.2 * B j q.2 q.1 := by
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [hL, hR, Fintype.prod_sum]
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => O × I) (fun _ => O × I)).symm.sum_comp,
    Fintype.sum_prod_type]
  rw [← (combSlotEquiv (O := O) (I := I) n).sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← (combSlotEquiv (O := O) (I := I) n).sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  rfl

theorem combProd_conjTranspose {n : ℕ} (A : Fin n → Matrix (O × I) (O × I) ℂ) :
    (combProd A)ᴴ = combProd (fun j => (A j)ᴴ) := by
  ext x y
  simp only [combProd, conjTranspose_apply, Matrix.of_apply, star_prod]

/-- Products of matrix units are matrix units. -/
theorem combProd_single {n : ℕ} (x₀ y₀ : CombCarrier O I n) :
    combProd (fun j => Matrix.single (combSlot x₀ j) (combSlot y₀ j) (1 : ℂ)) =
      Matrix.single x₀ y₀ 1 := by
  ext x y
  simp only [combProd, Matrix.of_apply, Matrix.single_apply, Fintype.prod_boole]
  by_cases h : x₀ = x ∧ y₀ = y
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg]
    intro hall
    apply h
    exact ⟨combSlot_injective (funext fun j => (hall j).1),
      combSlot_injective (funext fun j => (hall j).2)⟩

/-- The entry functional `M ↦ M p q`. -/
def entryLM (p q : O × I) : Matrix (O × I) (O × I) ℂ →ₗ[ℂ] ℂ where
  toFun M := M p q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The multilinear entry map `(M_j)_j ↦ (⊗_j M_j)(x, y)`. -/
def combEntryML {n : ℕ} (x y : CombCarrier O I n) :
    MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap
    (fun j => entryLM (combSlot x j) (combSlot y j))

theorem combEntryML_apply {n : ℕ} (x y : CombCarrier O I n)
    (M : Fin n → Matrix (O × I) (O × I) ℂ) : combEntryML x y M = combProd M x y := by
  simp [combEntryML, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    entryLM, combProd]
  rfl

/-- **The multilinear intervention functional represented by a tensor**:
`(M_1, …, M_n) ↦ Tr(R (M_n ⊗ ⋯ ⊗ M_1))`. -/
def combPairing {n : ℕ} (R : Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ) :
    MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ :=
  ∑ x, ∑ y, R x y • combEntryML y x

theorem combPairing_apply {n : ℕ} (R : Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ)
    (M : Fin n → Matrix (O × I) (O × I) ℂ) : combPairing R M = (R * combProd M).trace := by
  simp only [combPairing, MultilinearMap.sum_apply, MultilinearMap.smul_apply, combEntryML_apply,
    smul_eq_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply]

/-- **Uniqueness of the representing tensor**: a tensor is determined by the
multilinear intervention functional it represents. -/
theorem combPairing_injective {n : ℕ} :
    Function.Injective (combPairing (O := O) (I := I) (n := n)) := by
  intro R R' h
  ext x y
  have hxy := congrArg (fun f => f (fun j => Matrix.single (combSlot y j) (combSlot x j) (1 : ℂ))) h
  simp only [combPairing_apply, combProd_single] at hxy
  have key : ∀ S : Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ,
      (S * Matrix.single y x (1 : ℂ)).trace = S x y := by
    intro S
    simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply]
    simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rwa [key, key] at hxy

/-- Expansion of a matrix in a spanning frame with trace-dual basis. -/
theorem frame_expansion {d P : Type*} [Fintype d] [Fintype P] [DecidableEq P]
    (probe dual : P → Matrix d d ℂ)
    (hdual : ∀ a b, (dual a * probe b).trace = if a = b then 1 else 0)
    (hspan : Submodule.span ℂ (Set.range probe) = ⊤) (M : Matrix d d ℂ) :
    M = ∑ a, (dual a * M).trace • probe a := by
  have hM : M ∈ Submodule.span ℂ (Set.range probe) := hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hM
  have hcoef : ∀ b, (dual b * M).trace = c b := by
    intro b
    rw [← hc, Matrix.mul_sum, Matrix.trace_sum]
    simp only [Matrix.mul_smul, Matrix.trace_smul, hdual, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  conv_lhs => rw [← hc]
  simp only [hcoef]

/-- The dual-frame reconstruction `R = ∑_α p(F_α) D^{α_n} ⊗ ⋯ ⊗ D^{α_1}`
(`eq:supp-comb-tomography`, `eq:ncg-comb-tomography`) for slot frames
`probe j` with trace-duals `dual j`. -/
def combDualTensor {n : ℕ} {P : Fin n → Type*} [∀ j, Fintype (P j)]
    (probe dual : ∀ j, P j → Matrix (O × I) (O × I) ℂ)
    (p : MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ) :
    Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ :=
  ∑ α : (∀ j, P j), p (fun j => probe j (α j)) • combProd (fun j => dual j (α j))

/-- **Representation lemma**: when every slot frame spans and has a trace-dual
basis, the dual-frame tensor represents **all** multilinear intervention
probabilities. -/
theorem combPairing_combDualTensor {n : ℕ} {P : Fin n → Type*} [∀ j, Fintype (P j)]
    [∀ j, DecidableEq (P j)] (probe dual : ∀ j, P j → Matrix (O × I) (O × I) ℂ)
    (hdual : ∀ j a b, (dual j a * probe j b).trace = if a = b then 1 else 0)
    (hspan : ∀ j, Submodule.span ℂ (Set.range (probe j)) = ⊤)
    (p : MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ) :
    combPairing (combDualTensor probe dual p) = p := by
  classical
  refine MultilinearMap.ext fun M => ?_
  rw [combPairing_apply, combDualTensor, Matrix.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, trace_combProd_mul, smul_eq_mul]
  have hM : M = fun j => ∑ a, (dual j a * M j).trace • probe j a :=
    funext fun j => frame_expansion (probe j) (dual j) (hdual j) (hspan j) (M j)
  conv_rhs => rw [hM, MultilinearMap.map_sum]
  simp only [MultilinearMap.map_smul_univ, smul_eq_mul]
  exact Finset.sum_congr rfl fun α _ => mul_comm _ _

/-- The canonical (matrix-unit) frame. -/
def unitProbe (st : (O × I) × (O × I)) : Matrix (O × I) (O × I) ℂ := Matrix.single st.1 st.2 1

/-- The trace-dual of the matrix-unit frame. -/
def unitDual (st : (O × I) × (O × I)) : Matrix (O × I) (O × I) ℂ := Matrix.single st.2 st.1 1

theorem unit_duality (a b : (O × I) × (O × I)) :
    (unitDual a * unitProbe b).trace = if a = b then 1 else 0 := by
  obtain ⟨s, t⟩ := a
  obtain ⟨s', t'⟩ := b
  simp only [unitDual, unitProbe]
  by_cases hs : s = s'
  · subst hs
    rw [Matrix.single_mul_single_same, one_mul]
    by_cases ht : t = t'
    · subst ht; simp
    · rw [Matrix.trace_single_eq_of_ne _ _ _ ht, if_neg]
      intro h; exact ht (congrArg Prod.snd h)
  · have h0 : Matrix.single t s (1 : ℂ) * Matrix.single s' t' (1 : ℂ) = 0 := by
      ext a b
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases h1 : s = c
      · subst h1
        simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
        split_ifs with h2 h3 <;> first | rfl | exact absurd h2.1 (Ne.symm hs)
      · simp [h1]
    rw [h0, Matrix.trace_zero, if_neg]
    intro h; exact hs (congrArg Prod.fst h)

theorem unit_span :
    Submodule.span ℂ (Set.range (unitProbe (O := O) (I := I))) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun s _ => Submodule.sum_mem _ fun t _ => ?_
  have : Matrix.single s t (M s t) = M s t • unitProbe (s, t) := by
    rw [unitProbe, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(s, t), rfl⟩)

/-- The tensor representing a multilinear intervention functional, reconstructed in
the canonical matrix-unit frame. -/
def combRepTensor {n : ℕ} (p : MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ) :
    Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ :=
  combDualTensor (fun _ => unitProbe) (fun _ => unitDual) p

theorem combPairing_combRepTensor {n : ℕ}
    (p : MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ) :
    combPairing (combRepTensor p) = p :=
  combPairing_combDualTensor _ _ (fun _ => unit_duality) (fun _ => unit_span) p

/-- Representing tensors are exactly the canonical reconstruction. -/
theorem combPairing_eq_iff {n : ℕ} (R : Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ)
    (p : MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ) :
    combPairing R = p ↔ R = combRepTensor p := by
  constructor
  · intro h
    exact combPairing_injective (h.trans (combPairing_combRepTensor p).symm)
  · rintro rfl
    exact combPairing_combRepTensor p

theorem combPairing_combRepTensor_of_eq {n : ℕ}
    (R : Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ) :
    combRepTensor (combPairing R) = R :=
  ((combPairing_eq_iff R (combPairing R)).1 rfl).symm

/-- The physical dual-frame reconstruction from slot frames of trace-normalized
positive Choi probes. -/
def combFrameTensor {n : ℕ} (F : Fin n → PhysicalChoiTomographyFrame (O × I))
    (p : MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ) :
    Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ :=
  combDualTensor (fun j => (F j).probe) (fun j => (F j).dual) p

/-- The physical dual-frame tensor represents every multilinear intervention
probability. -/
theorem combPairing_combFrameTensor {n : ℕ} (F : Fin n → PhysicalChoiTomographyFrame (O × I))
    (hspan : ∀ j, Submodule.span ℂ (Set.range (F j).probe) = ⊤)
    (p : MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ) :
    combPairing (combFrameTensor F p) = p :=
  combPairing_combDualTensor _ _ (fun j => (F j).duality) hspan p

/-- The physical reconstruction is the canonical representing tensor. -/
theorem combFrameTensor_eq_combRepTensor {n : ℕ}
    (F : Fin n → PhysicalChoiTomographyFrame (O × I))
    (hspan : ∀ j, Submodule.span ℂ (Set.range (F j).probe) = ⊤)
    (p : MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ) :
    combFrameTensor F p = combRepTensor p :=
  (combPairing_eq_iff _ p).1 (combPairing_combFrameTensor F hspan p)

/-- **Frame independence** (derived): two spanning physical frame families
reconstruct the same tensor from the same intervention functional. -/
theorem combFrameTensor_frame_independent {n : ℕ}
    (F G : Fin n → PhysicalChoiTomographyFrame (O × I))
    (hF : ∀ j, Submodule.span ℂ (Set.range (F j).probe) = ⊤)
    (hG : ∀ j, Submodule.span ℂ (Set.range (G j).probe) = ⊤)
    (p : MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ) :
    combFrameTensor F p = combFrameTensor G p := by
  rw [combFrameTensor_eq_combRepTensor F hF, combFrameTensor_eq_combRepTensor G hG]

/-- The reconstructed tensor is Hermitian when the intervention probabilities of
physical probes are real. -/
theorem combFrameTensor_isHermitian {n : ℕ} (F : Fin n → PhysicalChoiTomographyFrame (O × I))
    (p : MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ)
    (hreal : ∀ α : (∀ j, (F j).Probe), (p (fun j => (F j).probe (α j))).im = 0) :
    (combFrameTensor F p).IsHermitian := by
  unfold combFrameTensor combDualTensor
  rw [IsHermitian, conjTranspose_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hs : star (p (fun j => (F j).probe (α j))) = p (fun j => (F j).probe (α j)) :=
    Complex.conj_eq_iff_im.mpr (hreal α)
  have hd : (fun j => ((F j).dual (α j))ᴴ) = fun j => (F j).dual (α j) :=
    funext fun j => (F j).dualHermitian (α j)
  rw [conjTranspose_smul, combProd_conjTranspose, hd, hs]

/-- A multilinear map is determined by its values on tuples from a spanning set. -/
theorem multilinear_eq_of_eq_on_spanning {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    (S : Set M₁) (hS : Submodule.span ℂ S = ⊤) (f g : MultilinearMap ℂ (fun _ : ι => M₁) M₂)
    (h : ∀ m : ι → M₁, (∀ i, m i ∈ S) → f m = g m) : f = g := by
  have key : ∀ s : Finset ι, ∀ m : ι → M₁, (∀ i, i ∉ s → m i ∈ S) → (f - g) m = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro m hm
        rw [MultilinearMap.sub_apply, h m (fun i => hm i (Finset.notMem_empty i)), sub_self]
    | insert i s hi ih =>
        intro m hm
        have hx : ∀ x ∈ Submodule.span ℂ S, (f - g) (Function.update m i x) = 0 := by
          intro x hxs
          induction hxs using Submodule.span_induction with
          | mem x hx =>
              apply ih
              intro j hj
              by_cases hji : j = i
              · subst hji; simpa using hx
              · rw [Function.update_of_ne hji]
                exact hm j (by simp [hji, hj])
          | zero => exact MultilinearMap.map_update_zero _ _ _
          | add x y _ _ hx hy => rw [MultilinearMap.map_update_add, hx, hy, add_zero]
          | smul a x _ hx => rw [MultilinearMap.map_update_smul, hx, smul_zero]
        have := hx (m i) (hS ▸ Submodule.mem_top)
        rwa [Function.update_eq_self] at this
  ext m
  have := key Finset.univ m (fun i hi => absurd (Finset.mem_univ i) hi)
  rwa [MultilinearMap.sub_apply, sub_eq_zero] at this

/-- Trace-normalized positive matrices span all matrices. -/
theorem physicalProbes_span {d : Type*} [Fintype d] :
    Submodule.span ℂ {M : Matrix d d ℂ | M.PosSemidef ∧ (M.trace).re ≤ 1} = ⊤ := by
  rw [eq_top_iff]
  intro M _
  have hherm : ∀ H : Matrix d d ℂ, H.IsHermitian →
      H ∈ Submodule.span ℂ {M : Matrix d d ℂ | M.PosSemidef ∧ (M.trace).re ≤ 1} := by
    intro H hH
    obtain ⟨A, B, s, t, hA, hB, hAtr, hBtr, -, -, hsplit⟩ := cp_frame_span H hH
    rw [hsplit]
    refine Submodule.sub_mem _ ?_ ?_
    · rw [← Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hA, hAtr⟩)
    · rw [← Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hB, hBtr⟩)
  rw [matrix_eq_hermitian_parts M]
  exact Submodule.add_mem _ (hherm _ (matrixHermitianRealPart_isHermitian M))
    (Submodule.smul_mem _ _ (hherm _ (matrixHermitianImaginaryPart_isHermitian M)))

/-- **Physical probes suffice**: two multilinear intervention functionals agreeing
on every tuple of trace-normalized positive Choi probes coincide. -/
theorem multilinear_eq_of_physical {n : ℕ}
    (f g : MultilinearMap ℂ (fun _ : Fin n => Matrix (O × I) (O × I) ℂ) ℂ)
    (h : ∀ M : Fin n → Matrix (O × I) (O × I) ℂ,
      (∀ j, (M j).PosSemidef ∧ ((M j).trace).re ≤ 1) → f M = g M) : f = g :=
  multilinear_eq_of_eq_on_spanning _ physicalProbes_span f g h

/-- A tensor is determined by its intervention probabilities on physical probes. -/
theorem combTensor_eq_of_physical {n : ℕ}
    (R R' : Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ)
    (h : ∀ M : Fin n → Matrix (O × I) (O × I) ℂ,
      (∀ j, (M j).PosSemidef ∧ ((M j).trace).re ≤ 1) →
        (R * combProd M).trace = (R' * combProd M).trace) : R = R' := by
  apply combPairing_injective
  apply multilinear_eq_of_physical
  intro M hM
  rw [combPairing_apply, combPairing_apply]
  exact h M hM

end Tomography

/-! ## The paper's literal comb conditions -/

/-- Partial traces of positive tensors are positive. -/
theorem combOutputTrace_posSemidef {n : ℕ} {R : Matrix (CombCarrier O I (n + 1))
    (CombCarrier O I (n + 1)) ℂ} (hR : R.PosSemidef) : (combOutputTrace R).PosSemidef := by
  have h : combOutputTrace R = ∑ o : O, R.submatrix (fun ix : I × CombCarrier O I n =>
      ((o, ix) : O × (I × CombCarrier O I n))) (fun ix => ((o, ix) : O × (I × CombCarrier O I n))) := by
    ext ix jy
    simp only [combOutputTrace, Matrix.sum_apply, Matrix.submatrix_apply]
    rfl
  rw [h]
  exact Finset.sum_induction _ _ (fun A B hA hB => hA.add hB) PosSemidef.zero
    fun o _ => hR.submatrix _

/-- A prefix whose identity extension is positive is positive. -/
theorem posSemidef_of_combIdentityExtension [Nonempty I] {n : ℕ}
    {R : Matrix (CombCarrier O I n) (CombCarrier O I n) ℂ}
    (h : (combIdentityExtension (O := O) R).PosSemidef) : R.PosSemidef := by
  have i₀ : I := Classical.arbitrary I
  have hsub := h.submatrix (fun x : CombCarrier O I n => (i₀, x))
  have : (combIdentityExtension (O := O) R).submatrix (fun x : CombCarrier O I n => (i₀, x))
      (fun x => (i₀, x)) = R := by
    ext x y
    simp [combIdentityExtension]
  rwa [this] at hsub

/-- **The paper's conditions** (`eq:supp-comb-conditions`): terminal positivity,
the nested trace recursion and `R^(0) = 1` already force positivity of every
prefix, so they are equivalent to `IsDeterministicCombThrough`. -/
theorem isDeterministicCombThrough_iff_terminal [Nonempty I] (R : CombPrefixFamily O I) (N : ℕ) :
    IsDeterministicCombThrough R N ↔
      R 0 = 1 ∧ (R N).PosSemidef ∧
        ∀ k, k < N → combOutputTrace (R (k + 1)) = combIdentityExtension (R k) := by
  constructor
  · rintro ⟨h0, hpos, hrec⟩
    exact ⟨h0, hpos N le_rfl, hrec⟩
  · rintro ⟨h0, hN, hrec⟩
    refine ⟨h0, fun k hk => ?_, hrec⟩
    exact Nat.decreasingInduction (motive := fun j _ => (R j).PosSemidef)
      (fun j hj ih => by
        apply posSemidef_of_combIdentityExtension (O := O)
        rw [← hrec j hj]
        exact combOutputTrace_posSemidef ih) hN hk

/-- **Deterministic finite quantum process exactly when** — with the paper's
literal conditions `R^(N) ⪰ 0`, `Tr_out R^(k+1) = I ⊗ R^(k)`, `R^(0) = 1`. -/
theorem exists_sequentialIsometricComb_iff_conditions [Nonempty I] (R : CombPrefixFamily O I)
    (N : ℕ) :
    (∃ C : SequentialIsometricComb O I N, ∀ k, k ≤ N → C.realizedChoi k = R k) ↔
      R 0 = 1 ∧ (R N).PosSemidef ∧
        ∀ k, k < N → combOutputTrace (R (k + 1)) = combIdentityExtension (R k) := by
  rw [exists_sequentialIsometricComb_iff, isDeterministicCombThrough_iff_terminal]

/-! ## Assembled statements -/

section Assembled

/-- **Support-minimal sequential realization** (existence and sequential
uniqueness).  For a positive, normalized, causal prefix family there is a
sequential isometric realization with `A_0 = ℂ`, `dim A_k = rank R^(k)`, prefix
support minimal at every cut, whose sequential link followed by final discard
gives every `R^(k)`; every other prefix-support-minimal sequential isometric
realization of the terminal tensor is related to it by unique memory unitaries
(`U_0 = I`) through `V'_k = (I ⊗ U_{k+1}) V_k (I ⊗ U_k)ᴴ`, and the reduced Kraus
operator of every external intervention is transported by the same unitaries. -/
theorem supportMinimal_sequential_realization [Nonempty I] {R : CombPrefixFamily O I} {N : ℕ}
    (hR : IsDeterministicCombThrough R N) :
    ∃ C : SequentialIsometricComb O I N,
      (∀ k, k ≤ N → C.realizedChoi k = R k) ∧
      (∀ k, k ≤ N → Fintype.card (C.Mem k) = (R k).rank) ∧
      (∀ k, k ≤ N → IsPrefixSupportMinimal (C.cumulative k)) ∧
      ∀ C' : SequentialIsometricComb O I N,
        (∀ k, k ≤ N → IsPrefixSupportMinimal (C'.cumulative k)) →
        C'.realizedChoi N = R N →
        ∃ U : ∀ k, Matrix (C'.Mem k) (C.Mem k) ℂ,
          (∀ k, k ≤ N → (U k)ᴴ * U k = 1 ∧ U k * (U k)ᴴ = 1) ∧
          (∀ a b, U 0 a b = 1) ∧
          (∀ k, k ≤ N → C'.cumulative k = C.cumulative k * (U k)ᵀ) ∧
          (∀ k, k < N → C'.link k =
            ((1 : Matrix O O ℂ) ⊗ₖ U (k + 1)) * C.link k * ((1 : Matrix I I ℂ) ⊗ₖ U k)ᴴ) ∧
          (∀ k, k < N → ∀ m : O × I → ℂ,
            reducedKraus (C'.link k) m = U (k + 1) * reducedKraus (C.link k) m * (U k)ᴴ) ∧
          ∀ U' : ∀ k, Matrix (C'.Mem k) (C.Mem k) ℂ,
            (∀ k, k ≤ N → (U' k)ᴴ * U' k = 1) → (∀ a b, U' 0 a b = 1) →
            (∀ k, k < N → C'.link k =
              ((1 : Matrix O O ℂ) ⊗ₖ U' (k + 1)) * C.link k * ((1 : Matrix I I ℂ) ⊗ₖ U' k)ᴴ) →
            ∀ k, k ≤ N → U' k = U k := by
  refine ⟨canonicalComb R N hR, fun k hk => canonicalComb_realizedChoi hR k hk,
    fun k hk => canonicalComb_card hR k hk, fun k hk => canonicalComb_minimal hR k hk, ?_⟩
  intro C' hmin' hT
  obtain ⟨U, hU, hU0, hW, hcov, huniq⟩ := sequentialComb_unitary_covariance
    (canonicalComb R N hR) C' (fun k hk => canonicalComb_minimal hR k hk) hmin'
    ((canonicalComb_realizedChoi hR N le_rfl).trans hT.symm)
  refine ⟨U, hU, hU0, hW, hcov, fun k hk m => ?_, huniq⟩
  rw [hcov k hk, reducedKraus_covariant]

/-- **Finite process-comb tomography** (`thm:supp-comb-tomography`,
`thm:ncg-comb-tomography`, tomography and characterization clauses).  Let
`F k j` be spanning physical slot frames (trace-normalized positive probes with
Hilbert–Schmidt dual bases) and `p k` the `k`-slot multilinear intervention
functionals, with reconstructed tensors `R^(k) = combFrameTensor (F k) (p k)`:

1. `R^(k)` represents every multilinear intervention probability;
2. it is independent of the spanning physical frames;
3. it is the unique tensor representing `p k`, and already the probabilities of
   physical probes determine it;
4. the family is realized at every cut by a finite sequential isometric quantum
   process exactly when it is positive, normalized and causal. -/
theorem finite_process_comb_tomography {N : ℕ}
    (F : ∀ k, Fin k → PhysicalChoiTomographyFrame (O × I))
    (hF : ∀ k j, Submodule.span ℂ (Set.range (F k j).probe) = ⊤)
    (p : ∀ k, MultilinearMap ℂ (fun _ : Fin k => Matrix (O × I) (O × I) ℂ) ℂ) :
    (∀ k, combPairing (combFrameTensor (F k) (p k)) = p k) ∧
    (∀ (G : ∀ k, Fin k → PhysicalChoiTomographyFrame (O × I)),
      (∀ k j, Submodule.span ℂ (Set.range (G k j).probe) = ⊤) →
        ∀ k, combFrameTensor (G k) (p k) = combFrameTensor (F k) (p k)) ∧
    (∀ k (R' : Matrix (CombCarrier O I k) (CombCarrier O I k) ℂ),
      combPairing R' = p k → R' = combFrameTensor (F k) (p k)) ∧
    (∀ k (R' : Matrix (CombCarrier O I k) (CombCarrier O I k) ℂ),
      (∀ M : Fin k → Matrix (O × I) (O × I) ℂ,
        (∀ j, (M j).PosSemidef ∧ ((M j).trace).re ≤ 1) → (R' * combProd M).trace = p k M) →
        R' = combFrameTensor (F k) (p k)) ∧
    ((∃ C : SequentialIsometricComb O I N,
        ∀ k, k ≤ N → C.realizedChoi k = combFrameTensor (F k) (p k)) ↔
      IsDeterministicCombThrough (fun k => combFrameTensor (F k) (p k)) N) := by
  refine ⟨fun k => combPairing_combFrameTensor (F k) (hF k) (p k),
    fun G hG k => combFrameTensor_frame_independent (G k) (F k) (hG k) (hF k) (p k),
    fun k R' hR' => (combPairing_eq_iff R' _).1 hR' |>.trans
      (combFrameTensor_eq_combRepTensor (F k) (hF k) (p k)).symm, ?_,
    exists_sequentialIsometricComb_iff _ N⟩
  intro k R' hR'
  have hp : combPairing R' = p k := by
    apply multilinear_eq_of_physical
    intro M hM
    rw [combPairing_apply]
    exact hR' M hM
  exact ((combPairing_eq_iff R' _).1 hp).trans
    (combFrameTensor_eq_combRepTensor (F k) (hF k) (p k)).symm

end Assembled

/-! ## Non-vacuity -/

/-- The identity process on a qubit: trivial memory and identity links. -/
def qubitIdentityComb (N : ℕ) : SequentialIsometricComb (Fin 2) (Fin 2) N where
  Mem _ := PUnit
  memFintype _ := inferInstanceAs (Fintype PUnit)
  memDecidableEq _ := inferInstanceAs (DecidableEq PUnit)
  memZero := inferInstanceAs (Unique PUnit)
  link _ := (1 : Matrix (Fin 2 × PUnit) (Fin 2 × PUnit) ℂ)
  isometry _ _ := by simp

/-- Non-vacuity: the identity process gives a positive causal family, its
canonical support-minimal realization exists, and the covariance theorem
applies to it. -/
example (N : ℕ) : IsDeterministicCombThrough (qubitIdentityComb N).realizedChoi N :=
  (qubitIdentityComb N).realizedChoi_isDeterministic

example (N : ℕ) :
    let R := (qubitIdentityComb N).realizedChoi
    let hR := (qubitIdentityComb N).realizedChoi_isDeterministic
    ∃ U : ∀ k, Matrix ((canonicalComb R N hR).Mem k) ((canonicalComb R N hR).Mem k) ℂ,
      (∀ k, k ≤ N → (U k)ᴴ * U k = 1 ∧ U k * (U k)ᴴ = 1) ∧ (∀ a b, U 0 a b = 1) := by
  intro R hR
  obtain ⟨U, hU, hU0, -⟩ := sequentialComb_unitary_covariance (canonicalComb R N hR)
    (canonicalComb R N hR) (fun k hk => canonicalComb_minimal hR k hk)
    (fun k hk => canonicalComb_minimal hR k hk) rfl
  exact ⟨U, hU, hU0⟩

end SequentialComb
end RenewalGeometry
