/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.SkewPfaffian

/-!
# One bordered Pfaffian for the range obstruction
  (`prop:supp-finite-range-pfaffian`, `eq:supp-finite-range-border`,
  `eq:supp-finite-range-pfaffian`; emergent-spacetime manuscript)

For an even skew matrix `K ∈ ℝ^{2m×2m}`, `R ∈ ℝ^{3×2m}`, `d ∈ ℝ³`, the border
`𝔹(K, R, d) = [[K, Rᵀ, 0], [-R, 0₃, d], [0, -dᵀ, 0]]` (`border`, a `(2m+4)×(2m+4)` matrix,
built with `Matrix.fromBlocks` and `finSumFinEquiv` in the paper's block order), the polynomial
Pfaffian adjugate `P(K)` (`SkewPfaffian.pfAdj`), `S = R P(K) Rᵀ` and
`n_P = (S₂₃, -S₁₃, S₁₂)ᵀ` (`nP`).

* `Pf_border`: `Pf 𝔹(K, R, d) = n_Pᵀ d` (`eq:supp-finite-range-pfaffian`), for every square `K`
  over any commutative ring (the identity is a formal consequence of the expansion in the final
  index and then in the two remaining added indices, `pfaff_three_border`).

For real skew `K` of rank `2m - 2` (`hrank : K.rank + 2 = 2m`):
* `Pf_eq_zero_of_kernel`, `pfAdj_eq_rank_two_ne`: `Pf K = 0`, `K P(K) = 0`, and for any ordered
  kernel basis `Z = (z₁ z₂)`, `P(K) = c (z₁ z₂ᵀ - z₂ z₁ᵀ)` with `c ≠ 0` (`c ≠ 0` because the
  two-border `[[K, Z], [-Zᵀ, 0]]` is nonsingular, so its Pfaffian `z₁ᵀ P(K) z₂` is nonzero by
  `SkewPfaffian.Pf_ne_zero_iff`);
* `nP_eq_smul_cross`: `n_P = c (R z₁ × R z₂)`;
* `nP_ne_zero_iff`: `n_P ≠ 0 ↔ rank (R|_{ker K}) = 2`;
* `Pf_border_eq_zero_iff`: on that branch, `Pf 𝔹 = 0 ↔ d ∈ R(ker K)`;
* `border_rank_of_mem`: on that branch, at membership `rank 𝔹 = 2m + 2` (lower bound from a
  nonzero principal `(2m+2)`-Pfaffian `S_{ab}`, upper bound from `𝔹 P(𝔹) = 0` with `P(𝔹) ≠ 0`);
* `border_isUnit_det`: on that branch, away from membership `𝔹` is invertible;
* `supp_finite_range_pfaffian`: the five assertions together;
* `border_test_iff_range`: with the incidence `C_* = -D_c⁻¹ R_c Z_g`, `d = D_c q_*`
  (`eq:supp-finite-range-incidence`), `d ∈ R_c(ker K_g) ↔ q_* ∈ Ran C_*`, so on the branch the
  bordered test is the range obstruction; for `2m = 26` the border is `30 × 30`;
* `nonvacuity_branch`: the hypotheses with the branch `n_P ≠ 0` are satisfiable.

The "branch" qualification of the rank and invertibility assertions is the paper's ("on that
branch"); off the branch `n_P = 0` makes `Pf 𝔹 ≡ 0`, so invertibility genuinely needs it.
-/

namespace RenewalGeometry
namespace BorderedPfaffian

open Matrix SkewPfaffian Finset

/-! ### The three-plus-one border expansion on a linearly ordered index type -/

section General

variable {ι : Type*} [LinearOrder ι] {𝕂 : Type*} [CommRing 𝕂]

/-- `xᵀ P_s y` for the border columns `x = A(·, x)`, `y = A(·, y)`. -/
def borderPair (A : ι → ι → 𝕂) (s : Finset ι) (x y : ι) : 𝕂 :=
  ∑ a ∈ s, ∑ b ∈ s, A a x * adjE A s a b * A b y

/-- Expansion of a Pfaffian with three border indices `r₀ < r₁ < r₂` (mutually orthogonal) and a
final index `e` coupled only to them. -/
theorem pfaff_three_border (A : ι → ι → 𝕂) {s : Finset ι} {r0 r1 r2 e : ι}
    (hs : ∀ z ∈ s, z < r0) (h01 : r0 < r1) (h12 : r1 < r2) (h2e : r2 < e)
    (hev : Even s.card) (hse : ∀ z ∈ s, A z e = 0)
    (h01z : A r0 r1 = 0) (h02z : A r0 r2 = 0) (h12z : A r1 r2 = 0) :
    pfaff A (insert e (insert r2 (insert r1 (insert r0 s)))) =
      A r0 e * borderPair A s r1 r2 - A r1 e * borderPair A s r0 r2 +
        A r2 e * borderPair A s r0 r1 := by
  have hs1 : ∀ z ∈ s, z < r1 := fun z hz => (hs z hz).trans h01
  have hs2 : ∀ z ∈ s, z < r2 := fun z hz => (hs1 z hz).trans h12
  have hr0 : r0 ∉ s := fun h => lt_irrefl _ (hs r0 h)
  have hr1 : r1 ∉ insert r0 s := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨h01.ne', fun h => lt_irrefl _ (hs1 r1 h)⟩
  have hr2 : r2 ∉ insert r1 (insert r0 s) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨h12.ne', (h01.trans h12).ne', fun h => lt_irrefl _ (hs2 r2 h)⟩
  have hr1' : r1 ∉ s := fun h => hr1 (Finset.mem_insert_of_mem h)
  have hT : ∀ z ∈ insert r2 (insert r1 (insert r0 s)), z < e := by
    intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | rfl | rfl | hz
    · exact h2e
    · exact h12.trans h2e
    · exact (h01.trans h12).trans h2e
    · exact (hs2 z hz).trans h2e
  rw [pfaff_insert_max A hT, Finset.sum_insert hr2, Finset.sum_insert hr1,
    Finset.sum_insert hr0, Finset.sum_eq_zero (fun z hz => by rw [hse z hz]; ring), add_zero]
  -- positions
  have p2 : pos (insert r2 (insert r1 (insert r0 s))) r2 = s.card + 2 := by
    rw [pos_insert hr2, if_neg (lt_irrefl _), add_zero, pos_of_forall_lt (by
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact h12
      · exact h01.trans h12
      · exact hs2 z hz), Finset.card_insert_of_notMem hr1, Finset.card_insert_of_notMem hr0]
  have p1 : pos (insert r2 (insert r1 (insert r0 s))) r1 = s.card + 1 := by
    rw [pos_insert_of_lt h12, pos_insert hr1, if_neg (lt_irrefl _), add_zero,
      pos_of_forall_lt (by
        intro z hz
        simp only [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact h01
        · exact hs1 z hz), Finset.card_insert_of_notMem hr0]
  have p0 : pos (insert r2 (insert r1 (insert r0 s))) r0 = s.card := by
    rw [pos_insert_of_lt (h01.trans h12), pos_insert_of_lt h01, pos_insert hr0,
      if_neg (lt_irrefl _), add_zero, pos_of_forall_lt hs]
  rw [p2, p1, p0]
  -- minors
  have m2 : (insert r2 (insert r1 (insert r0 s))).erase r2 = insert r1 (insert r0 s) :=
    Finset.erase_insert hr2
  have m1 : (insert r2 (insert r1 (insert r0 s))).erase r1 = insert r2 (insert r0 s) := by
    rw [Finset.erase_insert_of_ne h12.ne', Finset.erase_insert hr1]
  have m0 : (insert r2 (insert r1 (insert r0 s))).erase r0 = insert r2 (insert r1 s) := by
    rw [Finset.erase_insert_of_ne (h01.trans h12).ne', Finset.erase_insert_of_ne h01.ne',
      Finset.erase_insert hr0]
  rw [m2, m1, m0, pfaff_insert_insert A hs h01 h01z,
    pfaff_insert_insert A hs (h01.trans h12) h02z,
    pfaff_insert_insert A hs1 h12 h12z]
  unfold borderPair
  rw [pow_add, pow_add, hev.neg_one_pow]
  ring

end General

/-! ### The paper's border on `Fin (2m + 4)` -/

section Border

variable {𝕂 : Type*} [CommRing 𝕂] {m : ℕ}

/-- The top-right block `(Rᵀ | 0)` of the border. -/
def borderTop (R : Matrix (Fin 3) (Fin (2 * m)) 𝕂) : Matrix (Fin (2 * m)) (Fin 4) 𝕂 :=
  fun i j => if h : (j : ℕ) < 3 then R ⟨j, h⟩ i else 0

/-- The bottom-right block `[[0₃, d], [-dᵀ, 0]]`. -/
def dBlock (d : Fin 3 → 𝕂) : Matrix (Fin 4) (Fin 4) 𝕂 :=
  !![0, 0, 0, d 0; 0, 0, 0, d 1; 0, 0, 0, d 2; -d 0, -d 1, -d 2, 0]

/-- **`eq:supp-finite-range-border`**: `𝔹(K, R, d) = [[K, Rᵀ, 0], [-R, 0₃, d], [0, -dᵀ, 0]]`. -/
def border (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) (R : Matrix (Fin 3) (Fin (2 * m)) 𝕂)
    (d : Fin 3 → 𝕂) : Matrix (Fin (2 * m + 4)) (Fin (2 * m + 4)) 𝕂 :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks K (borderTop R) (-(borderTop R)ᵀ) (dBlock d))

/-- `S = R P(K) Rᵀ`. -/
def S (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) (R : Matrix (Fin 3) (Fin (2 * m)) 𝕂) :
    Matrix (Fin 3) (Fin 3) 𝕂 :=
  R * pfAdj K * Rᵀ

/-- `n_P = (S₂₃, -S₁₃, S₁₂)ᵀ` (one-based indices). -/
def nP (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) (R : Matrix (Fin 3) (Fin (2 * m)) 𝕂) :
    Fin 3 → 𝕂 :=
  ![S K R 1 2, -S K R 0 2, S K R 0 1]

theorem border_castAdd_castAdd (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) R d (i j : Fin (2 * m)) :
    border K R d (Fin.castAdd 4 i) (Fin.castAdd 4 j) = K i j := by
  simp [border]

theorem border_castAdd_natAdd (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) R d (i : Fin (2 * m))
    (k : Fin 4) : border K R d (Fin.castAdd 4 i) (Fin.natAdd (2 * m) k) = borderTop R i k := by
  simp [border]

theorem border_natAdd_castAdd (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) R d (k : Fin 4)
    (j : Fin (2 * m)) : border K R d (Fin.natAdd (2 * m) k) (Fin.castAdd 4 j) = -borderTop R j k := by
  simp [border]

theorem border_natAdd_natAdd (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) R d (k l : Fin 4) :
    border K R d (Fin.natAdd (2 * m) k) (Fin.natAdd (2 * m) l) = dBlock d k l := by
  simp [border]

end Border

section BorderFin

/-- The `K`-indices inside `Fin (2m + 4)`. -/
def kSet (m : ℕ) : Finset (Fin (2 * m + 4)) :=
  (Finset.univ : Finset (Fin (2 * m))).map (Fin.castAddOrderEmb 4).toEmbedding

/-- The added indices `2m, 2m+1, 2m+2, 2m+3` (zero-based). -/
def rIdx (m : ℕ) (k : Fin 4) : Fin (2 * m + 4) := Fin.natAdd (2 * m) k

theorem kSet_lt (m : ℕ) (k : Fin 4) : ∀ z ∈ kSet m, z < rIdx m k := by
  intro z hz
  simp only [kSet, Finset.mem_map, Finset.mem_univ, true_and] at hz
  obtain ⟨i, rfl⟩ := hz
  simp [rIdx, Fin.lt_def, Fin.castAddOrderEmb]
  omega

theorem rIdx_lt {m : ℕ} {k l : Fin 4} (h : k < l) : rIdx m k < rIdx m l := by
  rw [Fin.lt_def] at h ⊢
  simp only [rIdx, Fin.coe_natAdd]
  omega

theorem univ_eq_border_sets (m : ℕ) :
    (Finset.univ : Finset (Fin (2 * m + 4))) =
      insert (rIdx m 3) (insert (rIdx m 2) (insert (rIdx m 1) (insert (rIdx m 0) (kSet m)))) := by
  symm
  rw [Finset.eq_univ_iff_forall]
  intro x
  refine Fin.addCases (fun i => ?_) (fun k => ?_) x
  · simp [kSet, Fin.castAddOrderEmb]
  · simp only [Finset.mem_insert, rIdx]
    fin_cases k <;> simp

theorem card_kSet (m : ℕ) : (kSet m).card = 2 * m := by
  simp [kSet]

variable {𝕂 : Type*} [CommRing 𝕂] {m : ℕ}

theorem border_restrict (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) R (d : Fin 3 → 𝕂) :
    (fun i j => border K R d ((Fin.castAddOrderEmb 4) i) ((Fin.castAddOrderEmb 4) j)) = K := by
  funext i j
  simp [Fin.castAddOrderEmb, border_castAdd_castAdd]

/-- `xᵀ P y` for the border columns `R_k`, `R_l` equals `S_{kl}`. -/
theorem borderPair_border (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) R (d : Fin 3 → 𝕂)
    (k l : Fin 3) :
    borderPair (border K R d) (kSet m) (rIdx m k.castSucc) (rIdx m l.castSucc) = S K R k l := by
  unfold borderPair kSet
  rw [Finset.sum_map]
  simp only [Finset.sum_map]
  have hadj : ∀ a b : Fin (2 * m), adjE (border K R d)
      ((Finset.univ : Finset (Fin (2 * m))).map (Fin.castAddOrderEmb 4).toEmbedding)
      ((Fin.castAddOrderEmb 4).toEmbedding a) ((Fin.castAddOrderEmb 4).toEmbedding b) =
      pfAdj K a b := by
    intro a b
    rw [pfAdj_eq_adjE]
    have := adjE_map (Fin.castAddOrderEmb 4) (border K R d) Finset.univ a b
    rw [border_restrict] at this
    rw [this]
    rfl
  simp only [hadj]
  unfold S
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ (c : Fin (2 * m)) (k : Fin 3),
      border K R d ((Fin.castAddOrderEmb 4).toEmbedding c) (rIdx m k.castSucc) = R k c := by
    intro c k
    simp [rIdx, Fin.castAddOrderEmb, border_castAdd_natAdd, borderTop]
  rw [h1, h1]

/-- **`eq:supp-finite-range-pfaffian`**: `Pf 𝔹(K, R, d) = n_Pᵀ d`. -/
theorem Pf_border (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) (R : Matrix (Fin 3) (Fin (2 * m)) 𝕂)
    (d : Fin 3 → 𝕂) : Pf (border K R d) = nP K R ⬝ᵥ d := by
  have hz : ∀ k l : Fin 4, (k : ℕ) < 3 → (l : ℕ) < 3 →
      border K R d (rIdx m k) (rIdx m l) = 0 := by
    intro k l hk hl
    rw [rIdx, rIdx, border_natAdd_natAdd]
    fin_cases k <;> fin_cases l <;> simp_all [dBlock]
  unfold Pf
  rw [univ_eq_border_sets m, pfaff_three_border (border K R d) (kSet_lt m 0)
    (rIdx_lt (by decide)) (rIdx_lt (by decide)) (rIdx_lt (by decide))
    (by rw [card_kSet]; exact even_two_mul m)
    (fun z hz => by
      simp only [kSet, Finset.mem_map, Finset.mem_univ, true_and] at hz
      obtain ⟨i, rfl⟩ := hz
      simp [rIdx, Fin.castAddOrderEmb, border_castAdd_natAdd, borderTop])
    (hz 0 1 (by decide) (by decide)) (hz 0 2 (by decide) (by decide))
    (hz 1 2 (by decide) (by decide))]
  rw [show (0 : Fin 4) = (0 : Fin 3).castSucc from rfl, show (1 : Fin 4) = (1 : Fin 3).castSucc from rfl,
    show (2 : Fin 4) = (2 : Fin 3).castSucc from rfl]
  rw [borderPair_border, borderPair_border, borderPair_border]
  have he : ∀ k : Fin 3, border K R d (rIdx m k.castSucc) (rIdx m 3) = d k := by
    intro k
    rw [rIdx, rIdx, border_natAdd_natAdd]
    fin_cases k <;> rfl
  rw [he, he, he]
  simp [nP, dotProduct, Fin.sum_univ_three]
  ring

end BorderFin

/-! ### The rank `2m - 2` branch over `ℝ` -/

section RealRank

variable {m : ℕ}

/-- `ker K` as a subspace of `ℝ^{2m}`. -/
abbrev kerK (K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : Submodule ℝ (Fin (2 * m) → ℝ) :=
  LinearMap.ker K.mulVecLin

theorem finrank_kerK {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hrank : K.rank + 2 = 2 * m) :
    Module.finrank ℝ (kerK K) = 2 := by
  show Module.finrank ℝ (LinearMap.ker K.mulVecLin) = 2
  have h := LinearMap.finrank_range_add_finrank_ker K.mulVecLin
  rw [Module.finrank_fin_fun] at h
  rw [Matrix.rank] at hrank
  omega

/-- A kernel basis as the two columns of a matrix `Z` (`ker K = Ran Z`, `Z` injective). -/
theorem exists_kernel_basis {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ}
    (hker : Module.finrank ℝ (kerK K) = 2) :
    ∃ Z : Matrix (Fin (2 * m)) (Fin 2) ℝ,
      LinearMap.range Z.mulVecLin = kerK K ∧ Function.Injective Z.mulVec := by
  let b : Module.Basis (Fin 2) ℝ (kerK K) := Module.finBasisOfFinrankEq ℝ (kerK K) hker
  let Z : Matrix (Fin (2 * m)) (Fin 2) ℝ := Matrix.of fun i a => (b a : Fin (2 * m) → ℝ) i
  have hZ : ∀ x : Fin 2 → ℝ, Z *ᵥ x = ((∑ a, x a • b a : kerK K) : Fin (2 * m) → ℝ) := by
    intro x
    funext i
    simp [Z, Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨Z, ?_, ?_⟩
  · apply le_antisymm
    · rintro v ⟨x, rfl⟩
      rw [Matrix.mulVecLin_apply, hZ]
      exact Submodule.coe_mem _
    · intro v hv
      refine ⟨fun a => b.repr ⟨v, hv⟩ a, ?_⟩
      rw [Matrix.mulVecLin_apply, hZ, b.sum_repr ⟨v, hv⟩]
  · intro x y hxy
    rw [hZ, hZ] at hxy
    have h := Subtype.coe_injective hxy
    have := (Fintype.linearIndependent_iff.1 b.linearIndependent) (x - y) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
    funext a
    exact sub_eq_zero.1 (this a)

/-- A left inverse of an injective `Z`. -/
theorem exists_leftInv {n k : ℕ} {Z : Matrix (Fin n) (Fin k) ℝ}
    (hZ : Function.Injective Z.mulVec) : ∃ W : Matrix (Fin k) (Fin n) ℝ, W * Z = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective Z.mulVecLin
    (LinearMap.ker_eq_bot.2 hZ)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have : LinearMap.toMatrix' g * Z = LinearMap.toMatrix' (g.comp Z.mulVecLin) := by
    rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [this, hg, LinearMap.toMatrix'_id]

theorem alt_of_skew {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} (hK : Kᵀ = -K) :
    (∀ i j, K j i = -K i j) ∧ ∀ i, K i i = 0 :=
  alt_of_transpose_eq_neg hK

/-- A skew matrix with a nontrivial kernel has Pfaffian zero. -/
theorem Pf_eq_zero_of_kernel {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hK : Kᵀ = -K)
    (hker : Module.finrank ℝ (kerK K) = 2) : Pf K = 0 := by
  by_contra h
  obtain ⟨hs, hd⟩ := alt_of_skew hK
  have hu := (Pf_ne_zero_iff K hs hd).1 h
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det K).2 hu)
  have hbot : kerK K = ⊥ := LinearMap.ker_eq_bot.2 hinj
  rw [hbot, finrank_bot] at hker
  exact absurd hker (by norm_num)

/-- Matrices annihilated by `K` factor through the kernel basis: `Z W Q = Q`. -/
theorem mul_eq_of_mul_eq_zero {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ}
    {Z : Matrix (Fin (2 * m)) (Fin 2) ℝ} (hZr : LinearMap.range Z.mulVecLin = kerK K)
    {W : Matrix (Fin 2) (Fin (2 * m)) ℝ} (hW : W * Z = 1)
    {Q : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hQ : K * Q = 0) : Z * W * Q = Q := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply]
  have hmem : Q *ᵥ x ∈ kerK K := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQ, Matrix.zero_mulVec]
  rw [← hZr] at hmem
  obtain ⟨y, hy⟩ := hmem
  rw [Matrix.mulVecLin_apply] at hy
  rw [← Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_mulVec, Matrix.mul_assoc, hW,
    Matrix.mul_one]

/-- **Rank-two form of the Pfaffian adjugate**: on the rank `2m - 2` branch,
`P(K) = c (z₁ z₂ᵀ - z₂ z₁ᵀ)` for the kernel basis `Z = (z₁ z₂)`. -/
theorem pfAdj_eq_rank_two {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hK : Kᵀ = -K)
    (hker : Module.finrank ℝ (kerK K) = 2) {Z : Matrix (Fin (2 * m)) (Fin 2) ℝ}
    (hZr : LinearMap.range Z.mulVecLin = kerK K) (hZi : Function.Injective Z.mulVec) :
    ∃ c : ℝ, ∀ i j, pfAdj K i j = c * (Z i 0 * Z j 1 - Z i 1 * Z j 0) := by
  obtain ⟨hs, hd⟩ := alt_of_skew hK
  obtain ⟨W, hW⟩ := exists_leftInv hZi
  have hPf := Pf_eq_zero_of_kernel hK hker
  set P := pfAdj K with hPdef
  have hKP : K * P = 0 := by rw [hPdef, mul_pfAdj K hs hd, hPf, zero_smul]
  have hPt : Pᵀ = -P := by ext i j; simp [hPdef, pfAdj_skew K i j]
  have hKPt : K * Pᵀ = 0 := by rw [hPt, Matrix.mul_neg, hKP, neg_zero]
  have h1 := mul_eq_of_mul_eq_zero hZr hW hKP
  have h2 := mul_eq_of_mul_eq_zero hZr hW hKPt
  have h2' : P * Wᵀ * Zᵀ = P := by
    have := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [Matrix.mul_assoc]; exact this
  set C := W * P * Wᵀ with hC
  have hPC : P = Z * C * Zᵀ := by
    conv_lhs => rw [← h1, ← h2']
    rw [hC]; simp only [Matrix.mul_assoc]
  have hCt : Cᵀ = -C := by
    rw [hC, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hPt]
    simp [Matrix.mul_assoc]
  have c00 : C 0 0 = 0 := by
    have := congrFun (congrFun hCt 0) 0
    simp at this; linarith
  have c11 : C 1 1 = 0 := by
    have := congrFun (congrFun hCt 1) 1
    simp at this; linarith
  have c10 : C 1 0 = -C 0 1 := by
    have := congrFun (congrFun hCt 0) 1
    simpa using this
  refine ⟨C 0 1, fun i j => ?_⟩
  rw [hPC]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, c00, c11, c10]
  ring

end RealRank

/-! ### The two-border matrix of a kernel basis (nonvanishing of `P(K)`) -/

section TwoBorder

variable {𝕂 : Type*} [CommRing 𝕂] {m : ℕ}

/-- `[[K, Z], [-Zᵀ, 0₂]]`. -/
def border2 (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) (Z : Matrix (Fin (2 * m)) (Fin 2) 𝕂) :
    Matrix (Fin (2 * m + 2)) (Fin (2 * m + 2)) 𝕂 :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks K Z (-Zᵀ) 0)

@[simp] theorem border2_cc (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) Z (i j : Fin (2 * m)) :
    border2 K Z (Fin.castAdd 2 i) (Fin.castAdd 2 j) = K i j := by simp [border2]
@[simp] theorem border2_cn (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) Z (i : Fin (2 * m))
    (k : Fin 2) : border2 K Z (Fin.castAdd 2 i) (Fin.natAdd (2 * m) k) = Z i k := by
  simp [border2]
@[simp] theorem border2_nc (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) Z (k : Fin 2)
    (j : Fin (2 * m)) : border2 K Z (Fin.natAdd (2 * m) k) (Fin.castAdd 2 j) = -Z j k := by
  simp [border2]
@[simp] theorem border2_nn (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) Z (k l : Fin 2) :
    border2 K Z (Fin.natAdd (2 * m) k) (Fin.natAdd (2 * m) l) = 0 := by
  simp [border2]

/-- The `K`-indices inside `Fin (2m + 2)`. -/
def kSet2 (m : ℕ) : Finset (Fin (2 * m + 2)) :=
  (Finset.univ : Finset (Fin (2 * m))).map (Fin.castAddOrderEmb 2).toEmbedding

theorem univ_eq_border2_sets (m : ℕ) :
    (Finset.univ : Finset (Fin (2 * m + 2))) =
      insert (Fin.natAdd (2 * m) (1 : Fin 2)) (insert (Fin.natAdd (2 * m) (0 : Fin 2)) (kSet2 m)) := by
  symm
  rw [Finset.eq_univ_iff_forall]
  intro x
  refine Fin.addCases (fun i => ?_) (fun k => ?_) x
  · simp [kSet2, Fin.castAddOrderEmb]
  · simp only [Finset.mem_insert]
    fin_cases k <;> simp

/-- `Pf [[K, Z], [-Zᵀ, 0]] = z₁ᵀ P(K) z₂`. -/
theorem Pf_border2 (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂) (Z : Matrix (Fin (2 * m)) (Fin 2) 𝕂) :
    Pf (border2 K Z) = ∑ a, ∑ b, Z a 0 * pfAdj K a b * Z b 1 := by
  unfold Pf
  rw [univ_eq_border2_sets m, pfaff_insert_insert (border2 K Z)
    (fun z hz => by
      simp only [kSet2, Finset.mem_map, Finset.mem_univ, true_and] at hz
      obtain ⟨i, rfl⟩ := hz
      rw [Fin.lt_def]; simp [Fin.castAddOrderEmb])
    (by rw [Fin.lt_def]; simp) (border2_nn K Z 0 1)]
  unfold kSet2
  rw [Finset.sum_map]
  simp only [Finset.sum_map]
  have hres : (fun i j => border2 K Z ((Fin.castAddOrderEmb 2) i) ((Fin.castAddOrderEmb 2) j))
      = K := by
    funext i j; simp [Fin.castAddOrderEmb]
  have hadj : ∀ a b : Fin (2 * m), adjE (border2 K Z)
      ((Finset.univ : Finset (Fin (2 * m))).map (Fin.castAddOrderEmb 2).toEmbedding)
      ((Fin.castAddOrderEmb 2).toEmbedding a) ((Fin.castAddOrderEmb 2).toEmbedding b) =
      pfAdj K a b := by
    intro a b
    rw [pfAdj_eq_adjE]
    have := adjE_map (Fin.castAddOrderEmb 2) (border2 K Z) Finset.univ a b
    rw [hres] at this
    rw [this]
    rfl
  simp only [hadj]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [Fin.castAddOrderEmb]

theorem border2_alt {K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂} (hs : ∀ i j, K j i = -K i j)
    (hd : ∀ i, K i i = 0) (Z : Matrix (Fin (2 * m)) (Fin 2) 𝕂) :
    (∀ i j, border2 K Z j i = -border2 K Z i j) ∧ ∀ i, border2 K Z i i = 0 := by
  constructor
  · intro i j
    refine Fin.addCases (fun i' => ?_) (fun k => ?_) i <;>
      refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
    · rw [border2_cc, border2_cc]; exact hs i' j'
    · rw [border2_nc, border2_cn]
    · rw [border2_cn, border2_nc, neg_neg]
    · rw [border2_nn, border2_nn, neg_zero]
  · intro i
    refine Fin.addCases (fun i' => ?_) (fun k => ?_) i
    · rw [border2_cc]; exact hd i'
    · rw [border2_nn]

end TwoBorder

section TwoBorderReal

variable {m : ℕ}

/-- `[[K, Z], [-Zᵀ, 0]]` is nonsingular when the columns of `Z` form a basis of `ker K`
(`K` skew: `Ran K ⊥ ker K`). -/
theorem border2_injective {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hK : Kᵀ = -K)
    {Z : Matrix (Fin (2 * m)) (Fin 2) ℝ} (hZr : LinearMap.range Z.mulVecLin = kerK K)
    (hZi : Function.Injective Z.mulVec) : Function.Injective (border2 K Z).mulVec := by
  have hlin : Function.Injective (border2 K Z).mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [Matrix.mulVecLin_apply] at hv
    set w : Fin (2 * m) → ℝ := fun j => v (Fin.castAdd 2 j) with hw
    set α : Fin 2 → ℝ := fun k => v (Fin.natAdd (2 * m) k) with hα
    have e1 : K *ᵥ w + Z *ᵥ α = 0 := by
      funext i
      have := congrFun hv (Fin.castAdd 2 i)
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, border2_cc, border2_cn,
        Pi.zero_apply] at this
      simpa [Matrix.mulVec, dotProduct, hw, hα] using this
    have e2 : Zᵀ *ᵥ w = 0 := by
      funext k
      have := congrFun hv (Fin.natAdd (2 * m) k)
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, border2_nc, border2_nn,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, neg_mul,
        Finset.sum_neg_distrib, neg_eq_zero] at this
      simpa [Matrix.mulVec, dotProduct, hw, mul_comm] using this
    set u := Z *ᵥ α with hu
    have huker : K *ᵥ u = 0 := by
      have : u ∈ kerK K := by rw [← hZr]; exact ⟨α, rfl⟩
      simpa using this
    have hdot : u ⬝ᵥ (K *ᵥ w) = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hK, Matrix.neg_mulVec, huker,
        neg_zero, zero_dotProduct]
    have huu : u ⬝ᵥ u = 0 := by
      have : K *ᵥ w = -u := eq_neg_of_add_eq_zero_left e1
      rw [this, dotProduct_neg] at hdot
      linarith
    have hu0 : u = 0 := dotProduct_self_eq_zero.1 huu
    have hα0 : α = 0 := hZi (by rw [← hu, hu0, Matrix.mulVec_zero])
    have hw0 : w = 0 := by
      have hKw : K *ᵥ w = 0 := by rw [← hu0]; simpa [hu0] using e1
      have hmem : w ∈ kerK K := by simpa using hKw
      rw [← hZr] at hmem
      obtain ⟨β, hβ⟩ := hmem
      rw [Matrix.mulVecLin_apply] at hβ
      have : w ⬝ᵥ w = 0 := by
        calc w ⬝ᵥ w = (Z *ᵥ β) ⬝ᵥ w := by rw [hβ]
          _ = 0 := by
            rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, e2,
              zero_dotProduct]
      exact dotProduct_self_eq_zero.1 this
    funext x
    refine Fin.addCases (fun i => ?_) (fun k => ?_) x
    · have := congrFun hw0 i; simpa [hw] using this
    · have := congrFun hα0 k; simpa [hα] using this
  exact hlin

/-- **`P(K) ≠ 0` on the rank `2m-2` branch**: `P(K) = c (z₁ z₂ᵀ - z₂ z₁ᵀ)` with `c ≠ 0`. -/
theorem pfAdj_eq_rank_two_ne {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hK : Kᵀ = -K)
    (hker : Module.finrank ℝ (kerK K) = 2) {Z : Matrix (Fin (2 * m)) (Fin 2) ℝ}
    (hZr : LinearMap.range Z.mulVecLin = kerK K) (hZi : Function.Injective Z.mulVec) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ i j, pfAdj K i j = c * (Z i 0 * Z j 1 - Z i 1 * Z j 0) := by
  obtain ⟨c, hc⟩ := pfAdj_eq_rank_two hK hker hZr hZi
  refine ⟨c, fun h0 => ?_, hc⟩
  obtain ⟨hs, hd⟩ := alt_of_skew hK
  obtain ⟨hs2, hd2⟩ := border2_alt hs hd Z
  have hu : IsUnit (border2 K Z).det :=
    (Matrix.isUnit_iff_isUnit_det _).1
      (Matrix.mulVec_injective_iff_isUnit.1 (border2_injective hK hZr hZi))
  have hne := (Pf_ne_zero_iff (border2 K Z) hs2 hd2).2 hu
  apply hne
  rw [Pf_border2]
  simp [hc, h0]

end TwoBorderReal

/-! ### The proposition -/

section PropMain

theorem S_apply {𝕂 : Type*} [CommRing 𝕂] {m : ℕ} (K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂)
    (R : Matrix (Fin 3) (Fin (2 * m)) 𝕂) (k l : Fin 3) :
    S K R k l = ∑ a, ∑ b, R k a * pfAdj K a b * R l b := by
  unfold S
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem border_alt {𝕂 : Type*} [CommRing 𝕂] {m : ℕ} {K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂}
    (hs : ∀ i j, K j i = -K i j) (hd : ∀ i, K i i = 0) (R : Matrix (Fin 3) (Fin (2 * m)) 𝕂)
    (d : Fin 3 → 𝕂) :
    (∀ i j, border K R d j i = -border K R d i j) ∧ ∀ i, border K R d i i = 0 := by
  constructor
  · intro i j
    refine Fin.addCases (fun i' => ?_) (fun k => ?_) i <;>
      refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
    · rw [border_castAdd_castAdd, border_castAdd_castAdd]; exact hs i' j'
    · rw [border_natAdd_castAdd, border_castAdd_natAdd]
    · rw [border_castAdd_natAdd, border_natAdd_castAdd, neg_neg]
    · rw [border_natAdd_natAdd, border_natAdd_natAdd]
      fin_cases k <;> fin_cases l <;> simp [dBlock]
  · intro i
    refine Fin.addCases (fun i' => ?_) (fun k => ?_) i
    · rw [border_castAdd_castAdd]; exact hd i'
    · rw [border_natAdd_natAdd]; fin_cases k <;> simp [dBlock]

variable {m : ℕ}

/-- The two image vectors `u = R z₁`, `v = R z₂` of a kernel basis. -/
def imgVec (R : Matrix (Fin 3) (Fin (2 * m)) ℝ) (Z : Matrix (Fin (2 * m)) (Fin 2) ℝ) (a : Fin 2) :
    Fin 3 → ℝ :=
  R *ᵥ (fun i => Z i a)

/-- On the rank `2m-2` branch, `n_P = c (R z₁ × R z₂)` with `c ≠ 0`. -/
theorem nP_eq_smul_cross {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hK : Kᵀ = -K)
    (hker : Module.finrank ℝ (kerK K) = 2) {Z : Matrix (Fin (2 * m)) (Fin 2) ℝ}
    (hZr : LinearMap.range Z.mulVecLin = kerK K) (hZi : Function.Injective Z.mulVec)
    (R : Matrix (Fin 3) (Fin (2 * m)) ℝ) :
    ∃ c : ℝ, c ≠ 0 ∧ nP K R = c • (imgVec R Z 0 ⨯₃ imgVec R Z 1) := by
  obtain ⟨c, hc0, hc⟩ := pfAdj_eq_rank_two_ne hK hker hZr hZi
  refine ⟨c, hc0, ?_⟩
  have hS : ∀ k l, S K R k l =
      c * (imgVec R Z 0 k * imgVec R Z 1 l - imgVec R Z 1 k * imgVec R Z 0 l) := by
    intro k l
    rw [S_apply]
    simp only [imgVec, Matrix.mulVec, dotProduct, Finset.sum_mul_sum, hc]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  funext k
  fin_cases k
  · show S K R 1 2 = c * (imgVec R Z 0 1 * imgVec R Z 1 2 - imgVec R Z 0 2 * imgVec R Z 1 1)
    rw [hS]; ring
  · show -S K R 0 2 = c * (imgVec R Z 0 2 * imgVec R Z 1 0 - imgVec R Z 0 0 * imgVec R Z 1 2)
    rw [hS]; ring
  · show S K R 0 1 = c * (imgVec R Z 0 0 * imgVec R Z 1 1 - imgVec R Z 0 1 * imgVec R Z 1 0)
    rw [hS]; ring

/-- `R(ker K) = span {R z₁, R z₂}`. -/
theorem map_kerK_eq_span {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ}
    {Z : Matrix (Fin (2 * m)) (Fin 2) ℝ} (hZr : LinearMap.range Z.mulVecLin = kerK K)
    (R : Matrix (Fin 3) (Fin (2 * m)) ℝ) :
    (kerK K).map R.mulVecLin = Submodule.span ℝ (Set.range ![imgVec R Z 0, imgVec R Z 1]) := by
  rw [← hZr, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul, Matrix.range_mulVecLin]
  congr 2
  funext a k
  fin_cases a <;> simp [imgVec, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem range_pair (u v : Fin 3 → ℝ) : Set.range ![u, v] = {u, v} := by
  ext x
  simp [eq_comm, or_comm]

/-- **`n_P ≠ 0` exactly when `rank(R|_{ker K}) = 2`.** -/
theorem nP_ne_zero_iff {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hK : Kᵀ = -K)
    (hrank : K.rank + 2 = 2 * m) (R : Matrix (Fin 3) (Fin (2 * m)) ℝ) :
    nP K R ≠ 0 ↔ Module.finrank ℝ ((kerK K).map R.mulVecLin) = 2 := by
  have hker := finrank_kerK hrank
  obtain ⟨Z, hZr, hZi⟩ := exists_kernel_basis hker
  obtain ⟨c, hc0, hc⟩ := nP_eq_smul_cross hK hker hZr hZi R
  rw [hc, map_kerK_eq_span hZr, smul_ne_zero_iff, and_iff_right hc0,
    crossProduct_ne_zero_iff_linearIndependent, linearIndependent_iff_card_eq_finrank_span,
    Fintype.card_fin, Set.finrank]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- In `ℝ³`, for `u × v ≠ 0`: `d ∈ span {u, v} ↔ (u × v) · d = 0`. -/
theorem mem_span_pair_iff_cross_dot {u v d : Fin 3 → ℝ} (hn : u ⨯₃ v ≠ 0) :
    d ∈ Submodule.span ℝ {u, v} ↔ (u ⨯₃ v) ⬝ᵥ d = 0 := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_comm, dot_self_cross,
      dotProduct_comm, dot_cross_self]
    simp
  · intro hnd
    set n := u ⨯₃ v with hndef
    have hnn : n ⬝ᵥ n ≠ 0 := by
      intro h; exact hn (dotProduct_self_eq_zero.1 h)
    refine ⟨((n ⨯₃ d) ⬝ᵥ v) / (n ⬝ᵥ n), -((n ⨯₃ d) ⬝ᵥ u) / (n ⬝ᵥ n), ?_⟩
    funext i
    have key : (n ⬝ᵥ n) * d i = ((n ⨯₃ d) ⬝ᵥ v) * u i - ((n ⨯₃ d) ⬝ᵥ u) * v i := by
      rw [hndef] at hnd ⊢
      simp only [cross_apply, dotProduct, Fin.sum_univ_three] at hnd ⊢
      fin_cases i
      · simp at hnd ⊢; linear_combination (u 1 * v 2 - u 2 * v 1) * hnd
      · simp at hnd ⊢; linear_combination (u 2 * v 0 - u 0 * v 2) * hnd
      · simp at hnd ⊢; linear_combination (u 0 * v 1 - u 1 * v 0) * hnd
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination -key

end PropMain

/-! ### Membership, invertibility and rank of the border -/

section BorderRank

variable {m : ℕ}

/-- **On the branch `n_P ≠ 0`: `Pf 𝔹 = 0 ↔ d ∈ R(ker K)`.** -/
theorem Pf_border_eq_zero_iff {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hK : Kᵀ = -K)
    (hrank : K.rank + 2 = 2 * m) (R : Matrix (Fin 3) (Fin (2 * m)) ℝ) (d : Fin 3 → ℝ)
    (hbr : nP K R ≠ 0) :
    Pf (border K R d) = 0 ↔ d ∈ (kerK K).map R.mulVecLin := by
  have hker := finrank_kerK hrank
  obtain ⟨Z, hZr, hZi⟩ := exists_kernel_basis hker
  obtain ⟨c, hc0, hc⟩ := nP_eq_smul_cross hK hker hZr hZi R
  have hcross : imgVec R Z 0 ⨯₃ imgVec R Z 1 ≠ 0 := by
    intro h; apply hbr; rw [hc, h, smul_zero]
  rw [Pf_border, hc, smul_dotProduct, smul_eq_mul, mul_eq_zero, or_iff_right hc0,
    map_kerK_eq_span hZr, range_pair, mem_span_pair_iff_cross_dot hcross]

/-- **Away from membership the border is invertible** (on the branch `n_P ≠ 0`). -/
theorem border_isUnit_det {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hK : Kᵀ = -K)
    (hrank : K.rank + 2 = 2 * m) (R : Matrix (Fin 3) (Fin (2 * m)) ℝ) (d : Fin 3 → ℝ)
    (hbr : nP K R ≠ 0) (hd : d ∉ (kerK K).map R.mulVecLin) : IsUnit (border K R d).det := by
  obtain ⟨hs, hdg⟩ := alt_of_skew hK
  obtain ⟨hs', hd'⟩ := border_alt hs hdg R d
  exact (Pf_ne_zero_iff _ hs' hd').1
    (fun h => hd ((Pf_border_eq_zero_iff hK hrank R d hbr).1 h))

/-- A nonzero Pfaffian of a principal submatrix bounds the rank from below. -/
theorem card_le_rank_of_pfaff_ne_zero {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hs : ∀ i j, A j i = -A i j) (hd : ∀ i, A i i = 0) (T : Finset (Fin N))
    (h : pfaff A T ≠ 0) : T.card ≤ A.rank := by
  classical
  let M : Matrix T T ℝ := A.submatrix Subtype.val Subtype.val
  let Adj : Matrix T T ℝ := fun j l => adjE A T j l
  have hMA : M * ((pfaff A T)⁻¹ • Adj) = 1 := by
    ext a l
    rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply]
    have hsum : ∑ j : T, M a j * Adj j l = ∑ j ∈ T, A a j * adjE A T j l :=
      Finset.sum_coe_sort T (fun j => A a j * adjE A T j l)
    rw [hsum, sum_mul_adjE A hs hd T a.2 l.2]
    by_cases hal : a = l
    · subst hal; simp [h]
    · rw [if_neg (fun h' => hal (Subtype.ext h')), if_neg hal, smul_zero]
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_right_inverse hMA
  have hrM : M.rank = Fintype.card T :=
    Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).2 hdet)
  rw [Fintype.card_coe] at hrM
  rw [← hrM]
  exact Matrix.rank_submatrix_le A Subtype.val Subtype.val

/-- A matrix killed on the right by a skew matrix with a nonzero entry has corank `≥ 2`. -/
theorem rank_add_two_le {N : ℕ} {B Q : Matrix (Fin N) (Fin N) ℝ} (hBQ : B * Q = 0)
    {i j : Fin N} (hQ : Q i j ≠ 0) (hQs : Q j i = -Q i j) (hQi : Q i i = 0) (hQj : Q j j = 0) :
    B.rank + 2 ≤ N := by
  have hsub : (Q.submatrix ![i, j] ![i, j]).rank = 2 := by
    have hdet : IsUnit (Q.submatrix ![i, j] ![i, j]).det := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, hQi, hQj, hQs]
      simpa using hQ
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 hdet), Fintype.card_fin]
  have hQr : 2 ≤ Q.rank := hsub ▸ Matrix.rank_submatrix_le Q ![i, j] ![i, j]
  have hle : LinearMap.range Q.mulVecLin ≤ LinearMap.ker B.mulVecLin := by
    rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hBQ, Matrix.zero_mulVec]
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [Module.finrank_fin_fun] at h2
  rw [Matrix.rank] at hQr ⊢
  omega

theorem exists_S_ne_zero {𝕂 : Type*} [CommRing 𝕂] {K : Matrix (Fin (2 * m)) (Fin (2 * m)) 𝕂}
    {R : Matrix (Fin 3) (Fin (2 * m)) 𝕂} (hbr : nP K R ≠ 0) :
    ∃ a b c : Fin 3, a < b ∧ c ≠ a ∧ c ≠ b ∧ S K R a b ≠ 0 := by
  by_contra h
  push_neg at h
  apply hbr
  funext k
  fin_cases k
  · exact h 1 2 0 (by decide) (by decide) (by decide)
  · show -S K R 0 2 = 0
    rw [h 0 2 1 (by decide) (by decide) (by decide), neg_zero]
  · exact h 0 1 2 (by decide) (by decide) (by decide)

theorem erase_erase_eq_insert (a b c : Fin 3) (hab : a < b) (hca : c ≠ a) (hcb : c ≠ b) :
    ((Finset.univ : Finset (Fin (2 * m + 4))).erase (rIdx m 3)).erase (rIdx m c.castSucc) =
      insert (rIdx m b.castSucc) (insert (rIdx m a.castSucc) (kSet m)) := by
  have key : ∀ k : Fin 4, (k ≠ c.castSucc ∧ k ≠ 3) ↔ (k = b.castSucc ∨ k = a.castSucc) := by
    revert a b c
    decide
  ext x
  refine Fin.addCases (fun i => ?_) (fun k => ?_) x
  · have hne : ∀ k : Fin 4, Fin.castAdd 4 i ≠ Fin.natAdd (2 * m) k := by
      intro k h
      have := congrArg Fin.val h
      simp at this
      omega
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_univ, and_true, rIdx]
    simp [hne, kSet, Fin.castAddOrderEmb]
  · have hnot : Fin.natAdd (2 * m) k ∉ kSet m := by
      simp only [kSet, Finset.mem_map, Finset.mem_univ, true_and, not_exists]
      intro i h
      have := congrArg Fin.val h
      simp [Fin.castAddOrderEmb] at this
      omega
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_univ, and_true, rIdx, hnot,
      or_false]
    have := key k
    have ninj : ∀ k l : Fin 4, Fin.natAdd (2 * m) k = Fin.natAdd (2 * m) l → k = l := by
      intro k l h
      ext
      have := congrArg Fin.val h
      simpa using this
    constructor
    · rintro ⟨h1, h2⟩
      rcases this.1 ⟨fun h => h1 (by rw [h]), fun h => h2 (by rw [h])⟩ with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    · rintro (h | h)
      · have hk : k = b.castSucc := ninj _ _ h
        have := this.2 (Or.inl hk)
        exact ⟨fun h' => this.1 (ninj _ _ h'),
          fun h' => this.2 (ninj _ _ h')⟩
      · have hk : k = a.castSucc := ninj _ _ h
        have := this.2 (Or.inr hk)
        exact ⟨fun h' => this.1 (ninj _ _ h'),
          fun h' => this.2 (ninj _ _ h')⟩

/-- **At membership the border has rank `2m + 2`** (on the branch `n_P ≠ 0`). -/
theorem border_rank_of_mem {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hK : Kᵀ = -K)
    (hrank : K.rank + 2 = 2 * m) (R : Matrix (Fin 3) (Fin (2 * m)) ℝ) (d : Fin 3 → ℝ)
    (hbr : nP K R ≠ 0) (hd : d ∈ (kerK K).map R.mulVecLin) :
    (border K R d).rank = 2 * m + 2 := by
  obtain ⟨hs, hdg⟩ := alt_of_skew hK
  obtain ⟨hs', hd'⟩ := border_alt hs hdg R d
  have hPf := (Pf_border_eq_zero_iff hK hrank R d hbr).2 hd
  obtain ⟨a, b, c, hab, hca, hcb, hS⟩ := exists_S_ne_zero hbr
  have hz : border K R d (rIdx m a.castSucc) (rIdx m b.castSucc) = 0 := by
    rw [rIdx, rIdx, border_natAdd_natAdd]
    fin_cases a <;> fin_cases b <;> simp [dBlock]
  have hT : pfaff (border K R d)
      (insert (rIdx m b.castSucc) (insert (rIdx m a.castSucc) (kSet m))) = S K R a b := by
    rw [pfaff_insert_insert _ (kSet_lt m _) (rIdx_lt (Fin.castSucc_lt_castSucc_iff.2 hab)) hz]
    exact borderPair_border K R d a b
  have hTcard : (insert (rIdx m b.castSucc) (insert (rIdx m a.castSucc) (kSet m))).card =
      2 * m + 2 := by
    have ha : rIdx m a.castSucc ∉ kSet m := fun h => lt_irrefl _ (kSet_lt m _ _ h)
    have hb : rIdx m b.castSucc ∉ insert (rIdx m a.castSucc) (kSet m) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨(rIdx_lt (Fin.castSucc_lt_castSucc_iff.2 hab)).ne',
        fun h => lt_irrefl _ (kSet_lt m _ _ h)⟩
    rw [Finset.card_insert_of_notMem hb, Finset.card_insert_of_notMem ha, card_kSet]
  -- lower bound
  have hlow := card_le_rank_of_pfaff_ne_zero hs' hd' _ (by rw [hT]; exact hS)
  rw [hTcard] at hlow
  -- upper bound through the adjugate
  have hBQ : border K R d * pfAdj (border K R d) = 0 := by
    rw [mul_pfAdj _ hs' hd', hPf, zero_smul]
  have hce : rIdx m c.castSucc ≠ rIdx m 3 := by
    intro h
    have := congrArg Fin.val h
    simp [rIdx] at this
    have := c.2
    omega
  have hQ : pfAdj (border K R d) (rIdx m c.castSucc) (rIdx m 3) ≠ 0 := by
    rw [pfAdj_eq_adjE]
    unfold adjE
    rw [if_neg hce, erase_erase_eq_insert a b c hab hca hcb, hT]
    exact mul_ne_zero (sgnE_ne_zero _ _ _) hS
  have hdiag : ∀ x, pfAdj (border K R d) x x = 0 := fun x => by simp [pfAdj]
  have hup := rank_add_two_le hBQ hQ (pfAdj_skew _ _ _) (hdiag _) (hdiag _)
  omega

end BorderRank

/-! ### The statement -/

section Statement

variable {m : ℕ}

/-- **`prop:supp-finite-range-pfaffian`.** Let `K ∈ ℝ^{2m×2m}` be skew of rank `2m - 2`,
`R ∈ ℝ^{3×2m}`, `d ∈ ℝ³`, `S = R P(K) Rᵀ`, `n_P = (S₂₃, -S₁₃, S₁₂)ᵀ`. Then
1. `Pf 𝔹(K, R, d) = n_Pᵀ d`;
2. `n_P ≠ 0` exactly when `rank (R|_{ker K}) = 2`;
3. on that branch, `Pf 𝔹 = 0` exactly when `d ∈ R(ker K)`;
4. on that branch, at membership the border has rank `2m + 2`;
5. on that branch, away from membership the border is invertible. -/
theorem supp_finite_range_pfaffian {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hK : Kᵀ = -K)
    (hrank : K.rank + 2 = 2 * m) (R : Matrix (Fin 3) (Fin (2 * m)) ℝ) (d : Fin 3 → ℝ) :
    Pf (border K R d) = nP K R ⬝ᵥ d ∧
    (nP K R ≠ 0 ↔ Module.finrank ℝ ((kerK K).map R.mulVecLin) = 2) ∧
    (nP K R ≠ 0 → (Pf (border K R d) = 0 ↔ d ∈ (kerK K).map R.mulVecLin)) ∧
    (nP K R ≠ 0 → d ∈ (kerK K).map R.mulVecLin → (border K R d).rank = 2 * m + 2) ∧
    (nP K R ≠ 0 → d ∉ (kerK K).map R.mulVecLin → IsUnit (border K R d).det) :=
  ⟨Pf_border K R d, nP_ne_zero_iff hK hrank R,
    fun hbr => Pf_border_eq_zero_iff hK hrank R d hbr,
    fun hbr hd => border_rank_of_mem hK hrank R d hbr hd,
    fun hbr hd => border_isUnit_det hK hrank R d hbr hd⟩

/-- A kernel basis `Z` (`K Z = 0`, `Z` injective) spans `ker K` on the rank `2m - 2` branch. -/
theorem range_eq_kerK {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hrank : K.rank + 2 = 2 * m)
    {Z : Matrix (Fin (2 * m)) (Fin 2) ℝ} (hKZ : K * Z = 0) (hZi : Function.Injective Z.mulVec) :
    LinearMap.range Z.mulVecLin = kerK K := by
  have hle : LinearMap.range Z.mulVecLin ≤ kerK K := by
    rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hKZ, Matrix.zero_mulVec]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_kerK hrank, LinearMap.finrank_range_of_inj hZi, Module.finrank_fin_fun]

/-- **The incidence reduction (last sentence of `prop:supp-finite-range-pfaffian`).** With the
exact incidence `C_* = -D_c⁻¹ R_c Z_g`, `d = D_c q_*` (`eq:supp-finite-range-incidence`),
`D_c` invertible and `Z_g` a kernel basis of `K_g`, membership `d ∈ R_c(ker K_g)` is exactly
`q_* ∈ Ran C_*`; hence on the branch `n_P ≠ 0` the bordered Pfaffian test `Pf 𝔹(K_g, R_c, d) = 0`
is the range obstruction `q_* ∈ Ran C_*`. -/
theorem border_test_iff_range {K : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ} (hK : Kᵀ = -K)
    (hrank : K.rank + 2 = 2 * m) {Z : Matrix (Fin (2 * m)) (Fin 2) ℝ} (hKZ : K * Z = 0)
    (hZi : Function.Injective Z.mulVec) {D : Matrix (Fin 3) (Fin 3) ℝ} (hD : IsUnit D.det)
    (Rc : Matrix (Fin 3) (Fin (2 * m)) ℝ) (q : Fin 3 → ℝ) :
    (D *ᵥ q ∈ (kerK K).map Rc.mulVecLin ↔
      q ∈ LinearMap.range (-(D⁻¹ * Rc * Z)).mulVecLin) ∧
    (nP K Rc ≠ 0 → (Pf (border K Rc (D *ᵥ q)) = 0 ↔
      q ∈ LinearMap.range (-(D⁻¹ * Rc * Z)).mulVecLin)) := by
  have hmem : D *ᵥ q ∈ (kerK K).map Rc.mulVecLin ↔
      q ∈ LinearMap.range (-(D⁻¹ * Rc * Z)).mulVecLin := by
    rw [← range_eq_kerK hrank hKZ hZi, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨-x, ?_⟩
      rw [Matrix.mulVecLin_apply] at hx ⊢
      calc (-(D⁻¹ * Rc * Z)) *ᵥ (-x) = (D⁻¹ * (Rc * Z)) *ᵥ x := by
            rw [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg, Matrix.mul_assoc]
        _ = D⁻¹ *ᵥ ((Rc * Z) *ᵥ x) := by rw [Matrix.mulVec_mulVec]
        _ = D⁻¹ *ᵥ (D *ᵥ q) := by rw [hx]
        _ = q := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hD, Matrix.one_mulVec]
    · rintro ⟨x, hx⟩
      refine ⟨-x, ?_⟩
      rw [Matrix.mulVecLin_apply] at hx ⊢
      have hDD : D * (D⁻¹ * Rc * Z) = Rc * Z := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD, Matrix.one_mul]
      calc (Rc * Z) *ᵥ (-x) = D *ᵥ ((-(D⁻¹ * Rc * Z)) *ᵥ x) := by
            rw [Matrix.mulVec_mulVec, Matrix.mul_neg, hDD, Matrix.neg_mulVec, Matrix.mulVec_neg]
        _ = D *ᵥ q := by rw [hx]
  exact ⟨hmem, fun hbr => (Pf_border_eq_zero_iff hK hrank Rc (D *ᵥ q) hbr).trans hmem⟩

/-- For `K = K_g` (`2m = 26`) the border is a `30 × 30` matrix. -/
example (K : Matrix (Fin (2 * 13)) (Fin (2 * 13)) ℝ) (R : Matrix (Fin 3) (Fin (2 * 13)) ℝ)
    (d : Fin 3 → ℝ) : Matrix (Fin 30) (Fin 30) ℝ := border K R d

end Statement

/-! ### Non-vacuity -/

section NonVacuity

/-- The hypotheses of `supp_finite_range_pfaffian` together with the branch `n_P ≠ 0` are
satisfiable: `m = 1`, `K = 0` (rank `0 = 2m - 2`), `R = [[1,0],[0,1],[0,0]]`. -/
theorem nonvacuity_branch :
    ∃ (K : Matrix (Fin (2 * 1)) (Fin (2 * 1)) ℝ) (R : Matrix (Fin 3) (Fin (2 * 1)) ℝ),
      Kᵀ = -K ∧ K.rank + 2 = 2 * 1 ∧ nP K R ≠ 0 := by
  refine ⟨0, !![1, 0; 0, 1; 0, 0], by simp, by simp, ?_⟩
  intro h
  have h2 := congrFun h 2
  have hP : pfAdj (0 : Matrix (Fin (2 * 1)) (Fin (2 * 1)) ℝ) 0 1 = -1 := by
    have he : ((Finset.univ : Finset (Fin (2 * 1))).erase 0).erase 1 = ∅ := by decide
    have h0 : pfaff (0 : Matrix (Fin (2 * 1)) (Fin (2 * 1)) ℝ) ∅ = 1 := pfaff_empty _
    simp only [pfAdj, he]
    simp [h0]
  simp [nP, S_apply, Fin.sum_univ_two, hP] at h2

end NonVacuity

end BorderedPfaffian
end RenewalGeometry
