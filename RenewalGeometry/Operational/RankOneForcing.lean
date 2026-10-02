/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.MatrixKrausExistence
/-!
# Rank-one forcing from a deterministic transition panel

Paper label: `lem:ncg-rank-one-forcing` (predictive spectral geometry).

API (`Matrix h h ℂ`, `open scoped ComplexOrder`; namespace `RenewalGeometry.RankOneForcing`):

* `IsDensity ρ` (`ρ ⪰ 0`, `Tr ρ = 1`) and `IsEffect E` (`0 ⪯ E ⪯ 1`);
* `trace_mul_eq_zero_iff`: for `A, B ⪰ 0`, `Tr(AB) = 0 ↔ AB = 0`;
* `mul_eq_zero_of_perfectDiscrimination`: perfectly distinguished densities
  (`Tr(E_i ρ_j) = δ_ij`) have orthogonal supports, `ρ_i ρ_j = 0` for `i ≠ j`;
* `sum_rank_le_card_of_mul_eq_zero`: Hermitian matrices with pairwise vanishing products have
  `∑ rank ≤ dim`; `sum_rank_le_card` is `eq:perfect-discrimination-rank`;
* `rank_eq_one_of_card_eq`, `exists_orthonormal_of_card_eq`: at `N = dim H` every `ρ_j` is a
  rank-one projector `|e_j⟩⟨e_j|` on an orthonormal basis;
* `panel_invariant_kraus`: for a Kraus map with a deterministic injective panel on such
  projectors, `𝒱 = span{ρ_j}` is invariant under the map and under its Hilbert–Schmidt adjoint;
* `rankOneForcing`: **the lemma** in the paper's form (perfect discrimination, `dim H = N`,
  `Φ` completely positive on `M_d(ℂ)`, `Ψ` its Hilbert–Schmidt adjoint).
-/

namespace RenewalGeometry
namespace RankOneForcing

open Matrix MatrixKraus
open scoped ComplexOrder

variable {h : Type*} [Fintype h] [DecidableEq h]

/-- A density matrix: positive semidefinite with unit trace. -/
def IsDensity (ρ : Matrix h h ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- An effect: `0 ⪯ E ⪯ 1`. -/
def IsEffect (E : Matrix h h ℂ) : Prop := E.PosSemidef ∧ (1 - E).PosSemidef

/-- For positive semidefinite `A, B`, `Tr(AB) = 0` iff `AB = 0`. -/
theorem trace_mul_eq_zero_iff {A B : Matrix h h ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A * B).trace = 0 ↔ A * B = 0 := by
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, trace_zero]⟩
  obtain ⟨X, rfl⟩ := exists_eq_conjTranspose_mul_self hA
  obtain ⟨Y, rfl⟩ := exists_eq_conjTranspose_mul_self hB
  have h1 : ((Y * Xᴴ)ᴴ * (Y * Xᴴ)).trace = 0 := by
    rw [← h0, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show X * Yᴴ * (Y * Xᴴ) = (X * (Yᴴ * Y)) * Xᴴ by simp only [Matrix.mul_assoc],
      trace_mul_comm, ← Matrix.mul_assoc]
  have h2 := trace_conjTranspose_mul_self_eq_zero_iff.1 h1
  have h3 : X * Yᴴ = 0 := by
    have := congrArg conjTranspose h2
    simpa [conjTranspose_mul] using this
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc X, h3, Matrix.zero_mul, Matrix.mul_zero]

/-- **Orthogonal supports** (`lem:ncg-rank-one-forcing`, first step of the proof): perfectly
distinguished densities satisfy `ρ_i ρ_j = 0` for `i ≠ j`. -/
theorem mul_eq_zero_of_perfectDiscrimination {ι : Type*} [DecidableEq ι]
    {ρ E : ι → Matrix h h ℂ} (hρ : ∀ j, IsDensity (ρ j)) (hE : ∀ i, IsEffect (E i))
    (hd : ∀ i j, (E i * ρ j).trace = if i = j then 1 else 0) {i j : ι} (hij : i ≠ j) :
    ρ i * ρ j = 0 := by
  have h1 : E i * ρ j = 0 :=
    (trace_mul_eq_zero_iff (hE i).1 (hρ j).1).1 (by rw [hd, if_neg hij])
  have h2 : (1 - E i) * ρ i = 0 := by
    refine (trace_mul_eq_zero_iff (hE i).2 (hρ i).1).1 ?_
    rw [Matrix.sub_mul, Matrix.one_mul, trace_sub, hd, if_pos rfl, (hρ i).2, sub_self]
  have h3 : ρ i = ρ i * E i := by
    have h4 : ρ i = E i * ρ i := by
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h2; exact h2
    have hh := congrArg conjTranspose h4
    rw [conjTranspose_mul, (hρ i).1.isHermitian.eq, (hE i).1.isHermitian.eq] at hh
    exact hh
  rw [h3, Matrix.mul_assoc, h1, Matrix.mul_zero]

/-- Ranges of Hermitian matrices with pairwise vanishing products are independent: the
dimension of their sum over a finite set is the sum of the ranks. -/
theorem finrank_iSup_range_eq_sum {ι : Type*} [DecidableEq ι] {ρ : ι → Matrix h h ℂ}
    (hH : ∀ j, (ρ j).IsHermitian) (horth : ∀ i j, i ≠ j → ρ i * ρ j = 0) (s : Finset ι) :
    Module.finrank ℂ (⨆ j ∈ s, LinearMap.range (ρ j).mulVecLin : Submodule ℂ (h → ℂ))
      = ∑ j ∈ s, (ρ j).rank := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hle : (⨆ j ∈ s, LinearMap.range (ρ j).mulVecLin) ≤ LinearMap.ker (ρ a).mulVecLin := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v, rfl⟩
      have hja : a ≠ j := fun h' => ha (h' ▸ hj)
      simp [LinearMap.mem_ker, mulVec_mulVec, horth a j hja]
    have hbot : LinearMap.range (ρ a).mulVecLin ⊓ (⨆ j ∈ s, LinearMap.range (ρ j).mulVecLin)
        = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨v, rfl⟩, hx⟩
      have h1 := hle hx
      simp only [LinearMap.mem_ker, mulVecLin_apply, mulVec_mulVec] at h1
      have h2 : ((ρ a)ᴴ * ρ a) *ᵥ v = 0 := by rw [(hH a).eq]; exact h1
      simpa using (conjTranspose_mul_self_mulVec_eq_zero _ _).1 h2
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    have := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (ρ a).mulVecLin)
      (⨆ j ∈ s, LinearMap.range (ρ j).mulVecLin)
    rw [hbot, finrank_bot, add_zero] at this
    rw [this]
    rfl

/-- Hermitian matrices with pairwise vanishing products have `∑ rank ≤ dim`. -/
theorem sum_rank_le_card_of_mul_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : ι → Matrix h h ℂ} (hH : ∀ j, (ρ j).IsHermitian)
    (horth : ∀ i j, i ≠ j → ρ i * ρ j = 0) :
    ∑ j, (ρ j).rank ≤ Fintype.card h := by
  rw [← finrank_iSup_range_eq_sum hH horth Finset.univ, ← Module.finrank_fintype_fun_eq_card ℂ]
  exact Submodule.finrank_le _

/-- **`eq:perfect-discrimination-rank`**: perfectly distinguished densities on a finite Hilbert
space satisfy `∑_j rank ρ_j ≤ dim H`. -/
theorem sum_rank_le_card {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ E : ι → Matrix h h ℂ}
    (hρ : ∀ j, IsDensity (ρ j)) (hE : ∀ i, IsEffect (E i))
    (hd : ∀ i j, (E i * ρ j).trace = if i = j then 1 else 0) :
    ∑ j, (ρ j).rank ≤ Fintype.card h :=
  sum_rank_le_card_of_mul_eq_zero (fun j => (hρ j).1.isHermitian)
    fun _ _ hij => mul_eq_zero_of_perfectDiscrimination hρ hE hd hij

/-- A matrix killing every vector is zero. -/
theorem eq_zero_of_forall_mulVec_eq_zero {M : Matrix h h ℂ} (hM : ∀ v, M *ᵥ v = 0) : M = 0 := by
  ext i j
  have := congrFun (hM (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

/-- A density matrix has positive rank. -/
theorem rank_pos_of_isDensity {ρ : Matrix h h ℂ} (hρ : IsDensity ρ) : 0 < ρ.rank := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  have hbot : LinearMap.range ρ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h0
  have hz : ρ = 0 := eq_zero_of_forall_mulVec_eq_zero fun v => by
    have : ρ.mulVecLin v ∈ LinearMap.range ρ.mulVecLin := LinearMap.mem_range_self _ v
    rw [hbot, Submodule.mem_bot] at this
    simpa using this
  have := hρ.2
  rw [hz, trace_zero] at this
  exact zero_ne_one this

/-- **Rank-one forcing at `dim H = N`**: every perfectly distinguished density has rank one. -/
theorem rank_eq_one_of_card_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ E : ι → Matrix h h ℂ}
    (hρ : ∀ j, IsDensity (ρ j)) (hE : ∀ i, IsEffect (E i))
    (hd : ∀ i j, (E i * ρ j).trace = if i = j then 1 else 0)
    (hcard : Fintype.card ι = Fintype.card h) (j : ι) : (ρ j).rank = 1 := by
  by_contra hne
  have h1 : ∀ i ∈ (Finset.univ : Finset ι), 1 ≤ (ρ i).rank := fun i _ => rank_pos_of_isDensity (hρ i)
  have h2 : ∃ i ∈ (Finset.univ : Finset ι), 1 < (ρ i).rank :=
    ⟨j, Finset.mem_univ _, lt_of_le_of_ne (rank_pos_of_isDensity (hρ j)) (Ne.symm hne)⟩
  have h3 := Finset.sum_lt_sum h1 h2
  have h4 := sum_rank_le_card hρ hE hd
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h3
  omega

/-- A rank-one density is a projector `|v⟩⟨v|` onto a unit vector. -/
theorem exists_unit_vector_of_rank_one {ρ : Matrix h h ℂ} (hρ : IsDensity ρ) (hrk : ρ.rank = 1) :
    ∃ v : h → ℂ, ρ = vecMulVec v (star v) ∧ star v ⬝ᵥ v = 1 := by
  have hA := hρ.1.isHermitian
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_eq_one_iff] at hrk
  obtain ⟨⟨k, hk⟩, huniq⟩ := hrk
  have hzero : ∀ i, i ≠ k → hA.eigenvalues i = 0 := fun i hi => by
    by_contra hne
    exact hi (congrArg Subtype.val (huniq ⟨i, hne⟩))
  have hlk : (hA.eigenvalues k : ℂ) = 1 := by
    rw [← hρ.2, hA.trace_eq_sum_eigenvalues,
      Finset.sum_eq_single k (fun i _ hi => by rw [hzero i hi]; simp) (by simp)]
    exact rfl
  have hdiag : diagonal ((RCLike.ofReal ∘ hA.eigenvalues) : h → ℂ) = single k k 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hik : i = k
      · subst hik; simp [hlk]
      · simp [hzero i hik, Ne.symm hik]
    · simp [hij, single_apply]; intro h1 h2; exact absurd (h1.symm.trans h2) hij
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, hdiag] at hspec
  set U : Matrix h h ℂ := (hA.eigenvectorUnitary : Matrix h h ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  refine ⟨fun a => U a k, ?_, ?_⟩
  · rw [hspec]
    ext a b
    simp only [Matrix.mul_apply, single_apply, vecMulVec_apply, star_apply, Pi.star_apply]
    rw [Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro c _ hc; simp [Ne.symm hc]
      · simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  · have := congrFun (congrFun hUU k) k
    simpa [Matrix.mul_apply, dotProduct, star_apply] using this

/-- `|u⟩⟨v| w = ⟨v, w⟩ u` (bilinear form). -/
theorem vecMulVec_mulVec' (u v w : h → ℂ) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]

/-- `M |x⟩⟨x| Mᴴ = |Mx⟩⟨Mx|`. -/
theorem mul_vecMulVec_mul_conjTranspose {k : Type*} [Fintype k] (M : Matrix k h ℂ) (x : h → ℂ) :
    M * vecMulVec x (star x) * Mᴴ = vecMulVec (M *ᵥ x) (star (M *ᵥ x)) := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

/-- **Orthonormal rank-one form at `dim H = N`** (`lem:ncg-rank-one-forcing`, "in
particular"): the `ρ_j` are the projectors `|e_j⟩⟨e_j|` onto an orthonormal family
(so their supports are mutually orthogonal lines). -/
theorem exists_orthonormal_of_card_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ E : ι → Matrix h h ℂ} (hρ : ∀ j, IsDensity (ρ j)) (hE : ∀ i, IsEffect (E i))
    (hd : ∀ i j, (E i * ρ j).trace = if i = j then 1 else 0)
    (hcard : Fintype.card ι = Fintype.card h) :
    ∃ e : ι → h → ℂ, (∀ j, ρ j = vecMulVec (e j) (star (e j))) ∧
      ∀ i j, star (e i) ⬝ᵥ e j = if i = j then 1 else 0 := by
  choose e he hn using fun j =>
    exists_unit_vector_of_rank_one (hρ j) (rank_eq_one_of_card_eq hρ hE hd hcard j)
  refine ⟨e, he, fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, hn]
  · rw [if_neg hij]
    have h0 := mul_eq_zero_of_perfectDiscrimination hρ hE hd hij
    have h1 := congrArg (fun M => star (e i) ⬝ᵥ (M *ᵥ e j)) h0
    simp only [zero_mulVec, dotProduct_zero] at h1
    rw [← mulVec_mulVec, he j, vecMulVec_mulVec', hn, one_smul, he i, vecMulVec_mulVec',
      dotProduct_smul, hn, smul_eq_mul, mul_one] at h1
    exact h1

section Panel

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Expansion in an orthonormal basis: if `e` is an orthonormal family of `card h` vectors,
every matrix whose off-diagonal `e`-coefficients vanish is `∑_j ⟨e_j, M e_j⟩ |e_j⟩⟨e_j|`. -/
theorem eq_sum_of_offDiag_eq_zero {e : ι → h → ℂ}
    (he : ∀ i j, star (e i) ⬝ᵥ e j = if i = j then 1 else 0)
    (hcard : Fintype.card ι = Fintype.card h) {M : Matrix h h ℂ}
    (hM : ∀ j k, j ≠ k → star (e j) ⬝ᵥ (M *ᵥ e k) = 0) :
    M = ∑ j, (star (e j) ⬝ᵥ (M *ᵥ e j)) • vecMulVec (e j) (star (e j)) := by
  set B : Matrix h ι ℂ := Matrix.of fun a j => e j a with hB
  have hBB : Bᴴ * B = 1 := by
    ext i j
    rw [Matrix.mul_apply, one_apply, ← he i j]
    simp [hB, dotProduct, conjTranspose_apply]
  have hBB' : B * Bᴴ = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).1 hBB
  have hD : ∀ j k, (Bᴴ * M * B) j k = star (e j) ⬝ᵥ (M *ᵥ e k) := by
    intro j k
    simp only [hB, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, dotProduct, mulVec,
      Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hdiag : Bᴴ * M * B = diagonal fun j => star (e j) ⬝ᵥ (M *ᵥ e j) := by
    ext j k
    rw [hD, diagonal_apply]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk, hM j k hjk]
  calc M = (B * Bᴴ) * M * (B * Bᴴ) := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
    _ = B * (Bᴴ * M * B) * Bᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hdiag]
      ext a b
      simp only [Matrix.mul_apply, diagonal_apply, conjTranspose_apply, hB, Matrix.of_apply,
        Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single c]
      · simp; ring
      · intro d _ hd; simp [hd]
      · simp

/-- **Panel invariance for Kraus maps** (`lem:ncg-rank-one-forcing`, invariance part): let
`e` be an orthonormal basis (`card ι = card h`), `ρ_j = |e_j⟩⟨e_j|`, and let the Kraus map
`Φ = ∑ W_ν (·) W_νᴴ` satisfy `Φ(ρ_j) = w_j ρ_{σ(j)}` on `J` and `Tr Φ(ρ_j) = 0` off `J`, with
`σ` injective on `J`.  Then `𝒱 = span{ρ_j}` is invariant under `Φ` and under its
Hilbert–Schmidt adjoint `Φ^* = ∑ W_νᴴ (·) W_ν`. -/
theorem panel_invariant_kraus {e : ι → h → ℂ}
    (he : ∀ i j, star (e i) ⬝ᵥ e j = if i = j then 1 else 0)
    (hcard : Fintype.card ι = Fintype.card h) (W : κ → Matrix h h ℂ) (J : Set ι) (σ : ι → ι)
    (hσ : Set.InjOn σ J) (w : ι → ℝ)
    (hpanel : ∀ j ∈ J, krausMap W (vecMulVec (e j) (star (e j)))
      = (w j : ℂ) • vecMulVec (e (σ j)) (star (e (σ j))))
    (hnull : ∀ j ∉ J, (krausMap W (vecMulVec (e j) (star (e j)))).trace = 0) :
    (∀ X ∈ Submodule.span ℂ (Set.range fun j => vecMulVec (e j) (star (e j))),
        krausMap W X ∈ Submodule.span ℂ (Set.range fun j => vecMulVec (e j) (star (e j)))) ∧
    (∀ X ∈ Submodule.span ℂ (Set.range fun j => vecMulVec (e j) (star (e j))),
        krausMap (fun a => (W a)ᴴ) X ∈
          Submodule.span ℂ (Set.range fun j => vecMulVec (e j) (star (e j)))) := by
  set V := Submodule.span ℂ (Set.range fun j => vecMulVec (e j) (star (e j))) with hV
  have hmem : ∀ j, vecMulVec (e j) (star (e j)) ∈ V := fun j =>
    Submodule.subset_span ⟨j, rfl⟩
  -- Kraus form on the projectors
  have hK : ∀ (Wf : κ → Matrix h h ℂ) (x : h → ℂ), krausMap Wf (vecMulVec x (star x))
      = ∑ ν, vecMulVec (Wf ν *ᵥ x) (star (Wf ν *ᵥ x)) := fun Wf x => by
    rw [krausMap_apply]
    exact Finset.sum_congr rfl fun ν _ => mul_vecMulVec_mul_conjTranspose _ _
  -- the coefficients `a ν i j = ⟨e_i, W_ν e_j⟩`
  have hquad : ∀ i j, star (e i) ⬝ᵥ (krausMap W (vecMulVec (e j) (star (e j))) *ᵥ e i)
      = ∑ ν, star (star (e i) ⬝ᵥ (W ν *ᵥ e j)) * (star (e i) ⬝ᵥ (W ν *ᵥ e j)) := by
    intro i j
    rw [hK, sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [vecMulVec_mulVec', dotProduct_smul, smul_eq_mul, star_dotProduct]
  have hsumzero : ∀ (c : κ → ℂ), ∑ ν, star (c ν) * c ν = 0 → ∀ ν, c ν = 0 := by
    intro c hc ν
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun ν _ => star_mul_self_nonneg (c ν)).1 hc ν
      (Finset.mem_univ _)
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact star_eq_zero.1 h2
    · exact h2
  -- kernel vanishing off the domain
  have hWnull : ∀ j ∉ J, ∀ ν, W ν *ᵥ e j = 0 := by
    intro j hj
    have h1 := hnull j hj
    rw [hK, trace_sum] at h1
    simp only [trace_vecMulVec] at h1
    intro ν
    exact dotProduct_self_star_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun ν _ => dotProduct_self_star_nonneg _).1 h1 ν
        (Finset.mem_univ _))
  have hvan : ∀ ν i j, star (e i) ⬝ᵥ (W ν *ᵥ e j) ≠ 0 → j ∈ J ∧ σ j = i := by
    intro ν i j hne
    by_cases hj : j ∈ J
    · refine ⟨hj, ?_⟩
      by_contra hσi
      apply hne
      refine hsumzero (fun ν => star (e i) ⬝ᵥ (W ν *ᵥ e j)) ?_ ν
      rw [← hquad, hpanel j hj, smul_mulVec, vecMulVec_mulVec', he (σ j) i, if_neg hσi,
        zero_smul, smul_zero, dotProduct_zero]
    · exact absurd (by rw [hWnull j hj ν, dotProduct_zero]) hne
  constructor
  · -- forward invariance
    have hle : V ≤ V.comap (krausMap W) := by
      rw [hV, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      change krausMap W (vecMulVec (e j) (star (e j))) ∈ V
      by_cases hj : j ∈ J
      · rw [hpanel j hj]; exact V.smul_mem _ (hmem _)
      · rw [hK]
        simp only [hWnull j hj, star_zero]
        simp
    exact fun X hX => hle hX
  · -- adjoint invariance
    have hle : V ≤ V.comap (krausMap fun a => (W a)ᴴ) := by
      rw [hV, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change krausMap (fun a => (W a)ᴴ) (vecMulVec (e i) (star (e i))) ∈ V
      set M := krausMap (fun a => (W a)ᴴ) (vecMulVec (e i) (star (e i))) with hMdef
      have hoff : ∀ j k, j ≠ k → star (e j) ⬝ᵥ (M *ᵥ e k) = 0 := by
        intro j k hjk
        rw [hMdef, hK, sum_mulVec, dotProduct_sum]
        refine Finset.sum_eq_zero fun ν _ => ?_
        rw [vecMulVec_mulVec', dotProduct_smul, smul_eq_mul]
        -- `⟨Wᴴ e_i, e_k⟩ = ⟨e_i, W e_k⟩` and `⟨e_j, Wᴴ e_i⟩ = conj ⟨e_i, W e_j⟩`
        have hk : star ((W ν)ᴴ *ᵥ e i) ⬝ᵥ e k = star (e i) ⬝ᵥ (W ν *ᵥ e k) := by
          rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]
        have hj : star (e j) ⬝ᵥ ((W ν)ᴴ *ᵥ e i) = star (star (e i) ⬝ᵥ (W ν *ᵥ e j)) := by
          rw [star_dotProduct, star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]
        rw [hk, hj]
        by_cases hj0 : star (e i) ⬝ᵥ (W ν *ᵥ e j) = 0
        · rw [hj0, star_zero, mul_zero]
        by_cases hk0 : star (e i) ⬝ᵥ (W ν *ᵥ e k) = 0
        · rw [hk0, zero_mul]
        exfalso
        obtain ⟨hjJ, hσj⟩ := hvan ν i j hj0
        obtain ⟨hkJ, hσk⟩ := hvan ν i k hk0
        exact hjk (hσ hjJ hkJ (hσj.trans hσk.symm))
      rw [eq_sum_of_offDiag_eq_zero he hcard hoff]
      exact V.sum_mem fun j _ => V.smul_mem _ (hmem j)
    exact fun X hX => hle hX

end Panel

/-- **Lemma `lem:ncg-rank-one-forcing`.**  Let `ρ_1, …, ρ_N` be density matrices on
`H = ℂ^d` perfectly distinguished by effects `E_i` (`Tr(E_i ρ_j) = δ_ij`).  Then
`∑_j rank ρ_j ≤ d`.  If `d = N`, every `ρ_j` is a rank-one projector `|e_j⟩⟨e_j|` on an
orthonormal basis.  If moreover `Φ` is completely positive with `Φ(ρ_j) = w_j ρ_{σ(j)}`
(`w_j > 0`) on a domain `J`, `Tr Φ(ρ_j) = 0` off `J`, and `σ` is injective on `J`, then the
diagonal span `𝒱 = span{ρ_j}` is invariant under `Φ` and under every Hilbert–Schmidt
adjoint `Ψ` of `Φ` (`⟪Y, Φ X⟫ = ⟪Ψ Y, X⟫`). -/
theorem rankOneForcing {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ E : ι → Matrix (Fin d) (Fin d) ℂ} (hρ : ∀ j, IsDensity (ρ j)) (hE : ∀ i, IsEffect (E i))
    (hd : ∀ i j, (E i * ρ j).trace = if i = j then 1 else 0) :
    ∑ j, (ρ j).rank ≤ d ∧
    (Fintype.card ι = d →
      (∃ e : ι → Fin d → ℂ, (∀ j, ρ j = vecMulVec (e j) (star (e j))) ∧
        ∀ i j, star (e i) ⬝ᵥ e j = if i = j then 1 else 0) ∧
      ∀ (Φ Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ),
        IsMatrixCompletelyPositive Φ → (∀ X Y, hsInner Y (Φ X) = hsInner (Ψ Y) X) →
        ∀ (J : Set ι) (σ : ι → ι) (w : ι → ℝ), Set.InjOn σ J → (∀ j ∈ J, 0 < w j) →
        (∀ j ∈ J, Φ (ρ j) = (w j : ℂ) • ρ (σ j)) → (∀ j ∉ J, (Φ (ρ j)).trace = 0) →
        (∀ X ∈ Submodule.span ℂ (Set.range ρ), Φ X ∈ Submodule.span ℂ (Set.range ρ)) ∧
        (∀ X ∈ Submodule.span ℂ (Set.range ρ), Ψ X ∈ Submodule.span ℂ (Set.range ρ))) := by
  refine ⟨by simpa using sum_rank_le_card hρ hE hd, fun hcard => ?_⟩
  have hcard' : Fintype.card ι = Fintype.card (Fin d) := by simpa using hcard
  obtain ⟨e, he, hon⟩ := exists_orthonormal_of_card_eq hρ hE hd hcard'
  refine ⟨⟨e, he, hon⟩, fun Φ Ψ hΦ hΨ J σ w hσ _ hpanel hnull => ?_⟩
  obtain ⟨W, hW⟩ := exists_kraus_of_completelyPositive hΦ
  have hΦW : Φ = krausMap W := LinearMap.ext fun X => (hW X).trans (krausMap_apply W X).symm
  subst hΦW
  have hΨW := eq_krausMap_conjTranspose_of_hsAdjoint W Ψ hΨ
  subst hΨW
  have hρe : ρ = fun j => vecMulVec (e j) (star (e j)) := funext he
  subst hρe
  exact panel_invariant_kraus hon hcard' W J σ hσ w
    (fun j hj => hpanel j hj) (fun j hj => hnull j hj)

/-- Non-vacuity witness for `rankOneForcing`: on `H = ℂ¹` the state `ρ = 1`, the effect
`E = 1`, the identity channel (Kraus operator `1`) with its Hilbert–Schmidt adjoint, and the
panel `J = univ`, `σ = id`, `w = 1` satisfy every hypothesis. -/
example :
    let ρ : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
    let Φ := krausMap (fun _ : Unit => (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (∀ j, IsDensity (ρ j)) ∧ (∀ i, IsEffect (ρ i)) ∧
    (∀ i j, (ρ i * ρ j).trace = if i = j then 1 else 0) ∧ Fintype.card (Fin 1) = 1 ∧
    IsMatrixCompletelyPositive Φ ∧ (∀ X Y, hsInner Y (Φ X) = hsInner (Φ Y) X) ∧
    Set.InjOn (id : Fin 1 → Fin 1) Set.univ ∧
    (∀ j ∈ (Set.univ : Set (Fin 1)), Φ (ρ j) = ((1 : ℝ) : ℂ) • ρ (id j)) := by
  intro ρ Φ
  refine ⟨fun _ => ⟨PosSemidef.one, by simp [ρ]⟩, fun _ => ⟨PosSemidef.one, by simp [ρ, PosSemidef.zero]⟩,
    fun i j => by simp [ρ, Subsingleton.elim i j], rfl, krausMap_completelyPositive _,
    fun X Y => by rw [hsInner_krausMap]; simp [Φ], Set.injOn_id _, fun j _ => by
      simp [Φ, ρ, krausMap_apply]⟩

end RankOneForcing
end RenewalGeometry
