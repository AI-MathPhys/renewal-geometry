/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.ExactSourceSchurResidual

/-!
# Terminating source-minimal fermion saturation (`thm:fermion-source-saturation`)

`thm:fermion-source-saturation` of the spacetime–gauge duality manuscript.  On the finite
represented carrier `ℋ_F^amb = ℂ^h` let `c₁, …, c_m` be the loaded letters, `𝒜_F` the
`*`-algebra they generate (`loadedAlgebra`; in finite dimension this is the generated
`C^*`-algebra) and `B_F` a synthesis of the retained source.  The cyclic filtration
(`eq:fermion-cyclic-filtration`)

`𝒦₀ = Ran B_F,   𝒦_{r+1} = 𝒦_r + ∑_j (c_j 𝒦_r + c_j^* 𝒦_r)`

is `cyclicFiltration`.

* `cyclicFiltration_stabilizes`: there is a first index `r₀ ≤ h` with `𝒦_{r₀+1} = 𝒦_{r₀}`;
  every earlier step is a strict increase, and `𝒦_s = 𝒦_{r₀}` for all `s ≥ r₀`;
* `stable_eq_minimalCarrier`: at any equality `𝒦_{r+1} = 𝒦_r`,
  `𝒦_r = 𝒦_F^min = 𝒜_F Ran B_F` (`eq:fermion-minimal-carrier`);
* `stable_reduces`: at that equality every `a ∈ 𝒜_F` maps `𝒦_r` into itself and commutes with
  the orthogonal projector onto `𝒦_r` (the stabilized space reduces `𝒜_F`);
* `cyclic_innovation_rank`: with `Ran S_r = 𝒦_r` and `Ran N_r = ∑_j (c_j 𝒦_r + c_j^* 𝒦_r)`,
  `𝕃_r = D_r − C_r^* G_r^† C_r = N_r^*(I − P_r)N_r ⪰ 0` and
  `rank 𝕃_r = dim 𝒦_{r+1} − dim 𝒦_r` (`eq:fermion-cyclic-innovation`,
  `eq:fermion-cyclic-rank`); `range_columnBank` shows that the explicit column bank
  `(c_j S_r, c_j^* S_r)_j` has exactly this range;
* `compressed_word_gram`, `complement_invisible`: compression to `𝒦_F^min` preserves every
  loaded source-word Gram `B_F^* w(c) B_F`, and every vector orthogonal to `𝒦_F^min` is
  invisible to every source correlation `(w(c) B_F)^* x`;
* `fermion_source_saturation`: the assembled statement.

Renderings disclosed: the carrier is `Fin h → ℂ`; letters are indexed by `Fin m × Bool`
(`false ↦ c_j`, `true ↦ c_j^*`); words are lists of letters; the orthogonal projector onto a
subspace is any Hermitian idempotent with that range (one exists: `exists_projector`); `N_r`
is any `Fin`-indexed synthesis of the next columns (the explicit bank is reindexed by an
equivalence, which does not change its range).
-/

open Matrix
open scoped ComplexOrder

namespace RenewalGeometry
namespace FermionSourceSaturation

set_option linter.unusedSectionVars false

variable {h m : ℕ}

/-- The loaded letters: `(j, false) ↦ c_j`, `(j, true) ↦ c_j^*`. -/
def letter (c : Fin m → Matrix (Fin h) (Fin h) ℂ) : Fin m × Bool → Matrix (Fin h) (Fin h) ℂ
  | (j, false) => c j
  | (j, true) => (c j)ᴴ

/-- The new columns `∑_j (c_j 𝒦 + c_j^* 𝒦)` produced from a subspace `𝒦`. -/
def nextColumns (c : Fin m → Matrix (Fin h) (Fin h) ℂ) (K : Submodule ℂ (Fin h → ℂ)) :
    Submodule ℂ (Fin h → ℂ) :=
  ⨆ l : Fin m × Bool, K.map (letter c l).mulVecLin

/-- One step `𝒦 ↦ 𝒦 + ∑_j (c_j 𝒦 + c_j^* 𝒦)` of the cyclic filtration. -/
def step (c : Fin m → Matrix (Fin h) (Fin h) ℂ) (K : Submodule ℂ (Fin h → ℂ)) :
    Submodule ℂ (Fin h → ℂ) :=
  K ⊔ nextColumns c K

/-- The cyclic filtration `eq:fermion-cyclic-filtration`. -/
def cyclicFiltration {E : Type*} [Fintype E] (c : Fin m → Matrix (Fin h) (Fin h) ℂ)
    (B : Matrix (Fin h) E ℂ) : ℕ → Submodule ℂ (Fin h → ℂ)
  | 0 => LinearMap.range B.mulVecLin
  | r + 1 => step c (cyclicFiltration c B r)

/-- The loaded algebra `𝒜_F = C^*(c₁, …, c_m)` (the generated `*`-subalgebra). -/
def loadedAlgebra (c : Fin m → Matrix (Fin h) (Fin h) ℂ) :
    StarSubalgebra ℂ (Matrix (Fin h) (Fin h) ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range c)

/-- The minimal carrier `𝒦_F^min = 𝒜_F Ran B_F`. -/
def minimalCarrier {E : Type*} [Fintype E] (c : Fin m → Matrix (Fin h) (Fin h) ℂ)
    (B : Matrix (Fin h) E ℂ) : Submodule ℂ (Fin h → ℂ) :=
  Submodule.span ℂ {v | ∃ a ∈ loadedAlgebra c, ∃ w ∈ LinearMap.range B.mulVecLin, v = a *ᵥ w}

variable {E : Type*} [Fintype E] (c : Fin m → Matrix (Fin h) (Fin h) ℂ)
  (B : Matrix (Fin h) E ℂ)

theorem le_step (K : Submodule ℂ (Fin h → ℂ)) : K ≤ step c K := le_sup_left

theorem cyclicFiltration_succ (r : ℕ) :
    cyclicFiltration c B (r + 1) = step c (cyclicFiltration c B r) := rfl

/-- The filtration is nested. -/
theorem cyclicFiltration_monotone : Monotone (cyclicFiltration c B) :=
  monotone_nat_of_le_succ fun r => le_step c _

theorem letter_mem_loadedAlgebra (l : Fin m × Bool) : letter c l ∈ loadedAlgebra c := by
  obtain ⟨j, b⟩ := l
  cases b
  · exact StarAlgebra.subset_adjoin ℂ _ ⟨j, rfl⟩
  · show (c j)ᴴ ∈ loadedAlgebra c
    rw [← Matrix.star_eq_conjTranspose]
    exact star_mem (StarAlgebra.subset_adjoin ℂ _ ⟨j, rfl⟩)

/-- `step 𝒦 = 𝒦` iff every letter maps `𝒦` into itself. -/
theorem step_eq_self_iff (K : Submodule ℂ (Fin h → ℂ)) :
    step c K = K ↔ ∀ l, K.map (letter c l).mulVecLin ≤ K := by
  constructor
  · intro hK l
    have H : K.map (letter c l).mulVecLin ≤ step c K :=
      (le_iSup (fun l => K.map (letter c l).mulVecLin) l).trans le_sup_right
    rwa [hK] at H
  · intro hl
    exact le_antisymm (sup_le le_rfl (iSup_le hl)) (le_step c K)

/-- After the first equality the filtration is constant. -/
theorem cyclicFiltration_eq_of_stable {r : ℕ}
    (hr : cyclicFiltration c B (r + 1) = cyclicFiltration c B r) :
    ∀ s, r ≤ s → cyclicFiltration c B s = cyclicFiltration c B r := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => rfl
  | succ s _ ih => rw [cyclicFiltration_succ, ih, ← cyclicFiltration_succ, hr]

/-- If no equality occurs before `n`, the dimension has grown by at least `n`. -/
theorem le_finrank_of_strict (n : ℕ)
    (hn : ∀ s < n, cyclicFiltration c B (s + 1) ≠ cyclicFiltration c B s) :
    n ≤ Module.finrank ℂ (cyclicFiltration c B n) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hlt : cyclicFiltration c B n < cyclicFiltration c B (n + 1) :=
      lt_of_le_of_ne (le_step c _) (hn n (Nat.lt_succ_self n)).symm
    have := Submodule.finrank_lt_finrank_of_lt hlt
    have := ih fun s hs => hn s (Nat.lt_succ_of_lt hs)
    omega

/-- Some equality occurs at an index `≤ h`. -/
theorem exists_stable : ∃ r, r ≤ h ∧ cyclicFiltration c B (r + 1) = cyclicFiltration c B r := by
  by_contra hcon
  push Not at hcon
  have := le_finrank_of_strict c B (h + 1) fun s hs => hcon s (Nat.lt_succ_iff.mp hs)
  have hle := Submodule.finrank_le (cyclicFiltration c B (h + 1))
  simp only [Module.finrank_fin_fun] at hle
  omega

/-- **Termination**: the first equality index `r₀` satisfies `r₀ ≤ h = dim ℋ_F^amb`; every
earlier step is a strict increase (so there are at most `h` strict increases), and the
filtration is constant from `r₀` on. -/
theorem cyclicFiltration_stabilizes :
    ∃ r₀, r₀ ≤ h ∧ cyclicFiltration c B (r₀ + 1) = cyclicFiltration c B r₀ ∧
      (∀ s < r₀, cyclicFiltration c B s < cyclicFiltration c B (s + 1)) ∧
      ∀ s, r₀ ≤ s → cyclicFiltration c B s = cyclicFiltration c B r₀ := by
  classical
  have hex := exists_stable c B
  let P : ℕ → Prop := fun r => cyclicFiltration c B (r + 1) = cyclicFiltration c B r
  have hex' : ∃ r, P r := ⟨hex.choose, hex.choose_spec.2⟩
  refine ⟨Nat.find hex', (Nat.find_min' hex' hex.choose_spec.2).trans hex.choose_spec.1,
    Nat.find_spec hex', fun s hs => ?_, cyclicFiltration_eq_of_stable c B (Nat.find_spec hex')⟩
  exact lt_of_le_of_ne (le_step c _) (Ne.symm (Nat.find_min hex' hs))

/-! ### The minimal carrier -/

theorem minimalCarrier_invariant (a : Matrix (Fin h) (Fin h) ℂ) (ha : a ∈ loadedAlgebra c) :
    (minimalCarrier c B).map a.mulVecLin ≤ minimalCarrier c B := by
  rw [minimalCarrier, Submodule.map_span_le]
  rintro v ⟨a', ha', w, hw, rfl⟩
  refine Submodule.subset_span ⟨a * a', mul_mem ha ha', w, hw, ?_⟩
  simp [Matrix.mulVec_mulVec]

theorem range_le_minimalCarrier : LinearMap.range B.mulVecLin ≤ minimalCarrier c B := by
  intro w hw
  exact Submodule.subset_span ⟨1, one_mem _, w, hw, by simp⟩

/-- Every stage of the filtration lies in `𝒜_F Ran B_F`. -/
theorem cyclicFiltration_le_minimalCarrier (r : ℕ) :
    cyclicFiltration c B r ≤ minimalCarrier c B := by
  induction r with
  | zero => exact range_le_minimalCarrier c B
  | succ r ih =>
    refine sup_le ih (iSup_le fun l => ?_)
    exact (Submodule.map_mono ih).trans
      (minimalCarrier_invariant c B _ (letter_mem_loadedAlgebra c l))

/-- A subspace invariant under every letter is invariant under the whole loaded algebra. -/
theorem invariant_of_letters (K : Submodule ℂ (Fin h → ℂ))
    (hl : ∀ l, K.map (letter c l).mulVecLin ≤ K) :
    ∀ a ∈ loadedAlgebra c, K.map a.mulVecLin ≤ K := by
  have hinv : ∀ a : Matrix (Fin h) (Fin h) ℂ,
      K.map a.mulVecLin ≤ K ↔ ∀ v ∈ K, a *ᵥ v ∈ K := by
    intro a
    rw [Submodule.map_le_iff_le_comap]
    exact ⟨fun H v hv => H hv, fun H v hv => H v hv⟩
  intro a ha
  suffices H : (∀ v ∈ K, a *ᵥ v ∈ K) ∧ ∀ v ∈ K, aᴴ *ᵥ v ∈ K from (hinv a).2 H.1
  induction ha using StarAlgebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨(hinv _).1 (hl (j, false)), (hinv _).1 (hl (j, true))⟩
  | algebraMap r =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact K.smul_mem _ hv
    · rw [Algebra.algebraMap_eq_smul_one, conjTranspose_smul, conjTranspose_one,
        Matrix.smul_mulVec, Matrix.one_mulVec]
      exact K.smul_mem _ hv
  | add x y _ _ hx hy =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [Matrix.add_mulVec]; exact K.add_mem (hx.1 v hv) (hy.1 v hv)
    · rw [conjTranspose_add, Matrix.add_mulVec]; exact K.add_mem (hx.2 v hv) (hy.2 v hv)
  | mul x y _ _ hx hy =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [← Matrix.mulVec_mulVec]; exact hx.1 _ (hy.1 v hv)
    · rw [conjTranspose_mul, ← Matrix.mulVec_mulVec]; exact hy.2 _ (hx.2 v hv)
  | star x _ hx =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [Matrix.star_eq_conjTranspose]; exact hx.2 v hv
    · rw [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]; exact hx.1 v hv

/-- **`eq:fermion-minimal-carrier`**: at any equality `𝒦_{r+1} = 𝒦_r`, the stabilized space is
`𝒦_F^min = 𝒜_F Ran B_F`. -/
theorem stable_eq_minimalCarrier {r : ℕ}
    (hr : cyclicFiltration c B (r + 1) = cyclicFiltration c B r) :
    cyclicFiltration c B r = minimalCarrier c B := by
  refine le_antisymm (cyclicFiltration_le_minimalCarrier c B r) ?_
  have hl := (step_eq_self_iff c _).1 hr
  have hA := invariant_of_letters c _ hl
  have h0 : LinearMap.range B.mulVecLin ≤ cyclicFiltration c B r :=
    cyclicFiltration_monotone c B (Nat.zero_le r)
  rw [minimalCarrier, Submodule.span_le]
  rintro v ⟨a, ha, w, hw, rfl⟩
  exact hA a ha ⟨w, h0 hw, rfl⟩

/-! ### Reduction -/

/-- The range of a matrix. -/
abbrev rangeOf {n : Type*} [Fintype n] (S : Matrix (Fin h) n ℂ) : Submodule ℂ (Fin h → ℂ) :=
  LinearMap.range S.mulVecLin

/-- Invariance of `Ran P` (for an idempotent `P`) is `P a P = a P`. -/
theorem map_le_range_iff {P a : Matrix (Fin h) (Fin h) ℂ} (hP : P * P = P) :
    (rangeOf P).map a.mulVecLin ≤ rangeOf P ↔ P * a * P = a * P := by
  constructor
  · intro H
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply]
    have hmem : a *ᵥ (P *ᵥ v) ∈ rangeOf P := H ⟨P *ᵥ v, ⟨v, rfl⟩, rfl⟩
    obtain ⟨u, hu⟩ := hmem
    simp only [Matrix.mulVecLin_apply] at hu
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu,
      Matrix.mulVec_mulVec, hP]
  · intro H
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨a *ᵥ (P *ᵥ v), ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, H]

/-- **Reduction**: at any equality `𝒦_{r+1} = 𝒦_r`, every `a ∈ 𝒜_F` leaves `𝒦_r` invariant and
commutes with every orthogonal projector `P` onto `𝒦_r`; since `𝒜_F` is `*`-closed, `𝒦_r` and its
orthogonal complement are both invariant (`𝒦_r` reduces `𝒜_F`). -/
theorem stable_reduces {r : ℕ} (hr : cyclicFiltration c B (r + 1) = cyclicFiltration c B r)
    (P : Matrix (Fin h) (Fin h) ℂ) (hP : P * P = P) (hPH : Pᴴ = P)
    (hran : rangeOf P = cyclicFiltration c B r) :
    ∀ a ∈ loadedAlgebra c,
      (cyclicFiltration c B r).map a.mulVecLin ≤ cyclicFiltration c B r ∧ P * a = a * P := by
  have hA := invariant_of_letters c _ ((step_eq_self_iff c _).1 hr)
  intro a ha
  refine ⟨hA a ha, ?_⟩
  have h1 : P * a * P = a * P := (map_le_range_iff hP).1 (hran ▸ hA a ha)
  have hs : aᴴ ∈ loadedAlgebra c := by
    rw [← Matrix.star_eq_conjTranspose]; exact star_mem ha
  have h2 : P * aᴴ * P = aᴴ * P := (map_le_range_iff hP).1 (hran ▸ hA _ hs)
  have h3 := congrArg Matrix.conjTranspose h2
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hPH, ← Matrix.mul_assoc] at h3
  rw [← h3, h1]

/-- An orthogonal projector onto any subspace exists. -/
theorem exists_projector (K : Submodule ℂ (Fin h → ℂ)) :
    ∃ P : Matrix (Fin h) (Fin h) ℂ, P * P = P ∧ Pᴴ = P ∧ rangeOf P = K := by
  classical
  let b := Module.finBasis ℂ K
  let S : Matrix (Fin h) (Fin (Module.finrank ℂ K)) ℂ := Matrix.of fun i k => (b k : Fin h → ℂ) i
  have hS : rangeOf S = K := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      have : S *ᵥ v = ((∑ k, v k • b k : K) : Fin h → ℂ) := by
        ext i
        simp [S, Matrix.mulVec, dotProduct, mul_comm]
      simp only [Matrix.mulVecLin_apply, this]
      exact Submodule.coe_mem _
    · intro x hx
      refine ⟨fun k => b.repr ⟨x, hx⟩ k, ?_⟩
      have hsum := b.sum_repr ⟨x, hx⟩
      have := congrArg (fun y : K => (y : Fin h → ℂ)) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      ext i
      have hi := congrFun this i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, S, Matrix.of_apply]
      rw [← hi]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  obtain ⟨_, _, _, hPH, hP2, hPS⟩ := sourceGramPseudoinverse_projection S
  refine ⟨sourceRangeProjection S, hP2, hPH, ?_⟩
  suffices H : rangeOf (sourceRangeProjection S) = rangeOf S by rw [H, hS]
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨(sourceGramPseudoinverse S * Sᴴ) *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, sourceRangeProjection,
      Matrix.mul_assoc]
  · rintro _ ⟨v, rfl⟩
    refine ⟨S *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPS]

/-! ### The cyclic innovation and its rank -/

/-- The explicit column bank `(c_j S, c_j^* S)_j` of a synthesis `S`. -/
def columnBank {e : ℕ} (S : Matrix (Fin h) (Fin e) ℂ) :
    Matrix (Fin h) ((Fin m × Bool) × Fin e) ℂ :=
  Matrix.of fun i lk => (letter c lk.1 * S) i lk.2

theorem columnBank_mulVec {e : ℕ} (S : Matrix (Fin h) (Fin e) ℂ)
    (v : (Fin m × Bool) × Fin e → ℂ) :
    columnBank c S *ᵥ v = ∑ l : Fin m × Bool, (letter c l * S) *ᵥ fun k => v (l, k) := by
  ext i
  simp only [columnBank, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply,
    Fintype.sum_prod_type]

theorem range_columnBank {e : ℕ} (S : Matrix (Fin h) (Fin e) ℂ) :
    rangeOf (columnBank c S) = nextColumns c (rangeOf S) := by
  classical
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    simp only [Matrix.mulVecLin_apply, columnBank_mulVec]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [← Matrix.mulVec_mulVec]
    exact (le_iSup (fun l => (rangeOf S).map (letter c l).mulVecLin) l)
      ⟨S *ᵥ fun k => v (l, k), ⟨_, rfl⟩, rfl⟩
  · refine iSup_le fun l => ?_
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨fun lk => if lk.1 = l then w lk.2 else 0, ?_⟩
    simp only [Matrix.mulVecLin_apply, columnBank_mulVec]
    have hz : ∀ l' ∈ (Finset.univ : Finset (Fin m × Bool)), l' ≠ l →
        ((letter c l' * S) *ᵥ fun k => if l' = l then w k else 0) = 0 := by
      intro l' _ hl'
      simp only [hl', ite_false]
      exact Matrix.mulVec_zero _
    rw [Finset.sum_eq_single l hz (by simp)]
    simp only [ite_true, Matrix.mulVec_mulVec]

/-- Reindexing the columns by an equivalence does not change the range. -/
theorem range_submatrix_equiv {n n' : Type*} [Fintype n] [Fintype n']
    (S : Matrix (Fin h) n ℂ) (σ : n' ≃ n) :
    rangeOf (S.submatrix id σ) = rangeOf S := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨fun k => v (σ.symm k), ?_⟩
    ext i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
    exact Fintype.sum_equiv σ.symm _ _ (fun k => by simp)
  · rintro _ ⟨v, rfl⟩
    refine ⟨fun k => v (σ k), ?_⟩
    ext i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
    exact (Fintype.sum_equiv σ _ _ (fun k => rfl))

theorem range_fromCols {e₁ e₂ : ℕ} (S : Matrix (Fin h) (Fin e₁) ℂ)
    (N : Matrix (Fin h) (Fin e₂) ℂ) :
    rangeOf (Matrix.fromCols S N) = rangeOf S ⊔ rangeOf N := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    simp only [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · rw [sup_le_iff]
    constructor
    · rintro _ ⟨v, rfl⟩
      exact ⟨Sum.elim v 0, by simp⟩
    · rintro _ ⟨v, rfl⟩
      exact ⟨Sum.elim 0 v, by simp⟩

/-- A matrix has rank zero iff it vanishes. -/
theorem rank_eq_zero_iff {n n' : Type*} [Fintype n] [Fintype n'] (A : Matrix n n' ℂ) :
    A.rank = 0 ↔ A = 0 := by
  classical
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  constructor
  · intro h
    apply Matrix.toLin'.injective
    rw [map_zero]
    exact h
  · rintro rfl
    exact Matrix.mulVecLin_zero

/-- **`eq:fermion-cyclic-innovation`, `eq:fermion-cyclic-rank`.**  If `S_r` synthesizes `𝒦_r`
and `N_r` synthesizes the next columns `∑_j (c_j 𝒦_r + c_j^* 𝒦_r)`, then
`𝕃_r = D_r − C_r^* G_r^† C_r = N_r^*(I − P_r)N_r ⪰ 0` and
`rank 𝕃_r = dim 𝒦_{r+1} − dim 𝒦_r`; in particular `𝕃_r = 0` iff `𝒦_{r+1} = 𝒦_r`. -/
theorem cyclic_innovation_rank {e₁ e₂ : ℕ} (r : ℕ) (S : Matrix (Fin h) (Fin e₁) ℂ)
    (N : Matrix (Fin h) (Fin e₂) ℂ) (hS : rangeOf S = cyclicFiltration c B r)
    (hN : rangeOf N = nextColumns c (cyclicFiltration c B r)) :
    sourceSchurResidual S N = Nᴴ * (1 - sourceRangeProjection S) * N ∧
      (sourceSchurResidual S N).PosSemidef ∧
      (sourceSchurResidual S N).rank =
        Module.finrank ℂ (cyclicFiltration c B (r + 1)) -
          Module.finrank ℂ (cyclicFiltration c B r) ∧
      (sourceSchurResidual S N = 0 ↔
        cyclicFiltration c B (r + 1) = cyclicFiltration c B r) := by
  have hblock : (Matrix.fromCols S N)ᴴ * Matrix.fromCols S N =
      Matrix.fromBlocks (Sᴴ * S) (Sᴴ * N) ((Sᴴ * N)ᴴ) (Nᴴ * N) := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hrank := sourceSchurResidual_rank_increment S N
  rw [← hblock, Matrix.rank_conjTranspose_mul_self, Matrix.rank_conjTranspose_mul_self] at hrank
  have hC : (Matrix.fromCols S N).rank = Module.finrank ℂ (cyclicFiltration c B (r + 1)) := by
    show Module.finrank ℂ (rangeOf (Matrix.fromCols S N)) = _
    rw [range_fromCols, hS, hN]
    rfl
  have hS' : S.rank = Module.finrank ℂ (cyclicFiltration c B r) := by
    show Module.finrank ℂ (rangeOf S) = _
    rw [hS]
  have hR : (sourceSchurResidual S N).rank = Module.finrank ℂ (cyclicFiltration c B (r + 1)) -
      Module.finrank ℂ (cyclicFiltration c B r) := by
    rw [← hrank, hC, hS']
  refine ⟨sourceSchurResidual_eq_orthogonalResidual S N, sourceSchurResidual_posSemidef S N, hR,
    ?_⟩
  rw [← rank_eq_zero_iff, hR]
  have hle : cyclicFiltration c B r ≤ cyclicFiltration c B (r + 1) := le_step c _
  constructor
  · intro h0
    have hfin : Module.finrank ℂ (cyclicFiltration c B (r + 1)) ≤
        Module.finrank ℂ (cyclicFiltration c B r) := Nat.sub_eq_zero_iff_le.mp h0
    exact (Submodule.eq_of_le_of_finrank_le hle hfin).symm
  · intro heq
    rw [heq, Nat.sub_self]

/-- The explicit column bank, reindexed by `Fin`, is a valid `N_r`. -/
theorem cyclic_innovation_rank_columnBank {e₁ : ℕ} (r : ℕ) (S : Matrix (Fin h) (Fin e₁) ℂ)
    (hS : rangeOf S = cyclicFiltration c B r) :
    let N := (columnBank c S).submatrix id
      (Fintype.equivFin ((Fin m × Bool) × Fin e₁)).symm
    (sourceSchurResidual S N).PosSemidef ∧
      (sourceSchurResidual S N).rank =
        Module.finrank ℂ (cyclicFiltration c B (r + 1)) -
          Module.finrank ℂ (cyclicFiltration c B r) := by
  intro N
  have hN : rangeOf N = nextColumns c (cyclicFiltration c B r) := by
    rw [range_submatrix_equiv, range_columnBank, hS]
  obtain ⟨_, h1, h2, _⟩ := cyclic_innovation_rank c B r S N hS hN
  exact ⟨h1, h2⟩

/-! ### Compression preserves the loaded source-word Grams -/

/-- The operator `w(c)` of a loaded word (a list of letters). -/
def wordOp (w : List (Fin m × Bool)) : Matrix (Fin h) (Fin h) ℂ :=
  (w.map (letter c)).prod

/-- The compressed word `w(P c P)`. -/
def compressedWordOp (P : Matrix (Fin h) (Fin h) ℂ) (w : List (Fin m × Bool)) :
    Matrix (Fin h) (Fin h) ℂ :=
  (w.map fun l => P * letter c l * P).prod

theorem wordOp_mem (w : List (Fin m × Bool)) : wordOp c w ∈ loadedAlgebra c := by
  induction w with
  | nil => exact one_mem _
  | cons l w ih =>
    simp only [wordOp, List.map_cons, List.prod_cons] at ih ⊢
    exact mul_mem (letter_mem_loadedAlgebra c l) ih

/-- **Compression clause**: if `P` is an idempotent commuting with every letter and fixing the
source (`P B_F = B_F`), then `w(P c P) B_F = w(c) B_F` for every loaded word; hence every loaded
source-word Gram is preserved: `B_F^* w(P c P) B_F = B_F^* w(c) B_F`. -/
theorem compressed_word_gram (P : Matrix (Fin h) (Fin h) ℂ) (hP : P * P = P)
    (hcomm : ∀ l, P * letter c l = letter c l * P) (hPB : P * B = B)
    (w : List (Fin m × Bool)) :
    compressedWordOp c P w * B = wordOp c w * B ∧
      Bᴴ * compressedWordOp c P w * B = Bᴴ * wordOp c w * B := by
  have hW : ∀ w : List (Fin m × Bool), P * wordOp c w = wordOp c w * P := by
    intro w
    induction w with
    | nil => simp [wordOp]
    | cons l w ih =>
      simp only [wordOp, List.map_cons, List.prod_cons] at ih ⊢
      rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, ih, Matrix.mul_assoc]
  have key : compressedWordOp c P w * B = wordOp c w * B := by
    induction w with
    | nil => simp [compressedWordOp, wordOp]
    | cons l w ih =>
      simp only [compressedWordOp, wordOp, List.map_cons, List.prod_cons] at ih ⊢
      rw [Matrix.mul_assoc, ih]
      calc P * letter c l * P * ((List.map (letter c) w).prod * B)
          = P * letter c l * (P * wordOp c w * B) := by
            simp only [wordOp, Matrix.mul_assoc]
        _ = P * letter c l * (wordOp c w * B) := by
            congr 1
            rw [hW, Matrix.mul_assoc, hPB]
        _ = letter c l * (P * (wordOp c w * B)) := by
            rw [hcomm, Matrix.mul_assoc]
        _ = letter c l * ((List.map (letter c) w).prod * B) := by
            rw [← Matrix.mul_assoc P, hW, Matrix.mul_assoc, hPB]; rfl
        _ = letter c l * (List.map (letter c) w).prod * B := by rw [Matrix.mul_assoc]
  refine ⟨key, ?_⟩
  rw [Matrix.mul_assoc, key, ← Matrix.mul_assoc]

/-- **Invisibility of the complement**: if `P` commutes with every letter and `P B_F = B_F`,
every vector `x` with `P x = 0` (orthogonal to `𝒦_F^min` for the orthogonal projector `P`) is
invisible to every source correlation: `(w(c) B_F)^* x = 0`. -/
theorem complement_invisible (P : Matrix (Fin h) (Fin h) ℂ) (hPH : Pᴴ = P)
    (hcomm : ∀ l, P * letter c l = letter c l * P) (hPB : P * B = B)
    (w : List (Fin m × Bool)) (x : Fin h → ℂ) (hx : P *ᵥ x = 0) :
    (wordOp c w * B)ᴴ *ᵥ x = 0 := by
  have hW : P * wordOp c w = wordOp c w * P := by
    induction w with
    | nil => simp [wordOp]
    | cons l w ih =>
      simp only [wordOp, List.map_cons, List.prod_cons] at ih ⊢
      rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, ih, Matrix.mul_assoc]
  have hfix : wordOp c w * B = P * (wordOp c w * B) := by
    rw [← Matrix.mul_assoc, hW, Matrix.mul_assoc, hPB]
  rw [hfix, conjTranspose_mul, hPH, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- **`thm:fermion-source-saturation`, assembled.**  The cyclic filtration stabilizes after at
most `h` strict increases at `𝒦_F^min = 𝒜_F Ran B_F`; the stabilized space reduces `𝒜_F`; for
every stage the innovation `𝕃_r` is `N_r^*(I − P_r)N_r ⪰ 0` with
`rank 𝕃_r = dim 𝒦_{r+1} − dim 𝒦_r` (exact terminating test `𝕃_r = 0`); and compression to
`𝒦_F^min` preserves every loaded source-word Gram while its orthogonal complement is invisible
to all source correlations. -/
theorem fermion_source_saturation :
    (∃ r₀, r₀ ≤ h ∧ cyclicFiltration c B (r₀ + 1) = cyclicFiltration c B r₀ ∧
      (∀ s < r₀, cyclicFiltration c B s < cyclicFiltration c B (s + 1)) ∧
      (∀ s, r₀ ≤ s → cyclicFiltration c B s = minimalCarrier c B) ∧
      ∀ P : Matrix (Fin h) (Fin h) ℂ, P * P = P → Pᴴ = P →
        rangeOf P = minimalCarrier c B →
        (∀ a ∈ loadedAlgebra c, (minimalCarrier c B).map a.mulVecLin ≤ minimalCarrier c B ∧
          P * a = a * P) ∧
        (∀ w : List (Fin m × Bool),
          Bᴴ * compressedWordOp c P w * B = Bᴴ * wordOp c w * B) ∧
        (∀ (w : List (Fin m × Bool)) (x : Fin h → ℂ), P *ᵥ x = 0 →
          (wordOp c w * B)ᴴ *ᵥ x = 0)) ∧
    (∀ {e₁ e₂ : ℕ} (r : ℕ) (S : Matrix (Fin h) (Fin e₁) ℂ) (N : Matrix (Fin h) (Fin e₂) ℂ),
      rangeOf S = cyclicFiltration c B r →
      rangeOf N = nextColumns c (cyclicFiltration c B r) →
      sourceSchurResidual S N = Nᴴ * (1 - sourceRangeProjection S) * N ∧
      (sourceSchurResidual S N).PosSemidef ∧
      (sourceSchurResidual S N).rank =
        Module.finrank ℂ (cyclicFiltration c B (r + 1)) -
          Module.finrank ℂ (cyclicFiltration c B r) ∧
      (sourceSchurResidual S N = 0 ↔
        cyclicFiltration c B (r + 1) = cyclicFiltration c B r)) := by
  classical
  refine ⟨?_, fun r S N hS hN => cyclic_innovation_rank c B r S N hS hN⟩
  obtain ⟨r₀, hr₀, hstab, hstrict, hconst⟩ := cyclicFiltration_stabilizes c B
  have hmin := stable_eq_minimalCarrier c B hstab
  refine ⟨r₀, hr₀, hstab, hstrict, fun s hs => (hconst s hs).trans hmin, ?_⟩
  intro P hP hPH hran
  have hred := stable_reduces c B hstab P hP hPH (hran.trans hmin.symm)
  rw [hmin] at hred
  have hcomm : ∀ l, P * letter c l = letter c l * P := fun l =>
    (hred _ (letter_mem_loadedAlgebra c l)).2
  have hPB : P * B = B := by
    have hle := range_le_minimalCarrier c B
    rw [← hran] at hle
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply]
    obtain ⟨u, hu⟩ := hle ⟨v, rfl⟩
    simp only [Matrix.mulVecLin_apply] at hu
    rw [← Matrix.mulVec_mulVec, ← hu, Matrix.mulVec_mulVec, hP]
  exact ⟨hred, fun w => (compressed_word_gram c B P hP hcomm hPB w).2,
    fun w x hx => complement_invisible c B P hPH hcomm hPB w x hx⟩

end FermionSourceSaturation
end RenewalGeometry
