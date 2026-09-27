/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
/-!
# Shifted Hankel ranks of a local realization and Jordan structure

Infrastructure for `thm:supp-pole-Hankel` (P1) of `papers/predictive_spectral_geometry`: for a
local realization `(N, B, L)` (state operator `N` on `V`, source `B : H → V`, output `L : V → H`)
with coefficient sequence `C_k = L N^k B`, the shifted block-Hankel operators
`H_s = [C_{i+j+s}]_{i,j < p}` factor as `H_s = O_p ∘ N^s ∘ R_p` through the observability map
`O_p x = (L N^i x)_i` and the controllability map `R_p u = ∑_j N^j B u_j`
(`hankelMap_eq_obsMap_comp_ctrlMap`).  When the local realization is controllable
(`R_p` onto) and observable (`O_p` injective), the rank of `H_s` is the rank of `N^s`
(`finrank_range_hankelMap`).

For a nilpotent `N`, the ranks of the powers `N^s` determine the Jordan structure: if `V` has a
basis of Jordan chains `N^j v_i` (`j < len i`), the number of chains of length `≥ k + 1` is
`rank N^k - rank N^(k+1)` (`card_chains_ge_eq_finrank_sub`), so the shifted Hankel ranks determine
the local McMillan degree `dim V = rank H_0` and all Jordan block sizes.
-/

open Module LinearMap

namespace RenewalGeometry
namespace NilpotentHankel

variable {K : Type*} [Field K] {V H : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup H] [Module K H]

/-! ## Ranks of compositions with onto / one-to-one maps -/

theorem finrank_range_comp_of_range_eq_top {U W : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (g : U →ₗ[K] V) (hg : range g = ⊤) :
    finrank K (range (f ∘ₗ g)) = finrank K (range f) := by
  rw [range_comp_of_range_eq_top f hg]

theorem finrank_range_comp_of_ker_eq_bot {W W' : Type*} [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module K W'] (O : W →ₗ[K] W') (f : V →ₗ[K] W) (hO : ker O = ⊥) :
    finrank K (range (O ∘ₗ f)) = finrank K (range f) := by
  rw [range_comp]
  exact (Submodule.equivMapOfInjective O (ker_eq_bot.mp hO) (range f)).finrank_eq.symm

/-! ## The Hankel, controllability and observability maps of a local realization -/

variable (N : Module.End K V) (B : H →ₗ[K] V) (L : V →ₗ[K] H)

/-- The controllability map `R_p u = ∑_{j < p} N^j B u_j`. -/
noncomputable def ctrlMap (p : ℕ) : (Fin p → H) →ₗ[K] V :=
  ∑ j : Fin p, (N ^ (j : ℕ)) ∘ₗ B ∘ₗ LinearMap.proj j

/-- The observability map `O_p x = (L N^i x)_{i < p}`. -/
noncomputable def obsMap (p : ℕ) : V →ₗ[K] (Fin p → H) :=
  LinearMap.pi fun i : Fin p => L ∘ₗ N ^ (i : ℕ)

/-- The shifted block-Hankel operator `H_s u = (∑_j C_{i+j+s} u_j)_i` with `C_k = L N^k B`. -/
noncomputable def hankelMap (s p : ℕ) : (Fin p → H) →ₗ[K] (Fin p → H) :=
  LinearMap.pi fun i : Fin p => ∑ j : Fin p, L ∘ₗ (N ^ ((i : ℕ) + j + s)) ∘ₗ B ∘ₗ LinearMap.proj j

theorem ctrlMap_apply (p : ℕ) (u : Fin p → H) :
    ctrlMap N B p u = ∑ j : Fin p, (N ^ (j : ℕ)) (B (u j)) := by
  simp [ctrlMap]

theorem obsMap_apply (p : ℕ) (x : V) (i : Fin p) : obsMap N L p x i = L ((N ^ (i : ℕ)) x) := by
  simp [obsMap]

theorem hankelMap_apply (s p : ℕ) (u : Fin p → H) (i : Fin p) :
    hankelMap N B L s p u i = ∑ j : Fin p, L ((N ^ ((i : ℕ) + j + s)) (B (u j))) := by
  simp [hankelMap]

/-- **Hankel factorization** `H_s = O_p ∘ N^s ∘ R_p`. -/
theorem hankelMap_eq_obsMap_comp_ctrlMap (s p : ℕ) :
    hankelMap N B L s p = obsMap N L p ∘ₗ (N ^ s) ∘ₗ ctrlMap N B p := by
  refine LinearMap.ext fun u => funext fun i => ?_
  rw [comp_apply, comp_apply, obsMap_apply, ctrlMap_apply, hankelMap_apply]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_add, ← pow_add]
  congr 2
  omega

/-- **Shifted Hankel ranks of a controllable and observable local realization are the ranks of
the powers of the state operator** (`thm:supp-pole-Hankel`, (P1)). -/
theorem finrank_range_hankelMap (s p : ℕ) (hctrl : range (ctrlMap N B p) = ⊤)
    (hobs : ker (obsMap N L p) = ⊥) :
    finrank K (range (hankelMap N B L s p)) = finrank K (range (N ^ s)) := by
  rw [hankelMap_eq_obsMap_comp_ctrlMap, ← comp_assoc,
    finrank_range_comp_of_range_eq_top _ _ hctrl, finrank_range_comp_of_ker_eq_bot _ _ hobs]

/-- The unshifted Hankel rank is the local McMillan degree `dim V`. -/
theorem finrank_range_hankelMap_zero [FiniteDimensional K V] (p : ℕ)
    (hctrl : range (ctrlMap N B p) = ⊤) (hobs : ker (obsMap N L p) = ⊥) :
    finrank K (range (hankelMap N B L 0 p)) = finrank K V := by
  rw [finrank_range_hankelMap N B L 0 p hctrl hobs, pow_zero, Module.End.one_eq_id, range_id,
    finrank_top]

/-! ## Jordan chains and ranks of powers -/

section Jordan

open scoped Classical

variable {ι : Type*} [Fintype ι] {N} {v : ι → V} {len : ι → ℕ}

/-- The index set of the basis vectors `N^j v_i` with `j ≥ s`. -/
def shiftedIndices (len : ι → ℕ) (s : ℕ) : Set (Σ i : ι, Fin (len i)) := {x | s ≤ (x.2 : ℕ)}

omit [Fintype ι] in
theorem pow_apply_eq_zero_of_le (hlen : ∀ i, (N ^ len i) (v i) = 0) (i : ι) {n : ℕ}
    (hn : len i ≤ n) : (N ^ n) (v i) = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm, pow_add, Module.End.mul_apply, hlen, map_zero]

omit [Fintype ι] in
/-- Given a basis of Jordan chains, `range N^s` is the span of the chain vectors `N^j v_i` with
`j ≥ s`. -/
theorem range_pow_eq_span (b : Basis (Σ i : ι, Fin (len i)) K V)
    (hb : ∀ i (j : Fin (len i)), b ⟨i, j⟩ = (N ^ (j : ℕ)) (v i))
    (hlen : ∀ i, (N ^ len i) (v i) = 0) (s : ℕ) :
    range (N ^ s) = Submodule.span K (b '' shiftedIndices len s) := by
  rw [range_eq_map, ← b.span_eq, Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩
    rw [hb, ← Module.End.mul_apply, ← pow_add]
    by_cases h : s + j < len i
    · refine Submodule.subset_span ⟨⟨i, ⟨s + j, h⟩⟩, ?_, ?_⟩
      · change s ≤ s + j
        omega
      · rw [hb]
    · rw [pow_apply_eq_zero_of_le hlen i (not_lt.mp h)]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, hj, rfl⟩
    change s ≤ (j : ℕ) at hj
    refine Submodule.subset_span ⟨b ⟨i, ⟨(j : ℕ) - s, by omega⟩⟩, ⟨_, rfl⟩, ?_⟩
    rw [hb, hb, ← Module.End.mul_apply, ← pow_add]
    congr 2
    change s + ((j : ℕ) - s) = (j : ℕ)
    omega

/-- `rank N^s` counts the chain vectors `N^j v_i` with `j ≥ s`. -/
theorem finrank_range_pow_eq_card (b : Basis (Σ i : ι, Fin (len i)) K V)
    (hb : ∀ i (j : Fin (len i)), b ⟨i, j⟩ = (N ^ (j : ℕ)) (v i))
    (hlen : ∀ i, (N ^ len i) (v i) = 0) (s : ℕ) :
    finrank K (range (N ^ s)) = Fintype.card (shiftedIndices len s) := by
  classical
  rw [range_pow_eq_span b hb hlen s]
  have hli : LinearIndependent K (b ∘ (Subtype.val : shiftedIndices len s → _)) :=
    b.linearIndependent.comp _ Subtype.val_injective
  have himg : b '' shiftedIndices len s = Set.range (b ∘ (Subtype.val : shiftedIndices len s → _)) := by
    rw [Set.range_comp, Subtype.range_coe]
  rw [himg]
  exact finrank_span_eq_card hli

/-- The chain vectors with `j ≥ k` are those with `j ≥ k + 1` together with one vector `N^k v_i`
for each chain of length `≥ k + 1`. -/
theorem card_shiftedIndices (len : ι → ℕ) (k : ℕ) :
    Fintype.card {i : ι // k + 1 ≤ len i} + Fintype.card (shiftedIndices len (k + 1)) =
      Fintype.card (shiftedIndices len k) := by
  rw [← Fintype.card_sum]
  let f : {i : ι // k + 1 ≤ len i} ⊕ shiftedIndices len (k + 1) → shiftedIndices len k :=
    fun x => match x with
      | Sum.inl i => ⟨⟨i.1, ⟨k, i.2⟩⟩, show k ≤ k from le_rfl⟩
      | Sum.inr y => ⟨y.1, show k ≤ _ from (Nat.le_succ k).trans y.2⟩
  let g : shiftedIndices len k → {i : ι // k + 1 ≤ len i} ⊕ shiftedIndices len (k + 1) :=
    fun x => if h : (x.1.2 : ℕ) = k then Sum.inl ⟨x.1.1, by have := x.1.2.2; omega⟩
      else Sum.inr ⟨x.1, by have := x.2; change k ≤ _ at this; change k + 1 ≤ _; omega⟩
  have hgf : Function.LeftInverse g f := by
    rintro (i | y)
    · simp [f, g]
    · have hy : (y.1.2 : ℕ) ≠ k := by have := y.2; change k + 1 ≤ _ at this; omega
      simp [f, g, hy]
  have hfg : Function.RightInverse g f := by
    intro x
    by_cases h : (x.1.2 : ℕ) = k
    · simp only [g, h, dite_true, f]
      refine Subtype.ext (Sigma.ext rfl ?_)
      exact heq_of_eq (Fin.ext h.symm)
    · simp [g, h, f]
  exact Fintype.card_congr ⟨f, g, hgf, hfg⟩

/-- **Jordan structure from ranks of powers**: given a basis of Jordan chains, the number of chains
of length `≥ k + 1` is `rank N^k - rank N^(k+1)` (`thm:supp-pole-Hankel`, (P1): with
`finrank_range_hankelMap`, the shifted Hankel ranks determine all Jordan block sizes). -/
theorem card_chains_ge_eq_finrank_sub (b : Basis (Σ i : ι, Fin (len i)) K V)
    (hb : ∀ i (j : Fin (len i)), b ⟨i, j⟩ = (N ^ (j : ℕ)) (v i))
    (hlen : ∀ i, (N ^ len i) (v i) = 0) (k : ℕ) :
    Fintype.card {i : ι // k + 1 ≤ len i} =
      finrank K (range (N ^ k)) - finrank K (range (N ^ (k + 1))) := by
  rw [finrank_range_pow_eq_card b hb hlen k, finrank_range_pow_eq_card b hb hlen (k + 1),
    ← card_shiftedIndices len k]
  omega

/-- The number of chains (Jordan blocks) is `dim V - rank N`. -/
theorem card_chains_eq_finrank_sub [FiniteDimensional K V] (b : Basis (Σ i : ι, Fin (len i)) K V)
    (hb : ∀ i (j : Fin (len i)), b ⟨i, j⟩ = (N ^ (j : ℕ)) (v i))
    (hlen : ∀ i, (N ^ len i) (v i) = 0) :
    Fintype.card {i : ι // 1 ≤ len i} = finrank K V - finrank K (range N) := by
  have := card_chains_ge_eq_finrank_sub b hb hlen 0
  rwa [pow_zero, Module.End.one_eq_id, range_id, finrank_top, zero_add, pow_one] at this

end Jordan

end NilpotentHankel
end RenewalGeometry
