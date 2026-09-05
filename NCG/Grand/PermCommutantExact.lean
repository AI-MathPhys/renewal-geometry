/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.PermutationSpanExact

/-!
# Compressed Burnside surjectivity and the permutation commutant

Second machinery layer for `thm:SM-active-residual-algebra`.

* `exists_perm_two_points`: the symmetric group is transitive on ordered pairs of
  distinct points (explicit two-swap construction);
* `corner_mem_span`: the compression `(1 - P₀)·B·(1 - P₀)` of **any** matrix by the
  complement of the mean projector lies in the span of the permutation matrices —
  the external Burnside algebra acts as the **full** matrix algebra on the standard
  block (`C*(ρ_W(S_n)) = M_{n-1}` in compressed form);
* `commutant_perm_iff`: the commutant of the permutation algebra on the natural
  carrier is exactly `span{I, J}` — the multiplicity side `I ⊗ M_m` of the isotypic
  decomposition `𝟙 ⊕ W` (the SM.0j shape on the natural carrier).
-/

open Finset Matrix

namespace NCG
namespace PermCommutant

variable {n : Type*} [Fintype n] [DecidableEq n]

open NCG.PermSpan

/-- The all-ones matrix. -/
def jmat (n : Type*) [Fintype n] [DecidableEq n] : Matrix n n ℂ := fun _ _ => 1

theorem jmat_mem_span :
    jmat n ∈ Submodule.span ℂ (Set.range fun σ : Equiv.Perm n => σ.permMatrix ℂ) := by
  rw [span_permMatrix]
  intro i j
  simp [jmat]

omit [Fintype n] in
/-- Transitivity on ordered pairs of distinct points, by an explicit two-swap
construction. -/
theorem exists_perm_two_points {a b c d : n} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm n, σ a = c ∧ σ b = d := by
  set τ : Equiv.Perm n := Equiv.swap a c with hτ
  have hτa : τ a = c := Equiv.swap_apply_left a c
  have hτbne : τ b ≠ c := by
    intro hcon
    exact hab (τ.injective (hcon.trans hτa.symm)).symm
  refine ⟨τ.trans (Equiv.swap (τ b) d), ?_, ?_⟩
  · rw [Equiv.trans_apply, hτa,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hτbne) hcd]
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

/-- The mean projector `P₀ = J/n`. -/
noncomputable def meanProj (n : Type*) [Fintype n] [DecidableEq n] : Matrix n n ℂ :=
  ((Fintype.card n : ℂ))⁻¹ • jmat n

theorem meanProj_mem_span :
    meanProj n
      ∈ Submodule.span ℂ (Set.range fun σ : Equiv.Perm n => σ.permMatrix ℂ) :=
  Submodule.smul_mem _ _ jmat_mem_span

theorem rowSum_one (m : n) : ∑ k, (1 : Matrix n n ℂ) m k = 1 := by
  rw [Finset.sum_congr rfl fun k _ => Matrix.one_apply,
    Finset.sum_ite_eq Finset.univ m fun _ => (1 : ℂ), if_pos (Finset.mem_univ m)]

theorem colSum_one (m : n) : ∑ k, (1 : Matrix n n ℂ) k m = 1 := by
  have hc : ∀ k : n, (1 : Matrix n n ℂ) k m = if k = m then 1 else 0 := fun k =>
    Matrix.one_apply
  rw [Finset.sum_congr rfl fun k _ => hc k,
    Finset.sum_ite_eq' Finset.univ m fun _ => (1 : ℂ), if_pos (Finset.mem_univ m)]

theorem rowSum_oneSubMeanProj (m : n) : ∑ k, (1 - meanProj n) m k = 0 := by
  have hcard : ((Fintype.card n : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (@Fintype.card_ne_zero n _ ⟨m⟩)
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib, meanProj, Matrix.smul_apply,
    jmat, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [rowSum_one m, mul_inv_cancel₀ hcard, sub_self]

theorem colSum_oneSubMeanProj (m : n) : ∑ k, (1 - meanProj n) k m = 0 := by
  have hcard : ((Fintype.card n : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (@Fintype.card_ne_zero n _ ⟨m⟩)
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib, meanProj, Matrix.smul_apply,
    jmat, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [colSum_one m, mul_inv_cancel₀ hcard, sub_self]

omit [DecidableEq n] in
theorem rowSum_mul_right_zero (A C : Matrix n n ℂ)
    (hC : ∀ m, ∑ k, C m k = 0) (i : n) : ∑ k, (A * C) i k = 0 := by
  calc ∑ k, (A * C) i k = ∑ k, ∑ m, A i m * C m k :=
        Finset.sum_congr rfl fun k _ => Matrix.mul_apply
    _ = ∑ m, ∑ k, A i m * C m k := Finset.sum_comm
    _ = ∑ m, A i m * ∑ k, C m k :=
        Finset.sum_congr rfl fun m _ => (Finset.mul_sum _ _ _).symm
    _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hC m, mul_zero]

omit [DecidableEq n] in
theorem colSum_mul_left_zero (A C : Matrix n n ℂ)
    (hA : ∀ m, ∑ k, A k m = 0) (j : n) : ∑ k, (A * C) k j = 0 := by
  calc ∑ k, (A * C) k j = ∑ k, ∑ m, A k m * C m j :=
        Finset.sum_congr rfl fun k _ => Matrix.mul_apply
    _ = ∑ m, ∑ k, A k m * C m j := Finset.sum_comm
    _ = ∑ m, (∑ k, A k m) * C m j :=
        Finset.sum_congr rfl fun m _ => (Finset.sum_mul _ _ _).symm
    _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hA m, zero_mul]

/-- **Compressed Burnside surjectivity**: the compression of any matrix by the
complement of the mean projector lies in the external Burnside algebra. -/
theorem corner_mem_span (B : Matrix n n ℂ) :
    (1 - meanProj n) * B * (1 - meanProj n)
      ∈ Submodule.span ℂ (Set.range fun σ : Equiv.Perm n => σ.permMatrix ℂ) := by
  rw [span_permMatrix]
  intro i j
  have h1 := rowSum_mul_right_zero ((1 - meanProj n) * B) (1 - meanProj n)
    rowSum_oneSubMeanProj i
  have h2 : ∑ k, ((1 - meanProj n) * B * (1 - meanProj n)) k j = 0 := by
    rw [Matrix.mul_assoc]
    exact colSum_mul_left_zero (1 - meanProj n) (B * (1 - meanProj n))
      colSum_oneSubMeanProj j
  rw [h1, h2]

/-- Commutation with every permutation matrix is entrywise conjugation
invariance. -/
theorem conj_invariance_of_comm {X : Matrix n n ℂ}
    (hcomm : ∀ σ : Equiv.Perm n, X * σ.permMatrix ℂ = σ.permMatrix ℂ * X)
    (σ : Equiv.Perm n) (a b : n) : X (σ a) (σ b) = X a b := by
  have h := congrFun (congrFun (hcomm σ) a) (σ b)
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  have hL : ∑ m, X a m * σ.permMatrix ℂ m (σ b) = X a b := by
    have hm : ∀ m : n, X a m * σ.permMatrix ℂ m (σ b)
        = if m = b then X a m else 0 := by
      intro m
      rw [permMatrix_entry]
      by_cases hmb : m = b
      · rw [if_pos (by rw [hmb]), if_pos hmb, mul_one]
      · rw [if_neg (fun hc => hmb (σ.injective hc)), if_neg hmb, mul_zero]
    rw [Finset.sum_congr rfl fun m _ => hm m,
      Finset.sum_ite_eq' Finset.univ b fun m => X a m,
      if_pos (Finset.mem_univ b)]
  have hR : ∑ m, σ.permMatrix ℂ a m * X m (σ b) = X (σ a) (σ b) := by
    have hm : ∀ m : n, σ.permMatrix ℂ a m * X m (σ b)
        = if σ a = m then X m (σ b) else 0 := by
      intro m
      rw [permMatrix_entry]
      by_cases hma : σ a = m
      · rw [if_pos hma, if_pos hma, one_mul]
      · rw [if_neg hma, if_neg hma, zero_mul]
    rw [Finset.sum_congr rfl fun m _ => hm m,
      Finset.sum_ite_eq Finset.univ (σ a) fun m => X m (σ b),
      if_pos (Finset.mem_univ _)]
  rw [hL, hR] at h
  exact h.symm

/-- **The permutation commutant**: a matrix commutes with every permutation matrix
iff it is a combination of the identity and the all-ones matrix. -/
theorem commutant_perm_iff (X : Matrix n n ℂ) :
    (∀ σ : Equiv.Perm n, X * σ.permMatrix ℂ = σ.permMatrix ℂ * X)
      ↔ ∃ α β : ℂ, X = α • (1 : Matrix n n ℂ) + β • jmat n := by
  constructor
  · intro hcomm
    have hinv := conj_invariance_of_comm hcomm
    rcases isEmpty_or_nonempty n with hn | hn
    · refine ⟨0, 0, ?_⟩
      ext a b
      exact (IsEmpty.false a).elim
    · obtain ⟨x⟩ := hn
      have hdiag : ∀ a : n, X a a = X x x := by
        intro a
        have h := hinv (Equiv.swap a x) a a
        rw [Equiv.swap_apply_left] at h
        exact h.symm
      by_cases hpair : ∃ y : n, y ≠ x
      · obtain ⟨y, hyx⟩ := hpair
        have hoff : ∀ a b : n, a ≠ b → X a b = X y x := by
          intro a b hab
          obtain ⟨σ, hσa, hσb⟩ := exists_perm_two_points hab hyx
          have h := hinv σ a b
          rw [hσa, hσb] at h
          exact h.symm
        refine ⟨X x x - X y x, X y x, ?_⟩
        ext a b
        rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
          Matrix.one_apply]
        by_cases hab : a = b
        · rw [if_pos hab, hab, hdiag b]
          simp [jmat]
        · rw [if_neg hab, hoff a b hab]
          simp [jmat]
      · -- singleton carrier
        have hsingle : ∀ a : n, a = x := by
          intro a
          by_contra hax
          exact hpair ⟨a, hax⟩
        refine ⟨X x x, 0, ?_⟩
        ext a b
        rw [hsingle a, hsingle b, Matrix.add_apply, Matrix.smul_apply,
          Matrix.smul_apply, Matrix.one_apply, if_pos rfl]
        simp [jmat]
  · rintro ⟨α, β, rfl⟩
    intro σ
    have hJP : jmat n * σ.permMatrix ℂ = jmat n := by
      ext a b
      rw [Matrix.mul_apply]
      calc ∑ m, jmat n a m * σ.permMatrix ℂ m b
          = ∑ m, σ.permMatrix ℂ m b :=
            Finset.sum_congr rfl fun m _ => by rw [jmat, one_mul]
        _ = 1 := colSum_permMatrix σ b
    have hPJ : σ.permMatrix ℂ * jmat n = jmat n := by
      ext a b
      rw [Matrix.mul_apply]
      calc ∑ m, σ.permMatrix ℂ a m * jmat n m b
          = ∑ m, σ.permMatrix ℂ a m :=
            Finset.sum_congr rfl fun m _ => by rw [jmat, mul_one]
        _ = 1 := rowSum_permMatrix σ a
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      hJP, hPJ]

end PermCommutant
end NCG
