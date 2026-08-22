/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Two-stage localizer flatness: the action–Krylov chain

Exact finite-dimensional encoding of `cor:GT-two-stage-localizer-flatness`.

For a symmetric localizer `T` on a finite-dimensional inner product space and
the physical source range `V`, the Krylov spaces
`krylov T V n = span{T^j V : j < n}` satisfy:

* `krylov_mono`: the chain is increasing, `K_{n+1} = K_n ⊔ T^n V` by
  definition, and `K_{n+1} = K_n ⊔ T(K_n)` for `n ≥ 1` (`krylov_succ_eq_sup_map`);
* `krylov_stable_of_eq`: at an equality `K_{n+1} = K_n` the space `K_n`
  is `T`-invariant and the chain is constant from `n` on (`krylov_eq_of_stable`);
* `exists_stable_index`: the chain stabilizes after at most `finrank E + 1`
  steps (each strict increase raises the dimension);
* `invariant_orthogonal_of_symmetric` / `krylov_reduces`: a `T`-invariant
  subspace of a symmetric `T` is reducing;
* `krylov_minimal` / `krylov_stable_eq_minimal`: the stabilized Krylov space is
  the least `T`-invariant subspace containing the source — the complete
  localizer carrier visible from the source;
* `increment_zero_iff`: the dimension increment `finrank K_{n+1} - finrank K_n`
  vanishes exactly at a stable index.

The rank of the leakage Gram at each stage equals the dimension of the new
Krylov component: this is `thm:universal-moment-leakage`
(`NCG.universal_moment_leakage`, proved) in whitened coordinates.
-/

open Submodule

namespace NCG
namespace KrylovLocalizerFlatness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Krylov space `K_n = span{T^j V : 0 ≤ j < n}`, built recursively. -/
def krylov (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) : ℕ → Submodule ℂ E
  | 0 => ⊥
  | n + 1 => krylov T V n ⊔ V.map (T ^ n)

@[simp] theorem krylov_zero (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) : krylov T V 0 = ⊥ := rfl

theorem krylov_succ (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) (n : ℕ) :
    krylov T V (n + 1) = krylov T V n ⊔ V.map (T ^ n) := rfl

theorem map_pow_zero (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) : V.map (T ^ 0) = V := by
  rw [pow_zero, Module.End.one_eq_id, Submodule.map_id]

theorem krylov_one (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) : krylov T V 1 = V := by
  rw [krylov_succ, krylov_zero, bot_sup_eq, map_pow_zero]

theorem krylov_mono (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) : Monotone (krylov T V) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [krylov_succ]
  exact le_sup_left

theorem map_pow_le_krylov (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) {j n : ℕ} (hj : j < n) :
    V.map (T ^ j) ≤ krylov T V n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [krylov_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact le_trans (ih h) le_sup_left
    · subst h; exact le_sup_right

theorem source_le_krylov (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) {n : ℕ} (hn : 1 ≤ n) :
    V ≤ krylov T V n := by
  have := map_pow_le_krylov T V (j := 0) (n := n) hn
  rwa [map_pow_zero] at this

theorem map_pow_succ (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) (j : ℕ) :
    V.map (T ^ (j + 1)) = (V.map (T ^ j)).map T := by
  rw [pow_succ', Module.End.mul_eq_comp, Submodule.map_comp]

/-- `T(K_n) ≤ K_{n+1}`. -/
theorem map_krylov_le_succ (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) (n : ℕ) :
    (krylov T V n).map T ≤ krylov T V (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [krylov_succ, Submodule.map_sup, ← map_pow_succ]
    exact sup_le (le_trans ih (krylov_mono T V (Nat.le_succ _)))
      (map_pow_le_krylov T V (Nat.lt_succ_self _))

/-- `K_{n+1} = K_n ⊔ T(K_n)` for `n ≥ 1`. -/
theorem krylov_succ_eq_sup_map (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) {n : ℕ} (hn : 1 ≤ n) :
    krylov T V (n + 1) = krylov T V n ⊔ (krylov T V n).map T := by
  apply le_antisymm
  · rw [krylov_succ]
    refine sup_le le_sup_left (le_trans ?_ le_sup_right)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [map_pow_succ]
    exact Submodule.map_mono (map_pow_le_krylov T V (Nat.lt_succ_self m))
  · exact sup_le (krylov_mono T V (Nat.le_succ n)) (map_krylov_le_succ T V n)

/-- **Minimality**: a `T`-invariant subspace containing the source contains every
Krylov space. -/
theorem krylov_minimal (T : E →ₗ[ℂ] E) (V M : Submodule ℂ E) (hV : V ≤ M)
    (hinv : M.map T ≤ M) (n : ℕ) : krylov T V n ≤ M := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [krylov_succ]
    refine sup_le ih ?_
    clear ih
    induction n with
    | zero => rwa [map_pow_zero]
    | succ j ihj =>
      rw [map_pow_succ]
      exact le_trans (Submodule.map_mono ihj) hinv

/-- **Stabilization**: at an equality `K_{n+1} = K_n` (`n ≥ 1`) the Krylov space
is `T`-invariant. -/
theorem krylov_stable_of_eq (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) {n : ℕ} (hn : 1 ≤ n)
    (heq : krylov T V (n + 1) = krylov T V n) : (krylov T V n).map T ≤ krylov T V n :=
  calc (krylov T V n).map T ≤ krylov T V n ⊔ (krylov T V n).map T := le_sup_right
    _ = krylov T V (n + 1) := (krylov_succ_eq_sup_map T V hn).symm
    _ = krylov T V n := heq

/-- After stabilization the chain is constant. -/
theorem krylov_eq_of_stable (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) {n : ℕ} (hn : 1 ≤ n)
    (heq : krylov T V (n + 1) = krylov T V n) {m : ℕ} (hm : n ≤ m) :
    krylov T V m = krylov T V n :=
  le_antisymm
    (krylov_minimal T V (krylov T V n) (source_le_krylov T V hn)
      (krylov_stable_of_eq T V hn heq) m)
    (krylov_mono T V hm)

/-- **Termination**: the chain stabilizes at some `1 ≤ n ≤ finrank E + 1`. -/
theorem exists_stable_index [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) :
    ∃ n, 1 ≤ n ∧ n ≤ Module.finrank ℂ E + 1 ∧ krylov T V (n + 1) = krylov T V n := by
  by_contra hcon
  push Not at hcon
  have hstrict : ∀ n, 1 ≤ n → n ≤ Module.finrank ℂ E + 1 →
      krylov T V n < krylov T V (n + 1) :=
    fun n h1 h2 => lt_of_le_of_ne (krylov_mono T V (Nat.le_succ n)) (Ne.symm (hcon n h1 h2))
  have hgrow : ∀ k, k ≤ Module.finrank ℂ E + 1 →
      k ≤ Module.finrank ℂ (krylov T V (k + 1)) := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := Submodule.finrank_lt_finrank_of_lt (hstrict (k + 1) (by omega) hk)
      omega
  have := hgrow (Module.finrank ℂ E + 1) le_rfl
  have hle := Submodule.finrank_le (krylov T V (Module.finrank ℂ E + 1 + 1))
  omega

/-- **Reducing**: a `T`-invariant subspace of a symmetric `T` has `T`-invariant
orthogonal complement. -/
theorem invariant_orthogonal_of_symmetric (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (M : Submodule ℂ E) (hinv : M.map T ≤ M) : Mᗮ.map T ≤ Mᗮ := by
  rintro _ ⟨v, hv, rfl⟩
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← hT u v]
  exact (Submodule.mem_orthogonal M v).mp hv (T u) (hinv ⟨u, hu, rfl⟩)

/-- At stabilization the Krylov carrier reduces the symmetric localizer. -/
theorem krylov_reduces (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (V : Submodule ℂ E) {n : ℕ}
    (hn : 1 ≤ n) (heq : krylov T V (n + 1) = krylov T V n) :
    (krylov T V n).map T ≤ krylov T V n ∧ (krylov T V n)ᗮ.map T ≤ (krylov T V n)ᗮ :=
  ⟨krylov_stable_of_eq T V hn heq,
    invariant_orthogonal_of_symmetric T hT _ (krylov_stable_of_eq T V hn heq)⟩

/-- The stabilized Krylov carrier is the least `T`-invariant subspace containing
the source: every localizer moment visible from the source lies in it, and it
is contained in every invariant carrier of the source. -/
theorem krylov_stable_eq_minimal (T : E →ₗ[ℂ] E) (V : Submodule ℂ E) {n : ℕ} (hn : 1 ≤ n)
    (heq : krylov T V (n + 1) = krylov T V n) :
    (∀ j, V.map (T ^ j) ≤ krylov T V n) ∧
      ∀ M : Submodule ℂ E, V ≤ M → M.map T ≤ M → krylov T V n ≤ M := by
  refine ⟨fun j => ?_, fun M hV hinv => krylov_minimal T V M hV hinv n⟩
  calc V.map (T ^ j) ≤ krylov T V (j + 1) := map_pow_le_krylov T V (Nat.lt_succ_self j)
    _ ≤ krylov T V (max n (j + 1)) := krylov_mono T V (le_max_right _ _)
    _ = krylov T V n := krylov_eq_of_stable T V hn heq (le_max_left _ _)

/-- The dimension increment at stage `n` (the dimension of the new Krylov
component) vanishes exactly at a stable index. -/
theorem increment_zero_iff [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (V : Submodule ℂ E)
    (n : ℕ) :
    Module.finrank ℂ (krylov T V (n + 1)) = Module.finrank ℂ (krylov T V n) ↔
      krylov T V (n + 1) = krylov T V n := by
  constructor
  · intro h
    exact (Submodule.eq_of_le_of_finrank_eq (krylov_mono T V (Nat.le_succ n)) h.symm).symm
  · intro h
    rw [h]

end KrylovLocalizerFlatness
end NCG
