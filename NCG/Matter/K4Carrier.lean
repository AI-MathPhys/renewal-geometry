/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The K₄ generation carrier (SM_emergence, graph cluster)

The rank-three circulation carrier `H¹(K₄;ℂ)` in concrete form —
antisymmetric divergence-free edge functions on the complete graph —
and the records riding on it:

* `K4Carrier`, `K4CarrierEquiv`, `finrank_K4Carrier` — the carrier
  is exactly three-dimensional (`b₁(K₄) = 3`), by the explicit
  parameterization `(α₀₁, α₀₂, α₁₂)`: the
  `corollary:conditional-generation-fibre-identification` count
  `dim_ℂ K_gen = 3`;
* `transfer_carrier_eigen` — `thm:family-wide-carrier`: the whole
  incidence-local covariant transfer family `T_{w,b}` acts on the
  carrier by the scalar `w - b`; for `B₀ = T_{1,0}` this exhibits
  the three-dimensional circulation sector inside `Ker(B₀ - 1)`
  (`thm:exact-amplitude-carrier`, eigenvalue-one part) and the
  injection direction of `thm:general-circulation-carrier`;
* `k4_fpf_involution`, `k3_no_fpf_involution`, `k4_selection` —
  `thm:k4-selection`: among complete simple graphs with a
  fixed-point-free involutive automorphism and nonzero first cycle
  rank, `K₄` has the fewest vertices, with `b₁(K₄) = 3`;
* `k4_constant_not_coboundary` — `lem:constant-bipartite-updated`
  (K₄ content): the constant sign class `[c]` is nonzero on `K₄`.
-/

namespace NCG

open Finset

/-! ## The carrier and its dimension -/

/-- The `K₄` circulation carrier: antisymmetric, divergence-free
edge functions — the concrete harmonic model of `H¹(K₄;ℂ)`. -/
def K4Carrier : Submodule ℂ (Fin 4 → Fin 4 → ℂ) where
  carrier := {α | (∀ i j, α j i = -α i j) ∧ ∀ i, ∑ k, α i k = 0}
  add_mem' := by
    rintro α β ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [Pi.add_apply]
      rw [ha1, hb1]
      ring
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, ha2, hb2, add_zero]
  zero_mem' := by
    refine ⟨fun i j => ?_, fun i => ?_⟩ <;> simp
  smul_mem' := by
    rintro c α ⟨ha1, ha2⟩
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [ha1]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum, ha2, mul_zero]

/-- The explicit antisymmetric divergence-free extension of the free
coordinates `(α₀₁, α₀₂, α₁₂)`. -/
def k4Fill (v : Fin 3 → ℂ) : Fin 4 → Fin 4 → ℂ := fun i j =>
  !![0, v 0, v 1, -v 0 - v 1;
     -v 0, 0, v 2, v 0 - v 2;
     -v 1, -v 2, 0, v 1 + v 2;
     v 0 + v 1, v 2 - v 0, -v 1 - v 2, 0] i j

theorem k4Fill_mem (v : Fin 3 → ℂ) : k4Fill v ∈ K4Carrier := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [k4Fill] <;> ring
  · fin_cases i <;>
      simp [k4Fill, Fin.sum_univ_four] <;> ring

/-- Diagonal entries of carrier elements vanish. -/
theorem K4Carrier.diag_zero {α : Fin 4 → Fin 4 → ℂ}
    (h : α ∈ K4Carrier) (i : Fin 4) : α i i = 0 := by
  have h1 := h.1 i i
  linear_combination h1 / 2

set_option linter.flexible false in
/-- **The carrier is exactly rank three**: the explicit linear
equivalence with `ℂ³` by the free coordinates
`(α₀₁, α₀₂, α₁₂)`. -/
noncomputable def K4CarrierEquiv : K4Carrier ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun α := ![α.1 0 1, α.1 0 2, α.1 1 2]
  map_add' α β := by
    funext i
    fin_cases i <;> simp
  map_smul' c α := by
    funext i
    fin_cases i <;> simp
  invFun v := ⟨k4Fill v, k4Fill_mem v⟩
  left_inv := by
    rintro ⟨α, hα⟩
    ext i j
    have h00 := K4Carrier.diag_zero hα 0
    have h11 := K4Carrier.diag_zero hα 1
    have h22 := K4Carrier.diag_zero hα 2
    have h33 := K4Carrier.diag_zero hα 3
    have hd0 := hα.2 0
    have hd1 := hα.2 1
    have hd2 := hα.2 2
    rw [Fin.sum_univ_four] at hd0 hd1 hd2
    have ha10 := hα.1 0 1
    have ha20 := hα.1 0 2
    have ha30 := hα.1 0 3
    have ha21 := hα.1 1 2
    have ha31 := hα.1 1 3
    have ha32 := hα.1 2 3
    fin_cases i <;> fin_cases j <;>
      simp only [k4Fill] <;>
      simp <;>
      first
        | linear_combination -h00
        | linear_combination -h11
        | linear_combination -h22
        | linear_combination -h33
        | linear_combination -ha10
        | linear_combination -ha20
        | linear_combination -ha21
        | linear_combination -hd0 + h00
        | linear_combination -hd1 + ha10 + h11
        | linear_combination -hd2 + ha20 + ha21 + h22
        | linear_combination -ha30 + hd0 - h00
        | linear_combination -ha31 + hd1 - ha10 - h11
        | linear_combination -ha32 + hd2 - ha20 - ha21 - h22
  right_inv v := by
    funext i
    fin_cases i <;> simp [k4Fill]

/-- `b₁(K₄) = 3`: the generation fibre
(`corollary:conditional-generation-fibre-identification`,
`dim_ℂ K_gen = 3`) is exactly three-dimensional. -/
theorem finrank_K4Carrier : Module.finrank ℂ K4Carrier = 3 := by
  rw [K4CarrierEquiv.finrank_eq]
  simp

/-! ## `thm:family-wide-carrier` -/

/-- The incidence-local covariant transfer family on oriented-edge
functions: weight `w` on nonbacktracking continuations, `b` on the
backtracking step. -/
def transferT (w b : ℂ) (f : Fin 4 → Fin 4 → ℂ) :
    Fin 4 → Fin 4 → ℂ := fun i j =>
  w * ∑ k, (if k ≠ i ∧ k ≠ j then f j k else 0) + b * f j i

/-- `thm:family-wide-carrier`: the whole transfer family acts on the
circulation carrier by the scalar `w - b` — an invariant
three-dimensional eigenspace for every `(w, b)`.  For the amplitude
nonbacktracking operator `B₀ = T_{1,0}` this is the canonical
circulation sector inside `Ker(B₀ - 1)`
(`thm:exact-amplitude-carrier`, eigenvalue-one part;
`thm:general-circulation-carrier`, injection direction). -/
theorem transfer_carrier_eigen (w b : ℂ)
    {α : Fin 4 → Fin 4 → ℂ} (hα : α ∈ K4Carrier) :
    transferT w b α = fun i j => (w - b) * α i j := by
  funext i j
  unfold transferT
  have hsplit : ∀ k : Fin 4, (if k ≠ i ∧ k ≠ j then α j k else 0)
      = α j k - (if k = i then α j k else 0)
        - (if k = j then α j k else 0)
        + (if k = i ∧ k = j then α j k else 0) := by
    intro k
    by_cases h1 : k = i <;> by_cases h2 : k = j <;>
      simp [h1, h2]
  have key : ∑ k, (if k ≠ i ∧ k ≠ j then α j k else 0)
      = -(α j i) + (if i = j then α j i else 0) := by
    rw [Finset.sum_congr rfl fun k _ => hsplit k]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
    rw [hα.2 j]
    rw [Finset.sum_ite_eq' Finset.univ i (α j),
      Finset.sum_ite_eq' Finset.univ j (α j)]
    have hlast : ∑ k, (if k = i ∧ k = j then α j k else 0)
        = if i = j then α j i else 0 := by
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        simp_rw [and_self]
        rw [Finset.sum_ite_eq' Finset.univ i (α i)]
        simp
      · rw [if_neg hij]
        apply Finset.sum_eq_zero
        intro k _
        by_cases h1 : k = i
        · subst h1
          simp [hij]
        · simp [h1]
    rw [hlast]
    rw [if_pos (Finset.mem_univ i), if_pos (Finset.mem_univ j)]
    rw [K4Carrier.diag_zero hα j]
    ring
  rw [key]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    rw [K4Carrier.diag_zero hα i]
    ring
  · rw [if_neg hij]
    rw [hα.1 i j]
    ring

/-! ## `thm:k4-selection` -/

/-- The first cycle rank of the complete simple graph `K_n`:
`b₁ = |E| - |V| + 1 = (n-1)(n-2)/2`. -/
def b1Complete (n : ℕ) : ℕ := (n - 1) * (n - 2) / 2

/-- `K₄` admits a fixed-point-free involutive automorphism, and its
cycle rank is `b₁(K₄) = 6 - 4 + 1 = 3 > 0`. -/
theorem k4_fpf_involution :
    (∃ f : Equiv.Perm (Fin 4), (∀ x, f (f x) = x) ∧ ∀ x, f x ≠ x) ∧
    b1Complete 4 = 3 := by
  constructor
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide, by decide⟩
  · decide

/-- `K₃` has cycle rank one but admits no fixed-point-free
involution (odd vertex count). -/
theorem k3_no_fpf_involution :
    ¬∃ f : Equiv.Perm (Fin 3), (∀ x, f (f x) = x) ∧ ∀ x, f x ≠ x := by
  decide

/-- `thm:k4-selection`: among complete simple graphs with both a
fixed-point-free involutive automorphism and nonzero first cycle
rank, `K₄` is the one with the fewest vertices: every `n < 4` fails
one of the two conditions, while `K₄` satisfies both with
`b₁(K₄) = 3`. -/
theorem k4_selection :
    (∀ n < 4, ¬((∃ f : Equiv.Perm (Fin n), Function.Involutive f
        ∧ ∀ x, f x ≠ x) ∧ 0 < b1Complete n)) ∧
    (∃ f : Equiv.Perm (Fin 4), (∀ x, f (f x) = x) ∧ ∀ x, f x ≠ x) ∧
    b1Complete 4 = 3 := by
  refine ⟨?_, k4_fpf_involution⟩
  intro n hn
  interval_cases n
  · rintro ⟨-, hb⟩
    simp [b1Complete] at hb
  · rintro ⟨⟨f, -, hfp⟩, -⟩
    exact hfp 0 (Subsingleton.elim _ _)
  · rintro ⟨-, hb⟩
    simp [b1Complete] at hb
  · rintro ⟨hf, -⟩
    exact k3_no_fpf_involution hf

/-! ## `lem:constant-bipartite-updated` (K₄ content) -/

/-- `lem:constant-bipartite-updated`: the constant edge cochain on
`K₄` is not a coboundary — `[c] ≠ 0`, because `K₄` contains odd
cycles (is not bipartite).  A coboundary would be a two-colouring
`g` with `g i + g j = 1` on every edge. -/
theorem k4_constant_not_coboundary :
    ¬∃ g : Fin 4 → ZMod 2, ∀ i j : Fin 4, i ≠ j → g i + g j = 1 := by
  decide

end NCG
