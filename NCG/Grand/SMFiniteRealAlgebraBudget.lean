/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Matter.FiniteAlgebra

/-!
# Renewal-admissible finite real algebra
  (`thm:SM-finite-real-algebra`, Gran-Tensor manuscript)

* `sm_finite_real_algebra_budget`: the budget derivation —
  for Wedderburn block data `L` (blocks `M_n(D)` with `D`
  one of `ℝ, ℂ, ℍ` by Frobenius, encoded as
  `DivType × ℕ`), IF
  (i) there are at most three charged central summands
      (`L.length ≤ 3`),
  (ii) the total non-scalar real dimension is at most
      `22` (a block is scalar exactly when it is
      commutative, i.e. `M₁(ℝ)` or `M₁(ℂ)`),
  (iii) `L` contains an independent complex scalar factor
      `ℂ = M₁(ℂ)`,
  (iv) `L` contains a quaternionic factor `M_m(ℍ)`
      (`m ≥ 1`), and
  (v) `L` contains a genuinely complex colour factor
      `M_n(ℂ)` of rank `n ≥ 3`,
  THEN the budget forces `m = 1` and `n = 3`, and `L` is
  a permutation of the boxed
  `𝒜_F^ch ≅ ℂ ⊕ ℍ ⊕ M₃(ℂ)` —
  exactly the manuscript's argument
  (`4m² + 2n² ≤ 22` with `n ≥ 3` forces `m = 1`, `n = 3`,
  and the three-summand bound leaves no room for more).

The identification of abstract charged summands with
Wedderburn blocks over `ℝ, ℂ, ℍ` is the Frobenius /
real Artin–Wedderburn layer
(`NCG/Matter/FiniteAlgebra.lean` and the real
classification files); the pseudoreal-doublet and
faithful-colour typing of the hypotheses is the
manuscript's bimodule layer.
-/

namespace NCG

/-- Non-scalar real dimension of a Wedderburn block:
zero for the commutative blocks `M₁(ℝ)` and `M₁(ℂ)`,
the full real dimension otherwise. -/
def nonScalarBlockDim (b : DivType × ℕ) : ℕ :=
  if b.2 = 1 ∧ (b.1 = DivType.R ∨ b.1 = DivType.C)
  then 0 else blockDim b

/-- `thm:SM-finite-real-algebra` (the budget
derivation of the boxed block list). -/
theorem sm_finite_real_algebra_budget
    (L : List (DivType × ℕ)) (m n : ℕ)
    -- (i) at most three charged central summands
    (hlen : L.length ≤ 3)
    -- (ii) non-scalar real-dimension budget 22
    (hdim : (L.map nonScalarBlockDim).sum ≤ 22)
    -- (iii) independent complex scalar factor
    (hC : (DivType.C, 1) ∈ L)
    -- (iv) quaternionic factor
    (hm : 1 ≤ m) (hH : (DivType.H, m) ∈ L)
    -- (v) genuinely complex colour factor of rank ≥ 3
    (hn : 3 ≤ n) (hCol : (DivType.C, n) ∈ L) :
    m = 1 ∧ n = 3 ∧ L.Perm canonicalBlocks := by
  -- the three demanded elements are pairwise distinct
  have hne1 : (DivType.C, 1) ≠ (DivType.H, m) := by
    simp
  have hne2 : ((DivType.C, 1) : DivType × ℕ)
      ≠ (DivType.C, n) := by
    simp only [ne_eq, Prod.mk.injEq, true_and]
    omega
  have hne3 : ((DivType.H, m) : DivType × ℕ)
      ≠ (DivType.C, n) := by
    simp
  -- so the candidate list subpermutes into `L` …
  have hsub : List.Subperm
      [(DivType.C, 1), (DivType.H, m),
        (DivType.C, n)] L := by
    apply List.subperm_of_subset
    · simp [List.nodup_cons, hne1, hne2, hne3]
    · intro x hx
      simp only [List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hC
      · exact hH
      · exact hCol
  -- … and the length bound upgrades it to a permutation
  have hperm : L.Perm
      [(DivType.C, 1), (DivType.H, m),
        (DivType.C, n)] := by
    have hlen' : L.length ≤
        ([(DivType.C, 1), (DivType.H, m),
          (DivType.C, n)] : List (DivType × ℕ)).length := by
      simpa using hlen
    exact (hsub.perm_of_length_le hlen').symm
  -- transport the budget through the permutation
  have hsum : (L.map nonScalarBlockDim).sum
      = 4 * m ^ 2 + 2 * n ^ 2 := by
    have := ((hperm.map nonScalarBlockDim).sum_eq)
    rw [this]
    simp [nonScalarBlockDim, blockDim, DivType.dim,
      (show ¬ n = 1 by omega)]
    ring
  rw [hsum] at hdim
  -- the manuscript's arithmetic: `m = 1`, `n = 3`
  have hm1 : m = 1 := by nlinarith
  have hn3 : n = 3 := by nlinarith
  subst hm1 hn3
  exact ⟨rfl, rfl, hperm⟩

end NCG
