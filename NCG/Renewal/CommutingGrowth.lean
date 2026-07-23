/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Polynomial growth in the cancellative commuting regime

**Theorem `thm:commuting`** (lattice-cone counting core): for commuting
channels the accumulated channel depends only on the exponent vector,
and in the free cancellative case the number of predictive classes of
degree `≤ R` is the number of lattice points `{n ∈ ℕ^c : Σ n_i ≤ R}`,
which grows like `R^c`:

`(⌊R/c⌋ + 1)^c ≤ N(R) ≤ (R + 1)^c`

(`NCG.le_latticeShellCard`, `NCG.latticeShellCard_le`), so the growth
exponent is `q_alg = r_mon = c`.  (The reduction of a general
cancellative finitely generated affine semigroup to full-dimensional
lattice-cone counting is not formalised.)

**Definition `def:renewal-exponent`** is encoded as the specification
`0 < α ≤ 1` with the pole regime `α = 1`
(`NCG.IsRenewalExponent`). -/

namespace NCG

/-- The lattice shell `{n ∈ ℕ^c : Σ nᵢ ≤ R}` — predictive classes of
quotient degree `≤ R` in the free commuting regime
(Theorem `thm:commuting`). -/
noncomputable def latticeShellCard (c R : ℕ) : ℕ :=
  Nat.card {n : Fin c → ℕ // ∑ i, n i ≤ R}

/-- **Theorem `thm:commuting`, upper bound**: `N(R) ≤ (R+1)^c` — each
coordinate of a degree-`≤ R` exponent vector is at most `R`. -/
theorem latticeShellCard_le (c R : ℕ) :
    latticeShellCard c R ≤ (R + 1) ^ c := by
  have hinj : Function.Injective
      (fun n : {n : Fin c → ℕ // ∑ i, n i ≤ R} =>
        (fun i => (⟨n.1 i, by
          have hle : n.1 i ≤ ∑ j, n.1 j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le _)
              (Finset.mem_univ i)
          have := n.2
          omega⟩ : Fin (R + 1))) : _ → (Fin c → Fin (R + 1))) := by
    intro a b hab
    apply Subtype.ext
    funext i
    have := congrFun hab i
    exact congrArg Fin.val this
  calc latticeShellCard c R
      ≤ Nat.card (Fin c → Fin (R + 1)) :=
        Nat.card_le_card_of_injective _ hinj
    _ = (R + 1) ^ c := by
        simp [Nat.card_eq_fintype_card]

/-- **Theorem `thm:commuting`, lower bound**: `(⌊R/c⌋+1)^c ≤ N(R)` —
vectors with every coordinate at most `⌊R/c⌋` have total degree
`≤ R`. -/
theorem le_latticeShellCard (c R : ℕ) :
    (R / c + 1) ^ c ≤ latticeShellCard c R := by
  have hinj : Function.Injective
      (fun g : Fin c → Fin (R / c + 1) =>
        (⟨fun i => (g i).val, by
          calc ∑ i, (g i).val ≤ ∑ _i : Fin c, R / c :=
                Finset.sum_le_sum fun i _ =>
                  Nat.lt_succ_iff.mp (g i).2
            _ = c * (R / c) := by
                rw [Finset.sum_const, Finset.card_univ,
                  Fintype.card_fin, smul_eq_mul]
            _ ≤ R := by
                rw [mul_comm]
                exact Nat.div_mul_le_self R c⟩ :
          {n : Fin c → ℕ // ∑ i, n i ≤ R})) := by
    intro a b hab
    funext i
    have := congrFun (congrArg Subtype.val hab) i
    exact Fin.val_injective this
  have hfin : Finite {n : Fin c → ℕ // ∑ i, n i ≤ R} := by
    have hinj2 : Function.Injective
        (fun n : {n : Fin c → ℕ // ∑ i, n i ≤ R} =>
          (fun i => (⟨n.1 i, by
            have hle : n.1 i ≤ ∑ j, n.1 j :=
              Finset.single_le_sum (fun j _ => Nat.zero_le _)
                (Finset.mem_univ i)
            have := n.2
            omega⟩ : Fin (R + 1))) : _ → (Fin c → Fin (R + 1))) := by
      intro a b hab
      apply Subtype.ext
      funext i
      have := congrFun hab i
      exact congrArg Fin.val this
    exact Finite.of_injective _ hinj2
  calc (R / c + 1) ^ c
      = Nat.card (Fin c → Fin (R / c + 1)) := by
        simp [Nat.card_eq_fintype_card]
    _ ≤ latticeShellCard c R :=
        Nat.card_le_card_of_injective _ hinj

/-- **Definition `def:renewal-exponent`** (specification): the renewal
exponent lies in `(0, 1]`, with `α = 1` the finite-mean pole regime and
`α ∈ (0,1)` the regularly varying branch regime. -/
def IsRenewalExponent (α : ℝ) : Prop := 0 < α ∧ α ≤ 1

/-- The pole regime realises the boundary exponent. -/
theorem isRenewalExponent_one : IsRenewalExponent 1 := by
  constructor <;> norm_num

end NCG
