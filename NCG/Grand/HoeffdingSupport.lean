/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Complete interaction tangent of independent primitive cells
  (`thm:primitive-Hoeffding-support`, Gran-Tensor manuscript)

For complementary conditional-expectation projections `E`
(onto constants) and `Q = I - E` (score bank, dimension 3)
in each of four independent cells, with Hoeffding projections
`P_A = ⊗_{i∈A} Q ⊗_{i∉A} E` indexed by Boolean masks:

* `primitive_hoeffding_support`:
  (i) mutual orthogonality `P_A P_B = 0` for `A ≠ B`;
  (ii) resolution of the identity `∑_A P_A = I`
      (the boxed Hoeffding decomposition);
  (iii) support-order dimensions
      `dim Ran P_A = tr P_A = 3^{|A|}`;
  (iv) the boxed dimension table
      `|A| = 2 : 6·9 = 54`, `|A| = 3 : 4·27 = 108`,
      `|A| = 4 : 81`, total interaction dimension
      `54 + 108 + 81 = 243`;
  (v) the two-cell connected tangent
      `tr (Q ⊗ Q) = 9` (`ℐ_conn ≅ ℐ_br ⊗ ℐ_br`).

* `hoeffding_frame_window`: the boxed tensor frame window —
  a spectral window `a·I ⪯ G ⪯ I` tensorizes to
  `a²·I ⪯ G ⊗ G ⪯ I` (instantiated at `a = 176/225` by the
  manuscript's cell Gram `G₀`).

The identification of `E, Q` as the concrete conditional
expectations of the primitive renewal cell (and of `3` as
the score-bank dimension) is the previously proved one-cell
layer; independence tensorizes the Gram, which is clause
(v) plus `hoeffding_frame_window`.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace NCG

/-- Choose `Q` (mask bit set) or `E` in one Hoeffding
factor. -/
def hoeffPick {d : Type*} (E Q : Matrix d d ℂ) :
    Bool → Matrix d d ℂ :=
  fun b => bif b then Q else E

/-- Four-cell Hoeffding projection for a Boolean mask. -/
def hoeffP {d : Type*} (E Q : Matrix d d ℂ)
    (m : Bool × Bool × Bool × Bool) :
    Matrix (d × d × d × d) (d × d × d × d) ℂ :=
  hoeffPick E Q m.1 ⊗ₖ (hoeffPick E Q m.2.1
    ⊗ₖ (hoeffPick E Q m.2.2.1 ⊗ₖ hoeffPick E Q m.2.2.2))

/-- Support order `|A|` of a Boolean mask. -/
def hoeffCount (m : Bool × Bool × Bool × Bool) : ℕ :=
  (cond m.1 1 0) + (cond m.2.1 1 0) + (cond m.2.2.1 1 0)
    + (cond m.2.2.2 1 0)

/-- `thm:primitive-Hoeffding-support`. -/
theorem primitive_hoeffding_support {d : Type} [Fintype d]
    [DecidableEq d] (E Q : Matrix d d ℂ)
    (hEQ : E + Q = 1) (hEQ0 : E * Q = 0) (hQE0 : Q * E = 0)
    (hEtr : E.trace = 1) (hQtr : Q.trace = 3) :
    -- (i) mutual orthogonality
    (∀ m m' : Bool × Bool × Bool × Bool, m ≠ m' →
      hoeffP E Q m * hoeffP E Q m' = 0)
    -- (ii) resolution of the identity
    ∧ (∑ m : Bool × Bool × Bool × Bool, hoeffP E Q m = 1)
    -- (iii) support-order dimensions
    ∧ (∀ m : Bool × Bool × Bool × Bool,
        (hoeffP E Q m).trace = 3 ^ hoeffCount m)
    -- (iv) the boxed dimension table
    ∧ ((Finset.univ.filter
          (fun m : Bool × Bool × Bool × Bool =>
            hoeffCount m = 2)).card * 3 ^ 2 = 54
        ∧ (Finset.univ.filter
            (fun m : Bool × Bool × Bool × Bool =>
              hoeffCount m = 3)).card * 3 ^ 3 = 108
        ∧ (Finset.univ.filter
            (fun m : Bool × Bool × Bool × Bool =>
              hoeffCount m = 4)).card * 3 ^ 4 = 81
        ∧ 54 + 108 + 81 = 243)
    -- (v) the two-cell connected tangent
    ∧ (Q ⊗ₖ Q).trace = 9 := by
  have pickOrth : ∀ {b b' : Bool}, b ≠ b' →
      hoeffPick E Q b * hoeffPick E Q b' = 0 := by
    intro b b' h
    cases b <;> cases b' <;> simp_all [hoeffPick]
  refine ⟨?_, ?_, ?_, ⟨by decide, by decide, by decide,
    by norm_num⟩, ?_⟩
  · intro m m' hne
    obtain ⟨a1, a2, a3, a4⟩ := m
    obtain ⟨b1, b2, b3, b4⟩ := m'
    simp only [hoeffP]
    rw [← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    by_cases h1 : a1 = b1
    · by_cases h2 : a2 = b2
      · by_cases h3 : a3 = b3
        · by_cases h4 : a4 = b4
          · subst h1; subst h2; subst h3; subst h4
            exact absurd rfl hne
          · rw [pickOrth h4, Matrix.kronecker_zero,
              Matrix.kronecker_zero, Matrix.kronecker_zero]
        · rw [pickOrth h3, Matrix.zero_kronecker,
            Matrix.kronecker_zero, Matrix.kronecker_zero]
      · rw [pickOrth h2, Matrix.zero_kronecker,
          Matrix.kronecker_zero]
    · rw [pickOrth h1, Matrix.zero_kronecker]
  · have hs : (∑ b : Bool, hoeffPick E Q b) = 1 := by
      rw [Fintype.sum_bool]
      simp only [hoeffPick, cond_true, cond_false]
      rw [add_comm]
      exact hEQ
    have pull : ∀ {x y z w : Type} [Fintype y]
        (M : Matrix x y ℂ) (g : Bool → Matrix z w ℂ),
        ∑ b : Bool, M ⊗ₖ g b
          = M ⊗ₖ ∑ b : Bool, g b := by
      intro x y z w _ M g
      rw [Fintype.sum_bool, Fintype.sum_bool,
        Matrix.kronecker_add]
    have pull' : ∀ {x y z w : Type} [Fintype y]
        (M : Matrix z w ℂ) (g : Bool → Matrix x y ℂ),
        ∑ b : Bool, g b ⊗ₖ M
          = (∑ b : Bool, g b) ⊗ₖ M := by
      intro x y z w _ M g
      rw [Fintype.sum_bool, Fintype.sum_bool,
        Matrix.add_kronecker]
    simp only [Fintype.sum_prod_type, hoeffP]
    simp only [pull, pull', hs, Matrix.one_kronecker_one]
  · intro m
    rcases m with ⟨a1, a2, a3, a4⟩
    cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;>
      simp [hoeffP, hoeffPick, hoeffCount,
        Matrix.trace_kronecker, hEtr, hQtr] <;>
      norm_num
  · rw [Matrix.trace_kronecker, hQtr]
    norm_num

/-- `thm:primitive-Hoeffding-support`, the boxed tensor
frame window `a²I ⪯ G ⊗ G ⪯ I`. -/
theorem hoeffding_frame_window {d : Type*} [Finite d]
    [DecidableEq d] (G : Matrix d d ℂ) (a : ℂ)
    (hG : G.PosSemidef) (ha : 0 ≤ a)
    (hlow : (G - a • 1).PosSemidef)
    (hup : ((1 : Matrix d d ℂ) - G).PosSemidef) :
    ((G ⊗ₖ G) - (a * a) • 1).PosSemidef
    ∧ ((1 : Matrix (d × d) (d × d) ℂ) - G ⊗ₖ G).PosSemidef := by
  constructor
  · have key : (G ⊗ₖ G) - (a * a)
        • (1 : Matrix (d × d) (d × d) ℂ)
        = (G - a • 1) ⊗ₖ G
          + a • ((1 : Matrix d d ℂ) ⊗ₖ (G - a • 1)) := by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, smul_eq_mul, Prod.mk.injEq]
      by_cases hik : i = k <;> by_cases hjl : j = l <;>
        simp [hik, hjl] <;> ring
    rw [key]
    exact (hlow.kronecker hG).add
      ((Matrix.PosSemidef.one.kronecker hlow).smul ha)
  · have key : (1 : Matrix (d × d) (d × d) ℂ) - G ⊗ₖ G
        = ((1 : Matrix d d ℂ) - G) ⊗ₖ G
          + (1 : Matrix d d ℂ)
            ⊗ₖ ((1 : Matrix d d ℂ) - G) := by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.sub_apply, Matrix.add_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply,
        Prod.mk.injEq]
      by_cases hik : i = k <;> by_cases hjl : j = l <;>
        simp [hik, hjl] <;> ring
    rw [key]
    exact (hup.kronecker hG).add
      (Matrix.PosSemidef.one.kronecker hup)

end NCG
