/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Relative action–unit holonomy and residual writer
  selection (`thm:SMST-relative-writer-selection`,
  Gran-Tensor manuscript)

* `smst_relative_writer_selection`: for the holonomy
  writers `𝒮_γ(B) = P_γB - BT_γ` and the positive
  holonomy action
  `⟨B, L^hol B⟩ = ∑_γ a_γ‖𝒮_γ(B)‖²_F` with positive
  weights,
  (i) the holonomy action is a nonnegative quadratic form
      on the writer fibre; and
  (ii) the boxed SMW.9 kernel identification — the action
      vanishes exactly on the flat intertwiner
      orientations,
      `Ker L^hol = Hom_Hol(E^a, E^u)`
      (`𝒮_γ(B) = 0` for every cycle, i.e.
      `P_γB = BT_γ`).

The boxed SMW.8 three-way orthogonal split of the writer
fibre (Read-forced ⊕ holonomy-nonflat ⊕ flat), the pricing
of the nonflat term by the holonomy action, and the
word-level residual gate (`thm:GT-monoidal-transport`) on
the actual scalar contractions are the manuscript's
selection layer.
-/

open Matrix Finset

namespace NCG

/-- `thm:SMST-relative-writer-selection` (SMW.7 positivity
and the boxed SMW.9 kernel identification). -/
theorem smst_relative_writer_selection {G : Type}
    [Fintype G] {n m : Type} [Fintype n] [Fintype m]
    (P : G → Matrix n n ℂ) (T : G → Matrix m m ℂ)
    (a : G → ℝ) (ha : ∀ g, 0 < a g)
    (B : Matrix n m ℂ) :
    -- (i) the holonomy action is nonnegative
    (0 ≤ ∑ g, a g * ∑ i, ∑ j,
      Complex.normSq ((P g * B - B * T g) i j))
    -- (ii) the boxed SMW.9: zero action ⟺ flat
    -- intertwiner
    ∧ ((∑ g, a g * ∑ i, ∑ j,
        Complex.normSq ((P g * B - B * T g) i j)) = 0
      ↔ ∀ g, P g * B = B * T g) := by
  have hterm : ∀ g, 0 ≤ ∑ i, ∑ j,
      Complex.normSq ((P g * B - B * T g) i j) :=
    fun g => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ =>
        Complex.normSq_nonneg _
  constructor
  · exact Finset.sum_nonneg fun g _ =>
      mul_nonneg (ha g).le (hterm g)
  · constructor
    · intro hzero g
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun g _ => mul_nonneg (ha g).le
          (hterm g))).mp hzero g (Finset.mem_univ g)
      have hg : ∑ i, ∑ j, Complex.normSq
          ((P g * B - B * T g) i j) = 0 := by
        rcases mul_eq_zero.mp hall with h | h
        · exact absurd h (ne_of_gt (ha g))
        · exact h
      have hentries : ∀ i j,
          (P g * B - B * T g) i j = 0 := by
        intro i j
        have hrow := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => Finset.sum_nonneg fun j _ =>
            Complex.normSq_nonneg _)).mp hg i
          (Finset.mem_univ i)
        have hij := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => Complex.normSq_nonneg _)).mp
          hrow j (Finset.mem_univ j)
        exact Complex.normSq_eq_zero.mp hij
      have hmat : P g * B - B * T g = 0 := by
        ext i j
        exact hentries i j
      exact sub_eq_zero.mp hmat
    · intro hflat
      apply Finset.sum_eq_zero
      intro g _
      rw [show P g * B - B * T g = 0 from by
        rw [hflat g, sub_self]]
      simp

end NCG
