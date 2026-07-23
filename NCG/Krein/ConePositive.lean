/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.PolyhedralObstruction

/-!
# Cone-positive unitaries are permutations

**Lemma `lem:cone-positive-permutation`**: a unitary between renewal
fibres carrying the simplicial renewal cone onto the renewal cone permutes
the distinguished renewal basis.  This is the rigidity input for the
minimal-rank classification of signed enrichments
(Lemma `lem:minimal-rank-two`, Theorem `thm:classification`): at rank two
it leaves exactly the two permutation matrices `I` and `S`, reducing the
structure group to `{I,S} ≅ ℤ/2`.

The proof is pure extreme-ray combinatorics on top of
`NCG.isExtremeDir_orthant_iff` (the simplicial cone `[0,∞)^n` has exactly
the basis rays as extreme rays, `NCG/Lorentz/PolyhedralObstruction.lean`):
a cone automorphism sends each basis vector to a *positive multiple* of a
basis vector, and norm preservation forces the multiple to be `1`.

## Main result

* `NCG.conePositive_perm` — **Lemma `lem:cone-positive-permutation`**.
-/

namespace NCG

/-- **Lemma `lem:cone-positive-permutation`** (cone-positive unitaries are
permutations): a linear automorphism of `ℝⁿ` that carries the simplicial
renewal cone `[0,∞)ⁿ` onto itself and preserves norms permutes the
distinguished renewal basis `(eᵢ)`. -/
theorem conePositive_perm {n : ℕ} (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hT : T '' orthant n = orthant n) (hnorm : ∀ x, ‖T x‖ = ‖x‖) :
    ∃ π : Equiv.Perm (Fin n),
      ∀ i, T (Pi.single i 1) = Pi.single (π i) 1 := by
  have hex : ∀ i : Fin n, ∃ j : Fin n, ∃ t : ℝ, 0 < t ∧
      T (Pi.single i 1) = t • Pi.single j 1 := by
    intro i
    have h1 : IsExtremeDir (orthant n) (Pi.single i (1 : ℝ)) :=
      isExtremeDir_orthant_iff.mpr ⟨i, 1, one_pos, (one_smul ℝ _).symm⟩
    have h2 := h1.map T
    rw [hT] at h2
    exact isExtremeDir_orthant_iff.mp h2
  choose g t ht hg using hex
  have ht1 : ∀ i, t i = 1 := by
    intro i
    have hni := hnorm (Pi.single i 1)
    rw [hg i, norm_smul, Real.norm_eq_abs, abs_of_pos (ht i),
      Pi.norm_single, Pi.norm_single, norm_one, mul_one] at hni
    exact hni
  have hginj : Function.Injective g := by
    intro i j hij
    have h1 : T (Pi.single i 1) = T (Pi.single j 1) := by
      rw [hg i, hg j, ht1 i, ht1 j, hij]
    have h2 := T.injective h1
    by_contra hne
    have h3 := congrFun h2 i
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h3
    exact one_ne_zero h3
  refine ⟨Equiv.ofBijective g
    (Finite.injective_iff_bijective.mp hginj), fun i => ?_⟩
  rw [Equiv.ofBijective_apply, hg i, ht1 i, one_smul]

end NCG
