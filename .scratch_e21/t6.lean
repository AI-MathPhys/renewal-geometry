import Mathlib
abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ
def jetBasis (lam : Fin 4) (i j : Fin 4) : Fin 4 → Mat := Pi.single lam (Matrix.single i j 1)
theorem jet_expand (q : Fin 4 → Mat) :
    q = ∑ lam, ∑ i, ∑ j, q lam i j • jetBasis lam i j := by
  funext lam' a b
  simp [jetBasis, Finset.sum_apply, Pi.single_apply]
  rw [← Matrix.matrix_eq_sum_single]
