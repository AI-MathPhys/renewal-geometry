import NCG.Grand.ZetaIncidence

/-! # universal characterization of the zeta history -/

open Matrix

namespace NCG

/-- `thm:ar-zeta-incidence`, uniqueness clause.  The endpoint-corner rule
determines every matrix coefficient, hence determines the zeta history even
among all matrices (and therefore in the forward algebra). -/
theorem zetaX_unique_of_corners {X : ℕ}
    (Z : Matrix (Fin X) (Fin X) ℂ)
    (hcorner : ∀ m b : Fin X,
      Matrix.single m m (1 : ℂ) * Z * Matrix.single b b (1 : ℂ)
        = if ((b : ℕ) + 1) ∣ ((m : ℕ) + 1)
          then Matrix.single m b (1 : ℂ) else 0) :
    Z = zetaX X := by
  ext m b
  have h := congrArg (fun M : Matrix (Fin X) (Fin X) ℂ => M m b)
    (hcorner m b)
  rw [zetaX, Matrix.of_apply]
  by_cases hd : ((b : ℕ) + 1) ∣ ((m : ℕ) + 1)
  · simpa [Matrix.mul_apply, Matrix.single_apply, hd] using h
  · simpa [Matrix.mul_apply, Matrix.single_apply, hd] using h

end NCG
