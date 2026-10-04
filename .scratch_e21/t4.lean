import Mathlib
theorem dirac_form_aux (v : ℝ) (a b c d : Fin 4 → ℂ) (m : ℂ) :
    v * (Complex.I / 2 * ∑ μ, (a μ + b μ - (c μ + d μ)) - m).re =
      (∑ μ, ((Complex.I / 2 * ((v : ℂ) * a μ)).re + (Complex.I / 2 * ((v : ℂ) * b μ)).re -
        (Complex.I / 2 * ((v : ℂ) * c μ)).re - (Complex.I / 2 * ((v : ℂ) * d μ)).re)) -
        (1 * ((v : ℂ) * m)).re := by
  have k1 : ∀ w : ℂ, (Complex.I / 2 * w).re = -(w.im / 2) := fun w => by
    simp [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im]
  have k2 : ∀ w : ℂ, ((v : ℂ) * w).im = v * w.im := fun w => by simp [Complex.mul_im]
  have k3 : ∀ w : ℂ, (1 * ((v : ℂ) * w)).re = v * w.re := fun w => by simp [Complex.mul_re]
  simp only [Complex.sub_re, k1, k2, k3, Complex.im_sum, Complex.add_im, Complex.sub_im,
    Fin.sum_univ_four]
  ring
