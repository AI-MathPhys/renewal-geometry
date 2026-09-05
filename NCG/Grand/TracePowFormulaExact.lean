/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.LiebPairingExact

/-!
# Eigenvalue formulas for the dyadic trace interpolation

Step (D4i) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: the two-sided spectral trace formula and
the eigenvalue expansion of `tracePow`.

* `trace_matFun_mul_matFun_re`:
  `Re Tr(f(ρ) g(σ)) = Σ_{ij} f(p_i) g(q_j) |W_{ij}|²`;
* `tracePow_eq_sum`: the eigenvalue expansion of the interpolation;
* `trace_re_eq_sum_eigenvalues`, `numerator_spread`: the entropy
  numerator as a doubly indexed sum.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ρ σ : Matrix n n ℂ}

set_option maxHeartbeats 1600000 in -- two-sided spectral trace chain
/-- **The two-sided spectral trace formula**:
`Re Tr(f(ρ) g(σ)) = Σ_{ij} f(p_i) g(q_j) |W_{ij}|²`. -/
theorem trace_matFun_mul_matFun_re (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) (f g : ℝ → ℝ) :
    ((matFun hρ f * matFun hσ g).trace).re =
      ∑ i, ∑ j, f (hρ.eigenvalues i) * g (hσ.eigenvalues j) *
        Complex.normSq (overlap hρ hσ i j) := by
  have hfdec : matFun hρ f =
      (hρ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ fun i => f (hρ.eigenvalues i)) *
        star (hρ.eigenvectorUnitary : Matrix n n ℂ) := by
    unfold matFun
    rw [conjStarAlgAut_apply]
  have hgdec : matFun hσ g =
      (hσ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ fun j => g (hσ.eigenvalues j)) *
        star (hσ.eigenvectorUnitary : Matrix n n ℂ) := by
    unfold matFun
    rw [conjStarAlgAut_apply]
  rw [hfdec, hgdec]
  have hshape : ((hρ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ fun i => f (hρ.eigenvalues i)) *
        star (hρ.eigenvectorUnitary : Matrix n n ℂ)) *
      ((hσ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ fun j => g (hσ.eigenvalues j)) *
        star (hσ.eigenvectorUnitary : Matrix n n ℂ)) =
      (hρ.eigenvectorUnitary : Matrix n n ℂ) *
        (diagonal (RCLike.ofReal ∘ fun i => f (hρ.eigenvalues i)) *
          (overlap hρ hσ *
            diagonal (RCLike.ofReal ∘ fun j => g (hσ.eigenvalues j)) *
            star (overlap hρ hσ))) *
        star (hρ.eigenvectorUnitary : Matrix n n ℂ) := by
    unfold overlap
    rw [star_mul, star_star]
    conv_lhs => rw [← Matrix.mul_one
      (((hρ.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ fun i => f (hρ.eigenvalues i)) *
          star (hρ.eigenvectorUnitary : Matrix n n ℂ)) *
        ((hσ.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ fun j => g (hσ.eigenvalues j)) *
          star (hσ.eigenvectorUnitary : Matrix n n ℂ))),
      ← coe_mul_star hρ.eigenvectorUnitary]
    simp only [Matrix.mul_assoc]
  rw [hshape, Matrix.trace_mul_cycle,
    star_mul_coe hρ.eigenvectorUnitary, Matrix.one_mul]
  exact trace_diag_mul_conj_re (fun i => f (hρ.eigenvalues i))
    (fun j => g (hσ.eigenvalues j)) (overlap hρ hσ)

/-- The eigenvalue expansion of the dyadic trace interpolation. -/
theorem tracePow_eq_sum (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (t : ℝ) :
    tracePow hρ hσ t =
      ∑ i, ∑ j, (hρ.eigenvalues i) ^ (1 - t) *
        (hσ.eigenvalues j) ^ t *
        Complex.normSq (overlap hρ hσ i j) :=
  trace_matFun_mul_matFun_re hρ hσ _ _

theorem trace_re_eq_sum_eigenvalues (hρ : ρ.IsHermitian) :
    (ρ.trace).re = ∑ i, hρ.eigenvalues i := by
  have h := hρ.trace_eq_sum_eigenvalues
  have h2 := congrArg Complex.re h
  rw [h2, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- The entropy numerator as a doubly indexed sum: spreading `Tr ρ` over
the doubly stochastic overlap weights. -/
theorem numerator_spread (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (t : ℝ) :
    (ρ.trace).re - tracePow hρ hσ t =
      ∑ i, ∑ j, (hρ.eigenvalues i -
        (hρ.eigenvalues i) ^ (1 - t) * (hσ.eigenvalues j) ^ t) *
        Complex.normSq (overlap hρ hσ i j) := by
  have hrow : ∀ i, ∑ j, Complex.normSq (overlap hρ hσ i j) = 1 :=
    sum_normSq_row (overlap_mul_star hρ hσ)
  rw [trace_re_eq_sum_eigenvalues hρ, tracePow_eq_sum]
  have hexp : ∑ i, hρ.eigenvalues i =
      ∑ i, ∑ j, hρ.eigenvalues i *
        Complex.normSq (overlap hρ hσ i j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hrow i, mul_one]
  rw [hexp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

end QRE
end NCG
