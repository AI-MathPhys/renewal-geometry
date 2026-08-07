/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Entropy Hessian, Fisher window, and expectation
  coordinates (`thm:primitive-information-geometry`,
  Gran-Tensor manuscript)

For the finite exponential family
`p_θ(a) = p₀(a)·exp(θf(a))/Z(θ)`, `ψ(θ) = log Z(θ)`:

* `primitive_information_geometry`:
  (i) the partition sum is positive and `p_θ` is a
      probability vector;
  (ii) the boxed Bregman identity: the relative entropy of
      two tilted laws is exactly
      `𝒟(θ‖φ) = ψ(φ) - ψ(θ) - m(θ)(φ - θ)` with
      `m(θ) = Σ p_θ f` the expectation coordinate;
  (iii) nonnegativity `𝒟(θ‖φ) ≥ 0` (Gibbs), so `ψ` is
      convex along the family and the primitive is a
      minimizer of the renormalized action on its ray.

The Fisher-window clauses (`g₋I ⪯ G(θ) ⪯ g₊I` on a ball by
real-analyticity, the bi-Lipschitz expectation map, and the
two-sided quadratic bounds `g₋/2‖θ-φ‖² ≤ 𝒟 ≤ g₊/2‖θ-φ‖²`)
are the manuscript's Taylor/continuity layer over this
exact identity; the second-variation Gram
`D²𝒜(p₀) = G₀` is the score-bank Gram of
`NCG.primitive_score_bank`.
-/

open Finset

namespace NCG

variable {ι : Type*} [Fintype ι]

/-- Partition sum of the tilted family. -/
noncomputable def igZ (p₀ f : ι → ℝ) (θ : ℝ) : ℝ :=
  ∑ a, p₀ a * Real.exp (θ * f a)

/-- Tilted law. -/
noncomputable def igP (p₀ f : ι → ℝ) (θ : ℝ) (a : ι) :
    ℝ :=
  p₀ a * Real.exp (θ * f a) / igZ p₀ f θ

/-- Log-partition (cumulant) function. -/
noncomputable def igPsi (p₀ f : ι → ℝ) (θ : ℝ) : ℝ :=
  Real.log (igZ p₀ f θ)

/-- Expectation coordinate. -/
noncomputable def igM (p₀ f : ι → ℝ) (θ : ℝ) : ℝ :=
  ∑ a, igP p₀ f θ a * f a

/-- `thm:primitive-information-geometry`. -/
theorem primitive_information_geometry [Nonempty ι]
    (p₀ f : ι → ℝ) (hp : ∀ a, 0 < p₀ a) :
    -- (i) positivity and normalization
    (∀ θ, 0 < igZ p₀ f θ)
    ∧ (∀ θ a, 0 < igP p₀ f θ a)
    ∧ (∀ θ, ∑ a, igP p₀ f θ a = 1)
    -- (ii) the boxed Bregman identity
    ∧ (∀ θ φ, ∑ a, igP p₀ f θ a
          * Real.log (igP p₀ f θ a / igP p₀ f φ a)
        = igPsi p₀ f φ - igPsi p₀ f θ
          - igM p₀ f θ * (φ - θ))
    -- (iii) Gibbs nonnegativity
    ∧ (∀ θ φ, 0 ≤ ∑ a, igP p₀ f θ a
          * Real.log (igP p₀ f θ a / igP p₀ f φ a)) := by
  have hZ : ∀ θ, 0 < igZ p₀ f θ := by
    intro θ
    exact Finset.sum_pos
      (fun a _ => mul_pos (hp a) (Real.exp_pos _))
      Finset.univ_nonempty
  have hPpos : ∀ θ a, 0 < igP p₀ f θ a := by
    intro θ a
    exact div_pos
      (mul_pos (hp a) (Real.exp_pos _)) (hZ θ)
  have hPsum : ∀ θ, ∑ a, igP p₀ f θ a = 1 := by
    intro θ
    rw [show ∑ a, igP p₀ f θ a
        = (∑ a, p₀ a * Real.exp (θ * f a)) / igZ p₀ f θ
      from by rw [Finset.sum_div]; rfl]
    exact div_self (ne_of_gt (hZ θ))
  have hlogterm : ∀ θ φ a,
      Real.log (igP p₀ f θ a / igP p₀ f φ a)
        = (θ - φ) * f a
          + (igPsi p₀ f φ - igPsi p₀ f θ) := by
    intro θ φ a
    rw [Real.log_div (ne_of_gt (hPpos θ a))
      (ne_of_gt (hPpos φ a))]
    unfold igP igPsi
    rw [Real.log_div
        (ne_of_gt (mul_pos (hp a) (Real.exp_pos _)))
        (ne_of_gt (hZ θ)),
      Real.log_div
        (ne_of_gt (mul_pos (hp a) (Real.exp_pos _)))
        (ne_of_gt (hZ φ)),
      Real.log_mul (ne_of_gt (hp a))
        (ne_of_gt (Real.exp_pos _)),
      Real.log_mul (ne_of_gt (hp a))
        (ne_of_gt (Real.exp_pos _)),
      Real.log_exp, Real.log_exp]
    ring
  refine ⟨hZ, hPpos, hPsum, ?_, ?_⟩
  · intro θ φ
    calc ∑ a, igP p₀ f θ a
          * Real.log (igP p₀ f θ a / igP p₀ f φ a)
        = ∑ a, (igP p₀ f θ a * ((θ - φ) * f a)
            + igP p₀ f θ a
              * (igPsi p₀ f φ - igPsi p₀ f θ)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hlogterm θ φ a]
          ring
      _ = (θ - φ) * igM p₀ f θ
          + (igPsi p₀ f φ - igPsi p₀ f θ) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul,
            hPsum, one_mul]
          congr 1
          rw [igM, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = igPsi p₀ f φ - igPsi p₀ f θ
          - igM p₀ f θ * (φ - θ) := by ring
  · intro θ φ
    have hterm : ∀ a ∈ Finset.univ,
        igP p₀ f θ a
          * Real.log (igP p₀ f φ a / igP p₀ f θ a)
        ≤ igP p₀ f φ a - igP p₀ f θ a := by
      intro a _
      have hratio : 0 < igP p₀ f φ a / igP p₀ f θ a :=
        div_pos (hPpos φ a) (hPpos θ a)
      have hlog := Real.log_le_sub_one_of_pos hratio
      have h1 := mul_le_mul_of_nonneg_left hlog
        (le_of_lt (hPpos θ a))
      calc igP p₀ f θ a
            * Real.log (igP p₀ f φ a / igP p₀ f θ a)
          ≤ igP p₀ f θ a
            * (igP p₀ f φ a / igP p₀ f θ a - 1) := h1
        _ = igP p₀ f φ a - igP p₀ f θ a := by
            have hne := ne_of_gt (hPpos θ a)
            field_simp
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, hPsum, hPsum,
      sub_self] at hsum
    have hflip : ∀ a,
        igP p₀ f θ a
          * Real.log (igP p₀ f θ a / igP p₀ f φ a)
        = -(igP p₀ f θ a
          * Real.log (igP p₀ f φ a / igP p₀ f θ a)) := by
      intro a
      have hlogflip :
          Real.log (igP p₀ f θ a / igP p₀ f φ a)
          = -Real.log (igP p₀ f φ a / igP p₀ f θ a) := by
        rw [← Real.log_inv, inv_div]
      rw [hlogflip]
      ring
    calc (0 : ℝ)
        ≤ -∑ a, igP p₀ f θ a
            * Real.log (igP p₀ f φ a / igP p₀ f θ a) := by
          linarith
      _ = ∑ a, igP p₀ f θ a
            * Real.log (igP p₀ f θ a / igP p₀ f φ a) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun a _ =>
            (hflip a).symm

end NCG
