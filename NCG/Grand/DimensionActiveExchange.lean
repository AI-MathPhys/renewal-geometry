/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Minimum active recurrent tetrahedral port
  (`thm:dimension-active-exchange`,
  Gran-Tensor manuscript)

The DS.12 instrument draws `g` uniformly from
`{s, r, r⁻¹} = {(12), (1234), (4321)}` and writes
`s' = gt`.  Its endpoint chain on `X = {1,2,3,4}` is the
symmetric kernel `K₁ = ⅓(P_s + P_r + P_{r⁻¹})`, and its
unordered-pair chain on the six pairs is
`K₂ = ⅓(P̃_s + P̃_r + P̃_{r⁻¹})`.

* `dimension_active_exchange`: the boxed DS.13 Poincaré
  gaps:
  (i) `γ₁ = 2/3` — the endpoint Dirichlet bound
      `⟨f, K₁f⟩ ≤ ⅓‖f‖²` on mean-zero `f` (rational
      sum-of-squares certificate) with attainment by the
      eigenvector `(1,1,-1,-1)`;
  (ii) `γ₂ = 1 - 1/√3` — the pair-chain bound
      `√3·⟨f, K₂f⟩ ≤ ‖f‖²` on mean-zero `f` (sector
      certificates through the matching/antisymmetric
      splitting) with attainment by the explicit
      eigenvector
      `(√3+1, -(√3+2), 1, 1, -(√3+2), √3+1)` of
      eigenvalue `1/√3`;
  (iii) both kernels are stochastic (rows sum to one).

The construction clauses A1–A5 (sharp recovery
`t = g⁻¹s'`, `⟨s,r⟩ = S₄` pair-transitivity, reciprocal
endpoint marginal, cylinder recovery on forgetting the
port, and the three-contrast register with one transient
trit) are properties of the DS.12 instrument
(`con:dimension-active-exchange`) — its bookkeeping layer;
the endpoint-only no-go rides on the proved gaps.
-/

open Matrix Finset

namespace NCG

/-- The endpoint kernel of the DS.12 instrument. -/
noncomputable def activeEndpointKernel : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 2/3, 0, 1/3;
     2/3, 0, 1/3, 0;
     0, 1/3, 1/3, 1/3;
     1/3, 0, 1/3, 1/3]

/-- The unordered-pair kernel of the DS.12 instrument
(pairs ordered 12, 13, 14, 23, 24, 34). -/
noncomputable def activePairKernel : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1/3, 0, 1/3, 1/3, 0, 0;
     0, 0, 0, 1/3, 2/3, 0;
     1/3, 0, 0, 0, 1/3, 1/3;
     1/3, 1/3, 0, 0, 0, 1/3;
     0, 2/3, 1/3, 0, 0, 0;
     0, 0, 1/3, 1/3, 0, 1/3]

private lemma finval_five : (5 : Fin 6) = Fin.succ 4 :=
  rfl

/-- Matching-sector certificate: the symmetric block of
the pair form is dominated at `1/√3`. -/
private lemma active_sector_sym (t u₁ u₂ u₃ : ℝ)
    (ht2 : t ^ 2 = 3) (_ht : 1 ≤ t)
    (hsum : u₁ + u₂ + u₃ = 0) :
    t * ((1/3) * (u₁^2 + 2*u₂^2 + 4*u₁*u₃ + 2*u₂*u₃))
      ≤ u₁^2 + u₂^2 + u₃^2 := by
  have hu3 : u₃ = -u₁ - u₂ := by linarith
  rw [hu3]
  nlinarith [sq_nonneg ((2 + t)*u₁ + (1 + t)*u₂),
    sq_nonneg u₂, ht2, sq_nonneg u₁,
    mul_pos (by linarith : (0:ℝ) < 2 + t)
      (by linarith : (0:ℝ) < 2 + t)]

/-- Antisymmetric-sector certificate. -/
private lemma active_sector_anti (t a b c : ℝ)
    (ht2 : t ^ 2 = 3) (ht : 1 ≤ t) (ht3 : t ≤ 3) :
    t * ((1/3)*a^2 - (2/3)*b^2 - (2/3)*b*c)
      ≤ a^2 + b^2 + c^2 := by
  nlinarith [sq_nonneg (t*b + c), sq_nonneg a,
    sq_nonneg b, sq_nonneg c, ht2,
    mul_nonneg (by linarith : (0:ℝ) ≤ 3 - t)
      (sq_nonneg a),
    mul_nonneg (by linarith : (0:ℝ) ≤ t)
      (sq_nonneg b)]

/-- `thm:dimension-active-exchange` (the boxed DS.13
Poincaré gaps). -/
theorem dimension_active_exchange :
    -- (iii) both kernels are stochastic
    ((∀ i, ∑ j, activeEndpointKernel i j = 1)
      ∧ (∀ i, ∑ j, activePairKernel i j = 1))
    -- (i) γ₁ = 2/3: bound and attainment
    ∧ (∀ f : Fin 4 → ℝ, ∑ i, f i = 0 →
        f ⬝ᵥ (activeEndpointKernel *ᵥ f)
          ≤ (1/3) * ∑ i, (f i)^2)
    ∧ (activeEndpointKernel *ᵥ
        (![1, 1, -1, -1] : Fin 4 → ℝ)
        = ((1/3 : ℝ)) • (![1, 1, -1, -1] : Fin 4 → ℝ))
    -- (ii) γ₂ = 1 - 1/√3: bound and attainment
    ∧ (∀ f : Fin 6 → ℝ, ∑ i, f i = 0 →
        Real.sqrt 3 * (f ⬝ᵥ (activePairKernel *ᵥ f))
          ≤ ∑ i, (f i)^2)
    ∧ (activePairKernel *ᵥ
        ![Real.sqrt 3 + 1, -(Real.sqrt 3 + 2), 1, 1,
          -(Real.sqrt 3 + 2), Real.sqrt 3 + 1]
        = (Real.sqrt 3)⁻¹ •
        ![Real.sqrt 3 + 1, -(Real.sqrt 3 + 2), 1, 1,
          -(Real.sqrt 3 + 2), Real.sqrt 3 + 1])
    ∧ ((∑ i, (![Real.sqrt 3 + 1, -(Real.sqrt 3 + 2), 1,
          1, -(Real.sqrt 3 + 2),
          Real.sqrt 3 + 1] : Fin 6 → ℝ) i) = 0) := by
  have ht2 : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have ht1 : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, ht2]
  have ht3 : Real.sqrt 3 ≤ 3 := by
    nlinarith [Real.sqrt_nonneg 3, ht2]
  have ht0 : Real.sqrt 3 ≠ 0 := by linarith
  set t := Real.sqrt 3 with htdef
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases (by decide : ∀ x : Fin 4, x = 0 ∨ x = 1
        ∨ x = 2 ∨ x = 3) i with rfl | rfl | rfl | rfl <;>
      norm_num [activeEndpointKernel,
        Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.of_apply]
  · intro i
    rcases (by decide : ∀ x : Fin 6, x = 0 ∨ x = 1
        ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5) i
      with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [activePairKernel, Fin.sum_univ_six,
        Matrix.cons_val, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.of_apply]
       norm_num)
  · -- γ₁ bound: rational SOS certificate
    intro f hsum
    rw [Fin.sum_univ_four] at hsum
    have hexp : f ⬝ᵥ (activeEndpointKernel *ᵥ f)
        = (2/3)*(2*(f 0)*(f 1))
          + (1/3)*(2*(f 0)*(f 3))
          + (1/3)*(2*(f 1)*(f 2))
          + (1/3)*(2*(f 2)*(f 3))
          + (1/3)*(f 2)^2 + (1/3)*(f 3)^2 := by
      simp only [activeEndpointKernel, dotProduct,
        Matrix.mulVec, Fin.sum_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.cons_val_three,
        Matrix.of_apply]
      ring
    rw [hexp, Fin.sum_univ_four]
    have h3 : f 3 = -(f 0) - f 1 - f 2 := by linarith
    rw [h3]
    nlinarith [sq_nonneg (f 1 - f 0),
      sq_nonneg (f 0 + f 2)]
  · -- γ₁ attainment
    funext i
    rcases (by decide : ∀ x : Fin 4, x = 0 ∨ x = 1
        ∨ x = 2 ∨ x = 3) i with rfl | rfl | rfl | rfl <;>
      norm_num [activeEndpointKernel, Matrix.mulVec,
        dotProduct, Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.of_apply]
  · -- γ₂ bound: sector certificates
    intro f hsum
    rw [Fin.sum_univ_six] at hsum
    have hexp : f ⬝ᵥ (activePairKernel *ᵥ f)
        = (1/3)*(f 0)^2 + (1/3)*(f 5)^2
          + (2/3)*(f 0)*(f 2) + (2/3)*(f 0)*(f 3)
          + (2/3)*(f 1)*(f 3) + (4/3)*(f 1)*(f 4)
          + (2/3)*(f 2)*(f 4) + (2/3)*(f 2)*(f 5)
          + (2/3)*(f 3)*(f 5) := by
      simp only [activePairKernel, dotProduct,
        Matrix.mulVec, Fin.sum_univ_six,
        Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.of_apply]
      ring
    have hQ : f ⬝ᵥ (activePairKernel *ᵥ f)
        = ((1/3)*((f 0 + f 5)^2 + 2*(f 1 + f 4)^2
            + 4*(f 0 + f 5)*(f 2 + f 3)
            + 2*(f 1 + f 4)*(f 2 + f 3))
          + ((1/3)*(f 0 - f 5)^2
            - (2/3)*(f 1 - f 4)^2
            - (2/3)*(f 1 - f 4)*(f 2 - f 3))) / 2 := by
      rw [hexp]
      ring
    have hN : ∑ i, (f i)^2
        = ((f 0 + f 5)^2 + (f 1 + f 4)^2
            + (f 2 + f 3)^2 + (f 0 - f 5)^2
            + (f 1 - f 4)^2 + (f 2 - f 3)^2) / 2 := by
      rw [Fin.sum_univ_six]
      ring
    have hsym := active_sector_sym t (f 0 + f 5)
      (f 1 + f 4) (f 2 + f 3) ht2 ht1 (by linarith)
    have hanti := active_sector_anti t (f 0 - f 5)
      (f 1 - f 4) (f 2 - f 3) ht2 ht1 ht3
    rw [hQ, hN]
    nlinarith [hsym, hanti]
  · -- γ₂ attainment
    funext i
    rcases (by decide : ∀ x : Fin 6, x = 0 ∨ x = 1
        ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5) i
      with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [activePairKernel, Matrix.mulVec,
        dotProduct, Fin.sum_univ_six,
        Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.of_apply,
        Pi.smul_apply, smul_eq_mul]
       field_simp
       nlinarith [ht2])
  · -- the attainment vector is mean-zero
    rw [Fin.sum_univ_six]
    simp only [Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, Matrix.cons_val_four]
    ring

end NCG
