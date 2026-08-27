/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DimensionLockedK4
import NCG.Grand.ContrastSpectrum

/-!
# Exact range--kernel split for the locked `K₄` source

This file supplies the two clauses left implicit in the original finite
calculation.  Every reversal-odd edge coefficient has a unique cut-plus-loop
decomposition, and the locked opportunity contrast metric restricts with the
same scalar `θ` to every zero-sum embedded `K₄` coefficient carrier.
-/

open Finset Matrix

namespace NCG

theorem k4Compiler_sum_zero (d : Fin 4 → Fin 4 → ℝ) :
    ∑ m, k4Compiler d m = 0 := by
  simp only [k4Compiler, Fin.sum_univ_four]
  norm_num [Fin.lt_def, Fin.ext_iff]
  ring

theorem k4Compiler_add (d e : Fin 4 → Fin 4 → ℝ) :
    k4Compiler (d + e) = k4Compiler d + k4Compiler e := by
  funext m
  unfold k4Compiler
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j <;> simp [hij, add_mul]

theorem k4Compiler_sub (d e : Fin 4 → Fin 4 → ℝ) :
    k4Compiler (d - e) = k4Compiler d - k4Compiler e := by
  funext m
  unfold k4Compiler
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j <;> simp [hij, sub_mul]

/-- Constructive and unique form of
`P⁻ = Ran B* ⊕ Ker B`.  The cut potential is `Bd/4`, and the remainder
is the unique reversal-odd loop coefficient. -/
theorem k4Odd_unique_cut_loop_decomposition
    (d : Fin 4 → Fin 4 → ℝ) (hd : ∀ i j, d j i = -(d i j)) :
    ∃ (w : Fin 4 → ℝ) (c : Fin 4 → Fin 4 → ℝ),
      (∑ i, w i = 0) ∧
      (∀ i j, c j i = -(c i j)) ∧
      k4Compiler c = 0 ∧
      d = (fun i j => k4Lift w i j + c i j) ∧
      ∀ (w' : Fin 4 → ℝ) (c' : Fin 4 → Fin 4 → ℝ),
        (∑ i, w' i = 0) →
        (∀ i j, c' j i = -(c' i j)) →
        k4Compiler c' = 0 →
        d = (fun i j => k4Lift w' i j + c' i j) →
        w' = w ∧ c' = c := by
  let w : Fin 4 → ℝ := fun m => (4 : ℝ)⁻¹ * k4Compiler d m
  let c : Fin 4 → Fin 4 → ℝ := d - k4Lift w
  have hw : ∑ i, w i = 0 := by
    simp only [w, ← Finset.mul_sum, k4Compiler_sum_zero, mul_zero]
  have hcodd : ∀ i j, c j i = -(c i j) := by
    intro i j
    simp only [c, Pi.sub_apply, k4Lift]
    rw [hd]
    ring
  have hframe : k4Compiler (k4Lift w) = fun m => 4 * w m :=
    dimension_locked_k4_source.1 w hw
  have hcker : k4Compiler c = 0 := by
    change k4Compiler (d - k4Lift w) = 0
    rw [k4Compiler_sub, hframe]
    funext m
    simp [w]
  have hdecomp : d = fun i j => k4Lift w i j + c i j := by
    funext i j
    simp [c]
  refine ⟨w, c, hw, hcodd, hcker, hdecomp, ?_⟩
  intro w' c' hw' _hcodd' hc' hd'
  have hframe' : k4Compiler (k4Lift w') = fun m => 4 * w' m :=
    dimension_locked_k4_source.1 w' hw'
  have hd'' : d = k4Lift w' + c' := by
    funext i j
    exact congrFun (congrFun hd' i) j
  have hcompiler' : k4Compiler d = fun m => 4 * w' m := by
    rw [hd'', k4Compiler_add, hframe', hc']
    simp
  have hweq : w' = w := by
    funext m
    have hm := congrFun hcompiler' m
    dsimp [w]
    linarith [hm]
  refine ⟨hweq, ?_⟩
  funext i j
  have hij := congrFun (congrFun hd' i) j
  rw [hweq] at hij
  have hij0 := congrFun (congrFun hdecomp i) j
  linarith

/-- The opportunity contrast theorem identifies, rather than merely names,
the scalar in the locked `K₄` source metric: any zero-sum coefficient embedding
sees exactly multiplication by `θ`, hence its pulled-back Gram is `θ` times
the original coefficient Gram. -/
theorem lockedContrastMetric_restricts_to_embeddedK4
    {D : Type*} (θ : ℂ) (hθ : θ ≠ 0)
    (h12 : (12 : ℂ) - 11 * θ ≠ 0)
    (E : D → Fin 24 → ℂ) (q : D → D → ℂ)
    (hzero : ∀ d, ∑ i, E d i = 0)
    (hpair : ∀ d e, star (E d) ⬝ᵥ E e = q d e) :
    ∀ d e,
      star (E d) ⬝ᵥ
          ((θ • (1 - (24 : ℂ)⁻¹ • allOnes24)
            + ((12 : ℂ) - 11 * θ) • ((24 : ℂ)⁻¹ • allOnes24)) *ᵥ E e)
        = θ * q d e := by
  intro d e
  rw [(locked_opportunity_contrast_spectrum θ hθ h12).2.1 (E e) (hzero e)]
  rw [dotProduct_smul, hpair]
  rfl

end NCG
