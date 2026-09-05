/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.V036EinsteinBoundary

/-!
# Localized renewal–Palatini insertion
  (`thm:Palatini`, Gran-Tensor manuscript)

* `holst_palatini_coefficients_unique`: the boxed unique form —
  when the Holst, Palatini, and volume densities are linearly
  independent, the coefficients `(α, β, λ)` of the
  memory-shorted primitive gravitational score are uniquely
  determined;
* `palatini_insertion_determined` /
  `palatini_insertion_linear`: the boxed first-variation limit
  `χ∫√-g(G+Λg)k` is faithful and linear in the test insertion
  (re-exported from the proved insertion-pairing layer) — the
  limit determines the Einstein tensor content exactly.

Rendering disclosed: hypotheses (E1)–(E4) (the memory-cumulant
subtraction, face linearization, Lorentz naturality/commutant
audit, the torsion alternative, and the `L²`/`L⁶`/weak-`L^p`
convergence of coframe and curvature) are the manuscript's
analytic layer; the coefficient uniqueness and the insertion
faithfulness/linearity are proved here.
-/

namespace NCG

/-- Boxed unique form: linear independence of the Holst,
Palatini, and volume densities forces unique coefficients. -/
theorem holst_palatini_coefficients_unique {V : Type*}
    [AddCommGroup V] [Module ℝ V] (LH LP LV : V)
    (hli : LinearIndependent ℝ ![LH, LP, LV])
    (α₁ β₁ lam₁ α₂ β₂ lam₂ : ℝ)
    (heq : α₁ • LH + β₁ • LP + lam₁ • LV
      = α₂ • LH + β₂ • LP + lam₂ • LV) :
    α₁ = α₂ ∧ β₁ = β₂ ∧ lam₁ = lam₂ := by
  have hcomb : (α₁ - α₂) • LH + (β₁ - β₂) • LP
      + (lam₁ - lam₂) • LV = 0 := by
    have h := sub_eq_zero.mpr heq
    rw [show α₁ • LH + β₁ • LP + lam₁ • LV
        - (α₂ • LH + β₂ • LP + lam₂ • LV)
      = (α₁ - α₂) • LH + (β₁ - β₂) • LP
        + (lam₁ - lam₂) • LV from by
        rw [sub_smul, sub_smul, sub_smul]
        abel] at h
    exact h
  have hzero := Fintype.linearIndependent_iff.mp hli
    ![α₁ - α₂, β₁ - β₂, lam₁ - lam₂] (by
      simpa [Fin.sum_univ_three] using hcomb)
  have h0 : α₁ - α₂ = 0 := hzero 0
  have h1 : β₁ - β₂ = 0 := hzero 1
  have h2 : lam₁ - lam₂ = 0 := hzero 2
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The boxed insertion limit is faithful: vanishing against
every test forces the tensor to vanish (re-export). -/
theorem palatini_insertion_determined {ι : Type*} [Fintype ι]
    (T : ι → ℝ) (h : ∀ k : ι → ℝ, ∑ i, T i * k i = 0) :
    ∀ i, T i = 0 :=
  insertion_functional_determined T h

/-- The boxed insertion limit is linear in the test insertion
(re-export). -/
theorem palatini_insertion_linear {ι : Type*} [Fintype ι]
    (T : ι → ℝ) (k₁ k₂ : ι → ℝ) (c : ℝ) :
    ∑ i, T i * (c * k₁ i + k₂ i)
      = c * (∑ i, T i * k₁ i) + ∑ i, T i * k₂ i :=
  insertion_pairing_linear T k₁ k₂ c

end NCG
