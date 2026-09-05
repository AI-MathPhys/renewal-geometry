/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Reflected endpoint-action identity

Exact finite encoding of `def:GT-conditional-action-response` and
`thm:GT-reflected-endpoint-action` (AR.2–AR.7) for a reversible Markov
transfer `P` on a finite configuration space with stationary weight `μ`.

* `pairAction F x y` (AR.2) is the Hermitian matrix-valued pair action
  `½ conj(F_i(y) - F_i(x)) (F_j(y) - F_j(x))`, symmetric in `(x,y)`
  (`pairAction_symm`) and PSD (`pairAction_posSemidef`);
* `entranceWriter P F x = Γ_P(F)(x) = ∑_y P(x,y) A_F(x,y)` (AR.3), PSD
  (`entranceWriter_posSemidef`);
* `condExp_entrance` (AR.5): the conditional expectation of
  `A_F(X₀,X₁)` given `X₀ = x` under the stationary pair law `μ(x)P(x,y)` is
  `Γ_P(F)(x)`;
* `condExp_exit` (AR.6): the conditional expectation given `X₁ = y` is
  `Γ_P(F)(y)` (reversibility + symmetry of the action);
* `mean_entranceWriter` (AR.7): `E_μ Γ_P(F) = ⟪F_i, (I - P) F_j⟫_{L²(μ)}`, the
  transfer Dirichlet action on the bank.

Scope: `P` is taken as the reversible Markov kernel on `L²(μ)`; its
construction from the physical transfer `T` by the ground-state
multiplication `U_Ω` (AR.1) is the change of representation the record
starts from, and conjugation by `U_Ω` identifies the Dirichlet form
`⟪F_i,(I-P)F_j⟫_μ` with `Y_F^*(I-T)Y_F`.
-/

open Finset Matrix
open scoped ComplexOrder

namespace NCG
namespace ReflectedEndpointAction

variable {X ι : Type*} [Fintype X]

/-- The pair action `A_F(x,y)_{ij} = ½ conj(F_i y - F_i x) (F_j y - F_j x)`. -/
noncomputable def pairAction (F : ι → X → ℂ) (x y : X) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (1 / 2 : ℂ) * star (F i y - F i x) * (F j y - F j x)

/-- The entrance-conditional writer `Γ_P(F)(x) = ∑_y P(x,y) A_F(x,y)`. -/
noncomputable def entranceWriter (P : X → X → ℝ) (F : ι → X → ℂ) (x : X) : Matrix ι ι ℂ :=
  ∑ y, (P x y : ℂ) • pairAction F x y

omit [Fintype X] in
theorem pairAction_symm (F : ι → X → ℂ) (x y : X) : pairAction F x y = pairAction F y x := by
  ext i j
  simp only [pairAction, Matrix.of_apply]
  have : F i x - F i y = -(F i y - F i x) := by ring
  have h2 : F j x - F j y = -(F j y - F j x) := by ring
  rw [this, h2, star_neg]
  ring

omit [Fintype X] in
set_option linter.unusedFintypeInType false in
theorem pairAction_posSemidef [Fintype ι] (F : ι → X → ℂ) (x y : X) :
    (pairAction F x y).PosSemidef := by
  have : pairAction F x y
      = (Matrix.of fun (_ : Unit) j => (Real.sqrt (1 / 2) : ℂ) * (F j y - F j x))ᴴ
        * Matrix.of fun (_ : Unit) j => (Real.sqrt (1 / 2) : ℂ) * (F j y - F j x) := by
    ext i j
    simp only [pairAction, Matrix.of_apply, mul_apply, conjTranspose_apply, Finset.univ_unique,
      Finset.sum_singleton, star_mul', Complex.star_def, Complex.conj_ofReal]
    have hs : ((Real.sqrt (1 / 2) : ℝ) : ℂ) * (Real.sqrt (1 / 2) : ℝ) = (1 / 2 : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
      push_cast
      ring
    calc (1 / 2 : ℂ) * star (F i y - F i x) * (F j y - F j x)
        = (((Real.sqrt (1 / 2) : ℝ) : ℂ) * (Real.sqrt (1 / 2) : ℝ))
          * ((starRingEnd ℂ) (F i y - F i x) * (F j y - F j x)) := by
          rw [hs, Complex.star_def]; ring
      _ = _ := by ring
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

set_option linter.unusedFintypeInType false in
/-- **(AR.3)**: the entrance writer is positive for a nonnegative kernel. -/
theorem entranceWriter_posSemidef [Fintype ι] (P : X → X → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (F : ι → X → ℂ)
    (x : X) : (entranceWriter P F x).PosSemidef := by
  unfold entranceWriter
  refine Matrix.posSemidef_sum _ fun y _ => ?_
  exact (pairAction_posSemidef F x y).smul (Complex.zero_le_real.mpr (hP x y))

/-! ### Conditional expectations under the stationary pair law -/

/-- The stationary pair law `π(x,y) = μ(x) P(x,y)`. -/
def pairLaw (μ : X → ℝ) (P : X → X → ℝ) (x y : X) : ℝ := μ x * P x y

/-- Finite conditional expectation of a matrix-valued pair observable given
the first coordinate. -/
noncomputable def condExpFirst (μ : X → ℝ) (P : X → X → ℝ) (A : X → X → Matrix ι ι ℂ) (x : X) :
    Matrix ι ι ℂ :=
  ((∑ y, pairLaw μ P x y : ℝ) : ℂ)⁻¹ • ∑ y, (pairLaw μ P x y : ℂ) • A x y

/-- Finite conditional expectation given the second coordinate. -/
noncomputable def condExpSecond (μ : X → ℝ) (P : X → X → ℝ) (A : X → X → Matrix ι ι ℂ)
    (y : X) : Matrix ι ι ℂ :=
  ((∑ x, pairLaw μ P x y : ℝ) : ℂ)⁻¹ • ∑ x, (pairLaw μ P x y : ℂ) • A x y

/-- **(AR.5)**: `E[A_F(X₀,X₁) | X₀ = x] = Γ_P(F)(x)` on the support of `μ`. -/
theorem condExp_entrance (μ : X → ℝ) (P : X → X → ℝ) (hP1 : ∀ x, ∑ y, P x y = 1)
    (F : ι → X → ℂ) (x : X) (hx : μ x ≠ 0) :
    condExpFirst μ P (pairAction F) x = entranceWriter P F x := by
  unfold condExpFirst entranceWriter pairLaw
  have hsum : ∑ y, μ x * P x y = μ x := by
    rw [← Finset.mul_sum, hP1 x, mul_one]
  rw [hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  field_simp

/-- Reversibility `μ(x)P(x,y) = μ(y)P(y,x)` makes `μ` stationary. -/
theorem stationary_of_reversible (μ : X → ℝ) (P : X → X → ℝ) (hP1 : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, μ x * P x y = μ y * P y x) (y : X) :
    ∑ x, μ x * P x y = μ y := by
  calc ∑ x, μ x * P x y = ∑ x, μ y * P y x := Finset.sum_congr rfl fun x _ => hrev x y
    _ = μ y := by rw [← Finset.mul_sum, hP1 y, mul_one]

/-- **(AR.6)**: `E[A_F(X₀,X₁) | X₁ = y] = Γ_P(F)(y)` on the support of `μ`. -/
theorem condExp_exit (μ : X → ℝ) (P : X → X → ℝ) (hP1 : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, μ x * P x y = μ y * P y x) (F : ι → X → ℂ) (y : X) (hy : μ y ≠ 0) :
    condExpSecond μ P (pairAction F) y = entranceWriter P F y := by
  unfold condExpSecond entranceWriter pairLaw
  rw [stationary_of_reversible μ P hP1 hrev y, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul, hrev x y, pairAction_symm]
  congr 1
  push_cast
  field_simp

/-! ### The mean is the transfer Dirichlet action (AR.7) -/

/-- The `L²(μ)` Dirichlet form of the transfer: `⟪f, (I - P) g⟫_μ`. -/
noncomputable def dirichletForm (μ : X → ℝ) (P : X → X → ℝ) (f g : X → ℂ) : ℂ :=
  ∑ x, (μ x : ℂ) * star (f x) * (g x - ∑ y, (P x y : ℂ) * g y)

/-- **(AR.7)**: `E_μ[Γ_P(F)]_{ij} = ⟪F_i, (I - P) F_j⟫_{L²(μ)}`. -/
theorem mean_entranceWriter (μ : X → ℝ) (P : X → X → ℝ) (hP1 : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, μ x * P x y = μ y * P y x) (F : ι → X → ℂ) (i j : ι) :
    (∑ x, (μ x : ℂ) • entranceWriter P F x) i j = dirichletForm μ P (F i) (F j) := by
  unfold entranceWriter dirichletForm pairAction
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  -- the four terms of the expanded pair action
  have hrevC : ∀ x y, (μ x : ℂ) * (P x y : ℂ) = (μ y : ℂ) * (P y x : ℂ) := by
    intro x y
    have := hrev x y
    exact_mod_cast this
  have hP1C : ∀ x, ∑ y, (P x y : ℂ) = 1 := by
    intro x
    have := hP1 x
    exact_mod_cast this
  -- term identities obtained by swapping the summation order with reversibility
  have hA : ∑ x, ∑ y, (μ x : ℂ) * (P x y : ℂ) * (star (F i y) * F j y)
      = ∑ x, (μ x : ℂ) * (star (F i x) * F j x) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    calc ∑ x, (μ x : ℂ) * (P x y : ℂ) = ∑ x, (μ y : ℂ) * (P y x : ℂ) :=
          Finset.sum_congr rfl fun x _ => hrevC x y
      _ = (μ y : ℂ) := by rw [← Finset.mul_sum, hP1C y, mul_one]
  have hB : ∑ x, ∑ y, (μ x : ℂ) * (P x y : ℂ) * (star (F i y) * F j x)
      = ∑ x, (μ x : ℂ) * star (F i x) * ∑ y, (P x y : ℂ) * F j y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hrevC x y]
    ring
  have hC : ∑ x, ∑ y, (μ x : ℂ) * (P x y : ℂ) * (star (F i x) * F j y)
      = ∑ x, (μ x : ℂ) * star (F i x) * ∑ y, (P x y : ℂ) * F j y := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hD : ∑ x, ∑ y, (μ x : ℂ) * (P x y : ℂ) * (star (F i x) * F j x)
      = ∑ x, (μ x : ℂ) * (star (F i x) * F j x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP1C x, mul_one]
  -- expand the pair action entrywise and regroup
  have hexp : ∀ x, (μ x : ℂ) * ∑ y, (P x y : ℂ) * ((1 / 2 : ℂ) * star (F i y - F i x)
      * (F j y - F j x))
      = (1 / 2 : ℂ) * (∑ y, (μ x : ℂ) * (P x y : ℂ) * (star (F i y) * F j y)
        - ∑ y, (μ x : ℂ) * (P x y : ℂ) * (star (F i y) * F j x)
        - ∑ y, (μ x : ℂ) * (P x y : ℂ) * (star (F i x) * F j y)
        + ∑ y, (μ x : ℂ) * (P x y : ℂ) * (star (F i x) * F j x)) := by
    intro x
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [star_sub]
    ring
  simp only [hexp]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hA, hB, hC, hD]
  have : ∑ x, (μ x : ℂ) * star (F i x) * (F j x - ∑ y, (P x y : ℂ) * F j y)
      = ∑ x, (μ x : ℂ) * (star (F i x) * F j x)
        - ∑ x, (μ x : ℂ) * star (F i x) * ∑ y, (P x y : ℂ) * F j y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [this]
  ring

end ReflectedEndpointAction
end NCG
