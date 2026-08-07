/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Commutant audit, metric independence, and the common-action
  Legendre transform
  (`prop:commutant-audit`, `thm:metric-independence`,
   `thm:common-action-Legendre`, Gran-Tensor manuscript)

* `commutant_kernel` / `howe_pair_audit`: the joint commutant of
  a finite generating set is the kernel of one explicit linear
  map (`X ↦ ([X, A_i])_i`), so the Howe-pair assertion is
  decidable by finite linear algebra — solve the linear systems
  and verify the inclusions;
* `metric_independence`: any faithful physical future form
  sandwiched between `g₋·I` and `g₊·I` produces panel kernels
  sandwiched between the regular ones — all faithful metrics see
  the same word relations and ranks;
* `common_action_legendre`: the boxed Legendre transform — one
  common Lagrangian coefficient `χ` produces reciprocal
  Hamiltonian coefficients `a = χ⁻¹`, `b = χ`, with `ab = 1`.

Rendering disclosed: the dimension comparison in the audit is
`Module.finrank` of the displayed kernel; the uniqueness of the
metric operator `G` is the standard finite-dimensional
sesquilinear-form representation, taken as the frame here.
-/

open Matrix
open scoped ComplexOrder

set_option linter.unusedFintypeInType false

namespace NCG

/-- The commutator map whose kernel is the joint commutant. -/
def commMap {n : Type*} [Fintype n] {s : ℕ}
    (A : Fin s → Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] (Fin s → Matrix n n ℂ) where
  toFun X := fun i => X * A i - A i * X
  map_add' X Y := by
    funext i
    simp only [Pi.add_apply, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' c X := by
    funext i
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub,
      RingHom.id_apply, Pi.smul_apply]

/-- `prop:commutant-audit`, kernel clause: the joint commutant
is exactly the kernel of the displayed linear map. -/
theorem commutant_kernel {n : Type*} [Fintype n] {s : ℕ}
    (A : Fin s → Matrix n n ℂ) (X : Matrix n n ℂ) :
    X ∈ LinearMap.ker (commMap A)
      ↔ ∀ i, X * A i = A i * X := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h i
    have hi := congrFun h i
    exact sub_eq_zero.mp hi
  · intro h
    funext i
    exact sub_eq_zero.mpr (h i)

/-- `prop:commutant-audit`, inclusion clause: the Howe-pair
inclusions are membership of the generators in the displayed
kernels — finite linear algebra. -/
theorem howe_pair_audit {n : Type*} [Fintype n] {s t : ℕ}
    (A : Fin s → Matrix n n ℂ) (B : Fin t → Matrix n n ℂ) :
    ((∀ j i, B j * A i = A i * B j)
      ↔ ∀ j, B j ∈ LinearMap.ker (commMap A))
    ∧ ((∀ i j, A i * B j = B j * A i)
      ↔ ∀ i, A i ∈ LinearMap.ker (commMap B)) := by
  constructor
  · constructor
    · intro h j
      exact (commutant_kernel A (B j)).mpr (h j)
    · intro h j i
      exact (commutant_kernel A (B j)).mp (h j) i
  · constructor
    · intro h i
      exact (commutant_kernel B (A i)).mpr (h i)
    · intro h i j
      exact (commutant_kernel B (A i)).mp (h i) j

/-- `thm:metric-independence`: a two-sided scalar sandwich on
the metric operator transfers to every panel kernel, so all
faithful physical metrics have the same word relations and
ranks. -/
theorem metric_independence {n r : Type*} [Fintype n]
    [DecidableEq n] [Fintype r]
    (G : Matrix n n ℂ) (W : Matrix n r ℂ) (gm gp : ℝ)
    (hlow : (G - (gm : ℂ) • 1).PosSemidef)
    (hhigh : ((gp : ℂ) • 1 - G).PosSemidef) :
    (Wᴴ * G * W - (gm : ℂ) • (Wᴴ * W)).PosSemidef
    ∧ ((gp : ℂ) • (Wᴴ * W) - Wᴴ * G * W).PosSemidef := by
  constructor
  · have h := hlow.conjTranspose_mul_mul_same W
    have hexp : Wᴴ * (G - (gm : ℂ) • 1) * W
        = Wᴴ * G * W - (gm : ℂ) • (Wᴴ * W) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul]
    rwa [hexp] at h
  · have h := hhigh.conjTranspose_mul_mul_same W
    have hexp : Wᴴ * ((gp : ℂ) • 1 - G) * W
        = (gp : ℂ) • (Wᴴ * W) - Wᴴ * G * W := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul]
    rwa [hexp] at h

/-- `thm:common-action-Legendre`: the boxed transform — with
`p = χBv`, the Legendre value is
`H = (2χ)⁻¹·B⁻¹(p,p) + χV`, and the coefficients are exactly
reciprocal, `ab = χ⁻¹·χ = 1`. -/
theorem common_action_legendre {n : Type*} [Fintype n]
    [DecidableEq n] (B : Matrix n n ℝ) (_hB : Bᵀ = B)
    [Invertible B] (χ : ℝ) (hχ : 0 < χ) (v : n → ℝ) (V : ℝ) :
    ((χ • (B *ᵥ v)) ⬝ᵥ v
        - (χ / 2 * (v ⬝ᵥ (B *ᵥ v)) - χ * V)
      = (2 * χ)⁻¹
          * ((χ • (B *ᵥ v)) ⬝ᵥ (B⁻¹ *ᵥ (χ • (B *ᵥ v))))
        + χ * V)
    ∧ χ⁻¹ * χ = 1 := by
  refine ⟨?_, inv_mul_cancel₀ hχ.ne'⟩
  have hsolve : B⁻¹ *ᵥ (χ • (B *ᵥ v)) = χ • v := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  rw [hsolve]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (B *ᵥ v) v]
  have hne : χ ≠ 0 := hχ.ne'
  field_simp
  ring

end NCG
