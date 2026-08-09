/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HoweCertificate

/-!
# the relative Howe certificate at the commutator source
-/

open scoped InnerProductSpace

namespace NCG

/-- The stacked commutator source whose Gram is the relative Howe Gram. -/
def smstCommutatorSource {n ι : Type*} [Fintype n]
    (c : ι → Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] (ι → Matrix n n ℂ) where
  toFun X j := c j * X - X * c j
  map_add' X Y := by
    ext j a b
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
      Matrix.sub_apply, Pi.add_apply]
    ring
  map_smul' z X := by
    ext j a b
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
      Matrix.sub_apply, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem smstCommutatorSource_apply {n ι : Type*} [Fintype n]
    (c : ι → Matrix n n ℂ) (X : Matrix n n ℂ) (j : ι) :
    smstCommutatorSource c X j = c j * X - X * c j := rfl

theorem smstCommutatorSource_ker {n ι : Type*} [Fintype n]
    (c : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    X ∈ LinearMap.ker (smstCommutatorSource c)
      ↔ ∀ j, c j * X = X * c j := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j
    have hj := congrFun h j
    exact sub_eq_zero.mp hj
  · intro h
    funext j
    exact sub_eq_zero.mpr (h j)

/-- `thm:SMST-relative-Howe-certificate`: positivity of the
relative commutator Gram on `Mᴺ` is equivalent to its kernel
being `M`; the commutator-source clause identifies that zero
space with the tuple commutant. -/
theorem relative_howe_certificate_exact
    {T S n ι : Type*}
    [NormedAddCommGroup T] [InnerProductSpace ℂ T]
    [FiniteDimensional ℂ T]
    [NormedAddCommGroup S] [InnerProductSpace ℂ S]
    [Fintype n]
    (J : T →ₗ[ℂ] S) (M : Submodule ℂ T)
    (hM : M ≤ LinearMap.ker J) (c : ι → Matrix n n ℂ) :
    (((∀ X ∈ Mᗮ, X ≠ 0 → 0 < ‖J X‖ ^ 2)
      ↔ LinearMap.ker J = M)
    ∧ (∀ X, X ∈ LinearMap.ker (smstCommutatorSource c)
      ↔ ∀ j, c j * X = X * c j)) := by
  exact ⟨howe_certificate J M hM, smstCommutatorSource_ker c⟩

end NCG
