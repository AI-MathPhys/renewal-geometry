/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite positive certificate for the exact multiplicity
  algebra (`thm:SMST-relative-Howe-certificate`,
  Gran-Tensor manuscript)

* `howe_certificate`: the boxed equivalence
  `𝔾_Howe(c | ℳ) ≻ 0 ⟺ C*(c)' = ℳ`.
  The relative Howe Gram is the commutator-Laplacian
  quadratic form `x ↦ ‖𝒥x‖²` restricted to `ℳᗮ`; since
  `ℳ` already sits inside the kernel, the restriction is
  positive definite exactly when no further kernel vector
  exists, i.e. exactly when the commutant is no larger than
  `ℳ`.

* `howe_commutator_kernel`: the commutator source
  `𝒥(x) = ([c_j, x])_j` is linear and its kernel is exactly
  the commutant of the generating tuple — so the Gram is
  reconstructed from commutator words.

The reading of the least eigenvalue as the first positive
eigenvalue of the commutant Laplacian (the finite rigidity
margin) is the spectral restatement of positive
definiteness on `ℳᗮ`.
-/

open scoped InnerProductSpace

namespace NCG

/-- `thm:SMST-relative-Howe-certificate`. -/
theorem howe_certificate {T S : Type*}
    [NormedAddCommGroup T] [InnerProductSpace ℂ T]
    [FiniteDimensional ℂ T]
    [NormedAddCommGroup S] [InnerProductSpace ℂ S]
    (J : T →ₗ[ℂ] S) (M : Submodule ℂ T)
    (hM : M ≤ LinearMap.ker J) :
    -- the boxed positivity certificate
    ((∀ x ∈ Mᗮ, x ≠ 0 → 0 < ‖J x‖ ^ 2)
      ↔ LinearMap.ker J = M) := by
  constructor
  · intro hpos
    refine le_antisymm ?_ hM
    intro y hy
    -- split `y` along `ℳ ⊕ ℳᗮ`
    obtain ⟨m, hm, x, hx, hyx⟩ :=
      M.exists_add_mem_mem_orthogonal y
    have hJm : J m = 0 := hM hm
    have hJx : J x = 0 := by
      have : J y = J m + J x := by
        rw [← map_add, ← hyx]
      rw [LinearMap.mem_ker.mp hy, hJm, zero_add] at this
      exact this.symm
    have hx0 : x = 0 := by
      by_contra hne
      have := hpos x hx hne
      rw [hJx, norm_zero] at this
      simp at this
    rw [hyx, hx0, add_zero]
    exact hm
  · intro hker x hx hne
    have hJx : J x ≠ 0 := by
      intro h0
      have hxk : x ∈ LinearMap.ker J :=
        LinearMap.mem_ker.mpr h0
      rw [hker] at hxk
      have hzero : ⟪x, x⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal M x).mp hx x hxk
      exact hne (inner_self_eq_zero.mp hzero)
    have : 0 < ‖J x‖ := norm_pos_iff.mpr hJx
    positivity

/-- The commutator source and its kernel (the commutant). -/
theorem howe_commutator_kernel {n ι : Type*} [Fintype n]
    (c : ι → Matrix n n ℂ) :
    -- the commutator source is linear
    (∀ (x y : Matrix n n ℂ) (j : ι),
      c j * (x + y) - (x + y) * c j
        = (c j * x - x * c j) + (c j * y - y * c j))
    ∧ (∀ (t : ℂ) (x : Matrix n n ℂ) (j : ι),
        c j * (t • x) - (t • x) * c j
          = t • (c j * x - x * c j))
    -- its kernel is exactly the commutant
    ∧ (∀ x : Matrix n n ℂ,
        (∀ j, c j * x - x * c j = 0)
          ↔ ∀ j, c j * x = x * c j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y j
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  · intro t x j
    simp only [Matrix.mul_smul, Matrix.smul_mul,
      smul_sub]
  · intro x
    constructor
    · intro h j
      exact sub_eq_zero.mp (h j)
    · intro h j
      rw [h j, sub_self]

end NCG
