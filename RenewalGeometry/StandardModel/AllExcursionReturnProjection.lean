/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.AllExcursionReturnExact
import RenewalGeometry.StandardModel.ReciprocalReturnBankExact

/-!
# All-excursion return alternative: the cyclic spaces and the stopping projection

Completes `prop:all-excursion-return` of the spacetime–gauge duality paper on top of
`AllExcursionReturnExact` (which proved the proposition conditionally on a matrix `P`
with the four properties of the orthogonal projection `P_{𝒩_A}`).

For the mediator notation of `thm:reciprocal-return` (`h = h^*` on `N`, `n = dim N`,
`ρ_A = Tr_V(A A^*)`, `ρ_B = Tr_V(B B^*)`) the manuscript sets
`𝒩_A = Span{h^k Ran ρ_A : 0 ≤ k < n}` and `𝒩_B = Span{h^k Ran ρ_B : 0 ≤ k < n}`.

* `cyclicSpace h ρ`: the subspace `Span{h^k Ran ρ : k < n}` of `EuclideanSpace ℂ N`;
  `pow_mul_apply_mem`: by Cayley–Hamilton `h^k Ran ρ ⊆ 𝒩_ρ` for **every** `k`, hence
  `toEuclideanLin_mul_mem`: `𝒩_ρ` is `h`-invariant;
* `cyclicProj h ρ`: the orthogonal projection `P_{𝒩_ρ}` as a matrix on `N`;
  `cyclicProj_conjTranspose` (Hermitian), `cyclicProj_mul_self` (`P ρ = ρ`),
  `cyclicProj_comm` (`P h = h P`: `h` self-adjoint makes the invariant subspace reducing),
  `mul_cyclicProj_eq_zero` (`σ h^k ρ = 0` for `k < n` gives `σ P = 0`);
* `cyclicSpace_isOrtho`: `ρ_B h^k ρ_A = 0` for `k < n` gives `𝒩_A ⊥ 𝒩_B`;
* `all_excursion_return_of_mass_eq_zero`: **the proposition** — if `𝔪_ret = 0` (at the
  horizon `n = dim N`), then `𝒩_A ⊥ 𝒩_B`, the stopping projection
  `Q = I_T ⊕ 0_{H_priv} ⊕ (I_V ⊗ P_{𝒩_A})` commutes with every generator of the declared
  reciprocal route bank and with its adjoint, and every word `w` of the bank has
  `p_H w p_T = 0`.

Scoped hypotheses as in `ReciprocalReturnMassExact.mass_eq_zero_iff`: finite index
types, `V` nonempty, `v` a unitary representation of the finite group `G` that is
irreducible in the Schur (scalar-commutant) form, `h` self-adjoint.
-/

open Matrix Kronecker

namespace RenewalGeometry
namespace AllExcursion

open ReciprocalReturn ReciprocalReturnMass

/-! ### A symmetric operator commutes with the projection onto an invariant subspace -/

/-- If `T` is symmetric and `K` is `T`-invariant, then `P_K T = T P_K`. -/
theorem starProjection_comm_of_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (hK : ∀ x ∈ K, T x ∈ K) (x : E) :
    K.starProjection (T x) = T (K.starProjection x) := by
  have h1 : K.starProjection (T (K.starProjection x)) = T (K.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr (hK _ (K.starProjection_apply_mem x))
  have h2 : K.starProjection (T (x - K.starProjection x)) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
    intro u hu
    have hz := K.sub_starProjection_mem_orthogonal x
    rw [Submodule.mem_orthogonal] at hz
    rw [← hT u]
    exact hz _ (hK u hu)
  calc K.starProjection (T x)
      = K.starProjection (T (K.starProjection x) + T (x - K.starProjection x)) := by
        rw [← map_add, add_sub_cancel]
    _ = T (K.starProjection x) := by rw [map_add, h1, h2, add_zero]

section Cyclic

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A Hermitian matrix acts as a symmetric operator on `EuclideanSpace ℂ N`. -/
theorem toEuclideanLin_isSymmetric {h : Matrix N N ℂ} (hh : hᴴ = h) :
    (Matrix.toEuclideanLin h).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff',
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hh]

/-- The `h`-cyclic space `𝒩_ρ = Span{h^k Ran ρ : 0 ≤ k < n}`, `n = dim N`. -/
noncomputable def cyclicSpace (h ρ : Matrix N N ℂ) : Submodule ℂ (EuclideanSpace ℂ N) :=
  ⨆ k : Fin (Fintype.card N), LinearMap.range (Matrix.toEuclideanLin (h ^ (k : ℕ) * ρ))

/-- The orthogonal projection `P_{𝒩_ρ}` onto the cyclic space, as a matrix on `N`. -/
noncomputable def cyclicProj (h ρ : Matrix N N ℂ) : Matrix N N ℂ :=
  Matrix.toEuclideanLin.symm
    ((cyclicSpace h ρ).starProjection : EuclideanSpace ℂ N →ₗ[ℂ] EuclideanSpace ℂ N)

theorem toEuclideanLin_cyclicProj (h ρ : Matrix N N ℂ) :
    Matrix.toEuclideanLin (cyclicProj h ρ) =
      ((cyclicSpace h ρ).starProjection : EuclideanSpace ℂ N →ₗ[ℂ] EuclideanSpace ℂ N) := by
  simp [cyclicProj]

/-- **Cayley–Hamilton beyond the horizon**: `h^k Ran ρ ⊆ 𝒩_ρ` for every `k ∈ ℕ`. -/
theorem pow_mul_apply_mem (h ρ : Matrix N N ℂ) (k : ℕ) (y : EuclideanSpace ℂ N) :
    Matrix.toEuclideanLin (h ^ k * ρ) y ∈ cyclicSpace h ρ := by
  rcases isEmpty_or_nonempty N with hN | hN
  · rw [show h ^ k * ρ = 0 from Subsingleton.elim _ _, map_zero, LinearMap.zero_apply]
    exact zero_mem _
  have hdeg : (Polynomial.X ^ k %ₘ h.charpoly).natDegree < Fintype.card N := by
    have h1 := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ k) (Matrix.charpoly_monic h)
      (by
        intro hc
        have := Matrix.charpoly_natDegree_eq_dim h
        rw [hc, Polynomial.natDegree_one] at this
        exact (Fintype.card_pos (α := N)).ne this)
    rwa [Matrix.charpoly_natDegree_eq_dim] at h1
  rw [Matrix.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hdeg, Matrix.sum_mul,
    map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Matrix.smul_mul, map_smul, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem ⟨i, hi⟩ (LinearMap.mem_range_self _ y))

/-- `Ran ρ ⊆ 𝒩_ρ`. -/
theorem apply_mem_cyclicSpace (h ρ : Matrix N N ℂ) (y : EuclideanSpace ℂ N) :
    Matrix.toEuclideanLin ρ y ∈ cyclicSpace h ρ := by
  have := pow_mul_apply_mem h ρ 0 y
  rwa [pow_zero, one_mul] at this

/-- `𝒩_ρ` is `h`-invariant. -/
theorem toEuclideanLin_mul_mem (h ρ : Matrix N N ℂ) {x : EuclideanSpace ℂ N}
    (hx : x ∈ cyclicSpace h ρ) : Matrix.toEuclideanLin h x ∈ cyclicSpace h ρ := by
  refine Submodule.iSup_induction _
    (motive := fun x : EuclideanSpace ℂ N => Matrix.toEuclideanLin h x ∈ cyclicSpace h ρ)
    hx ?_ ?_ ?_
  · rintro k x ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, ← mul_assoc, ← pow_succ']
    exact pow_mul_apply_mem h ρ _ y
  · rw [map_zero]; exact zero_mem _
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

/-- `𝒩_ρ` is `h^j`-invariant for every `j`. -/
theorem toEuclideanLin_pow_mem (h ρ : Matrix N N ℂ) (j : ℕ) {x : EuclideanSpace ℂ N}
    (hx : x ∈ cyclicSpace h ρ) : Matrix.toEuclideanLin (h ^ j) x ∈ cyclicSpace h ρ := by
  induction j with
  | zero => rw [pow_zero, Matrix.toLpLin_one, LinearMap.id_apply]; exact hx
  | succ j ih =>
    rw [pow_succ', Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    exact toEuclideanLin_mul_mem h ρ ih

/-- `P_{𝒩_ρ}` is Hermitian. -/
theorem cyclicProj_conjTranspose (h ρ : Matrix N N ℂ) : (cyclicProj h ρ)ᴴ = cyclicProj h ρ := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, toEuclideanLin_cyclicProj]
  exact (cyclicSpace h ρ).starProjection_isSymmetric.adjoint_eq

/-- `P_{𝒩_ρ} ρ = ρ` (`Ran ρ ⊆ 𝒩_ρ`). -/
theorem cyclicProj_mul_self (h ρ : Matrix N N ℂ) : cyclicProj h ρ * ρ = ρ := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, toEuclideanLin_cyclicProj]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  exact Submodule.starProjection_eq_self_iff.mpr (apply_mem_cyclicSpace h ρ x)

/-- `P_{𝒩_ρ} h = h P_{𝒩_ρ}`: the `h`-invariant subspace `𝒩_ρ` is reducing for the
self-adjoint `h`. -/
theorem cyclicProj_comm (h ρ : Matrix N N ℂ) (hh : hᴴ = h) :
    cyclicProj h ρ * h = h * cyclicProj h ρ := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same, toEuclideanLin_cyclicProj]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  exact starProjection_comm_of_invariant _ _ (toEuclideanLin_isSymmetric hh)
    (fun x hx => toEuclideanLin_mul_mem h ρ hx) x

/-- A matrix `σ` with `σ h^k ρ = 0` for all `k < n` vanishes on `𝒩_ρ`. -/
theorem toEuclideanLin_eq_zero_of_mem (h ρ σ : Matrix N N ℂ)
    (hall : ∀ k : Fin (Fintype.card N), σ * h ^ (k : ℕ) * ρ = 0)
    {x : EuclideanSpace ℂ N} (hx : x ∈ cyclicSpace h ρ) : Matrix.toEuclideanLin σ x = 0 := by
  refine Submodule.iSup_induction _
    (motive := fun x : EuclideanSpace ℂ N => Matrix.toEuclideanLin σ x = 0) hx ?_ ?_ ?_
  · rintro k x ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, ← mul_assoc, hall k, map_zero,
      LinearMap.zero_apply]
  · exact map_zero _
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- `σ h^k ρ = 0` for all `k < n` gives `σ P_{𝒩_ρ} = 0`. -/
theorem mul_cyclicProj_eq_zero (h ρ σ : Matrix N N ℂ)
    (hall : ∀ k : Fin (Fintype.card N), σ * h ^ (k : ℕ) * ρ = 0) :
    σ * cyclicProj h ρ = 0 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, toEuclideanLin_cyclicProj, map_zero]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.zero_apply]
  exact toEuclideanLin_eq_zero_of_mem h ρ σ hall ((cyclicSpace h ρ).starProjection_apply_mem x)

/-- For Hermitian `σ`, `σ h^k ρ = 0` for all `k < n` gives `P_{𝒩_ρ} σ = 0`. -/
theorem cyclicProj_mul_eq_zero (h ρ σ : Matrix N N ℂ) (hσ : σᴴ = σ)
    (hall : ∀ k : Fin (Fintype.card N), σ * h ^ (k : ℕ) * ρ = 0) :
    cyclicProj h ρ * σ = 0 := by
  have := congrArg Matrix.conjTranspose (mul_cyclicProj_eq_zero h ρ σ hall)
  rwa [Matrix.conjTranspose_mul, cyclicProj_conjTranspose, hσ, Matrix.conjTranspose_zero] at this

/-- **`𝒩_A ⊥ 𝒩_B`**: if `h` and `ρ_B` are Hermitian and `ρ_B h^k ρ_A = 0` for all `k < n`,
the two cyclic spaces are orthogonal. -/
theorem cyclicSpace_isOrtho (h ρA ρB : Matrix N N ℂ) (hh : hᴴ = h) (hB : ρBᴴ = ρB)
    (hall : ∀ k : Fin (Fintype.card N), ρB * h ^ (k : ℕ) * ρA = 0) :
    cyclicSpace h ρA ⟂ cyclicSpace h ρB := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  refine Submodule.iSup_induction _
    (motive := fun v : EuclideanSpace ℂ N => inner ℂ u v = 0) hv ?_ ?_ ?_
  · rintro j v ⟨z, rfl⟩
    rw [← LinearMap.adjoint_inner_left, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hh, hB, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply,
      toEuclideanLin_eq_zero_of_mem h ρA ρB hall (toEuclideanLin_pow_mem h ρA _ hu),
      inner_zero_left]
  · exact inner_zero_right u
  · intro x y hx hy
    rw [inner_add_right, hx, hy, add_zero]

end Cyclic

/-! ### The proposition -/

section Main

variable {V N T H G : Type*} [Fintype V] [Fintype N] [Fintype T] [Fintype H] [Fintype G]
  [DecidableEq V] [DecidableEq N] [DecidableEq T] [DecidableEq H] [Group G]

/-- **`prop:all-excursion-return`.**  If `𝔪_ret = 0` (at the horizon `n = dim N`), then
`𝒩_A ⊥ 𝒩_B`, the stopping projection `Q = I_T ⊕ 0_{H_priv} ⊕ (I_V ⊗ P_{𝒩_A})` commutes
with every generator of the declared reciprocal route bank and with its adjoint, and
consequently every word `w` of the bank has `p_H w p_T = 0`. -/
theorem all_excursion_return_of_mass_eq_zero [Nonempty V]
    (v : G → Matrix V V ℂ) (h : Matrix N N ℂ) (A : Matrix (V × N) T ℂ) (B : Matrix (V × N) H ℂ)
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (hh : hᴴ = h) (hmass : mass v h A B (Fintype.card N) = 0) :
    cyclicSpace h (partialGram A) ⟂ cyclicSpace h (partialGram B) ∧
    (∀ M ∈ bank v h A B,
      stopProj (cyclicProj h (partialGram A)) * M = M * stopProj (cyclicProj h (partialGram A)) ∧
      stopProj (cyclicProj h (partialGram A)) * Mᴴ =
        Mᴴ * stopProj (cyclicProj h (partialGram A))) ∧
    ∀ w ∈ words (bank v h A B), pH * w * pT = 0 := by
  have hall := (mass_eq_zero_iff v h A B hmul hone hunit hirr hh _).mp hmass
  have hB : (partialGram B)ᴴ = partialGram B := (partialGram_posSemidef B).1
  refine ⟨cyclicSpace_isOrtho h _ _ hh hB hall, ?_⟩
  exact all_excursion_return v h A B (cyclicProj_conjTranspose h _)
    (cyclicProj_comm h _ hh) (cyclicProj_mul_self h _) (cyclicProj_mul_eq_zero h _ _ hB hall)

end Main

end AllExcursion
end RenewalGeometry
