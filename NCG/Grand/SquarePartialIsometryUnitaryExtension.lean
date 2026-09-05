/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointSourceUniversality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Extending a square partial isometry to a unitary

A partial isometry on a finite square complex space is an isometry on the
range of its initial projection.  Mathlib's finite-dimensional isometry
extension then supplies a full isometry, which is automatically a unitary.
This file converts that extension back to a matrix and records the exact
matrix identity `U p = V`.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace NCG
namespace SquarePartialIsometryUnitaryExtension

variable {d : ℕ}

/-- A square partial isometry extends from its initial projection to a full
unitary matrix. -/
theorem exists_unitary_extension
    (V p : Matrix (Fin d) (Fin d) ℂ)
    (hp2 : p * p = p)
    (hVV : Vᴴ * V = p)
    (hVp : V * p = V) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ U * p = V := by
  classical
  let E := EuclideanSpace ℂ (Fin d)
  let pL : E →ₗ[ℂ] E := Matrix.toEuclideanLin p
  let VL : E →ₗ[ℂ] E := Matrix.toEuclideanLin V
  let S : Submodule ℂ E := LinearMap.range pL
  let L0 : S →ₗ[ℂ] E := VL.comp S.subtype
  have hpfix : ∀ y : S, pL y = y := by
    intro y
    obtain ⟨z, hz⟩ := y.property
    rw [← hz]
    change (Matrix.toLpLin 2 2 p ∘ₗ Matrix.toLpLin 2 2 p) z =
      Matrix.toLpLin 2 2 p z
    rw [← Matrix.toLpLin_mul_same, hp2]
  have hinner : ∀ x y : S, inner ℂ (L0 x) (L0 y) = inner ℂ x y := by
    intro x y
    have hy := congrArg WithLp.ofLp (hpfix y)
    change p *ᵥ WithLp.ofLp (y : E) = WithLp.ofLp (y : E) at hy
    calc
      inner ℂ (L0 x) (L0 y) =
          WithLp.ofLp (L0 y) ⬝ᵥ star (WithLp.ofLp (L0 x)) :=
        EuclideanSpace.inner_eq_star_dotProduct _ _
      _ = star (V *ᵥ WithLp.ofLp (x : E)) ⬝ᵥ
          (V *ᵥ WithLp.ofLp (y : E)) := by
        simp only [L0, VL, LinearMap.comp_apply, Submodule.coe_subtype]
        change (V *ᵥ WithLp.ofLp (y : E)) ⬝ᵥ
          star (V *ᵥ WithLp.ofLp (x : E)) = _
        rw [dotProduct_comm]
      _ = star (WithLp.ofLp (x : E)) ⬝ᵥ
          (p *ᵥ WithLp.ofLp (y : E)) := by
        rw [gram_realization_inner, hVV]
      _ = star (WithLp.ofLp (x : E)) ⬝ᵥ WithLp.ofLp (y : E) := by
        rw [hy]
      _ = WithLp.ofLp (y : E) ⬝ᵥ star (WithLp.ofLp (x : E)) :=
        dotProduct_comm _ _
      _ = inner ℂ x y := (EuclideanSpace.inner_eq_star_dotProduct _ _).symm
  let L : S →ₗᵢ[ℂ] E :=
    ⟨L0, fun x => by simp only [@norm_eq_sqrt_re_inner ℂ, hinner]⟩
  let M : E →ₗᵢ[ℂ] E := L.extend
  let U : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.toEuclideanLin.symm M.toLinearMap
  have hUlin : Matrix.toEuclideanLin U = M.toLinearMap := by
    exact LinearEquiv.apply_symm_apply Matrix.toEuclideanLin M.toLinearMap
  have hUstar : Uᴴ * U = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_one,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hUlin]
    exact M.adjoint_comp_self'
  have hUUstar : U * Uᴴ = 1 := mul_eq_one_comm.mp hUstar
  have hUp : U * p = V := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, hUlin]
    apply LinearMap.ext
    intro z
    have hpz : pL z ∈ S := LinearMap.mem_range_self pL z
    let sz : S := ⟨pL z, hpz⟩
    have hext : M sz = L sz := LinearIsometry.extend_apply L sz
    change M (pL z) = VL z
    change M (sz : E) = VL z
    rw [hext]
    change VL (pL z) = VL z
    change (Matrix.toLpLin 2 2 V ∘ₗ Matrix.toLpLin 2 2 p) z =
      Matrix.toLpLin 2 2 V z
    rw [← Matrix.toLpLin_mul_same, hVp]
  exact ⟨U, hUstar, hUUstar, hUp⟩

end SquarePartialIsometryUnitaryExtension
end NCG
