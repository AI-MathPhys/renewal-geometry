/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.EdgeCommutantBasisExact
import RenewalGeometry.Commutant.MatrixFactorNormalForm

/-!
# The degree-one internal-colour obstruction

`thm:degree-one-colour-no-go` of the spacetime–gauge duality paper (the last clause
of `thm:active-isotypic`): the populated categorical degree-one residual cannot
support a commuting internal colour factor `M₃(ℂ)`, and the same remains true after
adjoining one external-trivial private contrast line.

A "commuting internal colour factor" is a unital copy of `M₃(ℂ)` inside the
relative commutant of the external tetrahedral action, i.e. a unital `ℂ`-algebra
homomorphism `M₃(ℂ) →ₐ[ℂ] 𝒜'` (automatically injective, `M₃(ℂ)` being simple).

* `degreeOneCommutant`: the relative commutant of the relabeling action on the
  twelve-dimensional ordered-root carrier `E`, as a unital subalgebra; it has
  dimension `7` (`EdgeCommutantBasisExact.commutant_finrank_eq_seven`), so no unital
  `M₃(ℂ)` (dimension `9`) fits (`no_unital_M3_degreeOne`).
* `privateLineCommutant`: the relative commutant on the thirteen-dimensional carrier
  `E ⊕ ℂ` with the action extended trivially on the private line.  Here the paper's
  census gives `M₂ ⊕ M₂ ⊕ ℂ ⊕ ℂ`; we obtain the obstruction directly from the
  representation-dimension divisibility `matrix_representation_dimension`: a unital
  copy of `M₃(ℂ)` inside `M₁₃(ℂ)` would force `3 ∣ 13`
  (`no_unital_M3_privateLine`, via the general `no_unital_M3_of_card_not_dvd`).
* `degree_one_colour_no_go`: both clauses together.
-/

open Matrix Module RenewalGeometry.ActiveResidual RenewalGeometry.EdgeCommutant

namespace RenewalGeometry
namespace DegreeOneColourNoGo

/-! ### The degree-one carrier -/

/-- The relative commutant of the tetrahedral relabeling action on the ordered-root
carrier, as a unital subalgebra of `M_E(ℂ)`. -/
def degreeOneCommutant : Subalgebra ℂ (Matrix E E ℂ) :=
  Subalgebra.centralizer ℂ (Set.range Pm)

theorem mem_degreeOneCommutant {X : Matrix E E ℂ} :
    X ∈ degreeOneCommutant ↔ ∀ σ : Equiv.Perm V, X * Pm σ = Pm σ * X := by
  rw [degreeOneCommutant, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h σ
    exact (h (Pm σ) ⟨σ, rfl⟩).symm
  · rintro h _ ⟨σ, rfl⟩
    exact (h σ).symm

/-- The commutant subalgebra embeds linearly into the commutant submodule of
`EdgeCommutantDimensionExact`. -/
def toCommutantSubmodule : degreeOneCommutant →ₗ[ℂ] commutantSubmodule where
  toFun X := ⟨X.1, mem_degreeOneCommutant.mp X.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toCommutantSubmodule_injective : Function.Injective toCommutantSubmodule := by
  intro X Y h
  exact Subtype.ext (congrArg (fun Z : commutantSubmodule => (Z : Matrix E E ℂ)) h)

/-- The degree-one commutant has dimension at most seven. -/
theorem finrank_degreeOneCommutant_le : finrank ℂ degreeOneCommutant ≤ 7 := by
  have h := LinearMap.finrank_le_finrank_of_injective toCommutantSubmodule_injective
  rw [EdgeCommutantBasis.commutant_finrank_eq_seven] at h
  exact h

instance : Nonempty E := ⟨ActiveResidual.e01⟩

instance : Nontrivial degreeOneCommutant :=
  ⟨⟨0, 1, fun h => zero_ne_one (α := Matrix E E ℂ) (Subtype.ext_iff.mp h)⟩⟩

theorem finrank_M3 : finrank ℂ (Matrix (Fin 3) (Fin 3) ℂ) = 9 := by
  rw [Module.finrank_matrix, Module.finrank_self]
  simp

/-- A unital algebra map out of `M₃(ℂ)` into a nontrivial algebra is injective
(`M₃(ℂ)` is simple). -/
theorem algHom_M3_injective {B : Type*} [Ring B] [Algebra ℂ B] [Nontrivial B]
    (f : Matrix (Fin 3) (Fin 3) ℂ →ₐ[ℂ] B) : Function.Injective f :=
  RingHom.injective f.toRingHom

/-- **First clause**: the degree-one relative commutant contains no unital copy of
`M₃(ℂ)`. -/
theorem no_unital_M3_degreeOne
    (f : Matrix (Fin 3) (Fin 3) ℂ →ₐ[ℂ] degreeOneCommutant) : False := by
  have hinj : Function.Injective f := algHom_M3_injective f
  have h9 := LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hinj
  rw [finrank_M3] at h9
  have := finrank_degreeOneCommutant_le
  omega

/-! ### One external-trivial private contrast line -/

/-- The carrier `E ⊕ ℂ`: the ordered roots plus one private line. -/
abbrev Eplus := E ⊕ Unit

/-- The relabeling action extended trivially on the private line. -/
def PmPlus (σ : Equiv.Perm V) : Matrix Eplus Eplus ℂ :=
  Matrix.fromBlocks (Pm σ) 0 0 1

/-- The relative commutant of the extended action on `E ⊕ ℂ`. -/
def privateLineCommutant : Subalgebra ℂ (Matrix Eplus Eplus ℂ) :=
  Subalgebra.centralizer ℂ (Set.range PmPlus)

theorem card_E : Fintype.card E = 12 := by decide

theorem card_Eplus : Fintype.card Eplus = 13 := by
  rw [Fintype.card_sum, card_E, Fintype.card_unit]

/-- **Representation-dimension obstruction**: a carrier whose dimension is not
divisible by `3` admits no unital copy of `M₃(ℂ)` in its matrix algebra, hence in
no subalgebra of it. -/
theorem no_unital_M3_of_card_not_dvd {m : Type*} [Fintype m] [DecidableEq m]
    (hm : ¬ 3 ∣ Fintype.card m)
    (f : Matrix (Fin 3) (Fin 3) ℂ →ₐ[ℂ] Matrix m m ℂ) : False := by
  let g : Matrix (Fin 3) (Fin 3) ℂ →ₐ[ℂ]
      Matrix (Fin (Fintype.card m)) (Fin (Fintype.card m)) ℂ :=
    (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin m)).toAlgHom.comp f
  obtain ⟨k, hk⟩ := matrix_representation_dimension g
  exact hm ⟨k, hk⟩

/-- **Second clause**: after adjoining one external-trivial private line, the
relative commutant still contains no unital copy of `M₃(ℂ)`. -/
theorem no_unital_M3_privateLine
    (f : Matrix (Fin 3) (Fin 3) ℂ →ₐ[ℂ] privateLineCommutant) : False :=
  no_unital_M3_of_card_not_dvd (m := Eplus)
    (by rw [card_Eplus]; decide) (privateLineCommutant.val.comp f)

/-- **The degree-one internal-colour obstruction** (`thm:degree-one-colour-no-go`):
neither the degree-one relative commutant nor its enlargement by one
external-trivial private contrast line contains a unital copy of `M₃(ℂ)`. -/
theorem degree_one_colour_no_go :
    (¬ ∃ _ : Matrix (Fin 3) (Fin 3) ℂ →ₐ[ℂ] degreeOneCommutant, True) ∧
    (¬ ∃ _ : Matrix (Fin 3) (Fin 3) ℂ →ₐ[ℂ] privateLineCommutant, True) :=
  ⟨fun ⟨f, _⟩ => no_unital_M3_degreeOne f, fun ⟨f, _⟩ => no_unital_M3_privateLine f⟩

end DegreeOneColourNoGo
end RenewalGeometry
