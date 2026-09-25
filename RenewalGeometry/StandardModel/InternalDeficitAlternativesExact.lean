/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.InternalAssemblyExact
import RenewalGeometry.StandardModel.CentralSeparationExact

/-!
# Exact internal-algebra deficit alternatives

`thm:internal-deficit-alternatives` of the spacetime–gauge duality paper, on the
census carrier `ℂ³ ⊕ ℂ² ⊕ ℂ ⊕ ℂ = ℂ⁷` of `InternalAssemblyExact` (colour block
`{0,1,2}` with type line `0` and private plane `{1,2}`, weak plane `{3,4}`, scalar
sectors `{5}`, `{6}`).

The represented internal words are: the type-line projection `E₀₀`, the private
matrix units (so the colour three-space initially carries `M₂ ⊕ ℂ`), one weak
rank-one projection `E₃₃` (coordinates chosen so that `t = e₃`), the independent
central supports of the colour, weak and two scalar sectors, together with an
optional colour-supported bridge word `u` (with `uᴴ`) and an optional second weak
rank-one projection `|h⟩⟨h|` (the weak router, with `0 < |⟨t,h⟩| < 1`, i.e.
`h₃ ≠ 0 ≠ h₄`).  The unital algebra `𝒜` they generate has exactly the dimensions

| represented internal words                | `dim_ℂ 𝒜` |
|-------------------------------------------|-----------|
| neither colour bridge nor weak router     |  `9`      |
| weak router but no colour bridge          | `11`      |
| colour bridge but no weak router          | `13`      |
| both bridge and router                    | `15`      |

(`finrank_neither`, `finrank_router_only`, `finrank_bridge_only`,
`finrank_both`, assembled in `internal_deficit_alternatives`), where "bridge"
means `ω_col(u) > 0` (`InternalAssembly.omega7`) and "no bridge" means
`ω_col(u) = 0` (absence of a bridge word is the case `u = 0`).  The terminal
value `15` is equivalent to saturation `𝒜 = M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` of the full block
algebra (`saturation_iff_finrank`), the algebra of `thm:internal-seed-saturation`.
The scalar-locked `14`-dimensional branch of a blockwise-surjective bank without
independent scalar supports is `CentralSeparationExact.lockedAlgebra`
(`thm:central-separation`).

Method: in each case the generated algebra equals the pattern algebra of a block
partition `β : Fin 7 → Fin m` (`patternAlgebra β`, matrices vanishing off the
diagonal blocks of `β`), whose dimension is the number of same-block index pairs
(`finrank_patternAlgebra`): the generators lie in it, and every matrix unit of the
pattern is generated (`colour_units_of_bridge`, `weak_units_of_router`).
-/

open Finset Matrix
open RenewalGeometry.InternalAssembly (blockOf blockAlgebra ColourSupported omega7 omega7_nonneg)
open RenewalGeometry.CentralSeparation (supportedOn finrank_supportedOn finrank_blockAlgebra)

namespace RenewalGeometry
namespace InternalDeficit

/-! ### Pattern algebras -/

/-- The block-diagonal algebra of a partition `β` of the seven coordinates. -/
def patternAlgebra {m : ℕ} (β : Fin 7 → Fin m) : Subalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ) where
  carrier := {X | ∀ i j, β i ≠ β j → X i j = 0}
  zero_mem' := fun i j _ => rfl
  one_mem' := fun i j hij => by
    rw [Matrix.one_apply, if_neg (fun hc => hij (by rw [hc]))]
  add_mem' := fun {X Y} hX hY i j hij => by
    rw [Matrix.add_apply, hX i j hij, hY i j hij, add_zero]
  mul_mem' := fun {X Y} hX hY i j hij => by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : β i = β k
    · rw [hY k j (fun hc => hij (hk.trans hc)), mul_zero]
    · rw [hX i k hk, zero_mul]
  algebraMap_mem' := fun c i j hij => by
    rw [Matrix.algebraMap_matrix_apply, if_neg (fun hc => hij (by rw [hc]))]

theorem mem_patternAlgebra {m : ℕ} {β : Fin 7 → Fin m} {X : Matrix (Fin 7) (Fin 7) ℂ} :
    X ∈ patternAlgebra β ↔ ∀ i j, β i ≠ β j → X i j = 0 := Iff.rfl

theorem single_mem_patternAlgebra {m : ℕ} {β : Fin 7 → Fin m} {i j : Fin 7} (h : β i = β j)
    (c : ℂ) : Matrix.single i j c ∈ patternAlgebra β := by
  intro a b hab
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hab h

/-- The same-block pairs of a partition. -/
def patternPairs {m : ℕ} (β : Fin 7 → Fin m) : Finset (Fin 7 × Fin 7) :=
  Finset.univ.filter fun p => β p.1 = β p.2

theorem toSubmodule_patternAlgebra {m : ℕ} (β : Fin 7 → Fin m) :
    Subalgebra.toSubmodule (patternAlgebra β) = supportedOn (patternPairs β) := by
  ext X
  rw [Subalgebra.mem_toSubmodule, CentralSeparation.mem_supportedOn]
  change (∀ i j, β i ≠ β j → X i j = 0) ↔ _
  simp [patternPairs, Finset.mem_filter]

theorem finrank_patternAlgebra {m : ℕ} (β : Fin 7 → Fin m) :
    Module.finrank ℂ (patternAlgebra β) = (patternPairs β).card := by
  rw [← Subalgebra.finrank_toSubmodule, toSubmodule_patternAlgebra, finrank_supportedOn]

/-- A subalgebra containing all matrix units of a pattern contains the pattern
algebra. -/
theorem patternAlgebra_le_of_units {m : ℕ} {β : Fin 7 → Fin m}
    {A : Subalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ)}
    (hunits : ∀ i j, β i = β j → Matrix.single i j (1 : ℂ) ∈ A) :
    patternAlgebra β ≤ A := by
  intro X hX
  rw [Matrix.matrix_eq_sum_single X]
  refine A.sum_mem fun i _ => A.sum_mem fun j _ => ?_
  by_cases hb : β i = β j
  · rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j 1 from by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]]
    exact A.smul_mem (hunits i j hb) _
  · rw [hX i j hb, Matrix.single_zero]
    exact A.zero_mem

/-- The block algebra of `InternalAssemblyExact` is the pattern algebra of
`blockOf`. -/
theorem blockAlgebra_eq_patternAlgebra : blockAlgebra = patternAlgebra blockOf := rfl

/-! ### The represented words -/

/-- The words always represented: type line, private units, one weak projection,
the central supports of the four sectors, and the scalar sectors. -/
def baseGens : Set (Matrix (Fin 7) (Fin 7) ℂ) :=
  {Matrix.single 0 0 1, Matrix.single 1 1 1, Matrix.single 1 2 1, Matrix.single 2 1 1,
   Matrix.single 2 2 1, Matrix.single 3 3 1,
   Matrix.single 3 3 1 + Matrix.single 4 4 1,
   Matrix.single 5 5 1, Matrix.single 6 6 1}

/-- The bridge word and its adjoint. -/
def bridgeGens (u : Matrix (Fin 7) (Fin 7) ℂ) : Set (Matrix (Fin 7) (Fin 7) ℂ) := {u, uᴴ}

/-- The weak router: the rank-one projection `|h⟩⟨h|` on the weak plane. -/
def routerGen (h : Fin 7 → ℂ) : Set (Matrix (Fin 7) (Fin 7) ℂ) :=
  {Matrix.vecMulVec h (star h)}

/-- Weak support of the router vector: `h` lives on the weak plane `{3,4}`. -/
def WeakSupported (h : Fin 7 → ℂ) : Prop := ∀ i, blockOf i ≠ 1 → h i = 0

/-- The router is nonorthogonal to and distinct from `t = e₃`: `0 < |⟨t,h⟩| < 1`
for a unit vector on the weak plane, i.e. both weak coordinates are nonzero. -/
def Router (h : Fin 7 → ℂ) : Prop := WeakSupported h ∧ h 3 ≠ 0 ∧ h 4 ≠ 0

/-! ### Generation of the nonabelian blocks -/

section Generation

variable {A : Subalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ)}

theorem step {a b c : Fin 7} (hab : Matrix.single a b (1 : ℂ) ∈ A)
    (hbc : Matrix.single b c (1 : ℂ) ∈ A) : Matrix.single a c (1 : ℂ) ∈ A := by
  have h1 := mul_mem hab hbc
  rwa [Matrix.single_mul_single_same, one_mul] at h1

theorem extract {u : Matrix (Fin 7) (Fin 7) ℂ} (hu : u ∈ A) {i j : Fin 7}
    (hii : Matrix.single i i (1 : ℂ) ∈ A) (hjj : Matrix.single j j (1 : ℂ) ∈ A)
    (hne : u i j ≠ 0) : Matrix.single i j (1 : ℂ) ∈ A := by
  have h1 : Matrix.single i i (1 : ℂ) * u * Matrix.single j j 1 ∈ A :=
    mul_mem (mul_mem hii hu) hjj
  rw [Matrix.single_mul_mul_single] at h1
  have h2 := A.smul_mem h1 (u i j)⁻¹
  rwa [Matrix.smul_single, smul_eq_mul, one_mul, mul_one, inv_mul_cancel₀ hne] at h2

/-- **Colour-block generation** (`thm:colour-bridge`, as in
`InternalAssembly.assembled_dichotomy`): the type line, the private units and a
colour-supported word with `ω_col(u) > 0` (with its adjoint) generate all nine
colour matrix units. -/
theorem colour_units_of_bridge {u : Matrix (Fin 7) (Fin 7) ℂ} (hpos : 0 < omega7 u)
    (hu : u ∈ A) (huH : uᴴ ∈ A)
    (h00 : Matrix.single (0 : Fin 7) 0 (1 : ℂ) ∈ A) (h11 : Matrix.single (1 : Fin 7) 1 (1 : ℂ) ∈ A)
    (h12 : Matrix.single (1 : Fin 7) 2 (1 : ℂ) ∈ A) (h21 : Matrix.single (2 : Fin 7) 1 (1 : ℂ) ∈ A)
    (h22 : Matrix.single (2 : Fin 7) 2 (1 : ℂ) ∈ A) :
    ∀ i j : Fin 7, blockOf i = 0 → blockOf j = 0 → Matrix.single i j (1 : ℂ) ∈ A := by
  have hcase : u 1 0 ≠ 0 ∨ u 2 0 ≠ 0 ∨ u 0 1 ≠ 0 ∨ u 0 2 ≠ 0 := by
    by_contra hall
    rw [not_or, not_or, not_or, not_not, not_not, not_not, not_not] at hall
    obtain ⟨h1, h2, h3, h4⟩ := hall
    rw [omega7, h1, h2, h3, h4] at hpos
    simp at hpos
  have hextractH : ∀ i j : Fin 7, Matrix.single i i (1 : ℂ) ∈ A →
      Matrix.single j j (1 : ℂ) ∈ A → u j i ≠ 0 → Matrix.single i j (1 : ℂ) ∈ A := by
    intro i j hii hjj hne
    refine extract huH hii hjj ?_
    rw [Matrix.conjTranspose_apply]
    intro hc
    exact hne (by simpa using congrArg star hc)
  have hfinish : Matrix.single (0 : Fin 7) 1 (1 : ℂ) ∈ A →
      Matrix.single (0 : Fin 7) 2 (1 : ℂ) ∈ A →
      Matrix.single (1 : Fin 7) 0 (1 : ℂ) ∈ A →
      Matrix.single (2 : Fin 7) 0 (1 : ℂ) ∈ A →
      ∀ i j : Fin 7, blockOf i = 0 → blockOf j = 0 → Matrix.single i j (1 : ℂ) ∈ A := by
    intro h01 h02 h10 h20 i j hi hj
    fin_cases i <;> fin_cases j <;>
      first
        | exact h00 | exact h01 | exact h02 | exact h10 | exact h11
        | exact h12 | exact h20 | exact h21 | exact h22
        | exact absurd hi (by decide) | exact absurd hj (by decide)
  rcases hcase with h | h | h | h
  · have h10 := extract hu h11 h00 h
    have h01 := hextractH 0 1 h00 h11 h
    exact hfinish h01 (step h01 h12) h10 (step h21 h10)
  · have h20 := extract hu h22 h00 h
    have h02 := hextractH 0 2 h00 h22 h
    exact hfinish (step h02 h21) h02 (step h12 h20) h20
  · have h01 := extract hu h00 h11 h
    have h10 := hextractH 1 0 h11 h00 h
    exact hfinish h01 (step h01 h12) h10 (step h21 h10)
  · have h02 := extract hu h00 h22 h
    have h20 := hextractH 2 0 h22 h00 h
    exact hfinish (step h02 h21) h02 (step h12 h20) h20

/-- **Weak-block generation** (`lem:weak-M2`): the projection `E₃₃`, the weak
central support `E₃₃ + E₄₄` and a router projection `|h⟩⟨h|` with `h₃ ≠ 0 ≠ h₄`
generate all four weak matrix units. -/
theorem weak_units_of_router {h : Fin 7 → ℂ} (hr : Router h)
    (hP : Matrix.vecMulVec h (star h) ∈ A)
    (h33 : Matrix.single (3 : Fin 7) 3 (1 : ℂ) ∈ A)
    (hW : Matrix.single (3 : Fin 7) 3 (1 : ℂ) + Matrix.single 4 4 1 ∈ A) :
    ∀ i j : Fin 7, blockOf i = 1 → blockOf j = 1 → Matrix.single i j (1 : ℂ) ∈ A := by
  have h44 : Matrix.single (4 : Fin 7) 4 (1 : ℂ) ∈ A := by
    have := A.sub_mem hW h33
    rwa [add_sub_cancel_left] at this
  have h34 : Matrix.single (3 : Fin 7) 4 (1 : ℂ) ∈ A := by
    refine extract hP h33 h44 ?_
    rw [Matrix.vecMulVec_apply, Pi.star_apply]
    exact mul_ne_zero hr.2.1 (star_ne_zero.mpr hr.2.2)
  have h43 : Matrix.single (4 : Fin 7) 3 (1 : ℂ) ∈ A := by
    refine extract hP h44 h33 ?_
    rw [Matrix.vecMulVec_apply, Pi.star_apply]
    exact mul_ne_zero hr.2.2 (star_ne_zero.mpr hr.2.1)
  intro i j hi hj
  fin_cases i <;> fin_cases j <;>
    first
      | exact h33 | exact h34 | exact h43 | exact h44
      | exact absurd hi (by decide) | exact absurd hj (by decide)

end Generation

/-! ### Membership of the words in the pattern algebras -/

/-- With `ω_col(u) = 0` the four bridge entries vanish. -/
theorem bridge_entries_of_omega_zero {u : Matrix (Fin 7) (Fin 7) ℂ} (h : omega7 u = 0) :
    u 1 0 = 0 ∧ u 2 0 = 0 ∧ u 0 1 = 0 ∧ u 0 2 = 0 := by
  have h1 := Complex.normSq_nonneg (u 1 0)
  have h2 := Complex.normSq_nonneg (u 2 0)
  have h3 := Complex.normSq_nonneg (u 0 1)
  have h4 := Complex.normSq_nonneg (u 0 2)
  rw [omega7] at h
  exact ⟨Complex.normSq_eq_zero.mp (by linarith), Complex.normSq_eq_zero.mp (by linarith),
    Complex.normSq_eq_zero.mp (by linarith), Complex.normSq_eq_zero.mp (by linarith)⟩

/-- A colour-supported word with `ω_col(u) = 0` lies in every pattern algebra whose
partition separates `0` from `{1,2}` but keeps `1, 2` together and is arbitrary
elsewhere — concretely, in the pattern algebra of any `β` with
`β 0 ≠ β 1`, `β 0 ≠ β 2`, `β 1 = β 2`. -/
theorem word_mem_pattern_of_omega_zero {m : ℕ} {β : Fin 7 → Fin m}
    (hβ : ∀ i j : Fin 7, blockOf i = 0 → blockOf j = 0 → β i ≠ β j →
      (i = 0 ∧ j ≠ 0) ∨ (i ≠ 0 ∧ j = 0))
    {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u) (h : omega7 u = 0) :
    u ∈ patternAlgebra β ∧ uᴴ ∈ patternAlgebra β := by
  obtain ⟨h10, h20, h01, h02⟩ := bridge_entries_of_omega_zero h
  have hcol : ∀ j : Fin 7, blockOf j = 0 → j ≠ 0 → j = 1 ∨ j = 2 := by decide
  have key : ∀ i j, β i ≠ β j → u i j = 0 := by
    intro i j hij
    by_cases hc : blockOf i = 0 ∧ blockOf j = 0
    · rcases hβ i j hc.1 hc.2 hij with ⟨rfl, hj⟩ | ⟨hi, rfl⟩
      · rcases hcol j hc.2 hj with rfl | rfl
        · exact h01
        · exact h02
      · rcases hcol i hc.1 hi with rfl | rfl
        · exact h10
        · exact h20
    · exact hsupp i j hc
  refine ⟨key, ?_⟩
  intro i j hij
  rw [Matrix.conjTranspose_apply, key j i (Ne.symm hij), star_zero]

/-- A colour-supported word lies in every pattern algebra whose partition keeps the
colour block together. -/
theorem word_mem_pattern_of_colourSupported {m : ℕ} {β : Fin 7 → Fin m}
    (hβ : ∀ i j : Fin 7, blockOf i = 0 → blockOf j = 0 → β i = β j)
    {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u) :
    u ∈ patternAlgebra β ∧ uᴴ ∈ patternAlgebra β := by
  have key : ∀ i j, β i ≠ β j → u i j = 0 := fun i j hij =>
    hsupp i j fun hc => hij (hβ i j hc.1 hc.2)
  refine ⟨key, ?_⟩
  intro i j hij
  rw [Matrix.conjTranspose_apply, key j i (Ne.symm hij), star_zero]

/-- A weakly supported router lies in every pattern algebra whose partition keeps
the weak plane together. -/
theorem router_mem_pattern {m : ℕ} {β : Fin 7 → Fin m}
    (hβ : ∀ i j : Fin 7, blockOf i = 1 → blockOf j = 1 → β i = β j)
    {h : Fin 7 → ℂ} (hw : WeakSupported h) :
    Matrix.vecMulVec h (star h) ∈ patternAlgebra β := by
  intro i j hij
  rw [Matrix.vecMulVec_apply, Pi.star_apply]
  by_cases hi : blockOf i = 1
  · by_cases hj : blockOf j = 1
    · exact absurd (hβ i j hi hj) hij
    · rw [hw j hj, star_zero, mul_zero]
  · rw [hw i hi, zero_mul]

/-- The base words lie in every pattern algebra whose partition keeps `1, 2`
together (they are otherwise diagonal). -/
theorem baseGens_subset_pattern {m : ℕ} {β : Fin 7 → Fin m} (h12 : β 1 = β 2) :
    baseGens ⊆ (patternAlgebra β : Set (Matrix (Fin 7) (Fin 7) ℂ)) := by
  intro X hX
  simp only [baseGens, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact single_mem_patternAlgebra rfl 1
  · exact single_mem_patternAlgebra rfl 1
  · exact single_mem_patternAlgebra h12 1
  · exact single_mem_patternAlgebra h12.symm 1
  · exact single_mem_patternAlgebra rfl 1
  · exact single_mem_patternAlgebra rfl 1
  · exact (patternAlgebra β).add_mem (single_mem_patternAlgebra rfl 1)
      (single_mem_patternAlgebra rfl 1)
  · exact single_mem_patternAlgebra rfl 1
  · exact single_mem_patternAlgebra rfl 1

/-! ### The four partitions -/

/-- Neither bridge nor router: `{0} {1,2} {3} {4} {5} {6}`. -/
def βneither : Fin 7 → Fin 6 := ![0, 1, 1, 2, 3, 4, 5]

/-- Router but no bridge: `{0} {1,2} {3,4} {5} {6}`. -/
def βrouter : Fin 7 → Fin 5 := ![0, 1, 1, 2, 2, 3, 4]

/-- Bridge but no router: `{0,1,2} {3} {4} {5} {6}`. -/
def βbridge : Fin 7 → Fin 5 := ![0, 0, 0, 1, 2, 3, 4]

theorem card_βneither : (patternPairs βneither).card = 9 := by decide

theorem card_βrouter : (patternPairs βrouter).card = 11 := by decide

theorem card_βbridge : (patternPairs βbridge).card = 13 := by decide

/-! ### Base membership in the generated algebra -/

section Base

variable {S : Set (Matrix (Fin 7) (Fin 7) ℂ)} (hS : baseGens ⊆ S)

include hS

theorem base00 : Matrix.single (0 : Fin 7) 0 (1 : ℂ) ∈ Algebra.adjoin ℂ S :=
  Algebra.subset_adjoin (hS (by simp [baseGens]))
theorem base11 : Matrix.single (1 : Fin 7) 1 (1 : ℂ) ∈ Algebra.adjoin ℂ S :=
  Algebra.subset_adjoin (hS (by simp [baseGens]))
theorem base12 : Matrix.single (1 : Fin 7) 2 (1 : ℂ) ∈ Algebra.adjoin ℂ S :=
  Algebra.subset_adjoin (hS (by simp [baseGens]))
theorem base21 : Matrix.single (2 : Fin 7) 1 (1 : ℂ) ∈ Algebra.adjoin ℂ S :=
  Algebra.subset_adjoin (hS (by simp [baseGens]))
theorem base22 : Matrix.single (2 : Fin 7) 2 (1 : ℂ) ∈ Algebra.adjoin ℂ S :=
  Algebra.subset_adjoin (hS (by simp [baseGens]))
theorem base33 : Matrix.single (3 : Fin 7) 3 (1 : ℂ) ∈ Algebra.adjoin ℂ S :=
  Algebra.subset_adjoin (hS (by simp [baseGens]))
theorem baseW : Matrix.single (3 : Fin 7) 3 (1 : ℂ) + Matrix.single 4 4 1 ∈ Algebra.adjoin ℂ S :=
  Algebra.subset_adjoin (hS (by simp [baseGens]))
theorem base44 : Matrix.single (4 : Fin 7) 4 (1 : ℂ) ∈ Algebra.adjoin ℂ S := by
  have := (Algebra.adjoin ℂ S).sub_mem (baseW hS) (base33 hS)
  rwa [add_sub_cancel_left] at this
theorem base55 : Matrix.single (5 : Fin 7) 5 (1 : ℂ) ∈ Algebra.adjoin ℂ S :=
  Algebra.subset_adjoin (hS (by simp [baseGens]))
theorem base66 : Matrix.single (6 : Fin 7) 6 (1 : ℂ) ∈ Algebra.adjoin ℂ S :=
  Algebra.subset_adjoin (hS (by simp [baseGens]))

end Base

/-! ### The four rows of the table -/

/-- **Row 1**: neither colour bridge nor weak router — dimension `9`. -/
theorem finrank_neither {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u)
    (h0 : omega7 u = 0) :
    Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u)) = 9 := by
  have hS : baseGens ⊆ baseGens ∪ bridgeGens u := Set.subset_union_left
  have heq : Algebra.adjoin ℂ (baseGens ∪ bridgeGens u) = patternAlgebra βneither := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro X (hX | hX)
      · exact baseGens_subset_pattern rfl hX
      · obtain ⟨hu, huH⟩ := word_mem_pattern_of_omega_zero (β := βneither) (by decide) hsupp h0
        rcases hX with rfl | rfl
        · exact hu
        · exact huH
    · apply patternAlgebra_le_of_units
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
          | exact base00 hS | exact base11 hS | exact base12 hS | exact base21 hS
          | exact base22 hS | exact base33 hS | exact base44 hS | exact base55 hS
          | exact base66 hS | exact absurd hij (by decide)
  rw [heq, finrank_patternAlgebra, card_βneither]

/-- **Row 2**: weak router but no colour bridge — dimension `11`. -/
theorem finrank_router_only {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u)
    (h0 : omega7 u = 0) {h : Fin 7 → ℂ} (hr : Router h) :
    Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h)) = 11 := by
  have hS : baseGens ⊆ baseGens ∪ bridgeGens u ∪ routerGen h :=
    Set.subset_union_left.trans Set.subset_union_left
  have hP : Matrix.vecMulVec h (star h) ∈ Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h) :=
    Algebra.subset_adjoin (Set.mem_union_right _ rfl)
  have hweak := weak_units_of_router hr hP (base33 hS) (baseW hS)
  have heq : Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h) = patternAlgebra βrouter := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro X ((hX | hX) | hX)
      · exact baseGens_subset_pattern rfl hX
      · obtain ⟨hu, huH⟩ := word_mem_pattern_of_omega_zero (β := βrouter) (by decide) hsupp h0
        rcases hX with rfl | rfl
        · exact hu
        · exact huH
      · rw [Set.mem_singleton_iff.mp hX]
        exact router_mem_pattern (by decide) hr.1
    · apply patternAlgebra_le_of_units
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
          | exact base00 hS | exact base11 hS | exact base12 hS | exact base21 hS
          | exact base22 hS | exact base55 hS | exact base66 hS
          | exact hweak _ _ rfl rfl | exact absurd hij (by decide)
  rw [heq, finrank_patternAlgebra, card_βrouter]

/-- **Row 3**: colour bridge but no weak router — dimension `13`. -/
theorem finrank_bridge_only {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u)
    (hpos : 0 < omega7 u) :
    Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u)) = 13 := by
  have hS : baseGens ⊆ baseGens ∪ bridgeGens u := Set.subset_union_left
  have hu : u ∈ Algebra.adjoin ℂ (baseGens ∪ bridgeGens u) :=
    Algebra.subset_adjoin (Set.mem_union_right _ (by simp [bridgeGens]))
  have huH : uᴴ ∈ Algebra.adjoin ℂ (baseGens ∪ bridgeGens u) :=
    Algebra.subset_adjoin (Set.mem_union_right _ (by simp [bridgeGens]))
  have hcol := colour_units_of_bridge hpos hu huH (base00 hS) (base11 hS) (base12 hS) (base21 hS)
    (base22 hS)
  have heq : Algebra.adjoin ℂ (baseGens ∪ bridgeGens u) = patternAlgebra βbridge := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro X (hX | hX)
      · exact baseGens_subset_pattern rfl hX
      · obtain ⟨hu', huH'⟩ := word_mem_pattern_of_colourSupported (β := βbridge) (by decide) hsupp
        rcases hX with rfl | rfl
        · exact hu'
        · exact huH'
    · apply patternAlgebra_le_of_units
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
          | exact hcol _ _ rfl rfl | exact base33 hS | exact base44 hS | exact base55 hS
          | exact base66 hS | exact absurd hij (by decide)
  rw [heq, finrank_patternAlgebra, card_βbridge]

/-- **Row 4**: both bridge and router — dimension `15`, the full block algebra. -/
theorem adjoin_both_eq_blockAlgebra {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u)
    (hpos : 0 < omega7 u) {h : Fin 7 → ℂ} (hr : Router h) :
    Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h) = blockAlgebra := by
  have hS : baseGens ⊆ baseGens ∪ bridgeGens u ∪ routerGen h :=
    Set.subset_union_left.trans Set.subset_union_left
  have hu : u ∈ Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h) :=
    Algebra.subset_adjoin (Set.mem_union_left _ (Set.mem_union_right _ (by simp [bridgeGens])))
  have huH : uᴴ ∈ Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h) :=
    Algebra.subset_adjoin (Set.mem_union_left _ (Set.mem_union_right _ (by simp [bridgeGens])))
  have hP : Matrix.vecMulVec h (star h) ∈ Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h) :=
    Algebra.subset_adjoin (Set.mem_union_right _ rfl)
  have hcol := colour_units_of_bridge hpos hu huH (base00 hS) (base11 hS) (base12 hS) (base21 hS)
    (base22 hS)
  have hweak := weak_units_of_router hr hP (base33 hS) (baseW hS)
  rw [blockAlgebra_eq_patternAlgebra]
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro X ((hX | hX) | hX)
    · exact baseGens_subset_pattern rfl hX
    · obtain ⟨hu', huH'⟩ := word_mem_pattern_of_colourSupported (β := blockOf) (by decide) hsupp
      rcases hX with rfl | rfl
      · exact hu'
      · exact huH'
    · rw [Set.mem_singleton_iff.mp hX]
      exact router_mem_pattern (by decide) hr.1
  · apply patternAlgebra_le_of_units
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact hcol _ _ rfl rfl | exact hweak _ _ rfl rfl | exact base55 hS
        | exact base66 hS | exact absurd hij (by decide)

theorem finrank_both {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u)
    (hpos : 0 < omega7 u) {h : Fin 7 → ℂ} (hr : Router h) :
    Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h)) = 15 := by
  rw [adjoin_both_eq_blockAlgebra hsupp hpos hr, finrank_blockAlgebra]

/-- The generated algebra always sits inside the block algebra. -/
theorem adjoin_le_blockAlgebra {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u)
    {h : Fin 7 → ℂ} (hw : WeakSupported h) :
    Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h) ≤ blockAlgebra := by
  rw [blockAlgebra_eq_patternAlgebra]
  apply Algebra.adjoin_le
  rintro X ((hX | hX) | hX)
  · exact baseGens_subset_pattern rfl hX
  · obtain ⟨hu', huH'⟩ := word_mem_pattern_of_colourSupported (β := blockOf) (by decide) hsupp
    rcases hX with rfl | rfl
    · exact hu'
    · exact huH'
  · rw [Set.mem_singleton_iff.mp hX]
    exact router_mem_pattern (by decide) hw

/-- **Terminal value `15` ⇔ saturation** of the complete relative commutant
`M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` (`thm:internal-seed-saturation`). -/
theorem saturation_iff_finrank {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u)
    {h : Fin 7 → ℂ} (hw : WeakSupported h) :
    Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h) = blockAlgebra ↔
      Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h)) = 15 := by
  constructor
  · intro heq; rw [heq, finrank_blockAlgebra]
  · intro hfin
    exact Subalgebra.eq_of_le_of_finrank_eq (adjoin_le_blockAlgebra hsupp hw)
      (hfin.trans finrank_blockAlgebra.symm)

/-- **`thm:internal-deficit-alternatives`**: the four rows of the dimension table
`9 / 11 / 13 / 15`, for a colour-supported word `u` (bridge iff `ω_col(u) > 0`)
and a weakly supported router vector `h` (router iff `h₃ ≠ 0 ≠ h₄`). -/
theorem internal_deficit_alternatives {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u)
    {h : Fin 7 → ℂ} :
    (omega7 u = 0 → Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u)) = 9) ∧
    (omega7 u = 0 → Router h →
      Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h)) = 11) ∧
    (0 < omega7 u → Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u)) = 13) ∧
    (0 < omega7 u → Router h →
      Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h)) = 15) :=
  ⟨fun h0 => finrank_neither hsupp h0, fun h0 hr => finrank_router_only hsupp h0 hr,
    fun hpos => finrank_bridge_only hsupp hpos, fun hpos hr => finrank_both hsupp hpos hr⟩


/-! ### The centre of the saturated algebra (`thm:internal-seed-saturation`) -/

open RenewalGeometry.CentralSeparation (centralProj centralProj_mul_apply centralProj_mem_blockAlgebra)

/-- The centre of the block algebra `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ`, as a subspace of `M₇(ℂ)`. -/
def centre : Submodule ℂ (Matrix (Fin 7) (Fin 7) ℂ) where
  carrier := {X | X ∈ blockAlgebra ∧ ∀ Y ∈ blockAlgebra, X * Y = Y * X}
  zero_mem' := ⟨blockAlgebra.zero_mem, fun Y _ => by simp⟩
  add_mem' := fun {X X'} hX hX' => ⟨blockAlgebra.add_mem hX.1 hX'.1, fun Y hY => by
    rw [Matrix.add_mul, Matrix.mul_add, hX.2 Y hY, hX'.2 Y hY]⟩
  smul_mem' := fun c {X} hX => ⟨blockAlgebra.smul_mem hX.1 c, fun Y hY => by
    rw [Matrix.smul_mul, Matrix.mul_smul, hX.2 Y hY]⟩

/-- A representative coordinate of each block. -/
def rep : Fin 4 → Fin 7 := ![0, 3, 5, 6]

theorem blockOf_rep : ∀ k, blockOf (rep k) = k := by decide

theorem centralProj_mem_centre (k : Fin 4) : centralProj k ∈ centre :=
  ⟨centralProj_mem_blockAlgebra k, fun Y hY => CentralSeparation.centralProj_comm hY k⟩

/-- Entries of `X * E_{ij}` and `E_{ij} * X`. -/
theorem mul_single_apply' (X : Matrix (Fin 7) (Fin 7) ℂ) (i j a b : Fin 7) :
    (X * Matrix.single i j (1 : ℂ)) a b = if b = j then X a i else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.single_apply, mul_ite, mul_one, mul_zero]
  by_cases hb : b = j
  · subst hb; simp
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg]
    rintro ⟨_, h⟩
    exact hb h.symm

theorem single_mul_apply' (X : Matrix (Fin 7) (Fin 7) ℂ) (i j a b : Fin 7) :
    (Matrix.single i j (1 : ℂ) * X) a b = if a = i then X j b else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.single_apply, ite_mul, one_mul, zero_mul]
  by_cases ha : a = i
  · subst ha; simp
  · rw [if_neg ha]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg]
    rintro ⟨h, _⟩
    exact ha h.symm

/-- A central element is diagonal and constant on each block:
`X = ∑_k X_{r_k r_k} P_k`. -/
theorem centre_eq_sum {X : Matrix (Fin 7) (Fin 7) ℂ} (hX : X ∈ centre) :
    X = ∑ k, X (rep k) (rep k) • centralProj k := by
  obtain ⟨hXb, hXc⟩ := hX
  have hoff : ∀ i j, i ≠ j → X i j = 0 := by
    intro i j hij
    by_cases hb : blockOf i = blockOf j
    · have := congrFun (congrFun (hXc _ (InternalAssembly.single_mem_blockAlgebra (rfl : blockOf j = blockOf j) 1)) i) j
      rw [mul_single_apply', single_mul_apply', if_pos rfl, if_neg hij] at this
      exact this
    · exact hXb i j hb
  have hdiag : ∀ i j, blockOf i = blockOf j → X i i = X j j := by
    intro i j hb
    have := congrFun (congrFun (hXc _ (InternalAssembly.single_mem_blockAlgebra hb 1)) i) j
    rw [mul_single_apply', single_mul_apply', if_pos rfl, if_pos rfl] at this
    exact this
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, centralProj, Matrix.diagonal_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single (blockOf i)]
    · rw [if_pos rfl, if_pos rfl]
      exact hdiag i (rep (blockOf i)) (blockOf_rep _).symm
    · intro k _ hk
      rw [if_neg (Ne.symm hk)]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [hoff i j hij]
    symm
    exact Finset.sum_eq_zero fun k _ => by simp [hij]

/-- Coordinates identify the centre with `ℂ⁴`. -/
def centreEquiv : centre ≃ₗ[ℂ] (Fin 4 → ℂ) where
  toFun X := fun k => X.1 (rep k) (rep k)
  map_add' X Y := by ext k; simp
  map_smul' c X := by ext k; simp
  invFun c := ⟨∑ k, c k • centralProj k, centre.sum_mem fun k _ =>
    centre.smul_mem _ (centralProj_mem_centre k)⟩
  left_inv X := by
    apply Subtype.ext
    exact (centre_eq_sum X.2).symm
  right_inv c := by
    ext k
    simp only [Matrix.sum_apply, Matrix.smul_apply, centralProj, Matrix.diagonal_apply,
      smul_eq_mul, if_true, blockOf_rep]
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **The centre of `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` has dimension four.** -/
theorem finrank_centre : Module.finrank ℂ centre = 4 := by
  rw [centreEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- **`thm:internal-seed-saturation`, concrete generation form.**  With the private
units and the type line (I1, colour part), a represented colour-supported word with
`ω_col > 0` (I1, bridge alternative), a weak router (I2), the two represented
multiplicity-one scalar sectors and the independent central supports (I3, I4; the
scalar projectors `E₅₅`, `E₆₆` discharge `η_cen > 0`), the generated word algebra
is exactly `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` (`blockAlgebra`), of dimension `15`, with a centre of
dimension `4`, and the two nonabelian blocks have `9` and `4` matrix entries.  The
identification of `blockAlgebra` with the external relative commutant `𝒜'_ext` at
census `(3,2,1,1)` (`thm:active-isotypic`) is not part of this statement. -/
theorem internal_seed_saturation_concrete {u : Matrix (Fin 7) (Fin 7) ℂ}
    (hsupp : ColourSupported u) (hpos : 0 < omega7 u) {h : Fin 7 → ℂ} (hr : Router h) :
    Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h) = blockAlgebra ∧
    Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h)) = 15 ∧
    Module.finrank ℂ centre = 4 ∧
    (Finset.univ.filter fun p : Fin 7 × Fin 7 => blockOf p.1 = 0 ∧ blockOf p.2 = 0).card = 9 ∧
    (Finset.univ.filter fun p : Fin 7 × Fin 7 => blockOf p.1 = 1 ∧ blockOf p.2 = 1).card = 4 :=
  ⟨adjoin_both_eq_blockAlgebra hsupp hpos hr, finrank_both hsupp hpos hr, finrank_centre,
    by decide, by decide⟩
end InternalDeficit
end RenewalGeometry
