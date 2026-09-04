/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteLatticeGaugeInvariantDensityExact

/-!
# Literal transport words and the finite holonomy matrix-entry algebra

Signed edge words are evaluated as chronological group products. Every
transport-word matrix entry is an explicit finite polynomial in edge entries
and their adjoints, and singleton words recover every edge entry. Therefore
the two generated star algebras coincide before any topological closure.
This establishes the concatenation/reversal layer, not the identification of
a restricted primitive current or plaquette bank with all edge entries.
-/

open scoped BigOperators

namespace NCG.HolonomyWordAlgebra

open FiniteLatticeGaugeInvariantDensity

noncomputable section

variable {E n : Type*} [Fintype E] [Fintype n] [DecidableEq n]
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G]
variable [FirstCountableTopology G] [SecondCountableTopology G]
variable [MeasurableSpace G] [BorelSpace G]
variable (rho : G →* Matrix n n ℂ) (hcontinuous : Continuous rho)

def letterValue (U : E → G) (a : E × Bool) : G :=
  if a.2 then U a.1 else (U a.1)⁻¹

def wordValue (U : E → G) : List (E × Bool) → G
  | [] => 1
  | a :: w => wordValue U w * letterValue G U a

theorem wordValue_append (U : E → G) (w v : List (E × Bool)) :
    wordValue G U (w ++ v) = wordValue G U v * wordValue G U w := by
  induction w with
  | nil => simp [wordValue]
  | cons a w ih => simp [wordValue, ih, mul_assoc]

theorem continuous_wordValue (w : List (E × Bool)) :
    Continuous (fun U : E → G => wordValue G U w) := by
  induction w with
  | nil => exact continuous_const
  | cons a w ih =>
    apply ih.mul
    rcases a with ⟨e, b⟩
    cases b <;> simp only [letterValue, Bool.false_eq_true, ↓reduceIte]
    · exact (continuous_apply e).inv
    · exact continuous_apply e

def wordEntry (w : List (E × Bool)) (i j : n) : C(E → G, ℂ) where
  toFun U := rho (wordValue G U w) i j
  continuous_toFun := (hcontinuous.comp (continuous_wordValue G w)).matrix_elem i j

theorem wordEntry_singleton (e : E) (i j : n) :
    wordEntry G rho hcontinuous [(e, true)] i j = matrixEntry G rho hcontinuous e i j := by
  ext U
  simp [wordEntry, wordValue, letterValue, matrixEntry]

theorem wordEntry_nil (i j : n) :
    wordEntry G rho hcontinuous [] i j =
      algebraMap ℂ C(E → G, ℂ) ((1 : Matrix n n ℂ) i j) := by
  ext U
  simp [wordEntry, wordValue]

theorem wordEntry_cons (a : E × Bool) (w : List (E × Bool)) (i j : n) :
    wordEntry G rho hcontinuous (a :: w) i j =
      ∑ k, wordEntry G rho hcontinuous w i k * wordEntry G rho hcontinuous [a] k j := by
  ext U
  simp [wordEntry, wordValue, map_mul, Matrix.mul_apply]

theorem wordEntry_inverse (hunitary : ∀ g, rho g⁻¹ = (rho g).conjTranspose)
    (e : E) (i j : n) :
    wordEntry G rho hcontinuous [(e, false)] i j =
      star (matrixEntry G rho hcontinuous e j i) := by
  ext U
  simp [wordEntry, wordValue, letterValue, hunitary, matrixEntry, Matrix.conjTranspose_apply]

theorem wordEntry_mem_matrixEntryAlgebra
    (hunitary : ∀ g, rho g⁻¹ = (rho g).conjTranspose)
    (w : List (E × Bool)) (i j : n) :
    wordEntry G rho hcontinuous w i j ∈ matrixEntryAlgebra (E := E) G rho hcontinuous := by
  have hedge (e : E) (i j : n) :
      matrixEntry G rho hcontinuous e i j ∈ matrixEntryAlgebra (E := E) G rho hcontinuous :=
    StarAlgebra.subset_adjoin ℂ _ ⟨(e, i, j), rfl⟩
  have hletter (a : E × Bool) (i j : n) :
      wordEntry G rho hcontinuous [a] i j ∈ matrixEntryAlgebra (E := E) G rho hcontinuous := by
    rcases a with ⟨e, b⟩
    cases b
    · rw [wordEntry_inverse G rho hcontinuous hunitary]
      exact star_mem (hedge e j i)
    · rw [wordEntry_singleton]
      exact hedge e i j
  induction w generalizing i j with
  | nil =>
    rw [wordEntry_nil]
    exact (matrixEntryAlgebra (E := E) G rho hcontinuous).algebraMap_mem _
  | cons a w ih =>
    rw [wordEntry_cons]
    exact (matrixEntryAlgebra (E := E) G rho hcontinuous).sum_mem fun k _ =>
      (matrixEntryAlgebra (E := E) G rho hcontinuous).mul_mem (ih i k) (hletter a k j)

def wordAlgebra : StarSubalgebra ℂ C(E → G, ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range fun a : List (E × Bool) × n × n =>
    wordEntry G rho hcontinuous a.1 a.2.1 a.2.2)

theorem wordAlgebra_eq_matrixEntryAlgebra
    (hunitary : ∀ g, rho g⁻¹ = (rho g).conjTranspose) :
    wordAlgebra (E := E) G rho hcontinuous = matrixEntryAlgebra (E := E) G rho hcontinuous := by
  apply le_antisymm
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨⟨w, i, j⟩, rfl⟩
    exact wordEntry_mem_matrixEntryAlgebra G rho hcontinuous hunitary w i j
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨⟨e, i, j⟩, rfl⟩
    change matrixEntry G rho hcontinuous e i j ∈ wordAlgebra G rho hcontinuous
    rw [← wordEntry_singleton]
    exact StarAlgebra.subset_adjoin ℂ _ ⟨([(e, true)], i, j), rfl⟩

theorem closure_gaugeAverage_wordAlgebra
    {V : Type*} [Fintype V] (target source : E → V)
    (hfaithful : Function.Injective rho)
    (hunitary : ∀ g, rho g⁻¹ = (rho g).conjTranspose) :
    closure (gaugeAverage G target source ''
      (wordAlgebra (E := E) G rho hcontinuous : Set C(E → G, ℂ))) =
      {f : C(E → G, ℂ) | ∀ h U, f (gaugeAction G target source h U) = f U} := by
  rw [wordAlgebra_eq_matrixEntryAlgebra G rho hcontinuous hunitary]
  exact closure_gaugeAverage_coordinateAlgebra G target source rho hcontinuous hfaithful

end

end NCG.HolonomyWordAlgebra
