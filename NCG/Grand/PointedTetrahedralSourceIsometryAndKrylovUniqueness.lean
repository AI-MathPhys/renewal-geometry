/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TerminatingSourceTest
import NCG.Grand.JointSourceRangeUnitary
import NCG.Grand.PhysicalSourceMinimality

/-!
# Pointed tetrahedral source isometry and Krylov uniqueness

This file closes the two converse/uniqueness clauses of the terminating
arithmetic--renewal source test.  The five real Gram parameters are encoded
explicitly, equality is shown equivalent to the unique label-fixing isometry
of source ranges, and source-minimality makes the transfer intertwiner unique.
-/

open Matrix

namespace NCG

/-- The five real parameters of a Hermitian pointed tetrahedral Gram:
three real scalars and one complex scalar. -/
structure PointedTetrahedralGramParameters where
  anchor : ℝ
  anchorVertex : ℂ
  vertexDiagonal : ℝ
  vertexOffDiagonal : ℝ

/-- The full `5 × 5` pointed tetrahedral Gram reconstructed from its five real
parameters.  Label `0` is the fixed anchor and labels `1,...,4` are the
tetrahedral orbit. -/
def pointedTetrahedralGramMatrix
    (p : PointedTetrahedralGramParameters) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.of fun i j =>
    if i = 0 then
      if j = 0 then p.anchor else p.anchorVertex
    else if j = 0 then star p.anchorVertex
    else if i = j then p.vertexDiagonal
    else p.vertexOffDiagonal

/-- No information is lost in the five-parameter reconstruction. -/
theorem pointedTetrahedralGramMatrix_injective :
    Function.Injective pointedTetrahedralGramMatrix := by
  intro p q h
  cases p with
  | mk pa pb pc pd =>
    cases q with
    | mk qa qb qc qd =>
      have ha := congrFun (congrFun h (0 : Fin 5)) (0 : Fin 5)
      have hb := congrFun (congrFun h (0 : Fin 5)) (1 : Fin 5)
      have hc := congrFun (congrFun h (1 : Fin 5)) (1 : Fin 5)
      have hd := congrFun (congrFun h (1 : Fin 5)) (2 : Fin 5)
      norm_num [pointedTetrahedralGramMatrix] at ha hb hc hd
      simp [show (2 : Fin 5) ≠ 0 by decide,
        show (1 : Fin 5) ≠ 2 by decide] at hd
      have ha' : pa = qa := by exact_mod_cast ha
      have hb' : pb = qb := hb
      have hc' : pc = qc := by exact_mod_cast hc
      have hd' : pd = qd := by exact_mod_cast hd
      cases ha'
      cases hb'
      cases hc'
      cases hd'
      rfl

/-- A label-fixing isometry is an isometric linear equivalence between the two
source ranges which sends every coefficient-labelled source vector to its
counterpart. -/
def HasUniqueLabelFixingRangeIsometry
    {h h' e : Type} [Fintype h] [Fintype h'] [Fintype e]
    (S : Matrix h e ℂ) (T : Matrix h' e ℂ) : Prop :=
  ∃! U : LinearMap.range S.mulVecLin ≃ₗ[ℂ]
      LinearMap.range T.mulVecLin,
    (∀ u : e → ℂ,
      U (S.mulVecLin.rangeRestrict u) = T.mulVecLin.rangeRestrict u)
    ∧ (∀ x y : LinearMap.range S.mulVecLin,
      star (x : h → ℂ) ⬝ᵥ (y : h → ℂ)
        = star (U x : h' → ℂ) ⬝ᵥ (U y : h' → ℂ))

/-- Conversely to the standard Gram construction, a label-fixing range
isometry forces equality of the complete source Grams. -/
theorem labelFixingRangeIsometry_gram_eq
    {h h' e : Type} [Fintype h] [Fintype h'] [Fintype e]
    (S : Matrix h e ℂ) (T : Matrix h' e ℂ)
    (hiso : HasUniqueLabelFixingRangeIsometry S T) :
    Sᴴ * S = Tᴴ * T := by
  classical
  obtain ⟨U, hU, -⟩ := hiso
  have hinner : ∀ u v : e → ℂ,
      star (S *ᵥ u) ⬝ᵥ (S *ᵥ v) =
        star (T *ᵥ u) ⬝ᵥ (T *ᵥ v) := by
    intro u v
    have h := hU.2 (S.mulVecLin.rangeRestrict u)
      (S.mulVecLin.rangeRestrict v)
    rw [hU.1 u, hU.1 v] at h
    exact h
  ext i j
  have h := hinner (Pi.single i 1) (Pi.single j 1)
  rw [gram_realization_inner, gram_realization_inner] at h
  simpa only [Pi.star_single, star_one, Matrix.mulVec_single_one,
    single_one_dotProduct, Matrix.col_apply] using h

/-- Equality of complete source Grams is equivalent to the unique
label-fixing isometry between their ranges. -/
theorem uniqueLabelFixingRangeIsometry_iff_gram_eq
    {h h' e : Type} [Fintype h] [Fintype h'] [Fintype e]
    (S : Matrix h e ℂ) (T : Matrix h' e ℂ) :
    HasUniqueLabelFixingRangeIsometry S T ↔ Sᴴ * S = Tᴴ * T := by
  constructor
  · exact labelFixingRangeIsometry_gram_eq S T
  · exact joint_source_unique_range_unitary S T

/-- Two pointed tetrahedral families are related by a unique label-fixing
range isometry exactly when their five Gram parameters agree. -/
theorem pointedTetrahedral_fiveParameters_iff_labelFixingIsometry
    {h h' : Type} [Fintype h] [Fintype h']
    (S : Matrix h (Fin 5) ℂ) (T : Matrix h' (Fin 5) ℂ)
    (p q : PointedTetrahedralGramParameters)
    (hS : Sᴴ * S = pointedTetrahedralGramMatrix p)
    (hT : Tᴴ * T = pointedTetrahedralGramMatrix q) :
    p = q ↔ HasUniqueLabelFixingRangeIsometry S T := by
  constructor
  · intro hp
    subst q
    apply (uniqueLabelFixingRangeIsometry_iff_gram_eq S T).2
    rw [hS, hT]
  · intro hiso
    apply pointedTetrahedralGramMatrix_injective
    rw [← hS, ← hT]
    exact labelFixingRangeIsometry_gram_eq S T hiso

/-- The finite Krylov intertwiner supplied by matching orbit panels is unique
on a source-minimal carrier. -/
theorem terminatingKrylov_sourceFixingIntertwiner_existsUnique
    {u p : Type*} [Fintype u] [Fintype p]
    [DecidableEq u] [DecidableEq p]
    (G G' : Matrix u u ℂ) (B B' : Matrix u p ℂ)
    (hG : Gᴴ = G) (hG' : G'ᴴ = G')
    (d : ℕ) (hd : 0 < d)
    (hmin : Function.Surjective (krylovMat G B d).mulVec)
    (hmom : ∀ n : ℕ, Bᴴ * G ^ n * B = B'ᴴ * G' ^ n * B') :
    ∃! W : Matrix u u ℂ,
      Wᴴ * W = 1 ∧ W * B = B' ∧ W * G = G' * W := by
  obtain ⟨W, hWu, hWB, hWG⟩ :=
    physical_source_uniqueness G G' B B' hG hG' d hd hmin hmom
  refine ⟨W, ⟨hWu, hWB, hWG⟩, ?_⟩
  intro V hV
  exact source_fixing_intertwiner_unique G G' B B' d hmin
    V W hV.2.1 hWB hV.2.2 hWG

end NCG
