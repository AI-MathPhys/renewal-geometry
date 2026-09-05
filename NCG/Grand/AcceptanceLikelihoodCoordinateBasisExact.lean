/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LikelihoodGaugeStripping

/-!
# Acceptance likelihood in the locked accepted-effect coordinates

The locked opportunity instrument assumes an independent accepted family.
Writing its accepted effects in that family's coefficient coordinates turns
them into the canonical coordinate basis.  This removes the formerly exposed
linear-independence argument from `cor:acceptance-likelihood` and proves the
corollary directly in the intrinsic accepted-effect coordinates.
-/

namespace NCG

/-- The coordinate effects of a finite accepted family are linearly
independent over the real score field. -/
theorem acceptanceCoordinateEffects_linearIndependent
    {J : Type*} [Fintype J] [DecidableEq J] :
    LinearIndependent ℝ (fun j : J => (Pi.single j 1 : J → ℝ)) := by
  convert (Pi.basisFun ℝ J).linearIndependent using 1
  funext j
  simp [Pi.basisFun_apply]

/-- `cor:acceptance-likelihood` in the intrinsic coefficient coordinates of
the locked independent accepted-effect family.  Scalar normalization on any
nonempty open tilt interval forces one common accepted score; if that score
differs from the rejected score, the unique affine gauge sends rejection to
zero and every accepted outcome to one. -/
theorem acceptance_likelihood_coordinate_basis_exact
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (s : J → ℝ) (sEmpty a b : ℝ) (hab : a < b) (w : ℝ → ℝ)
    (hscalar : ∀ q ∈ Set.Ioo a b,
      ∑ j, Real.exp (q * s j) • (Pi.single j 1 : J → ℝ) =
        w q • ∑ j, (Pi.single j 1 : J → ℝ))
    (hne : s (Classical.choice (inferInstance : Nonempty J)) ≠ sEmpty) :
    (∀ j k, s j = s k)
    ∧ let c := s (Classical.choice (inferInstance : Nonempty J))
       let normalizedEmpty := (sEmpty - sEmpty) / (c - sEmpty)
       let normalized := fun j => (s j - sEmpty) / (c - sEmpty)
       normalizedEmpty = 0 ∧ ∀ j, normalized j = 1 := by
  exact acceptance_likelihood_exact
    (fun j : J => (Pi.single j 1 : J → ℝ))
    acceptanceCoordinateEffects_linearIndependent
    s sEmpty a b hab w hscalar hne

end NCG
