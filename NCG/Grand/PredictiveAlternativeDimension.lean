/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.InfiniteHankelRankAlternative
import NCG.Grand.GeneratedMinimalRecord
import NCG.Grand.HankelMinimality

/-!
# Hankel rank is the canonical predictor dimension

This closes the dimension-identification step in
`thm:predictive-alternative`: a finite Hankel table has rank exactly the
dimension of its intrinsic response-space realization, and every reachable,
future-separated realization of that table has the same dimension.
-/

open Matrix

namespace NCG

/-- A finite operational table regarded as its Hankel matrix. -/
def finiteHankelMatrix {P F : Type} (tbl : F → P → ℂ) : Matrix F P ℂ :=
  fun f p => tbl f p

/-- The rank of a finite Hankel table is exactly the dimension of its
canonical reachable response space. -/
theorem finiteHankel_rank_eq_response_finrank {P F : Type}
    [Fintype P] [Fintype F]
    (tbl : F → P → ℂ) :
    (finiteHankelMatrix tbl).rank =
      Module.finrank ℂ (HankelResponseSpace tbl) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  rfl

/-- Every reachable and future-separated finite-dimensional realization has
dimension equal to the Hankel rank; the canonical similarity supplies the
uniqueness up to one linear equivalence. -/
theorem reachable_separated_predictor_dimension {P F N : Type}
    [Fintype P] [Fintype F]
    [AddCommGroup N] [Module ℂ N]
    (tbl : F → P → ℂ) (state : P → N)
    (read : F → N →ₗ[ℂ] ℂ)
    (hmatch : ∀ f p, read f (state p) = tbl f p)
    (hreach : Submodule.span ℂ (Set.range state) = ⊤)
    (hsep : ∀ v : N, (∀ f, read f v = 0) → v = 0) :
    Module.finrank ℂ N = (finiteHankelMatrix tbl).rank := by
  let canonicalState : P → HankelResponseSpace tbl := hankelColumn tbl
  let canonicalRead : F → HankelResponseSpace tbl →ₗ[ℂ] ℂ := fun f =>
    { toFun := fun v => v.1 f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcanonicalMatch : ∀ f p,
      canonicalRead f (canonicalState p) = tbl f p := by
    intro f p
    rfl
  have hcanonicalReach :
      Submodule.span ℂ (Set.range canonicalState) = ⊤ := by
    exact (typed_hankel_realization_exact tbl tbl id id
      (fun _ _ => rfl)).choose_spec.2.2.2.1
  have hcanonicalSep : ∀ v : HankelResponseSpace tbl,
      (∀ f, canonicalRead f v = 0) → v = 0 := by
    intro v hv
    apply Subtype.ext
    funext f
    exact hv f
  let e := minimalRealizationSimilarity tbl state canonicalState read canonicalRead
    hmatch hcanonicalMatch hreach hcanonicalReach hsep hcanonicalSep
  calc
    Module.finrank ℂ N = Module.finrank ℂ (HankelResponseSpace tbl) :=
      e.finrank_eq
    _ = (finiteHankelMatrix tbl).rank :=
      (finiteHankel_rank_eq_response_finrank tbl).symm

/-- Predictor-dimension assembly for the finite branch of the exhaustive
panel alternative. -/
theorem finite_predictive_branch_dimension {P F N : Type}
    [Fintype P] [Fintype F]
    [AddCommGroup N] [Module ℂ N]
    (tbl : F → P → ℂ) (state : P → N)
    (read : F → N →ₗ[ℂ] ℂ)
    (hmatch : ∀ f p, read f (state p) = tbl f p)
    (hreach : Submodule.span ℂ (Set.range state) = ⊤)
    (hsep : ∀ v : N, (∀ f, read f v = 0) → v = 0) :
    (finiteHankelMatrix tbl).rank =
        Module.finrank ℂ (HankelResponseSpace tbl)
    ∧ Module.finrank ℂ N = (finiteHankelMatrix tbl).rank :=
  ⟨finiteHankel_rank_eq_response_finrank tbl,
    reachable_separated_predictor_dimension tbl state read
      hmatch hreach hsep⟩

end NCG
