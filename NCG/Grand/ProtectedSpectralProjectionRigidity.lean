/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NearbyProjectionRankStability
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Rigidity of protected and spectral projections

If a protected finite-rank range lies in a spectral range and their stabilized dimensions agree,
the two ranges coincide.  When both operators are orthogonal projections, equality of ranges
upgrades to equality of the projections.  This is the finite-rank kernel-locking step in the
continuum Howe argument.
-/

open Filter Topology

noncomputable section

open scoped InnerProduct
namespace NCG.ProjectionStability

universe u v

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]


/-- Eventual inclusion plus eventual equality of finite range dimensions forces eventual equality
of the ranges. -/
theorem eventually_range_eq_of_le_of_finrank_eq
    {I : Type*} {l : Filter I}
    (P Q : I → H →L[K] H)
    (hfiniteQ : ∀ i, Module.Finite K (LinearMap.range (Q i).toLinearMap))
    (hle : ∀ᶠ i in l,
      LinearMap.range (P i).toLinearMap ≤ LinearMap.range (Q i).toLinearMap)
    (hrank : ∀ᶠ i in l,
      Module.finrank K (LinearMap.range (P i).toLinearMap) =
        Module.finrank K (LinearMap.range (Q i).toLinearMap)) :
    ∀ᶠ i in l,
      LinearMap.range (P i).toLinearMap = LinearMap.range (Q i).toLinearMap := by
  filter_upwards [hle, hrank] with i hi hdim
  letI : Module.Finite K (LinearMap.range (Q i).toLinearMap) := hfiniteQ i
  exact Submodule.eq_of_le_of_finrank_eq hi hdim

/-- If protected and spectral orthogonal projections have the same eventual finite rank and the
protected range is included in the spectral range, the projections are eventually identical. -/
theorem protectedProjection_eventually_eq_spectralProjection
    [CompleteSpace H]
    {I : Type*} {l : Filter I}
    (P Q : I → H →L[K] H)
    (hstarP : ∀ᶠ i in l, IsStarProjection (P i))
    (hstarQ : ∀ᶠ i in l, IsStarProjection (Q i))
    (hfiniteQ : ∀ i, Module.Finite K (LinearMap.range (Q i).toLinearMap))
    (hle : ∀ᶠ i in l,
      LinearMap.range (P i).toLinearMap ≤ LinearMap.range (Q i).toLinearMap)
    (hrank : ∀ᶠ i in l,
      Module.finrank K (LinearMap.range (P i).toLinearMap) =
        Module.finrank K (LinearMap.range (Q i).toLinearMap)) :
    ∀ᶠ i in l, P i = Q i := by
  have hrange := eventually_range_eq_of_le_of_finrank_eq
    P Q hfiniteQ hle hrank
  filter_upwards [hstarP, hstarQ, hrange] with i hPi hQi hi
  exact ContinuousLinearMap.IsStarProjection.ext hPi hQi hi
/-- Orthogonal projections with eventually equal ranges are eventually equal as operators. -/
theorem orthogonalProjections_eventually_eq_of_range_eq
    [CompleteSpace H] {I : Type*} {l : Filter I}
    (P Q : I → H →L[K] H)
    (hstarP : ∀ᶠ i in l, IsStarProjection (P i))
    (hstarQ : ∀ᶠ i in l, IsStarProjection (Q i))
    (hrange : ∀ᶠ i in l,
      LinearMap.range (P i).toLinearMap = LinearMap.range (Q i).toLinearMap) :
    P =ᶠ[l] Q := by
  filter_upwards [hstarP, hstarQ, hrange] with i hPi hQi hi
  exact ContinuousLinearMap.IsStarProjection.ext hPi hQi hi

/-- If spectral orthogonal projections converge and protected orthogonal projections eventually
have the same ranges, then the protected projections converge to the same norm limit. -/
theorem protectedProjection_tendsto_of_eventually_range_eq
    [CompleteSpace H] {I : Type*} {l : Filter I}
    (P Q : I → H →L[K] H) (Qlim : H →L[K] H)
    (hstarP : ∀ᶠ i in l, IsStarProjection (P i))
    (hstarQ : ∀ᶠ i in l, IsStarProjection (Q i))
    (hrange : ∀ᶠ i in l,
      LinearMap.range (P i).toLinearMap = LinearMap.range (Q i).toLinearMap)
    (hQlim : Tendsto Q l (nhds Qlim)) :
    Tendsto P l (nhds Qlim) := by
  have heq := orthogonalProjections_eventually_eq_of_range_eq
    P Q hstarP hstarQ hrange
  exact hQlim.congr' (heq.mono fun _ hi ↦ hi.symm)


/-- Manuscript-facing stabilized-rank form: fixed protected rank, convergence-stable spectral
rank, and equality of the two limiting ranges force eventual equality of the cutoff projections. -/
theorem protectedProjection_eventually_eq_of_limitRange
    [CompleteSpace H]
    (P Q : ℕ → H →L[K] H) (Plim Qlim : H →L[K] H)
    (hstarP : ∀ n, IsStarProjection (P n))
    (hstarQ : ∀ᶠ n in atTop, IsStarProjection (Q n))
    (hfiniteQ : ∀ n, Module.Finite K (LinearMap.range (Q n).toLinearMap))
    (hle : ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap ≤ LinearMap.range (Q n).toLinearMap)
    (hprotectedRank : ∀ n,
      Module.finrank K (LinearMap.range (P n).toLinearMap) =
        Module.finrank K (LinearMap.range Plim.toLinearMap))
    (hspectralRank : ∀ᶠ n in atTop,
      Module.finrank K (LinearMap.range (Q n).toLinearMap) =
        Module.finrank K (LinearMap.range Qlim.toLinearMap))
    (hlimitRange : LinearMap.range Plim.toLinearMap =
      LinearMap.range Qlim.toLinearMap) :
    ∀ᶠ n in atTop, P n = Q n := by
  apply protectedProjection_eventually_eq_spectralProjection
    P Q (Filter.Eventually.of_forall hstarP) hstarQ hfiniteQ hle
  filter_upwards [hspectralRank] with n hn
  calc
    Module.finrank K (LinearMap.range (P n).toLinearMap) =
        Module.finrank K (LinearMap.range Plim.toLinearMap) := hprotectedRank n
    _ = Module.finrank K (LinearMap.range Qlim.toLinearMap) :=
      congrArg (fun S : Submodule K H => Module.finrank K S) hlimitRange
    _ = Module.finrank K (LinearMap.range (Q n).toLinearMap) := hn.symm

/-- Norm convergence of finite-rank spectral projections supplies the stabilized-rank premise
automatically.  Thus protected range inclusion and exactness of the limiting protected range
force eventual equality of the cutoff protected and spectral projections. -/
theorem protectedProjection_eventually_eq_of_tendsto
    [CompleteSpace H]
    (P Q : ℕ → H →L[K] H) (Plim Qlim : H →L[K] H)
    (hstarP : ∀ n, IsStarProjection (P n))
    (hstarQ : ∀ n, IsStarProjection (Q n))
    (hstarQlim : IsStarProjection Qlim)
    (hfiniteQ : ∀ n, Module.Finite K (LinearMap.range (Q n).toLinearMap))
    [Module.Finite K (LinearMap.range Qlim.toLinearMap)]
    (hQconv : Tendsto Q atTop (nhds Qlim))
    (hle : ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap ≤ LinearMap.range (Q n).toLinearMap)
    (hprotectedRank : ∀ n,
      Module.finrank K (LinearMap.range (P n).toLinearMap) =
        Module.finrank K (LinearMap.range Plim.toLinearMap))
    (hlimitRange : LinearMap.range Plim.toLinearMap =
      LinearMap.range Qlim.toLinearMap) :
    ∀ᶠ n in atTop, P n = Q n := by
  have hspectralRank :
      ∀ᶠ n in atTop,
        Module.finrank K (LinearMap.range (Q n).toLinearMap) =
          Module.finrank K (LinearMap.range Qlim.toLinearMap) :=
    eventually_finrank_range_eq_of_tendsto Q Qlim hQconv
      (Filter.Eventually.of_forall fun n =>
        (ContinuousLinearMap.IsStarProjection.isSymmetricProjection (hstarQ n)).isIdempotentElem)
      (ContinuousLinearMap.IsStarProjection.isSymmetricProjection hstarQlim).isIdempotentElem
      (Filter.Eventually.of_forall hfiniteQ)
  exact protectedProjection_eventually_eq_of_limitRange
    P Q Plim Qlim hstarP (Filter.Eventually.of_forall hstarQ)
      hfiniteQ hle hprotectedRank hspectralRank hlimitRange

end NCG.ProjectionStability
