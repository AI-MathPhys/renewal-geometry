/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NearbyProjectionRankStability
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Protected kernel ranks from projection convergence

Norm convergence of finite-rank protected orthogonal projections stabilizes
their dimensions.  If the limiting protected range is the continuum operator
kernel, this supplies exactly the eventual rank premise used by protected
finite-kernel rigidity.
-/

open Filter Topology

noncomputable section

namespace NCG.ProjectionStability

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace K F]

/-- Convergent finite-rank protected projections whose limiting range is an
operator kernel have the kernel dimension eventually. -/
theorem eventually_finrank_range_eq_kernel_of_tendsto
    (P : ℕ → H →L[K] H) (Plim : H →L[K] H) (A : H →L[K] F)
    (hconv : Tendsto P atTop (nhds Plim))
    (hstarP : ∀ᶠ n in atTop, IsStarProjection (P n))
    (hstarPlim : IsStarProjection Plim)
    (hfiniteP : ∀ᶠ n in atTop,
      Module.Finite K (LinearMap.range (P n).toLinearMap))
    [Module.Finite K (LinearMap.range Plim.toLinearMap)]
    (hlimitRange : LinearMap.range Plim.toLinearMap =
      LinearMap.ker A.toLinearMap) :
    ∀ᶠ n in atTop,
      Module.finrank K (LinearMap.range (P n).toLinearMap) =
        Module.finrank K (LinearMap.ker A.toLinearMap) := by
  have hrank := eventually_finrank_range_eq_of_tendsto
    P Plim hconv
      (hstarP.mono fun _ hn ↦
        ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr
          hn.isIdempotentElem)
      (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr
        hstarPlim.isIdempotentElem) hfiniteP
  filter_upwards [hrank] with n hn
  calc
    Module.finrank K (LinearMap.range (P n).toLinearMap) =
        Module.finrank K (LinearMap.range Plim.toLinearMap) := hn
    _ = Module.finrank K (LinearMap.ker A.toLinearMap) :=
      congrArg (fun S : Submodule K H ↦ Module.finrank K S) hlimitRange

end NCG.ProjectionStability
