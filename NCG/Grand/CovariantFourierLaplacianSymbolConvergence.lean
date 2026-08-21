/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CovariantFourierSymbolConvergence
import NCG.Grand.BanachAlgebraResolventStability

/-!
# Convergence of covariant Fourier Laplacian symbols

The positive directional multipliers are summed over finitely many lattice
directions.  Fixed-mode convergence therefore gives convergence of the full
`Σ Dⱼ†Dⱼ` symbol, uniformly on every fixed finite Fourier box.  Banach-algebra
inverse continuity then yields the corresponding finite-box resolvent
comparison and simultaneous eventual resolvent-set membership.
-/

open Filter NormedSpace Set Topology
open scoped BigOperators

namespace NCG

variable {A : Type} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℝ A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [IsScalarTower ℝ ℂ A] [StarRing A] [NormedStarGroup A]
variable {d : Type*} [Fintype d]

/-- Full finite-mesh positive covariant Laplacian symbol. -/
noncomputable def meshCovariantLaplacianSymbol
    (h : ℝ) (k : d → ℤ) (B : d → A) : A :=
  ∑ j, meshCovariantPositiveSymbol h (k j) (B j)

/-- Full continuum positive covariant Laplacian symbol. -/
noncomputable def continuumCovariantLaplacianSymbol
    (k : d → ℤ) (B : d → A) : A :=
  ∑ j, continuumCovariantPositiveSymbol (k j) (B j)

/-- The full positive symbol converges at every fixed multidimensional mode. -/
theorem meshCovariantLaplacianSymbol_tendsto_right
    (k : d → ℤ) (B : d → A) :
    Tendsto (fun h : ℝ => meshCovariantLaplacianSymbol h k B)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (continuumCovariantLaplacianSymbol k B)) := by
  classical
  unfold meshCovariantLaplacianSymbol continuumCovariantLaplacianSymbol
  exact tendsto_finset_sum _ fun j _ =>
    meshCovariantPositiveSymbol_tendsto_right (k j) (B j)

/-- Full Laplacian-symbol convergence is uniform on every fixed finite
multidimensional Fourier box. -/
theorem meshCovariantLaplacianSymbol_tendstoUniformlyOn_finset
    (s : Finset (d → ℤ)) (B : d → A) :
    TendstoUniformlyOn
      (fun h k => meshCovariantLaplacianSymbol h k B)
      (fun k => continuumCovariantLaplacianSymbol k B)
      (nhdsWithin 0 (Ioi 0)) (s : Set (d → ℤ)) :=
  tendstoUniformlyOn_finset_of_tendsto s fun k _ =>
    meshCovariantLaplacianSymbol_tendsto_right k B

/-- Every limit resolvent point remains a resolvent point of the fixed-mode
finite-mesh Laplacian symbol for all sufficiently small positive meshes. -/
theorem eventually_mem_resolventSet_meshCovariantLaplacianSymbol
    (k : d → ℤ) (B : d → A) (z : ℂ)
    (hz : z ∈ resolventSet ℂ
      (continuumCovariantLaplacianSymbol k B)) :
    ∀ᶠ h : ℝ in nhdsWithin 0 (Ioi 0),
      z ∈ resolventSet ℂ
        (meshCovariantLaplacianSymbol h k B) :=
  ResolventStability.eventually_mem_resolventSet_of_tendsto
    (meshCovariantLaplacianSymbol_tendsto_right k B) hz

/-- Resolvents of the full positive symbol converge at every fixed mode and
every limit resolvent point. -/
theorem resolvent_meshCovariantLaplacianSymbol_tendsto_right
    (k : d → ℤ) (B : d → A) (z : ℂ)
    (hz : z ∈ resolventSet ℂ
      (continuumCovariantLaplacianSymbol k B)) :
    Tendsto
      (fun h : ℝ => resolvent
        (meshCovariantLaplacianSymbol h k B) z)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (resolvent
        (continuumCovariantLaplacianSymbol k B) z)) :=
  ResolventStability.resolvent_tendsto_of_tendsto
    (meshCovariantLaplacianSymbol_tendsto_right k B) hz

/-- On a fixed finite Fourier box, one sufficiently small positive mesh keeps
the chosen spectral parameter in every discrete resolvent set. -/
theorem eventually_forall_mem_resolventSet_meshCovariantLaplacianSymbol
    (s : Finset (d → ℤ)) (B : d → A) (z : ℂ)
    (hz : ∀ k ∈ s, z ∈ resolventSet ℂ
      (continuumCovariantLaplacianSymbol k B)) :
    ∀ᶠ h : ℝ in nhdsWithin 0 (Ioi 0), ∀ k ∈ s,
      z ∈ resolventSet ℂ
        (meshCovariantLaplacianSymbol h k B) := by
  rw [eventually_all_finset]
  intro k hk
  exact eventually_mem_resolventSet_meshCovariantLaplacianSymbol
    k B z (hz k hk)

/-- Resolvent convergence of the positive Laplacian symbols is uniform on
every fixed finite Fourier box. -/
theorem resolvent_meshCovariantLaplacianSymbol_tendstoUniformlyOn_finset
    (s : Finset (d → ℤ)) (B : d → A) (z : ℂ)
    (hz : ∀ k ∈ s, z ∈ resolventSet ℂ
      (continuumCovariantLaplacianSymbol k B)) :
    TendstoUniformlyOn
      (fun h k => resolvent
        (meshCovariantLaplacianSymbol h k B) z)
      (fun k => resolvent
        (continuumCovariantLaplacianSymbol k B) z)
      (nhdsWithin 0 (Ioi 0)) (s : Set (d → ℤ)) :=
  tendstoUniformlyOn_finset_of_tendsto s fun k hk =>
    resolvent_meshCovariantLaplacianSymbol_tendsto_right
      k B z (hz k hk)

end NCG
