/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactNormalEigenspaces
import NCG.Grand.NormalOperatorEigenspaceOrthogonality
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Order.CompleteLattice.Finset

/-!
# Cofinal finite spectral screens of an injective compact normal operator

An injective compact normal operator has no zero eigenspace, while every
nonzero eigenspace is finite-dimensional.  The finite sums of its eigenspaces
therefore give genuine finite-rank orthogonal projections.  They commute with
the operator and converge strongly to the identity over the directed set of
finite spectral subsets.

This is the compact-normal screen theorem needed for the strong essential
image of the Renewal spectralization functor.
-/

open Complex Filter Module Set Topology

noncomputable section

namespace NCG.CompactNormalFiniteSpectralScreensExact

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The algebraic sum of the eigenspaces whose eigenvalues lie in `s`. -/
def spectralScreenSubspace (R : H →L[ℂ] H) (s : Finset ℂ) :
    Submodule ℂ H :=
  s.sup fun μ => Module.End.eigenspace R.toLinearMap μ

theorem spectralScreenSubspace_mono (R : H →L[ℂ] H)
    {s t : Finset ℂ} (hst : s ⊆ t) :
    spectralScreenSubspace R s ≤ spectralScreenSubspace R t := by
  rw [spectralScreenSubspace, spectralScreenSubspace]
  exact Finset.sup_mono hst

theorem spectralScreenSubspace_directed (R : H →L[ℂ] H) :
    Directed (· ≤ ·) (spectralScreenSubspace R) := by
  intro s t
  exact ⟨s ∪ t,
    spectralScreenSubspace_mono R Finset.subset_union_left,
    spectralScreenSubspace_mono R Finset.subset_union_right⟩

theorem iSup_spectralScreenSubspace (R : H →L[ℂ] H) :
    (⨆ s : Finset ℂ, spectralScreenSubspace R s) =
      ⨆ μ : ℂ, Module.End.eigenspace R.toLinearMap μ := by
  simpa only [spectralScreenSubspace, Finset.sup_eq_iSup] using
    (iSup_eq_iSup_finset
      (fun μ : ℂ => Module.End.eigenspace R.toLinearMap μ)).symm

private theorem eigenspace_finiteDimensional
    (R : H →L[ℂ] H) (hcompact : IsCompactOperator (R : H → H))
    (hinjective : Function.Injective R) (μ : ℂ) :
    FiniteDimensional ℂ (Module.End.eigenspace R.toLinearMap μ) := by
  classical
  by_cases hμ : μ = 0
  · subst μ
    rw [Module.End.eigenspace_zero,
      LinearMap.ker_eq_bot.mpr hinjective]
    infer_instance
  · exact ContinuousLinearMap.finite_dimensional_eigenspace
      hcompact μ hμ

private theorem spectralScreenSubspace_finiteDimensional
    (R : H →L[ℂ] H) (hcompact : IsCompactOperator (R : H → H))
    (hinjective : Function.Injective R) (s : Finset ℂ) :
    FiniteDimensional ℂ (spectralScreenSubspace R s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change FiniteDimensional ℂ (↥(⊥ : Submodule ℂ H))
      infer_instance
  | @insert μ s hμ ih =>
      letI : FiniteDimensional ℂ
          (Module.End.eigenspace R.toLinearMap μ) :=
        eigenspace_finiteDimensional R hcompact hinjective μ
      letI : FiniteDimensional ℂ (spectralScreenSubspace R s) := ih
      change FiniteDimensional ℂ
        (↥((insert μ s).sup fun z =>
          Module.End.eigenspace R.toLinearMap z))
      rw [Finset.sup_insert]
      change FiniteDimensional ℂ
        (↥(Module.End.eigenspace R.toLinearMap μ ⊔
          spectralScreenSubspace R s))
      infer_instance

/-- The orthogonal projection onto a finite spectral sum. -/
def spectralScreen
    (R : H →L[ℂ] H) (hcompact : IsCompactOperator (R : H → H))
    (hinjective : Function.Injective R) (s : Finset ℂ) : H →L[ℂ] H := by
  letI : FiniteDimensional ℂ (spectralScreenSubspace R s) :=
    spectralScreenSubspace_finiteDimensional R hcompact hinjective s
  letI : CompleteSpace (spectralScreenSubspace R s) :=
    FiniteDimensional.complete ℂ _
  exact (spectralScreenSubspace R s).starProjection

theorem spectralScreen_isSymmetricProjection
    (R : H →L[ℂ] H) (hcompact : IsCompactOperator (R : H → H))
    (hinjective : Function.Injective R) (s : Finset ℂ) :
    (spectralScreen R hcompact hinjective s).IsSymmetricProjection := by
  letI : FiniteDimensional ℂ (spectralScreenSubspace R s) :=
    spectralScreenSubspace_finiteDimensional R hcompact hinjective s
  letI : CompleteSpace (spectralScreenSubspace R s) :=
    FiniteDimensional.complete ℂ _
  change (spectralScreenSubspace R s).starProjection.IsSymmetricProjection
  exact Submodule.isSymmetricProjection_starProjection _

theorem spectralScreen_range
    (R : H →L[ℂ] H) (hcompact : IsCompactOperator (R : H → H))
    (hinjective : Function.Injective R) (s : Finset ℂ) :
    LinearMap.range (spectralScreen R hcompact hinjective s).toLinearMap =
      spectralScreenSubspace R s := by
  letI : FiniteDimensional ℂ (spectralScreenSubspace R s) :=
    spectralScreenSubspace_finiteDimensional R hcompact hinjective s
  letI : CompleteSpace (spectralScreenSubspace R s) :=
    FiniteDimensional.complete ℂ _
  change LinearMap.range
    (spectralScreenSubspace R s).starProjection.toLinearMap = _
  exact Submodule.range_starProjection _

theorem spectralScreen_range_finiteDimensional
    (R : H →L[ℂ] H) (hcompact : IsCompactOperator (R : H → H))
    (hinjective : Function.Injective R) (s : Finset ℂ) :
    FiniteDimensional ℂ
      (LinearMap.range (spectralScreen R hcompact hinjective s).toLinearMap) := by
  rw [spectralScreen_range R hcompact hinjective s]
  exact spectralScreenSubspace_finiteDimensional R hcompact hinjective s

theorem spectralScreenSubspace_invariant
    (R : H →L[ℂ] H) (s : Finset ℂ) :
    ∀ x ∈ spectralScreenSubspace R s, R x ∈ spectralScreenSubspace R s := by
  intro x hx
  let E : ℂ → Submodule ℂ H :=
    fun μ => Module.End.eigenspace R.toLinearMap μ
  have hmap : Submodule.map R.toLinearMap (s.sup E) ≤ s.sup E := by
    refine Finset.sup_induction
      (p := fun U : Submodule ℂ H => Submodule.map R.toLinearMap U ≤ U)
      ?_ ?_ ?_
    · simp
    · intro U hU V hV
      rw [Submodule.map_sup]
      exact sup_le_sup hU hV
    · intro μ hμ y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hzEig : R z = μ • z := Module.End.mem_eigenspace_iff.mp hz
      change R z ∈ E μ
      rw [hzEig]
      exact (E μ).smul_mem μ hz
  exact hmap ⟨x, hx, rfl⟩

theorem spectralScreenSubspace_adjoint_invariant
    (R : H →L[ℂ] H) (hnormal : IsStarNormal R) (s : Finset ℂ) :
    ∀ x ∈ spectralScreenSubspace R s,
      ContinuousLinearMap.adjoint R x ∈ spectralScreenSubspace R s := by
  intro x hx
  let E : ℂ → Submodule ℂ H :=
    fun μ => Module.End.eigenspace R.toLinearMap μ
  have hmap : Submodule.map (ContinuousLinearMap.adjoint R).toLinearMap
      (s.sup E) ≤ s.sup E := by
    refine Finset.sup_induction
      (p := fun U : Submodule ℂ H =>
        Submodule.map (ContinuousLinearMap.adjoint R).toLinearMap U ≤ U)
      ?_ ?_ ?_
    · simp
    · intro U hU V hV
      rw [Submodule.map_sup]
      exact sup_le_sup hU hV
    · intro μ hμ y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hzEig : R z = μ • z := Module.End.mem_eigenspace_iff.mp hz
      change ContinuousLinearMap.adjoint R z ∈ E μ
      rw [NCG.NormalSpectrum.adjoint_apply_eigenvector_of_isStarNormal
        R hnormal hzEig]
      exact (E μ).smul_mem (star μ) hz
  exact hmap ⟨x, hx, rfl⟩

/-- Every finite spectral screen reduces the compact normal operator. -/
theorem spectralScreen_commutes
    (R : H →L[ℂ] H) (hcompact : IsCompactOperator (R : H → H))
    (hnormal : IsStarNormal R) (hinjective : Function.Injective R)
    (s : Finset ℂ) :
    Commute R (spectralScreen R hcompact hinjective s) := by
  letI : FiniteDimensional ℂ (spectralScreenSubspace R s) :=
    spectralScreenSubspace_finiteDimensional R hcompact hinjective s
  letI : CompleteSpace (spectralScreenSubspace R s) :=
    FiniteDimensional.complete ℂ _
  rw [commute_iff_eq]
  apply ContinuousLinearMap.ext
  intro x
  change R ((spectralScreenSubspace R s).starProjection x) =
    (spectralScreenSubspace R s).starProjection (R x)
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact spectralScreenSubspace_invariant R s _
      (Submodule.starProjection_apply_mem _ _)
  · intro y hy
    calc
      inner ℂ (R x - R ((spectralScreenSubspace R s).starProjection x)) y =
          inner ℂ (R (x - (spectralScreenSubspace R s).starProjection x)) y := by
            rw [map_sub]
      _ = inner ℂ (x - (spectralScreenSubspace R s).starProjection x)
          (ContinuousLinearMap.adjoint R y) := by
            rw [R.adjoint_inner_right]
      _ = 0 := Submodule.starProjection_inner_eq_zero _ _
        (spectralScreenSubspace_adjoint_invariant R hnormal s y hy)

/-- The finite spectral screens converge strongly to the identity. -/
theorem tendsto_spectralScreen_apply
    (R : H →L[ℂ] H) (hcompact : IsCompactOperator (R : H → H))
    (hnormal : IsStarNormal R) (hinjective : Function.Injective R)
    (x : H) :
    Tendsto (fun s : Finset ℂ => spectralScreen R hcompact hinjective s x)
      atTop (𝓝 x) := by
  have hdenseEigen :=
    NCG.NormalSpectrum.dense_iSup_eigenspaces_of_compact_of_isStarNormal
      R hcompact hnormal
  have hdenseScreens : Dense
      (((⨆ s : Finset ℂ, spectralScreenSubspace R s) : Submodule ℂ H) : Set H) := by
    rw [iSup_spectralScreenSubspace]
    exact hdenseEigen
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hyx⟩ := hdenseScreens.exists_dist_lt x (half_pos hε)
  obtain ⟨s₀, hys₀⟩ :=
    (Submodule.mem_iSup_of_directed (spectralScreenSubspace R)
      (spectralScreenSubspace_directed R)).mp hy
  refine ⟨s₀, fun s hs => ?_⟩
  letI : FiniteDimensional ℂ (spectralScreenSubspace R s) :=
    spectralScreenSubspace_finiteDimensional R hcompact hinjective s
  letI : CompleteSpace (spectralScreenSubspace R s) :=
    FiniteDimensional.complete ℂ _
  rw [dist_eq_norm]
  have hys : y ∈ spectralScreenSubspace R s :=
    spectralScreenSubspace_mono R hs hys₀
  have hPy : spectralScreen R hcompact hinjective s y = y := by
    change (spectralScreenSubspace R s).starProjection y = y
    exact Submodule.starProjection_eq_self_iff.mpr hys
  have hcontract :
    ‖spectralScreen R hcompact hinjective s (x - y)‖ ≤ ‖x - y‖ :=
    (spectralScreenSubspace R s).norm_starProjection_apply_le (x - y)
  have hxy : ‖x - y‖ < ε / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hyx
  calc
    ‖spectralScreen R hcompact hinjective s x - x‖ =
        ‖spectralScreen R hcompact hinjective s (x - y) - (x - y)‖ := by
          congr 1
          rw [map_sub, hPy]
          abel
    _ ≤ ‖spectralScreen R hcompact hinjective s (x - y)‖ + ‖x - y‖ :=
      norm_sub_le _ _
    _ ≤ ‖x - y‖ + ‖x - y‖ := add_le_add hcontract le_rfl
    _ < ε := by linarith

/-- Combined compact-normal spectral-screen certificate. -/
theorem compactNormal_injective_has_cofinal_finiteSpectralScreens
    (R : H →L[ℂ] H) (hcompact : IsCompactOperator (R : H → H))
    (hnormal : IsStarNormal R) (hinjective : Function.Injective R) :
    (∀ s, (spectralScreen R hcompact hinjective s).IsSymmetricProjection) ∧
    (∀ s, FiniteDimensional ℂ
      (LinearMap.range (spectralScreen R hcompact hinjective s).toLinearMap)) ∧
    (∀ s, Commute R (spectralScreen R hcompact hinjective s)) ∧
    (∀ x, Tendsto
      (fun s : Finset ℂ => spectralScreen R hcompact hinjective s x)
      atTop (𝓝 x)) := by
  exact ⟨spectralScreen_isSymmetricProjection R hcompact hinjective,
    spectralScreen_range_finiteDimensional R hcompact hinjective,
    spectralScreen_commutes R hcompact hnormal hinjective,
    tendsto_spectralScreen_apply R hcompact hnormal hinjective⟩

end NCG.CompactNormalFiniteSpectralScreensExact
