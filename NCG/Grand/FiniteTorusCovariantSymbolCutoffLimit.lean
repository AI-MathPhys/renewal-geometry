/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CovariantFourierLaplacianSymbolConvergence
import NCG.Grand.ZModCenteredFrequencyStabilization
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Covariant symbol limits along integer torus cutoffs

The analytic mesh parameter is specialized to `h_N = (N+1)⁻¹`.  Along this
sequence, every fixed finite continuum Fourier box is simultaneously stable
under centered reduction modulo `N+1`, while its covariant symbols, positive
Laplacian symbols, and admissible resolvents converge uniformly.
-/

open Filter NormedSpace Set Topology

namespace NCG

/-- Positive mesh associated with the nonzero finite torus `ZMod (N+1)`. -/
noncomputable def finiteTorusCutoffMesh (N : ℕ) : ℝ := ((N + 1 : ℕ) : ℝ)⁻¹

/-- The cutoff mesh tends to zero through positive values. -/
theorem finiteTorusCutoffMesh_tendsto_right :
    Tendsto finiteTorusCutoffMesh atTop (nhdsWithin 0 (Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).congr'
      (Eventually.of_forall fun N => by
        simp only [finiteTorusCutoffMesh, one_div, Nat.cast_add, Nat.cast_one])
  · exact Eventually.of_forall fun N => by
      simp only [finiteTorusCutoffMesh, Set.mem_Ioi]
      positivity

/-- A fixed integer mode embedded in the cutoff torus. -/
def finiteTorusCutoffMode {d : Type*} (N : ℕ) (k : d → ℤ) :
    d → ZMod (N + 1) :=
  fun j => (k j : ZMod (N + 1))

@[simp]
theorem finiteTorusCutoffMode_apply {d : Type*}
    (N : ℕ) (k : d → ℤ) (j : d) :
    finiteTorusCutoffMode N k j = (k j : ZMod (N + 1)) := rfl

/-- The standard character of an integer cutoff mode is exactly the
`exp(2π i h_N k)` phase used by the analytic mesh symbol. -/
theorem stdAddChar_finiteTorusCutoffMode_apply {d : Type*}
    (N : ℕ) (k : d → ℤ) (j : d) :
    ZMod.stdAddChar (finiteTorusCutoffMode N k j) =
      Complex.exp (Complex.I *
        ((2 * Real.pi * finiteTorusCutoffMesh N * (k j : ℝ) : ℝ) : ℂ)) := by
  rw [finiteTorusCutoffMode_apply, ZMod.stdAddChar_coe]
  congr 1
  unfold finiteTorusCutoffMesh
  push_cast
  have hne : ((N : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show (N : ℝ) + 1 ≠ 0 by positivity)
  field_simp [hne]

variable {A : Type} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℝ A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [IsScalarTower ℝ ℂ A] [StarRing A] [NormedStarGroup A]
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Fixed-mode covariant symbols converge along the integer cutoff mesh. -/
theorem meshCovariantFourierSymbol_tendsto_cutoff
    (k : ℤ) (B : A) :
    Tendsto (fun N : ℕ =>
        meshCovariantFourierSymbol (finiteTorusCutoffMesh N) k B)
      atTop (𝓝 (continuumCovariantFourierSymbol k B)) :=
  (meshCovariantFourierSymbol_tendsto_right k B).comp
    finiteTorusCutoffMesh_tendsto_right

/-- Literal finite-torus covariant-difference symbol at cutoff `N`, with
parallel transport `exp(-h_N B)`. -/
noncomputable def finiteTorusCutoffCovariantFourierSymbol
    (N : ℕ) (k : ℤ) (B : A) : A :=
  ((finiteTorusCutoffMesh N)⁻¹ : ℂ) •
    ((ZMod.stdAddChar (k : ZMod (N + 1))) • (1 : A) -
      NormedSpace.exp
        (((-finiteTorusCutoffMesh N : ℝ) : ℂ) • B))

/-- The literal `ZMod` cutoff symbol is the intrinsic two-exponential mesh
symbol used by the convergence theorem. -/
theorem finiteTorusCutoffCovariantFourierSymbol_eq_mesh
    (N : ℕ) (k : ℤ) (B : A)
    (hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x) :
    finiteTorusCutoffCovariantFourierSymbol N k B =
      meshCovariantFourierSymbol (finiteTorusCutoffMesh N) k B := by
  rw [finiteTorusCutoffCovariantFourierSymbol,
    ZMod.stdAddChar_coe]
  symm
  rw [meshCovariantFourierSymbol_eq_explicit
    (finiteTorusCutoffMesh N) k B hreal]
  congr 3
  unfold finiteTorusCutoffMesh
  push_cast
  have hne : ((N : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show (N : ℝ) + 1 ≠ 0 by positivity)
  field_simp [hne]

/-- Literal cutoff symbols converge at every fixed integer mode. -/
theorem finiteTorusCutoffCovariantFourierSymbol_tendsto
    (k : ℤ) (B : A)
    (hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x) :
    Tendsto (fun N : ℕ => finiteTorusCutoffCovariantFourierSymbol N k B)
      atTop (𝓝 (continuumCovariantFourierSymbol k B)) :=
  (meshCovariantFourierSymbol_tendsto_cutoff k B).congr'
    (Eventually.of_forall fun N =>
      (finiteTorusCutoffCovariantFourierSymbol_eq_mesh N k B hreal).symm)


/-- Full positive Laplacian symbols converge at a fixed multidimensional mode
along the integer cutoff mesh. -/
theorem meshCovariantLaplacianSymbol_tendsto_cutoff
    (k : d → ℤ) (B : d → A) :
    Tendsto (fun N : ℕ =>
        meshCovariantLaplacianSymbol (finiteTorusCutoffMesh N) k B)
      atTop (𝓝 (continuumCovariantLaplacianSymbol k B)) :=
  (meshCovariantLaplacianSymbol_tendsto_right k B).comp
    finiteTorusCutoffMesh_tendsto_right

/-- Along integer cutoffs, full positive symbols converge uniformly on every
fixed finite multidimensional Fourier box. -/
theorem meshCovariantLaplacianSymbol_tendstoUniformlyOn_cutoff_finset
    (s : Finset (d → ℤ)) (B : d → A) :
    TendstoUniformlyOn
      (fun N k => meshCovariantLaplacianSymbol
        (finiteTorusCutoffMesh N) k B)
      (fun k => continuumCovariantLaplacianSymbol k B)
      atTop (s : Set (d → ℤ)) :=
  tendstoUniformlyOn_finset_of_tendsto s fun k _ =>
    meshCovariantLaplacianSymbol_tendsto_cutoff k B

/-- One late cutoff simultaneously stabilizes all centered indices in a fixed
Fourier box and makes every full positive symbol uniformly close to its
continuum counterpart. -/
theorem eventually_centeredModes_stable_and_laplacianSymbols_close
    (s : Finset (d → ℤ)) (B : d → A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ s,
      finiteTorusCenteredFrequency (finiteTorusCutoffMode N k) = k ∧
      dist
        (meshCovariantLaplacianSymbol (finiteTorusCutoffMesh N) k B)
        (continuumCovariantLaplacianSymbol k B) < ε := by
  filter_upwards
    [eventually_forall_mem_finiteBox_centeredFrequency_intCast_eq s,
      eventually_forall_mem_finset_dist_lt_of_tendsto s
        (fun k _ => meshCovariantLaplacianSymbol_tendsto_cutoff k B) hε]
    with N hcenter hclose
  intro k hk
  exact ⟨hcenter k hk, hclose k hk⟩

/-- Resolvents of the full positive symbol converge at a fixed mode along the
integer cutoff mesh. -/
theorem resolvent_meshCovariantLaplacianSymbol_tendsto_cutoff
    (k : d → ℤ) (B : d → A) (z : ℂ)
    (hz : z ∈ resolventSet ℂ
      (continuumCovariantLaplacianSymbol k B)) :
    Tendsto
      (fun N : ℕ => resolvent
        (meshCovariantLaplacianSymbol (finiteTorusCutoffMesh N) k B) z)
      atTop
      (𝓝 (resolvent (continuumCovariantLaplacianSymbol k B) z)) :=
  (resolvent_meshCovariantLaplacianSymbol_tendsto_right k B z hz).comp
    finiteTorusCutoffMesh_tendsto_right

/-- Along integer cutoffs, resolvent convergence is uniform on every fixed
finite Fourier box. -/
theorem resolvent_meshCovariantLaplacianSymbol_tendstoUniformlyOn_cutoff_finset
    (s : Finset (d → ℤ)) (B : d → A) (z : ℂ)
    (hz : ∀ k ∈ s, z ∈ resolventSet ℂ
      (continuumCovariantLaplacianSymbol k B)) :
    TendstoUniformlyOn
      (fun N k => resolvent
        (meshCovariantLaplacianSymbol (finiteTorusCutoffMesh N) k B) z)
      (fun k => resolvent (continuumCovariantLaplacianSymbol k B) z)
      atTop (s : Set (d → ℤ)) :=
  tendstoUniformlyOn_finset_of_tendsto s fun k hk =>
    resolvent_meshCovariantLaplacianSymbol_tendsto_cutoff
      k B z (hz k hk)

/-- One late cutoff simultaneously stabilizes all centered modes and makes
all admissible finite-box resolvents uniformly close. -/
theorem eventually_centeredModes_stable_and_resolvents_close
    (s : Finset (d → ℤ)) (B : d → A) (z : ℂ)
    (hz : ∀ k ∈ s, z ∈ resolventSet ℂ
      (continuumCovariantLaplacianSymbol k B))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ s,
      finiteTorusCenteredFrequency (finiteTorusCutoffMode N k) = k ∧
      dist
        (resolvent
          (meshCovariantLaplacianSymbol (finiteTorusCutoffMesh N) k B) z)
        (resolvent (continuumCovariantLaplacianSymbol k B) z) < ε := by
  filter_upwards
    [eventually_forall_mem_finiteBox_centeredFrequency_intCast_eq s,
      eventually_forall_mem_finset_dist_lt_of_tendsto s
        (fun k hk =>
          resolvent_meshCovariantLaplacianSymbol_tendsto_cutoff
            k B z (hz k hk)) hε]
    with N hcenter hclose
  intro k hk
  exact ⟨hcenter k hk, hclose k hk⟩

/-- Literal positive cutoff symbol `D†D`. -/
noncomputable def finiteTorusCutoffCovariantPositiveSymbol
    (N : ℕ) (k : ℤ) (B : A) : A :=
  star (finiteTorusCutoffCovariantFourierSymbol N k B) *
    finiteTorusCutoffCovariantFourierSymbol N k B

/-- Literal and intrinsic positive cutoff symbols agree. -/
theorem finiteTorusCutoffCovariantPositiveSymbol_eq_mesh
    (N : ℕ) (k : ℤ) (B : A)
    (hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x) :
    finiteTorusCutoffCovariantPositiveSymbol N k B =
      meshCovariantPositiveSymbol (finiteTorusCutoffMesh N) k B := by
  rw [finiteTorusCutoffCovariantPositiveSymbol,
    meshCovariantPositiveSymbol,
    finiteTorusCutoffCovariantFourierSymbol_eq_mesh N k B hreal]

/-- Literal full cutoff Laplacian symbol `Σⱼ Dⱼ†Dⱼ`. -/
noncomputable def finiteTorusCutoffCovariantLaplacianSymbol
    (N : ℕ) (k : d → ℤ) (B : d → A) : A :=
  ∑ j, finiteTorusCutoffCovariantPositiveSymbol N (k j) (B j)

/-- The literal cutoff Laplacian symbol agrees with the intrinsic mesh
Laplacian symbol. -/
theorem finiteTorusCutoffCovariantLaplacianSymbol_eq_mesh
    (N : ℕ) (k : d → ℤ) (B : d → A)
    (hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x) :
    finiteTorusCutoffCovariantLaplacianSymbol N k B =
      meshCovariantLaplacianSymbol (finiteTorusCutoffMesh N) k B := by
  classical
  unfold finiteTorusCutoffCovariantLaplacianSymbol
    meshCovariantLaplacianSymbol
  apply Finset.sum_congr rfl
  intro j _
  exact finiteTorusCutoffCovariantPositiveSymbol_eq_mesh
    N (k j) (B j) hreal

/-- Literal full cutoff Laplacian symbols converge at each fixed mode. -/
theorem finiteTorusCutoffCovariantLaplacianSymbol_tendsto
    (k : d → ℤ) (B : d → A)
    (hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x) :
    Tendsto
      (fun N : ℕ => finiteTorusCutoffCovariantLaplacianSymbol N k B)
      atTop (𝓝 (continuumCovariantLaplacianSymbol k B)) :=
  (meshCovariantLaplacianSymbol_tendsto_cutoff k B).congr'
    (Eventually.of_forall fun N =>
      (finiteTorusCutoffCovariantLaplacianSymbol_eq_mesh
        N k B hreal).symm)

/-- Literal full cutoff Laplacian symbols converge uniformly on every fixed
finite Fourier box. -/
theorem finiteTorusCutoffCovariantLaplacianSymbol_tendstoUniformlyOn_finset
    (s : Finset (d → ℤ)) (B : d → A)
    (hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x) :
    TendstoUniformlyOn
      (fun N k => finiteTorusCutoffCovariantLaplacianSymbol N k B)
      (fun k => continuumCovariantLaplacianSymbol k B)
      atTop (s : Set (d → ℤ)) :=
  tendstoUniformlyOn_finset_of_tendsto s fun k _ =>
    finiteTorusCutoffCovariantLaplacianSymbol_tendsto k B hreal

/-- Literal cutoff-symbol resolvents converge at every fixed mode. -/
theorem resolvent_finiteTorusCutoffCovariantLaplacianSymbol_tendsto
    (k : d → ℤ) (B : d → A) (z : ℂ)
    (hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x)
    (hz : z ∈ resolventSet ℂ
      (continuumCovariantLaplacianSymbol k B)) :
    Tendsto
      (fun N : ℕ => resolvent
        (finiteTorusCutoffCovariantLaplacianSymbol N k B) z)
      atTop
      (𝓝 (resolvent (continuumCovariantLaplacianSymbol k B) z)) :=
  (resolvent_meshCovariantLaplacianSymbol_tendsto_cutoff k B z hz).congr'
    (Eventually.of_forall fun N => by
      exact congrArg (fun L : A => resolvent L z)
        (finiteTorusCutoffCovariantLaplacianSymbol_eq_mesh
          N k B hreal).symm)

/-- Literal cutoff-symbol resolvents converge uniformly on every fixed
finite Fourier box. -/
theorem resolvent_finiteTorusCutoffCovariantLaplacianSymbol_tendstoUniformlyOn_finset
    (s : Finset (d → ℤ)) (B : d → A) (z : ℂ)
    (hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x)
    (hz : ∀ k ∈ s, z ∈ resolventSet ℂ
      (continuumCovariantLaplacianSymbol k B)) :
    TendstoUniformlyOn
      (fun N k => resolvent
        (finiteTorusCutoffCovariantLaplacianSymbol N k B) z)
      (fun k => resolvent (continuumCovariantLaplacianSymbol k B) z)
      atTop (s : Set (d → ℤ)) :=
  tendstoUniformlyOn_finset_of_tendsto s fun k hk =>
    resolvent_finiteTorusCutoffCovariantLaplacianSymbol_tendsto
      k B z hreal (hz k hk)

/-- One late cutoff simultaneously stabilizes every centered index in a
fixed box and makes all literal cutoff-symbol resolvents uniformly close. -/
theorem eventually_centeredModes_stable_and_literal_resolvents_close
    (s : Finset (d → ℤ)) (B : d → A) (z : ℂ)
    (hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x)
    (hz : ∀ k ∈ s, z ∈ resolventSet ℂ
      (continuumCovariantLaplacianSymbol k B))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ s,
      finiteTorusCenteredFrequency (finiteTorusCutoffMode N k) = k ∧
      dist
        (resolvent
          (finiteTorusCutoffCovariantLaplacianSymbol N k B) z)
        (resolvent (continuumCovariantLaplacianSymbol k B) z) < ε := by
  filter_upwards
    [eventually_forall_mem_finiteBox_centeredFrequency_intCast_eq s,
      eventually_forall_mem_finset_dist_lt_of_tendsto s
        (fun k hk =>
          resolvent_finiteTorusCutoffCovariantLaplacianSymbol_tendsto
            k B z hreal (hz k hk)) hε]
    with N hcenter hclose
  intro k hk
  exact ⟨hcenter k hk, hclose k hk⟩

end NCG
