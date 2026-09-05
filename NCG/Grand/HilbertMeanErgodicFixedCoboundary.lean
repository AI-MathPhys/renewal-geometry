/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Sequences
import NCG.Grand.MoorePenroseSchurExact

/-!
# Hilbert-space fixed/coboundary decomposition

The infinite-dimensional analytic core of `thm:GT-fixed-coboundary`.
For a contraction on a Hilbert space, fixed and co-fixed vectors coincide,
the closed coboundary range is the orthogonal complement of the fixed space,
the Cesàro averages converge strongly to the orthogonal projection onto that
space, and every co-fixed reader depends only on this zero-mode projection.
-/

open ContinuousLinearMap Filter Function
open scoped Topology InnerProduct

namespace NCG
namespace HilbertMeanErgodicFixedCoboundary

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The fixed vectors of a contraction and of its adjoint coincide. -/
theorem fixed_iff_adjoint_fixed (T : H →L[𝕜] H) (hT : ‖T‖ ≤ 1) (x : H) :
    T x = x ↔ (T†) x = x := by
  have hTadj : ‖T†‖ ≤ 1 := by simpa using hT
  constructor
  · intro hx
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜)
      (by simpa using (T†).le_of_opNorm_le hTadj x)
    rw [T.adjoint_inner_left, hx]
    exact inner_self_eq_norm_sq x
  · intro hx
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜)
      (by simpa using T.le_of_opNorm_le hT x)
    rw [← T.adjoint_inner_right, hx]
    exact inner_self_eq_norm_sq x

/-- The topological closure of the coboundaries is exactly the orthogonal
complement of the fixed-point space. -/
theorem coboundary_closure_eq_fixed_orthogonal
    (T : H →L[𝕜] H) (hT : ‖T‖ ≤ 1) :
    (T - 1).range.topologicalClosure =
      (T.eqLocus (1 : H →L[𝕜] H))ᗮ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    ContinuousLinearMap.orthogonal_range]
  congr 1
  ext x
  change ((T - 1)†) x = 0 ↔ T x = x
  simp only [map_sub, ContinuousLinearMap.adjoint_one, sub_apply,
    one_apply_eq_self, sub_eq_zero]
  exact (fixed_iff_adjoint_fixed T hT x).symm

/-- Orthogonal direct-sum form of the fixed/coboundary decomposition. -/
theorem fixed_sup_coboundary_closure
    (T : H →L[𝕜] H) (hT : ‖T‖ ≤ 1) :
    T.eqLocus (1 : H →L[𝕜] H) ⊔
        (T - 1).range.topologicalClosure = ⊤ := by
  rw [coboundary_closure_eq_fixed_orthogonal T hT]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- Strong convergence of the Cesàro means to the fixed-space projection. -/
theorem cesaro_tendsto_fixed_projection
    (T : H →L[𝕜] H) (hT : ‖T‖ ≤ 1) (x : H) :
    Tendsto (birkhoffAverage 𝕜 T id · x) atTop
      (𝓝 ((T.eqLocus (1 : H →L[𝕜] H)).orthogonalProjectionOnto x)) :=
  T.tendsto_birkhoffAverage_orthogonalProjection hT x

/-- A co-fixed accepted source reads only the fixed (zero-mode) component. -/
theorem inner_eq_inner_fixed_projection
    (T : H →L[𝕜] H) (hT : ‖T‖ ≤ 1) (a z : H)
    (ha : (T†) a = a) :
    inner 𝕜 a z = inner 𝕜 a
      ((T.eqLocus (1 : H →L[𝕜] H)).orthogonalProjectionOnto z) := by
  let K := T.eqLocus (1 : H →L[𝕜] H)
  have haK : a ∈ K := (fixed_iff_adjoint_fixed T hT a).mpr ha
  symm
  exact K.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨a, haK⟩ z

/-- The general Hilbert-space core of `thm:GT-fixed-coboundary`, bundled in
the same order as the manuscript: fixed/co-fixed equality, orthogonal
decomposition, strong Cesàro convergence, and zero-mode-only readout. -/
theorem hilbert_fixed_coboundary_core
    (T : H →L[𝕜] H) (hT : ‖T‖ ≤ 1) :
    (∀ x, T x = x ↔ (T†) x = x)
      ∧ T.eqLocus (1 : H →L[𝕜] H) ⊔
          (T - 1).range.topologicalClosure = ⊤
      ∧ (∀ x, Tendsto (birkhoffAverage 𝕜 T id · x) atTop
          (𝓝 ((T.eqLocus (1 : H →L[𝕜] H)).orthogonalProjectionOnto x)))
      ∧ (∀ a z, (T†) a = a →
          inner 𝕜 a z = inner 𝕜 a
            ((T.eqLocus (1 : H →L[𝕜] H)).orthogonalProjectionOnto z)) := by
  exact ⟨fixed_iff_adjoint_fixed T hT,
    fixed_sup_coboundary_closure T hT,
    cesaro_tendsto_fixed_projection T hT,
    inner_eq_inner_fixed_projection T hT⟩

section FiniteSource

variable {K : Type*} [Fintype K]

/-- The fixed-space Gram of a finite source synthesis `Z : K → H`. -/
noncomputable def fixedSourceGram (T : H →L[𝕜] H) (Z : K → H) :
    Matrix K K 𝕜 := fun i j =>
  inner 𝕜
    (((T.eqLocus (1 : H →L[𝕜] H)).orthogonalProjectionOnto (Z i) :
      T.eqLocus (1 : H →L[𝕜] H)) : H)
    (((T.eqLocus (1 : H →L[𝕜] H)).orthogonalProjectionOnto (Z j) :
      T.eqLocus (1 : H →L[𝕜] H)) : H)

/-- Gram of the finite source after applying the `N`th Cesàro mean. -/
noncomputable def cesaroSourceGram (T : H →L[𝕜] H) (Z : K → H)
    (N : ℕ) : Matrix K K 𝕜 := fun i j =>
  inner 𝕜 (birkhoffAverage 𝕜 T id N (Z i))
    (birkhoffAverage 𝕜 T id N (Z j))

/-- Matrix form of the manuscript limit
`Z* P₀ Z = lim Z* M_N(T)* M_N(T) Z`. -/
theorem cesaroSourceGram_tendsto_fixedSourceGram
    (T : H →L[𝕜] H) (hT : ‖T‖ ≤ 1) (Z : K → H) :
    Tendsto (cesaroSourceGram T Z) atTop (𝓝 (fixedSourceGram T Z)) := by
  unfold cesaroSourceGram fixedSourceGram
  exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
    (cesaro_tendsto_fixed_projection T hT (Z i)).inner
      (cesaro_tendsto_fixed_projection T hT (Z j))

/-- The Hilbert--Schmidt energy of the fixed part of a finite source.  For a
finite column space this is `Tr (Z^* P₀ Z)`. -/
noncomputable def fixedSourceEnergy (T : H →L[𝕜] H) (Z : K → H) : ℝ :=
  ∑ i, ‖(T.eqLocus (1 : H →L[𝕜] H)).starProjection (Z i)‖ ^ 2

/-- The squared Hilbert--Schmidt norm of the residual after subtracting a
coboundary source. -/
noncomputable def coboundaryResidualEnergy (T : H →L[𝕜] H)
    (Z G : K → H) : ℝ :=
  ∑ i, ‖Z i - (T - 1) (G i)‖ ^ 2

/-- Projecting a residual onto the fixed space recovers the fixed part of the
original vector, hence no coboundary can reduce its norm. -/
theorem fixed_projection_norm_le_coboundary_residual
    (T : H →L[𝕜] H) (hT : ‖T‖ ≤ 1) (z g : H) :
    ‖(T.eqLocus (1 : H →L[𝕜] H)).starProjection z‖ ≤
      ‖z - (T - 1) g‖ := by
  let F := T.eqLocus (1 : H →L[𝕜] H)
  have hc : (T - 1) g ∈ Fᗮ := by
    rw [← coboundary_closure_eq_fixed_orthogonal T hT]
    exact Submodule.le_topologicalClosure _ ⟨g, rfl⟩
  calc
    ‖F.starProjection z‖ = ‖F.starProjection (z - (T - 1) g)‖ := by
      rw [map_sub, (F.starProjection_apply_eq_zero_iff).2 hc, sub_zero]
    _ ≤ ‖z - (T - 1) g‖ := F.norm_starProjection_apply_le _

/-- A vector's fixed energy is approached by actual coboundaries, not merely
by vectors in the closure of the coboundary range. -/
theorem exists_coboundary_residual_energy_approximation
    (T : H →L[𝕜] H) (hT : ‖T‖ ≤ 1) (z : H) :
    ∃ g : ℕ → H,
      Tendsto (fun n => ‖z - (T - 1) (g n)‖ ^ 2) atTop
        (𝓝 (‖(T.eqLocus (1 : H →L[𝕜] H)).starProjection z‖ ^ 2)) := by
  let F := T.eqLocus (1 : H →L[𝕜] H)
  have hx : z - F.starProjection z ∈ (T - 1).range.topologicalClosure := by
    rw [coboundary_closure_eq_fixed_orthogonal T hT]
    exact F.sub_starProjection_mem_orthogonal z
  obtain ⟨y, hyRange, hy⟩ := mem_closure_iff_seq_limit.mp hx
  choose g hg using hyRange
  refine ⟨g, ?_⟩
  have hres : Tendsto (fun n => z - ((T - 1 : H →L[𝕜] H) (g n))) atTop
      (𝓝 (F.starProjection z)) := by
    have hz : Tendsto (fun _ : ℕ => z) atTop (𝓝 z) := tendsto_const_nhds
    have hsub := hz.sub hy
    rw [show z - (z - F.starProjection z) = F.starProjection z by abel] at hsub
    exact hsub.congr' (Filter.Eventually.of_forall fun n => by simpa using congrArg (z - ·) (hg n).symm)
  exact hres.norm.pow 2

/-- Exact finite-source Hilbert--Schmidt variational identity in constructive
infimum form: the fixed energy is a lower bound for every coboundary residual,
and a sequence of genuine coboundary sources converges to that bound. -/
theorem finiteSource_coboundary_variational
    (T : H →L[𝕜] H) (hT : ‖T‖ ≤ 1) (Z : K → H) :
    (∀ G : K → H, fixedSourceEnergy T Z ≤ coboundaryResidualEnergy T Z G) ∧
      ∃ G : ℕ → K → H,
        Tendsto (fun n => coboundaryResidualEnergy T Z (G n)) atTop
          (𝓝 (fixedSourceEnergy T Z)) := by
  constructor
  · intro G
    unfold fixedSourceEnergy coboundaryResidualEnergy
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (fixed_projection_norm_le_coboundary_residual T hT (Z i) (G i)) 2
  · choose g hg using fun i : K =>
      exists_coboundary_residual_energy_approximation T hT (Z i)
    refine ⟨fun n i => g i n, ?_⟩
    unfold coboundaryResidualEnergy fixedSourceEnergy
    exact tendsto_finsetSum Finset.univ fun i _ => hg i

end FiniteSource

section RealRouter

variable {H₀ E K₀ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup K₀] [InnerProductSpace ℝ K₀] [CompleteSpace K₀]

/-- Exact Moore--Penrose router domination for a finite accepted source in a
possibly infinite-dimensional real Hilbert space.  The left term is
`Z* P₀ Z`; the subtracted term is
`(A*Z)*(A*A)†(A*Z)`. -/
theorem accepted_router_le_fixed
    (T : H₀ →L[ℝ] H₀) (hT : ‖T‖ ≤ 1)
    (A : E →L[ℝ] H₀) (Z : K₀ →L[ℝ] H₀)
    (hA : ∀ e, (T†) (A e) = A e) :
    (Z† ∘L (T.eqLocus (1 : H₀ →L[ℝ] H₀)).starProjection ∘L Z -
      (MoorePenrose.crossGram A Z)† ∘L MoorePenrose.gramPinv A ∘L
        MoorePenrose.crossGram A Z).IsPositive := by
  let F := T.eqLocus (1 : H₀ →L[ℝ] H₀)
  let P : H₀ →L[ℝ] H₀ := F.starProjection
  let Z₀ : K₀ →L[ℝ] H₀ := P ∘L Z
  have hPA : P ∘L A = A := by
    apply ContinuousLinearMap.ext
    intro e
    exact F.starProjection_eq_self_iff.mpr
      ((fixed_iff_adjoint_fixed T hT (A e)).mpr (hA e))
  have hPself : P† = P := isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection F)
  have hAP : A† ∘L P = A† := by
    rw [← hPself, ← adjoint_comp, hPA]
  have hcross : MoorePenrose.crossGram A Z₀ = MoorePenrose.crossGram A Z := by
    unfold MoorePenrose.crossGram Z₀
    rw [← ContinuousLinearMap.comp_assoc, hAP]
  have hPP : P ∘L P = P :=
    F.starProjection_comp_starProjection_of_le le_rfl
  have hgram : Z₀† ∘L Z₀ = Z† ∘L P ∘L Z := by
    unfold Z₀
    rw [adjoint_comp, hPself]
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply]
    have hz := congrArg (fun Q : H₀ →L[ℝ] H₀ => Q (Z z)) hPP
    exact congrArg (fun v => (Z†) v) hz
  have hp := MoorePenrose.innovation_isPositive A Z₀
  rw [← MoorePenrose.schur_innovation] at hp
  rw [hgram, hcross] at hp
  exact hp

/-- Operator form of `A*Z = A*P₀Z`: every co-fixed accepted source sees only
the fixed component. -/
theorem accepted_crossGram_eq_fixed_crossGram
    (T : H₀ →L[ℝ] H₀) (hT : ‖T‖ ≤ 1)
    (A : E →L[ℝ] H₀) (Z : K₀ →L[ℝ] H₀)
    (hA : ∀ e, (T†) (A e) = A e) :
    MoorePenrose.crossGram A Z = MoorePenrose.crossGram A
      ((T.eqLocus (1 : H₀ →L[ℝ] H₀)).starProjection ∘L Z) := by
  apply ContinuousLinearMap.ext
  intro z
  refine ext_inner_right ℝ fun e => ?_
  simp only [MoorePenrose.crossGram, ContinuousLinearMap.comp_apply]
  rw [adjoint_inner_left, adjoint_inner_left]
  calc
    inner ℝ (Z z) (A e) = inner ℝ (A e) (Z z) := real_inner_comm _ _
    _ = inner ℝ (A e)
        ((T.eqLocus (1 : H₀ →L[ℝ] H₀)).starProjection (Z z)) :=
      inner_eq_inner_fixed_projection T hT (A e) (Z z) (hA e)
    _ = inner ℝ ((T.eqLocus (1 : H₀ →L[ℝ] H₀)).starProjection (Z z))
        (A e) := real_inner_comm _ _

end RealRouter

end HilbertMeanErgodicFixedCoboundary
end NCG
