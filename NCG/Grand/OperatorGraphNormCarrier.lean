/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventGraphMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# The operator graph as a graph-norm carrier

The range of `u ↦ (u, A u)` inside the Hilbert direct sum is the literal
carrier of the graph norm.  Its inherited norm satisfies
`‖u‖²_graph = ‖u‖² + ‖A u‖²`.  This module also codomain-restricts a
weak resolvent graph map to that carrier, so compactness of the graph-unit
ball can be transferred to resolvent outputs by bounded precomposition.
-/

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- The algebraic graph embedding into the Hilbert direct sum. -/
def operatorGraphHilbertLinearMap
    (D : Submodule K E) (A : D →ₗ[K] F) :
    D →ₗ[K] WithLp 2 (E × F) where
  toFun x := WithLp.toLp 2 ((x : E), A x)
  map_add' x y := by
    apply (WithLp.equiv 2 (E × F)).injective
    simp
  map_smul' c x := by
    apply (WithLp.equiv 2 (E × F)).injective
    simp

@[simp] theorem operatorGraphHilbertLinearMap_fst
    (D : Submodule K E) (A : D →ₗ[K] F) (x : D) :
    (operatorGraphHilbertLinearMap D A x).fst = (x : E) := rfl

@[simp] theorem operatorGraphHilbertLinearMap_snd
    (D : Submodule K E) (A : D →ₗ[K] F) (x : D) :
    (operatorGraphHilbertLinearMap D A x).snd = A x := rfl

/-- The operator graph, regarded as a normed submodule of the Hilbert direct
sum.  No closedness assumption is needed for the compact-screen arguments. -/
def operatorGraphNormCarrier
    (D : Submodule K E) (A : D →ₗ[K] F) :
    Submodule K (WithLp 2 (E × F)) :=
  LinearMap.range (operatorGraphHilbertLinearMap D A)

/-- A domain vector regarded as a vector in the graph-norm carrier. -/
def operatorGraphNormVector
    (D : Submodule K E) (A : D →ₗ[K] F) (x : D) :
    operatorGraphNormCarrier D A :=
  ⟨operatorGraphHilbertLinearMap D A x,
    LinearMap.mem_range_self (operatorGraphHilbertLinearMap D A) x⟩

@[simp] theorem operatorGraphNormVector_coe
    (D : Submodule K E) (A : D →ₗ[K] F) (x : D) :
    (operatorGraphNormVector D A x : WithLp 2 (E × F)) =
      operatorGraphHilbertLinearMap D A x := rfl

/-- The inherited carrier norm is exactly the graph norm. -/
theorem operatorGraphNormVector_norm_sq
    (D : Submodule K E) (A : D →ₗ[K] F) (x : D) :
    ‖operatorGraphNormVector D A x‖ ^ 2 = ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2 := by
  change ‖operatorGraphHilbertLinearMap D A x‖ ^ 2 =
    ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

/-- A graph-unit-ball vector is precisely a domain vector satisfying the
quadratic graph-energy bound. -/
theorem operatorGraphNormVector_norm_le_one_iff
    (D : Submodule K E) (A : D →ₗ[K] F) (x : D) :
    ‖operatorGraphNormVector D A x‖ ≤ 1 ↔
      ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2 ≤ 1 := by
  rw [← operatorGraphNormVector_norm_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg (operatorGraphNormVector D A x)]
  · intro h
    nlinarith [norm_nonneg (operatorGraphNormVector D A x)]

/-- The canonical continuous inclusion of the graph-norm carrier. -/
def operatorGraphNormInclusion
    (D : Submodule K E) (A : D →ₗ[K] F) :
    operatorGraphNormCarrier D A →L[K] WithLp 2 (E × F) :=
  (operatorGraphNormCarrier D A).subtypeL

@[simp] theorem operatorGraphNormInclusion_apply
    (D : Submodule K E) (A : D →ₗ[K] F)
    (x : operatorGraphNormCarrier D A) :
    operatorGraphNormInclusion D A x = x := rfl

/-- The canonical Hilbert graph resolvent, with codomain restricted to the
operator graph. -/
def operatorGraphResolventNormCarrier
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    E →L[K] operatorGraphNormCarrier D A :=
  (operatorGraphResolventHilbertGraph D A R lam hlam hR).codRestrict
    (operatorGraphNormCarrier D A) (fun f ↦ by
      refine ⟨operatorGraphResolventRangeLinearMap D A R lam hR f, ?_⟩
      apply (WithLp.equiv 2 (E × F)).injective
      rfl)

@[simp] theorem operatorGraphResolventNormCarrier_coe
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f))
    (f : E) :
    (operatorGraphResolventNormCarrier D A R lam hlam hR f :
        WithLp 2 (E × F)) =
      operatorGraphResolventHilbertGraph D A R lam hlam hR f := rfl

/-- Inclusion after the graph-carrier lift recovers the original Hilbert
graph-output map exactly. -/
theorem operatorGraphNormInclusion_comp_resolventNormCarrier
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    (operatorGraphNormInclusion D A).comp
      (operatorGraphResolventNormCarrier D A R lam hlam hR) =
        operatorGraphResolventHilbertGraph D A R lam hlam hR := by
  ext f
  rfl

/-- The graph-carrier resolvent lift has the same uniform bound as its
ambient Hilbert graph map. -/
theorem norm_operatorGraphResolventNormCarrier_le
    (D : Submodule K E) (A : D →ₗ[K] F) (R : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (hR : ∀ f : E, OperatorGraphResolventEquation D A lam f (R f)) :
    ‖operatorGraphResolventNormCarrier D A R lam hlam hR‖ ≤
      2 * (1 + 1 / lam) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖operatorGraphResolventHilbertGraph D A R lam hlam hR f‖ ≤
    (2 * (1 + 1 / lam)) * ‖f‖
  exact norm_operatorGraphResolventHilbertGraph_le D A R lam hlam hR f

/-- If the physical stage carrier is finite-dimensional, so is every graph
carrier over one of its submodules. -/
instance operatorGraphNormCarrier_finiteDimensional
    (D : Submodule K E) (A : D →ₗ[K] F) [FiniteDimensional K E] :
    FiniteDimensional K (operatorGraphNormCarrier D A) :=
  LinearMap.finiteDimensional_range (operatorGraphHilbertLinearMap D A)

/-- At a finite-dimensional cutoff the graph inclusion is automatically a
compact operator, even if the auxiliary graph component is infinite-dimensional. -/
theorem isCompactOperator_operatorGraphNormInclusion
    (D : Submodule K E) (A : D →ₗ[K] F) [FiniteDimensional K E] :
    IsCompactOperator (operatorGraphNormInclusion D A) := by
  letI : ProperSpace (operatorGraphNormCarrier D A) :=
    FiniteDimensional.proper_rclike K (operatorGraphNormCarrier D A)
  exact isCompactOperator_of_locallyCompactSpace_rng
    (operatorGraphNormInclusion D A)

end NCG.VaryingHilbert
