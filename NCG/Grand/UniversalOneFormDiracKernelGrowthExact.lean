import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Universal one-form Dirac kernel growth

This file isolates the finite-dimensional calculation behind the manuscript's
universal-one-form obstruction.  If `d : V → W` is the graph differential and
both orientations of every edge are retained, then `dim W = 2e`.  The block
Dirac operator `(v,w) ↦ (d†w,dv)` has kernel `ker d × ker d†`; connectedness
gives `dim ker d = 1`, while rank-nullity and equality of the ranks of `d` and
`d†` give `dim ker d† = 2e - (n-1)`.
-/

open scoped InnerProductSpace

namespace NCG.UniversalOneFormDiracKernelGrowth

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The off-diagonal Dirac operator associated to a differential `d`. -/
noncomputable def universalDirac (d : V →L[ℝ] W) : (V × W) →L[ℝ] (V × W) :=
  (d.adjoint.comp (ContinuousLinearMap.snd ℝ V W)).prod
    (d.comp (ContinuousLinearMap.fst ℝ V W))

@[simp]
theorem universalDirac_apply (d : V →L[ℝ] W) (x : V × W) :
    universalDirac d x = (d.adjoint x.2, d x.1) :=
  rfl

/-- The zero modes of the block Dirac operator are exactly the zero modes of
`d` and of its adjoint, independently in the two summands. -/
noncomputable def universalDiracKernelEquiv (d : V →L[ℝ] W) :
    LinearMap.ker (universalDirac d).toLinearMap ≃ₗ[ℝ]
      LinearMap.ker d.toLinearMap × LinearMap.ker d.adjoint.toLinearMap where
  toFun x :=
    (⟨x.1.1, by
      have h := congrArg Prod.snd x.2
      simpa [universalDirac] using h⟩,
     ⟨x.1.2, by
      have h := congrArg Prod.fst x.2
      simpa [universalDirac] using h⟩)
  invFun x :=
    ⟨(x.1.1, x.2.1), by
      apply Prod.ext
      · simpa [universalDirac] using x.2.2
      · simpa [universalDirac] using x.1.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    ext <;> rfl
  map_add' x y := by
    ext <;> rfl
  map_smul' c x := by
    ext <;> rfl

/-- Abstract kernel formula for the universal one-form Dirac operator. -/
theorem finrank_universalDirac_kernel (d : V →L[ℝ] W) :
    Module.finrank ℝ (LinearMap.ker (universalDirac d).toLinearMap) =
      Module.finrank ℝ (LinearMap.ker d.toLinearMap) +
        Module.finrank ℝ (LinearMap.ker d.adjoint.toLinearMap) := by
  rw [← Module.finrank_prod]
  exact LinearEquiv.finrank_eq (universalDiracKernelEquiv d)

/-- With `n` vertices and `2e` oriented universal one-forms, a connected
incidence differential has universal Dirac nullity `2e - n + 2`.  Since
`finrank` is natural-valued, the subtraction-safe spelling is `2e + 2 - n`. -/
theorem connected_graph_kernel_dimension
    (d : V →L[ℝ] W) (n e : ℕ)
    (hV : Module.finrank ℝ V = n)
    (hW : Module.finrank ℝ W = 2 * e)
    (hconn : Module.finrank ℝ (LinearMap.ker d.toLinearMap) = 1) :
    Module.finrank ℝ (LinearMap.ker (universalDirac d).toLinearMap) =
      2 * e + 2 - n := by
  have hrange : Module.finrank ℝ (LinearMap.range d.toLinearMap) = n - 1 := by
    have h := d.toLinearMap.finrank_range_add_finrank_ker
    omega
  have hadjRange :
      Module.finrank ℝ (LinearMap.range d.adjoint.toLinearMap) = n - 1 := by
    have h := d.toLinearMap.finrank_range_adjoint
    rw [ContinuousLinearMap.adjoint_toLinearMap, hrange] at h
    exact h
  have hadjKer :
      Module.finrank ℝ (LinearMap.ker d.adjoint.toLinearMap) = 2 * e - (n - 1) := by
    have h := d.adjoint.toLinearMap.finrank_range_add_finrank_ker
    omega
  have hadjRankNullity := d.adjoint.toLinearMap.finrank_range_add_finrank_ker
  have hbaseRankNullity := d.toLinearMap.finrank_range_add_finrank_ker
  rw [finrank_universalDirac_kernel, hconn, hadjKer]
  rw [hadjRange, hW] at hadjRankNullity
  rw [hconn, hV] at hbaseRankNullity
  have hn : 1 ≤ n := by omega
  have hne : n - 1 ≤ 2 * e := by omega
  omega

/-- In the periodic `A₃` cellulation used in the manuscript, `e = 6n`, so the
universal one-form Dirac nullity is `11n + 2`. -/
theorem periodic_A3_kernel_dimension
    (d : V →L[ℝ] W) (n : ℕ)
    (hV : Module.finrank ℝ V = n)
    (hW : Module.finrank ℝ W = 12 * n)
    (hconn : Module.finrank ℝ (LinearMap.ker d.toLinearMap) = 1) :
    Module.finrank ℝ (LinearMap.ker (universalDirac d).toLinearMap) =
      11 * n + 2 := by
  have h := connected_graph_kernel_dimension d n (6 * n) hV (by omega) hconn
  omega

/-- The periodic `A₃` nullities admit no uniform finite bound.  Consequently,
retaining all universal one-forms cannot supply a compact-resolvent limit via
a uniformly bounded zero-mode sector. -/
theorem periodic_A3_nullity_unbounded :
    ∀ M : ℕ, ∃ n : ℕ, M < 11 * n + 2 := by
  intro M
  exact ⟨M + 1, by omega⟩

/-- Exact bundled statement used by the Gran--Tensor ledger. -/
theorem extensive_universal_oneform_kernel
    (d : V →L[ℝ] W) (n e : ℕ)
    (hV : Module.finrank ℝ V = n)
    (hW : Module.finrank ℝ W = 2 * e)
    (hconn : Module.finrank ℝ (LinearMap.ker d.toLinearMap) = 1) :
    Module.finrank ℝ (LinearMap.ker (universalDirac d).toLinearMap) =
        2 * e + 2 - n ∧
      (e = 6 * n →
        Module.finrank ℝ (LinearMap.ker (universalDirac d).toLinearMap) =
          11 * n + 2) ∧
      (∀ M : ℕ, ∃ k : ℕ, M < 11 * k + 2) := by
  refine ⟨connected_graph_kernel_dimension d n e hV hW hconn, ?_,
    periodic_A3_nullity_unbounded⟩
  intro he
  have h := connected_graph_kernel_dimension d n e hV hW hconn
  omega

end NCG.UniversalOneFormDiracKernelGrowth
