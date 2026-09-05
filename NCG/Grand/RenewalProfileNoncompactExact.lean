/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The global renewal resolvent is noncompact: orthonormal escape

Record-local machinery for the infinite-volume clause of
`thm:concrete-renewal-continuum-profile`: in the countable-product renewal
field the Walsh modes form an infinite orthonormal family on which the
global transfer/resolvent acts with equal spectral weight, so the global
resolvent is not a compact operator.

* `tendsto_inner_orthonormal_zero`: every orthonormal sequence is weakly
  null (Bessel's inequality);
* `not_isCompactOperator_of_orthonormal_lower_bound`: a bounded operator
  whose images of an orthonormal sequence keep norm `>= eps > 0` is not
  compact — a compact operator maps the weakly-null orthonormal modes to a
  norm-null sequence;
* `not_isCompactOperator_of_orthonormal_eigen`: an operator with an
  orthonormal sequence of eigenvectors whose eigenvalues stay bounded away
  from zero (the equal-weight Walsh modes of the global renewal resolvent)
  is not compact.
-/

open Filter Topology

namespace NCG
namespace RenewalNoncompact

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Orthonormal sequences are weakly null** (Bessel's inequality). -/
theorem tendsto_inner_orthonormal_zero (e : ℕ → H) (he : Orthonormal ℂ e)
    (y : H) : Tendsto (fun n => inner ℂ y (e n)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsum : Summable fun n => ‖inner ℂ (e n) y‖ ^ 2 :=
    he.inner_products_summable (x := y)
  have hsq : Tendsto (fun n => ‖inner ℂ (e n) y‖ ^ 2) atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero, Function.comp_def] at hsqrt
  have heq : (fun n => Real.sqrt (‖inner ℂ (e n) y‖ ^ 2))
      = fun n => ‖inner ℂ y (e n)‖ := by
    funext n
    rw [Real.sqrt_sq (norm_nonneg _), norm_inner_symm]
  rwa [heq] at hsqrt

/-- **A uniform lower bound on the images of an orthonormal sequence
excludes compactness**: a compact operator maps the weakly-null orthonormal
modes to a norm-null sequence. -/
theorem not_isCompactOperator_of_orthonormal_lower_bound [CompleteSpace H]
    (e : ℕ → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] H) {ε : ℝ} (hε : 0 < ε)
    (hlow : ∀ n, ε ≤ ‖T (e n)‖) : ¬ IsCompactOperator (⇑T) := by
  intro hT
  have hT' : IsCompactOperator (⇑(T : H →ₗ[ℂ] H)) := by
    rwa [ContinuousLinearMap.coe_coe]
  have hbdd : Bornology.IsBounded (Set.range e) := by
    have hsub : Set.range e ⊆ Metric.closedBall (0 : H) 1 := by
      rintro - ⟨n, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq (he.1 n)
    exact Metric.isBounded_closedBall.subset hsub
  have hK : IsCompact (closure ((T : H →ₗ[ℂ] H) '' Set.range e)) :=
    hT'.isCompact_closure_image_of_bounded hbdd
  obtain ⟨z, -, ψ, hψ, hconv⟩ := hK.isSeqCompact
    (x := fun n => T (e n))
    (fun n => subset_closure ⟨e n, Set.mem_range_self n, rfl⟩)
  rw [Function.comp_def] at hconv
  have hz : z = 0 := by
    have hy : ∀ y : H, inner ℂ y z = 0 := by
      intro y
      have hweak : Tendsto
          (fun n => inner ℂ (ContinuousLinearMap.adjoint T y) (e n))
          atTop (𝓝 0) := tendsto_inner_orthonormal_zero e he _
      have hweakψ := hweak.comp hψ.tendsto_atTop
      rw [Function.comp_def] at hweakψ
      have hlim : Tendsto (fun n => inner ℂ y (T (e (ψ n)))) atTop
          (𝓝 (inner ℂ y z)) := Filter.Tendsto.inner tendsto_const_nhds hconv
      have heqf : (fun n => inner ℂ y (T (e (ψ n))))
          = fun n => inner ℂ (ContinuousLinearMap.adjoint T y) (e (ψ n)) := by
        funext n
        rw [ContinuousLinearMap.adjoint_inner_left]
      rw [heqf] at hlim
      exact tendsto_nhds_unique hlim hweakψ
    exact inner_self_eq_zero.mp (hy z)
  have hnorm : Tendsto (fun n => ‖T (e (ψ n))‖) atTop (𝓝 ‖z‖) := hconv.norm
  rw [hz, norm_zero] at hnorm
  have hεle : ε ≤ 0 :=
    ge_of_tendsto hnorm (Filter.Eventually.of_forall fun n => hlow (ψ n))
  exact absurd hεle (not_le.mpr hε)

/-- **Equal-weight orthonormal eigenmodes exclude compactness**: the global
renewal resolvent keeps every Walsh mode at spectral weight bounded away
from zero, hence is not compact. -/
theorem not_isCompactOperator_of_orthonormal_eigen [CompleteSpace H]
    (e : ℕ → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] H) (μ : ℕ → ℂ) {ε : ℝ}
    (hε : 0 < ε) (heig : ∀ n, T (e n) = μ n • e n) (hμ : ∀ n, ε ≤ ‖μ n‖) :
    ¬ IsCompactOperator (⇑T) :=
  not_isCompactOperator_of_orthonormal_lower_bound e he T hε fun n => by
    rw [heig n, norm_smul, he.1 n, mul_one]
    exact hμ n

end RenewalNoncompact
end NCG
