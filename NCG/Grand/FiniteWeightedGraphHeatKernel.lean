/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteMarkovHeatKernel

/-!
# Heat kernels of finite weighted graphs

This file instantiates finite Markov uniformization for the self-adjoint
weighted graph Laplacian occurring in the operational Sobolev--Weyl theorem.
-/

open scoped BigOperators

noncomputable section

namespace NCG

/-- A finite weighted graph with strictly positive vertex masses and
nonnegative symmetric conductances.  Zero conductance records a missing edge. -/
structure FiniteWeightedGraph (V : Type*) [Fintype V] where
  mass : V → ℝ
  conductance : V → V → ℝ
  mass_pos : ∀ v, 0 < mass v
  conductance_nonneg : ∀ u v, 0 ≤ conductance u v
  conductance_symm : ∀ u v, conductance u v = conductance v u

namespace FiniteWeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : FiniteWeightedGraph V)

/-- Weighted degree, including a harmless possible diagonal conductance. -/
def degree (v : V) : ℝ := ∑ u, G.conductance v u

theorem degree_nonneg (v : V) : 0 ≤ G.degree v :=
  Finset.sum_nonneg fun u _ => G.conductance_nonneg v u

/-- A canonical uniformization rate strictly larger than every exit rate. -/
def uniformizationRate : ℝ := 1 + ∑ v, G.degree v / G.mass v

theorem uniformizationRate_pos : 0 < G.uniformizationRate := by
  unfold uniformizationRate
  have : 0 ≤ ∑ v, G.degree v / G.mass v :=
    Finset.sum_nonneg fun v _ => div_nonneg (G.degree_nonneg v) (G.mass_pos v).le
  linarith

theorem exitRate_lt_uniformizationRate (v : V) :
    G.degree v / G.mass v < G.uniformizationRate := by
  unfold uniformizationRate
  have hterm : 0 ≤ G.degree v / G.mass v :=
    div_nonneg (G.degree_nonneg v) (G.mass_pos v).le
  have hle : G.degree v / G.mass v ≤ ∑ u, G.degree u / G.mass u :=
    Finset.single_le_sum
      (fun u _ => div_nonneg (G.degree_nonneg u) (G.mass_pos u).le)
      (Finset.mem_univ v)
  linarith

/-- The stochastic matrix `I - Δ/Λ`, written entrywise. -/
def transition : Matrix V V ℝ := fun v u =>
  (if v = u then 1 else 0) +
    (G.conductance v u - if v = u then G.degree v else 0) /
      (G.uniformizationRate * G.mass v)

theorem transition_offdiag {v u : V} (hvu : v ≠ u) :
    G.transition v u =
      G.conductance v u / (G.uniformizationRate * G.mass v) := by
  simp [transition, hvu]

theorem transition_diag (v : V) :
    G.transition v v = 1 +
      (G.conductance v v - G.degree v) /
        (G.uniformizationRate * G.mass v) := by
  simp [transition]

theorem transition_nonnegative : Matrix.EntrywiseNonnegative G.transition := by
  intro v u
  by_cases hvu : v = u
  · subst u
    rw [G.transition_diag]
    have hΛμ : 0 < G.uniformizationRate * G.mass v :=
      mul_pos G.uniformizationRate_pos (G.mass_pos v)
    have hdeg : G.degree v < G.uniformizationRate * G.mass v := by
      have h := G.exitRate_lt_uniformizationRate v
      exact (div_lt_iff₀ (G.mass_pos v)).mp h
    have hcvv : 0 ≤ G.conductance v v := G.conductance_nonneg v v
    rw [show 1 + (G.conductance v v - G.degree v) /
        (G.uniformizationRate * G.mass v) =
        (G.uniformizationRate * G.mass v + G.conductance v v - G.degree v) /
          (G.uniformizationRate * G.mass v) by
            apply (eq_div_iff hΛμ.ne').2
            rw [add_mul]
            rw [div_mul_cancel₀ _ hΛμ.ne']
            ring]
    exact div_nonneg (by linarith) hΛμ.le
  · rw [G.transition_offdiag hvu]
    exact div_nonneg (G.conductance_nonneg v u)
      (mul_nonneg G.uniformizationRate_pos.le (G.mass_pos v).le)

theorem transition_rowSum (v : V) : ∑ u, G.transition v u = 1 := by
  unfold transition
  rw [Finset.sum_add_distrib]
  have hdelta : ∑ u : V, (if v = u then (1 : ℝ) else 0) = 1 := by simp
  rw [hdelta]
  have hden : G.uniformizationRate * G.mass v ≠ 0 :=
    (mul_pos G.uniformizationRate_pos (G.mass_pos v)).ne'
  have hnum : ∑ u : V,
      (G.conductance v u - if v = u then G.degree v else 0) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp [degree]
  rw [← Finset.sum_div, hnum, zero_div, add_zero]

theorem transition_rowStochastic : Matrix.RowStochastic G.transition :=
  ⟨G.transition_nonnegative, G.transition_rowSum⟩

/-- Detailed balance of the uniformized transition. -/
theorem transition_detailedBalance (v u : V) :
    G.mass v * G.transition v u = G.mass u * G.transition u v := by
  by_cases hvu : v = u
  · subst u
    rfl
  · rw [G.transition_offdiag hvu, G.transition_offdiag (Ne.symm hvu)]
    rw [G.conductance_symm]
    have hΛ : G.uniformizationRate ≠ 0 := G.uniformizationRate_pos.ne'
    have hmv : G.mass v ≠ 0 := (G.mass_pos v).ne'
    have hmu : G.mass u ≠ 0 := (G.mass_pos u).ne'
    field_simp

theorem transition_detailedBalance' :
    Matrix.DetailedBalance G.mass G.transition :=
  G.transition_detailedBalance

/-- The uniformized heat kernel. -/
def heatKernel (t : ℝ) : Matrix V V ℝ :=
  Real.exp (-(G.uniformizationRate * t)) •
    Matrix.exponentialEntry ((G.uniformizationRate * t) • G.transition)

theorem heatKernel_rowStochastic (t : ℝ) (ht : 0 ≤ t) :
    Matrix.RowStochastic (G.heatKernel t) := by
  have hs := Matrix.exponentialEntry_uniformized_rowStochastic
    G.transition G.transition_rowStochastic (G.uniformizationRate * t)
    (mul_nonneg G.uniformizationRate_pos.le ht)
  simpa [heatKernel] using hs

theorem heatKernel_detailedBalance (t : ℝ) :
    Matrix.DetailedBalance G.mass (G.heatKernel t) := by
  have hs := Matrix.exponentialEntry_uniformized_detailedBalance
    G.mass G.transition G.transition_detailedBalance'
    (G.uniformizationRate * t)
  simpa [heatKernel] using hs

/-- Weighted mass is preserved by the heat kernel. -/
theorem heatKernel_weightedColumnSum (t : ℝ) (ht : 0 ≤ t) (u : V) :
    ∑ v, G.mass v * G.heatKernel t v u = G.mass u := by
  calc
    (∑ v, G.mass v * G.heatKernel t v u)
        = ∑ v, G.mass u * G.heatKernel t u v := by
            apply Finset.sum_congr rfl
            intro v _
            exact G.heatKernel_detailedBalance t v u
    _ = G.mass u * ∑ v, G.heatKernel t u v := by rw [Finset.mul_sum]
    _ = G.mass u := by
      have hrow := (G.heatKernel_rowStochastic t ht).2 u
      rw [hrow, mul_one]

/-- The weighted heat action on vertex functions. -/
def heatApply (t : ℝ) (f : V → ℝ) (v : V) : ℝ :=
  ∑ u, G.heatKernel t v u * f u

/-- The self-adjoint weighted graph Laplacian conjugated to ordinary
Euclidean coordinates by multiplication with `sqrt mass`. -/
def symmetricLaplacian : Matrix V V ℝ := fun v u =>
  (if v = u then G.degree v / G.mass v else 0) -
    G.conductance v u / (Real.sqrt (G.mass v) * Real.sqrt (G.mass u))

theorem symmetricLaplacian_isHermitian :
    Matrix.IsHermitian G.symmetricLaplacian := by
  rw [Matrix.isHermitian_iff_isSymm]
  rw [Matrix.IsSymm.ext_iff]
  intro v u
  unfold symmetricLaplacian
  rw [G.conductance_symm]
  by_cases hvu : v = u
  · subst u
    rfl
  · simp [hvu, Ne.symm hvu, mul_comm]

theorem symmetricLaplacian_quadraticForm (x : V → ℝ) :
    dotProduct (star x) (Matrix.mulVec G.symmetricLaplacian x) =
      finiteSpatialEnergy G.conductance
        (fun v => x v / Real.sqrt (G.mass v)) := by
  let f : V → ℝ := fun v => x v / Real.sqrt (G.mass v)
  have hsqrt (v : V) : 0 < Real.sqrt (G.mass v) :=
    Real.sqrt_pos.2 (G.mass_pos v)
  have hmass (v : V) : (Real.sqrt (G.mass v)) ^ 2 = G.mass v :=
    Real.sq_sqrt (G.mass_pos v).le
  have hx (v : V) : x v = Real.sqrt (G.mass v) * f v := by
    unfold f
    field_simp [ne_of_gt (hsqrt v)]
  have henergy : finiteSpatialEnergy G.conductance f =
      (∑ v, G.degree v * f v ^ 2) -
        ∑ v, ∑ u, G.conductance v u * f v * f u := by
    unfold finiteSpatialEnergy degree
    have hfirst :
        ∑ v, ∑ u, G.conductance v u * f v ^ 2 =
          ∑ v, (∑ u, G.conductance v u) * f v ^ 2 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_mul]
    have hsecond :
        ∑ v, ∑ u, G.conductance v u * f u ^ 2 =
          ∑ v, (∑ u, G.conductance v u) * f v ^ 2 := by
      calc
        (∑ v, ∑ u, G.conductance v u * f u ^ 2)
            = ∑ u, ∑ v, G.conductance v u * f u ^ 2 := Finset.sum_comm
        _ = ∑ u, (∑ v, G.conductance u v) * f u ^ 2 := by
              apply Finset.sum_congr rfl
              intro u _
              have hsymm : (∑ v, G.conductance v u) =
                  ∑ v, G.conductance u v := by
                apply Finset.sum_congr rfl
                intro v _
                exact G.conductance_symm v u
              calc
                (∑ v, G.conductance v u * f u ^ 2) =
                    (∑ v, G.conductance v u) * f u ^ 2 := by
                      rw [Finset.sum_mul]
                _ = (∑ v, G.conductance u v) * f u ^ 2 := by rw [hsymm]
    rw [show (∑ v, ∑ u, G.conductance v u * (f v - f u) ^ 2) =
        (∑ v, ∑ u, G.conductance v u * f v ^ 2) +
        (∑ v, ∑ u, G.conductance v u * f u ^ 2) -
        2 * (∑ v, ∑ u, G.conductance v u * f v * f u) by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib,
            ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro v _
          apply Finset.sum_congr rfl
          intro u _
          ring]
    rw [hfirst, hsecond]
    ring
  change dotProduct (star x) (Matrix.mulVec G.symmetricLaplacian x) =
    finiteSpatialEnergy G.conductance f
  rw [henergy]
  unfold symmetricLaplacian
  simp only [starRingEnd_apply, star_id_of_comm, dotProduct, Matrix.mulVec]
  rw [show (∑ v, x v * ∑ u,
      ((if v = u then G.degree v / G.mass v else 0) -
        G.conductance v u /
          (Real.sqrt (G.mass v) * Real.sqrt (G.mass u))) * x u) =
      (∑ v, G.degree v * f v ^ 2) -
        ∑ v, ∑ u, G.conductance v u * f v * f u by
    rw [show (∑ v, x v * ∑ u,
        ((if v = u then G.degree v / G.mass v else 0) -
          G.conductance v u /
            (Real.sqrt (G.mass v) * Real.sqrt (G.mass u))) * x u) =
        (∑ v, x v * ∑ u,
          (if v = u then G.degree v / G.mass v else 0) * x u) -
        (∑ v, x v * ∑ u,
          (G.conductance v u /
            (Real.sqrt (G.mass v) * Real.sqrt (G.mass u))) * x u) by
          simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
          rw [Finset.sum_sub_distrib]]
    congr 1
    · apply Finset.sum_congr rfl
      intro v _
      simp only [Finset.mul_sum]
      rw [Finset.sum_ite_eq' Finset.univ v (Finset.mem_univ v)]
      rw [hx v, hmass v]
      field_simp [ne_of_gt (hsqrt v)]
      ring
    · apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro u _
      rw [hx v, hx u]
      field_simp [ne_of_gt (hsqrt v), ne_of_gt (hsqrt u)]
      ring]

theorem symmetricLaplacian_posSemidef :
    Matrix.PosSemidef G.symmetricLaplacian := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    G.symmetricLaplacian_isHermitian
  intro x
  rw [G.symmetricLaplacian_quadraticForm]
  unfold finiteSpatialEnergy
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ =>
    Finset.sum_nonneg fun v _ =>
      mul_nonneg (G.conductance_nonneg u v) (sq_nonneg _))

/-- The canonical finite weighted-Laplacian spectrum. -/
def eigenvalue : V → ℝ :=
  G.symmetricLaplacian_isHermitian.eigenvalues

theorem eigenvalue_nonnegative (j : V) : 0 ≤ G.eigenvalue j :=
  G.symmetricLaplacian_posSemidef.eigenvalues_nonneg j

/-- Detailed balance and stochasticity imply weighted L1 contraction. -/
theorem heatApply_weightedL1_le
    (t : ℝ) (ht : 0 ≤ t) (f : V → ℝ) :
    ∑ v, G.mass v * |G.heatApply t f v| ≤ ∑ v, G.mass v * |f v| := by
  have hnonneg := (G.heatKernel_rowStochastic t ht).1
  calc
    (∑ v, G.mass v * |G.heatApply t f v|)
        ≤ ∑ v, G.mass v * ∑ u, G.heatKernel t v u * |f u| := by
            apply Finset.sum_le_sum
            intro v _
            apply mul_le_mul_of_nonneg_left _ (G.mass_pos v).le
            unfold heatApply
            calc
              |∑ u, G.heatKernel t v u * f u|
                  ≤ ∑ u, |G.heatKernel t v u * f u| :=
                    Finset.abs_sum_le_sum_abs _ _
              _ = ∑ u, G.heatKernel t v u * |f u| := by
                    apply Finset.sum_congr rfl
                    intro u _
                    rw [abs_mul, abs_of_nonneg (hnonneg v u)]
    _ = ∑ u, (∑ v, G.mass v * G.heatKernel t v u) * |f u| := by
          calc
            (∑ v, G.mass v * ∑ u, G.heatKernel t v u * |f u|)
                = ∑ v, ∑ u, (G.mass v * G.heatKernel t v u) * |f u| := by
                    apply Finset.sum_congr rfl
                    intro v _
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro u _
                    ring
            _ = ∑ u, ∑ v, (G.mass v * G.heatKernel t v u) * |f u| :=
              Finset.sum_comm
            _ = ∑ u, (∑ v, G.mass v * G.heatKernel t v u) * |f u| := by
                    apply Finset.sum_congr rfl
                    intro u _
                    rw [Finset.sum_mul]
    _ = ∑ u, G.mass u * |f u| := by
          apply Finset.sum_congr rfl
          intro u _
          rw [G.heatKernel_weightedColumnSum t ht u]

end FiniteWeightedGraph

end NCG
