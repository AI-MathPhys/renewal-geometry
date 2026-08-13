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
  (if v = u then G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) -
    G.conductance v u * (Real.sqrt (G.mass v))⁻¹ *
      (Real.sqrt (G.mass u))⁻¹

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
  · simp [hvu, Ne.symm hvu]
    ring

theorem symmetricLaplacian_quadraticForm (x : V → ℝ) :
    dotProduct (star x) (Matrix.mulVec G.symmetricLaplacian x) =
      finiteSpatialEnergy G.conductance
        (fun v => x v / Real.sqrt (G.mass v)) := by
  let f : V → ℝ := fun v => x v / Real.sqrt (G.mass v)
  have hsqrt (v : V) : 0 < Real.sqrt (G.mass v) :=
    Real.sqrt_pos.2 (G.mass_pos v)
  have hx (v : V) : x v = Real.sqrt (G.mass v) * f v := by
    unfold f
    rw [div_eq_mul_inv]
    have hs : Real.sqrt (G.mass v) * (Real.sqrt (G.mass v))⁻¹ = 1 :=
      mul_inv_cancel₀ (hsqrt v).ne'
    calc
      x v = 1 * x v := by ring
      _ = (Real.sqrt (G.mass v) * (Real.sqrt (G.mass v))⁻¹) * x v := by rw [hs]
      _ = Real.sqrt (G.mass v) * (x v * (Real.sqrt (G.mass v))⁻¹) := by ring
  have hdiag (v : V) :
      x v * (G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 * x v) =
        G.degree v * f v ^ 2 := by
    rw [hx v]
    have hs : Real.sqrt (G.mass v) * (Real.sqrt (G.mass v))⁻¹ = 1 :=
      mul_inv_cancel₀ (hsqrt v).ne'
    calc
      Real.sqrt (G.mass v) * f v *
          (G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 *
            (Real.sqrt (G.mass v) * f v)) =
          G.degree v * f v ^ 2 *
            (Real.sqrt (G.mass v) * (Real.sqrt (G.mass v))⁻¹) ^ 2 := by ring
      _ = G.degree v * f v ^ 2 := by rw [hs]; ring
  have hoff (v u : V) :
      x v * (G.conductance v u * (Real.sqrt (G.mass v))⁻¹ *
        (Real.sqrt (G.mass u))⁻¹ * x u) =
        G.conductance v u * f v * f u := by
    rw [hx v, hx u]
    have hsv : Real.sqrt (G.mass v) * (Real.sqrt (G.mass v))⁻¹ = 1 :=
      mul_inv_cancel₀ (hsqrt v).ne'
    have hsu : Real.sqrt (G.mass u) * (Real.sqrt (G.mass u))⁻¹ = 1 :=
      mul_inv_cancel₀ (hsqrt u).ne'
    calc
      Real.sqrt (G.mass v) * f v *
          (G.conductance v u * (Real.sqrt (G.mass v))⁻¹ *
            (Real.sqrt (G.mass u))⁻¹ * (Real.sqrt (G.mass u) * f u)) =
          G.conductance v u * f v * f u *
            (Real.sqrt (G.mass v) * (Real.sqrt (G.mass v))⁻¹) *
            (Real.sqrt (G.mass u) * (Real.sqrt (G.mass u))⁻¹) := by ring
      _ = G.conductance v u * f v * f u := by rw [hsv, hsu]; ring
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
      ((if v = u then G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) -
        G.conductance v u * (Real.sqrt (G.mass v))⁻¹ *
          (Real.sqrt (G.mass u))⁻¹) * x u) =
      (∑ v, G.degree v * f v ^ 2) -
        ∑ v, ∑ u, G.conductance v u * f v * f u by
    rw [show (∑ v, x v * ∑ u,
        ((if v = u then G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) -
          G.conductance v u * (Real.sqrt (G.mass v))⁻¹ *
            (Real.sqrt (G.mass u))⁻¹) * x u) =
        (∑ v, x v * ∑ u,
          (if v = u then G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) * x u) -
        (∑ v, x v * ∑ u,
          (G.conductance v u * (Real.sqrt (G.mass v))⁻¹ *
            (Real.sqrt (G.mass u))⁻¹) * x u) by
          simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
          ]
    congr 1
    · apply Finset.sum_congr rfl
      intro v _
      simp only [Finset.mul_sum]
      calc
        (∑ u, x v * ((if v = u then
            G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) * x u)) =
            x v * (G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 * x v) := by
              rw [show (∑ u, x v * ((if v = u then
                  G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) * x u)) =
                  ∑ u, (if v = u then
                    x v * (G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 * x u)
                  else 0) by
                    apply Finset.sum_congr rfl
                    intro u _
                    split_ifs <;> ring]
              rw [Fintype.sum_ite_eq v]
        _ = G.degree v * f v ^ 2 := hdiag v
    · apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      exact hoff v u]

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

/-- Euclidean eigenvectors of the conjugated Laplacian. -/
def eigenvector (j : V) : V → ℝ :=
  ⇑(G.symmetricLaplacian_isHermitian.eigenvectorBasis j)

theorem symmetricLaplacian_mulVec_eigenvector (j : V) :
    Matrix.mulVec G.symmetricLaplacian (G.eigenvector j) =
      G.eigenvalue j • G.eigenvector j := by
  exact G.symmetricLaplacian_isHermitian.mulVec_eigenvectorBasis j

/-- Weighted eigenfunctions in `L²(V,mass)`. -/
def eigenfunction (j v : V) : ℝ :=
  G.eigenvector j v * (Real.sqrt (G.mass v))⁻¹

/-- The weighted eigenfunctions are orthonormal in `L²(V,mass)`. -/
theorem eigenfunction_weighted_orthonormal (i j : V) :
    ∑ v, G.mass v * G.eigenfunction i v * G.eigenfunction j v =
      if i = j then 1 else 0 := by
  have hsqrt (v : V) : 0 < Real.sqrt (G.mass v) :=
    Real.sqrt_pos.2 (G.mass_pos v)
  have hterm (v : V) :
      G.mass v * G.eigenfunction i v * G.eigenfunction j v =
        G.eigenvector i v * G.eigenvector j v := by
    unfold eigenfunction
    have hsquare : Real.sqrt (G.mass v) ^ 2 = G.mass v :=
      Real.sq_sqrt (G.mass_pos v).le
    field_simp [(hsqrt v).ne']
    rw [hsquare]
    ring
  simp_rw [hterm]
  have hortho := G.symmetricLaplacian_isHermitian.eigenvectorBasis.orthonormal
  rw [orthonormal_iff_ite] at hortho
  have hij := hortho i j
  simpa [eigenvector, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, mul_comm] using hij

/-- The quadratic form of the conjugated Laplacian is diagonal in its
canonical orthonormal eigenbasis. -/
theorem symmetricLaplacian_quadraticForm_eigenExpansion (a : V → ℝ) :
    dotProduct (star (∑ j, a j • G.eigenvector j))
        (Matrix.mulVec G.symmetricLaplacian (∑ j, a j • G.eigenvector j)) =
      ∑ j, G.eigenvalue j * a j ^ 2 := by
  have hmul :
      Matrix.mulVec G.symmetricLaplacian (∑ j, a j • G.eigenvector j) =
        ∑ j, (G.eigenvalue j * a j) • G.eigenvector j := by
    rw [Matrix.mulVec_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mulVec_smul, G.symmetricLaplacian_mulVec_eigenvector]
    ext v
    simp [mul_assoc, mul_comm, mul_left_comm]
  rw [hmul]
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_sum, map_mul, starRingEnd_apply, star_trivial]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hortho (i : V) :
      ∑ v, G.eigenvector i v * G.eigenvector j v =
        if i = j then 1 else 0 := by
    have h := G.eigenfunction_weighted_orthonormal i j
    have hsqrt (v : V) : 0 < Real.sqrt (G.mass v) :=
      Real.sqrt_pos.2 (G.mass_pos v)
    have hterm (v : V) :
        G.mass v * G.eigenfunction i v * G.eigenfunction j v =
          G.eigenvector i v * G.eigenvector j v := by
      unfold eigenfunction
      have hsquare : Real.sqrt (G.mass v) ^ 2 = G.mass v :=
        Real.sq_sqrt (G.mass_pos v).le
      field_simp [(hsqrt v).ne']
      rw [hsquare]
      ring
    simpa only [hterm] using h
  calc
    (∑ i, ∑ v,
        a i * G.eigenvector i v *
          (G.eigenvalue j * a j * G.eigenvector j v)) =
        ∑ i, (a i * (G.eigenvalue j * a j)) *
          ∑ v, G.eigenvector i v * G.eigenvector j v := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro v _
            ring
    _ = ∑ i, (a i * (G.eigenvalue j * a j)) *
          (if i = j then 1 else 0) := by simp_rw [hortho]
    _ = G.eigenvalue j * a j ^ 2 := by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
            Finset.sum_ite_eq', Finset.mem_univ, if_pos]
          ring

/-- Completeness of the weighted eigenfunctions, in kernel form. -/
theorem eigenfunction_completeness (v u : V) :
    ∑ j, G.eigenfunction j v * G.eigenfunction j u =
      if v = u then (G.mass v)⁻¹ else 0 := by
  let U : Matrix V V ℝ :=
    G.symmetricLaplacian_isHermitian.eigenvectorUnitary
  have hunit : U * star U = 1 :=
    Unitary.coe_mul_star_self G.symmetricLaplacian_isHermitian.eigenvectorUnitary
  have hvu := congrFun (congrFun hunit v) u
  change (∑ j, U v j * (star U) j u) = (1 : Matrix V V ℝ) v u at hvu
  have hstar (j : V) : (star U) j u = G.eigenvector j u := by
    change star (U u j) = G.eigenvector j u
    simp [U, eigenvector]
  have hU (j : V) : U v j = G.eigenvector j v := by
    simp [U, eigenvector]
  simp_rw [hstar, hU] at hvu
  have hsqrtv : Real.sqrt (G.mass v) ≠ 0 :=
    (Real.sqrt_pos.2 (G.mass_pos v)).ne'
  have hsqrtu : Real.sqrt (G.mass u) ≠ 0 :=
    (Real.sqrt_pos.2 (G.mass_pos u)).ne'
  unfold eigenfunction
  by_cases hvu' : v = u
  · subst u
    simp only [if_pos]
    have hsquare : Real.sqrt (G.mass v) ^ 2 = G.mass v :=
      Real.sq_sqrt (G.mass_pos v).le
    have hvv : (∑ j, G.eigenvector j v * G.eigenvector j v) = 1 := by
      simpa [Matrix.one_apply] using hvu
    calc
      (∑ j, (G.eigenvector j v * (Real.sqrt (G.mass v))⁻¹) *
          (G.eigenvector j v * (Real.sqrt (G.mass v))⁻¹)) =
          (Real.sqrt (G.mass v))⁻¹ ^ 2 *
            ∑ j, G.eigenvector j v * G.eigenvector j v := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (Real.sqrt (G.mass v))⁻¹ ^ 2 := by rw [hvv]; ring
      _ = ((Real.sqrt (G.mass v)) ^ 2)⁻¹ := by
            rw [inv_pow]
      _ = (G.mass v)⁻¹ := by rw [hsquare]
  · simp only [hvu', if_false]
    have hzero : (∑ j, G.eigenvector j v * G.eigenvector j u) = 0 := by
      simpa [Matrix.one_apply, hvu'] using hvu
    calc
      (∑ j, (G.eigenvector j v * (Real.sqrt (G.mass v))⁻¹) *
          (G.eigenvector j u * (Real.sqrt (G.mass u))⁻¹)) =
          ((Real.sqrt (G.mass v))⁻¹ * (Real.sqrt (G.mass u))⁻¹) *
            ∑ j, G.eigenvector j v * G.eigenvector j u := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = 0 := by rw [hzero, mul_zero]

theorem eigenfunction_weighted_norm (j : V) :
    ∑ v, G.mass v * G.eigenfunction j v ^ 2 = 1 := by
  have h := G.eigenfunction_weighted_orthonormal j j
  rw [if_pos rfl] at h
  calc
    (∑ v, G.mass v * G.eigenfunction j v ^ 2) =
        ∑ v, G.mass v * G.eigenfunction j v * G.eigenfunction j v := by
          apply Finset.sum_congr rfl
          intro v _
          ring
    _ = 1 := h

/-- The Dirichlet energy of a normalized eigenfunction is its eigenvalue. -/
theorem eigenfunction_energy (j : V) :
    finiteSpatialEnergy G.conductance (G.eigenfunction j) = G.eigenvalue j := by
  have hquad := G.symmetricLaplacian_quadraticForm (G.eigenvector j)
  have heig := G.symmetricLaplacian_mulVec_eigenvector j
  rw [heig] at hquad
  have hsqrt (v : V) : Real.sqrt (G.mass v) ≠ 0 :=
    (Real.sqrt_pos.2 (G.mass_pos v)).ne'
  have hfun : (fun v => G.eigenvector j v / Real.sqrt (G.mass v)) =
      G.eigenfunction j := by
    funext v
    unfold eigenfunction
    rw [div_eq_mul_inv]
  rw [hfun] at hquad
  have hnorm : dotProduct (star (G.eigenvector j)) (G.eigenvector j) = 1 := by
    have h := G.eigenfunction_weighted_norm j
    have hsquare (v : V) : Real.sqrt (G.mass v) ^ 2 = G.mass v :=
      Real.sq_sqrt (G.mass_pos v).le
    have hterm (v : V) :
        G.mass v * G.eigenfunction j v ^ 2 = G.eigenvector j v ^ 2 := by
      unfold eigenfunction
      have hmass : G.mass v = Real.sqrt (G.mass v) ^ 2 := (hsquare v).symm
      have hsqrtMass : Real.sqrt (Real.sqrt (G.mass v) ^ 2) =
          Real.sqrt (G.mass v) :=
        Real.sqrt_sq_eq_abs _ |>.trans
          (abs_of_pos (Real.sqrt_pos.2 (G.mass_pos v)))
      rw [hmass, hsqrtMass]
      calc
        Real.sqrt (G.mass v) ^ 2 *
            (G.eigenvector j v * (Real.sqrt (G.mass v))⁻¹) ^ 2 =
            G.eigenvector j v ^ 2 *
              (Real.sqrt (G.mass v) ^ 2 *
                (Real.sqrt (G.mass v))⁻¹ ^ 2) := by ring
        _ = G.eigenvector j v ^ 2 * 1 := by
              congr 1
              field_simp [hsqrt v]
        _ = G.eigenvector j v ^ 2 := by ring
    unfold dotProduct
    simp only [star_id_of_comm]
    calc
      (∑ i, G.eigenvector j i * G.eigenvector j i) =
          ∑ i, G.eigenvector j i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = ∑ i, G.mass i * G.eigenfunction j i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            exact (hterm i).symm
      _ = 1 := h
  calc
    finiteSpatialEnergy G.conductance (G.eigenfunction j) =
        dotProduct (star (G.eigenvector j))
          (G.eigenvalue j • G.eigenvector j) := hquad.symm
    _ = G.eigenvalue j *
        dotProduct (star (G.eigenvector j)) (G.eigenvector j) := by
          unfold dotProduct
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          simp only [Pi.smul_apply, smul_eq_mul, starRingEnd_apply, star_id_of_comm]
          ring
    _ = G.eigenvalue j := by rw [hnorm, mul_one]

/-- The weighted graph Laplacian in function coordinates. -/
def laplacianApply (f : V → ℝ) (v : V) : ℝ :=
  (∑ u, G.conductance v u * (f v - f u)) / G.mass v

theorem transition_mulVec_eq (f : V → ℝ) (v : V) :
    Matrix.mulVec G.transition f v =
      f v - G.uniformizationRate⁻¹ * G.laplacianApply f v := by
  unfold Matrix.mulVec transition laplacianApply degree
  have hΛ : G.uniformizationRate ≠ 0 := G.uniformizationRate_pos.ne'
  have hμ : G.mass v ≠ 0 := (G.mass_pos v).ne'
  change (∑ u, ((if v = u then 1 else 0) +
      (G.conductance v u - if v = u then ∑ x, G.conductance v x else 0) /
        (G.uniformizationRate * G.mass v)) * f u) = _
  simp only [add_mul, Finset.sum_add_distrib]
  have hdelta : (∑ u : V, (if v = u then 1 else 0) * f u) = f v := by simp
  rw [hdelta]
  have hfrac : (∑ u : V,
      (G.conductance v u - if v = u then ∑ x, G.conductance v x else 0) /
        (G.uniformizationRate * G.mass v) * f u) =
      -G.uniformizationRate⁻¹ *
        ((∑ u, G.conductance v u * (f v - f u)) / G.mass v) := by
    have hden : G.uniformizationRate * G.mass v ≠ 0 := mul_ne_zero hΛ hμ
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    apply (div_eq_iff hden).2
    have hnum : (∑ u : V,
        (G.conductance v u - if v = u then ∑ x, G.conductance v x else 0) * f u) =
        (∑ u, G.conductance v u * f u) -
          (∑ x, G.conductance v x) * f v := by
      calc
        (∑ u : V,
            (G.conductance v u - if v = u then ∑ x, G.conductance v x else 0) * f u) =
            ∑ u, (G.conductance v u * f u -
              (if v = u then ∑ x, G.conductance v x else 0) * f u) := by
                apply Finset.sum_congr rfl
                intro u _
                ring
        _ = (∑ u, G.conductance v u * f u) -
            ∑ u, (if v = u then ∑ x, G.conductance v x else 0) * f u :=
              by rw [Finset.sum_sub_distrib]
        _ = (∑ u, G.conductance v u * f u) -
            (∑ x, G.conductance v x) * f v := by
              congr 1
              rw [show (∑ u : V,
                  (if v = u then ∑ x, G.conductance v x else 0) * f u) =
                  ∑ u : V, if v = u then (∑ x, G.conductance v x) * f u else 0 by
                    apply Finset.sum_congr rfl
                    intro u _
                    split_ifs <;> ring]
              rw [Fintype.sum_ite_eq v]
    rw [hnum]
    field_simp [hΛ, hμ]
    calc
      (∑ x, G.conductance v x * f x) -
          (∑ x, G.conductance v x) * f v =
          ∑ x, (G.conductance v x * f x -
            G.conductance v x * f v) := by
              rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = -∑ x, G.conductance v x * (f v - f x) := by
            rw [show -(∑ x, G.conductance v x * (f v - f x)) =
                ∑ x, -(G.conductance v x * (f v - f x)) by
                  rw [Finset.sum_neg_distrib]]
            apply Finset.sum_congr rfl
            intro x _
            ring
  rw [hfrac]
  ring

/-- The transition matrix conjugated to ordinary Euclidean coordinates. -/
def symmetricTransition : Matrix V V ℝ := fun v u =>
  Real.sqrt (G.mass v) * G.transition v u *
    (Real.sqrt (G.mass u))⁻¹

theorem symmetricTransition_eq :
    G.symmetricTransition = 1 - G.uniformizationRate⁻¹ • G.symmetricLaplacian := by
  ext v u
  have hsv : Real.sqrt (G.mass v) ≠ 0 := (Real.sqrt_pos.2 (G.mass_pos v)).ne'
  have hsu : Real.sqrt (G.mass u) ≠ 0 := (Real.sqrt_pos.2 (G.mass_pos u)).ne'
  have hmv : G.mass v = (Real.sqrt (G.mass v)) ^ 2 :=
    (Real.sq_sqrt (G.mass_pos v).le).symm
  have hΛ : G.uniformizationRate ≠ 0 := G.uniformizationRate_pos.ne'
  by_cases hvu : v = u
  · subst u
    unfold symmetricTransition
    rw [G.transition_diag]
    change Real.sqrt (G.mass v) *
        (1 + (G.conductance v v - G.degree v) /
          (G.uniformizationRate * G.mass v)) *
          (Real.sqrt (G.mass v))⁻¹ =
      (if v = v then 1 else 0) - G.uniformizationRate⁻¹ *
        ((if v = v then G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) -
          G.conductance v v * (Real.sqrt (G.mass v))⁻¹ *
            (Real.sqrt (G.mass v))⁻¹)
    simp only [if_pos]
    rw [hmv]
    have hsqrtMass : Real.sqrt ((Real.sqrt (G.mass v)) ^ 2) =
        Real.sqrt (G.mass v) := Real.sqrt_sq_eq_abs _ |>.trans
          (abs_of_pos (Real.sqrt_pos.2 (G.mass_pos v)))
    rw [hsqrtMass]
    field_simp [hsv, hΛ]
    ring
  · unfold symmetricTransition
    rw [G.transition_offdiag hvu]
    change Real.sqrt (G.mass v) *
        (G.conductance v u / (G.uniformizationRate * G.mass v)) *
          (Real.sqrt (G.mass u))⁻¹ =
      (if v = u then 1 else 0) - G.uniformizationRate⁻¹ *
        ((if v = u then G.degree v * (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) -
          G.conductance v u * (Real.sqrt (G.mass v))⁻¹ *
            (Real.sqrt (G.mass u))⁻¹)
    simp only [hvu, if_false, zero_sub]
    rw [hmv]
    have hsqrtMass : Real.sqrt ((Real.sqrt (G.mass v)) ^ 2) =
        Real.sqrt (G.mass v) := Real.sqrt_sq_eq_abs _ |>.trans
          (abs_of_pos (Real.sqrt_pos.2 (G.mass_pos v)))
    rw [hsqrtMass]
    field_simp [hsv, hsu, hΛ]

theorem symmetricTransition_mulVec_eigenvector (j : V) :
    Matrix.mulVec G.symmetricTransition (G.eigenvector j) =
      (1 - G.eigenvalue j / G.uniformizationRate) • G.eigenvector j := by
  rw [G.symmetricTransition_eq]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    G.symmetricLaplacian_mulVec_eigenvector]
  ext v
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [G.uniformizationRate_pos.ne']

theorem transition_mulVec_eigenfunction (j : V) :
    Matrix.mulVec G.transition (G.eigenfunction j) =
      (1 - G.eigenvalue j / G.uniformizationRate) • G.eigenfunction j := by
  have hs := G.symmetricTransition_mulVec_eigenvector j
  ext v
  have hsv : Real.sqrt (G.mass v) ≠ 0 := (Real.sqrt_pos.2 (G.mass_pos v)).ne'
  have hterm (u : V) :
      G.symmetricTransition v u * G.eigenvector j u =
        Real.sqrt (G.mass v) *
          (G.transition v u * G.eigenfunction j u) := by
    unfold symmetricTransition eigenfunction
    ring
  have hsum :
      Matrix.mulVec G.symmetricTransition (G.eigenvector j) v =
        Real.sqrt (G.mass v) *
          Matrix.mulVec G.transition (G.eigenfunction j) v := by
    simp only [Matrix.mulVec]
    calc
      (∑ u, G.symmetricTransition v u * G.eigenvector j u) =
          ∑ u, Real.sqrt (G.mass v) *
            (G.transition v u * G.eigenfunction j u) := by
              apply Finset.sum_congr rfl
              intro u _
              exact hterm u
      _ = Real.sqrt (G.mass v) *
          ∑ u, G.transition v u * G.eigenfunction j u := by
            rw [Finset.mul_sum]
  have hs_v := congrFun hs v
  rw [hsum] at hs_v
  unfold eigenfunction
  simp only [Pi.smul_apply, smul_eq_mul] at hs_v ⊢
  calc
    Matrix.mulVec G.transition (G.eigenfunction j) v =
        (Real.sqrt (G.mass v))⁻¹ *
          (Real.sqrt (G.mass v) *
            Matrix.mulVec G.transition (G.eigenfunction j) v) := by
              field_simp [hsv]
    _ = (Real.sqrt (G.mass v))⁻¹ *
        ((1 - G.eigenvalue j / G.uniformizationRate) *
          G.eigenvector j v) := by rw [hs_v]
    _ = (1 - G.eigenvalue j / G.uniformizationRate) *
        (G.eigenvector j v * (Real.sqrt (G.mass v))⁻¹) := by ring

theorem laplacianApply_eigenfunction (j : V) (v : V) :
    G.laplacianApply (G.eigenfunction j) v =
      G.eigenvalue j * G.eigenfunction j v := by
  have ht := congrFun (G.transition_mulVec_eigenfunction j) v
  rw [G.transition_mulVec_eq] at ht
  simp only [Pi.smul_apply, smul_eq_mul] at ht
  have hΛ : G.uniformizationRate ≠ 0 := G.uniformizationRate_pos.ne'
  field_simp [hΛ] at ht
  linarith

/-- Every strictly positive Laplacian eigenmode has weighted mean zero. -/
theorem eigenfunction_mean_zero {j : V} (hj : 0 < G.eigenvalue j) :
    ∑ v, G.mass v * G.eigenfunction j v = 0 := by
  have hsum : ∑ v, G.mass v * G.laplacianApply (G.eigenfunction j) v = 0 := by
    unfold laplacianApply
    have hμ (v : V) : G.mass v ≠ 0 := (G.mass_pos v).ne'
    simp_rw [mul_div_cancel₀ _ (hμ _)]
    rw [show (∑ v, ∑ u, G.conductance v u *
        (G.eigenfunction j v - G.eigenfunction j u)) = 0 by
      rw [Finset.sum_comm]
      have hswap : (∑ u, ∑ v, G.conductance v u * G.eigenfunction j v) =
          ∑ u, ∑ v, G.conductance v u * G.eigenfunction j u := by
        calc
          (∑ u, ∑ v, G.conductance v u * G.eigenfunction j v) =
              ∑ v, ∑ u, G.conductance v u * G.eigenfunction j v := Finset.sum_comm
          _ = ∑ v, ∑ u, G.conductance u v * G.eigenfunction j v := by
                apply Finset.sum_congr rfl
                intro v _
                apply Finset.sum_congr rfl
                intro u _
                rw [G.conductance_symm]
          _ = ∑ u, ∑ v, G.conductance v u * G.eigenfunction j u := by
                apply Finset.sum_congr rfl
                intro u _
                apply Finset.sum_congr rfl
                intro v _
                ring
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [hswap]
      ring]
  simp_rw [G.laplacianApply_eigenfunction] at hsum
  have hfactor : (∑ v, G.mass v *
      (G.eigenvalue j * G.eigenfunction j v)) =
      G.eigenvalue j * ∑ v, G.mass v * G.eigenfunction j v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hfactor] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left hj.ne'

/-- The uniformized graph heat kernel acts on each weighted Laplacian
eigenfunction by the exact scalar `exp (-t λ)`. -/
theorem heatApply_eigenfunction (j : V) (t : ℝ) (ht : 0 ≤ t) :
    G.heatApply t (G.eigenfunction j) =
      Real.exp (-t * G.eigenvalue j) • G.eigenfunction j := by
  have hs : 0 ≤ G.uniformizationRate * t :=
    mul_nonneg G.uniformizationRate_pos.le ht
  have hexp := Matrix.exponentialEntry_smul_mulVec_eigenvector
    G.transition G.transition_rowStochastic (G.eigenfunction j)
    (1 - G.eigenvalue j / G.uniformizationRate)
    (G.uniformizationRate * t) hs
    (G.transition_mulVec_eigenfunction j)
  ext v
  have hexp_v := congrFun hexp v
  unfold heatApply heatKernel
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hexp_v ⊢
  calc
    (∑ x, Real.exp (-(G.uniformizationRate * t)) *
        Matrix.exponentialEntry ((G.uniformizationRate * t) • G.transition) v x *
          G.eigenfunction j x) =
        Real.exp (-(G.uniformizationRate * t)) *
          ∑ x, Matrix.exponentialEntry
            ((G.uniformizationRate * t) • G.transition) v x *
              G.eigenfunction j x := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _
                ring
    _ = Real.exp (-(G.uniformizationRate * t)) *
        (Real.exp (G.uniformizationRate * t *
          (1 - G.eigenvalue j / G.uniformizationRate)) *
            G.eigenfunction j v) := by
              have hexp_v' :
                  (∑ x, Matrix.exponentialEntry
                    ((G.uniformizationRate * t) • G.transition) v x *
                      G.eigenfunction j x) =
                    Real.exp (G.uniformizationRate * t *
                      (1 - G.eigenvalue j / G.uniformizationRate)) *
                        G.eigenfunction j v := hexp_v
              rw [hexp_v']
    _ = Real.exp (-t * G.eigenvalue j) * G.eigenfunction j v := by
      have harg : -(G.uniformizationRate * t) +
          G.uniformizationRate * t *
            (1 - G.eigenvalue j / G.uniformizationRate) =
          -t * G.eigenvalue j := by
        field_simp [G.uniformizationRate_pos.ne']
        ring
      calc
        Real.exp (-(G.uniformizationRate * t)) *
            (Real.exp (G.uniformizationRate * t *
              (1 - G.eigenvalue j / G.uniformizationRate)) *
                G.eigenfunction j v) =
            (Real.exp (-(G.uniformizationRate * t)) *
              Real.exp (G.uniformizationRate * t *
                (1 - G.eigenvalue j / G.uniformizationRate))) *
                  G.eigenfunction j v := by ring
        _ = Real.exp (-(G.uniformizationRate * t) +
              G.uniformizationRate * t *
                (1 - G.eigenvalue j / G.uniformizationRate)) *
                  G.eigenfunction j v := by rw [Real.exp_add]
        _ = Real.exp (-t * G.eigenvalue j) * G.eigenfunction j v := by rw [harg]

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
