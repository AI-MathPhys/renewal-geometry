/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HolonomyCoercivity

/-!
# Operational holonomy and spanning-tree observability

This file gives the full finite weighted estimate in
`thm:operational-holonomy-coercivity`.  The connection has already been put in
tree gauge: routers on `treeEdges` are the identity, while routers on
`treeEdgesᶜ` are the fundamental-cycle holonomies.  The earlier
`HolonomyCoercivity` module supplies the pathwise weighted tree estimate.

The proof below performs the missing non-tree bookkeeping, applies the
holonomy-observability margin on the orthogonal complement of the common fixed
space, constructs the resulting parallel section, and obtains exactly

`2 * C_T + 6 * |V| * (1 + d_T^nt * C_T) / σ_T^2`.
-/

open Finset

namespace NCG

section GaugeCovariance

variable {V E 𝓗 : Type*}
  [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]

/-- Endpoint gauge action on a unitary edge router. -/
def endpointGaugeRouter (src tgt : E → V) (Q : V → 𝓗 ≃ₗᵢ[ℂ] 𝓗)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (e : E) : 𝓗 ≃ₗᵢ[ℂ] 𝓗 :=
  ((Q (src e)).symm.trans (U e)).trans (Q (tgt e))

/-- Edge defects, hence their weighted energy, are invariant under endpoint
gauge transformations. -/
theorem endpointGaugeRouter_defect_norm
    (src tgt : E → V) (Q : V → 𝓗 ≃ₗᵢ[ℂ] 𝓗)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (f : V → 𝓗) (e : E) :
    ‖Q (tgt e) (f (tgt e))
        - endpointGaugeRouter src tgt Q U e (Q (src e) (f (src e)))‖
      = ‖f (tgt e) - U e (f (src e))‖ := by
  simp only [endpointGaugeRouter, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply]
  rw [← map_sub, LinearIsometryEquiv.norm_map]

end GaugeCovariance

section TreeGauge

variable {V E 𝓗 : Type*} [Fintype E] [DecidableEq E]
  [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]

/-- Weighted connection energy, with every edge in the finite carrier counted
once. -/
noncomputable def operationalConnectionEnergy
    (src tgt : E → V) (κ : E → ℝ) (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗)
    (f : V → 𝓗) : ℝ :=
  ∑ e : E, κ e * ‖f (tgt e) - U e (f (src e))‖ ^ 2

/-- The non-tree part of the energy is bounded by the full connection energy. -/
theorem nonTreeEnergy_le_operationalConnectionEnergy
    (src tgt : E → V) (treeEdges : Finset E) (κ : E → ℝ)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (f : V → 𝓗)
    (hκ : ∀ e, 0 ≤ κ e) :
    ∑ e ∈ Finset.univ \ treeEdges,
        κ e * ‖f (tgt e) - U e (f (src e))‖ ^ 2
      ≤ operationalConnectionEnergy src tgt κ U f := by
  unfold operationalConnectionEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
    (fun e _ _ => mul_nonneg (hκ e) (sq_nonneg _))

/-- Weighted non-tree observation of a root vector by the fundamental-cycle
holonomies.  Its kernel is their common fixed space. -/
noncomputable def holonomyObservationEnergy
    (treeEdges : Finset E) (κ : E → ℝ)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (v : 𝓗) : ℝ :=
  ∑ e ∈ Finset.univ \ treeEdges, κ e * ‖v - U e v‖ ^ 2

/-- A vector is in the root-fibre common fixed space `K_T`. -/
def IsHolonomyFixed (treeEdges : Finset E)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (v : 𝓗) : Prop :=
  ∀ e ∈ Finset.univ \ treeEdges, U e v = v

/-- A section is parallel for every edge router. -/
def IsConnectionParallel (src tgt : E → V)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (f : V → 𝓗) : Prop :=
  ∀ e, f (tgt e) = U e (f (src e))

/-- In tree gauge, a common fixed vector of the fundamental-cycle holonomies
gives a global parallel section. -/
theorem constantSection_parallel_in_treeGauge
    (src tgt : E → V) (treeEdges : Finset E)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (v : 𝓗)
    (htree : ∀ e ∈ treeEdges, U e = LinearIsometryEquiv.refl ℂ 𝓗)
    (hfixed : IsHolonomyFixed treeEdges U v) :
    IsConnectionParallel src tgt U (fun _ => v) := by
  intro e
  by_cases he : e ∈ treeEdges
  · rw [htree e he]
    rfl
  · have hec : e ∈ Finset.univ \ treeEdges := by simp [he]
    simpa using (hfixed e hec).symm

/-- In tree gauge, flatness is equivalent to triviality of the finitely many
fundamental-cycle holonomies. -/
theorem treeGauge_flat_iff_fundamentalHolonomies_trivial
    (treeEdges : Finset E) (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗)
    (htree : ∀ e ∈ treeEdges, U e = LinearIsometryEquiv.refl ℂ 𝓗) :
    (∀ e, U e = LinearIsometryEquiv.refl ℂ 𝓗) ↔
      (∀ e ∈ Finset.univ \ treeEdges,
        U e = LinearIsometryEquiv.refl ℂ 𝓗) := by
  constructor
  · intro h e _
    exact h e
  · intro h e
    by_cases he : e ∈ treeEdges
    · exact htree e he
    · exact h e (by simp [he])

/-- The elementary three-term inequality used to extract the root holonomy
residual from an edge defect and its two endpoint tree deviations. -/
private theorem norm_add_add_sq_le_three {x y z : 𝓗} :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have hnorm : ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    calc
      ‖x + y + z‖ ≤ ‖x + y‖ + ‖z‖ := norm_add_le _ _
      _ ≤ (‖x‖ + ‖y‖) + ‖z‖ :=
        add_le_add (norm_add_le x y) (le_refl ‖z‖)
      _ = ‖x‖ + ‖y‖ + ‖z‖ := rfl
  have hnonneg : 0 ≤ ‖x + y + z‖ := norm_nonneg _
  have hs : (‖x‖ + ‖y‖ + ‖z‖) ^ 2
      ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
      sq_nonneg (‖y‖ - ‖z‖)]
  nlinarith

/-- The two-term squared triangle inequality with its sharp universal factor
two. -/
private theorem norm_add_sq_le_two {x y : 𝓗} :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have hnonneg : 0 ≤ ‖x + y‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Exact non-tree estimate from the manuscript.  `hdegree` is the incidence
form of `d_T^nt`: it is precisely the bound obtained by summing the two endpoint
loads and using the maximal non-tree weighted degree. -/
theorem rootHolonomyEnergy_le_of_incidenceBound
    [Fintype V]
    (src tgt : E → V) (treeEdges : Finset E) (root : V)
    (κ : E → ℝ) (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (f : V → 𝓗)
    (q C_T d_T_nt : ℝ)
    (hκ : ∀ e, 0 ≤ κ e)
    (hedge : ∑ e ∈ Finset.univ \ treeEdges,
        κ e * ‖f (tgt e) - U e (f (src e))‖ ^ 2 ≤ q)
    (htree : ∑ x : V, ‖f x - f root‖ ^ 2 ≤ C_T * q)
    (hdegree : ∑ e ∈ Finset.univ \ treeEdges, κ e *
        (‖f (tgt e) - f root‖ ^ 2 + ‖f (src e) - f root‖ ^ 2)
        ≤ d_T_nt * ∑ x : V, ‖f x - f root‖ ^ 2)
    (hd : 0 ≤ d_T_nt) :
    holonomyObservationEnergy treeEdges κ U (f root)
      ≤ 3 * (1 + d_T_nt * C_T) * q := by
  let a : V → 𝓗 := fun x => f x - f root
  have hpoint : ∀ e, ‖f root - U e (f root)‖ ^ 2 ≤
      3 * (‖f (tgt e) - U e (f (src e))‖ ^ 2
        + ‖a (tgt e)‖ ^ 2 + ‖a (src e)‖ ^ 2) := by
    intro e
    have hid : f root - U e (f root) =
        (f (tgt e) - U e (f (src e))) + (-a (tgt e)) + U e (a (src e)) := by
      dsimp [a]
      rw [map_sub]
      abel
    rw [hid]
    simpa only [norm_neg, LinearIsometryEquiv.norm_map] using
      (norm_add_add_sq_le_three
        (x := f (tgt e) - U e (f (src e)))
        (y := -a (tgt e)) (z := U e (a (src e))))
  have hsum : holonomyObservationEnergy treeEdges κ U (f root) ≤
      3 * (∑ e ∈ Finset.univ \ treeEdges,
          κ e * ‖f (tgt e) - U e (f (src e))‖ ^ 2
        + ∑ e ∈ Finset.univ \ treeEdges, κ e *
          (‖f (tgt e) - f root‖ ^ 2 + ‖f (src e) - f root‖ ^ 2)) := by
    unfold holonomyObservationEnergy
    calc
      ∑ e ∈ Finset.univ \ treeEdges, κ e * ‖f root - U e (f root)‖ ^ 2
          ≤ ∑ e ∈ Finset.univ \ treeEdges, κ e *
              (3 * (‖f (tgt e) - U e (f (src e))‖ ^ 2
                + ‖a (tgt e)‖ ^ 2 + ‖a (src e)‖ ^ 2)) := by
            exact Finset.sum_le_sum fun e _ =>
              mul_le_mul_of_nonneg_left (hpoint e) (hκ e)
      _ = 3 * (∑ e ∈ Finset.univ \ treeEdges,
            κ e * ‖f (tgt e) - U e (f (src e))‖ ^ 2
          + ∑ e ∈ Finset.univ \ treeEdges, κ e *
            (‖f (tgt e) - f root‖ ^ 2 + ‖f (src e) - f root‖ ^ 2)) := by
            simp only [a]
            rw [← Finset.sum_add_distrib, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _
            ring
  have hdev : ∑ e ∈ Finset.univ \ treeEdges, κ e *
      (‖f (tgt e) - f root‖ ^ 2 + ‖f (src e) - f root‖ ^ 2)
      ≤ d_T_nt * C_T * q := by
    calc
      _ ≤ d_T_nt * ∑ x : V, ‖f x - f root‖ ^ 2 := hdegree
      _ ≤ d_T_nt * (C_T * q) := mul_le_mul_of_nonneg_left htree hd
      _ = d_T_nt * C_T * q := by ring
  calc
    holonomyObservationEnergy treeEdges κ U (f root)
        ≤ 3 * (∑ e ∈ Finset.univ \ treeEdges,
            κ e * ‖f (tgt e) - U e (f (src e))‖ ^ 2
          + ∑ e ∈ Finset.univ \ treeEdges, κ e *
            (‖f (tgt e) - f root‖ ^ 2 + ‖f (src e) - f root‖ ^ 2)) := hsum
    _ ≤ 3 * (q + d_T_nt * C_T * q) := by
      gcongr
    _ = 3 * (1 + d_T_nt * C_T) * q := by ring

/-- **Operational connection, holonomy, and tree observability.**

`p` is the orthogonal projection of the root value onto `K_T`, expressed by
`hpFixed` and `hpOrthogonal`.  `hσ` says that `σ_T²` is a lower bound for the
holonomy observation operator on `K_Tᗮ`.  The conclusion constructs the
parallel section and proves the manuscript's displayed `C_TH` estimate with
the exact constants. -/
theorem operationalHolonomy_treeObservability
    [Fintype V]
    (src tgt : E → V) (treeEdges : Finset E) (root : V)
    (κ : E → ℝ) (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (f : V → 𝓗)
    (C_T d_T_nt σ_T : ℝ) (p : 𝓗)
    (hκ : ∀ e, 0 ≤ κ e)
    (hd : 0 ≤ d_T_nt) (hσpos : 0 < σ_T)
    (htreeRouter : ∀ e ∈ treeEdges,
      U e = LinearIsometryEquiv.refl ℂ 𝓗)
    (htree : ∑ x : V, ‖f x - f root‖ ^ 2 ≤
      C_T * operationalConnectionEnergy src tgt κ U f)
    (hdegree : ∑ e ∈ Finset.univ \ treeEdges, κ e *
        (‖f (tgt e) - f root‖ ^ 2 + ‖f (src e) - f root‖ ^ 2)
        ≤ d_T_nt * ∑ x : V, ‖f x - f root‖ ^ 2)
    (hpFixed : IsHolonomyFixed treeEdges U p)
    (hpOrthogonal : ∀ v, IsHolonomyFixed treeEdges U v →
      @inner ℂ 𝓗 _ (f root - p) v = 0)
    (hmargin : ∀ v, (∀ w, IsHolonomyFixed treeEdges U w →
        @inner ℂ 𝓗 _ v w = 0) →
      σ_T ^ 2 * ‖v‖ ^ 2 ≤ holonomyObservationEnergy treeEdges κ U v) :
    ∃ g : V → 𝓗,
      IsConnectionParallel src tgt U g ∧
      ∑ x : V, ‖f x - g x‖ ^ 2 ≤
        (2 * C_T + 6 * Fintype.card V *
          (1 + d_T_nt * C_T) / σ_T ^ 2) *
            operationalConnectionEnergy src tgt κ U f := by
  let q := operationalConnectionEnergy src tgt κ U f
  have hq : 0 ≤ q := by
    unfold q operationalConnectionEnergy
    exact Finset.sum_nonneg fun e _ => mul_nonneg (hκ e) (sq_nonneg _)
  have hedge : ∑ e ∈ Finset.univ \ treeEdges,
      κ e * ‖f (tgt e) - U e (f (src e))‖ ^ 2 ≤ q := by
    exact nonTreeEnergy_le_operationalConnectionEnergy
      src tgt treeEdges κ U f hκ
  change ∃ g : V → 𝓗,
    IsConnectionParallel src tgt U g ∧
    ∑ x : V, ‖f x - g x‖ ^ 2 ≤
      (2 * C_T + 6 * Fintype.card V *
        (1 + d_T_nt * C_T) / σ_T ^ 2) * q
  change (∑ x : V, ‖f x - f root‖ ^ 2 ≤ C_T * q) at htree
  have hrootObs := rootHolonomyEnergy_le_of_incidenceBound
    src tgt treeEdges root κ U f q C_T d_T_nt
    hκ hedge htree hdegree hd
  have htranslate : holonomyObservationEnergy treeEdges κ U (f root - p) =
      holonomyObservationEnergy treeEdges κ U (f root) := by
    unfold holonomyObservationEnergy
    apply Finset.sum_congr rfl
    intro e he
    rw [map_sub, hpFixed e he]
    congr 1
    abel_nf
  have hsigma : σ_T ^ 2 * ‖f root - p‖ ^ 2 ≤
      3 * (1 + d_T_nt * C_T) * q := by
    calc
      σ_T ^ 2 * ‖f root - p‖ ^ 2
          ≤ holonomyObservationEnergy treeEdges κ U (f root - p) :=
            hmargin (f root - p) hpOrthogonal
      _ = holonomyObservationEnergy treeEdges κ U (f root) := htranslate
      _ ≤ 3 * (1 + d_T_nt * C_T) * q := hrootObs
  have hsigmaSq : 0 < σ_T ^ 2 := sq_pos_of_pos hσpos
  have hroot : ‖f root - p‖ ^ 2 ≤
      3 * (1 + d_T_nt * C_T) * q / σ_T ^ 2 := by
    apply (le_div_iff₀ hsigmaSq).2
    simpa [mul_comm] using hsigma
  refine ⟨fun _ => p,
    constantSection_parallel_in_treeGauge src tgt treeEdges U p htreeRouter hpFixed, ?_⟩
  have hpoint : ∀ x, ‖f x - p‖ ^ 2 ≤
      2 * ‖f x - f root‖ ^ 2 + 2 * ‖f root - p‖ ^ 2 := by
    intro x
    have hid : f x - p = (f x - f root) + (f root - p) := by abel
    rw [hid]
    exact norm_add_sq_le_two
  calc
    ∑ x : V, ‖f x - p‖ ^ 2
        ≤ ∑ x : V,
          (2 * ‖f x - f root‖ ^ 2 + 2 * ‖f root - p‖ ^ 2) :=
          Finset.sum_le_sum fun x _ => hpoint x
    _ = 2 * (∑ x : V, ‖f x - f root‖ ^ 2) +
        2 * Fintype.card V * ‖f root - p‖ ^ 2 := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [Finset.mul_sum]
          ac_rfl
    _ ≤ 2 * (C_T * q) + 2 * Fintype.card V *
        (3 * (1 + d_T_nt * C_T) * q / σ_T ^ 2) := by
          gcongr
    _ = (2 * C_T + 6 * Fintype.card V *
          (1 + d_T_nt * C_T) / σ_T ^ 2) * q := by ring

end TreeGauge

end NCG
