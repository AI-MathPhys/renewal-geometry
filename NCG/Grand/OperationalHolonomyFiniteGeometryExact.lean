/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperationalHolonomyTreeObservability
import NCG.Grand.FiniteCommutantPoincareGap

/-!
# Finite geometry behind operational holonomy coercivity

This file discharges the finite bookkeeping inputs in the spanning-tree
observability estimate:

* weighted Cauchy--Schwarz along certified rooted tree paths gives the exact
  manuscript constant `C_T`;
* the maximum non-tree endpoint load gives the incidence inequality with the
  exact `d_T^nt`;
* the common holonomy-fixed vectors form a subspace, and finite dimensionality
  supplies the canonical orthogonal projection onto it.

The resulting assembly theorem feeds these derived quantities directly into
`operationalHolonomy_treeObservability`.
-/

open Finset
open scoped ComplexOrder MatrixOrder

namespace NCG

section TreePaths

variable {V E 𝓗 : Type*} [Fintype V] [Fintype E]
  [DecidableEq E] [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]

/-- Sum of reciprocal edge weights along all certified root paths.  This is
the manuscript's `C_T`. -/
noncomputable def treePathConstant (paths : V → Finset E) (κ : E → ℝ) : ℝ :=
  ∑ x : V, ∑ e ∈ paths x, (κ e)⁻¹

/-- Weighted Cauchy--Schwarz along finite rooted paths gives the exact tree
Poincare estimate.  `hpath` is the finite path telescope; for a genuine rooted
tree it follows by iterating the triangle inequality along the unique path. -/
theorem weightedTreePath_deviation_le
    (src tgt : E → V) (root : V) (paths : V → Finset E)
    (κ : E → ℝ) (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (f : V → 𝓗)
    (hκ : ∀ e, 0 < κ e)
    (hpath : ∀ x, ‖f x - f root‖ ≤
      ∑ e ∈ paths x, ‖f (tgt e) - U e (f (src e))‖) :
    ∑ x : V, ‖f x - f root‖ ^ 2 ≤
      treePathConstant paths κ *
        operationalConnectionEnergy src tgt κ U f := by
  let q := operationalConnectionEnergy src tgt κ U f
  have hq : 0 ≤ q := by
    unfold q operationalConnectionEnergy
    exact Finset.sum_nonneg fun e _ => mul_nonneg (hκ e).le (sq_nonneg _)
  have hpoint : ∀ x, ‖f x - f root‖ ^ 2 ≤
      (∑ e ∈ paths x, (κ e)⁻¹) * q := by
    intro x
    let r : E → ℝ := fun e => ‖f (tgt e) - U e (f (src e))‖
    have hsq : ‖f x - f root‖ ^ 2 ≤ (∑ e ∈ paths x, r e) ^ 2 := by
      have hn := norm_nonneg (f x - f root)
      have hs : 0 ≤ ∑ e ∈ paths x, r e :=
        Finset.sum_nonneg fun e _ => norm_nonneg _
      nlinarith [hpath x]
    have hcs : (∑ e ∈ paths x, r e) ^ 2 ≤
        (∑ e ∈ paths x, (κ e)⁻¹) *
          ∑ e ∈ paths x, κ e * r e ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro e _
        exact inv_nonneg.mpr (hκ e).le
      · intro e _
        exact mul_nonneg (hκ e).le (sq_nonneg _)
      · intro e _
        rw [inv_mul_eq_div]
        field_simp [(hκ e).ne']
        exact le_rfl
    have hpathEnergy : (∑ e ∈ paths x, κ e * r e ^ 2) ≤ q := by
      unfold q operationalConnectionEnergy r
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun e _ => Finset.mem_univ e)
        (fun e _ _ => mul_nonneg (hκ e).le (sq_nonneg _))
    calc
      ‖f x - f root‖ ^ 2 ≤ (∑ e ∈ paths x, r e) ^ 2 := hsq
      _ ≤ (∑ e ∈ paths x, (κ e)⁻¹) *
          ∑ e ∈ paths x, κ e * r e ^ 2 := hcs
      _ ≤ (∑ e ∈ paths x, (κ e)⁻¹) * q := by
        exact mul_le_mul_of_nonneg_left hpathEnergy
          (Finset.sum_nonneg fun e _ => inv_nonneg.mpr (hκ e).le)
  calc
    ∑ x : V, ‖f x - f root‖ ^ 2
        ≤ ∑ x : V, (∑ e ∈ paths x, (κ e)⁻¹) * q :=
          Finset.sum_le_sum fun x _ => hpoint x
    _ = treePathConstant paths κ * q := by
      unfold treePathConstant
      rw [Finset.sum_mul]
    _ = treePathConstant paths κ *
        operationalConnectionEnergy src tgt κ U f := rfl

end TreePaths

section IncidenceLoad

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

/-- Weighted endpoint load of the non-tree edges at one vertex. -/
noncomputable def nonTreeIncidenceLoad
    (src tgt : E → V) (treeEdges : Finset E) (κ : E → ℝ) (x : V) : ℝ :=
  (∑ e ∈ (Finset.univ \ treeEdges).filter (fun e => tgt e = x), κ e) +
  ∑ e ∈ (Finset.univ \ treeEdges).filter (fun e => src e = x), κ e

/-- Maximum weighted non-tree endpoint load, the manuscript's `d_T^nt`. -/
noncomputable def nonTreeWeightedDegree
    (src tgt : E → V) (treeEdges : Finset E) (κ : E → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (nonTreeIncidenceLoad src tgt treeEdges κ)

theorem nonTreeIncidenceLoad_le_degree
    (src tgt : E → V) (treeEdges : Finset E) (κ : E → ℝ) (x : V) :
    nonTreeIncidenceLoad src tgt treeEdges κ x ≤
      nonTreeWeightedDegree src tgt treeEdges κ := by
  exact Finset.le_sup' _ (Finset.mem_univ x)

theorem nonTreeWeightedDegree_nonneg
    (src tgt : E → V) (treeEdges : Finset E) (κ : E → ℝ)
    (hκ : ∀ e, 0 ≤ κ e) :
    0 ≤ nonTreeWeightedDegree src tgt treeEdges κ := by
  let x : V := Classical.arbitrary V
  calc
    0 ≤ nonTreeIncidenceLoad src tgt treeEdges κ x := by
      unfold nonTreeIncidenceLoad
      exact add_nonneg
        (Finset.sum_nonneg fun e _ => hκ e)
        (Finset.sum_nonneg fun e _ => hκ e)
    _ ≤ nonTreeWeightedDegree src tgt treeEdges κ :=
      nonTreeIncidenceLoad_le_degree src tgt treeEdges κ x

/-- Summing endpoint deviations edgewise is exactly summing the incidence
load vertexwise. -/
theorem nonTree_endpoint_sum_eq_incidence_sum
    (src tgt : E → V) (treeEdges : Finset E) (κ : E → ℝ) (a : V → ℝ) :
    ∑ e ∈ Finset.univ \ treeEdges, κ e * (a (tgt e) + a (src e)) =
      ∑ x : V, nonTreeIncidenceLoad src tgt treeEdges κ x * a x := by
  classical
  let S : Finset E := Finset.univ \ treeEdges
  have htgt : ∑ e ∈ S, κ e * a (tgt e) =
      ∑ x : V, (∑ e ∈ S.filter (fun e => tgt e = x), κ e) * a x := by
    rw [← Finset.sum_fiberwise S tgt (fun e => κ e * a (tgt e))]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]
  have hsrc : ∑ e ∈ S, κ e * a (src e) =
      ∑ x : V, (∑ e ∈ S.filter (fun e => src e = x), κ e) * a x := by
    rw [← Finset.sum_fiberwise S src (fun e => κ e * a (src e))]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]
  have hsplit : ∑ e ∈ S, κ e * (a (tgt e) + a (src e)) =
      (∑ e ∈ S, κ e * a (tgt e)) + ∑ e ∈ S, κ e * a (src e) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  change ∑ e ∈ S, κ e * (a (tgt e) + a (src e)) = _
  rw [hsplit, htgt, hsrc, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  unfold nonTreeIncidenceLoad
  change (_ * a x + _ * a x) = (_ + _) * a x
  ring

/-- The exact incidence inequality follows from the maximum endpoint load. -/
theorem nonTree_endpoint_sum_le_degree
    (src tgt : E → V) (treeEdges : Finset E) (κ : E → ℝ) (a : V → ℝ)
    (ha : ∀ x, 0 ≤ a x) :
    ∑ e ∈ Finset.univ \ treeEdges, κ e * (a (tgt e) + a (src e)) ≤
      nonTreeWeightedDegree src tgt treeEdges κ * ∑ x : V, a x := by
  rw [nonTree_endpoint_sum_eq_incidence_sum]
  calc
    ∑ x : V, nonTreeIncidenceLoad src tgt treeEdges κ x * a x
        ≤ ∑ x : V, nonTreeWeightedDegree src tgt treeEdges κ * a x := by
          exact Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_right
              (nonTreeIncidenceLoad_le_degree src tgt treeEdges κ x) (ha x)
    _ = nonTreeWeightedDegree src tgt treeEdges κ * ∑ x : V, a x := by
      rw [Finset.mul_sum]

end IncidenceLoad

section FixedProjection

variable {E 𝓗 : Type*} [Fintype E] [DecidableEq E]
  [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]

/-- The common fixed space of the finitely many fundamental holonomies. -/
def holonomyFixedSubmodule (treeEdges : Finset E)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) : Submodule ℂ 𝓗 where
  carrier := {v | IsHolonomyFixed treeEdges U v}
  zero_mem' := by
    intro e _
    exact map_zero (U e)
  add_mem' := by
    intro v w hv hw e he
    rw [map_add, hv e he, hw e he]
  smul_mem' := by
    intro c v hv e he
    rw [map_smul, hv e he]

@[simp] theorem mem_holonomyFixedSubmodule
    (treeEdges : Finset E) (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (v : 𝓗) :
    v ∈ holonomyFixedSubmodule treeEdges U ↔
      IsHolonomyFixed treeEdges U v := Iff.rfl

/-- Finite dimensionality supplies the canonical fixed component and its
orthogonal residual. -/
theorem exists_holonomyFixed_orthogonal_decomposition
    [FiniteDimensional ℂ 𝓗]
    (treeEdges : Finset E) (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (v : 𝓗) :
    ∃ p : 𝓗, IsHolonomyFixed treeEdges U p ∧
      ∀ w, IsHolonomyFixed treeEdges U w →
        @inner ℂ 𝓗 _ (v - p) w = 0 := by
  let K := holonomyFixedSubmodule treeEdges U
  refine ⟨K.starProjection v, ?_, ?_⟩
  · exact K.starProjection_apply_mem v
  · intro w hw
    exact (K.mem_orthogonal' (v - K.starProjection v)).mp
      (K.sub_starProjection_mem_orthogonal v) w hw

end FixedProjection

section ObservationGap

variable {E 𝓗 : Type*} [Fintype E] [DecidableEq E]
  [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]

/-- The weighted finite holonomy observation map
`v ↦ (sqrt κ_e (v-U_e v))_e`, extended by zero on tree edges. -/
noncomputable def holonomyObservationLinear
    (treeEdges : Finset E) (κ : E → ℝ)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) :
    𝓗 →ₗ[ℂ] PiLp 2 (fun _ : E => 𝓗) where
  toFun v := WithLp.toLp 2 (fun e =>
    if e ∈ treeEdges then 0
    else (Real.sqrt (κ e) : ℂ) • (v - U e v))
  map_add' v w := by
    ext e
    change (if e ∈ treeEdges then 0
      else (Real.sqrt (κ e) : ℂ) •
        (v + w - U e (v + w))) =
      (if e ∈ treeEdges then 0
        else (Real.sqrt (κ e) : ℂ) • (v - U e v)) +
      (if e ∈ treeEdges then 0
        else (Real.sqrt (κ e) : ℂ) • (w - U e w))
    by_cases he : e ∈ treeEdges
    · simp [he]
    · simp only [he, if_false, map_add]
      rw [show v + w - (U e v + U e w) =
        (v - U e v) + (w - U e w) by abel, smul_add]
  map_smul' c v := by
    ext e
    change (if e ∈ treeEdges then 0
      else (Real.sqrt (κ e) : ℂ) •
        (c • v - U e (c • v))) =
      c • (if e ∈ treeEdges then 0
        else (Real.sqrt (κ e) : ℂ) • (v - U e v))
    by_cases he : e ∈ treeEdges
    · simp [he]
    · simp only [he, if_false, map_smul]
      rw [← smul_sub, smul_smul, smul_smul, mul_comm]

/-- The observation-map Hilbert norm is exactly the weighted holonomy energy. -/
theorem holonomyObservationLinear_norm_sq
    (treeEdges : Finset E) (κ : E → ℝ)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (hκ : ∀ e, 0 ≤ κ e) (v : 𝓗) :
    ‖holonomyObservationLinear treeEdges κ U v‖ ^ 2 =
      holonomyObservationEnergy treeEdges κ U v := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold holonomyObservationEnergy holonomyObservationLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  rw [Finset.sdiff_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ∈ treeEdges
  · simp [he]
  · simp only [he, if_false, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hκ e)]
    simp

/-- Positive weights make the kernel of the weighted observation map exactly
the common fixed space. -/
theorem mem_ker_holonomyObservationLinear_iff
    (treeEdges : Finset E) (κ : E → ℝ)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (hκ : ∀ e, 0 < κ e) (v : 𝓗) :
    v ∈ LinearMap.ker (holonomyObservationLinear treeEdges κ U) ↔
      IsHolonomyFixed treeEdges U v := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hv e he
    have hc := congrArg
      (fun z : PiLp 2 (fun _ : E => 𝓗) => WithLp.ofLp z e) hv
    have hent : e ∉ treeEdges := by
      simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and] using he
    change (if e ∈ treeEdges then 0
      else (Real.sqrt (κ e) : ℂ) • (v - U e v)) = 0 at hc
    rw [if_neg hent] at hc
    have hsqrt : (Real.sqrt (κ e) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (hκ e)).ne'
    have hsub : v - U e v = 0 := by
      exact (smul_eq_zero.mp hc).resolve_left hsqrt
    exact (sub_eq_zero.mp hsub).symm
  · intro hv
    ext e
    by_cases he : e ∈ treeEdges
    · simp [holonomyObservationLinear, he]
    · have heS : e ∈ Finset.univ \ treeEdges := by simp [he]
      simp [holonomyObservationLinear, he, hv e heS]

theorem ker_holonomyObservationLinear
    (treeEdges : Finset E) (κ : E → ℝ)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (hκ : ∀ e, 0 < κ e) :
    LinearMap.ker (holonomyObservationLinear treeEdges κ U) =
      holonomyFixedSubmodule treeEdges U := by
  ext v
  exact mem_ker_holonomyObservationLinear_iff treeEdges κ U hκ v

/-- A finite-dimensional fibre always has a positive holonomy-observability
margin on the orthogonal complement of the common fixed space. -/
theorem exists_holonomyObservation_margin
    [FiniteDimensional ℂ 𝓗]
    (treeEdges : Finset E) (κ : E → ℝ)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (hκ : ∀ e, 0 < κ e) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v : 𝓗,
      (∀ w, IsHolonomyFixed treeEdges U w →
        @inner ℂ 𝓗 _ v w = 0) →
      lam * ‖v‖ ^ 2 ≤ holonomyObservationEnergy treeEdges κ U v := by
  let T := holonomyObservationLinear treeEdges κ U
  obtain ⟨lam, hlam, hgap⟩ := finite_dimensional_kernel_gap T
  refine ⟨lam, hlam, ?_⟩
  intro v hv
  have hvorth : v ∈ (LinearMap.ker T)ᗮ := by
    rw [ker_holonomyObservationLinear treeEdges κ U hκ]
    exact (Submodule.mem_orthogonal'
      (holonomyFixedSubmodule treeEdges U) v).2 (fun w hw => hv w hw)
  have h := hgap v hvorth
  rwa [holonomyObservationLinear_norm_sq treeEdges κ U
    (fun e => (hκ e).le) v] at h

/-- On the nontrivial fixed-space complement, the observability margin is the
actual least eigenvalue of the restricted weighted Gram matrix.  The other
branch records the geometrically degenerate case in which every fibre vector
is holonomy-fixed. -/
theorem holonomyObservation_least_eigenvalue_gap
    [FiniteDimensional ℂ 𝓗]
    (treeEdges : Finset E) (κ : E → ℝ)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (hκ : ∀ e, 0 < κ e) :
    let T := holonomyObservationLinear treeEdges κ U
    let K : Submodule ℂ 𝓗 := (LinearMap.ker T)ᗮ
    K = ⊥ ∨
      ∃ (r : ℕ) (G : Matrix (Fin r) (Fin r) ℂ)
        (hG : G.PosDef) (lam : ℝ),
        r = Module.finrank ℂ K
        ∧ 0 < lam
        ∧ (∃ i : Fin r, lam = hG.1.eigenvalues i)
        ∧ (∀ i : Fin r, lam ≤ hG.1.eigenvalues i)
        ∧ ∀ v : 𝓗,
          (∀ w, IsHolonomyFixed treeEdges U w →
            @inner ℂ 𝓗 _ v w = 0) →
          lam * ‖v‖ ^ 2 ≤ holonomyObservationEnergy treeEdges κ U v := by
  dsimp only
  let T := holonomyObservationLinear treeEdges κ U
  obtain hzero | ⟨r, G, hG, lam, hr, hlam, heig, hleast, hgap⟩ :=
    finite_dimensional_kernel_least_eigenvalue_gap T
  · exact Or.inl hzero
  · right
    refine ⟨r, G, hG, lam, hr, hlam, heig, hleast, ?_⟩
    intro v hv
    have hvorth : v ∈ (LinearMap.ker T)ᗮ := by
      rw [ker_holonomyObservationLinear treeEdges κ U hκ]
      exact (Submodule.mem_orthogonal'
        (holonomyFixedSubmodule treeEdges U) v).2
          (fun w hw => hv w hw)
    have h := hgap v hvorth
    rwa [holonomyObservationLinear_norm_sq treeEdges κ U
      (fun e => (hκ e).le) v] at h

end ObservationGap

section ExactAssembly

variable {V E 𝓗 : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]
  [FiniteDimensional ℂ 𝓗]

/-- Fully derived finite operational-holonomy coercivity.  Rooted path
telescopes, positive edge weights, and tree gauge determine `C_T`,
`d_T^nt`, the fixed-space projection, and a positive observation margin.
The conclusion is the manuscript's displayed constant. -/
theorem operationalHolonomy_finiteGeometry
    (src tgt : E → V) (treeEdges : Finset E) (root : V)
    (paths : V → Finset E) (κ : E → ℝ)
    (U : E → 𝓗 ≃ₗᵢ[ℂ] 𝓗) (f : V → 𝓗)
    (hκ : ∀ e, 0 < κ e)
    (htreeRouter : ∀ e ∈ treeEdges,
      U e = LinearIsometryEquiv.refl ℂ 𝓗)
    (hpath : ∀ x, ‖f x - f root‖ ≤
      ∑ e ∈ paths x, ‖f (tgt e) - U e (f (src e))‖) :
    ∃ σ_T : ℝ, 0 < σ_T ∧
      ∃ g : V → 𝓗,
        IsConnectionParallel src tgt U g ∧
        ∑ x : V, ‖f x - g x‖ ^ 2 ≤
          (2 * treePathConstant paths κ +
            6 * Fintype.card V *
              (1 + nonTreeWeightedDegree src tgt treeEdges κ *
                treePathConstant paths κ) / σ_T ^ 2) *
              operationalConnectionEnergy src tgt κ U f := by
  obtain ⟨lam, hlam, hmargin⟩ :=
    exists_holonomyObservation_margin treeEdges κ U hκ
  let σ_T := Real.sqrt lam
  have hσ : 0 < σ_T := Real.sqrt_pos.2 hlam
  obtain ⟨p, hpFixed, hpOrthogonal⟩ :=
    exists_holonomyFixed_orthogonal_decomposition treeEdges U (f root)
  have htree := weightedTreePath_deviation_le
    src tgt root paths κ U f hκ hpath
  have hdegree :
      ∑ e ∈ Finset.univ \ treeEdges, κ e *
          (‖f (tgt e) - f root‖ ^ 2 + ‖f (src e) - f root‖ ^ 2)
        ≤ nonTreeWeightedDegree src tgt treeEdges κ *
          ∑ x : V, ‖f x - f root‖ ^ 2 := by
    exact nonTree_endpoint_sum_le_degree src tgt treeEdges κ
      (fun x => ‖f x - f root‖ ^ 2) (fun x => sq_nonneg _)
  have hd : 0 ≤ nonTreeWeightedDegree src tgt treeEdges κ :=
    nonTreeWeightedDegree_nonneg src tgt treeEdges κ (fun e => (hκ e).le)
  have hmarginσ : ∀ v,
      (∀ w, IsHolonomyFixed treeEdges U w →
        @inner ℂ 𝓗 _ v w = 0) →
      σ_T ^ 2 * ‖v‖ ^ 2 ≤
        holonomyObservationEnergy treeEdges κ U v := by
    intro v hv
    simpa [σ_T, Real.sq_sqrt hlam.le] using hmargin v hv
  refine ⟨σ_T, hσ, ?_⟩
  exact operationalHolonomy_treeObservability
    src tgt treeEdges root κ U f
    (treePathConstant paths κ)
    (nonTreeWeightedDegree src tgt treeEdges κ)
    σ_T p (fun e => (hκ e).le) hd hσ htreeRouter htree hdegree
    hpFixed hpOrthogonal hmarginσ

end ExactAssembly

end NCG
