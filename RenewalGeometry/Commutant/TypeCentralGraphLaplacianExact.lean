/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.OddChoiOccurrenceExact
import RenewalGeometry.Commutant.SourceCoercivityInfluenceExact

/-!
# Type-central incidence graph Laplacian (`prop:type-central-graph-laplacian`)

Spacetime–gauge duality manuscript, `app:incidence-flavour-stability`.

Data: nonzero, mutually orthogonal orthogonal projections `P_v` (`TypeFrame`), typed
incidences `Y_e = P_{t(e)} Y_e P_{s(e)}`, weights `w_e = ‖Y_e‖²_HS` (`edgeWeight`),
`h_v = ‖P_v‖²_HS = Tr P_v` (`typeRank`, the rank of `P_v`), the oriented incidence matrix
`B` (`incidence`, `(Bz)_e = z_{t(e)} − z_{s(e)}`) and

`L_cen = H^{-1/2} Bᴴ diag(2 w_e) B H^{-1/2}` (`centralLaplacian`).

* `type_central_graph_energy` — `∑_e (‖[X_z,Y_e]‖² + ‖[X_z,Y_eᴴ]‖²) = 2 ∑_e w_e |z_t − z_s|²`
  (`eq:type-central-graph-energy`), and `rayleigh_centralLaplacian_halfH` — this energy is the
  quadratic form of `L_cen` at `H^{1/2} z`;
* `centralLaplacian_ker_iff` — `Ker L_cen = H^{1/2} span{1_C}` over the connected components
  of the positive-weight graph `posGraph` (`eq:type-central-graph-kernel`);
* `centralLaplacian_ker_iff_centre` — `H^{1/2} z ∈ Ker L_cen` iff `X_z` lies in the
  block-scalar centre `span{P_C}`;
* `hsProjection_weighted_average` — the HS projection of `X_z` onto `span{P_C}` replaces the
  coefficients by the weighted component averages `z̄_C = ∑_{v∈C} h_v z_v / ∑_{v∈C} h_v`;
* `type_central_rigidity_gap` — with `λ₁ = posFloor` the least positive eigenvalue of
  `L_cen`, `E(z) ≥ λ₁ ‖X_z − Π X_z‖²_HS` for all `z`, with equality attained at a
  non-central `X_z` whenever `L_cen` has a positive eigenvalue: `λ₁` is the exact
  type-central rigidity gap.

Rendering disclosed: the type projections are assumed nonzero (so `h_v > 0` and
`H^{-1/2}` exists), `h_v` is encoded as `‖P_v‖²_HS = Tr P_v` (the rank of an orthogonal
projection); the projections need not sum to the identity.
-/

open Matrix
open scoped ComplexOrder

namespace RenewalGeometry
namespace TypeCentralGraphLaplacian

open OddChoiOccurrence GeometricThresholdBank SourceCoercivityInfluence

variable {N V E : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Nonzero mutually orthogonal orthogonal type projections. -/
structure TypeFrame (P : V → Matrix N N ℂ) : Prop where
  idem : ∀ v, P v * P v = P v
  herm : ∀ v, (P v)ᴴ = P v
  orth : ∀ v w, v ≠ w → P v * P w = 0
  ne_zero : ∀ v, P v ≠ 0

/-- The type-central operator `X_z = ∑_v z_v P_v`. -/
noncomputable def typeCentral (P : V → Matrix N N ℂ) (z : V → ℂ) : Matrix N N ℂ :=
  ∑ v, z v • P v

/-- `h_v = ‖P_v‖²_HS = Tr P_v`. -/
noncomputable def typeRank (P : V → Matrix N N ℂ) (v : V) : ℝ := hsSq (P v)

/-- `w_e = ‖Y_e‖²_HS`. -/
noncomputable def edgeWeight (Y : E → Matrix N N ℂ) (e : E) : ℝ := hsSq (Y e)

/-- The oriented incidence matrix, `(B z)_e = z_{t(e)} − z_{s(e)}`. -/
def incidence (src tgt : E → V) : Matrix E V ℂ :=
  Matrix.of fun e v => (if v = tgt e then 1 else 0) - (if v = src e then 1 else 0)

/-- `H^{-1/2}`. -/
noncomputable def invSqrtH (P : V → Matrix N N ℂ) : Matrix V V ℂ :=
  diagonal fun v => (((Real.sqrt (typeRank P v))⁻¹ : ℝ) : ℂ)

/-- `H^{1/2} z`. -/
noncomputable def halfH (P : V → Matrix N N ℂ) (z : V → ℂ) : V → ℂ :=
  fun v => (Real.sqrt (typeRank P v) : ℂ) * z v

/-- `L_cen = H^{-1/2} Bᴴ diag(2 w_e) B H^{-1/2}`. -/
noncomputable def centralLaplacian (P : V → Matrix N N ℂ) (Y : E → Matrix N N ℂ)
    (src tgt : E → V) : Matrix V V ℂ :=
  invSqrtH P * (incidence src tgt)ᴴ * diagonal (fun e => ((2 * edgeWeight Y e : ℝ) : ℂ)) *
    incidence src tgt * invSqrtH P

/-- The positive-weight incidence graph. -/
def posGraph (Y : E → Matrix N N ℂ) (src tgt : E → V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ e, 0 < edgeWeight Y e ∧ src e = u ∧ tgt e = v

/-! ## HS-norm helpers -/

omit [DecidableEq N] in
theorem hsSq_smul (c : ℂ) (A : Matrix N N ℂ) : hsSq (c • A) = ‖c‖ ^ 2 * hsSq A := by
  simp only [hsSq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

omit [DecidableEq N] in
theorem hsSq_conjTranspose (A : Matrix N N ℂ) : hsSq Aᴴ = hsSq A := by
  simp only [hsSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

/-! ## Typed incidences -/

section Typed

variable {P : V → Matrix N N ℂ}

theorem proj_mul_typed (hF : TypeFrame P) {A : Matrix N N ℂ} {a b : V}
    (hA : A = P a * A * P b) (v : V) : P v * A = if v = a then A else 0 := by
  by_cases h : v = a
  · subst h
    rw [if_pos rfl]
    conv_lhs => rw [hA]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hF.idem, ← hA]
  · rw [if_neg h, hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hF.orth v a h]
    simp

theorem typed_mul_proj (hF : TypeFrame P) {A : Matrix N N ℂ} {a b : V}
    (hA : A = P a * A * P b) (v : V) : A * P v = if v = b then A else 0 := by
  by_cases h : v = b
  · subst h
    rw [if_pos rfl]
    conv_lhs => rw [hA]
    rw [Matrix.mul_assoc, hF.idem, ← hA]
  · rw [if_neg h, hA, Matrix.mul_assoc, hF.orth b v (Ne.symm h)]
    simp

theorem typeCentral_mul_typed (hF : TypeFrame P) {A : Matrix N N ℂ} {a b : V}
    (hA : A = P a * A * P b) (z : V → ℂ) : typeCentral P z * A = z a • A := by
  simp only [typeCentral, Finset.sum_mul, Matrix.smul_mul, proj_mul_typed hF hA, smul_ite,
    smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem typed_mul_typeCentral (hF : TypeFrame P) {A : Matrix N N ℂ} {a b : V}
    (hA : A = P a * A * P b) (z : V → ℂ) : A * typeCentral P z = z b • A := by
  simp only [typeCentral, Finset.mul_sum, Matrix.mul_smul, typed_mul_proj hF hA, smul_ite,
    smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem typed_conjTranspose (hF : TypeFrame P) {A : Matrix N N ℂ} {a b : V}
    (hA : A = P a * A * P b) : Aᴴ = P b * Aᴴ * P a := by
  conv_lhs => rw [hA]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hF.herm, hF.herm, Matrix.mul_assoc]

theorem commutator_typed (hF : TypeFrame P) {A : Matrix N N ℂ} {a b : V}
    (hA : A = P a * A * P b) (z : V → ℂ) :
    typeCentral P z * A - A * typeCentral P z = (z a - z b) • A := by
  rw [typeCentral_mul_typed hF hA, typed_mul_typeCentral hF hA, sub_smul]

/-- **`eq:type-central-graph-energy`**:
`∑_e (‖[X_z,Y_e]‖² + ‖[X_z,Y_eᴴ]‖²) = 2 ∑_e w_e |z_{t(e)} − z_{s(e)}|²`. -/
theorem type_central_graph_energy (hF : TypeFrame P) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (hY : ∀ e, Y e = P (tgt e) * Y e * P (src e)) (z : V → ℂ) :
    ∑ e, (hsSq (typeCentral P z * Y e - Y e * typeCentral P z)
        + hsSq (typeCentral P z * (Y e)ᴴ - (Y e)ᴴ * typeCentral P z))
      = 2 * ∑ e, edgeWeight Y e * ‖z (tgt e) - z (src e)‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [commutator_typed hF (hY e), commutator_typed hF (typed_conjTranspose hF (hY e)),
    hsSq_smul, hsSq_smul, hsSq_conjTranspose, norm_sub_rev (z (src e)), edgeWeight]
  ring

end Typed

/-! ## The Laplacian quadratic form and its kernel -/

section Laplacian

variable {P : V → Matrix N N ℂ}

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem typeRank_pos (hF : TypeFrame P) (v : V) : 0 < typeRank P v :=
  lt_of_le_of_ne (hsSq_nonneg _) (fun h => hF.ne_zero v ((hsSq_eq_zero_iff _).mp h.symm))

omit [DecidableEq N] [DecidableEq E] in
theorem edgeWeight_nonneg (Y : E → Matrix N N ℂ) (e : E) : 0 ≤ edgeWeight Y e := hsSq_nonneg _

omit [Fintype E] [DecidableEq E] in
theorem incidence_mulVec (src tgt : E → V) (y : V → ℂ) (e : E) :
    (incidence src tgt *ᵥ y) e = y (tgt e) - y (src e) := by
  simp [incidence, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

omit [Fintype E] [DecidableEq E] in
theorem invSqrtH_isHermitian (P : V → Matrix N N ℂ) : (invSqrtH P).IsHermitian := by
  rw [invSqrtH, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext v
  simp

omit [Fintype E] [DecidableEq E] in
theorem invSqrtH_mulVec_halfH (hF : TypeFrame P) (z : V → ℂ) :
    invSqrtH P *ᵥ halfH P z = z := by
  funext v
  have hs : (Real.sqrt (typeRank P v) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (typeRank_pos hF v)).ne'
  rw [invSqrtH, Matrix.mulVec_diagonal, halfH, Complex.ofReal_inv, ← mul_assoc,
    inv_mul_cancel₀ hs, one_mul]

omit [Fintype E] [DecidableEq E] in
theorem halfH_invSqrtH (hF : TypeFrame P) (x : V → ℂ) : halfH P (invSqrtH P *ᵥ x) = x := by
  funext v
  have hs : (Real.sqrt (typeRank P v) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (typeRank_pos hF v)).ne'
  simp only [halfH, invSqrtH, Matrix.mulVec_diagonal]
  rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- The quadratic form of `L_cen`: `⟪x, L_cen x⟫ = ∑_e 2 w_e |y_{t(e)} − y_{s(e)}|²` with
`y = H^{-1/2} x`. -/
theorem centralLaplacian_quadForm (Y : E → Matrix N N ℂ) (src tgt : E → V) (x : V → ℂ) :
    star x ⬝ᵥ (centralLaplacian P Y src tgt *ᵥ x)
      = ((∑ e, 2 * edgeWeight Y e *
          ‖(invSqrtH P *ᵥ x) (tgt e) - (invSqrtH P *ᵥ x) (src e)‖ ^ 2 : ℝ) : ℂ) := by
  set y := invSqrtH P *ᵥ x with hy
  have h1 : centralLaplacian P Y src tgt *ᵥ x = invSqrtH P *ᵥ ((incidence src tgt)ᴴ *ᵥ
      (diagonal (fun e => ((2 * edgeWeight Y e : ℝ) : ℂ)) *ᵥ (incidence src tgt *ᵥ y))) := by
    simp only [centralLaplacian, hy, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h1, dotProduct_mulVec_hermitian (invSqrtH_isHermitian P), ← hy, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec, Complex.ofReal_sum]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, incidence_mulVec]
  refine Finset.sum_congr rfl fun e _ => ?_
  have : star (y (tgt e) - y (src e)) * (y (tgt e) - y (src e))
      = ((‖y (tgt e) - y (src e)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [mul_left_comm, this]
  push_cast
  ring

/-- **Energy as Rayleigh form**: the type-central energy of `z` is `⟪H^{1/2}z, L_cen H^{1/2}z⟫`. -/
theorem rayleigh_centralLaplacian_halfH (hF : TypeFrame P) (Y : E → Matrix N N ℂ)
    (src tgt : E → V) (z : V → ℂ) :
    rayleigh (centralLaplacian P Y src tgt) (halfH P z)
      = 2 * ∑ e, edgeWeight Y e * ‖z (tgt e) - z (src e)‖ ^ 2 := by
  rw [rayleigh, centralLaplacian_quadForm, Complex.ofReal_re, invSqrtH_mulVec_halfH hF,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

theorem centralLaplacian_posSemidef (Y : E → Matrix N N ℂ) (src tgt : E → V) :
    (centralLaplacian P Y src tgt).PosSemidef := by
  have hD : (diagonal (fun e => ((2 * edgeWeight Y e : ℝ) : ℂ))).PosSemidef := by
    refine Matrix.PosSemidef.diagonal ?_
    intro e
    simp only [Pi.zero_apply]
    exact_mod_cast mul_nonneg zero_le_two (edgeWeight_nonneg Y e)
  have := hD.conjTranspose_mul_mul_same (incidence src tgt * invSqrtH P)
  rw [Matrix.conjTranspose_mul, (invSqrtH_isHermitian P).eq] at this
  simpa only [centralLaplacian, Matrix.mul_assoc] using this

/-- `L_cen x = 0` iff `y = H^{-1/2}x` agrees across every positive-weight edge. -/
theorem centralLaplacian_mulVec_eq_zero_iff (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (x : V → ℂ) :
    centralLaplacian P Y src tgt *ᵥ x = 0 ↔
      ∀ e, 0 < edgeWeight Y e →
        (invSqrtH P *ᵥ x) (tgt e) = (invSqrtH P *ᵥ x) (src e) := by
  constructor
  · intro h e he
    have h0 := centralLaplacian_quadForm (P := P) Y src tgt x
    rw [h, dotProduct_zero, eq_comm, Complex.ofReal_eq_zero,
      Finset.sum_eq_zero_iff_of_nonneg (fun e _ => by
        have := edgeWeight_nonneg Y e; positivity)] at h0
    have := h0 e (Finset.mem_univ _)
    have h2 : ‖(invSqrtH P *ᵥ x) (tgt e) - (invSqrtH P *ᵥ x) (src e)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp this with h3 | h3
      · nlinarith
      · exact h3
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    rw [norm_eq_zero, sub_eq_zero] at this
    exact this
  · intro h
    have hD : diagonal (fun e => ((2 * edgeWeight Y e : ℝ) : ℂ)) *ᵥ
        (incidence src tgt *ᵥ (invSqrtH P *ᵥ x)) = 0 := by
      funext e
      rw [Matrix.mulVec_diagonal, incidence_mulVec, Pi.zero_apply]
      rcases (edgeWeight_nonneg Y e).lt_or_eq with he | he
      · rw [h e he, sub_self, mul_zero]
      · rw [← he]; simp
    simp only [centralLaplacian, ← Matrix.mulVec_mulVec, Matrix.mul_assoc] at hD ⊢
    rw [hD]
    simp

/-- Functions agreeing across positive-weight edges are exactly the functions constant on
the connected components of the positive-weight graph. -/
theorem edge_const_iff_component (Y : E → Matrix N N ℂ) (src tgt : E → V) (y : V → ℂ) :
    (∀ e, 0 < edgeWeight Y e → y (tgt e) = y (src e)) ↔
      ∃ c : (posGraph Y src tgt).ConnectedComponent → ℂ,
        ∀ v, y v = c ((posGraph Y src tgt).connectedComponentMk v) := by
  constructor
  · intro h
    have hadj : ∀ u v, (posGraph Y src tgt).Adj u v → y u = y v := by
      intro u v huv
      rw [posGraph, SimpleGraph.fromRel_adj] at huv
      rcases huv.2 with ⟨e, he, hs, ht⟩ | ⟨e, he, hs, ht⟩
      · rw [← hs, ← ht, h e he]
      · rw [← hs, ← ht, h e he]
    have hreach : ∀ u v, (posGraph Y src tgt).Reachable u v → y u = y v := by
      intro u v ⟨p⟩
      induction p with
      | nil => rfl
      | cons ha _ ih => exact (hadj _ _ ha).trans ih
    exact ⟨SimpleGraph.ConnectedComponent.lift y fun u v p _ => hreach u v p.reachable,
      fun v => by simp⟩
  · rintro ⟨c, hc⟩ e he
    rw [hc, hc]
    by_cases hst : src e = tgt e
    · rw [hst]
    · congr 1
      symm
      apply SimpleGraph.ConnectedComponent.sound
      apply SimpleGraph.Adj.reachable
      rw [posGraph, SimpleGraph.fromRel_adj]
      exact ⟨hst, Or.inl ⟨e, he, rfl, rfl⟩⟩

/-- **`eq:type-central-graph-kernel`**: `Ker L_cen = H^{1/2} span{1_{C_a}}`, i.e. `x ∈ Ker L_cen`
iff `x_v = √h_v · c(C(v))` for a function `c` of the connected component `C(v)` of `v` in the
positive-weight graph. -/
theorem centralLaplacian_ker_iff (hF : TypeFrame P) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (x : V → ℂ) :
    centralLaplacian P Y src tgt *ᵥ x = 0 ↔
      ∃ c : (posGraph Y src tgt).ConnectedComponent → ℂ,
        x = halfH P (fun v => c ((posGraph Y src tgt).connectedComponentMk v)) := by
  rw [centralLaplacian_mulVec_eq_zero_iff, edge_const_iff_component]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← halfH_invSqrtH hF x]
    congr 1
    funext v
    exact hc v
  · rintro ⟨c, rfl⟩
    exact ⟨c, fun v => by rw [invSqrtH_mulVec_halfH hF]⟩

end Laplacian

/-! ## The block-scalar centre and the Hilbert–Schmidt projection -/

section Centre

open Classical

variable {P : V → Matrix N N ℂ}

/-- The connected component of `v` in the positive-weight graph. -/
def comp (Y : E → Matrix N N ℂ) (src tgt : E → V) (v : V) :
    (posGraph Y src tgt).ConnectedComponent :=
  (posGraph Y src tgt).connectedComponentMk v

/-- The component projection `P_C = ∑_{v ∈ C} P_v`. -/
noncomputable def compProj (P : V → Matrix N N ℂ) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (C : (posGraph Y src tgt).ConnectedComponent) : Matrix N N ℂ :=
  ∑ v ∈ Finset.univ.filter (fun v => comp Y src tgt v = C), P v

/-- The component mass `∑_{v ∈ C} h_v`. -/
noncomputable def compMass (P : V → Matrix N N ℂ) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (C : (posGraph Y src tgt).ConnectedComponent) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => comp Y src tgt v = C), typeRank P v

/-- The weighted component average `z̄_C = ∑_{v∈C} h_v z_v / ∑_{v∈C} h_v`. -/
noncomputable def compAvg (P : V → Matrix N N ℂ) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (z : V → ℂ) (C : (posGraph Y src tgt).ConnectedComponent) : ℂ :=
  (∑ v ∈ Finset.univ.filter (fun v => comp Y src tgt v = C), (typeRank P v : ℂ) * z v) /
    (compMass P Y src tgt C : ℂ)

/-- The HS projection of `X_z` onto the block-scalar centre: `Π X_z = ∑_C z̄_C P_C`. -/
noncomputable def hsProj (P : V → Matrix N N ℂ) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (z : V → ℂ) : Matrix N N ℂ :=
  typeCentral P fun v => compAvg P Y src tgt z (comp Y src tgt v)

omit [DecidableEq V] in
theorem trace_proj (hF : TypeFrame P) (v : V) : (P v).trace = (typeRank P v : ℂ) := by
  rw [typeRank, ← trace_mul_conjTranspose_eq_hsSq, hF.herm, hF.idem]

theorem proj_mul_typeCentral (hF : TypeFrame P) (v : V) (y : V → ℂ) :
    P v * typeCentral P y = y v • P v := by
  rw [typeCentral, Finset.mul_sum, Finset.sum_eq_single v]
  · rw [Matrix.mul_smul, hF.idem]
  · intro u _ hu
    rw [Matrix.mul_smul, hF.orth v u (Ne.symm hu), smul_zero]
  · simp

theorem typeCentral_mul_typeCentral (hF : TypeFrame P) (y y' : V → ℂ) :
    typeCentral P y * typeCentral P y' = typeCentral P fun v => y v * y' v := by
  conv_lhs => rw [typeCentral]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.smul_mul, proj_mul_typeCentral hF, smul_smul]

omit [DecidableEq V] in
theorem typeCentral_conjTranspose (hF : TypeFrame P) (y : V → ℂ) :
    (typeCentral P y)ᴴ = typeCentral P (star y) := by
  simp only [typeCentral, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hF.herm,
    Pi.star_apply]

omit [DecidableEq V] in
theorem trace_typeCentral (hF : TypeFrame P) (y : V → ℂ) :
    (typeCentral P y).trace = ∑ v, y v * (typeRank P v : ℂ) := by
  simp only [typeCentral, Matrix.trace_sum, Matrix.trace_smul, trace_proj hF, smul_eq_mul]

omit [DecidableEq V] in
theorem typeCentral_sub (y y' : V → ℂ) :
    typeCentral P y - typeCentral P y' = typeCentral P (y - y') := by
  simp only [typeCentral, ← Finset.sum_sub_distrib, Pi.sub_apply, sub_smul]

/-- `‖X_y‖²_HS = ∑_v h_v |y_v|²`. -/
theorem hsSq_typeCentral (hF : TypeFrame P) (y : V → ℂ) :
    hsSq (typeCentral P y) = ∑ v, typeRank P v * ‖y v‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← trace_mul_conjTranspose_eq_hsSq, typeCentral_conjTranspose hF,
    typeCentral_mul_typeCentral hF, trace_typeCentral hF, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem typeCentral_injective (hF : TypeFrame P) {y y' : V → ℂ}
    (h : typeCentral P y = typeCentral P y') : y = y' := by
  funext v
  have h1 := congrArg (fun X => P v * X) h
  simp only [proj_mul_typeCentral hF] at h1
  have h2 : (y v - y' v) • P v = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 (hF.ne_zero v)

theorem compProj_sum (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (c : (posGraph Y src tgt).ConnectedComponent → ℂ) :
    ∑ C, c C • compProj P Y src tgt C = typeCentral P fun v => c (comp Y src tgt v) := by
  simp only [compProj, Finset.smul_sum, typeCentral]
  rw [← Finset.sum_fiberwise Finset.univ (comp Y src tgt) fun v => c (comp Y src tgt v) • P v]
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.mp hv).2]

theorem halfH_injective (hF : TypeFrame P) {z z' : V → ℂ} (h : halfH P z = halfH P z') :
    z = z' := by
  rw [← invSqrtH_mulVec_halfH hF z, h, invSqrtH_mulVec_halfH hF]

/-- **Centre correspondence**: `H^{1/2} z ∈ Ker L_cen` iff `X_z` lies in the block-scalar
centre `span{P_C}`. -/
theorem centralLaplacian_ker_iff_centre (hF : TypeFrame P) (Y : E → Matrix N N ℂ)
    (src tgt : E → V) (z : V → ℂ) :
    centralLaplacian P Y src tgt *ᵥ halfH P z = 0 ↔
      ∃ c : (posGraph Y src tgt).ConnectedComponent → ℂ,
        typeCentral P z = ∑ C, c C • compProj P Y src tgt C := by
  rw [centralLaplacian_ker_iff hF]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [compProj_sum, halfH_injective hF hc]
    rfl
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [compProj_sum] at hc
    rw [typeCentral_injective hF hc]
    rfl

theorem compProj_conjTranspose (hF : TypeFrame P) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (C : (posGraph Y src tgt).ConnectedComponent) :
    (compProj P Y src tgt C)ᴴ = compProj P Y src tgt C := by
  simp only [compProj, Matrix.conjTranspose_sum, hF.herm]

/-- `⟨P_C, X_y⟩_HS = ∑_{v ∈ C} h_v y_v`. -/
theorem trace_compProj_mul (hF : TypeFrame P) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (C : (posGraph Y src tgt).ConnectedComponent) (y : V → ℂ) :
    ((compProj P Y src tgt C)ᴴ * typeCentral P y).trace
      = ∑ v ∈ Finset.univ.filter (fun v => comp Y src tgt v = C), (typeRank P v : ℂ) * y v := by
  rw [compProj_conjTranspose hF, compProj, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [proj_mul_typeCentral hF, Matrix.trace_smul, trace_proj hF, smul_eq_mul, mul_comm]

omit [DecidableEq N] [DecidableEq V] in
theorem compMass_pos (hF : TypeFrame P) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (C : (posGraph Y src tgt).ConnectedComponent) : 0 < compMass P Y src tgt C := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    refine Finset.sum_pos' (fun u _ => (typeRank_pos hF u).le) ⟨v, ?_, typeRank_pos hF v⟩
    simp [comp]

/-- **Weighted component averages**: `Π X_z = ∑_C z̄_C P_C` lies in the centre, `X_z − Π X_z`
is HS-orthogonal to every `P_C`, and `Π X_z` is the unique such element of the centre. -/
theorem hsProjection_weighted_average (hF : TypeFrame P) (Y : E → Matrix N N ℂ)
    (src tgt : E → V) (z : V → ℂ) :
    hsProj P Y src tgt z = ∑ C, compAvg P Y src tgt z C • compProj P Y src tgt C ∧
    (∀ C, ((compProj P Y src tgt C)ᴴ * (typeCentral P z - hsProj P Y src tgt z)).trace = 0) ∧
    (∀ c : (posGraph Y src tgt).ConnectedComponent → ℂ,
      (∀ C, ((compProj P Y src tgt C)ᴴ *
        (typeCentral P z - ∑ C', c C' • compProj P Y src tgt C')).trace = 0) →
      c = compAvg P Y src tgt z) := by
  have key : ∀ (c : (posGraph Y src tgt).ConnectedComponent → ℂ) C,
      ((compProj P Y src tgt C)ᴴ *
        (typeCentral P z - typeCentral P fun v => c (comp Y src tgt v))).trace
        = (∑ v ∈ Finset.univ.filter (fun v => comp Y src tgt v = C), (typeRank P v : ℂ) * z v)
          - c C * (compMass P Y src tgt C : ℂ) := by
    intro c C
    rw [typeCentral_sub, trace_compProj_mul hF, compMass, Complex.ofReal_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Pi.sub_apply, (Finset.mem_filter.mp hv).2]
    ring
  have hm : ∀ C, (compMass P Y src tgt C : ℂ) ≠ 0 := fun C => by
    exact_mod_cast (compMass_pos hF Y src tgt C).ne'
  refine ⟨(compProj_sum Y src tgt _).symm, fun C => ?_, fun c hc => ?_⟩
  · rw [hsProj, key, compAvg, div_mul_cancel₀ _ (hm C), sub_self]
  · funext C
    have := hc C
    rw [compProj_sum, key, sub_eq_zero] at this
    rw [compAvg, this, mul_div_cancel_right₀ _ (hm C)]

end Centre

/-! ## The exact type-central rigidity gap -/

section Gap

open Classical

variable {P : V → Matrix N N ℂ}

omit [DecidableEq N] [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem halfH_sub (y y' : V → ℂ) : halfH P y - halfH P y' = halfH P (y - y') := by
  funext v
  simp only [halfH, Pi.sub_apply, mul_sub]

omit [DecidableEq N] [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem star_halfH_dotProduct (y y' : V → ℂ) :
    star (halfH P y) ⬝ᵥ halfH P y' = ∑ v, (typeRank P v : ℂ) * (star (y v) * y' v) := by
  simp only [dotProduct, Pi.star_apply, halfH, star_mul', Complex.star_def, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h : ((Real.sqrt (typeRank P v) : ℝ) : ℂ) * ((Real.sqrt (typeRank P v) : ℝ) : ℂ)
      = (typeRank P v : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (show 0 ≤ typeRank P v from hsSq_nonneg _)]
  rw [← h]
  ring

omit [DecidableEq N] [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem norm_halfH_sq (y : V → ℂ) (v : V) :
    ‖halfH P y v‖ ^ 2 = typeRank P v * ‖y v‖ ^ 2 := by
  rw [halfH, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (show 0 ≤ typeRank P v from hsSq_nonneg _)]

/-- The kernel component `x̄ = H^{1/2} z̄` of `x = H^{1/2} z`. -/
noncomputable def kerPart (P : V → Matrix N N ℂ) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (z : V → ℂ) : V → ℂ :=
  halfH P fun v => compAvg P Y src tgt z (comp Y src tgt v)

theorem kerPart_mem_ker (hF : TypeFrame P) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (z : V → ℂ) : centralLaplacian P Y src tgt *ᵥ kerPart P Y src tgt z = 0 :=
  (centralLaplacian_ker_iff hF Y src tgt _).mpr ⟨compAvg P Y src tgt z, rfl⟩

/-- `x − x̄` is orthogonal to `Ker L_cen`. -/
theorem sub_kerPart_orth (hF : TypeFrame P) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (z : V → ℂ) (k : V → ℂ) (hk : centralLaplacian P Y src tgt *ᵥ k = 0) :
    star k ⬝ᵥ (halfH P z - kerPart P Y src tgt z) = 0 := by
  obtain ⟨c, rfl⟩ := (centralLaplacian_ker_iff hF Y src tgt k).mp hk
  have hm : ∀ C, (compMass P Y src tgt C : ℂ) ≠ 0 := fun C => by
    exact_mod_cast (compMass_pos hF Y src tgt C).ne'
  rw [kerPart, halfH_sub, star_halfH_dotProduct,
    ← Finset.sum_fiberwise Finset.univ (comp Y src tgt)]
  refine Finset.sum_eq_zero fun C _ => ?_
  have hsum : ∑ v ∈ Finset.univ.filter (fun v => comp Y src tgt v = C),
      (typeRank P v : ℂ) * (star (c ((posGraph Y src tgt).connectedComponentMk v)) *
        ((z - fun v => compAvg P Y src tgt z (comp Y src tgt v)) v))
      = star (c C) * ((∑ v ∈ Finset.univ.filter (fun v => comp Y src tgt v = C),
          (typeRank P v : ℂ) * z v) - compAvg P Y src tgt z C * (compMass P Y src tgt C : ℂ)) := by
    rw [compMass, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hvC : comp Y src tgt v = C := (Finset.mem_filter.mp hv).2
    have hvC' : (posGraph Y src tgt).connectedComponentMk v = C := hvC
    rw [Pi.sub_apply, hvC, hvC']
    ring
  rw [hsum, compAvg, div_mul_cancel₀ _ (hm C), sub_self, mul_zero]

/-- The support projection of `L_cen` acts on `x = H^{1/2} z` as `x ↦ x − x̄`. -/
theorem supportProj_halfH (hF : TypeFrame P) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (z : V → ℂ) :
    supportProj (centralLaplacian_posSemidef (P := P) Y src tgt).1 *ᵥ halfH P z
      = halfH P z - kerPart P Y src tgt z := by
  set hL := centralLaplacian_posSemidef (P := P) Y src tgt
  set Q := supportProj hL.1
  set x := halfH P z
  set xb := kerPart P Y src tgt z
  have hQH : Q.IsHermitian := (supportProj_posSemidef hL.1).1
  have h1 : centralLaplacian P Y src tgt *ᵥ (x - Q *ᵥ x) = 0 := mulVec_sub_supportProj hL x
  have h2 : ∀ k, centralLaplacian P Y src tgt *ᵥ k = 0 → star k ⬝ᵥ (Q *ᵥ x) = 0 := by
    intro k hk
    rw [dotProduct_mulVec_hermitian hQH, supportProj_mulVec_eq_zero hL.1 hk, star_zero,
      zero_dotProduct]
  set d := (x - xb) - Q *ᵥ x with hd
  have hdker : centralLaplacian P Y src tgt *ᵥ d = 0 := by
    have : d = (x - Q *ᵥ x) - xb := by rw [hd]; abel
    rw [this, Matrix.mulVec_sub, h1, kerPart_mem_ker hF, sub_zero]
  have hdd : star d ⬝ᵥ d = 0 := by
    conv_rhs => skip
    calc star d ⬝ᵥ d = star d ⬝ᵥ (x - xb) - star d ⬝ᵥ (Q *ᵥ x) := by
          rw [hd, dotProduct_sub]
      _ = 0 := by rw [sub_kerPart_orth hF Y src tgt z d hdker, h2 d hdker, sub_zero]
  have h0 : d = 0 := dotProduct_star_self_eq_zero.mp hdd
  rw [hd, sub_eq_zero] at h0
  exact h0.symm

/-- `‖X_z − Π X_z‖²_HS = ‖x − x̄‖²`. -/
theorem hsSq_sub_hsProj (hF : TypeFrame P) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (z : V → ℂ) :
    hsSq (typeCentral P z - hsProj P Y src tgt z)
      = ∑ v, ‖(halfH P z - kerPart P Y src tgt z) v‖ ^ 2 := by
  rw [hsProj, typeCentral_sub, hsSq_typeCentral hF, kerPart, halfH_sub]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [norm_halfH_sq]

/-- **Exact type-central rigidity gap.**  With `λ₁ = posFloor` the least positive eigenvalue
of `L_cen`: for every `z`, `λ₁ ‖X_z − Π X_z‖²_HS ≤ ∑_e (‖[X_z,Y_e]‖² + ‖[X_z,Y_eᴴ]‖²)`, and,
whenever `L_cen` has a positive eigenvalue, equality holds at some `z` with
`X_z − Π X_z ≠ 0`. -/
theorem type_central_rigidity_gap (hF : TypeFrame P) (Y : E → Matrix N N ℂ) (src tgt : E → V)
    (hY : ∀ e, Y e = P (tgt e) * Y e * P (src e)) :
    (∀ z : V → ℂ,
      posFloor (centralLaplacian_posSemidef (P := P) Y src tgt).1 *
          hsSq (typeCentral P z - hsProj P Y src tgt z)
        ≤ ∑ e, (hsSq (typeCentral P z * Y e - Y e * typeCentral P z)
            + hsSq (typeCentral P z * (Y e)ᴴ - (Y e)ᴴ * typeCentral P z))) ∧
    ((∃ i, 0 < (centralLaplacian_posSemidef (P := P) Y src tgt).1.eigenvalues i) →
      ∃ z : V → ℂ, typeCentral P z - hsProj P Y src tgt z ≠ 0 ∧
        ∑ e, (hsSq (typeCentral P z * Y e - Y e * typeCentral P z)
            + hsSq (typeCentral P z * (Y e)ᴴ - (Y e)ᴴ * typeCentral P z))
          = posFloor (centralLaplacian_posSemidef (P := P) Y src tgt).1 *
            hsSq (typeCentral P z - hsProj P Y src tgt z)) := by
  set hL := centralLaplacian_posSemidef (P := P) Y src tgt
  set L := centralLaplacian P Y src tgt
  have henergy : ∀ z, ∑ e, (hsSq (typeCentral P z * Y e - Y e * typeCentral P z)
      + hsSq (typeCentral P z * (Y e)ᴴ - (Y e)ᴴ * typeCentral P z)) = rayleigh L (halfH P z) := by
    intro z
    rw [type_central_graph_energy hF Y src tgt hY, rayleigh_centralLaplacian_halfH hF]
  refine ⟨fun z => ?_, fun ⟨i, hi⟩ => ?_⟩
  · rw [henergy, hsSq_sub_hsProj hF, ← supportProj_halfH hF,
      normSq_supportProj hL.1]
    have h0 := rayleigh_nonneg (floor_posSemidef hL) (halfH P z)
    rw [rayleigh_sub, rayleigh_smul] at h0
    linarith
  · -- the least positive eigenvalue is attained
    have hne : (Finset.univ.filter fun i => 0 < hL.1.eigenvalues i).Nonempty :=
      ⟨i, by simp [hi]⟩
    have hmem := Finset.min'_mem ((Finset.univ.filter fun i => 0 < hL.1.eigenvalues i).image
      hL.1.eigenvalues) (hne.image _)
    obtain ⟨i0, hi0, hval⟩ := Finset.mem_image.mp hmem
    have hpos0 : 0 < hL.1.eigenvalues i0 := (Finset.mem_filter.mp hi0).2
    have hpf : posFloor hL.1 = hL.1.eigenvalues i0 := by
      unfold posFloor
      rw [dif_pos hne, hval]
    set lam := hL.1.eigenvalues i0
    set u : V → ℂ := ⇑(hL.1.eigenvectorBasis i0)
    have hLu : L *ᵥ u = (lam : ℂ) • u := by
      rw [hL.1.mulVec_eigenvectorBasis i0]
      funext v
      simp [Pi.smul_apply, Complex.real_smul, lam, u]
    -- `u` is orthogonal to the kernel
    have horth : ∀ k, L *ᵥ k = 0 → star k ⬝ᵥ u = 0 := by
      intro k hk
      have h1 : star k ⬝ᵥ (L *ᵥ u) = 0 := by
        rw [dotProduct_mulVec_hermitian hL.1, hk, star_zero, zero_dotProduct]
      rw [hLu, dotProduct_smul, smul_eq_mul] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h (by exact_mod_cast hpos0.ne')
      · exact h
    set z := invSqrtH P *ᵥ u
    have hxu : halfH P z = u := halfH_invSqrtH hF u
    -- the kernel part of `u` vanishes
    have hub : kerPart P Y src tgt z = 0 := by
      set ub := kerPart P Y src tgt z
      have hk := kerPart_mem_ker hF Y src tgt z
      have h1 := sub_kerPart_orth hF Y src tgt z ub hk
      rw [hxu, dotProduct_sub, horth ub hk, zero_sub, neg_eq_zero] at h1
      exact dotProduct_star_self_eq_zero.mp h1
    -- the eigenvector is normalized
    have hnorm : ∑ v, ‖u v‖ ^ 2 = 1 := by
      have he := hL.1.eigenvalues_eq i0
      have h2 : star u ⬝ᵥ (L *ᵥ u) = (lam : ℂ) * ((∑ v, ‖u v‖ ^ 2 : ℝ) : ℂ) := by
        rw [hLu, dotProduct_smul, smul_eq_mul, Complex.ofReal_sum]
        congr 1
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
      change lam = RCLike.re (star u ⬝ᵥ (L *ᵥ u)) at he
      rw [h2, RCLike.re_to_complex, ← Complex.ofReal_mul, Complex.ofReal_re] at he
      have := hpos0.ne'
      field_simp at he
      linarith
    have hhs : hsSq (typeCentral P z - hsProj P Y src tgt z) = 1 := by
      rw [hsSq_sub_hsProj hF, hxu, hub, sub_zero, hnorm]
    refine ⟨z, fun h0 => ?_, ?_⟩
    · rw [h0] at hhs
      simp [hsSq] at hhs
    · rw [henergy, hhs, hpf, hxu, rayleigh, hLu, dotProduct_smul, smul_eq_mul, mul_one]
      have h3 : star u ⬝ᵥ u = ((∑ v, ‖u v‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
      rw [h3, hnorm, Complex.ofReal_one, mul_one, Complex.ofReal_re]

end Gap

open Classical in
/-- **`prop:type-central-graph-laplacian`** (packaged): the energy identity, the energy as the
quadratic form of `L_cen` at `H^{1/2} z`, the kernel `H^{1/2} span{1_C}`, its identification
with the block-scalar centre, the weighted-average HS projection, and the exact rigidity gap
(`type_central_rigidity_gap`). -/
theorem type_central_graph_laplacian {P : V → Matrix N N ℂ} (hF : TypeFrame P)
    (Y : E → Matrix N N ℂ) (src tgt : E → V) (hY : ∀ e, Y e = P (tgt e) * Y e * P (src e)) :
    (∀ z : V → ℂ, ∑ e, (hsSq (typeCentral P z * Y e - Y e * typeCentral P z)
        + hsSq (typeCentral P z * (Y e)ᴴ - (Y e)ᴴ * typeCentral P z))
      = 2 * ∑ e, edgeWeight Y e * ‖z (tgt e) - z (src e)‖ ^ 2) ∧
    (∀ z : V → ℂ, rayleigh (centralLaplacian P Y src tgt) (halfH P z)
      = 2 * ∑ e, edgeWeight Y e * ‖z (tgt e) - z (src e)‖ ^ 2) ∧
    (∀ x : V → ℂ, centralLaplacian P Y src tgt *ᵥ x = 0 ↔
      ∃ c : (posGraph Y src tgt).ConnectedComponent → ℂ,
        x = halfH P (fun v => c ((posGraph Y src tgt).connectedComponentMk v))) ∧
    (∀ z : V → ℂ, centralLaplacian P Y src tgt *ᵥ halfH P z = 0 ↔
      ∃ c : (posGraph Y src tgt).ConnectedComponent → ℂ,
        typeCentral P z = ∑ C, c C • compProj P Y src tgt C) ∧
    (∀ z : V → ℂ, hsProj P Y src tgt z = ∑ C, compAvg P Y src tgt z C • compProj P Y src tgt C ∧
      ∀ C, ((compProj P Y src tgt C)ᴴ * (typeCentral P z - hsProj P Y src tgt z)).trace = 0) :=
  ⟨type_central_graph_energy hF Y src tgt hY, rayleigh_centralLaplacian_halfH hF Y src tgt,
    centralLaplacian_ker_iff hF Y src tgt, centralLaplacian_ker_iff_centre hF Y src tgt,
    fun z => ⟨(hsProjection_weighted_average hF Y src tgt z).1,
      (hsProjection_weighted_average hF Y src tgt z).2.1⟩⟩

end TypeCentralGraphLaplacian
end RenewalGeometry
