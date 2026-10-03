/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Graph.Multigraph
import RenewalGeometry.Spectralization.CellularModularHodgeExact
/-!
# Cycle holonomy of the edge-ratio transport on a cellular model

This file completes `cor:supp-modular-trichotomy` of `papers/predictive_spectral_geometry` on
the cellular model.  A two-dimensional cell complex is given by a finite multigraph
`G` (its one-skeleton, `NCG.Multigraph`) and integer face–edge incidences `ε : P → E → ℤ`
satisfying `∂₁∂₂ = 0` (`IsCellBoundary`).  Its real cochain complex
`C⁰ →d₀ C¹ →d₁ C²` (`d₀ φ (e) = φ(t e) - φ(s e)`, `d₁ a (p) = Σ_e ε_{p,e} a_e`) is a finite real
Hilbert complex with the counting inner products (`d₁_comp_d₀`).

A cellular affinity comes from positive directed fluxes `q_e, q_{ē}`:
`a_e = ½ log(q_e/q_{ē})`, and the edge-ratio transport is `q_e/q_{ē} = exp(2 a_e)`.

* Walk calculus: the signed sum `walkSum a w`, the transport product `walkRatio r w`, and the
  integer one-chain `walkChain w` of a walk; for a closed walk `∂(walkChain w) = 0`
  (`boundary_walkChain_closed`), and
  `walkRatio (q/q̄) w = ∏_e (q_e/q_{ē})^{z_e} = exp(2 Σ_e z_e a_e)`
  (eq:supp-modular-cycle-holonomy).
* `exists_potential_of_walkSum_closed_eq_zero`: a one-cochain whose signed sum vanishes on every
  closed walk is exact, `a = d₀ φ` (no connectedness needed).
* (M1) `F_a ≠ 0` gives a face with nontrivial face holonomy `∏_e (q_e/q_{ē})^{ε_{p,e}} ≠ 1`.
* (M2) `F_a = 0`, `h_a ≠ 0`: all face holonomies are trivial (locally flat) and some closed walk —
  an integer cycle `z` with `∂z = 0` — has positive holonomy `∏_e (q_e/q_{ē})^{z_e} ≠ 1`.
* (M3) `F_a = h_a = 0`: `a = d₀ φ` and the positive vertex gauge `g = exp(2φ)` trivialises the
  transport, `q_e/q_{ē} = g(t e)/g(s e)`; consequently every cycle holonomy is `1`.
* `cellular_modular_trichotomy` packages (M1)–(M3) with the exhaustive case split, and
  `flat_holonomy_nontrivial_iff`: on a flat affinity, nontrivial cycle holonomy occurs exactly
  when `h_a ≠ 0`.
-/

open Finset
open scoped InnerProductSpace

namespace RenewalGeometry
namespace CellularModularHodge
namespace CellularModel

open NCG NCG.Multigraph

variable {G : Multigraph}

/-! ## Walk calculus -/

/-- The signed sum `Σ ± a_e` of a one-cochain along a walk (backward traversals count
negatively). -/
def walkSum (a : G.E → ℝ) : ∀ {u v : G.V}, G.Walk u v → ℝ
  | _, _, .nil _ => 0
  | _, _, .fwd e p => a e + walkSum a p
  | _, _, .bwd e p => -a e + walkSum a p

/-- The ordered transport product `∏ r_e^{±1}` along a walk. -/
noncomputable def walkRatio (r : G.E → ℝ) : ∀ {u v : G.V}, G.Walk u v → ℝ
  | _, _, .nil _ => 1
  | _, _, .fwd e p => r e * walkRatio r p
  | _, _, .bwd e p => (r e)⁻¹ * walkRatio r p

/-- The integer one-chain `z_e = #(forward traversals of e) - #(backward traversals of e)`
carried by a walk. -/
def walkChain [DecidableEq G.E] : ∀ {u v : G.V}, G.Walk u v → G.E → ℤ
  | _, _, .nil _ => 0
  | _, _, .fwd e p => Pi.single e 1 + walkChain p
  | _, _, .bwd e p => -Pi.single e 1 + walkChain p

theorem walkSum_append (a : G.E → ℝ) {u v w : G.V} (p : G.Walk u v) (q : G.Walk v w) :
    walkSum a (p.append q) = walkSum a p + walkSum a q := by
  induction p with
  | nil v => simp [walkSum]
  | fwd e p ih => simp only [Walk.fwd_append, walkSum, ih]; ring
  | bwd e p ih => simp only [Walk.bwd_append, walkSum, ih]; ring

theorem walkSum_reverse (a : G.E → ℝ) {u v : G.V} (p : G.Walk u v) :
    walkSum a p.reverse = -walkSum a p := by
  induction p with
  | nil v => simp [walkSum, Walk.reverse]
  | fwd e p ih =>
      simp only [Walk.reverse, walkSum_append, ih, Walk.singleRev, walkSum]; ring
  | bwd e p ih =>
      simp only [Walk.reverse, walkSum_append, ih, Walk.single, walkSum]; ring

/-- The signed sum is the pairing of the cochain with the walk's integer chain. -/
theorem walkSum_eq_sum_walkChain [Fintype G.E] [DecidableEq G.E] (a : G.E → ℝ) {u v : G.V}
    (p : G.Walk u v) : walkSum a p = ∑ e, (walkChain p e : ℝ) * a e := by
  induction p with
  | nil v => simp [walkSum, walkChain]
  | fwd e p ih =>
      simp only [walkSum, walkChain, ih, Pi.add_apply, Int.cast_add, add_mul, sum_add_distrib]
      congr 1
      rw [sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
      simp
  | bwd e p ih =>
      simp only [walkSum, walkChain, ih, Pi.add_apply, Pi.neg_apply, Int.cast_add, Int.cast_neg,
        add_mul, sum_add_distrib]
      congr 1
      rw [sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
      simp

/-- The transport product of `r = exp(2a)` is `exp(2 Σ ± a_e)`. -/
theorem walkRatio_exp (a : G.E → ℝ) {u v : G.V} (p : G.Walk u v) :
    walkRatio (fun e => Real.exp (2 * a e)) p = Real.exp (2 * walkSum a p) := by
  induction p with
  | nil v => simp [walkRatio, walkSum]
  | fwd e p ih =>
      simp only [walkRatio, walkSum, ih, mul_add, Real.exp_add]
  | bwd e p ih =>
      simp only [walkRatio, walkSum, ih, mul_add, Real.exp_add, mul_neg, Real.exp_neg]

/-- The transport product is `∏_e r_e^{z_e}` for the walk's integer chain `z`. -/
theorem walkRatio_eq_prod_zpow [Fintype G.E] [DecidableEq G.E] {r : G.E → ℝ}
    (hr : ∀ e, r e ≠ 0) {u v : G.V} (p : G.Walk u v) :
    walkRatio r p = ∏ e, r e ^ walkChain p e := by
  induction p with
  | nil v => simp [walkRatio, walkChain]
  | fwd e p ih =>
      simp only [walkRatio, walkChain, ih, Pi.add_apply]
      simp_rw [zpow_add₀ (hr _), prod_mul_distrib]
      congr 1
      rw [prod_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
      simp
  | bwd e p ih =>
      simp only [walkRatio, walkChain, ih, Pi.add_apply, Pi.neg_apply]
      simp_rw [zpow_add₀ (hr _), prod_mul_distrib]
      congr 1
      rw [prod_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
      simp

/-- The boundary `∂z (v) = Σ_e z_e ([t e = v] - [s e = v])` of an integer one-chain. -/
def chainBoundary [Fintype G.E] [DecidableEq G.V] (z : G.E → ℤ) (v : G.V) : ℤ :=
  ∑ e, z e * ((if G.tgt e = v then 1 else 0) - (if G.src e = v then 1 else 0))

/-- `∂(walkChain p) = δ_v - δ_u` for a walk `u ⟶ v`. -/
theorem chainBoundary_walkChain [Fintype G.E] [DecidableEq G.E] [DecidableEq G.V] {u v : G.V}
    (p : G.Walk u v) (x : G.V) :
    chainBoundary (walkChain p) x = (if v = x then 1 else 0) - (if u = x then 1 else 0) := by
  induction p with
  | nil v => simp [chainBoundary, walkChain]
  | fwd e p ih =>
      have : chainBoundary (Pi.single e 1 + walkChain p) x =
          ((if G.tgt e = x then 1 else 0) - (if G.src e = x then 1 else 0)) +
            chainBoundary (walkChain p) x := by
        simp only [chainBoundary, Pi.add_apply, add_mul, sum_add_distrib]
        congr 1
        rw [sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
        simp
      simp only [walkChain, this, ih]
      ring
  | bwd e p ih =>
      have : chainBoundary (-Pi.single e 1 + walkChain p) x =
          -((if G.tgt e = x then 1 else 0) - (if G.src e = x then 1 else 0)) +
            chainBoundary (walkChain p) x := by
        simp only [chainBoundary, Pi.add_apply, Pi.neg_apply, add_mul, sum_add_distrib]
        congr 1
        rw [sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
        simp
      simp only [walkChain, this, ih]
      ring

/-- A closed walk carries an integer cycle: `∂(walkChain p) = 0`. -/
theorem boundary_walkChain_closed [Fintype G.E] [DecidableEq G.E] [DecidableEq G.V] {v : G.V}
    (p : G.Walk v v) : chainBoundary (walkChain p) = 0 := by
  funext x
  rw [chainBoundary_walkChain]
  simp

/-! ## Exactness from vanishing cycle sums -/

/-- Reachability by (undirected) walks, as a setoid. -/
def reachSetoid (G : Multigraph) : Setoid G.V where
  r u v := Nonempty (G.Walk u v)
  iseqv := ⟨fun v => ⟨Walk.nil v⟩, fun ⟨p⟩ => ⟨p.reverse⟩, fun ⟨p⟩ ⟨q⟩ => ⟨p.append q⟩⟩

/-- **Exactness criterion.**  If the signed sum of `a` vanishes along every closed walk, then
`a` is exact: `a_e = φ(t e) - φ(s e)` for a vertex potential `φ` (no connectedness needed:
`φ` is integrated from a chosen root in each component). -/
theorem exists_potential_of_walkSum_closed_eq_zero (a : G.E → ℝ)
    (h : ∀ (v : G.V) (p : G.Walk v v), walkSum a p = 0) :
    ∃ φ : G.V → ℝ, ∀ e, a e = φ (G.tgt e) - φ (G.src e) := by
  let S := reachSetoid G
  let root : G.V → G.V := fun v => (Quotient.mk S v).out
  have hroot : ∀ v, Nonempty (G.Walk (root v) v) := fun v => Quotient.mk_out (s := S) v
  let W : ∀ v, G.Walk (root v) v := fun v => (hroot v).some
  -- path independence, allowing propositionally equal start points
  have hind : ∀ {u u' v : G.V} (hu : u = u') (p : G.Walk u v) (q : G.Walk u' v),
      walkSum a p = walkSum a q := by
    intro u u' v hu p q
    subst hu
    have := h u (p.append q.reverse)
    rw [walkSum_append, walkSum_reverse] at this
    linarith
  refine ⟨fun v => walkSum a (W v), fun e => ?_⟩
  have hsame : root (G.src e) = root (G.tgt e) := by
    show (Quotient.mk S (G.src e)).out = (Quotient.mk S (G.tgt e)).out
    rw [Quotient.sound (s := S) ⟨Walk.single e⟩]
  have := hind hsame ((W (G.src e)).append (Walk.single e)) (W (G.tgt e))
  rw [walkSum_append] at this
  simp only [Walk.single, walkSum] at this
  linarith

/-! ## The cellular cochain complex -/

variable [Fintype G.V] [Fintype G.E] [DecidableEq G.V] [DecidableEq G.E]
variable {P : Type*} [Fintype P]

/-- The integer face–edge incidences `ε : P → E → ℤ` form a cell complex: the boundary of every
two-cell is a one-cycle, `∂₁ ∂₂ p = 0`. -/
def IsCellBoundary (G : Multigraph) [Fintype G.E] [DecidableEq G.V] (ε : P → G.E → ℤ) : Prop :=
  ∀ p, chainBoundary (ε p) = 0

variable (G) in
/-- The vertex coboundary `d₀ φ (e) = φ(t e) - φ(s e)`. -/
noncomputable def d₀ : EuclideanSpace ℝ G.V →ₗ[ℝ] EuclideanSpace ℝ G.E where
  toFun φ := WithLp.toLp 2 fun e => φ (G.tgt e) - φ (G.src e)
  map_add' φ ψ := by
    ext e
    simp only [PiLp.add_apply]
    ring
  map_smul' c φ := by
    ext e
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The edge coboundary `d₁ a (p) = Σ_e ε_{p,e} a_e` (the cellular face-curvature). -/
noncomputable def d₁ (ε : P → G.E → ℤ) : EuclideanSpace ℝ G.E →ₗ[ℝ] EuclideanSpace ℝ P where
  toFun a := WithLp.toLp 2 fun p => ∑ e, (ε p e : ℝ) * a e
  map_add' a b := by
    ext p
    simp only [PiLp.add_apply, mul_add, sum_add_distrib]
  map_smul' c a := by
    ext p
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun e _ => by ring

theorem d₀_apply (φ : EuclideanSpace ℝ G.V) (e : G.E) :
    d₀ G φ e = φ (G.tgt e) - φ (G.src e) := rfl

theorem d₁_apply (ε : P → G.E → ℤ) (a : EuclideanSpace ℝ G.E) (p : P) :
    d₁ ε a p = ∑ e, (ε p e : ℝ) * a e := rfl

/-- `d₁ ∘ d₀ = 0` for a cell complex. -/
theorem d₁_comp_d₀ {ε : P → G.E → ℤ} (hε : IsCellBoundary G ε) : d₁ ε ∘ₗ d₀ G = 0 := by
  ext φ p
  simp only [LinearMap.comp_apply, d₁_apply, d₀_apply, LinearMap.zero_apply, PiLp.zero_apply]
  have h := congrFun (hε p)
  -- `Σ_e ε_{p,e} (φ(t e) - φ(s e)) = Σ_v φ_v (∂ε_p)(v) = 0`
  have hexp : ∀ e, (ε p e : ℝ) * (φ (G.tgt e) - φ (G.src e)) =
      ∑ v, φ v * ((ε p e : ℝ) * ((if G.tgt e = v then 1 else 0) -
        (if G.src e = v then 1 else 0))) := by
    intro e
    simp only [mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ,
      ite_true]
    ring
  rw [sum_congr rfl fun e _ => hexp e, sum_comm]
  refine sum_eq_zero fun v _ => ?_
  rw [← mul_sum]
  have hv := h v
  simp only [chainBoundary, Pi.zero_apply] at hv
  have hv' : ∑ e, (ε p e : ℝ) * ((if G.tgt e = v then 1 else 0) -
      (if G.src e = v then 1 else 0)) = 0 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hv
    push_cast at this
    simpa using this
  rw [hv', mul_zero]

/-! ## Cellular affinities from directed fluxes -/

/-- The cellular affinity `a_e = ½ log(q_e / q_{ē})` of positive forward/backward fluxes. -/
noncomputable def cellAffinity (qf qb : G.E → ℝ) : EuclideanSpace ℝ G.E :=
  WithLp.toLp 2 fun e => (1 / 2 : ℝ) * Real.log (qf e / qb e)

/-- The edge-ratio transport is `q_e / q_{ē} = exp(2 a_e)`. -/
theorem ratio_eq_exp_cellAffinity {qf qb : G.E → ℝ} (hf : ∀ e, 0 < qf e) (hb : ∀ e, 0 < qb e)
    (e : G.E) : qf e / qb e = Real.exp (2 * cellAffinity qf qb e) := by
  simp only [cellAffinity]
  rw [show 2 * ((1 / 2 : ℝ) * Real.log (qf e / qb e)) = Real.log (qf e / qb e) by ring,
    Real.exp_log (div_pos (hf e) (hb e))]

/-- Face holonomy `∏_e (q_e/q_{ē})^{ε_{p,e}} = exp(2 F_a(p))` (thm:supp-face-holonomy in the
cellular model). -/
theorem prod_ratio_zpow_eq_exp_curvature {qf qb : G.E → ℝ} (hf : ∀ e, 0 < qf e)
    (hb : ∀ e, 0 < qb e) (ε : P → G.E → ℤ) (p : P) :
    ∏ e, (qf e / qb e) ^ ε p e = Real.exp (2 * curvature (d₁ ε) (cellAffinity qf qb) p) := by
  simp only [curvature, d₁_apply, mul_sum, Real.exp_sum]
  refine prod_congr rfl fun e _ => ?_
  rw [ratio_eq_exp_cellAffinity hf hb e, ← Real.rpow_intCast, ← Real.exp_mul]
  congr 1
  ring

/-- Cycle holonomy (eq:supp-modular-cycle-holonomy): along a walk with integer chain `z`,
`∏ (q_e/q_{ē})^{±1} = ∏_e (q_e/q_{ē})^{z_e} = exp(2 Σ_e z_e a_e)`. -/
theorem walkRatio_ratio {qf qb : G.E → ℝ} (hf : ∀ e, 0 < qf e) (hb : ∀ e, 0 < qb e)
    {u v : G.V} (w : G.Walk u v) :
    walkRatio (fun e => qf e / qb e) w = ∏ e, (qf e / qb e) ^ walkChain w e ∧
    walkRatio (fun e => qf e / qb e) w =
      Real.exp (2 * ∑ e, (walkChain w e : ℝ) * cellAffinity qf qb e) := by
  refine ⟨walkRatio_eq_prod_zpow (fun e => (div_pos (hf e) (hb e)).ne') w, ?_⟩
  have hfun : (fun e => qf e / qb e) = fun e => Real.exp (2 * cellAffinity qf qb e) :=
    funext (ratio_eq_exp_cellAffinity hf hb)
  rw [hfun, walkRatio_exp, walkSum_eq_sum_walkChain]

/-! ## The trichotomy on the cellular model -/

variable {ε : P → G.E → ℤ}

/-- An exact cochain has zero harmonic part. -/
theorem harmonicPart_d₀ (φ : EuclideanSpace ℝ G.V) :
    harmonicPart (d₀ G) (d₁ ε) (d₀ G φ) = 0 := by
  rw [harmonicPart, Submodule.starProjection_apply_eq_zero_iff]
  intro h hh
  rw [real_inner_comm]
  exact inner_d₀_harmonic hh φ

/-- A cochain is exact iff its signed sum vanishes along every closed walk. -/
theorem exists_d₀_iff_walkSum (a : EuclideanSpace ℝ G.E) :
    (∃ φ : EuclideanSpace ℝ G.V, a = d₀ G φ) ↔
      ∀ (v : G.V) (w : G.Walk v v), walkSum (fun e => a e) w = 0 := by
  constructor
  · rintro ⟨φ, rfl⟩ v w
    -- telescoping along the walk
    have key : ∀ {x y : G.V} (p : G.Walk x y),
        walkSum (fun e => d₀ G φ e) p = φ y - φ x := by
      intro x y p
      induction p with
      | nil v => simp [walkSum]
      | fwd e p ih => rw [walkSum, ih, d₀_apply]; ring
      | bwd e p ih => rw [walkSum, ih, d₀_apply]; ring
    rw [key, sub_self]
  · intro h
    obtain ⟨φ, hφ⟩ := exists_potential_of_walkSum_closed_eq_zero _ h
    exact ⟨WithLp.toLp 2 φ, by ext e; simp [d₀_apply, hφ e]⟩

variable {qf qb : G.E → ℝ}

/-- **(M3)**: a cellular affinity with `F_a = h_a = 0` is exact, `a = d₀ φ`, and the positive
vertex gauge `g = exp(2φ)` trivialises the edge-ratio transport:
`q_e/q_{ē} = g(t e)/g(s e)`; in particular every cycle holonomy is trivial. -/
theorem trivializing_gauge_of_harmonicPart_eq_zero (hε : IsCellBoundary G ε)
    (hf : ∀ e, 0 < qf e) (hb : ∀ e, 0 < qb e)
    (hF : curvature (d₁ ε) (cellAffinity qf qb) = 0)
    (hh : harmonicPart (d₀ G) (d₁ ε) (cellAffinity qf qb) = 0) :
    ∃ φ : EuclideanSpace ℝ G.V, cellAffinity qf qb = d₀ G φ ∧
      (∀ e, qf e / qb e = Real.exp (2 * φ (G.tgt e)) / Real.exp (2 * φ (G.src e))) ∧
      ∀ (v : G.V) (w : G.Walk v v), walkRatio (fun e => qf e / qb e) w = 1 := by
  have hmem := sub_mem_range_d₀_of_harmonicPart_eq_of_curvature_eq (d₁_comp_d₀ hε)
    (a := cellAffinity qf qb) (b := 0)
    (by rw [hh, harmonicPart, map_zero]) (by rw [hF, curvature, map_zero])
  obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp hmem
  rw [sub_zero] at hφ
  refine ⟨φ, hφ.symm, fun e => ?_, fun v w => ?_⟩
  · rw [ratio_eq_exp_cellAffinity hf hb, ← hφ, d₀_apply, ← Real.exp_sub]
    congr 1
    ring
  · have hex : ∀ (v : G.V) (w : G.Walk v v),
        walkSum (fun e => cellAffinity qf qb e) w = 0 :=
      (exists_d₀_iff_walkSum _).1 ⟨φ, hφ.symm⟩
    rw [(walkRatio_ratio hf hb w).2, ← walkSum_eq_sum_walkChain, hex v w, mul_zero,
      Real.exp_zero]

/-- **(M2)**: a flat cellular affinity (`F_a = 0`) with `h_a ≠ 0` has all face holonomies
trivial (local flatness) and nontrivial global positive holonomy: some closed walk, i.e. an
integer cycle `z` with `∂z = 0`, has `∏_e (q_e/q_{ē})^{z_e} ≠ 1`. -/
theorem nontrivial_cycle_holonomy_of_harmonicPart_ne_zero
    (hf : ∀ e, 0 < qf e) (hb : ∀ e, 0 < qb e)
    (hF : curvature (d₁ ε) (cellAffinity qf qb) = 0)
    (hh : harmonicPart (d₀ G) (d₁ ε) (cellAffinity qf qb) ≠ 0) :
    (∀ p : P, ∏ e, (qf e / qb e) ^ ε p e = 1) ∧
    ∃ (v : G.V) (w : G.Walk v v),
      chainBoundary (walkChain w) = 0 ∧
      ∏ e, (qf e / qb e) ^ walkChain w e ≠ 1 ∧
      walkRatio (fun e => qf e / qb e) w ≠ 1 := by
  refine ⟨fun p => ?_, ?_⟩
  · rw [prod_ratio_zpow_eq_exp_curvature hf hb, hF]
    simp
  · -- `a` is not exact, so some closed walk has nonzero signed sum
    have hne : ¬ ∀ (v : G.V) (w : G.Walk v v),
        walkSum (fun e => cellAffinity qf qb e) w = 0 := by
      intro hall
      obtain ⟨φ, hφ⟩ := (exists_d₀_iff_walkSum _).2 hall
      exact hh (hφ ▸ harmonicPart_d₀ φ)
    push Not at hne
    obtain ⟨v, w, hw⟩ := hne
    have hR := walkRatio_ratio hf hb w
    have hexp : walkRatio (fun e => qf e / qb e) w ≠ 1 := by
      rw [hR.2, ← walkSum_eq_sum_walkChain]
      intro h1
      have := Real.exp_eq_one_iff _ |>.1 h1
      exact hw (by linarith)
    exact ⟨v, w, boundary_walkChain_closed w, hR.1 ▸ hexp, hexp⟩

/-- **(M1)**: `F_a ≠ 0` gives a two-cell with nontrivial face holonomy (local face
curvature). -/
theorem face_holonomy_ne_one_of_curvature_ne_zero (hf : ∀ e, 0 < qf e) (hb : ∀ e, 0 < qb e)
    (hF : curvature (d₁ ε) (cellAffinity qf qb) ≠ 0) :
    ∃ p : P, ∏ e, (qf e / qb e) ^ ε p e ≠ 1 := by
  by_contra hall
  push Not at hall
  apply hF
  ext p
  have h1 := hall p
  rw [prod_ratio_zpow_eq_exp_curvature hf hb, Real.exp_eq_one_iff] at h1
  simp only [PiLp.zero_apply]
  linarith

/-- On a flat cellular affinity, nontrivial cycle holonomy occurs **exactly** when the harmonic
part is nonzero. -/
theorem flat_holonomy_nontrivial_iff (hε : IsCellBoundary G ε) (hf : ∀ e, 0 < qf e)
    (hb : ∀ e, 0 < qb e) (hF : curvature (d₁ ε) (cellAffinity qf qb) = 0) :
    harmonicPart (d₀ G) (d₁ ε) (cellAffinity qf qb) ≠ 0 ↔
      ∃ (v : G.V) (w : G.Walk v v), walkRatio (fun e => qf e / qb e) w ≠ 1 := by
  constructor
  · intro hh
    obtain ⟨-, v, w, -, -, hw⟩ := nontrivial_cycle_holonomy_of_harmonicPart_ne_zero hf hb hF hh
    exact ⟨v, w, hw⟩
  · rintro ⟨v, w, hw⟩ hh
    obtain ⟨-, -, -, htriv⟩ := trivializing_gauge_of_harmonicPart_eq_zero hε hf hb hF hh
    exact hw (htriv v w)

/-- **`cor:supp-modular-trichotomy` on the cellular model.**  For a cell complex (one-skeleton a
finite multigraph, integer face incidences with `∂₁∂₂ = 0`) and a cellular affinity
`a_e = ½ log(q_e/q_{ē})` of positive directed fluxes, exactly one of the following holds, with
the stated geometric content:

* (M1) `F_a ≠ 0`, and some two-cell has nontrivial face holonomy;
* (M2) `F_a = 0`, `h_a ≠ 0`: every face holonomy is trivial, and some closed walk (integer cycle
  `z`, `∂z = 0`) has nontrivial positive holonomy `∏_e (q_e/q_{ē})^{z_e} ≠ 1`;
* (M3) `F_a = h_a = 0`: `a = d₀ φ` and the positive vertex gauge `exp(2φ)` trivialises the
  transport, so all cycle holonomies are trivial. -/
theorem cellular_modular_trichotomy (hε : IsCellBoundary G ε) (hf : ∀ e, 0 < qf e)
    (hb : ∀ e, 0 < qb e) :
    (curvature (d₁ ε) (cellAffinity qf qb) ≠ 0 ∧ ∃ p : P, ∏ e, (qf e / qb e) ^ ε p e ≠ 1) ∨
    (curvature (d₁ ε) (cellAffinity qf qb) = 0 ∧
      harmonicPart (d₀ G) (d₁ ε) (cellAffinity qf qb) ≠ 0 ∧
      (∀ p : P, ∏ e, (qf e / qb e) ^ ε p e = 1) ∧
      ∃ (v : G.V) (w : G.Walk v v), chainBoundary (walkChain w) = 0 ∧
        ∏ e, (qf e / qb e) ^ walkChain w e ≠ 1) ∨
    (curvature (d₁ ε) (cellAffinity qf qb) = 0 ∧
      harmonicPart (d₀ G) (d₁ ε) (cellAffinity qf qb) = 0 ∧
      ∃ φ : EuclideanSpace ℝ G.V, cellAffinity qf qb = d₀ G φ ∧
        (∀ e, qf e / qb e = Real.exp (2 * φ (G.tgt e)) / Real.exp (2 * φ (G.src e))) ∧
        ∀ (v : G.V) (w : G.Walk v v), walkRatio (fun e => qf e / qb e) w = 1) := by
  by_cases hF : curvature (d₁ ε) (cellAffinity qf qb) = 0
  · by_cases hh : harmonicPart (d₀ G) (d₁ ε) (cellAffinity qf qb) = 0
    · exact Or.inr (Or.inr ⟨hF, hh, trivializing_gauge_of_harmonicPart_eq_zero hε hf hb hF hh⟩)
    · obtain ⟨hflat, v, w, hz, hprod, -⟩ :=
        nontrivial_cycle_holonomy_of_harmonicPart_ne_zero hf hb hF hh
      exact Or.inr (Or.inl ⟨hF, hh, hflat, v, w, hz, hprod⟩)
  · exact Or.inl ⟨hF, face_holonomy_ne_one_of_curvature_ne_zero hf hb hF⟩

/-! ## Non-vacuity: the circle carries the flat, nontrivial branch (M2) -/

/-- The circle: one vertex, one loop edge, no two-cells. -/
def circle : Multigraph := ⟨Unit, Unit, fun _ => (), fun _ => ()⟩

instance : Fintype circle.V := inferInstanceAs (Fintype Unit)
instance : Fintype circle.E := inferInstanceAs (Fintype Unit)
instance : DecidableEq circle.V := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq circle.E := inferInstanceAs (DecidableEq Unit)

/-- On the circle with fluxes `q = 2`, `q̄ = 1` the affinity `½ log 2` is flat with nonzero harmonic
part: branch (M2) of the trichotomy is inhabited. -/
example : harmonicPart (d₀ circle) (d₁ (fun (_ : Empty) (_ : circle.E) => (0 : ℤ)))
    (cellAffinity (G := circle) (fun _ => 2) (fun _ => 1)) ≠ 0 := by
  refine (flat_holonomy_nontrivial_iff (fun p => p.elim) (fun _ => two_pos) (fun _ => one_pos)
    (Subsingleton.elim _ _)).2 ⟨(), Walk.single (G := circle) (), ?_⟩
  simp [Walk.single, walkRatio]

end CellularModel
end CellularModularHodge
end RenewalGeometry
