/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.RootParityConnectorExact

/-!
# Locality and continuum consistency of the harmonic writer
  (`prop:supp-open-locality`, `eq:main-open-writer`, `eq:main-open-differences`,
  `eq:main-open-skew-transport`, `eq:main-open-compensator`,
  `eq:main-harmonic-normal-row`; emergent-spacetime manuscript, supplement)

The local evolution law `eq:main-open-writer`
`q_t = v,  a(g) v_t = Σ_{ij} D_i⁻(c^{ij}(g) D_j⁺ q) - 𝖪_b v + 𝖦_h(q, v)`
is defined for grid functions on an arbitrary additive group `X` of sites
with step vectors `s_i` and mesh `h` (`fwd`, `bwd`, `ctr` are
`D_i⁺, D_i⁻, D_i⁰` of `eq:main-open-differences`; `skewTransport` is `𝖪_b`
of `eq:main-open-skew-transport`; `compensator` is `𝖦_h` of
`eq:main-open-compensator` with abstract coefficient derivatives `Dc, Db`;
`writerRhs` is the right-hand side of the second row and
`writerAcceleration` the acceleration `v_t`).  The periodic grid `(ℤ/N)³`
with `s_i = e_i`, `h = 1/N` and the lattice `h ℤ³ ⊂ ℝ³` with `s_i = h e_i`
are instances.

* `writerRhs_local` (locality): the acceleration at a site `x` depends only
  on the values of `q` and `v` at `x` and at the twelve coordinate-stencil
  neighbours `x ± s_i`, `x - s_i + s_j` (`i ≠ j`) (`InStencil`; the case
  `i = j` of the last family is the site itself).
* `grid_stencil_within_two_hops`: on the periodic grid every stencil
  neighbour is reached from `x` by at most two steps of the execution graph
  of `lem:supp-open-parity` (the `A₃` roots together with the connector
  `±e₁`; `IsConnectorStep`, `ReachTwo`).
* `writer_continuum_consistency`: on every smooth metric jet (`q ∈ C²`,
  `v ∈ C¹`, `C¹` coefficients `b^i, c^{ij}`, continuous first-jet source `F`,
  with `Dc^{ij}, Db^i` their Fréchet derivatives) the right-hand side of the
  second row at a point `x ∈ ℝ³`, with steps `h e_i`, converges as `h ↓ 0` to
  `Σ_{ij} c^{ij}(g) ∂_i∂_j q - 2 Σ_i b^i(g) ∂_i v + F(g, (v, ∂q))`, i.e. to
  the right-hand side of the harmonic normal row
  `eq:main-harmonic-normal-row` `a q_tt = c^{ij}∂_i∂_j q - 2 b^i ∂_i q_t + F`
  (`∂_i∂_j q = D²q(x)(e_i)(e_j)`, `∂_i v = Dv(x) e_i`).  The divergence
  contributes `(∂_i c^{ij}) ∂_j q` and the skew transport `(∂_i b^i) v`, and
  the two coefficient-differential terms of the compensator cancel them by
  the chain rule (`tendsto_flux_term`, `tendsto_skewTransport`,
  `tendsto_compensator`); the mixed second differences converge by the
  two-segment Taylor expansion `Convex.taylor_approx_two_segment`
  (`tendsto_mixed_second_difference`).

Scoped hypotheses disclosed: the consistency statement is pointwise in `x`
for the lattice writer on `ℝ³` (for `N`-periodic smooth fields sampled on the
grid it is the same formula); `q` is `C²` and `v`, `b^i`, `c^{ij}` are `C¹`
(the manuscript's analytic jets).
-/

open scoped BigOperators Topology
open Finset Filter Asymptotics

namespace RenewalGeometry.HarmonicWriter

noncomputable section

section Abstract

variable {X V : Type*} [AddCommGroup X] [AddCommGroup V] [Module ℝ V]

/-- Forward difference `D_i⁺ u (x) = (u(x + s_i) - u(x))/h`. -/
def fwd (h : ℝ) (s : Fin 3 → X) (i : Fin 3) (u : X → V) (x : X) : V :=
  h⁻¹ • (u (x + s i) - u x)

/-- Backward difference `D_i⁻ u (x) = (u(x) - u(x - s_i))/h`. -/
def bwd (h : ℝ) (s : Fin 3 → X) (i : Fin 3) (u : X → V) (x : X) : V :=
  h⁻¹ • (u x - u (x - s i))

/-- Central difference `D_i⁰ = (D_i⁺ + D_i⁻)/2`. -/
def ctr (h : ℝ) (s : Fin 3 → X) (i : Fin 3) (u : X → V) (x : X) : V :=
  (1 / 2 : ℝ) • (fwd h s i u x + bwd h s i u x)

/-- Skew transport `𝖪_b v = Σ_i (M_{b^i} D_i⁰ + D_i⁰ M_{b^i}) v` with
`g = η + q` (`eq:main-open-skew-transport`). -/
def skewTransport (b : Fin 3 → V → ℝ) (η : V) (h : ℝ) (s : Fin 3 → X) (q v : X → V)
    (x : X) : V :=
  ∑ i, (b i (η + q x) • ctr h s i v x + ctr h s i (fun y => b i (η + q y) • v y) x)

/-- First-jet compensator `𝖦_h(q, v) = F(g, Y_h) - Σ_{ij} Dc^{ij}(g)[D_i⁺q] D_j⁺q
+ Σ_i Db^i(g)[D_i⁺q] v` with `Y_h = (v, D_1⁺q, D_2⁺q, D_3⁺q)`
(`eq:main-open-compensator`). -/
def compensator (F : V → V × (Fin 3 → V) → V) (Dc : Fin 3 → Fin 3 → V → V → ℝ)
    (Db : Fin 3 → V → V → ℝ) (η : V) (h : ℝ) (s : Fin 3 → X) (q v : X → V) (x : X) : V :=
  F (η + q x) (v x, fun i => fwd h s i q x)
    - ∑ i, ∑ j, Dc i j (η + q x) (fwd h s i q x) • fwd h s j q x
    + ∑ i, Db i (η + q x) (fwd h s i q x) • v x

/-- Divergence flux `Σ_{ij} D_i⁻(c^{ij}(g) D_j⁺ q)`. -/
def divergenceFlux (c : Fin 3 → Fin 3 → V → ℝ) (η : V) (h : ℝ) (s : Fin 3 → X) (q : X → V)
    (x : X) : V :=
  ∑ i, ∑ j, bwd h s i (fun y => c i j (η + q y) • fwd h s j q y) x

/-- Right-hand side of the second row of `eq:main-open-writer`:
`Σ_{ij} D_i⁻(c^{ij}(g) D_j⁺ q) - 𝖪_b v + 𝖦_h(q, v)`. -/
def writerRhs (c : Fin 3 → Fin 3 → V → ℝ) (b : Fin 3 → V → ℝ) (F : V → V × (Fin 3 → V) → V)
    (Dc : Fin 3 → Fin 3 → V → V → ℝ) (Db : Fin 3 → V → V → ℝ) (η : V) (h : ℝ)
    (s : Fin 3 → X) (q v : X → V) (x : X) : V :=
  divergenceFlux c η h s q x - skewTransport b η h s q v x + compensator F Dc Db η h s q v x

/-- The acceleration `v_t = a(g)⁻¹ [Σ_{ij} D_i⁻(c^{ij}(g) D_j⁺ q) - 𝖪_b v + 𝖦_h(q, v)]`
of `eq:main-open-writer`. -/
def writerAcceleration (a : V → ℝ) (c : Fin 3 → Fin 3 → V → ℝ) (b : Fin 3 → V → ℝ)
    (F : V → V × (Fin 3 → V) → V) (Dc : Fin 3 → Fin 3 → V → V → ℝ) (Db : Fin 3 → V → V → ℝ)
    (η : V) (h : ℝ) (s : Fin 3 → X) (q v : X → V) (x : X) : V :=
  (a (η + q x))⁻¹ • writerRhs c b F Dc Db η h s q v x

/-- The coordinate stencil of a site: the site itself and its twelve
neighbours `x ± s_i`, `x - s_i + s_j` (`i ≠ j`; `i = j` gives `x`). -/
def InStencil (s : Fin 3 → X) (x y : X) : Prop :=
  y = x ∨ (∃ i, y = x + s i) ∨ (∃ i, y = x - s i) ∨ ∃ i j, y = x - s i + s j

/-- `prop:supp-open-locality`, locality clause: the right-hand side of the
second row at `x` depends only on the values of `q` and `v` on the stencil
of `x`. -/
theorem writerRhs_local (c : Fin 3 → Fin 3 → V → ℝ) (b : Fin 3 → V → ℝ)
    (F : V → V × (Fin 3 → V) → V) (Dc : Fin 3 → Fin 3 → V → V → ℝ) (Db : Fin 3 → V → V → ℝ)
    (η : V) (h : ℝ) (s : Fin 3 → X) (q q' v v' : X → V) (x : X)
    (hq : ∀ y, InStencil s x y → q y = q' y) (hv : ∀ y, InStencil s x y → v y = v' y) :
    writerRhs c b F Dc Db η h s q v x = writerRhs c b F Dc Db η h s q' v' x := by
  have hqx : q x = q' x := hq x (Or.inl rfl)
  have hqp : ∀ i, q (x + s i) = q' (x + s i) := fun i => hq _ (Or.inr (Or.inl ⟨i, rfl⟩))
  have hqm : ∀ i, q (x - s i) = q' (x - s i) := fun i =>
    hq _ (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))
  have hqmp : ∀ i j, q (x - s i + s j) = q' (x - s i + s j) := fun i j =>
    hq _ (Or.inr (Or.inr (Or.inr ⟨i, j, rfl⟩)))
  have hvx : v x = v' x := hv x (Or.inl rfl)
  have hvp : ∀ i, v (x + s i) = v' (x + s i) := fun i => hv _ (Or.inr (Or.inl ⟨i, rfl⟩))
  have hvm : ∀ i, v (x - s i) = v' (x - s i) := fun i =>
    hv _ (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))
  simp only [writerRhs, divergenceFlux, skewTransport, compensator, bwd, fwd, ctr, hqx, hqp,
    hqm, hqmp, hvx, hvp, hvm]

/-- The acceleration is local in the same sense. -/
theorem writerAcceleration_local (a : V → ℝ) (c : Fin 3 → Fin 3 → V → ℝ) (b : Fin 3 → V → ℝ)
    (F : V → V × (Fin 3 → V) → V) (Dc : Fin 3 → Fin 3 → V → V → ℝ) (Db : Fin 3 → V → V → ℝ)
    (η : V) (h : ℝ) (s : Fin 3 → X) (q q' v v' : X → V) (x : X)
    (hq : ∀ y, InStencil s x y → q y = q' y) (hv : ∀ y, InStencil s x y → v y = v' y) :
    writerAcceleration a c b F Dc Db η h s q v x = writerAcceleration a c b F Dc Db η h s q' v' x := by
  unfold writerAcceleration
  rw [writerRhs_local c b F Dc Db η h s q q' v v' x hq hv, hq x (Or.inl rfl)]

end Abstract

/-! ### Two hops of the execution graph on the periodic grid -/

section Grid

open RootParityConnector

/-- A step of the execution graph of `lem:supp-open-parity`: an `A₃` root or
the connector `±e₁`. -/
def IsConnectorStep (r : Fin 3 → ℤ) : Prop := IsRoot r ∨ r = ε 0 ∨ r = -ε 0

/-- Displacements reachable in at most two execution steps. -/
def ReachTwo (d : Fin 3 → ℤ) : Prop :=
  ∃ ℓ ≤ 2, ∃ p : ℕ → Fin 3 → ℤ, (∀ n < ℓ, IsConnectorStep (p n)) ∧ ∑ n ∈ range ℓ, p n = d

theorem reachTwo_zero : ReachTwo 0 := ⟨0, by norm_num, fun _ => 0, fun _ h => absurd h (by omega), by simp⟩

theorem reachTwo_of_step {r : Fin 3 → ℤ} (hr : IsConnectorStep r) : ReachTwo r :=
  ⟨1, by norm_num, fun _ => r, fun _ _ => hr, by simp⟩

theorem reachTwo_add {r s : Fin 3 → ℤ} (hr : IsConnectorStep r) (hs : IsConnectorStep s) :
    ReachTwo (r + s) := by
  refine ⟨2, le_rfl, fun n => if n = 0 then r else s, fun n hn => ?_, by simp [sum_range_succ]⟩
  interval_cases n <;> simp [hr, hs]

theorem isRoot_add {i j : Fin 3} (hij : i ≠ j) : IsRoot (ε i + ε j) := ⟨i, j, hij, Or.inl rfl⟩

theorem isRoot_neg_add {i j : Fin 3} (hij : i ≠ j) : IsRoot (-(ε i + ε j)) :=
  ⟨i, j, hij, Or.inr (Or.inl rfl)⟩

theorem isRoot_sub {i j : Fin 3} (hij : i ≠ j) : IsRoot (ε i - ε j) :=
  ⟨i, j, hij, Or.inr (Or.inr rfl)⟩

/-- `±e_i` is within two execution hops (`e_i = (e₁ + e_i) - e₁`). -/
theorem reachTwo_unit (i : Fin 3) : ReachTwo (ε i) ∧ ReachTwo (-ε i) := by
  by_cases hi : i = 0
  · subst hi
    exact ⟨reachTwo_of_step (Or.inr (Or.inl rfl)), reachTwo_of_step (Or.inr (Or.inr rfl))⟩
  · have h0i : (0 : Fin 3) ≠ i := fun h => hi h.symm
    constructor
    · have := reachTwo_add (Or.inl (isRoot_add h0i)) (Or.inr (Or.inr rfl) : IsConnectorStep (-ε 0))
      rwa [show ε 0 + ε i + -ε 0 = ε i by abel] at this
    · have := reachTwo_add (Or.inl (isRoot_neg_add h0i)) (Or.inr (Or.inl rfl) : IsConnectorStep (ε 0))
      rwa [show -(ε 0 + ε i) + ε 0 = -ε i by abel] at this

/-- `e_j - e_i` is within two execution hops (one root step, or `0`). -/
theorem reachTwo_sub (i j : Fin 3) : ReachTwo (ε j - ε i) := by
  by_cases hij : j = i
  · subst hij; rw [sub_self]; exact reachTwo_zero
  · exact reachTwo_of_step (Or.inl (isRoot_sub hij))

theorem toGrid_unit (N : ℕ) (i : Fin 3) : toGrid N (ε i) = e N i := by
  funext k
  simp only [toGrid, e, ε, Pi.single_apply]
  split_ifs <;> simp

theorem toGrid_neg (N : ℕ) (v : Fin 3 → ℤ) : toGrid N (-v) = -toGrid N v := by
  funext k; simp [toGrid]

theorem toGrid_sub (N : ℕ) (v w : Fin 3 → ℤ) : toGrid N (v - w) = toGrid N v - toGrid N w := by
  funext k; simp [toGrid]

theorem toGrid_zero (N : ℕ) : toGrid N 0 = 0 := by
  funext k; simp [toGrid]

/-- `prop:supp-open-locality`, execution-graph clause: on the periodic grid
every coordinate-stencil neighbour of `x` is `x + d` for a displacement `d`
reachable within two hops of the execution graph of `lem:supp-open-parity`. -/
theorem grid_stencil_within_two_hops (N : ℕ) (x y : Grid N) (hy : InStencil (e N) x y) :
    ∃ d : Fin 3 → ℤ, ReachTwo d ∧ y = x + toGrid N d := by
  rcases hy with h | ⟨i, h⟩ | ⟨i, h⟩ | ⟨i, j, h⟩
  · exact ⟨0, reachTwo_zero, by rw [h, toGrid_zero, add_zero]⟩
  · exact ⟨ε i, (reachTwo_unit i).1, by rw [h, toGrid_unit]⟩
  · exact ⟨-ε i, (reachTwo_unit i).2, by rw [h, toGrid_neg, toGrid_unit, sub_eq_add_neg]⟩
  · refine ⟨ε j - ε i, reachTwo_sub i j, ?_⟩
    rw [h, toGrid_sub, toGrid_unit, toGrid_unit]
    abel

end Grid

/-! ### Continuum consistency on smooth jets -/

section Continuum

/-- Sites of the continuum lattice: `ℝ³`. -/
abbrev Space := Fin 3 → ℝ

/-- Coordinate unit vector of `ℝ³`. -/
def E (i : Fin 3) : Space := Pi.single i 1

/-- Lattice step vectors `h e_i`. -/
def stepVec (h : ℝ) : Fin 3 → Space := fun i => h • E i

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Forward difference quotients at a fixed base point converge to the
directional derivative. -/
theorem tendsto_fwd_quotient {φ : Space → V} {φ' : Space →L[ℝ] V} {x : Space}
    (hφ : HasFDerivAt φ φ' x) (u : Space) :
    Tendsto (fun h : ℝ => h⁻¹ • (φ (x + h • u) - φ x)) (𝓝[>] 0) (𝓝 (φ' u)) := by
  have hline : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
    simpa using this
  have hφ0 : HasFDerivAt φ φ' ((fun t : ℝ => x + t • u) 0) := by simpa using hφ
  have hcomp : HasDerivAt (φ ∘ fun t : ℝ => x + t • u) (φ' u) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => x + t • u) (0 : ℝ) hφ0 hline
  have := hcomp.tendsto_slope_zero_right
  refine this.congr fun t => ?_
  simp [Function.comp]

/-- Backward difference quotients at a fixed base point converge to the
directional derivative. -/
theorem tendsto_bwd_quotient {φ : Space → V} {φ' : Space →L[ℝ] V} {x : Space}
    (hφ : HasFDerivAt φ φ' x) (u : Space) :
    Tendsto (fun h : ℝ => h⁻¹ • (φ x - φ (x - h • u))) (𝓝[>] 0) (𝓝 (φ' u)) := by
  have := (tendsto_fwd_quotient hφ (-u)).neg
  rw [map_neg, neg_neg] at this
  refine this.congr fun t => ?_
  rw [smul_neg, ← sub_eq_add_neg, ← smul_neg, neg_sub]

/-- Central differences converge to the directional derivative. -/
theorem tendsto_ctr {φ : Space → V} {φ' : Space →L[ℝ] V} {x : Space}
    (hφ : HasFDerivAt φ φ' x) (i : Fin 3) :
    Tendsto (fun h : ℝ => ctr h (stepVec h) i φ x) (𝓝[>] 0) (𝓝 (φ' (E i))) := by
  have h1 := tendsto_fwd_quotient hφ (E i)
  have h2 := tendsto_bwd_quotient hφ (E i)
  have := (h1.add h2).const_smul (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) • (φ' (E i) + φ' (E i)) = φ' (E i) := by
    rw [← two_smul ℝ, smul_smul]; norm_num
  rw [hval] at this
  exact this

/-- Two-segment Taylor expansion of a `C²` function on `ℝ³` (Mathlib's
`Convex.taylor_approx_two_segment` on `univ`). -/
theorem taylor_two_segment {q : Space → V} (hq : ContDiff ℝ 2 q) (x v w : Space) :
    (fun h : ℝ => q (x + h • v + h • w) - q (x + h • v) - h • fderiv ℝ q x w
        - h ^ 2 • fderiv ℝ (fderiv ℝ q) x v w - (h ^ 2 / 2) • fderiv ℝ (fderiv ℝ q) x w w)
      =o[𝓝[>] 0] fun h => h ^ 2 := by
  have hf : ∀ y ∈ interior (Set.univ : Set Space), HasFDerivAt q (fderiv ℝ q y) y :=
    fun y _ => (hq.differentiable (by norm_num) y).hasFDerivAt
  have hx : HasFDerivWithinAt (fderiv ℝ q) (fderiv ℝ (fderiv ℝ q) x)
      (interior (Set.univ : Set Space)) x := by
    rw [interior_univ]
    exact (((hq.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
      ).hasFDerivWithinAt
  exact convex_univ.taylor_approx_two_segment hf (Set.mem_univ x) hx (by simp) (by simp)

/-- On `𝓝[>] 0`, `h² = O(h)`. -/
theorem isBigO_sq_id : (fun h : ℝ => h ^ 2) =O[𝓝[>] 0] fun h => h := by
  refine IsBigO.of_bound 1 ?_
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hmem] with h hh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hh.1, abs_of_pos (pow_pos hh.1 2), one_mul,
    sq]
  nlinarith [hh.1, hh.2]

/-- First difference quotient with a moving base point `x + h v`:
`(q(x + hv + hw) - q(x + hv))/h → Dq(x) w`. -/
theorem tendsto_fwd_shifted {q : Space → V} (hq : ContDiff ℝ 2 q) (x v w : Space) :
    Tendsto (fun h : ℝ => h⁻¹ • (q (x + h • v + h • w) - q (x + h • v))) (𝓝[>] 0)
      (𝓝 (fderiv ℝ q x w)) := by
  set D := fderiv ℝ (fderiv ℝ q) x with hD
  set R : ℝ → V := fun h => q (x + h • v + h • w) - q (x + h • v) - h • fderiv ℝ q x w
    - h ^ 2 • D v w - (h ^ 2 / 2) • D w w with hR
  have hRo : R =o[𝓝[>] 0] fun h : ℝ => h := (taylor_two_segment hq x v w).trans_isBigO isBigO_sq_id
  have h1 : Tendsto (fun h : ℝ => h⁻¹ • R h) (𝓝[>] 0) (𝓝 0) := hRo.tendsto_inv_smul_nhds_zero
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h2 : Tendsto (fun h : ℝ => h • D v w) (𝓝[>] 0) (𝓝 0) := by
    have := hid.smul_const (D v w)
    simpa using this
  have h3 : Tendsto (fun h : ℝ => (h / 2) • D w w) (𝓝[>] 0) (𝓝 0) := by
    have := (hid.div_const 2).smul_const (D w w)
    simpa using this
  have hsum := ((h1.add (tendsto_const_nhds (x := fderiv ℝ q x w))).add h2).add h3
  simp only [zero_add, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := ne_of_gt hh
  have hdiff : q (x + h • v + h • w) - q (x + h • v) =
      R h + h • fderiv ℝ q x w + h ^ 2 • D v w + (h ^ 2 / 2) • D w w := by
    simp only [hR]; abel
  rw [hdiff]
  simp only [smul_add, smul_smul]
  congr 2
  · rw [inv_mul_cancel₀ hne, one_smul]
  · congr 1; field_simp
  · congr 1; field_simp

/-- Mixed second difference:
`((q(x + hw) - q(x)) - (q(x + hv + hw) - q(x + hv)))/h² → -D²q(x) v w`. -/
theorem tendsto_mixed_second_difference {q : Space → V} (hq : ContDiff ℝ 2 q) (x v w : Space) :
    Tendsto (fun h : ℝ => (h ^ 2)⁻¹ •
        ((q (x + h • w) - q x) - (q (x + h • v + h • w) - q (x + h • v)))) (𝓝[>] 0)
      (𝓝 (-(fderiv ℝ (fderiv ℝ q) x v w))) := by
  set D := fderiv ℝ (fderiv ℝ q) x with hD
  set R₀ : ℝ → V := fun h => q (x + h • (0 : Space) + h • w) - q (x + h • (0 : Space))
    - h • fderiv ℝ q x w - h ^ 2 • D 0 w - (h ^ 2 / 2) • D w w with hR₀
  set R₁ : ℝ → V := fun h => q (x + h • v + h • w) - q (x + h • v) - h • fderiv ℝ q x w
    - h ^ 2 • D v w - (h ^ 2 / 2) • D w w with hR₁
  have h0 : Tendsto (fun h : ℝ => (h ^ 2)⁻¹ • R₀ h) (𝓝[>] 0) (𝓝 0) :=
    (taylor_two_segment hq x 0 w).tendsto_inv_smul_nhds_zero
  have h1 : Tendsto (fun h : ℝ => (h ^ 2)⁻¹ • R₁ h) (𝓝[>] 0) (𝓝 0) :=
    (taylor_two_segment hq x v w).tendsto_inv_smul_nhds_zero
  have hsum := (h0.sub h1).sub (tendsto_const_nhds (x := D v w))
  simp only [sub_zero, zero_sub] at hsum
  have hdiff : ∀ h : ℝ, (q (x + h • w) - q x) - (q (x + h • v + h • w) - q (x + h • v)) =
      R₀ h - R₁ h - h ^ 2 • D v w := by
    intro h
    simp only [hR₀, hR₁, smul_zero, add_zero, map_zero, ContinuousLinearMap.zero_apply]
    abel
  clear_value R₀ R₁
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := ne_of_gt hh
  rw [hdiff h, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hne), one_smul]

/-- Limit of one divergence-flux term `D_i⁻(c^{ij}(g) D_j⁺ q)(x)`:
`c^{ij}(g) ∂_i∂_j q + (∂_i c^{ij}(g)) ∂_j q` with
`∂_i c^{ij}(g) = Dc^{ij}(g)[∂_i q]` by the chain rule. -/
theorem tendsto_flux_term {q : Space → V} (hq : ContDiff ℝ 2 q) {c : V → ℝ}
    (hc : ContDiff ℝ 1 c) (η : V) (x : Space) (i j : Fin 3) :
    Tendsto (fun h : ℝ => bwd h (stepVec h) i (fun y => c (η + q y) • fwd h (stepVec h) j q y) x)
      (𝓝[>] 0)
      (𝓝 (c (η + q x) • fderiv ℝ (fderiv ℝ q) x (E i) (E j)
        + fderiv ℝ c (η + q x) (fderiv ℝ q x (E i)) • fderiv ℝ q x (E j))) := by
  have hqd : HasFDerivAt q (fderiv ℝ q x) x := (hq.differentiable (by norm_num) x).hasFDerivAt
  have hg : HasFDerivAt (fun y => η + q y) (fderiv ℝ q x) x := hqd.const_add η
  have hcg : HasFDerivAt (fun y => c (η + q y))
      ((fderiv ℝ c (η + q x)).comp (fderiv ℝ q x)) x :=
    ((hc.differentiable (by norm_num) _).hasFDerivAt).comp x hg
  -- the second difference of `q`
  have hA : Tendsto (fun h : ℝ => h⁻¹ • (fwd h (stepVec h) j q x - fwd h (stepVec h) j q (x - h • E i)))
      (𝓝[>] 0) (𝓝 (fderiv ℝ (fderiv ℝ q) x (E i) (E j))) := by
    have := tendsto_mixed_second_difference hq x (-E i) (E j)
    rw [map_neg, ContinuousLinearMap.neg_apply, neg_neg] at this
    refine this.congr fun h => ?_
    simp only [fwd, stepVec]
    rw [← smul_sub, smul_smul, smul_neg, ← sub_eq_add_neg, ← mul_inv, ← sq]
  -- the coefficient difference
  have hB : Tendsto (fun h : ℝ => h⁻¹ • (c (η + q x) - c (η + q (x - h • E i)))) (𝓝[>] 0)
      (𝓝 (fderiv ℝ c (η + q x) (fderiv ℝ q x (E i)))) := by
    have := tendsto_bwd_quotient hcg (E i)
    simpa using this
  -- the shifted first difference of `q`
  have hC : Tendsto (fun h : ℝ => fwd h (stepVec h) j q (x - h • E i)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ q x (E j))) := by
    have := tendsto_fwd_shifted hq x (-E i) (E j)
    refine this.congr fun h => ?_
    simp only [fwd, stepVec]
    rw [smul_neg, ← sub_eq_add_neg]
  have hlim := (hA.const_smul (c (η + q x))).add (hB.smul hC)
  refine hlim.congr fun h => ?_
  simp only [bwd, stepVec, smul_eq_mul]
  module

/-- Limit of the skew transport `𝖪_b v (x)`:
`Σ_i [2 b^i(g) ∂_i v + (∂_i b^i(g)) v]` with `∂_i b^i(g) = Db^i(g)[∂_i q]`. -/
theorem tendsto_skewTransport {q v : Space → V} (hq : ContDiff ℝ 2 q) (hv : ContDiff ℝ 1 v)
    {b : Fin 3 → V → ℝ} (hb : ∀ i, ContDiff ℝ 1 (b i)) (η : V) (x : Space) :
    Tendsto (fun h : ℝ => skewTransport b η h (stepVec h) q v x) (𝓝[>] 0)
      (𝓝 (∑ i, (b i (η + q x) • fderiv ℝ v x (E i)
        + (b i (η + q x) • fderiv ℝ v x (E i)
          + fderiv ℝ (b i) (η + q x) (fderiv ℝ q x (E i)) • v x)))) := by
  unfold skewTransport
  refine tendsto_finset_sum _ fun i _ => ?_
  have hqd : HasFDerivAt q (fderiv ℝ q x) x := (hq.differentiable (by norm_num) x).hasFDerivAt
  have hvd : HasFDerivAt v (fderiv ℝ v x) x := (hv.differentiable (by norm_num) x).hasFDerivAt
  have hg : HasFDerivAt (fun y => η + q y) (fderiv ℝ q x) x := hqd.const_add η
  have hbg : HasFDerivAt (fun y => b i (η + q y))
      ((fderiv ℝ (b i) (η + q x)).comp (fderiv ℝ q x)) x :=
    (((hb i).differentiable (by norm_num) _).hasFDerivAt).comp x hg
  have hprod : HasFDerivAt (fun y => b i (η + q y) • v y)
      (b i (η + q x) • fderiv ℝ v x
        + ((fderiv ℝ (b i) (η + q x)).comp (fderiv ℝ q x)).smulRight (v x)) x :=
    hbg.smul hvd
  have h1 := (tendsto_ctr hvd i).const_smul (b i (η + q x))
  have h2 := tendsto_ctr hprod i
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply] at h2
  exact h1.add h2

/-- Limit of the compensator `𝖦_h(q, v)(x)`:
`F(g, (v, ∂q)) - Σ_{ij} Dc^{ij}(g)[∂_i q] ∂_j q + Σ_i Db^i(g)[∂_i q] v`. -/
theorem tendsto_compensator {q v : Space → V} (hq : ContDiff ℝ 2 q)
    {b : Fin 3 → V → ℝ} {c : Fin 3 → Fin 3 → V → ℝ} {F : V → V × (Fin 3 → V) → V}
    (hF : ∀ g, Continuous (F g)) (η : V) (x : Space) :
    Tendsto (fun h : ℝ => compensator F (fun i j g w => fderiv ℝ (c i j) g w)
        (fun i g w => fderiv ℝ (b i) g w) η h (stepVec h) q v x) (𝓝[>] 0)
      (𝓝 (F (η + q x) (v x, fun i => fderiv ℝ q x (E i))
        - ∑ i, ∑ j, fderiv ℝ (c i j) (η + q x) (fderiv ℝ q x (E i)) • fderiv ℝ q x (E j)
        + ∑ i, fderiv ℝ (b i) (η + q x) (fderiv ℝ q x (E i)) • v x)) := by
  unfold compensator
  have hqd : HasFDerivAt q (fderiv ℝ q x) x := (hq.differentiable (by norm_num) x).hasFDerivAt
  have hfwd : ∀ i, Tendsto (fun h : ℝ => fwd h (stepVec h) i q x) (𝓝[>] 0)
      (𝓝 (fderiv ℝ q x (E i))) := fun i => tendsto_fwd_quotient hqd (E i)
  have hF' : Tendsto (fun h : ℝ => F (η + q x) (v x, fun i => fwd h (stepVec h) i q x)) (𝓝[>] 0)
      (𝓝 (F (η + q x) (v x, fun i => fderiv ℝ q x (E i)))) :=
    ((hF (η + q x)).tendsto _).comp (tendsto_const_nhds.prodMk_nhds (tendsto_pi_nhds.mpr hfwd))
  have hc' : Tendsto (fun h : ℝ => ∑ i, ∑ j,
      fderiv ℝ (c i j) (η + q x) (fwd h (stepVec h) i q x) • fwd h (stepVec h) j q x) (𝓝[>] 0)
      (𝓝 (∑ i, ∑ j, fderiv ℝ (c i j) (η + q x) (fderiv ℝ q x (E i)) • fderiv ℝ q x (E j))) := by
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
    exact (((fderiv ℝ (c i j) (η + q x)).continuous.tendsto _).comp (hfwd i)).smul (hfwd j)
  have hb' : Tendsto (fun h : ℝ => ∑ i,
      fderiv ℝ (b i) (η + q x) (fwd h (stepVec h) i q x) • v x) (𝓝[>] 0)
      (𝓝 (∑ i, fderiv ℝ (b i) (η + q x) (fderiv ℝ q x (E i)) • v x)) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    exact (((fderiv ℝ (b i) (η + q x)).continuous.tendsto _).comp (hfwd i)).smul_const (v x)
  exact (hF'.sub hc').add hb'

/-- `prop:supp-open-locality`, continuum-consistency clause: on every smooth
metric jet the right-hand side of the second row of `eq:main-open-writer`
with lattice steps `h e_i` converges as `h ↓ 0` to
`Σ_{ij} c^{ij}(g) ∂_i∂_j q - 2 Σ_i b^i(g) ∂_i v + F(g, (v, ∂q))`, the
right-hand side of the harmonic normal row `eq:main-harmonic-normal-row`
`a q_tt = c^{ij} ∂_i∂_j q - 2 b^i ∂_i q_t + F` (with `∂_i∂_j q = D²q(x)(e_i)(e_j)`,
`∂_i v = Dv(x) e_i`, `g = η + q`).  The coefficient-differential terms of the
compensator cancel exactly the `(∂_i c^{ij}) ∂_j q` and `(∂_i b^i) v`
contributions of the divergence and skew placements. -/
theorem writer_continuum_consistency {q v : Space → V} (hq : ContDiff ℝ 2 q)
    (hv : ContDiff ℝ 1 v) {b : Fin 3 → V → ℝ} {c : Fin 3 → Fin 3 → V → ℝ}
    {F : V → V × (Fin 3 → V) → V} (hb : ∀ i, ContDiff ℝ 1 (b i))
    (hc : ∀ i j, ContDiff ℝ 1 (c i j)) (hF : ∀ g, Continuous (F g)) (η : V) (x : Space) :
    Tendsto (fun h : ℝ => writerRhs c b F (fun i j g w => fderiv ℝ (c i j) g w)
        (fun i g w => fderiv ℝ (b i) g w) η h (stepVec h) q v x) (𝓝[>] 0)
      (𝓝 (∑ i, ∑ j, c i j (η + q x) • fderiv ℝ (fderiv ℝ q) x (E i) (E j)
        - ∑ i, (2 * b i (η + q x)) • fderiv ℝ v x (E i)
        + F (η + q x) (v x, fun i => fderiv ℝ q x (E i)))) := by
  unfold writerRhs
  have hflux : Tendsto (fun h : ℝ => divergenceFlux c η h (stepVec h) q x) (𝓝[>] 0)
      (𝓝 (∑ i, ∑ j, (c i j (η + q x) • fderiv ℝ (fderiv ℝ q) x (E i) (E j)
        + fderiv ℝ (c i j) (η + q x) (fderiv ℝ q x (E i)) • fderiv ℝ q x (E j)))) := by
    unfold divergenceFlux
    exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
      tendsto_flux_term hq (hc i j) η x i j
  have hlim := (hflux.sub (tendsto_skewTransport hq hv hb η x)).add
    (tendsto_compensator (v := v) (c := c) (b := b) hq hF η x)
  have hval : (∑ i, ∑ j, (c i j (η + q x) • fderiv ℝ (fderiv ℝ q) x (E i) (E j)
        + fderiv ℝ (c i j) (η + q x) (fderiv ℝ q x (E i)) • fderiv ℝ q x (E j)))
      - (∑ i, (b i (η + q x) • fderiv ℝ v x (E i)
        + (b i (η + q x) • fderiv ℝ v x (E i)
          + fderiv ℝ (b i) (η + q x) (fderiv ℝ q x (E i)) • v x)))
      + (F (η + q x) (v x, fun i => fderiv ℝ q x (E i))
        - ∑ i, ∑ j, fderiv ℝ (c i j) (η + q x) (fderiv ℝ q x (E i)) • fderiv ℝ q x (E j)
        + ∑ i, fderiv ℝ (b i) (η + q x) (fderiv ℝ q x (E i)) • v x) =
      ∑ i, ∑ j, c i j (η + q x) • fderiv ℝ (fderiv ℝ q) x (E i) (E j)
        - ∑ i, (2 * b i (η + q x)) • fderiv ℝ v x (E i)
        + F (η + q x) (v x, fun i => fderiv ℝ q x (E i)) := by
    simp only [Finset.sum_add_distrib, two_mul, add_smul]
    abel
  rw [hval] at hlim
  exact hlim

end Continuum

end

end RenewalGeometry.HarmonicWriter
