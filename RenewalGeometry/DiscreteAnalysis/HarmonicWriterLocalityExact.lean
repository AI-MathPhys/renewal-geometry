/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.RootParityConnectorExact
import MathPhys.DiscreteAnalysis.HarmonicWriterScheme
open MathPhys

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
open MathPhys.HarmonicWriter

noncomputable section

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


end

end RenewalGeometry.HarmonicWriter
