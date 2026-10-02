/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterRateLift
import RenewalGeometry.DiscreteAnalysis.TorusCoordinateIsoperimetryExact
import RenewalGeometry.Renewal.EfficientCutConstantScreen

/-!
# Cutoff-uniform cut margin of the `D₃` rate-lift graph on the odd periodic grid
  (`eq:supp-open-rate-lift` and the sentence after `eq:supp-open-rate-inversion`;
  `thm:main-spatial-screen`; clause (O3) of `thm:main-open-3plus1`; emergent-spacetime manuscript)

On the odd periodic grid `Λ_h = (ℤ/N)³` (`N` odd, `h = 1/N`; the manuscript's open writer uses
the odd periodic regulator), a field of masses `m_x` and directed `D₃` root rates
`k(x, a, s)` (twelve directions `±r_a`, `d3Step x a s = x + s·r_a`) defines the weighted
periodic graph `d3Graph`: vertex masses `m_x` and the symmetrised conductance
`c(x, y) = (m_x K(x, y) + m_y K(y, x))/2` of the directed kernel
`K(x, y) = Σ_{a,s} [d3Step x a s = y] k(x, a, s)` (`d3Conductance`).

**Perturbation of the flat `D₃` regulator.**  For odd `N` the map
`φ(n) = (n₀ + n₁, n₀ + n₂, n₁ + n₂)` is an additive bijection of `(ℤ/N)³`
(`d3Equiv`, inverse `½(y₀ + y₁ - y₂, y₀ - y₁ + y₂, -y₀ + y₁ + y₂)`, `2` being a unit mod `N`)
which carries the six coordinate directions `±e_m` of the periodic `A₃` graph onto the six
`D₃` directions `±(1,1,0), ±(1,0,1), ±(0,1,1)` (`phi_rootStep`).  Hence the `D₃` boundary count in
these directions equals the coordinate boundary count of the transported set
(`d3Boundary_eq`), and the `d`-uniform coordinate-grid isoperimetry
(`TorusCoordinateIsoperimetry.coordinateGridIsoperimetry`, constant `1/32`) transfers.

* `d3_cut_min` — if `h³/2 ≤ m_x ≤ 2h³` and `1/(16h²) ≤ k ≤ 3/(16h²)` (the interior cone of
  `rateLift_chart`), then for **every** vertex set `A`,
  `(1/4096) · min(μ(A), μ(Aᶜ))^{2/3} ≤ h · c(∂A)`, uniformly in odd `N`;
* `d3_degree_bound` — `h² Σ_u c(u, v) ≤ 6 m_v`; `d3_volume_le` — `μ(V) ≤ 2`;
* `d3_cutRatio_ge` — every half-volume cut has ratio `h c(∂A)/μ(A)^{2/3} ≥ 1/4096`
  (the spatial cut margin `I^sp ≥ 1/4096` of `eq:main-cut-constant`), and
  `d3_spatialCutConstant_ge` — `I^sp ≥ 1/4096` whenever a half-volume cut exists;
* `d3_screen` — **`thm:main-spatial-screen` for the rate-lift graph**: the complete
  `RenewalSpatialPositiveScreen` package (`L⁶` Sobolev, Poincaré, positive spectral floor,
  Weyl count, screen tail) with the cutoff-independent constants `I = 1/4096`, `D = 6`,
  `V_* = 2`.

The oddness of `N` is necessary: for even `N` the `D₃` graph splits into the two parity classes
and has a zero-capacity half-volume cut.
-/

open Finset
open scoped BigOperators

namespace RenewalGeometry.OpenWriterRateLift

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### The `D₃` step and graph -/

/-- The `D₃` root `r_a` as a grid vector. -/
def rootZ (a : D3Root) : Fin 3 → ZMod N :=
  fun m => (if m = a.1 + 1 then 1 else 0) + (if a.2 then 1 else -1) * (if m = a.1 + 2 then 1 else 0)

/-- The directed `D₃` direction `s · r_a` (`s = true`: `+r_a`). -/
def dirZ (a : D3Root) (s : Bool) : Fin 3 → ZMod N := if s then rootZ a else -rootZ a

/-- The `D₃` step `x ↦ x + s·r_a` on `(ℤ/N)³`. -/
def d3Step (x : Fin 3 → ZMod N) (a : D3Root) (s : Bool) : Fin 3 → ZMod N := x + dirZ a s

/-- The directed kernel `K(x, y) = Σ_{a,s} [x + s r_a = y] k(x, a, s)`. -/
def d3Kernel (k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ) (x y : Fin 3 → ZMod N) : ℝ :=
  ∑ a : D3Root, ∑ s : Bool, if d3Step x a s = y then k x a s else 0

/-- The symmetrised conductance `c(x, y) = (m_x K(x, y) + m_y K(y, x))/2`. -/
def d3Conductance (m : (Fin 3 → ZMod N) → ℝ) (k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ)
    (x y : Fin 3 → ZMod N) : ℝ :=
  (m x * d3Kernel k x y + m y * d3Kernel k y x) / 2

theorem d3Kernel_nonneg {k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ} (hk : ∀ x a s, 0 ≤ k x a s)
    (x y : Fin 3 → ZMod N) : 0 ≤ d3Kernel k x y :=
  sum_nonneg fun a _ => sum_nonneg fun s _ => by split_ifs <;> simp [hk]

/-- **The `D₃` rate graph** with masses `m` and directed rates `k`. -/
def d3Graph (m : (Fin 3 → ZMod N) → ℝ) (k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ)
    (hm : ∀ x, 0 < m x) (hk : ∀ x a s, 0 ≤ k x a s) : FiniteWeightedGraph (Fin 3 → ZMod N) where
  mass := m
  conductance := d3Conductance m k
  mass_pos := hm
  conductance_nonneg u v := by
    unfold d3Conductance
    have := d3Kernel_nonneg hk u v; have := d3Kernel_nonneg hk v u
    have := hm u; have := hm v
    positivity
  conductance_symm u v := by unfold d3Conductance; ring

/-! ### The `A₃ → D₃` transport on the odd grid -/

/-- `φ(n) = (n₀ + n₁, n₀ + n₂, n₁ + n₂)`. -/
def phiD3 (n : Fin 3 → ZMod N) : Fin 3 → ZMod N := ![n 0 + n 1, n 0 + n 2, n 1 + n 2]

/-- The half `(N + 1)/2` of the odd modulus `N = 2m + 1`. -/
def halfZ (m : ℕ) : ZMod N := ((m + 1 : ℕ) : ZMod N)

theorem two_mul_halfZ {m : ℕ} (hN : N = 2 * m + 1) : (2 : ZMod N) * halfZ m = 1 := by
  unfold halfZ
  have h0 : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
  have : (2 : ZMod N) * ((m + 1 : ℕ) : ZMod N) = ((N : ℕ) : ZMod N) + 1 := by
    rw [hN]; push_cast; ring
  rw [this, h0, zero_add]

/-- The inverse `ψ(y) = ½(y₀ + y₁ - y₂, y₀ - y₁ + y₂, -y₀ + y₁ + y₂)`. -/
def psiD3 (m : ℕ) (y : Fin 3 → ZMod N) : Fin 3 → ZMod N :=
  ![halfZ m * (y 0 + y 1 - y 2), halfZ m * (y 0 - y 1 + y 2), halfZ m * (-y 0 + y 1 + y 2)]

/-- **The additive bijection `φ` of the odd grid** (`N = 2m + 1`). -/
def d3Equiv {m : ℕ} (hN : N = 2 * m + 1) : (Fin 3 → ZMod N) ≃ (Fin 3 → ZMod N) where
  toFun := phiD3
  invFun := psiD3 m
  left_inv n := by
    have h2 := two_mul_halfZ (N := N) hN
    funext i; fin_cases i <;> simp [phiD3, psiD3] <;> first
      | linear_combination (n 0) * h2 | linear_combination (n 1) * h2
      | linear_combination (n 2) * h2
  right_inv y := by
    have h2 := two_mul_halfZ (N := N) hN
    funext i; fin_cases i <;> simp [phiD3, psiD3] <;> first
      | linear_combination (y 0) * h2 | linear_combination (y 1) * h2
      | linear_combination (y 2) * h2

theorem phiD3_add (x y : Fin 3 → ZMod N) : phiD3 (x + y) = phiD3 x + phiD3 y := by
  funext i; fin_cases i <;> simp [phiD3] <;> ring

/-- The `A₃` step `rootStep N n r` is `n + (rootCoordinates r)` cast to the grid. -/
theorem rootStep_eq (n : Fin 3 → ZMod N) (r : Fin 12) :
    A3PeriodicGraphSampling.rootStep N n r =
      n + fun i => ((A3PeriodicSmoothEnergy.rootCoordinates r i : ℤ) : ZMod N) := by
  funext i; rfl

/-- **The six coordinate directions of the `A₃` graph are carried to the `D₃` directions
`±(1,1,0), ±(1,0,1), ±(0,1,1)`.** -/
theorem phi_rootStep (n : Fin 3 → ZMod N) :
    phiD3 (A3PeriodicGraphSampling.rootStep N n 0) = d3Step (phiD3 n) (2, true) true ∧
    phiD3 (A3PeriodicGraphSampling.rootStep N n 3) = d3Step (phiD3 n) (2, true) false ∧
    phiD3 (A3PeriodicGraphSampling.rootStep N n 4) = d3Step (phiD3 n) (1, true) true ∧
    phiD3 (A3PeriodicGraphSampling.rootStep N n 7) = d3Step (phiD3 n) (1, true) false ∧
    phiD3 (A3PeriodicGraphSampling.rootStep N n 8) = d3Step (phiD3 n) (0, true) true ∧
    phiD3 (A3PeriodicGraphSampling.rootStep N n 11) = d3Step (phiD3 n) (0, true) false := by
  simp only [rootStep_eq, phiD3_add, d3Step]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> congr 1 <;> funext i <;> fin_cases i <;>
    simp [phiD3, dirZ, rootZ, A3PeriodicSmoothEnergy.rootCoordinates]

/-- The `D₃` boundary count of `A` in the six directions `±(1,1,0), ±(1,0,1), ±(0,1,1)`. -/
def d3Boundary (A : Finset (Fin 3 → ZMod N)) : ℕ :=
  ∑ u ∈ A, ((univ : Finset (Fin 3 × Bool)).filter fun p => d3Step u (p.1, true) p.2 ∉ A).card

/-- **The `D₃` boundary count is the coordinate boundary count of the transported set.** -/
theorem d3Boundary_eq {m : ℕ} (hN : N = 2 * m + 1) (A : Finset (Fin 3 → ZMod N)) :
    d3Boundary A =
      A3PeriodicScreens.basisBoundary N (A.map (d3Equiv hN).symm.toEmbedding) := by
  set e := d3Equiv hN
  set A' := A.map e.symm.toEmbedding
  have hmem : ∀ n, n ∈ A' ↔ phiD3 n ∈ A := by
    intro n; simp only [A', Finset.mem_map_equiv, Equiv.symm_symm]; rfl
  unfold A3PeriodicScreens.basisBoundary d3Boundary
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hu : phiD3 (e.symm u) = u := e.apply_symm_apply u
  obtain ⟨h0, h3, h4, h7, h8, h11⟩ := phi_rootStep (N := N) (e.symm u)
  rw [hu] at h0 h3 h4 h7 h8 h11
  rw [Finset.card_filter, Finset.card_filter]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool,
    A3PeriodicScreens.basisRoots]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Equiv.coe_toEmbedding, hmem, h0, h3, h4, h7, h8, h11]
  ring

/-! ### The cut inequality -/

/-- The mesh `h = 1/N`. -/
def meshN (N : ℕ) : ℝ := 1 / (N : ℝ)

theorem meshN_pos : 0 < meshN N := by
  unfold meshN; have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  positivity

/-- The interior-cone hypotheses on masses and rates at mesh `h = 1/N`. -/
structure ConeData (m : (Fin 3 → ZMod N) → ℝ) (k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ) :
    Prop where
  mass_lo : ∀ x, meshN N ^ 3 / 2 ≤ m x
  mass_hi : ∀ x, m x ≤ 2 * meshN N ^ 3
  rate_lo : ∀ x a s, 1 / (16 * meshN N ^ 2) ≤ k x a s
  rate_hi : ∀ x a s, k x a s ≤ 3 / (16 * meshN N ^ 2)

namespace ConeData

variable {m : (Fin 3 → ZMod N) → ℝ} {k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ}

theorem mass_pos (hc : ConeData m k) (x : Fin 3 → ZMod N) : 0 < m x :=
  lt_of_lt_of_le (by have := meshN_pos (N := N); positivity) (hc.mass_lo x)

theorem rate_nonneg (hc : ConeData m k) (x : Fin 3 → ZMod N) (a : D3Root) (s : Bool) :
    0 ≤ k x a s :=
  le_trans (by have := meshN_pos (N := N); positivity) (hc.rate_lo x a s)

end ConeData

/-- Capacity of a cut through the outgoing kernel: `Σ_{v ∉ A} K(u, v) = Σ_{a,s} [u + s r_a ∉ A] k`. -/
theorem sum_compl_kernel (k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ) (A : Finset (Fin 3 → ZMod N))
    (u : Fin 3 → ZMod N) :
    ∑ v ∈ Aᶜ, d3Kernel k u v = ∑ a : D3Root, ∑ s : Bool, if d3Step u a s ∉ A then k u a s else 0 := by
  unfold d3Kernel
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_compl]

/-- **Capacity lower bound**: `c(∂A) ≥ (h/64) · d3Boundary A`. -/
theorem cap_ge_d3Boundary {m : (Fin 3 → ZMod N) → ℝ} {k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ}
    (hc : ConeData m k) (A : Finset (Fin 3 → ZMod N)) :
    meshN N / 64 * (d3Boundary A : ℝ) ≤ finiteCutCapacity (d3Conductance m k) A := by
  have hh := meshN_pos (N := N)
  unfold finiteCutCapacity d3Boundary
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  -- lower bound by the outgoing half of the conductance
  have hhalf : ∀ v, m u * d3Kernel k u v / 2 ≤ d3Conductance m k u v := by
    intro v
    unfold d3Conductance
    have := d3Kernel_nonneg hc.rate_nonneg v u
    have := (hc.mass_pos v).le
    nlinarith [mul_nonneg (hc.mass_pos v).le (d3Kernel_nonneg hc.rate_nonneg v u)]
  have h1 : m u / 2 * ∑ v ∈ Aᶜ, d3Kernel k u v ≤ ∑ v ∈ Aᶜ, d3Conductance m k u v := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => by have := hhalf v; linarith
  refine le_trans ?_ h1
  rw [sum_compl_kernel, Finset.card_filter]
  push_cast
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool]
  -- each basis direction contributes at least `(h³/2)/2 · 1/(16h²) = h/64`
  have hm := hc.mass_lo u
  have key : ∀ a s, (if d3Step u a s ∉ A then (1 : ℝ) else 0) * (meshN N / 64) ≤
      m u / 2 * (if d3Step u a s ∉ A then k u a s else 0) := by
    intro a s
    by_cases hA : d3Step u a s ∈ A
    · simp [hA]
    · simp only [hA, not_false_eq_true, ite_true, one_mul]
      have hk := hc.rate_lo u a s
      have e : meshN N / 64 = (meshN N ^ 3 / 2) / 2 * (1 / (16 * meshN N ^ 2)) := by
        field_simp; ring
      rw [e]
      have hk0 : 0 ≤ 1 / (16 * meshN N ^ 2) := by positivity
      exact mul_le_mul (by linarith) hk hk0 (by have := hc.mass_pos u; linarith)
  have hnn : ∀ a s, 0 ≤ m u / 2 * (if d3Step u a s ∉ A then k u a s else 0) := by
    intro a s
    have := (hc.mass_pos u).le
    by_cases hA : d3Step u a s ∈ A
    · simp [hA]
    · simp only [hA, not_false_eq_true, ite_true]
      exact mul_nonneg (by linarith) (hc.rate_nonneg u a s)
  have k0 := key (0, true) true; have k1 := key (0, true) false
  have k2 := key (1, true) true; have k3 := key (1, true) false
  have k4 := key (2, true) true; have k5 := key (2, true) false
  have n0 := hnn (0, false) true; have n1 := hnn (0, false) false
  have n2 := hnn (1, false) true; have n3 := hnn (1, false) false
  have n4 := hnn (2, false) true; have n5 := hnn (2, false) false
  rw [mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add,
    mul_add]
  nlinarith

/-- The coordinate isoperimetry, transported: for `0 < #B ≤ N³/2`,
`(1/32) (h³ #B)^{2/3} ≤ h² d3Boundary B`. -/
theorem d3_isoperimetry {m : ℕ} (hN : N = 2 * m + 1) (B : Finset (Fin 3 → ZMod N))
    (hB : 0 < B.card) (hhalf : 2 * B.card ≤ N ^ 3) :
    1 / 32 * (meshN N ^ 3 * B.card) ^ ((2 : ℝ) / 3) ≤ meshN N ^ 2 * (d3Boundary B : ℝ) := by
  have hiso := TorusCoordinateIsoperimetry.coordinateGridIsoperimetry N
    (B.map (d3Equiv hN).symm.toEmbedding) (by rwa [Finset.card_map])
    (by rwa [Finset.card_map])
  rw [Finset.card_map, ← d3Boundary_eq hN] at hiso
  simpa [A3PeriodicGraphSampling.mesh, meshN] using hiso

/-- **The cutoff-uniform cut margin of the `D₃` rate graph** (min form, every vertex set):
`(1/4096) · min(μ(A), μ(Aᶜ))^{2/3} ≤ h · c(∂A)` for odd `N`. -/
theorem d3_cut_min {m₀ : ℕ} (hN : N = 2 * m₀ + 1) {m : (Fin 3 → ZMod N) → ℝ}
    {k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ} (hc : ConeData m k) (A : Finset (Fin 3 → ZMod N)) :
    1 / 4096 * min (∑ v ∈ A, m v) (∑ v ∈ Aᶜ, m v) ^ ((2 : ℝ) / 3) ≤
      meshN N * finiteCutCapacity (d3Conductance m k) A := by
  have hh := meshN_pos (N := N)
  have hsym : ∀ x y, d3Conductance m k x y = d3Conductance m k y x := fun x y => by
    unfold d3Conductance; ring
  have hcap0 : ∀ A : Finset (Fin 3 → ZMod N), 0 ≤ finiteCutCapacity (d3Conductance m k) A := by
    intro A
    refine le_trans ?_ (cap_ge_d3Boundary hc A)
    positivity
  have hcardV : (univ : Finset (Fin 3 → ZMod N)).card = N ^ 3 := by
    rw [Finset.card_univ]; simp [ZMod.card]
  -- the smaller of `A`, `Aᶜ`
  have key : ∀ B : Finset (Fin 3 → ZMod N), 2 * B.card ≤ N ^ 3 →
      finiteCutCapacity (d3Conductance m k) B = finiteCutCapacity (d3Conductance m k) A →
      min (∑ v ∈ A, m v) (∑ v ∈ Aᶜ, m v) ≤ ∑ v ∈ B, m v →
      1 / 4096 * min (∑ v ∈ A, m v) (∑ v ∈ Aᶜ, m v) ^ ((2 : ℝ) / 3) ≤
        meshN N * finiteCutCapacity (d3Conductance m k) A := by
    intro B hB hcapB hminB
    have hmin0 : 0 ≤ min (∑ v ∈ A, m v) (∑ v ∈ Aᶜ, m v) :=
      le_min (sum_nonneg fun v _ => (hc.mass_pos v).le) (sum_nonneg fun v _ => (hc.mass_pos v).le)
    rcases Nat.eq_zero_or_pos B.card with h0 | hpos
    · rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hminB
      have : min (∑ v ∈ A, m v) (∑ v ∈ Aᶜ, m v) = 0 := le_antisymm hminB hmin0
      rw [this, Real.zero_rpow (by norm_num), mul_zero]
      exact mul_nonneg hh.le (hcap0 A)
    have hiso := d3_isoperimetry hN B hpos hB
    have hcapB' := cap_ge_d3Boundary hc B
    -- `μ(B) ≤ 2 h³ #B`
    have hμB : ∑ v ∈ B, m v ≤ 2 * (meshN N ^ 3 * B.card) := by
      calc ∑ v ∈ B, m v ≤ ∑ _v ∈ B, 2 * meshN N ^ 3 := sum_le_sum fun v _ => hc.mass_hi v
        _ = 2 * (meshN N ^ 3 * B.card) := by rw [sum_const, nsmul_eq_mul]; ring
    have hX0 : 0 ≤ meshN N ^ 3 * (B.card : ℝ) := by positivity
    have hrp : min (∑ v ∈ A, m v) (∑ v ∈ Aᶜ, m v) ^ ((2 : ℝ) / 3) ≤
        2 * (meshN N ^ 3 * B.card) ^ ((2 : ℝ) / 3) := by
      calc min (∑ v ∈ A, m v) (∑ v ∈ Aᶜ, m v) ^ ((2 : ℝ) / 3)
          ≤ (2 * (meshN N ^ 3 * B.card)) ^ ((2 : ℝ) / 3) :=
            Real.rpow_le_rpow hmin0 (hminB.trans hμB) (by norm_num)
        _ = (2 : ℝ) ^ ((2 : ℝ) / 3) * (meshN N ^ 3 * B.card) ^ ((2 : ℝ) / 3) :=
            Real.mul_rpow (by norm_num) hX0
        _ ≤ 2 * (meshN N ^ 3 * B.card) ^ ((2 : ℝ) / 3) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX0 _)
            calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
    rw [← hcapB]
    have hY0 : 0 ≤ (meshN N ^ 3 * B.card) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hX0 _
    calc 1 / 4096 * min (∑ v ∈ A, m v) (∑ v ∈ Aᶜ, m v) ^ ((2 : ℝ) / 3)
        ≤ 1 / 4096 * (2 * (meshN N ^ 3 * B.card) ^ ((2 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left hrp (by norm_num)
      _ = 1 / 64 * (1 / 32 * (meshN N ^ 3 * B.card) ^ ((2 : ℝ) / 3)) := by ring
      _ ≤ 1 / 64 * (meshN N ^ 2 * (d3Boundary B : ℝ)) :=
          mul_le_mul_of_nonneg_left hiso (by norm_num)
      _ = meshN N * (meshN N / 64 * (d3Boundary B : ℝ)) := by ring
      _ ≤ meshN N * finiteCutCapacity (d3Conductance m k) B :=
          mul_le_mul_of_nonneg_left hcapB' hh.le
  by_cases hA : 2 * A.card ≤ N ^ 3
  · exact key A hA rfl (min_le_left _ _)
  · have hAc : 2 * Aᶜ.card ≤ N ^ 3 := by
      have h1 := Finset.card_compl (s := A)
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin] at h1
      have h2 : A.card ≤ N ^ 3 := by
        have := Finset.card_le_univ A
        rwa [Fintype.card_fun, ZMod.card, Fintype.card_fin] at this
      omega
    exact key Aᶜ hAc (FiniteWeightedGraph.finiteCutCapacity_compl _ hsym A) (min_le_right _ _)

/-- The total outgoing rate: `Σ_u K(v, u) = Σ_{a,s} k(v, a, s)`. -/
theorem sum_kernel_out (k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ) (v : Fin 3 → ZMod N) :
    ∑ u, d3Kernel k v u = ∑ a : D3Root, ∑ s : Bool, k v a s := by
  unfold d3Kernel
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem d3Step_eq_iff (u v : Fin 3 → ZMod N) (a : D3Root) (s : Bool) :
    d3Step u a s = v ↔ u = v - dirZ a s := by
  unfold d3Step
  constructor
  · intro h; rw [← h]; abel
  · intro h; rw [h]; abel

/-- The incoming mass flux: `Σ_u m_u K(u, v) = Σ_{a,s} m_{v - s r_a} k(v - s r_a, a, s)`. -/
theorem sum_kernel_in (m : (Fin 3 → ZMod N) → ℝ) (k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ)
    (v : Fin 3 → ZMod N) :
    ∑ u, m u * d3Kernel k u v =
      ∑ a : D3Root, ∑ s : Bool, m (v - dirZ a s) * k (v - dirZ a s) a s := by
  unfold d3Kernel
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : ∀ u, (m u * if d3Step u a s = v then k u a s else 0) =
      if u = v - dirZ a s then m u * k u a s else 0 := by
    intro u
    by_cases h : u = v - dirZ a s
    · have h' : d3Step u a s = v := (d3Step_eq_iff u v a s).mpr h
      rw [if_pos h', if_pos h]
    · have h' : ¬ d3Step u a s = v := fun h' => h ((d3Step_eq_iff u v a s).mp h')
      simp [h, h']
  simp only [e]
  rw [Finset.sum_ite_eq']
  simp

/-- **Weighted degree bound** `h² Σ_u c(u, v) ≤ 6 m_v` (`eq:supp-weighted-degree`). -/
theorem d3_degree_bound {m : (Fin 3 → ZMod N) → ℝ} {k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ}
    (hc : ConeData m k) (v : Fin 3 → ZMod N) :
    meshN N ^ 2 * (∑ u, d3Conductance m k u v) ≤ 6 * m v := by
  have hh := meshN_pos (N := N)
  have hsplit : ∑ u, d3Conductance m k u v =
      ((∑ u, m u * d3Kernel k u v) + m v * ∑ u, d3Kernel k v u) / 2 := by
    unfold d3Conductance
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit, sum_kernel_in, sum_kernel_out]
  have hin : ∑ a : D3Root, ∑ s : Bool, m (v - dirZ a s) * k (v - dirZ a s) a s ≤
      12 * (2 * meshN N ^ 3 * (3 / (16 * meshN N ^ 2))) := by
    have hb : ∀ a s, m (v - dirZ a s) * k (v - dirZ a s) a s ≤
        2 * meshN N ^ 3 * (3 / (16 * meshN N ^ 2)) := fun a s =>
      mul_le_mul (hc.mass_hi _) (hc.rate_hi _ a s) (hc.rate_nonneg _ a s) (by positivity)
    calc ∑ a : D3Root, ∑ s : Bool, m (v - dirZ a s) * k (v - dirZ a s) a s
        ≤ ∑ _a : D3Root, ∑ _s : Bool, 2 * meshN N ^ 3 * (3 / (16 * meshN N ^ 2)) :=
          sum_le_sum fun a _ => sum_le_sum fun s _ => hb a s
      _ = 12 * (2 * meshN N ^ 3 * (3 / (16 * meshN N ^ 2))) := by simp; ring
  have hout : ∑ a : D3Root, ∑ s : Bool, k v a s ≤ 12 * (3 / (16 * meshN N ^ 2)) := by
    calc ∑ a : D3Root, ∑ s : Bool, k v a s ≤ ∑ _a : D3Root, ∑ _s : Bool, 3 / (16 * meshN N ^ 2) :=
          sum_le_sum fun a _ => sum_le_sum fun s _ => hc.rate_hi v a s
      _ = 12 * (3 / (16 * meshN N ^ 2)) := by simp; ring
  have hmv := hc.mass_lo v
  have hm0 := (hc.mass_pos v).le
  have e1 : meshN N ^ 2 * (12 * (2 * meshN N ^ 3 * (3 / (16 * meshN N ^ 2)))) =
      9 / 2 * meshN N ^ 3 := by field_simp; ring
  have e2 : meshN N ^ 2 * (m v * (12 * (3 / (16 * meshN N ^ 2)))) = m v * (9 / 4) := by
    field_simp; ring
  have h1 := mul_le_mul_of_nonneg_left hin (sq_nonneg (meshN N))
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hout hm0) (sq_nonneg (meshN N))
  rw [e1] at h1
  rw [e2] at h2
  have e3 : meshN N ^ 2 * ((∑ a : D3Root, ∑ s : Bool, m (v - dirZ a s) * k (v - dirZ a s) a s +
      m v * ∑ a : D3Root, ∑ s : Bool, k v a s) / 2) =
      (meshN N ^ 2 * ∑ a : D3Root, ∑ s : Bool, m (v - dirZ a s) * k (v - dirZ a s) a s +
        meshN N ^ 2 * (m v * ∑ a : D3Root, ∑ s : Bool, k v a s)) / 2 := by ring
  rw [e3]
  linarith

/-- The total mass is at most `2` (`h = 1/N`, `m ≤ 2h³`). -/
theorem d3_volume_le {m : (Fin 3 → ZMod N) → ℝ} {k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ}
    (hc : ConeData m k) : ∑ v, m v ≤ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  calc ∑ v, m v ≤ ∑ _v : Fin 3 → ZMod N, 2 * meshN N ^ 3 := sum_le_sum fun v _ => hc.mass_hi v
    _ = 2 := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, meshN]
        push_cast
        field_simp

/-- **The spatial cut margin** `I^sp ≥ 1/4096` (`eq:main-cut-constant`): every half-volume cut
of the rate graph has `h c(∂A)/μ(A)^{2/3} ≥ 1/4096`, uniformly in odd `N`. -/
theorem d3_cutRatio_ge {m₀ : ℕ} (hN : N = 2 * m₀ + 1) {m : (Fin 3 → ZMod N) → ℝ}
    {k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ} (hc : ConeData m k) (A : Finset (Fin 3 → ZMod N))
    (hA : (d3Graph m k hc.mass_pos hc.rate_nonneg).IsHalfVolumeCut A) :
    1 / 4096 ≤ (d3Graph m k hc.mass_pos hc.rate_nonneg).cutRatio
      (fun x y => meshN N * (d3Graph m k hc.mass_pos hc.rate_nonneg).conductance x y) A := by
  set G := d3Graph m k hc.mass_pos hc.rate_nonneg
  have hmin : min (∑ v ∈ A, m v) (∑ v ∈ Aᶜ, m v) = ∑ v ∈ A, m v := by
    apply min_eq_left
    have := G.setMass_compl A
    have h2 := hA.2
    change ∑ v ∈ Aᶜ, m v = G.volume - ∑ v ∈ A, m v at this
    change ∑ v ∈ A, m v ≤ G.volume / 2 at h2
    linarith
  have hcut := d3_cut_min hN hc A
  rw [hmin] at hcut
  have hpos : 0 < (∑ v ∈ A, m v) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hA.1 _
  show 1 / 4096 ≤ finiteCutCapacity (fun x y => meshN N * G.conductance x y) A /
    (∑ v ∈ A, m v) ^ ((2 : ℝ) / 3)
  rw [le_div_iff₀ hpos]
  have hcap : finiteCutCapacity (fun x y => meshN N * G.conductance x y) A =
      meshN N * finiteCutCapacity (d3Conductance m k) A := by
    unfold finiteCutCapacity; simp only [Finset.mul_sum]; rfl
  rw [hcap]
  exact hcut

/-- `I^sp ≥ 1/4096` for the rate graph whenever a half-volume cut exists (e.g. `N ≥ 3`). -/
theorem d3_spatialCutConstant_ge {m₀ : ℕ} (hN : N = 2 * m₀ + 1) {m : (Fin 3 → ZMod N) → ℝ}
    {k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ} (hc : ConeData m k)
    (hne : ∃ A, (d3Graph m k hc.mass_pos hc.rate_nonneg).IsHalfVolumeCut A) :
    1 / 4096 ≤ (d3Graph m k hc.mass_pos hc.rate_nonneg).spatialCutConstant (meshN N) := by
  obtain ⟨A₀, hA₀⟩ := hne
  unfold FiniteWeightedGraph.spatialCutConstant FiniteWeightedGraph.cutConstant
  refine le_csInf ⟨_, ⟨A₀, hA₀, rfl⟩⟩ ?_
  rintro r ⟨A, hA, rfl⟩
  exact d3_cutRatio_ge hN hc A hA

/-- The min-form cut margin as a `SpatialCutMargin` with constant `1/4096`. -/
def d3CutMargin {m₀ : ℕ} (hN : N = 2 * m₀ + 1) {m : (Fin 3 → ZMod N) → ℝ}
    {k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ} (hc : ConeData m k) :
    (d3Graph m k hc.mass_pos hc.rate_nonneg).SpatialCutMargin (meshN N) where
  constant := 1 / 4096
  constant_pos := by norm_num
  cut A := d3_cut_min hN hc A

/-- **`thm:main-spatial-screen` for the `D₃` rate graph**: on the odd grid, interior-cone masses
and rates give the complete `RenewalSpatialPositiveScreen` package (`L⁶` Sobolev, Poincaré,
positive spectral floor, Weyl count, compact-screen tail) with cutoff-independent constants
`I = 1/4096`, `D = 6`, `V_* = 2`. -/
theorem d3_screen {m₀ : ℕ} (hN : N = 2 * m₀ + 1) {m : (Fin 3 → ZMod N) → ℝ}
    {k : (Fin 3 → ZMod N) → D3Root → Bool → ℝ} (hc : ConeData m k) :
    ∃ S : (d3Graph m k hc.mass_pos hc.rate_nonneg).RenewalSpatialPositiveScreen (1 / 4096) 6
        (meshN N) 2,
      S.poincareConstant = 128 * 6 * (2 : ℝ) ^ ((2 : ℝ) / 3) / (1 / 4096) ^ 2 ∧
      S.spectralFloor = (1 / 4096) ^ 2 / (128 * 6 * (2 : ℝ) ^ ((2 : ℝ) / 3)) :=
  (d3Graph m k hc.mass_pos hc.rate_nonneg).renewalSpatialPositiveScreen 6 (meshN N) 2
    (by norm_num) meshN_pos (by norm_num) (d3_volume_le hc) (fun v => d3_degree_bound hc v)
    (d3CutMargin hN hc)

end

end RenewalGeometry.OpenWriterRateLift
