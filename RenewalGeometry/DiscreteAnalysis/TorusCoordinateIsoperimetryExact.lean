/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.A3PeriodicScreensScalingExact

/-!
# The coordinate-grid edge-isoperimetric inequality on the periodic torus
  (`lem:supp-periodic-screens`, emergent-spacetime supplement)

This file discharges the hypothesis `CoordinateGridIsoperimetry d c₀` of
`A3PeriodicScreensScalingExact` with the `d`-independent constant
`c₀ = 1/32`: for every vertex set `A ⊆ (ZMod d)³` with `0 < #A ≤ d³/2`,

  `#∂A ≥ (1/32) · #A^{2/3}`,

where `#∂A = basisBoundary d A` counts the boundary edges of `A` in the six
basis-root directions `±e₁, ±e₂, ±e₃` (each counted through its endpoint
in `A`).  In physical units `h = 1/d` this is exactly
`h² #∂A ≥ c₀ (h³ #A)^{2/3}`.

The proof is a *box-path* argument rather than the Loomis–Whitney slicing
sketched in the manuscript (disclosed): writing
`shiftDefect A p = #{u ∈ A : u + p ∉ A}`,

* `shiftDefect_add`: `shiftDefect A (p + q) ≤ shiftDefect A p + shiftDefect A q`
  (a path `u → u + p → u + p + q` leaving `A` leaves it on one of its two legs);
* `shiftDefect_nsmul`: `shiftDefect A (s • p) ≤ s · shiftDefect A p`;
* hence for a box vector `δ ∈ [0,m)³`,
  `shiftDefect A δ ≤ m · basisBoundary d A` (`shiftDefect_box_le`);
* summing over the `m³` box vectors with `m ≤ d` (so `δ ↦ u + δ` is
  injective) gives `#A · (m³ − #A) ≤ m⁴ · basisBoundary d A`
  (`card_mul_le_box_sum`);
* the least `m` with `m³ ≥ 2 #A` satisfies `m < 2.3 · #A^{1/3}`, whence
  `#A^{2/3} ≤ 28 · basisBoundary d A` (`basisBoundary_ge`).

`coordinateGridIsoperimetry` packages this as `CoordinateGridIsoperimetry d (1/32)`
for every `d`, and `periodic_screens_unconditional` restates
`lem:supp-periodic-screens` with no remaining hypothesis: the cut constant is
`c_cut = 1/(256 a₊)` and the Poincaré / Weyl constants are
`poincareConstant a₋ a₊ (1/32)`, `weylConstant a₋ a₊ (1/32)`, depending only on
`a₋, a₊`, uniformly in `h = 1/d` and `a ∈ [a₋, a₊]`.
-/

open Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace RenewalGeometry.TorusCoordinateIsoperimetry

open A3PeriodicGraphSampling A3PeriodicScreens

/-! ### Shift defects on an additive group -/

section Group

variable {V : Type*} [AddCommGroup V] [DecidableEq V]

/-- `shiftDefect A p = #{u ∈ A : u + p ∉ A}`, the number of points of `A`
whose translate by `p` leaves `A`. -/
def shiftDefect (A : Finset V) (p : V) : ℕ :=
  (A.filter fun u => u + p ∉ A).card

theorem shiftDefect_zero (A : Finset V) : shiftDefect A 0 = 0 := by
  unfold shiftDefect
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u hu; simp [hu]

/-- Subadditivity of the shift defect: a two-leg path `u → u + p → u + p + q`
that leaves `A` leaves it on one of its legs. -/
theorem shiftDefect_add (A : Finset V) (p q : V) :
    shiftDefect A (p + q) ≤ shiftDefect A p + shiftDefect A q := by
  unfold shiftDefect
  have hsub : (A.filter fun u => u + (p + q) ∉ A) ⊆
      (A.filter fun u => u + p ∉ A) ∪
        ((A.filter fun w => w + q ∉ A).image fun w => w - p) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
    by_cases hp : u + p ∈ A
    · right
      refine ⟨u + p, ?_, by abel⟩
      rw [Finset.mem_filter]
      exact ⟨hp, by rw [add_assoc]; exact hu.2⟩
    · left; exact ⟨hu.1, hp⟩
  calc (A.filter fun u => u + (p + q) ∉ A).card
      ≤ ((A.filter fun u => u + p ∉ A) ∪
          ((A.filter fun w => w + q ∉ A).image fun w => w - p)).card :=
        Finset.card_le_card hsub
    _ ≤ (A.filter fun u => u + p ∉ A).card +
          ((A.filter fun w => w + q ∉ A).image fun w => w - p).card :=
        Finset.card_union_le _ _
    _ ≤ (A.filter fun u => u + p ∉ A).card +
          (A.filter fun w => w + q ∉ A).card :=
        Nat.add_le_add_left Finset.card_image_le _

/-- `shiftDefect A (s • p) ≤ s · shiftDefect A p`. -/
theorem shiftDefect_nsmul (A : Finset V) (p : V) (s : ℕ) :
    shiftDefect A (s • p) ≤ s * shiftDefect A p := by
  induction s with
  | zero => simp [shiftDefect_zero]
  | succ s ih =>
    rw [succ_nsmul]
    calc shiftDefect A (s • p + p) ≤ shiftDefect A (s • p) + shiftDefect A p :=
          shiftDefect_add A _ _
      _ ≤ s * shiftDefect A p + shiftDefect A p := Nat.add_le_add_right ih _
      _ = (s + 1) * shiftDefect A p := by ring

end Group

/-! ### The periodic coordinate grid `(ZMod d)³` -/

variable (d : ℕ) [NeZero d]

/-- The unit vector `e i` of the periodic coordinate grid. -/
def unitVec (i : Fin 3) : Vertex d := Pi.single i (1 : ZMod d)

/-- A box vector `δ ∈ ℕ³` reduced into the torus. -/
def toVec (δ : Fin 3 → ℕ) : Vertex d := fun i => (δ i : ZMod d)

theorem toVec_eq (δ : Fin 3 → ℕ) :
    toVec d δ = δ 0 • unitVec d 0 + (δ 1 • unitVec d 1 + δ 2 • unitVec d 2) := by
  funext i
  fin_cases i <;> simp [toVec, unitVec]

/-- The basis roots `0, 4, 8` of `rootCoordinates` are `+e₁, +e₂, +e₃`. -/
theorem rootStep_unitVec (u : Vertex d) :
    rootStep d u 0 = u + unitVec d 0 ∧ rootStep d u 4 = u + unitVec d 1 ∧
      rootStep d u 8 = u + unitVec d 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;>
    simp [rootStep, LatticeGridSampling.step, A3PeriodicSmoothEnergy.rootCoordinates,
      unitVec]

/-- The three `+e_i` defects are dominated by the basis boundary count. -/
theorem sum_unitVec_defect_le (A : Finset (Vertex d)) :
    shiftDefect A (unitVec d 0) + shiftDefect A (unitVec d 1) +
      shiftDefect A (unitVec d 2) ≤ basisBoundary d A := by
  unfold shiftDefect basisBoundary
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  obtain ⟨h0, h4, h8⟩ := rootStep_unitVec d u
  have hexp : ∑ r ∈ basisRoots, (if rootStep d u r ∉ A then 1 else 0) =
      (if rootStep d u 0 ∉ A then 1 else 0) + (if rootStep d u 3 ∉ A then 1 else 0) +
      (if rootStep d u 4 ∉ A then 1 else 0) + (if rootStep d u 7 ∉ A then 1 else 0) +
      (if rootStep d u 8 ∉ A then 1 else 0) + (if rootStep d u 11 ∉ A then 1 else 0) := by
    simp [basisRoots, Finset.sum_insert, add_assoc]
  rw [hexp, h0, h4, h8]
  split_ifs <;> omega

/-- A box vector `δ ∈ [0,m)³` has defect at most `m · basisBoundary d A`. -/
theorem shiftDefect_box_le (A : Finset (Vertex d)) (m : ℕ) (δ : Fin 3 → ℕ)
    (hδ : ∀ i, δ i ≤ m) :
    shiftDefect A (toVec d δ) ≤ m * basisBoundary d A := by
  rw [toVec_eq]
  have h1 := shiftDefect_nsmul A (unitVec d 0) (δ 0)
  have h2 := shiftDefect_nsmul A (unitVec d 1) (δ 1)
  have h3 := shiftDefect_nsmul A (unitVec d 2) (δ 2)
  have hB := sum_unitVec_defect_le d A
  calc shiftDefect A (δ 0 • unitVec d 0 + (δ 1 • unitVec d 1 + δ 2 • unitVec d 2))
      ≤ shiftDefect A (δ 0 • unitVec d 0) +
          shiftDefect A (δ 1 • unitVec d 1 + δ 2 • unitVec d 2) :=
        shiftDefect_add A _ _
    _ ≤ shiftDefect A (δ 0 • unitVec d 0) +
          (shiftDefect A (δ 1 • unitVec d 1) + shiftDefect A (δ 2 • unitVec d 2)) :=
        Nat.add_le_add_left (shiftDefect_add A _ _) _
    _ ≤ δ 0 * shiftDefect A (unitVec d 0) +
          (δ 1 * shiftDefect A (unitVec d 1) + δ 2 * shiftDefect A (unitVec d 2)) := by
        omega
    _ ≤ m * shiftDefect A (unitVec d 0) +
          (m * shiftDefect A (unitVec d 1) + m * shiftDefect A (unitVec d 2)) := by
        have := hδ 0; have := hδ 1; have := hδ 2
        gcongr
    _ = m * (shiftDefect A (unitVec d 0) + shiftDefect A (unitVec d 1) +
          shiftDefect A (unitVec d 2)) := by ring
    _ ≤ m * basisBoundary d A := Nat.mul_le_mul_left _ hB

/-- The box `[0,m)³` of natural vectors. -/
def box (m : ℕ) : Finset (Fin 3 → ℕ) := Fintype.piFinset fun _ => Finset.range m

theorem card_box (m : ℕ) : (box m).card = m ^ 3 := by
  simp [box, Fintype.card_piFinset]

theorem mem_box {m : ℕ} {δ : Fin 3 → ℕ} : δ ∈ box m ↔ ∀ i, δ i < m := by
  simp [box, Fintype.mem_piFinset]

/-- For `m ≤ d` the box embeds injectively into the torus. -/
theorem toVec_injOn (m : ℕ) (hm : m ≤ d) :
    Set.InjOn (toVec d) (box m : Set (Fin 3 → ℕ)) := by
  intro δ hδ δ' hδ' h
  rw [Finset.mem_coe, mem_box] at hδ hδ'
  funext i
  have hi : (δ i : ZMod d) = (δ' i : ZMod d) := congrFun h i
  rw [ZMod.natCast_eq_natCast_iff'] at hi
  rwa [Nat.mod_eq_of_lt (lt_of_lt_of_le (hδ i) hm),
    Nat.mod_eq_of_lt (lt_of_lt_of_le (hδ' i) hm)] at hi

/-- For `u ∈ A` and `m ≤ d`, at least `m³ − #A` box translates of `u` leave `A`. -/
theorem card_box_leaving_ge (A : Finset (Vertex d)) (m : ℕ) (hm : m ≤ d)
    (u : Vertex d) :
    m ^ 3 ≤ A.card + ((box m).filter fun δ => u + toVec d δ ∉ A).card := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := box m) (fun δ => u + toVec d δ ∈ A)
  rw [card_box] at hsplit
  have hin : ((box m).filter fun δ => u + toVec d δ ∈ A).card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun δ => u + toVec d δ)
    · intro δ hδ
      exact (Finset.mem_filter.mp hδ).2
    · intro δ hδ δ' hδ' h
      have hδ0 : δ ∈ (box m : Set (Fin 3 → ℕ)) :=
        Finset.mem_coe.mpr (Finset.mem_filter.mp hδ).1
      have hδ0' : δ' ∈ (box m : Set (Fin 3 → ℕ)) :=
        Finset.mem_coe.mpr (Finset.mem_filter.mp hδ').1
      exact toVec_injOn d m hm hδ0 hδ0' (add_left_cancel h)
  omega

/-- The box-path count: `#A · (m³ − #A) ≤ m⁴ · basisBoundary d A` for `m ≤ d`
(stated without truncated subtraction). -/
theorem card_mul_le_box_sum (A : Finset (Vertex d)) (m : ℕ) (hm : m ≤ d) :
    A.card * m ^ 3 ≤ A.card * A.card + m ^ 4 * basisBoundary d A := by
  -- the double count `∑_{δ ∈ box} shiftDefect A δ = ∑_{u ∈ A} #{δ : u + δ ∉ A}`
  have hdouble : ∑ δ ∈ box m, shiftDefect A (toVec d δ) =
      ∑ u ∈ A, ((box m).filter fun δ => u + toVec d δ ∉ A).card := by
    unfold shiftDefect
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  -- upper bound
  have hupper : ∑ δ ∈ box m, shiftDefect A (toVec d δ) ≤ m ^ 4 * basisBoundary d A := by
    calc ∑ δ ∈ box m, shiftDefect A (toVec d δ)
        ≤ ∑ _δ ∈ box m, m * basisBoundary d A := by
          apply Finset.sum_le_sum
          intro δ hδ
          exact shiftDefect_box_le d A m δ fun i => (mem_box.mp hδ i).le
      _ = m ^ 4 * basisBoundary d A := by
          rw [Finset.sum_const, card_box, smul_eq_mul]; ring
  -- lower bound
  have hlower : A.card * m ^ 3 ≤ A.card * A.card +
      ∑ u ∈ A, ((box m).filter fun δ => u + toVec d δ ∉ A).card := by
    have : ∑ u ∈ A, m ^ 3 ≤
        ∑ u ∈ A, (A.card + ((box m).filter fun δ => u + toVec d δ ∉ A).card) :=
      Finset.sum_le_sum fun u _ => card_box_leaving_ge d A m hm u
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, smul_eq_mul,
      smul_eq_mul] at this
    exact this
  rw [← hdouble] at hlower
  omega

/-- The least `m` with `m³ ≥ 2 #A`: it satisfies `m ≤ d`, `2 ≤ m` and
`(m − 1)³ < 2 #A`. -/
theorem exists_cube_root (N : ℕ) (hN : 0 < N) (hhalf : 2 * N ≤ d ^ 3) :
    ∃ m : ℕ, m ≤ d ∧ 2 ≤ m ∧ 2 * N ≤ m ^ 3 ∧ (m - 1) ^ 3 < 2 * N := by
  have hex : ∃ m : ℕ, 2 * N ≤ m ^ 3 := ⟨d, hhalf⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hhalf, ?_, Nat.find_spec hex, ?_⟩
  · by_contra hlt
    push Not at hlt
    have h := Nat.find_spec hex
    have : Nat.find hex ^ 3 ≤ 1 ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    omega
  · have hpos : 0 < Nat.find hex := by
      by_contra h0
      push Not at h0
      have h := Nat.find_spec hex
      rw [Nat.le_zero.mp h0] at h
      omega
    have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    omega

/-- The torus edge-isoperimetric inequality in counting form:
`#A^{2/3} ≤ 28 · basisBoundary d A` for `0 < #A ≤ d³/2`. -/
theorem basisBoundary_ge (A : Finset (Vertex d)) (hA : 0 < A.card)
    (hhalf : 2 * A.card ≤ d ^ 3) :
    (A.card : ℝ) ^ ((2 : ℝ) / 3) ≤ 28 * (basisBoundary d A : ℝ) := by
  obtain ⟨m, hmd, hm2, hm3, hm1⟩ := exists_cube_root d A.card hA hhalf
  have hbox := card_mul_le_box_sum d A m hmd
  -- `#A² ≤ m⁴ B` in ℕ
  have hnat : A.card * A.card ≤ m ^ 4 * basisBoundary d A := by
    have : A.card * A.card + A.card * A.card ≤ A.card * m ^ 3 := by
      calc A.card * A.card + A.card * A.card = A.card * (2 * A.card) := by ring
        _ ≤ A.card * m ^ 3 := Nat.mul_le_mul_left _ hm3
    omega
  -- pass to the reals
  set N : ℝ := (A.card : ℝ) with hNdef
  set B : ℝ := (basisBoundary d A : ℝ) with hBdef
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hNdef]; exact_mod_cast hA
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hnatR : N * N ≤ (m : ℝ) ^ 4 * B := by
    rw [hNdef, hBdef]; exact_mod_cast hnat
  have hm1R : ((m : ℝ) - 1) ^ 3 < 2 * N := by
    have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [← this, hNdef]; exact_mod_cast hm1
  have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  -- the real cube root `x = N^{1/3}`
  set x : ℝ := N ^ ((1 : ℝ) / 3) with hxdef
  have hx1 : 1 ≤ x := Real.one_le_rpow hN1 (by norm_num)
  have hx0 : 0 < x := by linarith
  have hx3 : x ^ 3 = N := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hx2 : N ^ ((2 : ℝ) / 3) = x ^ 2 := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  -- `m - 1 < 1.3 x`, hence `m < 2.3 x`
  have hmx : (m : ℝ) - 1 < 13 / 10 * x := by
    by_contra hcon
    push Not at hcon
    have h13 : (13 / 10 * x) ^ 3 ≤ ((m : ℝ) - 1) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hcon 3
    have : (13 / 10 * x) ^ 3 = 2197 / 1000 * x ^ 3 := by ring
    rw [this, hx3] at h13
    linarith
  have hm23 : (m : ℝ) < 23 / 10 * x := by linarith
  have hm4 : (m : ℝ) ^ 4 < (23 / 10 * x) ^ 4 :=
    pow_lt_pow_left₀ hm23 (by positivity) (by norm_num)
  have hm4' : (m : ℝ) ^ 4 ≤ 28 * x ^ 4 := by
    have : (23 / 10 * x) ^ 4 = 279841 / 10000 * x ^ 4 := by ring
    rw [this] at hm4
    have : 0 ≤ x ^ 4 := by positivity
    nlinarith
  -- conclude: `x⁶ = N² ≤ m⁴ B ≤ 28 x⁴ B`
  have hx6 : x ^ 6 ≤ 28 * x ^ 4 * B := by
    have : x ^ 6 = N * N := by rw [← hx3]; ring
    rw [this]
    calc N * N ≤ (m : ℝ) ^ 4 * B := hnatR
      _ ≤ 28 * x ^ 4 * B := mul_le_mul_of_nonneg_right hm4' hB0
  rw [hx2]
  have hx4 : 0 < x ^ 4 := by positivity
  have hx6' : x ^ 4 * x ^ 2 ≤ x ^ 4 * (28 * B) := by
    have : x ^ 6 = x ^ 4 * x ^ 2 := by ring
    rw [this] at hx6
    linarith
  exact le_of_mul_le_mul_left hx6' hx4

/-- **The coordinate-grid edge-isoperimetric inequality of the periodic torus**
(`lem:supp-periodic-screens`, slicing step): `h² #∂A ≥ (1/32) (h³ #A)^{2/3}` for
`0 < #A ≤ d³/2`, with the `d`-independent constant `c₀ = 1/32`. -/
theorem coordinateGridIsoperimetry : CoordinateGridIsoperimetry d (1 / 32) := by
  intro A hA hhalf
  have hm := mesh_pos d
  have hsplit : (mesh d ^ 3 * (A.card : ℝ)) ^ ((2 : ℝ) / 3) =
      mesh d ^ 2 * (A.card : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (mesh d) 3, ← Real.rpow_mul hm.le]
    norm_num
  rw [hsplit]
  have h28 := basisBoundary_ge d A hA hhalf
  have hm2 : 0 ≤ mesh d ^ 2 := by positivity
  calc 1 / 32 * (mesh d ^ 2 * (A.card : ℝ) ^ ((2 : ℝ) / 3))
      = mesh d ^ 2 * ((A.card : ℝ) ^ ((2 : ℝ) / 3) / 32) := by ring
    _ ≤ mesh d ^ 2 * (basisBoundary d A : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hm2
        linarith

/-- `lem:supp-periodic-screens`, unconditional: for every mesh `h = 1/d` and every
`a ∈ [a₋, a₊]`, the scaled periodic `A₃` graph satisfies (iii) the cut inequality
`h c_h(∂A) ≥ (1/(256 a₊)) μ_h(A)^{2/3}` for `0 < #A ≤ d³/2`, (i) the spectral floor
`poincareConstant a₋ a₊ (1/32)`, (ii) the Weyl count with `weylConstant a₋ a₊ (1/32)`,
and the compact-screen tail bound; all constants depend only on `a₋, a₊`. -/
theorem periodic_screens_unconditional (aminus aplus a : ℝ) (hminus : 0 < aminus)
    (ha : aminus ≤ a) (ha' : a ≤ aplus) :
    let hapos : 0 < a := lt_of_lt_of_le hminus ha
    let G := scaledGraph d a hapos
    (∀ A : Finset (Vertex d), 0 < A.card → 2 * A.card ≤ d ^ 3 →
      1 / (256 * aplus) * (∑ v ∈ A, G.mass v) ^ ((2 : ℝ) / 3) ≤
        mesh d * finiteCutCapacity G.conductance A) ∧
    (∀ j, 0 < G.eigenvalue j →
      poincareConstant aminus aplus (1 / 32) ≤ G.eigenvalue j) ∧
    (∀ R : ℝ, 0 < R →
      (finiteEigenvalueCount G.eigenvalue R : ℝ) ≤
        weylConstant aminus aplus (1 / 32) * (1 + R ^ ((3 : ℝ) / 2))) ∧
    (∀ (f : Vertex d → ℝ) (R : ℝ), 0 < R →
      ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
          G.spectralCoefficient f j ^ 2 ≤
        R⁻¹ * ∑ j, G.eigenvalue j * G.spectralCoefficient f j ^ 2) := by
  intro hapos G
  have h := periodic_screens d aminus aplus a (1 / 32) hminus ha ha' (by norm_num)
    (coordinateGridIsoperimetry d)
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, h2, h3, h4⟩
  intro A hA hhalf
  have := h1 A hA hhalf
  have heq : (1 : ℝ) / 32 / (8 * aplus) = 1 / (256 * aplus) := by
    field_simp; ring
  rwa [heq] at this

end RenewalGeometry.TorusCoordinateIsoperimetry
