/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.A3PeriodicGraphSamplingExact
import RenewalGeometry.DiscreteAnalysis.OperationalSobolevWeylFiniteGraph

/-!
# Uniform spatial screens for the periodic `A₃` graph
  (`lem:supp-periodic-screens`, emergent-spacetime supplement)

The periodic `A₃` graph `Λ/dΛ` (vertices `Fin 3 → ZMod d` in the root
basis, twelve root edges) with vertex mass `a³h³` and symmetric root rate
`a⁻²/(8h²)`, `h = 1/d`, is packaged as a `FiniteWeightedGraph`
(`scaledGraph`): every undirected root edge has conductance `a h / 8`
(`scaledMass_mul_rate`).

* `scaledConductance_symm`, `scaledDegree` — reversal symmetry of the
  twelve roots and the exact weighted degree `12 · a h / 8`;
* `cut_capacity_ge_basisBoundary` — the cut capacity dominates
  `(a h / 8)` times the number of boundary edges in the three basis-root
  directions (the paper's "retain only `±e₁, ±e₂, ±e₃`" step);
* `periodic_screens` — the manuscript's (i) spectral floor, (ii) Weyl
  count `≤ C_W (1 + R^{3/2})`, (iii) cut inequality
  `h c_h(∂A) ≥ c_cut μ_h(A)^{2/3}`, and the compact-screen tail bound, with
  constants depending only on `a₋, a₊` (uniform in `h` and in
  `a ∈ [a₋, a₊]`), **under the hypothesis** `CoordinateGridIsoperimetry d c₀`
  that the periodic coordinate grid `(ZMod d)³` obeys the discrete
  edge-isoperimetric inequality `h² #∂A ≥ c₀ (h³ #A)^{2/3}` for
  `0 < #A ≤ d³/2` (the Loomis–Whitney slicing step of the manuscript's
  proof of (iii), which is not formalised here).

The scaling `a ↦ (a³h³, a⁻²/(8h²))` is thereby discharged exactly: the
cut constant is `c₀/(8a₊)`, the degree constant `3/(2a₋²)` and the volume
bound `a₊³`.
-/

open Finset
open scoped BigOperators

namespace RenewalGeometry.A3PeriodicScreens

open A3PeriodicGraphSampling A3PeriodicSmoothEnergy FiniteRootGraphEnergy

noncomputable section

/-- Reversal involution `α ↦ -α` on the twelve roots, in the ordering of
`rootCoordinates`. -/
def reverse : Fin 12 → Fin 12 := ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8]

theorem reverse_involutive : Function.Involutive reverse := by
  intro r; fin_cases r <;> rfl

/-- The reversal as a permutation of the root alphabet. -/
def reverseEquiv : Equiv.Perm (Fin 12) := reverse_involutive.toPerm

theorem rootCoordinates_reverse (r : Fin 12) :
    rootCoordinates (reverse r) = -rootCoordinates r := by
  fin_cases r <;> (ext i; fin_cases i <;> rfl)

variable (d : ℕ) [NeZero d]

omit [NeZero d] in
theorem rootStep_reverse_iff (x y : Vertex d) (r : Fin 12) :
    rootStep d x r = y ↔ rootStep d y (reverse r) = x := by
  unfold rootStep LatticeGridSampling.step
  rw [rootCoordinates_reverse]
  simp only [funext_iff, Pi.neg_apply, Int.cast_neg]
  constructor
  · intro h i; rw [← h i]; ring
  · intro h i; rw [← h i]; ring

/-- Root-edge conductance at scale `a`: `(a/8) h` along every oriented
root (the paper's `c_{e,h} = m_h k_{α,h} = a h/8`). -/
def scaledConductance (a : ℝ) : Vertex d → Vertex d → ℝ :=
  rootConductance (rootStep d) (a / 8) (mesh d)

/-- Vertex mass at scale `a`: `m_h = a³ h³`. -/
def scaledMass (a : ℝ) : Vertex d → ℝ := fun _ => a ^ 3 * mesh d ^ 3

/-- Symmetric root rate at scale `a`: `k_{α,h} = a⁻² / (8h²)`. -/
def scaledRate (a : ℝ) : ℝ := a⁻¹ ^ 2 / (8 * mesh d ^ 2)

/-- Mass times one directed rate is the conductance `a h / 8`. -/
theorem scaledMass_mul_rate (a : ℝ) (ha : a ≠ 0) (v : Vertex d) :
    scaledMass d a v * scaledRate d a = a * mesh d / 8 := by
  unfold scaledMass scaledRate
  have hm := (mesh_pos d).ne'
  field_simp

omit [NeZero d] in
theorem scaledConductance_symm (a : ℝ) (x y : Vertex d) :
    scaledConductance d a x y = scaledConductance d a y x := by
  unfold scaledConductance rootConductance
  refine Fintype.sum_equiv reverseEquiv _ _ fun r => ?_
  refine if_congr ?_ rfl rfl
  show rootStep d x r = y ↔ rootStep d y (reverse r) = x
  exact rootStep_reverse_iff d x y r

theorem scaledConductance_nonneg (a : ℝ) (ha : 0 ≤ a) (x y : Vertex d) :
    0 ≤ scaledConductance d a x y :=
  rootConductance_nonneg _ _ _ (by positivity) (mesh_pos d).le x y

/-- Exact weighted degree: twelve roots of conductance `a h / 8`. -/
theorem scaledDegree (a : ℝ) (v : Vertex d) :
    ∑ u, scaledConductance d a u v = 12 * (a / 8 * mesh d) := by
  simp_rw [scaledConductance_symm d a _ v]
  unfold scaledConductance rootConductance
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

/-- The periodic `A₃` graph at scale `a` as a finite weighted graph. -/
def scaledGraph (a : ℝ) (ha : 0 < a) : FiniteWeightedGraph (Vertex d) where
  mass := scaledMass d a
  conductance := scaledConductance d a
  mass_pos := fun _ => by unfold scaledMass; have := mesh_pos d; positivity
  conductance_nonneg := scaledConductance_nonneg d a ha.le
  conductance_symm := scaledConductance_symm d a

/-- The six basis-root indices `±e₁, ±e₂, ±e₃` in the `rootCoordinates`
ordering. -/
def basisRoots : Finset (Fin 12) := {0, 3, 4, 7, 8, 11}

/-- Number of coordinate-direction boundary edges of `A` (each undirected
basis edge leaving `A` counted once, through its endpoint in `A`). -/
def basisBoundary (A : Finset (Vertex d)) : ℕ :=
  ∑ u ∈ A, (basisRoots.filter fun r => rootStep d u r ∉ A).card

/-- The discrete edge-isoperimetric inequality of the periodic coordinate
grid `(ZMod d)³` in physical units, `h² #∂A ≥ c₀ (h³ #A)^{2/3}` for
`0 < #A ≤ d³/2` (the Loomis–Whitney slicing input of the manuscript). -/
def CoordinateGridIsoperimetry (c₀ : ℝ) : Prop :=
  ∀ A : Finset (Vertex d), 0 < A.card → 2 * A.card ≤ d ^ 3 →
    c₀ * (mesh d ^ 3 * A.card) ^ ((2 : ℝ) / 3) ≤
      mesh d ^ 2 * (basisBoundary d A : ℝ)

/-- Retaining only the basis roots: the cut capacity dominates
`(a h / 8)` times the coordinate boundary count. -/
theorem cut_capacity_ge_basisBoundary (a : ℝ) (ha : 0 ≤ a)
    (A : Finset (Vertex d)) :
    a / 8 * mesh d * (basisBoundary d A : ℝ) ≤
      finiteCutCapacity (scaledConductance d a) A := by
  unfold finiteCutCapacity scaledConductance rootConductance basisBoundary
  have hκ : 0 ≤ a / 8 * mesh d := by
    have := mesh_pos d; positivity
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_compl]
  calc a / 8 * mesh d *
        ((basisRoots.filter fun r => rootStep d u r ∉ A).card : ℝ)
      = ∑ r ∈ basisRoots,
          (if rootStep d u r ∉ A then a / 8 * mesh d else 0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ r, (if rootStep d u r ∉ A then a / 8 * mesh d else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro r _ _
        split_ifs <;> linarith

theorem card_vertex : Fintype.card (Vertex d) = d ^ 3 := by
  simp [Vertex, ZMod.card]

omit [NeZero d] in
theorem mass_sum (a : ℝ) (A : Finset (Vertex d)) :
    ∑ v ∈ A, scaledMass d a v = A.card * (a ^ 3 * mesh d ^ 3) := by
  simp [scaledMass, Finset.sum_const, nsmul_eq_mul]

theorem volume_eq (a : ℝ) (ha : 0 < a) :
    (scaledGraph d a ha).volume = a ^ 3 := by
  unfold FiniteWeightedGraph.volume
  change ∑ v : Vertex d, scaledMass d a v = a ^ 3
  rw [mass_sum d a Finset.univ, Finset.card_univ, card_vertex, mesh,
    Nat.cast_pow]
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  field_simp

theorem finiteCutCapacity_compl (c : Vertex d → Vertex d → ℝ)
    (hsym : ∀ u v, c u v = c v u) (A : Finset (Vertex d)) :
    finiteCutCapacity c Aᶜ = finiteCutCapacity c A := by
  unfold finiteCutCapacity
  rw [compl_compl, Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hsym v u

/-- The scaled cut inequality for sets of at most half the vertices:
`h c_h(∂A) ≥ (c₀/(8a₊)) μ_h(A)^{2/3}`. -/
theorem cut_of_half (aminus aplus a c₀ : ℝ) (hminus : 0 < aminus)
    (ha : aminus ≤ a) (ha' : a ≤ aplus) (hc₀ : 0 < c₀)
    (hiso : CoordinateGridIsoperimetry d c₀)
    (A : Finset (Vertex d)) (hhalf : 2 * A.card ≤ d ^ 3) :
    c₀ / (8 * aplus) * (∑ v ∈ A, scaledMass d a v) ^ ((2 : ℝ) / 3) ≤
      mesh d * finiteCutCapacity (scaledConductance d a) A := by
  have hm := mesh_pos d
  have hapos : 0 < a := lt_of_lt_of_le hminus ha
  have hcap := cut_capacity_ge_basisBoundary d a hapos.le A
  have hcap0 : 0 ≤ finiteCutCapacity (scaledConductance d a) A := by
    refine le_trans ?_ hcap; positivity
  rcases Nat.eq_zero_or_pos A.card with hA | hA
  · rw [mass_sum, hA]
    simp only [Nat.cast_zero, zero_mul]
    rw [Real.zero_rpow (by norm_num), mul_zero]
    positivity
  have hiso' := hiso A hA hhalf
  rw [mass_sum]
  set X : ℝ := (mesh d ^ 3 * A.card) ^ ((2 : ℝ) / 3) with hX
  have hX0 : 0 ≤ X := by positivity
  have hsplit : ((A.card : ℝ) * (a ^ 3 * mesh d ^ 3)) ^ ((2 : ℝ) / 3) =
      a ^ 2 * X := by
    rw [hX, show (A.card : ℝ) * (a ^ 3 * mesh d ^ 3) =
      a ^ 3 * (mesh d ^ 3 * A.card) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast a 3, ← Real.rpow_mul hapos.le]
    norm_num
  rw [hsplit]
  have hB : 0 ≤ (basisBoundary d A : ℝ) := by positivity
  -- `(c₀/(8a₊)) a² X ≤ (a/8) c₀ X`
  have h1 : c₀ / (8 * aplus) * (a ^ 2 * X) ≤ a / 8 * (c₀ * X) := by
    have haplus : 0 < aplus := lt_of_lt_of_le hapos ha'
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : 0 ≤ c₀ * X * a := by positivity
    nlinarith [mul_le_mul_of_nonneg_left ha' this]
  calc c₀ / (8 * aplus) * (a ^ 2 * X) ≤ a / 8 * (c₀ * X) := h1
    _ ≤ a / 8 * (mesh d ^ 2 * (basisBoundary d A : ℝ)) :=
        mul_le_mul_of_nonneg_left hiso' (by positivity)
    _ = mesh d * (a / 8 * mesh d * (basisBoundary d A : ℝ)) := by ring
    _ ≤ mesh d * finiteCutCapacity (scaledConductance d a) A :=
        mul_le_mul_of_nonneg_left hcap hm.le

/-- The manuscript's cut inequality in the `min`-form consumed by the
finite Sobolev–Weyl theorems, valid for every vertex set. -/
theorem cut_min (aminus aplus a c₀ : ℝ) (hminus : 0 < aminus)
    (ha : aminus ≤ a) (ha' : a ≤ aplus) (hc₀ : 0 < c₀)
    (hiso : CoordinateGridIsoperimetry d c₀) (A : Finset (Vertex d)) :
    c₀ / (8 * aplus) *
        min (∑ v ∈ A, scaledMass d a v) (∑ v ∈ Aᶜ, scaledMass d a v) ^
          ((2 : ℝ) / 3) ≤
      mesh d * finiteCutCapacity (scaledConductance d a) A := by
  have hapos : 0 < a := lt_of_lt_of_le hminus ha
  have hI : 0 < c₀ / (8 * aplus) := by
    have : 0 < aplus := lt_of_lt_of_le hapos ha'
    positivity
  have hmassA : 0 ≤ ∑ v ∈ A, scaledMass d a v := by
    rw [mass_sum]; have := mesh_pos d; positivity
  have hmassAc : 0 ≤ ∑ v ∈ Aᶜ, scaledMass d a v := by
    rw [mass_sum]; have := mesh_pos d; positivity
  by_cases hhalf : 2 * A.card ≤ d ^ 3
  · refine le_trans ?_ (cut_of_half d aminus aplus a c₀ hminus ha ha' hc₀
      hiso A hhalf)
    apply mul_le_mul_of_nonneg_left _ hI.le
    exact Real.rpow_le_rpow (le_min hmassA hmassAc) (min_le_left _ _)
      (by norm_num)
  · have hcard : A.card + Aᶜ.card = d ^ 3 := by
      rw [Finset.card_compl, card_vertex]
      have := Finset.card_le_univ A
      rw [card_vertex] at this
      omega
    have hhalf' : 2 * Aᶜ.card ≤ d ^ 3 := by omega
    have := cut_of_half d aminus aplus a c₀ hminus ha ha' hc₀ hiso Aᶜ hhalf'
    rw [finiteCutCapacity_compl d _ (scaledConductance_symm d a)] at this
    refine le_trans ?_ this
    apply mul_le_mul_of_nonneg_left _ hI.le
    exact Real.rpow_le_rpow (le_min hmassA hmassAc) (min_le_right _ _)
      (by norm_num)

/-- The `h²`-degree bound with constant `3/(2a₋²)`. -/
theorem degree_bound (aminus a : ℝ) (hminus : 0 < aminus) (ha : aminus ≤ a)
    (v : Vertex d) :
    mesh d ^ 2 * (∑ u, scaledConductance d a u v) ≤
      3 / (2 * aminus ^ 2) * scaledMass d a v := by
  rw [scaledDegree]
  unfold scaledMass
  have hm := mesh_pos d
  have hapos : 0 < a := lt_of_lt_of_le hminus ha
  have key : mesh d ^ 2 * (12 * (a / 8 * mesh d)) = 3 / 2 * a * mesh d ^ 3 := by
    ring
  rw [key]
  have h2 : aminus ^ 2 ≤ a ^ 2 := by nlinarith
  have hfrac : 1 ≤ a ^ 2 / aminus ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc 3 / 2 * a * mesh d ^ 3 = 3 / 2 * a * mesh d ^ 3 * 1 := by ring
    _ ≤ 3 / 2 * a * mesh d ^ 3 * (a ^ 2 / aminus ^ 2) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = 3 / (2 * aminus ^ 2) * (a ^ 3 * mesh d ^ 3) := by
        field_simp

/-- Poincaré constant `c_P = I²/(128 D V*^{2/3})` with
`I = c₀/(8a₊)`, `D = 3/(2a₋²)`, `V* = a₊³`. -/
def poincareConstant (aminus aplus c₀ : ℝ) : ℝ :=
  (c₀ / (8 * aplus)) ^ 2 /
    (128 * (3 / (2 * aminus ^ 2)) * (aplus ^ 3) ^ ((2 : ℝ) / 3))

/-- Weyl constant `C_W = 1 + 4 e^{3/2} V* (128 D / I²)^{3/2}`. -/
def weylConstant (aminus aplus c₀ : ℝ) : ℝ :=
  1 + 4 * Real.exp (3 / 2) * aplus ^ 3 *
    (128 * (3 / (2 * aminus ^ 2)) / (c₀ / (8 * aplus)) ^ 2) ^ ((3 : ℝ) / 2)

/-- `lem:supp-periodic-screens`, conditional on the coordinate-grid
isoperimetric inequality: for `a ∈ [a₋, a₊]` the scaled periodic `A₃`
graph satisfies (iii) the cut inequality with `c_cut = c₀/(8a₊)`,
(i) the spectral floor `c_P`, (ii) the Weyl count
`N_h(R) ≤ C_W (1 + R^{3/2})`, and the compact-screen tail bound
`‖(I - P_R) f‖² ≤ R⁻¹ 𝓔(f)` (in spectral coefficients), with all constants
depending only on `a₋, a₊, c₀`. -/
theorem periodic_screens (aminus aplus a c₀ : ℝ) (hminus : 0 < aminus)
    (ha : aminus ≤ a) (ha' : a ≤ aplus) (hc₀ : 0 < c₀)
    (hiso : CoordinateGridIsoperimetry d c₀) :
    let hapos : 0 < a := lt_of_lt_of_le hminus ha
    let G := scaledGraph d a hapos
    -- (iii) cut inequality
    (∀ A : Finset (Vertex d), 0 < A.card → 2 * A.card ≤ d ^ 3 →
      c₀ / (8 * aplus) * (∑ v ∈ A, G.mass v) ^ ((2 : ℝ) / 3) ≤
        mesh d * finiteCutCapacity G.conductance A) ∧
    -- (i) spectral floor
    (∀ j, 0 < G.eigenvalue j →
      poincareConstant aminus aplus c₀ ≤ G.eigenvalue j) ∧
    -- (ii) Weyl count
    (∀ R : ℝ, 0 < R →
      (finiteEigenvalueCount G.eigenvalue R : ℝ) ≤
        weylConstant aminus aplus c₀ * (1 + R ^ ((3 : ℝ) / 2))) ∧
    -- compact-screen tail
    (∀ (f : Vertex d → ℝ) (R : ℝ), 0 < R →
      ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
          G.spectralCoefficient f j ^ 2 ≤
        R⁻¹ * ∑ j, G.eigenvalue j * G.spectralCoefficient f j ^ 2) := by
  intro hapos G
  have haplus : 0 < aplus := lt_of_lt_of_le hapos ha'
  have hI : 0 < c₀ / (8 * aplus) := by positivity
  have hD : 0 < 3 / (2 * aminus ^ 2) := by positivity
  have hV : 0 < aplus ^ 3 := by positivity
  have hvol : G.volume ≤ aplus ^ 3 := by
    rw [volume_eq]
    exact pow_le_pow_left₀ hapos.le ha' 3
  have hdeg : ∀ v, mesh d ^ 2 * (∑ u, G.conductance u v) ≤
      3 / (2 * aminus ^ 2) * G.mass v :=
    fun v => degree_bound d aminus a hminus ha v
  have hcut : ∀ A : Finset (Vertex d),
      c₀ / (8 * aplus) *
        min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
      mesh d * finiteCutCapacity G.conductance A :=
    fun A => cut_min d aminus aplus a c₀ hminus ha ha' hc₀ hiso A
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A _ hhalf
    exact cut_of_half d aminus aplus a c₀ hminus ha ha' hc₀ hiso A hhalf
  · intro j hj
    have := G.positiveEigenvalue_floor (c₀ / (8 * aplus))
      (3 / (2 * aminus ^ 2)) (mesh d) (aplus ^ 3) hI hD (mesh_pos d) hV
      hvol hdeg hcut j hj
    exact this
  · intro R hR
    have hcount := G.eigenvalueCount_bound (c₀ / (8 * aplus))
      (3 / (2 * aminus ^ 2)) (mesh d) (aplus ^ 3) R hI hD.le (mesh_pos d)
      hV.le hvol hR hdeg hcut
    refine le_trans hcount ?_
    unfold weylConstant
    set K : ℝ := 4 * Real.exp (3 / 2) * aplus ^ 3 *
      (128 * (3 / (2 * aminus ^ 2)) / (c₀ / (8 * aplus)) ^ 2) ^
        ((3 : ℝ) / 2) with hK
    have hK0 : 0 ≤ K := by positivity
    have hR32 : 0 ≤ R ^ ((3 : ℝ) / 2) := by positivity
    have hsplit : (128 * (3 / (2 * aminus ^ 2)) / (c₀ / (8 * aplus)) ^ 2 * R) ^
        ((3 : ℝ) / 2) =
        (128 * (3 / (2 * aminus ^ 2)) / (c₀ / (8 * aplus)) ^ 2) ^
          ((3 : ℝ) / 2) * R ^ ((3 : ℝ) / 2) :=
      Real.mul_rpow (by positivity) hR.le
    rw [hsplit]
    nlinarith
  · intro f R hR
    exact G.eigenfunction_spectralTail_bound f R hR

end

end RenewalGeometry.A3PeriodicScreens
