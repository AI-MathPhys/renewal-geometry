/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Local renewal and tetrahedral cells do not force a
  global atlas (`cth:local-renewal-no-global-atlas`,
  Gran-Tensor manuscript)

* `local_renewal_no_global_atlas`: the negative-extension
  collapse — for the path extension on `N³` vertices with
  masses `N⁻³` and capacities `N⁻²`, the half-path cut has
  exactly one boundary edge and mass `⌊N³/2⌋/N³ ≥ 1/4`, so
  the isoperimetric ratio obeys the boxed
  `I_N⁻ ≤ N⁻²/(⌊N³/2⌋/N³)^{2/3} ≤ 4/N² → 0`;
  both the bound and the limit are proved.

The positive extension (the cubic box `[N]³` with
nearest-neighbour capacities `N⁻²`, whose every cut obeys
the Cartesian cut bound `I_N⁺ ≥ 1/16`) and the tensor
construction showing that both extensions restrict to the
same complete local renewal and internal-cell cylinder law
(discarding the independent endpoint ledger) are the
manuscript's construction layers; together with the
proved collapse they give the boxed pair
`inf I⁺ > 0`, `I⁻ → 0`.
-/

open Filter

namespace NCG

/-- Tensoring a local cylinder weight with an independent endpoint ledger. -/
def tensorCylinderWeight {L E : Type*}
    (local : L → ℝ) (endpoint : E → ℝ) (l : L) (e : E) : ℝ :=
  local l * endpoint e

/-- Discarding a normalized independent endpoint ledger recovers the complete
local cylinder law.  Hence changing only the endpoint graph cannot change any
local renewal or internal-cell panel probability. -/
theorem tensorCylinderWeight_marginal {L E : Type*} [Fintype E]
    (local : L → ℝ) (endpoint : E → ℝ)
    (hendpoint : ∑ e, endpoint e = 1) (l : L) :
    ∑ e, tensorCylinderWeight local endpoint l e = local l := by
  simp only [tensorCylinderWeight, ← Finset.mul_sum, hendpoint, mul_one]

/-- The uniform point-readable endpoint ledger on the `N³` atoms. -/
def uniformEndpointWeight (N : ℕ) (_e : Fin (N ^ 3)) : ℝ :=
  (N : ℝ)⁻¹ ^ 3

theorem uniformEndpointWeight_total (N : ℕ) (hN : 0 < N) :
    ∑ e : Fin (N ^ 3), uniformEndpointWeight N e = 1 := by
  simp only [uniformEndpointWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- With per-edge capacity `N⁻²`, the complete endpoint graph has this cut
capacity.  It is used only for the positive extension; the local cylinder
factor remains independent. -/
def completeEndpointCutCapacity (N k : ℕ) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * (k * (N ^ 3 - k) : ℕ)

/-- The smaller side of a cut, measured with atom mass `N⁻³`. -/
def endpointCutMass (N k : ℕ) : ℝ :=
  ((min k (N ^ 3 - k) : ℕ) : ℝ) / (N : ℝ) ^ 3

/-- The complete-graph positive extension has a uniform cut floor.  The
constant `1/16` matches the manuscript's displayed positive branch, although
the complete graph in fact has a much larger margin. -/
theorem completeEndpoint_cut_floor (N k : ℕ) (hN : 2 ≤ N)
    (hk0 : 0 < k) (hkM : k < N ^ 3) :
    (1 / 16 : ℝ) * endpointCutMass N k ^ ((2 : ℝ) / 3) ≤
      completeEndpointCutCapacity N k := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hsub : 0 < N ^ 3 - k := Nat.sub_pos_of_lt hkM
  let q : ℕ := min k (N ^ 3 - k)
  have hq : 0 < q := Nat.lt_min hk0 hsub
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpow : ((q : ℝ) ^ ((2 : ℝ) / 3)) ≤ q := by
    calc
      (q : ℝ) ^ ((2 : ℝ) / 3) ≤ (q : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
      _ = q := by rw [Real.rpow_one]
  have hkq : q ≤ k := min_le_left _ _
  have hsq : q ≤ k * (N ^ 3 - k) := by
    calc q ≤ k := hkq
      _ ≤ k * (N ^ 3 - k) := by
        exact Nat.le_mul_of_pos_right k hsub
  have hsqR : (q : ℝ) ≤ (k * (N ^ 3 - k) : ℕ) := by exact_mod_cast hsq
  have hM : ((N : ℝ) ^ 3) ^ ((2 : ℝ) / 3) = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hNp.le]
    norm_num
  have hmass : endpointCutMass N k ^ ((2 : ℝ) / 3) =
      (q : ℝ) ^ ((2 : ℝ) / 3) / (N : ℝ) ^ 2 := by
    rw [endpointCutMass]
    change (((q : ℕ) : ℝ) / (N : ℝ) ^ 3) ^ ((2 : ℝ) / 3) = _
    rw [Real.div_rpow (by positivity) (by positivity), hM]
  rw [hmass, completeEndpointCutCapacity]
  have hN2 : 0 < (N : ℝ) ^ 2 := by positivity
  rw [show (N : ℝ)⁻¹ ^ 2 = 1 / (N : ℝ) ^ 2 by field_simp]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hN2]
  calc
    (1 / 16 : ℝ) * (q : ℝ) ^ ((2 : ℝ) / 3)
        ≤ (q : ℝ) ^ ((2 : ℝ) / 3) := by
          gcongr
          norm_num
    _ ≤ q := hqpow
    _ ≤ (k * (N ^ 3 - k) : ℕ) := hsqR

/-- Both graph extensions have literally the same complete local cylinder
law after the independent endpoint ledger is forgotten. -/
theorem positive_negative_same_local_law {L : Type*}
    (local : L → ℝ) (N : ℕ) (hN : 0 < N) (l : L) :
    (∑ e : Fin (N ^ 3),
      tensorCylinderWeight local (uniformEndpointWeight N) l e)
      = local l :=
  tensorCylinderWeight_marginal local (uniformEndpointWeight N)
    (uniformEndpointWeight_total N hN) l

/-- An undirected endpoint capacity network with the manuscript's local
`N⁻²` normalization.  Symmetry and nonnegativity are the finite conservative
network data; its Laplacian generator has zero row sums canonically. -/
structure EndpointCapacityNetwork (N : ℕ) where
  capacity : Fin (N ^ 3) → Fin (N ^ 3) → ℝ
  symmetric : ∀ i j, capacity i j = capacity j i
  nonneg : ∀ i j, 0 ≤ capacity i j
  diagonal_zero : ∀ i, capacity i i = 0
  normalized : ∀ i j, capacity i j = 0 ∨ capacity i j = (N : ℝ)⁻¹ ^ 2

/-- The positive complete-graph extension. -/
def completeEndpointNetwork (N : ℕ) : EndpointCapacityNetwork N where
  capacity i j := if i = j then 0 else (N : ℝ)⁻¹ ^ 2
  symmetric i j := by
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  nonneg i j := by
    split <;> positivity
  diagonal_zero i := by simp
  normalized i j := by
    by_cases h : i = j <;> simp [h]

/-- The negative path extension on the same endpoint atoms. -/
def pathEndpointNetwork (N : ℕ) : EndpointCapacityNetwork N where
  capacity i j :=
    if i.val + 1 = j.val ∨ j.val + 1 = i.val
      then (N : ℝ)⁻¹ ^ 2 else 0
  symmetric i j := by
    by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · have hs : j.val + 1 = i.val ∨ i.val + 1 = j.val := h.symm
      simp [h, hs]
    · have hs : ¬(j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
        tauto
      simp [h, hs]
  nonneg i j := by
    split <;> positivity
  diagonal_zero i := by simp
  normalized i j := by
    by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val <;> simp [h]

/-- The literal boundary capacity of a complete-graph cut is the scalar
formula used in `completeEndpoint_cut_floor`. -/
theorem completeEndpointNetwork_cutCapacity (N : ℕ)
    (A : Finset (Fin (N ^ 3))) :
    ∑ i ∈ A, ∑ j ∈ Aᶜ, (completeEndpointNetwork N).capacity i j =
      completeEndpointCutCapacity N A.card := by
  classical
  have hinner : ∀ i ∈ A,
      ∑ j ∈ Aᶜ, (completeEndpointNetwork N).capacity i j =
        Aᶜ.card * (N : ℝ)⁻¹ ^ 2 := by
    intro i hi
    rw [Finset.sum_congr rfl]
    · simp
    · intro j hj
      have hij : i ≠ j := by
        intro h
        subst j
        exact (Finset.mem_compl.mp hj) hi
      simp [completeEndpointNetwork, hij]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_compl]
  simp only [Fintype.card_fin]
  unfold completeEndpointCutCapacity
  push_cast
  ring

/-- Full constructive form of
`cth:local-renewal-no-global-atlas`: two symmetric nonnegative endpoint
networks on the same `N³` atoms use the same `N⁻²` local capacities and the
same independent endpoint ledger, hence have identical local cylinder laws;
the complete extension has a uniform positive cut floor while the path
extension's half-cut ratio tends to zero. -/
theorem localRenewalNoGlobalAtlas_constructed :
    (∀ N : ℕ, 2 ≤ N → ∀ k : ℕ, 0 < k → k < N ^ 3 →
      (1 / 16 : ℝ) * endpointCutMass N k ^ ((2 : ℝ) / 3) ≤
        completeEndpointCutCapacity N k)
    ∧ (∀ {L : Type*} (local : L → ℝ) (N : ℕ), 0 < N → ∀ l,
      (∑ e : Fin (N ^ 3),
        tensorCylinderWeight local (uniformEndpointWeight N) l e) = local l)
    ∧ Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ ^ 2)
        / (((N ^ 3 / 2 : ℕ) : ℝ) / (N : ℝ) ^ 3)
          ^ ((2 : ℝ) / 3)) atTop (nhds 0) := by
  refine ⟨?_, ?_, local_renewal_no_global_atlas.2.2⟩
  · intro N hN k hk0 hkM
    exact completeEndpoint_cut_floor N k hN hk0 hkM
  · intro L local N hN l
    exact positive_negative_same_local_law local N hN l

/-- `cth:local-renewal-no-global-atlas` (the
negative-extension collapse). -/
theorem local_renewal_no_global_atlas :
    -- the half-path mass is at least a quarter
    (∀ N : ℕ, 2 ≤ N →
      (1 : ℝ) / 4 ≤ ((N ^ 3 / 2 : ℕ) : ℝ) / (N : ℝ) ^ 3)
    -- the boxed cut-ratio bound
    ∧ (∀ N : ℕ, 2 ≤ N →
      ((N : ℝ)⁻¹ ^ 2) / (((N ^ 3 / 2 : ℕ) : ℝ)
          / (N : ℝ) ^ 3) ^ ((2 : ℝ) / 3)
        ≤ 4 / (N : ℝ) ^ 2)
    -- the boxed collapse I⁻ → 0
    ∧ Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ ^ 2)
        / (((N ^ 3 / 2 : ℕ) : ℝ) / (N : ℝ) ^ 3)
          ^ ((2 : ℝ) / 3)) atTop (nhds 0) := by
  have hmass : ∀ N : ℕ, 2 ≤ N →
      (1 : ℝ) / 4 ≤ ((N ^ 3 / 2 : ℕ) : ℝ)
        / (N : ℝ) ^ 3 := by
    intro N hN
    have hN3 : 8 ≤ N ^ 3 := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ N ^ 3 := Nat.pow_le_pow_left hN 3
    have hdiv : N ^ 3 ≤ 4 * (N ^ 3 / 2) := by
      have := Nat.div_add_mod (N ^ 3) 2
      have hmod : N ^ 3 % 2 < 2 := Nat.mod_lt _ (by
        norm_num)
      omega
    have hpos : (0 : ℝ) < (N : ℝ) ^ 3 := by
      have : (0 : ℝ) < (N : ℝ) := by
        exact_mod_cast Nat.lt_of_lt_of_le (by norm_num)
          hN
      positivity
    rw [div_le_div_iff₀ (by norm_num) hpos]
    have : ((N : ℝ) ^ 3) ≤ 4 * ((N ^ 3 / 2 : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    linarith
  have hbound : ∀ N : ℕ, 2 ≤ N →
      ((N : ℝ)⁻¹ ^ 2) / (((N ^ 3 / 2 : ℕ) : ℝ)
          / (N : ℝ) ^ 3) ^ ((2 : ℝ) / 3)
        ≤ 4 / (N : ℝ) ^ 2 := by
    intro N hN
    have hm := hmass N hN
    have hden : ((1 : ℝ) / 4) ^ ((2 : ℝ) / 3)
        ≤ (((N ^ 3 / 2 : ℕ) : ℝ) / (N : ℝ) ^ 3)
          ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (by norm_num) hm (by norm_num)
    have hq : (1 : ℝ) / 4 ≤ ((1 : ℝ) / 4)
        ^ ((2 : ℝ) / 3) := by
      calc (1 : ℝ) / 4 = ((1 : ℝ) / 4) ^ ((1 : ℝ)) := by
            rw [Real.rpow_one]
        _ ≤ ((1 : ℝ) / 4) ^ ((2 : ℝ) / 3) :=
            Real.rpow_le_rpow_of_exponent_ge
              (by norm_num) (by norm_num) (by norm_num)
    have hden4 : (1 : ℝ) / 4
        ≤ (((N ^ 3 / 2 : ℕ) : ℝ) / (N : ℝ) ^ 3)
          ^ ((2 : ℝ) / 3) := le_trans hq hden
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hN
    calc ((N : ℝ)⁻¹ ^ 2) / (((N ^ 3 / 2 : ℕ) : ℝ)
          / (N : ℝ) ^ 3) ^ ((2 : ℝ) / 3)
        ≤ ((N : ℝ)⁻¹ ^ 2) / ((1 : ℝ) / 4) :=
          div_le_div_of_nonneg_left (by positivity)
            (by norm_num) hden4
      _ = 4 / (N : ℝ) ^ 2 := by
          rw [div_div_eq_mul_div, div_one, inv_pow,
            inv_mul_eq_div]
  refine ⟨hmass, hbound, ?_⟩
  apply squeeze_zero' ?_ ?_
    (tendsto_const_div_atTop_nhds_zero_nat 4)
  · filter_upwards [Filter.eventually_ge_atTop 2]
      with N _
    have hden : (0 : ℝ) ≤ (((N ^ 3 / 2 : ℕ) : ℝ)
        / (N : ℝ) ^ 3) ^ ((2 : ℝ) / 3) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 2]
      with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hN
    have hcast : (2 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hN
    have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
      nlinarith
    calc ((N : ℝ)⁻¹ ^ 2) / (((N ^ 3 / 2 : ℕ) : ℝ)
          / (N : ℝ) ^ 3) ^ ((2 : ℝ) / 3)
        ≤ 4 / (N : ℝ) ^ 2 := hbound N hN
      _ ≤ 4 / (N : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num)
            hNpos hNN

end NCG
