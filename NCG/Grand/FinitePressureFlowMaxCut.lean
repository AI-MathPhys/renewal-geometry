/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FlowDuality

/-!
# Finite pressure transshipment: the max-cut converse

The key missing ingredient in `thm:pressure-flow-isoperimetry` is finite
coarea.  We encode a potential as a nonnegative combination of nested
superlevel cuts.  Both the potential and every pairwise absolute difference
then have exact layer-cake expansions.  This is the finite LP-duality
certificate used by the pressure transshipment converse.
-/

open scoped BigOperators

noncomputable section

namespace NCG

/-- Indicator of a finite vertex cut, as a real-valued potential. -/
def cutIndicator {V : Type*} [DecidableEq V] (A : Finset V) (v : V) : ℝ :=
  if v ∈ A then 1 else 0

/-- A finite layer-cake representation.  The second identity is the exact
coarea identity pointwise on each ordered pair. -/
structure FiniteCutLayerCake {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → ℝ) where
  coeff : Finset V → ℝ
  coeff_nonneg : ∀ A, 0 ≤ coeff A
  expansion : ∀ v, g v = ∑ A, coeff A * cutIndicator A v
  pair_expansion : ∀ u v,
    |g u - g v| = ∑ A, coeff A * |cutIndicator A u - cutIndicator A v|

/-- Every nonnegative potential on a finite carrier has an exact superlevel
cut layer-cake representation. -/
theorem finite_nonnegative_cut_layerCake
    {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → ℝ) (hg : ∀ v, 0 ≤ g v) :
    Nonempty (FiniteCutLayerCake g) := by
  classical
  let supp (f : V → ℝ) : Finset V := Finset.univ.filter fun v => 0 < f v
  have aux : ∀ n : ℕ, ∀ f : V → ℝ, (∀ v, 0 ≤ f v) →
      (supp f).card = n → Nonempty (FiniteCutLayerCake f) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf hn
      by_cases hS : (supp f).Nonempty
      · obtain ⟨v₀, hv₀S, hv₀min⟩ :=
          Finset.exists_min_image (supp f) f hS
        let δ := f v₀
        have hδ : 0 < δ := by
          exact (Finset.mem_filter.mp hv₀S).2
        let f' : V → ℝ := fun v =>
          if v ∈ supp f then f v - δ else 0
        have hf' : ∀ v, 0 ≤ f' v := by
          intro v
          simp only [f']
          split_ifs with hv
          · exact sub_nonneg.mpr (hv₀min v hv)
          · exact le_rfl
        have hsupp' : supp f' ⊂ supp f := by
          apply Finset.ssubset_iff_subset_ne.mpr
          constructor
          · intro v hv
            have hvpos := (Finset.mem_filter.mp hv).2
            by_contra hvS
            simp [f', hvS] at hvpos
          · intro heq
            have hv₀' : v₀ ∈ supp f' := heq.symm ▸ hv₀S
            have hvpos := (Finset.mem_filter.mp hv₀').2
            simp [f', hv₀S, δ] at hvpos
        have hcard' : (supp f').card < n := by
          rw [← hn]
          exact Finset.card_lt_card hsupp'
        obtain ⟨L⟩ := ih (supp f').card hcard' f' hf' rfl
        let c : Finset V → ℝ := fun A =>
          L.coeff A + if A = supp f then δ else 0
        have hc : ∀ A, 0 ≤ c A := by
          intro A
          exact add_nonneg (L.coeff_nonneg A) (by split_ifs <;> positivity)
        have hsum_indicator (v : V) :
            (∑ A, (if A = supp f then δ else 0) * cutIndicator A v) =
              δ * cutIndicator (supp f) v := by
          classical
          simp
        have hf_split (v : V) :
            f v = f' v + δ * cutIndicator (supp f) v := by
          simp only [f', cutIndicator]
          by_cases hv : v ∈ supp f
          · simp [hv]
          · have hz : f v = 0 := by
              have hnpos : ¬0 < f v := by
                intro hp
                exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
              exact le_antisymm (le_of_not_gt hnpos) (hf v)
            simp [hv, hz]
        have hpair_split (u v : V) :
            |f u - f v| = |f' u - f' v| +
              δ * |cutIndicator (supp f) u - cutIndicator (supp f) v| := by
          by_cases hu : u ∈ supp f <;> by_cases hv : v ∈ supp f
          · have huδ : δ ≤ f u := hv₀min u hu
            have hvδ : δ ≤ f v := hv₀min v hv
            simp [f', cutIndicator, hu, hv]
          · have hv0 : f v = 0 := by
              have hnpos : ¬0 < f v := by
                intro hp
                exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
              exact le_antisymm (le_of_not_gt hnpos) (hf v)
            have huδ : δ ≤ f u := hv₀min u hu
            simp [f', cutIndicator, hu, hv, hv0, abs_of_nonneg (hf u),
              abs_of_nonneg (sub_nonneg.mpr huδ), hδ.le]
          · have hu0 : f u = 0 := by
              have hnpos : ¬0 < f u := by
                intro hp
                exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
              exact le_antisymm (le_of_not_gt hnpos) (hf u)
            have hvδ : δ ≤ f v := hv₀min v hv
            have habs : |δ - f v| = f v - δ :=
              abs_of_nonpos (sub_nonpos.mpr hvδ) |>.trans (by ring)
            simp [f', cutIndicator, hu, hv, hu0, abs_of_nonneg (hf v), habs]
          · have hu0 : f u = 0 := by
              have hnpos : ¬0 < f u := by
                intro hp
                exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
              exact le_antisymm (le_of_not_gt hnpos) (hf u)
            have hv0 : f v = 0 := by
              have hnpos : ¬0 < f v := by
                intro hp
                exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
              exact le_antisymm (le_of_not_gt hnpos) (hf v)
            simp [f', cutIndicator, hu, hv, hu0, hv0]
        refine ⟨{
          coeff := c
          coeff_nonneg := hc
          expansion := fun v => ?_
          pair_expansion := fun u v => ?_ }⟩
        · rw [hf_split v, L.expansion v]
          simp only [c, add_mul, Finset.sum_add_distrib]
          rw [hsum_indicator]
        · rw [hpair_split u v, L.pair_expansion u v]
          simp only [c, add_mul, Finset.sum_add_distrib]
          rw [show (∑ A, (if A = supp f then δ else 0) *
            |cutIndicator A u - cutIndicator A v|) =
              δ * |cutIndicator (supp f) u - cutIndicator (supp f) v| by simp]
      · have hf0 : ∀ v, f v = 0 := by
          intro v
          have hnpos : ¬0 < f v := by
            intro hv
            exact hS ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
          exact le_antisymm (le_of_not_gt hnpos) (hf v)
        refine ⟨{
          coeff := fun _ => 0
          coeff_nonneg := fun _ => le_rfl
          expansion := fun v => by simp [hf0 v]
          pair_expansion := fun u v => by simp [hf0 u, hf0 v] }⟩
  exact aux (supp g).card g hg rfl

/-- Every finite real potential is a constant plus a nonnegative cut
layer-cake; constants disappear against centered demands and pairwise
differences. -/
theorem finite_potential_cut_layerCake
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (φ : V → ℝ) :
    ∃ base : ℝ, ∃ L : FiniteCutLayerCake (fun v => φ v - base), True := by
  classical
  obtain ⟨v₀, _, hv₀⟩ :=
    Finset.exists_min_image (Finset.univ : Finset V) φ Finset.univ_nonempty
  let base := φ v₀
  have hnonneg : ∀ v, 0 ≤ φ v - base := fun v =>
    sub_nonneg.mpr (hv₀ v (Finset.mem_univ v))
  obtain ⟨L⟩ := finite_nonnegative_cut_layerCake (fun v => φ v - base) hnonneg
  exact ⟨base, L, trivial⟩

/-- Ordered cut capacity. -/
def finiteCutCapacity {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (A : Finset V) : ℝ :=
  ∑ u ∈ A, ∑ v ∈ Aᶜ, c u v

/-- The total variation of a cut indicator is twice its cut capacity. -/
theorem cutIndicator_weightedVariation
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hsym : ∀ u v, c u v = c v u)
    (A : Finset V) :
    (∑ u, ∑ v, c u v * |cutIndicator A u - cutIndicator A v|) =
      2 * finiteCutCapacity c A := by
  classical
  have hcross :
      (∑ u, ∑ v, c u v * |cutIndicator A u - cutIndicator A v|) =
        (∑ u ∈ A, ∑ v ∈ Aᶜ, c u v) +
        (∑ u ∈ Aᶜ, ∑ v ∈ A, c u v) := by
    calc
      (∑ u, ∑ v, c u v * |cutIndicator A u - cutIndicator A v|)
          = ∑ u ∈ A, ∑ v, c u v * |cutIndicator A u - cutIndicator A v| +
            ∑ u ∈ Aᶜ, ∑ v, c u v * |cutIndicator A u - cutIndicator A v| := by
              rw [← Finset.sum_add_sum_compl A]
      _ = (∑ u ∈ A, ∑ v ∈ Aᶜ, c u v) +
            (∑ u ∈ Aᶜ, ∑ v ∈ A, c u v) := by
              apply congrArg₂ (· + ·)
              · apply Finset.sum_congr rfl
                intro u hu
                rw [← Finset.sum_add_sum_compl A]
                have hzero : (∑ x ∈ A, c u x *
                    |cutIndicator A u - cutIndicator A x|) = 0 := by
                  apply Finset.sum_eq_zero
                  intro x hx
                  simp [cutIndicator, hu, hx]
                rw [hzero, zero_add]
                apply Finset.sum_congr rfl
                intro x hxAc
                have hx : x ∉ A := Finset.mem_compl.mp hxAc
                simp [cutIndicator, hu, hx]
              · apply Finset.sum_congr rfl
                intro u huAc
                have hu : u ∉ A := Finset.mem_compl.mp huAc
                rw [← Finset.sum_add_sum_compl A]
                have hzero : (∑ x ∈ Aᶜ, c u x *
                    |cutIndicator A u - cutIndicator A x|) = 0 := by
                  apply Finset.sum_eq_zero
                  intro x hxAc
                  have hx : x ∉ A := Finset.mem_compl.mp hxAc
                  simp [cutIndicator, hu, hx]
                rw [hzero, add_zero]
                apply Finset.sum_congr rfl
                intro x hx
                simp [cutIndicator, hu, hx]
  rw [hcross]
  have hswap : (∑ u ∈ Aᶜ, ∑ v ∈ A, c u v) =
      ∑ u ∈ A, ∑ v ∈ Aᶜ, c u v := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun v _ => hsym v u
  rw [hswap]
  unfold finiteCutCapacity
  ring

/-- Coarea for one selected layer-cake decomposition. -/
theorem cutLayerCake_weightedVariation
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hsym : ∀ u v, c u v = c v u)
    (φ : V → ℝ) (base : ℝ)
    (L : FiniteCutLayerCake (fun v => φ v - base)) :
    (∑ u, ∑ v, c u v * |φ u - φ v|) =
      2 * ∑ A, L.coeff A * finiteCutCapacity c A := by
  have hdiff (u v : V) :
      |φ u - φ v| = ∑ A, L.coeff A *
        |cutIndicator A u - cutIndicator A v| := by
    simpa only [sub_sub_sub_cancel_right] using L.pair_expansion u v
  calc
    (∑ u, ∑ v, c u v * |φ u - φ v|)
        = ∑ A, L.coeff A *
            (∑ u, ∑ v, c u v *
              |cutIndicator A u - cutIndicator A v|) := by
          calc
            (∑ u, ∑ v, c u v * |φ u - φ v|)
                = ∑ u, ∑ v, ∑ A,
                    c u v * (L.coeff A *
                      |cutIndicator A u - cutIndicator A v|) := by
                        apply Finset.sum_congr rfl
                        intro u _
                        apply Finset.sum_congr rfl
                        intro v _
                        rw [hdiff u v, Finset.mul_sum]
            (∑ u, ∑ v, ∑ A,
                c u v * (L.coeff A *
                  |cutIndicator A u - cutIndicator A v|))
                = ∑ u, ∑ A, ∑ v,
                    c u v * (L.coeff A *
                      |cutIndicator A u - cutIndicator A v|) := by
                        apply Finset.sum_congr rfl
                        intro u _
                        rw [Finset.sum_comm]
            _ = ∑ A, ∑ u, ∑ v,
                    c u v * (L.coeff A *
                      |cutIndicator A u - cutIndicator A v|) := by
                        rw [Finset.sum_comm]
            _ = ∑ A, L.coeff A *
                  (∑ u, ∑ v, c u v *
                    |cutIndicator A u - cutIndicator A v|) := by
                        apply Finset.sum_congr rfl
                        intro A _
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro u _
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro v _
                        ring
    _ = 2 * ∑ A, L.coeff A * finiteCutCapacity c A := by
      simp_rw [cutIndicator_weightedVariation c hsym]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      ring

/-- Exact finite coarea formula for a symmetric capacity kernel. -/
theorem finite_weighted_coarea
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (c : V → V → ℝ) (_hc : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u) (φ : V → ℝ) :
    ∃ coeff : Finset V → ℝ, (∀ A, 0 ≤ coeff A) ∧
      (∑ u, ∑ v, c u v * |φ u - φ v|) =
        2 * ∑ A, coeff A * finiteCutCapacity c A := by
  obtain ⟨base, L, _⟩ := finite_potential_cut_layerCake φ
  exact ⟨L.coeff, L.coeff_nonneg,
    cutLayerCake_weightedVariation c hsym φ base L⟩

/-- Pairing of a centered demand with a vertex potential. -/
def demandPairing {V : Type*} [Fintype V] (b φ : V → ℝ) : ℝ :=
  ∑ v, b v * φ v

/-- The cut conditions control every dual potential. -/
theorem cut_conditions_bound_every_potential
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (c : V → V → ℝ) (_hc : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u)
    (b : V → ℝ) (κ : ℝ) (_hκ : 0 ≤ κ)
    (hcenter : ∑ v, b v = 0)
    (hcut : ∀ A : Finset V,
      |∑ v ∈ A, b v| ≤ κ * finiteCutCapacity c A)
    (φ : V → ℝ) :
    |demandPairing b φ| ≤
      κ / 2 * ∑ u, ∑ v, c u v * |φ u - φ v| := by
  classical
  obtain ⟨base, L, _⟩ := finite_potential_cut_layerCake φ
  have hshift : demandPairing b φ = ∑ v, b v * (φ v - base) := by
    unfold demandPairing
    calc
      (∑ v, b v * φ v) = ∑ v, (b v * (φ v - base) + b v * base) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = (∑ v, b v * (φ v - base)) + (∑ v, b v) * base := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = ∑ v, b v * (φ v - base) := by rw [hcenter, zero_mul, add_zero]
  have hpair : demandPairing b φ =
      ∑ A, L.coeff A * (∑ v ∈ A, b v) := by
    rw [hshift]
    calc
      (∑ v, b v * (φ v - base))
          = ∑ v, b v * ∑ A, L.coeff A * cutIndicator A v := by
            apply Finset.sum_congr rfl
            intro v _
            rw [L.expansion]
      _ = ∑ A, L.coeff A * (∑ v ∈ A, b v) := by
        calc
          (∑ v, b v * ∑ A, L.coeff A * cutIndicator A v)
              = ∑ v, ∑ A, b v * (L.coeff A * cutIndicator A v) := by
                apply Finset.sum_congr rfl
                intro v _
                rw [Finset.mul_sum]
          (∑ v, ∑ A, b v * (L.coeff A * cutIndicator A v))
              = ∑ A, ∑ v, b v * (L.coeff A * cutIndicator A v) :=
                Finset.sum_comm
          _ = ∑ A, L.coeff A * (∑ v ∈ A, b v) := by
            apply Finset.sum_congr rfl
            intro A _
            rw [Finset.mul_sum]
            simp [cutIndicator]
            apply Finset.sum_congr rfl
            intro v _
            ring
  have hvar := cutLayerCake_weightedVariation c hsym φ base L
  rw [hpair]
  calc
    |∑ A, L.coeff A * (∑ v ∈ A, b v)|
        ≤ ∑ A, |L.coeff A * (∑ v ∈ A, b v)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ A, L.coeff A * |∑ v ∈ A, b v| := by
      apply Finset.sum_congr rfl
      intro A _
      rw [abs_mul, abs_of_nonneg (L.coeff_nonneg A)]
    _ ≤ ∑ A, L.coeff A * (κ * finiteCutCapacity c A) :=
      Finset.sum_le_sum fun A _ =>
        mul_le_mul_of_nonneg_left (hcut A) (L.coeff_nonneg A)
    _ = κ * ∑ A, L.coeff A * finiteCutCapacity c A := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      ring
    _ = κ / 2 * ∑ u, ∑ v, c u v * |φ u - φ v| := by
      rw [hvar]
      ring

/-- Antisymmetric currents obeying the pointwise capacity box. -/
def finiteCapacityCurrentSet
    {V : Type*} [Fintype V]
    (c : V → V → ℝ) (κ : ℝ) : Set (V → V → ℝ) :=
  {j | (∀ u v, j u v = -j v u) ∧
    ∀ u v, |j u v| ≤ κ * c u v}

/-- Divergence of a finite current. -/
def finiteDivergence {V : Type*} [Fintype V]
    (j : V → V → ℝ) (v : V) : ℝ :=
  ∑ u, j v u

/-- The antisymmetric capacity box is compact. -/
theorem finiteCapacityCurrentSet_isCompact
    {V : Type*} [Fintype V]
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    IsCompact (finiteCapacityCurrentSet c κ) := by
  let B : Set (V → V → ℝ) :=
    {j | ∀ u v, j u v ∈ Set.Icc (-(κ * c u v)) (κ * c u v)}
  let S : Set (V → V → ℝ) := {j | j = fun u v => -j v u}
  have hB : IsCompact B := by
    exact isCompact_pi_infinite fun u =>
      isCompact_pi_infinite fun v => isCompact_Icc
  have hS : IsClosed S := by
    exact isClosed_eq continuous_id
      (continuous_pi fun u => continuous_pi fun v =>
        (continuous_apply_apply v u).neg)
  have heq : finiteCapacityCurrentSet c κ = B ∩ S := by
    ext j
    simp only [finiteCapacityCurrentSet, B, S, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · intro hj
      exact ⟨fun u v => abs_le.mp (hj.2 u v),
        funext fun u => funext fun v => hj.1 u v⟩
    · intro hj
      exact ⟨fun u v => congrFun (congrFun hj.2 u) v,
        fun u v => abs_le.mpr (hj.1 u v)⟩
  rw [heq]
  exact hB.inter_right hS

/-- Divergence is continuous on the finite current space. -/
theorem continuous_finiteDivergence
    {V : Type*} [Fintype V] :
    Continuous (finiteDivergence : (V → V → ℝ) → (V → ℝ)) := by
  apply continuous_pi
  intro v
  exact continuous_finset_sum Finset.univ fun u _ =>
    continuous_apply_apply v u

/-- The set of demands routable in a fixed capacity box is compact. -/
theorem finiteRoutableDemandSet_isCompact
    {V : Type*} [Fintype V]
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    IsCompact (finiteDivergence '' finiteCapacityCurrentSet c κ) :=
  (finiteCapacityCurrentSet_isCompact c hc κ hκ).image
    continuous_finiteDivergence

/-- The capacity box is convex. -/
theorem finiteCapacityCurrentSet_convex
    {V : Type*} [Fintype V]
    (c : V → V → ℝ) (κ : ℝ) :
    Convex ℝ (finiteCapacityCurrentSet c κ) := by
  intro j hj k hk a b ha hb hab
  constructor
  · intro u v
    change a * j u v + b * k u v = -(a * j v u + b * k v u)
    rw [hj.1 u v, hk.1 u v]
    ring
  · intro u v
    change |a * j u v + b * k u v| ≤ κ * c u v
    calc
      |a * j u v + b * k u v|
          ≤ a * |j u v| + b * |k u v| := by
            calc
              |a * j u v + b * k u v|
                  ≤ |a * j u v| + |b * k u v| := abs_add_le _ _
              _ = a * |j u v| + b * |k u v| := by
                rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (κ * c u v) + b * (κ * c u v) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hj.2 u v) ha)
          (mul_le_mul_of_nonneg_left (hk.2 u v) hb)
      _ = κ * c u v := by rw [← add_mul, hab, one_mul]

/-- Divergence as a linear map. -/
def finiteDivergenceLinear
    {V : Type*} [Fintype V] :
    (V → V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := finiteDivergence
  map_add' j k := by
    funext v
    simp [finiteDivergence, Finset.sum_add_distrib]
  map_smul' a j := by
    funext v
    simp [finiteDivergence, Finset.mul_sum]

/-- Routable demands form a convex set. -/
theorem finiteRoutableDemandSet_convex
    {V : Type*} [Fintype V]
    (c : V → V → ℝ) (κ : ℝ) :
    Convex ℝ (finiteDivergence '' finiteCapacityCurrentSet c κ) := by
  change Convex ℝ
    ((finiteDivergenceLinear : (V → V → ℝ) →ₗ[ℝ] (V → ℝ)) ''
      finiteCapacityCurrentSet c κ)
  exact (finiteCapacityCurrentSet_convex c κ).linear_image
    (finiteDivergenceLinear : (V → V → ℝ) →ₗ[ℝ] (V → ℝ))

/-- Discrete integration by parts for an antisymmetric current. -/
theorem divergence_pairing_eq_half_edge_pairing
    {V : Type*} [Fintype V]
    (j : V → V → ℝ) (hanti : ∀ u v, j u v = -j v u)
    (φ : V → ℝ) :
    demandPairing (finiteDivergence j) φ =
      1 / 2 * ∑ u, ∑ v, j u v * (φ u - φ v) := by
  have hleft :
      demandPairing (finiteDivergence j) φ =
        ∑ u, ∑ v, j u v * φ u := by
    unfold demandPairing finiteDivergence
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_mul]
  have hright :
      (∑ u, ∑ v, j u v * φ v) =
        -(∑ u, ∑ v, j u v * φ u) := by
    calc
      (∑ u, ∑ v, j u v * φ v)
          = ∑ v, ∑ u, j u v * φ v := Finset.sum_comm
      _ = ∑ v, -(∑ u, j v u * φ v) := by
        apply Finset.sum_congr rfl
        intro v _
        calc
          (∑ u, j u v * φ v) = ∑ u, -(j v u * φ v) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [hanti u v]
            ring
          _ = -(∑ u, j v u * φ v) := by
            rw [Finset.sum_neg_distrib]
      _ = -(∑ v, ∑ u, j v u * φ v) := by
        rw [Finset.sum_neg_distrib]
  have hsplit :
      (∑ u, ∑ v, j u v * (φ u - φ v)) =
        (∑ u, ∑ v, j u v * φ u) -
          (∑ u, ∑ v, j u v * φ v) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  calc
    demandPairing (finiteDivergence j) φ
        = ∑ u, ∑ v, j u v * φ u := hleft
    _ = 1 / 2 * ((∑ u, ∑ v, j u v * φ u) -
          (∑ u, ∑ v, j u v * φ v)) := by rw [hright]; ring
    _ = 1 / 2 * ∑ u, ∑ v, j u v * (φ u - φ v) := by rw [hsplit]

/-- Saturating every oriented edge by the sign of a potential difference. -/
def saturatedPotentialCurrent
    {V : Type*} [Fintype V]
    (c : V → V → ℝ) (κ : ℝ) (φ : V → ℝ) : V → V → ℝ :=
  fun u v => κ * c u v * Real.sign (φ u - φ v)

theorem abs_real_sign_le_one (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num

/-- The sign-saturated current belongs to the capacity box. -/
theorem saturatedPotentialCurrent_mem
    {V : Type*} [Fintype V]
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u)
    (κ : ℝ) (hκ : 0 ≤ κ) (φ : V → ℝ) :
    saturatedPotentialCurrent c κ φ ∈ finiteCapacityCurrentSet c κ := by
  constructor
  · intro u v
    unfold saturatedPotentialCurrent
    rw [hsym u v]
    have hneg : φ v - φ u = -(φ u - φ v) := by ring
    rw [hneg, Real.sign_neg]
    ring
  · intro u v
    unfold saturatedPotentialCurrent
    rw [abs_mul, abs_mul, abs_of_nonneg hκ, abs_of_nonneg (hc u v)]
    calc
      κ * c u v * |Real.sign (φ u - φ v)|
          ≤ κ * c u v * 1 :=
            mul_le_mul_of_nonneg_left
              (abs_real_sign_le_one _) (mul_nonneg hκ (hc u v))
      _ = κ * c u v := mul_one _

/-- The sign-saturated current realizes the support function of the box. -/
theorem saturatedPotentialCurrent_pairing
    {V : Type*} [Fintype V]
    (c : V → V → ℝ) (hsym : ∀ u v, c u v = c v u)
    (κ : ℝ) (φ : V → ℝ) :
    demandPairing (finiteDivergence (saturatedPotentialCurrent c κ φ)) φ =
      κ / 2 * ∑ u, ∑ v, c u v * |φ u - φ v| := by
  rw [divergence_pairing_eq_half_edge_pairing
    (saturatedPotentialCurrent c κ φ)
    (fun u v => by
      unfold saturatedPotentialCurrent
      rw [hsym u v]
      have hneg : φ v - φ u = -(φ u - φ v) := by ring
      rw [hneg, Real.sign_neg]
      ring) φ]
  unfold saturatedPotentialCurrent
  have hsum :
    (∑ u, ∑ v, κ * c u v * Real.sign (φ u - φ v) *
        (φ u - φ v))
        = ∑ u, ∑ v, κ * (c u v * |φ u - φ v|) := by
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro v _
          have hsign :
              Real.sign (φ u - φ v) * (φ u - φ v) =
                |φ u - φ v| := by
            rcases lt_trichotomy (φ u - φ v) 0 with h | h | h
            · rw [Real.sign_of_neg h, abs_of_neg h]
              ring
            · rw [h, Real.sign_zero, abs_zero]
              ring
            · rw [Real.sign_of_pos h, abs_of_pos h]
              ring
          calc
            κ * c u v * Real.sign (φ u - φ v) * (φ u - φ v)
                = κ * c u v *
                    (Real.sign (φ u - φ v) * (φ u - φ v)) := by ring
            _ = κ * c u v * |φ u - φ v| := by rw [hsign]
            _ = κ * (c u v * |φ u - φ v|) := by ring
  calc
    1 / 2 * (∑ u, ∑ v, κ * c u v * Real.sign (φ u - φ v) *
        (φ u - φ v))
        = 1 / 2 * (∑ u, ∑ v, κ * (c u v * |φ u - φ v|)) := by rw [hsum]
    _ = 1 / 2 * (κ * ∑ u, ∑ v, c u v * |φ u - φ v|) := by
      congr 1
      calc
        (∑ u, ∑ v, κ * (c u v * |φ u - φ v|))
            = ∑ u, κ * (∑ v, c u v * |φ u - φ v|) := by
              apply Finset.sum_congr rfl
              intro u _
              rw [Finset.mul_sum]
        _ = κ * ∑ u, ∑ v, c u v * |φ u - φ v| := by
          rw [Finset.mul_sum]
    _ = κ / 2 * ∑ u, ∑ v, c u v * |φ u - φ v| := by ring

/-- Coordinate potential associated to a finite-dimensional linear functional. -/
def functionalPotential
    {V : Type*} [Fintype V] [DecidableEq V]
    (f : StrongDual ℝ (V → ℝ)) (v : V) : ℝ :=
  f (fun w => if v = w then 1 else 0)

/-- Every functional on the finite vertex space is pairing with its coordinate potential. -/
theorem functional_eq_demandPairing
    {V : Type*} [Fintype V] [DecidableEq V]
    (f : StrongDual ℝ (V → ℝ)) (x : V → ℝ) :
    f x = demandPairing x (functionalPotential f) := by
  have hcoord := f.toLinearMap.pi_apply_eq_sum_univ x
  change f.toLinearMap x = _
  rw [hcoord]
  unfold demandPairing functionalPotential
  apply Finset.sum_congr rfl
  intro v _
  simp [smul_eq_mul]

/-- Finite max-flow/min-cut converse for a centered transshipment demand. -/
theorem finite_transshipment_maxCut_converse
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u)
    (b : V → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hcenter : ∑ v, b v = 0)
    (hcut : ∀ A : Finset V,
      |∑ v ∈ A, b v| ≤ κ * finiteCutCapacity c A) :
    ∃ j, j ∈ finiteCapacityCurrentSet c κ ∧ finiteDivergence j = b := by
  by_contra hno
  have hbnot :
      b ∉ finiteDivergence '' finiteCapacityCurrentSet c κ := by
    intro hb
    rcases hb with ⟨j, hj, hjdiv⟩
    exact hno ⟨j, hj, hjdiv⟩
  obtain ⟨f, t, hsep, hfb⟩ :=
    geometric_hahn_banach_closed_point
      (finiteRoutableDemandSet_convex c κ)
      (finiteRoutableDemandSet_isCompact c hc κ hκ).isClosed hbnot
  let φ := functionalPotential f
  let jφ := saturatedPotentialCurrent c κ φ
  have hjφ : jφ ∈ finiteCapacityCurrentSet c κ :=
    saturatedPotentialCurrent_mem c hc hsym κ hκ φ
  have hdivmem :
      finiteDivergence jφ ∈
        finiteDivergence '' finiteCapacityCurrentSet c κ :=
    ⟨jφ, hjφ, rfl⟩
  have hstrict : f (finiteDivergence jφ) < f b :=
    (hsep _ hdivmem).trans hfb
  have hcutdual :
      |demandPairing b φ| ≤
        κ / 2 * ∑ u, ∑ v, c u v * |φ u - φ v| :=
    cut_conditions_bound_every_potential c hc hsym b κ hκ
      hcenter hcut φ
  have hsat :
      demandPairing (finiteDivergence jφ) φ =
        κ / 2 * ∑ u, ∑ v, c u v * |φ u - φ v| := by
    exact saturatedPotentialCurrent_pairing c hsym κ φ
  have hfbpair : f b = demandPairing b φ := by
    exact functional_eq_demandPairing f b
  have hfjpair :
      f (finiteDivergence jφ) =
        demandPairing (finiteDivergence jφ) φ := by
    exact functional_eq_demandPairing f _
  rw [hfbpair, hfjpair, hsat] at hstrict
  exact (not_lt_of_ge ((le_abs_self _).trans hcutdual)) hstrict

/-- Exact finite flow/cut characterization for centered transshipment. -/
theorem finite_transshipment_flow_cut_iff
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u)
    (b : V → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hcenter : ∑ v, b v = 0) :
    (∃ j, j ∈ finiteCapacityCurrentSet c κ ∧ finiteDivergence j = b) ↔
      ∀ A : Finset V,
        |∑ v ∈ A, b v| ≤ κ * finiteCutCapacity c A := by
  constructor
  · rintro ⟨j, hj, hjdiv⟩ A
    apply abs_le.mpr
    have hup := flow_cut_weak_duality j c hj.1 A κ hj.2
    have hup' :
        (∑ v ∈ A, b v) ≤ κ * finiteCutCapacity c A := by
      rw [← hjdiv]
      exact hup
    have hnegAnti : ∀ u v, -j u v = -(-j v u) := by
      intro u v
      rw [hj.1 u v]
    have hnegCong : ∀ u v, |-j u v| ≤ κ * c u v := by
      intro u v
      simpa only [abs_neg] using hj.2 u v
    have hlo := flow_cut_weak_duality
      (fun u v => -j u v) c hnegAnti A κ hnegCong
    have hlo' :
        -(∑ v ∈ A, b v) ≤ κ * finiteCutCapacity c A := by
      rw [← hjdiv]
      change -(∑ v ∈ A, finiteDivergence j v) ≤
        κ * finiteCutCapacity c A
      change -(∑ v ∈ A, ∑ u, j v u) ≤
        κ * (∑ v ∈ A, ∑ u ∈ Aᶜ, c v u)
      simpa only [Finset.sum_neg_distrib] using hlo
    exact ⟨by linarith, hup'⟩
  · exact finite_transshipment_maxCut_converse c hc hsym b κ hκ
      hcenter

end NCG
