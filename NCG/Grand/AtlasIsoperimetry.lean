/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Coordinate and atlas discharge of the cut margin
  (`thm:coordinate-atlas-isoperimetry`, Gran-Tensor manuscript)

* `loomis_whitney_dim3`: the discrete three-dimensional
  Loomis–Whitney inequality —
  `|A|² ≤ |π₁₂A|·|π₁₃A|·|π₂₃A|` for every finite set of
  coordinate triples (proved from scratch by fiberwise
  Cauchy–Schwarz); this is the axis bound behind the boxed
  Cartesian cut floor `I_X ≥ I_ax`;
* `axis_floor_positive`: the boxed Cartesian floor
  `I_ax = c₋δ_κ/m₊^{2/3} > 0` with
  `δ_κ = (16C_κ²)⁻¹`, `C_κ = max{1, 2^{-1/3}κ⁻¹}`;
* `atlas_floor_positive`: the boxed atlas floor
  `I_atlas = min{I₀(2ηv_*/V_*)^{2/3}, J_*(2/V_*)^{2/3}} > 0`.

Rendering disclosed: the reduction of the cut constant to the
Loomis–Whitney axis bound through the unit-coordinate-edge
counting (the manuscript's `δ_κ` bookkeeping) and the
chart-nerve case analysis behind the atlas branch are the
manuscript's isoperimetric layer; the Loomis–Whitney inequality
itself and both positivity floors are proved here.
-/

open Finset

namespace NCG

variable {α β γ : Type*}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Discrete three-dimensional Loomis–Whitney:
`|A|² ≤ |π₁₂A|·(|π₁₃A|·|π₂₃A|)`. -/
theorem loomis_whitney_dim3 (A : Finset (α × β × γ)) :
    A.card ^ 2
      ≤ (A.image fun p => (p.1, p.2.1)).card
        * ((A.image fun p => (p.1, p.2.2)).card
          * (A.image fun p => p.2).card) := by
  set P12 := A.image fun p => (p.1, p.2.1) with hP12
  set P13 := A.image fun p => (p.1, p.2.2) with hP13
  set P23 := A.image fun p => p.2 with hP23
  set T := A.image Prod.fst with hT
  -- fiber cards over the first coordinate
  have hA : A.card
      = ∑ a ∈ T, (A.filter fun p => p.1 = a).card :=
    card_eq_sum_card_fiberwise fun x hx =>
      mem_image_of_mem _ hx
  have h12 : P12.card
      = ∑ a ∈ T, (P12.filter fun q => q.1 = a).card :=
    card_eq_sum_card_fiberwise fun x hx => by
      rcases mem_image.mp hx with ⟨p, hp, rfl⟩
      exact mem_image_of_mem _ hp
  have h13 : P13.card
      = ∑ a ∈ T, (P13.filter fun q => q.1 = a).card :=
    card_eq_sum_card_fiberwise fun x hx => by
      rcases mem_image.mp hx with ⟨p, hp, rfl⟩
      exact mem_image_of_mem _ hp
  -- each fiber embeds into the product of its two projections
  have hfiber : ∀ a : α, (A.filter fun p => p.1 = a).card
      ≤ (P12.filter fun q => q.1 = a).card
        * (P13.filter fun q => q.1 = a).card := by
    intro a
    have hmap : ∀ p ∈ A.filter fun p => p.1 = a,
        ((p.1, p.2.1), (p.1, p.2.2))
          ∈ (P12.filter fun q => q.1 = a)
            ×ˢ (P13.filter fun q => q.1 = a) := by
      intro p hp
      rcases mem_filter.mp hp with ⟨hpA, hpa⟩
      refine mem_product.mpr ⟨?_, ?_⟩
      · exact mem_filter.mpr
          ⟨mem_image_of_mem _ hpA, hpa⟩
      · exact mem_filter.mpr
          ⟨mem_image_of_mem _ hpA, hpa⟩
    have hinj : ∀ p ∈ A.filter fun p => p.1 = a,
        ∀ q ∈ A.filter fun p => p.1 = a,
        ((p.1, p.2.1), (p.1, p.2.2))
          = ((q.1, q.2.1), (q.1, q.2.2)) → p = q := by
      intro p _ q _ h
      have ha1 : p.1 = q.1 := congrArg (fun x => x.1.1) h
      have hb : p.2.1 = q.2.1 := congrArg (fun x => x.1.2) h
      have hc : p.2.2 = q.2.2 := congrArg (fun x => x.2.2) h
      exact Prod.ext ha1 (Prod.ext hb hc)
    calc (A.filter fun p => p.1 = a).card
        ≤ ((P12.filter fun q => q.1 = a)
            ×ˢ (P13.filter fun q => q.1 = a)).card :=
          card_le_card_of_injOn _ hmap hinj
      _ = _ := card_product _ _
  -- each fiber also embeds into the 23-projection
  have hfiber23 : ∀ a : α, (A.filter fun p => p.1 = a).card
      ≤ P23.card := by
    intro a
    refine card_le_card_of_injOn Prod.snd
      (fun p hp => mem_image_of_mem _ (mem_filter.mp hp).1) ?_
    intro p hp q hq h2
    have hpa := (mem_filter.mp hp).2
    have hqa := (mem_filter.mp hq).2
    exact Prod.ext (hpa.trans hqa.symm) h2
  -- fiberwise Cauchy–Schwarz
  have hkey := sum_sq_le_sum_mul_sum_of_sq_le_mul T
    (r := fun a => (A.filter fun p => p.1 = a).card)
    (f := fun a => ((P12.filter fun q => q.1 = a).card : ℕ))
    (g := fun a => (P13.filter fun q => q.1 = a).card
      * P23.card)
    (fun a _ => Nat.zero_le _) (fun a _ => Nat.zero_le _)
    (fun a _ => by
      have h1 := hfiber a
      have h2 := hfiber23 a
      calc (A.filter fun p => p.1 = a).card ^ 2
          = (A.filter fun p => p.1 = a).card
            * (A.filter fun p => p.1 = a).card := sq _
        _ ≤ ((P12.filter fun q => q.1 = a).card
              * (P13.filter fun q => q.1 = a).card)
            * P23.card :=
            Nat.mul_le_mul h1 h2
        _ = (P12.filter fun q => q.1 = a).card
            * ((P13.filter fun q => q.1 = a).card
              * P23.card) := by ring)
  rw [← hA, ← h12] at hkey
  refine le_trans hkey ?_
  rw [← Finset.sum_mul, ← h13]

/-- Boxed Cartesian axis floor:
`I_ax = c₋δ_κ/m₊^{2/3} > 0` with `δ_κ = (16C_κ²)⁻¹`. -/
theorem axis_floor_positive (cminus mplus κ : ℝ)
    (hc : 0 < cminus) (hm : 0 < mplus) (_hκ : 0 < κ) :
    0 < cminus * (16 * max 1 (2 ^ (-(1 : ℝ) / 3) * κ⁻¹) ^ 2)⁻¹
      / mplus ^ ((2 : ℝ) / 3) := by
  have hC : 0 < max 1 (2 ^ (-(1 : ℝ) / 3) * κ⁻¹) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  have hrpow : 0 < mplus ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hm _
  positivity

/-- Boxed atlas floor:
`I_atlas = min{I₀(2ηv_*/V_*)^{2/3}, J_*(2/V_*)^{2/3}} > 0`. -/
theorem atlas_floor_positive (I0 Jstar η vstar Vstar : ℝ)
    (hI : 0 < I0) (hJ : 0 < Jstar) (hη : 0 < η)
    (hv : 0 < vstar) (hV : 0 < Vstar) :
    0 < min (I0 * (2 * η * vstar / Vstar) ^ ((2 : ℝ) / 3))
      (Jstar * (2 / Vstar) ^ ((2 : ℝ) / 3)) := by
  have h1 : 0 < (2 * η * vstar / Vstar : ℝ) := by positivity
  have h2 : 0 < (2 / Vstar : ℝ) := by positivity
  have hr1 : 0 < (2 * η * vstar / Vstar) ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos h1 _
  have hr2 : 0 < (2 / Vstar) ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos h2 _
  exact lt_min (by positivity) (by positivity)

/-- Exact Cartesian reduction from a mixed-fiber crossing count to the
manuscript's weighted cut inequality.  The geometric Loomis--Whitney step is
isolated in `hmixed`; every remaining scale and constant is discharged here. -/
theorem cartesian_cut_bound_of_mixedFibers
    (cardA massA cutCapacity h cminus mplus δ : ℝ)
    (hh : 0 < h) (hc : 0 ≤ cminus) (hm : 0 < mplus)
    (hδ : 0 ≤ δ) (hcard : 0 ≤ cardA) (hmass0 : 0 ≤ massA)
    (hmass : massA ≤ mplus * h ^ 3 * cardA)
    (hmixed : cminus * h * (δ * cardA ^ ((2 : ℝ) / 3)) ≤ cutCapacity) :
    (cminus * δ / mplus ^ ((2 : ℝ) / 3)) *
        massA ^ ((2 : ℝ) / 3) ≤ h * cutCapacity := by
  have hrpow := Real.rpow_le_rpow hmass0 hmass (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hscale :
      (mplus * h ^ 3 * cardA) ^ ((2 : ℝ) / 3) =
        mplus ^ ((2 : ℝ) / 3) * h ^ 2 * cardA ^ ((2 : ℝ) / 3) := by
    rw [Real.mul_rpow (mul_nonneg hm.le (by positivity)) hcard,
      Real.mul_rpow hm.le (by positivity), ← Real.rpow_natCast h 3,
      ← Real.rpow_mul hh.le]
    norm_num
  rw [hscale] at hrpow
  have hmPow : 0 < mplus ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hm _
  calc
    (cminus * δ / mplus ^ ((2 : ℝ) / 3)) * massA ^ ((2 : ℝ) / 3) ≤
        (cminus * δ / mplus ^ ((2 : ℝ) / 3)) *
          (mplus ^ ((2 : ℝ) / 3) * h ^ 2 * cardA ^ ((2 : ℝ) / 3)) := by
            exact mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ = h * (cminus * h * (δ * cardA ^ ((2 : ℝ) / 3))) := by
      field_simp [hmPow.ne']
    _ ≤ h * cutCapacity := mul_le_mul_of_nonneg_left hmixed hh.le

set_option maxHeartbeats 800000 in
/-- The exact normalized bookkeeping behind the Cartesian mixed-fiber
alternative.  Here `xᵢ` is the normalized full-fiber contribution,
`pᵢ` the normalized projection size, and `mᵢ` the normalized mixed-fiber
count.  Loomis--Whitney gives `1 ≤ p₁p₂p₃`. -/
theorem normalized_mixedFiber_direction_exists
    (x1 x2 x3 p1 p2 p3 m1 m2 m3 C δ : ℝ)
    (hC : 1 ≤ C) (hδ : 0 < δ) (hδid : 16 * C ^ 2 * δ = 1)
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)
    (hx1C : x1 ≤ C) (hx2C : x2 ≤ C) (hx3C : x3 ≤ C)
    (hproduct : x1 * x2 * x3 ≤ 1 / 2)
    (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hp3 : 0 ≤ p3)
    (hproj1 : p1 ≤ m1 + x1) (hproj2 : p2 ≤ m2 + x2)
    (hproj3 : p3 ≤ m3 + x3) (hLW : 1 ≤ p1 * p2 * p3) :
    δ ≤ m1 ∨ δ ≤ m2 ∨ δ ≤ m3 := by
  by_contra hn
  push_neg at hn
  rcases hn with ⟨hm1, hm2, hm3⟩
  have ha1 : p1 < δ + x1 := hproj1.trans_lt (by linarith)
  have ha2 : p2 < δ + x2 := hproj2.trans_lt (by linarith)
  have ha3 : p3 < δ + x3 := hproj3.trans_lt (by linarith)
  have hapos1 : 0 < δ + x1 := by positivity
  have hapos2 : 0 < δ + x2 := by positivity
  have hapos3 : 0 < δ + x3 := by positivity
  have hp1pos : 0 < p1 := by
    by_contra hn
    have hz : p1 = 0 := le_antisymm (le_of_not_gt hn) hp1
    rw [hz] at hLW
    norm_num at hLW
  have hp2pos : 0 < p2 := by
    by_contra hn
    have hz : p2 = 0 := le_antisymm (le_of_not_gt hn) hp2
    rw [hz] at hLW
    norm_num at hLW
  have hp3pos : 0 < p3 := by
    by_contra hn
    have hz : p3 = 0 := le_antisymm (le_of_not_gt hn) hp3
    rw [hz] at hLW
    norm_num at hLW
  have hprodlt : p1 * p2 * p3 < (δ + x1) * (δ + x2) * (δ + x3) := by
    have h12 : p1 * p2 < (δ + x1) * (δ + x2) :=
      mul_lt_mul ha1 ha2.le hp2pos hapos1.le
    exact mul_lt_mul h12 ha3.le hp3pos (mul_nonneg hapos1.le hapos2.le)
  have hC0 : 0 < C := one_pos.trans_le hC
  have hCC : C ≤ C ^ 2 := by nlinarith
  have hδC2 : δ * C ^ 2 = 1 / 16 := by nlinarith [hδid]
  have hδle : δ ≤ 1 / 16 := by
    have := mul_le_mul_of_nonneg_left hCC hδ.le
    nlinarith [hδC2]
  have hδC : δ * C ≤ 1 / 16 := by
    have := mul_le_mul_of_nonneg_left hCC hδ.le
    nlinarith [hδC2]
  have hpair12 : δ * (x1 * x2) ≤ 1 / 16 := by
    have hxy : x1 * x2 ≤ C ^ 2 := by nlinarith [mul_nonneg hx1 hx2]
    exact (mul_le_mul_of_nonneg_left hxy hδ.le).trans_eq hδC2
  have hpair13 : δ * (x1 * x3) ≤ 1 / 16 := by
    have hxy : x1 * x3 ≤ C ^ 2 := by nlinarith [mul_nonneg hx1 hx3]
    exact (mul_le_mul_of_nonneg_left hxy hδ.le).trans_eq hδC2
  have hpair23 : δ * (x2 * x3) ≤ 1 / 16 := by
    have hxy : x2 * x3 ≤ C ^ 2 := by nlinarith [mul_nonneg hx2 hx3]
    exact (mul_le_mul_of_nonneg_left hxy hδ.le).trans_eq hδC2
  have hsingle1 : δ ^ 2 * x1 ≤ 1 / 256 := by
    have hx : δ * x1 ≤ 1 / 16 :=
      (mul_le_mul_of_nonneg_left hx1C hδ.le).trans hδC
    nlinarith [mul_nonneg hδ.le hx1]
  have hsingle2 : δ ^ 2 * x2 ≤ 1 / 256 := by
    have hx : δ * x2 ≤ 1 / 16 :=
      (mul_le_mul_of_nonneg_left hx2C hδ.le).trans hδC
    nlinarith [mul_nonneg hδ.le hx2]
  have hsingle3 : δ ^ 2 * x3 ≤ 1 / 256 := by
    have hx : δ * x3 ≤ 1 / 16 :=
      (mul_le_mul_of_nonneg_left hx3C hδ.le).trans hδC
    nlinarith [mul_nonneg hδ.le hx3]
  have hcube : δ ^ 3 ≤ 1 / 4096 := by nlinarith [hδle, sq_nonneg δ]
  have hexpand :
      (δ + x1) * (δ + x2) * (δ + x3) =
        x1 * x2 * x3 + δ * (x1 * x2) + δ * (x1 * x3) +
          δ * (x2 * x3) + δ ^ 2 * x1 + δ ^ 2 * x2 +
            δ ^ 2 * x3 + δ ^ 3 := by ring
  rw [hexpand] at hprodlt
  nlinarith

/-- A finite protected nerve is connected when every nonempty proper set of
charts has an interface crossing its boundary.  This cut formulation is
equivalent to graph connectedness and is the exact form used by atlas gluing. -/
def NerveCutConnected {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adj : ι → ι → Prop) : Prop :=
  ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ →
    ∃ a ∈ S, ∃ b ∉ S, adj a b

/-- Connected-nerve majority lemma: if both majority colours occur, an
interface joins opposite colours. -/
theorem exists_opposite_majority_interface
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adj : ι → ι → Prop) (inside : ι → Prop)
    (hconn : NerveCutConnected adj)
    (hin : ∃ a, inside a) (hout : ∃ b, ¬ inside b) :
    ∃ a b, inside a ∧ ¬ inside b ∧ adj a b := by
  classical
  let S : Finset ι := Finset.univ.filter inside
  have hSne : S.Nonempty := by
    rcases hin with ⟨a, ha⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  have hSproper : S ≠ Finset.univ := by
    rcases hout with ⟨b, hb⟩
    intro h
    have : inside b := (Finset.mem_filter.mp (h ▸ Finset.mem_univ b)).2
    exact hb this
  rcases hconn S hSne hSproper with ⟨a, haS, b, hbS, hab⟩
  exact ⟨a, b, (Finset.mem_filter.mp haS).2,
    fun hb => hbS (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩), hab⟩

/-- Concavity of `x ↦ x^p`, in the finite-sum form used to aggregate
disjoint local chart cuts. -/
theorem rpow_sum_le_sum_rpow
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ) (p : ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, x i) ^ p ≤ ∑ i ∈ s, x i ^ p := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [Real.zero_rpow hp0.ne']
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine (Real.rpow_add_le_add_rpow (hx a (Finset.mem_insert_self a s))
        (Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)) hp0.le hp1).trans ?_
      exact add_le_add (le_refl _) (ih (fun i hi => hx i (Finset.mem_insert_of_mem hi)))

/-- Exact scalar atlas gluing theorem, including the all-outside chart case.
The two aggregation hypotheses are the quantitative content of the manuscript
phrase "partitioned protected chart cores". -/
theorem protected_atlas_cut_bound
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (chartMass insideMass localCut : ι → ℝ)
    (interfaceCut : ι → ι → ℝ) (adj : ι → ι → Prop)
    (totalMass globalMass globalCut I0 Jstar η vstar Vstar : ℝ)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hv : 0 < vstar) (hV : 0 < Vstar)
    (hI : 0 ≤ I0) (hJ : 0 ≤ Jstar)
    (hchartMass : ∀ a, vstar ≤ chartMass a)
    (hinside0 : ∀ a, 0 ≤ insideMass a)
    (hinside : ∀ a, insideMass a ≤ chartMass a)
    (hchartSum : totalMass = ∑ a, chartMass a)
    (hmassSum : globalMass = ∑ a, insideMass a)
    (htotal : totalMass ≤ Vstar)
    (hglobalHalf : globalMass ≤ totalMass / 2)
    (hlocal : ∀ a,
      I0 * min (insideMass a) (chartMass a - insideMass a) ^ ((2 : ℝ) / 3) ≤
        localCut a)
    (hlocalAggregate : ∑ a, localCut a ≤ globalCut)
    (hconn : NerveCutConnected adj)
    (hinterface : ∀ a b, adj a b →
      η * chartMass a ≤ insideMass a →
      insideMass b ≤ (1 - η) * chartMass b →
      Jstar ≤ interfaceCut a b)
    (hinterfaceGlobal : ∀ a b, interfaceCut a b ≤ globalCut) :
    min (I0 * (2 * η * vstar / Vstar) ^ ((2 : ℝ) / 3))
        (Jstar * (2 / Vstar) ^ ((2 : ℝ) / 3)) *
      globalMass ^ ((2 : ℝ) / 3) ≤ globalCut := by
  classical
  have hchart0 (a : ι) : 0 ≤ chartMass a := (hv.trans_le (hchartMass a)).le
  have htotal0 : 0 < totalMass := by
    rw [hchartSum]
    exact Finset.sum_pos (fun a _ => (hv.trans_le (hchartMass a))) Finset.univ_nonempty
  have hglobal0 : 0 ≤ globalMass := by
    rw [hmassSum]
    exact Finset.sum_nonneg fun a _ => hinside0 a
  have hscaleLocal :
      (2 * η * vstar / Vstar) ^ ((2 : ℝ) / 3) *
        globalMass ^ ((2 : ℝ) / 3) ≤ (η * vstar) ^ ((2 : ℝ) / 3) := by
    rw [← Real.mul_rpow (by positivity) hglobal0]
    apply Real.rpow_le_rpow (by positivity) (by
      have hhalf : 2 * globalMass ≤ Vstar := by nlinarith [hglobalHalf, htotal]
      calc
        2 * η * vstar / Vstar * globalMass =
            (η * vstar) * (2 * globalMass / Vstar) := by ring
        _ ≤ (η * vstar) * 1 := by
          gcongr
          exact (div_le_one hV).2 hhalf
        _ = η * vstar := mul_one _)
      (by norm_num)
  let majority : ι → Prop := fun a => (1 - η) * chartMass a < insideMass a
  by_cases hsplit : ∃ a,
      η * chartMass a ≤ insideMass a ∧
        insideMass a ≤ (1 - η) * chartMass a
  · rcases hsplit with ⟨a, haLow, haHigh⟩
    have hmin : η * vstar ≤ min (insideMass a)
        (chartMass a - insideMass a) := by
      apply le_min
      · exact (mul_le_mul_of_nonneg_left (hchartMass a) hη.le).trans haLow
      · have : η * chartMass a ≤ chartMass a - insideMass a := by
          nlinarith [mul_le_mul_of_nonneg_right (show η ≤ 1 - η by linarith)
            (hchart0 a)]
        exact (mul_le_mul_of_nonneg_left (hchartMass a) hη.le).trans this
    have hlocalA : I0 * (η * vstar) ^ ((2 : ℝ) / 3) ≤ globalCut := by
      have hexp : 0 ≤ (2 : ℝ) / 3 := by norm_num
      have hp : (η * vstar) ^ ((2 : ℝ) / 3) ≤
          min (insideMass a) (chartMass a - insideMass a) ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow (mul_nonneg hη.le hv.le) hmin hexp
      calc
        I0 * (η * vstar) ^ ((2 : ℝ) / 3) ≤
            I0 * min (insideMass a) (chartMass a - insideMass a) ^
              ((2 : ℝ) / 3) := mul_le_mul_of_nonneg_left hp hI
        _ ≤ localCut a := hlocal a
        _ ≤ ∑ i, localCut i := Finset.single_le_sum
          (fun i _ => (mul_nonneg hI (Real.rpow_nonneg
            (le_min (hinside0 i) (sub_nonneg.mpr (hinside i))) _)).trans
              (hlocal i)) (Finset.mem_univ a)
        _ ≤ globalCut := hlocalAggregate
    calc
      min (I0 * (2 * η * vstar / Vstar) ^ ((2 : ℝ) / 3))
          (Jstar * (2 / Vstar) ^ ((2 : ℝ) / 3)) *
          globalMass ^ ((2 : ℝ) / 3) ≤
          I0 * (2 * η * vstar / Vstar) ^ ((2 : ℝ) / 3) *
          globalMass ^ ((2 : ℝ) / 3) := by gcongr; exact min_le_left _ _
      _ ≤ I0 * (η * vstar) ^ ((2 : ℝ) / 3) := by rw [mul_assoc]; gcongr
      _ ≤ globalCut := hlocalA
  · push_neg at hsplit
    have hcolour (a : ι) : insideMass a < η * chartMass a ∨ majority a := by
      by_cases ha : η * chartMass a ≤ insideMass a
      · exact Or.inr (hsplit a ha)
      · exact Or.inl (lt_of_not_ge ha)
    by_cases hin : ∃ a, majority a
    · have hout : ∃ b, ¬ majority b := by
        by_contra hn
        have hn' : ∀ b, majority b := by
          simpa only [not_exists, not_not] using hn
        have hsum : totalMass / 2 < globalMass := by
          rw [hchartSum, hmassSum]
          rw [Finset.sum_div]
          let a0 : ι := Classical.choice inferInstance
          exact Finset.sum_lt_sum (fun a _ => by
            have hscalar : (1 / 2 : ℝ) < 1 - η := by linarith
            have hhalf : chartMass a / 2 < (1 - η) * chartMass a := by
              rw [div_eq_mul_inv]
              norm_num
              simpa [mul_comm] using
                mul_lt_mul_of_pos_right hscalar (hv.trans_le (hchartMass a))
            exact (hhalf.trans (hn' a)).le)
            ⟨a0, Finset.mem_univ a0, by
              have hscalar : (1 / 2 : ℝ) < 1 - η := by linarith
              have hhalf : chartMass a0 / 2 < (1 - η) * chartMass a0 := by
                rw [div_eq_mul_inv]
                norm_num
                simpa [mul_comm] using mul_lt_mul_of_pos_right hscalar
                  (hv.trans_le (hchartMass a0))
              exact hhalf.trans (hn' a0)⟩
        linarith
      rcases exists_opposite_majority_interface adj majority hconn hin hout with
        ⟨a, b, ha, hb, hab⟩
      have haLow : η * chartMass a ≤ insideMass a := by
        exact (mul_le_mul_of_nonneg_right (show η ≤ 1 - η by linarith)
          (hchart0 a)).trans ha.le
      have hJglobal : Jstar ≤ globalCut :=
        (hinterface a b hab haLow (le_of_not_gt hb)).trans
          (hinterfaceGlobal a b)
      have hscale : (2 / Vstar) ^ ((2 : ℝ) / 3) *
          globalMass ^ ((2 : ℝ) / 3) ≤ 1 := by
        rw [← Real.mul_rpow (by positivity) hglobal0]
        have hb : 2 / Vstar * globalMass ≤ 1 := by
          have hh : 2 * globalMass ≤ Vstar := by nlinarith [hglobalHalf, htotal]
          calc
            2 / Vstar * globalMass = (2 * globalMass) / Vstar := by ring
            _ ≤ 1 := (div_le_one hV).2 hh
        simpa using Real.rpow_le_one (by positivity) hb (by norm_num)
      calc
        min (I0 * (2 * η * vstar / Vstar) ^ ((2 : ℝ) / 3))
            (Jstar * (2 / Vstar) ^ ((2 : ℝ) / 3)) *
            globalMass ^ ((2 : ℝ) / 3) ≤
            Jstar * (2 / Vstar) ^ ((2 : ℝ) / 3) *
            globalMass ^ ((2 : ℝ) / 3) := by gcongr; exact min_le_right _ _
        _ ≤ Jstar := by rw [mul_assoc]; nlinarith
        _ ≤ globalCut := hJglobal
    · push_neg at hin
      have hallLow (a : ι) : insideMass a < η * chartMass a :=
        (hcolour a).resolve_right (hin a)
      have hminEq (a : ι) :
          min (insideMass a) (chartMass a - insideMass a) = insideMass a := by
        rw [min_eq_left]
        nlinarith [hηhalf, hchart0 a, (hallLow a).le]
      have hsumPow : globalMass ^ ((2 : ℝ) / 3) ≤
          ∑ a, insideMass a ^ ((2 : ℝ) / 3) := by
        rw [hmassSum]
        exact rpow_sum_le_sum_rpow Finset.univ insideMass ((2 : ℝ) / 3)
          (fun a _ => hinside0 a) (by norm_num) (by norm_num)
      have hlocalSum : I0 * globalMass ^ ((2 : ℝ) / 3) ≤ globalCut := by
        calc
          _ ≤ I0 * ∑ a, insideMass a ^ ((2 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_left hsumPow hI
          _ = ∑ a, I0 * insideMass a ^ ((2 : ℝ) / 3) := by rw [Finset.mul_sum]
          _ ≤ ∑ a, localCut a := Finset.sum_le_sum fun a _ => by
            simpa [hminEq a] using hlocal a
          _ ≤ globalCut := hlocalAggregate
      have hvV : vstar ≤ Vstar := by
        let a : ι := Classical.choice inferInstance
        calc vstar ≤ chartMass a := hchartMass a
          _ ≤ ∑ i, chartMass i := Finset.single_le_sum (fun i _ => hchart0 i)
            (Finset.mem_univ a)
          _ = totalMass := hchartSum.symm
          _ ≤ Vstar := htotal
      have hfactor : (2 * η * vstar / Vstar) ^ ((2 : ℝ) / 3) ≤ 1 := by
        apply Real.rpow_le_one (by positivity) (by
          apply (div_le_iff₀ hV).2
          nlinarith) (by norm_num)
      calc
        min (I0 * (2 * η * vstar / Vstar) ^ ((2 : ℝ) / 3))
            (Jstar * (2 / Vstar) ^ ((2 : ℝ) / 3)) *
            globalMass ^ ((2 : ℝ) / 3) ≤
            I0 * (2 * η * vstar / Vstar) ^ ((2 : ℝ) / 3) *
            globalMass ^ ((2 : ℝ) / 3) := by gcongr; exact min_le_left _ _
        _ ≤ I0 * globalMass ^ ((2 : ℝ) / 3) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_left (Real.rpow_nonneg hglobal0 _) hfactor) hI
        _ ≤ globalCut := hlocalSum

end NCG
