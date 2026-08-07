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

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

omit [Fintype β] [Fintype γ] in
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
  -- fiber cards over the first coordinate
  have hA : A.card
      = ∑ a : α, (A.filter fun p => p.1 = a).card :=
    card_eq_sum_card_fiberwise fun x _ => mem_univ x.1
  have h12 : P12.card
      = ∑ a : α, (P12.filter fun q => q.1 = a).card :=
    card_eq_sum_card_fiberwise fun x _ => mem_univ x.1
  have h13 : P13.card
      = ∑ a : α, (P13.filter fun q => q.1 = a).card :=
    card_eq_sum_card_fiberwise fun x _ => mem_univ x.1
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
  have hkey := sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset α)
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

end NCG
