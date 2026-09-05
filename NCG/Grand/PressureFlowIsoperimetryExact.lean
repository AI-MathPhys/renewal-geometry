/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GlobalSpatialCompiler

/-!
# Exact pressure-flow characterization of spatial isoperimetry

This file performs the pressure-demand instantiation left open in the earlier
finite max-flow/min-cut development.  In particular it proves the manuscript's
two-thirds-power cut estimate for the actual centered pressure demand and
assembles the uniform isoperimetric-margin / physical-current equivalence.
-/

open Finset

namespace NCG
namespace PressureFlowIsoperimetry

open GlobalSpatialCompiler

private theorem scaled_min_twoThird_le
    (a b scale : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hscale : 0 ≤ scale) (hscaleA : scale ≤ a ^ ((2 : ℝ) / 3)) :
    scale / a * min a b ≤ b ^ ((2 : ℝ) / 3) := by
  by_cases hb0 : b = 0
  · subst b
    rw [min_eq_right ha.le]
    norm_num
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  by_cases hba : b ≤ a
  · rw [min_eq_right hba]
    have hratio0 : 0 ≤ b / a := div_nonneg hb ha.le
    have hratio1 : b / a ≤ 1 := (div_le_one ha).2 hba
    have hratioPow : b / a ≤ (b / a) ^ ((2 : ℝ) / 3) := by
      calc
        b / a = (b / a) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ (b / a) ^ ((2 : ℝ) / 3) :=
          Real.rpow_le_rpow_of_exponent_ge (div_pos hbpos ha) hratio1 (by norm_num)
    have hmul : scale * (b / a) ≤
        a ^ ((2 : ℝ) / 3) * (b / a) :=
      mul_le_mul_of_nonneg_right hscaleA hratio0
    have hpowmul :
        a ^ ((2 : ℝ) / 3) * (b / a) ^ ((2 : ℝ) / 3) =
          b ^ ((2 : ℝ) / 3) := by
      rw [← Real.mul_rpow ha.le hratio0]
      congr 1
      field_simp
    calc
      scale / a * b = scale * (b / a) := by field_simp
      _ ≤ a ^ ((2 : ℝ) / 3) * (b / a) := hmul
      _ ≤ a ^ ((2 : ℝ) / 3) * (b / a) ^ ((2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left hratioPow (Real.rpow_nonneg ha.le _)
      _ = b ^ ((2 : ℝ) / 3) := hpowmul
  · have hab : a ≤ b := le_of_not_ge hba
    rw [min_eq_left hab]
    have hcancel : scale / a * a = scale := div_mul_cancel₀ scale ha.ne'
    rw [hcancel]
    exact hscaleA.trans (Real.rpow_le_rpow ha.le hab (by norm_num))

theorem cutMass_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (mass : V → ℝ) (hmass : ∀ v, 0 ≤ mass v) (A : Finset V) :
    0 ≤ cutMass mass A := by
  exact Finset.sum_nonneg fun v _ => hmass v

theorem cutMass_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    (mass : V → ℝ) (hmass : ∀ v, 0 ≤ mass v)
    {A B : Finset V} (hAB : A ⊆ B) :
    cutMass mass A ≤ cutMass mass B := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun v _ _ => hmass v

theorem pressureDemand_sum_eq_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (mass : V → ℝ) (A B : Finset V) (scale : ℝ) :
    ∑ v ∈ B, pressureDemand mass A scale v =
      scale / cutMass mass A * cutMass mass (B ∩ A) -
        scale / cutMass mass Aᶜ * cutMass mass (B ∩ Aᶜ) := by
  classical
  have hin : B.filter (fun v => v ∈ A) = B ∩ A := by
    ext v
    simp
  have hout : B.filter (fun v => ¬ v ∈ A) = B ∩ Aᶜ := by
    ext v
    simp
  calc
    (∑ v ∈ B, pressureDemand mass A scale v) =
        (∑ v ∈ B.filter (fun v => v ∈ A), pressureDemand mass A scale v) +
          ∑ v ∈ B.filter (fun v => ¬ v ∈ A), pressureDemand mass A scale v := by
            exact (Finset.sum_filter_add_sum_filter_not B
              (fun v => v ∈ A) (pressureDemand mass A scale)).symm
    _ = (scale / cutMass mass A) * (∑ v ∈ B ∩ A, mass v) +
          (-(scale / cutMass mass Aᶜ)) * (∑ v ∈ B ∩ Aᶜ, mass v) := by
      congr 1
      · rw [hin, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        rw [pressureDemand, if_pos (Finset.mem_inter.mp hv).2]
      · rw [hout, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        have hvA : v ∉ A := Finset.mem_compl.mp (Finset.mem_inter.mp hv).2
        rw [pressureDemand, if_neg hvA]
    _ = scale / cutMass mass A * cutMass mass (B ∩ A) -
          scale / cutMass mass Aᶜ * cutMass mass (B ∩ Aᶜ) := by
      unfold cutMass
      ring

/-- The actual dimension-three pressure demand has no larger imbalance on a
 test set than that test set's two-thirds mass. -/
theorem pressureDemand_abs_sum_le_cutMass_rpow
    {V : Type*} [Fintype V] [DecidableEq V]
    (mass : V → ℝ) (hmass : ∀ v, 0 ≤ mass v)
    (A B : Finset V)
    (hA : 0 < cutMass mass A)
    (hAc : 0 < cutMass mass Aᶜ)
    (hhalf : cutMass mass A ≤ cutMass mass Aᶜ) :
    |∑ v ∈ B,
        pressureDemand mass A (cutMass mass A ^ ((2 : ℝ) / 3)) v| ≤
      cutMass mass B ^ ((2 : ℝ) / 3) := by
  let a := cutMass mass A
  let ac := cutMass mass Aᶜ
  let b := cutMass mass B
  let x := cutMass mass (B ∩ A)
  let y := cutMass mass (B ∩ Aᶜ)
  let scale := a ^ ((2 : ℝ) / 3)
  have hb : 0 ≤ b := cutMass_nonneg mass hmass B
  have hx : 0 ≤ x := cutMass_nonneg mass hmass (B ∩ A)
  have hy : 0 ≤ y := cutMass_nonneg mass hmass (B ∩ Aᶜ)
  have hxa : x ≤ a := cutMass_mono mass hmass (Finset.inter_subset_right)
  have hxb : x ≤ b := cutMass_mono mass hmass (Finset.inter_subset_left)
  have hyac : y ≤ ac := cutMass_mono mass hmass (Finset.inter_subset_right)
  have hyb : y ≤ b := cutMass_mono mass hmass (Finset.inter_subset_left)
  have hscale : 0 ≤ scale := Real.rpow_nonneg hA.le _
  have hscaleAc : scale ≤ ac ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow hA.le hhalf (by norm_num)
  have hP : scale / a * x ≤ b ^ ((2 : ℝ) / 3) := by
    calc
      scale / a * x ≤ scale / a * min a b := by
        apply mul_le_mul_of_nonneg_left (le_min hxa hxb)
        exact div_nonneg hscale hA.le
      _ ≤ b ^ ((2 : ℝ) / 3) :=
        scaled_min_twoThird_le a b scale hA hb hscale le_rfl
  have hN : scale / ac * y ≤ b ^ ((2 : ℝ) / 3) := by
    calc
      scale / ac * y ≤ scale / ac * min ac b := by
        apply mul_le_mul_of_nonneg_left (le_min hyac hyb)
        exact div_nonneg hscale hAc.le
      _ ≤ b ^ ((2 : ℝ) / 3) :=
        scaled_min_twoThird_le ac b scale hAc hb hscale hscaleAc
  have hP0 : 0 ≤ scale / a * x :=
    mul_nonneg (div_nonneg hscale hA.le) hx
  have hN0 : 0 ≤ scale / ac * y :=
    mul_nonneg (div_nonneg hscale hAc.le) hy
  rw [pressureDemand_sum_eq_inter]
  change |scale / a * x - scale / ac * y| ≤ b ^ ((2 : ℝ) / 3)
  rw [abs_le]
  constructor <;> linarith

/-- The manuscript's sharp cut estimate: every pressure demand is controlled
by the smaller side of every test cut. -/
theorem canonical_pressureDemand_cut_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (mass : V → ℝ) (hmass : ∀ v, 0 ≤ mass v)
    (A B : Finset V)
    (hA : 0 < cutMass mass A)
    (hAc : 0 < cutMass mass Aᶜ)
    (hhalf : cutMass mass A ≤ cutMass mass Aᶜ) :
    |∑ v ∈ B,
        pressureDemand mass A (cutMass mass A ^ ((2 : ℝ) / 3)) v| ≤
      min (cutMass mass B) (cutMass mass Bᶜ) ^ ((2 : ℝ) / 3) := by
  have hcenter := pressureDemand_centered mass A
    (cutMass mass A ^ ((2 : ℝ) / 3)) hA.ne' hAc.ne'
  have hcomplEq :
      (∑ v ∈ B,
          pressureDemand mass A (cutMass mass A ^ ((2 : ℝ) / 3)) v) =
        -(∑ v ∈ Bᶜ,
          pressureDemand mass A (cutMass mass A ^ ((2 : ℝ) / 3)) v) := by
    have hpartition := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset V) (fun v => v ∈ B)
      (pressureDemand mass A (cutMass mass A ^ ((2 : ℝ) / 3)))
    have hfilter : Finset.univ.filter (fun v => v ∈ B) = B := by ext v; simp
    have hfilterc : Finset.univ.filter (fun v => ¬ v ∈ B) = Bᶜ := by ext v; simp
    rw [hfilter, hfilterc, hcenter] at hpartition
    linarith
  by_cases hBBc : cutMass mass B ≤ cutMass mass Bᶜ
  · rw [min_eq_left hBBc]
    exact pressureDemand_abs_sum_le_cutMass_rpow mass hmass A B hA hAc hhalf
  · rw [min_eq_right (le_of_not_ge hBBc), hcomplEq, abs_neg]
    exact pressureDemand_abs_sum_le_cutMass_rpow mass hmass A Bᶜ hA hAc hhalf

/-- Uniform three-dimensional cut margin in the physical masses and edge
capacities. -/
def SpatialIsoperimetricBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (mass : V → ℝ) (capacity : V → V → ℝ) (I : ℝ) : Prop :=
  ∀ B : Finset V,
    I * min (cutMass mass B) (cutMass mass Bᶜ) ^ ((2 : ℝ) / 3) ≤
      finiteCutCapacity capacity B

/-- Every canonical pressure demand on a positive half-volume cut is
physically routable with one uniform congestion bound. -/
def UniformCanonicalPressureRouting
    {V : Type*} [Fintype V] [DecidableEq V]
    (mass : V → ℝ) (capacity : V → V → ℝ) (κ : ℝ) : Prop :=
  ∀ A : Finset V,
    0 < cutMass mass A → cutMass mass A ≤ cutMass mass Aᶜ →
      ∃ current,
        current ∈ finiteCapacityCurrentSet capacity κ ∧
        finiteDivergence current =
          pressureDemand mass A (cutMass mass A ^ ((2 : ℝ) / 3))

theorem finiteCutCapacity_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (capacity : V → V → ℝ) (hcapacity : ∀ u v, 0 ≤ capacity u v)
    (A : Finset V) :
    0 ≤ finiteCutCapacity capacity A := by
  exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => hcapacity u v

theorem finiteCutCapacity_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (capacity : V → V → ℝ)
    (hsym : ∀ u v, capacity u v = capacity v u)
    (A : Finset V) :
    finiteCutCapacity capacity Aᶜ = finiteCutCapacity capacity A := by
  classical
  unfold finiteCutCapacity
  have hcc : (Aᶜ)ᶜ = A := by ext v; simp
  rw [hcc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ =>
    Finset.sum_congr rfl fun v _ => hsym v u

/-- Exact pressure-flow characterization at every positive margin.  This is
the manuscript's reciprocal relation in its order-theoretically equivalent
form: a cut constant `I` holds exactly when every canonical pressure demand
has congestion at most `I⁻¹`. -/
theorem pressure_flow_isoperimetry_exact
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (mass : V → ℝ) (hmass : ∀ v, 0 ≤ mass v)
    (capacity : V → V → ℝ)
    (hcapacity : ∀ u v, 0 ≤ capacity u v)
    (hsym : ∀ u v, capacity u v = capacity v u)
    (I : ℝ) (hI : 0 < I) :
    SpatialIsoperimetricBound mass capacity I ↔
      UniformCanonicalPressureRouting mass capacity I⁻¹ := by
  constructor
  · intro hIso A hA hhalf
    have hAc : 0 < cutMass mass Aᶜ := hA.trans_le hhalf
    apply finite_transshipment_maxCut_converse capacity hcapacity hsym
      (pressureDemand mass A (cutMass mass A ^ ((2 : ℝ) / 3))) I⁻¹
      (inv_nonneg.mpr hI.le)
      (pressureDemand_centered mass A
        (cutMass mass A ^ ((2 : ℝ) / 3)) hA.ne' hAc.ne')
    intro B
    have hdemand := canonical_pressureDemand_cut_bound
      mass hmass A B hA hAc hhalf
    have hiso := hIso B
    calc
      |∑ v ∈ B,
          pressureDemand mass A (cutMass mass A ^ ((2 : ℝ) / 3)) v|
          ≤ min (cutMass mass B) (cutMass mass Bᶜ) ^ ((2 : ℝ) / 3) := hdemand
      _ = I⁻¹ *
          (I * min (cutMass mass B) (cutMass mass Bᶜ) ^ ((2 : ℝ) / 3)) := by
            field_simp
      _ ≤ I⁻¹ * finiteCutCapacity capacity B :=
        mul_le_mul_of_nonneg_left hiso (inv_nonneg.mpr hI.le)
  · intro hRoute B
    let b := cutMass mass B
    let bc := cutMass mass Bᶜ
    have hb : 0 ≤ b := cutMass_nonneg mass hmass B
    have hbc : 0 ≤ bc := cutMass_nonneg mass hmass Bᶜ
    by_cases hsmall : b ≤ bc
    · rw [min_eq_left hsmall]
      by_cases hb0 : b = 0
      · rw [hb0, Real.zero_rpow (by norm_num : (2 : ℝ) / 3 ≠ 0), mul_zero]
        exact finiteCutCapacity_nonneg capacity hcapacity B
      · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        obtain ⟨j, hj, hjdiv⟩ := hRoute B hbpos hsmall
        have hflux := flow_cut_weak_duality j capacity hj.1 B I⁻¹ hj.2
        have hsum := pressureDemand_sum_cut mass B
          (b ^ ((2 : ℝ) / 3)) hbpos.ne'
        change (∑ v ∈ B, pressureDemand mass B (b ^ ((2 : ℝ) / 3)) v) =
          b ^ ((2 : ℝ) / 3) at hsum
        have hbound : b ^ ((2 : ℝ) / 3) ≤ I⁻¹ * finiteCutCapacity capacity B := by
          rw [← hsum, ← hjdiv]
          exact hflux
        calc
          I * b ^ ((2 : ℝ) / 3) ≤ I * (I⁻¹ * finiteCutCapacity capacity B) :=
            mul_le_mul_of_nonneg_left hbound hI.le
          _ = finiteCutCapacity capacity B := by field_simp
    · have hsmallc : bc ≤ b := le_of_not_ge hsmall
      rw [min_eq_right hsmallc]
      by_cases hbc0 : bc = 0
      · rw [hbc0, Real.zero_rpow (by norm_num : (2 : ℝ) / 3 ≠ 0), mul_zero]
        exact finiteCutCapacity_nonneg capacity hcapacity B
      · have hbcpos : 0 < bc := lt_of_le_of_ne hbc (Ne.symm hbc0)
        have hhalfC : cutMass mass Bᶜ ≤ cutMass mass (Bᶜ)ᶜ := by
          simpa using hsmallc
        obtain ⟨j, hj, hjdiv⟩ := hRoute Bᶜ hbcpos hhalfC
        have hflux := flow_cut_weak_duality j capacity hj.1 Bᶜ I⁻¹ hj.2
        have hsum := pressureDemand_sum_cut mass Bᶜ
          (bc ^ ((2 : ℝ) / 3)) hbcpos.ne'
        change (∑ v ∈ Bᶜ,
          pressureDemand mass Bᶜ (bc ^ ((2 : ℝ) / 3)) v) =
            bc ^ ((2 : ℝ) / 3) at hsum
        have hbound : bc ^ ((2 : ℝ) / 3) ≤
            I⁻¹ * finiteCutCapacity capacity Bᶜ := by
          rw [← hsum, ← hjdiv]
          exact hflux
        rw [finiteCutCapacity_compl capacity hsym B] at hbound
        calc
          I * bc ^ ((2 : ℝ) / 3) ≤ I * (I⁻¹ * finiteCutCapacity capacity B) :=
            mul_le_mul_of_nonneg_left hbound hI.le
          _ = finiteCutCapacity capacity B := by field_simp

end PressureFlowIsoperimetry
end NCG






