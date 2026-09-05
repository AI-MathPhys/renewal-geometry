/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FieldTightness
import NCG.Grand.RenewalLyapunovStateTightness

/-!
# Exact field tightness for finite spectral laws

This module applies the scalar hard/soft tail comparison to the genuine
spectral probability laws of a family of finite Hermitian matrices in density
states.  It proves the uniform tightness equivalence, identifies both profiles
with functional-calculus expectations, and extracts an escaping positive-mass
spectral projection whenever tightness fails.
-/

open Filter Finset

namespace NCG

open RenewalLyapunovStateTightness
open Upstream.PrimitiveWeight

/-- Hard spectral tail of the `j`th regulated field. -/
noncomputable def fieldSpectralTailMass
    (dim : ℕ → ℕ)
    (rho F : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hF : ∀ j, (F j).IsHermitian) (j : ℕ) (R : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => R < |(hF j).eigenvalues i|),
    spectralWeight (rho j) (F j) (hF j) i

/-- Soft resolvent tail of the `j`th regulated field. -/
noncomputable def fieldSoftTailMass
    (dim : ℕ → ℕ)
    (rho F : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hF : ∀ j, (F j).IsHermitian) (j : ℕ) (R : ℝ) : ℝ :=
  ∑ i, spectralWeight (rho j) (F j) (hF j) i *
    ((hF j).eigenvalues i) ^ 2 /
      (((hF j).eigenvalues i) ^ 2 + R ^ 2)

/-- Uniform vanishing at infinity for a family of nonnegative tail profiles. -/
def UniformTailVanishes (p : ℕ → ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ R, ∀ j S, R ≤ S → p j S < ε

/-- The hard tail is the expectation of the spectral projection selected by
the indicator of `|x| > R`. -/
theorem matrixStateValue_tailProjection_eq
    (dim : ℕ → ℕ)
    (rho F : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hF : ∀ j, (F j).IsHermitian) (j : ℕ) (R : ℝ) :
    matrixStateValue (rho j)
        ((hF j).cfc (fun x => if R < |x| then 1 else 0)) =
      fieldSpectralTailMass dim rho F hF j R := by
  rw [matrixStateValue_cfc_eq_spectralSum]
  simp [fieldSpectralTailMass, Finset.sum_filter]

/-- The soft tail is exactly the expectation of
`F² / (F² + R²)`. -/
theorem matrixStateValue_softTail_eq
    (dim : ℕ → ℕ)
    (rho F : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hF : ∀ j, (F j).IsHermitian) (j : ℕ) (R : ℝ) :
    matrixStateValue (rho j)
        ((hF j).cfc (fun x => x ^ 2 / (x ^ 2 + R ^ 2))) =
      fieldSoftTailMass dim rho F hF j R := by
  rw [matrixStateValue_cfc_eq_spectralSum]
  unfold fieldSoftTailMass
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Pointwise hard-to-soft comparison for the actual spectral law. -/
theorem fieldSpectralTailMass_le_two_soft
    (dim : ℕ → ℕ)
    (rho F : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hrho : ∀ j, rho j ∈ densitySet (dim j) ℂ)
    (hF : ∀ j, (F j).IsHermitian) (j : ℕ) {R : ℝ} (hR : 0 < R) :
    fieldSpectralTailMass dim rho F hF j R ≤
      2 * fieldSoftTailMass dim rho F hF j R := by
  rw [fieldSpectralTailMass, fieldSoftTailMass, Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : R < |(hF j).eigenvalues i|
  · rw [if_pos hi]
    let w := spectralWeight (rho j) (F j) (hF j) i
    let x := (hF j).eigenvalues i
    have hw : 0 ≤ w := spectralWeight_nonneg (hrho j) (hF j) i
    have hs := field_tightness_alternative.1 x R hR hi
    have hm := mul_le_mul_of_nonneg_left hs hw
    dsimp [w, x] at hm ⊢
    convert hm using 1 <;> ring
  · rw [if_neg hi]
    have hw := spectralWeight_nonneg (hrho j) (hF j) i
    have hden : 0 < ((hF j).eigenvalues i) ^ 2 + R ^ 2 := by positivity
    exact mul_nonneg (by norm_num)
      (div_nonneg (mul_nonneg hw (sq_nonneg _)) hden.le)

/-- Pointwise soft-tail comparison with a fixed hard window. -/
theorem fieldSoftTailMass_le_hard_add
    (dim : ℕ → ℕ)
    (rho F : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hrho : ∀ j, rho j ∈ densitySet (dim j) ℂ)
    (hF : ∀ j, (F j).IsHermitian) (j : ℕ)
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S) :
    fieldSoftTailMass dim rho F hF j S ≤
      fieldSpectralTailMass dim rho F hF j R +
        R ^ 2 / (R ^ 2 + S ^ 2) := by
  let c := R ^ 2 / (R ^ 2 + S ^ 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hterm : ∀ i : Fin (dim j),
      spectralWeight (rho j) (F j) (hF j) i *
          ((hF j).eigenvalues i) ^ 2 /
            (((hF j).eigenvalues i) ^ 2 + S ^ 2) ≤
        (if R < |(hF j).eigenvalues i| then
          spectralWeight (rho j) (F j) (hF j) i else 0) +
        spectralWeight (rho j) (F j) (hF j) i * c := by
    intro i
    let w := spectralWeight (rho j) (F j) (hF j) i
    let x := (hF j).eigenvalues i
    have hw : 0 ≤ w := spectralWeight_nonneg (hrho j) (hF j) i
    by_cases hx : R < |x|
    · rw [if_pos hx]
      have hfrac : x ^ 2 / (x ^ 2 + S ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [sq_nonneg S]
      have hnonneg : 0 ≤ x ^ 2 / (x ^ 2 + S ^ 2) := by positivity
      have hm := mul_le_mul_of_nonneg_left hfrac hw
      dsimp [w, x] at hm ⊢
      have hm' : spectralWeight (rho j) (F j) (hF j) i *
            ((hF j).eigenvalues i) ^ 2 /
              (((hF j).eigenvalues i) ^ 2 + S ^ 2) ≤
          spectralWeight (rho j) (F j) (hF j) i := by
        calc
          spectralWeight (rho j) (F j) (hF j) i *
                ((hF j).eigenvalues i) ^ 2 /
                  (((hF j).eigenvalues i) ^ 2 + S ^ 2)
              = spectralWeight (rho j) (F j) (hF j) i *
                  (((hF j).eigenvalues i) ^ 2 /
                    (((hF j).eigenvalues i) ^ 2 + S ^ 2)) := by ring
          _ ≤ spectralWeight (rho j) (F j) (hF j) i * 1 := hm
          _ = spectralWeight (rho j) (F j) (hF j) i := mul_one _
      exact hm'.trans (le_add_of_nonneg_right (mul_nonneg hw hc))
    · rw [if_neg hx, zero_add]
      have hxR : |x| ≤ R := le_of_not_gt hx
      have hs := field_tightness_alternative.2.1 x R S hR hS hxR
      have hm := mul_le_mul_of_nonneg_left hs hw
      dsimp [w, x, c] at hm ⊢
      calc
        spectralWeight (rho j) (F j) (hF j) i *
              ((hF j).eigenvalues i) ^ 2 /
                (((hF j).eigenvalues i) ^ 2 + S ^ 2)
            = spectralWeight (rho j) (F j) (hF j) i *
                (((hF j).eigenvalues i) ^ 2 /
                  (((hF j).eigenvalues i) ^ 2 + S ^ 2)) := by ring
        _ ≤ spectralWeight (rho j) (F j) (hF j) i *
              (R ^ 2 / (R ^ 2 + S ^ 2)) := hm
  calc
    fieldSoftTailMass dim rho F hF j S
        ≤ ∑ i, ((if R < |(hF j).eigenvalues i| then
              spectralWeight (rho j) (F j) (hF j) i else 0) +
            spectralWeight (rho j) (F j) (hF j) i * c) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = fieldSpectralTailMass dim rho F hF j R + c := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,
        spectralWeight_sum_one (hrho j) (hF j), one_mul]
      simp [fieldSpectralTailMass, Finset.sum_filter]
    _ = fieldSpectralTailMass dim rho F hF j R +
        R ^ 2 / (R ^ 2 + S ^ 2) := rfl

/-- Exact uniform hard/soft field-tightness equivalence for finite Hermitian
spectral laws in density states. -/
theorem exactFieldTightness_iff_softTail
    (dim : ℕ → ℕ)
    (rho F : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hrho : ∀ j, rho j ∈ densitySet (dim j) ℂ)
    (hF : ∀ j, (F j).IsHermitian) :
    UniformTailVanishes (fieldSpectralTailMass dim rho F hF) ↔
      UniformTailVanishes (fieldSoftTailMass dim rho F hF) := by
  constructor
  · intro hhard ε hε
    obtain ⟨R₀, hR₀⟩ := hhard (ε / 2) (by positivity)
    let R := max R₀ 1
    have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
    let S₀ := max R (R * Real.sqrt (2 / ε))
    refine ⟨S₀, ?_⟩
    intro j S hS
    have hRS : R ≤ S := (le_max_left _ _).trans hS
    have hSpos : 0 < S := hR.trans_le hRS
    have hhard' : fieldSpectralTailMass dim rho F hF j R < ε / 2 :=
      hR₀ j R (le_max_left _ _)
    have hsqrt : R * Real.sqrt (2 / ε) ≤ S :=
      (le_max_right _ _).trans hS
    have htail : R ^ 2 / (R ^ 2 + S ^ 2) ≤ ε / 2 := by
      have hsq : R ^ 2 * (2 / ε) ≤ S ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hsqrt 2
        rwa [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / ε)] at this
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hscaled := mul_le_mul_of_nonneg_right hsq hε.le
      field_simp at hscaled
      nlinarith [sq_nonneg R]
    calc
      fieldSoftTailMass dim rho F hF j S
          ≤ fieldSpectralTailMass dim rho F hF j R +
              R ^ 2 / (R ^ 2 + S ^ 2) :=
        fieldSoftTailMass_le_hard_add dim rho F hrho hF j hR hSpos
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hhard' htail
      _ = ε := by ring
  · intro hsoft ε hε
    obtain ⟨R, hR⟩ := hsoft (ε / 2) (by positivity)
    refine ⟨max R 1, ?_⟩
    intro j S hS
    have hSpos : 0 < S := one_pos.trans_le ((le_max_right R 1).trans hS)
    calc
      fieldSpectralTailMass dim rho F hF j S
          ≤ 2 * fieldSoftTailMass dim rho F hF j S :=
        fieldSpectralTailMass_le_two_soft dim rho F hrho hF j hSpos
      _ < 2 * (ε / 2) := mul_lt_mul_of_pos_left
        (hR j S ((le_max_left R 1).trans hS)) (by norm_num)
      _ = ε := by ring

/-- Failure of uniform field tightness yields a sequence of cutoffs and radii
escaping to infinity whose spectral projections retain a fixed positive
mass. -/
theorem fieldNontightness_extracts_massEscape
    (dim : ℕ → ℕ)
    (rho F : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hF : ∀ j, (F j).IsHermitian)
    (hfail : ¬ UniformTailVanishes (fieldSpectralTailMass dim rho F hF)) :
    ∃ ε > 0, ∃ cutoff : ℕ → ℕ, ∃ radius : ℕ → ℝ,
      Tendsto radius atTop atTop ∧
      ∀ m, ε ≤ fieldSpectralTailMass dim rho F hF (cutoff m) (radius m) := by
  unfold UniformTailVanishes at hfail
  push Not at hfail
  obtain ⟨ε, hε, hbad⟩ := hfail
  choose cutoff radius hrad hmass using fun m : ℕ => hbad m
  refine ⟨ε, hε, cutoff, radius, ?_, hmass⟩
  rw [tendsto_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge b
  filter_upwards [eventually_ge_atTop N] with m hm
  exact hN.trans ((Nat.cast_le.mpr hm).trans (hrad m))

end NCG
