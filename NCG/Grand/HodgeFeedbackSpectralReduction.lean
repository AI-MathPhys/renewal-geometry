/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FeedbackTail
import NCG.Grand.OperationalSobolevWeylFiniteGraph

/-!
# Hodge spectral reduction for loaded feedback

The finite-dimensional min--max step and its Weyl-count consequence for
`thm:Hodge-feedback-tail`.
-/

open scoped BigOperators

noncomputable section

namespace NCG

/-- Abstract finite-dimensional Courant--Fischer step in spectral-projection
form.  The spatial low-mode projection is injective on the loaded low carrier:
otherwise a nonzero vector would simultaneously obey the Hodge upper energy
bound and the complementary spatial spectral lower bound. -/
theorem hodge_low_mode_projection_injective
    {V L : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup L] [NormedSpace ℝ L]
    (P : Submodule ℝ V) (spatialLow : V →ₗ[ℝ] L)
    (spatialEnergy : V → ℝ) (R cH CH : ℝ)
    (hcH : 0 < cH)
    (hHodgeLow : ∀ u : P,
      cH * spatialEnergy u - CH * ‖(u : V)‖ ^ 2
        ≤ R * ‖(u : V)‖ ^ 2)
    (hSpatialHigh : ∀ v : V, spatialLow v = 0 → v ≠ 0 →
      ((R + CH) / cH) * ‖v‖ ^ 2 < spatialEnergy v) :
    Function.Injective (spatialLow.domRestrict P) := by
  rw [← LinearMap.ker_eq_bot]
  ext u
  constructor
  · intro hu
    have hproj : spatialLow (u : V) = 0 := by
      simpa using hu
    by_contra hune
    have huneV : (u : V) ≠ 0 := by
      intro hz
      exact hune (Subtype.ext hz)
    have hhigh := hSpatialHigh (u : V) hproj huneV
    have hlow := hHodgeLow u
    have hcH0 : cH ≠ 0 := hcH.ne'
    have hnorm : 0 ≤ ‖(u : V)‖ ^ 2 := sq_nonneg _
    have hupper : spatialEnergy (u : V) ≤
        ((R + CH) / cH) * ‖(u : V)‖ ^ 2 := by
      have hmul : cH * spatialEnergy (u : V) ≤
          (R + CH) * ‖(u : V)‖ ^ 2 := by nlinarith
      calc
        spatialEnergy (u : V) ≤
            ((R + CH) * ‖(u : V)‖ ^ 2) / cH :=
              (le_div_iff₀ hcH).2 (by simpa [mul_comm] using hmul)
        _ = ((R + CH) / cH) * ‖(u : V)‖ ^ 2 := by ring
    exact (not_lt_of_ge hupper) hhigh
  · intro hu
    simp only [Submodule.mem_bot] at hu
    subst u
    simp

/-- The low loaded carrier has dimension at most the spatial low-mode count. -/
theorem hodge_low_mode_finrank_le
    {V L : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup L] [NormedSpace ℝ L]
    [FiniteDimensional ℝ L]
    (P : Submodule ℝ V) (spatialLow : V →ₗ[ℝ] L)
    (spatialEnergy : V → ℝ) (R cH CH : ℝ)
    (hcH : 0 < cH)
    (hHodgeLow : ∀ u : P,
      cH * spatialEnergy u - CH * ‖(u : V)‖ ^ 2
        ≤ R * ‖(u : V)‖ ^ 2)
    (hSpatialHigh : ∀ v : V, spatialLow v = 0 → v ≠ 0 →
      ((R + CH) / cH) * ‖v‖ ^ 2 < spatialEnergy v) :
    Module.finrank ℝ P ≤ Module.finrank ℝ L := by
  exact LinearMap.finrank_le_finrank_of_injective
    (hodge_low_mode_projection_injective P spatialLow spatialEnergy
      R cH CH hcH hHodgeLow hSpatialHigh)

/-- Scalar assembly of the operational Weyl count after the Hodge threshold
change `λ=(R+C_H)/c_H`. -/
theorem hodge_weyl_envelope
    (N CW R cH CH : ℝ) (hcH : 0 < cH)
    (hR : 0 ≤ R) (hCH : 0 ≤ CH)
    (hcount : N ≤ CW * (1 + ((R + CH) / cH) ^ ((3 : ℝ) / 2)))
    (hCW : 0 ≤ CW) :
    N ≤ CW * (1 + (2 : ℝ) ^ ((3 : ℝ) / 2) *
        (1 + CH) ^ ((3 : ℝ) / 2) /
        cH ^ ((3 : ℝ) / 2)) * (1 + R ^ ((3 : ℝ) / 2)) := by
  have hbase : 0 ≤ (R + CH) / cH := by positivity
  have hcbase : 0 ≤ cH := hcH.le
  have hsum : R + CH ≤ (1 + CH) * (1 + R) := by nlinarith
  have hpow : ((R + CH) / cH) ^ ((3 : ℝ) / 2) ≤
      (2 : ℝ) ^ ((3 : ℝ) / 2) *
        ((1 + CH) / cH) ^ ((3 : ℝ) / 2) *
        (1 + R ^ ((3 : ℝ) / 2)) := by
    have hdiv : (R + CH) / cH ≤ ((1 + CH) / cH) * (1 + R) := by
      apply (div_le_iff₀ hcH).2
      field_simp [hcH.ne']
      nlinarith
    have hmono := Real.rpow_le_rpow hbase hdiv (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [Real.mul_rpow (by positivity) (by positivity)] at hmono
    have hone : (1 + R) ^ ((3 : ℝ) / 2) ≤
        (2 : ℝ) ^ ((3 : ℝ) / 2) *
          (1 + R ^ ((3 : ℝ) / 2)) := by
      by_cases hR1 : R ≤ 1
      · have hbasele : 1 + R ≤ 2 := by linarith
        have hp := Real.rpow_le_rpow (by positivity) hbasele
          (by norm_num : (0 : ℝ) ≤ 3 / 2)
        have hRp0 : 0 ≤ R ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hR _
        have honeR : 1 ≤ 1 + R ^ ((3 : ℝ) / 2) := by linarith
        calc
          _ ≤ (2 : ℝ) ^ ((3 : ℝ) / 2) := hp
          _ ≤ _ := le_mul_of_one_le_right (Real.rpow_nonneg (by norm_num) _) honeR
      · have hRge : 1 ≤ R := le_of_not_ge hR1
        have hbasele : 1 + R ≤ 2 * R := by linarith
        have hp := Real.rpow_le_rpow (by positivity) hbasele
          (by norm_num : (0 : ℝ) ≤ 3 / 2)
        rw [Real.mul_rpow (by norm_num) hR] at hp
        have hRp0 : 0 ≤ R ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hR _
        have hRp : R ^ ((3 : ℝ) / 2) ≤
            1 + R ^ ((3 : ℝ) / 2) := by linarith
        exact hp.trans (mul_le_mul_of_nonneg_left hRp
          (Real.rpow_nonneg (by norm_num) _))
    calc
      _ ≤ (((1 + CH) / cH) ^ ((3 : ℝ) / 2)) *
          ((1 + R) ^ ((3 : ℝ) / 2)) := hmono
      _ ≤ _ := by
        have hA : 0 ≤ ((1 + CH) / cH) ^ ((3 : ℝ) / 2) :=
          Real.rpow_nonneg (by positivity) _
        calc
          _ ≤ ((1 + CH) / cH) ^ ((3 : ℝ) / 2) *
              ((2 : ℝ) ^ ((3 : ℝ) / 2) *
                (1 + R ^ ((3 : ℝ) / 2))) :=
            mul_le_mul_of_nonneg_left hone hA
          _ = _ := by ring
  calc
    N ≤ CW * (1 + ((R + CH) / cH) ^ ((3 : ℝ) / 2)) := hcount
    _ ≤ CW * (1 + (2 : ℝ) ^ ((3 : ℝ) / 2) *
          (((1 + CH) / cH) ^ ((3 : ℝ) / 2)) *
          (1 + R ^ ((3 : ℝ) / 2))) := by gcongr
    _ ≤ CW * (1 + (2 : ℝ) ^ ((3 : ℝ) / 2) *
        (1 + CH) ^ ((3 : ℝ) / 2) /
        cH ^ ((3 : ℝ) / 2)) * (1 + R ^ ((3 : ℝ) / 2)) := by
      rw [Real.div_rpow (by positivity) hcbase]
      have hRp : 0 ≤ R ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hR _
      have hCp : 0 ≤ (1 + CH) ^ ((3 : ℝ) / 2) /
          cH ^ ((3 : ℝ) / 2) := by positivity
      have htwo : 1 ≤ (2 : ℝ) ^ ((3 : ℝ) / 2) :=
        Real.one_le_rpow (by norm_num) (by norm_num)
      have honeRp : 0 ≤ 1 + R ^ ((3 : ℝ) / 2) := by linarith
      calc
        _ = CW * (1 + (2 : ℝ) ^ ((3 : ℝ) / 2) *
            ((1 + CH) ^ ((3 : ℝ) / 2) / cH ^ ((3 : ℝ) / 2)) *
            (1 + R ^ ((3 : ℝ) / 2))) := by ring
        _ ≤ CW * (1 + (2 : ℝ) ^ ((3 : ℝ) / 2) *
            ((1 + CH) ^ ((3 : ℝ) / 2) / cH ^ ((3 : ℝ) / 2))) *
            (1 + R ^ ((3 : ℝ) / 2)) := by nlinarith
        _ = _ := by ring

end NCG
