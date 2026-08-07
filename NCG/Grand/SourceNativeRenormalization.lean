/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GramHelpers

/-!
# Canonical source-native router and Pythagoras
  (`thm:source-native-renormalization`,
  Gran-Tensor manuscript)

* `source_native_renormalization`: for source syntheses
  `S_m, S_n`, a carrier isometry `I` (`IᴴI = 1`), and the
  minimum-norm router `Z = S_n†·I·S_m` (with
  `S_n† = (S_nᴴS_n)⁻¹S_nᴴ` on a saturating new source):
  (i) the boxed transport Pythagoras
      `G_m = Zᴴ·G_n·Z + RᴴR` with the old-source residual
      `R = (I - P_n)·I·S_m`;
  (ii) exact metric transport holds iff the residual
      vanishes;
  (iii) the independent new-source innovation
      `𝕀ⁿᵉʷ = S_nᴴ(I - I·P_m·Iᴴ)S_n` is positive whenever
      `P_m` is an orthogonal projection.
-/

open Matrix
open scoped ComplexOrder

set_option linter.unusedSimpArgs false

namespace NCG

/-- `thm:source-native-renormalization`. -/
theorem source_native_renormalization {Hm Hn Em En : Type*}
    [Fintype Hm] [Fintype Hn] [Fintype En]
    [DecidableEq Hm] [DecidableEq Hn] [DecidableEq En]
    (Sm : Matrix Hm Em ℂ) (Sn : Matrix Hn En ℂ)
    (I0 : Matrix Hn Hm ℂ) (hI : I0ᴴ * I0 = 1)
    [Invertible (Snᴴ * Sn)] :
    -- (i) the boxed router Pythagoras
    Smᴴ * Sm
      = ((Snᴴ * Sn)⁻¹ * Snᴴ * (I0 * Sm))ᴴ * (Snᴴ * Sn)
          * ((Snᴴ * Sn)⁻¹ * Snᴴ * (I0 * Sm))
        + ((1 - Sn * (Snᴴ * Sn)⁻¹ * Snᴴ) * (I0 * Sm))ᴴ
          * ((1 - Sn * (Snᴴ * Sn)⁻¹ * Snᴴ) * (I0 * Sm))
    -- (ii) exact transport ↔ zero old-source residual
    ∧ (Smᴴ * Sm
        = ((Snᴴ * Sn)⁻¹ * Snᴴ * (I0 * Sm))ᴴ * (Snᴴ * Sn)
          * ((Snᴴ * Sn)⁻¹ * Snᴴ * (I0 * Sm))
      ↔ (1 - Sn * (Snᴴ * Sn)⁻¹ * Snᴴ) * (I0 * Sm) = 0)
    -- (iii) the new-source innovation is positive
    ∧ (∀ Pm : Matrix Hm Hm ℂ, Pmᴴ = Pm → Pm * Pm = Pm →
        (Snᴴ * ((1 - I0 * Pm * I0ᴴ) * Sn)).PosSemidef) := by
  have hGH : (Snᴴ * Sn)ᴴ = Snᴴ * Sn := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hGinvH : ((Snᴴ * Sn)⁻¹)ᴴ = (Snᴴ * Sn)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hGH]
  have hmain : Smᴴ * Sm
      = ((Snᴴ * Sn)⁻¹ * Snᴴ * (I0 * Sm))ᴴ * (Snᴴ * Sn)
          * ((Snᴴ * Sn)⁻¹ * Snᴴ * (I0 * Sm))
        + ((1 - Sn * (Snᴴ * Sn)⁻¹ * Snᴴ) * (I0 * Sm))ᴴ
          * ((1 - Sn * (Snᴴ * Sn)⁻¹ * Snᴴ)
            * (I0 * Sm)) := by
    have hcore : ((Snᴴ * Sn)⁻¹ * Snᴴ * (I0 * Sm))ᴴ
        * (Snᴴ * Sn)
        * ((Snᴴ * Sn)⁻¹ * Snᴴ * (I0 * Sm))
        = (I0 * Sm)ᴴ
          * (Sn * ((Snᴴ * Sn)⁻¹ * (Snᴴ * (I0 * Sm)))) := by
      simp only [Matrix.conjTranspose_mul, hGinvH,
        Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc, proj_cancel Sn]
    rw [hcore]
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hGinvH, Matrix.conjTranspose_conjTranspose,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]
    simp only [Matrix.mul_assoc, proj_cancel Sn,
      cancel_left hI]
    abel
  refine ⟨hmain, ?_, ?_⟩
  · constructor
    · intro hexact
      have h0 : ((1 - Sn * (Snᴴ * Sn)⁻¹ * Snᴴ)
          * (I0 * Sm))ᴴ
          * ((1 - Sn * (Snᴴ * Sn)⁻¹ * Snᴴ) * (I0 * Sm))
          = 0 := by
        have h := hmain
        rw [← hexact] at h
        have h2 := h.symm
        rwa [add_eq_left] at h2
      exact Matrix.conjTranspose_mul_self_eq_zero.mp h0
    · intro h0
      rw [hmain, h0, Matrix.conjTranspose_zero,
        Matrix.zero_mul, add_zero]
  · intro Pm hPmH hPm2
    have hPmProj : ∀ X : Matrix Hm En ℂ,
        Pm * (Pm * X) = Pm * X := fun X => by
      rw [← Matrix.mul_assoc, hPm2]
    have hfac : Snᴴ * ((1 - I0 * Pm * I0ᴴ) * Sn)
        = ((1 - I0 * Pm * I0ᴴ) * Sn)ᴴ
          * ((1 - I0 * Pm * I0ᴴ) * Sn) := by
      simp only [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        hPmH, Matrix.conjTranspose_conjTranspose,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one]
      simp only [Matrix.mul_assoc, cancel_left hI, hPmProj]
      abel
    rw [hfac]
    exact Matrix.posSemidef_conjTranspose_mul_self _

end NCG
