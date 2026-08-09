/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.SourceNativeRenormalization

/-!
# strict composition of source-native routers

`source_native_renormalization` proves the router Pythagoras, the exact
transport/zero-residual equivalence, and positivity of new-source innovation.
This file proves the remaining manuscript clause: on zero-old-residual arrows,
the reduced minimum-norm source routers compose strictly.
-/

open Matrix

namespace NCG

/-- The full-column-rank source-native router used in the manuscript. -/
noncomputable def sourceNativeRouter
    {Hs Ht Es Et : Type*} [Fintype Hs] [Fintype Ht]
    [Fintype Et] [DecidableEq Ht] [DecidableEq Et]
    (Ss : Matrix Hs Es ℂ) (St : Matrix Ht Et ℂ)
    (I : Matrix Ht Hs ℂ) [Invertible (Stᴴ * St)] : Matrix Et Es ℂ :=
  (Stᴴ * St)⁻¹ * Stᴴ * (I * Ss)

/-- Zero old-source residuals make both routers synthesize the embedded old
sources exactly; for a composable physical carrier cocycle, the corresponding
source-native routers then compose strictly. -/
theorem source_native_router_strict_composition
    {Hm Hn Hl Em En El : Type*}
    [Fintype Hm] [Fintype Hn] [Fintype Hl]
    [Fintype En] [Fintype El]
    [DecidableEq Hn] [DecidableEq Hl]
    [DecidableEq En] [DecidableEq El]
    (Sm : Matrix Hm Em ℂ) (Sn : Matrix Hn En ℂ)
    (Sl : Matrix Hl El ℂ)
    (Inm : Matrix Hn Hm ℂ) (Iln : Matrix Hl Hn ℂ)
    (Ilm : Matrix Hl Hm ℂ)
    [Invertible (Snᴴ * Sn)] [Invertible (Slᴴ * Sl)]
    (hcarrier : Ilm = Iln * Inm)
    (hres_nm :
      (1 - Sn * (Snᴴ * Sn)⁻¹ * Snᴴ) * (Inm * Sm) = 0)
    (hres_ln :
      (1 - Sl * (Slᴴ * Sl)⁻¹ * Slᴴ) * (Iln * Sn) = 0) :
    Sn * sourceNativeRouter Sm Sn Inm = Inm * Sm
    ∧ Sl * sourceNativeRouter Sn Sl Iln = Iln * Sn
    ∧ sourceNativeRouter Sn Sl Iln * sourceNativeRouter Sm Sn Inm
        = sourceNativeRouter Sm Sl Ilm := by
  have hPn :
      Sn * (Snᴴ * Sn)⁻¹ * Snᴴ * (Inm * Sm) = Inm * Sm := by
    have h : Inm * Sm =
        (Sn * (Snᴴ * Sn)⁻¹ * Snᴴ) * (Inm * Sm) :=
      sub_eq_zero.mp (by
        simpa only [Matrix.sub_mul, Matrix.one_mul] using hres_nm)
    simpa only [Matrix.mul_assoc] using h.symm
  have hPl :
      Sl * (Slᴴ * Sl)⁻¹ * Slᴴ * (Iln * Sn) = Iln * Sn := by
    have h : Iln * Sn =
        (Sl * (Slᴴ * Sl)⁻¹ * Slᴴ) * (Iln * Sn) :=
      sub_eq_zero.mp (by
        simpa only [Matrix.sub_mul, Matrix.one_mul] using hres_ln)
    simpa only [Matrix.mul_assoc] using h.symm
  constructor
  · simpa only [sourceNativeRouter, Matrix.mul_assoc] using hPn
  constructor
  · simpa only [sourceNativeRouter, Matrix.mul_assoc] using hPl
  · simp only [sourceNativeRouter]
    calc
      ((Slᴴ * Sl)⁻¹ * Slᴴ * (Iln * Sn)) *
            ((Snᴴ * Sn)⁻¹ * Snᴴ * (Inm * Sm))
          = (Slᴴ * Sl)⁻¹ * Slᴴ *
              (Iln * (Sn * (Snᴴ * Sn)⁻¹ * Snᴴ * (Inm * Sm))) := by
                simp only [Matrix.mul_assoc]
      _ = (Slᴴ * Sl)⁻¹ * Slᴴ * (Iln * (Inm * Sm)) := by rw [hPn]
      _ = (Slᴴ * Sl)⁻¹ * Slᴴ * ((Iln * Inm) * Sm) := by
            simp only [Matrix.mul_assoc]
      _ = (Slᴴ * Sl)⁻¹ * Slᴴ * (Ilm * Sm) := by rw [← hcarrier]

end NCG
