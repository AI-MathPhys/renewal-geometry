/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Fourier.ZMod

/-!
# Fourier symbols of covariant differences on finite cycles

This file supplies the concrete cyclic Fourier layer for periodic covariant
regulators.  In mathlib's `ZMod.dft` normalization, forward translation by one
site has multiplier `ZMod.stdAddChar k`.  Constant fibre operators commute with
the DFT, so a covariant forward difference diagonalizes to the symbol
`stdAddChar k · 1 - U`.
-/

open Finset AddChar
open scoped ZMod

namespace NCG

variable {N : ℕ} [NeZero N]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Forward translation by one site on the finite cycle. -/
def zmodForwardShift (Phi : ZMod N → E) : ZMod N → E :=
  fun x => Phi (x + 1)

/-- In mathlib's DFT convention, forward translation has multiplier
`stdAddChar k`. -/
theorem zmod_dft_forwardShift (Phi : ZMod N → E) (k : ZMod N) :
    ZMod.dft (zmodForwardShift Phi) k =
      ZMod.stdAddChar k • ZMod.dft Phi k := by
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [zmodForwardShift]
  have hreindex :
      (∑ j : ZMod N,
        ZMod.stdAddChar (-(j * k)) • Phi (j + 1)) =
      ∑ l : ZMod N,
        ZMod.stdAddChar (-((l - 1) * k)) • Phi l := by
    simpa using Fintype.sum_equiv (Equiv.addRight (1 : ZMod N))
      (fun j : ZMod N =>
        ZMod.stdAddChar (-(j * k)) • Phi (j + 1))
      (fun l : ZMod N =>
        ZMod.stdAddChar (-((l - 1) * k)) • Phi l)
      (fun j => by simp)
  rw [hreindex, smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have harg : -((l - 1) * k) = k + -(l * k) := by ring
  rw [harg, map_add_eq_mul, mul_smul]

/-- A constant continuous fibre operator commutes with the cyclic DFT. -/
theorem zmod_dft_clm_apply
    (U : E →L[ℂ] E) (Phi : ZMod N → E) (k : ZMod N) :
    ZMod.dft (fun x => U (Phi x)) k = U (ZMod.dft Phi k) := by
  simp only [ZMod.dft_apply, map_sum, map_smul]

/-- The unscaled covariant forward difference on a finite cycle. -/
def zmodCovariantDifference
    (U : E →L[ℂ] E) (Phi : ZMod N → E) : ZMod N → E :=
  fun x => Phi (x + 1) - U (Phi x)

/-- Exact Fourier multiplier of the covariant forward difference. -/
theorem zmod_dft_covariantDifference
    (U : E →L[ℂ] E) (Phi : ZMod N → E) (k : ZMod N) :
    ZMod.dft (zmodCovariantDifference U Phi) k =
      (ZMod.stdAddChar k • (1 : E →L[ℂ] E) - U)
        (ZMod.dft Phi k) := by
  have hshift := zmod_dft_forwardShift Phi k
  have hU := zmod_dft_clm_apply U Phi k
  rw [ZMod.dft_apply]
  simp only [zmodCovariantDifference, smul_sub, sum_sub_distrib]
  rw [← ZMod.dft_apply, ← ZMod.dft_apply,
    show (fun x => Phi (x + 1)) = zmodForwardShift Phi from rfl, hshift, hU]
  change ZMod.stdAddChar k • ZMod.dft Phi k - U (ZMod.dft Phi k) =
    ZMod.stdAddChar k • ZMod.dft Phi k - U (ZMod.dft Phi k)
  rfl

/-- Exact Fourier multiplier after scaling by a positive mesh. -/
theorem zmod_dft_scaledCovariantDifference
    (h : ℝ) (U : E →L[ℂ] E) (Phi : ZMod N → E) (k : ZMod N) :
    ZMod.dft (fun x => (h⁻¹ : ℂ) • zmodCovariantDifference U Phi x) k =
      (h⁻¹ : ℂ) •
        ((ZMod.stdAddChar k • (1 : E →L[ℂ] E) - U)
          (ZMod.dft Phi k)) := by
  calc
    ZMod.dft (fun x => (h⁻¹ : ℂ) • zmodCovariantDifference U Phi x) k =
        (h⁻¹ : ℂ) • ZMod.dft (zmodCovariantDifference U Phi) k := by
      have hdft := congrFun
        (ZMod.dft_const_smul (h⁻¹ : ℂ) (zmodCovariantDifference U Phi)) k
      change ZMod.dft (((h⁻¹ : ℂ) • zmodCovariantDifference U Phi)) k = _
      exact hdft
    _ = _ := congrArg ((h⁻¹ : ℂ) • ·)
      (zmod_dft_covariantDifference U Phi k)

end NCG
