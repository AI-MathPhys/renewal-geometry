/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual

/-!
# Source-native routers for singular source Grams

This file removes the full-column-rank hypothesis from the source-native
renormalization theorem.  The router uses the spectral Moore--Penrose inverse
already constructed for source Grams, so redundant and rank-deficient source
banks are covered without changing coordinates.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Moore--Penrose inverse of a source synthesis, in Gram form. -/
noncomputable def sourceSynthesisPseudoinverse {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ) : Matrix (Fin e) (Fin h) ℂ :=
  sourceGramPseudoinverse S * Sᴴ

/-- Canonical minimum-support source router, valid for singular source Grams. -/
noncomputable def sourceNativeRouterMP {hm hn em en : ℕ}
    (Sm : Matrix (Fin hm) (Fin em) ℂ)
    (Sn : Matrix (Fin hn) (Fin en) ℂ)
    (I : Matrix (Fin hn) (Fin hm) ℂ) : Matrix (Fin en) (Fin em) ℂ :=
  sourceSynthesisPseudoinverse Sn * (I * Sm)

/-- Component of the embedded old source orthogonal to the new source range. -/
noncomputable def sourceOldResidualMP {hm hn em en : ℕ}
    (Sm : Matrix (Fin hm) (Fin em) ℂ)
    (Sn : Matrix (Fin hn) (Fin en) ℂ)
    (I : Matrix (Fin hn) (Fin hm) ℂ) : Matrix (Fin hn) (Fin em) ℂ :=
  (1 - sourceRangeProjection Sn) * (I * Sm)

/-- The source router synthesizes the orthogonal projection of the embedded
old source onto the new source range. -/
theorem sourceNativeRouterMP_synthesis {hm hn em en : ℕ}
    (Sm : Matrix (Fin hm) (Fin em) ℂ)
    (Sn : Matrix (Fin hn) (Fin en) ℂ)
    (I : Matrix (Fin hn) (Fin hm) ℂ) :
    Sn * sourceNativeRouterMP Sm Sn I =
      sourceRangeProjection Sn * (I * Sm) := by
  simp only [sourceNativeRouterMP, sourceSynthesisPseudoinverse,
    sourceRangeProjection, Matrix.mul_assoc]

set_option maxHeartbeats 800000 in
/-- Exact source-native Pythagoras for the spectral Moore--Penrose router. -/
theorem sourceNativeRouterMP_pythagoras {hm hn em en : ℕ}
    (Sm : Matrix (Fin hm) (Fin em) ℂ)
    (Sn : Matrix (Fin hn) (Fin en) ℂ)
    (I : Matrix (Fin hn) (Fin hm) ℂ)
    (hI : Iᴴ * I = 1) :
    Smᴴ * Sm =
      (sourceNativeRouterMP Sm Sn I)ᴴ * (Snᴴ * Sn) *
          sourceNativeRouterMP Sm Sn I
        + (sourceOldResidualMP Sm Sn I)ᴴ *
          sourceOldResidualMP Sm Sn I := by
  let A : Matrix (Fin hn) (Fin em) ℂ := I * Sm
  let P : Matrix (Fin hn) (Fin hn) ℂ := sourceRangeProjection Sn
  let Q : Matrix (Fin hn) (Fin hn) ℂ := 1 - P
  obtain ⟨hPH, hP2, -⟩ := (sourceGramPseudoinverse_projection Sn).2.2.2
  change Pᴴ = P at hPH
  change P * P = P at hP2
  have hQH : Qᴴ = Q := by
    dsimp only [Q]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : Q * Q = Q := by
    dsimp only [Q]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  have hAgram : Aᴴ * A = Smᴴ * Sm := by
    dsimp only [A]
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Iᴴ I Sm, hI, Matrix.one_mul]
  have hPgram : (P * A)ᴴ * (P * A) = Aᴴ * (P * A) := by
    rw [Matrix.conjTranspose_mul, hPH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P A, hP2]
  have hQgram : (Q * A)ᴴ * (Q * A) = Aᴴ * (Q * A) := by
    rw [Matrix.conjTranspose_mul, hQH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q A, hQ2]
  have hdecomp : Aᴴ * A =
      (P * A)ᴴ * (P * A) + (Q * A)ᴴ * (Q * A) := by
    have hsum : P + Q = 1 := by
      dsimp only [Q]
      abel
    rw [hPgram, hQgram, ← Matrix.mul_add, ← Matrix.add_mul]
    rw [hsum, Matrix.one_mul]
  have hsynth : Sn * sourceNativeRouterMP Sm Sn I = P * A := by
    simpa only [P, A] using sourceNativeRouterMP_synthesis Sm Sn I
  have hrouter :
      (sourceNativeRouterMP Sm Sn I)ᴴ * (Snᴴ * Sn) *
          sourceNativeRouterMP Sm Sn I = (P * A)ᴴ * (P * A) := by
    calc
      (sourceNativeRouterMP Sm Sn I)ᴴ * (Snᴴ * Sn) *
            sourceNativeRouterMP Sm Sn I =
          (Sn * sourceNativeRouterMP Sm Sn I)ᴴ *
            (Sn * sourceNativeRouterMP Sm Sn I) := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P * A)ᴴ * (P * A) := by rw [hsynth]
  rw [← hAgram, hdecomp, ← hrouter]
  rfl

/-- Exact metric transport is equivalent to vanishing old-source residual. -/
theorem sourceNativeRouterMP_exact_iff_residual_zero {hm hn em en : ℕ}
    (Sm : Matrix (Fin hm) (Fin em) ℂ)
    (Sn : Matrix (Fin hn) (Fin en) ℂ)
    (I : Matrix (Fin hn) (Fin hm) ℂ)
    (hI : Iᴴ * I = 1) :
    Smᴴ * Sm =
        (sourceNativeRouterMP Sm Sn I)ᴴ * (Snᴴ * Sn) *
          sourceNativeRouterMP Sm Sn I
      ↔ sourceOldResidualMP Sm Sn I = 0 := by
  have hmain := sourceNativeRouterMP_pythagoras Sm Sn I hI
  constructor
  · intro hexact
    have hzero : (sourceOldResidualMP Sm Sn I)ᴴ *
        sourceOldResidualMP Sm Sn I = 0 := by
      rw [hexact] at hmain
      exact (add_eq_left.mp hmain.symm)
    exact Matrix.conjTranspose_mul_self_eq_zero.mp hzero
  · intro hzero
    rw [hmain, hzero, Matrix.conjTranspose_zero, Matrix.zero_mul, add_zero]

/-- Vanishing old-source residual is exactly physical source-range inclusion. -/
theorem sourceOldResidualMP_zero_iff_rangeIncluded {hm hn em en : ℕ}
    (Sm : Matrix (Fin hm) (Fin em) ℂ)
    (Sn : Matrix (Fin hn) (Fin en) ℂ)
    (I : Matrix (Fin hn) (Fin hm) ℂ) :
    sourceOldResidualMP Sm Sn I = 0 ↔
      SourceRangeIncluded (I * Sm) Sn := by
  let P : Matrix (Fin hn) (Fin hn) ℂ := sourceRangeProjection Sn
  obtain ⟨-, -, hPSn⟩ := (sourceGramPseudoinverse_projection Sn).2.2.2
  change P * Sn = Sn at hPSn
  constructor
  · intro hres
    have hPA : P * (I * Sm) = I * Sm := by
      have h := hres
      change (1 - P) * (I * Sm) = 0 at h
      rw [Matrix.sub_mul, Matrix.one_mul] at h
      exact (sub_eq_zero.mp h).symm
    refine ⟨sourceSynthesisPseudoinverse Sn * (I * Sm), ?_⟩
    simpa only [P, sourceRangeProjection, sourceSynthesisPseudoinverse,
      Matrix.mul_assoc] using hPA.symm
  · rintro ⟨T, hfactor⟩
    change (1 - P) * (I * Sm) = 0
    rw [hfactor]
    rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPSn,
      sub_self, Matrix.zero_mul]

/-- The new-source innovation is the Gram of the component orthogonal to the
embedded old-source range, hence positive. -/
theorem sourceNewInnovation_posSemidef {hm hn en : ℕ}
    (Sn : Matrix (Fin hn) (Fin en) ℂ)
    (I : Matrix (Fin hn) (Fin hm) ℂ)
    (hI : Iᴴ * I = 1)
    (Pm : Matrix (Fin hm) (Fin hm) ℂ)
    (hPmH : Pmᴴ = Pm) (hPm2 : Pm * Pm = Pm) :
    (Snᴴ * ((1 - I * Pm * Iᴴ) * Sn)).PosSemidef := by
  have hPmProj : ∀ X : Matrix (Fin hm) (Fin en) ℂ,
      Pm * (Pm * X) = Pm * X := fun X => by
    rw [← Matrix.mul_assoc, hPm2]
  have hfac : Snᴴ * ((1 - I * Pm * Iᴴ) * Sn) =
      ((1 - I * Pm * Iᴴ) * Sn)ᴴ *
        ((1 - I * Pm * Iᴴ) * Sn) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hPmH, Matrix.conjTranspose_conjTranspose,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc, cancel_left hI, hPmProj]
    abel
  rw [hfac]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- On zero-residual arrows the Moore--Penrose source routers synthesize the
embedded sources exactly and compose strictly. -/
theorem sourceNativeRouterMP_strict_composition
    {hm hn hl em en el : ℕ}
    (Sm : Matrix (Fin hm) (Fin em) ℂ)
    (Sn : Matrix (Fin hn) (Fin en) ℂ)
    (Sl : Matrix (Fin hl) (Fin el) ℂ)
    (Inm : Matrix (Fin hn) (Fin hm) ℂ)
    (Iln : Matrix (Fin hl) (Fin hn) ℂ)
    (Ilm : Matrix (Fin hl) (Fin hm) ℂ)
    (hcarrier : Ilm = Iln * Inm)
    (hres_nm : sourceOldResidualMP Sm Sn Inm = 0)
    (hres_ln : sourceOldResidualMP Sn Sl Iln = 0) :
    Sn * sourceNativeRouterMP Sm Sn Inm = Inm * Sm
      ∧ Sl * sourceNativeRouterMP Sn Sl Iln = Iln * Sn
      ∧ sourceNativeRouterMP Sn Sl Iln * sourceNativeRouterMP Sm Sn Inm =
        sourceNativeRouterMP Sm Sl Ilm := by
  have hnm : Sn * sourceNativeRouterMP Sm Sn Inm = Inm * Sm := by
    rw [sourceNativeRouterMP_synthesis]
    have h := hres_nm
    rw [sourceOldResidualMP, Matrix.sub_mul, Matrix.one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hln : Sl * sourceNativeRouterMP Sn Sl Iln = Iln * Sn := by
    rw [sourceNativeRouterMP_synthesis]
    have h := hres_ln
    rw [sourceOldResidualMP, Matrix.sub_mul, Matrix.one_mul] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨hnm, hln, ?_⟩
  simp only [sourceNativeRouterMP, sourceSynthesisPseudoinverse]
  calc
    (sourceGramPseudoinverse Sl * Slᴴ * (Iln * Sn)) *
          (sourceGramPseudoinverse Sn * Snᴴ * (Inm * Sm)) =
        sourceGramPseudoinverse Sl * Slᴴ *
          (Iln * (Sn * sourceGramPseudoinverse Sn * Snᴴ * (Inm * Sm))) := by
            simp only [Matrix.mul_assoc]
    _ = sourceGramPseudoinverse Sl * Slᴴ * (Iln * (Inm * Sm)) := by
      have hsynth : Sn * sourceGramPseudoinverse Sn * Snᴴ * (Inm * Sm) =
          Inm * Sm := by
        simpa only [sourceNativeRouterMP, sourceSynthesisPseudoinverse,
          Matrix.mul_assoc] using hnm
      rw [hsynth]
    _ = sourceGramPseudoinverse Sl * Slᴴ * ((Iln * Inm) * Sm) := by
      simp only [Matrix.mul_assoc]
    _ = sourceGramPseudoinverse Sl * Slᴴ * (Ilm * Sm) := by rw [← hcarrier]

/-- Complete general-rank form of `thm:source-native-renormalization`. -/
theorem source_native_renormalization_moore_penrose
    {hm hn em en : ℕ}
    (Sm : Matrix (Fin hm) (Fin em) ℂ)
    (Sn : Matrix (Fin hn) (Fin en) ℂ)
    (I : Matrix (Fin hn) (Fin hm) ℂ)
    (hI : Iᴴ * I = 1) :
    Smᴴ * Sm =
      (sourceNativeRouterMP Sm Sn I)ᴴ * (Snᴴ * Sn) *
          sourceNativeRouterMP Sm Sn I
        + (sourceOldResidualMP Sm Sn I)ᴴ * sourceOldResidualMP Sm Sn I
    ∧ (Smᴴ * Sm =
          (sourceNativeRouterMP Sm Sn I)ᴴ * (Snᴴ * Sn) *
            sourceNativeRouterMP Sm Sn I
        ↔ SourceRangeIncluded (I * Sm) Sn)
    ∧ (∀ Pm : Matrix (Fin hm) (Fin hm) ℂ,
        Pmᴴ = Pm → Pm * Pm = Pm →
          (Snᴴ * ((1 - I * Pm * Iᴴ) * Sn)).PosSemidef) := by
  refine ⟨sourceNativeRouterMP_pythagoras Sm Sn I hI, ?_, ?_⟩
  · exact (sourceNativeRouterMP_exact_iff_residual_zero Sm Sn I hI).trans
      (sourceOldResidualMP_zero_iff_rangeIncluded Sm Sn I)
  · exact sourceNewInnovation_posSemidef Sn I hI

end NCG
